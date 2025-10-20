import RISCV.Alu
import RISCV.AluDecode
import RISCV.ImmGen
import RISCV.InstrDecode
import RISCV.RegisterFile
import RISCV.Types

namespace RISCV.SingleCycle

structure ProcessorI where
  instruction : Instruction
  data_mem_r_data : Ptr -> Word
  deriving Inhabited

structure ProcessorO where
  pc : Ptr
  mem_addr : Ptr
  mem_w_en : Enable
  mem_w_data : Word
  deriving Repr, Inhabited, BEq

structure ProcessorState where
  pc : Word
  registers : RegisterFile
  deriving Repr, Inhabited, BEq

-- Extract the reg_dst if the instruction has one.
def regDstFromParsedInstruction (instr : ParsedInstruction) : Option Reg := if isSw instr.opcode then .none else .some instr.rd

def processorT  (processorI : ProcessorI) (processorState : ProcessorState) : (ProcessorO × ProcessorState) :=
  .mk {
      pc := pc'
      mem_addr := mem_addr
      mem_w_en := decodedInstruction.mem_w_en
      mem_w_data
    } {
      pc := pc'
      registers := registers'
    }
where
  parsedInstruction := parseInstruction processorI.instruction
  decodedInstruction := instrDecode parsedInstruction.opcode
  immediate := ImmGen.immGen processorI.instruction
  aluCtrl := aluDecodeT parsedInstruction.opcode parsedInstruction.funct7 parsedInstruction.funct3
  reg_r_data_a := readRegister
    processorState.registers parsedInstruction.rs1
  reg_r_data_b := readRegister
    processorState.registers parsedInstruction.rs2
  aluInA := reg_r_data_a
  aluInB := if decodedInstruction.use_imm then immediate else reg_r_data_b
  mem_w_data := reg_r_data_b
  aluTRes := aluT aluCtrl aluInA aluInB
  aluRes := aluTRes.1
  equals := aluTRes.2
  mem_addr := aluRes
  reg_w_data := match decodedInstruction.reg_src with
    | .pc4 => processorState.pc + 4
    | .mem => processorI.data_mem_r_data mem_addr
    | .alu => aluRes
  registersTRes := registersT
    (register_file := processorState.registers)
    (r_reg_a := parsedInstruction.rs1)
    (r_reg_b := parsedInstruction.rs2)
    (reg_w_en := decodedInstruction.reg_w_en)
    (w_reg_dst := regDstFromParsedInstruction parsedInstruction |>.getD 0)
    (reg_w_data := reg_w_data)
  registers' := registersTRes.1
  pc' := match (decodedInstruction.jump, decodedInstruction.branch, equals) with
    | (true,_,_)
    | (false,true,true) => processorState.pc + immediate
    | _ => processorState.pc + 4
