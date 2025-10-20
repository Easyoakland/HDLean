import RISCV.Types
import RISCV.Basic

-- Define the output record type
structure InstrDecodeOutput where
  use_imm : Bool
  jump : Bool
  branch : Bool
  mem_r_en : Enable
  mem_w_en : Enable
  reg_src : RegSrc
  reg_w_en : Enable
  use_rs1 : Bool
  use_rs2 : Bool
  deriving Repr, BEq

def isSw (opcode:Opcode): Bool := opcode == 0b0100011

-- Instruction decode function
def instrDecode  : Opcode → InstrDecodeOutput
  -- R-type arithmetic instruction (0b0110011)
  | 0b0110011 =>
      { use_imm := False,
        jump := False,
        branch := False,
        mem_r_en := False,
        mem_w_en := False,
        reg_src := .alu, -- ALU output
        reg_w_en := True, -- reg write
        use_rs1 := True, -- use rs1
        use_rs2 := True -- use rs2
      }
  -- I-type arithmetic instructions (0b0010011)
  | 0b0010011 =>
      { use_imm := True, -- use immediate
        jump := False,
        branch := False,
        mem_r_en := False,
        mem_w_en := False,
        reg_src := .alu, -- ALU output
        reg_w_en := True, -- reg write
        use_rs1 := True, -- use rs1
        use_rs2 := False
      }
  -- lw (0b0000011)
  | 0b0000011 =>
      { use_imm := True, -- use immediate
        jump := False,
        branch := False,
        mem_r_en := True, -- mem read
        mem_w_en := False,
        reg_src := .mem, -- data memory
        reg_w_en := True, -- reg write
        use_rs1 := True, -- use rs1
        use_rs2 := False -- use rs2
      }
  -- sw (0b0100011)
  | 0b0100011 =>
      { use_imm := True, -- use immediate
        jump := False,
        branch := False,
        mem_r_en := False,
        mem_w_en := True, -- mem write
        reg_src := .alu, -- Don't care value, using ALU as default
        reg_w_en := False,
        use_rs1 := True, -- use rs1
        use_rs2 := True -- use rs2
      }
  -- beq (0b1100011)
  | 0b1100011 =>
      { use_imm := False,
        jump := False,
        branch := True, -- branch
        mem_r_en := False,
        mem_w_en := False,
        reg_src := .alu, -- Don't care value, using ALU as default
        reg_w_en := False,
        use_rs1 := True, -- use rs1
        use_rs2 := True -- use rs2
      }
  -- jal (0b1101111)
  | 0b1101111 =>
    -- Immediate is source of jump, but doesn't go to the ALU
    -- This would be where PCsrc would be set to the immediate but this module doesn't handle that
      { use_imm := False,
        jump := True,
        branch := False,
        mem_r_en := False,
        mem_w_en := False,
        reg_src := .pc4, -- and link
        reg_w_en := True, -- reg write "link"
        use_rs1 := False,
        use_rs2 := False
      }
  -- lui (0b0110111)
  | 0b0110111 =>
      { use_imm := True, -- use immediate
        jump := False,
        branch := False,
        mem_r_en := False,
        mem_w_en := False,
        reg_src := .alu, -- ALU output
        reg_w_en := True, -- write reg
        use_rs1 := False,
        use_rs2 := False
      }
  -- Unsupported/invalid instructions shouldn't change state
  | _ =>
      { use_imm := False, -- Don't care, using False as default
        jump := False, -- Don't jump
        branch := False, -- Don't branch
        mem_r_en := False, -- Don't touch mem
        mem_w_en := False, -- Don't touch mem
        reg_src := .alu, -- Don't care, using ALU as default
        reg_w_en := False, -- Don't write to reg
        use_rs1 := False, -- Not using rs1
        use_rs2 := False -- Not using rs2
      }

structure ParsedInstruction where
  opcode : Opcode
  rd : Reg
  rs1 : Reg
  rs2 : Reg
  funct3 : Funct3
  funct7 : Funct7
  deriving Repr

def parseInstruction  (instruction:Instruction) : ParsedInstruction :=
  {opcode, rd, funct3, rs1, rs2, funct7}
  where
    instruction' := instruction.reverse.toVector
    opcode := instruction'[0:7].reverse.toBitVec
    rd := instruction'[7:12].reverse.toBitVec
    funct3 := instruction'[12:15].reverse.toBitVec
    rs1 := instruction'[15:20].reverse.toBitVec
    rs2 := instruction'[20:25].reverse.toBitVec
    funct7 := instruction'[25:32].reverse.toBitVec

#eval (0x000002b3:Word).reverse.toVector[0:2]
