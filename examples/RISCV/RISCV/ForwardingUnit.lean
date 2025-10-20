import RISCV.Types

structure ForwardingUnitInput where
  use_imm : Bool
  ex_reg_w_en : Enable
  mem_reg_w_en : Enable
  id_rs1 : Reg
  id_rs2 : Reg
  ex_reg_dst : Reg
  mem_reg_dst : Reg
  deriving Repr, Inhabited, DecidableEq

structure ForwardingUnitOutput where
  -- | Which stage/input the alu should read from.
  alu_src_a : NonImmAluSrc
  alu_src_b : AluSrc
  -- | Which stage/input the data to write to memory should come from.
  mem_src : NonImmAluSrc
  deriving Repr, Inhabited, DecidableEq

def forwardingUnit (inp: ForwardingUnitInput): ForwardingUnitOutput := {alu_src_a, alu_src_b, mem_src}
where
  ex_reg_dst_nonzero := inp.ex_reg_dst != 0
  mem_reg_dst_nonzero := inp.mem_reg_dst != 0

  alu_src_a :=
    -- If data is produced one stage ahead in the execute stage.
    -- In other words, instruction source register 1 matches the destination of the data in the ex stage and the data is going to be written into the register file.
    if inp.ex_reg_w_en && (inp.id_rs1 == inp.ex_reg_dst) && ex_reg_dst_nonzero then NonImmAluSrc.ex
    -- If data is produced two stages ahead in the memory stage.
    else if inp.mem_reg_w_en && (inp.id_rs1 == inp.mem_reg_dst) && mem_reg_dst_nonzero then NonImmAluSrc.mem
    -- Data produced in write-back or beyond.
    else NonImmAluSrc.reg

  alu_src_b :=
    -- If immediate instruction don't forward.
    if inp.use_imm then AluSrc.imm
    -- If data is produced one stage ahead in the execute stage.
    else if inp.ex_reg_w_en && (inp.id_rs2 == inp.ex_reg_dst) && ex_reg_dst_nonzero then AluSrc.ex
    -- If data is produced two stages ahead in the memory stage.
    else if inp.mem_reg_w_en && (inp.id_rs2 == inp.mem_reg_dst) && mem_reg_dst_nonzero then AluSrc.mem
    -- Data produced in write-back or beyond.
    else AluSrc.reg

  -- Data input to memory comes from reg_b in single-stage design, so the logic here will look the same as reg_b other than not using immediate.
  -- It is up to `mem_w_en` in the instruction decode for whether to use this value or not.
  mem_src :=
    if inp.ex_reg_w_en && (inp.id_rs2 == inp.ex_reg_dst) && ex_reg_dst_nonzero then NonImmAluSrc.ex
    else if inp.mem_reg_w_en && (inp.id_rs2 == inp.mem_reg_dst) && mem_reg_dst_nonzero then NonImmAluSrc.mem
    else NonImmAluSrc.reg
