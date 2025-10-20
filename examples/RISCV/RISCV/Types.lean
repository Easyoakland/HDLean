inductive AluCtrl where
  | and
  | or
  | add
  | sll
  | srl
  | sub
  | slt
  | xor
  | sltu
  | sra
  | lui
  deriving Repr, Inhabited, DecidableEq

abbrev Reg := BitVec 5
abbrev Word := BitVec 32
abbrev Instruction := BitVec 32
abbrev Ptr := BitVec 32
abbrev Opcode := BitVec 7
abbrev Funct7 := BitVec 7
abbrev Funct3 := BitVec 3
abbrev Enable := Bool

inductive NonImmAluSrc where
  | ex
  | mem
  | reg
  deriving Repr, DecidableEq

instance : Inhabited NonImmAluSrc := ⟨.reg⟩

inductive AluSrc where
  | imm
  | ex
  | mem
  | reg
  deriving Repr, DecidableEq

instance : Inhabited AluSrc := ⟨.reg⟩

inductive PcSrc where
  | pc4
  | jump
  | branch
  deriving Repr, DecidableEq

inductive RegSrc where
  | pc4
  | mem
  | alu
  deriving Repr, DecidableEq

instance : Inhabited RegSrc := ⟨.alu⟩
