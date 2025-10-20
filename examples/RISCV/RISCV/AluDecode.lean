import RISCV.Types

set_option trace.compiler.ir true in
def aluDecodeT (op:Opcode) (fn7: Funct7) (fn3: Funct3): AluCtrl := match op with
  -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#lui
  | 0b0110111 => .lui
  -- Loads and stores perform adds due to offset calculation.
  -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#sw
  | 0b0100011 => .add
  -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#lw
  | 0b0000011 => .add
  -- i-type
  | 0b0010011 =>
    match fn3 with
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#andi
      | 0b111 => .and
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#ori
      | 0b110 => .or
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#addi
      | 0b000 => .add
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#xori
      | 0b100 => .xor
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#slli
      | 0b001 => .sll
      | 0b101 =>
        if fn7[5]
          -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#srai
          then .sra
          -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#srli
          else .srl
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#slti
      | 0b010 => .slt
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#sltiu
      | 0b011 => .sltu
      | _ => panic! "invalid fn3 for i-type"
  -- r-type
  | 0b0110011 =>
    match (fn7, fn3) with
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#and
      | (0b0000000, 0b111) => .and
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#or
      | (0b0000000, 0b110) => .or
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#add
      | (0b0000000, 0b000) => .add
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#sll
      | (0b0000000, 0b001) => .sll
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#srl
      | (0b0000000, 0b101) => .srl
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#sub
      | (0b0100000, 0b000) => .sub
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#slt
      | (0b0000000, 0b010) => .slt
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#xor
      | (0b0000000, 0b100) => .xor
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#sltu
      | (0b0000000, 0b011) => .sltu
      -- https://msyksphinz-self.github.io/riscv-isadoc/html/rvi.html#sra
      | (0b0100000, 0b101) => .sra
      | _ => panic! "invalid fn7, fn3 for r-type"
  | 0b1101111 -- jal
  | 0b1100111 -- jalr
  | 0b1100011 -- beq, bne, blt, bge, bltu, bgeu
    => default
  | op => panic! s!"invalid instr: {op}"
