import RISCV.Basic
import RISCV.Types
import Hdlean

abbrev RegisterFile := Vector Word 31

section Unused
-- attribute [simp] Fin.sub_val_of_le
def Fin.subSat.aux (a b : Fin n): Fin n := if a ≤ b then ⟨0, Fin.pos a⟩ else a - b
@[implemented_by_hw Fin.subSat.aux]
def Fin.subSat (a b : Fin n): Fin n := ⟨a.1 - b.1, by omega⟩
theorem Fin.subSat_eq_subSat_aux : @Fin.subSat = @Fin.subSat.aux := by
  funext n a b
  simp [Fin.subSat, Fin.subSat.aux]
  if h:a ≤ b then
    simp [h]
    omega
  else
    simp [h]
    simp at h
    congr
    have : (n - b.1 + a.1) = n + (a.1 - b.1) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega

def readRegister' (regFile : RegisterFile) (reg : Reg) : Word :=
  let reg' : Fin 31 := reg.toFin.subSat 1 |>.castLT (by decide +revert)
  if reg == 0 then 0 else Vector.get regFile reg'
end Unused

def readRegister (regFile : RegisterFile) (reg : Reg) : Word :=
  if h:reg = 0 then 0 else
  let i := reg - 1 |>.toFin |>.castLT (by
    change reg - 1 < 31
    bv_omega
  )
  regFile[i]

section Unused
def writeRegister' (regFile:RegisterFile) (reg:Reg) (value:Word) : RegisterFile :=
  if h:reg == 0 then regFile else {regFile with [reg-1 |>.toFin|>.castLT (by
    simp at h
    change (reg-1 < 31)
    bv_omega)] := value}
end Unused

def writeRegister (regFile:RegisterFile) (reg:Reg) (value:Word) : RegisterFile :=
  if h:reg = 0 then regFile else
  let i := reg-1 |>.toFin |>.castLT (by
    change reg-1 < 31
    bv_omega
  )
  regFile.set i value

def registersT (register_file:RegisterFile) (r_reg_a:Reg) (r_reg_b:Reg) (reg_w_en:Enable) (w_reg_dst:Reg) (reg_w_data:Word) : (RegisterFile× Word× Word) :=
 (register_file', r_reg_a_data, r_reg_b_data)
  where
  register_file' := if reg_w_en then writeRegister register_file w_reg_dst reg_w_data else register_file
  -- Forward the write to the reads as needed instead of using the negative edge of the clock to create an implicit forwarding path like in the System Verilog version.
  -- In HDLean, using multiple domains is more tedious since you have to thread them from the topEntity, and you can't easily generate an inverted clock from the input clock.
  fwd_read r_reg := if r_reg == w_reg_dst && r_reg != 0 then reg_w_data else readRegister register_file r_reg
  r_reg_a_data := fwd_read r_reg_a
  r_reg_b_data := fwd_read r_reg_b
