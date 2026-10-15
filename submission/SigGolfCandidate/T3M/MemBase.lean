import SigGolfCandidate.Rv

/-! Machine-state predicates shared by the selector and the signature memory
lemmas. Kept independent of the signing/expansion development. -/
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

abbrev pcOf (k : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * k)
theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

def Frame (s t : MachineState) (W : Nat → Prop) : Prop :=
  ∀ A < 2 ^ 64, ¬ W A → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
theorem Frame.refl (s : MachineState) (W : Nat → Prop) : Frame s s W := fun _ _ _ => rfl
theorem Frame.trans {s t u : MachineState} {W₁ W₂ : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) : Frame s u (fun A => W₁ A ∨ W₂ A) := by
  intro A hA hne
  rw [h₂ A hA (fun h => hne (Or.inr h)), h₁ A hA (fun h => hne (Or.inl h))]
theorem Frame.mono {s t : MachineState} {W W' : Nat → Prop} (h : Frame s t W)
    (hW : ∀ A, A < 2 ^ 64 → W A → W' A) : Frame s t W' :=
  fun A hA hn => h A hA (fun hw => hn (hW A hA hw))
theorem Frame.get {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {A : Nat} (hA : A < 2 ^ 64)
    (hn : ¬ W A) : t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := h A hA hn
def DigAt (t : MachineState) (A : Nat) (d : BitVec 128) : Prop :=
  t.getMem (BitVec.ofNat 64 A) = d.extractLsb' 0 64 ∧ t.getMem (BitVec.ofNat 64 (A + 8)) = d.extractLsb' 64 64

def RegsExcept (s t : MachineState) (l : List Reg) : Prop := ∀ r, r ∉ l → t.getReg r = s.getReg r
theorem RegsExcept.refl (s : MachineState) (l : List Reg) : RegsExcept s s l := fun _ _ => rfl
theorem RegsExcept.trans {s t u : MachineState} {l₁ l₂ : List Reg} (h₁ : RegsExcept s t l₁)
    (h₂ : RegsExcept t u l₂) : RegsExcept s u (l₁ ++ l₂) := by
  intro r hr
  rw [List.mem_append, not_or] at hr
  rw [h₂ r hr.2, h₁ r hr.1]
theorem RegsExcept.mono {s t : MachineState} {l l' : List Reg} (h : RegsExcept s t l)
    (hl : ∀ r ∈ l, r ∈ l') : RegsExcept s t l' := fun r hr => h r (fun hm => hr (hl r hm))
theorem RegsExcept.get {s t : MachineState} {l : List Reg} (h : RegsExcept s t l) {r : Reg}
    (hr : r ∉ l) : t.getReg r = s.getReg r := h r hr
end SigGolfCandidate.T3M
