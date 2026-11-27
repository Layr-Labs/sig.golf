import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace ClaudeWCT.WCT9.CanonicalPolicy

/-- Layer 1 saves 0/1/2 credits from the low six Gray-code bits `d` of its leaf
(`d ≠ 0` saves one, an odd `d ≥ 4` saves another; 2/66/60 of the 128 leaves);
layers 2 and 3 keep the 0/1 pair save. -/
def lowerPathSave (lay leaf : Nat) : Nat :=
  if lay=1 then
    (if (leaf ^^^ leaf/2)%64≠0 then 1 else 0) +
      (if (leaf ^^^ leaf/2)%64%2=1 ∧ 4≤(leaf ^^^ leaf/2)%64 then 1 else 0)
  else if (lay=2 ∨ lay=3) ∧ (leaf%4=1 ∨ leaf%4=2) then 1 else 0

theorem lowerPathSave_le_two (lay leaf : Nat) : lowerPathSave lay leaf ≤ 2 := by
  unfold lowerPathSave
  split_ifs <;> omega

/-- Layers 2 and 3 (and the top) still save at most one credit. -/
theorem lowerPathSave_le_one (lay leaf : Nat) (hl : lay≠1 := by decide) : lowerPathSave lay leaf ≤ 1 := by
  unfold lowerPathSave
  split_ifs <;> omega

/-- The low six Gray-code bits only read the low seven leaf bits. -/
theorem gray_mod64 (a : Nat) : (a ^^^ a/2)%64=((a%128) ^^^ (a%128)/2)%64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (64:Nat)=2^6 from rfl, show (128:Nat)=2^7 from rfl]
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_xor,Nat.testBit_div_two]
  by_cases hi : i<6
  · have h7 : i<7 := by omega
    have h7' : i+1<7 := by omega
    simp [hi,h7,h7']
  · simp [hi]

theorem lowerPathSave_mod128 (lay a b : Nat) (h : a%128=b%128) :
    lowerPathSave lay a = lowerPathSave lay b := by
  have h4 : a%4=b%4 := by omega
  have hg : (a ^^^ a/2)%64=(b ^^^ b/2)%64 := by rw [gray_mod64 a,gray_mod64 b,h]
  unfold lowerPathSave
  simp only [hg,h4]

/-- Layers other than 1 only read the leaf modulo 4. -/
theorem lowerPathSave_mod8 (lay a b : Nat) (h : a%8=b%8) (hl : lay≠1 := by decide) :
    lowerPathSave lay a = lowerPathSave lay b := by
  have h4 : a%4=b%4 := by omega
  unfold lowerPathSave
  simp only [hl,h4,if_false]

theorem lowerPathSave_congr (lay a b : Nat) (h8 : a%8=b%8) (h128 : lay=1 → a%128=b%128) :
    lowerPathSave lay a = lowerPathSave lay b := by
  by_cases hl : lay=1
  · exact lowerPathSave_mod128 lay a b (h128 hl)
  · exact lowerPathSave_mod8 lay a b h8 hl

theorem lowerPathSave_one_mod (leaf : Nat) : lowerPathSave 1 leaf = lowerPathSave 1 (leaf%128) :=
  lowerPathSave_mod128 1 _ _ (by omega)

theorem lowerPathSave_one_counts :
    ((List.range 128).filter fun n => lowerPathSave 1 n=0).length=2 ∧
      ((List.range 128).filter fun n => lowerPathSave 1 n=1).length=66 ∧
        ((List.range 128).filter fun n => lowerPathSave 1 n=2).length=60 := by decide +kernel

theorem lowerPathSave_top (leaf : Nat) : lowerPathSave 0 leaf=0 := by simp [lowerPathSave]
#print axioms lowerPathSave_mod128
#print axioms lowerPathSave_mod8

/-- Gate a credit increment of at most two so it cannot wrap a bounded machine word. -/
def guardedCredit (r c saved : Nat) : Nat := c + if c<r then saved else 0

theorem guardedCredit_lt (r c saved bound : Nat) (hr : r+1<bound) (hc : c<bound) (hs : saved≤2) :
    guardedCredit r c saved<bound := by
  unfold guardedCredit
  split_ifs <;> omega

theorem residual_guardedCredit (r c saved : Nat) :
    r-guardedCredit r c saved = r-c-saved := by
  unfold guardedCredit
  split_ifs <;> omega
#print axioms residual_guardedCredit
end ClaudeWCT.WCT9.CanonicalPolicy
