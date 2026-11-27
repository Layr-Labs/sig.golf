import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
open scoped BigOperators
open Finset
namespace ClaudeWCT.Numerics.LocalRouteUniform

def pairSave (n : Nat) : Nat := if n%4=1 ∨ n%4=2 then 1 else 0
/-- Layer-1 save of leaf `n`: the expression of `CanonicalPolicy.lowerPathSave 1 n`
(low six Gray-code bits `d`; `d ≠ 0` saves one, an odd `d ≥ 4` saves another). -/
def oneSave (n : Nat) : Nat :=
  (if (n ^^^ n/2)%64≠0 then 1 else 0) + (if (n ^^^ n/2)%64%2=1 ∧ 4≤(n ^^^ n/2)%64 then 1 else 0)

/-- Line-A top save of row `r % 64` (top levels 0..5): the table of `CanonicalPolicy.topSaveATab`
(0/1/2 setups for 6/36/22 rows). -/
def saveATab : List Nat := [0,1,1,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,0,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,0,1,1,1,1,1,1,0,0,1,1,1,1,1,1,0]
/-- The expression of `CanonicalPolicy.topSaveA`. -/
def saveA (r : Nat) : Nat := saveATab.getD (r % 64) 0
/-- Line-B top save of row `r % 64` (top levels 6..11): the table of `CanonicalPolicy.topSaveBTab`
(0/1 setups for 22/42 rows). -/
def saveBTab : List Nat := [0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,0,1,1,0,0,1,1,1,0,1,1,0]
/-- The expression of `CanonicalPolicy.topSaveB`. -/
def saveB (r : Nat) : Nat := saveBTab.getD (r % 64) 0

theorem oneSave_le_two (n : Nat) : oneSave n ≤ 2 := by
  unfold oneSave
  split_ifs <;> omega

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

theorem oneSave_mod128 (a b : Nat) (h : a%128=b%128) : oneSave a = oneSave b := by
  have hg : (a ^^^ a/2)%64=(b ^^^ b/2)%64 := by rw [gray_mod64 a,gray_mod64 b,h]
  unfold oneSave
  simp only [hg]

theorem sum_binary {n : Nat} (g : Fin n → Nat) (h : ∀ i, g i ≤ 1) (f : Nat → Nat) :
    (∑ i : Fin n, f (g i)) =
      ((univ.filter fun i => g i=0).card)*f 0 + ((univ.filter fun i => g i=1).card)*f 1 := by
  have point (i : Fin n) : f (g i) = (if g i=0 then f 0 else 0) + (if g i=1 then f 1 else 0) := by
    have hi := h i
    have cases : g i=0 ∨ g i=1 := by omega
    rcases cases with hc | hc <;> simp [hc]
  simp_rw [point]
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  simp

theorem sum_ternary {n : Nat} (g : Fin n → Nat) (h : ∀ i, g i ≤ 2) (f : Nat → Nat) :
    (∑ i : Fin n, f (g i)) =
      ((univ.filter fun i => g i=0).card)*f 0 + ((univ.filter fun i => g i=1).card)*f 1 +
        ((univ.filter fun i => g i=2).card)*f 2 := by
  have point (i : Fin n) : f (g i) =
      (if g i=0 then f 0 else 0) + (if g i=1 then f 1 else 0) + (if g i=2 then f 2 else 0) := by
    have hi := h i
    have cases : g i=0 ∨ g i=1 ∨ g i=2 := by omega
    rcases cases with hc | hc | hc <;> simp [hc]
  simp_rw [point]
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  simp

theorem pair_zero_count : ((univ : Finset (Fin 64)).filter fun i => pairSave i.val=0).card=32 := by decide +kernel
theorem pair_one_count : ((univ : Finset (Fin 64)).filter fun i => pairSave i.val=1).card=32 := by decide +kernel
theorem one_zero_count : ((univ : Finset (Fin 128)).filter fun i => oneSave i.val=0).card=2 := by decide +kernel
theorem one_one_count : ((univ : Finset (Fin 128)).filter fun i => oneSave i.val=1).card=66 := by decide +kernel
theorem one_two_count : ((univ : Finset (Fin 128)).filter fun i => oneSave i.val=2).card=60 := by decide +kernel

theorem saveA_zero_count : ((univ : Finset (Fin 64)).filter fun i => saveA i.val=0).card=6 := by decide +kernel
theorem saveA_one_count : ((univ : Finset (Fin 64)).filter fun i => saveA i.val=1).card=36 := by decide +kernel
theorem saveA_two_count : ((univ : Finset (Fin 64)).filter fun i => saveA i.val=2).card=22 := by decide +kernel
theorem saveB_zero_count : ((univ : Finset (Fin 64)).filter fun i => saveB i.val=0).card=22 := by decide +kernel
theorem saveB_one_count : ((univ : Finset (Fin 64)).filter fun i => saveB i.val=1).card=42 := by decide +kernel
theorem saveA_le_two : ∀ i : Fin 64, saveA i.val ≤ 2 := by decide +kernel
theorem saveB_le_one : ∀ i : Fin 64, saveB i.val ≤ 1 := by decide +kernel

def sum64 (f : Nat → Nat) : Nat := ∑ i : Fin 64, f (pairSave i.val)
def sum128 (f : Nat → Nat) : Nat := ∑ i : Fin 128, f (oneSave i.val)
theorem sum64_eq (f : Nat → Nat) : sum64 f=32*(f 0+f 1) := by
  unfold sum64
  rw [sum_binary (fun i : Fin 64 => pairSave i.val) (by intro i; unfold pairSave; split_ifs <;> omega)]
  rw [pair_zero_count,pair_one_count]
  omega

theorem sum128_eq (f : Nat → Nat) : sum128 f=2*f 0+66*f 1+60*f 2 := by
  unfold sum128
  rw [sum_ternary (fun i : Fin 128 => oneSave i.val) (fun i => oneSave_le_two i.val)]
  rw [one_zero_count,one_one_count,one_two_count]

def sumA (f : Nat → Nat) : Nat := ∑ i : Fin 64, f (saveA i.val)
def sumB (f : Nat → Nat) : Nat := ∑ i : Fin 64, f (saveB i.val)
theorem sumA_eq (f : Nat → Nat) : sumA f=6*f 0+36*f 1+22*f 2 := by
  unfold sumA
  rw [sum_ternary (fun i : Fin 64 => saveA i.val) saveA_le_two]
  rw [saveA_zero_count,saveA_one_count,saveA_two_count]

theorem sumB_eq (f : Nat → Nat) : sumB f=22*f 0+42*f 1 := by
  unfold sumB
  rw [sum_binary (fun i : Fin 64 => saveB i.val) saveB_le_one]
  rw [saveB_zero_count,saveB_one_count]

/-- Line-B row (outer), line-A row, layer-1 leaf, layer-2 leaf, layer-3 leaf; the root save is
line-A save + line-B save. -/
def nested (F : Nat → Nat → Nat → Nat → Nat) : Nat :=
  sumB fun a => sumA fun b => sum128 fun c => sum64 fun d => sum64 fun e => F (b+a) c d e

/-- The layer-1 save is ternary with weights 2/66/60 out of 128. -/
def weighted (F : Nat → Nat → Nat → Nat → Nat) (r d e : Nat) : Nat :=
  2*F r 0 d e+66*F r 1 d e+60*F r 2 d e

/-- The root save 0/1/2/3 has weights 132/1044/1996/924 out of 4096 (`6/36/22 ⊗ 22/42`). -/
def topWeighted (F : Nat → Nat → Nat → Nat → Nat) (d e : Nat) : Nat :=
  132*weighted F 0 d e+1044*weighted F 1 d e+1996*weighted F 2 d e+924*weighted F 3 d e

theorem nested_eq (F : Nat → Nat → Nat → Nat → Nat) :
    nested F = 2^10 * (∑ d : Fin 2, ∑ e : Fin 2, topWeighted F d.val e.val) := by
  simp only [nested,sumB_eq,sumA_eq,sum128_eq,sum64_eq,topWeighted,weighted,Nat.reduceAdd]
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  ring

#print axioms nested_eq

def evalIndex (F : Nat → Nat → Nat → Nat → Nat) (n : Nat) : Nat :=
  F (saveA (n/524288) + saveB (n/33554432)) (oneSave (n/4096)) (pairSave (n/64)) (pairSave n)

theorem eval_join (F : Nat → Nat → Nat → Nat → Nat)
    (a b : Fin 64) (c : Fin 128) (d e : Fin 64) :
    evalIndex F (((((a.val*64+b.val)*128+c.val)*64+d.val)*64+e.val)) =
      F (saveA b.val + saveB a.val) (oneSave c.val) (pairSave d.val) (pairSave e.val) := by
  let n := ((((a.val*64+b.val)*128+c.val)*64+d.val)*64+e.val)
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  have h0 : n/524288%64=b.val%64 := by dsimp [n]; omega
  have h1' : n/33554432%64=a.val%64 := by dsimp [n]; omega
  have h2 : n/4096%128=c.val%128 := by dsimp [n]; omega
  have h3 : n/64%4=d.val%4 := by dsimp [n]; omega
  have h4 : n%4=e.val%4 := by dsimp [n]; omega
  change evalIndex F n = _
  unfold evalIndex
  rw [oneSave_mod128 (n/4096) c.val h2]
  simp only [saveA,saveB,pairSave,h0,h1',h3,h4]

theorem sum_split (n m : Nat) (f : Nat → Nat) :
    (∑ i : Fin (n*m), f i.val) = ∑ a : Fin n, ∑ b : Fin m, f (a.val*m+b.val) := by
  rw [← (finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin n, ∑ b : Fin m, f (b.val+m*a.val)) = _
  simp only [Nat.mul_comm, Nat.add_comm]

theorem index_nested (F : Nat → Nat → Nat → Nat → Nat) :
    (∑ i : Fin (2^31), evalIndex F i.val) = nested F := by
  let f0 := evalIndex F
  let f1 := fun n => ∑ e : Fin 64, f0 (n*64+e.val)
  let f2 := fun n => ∑ d : Fin 64, f1 (n*64+d.val)
  let f3 := fun n => ∑ c : Fin 128, f2 (n*128+c.val)
  let f4 := fun n => ∑ b : Fin 64, f3 (n*64+b.val)
  change (∑ i : Fin ((64*64*128*64)*64), f0 i.val) = _
  rw [sum_split (64*64*128*64) 64 f0]
  change (∑ i : Fin ((64*64*128)*64), f1 i.val) = _
  rw [sum_split (64*64*128) 64 f1]
  change (∑ i : Fin ((64*64)*128), f2 i.val) = _
  rw [sum_split (64*64) 128 f2]
  change (∑ i : Fin (64*64), f3 i.val) = _
  rw [sum_split 64 64 f3]
  dsimp only [f4,f3,f2,f1,f0]
  simp_rw [eval_join]
  unfold nested sumB sumA sum64 sum128
  rfl

theorem index_uniform (F : Nat → Nat → Nat → Nat → Nat) :
    (∑ i : Fin (2^31), evalIndex F i.val) =
      2^10 * (∑ d : Fin 2, ∑ e : Fin 2, topWeighted F d.val e.val) := by
  rw [index_nested,nested_eq]
#print axioms index_uniform
end ClaudeWCT.Numerics.LocalRouteUniform
