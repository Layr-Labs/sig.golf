import Mathlib
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
open scoped BigOperators
open Finset
namespace ClaudeWCT.Numerics.LocalRouteUniform

def pairSave (n : Nat) : Nat := if n%4=1 ∨ n%4=2 then 1 else 0
def oneDiff (n : Nat) : Nat := ((n % 128) ^^^ ((n % 128) / 2)) % 64
def oneSave (n : Nat) : Nat := (if oneDiff n = 0 then 0 else 1) + (if oneDiff n % 2 = 1 ∧ 4 ≤ oneDiff n then 1 else 0)

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

theorem pair_zero_count : ((univ : Finset (Fin 64)).filter fun i => pairSave i.val=0).card=32 := by decide +kernel
theorem pair_one_count : ((univ : Finset (Fin 64)).filter fun i => pairSave i.val=1).card=32 := by decide +kernel
theorem one_zero_count : ((univ : Finset (Fin 128)).filter fun i => oneSave i.val=0).card=2 := by decide +kernel
theorem one_one_count : ((univ : Finset (Fin 128)).filter fun i => oneSave i.val=1).card=66 := by decide +kernel
theorem one_two_count : ((univ : Finset (Fin 128)).filter fun i => oneSave i.val=2).card=60 := by decide +kernel

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

def sum64 (f : Nat → Nat) : Nat := ∑ i : Fin 64, f (pairSave i.val)
def sum128 (f : Nat → Nat) : Nat := ∑ i : Fin 128, f (oneSave i.val)
theorem sum64_eq (f : Nat → Nat) : sum64 f=32*(f 0+f 1) := by
  unfold sum64
  rw [sum_binary (fun i : Fin 64 => pairSave i.val) (by intro i; unfold pairSave; split_ifs <;> omega)]
  rw [pair_zero_count,pair_one_count]
  omega

theorem oneSave_le_two (n : Nat) : oneSave n ≤ 2 := by
  unfold oneSave; split_ifs <;> omega

theorem sum128_eq (f : Nat → Nat) : sum128 f=2*f 0+66*f 1+60*f 2 := by
  unfold sum128
  rw [sum_ternary (fun i : Fin 128 => oneSave i.val) (fun i => oneSave_le_two _)]
  rw [one_zero_count,one_one_count,one_two_count]

def nested (F : Nat → Nat → Nat → Nat → Nat) : Nat :=
  sum64 fun a => sum64 fun b => sum128 fun c => sum64 fun d => sum64 fun e => F (a+b) c d e

theorem nested_eq (F : Nat → Nat → Nat → Nat → Nat) :
    nested F = 2^20 * (∑ a : Fin 2, ∑ b : Fin 2, ∑ d : Fin 2, ∑ e : Fin 2,
      (2*F (a.val+b.val) 0 d.val e.val + 66*F (a.val+b.val) 1 d.val e.val + 60*F (a.val+b.val) 2 d.val e.val)) := by
  simp only [nested,sum64_eq,sum128_eq]
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  ring

#print axioms nested_eq

def evalIndex (F : Nat → Nat → Nat → Nat → Nat) (n : Nat) : Nat :=
  F (pairSave (n/524288) + pairSave (n/33554432)) (oneSave (n/4096)) (pairSave (n/64)) (pairSave n)

theorem eval_join (F : Nat → Nat → Nat → Nat → Nat)
    (a b : Fin 64) (c : Fin 128) (d e : Fin 64) :
    evalIndex F (((((a.val*64+b.val)*128+c.val)*64+d.val)*64+e.val)) =
      F (pairSave b.val + pairSave a.val) (oneSave c.val) (pairSave d.val) (pairSave e.val) := by
  let n := ((((a.val*64+b.val)*128+c.val)*64+d.val)*64+e.val)
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  have h0 : n/524288%4=b.val%4 := by dsimp [n]; omega
  have h1 : n/33554432%4=a.val%4 := by dsimp [n]; omega
  have h2 : n/4096%128=c.val%128 := by dsimp [n]; omega
  have h3 : n/64%4=d.val%4 := by dsimp [n]; omega
  have h4 : n%4=e.val%4 := by dsimp [n]; omega
  change evalIndex F n = _
  simp only [evalIndex,pairSave,oneSave,oneDiff,h0,h1,h2,h3,h4]
  rfl

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
  unfold nested sum64 sum128
  simp only [Nat.add_comm]

theorem index_uniform (F : Nat → Nat → Nat → Nat → Nat) :
    (∑ i : Fin (2^31), evalIndex F i.val) =
      2^20 * (∑ a : Fin 2, ∑ b : Fin 2, ∑ d : Fin 2, ∑ e : Fin 2,
        (2*F (a.val+b.val) 0 d.val e.val + 66*F (a.val+b.val) 1 d.val e.val + 60*F (a.val+b.val) 2 d.val e.val)) := by
  rw [index_nested,nested_eq]
#print axioms index_uniform
end ClaudeWCT.Numerics.LocalRouteUniform
