import SigGolfCandidate.T3M.Keygen.LeafBlocks

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
def n4 (lay : Layer) : Nat := if lay = 0 then 51 else 0
def leafBlocks (lay : Layer) : Nat := (16 * (chainCount lay + 1) + 63) / 64
theorem chainCount_cases (lay : Layer) : chainCount lay = 54 ∨ chainCount lay = 43 := by
  fin_cases lay <;> simp [chainCount]
theorem n4_le (lay : Layer) : n4 lay ≤ chainCount lay := by
  unfold n4; split_ifs with h
  · subst h; simp [chainCount]
  · omega
theorem maxDigit_shape (lay : Layer) (i : Nat) :
    maxDigit lay i = if lay = 0 then (if i < n4 lay then 4 else 7) else 7 := by
  unfold maxDigit n4
  split_ifs <;> rfl
def selectorExtra (lay : Layer) (i : Nat) : Nat :=
  if lay = 0 then (if i < n4 lay then 5 else 3) else 0
def slotK (lay : Layer) (i : Nat) : Nat := if lay = 0 then 1 else if i = 0 then 0 else 1
structure LeafArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  digits : List Nat
  so : Bool
  digp : Nat
  valp : Nat
  dest : Nat
  ret : Nat
namespace LeafArgs
variable (A : LeafArgs)
abbrev n : Nat := chainCount A.lay
abbrev d (i : Nat) : Nat := A.digits.getD i 0
def e (i : Nat) : Nat := if A.so then A.d i else maxDigit A.lay i
def iterK (i : Nat) : Nat :=
  21 + selectorExtra A.lay i + (if A.so then 1 else 0) + (rungK A.lay * A.e i + 10) +
    (if A.so then 0 else 11 + slotK A.lay i)
def iterC (i : Nat) : Nat :=
  21 + selectorExtra A.lay i + (if A.so then 1 else 0) + (rungC A.lay * A.e i + 10) +
    (if A.so then 0 else 11 + slotK A.lay i)
def pairK (p : Nat) : Nat :=
  19 + A.iterK (2 * p) + (if 2 * p + 1 < A.n then 3 + A.iterK (2 * p + 1) else 0)
def pairC (p : Nat) : Nat :=
  26 + A.iterC (2 * p) + (if 2 * p + 1 < A.n then 3 + A.iterC (2 * p + 1) else 0)
def pairN (p : Nat) : Nat := 1 + A.e (2 * p) + (if 2 * p + 1 < A.n then A.e (2 * p + 1) else 0)
def leafK : Nat := 14 + sumTo A.pairK ((A.n + 1) / 2) + (if A.so then 3 else 19)
def leafC : Nat := 14 + sumTo A.pairC ((A.n + 1) / 2) + (if A.so then 3 else 18 + 8 * leafBlocks A.lay)
def leafN : Nat := sumTo A.pairN ((A.n + 1) / 2) + (if A.so then 0 else 1)
def leafB : Nat := sumTo A.pairN ((A.n + 1) / 2) + (if A.so then 0 else leafBlocks A.lay)
end LeafArgs
def LeafW (A : LeafArgs) (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨
    ((if A.lay = 0 then LEAFPK + 16 else LEAFPK) ≤ X ∧ X < LEAFPK + 16 * (A.n + 2)) ∨
    (LOUT ≤ X ∧ X < LOUT + 32) ∨ (A.valp ≤ X ∧ X < A.valp + 16 * A.n) ∨ (A.dest ≤ X ∧ X < A.dest + 16)
def leafRegs : List Reg :=
  [.x1, .x3, .x6, .x7, .x10, .x11, .x12, .x17, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def slot (lay : Layer) (c : Nat) : Nat :=
  if lay = 0 then LEAFPK + 16 * (c + 2) else if c = 0 then LEAFPK else LEAFPK + 16 * (c + 1)
structure LeafPre (sk : BitVec 256) (s : MachineState) (A : LeafArgs) : Prop where
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x22 : s.getReg .x22 = BitVec.ofNat 64 A.digp
  x23 : s.getReg .x23 = BitVec.ofNat 64 A.valp
  x25 : s.getReg .x25 = BitVec.ofNat 64 A.dest
  x26 : s.getReg .x26 = BitVec.ofNat 64 A.n
  x27 : s.getReg .x27 = BitVec.ofNat 64 (n4 A.lay)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 31
  hleafHeight : A.leaf < 2 ^ T3.height A.lay
  hsteps : ∀ i < A.n, A.e i ≤ 8
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  z32 : s.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
  top0 : A.lay = 0 ∧ A.tree = 0
  zhead : s.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ s.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0
  hdig : ∀ i < A.n, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i)
  hdigb : ∀ i < A.n, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit A.lay i)
  hdigp : A.digp + A.n ≤ 2 ^ 24
  hdigW : ∀ i < A.n, ¬ LeafW A ((A.digp + i) / 8 * 8)
  hv8 : A.valp % 8 = 0
  hv : A.valp + 16 * A.n ≤ 2 ^ 24
  hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp
  hd8 : A.dest % 8 = 0
  hd : A.dest + 16 ≤ 2 ^ 24
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
  hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * A.n ≤ A.dest
structure LeafInv (s0 : MachineState) (A : LeafArgs) (j : Nat) (st : List Digest × List Digest)
    (t : MachineState) : Prop where
  x19 : t.getReg .x19 = BitVec.ofNat 64 j
  x23 : t.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j)
  x3 : t.getReg .x3 = pcOf A.ret
  regs : RegsExcept s0 t leafRegs
  frame : Frame s0 t (LeafW A)
  lh16 : t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf)
  lh24 : t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0
  elen : st.1.length = if A.so then 0 else j
  vlen : st.2.length = j
  ends : A.so = false → ∀ c < j, DigAt t (slot A.lay c) (st.1.getD c 0)
  vals : DigsAt t A.valp st.2
theorem slot_ge (lay : Layer) (c : Nat) : LEAFPK ≤ slot lay c := by unfold slot; split_ifs <;> omega
theorem slot_ge' (lay : Layer) (c : Nat) : (if lay = 0 then LEAFPK + 16 else LEAFPK) ≤ slot lay c := by
  unfold slot; split_ifs <;> omega
theorem slot_lt (lay : Layer) {c n : Nat} (hc : c < n) : slot lay c + 16 ≤ LEAFPK + 16 * (n + 2) := by
  unfold slot; split_ifs <;> omega
theorem slot_disj (lay : Layer) {c j : Nat} (h : c ≠ j) :
    slot lay c + 16 ≤ slot lay j ∨ slot lay j + 16 ≤ slot lay c := by
  unfold slot; split_ifs <;> omega
theorem slot_hdr (lay : Layer) (c : Nat) : slot lay c + 16 ≤ LEAFPK + 16 ∨ LEAFPK + 32 ≤ slot lay c := by
  unfold slot; split_ifs <;> omega
theorem slot_mod (lay : Layer) (c : Nat) : slot lay c % 8 = 0 := by
  unfold slot; split_ifs <;> simp only [LEAFPK] <;> omega
theorem LeafW_of_c48 {A : LeafArgs} {X : Nat} (h : X = CHAIN + 48 ∨ X = CHAIN + 56) : LeafW A X := by
  unfold LeafW; right; right; right; right; right; left; simp only [CHAIN] at h ⊢; omega
theorem LeafW_of_chainW {A : LeafArgs} {j X : Nat} (hj : j < A.n) (h : ChainW (A.valp + 16 * j) X) :
    LeafW A X := by
  unfold ChainW at h; unfold LeafW
  rcases h with h | h | h
  · rcases h with h | h
    · right; right; right; left; exact h
    · right; right; right; right; left; exact h
  · right; right; right; right; right; left; exact h
  · right; right; right; right; right; right; right; right; left; constructor <;> omega
theorem LeafW_of_slot {A : LeafArgs} {j X : Nat} (hj : j < A.n) (h : slot A.lay j ≤ X ∧ X < slot A.lay j + 16) :
    LeafW A X := by
  have := slot_ge' A.lay j; have := slot_lt A.lay hj
  unfold LeafW; right; right; right; right; right; right; left; constructor <;> omega
def chainProg (A : LeafArgs) (i : Nat) (seed : Digest) : T3.M (Digest × Digest) := do
  let v ← chain A.lay A.tree A.leaf i 0 (A.d i) seed
  let last ← chain A.lay A.tree A.leaf i (A.d i) (A.e i - A.d i) v
  pure (v, last)
def halfUpd (A : LeafArgs) (st : List Digest × List Digest) (r : Digest × Digest) :
    List Digest × List Digest :=
  if A.so then (st.1, st.2 ++ [r.1]) else (st.1 ++ [r.2], st.2 ++ [r.1])
def leafHalf (A : LeafArgs) (seeds : Digest × Digest) (pair : Nat) (state : List Digest × List Digest)
    (half : Nat) : T3.M (List Digest × List Digest) := do
  let i := 2*pair+half
  if chainCount A.lay ≤ i then return state
  let seed := if half = 0 then seeds.1 else seeds.2
  let digit := A.digits.getD i 0
  let value ← chain A.lay A.tree A.leaf i 0 digit seed
  if A.so then return (state.1, state.2 ++ [value])
  let last ← chain A.lay A.tree A.leaf i digit (maxDigit A.lay i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])
theorem buildLeaf_unfold (A : LeafArgs) : buildLeaf A.lay A.tree A.leaf A.digits A.so = (do
    let state ← (List.range ((chainCount A.lay + 1) / 2)).foldlM (fun state pair => do
      let seeds ← privatePair 0 A.lay.val A.tree pair A.leaf
      (List.range 2).foldlM (leafHalf A seeds pair) state) ([], [])
    if A.so then return (0, state.2)
    let root ← leafHash A.lay A.tree A.leaf state.1
    pure (root, state.2)) := rfl
theorem leafHalf_ge (A : LeafArgs) (seeds : Digest × Digest) (pair : Nat) (state : List Digest × List Digest)
    (half : Nat) (hi : A.n ≤ 2 * pair + half) : leafHalf A seeds pair state half = pure state := by
  unfold leafHalf; simp only [hi, if_true]
theorem chain_zero (lay : Layer) (tree leaf i start : Nat) (v : Digest) :
    chain lay tree leaf i start 0 v = pure v := rfl
theorem leafHalf_lt (A : LeafArgs) (seeds : Digest × Digest) (pair : Nat) (state : List Digest × List Digest)
    (half : Nat) (hi : 2 * pair + half < A.n)
    (hd : A.so = false → A.d (2 * pair + half) ≤ maxDigit A.lay (2 * pair + half)) :
    leafHalf A seeds pair state half =
      halfUpd A state <$> chainProg A (2 * pair + half) (if half = 0 then seeds.1 else seeds.2) := by
  unfold leafHalf chainProg halfUpd
  simp only [show ¬ chainCount A.lay ≤ 2 * pair + half from Nat.not_le.mpr hi, if_false]
  cases hso : A.so
  · simp only [Bool.false_eq_true, if_false, LeafArgs.e, hso, map_bind, map_pure]
  · simp only [if_true, LeafArgs.e, hso, Nat.sub_self, chain_zero, map_bind, pure_bind, map_pure]
theorem leafInput_words (A : LeafArgs) (h0 : A.lay = 0) (ends : List Digest) (hlen : ends.length = A.n) :
    wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf ends)) =
      [0, 0] ++ [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] ++
        wordsOf (ends.flatMap (bytesLE 16)) := by
  have hn54 : A.n = 54 := by show chainCount A.lay = 54; rw [h0]; rfl
  have hfl : (ends.flatMap (bytesLE 16)).length = 16 * A.n := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold T3.leafInput
  rw [if_pos h0, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length, T3.zero16, List.length_replicate, hfl, hn54]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length, T3.zero16, List.length_replicate] <;> omega),
    wordsOf_append _ _ (by simp only [T3.zero16, List.length_replicate] <;> omega), wordsOf_zero16, wordsOf_bytesLE16]
  unfold T3.leafTweak
  rw [T3.append64_low, BitVec.extractLsb'_append_eq_left]
  rfl
theorem leafInput_length (A : LeafArgs) (h0 : A.lay = 0) (ends : List Digest) (hlen : ends.length = A.n) :
    (pad64 (T3.leafInput A.lay A.tree A.leaf ends)).length = 64 * leafBlocks A.lay := by
  have hn54 : A.n = 54 := by show chainCount A.lay = 54; rw [h0]; rfl
  have hfl : (ends.flatMap (bytesLE 16)).length = 16 * A.n := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold T3.leafInput
  rw [if_pos h0, pad64_length]
  simp only [List.length_append, bytesLE_length, T3.zero16, List.length_replicate, hfl, hn54, leafBlocks,
    show chainCount A.lay = A.n from rfl]
/-- Retired in campaign T8D: the keygen top leaf (family seeds) is `buildLeafTop_tsim` in `T3M/Keygen/TopLeaf.lean`.
The name is kept because `T3M/Sign/PackedLowTree.lean` lists it in an `open` clause. -/
theorem buildLeaf_tsim : True := trivial
end SigGolfCandidate.T3M.Keygen
