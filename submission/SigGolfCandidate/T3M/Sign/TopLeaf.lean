import SigGolfCandidate.T3M.Keygen.Leaf

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
structure LeafPreS (sk : BitVec 256) (s : MachineState) (A : LeafArgs) : Prop where
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
  hsl : A.so = false → A.lay ≠ 0
  hdig : ∀ i < A.n, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i)
  hdigb : ∀ i < A.n, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit A.lay i)
  hdigp : A.digp + A.n ≤ 2 ^ 24
  hdigW : ∀ i < A.n, ¬ LeafW A ((A.digp + i) / 8 * 8)
  hv8 : A.valp % 8 = 0
  hv : A.valp + 16 * A.n ≤ 2 ^ 24
  hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp
  hd8 : A.so = false → A.dest % 8 = 0
  hd : A.dest + 16 ≤ 2 ^ 24
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
  hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * A.n ≤ A.dest
theorem chainCount_low {lay : Layer} (h0 : lay ≠ 0) : chainCount lay = 43 := by
  revert h0; revert lay; decide
theorem leafInput_wordsS (A : LeafArgs) (h0 : A.lay ≠ 0) (ends : List Digest) (hlen : ends.length = A.n) :
    wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++
        [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) := by
  have hn : A.n = 43 := chainCount_low h0
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (A.n - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold T3.leafInput
  rw [if_neg h0, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length, hfl, hn]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length] <;> omega),
    wordsOf_append _ _ (by simp only [bytesLE_length] <;> omega), wordsOf_bytesLE16 (T3.leafTweak _ _ _)]
  unfold T3.leafTweak
  rw [T3.append64_low, BitVec.extractLsb'_append_eq_left]
  rfl
theorem leafInput_lengthS (A : LeafArgs) (h0 : A.lay ≠ 0) (ends : List Digest) (hlen : ends.length = A.n) :
    (pad64 (T3.leafInput A.lay A.tree A.leaf ends)).length = 64 * leafBlocks A.lay := by
  have hn : A.n = 43 := chainCount_low h0
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (A.n - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold T3.leafInput
  rw [if_neg h0, pad64_length, List.length_append, List.length_append, bytesLE_length, bytesLE_length, hfl]
  unfold leafBlocks
  rw [show chainCount A.lay = A.n from rfl, hn]
end SigGolfCandidate.T3M.Sign
