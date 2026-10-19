import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PostEncW
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PadWit
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePassInit
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_CompactRun
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_ChoiceWord
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Compact2Wit
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_ComposeBack
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_H2Search
import SigGolfCandidate.ClaudeWCT_W9_T3M_Submission
import SigGolfCandidate.T3M_Submission
import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_Pending


set_option Elab.async false
set_option maxRecDepth 100000

section



namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_full window_zeros
  zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (regionBytes merkleBytes chainBytes leafBytes topBlockBytes merkleBytes_length
  chainBytes_length region_merkle region_top merkleBytes_sib topBlock_sib authByte5_none window_map_range zeros_len)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 wctBytesV6_length witListV6_length witListV5 wctBytesV5
  regionBytesV5 merkleBytesV5 merkleBytesV5_length regionBytesV6 regionBytesV6_length regionBytesV5_length
  wctBytesV5_length witListV5_length wordsOf_getD headerBytesV5
  headerBytesV5_length)
set_option linter.unusedSimpArgs false
theorem window_window (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem witList_head (o : Nat) (h : o + 8 ≤ 64) : window (witListV6 N w) o 8 = window (witListV5 N w) o 8 := by
  unfold witListV6 witListV5
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega)]
theorem witList_tail (o : Nat) (h : 8128 ≤ o) :
    window (witListV6 N w) o 8 = window (witListV5 N w) (o + 1152) 8 := by
  unfold witListV6 witListV5
  simp only [List.append_assoc]
  rw [window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega),
    window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
    window_append_right (wctBytesV6 N w.signature) _ _ _ (by rw [wctBytesV6_length]; omega),
    window_append_right (wctBytesV5 N w.signature) _ _ _ (by rw [wctBytesV5_length]; omega), wctBytesV6_length,
    wctBytesV5_length,
    show o + 1152 - 64 - 9216 = o - 64 - 8064 by omega]
end
/-- r3w: only the header and the layer/tail words of the staging are used downstream (its FTS content is dead). -/
theorem compact_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (hi : i < 2729) (hz : i < 8 ∨ 1016 ≤ i) :
    (wordsOf (witListV6 N w)).getD i 0 =
      finalWord (fun B => (wordsOf (witListV5 N w)).getD ((B - 0x800) / 8) 0)
        (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i := by
  have hW := witListV6_length N w
  have hV := witListV5_length N w
  rw [wordsOf_getD _ 2729 (by omega) i hi]
  unfold finalWord
  by_cases h8 : i < 8
  · rw [if_pos h8]
    beta_reduce
    rw [show (0x800 + 8 * i - 0x800) / 8 = i by omega, wordsOf_getD _ 2873 (by omega) i (by omega),
      witList_head N w _ (by omega)]
  rw [if_neg h8]
  rw [if_neg (show ¬ i < 1016 by omega)]
  beta_reduce
  rw [show (0x800 + 8 * (i + 144) - 0x800) / 8 = i + 144 by omega,
    wordsOf_getD _ 2873 (by omega) (i + 144) (by omega), witList_tail N w _ (by omega),
    show 8 * i + 1152 = 8 * (i + 144) by ring]
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
theorem lvSrc_val (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    SNAP2 + 8136 ≤ lvSrc lay j ∧ lvSrc lay j ≤ SNAP2 + 8136 + 64 * 171 ∧ (lvSrc lay j - SNAP2) % 8 = 0 := by
  have hS : SNAP2 = 0x310000 := rfl
  unfold lvSrc
  split_ifs <;> omega
theorem pathOut_congr (M M' : Nat → Word) (lay r p : Nat)
    (h : ∀ j < lvH lay, M (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j)) =
      M' (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j))) :
    pathOut M lay r p = pathOut M' lay r p := by
  unfold pathOut
  split_ifs
  · rfl
  · split
    · rename_i j hj
      exact h j (List.mem_range.mp (List.mem_of_find?_eq_some hj))
    · rfl
theorem index_shr (N : SigGolfCandidate.T3.HashOutput) :
    N.extractLsb' 0 64 >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex N) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero,
    BitVec.toNat_ofNat]
  unfold WCT9.digestIndex
  rw [Nat.mod_eq_of_lt (show N.toNat / 2 ^ 33 % 2 ^ 31 < 2 ^ 64 by omega)]
  rw [show (2 : Nat) ^ 64 = 2 ^ 33 * 2 ^ 31 by norm_num, Nat.mod_mul_right_div_self]
end ClaudeWCT.W9.Machine.Expand.Compact2
end


section










section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (KernAt)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK KernAt NODE NOUT EOUT DIGITS)
open SigGolfCandidate.T3M.Expand (IDXV lP lD lk lWC lWM RlWit lval lpath sideOff CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LInv LZero SigLayersAt HalfAt entryOf)
open SigGolfCandidate.T3M.Expand.BC (ltable ltable_lo ltable_disj rlWit_range)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests sigDigests_sigDec sigDigests_layValue sigDigests_layPath)
set_option linter.unusedSimpArgs false
theorem dword_of_halves (w : BitVec 64) :
    w = BitVec.ofNat 64 ((w.extractLsb' 0 32).toNat + 2 ^ 32 * (w.extractLsb' 32 32).toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h1 : w.toNat / 2 ^ 32 % 2 ^ 32 = w.toNat / 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  omega
theorem lD_cases (lay : Layer) : lD lay = 0x3ce8 ∨ lD lay = 0x4968 ∨ lD lay = 0x55a8 ∨ lD lay = 0x820 := by
  fin_cases lay <;> simp [lD]
theorem lk_zero (lay : Layer) : lk lay = 0 := by fin_cases lay <;> rfl
theorem lD_above (lay : Layer) (h : lay.val ≠ 0) : lD (Fin.ofNat 4 (lay.val - 1)) = lBase lay + 32 := by
  fin_cases lay <;> simp_all [lD, lBase] <;> rfl
theorem region_bounds (lay : Layer) : 0x2c48 ≤ lBase lay ∧ lBase lay + 64 * (height lay + chainCount lay) ≤ 0x61C8 := by
  fin_cases lay <;> decide
theorem lD_in_region (lay lay' : Layer) (A : Nat) (h1 : lBase lay ≤ A) (h2 : A < lBase lay + 64 * (height lay + chainCount lay))
    (he : A = lD lay') : A = lBase lay + 32 := by
  subst he
  fin_cases lay <;> fin_cases lay' <;> simp_all [lD, lBase, height, chainCount] <;> omega
theorem rlWit_region (lay lay' : Layer) (leaf A : Nat) (h1 : lBase lay ≤ A)
    (h2 : A < lBase lay + 64 * (height lay + chainCount lay)) (hne : lay' ≠ lay)
    (h : RlWit lay' leaf (lWC lay') (lWM lay') A) : False := by
  have hr := rlWit_range h
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  obtain ⟨hWM', hWC'⟩ := lBase_eq lay'
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  rcases ltable_disj lay' lay hne with hd | hd <;> omega
section run
variable {sk : BitVec 256}
end run
theorem readBuffer_foldl_mod (t : MachineState) (A n : Nat) : ∀ m, n ≤ m →
    (List.range m).foldl
        (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0 % 2 ^ (8 * n) =
      (List.range n).foldl
        (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0 % 2 ^ (8 * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega : 8 * n ≤ 8 * m)) _),
      Nat.add_zero, Nat.mod_mod, ih]
/-- Reading a buffer prefix: the first `n` bytes of a longer read. -/
theorem readBuffer_trunc (t : MachineState) (A n m : Nat) (h : n ≤ m) :
    readBuffer t A n = BitVec.ofNat (8 * n) (readBuffer t A m).toNat := by
  unfold readBuffer
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * n ≤ 8 * m)), readBuffer_foldl_mod t A n m h]
/- Witness trim: archived. After the trim the legacy (5310-byte) compactor no longer leaves the inner header at
the witness base (its counter copy at 1248, LE64(1) at 1240 and bit-6 = 1 top sibling at 1216 are now scratch
below `WIT = 1312`), so the full legacy readout `expqW_output` and the legacy `expandComposeSpec_holds` are no
longer derivable; they were only consumed by the archived 5310-byte bindings below. The paired chain
(`SharedCompactMain.finish_steps`) is unaffected.
/-- Expand writes 3116 whole words from 0x4c0; the 24924-byte witness is their prefix (the 4 bytes
after the 32-bit digest counter are zero and lie outside the witness). -/
theorem expqW_output {imgs : Phase → Image} {N : HashOutput} {w : WCT9.Witness} {t : MachineState}
    (h : t.readWords (BitVec.ofNat 64 0x4c0) 3116 = wordsOf (ClaudeWCT.W9.T3M.witList N w)) :
    readOutput (w9Sub imgs).sizes (w9Sub imgs).layout .expand t = ClaudeWCT.W9.T3M.witEnc N w := by
  show readBuffer t 0x4c0 24924 =
    BitVec.ofNat (8 * 24924) (SigGolfCandidate.T3.readLE (ClaudeWCT.W9.T3M.witList N w))
  rw [readBuffer_trunc t 0x4c0 24924 (8 * 3116) (by omega),
    readBuffer_of_words t 0x4c0 3116 (ClaudeWCT.W9.T3M.witList N w) (by decide) (by decide)
      (ClaudeWCT.W9.T3M.witList_length_eq N w) h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
set_option maxRecDepth 10000 in
theorem expandComposeSpec_holds : ExpandComposeSpec := by
  intro imgs hv hc hF hP hS hd hB
  have hsim : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 5310),
      Sim ((w9Sub imgs).image .expand) (w9init (imgs .expand) m pk σ) expCostW
        (mrealize 0 (ClaudeWCT.W9.T3M.expandN m pk (ClaudeWCT.W9.T3M.sigDecC σ))) ExpQW :=
    fun m pk σ => expandW_tbsim (sk := 0) hc hF hP hS hd hB m pk σ
  refine ⟨fun m pk σ => ?_, fun hash m pk σ => ?_⟩
  · exact Sim.run_eq (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ) (hsim m pk σ)
      (Nat.lt_of_succ_lt expCostW_lt) _ (expqW_halt imgs hc hB)
  · obtain ⟨h1, h2⟩ := Sim.runWith (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ)
      (hsim m pk σ) expCostW_lt (fun a t h => ⟨(expqW_halt imgs hc hB a t h).1, (expqW_halt imgs hc hB a t h).2.1⟩) hash
    exact ⟨h1, lt_of_le_of_lt h2 expCostW_lt⟩
-/
end ClaudeWCT.W9.Machine.Expand
end
/- Archived concrete 5310-byte image bindings. The paired image is bound below.
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Expand (expChunks)
set_option maxRecDepth 100000
end SigGolfCandidate.T3M.Expand
end
-/
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
end ClaudeWCT.W9.Machine.Expand
end
/- Archived 5310-byte export for the former concrete image.
section
namespace ClaudeWCT.W9.Machine.ExpandLink
open SigGolfCandidate.T3M
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
end ClaudeWCT.W9.Machine.ExpandLink
end
-/
end

namespace ClaudeWCT.W9.Machine.Expand.SharedWitnessOutput
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem words_map (t : MachineState) (A : Nat) : ∀n,
    t.readWords (BitVec.ofNat 64 A) n=(List.range n).map (fun j=>t.getMem (BitVec.ofNat 64 (A+8*j)))
  | 0 => rfl
  | n+1 => by
    rw [readWords_add,words_map t A n,readWords_one,List.range_succ,List.map_append]
    rfl

theorem readBuffer_words (t : MachineState) (A n m : Nat) (b : BitVec (8*n))
    (hal : A%8=0) (haddr : A+8*m<2^64) (hsize : n≤8*m)
    (hw : ∀k,k < m → t.getMem (BitVec.ofNat 64 (A+8*k))=b.extractLsb' (64*k) 64) :
    readBuffer t A n=b := by
  let b' : BitVec (8*(8*m)):=b.setWidth _
  have hw' : t.readWords (BitVec.ofNat 64 A) m=wordsOf (SphincsSecurity.bytesLE (8*m) b') := by
    rw[words_map,wordsOf_bytesLE]
    apply List.map_congr_left
    intro k hk
    rw[show b'.extractLsb' (64*k) 64=b.extractLsb' (64*k) 64 from
      BitVec.extractLsb'_setWidth_of_le (by have h:=List.mem_range.mp hk;omega)]
    exact hw k (List.mem_range.mp hk)
  have h:=readBuffer_of_words t A m (SphincsSecurity.bytesLE (8*m) b') hal haddr
    (by rw[SphincsSecurity.bytesLE_length]) hw'
  rw[readLE_bytesLE] at h
  rw[readBuffer_trunc t A n (8*m) hsize,h]
  apply BitVec.eq_of_toNat_eq
  simp only[BitVec.toNat_ofNat,BitVec.toNat_setWidth,b',Nat.mod_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8*n≤8*(8*m))),
    Nat.mod_eq_of_lt b.isLt]
#print axioms readBuffer_words
end ClaudeWCT.W9.Machine.Expand.SharedWitnessOutput

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput route)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem leafOf_output (output : HashOutput) :
    PostPass.leafOf (output.extractLsb' 0 64) % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096 := by
  unfold PostPass.leafOf SigGolfCandidate.T3.route WCT9.digestIndex
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have h : ∀ o : Nat, o % 2^64 / 2^52 % 4096 = o / 2^33 % 2^31 / 2^19 % 2^(SigGolfCandidate.T3.height 0) % 4096 := by
    intro o
    rw [show SigGolfCandidate.T3.height 0 = 12 by decide]
    norm_num
    omega
  simpa using h output.toNat

/-- img-v6 phase-1 witness image at the post-pass entry 49400 (r3w post-pass plan U4b; `PostEnc.pp_witEnc`):
FTS block = new `Paired.witEnc` words, old-layout region = `OldW.witList` words, choice word, digest leaf word. -/
structure Phase1 (output : HashOutput) (w : SharedForest.Witness) (s : MachineState) : Prop where
  fts : ∀ j, j < 958 → s.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = (Paired.witEnc output w).extractLsb' (64 * j) 64
  old : ∀ j, 1012 ≤ j → j < 2905 → j ≠ 2789 →
    s.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = PostEnc.oldWord output (Paired.mainWitness w) (8 * j)
  choice : s.getMem (BitVec.ofNat 64 (2904 + 8 * 2789)) =
    replaceByte (PostEnc.oldWord output (Paired.mainWitness w) (8 * 2789)) 0 (choiceByte w.topHigh).toBitVec
  leaf : PostPass.leafOf (s.getMem (BitVec.ofNat 64 0x20160)) % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096

theorem NoncesAt.frame {s t : MachineState} {n : List Nat} {l : Nat} {W : Nat → Prop}
    (h : SigGolfCandidate.T3M.Expand.NoncesAt s n l) (hf : Frame s t W)
    (hW : ∀ A, 0x66700 ≤ A → A < 0x66760 → ¬W A) : SigGolfCandidate.T3M.Expand.NoncesAt t n l :=
  ⟨h.1, fun k hk => (hf.get (by omega) (hW _ (by omega) (by omega))).trans (h.2.1 k hk),
    (hf.get (by omega) (hW _ (by omega) (by omega))).trans h.2.2⟩

/-- Cycles of the img-v6 witness tail: post-pass (49400 -> 54174) + pad writer hook (54174 -> 45016). -/
def suffixW : Nat := PostPass.ppCycles + 68
#print axioms leafOf_output
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem scatter_finish_readout {im : Image} (hc : ∀k:Fin 9,CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) afterCode) (hf : CodeAt im (pcOf 47005) finishCode)
    (he : CodeAt im (pcOf 43071) endCode)
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec48.CBytes)
    (s : MachineState) (hp : s.pc=pcOf 45257)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec48.sigDecC b).forest)
    (hraw : RawAt s (SharedForest.rawChildFromOutput output)) (hplan : PlanAt s)
    (hmode : s.getMem 417824=1)
    (hc3 : s.getMem 417816=(witness.counters 3).setWidth 64)
    (hz : ∀ (off : Nat), off+8≤8096 → off%8=0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (htail : ∀ (j : Nat), 1012≤j → j<2905 → j≠2789 → s.getMem (BitVec.ofNat 64 (2904+8*j))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*j))
    (hchoice : s.getMem (BitVec.ofNat 64 (2904+8*2789))=PostEnc.oldWord output (Paired.mainWitness witness) (8*2789))
    (hflag : s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0)) :
    ∃v,Steps im s 1269 1446 v ∧ v.pc=pcOf 49400 ∧ v.getReg .x5=1 ∧
      (∀ j, j < 958 → v.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = (Paired.witEnc output witness).extractLsb' (64 * j) 64) ∧
      (∀ j, 1012 ≤ j → j < 2905 → j ≠ 2789 →
        v.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = PostEnc.oldWord output (Paired.mainWitness witness) (8 * j)) ∧
      v.getMem (BitVec.ofNat 64 (2904 + 8 * 2789)) =
        replaceByte (PostEnc.oldWord output (Paired.mainWitness witness) (8 * 2789)) 0 (choiceByte witness.topHigh).toBitVec ∧
      Frame s v (fun A=>ScatterW A ∨ A=25216) := by
  obtain ⟨t,st,ht⟩:=scatter_steps hc s _ hraw hplan hp
  obtain ⟨u,tu,up,ur,uf⟩:=after_steps ha t ht.pc
  have hm:t.getMem 417824=1:=
    (ht.frame.get (A:=417824) (by decide) (by unfold ScatterW;omega)).trans hmode
  have up':u.pc=pcOf 47005:=by simpa only [hm,if_neg (show (1:BitVec 64)≠0 by decide)] using up
  have u8:u.getReg .x8=BitVec.ofNat 64 2984:=by rw [ur.get (by decide),ht.x8 (by decide)];rfl
  obtain ⟨v,uv,vp,vc,vpad,vchoice,v5,v10,vr,vf⟩:=finish_steps hf he u up' u8
  have hcounter:v.getMem (BitVec.ofNat 64 2936)=(witness.counters 3).setWidth 64:=by
    exact vc.trans ((uf.get (A:=417816) (by decide) (by tauto)).trans
      ((ht.frame.get (A:=417816) (by decide) (by unfold ScatterW;omega)).trans hc3))
  have hframe:Frame s v (fun A=>ScatterW A ∨ A=25216):=((ht.frame.trans uf).trans vf).mono (by
    intro A hA hw
    rcases hw with (hw|hw)|hw
    · exact Or.inl hw
    · exact hw.elim
    · rcases hw with hw|hw|hw
      · left; unfold ScatterW;omega
      · left; unfold ScatterW;omega
      · exact Or.inr hw)
  have hfl : flagByte u=(choiceByte witness.topHigh).toBitVec := by
    have hflag' : s.getMem (BitVec.ofNat 64 0x667F8)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0) := hflag
    unfold flagByte
    rw [uf.get (A:=0x667F8) (by decide) (by simp),ht.frame.get (A:=0x667F8) (by decide) (by unfold ScatterW;omega),hflag']
    cases witness.topHigh <;> decide
  have hw25 : u.getMem (BitVec.ofNat 64 25216)=s.getMem (BitVec.ofNat 64 25216) :=
    (uf.get (by norm_num) (by simp)).trans (ht.frame.get (by norm_num) (by unfold ScatterW;omega))
  -- Stage 2 (C3): the final pass restores the counter word (`off = 32`) and the row-tweak pad (`off = 24`); every
  -- other prefix word is the scatter's original word.
  have hprefix : ∀ (off:Nat), off+8≤7664 → off%8=0 →
      W9Machine.OrigWD 1224 (Paired.witEnc output witness) v (2904+off) := by
    intro off hb hal
    unfold W9Machine.OrigWD
    rw [show 2904+off+1224-0x1020=off by omega]
    by_cases h32:off=32
    · subst off
      rw [Paired.counterWord_witEnc]
      exact hcounter
    by_cases h24:off=24
    · subst off
      rw [SharedScatter.witPad24_witEnc]
      exact vpad
    have ho:=ScatterInv.original_prefix_forest output witness b s t hin hforest ht hz off hb hal (Or.inl h32) h24
    unfold W9Machine.OrigWD at ho
    rw [show 2904+off+1224-0x1020=off by omega] at ho
    rw [vf.get (A:=2904+off) (by omega) (by omega)]
    exact (uf.get (by omega) (by tauto)).trans ho
  refine ⟨v,(st.trans tu).trans uv,vp,v5,?_,?_,?_,hframe⟩
  · intro j hj
    have hh:=hprefix (8*j) (by omega) (by omega)
    simpa only [W9Machine.OrigWD,show 2904+8*j+1224-0x1020=8*j by omega,
      show 8*(8*j)=64*j by omega] using hh
  · intro j hj hj' hc
    have hm':v.getMem (BitVec.ofNat 64 (2904+8*j))=s.getMem (BitVec.ofNat 64 (2904+8*j)):=
      hframe.get (by omega) (by unfold ScatterW;omega)
    exact hm'.trans (htail j hj hj' hc)
  · rw [show (2904:Nat)+8*2789=25216 by norm_num, vchoice, hw25, hfl]
    rw [show (25216:Nat)=2904+8*2789 by norm_num, hchoice]
#print axioms scatter_finish_readout
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem PlanAt.frame {s t:MachineState} {W:Nat → Prop} (h:PlanAt s) (hf:Frame s t W)
    (hn:∀A,16748424≤A → A<16748600 → ¬W A) : PlanAt t := by
  intro child j hj
  have hm:=Nat.mod_lt child.val (by decide:0<32)
  exact (hf.getByte (by omega) (hn _ (by omega) (by omega))).trans (h child j hj)

theorem rawAt_of_output (s:MachineState) (output:HashOutput) (ho:OutAt s NBUF output) :
    RawAt s (SharedForest.rawChildFromOutput output) := by
  intro k
  convert SharedDispatch.raw_output s output ho k using 1 <;> fin_cases k <;> rfl

theorem clear_scatter_finish {im:Image} (hz:SharedZero.ClearCode im)
    (hc:∀k:Fin 9,CoordinateCode im k.val) (ha:CodeAt im (pcOf 46509) afterCode)
    (hf:CodeAt im (pcOf 47005) finishCode) (he:CodeAt im (pcOf 43071) endCode)
    (output:HashOutput) (witness:SharedForest.Witness) (b:SharedCodec48.CBytes)
    (s:MachineState) (hp:s.pc=pcOf 46980) (hin:SharedCompact.ForestAt s b)
    (hforest:witness.signature.forest=(SharedCodec48.sigDecC b).forest)
    (hplan:PlanAt s) (hout:OutAt s 96 output)
    (hc3:s.getMem 1184=(witness.counters 3).setWidth 64)
    (htail:∀ (j:Nat),1012≤j → j<2905 → j≠2789 → s.getMem (BitVec.ofNat 64 (2904+8*j))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*j))
    (hchoice:s.getMem (BitVec.ofNat 64 (2904+8*2789))=PostEnc.oldWord output (Paired.mainWitness witness) (8*2789))
    (hflag:s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0)) :
    ∃v,Steps im s 4984 5161 v ∧ v.pc=pcOf 49400 ∧ v.getReg .x5=1 ∧
      ClaudeWCT.W9.Machine.Expand.SharedCompactMain.Phase1 output witness v ∧
      (∀ A, 0x66700 ≤ A → A < 0x66760 → v.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨t,st,tp,tzero,tctr,tmode,tdigest,tr,tf⟩:=SharedZero.final_clear hz s hp
  have tin:SharedCompact.ForestAt t b:=hin.frame tf (by intros A hA hB hw;omega)
  have tplan:PlanAt t:=hplan.frame tf (by intros A hA hB hw;omega)
  have tout:OutAt t NBUF output:=by
    intro k hk
    exact (tdigest k hk).trans (hout k hk)
  obtain ⟨v,tv,vp,v5,vfts,vold,vch,vf⟩:=scatter_finish_readout hc ha hf he output witness b t tp tin hforest
    (rawAt_of_output t output tout) tplan tmode (tctr.trans hc3)
    (by intro off hb hal;exact tzero _ (by omega) (by omega) (by omega)) (by
      intro j hj hbound hne
      exact (tf.get (by omega) (by omega)).trans (htail j hj hbound hne))
    ((tf.get (by omega) (by omega)).trans hchoice)
    ((tf.get (by decide) (by unfold Search.FLAG; omega)).trans hflag)
  refine ⟨v,st.trans tv,vp,v5,⟨vfts,vold,vch,?_⟩,?_⟩
  · have h0 : v.getMem (BitVec.ofNat 64 0x20160)=output.extractLsb' 0 64 := by
      rw [vf.get (by decide) (by unfold ScatterW; omega)]
      exact tout 0 (by decide)
    rw [h0]
    exact ClaudeWCT.W9.Machine.Expand.SharedCompactMain.leafOf_output output
  · intro A h1 h2
    rw [vf.get (by omega) (by unfold ScatterW; omega), tf.get (by omega) (by omega)]
#print axioms PlanAt.frame
#print axioms rawAt_of_output
#print axioms clear_scatter_finish
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window zeros wordsOf)
open ClaudeWCT.W9.T3M (leafBufferSlot leafBufferBase)
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
theorem out2old_main_congr (M M' : Nat → Word) (h : ∀ x < 8 * 2729, x % 8 = 0 → (x ≤ 16 ∨ 8136 ≤ x) → M (WIT + x) = M' (WIT + x))
    (idx o : Nat) (hlo : 8952 ≤ o) (ho : o % 8 = 0) : out2old M idx o = out2old M' idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have e : ∀ A, WIT ≤ A → A - WIT < 8 * 2729 → (A - WIT) % 8 = 0 → (A - WIT ≤ 16 ∨ 8136 ≤ A - WIT) → M A = M' A := fun A h1 h2 h3 h4 => by
    have := h (A - WIT) h2 h3 h4
    rwa [show WIT + (A - WIT) = A by omega] at this
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  have hz : (zoneLay o = 1 ∧ o < 15824) ∨ (zoneLay o = 2 ∧ 15824 ≤ o ∧ o < 18392) ∨
      (zoneLay o = 3 ∧ 18392 ≤ o) := by
    unfold zoneLay; split_ifs <;> omega
  have hzl : 1 ≤ zoneLay o ∧ zoneLay o < 4 := by omega
  have hpt : pathTop (zoneLay o) ≤ 400 := by unfold pathTop; split_ifs <;> omega
  have hcs : 8136 ≤ chSrc (zoneLay o) - SNAP2 ∧ chSrc (zoneLay o) - SNAP2 + 2752 ≤ 8 * 2729 ∧
      (chSrc (zoneLay o) - SNAP2) % 8 = 0 ∧ SNAP2 ≤ chSrc (zoneLay o) := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> decide
  have hdl : (lvDst (zoneLay o) - WIT) % 8 = 0 := by
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> omega
  have hso : ∀ r, PairCopy.srcOff r ≤ 120 ∧ PairCopy.srcOff r % 8 = 0 := by
    intro r; unfold PairCopy.srcOff; split_ifs <;> omega
  unfold out2old
  rw [if_neg (show ¬ o < 8952 by omega), if_neg (show ¬ o < 8952 by omega)]
  by_cases h3 : o < 13176
  · rw [if_pos h3, if_pos h3]; exact e _ (by omega) (by omega) (by omega) (by omega)
  rw [if_neg h3, if_neg h3]
  by_cases h4 : o < 20960
  · rw [if_pos h4, if_pos h4]
    by_cases h5 : o - (lvDst (zoneLay o) - WIT) < pathTop (zoneLay o)
    · rw [if_pos h5, if_pos h5]
      apply pathOut_congr
      intro j hj
      obtain ⟨s1, s2, s3⟩ := lvSrc_val (zoneLay o) j hzl
      exact e _ (by omega) (by omega) (by omega) (by omega)
    · rw [if_neg h5, if_neg h5]
      unfold chOut
      have := hso ((o - (chDst (zoneLay o) - WIT)) % 104)
      by_cases q1 : o - (chDst (zoneLay o) - WIT) < 2184 ∧ PairCopy.isVal ((o - (chDst (zoneLay o) - WIT)) % 104)
      · rw [if_pos q1, if_pos q1]; exact e _ (by omega) (by omega) (by omega) (by omega)
      rw [if_neg q1, if_neg q1]
      by_cases q2 : o - (chDst (zoneLay o) - WIT) = 2232 ∨ o - (chDst (zoneLay o) - WIT) = 2240
      · rw [if_pos q2, if_pos q2]; exact e _ (by omega) (by omega) (by omega) (by omega)
      · rw [if_neg q2, if_neg q2]
  rw [if_neg h4, if_neg h4]
  by_cases h6 : o = 20960
  · rw [if_pos h6, if_pos h6]; exact e _ (by omega) (by omega) (by omega) (by omega)
  rw [if_neg h6, if_neg h6]
  by_cases h7 : o = 20968
  · rw [if_pos h7, if_pos h7]; exact e _ (by omega) (by omega) (by omega) (by omega)
  rw [if_neg h7, if_neg h7]
  by_cases h8 : o = 20976
  · rw [if_pos h8, if_pos h8]
  rw [if_neg h8, if_neg h8, e _ (by omega) (by omega) (by omega) (by omega)]

#print axioms out2old_main_congr
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem plMem_counter (M : Nat → Word) (Q : Nat) (hQ : Q ≤ 9) : plMem M Q 1184 = M 1184 := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    have hm:=Nat.min_le_right (M (Compact.holdAt Q + 16)).toNat 1
    have hb : 896*Q ≤ 8384 := by omega
    unfold plMem hslot hdst
    rw [if_neg (by omega),if_neg (by omega)]
    exact ih (by omega)

theorem stMem_counter (M : Nat → Word) : stMem M 1184 = M (WIT+32) := by
  unfold stMem
  rw [plMem_counter _ 9 le_rfl]
  unfold regsMem ctrMem
  rw [if_neg (by norm_num),if_pos (by norm_num)]
  unfold zMem snapMem WZ SNAP2 WIT
  norm_num

theorem run2Mem_counter (M : Nat → Word) (idx : Nat) : run2Mem M idx 1184 = M (WIT+32) := by
  have hw : WIT = 2048 := rfl
  unfold run2Mem tailMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),lays_low _ idx _ (by omega)]
  unfold topMem
  rw [if_neg (by omega),stMem_counter]

theorem bufferMem_counter (M : Nat → Word) : Buffer.bufferMem M 1184 = M 1184 :=
  bufferMem_low M 1184 (by norm_num) (by norm_num)

#print axioms run2Mem_counter
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem stMem_keep (M : Nat → Word) (A : Nat)
    (hA : A < 1152 ∨ 26144 ≤ A) (hSnap : A < SNAP2 ∨ SNAP2+8*2729 ≤ A) : stMem M A = M A := by
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem snapMem
  have hs : SNAP2 = 0x310000 := rfl
  have hw : WZ = 1152 := rfl
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem run2Mem_keep (M : Nat → Word) (idx A : Nat)
    (hA : A < 1152 ∨ 26144 ≤ A) (hSnap : A < SNAP2 ∨ SNAP2+8*2729 ≤ A) : run2Mem M idx A = M A := by
  have hw : WIT = 2048 := rfl
  obtain ⟨d1,d2,d3,c1,c2,c3⟩ := lay_consts
  unfold run2Mem tailMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    layMem_out _ 3 (by omega) idx A (by omega),
    layMem_out _ 2 (by omega) idx A (by omega),
    layMem_out _ 1 (by omega) idx A (by omega)]
  unfold topMem
  rw [if_neg (by omega),stMem_keep M A hA hSnap]

theorem bufferMem_keep (M : Nat → Word) (A : Nat) (hA : A < 1152 ∨ 26144 ≤ A) :
    Buffer.bufferMem M A = M A := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

#print axioms run2Mem_keep
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 1000000

theorem finalWord_main_congr (M M' : Nat → Word) (cs : Nat → Nat)
    (h : ∀ i < 2873, (i ≤ 4 ∨ 1161 ≤ i) → M (0x800+8*i)=M' (0x800+8*i))
    (i : Nat) (hi : i < 2729) (hmain : i ≤ 4 ∨ 1017 ≤ i) :
    finalWord M cs i=finalWord M' cs i := by
  rcases hmain with hsmall | hlarge
  · simp only [finalWord,if_pos (show i<8 by omega)]
    exact h i (by omega) (Or.inl hsmall)
  · simp only [finalWord,if_neg (show ¬i<8 by omega),if_neg (show ¬i<1016 by omega)]
    exact h (i+144) (by omega) (Or.inr (by omega))
#print axioms finalWord_main_congr
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def Protected (A : Nat) : Prop :=
  (A < 1152 ∨ 26144 ≤ A) ∧
  (((A < Compact.SNAP ∨ Compact.SNAP+9216 ≤ A) ∧
    (A < Compact2.SNAP2 ∨ Compact2.SNAP2+8*2729 ≤ A) ∧ ¬Compact.InHold 9 A) ∧
    ¬ (Compact2.Buffer.Post.SCR ≤ A ∧ A < Compact2.Buffer.Post.SCR+192))

theorem compact_main_steps {im : Image} (hc : CompactCodeAt im)
    (N : HashOutput) (w : WCT9.Witness) (s : MachineState) (hpc : s.pc = pcOf 41108)
    (hN : OutAt s 96 N) (hp : PlanAt s) (hlp : Compact2.LPlanAt s) (htp : Compact2.TopTabAt s)
    (hmain : ∀ i < 2873, (i ≤ 4  ∨  1161 ≤ i)  →  s.getMem (BitVec.ofNat 64 (2048+8*i))=(wordsOf (witListV5 N w)).getD i 0) :
    ∃ t, Steps im s 65987 65987 t  ∧  t.pc = pcOf 43761  ∧
      (∀ i,1012 ≤ i  →  i < 2905  →  t.getMem (BitVec.ofNat 64 (2904+8*i))=(wordsOf (ClaudeWCT.W9.Machine.Expand.OldW.witList N w)).getD i 0)  ∧
      t.getMem (BitVec.ofNat 64 1184)=s.getMem (BitVec.ofNat 64 2080)  ∧
      (∀ A < 2^64, Protected A  →  t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨v,sv,pv,rv,mv,mhv,fv⟩ := Compact.run_spec_framed hc N s hpc hN hp
  have hix : v.getMem (BitVec.ofNat 64 96) >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex N) := by
    rw [fv 96 (by norm_num) (Or.inl (by norm_num)) (Or.inl (by decide)) (by unfold Compact.InHold;omega)]
    have h0:=hN 0 (by norm_num)
    rw [Nat.mul_zero,Nat.add_zero] at h0
    rw [h0]
    exact Compact2.index_shr N
  have hlv : Compact2.LPlanAt v := by
    intro k hk
    rw [fv _ (by unfold Compact2.LPLAN;omega) (Or.inr (by unfold Compact2.LPLAN;omega))
      (Or.inr (by unfold Compact2.LPLAN Compact.SNAP;omega)) (by unfold Compact2.LPLAN Compact.InHold;omega)]
    exact hlp k hk
  have hfl : ∀ c < 9, ∃f < 2, v.getMem (BitVec.ofNat 64 (Compact.holdAt c+16))=BitVec.ofNat 64 f := by
    intro c hc9
    refine ⟨1-(N.toNat/2^WCT9.childBase c%128)/2^6%2,by omega,?_⟩
    rw [show Compact.holdAt c+16 = Compact.holdAt c+8*2 by omega,mhv c hc9 2 (by omega)]
    simp only [Compact.holdVal,if_neg (by decide : ¬(2:Nat)=0),if_neg (by decide : ¬(2:Nat)=1)]
  obtain ⟨u,su,pu,mu⟩ := Compact2.run2_spec hc v pv (WCT9.digestIndex N) (WCT9.digestIndex_lt N) hix hlv hfl
  have hv6 : ∀ x < 8*2729,x%8 = 0  →  (x ≤ 16  ∨  8136 ≤ x)  →
      v.getMem (BitVec.ofNat 64 (Compact2.WIT+x))=Compact2.v6M N w (Compact2.WIT+x) := by
    intro x hx h8 hzone
    obtain ⟨i,rfl⟩ : ∃i,x = 8*i := ⟨x/8,by omega⟩
    rw [show Compact2.WIT = 2048 from rfl,mv i (by omega) (by omega)]
    unfold Compact2.v6M
    rw [show (2048+8*i-Compact2.WIT)/8 = i by unfold Compact2.WIT;omega,Compact.compact_words N w i (by omega) (by omega)]
    apply Compact.finalWord_main_congr _ _ _ (fun j hj hm => ?_) i (by omega) (by omega)
    rw [hmain j hj hm,show (2048+8*j-2048)/8 = j by omega]
  have hout : ∀ o, o < 20136 → o % 8 = 0 → 8096 ≤ o → u.getMem (BitVec.ofNat 64 (2904 + o)) =
      Compact2.out2old (Compact2.v6M N w) (WCT9.digestIndex N) (o + 856) := by
    intro o ho h8 hlo
    rw [mu _ (by omega), show 2904 + o = Compact2.WOUT + o from rfl, Compact2.run2_zone _ _ _ ho h8]
    unfold Compact2.out2
    rw [if_neg (by omega)]
    exact Compact2.out2old_main_congr _ _ hv6 _ _ (by omega) (by omega)
  have hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 → u.getMem (BitVec.ofNat 64 (2904 + o)) =
      BitVec.ofNat 64 (SigGolfCandidate.T3.readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)) := by
    intro o h1 h2 h8
    obtain ⟨i, rfl⟩ : ∃ i, o = 8 * i := ⟨o / 8, by omega⟩
    rw [hout _ (by omega) h8 (by omega), Compact2.compact2_words N w i h1 h2]
  have hT : ∀ t < 4, u.getMem (BitVec.ofNat 64 (23008 + 8 * t)) =
      BitVec.ofNat 64 (SigGolfCandidate.T3.readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)) := by
    intro t ht
    rw [show 23008 + 8 * t = 2904 + (20104 + 8 * t) by omega, hout _ (by omega) (by omega) (by omega),
      show 20104 + 8 * t + 856 = 20960 + 8 * t by omega, Compact2.tail_words N w t ht]
  have hold : ∀ q < 96, u.getMem (BitVec.ofNat 64 (11000 + 8 * q)) =
      BitVec.ofNat 64 (SigGolfCandidate.T3.readLE (window (layerRegionV6 N w 0) (8 * q) 8)) := by
    intro q hq
    rw [show 11000 + 8 * q = 2904 + 8 * (1012 + q) by omega, hout _ (by omega) (by omega) (by omega),
      Compact2.compact2_top_old N w (1012 + q) (by omega) (by omega), show 8 * (1012 + q) - 8096 = 8 * q by omega]
  have beforeKeep : ∀ A < 2^64, Protected A → u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hkeep
    rw [mu A hA,Compact2.run2Mem_keep _ _ A hkeep.1 hkeep.2.1.2.1]
    exact fv A hA (by rcases hkeep.1 with h | h <;> omega) hkeep.2.1.1 hkeep.2.1.2.2
  have htab : Compact2.TopTabAt u := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [beforeKeep _ (by unfold Compact2.TOPA;omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.TOPA Compact2.Buffer.Post.SCR;omega)]
      exact htp.1 k hk
    · rw [beforeKeep _ (by unfold Compact2.TOPB;omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.TOPB Compact2.Buffer.Post.SCR;omega)]
      exact htp.2 k hk
  have hleaf : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2^19 := by
    have := WCT9.digestIndex_lt N
    change WCT9.digestIndex N / 2^19 % 2^12 = _
    omega
  have hl : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 < 4096 := by
    rw [hleaf];have := WCT9.digestIndex_lt N;omega
  have hix52 : u.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 := by
    rw [beforeKeep 96 (by decide) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;decide)]
    rw [hN 0 (by decide), show (52:Nat)=33+19 from rfl, BitVec.shiftRight_add, Compact2.index_shr, hleaf,
      SigGolfCandidate.T3M.ofNat_shr _ _ (by have := WCT9.digestIndex_lt N;omega)]
  obtain ⟨q,tq,pq,mq⟩ := Compact2.Buffer.bufferPost_prefix_spec hc u pu _ hl hix52 htab
  refine ⟨q,((sv.trans su).trans tq).of_eq (by norm_num) (by norm_num),pq,?_,?_,?_⟩
  · intro i hi hi'
    rw [mq _ (by omega) (by unfold Compact2.Buffer.Post.SCR;omega)]
    exact Compact2.postMem_words N w _ hM hT hold i hi hi'
  · rw [mq _ (by decide) (by unfold Compact2.Buffer.Post.SCR;decide),
      Compact2.Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by decide),
      Compact2.bufferMem_counter, mu _ (by norm_num), Compact2.run2Mem_counter,
      show Compact2.WIT+32=2048+8*4 from rfl, mv 4 (by norm_num) (by norm_num)]
    simp only [Compact.finalWord,if_pos (by decide : (4:Nat)<8)]
  · intro A hA hkeep
    rw [mq A hA hkeep.2.2, Compact2.Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by rcases hkeep.1 with h|h <;> omega),
      Compact2.bufferMem_keep _ A hkeep.1]
    exact beforeKeep A hA hkeep
#print axioms compact_main_steps
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer height chainCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem readWords_getD (t : MachineState) : ∀ (n a i : Nat), i<n →
    (t.readWords (BitVec.ofNat 64 a) n).getD i 0=t.getMem (BitVec.ofNat 64 (a+8*i))
  | 0,_,_,h => by omega
  | n+1,a,i,h => by
    have e : BitVec.ofNat 64 a+8=BitVec.ofNat 64 (a+8) := by
      apply BitVec.eq_of_toNat_eq;simp
    rw [MachineState.readWords_succ,e]
    cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ,readWords_getD t n (a+8) i (by omega)]
      congr 2;omega

theorem main_words_of_regions (t : MachineState) (N : HashOutput) (w : WCT9.Witness)
    (hh : t.readWords (BitVec.ofNat 64 2048) 8=wordsOf (headerBytesV5 w))
    (hlay : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N w lay)) :
    ∀i,i<2873 → (i ≤ 4 ∨ 1161 ≤ i) →
      t.getMem (BitVec.ofNat 64 (2048+8*i))=(wordsOf (witListV5 N w)).getD i 0 := by
  have hf : (List.finRange 4).flatMap (layerRegionV6 N w)=
      layerRegionV6 N w 0++layerRegionV6 N w 1++layerRegionV6 N w 2++layerRegionV6 N w 3 := by
    simp only [List.finRange_succ,List.finRange_zero,List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,List.append_nil,List.append_assoc]
    rfl
  have hlenh : (wordsOf (headerBytesV5 w)).length=8 := length_wordsOf 8 _ (headerBytesV5_length w)
  have hlenf : (wordsOf (wctBytesV5 N w.signature)).length=1152 := length_wordsOf 1152 _ (wctBytesV5_length N w.signature)
  have htail : t.readWords (BitVec.ofNat 64 11336) 1712=
      wordsOf ((List.finRange 4).flatMap (layerRegionV6 N w)) := by
    rw [hf]
    simp only [List.append_assoc]
    rw [wordsOf_append _ _ (by rw[layerRegionV6_length];decide),
      wordsOf_append _ _ (by rw[layerRegionV6_length];decide),
      wordsOf_append _ _ (by rw[layerRegionV6_length];decide),←hlay 0,←hlay 1,←hlay 2,←hlay 3]
    simp only [lBase,height,chainCount]
    rw [show (1712:Nat)=528+(400+(392+392)) by rfl,readWords_add,readWords_add,readWords_add]
    rfl
  have hwords : wordsOf (witListV5 N w)=wordsOf (headerBytesV5 w)++wordsOf (wctBytesV5 N w.signature)++
      [0]++wordsOf ((List.finRange 4).flatMap (layerRegionV6 N w)) := by
    unfold witListV5
    rw [wordsOf_append _ _ (by simp only[List.length_append,headerBytesV5_length,wctBytesV5_length,zeros,List.length_replicate]),
      wordsOf_append _ _ (by simp only[List.length_append,headerBytesV5_length,wctBytesV5_length]),
      wordsOf_append _ _ (by rw[headerBytesV5_length])]
    have hz : wordsOf (zeros 8)=[0] := by
      rw [show zeros 8=List.replicate (8*1) 0 by rfl,wordsOf_replicate_zero];rfl
    rw [hz]
  intro i hi hz
  rw [hwords]
  rcases hz with hz|hz
  · have hm:=congrArg (fun l:List Word=>l.getD i 0) hh
    rw [readWords_getD _ _ _ _ (by omega)] at hm
    rw [hm]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_append,hlenh,hlenf,List.length_cons,List.length_nil,
      if_pos (show i<8 by omega),if_pos (show i<8+1152 by omega),if_pos (show i<8+1152+1 by omega)]
  · have hm:=congrArg (fun l:List Word=>l.getD (i-1161) 0) htail
    rw [readWords_getD _ _ _ _ (by omega),show 11336+8*(i-1161)=2048+8*i by omega] at hm
    rw [hm]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_append,hlenh,hlenf,List.length_cons,List.length_nil,
      if_neg (show ¬i<8+1152+1 by omega)]
#print axioms main_words_of_regions
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem finish_steps {im : Image} (hcompact : CompactCodeAt im)
    (hz : SharedZero.ClearCode im) (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (he : CodeAt im (pcOf 43071) SharedScatter.endCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec48.CBytes)
    (s : MachineState) (hpc : s.pc=pcOf 41108)
    (hout : OutAt s 96 output) (hp : PlanAt s) (hlp : Compact2.LPlanAt s) (htp : Compact2.TopTabAt s)
    (hmain : ∀i,i<2873 → (i ≤ 4 ∨ 1161 ≤ i) → s.getMem (BitVec.ofNat 64 (2048+8*i))=
      (wordsOf (witListV5 output (Paired.mainWitness witness))).getD i 0)
    (hc3 : s.getMem 2080=(witness.counters 3).setWidth 64)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec48.sigDecC b).forest)
    (hplan : SharedScatter.PlanAt s)
    (hflag : s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0)) :
    ∃v,Steps im s 70972 71149 v ∧ v.pc=pcOf 49400 ∧ v.getReg .x5=1 ∧
      ClaudeWCT.W9.Machine.Expand.SharedCompactMain.Phase1 output witness v ∧
      (∀ A, 0x66700 ≤ A → A < 0x66760 → v.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨t,st,pt,main,ctr,keep⟩:=compact_main_steps hcompact output (Paired.mainWitness witness) s hpc hout hp hlp htp hmain
  have tin : SharedCompact.ForestAt t b := by
    intro k hk
    have old:=hin k hk
    exact ⟨(keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans old.1,
      (keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans old.2⟩
  have tout : OutAt t 96 output := by
    intro k hk
    exact (keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans (hout k hk)
  have tplan : SharedScatter.PlanAt t := by
    intro child j hj
    have hm:=Nat.mod_lt child.val (by decide : 0<32)
    have hh:=hplan child j hj
    rw [getByte_eq_word _ _ (by omega)] at hh ⊢
    rw [keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)]
    exact hh
  have ttail : ∀j,1012 ≤ j → j<2905 → j≠2789 → t.getMem (BitVec.ofNat 64 (2904+8*j))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*j) := by
    intro j hj hj' hne
    rw [main j hj hj',Compact2.wordsOf_getD' _ 2905 (ClaudeWCT.W9.Machine.Expand.OldW.witList_length_eq _ _) j hj']
    rfl
  have tchoice : t.getMem (BitVec.ofNat 64 (2904+8*2789))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*2789) := by
    rw [main 2789 (by norm_num) (by norm_num),
      Compact2.wordsOf_getD' _ 2905 (ClaudeWCT.W9.Machine.Expand.OldW.witList_length_eq _ _) 2789 (by norm_num)]
    rfl
  have tflag : t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0) :=
    (keep _ (by decide) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR Search.FLAG;omega)).trans hflag
  obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0x24c0306f#32) 43761=some 46980 by decide)
  have jump:=jal_x0_step hj hd ho t pt
  obtain ⟨v,tv,pv,v5,vph,vn⟩:=SharedScatter.clear_scatter_finish hz hc ha hf he output witness b
    (t.setPC (pcOf 46980)) rfl tin hforest tplan tout (ctr.trans hc3) ttail tchoice tflag
  refine ⟨v,((st.trans jump).trans tv).of_eq (by norm_num) (by norm_num),pv,v5,vph,fun A h1 h2 => ?_⟩
  rw [vn A h1 h2]
  exact keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)
#print axioms finish_steps
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit lval lpath CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame HalfAt ltable rlWit_range)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem region_not_written (index : Nat) (lay : Layer) (A : Nat)
    (hlo : lBase lay ≤ A) (hhi : A<lBase lay+64*(height lay+chainCount lay))
    (hW : ¬RlWit lay (route index lay).1 (lWC lay) (lWM lay) A)
    (hctr : A≠lBase lay+32) : ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  intro h
  rcases h with h|h|⟨lay',_,h|h|h⟩
  · unfold Search.CsW Search.DigW at h
    have hb:=region_bounds lay
    simp only [ENC,EOUT,DIGITS] at h;omega
  · have hb:=region_bounds lay
    simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,Search.NODE,Search.NOUT,LEAFPK,ENC] at h;omega
  · exact hctr (lD_in_region lay lay' A hlo hhi h)
  · by_cases he:lay'=lay
    · subst he;exact hW h
    · exact rlWit_region lay lay' _ A hlo hhi he h
  · have hb:=region_bounds lay
    rcases h with h|h
    · have hc:=h.2.1
      omega
    · simp only [Search.FLAG] at h; omega

theorem layer_regions (N : HashOutput) (w : WCT9.Witness) (s t : MachineState)
    (hout : ∀lay:Layer,LayerOut t w.signature (WCT9.digestIndex N) lay (w.counters lay))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex N) 4))
    (hz : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0) :
    ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N w lay) := by
  intro lay
  have hrb:=region_bounds lay
  have hv : ∀i (h:i<chainCount lay),DigAt t (lWC lay-64*i+48) ((w.signature.layers lay).values ⟨i,h⟩) := by
    intro i hi
    simpa only [lval,dif_pos hi,WCT9.toT3Signature] using (hout lay).2.1 i hi
  have hp : ∀j (h:j<height lay),DigAt t (lWM lay-64*j+SigGolfCandidate.T3M.Expand.sideOff (route (WCT9.digestIndex N) lay).1 j)
      ((w.signature.layers lay).path ⟨j,h⟩) := by
    intro j hj
    simpa only [lpath,dif_pos hj,WCT9.toT3Signature] using (hout lay).2.2 j hj
  have zero (A : Nat) (hlo : lBase lay ≤ A) (hhi : A<lBase lay+64*(height lay+chainCount lay))
      (hn : ¬RlWit lay (route (WCT9.digestIndex N) lay).1 (lWC lay) (lWM lay) A)
      (hc : A≠lBase lay+32) : t.getMem (BitVec.ofNat 64 A)=0 := by
    rw [hframe.get (by omega) (region_not_written _ lay A hlo hhi hn hc)]
    exact hz A (by omega) (by omega)
  unfold layerRegionV6
  split
  · rename_i h0
    refine layer_words t lay _ _ hv hp (fun A h1 h2 hn=>?_)
    by_cases he:A=lBase lay+32
    · have e:lay=0:=Fin.ext h0
      subst e
      rw [hframe.get (by omega) ?_]
      · exact hz A (by omega) (by omega)
      · rintro (h|h|⟨l,_,h|h|h⟩)
        · simp only [Search.CsW,Search.DigW,ENC,EOUT,DIGITS] at h;norm_num [lBase] at he;omega
        · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,Search.NODE,Search.NOUT,LEAFPK,ENC] at h;norm_num [lBase] at he;omega
        · have hd:=lD_cases l;norm_num [lBase] at he;omega
        · by_cases hl:l=0
          · subst hl;exact hn h
          · exact rlWit_region 0 l _ A h1 h2 hl h
        · rcases h with h|h
          · have hc:=h.2.1;norm_num [lBase] at he;omega
          · simp only [Search.FLAG] at h;norm_num [lBase] at he;omega
    · exact zero A h1 h2 hn he
  · rename_i h0
    refine layerBC_words t lay _ _ _ hv hp ?_ zero
    let prev : Layer := Fin.ofNat 4 (lay.val-1)
    have hd : lD prev=lBase lay+32:=lD_above lay h0
    have hlo:=(hout prev).1
    simp only [HalfAt,lk_zero,Nat.mul_zero,hd] at hlo
    have hhi:=hhalf (lBase lay+32) 1 (by rw [←hd];rcases lD_cases prev with h|h|h|h <;> simp[h]) (by decide)
      (by intro l hl he;rw[lk_zero] at he;exact absurd he.2 (by decide))
    simp only [Nat.mul_one] at hhi
    rw [hz _ (by omega) (by fin_cases lay <;> simp_all [lBase,height,chainCount]) ] at hhi
    rw [dword_of_halves (t.getMem (BitVec.ofNat 64 (lBase lay+32))),hlo,hhi]
    simp [prev]
#print axioms layer_regions
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit lval lpath sideOff)
open SigGolfCandidate.T3M.Expand.BC (LayerOut)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem regions_fillTop (N : HashOutput) (w : WCT9.Witness) (s t : MachineState) (c : Nat)
    (hproj : WCT9.fillTop w.signature 0=w.signature)
    (hregions : ∀lay:Layer,s.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N w lay))
    (hout : LayerOut s w.signature (WCT9.digestIndex N) 0 (w.counters 0))
    (hz : ∀A,0x2c48 ≤ A → A<0x2c48+64*66 →
      ¬RlWit 0 (route (WCT9.digestIndex N) 0).1 (lWC 0) (lWM 0) A → s.getMem (BitVec.ofNat 64 A)=0)
    (hzero : c=0 → Frame s t (fun _=>False))
    (hwritten : c≠0 → t.getMem (BitVec.ofNat 64 (0x2c48+sOff (WCT9.digestIndex N)))=
      hi64 (WCT9.setTop (WCT9.topSib w.signature) c))
    (hf : Frame s t (fun A=>(NODE ≤ A ∧ A<NODE+64) ∨ (NOUT ≤ A ∧ A<NOUT+32) ∨ A=0x2c48+sOff (WCT9.digestIndex N))) :
    ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N {w with signature:=WCT9.fillTop w.signature c} lay) := by
  intro lay
  by_cases hc:c=0
  · subst hc
    rw [frame_readWords (hzero rfl) _ _ (by have:=region_bounds lay;omega) (by simp),hregions lay,hproj]
  have hso:=sOff_cases (WCT9.digestIndex N)
  have hrb:=region_bounds lay
  by_cases hl0:lay.val=0
  swap
  · have hge : 0x3cc8 ≤ lBase lay := by fin_cases lay <;> first | exact absurd rfl hl0 | decide
    rw [frame_readWords hf _ _ (by omega) (by intro i hi h;simp only [NODE,NOUT] at h;omega),hregions lay]
    unfold layerRegionV6
    rw [if_neg hl0,if_neg hl0]
    change _=wordsOf (layerBytesBCV6 lay _ (WCT9.fillLayer lay (w.signature.layers lay) c) _)
    rw [WCT9.fillLayer_ne _ _ _ hl0]
  have h0:lay=0:=Fin.ext hl0
  subst h0
  have hsoe:=sOff_eq (WCT9.digestIndex N)
  unfold layerRegionV6
  rw [if_pos (show (0:Layer).val=0 by rfl)]
  refine layer_words t 0 _ _ (fun i hi=>?_) (fun j hj=>?_) (fun A h1 h2 hn=>?_)
  · have d:=hout.2.1 i hi
    simp only [lval,dif_pos hi,WCT9.toT3Signature] at d
    have hi54:i<54:=hi
    change DigAt t (0x3c88-64*i+48) ((w.signature.layers 0).values ⟨i,hi⟩)
    exact ⟨(hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.1,
      (hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.2⟩
  · have d:=hout.2.2 j hj
    simp only [lpath,dif_pos hj,WCT9.toT3Signature] at d
    have h12:j<12:=hj
    have hs : sideOff (route (WCT9.digestIndex N) 0).1 j ≤ 48 := by unfold sideOff;split <;> omega
    rw [show lWM (0:Layer)=0x2f08 by rfl] at d ⊢
    change DigAt t _ ((WCT9.fillLayer 0 (w.signature.layers 0) c).path ⟨j,hj⟩)
    unfold WCT9.fillLayer
    dsimp only
    by_cases hj11:j=11
    · subst hj11
      rw [if_pos ⟨rfl,rfl⟩]
      constructor
      · rw [hf.get (by omega) (by simp only [NODE,NOUT];omega),d.1]
        exact (lo64_setTop _ c).symm
      · rw [show 0x2f08-64*11+sideOff (route (WCT9.digestIndex N) 0).1 11+8=0x2c48+sOff (WCT9.digestIndex N) by omega,
          hwritten hc]
        rfl
    · rw [if_neg (fun h=>hj11 h.2)]
      exact ⟨(hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.1,
        (hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.2⟩
  · have h1':0x2c48 ≤ A:=h1
    have h2':A<0x2c48+64*66:=h2
    have hne:A≠0x2c48+sOff (WCT9.digestIndex N) := by
      intro he
      apply hn
      refine Or.inr ⟨11,by decide,Or.inr ?_⟩
      rw [show lWM (0:Layer)=0x2f08 by rfl]
      omega
    rw [hf.get (by omega) (by simp only [NODE,NOUT];omega)]
    exact hz A h1' h2' hn
#print axioms regions_fillTop
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain
