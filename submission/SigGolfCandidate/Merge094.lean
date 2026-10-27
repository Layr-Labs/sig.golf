import SigGolfCandidate.Merge007
import SigGolfCandidate.Merge008
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge047
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge071
import SigGolfCandidate.Merge072
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge078
import SigGolfCandidate.Merge080
import SigGolfCandidate.Merge084
import SigGolfCandidate.Merge093

-- ==== merged from ClaudeWCT_W9_New_Machine_ExpandLink_Link ====
section

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
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
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
theorem region_bounds (lay : Layer) : 0x2c48 ≤ lBase lay ∧ lBase lay + 64 * (height lay + chainSlotsV6 lay) ≤ 0x61C8 := by
  fin_cases lay <;> decide
theorem lD_in_region (lay lay' : Layer) (A : Nat) (h1 : lBase lay ≤ A) (h2 : A < lBase lay + 64 * (height lay + chainSlotsV6 lay))
    (he : A = lD lay') : A = lBase lay + 32 := by
  subst he
  fin_cases lay <;> fin_cases lay' <;> simp_all [lD, lBase, height, chainCount, chainSlotsV6] <;> omega
theorem rlWit_region (lay lay' : Layer) (leaf A : Nat) (h1 : lBase lay ≤ A)
    (h2 : A < lBase lay + 64 * (height lay + chainSlotsV6 lay)) (hne : lay' ≠ lay)
    (h : RlWit lay' leaf (lWC lay') (lWM lay') A) : False := by
  have hr := rlWit_range h
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  obtain ⟨hWM', hWC'⟩ := lBase_eq lay'
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hS := chainSlotsV6_ge lay
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
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (s : MachineState) (hp : s.pc=pcOf 45257)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
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
    (output:HashOutput) (witness:SharedForest.Witness) (b:SharedCodec.CBytes)
    (s:MachineState) (hp:s.pc=pcOf 46980) (hin:SharedCompact.ForestAt s b)
    (hforest:witness.signature.forest=(SharedCodec.sigDecC b).forest)
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
    (hlay : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
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
    rw [show 8*(height (0:Layer)+chainSlotsV6 0)=528 by decide,show 8*(height (1:Layer)+chainSlotsV6 1)=400 by decide,
      show 8*(height (2:Layer)+chainSlotsV6 2)=392 by decide,show 8*(height (3:Layer)+chainSlotsV6 3)=392 by decide,
      show lBase 0=11336 by rfl,show lBase 1=15560 by rfl,show lBase 2=18760 by rfl,show lBase 3=21896 by rfl]
    rw [show (1712:Nat)=528+(400+(392+392)) by rfl,readWords_add,readWords_add,readWords_add]
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
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (s : MachineState) (hpc : s.pc=pcOf 41108)
    (hout : OutAt s 96 output) (hp : PlanAt s) (hlp : Compact2.LPlanAt s) (htp : Compact2.TopTabAt s)
    (hmain : ∀i,i<2873 → (i ≤ 4 ∨ 1161 ≤ i) → s.getMem (BitVec.ofNat 64 (2048+8*i))=
      (wordsOf (witListV5 output (Paired.mainWitness witness))).getD i 0)
    (hc3 : s.getMem 2080=(witness.counters 3).setWidth 64)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
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
    (hlo : lBase lay ≤ A) (hhi : A<lBase lay+64*(height lay+chainSlotsV6 lay))
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
    ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
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
  have zero (A : Nat) (hlo : lBase lay ≤ A) (hhi : A<lBase lay+64*(height lay+chainSlotsV6 lay))
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
    have hS := chainSlotsV6_lower lay h0
    rw [hS]
    refine layerBC_words t lay h0 _ _ _ hv hp ?_ (fun A h1 h2 hn hc => zero A h1 (by rw [hS]; exact h2) hn hc)
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
    (hregions : ∀lay:Layer,s.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
      wordsOf (layerRegionV6 N w lay))
    (hout : LayerOut s w.signature (WCT9.digestIndex N) 0 (w.counters 0))
    (hz : ∀A,0x2c48 ≤ A → A<0x2c48+64*66 →
      ¬RlWit 0 (route (WCT9.digestIndex N) 0).1 (lWC 0) (lWM 0) A → s.getMem (BitVec.ofNat 64 A)=0)
    (hzero : c=0 → Frame s t (fun _=>False))
    (hwritten : c≠0 → t.getMem (BitVec.ofNat 64 (0x2c48+sOff (WCT9.digestIndex N)))=
      hi64 (WCT9.setTop (WCT9.topSib w.signature) c))
    (hf : Frame s t (fun A=>(NODE ≤ A ∧ A<NODE+64) ∨ (NOUT ≤ A ∧ A<NOUT+32) ∨ A=0x2c48+sOff (WCT9.digestIndex N))) :
    ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
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
    have hi51:i<51:=hi
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
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit lval lpath CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame HalfAt ltable rlWit_range)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layer_not_low (index A : Nat) (ha : A<0x2c48) (hc : A≠0x820) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=SigGolfCandidate.T3M.Expand.BC.ltable_lo lay;omega
  · rcases h with h|h
    · have:=h.2.1;omega
    · simp only [Search.FLAG] at h;omega

theorem layer_not_high (index A : Nat) (ha : 0xff0000 ≤ A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=ltable lay;omega
  · rcases h with h|h
    · have:=h.2.2;omega
    · simp only [Search.FLAG] at h;omega

theorem layer_header (N : HashOutput) (w : WCT9.Witness) (s t : MachineState)
    (hout : LayerOut t w.signature (WCT9.digestIndex N) 3 (w.counters 3))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex N) 4))
    (hr : DigAt s 2048 w.signature.rho)
    (hc : s.getMem 2064=BitVec.ofNat 64 w.digestCounter.toNat)
    (hz : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0) :
    t.readWords (BitVec.ofNat 64 2048) 8=wordsOf (headerBytesV5 w) ∧
      t.getMem 2080=BitVec.ofNat 64 (w.counters 3).toNat := by
  have ctr : t.getMem 2080=BitVec.ofNat 64 (w.counters 3).toNat := by
    have hlo:=hout.1
    change (t.getMem 2080).extractLsb' 0 32=w.counters 3 at hlo
    have hhi:=hhalf 2080 1 (by simp) (by decide) (by intro lay hl h;rw [lk_zero] at h;omega)
    rw [hz 4 (by decide) (by decide)] at hhi
    have hh : (t.getMem 2080).extractLsb' 32 32=0:=hhi
    rw [dword_of_halves (t.getMem 2080),hlo,hh]
    simp
  have r0:= (hframe.get (by decide) (layer_not_low _ 2048 (by decide) (by decide))).trans hr.1
  have r1:= (hframe.get (by decide) (layer_not_low _ 2056 (by decide) (by decide))).trans hr.2
  have dc:= (hframe.get (by decide) (layer_not_low _ 2064 (by decide) (by decide))).trans hc
  have zero (i:Nat) (hi:3 ≤ i) (hi':i<8) (hne:i≠4) : t.getMem (BitVec.ofNat 64 (2048+8*i))=0 := by
    rw [hframe.get (by omega) (layer_not_low _ _ (by omega) (by omega))]
    exact hz i hi hi'
  have ctr' : t.getMem (BitVec.ofNat 64 (2048+32))=BitVec.ofNat 64 (w.counters 3).toNat:=ctr
  refine ⟨?_,ctr⟩
  rw [headerW_words,readWords_eight,r0,r1,dc,zero 3 (by decide) (by decide) (by decide),
    ctr',
    zero 5 (by decide) (by decide) (by decide),zero 6 (by decide) (by decide) (by decide),
    zero 7 (by decide) (by decide) (by decide)]

end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT OutAt)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (ltable rlWit_range)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def Keep (A : Nat) : Prop := A<256 ∨ A=0x20550 ∨ (0x7000 ≤ A ∧ A<0x7760) ∨ 0xff0000 ≤ A

structure Stable (output : HashOutput) (b : SharedCodec.CBytes) (pk : Digest) (s : MachineState) : Prop where
  digest : OutAt s 96 output
  forest : SharedCompact.ForestAt s b
  plan : PlanAt s
  lplan : Compact2.LPlanAt s
  toptab : Compact2.TopTabAt s
  scatterPlan : SharedScatter.PlanAt s
  pk : DigAt s 0xA0 pk
  index : s.getMem (0x20550#64)=BitVec.ofNat 64 (WCT9.digestIndex output)
  threshold1 : ∀r,r<56 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (WCT9.CanonicalPolicy.threshold 1 r)
  threshold2 : ∀r,r<41 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (WCT9.CanonicalPolicy.threshold 2 r)
  zt : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 s
  t51src : SigGolfCandidate.T3M.Search.T51.T51TableW 0xFF9E00 s

theorem Stable.frame {output : HashOutput} {b : SharedCodec.CBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (h : Stable output b pk s) (hf : Frame s t W)
    (hn : ∀A,Keep A → ¬W A) : Stable output b pk t := by
  have word (A:Nat) (ha:A<2^64) (hk:Keep A) : t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := hf.get ha (hn A hk)
  have byte (A:Nat) (ha:A<2^64) (hk:0xff0000 ≤ A) : t.getByte (BitVec.ofNat 64 A)=s.getByte (BitVec.ofNat 64 A) :=
    hf.getByte ha (hn _ (Or.inr (Or.inr (Or.inr (by omega)))))
  constructor
  · intro k hk;rw [word _ (by omega) (Or.inl (by omega))];exact h.digest k hk
  · intro k hk
    have d:=h.forest k hk
    exact ⟨(word _ (by omega) (Or.inr (Or.inr (Or.inl (by omega))))).trans d.1,
      (word _ (by omega) (Or.inr (Or.inr (Or.inl (by omega))))).trans d.2⟩
  · intro k hk;rw [word _ (by unfold PLAN;omega) (Or.inr (Or.inr (Or.inr (by unfold PLAN;omega))))];exact h.plan k hk
  · intro k hk;rw [word _ (by unfold Compact2.LPLAN;omega) (Or.inr (Or.inr (Or.inr (by unfold Compact2.LPLAN;omega))))];exact h.lplan k hk
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [word _ (by unfold Compact2.TOPA;omega) (by unfold Keep Compact2.TOPA;omega)];exact h.toptab.1 k hk
    · rw [word _ (by unfold Compact2.TOPB;omega) (by unfold Keep Compact2.TOPB;omega)];exact h.toptab.2 k hk
  · intro child j hj;rw [byte _ (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by omega)];exact h.scatterPlan child j hj
  · exact ⟨(word _ (by decide) (Or.inl (by decide))).trans h.pk.1,(word _ (by decide) (Or.inl (by decide))).trans h.pk.2⟩
  · exact (word _ (by decide) (Or.inr (Or.inl rfl))).trans h.index
  · intro r hr;rw [byte _ (by omega) (by omega)];exact h.threshold1 r hr
  · intro r hr;rw [byte _ (by omega) (by omega)];exact h.threshold2 r hr
  · exact h.zt.frame hf (fun r hr => hn _ (Or.inr (Or.inr (Or.inr (by
      rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl]; omega)))))
  · exact h.t51src.frame hf (by decide) (by decide) (fun k hk => hn _ (Or.inr (Or.inr (Or.inr (by omega)))))

theorem layer_keep (index A : Nat) (hk : Keep A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rcases hk with hk|rfl|hk|hk
  · exact layer_not_low index A (by omega) (by omega)
  · rintro (h|h|⟨lay,_,h|h|h⟩)
    · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
    · rcases lD_cases lay with hD|hD|hD|hD <;> omega
    · have:=rlWit_range h;have:=ltable lay;omega
    · rcases h with h|h
      · have:=h.2.1;omega
      · simp only [Search.FLAG] at h;omega
  · rintro (h|h|⟨lay,_,h|h|h⟩)
    · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
    · rcases lD_cases lay with hD|hD|hD|hD <;> omega
    · have:=rlWit_range h;have:=ltable lay;omega
    · rcases h with h|h
      · have:=h.2.1;omega
      · simp only [Search.FLAG] at h;omega
  · exact layer_not_high index A hk

def H2Writes (index A : Nat) : Prop := (NODE ≤ A ∧ A<NODE+64) ∨ (NOUT ≤ A ∧ A<NOUT+32) ∨ A=0x2c48+sOff index

theorem h2_keep (index A : Nat) (hk : Keep A) : ¬H2Writes index A := by
  have:=sOff_cases index
  unfold Keep at hk
  unfold H2Writes
  simp only [NODE,NOUT]
  omega
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open SigGolfCandidate.T3M.Expand.BC (LayerOut)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def topProgram (output : HashOutput) (w : SharedForest.Witness) (folded root pk : Digest) :
    M (Option (HashOutput × SharedForest.Witness)) :=
  (if root=pk then pure (some 0) else WCT9.searchTop (WCT9.digestIndex output) folded (WCT9.topSib (SharedForest.mainSignature w.signature)) pk WCT9.searchFuel 1) >>= fun c=>
  pure (c.map fun c=>(output,{w with signature:=SharedForest.fillTopSignature w.signature c}))

/-- `some`: the expander reached the post-pass entry (pc 49400) with the phase-1 witness image and the top-node
nonces (`NoncesAt`, written by the img-v6 nonce routine) in place. -/
def Done (r : Option (HashOutput × SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none => s.pc=pcOf 354
  | some (output,w) => s.pc=pcOf 49400 ∧ s.getReg .x5=1 ∧ Phase1 output w s ∧
      SigGolfCandidate.T3M.Expand.NoncesAt s w.topNonces (route (WCT9.digestIndex output) 0).1

structure TopReady (output : HashOutput) (w : SharedForest.Witness) (b : SharedCodec.CBytes)
    (folded root pk : Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf 42795
  x5 : s.getReg .x5=0
  root : DigAt s ENC root
  stable : Stable output b pk s
  indexLt : WCT9.digestIndex output<2^31
  top : ∀i,i<8 → s.getMem (BitVec.ofNat 64 (NODE+8*i))=
    (blkW (WCT9.digestIndex output) folded (WCT9.topSib (SharedForest.mainSignature w.signature))).getD i 0
  proj : WCT9.fillTop (SharedForest.mainSignature w.signature) 0=SharedForest.mainSignature w.signature
  header : s.readWords 2048 8=wordsOf (headerBytesV5 (Paired.mainWitness w))
  regions : ∀lay:Layer,s.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
    wordsOf (layerRegionV6 output (Paired.mainWitness w) lay)
  layer : LayerOut s (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) 0 (w.counters 0)
  zero : ∀A,0x2c48 ≤ A → A<0x2c48+64*66 →
    ¬RlWit 0 (route (WCT9.digestIndex output) 0).1 (lWC 0) (lWM 0) A → s.getMem (BitVec.ofNat 64 A)=0
  ctr3 : s.getMem 2080=(w.counters 3).setWidth 64
  forest : w.signature.forest=(SharedCodec.sigDecC b).forest
  flag : s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if w.topHigh then 128 else 0)
  nonces : SigGolfCandidate.T3M.Expand.NoncesAt s w.topNonces (route (WCT9.digestIndex output) 0).1

theorem top_good {im : Image} {sk : BitVec 256} (hsearch : SrchCoreAt im)
    (hcompact : CompactCodeAt im) (hz : SharedZero.ClearCode im)
    (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (he : CodeAt im (pcOf 43071) SharedScatter.endCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (hentry : CodeAt im (pcOf 351) [0x4d52706f])
    {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec.CBytes} {folded root pk : Digest} {s : MachineState}
    (h : TopReady output w b folded root pk s) :
    TBSim im sk s 15800000 (topProgram output w folded root pk) Done := by
  have hsib : WCT9.setTop (WCT9.topSib (SharedForest.mainSignature w.signature)) 0=
      WCT9.topSib (SharedForest.mainSignature w.signature) := by
    rw [←WCT9.topSib_fillTop,h.proj]
  have call:=search_entry_core (sk:=sk) hsearch (WCT9.digestIndex output) h.indexLt folded
    (WCT9.topSib (SharedForest.mainSignature w.signature)) root pk hsib s h.pc h.x5 h.root
    h.stable.pk.1 h.stable.pk.2 h.stable.index h.top
  unfold topProgram
  refine (TBSim.bind (W₂:=71150) call (fun result t ht=>?_)).mono (W':=15800000) (by norm_num) (fun _ _ h=>h)
  cases result with
  | none => exact (TBSim.pure (Q:=Done) (a:=none) ht).mono (by omega) (fun _ _ h=>h)
  | some c =>
    obtain ⟨tp,tzero,tnonzero⟩:=ht
    have frame : Frame s t (H2Writes (WCT9.digestIndex output)) := by
      by_cases hz:c=0
      · exact (tzero hz).mono (by simp)
      · exact (tnonzero hz).2.2
    have stable:=h.stable.frame frame (h2_keep (WCT9.digestIndex output))
    let w' : SharedForest.Witness:={w with signature:=SharedForest.fillTopSignature w.signature c}
    have regs : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
        wordsOf (layerRegionV6 output (Paired.mainWitness w') lay) := by
      exact regions_fillTop output (Paired.mainWitness w) s t c h.proj h.regions h.layer h.zero
        tzero (fun hc=>(tnonzero hc).2.1) frame
    have head : t.readWords 2048 8=wordsOf (headerBytesV5 (Paired.mainWitness w')) := by
      change t.readWords (BitVec.ofNat 64 2048) 8=_
      rw [frame_readWords frame 2048 8 (by decide) (by
        intro i hi hw;unfold H2Writes at hw;simp only [NODE,NOUT] at hw
        have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.header
    have ctr : t.getMem 2080=(w'.counters 3).setWidth 64 := by
      change t.getMem (BitVec.ofNat 64 2080)=_
      rw [frame.get (A:=2080) (by decide) (by unfold H2Writes;simp only [NODE,NOUT];have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.ctr3
    have fields:=main_words_of_regions t output (Paired.mainWitness w') head regs
    obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0x4d52706f#32) 351=some 41108 by decide)
    have jump:=jal_x0_step hentry hd ho t tp
    have flag : t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if w'.topHigh then 128 else 0) := by
      rw [frame.get (by decide) (by unfold H2Writes;simp only [NODE,NOUT,Search.FLAG];have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.flag
    obtain ⟨v,tv,vp,v5,vph,vn⟩:=finish_steps hcompact hz hc ha hf he hj output w' b
      (t.setPC (pcOf 41108)) rfl stable.digest stable.plan stable.lplan stable.toptab fields ctr stable.forest
      h.forest stable.scatterPlan flag
    have tn := NoncesAt.frame h.nonces frame (by
      intro A h1 h2 hw; unfold H2Writes at hw; simp only [NODE,NOUT] at hw
      have:=sOff_cases (WCT9.digestIndex output);omega)
    have vnon : SigGolfCandidate.T3M.Expand.NoncesAt v w'.topNonces (route (WCT9.digestIndex output) 0).1 :=
      ⟨tn.1, fun k hk => (vn _ (by omega) (by omega)).trans (tn.2.1 k hk), (vn _ (by norm_num) (by norm_num)).trans tn.2.2⟩
    exact TBSim.steps (jump.trans tv) (TBSim.pure ⟨vp,v5,vph,vnon⟩)
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (HashOutput)

def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage,Images.expandImage,Images.verifyImage⟩

def pairedExpandCost : Nat := 4210000000 + ClaudeWCT.W9.Machine.Expand.SharedCompactMain.suffixW

def PairedExpPost : Option (HashOutput × SigGolfCandidate.Research.SharedForest.Witness) → MachineState → Prop
  | none,t => (t.pc=pcOf 356 ∨ t.pc=pcOf 45231) ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      fetch Images.expandImage t=some (.base .ECALL)
  | some (output,w),t => t.pc=pcOf 45016 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t 4128 22012=ClaudeWCT.W9.T3M.Paired.witEncN output w ∧
      fetch Images.expandImage t=some (.base .ECALL)
end ClaudeWCT.W9.Machine.ExpandLink

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK TopBlkG)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame ltable rlWit_range)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem top_not_written (index A : Nat) (ha : 0x2c48 ≤ A) (hb : A<0x2c48+64*66)
    (hn : ¬RlWit 0 (route index 0).1 (lWC 0) (lWM 0) A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hd|hd|hd|hd <;> omega
  · by_cases he:lay=0
    · subst he;exact hn h
    · exact rlWit_region 0 lay _ A ha hb he h
  · rcases h with h|h
    · have:=h.2.1;omega
    · simp only [Search.FLAG] at h;omega

theorem ready_of_layers {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec.CBytes}
    {pk folded root : Digest} {s t u : MachineState}
    (hi : WCT9.digestIndex output<2^31)
    (stable : Stable output b pk s)
    (hr : DigAt s 2048 w.signature.rho)
    (hdc : s.getMem 2064=BitVec.ofNat 64 w.digestCounter.toNat)
    (hzhead : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0)
    (hzregions : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hproj : WCT9.fillTop (SharedForest.mainSignature w.signature) 0=SharedForest.mainSignature w.signature)
    (hforest : w.signature.forest=(SharedCodec.sigDecC b).forest)
    (hout : ∀lay:Layer,LayerOut t (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) lay (w.counters lay))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex output) 4))
    (hroot : DigAt t ENC root)
    (hblk : TopBlkG (WCT9.toT3Signature (SharedForest.mainSignature w.signature)) (WCT9.digestIndex output) 0 folded t)
    (hu : Frame t u (fun _=>False)) (up : u.pc=pcOf 42795) (u5 : u.getReg .x5=0)
    (hflag : t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if w.topHigh then 128 else 0))
    (hnon : SigGolfCandidate.T3M.Expand.NoncesAt t w.topNonces (route (WCT9.digestIndex output) 0).1) :
    TopReady output w b folded root pk u := by
  have mem (A:Nat) (ha:A<2^64) : u.getMem (BitVec.ofNat 64 A)=t.getMem (BitVec.ofNat 64 A):=hu.get ha (by simp)
  have rs:=layer_regions output (Paired.mainWitness w) s t hout hhalf hframe hzregions
  have hs:=layer_header output (Paired.mainWitness w) s t (hout 3) hhalf hframe hr hdc hzhead
  constructor
  · exact up
  · exact u5
  · exact ⟨(mem _ (by unfold ENC;omega)).trans hroot.1,(mem _ (by unfold ENC;omega)).trans hroot.2⟩
  · exact (stable.frame hframe (layer_keep _)).frame hu (by simp)
  · exact hi
  · intro i hi
    rw [mem _ (by unfold NODE;omega)]
    exact topBlk_get (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) folded t hblk i hi
  · exact hproj
  · change u.readWords (BitVec.ofNat 64 2048) 8=_
    rw [frame_readWords hu 2048 8 (by decide) (by simp)]
    exact hs.1
  · intro lay
    rw [frame_readWords hu _ _ (by have:=region_bounds lay;omega) (by simp)]
    exact rs lay
  · rcases hout 0 with ⟨ctr,values,paths⟩
    refine ⟨?_,?_,?_⟩
    · unfold SigGolfCandidate.T3M.Expand.BC.HalfAt at ctr ⊢
      rw [mem _ (by rw [show lD (0:Layer)=0x3ce8 by rfl];omega)]
      exact ctr
    · intro i hi
      exact ⟨(mem _ (by have:=ltable (0:Layer);omega)).trans (values i hi).1,
        (mem _ (by have:=ltable (0:Layer);omega)).trans (values i hi).2⟩
    · intro j hj
      have hh:SigGolfCandidate.T3M.Expand.sideOff (route (WCT9.digestIndex output) 0).1 j ≤ 48 := by
        unfold SigGolfCandidate.T3M.Expand.sideOff;split <;> omega
      exact ⟨(mem _ (by have:=ltable (0:Layer);omega)).trans (paths j hj).1,
        (mem _ (by have:=ltable (0:Layer);omega)).trans (paths j hj).2⟩
  · intro A ha hb hn
    rw [mem _ (by omega),hframe.get (by omega) (top_not_written _ A ha hb hn)]
    exact hzregions A ha (by omega)
  · change u.getMem (BitVec.ofNat 64 2080)=_
    rw [mem _ (by decide)]
    change t.getMem 2080=_
    exact hs.2.trans (BitVec.ofNat_toNat 64 (w.counters 3))
  · exact hforest
  · rw [mem _ (by decide)]; exact hflag
  · exact NoncesAt.frame hnon hu (by simp)
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Expand (w9init)
open ClaudeWCT.W9.T3M.Final.Paired (ExpandRefines ExpandTerminates)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- img-v6: the expander reads the 5,239-byte signature (`SharedCodec.sigDecC`, 19-bit top field). -/
abbrev PairedExpandSimulation : Prop := ∀(sk : SecretKey)(message : Message)(pk : PublicKey)(b : Bytes 5195),
  TBSim Images.expandImage sk (w9init Images.expandImage message pk b) pairedExpandCost
    (ClaudeWCT.W9.T3M.Paired.expandN message pk (ClaudeWCT.W9.T3M.SharedCodec.sigDecC b)) PairedExpPost

theorem ppCycles_le : ClaudeWCT.W9.Machine.Expand.PostPass.ppCycles ≤ 1000000 := by
  unfold ClaudeWCT.W9.Machine.Expand.PostPass.ppCycles
  first
  | decide
  | (simp only [ClaudeWCT.W9.Machine.Expand.PostPass.RDA.res, ClaudeWCT.W9.Machine.Expand.PostPass.RDB.res,
      ClaudeWCT.W9.Machine.Expand.PostPass.RJ.res]; omega)
  | (norm_num [ClaudeWCT.W9.Machine.Expand.PostPass.RDA.res, ClaudeWCT.W9.Machine.Expand.PostPass.RDB.res,
      ClaudeWCT.W9.Machine.Expand.PostPass.RJ.res])
theorem pairedExpandCost_lt : pairedExpandCost+1<CYCLE_LIMIT := by
  have := ppCycles_le
  unfold pairedExpandCost ClaudeWCT.W9.Machine.Expand.SharedCompactMain.suffixW CYCLE_LIMIT
  omega

theorem paired_expand_initial (message : Message) (pk : PublicKey) (b : Bytes 5195) :
    initialState SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)=
      some (w9init Images.expandImage message pk b) := by
  unfold initialState
  rw [if_pos SigGolfCandidate.T3M.Paired.submission_expand_valid]
  simp only [inputBuffers,List.foldl_cons,List.foldl_nil]
  rfl

theorem paired_expPost_halt {o : Option (SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness)}
    {t : MachineState} (h : PairedExpPost o t) :
    fetch Images.expandImage t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none=>exact ⟨h.2.2.2,h.2.1⟩
  | some x=>exact ⟨h.2.2.2.2,h.2.1⟩

theorem paired_expPost_readout {o : Option (SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness)}
    {t : MachineState} (h : PairedExpPost o t) :
    o.map (fun x=>ClaudeWCT.W9.T3M.Paired.witEncN x.1 x.2)=
      if t.getReg .x10=0 then some (readOutput SigGolfCandidate.T3M.Paired.submission.sizes
        SigGolfCandidate.T3M.Paired.submission.layout .expand t) else none := by
  cases o with
  | none=>rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some x=>
    rw [if_pos h.2.2.1]
    exact congrArg some h.2.2.2.1.symm

theorem paired_expand_refines_of (H : PairedExpandSimulation) : ExpandRefines I0 := by
  intro message pk b
  apply Sim.run_eq SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)
    (paired_expand_initial message pk b) (H 0 message pk b) (Nat.lt_of_succ_lt pairedExpandCost_lt)
    (fun o=>o.map (fun x=>ClaudeWCT.W9.T3M.Paired.witEncN x.1 x.2))
  intro o t ht
  exact ⟨(paired_expPost_halt ht).1,(paired_expPost_halt ht).2,paired_expPost_readout ht⟩

theorem paired_expand_terminates_of (H : PairedExpandSimulation) : ExpandTerminates I0 := by
  intro hash message pk b
  obtain ⟨hf,hc⟩:=Sim.runWith SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)
    (paired_expand_initial message pk b) (H 0 message pk b) pairedExpandCost_lt
    (fun _ _ h=>paired_expPost_halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc pairedExpandCost_lt⟩

theorem paired_expand_pending_of (H : PairedExpandSimulation) : ExpandRefines I0 ∧ ExpandTerminates I0 :=
  ⟨paired_expand_refines_of H,paired_expand_terminates_of H⟩
end ClaudeWCT.W9.Machine.ExpandLink

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

structure LayersReady (output : HashOutput) (sig : SharedForest.Signature) (b : SharedCodec.CBytes)
    (counter : BitVec 32) (forest : Digest × Digest) (pk : Digest) (s : MachineState) : Prop where
  inv : SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature sig) sig.policyHints
    (WCT9.digestIndex output) 4 (.pair forest.1 forest.2) s
  stable : Stable output b pk s
  rho : DigAt s 2048 sig.rho
  dc : s.getMem 2064=BitVec.ofNat 64 counter.toNat
  headerZero : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0
  regionZero : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : WCT9.fillTop (SharedForest.mainSignature sig) 0=SharedForest.mainSignature sig
  forestEq : sig.forest=(SharedCodec.sigDecC b).forest

def recoverProgram (output : HashOutput) (sig : SharedForest.Signature) (counter : BitVec 32)
    (forest : Digest × Digest) (pk : Digest) : M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverHintedLayers sig (WCT9.digestIndex output) (WCT9.topSib (SharedForest.mainSignature sig))
    4 (.pair forest.1 forest.2) >>= fun result=>
  match result with
  | none => pure none
  | some r => if SharedForest.policyHintsValid sig.policyHints r.digits r.lows then
      topProgram output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),r.nonces⟩ r.foldedTop r.root pk
    else pure none

def SuffixDone (im : Image) (r : Option (HashOutput × SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none => s.pc=pcOf 354 ∨ (s.pc=pcOf 356 ∧ s.getReg .x5=1 ∧ s.getReg .x10=1 ∧ fetch im s=some (.base .ECALL))
  | some p => Done (some p) s

theorem layers_good {sk : BitVec 256} {output : HashOutput} {sig : SharedForest.Signature}
    {b : SharedCodec.CBytes} {counter : BitVec 32} {forest : Digest × Digest} {pk : Digest} {s : MachineState}
    (h : LayersReady output sig b counter forest pk s) :
    TBSim Images.expandImage sk s 3782800060 (recoverProgram output sig counter forest pk) (SuffixDone Images.expandImage) := by
  have call:=SigGolfCandidate.T3M.Expand.SharedLayers.installed_recover_good (sk:=sk) (vin:=0) h.inv
  unfold recoverProgram
  refine TBSim.bind (W₂:=15800060) call (fun result t ht=>?_)
  cases result with
  | none => exact (TBSim.pure (Q:=SuffixDone Images.expandImage) (a:=none) (Or.inr ht)).mono (by omega) (fun _ _ h=>h)
  | some r =>
    dsimp only
    obtain ⟨tp,t5,troot,clen,dlen,fields,credits,half,regs,frame,_,top,hints,floors,llen,flagP,_,nonces⟩:=ht
    have stable:=h.stable.frame frame (layer_keep _)
    have jump:=SharedControl.validate_step t tp
    let u:=t.setPC (pcOf 46929)
    obtain ⟨v,n,c,hn,hc,uv,vp,vr,vf⟩:=SharedValidateV6.validate_source_steps SharedValidateV6.installed_code
      u rfl sig.policyHints r.digits r.lows h.inv.hintsLt dlen (fun lay=>floors lay lay.isLt) hints
      (fun lay=>credits lay lay.isLt) SharedValidate.threshold1_lt SharedValidate.threshold2_lt
      stable.threshold1 stable.threshold2
    have tf : Frame t v (fun _=>False):=vf
    by_cases valid:SharedForest.policyHintsValid sig.policyHints r.digits r.lows=true
    · rw [if_pos valid] at vp ⊢
      have v5:v.getReg .x5=0 := (vr.get (by decide)).trans t5
      have ready:TopReady output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),r.nonces⟩ b
          r.foldedTop r.root pk v :=
        ready_of_layers h.inv.hidx h.stable h.rho h.dc h.headerZero h.regionZero h.proj h.forestEq
          (fun lay=>fields lay lay.isLt) half frame troot (top (by decide)) tf vp v5
          (by rw [flagP (by decide)]; cases r.lows.getD 0 true <;> rfl) (nonces (by decide))
      have result:=top_good (sk:=sk) SharedControl.installed_srchCore installed_compact SharedZero.installed_code
        SharedScatter.installed_coordinates SharedScatter.installed_after SharedScatter.installed_finish
        SharedScatter.installed_end
        SharedControl.scatter_code SharedControl.compact_code ready
      exact (TBSim.steps (jump.trans uv) result).mono (by omega) (by
        intro rv st hp
        cases rv with
        | none => exact Or.inl hp
        | some p => exact hp)
    · rw [if_neg valid] at vp ⊢
      exact (TBSim.steps (jump.trans uv) (TBSim.pure (Q:=SuffixDone Images.expandImage) (a:=none) (Or.inl vp))).mono
        (by omega) (fun _ _ h=>h)
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M)
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- Pairing stage 1: the signature with a zero top path, the witness of the initial FTS phase (the expander's
initial forest region and the cleared top path area agree with it; the forest only reads `.forest`). -/
def forestSig (sig : SharedForest.Signature) : SharedForest.Signature :=
  { sig with layers := fun lay => ⟨(sig.layers lay).values, fun j => if lay.val = 0 then 0 else (sig.layers lay).path j⟩ }
theorem forestSig_top (sig : SharedForest.Signature) : ∀ j, ((forestSig sig).layers 0).path j = 0 := fun _ => by simp [forestSig]

structure ForestMemory (output : HashOutput) (b : SharedCodec.CBytes) (counter : BitVec 32) (pk : Digest) (s : MachineState) : Prop where
  stable : Stable output b pk s
  inflated : SharedCompact.InflatedAt s b
  hintsLt : (SharedCodec.sigDecC b).policyHints.toNat<7744
  hints : s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat
  dc : s.getMem 0x66008=BitVec.ofNat 64 counter.toNat
  c32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x
  zero : SigGolfCandidate.T3M.Expand.BC.LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
  regionZero : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0=SharedForest.mainSignature (SharedCodec.sigDecC b)

theorem ForestMemory.frame {output : HashOutput} {b : SharedCodec.CBytes} {counter : BitVec 32} {pk : Digest}
    {s t : MachineState} (h : ForestMemory output b counter pk s)
    (hf : Frame s t (fun A=>1152 ≤ A ∧ A<11000)) : ForestMemory output b counter pk t := by
  have mem (A:Nat) (ha:A<2^64) (hn:¬(1152 ≤ A ∧ A<11000)) := hf.get ha hn
  constructor
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;omega)
  · exact h.inflated.frame hf (by intro A ha hb;omega)
  · exact h.hintsLt
  · change t.getMem (BitVec.ofNat 64 0x66000)=_
    rw [mem _ (by decide) (by decide)]
    exact h.hints
  · change t.getMem (BitVec.ofNat 64 0x66008)=_
    rw [mem _ (by decide) (by decide)]
    exact h.dc
  · obtain ⟨x,hx,hm⟩:=h.c32
    exact ⟨x,hx,(mem _ (by unfold ENC;omega) (by unfold ENC;omega)).trans hm⟩
  · exact ⟨(mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c0,
      (mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c8,
      (mem _ (by unfold NODE;omega) (by unfold NODE;omega)).trans h.zero.n32,
      (mem _ (by unfold NODE;omega) (by unfold NODE;omega)).trans h.zero.n40,
      (mem _ (by unfold ENC;omega) (by unfold ENC;omega)).trans h.zero.e40⟩
  · exact h.table.frame hf (by intro i hi;unfold TOP_DATA;omega)
  · exact h.cf.frame hf (by intro i hi hj;unfold TOP_DATA;omega)
  · exact h.reward.frame hf (by intro i hi hj;unfold TOP_DATA;omega)
  · intro A ha hb;rw [mem _ (by omega) (by omega)];exact h.regionZero A ha hb
  · exact h.proj

theorem handoff_ready {output : HashOutput} {b : SharedCodec.CBytes} {counter : BitVec 32} {pk : Digest}
    {pair : Digest × Digest} {s t : MachineState}
    (h : ForestMemory output b counter pk s) (hi:WCT9.digestIndex output<2^31)
    (hp:t.pc=pcOf 249) (h5:t.getReg .x5=0)
    (hL:DigAt s 2904 pair.1) (hR:DigAt s 2952 pair.2)
    (hroots:∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (2904+o)))
    (hrho:∀i,i<2 → t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i)))
    (hdc:t.getMem 2064=s.getMem 0x66008)
    (hzero:∀i,3 ≤ i → i<8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0)
    (hmove:∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i)))
    (hf:Frame s t SharedHandoff.Writes) :
    LayersReady output (SharedCodec.sigDecC b) b counter pair pk t := by
  constructor
  · exact SharedHandoff.layer_inv hp h5 hi h.stable.index h.inflated hL hR hroots hmove hf h.c32 h.zero h.table h.cf h.reward h.hintsLt h.hints h.stable.zt h.stable.t51src
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;unfold SharedHandoff.Writes;omega)
  · have d:=h.inflated.rho
    exact ⟨(hrho 0 (by decide)).trans d.1,(hrho 1 (by decide)).trans d.2⟩
  · exact hdc.trans h.dc
  · exact hzero
  · intro A ha hb
    rw [hf.get (by omega) (by unfold SharedHandoff.Writes;omega)]
    exact h.regionZero A ha hb
  · exact h.proj
  · rfl
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def forestProgram (output : HashOutput) (b : SharedCodec.CBytes) (counter : BitVec 32) (pk : Digest) :
    M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverForest (WCT9.digestIndex output) (SharedForest.forestSelectionFromOutput output)
    (SharedForest.forestWordsFromOutput output) (SharedCodec.sigDecC b).forest >>= fun pair=>
  recoverProgram output (SharedCodec.sigDecC b) counter pair pk

theorem forest_suffix_good {sk : BitVec 256} {output : HashOutput} {b : SharedCodec.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩)) s) :
    TBSim Images.expandImage sk s 3782804681 (forestProgram output b counter pk) (SuffixDone Images.expandImage) := by
  have call:=SharedForestRun.installed_forest_good sk output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩
    (WCT9.digestIndex output) hi s hI
  unfold forestProgram
  refine TBSim.bind (W₂:=3782802665) call (fun pair t ht=>?_)
  obtain ⟨tp,left,right,frame,fields,x8⟩:=ht
  have memory:=hm.frame frame
  obtain ⟨u,tu,up,u2,u5,roots,rho,dc,zeros,moved,regs,fr⟩:=SharedHandoff.steps SharedHandoff.installed_code t tp x8
  have ready:=handoff_ready memory hi up u5 left right roots rho dc zeros moved fr
  exact TBSim.steps tu (layers_good ready)
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem expandN_source (message : Message) (pk : Digest) (b : SharedCodec.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0=SharedCodec.sigDecC b) :
    Paired.expandN message pk (SharedCodec.sigDecC b)=
      if (SharedCodec.sigDecC b).policyHints.toNat ≥ 7744 then pure none else
        SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 (2^21) >>= fun result=>
          match result with
          | none => pure none
          | some (counter,output)=>forestProgram output b counter pk := by
  unfold Paired.expandN
  rw [hfill]
  by_cases bad:(SharedCodec.sigDecC b).policyHints.toNat ≥ 7744
  · simp only [bad,ite_true]
  rw [if_neg bad,if_neg bad]
  apply congrArg (fun k=>SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 (2^21) >>= k)
  funext result
  cases result with
  | none => rfl
  | some pair =>
    rcases pair with ⟨counter,output⟩
    unfold forestProgram recoverProgram
    apply congrArg (fun k=>SharedForest.recoverForest (WCT9.digestIndex output)
      (SharedForest.forestSelectionFromOutput output) (SharedForest.forestWordsFromOutput output)
      (SharedCodec.sigDecC b).forest >>= k)
    funext forest
    apply congrArg (fun k=>SharedForest.recoverHintedLayers (SharedCodec.sigDecC b) (WCT9.digestIndex output)
      (WCT9.topSib (SharedForest.mainSignature (SharedCodec.sigDecC b))) 4 (.pair forest.1 forest.2) >>= k)
    funext layers
    cases layers with
    | none => rfl
    | some layers =>
      dsimp only
      by_cases valid:SharedForest.policyHintsValid (SharedCodec.sigDecC b).policyHints layers.digits layers.lows=true
      · simp only [valid,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
        unfold topProgram
        by_cases root:layers.root=pk
        · simp only [root,ite_true,pure_bind,Option.map_some,hfill]
        · simp only [root,ite_false]
          apply congrArg (fun k=>WCT9.searchTop (WCT9.digestIndex output) layers.foldedTop
            (WCT9.topSib (SharedForest.mainSignature (SharedCodec.sigDecC b))) pk WCT9.searchFuel 1 >>= k)
          funext c
          cases c <;> rfl
      · have vf : SharedForest.policyHintsValid (SharedCodec.sigDecC b).policyHints layers.digits layers.lows=false :=
          Bool.eq_false_iff.mpr valid
        simp only [vf,Bool.not_false,Bool.false_eq_true,ite_true,ite_false]
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research

structure InitialMemory (b : SharedCodec.CBytes) (pk : Digest) (s : MachineState) : Prop where
  plan : ClaudeWCT.W9.Machine.Expand.PlanAt s
  lplan : Compact2.LPlanAt s
  toptab : Compact2.TopTabAt s
  scatterPlan : SharedScatter.PlanAt s
  pk : DigAt s 0xA0 pk
  threshold1 : ∀r,r<56 → s.getByte (BitVec.ofNat 64 (16749456+r))=
    BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r)
  threshold2 : ∀r,r<41 → s.getByte (BitVec.ofNat 64 (16749520+r))=
    BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r)
  zt : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 s
  c32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x
  zero : SigGolfCandidate.T3M.Expand.BC.LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
  regionZero : ∀A,0x2c48≤A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : ClaudeWCT.WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0=
    SharedForest.mainSignature (SharedCodec.sigDecC b)
  t51src : SigGolfCandidate.T3M.Search.T51.T51TableW 0xFF9E00 s

theorem initial_memory (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0 = SharedCodec.sigDecC b) :
    InitialMemory b pk (w9init Images.expandImage m pk b) := by
  have hp := SharedInit.initial_plans m pk b
  have ht := SharedInit.initial_tables m pk b
  have hf := SharedInit.initial_thresholds m pk b
  exact ⟨hp.1,hp.2,SharedInit.initial_toptab m pk b,(SharedInit.initial_data m pk b).plans,
    SharedInit.public_key_of_length Images.expandData_length m pk b,hf.1,hf.2,SharedInit.initial_zt m pk b,
    SharedInit.counter_of_length Images.expandData_length m pk b,
    SharedInit.layer_zero_of_length Images.expandData_length m pk b,
    ht.1,ht.2.1,ht.2.2,SharedInit.region_zero_of_length Images.expandData_length m pk b,
    SharedHandoff.main_projection b hfill,
    SigGolfCandidate.T3M.Search.T51.T51TableW.of_bytes (by decide) (by decide) fun i hi => by
      rw [show 0xFF9E00 + i = SharedInit.DB0 + (4848 + i) by unfold SharedInit.DB0; omega,
        SharedInit.dataByte Images.expandData_length SharedInit.installed_dataBase m pk b (4848 + i) (by omega)]
      exact SigGolfCandidate.T3M.Search.expandData_t51 i hi⟩

end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem halt_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) :
    CodeAt im (pcOf 47012) [0x73] := by
  exact SharedCounterHooks.code_slice (off:=1956) hc (by decide +kernel) (by decide +kernel)

theorem installed_halt : CodeAt Images.expandImage (pcOf 47012) [0x73] :=
  halt_of_driver codeAt_expand_shared_driver

/-- img-v6: the pad writer's final `ecall` (45016). -/
theorem installed_halt_v6 : CodeAt Images.expandImage (pcOf 45016) [0x73] :=
  PadWriter.code_last (by decide) (by decide) (by decide +kernel)


theorem suffix_done {sk : BitVec 256} {r : Option (HashOutput × SharedForest.Witness)} {s : MachineState}
    (h : SuffixDone Images.expandImage r s) :
    TBSim Images.expandImage sk s suffixW (pure r) ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost := by
  cases r with
  | none =>
    rcases h with hp|⟨hp,h5,h10,hfetch⟩
    · obtain ⟨t,st,tp,t5,t10,tfetch⟩:=Search.cs0_spec SharedSearchCode.installed_searchKernel s hp
      exact (TBSim.steps st (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=none)
        ⟨Or.inl tp,t5,t10,tfetch⟩)).mono (by unfold suffixW; omega) (fun _ _ h=>h)
    · exact (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=none)
        ⟨Or.inl hp,h5,h10,hfetch⟩).mono (by unfold suffixW; omega) (fun _ _ h=>h)
  | some p =>
    rcases p with ⟨output,w⟩
    obtain ⟨hp,h5,ph,hn⟩:=h
    obtain ⟨t,st,tp,tr,tbuf,tm⟩:=PostEnc.pp_witEnc s hp output w ph.fts ph.old ph.choice ph.leaf
    have hscr (A:Nat) (h1:0x66700 ≤ A) (h2:A<0x66760) : t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
      rw [tm A (by omega)]; exact PostEnc.ppMem_scratch _ _ A h1 h2
    have hl : (SigGolfCandidate.T3.route (WCT9.digestIndex output) 0).1<4096 := by
      unfold SigGolfCandidate.T3.route; simp [SigGolfCandidate.T3.height]; omega
    have tleaf : (t.getMem (BitVec.ofNat 64 0x66758)).toNat % 4096=(SigGolfCandidate.T3.route (WCT9.digestIndex output) 0).1 % 4096 := by
      rw [hscr _ (by norm_num) (by norm_num),hn.2.2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show _ < 2^64 by omega)]
    have tnon : ∀ j, j < 11 → t.getMem (PadWriter.nonceAddr j)=BitVec.ofNat 64 (w.topNonces.getD j 0) := by
      intro j hj
      unfold PadWriter.nonceAddr
      rw [hscr _ (by omega) (by omega)]
      exact hn.2.1 j hj
    obtain ⟨u,su,up,u10,ur,ubuf,_⟩:=PadWit.pad_hook_witEncN t tp output w tleaf tnon tbuf
    have u5 : u.getReg .x5=1 := by rw [ur .x5 (by simp),tr .x5 (by simp)]; exact h5
    have fetch : fetch Images.expandImage u=some (.base .ECALL) := (installed_halt_v6.fetch u up).trans rfl
    have rb : readBuffer u 4128 22012=Paired.witEncN output w :=
      SharedWitnessOutput.readBuffer_words u 4128 22012 2752 _ (by decide) (by decide) (by decide) ubuf
    exact (TBSim.steps (st.trans su) (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost)
      (a:=some (output,w)) ⟨up,u5,u10,rb,fetch⟩)).mono (by unfold suffixW; omega) (fun _ _ h=>h)

theorem forest_suffix_halted {sk : BitVec 256} {output : HashOutput} {b : SharedCodec.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩)) s) :
    TBSim Images.expandImage sk s (3782804681+suffixW) (forestProgram output b counter pk)
      ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost := by
  simpa only [bind_pure] using
    (TBSim.bind (W₂:=suffixW) (forest_suffix_good hi hm hI) (fun _ _ h=>suffix_done h))
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA NBUF OutAt)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def ClearWrites (A:Nat) : Prop := A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128) ∨ (1152≤A ∧ A<11064)

theorem memory_after_clear {s0 s t:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<7744)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output)
    (hctr:t.getMem 0x66008=BitVec.ofNat 64 counter.toNat)
    (hindex:t.getMem 0x20550=s.getMem 0x20160 >>> 33)
    (hdigest:∀i,i<4 → t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (NBUF+8*i)))
    (hf:Frame s t ClearWrites) : ForestMemory output b counter pk t := by
  have word (A:Nat) (ha:A<2^64) (hS:¬SharedFront.SearchWrites A) (hC:¬ClearWrites A) :
      t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A) :=
    (hf.get ha hC).trans (hs.get ha hS)
  have highWord (A:Nat) (ha:A<2^64) (hA:0xff0000≤A) :
      t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A) := by
    apply word A ha
    · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes
      simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF];omega
    · unfold ClearWrites;omega
  have highByte (A:Nat) (ha:A<2^64) (hA:0xff0000≤A) :
      t.getByte (BitVec.ofNat 64 A)=s0.getByte (BitVec.ofNat 64 A) := by
    apply (hs.trans hf).getByte ha
    rintro (h|h)
    · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes at h
      simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF] at h;omega
    · unfold ClearWrites at h;omega
  have inflated:SharedCompact.InflatedAt t b:=hin.frame hf (by intro A ha hb;unfold ClearWrites;omega)
  constructor
  · constructor
    · intro i hi;exact (hdigest i hi).trans (hout i hi)
    · exact inflated.forest
    · intro i hi;rw[highWord _ (by unfold PLAN;omega) (by unfold PLAN;omega)];exact initial.plan i hi
    · intro i hi;rw[highWord _ (by unfold Compact2.LPLAN;omega) (by unfold Compact2.LPLAN;omega)];exact initial.lplan i hi
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [highWord _ (by unfold Compact2.TOPA;omega) (by unfold Compact2.TOPA;omega)];exact initial.toptab.1 k hk
      · rw [highWord _ (by unfold Compact2.TOPB;omega) (by unfold Compact2.TOPB;omega)];exact initial.toptab.2 k hk
    · intro child j hj
      rw[highByte _ (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by omega)]
      exact initial.scatterPlan child j hj
    · constructor
      · exact (word 160 (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.pk.1
      · exact (word 168 (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.pk.2
    · change t.getMem (0x20550:Word)=_
      rw[hindex]
      have ho:s.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
      rw[ho];exact Compact2.index_shr output
    · intro r hr;rw[highByte _ (by omega) (by omega)];exact initial.threshold1 r hr
    · intro r hr;rw[highByte _ (by omega) (by omega)];exact initial.threshold2 r hr
    · intro r hr;rw[highByte _ (by rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl];omega)
        (by rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl];omega)];exact initial.zt r hr
    · exact initial.t51src.frame (hs.trans hf) (by decide) (by decide) (fun k hk h => by
        rcases h with h|h
        · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes at h
          simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF] at h;omega
        · unfold ClearWrites at h;omega)
  · exact inflated
  · exact hh
  · exact (hf.get (A:=0x66000) (by decide) (by unfold ClearWrites;decide)).trans hhmem
  · exact hctr
  · obtain ⟨x,hx,hm⟩:=initial.c32
    exact ⟨x,hx,(word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans hm⟩
  · exact ⟨(word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c0,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c8,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.n32,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.n40,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.e40⟩
  · intro i hi;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.table i hi
  · intro i hi hj;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.cf i hi hj
  · intro i hi hj;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.reward i hi hj
  · intro A ha hb
    rw[hf.get (by omega) (by unfold ClearWrites;omega)]
    by_cases hz:A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8
    · exact hsetup A hz
    · rw[hs.get (by omega) (by
        unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes
        simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF];omega)]
      exact initial.regionZero A ha hb
  · exact initial.proj
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem cleared_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<7744)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226) :
    ∃t,Steps Images.expandImage s 3740 3740 t ∧ t.pc=pcOf 45257 ∧
      (∀ (off:Nat),off+8≤8160 → off%8=0 → t.getMem (BitVec.ofNat 64 (2904+off))=0) ∧
      t.getMem 417824=0 ∧ t.getMem 0x66010=BitVec.ofNat 64 (WCT9.digestIndex output) ∧
      OutAt t NBUF output ∧ ForestMemory output b counter pk t := by
  have jump:=ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary.expand_steps ClaudeWCT.W9.Machine.Expand.SharedDigestCode.installed_success s hp
  let u:=s.setPC (pcOf 45232)
  obtain ⟨t,ut,tp,zeros,mode,ctr,index,idx,digest,regs,frame⟩:=
    SharedZero.accepted_clear SharedZero.installed_code u rfl h17
  have memory:ForestMemory output b counter pk t:=
    memory_after_clear initial hin hh hhmem hs hsetup hout (ctr.trans h19) idx digest frame
  refine ⟨t,jump.trans ut,tp,?_,mode,?_,?_,memory⟩
  · intro off hb ha;exact zeros (2904+off) (by omega) (by omega) (by omega)
  · rw[index]
    have ho:u.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
    rw[ho];exact Compact2.index_shr output
  · intro i hi
    exact (frame.get (by unfold NBUF;omega) (by simp only [ClearWrites,NBUF];omega)).trans (hout i hi)
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem accepted_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<7744)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226)
    (hrank:∀k:Fin 9,SharedForest.rawForestRank output k.val<563) :
    ∃t,Steps Images.expandImage s 4996 5173 t ∧ ForestMemory output b counter pk t ∧
      SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩)
        (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
        (fun k=>SharedForest.forestRank output k.val) t 0
        (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩)) t := by
  obtain ⟨u,su,up,uz,um,ui,uo,uf⟩:=cleared_front initial hin hh hhmem hs hsetup hout h19 h17 hp
  have fields:=SharedForestRun.fields_of_output u output (WCT9.digestIndex output) ui uo hrank
  obtain ⟨t,ut,ht,hframe⟩:=SharedScatter.scatter_forest_pre SharedScatter.installed_coordinates SharedScatter.installed_after
    output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[]⟩ b (WCT9.digestIndex output) u up uf.inflated rfl
    fields uf.stable.scatterPlan um uz rfl (forestSig_top _)
  exact ⟨t,su.trans ut,uf.frame hframe,ht⟩
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.ExpandLink (PairedExpPost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem initial_pc (message : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    (w9init Images.expandImage message pk b).pc=pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg,MachineState.pc_writeBytesAsWords,MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords,MachineState.pc_writeBytesAsWords]
  rfl

theorem initial_x5 (message : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    (w9init Images.expandImage message pk b).getReg .x5=0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [MachineState.getReg_writeBytesAsWords]
  rfl

/-- Cycle budget after the digest search (layers + top + compaction/scatter + img-v6 witness tail). -/
def searchedW : Nat := 3782809854 + suffixW

theorem searched_continue {sk : BitVec 256} {s0 s : MachineState} {pk : Digest} {b : SharedCodec.CBytes}
    (initial : InitialMemory b pk s0) (hh:(SharedCodec.sigDecC b).policyHints.toNat<7744)
    {r : Option (BitVec 32 × HashOutput)} (hs : SharedFront.Searched s0 b r s) :
    TBSim Images.expandImage sk s searchedW
      (match r with | none=>pure none | some (counter,output)=>forestProgram output b counter pk) PairedExpPost := by
  cases r with
  | none =>
    obtain ⟨t,st,tp,t5,t10,regs,frame⟩:=Sign.SharedDigestBoundary.failure_steps true
      SharedDigestCode.installed_failure s hs.result
    have pc:t.pc=pcOf 45231:=tp
    have hf:fetch Images.expandImage t=some (.base .ECALL):=
      (SharedDigestCode.installed_failure_ecall.fetch t pc).trans rfl
    exact (TBSim.steps st (TBSim.pure (Q:=PairedExpPost) (a:=none)
      ⟨Or.inr pc,t5,t10,hf⟩)).mono (by unfold searchedW; omega) (fun _ _ h=>h)
  | some result =>
    rcases result with ⟨counter,output⟩
    obtain ⟨hp,h19,hc,ha,hout⟩:=hs.result
    have hrank:=((SharedForest.accepted_conditions output ha).2.1)
    obtain ⟨t,st,memory,inv⟩:=accepted_front initial hs.inflated hh hs.hints hs.frame hs.setupZero hout h19
      hs.resultR17 hp hrank
    exact (TBSim.steps st (forest_suffix_halted (WCT9.digestIndex_lt output) memory inv)).mono
      (by unfold searchedW; omega) (fun _ _ h=>h)

end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem paired_expand_tbsim : PairedExpandSimulation := by
  intro sk message pk b
  -- T51: word 0 jumps to DEC (54569), which writes the inflated slot layout of the 5,195-byte signature at `0x7000`
  -- and the hint at `0x66000` (a hint `≥ 7744` exits at word 354), then `j 1`; the front runs from word 1 on the
  -- real initial state `w9init .. b`.
  have hfill : SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0=SharedCodec.sigDecC b :=
    SharedCodec.fill_sigDecC b
  rw [expandN_source message pk _ hfill]
  by_cases bad:7744≤(SharedCodec.sigDecC b).policyHints.toNat
  · rw [if_pos bad]
    obtain ⟨t,st,tp⟩:=PrePass.dec_reject message pk b bad
    exact (TBSim.steps st (suffix_done (r:=none) (Or.inl tp))).mono
      (by unfold pairedExpandCost suffixW; omega) (fun _ _ h=>h)
  · rw [if_neg bad]
    have hh:(SharedCodec.sigDecC b).policyHints.toNat<7744:=by omega
    obtain ⟨u,su,up,ureg,uin,uh,uf⟩:=PrePass.dec_init message pk b hh
    have hmsg : ∀ k, k<4 → u.getMem (BitVec.ofNat 64 (0x6620+8*k))=message.extractLsb' (64*k) 64 := fun k hk =>
      (uf.get (by omega) (by omega)).trans
        (SharedInit.msgWord Images.expandData_length SharedInit.installed_dataBase message pk _ k hk)
    have u5 : u.getReg .x5=0 := (ureg .x5).trans (initial_x5 message pk _)
    obtain ⟨t,st,ready⟩:=SharedFront.prepare SharedFront.installed_tail
      SharedFront.installed_zero SharedFront.installed_jump _ u message b up u5 uin uh hmsg
      ((SharedInit.initial_data message pk _).frame uf (by intro A h1 h2; unfold SharedInit.DB at h1 h2; omega)) uf
    have search:=SharedFront.search_prepared (sk:=sk) SharedDigestCode.installed_look ready
    have continuation:=TBSim.bind (W₂:=searchedW) search
      (fun r s hs=>searched_continue (initial_memory message pk _ hfill) hh hs)
    exact (TBSim.steps (su.trans st) continuation).mono
      (by unfold pairedExpandCost SharedCompactMain.searchedW; omega) (fun _ _ h=>h)

theorem paired_expand_pending : Final.Paired.ExpandRefines I0 ∧ Final.Paired.ExpandTerminates I0 :=
  paired_expand_pending_of paired_expand_tbsim
end ClaudeWCT.W9.Machine.ExpandLink
end
-- ==== merged from T3M_FullCache_MacPass ====
section

namespace SigGolfCandidate.T3M.FullCache.MacPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SphincsSecurity
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
def fold61 (x : Nat) : Nat := x / 2 ^ 61 + x % 2 ^ 61
theorem fold61_mod (x : Nat) : fold61 x % macPrime = x % macPrime := by
  unfold fold61 macPrime
  have := Nat.div_add_mod x (2 ^ 61)
  simp only [Nat.reducePow, Nat.reduceSub] at *
  omega
def macStep (acc c k : Nat) : Nat := fold61 (fold61 ((acc + c) * k))
theorem macStep_mod (acc c k : Nat) : macStep acc c k % macPrime = (acc + c) * k % macPrime := by
  unfold macStep; rw [fold61_mod, fold61_mod]
theorem mul_lt_123 (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    (acc + c) * k < 2 ^ 123 :=
  calc (acc + c) * k < 2 ^ 62 * 2 ^ 61 := Nat.mul_lt_mul'' (by omega) hk
    _ = 2 ^ 123 := by norm_num
theorem fold61_lt_64 (m : Nat) (hm : m < 2 ^ 123) : fold61 m < 2 ^ 64 := by
  unfold fold61
  have h1 : m / 2 ^ 61 < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have h2 := Nat.mod_lt m (show 0 < 2 ^ 61 by norm_num)
  omega
theorem fold61_small (s : Nat) (hs : s < 2 ^ 64) : fold61 s < 2 ^ 61 + 7 := by
  unfold fold61
  have h2 := Nat.mod_lt s (show 0 < 2 ^ 61 by norm_num)
  omega
theorem macStep_lt (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    macStep acc c k < 2 ^ 61 + 7 :=
  fold61_small _ (fold61_lt_64 _ (mul_lt_123 acc c k hacc hc hk))
def macStep2 (k acc w : Nat) : Nat := macStep (macStep acc (w % 2 ^ 32) k) (w / 2 ^ 32) k
def passAcc (k : Nat) (ws : List Nat) : Nat := ws.foldl (macStep2 k) 0
def chunksOf (ws : List Nat) : List Nat := ws.flatMap fun w => [w % 2 ^ 32, w / 2 ^ 32]
theorem foldl_macStep2 (k : Nat) (hk : k < 2 ^ 61) (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 61 + 7) (hab : a % macPrime = b % macPrime) :
    ws.foldl (macStep2 k) a < 2 ^ 61 + 7 ∧
      ws.foldl (macStep2 k) a % macPrime =
        (chunksOf ws).foldl (fun acc c => (acc + c) * k % macPrime) b % macPrime := by
  induction ws generalizing a b with
  | nil => exact ⟨ha, hab⟩
  | cons w ws ih =>
    have hw := hws w (by simp)
    have h1 : w % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    have h2 : w / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hw (by norm_num)
    have hlt1 := macStep_lt a (w % 2 ^ 32) k ha h1 hk
    have hlt2 := macStep_lt _ (w / 2 ^ 32) k hlt1 h2 hk
    simp only [List.foldl_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append]
    refine ih (fun x hx => hws x (by simp [hx])) _ _ hlt2 ?_
    unfold macStep2
    rw [macStep_mod, Nat.mod_mod]
    refine Nat.ModEq.mul_right k (Nat.ModEq.add_right _ ?_)
    show macStep a (w % 2 ^ 32) k % macPrime = (b + w % 2 ^ 32) * k % macPrime % macPrime
    rw [macStep_mod, Nat.mod_mod]
    exact Nat.ModEq.mul_right k (Nat.ModEq.add_right _ hab)
theorem passAcc_spec (k : Nat) (hk : k < 2 ^ 61) (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 64) :
    passAcc k ws < 2 ^ 61 + 7 ∧ passAcc k ws % macPrime = polyMac k (chunksOf ws) := by
  obtain ⟨h1, h2⟩ := foldl_macStep2 k hk ws hws 0 0 (by norm_num) rfl
  refine ⟨h1, h2.trans ?_⟩
  unfold polyMac
  generalize chunksOf ws = cs
  rcases List.eq_nil_or_concat cs with rfl | ⟨cs', c, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.mod_mod]
theorem canon_eq (acc : Nat) (hacc : acc < 2 ^ 61 + 7) :
    (if fold61 acc = macPrime then 0 else fold61 acc) = acc % macPrime := by
  have hm := fold61_mod acc
  have hlt : fold61 acc ≤ macPrime := by
    unfold fold61 macPrime
    have h2 := Nat.mod_lt acc (show 0 < 2 ^ 61 by norm_num)
    simp only [Nat.reducePow, Nat.reduceSub] at *
    omega
  split_ifs with h
  · rw [← hm, h, Nat.mod_self]
  · rw [← hm, Nat.mod_eq_of_lt (lt_of_le_of_ne hlt h)]
theorem mulhu_toNat (a b : Word) : (rv64_mulhu a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  unfold rv64_mulhu
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show a.toNat * b.toNat < 2 ^ 128 by omega)]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  exact hab
theorem and_p_toNat (x : Word) : (x &&& BitVec.ofNat 64 (2 ^ 61 - 1)).toNat = x.toNat % 2 ^ 61 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.and_two_pow_sub_one_eq_mod]
def stepW (acc c k p : Word) : Word :=
  let t := c + acc
  let hi := rv64_mulhu t k
  let lo := t * k
  let s := (hi <<< 3) + (lo >>> 61) + (lo &&& p)
  (s >>> 61) + (s &&& p)
theorem stepW_ofNat (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    stepW (BitVec.ofNat 64 acc) (BitVec.ofNat 64 c) (BitVec.ofNat 64 k) (BitVec.ofNat 64 (2 ^ 61 - 1)) =
      BitVec.ofNat 64 (macStep acc c k) := by
  have hm := mul_lt_123 acc c k hacc hc hk
  have hs := fold61_lt_64 _ hm
  apply BitVec.eq_of_toNat_eq
  unfold stepW macStep
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, and_p_toNat,
    mulhu_toNat, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c + acc < 2 ^ 64 by omega),
    Nat.add_comm c acc]
  generalize (acc + c) * k = m at hm hs ⊢
  have hhi : m / 2 ^ 64 < 2 ^ 59 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have e1 : m / 2 ^ 64 * 2 ^ 3 % 2 ^ 64 = m / 2 ^ 64 * 8 := by
    rw [show (2 : Nat) ^ 3 = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have e2 : m / 2 ^ 64 * 8 + m % 2 ^ 64 / 2 ^ 61 = m / 2 ^ 61 := by
    have := Nat.div_add_mod m (2 ^ 64)
    omega
  have e3 : m % 2 ^ 64 % 2 ^ 61 = m % 2 ^ 61 := Nat.mod_mod_of_dvd m (by norm_num)
  have h61 : m / 2 ^ 61 < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have h61' := Nat.mod_lt m (show 0 < 2 ^ 61 by norm_num)
  rw [e1, e3, Nat.mod_eq_of_lt (show m / 2 ^ 64 * 8 + m % 2 ^ 64 / 2 ^ 61 < 2 ^ 64 by omega), e2,
    Nat.mod_eq_of_lt (show m / 2 ^ 61 + m % 2 ^ 61 < 2 ^ 64 by omega)]
  rfl
def tailW (acc p pad : Word) : Word :=
  let a := (acc &&& p) + (acc >>> 61)
  let b : Word := if BitVec.ult (a ^^^ p) 1 then 1 else 0
  (a &&& (b + 18446744073709551615#64)) + pad
theorem tailW_ofNat (acc : Nat) (hacc : acc < 2 ^ 61 + 7) (pad : Word) :
    tailW (BitVec.ofNat 64 acc) (BitVec.ofNat 64 (2 ^ 61 - 1)) pad =
      BitVec.ofNat 64 (acc % macPrime) + pad := by
  have hc := canon_eq acc hacc
  have ha : (BitVec.ofNat 64 acc &&& BitVec.ofNat 64 (2 ^ 61 - 1)) + (BitVec.ofNat 64 acc >>> 61) =
      BitVec.ofNat 64 (fold61 acc) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, and_p_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega), BitVec.toNat_ofNat]
    unfold fold61
    rw [Nat.add_comm]
  unfold tailW
  simp only [ha]
  have hf : fold61 acc < 2 ^ 64 := by have := fold61_small acc (by omega); omega
  by_cases h : fold61 acc = macPrime
  · rw [if_pos h] at hc
    rw [← hc, h]
    have : BitVec.ult (BitVec.ofNat 64 macPrime ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = true := by
      show BitVec.ult (BitVec.ofNat 64 (2 ^ 61 - 1) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = true
      rw [BitVec.xor_self]; rfl
    have e : ((1 : Word) + 18446744073709551615#64) = 0 := by decide
    rw [this, if_pos rfl, e]
    simp
  · rw [if_neg h] at hc
    have hx : BitVec.ult (BitVec.ofNat 64 (fold61 acc) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = false := by
      rw [Bool.eq_false_iff]
      intro hu
      apply h
      have hu' : (BitVec.ofNat 64 (fold61 acc) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)).toNat < (1#64).toNat :=
        of_decide_eq_true hu
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf,
        Nat.mod_eq_of_lt (by norm_num)] at hu'
      have h0 := Nat.lt_one_iff.mp hu'
      have hm : macPrime = fold61 acc := by
        calc macPrime = (fold61 acc ^^^ fold61 acc) ^^^ (2 ^ 61 - 1) := by rw [Nat.xor_self, Nat.zero_xor]; rfl
          _ = fold61 acc ^^^ (fold61 acc ^^^ (2 ^ 61 - 1)) := Nat.xor_assoc _ _ _
          _ = fold61 acc := by rw [h0, Nat.xor_zero]
      exact hm.symm
    rw [hx, ← hc]
    have e : ((0 : Word) + 18446744073709551615#64) = BitVec.allOnes 64 := by decide
    simp only [Bool.false_eq_true, if_false]
    rw [e, BitVec.and_allOnes]
theorem ofNat_toNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem byteOffset_ofNat {x : Nat} (hx : x < 2 ^ 64) : byteOffset (BitVec.ofNat 64 x) = x % 8 := by
  rw [byteOffset_eq, ofNat_toNat_lt hx]
theorem alignToDword_ofNat_aligned {x : Nat} (hx : x < 2 ^ 64) (h8 : x % 8 = 0) :
    alignToDword (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, ofNat_toNat_lt hx]; omega
theorem exec_load {s : MachineState} {k : LoadKind} {rd rs : Reg} {off : Word}
    (h : accessValid (s.getReg rs + off) k.width = true) :
    (Micro.load k rd rs off).exec s = some ((s.setReg rd (k.read s (s.getReg rs + off))).setPC (s.pc + 4)) := by
  simp [Micro.exec, h]
theorem getReg_setReg' (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  cases r <;> cases r' <;> rfl
@[simp] theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
theorem microN {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    {s t u : MachineState} (m : Micro) {k c n : Nat}
    (hc : CodeAt image pc (w :: ws)) (hpc : s.pc = pc)
    (hd : ∃ i, decodeInstruction w = some i ∧ classify i = some m ∧ instructionCycles i = n)
    (hex : m.exec s = some t) (tail : Steps image t k c u) : Steps image s (k + 1) (n + c) u := by
  obtain ⟨i, h1, h2, h3⟩ := hd
  have := Steps.step (hc.fetch s hpc ▸ h1) ((classify_sound h2 s).trans hex) tail
  rwa [h3] at this
theorem codeAt_drop {image : Image} : ∀ (n : Nat) {pc : Word} {code : List (BitVec 32)},
    CodeAt image pc code → n ≤ code.length → CodeAt image (pc + BitVec.ofNat 64 (4 * n)) (code.drop n)
  | 0, pc, code, h, _ => by simpa using h
  | n + 1, pc, [], h, hn => by simp at hn
  | n + 1, pc, w :: ws, h, hn => by
      have h' := codeAt_drop n h.tail (by simpa using hn)
      have e : pc + 4 + BitVec.ofNat 64 (4 * n) = pc + BitVec.ofNat 64 (4 * (n + 1)) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]
        omega
      rw [List.drop_succ_cons, ← e]
      exact h'
def macPassCode : List (BitVec 32) :=
  [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem read_wu0 (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24) :
    LoadKind.wu.read s (BitVec.ofNat 64 A + 0) =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 A)).toNat % 2 ^ 32) := by
  have e0 : BitVec.ofNat 64 A + 0 = BitVec.ofNat 64 A := by simp
  rw [e0, LoadKind.read_sub _ _ _ (by decide), byteOffset_ofNat (by omega),
    alignToDword_ofNat_aligned (by omega) hA]
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, hA, Nat.shiftRight_eq_div_pow]
theorem read_wu4 (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24) :
    LoadKind.wu.read s (BitVec.ofNat 64 A + 4) =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 A)).toNat / 2 ^ 32) := by
  have e : BitVec.ofNat 64 A + 4 = BitVec.ofNat 64 (A + 4) := by
    apply BitVec.eq_of_toNat_eq; simp
  have ea : alignToDword (BitVec.ofNat 64 (A + 4)) = BitVec.ofNat 64 A := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]; omega
  rw [e, LoadKind.read_sub _ _ _ (by decide), byteOffset_ofNat (by omega), ea]
  apply BitVec.eq_of_toNat_eq
  have hw := (s.getMem (BitVec.ofNat 64 A)).isLt
  simp [LoadKind.fromWord, extractWord32, show (A + 4) % 8 = 4 by omega, Nat.shiftRight_eq_div_pow]
  omega
theorem chunk0_steps {image : Image} {pc : Word} {rest : List (BitVec 32)}
    (hc : CodeAt image pc (0x0006e783 :: 0x00e787b3 :: 0x0377b833 :: 0x037787b3 :: 0x00381813 :: 0x03d7d893 :: 0x01180833 :: 0x0127f7b3 :: 0x00f80833 :: 0x03d85713 :: 0x01287833 :: 0x01070733 :: rest))
    (s : MachineState) (hpc : s.pc = pc)
    (hv : accessValid (s.getReg .x13 + 0) (LoadKind.width .wu) = true) :
    ∃ u, Steps image s 12 18 u ∧ u.pc = pc + 48 ∧
      u.getReg .x14 = stepW (s.getReg .x14) (LoadKind.wu.read s (s.getReg .x13 + 0)) (s.getReg .x23)
        (s.getReg .x18) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hc8 := hc7.tail
  have hc9 := hc8.tail
  have hc10 := hc9.tail
  have hc11 := hc10.tail
  refine ⟨_, microN (.load .wu .x15 .x13 0) hc hpc ⟨_, rfl, rfl, rfl⟩ (exec_load hv) <|
    microN (.alu .x15 .add (.reg .x15) (.reg .x14)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .mulhu (.reg .x15) (.reg .x23)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .mul (.reg .x15) (.reg .x23)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .sll (.reg .x16) (.imm 3)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x17 .srl (.reg .x15) (.imm 61)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x17)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .and (.reg .x15) (.reg .x18)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x15)) hc8 ?p8 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .srl (.reg .x16) (.imm 61)) hc9 ?p9 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .and (.reg .x16) (.reg .x18)) hc10 ?p10 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x16)) hc11 ?p11 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, stepW]
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp
theorem chunk4_steps {image : Image} {pc : Word} {rest : List (BitVec 32)}
    (hc : CodeAt image pc (0x0046e783 :: 0x00e787b3 :: 0x0377b833 :: 0x037787b3 :: 0x00381813 :: 0x03d7d893 :: 0x01180833 :: 0x0127f7b3 :: 0x00f80833 :: 0x03d85713 :: 0x01287833 :: 0x01070733 :: rest))
    (s : MachineState) (hpc : s.pc = pc)
    (hv : accessValid (s.getReg .x13 + 4) (LoadKind.width .wu) = true) :
    ∃ u, Steps image s 12 18 u ∧ u.pc = pc + 48 ∧
      u.getReg .x14 = stepW (s.getReg .x14) (LoadKind.wu.read s (s.getReg .x13 + 4)) (s.getReg .x23)
        (s.getReg .x18) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hc8 := hc7.tail
  have hc9 := hc8.tail
  have hc10 := hc9.tail
  have hc11 := hc10.tail
  refine ⟨_, microN (.load .wu .x15 .x13 4) hc hpc ⟨_, rfl, rfl, rfl⟩ (exec_load hv) <|
    microN (.alu .x15 .add (.reg .x15) (.reg .x14)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .mulhu (.reg .x15) (.reg .x23)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .mul (.reg .x15) (.reg .x23)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .sll (.reg .x16) (.imm 3)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x17 .srl (.reg .x15) (.imm 61)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x17)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .and (.reg .x15) (.reg .x18)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x15)) hc8 ?p8 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .srl (.reg .x16) (.imm 61)) hc9 ?p9 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .and (.reg .x16) (.reg .x18)) hc10 ?p10 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x16)) hc11 ?p11 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, stepW]
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp
theorem body_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 6))
    (s : MachineState) (hpc : s.pc = pc) (A acc k E : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 acc) (hacc : acc < 2 ^ 61 + 7)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 k) (hk : k < 2 ^ 61)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 E) (hE : E < 2 ^ 64) :
    ∃ u, Steps image s 26 38 u ∧
      u.pc = (if A + 8 = E then pc + 104 else pc) ∧
      u.getReg .x13 = BitVec.ofNat 64 (A + 8) ∧
      u.getReg .x14 = BitVec.ofNat 64 (macStep2 k acc (s.getMem (BitVec.ofNat 64 A)).toNat) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hv : ∀ off : Nat, off = 0 ∨ off = 4 →
      accessValid (BitVec.ofNat 64 A + BitVec.ofNat 64 off) 4 = true := by
    intro off hoff
    rw [accessValid_iff, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show A + off < 2 ^ 64 by omega)]
    exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
  have hw := (s.getMem (BitVec.ofNat 64 A)).isLt
  generalize hwdef : (s.getMem (BitVec.ofNat 64 A)).toNat = w at hw
  have hlo : w % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hhi : w / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hw (by norm_num)
  obtain ⟨u0, st0, pc0, a0, r0, m0⟩ := chunk0_steps (rest := macPassCode.drop 18) hc s hpc
    (by rw [h13]; exact hv 0 (Or.inl rfl))
  rw [h13, h14, h23, h18, read_wu0 s A hA hA', hwdef,
    stepW_ofNat acc (w % 2 ^ 32) k hacc hlo hk] at a0
  have hlt1 := macStep_lt acc (w % 2 ^ 32) k hacc hlo hk
  have hc4 : CodeAt image (pc + 48) (macPassCode.drop 18) := codeAt_drop 12 hc (by decide)
  have e13 : u0.getReg .x13 = BitVec.ofNat 64 A := by
    rw [r0 .x13 (by decide) (by decide) (by decide) (by decide), h13]
  have e23 : u0.getReg .x23 = BitVec.ofNat 64 k := by
    rw [r0 .x23 (by decide) (by decide) (by decide) (by decide), h23]
  have e18 : u0.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1) := by
    rw [r0 .x18 (by decide) (by decide) (by decide) (by decide), h18]
  obtain ⟨u1, st1, pc1, a1, r1, m1⟩ := chunk4_steps (rest := macPassCode.drop 30) hc4 u0 pc0
    (by rw [e13]; exact hv 4 (Or.inr rfl))
  rw [e13, a0, e23, e18, read_wu4 u0 A hA hA', m0, hwdef,
    stepW_ofNat _ (w / 2 ^ 32) k hlt1 hhi hk] at a1
  have hc5 : CodeAt image (pc + 48 + 48) (macPassCode.drop 30) := codeAt_drop 12 hc4 (by decide)
  have hc6 := hc5.tail
  have x13 : u1.getReg .x13 = BitVec.ofNat 64 A := by
    rw [r1 .x13 (by decide) (by decide) (by decide) (by decide), e13]
  have x19 : u1.getReg .x19 = BitVec.ofNat 64 E := by
    rw [r1 .x19 (by decide) (by decide) (by decide) (by decide),
      r0 .x19 (by decide) (by decide) (by decide) (by decide), h19]
  have st2 : Steps image u1 2 2 _ :=
    microN (.alu .x13 .add (.reg .x13) (.imm 8)) hc5 pc1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.branch .ne .x13 .x19 0xffffffffffffff9c) hc6 (by simp [pc1]) ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _
  have e8 : BitVec.ofNat 64 A + 8#64 = BitVec.ofNat 64 (A + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hcond : (BitVec.ofNat 64 (A + 8) = BitVec.ofNat 64 E) ↔ A + 8 = E := by
    constructor
    · intro hh
      have := congrArg BitVec.toNat hh
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hE] at this
    · rintro rfl; rfl
  refine ⟨_, (st0.trans (st1.trans st2)).of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [getReg_setReg', Src.eval, BinOp.eval, CmpOp.eval, x13, x19, pc1]
    simp only [e8, hcond]
    split_ifs
    · bv_omega
    · bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, x13, e8]
  · simp [getReg_setReg', Src.eval, BinOp.eval, a1, macStep2]
  · intro r h1 h2 h3 h4 h5
    simp [getReg_setReg', h1]
    rw [r1 r h2 h3 h4 h5, r0 r h2 h3 h4 h5]
  · intro a
    simp [m1, m0]
theorem loop_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 6))
    (s : MachineState) (hpc : s.pc = pc) (B0 n k : Nat) (ws : List Nat) (hn : 0 < n)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 B0) (hB : B0 % 8 = 0) (hB' : B0 + 8 * n ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 0)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 k) (hk : k < 2 ^ 61)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 (B0 + 8 * n))
    (hlen : ws.length = n)
    (hmem : ∀ i < n, (s.getMem (BitVec.ofNat 64 (B0 + 8 * i))).toNat = ws.getD i 0) :
    ∃ u, Steps image s (n * 26) (n * 38) u ∧ u.pc = pc + 104 ∧
      u.getReg .x14 = BitVec.ofNat 64 (passAcc k ws) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hws : ∀ w ∈ ws, w < 2 ^ 64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have := hmem i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [← this]; exact BitVec.isLt _
  let Inv : Nat → MachineState → Prop := fun i t =>
    i ≤ n ∧ t.pc = (if i = 0 then pc + 104 else pc) ∧
    t.getReg .x13 = BitVec.ofNat 64 (B0 + 8 * (n - i)) ∧
    t.getReg .x14 = BitVec.ofNat 64 ((ws.take (n - i)).foldl (macStep2 k) 0) ∧
    (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → t.getReg r = s.getReg r) ∧
    ∀ a, t.getMem a = s.getMem a
  have body : ∀ i t, Inv (i + 1) t → ∃ u, Steps image t 26 38 u ∧ Inv i u := by
    intro i t ⟨hi, tpc, t13, t14, treg, tmem⟩
    have hj : n - (i + 1) < n := by omega
    have hacc := (foldl_macStep2 k hk (ws.take (n - (i + 1)))
      (fun w hw => hws w (List.mem_of_mem_take hw)) 0 0 (by norm_num) rfl).1
    obtain ⟨u, st, upc, u13, u14, ureg, umem⟩ := body_steps hc t (by simpa using tpc)
      (B0 + 8 * (n - (i + 1))) _ k (B0 + 8 * n) t13 (by omega) (by omega) t14 hacc
      (by rw [treg .x23 (by decide) (by decide) (by decide) (by decide) (by decide), h23]) hk
      (by rw [treg .x18 (by decide) (by decide) (by decide) (by decide) (by decide), h18])
      (by rw [treg .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h19]) (by omega)
    refine ⟨u, st, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [upc]
      by_cases h0 : i = 0
      · subst h0; rw [if_pos (by omega), if_pos rfl]
      · rw [if_neg (by omega), if_neg h0]
    · rw [u13]; congr 1; omega
    · rw [u14, tmem, hmem _ hj]
      congr 1
      have e : n - i = (n - (i + 1)) + 1 := by omega
      rw [e, List.take_add_one, List.foldl_append, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      simp
    · intro r h1 h2 h3 h4 h5
      rw [ureg r h1 h2 h3 h4 h5, treg r h1 h2 h3 h4 h5]
    · intro a; rw [umem, tmem]
  have hinit : Inv n s := by
    refine ⟨le_refl _, ?_, ?_, ?_, fun _ _ _ _ _ _ => rfl, fun _ => rfl⟩
    · rw [hpc, if_neg (by omega)]
    · simpa using h13
    · simpa using h14
  obtain ⟨u, st, _, upc, _, u14, ureg, umem⟩ := Steps.iterate Inv body n s hinit
  refine ⟨u, st, by simpa using upc, ?_, ureg, umem⟩
  rw [u14, Nat.sub_zero, ← hlen, List.take_length]
  rfl
theorem valid_d (B : Nat) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24) (off : Word) (hoff : off = 0 ∨ off = 8) :
    accessValid (BitVec.ofNat 64 B + off) 8 = true := by
  have z : BitVec.ofNat 64 B + (0 : Word) = BitVec.ofNat 64 B := by simp
  have e0 : (BitVec.ofNat 64 B + (0 : Word)).toNat = B := by
    rw [z, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e8 : (BitVec.ofNat 64 B + (8 : Word)).toNat = B + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (show B < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [accessValid_iff]
  rcases hoff with rfl | rfl
  · rw [e0]; exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
  · rw [e8]; exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
theorem head_steps {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1)) :
    ∃ u, Steps image s 6 6 u ∧ u.pc = pc + 24 ∧
      u.getReg .x23 = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) ∧
      u.getReg .x24 = s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      u.getReg .x13 = BitVec.ofNat 64 0x80020 ∧ u.getReg .x14 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x23 → r ≠ .x24 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have e8 : BitVec.ofNat 64 B + 8#64 = BitVec.ofNat 64 (B + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have k_eq : s.getMem (BitVec.ofNat 64 B) &&& s.getReg .x18 =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) := by
    rw [h18]
    apply BitVec.eq_of_toNat_eq
    rw [and_p_toNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt (s.getMem (BitVec.ofNat 64 B)).toNat
      (show 0 < 2 ^ 61 by norm_num)) (show 2 ^ 61 ≤ 2 ^ 64 by norm_num))).symm
  refine ⟨_, microN (.load .d .x23 .x22 0) hc hpc ⟨_, rfl, rfl, rfl⟩
      (exec_load (by rw [h22]; exact valid_d B hB hB' 0 (Or.inl rfl))) <|
    microN (.alu .x23 .and (.reg .x23) (.reg .x18)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.load .d .x24 .x22 8) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩
      (exec_load (by
        simp only [getReg_setReg', MachineState.getReg_setPC]
        simp [h22]
        exact valid_d B hB hB' 8 (Or.inr rfl))) <|
    microN (.alu .x13 .add (.imm 0x80000) (.imm 0)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x13 .add (.reg .x13) (.imm 32)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x0) (.imm 0)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, LoadKind.read, h22, k_eq]
  · simp [getReg_setReg', Src.eval, BinOp.eval, LoadKind.read, h22, e8]
  · simp [getReg_setReg', Src.eval, BinOp.eval]
  · simp [getReg_setReg', Src.eval, BinOp.eval]
    rfl
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp
theorem tail_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 32))
    (s : MachineState) (hpc : s.pc = pc) :
    ∃ u, Steps image s 8 8 u ∧ u.pc = pc + 32 ∧
      u.getReg .x14 = tailW (s.getReg .x14) (s.getReg .x18) (s.getReg .x24) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  refine ⟨_, microN (.alu .x15 .srl (.reg .x14) (.imm 61)) hc hpc ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .and (.reg .x14) (.reg .x18)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x15)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .xor (.reg .x14) (.reg .x18)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .sltu (.reg .x15) (.imm 1)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .add (.reg .x15) (.imm 0xffffffffffffffff)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .and (.reg .x14) (.reg .x15)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x24)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, tailW]
  · intro r h1 h2
    simp [getReg_setReg', h1, h2]
  · intro a; simp
theorem mac_pass {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (ws : List Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0xA0000)
    (hlen : ws.length = 16380)
    (hmem : ∀ i < 16380, (s.getMem (BitVec.ofNat 64 (0x80020 + 8 * i))).toNat = ws.getD i 0) :
    ∃ u, Steps image s 425894 622454 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunksOf ws)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hk : (s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61 < 2 ^ 61 := Nat.mod_lt _ (by norm_num)
  obtain ⟨u0, st0, pc0, k0, p0, a13, a14, r0, m0⟩ := head_steps hc s hpc B h22 hB hB' h18
  have hcl : CodeAt image (pc + 24) (macPassCode.drop 6) := codeAt_drop 6 hc (by decide)
  have hws : ∀ w ∈ ws, w < 2 ^ 64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have := hmem i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [← this]; exact BitVec.isLt _
  obtain ⟨u1, st1, pc1, b14, r1, m1⟩ := loop_steps hcl u0 pc0 0x80020 16380 _ ws (by norm_num) a13
    (by norm_num) (by norm_num) a14 k0 hk
    (by rw [r0 .x18 (by decide) (by decide) (by decide) (by decide), h18])
    (by rw [r0 .x19 (by decide) (by decide) (by decide) (by decide), h19]) hlen
    (fun i hi => by rw [m0]; exact hmem i hi)
  have hct : CodeAt image (pc + 24 + 104) (macPassCode.drop 32) := codeAt_drop 26 hcl (by decide)
  obtain ⟨u2, st2, pc2, c14, r2, m2⟩ := tail_steps hct u1 pc1
  obtain ⟨hlt, hmod⟩ := passAcc_spec _ hk ws hws
  refine ⟨u2, (st0.trans (st1.trans st2)).of_eq (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · rw [pc2]; bv_omega
  · rw [c14, b14, r1 .x18 (by decide) (by decide) (by decide) (by decide) (by decide),
      r0 .x18 (by decide) (by decide) (by decide) (by decide), h18,
      r1 .x24 (by decide) (by decide) (by decide) (by decide) (by decide), p0,
      tailW_ofNat _ hlt, hmod]
  · intro r h13 h14 h15 h16 h17 h23 h24
    rw [r2 r h14 h15, r1 r h13 h14 h15 h16 h17, r0 r h13 h14 h23 h24]
  · intro a; rw [m2, m1, m0]
end SigGolfCandidate.T3M.FullCache.MacPass
end
-- ==== merged from T3M_FullCache_MacRun ====
section

section
namespace SigGolfCandidate.T3M.FullCache.MacPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
theorem readWords_getD (t : MachineState) : ∀ (n a i : Nat), i < n →
    (t.readWords (BitVec.ofNat 64 a) n).getD i 0 = t.getMem (BitVec.ofNat 64 (a + 8 * i))
  | 0, _, _, h => by omega
  | n + 1, a, i, h => by
      have e : BitVec.ofNat 64 a + 8 = BitVec.ofNat 64 (a + 8) := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [MachineState.readWords_succ, e]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, readWords_getD t n (a + 8) i (by omega)]
        congr 2; omega
theorem chunksOf_of_wordsToNat : ∀ (n : Nat) (R : List Word) (l : List UInt8), R.length = n →
    l.length = 8 * n → wordsToNat R = T3.readLE l → chunksOf (R.map BitVec.toNat) = chunks32 l
  | 0, R, l, hR, hl, _ => by
      rw [List.length_eq_zero_iff.mp hR, List.length_eq_zero_iff.mp (by omega : l.length = 0)]
      rfl
  | n + 1, R, l, hR, hl, h => by
      obtain ⟨w, R', rfl⟩ : ∃ w R', R = w :: R' := by
        cases R with
        | nil => simp at hR
        | cons w R' => exact ⟨w, R', rfl⟩
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, l', rfl⟩ :
          ∃ b0 b1 b2 b3 b4 b5 b6 b7 l', l = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' := by
        match l, hl with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l', _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        | [], h => simp at h <;> omega
        | [_], h => simp at h <;> omega
        | [_, _], h => simp at h <;> omega
        | [_, _, _], h => simp at h <;> omega
        | [_, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _, _], h => simp at h <;> omega
      simp only [List.length_cons] at hR hl
      have hw := w.isLt
      have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
      have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
      simp only [wordsToNat, T3M.readLE_cons] at h
      have hsplit : w.toNat = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
          256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) ∧
          wordsToNat R' = T3.readLE l' := by
        constructor <;> omega
      have ih := chunksOf_of_wordsToNat n R' l' (by omega) (by omega) hsplit.2
      simp only [List.map_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append, chunks32]
      rw [show List.flatMap (fun w => [w % 2 ^ 32, w / 2 ^ 32]) (List.map BitVec.toNat R') =
        chunksOf (R'.map BitVec.toNat) from rfl, ih]
      congr 1
      · rw [hsplit.1]; omega
      · congr 1
        rw [hsplit.1]; omega
theorem mac_pass_region {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (region : List UInt8)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0xA0000)
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 0x80020) 16380) = T3.readLE region) :
    ∃ u, Steps image s 425894 622454 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunks32 region)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hR := readWords_length s (BitVec.ofNat 64 0x80020) 16380
  have hch := chunksOf_of_wordsToNat 16380 _ region hR (by rw [hlen]) hreg
  have := mac_pass hc s hpc B ((s.readWords (BitVec.ofNat 64 0x80020) 16380).map BitVec.toNat) h22 hB hB' h18
    h19 (by rw [List.length_map, hR]) (fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, ← readWords_getD s 16380 0x80020 i hi,
        List.getD_eq_getElem?_getD]
      cases h : (s.readWords (BitVec.ofNat 64 0x80020) 16380)[i]? with
      | none =>
        exfalso
        rw [List.getElem?_eq_none_iff, hR] at h
        omega
      | some w => rfl)
  rwa [hch] at this
end SigGolfCandidate.T3M.FullCache.MacPass
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 20000
abbrev PRIV : Nat := 0x20000
abbrev KEYS : Nat := 0x70000
abbrev REGION : Nat := 0x80020
abbrev REGIONEND : Nat := 0xA0000
def macImage (sg : Bool) : Image := if sg then Images.signReferenceImage else Images.keygenImage
def macBase (sg : Bool) : Nat := if sg then 1227 else 334
def macOut (sg : Bool) : Nat := if sg then 0x203E0 else 0x80000
def macSeg_0 : List (BitVec 32) := [134711,921107,3767,0x80e8e93,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,0xe0130313,7223331,932899,132407,328979,67110291,460343,394771]
theorem macAt_0 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 0)) (macSeg_0) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 334)
      (post := Images.keygenCode.drop 357) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1227) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_0 := symRun { noAlias := true } (macSeg_0) (pcOf 334) 100
sym_block macBlkS_0 := symRun { noAlias := true } (macSeg_0) (pcOf 1227) 100
def macSeg_23 : List (BitVec 32) := [115]
theorem macAt_23 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 23)) (macSeg_23) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 357)
      (post := Images.keygenCode.drop 358) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1250) (by decide +kernel) (by decide +kernel)
def macSeg_24 : List (BitVec 32) := [1049363,33755923,7224355,460343,33949203]
theorem macAt_24 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 24)) (macSeg_24) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 358)
      (post := Images.keygenCode.drop 363) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1251) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_24 := symRun { noAlias := true } (macSeg_24) (pcOf 358) 100
sym_block macBlkS_24 := symRun { noAlias := true } (macSeg_24) (pcOf 1251) 100
def macSeg_29 : List (BitVec 32) := [115]
theorem macAt_29 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 29)) (macSeg_29) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 363)
      (post := Images.keygenCode.drop 364) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1256) (by decide +kernel) (by decide +kernel)
def macSeg_30 (sg : Bool) : List (BitVec 32) := if sg then [0xfff00913, 0x00395913, 0x000a09b7, 0x00098993, 0x00070b37, 0x000b0b13, 0x00020cb7, 0x3e0c8c93] else [0xfff00913, 0x00395913, 0x000a09b7, 0x00098993, 0x00070b37, 0x000b0b13, 0x00080cb7, 0x000c8c93]
theorem macAt_30 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 30)) (macSeg_30 sg) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 364)
      (post := Images.keygenCode.drop 372) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1257) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_30 := symRun { noAlias := true } (macSeg_30 false) (pcOf 364) 100
sym_block macBlkS_30 := symRun { noAlias := true } (macSeg_30 true) (pcOf 1257) 100
def macSeg_38 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_38_pass : macSeg_38 = MacPass.macPassCode := by decide +kernel
theorem macAt_38 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 38)) (macSeg_38) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 372)
      (post := Images.keygenCode.drop 412) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1265) (by decide +kernel) (by decide +kernel)
def macSeg_78 : List (BitVec 32) := [0xecb023,17500947]
theorem macAt_78 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 78)) (macSeg_78) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 412)
      (post := Images.keygenCode.drop 414) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1305) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_78 := symRun { noAlias := true } (macSeg_78) (pcOf 412) 100
sym_block macBlkS_78 := symRun { noAlias := true } (macSeg_78) (pcOf 1305) 100
def macSeg_80 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_80_pass : macSeg_80 = MacPass.macPassCode := by decide +kernel
theorem macAt_80 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 80)) (macSeg_80) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 414)
      (post := Images.keygenCode.drop 454) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1307) (by decide +kernel) (by decide +kernel)
def macSeg_120 : List (BitVec 32) := [0xecb423,17500947]
theorem macAt_120 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 120)) (macSeg_120) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 454)
      (post := Images.keygenCode.drop 456) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1347) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_120 := symRun { noAlias := true } (macSeg_120) (pcOf 454) 100
sym_block macBlkS_120 := symRun { noAlias := true } (macSeg_120) (pcOf 1347) 100
def macSeg_122 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_122_pass : macSeg_122 = MacPass.macPassCode := by decide +kernel
theorem macAt_122 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 122)) (macSeg_122) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 456)
      (post := Images.keygenCode.drop 496) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1349) (by decide +kernel) (by decide +kernel)
def macSeg_162 : List (BitVec 32) := [0xecb823,17500947]
theorem macAt_162 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 162)) (macSeg_162) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 496)
      (post := Images.keygenCode.drop 498) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1389) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_162 := symRun { noAlias := true } (macSeg_162) (pcOf 496) 100
sym_block macBlkS_162 := symRun { noAlias := true } (macSeg_162) (pcOf 1389) 100
def macSeg_164 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_164_pass : macSeg_164 = MacPass.macPassCode := by decide +kernel
theorem macAt_164 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 164)) (macSeg_164) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 498)
      (post := Images.keygenCode.drop 538) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1391) (by decide +kernel) (by decide +kernel)
def macSeg_204 : List (BitVec 32) := [0xecbc23]
theorem macAt_204 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 204)) (macSeg_204) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 538)
      (post := Images.keygenCode.drop 539) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1431) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_204 := symRun { noAlias := true } (macSeg_204) (pcOf 538) 100
sym_block macBlkS_204 := symRun { noAlias := true } (macSeg_204) (pcOf 1431) 100
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem mac_init (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg)) :
    ∃ t, Steps (macImage sg) s 23 23 t ∧ t.pc = pcOf (macBase sg + 23) ∧
      t.getReg .x28 = BitVec.ofNat 64 PRIV ∧ t.getReg .x10 = BitVec.ofNat 64 PRIV ∧
      t.getReg .x11 = 64 ∧ t.getReg .x12 = BitVec.ofNat 64 KEYS ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem 0x80 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+8)) = s.getMem 0x88 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+32)) = s.getMem 0x90 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+40)) = s.getMem 0x98 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 ∧
      RegsExcept s t [.x6,.x10,.x11,.x12,.x28,.x29] ∧
      Frame s t (fun A => PRIV ≤ A ∧ A < PRIV+64) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_0 (macAt_0 false) s hpc (by simp [macBlkK_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_0 (macAt_0 true) s hpc (by simp [macBlkS_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
theorem mac_next (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+24))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 PRIV) :
    ∃ t, Steps (macImage sg) s 5 5 t ∧ t.pc = pcOf (macBase sg+29) ∧
      t.getReg .x12 = BitVec.ofNat 64 (KEYS+32) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32) ∧
      RegsExcept s t [.x6,.x12] ∧ Frame s t (fun A => A = PRIV+24) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_24 (macAt_24 false) s hpc
      (by simp only [macBlkK_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkK_24.res, macBase, rv_simp]
    · simp [macBlkK_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkK_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_24 (macAt_24 true) s hpc
      (by simp only [macBlkS_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkS_24.res, macBase, rv_simp]
    · simp [macBlkS_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkS_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
theorem mac_lanes_init (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+30)) :
    ∃ t, Steps (macImage sg) s 8 8 t ∧ t.pc = pcOf (macBase sg+38) ∧
      t.getReg .x18 = BitVec.ofNat 64 (2^61-1) ∧
      t.getReg .x19 = BitVec.ofNat 64 REGIONEND ∧
      t.getReg .x22 = BitVec.ofNat 64 KEYS ∧ t.getReg .x25 = BitVec.ofNat 64 (macOut sg) ∧
      RegsExcept s t [.x18,.x19,.x22,.x25] ∧ Frame s t (fun _ => False) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_30 (macAt_30 false) s hpc
      (by simp [macBlkK_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkK_30.res, rv_simp]
  · refine ⟨_, symRun_sound macBlkS_30 (macAt_30 true) s hpc
      (by simp [macBlkS_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkS_30.res, rv_simp]
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def laneEnd (j : Fin 4) : Nat := if j.val < 3 then 80+42*j.val else 205
theorem mac_pass_at (sg : Bool) (j : Fin 4) :
    CodeAt (macImage sg) (pcOf (macBase sg+38+42*j.val)) MacPass.macPassCode := by
  fin_cases j
  · have h := macAt_38 sg
    rw [macSeg_38_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_80 sg
    rw [macSeg_80_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_122 sg
    rw [macSeg_122_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_164 sg
    rw [macSeg_164_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
theorem mac_store (sg : Bool) (j : Fin 4) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg+78+42*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg)) :
    ∃ t, Steps (macImage sg) s (if j.val < 3 then 2 else 1) (if j.val < 3 then 2 else 1) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = s.getReg .x14 ∧
      t.getReg .x22 = (if j.val < 3 then s.getReg .x22+16 else s.getReg .x22) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  cases sg
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkK_78 (macAt_78 false) s hpc
        (by simp only [macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_120 (macAt_120 false) s hpc
        (by simp only [macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_162 (macAt_162 false) s hpc
        (by simp only [macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_204 (macAt_204 false) s hpc
        (by simp only [macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkS_78 (macAt_78 true) s hpc
        (by simp only [macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_120 (macAt_120 true) s hpc
        (by simp only [macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_162 (macAt_162 true) s hpc
        (by simp only [macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_204 (macAt_204 true) s hpc
        (by simp only [macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
end SigGolfCandidate.T3M.FullCache
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
set_option maxRecDepth 20000
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
def laneWord (s : MachineState) (j : Fin 4) (region : List UInt8) : Word :=
  BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 (KEYS+16*j.val))).toNat % 2^61) (chunks32 region)) +
    s.getMem (BitVec.ofNat 64 (KEYS+16*j.val+8))
def laneRegs : List Reg := [.x13,.x14,.x15,.x16,.x17,.x22,.x23,.x24]
theorem one_lane (sg : Bool) (j : Fin 4) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+38+42*j.val))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2^61-1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 REGIONEND)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (KEYS+16*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg))
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps (macImage sg) s (425894+(if j.val<3 then 2 else 1))
        (622454+(if j.val<3 then 2 else 1)) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region ∧
      t.getReg .x22 = (if j.val<3 then BitVec.ofNat 64 (KEYS+16*(j.val+1)) else s.getReg .x22) ∧
      RegsExcept s t laneRegs ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  have hj := j.isLt
  obtain ⟨u,hu,upc,u14,ur,um⟩ := MacPass.mac_pass_region (mac_pass_at sg j) s hpc
    (KEYS+16*j.val) region h22 (by simp [KEYS]; omega) (by simp [KEYS]; omega)
    h18 h19 hlen hreg
  have upc' : u.pc = pcOf (macBase sg+78+42*j.val) := by
    rw [upc]; unfold pcOf
    change BitVec.ofNat 64 (4096+4*(macBase sg+38+42*j.val)) + BitVec.ofNat 64 160 = _
    rw [ofNat_add_ofNat]; exact congrArg (BitVec.ofNat 64) (by omega)
  have ur25 : u.getReg .x25 = BitVec.ofNat 64 (macOut sg) := by
    rw [ur .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h25]
  obtain ⟨t,ht,tpc,tm,t22,tr,tf⟩ := mac_store sg j u upc' ur25
  refine ⟨t,hu.trans ht,tpc,?_,?_,?_,?_⟩
  · rw [tm,u14]; rfl
  · rw [t22,ur .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    split_ifs
    · rw [h22]
      change BitVec.ofNat 64 (KEYS+16*j.val) + BitVec.ofNat 64 16 = _
      rw [ofNat_add_ofNat]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rfl
  · intro r hr
    have hr' : r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by simpa [laneRegs] using hr
    rw [tr.get (by simpa using hr'.2.2.2.2.2.1)]
    exact ur r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1 hr'.2.2.2.2.2.2.1 hr'.2.2.2.2.2.2.2
  · intro A hA hn; rw [tf.get hA hn,um]
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
set_option maxRecDepth 20000
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def OutW (sg : Bool) (A : Nat) : Prop := macOut sg ≤ A ∧ A < macOut sg+32
theorem lane_frame_out {s t : MachineState} {sg : Bool} {j : Fin 4}
    (h : Frame s t (fun A => A = macOut sg+8*j.val)) : Frame s t (OutW sg) :=
  h.mono (fun A _ ha => by subst A; have := j.isLt; unfold OutW; omega)
theorem out_region {s t : MachineState} {sg : Bool} (h : Frame s t (OutW sg)) :
    t.readWords (BitVec.ofNat 64 REGION) 16380 = s.readWords (BitVec.ofNat 64 REGION) 16380 := by
  apply frame_readWords h REGION 16380 (by decide)
  intro i hi
  cases sg <;> simp only [OutW, macOut, REGION, Bool.false_eq_true, if_false, if_true] <;> omega
theorem out_laneWord {s t : MachineState} {sg : Bool} (h : Frame s t (OutW sg))
    (j : Fin 4) (region : List UInt8) : laneWord t j region = laneWord s j region := by
  have hj := j.isLt
  unfold laneWord
  rw [h.get (by simp [KEYS]; omega) (by cases sg <;> simp [OutW,macOut,KEYS] <;> omega),
    h.get (by simp [KEYS]; omega) (by cases sg <;> simp [OutW,macOut,KEYS] <;> omega)]
theorem mac_pure (sg : Bool) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+30)) (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps (macImage sg) s 1703591 2489831 t ∧ t.pc = pcOf (macBase sg+205) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region) ∧
      t.getReg .x5 = s.getReg .x5 ∧ Frame s t (OutW sg) := by
  obtain ⟨u0,st0,pc0,m18,m19,m22,m25,r0,f0⟩ := mac_lanes_init sg s hpc
  have F0 : Frame s u0 (OutW sg) := f0.mono (fun _ _ h => h.elim)
  obtain ⟨u1,st1,pc1,word1,next1,r1,f1⟩ := one_lane sg 0 u0 region
    (by simpa using pc0) m18 m19 (by simpa using m22) m25 hlen (by rw [out_region F0]; exact hreg)
  have F1 : Frame s u1 (OutW sg) :=
    (F0.trans (lane_frame_out f1)).mono (fun _ _ h => h.elim id id)
  have W1 : u1.getMem (BitVec.ofNat 64 (macOut sg+8*(0 : Fin 4).val)) = laneWord s 0 region :=
    word1.trans (out_laneWord F0 0 region)
  obtain ⟨u2,st2,pc2,word2,next2,r2,f2⟩ := one_lane sg 1 u1 region
    (by simpa [laneEnd,Nat.add_assoc] using pc1)
    (by rw [r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next1)
    (by rw [r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F1]; exact hreg)
  have F2 : Frame s u2 (OutW sg) :=
    (F1.trans (lane_frame_out f2)).mono (fun _ _ h => h.elim id id)
  have W2 : u2.getMem (BitVec.ofNat 64 (macOut sg+8*(1 : Fin 4).val)) = laneWord s 1 region :=
    word2.trans (out_laneWord F1 1 region)
  obtain ⟨u3,st3,pc3,word3,next3,r3,f3⟩ := one_lane sg 2 u2 region
    (by simpa [laneEnd,Nat.add_assoc] using pc2)
    (by rw [r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next2)
    (by rw [r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F2]; exact hreg)
  have F3 : Frame s u3 (OutW sg) :=
    (F2.trans (lane_frame_out f3)).mono (fun _ _ h => h.elim id id)
  have W3 : u3.getMem (BitVec.ofNat 64 (macOut sg+8*(2 : Fin 4).val)) = laneWord s 2 region :=
    word3.trans (out_laneWord F2 2 region)
  obtain ⟨u4,st4,pc4,word4,next4,r4,f4⟩ := one_lane sg 3 u3 region
    (by simpa [laneEnd,Nat.add_assoc] using pc3)
    (by rw [r3.get (by decide : Reg.x18 ∉ laneRegs),r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r3.get (by decide : Reg.x19 ∉ laneRegs),r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next3)
    (by rw [r3.get (by decide : Reg.x25 ∉ laneRegs),r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F3]; exact hreg)
  have F4 : Frame s u4 (OutW sg) :=
    (F3.trans (lane_frame_out f4)).mono (fun _ _ h => h.elim id id)
  have W4 : u4.getMem (BitVec.ofNat 64 (macOut sg+8*(3 : Fin 4).val)) = laneWord s 3 region :=
    word4.trans (out_laneWord F3 3 region)
  refine ⟨u4,(st0.trans (st1.trans (st2.trans (st3.trans st4)))).of_eq (by decide) (by decide),
    ?_,?_,?_,F4⟩
  · simpa [laneEnd] using pc4
  · intro j; fin_cases j
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega),f2.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W1
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W2
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W3
    · exact W4
  · rw [r4.get (by decide : Reg.x5 ∉ laneRegs),r3.get (by decide : Reg.x5 ∉ laneRegs),r2.get (by decide : Reg.x5 ∉ laneRegs),r1.get (by decide : Reg.x5 ∉ laneRegs),r0.get (by decide)]
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity
open SiggolfT3Mac4
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
def KeysAt (s : MachineState) (a b : BitVec 256) : Prop :=
  ∀ j : Fin 8, s.getMem (BitVec.ofNat 64 (KEYS+8*j.val)) =
    if j.val < 4 then a.extractLsb' (64*j.val) 64 else b.extractLsb' (64*(j.val-4)) 64
def keyPair (a b : BitVec 256) : MacKey := fun i => if i = 0 then a else b
theorem extract64_mod61 (a : BitVec 256) (off : Nat) :
    (a.extractLsb' off 64).toNat % 2^61 = (a.extractLsb' off 61).toNat := by
  simp only [BitVec.extractLsb'_toNat]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem laneWord_eq_tag (s : MachineState) (a b : BitVec 256) (region : List UInt8)
    (hk : KeysAt s a b) (j : Fin 4) : laneWord s j region = macTag (keyPair a b) region j := by
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3
  have h4 := hk 4; have h5 := hk 5; have h6 := hk 6; have h7 := hk 7
  change s.getMem 458752#64 = a.extractLsb' 0 64 at h0
  change s.getMem 458760#64 = a.extractLsb' 64 64 at h1
  change s.getMem 458768#64 = a.extractLsb' 128 64 at h2
  change s.getMem 458776#64 = a.extractLsb' 192 64 at h3
  change s.getMem 458784#64 = b.extractLsb' 0 64 at h4
  change s.getMem 458792#64 = b.extractLsb' 64 64 at h5
  change s.getMem 458800#64 = b.extractLsb' 128 64 at h6
  change s.getMem 458808#64 = b.extractLsb' 192 64 at h7
  fin_cases j <;>
    simp [laneWord, macTag, macKeyWord, macPadWord, keyPair, KEYS, h0,h1,h2,h3,h4,h5,h6,h7,
      extract64_mod61]
theorem encodeTag_word (tag : MacTag) (j : Fin 4) :
    (encodeTag tag).extractLsb' (64*j.val) 64 = tag j := by
  obtain ⟨h0,h1,h2,h3⟩ := extract_answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)
  fin_cases j <;> simp only [encodeTag] <;> assumption
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open OracleComp OracleSpec
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def SkAt (s : MachineState) (sk : BitVec 256) : Prop :=
  ∀ j : Fin 4, s.getMem (BitVec.ofNat 64 (0x80+8*j.val)) = sk.extractLsb' (64*j.val) 64
def PrivAt (s : MachineState) (sk : BitVec 256) (i : Fin 2) : Prop :=
  ∀ j : Fin 8, s.getMem (BitVec.ofNat 64 (PRIV+8*j.val)) =
    [sk.extractLsb' 0 64,sk.extractLsb' 64 64,3585,BitVec.ofNat 64 (i.val*2^32),
      sk.extractLsb' 128 64,sk.extractLsb' 192 64,0,0].getD j.val 0
theorem priv_query (s : MachineState) (sk : BitVec 256) (i : Fin 2) (h : PrivAt s sk i)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h11 : s.getReg .x11 = 64) :
    hashInput s = toQ (T3.privateInput sk (.inl (T3.header 14 0 0 0 i.val))) := by
  apply hashInput_toQ s _ 0 PRIV (privateInput_tweak_length _ _) h10 (by decide) (by decide)
    h11 (by decide)
  rw [readWords_eight,wordsOf_privateInput_tweak]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  change s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64 at h0
  change s.getMem (BitVec.ofNat 64 (PRIV+8)) = sk.extractLsb' 64 64 at h1
  change s.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 at h2
  change s.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (i.val*2^32) at h3
  change s.getMem (BitVec.ofNat 64 (PRIV+32)) = sk.extractLsb' 128 64 at h4
  change s.getMem (BitVec.ofNat 64 (PRIV+40)) = sk.extractLsb' 192 64 at h5
  change s.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 at h6
  change s.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 at h7
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  fin_cases i <;> rfl
theorem priv_next {s t : MachineState} {sk : BitVec 256} {a : BitVec 256}
    (hp : PrivAt s sk 0) (h12 : s.getReg .x12 = BitVec.ofNat 64 KEYS)
    (hfr : Frame (writeHash s a) t (fun A => A = PRIV+24))
    (h24 : t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32)) : PrivAt t sk 1 := by
  intro j
  have hf := Frame.writeHash s a KEYS h12 (by decide)
  have hj := j.isLt
  by_cases he : j.val = 3
  · have ej : j = 3 := Fin.ext he
    subst j
    exact h24
  · rw [hfr.get (by simp [PRIV]; omega) (by simp [PRIV]; omega),
      hf.get (by simp [PRIV]; omega) (by simp [PRIV,KEYS]; omega),hp j]
    fin_cases j <;> first | rfl | exact False.elim (he rfl)
theorem keys_after {s t : MachineState} (a b : BitVec 256)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 KEYS)
    (hfr : Frame (writeHash s a) t (fun A => A = PRIV+24))
    (ht12 : t.getReg .x12 = BitVec.ofNat 64 (KEYS+32)) : KeysAt (writeHash t b) a b := by
  intro j
  have hj := j.isLt
  have hA : KEYS+8*j.val < 2^64 := by simp [KEYS]; omega
  rw [getMem_writeHash t b (KEYS+32) (KEYS+8*j.val) ht12 (by decide) hA]
  fin_cases j
  all_goals simp only [KEYS, Nat.reduceMul, Nat.reduceAdd, Fin.val_zero, Fin.val_one, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one, Nat.reduceEqDiff, if_true, if_false, Nat.reduceLT, Nat.reduceSub]
  all_goals first
    | rfl
    | (rw [hfr.get (by decide) (by decide), getMem_writeHash s a KEYS _ h12 (by decide) (by decide)]
       simp [KEYS])
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open OracleComp OracleSpec
open SphincsSecurity (bytesLE)
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def MacW (sg : Bool) (A : Nat) : Prop :=
  (PRIV ≤ A ∧ A < PRIV+64) ∨ (KEYS ≤ A ∧ A < KEYS+64) ∨ OutW sg A
structure MacDone (sg : Bool) (s : MachineState) (tag : T3.HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf (macBase sg+205)
  x5 : t.getReg .x5 = 0
  words : t.readWords (BitVec.ofNat 64 (macOut sg)) 4 = wordsOf (bytesLE 32 tag)
  frame : Frame s t (MacW sg)
theorem mac_tsim (sg : Bool) (sk : BitVec 256) (region : T3.Region) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg)) (h5 : s.getReg .x5 = 0) (hsk : SkAt s sk)
    (hreg : s.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region)) :
    TSim (macImage sg) sk s 1703621 2489875 2 2 (T3.privateMac region) (MacDone sg s) := by
  obtain ⟨u0,st0,pc0,x28,x10,x11,x12,m0,m8,m16,m24,m32,m40,m48,m56,r0,f0⟩ := mac_init sg s hpc
  have p0 : PrivAt u0 sk 0 := by
    intro j; fin_cases j
    · exact m0.trans (hsk 0)
    · exact m8.trans (hsk 1)
    · exact m16
    · exact m24
    · exact m32.trans (hsk 2)
    · exact m40.trans (hsk 3)
    · exact m48
    · exact m56
  have z0 : u0.getReg .x5 = 0 := by rw [r0.get (by decide),h5]
  have v0 : hashArgumentsValid u0 = true := hashArgs_const u0 PRIV 64 KEYS x10 x11 x12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q0 := priv_query u0 sk 0 p0 x10 x11
  have fetch0 : fetch (macImage sg) u0 = some (.base .ECALL) := (macAt_23 sg).fetch u0 pc0 |>.trans rfl
  unfold T3.privateMac T3.privateMacKey
  simp only [bind_assoc,pure_bind]
  refine (TSim.steps st0 (TSim.privateTweak_bind (k := 1703597) (c := 2489844) (n := 1) (b := 1) fetch0 z0 v0 q0 (fun a => ?_))).of_eq
    rfl (by decide) (by decide) (by decide) (by decide)
  have pa : (writeHash u0 a).pc = pcOf (macBase sg+24) := by
    rw [pc_writeHash,pc0,pcOf_add4]
  obtain ⟨u1,st1,pc1,y12,n24,r1,f1⟩ := mac_next sg (writeHash u0 a) pa (by simpa using x28)
  have p1 := priv_next p0 x12 f1 n24
  have y10 : u1.getReg .x10 = BitVec.ofNat 64 PRIV := by rw [r1.get (by decide),getReg_writeHash,x10]
  have y11 : u1.getReg .x11 = 64 := by rw [r1.get (by decide),getReg_writeHash,x11]
  have z1 : u1.getReg .x5 = 0 := by rw [r1.get (by decide),getReg_writeHash,z0]
  have v1 : hashArgumentsValid u1 = true := hashArgs_const u1 PRIV 64 (KEYS+32) y10 y11 y12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q1 := priv_query u1 sk 1 p1 y10 y11
  have fetch1 : fetch (macImage sg) u1 = some (.base .ECALL) := (macAt_29 sg).fetch u1 pc1 |>.trans rfl
  refine TSim.steps st1 (TSim.privateTweak_bind (k := 1703591) (c := 2489831) (n := 0) (b := 0) fetch1 z1 v1 q1 (fun b => ?_))
  have F0 : Frame s (writeHash u1 b) (MacW sg) := by
    have ha := Frame.writeHash u0 a KEYS x12 (by decide)
    have hb := Frame.writeHash u1 b (KEYS+32) y12 (by decide)
    apply (((f0.trans ha).trans f1).trans hb).mono
    intro A hA h
    unfold MacW
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · left; subst A; simp [PRIV]
    · exact Or.inr (Or.inl (by omega))
  have preg : (writeHash u1 b).readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region) := by
    rw [frame_readWords F0 REGION 16380 (by decide) (by
      intro i hi; cases sg <;> simp only [MacW,OutW,macOut,PRIV,KEYS,REGION,Bool.false_eq_true,if_false,if_true] <;> omega)]
    exact hreg
  have pb : (writeHash u1 b).pc = pcOf (macBase sg+30) := by
    rw [pc_writeHash,pc1,pcOf_add4]
  obtain ⟨t,st,pc,tagwords,zt,ft⟩ := mac_pure sg (writeHash u1 b) (List.ofFn region) pb
    (by rw [List.length_ofFn]) (by rw [preg,wordsToNat_wordsOf 16380 _ (by rw [List.length_ofFn])])
  have hk := keys_after a b x12 f1 y12
  refine TSim.pure_steps st ?_
  refine ⟨pc,?_,?_,?_⟩
  · rw [zt,getReg_writeHash,z1]
  · rw [show (4 : Nat) = 2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32]
    have H : ∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) =
        (SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag (keyPair a b) (List.ofFn region))).extractLsb' (64*j.val) 64 := by
      intro j
      rw [tagwords j,laneWord_eq_tag _ _ _ _ hk j,encodeTag_word]
    change [t.getMem (BitVec.ofNat 64 (macOut sg+8*(0:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(1:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(2:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(3:Fin 4).val))] = _
    rw [H 0,H 1,H 2,H 3]
    rfl
  · exact (F0.trans ft).mono (fun A hA h => h.elim id (fun h => Or.inr (Or.inr h)))
end SigGolfCandidate.T3M.FullCache
end

namespace SigGolfCandidate.T3M.FullCache.Generic
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity SiggolfT3Mac4 OracleComp OracleSpec
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
structure MacCodeAt (image : Image) (sg : Bool) : Prop where
  seg0 : CodeAt image (pcOf (macBase sg + 0)) (macSeg_0)
  seg23 : CodeAt image (pcOf (macBase sg + 23)) (macSeg_23)
  seg24 : CodeAt image (pcOf (macBase sg + 24)) (macSeg_24)
  seg29 : CodeAt image (pcOf (macBase sg + 29)) (macSeg_29)
  seg30 : CodeAt image (pcOf (macBase sg + 30)) (macSeg_30 sg)
  seg38 : CodeAt image (pcOf (macBase sg + 38)) (macSeg_38)
  seg78 : CodeAt image (pcOf (macBase sg + 78)) (macSeg_78)
  seg80 : CodeAt image (pcOf (macBase sg + 80)) (macSeg_80)
  seg120 : CodeAt image (pcOf (macBase sg + 120)) (macSeg_120)
  seg122 : CodeAt image (pcOf (macBase sg + 122)) (macSeg_122)
  seg162 : CodeAt image (pcOf (macBase sg + 162)) (macSeg_162)
  seg164 : CodeAt image (pcOf (macBase sg + 164)) (macSeg_164)
  seg204 : CodeAt image (pcOf (macBase sg + 204)) (macSeg_204)
theorem mac_init (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (s : MachineState) (hpc : s.pc = pcOf (macBase sg)) :
    ∃ t, Steps image s 23 23 t ∧ t.pc = pcOf (macBase sg + 23) ∧
      t.getReg .x28 = BitVec.ofNat 64 PRIV ∧ t.getReg .x10 = BitVec.ofNat 64 PRIV ∧
      t.getReg .x11 = 64 ∧ t.getReg .x12 = BitVec.ofNat 64 KEYS ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem 0x80 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+8)) = s.getMem 0x88 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+32)) = s.getMem 0x90 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+40)) = s.getMem 0x98 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 ∧
      RegsExcept s t [.x6,.x10,.x11,.x12,.x28,.x29] ∧
      Frame s t (fun A => PRIV ≤ A ∧ A < PRIV+64) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_0 (hc.seg0) s hpc (by simp [macBlkK_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_0 (hc.seg0) s hpc (by simp [macBlkS_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
theorem mac_next (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+24))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 PRIV) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf (macBase sg+29) ∧
      t.getReg .x12 = BitVec.ofNat 64 (KEYS+32) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32) ∧
      RegsExcept s t [.x6,.x12] ∧ Frame s t (fun A => A = PRIV+24) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_24 (hc.seg24) s hpc
      (by simp only [macBlkK_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkK_24.res, macBase, rv_simp]
    · simp [macBlkK_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkK_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_24 (hc.seg24) s hpc
      (by simp only [macBlkS_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkS_24.res, macBase, rv_simp]
    · simp [macBlkS_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkS_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
theorem mac_lanes_init (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+30)) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf (macBase sg+38) ∧
      t.getReg .x18 = BitVec.ofNat 64 (2^61-1) ∧
      t.getReg .x19 = BitVec.ofNat 64 REGIONEND ∧
      t.getReg .x22 = BitVec.ofNat 64 KEYS ∧ t.getReg .x25 = BitVec.ofNat 64 (macOut sg) ∧
      RegsExcept s t [.x18,.x19,.x22,.x25] ∧ Frame s t (fun _ => False) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_30 (hc.seg30) s hpc
      (by simp [macBlkK_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkK_30.res, rv_simp]
  · refine ⟨_, symRun_sound macBlkS_30 (hc.seg30) s hpc
      (by simp [macBlkS_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkS_30.res, rv_simp]
theorem mac_pass_at (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (j : Fin 4) :
    CodeAt image (pcOf (macBase sg+38+42*j.val)) MacPass.macPassCode := by
  fin_cases j
  · have h := hc.seg38
    rw [macSeg_38_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := hc.seg80
    rw [macSeg_80_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := hc.seg122
    rw [macSeg_122_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := hc.seg164
    rw [macSeg_164_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
theorem mac_store (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (j : Fin 4) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg+78+42*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg)) :
    ∃ t, Steps image s (if j.val < 3 then 2 else 1) (if j.val < 3 then 2 else 1) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = s.getReg .x14 ∧
      t.getReg .x22 = (if j.val < 3 then s.getReg .x22+16 else s.getReg .x22) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  cases sg
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkK_78 (hc.seg78) s hpc
        (by simp only [macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_120 (hc.seg120) s hpc
        (by simp only [macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_162 (hc.seg162) s hpc
        (by simp only [macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_204 (hc.seg204) s hpc
        (by simp only [macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkS_78 (hc.seg78) s hpc
        (by simp only [macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_120 (hc.seg120) s hpc
        (by simp only [macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_162 (hc.seg162) s hpc
        (by simp only [macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_204 (hc.seg204) s hpc
        (by simp only [macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
theorem one_lane (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (j : Fin 4) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+38+42*j.val))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2^61-1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 REGIONEND)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (KEYS+16*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg))
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps image s (425894+(if j.val<3 then 2 else 1))
        (622454+(if j.val<3 then 2 else 1)) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region ∧
      t.getReg .x22 = (if j.val<3 then BitVec.ofNat 64 (KEYS+16*(j.val+1)) else s.getReg .x22) ∧
      RegsExcept s t laneRegs ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  have hj := j.isLt
  obtain ⟨u,hu,upc,u14,ur,um⟩ := MacPass.mac_pass_region (mac_pass_at sg image hc j) s hpc
    (KEYS+16*j.val) region h22 (by simp [KEYS]; omega) (by simp [KEYS]; omega)
    h18 h19 hlen hreg
  have upc' : u.pc = pcOf (macBase sg+78+42*j.val) := by
    rw [upc]; unfold pcOf
    change BitVec.ofNat 64 (4096+4*(macBase sg+38+42*j.val)) + BitVec.ofNat 64 160 = _
    rw [ofNat_add_ofNat]; exact congrArg (BitVec.ofNat 64) (by omega)
  have ur25 : u.getReg .x25 = BitVec.ofNat 64 (macOut sg) := by
    rw [ur .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h25]
  obtain ⟨t,ht,tpc,tm,t22,tr,tf⟩ := mac_store sg image hc j u upc' ur25
  refine ⟨t,hu.trans ht,tpc,?_,?_,?_,?_⟩
  · rw [tm,u14]; rfl
  · rw [t22,ur .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    split_ifs
    · rw [h22]
      change BitVec.ofNat 64 (KEYS+16*j.val) + BitVec.ofNat 64 16 = _
      rw [ofNat_add_ofNat]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rfl
  · intro r hr
    have hr' : r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by simpa [laneRegs] using hr
    rw [tr.get (by simpa using hr'.2.2.2.2.2.1)]
    exact ur r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1 hr'.2.2.2.2.2.2.1 hr'.2.2.2.2.2.2.2
  · intro A hA hn; rw [tf.get hA hn,um]
theorem mac_pure (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+30)) (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps image s 1703591 2489831 t ∧ t.pc = pcOf (macBase sg+205) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region) ∧
      t.getReg .x5 = s.getReg .x5 ∧ Frame s t (OutW sg) := by
  obtain ⟨u0,st0,pc0,m18,m19,m22,m25,r0,f0⟩ := mac_lanes_init sg image hc s hpc
  have F0 : Frame s u0 (OutW sg) := f0.mono (fun _ _ h => h.elim)
  obtain ⟨u1,st1,pc1,word1,next1,r1,f1⟩ := one_lane sg image hc 0 u0 region
    (by simpa using pc0) m18 m19 (by simpa using m22) m25 hlen (by rw [out_region F0]; exact hreg)
  have F1 : Frame s u1 (OutW sg) :=
    (F0.trans (lane_frame_out f1)).mono (fun _ _ h => h.elim id id)
  have W1 : u1.getMem (BitVec.ofNat 64 (macOut sg+8*(0 : Fin 4).val)) = laneWord s 0 region :=
    word1.trans (out_laneWord F0 0 region)
  obtain ⟨u2,st2,pc2,word2,next2,r2,f2⟩ := one_lane sg image hc 1 u1 region
    (by simpa [laneEnd,Nat.add_assoc] using pc1)
    (by rw [r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next1)
    (by rw [r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F1]; exact hreg)
  have F2 : Frame s u2 (OutW sg) :=
    (F1.trans (lane_frame_out f2)).mono (fun _ _ h => h.elim id id)
  have W2 : u2.getMem (BitVec.ofNat 64 (macOut sg+8*(1 : Fin 4).val)) = laneWord s 1 region :=
    word2.trans (out_laneWord F1 1 region)
  obtain ⟨u3,st3,pc3,word3,next3,r3,f3⟩ := one_lane sg image hc 2 u2 region
    (by simpa [laneEnd,Nat.add_assoc] using pc2)
    (by rw [r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next2)
    (by rw [r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F2]; exact hreg)
  have F3 : Frame s u3 (OutW sg) :=
    (F2.trans (lane_frame_out f3)).mono (fun _ _ h => h.elim id id)
  have W3 : u3.getMem (BitVec.ofNat 64 (macOut sg+8*(2 : Fin 4).val)) = laneWord s 2 region :=
    word3.trans (out_laneWord F2 2 region)
  obtain ⟨u4,st4,pc4,word4,next4,r4,f4⟩ := one_lane sg image hc 3 u3 region
    (by simpa [laneEnd,Nat.add_assoc] using pc3)
    (by rw [r3.get (by decide : Reg.x18 ∉ laneRegs),r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r3.get (by decide : Reg.x19 ∉ laneRegs),r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next3)
    (by rw [r3.get (by decide : Reg.x25 ∉ laneRegs),r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F3]; exact hreg)
  have F4 : Frame s u4 (OutW sg) :=
    (F3.trans (lane_frame_out f4)).mono (fun _ _ h => h.elim id id)
  have W4 : u4.getMem (BitVec.ofNat 64 (macOut sg+8*(3 : Fin 4).val)) = laneWord s 3 region :=
    word4.trans (out_laneWord F3 3 region)
  refine ⟨u4,(st0.trans (st1.trans (st2.trans (st3.trans st4)))).of_eq (by decide) (by decide),
    ?_,?_,?_,F4⟩
  · simpa [laneEnd] using pc4
  · intro j; fin_cases j
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega),f2.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W1
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W2
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W3
    · exact W4
  · rw [r4.get (by decide : Reg.x5 ∉ laneRegs),r3.get (by decide : Reg.x5 ∉ laneRegs),r2.get (by decide : Reg.x5 ∉ laneRegs),r1.get (by decide : Reg.x5 ∉ laneRegs),r0.get (by decide)]
theorem mac_tsim (sg : Bool) (image : Image) (hc : MacCodeAt image sg) (sk : BitVec 256) (region : T3.Region) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg)) (h5 : s.getReg .x5 = 0) (hsk : SkAt s sk)
    (hreg : s.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region)) :
    TSim image sk s 1703621 2489875 2 2 (T3.privateMac region) (MacDone sg s) := by
  obtain ⟨u0,st0,pc0,x28,x10,x11,x12,m0,m8,m16,m24,m32,m40,m48,m56,r0,f0⟩ := mac_init sg image hc s hpc
  have p0 : PrivAt u0 sk 0 := by
    intro j; fin_cases j
    · exact m0.trans (hsk 0)
    · exact m8.trans (hsk 1)
    · exact m16
    · exact m24
    · exact m32.trans (hsk 2)
    · exact m40.trans (hsk 3)
    · exact m48
    · exact m56
  have z0 : u0.getReg .x5 = 0 := by rw [r0.get (by decide),h5]
  have v0 : hashArgumentsValid u0 = true := hashArgs_const u0 PRIV 64 KEYS x10 x11 x12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q0 := priv_query u0 sk 0 p0 x10 x11
  have fetch0 : fetch image u0 = some (.base .ECALL) := (hc.seg23).fetch u0 pc0 |>.trans rfl
  unfold T3.privateMac T3.privateMacKey
  simp only [bind_assoc,pure_bind]
  refine (TSim.steps st0 (TSim.privateTweak_bind (k := 1703597) (c := 2489844) (n := 1) (b := 1) fetch0 z0 v0 q0 (fun a => ?_))).of_eq
    rfl (by decide) (by decide) (by decide) (by decide)
  have pa : (writeHash u0 a).pc = pcOf (macBase sg+24) := by
    rw [pc_writeHash,pc0,pcOf_add4]
  obtain ⟨u1,st1,pc1,y12,n24,r1,f1⟩ := mac_next sg image hc (writeHash u0 a) pa (by simpa using x28)
  have p1 := priv_next p0 x12 f1 n24
  have y10 : u1.getReg .x10 = BitVec.ofNat 64 PRIV := by rw [r1.get (by decide),getReg_writeHash,x10]
  have y11 : u1.getReg .x11 = 64 := by rw [r1.get (by decide),getReg_writeHash,x11]
  have z1 : u1.getReg .x5 = 0 := by rw [r1.get (by decide),getReg_writeHash,z0]
  have v1 : hashArgumentsValid u1 = true := hashArgs_const u1 PRIV 64 (KEYS+32) y10 y11 y12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q1 := priv_query u1 sk 1 p1 y10 y11
  have fetch1 : fetch image u1 = some (.base .ECALL) := (hc.seg29).fetch u1 pc1 |>.trans rfl
  refine TSim.steps st1 (TSim.privateTweak_bind (k := 1703591) (c := 2489831) (n := 0) (b := 0) fetch1 z1 v1 q1 (fun b => ?_))
  have F0 : Frame s (writeHash u1 b) (MacW sg) := by
    have ha := Frame.writeHash u0 a KEYS x12 (by decide)
    have hb := Frame.writeHash u1 b (KEYS+32) y12 (by decide)
    apply (((f0.trans ha).trans f1).trans hb).mono
    intro A hA h
    unfold MacW
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · left; subst A; simp [PRIV]
    · exact Or.inr (Or.inl (by omega))
  have preg : (writeHash u1 b).readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region) := by
    rw [frame_readWords F0 REGION 16380 (by decide) (by
      intro i hi; cases sg <;> simp only [MacW,OutW,macOut,PRIV,KEYS,REGION,Bool.false_eq_true,if_false,if_true] <;> omega)]
    exact hreg
  have pb : (writeHash u1 b).pc = pcOf (macBase sg+30) := by
    rw [pc_writeHash,pc1,pcOf_add4]
  obtain ⟨t,st,pc,tagwords,zt,ft⟩ := mac_pure sg image hc (writeHash u1 b) (List.ofFn region) pb
    (by rw [List.length_ofFn]) (by rw [preg,wordsToNat_wordsOf 16380 _ (by rw [List.length_ofFn])])
  have hk := keys_after a b x12 f1 y12
  refine TSim.pure_steps st ?_
  refine ⟨pc,?_,?_,?_⟩
  · rw [zt,getReg_writeHash,z1]
  · rw [show (4 : Nat) = 2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32]
    have H : ∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) =
        (SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag (keyPair a b) (List.ofFn region))).extractLsb' (64*j.val) 64 := by
      intro j
      rw [tagwords j,laneWord_eq_tag _ _ _ _ hk j,encodeTag_word]
    change [t.getMem (BitVec.ofNat 64 (macOut sg+8*(0:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(1:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(2:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(3:Fin 4).val))] = _
    rw [H 0,H 1,H 2,H 3]
    rfl
  · exact (F0.trans ft).mono (fun A hA h => h.elim id (fun h => Or.inr (Or.inr h)))

end SigGolfCandidate.T3M.FullCache.Generic

namespace SigGolfCandidate.T3M.FullCache.Generic
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem sign_macCodeAt : MacCodeAt Images.signImage true := by
  constructor
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.FullCache.Generic
end
-- ==== merged from T3M_Keygen_LeafBlocks ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem sub41_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 41)) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if i < n then pcOf (b + 42) else pcOf (b + 95)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_41 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_41 h) s hpc (by simp [st_41, blk117_41.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_41, rebase, blk117_41.res, E.eval, CmpOp.eval, h19, h26,
      ofNat_slt i n hi hn]
    by_cases hin : i < n <;> simp [hin]
  · intro r hr; cases r <;> simp_all [st_41, blk117_41.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_41, blk117_41.res, rv_simp]
theorem fetch_sub59 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 59)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_59 h).fetch s hpc).trans rfl
set_option maxRecDepth 100000 in
theorem sub60_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 60)) (i digp : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (b + 72) ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16 * (i % 2))) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16 * (i % 2) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hrun := run_60 h.2.1
  have hm : i % 2 < 2 := Nat.mod_lt _ (by decide +kernel)
  have hobl : Oblig.all s st_60.obl := by
    simp only [st_60, blk117_60.res]
    t3n [h19, ofNat_and1]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_60 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_60, Result.toState_pc, E.eval]
  · t3n [st_60, blk117_60.res, h19, h22]
  · simp only [Result.toState_getMem, st_60, blk117_60.res, CHAIN, SEEDS]
    t3n [h19, ofNat_and1]
    congr 2; omega
  · simp only [Result.toState_getMem, st_60, blk117_60.res, CHAIN, SEEDS]
    t3n [h19, ofNat_and1]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_60, blk117_60.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, st_60, blk117_60.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub72_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 72)) (a : Nat) (ha : a + 1 ≤ 2 ^ 24) (d : Nat) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (hbyte : s.getByte (BitVec.ofNat 64 a) = BitVec.ofNat 8 d) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 73) ∧ t.getReg .x17 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x28 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 a := by
    rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x17) (rs := .x28) (off := 0) (codeAt_sub_72 h) hpc rfl
    (by rw [hoff, accessValid_iff, toNat_ofNat_lt (by omega)]; simp [MEMORY_BYTES]; omega)
  refine ⟨_, st, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = pcOf (b + 73)
    rw [hpc, pcOf_add4]
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide +kernel), hoff, hbyte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A _ _; simp
theorem sub73_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 73)) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf (b + 75) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_73 h.2.1
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt (show lay < 2 ^ 64 by omega)] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound hrun (codeAt_sub_73 h) s hpc (by simp [st_73, blk117_73.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, pcE_73, rebase, blk117_73.res, E.eval, CmpOp.eval, h8, hz]
  · simp [st_73, blk117_73.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_73, blk117_73.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_73, blk117_73.res, rv_simp]
theorem maxLow_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1000)) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i < n4 then pcOf (b + 1002) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 3 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_maxLow h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_maxLow h) s hpc (by simp [maxLowState, max117Low.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, maxLowPC, rebase, max117Low.res, E.eval, CmpOp.eval, h19, h27,
      ofNat_slt i n4 hi hn]
    by_cases hin : i < n4 <;> simp [hin]
  · simp [maxLowState, max117Low.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [maxLowState, max117Low.res, rv_simp] <;> rfl
  · intro A _ _; simp [maxLowState, max117Low.res, rv_simp]
theorem maxHigh_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1002)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 76) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_maxHigh h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_maxHigh h) s hpc (by simp [maxHighState, max117High.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [maxHighPC, Result.toState_pc, E.eval]
  · simp [maxHighState, max117High.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [maxHighState, max117High.res, rv_simp] <;> rfl
  · intro A _ _; simp [maxHighState, max117High.res, rv_simp]
theorem sub76_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 76)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 77) else pcOf (b + 78)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_76 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_76 h) s hpc (by simp [st_76, blk117_76.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_76, rebase, blk117_76.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_76, blk117_76.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_76, blk117_76.res, rv_simp]
theorem sub77_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 77)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 78) ∧ t.getReg .x21 = s.getReg .x17 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_77 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_77 h) s hpc (by simp [st_77, blk117_77.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_77, Result.toState_pc, E.eval]
  · simp [st_77, blk117_77.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_77, blk117_77.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_77, blk117_77.res, rv_simp]
theorem sub78_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 78)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf b ∧ t.getReg .x1 = pcOf (b + 79) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  have hrun := run_78 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_78 h) s hpc (by simp [st_78, blk117_78.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_78, Result.toState_pc, E.eval]
  · simp [st_78, blk117_78.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [st_78, blk117_78.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [st_78, blk117_78.res, rv_simp]
theorem sub79_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 79)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 92) else pcOf (b + 80)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_79 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_79 h) s hpc (by simp [st_79, blk117_79.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_79, rebase, blk117_79.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_79, blk117_79.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_79, blk117_79.res, rv_simp]
/-- Campaign T51 (endpad top leaf): 197..198 `sltu t5, zero, s3; add t3, s3, t5`. -/
theorem sub80_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 80)) (i : Nat) (hi : i < 2 ^ 32) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 82) ∧
      t.getReg .x28 = BitVec.ofNat 64 (i + (if i = 0 then 0 else 1)) ∧ RegsExcept s t [.x28, .x30] ∧
      Frame s t (fun _ => False) := by
  have hc := codeAt_sub80K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  have e : (if (0#64).ult (BitVec.ofNat 64 i) = true then (1#64) else 0#64) =
      BitVec.ofNat 64 (if i = 0 then 0 else 1) := by
    by_cases h0 : i = 0
    · subst h0; rfl
    · have : (0#64).ult (BitVec.ofNat 64 i) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
        simp; omega
      rw [if_pos this, if_neg h0]
  refine ⟨_, symRun_sound run_80K hc s hpc (by simp [st_80K, kblk_80.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_80K, kblk_80.res, rv_simp, h19]
    first | done | t3n [h19, e]
  · intro r hr; simp at hr; cases r <;> simp_all [st_80K, kblk_80.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_80K, kblk_80.res, rv_simp]
/-- Campaign T51: 199 `slli t3, t3, 4`. -/
theorem sub82_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 82)) (o : Nat) (ho : o < 2 ^ 32) (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 83) ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * o) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hc := codeAt_sub82K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  refine ⟨_, symRun_sound run_82K hc s hpc (by simp [st_82K, kblk_82.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_82K, kblk_82.res, rv_simp, h28]
    t3n [h28]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_82K, kblk_82.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_82K, kblk_82.res, rv_simp]
theorem sub83_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 83)) (o : Nat) (ho : o % 8 = 0) (ho' : LEAFPK + o + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 92) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + o ∨ A = LEAFPK + o + 8) := by
  have hrun := run_83 h.2.1
  have hobl : Oblig.all s st_83.obl := by
    simp only [st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho'
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_83 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_83, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho' ⊢
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho' ⊢
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [st_83, blk117_83.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [LEAFPK] at hn ho'
    simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub92_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 92)) (i v : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 v) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getReg .x23 = BitVec.ofNat 64 (v + 16) ∧ RegsExcept s t [.x19, .x23] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_92 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_92 h) s hpc (by simp [st_92, blk117_92.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_92, Result.toState_pc, E.eval]
  · t3n [st_92, blk117_92.res, h19]
  · t3n [st_92, blk117_92.res, h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_92, blk117_92.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_92, blk117_92.res, rv_simp]
theorem sub95_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 95)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 112) else pcOf (b + 96)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_95 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_95 h) s hpc (by simp [st_95, blk117_95.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_95, rebase, blk117_95.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_95, blk117_95.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_95, blk117_95.res, rv_simp]
/-- C4 (b3cc11b's keygen word): the top leaf exit also loads `x29 = leaf % 2` (the answer-half selector). -/
theorem sub96_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 96)) (n : Nat) (hn : n = 51 ∨ n = 43)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) (leaf : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 105) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧
      t.getReg .x12 = BitVec.ofNat 64 LOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (leaf % 2) ∧
      RegsExcept s t [.x10, .x11, .x12, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := codeAt_sub96K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  refine ⟨_, symRun_sound run_96K hc s hpc (by simp [st_96K, kblk_96.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [st_96K, kblk_96.res, rv_simp]
  · simp only [Result.toState_getReg, st_96K, kblk_96.res, rv_simp, h26]
    rcases hn with rfl | rfl <;> decide +kernel
  · simp [st_96K, kblk_96.res, rv_simp]
  · simp only [Result.toState_getReg, st_96K, kblk_96.res, rv_simp, h18]
    exact ofNat_and1 leaf
  · intro r hr; simp at hr; cases r <;> simp_all [st_96K, kblk_96.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_96K, kblk_96.res, rv_simp]
theorem fetch_sub105 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 105)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_105 h).fetch s hpc).trans rfl
/-- Leaf copy (C4, b3cc11b's keygen word): `dest ← LOUT + 16 - 16 p` (`p = leaf % 2`): the high half of the leaf
answer for an even leaf, the low half for an odd one. -/
theorem sub106_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 106)) (dest : Nat) (hd : dest % 8 = 0) (hd' : dest + 16 ≤ 2 ^ 24)
    (hdl : dest + 16 ≤ LOUT ∨ LOUT + 32 ≤ dest) (h25 : s.getReg .x25 = BitVec.ofNat 64 dest) (p : Nat) (hp : p < 2)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 p) (h12 : s.getReg .x12 = BitVec.ofNat 64 LOUT) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 112) ∧
      t.getMem (BitVec.ofNat 64 dest) = s.getMem (BitVec.ofNat 64 (LOUT + 16 - 16 * p)) ∧
      t.getMem (BitVec.ofNat 64 (dest + 8)) = s.getMem (BitVec.ofNat 64 (LOUT + 16 - 16 * p + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = dest ∨ A = dest + 8) := by
  have hc := codeAt_sub106K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  have e : s.getReg .x12 - s.getReg .x29 <<< 4 = BitVec.ofNat 64 (LOUT - 16 * p) := by
    rw [h12, h29, ofNat_shl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, LOUT]
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> norm_num
  have hobl : Oblig.all s st_106K.obl := by
    simp only [st_106K, kblk_106.res]
    t3n [h25, e]
    simp only [LOUT] at *
    omega
  refine ⟨_, symRun_sound run_106K hc s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_106K, kblk_106.res]
    t3n [h25, e]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2
    simp only [LOUT] at *
    omega
  · simp only [Result.toState_getMem, st_106K, kblk_106.res]
    t3n [h25, e]
    congr 2
    simp only [LOUT] at *
    omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_106K, kblk_106.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_106K, kblk_106.res]
    t3n [h25, e]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub112_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 112)) (k : Nat) (h3 : s.getReg .x3 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_112 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_112 h) s hpc (by simp [st_112, blk117_112.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_112, blk117_112.res, rv_simp, h3, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_112, blk117_112.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_112, blk117_112.res, rv_simp]
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_Leaf ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
def n4 (lay : Layer) : Nat := if lay = 0 then 51 else 0
def leafBlocks (lay : Layer) : Nat := (16 * (chainCount lay + 1) + 63) / 64
theorem chainCount_cases (lay : Layer) : chainCount lay = 51 ∨ chainCount lay = 43 := by
  fin_cases lay <;> simp [chainCount]
theorem n4_le (lay : Layer) : n4 lay ≤ chainCount lay := by
  unfold n4; split_ifs with h
  · subst h; simp [chainCount]
  · omega
/-- Campaign T51: top chains 0..26 radix 6, 27..47 radix 5, 48..49 radix 7, 50 radix 6 (restated; #938: 4 below
`n4 = 51`, else 7). -/
theorem maxDigit_shape (lay : Layer) (i : Nat) :
    maxDigit lay i = if lay = 0 then (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) else 7 := by
  unfold maxDigit
  split_ifs <;> rfl

/-- Steps of the sign's top cap selector from `b + 75` (campaign T51: `j 1937` and the cap block 1937..1947,
`maxDigit 0 i` = 5 / 4 / 6 / 5 for `i < 27 / 48 / 50 / else`); 0 on lower layers. Sign-only (the keygen and expand
leaf proofs do not use it). -/
def selectorExtra (lay : Layer) (i : Nat) : Nat :=
  if lay = 0 then (if i < 27 then 4 else if i < 48 then 7 else if i < 50 then 10 else 12) else 0
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
    (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨
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
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 112 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
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
/-- Campaign T51 ("endpad"): the top leaf input is `end_0 | tweak | end_1 .. end_50` (832 bytes, 13 blocks, aligned). -/
theorem leafInput_words (A : LeafArgs) (h0 : A.lay = 0) (ends : List Digest) (hlen : ends.length = A.n) :
    wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) := by
  have hn51 : A.n = 51 := by show chainCount A.lay = 51; rw [h0]; rfl
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * 50 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen, hn51]
  unfold T3.leafInput
  rw [if_pos h0, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length, hfl]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length] <;> omega),
    wordsOf_append _ _ (by simp only [bytesLE_length] <;> omega), wordsOf_bytesLE16 (T3.leafTweak _ _ _)]
  unfold T3.leafTweak
  rw [T3.append64_low, BitVec.extractLsb'_append_eq_left]
  rfl

theorem leafInput_length (A : LeafArgs) (h0 : A.lay = 0) (ends : List Digest) (hlen : ends.length = A.n) :
    (pad64 (T3.leafInput A.lay A.tree A.leaf ends)).length = 64 * leafBlocks A.lay := by
  have hn51 : A.n = 51 := by show chainCount A.lay = 51; rw [h0]; rfl
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * 50 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen, hn51]
  unfold T3.leafInput
  rw [if_pos h0, pad64_length]
  simp only [List.length_append, bytesLE_length, hfl, leafBlocks, show chainCount A.lay = A.n from rfl, hn51]

/-- Retired in campaign T8D: the keygen top leaf (family seeds) is `buildLeafTop_tsim` in `T3M/Keygen/TopLeaf.lean`.
The name is kept because `T3M/Sign/PackedLowTree.lean` lists it in an `open` clause. -/
theorem buildLeaf_tsim : True := trivial
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Sign_Kernels ====
section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Layer selections admissible digestSearch counterSearch decode
  attemptLimit counterLimit chainCount target Selection)
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((selections N).getD c ⟨0, []⟩).bucket * 128 + ((selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
structure DsPre (s : MachineState) (rho : Digest) (m : Message) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def DsPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => Failed t
  | some (_, N), t => t.pc = pcOf 172 ∧ t.getReg .x5 = 0 ∧ admissible (selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
def dsCost : Nat := attemptLimit * 700 + 100
def DigestSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (rho : Digest) (m : Message), DsPre s rho m →
    TBSim image sk s dsCost (digestSearch rho m 0 attemptLimit) (DsPost s)
def csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (X : Nat) : Prop :=
  X = ENC + 16 ∨ X = ENC + 24 ∨ X = ENC + 32 ∨ (EOUT ≤ X ∧ X < EOUT + 32) ∨ (DIGITS ≤ X ∧ X < DIGITS + 64)
structure CsPre (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : Digest) (ret : Nat) : Prop where
  pc : s.pc = pcOf 646
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (Keygen.n4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  msg : DigAt s ENC msg
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  z48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = 0
  z56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = 0
  table : Search.TableOK s
def DummyRet (s : MachineState) (ret : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧
    (∀ i < 54, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (T3.dummyTop.getD i 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
    (t.getReg .x25).toNat ≤ 126
def CsPost (s : MachineState) (lay : Layer) (ret : Nat) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if lay = 0 then DummyRet s ret t else Failed t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, decode lay v = some ds) ∧
      (∀ i < chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ target lay
def csCost (lay : Layer) : Nat := counterLimit * (if lay = 0 then 412 else 160) + 2000
def CounterSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : Digest) (ret : Nat),
    CsPre s lay tree leaf msg ret →
      TBSim image sk s (csCost lay) (counterSearch lay tree leaf msg 0 counterLimit) (CsPost s lay ret)
structure Kernels (sk : BitVec 256) : Prop where
  digest : DigestSearchSpec sk
  counter : CounterSearchSpec sk
end SigGolfCandidate.T3M.Sign
end
-- ==== merged from T3M_Sign_Init ====
section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Cache Region cacheBytes readLE)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (TOP_DATA TableOK signData_length signData_table)
theorem readWords_of_get (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_get t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]
theorem extractLsb'_ofNat_readLE (m : Nat) (l : List UInt8) (hl : l.length = 8 * m) (j : Nat) (hj : j < m) :
    (BitVec.ofNat (8 * (8 * m)) (readLE l)).extractLsb' (64 * j) 64 = (wordsOf l).getD j 0 := by
  rw [wordsOf_eq_range m l hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  have hlt := readLE_lt l
  rw [hl, ← two_pow_eight_mul] at hlt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
/-- Sign data base (`dataBase` of the 86,144-byte data: the 128-byte `Zt` table first). -/
def SIGN_DATA : Nat := 16691072
def sdata : MachineState :=
  ({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 SIGN_DATA) Images.signData
theorem sdata_getMem (A : Nat) (hA : A < 2 ^ 64) :
    sdata.getMem (BitVec.ofNat 64 A) =
      if SIGN_DATA ≤ A ∧ A < SIGN_DATA + 86144 ∧ (A - SIGN_DATA) % 8 = 0 then
        bytesToWordLE ((Images.signData.drop (A - SIGN_DATA)).take 8) else 0 := by
  unfold sdata
  rw [getMem_writeBytesAsWords _ _ SIGN_DATA A (by rw [signData_length]; decide) hA, signData_length]
  rfl
theorem sdata_zero (A : Nat) (hA : A < SIGN_DATA) : sdata.getMem (BitVec.ofNat 64 A) = 0 := by
  rw [sdata_getMem A (by unfold SIGN_DATA at hA; omega), if_neg (by omega)]
def sinit (sk : SecretKey) (cache : Bytes 131072) (m : Message) : MachineState :=
  (((sdata.writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).writeBytesAsWords (BitVec.ofNat 64 0x80000) (bytes cache)).writeBytesAsWords
    (BitVec.ofNat 64 0x6620) (bytes m)).setReg .x2 (BitVec.ofNat 64 SIGN_DATA)
theorem sinit_pc (sk : SecretKey) (cache : Bytes 131072) (m : Message) : (sinit sk cache m).pc = pcOf 0 := by
  unfold sinit
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords]
  simp [sdata, MachineState.pc_writeBytesAsWords]
theorem bytes_length' {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
theorem sinit_getMem (sk : SecretKey) (cache : Bytes 131072) (m : Message) (A : Nat) (hA : A < 2 ^ 64) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 A) =
      if 0x6620 ≤ A ∧ A < 0x6640 ∧ (A - 0x6620) % 8 = 0 then bytesToWordLE (((bytes m).drop (A - 0x6620)).take 8)
      else if 0x80000 ≤ A ∧ A < 0xA0000 ∧ (A - 0x80000) % 8 = 0 then
        bytesToWordLE (((bytes cache).drop (A - 0x80000)).take 8)
      else if 0x80 ≤ A ∧ A < 0xA0 ∧ (A - 0x80) % 8 = 0 then bytesToWordLE (((bytes sk).drop (A - 0x80)).take 8)
      else sdata.getMem (BitVec.ofNat 64 A) := by
  unfold sinit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x6620 A (by rw [bytes_length']; decide) hA,
    getMem_writeBytesAsWords _ _ 0x80000 A (by rw [bytes_length']; decide) hA,
    getMem_writeBytesAsWords _ _ 0x80 A (by rw [bytes_length']; decide) hA, bytes_length', bytes_length',
    bytes_length']
theorem sinit_sk (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_neg (by sg_omega), if_neg (by sg_omega), if_pos (by sg_omega),
    show SK + 8 * j - 0x80 = 8 * j by sg_omega, bytesToWordLE_bytes sk j (by omega)]
theorem sinit_msg (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_pos (by sg_omega), show MSG + 8 * j - 0x6620 = 8 * j by sg_omega,
    bytesToWordLE_bytes m j (by omega)]
theorem sinit_cache (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 16384) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * j)) = cache.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_neg (by sg_omega), if_pos (by sg_omega),
    show CACHE + 8 * j - 0x80000 = 8 * j by sg_omega, bytesToWordLE_bytes cache j (by omega)]
theorem sinit_zero (sk : SecretKey) (cache : Bytes 131072) (m : Message) (A : Nat) (hA : A < SIGN_DATA)
    (h : A < 0x80 ∨ (0xA0 ≤ A ∧ A < 0x6620) ∨ (0x6640 ≤ A ∧ A < 0x80000) ∨ 0xA0000 ≤ A) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [sinit_getMem _ _ _ _ (by unfold SIGN_DATA at hA; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), sdata_zero A hA]
theorem sinit_cacheWords (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 16384) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * j)) =
      (wordsOf (cacheBytes (cacheDec cache))).getD j 0 := by
  rw [sinit_cache _ _ _ j hj]
  conv_lhs => rw [← cacheB_cacheDec cache]
  exact extractLsb'_ofNat_readLE 16384 _ (cacheBytes_length _) j hj
theorem wordsOf_cacheBytes (c : Cache) :
    wordsOf (cacheBytes c) = [c.tag.extractLsb' 0 64, c.tag.extractLsb' 64 64, c.tag.extractLsb' 128 64,
      c.tag.extractLsb' 192 64] ++ wordsOf (List.ofFn c.region) := by
  rw [cacheBytes, wordsOf_append (bytesLE 32 c.tag) (List.ofFn c.region) (by rw [bytesLE_length]),
    wordsOf_bytesLE32]
theorem length_wordsOf_region (r : Region) : (wordsOf (List.ofFn r)).length = 16380 := by
  rw [wordsOf_eq_range 16380 _ (by rw [List.length_ofFn]), List.length_map, List.length_range]
theorem sinit_tag (sk : SecretKey) (cache : Bytes 131072) (m : Message) (k : Nat) (hk : k < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * k)) = (cacheDec cache).tag.extractLsb' (64 * k) 64 := by
  rw [sinit_cacheWords _ _ _ k (by omega), wordsOf_cacheBytes]
  interval_cases k <;> rfl
theorem sinit_region (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (sinit sk cache m).readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
  refine readWords_of_get _ _ _ _ (length_wordsOf_region _) (fun j hj => ?_)
  rw [show REGION + 8 * j = CACHE + 8 * (4 + j) by sg_omega, sinit_cacheWords _ _ _ _ (by omega),
    wordsOf_cacheBytes, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show [(cacheDec cache).tag.extractLsb' 0 64, (cacheDec cache).tag.extractLsb' 64 64,
      (cacheDec cache).tag.extractLsb' 128 64, (cacheDec cache).tag.extractLsb' 192 64].length ≤ 4 + j by
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton]; omega)]
  rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton, Nat.add_sub_cancel_left]
/-- Campaign T51: a byte of the top data block (`TOP_DATA + i`, sign data offset 82048 + i) in the initial state. -/
theorem sinit_topByte (sk : SecretKey) (cache : Bytes 131072) (m : Message) (i : Nat) (hi : i < 4096)
    (b : BitVec 8) (hb : Images.signData.getD (82048 + i) 0 = b) :
    (sinit sk cache m).getByte (BitVec.ofNat 64 (TOP_DATA + i)) = b := by
  rw [getByte_eq_word _ _ (by simp only [TOP_DATA]; omega),
    sinit_getMem _ _ _ _ (by simp only [TOP_DATA]; omega),
    if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega),
    sdata_getMem _ (by simp only [TOP_DATA]; omega), if_pos (by simp only [TOP_DATA, SIGN_DATA]; omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - SIGN_DATA + (TOP_DATA + i) % 8 = 82048 + i := by simp only [TOP_DATA, SIGN_DATA]; omega
  rw [hidx]
  rw [List.getD_eq_getElem?_getD] at hb
  exact hb
/-- Campaign T51: only the choice flag byte (TOP_DATA + 631) is read; it is 1 in the initial state. -/
theorem sinit_cf (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.CfFlagOK 1 (sinit sk cache m) :=
  sinit_topByte sk cache m 631 (by omega) _ Search.signData_flag
/-- Campaign T51: the lower reward tables (TOP_DATA + 1024..2047) in the initial state. -/
theorem sinit_reward (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.Reward.LowerTablesOK (sinit sk cache m) := fun i hi hj =>
  sinit_topByte sk cache m i (by omega) _ (Search.signData_lowerReward i hi hj)

/-! ### Campaign T51: the packed top tables (1892 bytes at `0xFFF800 = TOP_DATA + 2048`) as the 473 `lwu` words -/
/-- Checks dword `k` of a byte list against the T51 entries `2k` (low half) and `2k + 1` (high half, `< 473`). -/
def t51Chk : Nat → List (BitVec 8) → Bool
  | k, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      (extractWord32 (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]) 0 ==
        BitVec.ofNat 32 (Search.T51.tEntry (2 * k))) &&
      (decide (473 ≤ 2 * k + 1) || (extractWord32 (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]) 1 ==
        BitVec.ofNat 32 (Search.T51.tEntry (2 * k + 1)))) &&
      t51Chk (k + 1) rest
  | _, [] => true
  | _, _ => false
set_option maxRecDepth 100000 in
theorem t51_chk : t51Chk 0 ((Images.signLegacyData.drop 2048).take 1896) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t51Slice_length : ((Images.signLegacyData.drop 2048).take 1896).length = 1896 := by decide +kernel
theorem t51Chk_get : ∀ (m k : Nat) (l : List (BitVec 8)), t51Chk k l = true → 8 * m + 8 ≤ l.length →
    extractWord32 (bytesToWordLE ((l.drop (8 * m)).take 8)) 0 = BitVec.ofNat 32 (Search.T51.tEntry (2 * (k + m))) ∧
    (2 * (k + m) + 1 < 473 →
      extractWord32 (bytesToWordLE ((l.drop (8 * m)).take 8)) 1 = BitVec.ofNat 32 (Search.T51.tEntry (2 * (k + m) + 1)))
  | m, k, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h, hl => by
    simp only [t51Chk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases m with _ | m
    · refine ⟨by simpa using h.1.1, fun hlt => ?_⟩
      rcases h.1.2 with h' | h'
      · simp at hlt; omega
      · simpa using h'
    · have := t51Chk_get m (k + 1) rest h.2 (by simp at hl; omega)
      rw [show 8 * (m + 1) = 8 + 8 * m by omega, ← List.drop_drop]
      simpa [show k + 1 + m = k + (m + 1) by omega] using this
  | m, k, [], _, hl => by simp at hl
  | m, k, [_], _, hl => by simp at hl <;> omega
  | m, k, [_, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _, _, _], _, hl => by simp at hl <;> omega
theorem signData_drop_legacy (n : Nat) : Images.signData.drop (82048 + n) = Images.signLegacyData.drop n := by
  have h1 := Search.signZtData_length
  have h2 := Images.signPrefixData_length
  have e1 : Images.signZtData.length ≤ 82048 + n := by omega
  have e2 : Images.signPrefixData.length ≤ 82048 + n - Images.signZtData.length := by omega
  rw [Images.signData, List.drop_append, List.drop_eq_nil_of_le e1, List.nil_append, List.drop_append,
    List.drop_eq_nil_of_le e2, List.nil_append, h1, h2, show 82048 + n - 128 - 81920 = n by omega]
theorem t51_slice (m : Nat) (hm : 8 * m + 8 ≤ 1896) :
    ((((Images.signLegacyData.drop 2048).take 1896).drop (8 * m)).take 8) =
      (Images.signLegacyData.drop (2048 + 8 * m)).take 8 := by
  rw [List.drop_take, List.drop_drop, List.take_take, show min 8 (1896 - 8 * m) = 8 by omega]
/-- Campaign T51: the packed top tables at `0xFFF800` as the 473 `lwu` words in the initial state. -/
theorem sinit_t51 (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.T51.T51TableW 0xFFF800 (sinit sk cache m) := by
  intro f hf
  have hlt : 0xFFF800 + 4 * f < 2 ^ 64 := by omega
  unfold MachineState.getWord32
  have ha : alignToDword (BitVec.ofNat 64 (0xFFF800 + 4 * f)) = BitVec.ofNat 64 (0xFFF800 + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt hlt, toNat_ofNat_lt (by omega)]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0xFFF800 + 4 * f)) / 4 = f % 2 := by
    rw [byteOffset_eq, toNat_ofNat_lt hlt]; omega
  rw [ha, hb, sinit_getMem _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    sdata_getMem _ (by omega), if_pos (by simp only [SIGN_DATA]; omega),
    show 0xFFF800 + 8 * (f / 2) - SIGN_DATA = 82048 + (2048 + 8 * (f / 2)) by simp only [SIGN_DATA]; omega,
    signData_drop_legacy, ← t51_slice (f / 2) (by omega)]
  have hr := t51Chk_get (f / 2) 0 _ t51_chk (by rw [t51Slice_length]; omega)
  rw [Nat.zero_add] at hr
  rcases Nat.mod_two_eq_zero_or_one f with h0 | h1
  · rw [h0, hr.1, show 2 * (f / 2) = f by omega]
  · rw [h1, hr.2 (by omega), show 2 * (f / 2) + 1 = f by omega]
theorem sinit_table (sk : SecretKey) (cache : Bytes 131072) (m : Message) : TableOK (sinit sk cache m) := by
  intro i hi
  rw [getByte_eq_word _ _ (by simp only [TOP_DATA]; omega),
    sinit_getMem _ _ _ _ (by simp only [TOP_DATA]; omega),
    if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega),
    sdata_getMem _ (by simp only [TOP_DATA]; omega), if_pos (by simp only [TOP_DATA, SIGN_DATA]; omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - SIGN_DATA + (TOP_DATA + i) % 8 = 82048 + i := by simp only [TOP_DATA, SIGN_DATA]; omega
  rw [hidx]
  exact signData_table i hi
theorem sinit_zt (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.ZeroCap.ZtOK 543 (sinit sk cache m) := by
  intro r hr
  simp only [Search.ZeroCap.ZT, show (543:Nat) ≠ 354 by decide, if_false]
  rw [getByte_eq_word _ _ (by omega),
    sinit_getMem _ _ _ _ (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    sdata_getMem _ (by omega), if_pos (by simp only [SIGN_DATA]; omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (16691072 + r) (show 0 < 8 by decide))]
  have hidx : (16691072 + r) / 8 * 8 - SIGN_DATA + (16691072 + r) % 8 = r := by simp only [SIGN_DATA]; omega
  rw [hidx, ← List.getD_eq_getElem?_getD]
  exact Search.signData_zt r hr
end SigGolfCandidate.T3M.Sign
end
-- ==== merged from T3M_Sign_BaseInv ====
section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
def NeverW (A : Nat) : Prop :=
  A = FLEAF ∨ A = FLEAF + 8 ∨ A = FLEAF + 48 ∨ A = FLEAF + 56 ∨ A = NODE + 32 ∨ A = NODE + 40 ∨
    A = CHAIN ∨ A = CHAIN + 8 ∨ A = CHAIN + 32 ∨ A = CHAIN + 40 ∨
    (ZDIG ≤ A ∧ A < ZDIG + 64) ∨ A = ENC + 40 ∨ A = NBUF + 32
def BaseA (A : Nat) : Prop :=
  A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 ∨
    (REGION ≤ A ∧ A < REGION + 131040) ∨ NeverW A ∨
      ((Search.TOP_DATA ≤ A ∧ A < Search.TOP_DATA + 3944) ∨ (16691072 ≤ A ∧ A < 16691200))
structure Base (sk : SecretKey) (cache : Bytes 131072) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  x5 : t.getReg .x5 = 0
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  region : ∀ k < 16380, t.getMem (BitVec.ofNat 64 (REGION + 8 * k)) = cache.extractLsb' (64 * (k + 4)) 64
  zero : ∀ A < 2 ^ 64, NeverW A → t.getMem (BitVec.ofNat 64 A) = 0
  table : Search.TableOK t
  /-- Campaign T51: only the choice flag byte (TOP_DATA + 631) of the cf block is read. -/
  cf : Search.CfFlagOK cfFlag t
  /-- Campaign T51: only the lower reward tables (TOP_DATA + 1024..2047) are read. -/
  reward : Search.Reward.LowerTablesOK t
  /-- v6: the top zero-digit table `Zt` (first 128 data bytes). -/
  zt : Search.ZeroCap.ZtOK 543 t
  /-- Campaign T51: the packed top tables (1892 bytes at `TOP_DATA + 2048 = 0xFFF800`, 473 `lwu` words). -/
  t51 : Search.T51.T51TableW 0xFFF800 t
variable {cfFlag : Nat}
theorem Base.frame {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : Base (cfFlag := cfFlag) sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → ¬ W A) : Base (cfFlag := cfFlag) sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (hW A hA hb)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega),
      h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn), h.zero A hA hn]
  · exact h.table.frame hf (fun i hi => hW _ (by unfold Search.TOP_DATA; omega) (by
      unfold BaseA
      right; right; right; right; right; right; right; right
      unfold Search.TOP_DATA; omega))
  · exact h.cf.frame hf (fun i hi hi' => hW _ (by unfold Search.TOP_DATA; omega) (by
      unfold BaseA
      right; right; right; right; right; right; right; right
      unfold Search.TOP_DATA; omega))
  · exact h.reward.frame hf (fun i hi hi' => hW _ (by unfold Search.TOP_DATA; omega) (by
      unfold BaseA
      right; right; right; right; right; right; right; right
      unfold Search.TOP_DATA; omega))
  · exact h.zt.frame hf (fun r hr => hW _ (by simp only [Search.ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; omega) (by
      unfold BaseA
      right; right; right; right; right; right; right; right; right
      simp only [Search.ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; omega))
  · exact h.t51.frame hf (by decide) (by decide) (fun k hk => hW _ (by omega) (by
      unfold BaseA
      right; right; right; right; right; right; right; right; left
      unfold Search.TOP_DATA; omega))
theorem readWords_eq_map (t : MachineState) (A : Nat) :
    ∀ n, A + 8 * n < 2 ^ 64 →
      t.readWords (BitVec.ofNat 64 A) n = (List.range n).map fun j => t.getMem (BitVec.ofNat 64 (A + 8 * j))
  | 0, _ => rfl
  | n + 1, h => by
    rw [readWords_add, readWords_eq_map t A n (by omega), readWords_one, List.range_succ, List.map_append]
    rfl
theorem readLE_region (cache : Bytes 131072) :
    T3.readLE (List.ofFn (cacheDec cache).region) = cache.toNat / 2 ^ 256 := by
  have e : List.ofFn (cacheDec cache).region =
      List.ofFn fun i : Fin 131040 => UInt8.ofNat (cache.toNat / 256 ^ 32 / 256 ^ i.val % 256) := by
    exact congrArg List.ofFn (funext fun i => by
      show UInt8.ofNat (cache.toNat / 256 ^ (32 + i.val) % 256) = _
      rw [pow_add, Nat.div_div_eq_div_mul])
  rw [e, readLE_ofFn_digits, show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num]
  apply Nat.mod_eq_of_lt
  have h1 : cache.toNat < 2 ^ (256 + 8 * 131040) :=
    lt_of_lt_of_eq cache.isLt (congrArg (2 ^ ·) (by norm_num : 8 * 131072 = 256 + 8 * 131040))
  have h2 : (256 : Nat) ^ 131040 = 2 ^ (8 * 131040) :=
    (congrArg (· ^ 131040) (by norm_num : (256 : Nat) = 2 ^ 8)).trans (pow_mul 2 8 131040).symm
  rw [h2]
  rw [pow_add] at h1
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (lt_of_lt_of_eq h1 (Nat.mul_comm _ _))
theorem wordsOf_region (cache : Bytes 131072) :
    wordsOf (List.ofFn (cacheDec cache).region) =
      (List.range 16380).map fun k => cache.extractLsb' (64 * (k + 4)) 64 := by
  rw [wordsOf_eq_range 16380 _ (by rw [List.length_ofFn]), readLE_region]
  apply List.map_congr_left
  intro k _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
  congr 3; ring
theorem Base.region_words {sk : SecretKey} {cache : Bytes 131072} {t : MachineState} (h : Base (cfFlag := cfFlag) sk cache t) :
    t.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
  rw [readWords_eq_map t REGION 16380 (by sg_omega), wordsOf_region]
  exact List.map_congr_left (fun k hk => h.region k (List.mem_range.mp hk))
end SigGolfCandidate.T3M.Sign
end
-- ==== merged from T3M_Sign_BoundaryInvariant ====
section

section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
theorem blk0_spec (s : MachineState) (hpc : s.pc = pcOf 0) :
    ∃ t, Steps image s 17 17 t ∧ t.pc = pcOf 1227 ∧ t.getReg .x5 = 0 ∧
      t.getMem (BitVec.ofNat 64 TAG) = s.getMem (BitVec.ofNat 64 CACHE) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 8)) = s.getMem (BitVec.ofNat 64 (CACHE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 16)) = s.getMem (BitVec.ofNat 64 (CACHE + 16)) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 24)) = s.getMem (BitVec.ofNat 64 (CACHE + 24)) ∧
      RegsExcept s t [.x5, .x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => (TAG ≤ A ∧ A < TAG + 32) ∨ (MACBLK ≤ A ∧ A < MACBLK + 64)) := by
  refine ⟨_, symRun_sound blk_0 codeAt_0 s hpc (by simp [blk_0.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_0.res, E.eval]
  · simp [blk_0.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_0.res, TAG, CACHE, MACBLK, SK]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_0.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TAG, MACBLK] at hn
    simp only [Result.toState_getMem, blk_0.res]
    t3n []
    repeat rw [if_neg (by omega)]
theorem blk1432_spec (s : MachineState) (hpc : s.pc = pcOf 1432) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 47 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1432 codeAt_1432 s hpc (by simp [blk_1432.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [blk_1432.res, E.eval]
  · intro r hr; cases r <;> simp [blk_1432.res, rv_simp] <;> rfl
  · intro A hA hn; simp [blk_1432.res, rv_simp]
theorem fetch_46 (s : MachineState) (hpc : s.pc = pcOf 46) : fetch image s = some (.base .ECALL) :=
  (codeAt_46.fetch s hpc).trans rfl
theorem blk47_spec (s : MachineState) (hpc : s.pc = pcOf 47) :
    ∃ t, Steps image s 7 7 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 MACOUT) = s.getMem (BitVec.ofNat 64 TAG) then pcOf 54
        else pcOf 543) ∧
      t.getReg .x28 = BitVec.ofNat 64 MACOUT ∧ t.getReg .x29 = BitVec.ofNat 64 TAG ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_47 codeAt_47 s hpc (by simp [blk_47.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_47.res, E.eval, CmpOp.eval, MACOUT, TAG]
    t3n []
    split_ifs <;> simp_all
  · simp [blk_47.res, rv_simp]
  · simp [blk_47.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_47.res, rv_simp]
theorem cmp_next_spec {a k : Nat} {seg : List (BitVec 32)} {r : Result}
    (hc : CodeAt image (pcOf a) seg) (hrun : symRun { noAlias := true } seg (pcOf a) 100 = some r)
    (s : MachineState) (hpc : s.pc = pcOf a)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG)
    (hobl : r.obligs s)
    (hpcE : (r.toState s).pc = if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (TAG + 8 * k)) then pcOf (a + 3) else pcOf 543)
    (hregs : RegsExcept s (r.toState s) [.x6, .x7]) (hfr : Frame s (r.toState s) (fun _ => False)) :
    ∃ t, Steps image s r.steps r.cycles t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * k))
        then pcOf (a + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  ⟨_, symRun_sound hrun hc s hpc hobl, hpcE, hregs, hfr⟩
theorem blk54_spec (s : MachineState) (hpc : s.pc = pcOf 54)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 1)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 1))
        then pcOf (54 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec codeAt_54 blk_54 s hpc h28 h29 (by simp only [blk_54.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_54.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_54.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_54.res, rv_simp])
theorem blk57_spec (s : MachineState) (hpc : s.pc = pcOf 57)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 2)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 2))
        then pcOf (57 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec codeAt_57 blk_57 s hpc h28 h29 (by simp only [blk_57.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_57.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_57.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_57.res, rv_simp])
theorem blk60_spec (s : MachineState) (hpc : s.pc = pcOf 60)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 3)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 3))
        then pcOf (60 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec codeAt_60 blk_60 s hpc h28 h29 (by simp only [blk_60.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_60.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_60.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_60.res, rv_simp])
theorem blk63_spec (s : MachineState) (hpc : s.pc = pcOf 63) :
    ∃ t, Steps image s 59 59 t ∧ t.pc = pcOf 122 ∧
      t.getReg .x10 = BitVec.ofNat 64 NONCE ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 RHOOUT ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem (BitVec.ofNat 64 SK) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 8)) = s.getMem (BitVec.ofNat 64 (SK + 8)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 32)) = s.getMem (BitVec.ofNat 64 (SK + 16)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 40)) = s.getMem (BitVec.ofNat 64 (SK + 24)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0 ∧
      t.getMem (BitVec.ofNat 64 NONCE) = s.getMem (BitVec.ofNat 64 SK) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 8)) = s.getMem (BitVec.ofNat 64 (SK + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 16)) = BitVec.ofNat 64 1793 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 32)) = s.getMem (BitVec.ofNat 64 (SK + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 40)) = s.getMem (BitVec.ofNat 64 (SK + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (NONCE + 56)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 64)) = s.getMem (BitVec.ofNat 64 MSG) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 72)) = s.getMem (BitVec.ofNat 64 (MSG + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 80)) = s.getMem (BitVec.ofNat 64 (MSG + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 88)) = s.getMem (BitVec.ofNat 64 (MSG + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨
        A = PRIV + 56 ∨ (NONCE ≤ A ∧ A < NONCE + 96)) := by
  refine ⟨_, symRun_sound blk_63 codeAt_63 s hpc (by simp [blk_63.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_63.res, E.eval]
  · simp [blk_63.res, rv_simp]
  · simp [blk_63.res, rv_simp]
  · simp [blk_63.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_63.res, PRIV, NONCE, SK, MSG]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_63.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV, NONCE] at hn
    simp only [Result.toState_getMem, blk_63.res]
    t3n []
    repeat rw [if_neg (by omega)]
theorem fetch_122 (s : MachineState) (hpc : s.pc = pcOf 122) : fetch image s = some (.base .ECALL) :=
  (codeAt_122.fetch s hpc).trans rfl
theorem blk123_spec (s : MachineState) (hpc : s.pc = pcOf 123) :
    ∃ t, Steps image s 30 30 t ∧ t.pc = pcOf 153 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 SIG) = s.getMem (BitVec.ofNat 64 RHOOUT) ∧
      t.getMem (BitVec.ofNat 64 (SIG + 8)) = s.getMem (BitVec.ofNat 64 (RHOOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 RHOOUT) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 (RHOOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 MSG) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 (MSG + 8)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 (MSG + 16)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 (MSG + 24)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = SIG ∨ A = SIG + 8 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound blk_123 codeAt_123 s hpc (by simp [blk_123.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_123.res, E.eval]
  · simp [blk_123.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_123.res, SIG, DIG, RHOOUT, MSG]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_123.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG, DIG] at hn
    simp only [Result.toState_getMem, blk_123.res]
    t3n []
    repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign
end
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest HashOutput Cache Region Signature Selection sign signPayload signLayers
  privateMac privateNonce privateInput header digestSearch selections admissible attemptLimit buildFts frontier
  forestPk piecesSignature zero16)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
def payloadRest (cache : Cache) (rho : Digest) (output : HashOutput) : M (Option Signature) := do
  let index := output.toNat % 2^31
  let chosen := selections output
  let state ← (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
  let root ← forestPk index state.2.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)
theorem signPayload_eq (cache : Cache) (m : T3.Message) :
    signPayload cache m = privateNonce m >>= fun rho => digestSearch rho m 0 attemptLimit >>= fun r =>
      match r with
      | none => pure none
      | some (_, output) => payloadRest cache rho output := by
  unfold signPayload payloadRest
  congr 1; funext rho; congr 1; funext r
  rcases r with _ | ⟨_, output⟩ <;> rfl
theorem sign_eq (cache : Cache) (m : T3.Message) :
    sign cache m = privateMac cache.region >>= fun tag =>
      if tag ≠ cache.tag then pure none else signPayload cache m := by
  rfl
def FrontW (X : Nat) : Prop :=
  (TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64) ∨ (MACOUT ≤ X ∧ X < MACOUT + 32) ∨
    (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (RHOOUT ≤ X ∧ X < RHOOUT + 32) ∨
    (SIG ≤ X ∧ X < SIG + 16) ∨ (DIG ≤ X ∧ X < DIG + 64) ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨
    (SEL ≤ X ∧ X < SEL + 168) ∨ (0x70000 ≤ X ∧ X < 0x70040)
structure AfterDs (sk : SecretKey) (cache : Bytes 131072) (m : Message) (rho : Digest) (N : HashOutput)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 172
  x5 : t.getReg .x5 = 0
  adm : admissible (selections N) = true
  nbuf : OutAt t NBUF N
  sel : SelRows t N
  rho : DigAt t SIG rho
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  frame : Frame (sinit sk cache m) t FrontW
theorem AfterDs.base {sk : SecretKey} {cache : Bytes 131072} {m : Message} {rho : Digest} {N : HashOutput}
    {t : MachineState} (h : AfterDs sk cache m rho N t) : Base sk cache t := by
  refine ⟨h.x5, h.p0, h.p8, h.p32, h.p40, h.p48, h.p56, fun k hk => ?_, fun A hA hn => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.frame.get (by sg_omega) (by unfold FrontW; sg_omega), show REGION + 8 * k = CACHE + 8 * (k + 4) by sg_omega,
      sinit_cache sk cache m (k + 4) (by omega)]
  · unfold NeverW at hn
    rw [h.frame.get hA (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold SIGN_DATA; sg_omega) (by sg_omega)
  · exact (sinit_table sk cache m).frame h.frame (by
      intro i hi; unfold FrontW Search.TOP_DATA; sg_omega)
  · exact (sinit_cf sk cache m).frame h.frame (by
      intro i hi hi'; unfold FrontW Search.TOP_DATA; sg_omega)
  · exact (sinit_reward sk cache m).frame h.frame (by
      intro i hi hi'; unfold FrontW Search.TOP_DATA; sg_omega)
  · exact (sinit_zt sk cache m).frame h.frame (by
      intro r hr; simp only [Search.ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; unfold FrontW; sg_omega)
  · exact (sinit_t51 sk cache m).frame h.frame (by decide) (by decide) (by
      intro k hk; unfold FrontW; sg_omega)
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
theorem wordsOf_mac' (sk : BitVec 256) (region : Region) :
    wordsOf (privateInput sk (.inr (.inr region))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 3585, 0, sk.extractLsb' 128 64,
        sk.extractLsb' 192 64, 0, 0] ++ wordsOf (List.ofFn region) ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  have l1 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++ List.ofFn region).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length, List.length_ofFn, zero16, List.length_replicate]
  have l2 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length, zero16, List.length_replicate]
  have l3 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
      bytesLE 16 (sk.extractLsb' 128 128)).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length]
  have l4 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0)).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length]
  have l5 : (bytesLE 16 (sk.extractLsb' 0 128)).length % 8 = 0 := by simp only [bytesLE_length]
  rw [privateInput_mac_eq, wordsOf_append _ _ l1, wordsOf_append _ _ l2, wordsOf_append _ _ l3,
    wordsOf_append _ _ l4, wordsOf_append _ _ l5, wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE16,
    wordsOf_zero16, show List.replicate 32 (0 : UInt8) = List.replicate (8 * 4) 0 from rfl,
    wordsOf_replicate_zero, h1, h2, h3, h4]
  rfl
theorem cmp_chain (t : MachineState) (hpc : t.pc = pcOf 47) (a tag : BitVec 256)
    (ha : OutAt t MACOUT a) (ht : OutAt t TAG tag) :
    (a = tag → ∃ u, Steps image t 16 16 u ∧ u.pc = pcOf 63 ∧ RegsExcept t u [.x6, .x7, .x28, .x29] ∧
      Frame t u (fun _ => False)) ∧
    (a ≠ tag → ∃ u k c, Steps image t k c u ∧ c ≤ 16 ∧ u.pc = pcOf 543) := by
  have e : ∀ k < 4, (t.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = t.getMem (BitVec.ofNat 64 (TAG + 8 * k))) ↔
      a.extractLsb' (64 * k) 64 = tag.extractLsb' (64 * k) 64 := fun k hk => by rw [ha k hk, ht k hk]
  have hiff := bv256_eq_iff a tag
  obtain ⟨t1, s1, p1, x28, x29, r1, f1⟩ := blk47_spec t hpc
  have g : ∀ u, RegsExcept t u [.x6, .x7, .x28, .x29] → Frame t u (fun _ => False) →
      ∀ k < 4, (u.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = u.getMem (BitVec.ofNat 64 (TAG + 8 * k)) ↔
        a.extractLsb' (64 * k) 64 = tag.extractLsb' (64 * k) 64) := fun u _ hf k hk => by
    rw [hf.get (by sg_omega) (fun h => h), hf.get (by sg_omega) (fun h => h)]; exact e k hk
  have e0 := e 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at e0
  constructor
  · intro hat
    have h0 : a.extractLsb' 0 64 = tag.extractLsb' 0 64 := (hiff.1 hat).1
    rw [if_pos (e0.2 h0)] at p1
    have r1' : RegsExcept t t1 [.x6, .x7, .x28, .x29] := r1
    obtain ⟨t2, s2, p2, r2, f2⟩ := blk54_spec t1 p1 x28 x29
    rw [if_pos ((g t1 r1' f1 1 (by decide)).2 (hiff.1 hat).2.1)] at p2
    have r12 : RegsExcept t t2 [.x6, .x7, .x28, .x29] := (r1'.trans r2).mono (by decide)
    have f12 : Frame t t2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by simp_all)
    obtain ⟨t3, s3, p3, r3, f3⟩ := blk57_spec t2 p2 (by rw [r2.get (by decide), x28]) (by rw [r2.get (by decide), x29])
    rw [if_pos ((g t2 r12 f12 2 (by decide)).2 (hiff.1 hat).2.2.1)] at p3
    have r13 : RegsExcept t t3 [.x6, .x7, .x28, .x29] := (r12.trans r3).mono (by decide)
    have f13 : Frame t t3 (fun _ => False) := (f12.trans f3).mono (fun _ _ h => by simp_all)
    obtain ⟨t4, s4, p4, r4, f4⟩ := blk60_spec t3 p3 (by rw [r3.get (by decide), r2.get (by decide), x28])
      (by rw [r3.get (by decide), r2.get (by decide), x29])
    rw [if_pos ((g t3 r13 f13 3 (by decide)).2 (hiff.1 hat).2.2.2)] at p4
    exact ⟨t4, (s1.trans s2).trans (s3.trans s4), p4, (r13.trans r4).mono (by decide),
      (f13.trans f4).mono (fun _ _ h => by simp_all)⟩
  · intro hne
    have r1' : RegsExcept t t1 [.x6, .x7, .x28, .x29] := r1
    by_cases h0 : a.extractLsb' 0 64 = tag.extractLsb' 0 64
    · rw [if_pos (e0.2 h0)] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := blk54_spec t1 p1 x28 x29
      have r12 : RegsExcept t t2 [.x6, .x7, .x28, .x29] := (r1'.trans r2).mono (by decide)
      have f12 : Frame t t2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by simp_all)
      by_cases h1 : a.extractLsb' 64 64 = tag.extractLsb' 64 64
      · rw [if_pos ((g t1 r1' f1 1 (by decide)).2 h1)] at p2
        obtain ⟨t3, s3, p3, r3, f3⟩ := blk57_spec t2 p2 (by rw [r2.get (by decide), x28])
          (by rw [r2.get (by decide), x29])
        have r13 : RegsExcept t t3 [.x6, .x7, .x28, .x29] := (r12.trans r3).mono (by decide)
        have f13 : Frame t t3 (fun _ => False) := (f12.trans f3).mono (fun _ _ h => by simp_all)
        by_cases h2 : a.extractLsb' 128 64 = tag.extractLsb' 128 64
        · rw [if_pos ((g t2 r12 f12 2 (by decide)).2 h2)] at p3
          obtain ⟨t4, s4, p4, -, -⟩ := blk60_spec t3 p3 (by rw [r3.get (by decide), r2.get (by decide), x28])
            (by rw [r3.get (by decide), r2.get (by decide), x29])
          have h3 : ¬ a.extractLsb' 192 64 = tag.extractLsb' 192 64 := fun h3 => hne (hiff.2 ⟨h0, h1, h2, h3⟩)
          rw [if_neg (fun h => h3 ((g t3 r13 f13 3 (by decide)).1 h))] at p4
          exact ⟨t4, _, _, (s1.trans s2).trans (s3.trans s4), le_refl _, p4⟩
        · rw [if_neg (fun h => h2 ((g t2 r12 f12 2 (by decide)).1 h))] at p3
          exact ⟨t3, _, _, (s1.trans s2).trans s3, by norm_num, p3⟩
      · rw [if_neg (fun h => h1 ((g t1 r1' f1 1 (by decide)).1 h))] at p2
        exact ⟨t2, _, _, s1.trans s2, by norm_num, p2⟩
    · rw [if_neg (fun h => h0 (e0.1 h))] at p1
      exact ⟨t1, _, _, s1, by norm_num, p1⟩
def frontC : Nat := 17 + 2489875 + 1 + 16 + 59 + 8 * 2 + 30
theorem wordsOf_nonce (sk : BitVec 256) (m : T3.Message) :
    wordsOf (privateInput sk (.inr (.inl m))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 1793, 0, sk.extractLsb' 128 64,
        sk.extractLsb' 192 64, 0, 0, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64, 0, 0, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  rw [privateInput_nonce_eq, wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE16, wordsOf_zero16, wordsOf_bytesLE32,
    show List.replicate 32 (0 : UInt8) = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero, h1, h2, h3, h4]
  rfl
section front
variable {sk : SecretKey} {cache : Bytes 131072} {m : Message}
theorem sign_front (hK : DigestSearchSpec sk) {W : Nat} {Q : Option Signature → MachineState → Prop}
    (hfail : ∀ t, Failed t → Q none t)
    (hrest : ∀ rho N t, AfterDs sk cache m rho N t →
      TBSim image sk t W (payloadRest (cacheDec cache) rho N) Q) :
    TBSim image sk (sinit sk cache m) (frontC + dsCost + W) (sign (cacheDec cache) m) Q := by
  set s0 := sinit sk cache m with hs0
  obtain ⟨t1, st1, p1, x5, g0, g8, g16, g24, r1, f1⟩ := blk0_spec s0 (sinit_pc sk cache m)
  have e1 : ∀ X, X < 2 ^ 64 → ¬ ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) →
      t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h => f1.get hX h
  have hsk : FullCache.SkAt t1 sk := by
    intro j
    rw [e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j.val j.isLt
  have hregion : t1.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
    rw [frame_readWords f1 REGION 16380 (by decide) (fun i _ h => by sg_omega)]
    exact sinit_region sk cache m
  rw [sign_eq]
  refine TBSim.of_eq (W := 17 + (2489875 + (1 + (16 + (59 + (8 * 2 + (30 + (dsCost + W)))))))) ?_ rfl
    (by unfold frontC; ring)
  refine TBSim.steps st1 ?_
  refine TBSim.bind ((FullCache.mac_tsim true sk (cacheDec cache).region t1 p1 x5 hsk hregion).toTBSim (by decide))
    (fun a tm hm => ?_)
  obtain ⟨t2, stm, pcm, rm, fm⟩ := blk1432_spec tm hm.pc
  refine TBSim.steps stm ?_
  have t2x5 : t2.getReg .x5 = 0 := by rw [rm.get (by simp),hm.x5]
  have hwf : Frame t1 t2 (fun X => (PRIV ≤ X ∧ X < PRIV+64) ∨
      (0x70000 ≤ X ∧ X < 0x70040) ∨ (MACOUT ≤ X ∧ X < MACOUT+32)) :=
    (hm.frame.trans fm).mono (by
      intro X hX h; rcases h with h | h
      · exact h
      · exact h.elim)
  have ha : OutAt t2 MACOUT a := by
    have hw : t2.readWords (BitVec.ofNat 64 MACOUT) 4 = wordsOf (bytesLE 32 a) := by
      rw [frame_readWords fm MACOUT 4 (by decide) (by intro i hi h; exact h)]
      exact hm.words
    rw [show (4:Nat)=2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32] at hw
    simp only [List.cons_append,List.nil_append,List.cons.injEq] at hw
    intro k hk
    interval_cases k
    · exact hw.1
    · exact hw.2.1
    · exact hw.2.2.1
    · exact hw.2.2.2.1
  have ht : OutAt t2 TAG (cacheDec cache).tag := fun k hk => by
    rw [hwf.get (by sg_omega) (by sg_omega)]
    have := sinit_tag sk cache m k hk
    interval_cases k
    · rw [show TAG + 8 * 0 = TAG from rfl, g0]; exact this
    · rw [show TAG + 8 * 1 = TAG + 8 from rfl, g8]; exact this
    · rw [show TAG + 8 * 2 = TAG + 16 from rfl, g16]; exact this
    · rw [show TAG + 8 * 3 = TAG + 24 from rfl, g24]; exact this
  obtain ⟨heq, hne⟩ := cmp_chain t2 pcm a _ ha ht
  by_cases hat : a = (cacheDec cache).tag
  swap
  ·
    rw [if_pos hat]
    obtain ⟨u, k, c, su, hc, upc⟩ := hne hat
    obtain ⟨v, sv, hfv, -, -⟩ := fail_spec u upc
    exact TBSim.mono (TBSim.pure_steps (su.trans sv) (hfail v hfv)) (by omega) (fun _ _ h => h)
  rw [if_neg (not_not.2 hat)]
  obtain ⟨t3, st3, p3, r3, f3⟩ := heq hat
  refine TBSim.steps st3 ?_
  obtain ⟨t4, st4, p4, y10, y11, y12, q0, q8, q32, q40, q48, q56, n0, n8, n16, n24, n32, n40, n48, n56, n64, n72,
    n80, n88, r4, f4⟩ := blk63_spec t3 p3
  have f04 : Frame s0 t4 (fun X => ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) :=
    (((f1.trans hwf).trans f3).trans f4).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · exact Or.inl h
      · sg_omega
      · exact h.elim
      · sg_omega)
  have k : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j hj
  have mm : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_msg sk cache m j hj
  have x5' : t4.getReg .x5 = 0 := by
    rw [r4.get (by decide), r3.get (by decide), t2x5]
  have hv4 : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NONCE 128 RHOOUT y10 y11 y12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hq4 : hashInput t4 = toQ (privateInput sk (.inr (.inl m))) := by
    refine hashInput_toQ t4 _ 1 NONCE (by
      rw [privateInput_nonce_eq]; simp [bytesLE_length, SigGolfCandidate.T3.zero16]) y10 (by decide) (by decide)
      y11 (by decide) ?_
    rw [wordsOf_nonce, show 8 * (1 + 1) = 8 + 8 from rfl, readWords_add, readWords_eight, readWords_eight]
    have z : ∀ X, NONCE + 96 ≤ X → X < NONCE + 128 → t4.getMem (BitVec.ofNat 64 X) = 0 := fun X h1 h2 => by
      rw [f04.get (by sg_omega) (by sg_omega)]; exact sinit_zero sk cache m X (by unfold SIGN_DATA; sg_omega) (by sg_omega)
    rw [n0, n8, n16, n24, n32, n40, n48, n56, n64, n72, n80, n88, z _ (by sg_omega) (by sg_omega),
      z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega),
      show SK = SK + 8 * 0 from rfl, k 0 (by decide), k 1 (by decide), k 2 (by decide), k 3 (by decide),
      show MSG = MSG + 8 * 0 from rfl, mm 0 (by decide), mm 1 (by decide), mm 2 (by decide), mm 3 (by decide)]
    rfl
  refine TBSim.steps st4 ?_
  rw [signPayload_eq]
  refine TBSim.privateNonce_bind (W := 30 + (dsCost + W)) (fetch_122 t4 p4) x5' hv4 hq4 (fun b => ?_)
  set t5 := writeHash t4 b
  have hwf5 := Frame.writeHash t4 b RHOOUT y12 (by decide)
  have hrho : DigAt t5 RHOOUT (b.extractLsb' 0 128) := DigAt.writeHash_lo t4 b RHOOUT y12 (by decide)
  obtain ⟨t6, st6, p6, x19, s0', s8', d0, d8, d32, d40, d48, d56, r6, f6⟩ :=
    blk123_spec t5 (by rw [pc_writeHash, p4, pcOf_add4])
  have mm5 : ∀ j < 4, t5.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [hwf5.get (by sg_omega) (by sg_omega), f4.get (by sg_omega) (by sg_omega)]; exact mm j hj
  have hpre : DsPre t6 (b.extractLsb' 0 128) m :=
    { pc := p6
      x5 := by rw [r6.get (by decide), getReg_writeHash, x5']
      x19 := x19
      rho := ⟨by rw [d0]; exact hrho.1, by rw [d8]; exact hrho.2⟩
      msg := fun k hk => by
        interval_cases k
        · rw [show DIG + 32 + 8 * 0 = DIG + 32 from rfl, d32]; exact mm5 0 (by decide)
        · rw [show DIG + 32 + 8 * 1 = DIG + 40 from rfl, d40]; exact mm5 1 (by decide)
        · rw [show DIG + 32 + 8 * 2 = DIG + 48 from rfl, d48]; exact mm5 2 (by decide)
        · rw [show DIG + 32 + 8 * 3 = DIG + 56 from rfl, d56]; exact mm5 3 (by decide) }
  refine TBSim.steps st6 (TBSim.bind (hK t6 _ m hpre) (fun r u hu => ?_))
  rcases r with _ | ⟨ctr, N⟩
  · exact TBSim.mono (TBSim.pure (hfail u hu)) (by omega) (fun _ _ h => h)
  obtain ⟨upc, ux5, uadm, unb, usel, ur, uf⟩ := hu
  refine hrest _ N u ?_
  have f06 : Frame s0 t6 (fun X => (((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) ∨
      (RHOOUT ≤ X ∧ X < RHOOUT + 32) ∨ (SIG ≤ X ∧ X < SIG + 16) ∨ (DIG ≤ X ∧ X < DIG + 64)) :=
    ((f04.trans hwf5).trans f6).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · sg_omega)
  have g6 : ∀ X, X < 2 ^ 64 → ¬ DsW X → u.getMem (BitVec.ofNat 64 X) = t6.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => uf.get hX h
  have nDs : ∀ X, (X < DIG + 16 ∨ (DIG + 32 ≤ X ∧ X < NBUF)) → ¬ DsW X := fun X hX h => by
    unfold DsW at h; sg_omega
  have pv : ∀ X, X < 2 ^ 64 → (PRIV ≤ X ∧ X < PRIV + 64) → u.getMem (BitVec.ofNat 64 X) =
      t4.getMem (BitVec.ofNat 64 X) := fun X hX h => by
    rw [g6 X hX (nDs X (by sg_omega)), f6.get hX (by sg_omega), hwf5.get hX (by sg_omega)]
  exact
    { pc := upc
      x5 := ux5
      adm := uadm
      nbuf := unb
      sel := usel
      rho := ⟨by rw [g6 _ (by sg_omega) (nDs _ (by sg_omega)), s0']; exact hrho.1,
        by rw [g6 _ (by sg_omega) (nDs _ (by sg_omega)), s8']; exact hrho.2⟩
      p0 := by rw [pv _ (by sg_omega) (by sg_omega), q0, k 0 (by decide)]
      p8 := by rw [pv _ (by sg_omega) (by sg_omega), q8]; exact k 1 (by decide)
      p32 := by rw [pv _ (by sg_omega) (by sg_omega), q32]; exact k 2 (by decide)
      p40 := by rw [pv _ (by sg_omega) (by sg_omega), q40]; exact k 3 (by decide)
      p48 := by rw [pv _ (by sg_omega) (by sg_omega), q48]
      p56 := by rw [pv _ (by sg_omega) (by sg_omega), q56]
      frame := (f06.trans uf).mono (fun X _ h => by unfold FrontW; unfold DsW at h; sg_omega) }
end front
end SigGolfCandidate.T3M.Sign
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest HashOutput Cache Region Signature Selection sign signPayload signLayers
  privateMac privateNonce privateInput header digestSearch selections admissible attemptLimit buildFts frontier
  forestPk piecesSignature zero16)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
structure NoncePost (sk : SecretKey) (cache : Bytes 131072) (m : Message) (rho : Digest)
    (t : MachineState) : Prop where
  search : DsPre t rho m
  rho : DigAt t SIG rho
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  frame : Frame (sinit sk cache m) t FrontW
theorem nonce_front {sk : SecretKey} {cache : Bytes 131072} {m : Message}
    {α : Type} {W : Nat} {Q : Option α → MachineState → Prop}
    (K : Digest → M (Option α))
    (hfail : ∀ t, Failed t → Q none t)
    (hrest : ∀ rho t, NoncePost sk cache m rho t → TBSim image sk t W (K rho) Q) :
    TBSim image sk (sinit sk cache m) (frontC + W) (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= K) Q := by
  set s0 := sinit sk cache m with hs0
  obtain ⟨t1, st1, p1, x5, g0, g8, g16, g24, r1, f1⟩ := blk0_spec s0 (sinit_pc sk cache m)
  have e1 : ∀ X, X < 2 ^ 64 → ¬ ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) →
      t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h => f1.get hX h
  have hsk : FullCache.SkAt t1 sk := by
    intro j
    rw [e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j.val j.isLt
  have hregion : t1.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
    rw [frame_readWords f1 REGION 16380 (by decide) (fun i _ h => by sg_omega)]
    exact sinit_region sk cache m
  refine TBSim.of_eq (W := 17 + (2489875 + (1 + (16 + (59 + (8 * 2 + (30 + W))))))) ?_ rfl
    (by unfold frontC; ring)
  refine TBSim.steps st1 ?_
  refine TBSim.bind ((FullCache.mac_tsim true sk (cacheDec cache).region t1 p1 x5 hsk hregion).toTBSim (by decide))
    (fun a tm hm => ?_)
  obtain ⟨t2, stm, pcm, rm, fm⟩ := blk1432_spec tm hm.pc
  refine TBSim.steps stm ?_
  have t2x5 : t2.getReg .x5 = 0 := by rw [rm.get (by simp),hm.x5]
  have hwf : Frame t1 t2 (fun X => (PRIV ≤ X ∧ X < PRIV+64) ∨
      (0x70000 ≤ X ∧ X < 0x70040) ∨ (MACOUT ≤ X ∧ X < MACOUT+32)) :=
    (hm.frame.trans fm).mono (by
      intro X hX h; rcases h with h | h
      · exact h
      · exact h.elim)
  have ha : OutAt t2 MACOUT a := by
    have hw : t2.readWords (BitVec.ofNat 64 MACOUT) 4 = wordsOf (bytesLE 32 a) := by
      rw [frame_readWords fm MACOUT 4 (by decide) (by intro i hi h; exact h)]
      exact hm.words
    rw [show (4:Nat)=2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32] at hw
    simp only [List.cons_append,List.nil_append,List.cons.injEq] at hw
    intro k hk
    interval_cases k
    · exact hw.1
    · exact hw.2.1
    · exact hw.2.2.1
    · exact hw.2.2.2.1
  have ht : OutAt t2 TAG (cacheDec cache).tag := fun k hk => by
    rw [hwf.get (by sg_omega) (by sg_omega)]
    have := sinit_tag sk cache m k hk
    interval_cases k
    · rw [show TAG + 8 * 0 = TAG from rfl, g0]; exact this
    · rw [show TAG + 8 * 1 = TAG + 8 from rfl, g8]; exact this
    · rw [show TAG + 8 * 2 = TAG + 16 from rfl, g16]; exact this
    · rw [show TAG + 8 * 3 = TAG + 24 from rfl, g24]; exact this
  obtain ⟨heq, hne⟩ := cmp_chain t2 pcm a _ ha ht
  by_cases hat : a = (cacheDec cache).tag
  swap
  ·
    rw [if_pos hat]
    obtain ⟨u, k, c, su, hc, upc⟩ := hne hat
    obtain ⟨v, sv, hfv, -, -⟩ := fail_spec u upc
    exact TBSim.mono (TBSim.pure_steps (su.trans sv) (hfail v hfv)) (by omega) (fun _ _ h => h)
  rw [if_neg (not_not.2 hat)]
  obtain ⟨t3, st3, p3, r3, f3⟩ := heq hat
  refine TBSim.steps st3 ?_
  obtain ⟨t4, st4, p4, y10, y11, y12, q0, q8, q32, q40, q48, q56, n0, n8, n16, n24, n32, n40, n48, n56, n64, n72,
    n80, n88, r4, f4⟩ := blk63_spec t3 p3
  have f04 : Frame s0 t4 (fun X => ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) :=
    (((f1.trans hwf).trans f3).trans f4).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · exact Or.inl h
      · sg_omega
      · exact h.elim
      · sg_omega)
  have k : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j hj
  have mm : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_msg sk cache m j hj
  have x5' : t4.getReg .x5 = 0 := by
    rw [r4.get (by decide), r3.get (by decide), t2x5]
  have hv4 : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NONCE 128 RHOOUT y10 y11 y12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hq4 : hashInput t4 = toQ (privateInput sk (.inr (.inl m))) := by
    refine hashInput_toQ t4 _ 1 NONCE (by
      rw [privateInput_nonce_eq]; simp [bytesLE_length, SigGolfCandidate.T3.zero16]) y10 (by decide) (by decide)
      y11 (by decide) ?_
    rw [wordsOf_nonce, show 8 * (1 + 1) = 8 + 8 from rfl, readWords_add, readWords_eight, readWords_eight]
    have z : ∀ X, NONCE + 96 ≤ X → X < NONCE + 128 → t4.getMem (BitVec.ofNat 64 X) = 0 := fun X h1 h2 => by
      rw [f04.get (by sg_omega) (by sg_omega)]; exact sinit_zero sk cache m X (by unfold SIGN_DATA; sg_omega) (by sg_omega)
    rw [n0, n8, n16, n24, n32, n40, n48, n56, n64, n72, n80, n88, z _ (by sg_omega) (by sg_omega),
      z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega),
      show SK = SK + 8 * 0 from rfl, k 0 (by decide), k 1 (by decide), k 2 (by decide), k 3 (by decide),
      show MSG = MSG + 8 * 0 from rfl, mm 0 (by decide), mm 1 (by decide), mm 2 (by decide), mm 3 (by decide)]
    rfl
  refine TBSim.steps st4 ?_
  refine TBSim.privateNonce_bind (W := 30 + W) (fetch_122 t4 p4) x5' hv4 hq4 (fun b => ?_)
  set t5 := writeHash t4 b
  have hwf5 := Frame.writeHash t4 b RHOOUT y12 (by decide)
  have hrho : DigAt t5 RHOOUT (b.extractLsb' 0 128) := DigAt.writeHash_lo t4 b RHOOUT y12 (by decide)
  obtain ⟨t6, st6, p6, x19, s0', s8', d0, d8, d32, d40, d48, d56, r6, f6⟩ :=
    blk123_spec t5 (by rw [pc_writeHash, p4, pcOf_add4])
  have mm5 : ∀ j < 4, t5.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [hwf5.get (by sg_omega) (by sg_omega), f4.get (by sg_omega) (by sg_omega)]; exact mm j hj
  have hpre : DsPre t6 (b.extractLsb' 0 128) m :=
    { pc := p6
      x5 := by rw [r6.get (by decide), getReg_writeHash, x5']
      x19 := x19
      rho := ⟨by rw [d0]; exact hrho.1, by rw [d8]; exact hrho.2⟩
      msg := fun k hk => by
        interval_cases k
        · rw [show DIG + 32 + 8 * 0 = DIG + 32 from rfl, d32]; exact mm5 0 (by decide)
        · rw [show DIG + 32 + 8 * 1 = DIG + 40 from rfl, d40]; exact mm5 1 (by decide)
        · rw [show DIG + 32 + 8 * 2 = DIG + 48 from rfl, d48]; exact mm5 2 (by decide)
        · rw [show DIG + 32 + 8 * 3 = DIG + 56 from rfl, d56]; exact mm5 3 (by decide) }
  have f06 : Frame s0 t6 (fun X => (((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) ∨
      (RHOOUT ≤ X ∧ X < RHOOUT + 32) ∨ (SIG ≤ X ∧ X < SIG + 16) ∨ (DIG ≤ X ∧ X < DIG + 64)) :=
    ((f04.trans hwf5).trans f6).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · sg_omega)
  refine TBSim.steps st6 (hrest _ t6 ?_)
  refine ⟨hpre, ⟨by rw [s0']; exact hrho.1, by rw [s8']; exact hrho.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q0, k 0 (by decide)]
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q8]; exact k 1 (by decide)
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q32]; exact k 2 (by decide)
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q40]; exact k 3 (by decide)
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q48]
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q56]
  · exact f06.mono (fun X _ h => by unfold FrontW; sg_omega)
theorem NoncePost.base {sk : SecretKey} {cache : Bytes 131072} {m : Message} {rho : Digest}
    {t : MachineState} (h : NoncePost sk cache m rho t) : Base sk cache t := by
  refine ⟨h.search.x5, h.p0, h.p8, h.p32, h.p40, h.p48, h.p56, fun k hk => ?_, fun A hA hn => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.frame.get (by sg_omega) (by unfold FrontW; sg_omega), show REGION + 8 * k = CACHE + 8 * (k + 4) by sg_omega,
      sinit_cache sk cache m (k + 4) (by omega)]
  · unfold NeverW at hn
    rw [h.frame.get hA (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold SIGN_DATA; sg_omega) (by sg_omega)
  · exact (sinit_table sk cache m).frame h.frame (by
      intro i hi; unfold FrontW Search.TOP_DATA; sg_omega)
  · exact (sinit_cf sk cache m).frame h.frame (by
      intro i hi hi'; unfold FrontW Search.TOP_DATA; sg_omega)
  · exact (sinit_reward sk cache m).frame h.frame (by
      intro i hi hi'; unfold FrontW Search.TOP_DATA; sg_omega)
  · exact (sinit_zt sk cache m).frame h.frame (by
      intro r hr; simp only [Search.ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; unfold FrontW; sg_omega)
  · exact (sinit_t51 sk cache m).frame h.frame (by decide) (by decide) (by
      intro k hk; unfold FrontW; sg_omega)
end SigGolfCandidate.T3M.Sign.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- Nested FTS (r1-1): the encoding R slot `ENC + 48` now carries `R8` (written by the FTS phase), so it is no
longer part of the invariant. -/
def Inv (sk : SecretKey) (cache : Bytes 131072) (t : MachineState) : Prop :=
  Base sk cache t ∧ t.getMem (BitVec.ofNat 64 (ENC + 32)) = 0
def NewWrites (A : Nat) : Prop :=
  (A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV) ∨
  (0x50000 ≤ A ∧ A < 0x52010) ∨ (SIG + 16 ≤ A ∧ A < SIG + 1888) ∨
  (FOUT ≤ A ∧ A < FOUT + 32) ∨ (ENC + 48 ≤ A ∧ A < ENC + 64)
theorem NoncePost.inv {sk : SecretKey} {cache : Bytes 131072} {m : Message}
    {rho : SigGolfCandidate.T3.Digest} {t : MachineState}
    (h : NoncePost sk cache m rho t) : Inv sk cache t := by
  refine ⟨h.base, ?_⟩
  rw [h.frame.get (by sg_omega) (by unfold FrontW; sg_omega)]
  exact sinit_zero sk cache m (ENC + 32) (by unfold SIGN_DATA; sg_omega) (by sg_omega)
theorem Inv.stable {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState}
    {regs : List Reg} (h : Inv sk cache t) (hf : Frame t u NewWrites)
    (hr : RegsExcept t u regs) (h5 : Reg.x5 ∉ regs) : Inv sk cache u := by
  refine ⟨h.1.frame hf hr h5 ?_, ?_⟩
  · intro A hA hb hw
    unfold BaseA NeverW Search.TOP_DATA at hb
    unfold NewWrites at hw
    sg_omega
  · rw [hf.get (by sg_omega) (by unfold NewWrites; sg_omega)]
    exact h.2
end SigGolfCandidate.T3M.Sign.Boundary
end

namespace SigGolfCandidate.T3M.Sign.Boundary.Generic
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest HashOutput Cache Region Signature Selection sign signPayload signLayers privateMac privateNonce privateInput header digestSearch selections admissible attemptLimit buildFts frontier forestPk piecesSignature zero16)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
structure FrontCodeAt (im : Image) : Prop where
  seg0 : CodeAt im (pcOf 0) seg_0
  seg1432 : CodeAt im (pcOf 1432) seg_1432
  seg47 : CodeAt im (pcOf 47) seg_47
  seg54 : CodeAt im (pcOf 54) seg_54
  seg57 : CodeAt im (pcOf 57) seg_57
  seg60 : CodeAt im (pcOf 60) seg_60
  seg63 : CodeAt im (pcOf 63) seg_63
  seg122 : CodeAt im (pcOf 122) seg_122
  seg123 : CodeAt im (pcOf 123) seg_123
  seg543 : CodeAt im (pcOf 543) seg_543
theorem blk0_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 0) :
    ∃ t, Steps im s 17 17 t ∧ t.pc = pcOf 1227 ∧ t.getReg .x5 = 0 ∧
      t.getMem (BitVec.ofNat 64 TAG) = s.getMem (BitVec.ofNat 64 CACHE) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 8)) = s.getMem (BitVec.ofNat 64 (CACHE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 16)) = s.getMem (BitVec.ofNat 64 (CACHE + 16)) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 24)) = s.getMem (BitVec.ofNat 64 (CACHE + 24)) ∧
      RegsExcept s t [.x5, .x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => (TAG ≤ A ∧ A < TAG + 32) ∨ (MACBLK ≤ A ∧ A < MACBLK + 64)) := by
  refine ⟨_, symRun_sound blk_0 hc.seg0 s hpc (by simp [blk_0.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_0.res, E.eval]
  · simp [blk_0.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_0.res, TAG, CACHE, MACBLK, SK]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_0.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TAG, MACBLK] at hn
    simp only [Result.toState_getMem, blk_0.res]
    t3n []
    repeat rw [if_neg (by omega)]
theorem blk1432_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 1432) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 47 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1432 hc.seg1432 s hpc (by simp [blk_1432.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [blk_1432.res, E.eval]
  · intro r hr; cases r <;> simp [blk_1432.res, rv_simp] <;> rfl
  · intro A hA hn; simp [blk_1432.res, rv_simp]
theorem blk47_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 47) :
    ∃ t, Steps im s 7 7 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 MACOUT) = s.getMem (BitVec.ofNat 64 TAG) then pcOf 54
        else pcOf 543) ∧
      t.getReg .x28 = BitVec.ofNat 64 MACOUT ∧ t.getReg .x29 = BitVec.ofNat 64 TAG ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_47 hc.seg47 s hpc (by simp [blk_47.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_47.res, E.eval, CmpOp.eval, MACOUT, TAG]
    t3n []
    split_ifs <;> simp_all
  · simp [blk_47.res, rv_simp]
  · simp [blk_47.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_47.res, rv_simp]
theorem cmp_next_spec (im : Image) {a k : Nat} {seg : List (BitVec 32)} {r : Result}
    (hc : CodeAt im (pcOf a) seg) (hrun : symRun { noAlias := true } seg (pcOf a) 100 = some r)
    (s : MachineState) (hpc : s.pc = pcOf a)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG)
    (hobl : r.obligs s)
    (hpcE : (r.toState s).pc = if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (TAG + 8 * k)) then pcOf (a + 3) else pcOf 543)
    (hregs : RegsExcept s (r.toState s) [.x6, .x7]) (hfr : Frame s (r.toState s) (fun _ => False)) :
    ∃ t, Steps im s r.steps r.cycles t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * k))
        then pcOf (a + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  ⟨_, symRun_sound hrun hc s hpc hobl, hpcE, hregs, hfr⟩
theorem blk54_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 54)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 1)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 1))
        then pcOf (54 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec im hc.seg54 blk_54 s hpc h28 h29 (by simp only [blk_54.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_54.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_54.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_54.res, rv_simp])
theorem blk57_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 57)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 2)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 2))
        then pcOf (57 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec im hc.seg57 blk_57 s hpc h28 h29 (by simp only [blk_57.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_57.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_57.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_57.res, rv_simp])
theorem blk60_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 60)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 3)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 3))
        then pcOf (60 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec im hc.seg60 blk_60 s hpc h28 h29 (by simp only [blk_60.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_60.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_60.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_60.res, rv_simp])
theorem blk63_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 63) :
    ∃ t, Steps im s 59 59 t ∧ t.pc = pcOf 122 ∧
      t.getReg .x10 = BitVec.ofNat 64 NONCE ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 RHOOUT ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem (BitVec.ofNat 64 SK) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 8)) = s.getMem (BitVec.ofNat 64 (SK + 8)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 32)) = s.getMem (BitVec.ofNat 64 (SK + 16)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 40)) = s.getMem (BitVec.ofNat 64 (SK + 24)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0 ∧
      t.getMem (BitVec.ofNat 64 NONCE) = s.getMem (BitVec.ofNat 64 SK) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 8)) = s.getMem (BitVec.ofNat 64 (SK + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 16)) = BitVec.ofNat 64 1793 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 32)) = s.getMem (BitVec.ofNat 64 (SK + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 40)) = s.getMem (BitVec.ofNat 64 (SK + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (NONCE + 56)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 64)) = s.getMem (BitVec.ofNat 64 MSG) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 72)) = s.getMem (BitVec.ofNat 64 (MSG + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 80)) = s.getMem (BitVec.ofNat 64 (MSG + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 88)) = s.getMem (BitVec.ofNat 64 (MSG + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨
        A = PRIV + 56 ∨ (NONCE ≤ A ∧ A < NONCE + 96)) := by
  refine ⟨_, symRun_sound blk_63 hc.seg63 s hpc (by simp [blk_63.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_63.res, E.eval]
  · simp [blk_63.res, rv_simp]
  · simp [blk_63.res, rv_simp]
  · simp [blk_63.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_63.res, PRIV, NONCE, SK, MSG]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_63.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV, NONCE] at hn
    simp only [Result.toState_getMem, blk_63.res]
    t3n []
    repeat rw [if_neg (by omega)]
theorem fetch_122 (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 122) : fetch im s = some (.base .ECALL) :=
  (hc.seg122.fetch s hpc).trans rfl
theorem blk123_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 123) :
    ∃ t, Steps im s 30 30 t ∧ t.pc = pcOf 153 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 SIG) = s.getMem (BitVec.ofNat 64 RHOOUT) ∧
      t.getMem (BitVec.ofNat 64 (SIG + 8)) = s.getMem (BitVec.ofNat 64 (RHOOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 RHOOUT) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 (RHOOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 MSG) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 (MSG + 8)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 (MSG + 16)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 (MSG + 24)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = SIG ∨ A = SIG + 8 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound blk_123 hc.seg123 s hpc (by simp [blk_123.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_123.res, E.eval]
  · simp [blk_123.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_123.res, SIG, DIG, RHOOUT, MSG]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_123.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG, DIG] at hn
    simp only [Result.toState_getMem, blk_123.res]
    t3n []
    repeat rw [if_neg (by omega)]
theorem cmp_chain (im : Image) (hc : FrontCodeAt im) (t : MachineState) (hpc : t.pc = pcOf 47) (a tag : BitVec 256)
    (ha : OutAt t MACOUT a) (ht : OutAt t TAG tag) :
    (a = tag → ∃ u, Steps im t 16 16 u ∧ u.pc = pcOf 63 ∧ RegsExcept t u [.x6, .x7, .x28, .x29] ∧
      Frame t u (fun _ => False)) ∧
    (a ≠ tag → ∃ u k c, Steps im t k c u ∧ c ≤ 16 ∧ u.pc = pcOf 543) := by
  have e : ∀ k < 4, (t.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = t.getMem (BitVec.ofNat 64 (TAG + 8 * k))) ↔
      a.extractLsb' (64 * k) 64 = tag.extractLsb' (64 * k) 64 := fun k hk => by rw [ha k hk, ht k hk]
  have hiff := bv256_eq_iff a tag
  obtain ⟨t1, s1, p1, x28, x29, r1, f1⟩ := blk47_spec im hc t hpc
  have g : ∀ u, RegsExcept t u [.x6, .x7, .x28, .x29] → Frame t u (fun _ => False) →
      ∀ k < 4, (u.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = u.getMem (BitVec.ofNat 64 (TAG + 8 * k)) ↔
        a.extractLsb' (64 * k) 64 = tag.extractLsb' (64 * k) 64) := fun u _ hf k hk => by
    rw [hf.get (by sg_omega) (fun h => h), hf.get (by sg_omega) (fun h => h)]; exact e k hk
  have e0 := e 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at e0
  constructor
  · intro hat
    have h0 : a.extractLsb' 0 64 = tag.extractLsb' 0 64 := (hiff.1 hat).1
    rw [if_pos (e0.2 h0)] at p1
    have r1' : RegsExcept t t1 [.x6, .x7, .x28, .x29] := r1
    obtain ⟨t2, s2, p2, r2, f2⟩ := blk54_spec im hc t1 p1 x28 x29
    rw [if_pos ((g t1 r1' f1 1 (by decide)).2 (hiff.1 hat).2.1)] at p2
    have r12 : RegsExcept t t2 [.x6, .x7, .x28, .x29] := (r1'.trans r2).mono (by decide)
    have f12 : Frame t t2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by simp_all)
    obtain ⟨t3, s3, p3, r3, f3⟩ := blk57_spec im hc t2 p2 (by rw [r2.get (by decide), x28]) (by rw [r2.get (by decide), x29])
    rw [if_pos ((g t2 r12 f12 2 (by decide)).2 (hiff.1 hat).2.2.1)] at p3
    have r13 : RegsExcept t t3 [.x6, .x7, .x28, .x29] := (r12.trans r3).mono (by decide)
    have f13 : Frame t t3 (fun _ => False) := (f12.trans f3).mono (fun _ _ h => by simp_all)
    obtain ⟨t4, s4, p4, r4, f4⟩ := blk60_spec im hc t3 p3 (by rw [r3.get (by decide), r2.get (by decide), x28])
      (by rw [r3.get (by decide), r2.get (by decide), x29])
    rw [if_pos ((g t3 r13 f13 3 (by decide)).2 (hiff.1 hat).2.2.2)] at p4
    exact ⟨t4, (s1.trans s2).trans (s3.trans s4), p4, (r13.trans r4).mono (by decide),
      (f13.trans f4).mono (fun _ _ h => by simp_all)⟩
  · intro hne
    have r1' : RegsExcept t t1 [.x6, .x7, .x28, .x29] := r1
    by_cases h0 : a.extractLsb' 0 64 = tag.extractLsb' 0 64
    · rw [if_pos (e0.2 h0)] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := blk54_spec im hc t1 p1 x28 x29
      have r12 : RegsExcept t t2 [.x6, .x7, .x28, .x29] := (r1'.trans r2).mono (by decide)
      have f12 : Frame t t2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by simp_all)
      by_cases h1 : a.extractLsb' 64 64 = tag.extractLsb' 64 64
      · rw [if_pos ((g t1 r1' f1 1 (by decide)).2 h1)] at p2
        obtain ⟨t3, s3, p3, r3, f3⟩ := blk57_spec im hc t2 p2 (by rw [r2.get (by decide), x28])
          (by rw [r2.get (by decide), x29])
        have r13 : RegsExcept t t3 [.x6, .x7, .x28, .x29] := (r12.trans r3).mono (by decide)
        have f13 : Frame t t3 (fun _ => False) := (f12.trans f3).mono (fun _ _ h => by simp_all)
        by_cases h2 : a.extractLsb' 128 64 = tag.extractLsb' 128 64
        · rw [if_pos ((g t2 r12 f12 2 (by decide)).2 h2)] at p3
          obtain ⟨t4, s4, p4, -, -⟩ := blk60_spec im hc t3 p3 (by rw [r3.get (by decide), r2.get (by decide), x28])
            (by rw [r3.get (by decide), r2.get (by decide), x29])
          have h3 : ¬ a.extractLsb' 192 64 = tag.extractLsb' 192 64 := fun h3 => hne (hiff.2 ⟨h0, h1, h2, h3⟩)
          rw [if_neg (fun h => h3 ((g t3 r13 f13 3 (by decide)).1 h))] at p4
          exact ⟨t4, _, _, (s1.trans s2).trans (s3.trans s4), le_refl _, p4⟩
        · rw [if_neg (fun h => h2 ((g t2 r12 f12 2 (by decide)).1 h))] at p3
          exact ⟨t3, _, _, (s1.trans s2).trans s3, by norm_num, p3⟩
      · rw [if_neg (fun h => h1 ((g t1 r1' f1 1 (by decide)).1 h))] at p2
        exact ⟨t2, _, _, s1.trans s2, by norm_num, p2⟩
    · rw [if_neg (fun h => h0 (e0.1 h))] at p1
      exact ⟨t1, _, _, s1, by norm_num, p1⟩
theorem fail_spec (im : Image) (hc : FrontCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 543) :
    ∃ t, Steps im s 2 2 t ∧ Failed t ∧ RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_543 hc.seg543 s hpc (by simp [blk_543.res, rv_simp]), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [blk_543.res, E.eval]
  · simp [blk_543.res, rv_simp]
  · simp [blk_543.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_543.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_543.res, rv_simp]
theorem nonce_front (im : Image) (hc : FrontCodeAt im) (hmcode : FullCache.Generic.MacCodeAt im true) {sk : SecretKey} {cache : Bytes 131072} {m : Message}
    {α : Type} {W : Nat} {Q : Option α → MachineState → Prop}
    (K : Digest → M (Option α))
    (hfail : ∀ t, Failed t → Q none t)
    (hrest : ∀ rho t, NoncePost sk cache m rho t → TBSim im sk t W (K rho) Q) :
    TBSim im sk (sinit sk cache m) (frontC + W) (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= K) Q := by
  set s0 := sinit sk cache m with hs0
  obtain ⟨t1, st1, p1, x5, g0, g8, g16, g24, r1, f1⟩ := blk0_spec im hc s0 (sinit_pc sk cache m)
  have e1 : ∀ X, X < 2 ^ 64 → ¬ ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) →
      t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h => f1.get hX h
  have hsk : FullCache.SkAt t1 sk := by
    intro j
    rw [e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j.val j.isLt
  have hregion : t1.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
    rw [frame_readWords f1 REGION 16380 (by decide) (fun i _ h => by sg_omega)]
    exact sinit_region sk cache m
  refine TBSim.of_eq (W := 17 + (2489875 + (1 + (16 + (59 + (8 * 2 + (30 + W))))))) ?_ rfl
    (by unfold frontC; ring)
  refine TBSim.steps st1 ?_
  refine TBSim.bind ((FullCache.Generic.mac_tsim true im hmcode sk (cacheDec cache).region t1 p1 x5 hsk hregion).toTBSim (by decide))
    (fun a tm hm => ?_)
  obtain ⟨t2, stm, pcm, rm, fm⟩ := blk1432_spec im hc tm hm.pc
  refine TBSim.steps stm ?_
  have t2x5 : t2.getReg .x5 = 0 := by rw [rm.get (by simp),hm.x5]
  have hwf : Frame t1 t2 (fun X => (PRIV ≤ X ∧ X < PRIV+64) ∨
      (0x70000 ≤ X ∧ X < 0x70040) ∨ (MACOUT ≤ X ∧ X < MACOUT+32)) :=
    (hm.frame.trans fm).mono (by
      intro X hX h; rcases h with h | h
      · exact h
      · exact h.elim)
  have ha : OutAt t2 MACOUT a := by
    have hw : t2.readWords (BitVec.ofNat 64 MACOUT) 4 = wordsOf (bytesLE 32 a) := by
      rw [frame_readWords fm MACOUT 4 (by decide) (by intro i hi h; exact h)]
      exact hm.words
    rw [show (4:Nat)=2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32] at hw
    simp only [List.cons_append,List.nil_append,List.cons.injEq] at hw
    intro k hk
    interval_cases k
    · exact hw.1
    · exact hw.2.1
    · exact hw.2.2.1
    · exact hw.2.2.2.1
  have ht : OutAt t2 TAG (cacheDec cache).tag := fun k hk => by
    rw [hwf.get (by sg_omega) (by sg_omega)]
    have := sinit_tag sk cache m k hk
    interval_cases k
    · rw [show TAG + 8 * 0 = TAG from rfl, g0]; exact this
    · rw [show TAG + 8 * 1 = TAG + 8 from rfl, g8]; exact this
    · rw [show TAG + 8 * 2 = TAG + 16 from rfl, g16]; exact this
    · rw [show TAG + 8 * 3 = TAG + 24 from rfl, g24]; exact this
  obtain ⟨heq, hne⟩ := cmp_chain im hc t2 pcm a _ ha ht
  by_cases hat : a = (cacheDec cache).tag
  swap
  ·
    rw [if_pos hat]
    obtain ⟨u, k, c, su, hcycles, upc⟩ := hne hat
    obtain ⟨v, sv, hfv, -, -⟩ := fail_spec im hc u upc
    exact TBSim.mono (TBSim.pure_steps (su.trans sv) (hfail v hfv)) (by omega) (fun _ _ h => h)
  rw [if_neg (not_not.2 hat)]
  obtain ⟨t3, st3, p3, r3, f3⟩ := heq hat
  refine TBSim.steps st3 ?_
  obtain ⟨t4, st4, p4, y10, y11, y12, q0, q8, q32, q40, q48, q56, n0, n8, n16, n24, n32, n40, n48, n56, n64, n72,
    n80, n88, r4, f4⟩ := blk63_spec im hc t3 p3
  have f04 : Frame s0 t4 (fun X => ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) :=
    (((f1.trans hwf).trans f3).trans f4).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · exact Or.inl h
      · sg_omega
      · exact h.elim
      · sg_omega)
  have k : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j hj
  have mm : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_msg sk cache m j hj
  have x5' : t4.getReg .x5 = 0 := by
    rw [r4.get (by decide), r3.get (by decide), t2x5]
  have hv4 : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NONCE 128 RHOOUT y10 y11 y12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hq4 : hashInput t4 = toQ (privateInput sk (.inr (.inl m))) := by
    refine hashInput_toQ t4 _ 1 NONCE (by
      rw [privateInput_nonce_eq]; simp [bytesLE_length, SigGolfCandidate.T3.zero16]) y10 (by decide) (by decide)
      y11 (by decide) ?_
    rw [wordsOf_nonce, show 8 * (1 + 1) = 8 + 8 from rfl, readWords_add, readWords_eight, readWords_eight]
    have z : ∀ X, NONCE + 96 ≤ X → X < NONCE + 128 → t4.getMem (BitVec.ofNat 64 X) = 0 := fun X h1 h2 => by
      rw [f04.get (by sg_omega) (by sg_omega)]; exact sinit_zero sk cache m X (by unfold SIGN_DATA; sg_omega) (by sg_omega)
    rw [n0, n8, n16, n24, n32, n40, n48, n56, n64, n72, n80, n88, z _ (by sg_omega) (by sg_omega),
      z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega),
      show SK = SK + 8 * 0 from rfl, k 0 (by decide), k 1 (by decide), k 2 (by decide), k 3 (by decide),
      show MSG = MSG + 8 * 0 from rfl, mm 0 (by decide), mm 1 (by decide), mm 2 (by decide), mm 3 (by decide)]
    rfl
  refine TBSim.steps st4 ?_
  refine TBSim.privateNonce_bind (W := 30 + W) (fetch_122 im hc t4 p4) x5' hv4 hq4 (fun b => ?_)
  set t5 := writeHash t4 b
  have hwf5 := Frame.writeHash t4 b RHOOUT y12 (by decide)
  have hrho : DigAt t5 RHOOUT (b.extractLsb' 0 128) := DigAt.writeHash_lo t4 b RHOOUT y12 (by decide)
  obtain ⟨t6, st6, p6, x19, s0', s8', d0, d8, d32, d40, d48, d56, r6, f6⟩ :=
    blk123_spec im hc t5 (by rw [pc_writeHash, p4, pcOf_add4])
  have mm5 : ∀ j < 4, t5.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [hwf5.get (by sg_omega) (by sg_omega), f4.get (by sg_omega) (by sg_omega)]; exact mm j hj
  have hpre : DsPre t6 (b.extractLsb' 0 128) m :=
    { pc := p6
      x5 := by rw [r6.get (by decide), getReg_writeHash, x5']
      x19 := x19
      rho := ⟨by rw [d0]; exact hrho.1, by rw [d8]; exact hrho.2⟩
      msg := fun k hk => by
        interval_cases k
        · rw [show DIG + 32 + 8 * 0 = DIG + 32 from rfl, d32]; exact mm5 0 (by decide)
        · rw [show DIG + 32 + 8 * 1 = DIG + 40 from rfl, d40]; exact mm5 1 (by decide)
        · rw [show DIG + 32 + 8 * 2 = DIG + 48 from rfl, d48]; exact mm5 2 (by decide)
        · rw [show DIG + 32 + 8 * 3 = DIG + 56 from rfl, d56]; exact mm5 3 (by decide) }
  have f06 : Frame s0 t6 (fun X => (((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) ∨
      (RHOOUT ≤ X ∧ X < RHOOUT + 32) ∨ (SIG ≤ X ∧ X < SIG + 16) ∨ (DIG ≤ X ∧ X < DIG + 64)) :=
    ((f04.trans hwf5).trans f6).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · sg_omega)
  refine TBSim.steps st6 (hrest _ t6 ?_)
  refine ⟨hpre, ⟨by rw [s0']; exact hrho.1, by rw [s8']; exact hrho.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q0, k 0 (by decide)]
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q8]; exact k 1 (by decide)
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q32]; exact k 2 (by decide)
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q40]; exact k 3 (by decide)
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q48]
  · rw [f6.get (by sg_omega) (by sg_omega), hwf5.get (by sg_omega) (by sg_omega), q56]
  · exact f06.mono (fun X _ h => by unfold FrontW; sg_omega)

end SigGolfCandidate.T3M.Sign.Boundary.Generic

namespace SigGolfCandidate.T3M.Sign.Boundary.Generic
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest privateMac privateNonce)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem sign_frontCodeAt : FrontCodeAt Images.signImage := by
  constructor
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
theorem sign_nonce_front {sk : SecretKey} {cache : Bytes 131072} {m : Message}
    {α : Type} {W : Nat} {Q : Option α → MachineState → Prop}
    (K : Digest → M (Option α))
    (hfail : ∀ t, Failed t → Q none t)
    (hrest : ∀ rho t, NoncePost sk cache m rho t → TBSim Images.signImage sk t W (K rho) Q) :
    TBSim Images.signImage sk (sinit sk cache m) (frontC + W) (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= K) Q :=
  nonce_front Images.signImage sign_frontCodeAt FullCache.Generic.sign_macCodeAt K hfail hrest
end SigGolfCandidate.T3M.Sign.Boundary.Generic
end
-- ==== merged from T3M_Sign_InitState ====
section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem dataBase_sign : dataBase (submission.image .sign) = SIGN_DATA := by
  unfold dataBase; rw [show (submission.image .sign).data.length = 86144 from Images.signData_length]; rfl
private theorem initialState_sign_generic (s : Submission) (sk : SecretKey)
    (cache : Bytes s.sizes.cache) (m : Message)
    (hv : (s.image .sign).Valid s.sizes s.layout) :
    initialState s .sign (sk, cache, m) = some
      (((((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
        (BitVec.ofNat 64 (dataBase (s.image .sign))) (s.image .sign).data).writeBytesAsWords
        (BitVec.ofNat 64 s.layout.secretKey) (bytes sk)).writeBytesAsWords
        (BitVec.ofNat 64 s.layout.cache) (bytes cache)).writeBytesAsWords
        (BitVec.ofNat 64 s.layout.message) (bytes m)).setReg .x2
        (BitVec.ofNat 64 (dataBase (s.image .sign)))) := by
  simp only [initialState, if_pos hv, inputBuffers, List.foldl_cons, List.foldl_nil]
theorem initialState_sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    initialState submission .sign (sk, cache, m) = some (sinit sk cache m) := by
  rw [initialState_sign_generic submission sk cache m submission_sign_valid, dataBase_sign]
  rfl
end SigGolfCandidate.T3M.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_GfMul ====
section

/-!
# Limb-level facts for the sign machine's GF(2^128) Horner routine (campaign X1, stage A)

The routine keeps a 128-bit value in two 64-bit limbs and a product of up to 138 bits in three limbs. `lim2`/`lim3`
read limbs as a natural number. The lemmas relate one machine bit-step (conditional xor of the shifted multiplicand,
shift by one) to `clmulSmall`, the fold to `gfFold`, and the Horner step to `familyEval`.
-/

namespace ClaudeWCT.W9.Machine.Sign.Gf
open ClaudeWCT.Arith

/-- Two limbs as a number. -/
def lim2 (a b : BitVec 64) : Nat := a.toNat + 2 ^ 64 * b.toNat
/-- Three limbs as a number. -/
def lim3 (a b c : BitVec 64) : Nat := a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat)

theorem xor_split {k x y x' y' : Nat} (hx : x < 2 ^ k) (hx' : x' < 2 ^ k) :
    (x + 2 ^ k * y) ^^^ (x' + 2 ^ k * y') = (x ^^^ x') + 2 ^ k * (y ^^^ y') := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.add_comm x, Nat.add_comm x', Nat.add_comm (x ^^^ x'),
    Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hx',
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hx')]
  split <;> simp [Nat.testBit_xor]

theorem lim2_xor (a b a' b' : BitVec 64) : lim2 (a ^^^ a') (b ^^^ b') = lim2 a b ^^^ lim2 a' b' := by
  unfold lim2
  rw [BitVec.toNat_xor, BitVec.toNat_xor, xor_split a.isLt a'.isLt]

theorem lim3_xor (a b c a' b' c' : BitVec 64) :
    lim3 (a ^^^ a') (b ^^^ b') (c ^^^ c') = lim3 a b c ^^^ lim3 a' b' c' := by
  unfold lim3
  rw [BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_xor, xor_split a.isLt a'.isLt,
    xor_split b.isLt b'.isLt]

theorem toNat_shl1_or (b a : BitVec 64) :
    ((b <<< 1) ||| (a >>> 63)).toNat = 2 * (b.toNat % 2 ^ 63) + a.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have h1 : b.toNat * 2 ^ 1 % 2 ^ 64 = 2 ^ 1 * (b.toNat % 2 ^ 63) := by omega
  have h2 : a.toNat / 2 ^ 63 < 2 ^ 1 := by omega
  rw [h1, ← Nat.two_pow_add_eq_or_of_lt h2]

theorem toNat_shl1 (a : BitVec 64) : (a <<< 1).toNat = 2 * (a.toNat % 2 ^ 63) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- One shift of the three-limb multiplicand. -/
theorem lim3_shl1 (a b c : BitVec 64) (hc : c.toNat < 2 ^ 63) :
    lim3 (a <<< 1) ((b <<< 1) ||| (a >>> 63)) ((c <<< 1) ||| (b >>> 63)) = 2 * lim3 a b c := by
  unfold lim3
  rw [toNat_shl1_or, toNat_shl1_or, toNat_shl1]
  have := a.isLt
  have := b.isLt
  omega

theorem lim3_lt (a b c : BitVec 64) {n : Nat} (h : lim3 a b c < 2 ^ (128 + n)) : c.toNat < 2 ^ n := by
  unfold lim3 at h
  rw [Nat.pow_add] at h
  have : 2 ^ 128 * c.toNat < 2 ^ 128 * 2 ^ n := by
    calc 2 ^ 128 * c.toNat = 2 ^ 64 * (2 ^ 64 * c.toNat) := by rw [← Nat.mul_assoc]; rfl
      _ ≤ a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat) := by
        have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_add_left (2 ^ 64 * c.toNat) b.toNat)
        omega
      _ < 2 ^ 128 * 2 ^ n := h
  exact Nat.lt_of_mul_lt_mul_left this

theorem clmulSmall_succ (a d k : Nat) :
    clmulSmall a d (k + 1) = (if d.testBit k then a <<< k else 0) ^^^ clmulSmall a d k := rfl

theorem shl_lt {a m : Nat} (ha : a < 2 ^ m) (n : Nat) : a <<< n < 2 ^ (m + n) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos n)

/-- Terms `a <<< k` for `k ≤ n` only: the product with `n + 1` bits of `d` has at most `m + n` bits. -/
theorem clmulSmall_lt {a m : Nat} (ha : a < 2 ^ m) (d : Nat) : ∀ n, clmulSmall a d (n + 1) < 2 ^ (m + n)
  | 0 => by
    rw [clmulSmall_succ]
    simp only [clmulSmall, Nat.xor_zero, Nat.add_zero]
    split
    · rw [Nat.shiftLeft_zero]; exact ha
    · exact Nat.two_pow_pos _
  | n + 1 => by
    rw [clmulSmall_succ]
    have ih := clmulSmall_lt ha d n
    refine Nat.xor_lt_two_pow ?_ (lt_of_lt_of_le ih (Nat.pow_le_pow_right (by norm_num) (by omega)))
    split
    · exact shl_lt ha (n + 1)
    · exact Nat.two_pow_pos _

theorem clmulSmall_stable (a : Nat) {d n : Nat} (hd : d < 2 ^ n) : ∀ m, n ≤ m → clmulSmall a d m = clmulSmall a d n
  | m, hm => by
    induction m with
    | zero => have : n = 0 := by omega
              subst this; rfl
    | succ m ih =>
      by_cases h : n = m + 1
      · subst h; rfl
      · rw [clmulSmall_succ, ih (by omega), Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        simp

/-- The bit-step: conditional xor of the multiplicand into the product. -/
theorem clmul_step (a d k : Nat) (P : Nat) (hP : P = clmulSmall a d k) (bit : Bool)
    (hbit : bit = d.testBit k) :
    (if bit then P ^^^ a * 2 ^ k else P) = clmulSmall a d (k + 1) := by
  subst hP hbit
  rw [clmulSmall_succ, Nat.shiftLeft_eq]
  split
  · exact Nat.xor_comm _ _
  · simp

theorem testBit_eq_div (d k : Nat) : d.testBit k = decide (d / 2 ^ k % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]

theorem clmulSmall_87 (x : Nat) :
    clmulSmall x 0x87 8 = x <<< 7 ^^^ (x <<< 2 ^^^ (x <<< 1 ^^^ x)) := by
  simp only [clmulSmall, show Nat.testBit 135 0 = true by decide, show Nat.testBit 135 1 = true by decide,
    show Nat.testBit 135 2 = true by decide, show Nat.testBit 135 3 = false by decide,
    show Nat.testBit 135 4 = false by decide, show Nat.testBit 135 5 = false by decide,
    show Nat.testBit 135 6 = false by decide, show Nat.testBit 135 7 = true by decide, if_true,
    Bool.false_eq_true, if_false, Nat.shiftLeft_zero, Nat.xor_zero, Nat.zero_xor]

/-- The machine's fold of the high limb (bits 0, 1, 2, 7 of 0x87) into the low limb. -/
def foldLo (r0 r2 : BitVec 64) : BitVec 64 := (((r0 ^^^ r2 <<< 1) ^^^ r2 <<< 2) ^^^ r2 <<< 7) ^^^ r2

theorem shl_small_lt (x k : Nat) (hk : k ≤ 7) (hx : x < 2 ^ 9) : x <<< k < 2 ^ 64 := by
  have h1 := shl_lt hx k
  have h2 : 2 ^ (9 + k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem toNat_shl_small (x : BitVec 64) (k : Nat) (hk : k ≤ 7) (hx : x.toNat < 2 ^ 9) :
    (x <<< k).toNat = x.toNat <<< k := by
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (shl_small_lt _ k hk hx)]

theorem foldLo_toNat (r0 r2 : BitVec 64) (h2 : r2.toNat < 2 ^ 9) :
    (foldLo r0 r2).toNat = r0.toNat ^^^ clmulSmall r2.toNat 0x87 8 := by
  unfold foldLo
  simp only [BitVec.toNat_xor]
  rw [toNat_shl_small r2 1 (by norm_num) h2, toNat_shl_small r2 2 (by norm_num) h2,
    toNat_shl_small r2 7 (by norm_num) h2, clmulSmall_87]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases r0.toNat.testBit i <;> cases (r2.toNat <<< 1).testBit i <;> cases (r2.toNat <<< 2).testBit i <;>
    cases (r2.toNat <<< 7).testBit i <;> cases r2.toNat.testBit i <;> rfl

theorem clmul87_lt (x : Nat) (hx : x < 2 ^ 9) : clmulSmall x 0x87 8 < 2 ^ 64 := by
  rw [clmulSmall_87]
  have h0 : x < 2 ^ 64 := lt_of_lt_of_le hx (by norm_num)
  exact Nat.xor_lt_two_pow (shl_small_lt x 7 (by norm_num) hx) (Nat.xor_lt_two_pow (shl_small_lt x 2 (by norm_num) hx)
    (Nat.xor_lt_two_pow (shl_small_lt x 1 (by norm_num) hx) h0))

/-- The fold, on limbs. -/
theorem lim2_fold (r0 r1 r2 : BitVec 64) (h2 : r2.toNat < 2 ^ 9) :
    lim2 (foldLo r0 r2) r1 = gfFold (lim3 r0 r1 r2) := by
  unfold gfFold lim2
  have hmod : lim3 r0 r1 r2 % 2 ^ 128 = r0.toNat + 2 ^ 64 * r1.toNat := by
    unfold lim3; have := r0.isLt; have := r1.isLt; omega
  have hdiv : lim3 r0 r1 r2 >>> 128 = r2.toNat := by
    rw [Nat.shiftRight_eq_div_pow]; unfold lim3; have := r0.isLt; have := r1.isLt; omega
  rw [hmod, hdiv, foldLo_toNat r0 r2 h2]
  have h := xor_split (k := 64) (y := r1.toNat) (y' := 0) r0.isLt (clmul87_lt _ h2)
  rw [Nat.mul_zero, Nat.add_zero, Nat.xor_zero] at h
  exact h.symm

theorem gfMulSmall_lt {a : Nat} (ha : a < 2 ^ 128) (d : Nat) : gfMulSmall a d < 2 ^ 128 := by
  unfold gfMulSmall gfFold
  have hc := clmulSmall_lt ha d 9
  refine Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) ?_
  have h9 : clmulSmall a d 10 >>> 128 < 2 ^ 9 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hc)
  have := clmul87_lt _ h9
  exact lt_of_lt_of_le this (by norm_num)

theorem lim2_toNat (x : BitVec 128) : lim2 (x.extractLsb' 0 64) (x.extractLsb' 64 64) = x.toNat := by
  unfold lim2
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  have := x.isLt
  omega

theorem limbs_of_lim2 {a b : BitVec 64} {x : BitVec 128} (h : lim2 a b = x.toNat) :
    a = x.extractLsb' 0 64 ∧ b = x.extractLsb' 64 64 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold lim2 at h
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] <;>
    omega

theorem familyEval_cons (c : BitVec 128) (rest : List (BitVec 128)) (pt : Nat) :
    familyEval (c :: rest) pt = gfMulPt (familyEval rest pt) pt ^^^ c := rfl

/-- One Horner step on limbs: product limbs `r` of `acc * d`, coefficient limbs `c0 c1`. -/
theorem horner_limbs {acc c : BitVec 128} {d : Nat} {r0 r1 r2 c0 c1 : BitVec 64}
    (hr : lim3 r0 r1 r2 = clmulSmall acc.toNat d 10) (hc : lim2 c0 c1 = c.toNat) :
    lim2 (foldLo r0 r2 ^^^ c0) (r1 ^^^ c1) = (gfMulPt acc d ^^^ c).toNat := by
  have hlt := clmulSmall_lt acc.isLt d 9
  have h2 : r2.toNat < 2 ^ 9 := lim3_lt r0 r1 r2 (n := 9) (by rw [hr]; exact hlt)
  rw [lim2_xor, lim2_fold r0 r1 r2 h2, hr, hc, BitVec.toNat_xor]
  unfold gfMulPt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (gfMulSmall_lt acc.isLt d)]
  rfl

end ClaudeWCT.W9.Machine.Sign.Gf
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_HornRun ====
section

/-!
# The shared GF(2^128) Horner routine HORN of the stage-A sign image

HORN (entry `hornI`, return through `x1`) evaluates `familyEval coefs d` for the 54 coefficients stored at
`COEF + 16 k` and the point `d = x6 < 1024`, and stores the result at `CHAINW + 48`. Horner loop `HK`: `x7` walks
down the coefficients, `(x10, x11)` hold the accumulator; bit loop `HB`: `(x10, x11, x12)` hold `acc * 2^k`,
`(x13, x14, x15)` hold `clmulSmall acc d k`, `x16 = d >> k`; `HF` folds once with 0x87 and adds the coefficient.
-/

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open Gf ClaudeWCT.Arith

/-- Registers HORN may change. -/
def hornRegs : List Reg := [.x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29]
/-- The coefficient buffer. -/
def CoefAt (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < 54, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem CoefAt.frame {s t : MachineState} {coefs : List Digest} {W : Nat → Prop} (h : CoefAt s coefs)
    (hf : Frame s t W) (hW : ∀ A, COEF ≤ A → A < COEF + 864 → ¬ W A) : CoefAt t coefs :=
  fun k hk => (h k hk).frame hf (by unfold COEF; omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

section steps
variable {im : Image}

theorem horn_look (hcode : NewCodeAt im) : LookOK im (coordLook 0) := coordLook_ok hcode (by norm_num)

theorem step_H0 (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hornI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hkI ∧ t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * 54) ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ t.getReg .x11 = BitVec.ofNat 64 0 ∧
      t.getReg .x28 = BitVec.ofNat 64 COEF ∧ RegsExcept s t [.x7, .x10, .x11, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runH0_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

theorem step_HK (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hkI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hbI ∧
      t.getReg .x7 = s.getReg .x7 + BitVec.ofNat 64 (2 ^ 64 - 16) ∧ t.getReg .x12 = BitVec.ofNat 64 0 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ t.getReg .x14 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      t.getReg .x16 = s.getReg .x6 ∧ RegsExcept s t [.x7, .x12, .x13, .x14, .x15, .x16] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runHK_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- Cycles of one bit iteration (`b1`: the bit is zero, `b2`: more bits follow). -/
def hbRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]
def hbK (b1 b2 : Bool) : Nat := (if b1 then 11 else 14) + (if b2 then 0 else 1)

theorem step_HB (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hbI) (b1 b2 : Bool)
    (h1 : (s.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = b1)
    (h2 : (s.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = b2) :
    ∃ t, Steps im s (hbK b1 b2) (hbK b1 b2) t ∧ t.pc = pcOf (if b2 then hbI else hfI) ∧
      t.getReg .x10 = s.getReg .x10 <<< 1 ∧
      t.getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) ∧
      t.getReg .x13 = (if b1 then s.getReg .x13 else s.getReg .x13 ^^^ s.getReg .x10) ∧
      t.getReg .x14 = (if b1 then s.getReg .x14 else s.getReg .x14 ^^^ s.getReg .x11) ∧
      t.getReg .x15 = (if b1 then s.getReg .x15 else s.getReg .x15 ^^^ s.getReg .x12) ∧
      t.getReg .x16 = s.getReg .x16 >>> 1 ∧ RegsExcept s t hbRegs ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHB b1 b2).brs, b.holds s := by
    intro b hb
    simp only [expHB, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · show (BinOp.eval .srl (s.getReg .x16) (BitVec.ofNat 64 1) != BitVec.ofNat 64 0) = b2
      rw [binop_srl _ _ (by norm_num)]; exact h2
    · exact h1
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHB_eq b1 b2) s hpc (no_obl s) hbr
  have e10 : ((expHB b1 b2).toState s).getReg .x10 = s.getReg .x10 <<< 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_sll _ 1 (by norm_num)
  have e11 : ((expHB b1 b2).toState s).getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x11) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x10) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e12 : ((expHB b1 b2).toState s).getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x12) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x11) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e16 : ((expHB b1 b2).toState s).getReg .x16 = s.getReg .x16 >>> 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_srl _ 1 (by norm_num)
  refine ⟨_, hst, ?_, e10, e11, e12, ?_, ?_, ?_, e16, (pres_regsExcept _ _ _ _ _ _ _ s).mono ?_, fun A _ _ => rfl⟩
  · cases b2 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · cases b1 <;> simp [hbShift, hbRegs]

theorem eval_foldE (s : MachineState) : foldE.eval s = foldLo (s.getReg .x13) (s.getReg .x15) := by
  show BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (s.getReg .x13)
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 1))) (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 2)))
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 7))) (s.getReg .x15) = _
  rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num)]
  rfl

theorem eval_c0E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c0E.eval s = s.getMem (BitVec.ofNat 64 A) := by
  show s.getMem (s.getReg .x7) = _; rw [h7]

theorem eval_c1E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c1E.eval s = s.getMem (BitVec.ofNat 64 (A + 8)) := by
  show s.getMem (s.getReg .x7 + BitVec.ofNat 64 8) = _; rw [h7, ofNat_add_ofNat]

theorem hfObl_holds (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 16 ≤ MEMORY_BYTES) : ∀ o ∈ hfObl, o.holds s := by
  intro o ho
  simp only [hfObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  have hb : (E.reg .x7).eval s = BitVec.ofNat 64 A := h7
  rcases ho with rfl | rfl
  · exact valid_ofNat hb (by omega) (by omega)
  · exact valid_ofNat (off := 0) hb (by omega) (by omega)

theorem step_HF_cont (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (hne : s.getReg .x7 ≠ s.getReg .x28) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf hkI ∧
      t.getReg .x10 = foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x11 = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t hfRegs.unzip.1 ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHF true).brs, b.holds s := by
    intro b hb
    simp only [expHF, if_true, pres, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = true
    simpa using hne
  have hobl : ∀ o ∈ (expHF true).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHF_eq true) s hpc hobl hbr
  refine ⟨_, hst, rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [hfRegs]), fun A _ _ => rfl⟩
  · rw [pres_getReg]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [pres_getReg]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl

theorem step_HF_exit (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (heq : s.getReg .x7 = s.getReg .x28) :
    ∃ t, Steps im s 17 17 t ∧ t.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 48)) =
        foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 56)) = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t (.x29 :: hfRegs.unzip.1) ∧ Frame s t (fun B => B = CHAINW + 48 ∨ B = CHAINW + 56) := by
  have hbr : ∀ b ∈ (expHF false).brs, b.holds s := by
    intro b hb
    simp only [expHF, Bool.false_eq_true, if_false, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = false
    simp [heq]
  have hobl : ∀ o ∈ (expHF false).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_sound (horn_look hcode) (runHF_eq false) s hpc hobl hbr
  have hm : ∀ a, ((expHF false).toState s).getMem a =
      memEval s [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)] a :=
    fun a => rfl
  refine ⟨_, hst, rfl, ?_, ?_, fun x hx => ?_, frame_of_memEval hm _ (fun p hp => ?_)⟩
  · rw [hm, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [hm, memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl
  · rw [PRes.toState_getReg']
    show ((regsOf (hfRegs ++ [(.x29, cE CHAINW)])).get x).eval s = _
    rw [regsOf_get_ne _ _ (fun p hp he => hx (by
      simp only [hfRegs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> (subst he; simp [hfRegs]))), RegFile.init_get_eval]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> simp
end steps

section loops
variable {im : Image}

structure HbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hbI
  sh : lim3 (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d k
  dd : t.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

structure HfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hfI
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d 10
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

theorem lim3_ite (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 else a0 ^^^ x0) (if b then a1 else a1 ^^^ x1) (if b then a2 else a2 ^^^ x2) =
      if b then lim3 a0 a1 a2 else lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact lim3_xor ..
  · rfl

theorem hbK_le (b1 b2 : Bool) : hbK b1 b2 ≤ 15 := by unfold hbK; cases b1 <;> cases b2 <;> simp

theorem hb_loop (hcode : NewCodeAt im) {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, HbSt t0 d a k t →
      ∃ u m, Steps im t m m u ∧ m ≤ 14 * n + 1 ∧ HfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 10 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    have hk9 : k ≤ 9 := by omega
    have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    obtain ⟨u, su, upc, u10, u11, u12, u13, u14, u15, u16, uregs, uframe⟩ :=
      step_HB hcode t ht.pc _ _ rfl rfl
    have hand : t.getReg .x16 &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (d / 2 ^ k % 2) := by
      rw [ht.dd]; exact ofNat_and_one _ hdk
    have hshr : t.getReg .x16 >>> 1 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
      rw [ht.dd, ofNat_shr _ _ hdk, Nat.div_div_eq_div_mul, pow_one, ← Nat.pow_succ]
    have hb1 : (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = !(d.testBit k) := by
      rw [hand, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : d / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h <;> simp [h]
    have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
      have := lim3_lt (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) (n := 9) (by
        rw [ht.sh, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
      omega
    have hsh : lim3 (u.getReg .x10) (u.getReg .x11) (u.getReg .x12) = a * 2 ^ (k + 1) := by
      rw [u10, u11, u12, lim3_shl1 _ _ _ hlt12, ht.sh, Nat.pow_succ]; ring
    have hpr : lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) = clmulSmall a d (k + 1) := by
      rw [u13, u14, u15, lim3_ite, hb1, ht.pr, ht.sh]
      rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
      cases d.testBit k <;> rfl
    have hdd : u.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by rw [u16, hshr]
    have hregs : RegsExcept t0 u hbRegs := (ht.regs.trans uregs).mono (by simp [hbRegs])
    have hframe : Frame t0 u (fun _ => False) := (ht.frame.trans uframe).mono (fun _ _ h => by simpa using h)
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = false := by rw [hshr, hz]; rfl
      have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      refine ⟨u, _, su, le_trans (hbK_le _ _) (by omega), ⟨?_, ?_, hregs, hframe⟩⟩
      · rw [upc, hb2]; rfl
      · rw [hpr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = true := by
        rw [hshr, ofNat_bne (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num)]; simpa using hz
      have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      obtain ⟨v, m, sv, hm, hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u
        ⟨by rw [upc, hb2]; rfl, hsh, hpr, hdd, hregs, hframe⟩
      refine ⟨v, _, su.trans sv, ?_, hv⟩
      have hk14 : hbK (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0)
          (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) ≤ 14 := by
        rw [hb2]; unfold hbK; split <;> simp
      omega

structure HkSt (s0 : MachineState) (d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hkI
  x6 : t.getReg .x6 = BitVec.ofNat 64 d
  x7 : t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * m)
  x28 : t.getReg .x28 = BitVec.ofNat 64 COEF
  acc : lim2 (t.getReg .x10) (t.getReg .x11) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t hornRegs
  frame : Frame s0 t (fun _ => False)

/-- Cycle bound of one Horner step (HK, at most ten bit iterations, HF). -/
def hornStepC : Nat := 6 + (14 * 10 + 1) + 12

theorem lim3_zero_hi (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

theorem familyEval_drop (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, ClaudeWCT.Arith.familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coefAddr (m : Nat) : BitVec.ofNat 64 (COEF + 16 * (m + 1)) + BitVec.ofNat 64 (2 ^ 64 - 16) =
    BitVec.ofNat 64 (COEF + 16 * m) := by
  rw [ofNat_add_ofNat, SigGolfCandidate.T3M.ofNat_eq_iff]; unfold COEF; omega

theorem horner_mul (hcode : NewCodeAt im) {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    {m : Nat} {t : MachineState} (ht : HkSt s0 d coefs (m + 1) t) :
    ∃ u n, Steps im t n n u ∧ n ≤ 6 + (14 * 10 + 1) ∧ u.pc = pcOf hfI ∧
      u.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * m) ∧ u.getReg .x28 = BitVec.ofNat 64 COEF ∧
      u.getReg .x6 = BitVec.ofNat 64 d ∧
      lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) =
        clmulSmall (familyEval (coefs.drop (m + 1)) d).toNat d 10 ∧
      RegsExcept s0 u hornRegs ∧ Frame s0 u (fun _ => False) := by
  obtain ⟨t1, s1, p1, x7, x12, x13, x14, x15, x16, r1, f1⟩ := step_HK hcode t ht.pc
  have h0 : HbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi, r1.get (by simp), r1.get (by simp), ht.acc]; simp
    · rw [x13, x14, x15]; unfold lim3; simp [clmulSmall]
    · rw [x16, ht.x6]; simp
  obtain ⟨u, n, su, hn, hu⟩ := hb_loop hcode (BitVec.isLt _) hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  refine ⟨u, 6 + n, s1.trans su, by omega, hu.pc, ?_, ?_, ?_, hu.pr, ?_, ?_⟩
  · rw [hu.regs.get (by simp [hbRegs]), x7, ht.x7, coefAddr]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x28]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x6]
  · exact ((ht.regs.trans r1).trans hu.regs).mono (by simp [hornRegs, hbRegs])
  · exact ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simpa using h)

/-- The first `n` coefficients of the buffer (stage B: the 17 lower-family coefficients). -/
def CoefAtN (n : Nat) (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < n, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem coef_limbs {N : Nat} (hN : N ≤ 54) {s0 u : MachineState} {coefs : List Digest}
    (hcoef : CoefAtN N s0 coefs) (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < N) :
    lim2 (u.getMem (BitVec.ofNat 64 (COEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (COEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by unfold COEF; omega) id, hf.get (by unfold COEF; omega) id, h.1, h.2, lim2_toNat]

/-- The Horner loop over the first `n ≤ 54` coefficients of the buffer (54: HORN of stage A; 17: the lower
seeds of stage B, entered at `HK` with `x7 = COEF + 16 * 17`). -/
theorem horner_loop (hcode : NewCodeAt im) {s0 : MachineState} {d : Nat} {coefs : List Digest} {N : Nat}
    (hN : N ≤ 54) (hd : d < 2 ^ 10) (hlen : coefs.length = N) (hcoef : CoefAtN N s0 coefs) :
    ∀ m, m < N → ∀ t, HkSt s0 d coefs (m + 1) t →
      ∃ u n c, Steps im t n c u ∧ c ≤ hornStepC * (m + 1) + 5 ∧
        u.pc = s0.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧ DigAt u (CHAINW + 48) (familyEval coefs d) ∧
        RegsExcept s0 u hornRegs ∧ Frame s0 u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, -, upr, uregs, uframe⟩ := horner_mul hcode hd ht
    obtain ⟨v, sv, vpc, v48, v56, vregs, vframe⟩ := step_HF_exit hcode u upc (A := COEF + 16 * 0) u7
      (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) (by rw [u7, u28])
    have hl := horner_limbs upr (coef_limbs hN hcoef uframe (m := 0) (by omega))
    rw [← familyEval_drop coefs 0 (by omega), List.drop_zero] at hl
    obtain ⟨l0, l1⟩ := limbs_of_lim2 hl
    refine ⟨v, _, _, su.trans sv, by unfold hornStepC; omega, ?_, ⟨by rw [v48, l0], by rw [v56, ← l1]⟩, ?_, ?_⟩
    · rw [vpc, uregs.get (by simp [hornRegs])]
    · exact (uregs.trans vregs).mono (by simp [hornRegs, hfRegs])
    · exact (uframe.trans vframe).mono (fun _ _ h => by simpa using h)
  | succ m ih =>
    intro hm t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, u6, upr, uregs, uframe⟩ := horner_mul hcode hd ht
    have hne : u.getReg .x7 ≠ u.getReg .x28 := by
      rw [u7, u28]; intro h; rw [ofNat_inj (by unfold COEF; omega) (by unfold COEF; omega)] at h; omega
    obtain ⟨v, sv, vpc, v10, v11, vregs, vframe⟩ := step_HF_cont hcode u upc u7
      (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) hne
    have hl := horner_limbs upr (coef_limbs hN hcoef uframe (m := m + 1) (by omega))
    rw [← familyEval_drop coefs (m + 1) (by omega)] at hl
    have hv : HkSt s0 d coefs (m + 1) v := by
      refine ⟨vpc, ?_, ?_, ?_, ?_, (uregs.trans vregs).mono (by simp [hornRegs, hfRegs]),
        (uframe.trans vframe).mono (fun _ _ h => by simpa using h)⟩
      · rw [vregs.get (by simp [hfRegs]), u6]
      · rw [vregs.get (by simp [hfRegs]), u7]
      · rw [vregs.get (by simp [hfRegs]), u28]
      · rw [v10, v11]; exact hl
    obtain ⟨w, n', c', sw, hc', wpc, wd, wregs, wframe⟩ := ih (by omega) v hv
    refine ⟨w, _, _, (su.trans sv).trans sw, ?_, wpc, wd, wregs, wframe⟩
    unfold hornStepC at *
    omega

/-- Cycle bound of HORN. -/
def hornC : Nat := 6 + (hornStepC * 54 + 5)

theorem horn_run (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hornI) {d : Nat} (hd : d < 2 ^ 10)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 d) {coefs : List Digest} (hlen : coefs.length = 54)
    (hcoef : CoefAt s coefs) :
    ∃ u n c, Steps im s n c u ∧ c ≤ hornC ∧ u.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      DigAt u (CHAINW + 48) (familyEval coefs d) ∧ RegsExcept s u hornRegs ∧
      Frame s u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  obtain ⟨t, st, tpc, t7, t10, t11, t28, tregs, tframe⟩ := step_H0 hcode s hpc
  have ht : HkSt s d coefs (53 + 1) t := by
    refine ⟨tpc, by rw [tregs.get (by simp)]; exact h6, t7, t28, ?_, tregs.mono (by simp [hornRegs]), tframe⟩
    rw [t10, t11, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, n, c, su, hc, upc, ud, uregs, uframe⟩ := horner_loop hcode (le_refl 54) hd hlen hcoef 53 (by norm_num) t ht
  exact ⟨u, _, _, st.trans su, by unfold hornC; omega, upc, ud, uregs, uframe⟩

end loops
end ClaudeWCT.W9.Machine.Sign
end

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}
open Gf ClaudeWCT.Arith
section steps
variable {im : Image}

theorem horn_look (hcode : Fetch im) : LookOK im (coordLook 0) := coordLook_ok hcode (by norm_num)

theorem step_H0 (hcode : Fetch im) (s : MachineState) (hpc : s.pc = pcOf hornI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hkI ∧ t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * 54) ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ t.getReg .x11 = BitVec.ofNat 64 0 ∧
      t.getReg .x28 = BitVec.ofNat 64 COEF ∧ RegsExcept s t [.x7, .x10, .x11, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runH0_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

theorem step_HK (hcode : Fetch im) (s : MachineState) (hpc : s.pc = pcOf hkI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hbI ∧
      t.getReg .x7 = s.getReg .x7 + BitVec.ofNat 64 (2 ^ 64 - 16) ∧ t.getReg .x12 = BitVec.ofNat 64 0 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ t.getReg .x14 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      t.getReg .x16 = s.getReg .x6 ∧ RegsExcept s t [.x7, .x12, .x13, .x14, .x15, .x16] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runHK_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- Cycles of one bit iteration (`b1`: the bit is zero, `b2`: more bits follow). -/
def hbRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]
def hbK (b1 b2 : Bool) : Nat := (if b1 then 11 else 14) + (if b2 then 0 else 1)

theorem step_HB (hcode : Fetch im) (s : MachineState) (hpc : s.pc = pcOf hbI) (b1 b2 : Bool)
    (h1 : (s.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = b1)
    (h2 : (s.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = b2) :
    ∃ t, Steps im s (hbK b1 b2) (hbK b1 b2) t ∧ t.pc = pcOf (if b2 then hbI else hfI) ∧
      t.getReg .x10 = s.getReg .x10 <<< 1 ∧
      t.getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) ∧
      t.getReg .x13 = (if b1 then s.getReg .x13 else s.getReg .x13 ^^^ s.getReg .x10) ∧
      t.getReg .x14 = (if b1 then s.getReg .x14 else s.getReg .x14 ^^^ s.getReg .x11) ∧
      t.getReg .x15 = (if b1 then s.getReg .x15 else s.getReg .x15 ^^^ s.getReg .x12) ∧
      t.getReg .x16 = s.getReg .x16 >>> 1 ∧ RegsExcept s t hbRegs ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHB b1 b2).brs, b.holds s := by
    intro b hb
    simp only [expHB, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · show (BinOp.eval .srl (s.getReg .x16) (BitVec.ofNat 64 1) != BitVec.ofNat 64 0) = b2
      rw [binop_srl _ _ (by norm_num)]; exact h2
    · exact h1
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHB_eq b1 b2) s hpc (no_obl s) hbr
  have e10 : ((expHB b1 b2).toState s).getReg .x10 = s.getReg .x10 <<< 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_sll _ 1 (by norm_num)
  have e11 : ((expHB b1 b2).toState s).getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x11) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x10) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e12 : ((expHB b1 b2).toState s).getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x12) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x11) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e16 : ((expHB b1 b2).toState s).getReg .x16 = s.getReg .x16 >>> 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_srl _ 1 (by norm_num)
  refine ⟨_, hst, ?_, e10, e11, e12, ?_, ?_, ?_, e16, (pres_regsExcept _ _ _ _ _ _ _ s).mono ?_, fun A _ _ => rfl⟩
  · cases b2 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · cases b1 <;> simp [hbShift, hbRegs]

theorem eval_foldE (s : MachineState) : foldE.eval s = foldLo (s.getReg .x13) (s.getReg .x15) := by
  show BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (s.getReg .x13)
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 1))) (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 2)))
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 7))) (s.getReg .x15) = _
  rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num)]
  rfl

theorem eval_c0E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c0E.eval s = s.getMem (BitVec.ofNat 64 A) := by
  show s.getMem (s.getReg .x7) = _; rw [h7]

theorem eval_c1E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c1E.eval s = s.getMem (BitVec.ofNat 64 (A + 8)) := by
  show s.getMem (s.getReg .x7 + BitVec.ofNat 64 8) = _; rw [h7, ofNat_add_ofNat]

theorem hfObl_holds (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 16 ≤ MEMORY_BYTES) : ∀ o ∈ hfObl, o.holds s := by
  intro o ho
  simp only [hfObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  have hb : (E.reg .x7).eval s = BitVec.ofNat 64 A := h7
  rcases ho with rfl | rfl
  · exact valid_ofNat hb (by omega) (by omega)
  · exact valid_ofNat (off := 0) hb (by omega) (by omega)

theorem step_HF_cont (hcode : Fetch im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (hne : s.getReg .x7 ≠ s.getReg .x28) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf hkI ∧
      t.getReg .x10 = foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x11 = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t hfRegs.unzip.1 ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHF true).brs, b.holds s := by
    intro b hb
    simp only [expHF, if_true, pres, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = true
    simpa using hne
  have hobl : ∀ o ∈ (expHF true).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHF_eq true) s hpc hobl hbr
  refine ⟨_, hst, rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [hfRegs]), fun A _ _ => rfl⟩
  · rw [pres_getReg]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [pres_getReg]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl

theorem step_HF_exit (hcode : Fetch im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (heq : s.getReg .x7 = s.getReg .x28) :
    ∃ t, Steps im s 17 17 t ∧ t.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 48)) =
        foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 56)) = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t (.x29 :: hfRegs.unzip.1) ∧ Frame s t (fun B => B = CHAINW + 48 ∨ B = CHAINW + 56) := by
  have hbr : ∀ b ∈ (expHF false).brs, b.holds s := by
    intro b hb
    simp only [expHF, Bool.false_eq_true, if_false, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = false
    simp [heq]
  have hobl : ∀ o ∈ (expHF false).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_sound (horn_look hcode) (runHF_eq false) s hpc hobl hbr
  have hm : ∀ a, ((expHF false).toState s).getMem a =
      memEval s [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)] a :=
    fun a => rfl
  refine ⟨_, hst, rfl, ?_, ?_, fun x hx => ?_, frame_of_memEval hm _ (fun p hp => ?_)⟩
  · rw [hm, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [hm, memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl
  · rw [PRes.toState_getReg']
    show ((regsOf (hfRegs ++ [(.x29, cE CHAINW)])).get x).eval s = _
    rw [regsOf_get_ne _ _ (fun p hp he => hx (by
      simp only [hfRegs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> (subst he; simp [hfRegs]))), RegFile.init_get_eval]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> simp
end steps

section loops
variable {im : Image}

structure HbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hbI
  sh : lim3 (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d k
  dd : t.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

structure HfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hfI
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d 10
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

theorem lim3_ite (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 else a0 ^^^ x0) (if b then a1 else a1 ^^^ x1) (if b then a2 else a2 ^^^ x2) =
      if b then lim3 a0 a1 a2 else lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact lim3_xor ..
  · rfl

theorem hbK_le (b1 b2 : Bool) : hbK b1 b2 ≤ 15 := by unfold hbK; cases b1 <;> cases b2 <;> simp

theorem hb_loop (hcode : Fetch im) {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, HbSt t0 d a k t →
      ∃ u m, Steps im t m m u ∧ m ≤ 14 * n + 1 ∧ HfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 10 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    have hk9 : k ≤ 9 := by omega
    have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    obtain ⟨u, su, upc, u10, u11, u12, u13, u14, u15, u16, uregs, uframe⟩ :=
      step_HB hcode t ht.pc _ _ rfl rfl
    have hand : t.getReg .x16 &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (d / 2 ^ k % 2) := by
      rw [ht.dd]; exact ofNat_and_one _ hdk
    have hshr : t.getReg .x16 >>> 1 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
      rw [ht.dd, ofNat_shr _ _ hdk, Nat.div_div_eq_div_mul, pow_one, ← Nat.pow_succ]
    have hb1 : (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = !(d.testBit k) := by
      rw [hand, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : d / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h <;> simp [h]
    have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
      have := lim3_lt (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) (n := 9) (by
        rw [ht.sh, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
      omega
    have hsh : lim3 (u.getReg .x10) (u.getReg .x11) (u.getReg .x12) = a * 2 ^ (k + 1) := by
      rw [u10, u11, u12, lim3_shl1 _ _ _ hlt12, ht.sh, Nat.pow_succ]; ring
    have hpr : lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) = clmulSmall a d (k + 1) := by
      rw [u13, u14, u15, lim3_ite, hb1, ht.pr, ht.sh]
      rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
      cases d.testBit k <;> rfl
    have hdd : u.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by rw [u16, hshr]
    have hregs : RegsExcept t0 u hbRegs := (ht.regs.trans uregs).mono (by simp [hbRegs])
    have hframe : Frame t0 u (fun _ => False) := (ht.frame.trans uframe).mono (fun _ _ h => by simpa using h)
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = false := by rw [hshr, hz]; rfl
      have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      refine ⟨u, _, su, le_trans (hbK_le _ _) (by omega), ⟨?_, ?_, hregs, hframe⟩⟩
      · rw [upc, hb2]; rfl
      · rw [hpr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = true := by
        rw [hshr, ofNat_bne (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num)]; simpa using hz
      have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      obtain ⟨v, m, sv, hm, hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u
        ⟨by rw [upc, hb2]; rfl, hsh, hpr, hdd, hregs, hframe⟩
      refine ⟨v, _, su.trans sv, ?_, hv⟩
      have hk14 : hbK (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0)
          (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) ≤ 14 := by
        rw [hb2]; unfold hbK; split <;> simp
      omega

structure HkSt (s0 : MachineState) (d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hkI
  x6 : t.getReg .x6 = BitVec.ofNat 64 d
  x7 : t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * m)
  x28 : t.getReg .x28 = BitVec.ofNat 64 COEF
  acc : lim2 (t.getReg .x10) (t.getReg .x11) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t hornRegs
  frame : Frame s0 t (fun _ => False)

/-- Cycle bound of one Horner step (HK, at most ten bit iterations, HF). -/
def hornStepC : Nat := 6 + (14 * 10 + 1) + 12

theorem lim3_zero_hi (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

theorem familyEval_drop (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, ClaudeWCT.Arith.familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coefAddr (m : Nat) : BitVec.ofNat 64 (COEF + 16 * (m + 1)) + BitVec.ofNat 64 (2 ^ 64 - 16) =
    BitVec.ofNat 64 (COEF + 16 * m) := by
  rw [ofNat_add_ofNat, SigGolfCandidate.T3M.ofNat_eq_iff]; unfold COEF; omega

theorem horner_mul (hcode : Fetch im) {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    {m : Nat} {t : MachineState} (ht : HkSt s0 d coefs (m + 1) t) :
    ∃ u n, Steps im t n n u ∧ n ≤ 6 + (14 * 10 + 1) ∧ u.pc = pcOf hfI ∧
      u.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * m) ∧ u.getReg .x28 = BitVec.ofNat 64 COEF ∧
      u.getReg .x6 = BitVec.ofNat 64 d ∧
      lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) =
        clmulSmall (familyEval (coefs.drop (m + 1)) d).toNat d 10 ∧
      RegsExcept s0 u hornRegs ∧ Frame s0 u (fun _ => False) := by
  obtain ⟨t1, s1, p1, x7, x12, x13, x14, x15, x16, r1, f1⟩ := step_HK hcode t ht.pc
  have h0 : HbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi, r1.get (by simp), r1.get (by simp), ht.acc]; simp
    · rw [x13, x14, x15]; unfold lim3; simp [clmulSmall]
    · rw [x16, ht.x6]; simp
  obtain ⟨u, n, su, hn, hu⟩ := hb_loop hcode (BitVec.isLt _) hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  refine ⟨u, 6 + n, s1.trans su, by omega, hu.pc, ?_, ?_, ?_, hu.pr, ?_, ?_⟩
  · rw [hu.regs.get (by simp [hbRegs]), x7, ht.x7, coefAddr]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x28]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x6]
  · exact ((ht.regs.trans r1).trans hu.regs).mono (by simp [hornRegs, hbRegs])
  · exact ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simpa using h)

/-- The first `n` coefficients of the buffer (stage B: the 17 lower-family coefficients). -/
def CoefAtN (n : Nat) (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < n, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem coef_limbs {N : Nat} (hN : N ≤ 54) {s0 u : MachineState} {coefs : List Digest}
    (hcoef : CoefAtN N s0 coefs) (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < N) :
    lim2 (u.getMem (BitVec.ofNat 64 (COEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (COEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by unfold COEF; omega) id, hf.get (by unfold COEF; omega) id, h.1, h.2, lim2_toNat]

/-- The Horner loop over the first `n ≤ 54` coefficients of the buffer (54: HORN of stage A; 17: the lower
seeds of stage B, entered at `HK` with `x7 = COEF + 16 * 17`). -/
theorem horner_loop (hcode : Fetch im) {s0 : MachineState} {d : Nat} {coefs : List Digest} {N : Nat}
    (hN : N ≤ 54) (hd : d < 2 ^ 10) (hlen : coefs.length = N) (hcoef : CoefAtN N s0 coefs) :
    ∀ m, m < N → ∀ t, HkSt s0 d coefs (m + 1) t →
      ∃ u n c, Steps im t n c u ∧ c ≤ hornStepC * (m + 1) + 5 ∧
        u.pc = s0.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧ DigAt u (CHAINW + 48) (familyEval coefs d) ∧
        RegsExcept s0 u hornRegs ∧ Frame s0 u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, -, upr, uregs, uframe⟩ := horner_mul hcode hd ht
    obtain ⟨v, sv, vpc, v48, v56, vregs, vframe⟩ := step_HF_exit hcode u upc (A := COEF + 16 * 0) u7
      (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) (by rw [u7, u28])
    have hl := horner_limbs upr (coef_limbs hN hcoef uframe (m := 0) (by omega))
    rw [← familyEval_drop coefs 0 (by omega), List.drop_zero] at hl
    obtain ⟨l0, l1⟩ := limbs_of_lim2 hl
    refine ⟨v, _, _, su.trans sv, by unfold hornStepC; omega, ?_, ⟨by rw [v48, l0], by rw [v56, ← l1]⟩, ?_, ?_⟩
    · rw [vpc, uregs.get (by simp [hornRegs])]
    · exact (uregs.trans vregs).mono (by simp [hornRegs, hfRegs])
    · exact (uframe.trans vframe).mono (fun _ _ h => by simpa using h)
  | succ m ih =>
    intro hm t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, u6, upr, uregs, uframe⟩ := horner_mul hcode hd ht
    have hne : u.getReg .x7 ≠ u.getReg .x28 := by
      rw [u7, u28]; intro h; rw [ofNat_inj (by unfold COEF; omega) (by unfold COEF; omega)] at h; omega
    obtain ⟨v, sv, vpc, v10, v11, vregs, vframe⟩ := step_HF_cont hcode u upc u7
      (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) hne
    have hl := horner_limbs upr (coef_limbs hN hcoef uframe (m := m + 1) (by omega))
    rw [← familyEval_drop coefs (m + 1) (by omega)] at hl
    have hv : HkSt s0 d coefs (m + 1) v := by
      refine ⟨vpc, ?_, ?_, ?_, ?_, (uregs.trans vregs).mono (by simp [hornRegs, hfRegs]),
        (uframe.trans vframe).mono (fun _ _ h => by simpa using h)⟩
      · rw [vregs.get (by simp [hfRegs]), u6]
      · rw [vregs.get (by simp [hfRegs]), u7]
      · rw [vregs.get (by simp [hfRegs]), u28]
      · rw [v10, v11]; exact hl
    obtain ⟨w, n', c', sw, hc', wpc, wd, wregs, wframe⟩ := ih (by omega) v hv
    refine ⟨w, _, _, (su.trans sv).trans sw, ?_, wpc, wd, wregs, wframe⟩
    unfold hornStepC at *
    omega

/-- Cycle bound of HORN. -/
def hornC : Nat := 6 + (hornStepC * 54 + 5)

theorem horn_run (hcode : Fetch im) (s : MachineState) (hpc : s.pc = pcOf hornI) {d : Nat} (hd : d < 2 ^ 10)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 d) {coefs : List Digest} (hlen : coefs.length = 54)
    (hcoef : CoefAt s coefs) :
    ∃ u n c, Steps im s n c u ∧ c ≤ hornC ∧ u.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      DigAt u (CHAINW + 48) (familyEval coefs d) ∧ RegsExcept s u hornRegs ∧
      Frame s u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  obtain ⟨t, st, tpc, t7, t10, t11, t28, tregs, tframe⟩ := step_H0 hcode s hpc
  have ht : HkSt s d coefs (53 + 1) t := by
    refine ⟨tpc, by rw [tregs.get (by simp)]; exact h6, t7, t28, ?_, tregs.mono (by simp [hornRegs]), tframe⟩
    rw [t10, t11, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, n, c, su, hc, upc, ud, uregs, uframe⟩ := horner_loop hcode (le_refl 54) hd hlen hcoef 53 (by norm_num) t ht
  exact ⟨u, _, _, st.trans su, by unfold hornC; omega, upc, ud, uregs, uframe⟩

end loops
end ClaudeWCT.W9.Machine.Sign.SharedReuse

end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_PackedHelper ====
section

section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def seedHookCode : List (BitVec 32) := [985739375]
theorem codeAt_seedHookCode : CodeAt image (pcOf 1055) seedHookCode := by
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def packedSeedCode : List (BitVec 32) := [67374691,623715,0xb91f706f,335543,0x800e8e93,619411,233059,134711,84817155,93205891,11448355,12497955,17731219,8389395,40436531,7537459,1266451,33755923,17044755,10707763,1270547,0xf69f606f,19,0xbd0ed06f,0xbf9ec06f]
theorem codeAt_packedSeedCode : CodeAt image (pcOf 20746) packedSeedCode := by
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
end SigGolfCandidate.T3M.Sign
end

section


namespace ClaudeWCT.W9.Machine.Sign.PackedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS)
set_option maxRecDepth 100000
theorem lookOK_of_codeAt {im : Image} {base : Nat} {code : List (BitVec 32)} (h : CodeAt im (pcOf base) code)
    (hb : 0x1000 + 4 * base < 2 ^ 64) :
    LookOK im (fun n => if base ≤ n then code[n - base]? else none) := by
  intro n w hw
  dsimp only at hw
  split at hw
  · rename_i hle
    obtain ⟨-, -, -, hpre⟩ := h
    have hp : ((pcOf base).toNat - 0x1000) / 4 = base := by simp only [pcOf, BitVec.toNat_ofNat]; omega
    rw [hp] at hpre
    obtain ⟨rest, hrest⟩ := hpre
    have hlen : n - base < code.length := (List.getElem?_eq_some_iff.mp hw).1
    have h2 : (im.code.drop base)[n - base]? = some w := by rw [← hrest, List.getElem?_append_left hlen]; exact hw
    rwa [List.getElem?_drop, show base + (n - base) = n by omega] at h2
  · cases hw
def hkLook (n : Nat) : Option (BitVec 32) := if 1055 ≤ n then Sign.seedHookCode[n - 1055]? else none
def hLook (n : Nat) : Option (BitVec 32) := if 20746 ≤ n then Sign.packedSeedCode[n - 20746]? else none
theorem and_one_ofNat (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, toNat_ofNat_lt (by norm_num), toNat_ofNat_lt (by omega),
    Nat.and_one_is_mod]
theorem hkLook_ok : LookOK Sign.image hkLook := lookOK_of_codeAt Sign.codeAt_seedHookCode (by decide)
theorem hLook_ok : LookOK Sign.image hLook := lookOK_of_codeAt Sign.codeAt_packedSeedCode (by decide)
def resHk : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 20746, false, 1, 1, [], none⟩
/-- Campaign T8D: the top branch `20746 beq s0` lands on `20769 j TOPSEED (1557)`. -/
def resTop : PRes :=
  ⟨⟨RegFile.init, [], []⟩, pcOf 1557, false, 2, 2, [⟨.eq, .reg .x8, cst 0, true⟩], none⟩
theorem chk_helper : (optBeq (run hkLook [20746] 1055 []) resHk &&
    optBeq (run hLook [1557] 20746 [.br true]) resTop) = true := by decide +kernel
theorem run_hk : run hkLook [20746] 1055 [] = some resHk := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.1
theorem run_top : run hLook [1557] 20746 [.br true] = some resTop := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.2
theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1055) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf 20746 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hkLook_ok run_hk s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem top_spec (s : MachineState) (hpc : s.pc = pcOf 20746) (h8 : s.getReg .x8 = BitVec.ofNat 64 0) :
    ∃ t, Steps Sign.image s 2 2 t ∧ t.pc = pcOf 1557 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hLook_ok run_top s hpc rfl (by
    intro b hb
    simp only [resTop, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h8]; decide) rfl
  exact ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem hdr_or (lay pair : Nat) (hlay : lay < 256) (hp : pair < 2 ^ 32) :
    BitVec.ofNat 64 (lay * 2 ^ 16) ||| BitVec.ofNat 64 (pair * 2 ^ 32) ||| BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (1 + 65536 * lay + 2 ^ 32 * pair) := by
  rw [BitVec.or_comm (BitVec.ofNat 64 (lay * 2 ^ 16)), ofNat_or_add (lay * 2 ^ 16) pair 32 (by omega),
    show pair * 2 ^ 32 + lay * 2 ^ 16 = (pair * 2 ^ 16 + lay) * 2 ^ 16 by ring, ofNat_or_add 1 _ 16 (by norm_num)]
  congr 1; ring
end ClaudeWCT.W9.Machine.Sign.PackedLeaf
end
end
