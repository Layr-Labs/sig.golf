import SigGolfCandidate.T3M.Images.InlineNative
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailImage
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailJudg

/- The independently selected native image and the image used by the genuine
   chain/Merkle proofs are equal.  Original Blueprint.verifyImage remains the
   old reflected-check image; it is never circularly overridden. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

 theorem original_chunks : SigGolfCandidate.T3M.lChunks = Images.InlineBlueprint.originalChunks := by
  rfl

theorem mapRows_eq (rows : List (List (BitVec 32))) (start : Nat) :
    InlineTail.mapRows start rows = Images.InlineNative.mapRows start rows := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    simp only [InlineTail.mapRows, Images.InlineNative.mapRows]
    rw [ih]
    rfl

theorem image_eq : InlineTail.image = Images.InlineNative.image := by
  unfold InlineTail.image InlineTail.code InlineTail.chunks
    Images.InlineNative.image Images.InlineNative.code Images.InlineNative.chunks
  rw [original_chunks, mapRows_eq]

theorem data_eq_original : Images.InlineNative.image.data = Images.verifyImage.data := by
  rfl

 theorem mapRows_flatten_length (rows : List (List (BitVec 32))) (start : Nat)
    (h : ∀ j, j < rows.length → 691 ≤ start+j → start+j < 755 →
      (rows.getD j []).length=256) :
    (InlineTail.mapRows start rows).flatten.length=rows.flatten.length := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hh : (if 691 ≤ start ∧ start<755 then InlineTail.patchRow (start-691) row else row).length=row.length := by
      split_ifs with hs
      · have hl : row.length=256 := by simpa using h 0 (by simp) (by omega) (by omega)
        rw [InlineTail.patchRow_length _ (by omega) _ hl, hl]
      · rfl
    have ht := ih (start+1) (by
      intro j hj hlo hhi
      have hx := h (j+1) (by simp;omega) (by omega) (by omega)
      simpa only [List.getD_cons_succ] using hx)
    simpa only [InlineTail.mapRows,List.flatten_cons,List.length_append] using congrArg₂ (fun a b : Nat => a + b) hh ht

theorem code_length_eq_original : Images.InlineNative.image.code.length=Images.verifyImage.code.length := by
  rw [←image_eq]
  change InlineTail.code.length=Images.verifyCode.length
  have h := mapRows_flatten_length SigGolfCandidate.T3M.lChunks 0 (by
    intro j hj hlo hhi
    have hr : j-691<64 := by omega
    have hx := InlineTail.nativeRow_length (j-691) hr
    simpa only [show 691+(j-691)=j by omega] using hx)
  change (InlineTail.mapRows 0 SigGolfCandidate.T3M.lChunks).flatten.length=Images.verifyCode.length
  rw [h, SigGolfCandidate.T3M.lChunks_foldl, SigGolfCandidate.T3M.foldl_append_flatten']
  rfl

theorem mapRows_lengths (rows : List (List (BitVec 32))) (start : Nat)
    (h : ∀ j, j < rows.length → 691 ≤ start+j → start+j < 755 →
      (rows.getD j []).length=256) :
    (InlineTail.mapRows start rows).map List.length = rows.map List.length := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hh : (if 691 ≤ start ∧ start<755 then InlineTail.patchRow (start-691) row else row).length=row.length := by
      split_ifs with hs
      · have hl : row.length=256 := by simpa using h 0 (by simp) (by omega) (by omega)
        rw [InlineTail.patchRow_length _ (by omega) _ hl, hl]
      · rfl
    have ht := ih (start+1) (by
      intro j hj hlo hhi
      have hx := h (j+1) (by simp;omega) (by omega) (by omega)
      simpa only [List.getD_cons_succ] using hx)
    simpa only [InlineTail.mapRows, List.map_cons] using congrArg₂ List.cons hh ht

theorem native_chunk_lengths : Images.InlineNative.chunks.map List.length =
    List.replicate 984 256 ++ [23] := by
  have h := mapRows_lengths Images.InlineBlueprint.originalChunks 0 (by
    intro j hj hlo hhi
    exact InlineChunkLengths.full_chunk_length j (by omega))
  rw [mapRows_eq] at h
  exact h.trans InlineChunkLengths.lengths

theorem native_chunks_ok :
    (Images.InlineNative.chunks.dropLast.all fun c => c.length == 256) = true := by
  change (Images.InlineNative.chunks.dropLast.all ((fun n : Nat => n == 256) ∘ List.length)) = true
  rw [← List.all_map, List.map_dropLast, native_chunk_lengths]
  decide +kernel

theorem native_chunks_le :
    (Images.InlineNative.chunks.all fun c => decide (c.length ≤ 256)) = true := by
  change (Images.InlineNative.chunks.all ((fun n : Nat => decide (n ≤ 256)) ∘ List.length)) = true
  rw [← List.all_map, native_chunk_lengths]
  decide +kernel

theorem native_chunk_count : Images.InlineNative.chunks.length = 985 := by
  have h := congrArg List.length native_chunk_lengths
  simpa only [List.length_map, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil] using h

theorem native_code_length : Images.InlineNative.code.length = 251927 := by
  change Images.InlineNative.chunks.flatten.length = 251927
  rw [List.length_flatten, native_chunk_lengths]
  decide +kernel

theorem steps {s t : MachineState} {n c : Nat}
    (h : Steps InlineTail.image s n c t) : Steps Images.InlineNative.image s n c t := by
  rw [←image_eq]
  exact h

theorem fetch {s : MachineState} : Riscv.fetch InlineTail.image s = Riscv.fetch Images.InlineNative.image s := by
  rw [image_eq]

theorem goodQ {s : MachineState} {N C A : Nat} {Q : Prop}
    {X : OracleComp Legacy.HashSpec InlineTail.Judg.Obs}
    (h : InlineTail.Judg.GoodQ InlineTail.image s N C Q A X) :
    InlineTail.Judg.GoodQ Images.InlineNative.image s N C Q A X := by
  rw [←image_eq]
  exact h

#print axioms image_eq
#print axioms code_length_eq_original
#print axioms goodQ
end SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding
