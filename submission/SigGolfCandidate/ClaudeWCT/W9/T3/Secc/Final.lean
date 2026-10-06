import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingE1
import SigGolfCandidate.T3.Secc.WotsEncodingContact
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsRestart
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsClasses
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsSmallTransport
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsSmallContract
import SigGolfCandidate.ClaudeWCT.Numerics.WCTPrice
import SigGolfCandidate.ClaudeWCT.W9.New.C2.SignerCompleteBound

section






















namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
open SigGolfCandidate.T3.Security.Wots.Enc (AgreeOn)
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
def MarkEntry (T : Answers) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96) (digits : List Nat),
    Extract.msgFits a.key.lay message ∧ entry.1 = encRow a.key message counter pad ∧
      referenceInput T a.key ≠ some (encRow a.key message counter pad) ∧
      decode a.key.lay (low entry.2) = some digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T a.key).getD i 0 ≤ digits.getD i 0
theorem markerAt_iff (T : Answers) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T trace a ↔ ∃ entry ∈ trace, MarkEntry T a entry := by
  constructor
  · rintro ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
theorem markerAt_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry)
    (p : CanonGraph.LeafPos × Fin 58) : MarkerAt T' trace (chainAt p) ↔ MarkerAt T trace (chainAt p) := by
  unfold MarkerAt chainAt
  simp only
  rw [referenceInput_congr_honest h, referenceDigits_congr_honest h]
theorem markEntry_cell_le (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 57 / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, pad, digits, -, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
      _ ≤ 57 / (2 : ENNReal) ^ 128 := by
          apply ENNReal.div_le_div_right
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_bound _ W i)
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, pad, digits, -, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_rej_le (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | cell (rejAnswers a.key.lay)] ≤ 57 / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | cell (rejAnswers a.key.lay)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, pad, digits, -, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ ≤ 57 / 53 * Pr[fun output => output.extractLsb' 0 128 ∈ targets |
            ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_cell_rej_le _ _
      _ = 57 / 53 * (targets.card / (2 : ENNReal) ^ 128) := by rw [FirstHit.uniform_low_mem targets]
      _ ≤ 57 / 53 * (53 / (2 : ENNReal) ^ 128) := by
          refine mul_le_mul' le_rfl (ENNReal.div_le_div_right ?_ _)
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_le_53 _ W i)
      _ = 57 / (2 : ENNReal) ^ 128 := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc (53 : ENNReal)⁻¹,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | cell (rejAnswers a.key.lay)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, pad, digits, -, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_init_le (T : Answers) (k : CellKey) (e : k.1) (p : CanonGraph.LeafPos × Fin 58) :
    Pr[fun ans => MarkEntry T (chainAt p) (encInput e.val, ans) | cell (cellInit k e)] ≤
      57 / (2 : ENNReal) ^ 128 := by
  by_cases hp : p.1 = e.val.1.1
  · unfold cellInit
    split_ifs
    · rw [Lazy.probEvent_cell_univ]
      exact markEntry_cell_le T _ _
    · have h := markEntry_rej_le T (encInput e.val) (chainAt p)
      rw [show (chainAt p).key.lay = e.val.1.1.lay from by rw [← hp]; rfl] at h
      exact h
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
    rintro ans - ⟨message, counter, pad, digits, -, he, -⟩
    exact hp (encInput_leaf (he.trans rfl : encInput e.val = encRow (leafOf p.1) message counter pad)).symm
theorem markEntry_sum_init_le (T : Answers) (k : CellKey) (e : k.1) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e.val, ans) |
        cell (cellInit k e)] ≤ 3306 / (2 : ENNReal) ^ 128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e.val, ans) |
        cell (cellInit k e)] ≤ if p.1 = e.val.1.1 then 57 / (2 : ENNReal) ^ 128 else 0 := by
    intro p
    split_ifs with hp
    · exact (probEvent_mono fun ans _ h => h.2).trans (markEntry_init_le T k e p)
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨-, message, counter, pad, digits, -, he, -⟩
      exact hp (encInput_leaf (he.trans rfl : encInput e.val = encRow (leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single e.val.1.1 (fun L _ hL => by simp [hL]) (by simp)]
  simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_div_assoc]
  norm_num
theorem markEntry_sum_cell_le (T : Answers) (e : EncIndex) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e, ans) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 3306 / (2 : ENNReal) ^ 128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e, ans) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ if p.1 = e.1.1 then 57 / (2 : ENNReal) ^ 128 else 0 := by
    intro p
    split_ifs with hp
    · exact (probEvent_mono fun ans _ h => h.2).trans (markEntry_cell_le T _ _)
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨-, message, counter, pad, digits, -, he, -⟩
      exact hp (encInput_leaf (he.trans rfl : encInput e = encRow (leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single e.1.1 (fun L _ hL => by simp [hL]) (by simp)]
  simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_div_assoc]
  norm_num
theorem markEntry_noncell (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (cellKey (eagerAnswers U privateTable pub)).1 x)
    (p : CanonGraph.LeafPos × Fin 58) :
    ¬ (WotsExtract.SourceChain (chainAt p) ∧
      MarkEntry (eagerAnswers U privateTable pub) (chainAt p) (x, eagerAnswers U privateTable pub (.inl (.inr x)))) := by
  rintro ⟨-, message, counter, pad, digits, hfit, he, hne, hdec, -⟩
  have hin : encInput (encIdx p.1 message counter pad hfit) = x :=
    (encInput_encIdx p.1 message counter pad hfit).trans he.symm
  have hnc : ¬ (Free (eagerAnswers U privateTable pub) (encIdx p.1 message counter pad hfit) ∨
      Rej (eagerAnswers U privateTable pub) (encIdx p.1 message counter pad hfit)) :=
    fun hc => hx ⟨encIdx p.1 message counter pad hfit, hc, hin⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf p.1) x := by
    by_contra hfree
    refine hnc (Or.inl ?_)
    change ¬ Reached _ _ (encInput (encIdx p.1 message counter pad hfit))
    rw [hin]
    exact hfree
  cases hs : searchDecode p.1.lay (low (eagerAnswers U privateTable pub (.inl (.inr x)))) with
  | none =>
      refine hnc (Or.inr ⟨?_, ?_⟩)
      · change Reached _ _ (encInput (encIdx p.1 message counter pad hfit))
        rw [hin]
        exact hreached
      · change searchDecode p.1.lay (low (eagerAnswers U privateTable pub
          (.inl (.inr (encInput (encIdx p.1 message counter pad hfit)))))) = none
        rw [hin]
        exact hs
  | some w =>
      have href := reached_valid_reference hreached hs
      exact hne (he ▸ href)
noncomputable def markerCount (s : RefSample) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ MarkerAt s.answers s.trace (chainAt p)).card
theorem markerCount_marks (T : Answers) (trace : List Entry) (pk : Digest) :
    markerCount ⟨T, pk, trace⟩ =
      Lazy.marks (fun p entry => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) entry) trace := by
  unfold markerCount Lazy.marks
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : (WotsExtract.SourceChain (chainAt p) ∧ MarkerAt T trace (chainAt p)) ↔
      ∃ entry ∈ trace, WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) entry := by
    rw [markerAt_iff]
    constructor
    · rintro ⟨hs, entry, hmem, hm⟩
      exact ⟨entry, hmem, hs, hm⟩
    · rintro ⟨entry, hmem, hs, hm⟩
      exact ⟨hs, entry, hmem, hm⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl
theorem markerCount_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry)
    (pk : Digest) : markerCount ⟨T', pk, trace⟩ = markerCount ⟨T, pk, trace⟩ := by
  unfold markerCount
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff := markerAt_congr h trace p
  simp only at hiff ⊢
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, hiff.mp h1.2⟩ h2
  · exact absurd ⟨h2.1, hiff.mpr h2.2⟩ h1
  · rfl
theorem cells_marker_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (adversary : AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          (markerCount (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) : ENNReal) ≤
      (3306 / (2 : ENNReal) ^ 128) * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) : ENNReal) := by
  rw [cell_transfer adversary q U hU privateTable pub (fun s => (markerCount s : ENNReal))
      (fun tr => (Lazy.marks (fun p entry => WotsExtract.SourceChain (chainAt p) ∧
        MarkEntry (eagerAnswers U privateTable pub) (chainAt p) entry) tr : ENNReal))
      (fun y hy r => by
        unfold mkSample
        rw [markerCount_congr (agree_ovc U hU privateTable pub y hy), markerCount_marks]),
    cell_transfer adversary q U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y _ r => encodingCount_mkSample _ r)]
  refine (Lazy.lazy_marks_init_le encInput (cellKey (eagerAnswers U privateTable pub)).1 encInput_injective
    (eagerAnswers U privateTable pub)
    (fun p entry => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry (eagerAnswers U privateTable pub) (chainAt p) entry)
    _ (cellInit (cellKey (eagerAnswers U privateTable pub))) (cellInit_nonempty _)
    (fun e => markEntry_sum_init_le (eagerAnswers U privateTable pub) (cellKey (eagerAnswers U privateTable pub)) e)
    (fun x hx p => markEntry_noncell U privateTable pub x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  exact_mod_cast cellCount_le_encoding _ _
end Enc
open Enc in
theorem reference_markerCount_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * (Enc.markerCount s : ENNReal) ≤
      (3306 / (2 : ENNReal) ^ 128) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact Enc.reference_cells_le adversary q (fun s => (Enc.markerCount s : ENNReal))
    (fun s => (encodingCount s : ENNReal)) _
    (fun privateTable pub => Enc.cells_marker_le adversary q (referenceInputs adversary)
      (Enc.publicUniverse_sub adversary) privateTable pub)
open Enc in
theorem reference_marker_sum_le (adversary : AdversaryP) (q : Nat) :
    ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
      (3306 / 2 ^ 128 : ENNReal) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  refine le_trans (le_of_eq ?_) (reference_markerCount_le adversary q)
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun s => ?_
  unfold Enc.markerCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold Enc.chainAt Enc.leafOf
  split_ifs <;> simp
end ClaudeWCT.W9.T3.Security.Wots
end

section






























namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
def ContactFirstAt (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
def CFK (T : Answers) (trace : List Entry) : Prop :=
  ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain (chainAt p) ∧ ContactFirstAt T trace (chainAt p)
theorem wotsSeed_congr_nonEnc {T T' : Answers} (h : ∀ q, Enc.NonEnc q → T' q = T q) (lay : Layer)
    (tree leaf i : Nat) : WCT9.wotsSeed T' lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  rw [ClaudeWCT.W9.T3.Security.Wots.Mask.wotsSeed_eq, ClaudeWCT.W9.T3.Security.Wots.Mask.wotsSeed_eq,
    h (.inr (.inl _)) trivial]
theorem frontierValue_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (p : CanonGraph.LeafPos × Fin 58) : frontierValue T' (chainAt p) = frontierValue T (chainAt p) := by
  have hd : depth T' (chainAt p) = depth T (chainAt p) := by
    unfold depth chainAt
    rw [referenceDigits_congr_honest h]
  unfold frontierValue honestChainValue
  rw [hd, wotsSeed_congr_nonEnc (nonEnc_of_honest h)]
  exact (Enc.respects_chain _ _ _ _ _ _ _).eval_eq (nonEnc_of_honest h)
theorem contactAt_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry)
    (p : CanonGraph.LeafPos × Fin 58) : ContactAt T' trace (chainAt p) ↔ ContactAt T trace (chainAt p) := by
  have hd : depth T' (chainAt p) = depth T (chainAt p) := by
    unfold depth chainAt
    rw [referenceDigits_congr_honest h]
  unfold ContactAt
  rw [hd, frontierValue_congr_honest h p]
theorem cfk_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry) :
    CFK T' trace ↔ CFK T trace := by
  unfold CFK ContactFirstAt
  simp only [contactAt_congr h, markerAt_congr h]
noncomputable def contacts (T : Answers) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ ContactAt T trace (chainAt p)).card
theorem contacts_mono (T : Answers) {trace trace' : List Entry} (hsub : ∀ e ∈ trace, e ∈ trace') :
    contacts T trace ≤ contacts T trace' := by
  unfold contacts
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, WotsExtract.contactAt_mono hp.2 hsub⟩
theorem contacts_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (trace : List Entry) :
    contacts T' trace = contacts T trace := by
  unfold contacts
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff := contactAt_congr h trace p
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, hiff.mp h1.2⟩ h2
  · exact absurd ⟨h2.1, hiff.mpr h2.2⟩ h1
  · rfl
noncomputable def costL (T : Answers) (F : Set EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell encInput F e.1 then 57 * contacts T hist else 0) + costL T F (hist ++ [e]) rest
theorem costL_le (T : Answers) (F : Set EncIndex) :
    ∀ (trace hist : List Entry), costL T F hist trace ≤ 57 * trace.length * contacts T (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costL]
  | cons e rest ih =>
      intro hist
      unfold costL
      have h1 : contacts T hist ≤ contacts T (hist ++ e :: rest) :=
        contacts_mono T (fun x hx => List.mem_append_left _ hx)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell encInput F e.1 then 57 * contacts T hist else 0) ≤ 57 * contacts T hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith
theorem cfk_new {T : Answers} {h : List Entry} {e : Entry} (hold : ¬ CFK T h) (hnew : CFK T (h ++ [e])) :
    ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain (chainAt p) ∧ ContactAt T h (chainAt p) ∧
      MarkEntry T (chainAt p) e ∧ ¬ MarkerAt T h (chainAt p) := by
  obtain ⟨p, hs, k, hc, hnm, hm⟩ := hnew
  by_cases hk : k ≤ h.length
  · rw [List.take_append_of_le_length hk] at hc hnm
    have hnot : ¬ MarkerAt T h (chainAt p) := fun hmh => hold ⟨p, hs, k, hc, hnm, hmh⟩
    refine ⟨p, hs, WotsExtract.contactAt_mono hc (fun x hx => List.mem_of_mem_take hx), ?_, hnot⟩
    obtain ⟨entry, hmem, hme⟩ := (markerAt_iff T _ _).mp hm
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact absurd ((markerAt_iff T _ _).mpr ⟨entry, hmem, hme⟩) hnot
    · exact hme
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at hnm
    exact absurd hm hnm
noncomputable def cfCharge (T : Answers) (F : Set EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell encInput F x then 57 * contacts T h.toList else 0
  | _ => 0
theorem costL_step (T : Answers) (F : Set EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costL T F h.toList (Lazy.obs input answer * tail).toList =
      cfCharge T F h input + costL T F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costL, cfCharge]
  · simp [Lazy.obs, cfCharge]
theorem cfk_nil (T : Answers) : ¬ CFK T [] := by
  rintro ⟨p, -, k, -, -, hm⟩
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff T _ _).mp hm
  simp at hmem
section Step
variable [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
theorem cf_step (T : Answers) (F : Set EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => MarkEntry T (chainAt p) (encInput e.val, ans) | cell (init e)] ≤ 57 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl encInput F T input).run allowed] *
        (if CFK T (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfCharge T F h input : ENNReal) := by
  classical
  by_cases hold : CFK T h.toList
  · rw [if_pos hold]
    refine le_trans ?_ le_self_add
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (indicator_le_one _)).trans ?_
    exact Lazy.tsum_probOutput_mul_le_self _ _
  rw [if_neg hold, zero_add]
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
  · by_cases hx : Lazy.IsCell encInput F x
    · rw [Lazy.lazyImpl_cell encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfCharge, if_pos hx]
      set e₀ := Lazy.cellOf encInput F x hx with he₀
      have hx₀ : encInput e₀.val = x := Lazy.cellOf_input encInput F x hx
      by_cases hq : ∃ ans₀, (encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro ans
        by_cases hne : ans = ans₀
        · subst hne
          rw [if_neg, mul_zero]
          intro hnew
          obtain ⟨p, -, -, hme, hnm⟩ := cfk_new hold hnew
          rw [← hx₀] at hme
          exact hnm ((markerAt_iff T _ _).mpr ⟨_, hans₀, hme⟩)
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let S := Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
          WotsExtract.SourceChain (chainAt p) ∧ ContactAt T h.toList (chainAt p)
        calc _ = Pr[fun ans => CFK T (h.toList ++ [(x, ans)]) | cell (init e₀)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T (chainAt p) (x, ans) | cell (init e₀)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, -⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T (chainAt p) (x, ans) | cell (init e₀)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 57 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p _ => ?_
              rw [← hx₀]
              exact hcell e₀ p
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((57 * contacts T h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold contacts
              push_cast
              rw [div_eq_mul_inv]
              ring
    · rw [Lazy.lazyImpl_other encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      rw [if_neg]
      · exact zero_le
      · intro hnew
        obtain ⟨p, hs, -, hme, -⟩ := cfk_new hold hnew
        exact hother x hx p ⟨hs, hme⟩
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
theorem lazy_cf_le {α : Type} (T : Answers) (F : Set EncIndex) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => MarkEntry T (chainAt p) (encInput e.val, ans) | cell (init e)] ≤ 57 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        init] * (if CFK T z.1.2.toList then (1 : ENNReal) else 0) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run init] *
          (costL T F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl encInput F T)
    (fun h st => Lazy.Consistent encInput F init h st)
    (fun h st hc input result hr =>
      Lazy.consistent_step encInput F encInput_injective T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty encInput F hinit)))
    (fun h _ => if CFK T h.toList then (1 : ENNReal) else 0) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => costL T F h.toList tail.toList) (cfCharge T F)
    (fun h => by simp [costL]) (fun h input answer tail => costL_step T F h input answer tail)
    (fun h st hc input => cf_step T F init hcell hother h st hc input)
    C 1 init (Lazy.consistent_one encInput F init)
  simp only [one_mul] at key
  rw [if_neg (by simpa using cfk_nil T), zero_add] at key
  simpa using key
end Step
noncomputable def cfInd (s : RefSample) : ENNReal := if CFK s.answers s.trace then 1 else 0
noncomputable def cfCost (s : RefSample) : ENNReal := ((57 * s.trace.length * contacts s.answers s.trace : Nat) : ENNReal)
theorem cells_cf_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (adversary : AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          cfInd (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          cfCost (mkSample (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) r) := by
  rw [cell_transfer adversary q U hU privateTable pub cfInd
      (fun tr => if CFK (eagerAnswers U privateTable pub) tr then (1 : ENNReal) else 0)
      (fun y hy r => by
        unfold cfInd mkSample
        simp only [cfk_congr (agree_ovc U hU privateTable pub y hy)]),
    cell_transfer adversary q U hU privateTable pub cfCost
      (fun tr => ((57 * tr.length * contacts (eagerAnswers U privateTable pub) tr : Nat) : ENNReal))
      (fun y hy r => by
        unfold cfCost mkSample
        simp only [contacts_congr (agree_ovc U hU privateTable pub y hy)])]
  refine (lazy_cf_le (eagerAnswers U privateTable pub) (cellKey (eagerAnswers U privateTable pub)).1 (cellInit (cellKey (eagerAnswers U privateTable pub))) (cellInit_nonempty _)
    (fun e p => markEntry_init_le (eagerAnswers U privateTable pub) (cellKey (eagerAnswers U privateTable pub)) e p)
    (fun x hx p => markEntry_noncell U privateTable pub x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have := costL_le (eagerAnswers U privateTable pub) (cellKey (eagerAnswers U privateTable pub)).1 z.1.2.toList []
  rw [List.nil_append] at this
  exact_mod_cast this
theorem reference_cfInd_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * cfInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, referenceExperiment adversary q s * cfCost s := by
  let _ : ∀ k : Set EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_cells_le adversary q cfInd cfCost _
    (fun privateTable pub => cells_cf_le adversary q (referenceInputs adversary)
      (publicUniverse_sub adversary) privateTable pub)
theorem chainAt_injective : Function.Injective chainAt := by
  rintro ⟨⟨lay, tree, leaf⟩, i⟩ ⟨⟨lay', tree', leaf'⟩, i'⟩ h
  simp only [chainAt, leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hl⟩, hi⟩ := h
  have : tree = tree' := Fin.ext ht
  have : leaf = leaf' := Fin.ext hl
  have : i = i' := Fin.ext hi
  subst tree leaf i
  rfl
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain a) : ∃ p, chainAt p = a := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
theorem contacts_eq_contactCount (s : RefSample) : contacts s.answers s.trace = contactCount s := by
  unfold contacts contactCount
  apply Finset.card_bij (fun p _ => chainAt p)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Finset.mem_filter, mem_sourceChains]
    exact hp
  · intro p _ p' _ h
    exact chainAt_injective h
  · intro a ha
    rw [Finset.mem_filter, mem_sourceChains] at ha
    obtain ⟨p, rfl⟩ := exists_chainAt ha.1
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
theorem cfCost_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * cfCost s ≤
      ((57 * q : Nat) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfCost
    rw [contacts_eq_contactCount]
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlen)
end Enc
open Enc in
theorem reference_contactFirst_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧
        ∃ k, ContactAt s.answers (s.trace.take k) a ∧ ¬MarkerAt s.answers (s.trace.take k) a ∧
          MarkerAt s.answers s.trace a | referenceExperiment adversary q] ≤
      57 * ((q : ENNReal) / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
  calc _ ≤ ∑' s, referenceExperiment adversary q s * Enc.cfInd s := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun s => ?_
        split_ifs with h
        · obtain ⟨a, ha, hcf⟩ := h
          obtain ⟨p, rfl⟩ := Enc.exists_chainAt ha
          rw [Enc.cfInd, if_pos ⟨p, ha, hcf⟩, mul_one, PMF.probOutput_eq_apply]
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, referenceExperiment adversary q s * Enc.cfCost s := Enc.reference_cfInd_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((57 * q : Nat) : ENNReal) *
          ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal)) :=
        mul_le_mul' le_rfl (Enc.cfCost_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring
end ClaudeWCT.W9.T3.Security.Wots
end

section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
theorem reference_trace_length_le (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : s.trace.length ≤ q := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, hrun, rfl⟩ := hs
  have h1 := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hrun
  have h2 : run ∈ support (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) := by
    revert h1
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl (restTable R))
      (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) run
  have hcount : (run.1, SphincsSecurity.QueryCap.calls RefCharged run.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (restTable R) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨run, h2, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (restTable R) adversary q) _ hcount
  refine le_trans ?_ hle
  show (traceOf (restTable R) run.2).length ≤ _
  have hf := traceOf_filter_length (restTable R) (fun _ => True) run.2
  simp only [decide_true, List.filter_true] at hf
  rw [hf]
  unfold SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨x, rfl, -⟩ := hq
  trivial
theorem prefixClassCount_le_length (s : RefSample) : prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  have hsize : ∀ c : ChainAddr, WotsExtract.SourceChain c → c.key.tree < 2 ^ 40 ∧ c.key.leaf < 2 ^ 32 := by
    intro c hc
    refine ⟨by have := hc.1.1; omega, ?_⟩
    have h1 := hc.1.2
    have h2 : 2 ^ height c.key.lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le c.key.lay; omega)
    omega
  unfold ContactAt
  rw [depth_maskAt_all, frontierValue_maskAt_bounded T a b (hsize a ha) (hsize b hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRow a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; rw [hm]
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (prefixRowAt_unique (answers := T) ha hb ⟨_, va, by omega, rfl⟩ ⟨_, vb, by omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(mem_sourceChains b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
theorem reference_twoContacts_le_raw (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      ((2 * q : ℕ) : ENNReal) *
          ((2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
            (1 - (q : ENNReal) / 2 ^ 128)) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      ∑ a ∈ sourceChains, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum sourceChains (referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (mem_sourceChains a).mpr ha, h⟩
    · exact ⟨b, (mem_sourceChains b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ sourceChains) =>
    reference_contactAfterStop_charge adversary q hq a ((mem_sourceChains a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((mem_sourceChains a).mp ha))
  have halloc : ∑ a ∈ sourceChains, ∑' s, referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
        calc ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ sourceChains, prefixCount a s : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := reference_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ sourceChains, prefixCount a s ≤ 2 * q)
      calc referenceExperiment adversary q s * ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (referenceExperiment adversary q s * (contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ sourceChains, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ sourceChains, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains, ∑' s, referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := halloc
    _ ≤ ((2 * q : ℕ) : ENNReal) *
          ((2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
            (1 - (q : ENNReal) / 2 ^ 128)) := mul_le_mul' le_rfl (reference_contacts_cost_le adversary q hq)
theorem reference_twoContacts_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 := by
  refine (reference_twoContacts_le_raw adversary q hq).trans (le_of_eq ?_)
  set E := ∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hn0 : (2 : ENNReal) ^ 128 ≠ 0 := by simp
  have hnt : (2 : ENNReal) ^ 128 ≠ ⊤ := by simp
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring
end SigGolfCandidate.T3.Security.Wots
end

section





































section
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
theorem reference_trace_length_le (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : s.trace.length ≤ q := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, hrun, rfl⟩ := hs
  have h1 := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hrun
  have h2 : run ∈ support (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) := by
    revert h1
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl (restTable R))
      (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) run
  have hcount : (run.1, SphincsSecurity.QueryCap.calls RefCharged run.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (restTable R) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨run, h2, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (restTable R) adversary q) _ hcount
  refine le_trans ?_ hle
  show (traceOf (restTable R) run.2).length ≤ _
  have hf := traceOf_filter_length (restTable R) (fun _ => True) run.2
  simp only [decide_true, List.filter_true] at hf
  rw [hf]
  unfold SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨x, rfl, -⟩ := hq
  trivial
theorem prefixClassCount_le_length (s : RefSample) : prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  have hsize : ∀ c : ChainAddr, WotsExtract.SourceChain c → c.key.tree < 2 ^ 40 ∧ c.key.leaf < 2 ^ 24 := by
    intro c hc
    refine ⟨by have := hc.1.1; omega, ?_⟩
    have h1 := hc.1.2
    have h2 : 2 ^ height c.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le c.key.lay; omega)
    omega
  unfold ContactAt
  rw [depth_maskAt_all T a b (Mask.maskOK_of_lt (hsize a ha).2),
    frontierValue_maskAt_bounded T a b (hsize a ha) (hsize b hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRow a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; rw [hm]
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (prefixRowAt_unique (answers := T) ha hb ⟨_, va, by omega, rfl⟩ ⟨_, vb, by omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(mem_sourceChains b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
theorem reference_twoContacts_le_raw (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      ((2 * q : ℕ) : ENNReal) *
          ((2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
            (1 - (q : ENNReal) / 2 ^ 128)) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      ∑ a ∈ sourceChains, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum sourceChains (referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (mem_sourceChains a).mpr ha, h⟩
    · exact ⟨b, (mem_sourceChains b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ sourceChains) =>
    reference_contactAfterStop_charge adversary q hq a ((mem_sourceChains a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((mem_sourceChains a).mp ha))
  have halloc : ∑ a ∈ sourceChains, ∑' s, referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
        calc ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ sourceChains, prefixCount a s : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := reference_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ sourceChains, prefixCount a s ≤ 2 * q)
      calc referenceExperiment adversary q s * ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (referenceExperiment adversary q s * (contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ sourceChains, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ sourceChains, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains, ∑' s, referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := halloc
    _ ≤ ((2 * q : ℕ) : ENNReal) *
          ((2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
            (1 - (q : ENNReal) / 2 ^ 128)) := mul_le_mul' le_rfl (reference_contacts_cost_le adversary q hq)
theorem reference_twoContacts_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 := by
  refine (reference_twoContacts_le_raw adversary q hq).trans (le_of_eq ?_)
  set E := ∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hn0 : (2 : ENNReal) ^ 128 ≠ 0 := by simp
  have hnt : (2 : ENNReal) ^ 128 ≠ ⊤ := by simp
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]
theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : MarkerAt T trace a) (hc : ContactAt T trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, MarkerAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, MarkerAt T (trace.take k) a ∧ ∀ j < k, ¬MarkerAt T (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, ContactAt T (trace.take k) a ∧ ∀ j < k, ¬ContactAt T (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, answer, digits, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, answer, digits, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, answer, digits, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact SmallA.chainRow_ne_encodingRow _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩
theorem primitive_cases (T : Answers) (trace : List Entry) (h : WotsExtract.WotsPrimitiveSrc T trace) :
    (∃ L, WotsExtract.SourceLeaf L ∧ EncodingMatchAt T trace L) ∨ WotsExtract.StructuralHitSrc T trace ∨
      (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt T trace a) ∨
      (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧ ContactAt T trace a ∧
        ContactAt T trace b) ∨
      (∃ a, WotsExtract.SourceChain a ∧ MarkerFirst T trace a) ∨
      (∃ a, WotsExtract.SourceChain a ∧ ContactFirst T trace a) := by
  rcases h with h | h | h | h | ⟨a, ha, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases markerContact_split T trace a hm hc with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, h'⟩))))
theorem probEvent_le_six {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] + Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p] := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  exact probEvent_or_le _ _ _
def chainOf (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨⟨p.1.lay, p.1.tree.val, p.1.leaf.val⟩, p.2.val⟩
theorem exists_chainOf {a : ChainAddr} (ha : WotsExtract.SourceChain a) : ∃ p, chainOf p = a := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
end SmallP
open SmallP
def TwoContactsBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
      ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
    (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
      (1 - (q : ENNReal) / 2 ^ 128) ^ 2
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    57 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount
noncomputable def prefixCoeff (q : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
      (1 - (q : ENNReal) / 2 ^ 128) +
    4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
    2 * 57 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeff (q : Nat) : ENNReal :=
  1 + 2 * 3306 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
theorem reference_markerFirst_sum_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : MarkerSumBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ MarkerFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerFirst s.answers s.trace (chainOf p) |
          referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerAt s.answers s.trace (chainOf p) |
            referenceExperiment adversary q] := by
    intro p
    by_cases hs : WotsExtract.SourceChain (chainOf p)
    · simp only [hs, true_and]
      have hC := reference_markerFirst_at_le adversary q hq (chainOf p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (chainOf p)) s.answers s.trace
        (chainOf p) | referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (chainOf p) | referenceExperiment adversary q]
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ MarkerFirst s.answers s.trace a | referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain (chainOf p) ∧ MarkerFirst s.answers s.trace (chainOf p) |
          referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := exists_chainOf ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerFirst s.answers s.trace (chainOf p) |
            referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerAt s.answers s.trace (chainOf p) |
            referenceExperiment adversary q] :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain (chainOf p) ∧ MarkerAt s.answers s.trace (chainOf p) |
              referenceExperiment adversary q] := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact hMS
theorem reference_contactFirst_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hCF : ContactFirstBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      57 * ((q : ENNReal) / 2 ^ 128) *
        ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128)) :=
  hCF.trans (by gcongr; exact reference_contacts_cost_le adversary q hq)
theorem reference_primitive_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hTC : TwoContactsBound adversary q) (hCF : ContactFirstBound adversary q) (hMS : MarkerSumBound adversary q) :
    Pr[fun s => WotsExtract.WotsPrimitiveSrc s.answers s.trace | referenceExperiment adversary q] ≤
      prefixCoeff q / 2 ^ 128 * refExpect adversary q prefixClassCount +
        encodingCoeff q / 2 ^ 128 * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount := by
  refine (probEvent_le_six _ _ _ _ _ _ _ _ fun s h => primitive_cases s.answers s.trace h).trans ?_
  have h1 := reference_encodingMatch_le adversary q
  have h2 := reference_structural_src_le adversary q
  have h3 := reference_twoEdge_le adversary q hq
  have h5 := reference_markerFirst_sum_le adversary q hq hMS
  have h6 := reference_contactFirst_cost_le adversary q hq hCF
  calc _ ≤ (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount +
        twoEdgeRate q * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128) +
        (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
          (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ((3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
        57 * ((q : ENNReal) / 2 ^ 128) *
          ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128)) := by
        gcongr
        · exact h1
        · exact h2
        · exact h3
        · exact hTC
    _ = _ := by
        unfold prefixCoeff encodingCoeff twoEdgeRate
        simp only [div_eq_mul_inv]
        ring
end SigGolfCandidate.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
noncomputable def classRate : ENNReal := 181 / 100
theorem inv_one_sub_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ 8192 / 8191 := by
  calc (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ (8191 / 8192 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv.mpr (SeccClosing.one_sub_x_ge_of_small q hs)
    _ = 8192 / 8191 := ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))
theorem prefixCoeff_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) : prefixCoeff q ≤ classRate := by
  have hx := SeccClosing.x_le_of_small q hs
  have hu := inv_one_sub_le q hs
  unfold prefixCoeff classRate
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), div_eq_mul_inv _ (1 - x), ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc ((3 / 2 : ENNReal) + 4 * x + 2 * x ^ 2) * u + 4 * x * u ^ 2 + 2 * 57 * x * u
      ≤ ((3 / 2 : ENNReal) + 4 * ((2:ENNReal)^13)⁻¹ + 2 * (((2:ENNReal)^13)⁻¹)^2) * (8192/8191) +
          4 * ((2:ENNReal)^13)⁻¹ * (8192/8191)^2 + 2 * 57 * ((2:ENNReal)^13)⁻¹ * (8192/8191) := by
        gcongr
    _ ≤ 181 / 100 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num
theorem encodingCoeff_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) : encodingCoeff q ≤ classRate := by
  have hx := SeccClosing.x_le_of_small q hs
  have hu := inv_one_sub_le q hs
  unfold encodingCoeff classRate
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x)]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (1 : ENNReal) + 2 * 3306 * x * u ≤ 1 + 2 * 3306 * ((2:ENNReal)^13)⁻¹ * (8192/8191) := by gcongr
    _ ≤ 181 / 100 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem one_le_classRate : (1 : ENNReal) ≤ classRate := by
  unfold classRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem digestRate_le : 1 + SeccClosing.cacheRate ≤ classRate := by
  unfold classRate
  rw [SeccClosing.cacheRate_def]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem excess_le (q : Nat) :
    ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 ≤ (13 / 500) * ((q : ENNReal) / 2 ^ 128) := by
  rw [SeccClosing.excessRate_def]
  unfold signRatio
  push_cast
  simp only [div_eq_mul_inv]
  calc (201 : ENNReal) * q * (12500 * 100000000⁻¹) * (2 ^ 128)⁻¹
      = (201 * (12500 * 100000000⁻¹)) * (q * (2 ^ 128)⁻¹) := by ring
    _ ≤ (13 * 500⁻¹) * (q * (2 ^ 128)⁻¹) := by
        gcongr ?_ * _
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
          ENNReal.toReal_one]
        norm_num
theorem nearTerm_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    nearTerm q ≤ 405 * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 1000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosing.div_sub_le_of_small q hs
  unfold nearTerm nearPrice signRatio
  rw [SeccClosing.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : (404 : ENNReal) * q / 2 ^ 128 + 21 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      21 * (2 : ENNReal)⁻¹ ^ 700 =
      (404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 21 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 21 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (8192 / 8191 * x) * ((404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 21 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (8192 / 8191 * (404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (8192 / 8191 * (21 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ 405 * x ^ 2 + (1 / 1000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num
theorem pairTerm_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    BPair.pairTerm q ≤ 2 * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hg := SeccClosing.div_sub_le_of_small q hs
  have hc : (q.choose 2 : ENNReal) ≤ (q : ENNReal) * q := by
    have : q.choose 2 ≤ q * q := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  unfold BPair.pairTerm
  calc (q.choose 2 : ENNReal) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2
      ≤ ((q : ENNReal) * q) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2 := by gcongr
    _ = ((q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal)) ^ 2 := by rw [div_eq_mul_inv]; ring
    _ ≤ (8192 / 8191 * ((q : ENNReal) / 2 ^ 128)) ^ 2 := by gcongr
    _ = (8192 / 8191 : ENNReal) ^ 2 * ((q : ENNReal) / 2 ^ 128) ^ 2 := mul_pow _ _ _
    _ ≤ 2 * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        gcongr
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num
end SmallR
open SmallR
theorem twoContactsBound (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) : TwoContactsBound adversary q :=
  reference_twoContacts_le adversary q hq
theorem markerSumBound (adversary : AdversaryP) (q : Nat) : MarkerSumBound adversary q :=
  reference_marker_sum_le adversary q
theorem contactFirstBound (adversary : AdversaryP) (q : Nat) : ContactFirstBound adversary q :=
  reference_contactFirst_le adversary q
theorem cleanWin_le_cases (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) (probEvent_or_le _ _ _)
  intro z hz hclean
  rcases completed_split_src adversary q hq z hz hclean with h | h | h
  · exact Or.inl ⟨hclean, h⟩
  · exact Or.inr ⟨hclean, h⟩
  · exact absurd h (caseCSignedPinned_impossible adversary q hq z hz hclean)
theorem small_route (hC : CaseCSmallBound) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q := by
  intro adversary q hq hq1 hs
  have hq128 : q < 2 ^ 128 := lt_of_le_of_lt hq (by norm_num)
  have hbudget := reference_class_budget adversary q hq
  have hab := (caseABSrc_le_reference adversary q hq).trans (reference_primitive_le adversary q hq128
    (twoContactsBound adversary q hq128) (contactFirstBound adversary q) (markerSumBound adversary q))
  have hc := hC adversary q hq hq1 hs
  have k1 : prefixCoeff q / 2 ^ 128 ≤ classRate / 2 ^ 128 := by gcongr; exact prefixCoeff_le q hs
  have k2 : encodingCoeff q / 2 ^ 128 ≤ classRate / 2 ^ 128 := by gcongr; exact encodingCoeff_le q hs
  have k3 : (2 ^ 128 : ENNReal)⁻¹ ≤ classRate / 2 ^ 128 := by
    rw [← one_div]; exact ENNReal.div_le_div_right one_le_classRate _
  have k4 : (1 + SeccClosing.cacheRate) / 2 ^ 128 ≤ classRate / 2 ^ 128 := by gcongr; exact digestRate_le
  generalize refExpect adversary q prefixClassCount = EP at hbudget hab
  generalize refExpect adversary q encodingCount = EE at hbudget hab
  generalize refExpect adversary q otherCount = EO at hbudget hab
  generalize SeccLaw.expectedCharge adversary q hq digestClass = EM at hbudget hc
  have hcq : classRate / 2 ^ 128 * (EP + EE + EO + EM) ≤ classRate * ((q : ENNReal) / 2 ^ 128) := by
    calc classRate / 2 ^ 128 * (EP + EE + EO + EM) ≤ classRate / 2 ^ 128 * q := by gcongr
      _ = classRate * ((q : ENNReal) / 2 ^ 128) := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hex := excess_le q
  have hnear := nearTerm_le q hs
  have hpair := pairTerm_le q hs
  apply SeccClosing.smallBound_of_le q _ (classRate + 13 / 500 + 1 / 1000) 407 ((2 : ENNReal)⁻¹ ^ 700)
  · rw [SeccClosing.smallCoefficient_def]
    unfold classRate
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  · rw [SeccClosing.smallQuadratic_def]
    exact_mod_cast (by norm_num : (407 : ℕ) ≤ 2 ^ 9)
  · rw [SeccClosing.smallAbsolute_def, ← ENNReal.inv_pow]
    exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ one_le_two (by norm_num : 132 ≤ 700))
  generalize (q : ENNReal) / 2 ^ 128 = x at hcq hex hnear hpair
  calc Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z |
            SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
            SeccLaw.completedExperiment adversary q hq] := cleanWin_le_cases adversary q hq
    _ ≤ (prefixCoeff q / 2 ^ 128 * EP + encodingCoeff q / 2 ^ 128 * EE + (2 ^ 128 : ENNReal)⁻¹ * EO) +
          ((1 + SeccClosing.cacheRate) / 2 ^ 128 * EM +
            ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
            (2 : ENNReal)⁻¹ ^ 700) := add_le_add hab hc
    _ ≤ (classRate / 2 ^ 128 * EP + classRate / 2 ^ 128 * EE + classRate / 2 ^ 128 * EO) +
          (classRate / 2 ^ 128 * EM + 13 / 500 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 +
            (2 : ENNReal)⁻¹ ^ 700) := by gcongr
    _ = classRate / 2 ^ 128 * (EP + EE + EO + EM) +
          (13 / 500 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700) := by ring
    _ ≤ classRate * x + (13 / 500 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (classRate + 13 / 500 + 1 / 1000) * x + 407 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700 := by ring
theorem securityP_of_small (hC : CaseCSmallBound)
    (hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.largeBound q) :
    SecurityP :=
  SeccClosing.securityP_of_routes (small_route hC) hlarge
end SigGolfCandidate.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
open SigGolfCandidate.T3.Security.Wots.SmallP (mem_take_succ probEvent_le_six)
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : MarkerAt T trace a) (hc : ContactAt T trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, MarkerAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, MarkerAt T (trace.take k) a ∧ ∀ j < k, ¬MarkerAt T (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, ContactAt T (trace.take k) a ∧ ∀ j < k, ¬ContactAt T (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact ClaudeWCT.W9.T3.Security.Wots.SmallA.chainRow_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩
theorem primitive_cases (T : Answers) (trace : List Entry) (h : WotsExtract.WotsPrimitiveSrc T trace) :
    (∃ L, WotsExtract.SourceLeaf L ∧ EncodingMatchAt T trace L) ∨ WotsExtract.StructuralHitSrc T trace ∨
      (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt T trace a) ∨
      (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧ ContactAt T trace a ∧
        ContactAt T trace b) ∨
      (∃ a, WotsExtract.SourceChain a ∧ MarkerFirst T trace a) ∨
      (∃ a, WotsExtract.SourceChain a ∧ ContactFirst T trace a) := by
  rcases h with h | h | h | h | ⟨a, ha, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases markerContact_split T trace a hm hc with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, h'⟩))))
def chainOf (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨⟨p.1.lay, p.1.tree.val, p.1.leaf.val⟩, p.2.val⟩
theorem exists_chainOf {a : ChainAddr} (ha : WotsExtract.SourceChain a) : ∃ p, chainOf p = a := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
end SmallP
def TwoContactsBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
      ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
    (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
      (1 - (q : ENNReal) / 2 ^ 128) ^ 2
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    57 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount
theorem reference_markerFirst_sum_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : MarkerSumBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ SmallP.MarkerFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain (SmallP.chainOf p) ∧ SmallP.MarkerFirst s.answers s.trace (SmallP.chainOf p) |
          referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain (SmallP.chainOf p) ∧ MarkerAt s.answers s.trace (SmallP.chainOf p) |
            referenceExperiment adversary q] := by
    intro p
    by_cases hs : WotsExtract.SourceChain (SmallP.chainOf p)
    · simp only [hs, true_and]
      have hC := reference_markerFirst_at_le adversary q hq (SmallP.chainOf p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (SmallP.chainOf p)) s.answers s.trace
        (SmallP.chainOf p) | referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (SmallP.chainOf p) | referenceExperiment adversary q]
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ SmallP.MarkerFirst s.answers s.trace a | referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain (SmallP.chainOf p) ∧ SmallP.MarkerFirst s.answers s.trace (SmallP.chainOf p) |
          referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := SmallP.exists_chainOf ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain (SmallP.chainOf p) ∧ SmallP.MarkerFirst s.answers s.trace (SmallP.chainOf p) |
            referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain (SmallP.chainOf p) ∧ MarkerAt s.answers s.trace (SmallP.chainOf p) |
            referenceExperiment adversary q] :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain (SmallP.chainOf p) ∧ MarkerAt s.answers s.trace (SmallP.chainOf p) |
              referenceExperiment adversary q] := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact hMS
theorem reference_contactFirst_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hCF : ContactFirstBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      57 * ((q : ENNReal) / 2 ^ 128) *
        ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128)) :=
  hCF.trans (by gcongr; exact reference_contacts_cost_le adversary q hq)
theorem reference_primitive_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hTC : TwoContactsBound adversary q) (hCF : ContactFirstBound adversary q) (hMS : MarkerSumBound adversary q) :
    Pr[fun s => WotsExtract.WotsPrimitiveSrc s.answers s.trace | referenceExperiment adversary q] ≤
      prefixCoeff q / 2 ^ 128 * refExpect adversary q prefixClassCount +
        encodingCoeff q / 2 ^ 128 * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount := by
  refine (SmallP.probEvent_le_six _ _ _ _ _ _ _ _ fun s h => SmallP.primitive_cases s.answers s.trace h).trans ?_
  have h1 := reference_encodingMatch_le adversary q
  have h2 := reference_structural_src_le adversary q
  have h3 := reference_twoEdge_le adversary q hq
  have h5 := reference_markerFirst_sum_le adversary q hq hMS
  have h6 := reference_contactFirst_cost_le adversary q hq hCF
  calc _ ≤ (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount +
        twoEdgeRate q * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128) +
        (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
          (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ((3306 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
        57 * ((q : ENNReal) / 2 ^ 128) *
          ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount / (1 - (q : ENNReal) / 2 ^ 128)) := by
        gcongr
        · exact h1
        · exact h2
        · exact h3
        · exact hTC
    _ = _ := by
        unfold prefixCoeff encodingCoeff twoEdgeRate
        simp only [div_eq_mul_inv]
        ring
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
theorem near_rate : (8192/8191 : ℚ) * (404 + 63 * 201 / 2 ^ 25) ≤ 405 := by norm_num
theorem near_slack : 405 - (8192/8191 : ℚ) * (404 + 63 * 201 / 2 ^ 25) = 31882889 / 33550336 := by norm_num
theorem nearTerm_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    nearTerm q ≤ 405 * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 1000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosing.div_sub_le_of_small q hs
  unfold nearTerm nearPrice signRatio
  rw [SeccClosing.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : (404 : ENNReal) * q / 2 ^ 128 + 63 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      63 * (2 : ENNReal)⁻¹ ^ 700 =
      (404 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 63 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((404 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (8192 / 8191 * x) * ((404 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (8192 / 8191 * (404 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (8192 / 8191 * (63 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ 405 * x ^ 2 + (1 / 1000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num
end SmallR
theorem twoContactsBound (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) : TwoContactsBound adversary q :=
  reference_twoContacts_le adversary q hq
theorem markerSumBound (adversary : AdversaryP) (q : Nat) : MarkerSumBound adversary q :=
  reference_marker_sum_le adversary q
theorem contactFirstBound (adversary : AdversaryP) (q : Nat) : ContactFirstBound adversary q :=
  reference_contactFirst_le adversary q
theorem cleanWin_le_cases (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) ((probEvent_or_le _ _ _).trans (by gcongr; exact probEvent_or_le _ _ _))
  intro z hz hclean
  by_cases hcomp : BPB.SignerComplete z.2
  · rcases completed_split_src adversary q hq z hz hclean hcomp with h | h | h
    · exact Or.inl (Or.inl ⟨hclean, h⟩)
    · exact Or.inl (Or.inr ⟨hclean, h⟩)
    · exact absurd h (CaseC.caseCSignedPinned_impossible adversary q hq z hz hclean)
  · exact Or.inr hcomp
theorem small_route (hC : CaseCSmallBound) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q := by
  intro adversary q hq hq1 hs
  have hq128 : q < 2 ^ 128 := lt_of_le_of_lt hq (by norm_num)
  have hbudget := reference_class_budget adversary q hq
  have hab := (caseABSrc_le_reference adversary q hq).trans (reference_primitive_le adversary q hq128
    (twoContactsBound adversary q hq128) (contactFirstBound adversary q) (markerSumBound adversary q))
  have hc := hC adversary q hq hq1 hs
  have k1 : prefixCoeff q / 2 ^ 128 ≤ SmallR.classRate / 2 ^ 128 := by gcongr; exact SmallR.prefixCoeff_le q hs
  have k2 : encodingCoeff q / 2 ^ 128 ≤ SmallR.classRate / 2 ^ 128 := by gcongr; exact SmallR.encodingCoeff_le q hs
  have k3 : (2 ^ 128 : ENNReal)⁻¹ ≤ SmallR.classRate / 2 ^ 128 := by
    rw [← one_div]; exact ENNReal.div_le_div_right SmallR.one_le_classRate _
  have k4 : (1 + SeccClosing.cacheRate) / 2 ^ 128 ≤ SmallR.classRate / 2 ^ 128 := by gcongr; exact SmallR.digestRate_le
  generalize refExpect adversary q prefixClassCount = EP at hbudget hab
  generalize refExpect adversary q encodingCount = EE at hbudget hab
  generalize refExpect adversary q otherCount = EO at hbudget hab
  generalize SeccLaw.expectedCharge adversary q hq digestClass = EM at hbudget hc
  have hcq : SmallR.classRate / 2 ^ 128 * (EP + EE + EO + EM) ≤ SmallR.classRate * ((q : ENNReal) / 2 ^ 128) := by
    calc SmallR.classRate / 2 ^ 128 * (EP + EE + EO + EM) ≤ SmallR.classRate / 2 ^ 128 * q := by gcongr
      _ = SmallR.classRate * ((q : ENNReal) / 2 ^ 128) := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hex := SmallR.excess_le q
  have hnear := SmallR.nearTerm_le q hs
  have hpair := SmallR.pairTerm_le q hs
  have hinc := BPB.signerIncomplete_le adversary q hq
  apply SeccClosing.smallBound_of_le q _ (SmallR.classRate + 13 / 500 + 1 / 1000) 407
    ((2 : ENNReal)⁻¹ ^ 700 + 1 / (2 : ENNReal) ^ 722)
  · rw [SeccClosing.smallCoefficient_def]
    unfold SmallR.classRate
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  · rw [SeccClosing.smallQuadratic_def]
    exact_mod_cast (by norm_num : (407 : ℕ) ≤ 2 ^ 9)
  · rw [SeccClosing.smallAbsolute_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  generalize (q : ENNReal) / 2 ^ 128 = x at hcq hex hnear hpair
  calc Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z |
            SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z |
            SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] :=
        cleanWin_le_cases adversary q hq
    _ ≤ (prefixCoeff q / 2 ^ 128 * EP + encodingCoeff q / 2 ^ 128 * EE + (2 ^ 128 : ENNReal)⁻¹ * EO) +
          ((1 + SeccClosing.cacheRate) / 2 ^ 128 * EM +
            ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
            (2 : ENNReal)⁻¹ ^ 700) + 1 / (2 : ENNReal) ^ 722 := add_le_add (add_le_add hab hc) hinc
    _ ≤ (SmallR.classRate / 2 ^ 128 * EP + SmallR.classRate / 2 ^ 128 * EE + SmallR.classRate / 2 ^ 128 * EO) +
          (SmallR.classRate / 2 ^ 128 * EM + 13 / 500 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 +
            (2 : ENNReal)⁻¹ ^ 700) + 1 / (2 : ENNReal) ^ 722 := by gcongr
    _ = SmallR.classRate / 2 ^ 128 * (EP + EE + EO + EM) +
          (13 / 500 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + ((2 : ENNReal)⁻¹ ^ 700 + 1 / (2 : ENNReal) ^ 722)) := by
        ring
    _ ≤ SmallR.classRate * x + (13 / 500 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 +
          ((2 : ENNReal)⁻¹ ^ 700 + 1 / (2 : ENNReal) ^ 722)) := by
        gcongr
    _ = (SmallR.classRate + 13 / 500 + 1 / 1000) * x + 407 * x ^ 2 + ((2 : ENNReal)⁻¹ ^ 700 + 1 / (2 : ENNReal) ^ 722) := by
        ring
theorem securityP_of_small (hC : CaseCSmallBound)
    (hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.largeBound q) :
    SecurityP := by
  apply PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  have key : Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] + SeccClosing.secTerms q ≤
      (q : ENNReal) / 2 ^ 127 := by
    by_cases hs : q ≤ SeccClosing.budgetSplit
    · exact (add_le_add (small_route hC adversary q hq hpositive hs) le_rfl).trans
        (SeccClosing.small_closing q hpositive hs)
    · exact (add_le_add (hlarge adversary q hq (by omega)) le_rfl).trans
        (SeccClosing.large_closing q (by omega) hq)
  simpa only [SeccClosing.secTerms, add_assoc] using key
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Secc
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security (SeccClosing.budgetSplit SeccClosing.largeBound QueryRecorded.CleanWin)
open ClaudeWCT.W9.T3M.Final (AdversaryP SecurityP)
def LargeRouteBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq] ≤
      SeccClosing.largeBound q
theorem caseCSmallBound_of
    (hnear : ClaudeWCT.W9.T3.Security.CaseC.NearBound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
      ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.Wots.nearTerm)
    (hpair : ClaudeWCT.W9.T3.Security.WPair.PairGuessBound SigGolfCandidate.T3.Security.BPair.pairTerm) :
    ClaudeWCT.W9.T3.Security.Wots.CaseCSmallBound :=
  ClaudeWCT.W9.T3.Security.CaseC.caseC_small_bound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
    (ClaudeWCT.W9.T3.Security.CaseC.caseCSplitInterface SigGolfCandidate.T3.Security.BPair.pairTerm hpair)
    ClaudeWCT.W9.T3.Security.Wots.nearTerm ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32 hnear
theorem t3_securityP
    (hnear : ClaudeWCT.W9.T3.Security.CaseC.NearBound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
      ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.Wots.nearTerm)
    (hpair : ClaudeWCT.W9.T3.Security.WPair.PairGuessBound SigGolfCandidate.T3.Security.BPair.pairTerm)
    (hlarge : LargeRouteBound) : SecurityP :=
  ClaudeWCT.W9.T3.Security.Wots.securityP_of_small (caseCSmallBound_of hnear hpair) hlarge
end ClaudeWCT.W9.T3.Secc
end
end
