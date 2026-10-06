import SigGolfCandidate.T3.Secc.WotsEncodingResample
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingCongr

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
open SigGolfCandidate.T3.Security.Wots.Enc (tsum_uniform_coe)
def EncOk (lay : Layer) (msg : WCT9.LayerMsg) (pad : BitVec 96) : Prop :=
  Extract.msgFits lay msg ∧ (lay.val = 3 → pad = 0)
abbrev EncIndex := {e : CanonGraph.LeafPos × WCT9.LayerMsg × BitVec 32 × BitVec 96 // EncOk e.1.lay e.2.1 e.2.2.2}
instance encIndex_finite : Finite EncIndex := by
  haveI : Finite WCT9.LayerMsg := Finite.of_equiv _ CanonGraph.layerMsgEquiv.symm
  infer_instance
def encInput (e : EncIndex) : HashInput := encRow (leafOf e.1.1) e.1.2.1 e.1.2.2.1 e.1.2.2.2
def encIdx (L : CanonGraph.LeafPos) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96)
    (hfit : Extract.msgFits L.lay msg) : EncIndex :=
  ⟨(L, msg, counter, if L.lay.val = 3 then 0 else pad), hfit, fun h => if_pos h⟩
theorem encInput_encIdx (L : CanonGraph.LeafPos) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96)
    (hfit : Extract.msgFits L.lay msg) : encInput (encIdx L msg counter pad hfit) = encRow (leafOf L) msg counter pad := by
  unfold encInput encIdx
  dsimp only
  split_ifs with h3
  · cases msg with
    | forest root => rfl
    | pair l r =>
        change L.lay.val < 3 at hfit
        omega
  · rfl
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 :=
  ClaudeWCT.W9.T3M.BC.layerEncodingRow_length _ _ _ _ _ _
theorem encInput_injective : Function.Injective encInput := by
  rintro ⟨⟨L, m, c, p⟩, hf, hp⟩ ⟨⟨L', m', c', p'⟩, hf', hp'⟩ he
  have ht : L.tree.val < 2 ^ 40 := lt_of_lt_of_le L.tree.isLt (by norm_num)
  have ht' : L'.tree.val < 2 ^ 40 := lt_of_lt_of_le L'.tree.isLt (by norm_num)
  have hl : L.leaf.val < 2 ^ 32 := lt_of_lt_of_le L.leaf.isLt (by norm_num)
  have hl' : L'.leaf.val < 2 ^ 32 := lt_of_lt_of_le L'.leaf.isLt (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_injective ht hl ht' hl' hf hf' he
  obtain ⟨lay, tree, leaf⟩ := L
  obtain ⟨lay', tree', leaf'⟩ := L'
  simp only at h1 h2 h3 hf hp hf' hp'
  subst h1 h4 h5
  have : tree = tree' := Fin.ext h2
  have : leaf = leaf' := Fin.ext h3
  subst tree leaf
  have hpp : p = p' := by
    cases m with
    | forest root =>
        change lay.val = 3 at hf
        rw [hp hf, hp' hf]
    | pair l r => exact h6 l r rfl
  subst hpp
  rfl
theorem encInput_short (e : EncIndex) : encInput e ∈ SeccLaw.publicUniverse :=
  SeccLaw.mem_publicUniverse _ (by rw [encInput_length]; unfold SeccLaw.maxInputLength; omega)
theorem encInput_encHeader (e : EncIndex) : EncHeader (encInput e) :=
  ⟨e.1.1.lay.val, e.1.1.tree.val, 0, e.1.1.leaf.val,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _⟩
theorem reached_encInput {T : Answers} {L : CanonGraph.LeafPos} {input : HashInput}
    (h : Reached T (leafOf L) input) :
    ∃ c : BitVec 32, input = encInput ⟨(L, leafMsg T (leafOf L), c, 0), msgFits_leafMsg T (leafOf L), fun _ => rfl⟩ := by
  obtain ⟨c, -, rfl, -⟩ := h
  exact ⟨_, rfl⟩
def Free (T : Answers) (e : EncIndex) : Prop := ¬ Reached T (leafOf e.1.1) (encInput e)
def freeSet (T : Answers) : Set EncIndex := {e | Free T e}
theorem encRow_hdr (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96) :
    Extract.hdrBlock (encRow L msg counter pad) = bytesLE 16 (header 4 L.lay.val L.tree 0 L.leaf) :=
  ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _
theorem encInput_hdr (e : EncIndex) :
    Extract.hdrBlock (encInput e) = bytesLE 16 (header 4 e.1.1.lay.val e.1.1.tree.val 0 e.1.1.leaf.val) :=
  ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _
noncomputable def rowDec (T A : Answers) (L : CanonGraph.LeafPos) (c : Nat) : Option (List Nat) :=
  WCT9.producerDecode (leafOf L).lay (low (A (.inl (.inr (encRow (leafOf L) (leafMsg T (leafOf L))
    (BitVec.ofNat 32 c) 0)))))
theorem rowDec_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (L : CanonGraph.LeafPos) (c : Nat)
    (hc : c < WCT9.searchLimit (leafOf L).lay) (hprev : ∀ c' < c, rowDec T T L c' = none) :
    rowDec T T' L c = none ↔ rowDec T T L c = none := by
  rcases h (.inl (.inr (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c) 0)))
      (Or.inr ⟨L, c, hc, rfl, hprev⟩) with he | hrej
  · unfold rowDec
    rw [he]
  · obtain ⟨hT, hT'⟩ := hrej.layer (encRow_hdr (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c) 0)
    exact ⟨fun _ => hT, fun _ => hT'⟩
theorem rowDec_prefix_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (L : CanonGraph.LeafPos) :
    ∀ c, c ≤ WCT9.searchLimit (leafOf L).lay →
      ((∀ c' < c, rowDec T T' L c' = none) ↔ ∀ c' < c, rowDec T T L c' = none) := by
  intro c
  induction c with
  | zero =>
      intro _
      exact ⟨fun _ c' hc' => absurd hc' (Nat.not_lt_zero _), fun _ c' hc' => absurd hc' (Nat.not_lt_zero _)⟩
  | succ c ih =>
      intro hc
      have ih' := ih (by omega)
      constructor
      · intro hT' c' hc'
        have hprev := ih'.mp (fun c'' hc'' => hT' c'' (by omega))
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · exact hprev c' hlt
        · exact (rowDec_congr h L c' (by omega) hprev).mp (hT' c' (by omega))
      · intro hT c' hc'
        have hprev : ∀ c'' < c, rowDec T T L c'' = none := fun c'' hc'' => hT c'' (by omega)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · exact ih'.mpr hprev c' hlt
        · exact (rowDec_congr h L c' (by omega) hprev).mpr (hT c' (by omega))
theorem reached_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (L : CanonGraph.LeafPos)
    (input : HashInput) : Reached T' (leafOf L) input ↔ Reached T (leafOf L) input := by
  have hm : leafMsg T' (leafOf L) = leafMsg T (leafOf L) := leafMsg_congr_nonEnc (nonEnc_of_honest h) _
  unfold Reached
  rw [hm]
  constructor
  · rintro ⟨c, hc, rfl, hprev⟩
    exact ⟨c, hc, rfl, (rowDec_prefix_congr h L c (le_of_lt hc)).mp hprev⟩
  · rintro ⟨c, hc, rfl, hprev⟩
    exact ⟨c, hc, rfl, (rowDec_prefix_congr h L c (le_of_lt hc)).mpr hprev⟩
theorem free_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : freeSet T' = freeSet T := by
  ext e
  simp only [freeSet, Set.mem_ofPred_eq, Free]
  rw [reached_congr h]
section Overwrite
variable {U : Finset HashInput}
noncomputable def ov (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) : U → HashOutput :=
  fun u => if h : ∃ e, e ∈ k ∧ encInput e = u.val then y ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else pub u
noncomputable def rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) :
    k → HashOutput :=
  fun e => pub ⟨encInput e.val, hU (encInput_short e.val)⟩
theorem ov_at (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput)
    (e : k) : ov k pub y ⟨encInput e.val, hU (encInput_short e.val)⟩ = y e := by
  unfold ov
  have h : ∃ e', e' ∈ k ∧ encInput e' = encInput e.val := ⟨e.val, e.property, rfl⟩
  rw [dif_pos h]
  have he : Classical.choose h = e.val := encInput_injective (Classical.choose_spec h).2
  congr 1
  exact Subtype.ext he
theorem ov_other (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) (u : U)
    (hu : ∀ e, e ∈ k → encInput e ≠ u.val) : ov k pub y u = pub u := by
  unfold ov
  rw [dif_neg]
  rintro ⟨e, he, heq⟩
  exact hu e he heq
theorem rd_ov (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) :
    rd hU k (ov k pub y) = y := by
  funext e
  exact ov_at hU k pub y e
theorem ov_ov_rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput)
    (y : k → HashOutput) : ov k (ov k pub y) (rd hU k pub) = pub := by
  funext u
  unfold ov
  split_ifs with h
  · unfold rd
    congr 1
    exact Subtype.ext ((Classical.choose_spec h).2)
  · rfl
end Overwrite
section Tables
variable (U : Finset HashInput)
theorem honest_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    ∀ q, HonestQ (eagerAnswers U privateTable pub) q →
      eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) q =
        eagerAnswers U privateTable pub q := by
  intro q hq
  rcases q with (coin | input) | coordinate
  · simp only [eagerAnswers]
  · by_cases hin : input ∈ U
    · rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
        eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
      apply ov_other
      intro e he heq
      rcases hq with hnon | ⟨L, hr⟩
      · have h' : encInput e = input := heq
        exact hnon (h' ▸ encInput_encHeader e)
      · obtain ⟨c, hc⟩ := reached_encInput hr
        have hee := encInput_injective ((show encInput e = input from heq).trans hc)
        apply he
        rw [hee, ← hc]
        exact hr
    · rw [eagerAnswers_public_not_mem U _ _ input hin, eagerAnswers_public_not_mem U _ _ input hin]
  · simp only [eagerAnswers]
theorem free_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    freeSet (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) =
      freeSet (eagerAnswers U privateTable pub) :=
  free_congr (AgreeOn.of_eq (honest_ov U privateTable pub y))
theorem public_resample (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput))
    [Fintype (U → HashOutput)] (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
          F (ov (freeSet (eagerAnswers U privateTable pub)) pub y) :=
  @uniform_resample_tsum (U → HashOutput) (Set EncIndex) _ _ (fun k : Set EncIndex => k → HashOutput) iX _
    (fun pub => freeSet (eagerAnswers U privateTable pub)) (fun k pub y => ov k pub y) (fun k pub => rd hU k pub)
    (fun pub y => rd_ov hU _ pub y) (fun pub y => ov_ov_rd hU _ pub y) (fun pub y => free_ov U privateTable pub y) F
def Rej (T : Answers) (e : EncIndex) : Prop :=
  Reached T (leafOf e.1.1) (encInput e) ∧ WCT9.producerDecode e.1.1.lay (low (T (.inl (.inr (encInput e))))) = none
def cellSet (T : Answers) : Set EncIndex := {e | Free T e ∨ Rej T e}
noncomputable def rejAnswers (lay : Layer) : Finset HashOutput :=
  Finset.univ.filter fun a => WCT9.producerDecode lay (low a) = none
theorem mem_rejAnswers (lay : Layer) (a : HashOutput) :
    a ∈ rejAnswers lay ↔ WCT9.producerDecode lay (low a) = none := by
  simp only [rejAnswers, Finset.mem_filter, Finset.mem_univ, true_and]
theorem producerDecode_allOnes (lay : Layer) : WCT9.producerDecode lay (low (BitVec.allOnes 256)) = none := by
  fin_cases lay <;> decide +kernel
theorem rejAnswers_nonempty (lay : Layer) : (rejAnswers lay).Nonempty :=
  ⟨BitVec.allOnes 256, (mem_rejAnswers lay _).mpr (producerDecode_allOnes lay)⟩
abbrev CellKey := Set EncIndex × Set EncIndex
def cellKey (T : Answers) : CellKey := (cellSet T, freeSet T)
noncomputable def cellInit (k : CellKey) (e : k.1) : Finset HashOutput :=
  if e.val ∈ k.2 then Finset.univ else rejAnswers e.val.1.1.lay
theorem cellInit_nonempty (k : CellKey) (e : k.1) : (cellInit k e).Nonempty := by
  unfold cellInit
  split_ifs
  · exact Finset.univ_nonempty
  · exact rejAnswers_nonempty _
theorem rej_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (e : EncIndex) : Rej T' e ↔ Rej T e := by
  constructor
  · rintro ⟨hr', hv'⟩
    have hr := (reached_congr h e.1.1 _).mp hr'
    refine ⟨hr, ?_⟩
    obtain ⟨c, hc, hin, hprev⟩ := hr
    rw [hin] at hv' ⊢
    exact (rowDec_congr h e.1.1 c hc hprev).mp hv'
  · rintro ⟨hr, hv⟩
    refine ⟨(reached_congr h e.1.1 _).mpr hr, ?_⟩
    obtain ⟨c, hc, hin, hprev⟩ := hr
    rw [hin] at hv ⊢
    exact (rowDec_congr h e.1.1 c hc hprev).mpr hv
theorem cellKey_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : cellKey T' = cellKey T := by
  have hf := free_congr h
  refine Prod.ext ?_ hf
  ext e
  have hfe : Free T' e ↔ Free T e := by
    have := congrArg (fun s : Set EncIndex => e ∈ s) hf
    simpa only [freeSet, Set.mem_setOf_eq, eq_iff_iff] using this
  show (Free T' e ∨ Rej T' e) ↔ (Free T e ∨ Rej T e)
  rw [hfe, rej_congr h]
theorem rej_of_cell {T : Answers} {e : EncIndex} (he : e ∈ (cellKey T).1) (hf : e ∉ (cellKey T).2) : Rej T e := by
  rcases he with h | h
  · exact absurd h hf
  · exact h
theorem agree_ovc (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : (cellKey (eagerAnswers U privateTable pub)).1 → HashOutput)
    (hy : ∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e) :
    AgreeOn (HonestQ (eagerAnswers U privateTable pub)) (eagerAnswers U privateTable pub)
      (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) := by
  intro q hq
  rcases q with (coin | input) | coordinate
  · left; simp only [eagerAnswers]
  · by_cases hin : input ∈ U
    · by_cases hcell : ∃ e, e ∈ (cellKey (eagerAnswers U privateTable pub)).1 ∧ encInput e = input
      · obtain ⟨e, he, rfl⟩ := hcell
        right
        rcases hq with hnon | ⟨L, hr⟩
        · exact absurd (encInput_encHeader e) hnon
        · obtain ⟨c, hc⟩ := reached_encInput hr
          have hee := encInput_injective hc
          have hr' : Reached (eagerAnswers U privateTable pub) (leafOf e.1.1) (encInput e) := by
            rw [hee]
            rw [hee] at hr
            exact hr
          have hnf : e ∉ (cellKey (eagerAnswers U privateTable pub)).2 := fun hfree => hfree hr'
          have hrej := rej_of_cell he hnf
          refine RejPair.mk (encInput_hdr e) hrej.2 ?_
          rw [eagerAnswers_public_mem U privateTable _ ⟨encInput e, hin⟩]
          have hat := ov_at hU (cellKey (eagerAnswers U privateTable pub)).1 pub y ⟨e, he⟩
          rw [hat]
          have hmem := hy ⟨e, he⟩
          unfold cellInit at hmem
          rw [if_neg hnf] at hmem
          exact (mem_rejAnswers _ _).mp hmem
      · left
        rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
          eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
        exact ov_other _ _ _ _ (fun e he heq => hcell ⟨e, he, heq⟩)
    · left
      rw [eagerAnswers_public_not_mem U _ _ input hin, eagerAnswers_public_not_mem U _ _ input hin]
  · left; simp only [eagerAnswers]
theorem cellKey_ovc (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : (cellKey (eagerAnswers U privateTable pub)).1 → HashOutput)
    (hy : ∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e) :
    cellKey (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) =
      cellKey (eagerAnswers U privateTable pub) :=
  cellKey_congr (agree_ovc U hU privateTable pub y hy)
theorem rd_cellInit (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (e : (cellKey (eagerAnswers U privateTable pub)).1) :
    rd hU (cellKey (eagerAnswers U privateTable pub)).1 pub e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e := by
  unfold cellInit
  split_ifs with hf
  · exact Finset.mem_univ _
  · have hrej := rej_of_cell e.property hf
    rw [mem_rejAnswers]
    have h2 := hrej.2
    rw [eagerAnswers_public_mem U privateTable _ ⟨encInput e.val, hU (encInput_short e.val)⟩] at h2
    exact h2
set_option maxRecDepth 100000 in
theorem public_resample_cells [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    [Fintype (U → HashOutput)] (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
            (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
          F (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y) := by
  let A : ∀ k : CellKey, Finset (k.1 → HashOutput) := fun k => Fintype.piFinset (cellInit k)
  have hA : ∀ k, (A k).Nonempty := fun k => Fintype.piFinset_nonempty.mpr (cellInit_nonempty k)
  have iN : ∀ k, Nonempty ↥(A k) := fun k => (hA k).to_subtype
  let rd' : ∀ k : CellKey, (U → HashOutput) → ↥(A k) := fun k pub =>
    if h : rd hU k.1 pub ∈ A k then ⟨rd hU k.1 pub, h⟩ else Classical.choice (iN k)
  have hmem : ∀ pub, rd hU (cellKey (eagerAnswers U privateTable pub)).1 pub ∈
      A (cellKey (eagerAnswers U privateTable pub)) :=
    fun pub => Fintype.mem_piFinset.mpr (rd_cellInit U hU privateTable pub)
  have hrdv : ∀ (k : CellKey) (pub' : U → HashOutput) (h : rd hU k.1 pub' ∈ A k),
      rd' k pub' = ⟨rd hU k.1 pub', h⟩ := by
    intro k pub' h
    show (if h : rd hU k.1 pub' ∈ A k then (⟨rd hU k.1 pub', h⟩ : ↥(A k)) else Classical.choice (iN k)) = _
    rw [dif_pos h]
  have key := @uniform_resample_tsum (U → HashOutput) CellKey _ _ (fun k => ↥(A k)) (fun k => inferInstance) iN
    (fun pub => cellKey (eagerAnswers U privateTable pub)) (fun k pub x => ov k.1 pub x.val) rd'
    (fun pub x => by
      obtain ⟨xv, xp⟩ := x
      have he : rd hU (cellKey (eagerAnswers U privateTable pub)).1
          (ov (cellKey (eagerAnswers U privateTable pub)).1 pub xv) = xv := rd_ov hU _ pub xv
      have hm : rd hU (cellKey (eagerAnswers U privateTable pub)).1
          (ov (cellKey (eagerAnswers U privateTable pub)).1 pub xv) ∈
          A (cellKey (eagerAnswers U privateTable pub)) := by rw [he]; exact xp
      refine (hrdv _ _ hm).trans ?_
      exact Subtype.mk_eq_mk.mpr he)
    (fun pub x => by
      have h2 := hrdv _ pub (hmem pub)
      show ov (cellKey (eagerAnswers U privateTable pub)).1 (ov (cellKey (eagerAnswers U privateTable pub)).1 pub x.val)
        (rd' (cellKey (eagerAnswers U privateTable pub)) pub).val = pub
      rw [h2]
      exact ov_ov_rd hU _ pub x.val)
    (fun pub x => cellKey_ovc U hU privateTable pub x.val (Fintype.mem_piFinset.mp x.property)) F
  rw [key]
  refine tsum_congr fun pub => ?_
  congr 1
  exact tsum_uniform_coe (A (cellKey (eagerAnswers U privateTable pub))) (hA _) (iN _)
    (fun y => F (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y))
end Tables
end Enc
end ClaudeWCT.W9.T3.Security.Wots
