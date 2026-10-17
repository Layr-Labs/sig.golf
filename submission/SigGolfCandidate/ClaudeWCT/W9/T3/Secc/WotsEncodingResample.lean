import SigGolfCandidate.Research.V7Composed198Gate
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
/-- Canonical encoding-row index: the (unused since nested FTS) forest right slot is 0; the 12-byte pad and the
row tweak's high word (`pad.2.2`, C2/C3 FULL) are part of the row. -/
def EncOk (lay : Layer) (msg : WCT9.LayerMsg) (pad : RowPad) : Prop :=
  Extract.msgFits lay msg ∧ pad.2.1 = 0
abbrev EncIndex :=
  {e : CanonGraph.LeafPos × WCT9.LayerMsg × BitVec 32 × RowPad // e.1.Source ∧ EncOk e.1.lay e.2.1 e.2.2.2}
instance encIndex_finite : Finite EncIndex := by
  haveI : Finite WCT9.LayerMsg := Finite.of_equiv _ CanonGraph.layerMsgEquiv.symm
  infer_instance
def encInput (e : EncIndex) : HashInput := encRow (leafOf e.1.1) e.1.2.1 e.1.2.2.1 e.1.2.2.2
def encIdx (L : CanonGraph.LeafPos) (hs : L.Source) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad)
    (hfit : Extract.msgFits L.lay msg) : EncIndex :=
  ⟨(L, msg, counter, (pad.1, 0, pad.2.2)), hs, hfit, rfl⟩
theorem encInput_encIdx (L : CanonGraph.LeafPos) (hs : L.Source) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : RowPad) (hfit : Extract.msgFits L.lay msg) :
    encInput (encIdx L hs msg counter pad hfit) = encRow (leafOf L) msg counter pad := by
  unfold encInput encIdx
  dsimp only
  cases msg with
  | forest root => exact absurd hfit id
  | pair l r => rfl
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 :=
  ClaudeWCT.W9.T3M.BC.layerEncodingRow_length _ _ _ _ _ _ _ _
theorem encInput_injective : Function.Injective encInput := by
  rintro ⟨⟨L, m, c, p⟩, hs, hf, hp⟩ ⟨⟨L', m', c', p'⟩, hs', hf', hp'⟩ he
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_injective hs.routed.1 hs.routed.2
    hs'.routed.1 hs'.routed.2 hf hf' he
  obtain ⟨lay, tree, leaf⟩ := L
  obtain ⟨lay', tree', leaf'⟩ := L'
  simp only at h1 h2 h3 hf hp hf' hp'
  subst h1 h4 h5
  have : tree = tree' := Fin.ext h2
  have : leaf = leaf' := Fin.ext h3
  subst tree leaf
  have hpp : p = p' := by
    obtain ⟨h6, -, h7⟩ := h6
    have h8 : p.2.2 = p'.2.2 := by
      have := congrArg (fun x : BitVec 64 => x ^^^ 1) h7
      simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using this
    exact Prod.ext h6 (Prod.ext (hp.trans hp'.symm) h8)
  subst hpp
  rfl
theorem encInput_short (e : EncIndex) : encInput e ∈ SeccLaw.publicUniverse :=
  SeccLaw.mem_publicUniverse _ (by rw [encInput_length]; unfold SeccLaw.maxInputLength; omega)
theorem encInput_encHeader (e : EncIndex) : EncHeader (encInput e) :=
  ⟨encInput_length e, e.1.1.lay, e.1.1.tree.val, e.1.1.leaf.val, _,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _ _ _⟩
theorem reached_encInput {T : Answers} {L : CanonGraph.LeafPos} (hs : L.Source) {input : HashInput}
    (h : Reached T (leafOf L) input) :
    ∃ c : BitVec 32,
      input = encInput ⟨(L, leafMsg T (leafOf L), c, 0), hs, msgFits_leafMsg T (leafOf L), rfl⟩ := by
  obtain ⟨c, -, rfl, -⟩ := h
  exact ⟨_, rfl⟩
def Free (T : Answers) (e : EncIndex) : Prop := ¬ Reached T (leafOf e.1.1) (encInput e)
def freeSet (T : Answers) : Set EncIndex := {e | Free T e}
theorem encRow_hdr (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) :
    Extract.hdrBlock (encRow L msg counter pad) =
      bytesLE 16 ((pad.2.2 ^^^ 1) ++ hyperWord L.lay.val (L.tree * 2 ^ height L.lay + L.leaf)) :=
  ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _ _ _
theorem encRow_length (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) :
    (encRow L msg counter pad).length = 64 :=
  ClaudeWCT.W9.T3M.BC.layerEncodingRow_length _ _ _ _ _ _ _ _
theorem encInput_hdr (e : EncIndex) :
    Extract.hdrBlock (encInput e) = bytesLE 16 ((e.1.2.2.2.2.2 ^^^ 1) ++
      hyperWord e.1.1.lay.val (e.1.1.tree.val * 2 ^ height e.1.1.lay + e.1.1.leaf.val)) :=
  ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP _ _ _ _ _ _ _ _
noncomputable def rowDec (T A : Answers) (L : CanonGraph.LeafPos) (c : Nat) : Option (List Nat) :=
  WCT9.producerDecode (leafOf L).lay (WCT9.encodingAnswer (leafOf L).lay (A (.inl (.inr (encRow (leafOf L) (leafMsg T (leafOf L))
    (BitVec.ofNat 32 c) 0)))))
theorem rowDec_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') {L : CanonGraph.LeafPos} (hs : L.Source)
    (c : Nat) (hc : c < WCT9.searchLimit (leafOf L).lay) (hprev : ∀ c' < c, rowDec T T L c' = none) :
    rowDec T T' L c = none ↔ rowDec T T L c = none := by
  rcases h (.inl (.inr (encRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c) 0)))
      (Or.inr ⟨L, hs, c, hc, rfl, hprev⟩) with he | hrej
  · unfold rowDec
    rw [he]
  · obtain ⟨hT, hT'⟩ := hrej.layer (encRow_hdr (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c) 0)
    exact ⟨fun _ => hT, fun _ => hT'⟩
theorem rowDec_prefix_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') {L : CanonGraph.LeafPos}
    (hs : L.Source) :
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
        · exact (rowDec_congr h hs c' (by omega) hprev).mp (hT' c' (by omega))
      · intro hT c' hc'
        have hprev : ∀ c'' < c, rowDec T T L c'' = none := fun c'' hc'' => hT c'' (by omega)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · exact ih'.mpr hprev c' hlt
        · exact (rowDec_congr h hs c' (by omega) hprev).mpr (hT c' (by omega))
theorem reached_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') {L : CanonGraph.LeafPos} (hs : L.Source)
    (input : HashInput) : Reached T' (leafOf L) input ↔ Reached T (leafOf L) input := by
  have hm : leafMsg T' (leafOf L) = leafMsg T (leafOf L) := leafMsg_congr_nonEnc (nonEnc_of_honest h) _
  unfold Reached
  rw [hm]
  constructor
  · rintro ⟨c, hc, rfl, hprev⟩
    exact ⟨c, hc, rfl, (rowDec_prefix_congr h hs c (le_of_lt hc)).mp hprev⟩
  · rintro ⟨c, hc, rfl, hprev⟩
    exact ⟨c, hc, rfl, (rowDec_prefix_congr h hs c (le_of_lt hc)).mpr hprev⟩
theorem free_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : freeSet T' = freeSet T := by
  ext e
  simp only [freeSet, Set.mem_ofPred_eq, Free]
  rw [reached_congr h e.2.1]
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
      rcases hq with hnon | ⟨L, hs, hr⟩
      · have h' : encInput e = input := heq
        exact hnon (h' ▸ encInput_encHeader e)
      · obtain ⟨c, hc⟩ := reached_encInput hs hr
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
  Reached T (leafOf e.1.1) (encInput e) ∧ WCT9.producerDecode e.1.1.lay (WCT9.encodingAnswer e.1.1.lay (T (.inl (.inr (encInput e))))) = none
def cellSet (T : Answers) : Set EncIndex := {e | Free T e ∨ Rej T e}
noncomputable def rejAnswers (lay : Layer) : Finset HashOutput :=
  Finset.univ.filter fun a => WCT9.producerDecode lay (WCT9.encodingAnswer lay a) = none
theorem mem_rejAnswers (lay : Layer) (a : HashOutput) :
    a ∈ rejAnswers lay ↔ WCT9.producerDecode lay (WCT9.encodingAnswer lay a) = none := by
  simp only [rejAnswers, Finset.mem_filter, Finset.mem_univ, true_and]
theorem producerDecode_allOnes (lay : Layer) : WCT9.producerDecode lay (WCT9.encodingAnswer lay (BitVec.allOnes 256)) = none := by
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
    have hr := (reached_congr h e.2.1 _).mp hr'
    refine ⟨hr, ?_⟩
    obtain ⟨c, hc, hin, hprev⟩ := hr
    rw [hin] at hv' ⊢
    exact (rowDec_congr h e.2.1 c hc hprev).mp hv'
  · rintro ⟨hr, hv⟩
    refine ⟨(reached_congr h e.2.1 _).mpr hr, ?_⟩
    obtain ⟨c, hc, hin, hprev⟩ := hr
    rw [hin] at hv ⊢
    exact (rowDec_congr h e.2.1 c hc hprev).mpr hv
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
        rcases hq with hnon | ⟨L, hs, hr⟩
        · exact absurd (encInput_encHeader e) hnon
        · obtain ⟨c, hc⟩ := reached_encInput hs hr
          have hee := encInput_injective hc
          have hr' : Reached (eagerAnswers U privateTable pub) (leafOf e.1.1) (encInput e) := by
            rw [hee]
            rw [hee] at hr
            exact hr
          have hnf : e ∉ (cellKey (eagerAnswers U privateTable pub)).2 := fun hfree => hfree hr'
          have hrej := rej_of_cell he hnf
          refine RejPair.mk (encInput_length e) (encInput_hdr e) hrej.2 ?_
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

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

/-- Threshold context is part of the resampling key. In particular, two worlds
    with the same rejected rows but different ancestor credits are not placed
    in the same conditional cell. -/
structure CellKey where
  cells : Set Enc.EncIndex
  free : Set Enc.EncIndex
  contexts : Enc.EncIndex → Option Nat

noncomputable def rejectedAnswers (lay : Layer) (remaining : Nat) : Finset HashOutput :=
  Finset.univ.filter fun answer => WCT9.CanonicalPolicy.producerDecodeAt lay
    (WCT9.CanonicalPolicy.threshold lay.val remaining) (WCT9.encodingAnswer lay answer) = none

theorem mem_rejectedAnswers (lay : Layer) (remaining : Nat) (answer : HashOutput) :
    answer ∈ rejectedAnswers lay remaining ↔ WCT9.CanonicalPolicy.producerDecodeAt lay
      (WCT9.CanonicalPolicy.threshold lay.val remaining) (WCT9.encodingAnswer lay answer) = none := by
  simp only [rejectedAnswers, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rejectedAnswers_nonempty (lay : Layer) (remaining : Nat) :
    (rejectedAnswers lay remaining).Nonempty := by
  refine ⟨BitVec.allOnes 256, (mem_rejectedAnswers _ _ _).mpr ?_⟩
  have hd : WCT9.CanonicalPolicy.decode lay (WCT9.encodingAnswer lay (BitVec.allOnes 256)) = none := by
    fin_cases lay <;> decide +kernel
  simp only [WCT9.CanonicalPolicy.producerDecodeAt, hd]

noncomputable def cellInit (key : CellKey) (entry : key.cells) : Finset HashOutput :=
  if entry.val ∈ key.free then Finset.univ
  else match key.contexts entry.val with
    | none => Finset.univ
    | some remaining => rejectedAnswers entry.val.1.1.lay remaining

theorem cellInit_nonempty (key : CellKey) (entry : key.cells) : (cellInit key entry).Nonempty := by
  unfold cellInit
  split_ifs
  · exact Finset.univ_nonempty
  · split
    · exact Finset.univ_nonempty
    · exact rejectedAnswers_nonempty _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- Reached counters use the ancestor context from the same oracle world. -/
def ReachedCounter (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (leaf : LeafAddr) (counter : Nat) : Prop :=
  counter < WCT9.searchLimit leaf.lay ∧ ∃ remaining,
    referenceContext answers messages leaf = some remaining ∧
      ∀ earlier < counter, decodeRow answers leaf
        (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) earlier = none

def Reached (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (leaf : LeafAddr) (input : HashInput) : Prop :=
  ∃ counter, ReachedCounter answers messages leaf counter ∧
    input = encRow leaf (messages leaf) (BitVec.ofNat 32 counter) 0

theorem rejected_prefix_congr (answers answers' : Answers) (leaf : LeafAddr) (floor : Nat)
    (message : WCT9.LayerMsg)
    (hdecisions : ∀ counter < WCT9.searchLimit leaf.lay,
      (∀ earlier < counter, decodeRow answers leaf floor message earlier = none) →
        decodeRow answers' leaf floor message counter = decodeRow answers leaf floor message counter) :
    ∀ counter ≤ WCT9.searchLimit leaf.lay,
      (∀ earlier < counter, decodeRow answers' leaf floor message earlier = none) ↔
        ∀ earlier < counter, decodeRow answers leaf floor message earlier = none := by
  intro counter
  induction counter with
  | zero => intro _; simp
  | succ counter ih =>
      intro hc
      constructor
      · intro hnew
        have hprev := (ih (by omega)).mp (fun earlier he => hnew earlier (by omega))
        intro earlier he
        rcases Nat.lt_succ_iff_lt_or_eq.mp he with hlt | heq
        · exact hprev earlier hlt
        · rw [heq, ← hdecisions counter (by omega) hprev]
          exact hnew counter (by omega)
      · intro hold
        have hprev : ∀ earlier < counter, decodeRow answers leaf floor message earlier = none :=
          fun earlier he => hold earlier (by omega)
        intro earlier he
        rcases Nat.lt_succ_iff_lt_or_eq.mp he with hlt | heq
        · exact (ih (by omega)).mpr hprev earlier hlt
        · rw [heq, hdecisions counter (by omega) hprev]
          exact hold counter (by omega)

theorem reached_congr_of_decisions (answers answers' : Answers)
    (messages messages' : LeafAddr → WCT9.LayerMsg)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ leaf, allowed leaf → leaf.lay.val ≠ 0 → allowed (parent leaf))
    (hmessages : ∀ leaf, allowed leaf → messages' leaf = messages leaf)
    (hdecisions : ∀ leaf, allowed leaf → ∀ remaining,
      referenceContext answers messages leaf = some remaining →
      ∀ counter < WCT9.searchLimit leaf.lay,
        (∀ earlier < counter, decodeRow answers leaf
          (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) earlier = none) →
        decodeRow answers' leaf (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) counter =
          decodeRow answers leaf (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) counter)
    {leaf : LeafAddr} (hleaf : allowed leaf) (input : HashInput) :
    Reached answers' messages' leaf input ↔ Reached answers messages leaf input := by
  have hctx := (reference_congr_of_decisions answers answers' messages messages' allowed
    hparent hmessages hdecisions hleaf).1
  unfold Reached ReachedCounter
  rw [hctx, hmessages leaf hleaf]
  apply exists_congr
  intro counter
  apply and_congr_left
  intro _
  apply and_congr_right
  intro hcounter
  apply exists_congr
  intro remaining
  apply and_congr_right
  intro hremaining
  exact rejected_prefix_congr answers answers' leaf _ _
    (hdecisions leaf hleaf remaining hremaining) counter (Nat.le_of_lt hcounter)

noncomputable def freeSet (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) : Set Enc.EncIndex :=
  {entry | ¬Reached answers messages (Enc.leafOf entry.1.1) (Enc.encInput entry)}

noncomputable def rejectedSet (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) : Set Enc.EncIndex :=
  {entry | ∃ counter remaining,
    ReachedCounter answers messages (Enc.leafOf entry.1.1) counter ∧
    Enc.encInput entry = encRow (Enc.leafOf entry.1.1) (messages (Enc.leafOf entry.1.1))
      (BitVec.ofNat 32 counter) 0 ∧
    referenceContext answers messages (Enc.leafOf entry.1.1) = some remaining ∧
    decodeRow answers (Enc.leafOf entry.1.1)
      (WCT9.CanonicalPolicy.threshold entry.1.1.lay.val remaining)
      (messages (Enc.leafOf entry.1.1)) counter = none}

noncomputable def cellKey (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) : CellKey :=
  ⟨freeSet answers messages ∪ rejectedSet answers messages,
    freeSet answers messages, fun entry => referenceContext answers messages (Enc.leafOf entry.1.1)⟩

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000

theorem source_parent {leaf : LeafAddr} (hleaf : WotsExtract.SourceLeaf7 leaf)
    (hpositive : leaf.lay.val ≠ 0) : WotsExtract.SourceLeaf7 (parent leaf) := by
  rcases leaf with ⟨lay, tree, index⟩
  fin_cases lay <;>
    norm_num [WotsExtract.SourceLeaf7, parent, ClaudeWCT.W9.T3M.Extract.treeBits,
      SigGolfCandidate.T3.height] at * <;> omega

/-- Decisions on all valid source leaves preserve both ancestor context and
    the selected word. The hypothesis includes each world's actual message. -/
theorem source_reference_congr (answers answers' : Answers)
    (messages messages' : LeafAddr → WCT9.LayerMsg)
    (hmessages : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf = messages leaf)
    (hdecisions : ∀ leaf, WotsExtract.SourceLeaf7 leaf → ∀ remaining,
      referenceContext answers messages leaf = some remaining →
      ∀ counter < WCT9.searchLimit leaf.lay,
        (∀ earlier < counter, decodeRow answers leaf
          (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) earlier = none) →
        decodeRow answers' leaf (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) counter =
          decodeRow answers leaf (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) counter)
    {leaf : LeafAddr} (hleaf : WotsExtract.SourceLeaf7 leaf) :
    referenceContext answers' messages' leaf = referenceContext answers messages leaf ∧
      referenceSearch answers' messages' leaf = referenceSearch answers messages leaf :=
  reference_congr_of_decisions answers answers' messages messages' WotsExtract.SourceLeaf7
    (fun _ h hp => source_parent h hp) hmessages hdecisions hleaf

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- The exact answers may change, but each decision on an original reached
    prefix, including its ancestor-dependent threshold, stays unchanged. -/
def DecisionsAgree (answers answers' : Answers) (messages : LeafAddr → WCT9.LayerMsg) : Prop :=
  ∀ leaf, WotsExtract.SourceLeaf7 leaf → ∀ remaining,
    referenceContext answers messages leaf = some remaining →
    ∀ counter < WCT9.searchLimit leaf.lay,
      (∀ earlier < counter, decodeRow answers leaf
        (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) earlier = none) →
      decodeRow answers' leaf (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) counter =
        decodeRow answers leaf (WCT9.CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) counter

theorem reachedCounter_congr {answers answers' : Answers}
    {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hmessages : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf = messages leaf)
    (hdecisions : DecisionsAgree answers answers' messages)
    {leaf : LeafAddr} (hleaf : WotsExtract.SourceLeaf7 leaf) (counter : Nat) :
    ReachedCounter answers' messages' leaf counter ↔ ReachedCounter answers messages leaf counter := by
  have hctx := (source_reference_congr answers answers' messages messages' hmessages hdecisions hleaf).1
  unfold ReachedCounter
  rw [hctx, hmessages leaf hleaf]
  apply and_congr_right
  intro hc
  apply exists_congr
  intro remaining
  apply and_congr_right
  intro hr
  exact rejected_prefix_congr answers answers' leaf _ _ (hdecisions leaf hleaf remaining hr)
    counter (Nat.le_of_lt hc)

theorem cellKey_congr {answers answers' : Answers}
    {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hmessages : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf = messages leaf)
    (hdecisions : DecisionsAgree answers answers' messages) :
    cellKey answers' messages' = cellKey answers messages := by
  have hctx (entry : Enc.EncIndex) :
      referenceContext answers' messages' (Enc.leafOf entry.1.1) =
        referenceContext answers messages (Enc.leafOf entry.1.1) :=
    (source_reference_congr answers answers' messages messages' hmessages hdecisions (leaf := Enc.leafOf entry.1.1) entry.2.1).1
  have hf : freeSet answers' messages' = freeSet answers messages := by
    ext entry
    exact not_congr (reached_congr_of_decisions answers answers' messages messages'
      WotsExtract.SourceLeaf7 (fun _ h hp => source_parent h hp) hmessages hdecisions (leaf := Enc.leafOf entry.1.1) entry.2.1 _)
  have hr : rejectedSet answers' messages' = rejectedSet answers messages := by
    ext entry
    unfold rejectedSet
    simp only [Set.mem_setOf_eq]
    apply exists_congr
    intro counter
    apply exists_congr
    intro remaining
    rw [reachedCounter_congr hmessages hdecisions (leaf := Enc.leafOf entry.1.1) entry.2.1 counter,
      hmessages (Enc.leafOf entry.1.1) entry.2.1, hctx entry]
    apply and_congr_right
    intro hreach
    apply and_congr_right
    intro _
    apply and_congr_right
    intro hremaining
    have hprev : ∀ earlier < counter, decodeRow answers (Enc.leafOf entry.1.1)
        (WCT9.CanonicalPolicy.threshold entry.1.1.lay.val remaining)
        (messages (Enc.leafOf entry.1.1)) earlier = none := by
      obtain ⟨_, oldRemaining, hold, hp⟩ := hreach
      rw [hremaining] at hold
      cases hold
      exact hp
    exact Iff.of_eq (congrArg (fun result => result = none)
      (hdecisions (Enc.leafOf entry.1.1) entry.2.1 remaining hremaining counter hreach.1 hprev))
  unfold cellKey
  rw [hf, hr]
  congr 1
  funext entry
  exact hctx entry

theorem decodeRow_answer (answers : Answers) (leaf : LeafAddr) (floor : Nat)
    (message : WCT9.LayerMsg) (counter : Nat) :
    decodeRow answers leaf floor message counter = WCT9.CanonicalPolicy.producerDecodeAt leaf.lay floor
      (WCT9.encodingAnswer leaf.lay (answers (.inl (.inr
        (encRow leaf message (BitVec.ofNat 32 counter) 0))))) := by
  unfold decodeRow
  rw [WCT9.eval_encodingHash, encRow_zero]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open SigGolfCandidate.T3.Security.Wots.Enc (eagerAnswers_public_mem)

private def sourcePosition (leaf : LeafAddr) (hs : WotsExtract.SourceLeaf7 leaf) : CanonGraph.LeafPos :=
  ⟨leaf.lay, ⟨leaf.tree, hs.tree_lt⟩, ⟨leaf.leaf, by
    have hh : ∀ lay : Layer, 2 ^ height lay ≤ 4096 := by intro lay; fin_cases lay <;> decide
    exact hs.2.trans_le (hh leaf.lay)⟩⟩

private theorem sourcePosition_source (leaf : LeafAddr) (hs : WotsExtract.SourceLeaf7 leaf) :
    (sourcePosition leaf hs).Source := hs

private theorem leafOf_sourcePosition (leaf : LeafAddr) (hs : WotsExtract.SourceLeaf7 leaf) :
    Enc.leafOf (sourcePosition leaf hs) = leaf := by cases leaf; rfl

theorem rejected_answer {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg}
    {entry : Enc.EncIndex} (hr : entry ∈ rejectedSet answers messages) {remaining : Nat}
    (hctx : referenceContext answers messages (Enc.leafOf entry.1.1) = some remaining) :
    WCT9.CanonicalPolicy.producerDecodeAt entry.1.1.lay
      (WCT9.CanonicalPolicy.threshold entry.1.1.lay.val remaining)
      (WCT9.encodingAnswer entry.1.1.lay (answers (.inl (.inr (Enc.encInput entry))))) = none := by
  obtain ⟨counter, oldRemaining, _, hin, hold, hnone⟩ := hr
  rw [hctx] at hold
  cases hold
  rw [decodeRow_answer, ← hin] at hnone
  exact hnone

/-- Every overwritten reached row was rejected at its own canonical threshold;
    the replacement is rejected at that same threshold. -/
theorem overwrite_decisions {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
    (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (messages : LeafAddr → WCT9.LayerMsg)
    (hfits : ∀ leaf, WotsExtract.SourceLeaf7 leaf → ClaudeWCT.W9.T3M.Extract.msgFits leaf.lay (messages leaf))
    (values : (cellKey (eagerAnswers U privateTable pub) messages).cells → HashOutput)
    (hvalues : ∀ entry, values entry ∈ cellInit (cellKey (eagerAnswers U privateTable pub) messages) entry) :
    DecisionsAgree (eagerAnswers U privateTable pub)
      (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) messages).cells pub values)) messages := by
  intro leaf hleaf remaining hctx counter hcounter hprev
  let position := sourcePosition leaf hleaf
  let entry : Enc.EncIndex := Enc.encIdx position (sourcePosition_source leaf hleaf)
    (messages leaf) (BitVec.ofNat 32 counter) 0 (hfits leaf hleaf)
  have hleafEntry : Enc.leafOf entry.1.1 = leaf := leafOf_sourcePosition leaf hleaf
  have hinput : Enc.encInput entry = encRow leaf (messages leaf) (BitVec.ofNat 32 counter) 0 := by
    rfl
  have hreach : Reached (eagerAnswers U privateTable pub) messages (Enc.leafOf entry.1.1) (Enc.encInput entry) := by
    rw [hleafEntry, hinput]
    exact ⟨counter, ⟨hcounter, remaining, hctx, hprev⟩, rfl⟩
  have hentryctx : referenceContext (eagerAnswers U privateTable pub) messages (Enc.leafOf entry.1.1) = some remaining := by
    rwa [hleafEntry]
  have hnotfree : entry ∉ (cellKey (eagerAnswers U privateTable pub) messages).free := fun h => h hreach
  rw [decodeRow_answer, decodeRow_answer, ← hinput]
  have hin : Enc.encInput entry ∈ U := hU (Enc.encInput_short entry)
  rw [eagerAnswers_public_mem U privateTable _ ⟨_, hin⟩,
    eagerAnswers_public_mem U privateTable _ ⟨_, hin⟩]
  by_cases hcell : entry ∈ (cellKey (eagerAnswers U privateTable pub) messages).cells
  · have hrejected : entry ∈ rejectedSet (eagerAnswers U privateTable pub) messages := by
      rcases hcell with hf | hr
      · exact False.elim (hnotfree hf)
      · exact hr
    have hold := rejected_answer hrejected hentryctx
    rw [eagerAnswers_public_mem U privateTable _ ⟨_, hin⟩] at hold
    rw [Enc.ov_at hU _ pub values ⟨entry, hcell⟩]
    have hv := hvalues ⟨entry, hcell⟩
    unfold cellInit at hv
    rw [if_neg hnotfree] at hv
    change values ⟨entry, hcell⟩ ∈
      (match referenceContext (eagerAnswers U privateTable pub) messages (Enc.leafOf entry.1.1) with
        | none => Finset.univ
        | some remaining => rejectedAnswers entry.1.1.lay remaining) at hv
    rw [hentryctx] at hv
    exact ((mem_rejectedAnswers _ _ _).mp hv).trans hold.symm
  · apply congrArg
    apply congrArg
    exact Enc.ov_other _ pub values ⟨_, hin⟩ (fun other hother heq =>
      hcell ((Enc.encInput_injective heq) ▸ hother))

theorem cellKey_overwrite {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
    (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (messages messages' : LeafAddr → WCT9.LayerMsg)
    (hfits : ∀ leaf, WotsExtract.SourceLeaf7 leaf → ClaudeWCT.W9.T3M.Extract.msgFits leaf.lay (messages leaf))
    (hmessages : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf = messages leaf)
    (values : (cellKey (eagerAnswers U privateTable pub) messages).cells → HashOutput)
    (hvalues : ∀ entry, values entry ∈ cellInit (cellKey (eagerAnswers U privateTable pub) messages) entry) :
    cellKey (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) messages).cells pub values)) messages' =
      cellKey (eagerAnswers U privateTable pub) messages :=
  cellKey_congr hmessages (overwrite_decisions hU privateTable pub messages hfits values hvalues)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc (eagerAnswers_public_mem uniform_resample_tsum tsum_uniform_coe)
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable {U : Finset HashInput}

theorem read_cellInit (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (messages : LeafAddr → WCT9.LayerMsg)
    (entry : (cellKey (eagerAnswers U privateTable pub) messages).cells) :
    Enc.rd hU (cellKey (eagerAnswers U privateTable pub) messages).cells pub entry ∈
      cellInit (cellKey (eagerAnswers U privateTable pub) messages) entry := by
  unfold cellInit
  split_ifs with hf
  · exact Finset.mem_univ _
  · have hr : entry.val ∈ rejectedSet (eagerAnswers U privateTable pub) messages := by
      rcases entry.property with hfree | hrej
      · exact False.elim (hf hfree)
      · exact hrej
    obtain ⟨counter, remaining, hreach, hin, hctx, hnone⟩ := hr
    change Enc.rd hU (cellKey (eagerAnswers U privateTable pub) messages).cells pub entry ∈
      (match referenceContext (eagerAnswers U privateTable pub) messages (Enc.leafOf entry.val.1.1) with
        | none => Finset.univ
        | some remaining => rejectedAnswers entry.val.1.1.lay remaining)
    rw [hctx, mem_rejectedAnswers]
    have hd := rejected_answer ⟨counter, remaining, hreach, hin, hctx, hnone⟩ hctx
    rw [eagerAnswers_public_mem U privateTable pub
      ⟨Enc.encInput entry.val, hU (Enc.encInput_short entry.val)⟩] at hd
    exact hd

/- Conditional resampling includes the canonical threshold context in its key.
    The message-family premise is discharged separately from the free-node
    invariance of the prepared WOTS trees and the paired forest. -/
set_option maxRecDepth 100000 in
theorem public_resample_cells [∀ k : Set Enc.EncIndex, Fintype k]
    [∀ k : Set Enc.EncIndex, DecidableEq k] [Fintype (U → HashOutput)]
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (messages : Answers → LeafAddr → WCT9.LayerMsg)
    (hfits : ∀ answers leaf, WotsExtract.SourceLeaf7 leaf → ClaudeWCT.W9.T3M.Extract.msgFits leaf.lay (messages answers leaf))
    (hmessages : ∀ pub
      (values : (cellKey (eagerAnswers U privateTable pub) (messages (eagerAnswers U privateTable pub))).cells → HashOutput),
      (∀ entry, values entry ∈ cellInit
        (cellKey (eagerAnswers U privateTable pub) (messages (eagerAnswers U privateTable pub))) entry) →
      ∀ leaf, WotsExtract.SourceLeaf7 leaf →
        messages (eagerAnswers U privateTable (Enc.ov
          (cellKey (eagerAnswers U privateTable pub) (messages (eagerAnswers U privateTable pub))).cells pub values)) leaf =
          messages (eagerAnswers U privateTable pub) leaf)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' values, PMF.uniformOfFinset (Fintype.piFinset (cellInit
          (cellKey (eagerAnswers U privateTable pub) (messages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) values *
          F (Enc.ov (cellKey (eagerAnswers U privateTable pub) (messages (eagerAnswers U privateTable pub))).cells pub values) := by
  let key : (U → HashOutput) → CellKey := fun pub =>
    cellKey (eagerAnswers U privateTable pub) (messages (eagerAnswers U privateTable pub))
  let A : ∀ k : CellKey, Finset (k.cells → HashOutput) := fun k => Fintype.piFinset (cellInit k)
  have hA : ∀ k, (A k).Nonempty := fun k => Fintype.piFinset_nonempty.mpr (cellInit_nonempty k)
  have iN : ∀ k, Nonempty ↥(A k) := fun k => (hA k).to_subtype
  let read : ∀ k : CellKey, (U → HashOutput) → ↥(A k) := fun k pub =>
    if h : Enc.rd hU k.cells pub ∈ A k then ⟨Enc.rd hU k.cells pub, h⟩ else Classical.choice (iN k)
  have hmem : ∀ pub, Enc.rd hU (key pub).cells pub ∈ A (key pub) :=
    fun pub => Fintype.mem_piFinset.mpr (read_cellInit hU privateTable pub _)
  have hread : ∀ (k : CellKey) (pub : U → HashOutput) (h : Enc.rd hU k.cells pub ∈ A k),
      read k pub = ⟨Enc.rd hU k.cells pub, h⟩ := by
    intro k pub h
    dsimp only [read]
    rw [dif_pos h]
  have hid := @uniform_resample_tsum (U → HashOutput) CellKey _ _ (fun k => ↥(A k))
    (fun k => inferInstance) iN key (fun k pub values => Enc.ov k.cells pub values.val) read
    (fun pub values => by
      obtain ⟨values, hv⟩ := values
      have he : Enc.rd hU (key pub).cells (Enc.ov (key pub).cells pub values) = values :=
        Enc.rd_ov hU _ pub values
      have hmem' : Enc.rd hU (key pub).cells (Enc.ov (key pub).cells pub values) ∈ A (key pub) := by
        rw [he]; exact hv
      refine (hread _ _ hmem').trans ?_
      exact Subtype.mk_eq_mk.mpr he)
    (fun pub values => by
      have hr := hread _ pub (hmem pub)
      show Enc.ov (key pub).cells (Enc.ov (key pub).cells pub values.val) (read (key pub) pub).val = pub
      rw [hr]
      exact Enc.ov_ov_rd hU _ pub values.val)
    (fun pub values => cellKey_overwrite hU privateTable pub _ _ (hfits _)
      (hmessages pub values.val (Fintype.mem_piFinset.mp values.property)) values.val
      (Fintype.mem_piFinset.mp values.property)) F
  rw [hid]
  refine tsum_congr fun pub => ?_
  congr 1
  exact tsum_uniform_coe (A (key pub)) (hA _) (iN _)
    (fun values => F (Enc.ov (key pub).cells pub values))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc (NonEnc nonEnc_of_hdr)
open SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SourceQueries
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topInput_nonEnc (coord index heap : Nat) (hcoord : coord < 9) (left pad right : Digest) :
    NonEnc (.inl (.inr (pad64 (WCT9.wctTopInput coord index heap left pad right)))) := by
  apply nonEnc_of_hdr _ (WCT9.wctNodeHeader coord index heap) ?_
    (SigGolfCandidate.T3.Security.Wots.Enc.notHyper_of_tag (by
      rw [WCT9.wctNodeHeader_tweakTag hcoord]; split <;> decide))
  unfold WCT9.wctTopInput
  rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++ SphincsSecurity.bytesLE 16 _)]
  exact WCT9.hdrBlock_pad64_prefix _ _ _ (SphincsSecurity.bytesLE_length _ _)

theorem topLow_nonEnc (coord index heap : Nat) (hcoord : coord < 9) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (WCT9.wctTopInput coord index heap left pad right)) NonEnc := by
  unfold shortHash publicHash
  exact bind_allowed NonEnc ((allQueriesSatisfy_query_iff _ _).mpr
    (topInput_nonEnc coord index heap hcoord left pad right)) fun _ => pure_allowed _ _

theorem topHigh_nonEnc (coord index heap : Nat) (hcoord : coord < 9) (left pad right : Digest) :
    AllQueriesSatisfy (WCT9.highHash (WCT9.wctTopInput coord index heap left pad right)) NonEnc :=
  WCT9.allQ_highHash_of_shortHash _ (topLow_nonEnc coord index heap hcoord left pad right)

theorem sharedNode_nonEnc (first : Bool) (coord index heap : Nat) (hcoord : coord < 9)
    (pads : Nat → PairRoot) (left right : Digest) :
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) NonEnc := by
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact topLow_nonEnc _ _ _ hcoord _ _ _
    · exact topHigh_nonEnc _ _ _ hcoord _ _ _
  · split
    · split
      · exact topHigh_nonEnc _ _ _ hcoord _ _ _
      · exact topLow_nonEnc _ _ _ hcoord _ _ _
    · change AllQueriesSatisfy (WCT9.ftsHash heap (WCT9.wctTopInput coord index heap left 0 right)) NonEnc
      exact WCT9.allQ_ftsHash_of_shortHash _ _ (topLow_nonEnc _ _ _ hcoord _ _ _)

theorem sharedHeap_nonEnc (first : Bool) (index coord : Nat) (hcoord : coord < 9)
    (pads : Nat → PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (sharedHeap first index coord pads leaves) NonEnc := by
  unfold sharedHeap
  exact foldlM_allowed NonEnc _ _ (fun nodes heap =>
    bind_allowed NonEnc (sharedNode_nonEnc first coord index heap hcoord pads _ _) fun _ => pure_allowed _ _) _

theorem sharedLeaves_congr {answers answers' : Answers}
    (h : ∀ query, NonEnc query → answers' query = answers query)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedLeaves answers' first index coord.val pads = sharedLeaves answers first index coord.val pads := by
  unfold sharedLeaves
  apply congrArg List.ofFn
  funext physical
  have hraw : rawChild first physical.val < 128 := by
    have hp := physical.isLt
    cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega
  exact WCT9.Wots.childRootH_congr (fun query hq => h query (WCT9.Wots.ftsQuery_nonEnc hq))
    (128 + physical.val) coord ⟨rawChild first physical.val, hraw⟩ _

theorem sharedNodes_congr {answers answers' : Answers}
    (h : ∀ query, NonEnc query → answers' query = answers query)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedNodes answers' first index coord.val pads = sharedNodes answers first index coord.val pads := by
  unfold sharedNodes
  rw [sharedLeaves_congr h first index coord]
  exact (WCT9.Wots.respects_of_allQueriesSatisfy (sharedHeap_nonEnc first index coord.val coord.isLt pads _)).eval_eq h

theorem expectedPairRoot_congr {answers answers' : Answers}
    (h : ∀ query, NonEnc query → answers' query = answers query)
    (index : Nat) (pair : Fin 4) (prev : PairRoot) :
    expectedPairRoot answers' index pair.val prev = expectedPairRoot answers index pair.val prev := by
  have ha : firstNodes answers' index pair.val prev = firstNodes answers index pair.val prev :=
    sharedNodes_congr h true index ⟨2 * pair.val, by have := pair.isLt; omega⟩ _
  have hb : secondNodes answers' index pair.val prev = secondNodes answers index pair.val prev := by
    unfold secondNodes
    rw [ha]
    exact sharedNodes_congr h false index ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _
  unfold expectedPairRoot
  rw [hb]

noncomputable abbrev forestCommitment (answers : Answers) (index : Nat) : PairRoot :=
  SigGolfCandidate.Research.SharedForest.forestCommitment answers index

theorem forestCommitment_congr {answers answers' : Answers}
    (h : ∀ query, NonEnc query → answers' query = answers query) (index : Nat) :
    forestCommitment answers' index = forestCommitment answers index := by
  have hpair (pair : Nat) (hp : pair < 4) (prev : PairRoot) :=
    expectedPairRoot_congr h index ⟨pair, hp⟩ prev
  dsimp only [forestCommitment, SigGolfCandidate.Research.SharedForest.forestCommitment]
  rw [hpair 0 (by decide), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    sharedNodes_congr h false index ⟨8, by decide⟩]

noncomputable def sourceMessages (answers : Answers) (leaf : LeafAddr) : WCT9.LayerMsg :=
  if h : leaf.lay.val < 3 then
    let pair := ClaudeWCT.W9.T3M.Extract.honestPair answers ⟨leaf.lay.val + 1, by omega⟩
      (leaf.tree * 2 ^ height leaf.lay + leaf.leaf)
    .pair pair.1 pair.2
  else
    let pair := forestCommitment answers ((leaf.tree * 2 ^ height leaf.lay + leaf.leaf) % 2 ^ 31)
    .pair pair.1 pair.2

theorem sourceMessages_fit (answers : Answers) (leaf : LeafAddr) :
    ClaudeWCT.W9.T3M.Extract.msgFits leaf.lay (sourceMessages answers leaf) := by
  unfold sourceMessages
  split <;> trivial

theorem sourceMessages_congr {answers answers' : Answers}
    (h : ∀ query, NonEnc query → answers' query = answers query) (leaf : LeafAddr) :
    sourceMessages answers' leaf = sourceMessages answers leaf := by
  unfold sourceMessages
  split
  · rw [honestPair_congr_nonEnc h]
  · rw [forestCommitment_congr h]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc (NonEnc eagerAnswers_public_mem eagerAnswers_public_not_mem)
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Encoding-cell overwrites leave all tree and FTS commitment queries intact. -/
theorem overwrite_nonEnc {U : Finset HashInput} (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (cells : Set Enc.EncIndex) (values : cells → HashOutput) :
    ∀ query, NonEnc query → eagerAnswers U privateTable (Enc.ov cells pub values) query =
      eagerAnswers U privateTable pub query := by
  intro query hnon
  rcases query with (coin | input) | coordinate
  · rfl
  · by_cases hin : input ∈ U
    · rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
        eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
      apply Enc.ov_other
      intro entry _ heq
      apply hnon
      rw [← (show Enc.encInput entry = input from heq)]
      exact Enc.encInput_encHeader entry
    · rw [eagerAnswers_public_not_mem U privateTable _ input hin,
        eagerAnswers_public_not_mem U privateTable _ input hin]
  · rfl

theorem sourceMessages_overwrite {U : Finset HashInput} (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (cells : Set Enc.EncIndex) (values : cells → HashOutput) (leaf : LeafAddr) :
    sourceMessages (eagerAnswers U privateTable (Enc.ov cells pub values)) leaf =
      sourceMessages (eagerAnswers U privateTable pub) leaf :=
  sourceMessages_congr (overwrite_nonEnc privateTable pub cells values) leaf

/-- The candidate's paired commitment supplies the concrete message-family
    invariant needed by canonical conditional resampling. -/
theorem public_resample_source {U : Finset HashInput} [∀ k : Set Enc.EncIndex, Fintype k]
    [∀ k : Set Enc.EncIndex, DecidableEq k] [Fintype (U → HashOutput)]
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' values, PMF.uniformOfFinset (Fintype.piFinset (cellInit
          (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) values *
          F (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub values) :=
  public_resample_cells hU privateTable sourceMessages (fun answers leaf _ => sourceMessages_fit answers leaf)
    (fun pub values _ leaf _ => sourceMessages_overwrite privateTable pub _ values leaf) F

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def sourceLeaf (index : Nat) (lay : Layer) : LeafAddr :=
  ⟨lay, (route index lay).2, (route index lay).1⟩

theorem sourceLeaf_parent (index : Nat) (lay : Layer) (hlay : lay.val ≠ 0) :
    parent (sourceLeaf index lay) = sourceLeaf index ⟨lay.val - 1, by omega⟩ := by
  fin_cases lay
  · exact False.elim (hlay rfl)
  · change (⟨0, index / 524288 / 4096, index / 524288 % 4096⟩ : LeafAddr) =
      ⟨0, index / 2147483648, index / 524288 % 4096⟩
    rw [Nat.div_div_eq_div_mul]
  · change (⟨1, index / 4096 / 128, index / 4096 % 128⟩ : LeafAddr) =
      ⟨1, index / 524288, index / 4096 % 128⟩
    rw [Nat.div_div_eq_div_mul]
  · change (⟨2, index / 64 / 64, index / 64 % 64⟩ : LeafAddr) =
      ⟨2, index / 4096, index / 64 % 64⟩
    rw [Nat.div_div_eq_div_mul]

theorem sourceMessages_route_lower (answers : Answers) (index : Nat) (lay : Layer)
    (hlay : lay.val < 3) :
    sourceMessages answers (sourceLeaf index lay) =
      let pair := WCT9.builtPair answers ⟨lay.val + 1, by omega⟩
        (route index ⟨lay.val + 1, by omega⟩).2
      WCT9.LayerMsg.pair pair.1 pair.2 := by
  have hroute : (route index lay).2 * 2 ^ height lay + (route index lay).1 =
      (route index ⟨lay.val + 1, by omega⟩).2 := by
    fin_cases lay
    · norm_num [route, height]
      omega
    · norm_num [route, height]
      omega
    · norm_num [route, height]
      omega
    · exact False.elim (Nat.lt_irrefl 3 hlay)
  simp only [sourceMessages, sourceLeaf, hlay, dite_true, hroute]
  rfl

theorem sourceMessages_route_bottom (answers : Answers) (index : Nat) (hindex : index < 2 ^ 31) :
    sourceMessages answers (sourceLeaf index 3) =
      WCT9.LayerMsg.pair (forestCommitment answers index).1 (forestCommitment answers index).2 := by
  have hroute : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
    change index / 64 * 64 + (index / 1) % 64 = index
    rw [Nat.div_one]
    omega
  simp only [sourceMessages, sourceLeaf, show ¬ (3 : Layer).val < 3 by decide,
    dite_false, hroute, Nat.mod_eq_of_lt hindex]

theorem context_parent_success {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg}
    {leaf : LeafAddr} (hpositive : leaf.lay.val ≠ 0) {remaining : Nat}
    {counter : BitVec 32} {digits : List Nat}
    (hcontext : referenceContext answers messages (parent leaf) = some remaining)
    (hsearch : referenceSearch answers messages (parent leaf) = some (counter, digits)) :
    referenceContext answers messages leaf =
      some (WCT9.CanonicalPolicy.nextResidual remaining (parent leaf).lay digits) := by
  change (if leaf.lay.val = 0 then some 63 else
    after (searchOf answers messages) WCT9.CanonicalPolicy.credit (parent leaf)) = _
  rw [if_neg hpositive, after_eq]
  change (referenceContext answers messages (parent leaf)).bind _ = _
  rw [hcontext]
  unfold referenceSearch selected at hsearch
  change (referenceContext answers messages (parent leaf)).bind _ = _ at hsearch
  rw [hcontext] at hsearch
  simp only [Option.bind_some] at hsearch ⊢
  rw [hsearch]
  rfl

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceSearch_of_context {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg}
    {leaf : LeafAddr} {remaining : Nat} {counter : BitVec 32} {digits : List Nat}
    (hc : referenceContext answers messages leaf = some remaining)
    (hs : searchOf answers messages leaf remaining = some (counter, digits)) :
    referenceSearch answers messages leaf = some (counter, digits) := by
  change (referenceContext answers messages leaf).bind _ = _
  rw [hc]
  exact hs

theorem searchOf_route_lower (answers : Answers) (index : Nat) (lay : Layer)
    (hlay : lay.val < 3) (remaining : Nat) :
    searchOf answers (sourceMessages answers) (sourceLeaf index lay) remaining =
      let pair := WCT9.builtPair answers ⟨lay.val + 1, by omega⟩
        (route index ⟨lay.val + 1, by omega⟩).2
      evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (WCT9.CanonicalPolicy.threshold lay.val remaining) (route index lay).2 (route index lay).1
        (.pair pair.1 pair.2) 0 (WCT9.searchLimit lay)) := by
  unfold searchOf
  rw [sourceMessages_route_lower answers index lay hlay]
  rfl

theorem searchOf_route_bottom (answers : Answers) (index : Nat) (hindex : index < 2 ^ 31)
    (remaining : Nat) :
    searchOf answers (sourceMessages answers) (sourceLeaf index 3) remaining =
      evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt 3
        (WCT9.CanonicalPolicy.threshold 3 remaining) (route index 3).2 (route index 3).1
        (.pair (forestCommitment answers index).1 (forestCommitment answers index).2)
        0 (WCT9.searchLimit 3)) := by
  unfold searchOf
  rw [sourceMessages_route_bottom answers index hindex]
  rfl

def preparedContext (result : CanonicalLayers) (lay : Layer) : Nat :=
  if lay.val = 0 then 63
  else if lay.val = 1 then preparedResidual1 result
  else if lay.val = 2 then preparedResidual2 result
  else preparedResidual3 result

/-- The evaluated roots-first signer uses exactly the per-leaf canonical
reference cells, including the threshold context in every lower search. -/
theorem searchPreparedLayers_reference (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (hindex : index < 2 ^ 31) (result : CanonicalLayers)
    (he : evalWithAnswerFn answers (searchPreparedLayers cache index
      (evalWithAnswerFn answers (prepareRoots index)) (forestCommitment answers index)) = some result) :
    ∀ lay : Layer,
      referenceContext answers (sourceMessages answers) (sourceLeaf index lay) =
        some (preparedContext result lay) ∧
      referenceSearch answers (sourceMessages answers) (sourceLeaf index lay) =
        some (result.counters.getD lay.val 0, result.digits.getD lay.val []) := by
  rw [prepareRoots_result] at he
  have hf := searchPreparedLayers_some answers cache index _ _ result he
  have hc0 : referenceContext answers (sourceMessages answers) (sourceLeaf index 0) = some 63 := rfl
  have hd0 : searchOf answers (sourceMessages answers) (sourceLeaf index 0) 63 =
      some (result.counters.getD 0 0, result.digits.getD 0 []) := by
    rw [searchOf_route_lower answers index 0 (by decide)]
    change evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt 0
      (WCT9.CanonicalPolicy.threshold 0 63) (route index 0).2 (route index 0).1
      (.pair (WCT9.builtPair answers 1 (route index 1).2).1
        (WCT9.builtPair answers 1 (route index 1).2).2) 0 (WCT9.searchLimit 0)) = _
    simpa only [fixedPrepared_pair, WCT9.CanonicalPolicy.totalCredit, Fin.isValue, Nat.reduceAdd] using hf.search0
  have hs0 := referenceSearch_of_context hc0 hd0
  have hc1 : referenceContext answers (sourceMessages answers) (sourceLeaf index 1) =
      some (preparedResidual1 result) := by
    apply context_parent_success (leaf := sourceLeaf index 1) (by change 1 ≠ 0; decide)
    · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
    · rw [sourceLeaf_parent index 1 (by decide)]; exact hs0
  have hd1 : searchOf answers (sourceMessages answers) (sourceLeaf index 1) (preparedResidual1 result) =
      some (result.counters.getD 1 0, result.digits.getD 1 []) := by
    rw [searchOf_route_lower answers index 1 (by decide)]
    change evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt 1
      (WCT9.CanonicalPolicy.threshold 1 (preparedResidual1 result)) (route index 1).2 (route index 1).1
      (.pair (WCT9.builtPair answers 2 (route index 2).2).1
        (WCT9.builtPair answers 2 (route index 2).2).2) 0 (WCT9.searchLimit 1)) = _
    simpa only [fixedPrepared_pair, WCT9.CanonicalPolicy.totalCredit, Fin.isValue, Nat.reduceAdd] using hf.search1
  have hs1 := referenceSearch_of_context hc1 hd1
  have hc2 : referenceContext answers (sourceMessages answers) (sourceLeaf index 2) =
      some (preparedResidual2 result) := by
    apply context_parent_success (leaf := sourceLeaf index 2) (by change 2 ≠ 0; decide)
    · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
    · rw [sourceLeaf_parent index 2 (by decide)]; exact hs1
  have hd2 : searchOf answers (sourceMessages answers) (sourceLeaf index 2) (preparedResidual2 result) =
      some (result.counters.getD 2 0, result.digits.getD 2 []) := by
    rw [searchOf_route_lower answers index 2 (by decide)]
    change evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt 2
      (WCT9.CanonicalPolicy.threshold 2 (preparedResidual2 result)) (route index 2).2 (route index 2).1
      (.pair (WCT9.builtPair answers 3 (route index 3).2).1
        (WCT9.builtPair answers 3 (route index 3).2).2) 0 (WCT9.searchLimit 2)) = _
    simpa only [fixedPrepared_pair, WCT9.CanonicalPolicy.totalCredit, Fin.isValue, Nat.reduceAdd] using hf.search2
  have hs2 := referenceSearch_of_context hc2 hd2
  have hc3 : referenceContext answers (sourceMessages answers) (sourceLeaf index 3) =
      some (preparedResidual3 result) := by
    apply context_parent_success (leaf := sourceLeaf index 3) (by change 3 ≠ 0; decide)
    · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
    · rw [sourceLeaf_parent index 3 (by decide)]; exact hs2
  have hd3 : searchOf answers (sourceMessages answers) (sourceLeaf index 3) (preparedResidual3 result) =
      some (result.counters.getD 3 0, result.digits.getD 3 []) := by
    rw [searchOf_route_bottom answers index hindex]
    exact hf.search3
  have hs3 := referenceSearch_of_context hc3 hd3
  intro lay
  fin_cases lay
  · exact ⟨hc0, hs0⟩
  · exact ⟨hc1, hs1⟩
  · exact ⟨hc2, hs2⟩
  · exact ⟨hc3, hs3⟩

#print axioms searchPreparedLayers_reference
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SourceQueries
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topInput_untouched (a : ChainAddr) (coord index heap : Nat) (left pad right : Digest) :
    UntouchedP a (.inl (.inr (pad64 (WCT9.wctTopInput coord index heap left pad right)))) := by
  apply ClaudeWCT.W9.T3.Security.Wots.Mask.untouchedP_of_hdr a _
    (WCT9.wctNodeHeader coord index heap) ?_
    (fun _ _ _ _ _ _ => WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _)
  unfold WCT9.wctTopInput
  rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++ SphincsSecurity.bytesLE 16 _)]
  exact WCT9.hdrBlock_pad64_prefix _ _ _ (SphincsSecurity.bytesLE_length _ _)

theorem topLow_untouched (a : ChainAddr) (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (WCT9.wctTopInput coord index heap left pad right)) (UntouchedP a) := by
  unfold shortHash publicHash
  exact bind_allowed (UntouchedP a) ((allQueriesSatisfy_query_iff _ _).mpr
    (topInput_untouched a coord index heap left pad right)) fun _ => pure_allowed _ _

theorem topHigh_untouched (a : ChainAddr) (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (WCT9.highHash (WCT9.wctTopInput coord index heap left pad right)) (UntouchedP a) :=
  WCT9.allQ_highHash_of_shortHash _ (topLow_untouched a coord index heap left pad right)

theorem sharedNode_untouched (a : ChainAddr) (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) (UntouchedP a) := by
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact topLow_untouched a _ _ _ _ _ _
    · exact topHigh_untouched a _ _ _ _ _ _
  · split
    · split
      · exact topHigh_untouched a _ _ _ _ _ _
      · exact topLow_untouched a _ _ _ _ _ _
    · change AllQueriesSatisfy (WCT9.ftsHash heap (WCT9.wctTopInput coord index heap left 0 right)) (UntouchedP a)
      exact WCT9.allQ_ftsHash_of_shortHash _ _ (topLow_untouched a _ _ _ _ _ _)

theorem sharedHeap_untouched (a : ChainAddr) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (sharedHeap first index coord pads leaves) (UntouchedP a) := by
  unfold sharedHeap
  exact foldlM_allowed (UntouchedP a) _ _ (fun nodes heap =>
    bind_allowed (UntouchedP a) (sharedNode_untouched a first coord index heap pads _ _) fun _ => pure_allowed _ _) _
theorem sharedLeaves_congr_untouched (a : ChainAddr) {answers answers' : Answers}
    (h : ∀ query, UntouchedP a query → answers' query = answers query)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedLeaves answers' first index coord.val pads = sharedLeaves answers first index coord.val pads := by
  unfold sharedLeaves
  apply congrArg List.ofFn
  funext physical
  have hraw : rawChild first physical.val < 128 := by
    have hp := physical.isLt
    cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega
  exact WCT9.Wots.childRootH_congr (fun query hq => h query (Wots.Mask.ftsQuery_untouchedP a hq))
    (128 + physical.val) coord ⟨rawChild first physical.val, hraw⟩ _

theorem sharedNodes_congr_untouched (a : ChainAddr) {answers answers' : Answers}
    (h : ∀ query, UntouchedP a query → answers' query = answers query)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedNodes answers' first index coord.val pads = sharedNodes answers first index coord.val pads := by
  unfold sharedNodes
  rw [sharedLeaves_congr_untouched a h first index coord]
  exact (WCT9.Wots.respects_of_allQueriesSatisfy (sharedHeap_untouched a first index coord.val pads _)).eval_eq h

theorem expectedPairRoot_congr_untouched (a : ChainAddr) {answers answers' : Answers}
    (h : ∀ query, UntouchedP a query → answers' query = answers query)
    (index : Nat) (pair : Fin 4) (prev : PairRoot) :
    expectedPairRoot answers' index pair.val prev = expectedPairRoot answers index pair.val prev := by
  have ha : firstNodes answers' index pair.val prev = firstNodes answers index pair.val prev :=
    sharedNodes_congr_untouched a h true index ⟨2 * pair.val, by have := pair.isLt; omega⟩ _
  have hb : secondNodes answers' index pair.val prev = secondNodes answers index pair.val prev := by
    unfold secondNodes
    rw [ha]
    exact sharedNodes_congr_untouched a h false index ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _
  unfold expectedPairRoot
  rw [hb]


theorem forestCommitment_congr_untouched (a : ChainAddr) {answers answers' : Answers}
    (h : ∀ query, UntouchedP a query → answers' query = answers query) (index : Nat) :
    forestCommitment answers' index = forestCommitment answers index := by
  have hpair (pair : Nat) (hp : pair < 4) (prev : PairRoot) :=
    expectedPairRoot_congr_untouched a h index ⟨pair, hp⟩ prev
  dsimp only [forestCommitment, SigGolfCandidate.Research.SharedForest.forestCommitment]
  rw [hpair 0 (by decide), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    sharedNodes_congr_untouched a h false index ⟨8, by decide⟩]


theorem forestCommitment_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (index : Nat) :
    forestCommitment (maskAt answers messages a) index = forestCommitment answers index :=
  forestCommitment_congr_untouched a (fun _ hq => Mask.maskAt_untouched answers messages a hq) index

theorem sourceMessages_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (hal : Wots.Mask.MaskOK a) :
    sourceMessages (maskAt answers messages a) = sourceMessages answers := by
  funext L
  unfold sourceMessages
  split
  · rw [Mask.honestPair_maskAt answers messages a _ _ (Or.inr hal)]
  · rw [forestCommitment_maskAt]

theorem referenceSearch_source_maskAt (answers : Answers) (a : ChainAddr)
    (hal : Wots.Mask.MaskOK a) (L : LeafAddr) :
    referenceSearch (maskAt answers (sourceMessages answers) a)
      (sourceMessages (maskAt answers (sourceMessages answers) a)) L =
    referenceSearch answers (sourceMessages answers) L := by
  rw [sourceMessages_maskAt answers _ a hal]
  exact referenceSearch_maskAt answers _ a L

theorem referenceContext_source_maskAt (answers : Answers) (a : ChainAddr)
    (hal : Wots.Mask.MaskOK a) :
    referenceContext (maskAt answers (sourceMessages answers) a)
      (sourceMessages (maskAt answers (sourceMessages answers) a)) =
    referenceContext answers (sourceMessages answers) := by
  rw [sourceMessages_maskAt answers _ a hal]
  exact referenceContext_maskAt answers _ a

theorem depth_source_maskAt (answers : Answers) (a b : ChainAddr)
    (hal : Wots.Mask.MaskOK a) :
    depth (maskAt answers (sourceMessages answers) a)
      (sourceMessages (maskAt answers (sourceMessages answers) a)) b =
    depth answers (sourceMessages answers) b := by
  rw [sourceMessages_maskAt answers _ a hal]
  exact depth_maskAt_all answers _ a b

theorem frontierValue_source_maskAt (answers : Answers) (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 24)
    (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers (sourceMessages answers) a)
      (sourceMessages (maskAt answers (sourceMessages answers) a)) b =
    frontierValue answers (sourceMessages answers) b := by
  rw [sourceMessages_maskAt answers _ a (Or.inr ha.2)]
  exact frontierValue_maskAt_bounded answers _ a b ha hb hc

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem encodingHash_queries (T : Answers) (lay : Layer) (input : HashInput) :
    SourceReplay.queried T (WCT9.encodingHash lay input) = [.inl (.inr (pad64 input))] := by
  unfold WCT9.encodingHash publicHash
  simp only [map_eq_bind_pure_comp, SourceReplay.queried_bind, SourceReplay.queried_pure,
    List.append_nil]
  rfl

theorem search_queries_congr (T T' : Answers) (L : LeafAddr) (floor : Nat)
    (message : WCT9.LayerMsg) : ∀ fuel start,
    (∀ c < fuel, (∀ c' < c, decodeRow T L floor message (start+c')=none) →
      decodeRow T' L floor message (start+c)=decodeRow T L floor message (start+c)) →
    SourceReplay.queried T' (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message start fuel)=
      SourceReplay.queried T (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start h; rfl
  | succ fuel ih =>
      intro start h
      have hzero : decodeRow T' L floor message start=decodeRow T L floor message start := by
        simpa only [Nat.add_zero] using h 0 (Nat.zero_lt_succ _) (fun c hc => absurd hc (Nat.not_lt_zero _))
      have hrest (hnone : decodeRow T L floor message start=none) :
          SourceReplay.queried T' (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start+1) fuel)=
            SourceReplay.queried T (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start+1) fuel) := by
        apply ih (start+1)
        intro c hc hprev
        have hnext := h (c+1) (by omega) (fun c' hc' => by
          cases c' with
          | zero => simpa only [Nat.add_zero] using hnone
          | succ c' =>
              have hp := hprev c' (by omega)
              simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hp)
        simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hnext
      rw [WCT9.CanonicalPolicy.layerCounterSearchAt]
      conv_lhs => rw [SourceReplay.queried_bind, encodingHash_queries]
      conv_rhs => rw [SourceReplay.queried_bind, encodingHash_queries]
      change _ ++ SourceReplay.queried T' (match decodeRow T' L floor message start with
        | none => WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start+1) fuel
        | some digits => pure (some (BitVec.ofNat 32 start,digits))) =
        _ ++ SourceReplay.queried T (match decodeRow T L floor message start with
        | none => WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start+1) fuel
        | some digits => pure (some (BitVec.ofNat 32 start,digits)))
      rw [hzero]
      cases hd : decodeRow T L floor message start with
      | none => rw [hrest hd]
      | some digits => rfl

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3.Security.Wots.Enc
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem respects_chainPrefixes (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Respects NonEnc (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact Respects.pure' _
  | succ count ih =>
    unfold chainPrefixes
    exact Respects.bind (ClaudeWCT.W9.T3.Security.Wots.Mask.respects_halfHash' _ _
      (nonEnc_chainInputW _ _ _ _ _ _)) fun _ =>
      Respects.bind (ih _ _) fun _ => Respects.pure' _

theorem respects_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    Respects NonEnc (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine Respects.bind ?_ fun _ => ?_
  · unfold lowerCoefs
    exact Respects.foldlM _ _ (fun _ _ _ => Respects.bind (respects_packedSecret _ _ _ _)
      fun _ => Respects.pure' _) _
  · exact Respects.bind (Respects.mapM _ _ fun _ _ => respects_chainPrefixes _ _ _ _ _ _ _) fun _ =>
      Respects.bind (ClaudeWCT.W9.T3.Security.Wots.Enc.respects_lowerLeafHash _ _ _ _
        (by simpa only [List.length_map, List.length_range] using chainCount_ge4 lay)) fun _ => Respects.pure' _

theorem respects_buildTreePrefixes (lay : Layer) (tree selected : Nat) :
    Respects NonEnc (buildTreePrefixes lay tree selected) := by
  unfold buildTreePrefixes
  refine respects_bind_inv (fun rows : List Digest × List (List Digest) × Digest =>
    rows.1.length = 2 ^ height lay) ?_ ?_ ?_
  · exact Respects.foldlM _ _ (fun leaf _ state => by
      split
      · exact Respects.bind (respects_buildLeafPrefixes _ _ _ _) fun _ => Respects.pure' _
      · simp only [bind_assoc, pure_bind]
        exact Respects.bind (respects_buildLeafPF _ _ _ _ _) fun _ => Respects.pure' _) _
  · intro T
    refine Correctness.eval_foldlM_range_inv T (2 ^ height lay) _
      (fun done (rows : List Digest × List (List Digest) × Digest) => rows.1.length = done)
      ([],[],0) rfl ?_
    intro done _ rows hrows
    split <;> simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      List.length_append, List.length_singleton, hrows]
  · intro rows hrows
    exact Respects.bind (respects_buildLevelsBelow _ _ _ (by fin_cases lay <;> decide) (by fin_cases lay <;> decide) _
      (le_of_eq hrows)) fun _ => Respects.pure' _

theorem respects_prepareRoots (index : Nat) : Respects NonEnc (prepareRoots index) := by
  unfold prepareRoots
  exact Respects.bind (respects_buildTreePrefixes _ _ _) fun _ =>
    Respects.bind (respects_buildTreePrefixes _ _ _) fun _ =>
      Respects.bind (respects_buildTreePrefixes _ _ _) fun _ => Respects.pure' _

theorem respects_sharedDigestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    Respects NonEnc (sharedDigestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact Respects.pure' _
  | succ fuel ih =>
    unfold sharedDigestSearch
    refine Respects.bind (SigGolfCandidate.T3.Security.Wots.Enc.respects_digest _ _ _) fun _ => ?_
    split
    · exact Respects.pure' _
    · exact ih _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Mask SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem respects_ftsCoefs (index coord : Nat) : Respects NonEnc (ftsCoefs index coord) := by
  unfold ftsCoefs ftsSeedPair
  exact Respects.foldlM _ _ (fun _ _ _ => Respects.bind (respects_privatePair _ _ _ _ _)
    fun _ => Respects.pure' _) _

theorem respects_buildSharedCoordinate (first : Bool) (index coord : Nat) (hc : coord<9)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    Respects NonEnc (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine Respects.bind (respects_ftsCoefs index coord) fun _ => ?_
  refine Respects.bind (Respects.foldlM _ _ (fun j hj _ => ?_) _) fun _ => ?_
  · have hraw := rawChild_lt first j (List.mem_range.mp hj)
    exact Respects.bind (ClaudeWCT.WCT9.Wots.Enc.respects_buildChildH _ _ _ _ _ _ _ hc hraw)
      fun _ => Respects.pure' _
  · exact Respects.bind (WCT9.Wots.respects_of_allQueriesSatisfy
      (sharedHeap_nonEnc first index coord hc pads _)) fun _ => Respects.pure' _

theorem respects_buildPair (index pair : Nat) (hp : pair<4) (selected : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (previous : PairRoot) :
    Respects NonEnc (buildPair index pair selected aWord bWord previous) := by
  unfold buildPair
  exact Respects.bind (respects_buildSharedCoordinate true index (2*pair) (by omega) _ _ _) fun _ =>
    Respects.bind (respects_buildSharedCoordinate false index (2*pair+1) (by omega) _ _ _)
      fun _ => Respects.pure' _

theorem respects_buildSingleton (index : Nat) (selected : Child) (word : Rank) (previous : PairRoot) :
    Respects NonEnc (buildSingleton index selected word previous) := by
  unfold buildSingleton
  exact Respects.bind (respects_buildSharedCoordinate false index 8 (by decide) _ _ _)
    fun _ => Respects.pure' _

theorem respects_buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Respects NonEnc (buildForest index selected words) := by
  unfold buildForest
  exact Respects.bind (Respects.foldlM _ _ (fun pair _ _ =>
    Respects.bind (respects_buildPair index pair.val pair.isLt _ _ _ _) fun _ => Respects.pure' _) _) fun _ =>
      Respects.bind (respects_buildSingleton _ _ _ _) fun _ => Respects.pure' _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Equality of both the result and the charged query trace at two fixed worlds. -/
def RunEq (T T' : Answers) {α : Type} (p : M α) : Prop :=
  evalWithAnswerFn T' p=evalWithAnswerFn T p ∧
    SourceReplay.queried T' p=SourceReplay.queried T p

theorem RunEq.pure' (T T' : Answers) {α : Type} (value : α) :
    RunEq T T' (pure value) := ⟨rfl,rfl⟩

theorem RunEq.of_respects {T T' : Answers} {S : SigGolfCandidate.T3.Spec.Domain → Prop} {α : Type} {p : M α}
    (hp : Respects S p) (h : ∀ q, S q → T' q=T q) : RunEq T T' p := hp T' T h

theorem RunEq.bind {T T' : Answers} {α β : Type} {p : M α} {f : α → M β}
    (hp : RunEq T T' p)
    (hf : ∀ value, evalWithAnswerFn T p=value → RunEq T T' (f value)) :
    RunEq T T' (p >>= f) := by
  have hx := hf (evalWithAnswerFn T p) rfl
  constructor
  · rw [evalWithAnswerFn_bind,evalWithAnswerFn_bind,hp.1]
    exact hx.1
  · rw [SourceReplay.queried_bind,SourceReplay.queried_bind,hp.1,hp.2,hx.2]

theorem sourceLeaf_source (index : Nat) (hi : index<2^31) (lay : Layer) :
    WotsExtract.SourceLeaf7 (sourceLeaf index lay) :=
  Enc.routePos_source index hi lay

theorem search_runEq {T T' : Answers} {messages : LeafAddr → LayerMsg}
    (hdecisions : DecisionsAgree T T' messages) (leaf : LeafAddr)
    (hleaf : WotsExtract.SourceLeaf7 leaf) (remaining : Nat)
    (hc : referenceContext T messages leaf=some remaining) :
    RunEq T T' (CanonicalPolicy.layerCounterSearchAt leaf.lay
      (CanonicalPolicy.threshold leaf.lay.val remaining) leaf.tree leaf.leaf
      (messages leaf) 0 (searchLimit leaf.lay)) := by
  have hd : ∀ c<searchLimit leaf.lay,
      (∀ c'<c, decodeRow T leaf (CanonicalPolicy.threshold leaf.lay.val remaining)
        (messages leaf) (0+c')=none) →
      decodeRow T' leaf (CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) (0+c)=
        decodeRow T leaf (CanonicalPolicy.threshold leaf.lay.val remaining) (messages leaf) (0+c) := by
    simpa only [Nat.zero_add] using hdecisions leaf hleaf remaining hc
  exact ⟨search_congr T T' leaf _ _ _ _ hd,search_queries_congr T T' leaf _ _ _ _ hd⟩

theorem referenceSearch_of_run {T : Answers} {messages : LeafAddr → LayerMsg}
    {leaf : LeafAddr} {remaining : Nat} {counter : BitVec 32} {digits : List Nat}
    (hc : referenceContext T messages leaf=some remaining)
    (hr : evalWithAnswerFn T (CanonicalPolicy.layerCounterSearchAt leaf.lay
      (CanonicalPolicy.threshold leaf.lay.val remaining) leaf.tree leaf.leaf
      (messages leaf) 0 (searchLimit leaf.lay))= some (counter,digits)) :
    referenceSearch T messages leaf= some (counter,digits) :=
  referenceSearch_of_context hc hr

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem searchPreparedLayers_runEq {T T' : Answers} {messages : LeafAddr → LayerMsg}
    (hdecisions : DecisionsAgree T T' messages)
    (hnon : ∀ q, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc q → T' q=T q)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (prepared : PreparedRoots) (forest : PairRoot)
    (h0 : LayerMsg.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2 =
      messages (sourceLeaf index 0))
    (h1 : LayerMsg.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2 =
      messages (sourceLeaf index 1))
    (h2 : LayerMsg.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2 =
      messages (sourceLeaf index 2))
    (h3 : LayerMsg.pair forest.1 forest.2 = messages (sourceLeaf index 3)) :
    RunEq T T' (searchPreparedLayers cache index prepared forest) := by
  have hs (lay : Layer) (remaining : Nat)
      (hc : referenceContext T messages (sourceLeaf index lay)=some remaining) :=
    search_runEq hdecisions (sourceLeaf index lay) (sourceLeaf_source index hi lay) remaining hc
  have hc0 : referenceContext T messages (sourceLeaf index 0)=some 63 := rfl
  unfold searchPreparedLayers
  dsimp only
  rw [h0,h1,h2,h3]
  refine RunEq.bind (hs 0 63 hc0) ?_
  intro found0 hr0
  cases found0 with
  | none => exact RunEq.pure' _ _ _
  | some found0 =>
    rcases found0 with ⟨counter0,digits0⟩
    have href0 := referenceSearch_of_run hc0 hr0
    have hc1 : referenceContext T messages (sourceLeaf index 1)=
        some (CanonicalPolicy.nextResidual 63 0 digits0) := by
      apply context_parent_success (leaf:=sourceLeaf index 1) (by change 1 ≠ 0; decide)
      · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
      · rw [sourceLeaf_parent index 1 (by decide)]; exact href0
    dsimp only
    split
    · exact RunEq.pure' _ _ _
    · refine RunEq.bind (hs 1 _ hc1) ?_
      intro found1 hr1
      cases found1 with
      | none => exact RunEq.pure' _ _ _
      | some found1 =>
        rcases found1 with ⟨counter1,digits1⟩
        have href1 := referenceSearch_of_run hc1 hr1
        have hc2 : referenceContext T messages (sourceLeaf index 2)=
            some (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 63 0 digits0) 1 digits1) := by
          apply context_parent_success (leaf:=sourceLeaf index 2) (by change 2 ≠ 0; decide)
          · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
          · rw [sourceLeaf_parent index 2 (by decide)]; exact href1
        dsimp only
        split
        · exact RunEq.pure' _ _ _
        · refine RunEq.bind (hs 2 _ hc2) ?_
          intro found2 hr2
          cases found2 with
          | none => exact RunEq.pure' _ _ _
          | some found2 =>
            rcases found2 with ⟨counter2,digits2⟩
            have href2 := referenceSearch_of_run hc2 hr2
            have hc3 : referenceContext T messages (sourceLeaf index 3)=
                some (CanonicalPolicy.nextResidual
                  (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 63 0 digits0) 1 digits1) 2 digits2) := by
              apply context_parent_success (leaf:=sourceLeaf index 3) (by change 3 ≠ 0; decide)
              · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
              · rw [sourceLeaf_parent index 3 (by decide)]; exact href2
            dsimp only
            split
            · exact RunEq.pure' _ _ _
            · refine RunEq.bind (hs 3 _ hc3) ?_
              intro found3 hr3
              cases found3 with
              | none => exact RunEq.pure' _ _ _
              | some found3 =>
                rcases found3 with ⟨counter3,digits3⟩
                exact RunEq.bind (RunEq.of_respects
                  (SigGolfCandidate.T3.Security.Wots.Enc.respects_signTop _ _ _) hnon)
                  fun _ _ => RunEq.pure' _ _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

private theorem prepared_message0 (T : Answers) (index : Nat) :
    let prepared := evalWithAnswerFn T (prepareRoots index)
    LayerMsg.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2 =
      sourceMessages T (sourceLeaf index 0) := by
  rw [prepareRoots_result,sourceMessages_route_lower T index 0 (by decide)]
  simp only [fixedPrepared_pair]
  rfl
private theorem prepared_message1 (T : Answers) (index : Nat) :
    let prepared := evalWithAnswerFn T (prepareRoots index)
    LayerMsg.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2 =
      sourceMessages T (sourceLeaf index 1) := by
  rw [prepareRoots_result,sourceMessages_route_lower T index 1 (by decide)]
  simp only [fixedPrepared_pair]
  rfl
private theorem prepared_message2 (T : Answers) (index : Nat) :
    let prepared := evalWithAnswerFn T (prepareRoots index)
    LayerMsg.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2 =
      sourceMessages T (sourceLeaf index 2) := by
  rw [prepareRoots_result,sourceMessages_route_lower T index 2 (by decide)]
  simp only [fixedPrepared_pair]
  rfl

theorem signFromOutput_runEq {T T' : Answers}
    (hdecisions : DecisionsAgree T T' (sourceMessages T))
    (hnon : ∀ q, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc q → T' q=T q)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    RunEq T T' (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine RunEq.bind (RunEq.of_respects (respects_buildForest _ _ _) hnon) ?_
  intro forest hforest
  refine RunEq.bind (RunEq.of_respects (respects_prepareRoots _) hnon) ?_
  intro prepared hprepared
  refine RunEq.bind (searchPreparedLayers_runEq hdecisions hnon cache _
    (digestIndex_lt output) prepared forest.2 ?_ ?_ ?_ ?_) ?_
  · rw [←hprepared]; exact prepared_message0 T _
  · rw [←hprepared]; exact prepared_message1 T _
  · rw [←hprepared]; exact prepared_message2 T _
  · rw [←hforest,buildForest_commitment,sourceMessages_route_bottom T _ (digestIndex_lt output)]
  · intro layers _
    cases layers <;> exact RunEq.pure' _ _ _

theorem signPayload_runEq {T T' : Answers}
    (hdecisions : DecisionsAgree T T' (sourceMessages T))
    (hnon : ∀ q, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc q → T' q=T q)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    RunEq T T' (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine RunEq.bind (RunEq.of_respects
    (SigGolfCandidate.T3.Security.Wots.Enc.respects_privateNonce _) hnon) ?_
  intro rho _
  refine RunEq.bind (RunEq.of_respects (respects_sharedDigestSearch _ _ _ _) hnon) ?_
  intro selected _
  cases selected with
  | none => exact RunEq.pure' _ _ _
  | some selected =>
    rcases selected with ⟨counter,output⟩
    exact RunEq.bind (signFromOutput_runEq hdecisions hnon _ _ _ _) fun result _ => by
      cases result <;> exact RunEq.pure' _ _ _

theorem authenticatedSign_runEq {T T' : Answers}
    (hdecisions : DecisionsAgree T T' (sourceMessages T))
    (hnon : ∀ q, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc q → T' q=T q)
    (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    RunEq T T' (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine RunEq.bind (RunEq.of_respects
    (SigGolfCandidate.T3.Security.Wots.Enc.respects_privateMac _) hnon) ?_
  intro _ _
  split
  · exact signPayload_runEq hdecisions hnon _ _
  · exact RunEq.pure' _ _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem referenceGame_decisions {T T' : Answers}
    (hdecisions : DecisionsAgree T T' (sourceMessages T))
    (hnon : ∀ q, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc q → T' q=T q)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T' adversary q=PairedReference.referenceGame T adversary q := by
  have hkey := SigGolfCandidate.T3.Security.Wots.Enc.respects_keygen T' T hnon
  exact PairedReference.referenceGame_congr T' T hkey.1 (congrArg List.length hkey.2)
    (fun cache request => (authenticatedSign_runEq hdecisions hnon cache request).1)
    (fun cache request => congrArg List.length (authenticatedSign_runEq hdecisions hnon cache request).2)
    adversary q

theorem referenceGame_overwrite {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
    (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (values : (cellKey (eagerAnswers U privateTable pub)
      (sourceMessages (eagerAnswers U privateTable pub))).cells → HashOutput)
    (hvalues : ∀ entry, values entry ∈ cellInit
      (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))) entry)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame (eagerAnswers U privateTable
      (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub values)) adversary q =
      PairedReference.referenceGame (eagerAnswers U privateTable pub) adversary q :=
  referenceGame_decisions (overwrite_decisions hU privateTable pub _
    (fun leaf _ => sourceMessages_fit _ leaf) values hvalues)
    (overwrite_nonEnc privateTable pub _ values) adversary q

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem respectsP_ftsCoefs (a : ChainAddr) (index coord : Nat) : Respects (UntouchedP a) (ftsCoefs index coord) := by
  apply ClaudeWCT.W9.T3.Security.Wots.Mask.Respects.untouchedP (a := a)
  intro c
  unfold ftsCoefs ftsSeedPair
  exact Respects.foldlM _ _ (fun _ _ _ => Respects.bind (Respects.privatePair _ _ _ _ _ (untouched_privatePair c (by decide) _ _ _ _))
    fun _ => Respects.pure' _) _

theorem respectsP_buildSharedCoordinate (a : ChainAddr) (first : Bool) (index coord : Nat) (hc : coord<9)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    Respects (UntouchedP a) (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine Respects.bind (respectsP_ftsCoefs a index coord) fun _ => ?_
  refine Respects.bind (Respects.foldlM _ _ (fun j hj _ => ?_) _) fun _ => ?_
  · have hraw := rawChild_lt first j (List.mem_range.mp hj)
    exact Respects.bind (ClaudeWCT.W9.T3.Security.Wots.Mask.Respects.untouchedP (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_buildChildH c index (128 + j) coord (rawChild first j) _ _ _ hc hraw) a)
      fun _ => Respects.pure' _
  · exact Respects.bind (WCT9.Wots.respects_of_allQueriesSatisfy
      (sharedHeap_untouched a first index coord pads _)) fun _ => Respects.pure' _

theorem respectsP_buildPair (a : ChainAddr) (index pair : Nat) (hp : pair<4) (selected : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (previous : PairRoot) :
    Respects (UntouchedP a) (buildPair index pair selected aWord bWord previous) := by
  unfold buildPair
  exact Respects.bind (respectsP_buildSharedCoordinate a true index (2*pair) (by omega) _ _ _) fun _ =>
    Respects.bind (respectsP_buildSharedCoordinate a false index (2*pair+1) (by omega) _ _ _)
      fun _ => Respects.pure' _

theorem respectsP_buildSingleton (a : ChainAddr) (index : Nat) (selected : Child) (word : Rank) (previous : PairRoot) :
    Respects (UntouchedP a) (buildSingleton index selected word previous) := by
  unfold buildSingleton
  exact Respects.bind (respectsP_buildSharedCoordinate a false index 8 (by decide) _ _ _)
    fun _ => Respects.pure' _

theorem respectsP_buildForest (a : ChainAddr) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Respects (UntouchedP a) (buildForest index selected words) := by
  unfold buildForest
  exact Respects.bind (Respects.foldlM _ _ (fun pair _ _ =>
    Respects.bind (respectsP_buildPair a index pair.val pair.isLt _ _ _ _) fun _ => Respects.pure' _) _) fun _ =>
      Respects.bind (respectsP_buildSingleton a _ _ _ _) fun _ => Respects.pure' _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace Mask

theorem queried_length_chainPrefixes (T : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) :
    (SourceReplay.queried T (chainPrefixes lay tree leaf i start count value)).length=count := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    -- C3 (#866): a prefix step is a half hash (one query).
    simp only [chainPrefixes,queried_length_bind,ClaudeWCT.W9.T3.Security.Wots.Mask.queried_length_halfHash,
      queried_length_pure,ih]
    omega

theorem queried_length_buildLeafPrefixes (T : Answers) (lay : Layer)
    (tree leaf : Nat) (carry : Digest) :
    (SourceReplay.queried T (buildLeafPrefixes lay tree leaf carry)).length=
      Wots.Mask.leafCountP lay leaf [] := by
  unfold buildLeafPrefixes
  rw [queried_length_bind,Wots.Mask.queried_length_lowerCoefs]
  generalize evalWithAnswerFn T (lowerCoefs lay tree leaf carry)=coefs
  rcases coefs with ⟨coefs,carry⟩
  dsimp only
  rw [queried_length_bind,queried_length_mapM T _ _ (maxDigit lay)
    (fun i _ => queried_length_chainPrefixes T lay tree leaf i 0 _ _),queried_length_bind,
    queried_length_pure]
  -- C2 (#866): the leaf is `lowerLeafHash`, a half hash (one query).
  have hh : ∀ ends, (SourceReplay.queried T (lowerLeafHash lay tree leaf ends)).length=1 := fun _ => by
    unfold lowerLeafHash leafHashW lowerHash
    exact ClaudeWCT.W9.T3.Security.Wots.Mask.queried_length_halfHash _ _ _
  rw [hh]
  simp only [Wots.Mask.leafCountP,List.getD_nil,Nat.zero_add,Nat.sub_zero,Nat.add_zero,Nat.add_assoc]

theorem queried_length_prefixTreeRows (T : Answers) (lay : Layer) (tree selected : Nat) :
    (SourceReplay.queried T (prefixTreeRows lay tree selected)).length=
      ((List.range (2^height lay)).map fun leaf => Wots.Mask.leafCountP lay leaf []).sum := by
  unfold prefixTreeRows
  apply queried_length_foldlM
  intro leaf hleaf state
  by_cases hs : leaf=selected
  · simp only [hs,↓reduceIte]
    rw [queried_length_bind,queried_length_buildLeafPrefixes]
    generalize evalWithAnswerFn T (buildLeafPrefixes lay tree leaf state.2.2)=r
    rcases r with ⟨⟨root,prefixes⟩,carry⟩
    simp only [queried_length_pure,Nat.add_zero]
  · simp only [hs,↓reduceIte]
    rw [queried_length_bind,Wots.Mask.queried_length_buildLeafPF]
    generalize evalWithAnswerFn T (buildLeafPF lay tree leaf [] state.2.2)=r
    rcases r with ⟨⟨root,prefixes⟩,carry⟩
    simp only [pure_bind,queried_length_pure,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Nat.add_zero]

/-- C2 (#866): a lower level makes one (half-hash) query per node. -/
theorem queried_length_lowerLevel (T : Answers) (lay tree h level : Nat) (nodes : List Digest) :
    (SourceReplay.queried T (lowerLevel lay tree h level nodes)).length = nodes.length / 2 := by
  unfold lowerLevel
  rw [queried_length_mapM T _ _ (fun _ => 1) (fun i _ => by
      unfold lowerNodeHash lowerHash
      exact ClaudeWCT.W9.T3.Security.Wots.Mask.queried_length_halfHash _ _ _),
    sum_map_one, List.length_range]

/-- C2 (#866): `buildLevelsBelow` folds `lowerLevel`. -/
theorem queried_length_buildLevelsBelow_congr (T T' : Answers) (tag lay tree h : Nat)
    (leaves leaves' : List Digest) (hlen : leaves.length=leaves'.length) :
    (SourceReplay.queried T (buildLevelsBelow tag lay tree h leaves)).length=
      (SourceReplay.queried T' (buildLevelsBelow tag lay tree h leaves')).length := by
  unfold buildLevelsBelow
  suffices H : ∀ (ls : List Nat) (s s' : List (List Digest)), s.map List.length = s'.map List.length →
      (SourceReplay.queried T (ls.foldlM (fun levels level => do
        let nodes ← lowerLevel lay tree h level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s)).length =
      (SourceReplay.queried T' (ls.foldlM (fun levels level => do
        let nodes ← lowerLevel lay tree h level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s')).length from H _ _ _ (by simp [hlen])
  intro ls
  induction ls with
  | nil => intro s s' _; rfl
  | cons level ls ih =>
      intro s s' hs
      simp only [List.foldlM_cons, queried_length_bind, queried_length_lowerLevel, queried_length_pure,
        Nat.add_zero, getD_length_of_map hs]
      congr 1
      apply ih
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.map_append, List.map_cons, List.map_nil,
        ClaudeWCT.WCT9.eval_lowerLevel_length, hs, getD_length_of_map hs]

theorem queried_length_buildTreePrefixes_congr (T T' : Answers) (lay : Layer) (hlay : lay ≠ 0)
    (tree selected : Nat) :
    (SourceReplay.queried T (buildTreePrefixes lay tree selected)).length=
      (SourceReplay.queried T' (buildTreePrefixes lay tree selected)).length := by
  simp only [buildTreePrefixes_factor,queried_length_bind,queried_length_prefixTreeRows,
    queried_length_pure,Nat.add_zero]
  congr 1
  apply queried_length_buildLevelsBelow_congr
  exact (eval_prefixTreeRows T hlay tree selected).1.trans (eval_prefixTreeRows T' hlay tree selected).1.symm

theorem queried_length_prepareRoots_congr (T T' : Answers) (index : Nat) :
    (SourceReplay.queried T (prepareRoots index)).length=
      (SourceReplay.queried T' (prepareRoots index)).length := by
  simp only [prepareRoots,queried_length_bind,queried_length_pure]
  rw [queried_length_buildTreePrefixes_congr T T' 1 (by decide),
    queried_length_buildTreePrefixes_congr T T' 2 (by decide),
    queried_length_buildTreePrefixes_congr T T' 3 (by decide)]
end Mask
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Mask
open ClaudeWCT.W9.T3.Security.Wots.Mask
variable (answers : Answers) (messages : LeafAddr → LayerMsg) (a : ChainAddr)

theorem wotsValues_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → a.chain < chainCount lay → depth answers messages a ≤ digits.getD a.chain 0) :
    (List.range (chainCount lay)).map (wotsValue (maskAt answers messages a) lay tree leaf digits) =
      (List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits) := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  apply wotsValue_maskAt answers messages a lay tree leaf digits i hi'
  · have := hvalid i hi'
    have := width_le lay i
    omega
  · exact hb
  · intro hal hia
    subst hia
    exact halias hal hi'

theorem eval_topPath_maskAt (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) :
    evalWithAnswerFn (maskAt answers messages a) (topPath cache leaf) = evalWithAnswerFn answers (topPath cache leaf) := by
  apply eval_maskAt_of_respects
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsP_mask a _ _) fun _ => Respects.pure' _

theorem eval_signTop_maskAt (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (halias : LeafAlias 0 0 leaf a.key → a.chain < chainCount 0 → depth answers messages a ≤ digits.getD a.chain 0) :
    evalWithAnswerFn (maskAt answers messages a) (signTop cache leaf digits) =
      evalWithAnswerFn answers (signTop cache leaf digits) := by
  have hv := wotsValues_maskAt answers messages a 0 0 leaf digits hvalid (Or.inl rfl) halias
  rw [Wots.Mask.eval_signTop_wots _ cache leaf digits hvalid,
    Wots.Mask.eval_signTop_wots _ cache leaf digits hvalid,hv,eval_topPath_maskAt answers messages a]

theorem wotsPieces_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (hb : SlotOK a lay leaf) (hmask : MaskOK a)
    (halias : LeafAlias lay tree leaf a.key → a.chain < chainCount lay → depth answers messages a ≤ digits.getD a.chain 0) :
    wotsPieces (maskAt answers messages a) lay tree leaf digits=wotsPieces answers lay tree leaf digits := by
  unfold wotsPieces
  rw [wotsValues_maskAt answers messages a lay tree leaf digits hvalid hb halias,
    wotsTree_maskAt answers messages a lay tree (Or.inr hmask)]

theorem sourceLeaf_alias {index : Nat} (hindex : index<2^31) {lay : Layer} {counter : BitVec 32}
    {digits : List Nat} (hsearch : referenceSearch answers messages (sourceLeaf index lay)=some (counter,digits))
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (hal : LeafAlias lay (route index lay).2 (route index lay).1 a.key) :
    depth answers messages a≤digits.getD a.chain 0 := by
  have hk : sourceLeaf index lay=a.key :=
    hal.eq_of_lt (SigGolfCandidate.T3.Security.Wots.Mask.route_tree_lt index hindex lay) (SigGolfCandidate.T3.Security.Wots.Mask.route_leaf_lt index lay) htree (by omega)
  unfold depth referenceDigits
  rw [←hk,hsearch]
  simp

theorem source_digits_valid (lay : Layer) {counter : BitVec 32} {digits : List Nat}
    {leaf : LeafAddr} (hsearch : referenceSearch answers messages leaf=some (counter,digits))
    (hlay : leaf.lay=lay) : Cost.ValidDigits lay digits := by
  subst lay
  have hd := referenceSearch_decode answers messages leaf hsearch
  have hv := Cost.validDigits_decode hd
  intro i hi
  simpa only [normalLayer_maxDigit] using hv i (by simpa only [normalLayer_chainCount] using hi)

theorem fixedPrepared_pieces_maskAt (index : Nat) (hi : index<2^31) (lay : Layer) (hlay : lay≠0)
    {counter : BitVec 32} {digits : List Nat}
    (hsearch : referenceSearch answers messages (sourceLeaf index lay)=some (counter,digits))
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24) :
    preparedPieces lay (route index lay).1 (fixedPrepared (maskAt answers messages a) index lay) digits =
      preparedPieces lay (route index lay).1 (fixedPrepared answers index lay) digits := by
  have hv := source_digits_valid answers messages lay hsearch rfl
  have hpiece (T : Answers) : preparedPieces lay (route index lay).1 (fixedPrepared T index lay) digits =
      wotsPieces T lay (route index lay).2 (route index lay).1 digits := by
    unfold fixedPrepared
    rw [←eval_buildTreePrefixes_result T hlay _ _ (route_leaf_bound index lay)]
    exact preparedPieces_result T hlay _ _ digits hv (route_leaf_bound index lay)
  rw [hpiece,hpiece]
  exact wotsPieces_maskAt answers messages a lay _ _ digits hv
    (slotOK_of (Or.inr (maskOK_of_lt hleaf)) (by have := route_leaf_bound index lay; have := height_pow_le lay; omega))
    (maskOK_of_lt hleaf) (fun hal _ => sourceLeaf_alias answers messages a hi hsearch htree hleaf hal)
end Mask
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def ExecEq {α : Type} (T T' : Answers) (p p' : M α) : Prop :=
  evalWithAnswerFn T' p'=evalWithAnswerFn T p ∧
    (SourceReplay.queried T' p').length=(SourceReplay.queried T p).length

theorem ExecEq.pure' {α : Type} (T T' : Answers) (a : α) : ExecEq T T' (pure a) (pure a) := ⟨rfl,rfl⟩
theorem ExecEq.pure_eq {α : Type} (T T' : Answers) {a a' : α} (h : a'=a) :
    ExecEq T T' (pure a) (pure a') := by subst a'; exact .pure' _ _ _
theorem ExecEq.of_runEq {α : Type} {T T' : Answers} {p : M α} (h : RunEq T T' p) :
    ExecEq T T' p p := ⟨h.1,congrArg List.length h.2⟩
theorem ExecEq.bind {α β : Type} {T T' : Answers} {p p' : M α} {f f' : α → M β}
    (hp : ExecEq T T' p p')
    (hf : ∀ a, evalWithAnswerFn T p=a → ExecEq T T' (f a) (f' a)) :
    ExecEq T T' (p >>= f) (p' >>= f') := by
  have hcont := hf (evalWithAnswerFn T p) rfl
  constructor
  · simp only [evalWithAnswerFn_bind,hp.1,hcont.1]
  · simp only [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_bind,hp.1,hp.2,hcont.2]
theorem ExecEq.bind_effect {α β : Type} {T T' : Answers} {p p' : M α} {f f' : α → M β}
    (hp : (SourceReplay.queried T' p').length=(SourceReplay.queried T p).length)
    (hf : ExecEq T T' (f (evalWithAnswerFn T p)) (f' (evalWithAnswerFn T' p'))) :
    ExecEq T T' (p >>= f) (p' >>= f') := by
  constructor
  · simpa only [evalWithAnswerFn_bind] using hf.1
  · simp only [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_bind,hp,hf.2]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem searchPreparedLayers_maskEq (T : Answers) (a : ChainAddr)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (forest : PairRoot) (hforest : LayerMsg.pair forest.1 forest.2=sourceMessages T (sourceLeaf index 3)) :
    let T' := maskAt T (sourceMessages T) a
    let prepared := (⟨fixedPrepared T index 1,fixedPrepared T index 2,fixedPrepared T index 3⟩ : PreparedRoots)
    let prepared' := (⟨fixedPrepared T' index 1,fixedPrepared T' index 2,fixedPrepared T' index 3⟩ : PreparedRoots)
    ExecEq T T' (searchPreparedLayers cache index prepared forest)
      (searchPreparedLayers cache index prepared' forest) := by
  let messages := sourceMessages T
  let T' := maskAt T messages a
  have hlevels (lay : Layer) : (fixedPrepared T' index lay).levels=(fixedPrepared T index lay).levels := by
    dsimp only [fixedPrepared,T']
    rw [Mask.wotsTree_maskAt T messages a lay _ (Or.inr (Wots.Mask.maskOK_of_lt hleaf))]
  have hs (lay : Layer) (remaining : Nat)
      (_hc : referenceContext T messages (sourceLeaf index lay)=some remaining) :
      ExecEq T T' (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay))
        (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay)) :=
    ⟨Mask.eval_maskAt_of_respects T messages a (Mask.respectsP_layerCounterSearchAt a _ _ _ _ _ _ _),
      congrArg List.length (Mask.queried_maskAt_of_respects T messages a (Mask.respectsP_layerCounterSearchAt a _ _ _ _ _ _ _))⟩
  have h0 : LayerMsg.pair (topPair 1 (fixedPrepared T index 1).levels).1
      (topPair 1 (fixedPrepared T index 1).levels).2=messages (sourceLeaf index 0) := by
    dsimp only [messages]
    rw [fixedPrepared_pair,sourceMessages_route_lower T index 0 (by decide)]; rfl
  have h1 : LayerMsg.pair (topPair 2 (fixedPrepared T index 2).levels).1
      (topPair 2 (fixedPrepared T index 2).levels).2=messages (sourceLeaf index 1) := by
    dsimp only [messages]
    rw [fixedPrepared_pair,sourceMessages_route_lower T index 1 (by decide)]; rfl
  have h2 : LayerMsg.pair (topPair 3 (fixedPrepared T index 3).levels).1
      (topPair 3 (fixedPrepared T index 3).levels).2=messages (sourceLeaf index 2) := by
    dsimp only [messages]
    rw [fixedPrepared_pair,sourceMessages_route_lower T index 2 (by decide)]; rfl
  have h3 : LayerMsg.pair forest.1 forest.2=messages (sourceLeaf index 3) := hforest
  have hc0 : referenceContext T messages (sourceLeaf index 0)=some 63 := rfl
  dsimp only
  unfold searchPreparedLayers
  dsimp only
  rw [hlevels 1,hlevels 2,hlevels 3,h0,h1,h2,h3]
  refine ExecEq.bind (hs 0 63 hc0) ?_
  intro found0 hr0
  cases found0 with
  | none => exact ExecEq.pure' _ _ _
  | some found0 =>
    rcases found0 with ⟨counter0,digits0⟩
    have href0 := referenceSearch_of_run hc0 hr0
    have hc1 : referenceContext T messages (sourceLeaf index 1)=
        some (CanonicalPolicy.nextResidual 63 0 digits0) := by
      apply context_parent_success (leaf:=sourceLeaf index 1) (by change 1 ≠ 0; decide)
      · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
      · rw [sourceLeaf_parent index 1 (by decide)]; exact href0
    dsimp only
    split
    · exact ExecEq.pure' _ _ _
    · refine ExecEq.bind (hs 1 _ hc1) ?_
      intro found1 hr1
      cases found1 with
      | none => exact ExecEq.pure' _ _ _
      | some found1 =>
        rcases found1 with ⟨counter1,digits1⟩
        have href1 := referenceSearch_of_run hc1 hr1
        have hc2 : referenceContext T messages (sourceLeaf index 2)=
            some (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 63 0 digits0) 1 digits1) := by
          apply context_parent_success (leaf:=sourceLeaf index 2) (by change 2 ≠ 0; decide)
          · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
          · rw [sourceLeaf_parent index 2 (by decide)]; exact href1
        dsimp only
        split
        · exact ExecEq.pure' _ _ _
        · refine ExecEq.bind (hs 2 _ hc2) ?_
          intro found2 hr2
          cases found2 with
          | none => exact ExecEq.pure' _ _ _
          | some found2 =>
            rcases found2 with ⟨counter2,digits2⟩
            have href2 := referenceSearch_of_run hc2 hr2
            have hc3 : referenceContext T messages (sourceLeaf index 3)=
                some (CanonicalPolicy.nextResidual
                  (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 63 0 digits0) 1 digits1) 2 digits2) := by
              apply context_parent_success (leaf:=sourceLeaf index 3) (by change 3 ≠ 0; decide)
              · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
              · rw [sourceLeaf_parent index 3 (by decide)]; exact href2
            dsimp only
            split
            · exact ExecEq.pure' _ _ _
            · refine ExecEq.bind (hs 3 _ hc3) ?_
              intro found3 hr3
              cases found3 with
              | none => exact ExecEq.pure' _ _ _
              | some found3 =>
                rcases found3 with ⟨counter3,digits3⟩
                have href3 := referenceSearch_of_run hc3 hr3
                have hv0 := Mask.source_digits_valid T messages 0 href0 rfl
                have ht : ExecEq T T' (signTop cache (route index 0).1 digits0)
                    (signTop cache (route index 0).1 digits0) := by
                  refine ⟨Mask.eval_signTop_maskAt T messages a cache _ _ hv0 ?_,?_⟩
                  · intro hal _
                    apply Mask.sourceLeaf_alias T messages a hi href0 htree hleaf
                    rw [route_top_tree index hi]
                    exact hal
                  · rw [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop,
                      SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop]
                refine ExecEq.bind ht ?_
                intro top _
                apply ExecEq.pure_eq
                rw [Mask.fixedPrepared_pieces_maskAt T messages a index hi 1 (by decide) href1 htree hleaf,
                  Mask.fixedPrepared_pieces_maskAt T messages a index hi 2 (by decide) href2 htree hleaf,
                  Mask.fixedPrepared_pieces_maskAt T messages a index hi 3 (by decide) href3 htree hleaf]


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem ExecEq.of_untouched (T : Answers) (messages : LeafAddr → LayerMsg) (a : ChainAddr)
    {α : Type} {p : M α} (h : Respects (UntouchedP a) p) :
    ExecEq T (maskAt T messages a) p p :=
  ⟨Mask.eval_maskAt_of_respects T messages a h,
    congrArg List.length (Mask.queried_maskAt_of_respects T messages a h)⟩

theorem signFromOutput_maskEq (T : Answers) (a : ChainAddr)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ExecEq T (maskAt T (sourceMessages T) a)
      (signFromOutput cache rho counter output) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine ExecEq.bind (ExecEq.of_untouched T _ a (respectsP_buildForest a _ _ _)) ?_
  intro forest hforest
  refine ExecEq.bind_effect (Mask.queried_length_prepareRoots_congr _ _ _) ?_
  simp only [prepareRoots_result]
  refine ExecEq.bind (searchPreparedLayers_maskEq T a htree hleaf cache _ (digestIndex_lt output) forest.2 ?_) ?_
  · rw [←hforest,buildForest_commitment,sourceMessages_route_bottom T _ (digestIndex_lt output)]
  · intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem respectsP_sharedDigestSearch (a : ChainAddr) (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (UntouchedP a) (sharedDigestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro _; exact Respects.pure' _
  | succ fuel ih =>
    intro counter
    unfold sharedDigestSearch
    refine Respects.bind (Wots.Mask.respectsP_digest a _ _ _) fun _ => ?_
    split
    · exact Respects.pure' _
    · exact ih _

theorem signPayload_maskEq (T : Answers) (a : ChainAddr)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    ExecEq T (maskAt T (sourceMessages T) a)
      (SigGolfCandidate.Research.SharedForest.signPayload cache message)
      (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine ExecEq.bind (ExecEq.of_untouched T _ a (Wots.Mask.respectsP_privateNonce a _)) ?_
  intro rho _
  refine ExecEq.bind (ExecEq.of_untouched T _ a (respectsP_sharedDigestSearch a _ _ _ _)) ?_
  intro selected _
  cases selected with
  | none => exact ExecEq.pure' _ _ _
  | some selected =>
    rcases selected with ⟨counter,output⟩
    refine ExecEq.bind (signFromOutput_maskEq T a htree hleaf _ _ _ _) ?_
    intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem authenticatedSign_maskEq (T : Answers) (a : ChainAddr)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    ExecEq T (maskAt T (sourceMessages T) a)
      (PairedOuter.FullGame.authenticatedSign published request)
      (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine ExecEq.bind (ExecEq.of_untouched T _ a (Wots.Mask.respectsP_privateMac a _)) ?_
  intro tag _
  split
  · exact signPayload_maskEq T a htree hleaf _ _
  · exact ExecEq.pure' _ _ _

theorem keygen_maskEq (T : Answers) (a : ChainAddr) :
    ExecEq T (maskAt T (sourceMessages T) a) SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygen := by
  have hp : ExecEq T (maskAt T (sourceMessages T) a) keygenPayload keygenPayload := by
    refine ⟨?_,?_⟩
    · rw [Wots.Mask.eval_keygenPayload_wots,Wots.Mask.eval_keygenPayload_wots,
        Mask.wotsTree_maskAt T _ a 0 0 (Or.inl rfl)]
      exact Mask.eval_maskAt_of_respects T _ a (ClaudeWCT.W9.T3.Security.Wots.Mask.Respects.untouchedP (fun c => Wots.Mask.respects_keygenRest c _) a)
    · exact queried_length_keygenPayload_congr _ _
  unfold SigGolfCandidate.T3.keygen
  refine ExecEq.bind hp ?_
  rintro ⟨pk,region⟩ _
  exact ExecEq.bind (ExecEq.of_untouched T _ a (Wots.Mask.respectsP_privateMac a _))
    fun _ _ => ExecEq.pure' _ _ _

theorem referenceGame_maskAt (T : Answers) (a : ChainAddr)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame (maskAt T (sourceMessages T) a) adversary q=
      PairedReference.referenceGame T adversary q :=
  PairedReference.referenceGame_congr _ _ (keygen_maskEq T a).1 (keygen_maskEq T a).2
    (fun cache request => (authenticatedSign_maskEq T a htree hleaf cache request).1)
    (fun cache request => (authenticatedSign_maskEq T a htree hleaf cache request).2) adversary q
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security.Wots.Enc
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace MessageSwap
variable (left right : LeafAddr → LayerMsg)
  (hleft : ∀ L, ClaudeWCT.W9.T3M.Extract.msgFits L.lay (left L))
  (hright : ∀ L, ClaudeWCT.W9.T3M.Extract.msgFits L.lay (right L))

noncomputable def index (e : ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) : ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex :=
  ⟨(e.1.1, Equiv.swap (left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf e.1.1)) (right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf e.1.1)) e.1.2.1,
    e.1.2.2.1,e.1.2.2.2),e.2.1,by
      refine ⟨?_,e.2.2.2⟩
      by_cases hl : e.1.2.1=left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf e.1.1)
      · rw [hl,Equiv.swap_apply_left]; exact hright _
      · by_cases hr : e.1.2.1=right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf e.1.1)
        · rw [hr,Equiv.swap_apply_right]; exact hleft _
        · rw [Equiv.swap_apply_of_ne_of_ne hl hr]; exact e.2.2.1⟩

theorem index_involutive : Function.Involutive (index left right hleft hright) := by
  intro e
  apply Subtype.ext
  simp only [index,Equiv.swap_apply_self]

theorem index_comm : index left right hleft hright=index right left hright hleft := by
  funext e
  apply Subtype.ext
  simp only [index,Equiv.swap_comm]

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

noncomputable def table (pub : U → HashOutput) : U → HashOutput :=
  ClaudeWCT.W9.T3.Security.Wots.Enc.ov Set.univ pub (fun e => ClaudeWCT.W9.T3.Security.Wots.Enc.rd hU Set.univ pub ⟨index left right hleft hright e.1,Set.mem_univ _⟩)

theorem table_at (pub : U → HashOutput) (e : ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) :
    table left right hleft hright hU pub ⟨ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e,hU (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_short e)⟩ =
      pub ⟨ClaudeWCT.W9.T3.Security.Wots.Enc.encInput (index left right hleft hright e),hU (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_short _)⟩ := by
  exact ClaudeWCT.W9.T3.Security.Wots.Enc.ov_at hU Set.univ pub _ ⟨e,Set.mem_univ _⟩

theorem table_other (pub : U → HashOutput) (u : U) (hu : ∀ e, ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e≠u.val) :
    table left right hleft hright hU pub u=pub u :=
  ClaudeWCT.W9.T3.Security.Wots.Enc.ov_other _ _ _ _ (fun e _ => hu e)

theorem table_involutive : Function.Involutive (table left right hleft hright hU) := by
  intro pub
  funext u
  by_cases he : ∃ e,ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e=u.val
  · obtain ⟨e,he⟩:=he
    have hu : u=⟨ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e,hU (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_short e)⟩:=Subtype.ext he.symm
    rw [hu,table_at,table_at,index_involutive]
  · push_neg at he
    rw [table_other _ _ _ _ _ _ _ he,table_other _ _ _ _ _ _ _ he]

theorem table_comm : table left right hleft hright hU=table right left hright hleft hU := by
  unfold table
  rw [index_comm]

end MessageSwap
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.MessageSwap
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.WCT9
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable (left right : LeafAddr → LayerMsg)
  (hleft : ∀ L, ClaudeWCT.W9.T3M.Extract.msgFits L.lay (left L))
  (hright : ∀ L, ClaudeWCT.W9.T3M.Extract.msgFits L.lay (right L))
  {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
  (priv : FullGame.FullTable) (pub : U → HashOutput)

theorem answers_nonEnc (query : Spec.Domain) (hq : NonEnc query) :
    eagerAnswers U priv (table left right hleft hright hU pub) query=eagerAnswers U priv pub query := by
  rcases query with (coin | input) | coordinate
  · rfl
  · by_cases hu : input ∈ U
    · rw [eagerAnswers_public_mem U priv _ ⟨input,hu⟩,eagerAnswers_public_mem U priv _ ⟨input,hu⟩]
      apply table_other
      intro e he
      have hh := ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_encHeader e
      change ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e=input at he
      rw [he] at hh
      exact hq hh
    · rw [eagerAnswers_public_not_mem U priv _ input hu,eagerAnswers_public_not_mem U priv _ input hu]
  · rfl

theorem index_right (L : CanonGraph.LeafPos) (hL : L.Source) (counter : BitVec 32) (pad : RowPad) :
    index left right hleft hright
      (ClaudeWCT.W9.T3.Security.Wots.Enc.encIdx L hL (right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) counter pad (hright _))=
      ClaudeWCT.W9.T3.Security.Wots.Enc.encIdx L hL (left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) counter pad (hleft _) := by
  apply Subtype.ext
  simp only [index,ClaudeWCT.W9.T3.Security.Wots.Enc.encIdx,Equiv.swap_apply_right]

theorem answers_row (L : CanonGraph.LeafPos) (hL : L.Source) (counter : BitVec 32) (pad : RowPad) :
    eagerAnswers U priv (table left right hleft hright hU pub)
      (.inl (.inr (encRow (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L) (right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) counter pad)))=
    eagerAnswers U priv pub
      (.inl (.inr (encRow (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L) (left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) counter pad))) := by
  rw [←ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_encIdx L hL _ counter pad (hright _),
    ←ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_encIdx L hL _ counter pad (hleft _)]
  rw [eagerAnswers_public_mem U priv _ ⟨_,hU (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_short _)⟩,
    eagerAnswers_public_mem U priv _ ⟨_,hU (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_short _)⟩,
    table_at,index_right]

theorem search (L : CanonGraph.LeafPos) (hL : L.Source) (floor : Nat) : ∀ fuel counter,
    evalWithAnswerFn (eagerAnswers U priv (table left right hleft hright hU pub))
      (CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree.val L.leaf.val
        (right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) counter fuel)=
    evalWithAnswerFn (eagerAnswers U priv pub)
      (CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree.val L.leaf.val
        (left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
    intro counter
    simp only [CanonicalPolicy.layerCounterSearchAt,evalWithAnswerFn_bind]
    have hh : evalWithAnswerFn (eagerAnswers U priv (table left right hleft hright hU pub))
        (encodingHash L.lay (layerEncodingInput L.lay L.tree.val L.leaf.val
          (right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) (BitVec.ofNat 32 counter)))=
      evalWithAnswerFn (eagerAnswers U priv pub)
        (encodingHash L.lay (layerEncodingInput L.lay L.tree.val L.leaf.val
          (left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) (BitVec.ofNat 32 counter))) := by
      rw [eval_encodingHash,eval_encodingHash]
      have hr := congrArg (fun input : HashInput =>
        encodingAnswer L.lay (eagerAnswers U priv (table left right hleft hright hU pub) (.inl (.inr input))))
        (ClaudeWCT.W9.T3.Security.Wots.encRow_zero (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)
          (right (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) (BitVec.ofNat 32 counter))
      have hl := congrArg (fun input : HashInput =>
        encodingAnswer L.lay (eagerAnswers U priv pub (.inl (.inr input))))
        (ClaudeWCT.W9.T3.Security.Wots.encRow_zero (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)
          (left (ClaudeWCT.W9.T3.Security.Wots.Enc.leafOf L)) (BitVec.ofNat 32 counter))
      exact hr.symm.trans ((congrArg (encodingAnswer L.lay)
        (answers_row left right hleft hright hU priv pub L hL (BitVec.ofNat 32 counter) 0)).trans hl)
    rw [hh]
    split
    · exact ih _
    · rfl
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.MessageSwap

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace Normalized
noncomputable local instance : Fintype Coordinate := coordinateFintype
abbrev Tables (U : Finset HashInput) := FullGame.FullTable × (U → HashOutput)
def zeroMessages (_ : LeafAddr) : LayerMsg := .pair 0 0
theorem zeroMessages_fit (L : LeafAddr) : ClaudeWCT.W9.T3M.Extract.msgFits L.lay (zeroMessages L) := by
  unfold zeroMessages ClaudeWCT.W9.T3M.Extract.msgFits
  split <;> trivial
noncomputable def raw {U : Finset HashInput} (R : Tables U) : Answers := eagerAnswers U R.1 R.2
noncomputable def normalize {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U) : Tables U :=
  (R.1,MessageSwap.table zeroMessages (sourceMessages (raw R)) zeroMessages_fit (sourceMessages_fit (raw R)) hU R.2)
noncomputable def answers {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U) : Answers :=
  raw (normalize hU R)

theorem nonEnc {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U)
    (q : Spec.Domain) (hq : SigGolfCandidate.T3.Security.Wots.Enc.NonEnc q) :
    answers hU R q=raw R q :=
  MessageSwap.answers_nonEnc _ _ _ _ hU R.1 R.2 q hq

theorem messages {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U) :
    sourceMessages (answers hU R)=sourceMessages (raw R) := by
  funext L
  exact sourceMessages_congr (nonEnc hU R) L

theorem normalize_involutive {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) :
    Function.Involutive (normalize hU) := by
  intro R
  have hm : sourceMessages (raw (normalize hU R))=sourceMessages (raw R) := messages hU R
  apply Prod.ext
  · rfl
  · change MessageSwap.table zeroMessages (sourceMessages (raw (normalize hU R))) zeroMessages_fit
      (sourceMessages_fit (raw (normalize hU R))) hU (normalize hU R).2=R.2
    have ht : MessageSwap.table zeroMessages (sourceMessages (raw (normalize hU R))) zeroMessages_fit
        (sourceMessages_fit (raw (normalize hU R))) hU =
        MessageSwap.table zeroMessages (sourceMessages (raw R)) zeroMessages_fit
          (sourceMessages_fit (raw R)) hU := by
      congr 1
    rw [ht]
    exact MessageSwap.table_involutive _ _ _ _ hU R.2

noncomputable def equiv {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) : Tables U ≃ Tables U :=
  ⟨normalize hU,normalize hU,normalize_involutive hU,normalize_involutive hU⟩

theorem uniform_normalize {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) :
    (PMF.uniformOfFintype (Tables U)).map (normalize hU)=PMF.uniformOfFintype (Tables U) := by
  ext R
  rw [PMF.map_apply,tsum_eq_single (normalize hU R)]
  · simp only [normalize_involutive hU R,if_true,PMF.uniformOfFintype_apply]
  · intro R' hR'
    apply if_neg
    intro he
    have hh := congrArg (normalize hU) he
    rw [normalize_involutive] at hh
    exact hR' hh.symm

private def sourcePosition (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) : CanonGraph.LeafPos :=
  ⟨L.lay,⟨L.tree,hL.tree_lt⟩,⟨L.leaf,by
    have hh : ∀ lay : Layer,2^height lay≤4096 := by intro lay;fin_cases lay<;>decide
    exact hL.2.trans_le (hh L.lay)⟩⟩

theorem search_eq {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) (remaining : Nat) :
    searchOf (answers hU R) (sourceMessages (answers hU R)) L remaining =
      searchOf (raw R) zeroMessages L remaining := by
  rw [messages]
  unfold searchOf
  exact MessageSwap.search _ _ _ _ hU R.1 R.2 (sourcePosition L hL) hL _ _ _

theorem context_eq {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) :
    referenceContext (answers hU R) (sourceMessages (answers hU R)) L=
      referenceContext (raw R) zeroMessages L := by
  exact context_congr_on _ WotsExtract.SourceLeaf7 (fun _ h hp => source_parent h hp)
    (fun leaf hleaf remaining _ => search_eq hU R leaf hleaf remaining) hL

theorem referenceSearch_eq {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U) (R : Tables U)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) :
    referenceSearch (answers hU R) (sourceMessages (answers hU R)) L=
      referenceSearch (raw R) zeroMessages L := by
  change (referenceContext (answers hU R) (sourceMessages (answers hU R)) L).bind _ =
    (referenceContext (raw R) zeroMessages L).bind _
  rw [context_eq hU R L hL]
  cases hc : referenceContext (raw R) zeroMessages L with
  | none => rfl
  | some remaining => exact search_eq hU R L hL remaining
end Normalized
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sourceLeaf_surjective (L:LeafAddr) (hL:WotsExtract.SourceLeaf7 L) :
 ∃index:Nat,index<2^31 ∧ sourceLeaf index L.lay=L := by
 rcases L with ⟨lay,tree,leaf⟩
 fin_cases lay
 · refine ⟨leaf*524288,?_,?_⟩
   · norm_num [WotsExtract.SourceLeaf7,ClaudeWCT.W9.T3M.Extract.treeBits,height] at hL
     omega
   · simp only [sourceLeaf,route,height]
     norm_num
     have ht : tree=0 := by simpa [WotsExtract.SourceLeaf7,ClaudeWCT.W9.T3M.Extract.treeBits,height] using hL.1
     have hl : leaf<4096 := by simpa [height] using hL.2
     simp [ht,Nat.mod_eq_of_lt hl,Nat.mul_div_assoc]
     omega
 · refine ⟨(tree*128+leaf)*4096,?_,?_⟩
   · norm_num [WotsExtract.SourceLeaf7,ClaudeWCT.W9.T3M.Extract.treeBits,height] at hL
     omega
   · have hl : leaf<128 := by simpa [height] using hL.2
     simp [sourceLeaf,route,height,Nat.mul_div_assoc,Nat.mod_eq_of_lt hl]
     omega
 · refine ⟨(tree*64+leaf)*64,?_,?_⟩
   · norm_num [WotsExtract.SourceLeaf7,ClaudeWCT.W9.T3M.Extract.treeBits,height] at hL
     omega
   · have hl : leaf<64 := by simpa [height] using hL.2
     simp [sourceLeaf,route,height,Nat.mul_div_assoc,Nat.mod_eq_of_lt hl]
     omega
 · refine ⟨tree*64+leaf,?_,?_⟩
   · norm_num [WotsExtract.SourceLeaf7,ClaudeWCT.W9.T3M.Extract.treeBits,height] at hL
     omega
   · have hl : leaf<64 := by simpa [height] using hL.2
     simp [sourceLeaf,route,height,Nat.mul_div_assoc,Nat.mod_eq_of_lt hl]
     omega
#print axioms sourceLeaf_surjective
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceSearch_complete_of_routes (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcomplete : ∀ index : Nat, index<2^31 → ∃ result,
      evalWithAnswerFn answers (searchPreparedLayers cache index
        (evalWithAnswerFn answers (prepareRoots index)) (forestCommitment answers index))=some result)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) :
    referenceSearch answers (sourceMessages answers) L ≠ none := by
  obtain ⟨index,hi,hindex⟩ := sourceLeaf_surjective L hL
  obtain ⟨result,he⟩ := hcomplete index hi
  have hs := (searchPreparedLayers_reference answers cache index hi result he L.lay).2
  rw [hindex] at hs
  rw [hs]
  exact Option.some_ne_none _
#print axioms referenceSearch_complete_of_routes
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def decodeAt (L : EncLeaf) (floor : Nat) (answer : HashOutput) : Option Digest :=
  if (WCT9.CanonicalPolicy.producerDecodeAt L.1.lay floor
    (WCT9.encodingAnswer L.1.lay answer)).isSome then
    some (WCT9.encodingAnswer L.1.lay answer) else none
theorem counterSearch_select (answers : Answers) (lay : Layer) (floor : Nat) (tree leaf : Nat) (message : WCT9.LayerMsg)
    (decodeLay : HashOutput → Option Digest)
    (hdecode : ∀ answer, decodeLay answer =
      if (WCT9.CanonicalPolicy.producerDecodeAt lay floor (WCT9.encodingAnswer lay answer)).isSome then some (WCT9.encodingAnswer lay answer) else none) :
    ∀ fuel start, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf message start fuel) =
      (FirstSuccessTable.select decodeLay (fun i : Fin fuel =>
          answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
            (BitVec.ofNat 32 (start + i.val)))))))).bind
        fun r => (WCT9.CanonicalPolicy.producerDecodeAt lay floor r.2).map fun digits => (BitVec.ofNat 32 (start + r.1.val), digits) := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      simp only [WCT9.CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind, WCT9.eval_encodingHash]
      rw [FirstSuccessTable.select]
      have h0 : answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
          (BitVec.ofNat 32 (start + (0 : Fin (fuel + 1)).val)))))) =
          answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message (BitVec.ofNat 32 start))))) := by
        simp only [Fin.val_zero, Nat.add_zero]
      rw [h0, hdecode]
      generalize answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
        (BitVec.ofNat 32 start))))) = A
      cases hd : WCT9.CanonicalPolicy.producerDecodeAt lay floor (WCT9.encodingAnswer lay A) with
      | some digits =>
          simp only [hd, Option.isSome_some, if_true, evalWithAnswerFn_pure, Option.bind_some, Option.map_some,
            Fin.val_zero, Nat.add_zero]
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          rw [ih (start + 1)]
          have htail : (fun i : Fin fuel => answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
              (BitVec.ofNat 32 (start + (i.succ).val))))))) =
              (fun i : Fin fuel => answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
                (BitVec.ofNat 32 (start + 1 + i.val))))))) := by
            funext i
            rw [Fin.val_succ, show start + (i.val + 1) = start + 1 + i.val by omega]
          rw [htail]
          cases FirstSuccessTable.select decodeLay (fun i : Fin fuel => answers (.inl (.inr
              (pad64 (WCT9.layerEncodingInput lay tree leaf message (BitVec.ofNat 32 (start + 1 + i.val))))))) with
          | none => rfl
          | some r =>
              simp only [Option.map_some, Option.bind_some, Fin.val_succ,
                show start + (r.1.val + 1) = start + 1 + r.1.val by omega]

def encLeafOf (L : Wots.LeafAddr) (h : WotsExtract.SourceLeaf7 L) : EncLeaf :=
  ⟨⟨L.lay, ⟨L.tree, lt_of_lt_of_le h.1 (by
      apply Nat.pow_le_pow_right (by decide)
      generalize L.lay = lay
      fin_cases lay <;> decide)⟩,
    ⟨L.leaf, lt_of_lt_of_le h.2 (by
      calc 2 ^ height L.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
           _ = 4096 := by norm_num)⟩⟩, h⟩

theorem encLeafOf_toWots (L : Wots.LeafAddr) (h : WotsExtract.SourceLeaf7 L) :
    (encLeafOf L h).toWots = L := by cases L; rfl

theorem toWots_injective : Function.Injective EncLeaf.toWots := by
  rintro ⟨⟨l,t,k⟩,h⟩ ⟨⟨l',t',k'⟩,h'⟩ he
  simp only [EncLeaf.toWots, Wots.LeafAddr.mk.injEq] at he
  rcases he with ⟨rfl,ht,hk⟩
  have ht' : t=t' := Fin.ext ht
  have hk' : k=k' := Fin.ext hk
  subst t'; subst k'; rfl

theorem source_toWots (L : EncLeaf) : WotsExtract.SourceLeaf7 L.toWots := L.2

theorem encLeafOf_self (L : EncLeaf) (h : WotsExtract.SourceLeaf7 L.toWots) :
    encLeafOf L.toWots h=L := toWots_injective (encLeafOf_toWots _ _)

abbrev Rows := EncLeaf → Fin (2^22) → HashOutput
noncomputable def selectionAt (rows : Rows) (L : EncLeaf) (remaining : Nat) : Selection :=
  capSel L (FirstSuccessTable.select
    (decodeAt L (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining)) (rows L))
noncomputable def searchRows (rows : Rows) : Wots.CanonicalRef.Search := fun L remaining =>
  if h : WotsExtract.SourceLeaf7 L then
    (selectionAt rows (encLeafOf L h) remaining).bind fun r =>
      (WCT9.CanonicalPolicy.producerDecodeAt L.lay
        (WCT9.CanonicalPolicy.threshold L.lay.val remaining) r.2).map fun ds =>
          (BitVec.ofNat 32 r.1.val,ds)
  else none
noncomputable def rowsContext (rows : Rows) : Wots.LeafAddr → Option Nat :=
  Wots.CanonicalRef.context (searchRows rows) WCT9.CanonicalPolicy.credit
noncomputable def selectionsOfRows (rows : Rows) : Selections := fun L =>
  (rowsContext rows L.toWots).bind (selectionAt rows L)

#print axioms counterSearch_select
#print axioms encLeafOf_self
end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem searchRows_toWots (rows : Rows) (L : EncLeaf) (remaining : Nat) :
    searchRows rows L.toWots remaining = (selectionAt rows L remaining).bind fun r =>
      (WCT9.CanonicalPolicy.producerDecodeAt L.1.lay
        (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining) r.2).map fun ds =>
          (BitVec.ofNat 32 r.1.val,ds) := by
  simp only [searchRows, dif_pos (source_toWots L), encLeafOf_self]
  rfl

def RowAgreement (answers : Answers) (messages : Wots.LeafAddr → WCT9.LayerMsg)
    (rows : Rows) : Prop := ∀ (L : EncLeaf) (c : Fin (2^22)),
  answers (.inl (.inr (pad64 (WCT9.layerEncodingInput L.1.lay L.1.tree.val L.1.leaf.val
    (messages L.toWots) (BitVec.ofNat 32 c.val))))) = rows L c

theorem searchOf_eq_selectionAt (answers : Answers) (messages : Wots.LeafAddr → WCT9.LayerMsg)
    (rows : Rows) (hrows : RowAgreement answers messages rows) (L : EncLeaf) (remaining : Nat) :
    Wots.CanonicalRef.searchOf answers messages L.toWots remaining =
      (selectionAt rows L remaining).bind fun r =>
        (WCT9.CanonicalPolicy.producerDecodeAt L.1.lay
          (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining) r.2).map fun ds =>
            (BitVec.ofNat 32 r.1.val,ds) := by
  let floor := WCT9.CanonicalPolicy.threshold L.1.lay.val remaining
  change evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.1.lay floor
    L.1.tree.val L.1.leaf.val (messages L.toWots) 0 (WCT9.searchLimit L.1.lay)) = _
  rw [counterSearch_select answers L.1.lay floor L.1.tree.val L.1.leaf.val (messages L.toWots)
    (decodeAt L floor) (fun _ => rfl)]
  have hle : WCT9.searchLimit L.1.lay ≤ 2^22 := WCT9.searchLimit_le L.1.lay
  have hr : (fun i : Fin (WCT9.searchLimit L.1.lay) => answers (.inl (.inr
      (pad64 (WCT9.layerEncodingInput L.1.lay L.1.tree.val L.1.leaf.val (messages L.toWots)
        (BitVec.ofNat 32 (0+i.val))))))) = fun i => rows L (Fin.castLE hle i) := by
    funext i
    rw [Nat.zero_add]
    exact hrows L (Fin.castLE hle i)
  rw [hr]
  simp only [Nat.zero_add]
  unfold selectionAt capSel
  exact select_castLE_bind (decodeAt L floor) hle (rows L)
    (fun k v => (WCT9.CanonicalPolicy.producerDecodeAt L.1.lay floor v).map fun ds =>
      (BitVec.ofNat 32 k,ds))

theorem searchRows_eq (answers : Answers) (messages : Wots.LeafAddr → WCT9.LayerMsg)
    (rows : Rows) (hrows : RowAgreement answers messages rows) (L : Wots.LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) (remaining : Nat) :
    searchRows rows L remaining = Wots.CanonicalRef.searchOf answers messages L remaining := by
  let E := encLeafOf L hL
  have he : E.toWots=L := encLeafOf_toWots L hL
  have h := (searchRows_toWots rows E remaining).trans
    (searchOf_eq_selectionAt answers messages rows hrows E remaining).symm
  simpa only [he] using h

theorem rowsContext_eq (answers : Answers) (messages : Wots.LeafAddr → WCT9.LayerMsg)
    (rows : Rows) (hrows : RowAgreement answers messages rows) (L : Wots.LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    rowsContext rows L = Wots.CanonicalRef.referenceContext answers messages L := by
  exact Wots.CanonicalRef.context_congr_on WCT9.CanonicalPolicy.credit WotsExtract.SourceLeaf7
    (fun _ h hp => Wots.CanonicalRef.source_parent h hp)
    (fun L hL remaining _ => searchRows_eq answers messages rows hrows L hL remaining) hL

noncomputable def decodedSelection (rows : Rows) (L : EncLeaf) : Option (BitVec 32 × List Nat) :=
  (rowsContext rows L.toWots).bind fun remaining =>
    (selectionAt rows L remaining).bind fun r =>
      (WCT9.CanonicalPolicy.producerDecodeAt L.1.lay
        (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining) r.2).map fun ds =>
          (BitVec.ofNat 32 r.1.val,ds)

theorem referenceSearch_eq_rows (answers : Answers) (messages : Wots.LeafAddr → WCT9.LayerMsg)
    (rows : Rows) (hrows : RowAgreement answers messages rows) (L : EncLeaf) :
    Wots.CanonicalRef.referenceSearch answers messages L.toWots = decodedSelection rows L := by
  unfold decodedSelection Wots.CanonicalRef.referenceSearch Wots.CanonicalRef.selected
  rw [rowsContext_eq answers messages rows hrows L.toWots (source_toWots L)]
  apply congrArg (Option.bind (Wots.CanonicalRef.referenceContext answers messages L.toWots))
  funext remaining
  exact searchOf_eq_selectionAt answers messages rows hrows L remaining

#print axioms rowsContext_eq
#print axioms referenceSearch_eq_rows
end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem selectionAt_producer {rows : Rows} {L : EncLeaf} {remaining : Nat}
    {r : Fin (2^22) × Digest} (hsel : selectionAt rows L remaining = some r) :
    ∃ ds, WCT9.CanonicalPolicy.producerDecodeAt L.1.lay
      (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining) r.2=some ds := by
  have hs := (capSel_eq_some.mp hsel).1
  have hd := (FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hs |>.1
  cases he : WCT9.CanonicalPolicy.producerDecodeAt L.1.lay
      (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining)
      (WCT9.encodingAnswer L.1.lay (rows L r.1)) with
  | none => simp only [decodeAt,he,Option.isSome_none,Bool.false_eq_true,if_false] at hd; cases hd
  | some ds =>
      have hv : WCT9.encodingAnswer L.1.lay (rows L r.1)=r.2 := by
        simpa only [decodeAt,he,Option.isSome_some,if_true,Option.some.injEq] using hd
      exact ⟨ds,hv ▸ he⟩

theorem selectionAt_decoder (rows : Rows) (L : EncLeaf) (remaining : Nat) :
    ((selectionAt rows L remaining).bind fun r =>
      (WCT9.CanonicalPolicy.producerDecodeAt L.1.lay
        (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining) r.2).map fun ds =>
          (BitVec.ofNat 32 r.1.val,ds)) =
    ((selectionAt rows L remaining).bind fun r =>
      (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun ds =>
        (BitVec.ofNat 32 r.1.val,ds)) := by
  cases he : selectionAt rows L remaining with
  | none => rfl
  | some r =>
      obtain ⟨ds,hd⟩ := selectionAt_producer he
      simp only [Option.bind_some, hd, (WCT9.CanonicalPolicy.producerDecodeAt_spec hd).1]

theorem decodedSelection_eq (rows : Rows) (L : EncLeaf) :
    decodedSelection rows L = (selectionsOfRows rows L).bind fun r =>
      (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun ds =>
        (BitVec.ofNat 32 r.1.val,ds) := by
  unfold decodedSelection selectionsOfRows
  rw [Option.bind_assoc]
  apply congrArg (Option.bind (rowsContext rows L.toWots))
  funext remaining
  exact selectionAt_decoder rows L remaining

theorem referenceSearch_eq_selections (answers : Answers) (messages : Wots.LeafAddr → WCT9.LayerMsg)
    (rows : Rows) (hrows : RowAgreement answers messages rows) (L : EncLeaf) :
    Wots.CanonicalRef.referenceSearch answers messages L.toWots =
      (selectionsOfRows rows L).bind fun r =>
        (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun ds =>
          (BitVec.ofNat 32 r.1.val,ds) :=
  (referenceSearch_eq_rows answers messages rows hrows L).trans (decodedSelection_eq rows L)

#print axioms referenceSearch_eq_selections
end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_injective)
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.expectedPairRoot
def msgLabel (labels : Labels) (L : EncLeaf) : WCT9.LayerMsg :=
  if h : L.1.lay.val < 3 then
    .pair (treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩ - 1) 0)
      (treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩ - 1) 1)
  else .pair (CanonGraph.Paired.ftsLabel labels (childIndex L) 8 6 0) (CanonGraph.Paired.ftsLabel labels (childIndex L) 8 6 1)
def encKey (labels : Labels) (x : EncLeaf × Fin (2^22)) : EncKey :=
  ((x.1.1.lay, x.1.1.tree, x.1.1.leaf, msgLabel labels x.1), x.2)
theorem encodingQuery_ne_cell (key : EncKey) (secrets : Secrets) (node : Node) (labels : Labels) :
    encQuery key ≠ CanonGraph.Paired.cell secrets node labels := by
  intro heq
  have h1 := hdrBlock_encQuery key
  rw [heq, CanonGraph.Paired.hdrBlock_cell] at h1
  exact row_ne_hdr _ _ _ node (bytesLE_injective h1).symm
noncomputable def encCell (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (x : EncLeaf × Fin (2^22)) : U :=
  ⟨encQuery (encKey labels x), hE (encQuery_mem _)⟩
theorem encCell_val (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) (x : EncLeaf × Fin (2^22)) :
    (encCell U hE labels x).val = pad64 (WCT9.layerEncodingInput x.1.1.lay x.1.1.tree.val x.1.1.leaf.val
      (msgLabel labels x.1) (BitVec.ofNat 32 x.2.val)) := rfl
theorem encCell_injective (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    Function.Injective (encCell U hE labels) := by
  rintro ⟨⟨⟨lay, tree, leaf⟩, hL⟩, c⟩ ⟨⟨⟨lay', tree', leaf'⟩, hL'⟩, c'⟩ heq
  have hv := congrArg Subtype.val heq
  rw [encCell_val, encCell_val, ← BC.pad64_layerEncodingInputP_zero, ← BC.pad64_layerEncodingInputP_zero] at hv
  obtain ⟨e1, e2, e3, e4⟩ := BC.layerEncodingRow_coords hL.routed.1 hL.routed.2 hL'.routed.1 hL'.routed.2 hv
  simp only at e1 e2 e3 e4
  subst e1
  have e2' : tree = tree' := Fin.ext e2
  have e3' : leaf = leaf' := Fin.ext e3
  subst e2' e3'
  have e4' : c = c' := by
    have h1 := congrArg BitVec.toNat e4
    simp only [BitVec.toNat_ofNat] at h1
    exact Fin.ext (by rw [Nat.mod_eq_of_lt (lt_trans c.isLt (by norm_num)),
      Nat.mod_eq_of_lt (lt_trans c'.isLt (by norm_num))] at h1; exact h1)
  subst e4'
  rfl
theorem forestCommitment_eq (answers : Answers) (labels : Labels)
    (h : CanonGraph.Paired.Agrees answers labels) (index : Fin (2^31)) :
    Wots.CanonicalRef.forestCommitment answers index.val =
      (CanonGraph.Paired.ftsLabel labels index 8 6 0,
       CanonGraph.Paired.ftsLabel labels index 8 6 1) := by
  change ((Extract.Paired.nodes answers index.val 8).getD (2^(7-6)+0) 0,
    (Extract.Paired.nodes answers index.val 8).getD (2^(7-6)+1) 0) = _
  apply Prod.ext
  · exact CanonGraph.Paired.actual_nodes_label answers labels h index 8 6 0 (by decide) (by decide)
  · exact CanonGraph.Paired.actual_nodes_label answers labels h index 8 6 1 (by decide) (by decide)

theorem sourceMessages_eq {answers : Answers} {labels : Labels}
    (h : CanonGraph.Paired.Agrees answers labels) (L : EncLeaf) :
    Wots.CanonicalRef.sourceMessages answers L.toWots=msgLabel labels L := by
  unfold Wots.CanonicalRef.sourceMessages msgLabel EncLeaf.toWots
  dsimp only
  split_ifs with hlay
  · rw [show L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val = (childIndex L).val from rfl,
      CanonGraph.Paired.honestPair_eq h ⟨L.1.lay.val+1,by omega⟩ (childIndex L) (childIndex_treeBits L hlay)]
  · rw [show L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val = (childIndex L).val from rfl,
      Nat.mod_eq_of_lt (childIndex L).isLt, forestCommitment_eq answers labels h (childIndex L)]

theorem answers_encCell (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (hE : encInputs ⊆ U) (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) =
      CanonGraph.Paired.programmed U hU (CanonGraph.secretsOf answers) labels residual x)
    (x : EncLeaf × Fin (2^22)) :
    answers (.inl (.inr (encCell U hE labels x).val)) = residual (encCell U hE labels x) := by
  rw [hpub]
  apply CanonGraph.Paired.programmed_other
  intro node heq
  exact encodingQuery_ne_cell _ _ node labels heq

theorem rowAgreement_programmed (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (hE : encInputs ⊆ U) (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) =
      CanonGraph.Paired.programmed U hU (CanonGraph.secretsOf answers) labels residual x) :
    RowAgreement answers (Wots.CanonicalRef.sourceMessages answers)
      (fun L c => residual (encCell U hE labels (L,c))) := by
  intro L c
  rw [sourceMessages_eq (CanonGraph.Paired.agrees_of_programmed U hU answers labels residual hpub) L]
  exact answers_encCell U hU hE answers labels residual hpub (L,c)

#print axioms sourceMessages_eq
#print axioms rowAgreement_programmed
end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem msgLabel_complete (answers : Answers) (labels : Labels) (L : EncLeaf) :
    msgLabel (CanonGraph.Paired.Filtered.completeLabels answers labels) L = msgLabel labels L := by
  unfold msgLabel
  split_ifs
  · rw [CanonGraph.Paired.Filtered.treeLabel_complete,CanonGraph.Paired.Filtered.treeLabel_complete]
  · rw [CanonGraph.Paired.Filtered.ftsLabel_complete _ _ _ _ _ _ (by decide),
      CanonGraph.Paired.Filtered.ftsLabel_complete _ _ _ _ _ _ (by decide)]

theorem sourceMessages_eq_filtered {answers : Answers} {labels : Labels}
    (h : CanonGraph.Paired.Filtered.Agrees answers labels) (L : EncLeaf) :
    Wots.CanonicalRef.sourceMessages answers L.toWots=msgLabel labels L :=
  (sourceMessages_eq (CanonGraph.Paired.Filtered.completeLabels_agrees h) L).trans
    (msgLabel_complete answers labels L)

theorem answers_encCell_filtered (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (hE : encInputs ⊆ U) (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) =
      CanonGraph.Paired.Filtered.programmed U hU (CanonGraph.secretsOf answers) labels residual x)
    (x : EncLeaf × Fin (2^22)) :
    answers (.inl (.inr (encCell U hE labels x).val)) = residual (encCell U hE labels x) := by
  rw [hpub]
  apply CanonGraph.Paired.Filtered.programmed_other
  intro node _ heq
  exact encodingQuery_ne_cell _ _ node labels heq

theorem rowAgreement_filtered (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (hE : encInputs ⊆ U) (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) =
      CanonGraph.Paired.Filtered.programmed U hU (CanonGraph.secretsOf answers) labels residual x) :
    RowAgreement answers (Wots.CanonicalRef.sourceMessages answers)
      (fun L c => residual (encCell U hE labels (L,c))) := by
  intro L c
  rw [sourceMessages_eq_filtered (CanonGraph.Paired.Filtered.agrees_of_programmed U hU answers labels residual hpub) L]
  exact answers_encCell_filtered U hU hE answers labels residual hpub (L,c)

theorem referenceSearch_eq_filtered (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (hE : encInputs ⊆ U) (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) =
      CanonGraph.Paired.Filtered.programmed U hU (CanonGraph.secretsOf answers) labels residual x)
    (L : EncLeaf) :
    Wots.CanonicalRef.referenceSearch answers (Wots.CanonicalRef.sourceMessages answers) L.toWots =
      (selectionsOfRows (fun L c => residual (encCell U hE labels (L,c))) L).bind fun r =>
        (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun ds =>
          (BitVec.ofNat 32 r.1.val,ds) :=
  referenceSearch_eq_selections answers _ _ (rowAgreement_filtered U hU hE answers labels residual hpub) L

#print axioms referenceSearch_eq_filtered
end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
