import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactMonitor
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingObserved
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingSign
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingTrace
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsStructuralFinal
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingMatch
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportCount
import SigGolfCandidate.T3.Secc.WotsClasses
import SigGolfCandidate.T3.Secc.LargeCouplingQuery

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingQuery : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
/-- Local copy of `Wots.SmallA.encRow_ne_digest` (WotsClasses), so the large route does not import the small
route's `WotsTwoEdge`. -/
theorem encRow_ne_digest' (L : Wots.LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : Wots.RowPad) (rho : Digest)
    (m' : Message) (c' : BitVec 32) : Wots.encRow L m c pad ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h2 : ClaudeWCT.W9.T3M.Extract.hdrBlock (pad64 (digestInput rho m' c')) =
      bytesLE 16 (digestHeader c') :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest rho m' c'
  rw [h2, show Wots.encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  exact (digestHeader_ne_rowTweak _ _ _ _).symm (bytesLE_injective hb)
noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  joinLabels (fun N => vals (.inl N)) a.high
def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr
structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : Agrees T (routerLabels vals a)
  secrets : seedView (secretsOf T) = fun s => vals (.inr s)
  residual : ∀ (X : HashInput) (hX : X ∈ U), (∀ N : CanonGraph.Node, X ≠ cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩)
  prefixRow : ∀ (L : EncLeaf) (ctr : BitVec 32), PrefixRow a L ctr →
    T (.inl (.inr (Wots.encRow L.toWots (msgVals vals L) ctr 0))) = prefixValue a L ctr
  search : ∀ L : EncLeaf, Wots.referenceSearch T L.toWots =
    (a.sel L).bind fun r => (decode L.1.lay r.2).map fun d => (BitVec.ofNat 32 r.1.val, d)
  priv : ∀ c : Coordinate, (∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) → (∀ m : Message, c ≠ .inr (.inl m)) →
    T (.inr c) = a.priv c
  outside : ∀ X, X ∉ U → T (.inl (.inr X)) = (0 : HashOutput)
  nonce : ∀ m : Message, (T (.inr (.inr (.inl m)))).extractLsb' 0 128 = nv m
theorem rowPresent_parsed {X : HashInput} {N : CanonGraph.Node} (hN : Extract.posOf X = some N.toPos) :
    rowPresent X = CanonGraph.presentEquiv N := by
  have hp : Parsed X := ⟨N, hN⟩
  unfold rowPresent
  rw [dif_pos hp]
  have hc : Extract.posOf X = some (Classical.choose hp).toPos := Classical.choose_spec hp
  have he : Classical.choose hp = N := CanonGraph.toPos_injective (Option.some.inj (hc.symm.trans hN))
  rw [he]
theorem proj_rowPresent {X : HashInput} {N : CanonGraph.Node} (hN : Extract.posOf X = some N.toPos)
    (y : HashOutput) : N.toPos.proj (rowPresent X y) = y.extractLsb' 0 128 := by
  rw [rowPresent_parsed hN]; exact CanonGraph.proj_presentEquiv N y
theorem rowPresent_unparsed {X : HashInput} (hp : ¬Parsed X) (y : HashOutput) : rowPresent X y = y := by
  unfold rowPresent; rw [dif_neg hp]; rfl
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.residual_unparsed (h : Coherent U T vals nv τ a) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X)
    (hcell : ∀ N : CanonGraph.Node, X ≠ cell (secretsOf T) N (routerLabels vals a)) (hpre : ¬HonestPrefix vals a X) :
    T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
  (h.residual X hX hcell hpre).trans (rowPresent_unparsed hnp _)
theorem Coherent.honestValue (h : Coherent U T vals nv τ a) : LargeResidual.honestValue T = vals := by
  rw [honestValue_eq h.agrees]
  funext c
  cases c with
  | inl N => exact joinLabels_val _ _ N
  | inr s => exact congrFun h.secrets s
theorem Coherent.honestInput (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    Extract.honestInput T N.toPos = cellValues N vals := by
  rw [honestInput_eq h.agrees N, cell_eq_cellValues]
  congr 1
  funext c
  cases c with
  | inl M => exact joinLabels_val _ _ M
  | inr s => exact congrFun h.secrets s
theorem Coherent.cell (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    cell (secretsOf T) N (routerLabels vals a) = cellValues N vals := by
  rw [← honestInput_eq h.agrees N, h.honestInput N]
theorem Coherent.honest_answer (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    T (.inl (.inr (cellValues N vals))) = routerLabels vals a N := by
  rw [← h.honestInput N]
  exact CanonGraph.honest_answer h.agrees N
theorem Coherent.leafMsg (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.leafMsg T L.toWots = msgVals vals L := by
  rw [leafMsg_eq h.agrees L]
  unfold msgLabel msgVals
  by_cases hl : L.1.lay.val < 3
  · rw [dif_pos hl, dif_pos hl]
    congr 1
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans (joinLabels_low rfl)
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans (joinLabels_low rfl)
  · rw [dif_neg hl, dif_neg hl]
    congr 1
    · exact (ftsLabel_top _ _ _ 0).trans ((proj_top _ _ _ _).symm.trans (joinLabels_val _ _ _))
    · exact (ftsLabel_top _ _ _ 1).trans ((proj_top _ _ _ _).symm.trans (joinLabels_val _ _ _))
end Coherent
theorem encodingRow_parsed_none (L : Wots.LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : Wots.RowPad) :
    Extract.posOf (Wots.encRow L m c pad) = none :=
  Wots.Structural.posOf_layerEncodingP _ _ _ _ _ _ _
theorem digestRow_parsed_none {X : HashInput} (h : IsDigestRow X) : Extract.posOf X = none := by
  obtain ⟨rho, m, c, rfl⟩ := h
  exact Wots.Structural.posOf_digest _ _ _
theorem not_parsed_of_digest {X : HashInput} (h : IsDigestRow X) : ¬Parsed X := by
  rintro ⟨N, hN⟩
  rw [digestRow_parsed_none h] at hN
  cases hN
theorem not_parsed_of_encRow {X : HashInput} (h : EncRow X) : ¬Parsed X := by
  rintro ⟨N, hN⟩
  obtain ⟨L, m, c, pad, -, rfl⟩ := h
  rw [encodingRow_parsed_none] at hN
  cases hN
theorem encRow_encLeaf {L L' : EncLeaf} {m m' : WCT9.LayerMsg} {c c' : BitVec 32} {pad pad' : Wots.RowPad}
    (h : Wots.encRow L.toWots m c pad = Wots.encRow L'.toWots m' c' pad') : L = L' ∧ c = c' := by
  obtain ⟨⟨lay, tree, leaf⟩, hs⟩ := L
  obtain ⟨⟨lay', tree', leaf'⟩, hs'⟩ := L'
  obtain ⟨h1, h2, h3, h4⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_coords hs.routed.1 hs.routed.2
    hs'.routed.1 hs'.routed.2 h
  refine ⟨?_, h4⟩
  subst h1
  have e2 : tree = tree' := Fin.ext h2
  have e3 : leaf = leaf' := Fin.ext h3
  subst e2 e3
  rfl
theorem msgFits_msgVals (v : Coord → Digest) (L : EncLeaf) : Extract.msgFits L.1.lay (msgVals v L) := by
  unfold msgVals
  split_ifs <;> trivial
theorem msgVals_congr (v w : Coord → Digest) (L : EncLeaf) (h : ∀ cs ∈ msgSlots L, v cs.1 = w cs.1) :
    msgVals v L = msgVals w L := by
  unfold msgVals
  unfold msgSlots at h
  split_ifs with hl
  · rw [dif_pos hl] at h
    rw [h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)]
  · rw [dif_neg hl] at h
    rw [h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)]
theorem slotValue_three (A B C E : HashInput) (hA : A.length = 16) (hB : B.length = 16) (hC : C.length = 16)
    (x : Digest) : slotValue (A ++ (B ++ (C ++ (bytesLE 16 x ++ E)))) 3 = x := by
  rw [show (3 : Nat) = 2 + 1 from rfl, SigGolfCandidate.T3.Security.LargeResidual.slotValue_shift _ _ _ hA,
    show (2 : Nat) = 1 + 1 from rfl, SigGolfCandidate.T3.Security.LargeResidual.slotValue_shift _ _ _ hB,
    show (1 : Nat) = 0 + 1 from rfl, SigGolfCandidate.T3.Security.LargeResidual.slotValue_shift _ _ _ hC]
  exact SigGolfCandidate.T3.Security.LargeResidual.slotValue_bytes_cons x E
theorem slot_msgVals (L : EncLeaf) (v : Coord → Digest) (c : BitVec 32) (pad : Wots.RowPad) :
    ∀ cs ∈ msgSlots L, slotValue (Wots.encRow L.toWots (msgVals v L) c pad) cs.2 = v cs.1 := by
  intro cs hcs
  have hl16 : ∀ x : Digest, (bytesLE 16 x).length = 16 := fun x => bytesLE_length 16 x
  unfold msgSlots at hcs
  unfold msgVals Wots.encRow
  split_ifs at hcs ⊢ with hl
  · rw [ClaudeWCT.W9.T3M.BC.layerEncodingInputP_pair, ClaudeWCT.W9.T3M.BC.pad64_pairEncodingInputP]
    unfold WCT9.pairEncodingInputP
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcs
    rcases hcs with rfl | rfl
    · simp only [List.append_assoc]
      exact SigGolfCandidate.T3.Security.LargeResidual.slotValue_bytes_cons _ _
    · have e : ∀ (A B C D E : HashInput), A ++ B ++ C ++ D ++ E = A ++ (B ++ ((C ++ D) ++ (E ++ []))) := by
        intro A B C D E; simp only [List.append_assoc, List.append_nil]
      rw [e]
      exact slotValue_three _ _ _ [] (hl16 _) (hl16 _) (by simp only [List.length_append, bytesLE_length]) _
  · rw [ClaudeWCT.W9.T3M.BC.layerEncodingInputP_pair, ClaudeWCT.W9.T3M.BC.pad64_pairEncodingInputP]
    unfold WCT9.pairEncodingInputP
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcs
    rcases hcs with rfl | rfl
    · simp only [List.append_assoc]
      exact SigGolfCandidate.T3.Security.LargeResidual.slotValue_bytes_cons _ _
    · have e : ∀ (A B C D E : HashInput), A ++ B ++ C ++ D ++ E = A ++ (B ++ ((C ++ D) ++ (E ++ []))) := by
        intro A B C D E; simp only [List.append_assoc, List.append_nil]
      rw [e]
      exact slotValue_three _ _ _ [] (hl16 _) (hl16 _) (by simp only [List.length_append, bytesLE_length]) _
theorem firstUnknownMsg_some {K : Coord → Prop} {L : EncLeaf} {cs : Coord × Nat}
    (h : firstUnknownMsg K L = some cs) : cs ∈ msgSlots L ∧ ¬K cs.1 := by
  unfold firstUnknownMsg at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm, hp⟩
theorem firstUnknownMsg_none {K : Coord → Prop} {L : EncLeaf} (h : firstUnknownMsg K L = none) :
    ∀ cs ∈ msgSlots L, K cs.1 := by
  unfold firstUnknownMsg at h
  intro cs hcs
  have := List.find?_eq_none.mp h cs hcs
  simpa using this
theorem childSlots_ne (N : CanonGraph.Node) : ∀ cs ∈ childSlots N, cs.1 ≠ .inl N := by
  intro cs hcs
  cases N with
  | chain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      unfold chainChild
      split_ifs with h0
      · exact Sum.inl_ne_inr.symm
      · intro heq
        have h1 := congrArg (fun c : Coord => match c with | .inl (.chain x) => x.2.val | _ => 0) heq
        simp only [ChainGraph.predecessor] at h1
        omega
  | leaf L =>
      simp only [childSlots, List.mem_map] at hcs
      obtain ⟨i, -, rfl⟩ := hcs
      simp
  | node n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      · unfold treeChild at hc
        split_ifs at hc with hl
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨L, -, rfl⟩ := hc
          simp
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨m, hm, rfl⟩ := hc
          intro heq
          have hlev := treeNodeAt_level hm
          have hmn : m = n := by
            simp only [Sum.inl.injEq, CanonGraph.Node.node.injEq] at heq
            exact heq
          subst hmn
          omega
  | wctChain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      unfold wctItem
      split_ifs with h0
      · exact Sum.inl_ne_inr.symm
      · intro heq
        have h1 := congrArg (fun c : Coord => match c with | .inl (.wctChain x) => x.2.val | _ => 0) heq
        simp only at h1
        have := p.2.isLt
        omega
  | wctLeaf L =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with hcs | hcs
      · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hcs
        simp [wctItem]
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        unfold prevTop at hc
        split_ifs at hc
        cases hc
        simp
  | wctNode n =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with (hcs | hcs) | hcs
      rotate_left 2
      · split_ifs at hcs with hl5
        · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
          obtain ⟨c, hc, rfl⟩ := hcs
          unfold prevTop at hc
          split_ifs at hc with h0
          cases hc
          intro heq
          simp only [Sum.inl.injEq, CanonGraph.Node.wctNode.injEq] at heq
          have := congrArg (fun m : WctNodePos => m.1.coord.val) heq
          simp only [ftsTopNode] at this
          omega
        · simp at hcs
      all_goals simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
      all_goals obtain ⟨c, hc, rfl⟩ := hcs
      all_goals
      · unfold ftsChild at hc
        split_ifs at hc with hl
        · obtain ⟨⟩ := hc
          simp
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨m, hm, rfl⟩ := hc
          intro heq
          have hlev := ftsNodeAt_level hm
          have hmn : m = n := by
            simp only [Sum.inl.injEq, CanonGraph.Node.wctNode.injEq] at heq
            exact heq
          subst hmn
          omega
  | forest index =>
      unfold childSlots at hcs
      rw [List.mem_flatMap] at hcs
      obtain ⟨c, -, hc⟩ := hcs
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> simp
theorem firstUnknown_some {K : Coord → Prop} {N : CanonGraph.Node} {cs : Coord × Nat}
    (h : firstUnknown K N = some cs) : cs ∈ childSlots N ∧ ¬K cs.1 := by
  unfold firstUnknown at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm, hp⟩
theorem firstUnknown_none {K : Coord → Prop} {N : CanonGraph.Node} (h : firstUnknown K N = none) :
    ∀ cs ∈ childSlots N, K cs.1 := by
  unfold firstUnknown at h
  intro cs hcs
  have := List.find?_eq_none.mp h cs hcs
  simpa using this
theorem contactTest_parsed {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput} {N : CanonGraph.Node}
    (hN : Extract.posOf X = some N.toPos) :
    ContactTest A K X y ↔
      (∃ cs, firstUnknown K N = some cs ∧ slotValue X cs.2 = LargeResidual.honestValue A cs.1) ∨
        (X ≠ Extract.honestInput A N.toPos ∧ N.toPos.proj y = LargeResidual.honestValue A (.inl N)) := by
  constructor
  · rintro (⟨N', hN', h⟩ | ⟨L, m, c, pad, -, hX, -⟩)
    · rw [hN] at hN'
      have := toPos_injective (Option.some.inj hN')
      subst this
      exact h
    · rw [hX, encodingRow_parsed_none] at hN
      cases hN
  · intro h
    exact Or.inl ⟨N, hN, h⟩
theorem contactTest_enc {A : Answers} {K : Coord → Prop} {y : HashOutput} {L : EncLeaf} {m : WCT9.LayerMsg}
    {c : BitVec 32} {pad : Wots.RowPad} (hfit : Extract.msgFits L.1.lay m) :
    ContactTest A K (Wots.encRow L.toWots m c pad) y ↔
      (∃ cs, firstUnknownMsg K L = some cs ∧
          slotValue (Wots.encRow L.toWots m c pad) cs.2 = LargeResidual.honestValue A cs.1) ∨
        (Wots.referenceInput A L.toWots ≠ some (Wots.encRow L.toWots m c pad) ∧
          decode L.1.lay (WCT9.encodingAnswer L.1.lay y) = some (Wots.referenceDigits A L.toWots)) := by
  constructor
  · rintro (⟨N', hN', -⟩ | ⟨L', m', c', pad', -, hX, h⟩)
    · rw [encodingRow_parsed_none] at hN'
      cases hN'
    · obtain ⟨rfl, -⟩ := encRow_encLeaf hX
      exact h
  · intro h
    exact Or.inr ⟨L, m, c, pad, hfit, rfl, h⟩
theorem contactTest_other {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput}
    (hp : ¬Parsed X) (he : ¬EncRow X) : ¬ContactTest A K X y := by
  rintro (⟨N, hN, -⟩ | ⟨L, m, c, pad, hfit, hX, -⟩)
  · exact hp ⟨N, hN⟩
  · exact he ⟨L, m, c, pad, hfit, hX⟩
theorem sel_valid (a : AuxData) (L : EncLeaf) (r : Fin (2 ^ 22) × Digest) (hr : a.sel L = some r) :
    ∃ w, decode L.1.lay r.2 = some w := by
  have h := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp (capSel_eq_some.mp hr).1
  obtain ⟨-, hs⟩ := (decodeAt_eq_some L _ r.2).mp h.1
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨w, WCT9.producerDecode_decode hw⟩
section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.referenceDigits T L.toWots = ((a.sel L).bind fun r => decode L.1.lay r.2).getD (Wots.dummyDigits L.1.lay) := by
  unfold Wots.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases decode L.1.lay r.2 <;> rfl
theorem Coherent.referenceInput (h : Coherent U T vals nv τ a) (L : EncLeaf) (X : HashInput)
    (hX : Wots.referenceInput T L.toWots = some X) :
    ∃ r, a.sel L = some r ∧ X = Wots.encRow L.toWots (msgVals vals L) (BitVec.ofNat 32 r.1.val) 0 := by
  unfold Wots.referenceInput at hX
  rw [h.search, h.leafMsg] at hX
  cases hs : a.sel L with
  | none => rw [hs] at hX; cases hX
  | some r =>
      rw [hs] at hX
      simp only [Option.bind_some, Option.map_map] at hX
      cases hd : decode L.1.lay r.2 with
      | none => rw [hd] at hX; cases hX
      | some w =>
          rw [hd] at hX
          exact ⟨r, rfl, (Option.some.inj hX).symm⟩
theorem Coherent.decode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (d : Digest) :
    decode L.1.lay d = some (Wots.referenceDigits T L.toWots) ↔ d = refDigest a L := by
  rw [h.referenceDigits L]
  unfold refDigest
  cases hs : a.sel L with
  | none =>
      simp only [Option.bind_none, Option.getD_none]
      constructor
      · intro hd
        exact decode_some_injective hd (dummyDigest_decode' L.1.lay)
      · rintro rfl
        exact dummyDigest_decode' L.1.lay
  | some r =>
      obtain ⟨w, hw⟩ := sel_valid a L r hs
      simp only [Option.bind_some, hw, Option.getD_some]
      constructor
      · intro hd
        exact decode_some_injective hd hw
      · rintro rfl
        exact hw
theorem Coherent.prefix_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (ctr : BitVec 32) (hp : PrefixRow a L ctr)
    (hd : decode L.1.lay (WCT9.encodingAnswer L.1.lay (prefixValue a L ctr)) = some (Wots.referenceDigits T L.toWots)) :
    Wots.referenceInput T L.toWots = some (Wots.encRow L.toWots (msgVals vals L) ctr 0) := by
  obtain ⟨hcap, hle⟩ := hp
  have hlt : ctr.toNat < 2 ^ 22 := lt_of_lt_of_le hcap (WCT9.searchLimit_le L.1.lay)
  have hpv : prefixValue a L ctr = a.rows L ⟨ctr.toNat, hlt⟩ := by unfold prefixValue; rw [dif_pos hlt]
  rw [hpv] at hd
  have hd' : WCT9.producerDecode L.1.lay (WCT9.encodingAnswer L.1.lay (a.rows L ⟨ctr.toNat, hlt⟩)) =
      some (Wots.referenceDigits T L.toWots) := WotsExtract.producerDecode_of_reference T L.toWots hd
  have hrej : ∀ c : Fin (2 ^ 22), ∀ r', SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) (a.rows L) =
      some r' → c < r'.1 → WCT9.producerDecode L.1.lay (WCT9.encodingAnswer L.1.lay (a.rows L c)) = none := by
    intro c r' hr' hc
    have hn := ((SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r'.1 r'.2).mp hr').2 c hc
    exact (decodeAt_eq_none L _).mp hn
  cases hs : a.sel L with
  | none =>
      cases hraw : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) (a.rows L) with
      | none =>
          have hn := (SphincsSecurity.Concrete.FirstSuccessTable.select_none_iff _ _).mp hraw ⟨ctr.toNat, hlt⟩
          rw [decodeAt_eq_none] at hn
          rw [hn] at hd'
          cases hd'
      | some r' =>
          have hge : WCT9.searchLimit L.1.lay ≤ r'.1.val := by
            by_contra hlt'
            have hsome : a.sel L = some r' := by
              unfold AuxData.sel
              rw [hraw]
              exact capSel_eq_some.mpr ⟨rfl, by omega⟩
            rw [hs] at hsome
            cases hsome
          rw [hrej ⟨ctr.toNat, hlt⟩ r' hraw (by rw [Fin.lt_def]; dsimp only; omega)] at hd'
          cases hd'
  | some r =>
      have hraw := (capSel_eq_some.mp hs).1
      have hle' := hle r hs
      rcases Nat.lt_or_ge ctr.toNat r.1.val with hlt' | hge
      · rw [hrej ⟨ctr.toNat, hlt⟩ r hraw (by rw [Fin.lt_def]; exact hlt')] at hd'
        cases hd'
      · have heq : ctr.toNat = r.1.val := by omega
        unfold Wots.referenceInput
        rw [h.search, h.leafMsg, hs]
        obtain ⟨w, hw⟩ := sel_valid a L r hs
        simp only [Option.bind_some, hw, Option.map_some]
        congr 2
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, ← heq]
        exact Nat.mod_eq_of_lt (by omega)
end Reference
structure Rel (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) : Prop where
  disclosed : mon.disclosed = st.disclosed
  seen : mon.seen = st.seen
  calls : mon.calls = st.calls
  wcalls : ws.counters.calls = st.calls
  digests : mon.digests = ws.counters.mass
  contact : mon.contact = false
  probes : ws.counters.probes ≤ ws.counters.calls
  budget : st.calls ≤ q
  mem : ∀ c, Sum.elim vals nv c ∈ ws.candidates c
  hidden : ∀ c, ¬st.known c → 2 ^ 128 - ws.counters.probes ≤ (ws.candidates (.inl c)).card
  rowsEq : ∀ row v, ws.rows row = some v → v = τ row
  rowsSeen : ∀ row v, ws.rows row = some v → row.val ∈ st.seen ∨ IsDigestRow row.val
  seenCells : ∀ X ∈ st.seen, X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1
  seenEnc : ∀ X ∈ st.seen, X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32),
    X = Wots.encRow L.toWots (msgVals vals L) ctr 0 → ∀ cs ∈ msgSlots L, st.known cs.1
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
theorem Rel.known (h : Rel U T vals nv τ a q mon st ws) : mon.known = st.known := by
  unfold Monitor.known RouterState.known
  rw [h.disclosed]
theorem Rel.query (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (y : HashOutput) :
    mon.query U T q X y =
      if X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X y then
        ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests, true⟩
      else ⟨mon.disclosed, X :: mon.seen, mon.calls + 1,
        mon.digests + (if X ∈ U ∧ IsDigestRow X then 1 else 0), false⟩ := by
  have hc : mon.calls + 1 ≤ q := by rw [h.calls]; omega
  unfold Monitor.query
  rw [if_neg (by rw [h.contact]; decide), h.known, h.seen]
  by_cases ht : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X y
  · rw [if_pos ⟨ht.1, ht.2.1, hc, ht.2.2⟩, if_pos ht]
  · rw [if_neg (fun h' => ht ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg ht]
    by_cases hd : X ∈ U ∧ IsDigestRow X
    · rw [if_pos ⟨hd.1, hd.2, hc⟩, if_pos hd]
    · rw [if_neg (fun h' => hd ⟨h'.1, h'.2.1⟩), if_neg hd]
theorem Rel.two_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (c : Coord)
    (hc : ¬st.known c) : 2 ≤ (ws.candidates (.inl c)).card := by
  have h1 := h.hidden c hc
  have h2 := h.probes
  have h3 := h.wcalls
  omega
theorem Rel.next (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (ws' : LargeResidual.State WCoord (Cell U)) (δ : Nat)
    (hcalls : ws'.counters.calls = st.calls + 1) (hmass : ws'.counters.mass = ws.counters.mass + δ)
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬st.known c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1)
    (st' : RouterState) (hd : st'.disclosed = st.disclosed) (hs : st'.seen = X :: st.seen)
    (hc : st'.calls = st.calls + 1) :
    Rel U T vals nv τ a q ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests + δ, false⟩ st' ws' := by
  have hk : st'.known = st.known := by unfold RouterState.known; rw [hd]
  refine ⟨by rw [hd]; exact h.disclosed, by rw [hs, h.seen], by rw [hc, h.calls], by rw [hcalls, hc], ?_, rfl,
    hprobes, (show st'.calls ≤ q by omega), hmem, ?_, hrowsEq, ?_, ?_, ?_⟩
  · simp only [hmass, h.digests]
  · rw [hk]; exact hhidden
  · intro row v hv
    rw [hs]
    rcases hrowsSeen row v hv with h1 | h1 | h1
    · exact Or.inl (by rw [h1]; exact List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · exact Or.inr h1
  · intro Y hY hYU N hN cs hcs
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hcell hYU N hN cs hcs
    · exact h.seenCells Y hY hYU N hN cs hcs
  · intro Y hY hYU L ctr hL
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact henc hYU L ctr hL
    · exact h.seenEnc Y hY hYU L ctr hL
end Relation
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_of_not (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput)
    (h : ¬(X ∈ U ∧ IsDigestRow X)) : st.next U X y = st.after X := by
  unfold RouterState.next
  rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
def QueryOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U))
    (X : HashInput) (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))) : Prop :=
  ∃ ws' : LargeResidual.State WCoord (Cell U),
    ((mon.query U T q X (T (.inl (.inr X)))).contact = true ∧ out = pure (none, ws') ∧
        ws'.counters.mass = mon.digests ∧ ws'.counters.calls ≤ q) ∨
      ((mon.query U T q X (T (.inl (.inr X)))).contact = false ∧
        out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws') ∧
        Rel U T vals nv τ a q (mon.query U T q X (T (.inl (.inr X)))) (st.next U X (T (.inl (.inr X)))) ws')
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem observed_map {β γ : Type} (f : β → γ) (c : OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (f <$> c) s = (fun r => (r.1.map f, r.2)) <$> observedRun aux q (Sum.elim vals nv) τ c s :=
  runWith_map _ f c s
theorem observed_testReq (st' : RouterState) (X : HashInput) (hX : X ∈ U) (test : Probe WCoord)
    (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effF ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (τ ⟨X, hX⟩, st'), probeState ws ⟨X, hX⟩ (test.effF ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (τ ⟨X, hX⟩, st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
theorem observed_testReqP (g : HashOutput → HashOutput) (st' : RouterState) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (g y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effF ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (g (τ ⟨X, hX⟩), st'), probeState ws ⟨X, hX⟩ (test.effF ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (g (τ ⟨X, hX⟩), st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem outcome_stop (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X))))
    (hout : out = pure (none, stoppedState ws)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨stoppedState ws, Or.inl ⟨?_, hout, ?_, ?_⟩⟩
  · rw [hrel.query hlt, if_pos hc]
  · exact hrel.digests.symm
  · show ws.counters.calls + 1 ≤ q
    rw [hrel.wcalls]
    omega
theorem outcome_continue (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (ws' : LargeResidual.State WCoord (Cell U))
    (hout : out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws'))
    (hcalls : ws'.counters.calls = st.calls + 1)
    (hmass : ws'.counters.mass = ws.counters.mass + (if X ∈ U ∧ IsDigestRow X then 1 else 0))
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬st.known c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨ws', Or.inr ⟨?_, hout, ?_⟩⟩
  · rw [hrel.query hlt, if_neg hc]
  · rw [hrel.query hlt, if_neg hc]
    refine hrel.next hlt X ws' _ hcalls hmass hprobes hmem hhidden hrowsEq hrowsSeen hcell henc _ ?_ ?_ ?_ <;>
    · unfold RouterState.next
      split_ifs <;> rfl
theorem Rel.fresh (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) (hd : ¬IsDigestRow X)
    (hs : X ∉ st.seen) : ws.rows ⟨X, hX⟩ = none := by
  cases hr : ws.rows ⟨X, hX⟩ with
  | none => rfl
  | some v =>
      rcases hrel.rowsSeen _ v hr with h | h
      · exact absurd h hs
      · exact absurd h hd
theorem Coherent.not_cell_parsed (hcoh : Coherent U T vals nv τ a) {X : HashInput} {N : CanonGraph.Node}
    (hN : Extract.posOf X = some N.toPos) (hne : X ≠ cellValues N vals) :
    ∀ N' : CanonGraph.Node, X ≠ cellValues N' vals := by
  intro N' heq
  have hp : Extract.posOf X = some N'.toPos := by
    rw [heq, ← hcoh.cell N']
    exact posOf_cell _ _ _
  rw [hN] at hp
  have := toPos_injective (Option.some.inj hp)
  subst this
  exact hne heq
theorem not_cell_unparsed (hcoh : Coherent U T vals nv τ a) {X : HashInput} (hp : ¬Parsed X) :
    ∀ N' : CanonGraph.Node, X ≠ cellValues N' vals := by
  intro N' heq
  apply hp
  refine ⟨N', ?_⟩
  rw [heq, ← hcoh.cell N']
  exact posOf_cell _ _ _
theorem not_prefix_parsed {X : HashInput} (hp : Parsed X) : ¬HonestPrefix vals a X := by
  rintro ⟨L, ctr, rfl, -⟩
  exact not_parsed_of_encRow ⟨L, _, ctr, 0, msgFits_msgVals vals L, rfl⟩ hp
theorem not_prefix_enc {X : HashInput} (he : ¬EncRow X) : ¬HonestPrefix vals a X := by
  rintro ⟨L, ctr, rfl, -⟩
  exact he ⟨L, _, ctr, 0, msgFits_msgVals vals L, rfl⟩
theorem not_enc_parsed {X : HashInput} (hp : Parsed X) (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32)
    (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m) : X ≠ Wots.encRow L.toWots m ctr pad := by
  rintro rfl
  exact not_parsed_of_encRow ⟨L, m, ctr, pad, hfit, rfl⟩ hp
theorem case_outside (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∉ U) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (tickReq U .call >>= fun _ =>
      pure ((0 : HashOutput), st.after X)) ws) := by
  rw [observed_tickReq, observed_pure]
  apply outcome_continue hrel hlt X _ (fun h => hX h.2.1) (tickState q ws .call)
  · rw [hcoh.outside X hX, RouterState.next_of_not U st X _ (fun h' => hX h'.1)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hX h.1), Nat.add_zero]
  · show ws.counters.probes ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact hrel.rowsEq
  · intro row v hv; exact Or.inr (hrel.rowsSeen row v hv)
  · intro h; exact absurd h hX
  · intro h; exact absurd h hX
theorem rows_update_eq (hrel : Rel U T vals nv τ a q mon st ws) (row0 : Cell U) :
    ∀ row v, Function.update ws.rows row0 (some (τ row0)) row = some v → v = τ row := by
  intro row v hv
  by_cases hr : row = row0
  · subst hr
    rw [Function.update_self] at hv
    exact (Option.some.inj hv).symm
  · rw [Function.update_of_ne hr] at hv
    exact hrel.rowsEq row v hv
theorem rows_update_seen (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) :
    ∀ row v, Function.update ws.rows ⟨X, hX⟩ (some (τ ⟨X, hX⟩)) row = some v →
      row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val := by
  intro row v hv
  by_cases hr : row = ⟨X, hX⟩
  · exact Or.inl (by rw [hr])
  · rw [Function.update_of_ne hr] at hv
    exact Or.inr (hrel.rowsSeen row v hv)
theorem continue_read (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (ch : Charge) (hch : (ch = .call ∧ ¬IsDigestRow X) ∨ (ch = .mass ∧ IsDigestRow X))
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.next U X (τ ⟨X, hX⟩)),
        readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)
  · rw [hTX]
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    · show ws.counters.calls + 1 = st.calls + 1
      rw [hrel.wcalls]
  · rcases hch with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · show ws.counters.mass = ws.counters.mass + _
      rw [if_neg (fun h => hd h.2), Nat.add_zero]
    · show ws.counters.mass + (if ws.counters.calls + 1 ≤ q then 1 else 0) = ws.counters.mass + _
      rw [if_pos (show ws.counters.calls + 1 ≤ q by rw [hrel.wcalls]; omega),
        if_pos (show X ∈ U ∧ IsDigestRow X from ⟨hX, hd⟩)]
  · have := hrel.probes
    rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
  · exact hrel.mem
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hrel.hidden
    · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_call (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  have h := continue_read hrel hlt X hX .call (Or.inl ⟨rfl, hnd⟩) hTX hnc hcell henc
  rwa [RouterState.next_of_not U st X _ (fun h' => hnd h'.2)] at h
theorem continue_probe (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial
      | selectedTarget t pickLow => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_callP (g : HashOutput → HashOutput) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = g (τ ⟨X, hX⟩))
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (g (τ ⟨X, hX⟩), st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)
  · rw [hTX, RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · have := hrel.probes
    show ws.counters.probes ≤ ws.counters.calls + 1
    omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_probeP (g : HashOutput → HashOutput) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = g (τ ⟨X, hX⟩)) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (g (τ ⟨X, hX⟩), st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial
      | selectedTarget t pickLow => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
/-- FTS seeds of family `f` disclosed by the router so far. -/
@[irreducible] noncomputable def DiscSeeds (st : RouterState) (f : Fin (2 ^ 31) × Fin 9) : Finset CanonGraph.WctAddr :=
  Finset.univ.filter fun w => (w.1, w.2.1) = f ∧ (.inr (.inr w) : Coord) ∈ st.disclosed
theorem mem_DiscSeeds (st : RouterState) (f : Fin (2 ^ 31) × Fin 9) (w : CanonGraph.WctAddr) :
    w ∈ DiscSeeds st f ↔ (w.1, w.2.1) = f ∧ (.inr (.inr w) : Coord) ∈ st.disclosed := by
  unfold DiscSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Lower WOTS seeds of leaf `L` disclosed by the router so far (stage B). -/
@[irreducible] noncomputable def DiscLower (st : RouterState) (L : LowerLeaf) : Finset ChainGraph.Address :=
  Finset.univ.filter fun a => (a.layer, a.tree, a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed
theorem mem_DiscLower (st : RouterState) (L : LowerLeaf) (a : ChainGraph.Address) :
    a ∈ DiscLower st L ↔ (a.layer, a.tree, a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed := by
  unfold DiscLower
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- No seed family is determined by the router's disclosures: FTS families have at most 53 disclosed seeds, WOTS
leaf families at most `famCount − 1` (structurally at most `famCount − 3`: 14 lower, `lower_zero_count_le`; 20 top,
`top_zero_count_le`, campaign T8D). -/
def FamOK (st : RouterState) : Prop :=
  (∀ f, (DiscSeeds st f).card ≤ 53) ∧ ∀ L : LowerLeaf, (DiscLower st L).card ≤ WCT9.famCount L.1.1 - 1
theorem DiscSeeds_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed)
    (f : Fin (2 ^ 31) × Fin 9) : DiscSeeds st f ⊆ DiscSeeds st' f := by
  intro w hw
  rw [mem_DiscSeeds] at hw ⊢
  exact ⟨hw.1, h _ hw.2⟩
theorem DiscLower_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed)
    (L : LowerLeaf) : DiscLower st L ⊆ DiscLower st' L := by
  intro w hw
  rw [mem_DiscLower] at hw ⊢
  exact ⟨hw.1, h _ hw.2⟩
theorem famOK_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed) (hok : FamOK st') :
    FamOK st :=
  ⟨fun f => (Finset.card_le_card (DiscSeeds_mono h f)).trans (hok.1 f),
    fun L => (Finset.card_le_card (DiscLower_mono h L)).trans (hok.2 L)⟩
theorem famOK_of_disclosed {st st' : RouterState} (h : st'.disclosed = st.disclosed) (hok : FamOK st) :
    FamOK st' := famOK_mono (fun x hx => by rw [h] at hx; exact hx) hok
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_disclosed (U : Finset HashInput)
    (st : RouterState) (X : HashInput) (y : HashOutput) : (st.next U X y).disclosed = st.disclosed := by
  unfold RouterState.next RouterState.after
  split_ifs <;> rfl
theorem known_seed_base {D : Coord → Prop} {s : SeedIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem keygen_inl {c : Coord} (hc : c ∈ keygenDisclosed) : ∃ N, c = .inl N := by
  rcases List.mem_append.mp hc with hc | hc
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨level, _, node, _, h⟩ := hc
    unfold treeChild at h
    split_ifs at h
    · obtain ⟨L, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
    · obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
  · rcases encodingDisclosed_shape hc with ⟨n, rfl⟩ | ⟨i, rfl⟩ <;> exact ⟨_, rfl⟩
theorem known_seed_disc (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127)
    (s : SeedIndex) (hc1 : (ws.candidates (.inl (.inr s))).card = 1) : (.inr s : Coord) ∈ st.disclosed := by
  have hk : st.known (.inr s) := by
    by_contra hn
    have := h.two_le hlt hq _ hn
    omega
  rcases known_seed_base hk with hkg | hd
  · obtain ⟨N, hN⟩ := keygen_inl hkg; cases hN
  · exact hd
theorem famKnown_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st)
    (f : WFam) : (famKnown ws.candidates f).card ≤ ClaudeWCT.W9.T3.Security.FamResidual.Seeds.deg (Coord := WCoord) f := by
  rcases f with L | f
  · let e : ChainGraph.Address ↪ WCoord := ⟨fun a => .inl (.inr (.inl a)), fun a a' h => by simpa using h⟩
    refine (Finset.card_le_card (t := (DiscLower st L).map e) ?_).trans
      (by rw [Finset.card_map]; exact hok.2 L)
    intro c hc
    have hm := (mem_famKnown ws.candidates (Sum.inl L : WFam) c).mp hc
    obtain ⟨pt, hpt⟩ := hm.1
    rcases wsplit_inr hpt with ⟨a, ha, rfl, hfp⟩ | ⟨w, rfl, hfp⟩
    · simp only [Prod.mk.injEq] at hfp
      refine Finset.mem_map.mpr ⟨a, (mem_DiscLower st L a).mpr ⟨?_, known_seed_disc h hlt hq _ hm.2⟩, rfl⟩
      rw [Sum.inl.inj hfp.1]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hfp
  · let e : CanonGraph.WctAddr ↪ WCoord := ⟨fun w => .inl (.inr (.inr w)), fun w w' h => by simpa using h⟩
    refine (Finset.card_le_card (t := (DiscSeeds st f).map e) ?_).trans
      (by rw [Finset.card_map]; exact hok.1 f)
    intro c hc
    have hm := (mem_famKnown ws.candidates (Sum.inr f : WFam) c).mp hc
    obtain ⟨pt, hpt⟩ := hm.1
    rcases wsplit_inr hpt with ⟨a, ha, rfl, hfp⟩ | ⟨w, rfl, hfp⟩
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hfp
    · simp only [Prod.mk.injEq] at hfp
      exact Finset.mem_map.mpr ⟨w, (mem_DiscSeeds st f w).mpr ⟨(Sum.inr.inj hfp.1).symm,
        known_seed_disc h hlt hq _ hm.2⟩, rfl⟩
/-- Admissibility of a router guess on an unknown coordinate (the hit, if a label, is a node). -/
theorem Rel.adm (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st)
    (c : Coord) (hc : ¬st.known c) (v : Digest) (hit : Hit WCoord)
    (hpar : ∀ parent, hit = Hit.label parent → (.inl c : WCoord) ≠ parent ∧ ∃ N, parent = .inl (.inl N)) :
    Adm ws.candidates hit ((.inl c : WCoord), v) := by
  refine ⟨h.two_le hlt hq c hc, fun parent hp => (hpar parent hp).1, fun fp _ => ⟨famKnown_le h hlt hq hok fp.1,
    fun parent hp fp' => ?_⟩⟩
  obtain ⟨N, rfl⟩ := (hpar parent hp).2
  intro hs
  cases hs
theorem case_unknownChild (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node)
    (hN : Extract.posOf X = some N.toPos) (cs : Coord × Nat) (hfu : firstUnknown st.known N = some cs) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩) ws) := by
  obtain ⟨hcsm, hcsk⟩ := firstUnknown_some hfu
  have hp : Parsed X := ⟨N, hN⟩
  have hnd : ¬IsDigestRow X := fun hd => not_parsed_of_digest hd hp
  have hadm : ∀ g ∈ (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
      (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
    intro g hg parent hpar
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    simp only [Hit.label.injEq] at hpar
    subst hpar
    exact fun h => childSlots_ne N cs hcsm (Sum.inl.inj h)
  have heff : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).effF ws.candidates =
      ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ := by
    refine effF_self _ _ ?_ (Or.inl rfl)
    intro g hg
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hrel.adm hlt hq hok cs.1 hcsk _ _ fun parent hpar =>
      ⟨hadm _ rfl parent hpar, ⟨N, by simp only [Hit.label.injEq] at hpar; exact hpar.symm⟩⟩
  have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st) (ws := ws) aux
    (rowPresent X) (st.after X) X hX ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
    (hrel.fresh X hX hnd)
  refine (congrArg (QueryOutcome U T vals nv τ a q mon st ws X) hcomp).mpr ?_
  rw [heff]
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔
      slotValue X cs.2 = vals cs.1 ∨ (X ≠ cellValues N vals ∧ N.toPos.proj y = vals (.inl N)) := by
    intro y
    rw [contactTest_parsed hN, hcoh.honestValue, hcoh.honestInput]
    constructor
    · rintro (⟨cs', hcs', h⟩ | h)
      · rw [hfu] at hcs'
        cases hcs'
        exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨cs, hfu, h⟩
      · exact Or.inr h
  have hres : X ≠ cellValues N vals → T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) := fun hXc =>
    hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact hcoh.not_cell_parsed hN hXc N') (not_prefix_parsed hp)
  have hcell : X ≠ cellValues N vals → ∀ N' : CanonGraph.Node, X = cellValues N' vals →
      ∀ cs ∈ childSlots N', st.known cs.1 := fun hXc N' hN' => absurd hN' (hcoh.not_cell_parsed hN hXc N')
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1 := fun L ctr hL => absurd hL (not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  by_cases hs : X ∈ st.seen
  · rw [if_neg (not_not.mpr hs)]
    have hXc : X ≠ cellValues N vals := fun heq => hcsk (hrel.seenCells X hs hX N heq cs hcsm)
    exact continue_read_callP (rowPresent X) hrel hlt X hX hnd (hres hXc) (fun h => h.1 hs) (hcell hXc) henc
  · rw [if_pos hs]
    by_cases hXc : X = cellValues N vals
    · have hslot : slotValue X cs.2 = vals cs.1 := by
        rw [hXc]
        exact slot_cellValues N vals cs hcsm
      have hkeep : ¬(⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) := by
        rw [keep_guess_label]
        intro h
        exact h.1 hslot.symm
      rw [if_neg hkeep]
      exact outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr (Or.inl hslot)⟩ rfl
    · have hTX := hres hXc
      by_cases hk : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hk' := (keep_guess_label (Sum.elim vals nv) (.inl cs.1) (.inl (.inl N)) (slotValue X cs.2) _).mp hk
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, proj_rowPresent hN] at hc
          rcases hc with h | h
          · exact hk'.1 h.symm
          · exact hk'.2 h.2.symm
        exact continue_probeP (rowPresent X) hrel hlt X hX _ hk hadm hTX hnd hnc (hcell hXc) henc
      · rw [if_neg hk]
        refine outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr ?_⟩ rfl
        rw [keep_guess_label, not_and_or, not_not, not_not] at hk
        rcases hk with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨hXc, by rw [hTX, proj_rowPresent hN]; exact h.symm⟩
theorem queryOutcome_congr {X : HashInput}
    {out out' : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))} (h : out = out')
    (h' : QueryOutcome U T vals nv τ a q mon st ws X out') : QueryOutcome U T vals nv τ a q mon st ws X out := h ▸ h'
theorem lookupVal_map (f : Coord → Digest) (cs : List Coord) (c : Coord) (hc : c ∈ cs) :
    lookupVal (cs.map fun c => (c, f c)) c = f c := by
  induction cs with
  | nil => cases hc
  | cons d rest ih =>
      unfold lookupVal
      simp only [List.map_cons, List.find?_cons]
      by_cases hd : d = c
      · subst hd
        simp
      · simp only [hd, decide_false]
        exact ih ((List.mem_cons.mp hc).resolve_left (Ne.symm hd))
theorem discloseStates_counters (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).counters = s.counters := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_rows (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).rows = s.rows := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_candidates (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) :
    (discloseStates U q (Sum.elim vals nv) s cs).candidates c =
      if c ∈ cs.map Sum.inl then {Sum.elim vals nv c} else s.candidates c := by
  induction cs generalizing s with
  | nil => simp [discloseStates]
  | cons d rest ih =>
      change (discloseStates U q (Sum.elim vals nv)
        (disclosedState q s (.inl d) (Sum.elim vals nv (.inl d)) .none) rest).candidates c = _
      rw [ih]
      change (if c ∈ rest.map Sum.inl then {Sum.elim vals nv c}
        else Function.update s.candidates (.inl d) {Sum.elim vals nv (.inl d)} c) = _
      by_cases hr : c ∈ rest.map Sum.inl
      · rw [if_pos hr, if_pos (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hr)]
      · rw [if_neg hr]
        by_cases hd : c = .inl d
        · subst hd
          rw [Function.update_self, if_pos (by rw [List.map_cons]; exact List.mem_cons_self)]
        · rw [Function.update_of_ne hd, if_neg (by simp only [List.map_cons, List.mem_cons]; tauto)]
theorem Rel.discloseStates (hrel : Rel U T vals nv τ a q mon st ws) (cs : List Coord) (hk : ∀ c ∈ cs, st.known c) :
    Rel U T vals nv τ a q mon st (discloseStates U q (Sum.elim vals nv) ws cs) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  refine ⟨hrel.disclosed, hrel.seen, hrel.calls, by rw [hc]; exact hrel.wcalls, by rw [hc]; exact hrel.digests,
    hrel.contact, by rw [hc]; exact hrel.probes, hrel.budget, ?_, ?_, by rw [hr]; exact hrel.rowsEq,
    by rw [hr]; exact hrel.rowsSeen, hrel.seenCells, hrel.seenEnc⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact hrel.mem c
  · intro c hck
    rw [discloseStates_candidates, hc]
    rw [if_neg (fun hm => hck (by
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      have hdc' := Sum.inl.inj hdc
      subst hdc'
      exact hk _ hd))]
    exact hrel.hidden c hck
theorem case_knownChildren (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node)
    (hN : Extract.posOf X = some N.toPos) (hfu : firstUnknown st.known N = none) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U ((childSlots N).map Prod.fst)
      if X = cellFrom N (lookupVal pairs) then do
        let v ← discloseReq U (.inl (.inl N)) .call
        pure (CanonGraph.presentEquiv N (ChainGraph.joinOutput v (a.high N)), st.after X)
      else (fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, .label (.inl (.inl N))⟩) ws) := by
  have hall := firstUnknown_none hfu
  have hp : Parsed X := ⟨N, hN⟩
  have hnd : ¬IsDigestRow X := fun hd => not_parsed_of_digest hd hp
  have hkN : st.known (.inl N) := Known.node hall
  have hkc : ∀ c ∈ (childSlots N).map Prod.fst, st.known c := by
    intro c hc
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
    exact hall cs hcs
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hcf : cellFrom N (lookupVal (((childSlots N).map Prod.fst).map fun c => (c, Sum.elim vals nv (.inl c)))) =
      cellValues N vals := by
    rw [cellFrom_eq]
    apply cellValues_congr
    intro cs hcs
    exact lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ cs.1 (List.mem_map.mpr ⟨cs, hcs, rfl⟩)
  rw [hcf]
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔ X ≠ cellValues N vals ∧ N.toPos.proj y = vals (.inl N) := by
    intro y
    rw [contactTest_parsed hN, hcoh.honestValue, hcoh.honestInput, hfu]
    simp only [reduceCtorEq, false_and, exists_false, false_or]
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, st.known cs.1 := fun L ctr hL => absurd hL (not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  by_cases hXc : X = cellValues N vals
  · rw [if_pos hXc, observed_discloseReq, observed_pure]
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      exact ((hct _).mp hc).1 hXc
    apply outcome_continue hrel hlt X _ hnc
    · rw [RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hXc, hcoh.honest_answer]
      rfl
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.mass = ws.counters.mass + _
      rw [discloseStates_counters, if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤ (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · intro c
      show Sum.elim vals nv c ∈ Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates
        (.inl (.inl N)) {Sum.elim vals nv (.inl (.inl N))} c
      by_cases hc : c = .inl (.inl N)
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl N))
          {Sum.elim vals nv (.inl (.inl N))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hN'
      have : N' = N := cell_eq_of_posOf _ _ hN (by rw [hN', hcoh.cell])
      subst this
      exact hall
    · exact fun _ => henc
  · rw [if_neg hXc]
    have hTX : T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) :=
      hcoh.residual X hX (fun N' => by rw [hcoh.cell]; exact hcoh.not_cell_parsed hN hXc N') (not_prefix_parsed hp)
    have hcell : ∀ N' : CanonGraph.Node, X = cellValues N' vals → ∀ cs ∈ childSlots N', st.known cs.1 :=
      fun N' hN' => absurd hN' (hcoh.not_cell_parsed hN hXc N')
    have hfresh : X ∉ st.seen → (discloseStates U q (Sum.elim vals nv) ws ((childSlots N).map Prod.fst)).rows ⟨X, hX⟩ = none :=
      hrel1.fresh X hX hnd
    have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws ((childSlots N).map Prod.fst)) aux
      (rowPresent X) (st.after X) X hX ⟨none, .label (.inl (.inl N))⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effF_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      have h := continue_read_callP (rowPresent X) hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
      exact h
    · rw [if_pos hs]
      by_cases hk : (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, proj_rowPresent hN] at hc
          exact ((keep_label (Sum.elim vals nv) _ _).mp hk) hc.2.symm
        exact continue_probeP (rowPresent X) hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hXc, ?_⟩⟩ rfl
        rw [keep_label, not_not] at hk
        rw [hTX, proj_rowPresent hN]
        exact hk.symm
theorem honestPrefix_iff {L : EncLeaf} {m : WCT9.LayerMsg} {ctr : BitVec 32} {pad : Wots.RowPad} :
    HonestPrefix vals a (Wots.encRow L.toWots m ctr pad) ↔
      Wots.encRow L.toWots m ctr pad = Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr := by
  constructor
  · rintro ⟨L', ctr', hX, hp⟩
    obtain ⟨rfl, rfl⟩ := encRow_encLeaf hX
    exact ⟨hX, hp⟩
  · rintro ⟨hX, hp⟩
    exact ⟨L, ctr, hX, hp⟩
theorem Coherent.referenceInput_eq (hcoh : Coherent U T vals nv τ a) {L : EncLeaf} {m : WCT9.LayerMsg}
    {ctr : BitVec 32} {pad : Wots.RowPad}
    (h : Wots.referenceInput T L.toWots = some (Wots.encRow L.toWots m ctr pad)) :
    Wots.encRow L.toWots m ctr pad = Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr := by
  obtain ⟨r, hr, hX⟩ := hcoh.referenceInput L _ h
  obtain ⟨-, hc⟩ := encRow_encLeaf hX
  have hcap := (capSel_eq_some.mp hr).2
  refine ⟨by rw [hX, ← hc], ?_, ?_⟩
  · rw [hc, BitVec.toNat_ofNat]
    have := r.1.isLt
    have hm : r.1.val % 2 ^ 32 = r.1.val := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    exact hcap
  · intro r' hr'
    rw [hr] at hr'
    cases hr'
    rw [hc, BitVec.toNat_ofNat]
    have := r.1.isLt
    omega
theorem encRow_not_digest (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad) :
    ¬IsDigestRow (Wots.encRow L.toWots m ctr pad) := by
  rintro ⟨rho, m', c, h⟩
  exact encRow_ne_digest' _ _ _ _ _ _ _ h
theorem case_enc_known (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32)
    (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m) (hXe : X = Wots.encRow L.toWots m ctr pad)
    (hkm : firstUnknownMsg st.known L = none) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
      if X = Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
        tickReq U .call
        pure (prefixValue a L ctr, st.after X)
      else (fun y => (y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, encodingHit L.1.lay (refDigest a L)⟩) ws) := by
  have hall := firstUnknownMsg_none hkm
  have hnp : ¬Parsed X := by rw [hXe]; exact not_parsed_of_encRow ⟨L, m, ctr, pad, hfit, rfl⟩
  have hnd : ¬IsDigestRow X := by rw [hXe]; exact encRow_not_digest L m ctr pad
  have hnext : st.next U X (T (.inl (.inr X))) = st.after X := RouterState.next_of_not U st X _ (fun h => hnd h.2)
  have hkc : ∀ c ∈ (msgSlots L).map Prod.fst, st.known c := by
    intro c hc
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
    exact hall cs hcs
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hmv : msgVals (lookupVal (((msgSlots L).map Prod.fst).map fun c => (c, Sum.elim vals nv (.inl c)))) L =
      msgVals vals L :=
    msgVals_congr _ _ L (fun cs hcs =>
      lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ cs.1 (List.mem_map.mpr ⟨cs, hcs, rfl⟩))
  rw [hmv]
  have hct : ∀ y : HashOutput, ContactTest T st.known X y ↔
      Wots.referenceInput T L.toWots ≠ some X ∧ WCT9.encodingAnswer L.1.lay y = refDigest a L := by
    intro y
    rw [hXe, contactTest_enc hfit, hcoh.honestValue, hcoh.decode_ref, ← hXe, hkm] <;>
      simp only [reduceCtorEq, false_and, exists_false, false_or]
  have hcell : ∀ N' : CanonGraph.Node, X = cellValues N' vals → ∀ cs ∈ childSlots N', st.known cs.1 :=
    fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N')
  have henc : ∀ (L' : EncLeaf) (ctr' : BitVec 32), X = Wots.encRow L'.toWots (msgVals vals L') ctr' 0 →
      ∀ cs ∈ msgSlots L', st.known cs.1 := by
    intro L' ctr' hL'
    rw [hXe] at hL'
    obtain ⟨rfl, -⟩ := encRow_encLeaf hL'
    exact hall
  by_cases hpre : X = Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr
  · rw [if_pos hpre, observed_tickReq, observed_pure]
    have hTX : T (.inl (.inr X)) = prefixValue a L ctr := by
      rw [hpre.1]
      exact hcoh.prefixRow L ctr hpre.2
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      rw [hct] at hc
      apply hc.1
      rw [hpre.1]
      apply hcoh.prefix_ref L ctr hpre.2
      rw [← hTX]
      exact (hcoh.decode_ref L _).mpr hc.2
    apply outcome_continue hrel1 hlt X _ hnc
      (tickState q (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)) .call)
    · rw [hnext, hTX]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)).counters.mass =
        (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)).counters.mass + _
      rw [if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · exact hrel1.mem
    · exact hrel1.hidden
    · exact hrel1.rowsEq
    · intro row v hv; exact Or.inr (hrel1.rowsSeen row v hv)
    · exact fun _ => hcell
    · exact fun _ => henc
  · rw [if_neg hpre]
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual_unparsed X hX hnp (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N')
        (by rw [hXe, honestPrefix_iff, ← hXe]; exact hpre)
    have hri : Wots.referenceInput T L.toWots ≠ some X := by
      rw [hXe]
      intro h
      exact hpre (by rw [hXe]; exact hcoh.referenceInput_eq h)
    have hfresh := hrel1.fresh X hX hnd
    have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)) aux
      (st.after X) X hX ⟨none, encodingHit L.1.lay (refDigest a L)⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effF_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      exact continue_read_call hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
    · rw [if_pos hs]
      by_cases hk : (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX] at hc
          exact ((keep_encodingHit (Sum.elim vals nv) _ _ _).mp hk) hc.2.symm
        exact continue_probe hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hri, ?_⟩⟩ rfl
        rw [keep_encodingHit, not_not] at hk
        rw [hTX]
        exact hk.symm
theorem case_enc_unknown (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) (hX : X ∈ U) (L : EncLeaf) (m : WCT9.LayerMsg)
    (ctr : BitVec 32) (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m)
    (hXe : X = Wots.encRow L.toWots m ctr pad) (cs : Coord × Nat) (hfu : firstUnknownMsg st.known L = some cs) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl cs.1, slotValue X cs.2), .target (refDigest a L)⟩) ws) := by
  rw [st.firstUnknownMsg_none L] at hfu
  cases hfu
theorem case_digest (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, if st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X)) <$>
        readReq U ⟨X, hX⟩ .mass) ws) := by
  have hnp := not_parsed_of_digest hd
  have hne : ¬EncRow X := by
    rintro ⟨L, m, ctr, pad, -, rfl⟩
    exact encRow_not_digest L m ctr pad hd
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N') (not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), observed_readReq, observed_pure, map_pure]
  have h := continue_read hrel hlt X hX .mass (Or.inr ⟨rfl, hd⟩) hTX
    (fun h => contactTest_other hnp hne h.2.2)
    (fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne)
  have heq : (if st.Fresh X then { st.after X with births := (X, τ ⟨X, hX⟩) :: st.births } else st.after X) =
      st.next U X (τ ⟨X, hX⟩) := by
    unfold RouterState.next
    by_cases hf : st.Fresh X
    · rw [if_pos hf, if_pos ⟨hX, hd, hf⟩]
    · rw [if_neg hf, if_neg (fun h' => hf h'.2.2)]
  rw [← heq] at h
  exact h
theorem case_other (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (hne : ¬EncRow X) (hnd : ¬IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call) ws) := by
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' => by rw [hcoh.cell]; exact not_cell_unparsed hcoh hnp N') (not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
  exact continue_read_call hrel hlt X hX hnd hTX (fun h => contactTest_other hnp hne h.2.2)
    (fun N' hN' => absurd hN' (not_cell_unparsed hcoh hnp N'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne)
theorem routeQuery_observed (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (observedRun aux q (Sum.elim vals nv) τ (routeQuery U a st X) ws) := by
  unfold routeQuery
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hN := Classical.choose_spec hp
      split
      · rename_i cs hfu
        exact case_unknownChild aux hcoh hrel hlt hq hok X hX _ hN cs hfu
      · rename_i hfu
        exact case_knownChildren aux hcoh hrel hlt X hX _ hN hfu
    · rw [dif_neg hp]
      by_cases he : EncRow X
      · rw [dif_pos he]
        have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec he)))
        split
        · rename_i cs hfu
          exact case_enc_unknown aux hcoh hrel hlt hq hok X hX _ _ _ _ hspec.1 hspec.2 cs hfu
        · rename_i hfu
          exact case_enc_known aux hcoh hrel hlt X hX _ _ _ _ hspec.1 hspec.2 hfu
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd]
          exact case_digest aux hcoh hrel hlt X hX hd
        · rw [if_neg hd]
          exact case_other aux hcoh hrel hlt X hX hp he hd
  · rw [dif_neg hX]
    exact case_outside aux hcoh hrel hlt X hX
end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  CanonGraph.Paired.joinLabels (fun N => vals (.inl N)) a.high

def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃(L : CanonEncoding.EncLeaf)(ctr : BitVec 32),X=Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr

structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : CanonGraph.Paired.Filtered.Agrees T (routerLabels vals a)
  secrets : seedView (secretsOf T)=fun s => vals (.inr s)
  residual : ∀(X : HashInput)(hX : X∈U),
    (∀N : CanonGraph.Node,CanonGraph.Paired.Filtered.Used N → X≠CanonGraph.Paired.cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X))=rowPresent X (τ ⟨X,hX⟩)
  prefixRow : ∀(L : CanonEncoding.EncLeaf)(ctr : BitVec 32),PrefixRow a L ctr →
    T (.inl (.inr (Wots.encRow L.toWots (msgVals vals L) ctr 0)))=prefixValue a L ctr
  search : ∀L : CanonEncoding.EncLeaf,
    Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots =
      (a.sel L).bind fun r => (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun d => (BitVec.ofNat 32 r.1.val,d)
  priv : ∀c : Coordinate,(∀i : Fin 2,(c,i)∉Set.range secretCoordinate) → (∀m : Message,c≠.inr (.inl m)) →
    T (.inr c)=a.priv c
  outside : ∀X,X∉U → T (.inl (.inr X))=(0 : HashOutput)
  nonce : ∀m : Message,(T (.inr (.inr (.inl m)))).extractLsb' 0 128=nv m
  selected : a.sel=CanonEncoding.Paired.selectionsOfRows a.rows

theorem rowPresent_parsed {X : HashInput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) :
    rowPresent X=CanonGraph.Paired.presentEquiv N := by
  have hp : Parsed X := ⟨N,hu,hN⟩
  unfold rowPresent
  rw [dif_pos hp]
  have hc := (Classical.choose_spec hp).2
  have he : Classical.choose hp=N := CanonGraph.toPos_injective (Option.some.inj (hc.symm.trans hN))
  rw [he]

theorem proj_rowPresent {X : HashInput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) (y : HashOutput) :
    Extract.Paired.proj N.toPos (rowPresent X y)=y.extractLsb' 0 128 := by
  rw [rowPresent_parsed hu hN]
  exact CanonGraph.Paired.proj_presentEquiv N y

theorem rowPresent_unparsed {X : HashInput} (hp : ¬Parsed X) (y : HashOutput) : rowPresent X y=y := by
  unfold rowPresent
  rw [dif_neg hp]
  rfl

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}

theorem Coherent.coordVal (h : Coherent U T vals nv τ a) : coordVal (secretsOf T) (routerLabels vals a)=vals := by
  funext c
  cases c with
  | inl N => exact CanonGraph.Paired.joinLabels_val _ _ N
  | inr s => exact congrFun h.secrets s

theorem Coherent.honestInput (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    Extract.Paired.honestInput T N.toPos=cellValues N vals := by
  rw [CanonGraph.Paired.Filtered.honestInput_eq T (routerLabels vals a) h.agrees N
    ((CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu),cell_eq_cellValues _ _ _ hu,h.coordVal]

theorem Coherent.honestValue_node (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) : honestValue T (.inl N)=vals (.inl N) := by
  change Extract.Paired.proj N.toPos (T (.inl (.inr (Extract.Paired.honestInput T N.toPos))))=vals (.inl N)
  rw [CanonGraph.Paired.Filtered.honest_answer T (routerLabels vals a) h.agrees N
    ((CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu)]
  exact CanonGraph.Paired.joinLabels_val _ _ N

theorem Coherent.honestValue_seed (h : Coherent U T vals nv τ a) (s : SeedIndex) :
    honestValue T (.inr s)=vals (.inr s) := congrFun h.secrets s
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem childSlots_used (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : UsedCoord cs.1 := by
  obtain ⟨c,b⟩ := cs
  cases c with
  | inr s => trivial
  | inl n =>
    change CanonGraph.Paired.Filtered.Used n
    by_contra hn
    let secrets : Secrets := fun _ => 0
    let left : Labels := fun _ => 0
    let value := CanonGraph.Paired.presentEquiv n (ChainGraph.joinOutput 1 0)
    let right : Labels := Function.update left n value
    have heq : CanonGraph.Paired.cell secrets N left=CanonGraph.Paired.cell secrets N right := by
      apply CanonGraph.Paired.Filtered.cell_congr secrets N hu
      intro other ho _
      have hne : other≠n := by intro h; subst other; exact hn ho
      exact (Function.update_of_ne hne value left).symm
    rw [cell_eq_cellValues secrets left N hu,cell_eq_cellValues secrets right N hu] at heq
    have hs := congrArg (fun input => slotValue input b) heq
    rw [slot_cellValues N (coordVal secrets left) (Sum.inl n,b) hc,
      slot_cellValues N (coordVal secrets right) (Sum.inl n,b) hc] at hs
    change Extract.Paired.proj n.toPos 0=Extract.Paired.proj n.toPos (right n) at hs
    rw [show right n=value from Function.update_self ..,
      CanonGraph.Paired.proj_presentEquiv,ChainGraph.joinOutput_low] at hs
    have hz : Extract.Paired.proj n.toPos (0 : HashOutput)=0 := by
      cases n <;> simp only [CanonGraph.Node.toPos,Extract.Paired.proj,ite_apply]
      all_goals first | rfl | split_ifs <;> rfl
    rw [hz] at hs
    exact (by decide : (0 : Digest)≠1) hs

theorem Coherent.honestValue_used {U : Finset HashInput} {T : Answers} {vals : Coord→Digest}
    {nv : Message→Digest} {τ : SigGolfCandidate.T3.Security.LargeResidual.Cell U→HashOutput} {a : AuxData}
    (h : Coherent U T vals nv τ a) (c : Coord) (hc : UsedCoord c) : honestValue T c=vals c := by
  cases c with
  | inl n => exact h.honestValue_node n hc
  | inr s => exact h.honestValue_seed s
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell routeAddr)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    CanonGraph.Paired.ftsLabel labels index coord 6 b.val =
      Extract.Paired.proj (CanonGraph.Node.wctNode (ftsTopNode index coord b)).toPos
        (labels (.wctNode (ftsTopNode index coord b))) := by
  unfold CanonGraph.Paired.ftsLabel
  rw [if_neg (by decide)]
  unfold ftsNodeAt
  rw [dif_pos (show 6-1<6 ∧ b.val<2^(7-(6-1)-1) by have:=b.isLt;omega)]
  rfl

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem Coherent.cell (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    CanonGraph.Paired.cell (secretsOf T) N (routerLabels vals a)=cellValues N vals := by
  rw [cell_eq_cellValues _ _ N hu,h.coordVal]

theorem Coherent.honest_answer (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    T (.inl (.inr (cellValues N vals)))=routerLabels vals a N := by
  rw [←h.cell N hu]
  exact h.agrees N hu

theorem Coherent.leafMsg (h : Coherent U T vals nv τ a) (L : CanonEncoding.EncLeaf) :
    Wots.CanonicalRef.sourceMessages T L.toWots=msgVals vals L := by
  rw [CanonEncoding.Paired.sourceMessages_eq_filtered h.agrees L]
  unfold CanonEncoding.Paired.msgLabel msgVals
  by_cases hl : L.1.lay.val<3
  · rw [dif_pos hl,dif_pos hl]
    congr 1
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans (CanonGraph.Paired.joinLabels_low rfl)
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans (CanonGraph.Paired.joinLabels_low rfl)
  · rw [dif_neg hl,dif_neg hl]
    congr 1
    · exact (ftsLabel_top _ _ _ 0).trans (CanonGraph.Paired.joinLabels_val _ _ _)
    · exact (ftsLabel_top _ _ _ 1).trans (CanonGraph.Paired.joinLabels_val _ _ _)

theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : CanonEncoding.EncLeaf) :
    Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots =
      ((a.sel L).bind fun r => WCT9.CanonicalPolicy.decode L.1.lay r.2).getD
        (Wots.dummyDigits (WCT9.CanonicalPolicy.normalLayer L.1.lay)) := by
  unfold Wots.CanonicalRef.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases WCT9.CanonicalPolicy.decode L.1.lay r.2 <;> rfl

theorem Coherent.routerDigits_eq (h : Coherent U T vals nv τ a) (L : Wots.LeafAddr)
    (hL : ∃L' : CanonEncoding.EncLeaf,L'.toWots=L) :
    routerDigits a L=Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L := by
  unfold routerDigits
  rw [dif_pos hL]
  have hs := Classical.choose_spec hL
  have hlay : (Classical.choose hL).1.lay=L.lay := congrArg Wots.LeafAddr.lay hs
  conv_rhs => rw [←hs]
  rw [h.referenceDigits,hlay]

theorem Coherent.routeOk_iff (h : Coherent U T vals nv τ a) (index : Nat) (hindex : index<2^31) :
    RouteOkR a index ↔ RouteOk T index := by
  constructor
  · intro hok lay
    obtain ⟨L,r,hL,hs,hd⟩ := hok lay
    rw [←hL,h.search L,hs]
    have hlay : L.1.lay=lay := congrArg Wots.LeafAddr.lay hL
    simp only [Option.bind_some]
    rw [hlay]
    cases hdec : WCT9.CanonicalPolicy.decode lay r.2 with
    | none => rw [hdec] at hd; cases hd
    | some ds => rfl
  · intro hok lay
    obtain ⟨L,hL⟩ := route_source index hindex lay
    change L.toWots = routeAddr index lay at hL
    have h1 := hok lay
    rw [←hL,h.search L] at h1
    have hlay : L.1.lay=lay := congrArg Wots.LeafAddr.lay hL
    cases hs : a.sel L with
    | none => rw [hs] at h1; cases h1
    | some r =>
      rw [hs] at h1
      refine ⟨L,r,hL,hs,?_⟩
      rw [←hlay]
      simp only [Option.bind_some] at h1
      cases hdec : WCT9.CanonicalPolicy.decode L.1.lay r.2 with
      | none => rw [hdec] at h1; cases h1
      | some ds => rfl
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SphincsSecurity.Concrete
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem Coherent.sel_context (h : Coherent U T vals nv τ a) (L : EncLeaf)
    {r : Fin (2^22)×Digest} (hs : a.sel L=some r) :
    ∃remaining,CanonEncoding.Paired.rowsContext a.rows L.toWots=some remaining ∧
      CanonEncoding.Paired.selectionAt a.rows L remaining=some r := by
  rw [h.selected] at hs
  exact Option.bind_eq_some_iff.mp hs

theorem Coherent.sel_valid (h : Coherent U T vals nv τ a) (L : EncLeaf)
    {r : Fin (2^22)×Digest} (hs : a.sel L=some r) :
    ∃ds,WCT9.CanonicalPolicy.decode L.1.lay r.2=some ds := by
  obtain ⟨remaining,_,hr⟩ := h.sel_context L hs
  obtain ⟨ds,hd⟩ := CanonEncoding.Paired.selectionAt_producer hr
  exact ⟨ds,(WCT9.CanonicalPolicy.producerDecodeAt_spec hd).1⟩

theorem Coherent.search_isSome (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    (Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots).isSome =
      (a.sel L).isSome := by
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      obtain ⟨ds,hd⟩ := h.sel_valid L hs
      simp only [Option.bind_some,hd,Option.map_some,Option.isSome_some]

theorem Coherent.referenceInput (h : Coherent U T vals nv τ a) (L : EncLeaf) (X : HashInput)
    (hX : Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots=some X) :
    ∃r,a.sel L=some r ∧ X=Wots.encRow L.toWots (msgVals vals L) (BitVec.ofNat 32 r.1.val) 0 := by
  unfold Wots.CanonicalRef.referenceInput at hX
  rw [h.search,h.leafMsg] at hX
  cases hs : a.sel L with
  | none => rw [hs] at hX;cases hX
  | some r =>
      rw [hs] at hX
      obtain ⟨ds,hd⟩ := h.sel_valid L hs
      simp only [Option.bind_some,hd,Option.map_some] at hX
      exact ⟨r,rfl,(Option.some.inj hX).symm⟩

theorem Coherent.decode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf)
    (hs : (a.sel L).isSome) (d : Digest) :
    WCT9.CanonicalPolicy.decode L.1.lay d =
      some (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots) ↔
      d=refDigest a L := by
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨ds,hd⟩ := h.sel_valid L hr
  rw [h.referenceDigits]
  simp only [hr,Option.bind_some,hd,Option.getD_some]
  change WCT9.CanonicalPolicy.decode L.1.lay d=some ds ↔ d=refDigest a L
  have href : refDigest a L=r.2 := by simp only [refDigest,hr]
  rw [href]
  constructor
  · intro hd';exact decode_some_injective hd' hd
  · rintro rfl;exact hd

theorem Coherent.prefix_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (ctr : BitVec 32)
    (hp : PrefixRow a L ctr) (hs : (a.sel L).isSome)
    (hd : WCT9.CanonicalPolicy.decode L.1.lay (WCT9.encodingAnswer L.1.lay (prefixValue a L ctr))=
      some (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots)) :
    Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots=
      some (Wots.encRow L.toWots (msgVals vals L) ctr 0) := by
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨remaining,hctx,hsel⟩ := h.sel_context L hr
  obtain ⟨ds,hprod⟩ := CanonEncoding.Paired.selectionAt_producer hsel
  have hdec := (WCT9.CanonicalPolicy.producerDecodeAt_spec hprod).1
  have href : Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots=ds := by
    rw [h.referenceDigits,hr]
    simp only [Option.bind_some,hdec,Option.getD_some]
  rw [href] at hd
  obtain ⟨_,hcap,hle⟩ := hp
  have hlt : ctr.toNat<2^22 := lt_of_lt_of_le hcap (WCT9.searchLimit_le L.1.lay)
  have hpv : prefixValue a L ctr=a.rows L ⟨ctr.toNat,hlt⟩ := by unfold prefixValue;rw [dif_pos hlt]
  rw [hpv] at hd
  have hv : WCT9.encodingAnswer L.1.lay (a.rows L ⟨ctr.toNat,hlt⟩)=r.2 := decode_some_injective hd hdec
  have hraw := (capSel_eq_some.mp hsel).1
  have hle' := hle r hr
  have heq : ctr.toNat=r.1.val := by
    by_contra hne
    have hc : (⟨ctr.toNat,hlt⟩ : Fin (2^22))<r.1 := by change ctr.toNat<r.1.val;omega
    have hn := ((FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hraw).2 ⟨ctr.toNat,hlt⟩ hc
    have hdAt : CanonEncoding.Paired.decodeAt L (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining)
        (a.rows L ⟨ctr.toNat,hlt⟩)=some r.2 := by
      simp only [CanonEncoding.Paired.decodeAt,hv,hprod,Option.isSome_some,if_true]
    rw [hdAt] at hn
    cases hn
  unfold Wots.CanonicalRef.referenceInput
  rw [h.search,h.leafMsg,hr]
  simp only [Option.bind_some,hdec,Option.map_some]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,←heq]
  exact Nat.mod_eq_of_lt (by omega)
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
structure Rel (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) : Prop where
  disclosed : mon.disclosed = st.disclosed
  seen : mon.seen = st.seen
  calls : mon.calls = st.calls
  wcalls : ws.counters.calls = st.calls
  digests : mon.digests = ws.counters.mass
  contact : mon.contact = false
  probes : ws.counters.probes ≤ ws.counters.calls
  budget : st.calls ≤ q
  mem : ∀ c, Sum.elim vals nv c ∈ ws.candidates c
  hidden : ∀ c, ¬(LargeResidual.Paired.RouterState.known st) c → 2 ^ 128 - ws.counters.probes ≤ (ws.candidates (.inl c)).card
  rowsEq : ∀ row v, ws.rows row = some v → v = τ row
  rowsSeen : ∀ row v, ws.rows row = some v → row.val ∈ st.seen ∨ IsDigestRow row.val
  seenCells : ∀ X ∈ st.seen, X ∈ U → ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1
  seenEnc : ∀ X ∈ st.seen, X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32),
    X = Wots.encRow L.toWots (msgVals vals L) ctr 0 → ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
theorem Rel.known (h : Rel U T vals nv τ a q mon st ws) : mon.known = (LargeResidual.Paired.RouterState.known st) := by
  unfold Monitor.known LargeResidual.Paired.RouterState.known
  rw [h.disclosed]
theorem Rel.query (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (y : HashOutput) :
    mon.query U T q X y =
      if X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X y then
        ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests, true⟩
      else ⟨mon.disclosed, X :: mon.seen, mon.calls + 1,
        mon.digests + (if X ∈ U ∧ IsDigestRow X then 1 else 0), false⟩ := by
  have hc : mon.calls + 1 ≤ q := by rw [h.calls]; omega
  unfold Monitor.query
  rw [if_neg (by rw [h.contact]; decide), h.known, h.seen]
  by_cases ht : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X y
  · rw [if_pos ⟨ht.1, ht.2.1, hc, ht.2.2⟩, if_pos ht]
  · rw [if_neg (fun h' => ht ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg ht]
    by_cases hd : X ∈ U ∧ IsDigestRow X
    · rw [if_pos ⟨hd.1, hd.2, hc⟩, if_pos hd]
    · rw [if_neg (fun h' => hd ⟨h'.1, h'.2.1⟩), if_neg hd]
theorem Rel.two_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (c : Coord)
    (hc : ¬(LargeResidual.Paired.RouterState.known st) c) : 2 ≤ (ws.candidates (.inl c)).card := by
  have h1 := h.hidden c hc
  have h2 := h.probes
  have h3 := h.wcalls
  omega
theorem Rel.next (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (ws' : LargeResidual.State WCoord (Cell U)) (δ : Nat)
    (hcalls : ws'.counters.calls = st.calls + 1) (hmass : ws'.counters.mass = ws.counters.mass + δ)
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬(LargeResidual.Paired.RouterState.known st) c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1)
    (st' : RouterState) (hd : st'.disclosed = st.disclosed) (hs : st'.seen = X :: st.seen)
    (hc : st'.calls = st.calls + 1) :
    Rel U T vals nv τ a q ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests + δ, false⟩ st' ws' := by
  have hk : (LargeResidual.Paired.RouterState.known st') = (LargeResidual.Paired.RouterState.known st) := by unfold LargeResidual.Paired.RouterState.known; rw [hd]
  refine ⟨by rw [hd]; exact h.disclosed, by rw [hs, h.seen], by rw [hc, h.calls], by rw [hcalls, hc], ?_, rfl,
    hprobes, (show st'.calls ≤ q by omega), hmem, ?_, hrowsEq, ?_, ?_, ?_⟩
  · simp only [hmass, h.digests]
  · rw [hk]; exact hhidden
  · intro row v hv
    rw [hs]
    rcases hrowsSeen row v hv with h1 | h1 | h1
    · exact Or.inl (by rw [h1]; exact List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · exact Or.inr h1
  · intro Y hY hYU N hu hN cs hcs
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hcell hYU N hu hN cs hcs
    · exact h.seenCells Y hY hYU N hu hN cs hcs
  · intro Y hY hYU L ctr hL
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact henc hYU L ctr hL
    · exact h.seenEnc Y hY hYU L ctr hL
end Relation
def QueryOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U))
    (X : HashInput) (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))) : Prop :=
  ∃ ws' : LargeResidual.State WCoord (Cell U),
    ((mon.query U T q X (T (.inl (.inr X)))).contact = true ∧ out = pure (none, ws') ∧
        ws'.counters.mass = mon.digests ∧ ws'.counters.calls ≤ q) ∨
      ((mon.query U T q X (T (.inl (.inr X)))).contact = false ∧
        out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws') ∧
        Rel U T vals nv τ a q (mon.query U T q X (T (.inl (.inr X)))) (st.next U X (T (.inl (.inr X)))) ws')
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem observed_map {β γ : Type} (f : β → γ) (c : OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (f <$> c) s = (fun r => (r.1.map f, r.2)) <$> observedRun aux q (Sum.elim vals nv) τ c s :=
  runWith_map _ f c s
theorem observed_testReq (st' : RouterState) (X : HashInput) (hX : X ∈ U) (test : Probe WCoord)
    (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effF ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (τ ⟨X, hX⟩, st'), probeState ws ⟨X, hX⟩ (test.effF ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (τ ⟨X, hX⟩, st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
theorem observed_testReqP (g : HashOutput → HashOutput) (st' : RouterState) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (g y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effF ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (g (τ ⟨X, hX⟩), st'), probeState ws ⟨X, hX⟩ (test.effF ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (g (τ ⟨X, hX⟩), st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem outcome_stop (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X))))
    (hout : out = pure (none, stoppedState ws)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨stoppedState ws, Or.inl ⟨?_, hout, ?_, ?_⟩⟩
  · rw [hrel.query hlt, if_pos hc]
  · exact hrel.digests.symm
  · show ws.counters.calls + 1 ≤ q
    rw [hrel.wcalls]
    omega
theorem outcome_continue (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (ws' : LargeResidual.State WCoord (Cell U))
    (hout : out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws'))
    (hcalls : ws'.counters.calls = st.calls + 1)
    (hmass : ws'.counters.mass = ws.counters.mass + (if X ∈ U ∧ IsDigestRow X then 1 else 0))
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬(LargeResidual.Paired.RouterState.known st) c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨ws', Or.inr ⟨?_, hout, ?_⟩⟩
  · rw [hrel.query hlt, if_neg hc]
  · rw [hrel.query hlt, if_neg hc]
    refine hrel.next hlt X ws' _ hcalls hmass hprobes hmem hhidden hrowsEq hrowsSeen hcell henc _ ?_ ?_ ?_ <;>
    · unfold LargeResidual.RouterState.next
      split_ifs <;> rfl
theorem Rel.fresh (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) (hd : ¬IsDigestRow X)
    (hs : X ∉ st.seen) : ws.rows ⟨X, hX⟩ = none := by
  cases hr : ws.rows ⟨X, hX⟩ with
  | none => rfl
  | some v =>
      rcases hrel.rowsSeen _ v hr with h | h
      · exact absurd h hs
      · exact absurd h hd
theorem case_outside (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∉ U) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (tickReq U .call >>= fun _ =>
      pure ((0 : HashOutput), st.after X)) ws) := by
  rw [observed_tickReq, observed_pure]
  apply outcome_continue hrel hlt X _ (fun h => hX h.2.1) (tickState q ws .call)
  · rw [hcoh.outside X hX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hX h'.1)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hX h.1), Nat.add_zero]
  · show ws.counters.probes ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact hrel.rowsEq
  · intro row v hv; exact Or.inr (hrel.rowsSeen row v hv)
  · intro h; exact absurd h hX
  · intro h; exact absurd h hX
theorem rows_update_eq (hrel : Rel U T vals nv τ a q mon st ws) (row0 : Cell U) :
    ∀ row v, Function.update ws.rows row0 (some (τ row0)) row = some v → v = τ row := by
  intro row v hv
  by_cases hr : row = row0
  · subst hr
    rw [Function.update_self] at hv
    exact (Option.some.inj hv).symm
  · rw [Function.update_of_ne hr] at hv
    exact hrel.rowsEq row v hv
theorem rows_update_seen (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) :
    ∀ row v, Function.update ws.rows ⟨X, hX⟩ (some (τ ⟨X, hX⟩)) row = some v →
      row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val := by
  intro row v hv
  by_cases hr : row = ⟨X, hX⟩
  · exact Or.inl (by rw [hr])
  · rw [Function.update_of_ne hr] at hv
    exact Or.inr (hrel.rowsSeen row v hv)
theorem continue_read (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (ch : Charge) (hch : (ch = .call ∧ ¬IsDigestRow X) ∨ (ch = .mass ∧ IsDigestRow X))
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.next U X (τ ⟨X, hX⟩)),
        readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)
  · rw [hTX]
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    · show ws.counters.calls + 1 = st.calls + 1
      rw [hrel.wcalls]
  · rcases hch with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · show ws.counters.mass = ws.counters.mass + _
      rw [if_neg (fun h => hd h.2), Nat.add_zero]
    · show ws.counters.mass + (if ws.counters.calls + 1 ≤ q then 1 else 0) = ws.counters.mass + _
      rw [if_pos (show ws.counters.calls + 1 ≤ q by rw [hrel.wcalls]; omega),
        if_pos (show X ∈ U ∧ IsDigestRow X from ⟨hX, hd⟩)]
  · have := hrel.probes
    rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
  · exact hrel.mem
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hrel.hidden
    · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_call (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  have h := continue_read hrel hlt X hX .call (Or.inl ⟨rfl, hnd⟩) hTX hnc hcell henc
  rwa [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)] at h
theorem continue_probe (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial
      | selectedTarget t pickLow => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_callP (g : HashOutput → HashOutput) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = g (τ ⟨X, hX⟩))
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (g (τ ⟨X, hX⟩), st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)
  · rw [hTX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · have := hrel.probes
    show ws.counters.probes ≤ ws.counters.calls + 1
    omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_probeP (g : HashOutput → HashOutput) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = g (τ ⟨X, hX⟩)) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N → X = cellValues N vals → ∀ cs ∈ childSlots N, (LargeResidual.Paired.RouterState.known st) cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (g (τ ⟨X, hX⟩), st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial
      | selectedTarget t pickLow => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
/-- FTS seeds of family `f` disclosed by the router so far. -/
@[irreducible] noncomputable def DiscSeeds (st : RouterState) (f : Fin (2 ^ 31) × Fin 9) : Finset CanonGraph.WctAddr :=
  Finset.univ.filter fun w => (w.1, w.2.1) = f ∧ (.inr (.inr w) : Coord) ∈ st.disclosed
theorem mem_DiscSeeds (st : RouterState) (f : Fin (2 ^ 31) × Fin 9) (w : CanonGraph.WctAddr) :
    w ∈ DiscSeeds st f ↔ (w.1, w.2.1) = f ∧ (.inr (.inr w) : Coord) ∈ st.disclosed := by
  unfold DiscSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Lower WOTS seeds of leaf `L` disclosed by the router so far (stage B). -/
@[irreducible] noncomputable def DiscLower (st : RouterState) (L : LowerLeaf) : Finset ChainGraph.Address :=
  Finset.univ.filter fun a => (a.layer, a.tree, a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed
theorem mem_DiscLower (st : RouterState) (L : LowerLeaf) (a : ChainGraph.Address) :
    a ∈ DiscLower st L ↔ (a.layer, a.tree, a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed := by
  unfold DiscLower
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- No seed family is determined by the router's disclosures: FTS families have at most 53 disclosed seeds, WOTS
leaf families at most `famCount − 1` (structurally at most `famCount − 3`: 14 lower, `lower_zero_count_le`; 20 top,
`top_zero_count_le`, campaign T8D). -/
def FamOK (st : RouterState) : Prop :=
  (∀ f, (DiscSeeds st f).card ≤ 53) ∧ ∀ L : LowerLeaf, (DiscLower st L).card ≤ WCT9.famCount L.1.1 - 1
theorem DiscSeeds_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed)
    (f : Fin (2 ^ 31) × Fin 9) : DiscSeeds st f ⊆ DiscSeeds st' f := by
  intro w hw
  rw [mem_DiscSeeds] at hw ⊢
  exact ⟨hw.1, h _ hw.2⟩
theorem DiscLower_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed)
    (L : LowerLeaf) : DiscLower st L ⊆ DiscLower st' L := by
  intro w hw
  rw [mem_DiscLower] at hw ⊢
  exact ⟨hw.1, h _ hw.2⟩
theorem famOK_mono {st st' : RouterState} (h : ∀ x ∈ st.disclosed, x ∈ st'.disclosed) (hok : FamOK st') :
    FamOK st :=
  ⟨fun f => (Finset.card_le_card (DiscSeeds_mono h f)).trans (hok.1 f),
    fun L => (Finset.card_le_card (DiscLower_mono h L)).trans (hok.2 L)⟩
theorem famOK_of_disclosed {st st' : RouterState} (h : st'.disclosed = st.disclosed) (hok : FamOK st) :
    FamOK st' := famOK_mono (fun x hx => by rw [h] at hx; exact hx) hok
theorem router_next_disclosed (U : Finset HashInput)
    (st : RouterState) (X : HashInput) (y : HashOutput) : (st.next U X y).disclosed = st.disclosed := by
  unfold LargeResidual.RouterState.next LargeResidual.RouterState.after
  split_ifs <;> rfl
theorem known_seed_base {D : Coord → Prop} {s : SeedIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem keygen_inl {c : Coord} (hc : c ∈ keygenDisclosed) : ∃ N, c = .inl N := by
  rcases List.mem_append.mp hc with hc | hc
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨level, _, node, _, h⟩ := hc
    unfold treeChild at h
    split_ifs at h
    · obtain ⟨L, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
    · obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
  · rcases encodingDisclosed_shape hc with ⟨n, rfl⟩ | ⟨i, rfl⟩ <;> exact ⟨_, rfl⟩
theorem known_seed_disc (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127)
    (s : SeedIndex) (hc1 : (ws.candidates (.inl (.inr s))).card = 1) : (.inr s : Coord) ∈ st.disclosed := by
  have hk : (LargeResidual.Paired.RouterState.known st) (.inr s) := by
    by_contra hn
    have := h.two_le hlt hq _ hn
    omega
  rcases known_seed_base hk with hkg | hd
  · obtain ⟨N, hN⟩ := keygen_inl hkg; cases hN
  · exact hd
theorem famKnown_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st)
    (f : WFam) : (famKnown ws.candidates f).card ≤ ClaudeWCT.W9.T3.Security.FamResidual.Seeds.deg (Coord := WCoord) f := by
  rcases f with L | f
  · let e : ChainGraph.Address ↪ WCoord := ⟨fun a => .inl (.inr (.inl a)), fun a a' h => by simpa using h⟩
    refine (Finset.card_le_card (t := (DiscLower st L).map e) ?_).trans
      (by rw [Finset.card_map]; exact hok.2 L)
    intro c hc
    have hm := (mem_famKnown ws.candidates (Sum.inl L : WFam) c).mp hc
    obtain ⟨pt, hpt⟩ := hm.1
    rcases wsplit_inr hpt with ⟨a, ha, rfl, hfp⟩ | ⟨w, rfl, hfp⟩
    · simp only [Prod.mk.injEq] at hfp
      refine Finset.mem_map.mpr ⟨a, (mem_DiscLower st L a).mpr ⟨?_, known_seed_disc h hlt hq _ hm.2⟩, rfl⟩
      rw [Sum.inl.inj hfp.1]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hfp
  · let e : CanonGraph.WctAddr ↪ WCoord := ⟨fun w => .inl (.inr (.inr w)), fun w w' h => by simpa using h⟩
    refine (Finset.card_le_card (t := (DiscSeeds st f).map e) ?_).trans
      (by rw [Finset.card_map]; exact hok.1 f)
    intro c hc
    have hm := (mem_famKnown ws.candidates (Sum.inr f : WFam) c).mp hc
    obtain ⟨pt, hpt⟩ := hm.1
    rcases wsplit_inr hpt with ⟨a, ha, rfl, hfp⟩ | ⟨w, rfl, hfp⟩
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hfp
    · simp only [Prod.mk.injEq] at hfp
      exact Finset.mem_map.mpr ⟨w, (mem_DiscSeeds st f w).mpr ⟨(Sum.inr.inj hfp.1).symm,
        known_seed_disc h hlt hq _ hm.2⟩, rfl⟩
/-- Admissibility of a router guess on an unknown coordinate (the hit, if a label, is a node). -/
theorem Rel.adm (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st)
    (c : Coord) (hc : ¬(LargeResidual.Paired.RouterState.known st) c) (v : Digest) (hit : Hit WCoord)
    (hpar : ∀ parent, hit = Hit.label parent → (.inl c : WCoord) ≠ parent ∧ ∃ N, parent = .inl (.inl N)) :
    Adm ws.candidates hit ((.inl c : WCoord), v) := by
  refine ⟨h.two_le hlt hq c hc, fun parent hp => (hpar parent hp).1, fun fp _ => ⟨famKnown_le h hlt hq hok fp.1,
    fun parent hp fp' => ?_⟩⟩
  obtain ⟨N, rfl⟩ := (hpar parent hp).2
  intro hs
  cases hs

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell slotValue)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
open ClaudeWCT.W9.T3.Security.LargeResidual (msgVals msgSlots msgSlot_mem_keygen)
open ClaudeWCT.W9.T3.Security.LargeCoupling (encodingRow_parsed_none encRow_encLeaf)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem childSlots_ne (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : cs.1≠.inl N := by
  intro he
  obtain ⟨c,b⟩ := cs
  dsimp only at he
  subst c
  let secrets : Secrets := fun _ => 0
  let left : Labels := fun _ => 0
  let value := CanonGraph.Paired.presentEquiv N (ChainGraph.joinOutput 1 0)
  let right : Labels := Function.update left N value
  have heq : CanonGraph.Paired.cell secrets N left=CanonGraph.Paired.cell secrets N right := by
    apply CanonGraph.Paired.Filtered.cell_congr secrets N hu
    intro other _ hd
    have hne : other≠N := by intro he;subst other;exact (Nat.lt_irrefl _ hd)
    exact (Function.update_of_ne hne value left).symm
  rw [cell_eq_cellValues secrets left N hu,cell_eq_cellValues secrets right N hu] at heq
  have hs := congrArg (fun input => slotValue input b) heq
  rw [slot_cellValues N (coordVal secrets left) (Sum.inl N,b) hc,
    slot_cellValues N (coordVal secrets right) (Sum.inl N,b) hc] at hs
  change Extract.Paired.proj N.toPos 0=Extract.Paired.proj N.toPos (right N) at hs
  rw [show right N=value from Function.update_self ..,
    CanonGraph.Paired.proj_presentEquiv,ChainGraph.joinOutput_low] at hs
  have hz : Extract.Paired.proj N.toPos (0 : HashOutput)=0 := by
    cases N <;> simp only [CanonGraph.Node.toPos,Extract.Paired.proj,ite_apply]
    all_goals first | rfl | split_ifs <;> rfl
  rw [hz] at hs
  exact (by decide : (0 : Digest)≠1) hs

theorem firstUnknown_some {K : Coord→Prop} {N : CanonGraph.Node} {cs : Coord×Nat}
    (h : firstUnknown K N=some cs) : cs∈childSlots N ∧ ¬K cs.1 := by
  unfold firstUnknown at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm,hp⟩
theorem firstUnknown_none {K : Coord→Prop} {N : CanonGraph.Node} (h : firstUnknown K N=none) :
    ∀cs∈childSlots N,K cs.1 := by
  intro cs hc
  have ht := List.find?_eq_none.mp h cs hc
  simpa using ht

theorem RouterState.msgSlot_known (st : RouterState) (L : EncLeaf) (cs : Coord×Nat) (hc : cs∈msgSlots L) :
    RouterState.known st cs.1 := Known.base (Or.inl (msgSlot_mem_keygen hc))

theorem contactTest_parsed {A : Answers} {K : Coord→Prop} {X : HashInput} {y : HashOutput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) :
    ContactTest A K X y ↔
      (∃cs,firstUnknown K N=some cs ∧ slotValue X cs.2=honestValue A cs.1) ∨
        (X≠Extract.Paired.honestInput A N.toPos ∧ Extract.Paired.proj N.toPos y=honestValue A (.inl N)) := by
  constructor
  · rintro (⟨N',_,hN',h⟩ | ⟨L,m,c,pad,_,hX,_⟩)
    · rw [hN] at hN'
      have he := CanonGraph.toPos_injective (Option.some.inj hN')
      subst N';exact h
    · rw [hX,encodingRow_parsed_none] at hN;cases hN
  · intro h
    exact Or.inl ⟨N,(CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu,hN,h⟩

theorem contactTest_enc {A : Answers} {K : Coord→Prop} {y : HashOutput} {L : EncLeaf} {m : WCT9.LayerMsg}
    {c : BitVec 32} {pad : Wots.RowPad} (hfit : Extract.msgFits L.1.lay m) :
    ContactTest A K (Wots.encRow L.toWots m c pad) y ↔
      Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L.toWots≠none ∧
      Wots.CanonicalRef.referenceInput A (Wots.CanonicalRef.sourceMessages A) L.toWots≠some (Wots.encRow L.toWots m c pad) ∧
      WCT9.CanonicalPolicy.decode L.1.lay (WCT9.encodingAnswer L.1.lay y)=
        some (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) L.toWots) := by
  constructor
  · rintro (⟨N',_,hN',_⟩ | ⟨L',m',c',pad',_,hX,h⟩)
    · rw [encodingRow_parsed_none] at hN';cases hN'
    · obtain ⟨rfl,_⟩ := encRow_encLeaf hX
      exact h
  · intro h;exact Or.inr ⟨L,m,c,pad,hfit,rfl,h⟩

theorem not_parsed_of_encRow {X : HashInput} (he : EncRow X) : ¬Parsed X := by
  rintro ⟨N,_,hN⟩
  exact ClaudeWCT.W9.T3.Security.LargeCoupling.not_parsed_of_encRow he ⟨N,hN⟩
theorem not_parsed_of_digest {X : HashInput} (hd : SigGolfCandidate.T3.Security.LargeResidual.IsDigestRow X) :
    ¬Parsed X := by
  rintro ⟨N,_,hN⟩
  exact ClaudeWCT.W9.T3.Security.LargeCoupling.not_parsed_of_digest hd ⟨N,hN⟩
theorem contactTest_other {A : Answers} {K : Coord→Prop} {X : HashInput} {y : HashOutput}
    (hp : ¬Parsed X) (he : ¬EncRow X) : ¬ContactTest A K X y := by
  rintro (⟨N,hu,hN,_⟩ | ⟨L,m,c,pad,hfit,hX,_⟩)
  · exact hp ⟨N,(CanonGraph.Paired.Filtered.used_iff_bounded N).2 hu,hN⟩
  · exact he ⟨L,m,c,pad,hfit,hX⟩

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem Coherent.not_cell_parsed (h : Coherent U T vals nv τ a) {X : HashInput} {N : CanonGraph.Node}
    (hN : Extract.posOf X=some N.toPos) (hne : X≠cellValues N vals) :
    ∀N',CanonGraph.Paired.Filtered.Used N' → X≠cellValues N' vals := by
  intro N' hu heq
  have hp : Extract.posOf X=some N'.toPos := by
    rw [heq,←h.cell N' hu]
    exact CanonGraph.Paired.posOf_cell _ _ _
  rw [hN] at hp
  have he := CanonGraph.toPos_injective (Option.some.inj hp)
  subst N';exact hne heq

theorem not_cell_unparsed (h : Coherent U T vals nv τ a) {X : HashInput} (hp : ¬Parsed X) :
    ∀N',CanonGraph.Paired.Filtered.Used N' → X≠cellValues N' vals := by
  intro N' hu heq
  apply hp;refine ⟨N',hu,?_⟩
  rw [heq,←h.cell N' hu]
  exact CanonGraph.Paired.posOf_cell _ _ _

theorem not_prefix_parsed {X : HashInput} (hp : Parsed X) : ¬HonestPrefix vals a X := by
  rintro ⟨L,ctr,rfl,_⟩
  exact not_parsed_of_encRow ⟨L,_,ctr,0,LargeCoupling.msgFits_msgVals vals L,rfl⟩ hp
theorem not_prefix_enc {X : HashInput} (he : ¬EncRow X) : ¬HonestPrefix vals a X := by
  rintro ⟨L,ctr,rfl,_⟩
  exact he ⟨L,_,ctr,0,LargeCoupling.msgFits_msgVals vals L,rfl⟩
theorem not_enc_parsed {X : HashInput} (hp : Parsed X) (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32)
    (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m) : X≠Wots.encRow L.toWots m ctr pad := by
  rintro rfl
  exact not_parsed_of_encRow ⟨L,m,ctr,pad,hfit,rfl⟩ hp
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
open ClaudeWCT.W9.T3.Security.LargeResidual (msgVals)
open ClaudeWCT.W9.T3.Security.LargeCoupling (encRow_encLeaf)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

theorem honestPrefix_iff {L : EncLeaf} {m : WCT9.LayerMsg} {ctr : BitVec 32} {pad : Wots.RowPad} :
    HonestPrefix vals a (Wots.encRow L.toWots m ctr pad) ↔
      Wots.encRow L.toWots m ctr pad=Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr := by
  constructor
  · rintro ⟨L',ctr',hX,hp⟩
    obtain ⟨rfl,rfl⟩ := encRow_encLeaf hX
    exact ⟨hX,hp⟩
  · rintro ⟨hX,hp⟩;exact ⟨L,ctr,hX,hp⟩

theorem Coherent.referenceInput_eq (hcoh : Coherent U T vals nv τ a) {L : EncLeaf} {m : WCT9.LayerMsg}
    {ctr : BitVec 32} {pad : Wots.RowPad}
    (h : Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots=
      some (Wots.encRow L.toWots m ctr pad)) :
    Wots.encRow L.toWots m ctr pad=Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr := by
  obtain ⟨r,hr,hX⟩ := hcoh.referenceInput L _ h
  obtain ⟨_,hc⟩ := encRow_encLeaf hX
  obtain ⟨remaining,hctx,hsel⟩ := hcoh.sel_context L hr
  have hcap := (capSel_eq_some.mp hsel).2
  refine ⟨by rw [hX,←hc],?_,?_,?_⟩
  · rw [hctx];rfl
  · rw [hc,BitVec.toNat_ofNat]
    have hbound := r.1.isLt
    rw [Nat.mod_eq_of_lt (show r.1.val<2^32 by omega)]
    exact hcap
  · intro r' hr'
    rw [hr] at hr';cases hr'
    rw [hc,BitVec.toNat_ofNat]
    have hbound := r.1.isLt
    omega

theorem Coherent.residual_unparsed (h : Coherent U T vals nv τ a) (X : HashInput) (hX : X∈U)
    (hp : ¬Parsed X)
    (hc : ∀N,CanonGraph.Paired.Filtered.Used N → X≠CanonGraph.Paired.cell (secretsOf T) N (routerLabels vals a))
    (hn : ¬HonestPrefix vals a X) : T (.inl (.inr X))=τ ⟨X,hX⟩ := by
  exact (h.residual X hX hc hn).trans (rowPresent_unparsed hp _)
end Coherent
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
open ClaudeWCT.W9.T3.Security.LargeResidual (lookupVal)
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem case_unknownChild (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (hN : Extract.posOf X = some N.toPos) (cs : Coord × Nat) (hfu : firstUnknown (LargeResidual.Paired.RouterState.known st) N = some cs) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩) ws) := by
  obtain ⟨hcsm, hcsk⟩ := LargeResidual.Paired.firstUnknown_some hfu
  have hp : Parsed X := ⟨N,hu,hN⟩
  have hnd : ¬IsDigestRow X := fun hd => LargeResidual.Paired.not_parsed_of_digest hd hp
  have hadm : ∀ g ∈ (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
      (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
    intro g hg parent hpar
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    simp only [Hit.label.injEq] at hpar
    subst hpar
    exact fun h => LargeResidual.Paired.childSlots_ne N hu cs hcsm (Sum.inl.inj h)
  have heff : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).effF ws.candidates =
      ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ := by
    refine effF_self _ _ ?_ (Or.inl rfl)
    intro g hg
    simp only [Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hrel.adm hlt hq hok cs.1 hcsk _ _ fun parent hpar =>
      ⟨hadm _ rfl parent hpar, ⟨N, by simp only [Hit.label.injEq] at hpar; exact hpar.symm⟩⟩
  have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st) (ws := ws) aux
    (rowPresent X) (st.after X) X hX ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
    (hrel.fresh X hX hnd)
  refine (congrArg (QueryOutcome U T vals nv τ a q mon st ws X) hcomp).mpr ?_
  rw [heff]
  have hct : ∀ y : HashOutput, ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔
      slotValue X cs.2 = vals cs.1 ∨ (X ≠ cellValues N vals ∧ Extract.Paired.proj N.toPos y = vals (.inl N)) := by
    intro y
    rw [LargeResidual.Paired.contactTest_parsed hu hN, hcoh.honestValue_node N hu, hcoh.honestInput N hu]
    constructor
    · rintro (⟨cs', hcs', h⟩ | h)
      · rw [hfu] at hcs'
        cases hcs'
        exact Or.inl (by simpa only [hcoh.honestValue_used cs.1 (LargeResidual.Paired.childSlots_used N hu cs hcsm)] using h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨cs,hfu,by simpa only [hcoh.honestValue_used cs.1 (LargeResidual.Paired.childSlots_used N hu cs hcsm)] using h⟩
      · exact Or.inr h
  have hres : X ≠ cellValues N vals → T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) := fun hXc =>
    hcoh.residual X hX (fun N' hu' => by rw [hcoh.cell N' hu']; exact hcoh.not_cell_parsed hN hXc N' hu') (LargeResidual.Paired.not_prefix_parsed hp)
  have hcell : X ≠ cellValues N vals → ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals →
      ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 := fun hXc N' hu' hN' => absurd hN' (hcoh.not_cell_parsed hN hXc N' hu')
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 := fun L ctr hL => absurd hL (LargeResidual.Paired.not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  by_cases hs : X ∈ st.seen
  · rw [if_neg (not_not.mpr hs)]
    have hXc : X ≠ cellValues N vals := fun heq => hcsk (hrel.seenCells X hs hX N hu heq cs hcsm)
    exact continue_read_callP (rowPresent X) hrel hlt X hX hnd (hres hXc) (fun h => h.1 hs) (hcell hXc) henc
  · rw [if_pos hs]
    by_cases hXc : X = cellValues N vals
    · have hslot : slotValue X cs.2 = vals cs.1 := by
        rw [hXc]
        exact slot_cellValues N vals cs hcsm
      have hkeep : ¬(⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) := by
        rw [keep_guess_label]
        intro h
        exact h.1 hslot.symm
      rw [if_neg hkeep]
      exact outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr (Or.inl hslot)⟩ rfl
    · have hTX := hres hXc
      by_cases hk : (⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hk' := (keep_guess_label (Sum.elim vals nv) (.inl cs.1) (.inl (.inl N)) (slotValue X cs.2) _).mp hk
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, LargeResidual.Paired.proj_rowPresent hu hN] at hc
          rcases hc with h | h
          · exact hk'.1 h.symm
          · exact hk'.2 h.2.symm
        exact continue_probeP (rowPresent X) hrel hlt X hX _ hk hadm hTX hnd hnc (hcell hXc) henc
      · rw [if_neg hk]
        refine outcome_stop hrel hlt X _ ⟨hs, hX, (hct _).mpr ?_⟩ rfl
        rw [keep_guess_label, not_and_or, not_not, not_not] at hk
        rcases hk with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨hXc, by rw [hTX, LargeResidual.Paired.proj_rowPresent hu hN]; exact h.symm⟩
theorem queryOutcome_congr {X : HashInput}
    {out out' : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))} (h : out = out')
    (h' : QueryOutcome U T vals nv τ a q mon st ws X out') : QueryOutcome U T vals nv τ a q mon st ws X out := h ▸ h'
theorem lookupVal_map (f : Coord → Digest) (cs : List Coord) (c : Coord) (hc : c ∈ cs) :
    lookupVal (cs.map fun c => (c, f c)) c = f c := by
  induction cs with
  | nil => cases hc
  | cons d rest ih =>
      unfold lookupVal
      simp only [List.map_cons, List.find?_cons]
      by_cases hd : d = c
      · subst hd
        simp
      · simp only [hd, decide_false]
        exact ih ((List.mem_cons.mp hc).resolve_left (Ne.symm hd))
theorem discloseStates_counters (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).counters = s.counters := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_rows (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).rows = s.rows := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_candidates (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) :
    (discloseStates U q (Sum.elim vals nv) s cs).candidates c =
      if c ∈ cs.map Sum.inl then {Sum.elim vals nv c} else s.candidates c := by
  induction cs generalizing s with
  | nil => simp [discloseStates]
  | cons d rest ih =>
      change (discloseStates U q (Sum.elim vals nv)
        (disclosedState q s (.inl d) (Sum.elim vals nv (.inl d)) .none) rest).candidates c = _
      rw [ih]
      change (if c ∈ rest.map Sum.inl then {Sum.elim vals nv c}
        else Function.update s.candidates (.inl d) {Sum.elim vals nv (.inl d)} c) = _
      by_cases hr : c ∈ rest.map Sum.inl
      · rw [if_pos hr, if_pos (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hr)]
      · rw [if_neg hr]
        by_cases hd : c = .inl d
        · subst hd
          rw [Function.update_self, if_pos (by rw [List.map_cons]; exact List.mem_cons_self)]
        · rw [Function.update_of_ne hd, if_neg (by simp only [List.map_cons, List.mem_cons]; tauto)]
theorem Rel.discloseStates (hrel : Rel U T vals nv τ a q mon st ws) (cs : List Coord) (hk : ∀ c ∈ cs, (LargeResidual.Paired.RouterState.known st) c) :
    Rel U T vals nv τ a q mon st (discloseStates U q (Sum.elim vals nv) ws cs) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  refine ⟨hrel.disclosed, hrel.seen, hrel.calls, by rw [hc]; exact hrel.wcalls, by rw [hc]; exact hrel.digests,
    hrel.contact, by rw [hc]; exact hrel.probes, hrel.budget, ?_, ?_, by rw [hr]; exact hrel.rowsEq,
    by rw [hr]; exact hrel.rowsSeen, hrel.seenCells, hrel.seenEnc⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact hrel.mem c
  · intro c hck
    rw [discloseStates_candidates, hc]
    rw [if_neg (fun hm => hck (by
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      have hdc' := Sum.inl.inj hdc
      subst hdc'
      exact hk _ hd))]
    exact hrel.hidden c hck
theorem case_knownChildren (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (hN : Extract.posOf X = some N.toPos) (hfu : firstUnknown (LargeResidual.Paired.RouterState.known st) N = none) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U ((childSlots N).map Prod.fst)
      if X = cellFrom N (lookupVal pairs) then do
        let v ← discloseReq U (.inl (.inl N)) .call
        pure (CanonGraph.Paired.presentEquiv N (ChainGraph.joinOutput v (a.high N)), st.after X)
      else (fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, .label (.inl (.inl N))⟩) ws) := by
  have hall := LargeResidual.Paired.firstUnknown_none hfu
  have hp : Parsed X := ⟨N,hu,hN⟩
  have hnd : ¬IsDigestRow X := fun hd => LargeResidual.Paired.not_parsed_of_digest hd hp
  have hkN : (LargeResidual.Paired.RouterState.known st) (.inl N) := Known.node hall
  have hkc : ∀ c ∈ (childSlots N).map Prod.fst, (LargeResidual.Paired.RouterState.known st) c := by
    intro c hc
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
    exact hall cs hcs
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hcf : cellFrom N (lookupVal (((childSlots N).map Prod.fst).map fun c => (c, Sum.elim vals nv (.inl c)))) =
      cellValues N vals := by
    change cellValues N _ = cellValues N vals
    apply cellValues_congr
    intro cs hcs
    exact lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ cs.1 (List.mem_map.mpr ⟨cs, hcs, rfl⟩)
  rw [hcf]
  have hct : ∀ y : HashOutput, ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔ X ≠ cellValues N vals ∧ Extract.Paired.proj N.toPos y = vals (.inl N) := by
    intro y
    rw [LargeResidual.Paired.contactTest_parsed hu hN, hcoh.honestValue_node N hu, hcoh.honestInput N hu, hfu]
    simp only [reduceCtorEq, false_and, exists_false, false_or]
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 := fun L ctr hL => absurd hL (LargeResidual.Paired.not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  by_cases hXc : X = cellValues N vals
  · rw [if_pos hXc, observed_discloseReq, observed_pure]
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      exact ((hct _).mp hc).1 hXc
    apply outcome_continue hrel hlt X _ hnc
    · rw [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hXc, hcoh.honest_answer N hu]
      rfl
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.mass = ws.counters.mass + _
      rw [discloseStates_counters, if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤ (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · intro c
      show Sum.elim vals nv c ∈ Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates
        (.inl (.inl N)) {Sum.elim vals nv (.inl (.inl N))} c
      by_cases hc : c = .inl (.inl N)
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl N))
          {Sum.elim vals nv (.inl (.inl N))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hu' hN'
      have hp' : Extract.posOf X=some N'.toPos := by
        rw [hN',←hcoh.cell N' hu']
        exact CanonGraph.Paired.posOf_cell _ _ _
      have he : N'=N := CanonGraph.toPos_injective (Option.some.inj (hp'.symm.trans hN))
      subst N'
      exact hall
    · exact fun _ => henc
  · rw [if_neg hXc]
    have hTX : T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) :=
      hcoh.residual X hX (fun N' hu' => by rw [hcoh.cell N' hu']; exact hcoh.not_cell_parsed hN hXc N' hu') (LargeResidual.Paired.not_prefix_parsed hp)
    have hcell : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals → ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 :=
      fun N' hu' hN' => absurd hN' (hcoh.not_cell_parsed hN hXc N' hu')
    have hfresh : X ∉ st.seen → (discloseStates U q (Sum.elim vals nv) ws ((childSlots N).map Prod.fst)).rows ⟨X, hX⟩ = none :=
      hrel1.fresh X hX hnd
    have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws ((childSlots N).map Prod.fst)) aux
      (rowPresent X) (st.after X) X hX ⟨none, .label (.inl (.inl N))⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effF_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      have h := continue_read_callP (rowPresent X) hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
      exact h
    · rw [if_pos hs]
      by_cases hk : (⟨none, .label (.inl (.inl N))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, LargeResidual.Paired.proj_rowPresent hu hN] at hc
          exact ((keep_label (Sum.elim vals nv) _ _).mp hk) hc.2.symm
        exact continue_probeP (rowPresent X) hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hXc, ?_⟩⟩ rfl
        rw [keep_label, not_not] at hk
        rw [hTX, LargeResidual.Paired.proj_rowPresent hu hN]
        exact hk.symm

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
open ClaudeWCT.W9.T3.Security.LargeResidual (lookupVal encodingHit keep_encodingHit)
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem case_enc_known (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32)
    (pad : Wots.RowPad) (hfit : Extract.msgFits L.1.lay m) (hXe : X = Wots.encRow L.toWots m ctr pad)
    :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
      if X = Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
        tickReq U .call
        pure (prefixValue a L ctr, st.after X)
      else if (a.sel L).isSome then
        (fun y => (y,st.after X)) <$> testReq U (decide (X ∉ st.seen)) ⟨X,hX⟩ ⟨none,encodingHit L.1.lay (refDigest a L)⟩
      else (fun y => (y,st.after X)) <$> readReq U ⟨X,hX⟩ .call) ws) := by
  have hall : ∀cs∈msgSlots L,LargeResidual.Paired.RouterState.known st cs.1 :=
    LargeResidual.Paired.RouterState.msgSlot_known st L
  have hnp : ¬Parsed X := by rw [hXe]; exact LargeResidual.Paired.not_parsed_of_encRow ⟨L, m, ctr, pad, hfit, rfl⟩
  have hnd : ¬IsDigestRow X := by rw [hXe]; exact encRow_not_digest L m ctr pad
  have hnext : st.next U X (T (.inl (.inr X))) = st.after X := LargeResidual.RouterState.next_of_not U st X _ (fun h => hnd h.2)
  have hkc : ∀ c ∈ (msgSlots L).map Prod.fst, (LargeResidual.Paired.RouterState.known st) c := by
    intro c hc
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
    exact hall cs hcs
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hmv : msgVals (lookupVal (((msgSlots L).map Prod.fst).map fun c => (c, Sum.elim vals nv (.inl c)))) L =
      msgVals vals L :=
    msgVals_congr _ _ L (fun cs hcs =>
      lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ cs.1 (List.mem_map.mpr ⟨cs, hcs, rfl⟩))
  rw [hmv]
  have hct : ∀y : HashOutput,ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔
      (a.sel L).isSome ∧
        Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots≠some X ∧
        WCT9.encodingAnswer L.1.lay y=refDigest a L := by
    intro y
    rw [hXe,LargeResidual.Paired.contactTest_enc hfit,←hXe]
    have hs : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots≠none ↔
        (a.sel L).isSome := by
      rw [←Option.isSome_iff_ne_none,hcoh.search_isSome]
    rw [hs]
    constructor
    · rintro ⟨hsel,hi,hd⟩
      exact ⟨hsel,hi,(hcoh.decode_ref L hsel _).mp hd⟩
    · rintro ⟨hsel,hi,hd⟩
      exact ⟨hsel,hi,(hcoh.decode_ref L hsel _).mpr hd⟩
  have hcell : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals → ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 :=
    fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp N' hu')
  have henc : ∀ (L' : EncLeaf) (ctr' : BitVec 32), X = Wots.encRow L'.toWots (msgVals vals L') ctr' 0 →
      ∀ cs ∈ msgSlots L', (LargeResidual.Paired.RouterState.known st) cs.1 := by
    intro L' ctr' hL'
    rw [hXe] at hL'
    obtain ⟨rfl, -⟩ := encRow_encLeaf hL'
    exact hall
  by_cases hpre : X = Wots.encRow L.toWots (msgVals vals L) ctr 0 ∧ PrefixRow a L ctr
  · rw [if_pos hpre, observed_tickReq, observed_pure]
    have hTX : T (.inl (.inr X)) = prefixValue a L ctr := by
      rw [hpre.1]
      exact hcoh.prefixRow L ctr hpre.2
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      rw [hct] at hc
      apply hc.2.1
      rw [hpre.1]
      apply hcoh.prefix_ref L ctr hpre.2 hc.1
      rw [← hTX]
      exact (hcoh.decode_ref L hc.1 _).mpr hc.2.2
    apply outcome_continue hrel1 hlt X _ hnc
      (tickState q (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)) .call)
    · rw [hnext, hTX]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1 = st.calls + 1
      rw [discloseStates_counters, hrel.wcalls]
    · show (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)).counters.mass =
        (discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)).counters.mass + _
      rw [if_neg (fun h => hnd h.2), Nat.add_zero]
    · show (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (discloseStates U q (Sum.elim vals nv) ws _).counters.calls + 1
      rw [discloseStates_counters]
      have := hrel.probes; omega
    · exact hrel1.mem
    · exact hrel1.hidden
    · exact hrel1.rowsEq
    · intro row v hv; exact Or.inr (hrel1.rowsSeen row v hv)
    · exact fun _ => hcell
    · exact fun _ => henc
  · rw [if_neg hpre]
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp N' hu')
        (by rw [hXe, LargeResidual.Paired.honestPrefix_iff, ← hXe]; exact hpre)
    have hri : Wots.CanonicalRef.referenceInput T (Wots.CanonicalRef.sourceMessages T) L.toWots ≠ some X := by
      rw [hXe]
      intro h
      exact hpre (by rw [hXe]; exact hcoh.referenceInput_eq h)
    by_cases hsel : (a.sel L).isSome
    · rw [if_pos hsel]
      have hfresh := hrel1.fresh X hX hnd
      have hcomp := observed_testReq (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
        (ws := discloseStates U q (Sum.elim vals nv) ws ((msgSlots L).map Prod.fst)) aux
        (st.after X) X hX ⟨none, encodingHit L.1.lay (refDigest a L)⟩ hfresh
      refine queryOutcome_congr hcomp ?_
      rw [effF_self _ _ (by intro g hg; cases hg)]
      have hadm : ∀ g ∈ (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).guess, ∀ parent,
          (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
        intro g hg; cases hg
      by_cases hs : X ∈ st.seen
      · rw [if_neg (not_not.mpr hs)]
        exact continue_read_call hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
      · rw [if_pos hs]
        by_cases hk : (⟨none, encodingHit L.1.lay (refDigest a L)⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
        · rw [if_pos hk]
          have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
            rintro ⟨-, -, hc⟩
            rw [hct, hTX] at hc
            exact ((keep_encodingHit (Sum.elim vals nv) _ _ _).mp hk) hc.2.2.symm
          exact continue_probe hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
        · rw [if_neg hk]
          refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hsel,hri,?_⟩⟩ rfl
          rw [keep_encodingHit, not_not] at hk
          rw [hTX]
          exact hk.symm
    · rw [if_neg hsel,observed_map]
      rw [←bind_pure (readReq U ⟨X,hX⟩ .call),observed_readReq,observed_pure,map_pure]
      exact continue_read_call hrel1 hlt X hX hnd hTX
        (fun hc => hsel ((hct _).mp hc.2.2).1) hcell henc

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue IsDigestRow dummyDigest State Probe Hit Charge Cell
  readState probeState stoppedState tickState disclosedState runWith_map mem_restrict card_restrict_ge low)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_pure effF_self adm_of_plain Adm famKnown famSeeds
  mem_famSeeds mem_famKnown)
open SigGolfCandidate.T3.Security.LargeCoupling (low_eq keep_guess_label keep_label keep_target
  keep_guess_target dummyDigest_decode')
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord Coord SeedIndex WFam wsplit_inr keygenDisclosed keygenCacheDisclosed encodingDisclosed_shape LowerLeaf msgVals msgSlots treeChild)
open ClaudeWCT.W9.T3.Security.LargeResidual (lookupVal EncRow)
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem case_digest (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, if st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X)) <$>
        readReq U ⟨X, hX⟩ .mass) ws) := by
  have hnp := LargeResidual.Paired.not_parsed_of_digest hd
  have hne : ¬EncRow X := by
    rintro ⟨L, m, ctr, pad, -, rfl⟩
    exact encRow_not_digest L m ctr pad hd
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp N' hu') (LargeResidual.Paired.not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), observed_readReq, observed_pure, map_pure]
  have h := continue_read hrel hlt X hX .mass (Or.inr ⟨rfl, hd⟩) hTX
    (fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2)
    (fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp N' hu'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne)
  have heq : (if st.Fresh X then { st.after X with births := (X, τ ⟨X, hX⟩) :: st.births } else st.after X) =
      st.next U X (τ ⟨X, hX⟩) := by
    unfold LargeResidual.RouterState.next
    by_cases hf : st.Fresh X
    · rw [if_pos hf, if_pos ⟨hX, hd, hf⟩]
    · rw [if_neg hf, if_neg (fun h' => hf h'.2.2)]
  rw [← heq] at h
  exact h
theorem case_other (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (hne : ¬EncRow X) (hnd : ¬IsDigestRow X) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call) ws) := by
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp N' hu') (LargeResidual.Paired.not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
  exact continue_read_call hrel hlt X hX hnd hTX (fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2)
    (fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp N' hu'))
    (fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne)
theorem routeQuery_observed (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (hok : FamOK st) (X : HashInput) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (observedRun aux q (Sum.elim vals nv) τ (routeQuerySelected U a st X) ws) := by
  unfold routeQuerySelected
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hN := Classical.choose_spec hp
      split
      · rename_i cs hfu
        exact case_unknownChild aux hcoh hrel hlt hq hok X hX _ hN.1 hN.2 cs hfu
      · rename_i hfu
        exact case_knownChildren aux hcoh hrel hlt X hX _ hN.1 hN.2 hfu
    · rw [dif_neg hp]
      by_cases he : EncRow X
      · rw [dif_pos he]
        have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec he)))
        exact case_enc_known aux hcoh hrel hlt X hX _ _ _ _ hspec.1 hspec.2
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd]
          exact case_digest aux hcoh hrel hlt X hX hd
        · rw [if_neg hd]
          exact case_other aux hcoh hrel hlt X hX hp he hd
  · rw [dif_neg hX]
    exact case_outside aux hcoh hrel hlt X hX

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

