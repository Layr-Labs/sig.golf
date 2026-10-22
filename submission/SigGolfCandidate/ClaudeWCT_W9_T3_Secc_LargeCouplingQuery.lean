import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeContactMonitor
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeCouplingObserved
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeCouplingSign
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeCouplingTrace
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsStructuralFinal
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingMatch
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTransportCount
import SigGolfCandidate.T3_Secc_WotsClasses
import SigGolfCandidate.T3_Secc_LargeCouplingQuery

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
  rw [h2, show Wots.encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker, digestHeader_marker] at hm
  exact absurd hm (by decide)
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
end Coherent
theorem encodingRow_parsed_none (L : Wots.LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : Wots.RowPad) :
    Extract.posOf (Wots.encRow L m c pad) = none :=
  Wots.Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
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
section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
end Reference
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
end Relation
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_of_not (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput)
    (h : ¬(X ∈ U ∧ IsDigestRow X)) : st.next U X y = st.after X := by
  unfold RouterState.next
  rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.next_disclosed (U : Finset HashInput)
    (st : RouterState) (X : HashInput) (y : HashOutput) : (st.next U X y).disclosed = st.disclosed := by
  unfold RouterState.next RouterState.after
  split_ifs <;> rfl
theorem encRow_not_digest (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad) :
    ¬IsDigestRow (Wots.encRow L.toWots m ctr pad) := by
  rintro ⟨rho, m', c, h⟩
  exact encRow_ne_digest' _ _ _ _ _ _ _ h
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
      (a.sel L).bind fun r => (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun d =>
        (BitVec.ofNat 32 r.1.val,d,WCT9.lowSelected L.1.lay (a.rows L r.1))
  priv : ∀c : Coordinate,(∀i : Fin 2,(c,i)∉Set.range secretCoordinate) → (∀m : Message,c≠.inr (.inl m)) →
    T (.inr c)=a.priv c
  outside : ∀X,X∉U → T (.inl (.inr X))=(0 : HashOutput)
  nonce : ∀m : Message,(T (.inr (.inr (.inl m)))).extractLsb' 0 128=nv m
  selected : a.sel=CanonEncoding.Paired.selectionsOfRows a.rows
  /-- Top-nonce layer: no top position exhausted its trial cap (`CapFail`, probability ≤ 2^-142). -/
  capOk : ¬ CanonGraph.CapFail (routerLabels vals a)

/-! ### Top-nonce layer helpers (r3-lean-nonsec, Subagent L) -/
theorem presentEquiv_base (M : CanonGraph.Node) :
    CanonGraph.Paired.presentEquiv M.base = CanonGraph.Paired.presentEquiv M := by
  cases M <;> rfl
theorem presentEquiv_toPos {M N : CanonGraph.Node} (h : M.toPos = N.toPos) :
    CanonGraph.Paired.presentEquiv M = CanonGraph.Paired.presentEquiv N := by
  rw [← presentEquiv_base M, ← presentEquiv_base N, CanonGraph.toPos_injective_base h]
/-- The node is not an over-cap tree node (`nonce ≥ trialCap`, a structural phantom with no slots). -/
def NoOver (M : CanonGraph.Node) : Prop := ∀ m, M = .node m → m.1.nonce.val < trialCap m.1.lay m.1.level.val
theorem noOver_of_not_phantom {L : Labels} {M : CanonGraph.Node} (h : ¬ PhantomAt M L) : NoOver M := by
  intro m hm
  subst hm
  by_contra hc
  exact h ⟨m, rfl, fun ha => hc ha.1⟩
theorem noOver_base (M : CanonGraph.Node) : NoOver M.base := by
  intro m hm
  cases M with
  | node n =>
    cases hm
    have := trialCap_pos n.1.lay n.1.level.val
    simp only [withNonce_lay, withNonce_level]
    rw [withNonce_nonce n (by norm_num)]
    exact this
  | _ => cases hm
theorem childSlots_base_of {M : CanonGraph.Node} (hM : NoOver M) : childSlots M.base = childSlots M := by
  cases M with
  | node m =>
    have h1 := hM m rfl
    have h0 := trialCap_pos m.1.lay m.1.level.val
    show LargeResidual.childSlots (.node (withNonce m 0)) = LargeResidual.childSlots (.node m)
    simp only [LargeResidual.childSlots]
    rw [if_neg (by simp only [withNonce_lay, withNonce_level]; rw [withNonce_nonce m (by norm_num)]; omega),
      if_neg (by omega)]
    rfl
  | _ => rfl
theorem childSlots_sub_base (M : CanonGraph.Node) : ∀ cs ∈ childSlots M, cs ∈ childSlots M.base := by
  intro cs hcs
  by_cases hM : NoOver M
  · rw [childSlots_base_of hM]; exact hcs
  · cases M with
    | node m =>
      have h1 : trialCap m.1.lay m.1.level.val ≤ m.1.nonce.val := by
        by_contra h; exact hM (fun m' hm' => by cases hm'; omega)
      change cs ∈ LargeResidual.childSlots (.node m) at hcs
      simp only [LargeResidual.childSlots] at hcs
      rw [if_pos h1] at hcs
      cases hcs
    | _ => exact hcs
theorem childSlots_eq_of {M N : CanonGraph.Node} (h : M.toPos = N.toPos) (hM : NoOver M) (hN : NoOver N) :
    childSlots M = childSlots N := by
  rw [← childSlots_base_of hM, ← childSlots_base_of hN, CanonGraph.toPos_injective_base h]
theorem cellDepsP_sub_base (M : CanonGraph.Node) : ∀ c ∈ cellDepsP M, c ∈ cellDepsP M.base := by
  intro c hc
  cases M with
  | node m =>
    change c ∈ LargeResidual.cellDeps (.node m) at hc
    change c ∈ LargeResidual.cellDeps (.node (withNonce m 0))
    unfold LargeResidual.cellDeps at hc ⊢
    simp only [List.mem_append] at hc ⊢
    rcases hc with ((hc | hc) | hc) | hc
    · obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
      exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨cs, childSlots_sub_base (.node m) cs hcs, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr hc))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  | _ => exact hc
theorem cellDepsP_sub {M N : CanonGraph.Node} (h : M.toPos = N.toPos) (hN : N.base = N) :
    ∀ c ∈ cellDepsP M, c ∈ cellDepsP N := by
  intro c hc
  have := cellDepsP_sub_base M c hc
  rwa [CanonGraph.toPos_injective_base h, hN] at this
theorem used_base {M : CanonGraph.Node} (hu : CanonGraph.Paired.Filtered.Used M) :
    CanonGraph.Paired.Filtered.Used M.base := by
  cases M <;> exact hu
theorem lay_zero_of_cap {lay : Layer} {level : Nat} (h : trialCap lay level ≠ 1) : lay = 0 := by
  unfold trialCap at h
  split_ifs at h with h'
  · exact h'.1
  · exact absurd rfl h
theorem treeNodeAt_spec {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {m : TreeNode}
    (h : treeNodeAt lay tree level c = some m) :
    m.1.lay = lay ∧ m.1.tree = tree ∧ m.1.level.val = level ∧ m.1.idx.val = c ∧ m.1.nonce.val = 0 := by
  unfold treeNodeAt at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
/-- A tree-node child coordinate of a slot list belongs to a tree node of the same layer and has nonce 0. -/
theorem childSlots_node_child {N : CanonGraph.Node} {cs : Coord × Nat} (hc : cs ∈ childSlots N) {m : TreeNode}
    (hm : cs.1 = .inl (.node m)) :
    ∃ n, N = .node n ∧ m.1.lay = n.1.lay ∧ m.1.level.val + 1 = n.1.level.val ∧ m.1.nonce.val = 0 := by
  obtain ⟨c, b⟩ := cs
  simp only at hm
  subst hm
  cases N with
  | node n =>
    refine ⟨n, rfl, ?_⟩
    simp only [childSlots, LargeResidual.childSlots] at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with ⟨x, hx, hxe, -⟩ | ⟨x, hx, hxe, -⟩ <;> subst hxe <;>
    · unfold treeChild at hx
      split_ifs at hx with h0
      · simp at hx
      · simp only [Option.map_eq_some_iff, Sum.inl.injEq, CanonGraph.Node.node.injEq] at hx
        obtain ⟨m', hm', rfl⟩ := hx
        obtain ⟨h1, -, h3, -, h5⟩ := treeNodeAt_spec hm'
        exact ⟨h1, by omega, h5⟩
  | chain p =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_singleton, Prod.mk.injEq] at hc
    unfold chainChild at hc
    split_ifs at hc <;> simp at hc
  | leaf L =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_map, Prod.mk.injEq] at hc
    obtain ⟨i, -, h, -⟩ := hc
    simp at h
  | wctChain p =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_singleton, Prod.mk.injEq] at hc
    have := hc.1
    unfold wctItem at this
    split_ifs at this <;> simp at this
  | wctLeaf L =>
    simp only [childSlots, List.mem_append, List.mem_ofFn, Option.mem_toList, Option.map_eq_some_iff,
      Prod.mk.injEq] at hc
    rcases hc with ⟨t, ht⟩ | ⟨x, hx, hxe, -⟩
    · have := ht.1
      unfold wctItem at this
      split_ifs at this <;> simp at this
    · subst hxe
      unfold padCoord ftsChild at hx
      split_ifs at hx <;> simp at hx
  | wctNode n =>
    simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with (⟨x, hx, hxe, -⟩ | ⟨x, hx, hxe, -⟩) | hc
    · subst hxe; unfold ftsChild at hx; split_ifs at hx <;> simp at hx
    · subst hxe; unfold ftsChild at hx; split_ifs at hx <;> simp at hx
    · split_ifs at hc
      · simp only [Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨x, hx, hxe, -⟩ := hc
        subst hxe; unfold padCoord ftsChild at hx; split_ifs at hx <;> simp at hx
      · simp at hc
  | forest index =>
    simp only [childSlots, LargeResidual.childSlots, List.mem_flatMap, List.mem_cons, List.mem_range,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    obtain ⟨i, -, h | h⟩ := hc <;> simp at h
theorem selCoordV_self_of {v : Coord → Digest} {c : Coord}
    (h : ∀ m : TreeNode, c = .inl (.node m) → trialCap m.1.lay m.1.level.val = 1 ∧ m.1.nonce.val = 0) :
    selCoordV v c = c := by
  rcases c with (_ | _ | m | _ | _ | _ | _) | s
  all_goals try rfl
  obtain ⟨h1, h0⟩ := h m rfl
  show Sum.inl (CanonGraph.Node.node (withNonce m (selNonceV v m))) = _
  rw [selNonceV_cap_one h1]
  have hw := withNonce_self m
  rw [h0] at hw
  rw [hw]
/-- Off the top tree, child slots are their own selected trials. -/
theorem selCoordV_child {v : Coord → Digest} {N : CanonGraph.Node}
    (hN : ∀ n, N = .node n → n.1.lay ≠ 0) {cs : Coord × Nat} (hc : cs ∈ childSlots N) :
    selCoordV v cs.1 = cs.1 := by
  apply selCoordV_self_of
  intro m hm
  obtain ⟨n, rfl, hl, -, h0⟩ := childSlots_node_child hc hm
  exact ⟨trialCap_lower (hl ▸ hN n rfl) _, h0⟩
/-- A node of a single-trial position equal to its base representative is its position's selected trial. -/
theorem sel_of_single {L : Labels} {N : CanonGraph.Node} (hb : N.base = N)
    (hN : ∀ n, N = .node n → trialCap n.1.lay n.1.level.val = 1) : N.sel L = N := by
  cases N with
  | node n =>
    have h0 : n.1.nonce.val = 0 := by
      have := congrArg (fun M => match M with | CanonGraph.Node.node m => m.1.nonce.val | _ => 0) hb
      simpa [CanonGraph.Node.base, withNonce] using this.symm
    exact congrArg CanonGraph.Node.node (selNode_of_cap_one (hN n rfl) h0)
  | _ => rfl
/-- Two non-phantom nodes of one single-trial position coincide (with the base representative). -/
theorem eq_of_single {L : Labels} {M N : CanonGraph.Node} (hb : N.base = N)
    (hN : ∀ n, N = .node n → trialCap n.1.lay n.1.level.val = 1) (hM : M.toPos = N.toPos)
    (hnp : ¬ PhantomAt M L) : M = N := by
  have hbase := CanonGraph.toPos_injective_base hM
  rw [hb] at hbase
  cases M with
  | node m =>
    subst hbase
    have ha : Active L m := by by_contra ha; exact hnp ⟨m, rfl, ha⟩
    have hcap := hN _ rfl
    have h0 : m.1.nonce.val = 0 := by
      have := ha.1
      simp only [CanonGraph.Node.base, withNonce_lay, withNonce_level] at hcap
      omega
    show CanonGraph.Node.node m = CanonGraph.Node.node (withNonce m 0)
    have hw := withNonce_self m
    rw [h0] at hw
    rw [hw]
  | _ => exact hbase
/-- Top-tree child slots are keygen coordinates. -/
theorem top_childSlots_keygen {n : TreeNode} (hl : n.1.lay = 0) {cs : Coord × Nat}
    (hc : cs ∈ childSlots (.node n)) : cs.1 ∈ keygenDisclosed := by
  have hv : n.1.level.val < height n.1.lay ∧ n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) ∧
      n.1.tree.val < 2 ^ treeBits n.1.lay ∧ (n.1.lay = 0 ∨ n.1.level.val + 1 < height n.1.lay) := n.2
  rw [hl] at hv
  have ht : n.1.tree = 0 := Fin.ext (by simpa [treeBits] using hv.2.2.1)
  have hh : height 0 = 12 := rfl
  rw [hh] at hv
  obtain ⟨c, b⟩ := cs
  simp only [childSlots, LargeResidual.childSlots] at hc
  split_ifs at hc
  · cases hc
  simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
  have key : ∀ k, k < 2 ^ (12 - n.1.level.val) → ∀ x, treeChild 0 0 n.1.level.val k = some x →
      x ∈ keygenDisclosed := by
    intro k hk x hx
    apply List.mem_append_left
    apply List.mem_append_left
    unfold keygenCacheDisclosed
    simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
    exact ⟨n.1.level.val, ⟨by omega, by omega⟩, k, hk, hx⟩
  have hpow : 2 ^ (12 - n.1.level.val) = 2 * 2 ^ (12 - n.1.level.val - 1) := by
    rw [← pow_succ']; congr 1; omega
  rcases hc with ⟨x, hx, rfl, -⟩ | ⟨x, hx, rfl, -⟩
  · rw [hl, ht] at hx; exact key _ (by omega) x hx
  · rw [hl, ht] at hx; exact key _ (by omega) x hx
theorem nonce_zero_of_base {n : TreeNode} (h : (CanonGraph.Node.node n).base = .node n) : n.1.nonce.val = 0 := by
  have := congrArg (fun M => match M with | CanonGraph.Node.node m => m.1.nonce.val | _ => 0) h
  simp only [CanonGraph.Node.base] at this
  rw [← this, withNonce_nonce n (by norm_num)]
theorem base_base (M : CanonGraph.Node) : M.base.base = M.base := by
  cases M <;> rfl
theorem trialDeps_keygen {n : TreeNode} {c : Coord} (hc : c ∈ trialDeps n) : c ∈ keygenDisclosed := by
  unfold trialDeps at hc
  split_ifs at hc with h1
  · simp at hc
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact trialCoord_mem_keygen (lay_zero_of_cap h1) h1 (List.mem_range.mp hj)
theorem childTrialDeps_keygen {lay : Layer} {tree : Fin (2^31)} {level k : Nat} {c : Coord}
    (hc : c ∈ childTrialDeps lay tree level k) : c ∈ keygenDisclosed := by
  unfold childTrialDeps at hc
  split at hc
  · exact trialDeps_keygen hc
  · simp at hc
theorem cellDepsP_known (st : RouterState) {N : CanonGraph.Node}
    (hall : ∀ cs ∈ childSlots N, RouterState.known st cs.1) : ∀ c ∈ cellDepsP N, RouterState.known st c := by
  intro c hc
  cases N with
  | node n =>
    simp only [cellDepsP, LargeResidual.cellDeps, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc; exact hall cs hcs
    · exact Known.base (Or.inl (trialDeps_keygen hc))
    · exact Known.base (Or.inl (childTrialDeps_keygen hc))
    · exact Known.base (Or.inl (childTrialDeps_keygen hc))
  | _ => obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc; exact hall cs hcs
theorem ne_phantom_of_length {X : HashInput} (h : X.length = 64) : ∀ n, X ≠ phantom n := by
  intro n hX
  have := phantom_length n
  rw [← hX, h] at this
  exact absurd this (by decide)

theorem rowPresent_parsed {X : HashInput} {N : CanonGraph.Node}
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) :
    rowPresent X=CanonGraph.Paired.presentEquiv N := by
  have hp : Parsed X := ⟨N,hu,hN⟩
  unfold rowPresent
  rw [dif_pos hp]
  have hc := (Classical.choose_spec hp).2
  exact presentEquiv_toPos (Option.some.inj (hc.symm.trans hN))

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

theorem selCoordV_coordVal_sel (s : Secrets) (L : Labels) (N : CanonGraph.Node) :
    selCoordV (coordVal s L) (.inl N) = .inl (N.sel L) := by
  cases N with
  | node n =>
    show Sum.inl (CanonGraph.Node.node (withNonce n (selNonceV (coordVal s L) n))) = _
    rw [selNonceV_coordVal]
    rfl
  | _ => rfl

theorem Coherent.selCoord (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    selCoordV vals (.inl N) = .inl (N.sel (routerLabels vals a)) := by
  have := selCoordV_coordVal_sel (secretsOf T) (routerLabels vals a) N
  rwa [h.coordVal] at this

/-- Top-nonce layer: the honest input of a position is the cell of its selected trial. -/
theorem Coherent.honestInput (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    Extract.Paired.honestInput T N.toPos=cellValues (N.sel (routerLabels vals a)) vals := by
  have hb := (CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu
  rw [CanonGraph.Paired.Filtered.honestInput_eq T (routerLabels vals a) h.agrees N hb,
    cell_eq_cellValues _ _ _ (CanonGraph.Paired.Filtered.used_sel _ N hb),h.coordVal]

theorem Coherent.honestValue_sel (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    honestValue T (.inl N)=Extract.Paired.proj N.toPos (routerLabels vals a (N.sel (routerLabels vals a))) := by
  change Extract.Paired.proj N.toPos (T (.inl (.inr (Extract.Paired.honestInput T N.toPos))))=_
  rw [CanonGraph.Paired.Filtered.honest_answer T (routerLabels vals a) h.agrees N
    ((CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu)]

/-- Top-nonce layer: the honest value of a position is the value of its selected trial. -/
theorem Coherent.honestValue_node (h : Coherent U T vals nv τ a) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) : honestValue T (.inl N)=vals (selCoordV vals (.inl N)) := by
  rw [h.honestValue_sel N hu, h.selCoord N, ← CanonGraph.toPos_sel (routerLabels vals a) N]
  exact CanonGraph.Paired.joinLabels_val _ _ _

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

theorem treeChild_ne_self (n : TreeNode) (c : Nat) :
    treeChild n.1.lay n.1.tree n.1.level.val c ≠ some (.inl (.node n)) := by
  intro h
  unfold treeChild at h
  split_ifs at h with h0
  · simp at h
  · simp only [Option.map_eq_some_iff, Sum.inl.injEq, CanonGraph.Node.node.injEq] at h
    obtain ⟨m, hm, rfl⟩ := h
    have := (treeNodeAt_spec hm).2.2.1
    omega

theorem childSlots_used (N : CanonGraph.Node) (hu : CanonGraph.Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : UsedCoord cs.1 := by
  by_cases hnode : ∃ n, N = .node n
  · obtain ⟨n, rfl⟩ := hnode
    obtain ⟨c,b⟩ := cs
    simp only [childSlots, LargeResidual.childSlots] at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with ⟨x, hx, rfl, -⟩ | ⟨x, hx, rfl, -⟩ <;>
    · unfold treeChild at hx
      split_ifs at hx
      · obtain ⟨L, -, rfl⟩ := Option.map_eq_some_iff.mp hx; trivial
      · obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hx; trivial
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
    have hnn : ∀ m, N = .node m → False := fun m hm => hnode ⟨m, hm⟩
    rw [slot_cellValues N (coordVal secrets left) (fun m hm => (hnn m hm).elim) (Sum.inl n,b) hc,
      slot_cellValues N (coordVal secrets right) (fun m hm => (hnn m hm).elim) (Sum.inl n,b) hc] at hs
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
    (h : Coherent U T vals nv τ a) (c : Coord) (hc : UsedCoord c) : honestValue T c=vals (selCoordV vals c) := by
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
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
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
  obtain ⟨hv,⟨ds,low⟩,hd⟩ := CanonEncoding.Paired.selectionAt_producer hr
  have hdec := (WCT9.CanonicalPolicy.producerDecodeAt_spec (WCT9.CanonicalPolicy.producerDecodeOut_spec hd).2).1
  rw [hv] at hdec
  exact ⟨ds,hdec⟩

theorem Coherent.referenceLow (h : Coherent U T vals nv τ a) (L : CanonEncoding.EncLeaf) :
    Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T) L.toWots =
      ((a.sel L).bind fun r => (WCT9.CanonicalPolicy.decode L.1.lay r.2).map fun _ =>
        WCT9.lowSelected L.1.lay (a.rows L r.1)).getD true := by
  unfold Wots.CanonicalRef.referenceLow
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases WCT9.CanonicalPolicy.decode L.1.lay r.2 <;> rfl

theorem Coherent.routerLows_eq (h : Coherent U T vals nv τ a) (L : Wots.LeafAddr)
    (hL : ∃L' : CanonEncoding.EncLeaf,L'.toWots=L) :
    routerLows a L=Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T) L := by
  unfold routerLows
  rw [dif_pos hL]
  have hs := Classical.choose_spec hL
  have hlay : (Classical.choose hL).1.lay=L.lay := congrArg Wots.LeafAddr.lay hs
  conv_rhs => rw [←hs]
  rw [h.referenceLow,hlay]
  cases hsel : a.sel (Classical.choose hL) with
  | none => rfl
  | some r =>
      obtain ⟨ds,hd⟩ := h.sel_valid _ hsel
      have hd' : WCT9.CanonicalPolicy.decode L.lay r.2 = some ds := by rw [← hlay]; exact hd
      simp only [Option.map_some, Option.bind_some, hd, hd', Option.getD_some]

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

theorem Coherent.canDecode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf)
    (hs : (a.sel L).isSome) (y : HashOutput) :
    WCT9.encodingCanDecode L.1.lay y
      (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) L.toWots) ↔
      WCT9.encodingTarget L.1.lay (refDigest a L) y = refDigest a L :=
  WCT9.encodingCanDecode_iff_target _ _ _ _ ((h.decode_ref L hs _).mpr rfl)

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
  Finset.univ.filter fun a =>
    (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed
theorem mem_DiscLower (st : RouterState) (L : LowerLeaf) (a : ChainGraph.Address) :
    a ∈ DiscLower st L ↔
      (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧ (.inr (.inl a) : Coord) ∈ st.disclosed := by
  unfold DiscLower
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- No seed family is determined by the router's disclosures: FTS families have at most 53 disclosed seeds, WOTS
leaf families at most `famCount − 1` (structurally at most `famCount − 3`: 14 lower, `lower_zero_count_le`; 21 top of
31 coefficients, `top_zero_count_le`, campaign T51). -/
def FamOK (st : RouterState) : Prop :=
  (∀ f, (DiscSeeds st f).card ≤ 53) ∧ ∀ L : LowerLeaf, (DiscLower st L).card ≤ WCT9.famSize L.1.1 L.1.2.2.val - 1
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
  rcases LargeResidual.mem_keygenDisclosed.mp hc with hc | hc | hc
  rotate_left
  · rcases encodingDisclosed_shape hc with ⟨n, rfl⟩ | ⟨i, rfl⟩ <;> exact ⟨_, rfl⟩
  · obtain ⟨n, rfl⟩ := LargeResidual.topTrialsDisclosed_shape hc; exact ⟨_, rfl⟩
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨level, _, node, _, h⟩ := hc
    unfold treeChild at h
    split_ifs at h
    · obtain ⟨L, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
    · obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨_, rfl⟩
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
  by_cases hnode : ∃ n, N = .node n
  · obtain ⟨n, rfl⟩ := hnode
    obtain ⟨c,b⟩ := cs
    dsimp only at he
    subst c
    simp only [childSlots, LargeResidual.childSlots] at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    rcases hc with ⟨x, hx, hxe, -⟩ | ⟨x, hx, hxe, -⟩ <;> subst hxe <;> exact treeChild_ne_self n _ hx
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
  have hnn : ∀ m, N = .node m → False := fun m hm => hnode ⟨m, hm⟩
  rw [slot_cellValues N (coordVal secrets left) (fun m hm => (hnn m hm).elim) (Sum.inl N,b) hc,
    slot_cellValues N (coordVal secrets right) (fun m hm => (hnn m hm).elim) (Sum.inl N,b) hc] at hs
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
    (hu : CanonGraph.Paired.Filtered.Used N) (hN : Extract.posOf X=some N.toPos) (hN0 : NoOver N) :
    ContactTest A K X y ↔
      (∃cs,firstUnknown K N=some cs ∧ slotValue X cs.2=honestValue A cs.1) ∨
        (X≠Extract.Paired.honestInput A N.toPos ∧ Extract.Paired.proj N.toPos y=honestValue A (.inl N)) := by
  constructor
  · rintro (⟨N',_,hN',h⟩ | ⟨L,m,c,pad,_,hX,_⟩)
    · rw [hN] at hN'
      have he : N'.toPos = N.toPos := (Option.some.inj hN').symm
      have hv : honestValue A (.inl N') = honestValue A (.inl N) := by
        change Extract.Paired.proj N'.toPos _ = Extract.Paired.proj N.toPos _
        rw [he]
      by_cases hov : NoOver N'
      · have hfu : firstUnknown K N' = firstUnknown K N := by
          unfold firstUnknown; rw [childSlots_eq_of he hov hN0]
        rw [hfu, hv, he] at h
        exact h
      · have h0 : childSlots N' = [] := by
          cases N' with
          | node m =>
            have h1 : trialCap m.1.lay m.1.level.val ≤ m.1.nonce.val := by
              by_contra h2; exact hov (fun m' hm' => by cases hm'; omega)
            change LargeResidual.childSlots (.node m) = []
            simp only [LargeResidual.childSlots]; rw [if_pos h1]
          | _ => exact absurd (fun m' hm' => by cases hm') hov
        rcases h with ⟨cs, hcs, -⟩ | h
        · unfold firstUnknown at hcs; rw [h0] at hcs; cases hcs
        · rw [hv, he] at h; exact Or.inr h
    · rw [hX,encodingRow_parsed_none] at hN;cases hN
  · intro h
    exact Or.inl ⟨N,(CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu,hN,h⟩

theorem contactTest_enc {A : Answers} {K : Coord→Prop} {y : HashOutput} {L : EncLeaf} {m : WCT9.LayerMsg}
    {c : BitVec 32} {pad : Wots.RowPad} (hfit : Extract.msgFits L.1.lay m) :
    ContactTest A K (Wots.encRow L.toWots m c pad) y ↔
      Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L.toWots≠none ∧
      Wots.CanonicalRef.referenceInput A (Wots.CanonicalRef.sourceMessages A) L.toWots≠some (Wots.encRow L.toWots m c pad) ∧
      Wots.CanonicalRef.NotSearched A (Wots.CanonicalRef.sourceMessages A) L.toWots (Wots.encRow L.toWots m c pad) ∧
      WCT9.encodingCanDecode L.1.lay y
        (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) L.toWots) := by
  constructor
  · rintro (⟨N',_,hN',_⟩ | ⟨L',m',c',pad',_,hX,h⟩)
    · rw [encodingRow_parsed_none] at hN';cases hN'
    · obtain ⟨rfl,_⟩ := encRow_encLeaf hX
      exact h
  · intro h;exact Or.inr ⟨L,m,c,pad,hfit,rfl,h⟩

theorem not_parsed_of_encRow {X : HashInput} (he : LargeResidual.EncRow X) : ¬Parsed X := by
  rintro ⟨N,_,hN⟩
  exact ClaudeWCT.W9.T3.Security.LargeCoupling.not_parsed_of_encRow he ⟨N,hN⟩
theorem not_parsed_of_digest {X : HashInput} (hd : SigGolfCandidate.T3.Security.LargeResidual.IsDigestRow X) :
    ¬Parsed X := by
  rintro ⟨N,_,hN⟩
  exact ClaudeWCT.W9.T3.Security.LargeCoupling.not_parsed_of_digest hd ⟨N,hN⟩
theorem contactTest_other {A : Answers} {K : Coord→Prop} {X : HashInput} {y : HashOutput}
    (hp : ¬Parsed X) (he : ¬LargeResidual.EncRow X) : ¬ContactTest A K X y := by
  rintro (⟨N,hu,hN,_⟩ | ⟨L,m,c,pad,hfit,hX,_⟩)
  · exact hp ⟨N,(CanonGraph.Paired.Filtered.used_iff_bounded N).2 hu,hN⟩
  · exact he ⟨L,m,c,pad,hfit,hX⟩

section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord→Digest} {nv : Message→Digest}
  {τ : Cell U→HashOutput} {a : AuxData}

/-- A cell decoding to the position of `N` is the cell of a non-phantom node of that position. -/
theorem Coherent.cell_pos (h : Coherent U T vals nv τ a) {X : HashInput} {N M : CanonGraph.Node}
    (hN : Extract.posOf X=some N.toPos) (hu : CanonGraph.Paired.Filtered.Used M) (heq : X=cellValues M vals) :
    M.toPos=N.toPos ∧ ¬PhantomAt M (routerLabels vals a) :=
  CanonGraph.Paired.cell_eq_of_posOf (secretsOf T) (routerLabels vals a) hN (heq.trans (h.cell M hu).symm)

theorem Coherent.not_cell_parsed (h : Coherent U T vals nv τ a) {X : HashInput} {N : CanonGraph.Node}
    (hN : Extract.posOf X=some N.toPos)
    (hne : ∀M,CanonGraph.Paired.Filtered.Used M → M.toPos=N.toPos → X≠cellValues M vals) :
    ∀N',CanonGraph.Paired.Filtered.Used N' → X≠cellValues N' vals := by
  intro N' hu heq
  exact hne N' hu (h.cell_pos hN hu heq).1 heq

theorem not_cell_unparsed (h : Coherent U T vals nv τ a) {X : HashInput} (hp : ¬Parsed X)
    (hph : ∀ n, X ≠ phantom n) :
    ∀N',CanonGraph.Paired.Filtered.Used N' → X≠cellValues N' vals := by
  intro N' hu heq
  have hc : X = CanonGraph.Paired.cell (secretsOf T) N' (routerLabels vals a) := heq.trans (h.cell N' hu).symm
  by_cases hphA : PhantomAt N' (routerLabels vals a)
  · obtain ⟨n, rfl, hn⟩ := hphA
    apply hph n
    rw [hc, CanonGraph.Paired.cell_node]
    exact cell_node_inactive hn
  · exact hp ⟨N',hu,by rw [hc]; exact CanonGraph.Paired.posOf_cell _ _ _ hphA⟩

theorem Coherent.activeV_iff (h : Coherent U T vals nv τ a) (n : TreeNode) :
    LargeResidual.ActiveV vals n ↔ Active (routerLabels vals a) n := by
  have := activeV_coordVal (secretsOf T) (routerLabels vals a) n
  rwa [h.coordVal] at this

/-- A phantom input is the cell of exactly its own (inactive) tree node. -/
theorem Coherent.cell_phantom (h : Coherent U T vals nv τ a) {N' : CanonGraph.Node} {n : TreeNode}
    (hu : CanonGraph.Paired.Filtered.Used N') (heq : phantom n = cellValues N' vals) :
    N' = .node n ∧ ¬ Active (routerLabels vals a) n := by
  have hc : phantom n = CanonGraph.Paired.cell (secretsOf T) N' (routerLabels vals a) := heq.trans (h.cell N' hu).symm
  by_cases hphA : PhantomAt N' (routerLabels vals a)
  · obtain ⟨m, rfl, hm⟩ := hphA
    rw [CanonGraph.Paired.cell_node, cell_node_inactive hm] at hc
    have := phantom_injective hc
    subst this
    exact ⟨rfl, hm⟩
  · have := CanonGraph.Paired.posOf_cell (secretsOf T) N' (routerLabels vals a) hphA
    rw [← hc, posOf_phantom] at this
    cases this

theorem not_prefix_parsed {X : HashInput} (hp : Parsed X) : ¬HonestPrefix vals a X := by
  rintro ⟨L,ctr,rfl,_⟩
  exact not_parsed_of_encRow ⟨L,_,ctr,0,LargeCoupling.msgFits_msgVals vals L,rfl⟩ hp
theorem not_prefix_enc {X : HashInput} (he : ¬LargeResidual.EncRow X) : ¬HonestPrefix vals a X := by
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
    (hN : Extract.posOf X = some N.toPos) (hbN : N.base = N) (cs : Coord × Nat)
    (hfu : firstUnknown (LargeResidual.Paired.RouterState.known st) N = some cs) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩) ws) := by
  obtain ⟨hcsm, hcsk⟩ := LargeResidual.Paired.firstUnknown_some hfu
  have hlow : ∀ n, N = .node n → n.1.lay ≠ 0 := by
    intro n hn hl
    subst hn
    exact hcsk (Known.base (Or.inl (LargeResidual.Paired.top_childSlots_keygen hl hcsm)))
  have hcap1 : ∀ n, N = .node n → trialCap n.1.lay n.1.level.val = 1 := fun n hn => trialCap_lower (hlow n hn) _
  have hsel : N.sel (routerLabels vals a) = N := LargeResidual.Paired.sel_of_single hbN hcap1
  have hvN : honestValue T (.inl N) = vals (.inl N) := by rw [hcoh.honestValue_node N hu, hcoh.selCoord N, hsel]
  have hiN : Extract.Paired.honestInput T N.toPos = cellValues N vals := by rw [hcoh.honestInput N hu, hsel]
  have hchild : ∀ cs ∈ childSlots N, honestValue T cs.1 = vals cs.1 := fun cs hc => by
    rw [hcoh.honestValue_used cs.1 (LargeResidual.Paired.childSlots_used N hu cs hc),
      LargeResidual.Paired.selCoordV_child hlow hc]
  have hne' : X ≠ cellValues N vals → ∀ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M →
      M.toPos = N.toPos → X ≠ cellValues M vals := fun hXc M hMu hMpos heq =>
    hXc (by rw [LargeResidual.Paired.eq_of_single hbN hcap1 hMpos (hcoh.cell_pos hN hMu heq).2] at heq; exact heq)
  have hNact : ∀ n, N = .node n → LargeResidual.ActiveV vals n ∧ ∀ cs ∈ childSlots N, vals (LargeResidual.selCoordV vals cs.1) = vals cs.1 := by
    intro n hn
    refine ⟨⟨?_, fun j hj => ?_⟩, fun cs hc => by rw [LargeResidual.Paired.selCoordV_child hlow hc]⟩
    · rw [hcap1 n hn]; subst hn; rw [LargeResidual.Paired.nonce_zero_of_base hbN]; omega
    · subst hn; rw [LargeResidual.Paired.nonce_zero_of_base hbN] at hj; exact absurd hj (by omega)
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
    rw [LargeResidual.Paired.contactTest_parsed hu hN (hbN ▸ LargeResidual.Paired.noOver_base N), hvN, hiN]
    constructor
    · rintro (⟨cs', hcs', h⟩ | h)
      · rw [hfu] at hcs'
        cases hcs'
        exact Or.inl (by simpa only [hchild cs hcsm] using h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨cs,hfu,by simpa only [hchild cs hcsm] using h⟩
      · exact Or.inr h
  have hres : X ≠ cellValues N vals → T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) := fun hXc =>
    hcoh.residual X hX (fun N' hu' => by rw [hcoh.cell N' hu']; exact hcoh.not_cell_parsed hN (hne' hXc) N' hu') (LargeResidual.Paired.not_prefix_parsed hp)
  have hcell : X ≠ cellValues N vals → ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals →
      ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 := fun hXc N' hu' hN' => absurd hN' (hcoh.not_cell_parsed hN (hne' hXc) N' hu')
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
        exact slot_cellValues N vals hNact cs hcsm
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
    (hN : Extract.posOf X = some N.toPos) (hbN : N.base = N)
    (hfu : firstUnknown (LargeResidual.Paired.RouterState.known st) N = none) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U (cellDepsP N)
      if X = cellFrom (cellNode N (lookupVal pairs) X) (lookupVal pairs) then do
        let v ← discloseReq U (.inl (.inl (cellNode N (lookupVal pairs) X))) .call
        pure (CanonGraph.Paired.presentEquiv (cellNode N (lookupVal pairs) X)
          (ChainGraph.joinOutput v (a.high (cellNode N (lookupVal pairs) X))), st.after X)
      else (fun y => (rowPresent X y, st.after X)) <$>
        testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ ⟨none, .label (.inl (LargeResidual.selCoordV (lookupVal pairs) (.inl N)))⟩) ws) := by
  have hall := LargeResidual.Paired.firstUnknown_none hfu
  have hp : Parsed X := ⟨N,hu,hN⟩
  have hnd : ¬IsDigestRow X := fun hd => LargeResidual.Paired.not_parsed_of_digest hd hp
  have hN0 : LargeResidual.Paired.NoOver N := hbN ▸ LargeResidual.Paired.noOver_base N
  have hkN : ∀ M : CanonGraph.Node, M.toPos = N.toPos → LargeResidual.Paired.NoOver M →
      (LargeResidual.Paired.RouterState.known st) (.inl M) :=
    fun M hM hM0 => Known.node (by rw [LargeResidual.Paired.childSlots_eq_of hM hM0 hN0]; exact hall)
  have hkc : ∀ c ∈ cellDepsP N, (LargeResidual.Paired.RouterState.known st) c :=
    LargeResidual.Paired.cellDepsP_known st hall
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hv0c : ∀ c ∈ cellDepsP N,
      lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c))) c = vals c :=
    fun c hc => lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ c hc
  have hcf : ∀ M : CanonGraph.Node, M.toPos = N.toPos →
      cellFrom M (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) = cellValues M vals := by
    intro M hM
    change cellValues M _ = cellValues M vals
    apply cellValues_congr
    intro c hc
    exact hv0c c (LargeResidual.Paired.cellDepsP_sub hM hbN c hc)
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 := fun L ctr hL => absurd hL (LargeResidual.Paired.not_enc_parsed hp L _ ctr 0 (msgFits_msgVals vals L))
  obtain hex | hex := Classical.em (∃ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M ∧ M.toPos = N.toPos ∧
      X = cellFrom M (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))))
  · have hM := Classical.choose_spec hex
    have hcn : cellNode N (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) X =
        Classical.choose hex := by
      unfold cellNode; exact @dif_pos _ _ hex _ _ _
    rw [hcn]
    obtain ⟨hMu, hMpos, hMX⟩ := hM
    rw [if_pos hMX, observed_discloseReq, observed_pure]
    have hXc : X = cellValues (Classical.choose hex) vals := hMX.trans (hcf _ hMpos)
    have hTX : T (.inl (.inr X)) = routerLabels vals a (Classical.choose hex) := by
      have h1 := hcoh.honest_answer _ hMu
      rwa [← hXc] at h1
    have hnp : ¬PhantomAt (Classical.choose hex) (routerLabels vals a) := (hcoh.cell_pos hN hMu hXc).2
    have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
      rintro ⟨-, -, hc⟩
      rw [LargeResidual.Paired.contactTest_parsed hu hN hN0, hfu] at hc
      rcases hc with ⟨cs, hcs, -⟩ | ⟨hne, hval⟩
      · cases hcs
      · by_cases hMs : Classical.choose hex = N.sel (routerLabels vals a)
        · apply hne
          rw [hcoh.honestInput N hu, ← hMs, ← hXc]
        · apply hcoh.capOk
          refine CanonGraph.rejected_hit_capFail hMpos hnp hMs ?_
          rw [hTX, hcoh.honestValue_sel N hu] at hval
          exact hval
    apply outcome_continue hrel hlt X _ hnc
    · rw [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hTX]
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
        (.inl (.inl (Classical.choose hex))) {Sum.elim vals nv (.inl (.inl (Classical.choose hex)))} c
      by_cases hc : c = .inl (.inl (Classical.choose hex))
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl (Classical.choose hex)))
          {Sum.elim vals nv (.inl (.inl (Classical.choose hex)))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN _ hMpos (LargeResidual.Paired.noOver_of_not_phantom hnp)))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hu' hN'
      rw [LargeResidual.Paired.childSlots_eq_of (hcoh.cell_pos hN hu' hN').1
        (LargeResidual.Paired.noOver_of_not_phantom (hcoh.cell_pos hN hu' hN').2) hN0]
      exact hall
    · exact fun _ => henc
  · have hcn : cellNode N (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) X = N := by
      unfold cellNode; exact @dif_neg _ _ hex _ _ _
    rw [hcn]
    have hXN : ¬ X = cellFrom N (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) :=
      fun h => hex ⟨N, hu, rfl, h⟩
    rw [if_neg hXN]
    have hsc : LargeResidual.selCoordV (lookupVal ((cellDepsP N).map fun c => (c, Sum.elim vals nv (.inl c)))) (.inl N) =
        .inl (N.sel (routerLabels vals a)) := by
      rw [← hcoh.selCoord N]
      apply LargeResidual.selCoordV_congr
      intro n hn h1 j hj
      have hN' : N = .node n := Sum.inl.inj hn
      subst hN'
      exact hv0c _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (LargeResidual.mem_trialDeps h1 hj))))
    rw [hsc]
    have hSu : CanonGraph.Paired.Filtered.Used (N.sel (routerLabels vals a)) :=
      (CanonGraph.Paired.Filtered.used_iff_bounded _).2 (by
        rw [CanonGraph.toPos_sel]; exact (CanonGraph.Paired.Filtered.used_iff_bounded N).1 hu)
    have hne' : ∀ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M → M.toPos = N.toPos → X ≠ cellValues M vals :=
      fun M hMu hMpos h => hex ⟨M, hMu, hMpos, h.trans (hcf M hMpos).symm⟩
    have hTX : T (.inl (.inr X)) = rowPresent X (τ ⟨X, hX⟩) :=
      hcoh.residual X hX (fun N' hu' => by rw [hcoh.cell N' hu']; exact hcoh.not_cell_parsed hN hne' N' hu') (LargeResidual.Paired.not_prefix_parsed hp)
    have hct : ∀ y : HashOutput, ContactTest T (LargeResidual.Paired.RouterState.known st) X y ↔
        Extract.Paired.proj N.toPos y = vals (.inl (N.sel (routerLabels vals a))) := by
      intro y
      rw [LargeResidual.Paired.contactTest_parsed hu hN hN0, hcoh.honestValue_node N hu, hcoh.selCoord N, hfu]
      simp only [reduceCtorEq, false_and, exists_false, false_or]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [hcoh.honestInput N hu]
        exact hne' _ hSu (CanonGraph.toPos_sel _ N)
    have hcell : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals → ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 :=
      fun N' hu' hN' => absurd hN' (hcoh.not_cell_parsed hN hne' N' hu')
    have hfresh : X ∉ st.seen → (discloseStates U q (Sum.elim vals nv) ws (cellDepsP N)).rows ⟨X, hX⟩ = none :=
      hrel1.fresh X hX hnd
    have hcomp := observed_testReqP (U := U) (q := q) (vals := vals) (nv := nv) (τ := τ) (st := st)
      (ws := discloseStates U q (Sum.elim vals nv) ws (cellDepsP N)) aux
      (rowPresent X) (st.after X) X hX ⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ hfresh
    refine queryOutcome_congr hcomp ?_
    rw [effF_self _ _ (by intro g hg; cases hg)]
    have hadm : ∀ g ∈ (⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ : Probe WCoord).guess, ∀ parent,
        (⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ : Probe WCoord).hit = Hit.label parent → g.1 ≠ parent := by
      intro g hg; cases hg
    by_cases hs : X ∈ st.seen
    · rw [if_neg (not_not.mpr hs)]
      exact continue_read_callP (rowPresent X) hrel1 hlt X hX hnd hTX (fun h => h.1 hs) hcell henc
    · rw [if_pos hs]
      by_cases hk : (⟨none, .label (.inl (.inl (N.sel (routerLabels vals a))))⟩ : Probe WCoord).keep (Sum.elim vals nv) (τ ⟨X, hX⟩)
      · rw [if_pos hk]
        have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) := by
          rintro ⟨-, -, hc⟩
          rw [hct, hTX, LargeResidual.Paired.proj_rowPresent hu hN] at hc
          exact ((keep_label (Sum.elim vals nv) _ _).mp hk) hc.symm
        exact continue_probeP (rowPresent X) hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
      · rw [if_neg hk]
        refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ?_⟩ rfl
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
theorem case_phantom (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws)
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (n : TreeNode) (hXn : X = phantom n) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (do
      let pairs ← discloseAll U (LargeResidual.trialDeps n)
      if LargeResidual.ActiveV (lookupVal pairs) n then (fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call
      else do
        let v ← discloseReq U (.inl (.inl (.node n))) .call
        pure (CanonGraph.Paired.presentEquiv (.node n) (ChainGraph.joinOutput v (a.high (.node n))), st.after X)) ws) := by
  have hlen : X.length ≠ 64 := by rw [hXn, phantom_length]; decide
  have hne : ¬LargeResidual.EncRow X := by
    rintro ⟨L, m, ctr, pad, -, rfl⟩
    exact hlen (ClaudeWCT.W9.T3.Security.Wots.Enc.encRow_length _ _ _ _)
  have hnd : ¬IsDigestRow X := by
    rintro ⟨rho, m, c, hd⟩
    apply hlen
    rw [hd, Cost.pad64_length]
    simp [digestInput, SphincsSecurity.bytesLE_length]
  have hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T (LargeResidual.Paired.RouterState.known st) X (T (.inl (.inr X)))) :=
    fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2
  have hkc : ∀ c ∈ LargeResidual.trialDeps n, (LargeResidual.Paired.RouterState.known st) c :=
    fun c hc => Known.base (Or.inl (LargeResidual.Paired.trialDeps_keygen hc))
  have hrel1 := hrel.discloseStates _ hkc
  rw [observed_discloseAll]
  have hact : LargeResidual.ActiveV (lookupVal ((LargeResidual.trialDeps n).map fun c => (c, Sum.elim vals nv (.inl c)))) n ↔ LargeResidual.ActiveV vals n :=
    LargeResidual.activeV_congr (fun h1 j hj => lookupVal_map (fun c => Sum.elim vals nv (.inl c)) _ _ (LargeResidual.mem_trialDeps h1 hj))
  have henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encRow L.toWots (msgVals vals L) ctr 0 →
      ∀ cs ∈ msgSlots L, (LargeResidual.Paired.RouterState.known st) cs.1 :=
    fun L' ctr' hL' => absurd ⟨L', _, ctr', 0, msgFits_msgVals vals L', hL'⟩ hne
  by_cases ha : LargeResidual.ActiveV vals n
  · rw [if_pos (hact.mpr ha)]
    have hnot : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X ≠ cellValues N' vals := by
      intro N' hu' heq
      obtain ⟨rfl, hn⟩ := hcoh.cell_phantom hu' (hXn.symm.trans heq)
      exact hn ((hcoh.activeV_iff n).mp ha)
    have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
      hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact hnot N' hu')
        (LargeResidual.Paired.not_prefix_enc hne)
    rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    exact continue_read_call hrel1 hlt X hX hnd hTX hnc (fun N' hu' hN' => absurd hN' (hnot N' hu')) henc
  · rw [if_neg (fun h => ha (hact.mp h)), observed_discloseReq, observed_pure]
    have hXc : X = cellValues (.node n) vals := by
      rw [hXn]
      show phantom n = LargeResidual.cellValues (.node n) vals
      simp only [LargeResidual.cellValues, if_neg ha]
    have hTX : T (.inl (.inr X)) = routerLabels vals a (.node n) := by
      rw [hXc]; exact hcoh.honest_answer _ trivial
    have hslots : ∀ cs ∈ childSlots (.node n), (LargeResidual.Paired.RouterState.known st) cs.1 := by
      intro cs hcs
      by_cases hov : trialCap n.1.lay n.1.level.val ≤ n.1.nonce.val
      · simp [childSlots, LargeResidual.childSlots, hov] at hcs
      · have h1 : trialCap n.1.lay n.1.level.val ≠ 1 := by
          intro h1
          apply ha
          refine ⟨by omega, fun j hj => ?_⟩
          rw [h1] at hov; exact absurd hj (by omega)
        exact Known.base (Or.inl (LargeResidual.Paired.top_childSlots_keygen (LargeResidual.Paired.lay_zero_of_cap h1) hcs))
    have hkN : (LargeResidual.Paired.RouterState.known st) (.inl (.node n)) := Known.node hslots
    apply outcome_continue hrel hlt X _ hnc
    · rw [LargeResidual.RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
      congr 3
      rw [hTX]
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
        (.inl (.inl (.node n))) {Sum.elim vals nv (.inl (.inl (.node n)))} c
      by_cases hc : c = .inl (.inl (.node n))
      · subst hc
        rw [Function.update_self]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hc]
        exact hrel1.mem c
    · intro c hck
      show 2 ^ 128 - (discloseStates U q (Sum.elim vals nv) ws _).counters.probes ≤
        (Function.update (discloseStates U q (Sum.elim vals nv) ws _).candidates (.inl (.inl (.node n)))
          {Sum.elim vals nv (.inl (.inl (.node n)))} (.inl c)).card
      rw [Function.update_of_ne (fun h => hck (by rw [Sum.inl.inj h]; exact hkN))]
      exact hrel1.hidden c hck
    · intro row v hv
      exact hrel1.rowsEq row v hv
    · intro row v hv
      exact Or.inr (hrel1.rowsSeen row v hv)
    · intro _ N' hu' hN'
      obtain ⟨rfl, -⟩ := hcoh.cell_phantom hu' (hXn.symm.trans hN')
      exact hslots
    · exact fun _ => henc

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
  have hph : ∀ n, X ≠ phantom n :=
    LargeResidual.Paired.ne_phantom_of_length (by rw [hXe]; exact ClaudeWCT.W9.T3.Security.Wots.Enc.encRow_length _ _ _ _)
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
        Wots.CanonicalRef.NotSearched T (Wots.CanonicalRef.sourceMessages T) L.toWots X ∧
        WCT9.encodingTarget L.1.lay (refDigest a L) y=refDigest a L := by
    intro y
    rw [hXe,LargeResidual.Paired.contactTest_enc hfit,←hXe]
    have hs : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots≠none ↔
        (a.sel L).isSome := by
      rw [←Option.isSome_iff_ne_none,hcoh.search_isSome]
    rw [hs]
    constructor
    · rintro ⟨hsel,hi,hns,hd⟩
      exact ⟨hsel,hi,hns,(hcoh.canDecode_ref L hsel _).mp hd⟩
    · rintro ⟨hsel,hi,hns,hd⟩
      exact ⟨hsel,hi,hns,(hcoh.canDecode_ref L hsel _).mpr hd⟩
  have hcell : ∀ N' : CanonGraph.Node, CanonGraph.Paired.Filtered.Used N' → X = cellValues N' vals → ∀ cs ∈ childSlots N', (LargeResidual.Paired.RouterState.known st) cs.1 :=
    fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu')
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
      -- A searched honest row is never an encoding contact (path-aware floors: see `NotSearched`).
      rintro ⟨-, -, hc⟩
      rw [hct] at hc
      obtain ⟨hsel, -, hns, -⟩ := hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsel
      obtain ⟨ds, hd⟩ := hcoh.sel_valid L hr
      have hfound : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots =
          some (BitVec.ofNat 32 r.1.val, ds, WCT9.lowSelected L.1.lay (a.rows L r.1)) := by
        rw [hcoh.search, hr]
        simp only [Option.bind_some, hd, Option.map_some]
      have hle : ctr.toNat ≤ (BitVec.ofNat 32 r.1.val).toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := r.1.isLt; omega)]
        exact hpre.2.2.2 r hr
      have hctr : BitVec.ofNat 32 ctr.toNat = ctr := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt ctr.isLt
      apply hns _ hfound ctr.toNat hle
      rw [hpre.1, hcoh.leafMsg L, hctr]
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
      hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu')
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
            exact ((keep_encodingHit (Sum.elim vals nv) _ _ _).mp hk) hc.2.2.2.symm
          exact continue_probe hrel1 hlt X hX _ hk hadm hTX hnd hnc hcell henc
        · rw [if_neg hk]
          have hns : Wots.CanonicalRef.NotSearched T (Wots.CanonicalRef.sourceMessages T) L.toWots X := by
            intro found hfound c hc heq
            apply hpre
            obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsel
            obtain ⟨ds, hd⟩ := hcoh.sel_valid L hr
            have hfound' : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) L.toWots =
                some (BitVec.ofNat 32 r.1.val, ds, WCT9.lowSelected L.1.lay (a.rows L r.1)) := by
              rw [hcoh.search, hr]
              simp only [Option.bind_some, hd, Option.map_some]
            rw [hfound'] at hfound
            cases hfound
            have hr1 : (BitVec.ofNat 32 r.1.val).toNat = r.1.val := by
              rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := r.1.isLt; omega)
            rw [hr1] at hc
            rw [hXe] at heq
            have hc' := (encRow_encLeaf heq).2
            obtain ⟨remaining, hctx, hselAt⟩ := hcoh.sel_context L hr
            have hcap := (capSel_eq_some.mp hselAt).2
            have hctrc : ctr.toNat = c := by
              rw [hc', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := r.1.isLt; omega)
            refine ⟨?_, by rw [hctx]; rfl, by omega, fun r' hr' => ?_⟩
            · rw [hXe, heq, hcoh.leafMsg L, hc']
            · rw [hr] at hr'; cases hr'; omega
          refine outcome_stop hrel1 hlt X _ ⟨hs, hX, (hct _).mpr ⟨hsel,hri,hns,?_⟩⟩ rfl
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
  have hph : ∀ n, X ≠ phantom n := by
    obtain ⟨rho, m, c, hdX⟩ := hd
    exact LargeResidual.Paired.ne_phantom_of_length (by
      rw [hdX, Cost.pad64_length]; simp [digestInput, SphincsSecurity.bytesLE_length])
  have hne : ¬LargeResidual.EncRow X := by
    rintro ⟨L, m, ctr, pad, -, rfl⟩
    exact encRow_not_digest L m ctr pad hd
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu') (LargeResidual.Paired.not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), observed_readReq, observed_pure, map_pure]
  have h := continue_read hrel hlt X hX .mass (Or.inr ⟨rfl, hd⟩) hTX
    (fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2)
    (fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu'))
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
    (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U) (hnp : ¬Parsed X) (hne : ¬LargeResidual.EncRow X) (hnd : ¬IsDigestRow X)
    (hph : ∀ n, X ≠ phantom n) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ
      ((fun y => (y, st.after X)) <$> readReq U ⟨X, hX⟩ .call) ws) := by
  have hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩ :=
    hcoh.residual_unparsed X hX hnp (fun N' hu' => by rw [hcoh.cell N' hu']; exact LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu') (LargeResidual.Paired.not_prefix_enc hne)
  rw [observed_map, ← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
  exact continue_read_call hrel hlt X hX hnd hTX (fun h => LargeResidual.Paired.contactTest_other hnp hne h.2.2)
    (fun N' hu' hN' => absurd hN' (LargeResidual.Paired.not_cell_unparsed hcoh hnp hph N' hu'))
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
      have hu : CanonGraph.Paired.Filtered.Used (Classical.choose hp).base := LargeResidual.Paired.used_base hN.1
      have hpos : Extract.posOf X = some (Classical.choose hp).base.toPos := by
        rw [CanonGraph.toPos_base]; exact hN.2
      split
      · rename_i cs hfu
        exact case_unknownChild aux hcoh hrel hlt hq hok X hX _ hu hpos (LargeResidual.Paired.base_base _) cs hfu
      · rename_i hfu
        exact case_knownChildren aux hcoh hrel hlt X hX _ hu hpos (LargeResidual.Paired.base_base _) hfu
    · rw [dif_neg hp]
      by_cases hph : ∃ n : TreeNode, X = phantom n
      · rw [dif_pos hph]
        exact case_phantom aux hcoh hrel hlt X hX hp _ (Classical.choose_spec hph)
      rw [dif_neg hph]
      by_cases he : LargeResidual.EncRow X
      · rw [dif_pos he]
        have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec he)))
        exact case_enc_known aux hcoh hrel hlt X hX _ _ _ _ hspec.1 hspec.2
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd]
          exact case_digest aux hcoh hrel hlt X hX hd
        · rw [if_neg hd]
          exact case_other aux hcoh hrel hlt X hX hp he hd (fun n h => hph ⟨n, h⟩)
  · rw [dif_neg hX]
    exact case_outside aux hcoh hrel hlt X hX

end Cases
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

