import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingResample
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMaskBase
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeResidualRouter
import SigGolfCandidate.ClaudeWCT_W9_New_Positions_FtsBridge
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsExtractWord
import SigGolfCandidate.T3_Secc_LargeCouplingSign

section
namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue slotValue_pad64 slotValue_block4
  chainRow_block4 slotValue_listInput width_ge chainCount_pos slotValue_bytes_cons slotValue_shift)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem merkleNodeInputN_eq_block4 (lay tree heap n : Nat) (left right : Digest) :
    WCT9.merkleNodeInputN lay tree heap n left right =
      block4 left (WCT9.merkleTweak lay tree heap) (WCT9.nonceDigest n) right := rfl
theorem mem_cellDeps_of_slot {N : CanonGraph.Node} {cs : Coord × Nat} (h : cs ∈ childSlots N) :
    cs.1 ∈ cellDeps N := by
  have hm : cs.1 ∈ (childSlots N).map Prod.fst := List.mem_map.mpr ⟨cs, h, rfl⟩
  cases N with
  | node n => exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm))
  | _ => exact hm
/-- A tree child reads its selected trial: agreement on the child slot and on the child position's trials. -/
theorem treeChild_sel_agree {v w : Coord → Digest} {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {x : Coord}
    (hx : treeChild lay tree level c = some x) (h0 : v x = w x)
    (hd : ∀ y ∈ childTrialDeps lay tree level c, v y = w y) : v (selCoordV v x) = w (selCoordV v x) := by
  have hx' := hx
  unfold treeChild at hx
  split_ifs at hx
  · obtain ⟨L, -, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact h0
  · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
    simp only [selCoordV]
    by_cases h1 : trialCap m.1.lay m.1.level.val = 1
    · rw [selNonceV_cap_one h1]
      have hw := withNonce_self m
      rw [treeNodeAt_nonce hm] at hw
      rw [hw]; exact h0
    · apply hd
      unfold childTrialDeps
      rw [hx']
      exact mem_trialDeps h1 (selNonceV_lt v m)
theorem cellFrom_eq (N : CanonGraph.Node) (v : Coord → Digest) : cellFrom N v = cellValues N v := rfl
theorem cellValues_congr (N : CanonGraph.Node) (v v' : Coord → Digest)
    (hdep : ∀ c ∈ cellDeps N, v c = v' c) : cellValues N v = cellValues N v' := by
  have h : ∀ cs ∈ childSlots N, v cs.1 = v' cs.1 := fun cs hcs => hdep cs.1 (mem_cellDeps_of_slot hcs)
  cases N with
  | chain p =>
      have := h (chainChild p, if WCT9.isG p.1.layer p.1.chain.val then 0 else 3) (by simp [childSlots])
      simp only [cellValues, this]
  | leaf L =>
      simp only [cellValues]
      congr 2
      exact List.map_congr_left (fun i hi => h _ (by simp only [childSlots, List.mem_map]; exact ⟨i, hi, rfl⟩))
  | node n =>
      have hl : ∀ c ∈ childTrialDeps n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val), v c = v' c := fun c hc =>
        hdep c (List.mem_append_left _ (List.mem_append_right _ hc))
      have hr : ∀ c ∈ childTrialDeps n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1), v c = v' c := fun c hc =>
        hdep c (List.mem_append_right _ hc)
      have ht : ∀ c ∈ trialDeps n, v c = v' c := fun c hc =>
        hdep c (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hc)))
      have ha : ActiveV v n ↔ ActiveV v' n := activeV_congr (fun h1 j hj => ht _ (mem_trialDeps h1 hj))
      by_cases hav : ActiveV v n
      · have hlt : ¬ trialCap n.1.lay n.1.level.val ≤ n.1.nonce.val := by have := hav.1; omega
        have e1 : treeVal v n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val) =
            treeVal v' n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val) := by
          apply treeVal_congr _ _ _ _ _ hl
          intro x hx
          have hx' : treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val) = some x := by simpa using hx
          exact treeChild_sel_agree hx' (h (x, 0) (by simp [childSlots, hx', hlt])) hl
        have e2 : treeVal v n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1) =
            treeVal v' n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1) := by
          apply treeVal_congr _ _ _ _ _ hr
          intro x hx
          have hx' : treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1) = some x := by simpa using hx
          exact treeChild_sel_agree hx' (h (x, 3) (by simp [childSlots, hx', hlt])) hr
        simp only [cellValues]
        rw [e1, e2, if_pos hav, if_pos (ha.mp hav)]
      · simp only [cellValues]
        rw [if_neg hav, if_neg (fun h' => hav (ha.mpr h'))]
  | wctChain p =>
      have := h (wctItem p.1 p.2.val, if WCT9.ftsIsG p.1.2.2.2.val then 0 else 3) (by simp [childSlots])
      simp only [cellValues, this]
  | wctLeaf L =>
      have hfg : (fun t : Fin 6 => v (wctItem (L.index, L.coord, L.child, t) 4)) =
          fun t : Fin 6 => v' (wctItem (L.index, L.coord, L.child, t) 4) := by
        funext t
        exact h (wctItem (L.index, L.coord, L.child, t) 4, ftsLeafSlot t.val) (by
          simp only [childSlots]
          exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨t, rfl⟩))
      have hp : ((prevTop L.index L.coord 0).map v).getD 0 = ((prevTop L.index L.coord 0).map v').getD 0 := by
        cases hc : prevTop L.index L.coord 0 with
        | none => rfl
        | some c =>
            have := h (c, 2) (by simp [childSlots, hc])
            simp [this]
      simp only [cellValues, prevVals]
      rw [hfg, hp]
  | wctNode n =>
      simp only [cellValues]
      have h1 : ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0 =
          ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v').getD 0 := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val) with
        | none => rfl
        | some c =>
            have := h (c, 0) (by simp [childSlots, hc])
            simp [this]
      have h2 : ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0 =
          ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v').getD 0 := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1) with
        | none => rfl
        | some c =>
            have := h (c, 3) (by simp [childSlots, hc])
            simp [this]
      have h3 : (if n.1.level.val = 5 then (prevVals v n.1.index n.1.coord).2 else 0) =
          (if n.1.level.val = 5 then (prevVals v' n.1.index n.1.coord).2 else 0) := by
        split_ifs with hl
        · unfold prevVals
          cases hc : prevTop n.1.index n.1.coord 1 with
          | none => rfl
          | some c =>
              have := h (c, 2) (by simp [childSlots, hc, hl])
              simp [this]
        · rfl
      rw [h1, h2, h3]
  | forest index =>
      simp only [cellValues]
      congr 2
      refine List.map_congr_left (fun c hc => ?_)
      have e0 := h (.inl (.wctNode (ftsTopNode index (fin9 c) 0)), 2 + 2 * c) (by
          simp only [childSlots, List.mem_flatMap]
          exact ⟨c, hc, List.mem_cons_self⟩)
      have e1 := h (.inl (.wctNode (ftsTopNode index (fin9 c) 1)), 3 + 2 * c) (by
          simp only [childSlots, List.mem_flatMap]
          exact ⟨c, hc, List.mem_cons_of_mem _ List.mem_cons_self⟩)
      simp only at e0 e1
      rw [e0, e1]
theorem slotValue_listOf (hdr : BitVec 128) (values : List Digest) (i : Nat) (hi : i < values.length) :
    slotValue (pad64 (Extract.listInput (values.getD 0 0) hdr (values.drop 1))) (listBlock i) =
      values.getD i 0 := by
  have key := slotValue_listInput (values.getD 0 0) hdr (values.drop 1) i (by simp; omega)
  have hcons : values.getD 0 0 :: values.drop 1 = values := by
    cases values with
    | nil => simp at hi
    | cons x xs => rfl
  rw [hcons] at key
  exact key
/-- Slot of FTS end `i` in the padded FTS leaf `end0 | hdr | 0 | end1..end5` (campaign T8; large route, A5 pending:
not compiled on t8/int). -/
theorem slotValue_ftsLeaf (hdr : BitVec 128) (values : List Digest) (i : Nat) (hi : i < values.length) :
    slotValue (pad64 (Extract.listInput (values.getD 0 0) hdr (0 :: values.drop 1))) (ftsLeafSlot i) =
      values.getD i 0 := by
  have key := slotValue_listInput (values.getD 0 0) hdr (0 :: values.drop 1) (if i = 0 then 0 else i + 1)
    (by split <;> simp <;> omega)
  have hb : listBlock (if i = 0 then 0 else i + 1) = ftsLeafSlot i := by
    unfold listBlock ftsLeafSlot; split <;> simp_all
  rw [hb] at key
  refine key.trans ?_
  cases values with
  | nil => simp at hi
  | cons x xs =>
      rcases i with _ | i
      · rfl
      · simp only [List.getD_cons_succ, List.drop_succ_cons, List.drop_zero, if_neg (Nat.succ_ne_zero _)]
theorem slotValue_ftsLeafP (hdr : BitVec 128) (p : Digest) (values : List Digest) (i : Nat)
    (hi : i < values.length) :
    slotValue (pad64 (Extract.listInput (values.getD 0 0) hdr (p :: values.drop 1))) (ftsLeafSlot i) =
      values.getD i 0 := by
  have key := slotValue_listInput (values.getD 0 0) hdr (p :: values.drop 1) (if i = 0 then 0 else i + 1)
    (by split <;> simp <;> omega)
  have hb : listBlock (if i = 0 then 0 else i + 1) = ftsLeafSlot i := by
    unfold listBlock ftsLeafSlot; split <;> simp_all
  rw [hb] at key
  refine key.trans ?_
  cases values with
  | nil => simp at hi
  | cons x xs =>
      rcases i with _ | i
      · rfl
      · simp only [List.getD_cons_succ, List.drop_succ_cons, List.drop_zero, if_neg (Nat.succ_ne_zero _)]
theorem slotValue_ftsLeaf_pad (hdr : BitVec 128) (p : Digest) (values : List Digest) :
    slotValue (pad64 (Extract.listInput (values.getD 0 0) hdr (p :: values.drop 1))) 2 = p :=
  slotValue_listInput (values.getD 0 0) hdr (p :: values.drop 1) 1 (by simp)
theorem slotValue_leafInput (lay : Layer) (tree leaf : Nat) (values : List Digest) (i : Nat) (hi : i < values.length) :
    slotValue (pad64 (Extract.leafInput lay tree leaf values)) (leafBlock lay i) = values.getD i 0 := by
  unfold Extract.leafInput SigGolfCandidate.T3.leafInput leafBlock
  rw [ite_self, ite_self]
  exact slotValue_listOf (leafTweak lay tree leaf) values i hi

theorem slotValue_pairs (pairs : List (Digest × Digest)) :
    ∀ c, c < pairs.length →
      slotValue (pairs.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) (2 * c) = (pairs.getD c (0, 0)).1 ∧
      slotValue (pairs.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) (2 * c + 1) = (pairs.getD c (0, 0)).2 := by
  induction pairs with
  | nil => intro c hc; simp at hc
  | cons p ps ih =>
      intro c hc
      have hl : ∀ x : Digest, (bytesLE 16 x).length = 16 := fun x => bytesLE_length 16 x
      simp only [List.flatMap_cons, List.append_assoc]
      rcases c with _ | c
      · refine ⟨?_, ?_⟩
        · exact slotValue_bytes_cons p.1 _
        · rw [Nat.mul_zero, Nat.zero_add, show (1 : Nat) = 0 + 1 from rfl, slotValue_shift _ _ 0 (hl p.1)]
          exact slotValue_bytes_cons p.2 _
      · have hc' : c < ps.length := by simp at hc; omega
        obtain ⟨h1, h2⟩ := ih c hc'
        refine ⟨?_, ?_⟩
        · rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, slotValue_shift _ _ _ (hl p.1),
            show 2 * c + 1 = 2 * c + 0 + 1 by ring, slotValue_shift _ _ _ (hl p.2), Nat.add_zero, h1]
          rfl
        · rw [show 2 * (c + 1) + 1 = 2 * c + 1 + 1 + 1 by ring, slotValue_shift _ _ _ (hl p.1),
            slotValue_shift _ _ _ (hl p.2), h2]
          rfl
theorem slotValue_forest (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) (c : Nat)
    (hc : c < 9) :
    slotValue (pad64 (Extract.forestInput index pairs)) (2 + 2 * c) = (pairs.getD c (0, 0)).1 ∧
      slotValue (pad64 (Extract.forestInput index pairs)) (3 + 2 * c) = (pairs.getD c (0, 0)).2 := by
  have hflen := WCT9.forestInput_length index pairs hlen
  have hl16 : zero16.length = 16 := by simp [zero16]
  have hl : ∀ x : BitVec 128, (bytesLE 16 x).length = 16 := fun x => bytesLE_length 16 x
  obtain ⟨h1, h2⟩ := slotValue_pairs pairs c (by omega)
  refine ⟨?_, ?_⟩
  · rw [slotValue_pad64 _ _ (by rw [Extract.forestInput, hflen]; omega)]
    unfold Extract.forestInput WCT9.forestInput
    rw [List.append_assoc, show 2 + 2 * c = 2 * c + 1 + 1 by ring, slotValue_shift _ _ _ hl16,
      slotValue_shift _ _ _ (hl _)]
    exact h1
  · rw [slotValue_pad64 _ _ (by rw [Extract.forestInput, hflen]; omega)]
    unfold Extract.forestInput WCT9.forestInput
    rw [List.append_assoc, show 3 + 2 * c = 2 * c + 1 + 1 + 1 by ring, slotValue_shift _ _ _ hl16,
      slotValue_shift _ _ _ (hl _)]
    exact h2
/-- Slots of a cell. Tree nodes (top-nonce layer): the node must be an active trial whose child slots are their own
selected trials (always true off the top tree). -/
theorem slot_cellValues (N : CanonGraph.Node) (v : Coord → Digest)
    (hN : ∀ n, N = .node n → ActiveV v n ∧ ∀ cs ∈ childSlots N, v (selCoordV v cs.1) = v cs.1) :
    ∀ cs ∈ childSlots N, slotValue (cellValues N v) cs.2 = v cs.1 := by
  intro cs hcs
  cases N with
  | chain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      simp only [cellValues, CanonGraph.rowW]
      have hb : ∀ (x : Digest) (h : BitVec 128),
          bytesLE 16 x ++ bytesLE 16 h ++ zero16 ++ zero16 = block4 x h 0 0 := by
        intro x h; simp only [block4, show zero16 = bytesLE 16 (0 : Digest) by decide]
      cases hG : WCT9.isG p.1.layer p.1.chain.val
      · rw [WCT9.chainInputW_F hG, show SigGolfCandidate.T3.chainInput p.1.layer p.1.tree.val p.1.leaf.val
          p.1.chain.val p.2.val (v (chainChild p)) = ChainGraph.row p (v (chainChild p)) from rfl, chainRow_block4]
        exact (slotValue_block4 _ _ _ _).2.2
      · rw [WCT9.chainInputW_G hG, hb]
        exact (slotValue_block4 _ _ _ _).1
  | leaf L =>
      simp only [childSlots, List.mem_map, List.mem_range] at hcs
      obtain ⟨i, hi, rfl⟩ := hcs
      simp only [cellValues]
      rw [slotValue_leafInput _ _ _ _ _ (by simpa using hi)]
      simp [hi]
  | node n =>
      obtain ⟨ha, hsel⟩ := hN n rfl
      have hcs' := hcs
      have hlt : ¬ trialCap n.1.lay n.1.level.val ≤ n.1.nonce.val := by have := ha.1; omega
      simp only [childSlots, if_neg hlt, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      simp only [cellValues, if_pos ha, merkleNodeInputN_eq_block4, pad64_block4]
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · refine ((slotValue_block4 _ _ _ _).1).trans ?_
        unfold treeVal; rw [hc]; exact hsel _ hcs'
      · refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        unfold treeVal; rw [hc]; exact hsel _ hcs'
  | wctChain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      have hb : ∀ (x : Digest) (h : BitVec 128),
          bytesLE 16 x ++ bytesLE 16 h ++ zero16 ++ zero16 = block4 x h 0 0 := by
        intro x h; simp only [block4, show zero16 = bytesLE 16 (0 : Digest) by decide]
      simp only [cellValues]
      cases hG : WCT9.ftsIsG p.1.2.2.2.val
      · simp only [hG, Bool.false_eq_true, if_false]
        rw [WCT9.ftsChainInputW_F hG, Extract.wctChainInput_block4]
        exact (slotValue_block4 _ _ _ _).2.2
      · simp only [hG, if_true]
        rw [WCT9.ftsChainInputW_G hG, hb]
        exact (slotValue_block4 _ _ _ _).1
  | wctLeaf L =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with hcs | hcs
      · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hcs
        simp only [cellValues, Extract.wctLeafInputP]
        rw [slotValue_ftsLeafP _ _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues, Extract.wctLeafInputP]
        rw [slotValue_ftsLeaf_pad]
        unfold prevVals; rw [hc]; rfl
  | wctNode n =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with (hcs | hcs) | hcs
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues, nodeInputP, pad64_block4]
        refine ((slotValue_block4 _ _ _ _).1).trans ?_
        rw [hc]; rfl
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues, nodeInputP, pad64_block4]
        refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        rw [hc]; rfl
      · split_ifs at hcs with hl
        · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
          obtain ⟨c, hc, rfl⟩ := hcs
          simp only [cellValues, nodeInputP, pad64_block4, if_pos hl]
          refine ((slotValue_block4 _ _ _ _).2.1).trans ?_
          unfold prevVals; rw [hc]; rfl
        · simp at hcs
  | forest index =>
      simp only [childSlots, List.mem_flatMap, List.mem_range] at hcs
      obtain ⟨c, hc, hmem⟩ := hcs
      have hf := slotValue_forest index.val ((List.range 9).map fun c =>
        (v (.inl (.wctNode (ftsTopNode index (fin9 c) 0))), v (.inl (.wctNode (ftsTopNode index (fin9 c) 1)))))
        (by simp) c hc
      simp only [List.getD_eq_getElem _ _ (show c < ((List.range 9).map fun c =>
        (v (.inl (.wctNode (ftsTopNode index (fin9 c) 0))), v (.inl (.wctNode (ftsTopNode index (fin9 c) 1))))).length
          by simpa using hc), List.getElem_map, List.getElem_range] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hf.1
      · exact hf.2
end ClaudeWCT.W9.T3.Security.LargeResidual
end
section
namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafValue honestPieces)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr filterMap_map_getD)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.keygen ClaudeWCT.WCT9.heapBuild
noncomputable local instance instDecidableEqCache_w9largeCouplingSign : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem treeChild_isSome (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hl : level ≤ height lay)
    (hc : c < 2 ^ (height lay - level)) (ht : tree.val < 2 ^ treeBits lay) (hroot : lay = 0 ∨ level < height lay) :
    (treeChild lay tree level c).isSome := by
  unfold treeChild
  by_cases h0 : level = 0
  · subst h0
    rw [if_pos rfl]
    unfold leafAt
    rw [dif_pos ⟨by simpa using hc, ht⟩]
    rfl
  · rw [if_neg h0]
    unfold treeNodeAt
    rw [dif_pos ⟨by omega, by
      have : height lay - (level - 1) - 1 = height lay - level := by omega
      rw [this]; exact hc, ht, hroot.imp id (fun h => by omega)⟩]
    rfl
end ClaudeWCT.W9.T3.Security.LargeResidual
end

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue slotValue_block4 slotValue_pad64 chainRow_block4 width_ge)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def coordVal (s : Secrets) (L : Labels) : Coord → Digest
  | .inl M => Extract.Paired.proj M.toPos (L M)
  | .inr x => seedView s x

theorem trialFailsV_coordVal (s : Secrets) (L : Labels) (n : TreeNode) (j : Nat) :
    trialFailsV (coordVal s L) n j ↔ trialFails L n j := by
  unfold trialFailsV trialFails trialCoord
  show topZeroOk _ (Extract.Paired.proj (Node.node (withNonce n j)).toPos (L (.node (withNonce n j)))) = false ↔ _
  rw [CanonGraph.Paired.pairedProj_node]
  rfl
theorem selNonceV_coordVal (s : Secrets) (L : Labels) (n : TreeNode) : selNonceV (coordVal s L) n = selNonce L n := by
  unfold selNonceV selNonce
  congr 1
  apply find?_congr'
  intro j _
  simp only [decide_eq_decide.mpr (trialFailsV_coordVal s L n j)]
theorem activeV_coordVal (s : Secrets) (L : Labels) (n : TreeNode) : ActiveV (coordVal s L) n ↔ Active L n := by
  unfold ActiveV Active
  simp only [trialFailsV_coordVal]
/-- The value of a tree-node coordinate's selected trial is the label of the selected trial node. -/
theorem coordVal_selCoordV_node (s : Secrets) (L : Labels) (n : TreeNode) :
    coordVal s L (selCoordV (coordVal s L) (.inl (.node n))) =
      (Node.node n).toPos.proj (L (.node (selNode L n))) := by
  show Extract.Paired.proj (Node.node (withNonce n (selNonceV (coordVal s L) n))).toPos _ = _
  rw [CanonGraph.Paired.pairedProj_node, selNonceV_coordVal]
  rfl
theorem treeLabel_eq (s : Secrets) (L : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel L lay tree level c=treeVal (coordVal s L) lay tree level c := by
  unfold treeLabel treeVal treeChild
  by_cases h0 : level=0
  · rw [if_pos h0,if_pos h0]
    -- C2 (#866): `treeLabel` reads a lower leaf through `Pos.proj`, the paired `coordVal` through
    -- `Extract.Paired.proj`; they agree on the lower trees (`CanonGraph.Paired.pairedProj_leaf`).
    cases leafAt lay tree c with
    | none => rfl
    | some leaf => exact (congrFun (CanonGraph.Paired.pairedProj_leaf leaf) (L (.leaf leaf))).symm
  · rw [if_neg h0,if_neg h0]
    cases treeNodeAt lay tree (level-1) c with
    | none => rfl
    | some n => exact (coordVal_selCoordV_node s L n).symm

theorem ftsLabel_eq (s : Secrets) (L : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    CanonGraph.Paired.ftsLabel L index coord level c=((ftsChild index coord level c).map (coordVal s L)).getD 0 := by
  unfold CanonGraph.Paired.ftsLabel ftsChild
  by_cases h0 : level=0
  · rw [if_pos h0,if_pos h0]
    split_ifs <;> rfl
  · rw [if_neg h0,if_neg h0]
    cases hn : ftsNodeAt index coord (level-1) c with
    | none => rfl
    | some n =>
      simp only [Option.map_some,Option.getD_some,coordVal,CanonGraph.Node.toPos,
        ftsNodeAt_coord hn,ftsNodeAt_level hn]
      have hi : n.1.index=index := by
        unfold ftsNodeAt at hn
        split_ifs at hn
        cases hn
        rfl
      -- C1: the projection of an FTS node depends on its node index (`highNodeAt`), so the label's
      -- position index `c` must be identified with the node's own index.
      have hc : n.1.idx.val=c := by
        unfold ftsNodeAt at hn
        split_ifs at hn
        cases hn
        rfl
      rw [hi,hc]

theorem pads_eq (s : Secrets) (L : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) :
    CanonGraph.Paired.pads L index coord branch=padVals (coordVal s L) index coord branch := by
  unfold CanonGraph.Paired.pads padVals padCoord
  split_ifs with hz ho
  · rfl
  all_goals
    dsimp only
    rw [ftsLabel_eq s,ftsLabel_eq s]
    simp only [Fin.val_zero,Fin.val_one,Nat.add_zero]

theorem coordVal_wctItem (s : Secrets) (L : Labels) (a : WctAddr) (p : Nat) :
    coordVal s L (wctItem a p)=wctValueL s L a p := by
  unfold wctItem wctValueL
  split_ifs
  · rfl
  · simp only [coordVal]
    cases hh : WCT9.ftsChainHigh a.2.2.2.val ((p - 1) % 4) <;>
      simp [CanonGraph.Node.toPos, Extract.Pos.proj, Extract.Paired.proj, hh, projHalf_true, projHalf_false]

theorem cell_eq_cellValues (s : Secrets) (L : Labels) (N : CanonGraph.Node)
    (hu : CanonGraph.Paired.Filtered.Used N) :
    CanonGraph.Paired.cell s N L=cellValues N (coordVal s L) := by
  cases N with
  | chain p =>
      change CanonGraph.rowW p (CanonGraph.priorW (seedsOf s) p (chainLabels L))=CanonGraph.rowW p _
      congr 1
      unfold CanonGraph.priorW chainChild
      by_cases h0 : p.2.val=0
      · rw [if_pos h0,if_pos h0]; rfl
      · rw [if_neg h0,if_neg h0]
        -- C3 + pairing stage 1: a chain step reads the half `chainHigh` of its predecessor's label.
        simp only [coordVal]
        rw [CanonGraph.Paired.pairedProj_chain]
        rfl
  | leaf Lf =>
      change pad64 (Extract.leafInput _ _ _ ((List.range (chainCount Lf.1.lay)).map (endLabel s L Lf.1)))=_
      congr 3
      -- C3 (#866): the leaf reads the used half (`Pos.proj`) of its chains' last-step labels.
      all_goals
        funext i
        unfold endLabel
        exact (congrFun (CanonGraph.Paired.pairedProj_chain (endPt Lf.1 i)) (L (.chain (endPt Lf.1 i)))).symm
  | node n =>
      show CanonGraph.cell s (.node n) L = LargeResidual.cellValues (.node n) (coordVal s L)
      simp only [CanonGraph.cell, LargeResidual.cellValues]
      rw [treeLabel_eq s,treeLabel_eq s]
      by_cases ha : Active L n
      · rw [if_pos ha, if_pos ((activeV_coordVal s L n).mpr ha)]
      · rw [if_neg ha, if_neg (fun h => ha ((activeV_coordVal s L n).mp h))]
  | wctChain p =>
      change WCT9.ftsChainInputW _ _ _ _ _ (wctValueL s L p.1 p.2.val)=_
      rw [←coordVal_wctItem]
      rfl
  | wctLeaf Lf =>
      change pad64 (Extract.wctLeafInputP _ _ _ (CanonGraph.Paired.pads L Lf.index Lf.coord (Lf.child.val%2)).1
        (List.ofFn fun t : Fin 6 => wctEndLabel L (Lf.index,Lf.coord,Lf.child,t)))=_
      rw [pads_eq s L]
      simp only [cellValues,coordVal_wctItem,wctValueL_three]
  | wctNode n =>
      change pad64 (nodeInputP 3 _ _ _ (CanonGraph.Paired.ftsLabel L _ _ _ _)
        (if n.1.level.val=4 then (CanonGraph.Paired.pads L n.1.index n.1.coord (n.1.idx.val/2)).2 else 0)
        (CanonGraph.Paired.ftsLabel L _ _ _ _))=_
      rw [ftsLabel_eq s,ftsLabel_eq s,pads_eq s L]
      rfl
  | forest i => exact hu.elim

theorem cellValues_congr (N : CanonGraph.Node) (v v' : Coord → Digest)
    (hdep : ∀ c ∈ cellDepsP N, v c = v' c) : cellValues N v = cellValues N v' := by
  have h : ∀ cs ∈ childSlots N, v cs.1 = v' cs.1 := by
    intro cs hcs
    apply hdep
    cases N with
    | node n => exact LargeResidual.mem_cellDeps_of_slot (N := .node n) hcs
    | _ => exact List.mem_map.mpr ⟨cs, hcs, rfl⟩
  cases N with
  | chain p => exact LargeResidual.cellValues_congr (.chain p) v v' hdep

  | leaf L => exact LargeResidual.cellValues_congr (.leaf L) v v' hdep

  | node n => exact LargeResidual.cellValues_congr (.node n) v v' hdep

  | wctChain p => exact LargeResidual.cellValues_congr (.wctChain p) v v' hdep

  | wctLeaf L =>
      have hfg : (fun t : Fin 6 => v (wctItem (L.index, L.coord, L.child, t) 4)) =
          fun t : Fin 6 => v' (wctItem (L.index, L.coord, L.child, t) 4) := by
        funext t
        exact h (wctItem (L.index, L.coord, L.child, t) 4, ftsLeafSlot t.val) (by
          simp only [childSlots]
          exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨t, rfl⟩))
      have hp : ((padCoord L.index L.coord (L.child.val%2) 0).map v).getD 0 = ((padCoord L.index L.coord (L.child.val%2) 0).map v').getD 0 := by
        cases hc : padCoord L.index L.coord (L.child.val%2) 0 with
        | none => rfl
        | some c =>
            have := h (c, 2) (by simp [childSlots, hc])
            simp [this]
      simp only [cellValues, padVals]
      rw [hfg, hp]
  | wctNode n =>
      simp only [cellValues]
      have h1 : ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0 =
          ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v').getD 0 := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val) with
        | none => rfl
        | some c =>
            have := h (c, 0) (by simp [childSlots, hc])
            simp [this]
      have h2 : ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0 =
          ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v').getD 0 := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1) with
        | none => rfl
        | some c =>
            have := h (c, 3) (by simp [childSlots, hc])
            simp [this]
      have h3 : (if n.1.level.val = 4 then (padVals v n.1.index n.1.coord (n.1.idx.val/2)).2 else 0) =
          (if n.1.level.val = 4 then (padVals v' n.1.index n.1.coord (n.1.idx.val/2)).2 else 0) := by
        split_ifs with hl
        · unfold padVals
          cases hc : padCoord n.1.index n.1.coord (n.1.idx.val/2) 1 with
          | none => rfl
          | some c =>
              have := h (c, 2) (by simp [childSlots, hc, hl])
              simp [this]
        · rfl
      rw [h1, h2, h3]
  | forest index => exact LargeResidual.cellValues_congr (.forest index) v v' hdep

theorem slot_cellValues (N : CanonGraph.Node) (v : Coord → Digest)
    (hN : ∀ n, N = .node n → ActiveV v n ∧ ∀ cs ∈ childSlots N, v (selCoordV v cs.1) = v cs.1) :
    ∀ cs ∈ childSlots N, slotValue (cellValues N v) cs.2 = v cs.1 := by
  intro cs hcs
  cases N with
  | chain p => exact LargeResidual.slot_cellValues (.chain p) v (fun _ h => by cases h) cs hcs

  | leaf L => exact LargeResidual.slot_cellValues (.leaf L) v (fun _ h => by cases h) cs hcs

  | node n => exact LargeResidual.slot_cellValues (.node n) v hN cs hcs

  | wctChain p => exact LargeResidual.slot_cellValues (.wctChain p) v (fun _ h => by cases h) cs hcs

  | wctLeaf L =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with hcs | hcs
      · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hcs
        simp only [cellValues, Extract.wctLeafInputP]
        rw [LargeResidual.slotValue_ftsLeafP _ _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues, Extract.wctLeafInputP]
        rw [LargeResidual.slotValue_ftsLeaf_pad]
        unfold padVals; rw [hc]; rfl
  | wctNode n =>
      simp only [childSlots, List.mem_append] at hcs
      rcases hcs with (hcs | hcs) | hcs
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues, nodeInputP, pad64_block4]
        refine ((slotValue_block4 _ _ _ _).1).trans ?_
        rw [hc]; rfl
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
        obtain ⟨c, hc, rfl⟩ := hcs
        simp only [cellValues, nodeInputP, pad64_block4]
        refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        rw [hc]; rfl
      · split_ifs at hcs with hl
        · simp only [Option.mem_toList, Option.map_eq_some_iff] at hcs
          obtain ⟨c, hc, rfl⟩ := hcs
          simp only [cellValues, nodeInputP, pad64_block4, if_pos hl]
          refine ((slotValue_block4 _ _ _ _).2.1).trans ?_
          unfold padVals; rw [hc]; rfl
        · simp at hcs
  | forest index => exact LargeResidual.slot_cellValues (.forest index) v (fun _ h => by cases h) cs hcs

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (routeAddr)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

def firstCoordinate (p : Fin 4) : Fin 9 := ⟨2*p.val,by have:=p.isLt;omega⟩
def secondCoordinate (p : Fin 4) : Fin 9 := ⟨2*p.val+1,by have:=p.isLt;omega⟩

def openingValues (output : HashOutput) (v : Coord→Digest) (k : Fin 9) : Fin 6→Digest := fun t =>
  v (wctItem (digestIndex output,k,SigGolfCandidate.Research.SharedForest.rawChildFromOutput output k,t)
    (4-WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank output k.val) t))

def openingPath (output : HashOutput) (v : Coord→Digest) (k : Fin 9) (l : Nat) : Digest :=
  ((wctPath (digestIndex output) k output).map v).getD l 0

def assembleForest (output : HashOutput) (v : Coord→Digest) : SigGolfCandidate.Research.SharedForest.ForestOpening :=
  ⟨fun p => ⟨openingValues output v (firstCoordinate p),fun l => openingPath output v (firstCoordinate p) l.val,
    openingValues output v (secondCoordinate p),fun l => openingPath output v (secondCoordinate p) l.val⟩,
   ⟨openingValues output v 8,fun l => openingPath output v 8 l.val⟩⟩

/-- Policy hints (radix 20) from the path-aware residual chain (`lowsOf` = selected halves). -/
def hintsOf (index : Nat) (digitsOf : Wots.LeafAddr→List Nat) (lowsOf : Wots.LeafAddr→Bool) : BitVec 16 :=
  let r1 := WCT9.CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 (lowsOf (routeAddr index 0))
    (digitsOf (routeAddr index 0))
  let r2 := WCT9.CanonicalPolicy.nextResidual r1 1 (lowsOf (routeAddr index 1)) (digitsOf (routeAddr index 1))
  let r3 := WCT9.CanonicalPolicy.nextResidual r2 2 (lowsOf (routeAddr index 2)) (digitsOf (routeAddr index 2))
  BitVec.ofNat 16 (484*WCT9.CanonicalPolicy.threshold 1 r1+22*WCT9.CanonicalPolicy.threshold 2 r2+
    WCT9.CanonicalPolicy.threshold 3 r3)

def assembleSig (rho : Digest) (output : HashOutput) (v : Coord→Digest) (digitsOf : Wots.LeafAddr→List Nat)
    (lowsOf : Wots.LeafAddr→Bool) : SigGolfCandidate.Research.SharedForest.Signature :=
  ⟨rho,hintsOf (WCT9.digestIndex output) digitsOf lowsOf,assembleForest output v,
    fun lay => piecesSignature lay ((layerChains digitsOf (digestIndex output) lay).map v,
      (layerPath (digestIndex output) lay).map v)⟩

def signItemsWith (digitsOf : Wots.LeafAddr→List Nat) (output : HashOutput) : List Coord :=
  ftsItems (digestIndex output) output++layerItems digitsOf (digestIndex output)

def decodeDigest (output : HashOutput) : Option HashOutput :=
  if SigGolfCandidate.Research.SharedForest.digestAccepted output then some output else none

def Reuse (cache : Sampling.RCache) (rho : Digest) (message : Message) : Prop :=
  ¬Sampling.CachedTrialsReject (Sampling.digestTrial rho message) decodeDigest 0 (2^32) cache

noncomputable def RouterState.signed (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32×HashOutput)) : RouterState :=
  if Reuse st.cache rho m then
    { st with
      trials := st.trials ++ trialRows rho m found
      memo := (m, found) :: st.memo
      reused := true }
  else
    { st with
      trials := st.trials ++ trialRows rho m found
      memo := (m, found) :: st.memo
      exposures := st.exposures ++ (found.map Prod.snd).toList }

theorem RouterState.signed_fields (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32×HashOutput)) :
    (RouterState.signed st rho m found).disclosed=st.disclosed ∧
    (RouterState.signed st rho m found).seen=st.seen ∧
    (RouterState.signed st rho m found).calls=st.calls ∧
    (RouterState.signed st rho m found).births=st.births ∧
    (RouterState.signed st rho m found).trials=st.trials++trialRows rho m found ∧
    (RouterState.signed st rho m found).memo=(m,found)::st.memo := by
  unfold RouterState.signed
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

section Route
variable (U : Finset HashInput)
noncomputable def signFinish (a : AuxData) (st : RouterState) (rho : Digest)
    (found : Option (BitVec 32×HashOutput)) : OracleComp (RWorld U) (Option SigGolfCandidate.Research.SharedForest.Signature×RouterState) :=
  match found with
  | none => pure (none,st)
  | some (_,output) =>
      if RouteOkR a (WCT9.digestIndex output) then do
        let items := signItemsWith (routerDigits a) output
        let pairs ← discloseAll U (items ++ topTrialsDisclosed)
        pure (some (assembleSig rho output (selVals (lookupVal pairs)) (routerDigits a) (routerLows a)),
          {st with disclosed:=st.disclosed++items})
      else pure (none,st)

noncomputable def routeSign (a : AuxData) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : SigGolfCandidate.T3.Security.Request) : OracleComp (RWorld U) (Option SigGolfCandidate.Research.SharedForest.Signature×RouterState) :=
  if request.cache=published then do
    let rho ← discloseReq U (.inr request.message) .none
    match st.memo.lookup request.message with
    | some found => signFinish U a st rho found
    | none => do
        let found ← simulateQ (readImpl U a)
          (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho request.message 0 WCT9.digestAttemptLimit)
        signFinish U a (RouterState.signed st rho request.message found) rho found
  else pure (none,st)

noncomputable def routeInteraction (a : AuxData) (published : SigGolfCandidate.T3.Cache) (q : Nat) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    RouterState → OracleComp (RWorld U) (Option ((α×QueryLog Final.Paired.Requests)×RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some ((value,[]),st)))
    (fun input _ next st => match input,next with
      | .inl (.inl n),next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X),next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuerySelected U a st X
            next r.1 r.2
      | .inr request,next => do
          let s ← routeSign U a published st request
          let rest ← next s.1 s.2
          pure (rest.map fun res => ((res.1.1,⟨request,s.1⟩::res.1.2),res.2))) program

noncomputable def routeVerdict (a : AuxData) (q : Nat) {β : Type} (program : M β) :
    RouterState → OracleComp (RWorld U) (Option (β×RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some (value,st)))
    (fun input _ next st => match input,next with
      | .inl (.inl n),next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X),next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuerySelected U a st X
            next r.1 r.2
      | .inr c,next => next (a.priv c) st) program

noncomputable def routerWith (adversary : Final.Paired.AdversaryP) (q : Nat) (a : AuxData) :
    OracleComp (RWorld U) (Option (Bool×RouterState)) := do
  let pairs ← discloseAll U keygenDisclosed
  let v := lookupVal pairs
  let pk := v (.inl (.node rootNode))
  let region := Correctness.cacheRegion fun level node => topValue v level node ^^^ maskOf a level node
  let published : SigGolfCandidate.T3.Cache := ⟨macOf a region,region⟩
  let r ← routeInteraction U a published q (adversary pk published) RouterState.initial
  match r with
  | none => pure none
  | some (result,st) => routeVerdict U a q (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk result) st

noncomputable def router (adversary : Final.Paired.AdversaryP) (q : Nat) : OracleComp (RWorld U) (Option (Bool×RouterState)) :=
  initReq U >>= routerWith U adversary q
end Route
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
def UsedCoord : Coord → Prop
  | .inl n => CanonGraph.Paired.Filtered.Used n
  | .inr _ => True
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem ftsChild_used (index : Fin (2^31)) (k : Fin 9) (level physical : Nat)
    (hl : level < if firstCoord k.val then 6 else 7) (c : Coord)
    (hc : ftsChild index k level physical=some c) : UsedCoord c := by
  unfold ftsChild at hc
  by_cases hz : level=0
  · rw [if_pos hz] at hc
    split_ifs at hc <;> cases hc <;> trivial
  · rw [if_neg hz] at hc
    cases hn : ftsNodeAt index k (level-1) physical with
    | none => simp [hn] at hc
    | some n =>
      simp only [hn,Option.map_some,Option.some.injEq] at hc
      subst c
      change CanonGraph.Paired.first n.1.coord.val → n.1.level.val<5
      rw [ftsNodeAt_coord hn,ftsNodeAt_level hn]
      intro hfirst
      have hf : firstCoord k.val=true := by simpa [firstCoord,CanonGraph.Paired.first] using hfirst
      simp only [hf,ite_true] at hl
      omega

theorem wctPath_used (index : Fin (2^31)) (k : Fin 9) (output : HashOutput)
    (c : Coord) (hc : c∈wctPath index k output) : UsedCoord c := by
  obtain ⟨l,hl,hc⟩ := List.mem_filterMap.mp hc
  exact ftsChild_used index k l _ (List.mem_range.mp hl) c hc

theorem wctItem_used (a : WctAddr) (p : Nat) : UsedCoord (wctItem a p) := by
  unfold wctItem
  split_ifs <;> trivial

theorem treeChild_used (lay : Layer) (tree : Fin (2^31)) (level physical : Nat)
    (c : Coord) (hc : treeChild lay tree level physical=some c) : UsedCoord c := by
  unfold treeChild at hc
  split_ifs at hc
  · cases h : leafAt lay tree physical with
    | none => simp [h] at hc
    | some n => simp only [h,Option.map_some,Option.some.injEq] at hc; subst c; trivial
  · cases h : CanonGraph.treeNodeAt lay tree (level-1) physical with
    | none => simp [h] at hc
    | some n => simp only [h,Option.map_some,Option.some.injEq] at hc; subst c; trivial

theorem chainItem_used (L : CanonGraph.LeafPos) (i d : Nat) : UsedCoord (chainItem L i d) := by
  unfold chainItem
  split_ifs <;> trivial

theorem layerItems_used (digits : Wots.LeafAddr→List Nat) (index : Fin (2^31))
    (c : Coord) (hc : c∈layerItems digits index) : UsedCoord c := by
  obtain ⟨lay,_,hc⟩ := List.mem_flatMap.mp hc
  rcases List.mem_append.mp hc with hc|hc
  · unfold layerChains at hc
    split_ifs at hc
    · obtain ⟨i,_,hi⟩ := List.mem_map.mp hc
      subst c
      exact chainItem_used _ _ _
    · simp at hc
  · unfold layerPath at hc
    split_ifs at hc
    · obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
      exact treeChild_used _ _ _ _ _ hi
    · simp at hc

theorem ftsItems_used (index : Fin (2^31)) (output : HashOutput) (c : Coord)
    (hc : c∈ftsItems index output) : UsedCoord c := by
  obtain ⟨k,_,hc⟩ := List.mem_flatMap.mp hc
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨t,ht⟩ := List.mem_ofFn.mp hc
    subst c
    exact wctItem_used _ _
  · exact wctPath_used _ _ _ _ hc

theorem signItems_used (T : Answers) (output : HashOutput) (c : Coord)
    (hc : c∈signItems T output) : UsedCoord c := by
  rcases List.mem_append.mp hc with hc|hc
  · exact ftsItems_used _ _ _ hc
  · exact layerItems_used _ _ _ hc
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.LargeResidual (routeAddr)
open Wots.CanonicalRef
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem referenceDigits_some (T : Answers) (L : Wots.LeafAddr) (c : BitVec 32) (digits : List Nat) (low : Bool)
    (h : referenceSearch T (sourceMessages T) L=some (c,digits,low)) :
    referenceDigits T (sourceMessages T) L=digits := by
  simp only [referenceDigits,h,Option.map_some,Option.getD_some]

 theorem referenceLow_some (T : Answers) (L : Wots.LeafAddr) (c : BitVec 32) (digits : List Nat) (low : Bool)
    (h : referenceSearch T (sourceMessages T) L=some (c,digits,low)) :
    referenceLow T (sourceMessages T) L=low := by
  simp only [referenceLow,h,Option.map_some,Option.getD_some]

 theorem route_search_of_context (T : Answers) (index : Nat) (hok : RouteOk T index)
    (lay : Layer) (remaining : Nat)
    (hc : referenceContext T (sourceMessages T) (sourceLeaf index lay)=some remaining) :
    ∃ c d l, referenceSearch T (sourceMessages T) (sourceLeaf index lay)=some (c,d,l) ∧
      searchOf T (sourceMessages T) (sourceLeaf index lay) remaining=some (c,d,l) := by
  have hs := hok lay
  change (referenceSearch T (sourceMessages T) (sourceLeaf index lay)).isSome at hs
  cases he : referenceSearch T (sourceMessages T) (sourceLeaf index lay) with
  | none => simp [he] at hs
  | some found =>
    rcases found with ⟨c,d,l⟩
    refine ⟨c,d,l,rfl,?_⟩
    change (referenceContext T (sourceMessages T) (sourceLeaf index lay)).bind _ = _ at he
    simpa only [hc,Option.bind_some] using he

 theorem prepared_complete_of_route (T : Answers) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (hi : index<2^31) (hok : RouteOk T index) :
    ∃ result, evalWithAnswerFn T (searchPreparedLayers cache index
      (evalWithAnswerFn T (prepareRoots index)) (SigGolfCandidate.Research.SharedForest.forestCommitment T index))=some result := by
  have hc0 : referenceContext T (sourceMessages T) (sourceLeaf index 0)=some WCT9.CanonicalPolicy.totalCredit := rfl
  obtain ⟨c0,d0,l0,href0,hs0⟩ := route_search_of_context T index hok 0 WCT9.CanonicalPolicy.totalCredit hc0
  rw [searchOf_route_lower T index 0 (by decide)] at hs0
  have hd0 := (canonical_search_some' T 0 (WCT9.CanonicalPolicy.threshold 0 WCT9.CanonicalPolicy.totalCredit)
    (route index 0).2 (route index 0).1
    (.pair (ClaudeWCT.WCT9.builtPair T 1 (route index 1).2).1
      (ClaudeWCT.WCT9.builtPair T 1 (route index 1).2).2)
    (WCT9.searchLimit 0) 0 c0 d0 l0 (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs0).2.2.2
  let r1 := WCT9.CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 l0 d0
  have hr1 : r1<56 := WCT9.CanonicalPolicy.accepted_top_residual
    (by rwa [WCT9.CanonicalPolicy.threshold_top] at hd0)
  have hf1 : WCT9.CanonicalPolicy.threshold 1 r1<16 := WCT9.CanonicalPolicy.lower_one_floor_lt ⟨r1,hr1⟩
  have hc1 : referenceContext T (sourceMessages T) (sourceLeaf index 1)=some r1 := by
    apply context_parent_success (leaf:=sourceLeaf index 1) (by change 1≠0;decide)
    · rw [sourceLeaf_parent index 1 (by decide)];exact hc0
    · rw [sourceLeaf_parent index 1 (by decide)];exact href0
  obtain ⟨c1,d1,l1,href1,hs1⟩ := route_search_of_context T index hok 1 r1 hc1
  rw [searchOf_route_lower T index 1 (by decide)] at hs1
  have hd1 := (canonical_search_some' T 1 (WCT9.CanonicalPolicy.threshold 1 r1)
    (route index 1).2 (route index 1).1
    (.pair (ClaudeWCT.WCT9.builtPair T 2 (route index 2).2).1
      (ClaudeWCT.WCT9.builtPair T 2 (route index 2).2).2)
    (WCT9.searchLimit 1) 0 c1 d1 l1 (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs1).2.2.2
  let r2 := WCT9.CanonicalPolicy.nextResidual r1 1 l1 d1
  have hr2 : r2<41 := WCT9.CanonicalPolicy.accepted_one_residual ⟨r1,hr1⟩ hd1
  have hf2 : WCT9.CanonicalPolicy.threshold 2 r2<22 := by
    have h := (WCT9.CanonicalPolicy.lower_two_progress ⟨r2,hr2⟩).1
    change WCT9.CanonicalPolicy.threshold 2 r2≤19 at h
    omega
  have hc2 : referenceContext T (sourceMessages T) (sourceLeaf index 2)=some r2 := by
    apply context_parent_success (leaf:=sourceLeaf index 2) (by change 2≠0;decide)
    · rw [sourceLeaf_parent index 2 (by decide)];exact hc1
    · rw [sourceLeaf_parent index 2 (by decide)];exact href1
  obtain ⟨c2,d2,l2,href2,hs2⟩ := route_search_of_context T index hok 2 r2 hc2
  rw [searchOf_route_lower T index 2 (by decide)] at hs2
  have hd2 := (canonical_search_some' T 2 (WCT9.CanonicalPolicy.threshold 2 r2)
    (route index 2).2 (route index 2).1
    (.pair (ClaudeWCT.WCT9.builtPair T 3 (route index 3).2).1
      (ClaudeWCT.WCT9.builtPair T 3 (route index 3).2).2)
    (WCT9.searchLimit 2) 0 c2 d2 l2 (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs2).2.2.2
  let r3 := WCT9.CanonicalPolicy.nextResidual r2 2 l2 d2
  have hr3 : r3<22 := WCT9.CanonicalPolicy.accepted_two_residual ⟨r2,hr2⟩ hd2
  have hf3 : WCT9.CanonicalPolicy.threshold 3 r3<22 := by
    rwa [WCT9.CanonicalPolicy.lower_three_progress r3 hr3]
  have hc3 : referenceContext T (sourceMessages T) (sourceLeaf index 3)=some r3 := by
    apply context_parent_success (leaf:=sourceLeaf index 3) (by change 3≠0;decide)
    · rw [sourceLeaf_parent index 3 (by decide)];exact hc2
    · rw [sourceLeaf_parent index 3 (by decide)];exact href2
  obtain ⟨c3,d3,l3,href3,hs3⟩ := route_search_of_context T index hok 3 r3 hc3
  rw [searchOf_route_bottom T index hi] at hs3
  have hs0' : evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt 0
      (WCT9.CanonicalPolicy.threshold 0 WCT9.CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
      (.pair (ClaudeWCT.WCT9.builtPair T 1 (route index 1).2).1 (ClaudeWCT.WCT9.builtPair T 1 (route index 1).2).2) 0 (WCT9.searchLimit 0))=some (c0,d0,l0) := hs0
  have hs1' : evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt 1
      (WCT9.CanonicalPolicy.threshold 1 r1) (route index 1).2 (route index 1).1
      (.pair (ClaudeWCT.WCT9.builtPair T 2 (route index 2).2).1 (ClaudeWCT.WCT9.builtPair T 2 (route index 2).2).2) 0 (WCT9.searchLimit 1))=some (c1,d1,l1) := hs1
  have hs2' : evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt 2
      (WCT9.CanonicalPolicy.threshold 2 r2) (route index 2).2 (route index 2).1
      (.pair (ClaudeWCT.WCT9.builtPair T 3 (route index 3).2).1 (ClaudeWCT.WCT9.builtPair T 3 (route index 3).2).2) 0 (WCT9.searchLimit 2))=some (c2,d2,l2) := hs2
  have hs3' : evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt 3
      (WCT9.CanonicalPolicy.threshold 3 r3) (route index 3).2 (route index 3).1
      (.pair (SigGolfCandidate.Research.SharedForest.forestCommitment T index).1 (SigGolfCandidate.Research.SharedForest.forestCommitment T index).2) 0 (WCT9.searchLimit 3))=some (c3,d3,l3) := hs3
  have hn1 : ¬WCT9.CanonicalPolicy.threshold 1 r1≥16 := by omega
  have hn2 : ¬WCT9.CanonicalPolicy.threshold 2 r2≥22 := by omega
  have hn3 : ¬WCT9.CanonicalPolicy.threshold 3 r3≥22 := by omega
  dsimp only [r1,r2,r3] at hs1' hs2' hs3' hn1 hn2 hn3
  simp only [prepareRoots_result,searchPreparedLayers,fixedPrepared_pair,evalWithAnswerFn_bind]
  rw [hs0']
  simp only [hn1,if_false,evalWithAnswerFn_bind]
  rw [hs1']
  simp only [hn2,if_false,evalWithAnswerFn_bind]
  rw [hs2']
  simp only [hn3,if_false,evalWithAnswerFn_bind]
  rw [hs3']
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

 theorem prepared_route_iff (T : Answers) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (hi : index<2^31) :
    (evalWithAnswerFn T (searchPreparedLayers cache index
      (evalWithAnswerFn T (prepareRoots index)) (SigGolfCandidate.Research.SharedForest.forestCommitment T index))).isSome ↔ RouteOk T index := by
  constructor
  · intro hs lay
    cases he : evalWithAnswerFn T (searchPreparedLayers cache index
        (evalWithAnswerFn T (prepareRoots index)) (SigGolfCandidate.Research.SharedForest.forestCommitment T index)) with
    | none => simp [he] at hs
    | some result =>
      have hr := (searchPreparedLayers_reference T cache index hi result he lay).2
      change (referenceSearch T (sourceMessages T) (sourceLeaf index lay)).isSome
      rw [hr];rfl
  · intro hok
    obtain ⟨result,he⟩ := prepared_complete_of_route T cache index hi hok
    rw [he];rfl

 theorem prepared_digits_eq {T : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    (hi : index<2^31) {result : CanonicalLayers}
    (he : evalWithAnswerFn T (searchPreparedLayers cache index
      (evalWithAnswerFn T (prepareRoots index)) (SigGolfCandidate.Research.SharedForest.forestCommitment T index))=some result) (lay : Layer) :
    result.digits.getD lay.val []=referenceDigits T (sourceMessages T) (routeAddr index lay) :=
  (referenceDigits_some T _ _ _ _ (searchPreparedLayers_reference T cache index hi result he lay).2).symm

 theorem prepared_lows_eq {T : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    (hi : index<2^31) {result : CanonicalLayers}
    (he : evalWithAnswerFn T (searchPreparedLayers cache index
      (evalWithAnswerFn T (prepareRoots index)) (SigGolfCandidate.Research.SharedForest.forestCommitment T index))=some result) (lay : Layer) :
    result.lows.getD lay.val true=referenceLow T (sourceMessages T) (routeAddr index lay) :=
  (referenceLow_some T _ _ _ _ (searchPreparedLayers_reference T cache index hi result he lay).2).symm

 theorem prepared_hints_eq {T : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    (hi : index<2^31) {result : CanonicalLayers}
    (he : evalWithAnswerFn T (searchPreparedLayers cache index
      (evalWithAnswerFn T (prepareRoots index)) (SigGolfCandidate.Research.SharedForest.forestCommitment T index))=some result) :
    result.policyHints=hintsOf index (referenceDigits T (sourceMessages T)) (referenceLow T (sourceMessages T)) := by
  have hf := searchPreparedLayers_some T cache index _ _ result he
  rw [hf.hints_eq]
  have h0 : result.digits.getD 0 []=_ := prepared_digits_eq hi he 0
  have h1 : result.digits.getD 1 []=_ := prepared_digits_eq hi he 1
  have h2 : result.digits.getD 2 []=_ := prepared_digits_eq hi he 2
  have l0 : result.lows.getD 0 true=_ := prepared_lows_eq hi he 0
  have l1 : result.lows.getD 1 true=_ := prepared_lows_eq hi he 1
  have l2 : result.lows.getD 2 true=_ := prepared_lows_eq hi he 2
  simp only [hintsOf,preparedResidual1,preparedResidual2,preparedResidual3,h0,h1,h2,l0,l1,l2]

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sharedNodes ClaudeWCT.WCT9.heapBuild

theorem selCoordV_eq_self {v : Coord → Digest} {c : Coord} (h : ∀ n, c ≠ .inl (.node n)) : selCoordV v c = c := by
  rcases c with (_ | _ | n | _ | _ | _ | _) | s
  all_goals first | rfl | exact absurd rfl (h n)
theorem ftsChild_not_node {index : Fin (2^31)} {coord : Fin 9} {level physical : Nat} {c : Coord}
    (h : ftsChild index coord level physical = some c) : ∀ n, c ≠ .inl (.node n) := by
  intro n hn; subst hn
  unfold ftsChild at h
  split_ifs at h <;> simp at h
theorem wctItem_not_node (a : WctAddr) (p : Nat) : ∀ n, wctItem a p ≠ .inl (.node n) := by
  intro n; unfold wctItem; split_ifs <;> simp
theorem chainItem_not_node (L : CanonGraph.LeafPos) (i d : Nat) : ∀ n, chainItem L i d ≠ .inl (.node n) := by
  intro n; unfold chainItem; split_ifs <;> simp
/-- Honest values of used coordinates (top-nonce layer: a tree-node coordinate has the value of its position's
selected trial). -/
theorem honestValue_used_eq {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (c : Coord) (hc : UsedCoord c) :
    honestValue T c=coordVal (secretsOf T) labels (selCoordV (coordVal (secretsOf T) labels) c) := by
  cases c with
  | inl n =>
    change Extract.Paired.proj n.toPos (T (.inl (.inr (Extract.Paired.honestInput T n.toPos))))=_
    rw [CanonGraph.Paired.honest_answer T labels h n ((CanonGraph.Paired.Filtered.used_iff_bounded n).1 hc)]
    cases n with
    | node m =>
      rw [coordVal_selCoordV_node, CanonGraph.Paired.pairedProj_node]
      rfl
    | _ => rfl
  | inr s => rfl
theorem honestValue_used_eq_plain {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (c : Coord) (hc : UsedCoord c) (hn : ∀ n, c ≠ .inl (.node n)) :
    honestValue T c=coordVal (secretsOf T) labels c := by
  rw [honestValue_used_eq h c hc, selCoordV_eq_self hn]

 theorem buildForest_pairs (T : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (p : Fin 4) : (evalWithAnswerFn T (buildForest index selected words)).1.pairs p=
      expectedPairOpening T index p.val (selected.pairs p) (words.first p) (words.second p)
        (Extract.Paired.pairPrev T index p.val) := by
  have hfour : List.finRange 4=[0,1,2,3] := by decide
  fin_cases p <;>
    simp only [buildForest,hfour,List.foldlM_cons,List.foldlM_nil,evalWithAnswerFn_bind,
      evalWithAnswerFn_pure,buildPair_result,buildSingleton,buildSharedCoordinate_result]
  all_goals rfl

 theorem buildForest_singleton (T : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    (evalWithAnswerFn T (buildForest index selected words)).1.singleton=
      ⟨fun t => WCT9.chainValue T index 8 (rawChild false selected.singleton.val) words.singleton t,
       fun l => authAt (Extract.Paired.nodes T index 8) selected.singleton.val l.val⟩ := by
  have hfour : List.finRange 4=[0,1,2,3] := by decide
  simp only [buildForest,hfour,List.foldlM_cons,List.foldlM_nil,evalWithAnswerFn_bind,
    evalWithAnswerFn_pure,buildPair_result,buildSingleton,buildSharedCoordinate_result]
  congr 1
  funext t
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

 theorem nodes_first (T : Answers) (index : Nat) (p : Fin 4) :
    Extract.Paired.nodes T index (firstCoordinate p).val=
      firstNodes T index p.val (Extract.Paired.pairPrev T index p.val) := by
  fin_cases p <;> rfl
 theorem nodes_second (T : Answers) (index : Nat) (p : Fin 4) :
    Extract.Paired.nodes T index (secondCoordinate p).val=
      secondNodes T index p.val (Extract.Paired.pairPrev T index p.val) := by
  fin_cases p <;> rfl

 theorem authAt_index (nodes : Array Digest) (selected : Fin 128) (level : Fin 7) :
    authAt nodes selected.val level.val=
      nodes.getD (2^(7-level.val)+(selected.val/2^level.val ^^^ 1)) 0 := by
  have hi : ∀ c : Fin 128, ∀ l : Fin 7,
      ((128+c.val)/2^l.val ^^^ 1)=2^(7-l.val)+(c.val/2^l.val ^^^ 1) := by decide +kernel
  exact congrArg (fun n => nodes.getD n 0) (hi selected level)

 theorem physical_path_bound (N : HashOutput) (k : Fin 9) (l : Nat) (hl : l<7) :
    (physicalChildFromOutput N k).val/2^l ^^^ 1<2^(7-l) := by
  apply Nat.xor_lt_two_pow
  · rw [Nat.div_lt_iff_lt_mul (by positivity),←pow_add,show 7-l+l=7 by omega]
    exact (physicalChildFromOutput N k).isLt
  · exact Nat.one_lt_two_pow (by omega)

 theorem ftsChild_isSome (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hl : level≤6)
    (hc : c<2^(7-level)) : (ftsChild index coord level c).isSome := by
  unfold ftsChild
  by_cases hz : level=0
  · subst level
    rw [if_pos rfl]
    have hr : CanonGraph.Paired.rawLeaf coord.val c<128 := by
      unfold CanonGraph.Paired.rawLeaf
      split_ifs
      · simpa using hc
      · have hc' : c<128 := by simpa using hc
        omega
    rw [dif_pos hr];rfl
  · rw [if_neg hz]
    unfold CanonGraph.ftsNodeAt
    rw [dif_pos ⟨by omega,by
      have he : 7-(level-1)-1=7-level := by omega
      rw [he];exact hc⟩]
    rfl

 theorem wctPath_map (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) (v : Coord→Digest) :
    (wctPath index k N).map v=(List.range (if firstCoord k.val then 6 else 7)).map fun l =>
      ((ftsChild index k l ((physicalChildFromOutput N k).val/2^l ^^^ 1)).map v).getD 0 := by
  unfold wctPath
  apply SigGolfCandidate.T3.Security.LargeResidual.filterMap_map_getD _ _ _ 0
  intro l hl
  have hl' := List.mem_range.mp hl
  have hl7 : l<7 := by split_ifs at hl' <;> omega
  exact ftsChild_isSome _ _ _ _ (by omega) (physical_path_bound N k l hl7)

 theorem openingPath_nodes {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (N : HashOutput) (k : Fin 9) (l : Nat) (hl : l<(if firstCoord k.val then 6 else 7)) :
    openingPath N (honestValue T) k l=
      authAt (Extract.Paired.nodes T (WCT9.digestIndex N) k.val) (physicalChildFromOutput N k).val l := by
  have hl7 : l<7 := by split_ifs at hl <;> omega
  rw [authAt_index _ _ ⟨l,hl7⟩]
  have htop : l≤CanonGraph.Paired.topLevel k := by
    unfold CanonGraph.Paired.topLevel
    have hf : firstCoord k.val=true ↔ CanonGraph.Paired.first k.val := by
      simp only [firstCoord,CanonGraph.Paired.first,decide_eq_true_eq]
    split_ifs with hfirst
    · rw [if_pos (hf.mpr hfirst)] at hl;omega
    · rw [if_neg (fun hh => hfirst (hf.mp hh))] at hl;omega
  have hn := CanonGraph.Paired.actual_nodes_label T labels h (digestIndex N) k l _ htop (physical_path_bound N k l hl7)
  change (Extract.Paired.nodes T (WCT9.digestIndex N) k.val).getD
    (2^(7-l)+((physicalChildFromOutput N k).val/2^l ^^^ 1)) 0=_ at hn
  change openingPath N (honestValue T) k l=(Extract.Paired.nodes T (WCT9.digestIndex N) k.val).getD
    (2^(7-l)+((physicalChildFromOutput N k).val/2^l ^^^ 1)) 0
  rw [hn]
  unfold openingPath
  rw [wctPath_map, List.getD_eq_getElem _ _ (by simpa using hl)]
  simp only [List.getElem_map,List.getElem_range]
  rw [ftsLabel_eq (secretsOf T)]
  cases hc : ftsChild (digestIndex N) k l ((physicalChildFromOutput N k).val/2^l ^^^ 1) with
  | none => rfl
  | some c =>
    simp only [Option.map_some,Option.getD_some]
    exact honestValue_used_eq_plain h c (ftsChild_used _ _ _ _ hl c hc) (ftsChild_not_node hc)

 theorem openingValues_chain {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    openingValues N (honestValue T) k t=
      WCT9.chainValue T (WCT9.digestIndex N) k.val (rawChildFromOutput N k).val (forestRank N k.val) t := by
  unfold openingValues
  rw [honestValue_used_eq_plain h _ (wctItem_used _ _) (wctItem_not_node _ _),coordVal_wctItem]
  rw [←CanonGraph.Paired.wctValue_eq h _ _ (Nat.sub_le _ _)]
  rfl

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sharedNodes ClaudeWCT.WCT9.heapBuild

 theorem rawFromOutput_first (N : HashOutput) (p : Fin 4) :
    rawChild true (firstChild ((forestSelectionFromOutput N).pairs p)).val=
      (rawChildFromOutput N (firstCoordinate p)).val := by
  rw [←physicalFromOutput_first N p]
  have hf : firstCoord (firstCoordinate p).val=true := by fin_cases p <;> rfl
  change rawChild true (physicalChild (firstCoord (firstCoordinate p).val)
    (rawChildFromOutput N (firstCoordinate p)).val)=_
  rw [hf]
  exact raw_physical_child true _ (rawChildFromOutput N (firstCoordinate p)).isLt

 theorem rawFromOutput_second (N : HashOutput) (p : Fin 4) :
    rawChild false (secondChild ((forestSelectionFromOutput N).pairs p)).val=
      (rawChildFromOutput N (secondCoordinate p)).val := by
  rw [←physicalFromOutput_second N p]
  have hf : firstCoord (secondCoordinate p).val=false := by fin_cases p <;> rfl
  change rawChild false (physicalChild (firstCoord (secondCoordinate p).val)
    (rawChildFromOutput N (secondCoordinate p)).val)=_
  rw [hf]
  exact raw_physical_child false _ (rawChildFromOutput N (secondCoordinate p)).isLt

 theorem rawFromOutput_singleton (N : HashOutput) :
    rawChild false (forestSelectionFromOutput N).singleton.val=(rawChildFromOutput N 8).val :=
  raw_physical_child false _ (rawChildFromOutput N 8).isLt

 theorem buildForest_opening {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (N : HashOutput) :
    (evalWithAnswerFn T (buildForest (WCT9.digestIndex N) (forestSelectionFromOutput N)
      (forestWordsFromOutput N))).1=assembleForest N (honestValue T) := by
  have hp : ∀ p : Fin 4,
      (evalWithAnswerFn T (buildForest (WCT9.digestIndex N) (forestSelectionFromOutput N)
        (forestWordsFromOutput N))).1.pairs p=(assembleForest N (honestValue T)).pairs p := by
    intro p
    rw [buildForest_pairs]
    simp only [assembleForest,expectedPairOpening]
    congr 1
    · funext t
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn,openingValues_chain h,rawFromOutput_first]
      rfl
    · funext l
      rw [openingPath_nodes h _ _ _ (by
        have hl := l.isLt
        fin_cases p <;> exact hl)]
      rw [nodes_first]
      exact congrArg (fun c : WCT9.Child => authAt (firstNodes T (WCT9.digestIndex N) p.val
        (Extract.Paired.pairPrev T (WCT9.digestIndex N) p.val)) c.val l.val) (physicalFromOutput_first N p).symm
    · funext t
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn,openingValues_chain h,rawFromOutput_second]
      rfl
    · funext l
      rw [openingPath_nodes h _ _ _ (by
        have hl := l.isLt
        fin_cases p <;> exact hl)]
      rw [nodes_second]
      exact congrArg (fun c : WCT9.Child => authAt (secondNodes T (WCT9.digestIndex N) p.val
        (Extract.Paired.pairPrev T (WCT9.digestIndex N) p.val)) c.val l.val) (physicalFromOutput_second N p).symm
  have hs :
      (evalWithAnswerFn T (buildForest (WCT9.digestIndex N) (forestSelectionFromOutput N)
        (forestWordsFromOutput N))).1.singleton=(assembleForest N (honestValue T)).singleton := by
    rw [buildForest_singleton]
    simp only [assembleForest]
    congr 1
    · funext t
      rw [openingValues_chain h,rawFromOutput_singleton]
      rfl
    · funext l
      rw [openingPath_nodes h _ _ _ l.isLt,physicalFromOutput_singleton]
      rfl
  cases hf : (evalWithAnswerFn T (buildForest (WCT9.digestIndex N) (forestSelectionFromOutput N)
        (forestWordsFromOutput N))).1 with
  | mk pairs singleton =>
    simp only [hf] at hp hs
    simp only [assembleForest] at hp hs ⊢
    rw [funext hp,hs]

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
open CanonEncoding
open SigGolfCandidate.T3.Security.LargeResidual (routeAddr filterMap_map_getD)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem chainItem_value {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (L : CanonGraph.LeafPos) (digits : List Nat) (i : Nat) (hi : i<58) (hd : digits.getD i 0≤7) :
    WCT9.wotsValue T L.lay L.tree.val L.leaf.val digits i=honestValue T (chainItem L i (digits.getD i 0)) := by
  rw [CanonGraph.Paired.leafValue_eq h L digits i hi hd,honestValue_used_eq_plain h _ (chainItem_used _ _ _) (chainItem_not_node _ _ _)]
  -- C3 (#866): `leafValue_eq` states a revealed value through `Pos.proj` of its last step's label.
  unfold chainItem
  by_cases hz : digits.getD i 0=0
  · rw [if_pos hz,if_pos hz];rfl
  · rw [if_neg hz,if_neg hz]
    first
      | rfl
      | exact (congrFun (CanonGraph.Paired.pairedProj_chain _) _).symm

 theorem treeLabel_honest {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    CanonGraph.treeLabel labels lay tree level c=((treeChild lay tree level c).map (honestValue T)).getD 0 := by
  rw [treeLabel_eq (CanonGraph.secretsOf T)]
  unfold treeVal
  cases he : treeChild lay tree level c with
  | none => rfl
  | some value =>
    simp only [Option.map_some,Option.getD_some]
    exact (honestValue_used_eq h _ (treeChild_used _ _ _ _ _ he)).symm

 theorem honestPieces_eq {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    (index : Fin (2^31)) (lay : Layer) (digitsOf : Wots.LeafAddr→List Nat)
    (hvalid : Cost.ValidDigits lay (digitsOf (routeAddr index.val lay))) :
    WCT9.wotsPieces T lay (route index.val lay).2 (route index.val lay).1 (digitsOf (routeAddr index.val lay))=
      ((layerChains digitsOf index lay).map (honestValue T),(layerPath index lay).map (honestValue T)) := by
  have htree := CanonEncoding.route_tree_lt index.val index.isLt lay
  have ht31 : (route index.val lay).2<2^31 := lt_of_lt_of_le htree
    (Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide))
  have hleaf := route_leaf_bound index.val lay
  have hl4096 : (route index.val lay).1<4096 := lt_of_lt_of_le hleaf (by
    calc 2^height lay≤2^12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
         _=4096 := by norm_num)
  unfold WCT9.wotsPieces layerChains layerPath
  rw [dif_pos ⟨ht31,hl4096⟩,dif_pos ht31]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hi58 : i<58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
    have hd : (digitsOf (routeAddr index.val lay)).getD i 0≤7 := by
      have hv := hvalid i hi
      have hw : maxDigit lay i≤7 := by unfold maxDigit;split_ifs <;> norm_num
      omega
    exact chainItem_value h ⟨lay,⟨_,ht31⟩,⟨_,hl4096⟩⟩ _ i hi58 hd
  · have hc : ∀ j∈List.range (height lay),
        (route index.val lay).1/2^j ^^^ 1<2^(height lay-j) := by
      intro j hj
      rw [List.mem_range] at hj
      apply Nat.xor_lt_two_pow
      · rw [Nat.div_lt_iff_lt_mul (by positivity),←pow_add,show height lay-j+j=height lay by omega]
        exact hleaf
      · exact Nat.one_lt_two_pow (by omega)
    rw [filterMap_map_getD _ _ _ 0 (fun j hj => LargeResidual.treeChild_isSome _ _ _ _
      (by have := List.mem_range.mp hj;omega) (hc j hj) htree (Or.inr (List.mem_range.mp hj)))]
    apply List.map_congr_left
    intro j hj
    rw [CanonGraph.Paired.builtTree_eq h lay ⟨_,ht31⟩ j _ (by have := List.mem_range.mp hj;omega)
      (hc j hj) htree (Or.inr (List.mem_range.mp hj)),treeLabel_honest h]

 theorem prepared_pieces_eq {T : Answers} {labels : CanonGraph.Labels} (h : CanonGraph.Paired.Agrees T labels)
    {cache : SigGolfCandidate.T3.Cache} {index : Nat} (hi : index<2^31)
    (hcache : cache.region=Correctness.cacheRegion (Correctness.maskedTop T)) {result : CanonicalLayers}
    (he : evalWithAnswerFn T (searchPreparedLayers cache index
      (evalWithAnswerFn T (prepareRoots index)) (forestCommitment T index))=some result) (lay : Layer) :
    result.pieces.getD lay.val ([],[])=
      ((layerChains (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) ⟨index,hi⟩ lay).map (honestValue T),
       (layerPath ⟨index,hi⟩ lay).map (honestValue T)) := by
  have hf := searchPreparedLayers_some T cache index _ _ result he
  rw [hf.honest_pieces hcache hi lay,prepared_digits_eq hi he lay]
  have hv : Cost.ValidDigits lay (Wots.CanonicalRef.referenceDigits T
      (Wots.CanonicalRef.sourceMessages T) (routeAddr index lay)) := by
    rw [←prepared_digits_eq hi he lay]
    exact hf.validDigits lay
  exact honestPieces_eq h ⟨index,hi⟩ lay (Wots.CanonicalRef.referenceDigits T
    (Wots.CanonicalRef.sourceMessages T)) hv

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.LargeResidual (routeAddr)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

 theorem signPayload_disclosed {T : Answers} {labels : CanonGraph.Labels}
    (h : CanonGraph.Paired.Filtered.Agrees T labels) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=Correctness.cacheRegion (Correctness.maskedTop T)) (m : Message) :
    evalWithAnswerFn T (SigGolfCandidate.Research.SharedForest.signPayload cache m)=
      match signDigest T m with
      | none => none
      | some (_,N) => if RouteOk T (WCT9.digestIndex N) then
          some (assembleSig (evalWithAnswerFn T (privateNonce m)) N (honestValue T)
            (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T))
            (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T)))
        else none := by
  have hf := CanonGraph.Paired.Filtered.completeLabels_agrees h
  simp only [SigGolfCandidate.Research.SharedForest.signPayload,evalWithAnswerFn_bind,signDigest]
  cases hd : evalWithAnswerFn T (sharedDigestSearch (evalWithAnswerFn T (privateNonce m)) m 0 WCT9.digestAttemptLimit) with
  | none => rfl
  | some found =>
    rcases found with ⟨counter,N⟩
    simp only [signFromOutput,evalWithAnswerFn_bind,buildForest_commitment]
    cases hs : evalWithAnswerFn T (searchPreparedLayers cache (WCT9.digestIndex N)
        (evalWithAnswerFn T (prepareRoots (WCT9.digestIndex N))) (forestCommitment T (WCT9.digestIndex N))) with
    | none =>
      have hn : ¬RouteOk T (WCT9.digestIndex N) := by
        intro hok
        have ht := (prepared_route_iff T cache _ (WCT9.digestIndex_lt N)).mpr hok
        rw [hs] at ht;cases ht
      simp only [evalWithAnswerFn_pure,hn,if_false]
    | some result =>
      have hok : RouteOk T (WCT9.digestIndex N) :=
        (prepared_route_iff T cache _ (WCT9.digestIndex_lt N)).mp (by rw [hs];rfl)
      simp only [evalWithAnswerFn_pure,hok,if_true]
      apply congrArg some
      unfold assembleSig
      rw [buildForest_opening hf N,prepared_hints_eq (WCT9.digestIndex_lt N) hs]
      congr 1
      funext lay
      rw [prepared_pieces_eq hf (WCT9.digestIndex_lt N) hcache hs lay]
      rfl

 theorem authenticatedSign_disclosed {T : Answers} {labels : CanonGraph.Labels}
    (h : CanonGraph.Paired.Filtered.Agrees T labels) (published : SigGolfCandidate.T3.Cache)
    (hpub : published.region=Correctness.cacheRegion (Correctness.maskedTop T))
    (request : SigGolfCandidate.T3.Security.Request) :
    evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
      if request.cache=published then
        match signDigest T request.message with
        | none => none
        | some (_,N) => if RouteOk T (WCT9.digestIndex N) then
            some (assembleSig (evalWithAnswerFn T (privateNonce request.message)) N (honestValue T)
              (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T))
              (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T)))
          else none
      else none := by
  unfold PairedOuter.FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  split_ifs with hc
  · rw [hc]
    exact signPayload_disclosed h published hpub request.message
  · rfl

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired
