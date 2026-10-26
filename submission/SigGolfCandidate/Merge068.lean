import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge027
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge042
import SigGolfCandidate.Merge050
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge066
import SigGolfCandidate.Merge067

-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingSign ====
section

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
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTopLevelsSat ====
section

/-! Top-bytes layer: every query of the nonce-searched top tree `buildTopLevels` satisfies a predicate `P`,
given `P` on every trial input of every nonce search (up to the found nonce) and on the zero-nonce root input. -/
namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000

theorem topNonceSearch_fst_ge (T : Answers) (h heap : Nat) (left right : Digest) :
    ∀ fuel n, n ≤ (evalWithAnswerFn T (topNonceSearch h heap left right fuel n)).1
  | 0, n => by
      simp [topNonceSearch]
  | fuel + 1, n => by
      simp only [topNonceSearch, evalWithAnswerFn_bind]
      split
      · simp [evalWithAnswerFn_pure]
      · exact Nat.le_of_succ_le (topNonceSearch_fst_ge T h heap left right fuel (n + 1))

theorem eval_topNonceSearch_succ_of_not (T : Answers) (h heap : Nat) (left right : Digest) (fuel n : Nat)
    (hz : ¬ topZeroOk h (evalWithAnswerFn T (topNodeHashN heap n left right)) = true) :
    evalWithAnswerFn T (topNonceSearch h heap left right (fuel + 1) n) =
      evalWithAnswerFn T (topNonceSearch h heap left right fuel (n + 1)) := by
  simp only [topNonceSearch, evalWithAnswerFn_bind]
  rw [if_neg hz]

/-- (1) Generic nonce-search lemma. -/
theorem sat_topNonceSearch (T : Answers) (P : SigGolfCandidate.T3.Spec.Domain → Prop) (h heap : Nat)
    (left right : Digest) :
    ∀ fuel n, (∀ k, n ≤ k → k ≤ (evalWithAnswerFn T (topNonceSearch h heap left right fuel n)).1 →
        P (.inl (.inr (pad64 (topNodeInput heap k left right))))) →
      QueriesSat T P (topNonceSearch h heap left right fuel n)
  | 0, n, hk => by
      have h1 := hk n le_rfl (topNonceSearch_fst_ge T h heap left right 0 n)
      unfold topNonceSearch
      exact QueriesSat.bind (sat_projHash _ _ h1) (QueriesSat.pure' _)
  | fuel + 1, n, hk => by
      have h1 := hk n le_rfl (topNonceSearch_fst_ge T h heap left right (fuel + 1) n)
      have hrec : ¬ topZeroOk h (evalWithAnswerFn T (topNodeHashN heap n left right)) = true →
          QueriesSat T P (topNonceSearch h heap left right fuel (n + 1)) := fun hz =>
        sat_topNonceSearch T P h heap left right fuel (n + 1) (fun k hk1 hk2 => hk k (by omega) (by
          rw [eval_topNonceSearch_succ_of_not T h heap left right fuel n hz]
          exact hk2))
      unfold topNonceSearch
      refine QueriesSat.bind (sat_projHash _ _ h1) ?_
      split
      · exact QueriesSat.pure' _
      · next hz => exact hrec hz

def topLevelsStep (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← buildTopLevel level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])

def topLevelsFold (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM topLevelsStep [leaves]

theorem buildTopLevels_eq_fold (leaves : List Digest) : buildTopLevels leaves = topLevelsFold leaves 12 := rfl

theorem eval_topLevelsStep (T : Answers) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (topLevelsStep levels level) =
      levels ++ [evalWithAnswerFn T (buildTopLevel level (levels.getD (level - 1) []))] := by
  simp only [topLevelsStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

theorem eval_topLevelsSteps_append (T : Answers) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM topLevelsStep state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_topLevelsStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (buildTopLevel x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (buildTopLevel x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩

theorem topLevelsFold_succ (leaves : List Digest) (n : Nat) :
    topLevelsFold leaves (n + 1) =
      (topLevelsFold leaves n >>= fun state => topLevelsStep state (1 + n)) := by
  unfold topLevelsFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem topLevelsFold_length (T : Answers) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (topLevelsFold leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [topLevelsFold_succ, evalWithAnswerFn_bind, eval_topLevelsStep, List.length_append, ih]
      simp

theorem topLevelsFold_prefix (T : Answers) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (topLevelsFold leaves m) =
      evalWithAnswerFn T (topLevelsFold leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold topLevelsFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_topLevelsSteps_append T _ _

theorem nonceBytes_zero : nonceBytes 0 = zero16 := by decide

theorem nodeHash_root_eq (heap : Nat) (left right : Digest) :
    nodeHash 3 0 0 heap left right = topNodeHashN heap 0 left right := by
  unfold nodeHash topNodeHashN topNodeInput
  rw [nonceBytes_zero]

/-- (2) Every query of `buildTopLevels` satisfies `P`. -/
theorem sat_buildTopLevels (T : Answers) (P : SigGolfCandidate.T3.Spec.Domain → Prop) (leaves : List Digest)
    (hlen : leaves.length = 2 ^ 12)
    (hroot : P (.inl (.inr (pad64 (topNodeInput 1 0
      (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) 11 0)
      (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) 11 1))))))
    (htrial : ∀ level c k, level < 11 → c < 2 ^ (11 - level) →
      k ≤ (evalWithAnswerFn T (topNodeAt (level + 1) (2 ^ (11 - level) + c)
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c))
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c + 1)))).1 →
      P (.inl (.inr (pad64 (topNodeInput (2 ^ (11 - level) + c) k
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c))
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c + 1))))))) :
    QueriesSat T P (buildTopLevels leaves) := by
  have hfin := Correctness.eval_buildTopLevels_correct T leaves hlen
  rw [buildTopLevels_eq_fold] at hroot htrial hfin ⊢
  unfold topLevelsFold
  refine QueriesSat.foldlM_range' 1 12 _
    (fun i state => state = evalWithAnswerFn T (topLevelsFold leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold topLevelsStep
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    have hlen' := topLevelsFold_length T leaves i
    obtain ⟨extra, hext⟩ := topLevelsFold_prefix T leaves i 12 (by omega)
    have hget : (evalWithAnswerFn T (topLevelsFold leaves 12)).getD i [] =
        (evalWithAnswerFn T (topLevelsFold leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have hw : ((evalWithAnswerFn T (topLevelsFold leaves 12)).getD i []).length = 2 ^ (12 - i) :=
      hfin.1.2 i (by omega)
    have h1 : 1 + i - 1 = i := by omega
    rw [h1, ← hget]
    unfold buildTopLevel
    refine QueriesSat.mapM _ _ (fun c hc => ?_)
    rw [List.mem_range, hw] at hc
    split
    · next h12 =>
      have hi11 : i = 11 := by omega
      subst hi11
      have hc0 : c = 0 := by norm_num at hc; omega
      subst hc0
      rw [nodeHash_root_eq, show 2 ^ (12 - (1 + 11)) + 0 = 1 by norm_num]
      refine sat_projHash _ _ ?_
      simpa only [treeValue, Nat.mul_zero, Nat.zero_add] using hroot
    · next h12 =>
      have hi11 : i < 11 := by omega
      rw [show 12 - i = 11 - i + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)] at hc
      rw [show 1 + i = i + 1 by omega, show 12 - (i + 1) = 11 - i by omega]
      refine QueriesSat.map _ (sat_topNonceSearch T P _ _ _ _ _ 0 (fun k _ hk => ?_))
      exact htrial i c k hi11 hc hk
  · rw [topLevelsFold_succ, evalWithAnswerFn_bind]

end SigGolfCandidate.T3.Security.Wots.Structural
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsStructuralHonest ====
section

namespace ClaudeWCT.W9.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
/-- Top-nonce layer (r3-lean-nonsec): a rejected keygen trial (nonce below the selected one) of a top node, with honest
children. -/
def TopTrial (T : Answers) (x : HashInput) : Prop :=
  ∃ level c k, level < 11 ∧ c < 2 ^ (11 - level) ∧ k < WCT9.honestNonce T 0 0 level c ∧
    x = pad64 (WCT9.merkleNodeInputN 0 0 (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ (∃ p : Extract.Pos, p.Bounded ∧ x = Extract.honestInput T p) ∨ TopTrial T x
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    HonestQuery T (.inl (.inr (Extract.honestInput T p))) := Or.inr (Or.inl ⟨p, hp, rfl⟩)
theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)
theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privatePair tag lay tree position index) := by
  unfold SigGolfCandidate.T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.mask level index) := by
  unfold SigGolfCandidate.T3.mask SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateMac region) := by
  unfold SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)
theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.maskedLevel nodes level) := by
  unfold SigGolfCandidate.T3.maskedLevel SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)
theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateNonce message) := by
  unfold SigGolfCandidate.T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded → x.length = p.len →
      Extract.hdrKey x ≠ bytesLE 16 p.hdr) : Extract.posOf x = none :=
  Extract.posOf_eq_none h
/-- A 64-byte input whose header is an encoding row tweak with any high word (D6: the high word is a witness pad)
decodes to no position: every 64-byte position differs from the row tweak in the low word. -/
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat} {hi : BitVec 64} (hlen : x.length = 64)
    (hx' : Extract.hdrBlock x = bytesLE 16 (WCT9.rowTweakW lay tree leaf hi)) :
    Extract.posOf x = none := by
  have hlow : (rowTweak lay tree leaf).extractLsb' 0 64 = hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    unfold rowTweak; exact BitVec.extractLsb'_append_eq_right
  have hx : Extract.hdrBlock x = bytesLE 16 (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64) := by
    rw [hlow]; exact hx'
  apply posOf_eq_none
  intro p hb hl he
  have hm : (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64).toNat % 256 < 128 := by
    have h1 := append64_marker hi ((rowTweak lay tree leaf).extractLsb' 0 64)
    have h2 := rowTweak_marker lay tree leaf
    unfold tweakMarker at h1 h2
    rw [h1, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    have : (rowTweak lay tree leaf).toNat % 2 ^ 64 % 256 = (rowTweak lay tree leaf).toNat % 256 :=
      Nat.mod_mod_of_dvd _ (by norm_num)
    omega
  -- C4: the row tweak's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock x) := by
    rw [hx, Extract.topLow_bytesLE_iff, append64_lowNat, hlow, hyperWord_toNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT, hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ hm] at he
  have hlo := congrArg (BitVec.extractLsb' 0 64) (bytesLE_injective he)
  rw [BitVec.extractLsb'_append_eq_right] at hlo
  exact Extract.rowTweak_low_ne_hdr lay tree leaf hb (by rw [← hl, hlen]) hlo
theorem posOf_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.posOf (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none :=
  posOf_row_none (lay := lay) (tree := tree) (leaf := leaf) (hi := 1)
    (by rw [← BC.pad64_layerEncodingInputP_zero]; exact BC.layerEncodingRow_length _ _ _ _ _ _ _ _)
    ((BC.hdrBlock_layerEncodingInput lay tree leaf msg counter).trans (by rw [WCT9.rowTweakW_one]))
theorem posOf_layerEncodingP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Extract.posOf (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) = none :=
  posOf_row_none (BC.layerEncodingRow_length lay tree leaf msg counter pad padR hi)
    (BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR hi)
theorem posOf_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Extract.posOf (pad64 (digestInput rho message counter)) = none := by
  unfold digestInput
  apply posOf_eq_none
  intro p hb hl he
  have hlen : (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message)).length = 64 := by
    rw [Cost.pad64_length]; simp only [List.length_append, bytesLE_length]
  -- C4: the digest header's low word is 0, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock
      (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message))) := by
    rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
      Extract.hdrBlock_prefix, Extract.topLow_bytesLE_iff, digestHeader_lowNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT,
    Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix,
    SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
      (by rw [digestHeader_firstByte]; decide)] at he
  have hh := bytesLE_injective he
  cases p with
  | chain lay tree leaf i step => exact (chainHeader_ne_digestHeader _ _ _ _ _ counter).symm hh
  | wctChain index coord child c step =>
      have hn := congrArg (fun x : Digest => x.toNat % 256) hh
      simp only [Extract.Pos.hdr, WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_firstByte,
        digestHeader_firstByte] at hn
      omega
  | wctNode index coord level nd =>
      simp only [Extract.Pos.hdr, WCT9.wctNodeHeader] at hh
      exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
  | leaf lay tree lf => exact digestHeader_ne_leafTweak _ _ _ _ hh
  | node lay tree level nd =>
      simp only [Extract.Pos.hdr] at hh
      by_cases h0 : lay = 0
      · subst h0
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top] at hh
        exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
      · -- C2: a lower node word has marker `128 + heap`, the digest header marker 0.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay ≤ 7 := by revert h0; fin_cases lay <;> decide
        have hhp := Extract.node_heap_lt128 hnd h7
        rw [Extract.merkleTweak_layer_lower h0] at hh
        have hn := congrArg (fun x : Digest => x.toNat % 256) hh
        simp only [digestHeader_firstByte, WCT9.lowerTweak_firstByte hhp] at hn
        omega
  | wctLeaf index coord child => exact (WCT9.ftsLeafHeader_ne_digestHeader _ _ _ _).symm hh
  | forest index => simp only [Extract.Pos.hdr] at hh; exact digestHeader_ne_header _ _ _ _ _ _ hh
theorem sat_layerCounterSearch (T : Answers) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_layerEncoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _
theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Structural.sat_digestSearch_of T _ rho message fun _ => Or.inl (posOf_digest _ _ _)
private theorem canonicalHeader_low (hdr : Digest) :
    (Extract.canonicalHeader (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words]
  unfold SigGolfCandidate.T3M.Extract.canonicalHeader
  split_ifs <;> simp [List.take_append, bytesLE_length]
private theorem low_ne_of_firstByte (x y : BitVec 128)
    (hc : 128 ≤ x.toNat % 256) (hr : y.toNat % 256 < 128) :
    x.extractLsb' 0 64 ≠ y.extractLsb' 0 64 := by
  intro he
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] at hv
  omega
theorem posOf_chain_offgraph (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (hoff : chainHeaderSpill tree leaf i step ≠ 0) :
    Extract.posOf (pad64 (WCT9.chainInputW lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb _ he
  have hlen : (pad64 (WCT9.chainInputW lay tree leaf i step value)).length = 64 := by
    rw [WCT9.chainInputW_padded]; simp [WCT9.chainInputW_length]
  -- C4: a chain header's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock (pad64 (WCT9.chainInputW lay tree leaf i step value))) := by
    rw [WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header, Extract.topLow_bytesLE_iff, Extract.tweakLow_eq_low,
      chainHeader_low, chainHeaderFlaggedLow_toNat]
    have := chainHeaderLow_band lay tree leaf i step
    split_ifs <;> omega
  rw [Extract.hdrKey_of_len64 hlen hT, WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header] at he
  have hn := congrArg (List.take 8) he
  rw [canonicalHeader_low] at hn
  have hp : (bytesLE 16 p.hdr).take 8 = bytesLE 8 (p.hdr.extractLsb' 0 64) := by
    rw [← Extract.Pos.canonicalHeader_eq hb]
    exact canonicalHeader_low _
  rw [hp] at hn
  have hlo := bytesLE_injective hn
  have hbit := chainHeader_offgraph_bit lay tree leaf i step
  rw [if_neg hoff] at hbit
  cases p with
  | chain lay' tree' leaf' i' step' =>
      exact chainHeader_offgraph_low_ne hoff hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega) hlo
  | wctChain index coord child c step' =>
      exact WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ hlo.symm
  | wctNode index coord level nd =>
      exact WCT9.wctNodeHeader_low_ne_chainHeader hb.2.1 _ _ _ _ _ _ _ hlo.symm
  | node lay' tree' level nd =>
      by_cases h0 : lay' = 0
      · -- C4: a top label's low word is below 4096, a chain header's carries type byte 193.
        subst h0
        have hv := congrArg BitVec.toNat hlo
        simp only [Extract.Pos.hdr] at hv
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top_low, topNodeWord_toNat64, chainHeader_low,
          chainHeaderFlaggedLow_toNat] at hv
        have := chainHeaderLow_band lay tree leaf i step
        have := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        split_ifs at hv <;> omega
      · -- C2: a lower node word has bit 55 clear (layer byte `lay' - 1 ≤ 2`), an off-graph chain header has it set.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay' ≤ 7 := by revert h0; fin_cases lay' <;> decide
        have hh := Extract.node_heap_lt128 hnd h7
        rw [hlo] at hbit
        simp only [Extract.Pos.hdr] at hbit
        rw [Extract.merkleTweak_layer_lower h0, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
          WCT9.lowerTweak_toNat hh] at hbit
        have h1 := Nat.mod_lt tree' (show 0 < 2 ^ 32 by decide)
        have h2 : (lay'.val - 1) % 256 ≤ 2 := by have := lay'.isLt; omega
        omega
  | _ =>
      exact low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
        (Extract.Pos.hdr_marker_lt hb (by simp only [Extract.Pos.cls]; (try split) <;> omega)
          (by simp only [Extract.Pos.cls]; (try split) <;> omega)) hlo
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7)
    (hG : WCT9.isG lay i = false := by simp) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.chain lay tree leaf i start count
      (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chain_zero]; exact QueriesSat.pure' _
  | succ count ih =>
      rw [Correctness.chain_add lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_honestChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      rw [hq]
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        have he : Extract.honestInput T (.chain lay tree leaf i (start + count)) =
            pad64 (chainInput lay tree leaf i (start + count)
              (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count))) := by
          simp only [Extract.honestInput]
          rw [WCT9.chainInputW_F hG]
          exact congrArg (fun v => pad64 (chainInput lay tree leaf i (start + count) v))
            (honestChainValueW_eq hG (Or.inr (Or.inr (by omega))))
        rw [← he]
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · refine Or.inl ?_
        rw [← WCT9.chainInputW_F hG]
        exact posOf_chain_offgraph lay tree leaf i (start + count) _ hoff
theorem sat_halfHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (WCT9.halfHash high input) := by
  intro q hq
  have he : SourceReplay.queried T (WCT9.halfHash high input) = [.inl (.inr (pad64 input))] := by
    cases high <;> rfl
  rw [he, List.mem_singleton] at hq
  rw [hq]
  exact h
/-- `sat_chain` for the chains of the current scheme (`chainW`; the chain-0 high half changes only the value after
step 6, which no query reads). -/
theorem sat_chainW (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7) :
    QueriesSat T (HonestQuery T) (WCT9.chainW lay tree leaf i start count
      (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chainW_zero']; exact QueriesSat.pure' _
  | succ count ih =>
      rw [chainW_add' lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      have heval : evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count
          (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) =
          honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count) := by
        unfold honestChainValueW
        rw [eval_chainW_add' T lay tree leaf i 0 start count, Nat.zero_add]
      rw [heval, chainW_one']
      apply sat_halfHash
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        refine Or.inr (Or.inl ⟨.chain lay tree leaf i (start + count), hg, ?_⟩)
        rfl
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
/-! ### Top leaves (campaign T8D: family seeds through `topCoefs`, `buildLeafTop`, `buildTopTree`) -/
theorem sat_topPairsFrom (T : Answers) (first start : Nat) (init : List Digest) :
    QueriesSat T (HonestQuery T) (topPairsFrom first start init) := by
  unfold topPairsFrom
  refine QueriesSat.foldlM_range' _ _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
  unfold topSeedPair
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_topCoefs (T : Answers) (leaf : Nat) : QueriesSat T (HonestQuery T) (topCoefs leaf) := by
  unfold topCoefs
  exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
theorem sat_topFamilyCoefs (T : Answers) (leaf : Nat) (cc : List Digest × Digest) :
    QueriesSat T (HonestQuery T) (topFamilyCoefs leaf cc) := by
  unfold topFamilyCoefs
  split
  · unfold topCoefsK
    exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
  · exact QueriesSat.pure' _
theorem sat_buildLeafTopC (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTopC leaf (Correctness.topCoefList T leaf) digits signatureOnly) := by
  rw [Correctness.buildLeafTopC_eq]
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)) ?_
  · unfold Correctness.topLeafStep
    have hseed : topSeed (Correctness.topCoefList T leaf) leaf i = WCT9.wotsSeed T 0 0 leaf i := by
      rw [WCT9.wotsSeed_top, Correctness.leafSeed_top]; rfl
    rw [hseed]
    have hd := hvalid i hi
    have hw := Mask.width_le (0 : Layer) i
    have hc := Mask.chainCount_le (0 : Layer)
    -- witness stack: the top chain is `chainW 0 0` (G for even i ≤ 52), via the G-aware `sat_chainW`
    simp only [← WCT9.chainW_top_eq]
    have h0 : WCT9.wotsSeed T 0 0 leaf i =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0 := by
      simp [honestChainValueW, WCT9.chainW]
    rw [h0]
    refine QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i 0 _ (by decide) hleaf (by omega) (by omega)) ?_
    have heval : evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 (digits.getD i 0)
        (honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0)) =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) (digits.getD i 0) := by
      have hz : ∀ v, evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 0 v) = v := by
        intro v; simp [WCT9.chainW, evalWithAnswerFn_pure]
      unfold honestChainValueW
      rw [hz]
    rw [heval]
    split
    · exact QueriesSat.pure' _
    · exact QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i _ _ (by decide) hleaf (by omega) (by omega))
        (QueriesSat.pure' _)
  · cases signatureOnly
    · have hr := Correctness.eval_topLeafRows T leaf digits hvalid false
      simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_self] at hr
      have he := Correctness.list_eq_range_map _ (leafEnd T 0 0 leaf) _ hr.1
        (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
      simp only [Bool.false_eq_true, ite_false]
      refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [he, ← WCT9.wotsEnd_top]
      unfold leafHash
      exact sat_projHash _ _ (honestQuery_honest T (.leaf (0 : Layer) 0 leaf) hb)
    · simp only [ite_true]
      exact QueriesSat.pure' _
theorem sat_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine QueriesSat.bind (sat_topCoefs T leaf) ?_
  rw [Correctness.eval_topCoefs]
  have h := sat_buildLeafTopC T leaf digits hvalid signatureOnly hleaf hb
  rw [Correctness.buildLeafTopC_eq] at h
  exact h
theorem honestNonce_top_eq (T : Answers) (level c : Nat) (hl : level < 11) :
    WCT9.honestNonce T 0 0 level c = (evalWithAnswerFn T (topNodeAt (level + 1) (2 ^ (11 - level) + c)
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))).1 := by
  unfold WCT9.honestNonce
  rw [if_pos ⟨rfl, hl⟩, show height (0 : Layer) - level - 1 = 11 - level by simp [height]; omega]
theorem honestQuery_topTrial (T : Answers) (level c k : Nat) (hl : level < 11) (hc : c < 2 ^ (11 - level))
    (hk : k ≤ WCT9.honestNonce T 0 0 level c) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))))) := by
  rw [← WCT9.merkleNodeInputN_top 0]
  rcases Nat.lt_or_ge k (WCT9.honestNonce T 0 0 level c) with hlt | hge
  · exact Or.inr (Or.inr ⟨level, c, k, hl, hc, hlt, rfl⟩)
  · have heq : k = WCT9.honestNonce T 0 0 level c := le_antisymm hk hge
    subst heq
    have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
    refine Or.inr (Or.inl ⟨.node 0 0 level c, ⟨by norm_num, by simp [height]; omega, Or.inl rfl, fun _ => rfl,
      by rw [hh]; exact hc⟩, ?_⟩)
    show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - level - 1) + c)
      (WCT9.honestNonce T 0 0 level c) _ _)
    rw [hh]
    rfl
theorem honestQuery_topRoot (T : Answers) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput 1 0
      (treeValue (WCT9.wotsTree T 0 0) 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 1))))) := by
  refine Or.inr (Or.inl ⟨.node 0 0 11 0, ⟨by norm_num, by simp [height], Or.inl rfl, fun _ => rfl, by simp [height]⟩, ?_⟩)
  show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - 11 - 1) + 0)
    (WCT9.honestNonce T 0 0 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0)) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0 + 1)))
  rw [WCT9.honestNonce_root]
  exact (congrArg pad64 (WCT9.merkleNodeInputN_top 0 1 0 _ _)).symm
theorem sat_buildTopTree (T : Answers) : QueriesSat T (HonestQuery T) buildTopTree := by
  unfold buildTopTree
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (Correctness.TopTreeState T) _ (Correctness.topTreeState_zero T)
    (fun leaf hleaf st hst => ⟨?_, Correctness.eval_topTreeStep T leaf st hst⟩)) ?_
  · have hl' : leaf < 2 ^ 32 := by
      have : 2 ^ height (0 : Layer) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le 0)
      omega
    unfold topTreeStep
    refine QueriesSat.bind (sat_topFamilyCoefs T leaf st.2) ?_
    rw [(Correctness.topTreeStep_coefs T leaf st hst).1]
    exact QueriesSat.bind (sat_buildLeafTopC T leaf [] (Cost.validDigits_nil 0) false hl'
      (Extract.leaf_bounded_of_treeBits (by decide) hleaf)) (QueriesSat.pure' _)
  · rw [(Correctness.eval_topTreeLoop T (2 ^ height 0)).1]
    have hroots : (List.range (2 ^ height 0)).map (Correctness.leafRoot T 0 0) =
        (List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0) := by rw [WCT9.wotsRoot_top]
    have hW : evalWithAnswerFn T (buildTopLevels ((List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0))) =
        WCT9.wotsTree T 0 0 := by unfold WCT9.wotsTree; rw [if_pos rfl]
    rw [hroots]
    apply SigGolfCandidate.T3.Security.Wots.Structural.sat_buildTopLevels T (HonestQuery T) _ (by simp [height])
    · rw [hW]; exact honestQuery_topRoot T
    · intro level c k hl hc hk
      rw [hW] at hk ⊢
      exact honestQuery_topTrial T level c k hl hc (le_of_le_of_eq hk (honestNonce_top_eq T level c hl).symm)
theorem sat_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    QueriesSat T (HonestQuery T) (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) := by
  unfold WCT9.packedSecret
  split
  · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_lowerCoefs (T : Answers) (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    QueriesSat T (HonestQuery T) (WCT9.lowerCoefs lay tree leaf carry) := by
  unfold WCT9.lowerCoefs WCT9.lowerFamCoefs
  split
  · refine QueriesSat.bind (QueriesSat.bind ?_ (QueriesSat.pure' _)) (QueriesSat.pure' _)
    refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_leafRowsF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (WCT9.leafRowsF lay tree leaf digits (WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))) := by
  unfold WCT9.leafRowsF
  refine QueriesSat.foldlM_range _ _ (WCT9.LeafRowsF T lay tree leaf digits) _
    (by simp [WCT9.LeafRowsF])
    (fun i hi rows hrows => ⟨?_, WCT9.leafStepF_inv T hlay tree leaf digits hvalid i hi rows hrows⟩)
  unfold WCT9.leafStepF
  rw [WCT9.lowerFamilySeed_eq T hlay]
  have hd := hvalid i hi
  have hw := Mask.width_le lay i
  have hc := Mask.chainCount_le lay
  rw [← honestChainValueW_zero T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i)]
  refine QueriesSat.bind (sat_chainW T lay tree leaf i 0 (digits.getD i 0) htree hleaf (by omega) (by omega)) ?_
  rw [honestChainValueW_zero, show evalWithAnswerFn T (WCT9.chainW lay tree leaf i 0 (digits.getD i 0)
      (WCT9.wotsSeed T lay tree leaf i)) =
      honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (digits.getD i 0) from rfl]
  exact QueriesSat.bind (sat_chainW T lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
    htree hleaf (by omega) (by omega)) (QueriesSat.pure' _)
theorem sat_buildLeafPF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (carry : List Digest)
    (hcarry : leaf % WCT9.famGrp lay ≠ 0 → carry = WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (WCT9.buildLeafPF lay tree leaf digits carry) := by
  rw [WCT9.buildLeafPF_factor]
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [WCT9.eval_lowerCoefs T hlay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (sat_leafRowsF T hlay tree leaf digits hvalid htree hleaf) ?_
  rw [WCT9.eval_leafRowsF T hlay tree leaf digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  exact sat_halfHash _ _ (honestQuery_honest T (.leaf lay tree leaf) hb)
theorem sat_treeRowsP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.treeRowsP lay tree selected digits) := by
  unfold WCT9.treeRowsP
  refine QueriesSat.foldlM_range _ _ (fun done rows => rows.2.2 = WCT9.treeCarry T lay tree done) _
    (by simp [WCT9.treeCarry]) (fun leaf hleaf rows hrows => ?_)
  have hd : Cost.ValidDigits lay (if leaf = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  have hl' : leaf < 2 ^ 32 := by
    have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  have hcarry := WCT9.carryOk_treeCarry T lay tree leaf
  rw [← hrows] at hcarry
  refine ⟨QueriesSat.bind (sat_buildLeafPF T hlay tree leaf _ hd _ hcarry htree hl'
    (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_, ?_⟩
  · generalize evalWithAnswerFn T (WCT9.buildLeafPF lay tree leaf (if leaf = selected then digits else []) rows.2.2) = x
    obtain ⟨⟨root, values⟩, c⟩ := x
    exact QueriesSat.pure' _
  · simp only [evalWithAnswerFn_bind, WCT9.buildLeafPF_result T hlay tree leaf _ hd _ hcarry, evalWithAnswerFn_pure]
    show WCT9.leafCarryOut T lay tree leaf = WCT9.treeCarry T lay tree (leaf + 1)
    unfold WCT9.treeCarry
    rw [if_neg (show leaf + 1 ≠ 0 by omega), Nat.add_sub_cancel]
/-! ### C2 (FULL): the lower trees fold with `lowerLevel` (`lowerNodeHash`, the half of each heap) -/
def merkleQuery (lay tree heap : Nat) (left right : Digest) : SigGolfCandidate.T3.Spec.Domain :=
  .inl (.inr (pad64 (WCT9.merkleNodeInput lay tree heap left right)))
theorem sat_lowerNodeHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree heap : Nat)
    (left right : Digest) (h : Q (merkleQuery lay tree heap left right)) :
    QueriesSat T Q (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  exact sat_halfHash _ _ h
theorem sat_lowerLevel {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (WCT9.lowerLevel lay tree h level nodes) := by
  unfold WCT9.lowerLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_lowerNodeHash _ _ _ _ _ (hq i (List.mem_range.mp hi)))
def lowerStep (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])
def lowerFold (lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (lowerStep lay tree h) [leaves]
theorem eval_lowerStep (T : Answers) (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (lowerStep lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h level (levels.getD (level - 1) []))] := by
  simp only [lowerStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_lowerSteps_append (T : Answers) (lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (lowerStep lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_lowerStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩
theorem lowerFold_succ (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    lowerFold lay tree h leaves (n + 1) =
      (lowerFold lay tree h leaves n >>= fun state => lowerStep lay tree h state (1 + n)) := by
  unfold lowerFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem lowerFold_length (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (lowerFold lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lowerFold_succ, evalWithAnswerFn_bind, eval_lowerStep, List.length_append, ih]
      simp
theorem lowerFold_prefix (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (lowerFold lay tree h leaves m) =
      evalWithAnswerFn T (lowerFold lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold lowerFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_lowerSteps_append T lay tree h _ _
theorem sat_lowerFold {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h : Nat)
    (leaves : List Digest) (n : Nat) (hn : n ≤ h)
    (hq : ∀ level, level < n → ∀ node,
      node < ((evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD level []).length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node))
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node + 1)))) :
    QueriesSat T Q (lowerFold lay tree h leaves n) := by
  unfold lowerFold
  refine QueriesSat.foldlM_range' 1 n _
    (fun i state => state = evalWithAnswerFn T (lowerFold lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold lowerStep
    refine QueriesSat.bind (sat_lowerLevel _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := lowerFold_length T lay tree h leaves i
    obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves i n (by omega)
    have hget : (evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD i [] =
        (evalWithAnswerFn T (lowerFold lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i (by omega) node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [lowerFold_succ, evalWithAnswerFn_bind]
theorem honestQuery_lowerNode (T : Answers) (lay : Layer) (tree : Nat) (ht : tree < 2 ^ Extract.treeBits lay)
    (level node : Nat) (hlevel : level < height lay) (hroot : lay = 0 ∨ level + 1 < height lay) (hlay : lay ≠ 0)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (merkleQuery lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T hlay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine Or.inr (Or.inl ⟨.node lay tree level node, ⟨by
    have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
    have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
    omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht, by rw [hw, hpow] at hnode; omega⟩, ?_⟩)
  show pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - (level + 1)) + node) _ _) =
    pad64 (WCT9.merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + node) (WCT9.honestNonce T lay tree level node) _ _)
  rw [WCT9.honestInputN_lower T hlay, Nat.sub_sub]
theorem buildLevelsBelow_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    WCT9.buildLevelsBelow tag lay tree h leaves = lowerFold lay tree h leaves (h - 1) := rfl
theorem lowerLevels_eq_fold (lay tree h : Nat) (leaves : List Digest) :
    WCT9.lowerLevels lay tree h leaves = lowerFold lay tree h leaves h := rfl
theorem below_getD (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (level : Nat) (hl : level + 1 < h) :
    (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)).getD level [] =
      (evalWithAnswerFn T (WCT9.lowerLevels lay tree h leaves)).getD level [] := by
  rw [buildLevelsBelow_eq_fold, lowerLevels_eq_fold]
  obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves (h - 1) h (by omega)
  have hlen := lowerFold_length T lay tree h leaves (h - 1)
  rw [hext, List.getD_append _ _ _ _ (by omega)]
theorem sat_buildTreeP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.buildTreeP_factor]
  refine QueriesSat.bind (sat_treeRowsP T hlay tree selected digits hvalid htree ht) ?_
  obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP T hlay tree selected digits hvalid
  have hroots := Correctness.list_eq_range_map _ _ _ hlen hroot
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [hroots, buildLevelsBelow_eq_fold]
  refine sat_lowerFold _ _ _ _ _ (by omega) ?_
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level (by omega)
  rw [← buildLevelsBelow_eq_fold 3, hg] at hnode
  rw [← buildLevelsBelow_eq_fold 3]
  have hwt : WCT9.wotsTree T lay tree = evalWithAnswerFn T (WCT9.lowerLevels lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))) := by
    unfold WCT9.wotsTree; rw [if_neg hlay]
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hlay (by rw [hwt]; exact hnode)
  rw [hwt] at this
  simp only [treeValue, hg]
  exact this
theorem honestQuery_of_fts (T : Answers) {index : Nat} (hindex : index < 2 ^ 31) {q : SigGolfCandidate.T3.Spec.Domain}
    (h : ClaudeWCT.WCT9.Wots.FtsHonestQuery T index q) : HonestQuery T q := by
  rcases q with (coin | x) | (tweak | other)
  · exact h.elim
  · obtain ⟨pos, hb, hx⟩ := Extract.ftsHonestQuery_pos hindex h
    exact Or.inr (Or.inl ⟨pos, hb, hx⟩)
  · trivial
  · trivial
theorem sat_signForest (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.signForest index output) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_signForest T index output).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTopTree T) ?_
  generalize evalWithAnswerFn T buildTopTree = levels
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun level _ => sat_maskedLevel T _ _) (QueriesSat.pure' _)
theorem sat_keygen (T : Answers) : QueriesSat T (HonestQuery T) keygen := by
  unfold keygen
  refine QueriesSat.bind (sat_keygenPayload T) ?_
  generalize evalWithAnswerFn T keygenPayload = x
  obtain ⟨publicKey, region⟩ := x
  exact QueriesSat.bind (sat_privateMac T _) (QueriesSat.pure' _)
theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)
theorem sat_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (signTop cache leaf digits) := by
  unfold signTop
  refine QueriesSat.bind (sat_buildLeafTop T leaf digits hvalid true (by omega)
    (Extract.leaf_bounded_of_treeBits (by decide) (by simpa [height] using hleaf))) ?_
  generalize evalWithAnswerFn T (buildLeafTop leaf digits true) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.bind (sat_topPath T cache leaf hleaf) (QueriesSat.pure' _)
theorem sat_signLayers (T : Answers) (cache : Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, QueriesSat T (HonestQuery T) (WCT9.signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _; exact QueriesSat.pure' _
  | succ n ih =>
      intro hn msg
      simp only [WCT9.signLayersBC]
      refine QueriesSat.bind (sat_layerCounterSearch T _ _ _ _ _ _) ?_
      generalize hs : evalWithAnswerFn T (WCT9.layerCounterSearch _ _ _ _ _ _) = r
      cases r with
      | none =>
          dsimp only
          split_ifs with hn0
          · subst hn0
            refine QueriesSat.bind (sat_signTop T cache _ _ (Mask.dummyDigits_spec 0).2 ?_) (QueriesSat.pure' _)
            have := route_leaf_bound index (Fin.ofNat 4 0)
            exact this
          · exact QueriesSat.pure' _
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (WCT9.layerCounterSearch_some T _ _ _ msg _ 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          dsimp only
          split_ifs with hn0
          · subst hn0
            refine QueriesSat.bind (sat_signTop T cache _ digits hvalid ?_) (QueriesSat.pure' _)
            have := route_leaf_bound index (Fin.ofNat 4 0)
            exact this
          · have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
              rw [h] at hv
              exact hn0 hv.symm
            refine QueriesSat.bind (sat_buildTreeP T hl0 _ _ digits hvalid (Mask.route_tree_lt index hindex _)
              (Extract.route_tree_treeBits index hindex _)) ?_
            refine QueriesSat.bind (ih (by omega) _) ?_
            generalize evalWithAnswerFn T (WCT9.signLayersBC cache index n _) = r
            rcases r with _ | r <;> exact QueriesSat.pure' _
theorem sat_signPayload (T : Answers) (cache : Cache) (message : Message) :
    QueriesSat T (HonestQuery T) (signPayload cache message) := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine QueriesSat.bind (sat_privateNonce T message) ?_
  refine QueriesSat.bind (sat_digestSearch T _ _ _ _) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn T (privateNonce message)) message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact QueriesSat.pure' _
  · dsimp only
    have hindex : WCT9.digestIndex output < 2 ^ 31 := Nat.mod_lt _ (by decide)
    refine QueriesSat.bind (sat_signForest T _ hindex _) ?_
    refine QueriesSat.bind (sat_signLayers T cache _ hindex 4 le_rfl _) ?_
    generalize evalWithAnswerFn T (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
    rcases pieces with _ | pieces <;> exact QueriesSat.pure' _
theorem sat_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    QueriesSat T (HonestQuery T) (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine QueriesSat.bind (sat_privateMac T _) ?_
  split
  · exact sat_signPayload T _ _
  · exact QueriesSat.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Structural

-- Stage 2 (C2/C3, #866): this paired copy of `Structural` is #866's `Structural` section with Ghost's paired
-- `HonestQuery` (paired honest inputs/bounds) and without the unpaired signer lemmas.
namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
/-- Top-nonce layer (r3-lean-nonsec): a rejected keygen trial (nonce below the selected one) of a top node, with honest
children. -/
def TopTrial (T : Answers) (x : HashInput) : Prop :=
  ∃ level c k, level < 11 ∧ c < 2 ^ (11 - level) ∧ k < WCT9.honestNonce T 0 0 level c ∧
    x = pad64 (WCT9.merkleNodeInputN 0 0 (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ (∃ p : Extract.Pos, Extract.Paired.Bounded p ∧ x = Extract.Paired.honestInput T p) ∨
      TopTrial T x
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : Extract.Paired.Bounded p) :
    HonestQuery T (.inl (.inr (Extract.Paired.honestInput T p))) := Or.inr (Or.inl ⟨p, hp, rfl⟩)
theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)
theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privatePair tag lay tree position index) := by
  unfold SigGolfCandidate.T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.mask level index) := by
  unfold SigGolfCandidate.T3.mask SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateMac region) := by
  unfold SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)
theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.maskedLevel nodes level) := by
  unfold SigGolfCandidate.T3.maskedLevel SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)
theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateNonce message) := by
  unfold SigGolfCandidate.T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded → x.length = p.len →
      Extract.hdrKey x ≠ bytesLE 16 p.hdr) : Extract.posOf x = none :=
  Extract.posOf_eq_none h
/-- A 64-byte input whose header is an encoding row tweak with any high word (D6: the high word is a witness pad)
decodes to no position: every 64-byte position differs from the row tweak in the low word. -/
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat} {hi : BitVec 64} (hlen : x.length = 64)
    (hx' : Extract.hdrBlock x = bytesLE 16 (WCT9.rowTweakW lay tree leaf hi)) :
    Extract.posOf x = none := by
  have hlow : (rowTweak lay tree leaf).extractLsb' 0 64 = hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    unfold rowTweak; exact BitVec.extractLsb'_append_eq_right
  have hx : Extract.hdrBlock x = bytesLE 16 (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64) := by
    rw [hlow]; exact hx'
  apply posOf_eq_none
  intro p hb hl he
  have hm : (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64).toNat % 256 < 128 := by
    have h1 := append64_marker hi ((rowTweak lay tree leaf).extractLsb' 0 64)
    have h2 := rowTweak_marker lay tree leaf
    unfold tweakMarker at h1 h2
    rw [h1, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    have : (rowTweak lay tree leaf).toNat % 2 ^ 64 % 256 = (rowTweak lay tree leaf).toNat % 256 :=
      Nat.mod_mod_of_dvd _ (by norm_num)
    omega
  -- C4: the row tweak's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock x) := by
    rw [hx, Extract.topLow_bytesLE_iff, append64_lowNat, hlow, hyperWord_toNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT, hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ hm] at he
  have hlo := congrArg (BitVec.extractLsb' 0 64) (bytesLE_injective he)
  rw [BitVec.extractLsb'_append_eq_right] at hlo
  exact Extract.rowTweak_low_ne_hdr lay tree leaf hb (by rw [← hl, hlen]) hlo
theorem posOf_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.posOf (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none :=
  posOf_row_none (lay := lay) (tree := tree) (leaf := leaf) (hi := 1)
    (by rw [← BC.pad64_layerEncodingInputP_zero]; exact BC.layerEncodingRow_length _ _ _ _ _ _ _ _)
    ((BC.hdrBlock_layerEncodingInput lay tree leaf msg counter).trans (by rw [WCT9.rowTweakW_one]))
theorem posOf_layerEncodingP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Extract.posOf (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) = none :=
  posOf_row_none (BC.layerEncodingRow_length lay tree leaf msg counter pad padR hi)
    (BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR hi)
theorem posOf_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Extract.posOf (pad64 (digestInput rho message counter)) = none := by
  unfold digestInput
  apply posOf_eq_none
  intro p hb hl he
  have hlen : (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message)).length = 64 := by
    rw [Cost.pad64_length]; simp only [List.length_append, bytesLE_length]
  -- C4: the digest header's low word is 0, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock
      (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message))) := by
    rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
      Extract.hdrBlock_prefix, Extract.topLow_bytesLE_iff, digestHeader_lowNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT,
    Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix,
    SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
      (by rw [digestHeader_firstByte]; decide)] at he
  have hh := bytesLE_injective he
  cases p with
  | chain lay tree leaf i step => exact (chainHeader_ne_digestHeader _ _ _ _ _ counter).symm hh
  | wctChain index coord child c step =>
      have hn := congrArg (fun x : Digest => x.toNat % 256) hh
      simp only [Extract.Pos.hdr, WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_firstByte,
        digestHeader_firstByte] at hn
      omega
  | wctNode index coord level nd =>
      simp only [Extract.Pos.hdr, WCT9.wctNodeHeader] at hh
      exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
  | leaf lay tree lf => exact digestHeader_ne_leafTweak _ _ _ _ hh
  | node lay tree level nd =>
      simp only [Extract.Pos.hdr] at hh
      by_cases h0 : lay = 0
      · subst h0
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top] at hh
        exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
      · -- C2: a lower node word has marker `128 + heap`, the digest header marker 0.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay ≤ 7 := by revert h0; fin_cases lay <;> decide
        have hhp := Extract.node_heap_lt128 hnd h7
        rw [Extract.merkleTweak_layer_lower h0] at hh
        have hn := congrArg (fun x : Digest => x.toNat % 256) hh
        simp only [digestHeader_firstByte, WCT9.lowerTweak_firstByte hhp] at hn
        omega
  | wctLeaf index coord child => exact (WCT9.ftsLeafHeader_ne_digestHeader _ _ _ _).symm hh
  | forest index => simp only [Extract.Pos.hdr] at hh; exact digestHeader_ne_header _ _ _ _ _ _ hh
theorem sat_layerCounterSearch (T : Answers) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_layerEncoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _
theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Structural.sat_digestSearch_of T _ rho message fun _ => Or.inl (posOf_digest _ _ _)
private theorem canonicalHeader_low (hdr : Digest) :
    (Extract.canonicalHeader (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words]
  unfold SigGolfCandidate.T3M.Extract.canonicalHeader
  split_ifs <;> simp [List.take_append, bytesLE_length]
private theorem low_ne_of_firstByte (x y : BitVec 128)
    (hc : 128 ≤ x.toNat % 256) (hr : y.toNat % 256 < 128) :
    x.extractLsb' 0 64 ≠ y.extractLsb' 0 64 := by
  intro he
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] at hv
  omega
theorem posOf_chain_offgraph (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (hoff : chainHeaderSpill tree leaf i step ≠ 0) :
    Extract.posOf (pad64 (WCT9.chainInputW lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb _ he
  have hlen : (pad64 (WCT9.chainInputW lay tree leaf i step value)).length = 64 := by
    rw [WCT9.chainInputW_padded]; simp [WCT9.chainInputW_length]
  -- C4: a chain header's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock (pad64 (WCT9.chainInputW lay tree leaf i step value))) := by
    rw [WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header, Extract.topLow_bytesLE_iff, Extract.tweakLow_eq_low,
      chainHeader_low, chainHeaderFlaggedLow_toNat]
    have := chainHeaderLow_band lay tree leaf i step
    split_ifs <;> omega
  rw [Extract.hdrKey_of_len64 hlen hT, WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header] at he
  have hn := congrArg (List.take 8) he
  rw [canonicalHeader_low] at hn
  have hp : (bytesLE 16 p.hdr).take 8 = bytesLE 8 (p.hdr.extractLsb' 0 64) := by
    rw [← Extract.Pos.canonicalHeader_eq hb]
    exact canonicalHeader_low _
  rw [hp] at hn
  have hlo := bytesLE_injective hn
  have hbit := chainHeader_offgraph_bit lay tree leaf i step
  rw [if_neg hoff] at hbit
  cases p with
  | chain lay' tree' leaf' i' step' =>
      exact chainHeader_offgraph_low_ne hoff hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega) hlo
  | wctChain index coord child c step' =>
      exact WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ hlo.symm
  | wctNode index coord level nd =>
      exact WCT9.wctNodeHeader_low_ne_chainHeader hb.2.1 _ _ _ _ _ _ _ hlo.symm
  | node lay' tree' level nd =>
      by_cases h0 : lay' = 0
      · -- C4: a top label's low word is below 4096, a chain header's carries type byte 193.
        subst h0
        have hv := congrArg BitVec.toNat hlo
        simp only [Extract.Pos.hdr] at hv
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top_low, topNodeWord_toNat64, chainHeader_low,
          chainHeaderFlaggedLow_toNat] at hv
        have := chainHeaderLow_band lay tree leaf i step
        have := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        split_ifs at hv <;> omega
      · -- C2: a lower node word has bit 55 clear (layer byte `lay' - 1 ≤ 2`), an off-graph chain header has it set.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay' ≤ 7 := by revert h0; fin_cases lay' <;> decide
        have hh := Extract.node_heap_lt128 hnd h7
        rw [hlo] at hbit
        simp only [Extract.Pos.hdr] at hbit
        rw [Extract.merkleTweak_layer_lower h0, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
          WCT9.lowerTweak_toNat hh] at hbit
        have h1 := Nat.mod_lt tree' (show 0 < 2 ^ 32 by decide)
        have h2 : (lay'.val - 1) % 256 ≤ 2 := by have := lay'.isLt; omega
        omega
  | _ =>
      exact low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
        (Extract.Pos.hdr_marker_lt hb (by simp only [Extract.Pos.cls]; (try split) <;> omega)
          (by simp only [Extract.Pos.cls]; (try split) <;> omega)) hlo
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7)
    (hG : WCT9.isG lay i = false := by simp) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.chain lay tree leaf i start count
      (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chain_zero]; exact QueriesSat.pure' _
  | succ count ih =>
      rw [Correctness.chain_add lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_honestChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      rw [hq]
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        have he : Extract.honestInput T (.chain lay tree leaf i (start + count)) =
            pad64 (chainInput lay tree leaf i (start + count)
              (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count))) := by
          simp only [Extract.honestInput]
          rw [WCT9.chainInputW_F hG]
          exact congrArg (fun v => pad64 (chainInput lay tree leaf i (start + count) v))
            (honestChainValueW_eq hG (Or.inr (Or.inr (by omega))))
        rw [← he]
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · refine Or.inl ?_
        rw [← WCT9.chainInputW_F hG]
        exact posOf_chain_offgraph lay tree leaf i (start + count) _ hoff
theorem sat_halfHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (WCT9.halfHash high input) := by
  intro q hq
  have he : SourceReplay.queried T (WCT9.halfHash high input) = [.inl (.inr (pad64 input))] := by
    cases high <;> rfl
  rw [he, List.mem_singleton] at hq
  rw [hq]
  exact h
/-- `sat_chain` for the chains of the current scheme (`chainW`; the chain-0 high half changes only the value after
step 6, which no query reads). -/
theorem sat_chainW (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7) :
    QueriesSat T (HonestQuery T) (WCT9.chainW lay tree leaf i start count
      (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chainW_zero']; exact QueriesSat.pure' _
  | succ count ih =>
      rw [chainW_add' lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      have heval : evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count
          (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) =
          honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count) := by
        unfold honestChainValueW
        rw [eval_chainW_add' T lay tree leaf i 0 start count, Nat.zero_add]
      rw [heval, chainW_one']
      apply sat_halfHash
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        refine Or.inr (Or.inl ⟨.chain lay tree leaf i (start + count), hg, ?_⟩)
        rfl
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
/-! ### Top leaves (campaign T8D: family seeds through `topCoefs`, `buildLeafTop`, `buildTopTree`) -/
theorem sat_topPairsFrom (T : Answers) (first start : Nat) (init : List Digest) :
    QueriesSat T (HonestQuery T) (topPairsFrom first start init) := by
  unfold topPairsFrom
  refine QueriesSat.foldlM_range' _ _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
  unfold topSeedPair
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_topCoefs (T : Answers) (leaf : Nat) : QueriesSat T (HonestQuery T) (topCoefs leaf) := by
  unfold topCoefs
  exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
theorem sat_topFamilyCoefs (T : Answers) (leaf : Nat) (cc : List Digest × Digest) :
    QueriesSat T (HonestQuery T) (topFamilyCoefs leaf cc) := by
  unfold topFamilyCoefs
  split
  · unfold topCoefsK
    exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
  · exact QueriesSat.pure' _
theorem sat_buildLeafTopC (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTopC leaf (Correctness.topCoefList T leaf) digits signatureOnly) := by
  rw [Correctness.buildLeafTopC_eq]
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)) ?_
  · unfold Correctness.topLeafStep
    have hseed : topSeed (Correctness.topCoefList T leaf) leaf i = WCT9.wotsSeed T 0 0 leaf i := by
      rw [WCT9.wotsSeed_top, Correctness.leafSeed_top]; rfl
    rw [hseed]
    have hd := hvalid i hi
    have hw := Mask.width_le (0 : Layer) i
    have hc := Mask.chainCount_le (0 : Layer)
    -- witness stack: the top chain is `chainW 0 0` (G for even i ≤ 52), via the G-aware `sat_chainW`
    simp only [← WCT9.chainW_top_eq]
    have h0 : WCT9.wotsSeed T 0 0 leaf i =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0 := by
      simp [honestChainValueW, WCT9.chainW]
    rw [h0]
    refine QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i 0 _ (by decide) hleaf (by omega) (by omega)) ?_
    have heval : evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 (digits.getD i 0)
        (honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0)) =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) (digits.getD i 0) := by
      have hz : ∀ v, evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 0 v) = v := by
        intro v; simp [WCT9.chainW, evalWithAnswerFn_pure]
      unfold honestChainValueW
      rw [hz]
    rw [heval]
    split
    · exact QueriesSat.pure' _
    · exact QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i _ _ (by decide) hleaf (by omega) (by omega))
        (QueriesSat.pure' _)
  · cases signatureOnly
    · have hr := Correctness.eval_topLeafRows T leaf digits hvalid false
      simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_self] at hr
      have he := Correctness.list_eq_range_map _ (leafEnd T 0 0 leaf) _ hr.1
        (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
      simp only [Bool.false_eq_true, ite_false]
      refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [he, ← WCT9.wotsEnd_top]
      unfold leafHash
      exact sat_projHash _ _ (honestQuery_honest T (.leaf (0 : Layer) 0 leaf) hb)
    · simp only [ite_true]
      exact QueriesSat.pure' _
theorem sat_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine QueriesSat.bind (sat_topCoefs T leaf) ?_
  rw [Correctness.eval_topCoefs]
  have h := sat_buildLeafTopC T leaf digits hvalid signatureOnly hleaf hb
  rw [Correctness.buildLeafTopC_eq] at h
  exact h
theorem honestNonce_top_eq (T : Answers) (level c : Nat) (hl : level < 11) :
    WCT9.honestNonce T 0 0 level c = (evalWithAnswerFn T (topNodeAt (level + 1) (2 ^ (11 - level) + c)
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))).1 := by
  unfold WCT9.honestNonce
  rw [if_pos ⟨rfl, hl⟩, show height (0 : Layer) - level - 1 = 11 - level by simp [height]; omega]
theorem honestQuery_topTrial (T : Answers) (level c k : Nat) (hl : level < 11) (hc : c < 2 ^ (11 - level))
    (hk : k ≤ WCT9.honestNonce T 0 0 level c) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))))) := by
  rw [← WCT9.merkleNodeInputN_top 0]
  rcases Nat.lt_or_ge k (WCT9.honestNonce T 0 0 level c) with hlt | hge
  · exact Or.inr (Or.inr ⟨level, c, k, hl, hc, hlt, rfl⟩)
  · have heq : k = WCT9.honestNonce T 0 0 level c := le_antisymm hk hge
    subst heq
    have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
    refine Or.inr (Or.inl ⟨.node 0 0 level c, ⟨by norm_num, by simp [height]; omega, Or.inl rfl, fun _ => rfl,
      by rw [hh]; exact hc⟩, ?_⟩)
    show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - level - 1) + c)
      (WCT9.honestNonce T 0 0 level c) _ _)
    rw [hh]
    rfl
theorem honestQuery_topRoot (T : Answers) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput 1 0
      (treeValue (WCT9.wotsTree T 0 0) 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 1))))) := by
  refine Or.inr (Or.inl ⟨.node 0 0 11 0, ⟨by norm_num, by simp [height], Or.inl rfl, fun _ => rfl, by simp [height]⟩, ?_⟩)
  show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - 11 - 1) + 0)
    (WCT9.honestNonce T 0 0 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0)) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0 + 1)))
  rw [WCT9.honestNonce_root]
  exact (congrArg pad64 (WCT9.merkleNodeInputN_top 0 1 0 _ _)).symm
theorem sat_buildTopTree (T : Answers) : QueriesSat T (HonestQuery T) buildTopTree := by
  unfold buildTopTree
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (Correctness.TopTreeState T) _ (Correctness.topTreeState_zero T)
    (fun leaf hleaf st hst => ⟨?_, Correctness.eval_topTreeStep T leaf st hst⟩)) ?_
  · have hl' : leaf < 2 ^ 32 := by
      have : 2 ^ height (0 : Layer) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le 0)
      omega
    unfold topTreeStep
    refine QueriesSat.bind (sat_topFamilyCoefs T leaf st.2) ?_
    rw [(Correctness.topTreeStep_coefs T leaf st hst).1]
    exact QueriesSat.bind (sat_buildLeafTopC T leaf [] (Cost.validDigits_nil 0) false hl'
      (Extract.leaf_bounded_of_treeBits (by decide) hleaf)) (QueriesSat.pure' _)
  · rw [(Correctness.eval_topTreeLoop T (2 ^ height 0)).1]
    have hroots : (List.range (2 ^ height 0)).map (Correctness.leafRoot T 0 0) =
        (List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0) := by rw [WCT9.wotsRoot_top]
    have hW : evalWithAnswerFn T (buildTopLevels ((List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0))) =
        WCT9.wotsTree T 0 0 := by unfold WCT9.wotsTree; rw [if_pos rfl]
    rw [hroots]
    apply SigGolfCandidate.T3.Security.Wots.Structural.sat_buildTopLevels T (HonestQuery T) _ (by simp [height])
    · rw [hW]; exact honestQuery_topRoot T
    · intro level c k hl hc hk
      rw [hW] at hk ⊢
      exact honestQuery_topTrial T level c k hl hc (le_of_le_of_eq hk (honestNonce_top_eq T level c hl).symm)
theorem sat_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    QueriesSat T (HonestQuery T) (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) := by
  unfold WCT9.packedSecret
  split
  · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_lowerCoefs (T : Answers) (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    QueriesSat T (HonestQuery T) (WCT9.lowerCoefs lay tree leaf carry) := by
  unfold WCT9.lowerCoefs WCT9.lowerFamCoefs
  split
  · refine QueriesSat.bind (QueriesSat.bind ?_ (QueriesSat.pure' _)) (QueriesSat.pure' _)
    refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_leafRowsF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (WCT9.leafRowsF lay tree leaf digits (WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))) := by
  unfold WCT9.leafRowsF
  refine QueriesSat.foldlM_range _ _ (WCT9.LeafRowsF T lay tree leaf digits) _
    (by simp [WCT9.LeafRowsF])
    (fun i hi rows hrows => ⟨?_, WCT9.leafStepF_inv T hlay tree leaf digits hvalid i hi rows hrows⟩)
  unfold WCT9.leafStepF
  rw [WCT9.lowerFamilySeed_eq T hlay]
  have hd := hvalid i hi
  have hw := Mask.width_le lay i
  have hc := Mask.chainCount_le lay
  rw [← honestChainValueW_zero T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i)]
  refine QueriesSat.bind (sat_chainW T lay tree leaf i 0 (digits.getD i 0) htree hleaf (by omega) (by omega)) ?_
  rw [honestChainValueW_zero, show evalWithAnswerFn T (WCT9.chainW lay tree leaf i 0 (digits.getD i 0)
      (WCT9.wotsSeed T lay tree leaf i)) =
      honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (digits.getD i 0) from rfl]
  exact QueriesSat.bind (sat_chainW T lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
    htree hleaf (by omega) (by omega)) (QueriesSat.pure' _)
theorem sat_buildLeafPF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (carry : List Digest)
    (hcarry : leaf % WCT9.famGrp lay ≠ 0 → carry = WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (WCT9.buildLeafPF lay tree leaf digits carry) := by
  rw [WCT9.buildLeafPF_factor]
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [WCT9.eval_lowerCoefs T hlay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (sat_leafRowsF T hlay tree leaf digits hvalid htree hleaf) ?_
  rw [WCT9.eval_leafRowsF T hlay tree leaf digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  exact sat_halfHash _ _ (honestQuery_honest T (.leaf lay tree leaf) hb)
theorem sat_treeRowsP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.treeRowsP lay tree selected digits) := by
  unfold WCT9.treeRowsP
  refine QueriesSat.foldlM_range _ _ (fun done rows => rows.2.2 = WCT9.treeCarry T lay tree done) _
    (by simp [WCT9.treeCarry]) (fun leaf hleaf rows hrows => ?_)
  have hd : Cost.ValidDigits lay (if leaf = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  have hl' : leaf < 2 ^ 32 := by
    have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  have hcarry := WCT9.carryOk_treeCarry T lay tree leaf
  rw [← hrows] at hcarry
  refine ⟨QueriesSat.bind (sat_buildLeafPF T hlay tree leaf _ hd _ hcarry htree hl'
    (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_, ?_⟩
  · generalize evalWithAnswerFn T (WCT9.buildLeafPF lay tree leaf (if leaf = selected then digits else []) rows.2.2) = x
    obtain ⟨⟨root, values⟩, c⟩ := x
    exact QueriesSat.pure' _
  · simp only [evalWithAnswerFn_bind, WCT9.buildLeafPF_result T hlay tree leaf _ hd _ hcarry, evalWithAnswerFn_pure]
    show WCT9.leafCarryOut T lay tree leaf = WCT9.treeCarry T lay tree (leaf + 1)
    unfold WCT9.treeCarry
    rw [if_neg (show leaf + 1 ≠ 0 by omega), Nat.add_sub_cancel]
/-! ### C2 (FULL): the lower trees fold with `lowerLevel` (`lowerNodeHash`, the half of each heap) -/
def merkleQuery (lay tree heap : Nat) (left right : Digest) : SigGolfCandidate.T3.Spec.Domain :=
  .inl (.inr (pad64 (WCT9.merkleNodeInput lay tree heap left right)))
theorem sat_lowerNodeHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree heap : Nat)
    (left right : Digest) (h : Q (merkleQuery lay tree heap left right)) :
    QueriesSat T Q (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  exact sat_halfHash _ _ h
theorem sat_lowerLevel {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (WCT9.lowerLevel lay tree h level nodes) := by
  unfold WCT9.lowerLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_lowerNodeHash _ _ _ _ _ (hq i (List.mem_range.mp hi)))
def lowerStep (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])
def lowerFold (lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (lowerStep lay tree h) [leaves]
theorem eval_lowerStep (T : Answers) (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (lowerStep lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h level (levels.getD (level - 1) []))] := by
  simp only [lowerStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_lowerSteps_append (T : Answers) (lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (lowerStep lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_lowerStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩
theorem lowerFold_succ (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    lowerFold lay tree h leaves (n + 1) =
      (lowerFold lay tree h leaves n >>= fun state => lowerStep lay tree h state (1 + n)) := by
  unfold lowerFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem lowerFold_length (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (lowerFold lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lowerFold_succ, evalWithAnswerFn_bind, eval_lowerStep, List.length_append, ih]
      simp
theorem lowerFold_prefix (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (lowerFold lay tree h leaves m) =
      evalWithAnswerFn T (lowerFold lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold lowerFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_lowerSteps_append T lay tree h _ _
theorem sat_lowerFold {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h : Nat)
    (leaves : List Digest) (n : Nat) (hn : n ≤ h)
    (hq : ∀ level, level < n → ∀ node,
      node < ((evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD level []).length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node))
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node + 1)))) :
    QueriesSat T Q (lowerFold lay tree h leaves n) := by
  unfold lowerFold
  refine QueriesSat.foldlM_range' 1 n _
    (fun i state => state = evalWithAnswerFn T (lowerFold lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold lowerStep
    refine QueriesSat.bind (sat_lowerLevel _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := lowerFold_length T lay tree h leaves i
    obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves i n (by omega)
    have hget : (evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD i [] =
        (evalWithAnswerFn T (lowerFold lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i (by omega) node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [lowerFold_succ, evalWithAnswerFn_bind]
theorem honestQuery_lowerNode (T : Answers) (lay : Layer) (tree : Nat) (ht : tree < 2 ^ Extract.treeBits lay)
    (level node : Nat) (hlevel : level < height lay) (hroot : lay = 0 ∨ level + 1 < height lay) (hlay : lay ≠ 0)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (merkleQuery lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T hlay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine Or.inr (Or.inl ⟨.node lay tree level node, ⟨by
    have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
    have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
    omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht, by rw [hw, hpow] at hnode; omega⟩, ?_⟩)
  show pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - (level + 1)) + node) _ _) =
    pad64 (WCT9.merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + node) (WCT9.honestNonce T lay tree level node) _ _)
  rw [WCT9.honestInputN_lower T hlay, Nat.sub_sub]
theorem buildLevelsBelow_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    WCT9.buildLevelsBelow tag lay tree h leaves = lowerFold lay tree h leaves (h - 1) := rfl
theorem lowerLevels_eq_fold (lay tree h : Nat) (leaves : List Digest) :
    WCT9.lowerLevels lay tree h leaves = lowerFold lay tree h leaves h := rfl
theorem below_getD (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (level : Nat) (hl : level + 1 < h) :
    (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)).getD level [] =
      (evalWithAnswerFn T (WCT9.lowerLevels lay tree h leaves)).getD level [] := by
  rw [buildLevelsBelow_eq_fold, lowerLevels_eq_fold]
  obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves (h - 1) h (by omega)
  have hlen := lowerFold_length T lay tree h leaves (h - 1)
  rw [hext, List.getD_append _ _ _ _ (by omega)]
theorem sat_buildTreeP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.buildTreeP_factor]
  refine QueriesSat.bind (sat_treeRowsP T hlay tree selected digits hvalid htree ht) ?_
  obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP T hlay tree selected digits hvalid
  have hroots := Correctness.list_eq_range_map _ _ _ hlen hroot
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [hroots, buildLevelsBelow_eq_fold]
  refine sat_lowerFold _ _ _ _ _ (by omega) ?_
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level (by omega)
  rw [← buildLevelsBelow_eq_fold 3, hg] at hnode
  rw [← buildLevelsBelow_eq_fold 3]
  have hwt : WCT9.wotsTree T lay tree = evalWithAnswerFn T (WCT9.lowerLevels lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))) := by
    unfold WCT9.wotsTree; rw [if_neg hlay]
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hlay (by rw [hwt]; exact hnode)
  rw [hwt] at this
  simp only [treeValue, hg]
  exact this
theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTopTree T) ?_
  generalize evalWithAnswerFn T buildTopTree = levels
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun level _ => sat_maskedLevel T _ _) (QueriesSat.pure' _)
theorem sat_keygen (T : Answers) : QueriesSat T (HonestQuery T) keygen := by
  unfold keygen
  refine QueriesSat.bind (sat_keygenPayload T) ?_
  generalize evalWithAnswerFn T keygenPayload = x
  obtain ⟨publicKey, region⟩ := x
  exact QueriesSat.bind (sat_privateMac T _) (QueriesSat.pure' _)
theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)
theorem sat_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (signTop cache leaf digits) := by
  unfold signTop
  refine QueriesSat.bind (sat_buildLeafTop T leaf digits hvalid true (by omega)
    (Extract.leaf_bounded_of_treeBits (by decide) (by simpa [height] using hleaf))) ?_
  generalize evalWithAnswerFn T (buildLeafTop leaf digits true) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.bind (sat_topPath T cache leaf hleaf) (QueriesSat.pure' _)
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Stage 2 (C3, #866): the retained-prefix chain queries what `WCT9.chainW` queries. -/
theorem queried_chainPrefixes (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    queried T (chainPrefixes lay tree leaf i start count value) =
      queried T (WCT9.chainW lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
      rw [lower_chainW_succ_first]
      simp only [chainPrefixes,queried_bind,queried_pure,List.append_nil,ih]

theorem sat_chainPrefixes (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2^40) (hleaf : leaf < 2^32) (hi : i < 2^24) (hcount : start+count≤7) :
    QueriesSat T (HonestQuery T) (chainPrefixes lay tree leaf i start count
      (honestChainValueW T lay tree leaf i (wotsSeed T lay tree leaf i) start)) := by
  intro q hq
  change q ∈ queried T (chainPrefixes lay tree leaf i start count
    (honestChainValueW T lay tree leaf i (wotsSeed T lay tree leaf i) start)) at hq
  rw [queried_chainPrefixes] at hq
  exact sat_chainW T lay tree leaf i start count htree hleaf hi hcount q hq

theorem sat_buildLeafPrefixes (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL T lay tree (famOf lay leaf))
    (htree : tree < 2^40) (hleaf : leaf < 2^32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [eval_lowerCoefs T hlay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (QueriesSat.mapM _ _ (fun i hi => ?_)) ?_
  · rw [lowerFamilySeed_eq T hlay, ← honestChainValueW_zero T lay tree leaf i (wotsSeed T lay tree leaf i)]
    exact sat_chainPrefixes T lay tree leaf i 0 (maxDigit lay i) htree hleaf
      (by have := Mask.chainCount_le lay; have := List.mem_range.mp hi; omega)
      (by have := Mask.width_le lay i; omega)
  · rw [Correctness.eval_mapM]
    simp only [lowerFamilySeed_eq T hlay]
    change QueriesSat T (HonestQuery T) (do
      let root ← lowerLeafHash lay tree leaf
        ((List.range (chainCount lay)).map fun i =>
          ((prefixRows T lay tree leaf).getD i []).getD (maxDigit lay i) 0)
      pure ((root,prefixRows T lay tree leaf),leafCarryOut T lay tree leaf))
    have he : (List.range (chainCount lay)).map (fun i =>
        ((prefixRows T lay tree leaf).getD i []).getD (maxDigit lay i) 0) =
        (List.range (chainCount lay)).map (wotsEnd T lay tree leaf) := by
      apply List.map_congr_left
      intro i hi
      exact prefixRows_getD T lay tree leaf i _ (List.mem_range.mp hi) (by omega)
    rw [he]
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    rw [WCT9.lowerLeafHash_eq]
    unfold WCT9.lowerHash
    exact sat_halfHash _ _ (honestQuery_honest T (.leaf lay tree leaf) hb)
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sat_canonical_search (T : Answers) (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, QueriesSat T (HonestQuery T)
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [CanonicalPolicy.layerCounterSearchAt]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_layerEncoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _

theorem sat_sharedDigestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (sharedDigestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [sharedDigestSearch]
      refine QueriesSat.bind (sat_publicHash _ (Or.inl (posOf_digest rho message (BitVec.ofNat 32 counter)))) ?_
      split
      · exact QueriesSat.pure' _
      · exact ih _

theorem sat_searchPreparedLayers (T : Answers) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (prepared : PreparedRoots) (forest : PairRoot) :
    QueriesSat T (HonestQuery T) (searchPreparedLayers cache index prepared forest) := by
  unfold searchPreparedLayers
  refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
  cases hs : evalWithAnswerFn T (CanonicalPolicy.layerCounterSearchAt 0
      (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2
      (route index 0).1 (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2)
      0 (searchLimit 0)) with
  | none => exact QueriesSat.pure' _
  | some found =>
      obtain ⟨counter,digits,low⟩ := found
      have hd := (canonical_search_valid_credit T 0 _ _ _ _ _ _ counter digits low
        (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).1
      dsimp only
      split
      · exact QueriesSat.pure' _
      · refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
        split
        · split
          · exact QueriesSat.pure' _
          · refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
            split
            · split
              · exact QueriesSat.pure' _
              · refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
                split
                · exact QueriesSat.bind (sat_signTop T cache _ digits hd (route_leaf_bound index 0))
                    (QueriesSat.pure' _)
                · exact QueriesSat.pure' _
            · exact QueriesSat.pure' _
        · exact QueriesSat.pure' _
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sat_prefixTreeRows (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (htree : tree < 2^40) (ht : tree < 2^Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (prefixTreeRows lay tree selected) := by
  unfold prefixTreeRows
  refine QueriesSat.foldlM_range _ _ (fun done rows => rows.2.2 = treeCarry T lay tree done) _
    (by simp [treeCarry]) (fun leaf hleaf rows hrows => ?_)
  have hl : leaf < 2^32 := by
    have : 2^height lay ≤ 2^12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  have hc := carryOk_treeCarry T lay tree leaf
  rw [←hrows] at hc
  refine ⟨?_,?_⟩
  · by_cases hs : leaf = selected
    · simp only [if_pos hs]
      refine QueriesSat.bind (sat_buildLeafPrefixes T hlay tree leaf rows.2.2 hc htree hl
        (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_
      generalize evalWithAnswerFn T (buildLeafPrefixes lay tree leaf rows.2.2) = value
      rcases value with ⟨⟨root,prefixes⟩,carry⟩
      exact QueriesSat.pure' _
    · simp only [if_neg hs]
      refine QueriesSat.bind (sat_buildLeafPF T hlay tree leaf [] (Cost.validDigits_nil lay)
        rows.2.2 hc htree hl (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_
      generalize evalWithAnswerFn T (buildLeafPF lay tree leaf [] rows.2.2) = value
      rcases value with ⟨⟨root,values⟩,carry⟩
      exact QueriesSat.bind (QueriesSat.pure' _) (QueriesSat.pure' _)
  · by_cases hs : leaf = selected
    · simp only [if_pos hs,evalWithAnswerFn_bind,buildLeafPrefixes_result T hlay tree leaf _ hc,
        evalWithAnswerFn_pure]
      unfold treeCarry
      rw [if_neg (show leaf+1≠0 by omega),Nat.add_sub_cancel]
    · simp only [if_neg hs,evalWithAnswerFn_bind,
        buildLeafPF_result T hlay tree leaf [] (Cost.validDigits_nil lay) _ hc,evalWithAnswerFn_pure]
      unfold treeCarry
      rw [if_neg (show leaf+1≠0 by omega),Nat.add_sub_cancel]

theorem sat_buildTreePrefixes (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (htree : tree < 2^40) (ht : tree < 2^Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (buildTreePrefixes lay tree selected) := by
  rw [buildTreePrefixes_factor]
  refine QueriesSat.bind (sat_prefixTreeRows T hlay tree selected htree ht) ?_
  have hr := eval_prefixTreeRows T hlay tree selected
  have hroots := Correctness.list_eq_range_map _ _ _ hr.1 hr.2.1
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  -- C2 (#866): the lower levels are `lowerLevel` folds (as in `sat_buildTreeP`).
  rw [hroots, buildLevelsBelow_eq_fold]
  refine sat_lowerFold _ _ _ _ _ (by omega) ?_
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level (by omega)
  rw [← buildLevelsBelow_eq_fold 3, hg] at hnode
  rw [← buildLevelsBelow_eq_fold 3]
  have hwt : WCT9.wotsTree T lay tree = evalWithAnswerFn T (WCT9.lowerLevels lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))) := by
    unfold WCT9.wotsTree; rw [if_neg hlay]
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hlay (by rw [hwt]; exact hnode)
  rw [hwt] at this
  simp only [treeValue, hg]
  exact this

theorem sat_prepareRoots (T : Answers) (index : Nat) (hi : index<2^31) :
    QueriesSat T (HonestQuery T) (prepareRoots index) := by
  unfold prepareRoots
  refine QueriesSat.bind (sat_buildTreePrefixes T (by decide : (1 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 1) (Extract.route_tree_treeBits index hi 1)) ?_
  refine QueriesSat.bind (sat_buildTreePrefixes T (by decide : (2 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 2) (Extract.route_tree_treeBits index hi 2)) ?_
  exact QueriesSat.bind (sat_buildTreePrefixes T (by decide : (3 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 3) (Extract.route_tree_treeBits index hi 3)) (QueriesSat.pure' _)
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

theorem sat_ftsCoefs (coord : Coord) :
    QueriesSat T (HonestQuery T) (ftsCoefs index coord.val) := by
  unfold ftsCoefs
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun j hj acc _ => ⟨?_, trivial⟩)
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)

#check sat_ftsCoefs

include hidx in
theorem sat_fts_chain (coord : Coord) (child : Child) (t : Fin 6) (start count : Nat)
    (hcount : start+count ≤ 4) :
    QueriesSat T (HonestQuery T)
      (ClaudeWCT.WCT9.chain index coord.val child.val t.val start count
        (ftsChainValue T index coord child t start)) := by
  induction count with
  | zero => rw [chain_zero']; exact QueriesSat.pure' _
  | succ count ih =>
      rw [chain_add index coord.val child.val t.val start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_ftsChain]
      intro q hq
      rw [ClaudeWCT.WCT9.Wots.queried_chain_one, List.mem_singleton] at hq
      subst hq
      refine Or.inr (Or.inl ⟨.wctChain index coord.val child.val t.val (start+count),
        ⟨hidx,coord.isLt,child.isLt,t.isLt,by omega⟩,?_⟩)
      exact (Extract.honestInput_ofFts T index (.chain coord child t (start+count)) (by change start+count<4;omega)).symm

#check sat_fts_chain

include hidx in
theorem sat_fts_childStep (coord : Coord) (child : Child) (word : Rank)
    (t : Fin 6) (rows : List Digest × List Digest) :
    QueriesSat T (HonestQuery T)
      (childStep index coord.val child.val word (List.ofFn (ftsCoef T index coord.val)) rows t) := by
  unfold childStep
  have hd:=wordDigit_le_four word t
  have hz : ftsFamilySeed (List.ofFn (ftsCoef T index coord.val)) child.val t.val=
      ftsChainValue T index coord child t 0 := rfl
  simp only []
  rw [hz]
  refine QueriesSat.bind (sat_fts_chain T index hidx coord child t 0 _ (by omega)) ?_
  rw [eval_ftsChain,Nat.zero_add]
  exact QueriesSat.bind (sat_fts_chain T index hidx coord child _ _ _ (by omega)) (QueriesSat.pure' _)

#check sat_fts_childStep

include hidx in
theorem sat_fts_childRows (coord : Coord) (child : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (childRows index coord.val child.val word (List.ofFn (ftsCoef T index coord.val))) := by
  unfold childRows
  refine QueriesSat.foldlM_list _ _ (fun _ _ => True) _ trivial (fun i hi rows _ => ⟨?_,trivial⟩)
  have hi6:i<6 := by simpa using hi
  simp only [List.getElem_finRange,Fin.cast_mk]
  exact sat_fts_childStep T index hidx coord child word ⟨i,hi6⟩ rows

#check sat_fts_childRows

include hidx in
theorem sat_fts_buildChild (coord : Coord) (child : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (buildChildH (128 + Extract.Paired.physical coord.val child.val) index coord.val child.val word
        (List.ofFn (ftsCoef T index coord.val))
        (Extract.Paired.pads T index coord.val (Extract.Paired.physical coord.val child.val/64)).1) := by
  rw [buildChildH_factor]
  refine QueriesSat.bind (sat_fts_childRows T index hidx coord child word) ?_
  rw [eval_childRows_ends T index coord.val child.val word]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [ClaudeWCT.W9.T3M.WctExtract.leafHashH_eq_ftsHash]
  refine ClaudeWCT.WCT9.Wots.Structural.sat_ftsHash T _ _ ?_
  refine Or.inr (Or.inl ⟨.wctLeaf index coord.val child.val,⟨hidx,coord.isLt,child.isLt⟩,?_⟩)
  have he : List.ofFn (fun t : Fin 6 => chainEnd T index coord.val child.val t) =
      Extract.wctEnds T index coord.val child.val := by
    unfold Extract.wctEnds
    apply congrArg List.ofFn
    funext t
    rfl
  change pad64 (Extract.wctLeafInputP _ _ _ _ _) = pad64 (Extract.wctLeafInputP _ _ _ _ _)
  rw [he]

 #check sat_fts_buildChild

theorem physical_raw (first : Bool) (j : Nat) (hj:j<128) :
    SharedForest.physicalChild first (SharedForest.rawChild first j)=j := by
  cases first <;> simp only [SharedForest.physicalChild,SharedForest.rawChild,Bool.false_eq_true,↓reduceIte] <;> omega

 #check physical_raw

include hidx in
theorem sat_sharedRows (coord : Coord) (selected : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (SharedForest.sharedRows (Extract.Paired.first coord.val) index coord.val selected word
        (List.ofFn (ftsCoef T index coord.val)) (Extract.Paired.pads T index coord.val)) := by
  unfold SharedForest.sharedRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j hj rows _ => ⟨?_,trivial⟩)
  have hr:=SharedForest.rawChild_lt (Extract.Paired.first coord.val) j hj
  have hc:=sat_fts_buildChild T index hidx coord ⟨_,hr⟩ word
  simp only [Extract.Paired.physical,physical_raw _ j hj] at hc
  exact QueriesSat.bind hc (QueriesSat.pure' _)

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

 include hidx in
theorem honest_sharedNode_input (coord : Coord) (heap : Nat)
    (hcut:SharedForest.heapCut (Extract.Paired.first coord.val) ≤ heap) (hh:heap<128) :
    HonestQuery T (.inl (.inr (pad64 (wctTopInput coord.val index heap
      ((Extract.Paired.nodes T index coord.val).getD (2*heap) 0)
      (if 4≤heap ∧ heap<8 then (Extract.Paired.pads T index coord.val (heap/2-2)).2 else 0)
      ((Extract.Paired.nodes T index coord.val).getD (2*heap+1) 0))))) := by
  have h2:2≤heap := (SharedForest.heapCut_bounds _).1.trans hcut
  obtain ⟨hL,hN,hH⟩:=Extract.heap_decomp h2 hh
  have hused : Extract.Paired.first coord.val=true → Extract.heapLevel heap<5 := by
    intro hf
    have h4:4≤heap := by simpa only [SharedForest.heapCut,hf,if_true] using hcut
    have hlog:2≤Nat.log 2 heap := Nat.le_log_of_pow_le (by decide) h4
    unfold Extract.heapLevel;omega
  refine Or.inr (Or.inl ⟨.wctNode index coord.val (Extract.heapLevel heap) (Extract.heapNode heap),
    ⟨⟨hidx,coord.isLt,hL,hN⟩,hused⟩,?_⟩)
  have hsub:7-Extract.heapLevel heap-1=6-Extract.heapLevel heap := by omega
  rw [hsub] at hH hN
  have he : Extract.heapLevel heap=4 ↔ 4≤heap ∧ heap<8 := by
    have hlo:2^(6-Extract.heapLevel heap)≤heap := by omega
    have hhi:heap<2*2^(6-Extract.heapLevel heap) := by omega
    generalize Extract.heapLevel heap=L at hL hlo hhi ⊢
    interval_cases L <;> norm_num at hlo hhi ⊢ <;> omega
  simp only [Extract.Paired.honestInput,hH,he]

 include hidx in
theorem sat_sharedNode (coord : Coord) (heap : Nat)
    (hcut:SharedForest.heapCut (Extract.Paired.first coord.val) ≤ heap) (hh:heap<128) :
    QueriesSat T (HonestQuery T)
      (SharedForest.sharedNode (Extract.Paired.first coord.val) coord.val index heap
        (Extract.Paired.pads T index coord.val)
        ((Extract.Paired.nodes T index coord.val).getD (2*heap) 0)
        ((Extract.Paired.nodes T index coord.val).getD (2*heap+1) 0)) := by
  have hq:=honest_sharedNode_input T index hidx coord heap hcut hh
  unfold SharedForest.sharedNode
  split_ifs with h4 h8 hf
  · unfold SharedForest.sharedOuterHash
    rw [if_neg (by omega : ¬(4≤heap ∧ heap<8))] at hq
    split_ifs
    · exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq
    · exact ClaudeWCT.WCT9.Wots.Structural.sat_highHash T _ hq
  · rw [if_pos (show 4≤heap ∧ heap<8 by omega)] at hq
    exact ClaudeWCT.WCT9.Wots.Structural.sat_highHash T _ hq
  · rw [if_pos (show 4≤heap ∧ heap<8 by omega)] at hq
    exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq
  · rw [if_neg (by omega : ¬(4≤heap ∧ heap<8)),wctTopInput_zero] at hq
    rw [nodeHashH_eq]
    exact ClaudeWCT.WCT9.Wots.Structural.sat_ftsHash T _ _ hq

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

 theorem sharedNodes_actual (coord : Coord) :
    SharedForest.sharedNodes T (Extract.Paired.first coord.val) index coord.val
      (Extract.Paired.pads T index coord.val)=Extract.Paired.nodes T index coord.val := by
  fin_cases coord <;> simp only [Extract.Paired.nodes, Extract.Paired.first, SharedForest.firstNodes, SharedForest.secondNodes]
  all_goals norm_num
  all_goals first | rfl | (congr 1;funext b;simp only [Extract.Paired.pads,Extract.Paired.first,SharedForest.firstNodes];rfl)

theorem sharedHeap_arithmetic (cut done : Nat) (hcut : 2 ≤ cut) (hd : done < 128-cut) :
    cut ≤ 127-done ∧ 127-done < 128 ∧ 128-(128-cut) ≤ 127-done := by omega

theorem sharedHeap_other_arithmetic (done j : Nat) (hd : done < 128)
    (hj : 128-(done+1) ≤ j) (hne : j ≠ 127-done) : 128-done ≤ j := by omega

/-- Arithmetic side conditions of one `sat_sharedHeap` step, kept out of the step's large context so `omega`
never compares the heap-array atoms there. -/
theorem sharedHeap_child_arithmetic (cut done : Nat) (hcut : 2 ≤ cut) (hd : done < 128-cut) :
    128-done ≤ 2*(127-done) ∧ 128-done ≤ 2*(127-done)+1 ∧ 127-done < 256 := by omega

 include hidx in
set_option maxHeartbeats 800000 in
theorem sat_sharedHeap (coord : Coord) :
    QueriesSat T (HonestQuery T)
      (SharedForest.sharedHeap (Extract.Paired.first coord.val) index coord.val
        (Extract.Paired.pads T index coord.val)
        (SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
          (Extract.Paired.pads T index coord.val))) := by
  have hg:=SharedForest.sharedNodes_graph T (Extract.Paired.first coord.val) index coord.val
    (Extract.Paired.pads T index coord.val)
  rw [sharedNodes_actual T index coord] at hg
  obtain ⟨hsize,hleaf,hnode⟩:=hg
  have hcut:=SharedForest.heapCut_bounds (Extract.Paired.first coord.val)
  unfold SharedForest.sharedHeap
  rw [show (if Extract.Paired.first coord.val = true then 124 else 126) =
      128-SharedForest.heapCut (Extract.Paired.first coord.val) by
    cases hf : Extract.Paired.first coord.val <;> rfl]
  change QueriesSat T (HonestQuery T) ((List.range' (SharedForest.heapCut (Extract.Paired.first coord.val))
    (128-SharedForest.heapCut (Extract.Paired.first coord.val))).reverse.foldlM _ _)
  refine QueriesSat.foldlM_list _ _ (ClaudeWCT.WCT9.Wots.Structural.HeapAgree (Extract.Paired.nodes T index coord.val)) _ ?_ ?_
  · refine ⟨by simp [SharedForest.sharedLeaves],?_⟩
    intro j hj
    by_cases hj':j<256
    · simp only [Array.getD_eq_getD_getElem?,List.getElem?_toArray,←List.getD_eq_getElem?_getD]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
        List.length_replicate,←hleaf j hj hj']
      simp only [Array.getD_eq_getD_getElem?]
    · have h1 : ((List.replicate 128 (0:Digest)++
          SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
            (Extract.Paired.pads T index coord.val)).toArray).getD j 0=0 := by
        simp only [Array.getD_eq_getD_getElem?,List.getElem?_toArray]
        rw [List.getElem?_eq_none (by simp [SharedForest.sharedLeaves];omega)]
        rfl
      have h2:(Extract.Paired.nodes T index coord.val).getD j 0=0 := by
        simp only [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [h1,h2]
  · intro done hdone nodes ⟨hsz,hagree⟩
    have hd:done<128-SharedForest.heapCut (Extract.Paired.first coord.val) := by
      simpa only [List.length_reverse,List.length_range'] using hdone
    rw [SharedForest.shared_heap_order _ done hd]
    obtain ⟨ha,hb,hc⟩ := sharedHeap_arithmetic _ _ hcut.1 hd
    obtain ⟨hl2,hr2,hs⟩ := sharedHeap_child_arithmetic _ _ hcut.1 hd
    have hl:nodes.getD (2*(127-done)) 0=(Extract.Paired.nodes T index coord.val).getD (2*(127-done)) 0 :=
      hagree (2*(127-done)) hl2
    have hr:nodes.getD (2*(127-done)+1) 0=(Extract.Paired.nodes T index coord.val).getD (2*(127-done)+1) 0 :=
      hagree (2*(127-done)+1) hr2
    refine ⟨?_,?_⟩
    · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [hl,hr]
      exact sat_sharedNode T index hidx coord (127-done) ha hb
    · simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      refine ⟨by rw [Array.size_set!,hsz],?_⟩
      intro j hj
      by_cases he:j=127-done
      · subst he
        rw [getD_set_self nodes (127-done) _ (by rw [hsz]; exact hs),hl,hr]
        exact (hnode (127-done) ha hb hc).symm
      · rw [getD_set_other nodes _ _ _ (Ne.symm he)]
        exact hagree j (sharedHeap_other_arithmetic done j (lt_of_lt_of_le hd (Nat.sub_le _ _)) hj he)

 theorem sharedRows_roots (coord : Coord) (selected : Child) (word : Rank) :
    (evalWithAnswerFn T (SharedForest.sharedRows (Extract.Paired.first coord.val) index coord.val
      selected word (List.ofFn (ftsCoef T index coord.val)) (Extract.Paired.pads T index coord.val))).1=
      SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
        (Extract.Paired.pads T index coord.val) := by
  obtain ⟨hlen,hroot,-⟩:=SharedForest.eval_sharedRows T (Extract.Paired.first coord.val) index coord.val
    selected word (Extract.Paired.pads T index coord.val)
  apply List.ext_getElem (by simpa only [SharedForest.sharedLeaves,List.length_ofFn] using hlen)
  intro j hj hk
  simpa only [SharedForest.sharedLeaves,List.getD_eq_getElem _ _ hj,List.getElem_ofFn] using hroot j (by omega)

 include hidx in
theorem sat_sharedCoordinate (coord : Coord) (selected : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (SharedForest.buildSharedCoordinate (Extract.Paired.first coord.val) index coord.val selected word
        (Extract.Paired.pads T index coord.val)) := by
  unfold SharedForest.buildSharedCoordinate
  refine QueriesSat.bind (sat_ftsCoefs T index coord) ?_
  rw [eval_ftsCoefs]
  change QueriesSat T (HonestQuery T) (SharedForest.sharedRows _ _ _ _ _ _ _ >>= _)
  refine QueriesSat.bind (sat_sharedRows T index hidx coord selected word) ?_
  rw [sharedRows_roots]
  exact QueriesSat.bind (sat_sharedHeap T index hidx coord) (QueriesSat.pure' _)

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

 include hidx in
theorem sat_buildPair (pair : Fin 4) (s : SharedForest.Selection) (aWord bWord : Rank) :
    QueriesSat T (HonestQuery T) (SharedForest.buildPair index pair.val s aWord bWord
      (Extract.Paired.pairPrev T index pair.val)) := by
  have ha:=sat_sharedCoordinate T index hidx ⟨2*pair.val,by have:=pair.isLt;omega⟩
    (SharedForest.firstChild s) aWord
  have hA:SharedForest.buildSharedCoordinate true index (2*pair.val) (SharedForest.firstChild s) aWord
      (fun _=>Extract.Paired.pairPrev T index pair.val)=
    SharedForest.buildSharedCoordinate (Extract.Paired.first (2*pair.val)) index (2*pair.val)
      (SharedForest.firstChild s) aWord (Extract.Paired.pads T index (2*pair.val)) := by
    have hf : Extract.Paired.first (2*pair.val) = true := by
      simp only [Extract.Paired.first, decide_eq_true_eq]
      have := pair.isLt
      omega
    rw [hf]
    congr 1
    funext branch
    simp only [Extract.Paired.pads, if_neg (show 2*pair.val ≠ 8 by have := pair.isLt;omega),hf,if_true,
      Nat.mul_div_cancel_left pair.val (by decide : 0<2)]
  rw [←hA] at ha
  unfold SharedForest.buildPair
  refine QueriesSat.bind ha ?_
  rw [SharedForest.buildSharedCoordinate_result]
  have hb:=sat_sharedCoordinate T index hidx ⟨2*pair.val+1,by have:=pair.isLt;omega⟩
    (SharedForest.secondChild s) bWord
  have hB:SharedForest.buildSharedCoordinate false index (2*pair.val+1) (SharedForest.secondChild s) bWord
      (SharedForest.nodesPair (SharedForest.sharedNodes T true index (2*pair.val)
        (fun _=>Extract.Paired.pairPrev T index pair.val)))=
    SharedForest.buildSharedCoordinate (Extract.Paired.first (2*pair.val+1)) index (2*pair.val+1)
      (SharedForest.secondChild s) bWord (Extract.Paired.pads T index (2*pair.val+1)) := by
    have hf : Extract.Paired.first (2*pair.val+1) = false := by
      simp only [Extract.Paired.first, decide_eq_false_iff_not]
      omega
    rw [hf]
    congr 1
    funext branch
    simp only [Extract.Paired.pads, if_neg (show 2*pair.val+1 ≠ 8 by omega),hf,Bool.false_eq_true,if_false]
    rw [show (2*pair.val+1)/2 = pair.val by omega]
    unfold SharedForest.firstNodes
    rfl
  rw [←hB] at hb
  exact QueriesSat.bind hb (QueriesSat.pure' _)

 include hidx in
theorem sat_buildSingleton (s : Child) (word : Rank) :
    QueriesSat T (HonestQuery T) (SharedForest.buildSingleton index s word (Extract.Paired.pairPrev T index 4)) := by
  unfold SharedForest.buildSingleton
  have hs := sat_sharedCoordinate T index hidx 8 s word
  have hf : Extract.Paired.first 8 = false := by decide
  have hp : Extract.Paired.pads T index 8 = (fun _ => Extract.Paired.pairPrev T index 4) := by
    funext branch
    unfold Extract.Paired.pads
    rw [if_pos rfl]
  change QueriesSat T (HonestQuery T)
    (SharedForest.buildSharedCoordinate (Extract.Paired.first 8) index 8 s word (Extract.Paired.pads T index 8)) at hs
  rw [hf,hp] at hs
  exact QueriesSat.bind hs (QueriesSat.pure' _)

 include hidx in
theorem sat_buildForest (selected : SharedForest.ForestSelection) (words : SharedForest.ForestWords) :
    QueriesSat T (HonestQuery T) (SharedForest.buildForest index selected words) := by
  have hfour:List.finRange 4=[0,1,2,3] := by decide
  have h0 : Extract.Paired.pairPrev T index 0 = ftsStart := by unfold Extract.Paired.pairPrev;rfl
  have hstep : ∀ n, Extract.Paired.pairPrev T index (n+1) =
      SharedForest.expectedPairRoot T index n (Extract.Paired.pairPrev T index n) := by
    intro n
    conv_lhs => unfold Extract.Paired.pairPrev
  unfold SharedForest.buildForest
  rw [hfour]
  simp only [List.foldlM_cons,List.foldlM_nil,bind_assoc,pure_bind]
  have h := sat_buildPair T index hidx 0 (selected.pairs 0) (words.first 0) (words.second 0)
  change QueriesSat T (HonestQuery T)
    (SharedForest.buildPair index 0 (selected.pairs 0) (words.first 0) (words.second 0)
      (Extract.Paired.pairPrev T index 0)) at h
  rw [h0] at h
  refine QueriesSat.bind h ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←h0,←hstep 0]
  refine QueriesSat.bind (sat_buildPair T index hidx 1 _ _ _) ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←hstep 1]
  refine QueriesSat.bind (sat_buildPair T index hidx 2 _ _ _) ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←hstep 2]
  refine QueriesSat.bind (sat_buildPair T index hidx 3 _ _ _) ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←hstep 3]
  exact QueriesSat.bind (sat_buildSingleton T index hidx selected.singleton words.singleton) (QueriesSat.pure' _)

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sat_signFromOutput (T : Answers) (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine QueriesSat.bind (sat_buildForest T (digestIndex output) (digestIndex_lt output)
    (forestSelectionFromOutput output) (forestWordsFromOutput output)) ?_
  refine QueriesSat.bind (sat_prepareRoots T (digestIndex output) (digestIndex_lt output)) ?_
  refine QueriesSat.bind (sat_searchPreparedLayers T cache _ _ _) ?_
  generalize evalWithAnswerFn T (searchPreparedLayers cache _ _ _) = found
  rcases found with _ | result <;> exact QueriesSat.pure' _

theorem sat_signPayload (T : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine QueriesSat.bind (sat_privateNonce T message) ?_
  refine QueriesSat.bind (sat_sharedDigestSearch T _ _ _ _) ?_
  generalize evalWithAnswerFn T (sharedDigestSearch (evalWithAnswerFn T (privateNonce message))
    message 0 digestAttemptLimit) = found
  rcases found with _ | ⟨counter,output⟩
  · exact QueriesSat.pure' _
  · refine QueriesSat.bind (sat_signFromOutput T cache _ counter output) ?_
    generalize evalWithAnswerFn T (signFromOutput cache _ counter output) = result
    rcases result with _ | w <;> exact QueriesSat.pure' _

theorem sat_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    QueriesSat T (HonestQuery T) (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine QueriesSat.bind (sat_privateMac T _) ?_
  split
  · exact sat_signPayload T _ _
  · exact QueriesSat.pure' _

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural
end
-- ==== merged from T3_Secc_WotsReferenceInputs ====
section

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs keygen verifyP expandB buildFts buildTree signPayload
def allQueries {ι α : Type} {spec : OracleSpec ι} (computation : OracleComp spec α) : Set ι :=
  OracleComp.construct (fun _ => (∅ : Set ι)) (fun input _ next => {input} ∪ ⋃ u, next u) computation
theorem allQueries_pure {ι α : Type} {spec : OracleSpec ι} (value : α) :
    allQueries (pure value : OracleComp spec α) = ∅ := rfl
theorem allQueries_query_bind {ι α : Type} {spec : OracleSpec ι} (input : ι)
    (next : spec.Range input → OracleComp spec α) :
    allQueries (liftM (spec.query input) >>= next) = {input} ∪ ⋃ u, allQueries (next u) := by
  simp only [allQueries, OracleComp.construct_query_bind]
theorem mem_allQueries_query_bind {ι α : Type} {spec : OracleSpec ι} {input : ι}
    {next : spec.Range input → OracleComp spec α} {query : ι}
    (h : query ∈ allQueries (liftM (spec.query input) >>= next)) :
    query = input ∨ ∃ u, query ∈ allQueries (next u) := by
  rw [allQueries_query_bind] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_iUnion.mp h)
theorem recorded_mem_allQueries {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec ProbComp)
    (computation : OracleComp spec α) (result : α × List ι)
    (hr : result ∈ support (simulateQ impl (SphincsSecurity.QueryCap.recorded computation))) :
    ∀ query ∈ result.2, query ∈ allQueries computation := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind] at hr
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨answer, -, tail, htail, rfl⟩ := hr
      intro query hq
      rw [allQueries_query_bind]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr (Set.mem_iUnion.mpr ⟨answer, ih answer tail htail query hq⟩)
theorem allQueries_run_subset {ι α : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (computation : OracleComp spec α) (budget : Nat) :
    allQueries (SphincsSecurity.QueryCap.run selected computation budget) ⊆ allQueries computation := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      rw [SphincsSecurity.QueryCap.run_pure, allQueries_pure]
      exact Set.empty_subset _
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind, allQueries_query_bind]
      intro query hq
      by_cases hs : selected input
      · rw [if_pos hs] at hq
        cases budget with
        | zero => exact absurd hq (by rw [allQueries_pure]; exact id)
        | succ remaining =>
            rcases mem_allQueries_query_bind hq with rfl | ⟨u, hu⟩
            · exact Or.inl rfl
            · exact Or.inr (Set.mem_iUnion.mpr ⟨u, ih u remaining hu⟩)
      · rw [if_neg hs] at hq
        rcases mem_allQueries_query_bind hq with rfl | ⟨u, hu⟩
        · exact Or.inl rfl
        · exact Or.inr (Set.mem_iUnion.mpr ⟨u, ih u budget hu⟩)
theorem allQueries_bind {ι α β : Type} {spec : OracleSpec ι} (first : OracleComp spec α)
    (next : α → OracleComp spec β) (query : ι) (h : query ∈ allQueries (first >>= next)) :
    query ∈ allQueries first ∨ ∃ value ∈ support first, query ∈ allQueries (next value) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      rw [pure_bind] at h
      exact Or.inr ⟨value, by simp, h⟩
  | query_bind input rest ih =>
      rw [bind_assoc] at h
      rcases mem_allQueries_query_bind h with rfl | ⟨u, hu⟩
      · exact Or.inl (by rw [allQueries_query_bind]; exact Or.inl rfl)
      · rcases ih u hu with hl | ⟨value, hv, hq⟩
        · exact Or.inl (by rw [allQueries_query_bind]; exact Or.inr (Set.mem_iUnion.mpr ⟨u, hl⟩))
        · refine Or.inr ⟨value, ?_, hq⟩
          rw [mem_support_bind_iff]
          exact ⟨u, by simp, hv⟩
theorem allQueries_map {ι α β : Type} {spec : OracleSpec ι} (f : α → β) (computation : OracleComp spec α)
    (query : ι) (h : query ∈ allQueries (f <$> computation)) : query ∈ allQueries computation := by
  rw [map_eq_bind_pure_comp] at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact h
  · exact absurd h (by simp [Function.comp_def, allQueries_pure])
theorem ticks_allQueries (n : Nat) (query : RefWorld.Domain) (h : query ∈ allQueries (ticks n)) :
    query = .inr () := by
  induction n with
  | zero => exact absurd h (by simp [ticks, allQueries_pure])
  | succ n ih =>
      rw [ticks_succ] at h
      rcases mem_allQueries_query_bind h with rfl | ⟨_, hu⟩
      · rfl
      · exact ih hu
theorem hashInputs_bind_left {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    hashInputs first ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input rest ih =>
      rw [bind_assoc, SphincsSecurity.Concrete.hashInputs_query_bind, SphincsSecurity.Concrete.hashInputs_query_bind]
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · left
        cases input <;> exact hx
      · right
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨u, -, hu⟩ := hx
        exact ⟨u, Finset.mem_univ _, ih u hu⟩
theorem hashInputs_bind_of_mem {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (value : α) (hv : value ∈ support first) :
    hashInputs (next value) ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value' =>
      rw [mem_support_pure_iff] at hv
      subst hv
      rw [pure_bind]
  | query_bind input rest ih =>
      rw [mem_support_bind_iff] at hv
      obtain ⟨u, -, hu⟩ := hv
      rw [bind_assoc]
      exact (ih u hu).trans (SphincsSecurity.Concrete.hashInputs_next_subset input (fun x => rest x >>= next) u)
theorem tableRun_query_bind {α : Type} (t : FullGame.FullTable) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) :
    Derivation.tableRun t ((liftM (T3.Spec.query input) >>= next : M α)) =
      (Derivation.tableHandler t input >>= fun answer => Derivation.tableRun t (next answer)) := by
  unfold Derivation.tableRun
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl
theorem tableRun_bind {α β : Type} (t : FullGame.FullTable) (first : M α) (next : α → M β) :
    Derivation.tableRun t (first >>= next) =
      (Derivation.tableRun t first >>= fun value => Derivation.tableRun t (next value)) := by
  unfold Derivation.tableRun
  rw [simulateQ_bind]
theorem hashInputs_tableRun_sourceRecord {α : Type} (t : FullGame.FullTable) (program : M α)
    (state : LazyPrivate.State) :
    hashInputs (Derivation.tableRun t (FirstHit.sourceRecord program state)) =
      hashInputs (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [FirstHit.sourceRecord_pure]
      unfold Derivation.tableRun
      simp only [simulateQ_pure, SphincsSecurity.Concrete.hashInputs_pure]
  | query_bind input next ih =>
      rw [tableRun_sourceRecord_query_bind, tableRun_query_bind]
      rcases input with input | c
      · rw [tableHandler_world, SphincsSecurity.Concrete.hashInputs_query_bind,
          SphincsSecurity.Concrete.hashInputs_query_bind]
        have h : ∀ u, hashInputs ((fun last => (⟨last.value, ⟨state, .inl input, u⟩ :: last.events, last.state⟩ :
            FirstHit.Recorded α)) <$>
            Derivation.tableRun t (FirstHit.sourceRecord (next u) (FirstHit.advance state (.inl input) u))) =
            hashInputs (Derivation.tableRun t (next u)) := fun u => by rw [hashInputs_map, ih]
        simp only [h]
        cases input <;> rfl
      · rw [tableHandler_private, pure_bind, pure_bind, hashInputs_map, ih]
theorem eval_mem_support_tableRun {α : Type} (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (program : M α) (hp : SourceReplay.HashOnly program) :
    evalWithAnswerFn T program ∈ support (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [Derivation.tableRun]
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [tableRun_query_bind, evalWithAnswerFn_bind, eval_query]
      rcases input with (n | x) | c
      · exact False.elim hi
      · rw [tableHandler_world, mem_support_bind_iff]
        exact ⟨T (.inl (.inr x)), by simp, ih _ (hn _)⟩
      · rw [tableHandler_private, pure_bind, ht c]
        exact ht c ▸ ih _ (hn _)
theorem verdict_queries (t : FullGame.FullTable) {β : Type} (program : M β) (hp : PublicVerdict.Only program) :
    ∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (simulateQ verdictImpl program) →
      x ∈ hashInputs (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn with
  | pure value => intro x hx; exact absurd hx (by simp [allQueries_pure])
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | y) | c
      · exact False.elim hi
      · intro x hx
        rw [simulateQ_bind, simulateQ_spec_query] at hx
        change (.inl (.inr x) : RefWorld.Domain) ∈ allQueries
          (liftM (RefWorld.query (.inl (.inr y))) >>= fun answer => simulateQ verdictImpl (next answer)) at hx
        rw [tableRun_query_bind, tableHandler_world]
        rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
        · cases heq
          exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind _ _
        · exact SphincsSecurity.Concrete.hashInputs_next_subset (.inr y) _ u (ih u (hn u) x hu)
      · exact False.elim hi
end SigGolfCandidate.T3.Security.Wots.Ref
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
theorem traceOf_mem {T : Answers} {queries : List RefWorld.Domain} {entry : Entry}
    (h : entry ∈ traceOf T queries) : (.inl (.inr entry.1) : RefWorld.Domain) ∈ queries := by
  unfold traceOf at h
  obtain ⟨query, hq, he⟩ := List.mem_filterMap.mp h
  rcases query with (n | x) | u
  · cases he
  · simp only [Option.some.injEq] at he
    rw [← he]
    exact hq
  · cases he
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsReferenceInputs ====
section

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs SigGolfCandidate.T3.keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB SigGolfCandidate.T3.buildTree ClaudeWCT.WCT9.Rev3.signPayload
theorem offlineSign_support (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) (answer : Option Signature)
    (h : answer ∈ support (offlineSign T published request)) :
    answer = evalWithAnswerFn T (FullGame.authenticatedSign published request) := by
  unfold offlineSign at h
  rw [mem_support_bind_iff] at h
  obtain ⟨_, -, h⟩ := h
  rwa [mem_support_pure_iff] at h
theorem offlineSign_allQueries (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) (query : RefWorld.Domain)
    (h : query ∈ allQueries (offlineSign T published request)) : query = .inr () := by
  unfold offlineSign at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact ticks_allQueries _ query h
  · exact absurd h (by simp [allQueries_pure])
theorem interaction_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (published : SigGolfCandidate.T3.Cache) {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    (∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineInteraction T published program) →
      x ∈ hashInputs (Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) program))) ∧
    ∀ value ∈ support (offlineInteraction T published program),
      value ∈ support (Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [offlineInteraction_pure, FullGame.loggedWith_pure]
      refine ⟨fun x hx => absurd hx (by rw [allQueries_pure]; exact id), fun v hv => ?_⟩
      rw [mem_support_pure_iff] at hv
      subst hv
      simp [Derivation.tableRun]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [offlineInteraction_world, FullGame.loggedWith_world]
        have hreal : Derivation.tableRun t (forwardWorld input >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) =
            (liftM (OracleWorld.query input) >>= fun answer =>
              Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) (next answer))) := by
          change Derivation.tableRun t ((liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= _ : M _)) = _
          rw [tableRun_query_bind, tableHandler_world]
          rfl
        rw [hreal]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
          · cases heq
            exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind x _
          · exact SphincsSecurity.Concrete.hashInputs_next_subset input _ u ((ih u).1 x hu)
        · rw [mem_support_bind_iff] at hv ⊢
          obtain ⟨u, -, hu⟩ := hv
          exact ⟨u, by simp, (ih u).2 v hu⟩
      · rw [offlineInteraction_request, FullGame.loggedWith_request]
        have hans := eval_mem_support_tableRun T t ht _ (authenticatedSign_hashOnly published request)
        rw [tableRun_bind]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases allQueries_bind _ _ _ hx with h | ⟨answer, ha, h⟩
          · exact absurd (offlineSign_allQueries T published request _ h) (by simp)
          · rw [offlineSign_support T published request answer ha] at h
            have h' := (ih _).1 x (allQueries_map _ _ _ h)
            refine hashInputs_bind_of_mem _ _ _ hans ?_
            unfold Derivation.tableRun at h' ⊢
            rw [simulateQ_map, hashInputs_map]
            exact h'
        · rw [mem_support_bind_iff] at hv
          obtain ⟨answer, ha, hv⟩ := hv
          rw [offlineSign_support T published request answer ha] at hv
          rw [support_map] at hv
          obtain ⟨w, hw, rfl⟩ := hv
          rw [mem_support_bind_iff]
          refine ⟨_, hans, ?_⟩
          unfold Derivation.tableRun
          rw [simulateQ_map, support_map]
          exact ⟨w, (ih _).2 w hw, rfl⟩
theorem offlineGame_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (adversary : AdversaryP) (x : HashInput)
    (hx : (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineGame T adversary)) :
    x ∈ hashInputs (Derivation.tableRun t (GameWith.idealGame PaddedGame.checker adversary)) := by
  have hkey := eval_mem_support_tableRun T t ht keygen SourceReplay.keygen_hashOnly
  unfold offlineGame at hx
  unfold GameWith.idealGame
  rw [tableRun_bind]
  refine hashInputs_bind_of_mem _ _ _ hkey ?_
  rw [tableRun_bind]
  rcases allQueries_bind _ _ _ hx with h | ⟨_, -, h⟩
  · exact absurd (ticks_allQueries _ _ h) (by simp)
  rcases allQueries_bind _ _ _ h with h | ⟨result, hres, h⟩
  · exact hashInputs_bind_left _ _ ((interaction_queries T t ht _ _).1 x h)
  · exact hashInputs_bind_of_mem _ _ _ ((interaction_queries T t ht _ _).2 result hres)
      (verdict_queries t _ (PaddedGame.verdict_public _ _) x h)
theorem offlineRun_query_mem (adversary : AdversaryP) (q : Nat) (T : Answers) (privateTable : FullGame.FullTable)
    (ht : ∀ c, T (.inr c) = privateTable c) (run : Option (Bool × Nat) × List RefWorld.Domain)
    (hrun : run ∈ support (offlineRun T adversary q))
    (x : HashInput) (hx : (.inl (.inr x) : RefWorld.Domain) ∈ run.2) : x ∈ referenceInputs adversary := by
  have h1 := recorded_mem_allQueries _ _ run hrun _ hx
  have h2 := allQueries_run_subset RefCharged _ q h1
  have h3 := offlineGame_queries T privateTable ht adversary x h2
  rw [← hashInputs_tableRun_sourceRecord privateTable _ (∅, ∅)] at h3
  exact Finset.mem_union_right _ (ChainGraph.program_subset_recordedInputs _ privateTable h3)
end ClaudeWCT.W9.T3.Security.Wots.Ref
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB SigGolfCandidate.T3.buildTree ClaudeWCT.WCT9.Rev3.signPayload
theorem reference_trace_mem (adversary : AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) (entry : Entry) (he : entry ∈ sample.trace) :
    entry.1 ∈ referenceInputs adversary := by
  unfold referenceExperiment at hs
  rw [MonitoredPrivate.pmf_support] at hs
  unfold referenceComp at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨privateTable, -, hs⟩ := hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨publicTable, -, hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨run, hrun, hsample⟩ := hs
  have htrace : sample.trace = traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2 := by
    rw [← hsample]
  rw [htrace] at he
  exact Ref.offlineRun_query_mem adversary q _ privateTable (fun _ => rfl) run hrun entry.1 (traceOf_mem he)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs SigGolfCandidate.T3.keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB SigGolfCandidate.T3.buildTree ClaudeWCT.WCT9.Rev3.signPayload
theorem offlineSign_support (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) (answer : Option SigGolfCandidate.Research.SharedForest.Signature)
    (h : answer ∈ support (offlineSign T published request)) :
    answer = evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold offlineSign at h
  rw [mem_support_bind_iff] at h
  obtain ⟨_, -, h⟩ := h
  rwa [mem_support_pure_iff] at h
theorem offlineSign_allQueries (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) (query : RefWorld.Domain)
    (h : query ∈ allQueries (offlineSign T published request)) : query = .inr () := by
  unfold offlineSign at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact ticks_allQueries _ query h
  · exact absurd h (by simp [allQueries_pure])
theorem interaction_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (published : SigGolfCandidate.T3.Cache) {α : Type} (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    (∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineInteraction T published program) →
      x ∈ hashInputs (Derivation.tableRun t (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program))) ∧
    ∀ value ∈ support (offlineInteraction T published program),
      value ∈ support (Derivation.tableRun t (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [offlineInteraction_pure, PairedOuter.FullGame.loggedWith_pure]
      refine ⟨fun x hx => absurd hx (by rw [allQueries_pure]; exact id), fun v hv => ?_⟩
      rw [mem_support_pure_iff] at hv
      subst hv
      simp [Derivation.tableRun]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [offlineInteraction_world, PairedOuter.FullGame.loggedWith_world]
        have hreal : Derivation.tableRun t (forwardWorld input >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer)) =
            (liftM (OracleWorld.query input) >>= fun answer =>
              Derivation.tableRun t (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer))) := by
          change Derivation.tableRun t ((liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= _ : M _)) = _
          rw [tableRun_query_bind, tableHandler_world]
          rfl
        rw [hreal]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
          · cases heq
            exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind x _
          · exact SphincsSecurity.Concrete.hashInputs_next_subset input _ u ((ih u).1 x hu)
        · rw [mem_support_bind_iff] at hv ⊢
          obtain ⟨u, -, hu⟩ := hv
          exact ⟨u, by simp, (ih u).2 v hu⟩
      · rw [offlineInteraction_request, PairedOuter.FullGame.loggedWith_request]
        have hans := eval_mem_support_tableRun T t ht _ (authenticatedSign_hashOnly published request)
        rw [tableRun_bind]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases allQueries_bind _ _ _ hx with h | ⟨answer, ha, h⟩
          · exact absurd (offlineSign_allQueries T published request _ h) (by simp)
          · rw [offlineSign_support T published request answer ha] at h
            have h' := (ih _).1 x (allQueries_map _ _ _ h)
            refine hashInputs_bind_of_mem _ _ _ hans ?_
            unfold Derivation.tableRun at h' ⊢
            rw [simulateQ_map, hashInputs_map]
            exact h'
        · rw [mem_support_bind_iff] at hv
          obtain ⟨answer, ha, hv⟩ := hv
          rw [offlineSign_support T published request answer ha] at hv
          rw [support_map] at hv
          obtain ⟨w, hw, rfl⟩ := hv
          rw [mem_support_bind_iff]
          refine ⟨_, hans, ?_⟩
          unfold Derivation.tableRun
          rw [simulateQ_map, support_map]
          exact ⟨w, (ih _).2 w hw, rfl⟩
theorem offlineGame_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (x : HashInput)
    (hx : (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineGame T adversary)) :
    x ∈ hashInputs (Derivation.tableRun t (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary)) := by
  have hkey := eval_mem_support_tableRun T t ht keygen SourceReplay.keygen_hashOnly
  unfold offlineGame at hx
  unfold PairedOuter.GameWith.idealGame
  rw [tableRun_bind]
  refine hashInputs_bind_of_mem _ _ _ hkey ?_
  rw [tableRun_bind]
  rcases allQueries_bind _ _ _ hx with h | ⟨_, -, h⟩
  · exact absurd (ticks_allQueries _ _ h) (by simp)
  rcases allQueries_bind _ _ _ h with h | ⟨result, hres, h⟩
  · exact hashInputs_bind_left _ _ ((interaction_queries T t ht _ _).1 x h)
  · exact hashInputs_bind_of_mem _ _ _ ((interaction_queries T t ht _ _).2 result hres)
      (verdict_queries t _ (PairedOuter.PaddedGame.verdict_public _ _) x h)
theorem offlineRun_query_mem (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers) (privateTable : FullGame.FullTable)
    (ht : ∀ c, T (.inr c) = privateTable c) (run : Option (Bool × Nat) × List RefWorld.Domain)
    (hrun : run ∈ support (offlineRun T adversary q))
    (x : HashInput) (hx : (.inl (.inr x) : RefWorld.Domain) ∈ run.2) : x ∈ referenceInputs adversary := by
  have h1 := recorded_mem_allQueries _ _ run hrun _ hx
  have h2 := allQueries_run_subset RefCharged _ q h1
  have h3 := offlineGame_queries T privateTable ht adversary x h2
  rw [← hashInputs_tableRun_sourceRecord privateTable _ (∅, ∅)] at h3
  exact Finset.mem_union_right _ (ChainGraph.program_subset_recordedInputs _ privateTable h3)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB SigGolfCandidate.T3.buildTree ClaudeWCT.WCT9.Rev3.signPayload
theorem reference_trace_mem (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) (entry : Entry) (he : entry ∈ sample.trace) :
    entry.1 ∈ referenceInputs adversary := by
  unfold referenceExperiment at hs
  rw [MonitoredPrivate.pmf_support] at hs
  unfold referenceComp at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨privateTable, -, hs⟩ := hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨publicTable, -, hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨run, hrun, hsample⟩ := hs
  have htrace : sample.trace = traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2 := by
    rw [← hsample]
  rw [htrace] at he
  exact Ref.offlineRun_query_mem adversary q _ privateTable (fun _ => rfl) run hrun entry.1 (traceOf_mem he)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
end
-- ==== merged from T3_Secc_WotsStructuralVariant ====
section

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
theorem eval_query_bind {α : Type} (T : Answers) (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) :
    evalWithAnswerFn T (liftM (T3.Spec.query input) >>= next) = evalWithAnswerFn T (next (T input)) := by
  rw [evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn T (liftM (T3.Spec.query input)) = T input from simulateQ_spec_query T input]
theorem congr_of_queried {α : Type} (T T' : Answers) (program : M α)
    (h : ∀ q ∈ SourceReplay.queried T program, T q = T' q) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program := by
  induction program using OracleComp.inductionOn with
  | pure x => exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [SourceReplay.queried_query_bind] at h
      have h0 : T input = T' input := h input List.mem_cons_self
      have ih' := ih (T input) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      refine ⟨?_, ?_⟩
      · rw [eval_query_bind, eval_query_bind, ← h0]
        exact ih'.1
      · rw [SourceReplay.queried_query_bind, SourceReplay.queried_query_bind, ← h0, ih'.2]
end SigGolfCandidate.T3.Security.Wots.Structural
end
-- ==== merged from SphincsSecurity_Proof_Chains_PartialChainEndpoint ====
section

section
namespace SphincsSecurity.Concrete.EndpointPreimageDensity
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Table State : Type} [Fintype State] [Nonempty State] [DecidableEq State] [DecidableEq Table]
noncomputable def preimages (evaluate : Table → State → State) (table : Table) (endpoint : State) : Nat :=
  (Finset.univ.filter (fun secret => evaluate table secret = endpoint)).card
noncomputable def real (prior : PMF Table) (evaluate : Table → State → State) : PMF (Table × State) :=
  prior.bind (fun table => ((PMF.uniformOfFintype State).map (evaluate table)).map (fun endpoint => (table, endpoint)))
noncomputable def ideal (prior : PMF Table) : PMF (Table × State) :=
  prior.bind (fun table => (PMF.uniformOfFintype State).map (fun endpoint => (table, endpoint)))
theorem uniform_image_apply (evaluate : State → State) (endpoint : State) :
    (PMF.uniformOfFintype State).map evaluate endpoint =
      ((Finset.univ.filter (fun secret => evaluate secret = endpoint)).card : ENNReal) / Fintype.card State := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, eq_comm, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
omit [Fintype State] [Nonempty State] [DecidableEq State] in
theorem map_pair_apply (law : PMF State) (table target : Table) (endpoint : State) :
    law.map (fun value => (table, value)) (target, endpoint) = if table = target then law endpoint else 0 := by
  rw [PMF.map_apply]
  by_cases htable : table = target
  · subst target
    rw [if_pos rfl, tsum_eq_single endpoint]
    · rw [if_pos rfl]
    · intro value hvalue
      exact if_neg (fun h => hvalue (congrArg Prod.snd h).symm)
  · rw [if_neg htable]
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    exact if_neg (fun h => htable (congrArg Prod.fst h).symm)
omit [Fintype State] [Nonempty State] [DecidableEq State] in
theorem bind_pair_apply (prior : PMF Table) (law : Table → PMF State) (table : Table) (endpoint : State) :
    prior.bind (fun selected => (law selected).map (fun value => (selected, value))) (table, endpoint) =
      prior table * law table endpoint := by
  rw [PMF.bind_apply]
  simp only [map_pair_apply, mul_ite, mul_zero]
  rw [tsum_eq_single table]
  · simp only [if_true]
  · intro selected hselected
    exact if_neg hselected
theorem real_apply (prior : PMF Table) (evaluate : Table → State → State) (table : Table) (endpoint : State) :
    real prior evaluate (table, endpoint) = prior table * ((preimages evaluate table endpoint : ENNReal) / Fintype.card State) := by
  rw [real, bind_pair_apply, uniform_image_apply]
  rfl
omit [DecidableEq State] in
theorem ideal_apply (prior : PMF Table) (table : Table) (endpoint : State) :
    ideal prior (table, endpoint) = prior table / Fintype.card State := by
  rw [ideal, bind_pair_apply, PMF.uniformOfFintype_apply, div_eq_mul_inv]
theorem real_density (prior : PMF Table) (evaluate : Table → State → State) (table : Table) (endpoint : State) :
    real prior evaluate (table, endpoint) = (preimages evaluate table endpoint : ENNReal) * ideal prior (table, endpoint) := by
  rw [real_apply, ideal_apply]
  simp only [div_eq_mul_inv]
  ring
theorem real_payoff (prior : PMF Table) (evaluate : Table → State → State) (payoff : Table × State → ENNReal) :
    (∑' result, real prior evaluate result * payoff result) =
      ∑' result : Table × State, ideal prior result * (preimages evaluate result.1 result.2 : ENNReal) * payoff result := by
  apply tsum_congr
  rintro ⟨table, endpoint⟩
  rw [real_density]
  ring
omit [DecidableEq Table] in
theorem mean_preimages (prior : PMF Table) (evaluate : Table → State → State) (endpoint : State) :
    (∑' table, prior table * (preimages evaluate table endpoint : ENNReal)) =
      (Fintype.card State : ENNReal) *
        prior.bind (fun table => (PMF.uniformOfFintype State).map (evaluate table)) endpoint := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro table
  rw [uniform_image_apply]
  change prior table * (preimages evaluate table endpoint : ENNReal) =
    (Fintype.card State : ENNReal) * (prior table * ((preimages evaluate table endpoint : ENNReal) / Fintype.card State))
  rw [div_eq_mul_inv]
  calc
    _ = ((Fintype.card State : ENNReal) * (Fintype.card State : ENNReal)⁻¹) *
        (prior table * (preimages evaluate table endpoint : ENNReal)) := by
      rw [ENNReal.mul_inv_cancel hcard (by finiteness), one_mul]
    _ = _ := by ring
end SphincsSecurity.Concrete.EndpointPreimageDensity
end
section
namespace SphincsSecurity.Concrete.FinitePmfProduct
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Index Value : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]
theorem marginal (family : Index → PMF Value) (index : Index) :
    (law family).map (fun values => values index) = family index := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro value
  have hfactor (values : Index → Value) :
      (if value = values index then law family values else 0) =
        ∏ other, if other = index then
          (if value = values other then family other (values other) else 0) else family other (values other) := by
    by_cases hvalue : value = values index
    · rw [if_pos hvalue, apply]
      apply Finset.prod_congr rfl
      intro other _
      by_cases hother : other = index
      · subst other
        simp only [if_true, hvalue]
      · simp only [hother, if_false]
    · rw [if_neg hvalue]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp only [if_true, hvalue, if_false])
  rw [PMF.map_apply, tsum_fintype]
  trans ∑ values : Index → Value, ∏ other, if other = index then
    (if value = values other then family other (values other) else 0) else family other (values other)
  · exact Finset.sum_congr rfl (fun values _ => hfactor values)
  rw [← Fintype.prod_sum (fun other (candidate : Value) =>
    if other = index then (if value = candidate then family other candidate else 0) else family other candidate),
    Finset.prod_eq_single index]
  · simp only [if_true]
    simp
  · intro other _ hother
    simp only [hother, if_false]
    simpa only [tsum_fintype] using PMF.tsum_coe (family other)
  · simp
theorem fin_succ {n : Nat} (family : Fin (n + 1) → PMF Value) :
    law family = (family 0).bind (fun first => (law (fun index : Fin n => family index.succ)).map (Fin.cons first)) := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro values
  have hmap (first : Value) :
      (law (fun index : Fin n => family index.succ)).map (Fin.cons first) values =
        if first = values 0 then law (fun index : Fin n => family index.succ) (Fin.tail values) else 0 := by
    rw [PMF.map_apply]
    by_cases hfirst : first = values 0
    · rw [if_pos hfirst, tsum_eq_single (Fin.tail values)]
      · rw [hfirst, Fin.cons_self_tail, if_pos rfl]
      · intro tail htail
        exact if_neg (fun h => htail (by simpa using (congrArg Fin.tail h).symm))
    · rw [if_neg hfirst]
      apply ENNReal.tsum_eq_zero.mpr
      intro tail
      exact if_neg (fun h => hfirst (by simpa using (congrFun h 0).symm))
  rw [PMF.bind_apply]
  simp only [hmap, mul_ite, mul_zero]
  rw [tsum_eq_single (values 0)]
  · simp only [if_true, apply, Fin.prod_univ_succ, Fin.tail]
  · intro value hvalue
    exact if_neg hvalue
theorem update_apply (family : Index → PMF Value) (index : Index) (replacement : PMF Value)
    (values : Index → Value) :
    law (Function.update family index replacement) values =
      replacement (values index) * ∏ other ∈ Finset.univ.erase index, family other (values other) := by
  rw [apply, ← Finset.mul_prod_erase Finset.univ
    (fun other => Function.update family index replacement other (values other)) (Finset.mem_univ index)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]
theorem observe_mass [DecidableEq Value] (family : Index → PMF Value) (index : Index) (value : Value) (values : Index → Value) :
    family index value * law (Function.update family index (PMF.pure value)) values =
      if values index = value then law family values else 0 := by
  classical
  rw [update_apply, apply, ← Finset.mul_prod_erase Finset.univ
    (fun other => family other (values other)) (Finset.mem_univ index)]
  by_cases hvalue : values index = value
  · simp only [hvalue, PMF.pure_apply_self, one_mul, if_true]
  · simp only [PMF.pure_apply, if_false, zero_mul, mul_zero, hvalue]
end SphincsSecurity.Concrete.FinitePmfProduct
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def rowLaw : Option State → PMF State
  | none => PMF.uniformOfFintype State
  | some value => PMF.pure value
noncomputable def completeFunction (observed : State → Option State) : PMF (State → State) :=
  FinitePmfProduct.law (fun input => rowLaw (observed input))
theorem completeFunction_marginal (observed : State → Option State) (input : State) :
    (completeFunction observed).map (fun table => table input) = rowLaw (observed input) :=
  FinitePmfProduct.marginal _ input
def evaluate : {n : Nat} → (Fin n → State → State) → State → State
  | 0, _, start => start
  | _ + 1, tables, start => evaluate (Fin.tail tables) (tables 0 start)
noncomputable def completeTables {n : Nat} (observed : Fin n → State → Option State) :
    PMF (Fin n → State → State) := FinitePmfProduct.law (fun step => completeFunction (observed step))
noncomputable def kernel : {n : Nat} → (Fin n → State → Option State) → State → PMF State
  | 0, _, start => PMF.pure start
  | _ + 1, observed, start => (rowLaw (observed 0 start)).bind (kernel (Fin.tail observed))
theorem completeTables_evaluate {n : Nat} (observed : Fin n → State → Option State) (start : State) :
    (completeTables observed).map (fun tables => evaluate tables start) = kernel observed start := by
  induction n generalizing start with
  | zero => exact PMF.map_const _ _
  | succ n ih =>
      rw [completeTables, FinitePmfProduct.fin_succ, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def, evaluate, Fin.tail_cons, Fin.cons_zero]
      change (completeFunction (observed 0)).bind (fun first =>
        (completeTables (Fin.tail observed)).map (fun tables => evaluate tables (first start))) = _
      simp_rw [ih]
      calc
        _ = ((completeFunction (observed 0)).map (fun first => first start)).bind (kernel (Fin.tail observed)) :=
          (PMF.bind_map _ _ _).symm
        _ = _ := by rw [completeFunction_marginal, kernel]
theorem uniform_endpoint {n : Nat} (observed : Fin n → State → Option State) :
    (completeTables observed).bind (fun tables => (PMF.uniformOfFintype State).map (evaluate tables)) =
      (PMF.uniformOfFintype State).bind (kernel observed) := by
  change (completeTables observed).bind (fun tables =>
    (PMF.uniformOfFintype State).bind (fun start => PMF.pure (evaluate tables start))) = _
  rw [PMF.bind_comm]
  change (PMF.uniformOfFintype State).bind
    (fun start => (completeTables observed).map (fun tables => evaluate tables start)) = _
  simp only [completeTables_evaluate]
noncomputable def meanPreimages {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  ∑' tables, completeTables observed tables * (EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal)
theorem meanPreimages_eq {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint =
      (Fintype.card State : ENNReal) * ((PMF.uniformOfFintype State).bind (kernel observed)) endpoint := by
  rw [meanPreimages, EndpointPreimageDensity.mean_preimages, uniform_endpoint]
noncomputable def unqueried (observed : State → Option State) : Finset State :=
  Finset.univ.filter (fun input => observed input = none)
noncomputable def freeFraction (observed : State → Option State) : ENNReal :=
  (unqueried observed).card / (Fintype.card State : ENNReal)
omit [DecidableEq State] in
theorem advance_lower (observed : State → Option State) (prior : PMF State) (bound : ENNReal)
    (hlower : ∀ input, bound ≤ prior input) (endpoint : State) :
    bound * freeFraction observed ≤ prior.bind (fun input => rowLaw (observed input)) endpoint := by
  rw [PMF.bind_apply, tsum_fintype]
  calc
    _ = ∑ input ∈ unqueried observed, bound * (Fintype.card State : ENNReal)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul, freeFraction, div_eq_mul_inv]
      ring
    _ ≤ ∑ input ∈ unqueried observed, prior input * rowLaw (observed input) endpoint := by
      apply Finset.sum_le_sum
      intro input hinput
      have hnone : observed input = none := (Finset.mem_filter.mp hinput).2
      rw [hnone, rowLaw, PMF.uniformOfFintype_apply]
      exact mul_le_mul_left (hlower input) _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bot_le)
omit [DecidableEq State] in
theorem kernel_lower {n : Nat} (observed : Fin n → State → Option State) (prior : PMF State) (bound : ENNReal)
    (hlower : ∀ input, bound ≤ prior input) (endpoint : State) :
    bound * (∏ step, freeFraction (observed step)) ≤ prior.bind (kernel observed) endpoint := by
  induction n generalizing prior bound with
  | zero => simpa only [Fin.prod_univ_zero, mul_one, kernel, PMF.bind_pure] using hlower endpoint
  | succ n ih =>
      rw [Fin.prod_univ_succ, ← mul_assoc]
      have h := ih (Fin.tail observed) (prior.bind (fun input => rowLaw (observed 0 input)))
        (bound * freeFraction (observed 0)) (advance_lower (observed 0) prior bound hlower)
      simpa only [PMF.bind_bind, kernel, Fin.tail] using h
theorem meanPreimages_ge_product {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    (∏ step, freeFraction (observed step)) ≤ meanPreimages observed endpoint := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [meanPreimages_eq]
  have h := mul_le_mul_right (kernel_lower observed (PMF.uniformOfFintype State) (Fintype.card State : ENNReal)⁻¹
    (fun input => by rw [PMF.uniformOfFintype_apply]) endpoint) (Fintype.card State : ENNReal)
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hcard (by finiteness), one_mul] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainObservation ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
theorem completeFunction_empty :
    completeFunction (fun (_ : State) => none) = PMF.uniformOfFintype (State → State) :=
  FinitePmfProduct.uniform
theorem completeTables_empty {n : Nat} :
    completeTables (fun (_ : Fin n) (_ : State) => none) = PMF.uniformOfFintype (Fin n → State → State) := by
  simp only [completeTables, completeFunction_empty, FinitePmfProduct.uniform]
def record {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State) :
    Fin n → State → Option State :=
  Function.update observed query.1 (Function.update (observed query.1) query.2 (some answer))
theorem completeFunction_record (observed : State → Option State) (input answer : State) :
    completeFunction (Function.update observed input (some answer)) =
      FinitePmfProduct.law (Function.update (fun row => rowLaw (observed row)) input (PMF.pure answer)) := by
  unfold completeFunction
  congr 1
  funext row
  by_cases hrow : row = input
  · simp only [hrow, Function.update_self, rowLaw]
  · simp only [Function.update_of_ne hrow]
theorem completeFunction_observe_mass (observed : State → Option State) (input answer : State) (table : State → State) :
    rowLaw (observed input) answer * completeFunction (Function.update observed input (some answer)) table =
      if table input = answer then completeFunction observed table else 0 := by
  rw [completeFunction_record]
  exact FinitePmfProduct.observe_mass (fun row => rowLaw (observed row)) input answer table
theorem completeTables_record {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer : State) :
    completeTables (record observed query answer) =
      FinitePmfProduct.law (Function.update (fun step => completeFunction (observed step)) query.1
        (completeFunction (Function.update (observed query.1) query.2 (some answer)))) := by
  unfold completeTables record
  congr 1
  funext step
  by_cases hstep : step = query.1
  · simp only [hstep, Function.update_self]
  · simp only [Function.update_of_ne hstep]
theorem completeTables_observe_mass {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer : State) (tables : Fin n → State → State) :
    rowLaw (observed query.1 query.2) answer * completeTables (record observed query answer) tables =
      if tables query.1 query.2 = answer then completeTables observed tables else 0 := by
  rw [completeTables_record, FinitePmfProduct.update_apply, ← mul_assoc,
    completeFunction_observe_mass, ite_mul, zero_mul]
  by_cases hanswer : tables query.1 query.2 = answer
  · rw [if_pos hanswer, if_pos hanswer, completeTables, FinitePmfProduct.apply]
    exact Finset.mul_prod_erase Finset.univ (fun step => completeFunction (observed step) (tables step))
      (Finset.mem_univ query.1)
  · rw [if_neg hanswer, if_neg hanswer]
theorem completeTables_bind_observe {n : Nat} {Result : Type} (observed : Fin n → State → Option State)
    (query : Fin n × State) (next : State → (Fin n → State → State) → PMF Result) :
    (completeTables observed).bind (fun tables => next (tables query.1 query.2) tables) =
      (rowLaw (observed query.1 query.2)).bind (fun answer =>
        (completeTables (record observed query answer)).bind (next answer)) := by
  classical
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, completeTables_observe_mass,
    ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}
abbrev PrefixSpec (n : Nat) (State : Type) := (Fin n × State) →ₒ State
noncomputable def observedImpl (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State) :
    QueryImpl (auxSpec + PrefixSpec n State) (StateT (Fin n → State → Option State) PMF)
  | .inl input => StateT.mk fun observed => (auxiliary input).map (fun answer => (answer, observed))
  | .inr query => StateT.mk fun observed =>
      PMF.pure (tables query.1 query.2, record observed query (tables query.1 query.2))
noncomputable def lazyImpl (auxiliary : QueryImpl auxSpec PMF) :
    QueryImpl (auxSpec + PrefixSpec n State) (StateT (Fin n → State → Option State) PMF)
  | .inl input => StateT.mk fun observed => (auxiliary input).map (fun answer => (answer, observed))
  | .inr query => StateT.mk fun observed =>
      (rowLaw (observed query.1 query.2)).map (fun answer => (answer, record observed query answer))
noncomputable def observedRun {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    PMF (Result × (Fin n → State → Option State)) :=
  (simulateQ (observedImpl auxiliary tables) computation).run observed
noncomputable def lazyRun {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    PMF (Result × (Fin n → State → Option State)) :=
  (simulateQ (lazyImpl auxiliary) computation).run observed
omit [Fintype State] [Nonempty State] in
theorem observedRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (result : Result) (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (pure result) observed = PMF.pure (result, observed) := by
  simp only [observedRun, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure]
theorem lazyRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (result : Result) (observed : Fin n → State → Option State) :
    lazyRun auxiliary (pure result) observed = PMF.pure (result, observed) := by
  simp only [lazyRun, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure]
omit [Fintype State] [Nonempty State] in
theorem observedRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (input : (auxSpec + PrefixSpec n State).Domain)
    (next : (auxSpec + PrefixSpec n State).Range input → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (liftM ((auxSpec + PrefixSpec n State).query input) >>= next) observed =
      ((observedImpl auxiliary tables input).run observed).bind
        (fun result => observedRun auxiliary tables (next result.1) result.2) := by
  simp only [observedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind]
theorem lazyRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (input : (auxSpec + PrefixSpec n State).Domain)
    (next : (auxSpec + PrefixSpec n State).Range input → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    lazyRun auxiliary (liftM ((auxSpec + PrefixSpec n State).query input) >>= next) observed =
      ((lazyImpl auxiliary input).run observed).bind (fun result => lazyRun auxiliary (next result.1) result.2) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind]
theorem run_posterior {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (completeTables observed).bind (fun tables =>
      (observedRun auxiliary tables computation observed).map (fun result => (tables, result))) =
        (lazyRun auxiliary computation observed).bind (fun result =>
          (completeTables result.2).map (fun tables => (tables, result))) := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure result =>
      simp only [observedRun_pure, lazyRun_pure, PMF.pure_bind, PMF.map, PMF.pure_bind]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, PMF.bind_map, PMF.map_bind, PMF.bind_bind]
          rw [PMF.bind_comm]
          exact congrArg (fun continuation => (auxiliary input).bind continuation)
            (funext fun answer => ih answer observed)
      | inr query =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, PMF.pure_bind, PMF.bind_map, PMF.bind_bind]
          rw [completeTables_bind_observe observed query (fun answer tables =>
            (observedRun auxiliary tables (next answer) (record observed query answer)).map
              (fun result => (tables, result)))]
          exact congrArg (fun continuation => (rowLaw (observed query.1 query.2)).bind continuation)
            (funext fun answer => ih answer (record observed query answer))
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_PartialChainLikelihoodLower ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem one_sub_sum_le_prod {Index : Type} [DecidableEq Index] (indices : Finset Index)
    (loss : Index → ℝ) (hlower : ∀ index ∈ indices, 0 ≤ loss index) (hupper : ∀ index ∈ indices, loss index ≤ 1) :
    1 - ∑ index ∈ indices, loss index ≤ ∏ index ∈ indices, (1 - loss index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
      have hzero := hlower index (Finset.mem_insert_self _ _)
      have hone := hupper index (Finset.mem_insert_self _ _)
      have hsum : 0 ≤ ∑ other ∈ indices, loss other :=
        Finset.sum_nonneg (fun other hother => hlower other (Finset.mem_insert_of_mem hother))
      have htail := ih (fun other hother => hlower other (Finset.mem_insert_of_mem hother))
        (fun other hother => hupper other (Finset.mem_insert_of_mem hother))
      rw [Finset.sum_insert hnot, Finset.prod_insert hnot]
      calc
        _ ≤ (1 - loss index) * (1 - ∑ other ∈ indices, loss other) := by
          nlinarith [mul_nonneg hzero hsum]
        _ ≤ _ := mul_le_mul_of_nonneg_left htail (by linarith)
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def queriedCount (observed : State → Option State) : Nat :=
  Fintype.card State - (unqueried observed).card
noncomputable def queryCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  ∑ step, queriedCount (observed step)
omit [DecidableEq State] [Nonempty State] in
theorem queriedCount_le (observed : State → Option State) : queriedCount observed ≤ Fintype.card State :=
  Nat.sub_le _ _
omit [DecidableEq State] in
theorem freeFraction_ne_top (observed : State → Option State) : freeFraction observed ≠ ⊤ := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold freeFraction
  finiteness
omit [DecidableEq State] in
theorem freeFraction_toReal (observed : State → Option State) :
    (freeFraction observed).toReal = 1 - (queriedCount observed : ℝ) / Fintype.card State := by
  have hcard : (Fintype.card State : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcount : (unqueried observed).card ≤ Fintype.card State := Finset.card_le_univ _
  rw [freeFraction, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    queriedCount, Nat.cast_sub hcount, sub_div, div_self hcard]
  ring
omit [DecidableEq State] in
theorem product_ge_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    1 - (queryCount observed : ENNReal) / Fintype.card State ≤ ∏ step, freeFraction (observed step) := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardR : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  by_cases hbudget : (queryCount observed : ENNReal) / Fintype.card State ≤ 1
  · apply (ENNReal.toReal_le_toReal (by finiteness)
      (ENNReal.prod_ne_top (fun step _ => freeFraction_ne_top (observed step)))).mp
    rw [ENNReal.toReal_sub_of_le hbudget (by finiteness), ENNReal.toReal_one, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    simp only [ENNReal.toReal_prod, freeFraction_toReal, queryCount, Nat.cast_sum, Finset.sum_div]
    exact one_sub_sum_le_prod Finset.univ (fun step => (queriedCount (observed step) : ℝ) / Fintype.card State)
      (fun _ _ => by positivity)
      (fun step _ => (div_le_one hcardR).mpr (by exact_mod_cast queriedCount_le (observed step)))
  · rw [tsub_eq_zero_of_le (le_of_not_ge hbudget)]
    exact bot_le
theorem meanPreimages_ge_queryCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    1 - (queryCount observed : ENNReal) / Fintype.card State ≤ meanPreimages observed endpoint :=
  (product_ge_queryCount observed).trans (meanPreimages_ge_product observed endpoint)
theorem meanPreimages_ge_budget {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (budget : Nat) (hbudget : queryCount observed ≤ budget) :
    1 - (budget : ENNReal) / Fintype.card State ≤ meanPreimages observed endpoint := by
  apply le_trans _ (meanPreimages_ge_queryCount observed endpoint)
  have hcount : (queryCount observed : ENNReal) ≤ (budget : ENNReal) := by exact_mod_cast hbudget
  exact tsub_le_tsub_left (ENNReal.div_le_div_right hcount _) _
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainLikelihood ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
theorem expectation_bind {First Second : Type} (prior : PMF First) (next : First → PMF Second)
    (payoff : Second → ENNReal) :
    (∑' result, prior.bind next result * payoff result) =
      ∑' first, prior first * ∑' result, next first result * payoff result := by
  simpa only [PMF.probOutput_eq_apply, PMF.monad_bind_eq_bind] using
    tsum_probOutput_bind_mul prior next payoff
theorem expectation_map {First Second : Type} (prior : PMF First) (next : First → Second)
    (payoff : Second → ENNReal) :
    (∑' result, prior.map next result * payoff result) = ∑' first, prior first * payoff (next first) := by
  simpa only [PMF.probOutput_eq_apply, PMF.monad_map_eq_map] using
    tsum_probOutput_map_mul prior next payoff
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}
theorem run_weighted_payoff {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (payoff : Result × (Fin n → State → Option State) → ENNReal) :
    (∑' tables, completeTables observed tables * ∑' result, observedRun auxiliary tables computation observed result *
      ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff result)) =
        ∑' result, lazyRun auxiliary computation observed result * (meanPreimages result.2 endpoint * payoff result) := by
  have h := congrArg (fun law : PMF ((Fin n → State → State) × (Result × (Fin n → State → Option State))) =>
    ∑' result, law result * ((EndpointPreimageDensity.preimages evaluate result.1 endpoint : ENNReal) * payoff result.2))
    (run_posterior auxiliary computation observed)
  simp only [expectation_bind, expectation_map] at h
  rw [h]
  apply tsum_congr
  intro result
  congr 1
  simp only [meanPreimages, ← mul_assoc, ENNReal.tsum_mul_right]
theorem run_allocated_cost_lower {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (payoff : Result × (Fin n → State → Option State) → ENNReal) (budget : Nat)
    (hbudget : ∀ result ∈ (lazyRun auxiliary computation observed).support, queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, lazyRun auxiliary computation observed result * payoff result) ≤
      ∑' tables, completeTables observed tables * ∑' result, observedRun auxiliary tables computation observed result *
        ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff result) := by
  rw [run_weighted_payoff, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hzero : lazyRun auxiliary computation observed result = 0
  · simp only [hzero, zero_mul, mul_zero, le_refl]
  · have hlower := meanPreimages_ge_budget result.2 endpoint budget
      (hbudget result hzero)
    calc
      _ = lazyRun auxiliary computation observed result *
          ((1 - (budget : ENNReal) / Fintype.card State) * payoff result) := by ring
      _ ≤ _ := mul_le_mul_right (mul_le_mul_left hlower (payoff result)) _
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainQueryBound ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}
omit [Nonempty State] in
theorem unqueried_update_some (observed : State → Option State) (input answer : State) :
    unqueried (Function.update observed input (some answer)) = (unqueried observed).erase input := by
  ext row
  by_cases hrow : row = input <;> simp [unqueried, Function.update_apply, hrow]
omit [Nonempty State] in
theorem queriedCount_update_le (observed : State → Option State) (input answer : State) :
    queriedCount (Function.update observed input (some answer)) ≤ queriedCount observed + 1 := by
  rw [queriedCount, unqueried_update_some, queriedCount]
  have h := Finset.pred_card_le_card_erase (s := unqueried observed) (a := input)
  omega
omit [Nonempty State] in
theorem queryCount_record_le (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State) :
    queryCount (record observed query answer) ≤ queryCount observed + 1 := by
  have hfun : (fun step => queriedCount (record observed query answer step)) =
      Function.update (fun step => queriedCount (observed step)) query.1
        (queriedCount (Function.update (observed query.1) query.2 (some answer))) := by
    funext step
    by_cases hstep : step = query.1 <;> simp only [record, Function.update_apply, hstep, if_true, if_false]
  rw [queryCount, hfun, Finset.sum_update_of_mem (Finset.mem_univ query.1), Finset.sdiff_singleton_eq_erase,
    queryCount, ← Finset.add_sum_erase Finset.univ (fun step => queriedCount (observed step)) (Finset.mem_univ query.1)]
  have h := queriedCount_update_le (observed query.1) query.2 answer
  omega
omit [DecidableEq State] [Nonempty State] in
theorem queryCount_empty : queryCount (fun (_ : Fin n) (_ : State) => none) = 0 := by
  simp [queryCount, queriedCount, unqueried]
def IsPrefixQuery : AuxIndex ⊕ (Fin n × State) → Prop
  | .inl _ => False
  | .inr _ => True
instance instDecidableIsPrefixQuery (input : AuxIndex ⊕ (Fin n × State)) : Decidable (IsPrefixQuery input) := by
  cases input <;> unfold IsPrefixQuery <;> infer_instance
theorem lazyRun_queryCount_le {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget)
    (result : Result × (Fin n → State → Option State)) (hresult : result ∈ (lazyRun auxiliary computation observed).support) :
    queryCount result.2 ≤ queryCount observed + budget := by
  induction computation using OracleComp.inductionOn generalizing observed budget result with
  | pure value =>
      rw [lazyRun_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [lazyRun_query_bind] at hresult
      cases input with
      | inl input =>
          simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          exact ih answer observed budget (hbound.2 answer) result hresult
      | inr query =>
          simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          have hpos : 0 < budget := by simpa only [IsPrefixQuery, not_true_eq_false, false_or] using hbound.1
          have hnext := ih answer (record observed query answer) (budget - 1) (hbound.2 answer) result hresult
          have hrecord := queryCount_record_le observed query answer
          omega
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainEndpoint ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
noncomputable def realRun (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) : PMF (State × (Result × (Fin n → State → Option State))) :=
  (EndpointPreimageDensity.real (completeTables observed) evaluate).bind (fun pair =>
    (observedRun (auxiliary pair.2) pair.1 (computation pair.2) observed).map (fun result => (pair.2, result)))
noncomputable def idealRun (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) : PMF (State × (Result × (Fin n → State → Option State))) :=
  (PMF.uniformOfFintype State).bind (fun endpoint =>
    (lazyRun (auxiliary endpoint) (computation endpoint) observed).map (fun result => (endpoint, result)))
theorem realRun_expectation (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (payoff : State × (Result × (Fin n → State → Option State)) → ENNReal) :
    (∑' result, realRun auxiliary computation observed result * payoff result) =
      ∑' result, idealRun auxiliary computation observed result *
        (meanPreimages result.2.2 result.1 * payoff result) := by
  classical
  letI : DecidableEq (Fin n → State → State) := Classical.decEq _
  simp only [realRun, expectation_bind, expectation_map]
  rw [EndpointPreimageDensity.real_payoff, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [EndpointPreimageDensity.ideal_apply, div_eq_mul_inv]
  simp only [idealRun, expectation_bind, expectation_map, PMF.uniformOfFintype_apply]
  apply tsum_congr
  intro endpoint
  rw [← run_weighted_payoff (auxiliary endpoint) (computation endpoint) observed endpoint
    (fun result => payoff (endpoint, result)), ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro tables
  have hfactor :
      (∑' result, observedRun (auxiliary endpoint) tables (computation endpoint) observed result *
        ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff (endpoint, result))) =
      (EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) *
        ∑' result, observedRun (auxiliary endpoint) tables (computation endpoint) observed result * payoff (endpoint, result) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro result
    ring
  rw [hfactor]
  ring
theorem idealRun_queryCount_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (result : State × (Result × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary computation observed).support) :
    queryCount result.2.2 ≤ queryCount observed + budget := by
  rw [idealRun, PMF.mem_support_bind_iff] at hresult
  obtain ⟨endpoint, _, hresult⟩ := hresult
  rw [PMF.mem_support_map_iff] at hresult
  obtain ⟨output, houtput, rfl⟩ := hresult
  exact lazyRun_queryCount_le (auxiliary endpoint) (computation endpoint) observed budget (hbound endpoint) output houtput
theorem realRun_cost_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (payoff : State × (Result × (Fin n → State → Option State)) → ENNReal) :
    (1 - ((queryCount observed + budget : Nat) : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary computation observed result * payoff result) ≤
      ∑' result, realRun auxiliary computation observed result * payoff result := by
  rw [realRun_expectation, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hzero : idealRun auxiliary computation observed result = 0
  · simp only [hzero, zero_mul, mul_zero, le_refl]
  · have hlower := meanPreimages_ge_budget result.2.2 result.1 (queryCount observed + budget)
      (idealRun_queryCount_le auxiliary computation observed budget hbound result hzero)
    calc
      _ = idealRun auxiliary computation observed result *
          ((1 - ((queryCount observed + budget : Nat) : ENNReal) / Fintype.card State) * payoff result) := by ring
      _ ≤ _ := mul_le_mul_right (mul_le_mul_left hlower (payoff result)) _
theorem realRun_empty_cost_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (payoff : State × (Result × (Fin n → State → Option State)) → ENNReal) :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary computation (fun _ _ => none) result * payoff result) ≤
      ∑' result, realRun auxiliary computation (fun _ _ => none) result * payoff result := by
  simpa only [queryCount_empty, zero_add] using
    realRun_cost_lower auxiliary computation (fun _ _ => none) budget hbound payoff
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FrontierOracleMask ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def PrivateOtsPrefixInput (parameter : PublicParameter) (words : OtsReferenceWords) (input : HashInput) : Prop :=
  ∃ lay tree leaf chainIdx step,
    step.val < (words lay tree leaf chainIdx).val ∧
      AtPosition parameter input (.chain lay tree leaf chainIdx step)
theorem privateOtsPrefixInput_chain_iff (parameter : PublicParameter) (words : OtsReferenceWords)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (payload : HashInput) :
    PrivateOtsPrefixInput parameter words
        (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) ↔
      step.val < (words lay tree leaf chainIdx).val := by
  constructor
  · rintro ⟨otherLay, otherTree, otherLeaf, otherChain, otherStep, hlt, hat⟩
    have heq := atPosition_unique parameter
      (show AtPosition parameter (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload)
        (.chain lay tree leaf chainIdx step) from ⟨payload, rfl⟩) hat
    simp only [Position.chain.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    exact hlt
  · intro hlt
    exact ⟨lay, tree, leaf, chainIdx, step, hlt, payload, rfl⟩
theorem not_privateOtsPrefixInput_of_tag (parameter : PublicParameter) (words : OtsReferenceWords)
    (domain : HashDomain) (htag : (hashDomainFields domain).tag ≠ 1#8) (payload : HashInput) :
    ¬ PrivateOtsPrefixInput parameter words (tweakableHashInput parameter domain payload) := by
  rintro ⟨lay, tree, leaf, chainIdx, step, _, prefixPayload, heq⟩
  exact htag (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain
    (.chain lay tree leaf chainIdx step) payload prefixPayload heq)
def AgreeOutsideOtsPrefixes (parameter : PublicParameter) (words : OtsReferenceWords)
    (f g : QueryImpl HashSpec Id) : Prop :=
  ∀ input, ¬ PrivateOtsPrefixInput parameter words input → f input = g input
theorem AgreeOutsideOtsPrefixes.chain {parameter : PublicParameter} {words : OtsReferenceWords}
    {f g : QueryImpl HashSpec Id} (h : AgreeOutsideOtsPrefixes parameter words f g)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (hstep : (words lay tree leaf chainIdx).val ≤ step.val) (payload : HashInput) :
    f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) =
      g (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) := by
  apply h
  rw [privateOtsPrefixInput_chain_iff]
  exact not_lt_of_ge hstep
theorem AgreeOutsideOtsPrefixes.other {parameter : PublicParameter} {words : OtsReferenceWords}
    {f g : QueryImpl HashSpec Id} (h : AgreeOutsideOtsPrefixes parameter words f g)
    (domain : HashDomain) (htag : (hashDomainFields domain).tag ≠ 1#8) (payload : HashInput) :
    f (tweakableHashInput parameter domain payload) = g (tweakableHashInput parameter domain payload) :=
  h _ (not_privateOtsPrefixInput_of_tag parameter words domain htag payload)
noncomputable def maskOtsPrefixes (parameter : PublicParameter) (words : OtsReferenceWords)
    (f : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => if PrivateOtsPrefixInput parameter words input then 0 else f input
theorem maskOtsPrefixes_agrees (parameter : PublicParameter) (words : OtsReferenceWords)
    (f : QueryImpl HashSpec Id) : AgreeOutsideOtsPrefixes parameter words f (maskOtsPrefixes parameter words f) := by
  intro input hinput
  simp only [maskOtsPrefixes, if_neg hinput]
theorem maskOtsPrefixes_congr {parameter : PublicParameter} {words : OtsReferenceWords}
    {f g : QueryImpl HashSpec Id} (h : AgreeOutsideOtsPrefixes parameter words f g) :
    maskOtsPrefixes parameter words f = maskOtsPrefixes parameter words g := by
  funext input
  by_cases hinput : PrivateOtsPrefixInput parameter words input
  · simp only [maskOtsPrefixes, if_pos hinput]
  · simp only [maskOtsPrefixes, if_neg hinput, h input hinput]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_OtsPrefixOracle ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] chainWalk
noncomputable local instance instDecidableEqQueryImplHashInputHashSpecId : DecidableEq (QueryImpl HashSpec Id) := Classical.decEq _
noncomputable def otsChainFunctions (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin steps → Digest → Digest :=
  fun step value => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + step.val) 1 value)
theorem otsChainFunctions_tail (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin.tail (otsChainFunctions parameter lay tree leaf chainIdx start (steps + 1) f) =
      otsChainFunctions parameter lay tree leaf chainIdx (start + 1) steps f := by
  funext step value
  simp only [Fin.tail, otsChainFunctions, Fin.val_succ, Nat.add_right_comm start 1 step.val,
    Nat.add_assoc]
theorem otsChainFunctions_apply (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id)
    (step : Fin steps) (hstep : start + step.val < chainLength - 1) (value : Digest) :
    otsChainFunctions parameter lay tree leaf chainIdx start steps f step value =
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx ⟨start + step.val, hstep⟩)
        (digestBytes value))) := by
  simp only [otsChainFunctions, chainWalk, Nat.add_zero, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    dif_pos hstep, eval_tweakableHash]
theorem otsChainFunctions_evaluate (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) (value : Digest) :
    PartialChainEndpoint.evaluate (otsChainFunctions parameter lay tree leaf chainIdx start steps f) value =
      evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps generalizing start value with
  | zero => simp only [PartialChainEndpoint.evaluate, chainWalk, evalWithAnswerFn_pure]
  | succ steps ih =>
      rw [PartialChainEndpoint.evaluate, otsChainFunctions_tail, ih]
      change evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + 1) steps
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start 1 value))) = _
      simpa only [Nat.add_comm 1 steps] using
        (eval_chainWalk_add f parameter lay tree leaf chainIdx start 1 steps value).symm
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
structure OtsPrefix where
  parameter : PublicParameter
  lay : Layer
  tree : TreeIndex
  leaf : LeafIndex
  chainIdx : ChainIndex
  digit : Digit
namespace OtsPrefix
abbrev Query (segment : OtsPrefix) := Fin segment.digit.val × Digest
abbrev High := BitVec (hashOutputBits - digestBits)
def step (segment : OtsPrefix) (index : Fin segment.digit.val) : ChainStep :=
  ⟨index.val, by have := index.isLt; have := segment.digit.isLt; omega⟩
def input (segment : OtsPrefix) (query : segment.Query) : HashInput :=
  tweakableHashInput segment.parameter (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1))
    (digestBytes query.2)
theorem input_injective (segment : OtsPrefix) : Function.Injective segment.input := by
  intro left right heq
  have hparts := tweakableHashInput_injective segment.parameter (by trivial) (by trivial) heq
  have hstep : segment.step left.1 = segment.step right.1 := by
    simpa only [HashDomain.chain.injEq, true_and] using hparts.1
  have hindex : left.1.val = right.1.val := congrArg (fun position : ChainStep => position.val) hstep
  exact Prod.ext (Fin.ext hindex) (digestBytes_injective hparts.2)
noncomputable def parse (segment : OtsPrefix) (bytes : HashInput) : Option segment.Query :=
  if h : ∃ query, segment.input query = bytes then some h.choose else none
theorem parse_some_iff (segment : OtsPrefix) (bytes : HashInput) (query : segment.Query) :
    segment.parse bytes = some query ↔ bytes = segment.input query := by
  unfold parse
  split
  · rename_i hex
    rw [Option.some.injEq]
    constructor
    · intro heq
      rw [← heq]
      exact hex.choose_spec.symm
    · intro heq
      exact segment.input_injective (hex.choose_spec.trans heq)
  · rename_i hnone
    constructor
    · intro h
      cases h
    · intro heq
      exact False.elim (hnone ⟨query, heq.symm⟩)
theorem parse_input (segment : OtsPrefix) (query : segment.Query) : segment.parse (segment.input query) = some query :=
  (segment.parse_some_iff _ query).mpr rfl
noncomputable def combine (low : Digest) (high : High) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)
theorem split_combine (low : Digest) (high : High) : splitHashOutput digestBits (combine low high) = (low, high) := by
  exact (splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high)
theorem truncate_combine (low : Digest) (high : High) : truncateHash (combine low high) = low :=
  congrArg Prod.fst (split_combine low high)
theorem combine_split (output : HashOutput) :
    combine (truncateHash output) (splitHashOutput digestBits output).2 = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output
noncomputable def answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun bytes => match segment.parse bytes with
    | none => outside bytes
    | some query => combine (tables query.1 query.2) (high query)
theorem answer_input (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (query : segment.Query) :
    segment.answer tables high outside (segment.input query) = combine (tables query.1 query.2) (high query) := by
  simp only [answer, parse_input]
def lows (segment : OtsPrefix) (f : QueryImpl HashSpec Id) : Fin segment.digit.val → Digest → Digest :=
  fun index value => truncateHash (f (segment.input (index, value)))
def highs (segment : OtsPrefix) (f : QueryImpl HashSpec Id) : segment.Query → High :=
  fun query => (splitHashOutput digestBits (f (segment.input query))).2
theorem answer_original (segment : OtsPrefix) (f : QueryImpl HashSpec Id) :
    segment.answer (segment.lows f) (segment.highs f) f = f := by
  funext bytes
  cases hparse : segment.parse bytes with
  | none => simp only [answer, hparse]
  | some query =>
      have hinput := (segment.parse_some_iff bytes query).mp hparse
      rw [hinput, answer_input]
      exact combine_split (f (segment.input query))
theorem lows_eq_chainFunctions (segment : OtsPrefix) (f : QueryImpl HashSpec Id) :
    segment.lows f = otsChainFunctions segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val f := by
  funext index value
  rw [otsChainFunctions_apply segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val f
    index (by have := (segment.step index).isLt; simpa only [step, Nat.zero_add] using this) value]
  simp only [lows, input, step]
  congr 4
  exact Fin.ext (Nat.zero_add index.val).symm
theorem evaluate_lows (segment : OtsPrefix) (f : QueryImpl HashSpec Id) (secret : Digest) :
    PartialChainEndpoint.evaluate (segment.lows f) secret =
      evalWithAnswerFn f (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val secret) := by
  rw [lows_eq_chainFunctions, otsChainFunctions_evaluate]
theorem input_private (segment : OtsPrefix) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val) (query : segment.Query) :
    PrivateOtsPrefixInput segment.parameter words (segment.input query) := by
  rw [input, privateOtsPrefixInput_chain_iff]
  exact query.1.isLt.trans_le hword
theorem answer_agrees_outside (segment : OtsPrefix) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    AgreeOutsideOtsPrefixes segment.parameter words (segment.answer tables high outside) outside := by
  intro bytes hnot
  cases hparse : segment.parse bytes with
  | none => simp only [answer, hparse]
  | some query =>
      have hinput := (segment.parse_some_iff bytes query).mp hparse
      exact False.elim (hnot (hinput ▸ segment.input_private words hword query))
theorem mask_answer (segment : OtsPrefix) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    maskOtsPrefixes segment.parameter words (segment.answer tables high outside) = maskOtsPrefixes segment.parameter words outside :=
  maskOtsPrefixes_congr (segment.answer_agrees_outside words hword tables high outside)
end OtsPrefix
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_CanonicalGraph ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
abbrev CanonicalGraphLabels := Position → HashOutput
def canonicalGraphSlots
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (labels : CanonicalGraphLabels) : Position → List Digest
  | .chain lay tree leaf chain step =>
      if step.val = 0 then [otsSecret lay tree leaf chain]
      else (Position.chain lay tree leaf chain step).children.map (fun child => truncateHash (labels child))
  | .ftsLeaf index tree leaf => [ftsSecret index tree leaf]
  | position => position.children.map (fun child => truncateHash (labels child))
def canonicalGraphInput (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (position : Position) (labels : CanonicalGraphLabels) : HashInput :=
  tweakableHashInput parameter position.domain
    ((canonicalGraphSlots otsSecret ftsSecret labels position).flatMap digestBytes)
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
theorem canonicalGraphInput_separated :
    FiniteGraphSampling.Separated (canonicalGraphInput parameter otsSecret ftsSecret) := by
  intro left right hne before after heq
  exact hne (Position.domain_injective
    (tweakableHashInput_injective parameter left.domain_inRange right.domain_inRange heq).1)
theorem canonicalGraphInput_congr (position : Position) (left right : CanonicalGraphLabels)
    (hchildren : ∀ child ∈ position.children, truncateHash (left child) = truncateHash (right child)) :
    canonicalGraphInput parameter otsSecret ftsSecret position left =
      canonicalGraphInput parameter otsSecret ftsSecret position right := by
  have hmap := List.map_congr_left hchildren
  apply congrArg (fun values : List Digest =>
    tweakableHashInput parameter position.domain (values.flatMap digestBytes))
  cases position <;> simp only [canonicalGraphSlots] <;>
    first | rfl | exact hmap | (split_ifs <;> first | rfl | exact hmap)
theorem canonicalGraphInput_eq_honest (f : QueryImpl HashSpec Id) (position : Position)
    (hvalid : position.Valid) (labels : CanonicalGraphLabels)
    (hchildren : ∀ child ∈ position.children,
      truncateHash (labels child) = honestValue f parameter otsSecret ftsSecret child) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels =
      honestInput f parameter otsSecret ftsSecret position := by
  rw [honestInput, honestPayload_eq_slots f parameter otsSecret ftsSecret hvalid]
  have hmap := List.map_congr_left hchildren
  apply congrArg (fun values : List Digest =>
    tweakableHashInput parameter position.domain (values.flatMap digestBytes))
  cases position <;> simp only [canonicalGraphSlots, slots, childValues] <;>
    first | rfl | exact hmap | (split_ifs <;> first | rfl | exact hmap)
def readCanonicalGraph (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels) : CanonicalGraphLabels :=
  FiniteGraphSampling.read (canonicalGraphInput parameter otsSecret ftsSecret)
    (fun position output values => Function.update values position output) f positions labels
theorem readCanonicalGraph_preserves (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels) (position : Position) (hposition : position ∉ positions) :
    readCanonicalGraph parameter otsSecret ftsSecret f positions labels position = labels position := by
  induction positions generalizing labels with
  | nil => rfl
  | cons first rest ih =>
      have hne : position ≠ first := fun h => hposition (by simp [h])
      have hrest : position ∉ rest := fun h => hposition (List.mem_cons_of_mem _ h)
      change readCanonicalGraph parameter otsSecret ftsSecret f rest
        (Function.update labels first (f (canonicalGraphInput parameter otsSecret ftsSecret first labels))) position = _
      rw [ih _ hrest, Function.update_of_ne hne]
theorem readCanonicalGraph_consistent (f : QueryImpl HashSpec Id) (positions : List Position)
    (hnodup : positions.Nodup)
    (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth))
    (labels : CanonicalGraphLabels) :
    ∀ position ∈ positions,
      readCanonicalGraph parameter otsSecret ftsSecret f positions labels position =
        f (canonicalGraphInput parameter otsSecret ftsSecret position
          (readCanonicalGraph parameter otsSecret ftsSecret f positions labels)) := by
  induction positions generalizing labels with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      intro position hposition
      rcases List.mem_cons.mp hposition with hposition | hposition
      · subst position
        have hinput : canonicalGraphInput parameter otsSecret ftsSecret first
            (readCanonicalGraph parameter otsSecret ftsSecret f (first :: rest) labels) =
              canonicalGraphInput parameter otsSecret ftsSecret first labels := by
          apply canonicalGraphInput_congr
          intro child hchild
          apply congrArg truncateHash
          apply readCanonicalGraph_preserves
          intro hmem
          have hlt := Position.depth_lt_of_mem_children hchild
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst child
            omega
          · have := hdepth child hmem
            omega
        rw [hinput]
        change readCanonicalGraph parameter otsSecret ftsSecret f rest
          (Function.update labels first (f (canonicalGraphInput parameter otsSecret ftsSecret first labels))) first = _
        rw [readCanonicalGraph_preserves _ _ _ _ _ _ _ hfirst, Function.update_self]
      · exact ih hrest hsorted _ position hposition
noncomputable def canonicalGraphOrder : List Position :=
  (Finset.univ : Finset Position).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))
theorem canonicalGraphOrder_nodup : canonicalGraphOrder.Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
theorem mem_canonicalGraphOrder (position : Position) : position ∈ canonicalGraphOrder := by
  rw [canonicalGraphOrder, List.mem_mergeSort]
  simp
theorem canonicalGraphOrder_sorted :
    canonicalGraphOrder.Pairwise (fun left right => left.depth ≤ right.depth) := by
  have h := List.pairwise_mergeSort
    (le := fun left right : Position => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    (Finset.univ : Finset Position).toList
  simpa only [canonicalGraphOrder, decide_eq_true_eq] using h
noncomputable def canonicalGraphLabels (f : QueryImpl HashSpec Id) : CanonicalGraphLabels :=
  readCanonicalGraph parameter otsSecret ftsSecret f canonicalGraphOrder (fun _ => 0)
theorem canonicalGraphLabels_consistent (f : QueryImpl HashSpec Id) (position : Position) :
    canonicalGraphLabels parameter otsSecret ftsSecret f position =
      f (canonicalGraphInput parameter otsSecret ftsSecret position
        (canonicalGraphLabels parameter otsSecret ftsSecret f)) :=
  readCanonicalGraph_consistent parameter otsSecret ftsSecret f canonicalGraphOrder
    canonicalGraphOrder_nodup canonicalGraphOrder_sorted _ position (mem_canonicalGraphOrder position)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_CanonicalGraphHonest ====
section

namespace SphincsSecurity
namespace Position
def TreeBound : Position → Prop
  | .node _ _ level index => 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ maxLayerHeight
  | .ftsNode _ _ heap => 0 < heap.val
  | _ => True
theorem TreeBound.valid (position : Position) (h : position.TreeBound) : position.Valid := by
  cases position with
  | node lay tree level index =>
      have hpow : 0 < (2 : Nat) ^ level.val := pow_pos (by decide) _
      have hmul := Nat.mul_le_mul_right (index.val + 1) (show 2 ≤ 2 ^ (level.val + 1) by
        rw [pow_succ]; omega)
      change 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ maxLayerHeight at h
      change 2 * index.val + 1 < 2 ^ maxLayerHeight
      omega
  | ftsNode index tree heap => exact h
  | chain | leaf | ftsLeaf => trivial
private theorem treeBound_children_arithmetic (height level index : Nat)
    (h : 2 ^ (level + 1) * (index + 1) ≤ 2 ^ height) :
    2 ^ level * (2 * index + 1) ≤ 2 ^ height ∧
      2 ^ level * (2 * index + 1 + 1) ≤ 2 ^ height := by
  rw [pow_succ] at h
  constructor <;> nlinarith [Nat.zero_le (2 ^ level)]
theorem TreeBound.child {position child : Position} (h : position.TreeBound)
    (hchild : child ∈ position.children) : child.TreeBound := by
  cases position with
  | chain lay tree leaf chain step =>
      simp only [children] at hchild
      split_ifs at hchild with hstep
      · rw [List.mem_singleton] at hchild
        subst child
        trivial
      · simp at hchild
  | leaf lay tree leaf =>
      simp only [children, List.mem_ofFn] at hchild
      obtain ⟨chain, rfl⟩ := hchild
      trivial
  | node lay tree level index =>
      have hvalid : 2 * index.val + 1 < 2 ^ maxLayerHeight := TreeBound.valid _ h
      rw [children, dif_pos hvalid] at hchild
      split_ifs at hchild with hlevel
      · have bounds := treeBound_children_arithmetic maxLayerHeight level.val index.val h
        rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;>
          simp only [TreeBound, show level.val - 1 + 1 = level.val by omega] <;>
          first | exact bounds.1 | exact bounds.2
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;> trivial
  | ftsLeaf => simp [children] at hchild
  | ftsNode index tree heap =>
      have hpos : 0 < heap.val := h
      rw [children, dif_pos hpos] at hchild
      split_ifs at hchild with hidx
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;>
          simp only [TreeBound] <;> omega
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;> trivial
end Position
namespace Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
theorem canonicalGraphLabels_eq_honest (f : QueryImpl HashSpec Id)
    (position : Position) (hbound : position.TreeBound) :
    canonicalGraphLabels parameter otsSecret ftsSecret f position =
      f (honestInput f parameter otsSecret ftsSecret position) := by
  induction hdepth : position.depth using Nat.strong_induction_on generalizing position with
  | h depth ih =>
      rw [canonicalGraphLabels_consistent]
      apply congrArg f
      apply canonicalGraphInput_eq_honest parameter otsSecret ftsSecret f position (hbound.valid position)
      intro child hchild
      have hlt : child.depth < depth := by
        rw [← hdepth]
        exact Position.depth_lt_of_mem_children hchild
      rw [ih child.depth hlt child (hbound.child hchild) rfl]
      rfl
theorem canonicalGraphLabels_chain (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (.chain lay tree leaf chain step)) =
      honestChain f parameter lay tree leaf chain (otsSecret lay tree leaf chain) (step.val + 1) := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ (by trivial)]
  exact honestValue_chain f parameter otsSecret ftsSecret lay tree leaf chain step
def canonicalGraphRoot (labels : CanonicalGraphLabels) : Digest :=
  truncateHash (labels (.node topLayer rootTree ⟨maxLayerHeight - 1, by decide⟩ ⟨0, by positivity⟩))
theorem canonicalGraphLabels_root (f : QueryImpl HashSpec Id) :
    canonicalGraphRoot (canonicalGraphLabels parameter otsSecret ftsSecret f) =
      evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) := by
  rw [canonicalGraphRoot, canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _
    (by norm_num [Position.TreeBound, maxLayerHeight])]
  change honestValue f parameter otsSecret ftsSecret _ = _
  rw [honestValue_node]
  rfl
def graphTop (labels : CanonicalGraphLabels) (level nodeIdx : Nat) : Digest :=
  if hnode : nodeIdx < 2 ^ maxLayerHeight then
    if level = 0 then truncateHash (labels (.leaf topLayer rootTree ⟨nodeIdx, hnode⟩))
    else if hlevel : level - 1 < maxLayerHeight then
      truncateHash (labels (.node topLayer rootTree ⟨level - 1, hlevel⟩ ⟨nodeIdx, hnode⟩))
    else 0
  else 0
theorem graphTop_canonical (f : QueryImpl HashSpec Id) (level : Nat) (hlevel : level ≤ maxLayerHeight)
    (nodeIdx : Nat) (hnodeIdx : nodeIdx < 2 ^ (maxLayerHeight - level)) :
    graphTop (canonicalGraphLabels parameter otsSecret ftsSecret f) level nodeIdx =
      honestNode f parameter topLayer rootTree (otsSecret topLayer rootTree) level nodeIdx := by
  have hnode : nodeIdx < 2 ^ maxLayerHeight :=
    Nat.lt_of_lt_of_le hnodeIdx (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  unfold graphTop
  rw [dif_pos hnode]
  split_ifs with hzero hlevel'
  · subst hzero
    rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f (.leaf topLayer rootTree ⟨nodeIdx, hnode⟩) trivial]
    exact honestValue_leaf f parameter otsSecret ftsSecret topLayer rootTree ⟨nodeIdx, hnode⟩
  · have hbound : (Position.node topLayer rootTree ⟨level - 1, hlevel'⟩ ⟨nodeIdx, hnode⟩).TreeBound := by
      change 2 ^ (level - 1 + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight
      rw [show level - 1 + 1 = level by omega]
      have h1 : nodeIdx + 1 ≤ 2 ^ (maxLayerHeight - level) := hnodeIdx
      calc 2 ^ level * (nodeIdx + 1) ≤ 2 ^ level * 2 ^ (maxLayerHeight - level) :=
            Nat.mul_le_mul_left _ h1
        _ = 2 ^ maxLayerHeight := by rw [← pow_add]; congr 1; omega
    rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ hbound]
    have h := honestValue_node f parameter otsSecret ftsSecret topLayer rootTree ⟨level - 1, hlevel'⟩ ⟨nodeIdx, hnode⟩
    simp only [show level - 1 + 1 = level by omega] at h
    exact h
  · omega
theorem keyTopHonest_of_graphTop (key : SecretKey) (f : QueryImpl HashSpec Id)
    (htop : ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
      key.top level nodeIdx =
        graphTop (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) level nodeIdx) :
    KeyTopHonest f key := by
  intro level hlevel nodeIdx hnodeIdx
  rw [evalWithAnswerFn_pure, htop level hlevel nodeIdx hnodeIdx]
  exact graphTop_canonical key.parameter key.otsSecret key.ftsSecret f level hlevel.le nodeIdx hnodeIdx
def TopFromGraph (key : SecretKey) (labels : CanonicalGraphLabels) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    key.top level nodeIdx = graphTop labels level nodeIdx
noncomputable abbrev keyAtRoot (f : QueryImpl HashSpec Id) (key : SecretKey) (root : Digest) : SecretKey :=
  { key with root := root, top := honestTop f key.parameter (key.otsSecret topLayer rootTree) }
abbrev keyAtLabels (key : SecretKey) (labels : CanonicalGraphLabels) : SecretKey :=
  { key with root := canonicalGraphRoot labels, top := graphTop labels }
theorem topFromGraph_keyAtLabels (key : SecretKey) (labels : CanonicalGraphLabels) :
    TopFromGraph (keyAtLabels key labels) labels := fun _ _ _ _ => rfl
theorem keyTopHonest_keyAtRoot (f : QueryImpl HashSpec Id) (key : SecretKey) (root : Digest) :
    KeyTopHonest f (keyAtRoot f key root) :=
  keyTopHonest_of_eq f _ rfl
theorem topFromGraph_keyAtRoot (f : QueryImpl HashSpec Id) (key : SecretKey) (root : Digest) :
    TopFromGraph (keyAtRoot f key root) (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) := by
  intro level hlevel nodeIdx hnodeIdx
  have h := keyTopHonest_keyAtRoot f key root level hlevel nodeIdx hnodeIdx
  rw [evalWithAnswerFn_pure] at h
  rw [h]
  exact (graphTop_canonical key.parameter key.otsSecret key.ftsSecret f level hlevel.le nodeIdx hnodeIdx).symm
def canonicalGraphFrontier (labels : CanonicalGraphLabels) (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chain =>
    if h : (words lay tree leaf chain).val = 0 then otsSecret lay tree leaf chain
    else truncateHash (labels (.chain lay tree leaf chain
      ⟨(words lay tree leaf chain).val - 1, by have := (words lay tree leaf chain).isLt; omega⟩))
theorem canonicalGraphLabels_frontier (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (root : Digest) (top : Nat → Nat → Digest) :
    canonicalGraphFrontier otsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f) words =
      canonicalFrontierValues ⟨parameter, root, otsSecret, ftsSecret, top⟩ f words := by
  funext lay tree leaf chain
  simp only [canonicalGraphFrontier, canonicalFrontierValues]
  split_ifs with hzero
  · rw [hzero]
    simp [chainWalk]
  · rw [canonicalGraphLabels_chain]
    have hstep : (words lay tree leaf chain).val - 1 + 1 = (words lay tree leaf chain).val := by omega
    simp only [hstep, honestChain]
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Ots_EncodingInputs ====
section

namespace SphincsSecurity.Concrete
noncomputable def canonicalEncodingInputs (parameter : PublicParameter) : Finset HashInput :=
  Finset.univ.biUnion fun position : EncodingPosition =>
    (Finset.univ : Finset (Digest × Fin (2 ^ counterBits))).image fun pair =>
      encodingRetryInput parameter position pair.1 pair.2.val
attribute [local irreducible] canonicalEncodingInputs
theorem encodingRetryInput_mem_canonicalEncodingInputs_wide (parameter : PublicParameter)
    (position : EncodingPosition) (message : Digest) (counter : Fin (2 ^ counterBits)) :
    encodingRetryInput parameter position message counter.val ∈ canonicalEncodingInputs parameter := by
  classical
  rw [canonicalEncodingInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨position, ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(message, counter), rfl⟩
theorem encodingRetryInput_mem_canonicalEncodingInputs (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Fin encodingAttemptLimit) :
    encodingRetryInput parameter position message counter.val ∈ canonicalEncodingInputs parameter :=
  encodingRetryInput_mem_canonicalEncodingInputs_wide parameter position message
    ⟨counter.val, lt_of_lt_of_le counter.isLt (by decide)⟩
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_ReferenceEncodingTable ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def decodeEncodingOutput (output : HashOutput) : Option Encoding := OtsCode.decode (truncateHash output)
def referenceEncodingTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (attempts start : Nat) : Fin attempts → HashOutput :=
  fun index => f (encodingRetryInput parameter position message (start + index.val))
def encodingTableResult {n : Nat} (table : Fin n → HashOutput) (start : Nat) : Option (Counter × Encoding) × Nat :=
  let result := FirstSuccessTable.select decodeEncodingOutput table
  (result.map (fun result => (BitVec.ofNat counterBits (start + result.1.val), result.2)),
    result.elim n (fun result => result.1.val + 1))
theorem eval_encode_eq_decodeEncodingOutput (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (counter : Nat) :
    evalWithAnswerFn f (encodeAttempt parameter position.lay position.tree position.leafIdx message
      (BitVec.ofNat counterBits counter)) =
        decodeEncodingOutput (f (encodingRetryInput parameter position message counter)) := by
  simp only [encodeAttempt, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure]
  rfl
theorem referenceEncodingSearch_eq_table (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (attempts start : Nat) :
    referenceEncodingSearch parameter f position.lay position.tree position.leafIdx message attempts start =
      encodingTableResult (referenceEncodingTable parameter f position message attempts start) start := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      have htail :
          (fun i : Fin attempts => referenceEncodingTable parameter f position message (attempts + 1) start i.succ) =
            referenceEncodingTable parameter f position message attempts (start + 1) := by
        funext i
        change f (encodingRetryInput parameter position message (start + (i.val + 1))) =
          f (encodingRetryInput parameter position message (start + 1 + i.val))
        rw [show start + (i.val + 1) = start + 1 + i.val by omega]
      rw [referenceEncodingSearch, eval_encode_eq_decodeEncodingOutput,
        encodingTableResult, FirstSuccessTable.select]
      have hzero : referenceEncodingTable parameter f position message (attempts + 1) start 0 =
          f (encodingRetryInput parameter position message start) := by simp [referenceEncodingTable]
      rw [hzero]
      cases hdecode : decodeEncodingOutput (f (encodingRetryInput parameter position message start)) with
      | some word => simp
      | none =>
          rw [htail, ih]
          unfold encodingTableResult
          cases hselected : FirstSuccessTable.select decodeEncodingOutput
              (referenceEncodingTable parameter f position message attempts (start + 1)) with
          | none => simp [Nat.add_comm]
          | some result =>
              rcases result with ⟨index, word⟩
              simp [Nat.add_comm, Nat.add_left_comm]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_CanonicalEncodingSampling ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def canonicalGraphMessage (labels : CanonicalGraphLabels) (position : EncodingPosition) : Digest :=
  truncateHash (labels (layerMessagePosition
    (referenceIndex position.lay position.tree position.leafIdx) position.lay))
theorem layerMessagePosition_treeBound (index : Index) (lay : Layer) :
    (layerMessagePosition index lay).TreeBound := by
  unfold layerMessagePosition
  split_ifs with hbelow
  · simp only [Position.TreeBound, zero_add, mul_one]
    have hpos := layerHeight_pos ⟨lay.val + 1, hbelow⟩
    have hle := layerHeight_le ⟨lay.val + 1, hbelow⟩
    rw [Nat.sub_add_cancel hpos]
    exact Nat.pow_le_pow_right (by omega) hle
  · show 0 < 1
    omega
theorem canonicalGraphMessage_eq (key : SecretKey) (f : QueryImpl HashSpec Id) (position : EncodingPosition) :
    canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) position =
      evalWithAnswerFn f (layerMessage key (referenceIndex position.lay position.tree position.leafIdx) position.lay) := by
  rw [canonicalGraphMessage, canonicalGraphLabels_eq_honest _ _ _ _ _ (layerMessagePosition_treeBound _ _),
    eval_layerMessage_eq_honestValue]
  rfl
theorem canonicalEncodingSearch_eq_graph_table (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    canonicalEncodingSearch key f position.lay position.tree position.leafIdx =
      encodingTableResult (referenceEncodingTable key.parameter f position
        (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) position)
        encodingAttemptLimit 0) 0 := by
  rw [canonicalEncodingSearch, canonicalGraphMessage_eq, referenceEncodingSearch_eq_table]
abbrev EncodingRow := EncodingPosition × Fin encodingAttemptLimit
abbrev CanonicalEncodingRows := EncodingRow → HashOutput
noncomputable def canonicalEncodingRowInput (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (row : EncodingRow) : HashInput :=
  encodingRetryInput parameter row.1 (canonicalGraphMessage labels row.1) row.2.val
theorem canonicalEncodingRowInput_injective (parameter : PublicParameter) (labels : CanonicalGraphLabels) :
    Function.Injective (canonicalEncodingRowInput parameter labels) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ heq
  have hposition : left = right := atEncodingPosition_unique
    (show AtEncodingPosition parameter (canonicalEncodingRowInput parameter labels (left, first)) left from ⟨_, rfl⟩)
    (show AtEncodingPosition parameter (canonicalEncodingRowInput parameter labels (left, first)) right from
      ⟨_, heq⟩)
  subst right
  have hcounter := encodingRetryInput_injective_of_lt first.isLt second.isLt heq
  exact Prod.ext rfl (Fin.ext hcounter)
attribute [local irreducible] canonicalEncodingInputs
theorem canonicalEncodingRowInput_mem (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (row : EncodingRow) : canonicalEncodingRowInput parameter labels row ∈ canonicalEncodingInputs parameter := by
  exact encodingRetryInput_mem_canonicalEncodingInputs parameter row.1 _ row.2
noncomputable def canonicalEncodingCell (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) (row : EncodingRow) : inputs :=
  ⟨canonicalEncodingRowInput parameter labels row, hinputs (canonicalEncodingRowInput_mem parameter labels row)⟩
theorem canonicalEncodingCell_injective (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) :
    Function.Injective (canonicalEncodingCell parameter inputs hinputs labels) := by
  intro left right heq
  exact canonicalEncodingRowInput_injective parameter labels (congrArg Subtype.val heq)
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_2 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)
noncomputable local instance instSampleableTypeCanonicalGraphLabels_1 : SampleableType CanonicalGraphLabels := SampleableType.ofFintype CanonicalGraphLabels
noncomputable local instance instSampleableTypeCanonicalEncodingRows : SampleableType CanonicalEncodingRows := SampleableType.ofFintype CanonicalEncodingRows
noncomputable local instance instSampleableTypeForallFinEncodingAttemptLimitHashOutput : SampleableType (Fin encodingAttemptLimit → HashOutput) :=
  SampleableType.ofFintype (Fin encodingAttemptLimit → HashOutput)
noncomputable def readCanonicalEncodingRows (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) : CanonicalEncodingRows := fun row => f (canonicalEncodingRowInput parameter labels row)
theorem readCanonicalEncodingRows_finite (parameter : PublicParameter) (inputs : Finset HashInput)
    (hinputs : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (table : inputs → HashOutput) :
    readCanonicalEncodingRows parameter labels (finiteHashAnswer ∅ inputs table) =
      table ∘ canonicalEncodingCell parameter inputs hinputs labels := by
  funext row
  exact finiteHashAnswer_none ∅ inputs table _ (hinputs (canonicalEncodingRowInput_mem parameter labels row)) (by simp)
def canonicalEncodingResults (rows : CanonicalEncodingRows) : EncodingPosition → Option (Counter × Encoding) × Nat :=
  fun position => encodingTableResult (fun counter => rows (position, counter)) 0
theorem canonicalEncodingResults_eq (key : SecretKey) (f : QueryImpl HashSpec Id) :
    canonicalEncodingResults (readCanonicalEncodingRows key.parameter
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) f) =
        fun position => canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  funext position
  rw [canonicalEncodingSearch_eq_graph_table]
  apply congrArg (fun table => encodingTableResult table 0)
  funext counter
  simp only [readCanonicalEncodingRows, canonicalEncodingRowInput, referenceEncodingTable]
  rw [Nat.zero_add]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FrontierGameProjection ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem simulateQ_writer_compose {ι₁ ι₂ α ω : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m] [Monoid ω]
    (first : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))) (second : QueryImpl spec₂ m)
    (combined : QueryImpl spec₁ (WriterT ω m))
    (hquery : ∀ input, simulateQ second (first input).run = (combined input).run)
    (computation : OracleComp spec₁ α) :
    simulateQ second (simulateQ first computation).run = (simulateQ combined computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query, simulateQ_map, hquery]
      apply bind_congr
      rintro ⟨output, trace⟩
      rw [ih]
theorem simulateQ_writerAppend_compose {ι₁ ι₂ α ω : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m] [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (first : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))) (second : QueryImpl spec₂ m)
    (combined : QueryImpl spec₁ (WriterT ω m))
    (hquery : ∀ input, simulateQ second (first input).run = (combined input).run)
    (computation : OracleComp spec₁ α) :
    simulateQ second (simulateQ first computation).run = (simulateQ combined computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query, simulateQ_map, hquery]
      apply bind_congr
      rintro ⟨output, trace⟩
      rw [ih]
noncomputable def boundaryComputation {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × SigningBoundaryTrace) :=
  (simulateQ ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter)) computation).run
theorem simulateQ_boundaryComputation {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (parameter : PublicParameter) (impl : QueryImpl OracleWorld m) (computation : OracleComp OracleWorld α) :
    simulateQ impl (boundaryComputation parameter computation) =
      (simulateQ (impl.withTrace (signingBoundaryTrace parameter)) computation).run := by
  apply simulateQ_writer_compose
  intro input
  simp [QueryImpl.withTrace_apply]
theorem boundaryRun_fst_eq_boundaryComputation {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Prod.fst <$> boundaryRun parameter computation cache =
      (simulateQ romImpl (boundaryComputation parameter computation)).run' cache := by
  rw [simulateQ_boundaryComputation, StateT.run'_eq]
  rfl
theorem fixedBoundaryRun_eq_boundaryComputation {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld α) :
    fixedBoundaryRun parameter f computation =
      simulateQ (fixedHashWorld f) (boundaryComputation parameter computation) :=
  (simulateQ_boundaryComputation parameter (fixedHashWorld f) computation).symm
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval frontierTreeNode
theorem simulateQ_eq_fixedBoundaryRun {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) :
    simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter)) computation =
      WriterT.mk (fixedBoundaryRun parameter f computation) := rfl
theorem signDigestLoop_congr_key (attempts : Nat) (key key' : SecretKey)
    (hparameter : key.parameter = key'.parameter) (hroot : key.root = key'.root) (message : Message) :
    signDigestLoop attempts key message = signDigestLoop attempts key' message := by
  induction attempts with
  | zero => rw [signDigestLoop, signDigestLoop]
  | succ attempts ih =>
      have hattempt : (fun randomness => (signAttempt key message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) =
          fun randomness => signAttempt key' message randomness := by
        funext randomness
        unfold signAttempt
        rw [hparameter, hroot]
      rw [signDigestLoop, signDigestLoop]
      simp only [ih]
      exact congrArg (fun attempt => (liftM sampleRandomness : OracleComp OracleWorld Randomness) >>= fun randomness =>
        (liftM (attempt randomness) : OracleComp OracleWorld _) >>= fun result => match result with
          | some (index, leaves) => pure (some (randomness, index, leaves))
          | none => signDigestLoop attempts key' message) hattempt
theorem sign_congr_top (key key' : SecretKey) (hparameter : key.parameter = key'.parameter)
    (hroot : key.root = key'.root) (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx))) (message : Message) :
    sign key message = sign key' message := by
  rw [sign_eq, sign_eq, signDigestLoop_congr_key digestAttemptLimit key key' hparameter hroot message]
  congr 1
  funext selected
  rcases selected with _ | ⟨randomness, index, leaves⟩
  · rfl
  · simp only [signAfterDigest_congr_top key key' hparameter hots hfts htop]
theorem gameRest_congr_top (adversary : Adversary) (publicKey : PublicKey) (key key' : SecretKey)
    (hparameter : key.parameter = key'.parameter)
    (hroot : key.root = key'.root) (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx))) :
    gameRest scheme adversary publicKey key = gameRest scheme adversary publicKey key' := by
  have hsign : scheme.sign key = scheme.sign key' :=
    funext (sign_congr_top key key' hparameter hroot hots hfts htop)
  unfold gameRest signingOracle
  rw [hsign]
abbrev KeyCode :=
  PublicParameter × Digest × (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ×
    (Index → FtsTree → FtsLeaf → Digest) × (Fin maxLayerHeight → Fin (2 ^ maxLayerHeight) → Digest)
def KeyCode.key (code : KeyCode) : SecretKey :=
  ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1, fun level nodeIdx =>
    if h : level < maxLayerHeight ∧ nodeIdx < 2 ^ maxLayerHeight then code.2.2.2.2 ⟨level, h.1⟩ ⟨nodeIdx, h.2⟩
    else 0⟩
def keyCode (key : SecretKey) : KeyCode :=
  (key.parameter, key.root, key.otsSecret, key.ftsSecret, fun level nodeIdx => key.top level.val nodeIdx.val)
theorem keyCode_top (key : SecretKey) :
    TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure ((keyCode key).key.top level nodeIdx))
      (fun level nodeIdx => pure (key.top level nodeIdx)) := by
  intro level hlevel nodeIdx hnodeIdx
  have hnode : nodeIdx < 2 ^ maxLayerHeight :=
    Nat.lt_of_lt_of_le hnodeIdx (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  simp only [KeyCode.key, keyCode, dif_pos (And.intro hlevel hnode)]
noncomputable instance keyCodeFintype : Fintype KeyCode := by
  classical
  infer_instance
attribute [irreducible] keyCodeFintype
theorem gameRest_keyCode (adversary : Adversary) (key : SecretKey) :
    gameRest scheme adversary ⟨(keyCode key).key.root, (keyCode key).key.parameter⟩ (keyCode key).key =
      gameRest scheme adversary ⟨key.root, key.parameter⟩ key :=
  gameRest_congr_top adversary _ _ _ rfl rfl rfl rfl (keyCode_top key)
noncomputable def frontierAdversaryImpl (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp)
  | .inl input => (fixedHashWorld f).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk (frontierSigningRun parameter root f ftsSecret words frontier message)
theorem simulateQ_expandedAdversaryImpl_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace key.parameter)) (expandedAdversaryImpl key input) =
      frontierAdversaryImpl key.parameter key.root f key.ftsSecret words frontier input := by
  cases input with
  | inl input => exact simulateQ_spec_query (impl := (fixedHashWorld f).withTrace (signingBoundaryTrace key.parameter)) input
  | inr message =>
      rw [show expandedAdversaryImpl key (.inr message) = sign key message from rfl,
        simulateQ_eq_fixedBoundaryRun]
      unfold frontierAdversaryImpl
      exact congrArg (fun result : ProbComp (Option Signature × SigningBoundaryTrace) =>
        (WriterT.mk result : WriterT SigningBoundaryTrace ProbComp (Option Signature)))
        (fixedBoundaryRun_sign_frontier key f words frontier hfrontier htop hwords message)
noncomputable def frontierAdversaryRun {α : Type} (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp ((α × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  ((simulateQ ((frontierAdversaryImpl parameter root f ftsSecret words frontier).withTraceAppend signingLogFragment)
    computation).run).run
theorem fixedBoundaryRun_adversary_frontier {α : Type} (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    fixedBoundaryRun key.parameter f
        (simulateQ (forwardOracles + signingOracle scheme key) computation).run =
      frontierAdversaryRun key.parameter key.root f key.ftsSecret words frontier computation := by
  rw [forwardOracles_add_signingOracle_eq_withTraceAppend]
  unfold fixedBoundaryRun frontierAdversaryRun
  congr 1
  apply simulateQ_writerAppend_compose
  intro input
  simp only [QueryImpl.withTraceAppend_apply]
  simp [simulateQ_expandedAdversaryImpl_frontier key f words frontier hfrontier htop hwords input]
noncomputable def frontierGameRest (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let result ← frontierAdversaryRun parameter root f ftsSecret words frontier
    (adversary.main ⟨root, parameter⟩)
  let checked := boundaryEval parameter f (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature)
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)
theorem fixedBoundaryRun_gameRest_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (adversary : Adversary) :
    fixedBoundaryRun key.parameter f (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) =
      frontierGameRest key.parameter key.root f key.ftsSecret words frontier adversary := by
  rw [gameRest, fixedBoundaryRun_bind, fixedBoundaryRun_adversary_frontier key f words frontier hfrontier htop hwords]
  unfold frontierGameRest
  apply bind_congr
  rintro ⟨⟨forgery, log⟩, trace⟩
  rw [fixedBoundaryRun_bind]
  change (fun final => (final.1, trace * final.2)) <$>
    (fixedBoundaryRun key.parameter f (liftM (verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature)) >>=
      fun checked => (fun final => (final.1, checked.2 * final.2)) <$>
        fixedBoundaryRun key.parameter f (pure
          (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && checked.1))) = _
  rw [fixedBoundaryRun_lift_hash, pure_bind, fixedBoundaryRun_pure]
  simp only [map_pure, mul_one]
noncomputable def frontierRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) : Digest :=
  evalWithAnswerFn f (frontierTreeNode parameter topLayer rootTree (words topLayer rootTree)
    (frontier topLayer rootTree) (layerHeight topLayer) 0)
theorem frontierRoot_eq (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) :
    frontierRoot key.parameter f words frontier =
      evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)) :=
  eval_frontierTreeNode key.parameter f topLayer rootTree (key.otsSecret topLayer rootTree)
    (words topLayer rootTree) (frontier topLayer rootTree) (hfrontier topLayer rootTree) _ _
noncomputable def frontierGame (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ keygenHashCost * result.2)) <$>
    frontierGameRest parameter (frontierRoot parameter f words frontier) f ftsSecret words frontier adversary
theorem fixedBoundaryRun_gameAfterSecrets_canonical (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) :
    let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
    let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret, honestTop f parameter (otsSecret topLayer rootTree)⟩
    let words := canonicalReferenceWords key f dummy
    fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) =
      frontierGame parameter f ftsSecret words (canonicalFrontierValues key f words) adversary := by
  dsimp only
  let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let top := honestTop f parameter (otsSecret topLayer rootTree)
  let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret, top⟩
  let words := canonicalReferenceWords key f dummy
  let frontier := canonicalFrontierValues key f words
  have hfrontier := isSigningFrontier_canonical key f words
  have htop : KeyTopHonest f key := keyTopHonest_of_eq f key rfl
  change fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) =
    frontierGame parameter f ftsSecret words frontier adversary
  have hroot := frontierRoot_eq key f words frontier hfrontier
  change frontierRoot parameter f words frontier = root at hroot
  have htopRoot : top (layerHeight topLayer) 0 = root := honestTop_root f parameter (otsSecret topLayer rootTree)
  rw [gameAfterSecrets, fixedBoundaryRun_bind, fixedBoundaryRun_lift_hash]
  have htree : boundaryEval parameter f (keygenTable parameter (otsSecret topLayer rootTree)) =
      (top, (FreeMonoid.of none) ^ keygenHashCost) := by
    exact boundaryEval_keygen parameter f (otsSecret topLayer rootTree)
  rw [htree, pure_bind]
  dsimp only
  rw [htopRoot, fixedBoundaryRun_gameRest_frontier key f words frontier hfrontier htop
    (frontierReferenceWord_canonical key f dummy)]
  rw [frontierGame, hroot]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FrontierOracleCongruence ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierTreeNode referenceEncodingSearch boundaryEval
variable (parameter : PublicParameter) (words : OtsReferenceWords)
  (f g : QueryImpl HashSpec Id) (h : AgreeOutsideOtsPrefixes parameter words f g)
include h
theorem eval_frontierTreeNode_eq_of_agree (lay : Layer) (tree : TreeIndex)
    (frontier : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (frontierTreeNode parameter lay tree (words lay tree) frontier level nodeIdx) =
      evalWithAnswerFn g (frontierTreeNode parameter lay tree (words lay tree) frontier level nodeIdx) := by
  apply eval_frontierTreeNode_congr
  · intro leaf chainIdx step hstep input
    exact congrArg truncateHash (h.chain lay tree leaf chainIdx step hstep (digestBytes input))
  · intro leaf payload
    exact congrArg truncateHash (h.other (.leaf lay tree leaf) (by simp only [hashDomainFields, tweakFields]; decide) payload)
  · intro level nodeIdx payload
    exact congrArg truncateHash (h.other (.node lay tree level nodeIdx) (by simp only [hashDomainFields, tweakFields]; decide) payload)
theorem eval_frontierTreePath_eq_of_agree (lay : Layer) (tree : TreeIndex)
    (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (frontierTreePath parameter lay tree (words lay tree) frontier leaf) =
      evalWithAnswerFn g (frontierTreePath parameter lay tree (words lay tree) frontier leaf) := by
  simp only [frontierTreePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact eval_frontierTreeNode_eq_of_agree parameter words f g h lay tree frontier _ _
  · rfl
theorem eval_ftsNode_eq_of_agree (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest)
    (level nodeIdx : Nat) :
    evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx) =
      evalWithAnswerFn g (ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [ftsNode_zero_eq, ftsLeafHash, eval_tweakableHash]
      exact congrArg truncateHash (h.other (.ftsLeaf index tree _) (by simp only [hashDomainFields, tweakFields]; decide) _)
  | succ level ih =>
      simp only [ftsNode_succ_eq, evalWithAnswerFn_bind, ih, eval_tweakableHash]
      exact congrArg truncateHash (h.other (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx)) (by simp only [hashDomainFields, tweakFields]; decide) _)
theorem eval_ftsKey_eq_of_agree (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsKey parameter index secret) = evalWithAnswerFn g (ftsKey parameter index secret) := by
  simp only [ftsKey]
  exact eval_ftsNode_eq_of_agree parameter words f g h _ _ _ _ _
theorem eval_ftsOpen_eq_of_agree (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsOpen parameter index leaves secret) =
      evalWithAnswerFn g (ftsOpen parameter index leaves secret) := by
  rw [eval_ftsOpen, eval_ftsOpen]
  exact congrArg (honestFts leaves (secret porsTree)) (funext fun level => funext fun nodeIdx =>
    eval_ftsNode_eq_of_agree parameter words f g h _ _ _ _ _)
theorem eval_frontierLayerMessage_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (frontierLayerMessage parameter ftsSecret words frontier index lay) =
      evalWithAnswerFn g (frontierLayerMessage parameter ftsSecret words frontier index lay) := by
  unfold frontierLayerMessage
  split_ifs
  · exact eval_frontierTreeNode_eq_of_agree parameter words f g h _ _ _ _ _
  · exact eval_ftsKey_eq_of_agree parameter words f g h _ _
theorem eval_encode_eq_of_agree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) =
      evalWithAnswerFn g (encodeAttempt parameter lay tree leaf message counter) := by
  simp only [encodeAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_tweakableHash,
    h.other (.encoding lay tree leaf) (by simp only [hashDomainFields, tweakFields]; decide)]
theorem referenceEncodingSearch_eq_of_agree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (attempts start : Nat) :
    referenceEncodingSearch parameter f lay tree leaf message attempts start =
      referenceEncodingSearch parameter g lay tree leaf message attempts start := by
  induction attempts generalizing start with
  | zero => simp only [referenceEncodingSearch]
  | succ attempts ih =>
      simp only [referenceEncodingSearch, eval_encode_eq_of_agree parameter words f g h, ih]
theorem frontierLayerSearch_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay := by
  rw [frontierLayerSearch, frontierLayerSearch,
    eval_frontierLayerMessage_eq_of_agree parameter words f g h,
    referenceEncodingSearch_eq_of_agree parameter words f g h]
theorem frontierSignLayer_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    frontierSignLayer parameter f ftsSecret words frontier index lay =
      frontierSignLayer parameter g ftsSecret words frontier index lay := by
  simp only [frontierSignLayer, frontierLayerSearch_eq_of_agree parameter words f g h,
    eval_frontierTreePath_eq_of_agree parameter words f g h]
theorem frontierSignAfterDigest_eq_of_agree (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves =
      frontierSignAfterDigest parameter g ftsSecret words frontier randomness index leaves := by
  simp only [frontierSignAfterDigest, frontierSignLayer_eq_of_agree parameter words f g h,
    eval_ftsOpen_eq_of_agree parameter words f g h]
theorem frontierRoot_eq_of_agree (frontier : OtsFrontierValues) :
    frontierRoot parameter f words frontier = frontierRoot parameter g words frontier :=
  eval_frontierTreeNode_eq_of_agree parameter words f g h _ _ _ _ _
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_OtsPrefixFrontier ====
section

namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalFrontierValues frontierLayerMessage
def SameChain (segment : OtsPrefix) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) : Prop :=
  lay = segment.lay ∧ tree = segment.tree ∧ leaf = segment.leaf ∧ chainIdx = segment.chainIdx
instance (segment : OtsPrefix) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) :
    Decidable (segment.SameChain lay tree leaf chainIdx) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def replaceChain (segment : OtsPrefix) (values : OtsFrontierValues) (value : Digest) : OtsFrontierValues :=
  fun lay tree leaf chainIdx => if segment.SameChain lay tree leaf chainIdx then value else values lay tree leaf chainIdx
theorem parse_other_chain (segment : OtsPrefix) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (hother : ¬segment.SameChain lay tree leaf chainIdx) (step : ChainStep) (value : Digest) :
    segment.parse (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) = none := by
  cases hparse : segment.parse (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) with
  | none => rfl
  | some query =>
      have hinput := (segment.parse_some_iff _ query).mp hparse
      have hparts := tweakableHashInput_injective segment.parameter (by trivial) (by trivial) hinput
      have hchains : lay = segment.lay ∧ tree = segment.tree ∧ leaf = segment.leaf ∧ chainIdx = segment.chainIdx ∧
          step = segment.step query.1 := by
        simpa only [input, HashDomain.chain.injEq] using hparts.1
      exact False.elim (hother ⟨hchains.1, hchains.2.1, hchains.2.2.1, hchains.2.2.2.1⟩)
theorem answer_other_chain (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (hother : ¬segment.SameChain lay tree leaf chainIdx) (step : ChainStep) (value : Digest) :
    segment.answer tables high outside (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) =
      outside (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) := by
  simp only [answer, segment.parse_other_chain lay tree leaf chainIdx hother step value]
theorem lows_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    segment.lows (segment.answer tables high outside) = tables := by
  funext level value
  rw [lows, answer_input, truncate_combine]
noncomputable def frontierFromEndpoint (segment : OtsPrefix) (outside : QueryImpl HashSpec Id)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint : Digest) : OtsFrontierValues :=
  segment.replaceChain (fun lay tree leaf chainIdx => evalWithAnswerFn outside
    (chainWalk segment.parameter lay tree leaf chainIdx 0 (words lay tree leaf chainIdx).val
      (secrets lay tree leaf chainIdx))) endpoint
theorem frontierFromEndpoint_replaceSecret (segment : OtsPrefix) (outside : QueryImpl HashSpec Id)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.frontierFromEndpoint outside (segment.replaceChain secrets replacement) words endpoint =
      segment.frontierFromEndpoint outside secrets words endpoint := by
  funext lay tree leaf chainIdx
  by_cases h : segment.SameChain lay tree leaf chainIdx <;>
    simp only [frontierFromEndpoint, replaceChain, h, ↓reduceIte]
theorem canonicalFrontierValues_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (root : Digest) (top : Nat → Nat → Digest)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit) :
    canonicalFrontierValues ⟨segment.parameter, root, secrets, ftsSecret, top⟩ (segment.answer tables high outside) words =
      segment.frontierFromEndpoint outside secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  funext lay tree leaf chainIdx
  rw [canonicalFrontierValues, frontierFromEndpoint, replaceChain]
  by_cases h : segment.SameChain lay tree leaf chainIdx
  · rw [if_pos h]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rw [hword, ← segment.evaluate_lows, segment.lows_answer]
  · rw [if_neg h]
    apply eval_chainWalk_congr_tail
    · have hdigit := (words lay tree leaf chainIdx).isLt
      simp only [chainLength, winternitzBits] at hdigit ⊢
      omega
    · intro step _ value
      exact congrArg truncateHash (segment.answer_other_chain tables high outside lay tree leaf chainIdx h step value)
theorem graphMessage_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (root : Digest) (top : Nat → Nat → Digest)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (position : EncodingPosition) :
    canonicalGraphMessage (canonicalGraphLabels segment.parameter secrets ftsSecret (segment.answer tables high outside)) position =
      evalWithAnswerFn outside (frontierLayerMessage segment.parameter ftsSecret words
        (segment.frontierFromEndpoint outside secrets words
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)))
        (referenceIndex position.lay position.tree position.leafIdx) position.lay) := by
  let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret, top⟩
  have hfrontier : IsSigningFrontier key (segment.answer tables high outside) words
      (segment.frontierFromEndpoint outside secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx))) := by
    rw [← segment.canonicalFrontierValues_answer tables high outside root top secrets ftsSecret words hword]
    exact isSigningFrontier_canonical key _ words
  rw [canonicalGraphMessage_eq key, ← eval_frontierLayerMessage key _ words _ hfrontier]
  exact eval_frontierLayerMessage_eq_of_agree segment.parameter words _ outside
    (segment.answer_agrees_outside words (by rw [hword]) tables high outside) ftsSecret _ _ _
end SphincsSecurity.Concrete.OtsPrefix
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FrontierSigningOracleCongruence ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval publicDigestLoop
theorem fixedBoundaryRun_bind_congr {α β : Type} (parameter : PublicParameter)
    (f g : QueryImpl HashSpec Id) (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (hfirst : fixedBoundaryRun parameter f first = fixedBoundaryRun parameter g first)
    (hnext : ∀ value, fixedBoundaryRun parameter f (next value) = fixedBoundaryRun parameter g (next value)) :
    fixedBoundaryRun parameter f (first >>= next) = fixedBoundaryRun parameter g (first >>= next) := by
  simp only [fixedBoundaryRun_bind, hfirst, hnext]
theorem fixedBoundaryRun_lift_prob_eq {α : Type} (parameter : PublicParameter)
    (f g : QueryImpl HashSpec Id) (computation : ProbComp α) :
    fixedBoundaryRun parameter f (liftM computation) = fixedBoundaryRun parameter g (liftM computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, fixedBoundaryRun_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      apply fixedBoundaryRun_bind_congr
      · change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
            (liftM (OracleWorld.query (.inl input)))).run =
          (simulateQ ((fixedHashWorld g).withTrace (signingBoundaryTrace parameter))
            (liftM (OracleWorld.query (.inl input)))).run
        rw [simulateQ_spec_query, simulateQ_spec_query]
        rfl
      · exact ih
variable (parameter : PublicParameter) (words : OtsReferenceWords)
  (f g : QueryImpl HashSpec Id) (h : AgreeOutsideOtsPrefixes parameter words f g)
include h
theorem boundaryEval_publicSignAttempt_eq_of_agree (root : Digest) (message : Message) (randomness : Randomness) :
    boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
      boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
  have hinput := h.other .message (by decide) (messageDigestPayload root message randomness)
  simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hinput]
theorem fixedBoundaryRun_publicDigestLoop_eq_of_agree (root : Digest) (message : Message) (attempts : Nat) :
    fixedBoundaryRun parameter f (publicDigestLoop parameter root message attempts) =
      fixedBoundaryRun parameter g (publicDigestLoop parameter root message attempts) := by
  induction attempts with
  | zero => simp only [publicDigestLoop, fixedBoundaryRun_pure]
  | succ attempts ih =>
      rw [publicDigestLoop]
      apply fixedBoundaryRun_bind_congr
      · exact fixedBoundaryRun_lift_prob_eq parameter f g sampleRandomness
      · intro randomness
        apply fixedBoundaryRun_bind_congr
        · rw [fixedBoundaryRun_lift_hash, fixedBoundaryRun_lift_hash,
            boundaryEval_publicSignAttempt_eq_of_agree parameter words f g h]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl
theorem frontierSigningRecord_eq_of_agree (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (message : Message) :
    frontierSigningRecord parameter root f ftsSecret words frontier message =
      frontierSigningRecord parameter root g ftsSecret words frontier message := by
  simp only [frontierSigningRecord, fixedBoundaryRun_publicDigestLoop_eq_of_agree parameter words f g h,
    frontierSignAfterDigest_eq_of_agree parameter words f g h]
theorem frontierSigningRun_eq_of_agree (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (message : Message) :
    frontierSigningRun parameter root f ftsSecret words frontier message =
      frontierSigningRun parameter root g ftsSecret words frontier message := by
  rw [frontierSigningRun, frontierSigningRun, frontierSigningRecord_eq_of_agree parameter words f g h]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Reference_CausalFrontierGame ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval
noncomputable def causalFrontierAdversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp)
  | .inl input => (fixedHashWorld external).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk
      (frontierSigningRun parameter root (maskOtsPrefixes parameter words external) ftsSecret words frontier message)
theorem causalFrontierAdversaryImpl_eq (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    causalFrontierAdversaryImpl parameter root f ftsSecret words frontier =
      frontierAdversaryImpl parameter root f ftsSecret words frontier := by
  funext input
  cases input with
  | inl input => rfl
  | inr message =>
      change (WriterT.mk
        (frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier message) :
          WriterT SigningBoundaryTrace ProbComp (Option Signature)) =
        WriterT.mk (frontierSigningRun parameter root f ftsSecret words frontier message)
      rw [← frontierSigningRun_eq_of_agree parameter words f (maskOtsPrefixes parameter words f)
        (maskOtsPrefixes_agrees parameter words f)]
noncomputable def causalFrontierAdversaryRun {α : Type} (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp ((α × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  ((simulateQ ((causalFrontierAdversaryImpl parameter root external ftsSecret words frontier).withTraceAppend signingLogFragment)
    computation).run).run
theorem causalFrontierAdversaryRun_eq {α : Type} (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    causalFrontierAdversaryRun parameter root f ftsSecret words frontier computation =
      frontierAdversaryRun parameter root f ftsSecret words frontier computation := by
  rw [causalFrontierAdversaryRun, frontierAdversaryRun, causalFrontierAdversaryImpl_eq]
noncomputable def causalFrontierGameRest (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let result ← causalFrontierAdversaryRun parameter root external ftsSecret words frontier
    (adversary.main ⟨root, parameter⟩)
  let checked := boundaryEval parameter external (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature)
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)
theorem causalFrontierGameRest_eq (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    causalFrontierGameRest parameter root f ftsSecret words frontier adversary =
      frontierGameRest parameter root f ftsSecret words frontier adversary := by
  rw [causalFrontierGameRest, frontierGameRest, causalFrontierAdversaryRun_eq]
noncomputable def causalFrontierGame (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ keygenHashCost * result.2)) <$>
    causalFrontierGameRest parameter (frontierRoot parameter (maskOtsPrefixes parameter words external) words frontier)
      external ftsSecret words frontier adversary
theorem causalFrontierGame_eq (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    causalFrontierGame parameter f ftsSecret words frontier adversary =
      frontierGame parameter f ftsSecret words frontier adversary := by
  rw [causalFrontierGame, frontierGame, causalFrontierGameRest_eq,
    ← frontierRoot_eq_of_agree parameter words f (maskOtsPrefixes parameter words f)
      (maskOtsPrefixes_agrees parameter words f)]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_OtsPrefixSimulation ====
section

namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot
abbrev World (segment : OtsPrefix) := unifSpec + PartialChainEndpoint.PrefixSpec segment.digit.val Digest
noncomputable def fixedImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest) :
    QueryImpl segment.World ProbComp :=
  QueryImpl.id' unifSpec + (fun (query : segment.Query) => pure (tables query.1 query.2) :
    QueryImpl (PartialChainEndpoint.PrefixSpec segment.digit.val Digest) ProbComp)
noncomputable def hashImpl (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) : QueryImpl HashSpec (OracleComp segment.World) :=
  fun bytes => match segment.parse bytes with
    | none => pure (outside bytes)
    | some query => (combine · (high query)) <$> liftM (segment.World.query (.inr query))
noncomputable def worldImpl (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld (OracleComp segment.World)
  | .inl input => liftM (segment.World.query (.inl input))
  | .inr bytes => segment.hashImpl high outside bytes
theorem hashImpl_queryBound (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    (segment.hashImpl high outside bytes).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 1 := by
  cases hparse : segment.parse bytes with
  | none => simp only [hashImpl, hparse, isQueryBoundP_pure]
  | some query =>
      simp only [hashImpl, hparse, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => Nat.zero_lt_one
theorem lift_prob_queryBound (segment : OtsPrefix) {Result : Type} (computation : ProbComp Result) :
    (liftM computation : OracleComp segment.World Result).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change ((liftM (segment.World.query (.inl input)) >>= fun answer => liftM (next answer)) :
        OracleComp segment.World Result).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 0
      simp only [isQueryBoundP_query_bind_iff, PartialChainEndpoint.IsPrefixQuery, not_false_eq_true,
        true_or, ↓reduceIte, true_and]
      exact ih
theorem fixedImpl_lift_prob (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Result : Type} (computation : ProbComp Result) :
    simulateQ (segment.fixedImpl tables) (liftM computation) = computation := by
  rw [fixedImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_id']
private theorem fixedImpl_lift_prob_congr (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Parameter Result : Type} (work : Parameter → ProbComp Result) (first second : Parameter) (h : first = second) :
    simulateQ (segment.fixedImpl tables) (liftM (work first)) = work second :=
  (segment.fixedImpl_lift_prob tables (work first)).trans (congrArg work h)
theorem fixedImpl_hashImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    simulateQ (segment.fixedImpl tables) (segment.hashImpl high outside bytes) =
      pure (segment.answer tables high outside bytes) := by
  cases hparse : segment.parse bytes with
  | none => simp only [hashImpl, answer, hparse, simulateQ_pure]
  | some query =>
      simp only [hashImpl, answer, hparse, simulateQ_map, simulateQ_spec_query]
      rfl
theorem fixedImpl_worldImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    simulateQ (segment.fixedImpl tables) (segment.worldImpl high outside input) =
      fixedHashWorld (segment.answer tables high outside) input := by
  cases input with
  | inl input => rw [worldImpl, simulateQ_spec_query]; rfl
  | inr bytes => exact segment.fixedImpl_hashImpl tables high outside bytes
noncomputable def boundary (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) {Result : Type} (computation : OracleComp OracleWorld Result) :
    OracleComp segment.World (Result × SigningBoundaryTrace) :=
  (simulateQ ((segment.worldImpl high outside).withTrace (signingBoundaryTrace segment.parameter)) computation).run
theorem fixedImpl_boundary (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) {Result : Type}
    (computation : OracleComp OracleWorld Result) :
    simulateQ (segment.fixedImpl tables) (segment.boundary high outside computation) =
      fixedBoundaryRun segment.parameter (segment.answer tables high outside) computation := by
  apply simulateQ_writer_compose
  intro input
  simp [QueryImpl.withTrace_apply, segment.fixedImpl_worldImpl tables high outside input]
noncomputable def adversaryImpl (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace (OracleComp segment.World))
  | .inl input => (segment.worldImpl high outside).withTrace (signingBoundaryTrace segment.parameter) input
  | .inr message => WriterT.mk (liftM
      (frontierSigningRun segment.parameter root (maskOtsPrefixes segment.parameter words outside)
        ftsSecret words frontier message))
theorem adversaryImpl_signing (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (message : Message) :
    segment.adversaryImpl root high outside ftsSecret words frontier (.inr message) =
      WriterT.mk (liftM (frontierSigningRun segment.parameter root (maskOtsPrefixes segment.parameter words outside)
        ftsSecret words frontier message) : OracleComp segment.World _) := rfl
private theorem causalFrontierAdversaryImpl_signing (parameter : PublicParameter) (root : Digest)
    (oracle : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (message : Message) :
    causalFrontierAdversaryImpl parameter root oracle ftsSecret words frontier (.inr message) =
      WriterT.mk (frontierSigningRun parameter root (maskOtsPrefixes parameter words oracle) ftsSecret words frontier message) := rfl
theorem fixedImpl_adversaryImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (root : Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ (segment.fixedImpl tables)
        (segment.adversaryImpl root high outside ftsSecret words frontier input).run =
      (causalFrontierAdversaryImpl segment.parameter root (segment.answer tables high outside)
        ftsSecret words frontier input).run := by
  cases input with
  | inl input =>
      simp [adversaryImpl, causalFrontierAdversaryImpl, QueryImpl.withTrace_apply,
        segment.fixedImpl_worldImpl tables high outside input]
  | inr message =>
      rw [adversaryImpl_signing, causalFrontierAdversaryImpl_signing, WriterT.run_mk, WriterT.run_mk]
      exact fixedImpl_lift_prob_congr segment tables
        (fun oracle => frontierSigningRun segment.parameter root oracle ftsSecret words frontier message) _ _
        (segment.mask_answer words hword tables high outside).symm
noncomputable def logged {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp (OracleWorld + SigningSpec) (Result × QueryLog SigningSpec) :=
  (simulateQ ((QueryImpl.id' (OracleWorld + SigningSpec)).withTraceAppend signingLogFragment) computation).run
noncomputable def adversaryRun (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp segment.World ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  (simulateQ (segment.adversaryImpl root high outside ftsSecret words frontier) (logged computation)).run
theorem fixedImpl_adversaryRun (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (root : Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (segment.fixedImpl tables) (segment.adversaryRun root high outside ftsSecret words frontier computation) =
      causalFrontierAdversaryRun segment.parameter root (segment.answer tables high outside)
        ftsSecret words frontier computation := by
  rw [adversaryRun, simulateQ_writer_compose _ _ _
    (segment.fixedImpl_adversaryImpl tables root high outside ftsSecret words hword frontier)]
  unfold logged causalFrontierAdversaryRun
  congr 1
  apply simulateQ_writerAppend_compose
  intro input
  simp [QueryImpl.withTraceAppend_apply]
noncomputable def gameRest (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    OracleComp segment.World (Bool × SigningBoundaryTrace) := do
  let result ← segment.adversaryRun root high outside ftsSecret words frontier (adversary.main ⟨root, segment.parameter⟩)
  let checked ← segment.boundary high outside (liftM
    (verify ⟨root, segment.parameter⟩ result.1.1.message result.1.1.signature : OracleComp HashSpec Bool))
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)
theorem fixedImpl_gameRest (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (root : Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl tables) (segment.gameRest root high outside ftsSecret words frontier adversary) =
      causalFrontierGameRest segment.parameter root (segment.answer tables high outside)
        ftsSecret words frontier adversary := by
  simp only [gameRest, simulateQ_bind, segment.fixedImpl_adversaryRun tables root high outside ftsSecret words hword frontier]
  unfold causalFrontierGameRest
  apply bind_congr
  intro result
  rw [fixedImpl_boundary, fixedBoundaryRun_lift_hash, pure_bind, simulateQ_pure]
noncomputable def game (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : OracleComp segment.World (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ keygenHashCost * result.2)) <$>
    segment.gameRest (frontierRoot segment.parameter (maskOtsPrefixes segment.parameter words outside) words frontier)
      high outside ftsSecret words frontier adversary
theorem fixedImpl_game (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl tables) (segment.game high outside ftsSecret words frontier adversary) =
      frontierGame segment.parameter (segment.answer tables high outside) ftsSecret words frontier adversary := by
  rw [game, simulateQ_map, fixedImpl_gameRest segment tables _ high outside ftsSecret words hword frontier,
    ← causalFrontierGame_eq, causalFrontierGame, segment.mask_answer words hword tables high outside]
theorem fixedImpl_game_original (segment : OtsPrefix) (oracle : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl (segment.lows oracle))
        (segment.game (segment.highs oracle) oracle ftsSecret words frontier adversary) =
      frontierGame segment.parameter oracle ftsSecret words frontier adversary := by
  rw [fixedImpl_game segment _ _ _ ftsSecret words hword frontier adversary, answer_original]
end SphincsSecurity.Concrete.OtsPrefix
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_CanonicalGraphSampling ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_1 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)
noncomputable local instance instSampleableTypeCanonicalGraphLabels : SampleableType CanonicalGraphLabels :=
  SampleableType.ofFintype CanonicalGraphLabels
noncomputable def canonicalPayloadInputs : Finset HashInput :=
  (Finset.range (numChains + 1)).biUnion fun length =>
    (Finset.univ : Finset (Fin length → Digest)).image (fun values => (List.ofFn values).flatMap digestBytes)
attribute [local irreducible] canonicalPayloadInputs
theorem flatMap_mem_canonicalPayloadInputs (values : List Digest) (hvalues : values.length ≤ numChains) :
    values.flatMap digestBytes ∈ canonicalPayloadInputs := by
  classical
  rw [canonicalPayloadInputs, Finset.mem_biUnion]
  refine ⟨values.length, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr ⟨values.get, Finset.mem_univ _, by rw [List.ofFn_get]⟩
noncomputable def canonicalGraphInputs (parameter : PublicParameter) : Finset HashInput :=
  Finset.univ.biUnion fun position : Position =>
    canonicalPayloadInputs.image (tweakableHashInput parameter position.domain)
attribute [local irreducible] canonicalGraphInputs
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
theorem canonicalGraphSlots_length_le (labels : CanonicalGraphLabels) (position : Position) :
    (canonicalGraphSlots otsSecret ftsSecret labels position).length ≤ numChains := by
  have h := Position.children_length_le position
  cases position <;> simp only [canonicalGraphSlots] <;>
    (try split_ifs) <;> simp only [List.length_map, List.length_singleton] <;>
    first | exact h | decide
theorem canonicalGraphInput_mem (position : Position) (labels : CanonicalGraphLabels) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels ∈ canonicalGraphInputs parameter := by
  classical
  rw [canonicalGraphInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨position, ?_⟩
  exact Finset.mem_image.mpr ⟨(canonicalGraphSlots otsSecret ftsSecret labels position).flatMap digestBytes,
    flatMap_mem_canonicalPayloadInputs _
    (canonicalGraphSlots_length_le otsSecret ftsSecret labels position), rfl⟩
noncomputable def canonicalGraphCell (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs)
    (position : Position) (labels : CanonicalGraphLabels) : inputs :=
  ⟨canonicalGraphInput parameter otsSecret ftsSecret position labels,
    hinputs (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)⟩
theorem canonicalGraphCell_separated (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) :
    FiniteGraphSampling.Separated (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs) := by
  intro left right hne before after heq
  exact canonicalGraphInput_separated parameter otsSecret ftsSecret left right hne before after
    (congrArg Subtype.val heq)
theorem read_canonicalGraphCell (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) (table : inputs → HashOutput)
    (positions : List Position) (labels : CanonicalGraphLabels) :
    FiniteGraphSampling.read (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
      (fun position output values => Function.update values position output) table positions labels =
      readCanonicalGraph parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table) positions labels := by
  induction positions generalizing labels with
  | nil => rfl
  | cons position positions ih =>
      have hrow := hinputs (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)
      have hanswer := finiteHashAnswer_none ∅ inputs table
        (canonicalGraphInput parameter otsSecret ftsSecret position labels) hrow (by simp)
      change FiniteGraphSampling.read _ _ table positions (Function.update labels position
        (table (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs position labels))) =
          readCanonicalGraph parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table) positions
            (Function.update labels position
              (finiteHashAnswer ∅ inputs table (canonicalGraphInput parameter otsSecret ftsSecret position labels)))
      rw [ih, hanswer]
      rfl
noncomputable def plantCanonicalGraph (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) : ProbComp (CanonicalGraphLabels × (inputs → HashOutput)) :=
  FiniteGraphSampling.plant (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
    (fun position output values => Function.update values position output) canonicalGraphOrder (fun _ => 0)
theorem evalDist_canonicalGraph_eq_plant (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs) :
    𝒮[do
      let table ← sampleHashTable inputs
      pure (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table), table)] =
      𝒮[plantCanonicalGraph parameter otsSecret ftsSecret inputs hinputs] := by
  have h := FiniteGraphSampling.evalDist_read_eq_plant
    (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
    (fun position output values => Function.update values position output)
    (canonicalGraphCell_separated parameter otsSecret ftsSecret inputs hinputs)
    canonicalGraphOrder canonicalGraphOrder_nodup (fun _ => 0)
  simpa only [read_canonicalGraphCell, canonicalGraphLabels, plantCanonicalGraph, sampleHashTable] using h
theorem evalDist_canonicalGraph_bind_eq_plant {Result : Type} (inputs : Finset HashInput)
    (hinputs : canonicalGraphInputs parameter ⊆ inputs)
    (next : CanonicalGraphLabels → (inputs → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← sampleHashTable inputs
      next (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table)) table] =
      𝒮[do let result ← plantCanonicalGraph parameter otsSecret ftsSecret inputs hinputs; next result.1 result.2] := by
  have h := congrArg (fun distribution : SPMF (CanonicalGraphLabels × (inputs → HashOutput)) =>
    distribution >>= fun result => 𝒮[next result.1 result.2])
    (evalDist_canonicalGraph_eq_plant parameter otsSecret ftsSecret inputs hinputs)
  simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_EncodingOracleSplit ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false
noncomputable def encodingInputCell (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (input : canonicalEncodingInputs parameter) : inputs :=
  Set.inclusion hencoding input
theorem encodingInputCell_injective (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) : Function.Injective (encodingInputCell parameter inputs hencoding) := by
  exact Set.inclusion_injective hencoding
abbrev NonencodingRows (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :=
  UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) → HashOutput
noncomputable def joinEncodingTable (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (encoding : canonicalEncodingInputs parameter → HashOutput)
    (outside : NonencodingRows parameter inputs hencoding) : inputs → HashOutput :=
  UniformTableSplit.join (encodingInputCell parameter inputs hencoding)
    (encodingInputCell_injective parameter inputs hencoding) encoding outside
noncomputable def nonencodingAnswer (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl HashSpec Id := finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding (fun _ => 0) outside)
theorem canonicalGraphInput_not_encodingInputs (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (position : Position) (labels : CanonicalGraphLabels) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels ∉ canonicalEncodingInputs parameter := by
  intro h
  rw [canonicalEncodingInputs] at h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at h
  obtain ⟨encodingPosition, pair, heq⟩ := h
  have hencoding : AtEncodingPosition parameter (canonicalGraphInput parameter otsSecret ftsSecret position labels)
      encodingPosition := ⟨_, heq.symm⟩
  exact hencoding.not_atPosition position ⟨_, rfl⟩
theorem canonicalGraphCell_not_encodingRange (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (position : Position) (labels : CanonicalGraphLabels) :
    canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position labels ∉
      Set.range (encodingInputCell parameter inputs hencoding) := by
  exact UniformTableSplit.inclusion_not_range hencoding
    (canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position labels)
    (canonicalGraphInput_not_encodingInputs parameter otsSecret ftsSecret position labels)
theorem canonicalGraphLabels_joinEncodingTable (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (outside : NonencodingRows parameter inputs hencoding) :
    canonicalGraphLabels parameter otsSecret ftsSecret
        (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside)) =
      canonicalGraphLabels parameter otsSecret ftsSecret (nonencodingAnswer parameter inputs hencoding outside) := by
  apply FiniteGraphSampling.read_congr
  intro position labels
  have hrow := hgraph (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)
  rw [finiteHashAnswer_none ∅ inputs _ _ hrow (by simp), nonencodingAnswer,
    finiteHashAnswer_none ∅ inputs _ _ hrow (by simp)]
  let cell : UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) :=
    ⟨canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position labels,
      canonicalGraphCell_not_encodingRange parameter otsSecret ftsSecret inputs hencoding hgraph position labels⟩
  exact (UniformTableSplit.join_outside _ _ encoding outside cell).trans
    (UniformTableSplit.join_outside _ _ (fun _ => 0) outside cell).symm
noncomputable def referenceCounterCell (parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (counter : Fin encodingAttemptLimit) : canonicalEncodingInputs parameter :=
  ⟨encodingRetryInput parameter position message counter.val,
    encodingRetryInput_mem_canonicalEncodingInputs parameter position message counter⟩
theorem referenceCounterCell_injective (parameter : PublicParameter) (position : EncodingPosition) (message : Digest) :
    Function.Injective (referenceCounterCell parameter position message) := by
  intro left right heq
  exact Fin.ext (encodingRetryInput_injective_of_lt left.isLt right.isLt (congrArg Subtype.val heq))
noncomputable def outsideGraphMessage (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (position : EncodingPosition) : Digest :=
  canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) position
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_ReferenceFamilyConditioning ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false
abbrev ReferenceSelection := Option (Fin encodingAttemptLimit × Encoding)
noncomputable def referenceTableSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) : ReferenceSelection :=
  FirstSuccessTable.select decodeEncodingOutput (fun counter =>
    readCanonicalEncodingRows key.parameter (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      f (position, counter))
def referenceSelectionResult (selection : ReferenceSelection) : Option (Counter × Encoding) × Nat :=
  (selection.map (fun result => (BitVec.ofNat counterBits result.1.val, result.2)),
    selection.elim encodingAttemptLimit (fun result => result.1.val + 1))
theorem referenceSelectionResult_eq_search (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    referenceSelectionResult (referenceTableSelection key f position) =
      canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  rw [← congrFun (canonicalEncodingResults_eq key f) position]
  simp only [canonicalEncodingResults, referenceSelectionResult, referenceTableSelection, encodingTableResult, Nat.zero_add]
theorem referenceTableSelection_joinEncodingTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput) (outside : NonencodingRows key.parameter inputs hencoding)
    (position : EncodingPosition) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      position = FirstSuccessTable.select decodeEncodingOutput
        (encoding ∘ referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) := by
  rw [referenceTableSelection, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  apply congrArg (FirstSuccessTable.select decodeEncodingOutput)
  funext counter
  change finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    (encodingRetryInput key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter.val) = _
  rw [finiteHashAnswer_none ∅ inputs _ _
    (hencoding (encodingRetryInput_mem_canonicalEncodingInputs _ _ _ counter)) (by simp)]
  exact UniformTableSplit.join_embed _ _ encoding outside
    (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter)
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_3 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false
namespace UniformTableSplit
theorem uniform_bind_firstSuccessFamily {Index Cell Answer Value Result : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Cell] [DecidableEq Cell]
    [Fintype Answer] [DecidableEq Answer] [Nonempty Answer] [Fintype Value] {n : Nat}
    (embed : Index × Fin n → Cell) (hinj : Function.Injective embed) (decode : Answer → Option Value)
    (next : (Index → Option (Fin n × Value)) → (Cell → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Cell → Answer)).bind (fun table =>
        next (fun index => FirstSuccessTable.select decode (fun counter => table (embed (index, counter)))) table) =
      (FirstSuccessFamily.selected decode n).bind (fun results =>
        (FirstSuccessFamily.afterSelect decode n results).bind (fun rows =>
          (PMF.uniformOfFintype (Outside embed → Answer)).bind
            (fun outside => next results (join embed hinj (Function.uncurry rows) outside)))) := by
  rw [uniform_bind_split embed hinj]
  simp only [join_embed]
  have huncurry := PMF.uniformOfFintype_map_of_bijective (Equiv.curry Index (Fin n) Answer).symm
    (Equiv.curry Index (Fin n) Answer).symm.bijective
  rw [← huncurry, PMF.bind_map]
  exact FirstSuccessFamily.uniform_bind_eq_selected decode n
    (fun results rows => (PMF.uniformOfFintype (Outside embed → Answer)).bind
      (fun outside => next results (join embed hinj (Function.uncurry rows) outside)))
end UniformTableSplit
abbrev ReferenceFamily := EncodingPosition → ReferenceSelection
noncomputable def referenceFamilyCell (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (row : EncodingRow) : canonicalEncodingInputs parameter :=
  referenceCounterCell parameter row.1 (messages row.1) row.2
theorem referenceFamilyCell_injective (parameter : PublicParameter) (messages : EncodingPosition → Digest) :
    Function.Injective (referenceFamilyCell parameter messages) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ heq
  have hbytes := congrArg Subtype.val heq
  have hposition : left = right := atEncodingPosition_unique
    (show AtEncodingPosition parameter (encodingRetryInput parameter left (messages left) first.val) left from ⟨_, rfl⟩)
    (show AtEncodingPosition parameter (encodingRetryInput parameter left (messages left) first.val) right from ⟨_, hbytes⟩)
  subst right
  exact Prod.ext rfl (referenceCounterCell_injective parameter left (messages left) heq)
noncomputable def referenceFamilyOracleTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (remaining : UniformTableSplit.Outside
      (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput) :
    inputs → HashOutput :=
  joinEncodingTable key.parameter inputs hencoding
    (UniformTableSplit.join
      (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside))
      (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding outside))
      (Function.uncurry rows) remaining) outside
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false
theorem uniform_bind_referenceFamily {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (next : ReferenceFamily → (inputs → HashOutput) → PMF Result) :
    (PMF.uniformOfFintype (inputs → HashOutput)).bind
        (fun table => next (referenceTableSelection key (finiteHashAnswer ∅ inputs table)) table) =
      (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind (fun outside =>
        (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun results =>
          (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit results).bind
            (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside
              (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput)).bind
                (fun remaining => next results (referenceFamilyOracleTable key inputs hencoding outside rows remaining))))) := by
  rw [UniformTableSplit.uniform_bind_split (encodingInputCell key.parameter inputs hencoding)
    (encodingInputCell_injective key.parameter inputs hencoding), PMF.bind_comm]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext outside
  change ((PMF.uniformOfFintype (canonicalEncodingInputs key.parameter → HashOutput)).bind
    (fun encoding => next (fun position => referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) position)
      (joinEncodingTable key.parameter inputs hencoding encoding outside))) = _
  simp only [referenceTableSelection_joinEncodingTable key inputs hencoding hgraph]
  exact UniformTableSplit.uniform_bind_firstSuccessFamily
    (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside))
    (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding outside))
    decodeEncodingOutput
    (fun results encoding => next results (joinEncodingTable key.parameter inputs hencoding encoding outside))
noncomputable def referenceFamilyOracleSample (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) : PMF (ReferenceFamily × (inputs → HashOutput)) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun results =>
    (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind (fun outside =>
      (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit results).bind
        (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside
          (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput)).map
            (fun remaining => (results, referenceFamilyOracleTable key inputs hencoding outside rows remaining)))))
theorem uniform_joint_eq_referenceFamilyOracleSample (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) :
    (PMF.uniformOfFintype (inputs → HashOutput)).map
        (fun table => (referenceTableSelection key (finiteHashAnswer ∅ inputs table), table)) =
      referenceFamilyOracleSample key inputs hencoding := by
  have h := uniform_bind_referenceFamily key inputs hencoding hgraph (fun results table => PMF.pure (results, table))
  rw [PMF.bind_comm] at h
  exact h
theorem referenceFamilyOracleSample_selections (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) :
    result.1 = referenceTableSelection key (finiteHashAnswer ∅ inputs result.2) := by
  rw [← uniform_joint_eq_referenceFamilyOracleSample key inputs hencoding hgraph, PMF.mem_support_map_iff] at hresult
  obtain ⟨table, _, rfl⟩ := hresult
  rfl
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_4 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)
theorem referenceFamilyOracleSample_bind_selected {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (next : ReferenceFamily → (inputs → HashOutput) → ProbComp Result) :
    (𝒮[referenceFamilyOracleSample key inputs hencoding] >>= fun result => 𝒮[next result.1 result.2]) =
      𝒮[do
        let table ← sampleHashTable inputs
        next (referenceTableSelection key (finiteHashAnswer ∅ inputs table)) table] := by
  rw [← uniform_joint_eq_referenceFamilyOracleSample key inputs hencoding hgraph]
  simp only [← PMF.monad_map_eq_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    evalSPMF_bind, evalSPMF_pure, Function.comp_apply, sampleHashTable, evalSPMF_uniformSample]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Ots_ReferenceFamilyGame ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] hashInputs boundaryEval fixedBoundaryRun
theorem simulateQ_fixedHashWorld_lift_prob {α : Type} (f : QueryImpl HashSpec Id) (computation : ProbComp α) :
    simulateQ (fixedHashWorld f) (liftM computation) = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [liftM_bind, simulateQ_bind]
      have hquery : simulateQ (fixedHashWorld f)
          (liftM (liftM (unifSpec.query input) : ProbComp _)) = (liftM (unifSpec.query input) : ProbComp _) := by
        change simulateQ (fixedHashWorld f) (liftM (OracleWorld.query (.inl input))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hquery]
      exact bind_congr ih
noncomputable def boundaryGameCore (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  boundaryComputation parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)
theorem boundaryComputation_fst {α : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld α) :
    Prod.fst <$> boundaryComputation parameter computation = computation := by
  rw [boundaryComputation, QueryImpl.fst_map_run_withTrace, simulateQ_id']
theorem boundaryGameCore_fst (adversary : Adversary) :
    Prod.fst <$> boundaryGameCore adversary = gameCore scheme adversary := by
  rw [gameCore_eq_secrets, boundaryGameCore]
  simp only [map_bind, boundaryComputation_fst]
noncomputable def fixedFrontierGame (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret, honestTop f parameter (otsSecret topLayer rootTree)⟩
  let words := canonicalReferenceWords key f dummy
  frontierGame parameter f ftsSecret words (canonicalFrontierValues key f words) adversary
theorem simulateQ_boundaryGameCore_frontier (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) :
    simulateQ (fixedHashWorld f) (boundaryGameCore adversary) = fixedFrontierGame f dummy adversary := by
  rw [boundaryGameCore, fixedFrontierGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [← fixedBoundaryRun_eq_boundaryComputation, fixedBoundaryRun_gameAfterSecrets_canonical]
noncomputable def frontierOracleGame (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let table ← sampleHashTable inputs
  fixedFrontierGame (finiteHashAnswer ∅ inputs table) dummy adversary
theorem evalDist_boundaryGameCore_frontier (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒮[frontierOracleGame inputs dummy adversary] := by
  rw [evalDist_romRun_eq_finiteHash _ inputs hinputs ∅, frontierOracleGame]
  apply evalSPMF_bind_congr_left
  intro table
  rw [simulateQ_boundaryGameCore_frontier _ dummy adversary]
theorem evalDist_gameCore_frontier (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒮[Prod.fst <$> frontierOracleGame inputs dummy adversary] := by
  rw [← boundaryGameCore_fst, simulateQ_map, StateT.run'_eq, StateT.run_map]
  simp only [← LawfulFunctor.comp_map, Function.comp_def]
  rw [evalSPMF_map]
  have h := congrArg (fun distribution : SPMF (Bool × SigningBoundaryTrace) => Prod.fst <$> distribution)
    (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs)
  simpa only [StateT.run'_eq, evalSPMF_map, ← LawfulFunctor.comp_map, Function.comp_def] using h
theorem boundaryGameCore_hashCalls_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support ((simulateQ romImpl (boundaryGameCore adversary)).run' ∅)) :
    result.2.hashCalls ≤ q := by
  rw [boundaryGameCore, simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hresult⟩ := hresult
  rw [simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨otsSecret, hots, hresult⟩ := hresult
  rw [simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨ftsSecret, hfts, hresult⟩ := hresult
  rw [← boundaryRun_fst_eq_boundaryComputation, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact (hashQueryBound_iff_boundaryRun parameter _ ∅ q).mp
    (hashQueryBound_gameAfterSecrets adversary q hbound hparameter hots hfts) record hrecord
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalEncodingInputs
noncomputable def graphFrontierGameRest (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let key : SecretKey := ⟨parameter, canonicalGraphRoot labels, otsSecret, ftsSecret,
    honestTop f parameter (otsSecret topLayer rootTree)⟩
  let words := canonicalReferenceWords key f dummy
  frontierGame parameter f ftsSecret words (canonicalGraphFrontier otsSecret labels words) adversary
theorem graphFrontierGameRest_canonical (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    graphFrontierGameRest parameter otsSecret ftsSecret
      (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary =
        fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [graphFrontierGameRest, canonicalGraphLabels_root,
    canonicalGraphLabels_frontier parameter otsSecret ftsSecret f _
      (evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)))
      (honestTop f parameter (otsSecret topLayer rootTree)),
    fixedBoundaryRun_gameAfterSecrets_canonical adversary parameter otsSecret ftsSecret f dummy]
noncomputable def fixedGraphGame (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  graphFrontierGameRest parameter otsSecret ftsSecret
    (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary
theorem fixedGraphGame_eq_frontier (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : fixedGraphGame f dummy adversary = fixedFrontierGame f dummy adversary := by
  rw [← simulateQ_boundaryGameCore_frontier f dummy adversary, boundaryGameCore, fixedGraphGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [graphFrontierGameRest_canonical, fixedBoundaryRun_eq_boundaryComputation]
noncomputable def canonicalGraphOracleGame (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let graph ← plantCanonicalGraph parameter otsSecret ftsSecret inputs (hgraph parameter)
  graphFrontierGameRest parameter otsSecret ftsSecret graph.1
    (finiteHashAnswer ∅ inputs graph.2) dummy adversary
theorem evalDist_frontier_eq_canonicalGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒮[frontierOracleGame inputs dummy adversary] =
      𝒮[canonicalGraphOracleGame inputs hgraph dummy adversary] := by
  rw [frontierOracleGame, canonicalGraphOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame]
  rw [evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro parameter
  rw [evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro otsSecret
  rw [evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro ftsSecret
  exact evalDist_canonicalGraph_bind_eq_plant parameter otsSecret ftsSecret inputs (hgraph parameter)
    (fun labels table => graphFrontierGameRest parameter otsSecret ftsSecret labels
      (finiteHashAnswer ∅ inputs table) dummy adversary)
theorem evalDist_boundaryGameCore_canonicalGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒮[canonicalGraphOracleGame inputs hgraph dummy adversary] := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (evalDist_frontier_eq_canonicalGraph inputs hgraph dummy adversary)
noncomputable def canonicalGraphGameInputs (adversary : Adversary) : Finset HashInput :=
  ((hashInputs (boundaryGameCore adversary) ∪ Finset.univ.biUnion canonicalGraphInputs) ∪
    Finset.univ.biUnion canonicalEncodingInputs) ∪
    Finset.univ.biUnion fun code : KeyCode =>
      hashInputs (gameRest scheme adversary ⟨code.key.root, code.key.parameter⟩ code.key)
attribute [local irreducible] canonicalGraphGameInputs
theorem canonicalGraphInputs_subset_gameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalGraphInputs parameter ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨parameter, hinput⟩
theorem hashInputs_subset_canonicalGraphGameInputs (adversary : Adversary) :
    hashInputs (boundaryGameCore adversary) ⊆ canonicalGraphGameInputs adversary := by
  rw [canonicalGraphGameInputs]
  exact Finset.Subset.trans Finset.subset_union_left
    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
theorem canonicalEncodingInputs_subset_gameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalEncodingInputs parameter ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨parameter, hinput⟩
theorem hashInputs_gameRest_subset_canonicalGraphGameInputs (adversary : Adversary) (key : SecretKey) :
    hashInputs (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  refine ⟨keyCode key, Finset.mem_univ _, ?_⟩
  rw [gameRest_keyCode]
  exact hinput
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false
def fixedReferenceDummyWord : Encoding := OtsCode.defaultWord
theorem fixedReferenceDummyWord_valid : OtsCode.Valid fixedReferenceDummyWord := OtsCode.defaultWord_valid
def fixedReferenceDummy : OtsReferenceWords := fun _ _ _ => fixedReferenceDummyWord
def referenceFamilyWords (selections : ReferenceFamily) (dummy : OtsReferenceWords) : OtsReferenceWords :=
  fun lay tree leaf => ((selections ⟨lay, tree, leaf⟩).map Prod.snd).getD (dummy lay tree leaf)
theorem referenceFamilyWords_selected (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) :
    referenceFamilyWords (referenceTableSelection key f) dummy = canonicalReferenceWords key f dummy := by
  funext lay tree leaf
  rw [referenceFamilyWords, canonicalReferenceWords,
    ← referenceSelectionResult_eq_search key f ⟨lay, tree, leaf⟩]
  simp only [referenceSelectionResult, Option.map_map, Function.comp_def]
theorem referenceFamilyOracleSample_words (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) (dummy : OtsReferenceWords) :
    referenceFamilyWords result.1 dummy = canonicalReferenceWords key (finiteHashAnswer ∅ inputs result.2) dummy := by
  rw [referenceFamilyOracleSample_selections key inputs hencoding hgraph result hresult, referenceFamilyWords_selected]
theorem referenceFamilyOracleSample_words_valid (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) :
    ∀ lay tree leaf, OtsCode.Valid (referenceFamilyWords result.1 dummy lay tree leaf) := by
  rw [referenceFamilyOracleSample_words key inputs hencoding hgraph result hresult dummy]
  exact canonicalReferenceWords_valid key (finiteHashAnswer ∅ inputs result.2) dummy hdummy
noncomputable def referenceFamilyFrontierRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) :=
  let words := referenceFamilyWords selections dummy
  causalFrontierGame key.parameter f key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) adversary
theorem referenceFamilyFrontierRest_selected (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceFamilyFrontierRest key f labels (referenceTableSelection key f) dummy adversary =
      graphFrontierGameRest key.parameter key.otsSecret key.ftsSecret labels f dummy adversary := by
  rw [referenceFamilyFrontierRest, referenceFamilyWords_selected, causalFrontierGame_eq, graphFrontierGameRest]
  rfl
noncomputable def referenceFamilyGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒮[referenceFamilyFrontierRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (reference.1, result)
theorem referenceFamilyGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.snd <$> referenceFamilyGame inputs hencoding dummy adversary = 𝒮[frontierOracleGame inputs dummy adversary] := by
  rw [referenceFamilyGame, frontierOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame, map_bind, map_pure, bind_pure]
  rw [evalSPMF_bind_comm, evalSPMF_bind]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  rw [evalSPMF_bind_comm, evalSPMF_bind]
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalSPMF_bind_comm, evalSPMF_bind]
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  rw [referenceFamilyOracleSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩ inputs
    (hencoding parameter) (hgraph parameter) (fun selections table =>
      referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩ (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary)]
  simp only [referenceFamilyFrontierRest_selected]
theorem evalDist_boundaryGameCore_referenceFamily (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referenceFamilyGame inputs hencoding dummy adversary := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (referenceFamilyGame_erased inputs hencoding hgraph dummy adversary).symm
theorem forgeAdvantage_eq_referenceFamily (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true |
        referenceFamilyGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage, probOutput_def,
    evalDist_gameCore_frontier (canonicalGraphGameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)]
  simp only [evalSPMF_map]
  rw [← referenceFamilyGame_erased (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary,
    ← LawfulFunctor.comp_map]
  change Pr[= true | (Prod.fst ∘ Prod.snd) <$>
    referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _
  rw [probOutput_map]
  rfl
theorem referenceFamilyGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  apply boundaryGameCore_hashCalls_le adversary q hbound result.2
  apply (mem_support_iff_of_evalSPMF_eq
    (mx' := Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    (evalDist_boundaryGameCore_referenceFamily (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)) result.2).mpr
  rw [support_map]
  exact ⟨result, hresult, rfl⟩
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Chains_AdaptiveChainErasure ====
section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}
noncomputable def fixedImpl (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State) :
    QueryImpl (auxSpec + PrefixSpec n State) PMF :=
  auxiliary + (fun (query : Fin n × State) => PMF.pure (tables query.1 query.2) : QueryImpl (PrefixSpec n State) PMF)
omit [Fintype State] [Nonempty State] in
theorem observedRun_forget {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (observedRun auxiliary tables computation observed).map Prod.fst = simulateQ (fixedImpl auxiliary tables) computation := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure result =>
      simp only [observedRun_pure, ← PMF.monad_map_eq_map, ← PMF.monad_pure_eq_pure, map_pure, simulateQ_pure]
  | query_bind input next ih =>
      rw [observedRun_query_bind, PMF.map_bind, simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl input =>
          simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.monad_bind_eq_bind, fixedImpl, QueryImpl.add_apply_inl]
          exact congrArg (auxiliary input).bind (funext fun answer => ih answer observed)
      | inr query =>
          simp only [observedImpl, StateT.run_mk, PMF.pure_bind, fixedImpl, QueryImpl.add_apply_inr,
            PMF.monad_bind_eq_bind, PMF.pure_bind]
          exact ih (tables query.1 query.2) (record observed query (tables query.1 query.2))
theorem realRun_empty_forget {Result : Type} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) :
    (realRun auxiliary computation (fun _ _ => none)).map (fun result => result.2.1) =
      (PMF.uniformOfFintype (Fin n → State → State)).bind (fun tables =>
        (PMF.uniformOfFintype State).bind (fun secret =>
          simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables) (computation (evaluate tables secret)))) := by
  simp only [realRun, completeTables_empty, EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def, observedRun_forget]
theorem realRun_empty_result_mem {Result : Type} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (tables : Fin n → State → State) (secret : State) (result : Result)
    (hresult : result ∈ (simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables)
      (computation (evaluate tables secret))).support) :
    result ∈ ((realRun auxiliary computation (fun _ _ => none)).map (fun result => result.2.1)).support := by
  rw [realRun_empty_forget, PMF.mem_support_bind_iff]
  refine ⟨tables, PMF.mem_support_uniformOfFintype tables, ?_⟩
  rw [PMF.mem_support_bind_iff]
  exact ⟨secret, PMF.mem_support_uniformOfFintype secret, hresult⟩
end SphincsSecurity.Concrete.PartialChainEndpoint
end
-- ==== merged from SphincsSecurity_Proof_Ots_OtsPrefixObservedRun ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false
namespace UniformTableSplit
theorem uniform_outside {Index Cell Answer : Type} [Fintype Index] [Fintype Cell] [Fintype Answer]
    [Nonempty Answer] [DecidableEq Index] [DecidableEq Cell]
    (embed : Index → Cell) (hinj : Function.Injective embed) :
    (PMF.uniformOfFintype (Cell → Answer)).map (fun table => fun cell : Outside embed => table cell.val) =
      PMF.uniformOfFintype (Outside embed → Answer) := by
  rw [uniform_join embed hinj, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, join_outside, PMF.bind_const]
  exact PMF.map_id _
end UniformTableSplit
structure ReferenceFamilySeed (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) where
  selections : ReferenceFamily
  nonencoding : NonencodingRows parameter inputs hencoding
  selectedRows : EncodingPosition → Fin encodingAttemptLimit → HashOutput
  encoding : canonicalEncodingInputs parameter → HashOutput
noncomputable def referenceFamilySeedLawAt (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (selections : ReferenceFamily) :
    PMF (ReferenceFamilySeed parameter inputs hencoding) :=
  (PMF.uniformOfFintype (NonencodingRows parameter inputs hencoding)).bind (fun nonencoding =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
      (fun selectedRows => (PMF.uniformOfFintype (canonicalEncodingInputs parameter → HashOutput)).map
        (fun encoding => ⟨selections, nonencoding, selectedRows, encoding⟩)))
noncomputable def referenceFamilySeedLaw (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) : PMF (ReferenceFamilySeed parameter inputs hencoding) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
    (referenceFamilySeedLawAt parameter inputs hencoding)
noncomputable def referenceFamilySeedTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (seed : ReferenceFamilySeed key.parameter inputs hencoding) : inputs → HashOutput :=
  referenceFamilyOracleTable key inputs hencoding seed.nonencoding seed.selectedRows
    (fun cell => seed.encoding cell.val)
theorem referenceFamilyOracleSample_eq_seed (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) :
    referenceFamilyOracleSample key inputs hencoding =
      (referenceFamilySeedLaw key.parameter inputs hencoding).map
        (fun seed => (seed.selections, referenceFamilySeedTable key inputs hencoding seed)) := by
  rw [referenceFamilyOracleSample, referenceFamilySeedLaw, PMF.map_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [referenceFamilySeedLawAt, PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext nonencoding
  rw [PMF.map_bind]
  apply congrArg (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
  funext selectedRows
  rw [← UniformTableSplit.uniform_outside
    (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding nonencoding))
    (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding nonencoding))]
  simp only [PMF.map_comp, Function.comp_def, referenceFamilySeedTable]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalPayloadInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
theorem input_mem_graph (segment : OtsPrefix) (query : segment.Query) :
    segment.input query ∈ canonicalGraphInputs segment.parameter := by
  rw [canonicalGraphInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨[query.2].flatMap digestBytes, flatMap_mem_canonicalPayloadInputs _ (by change 1 ≤ numChains; decide), ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, input, Position.domain]
theorem input_not_encoding (segment : OtsPrefix) (query : segment.Query) :
    segment.input query ∉ canonicalEncodingInputs segment.parameter := by
  intro h
  rw [canonicalEncodingInputs] at h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at h
  obtain ⟨position, pair, heq⟩ := h
  have hencoding : AtEncodingPosition segment.parameter (segment.input query) position := ⟨_, heq.symm⟩
  exact hencoding.not_atPosition
    (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1)) ⟨digestBytes query.2, rfl⟩
noncomputable def nonencodingCell (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (query : segment.Query) :
    UniformTableSplit.Outside (encodingInputCell segment.parameter inputs hencoding) :=
  ⟨⟨segment.input query, hgraph (segment.input_mem_graph query)⟩,
    UniformTableSplit.inclusion_not_range hencoding _ (segment.input_not_encoding query)⟩
theorem nonencodingCell_injective (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :
    Function.Injective (segment.nonencodingCell inputs hencoding hgraph) := by
  intro left right heq
  exact segment.input_injective (congrArg (fun cell => cell.val.val) heq)
noncomputable def splitRows (segment : OtsPrefix) :
    (segment.Query → HashOutput) ≃ (Fin segment.digit.val → Digest → Digest) × (segment.Query → High) where
  toFun rows := (fun level input => truncateHash (rows (level, input)), fun query => (splitHashOutput digestBits (rows query)).2)
  invFun pair query := combine (pair.1 query.1 query.2) (pair.2 query)
  left_inv rows := funext fun query => combine_split (rows query)
  right_inv pair := Prod.ext
    (funext fun level => funext fun input => truncate_combine (pair.1 level input) (pair.2 (level, input)))
    (funext fun query => congrArg Prod.snd (split_combine (pair.1 query.1 query.2) (pair.2 query)))
theorem uniform_rows (segment : OtsPrefix) :
    PMF.uniformOfFintype (segment.Query → HashOutput) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (segment.Query → High)).map (fun high => fun query => combine (tables query.1 query.2) (high query))) := by
  have h := PMF.uniformOfFintype_map_of_bijective segment.splitRows.symm segment.splitRows.symm.bijective
  rw [UniformTableSplit.uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, splitRows, Equiv.coe_fn_symm_mk] using h.symm
abbrev RemainingRows (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :=
  UniformTableSplit.Outside (segment.nonencodingCell inputs hencoding hgraph) → HashOutput
noncomputable def joinNonencoding (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : NonencodingRows segment.parameter inputs hencoding :=
  UniformTableSplit.join (segment.nonencodingCell inputs hencoding hgraph)
    (segment.nonencodingCell_injective inputs hencoding hgraph)
    (fun query => combine (tables query.1 query.2) (high query)) remaining
theorem joinNonencoding_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (query : segment.Query) :
    segment.joinNonencoding inputs hencoding hgraph tables high remaining
        (segment.nonencodingCell inputs hencoding hgraph query) = combine (tables query.1 query.2) (high query) :=
  UniformTableSplit.join_embed _ _ _ _ _
theorem uniform_nonencoding (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :
    PMF.uniformOfFintype (NonencodingRows segment.parameter inputs hencoding) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (segment.Query → High)).bind (fun high =>
          (PMF.uniformOfFintype (segment.RemainingRows inputs hencoding hgraph)).map
            (segment.joinNonencoding inputs hencoding hgraph tables high))) := by
  rw [UniformTableSplit.uniform_join (segment.nonencodingCell inputs hencoding hgraph)
    (segment.nonencodingCell_injective inputs hencoding hgraph), segment.uniform_rows]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
noncomputable def rawAnswer (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  finiteHashAnswer ∅ inputs (joinEncodingTable segment.parameter inputs hencoding encoding
    (segment.joinNonencoding inputs hencoding hgraph tables high remaining))
noncomputable def auxiliaryAnswer (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  segment.rawAnswer inputs hencoding hgraph encoding (fun _ _ => 0) (fun _ => 0) remaining
theorem rawAnswer_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (query : segment.Query) :
    segment.rawAnswer inputs hencoding hgraph encoding tables high remaining (segment.input query) =
      combine (tables query.1 query.2) (high query) := by
  rw [rawAnswer, finiteHashAnswer_none ∅ inputs _ _ (hgraph (segment.input_mem_graph query)) (by simp)]
  exact (UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
    (encodingInputCell_injective segment.parameter inputs hencoding) encoding _
    (segment.nonencodingCell inputs hencoding hgraph query)).trans
    (segment.joinNonencoding_prefix inputs hencoding hgraph tables high remaining query)
theorem rawAnswer_other (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (first second : Fin segment.digit.val → Digest → Digest) (firstHigh secondHigh : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (bytes : HashInput) (hparse : segment.parse bytes = none) :
    segment.rawAnswer inputs hencoding hgraph encoding first firstHigh remaining bytes =
      segment.rawAnswer inputs hencoding hgraph encoding second secondHigh remaining bytes := by
  by_cases hin : bytes ∈ inputs
  · rw [rawAnswer, rawAnswer, finiteHashAnswer_none ∅ inputs _ _ hin (by simp),
      finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    by_cases henc : bytes ∈ canonicalEncodingInputs segment.parameter
    · exact (UniformTableSplit.join_embed (encodingInputCell segment.parameter inputs hencoding)
        (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ ⟨bytes, henc⟩).trans
        (UniformTableSplit.join_embed (encodingInputCell segment.parameter inputs hencoding)
          (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ ⟨bytes, henc⟩).symm
    · let cell : UniformTableSplit.Outside (encodingInputCell segment.parameter inputs hencoding) :=
        ⟨⟨bytes, hin⟩, UniformTableSplit.inclusion_not_range hencoding _ henc⟩
      have hcell : cell ∉ Set.range (segment.nonencodingCell inputs hencoding hgraph) := by
        rintro ⟨query, heq⟩
        have hbytes : segment.input query = bytes := congrArg (fun value => value.val.val) heq
        have hsome := (segment.parse_some_iff bytes query).mpr hbytes.symm
        rw [hparse] at hsome
        cases hsome
      calc
        _ = segment.joinNonencoding inputs hencoding hgraph first firstHigh remaining cell :=
          UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
            (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ cell
        _ = remaining ⟨cell, hcell⟩ :=
          UniformTableSplit.join_outside (segment.nonencodingCell inputs hencoding hgraph)
            (segment.nonencodingCell_injective inputs hencoding hgraph) _ remaining ⟨cell, hcell⟩
        _ = segment.joinNonencoding inputs hencoding hgraph second secondHigh remaining cell :=
          (UniformTableSplit.join_outside (segment.nonencodingCell inputs hencoding hgraph)
            (segment.nonencodingCell_injective inputs hencoding hgraph) _ remaining ⟨cell, hcell⟩).symm
        _ = _ :=
          (UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
            (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ cell).symm
  · simp only [rawAnswer, finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]
theorem rawAnswer_eq (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) :
    segment.rawAnswer inputs hencoding hgraph encoding tables high remaining =
      segment.answer tables high (segment.auxiliaryAnswer inputs hencoding hgraph encoding remaining) := by
  funext bytes
  cases hparse : segment.parse bytes with
  | none =>
      rw [answer, hparse]
      exact segment.rawAnswer_other inputs hencoding hgraph encoding _ _ _ _ remaining bytes hparse
  | some query =>
      rw [(segment.parse_some_iff bytes query).mp hparse, rawAnswer_prefix, answer_input]
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
namespace OtsPrefix
structure ReferenceAuxSeed (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) where
  high : segment.Query → High
  remaining : segment.RemainingRows inputs hencoding hgraph
  selectedRows : EncodingPosition → Fin encodingAttemptLimit → HashOutput
  encoding : canonicalEncodingInputs segment.parameter → HashOutput
noncomputable def referenceAuxSeedLaw (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily) :
    PMF (segment.ReferenceAuxSeed inputs hencoding hgraph) :=
  (PMF.uniformOfFintype (segment.Query → High)).bind (fun high =>
    (PMF.uniformOfFintype (segment.RemainingRows inputs hencoding hgraph)).bind (fun remaining =>
      (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
        (fun selectedRows => (PMF.uniformOfFintype (canonicalEncodingInputs segment.parameter → HashOutput)).map
          (fun encoding => ⟨high, remaining, selectedRows, encoding⟩))))
noncomputable def referenceSeed (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily)
    (tables : Fin segment.digit.val → Digest → Digest) (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) :
    ReferenceFamilySeed segment.parameter inputs hencoding :=
  ⟨selections, segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining,
    auxiliary.selectedRows, auxiliary.encoding⟩
theorem referenceFamilySeedLawAt_eq_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily) :
    referenceFamilySeedLawAt segment.parameter inputs hencoding selections =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).map
          (segment.referenceSeed inputs hencoding hgraph selections tables)) := by
  rw [referenceFamilySeedLawAt, segment.uniform_nonencoding inputs hencoding hgraph]
  simp only [PMF.bind_bind, PMF.bind_map, referenceAuxSeedLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl
end OtsPrefix
theorem referenceFamilyOracleSample_eq_prefixSeed (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : ReferenceFamily → Digit) :
    referenceFamilyOracleSample key inputs hencoding =
      (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
        let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, digit selections⟩
        (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
          (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).map (fun auxiliary =>
            (selections, referenceFamilySeedTable key inputs hencoding
              (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))))) := by
  rw [referenceFamilyOracleSample_eq_seed, referenceFamilySeedLaw, PMF.map_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [OtsPrefix.referenceFamilySeedLawAt_eq_prefix
    ⟨key.parameter, lay, tree, leaf, chainIdx, digit selections⟩ inputs hencoding hgraph selections]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, OtsPrefix.referenceSeed]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
  (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
noncomputable def encodingFromMessages (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (seed : canonicalEncodingInputs parameter → HashOutput) : canonicalEncodingInputs parameter → HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (Function.uncurry rows) (fun cell => seed cell.val)
noncomputable def seedBaseOracle (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  segment.auxiliaryAnswer inputs hencoding hgraph (fun _ => 0) auxiliary.remaining
noncomputable def seedFrontier (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint : Digest) : OtsFrontierValues :=
  segment.frontierFromEndpoint (segment.seedBaseOracle inputs hencoding hgraph auxiliary) secrets words endpoint
noncomputable def seedMessages (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : EncodingPosition → Digest :=
  fun position => evalWithAnswerFn (segment.seedBaseOracle inputs hencoding hgraph auxiliary)
    (frontierLayerMessage segment.parameter ftsSecret words
      (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint)
      (referenceIndex position.lay position.tree position.leafIdx) position.lay)
noncomputable def seedEncoding (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : canonicalEncodingInputs segment.parameter → HashOutput :=
  encodingFromMessages segment.parameter (segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    auxiliary.selectedRows auxiliary.encoding
noncomputable def seedOracle (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : QueryImpl HashSpec Id :=
  segment.auxiliaryAnswer inputs hencoding hgraph
    (segment.seedEncoding inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint) auxiliary.remaining
theorem seedFrontier_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedFrontier inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) words endpoint =
      segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint :=
  segment.frontierFromEndpoint_replaceSecret _ secrets words endpoint replacement
theorem seedMessages_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedMessages inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint =
      segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint := by
  funext position
  simp only [seedMessages, seedFrontier_replaceSecret]
theorem seedOracle_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedOracle inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint =
      segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint := by
  simp only [seedOracle, seedEncoding, seedMessages_replaceSecret]
theorem outsideGraphMessage_eq_seedMessages (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    outsideGraphMessage ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) =
      segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  funext position
  change canonicalGraphMessage (canonicalGraphLabels segment.parameter secrets ftsSecret
    (segment.rawAnswer inputs hencoding hgraph (fun _ => 0) tables auxiliary.high auxiliary.remaining)) position = _
  rw [rawAnswer_eq]
  exact segment.graphMessage_answer tables auxiliary.high _ root top secrets ftsSecret words hword position
theorem referenceSeedTable_eq_raw (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
        (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary) =
      joinEncodingTable segment.parameter inputs hencoding
        (segment.seedEncoding inputs hencoding hgraph auxiliary secrets ftsSecret words
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)))
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) := by
  change joinEncodingTable segment.parameter inputs hencoding
    (encodingFromMessages segment.parameter
      (outsideGraphMessage ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining))
      auxiliary.selectedRows auxiliary.encoding)
    (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) = _
  rw [segment.outsideGraphMessage_eq_seedMessages inputs hencoding hgraph auxiliary root top secrets ftsSecret words hword tables]
  rfl
theorem referenceSeedOracle_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    finiteHashAnswer ∅ inputs
        (referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
          (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary)) =
      segment.answer tables auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx))) := by
  rw [segment.referenceSeedTable_eq_raw inputs hencoding hgraph auxiliary root top secrets ftsSecret selections words hword tables]
  exact segment.rawAnswer_eq inputs hencoding hgraph _ tables auxiliary.high auxiliary.remaining
theorem referenceSeedFrontier_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    canonicalGraphFrontier secrets (canonicalGraphLabels segment.parameter secrets ftsSecret
      (finiteHashAnswer ∅ inputs
        (referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
          (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary)))) words =
      segment.seedFrontier inputs hencoding hgraph auxiliary secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  rw [segment.referenceSeedTable_eq_raw inputs hencoding hgraph auxiliary root top secrets ftsSecret selections words hword tables,
    canonicalGraphLabels_joinEncodingTable segment.parameter secrets ftsSecret inputs hencoding hgraph,
    canonicalGraphLabels_frontier segment.parameter secrets ftsSecret _ words root top]
  change canonicalFrontierValues ⟨segment.parameter, root, secrets, ftsSecret, top⟩
    (segment.rawAnswer inputs hencoding hgraph (fun _ => 0) tables auxiliary.high auxiliary.remaining) words = _
  rw [rawAnswer_eq, segment.canonicalFrontierValues_answer tables auxiliary.high _ root top secrets ftsSecret words hword]
  rfl
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
  (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
noncomputable def seedGame (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) (adversary : Adversary) : OracleComp segment.World (Bool × SigningBoundaryTrace) :=
  segment.game auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) adversary
theorem seedGame_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) (adversary : Adversary) :
    segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint adversary =
      segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [seedGame, seedGame, seedOracle_replaceSecret, seedFrontier_replaceSecret]
theorem referenceSeedGame_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (hword : referenceFamilyWords selections dummy segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) (adversary : Adversary) :
    let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret, top⟩
    let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding
      (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))
    referenceFamilyFrontierRest key oracle (canonicalGraphLabels segment.parameter secrets ftsSecret oracle) selections dummy adversary =
      simulateQ (segment.fixedImpl tables)
        (segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets 0) ftsSecret
          (referenceFamilyWords selections dummy)
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) adversary) := by
  dsimp only
  rw [seedGame_replaceSecret, seedGame,
    segment.fixedImpl_game tables auxiliary.high _ ftsSecret (referenceFamilyWords selections dummy) (by rw [hword])]
  rw [referenceFamilyFrontierRest, causalFrontierGame_eq,
    segment.referenceSeedFrontier_eq inputs hencoding hgraph auxiliary root top secrets ftsSecret selections _ hword tables,
    segment.referenceSeedOracle_eq inputs hencoding hgraph auxiliary root top secrets ftsSecret selections _ hword tables]
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
noncomputable def uniformImpl : QueryImpl unifSpec PMF :=
  fun input => PMF.uniformOfFintype (Fin (input + 1))
theorem fixedImpl_evalDist (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Result : Type} (computation : OracleComp segment.World Result) :
    𝒮[simulateQ (PartialChainEndpoint.fixedImpl uniformImpl tables) computation] =
      𝒮[simulateQ (segment.fixedImpl tables) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih]
      cases input with
      | inl input =>
          simp only [PartialChainEndpoint.fixedImpl, fixedImpl, QueryImpl.add_apply_inl,
            uniformImpl]
          change (𝒮[PMF.uniformOfFintype (Fin (input + 1))] >>= fun answer =>
            𝒮[simulateQ (segment.fixedImpl tables) (next answer)]) =
            (𝒮[(liftM (unifSpec.query input) : ProbComp (Fin (input + 1)))] >>= fun answer =>
              𝒮[simulateQ (segment.fixedImpl tables) (next answer)])
          rw [evalSPMF_query]
      | inr query =>
          simp only [PartialChainEndpoint.fixedImpl, fixedImpl, QueryImpl.add_apply_inr,
            ← PMF.monad_pure_eq_pure, evalSPMF_pure]
theorem realRun_empty_forget (segment : OtsPrefix) {Result : Type}
    (computation : Digest → OracleComp segment.World Result) :
    𝒮[(PartialChainEndpoint.realRun (fun _ => uniformImpl) computation (fun _ _ => none)).map
      (fun result => result.2.1)] = (do
        let tables ← 𝒮[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
        let secret ← 𝒮[PMF.uniformOfFintype Digest]
        𝒮[simulateQ (segment.fixedImpl tables) (computation (PartialChainEndpoint.evaluate tables secret))] : SPMF Result) := by
  rw [PartialChainEndpoint.realRun_empty_forget]
  simp only [← PMF.monad_bind_eq_bind, evalSPMF_bind, segment.fixedImpl_evalDist]
noncomputable def seedObservedRun (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) :
    PMF (Digest × ((Bool × SigningBoundaryTrace) × (Fin segment.digit.val → Digest → Option Digest))) :=
  PartialChainEndpoint.realRun (fun _ => uniformImpl)
    (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
    (fun _ _ => none)
end SphincsSecurity.Concrete.OtsPrefix
end
end
-- ==== merged from SphincsSecurity_Proof_Base_QueryPause ====
section

namespace SphincsSecurity.QueryPause
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (stop : Memory → Prop) [DecidablePred stop]
  (step : (input : spec.Domain) → spec.Range input → Memory → Memory)
noncomputable def run (computation : OracleComp spec Result) : Memory → OracleComp spec (Memory × OracleComp spec Result) :=
  OracleComp.construct (fun result memory => pure (memory, pure result))
    (fun input original next memory =>
      if stop memory then pure (memory, liftM (spec.query input) >>= original)
      else liftM (spec.query input) >>= fun answer => next answer (step input answer memory)) computation
theorem run_pure (result : Result) (memory : Memory) :
    run stop step (pure result : OracleComp spec Result) memory = pure (memory, pure result) := rfl
theorem run_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) (memory : Memory) :
    run stop step (liftM (spec.query input) >>= next) memory =
      if stop memory then pure (memory, liftM (spec.query input) >>= next)
      else liftM (spec.query input) >>= fun answer => run stop step (next answer) (step input answer memory) := rfl
theorem resume (computation : OracleComp spec Result) (memory : Memory) :
    (run stop step computation memory >>= fun paused => paused.2) = computation := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure result => simp only [run_pure, pure_bind]
  | query_bind input next ih =>
      rw [run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, pure_bind]
      · simp only [if_neg hs, bind_assoc, ih]
variable (selected : Index → Prop) [DecidablePred selected]
theorem counted_resume (computation : OracleComp spec Result) (memory : Memory) :
    (do
      let paused ← QueryCap.counted selected (run stop step computation memory)
      let result ← QueryCap.counted selected paused.1.2
      pure (result.1, paused.2 + result.2)) = QueryCap.counted selected computation := by
  rw [← QueryCap.counted_bind, resume]
end SphincsSecurity.QueryPause
end
-- ==== merged from SphincsSecurity_Proof_Reference_CausalFrontierProgram ====
section

namespace SphincsSecurity.Concrete.CausalFrontierProgram
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot
noncomputable def adversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace (OracleComp OracleWorld))
  | .inl input => (QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk (liftM
      (frontierSigningRun parameter root (maskOtsPrefixes parameter words external) ftsSecret words frontier message))
theorem adversaryImpl_signing (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (message : Message) :
    adversaryImpl parameter root external ftsSecret words frontier (.inr message) =
      WriterT.mk (liftM (frontierSigningRun parameter root (maskOtsPrefixes parameter words external)
        ftsSecret words frontier message) : OracleComp OracleWorld _) := rfl
noncomputable def adversaryRun {Result : Type} (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp OracleWorld ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  (simulateQ (adversaryImpl parameter root external ftsSecret words frontier) (OtsPrefix.logged computation)).run
noncomputable def gameRest (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    OracleComp OracleWorld (Bool × SigningBoundaryTrace) := do
  let result ← adversaryRun parameter root external ftsSecret words frontier (adversary.main ⟨root, parameter⟩)
  let checked ← boundaryComputation parameter (liftM
    (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature : OracleComp HashSpec Bool))
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)
noncomputable def game (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ keygenHashCost * result.2)) <$>
    gameRest parameter (frontierRoot parameter (maskOtsPrefixes parameter words external) words frontier)
      external ftsSecret words frontier adversary
theorem worldImpl_lift_prob (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) {Result : Type} (computation : ProbComp Result) :
    simulateQ (segment.worldImpl high outside) (liftM computation) =
      (liftM computation : OracleComp segment.World Result) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      rfl
theorem prefix_boundary (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) {Result : Type} (computation : OracleComp OracleWorld Result) :
    simulateQ (segment.worldImpl high outside) (boundaryComputation segment.parameter computation) =
      segment.boundary high outside computation := by
  apply simulateQ_writer_compose
  intro input
  simp [QueryImpl.withTrace_apply]
theorem prefix_adversaryImpl (segment : OtsPrefix) (root : Digest) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ (segment.worldImpl high outside)
        (adversaryImpl segment.parameter root outside ftsSecret words frontier input).run =
      (segment.adversaryImpl root high outside ftsSecret words frontier input).run := by
  cases input with
  | inl input => simp [adversaryImpl, OtsPrefix.adversaryImpl, QueryImpl.withTrace_apply]
  | inr message =>
      rw [adversaryImpl_signing, OtsPrefix.adversaryImpl_signing, WriterT.run_mk, WriterT.run_mk,
        worldImpl_lift_prob]
theorem prefix_adversaryRun (segment : OtsPrefix) (root : Digest) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (segment.worldImpl high outside)
        (adversaryRun segment.parameter root outside ftsSecret words frontier computation) =
      segment.adversaryRun root high outside ftsSecret words frontier computation :=
  simulateQ_writer_compose _ _ _ (prefix_adversaryImpl segment root high outside ftsSecret words frontier) _
theorem prefix_game (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) :
    simulateQ (segment.worldImpl high outside) (game segment.parameter outside ftsSecret words frontier adversary) =
      segment.game high outside ftsSecret words frontier adversary := by
  simp only [game, simulateQ_map, gameRest, simulateQ_bind, prefix_adversaryRun, prefix_boundary, simulateQ_pure,
    OtsPrefix.game, OtsPrefix.gameRest]
theorem fixed_game (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (fixedHashWorld external) (game parameter external ftsSecret words frontier adversary) =
      frontierGame parameter external ftsSecret words frontier adversary := by
  let chain : ChainIndex := ⟨0, by decide⟩
  let segment : OtsPrefix := ⟨parameter, topLayer, rootTree, 0, chain, words topLayer rootTree 0 chain⟩
  have h := prefix_game segment (segment.highs external) external ftsSecret words frontier adversary
  apply_fun simulateQ (segment.fixedImpl (segment.lows external)) at h
  rw [segment.fixedImpl_game_original external ftsSecret words (by rfl) frontier adversary] at h
  rw [← QueryImpl.simulateQ_compose] at h
  have himpl : (segment.fixedImpl (segment.lows external)).compose
      (segment.worldImpl (segment.highs external) external) = fixedHashWorld external := by
    funext input
    rw [QueryImpl.apply_compose, segment.fixedImpl_worldImpl, segment.answer_original]
  simpa only [himpl] using h
theorem fixed_adversaryRun {Result : Type} (parameter : PublicParameter) (root : Digest) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (fixedHashWorld external) (adversaryRun parameter root external ftsSecret words frontier computation) =
      frontierAdversaryRun parameter root external ftsSecret words frontier computation := by
  let chain : ChainIndex := ⟨0, by decide⟩
  let segment : OtsPrefix := ⟨parameter, topLayer, rootTree, 0, chain, words topLayer rootTree 0 chain⟩
  have h := prefix_adversaryRun segment root (segment.highs external) external ftsSecret words frontier computation
  apply_fun simulateQ (segment.fixedImpl (segment.lows external)) at h
  rw [segment.fixedImpl_adversaryRun _ root _ external ftsSecret words (by rfl) frontier computation,
    segment.answer_original, causalFrontierAdversaryRun_eq] at h
  rw [← QueryImpl.simulateQ_compose] at h
  have himpl : (segment.fixedImpl (segment.lows external)).compose
      (segment.worldImpl (segment.highs external) external) = fixedHashWorld external := by
    funext input
    rw [QueryImpl.apply_compose, segment.fixedImpl_worldImpl, segment.answer_original]
  simpa only [himpl] using h
end SphincsSecurity.Concrete.CausalFrontierProgram
end
-- ==== merged from SphincsSecurity_Proof_Reference_CausalFrontierAllocation ====
section

namespace SphincsSecurity.Concrete.CausalFrontierProgram
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot
def IsHash : OracleWorld.Domain → Prop := (· matches .inr _)
instance : DecidablePred IsHash := fun input => by unfold IsHash; infer_instance
structure TraceCharge (parameter : PublicParameter) where
  selected : OracleWorld.Domain → Prop
  decidable : DecidablePred selected
  cost : SigningBoundaryTrace → Nat
  cost_mul : ∀ first second, cost (first * second) = cost first + cost second
  uniform : ∀ input, ¬selected (.inl input)
  step : ∀ input answer, (if selected input then 1 else 0) ≤ cost (signingBoundaryTrace parameter input answer)
namespace TraceCharge
variable {parameter : PublicParameter} (charge : TraceCharge parameter)
noncomputable instance : DecidablePred charge.selected := charge.decidable
theorem lift_prob_queryBound {Result : Type} (computation : ProbComp Result) :
    (liftM computation : OracleComp OracleWorld Result).IsQueryBoundP charge.selected 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change ((liftM (OracleWorld.query (.inl input)) >>= fun answer => liftM (next answer)) :
        OracleComp OracleWorld Result).IsQueryBoundP charge.selected 0
      simp only [isQueryBoundP_query_bind_iff, charge.uniform, not_false_eq_true, true_or, ↓reduceIte, true_and]
      exact ih
private theorem withTrace_run {Input Trace : Type} {spec : OracleSpec Input} [Monoid Trace]
    (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    ((QueryImpl.id' spec).withTrace trace input).run =
      (fun answer => (answer, trace input answer)) <$> (liftM (spec.query input) : OracleComp spec _) := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]
theorem worldTrace_counted_le (input : OracleWorld.Domain)
    (result : (OracleWorld.Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) input).run)) :
    result.2 ≤ charge.cost result.1.2 := by
  rw [withTrace_run, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  rw [QueryCap.counted_query, support_map] at horiginal
  obtain ⟨answer, _, rfl⟩ := horiginal
  exact charge.step input answer
theorem boundary_counted_le {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : (Result × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected (boundaryComputation parameter computation))) :
    result.2 ≤ charge.cost result.1.2 :=
  QueryCap.counted_writer_simulate_le _ charge.cost charge.cost_mul _
    (worldTrace_counted_le charge) computation result hresult
theorem adversaryImpl_counted_le (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain)
    (result : ((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (adversaryImpl parameter root external ftsSecret words frontier input).run)) : result.2 ≤ charge.cost result.1.2 := by
  cases input with
  | inl input => exact worldTrace_counted_le charge input result hresult
  | inr message =>
      rw [adversaryImpl_signing, WriterT.run_mk] at hresult
      have hzero := QueryCap.counted_le_of_queryBound _ _ 0 (lift_prob_queryBound charge _) result hresult
      exact hzero.trans (Nat.zero_le _)
theorem adversaryRun_counted_le {Result : Type} (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (result : ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (adversaryRun parameter root external ftsSecret words frontier computation))) : result.2 ≤ charge.cost result.1.2 :=
  QueryCap.counted_writer_simulate_le _ charge.cost charge.cost_mul _
    (adversaryImpl_counted_le charge root external ftsSecret words frontier) (OtsPrefix.logged computation) result hresult
theorem gameRest_counted_le (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (gameRest parameter root external ftsSecret words frontier adversary))) : result.2 ≤ charge.cost result.1.2 := by
  simp only [gameRest, QueryCap.counted_bind, QueryCap.counted_pure, bind_assoc, pure_bind, Nat.add_zero] at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨second, hsecond, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  rw [charge.cost_mul]
  exact Nat.add_le_add (adversaryRun_counted_le charge root external ftsSecret words frontier _ first hfirst)
    (boundary_counted_le charge _ second hsecond)
theorem game_counted_le (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (game parameter external ftsSecret words frontier adversary))) : result.2 ≤ charge.cost result.1.2 := by
  rw [game, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  have h := gameRest_counted_le charge _ external ftsSecret words frontier adversary original horiginal
  simp only [charge.cost_mul]
  omega
end TraceCharge
noncomputable def hashTraceCharge (parameter : PublicParameter) : TraceCharge parameter where
  selected := IsHash
  decidable := inferInstance
  cost := SigningBoundaryTrace.hashCalls
  cost_mul := SigningBoundaryTrace.hashCalls_mul
  uniform := by intro input; simp [IsHash]
  step := by
    intro input answer
    cases input <;> simp [IsHash, signingBoundaryTrace_hashCalls_eq]
theorem game_counted_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      (game parameter external ftsSecret words frontier adversary))) : result.2 ≤ result.1.2.hashCalls :=
  TraceCharge.game_counted_le (hashTraceCharge parameter) external ftsSecret words frontier adversary result hresult
end SphincsSecurity.Concrete.CausalFrontierProgram
end
-- ==== merged from SphincsSecurity_Proof_Ots_OtsPrefixAllocation ====
section

namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot
abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev atAddress (parameter : PublicParameter) (words : OtsReferenceWords) (address : ChainAddress) : OtsPrefix :=
  ⟨parameter, address.1, address.2.1, address.2.2.1, address.2.2.2,
    words address.1 address.2.1 address.2.2.1 address.2.2.2⟩
def Selects (segment : OtsPrefix) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => segment.parse input ≠ none
noncomputable instance (segment : OtsPrefix) : DecidablePred segment.Selects := Classical.decPred _
theorem atAddress_selects_unique (parameter : PublicParameter) (words : OtsReferenceWords)
    (left right : ChainAddress) (input : OracleWorld.Domain)
    (hleft : (atAddress parameter words left).Selects input)
    (hright : (atAddress parameter words right).Selects input) : left = right := by
  cases input with
  | inl input => exact False.elim hleft
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hleft
      have hinput := ((atAddress parameter words left).parse_some_iff input query).mp hquery
      by_contra hne
      have hother : ¬(atAddress parameter words right).SameChain left.1 left.2.1 left.2.2.1 left.2.2.2 := by
        intro h
        exact hne (Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2)))
      have hnone := (atAddress parameter words right).parse_other_chain left.1 left.2.1 left.2.2.1 left.2.2.2
        hother ((atAddress parameter words left).step query.1) query.2
      exact hright (hinput ▸ hnone)
theorem allocation_step_le (parameter : PublicParameter) (words : OtsReferenceWords) (addresses : Finset ChainAddress)
    (input : OracleWorld.Domain) :
    (∑ address ∈ addresses, if (atAddress parameter words address).Selects input then 1 else 0) ≤
      if CausalFrontierProgram.IsHash input then 1 else 0 := by
  classical
  cases input with
  | inl input => simp [Selects, CausalFrontierProgram.IsHash]
  | inr input =>
      change (∑ address ∈ addresses, if (atAddress parameter words address).Selects (.inr input) then 1 else 0) ≤ 1
      apply Finset.sum_le_one_iff.mpr
      intro left right _ _ hleft hright
      have hl : (atAddress parameter words left).Selects (.inr input) := by simpa using hleft
      have hr : (atAddress parameter words right).Selects (.inr input) := by simpa using hright
      exact ⟨atAddress_selects_unique parameter words left right _ hl hr, if_pos hl⟩
theorem allocation_le (parameter : PublicParameter) (words : OtsReferenceWords) (addresses : Finset ChainAddress)
    (inputs : List OracleWorld.Domain) :
    (∑ address ∈ addresses, QueryCap.calls (atAddress parameter words address).Selects inputs) ≤
      QueryCap.calls CausalFrontierProgram.IsHash inputs :=
  QueryCap.calls_sum_le addresses _ _ (allocation_step_le parameter words addresses) inputs
theorem worldImpl_counted (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    simulateQ (segment.fixedImpl tables) (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.worldImpl high outside input)) =
      (fun answer => (answer, if segment.Selects input then 1 else 0)) <$>
        fixedHashWorld (segment.answer tables high outside) input := by
  cases input with
  | inl input =>
      simp only [worldImpl, QueryCap.counted_query, simulateQ_map, simulateQ_spec_query]
      simp only [PartialChainEndpoint.IsPrefixQuery, Selects, if_false]
      rfl
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none => simp [worldImpl, hashImpl, hparse, QueryCap.counted_pure, Selects, fixedHashWorld, answer]
      | some query =>
          simp [worldImpl, hashImpl, hparse, QueryCap.counted_map, QueryCap.counted_query,
            Selects, fixedHashWorld, answer, PartialChainEndpoint.IsPrefixQuery, fixedImpl]
theorem program_mask_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    CausalFrontierProgram.game segment.parameter (segment.answer tables high outside) ftsSecret words frontier adversary =
      CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary := by
  have himpl (root : Digest) : CausalFrontierProgram.adversaryImpl segment.parameter root
      (segment.answer tables high outside) ftsSecret words frontier =
      CausalFrontierProgram.adversaryImpl segment.parameter root outside ftsSecret words frontier := by
    funext input
    cases input with
    | inl input => rfl
    | inr message =>
        rw [CausalFrontierProgram.adversaryImpl_signing, CausalFrontierProgram.adversaryImpl_signing,
          segment.mask_answer words hword tables high outside]
  simp only [CausalFrontierProgram.game, CausalFrontierProgram.gameRest, CausalFrontierProgram.adversaryRun,
    segment.mask_answer words hword tables high outside, himpl]
theorem game_counted_source (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl tables) (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
        (segment.game high outside ftsSecret words frontier adversary)) =
      simulateQ (fixedHashWorld (segment.answer tables high outside)) (QueryCap.counted segment.Selects
        (CausalFrontierProgram.game segment.parameter (segment.answer tables high outside) ftsSecret words frontier adversary)) := by
  rw [← CausalFrontierProgram.prefix_game, segment.program_mask_answer tables high outside ftsSecret words hword frontier adversary]
  exact QueryCap.simulate_counted segment.Selects PartialChainEndpoint.IsPrefixQuery _ _ _
    (segment.worldImpl_counted tables high outside) _
end SphincsSecurity.Concrete.OtsPrefix
end
-- ==== merged from SphincsSecurity_Proof_Ots_OtsContactTrace ====
section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State AuxIndex ExtraIndex : Type} {auxSpec : OracleSpec AuxIndex} {extraSpec : OracleSpec ExtraIndex} {n : Nat} {Result : Type}
noncomputable def extendAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id) : QueryImpl (auxSpec + extraSpec) PMF
  | .inl input => auxiliary input
  | .inr input => PMF.pure (extra input)
noncomputable def eraseAux (extra : QueryImpl extraSpec Id) :
    QueryImpl ((auxSpec + extraSpec) + PrefixSpec n State) (OracleComp (auxSpec + PrefixSpec n State))
  | .inl (.inl input) => liftM ((auxSpec + PrefixSpec n State).query (.inl input))
  | .inl (.inr input) => pure (extra input)
  | .inr query => liftM ((auxSpec + PrefixSpec n State).query (.inr query))
variable [Fintype State] [DecidableEq State] [Nonempty State]
omit [Fintype State] [Nonempty State] in
theorem observedRun_eraseAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id)
    (tables : Fin n → State → State) (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (simulateQ (eraseAux extra) computation) observed = observedRun (extendAux auxiliary extra) tables computation observed := by
  have himpl : (observedImpl auxiliary tables).compose (eraseAux extra) = observedImpl (extendAux auxiliary extra) tables := by
    funext input
    cases input with
    | inl input =>
        cases input with
        | inl input => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
        | inr input =>
            simp only [QueryImpl.apply_compose, eraseAux, simulateQ_pure, observedImpl, extendAux]
            ext observed
            simp only [StateT.run_pure, StateT.run_mk, PMF.map, PMF.pure_bind, Function.comp_def, PMF.monad_pure_eq_pure]
    | inr query => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
  simp only [observedRun, ← QueryImpl.simulateQ_compose, himpl]
theorem realRun_eraseAux (auxiliary : State → QueryImpl auxSpec PMF) (extra : State → QueryImpl extraSpec Id)
    (computation : State → OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => simulateQ (eraseAux (extra endpoint)) (computation endpoint)) observed =
      realRun (fun endpoint => extendAux (auxiliary endpoint) (extra endpoint)) computation observed := by
  simp only [realRun, observedRun_eraseAux]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
abbrev VisibleWorld (segment : OtsPrefix) := OracleWorld + PartialChainEndpoint.PrefixSpec segment.digit.val Digest
noncomputable def visibleHashImpl (segment : OtsPrefix) (high : segment.Query → High) :
    QueryImpl HashSpec (OracleComp segment.VisibleWorld) := fun bytes =>
  match segment.parse bytes with
  | none => liftM (segment.VisibleWorld.query (.inl (.inr bytes)))
  | some query => (combine · (high query)) <$> liftM (segment.VisibleWorld.query (.inr query))
noncomputable def visibleWorldImpl (segment : OtsPrefix) (high : segment.Query → High) :
    QueryImpl OracleWorld (OracleComp segment.VisibleWorld)
  | .inl input => liftM (segment.VisibleWorld.query (.inl (.inl input)))
  | .inr bytes => segment.visibleHashImpl high bytes
theorem erase_visibleHashImpl (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    simulateQ (PartialChainEndpoint.eraseAux outside) (segment.visibleHashImpl high bytes) = segment.hashImpl high outside bytes := by
  cases hparse : segment.parse bytes <;>
    simp only [visibleHashImpl, hashImpl, hparse, simulateQ_spec_query, simulateQ_map, PartialChainEndpoint.eraseAux]
theorem erase_visibleWorldImpl (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    (PartialChainEndpoint.eraseAux outside).compose (segment.visibleWorldImpl high) = segment.worldImpl high outside := by
  funext input
  cases input with
  | inl input => simp only [QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query, PartialChainEndpoint.eraseAux, worldImpl]
  | inr bytes => exact segment.erase_visibleHashImpl high outside bytes
noncomputable def visibleGame (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) : OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) :=
  simulateQ (segment.visibleWorldImpl high) (CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary)
theorem erase_visibleGame (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (PartialChainEndpoint.eraseAux outside) (segment.visibleGame high outside ftsSecret words frontier adversary) =
      segment.game high outside ftsSecret words frontier adversary := by
  rw [visibleGame, ← QueryImpl.simulateQ_compose, erase_visibleWorldImpl, CausalFrontierProgram.prefix_game]
variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)
noncomputable def visibleSeedGame (endpoint : Digest) : OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) :=
  segment.visibleGame auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) adversary
theorem erase_visibleSeedGame (endpoint : Digest) :
    simulateQ (PartialChainEndpoint.eraseAux (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) =
        segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [visibleSeedGame, erase_visibleGame]
  rfl
theorem visibleSeedGame_real :
    PartialChainEndpoint.realRun (fun endpoint => PartialChainEndpoint.extendAux uniformImpl
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none) =
    PartialChainEndpoint.realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none) := by
  simpa only [erase_visibleSeedGame] using
    (PartialChainEndpoint.realRun_eraseAux (fun _ => uniformImpl)
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words)
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none)).symm
end SphincsSecurity.Concrete.OtsPrefix
end
section
namespace SphincsSecurity.QueryPause
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Source Target Memory Result : Type} {source : OracleSpec Source} {target : OracleSpec Target}
theorem run_translation (stop : Memory → Prop) [DecidablePred stop]
    (sourceStep : (input : source.Domain) → source.Range input → Memory → Memory)
    (targetStep : (input : target.Domain) → target.Range input → Memory → Memory)
    (queryMap : source.Domain → target.Domain)
    (answerMap : (input : source.Domain) → target.Range (queryMap input) → source.Range input)
    (impl : QueryImpl source (OracleComp target))
    (himpl : ∀ input, impl input = answerMap input <$> liftM (target.query (queryMap input)))
    (hstep : ∀ input answer memory, targetStep (queryMap input) answer memory = sourceStep input (answerMap input answer) memory)
    (computation : OracleComp source Result) (memory : Memory) :
    run stop targetStep (simulateQ impl computation) memory =
      (fun paused => (paused.1, simulateQ impl paused.2)) <$> simulateQ impl (run stop sourceStep computation memory) := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure result => simp only [simulateQ_pure, run_pure, map_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, simulateQ_pure, map_pure, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, map_bind, hstep, ih]
end SphincsSecurity.QueryPause
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def hashObservationTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → FreeMonoid (HashInput × HashOutput)
  | .inl _, _ => 1
  | .inr input, answer => FreeMonoid.of (input, answer)
namespace OtsPrefix
noncomputable def visibleObservationTrace (segment : OtsPrefix) (high : segment.Query → High) :
    (input : segment.VisibleWorld.Domain) → segment.VisibleWorld.Range input → FreeMonoid (HashInput × HashOutput)
  | .inl input, answer => hashObservationTrace input answer
  | .inr query, answer => FreeMonoid.of (segment.input query, combine answer (high query))
private theorem withTrace_run {Input Target Trace : Type} {spec : OracleSpec Input} {target : OracleSpec Target} [Monoid Trace]
    (impl : QueryImpl spec (OracleComp target)) (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    (impl.withTrace trace input).run = (fun answer => (answer, trace input answer)) <$> impl input := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]
theorem visible_observation_step (segment : OtsPrefix) (high : segment.Query → High) (input : OracleWorld.Domain) :
    (simulateQ ((QueryImpl.id' segment.VisibleWorld).withTrace (segment.visibleObservationTrace high))
      (segment.visibleWorldImpl high input)).run =
        ((segment.visibleWorldImpl high).withTrace hashObservationTrace input).run := by
  cases input with
  | inl input =>
      simp only [visibleWorldImpl, simulateQ_spec_query, withTrace_run, visibleObservationTrace, hashObservationTrace]
      rfl
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleWorldImpl, visibleHashImpl, hparse, simulateQ_spec_query, withTrace_run,
            visibleObservationTrace, hashObservationTrace]
          rfl
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleWorldImpl, visibleHashImpl, parse_input, simulateQ_map, simulateQ_spec_query, WriterT.run_map,
            withTrace_run, visibleObservationTrace, hashObservationTrace, Functor.map_map]
          rfl
theorem visible_observation_program (segment : OtsPrefix) (high : segment.Query → High)
    {Result : Type} (computation : OracleComp OracleWorld Result) :
    (simulateQ ((QueryImpl.id' segment.VisibleWorld).withTrace (segment.visibleObservationTrace high))
      (simulateQ (segment.visibleWorldImpl high) computation)).run =
    simulateQ (segment.visibleWorldImpl high)
      ((simulateQ ((QueryImpl.id' OracleWorld).withTrace hashObservationTrace) computation).run) := by
  rw [← QueryImpl.simulateQ_compose]
  symm
  apply simulateQ_writer_compose
  intro input
  rw [QueryImpl.apply_compose, visible_observation_step, withTrace_run, withTrace_run, simulateQ_map]
  change (fun answer => (answer, hashObservationTrace input answer)) <$>
    simulateQ (segment.visibleWorldImpl high) (liftM (OracleWorld.query input)) = _
  rw [simulateQ_spec_query]
theorem visible_pause_program (segment : OtsPrefix) (high : segment.Query → High)
    (stop : FreeMonoid (HashInput × HashOutput) → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : FreeMonoid (HashInput × HashOutput)) :
    QueryPause.run stop (fun input answer history => history * segment.visibleObservationTrace high input answer)
      (simulateQ (segment.visibleWorldImpl high) computation) trace =
    (fun paused => (paused.1, simulateQ (segment.visibleWorldImpl high) paused.2)) <$>
      simulateQ (segment.visibleWorldImpl high)
        (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace) := by
  classical
  have htranslation (input : OracleWorld.Domain) : ∃ (query : segment.VisibleWorld.Domain)
      (decode : segment.VisibleWorld.Range query → OracleWorld.Range input),
      segment.visibleWorldImpl high input = decode <$> liftM (segment.VisibleWorld.query query) ∧
        ∀ answer (history : FreeMonoid (HashInput × HashOutput)),
          history * segment.visibleObservationTrace high query answer = history * hashObservationTrace input (decode answer) := by
    cases input with
    | inl input =>
        refine ⟨.inl (.inl input), id, ?_, ?_⟩
        · simp only [visibleWorldImpl, id_map]
        · intro answer history; rfl
    | inr bytes =>
        cases hparse : segment.parse bytes with
        | none =>
            refine ⟨.inl (.inr bytes), id, ?_, ?_⟩
            · simp only [visibleWorldImpl, visibleHashImpl, hparse, id_map]
            · intro answer history; rfl
        | some query =>
            refine ⟨.inr query, fun answer => combine answer (high query), ?_, ?_⟩
            · simp only [visibleWorldImpl, visibleHashImpl, hparse]
              rfl
            · intro answer history
              simp only [visibleObservationTrace, hashObservationTrace, (segment.parse_some_iff bytes query).mp hparse]
  exact QueryPause.run_translation stop _ _ (fun input => (htranslation input).choose)
    (fun input => (htranslation input).choose_spec.choose) (segment.visibleWorldImpl high)
    (fun input => (htranslation input).choose_spec.choose_spec.1)
    (fun input => (htranslation input).choose_spec.choose_spec.2) computation trace
end OtsPrefix
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Trace := FreeMonoid (HashInput × HashOutput)
def EntryContact (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput) : Prop :=
  ∃ query : segment.Query, segment.parse entry.1 = some query ∧ query.1.val + 1 = segment.digit.val ∧ truncateHash entry.2 = endpoint
def Seen (segment : OtsPrefix) (endpoint : Digest) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, EntryContact segment endpoint entry
theorem entryContact_selects (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput)
    (h : EntryContact segment endpoint entry) : segment.Selects (.inr entry.1) := by
  obtain ⟨query, hquery, _⟩ := h
  change segment.parse entry.1 ≠ none
  rw [hquery]
  exact Option.some_ne_none query
theorem entryContact_unique (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (entry : HashInput × HashOutput) (left right : OtsPrefix.ChainAddress)
    (hleft : EntryContact (OtsPrefix.atAddress parameter words left) (frontier left.1 left.2.1 left.2.2.1 left.2.2.2) entry)
    (hright : EntryContact (OtsPrefix.atAddress parameter words right) (frontier right.1 right.2.1 right.2.2.1 right.2.2.2) entry) : left = right :=
  OtsPrefix.atAddress_selects_unique parameter words left right (.inr entry.1)
    (entryContact_selects _ _ entry hleft) (entryContact_selects _ _ entry hright)
theorem seen_one (segment : OtsPrefix) (endpoint : Digest) : ¬Seen segment endpoint 1 := by
  simp [Seen]
theorem seen_of (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput) :
    Seen segment endpoint (FreeMonoid.of entry) ↔ EntryContact segment endpoint entry := by
  simp [Seen]
theorem seen_mul (segment : OtsPrefix) (endpoint : Digest) (first second : Trace) :
    Seen segment endpoint (first * second) ↔ Seen segment endpoint first ∨ Seen segment endpoint second := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]
noncomputable def contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (trace : Trace) :
    Finset OtsPrefix.ChainAddress :=
  Finset.univ.filter fun address => Seen (OtsPrefix.atAddress parameter words address)
    (frontier address.1 address.2.1 address.2.2.1 address.2.2.2) trace
theorem mem_contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : Trace) (address : OtsPrefix.ChainAddress) :
    address ∈ contacts parameter words frontier trace ↔ Seen (OtsPrefix.atAddress parameter words address)
      (frontier address.1 address.2.1 address.2.2.1 address.2.2.2) trace := by simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
theorem contacts_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    contacts parameter words frontier 1 = ∅ := by
  ext address
  simp only [mem_contacts, seen_one, Finset.notMem_empty]
theorem contacts_mul (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (first second : Trace) :
    contacts parameter words frontier (first * second) = contacts parameter words frontier first ∪ contacts parameter words frontier second := by
  ext address
  simp only [mem_contacts, seen_mul, Finset.mem_union]
attribute [local irreducible] contacts
theorem contacts_of_card_le_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (entry : HashInput × HashOutput) : (contacts parameter words frontier (FreeMonoid.of entry)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro left hleft right hright
  rw [mem_contacts, seen_of] at hleft hright
  exact entryContact_unique parameter words frontier entry left right hleft hright
theorem contacts_step_card_le (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : Trace) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) :
    (contacts parameter words frontier (trace * hashObservationTrace input answer)).card ≤
      (contacts parameter words frontier trace).card + 1 := by
  cases input with
  | inl input => simp only [hashObservationTrace, mul_one]; omega
  | inr input =>
      rw [hashObservationTrace, contacts_mul]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (contacts_of_card_le_one parameter words frontier (input, answer)) _)
theorem new_contact_of_two (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (before after : Trace) (hbefore : (contacts parameter words frontier before).card ≤ 1)
    (hafter : 2 ≤ (contacts parameter words frontier (before * after)).card) :
    ∃ address, address ∉ contacts parameter words frontier before ∧ address ∈ contacts parameter words frontier after := by
  by_contra h
  push Not at h
  have hsub : contacts parameter words frontier after ⊆ contacts parameter words frontier before := by
    intro address ha
    by_contra hb
    exact h address hb ha
  rw [contacts_mul, Finset.union_eq_left.mpr hsub] at hafter
  omega
end SphincsSecurity.Concrete.OtsContactTrace
end
end
-- ==== merged from SphincsSecurity_Proof_Ots_EncodingFreshRow ====
section

section
namespace SphincsSecurity.OtsCode
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decode digest = some word
theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decode digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]
theorem decodingDigests_card_le (words : Finset Encoding) : (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn (fun digest => (decode digest).getD defaultWord)
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    simpa only [hdecode, Option.getD_some, Finset.mem_coe] using hw
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    simp only [hleft, hright, Option.getD_some] at he
    exact decode_some_injective hleft (by rw [he]; exact hright)
theorem decodingDigests_uniform_le (words : Finset Encoding) :
    Pr[fun output : HashOutput => truncateHash output ∈ decodingDigests words | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (words.card : ENNReal) / Fintype.card Digest := by
  rw [probEvent_uniform_truncateHash_mem]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (decodingDigests_card_le words)) _
end SphincsSecurity.OtsCode
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
def FreshEncodingSupport (reference : Encoding) (allowed : Finset HashOutput) : Prop :=
  allowed = Finset.univ ∨ ∀ output ∈ allowed, decodeEncodingOutput output = none ∨ decodeEncodingOutput output = some reference
theorem firstSuccess_allowed_fresh {n : Nat} (index : Fin n) (reference : Encoding) (coordinate : Fin n) :
    FreshEncodingSupport reference (FirstSuccessTable.allowed decodeEncodingOutput index reference coordinate) := by
  unfold FirstSuccessTable.allowed
  split_ifs with hlt heq
  · exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
  · exact Or.inr fun output ho => Or.inr ((FirstSuccessTable.mem_fiber _ _ _).mp ho)
  · exact Or.inl rfl
theorem freshEncodingSupport_probability_le (reference : Encoding) (targets : Finset Encoding) (href : reference ∉ targets)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests targets | PMF.uniformOfFinset allowed ha] ≤
      (targets.card : ENNReal) / Fintype.card Digest := by
  rcases hallowed with rfl | hrestricted
  · have h := OtsCode.decodingDigests_uniform_le targets
    simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply,
      Finset.mem_univ, if_true, Finset.card_univ] using h
  · have hzero : Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests targets |
        PMF.uniformOfFinset allowed ha] = 0 := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro output
      by_cases hm : output ∈ allowed
      · have hn : truncateHash output ∉ OtsCode.decodingDigests targets := by
          intro hd
          obtain ⟨word, hw, hdecode⟩ := OtsCode.mem_decodingDigests.mp hd
          change decodeEncodingOutput output = some word at hdecode
          rcases hrestricted output hm with hi | hr
          · rw [hi] at hdecode
            contradiction
          · have he : reference = word := Option.some.inj (hr.symm.trans hdecode)
            exact href (he ▸ hw)
        exact if_neg hn
      · simp only [PMF.uniformOfFinset_apply, if_neg hm, ite_self]
    rw [hzero]
    exact zero_le
theorem freshEncodingSupport_neighbor_le (reference : Encoding) (lowered : ChainIndex)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests (OtsCode.unitNeighbors reference lowered) |
      PMF.uniformOfFinset allowed ha] ≤ (OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  have href : reference ∉ OtsCode.unitNeighbors reference lowered := by
    intro h
    exact (OtsCode.mem_unitNeighbors.mp h).ne rfl
  exact (freshEncodingSupport_probability_le reference _ href allowed ha hallowed).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (OtsCode.unitNeighbors_card_le reference lowered)) _)
theorem freshEncodingSupport_all_neighbors_le (reference : Encoding)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests (OtsCode.allUnitNeighbors reference) |
      PMF.uniformOfFinset allowed ha] ≤ (OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  have href : reference ∉ OtsCode.allUnitNeighbors reference := by
    intro h
    obtain ⟨lowered, ht⟩ := OtsCode.mem_allUnitNeighbors.mp h
    exact ht.ne rfl
  exact (freshEncodingSupport_probability_le reference _ href allowed ha hallowed).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (OtsCode.allUnitNeighbors_card_le reference)) _)
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableObservation ====
section

namespace SphincsSecurity.Concrete.UniformTableObservation
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value AuxIndex : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
  {auxSpec : OracleSpec AuxIndex}
abbrev TableSpec (Coordinate Value : Type) := Coordinate →ₒ Value
noncomputable def observedImpl (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value) :
    QueryImpl (auxSpec + TableSpec Coordinate Value) (StateT (Coordinate → Finset Value) SPMF)
  | .inl input => StateT.mk fun allowed => (fun answer => (answer, allowed)) <$> auxiliary input
  | .inr coordinate => StateT.mk fun allowed =>
      pure (table coordinate, discloseTableValue allowed coordinate (table coordinate))
noncomputable def lazyImpl (auxiliary : QueryImpl auxSpec SPMF) :
    QueryImpl (auxSpec + TableSpec Coordinate Value) (StateT (Coordinate → Finset Value) SPMF)
  | .inl input => StateT.mk fun allowed => (fun answer => (answer, allowed)) <$> auxiliary input
  | .inr coordinate => StateT.mk fun allowed =>
      (fun answer => (answer, discloseTableValue allowed coordinate answer)) <$> cell (allowed coordinate)
noncomputable def observedRun {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    SPMF (Result × (Coordinate → Finset Value)) :=
  (simulateQ (observedImpl auxiliary table) computation).run allowed
noncomputable def lazyRun {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    SPMF (Result × (Coordinate → Finset Value)) :=
  (simulateQ (lazyImpl auxiliary) computation).run allowed
omit [Fintype Coordinate] [DecidableEq Value] in
theorem observedRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (result : Result) (allowed : Coordinate → Finset Value) :
    observedRun auxiliary table (pure result) allowed = pure (result, allowed) := by
  simp only [observedRun, simulateQ_pure, StateT.run_pure]
omit [Fintype Coordinate] [DecidableEq Value] in
theorem lazyRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (result : Result) (allowed : Coordinate → Finset Value) :
    lazyRun auxiliary (pure result) allowed = pure (result, allowed) := by
  simp only [lazyRun, simulateQ_pure, StateT.run_pure]
omit [Fintype Coordinate] [DecidableEq Value] in
theorem observedRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (input : (auxSpec + TableSpec Coordinate Value).Domain)
    (next : (auxSpec + TableSpec Coordinate Value).Range input → OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) :
    observedRun auxiliary table (liftM ((auxSpec + TableSpec Coordinate Value).query input) >>= next) allowed =
      ((observedImpl auxiliary table input).run allowed >>= fun result =>
        observedRun auxiliary table (next result.1) result.2) := by
  simp only [observedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
omit [Fintype Coordinate] [DecidableEq Value] in
theorem lazyRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (input : (auxSpec + TableSpec Coordinate Value).Domain)
    (next : (auxSpec + TableSpec Coordinate Value).Range input → OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) :
    lazyRun auxiliary (liftM ((auxSpec + TableSpec Coordinate Value).query input) >>= next) allowed =
      ((lazyImpl auxiliary input).run allowed >>= fun result => lazyRun auxiliary (next result.1) result.2) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
theorem run_posterior {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    (complete allowed >>= fun table =>
      (fun result => (table, result)) <$> observedRun auxiliary table computation allowed) =
        (lazyRun auxiliary computation allowed >>= fun result =>
          (fun table => (table, result)) <$> complete result.2) := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure result => simp only [observedRun_pure, lazyRun_pure, pure_bind, ← bind_pure_comp]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, bind_map_left, map_bind, bind_assoc]
          rw [RetainedObservation.bind_comm]
          exact congrArg (fun continuation => auxiliary input >>= continuation)
            (funext fun answer => ih answer allowed)
      | inr coordinate =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, pure_bind, bind_map_left, bind_assoc]
          rw [bind_disclose allowed coordinate (fun answer table =>
            (fun result => (table, result)) <$>
              observedRun auxiliary table (next answer) (discloseTableValue allowed coordinate answer))]
          exact congrArg (fun continuation => cell (allowed coordinate) >>= continuation)
            (funext fun answer => ih answer (discloseTableValue allowed coordinate answer))
end SphincsSecurity.Concrete.UniformTableObservation
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableProducts ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem uniformTable_eq_product {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Value] [DecidableEq Value] (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    uniformTable allowed ha = FinitePmfProduct.law (fun coordinate => PMF.uniformOfFinset (allowed coordinate) (ha coordinate)) := by
  apply PMF.ext
  intro table
  rw [uniformTable_apply, FinitePmfProduct.apply]
  simp only [PMF.uniformOfFinset_apply]
  by_cases ht : ∀ coordinate, table coordinate ∈ allowed coordinate
  · simp only [ht, implies_true, if_true]
    rw [Nat.cast_prod, ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by finiteness))]
  · rw [if_neg ht]
    obtain ⟨coordinate, hc⟩ := not_forall.mp ht
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ coordinate) (if_neg hc)
theorem FinitePmfProduct.uncurry {Index Coordinate Value : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Value]
    (family : Index → Coordinate → PMF Value) :
    (law (fun index => law (family index))).map Function.uncurry =
      law (fun coordinate : Index × Coordinate => family coordinate.1 coordinate.2) := by
  classical
  apply PMF.ext
  intro table
  rw [PMF.map_apply, tsum_eq_single (Function.curry table)]
  · simp only [Function.uncurry_curry, if_true, apply]
    rw [Fintype.prod_prod_type]
    rfl
  · intro candidate hne
    apply if_neg
    intro heq
    apply hne
    exact (congrArg Function.curry heq).symm
theorem uniformTable_univ {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Value] [DecidableEq Value] [Nonempty Value] :
    uniformTable (fun _ : Coordinate => (Finset.univ : Finset Value)) (fun _ => Finset.univ_nonempty) =
      PMF.uniformOfFintype (Coordinate → Value) := by
  apply PMF.ext
  intro table
  simp only [uniformTable_apply, Finset.mem_univ, implies_true, if_true, Finset.card_univ,
    Finset.prod_const, Nat.cast_pow, PMF.uniformOfFintype_apply, Fintype.card_fun]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_EncodingTablePrior ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def encodingSelectionRows (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  match selection with
  | none => fun _ => FirstSuccessTable.invalid decodeEncodingOutput
  | some (index, word) => FirstSuccessTable.allowed decodeEncodingOutput index word
noncomputable def encodingSelectionAllowed (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  if ∀ coordinate, (encodingSelectionRows selection coordinate).Nonempty then encodingSelectionRows selection
  else fun _ => Finset.univ
theorem encodingSelectionAllowed_nonempty (selection : ReferenceSelection) :
    ∀ coordinate, (encodingSelectionAllowed selection coordinate).Nonempty := by
  unfold encodingSelectionAllowed
  split_ifs with hrows
  · exact hrows
  · exact fun _ => Finset.univ_nonempty
theorem encodingSelectionAllowed_fresh (selection : ReferenceSelection) (dummy : Encoding) (coordinate : Fin encodingAttemptLimit) :
    FreshEncodingSupport ((selection.map Prod.snd).getD dummy) (encodingSelectionAllowed selection coordinate) := by
  unfold encodingSelectionAllowed
  split_ifs
  · cases selection with
    | none => exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
    | some selected =>
        obtain ⟨index, word⟩ := selected
        exact firstSuccess_allowed_fresh index word coordinate
  · exact Or.inl rfl
private theorem uniformTable_rows_eq {rows rows' : Fin encodingAttemptLimit → Finset HashOutput} (h : rows = rows')
    (hrows : ∀ coordinate, (rows coordinate).Nonempty) (hrows' : ∀ coordinate, (rows' coordinate).Nonempty) :
    uniformTable rows hrows = uniformTable rows' hrows' := by
  subst h
  rfl
theorem encoding_afterSelect_complete (selection : ReferenceSelection) :
    𝒮[FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection] =
      complete (encodingSelectionAllowed selection) := by
  rw [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection)]
  have hafter : FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      FirstSuccessTable.constrained (encodingSelectionRows selection) := by
    cases selection with
    | none => rfl
    | some selected =>
        obtain ⟨index, word⟩ := selected
        rfl
  rw [hafter, FirstSuccessTable.constrained]
  split_ifs with hrows
  · rw [uniformTable_rows_eq (show encodingSelectionRows selection = encodingSelectionAllowed selection from
      (if_pos hrows).symm) hrows (encodingSelectionAllowed_nonempty selection)]
  · rw [FirstSuccessTable.full, uniformTable_rows_eq (show (fun _ => Finset.univ) = encodingSelectionAllowed selection from
      (if_neg hrows).symm) _ (encodingSelectionAllowed_nonempty selection)]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def encodingFamilyAllowed (selections : ReferenceFamily) (row : EncodingRow) : Finset HashOutput :=
  encodingSelectionAllowed (selections row.1) row.2
theorem encodingFamilyAllowed_nonempty (selections : ReferenceFamily) :
    ∀ row, (encodingFamilyAllowed selections row).Nonempty :=
  fun row => encodingSelectionAllowed_nonempty (selections row.1) row.2
theorem encoding_afterSelect_uniform (selection : ReferenceSelection) :
    FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      uniformTable (encodingSelectionAllowed selection) (encodingSelectionAllowed_nonempty selection) := by
  apply PMF.ext
  intro table
  have h := congrArg (fun law : SPMF (Fin encodingAttemptLimit → HashOutput) => law table)
    (encoding_afterSelect_complete selection)
  simpa only [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection), PMF.evalSPMF_eq, SPMF.liftM_apply] using h
theorem encoding_family_uniform (selections : ReferenceFamily) :
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).map Function.uncurry =
        uniformTable (encodingFamilyAllowed selections) (encodingFamilyAllowed_nonempty selections) := by
  simp only [FirstSuccessFamily.afterSelect, encoding_afterSelect_uniform, uniformTable_eq_product]
  exact FinitePmfProduct.uncurry (fun position coordinate =>
    PMF.uniformOfFinset (encodingSelectionAllowed (selections position) coordinate)
      (encodingSelectionAllowed_nonempty (selections position) coordinate))
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.UniformTableSplit
open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Index Cell Answer : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
theorem join_eq_iff (table : Cell → Answer) (rows : Index → Answer) (outside : Outside embed → Answer) :
    table = join embed hinj rows outside ↔ rows = table ∘ embed ∧ outside = fun cell : Outside embed => table cell.val := by
  constructor
  · intro heq
    subst table
    constructor
    · funext index
      exact (join_embed embed hinj rows outside index).symm
    · funext cell
      exact (join_outside embed hinj rows outside cell).symm
  · rintro ⟨rfl, rfl⟩
    exact (join_split embed hinj table).symm
attribute [local irreducible] join
section Mass
attribute [local instance 10000] Classical.propDecidable
theorem bind_map_join_apply (left : PMF (Index → Answer)) (right : PMF (Outside embed → Answer)) (table : Cell → Answer) :
    (left.bind fun rows => right.map (join embed hinj rows)) table =
      left (table ∘ embed) * right (fun cell => table cell.val) := by
  simp only [PMF.bind_apply, PMF.map_apply]
  rw [tsum_eq_single (table ∘ embed)]
  · rw [tsum_eq_single (fun cell : Outside embed => table cell.val)]
    · rw [if_pos (join_split embed hinj table).symm]
    · intro outside hne
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table _ outside).mp h).2)
  · intro rows hne
    have hz : (∑' outside : Outside embed → Answer,
        if table = join embed hinj rows outside then right outside else 0) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro outside
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table rows outside).mp h).1)
    rw [hz, mul_zero]
end Mass
variable [Fintype Index] [Fintype Cell] [DecidableEq Cell]
include hinj in
theorem prod_embed_mul_outside {M : Type} [CommMonoid M] (f : Cell → M) :
    (∏ index, f (embed index)) * (∏ cell : Outside embed, f cell.val) = ∏ cell, f cell := by
  letI : Fintype (Set.range embed) := Subtype.fintype (Set.range embed)
  have he : (∏ index, f (embed index)) = ∏ cell : Set.range embed, f cell.val :=
    Fintype.prod_equiv (Equiv.ofInjective embed hinj) _ _ (fun _ => rfl)
  rw [he]
  convert Fintype.prod_subtype_mul_prod_subtype (Set.range embed) f using 1
  congr 1
  exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
variable [DecidableEq Index] [Fintype Answer]
theorem product_join (left : Index → PMF Answer) (right : Outside embed → PMF Answer) :
    (FinitePmfProduct.law left).bind (fun rows => (FinitePmfProduct.law right).map (join embed hinj rows)) =
      FinitePmfProduct.law (join embed hinj left right) := by
  apply PMF.ext
  intro table
  rw [bind_map_join_apply]
  simp only [FinitePmfProduct.apply]
  have hp := prod_embed_mul_outside embed hinj (fun cell => join embed hinj left right cell (table cell))
  simpa only [join_embed, join_outside, Function.comp_def] using hp
variable [DecidableEq Answer]
omit [Fintype Cell] [DecidableEq Index] [Fintype Answer] [DecidableEq Answer] in
theorem join_nonempty (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    ∀ cell, (join embed hinj left right cell).Nonempty := by
  intro cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    rw [join_embed]
    exact hl index
  · change (join embed hinj left right (⟨cell, hc⟩ : Outside embed).val).Nonempty
    rw [join_outside]
    exact hr ⟨cell, hc⟩
theorem uniformTable_join (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    (uniformTable left hl).bind (fun rows => (uniformTable right hr).map (join embed hinj rows)) =
      uniformTable (join embed hinj left right) (join_nonempty embed hinj left right hl hr) := by
  simp only [uniformTable_eq_product, product_join]
  apply congrArg FinitePmfProduct.law
  funext cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    simp only [join_embed]
  · change join embed hinj _ _ (⟨cell, hc⟩ : Outside embed).val = _
    rw [join_outside]
    have hrow := join_outside embed hinj left right (⟨cell, hc⟩ : Outside embed)
    simp only [hrow]
end SphincsSecurity.Concrete.UniformTableSplit
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs UniformTableSplit.join
noncomputable def referenceEncodingAllowed (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : canonicalEncodingInputs parameter → Finset HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (encodingFamilyAllowed selections) (fun _ => Finset.univ)
theorem referenceEncodingAllowed_nonempty (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : ∀ cell, (referenceEncodingAllowed parameter messages selections cell).Nonempty :=
  UniformTableSplit.join_nonempty _ _ _ _ (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
noncomputable def referenceEncodingPrior (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : PMF (canonicalEncodingInputs parameter → HashOutput) :=
  (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
    (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside (referenceFamilyCell parameter messages) → HashOutput)).map
      (UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
        (Function.uncurry rows)))
theorem referenceEncodingPrior_uniform (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    referenceEncodingPrior parameter messages selections =
      uniformTable (referenceEncodingAllowed parameter messages selections)
        (referenceEncodingAllowed_nonempty parameter messages selections) := by
  have h := UniformTableSplit.uniformTable_join (referenceFamilyCell parameter messages)
    (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => Finset.univ)
    (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
  rw [uniformTable_univ, ← encoding_family_uniform selections, PMF.bind_map] at h
  exact h
theorem referenceEncodingPrior_complete (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    𝒮[referenceEncodingPrior parameter messages selections] = complete (referenceEncodingAllowed parameter messages selections) := by
  rw [referenceEncodingPrior_uniform, complete_of_nonempty _ (referenceEncodingAllowed_nonempty parameter messages selections)]
theorem referenceEncodingAllowed_fresh (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter)
    (position : EncodingPosition) (hposition : AtEncodingPosition parameter cell.val position) :
    FreshEncodingSupport (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx)
      (referenceEncodingAllowed parameter messages selections cell) := by
  by_cases hc : cell ∈ Set.range (referenceFamilyCell parameter messages)
  · obtain ⟨row, rfl⟩ := hc
    have hp := atEncodingPosition_unique hposition
      (show AtEncodingPosition parameter (referenceFamilyCell parameter messages row).val row.1 from ⟨_, rfl⟩)
    subst position
    rw [referenceEncodingAllowed, UniformTableSplit.join_embed]
    exact encodingSelectionAllowed_fresh (selections row.1) (dummy row.1.lay row.1.tree row.1.leafIdx) row.2
  · have hrow := UniformTableSplit.join_outside (referenceFamilyCell parameter messages)
      (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => (Finset.univ : Finset HashOutput))
      (⟨cell, hc⟩ : UniformTableSplit.Outside (referenceFamilyCell parameter messages))
    exact Or.inl hrow
end SphincsSecurity.Concrete
end
end
