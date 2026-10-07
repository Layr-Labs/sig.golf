import SigGolfCandidate.T3.Secc.LargeContactChain
import SigGolfCandidate.T3.Secc.LargeContactWalk

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def AllClear (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) : Prop :=
  ∀ X, (.inl (.inr X) : Spec.Domain) ∈ qs → Clear A K X (A (.inl (.inr X)))
theorem slotValue_block4_three (a b c d : Digest) : slotValue (block4 a b c d) 3 = d := by
  unfold slotValue block4
  have ha := bytesLE_length 16 a
  have hb := bytesLE_length 16 b
  have hc := bytesLE_length 16 c
  have hd := bytesLE_length 16 d
  rw [show 16 * 3 = (bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c).length by simp [ha, hb, hc]]
  rw [List.drop_left]
  rw [show (bytesLE 16 d).take 16 = bytesLE 16 d from List.take_of_length_le (by rw [hd])]
  exact Correctness.readDigest_bytesLE d
theorem chainRow_block4 (a : Wots.ChainAddr) (s : Nat) (v : Digest) :
    Wots.chainRow a s v = block4 0 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) 0 v := by
  simp only [Wots.chainRow, chainInput, block4, show zero16 = bytesLE 16 (0 : Digest) by decide]
theorem slotValue_chainRow (a : Wots.ChainAddr) (s : Nat) (v : Digest) : slotValue (Wots.chainRow a s v) 3 = v := by
  rw [chainRow_block4, slotValue_block4_three]
theorem chainCount_le58 (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
def gAddr (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) : ChainGraph.Address :=
  ⟨a.key.lay, ⟨a.key.tree, ha.1.1⟩,
    ⟨a.key.leaf, lt_of_lt_of_le ha.1.2 (by
      calc 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
        _ = 4096 := by norm_num)⟩,
    ⟨a.chain, lt_of_lt_of_le ha.2 (chainCount_le58 _)⟩⟩
theorem wotsAddr_gAddr (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) : wotsAddr (gAddr a ha) = a := rfl
theorem honestInput_chainNode (A : Answers) (p : ChainGraph.Point) :
    Extract.honestInput A (CanonGraph.Node.chain p).toPos =
      Wots.chainRow (wotsAddr p.1) p.2.val (honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val) := by
  show pad64 _ = _
  rw [chainInput_padded]
  rfl
theorem honestValue_chainNode (A : Answers) (p : ChainGraph.Point) :
    honestValue A (.inl (.chain p)) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) (p.2.val + 1) := by
  rw [← honestChainValue_succ, eval_shortHash]
  rfl
theorem honestChainValue_zero' (A : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValue A lay tree leaf i seed 0 = seed := by
  simp [honestChainValue, chain]
theorem honestValue_chainChild (A : Answers) (p : ChainGraph.Point) :
    honestValue A (chainChild p) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val := by
  unfold chainChild
  by_cases h0 : p.2.val = 0
  · rw [if_pos h0, h0, honestChainValue_zero']
    rfl
  · rw [if_neg h0, honestValue_chainNode]
    simp only [ChainGraph.predecessor]
    congr 1
    omega
theorem childSlots_chain (p : ChainGraph.Point) : childSlots (.chain p) = [(chainChild p, 3)] := rfl
theorem structuralHitSrc_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (h : WotsExtract.StructuralHitSrc A (Wots.entriesOf A qs)) (hclear : AllClear A K qs) : False := by
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, -, hne, hlow⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hsp : CanonGraph.SourcePos position := by
    cases position with
    | chain lay tree leaf i step =>
        obtain ⟨h1, h2, h3, h4⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_, lt_of_lt_of_le h3 (chainCount_le58 lay), ?_⟩
        · calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
            _ = 4096 := by norm_num
        · have hw : 2 ^ width lay i ≤ 8 := by unfold width; split_ifs <;> norm_num
          omega
    | leaf lay tree leaf =>
        obtain ⟨h1, h2⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
          _ = 4096 := by norm_num
    | node lay tree level nd => exact hsrc
    | forest index => exact hsrc
    | ftsLeaf index coord leaf => exact hsrc
    | ftsNode index coord level nd => exact hsrc
  obtain ⟨N, rfl⟩ := CanonGraph.exists_toPos hsp
  exact (hclear _ hq).1 N hpos ⟨hne, hlow⟩
theorem encodingMatch_route_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) (index : Nat)
    (hidx : index < 2 ^ 31) (lay : Layer)
    (h : Wots.EncodingMatchAt A (Wots.entriesOf A qs) (WotsExtract.routeLeaf index lay))
    (hclear : AllClear A K qs) : False := by
  obtain ⟨m, ctr, answer, hmem, hne, hdec⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  obtain ⟨L, hL⟩ := CanonEncoding.route_source index hidx lay
  have hL' : L.toWots = WotsExtract.routeLeaf index lay := hL
  refine (hclear _ hq).2.2 L m ctr (by rw [hL']) ⟨?_, ?_⟩
  · rw [hL']; exact hne
  · have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL'
    rw [hans, hL', hlay]; exact hdec
end SigGolfCandidate.T3.Security.LargeCoupling
