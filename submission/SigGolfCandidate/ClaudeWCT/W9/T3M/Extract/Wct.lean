import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.W9Drv.FtsCore
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.HdrBlocks
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs

namespace ClaudeWCT.W9.T3M.WctExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (nodeHashP sibOff)
open Correctness (Answers treeValue TreeLevels)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem queried_mapM {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ l : List α, queried answers (l.mapM f) = l.flatMap fun a => queried answers (f a)
  | [] => rfl
  | a :: l => by
      rw [List.mapM_cons, queried_bind, queried_bind, queried_mapM answers f l]
      simp
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem queried_hashPath (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) :
    ∀ count, queried answers (hashPath input count initial) =
      (List.range count).map fun step => .inl (.inr (pad64 (pathInput answers input initial step)))
  | 0 => rfl
  | count + 1 => by
      rw [hashPath_succ, queried_bind, queried_hashPath answers input initial count, List.range_succ,
        List.map_append, queried_shortHash]
      rfl
theorem pathValue_honest (answers : Answers) (input : Nat → Digest → HashInput) (honestInput : Nat → HashInput)
    (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) : ∀ step, step ≤ count → pathValue answers input initial step = target step := by
  intro step
  induction step with
  | zero => intro _; exact h0
  | succ step ih =>
      intro hs
      rw [pathValue_succ, pathInput, ih (by omega), honest step (by omega), reference step (by omega)]
theorem queried_hashPath_honest (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) :
    ∀ q ∈ queried answers (hashPath input count initial), ∃ step, step < count ∧
      q = .inl (.inr (pad64 (honestInput step))) := by
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  refine ⟨step, hs, ?_⟩
  rw [pathInput, pathValue_honest answers input honestInput target initial count reference honest h0 step hs.le,
    honest step hs]
theorem hdrBlock_block4W (a b c d : Digest) : Extract.hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold Extract.hdrBlock block4
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a)]
  rw [List.take_append_of_le_length (by simp [bytesLE_length]), List.take_of_length_le (by simp [bytesLE_length])]
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    Extract.hdrBlock (pad64 (Extract.listInput first hdr rest)) = bytesLE 16 hdr := by
  unfold Extract.hdrBlock pad64 Extract.listInput
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 first)]
  rw [List.take_append_of_le_length (by simp [bytesLE_length]), List.take_of_length_le (by simp [bytesLE_length])]
theorem flatMap_bytesLE_length (l : List Digest) : (l.flatMap (bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem flatMap_bytesLE_injective : ∀ (l l' : List Digest), l.length = l'.length →
    l.flatMap (bytesLE 16) = l'.flatMap (bytesLE 16) → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, a' :: l', h, he => by
      simp only [List.flatMap_cons] at he
      obtain ⟨ha, hl⟩ := List.append_inj he (by simp only [bytesLE_length])
      rw [bytesLE_injective ha, flatMap_bytesLE_injective l l' (by simpa using h) hl]
theorem pad64_injective_of_length {x y : HashInput} (hl : x.length = y.length) (h : pad64 x = pad64 y) : x = y := by
  unfold pad64 at h
  rw [hl] at h
  exact (List.append_inj h hl).1
theorem listInput_injective {hdr : BitVec 128} {ds ds' : List Digest}
    (hds : ds.length = ds'.length) (hpos : 0 < ds.length)
    (h : pad64 (Extract.listInput (ds.getD 0 0) hdr (ds.drop 1)) =
      pad64 (Extract.listInput (ds'.getD 0 0) hdr (ds'.drop 1))) : ds = ds' := by
  have hlen : (Extract.listInput (ds.getD 0 0) hdr (ds.drop 1)).length =
      (Extract.listInput (ds'.getD 0 0) hdr (ds'.drop 1)).length := by
    simp only [Extract.listInput, List.length_append, bytesLE_length, flatMap_bytesLE_length, List.length_drop, hds]
  have h := pad64_injective_of_length hlen h
  unfold Extract.listInput at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h1, -⟩ := List.append_inj h12 (by simp only [bytesLE_length])
  have hd := flatMap_bytesLE_injective _ _ (by simp only [List.length_drop, hds]) h3
  have h0 := bytesLE_injective h1
  rcases ds with _ | ⟨a, t⟩
  · simp at hpos
  rcases ds' with _ | ⟨a', t'⟩
  · simp at hds
  simp only [List.getD_cons_zero] at h0
  simp only [List.drop_succ_cons, List.drop_zero] at hd
  rw [h0, hd]
section chain
variable (answers : Answers) (index coord child t : Nat)
theorem wctChainInputP_block4 (step : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainInputP index coord child t step pa pb pc v =
      block4 pa (WCT9.ftsChainHeaderP index coord child t step pb) pc v := rfl
theorem wctChainInput_block4' (step : Nat) (v : Digest) :
    WCT9.chainInput index coord child t step v = block4 0 (WCT9.ftsChainHeader index coord child t step) 0 v := by
  rw [← wctChainInputP_zero, wctChainInputP_block4]; rfl
theorem canonicalHeader_ftsChainHeaderP (step : Nat) (pb : BitVec 64) :
    Extract.canonicalHeader (bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step pb)) =
      Extract.canonicalHeader (bytesLE 16 (WCT9.ftsChainHeader index coord child t step)) := by
  unfold WCT9.ftsChainHeader WCT9.ftsChainHeaderP
  apply SigGolfCandidate.T3M.Extract.canonicalHeader_high_irrelevant
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (WCT9.ftsChainLow_lt ..) (by decide)),
    WCT9.ftsChainLow_byte0]
  omega
theorem wctChainP_eq_hashPath (start count : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainP index coord child t start count pa pb pc v =
      hashPath (fun step value => wctChainInputP index coord child t (start + step) pa pb pc value) count v :=
  foldlM_range'_eq_hashPath (fun step value => wctChainInputP index coord child t step pa pb pc value) start count v
theorem wctValue_succ (s : Nat) :
    evalWithAnswerFn answers (shortHash (WCT9.chainInput index coord child t s
      (Extract.wctValue answers index coord child t s))) = Extract.wctValue answers index coord child t (s + 1) := by
  unfold Extract.wctValue
  rw [WCT9.eval_chain_add answers index coord child t 0 s 1]
  simp [WCT9.chain]
theorem honestInput_wctChain (s : Nat) :
    Extract.honestInput answers (.wctChain index coord child t s) =
      WCT9.chainInput index coord child t s (Extract.wctValue answers index coord child t s) := by
  simp only [Extract.honestInput, Extract.pad64_wctChainInput]
theorem chain_extract (d : Nat) (hd : d ≤ 4) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6)
    (reaches : evalWithAnswerFn answers (wctChainP index coord child t (4 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 4) :
    (v = Extract.wctValue answers index coord child t (4 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d pa pb pc v), ∃ s, 4 - d ≤ s ∧ s < 4 ∧
        q = .inl (.inr (Extract.honestInput answers (.wctChain index coord child t s)))) ∨
    Extract.HitIn answers (queried answers (wctChainP index coord child t (4 - d) d pa pb pc v)) := by
  rw [wctChainP_eq_hashPath] at reaches ⊢
  have href : ∀ step, step < d →
      evalWithAnswerFn answers (shortHash (WCT9.chainInput index coord child t (4 - d + step)
        (Extract.wctValue answers index coord child t (4 - d + step)))) =
        Extract.wctValue answers index coord child t (4 - d + (step + 1)) := by
    intro step _
    rw [wctValue_succ, Nat.add_assoc]
  have hparse : ∀ step, step < d → ∀ value,
      pad64 (wctChainInputP index coord child t (4 - d + step) pa pb pc value) =
        pad64 (WCT9.chainInput index coord child t (4 - d + step)
          (Extract.wctValue answers index coord child t (4 - d + step))) →
      value = Extract.wctValue answers index coord child t (4 - d + step) ∧ (pa = 0 ∧ pb = 0 ∧ pc = 0) := by
    intro step _ value heq
    rw [wctChainInputP_block4, wctChainInput_block4', pad64_block4, pad64_block4] at heq
    obtain ⟨h0, hh, h1, hv⟩ := block4_injective heq
    have hpb := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) hh
    simp only [WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_high] at hpb
    exact ⟨hv, h0, hpb, h1⟩
  have h := hashPath_extract answers
    (fun step value => wctChainInputP index coord child t (4 - d + step) pa pb pc value)
    (fun step => WCT9.chainInput index coord child t (4 - d + step)
      (Extract.wctValue answers index coord child t (4 - d + step)))
    (fun step => Extract.wctValue answers index coord child t (4 - d + step))
    (fun _ => pa = 0 ∧ pb = 0 ∧ pc = 0) v d href hparse
    (by rw [show 4 - d + d = 4 by omega]; exact reaches)
  rcases h with ⟨hv, hgood⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by simpa using hv, fun hd0 => hgood 0 hd0, fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPath_honest answers
      (fun step value => wctChainInputP index coord child t (4 - d + step) pa pb pc value)
      (fun step => WCT9.chainInput index coord child t (4 - d + step)
        (Extract.wctValue answers index coord child t (4 - d + step)))
      (fun step => Extract.wctValue answers index coord child t (4 - d + step)) v d href
      (fun step hs => by
        obtain ⟨h0, hB, h1⟩ := hgood step hs
        simp only [h0, hB, h1, wctChainInputP_zero]) hv q hq
    refine ⟨4 - d + step, by omega, by omega, ?_⟩
    rw [honestInput_wctChain, Extract.pad64_wctChainInput]
  · right
    obtain ⟨hi, hc, hj, ht⟩ := hb
    refine ⟨.wctChain index coord child t (4 - d + step), _, ⟨hi, hc, hj, ht, by omega⟩, hq, ?_, ?_⟩
    · rw [honestInput_wctChain, ← Extract.pad64_wctChainInput]; exact hhit
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, pathInput]
      simp only [wctChainInputP_block4, pad64_block4, hdrBlock_block4W, Extract.Pos.hdr]
      exact canonicalHeader_ftsChainHeaderP index coord child t _ _
end chain
theorem leafHash_eq_shortHash (index coord child : Nat) (ends : List Digest) :
    WCT9.leafHash index coord child ends = shortHash (Extract.wctLeafInput index coord child ends) := by
  unfold WCT9.leafHash Extract.wctLeafInput Extract.listInput
  simp only [List.flatMap_cons, WCT9.bytesLE_zero16, List.append_assoc]
/-- The padded FTS leaf (campaign T8) as a list input: the pad is the first digest after the header. -/
theorem leafHashP_eq_shortHash (index coord child : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashP index coord child pad ends = shortHash (Extract.wctLeafInputP index coord child pad ends) := by
  unfold WCT9.leafHashP WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
  simp only [List.flatMap_cons, List.append_assoc]
/-- C1: the paired leaf of heap `heap` as a list input. -/
theorem leafHashH_eq_ftsHash (heap index coord child : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashH heap index coord child pad ends =
      WCT9.ftsHash heap (Extract.wctLeafInputP index coord child pad ends) := by
  unfold WCT9.leafHashH WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
  simp only [List.flatMap_cons, List.append_assoc]
/-- C1: an FTS hash (either half) makes the one query `pad64 input`. -/
theorem queried_ftsHash (answers : Answers) (heap : Nat) (input : HashInput) :
    queried answers (WCT9.ftsHash heap input) = [.inl (.inr (pad64 input))] := by
  unfold WCT9.ftsHash
  cases WCT9.ftsHighHeap heap <;> rfl
theorem childRoot_eq_out (answers : Answers) (index coord child : Nat) :
    WCT9.childRoot answers index coord child (Extract.ftsPrev answers index coord).1 =
      (answers (.inl (.inr (Extract.honestInput answers (.wctLeaf index coord child))))).extractLsb' 0 128 := by
  unfold WCT9.childRoot
  rw [leafHashP_eq_shortHash, eval_shortHash]
  rfl
theorem wctEnds_length (answers : Answers) (index coord child : Nat) :
    (Extract.wctEnds answers index coord child).length = 6 := by
  simp [Extract.wctEnds]
theorem listInput_inj {a a' : Digest} {hdr : BitVec 128} {r r' : List Digest} (hr : r.length = r'.length)
    (h : pad64 (Extract.listInput a hdr r) = pad64 (Extract.listInput a' hdr r')) : a = a' ∧ r = r' := by
  have hlen : (Extract.listInput a hdr r).length = (Extract.listInput a' hdr r').length := by
    simp only [Extract.listInput, List.length_append, bytesLE_length, flatMap_bytesLE_length, hr]
  have h := pad64_injective_of_length hlen h
  unfold Extract.listInput at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h1, -⟩ := List.append_inj h12 (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective h1, flatMap_bytesLE_injective _ _ hr h3⟩
theorem eq_of_getD_drop {ds ds' : List Digest} (hl : ds.length = ds'.length) (hpos : 0 < ds.length)
    (h0 : ds.getD 0 0 = ds'.getD 0 0) (h1 : ds.drop 1 = ds'.drop 1) : ds = ds' := by
  rcases ds with _ | ⟨a, t⟩
  · simp at hpos
  rcases ds' with _ | ⟨a', t'⟩
  · simp at hl
  simp only [List.getD_cons_zero] at h0
  simp only [List.drop_succ_cons, List.drop_zero] at h1
  rw [h0, h1]
/-- Leaf extraction with the leaf pad (campaign T8): a padded leaf query that reaches the honest child root is
either the honest leaf input (honest ends and zero pad) or a hit on the honest leaf position, exactly like the
chain and Merkle pads. -/
theorem leaf_extract (answers : Answers) (index coord child : Nat) (pad : Digest) (ends : List Digest)
    (hlen : ends.length = 6) (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128)
    (reaches : evalWithAnswerFn answers (WCT9.leafHashP index coord child pad ends) =
      WCT9.childRoot answers index coord child (Extract.ftsPrev answers index coord).1) :
    (ends = Extract.wctEnds answers index coord child ∧ pad = (Extract.ftsPrev answers index coord).1 ∧
      queried answers (WCT9.leafHashP index coord child pad ends) =
        [.inl (.inr (Extract.honestInput answers (.wctLeaf index coord child)))]) ∨
    Extract.HitIn answers (queried answers (WCT9.leafHashP index coord child pad ends)) := by
  rw [leafHashP_eq_shortHash] at reaches ⊢
  rw [queried_shortHash]
  by_cases heq : pad64 (Extract.wctLeafInputP index coord child pad ends) =
      Extract.honestInput answers (.wctLeaf index coord child)
  · left
    have hw : Extract.honestInput answers (.wctLeaf index coord child) =
        pad64 (Extract.wctLeafInputP index coord child (Extract.ftsPrev answers index coord).1
          (Extract.wctEnds answers index coord child)) := rfl
    obtain ⟨h0, hr⟩ := listInput_inj (by simp [hlen, wctEnds_length]) (heq.trans hw)
    obtain ⟨hpad, hrest⟩ := List.cons.inj hr
    exact ⟨eq_of_getD_drop (by rw [hlen, wctEnds_length]) (by omega) h0 hrest, hpad, by rw [heq]⟩
  · right
    refine ⟨.wctLeaf index coord child, _, hb, List.mem_singleton_self _, Extract.hashHitAt_of_low rfl ⟨heq, ?_⟩, ?_⟩
    · rw [eval_shortHash] at reaches
      rw [reaches, childRoot_eq_out]
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, Extract.hdrBlock_wctLeafInputP]
      rfl
theorem merkleInput_tree_reference_le (answers : Answers) (tag lay tree height completed leaf : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves completed levels)
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < completed) (hc : completed ≤ height) :
    evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInput
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rw [← nodeHash_eq_shortHash]
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2 ^ (step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub] using hp.symm
section merkle
variable (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat)
def mTarget (step : Nat) : Digest := treeValue (Extract.ftsLevels answers index c.val) step (j / 2 ^ step)
def mPath (l : Nat) : Digest := treeValue (Extract.ftsLevels answers index c.val) l (j / 2 ^ l ^^^ 1)
theorem ftsLevels_treeLevels :
    TreeLevels answers 3 (WCT9.nodeLayer c.val) index 7 (WCT9.coordLeaves answers index c) 5
      ((Extract.ftsLevels answers index c.val).take 6) :=
  WCT9.coordinate_treeLevels answers index c
theorem merkle_reference (hj : j < 128) : ∀ step, step < 5 →
    evalWithAnswerFn answers (shortHash (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j (mPath answers index c j)
      (fun _ => 0) step (mTarget answers index c j step))) = mTarget answers index c j (step + 1) := by
  intro step hstep
  have h := merkleInput_tree_reference_le answers 3 (WCT9.nodeLayer c.val) index 7 5 j _ _
    (ftsLevels_treeLevels answers index c) (by norm_num; omega) step hstep (by decide)
  have e1 : ∀ x, treeValue ((Extract.ftsLevels answers index c.val).take 6) step x =
      treeValue (Extract.ftsLevels answers index c.val) step x := fun x => WCT9.treeValue_take_lt _ (by omega) x
  have e2 : ∀ x, treeValue ((Extract.ftsLevels answers index c.val).take 6) (step + 1) x =
      treeValue (Extract.ftsLevels answers index c.val) (step + 1) x := fun x => WCT9.treeValue_take_lt _ (by omega) x
  unfold merkleInput at h ⊢
  simp only [e1, e2] at h
  exact h
theorem ftsLevels_leaf (hj : j < 128) :
    treeValue (Extract.ftsLevels answers index c.val) 0 j =
      WCT9.childRoot answers index c.val j (Extract.ftsPrev answers index c.val).1 := by
  unfold Extract.ftsLevels
  rw [WCT9.heapLevels_value _ 0 j (by omega) (by simpa using hj)]
  have hg := (WCT9.coordNodes_graph answers index c).2.1 (2 ^ (7 - 0) + j) (by norm_num) (by norm_num; omega)
  rw [show Extract.ftsNodes answers index c.val = WCT9.coordNodes answers index c from rfl, hg,
    show 2 ^ (7 - 0) + j - 128 = j by norm_num]
  unfold WCT9.coordLeaves WCT9.coordLeavesWith
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
theorem mTarget_zero (hj : j < 128) :
    mTarget answers index c j 0 = WCT9.childRoot answers index c.val j (Extract.ftsPrev answers index c.val).1 := by
  unfold mTarget
  rw [pow_zero, Nat.div_one, ftsLevels_leaf answers index c j hj]
theorem merkle_honestInput (step : Nat) (hs : step < 5) :
    pad64 (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j (mPath answers index c j) (fun _ => 0) step
      (mTarget answers index c j step)) =
      Extract.honestInput answers (.wctNode index c.val step (j / 2 ^ (step + 1))) := by
  unfold merkleInput mPath mTarget
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  simp only [Extract.honestInput, if_neg (show step ≠ 5 by omega)]
theorem hdrBlock_merkleInput (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    Extract.hdrBlock (pad64 (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j path pads step value)) =
      bytesLE 16 (nodeTweak 3 (WCT9.nodeLayer c.val) index (2 ^ (7 - step - 1) + j / 2 ^ (step + 1))) := by
  unfold merkleInput
  dsimp only
  split <;> rw [Extract.hdrBlock_nodeInputP]
theorem hdrBlock_merkleInputH (path pads : Nat → Digest) (hpads : Nat → BitVec 64) (step : Nat) (value : Digest) :
    Extract.hdrBlock (pad64 (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads step value)) =
      bytesLE 16 (withHigh (nodeTweak 3 (WCT9.nodeLayer c.val) index (2 ^ (7 - step - 1) + j / 2 ^ (step + 1)))
        (hpads step)) := by
  unfold merkleInputH nodeInputPH
  dsimp only
  split <;> rw [pad64_block4, hdrBlock_block4W]
theorem canonicalHeader_withHigh (t : BitVec 128) (hp : BitVec 64) :
    Extract.canonicalHeader (bytesLE 16 (withHigh t hp)) = Extract.canonicalHeader (bytesLE 16 t) := by
  unfold withHigh
  split
  · rename_i hm
    have ht : t = t.extractLsb' 64 64 ++ t.extractLsb' 0 64 := by
      have h := (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := t)).symm
      exact h
    conv_rhs => rw [ht]
    apply SigGolfCandidate.T3M.Extract.canonicalHeader_high_irrelevant
    rw [BitVec.extractLsb'_toNat]
    simp only [Nat.shiftRight_zero]
    have : t.toNat % 2 ^ 64 % 256 = t.toNat % 256 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num)]
    rw [show (2 : Nat) ^ 64 = 2 ^ 64 from rfl]
    omega
  · rfl

theorem merkle_extract (hidx : index < 2 ^ 31) (hj : j < 128) (path pads : Nat → Digest)
    (hpads : Nat → BitVec 64) (leaf : Digest)
    (reaches : evalWithAnswerFn answers (hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5
      leaf) = mTarget answers index c j 5) :
    (leaf = WCT9.childRoot answers index c.val j (Extract.ftsPrev answers index c.val).1 ∧
      (∀ l, l < 5 → path l = mPath answers index c j l ∧ pads l = 0) ∧
      ∀ q ∈ queried answers (hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5 leaf),
        ∃ l, l < 5 ∧ q = .inl (.inr (Extract.honestInput answers (.wctNode index c.val l (j / 2 ^ (l + 1)))))) ∨
    Extract.HitIn answers (queried answers
      (hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5 leaf)) := by
  have hR := merkle_reference answers index c j hj
  have h := merkleHPath_extract answers 3 (WCT9.nodeLayer c.val) index 7 j 5 path pads (mPath answers index c j)
    (mTarget answers index c j) hpads leaf hR reaches
  rcases h with ⟨h0, hall⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by rw [h0, mTarget_zero answers index c j hj], fun l hl => ⟨(hall l hl).1, (hall l hl).2.1⟩,
      fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPath_honest answers
      (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads)
      (fun step => merkleInput 3 (WCT9.nodeLayer c.val) index 7 j (mPath answers index c j) (fun _ => 0) step
        (mTarget answers index c j step))
      (mTarget answers index c j) leaf 5 hR
      (fun step hs => by
        rw [merkleInputH_ok _ _ _ _ _ _ _ _ _ _ (hall step hs).2.2]
        unfold merkleInput; rw [(hall step hs).1, (hall step hs).2.1]) h0 q hq
    exact ⟨step, hs, by rw [merkle_honestInput answers index c j step hs]⟩
  · right
    have hn : j / 2 ^ (step + 1) < 2 ^ (7 - step - 1) := by
      have := Correctness.div_pow_bound (node := j) (height := 7) (start := 0) (level := step + 1) (by omega)
        (by norm_num; omega)
      simpa [Nat.sub_sub] using this
    refine ⟨.wctNode index c.val step (j / 2 ^ (step + 1)), _, ⟨hidx, c.isLt, by omega, hn⟩, hq, ?_, ?_⟩
    · apply Extract.hashHitAt_of_low (by simp only [Extract.Pos.proj, if_neg (show step ≠ 5 by omega)])
      rw [← merkle_honestInput answers index c j step hstep]; exact hhit
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, pathInput, hdrBlock_merkleInputH, canonicalHeader_withHigh]
      rfl
theorem top_lt (hj : j < 128) : j / 2 ^ 6 < 2 := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr; norm_num; omega
theorem top_reference (hj : j < 128) :
    evalWithAnswerFn answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6)
      (treeValue (Extract.ftsLevels answers index c.val) 5 (2 * (j / 2 ^ 6))) (Extract.ftsPrev answers index c.val).2
      (treeValue (Extract.ftsLevels answers index c.val) 5 (2 * (j / 2 ^ 6) + 1))) = mTarget answers index c j 6 :=
  (WCT9.coordinate_top answers index c (j / 2 ^ 6) (top_lt j hj)).symm
theorem top_honestInput :
    pad64 (WCT9.wctTopInput c.val index (2 + j / 2 ^ 6)
      (treeValue (Extract.ftsLevels answers index c.val) 5 (2 * (j / 2 ^ 6))) (Extract.ftsPrev answers index c.val).2
      (treeValue (Extract.ftsLevels answers index c.val) 5 (2 * (j / 2 ^ 6) + 1))) =
      Extract.honestInput answers (.wctNode index c.val 5 (j / 2 ^ 6)) := by
  simp only [Extract.honestInput, if_pos rfl]
  rfl
theorem wctTopInput_block4 (coord index heap : Nat) (l p r : Digest) :
    WCT9.wctTopInput coord index heap l p r = block4 l (nodeTweak 3 (WCT9.nodeLayer coord) index heap) p r := rfl
/-- The top node of a coordinate (nested FTS r1-1): a high-half hash with the previous right top as pad. Either its
input is the honest one (honest level-5 value, honest sibling, honest previous right top) or it is a high-half hit. -/
theorem top_extract (hidx : index < 2 ^ 31) (hj : j < 128) (v other z : Digest)
    (reaches : evalWithAnswerFn answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6)
      (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)).1 z
      (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)).2) = mTarget answers index c j 6) :
    (v = mTarget answers index c j 5 ∧ other = mPath answers index c j 5 ∧ z = (Extract.ftsPrev answers index c.val).2 ∧
      queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6)
        (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)).1 z
        (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)).2) =
        [.inl (.inr (Extract.honestInput answers (.wctNode index c.val 5 (j / 2 ^ 6))))]) ∨
    Extract.HitIn answers (queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6)
      (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)).1 z
      (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)).2)) := by
  generalize hP : (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)) = P at reaches ⊢
  have hqry : queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6) P.1 z P.2) =
      [.inl (.inr (pad64 (WCT9.wctTopInput c.val index (2 + j / 2 ^ 6) P.1 z P.2)))] := rfl
  rw [hqry]
  by_cases heq : pad64 (WCT9.wctTopInput c.val index (2 + j / 2 ^ 6) P.1 z P.2) =
      Extract.honestInput answers (.wctNode index c.val 5 (j / 2 ^ 6))
  · left
    have heq' := heq
    rw [← top_honestInput answers index c j, wctTopInput_block4, wctTopInput_block4, pad64_block4,
      pad64_block4] at heq'
    obtain ⟨h1, -, hz, h2⟩ := block4_injective heq'
    have hs := Correctness.sibling_pair (fun n => treeValue (Extract.ftsLevels answers index c.val) 5 n) (j / 2 ^ 5)
    rw [Correctness.div_pow_succ] at hs
    have hPeq : (if j / 2 ^ 5 % 2 = 0 then (v, other) else (other, v)) =
        (if j / 2 ^ 5 % 2 = 0 then (mTarget answers index c j 5, mPath answers index c j 5)
          else (mPath answers index c j 5, mTarget answers index c j 5)) := by
      rw [hP]
      exact (Prod.ext h1 h2).trans hs.symm
    refine ⟨?_, ?_, hz, by rw [heq]⟩
    · by_cases hb : j / 2 ^ 5 % 2 = 0
      · simp only [hb, if_true, Prod.mk.injEq] at hPeq; exact hPeq.1
      · simp only [hb, if_false, Prod.mk.injEq] at hPeq; exact hPeq.2
    · by_cases hb : j / 2 ^ 5 % 2 = 0
      · simp only [hb, if_true, Prod.mk.injEq] at hPeq; exact hPeq.2
      · simp only [hb, if_false, Prod.mk.injEq] at hPeq; exact hPeq.1
  · right
    refine ⟨.wctNode index c.val 5 (j / 2 ^ 6), _, ⟨hidx, c.isLt, by norm_num, by have := top_lt j hj; norm_num at this ⊢; omega⟩,
      List.mem_singleton_self _, ⟨heq, ?_⟩, ?_⟩
    · simp only [Extract.Pos.proj, if_pos rfl]
      rw [← top_honestInput answers index c j]
      exact reaches.trans (top_reference answers index c j hj).symm
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, wctTopInput_block4, pad64_block4, hdrBlock_block4W]
      rfl
end merkle
theorem recoverCoordinateP_dec (N : HashOutput) (w : WBytes) (index : Nat) (c : WCT9.Coord) (prev : Digest × Digest) :
    recoverCoordinateP (witDecP N w).signature (padDecP N w) index N c prev =
      ((List.finRange 6).mapM (fun t => wctChainP index c.val (WCT9.child N c).val t.val
          (4 - WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit (WCT9.rank N c) t)
          (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
          (wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t))) >>= fun ends =>
        WCT9.leafHashP index c.val (WCT9.child N c).val prev.1 ends >>= fun leaf =>
          hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 (WCT9.child N c).val
            (wsib w c.val (WCT9.child N c).val) (wmpad w c.val (WCT9.child N c).val)
            (wmhpad w c.val (WCT9.child N c).val)) 5 leaf >>= fun v =>
          WCT9.wctTopHash c.val index (2 + (WCT9.child N c).val / 2 ^ 6)
            (if (WCT9.child N c).val / 2 ^ 5 % 2 = 0 then (v, wsib w c.val (WCT9.child N c).val 5)
              else (wsib w c.val (WCT9.child N c).val 5, v)).1 prev.2
            (if (WCT9.child N c).val / 2 ^ 5 % 2 = 0 then (v, wsib w c.val (WCT9.child N c).val 5)
              else (wsib w c.val (WCT9.child N c).val 5, v)).2 >>= fun top =>
          pure (if (WCT9.child N c).val / 2 ^ 6 % 2 = 0 then (top, wsib w c.val (WCT9.child N c).val 6)
            else (wsib w c.val (WCT9.child N c).val 6, top))) := by
  unfold recoverCoordinateP
  rfl
theorem pair_parse (levels : List (List Digest)) (j : Nat) (hj : j < 128) (top other : Digest)
    (h : (if j / 2 ^ 6 % 2 = 0 then (top, other) else (other, top)) =
      (treeValue levels 6 0, treeValue levels 6 1)) :
    top = treeValue levels 6 (j / 2 ^ 6) ∧ other = treeValue levels 6 (j / 2 ^ 6 ^^^ 1) := by
  have hq : j / 2 ^ 6 < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    norm_num; omega
  rcases (show j / 2 ^ 6 = 0 ∨ j / 2 ^ 6 = 1 by omega) with h0 | h0 <;> rw [h0] at h ⊢ <;>
    simp only [Nat.zero_mod, Nat.one_mod, if_true, if_false, one_ne_zero, Prod.mk.injEq] at h <;>
    exact ⟨by first | exact h.1 | exact h.2, by first | exact h.2 | exact h.1⟩
/-- One nested FTS coordinate: reaching the honest top pair forces the honest openings, pads and siblings and the
honest previous top pair `prev`, unless a query hits an honest position. -/
theorem coord_extract (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord) (prev : Digest × Digest)
    (reaches : evalWithAnswerFn answers
        (recoverCoordinateP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N c prev) =
      Extract.ftsPair answers (WCT9.digestIndex N) c.val) :
    ((∀ q ∈ queried answers (recoverCoordinateP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N c prev),
        HonestQ answers N c q) ∧ CoordHonest answers N w c ∧
        prev = Extract.ftsPrev answers (WCT9.digestIndex N) c.val) ∨
    Extract.HitIn answers
      (queried answers (recoverCoordinateP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N c prev)) := by
  have hidx : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  have hj := (WCT9.child N c).isLt
  rw [recoverCoordinateP_dec] at reaches ⊢
  rw [queried_bind, queried_bind, queried_bind, queried_bind]
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure] at reaches
  simp only [queried_pure, List.append_nil]
  generalize hE : evalWithAnswerFn answers ((List.finRange 6).mapM (fun t => wctChainP (WCT9.digestIndex N) c.val
      (WCT9.child N c).val t.val (4 - WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit (WCT9.rank N c) t)
      (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
      (wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t)))) = ends at reaches ⊢
  generalize hL : evalWithAnswerFn answers (WCT9.leafHashP (WCT9.digestIndex N) c.val (WCT9.child N c).val
    prev.1 ends) = leaf at reaches ⊢
  generalize hV : evalWithAnswerFn answers (hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) (WCT9.digestIndex N) 7
    (WCT9.child N c).val (wsib w c.val (WCT9.child N c).val) (wmpad w c.val (WCT9.child N c).val)
    (wmhpad w c.val (WCT9.child N c).val)) 5 leaf) = v at reaches ⊢
  generalize hT : evalWithAnswerFn answers (WCT9.wctTopHash c.val (WCT9.digestIndex N) (2 + (WCT9.child N c).val / 2 ^ 6)
    (if (WCT9.child N c).val / 2 ^ 5 % 2 = 0 then (v, wsib w c.val (WCT9.child N c).val 5)
      else (wsib w c.val (WCT9.child N c).val 5, v)).1 prev.2
    (if (WCT9.child N c).val / 2 ^ 5 % 2 = 0 then (v, wsib w c.val (WCT9.child N c).val 5)
      else (wsib w c.val (WCT9.child N c).val 5, v)).2) = top at reaches
  obtain ⟨htop, hsib6⟩ := pair_parse (Extract.ftsLevels answers (WCT9.digestIndex N) c.val) (WCT9.child N c).val hj
    top _ reaches
  rcases top_extract answers (WCT9.digestIndex N) c (WCT9.child N c).val hidx hj v _ prev.2
      (by rw [hT, htop]; rfl) with ⟨hv5, hother5, hz, hqT⟩ | hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hq)))
  rcases merkle_extract answers (WCT9.digestIndex N) c (WCT9.child N c).val hidx hj _ _ _ leaf
      (by rw [hV, hv5]) with ⟨hleaf, hsib, hqM⟩ | hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hq)))
  have hlen : ends.length = 6 := by rw [← hE, Correctness.eval_mapM]; simp
  rcases leaf_extract answers (WCT9.digestIndex N) c.val (WCT9.child N c).val prev.1 ends hlen
    ⟨hidx, c.isLt, hj⟩ (hL.trans hleaf) with ⟨hends, hpad, hqL⟩ | hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_left _ hq))
  have hend : ∀ t : Fin 6, evalWithAnswerFn answers (wctChainP (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val
      (4 - WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit (WCT9.rank N c) t)
      (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
      (wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t))) =
      Extract.wctValue answers (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val 4 := by
    intro t
    subst hE
    rw [Correctness.eval_mapM] at hends
    have h := List.getElem_of_eq hends (i := t.val) (by simp)
    simpa only [List.getElem_map, List.getElem_finRange, Extract.wctEnds, List.getElem_ofFn, Fin.cast_mk,
      Fin.eta, Fin.cast_eq_self] using h
  have hch := fun t : Fin 6 => chain_extract answers (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val
    (WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit_le_four _ t) _ _ _ _ ⟨hidx, c.isLt, hj, t.isLt⟩ (hend t)
  by_cases hhit : ∃ t : Fin 6, Extract.HitIn answers (queried answers (wctChainP (WCT9.digestIndex N) c.val
      (WCT9.child N c).val t.val (4 - WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit (WCT9.rank N c) t)
      (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
      (wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t))))
  · obtain ⟨t, ht⟩ := hhit
    exact Or.inr (ht.mono fun q hq => List.mem_append_left _
      (by rw [queried_mapM]; exact List.mem_flatMap.mpr ⟨t, List.mem_finRange t, hq⟩))
  · push Not at hhit
    have hgood := fun t => (hch t).resolve_right (hhit t)
    left
    refine ⟨fun q hq => ?_, ⟨fun t => ⟨(hgood t).1, fun hd => ?_⟩, fun l hl => ?_⟩, Prod.ext hpad hz⟩
    · rcases List.mem_append.mp hq with hq | hq
      · rw [queried_mapM] at hq
        obtain ⟨t, -, hq⟩ := List.mem_flatMap.mp hq
        obtain ⟨s, h1, h2, rfl⟩ := (hgood t).2.2 q hq
        exact Or.inl ⟨t, s, h1, h2, rfl⟩
      rcases List.mem_append.mp hq with hq | hq
      · rw [hqL] at hq
        rw [List.mem_singleton.mp hq]
        exact Or.inr (Or.inl rfl)
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨l, hl, rfl⟩ := hqM q hq
        exact Or.inr (Or.inr ⟨l, by omega, rfl⟩)
      · rw [hqT] at hq
        rw [List.mem_singleton.mp hq]
        exact Or.inr (Or.inr ⟨5, by omega, rfl⟩)
    · obtain ⟨h0, hB, h1⟩ := (hgood t).2.1 hd
      exact ⟨Prod.ext h0 h1, hB⟩
    · by_cases hl5 : l < 5
      · exact ⟨(hsib l hl5).1, fun _ => (hsib l hl5).2⟩
      · by_cases hl6 : l = 5
        · subst hl6
          exact ⟨hother5, fun h => absurd h (by decide)⟩
        · have hl6' : l = 6 := by omega
          subst hl6'
          exact ⟨hsib6, fun h => absurd h (by decide)⟩
/-! ### The nested coordinate fold -/
section fold
variable (answers : Answers) (start : Digest × Digest) (G : WCT9.Coord → Digest × Digest → M (Digest × Digest))
def nstep (pairs : List (Digest × Digest)) (coord : WCT9.Coord) : M (List (Digest × Digest)) := do
  let pair ← G coord (WCT9.prevPair start pairs)
  pure (pairs ++ [pair])
def npairs : Nat → List (Digest × Digest)
  | 0 => []
  | n + 1 => npairs n ++ [evalWithAnswerFn answers (G (Fin.ofNat 9 n) (WCT9.prevPair start (npairs n)))]
theorem npairs_length : ∀ n, (npairs answers start G n).length = n
  | 0 => rfl
  | n + 1 => by simp [npairs, npairs_length n]
theorem finRange_take_succ (n : Nat) (hn : n < 9) :
    (List.finRange 9).take (n + 1) = (List.finRange 9).take n ++ [Fin.ofNat 9 n] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hn)]
  simp only [List.getElem_finRange, Option.toList_some]
  congr 2
  ext; simp [Nat.mod_eq_of_lt hn]
theorem eval_nfold : ∀ n, n ≤ 9 →
    evalWithAnswerFn answers (((List.finRange 9).take n).foldlM (nstep start G) []) = npairs answers start G n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [finRange_take_succ n (by omega), List.foldlM_append, evalWithAnswerFn_bind, eval_nfold n (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, nstep, evalWithAnswerFn_bind, evalWithAnswerFn_pure, bind_pure]
    rfl
theorem queried_nfold : ∀ n, n ≤ 9 → ∀ q ∈ queried answers (((List.finRange 9).take n).foldlM (nstep start G) []),
    ∃ c : WCT9.Coord, c.val < n ∧ q ∈ queried answers (G c (WCT9.prevPair start (npairs answers start G c.val)))
  | 0, _, q, hq => by simp at hq
  | n + 1, hn, q, hq => by
    rw [finRange_take_succ n (by omega), List.foldlM_append, queried_bind, eval_nfold answers start G n (by omega)] at hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨c, hc, hq⟩ := queried_nfold n (by omega) q hq
      exact ⟨c, by omega, hq⟩
    · simp only [List.foldlM_cons, List.foldlM_nil, nstep, bind_pure, queried_bind, queried_pure,
        List.append_nil] at hq
      refine ⟨Fin.ofNat 9 n, by simp [Nat.mod_eq_of_lt (show n < 9 by omega)], ?_⟩
      simpa [Nat.mod_eq_of_lt (show n < 9 by omega)] using hq
theorem queried_nfold_sub : ∀ n, n ≤ 9 → ∀ c : WCT9.Coord, c.val < n →
    ∀ q ∈ queried answers (G c (WCT9.prevPair start (npairs answers start G c.val))),
      q ∈ queried answers (((List.finRange 9).take n).foldlM (nstep start G) [])
  | 0, _, c, hc, _, _ => absurd hc (by omega)
  | n + 1, hn, c, hc, q, hq => by
    rw [finRange_take_succ n (by omega), List.foldlM_append, queried_bind, eval_nfold answers start G n (by omega)]
    by_cases hcn : c.val < n
    · exact List.mem_append_left _ (queried_nfold_sub n (by omega) c hcn q hq)
    · have hce : c = Fin.ofNat 9 n := Fin.ext (by simp [Nat.mod_eq_of_lt (show n < 9 by omega)]; omega)
      subst hce
      apply List.mem_append_right
      simp only [List.foldlM_cons, List.foldlM_nil, nstep, bind_pure, queried_bind, queried_pure,
        List.append_nil]
      simpa [Nat.mod_eq_of_lt (show n < 9 by omega)] using hq
theorem npairs_prev_zero : WCT9.prevPair start (npairs answers start G 0) = start := rfl
theorem npairs_prev_succ (n : Nat) :
    WCT9.prevPair start (npairs answers start G (n + 1)) =
      evalWithAnswerFn answers (G (Fin.ofNat 9 n) (WCT9.prevPair start (npairs answers start G n))) := by
  show (npairs answers start G n ++
    [evalWithAnswerFn answers (G (Fin.ofNat 9 n) (WCT9.prevPair start (npairs answers start G n)))]).getLastD start = _
  simp
end fold
theorem recoverFtsP_nfold (sig : WCT9.Signature) (pads : Pads) (index : Nat) (N : HashOutput) :
    recoverFtsP sig pads index N =
      ((List.finRange 9).take 9).foldlM (nstep pads.start (recoverCoordinateP sig pads index N)) [] >>=
        fun ps => pure (WCT9.prevPair pads.start ps) := by
  rw [List.take_of_length_le (by simp)]
  rfl
theorem ftsPair_eq_prev (answers : Answers) (index c : Nat) :
    Extract.ftsPair answers index c = WCT9.ftsPrev answers index (c + 1) := by
  unfold Extract.ftsPair Extract.ftsLevels
  rw [WCT9.heapLevels_value _ 6 0 (by decide) (by decide), WCT9.heapLevels_value _ 6 1 (by decide) (by decide)]
  rfl
/-- Nested FTS extraction (r1-1): if the FTS output is the honest L3 message (coordinate 8's top pair), then by
descending induction every coordinate is honest and coordinate 0's pads are zero, unless a query hits. -/
theorem wct_extract (answers : Answers) (N : HashOutput) (w : WBytes) (_hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
      Extract.honestTop answers (WCT9.digestIndex N)) :
    Extract.HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N)) ∨
      WctHonest answers N w := by
  set idx := WCT9.digestIndex N with hidxDef
  set G := recoverCoordinateP (witDecP N w).signature (padDecP N w) idx N with hG
  set start := (padDecP N w).start with hstart
  have hrec := recoverFtsP_nfold (witDecP N w).signature (padDecP N w) idx N
  have hsub : ∀ c : WCT9.Coord, ∀ q ∈ queried answers (G c (WCT9.prevPair start (npairs answers start G c.val))),
      q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) idx N) := by
    intro c q hq
    rw [hrec, queried_bind]
    exact List.mem_append_left _ (queried_nfold_sub answers start G 9 le_rfl c c.isLt q hq)
  -- descending claim, stated upward on c
  have claim : ∀ c (hc : c < 9), evalWithAnswerFn answers (G ⟨c, hc⟩
        (WCT9.prevPair start (npairs answers start G c))) = Extract.ftsPair answers idx c →
      Extract.HitIn answers (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) idx N)) ∨
        ((∀ c' : WCT9.Coord, c'.val ≤ c →
          (∀ q ∈ queried answers (G c' (WCT9.prevPair start (npairs answers start G c'.val))), HonestQ answers N c' q) ∧
            CoordHonest answers N w c') ∧ start = (0, 0)) := by
    intro c
    induction c with
    | zero =>
      intro hc hreach
      rcases coord_extract answers N w ⟨0, hc⟩ _ hreach with ⟨hq, hcoh, hprev⟩ | hhit
      · right
        refine ⟨fun c' hc' => ?_, ?_⟩
        · have : c' = ⟨0, hc⟩ := Fin.ext (by show c'.val = 0; omega)
          subst this; exact ⟨hq, hcoh⟩
        · exact hprev
      · exact Or.inl (hhit.mono (hsub ⟨0, hc⟩))
    | succ c ih =>
      intro hc hreach
      rcases coord_extract answers N w ⟨c + 1, hc⟩ _ hreach with ⟨hq, hcoh, hprev⟩ | hhit
      · have hprev' : evalWithAnswerFn answers (G ⟨c, by omega⟩ (WCT9.prevPair start (npairs answers start G c))) =
            Extract.ftsPair answers idx c := by
          rw [ftsPair_eq_prev, ← show (Fin.ofNat 9 c : WCT9.Coord) = ⟨c, by omega⟩ from
            Fin.ext (by simp [Nat.mod_eq_of_lt (show c < 9 by omega)]), ← npairs_prev_succ]
          exact hprev
        rcases ih (by omega) hprev' with hhit | ⟨hall, hst⟩
        · exact Or.inl hhit
        · right
          refine ⟨fun c' hc' => ?_, hst⟩
          by_cases hle : c'.val ≤ c
          · exact hall c' hle
          · have : c' = ⟨c + 1, hc⟩ := Fin.ext (by show c'.val = c + 1; omega)
            subst this; exact ⟨hq, hcoh⟩
      · exact Or.inl (hhit.mono (hsub ⟨c + 1, hc⟩))
  have h8 : evalWithAnswerFn answers (G ⟨8, by decide⟩ (WCT9.prevPair start (npairs answers start G 8))) =
      Extract.ftsPair answers idx 8 := by
    have hn := npairs_prev_succ answers start G 8
    have := hrun
    rw [hrec, evalWithAnswerFn_bind, eval_nfold answers start G 9 le_rfl, evalWithAnswerFn_pure, hn] at this
    exact this
  rcases claim 8 (by decide) h8 with hhit | ⟨hall, hst⟩
  · exact Or.inl hhit
  · right
    refine ⟨fun q hq => ?_, fun c => (hall c (by omega)).2, by rw [← padDecP_start]; exact hst⟩
    rw [hrec, queried_bind] at hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨c, -, hq⟩ := queried_nfold answers start G 9 le_rfl q hq
      exact ⟨c, (hall c (by omega)).1 q hq⟩
    · simp at hq
def WctExtractSpecN (WctShaped : Answers → HashOutput → WBytes → Prop) : Prop :=
  ∀ (answers : Answers) (N : HashOutput) (w : WBytes), Shaped N w →
    evalWithAnswerFn answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
      Extract.honestTop answers (WCT9.digestIndex N) →
    Extract.HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N)) ∨
      WctShaped answers N w
theorem wctExtractSpecN_holds : WctExtractSpecN WctHonest := wct_extract
theorem eval_rejectTail (answers : Answers) (w : WBytes) (N : HashOutput) :
    evalWithAnswerFn answers (rejectTail w N) = false := by
  unfold rejectTail
  split
  · rfl
  · rw [evalWithAnswerFn_map]
theorem shaped_of_verifyP (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    (wdc w).toNat < WCT9.digestVerifyWindow ∧ Shaped (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w := by
  classical
  rw [verifyP_normal] at hv
  by_cases hdc : (wdc w).toNat ≥ WCT9.digestVerifyWindow
  · rw [if_pos hdc] at hv; simp at hv
  rw [if_neg hdc, evalWithAnswerFn_bind] at hv
  refine ⟨by omega, ?_⟩
  by_contra hS
  rw [if_neg hS, eval_rejectTail] at hv
  exact Bool.false_ne_true hv
theorem verifyP_walk_wct (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      evalWithAnswerFn answers (layersBC w (WCT9.digestIndex N) 4 (.pair (evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N)).1 (evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N)).2)) = some pk ∧
      (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
        q ∈ queried answers (verifyP m pk w)) ∧
      (∀ q ∈ queried answers (layersBC w (WCT9.digestIndex N) 4 (.pair (evalWithAnswerFn answers
          (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N)).1 (evalWithAnswerFn answers
          (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N)).2)),
        q ∈ queried answers (verifyP m pk w)) := by
  classical
  obtain ⟨hdcW, hS⟩ := shaped_of_verifyP answers m pk w hv
  have hdc := hdcW
  rw [verifyP_eq_tail] at hv ⊢
  have hD : digestP m w = some <$> digest (wrho w) m (wdc w) := by unfold digestP; rw [if_neg (by omega)]
  rw [hD, bind_map_left] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N at hv hS ⊢
  refine ⟨N, hdc, rfl, ?_, hS, ?_⟩
  · apply List.mem_append_left
    unfold digest publicHash
    rw [show (liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) : M HashOutput) =
      liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) >>= pure from (bind_pure _).symm,
      queried_query_bind]
    exact List.mem_cons_self
  dsimp only at hv ⊢
  try unfold verifyTailP at hv ⊢
  rw [if_neg (by simp [gateOk_of_admissible hS])] at hv ⊢
  rw [wctP_shaped N w hS, bind_map_left] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hR : evalWithAnswerFn answers
    (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) = root at hv ⊢
  dsimp only at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hL : evalWithAnswerFn answers (layersBC w (WCT9.digestIndex N) 4 (.pair root.1 root.2)) = ll at hv ⊢
  rcases ll with _ | root'
  · simp at hv
  simp only [evalWithAnswerFn_pure, beq_iff_eq] at hv
  subst hv
  exact ⟨rfl, fun q hq => List.mem_append_right _ (List.mem_append_left _ hq),
    fun q hq => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hq))⟩
theorem verifyP_wct_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (evalWithAnswerFn answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
          Extract.honestTop answers (WCT9.digestIndex N) →
        Extract.HitIn answers (queried answers (verifyP m pk w)) ∨ WctHonest answers N w) := by
  obtain ⟨N, hdc, hN, hdq, hS, -, hqF, -⟩ := verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, fun hroot => ?_⟩
  rcases wct_extract answers N w hS hroot with hhit | hhon
  · exact Or.inl (hhit.mono hqF)
  · exact Or.inr hhon
def LayersWalkSpec (LayerEvent : Answers → WBytes → Nat → List Spec.Domain → Prop)
    (LayersGood : Answers → WBytes → Nat → Prop) : Prop :=
  ∀ (answers : Answers) (w : WBytes) (index : Nat) (root : Digest × Digest) (qs : List Spec.Domain), index < 2 ^ 31 →
    (∀ q ∈ queried answers (layersBC w index 4 (.pair root.1 root.2)), q ∈ qs) →
    evalWithAnswerFn answers (layersBC w index 4 (.pair root.1 root.2)) = some (Extract.honestRoot answers 0 0) →
    LayerEvent answers w index qs ∨ (LayersGood answers w index ∧ root = Extract.honestTop answers index)
theorem verifyP_extract {LayerEvent : Answers → WBytes → Nat → List Spec.Domain → Prop}
    {LayersGood : Answers → WBytes → Nat → Prop} (hL : LayersWalkSpec LayerEvent LayersGood)
    (answers : Answers) (m : Message) (pk : Digest) (w : WBytes) (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (Extract.HitIn answers (queried answers (verifyP m pk w)) ∨
        LayerEvent answers w (WCT9.digestIndex N) (queried answers (verifyP m pk w)) ∨
        (LayersGood answers w (WCT9.digestIndex N) ∧ WctHonest answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hL answers w (WCT9.digestIndex N) _ _ (WCT9.digestIndex_lt N) hqL (hpk ▸ hlay) with hev | ⟨hgood, hroot⟩
  · exact Or.inr (Or.inl hev)
  rcases wct_extract answers N w hS hroot with hhit | hhon
  · exact Or.inl (hhit.mono hqF)
  · exact Or.inr (Or.inr ⟨hgood, hhon⟩)
end ClaudeWCT.W9.T3M.WctExtract


namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (nodeHashP sibOff)
open Correctness (Answers treeValue TreeLevels)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open ClaudeWCT.W9.T3M.WctExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem hdrBlock_honestInput (answers : Answers) (p : Pos) :
    hdrBlock (honestInput answers p) = bytesLE 16 p.hdr := by
  cases p with
  | wctLeaf index coord child => exact hdrBlock_wctLeafInputP ..
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.hdr]
      rw [wctTopInput_block4, pad64_block4, hdrBlock_block4W]
      rw [show 7-level-1=6-level by omega]
      rfl
  | chain lay tree lf i step => exact Extract.hdrBlock_honestInput answers (.chain lay tree lf i step)
  | leaf lay tree lf => exact Extract.hdrBlock_honestInput answers (.leaf lay tree lf)
  | node lay tree level nd => exact Extract.hdrBlock_honestInput answers (.node lay tree level nd)
  | forest index => exact Extract.hdrBlock_honestInput answers (.forest index)
  | wctChain index coord child t step => exact Extract.hdrBlock_honestInput answers (.wctChain index coord child t step)

section chain
variable (answers : Answers) (index coord child t : Nat)
theorem honestInput_wctChain (s : Nat) :
    honestInput answers (.wctChain index coord child t s) =
      WCT9.chainInput index coord child t s (Extract.wctValue answers index coord child t s) :=
  WctExtract.honestInput_wctChain answers index coord child t s
theorem chain_extract (d : Nat) (hd : d ≤ 4) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6)
    (reaches : evalWithAnswerFn answers (wctChainP index coord child t (4 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 4) :
    (v = Extract.wctValue answers index coord child t (4 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d pa pb pc v), ∃ s, 4 - d ≤ s ∧ s < 4 ∧
        q = .inl (.inr (honestInput answers (.wctChain index coord child t s)))) ∨
    HitIn answers (queried answers (wctChainP index coord child t (4 - d) d pa pb pc v)) := by
  rw [wctChainP_eq_hashPath] at reaches ⊢
  have href : ∀ step, step < d →
      evalWithAnswerFn answers (shortHash (WCT9.chainInput index coord child t (4 - d + step)
        (Extract.wctValue answers index coord child t (4 - d + step)))) =
        Extract.wctValue answers index coord child t (4 - d + (step + 1)) := by
    intro step _
    rw [wctValue_succ, Nat.add_assoc]
  have hparse : ∀ step, step < d → ∀ value,
      pad64 (wctChainInputP index coord child t (4 - d + step) pa pb pc value) =
        pad64 (WCT9.chainInput index coord child t (4 - d + step)
          (Extract.wctValue answers index coord child t (4 - d + step))) →
      value = Extract.wctValue answers index coord child t (4 - d + step) ∧ (pa = 0 ∧ pb = 0 ∧ pc = 0) := by
    intro step _ value heq
    rw [wctChainInputP_block4, wctChainInput_block4', pad64_block4, pad64_block4] at heq
    obtain ⟨h0, hh, h1, hv⟩ := block4_injective heq
    have hpb := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) hh
    simp only [WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_high] at hpb
    exact ⟨hv, h0, hpb, h1⟩
  have h := hashPath_extract answers
    (fun step value => wctChainInputP index coord child t (4 - d + step) pa pb pc value)
    (fun step => WCT9.chainInput index coord child t (4 - d + step)
      (Extract.wctValue answers index coord child t (4 - d + step)))
    (fun step => Extract.wctValue answers index coord child t (4 - d + step))
    (fun _ => pa = 0 ∧ pb = 0 ∧ pc = 0) v d href hparse
    (by rw [show 4 - d + d = 4 by omega]; exact reaches)
  rcases h with ⟨hv, hgood⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by simpa using hv, fun hd0 => hgood 0 hd0, fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPath_honest answers
      (fun step value => wctChainInputP index coord child t (4 - d + step) pa pb pc value)
      (fun step => WCT9.chainInput index coord child t (4 - d + step)
        (Extract.wctValue answers index coord child t (4 - d + step)))
      (fun step => Extract.wctValue answers index coord child t (4 - d + step)) v d href
      (fun step hs => by
        obtain ⟨h0, hB, h1⟩ := hgood step hs
        simp only [h0, hB, h1, wctChainInputP_zero]) hv q hq
    refine ⟨4 - d + step, by omega, by omega, ?_⟩
    rw [honestInput_wctChain, Extract.pad64_wctChainInput]
  · right
    obtain ⟨hi, hc, hj, ht⟩ := hb
    refine ⟨.wctChain index coord child t (4 - d + step), _, ⟨hi, hc, hj, ht, by omega⟩, hq, ?_, ?_⟩
    · rw [honestInput_wctChain, ← Extract.pad64_wctChainInput]; exact hhit
    · unfold Extract.SameHeader
      rw [hdrBlock_honestInput, pathInput]
      simp only [wctChainInputP_block4, pad64_block4, hdrBlock_block4W, Extract.Pos.hdr]
      exact canonicalHeader_ftsChainHeaderP index coord child t _ _
end chain

/-- C1: the honest leaf of raw child `child` is the half `proj` of its leaf position (heap `128 + physical`). -/
theorem childRoot_eq_out (answers : Answers) (index coord child : Nat) :
    WCT9.childRootH answers (128 + physical coord child) index coord child
        (pads answers index coord (physical coord child/64)).1 =
      proj (.wctLeaf index coord child) (answers (.inl (.inr (honestInput answers (.wctLeaf index coord child))))) := by
  unfold WCT9.childRootH
  rw [leafHashH_eq_ftsHash, WCT9.eval_ftsHash, proj_wctLeaf]
  rfl
theorem leaf_extract (answers : Answers) (index coord child : Nat) (pad : Digest) (ends : List Digest)
    (hlen : ends.length = 6) (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128)
    (reaches : evalWithAnswerFn answers (WCT9.leafHashH (128 + physical coord child) index coord child pad ends) =
      WCT9.childRootH answers (128 + physical coord child) index coord child
        (pads answers index coord (physical coord child/64)).1) :
    (ends = Extract.wctEnds answers index coord child ∧ pad = (pads answers index coord (physical coord child/64)).1 ∧
      queried answers (WCT9.leafHashH (128 + physical coord child) index coord child pad ends) =
        [.inl (.inr (honestInput answers (.wctLeaf index coord child)))]) ∨
    HitIn answers (queried answers (WCT9.leafHashH (128 + physical coord child) index coord child pad ends)) := by
  rw [leafHashH_eq_ftsHash] at reaches ⊢
  rw [queried_ftsHash]
  by_cases heq : pad64 (Extract.wctLeafInputP index coord child pad ends) =
      honestInput answers (.wctLeaf index coord child)
  · left
    have hw : honestInput answers (.wctLeaf index coord child) =
        pad64 (Extract.wctLeafInputP index coord child (pads answers index coord (physical coord child/64)).1
          (Extract.wctEnds answers index coord child)) := rfl
    obtain ⟨h0, hr⟩ := listInput_inj (by simp [hlen, wctEnds_length]) (heq.trans hw)
    obtain ⟨hpad, hrest⟩ := List.cons.inj hr
    exact ⟨eq_of_getD_drop (by rw [hlen, wctEnds_length]) (by omega) h0 hrest, hpad, by rw [heq]⟩
  · right
    refine ⟨.wctLeaf index coord child, _, hb, List.mem_singleton_self _, ⟨heq, ?_⟩, ?_⟩
    · rw [WCT9.eval_ftsHash] at reaches
      rw [proj_wctLeaf, reaches, childRoot_eq_out, proj_wctLeaf]
    · unfold Extract.SameHeader
      rw [hdrBlock_honestInput, Extract.hdrBlock_wctLeafInputP]
      rfl

#print axioms chain_extract
#print axioms leaf_extract
end ClaudeWCT.W9.T3M.Extract.Paired


namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (nodeHashP sibOff)
open Correctness (Answers treeValue TreeLevels)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open ClaudeWCT.W9.T3M.WctExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem node_block_extract (answers : Answers) (index coord level node : Nat)
    (left hdr pad right : Digest)
    (hb : Bounded (.wctNode index coord level node))
    (hs : canonicalHeader (bytesLE 16 hdr) =
      canonicalHeader (bytesLE 16 (Pos.hdr (.wctNode index coord level node))))
    (reaches : proj (.wctNode index coord level node)
        (answers (.inl (.inr (block4 left hdr pad right)))) =
      proj (.wctNode index coord level node)
        (answers (.inl (.inr (honestInput answers (.wctNode index coord level node)))))) :
    (left = (nodes answers index coord).getD (2*(2^(6-level)+node)) 0 ∧
      pad = (if level=4 then (pads answers index coord ((2^(6-level)+node)/2-2)).2 else 0) ∧
      right = (nodes answers index coord).getD (2*(2^(6-level)+node)+1) 0 ∧
      hdr = Pos.hdr (.wctNode index coord level node)) ∨
    HitIn answers [.inl (.inr (block4 left hdr pad right))] := by
  by_cases heq : block4 left hdr pad right = honestInput answers (.wctNode index coord level node)
  · left
    simp only [honestInput] at heq
    rw [wctTopInput_block4, pad64_block4] at heq
    obtain ⟨hl, hh, hp, hr⟩ := block4_injective heq
    refine ⟨hl, hp, hr, ?_⟩
    rw [hh]
    simp only [Pos.hdr, WCT9.wctNodeHeader, show 7-level-1=6-level by omega]
  · right
    refine ⟨.wctNode index coord level node, _, hb, List.mem_singleton_self _, ⟨heq,reaches⟩, ?_⟩
    unfold SameHeader
    rw [hdrBlock_block4W, hdrBlock_honestInput]
    exact hs

theorem nodes_shared (answers : Answers) (index coord : Nat) (hc : coord < 9) :
    nodes answers index coord = SharedForest.sharedNodes answers (first coord) index coord
      (pads answers index coord) := by
  by_cases he : coord = 8
  · subst coord
    simp only [nodes, pads, if_pos rfl]
    rfl
  · by_cases hf : first coord = true
    · have hp : coord % 2 = 0 := (of_decide_eq_true hf).2
      have hi : 2*(coord/2) = coord := by omega
      simp only [nodes, if_neg he, hf, if_true, SharedForest.firstNodes, hi]
      apply congrArg (SharedForest.sharedNodes answers true index coord)
      funext branch
      simp only [pads, if_neg he, hf, if_true]
    · have hff : first coord = false := Bool.eq_false_iff.mpr hf
      have hp : coord % 2 = 1 := by
        have hn : ¬(coord<8 ∧ coord%2=0) := by
          simpa only [first, decide_eq_true_eq] using hf
        omega
      have hi : 2*(coord/2)+1 = coord := by omega
      simp only [nodes, if_neg he, hff, Bool.false_eq_true, if_false,
        SharedForest.secondNodes, hi]
      apply congrArg (SharedForest.sharedNodes answers false index coord)
      funext branch
      simp only [pads, if_neg he, hff, Bool.false_eq_true, if_false]

theorem nodes_graph (answers : Answers) (index coord : Nat) (hc : coord < 9) :
    SharedForest.SharedHeapInv answers (first coord) index coord (pads answers index coord)
      (SharedForest.sharedLeaves answers (first coord) index coord (pads answers index coord))
      (128-SharedForest.heapCut (first coord)) (nodes answers index coord) := by
  rw [nodes_shared answers index coord hc]
  exact SharedForest.sharedNodes_graph ..

#print axioms chain_extract
#print axioms leaf_extract
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M.WctExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sharedNode_eq_nodeProgram (answers : Answers) (index coord level node : Nat)
    (hb : Bounded (.wctNode index coord level node)) (left right : Digest) :
    SharedForest.sharedNode (first coord) coord index (2^(6-level)+node)
      (pads answers index coord) left right =
    nodeProgram coord level node (WCT9.wctTopInput coord index (2^(6-level)+node) left
      (if level=4 then (pads answers index coord ((2^(6-level)+node)/2-2)).2 else 0) right) := by
  obtain ⟨⟨hi,hc,hl,hn⟩,hu⟩ := hb
  exact sharedNode_eq_nodeProgramP index coord level node hc hl
    (by simpa only [show 7-level-1=6-level by omega] using hn) hu (pads answers index coord) left right

theorem node_eval (answers : Answers) (index coord level node : Nat)
    (hb : Bounded (.wctNode index coord level node)) (left right : Digest) :
    evalWithAnswerFn answers (SharedForest.sharedNode (first coord) coord index
      (2^(6-level)+node) (pads answers index coord) left right) =
      proj (.wctNode index coord level node) (answers (.inl (.inr
        (pad64 (WCT9.wctTopInput coord index (2^(6-level)+node) left
          (if level=4 then (pads answers index coord ((2^(6-level)+node)/2-2)).2 else 0) right))))) := by
  rw [sharedNode_eq_nodeProgram answers index coord level node hb, eval_nodeProgram]

theorem node_reference (answers : Answers) (index coord level node : Nat)
    (hb : Bounded (.wctNode index coord level node)) :
    proj (.wctNode index coord level node)
      (answers (.inl (.inr (honestInput answers (.wctNode index coord level node))))) =
      (nodes answers index coord).getD (2^(6-level)+node) 0 := by
  have hb' := hb
  obtain ⟨⟨hi,hc,hl,hn⟩,hu⟩ := hb'
  have hg := nodes_graph answers index coord hc
  have hc' := SharedForest.heapCut_bounds (first coord)
  have hheap : SharedForest.heapCut (first coord)≤2^(6-level)+node ∧ 2^(6-level)+node<128 := by
    by_cases hf : first coord=true
    · have hl' := hu hf
      simp only [SharedForest.heapCut, hf, if_true]
      interval_cases level <;> norm_num at hn ⊢ <;> omega
    · have hff := Bool.eq_false_iff.mpr hf
      simp only [SharedForest.heapCut, hff, Bool.false_eq_true, if_false]
      interval_cases level <;> norm_num at hn ⊢ <;> omega
  have href := hg.2.2 (2^(6-level)+node) hheap.1 hheap.2 (by omega)
  rw [node_eval answers index coord level node hb] at href
  exact href.symm

theorem leaf_reference (answers : Answers) (index coord raw : Nat)
    (hc : coord<9) (hr : raw<128) :
    (nodes answers index coord).getD (128+physical coord raw) 0 =
      WCT9.childRootH answers (128 + physical coord raw) index coord raw
        (pads answers index coord (physical coord raw/64)).1 := by
  have hp := SharedForest.physicalChild_lt (first coord) raw hr
  change physical coord raw<128 at hp
  have hg := nodes_graph answers index coord hc
  have hl := hg.2.1 (128+physical coord raw) (by omega) (by omega)
  rw [Nat.add_sub_cancel_left, SharedForest.sharedLeaves,
    List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hp),
    List.getElem_ofFn] at hl
  rw [show SharedForest.rawChild (first coord) (physical coord raw) = raw from
    SharedForest.raw_physical_child (first coord) raw hr] at hl
  exact hl

#print axioms node_eval
#print axioms node_reference
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M.WctExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section chain
variable (answers : Answers) (index coord child t : Nat)
theorem chainV3_extract (d : Nat) (hd : d ≤ 4) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6)
    (reaches : evalWithAnswerFn answers (W9Machine.V3.chainP index coord child t (4 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 4) :
    (v = Extract.wctValue answers index coord child t (4 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (W9Machine.V3.chainP index coord child t (4 - d) d pa pb pc v), ∃ s, 4 - d ≤ s ∧ s < 4 ∧
        q = .inl (.inr (honestInput answers (.wctChain index coord child t s)))) ∨
    HitIn answers (queried answers (W9Machine.V3.chainP index coord child t (4 - d) d pa pb pc v)) := by
  have he := W9Machine.chainP_canonical index coord child t (4-d) d pa pc v pb
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (by omega)
  rw [he] at reaches ⊢
  exact chain_extract answers index coord child t d hd pa pb pc v hb reaches
end chain
/-- The verifier's leaf input is the source's padded leaf input. -/
theorem leafInputV3_eq (k index j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    W9Machine.V3.leafInput k index j pad ends = WCT9.leafInputP index k j pad ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5], _ =>
    simp only [W9Machine.V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, W9Machine.V3.leafFields, WCT9.leafInputP,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    rfl

/-- C1: the verifier's leaf half selector is the source's heap rule at heap `128 + physical`. -/
theorem hiOut_zero (p : Nat) : W9Machine.SharedV3.hiOut p 0 = WCT9.ftsHighHeap (128 + p) := by
  have hiff := WCT9.ftsHighHeap_iff (show 4 ≤ 128 + p by omega)
  unfold W9Machine.SharedV3.hiOut
  by_cases h : p % 2 = 0
  · rw [hiff.mpr ⟨by omega, by omega⟩]
    simp [h]
  · rw [show WCT9.ftsHighHeap (128 + p) = false from
      Bool.eq_false_iff.mpr (fun ht => h (by have := (hiff.mp ht).2; omega))]
    simp [h]

theorem hashSel_eq_ftsHash {hi : Bool} {heap : Nat} (h : hi = WCT9.ftsHighHeap heap) (input : HashInput) :
    W9Machine.SharedV3.hashSel hi input = WCT9.ftsHash heap input := by
  subst h
  unfold W9Machine.SharedV3.hashSel WCT9.ftsHash
  rfl

/-- C1: the verifier's leaf hash is the source's paired leaf of heap `128 + physical`. -/
theorem leafV3_eq (k index raw : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    W9Machine.SharedV3.hashSel (W9Machine.SharedV3.hiOut (W9Machine.SharedV3.physical k raw) 0)
        (W9Machine.V3.leafInput k index raw pad ends) =
      WCT9.leafHashH (128 + W9Machine.SharedV3.physical k raw) index k raw pad ends := by
  rw [hashSel_eq_ftsHash (hiOut_zero _), leafInputV3_eq k index raw pad ends h]
  rfl

theorem leafV3_extract (answers : Answers) (index coord child : Nat) (pad : Digest) (ends : List Digest)
    (hlen : ends.length = 6) (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128)
    (reaches : evalWithAnswerFn answers (W9Machine.SharedV3.hashSel
        (W9Machine.SharedV3.hiOut (W9Machine.SharedV3.physical coord child) 0)
        (W9Machine.V3.leafInput coord index child pad ends)) =
      WCT9.childRootH answers (128 + physical coord child) index coord child
        (pads answers index coord (physical coord child/64)).1) :
    (ends = Extract.wctEnds answers index coord child ∧ pad = (pads answers index coord (physical coord child/64)).1 ∧
      queried answers (W9Machine.SharedV3.hashSel (W9Machine.SharedV3.hiOut (W9Machine.SharedV3.physical coord child) 0)
          (W9Machine.V3.leafInput coord index child pad ends)) =
        [.inl (.inr (honestInput answers (.wctLeaf index coord child)))]) ∨
    HitIn answers (queried answers (W9Machine.SharedV3.hashSel
      (W9Machine.SharedV3.hiOut (W9Machine.SharedV3.physical coord child) 0)
      (W9Machine.V3.leafInput coord index child pad ends))) := by
  rw [leafV3_eq _ _ _ _ _ hlen] at reaches ⊢
  exact leaf_extract answers index coord child pad ends hlen hb reaches

theorem nodeV3_block_extract (answers : Answers) (index : Nat) (coord : Fin 9)
    (level node : Nat) (left pad right : Digest) (hp : BitVec 64)
    (hb : Bounded (.wctNode index coord.val level node))
    (reaches : proj (.wctNode index coord.val level node)
      (answers (.inl (.inr (pad64 (W9Machine.V3.nodeInput coord.val index
        (2^(6-level)+node) left hp pad right))))) =
      (nodes answers index coord.val).getD (2^(6-level)+node) 0) :
    (left = (nodes answers index coord.val).getD (2*(2^(6-level)+node)) 0 ∧
      pad = (if level=4 then (pads answers index coord.val ((2^(6-level)+node)/2-2)).2 else 0) ∧
      right = (nodes answers index coord.val).getD (2*(2^(6-level)+node)+1) 0 ∧
      W9Machine.V3.nodeHdr coord.val index (2^(6-level)+node) hp =
        Pos.hdr (.wctNode index coord.val level node)) ∨
    HitIn answers [.inl (.inr (pad64 (W9Machine.V3.nodeInput coord.val index
      (2^(6-level)+node) left hp pad right)))] := by
  have he : W9Machine.V3.nodeInput coord.val index (2^(6-level)+node) left hp pad right =
      block4 left (W9Machine.V3.nodeHdr coord.val index (2^(6-level)+node) hp) pad right := rfl
  rw [he, pad64_block4] at reaches ⊢
  apply node_block_extract answers index coord.val level node left _ pad right hb
  · rw [W9Drv.nodeHdr_canonical, canonicalHeader_withHigh]
    simp only [Pos.hdr, WCT9.wctNodeHeader, show 7-level-1=6-level by omega]
  · exact reaches.trans (node_reference answers index coord.val level node hb).symm

#print axioms chainV3_extract
#print axioms leafV3_extract
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def posHash (position : Pos) (input : HashInput) : M Digest := do
  pure (proj position (← publicHash input))

theorem queried_posHash (answers : Answers) (position : Pos) (input : HashInput) :
    queried answers (posHash position input) = [.inl (.inr (pad64 input))] := rfl

theorem eval_posHash (answers : Answers) (position : Pos) (input : HashInput) :
    evalWithAnswerFn answers (posHash position input) =
      proj position (answers (.inl (.inr (pad64 input)))) := rfl

def projectedPath (positions : Nat → Pos) (input : Nat → Digest → HashInput)
    (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => posHash (positions step) (input step value)) initial

def projectedValue (answers : Answers) (positions : Nat → Pos)
    (input : Nat → Digest → HashInput) (initial : Digest) (count : Nat) : Digest :=
  evalWithAnswerFn answers (projectedPath positions input count initial)

def projectedInput (answers : Answers) (positions : Nat → Pos)
    (input : Nat → Digest → HashInput) (initial : Digest) (step : Nat) : HashInput :=
  input step (projectedValue answers positions input initial step)

theorem projectedPath_succ (positions : Nat → Pos) (input : Nat → Digest → HashInput)
    (count : Nat) (initial : Digest) :
    projectedPath positions input (count+1) initial =
      (projectedPath positions input count initial >>= fun value => posHash (positions count) (input count value)) := by
  simp [projectedPath, List.range_succ, List.foldlM_append]

theorem projectedValue_succ (answers : Answers) (positions : Nat → Pos)
    (input : Nat → Digest → HashInput) (initial : Digest) (step : Nat) :
    projectedValue answers positions input initial (step+1) =
      evalWithAnswerFn answers (posHash (positions step) (projectedInput answers positions input initial step)) := by
  simp only [projectedValue, projectedPath_succ, evalWithAnswerFn_bind, projectedInput]

theorem projectedInput_queried (answers : Answers) (positions : Nat → Pos)
    (input : Nat → Digest → HashInput) (initial : Digest) (count step : Nat) (hstep : step<count) :
    .inl (.inr (pad64 (projectedInput answers positions input initial step))) ∈
      queried answers (projectedPath positions input count initial) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [projectedPath_succ, queried_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt|rfl
      · exact List.mem_append_left _ (ih hlt)
      · apply List.mem_append_right
        simp only [queried_posHash, List.mem_singleton]
        rfl

theorem projectedPath_extract (answers : Answers) (positions : Nat → Pos)
    (input : Nat → Digest → HashInput) (honest : Nat → HashInput)
    (target : Nat → Digest) (Good : Nat → Prop) (initial : Digest) (count : Nat)
    (reference : ∀ step, step<count →
      evalWithAnswerFn answers (posHash (positions step) (honest step)) = target (step+1))
    (parse : ∀ step, step<count → ∀ value,
      pad64 (input step value) = pad64 (honest step) → value=target step ∧ Good step)
    (reaches : projectedValue answers positions input initial count = target count) :
    (initial=target 0 ∧ ∀ step, step<count → Good step) ∨
    ∃ step, step<count ∧
      .inl (.inr (pad64 (projectedInput answers positions input initial step))) ∈
        queried answers (projectedPath positions input count initial) ∧
      HashHitAt answers (positions step) (pad64 (honest step))
        (pad64 (projectedInput answers positions input initial step)) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (projectedInput answers positions input initial count) = pad64 (honest count)
      · obtain ⟨hprev,hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit,hall⟩|⟨step,hstep,_,hhit⟩
        · left
          refine ⟨hinit,fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt|rfl
          · exact hall step hlt
          · exact hgood
        · exact Or.inr ⟨step,by omega, projectedInput_queried answers positions input initial _ _ (by omega),hhit⟩
      · right
        refine ⟨count,by omega,projectedInput_queried answers positions input initial _ _ (by omega),heq,?_⟩
        rw [projectedValue_succ] at reaches
        exact reaches.trans (reference count (by omega)).symm

theorem queried_projectedPath (answers : Answers) (positions : Nat→Pos)
    (input : Nat→Digest→HashInput) (initial : Digest) :
    ∀ count, queried answers (projectedPath positions input count initial) =
      (List.range count).map fun step =>
        .inl (.inr (pad64 (projectedInput answers positions input initial step)))
  | 0 => rfl
  | count+1 => by
      rw [projectedPath_succ, queried_bind, queried_projectedPath answers positions input initial count,
        List.range_succ, List.map_append, queried_posHash]
      rfl

theorem projectedValue_honest (answers : Answers) (positions : Nat→Pos)
    (input : Nat→Digest→HashInput) (honest : Nat→HashInput) (target : Nat→Digest)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step<count →
      evalWithAnswerFn answers (posHash (positions step) (honest step)) = target (step+1))
    (hin : ∀ step, step<count → pad64 (input step (target step)) = pad64 (honest step))
    (h0 : initial=target 0) :
    ∀ step, step≤count → projectedValue answers positions input initial step = target step := by
  intro step
  induction step with
  | zero => intro _; exact h0
  | succ step ih =>
      intro hs
      rw [projectedValue_succ, eval_posHash, projectedInput, ih (by omega), hin step (by omega)]
      exact reference step (by omega)

theorem queried_projectedPath_honest (answers : Answers) (positions : Nat→Pos)
    (input : Nat→Digest→HashInput) (honest : Nat→HashInput) (target : Nat→Digest)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step<count →
      evalWithAnswerFn answers (posHash (positions step) (honest step)) = target (step+1))
    (hin : ∀ step, step<count → pad64 (input step (target step)) = pad64 (honest step))
    (h0 : initial=target 0) :
    ∀ q ∈ queried answers (projectedPath positions input count initial),
      ∃ step, step<count ∧ q=.inl (.inr (pad64 (honest step))) := by
  intro q hq
  rw [queried_projectedPath] at hq
  obtain ⟨step,hs,rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  refine ⟨step,hs,?_⟩
  rw [projectedInput, projectedValue_honest answers positions input honest target initial count
    reference hin h0 step hs.le, hin step hs]

#print axioms projectedPath_extract
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def pathPos (index coord physical level : Nat) : Pos :=
  .wctNode index coord level (physical/2^(level+1))

theorem pathPos_bounded (index coord physical level : Nat)
    (hi : index<2^31) (hc : coord<9) (hp : physical<128)
    (hl : level≤SharedV3.lastLevel coord) : Bounded (pathPos index coord physical level) := by
  have hlast := SharedV3.lastLevel_cases coord
  have hl6 : level<6 := by omega
  refine ⟨⟨hi,hc,hl6,?_⟩,?_⟩
  · interval_cases level <;> norm_num <;> omega
  · intro hf
    have he : SharedV3.first coord=first coord := rfl
    simp only [SharedV3.lastLevel, he, hf, ↓reduceIte] at hl
    omega

theorem not_high_before_last (coord level : Nat) (hc : coord<9)
    (hl : level<SharedV3.lastLevel coord) : ¬highPosition coord level := by
  interval_cases coord <;>
    norm_num [SharedV3.lastLevel, SharedV3.first, highPosition] at hl ⊢ <;> omega

theorem high_last (coord : Nat) (hc : coord<9) :
    highPosition coord (SharedV3.lastLevel coord) ↔ coord≠8 := by
  interval_cases coord <;> decide

/-- C1: below the last level a path step hashes into the verifier's selected half. -/
theorem posHash_pathPos (index coord physical level : Nat) (hc : coord<9)
    (hl : level<SharedV3.lastLevel coord) (input : HashInput) :
    posHash (pathPos index coord physical level) input =
      SharedV3.hashSel (SharedV3.hiOut physical (level+1)) input := by
  have hp := not_high_before_last coord level hc hl
  have he : highNodeAt coord level (physical/2^(level+1)) ↔ SharedV3.hiOut physical (level+1) = true := by
    unfold highNodeAt SharedV3.hiOut
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact absurd h hp
      · exact ⟨by omega, h.2⟩
    · intro h
      exact Or.inr ⟨by omega, h.2⟩
  by_cases h : highNodeAt coord level (physical/2^(level+1))
  · have h' : SharedV3.hiOut physical (level+1) = true := he.mp h
    simp only [posHash, pathPos, proj, if_pos h, SharedV3.hashSel, h', ↓reduceIte]
    rfl
  · have h' : SharedV3.hiOut physical (level+1) = false := Bool.eq_false_iff.mpr (fun ht => h (he.mpr ht))
    simp only [posHash, pathPos, proj, if_neg h, SharedV3.hashSel, h', Bool.false_eq_true, ↓reduceIte]
    rfl

theorem childN_eq_projectedPath (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (ends : List Digest) (padL padR : Digest) :
    SharedV3.childN w index coord raw ends padL padR = (do
      let leaf ← SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) 0)
        (V3.leafInput coord.val index raw.val padL ends)
      projectedPath (pathPos index coord.val (SharedV3.physical coord.val raw.val))
        (fun level value => SharedV3.childInput w index coord.val
          (SharedV3.physical coord.val raw.val) padR value level)
        (SharedV3.lastLevel coord.val+1) leaf) := by
  unfold SharedV3.childN
  apply bind_congr
  intro leaf
  dsimp only
  have hf : projectedPath (pathPos index coord.val (SharedV3.physical coord.val raw.val))
      (fun level value => SharedV3.childInput w index coord.val
        (SharedV3.physical coord.val raw.val) padR value level)
      (SharedV3.lastLevel coord.val) leaf =
      (List.range (SharedV3.lastLevel coord.val)).foldlM
        (fun value level => SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level + 1))
          (SharedV3.childInput w index coord.val
            (SharedV3.physical coord.val raw.val) padR value level)) leaf := by
    unfold projectedPath
    apply foldlM_congr_mem
    intro value level hl
    exact posHash_pathPos index coord.val _ level coord.isLt (List.mem_range.mp hl) _
  rw [projectedPath_succ, hf]
  apply bind_congr
  intro value
  have hlast := SharedV3.lastLevel_cases coord.val
  by_cases hc : coord.val=8
  · have hp : ¬highNodeAt coord.val (SharedV3.lastLevel coord.val)
        (SharedV3.physical coord.val raw.val/2^(SharedV3.lastLevel coord.val+1)) := by
      rintro (h | h)
      · exact ((high_last _ coord.isLt).mp h) hc
      · omega
    simp only [if_pos hc, posHash, pathPos, proj, if_neg hp]
    rfl
  · have hp : highNodeAt coord.val (SharedV3.lastLevel coord.val)
        (SharedV3.physical coord.val raw.val/2^(SharedV3.lastLevel coord.val+1)) :=
      Or.inl ((high_last _ coord.isLt).mpr hc)
    simp only [if_neg hc, posHash, pathPos, proj, if_pos hp]
    rfl

def pathTarget (answers : Answers) (index coord physical level : Nat) : Digest :=
  (nodes answers index coord).getD ((128+physical)/2^level) 0

theorem pad64_honest_node (answers : Answers) (index coord level node : Nat) :
    pad64 (honestInput answers (.wctNode index coord level node)) =
      honestInput answers (.wctNode index coord level node) := by
  simp only [honestInput, WctExtract.wctTopInput_block4, pad64_block4]

theorem heap_path_pair6 (f : Nat→Digest) (physical level : Nat)
    (hp : physical<128) (hl : level<6) :
    (if physical/2^level%2=0 then
      (f ((128+physical)/2^level), f (((128+physical)/2^level)^^^1))
    else (f (((128+physical)/2^level)^^^1), f ((128+physical)/2^level))) =
    (f (2*((128+physical)/2^(level+1))),f (2*((128+physical)/2^(level+1))+1)) := by
  have hb : physical/2^level%2=(128+physical)/2^level%2 := by
    interval_cases level <;> norm_num <;> omega
  rw [hb, Correctness.sibling_pair f ((128+physical)/2^level)]
  have hd : (128+physical)/2^level/2=(128+physical)/2^(level+1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hd]

theorem childInput_sameHeader (w : SharedV3.WBytes) (answers : Answers)
    (index : Nat) (coord : Fin 9) (physical level : Nat) (hp : physical<128)
    (hl : level<6) (padR value : Digest) :
    SameHeader (pad64 (SharedV3.childInput w index coord.val physical padR value level))
      (honestInput answers (pathPos index coord.val physical level)) := by
  have hh := W9Drv.heap_eq physical level hp hl
  unfold SharedV3.childInput V3.nodeInput
  change SameHeader (pad64 (block4 _ (V3.nodeHdr _ _ _ _) _ _)) _
  unfold SameHeader
  rw [pad64_block4, WctExtract.hdrBlock_block4W, hdrBlock_honestInput,
    W9Drv.nodeHdr_canonical, WctExtract.canonicalHeader_withHigh]
  simp only [pathPos, Pos.hdr, WCT9.wctNodeHeader, hh,
    show 7-level-1=6-level by omega]

def PathStepGood (answers : Answers) (w : SharedV3.WBytes)
    (index coord physical : Nat) (padR : Digest) (level : Nat) : Prop :=
  pad64 (SharedV3.childInput w index coord physical padR
    (pathTarget answers index coord physical level) level) =
      honestInput answers (pathPos index coord physical level) ∧
  (level=4 → padR=(pads answers index coord (physical/64)).2)

theorem childInput_parse (answers : Answers) (w : SharedV3.WBytes)
    (index coord physical level : Nat) (hp : physical<128) (hl : level<6)
    (padR value : Digest)
    (heq : pad64 (SharedV3.childInput w index coord physical padR value level) =
      pad64 (honestInput answers (pathPos index coord physical level))) :
    value=pathTarget answers index coord physical level ∧
      PathStepGood answers w index coord physical padR level := by
  rw [pathPos, pad64_honest_node] at heq
  have he := heq
  simp only [SharedV3.childInput, V3.nodeInput] at he
  change pad64 (block4 _ (V3.nodeHdr _ _ _ _) _ _) = _ at he
  rw [pad64_block4] at he
  simp only [honestInput, WctExtract.wctTopInput_block4, pad64_block4] at he
  obtain ⟨hleft,hhdr,hpad,hright⟩ := block4_injective he
  have hh := W9Drv.heap_eq physical level hp hl
  have hs := heap_path_pair6 (fun j => (nodes answers index coord).getD j 0) physical level hp hl
  rw [hh] at hs
  have hv : value=pathTarget answers index coord physical level := by
    unfold pathTarget
    by_cases hb : physical/2^level%2=0
    · have href := congrArg Prod.fst hs
      simp only [if_pos hb, Prod.fst] at href hleft
      exact hleft.trans href.symm
    · have href := congrArg Prod.snd hs
      simp only [if_neg hb, Prod.snd] at href hright
      exact hright.trans href.symm
  refine ⟨hv,?_,?_⟩
  · rw [←hv]
    exact heq
  · intro h4
    subst level
    have he : (2^(6-4)+physical/2^(4+1))/2-2=physical/64 := by
      norm_num
      omega
    simpa only [↓reduceIte,he] using hpad

theorem path_extract (answers : Answers) (w : SharedV3.WBytes)
    (index : Nat) (coord : Fin 9) (physical count : Nat)
    (hi : index<2^31) (hp : physical<128)
    (hc : count≤SharedV3.lastLevel coord.val+1) (padR initial : Digest)
    (reaches : projectedValue answers (pathPos index coord.val physical)
      (fun level value => SharedV3.childInput w index coord.val physical padR value level)
      initial count = pathTarget answers index coord.val physical count) :
    (initial=pathTarget answers index coord.val physical 0 ∧
      ∀ level, level<count → PathStepGood answers w index coord.val physical padR level) ∨
    HitIn answers (queried answers (projectedPath (pathPos index coord.val physical)
      (fun level value => SharedV3.childInput w index coord.val physical padR value level) count initial)) := by
  have hlast := SharedV3.lastLevel_cases coord.val
  have hb (level : Nat) (hl : level<count) : Bounded (pathPos index coord.val physical level) :=
    pathPos_bounded index coord.val physical level hi coord.isLt hp (by omega)
  have h := projectedPath_extract answers (pathPos index coord.val physical)
    (fun level value => SharedV3.childInput w index coord.val physical padR value level)
    (fun level => honestInput answers (pathPos index coord.val physical level))
    (pathTarget answers index coord.val physical) (PathStepGood answers w index coord.val physical padR)
    initial count (by
      intro level hl
      rw [eval_posHash]
      change proj (.wctNode index coord.val level (physical/2^(level+1)))
        (answers (.inl (.inr (pad64 (honestInput answers
          (.wctNode index coord.val level (physical/2^(level+1)))))))) = _
      rw [pad64_honest_node, node_reference answers index coord.val level _ (hb level hl)]
      unfold pathTarget
      rw [W9Drv.heap_eq physical level hp (by omega)])
    (by
      intro level hl value he
      exact childInput_parse answers w index coord.val physical level hp (by omega) padR value he) reaches
  rcases h with hg|⟨level,hl,hq,hhit⟩
  · exact Or.inl hg
  · right
    refine ⟨pathPos index coord.val physical level,_,hb level hl,hq,?_,?_⟩
    · simpa only [pathPos, pad64_honest_node] using hhit
    · exact childInput_sameHeader w answers index coord physical level hp (by omega) padR _

#print axioms childN_eq_projectedPath
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def targetPair (answers : Answers) (index coord physical : Nat) : SharedForest.PairRoot :=
  if first coord then SharedForest.nodesPair (nodes answers index coord) (physical/64)
  else ((nodes answers index coord).getD 2 0,(nodes answers index coord).getD 3 0)

theorem ordered_target_pair (answers : Answers) (index coord physical : Nat) (hp : physical<128) :
    SharedV3.orderPair coord physical
      (pathTarget answers index coord physical (SharedV3.lastLevel coord+1))
      ((nodes answers index coord).getD
        (((128+physical)/2^(SharedV3.lastLevel coord+1))^^^1) 0) =
    targetPair answers index coord physical := by
  have hf : SharedV3.first coord=first coord := rfl
  by_cases hc : first coord=true
  · simpa only [SharedV3.orderPair, SharedV3.direction, SharedV3.lastLevel, hf, hc,
      if_true, targetPair, pathTarget, SharedForest.authAt, Nat.reduceAdd, Nat.reducePow] using
      SharedForest.ordered_branch_pair (nodes answers index coord) physical hp
  · have hff := Bool.eq_false_iff.mpr hc
    have he : (128+physical)/64=2+physical/64 := by omega
    simpa only [SharedV3.orderPair, SharedV3.direction, SharedV3.lastLevel, hf, hff,
      Bool.false_eq_true, if_false, targetPair, pathTarget, SharedForest.authAt,
      Nat.reduceAdd, Nat.reducePow, he] using
      SharedForest.ordered_top_pair (nodes answers index coord) physical hp

theorem targetPair_even (answers : Answers) (index pair physical : Nat) (hp : pair<4) :
    targetPair answers index (2*pair) physical =
      SharedForest.nodesPair (SharedForest.firstNodes answers index pair (pairPrev answers index pair))
        (physical/64) := by
  simp only [targetPair, first_even pair hp, ↓reduceIte, nodes_even answers index pair hp]

theorem targetPair_odd (answers : Answers) (index pair physical : Nat) :
    targetPair answers index (2*pair+1) physical = pairPrev answers index (pair+1) := by
  simp only [targetPair, first_odd pair, Bool.false_eq_true, ↓reduceIte, nodes_odd]
  rfl

theorem targetPair_singleton (answers : Answers) (index physical : Nat) :
    targetPair answers index 8 physical = SharedForest.forestCommitment answers index := by
  change ((nodes answers index 8).getD 2 0,(nodes answers index 8).getD 3 0) = _
  exact singleton_top answers index

theorem pair_handoff (answers : Answers) (index pair aPhysical bPhysical : Nat)
    (hp : pair<4) (hb : aPhysical/64=bPhysical/64) :
    pads answers index (2*pair+1) (bPhysical/64) = targetPair answers index (2*pair) aPhysical := by
  rw [pads_odd, targetPair_even answers index pair aPhysical hp, hb]

#print axioms ordered_target_pair
#print axioms pair_handoff
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research
open ClaudeWCT.W9.T3M.WctExtract
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def ChainOpenings (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (rank : Fin 666) : Prop :=
  ∀ t : Fin 6,
    V3.reveal w coord.val t.val (WCT9.digit rank t) =
      Extract.wctValue answers index coord.val raw.val t.val (4-WCT9.digit rank t) ∧
    (0<WCT9.digit rank t → V3.chainPadA w coord.val t.val=0 ∧
      V3.chainPadB w coord.val t.val=0 ∧ V3.chainPadC w coord.val t.val=0)

def CoordinateOpenings (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (rank : Fin 666) (prev : SharedV3.PairRoot) : Prop :=
  ChainOpenings answers w index coord raw rank ∧
  (∀ level, level≤SharedV3.lastLevel coord.val →
    PathStepGood answers w index coord.val (SharedV3.physical coord.val raw.val) prev.2 level) ∧
  SharedV3.topOther w coord.val (SharedV3.physical coord.val raw.val) =
    (nodes answers index coord.val).getD
      (((128+SharedV3.physical coord.val raw.val)/2^(SharedV3.lastLevel coord.val+1))^^^1) 0

theorem coordinate_extract (answers : Answers) (w : SharedV3.WBytes)
    (index : Nat) (coord : Fin 9) (raw : Fin 128) (rank : Fin 666)
    (hi : index<2^31) (prev : SharedV3.PairRoot)
    (reaches : evalWithAnswerFn answers (SharedV3.coordinate w index coord raw rank prev) =
      targetPair answers index coord.val (SharedV3.physical coord.val raw.val)) :
    (CoordinateOpenings answers w index coord raw rank prev ∧
      prev=pads answers index coord.val (SharedV3.physical coord.val raw.val/64)) ∨
    HitIn answers (queried answers (SharedV3.coordinate w index coord raw rank prev)) := by
  have hp := SharedV3.physical_lt coord.val raw.val raw.isLt
  have hlast := SharedV3.lastLevel_cases coord.val
  simp only [SharedV3.coordinate, childN_eq_projectedPath, bind_assoc] at reaches ⊢
  rw [queried_bind, queried_bind, queried_bind]
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure] at reaches
  simp only [queried_pure, List.append_nil]
  generalize hE : evalWithAnswerFn answers (V3.chainProgram w index coord raw rank) = ends at reaches ⊢
  generalize hL : evalWithAnswerFn answers
    (SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) 0)
      (V3.leafInput coord.val index raw.val prev.1 ends)) = leaf at reaches ⊢
  generalize hT : evalWithAnswerFn answers
    (projectedPath (pathPos index coord.val (SharedV3.physical coord.val raw.val))
      (fun level value => SharedV3.childInput w index coord.val
        (SharedV3.physical coord.val raw.val) prev.2 value level)
      (SharedV3.lastLevel coord.val+1) leaf) = top at reaches
  have hpairs := reaches.trans (ordered_target_pair answers index coord.val _ hp).symm
  have hout : top=pathTarget answers index coord.val (SharedV3.physical coord.val raw.val)
        (SharedV3.lastLevel coord.val+1) ∧
      SharedV3.topOther w coord.val (SharedV3.physical coord.val raw.val) =
        (nodes answers index coord.val).getD
          (((128+SharedV3.physical coord.val raw.val)/2^(SharedV3.lastLevel coord.val+1))^^^1) 0 := by
    by_cases hd : SharedV3.direction coord.val (SharedV3.physical coord.val raw.val)=0
    · simpa only [SharedV3.orderPair, if_pos hd, Prod.mk.injEq] using hpairs
    · have h := hpairs
      simp only [SharedV3.orderPair, if_neg hd, Prod.mk.injEq] at h
      exact ⟨h.2,h.1⟩
  rcases path_extract answers w index coord _ _ hi hp le_rfl prev.2 leaf
      (by rw [projectedValue, hT]; exact hout.1) with ⟨hleaf,hpath⟩|hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_right _ hq))
  have hlen : ends.length=6 := by
    rw [←hE, V3.chainProgram, Correctness.eval_mapM]
    simp
  have hleaf' : leaf=WCT9.childRootH answers (128 + SharedV3.physical coord.val raw.val) index coord.val raw.val
      (pads answers index coord.val (SharedV3.physical coord.val raw.val/64)).1 := by
    rw [hleaf]
    simpa only [pathTarget, pow_zero, Nat.div_one, SharedV3.physical, physical, SharedV3.first, first] using
      leaf_reference answers index coord.val raw.val coord.isLt raw.isLt
  rcases leafV3_extract answers index coord.val raw.val prev.1 ends hlen
      ⟨hi,coord.isLt,raw.isLt⟩ (hL.trans hleaf') with ⟨hends,hpad,hqL⟩|hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_left _ hq))
  have hend (t : Fin 6) : evalWithAnswerFn answers
      (V3.chainP index coord.val raw.val t.val (4-WCT9.digit rank t) (WCT9.digit rank t)
        (V3.chainPadA w coord.val t.val) (V3.chainPadB w coord.val t.val)
        (V3.chainPadC w coord.val t.val) (V3.reveal w coord.val t.val (WCT9.digit rank t))) =
      Extract.wctValue answers index coord.val raw.val t.val 4 := by
    rw [←hE, V3.chainProgram, Correctness.eval_mapM] at hends
    have h := List.getElem_of_eq hends (i:=t.val) (by simp)
    simpa only [List.getElem_map, List.getElem_finRange, Extract.wctEnds,
      List.getElem_ofFn, Fin.cast_mk, Fin.eta, Fin.cast_eq_self] using h
  have hchain (t : Fin 6) := chainV3_extract answers index coord.val raw.val t.val
    (WCT9.digit rank t) (WCT9.digit_le_four rank t) _ _ _ _
    ⟨hi,coord.isLt,raw.isLt,t.isLt⟩ (hend t)
  by_cases hhit : ∃ t : Fin 6, HitIn answers (queried answers
      (V3.chainP index coord.val raw.val t.val (4-WCT9.digit rank t) (WCT9.digit rank t)
        (V3.chainPadA w coord.val t.val) (V3.chainPadB w coord.val t.val)
        (V3.chainPadC w coord.val t.val) (V3.reveal w coord.val t.val (WCT9.digit rank t))))
  · obtain ⟨t,ht⟩ := hhit
    exact Or.inr (ht.mono fun q hq => List.mem_append_left _ (by
      rw [V3.chainProgram, queried_mapM]
      exact List.mem_flatMap.mpr ⟨t,List.mem_finRange t,hq⟩))
  · push Not at hhit
    have hgood (t : Fin 6) := (hchain t).resolve_right (hhit t)
    left
    refine ⟨⟨?_,?_,hout.2⟩,Prod.ext hpad ?_⟩
    · intro t
      exact ⟨(hgood t).1,(hgood t).2.1⟩
    · intro level hl
      exact hpath level (by omega)
    · exact (hpath 4 (by omega)).2 rfl

#print axioms coordinate_extract
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The shared selector fixes the same physical half in both coordinates of a pair.
The chain addresses below still contain the unrotated raw child. -/
def BranchCompatible (raw : Fin 9 → Fin 128) : Prop :=
  ∀ pair : Fin 4,
    SharedV3.physical (2*pair.val) (raw ⟨2*pair.val,by have := pair.isLt; omega⟩).val / 64 =
      SharedV3.physical (2*pair.val+1) (raw ⟨2*pair.val+1,by have := pair.isLt; omega⟩).val / 64

def canonicalBefore (answers : Answers) (index : Nat) (raw : Fin 9 → Fin 128)
    (coord : Fin 9) : SharedV3.PairRoot :=
  pads answers index coord.val (SharedV3.physical coord.val (raw coord).val / 64)

theorem canonicalBefore_zero (answers : Answers) (index : Nat) (raw : Fin 9 → Fin 128) :
    canonicalBefore answers index raw 0 = WCT9.ftsStart := by
  exact pads_even answers index 0 _ (by decide)

/-- B's two bindings recover the selected A pair; the next A starts at B's root. -/
theorem canonicalBefore_succ (answers : Answers) (index : Nat) (raw : Fin 9 → Fin 128)
    (shared : BranchCompatible raw) (c : Nat) (hc : c<8) :
    canonicalBefore answers index raw ⟨c+1,by omega⟩ =
      targetPair answers index c (SharedV3.physical c (raw ⟨c,by omega⟩).val) := by
  by_cases hlast : c=7
  · subst c
    change pads answers index 8 _ = targetPair answers index (2*3+1) _
    rw [targetPair_odd]
    rfl
  by_cases heven : c%2=0
  · let pair : Fin 4 := ⟨c/2,by omega⟩
    have he : c=2*pair.val := by dsimp [pair]; omega
    have h := pair_handoff answers index pair.val _ _ pair.isLt (shared pair)
    simpa only [canonicalBefore,←he] using h
  · let pair : Nat := c/2
    have he : c=2*pair+1 := by dsimp [pair]; omega
    have hp : pair+1<4 := by dsimp [pair]; omega
    have hn : c+1=2*(pair+1) := by omega
    have hpad (branch : Nat) : pads answers index (c+1) branch = pairPrev answers index (pair+1) := by
      rw [hn, pads_even answers index (pair+1) branch hp]
    have htarget (physical : Nat) : targetPair answers index c physical = pairPrev answers index (pair+1) := by
      rw [he, targetPair_odd]
    exact (hpad _).trans (htarget _).symm

section forestFold
variable (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666)

def forestPrefix (n : Nat) : M SharedV3.PairRoot :=
  ((List.finRange 9).take n).foldlM
    (fun prev k => SharedV3.coordinate w index k (raw k) (ranks k) prev)
    (SharedV3.initialPair w)

def forestState (n : Nat) : SharedV3.PairRoot :=
  evalWithAnswerFn answers (forestPrefix w index raw ranks n)

theorem forestPrefix_zero : forestPrefix w index raw ranks 0 = pure (SharedV3.initialPair w) := rfl

theorem forestState_zero : forestState answers w index raw ranks 0 = SharedV3.initialPair w := rfl

theorem forestPrefix_succ (n : Nat) (hn : n<9) :
    forestPrefix w index raw ranks (n+1) = (do
      let prev ← forestPrefix w index raw ranks n
      SharedV3.coordinate w index ⟨n,hn⟩ (raw ⟨n,hn⟩) (ranks ⟨n,hn⟩) prev) := by
  unfold forestPrefix
  rw [WctExtract.finRange_take_succ n hn, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  have he : (Fin.ofNat 9 n : Fin 9)=⟨n,hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
  rw [he]

theorem forestState_succ (n : Nat) (hn : n<9) :
    forestState answers w index raw ranks (n+1) =
      evalWithAnswerFn answers (SharedV3.coordinate w index ⟨n,hn⟩
        (raw ⟨n,hn⟩) (ranks ⟨n,hn⟩) (forestState answers w index raw ranks n)) := by
  rw [forestState, forestPrefix_succ w index raw ranks n hn, evalWithAnswerFn_bind]
  rfl

theorem forest_eq_prefix : SharedV3.forest w index raw ranks = forestPrefix w index raw ranks 9 := by
  unfold forestPrefix
  rw [List.take_of_length_le (by simp)]
  rfl

theorem forest_eq_prefix_drop (n : Nat) :
    SharedV3.forest w index raw ranks = (do
      let prev ← forestPrefix w index raw ranks n
      ((List.finRange 9).drop n).foldlM
        (fun prev k => SharedV3.coordinate w index k (raw k) (ranks k) prev) prev) := by
  have he := List.take_append_drop n (List.finRange 9)
  conv_lhs =>
    unfold SharedV3.forest
    rw [←he, List.foldlM_append]
  rfl

theorem forestPrefix_trace_sub (n : Nat) :
    ∀ q ∈ queried answers (forestPrefix w index raw ranks n),
      q ∈ queried answers (SharedV3.forest w index raw ranks) := by
  intro q hq
  rw [forest_eq_prefix_drop w index raw ranks n, queried_bind]
  exact List.mem_append_left _ hq

theorem coordinate_trace_sub (coord : Fin 9) :
    ∀ q ∈ queried answers (SharedV3.coordinate w index coord (raw coord) (ranks coord)
      (forestState answers w index raw ranks coord.val)),
      q ∈ queried answers (SharedV3.forest w index raw ranks) := by
  intro q hq
  apply forestPrefix_trace_sub answers w index raw ranks (coord.val+1) q
  rw [forestPrefix_succ w index raw ranks coord.val coord.isLt, queried_bind]
  exact List.mem_append_right _ hq
end forestFold

/-- The recovered canonical input of every coordinate, together with its opening facts.
Keeping the actual prefix equality makes trace membership available without rerunning the fold. -/
def ForestOpenings (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666) : Prop :=
  SharedV3.initialPair w = WCT9.ftsStart ∧
    ∀ coord : Fin 9,
      forestState answers w index raw ranks coord.val = canonicalBefore answers index raw coord ∧
      CoordinateOpenings answers w index coord (raw coord) (ranks coord)
        (canonicalBefore answers index raw coord)

/-- Reverse extraction starts at the singleton's two committed nodes and traverses B then A
for each pair. An inconsistent shared branch is excluded by the actual digest field relation. -/
theorem forest_extract (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666)
    (hi : index<2^31) (shared : BranchCompatible raw)
    (reaches : evalWithAnswerFn answers (SharedV3.forest w index raw ranks) =
      SharedForest.forestCommitment answers index) :
    ForestOpenings answers w index raw ranks ∨
      HitIn answers (queried answers (SharedV3.forest w index raw ranks)) := by
  have claim : ∀ c (hc : c<9),
      forestState answers w index raw ranks (c+1) =
        targetPair answers index c (SharedV3.physical c (raw ⟨c,hc⟩).val) →
      (SharedV3.initialPair w=WCT9.ftsStart ∧ ∀ k : Fin 9, k.val≤c →
        forestState answers w index raw ranks k.val=canonicalBefore answers index raw k ∧
        CoordinateOpenings answers w index k (raw k) (ranks k)
          (canonicalBefore answers index raw k)) ∨
        HitIn answers (queried answers (SharedV3.forest w index raw ranks)) := by
    intro c
    induction c with
    | zero =>
      intro hc hr
      rw [forestState_succ answers w index raw ranks 0 hc] at hr
      rcases coordinate_extract answers w index ⟨0,hc⟩ (raw ⟨0,hc⟩) (ranks ⟨0,hc⟩)
          hi (forestState answers w index raw ranks 0) hr with ⟨hop,hprev⟩|hhit
      · have hp : forestState answers w index raw ranks 0=canonicalBefore answers index raw 0 := hprev
        rw [hp] at hop
        left
        refine ⟨?_,fun k hk => ?_⟩
        · exact hp.trans (canonicalBefore_zero answers index raw)
        · have he : k=0 := Fin.ext (by omega)
          subst k
          exact ⟨hp,hop⟩
      · exact Or.inr (hhit.mono (coordinate_trace_sub answers w index raw ranks ⟨0,hc⟩))
    | succ c ih =>
      intro hc hr
      rw [forestState_succ answers w index raw ranks (c+1) hc] at hr
      rcases coordinate_extract answers w index ⟨c+1,hc⟩ (raw ⟨c+1,hc⟩) (ranks ⟨c+1,hc⟩)
          hi (forestState answers w index raw ranks (c+1)) hr with ⟨hop,hprev⟩|hhit
      · have hp : forestState answers w index raw ranks (c+1)=
            canonicalBefore answers index raw ⟨c+1,hc⟩ := hprev
        have hprior := hp.trans (canonicalBefore_succ answers index raw shared c (by omega))
        rcases ih (by omega) hprior with ⟨hstart,hall⟩|hhit
        · left
          refine ⟨hstart,fun k hk => ?_⟩
          by_cases hle : k.val≤c
          · exact hall k hle
          · have he : k=⟨c+1,hc⟩ := Fin.ext (by show k.val=c+1; omega)
            subst k
            rw [hp] at hop
            exact ⟨hp,hop⟩
        · exact Or.inr hhit
      · exact Or.inr (hhit.mono (coordinate_trace_sub answers w index raw ranks ⟨c+1,hc⟩))
  have hlast : forestState answers w index raw ranks 9 =
      targetPair answers index 8 (SharedV3.physical 8 (raw 8).val) := by
    rw [targetPair_singleton, forestState, ←forest_eq_prefix w index raw ranks]
    exact reaches
  rcases claim 8 (by decide) hlast with ⟨hstart,hall⟩|hhit
  · exact Or.inl ⟨hstart,fun k => hall k (by have := k.isLt; omega)⟩
  · exact Or.inr hhit

/-- Concrete output fields enforce the branch equality required by reverse extraction. -/
theorem branchCompatible_output (output : HashOutput) :
    BranchCompatible (SharedForest.rawChildFromOutput output) := by
  intro pair
  change (SharedForest.physicalChildFromOutput output
      ⟨2*pair.val,by have := pair.isLt; omega⟩).val/64 =
    (SharedForest.physicalChildFromOutput output
      ⟨2*pair.val+1,by have := pair.isLt; omega⟩).val/64
  rw [SharedForest.physicalFromOutput_first, SharedForest.physicalFromOutput_second]
  exact SharedForest.selected_branch ((SharedForest.forestSelectionFromOutput output).pairs pair)

#print axioms forest_extract
#print axioms branchCompatible_output
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research
open ClaudeWCT.W9.T3M.WctExtract
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Every nonempty chain emits its first public query, without any semantic assumption. -/
theorem chainV3_first_queried (answers : Answers) (index coord raw chain start count : Nat)
    (padA : Digest) (padB : BitVec 64) (padC value : Digest) (hcount : 0<count) :
    (.inl (.inr (pad64 (V3.chainInput index coord raw chain start padA padB padC value))) : Spec.Domain) ∈
      queried answers (V3.chainP index coord raw chain start count padA padB padC value) := by
  cases count with
  | zero => omega
  | succ n =>
    rw [V3.chainP, List.range'_succ, List.foldlM_cons, queried_bind]
    exact List.mem_append_left _ (by simp only [queried_shortHash, List.mem_singleton])

/-- Chain membership is independent of the incoming pair, which is consumed only after the chains. -/
theorem chainV3_coordinate_trace_sub (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (rank : Fin 666) (prev : SharedV3.PairRoot) (t : Fin 6) :
    ∀ q ∈ queried answers (V3.chainP index coord.val raw.val t.val
      (4-WCT9.digit rank t) (WCT9.digit rank t)
      (V3.chainPadA w coord.val t.val) (V3.chainPadB w coord.val t.val)
      (V3.chainPadC w coord.val t.val) (V3.reveal w coord.val t.val (WCT9.digit rank t))),
      q ∈ queried answers (SharedV3.coordinate w index coord raw rank prev) := by
  intro q hq
  rw [SharedV3.coordinate, queried_bind]
  apply List.mem_append_left
  rw [V3.chainProgram, queried_mapM]
  exact List.mem_flatMap.mpr ⟨t,List.mem_finRange t,hq⟩

/-- A successful no-collision opening exposes the canonical first input at the *raw* chain address. -/
theorem active_chain_queried (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (rank : Fin 666) (hi : index<2^31)
    (honest : ChainOpenings answers w index coord raw rank) (t : Fin 6)
    (active : 0<WCT9.digit rank t) (prev : SharedV3.PairRoot) :
    (.inl (.inr (honestInput answers
      (.wctChain index coord.val raw.val t.val (4-WCT9.digit rank t)))) : Spec.Domain) ∈
      queried answers (SharedV3.coordinate w index coord raw rank prev) := by
  have hd := WCT9.digit_le_four rank t
  obtain ⟨hvalue,hpads⟩ := honest t
  obtain ⟨hA,hB,hC⟩ := hpads active
  have hfirst := chainV3_first_queried answers index coord.val raw.val t.val
    (4-WCT9.digit rank t) (WCT9.digit rank t)
    (V3.chainPadA w coord.val t.val) (V3.chainPadB w coord.val t.val)
    (V3.chainPadC w coord.val t.val) (V3.reveal w coord.val t.val (WCT9.digit rank t)) active
  have hinput : pad64 (V3.chainInput index coord.val raw.val t.val (4-WCT9.digit rank t)
      (V3.chainPadA w coord.val t.val) (V3.chainPadB w coord.val t.val)
      (V3.chainPadC w coord.val t.val) (V3.reveal w coord.val t.val (WCT9.digit rank t))) =
      honestInput answers (.wctChain index coord.val raw.val t.val (4-WCT9.digit rank t)) := by
    rw [hA,hB,hC,hvalue,
      W9Machine.chainInput_canonical _ _ _ _ _ _ _ _ _ hi coord.isLt raw.isLt t.isLt (by omega),
      wctChainInputP_zero, Extract.pad64_wctChainInput,
      honestInput_wctChain]
  rw [hinput] at hfirst
  exact chainV3_coordinate_trace_sub answers w index coord raw rank prev t _ hfirst

/-- Export consumed by paired coverage: each active slot contributes its canonical start query.
No physical child permutation appears in this address. -/
theorem active_slot_queried (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666) (hi : index<2^31)
    (honest : ForestOpenings answers w index raw ranks)
    (coord : Fin 9) (t : Fin 6) (active : 0<WCT9.digit (ranks coord) t) :
    (.inl (.inr (honestInput answers
      (.wctChain index coord.val (raw coord).val t.val (4-WCT9.digit (ranks coord) t)))) : Spec.Domain) ∈
      queried answers (SharedV3.forest w index raw ranks) := by
  exact coordinate_trace_sub answers w index raw ranks coord _
    (active_chain_queried answers w index coord (raw coord) (ranks coord) hi
      (honest.2 coord).2.1 t active (forestState answers w index raw ranks coord.val))

/-- The extraction-facing corollary hides intermediate path facts from coverage clients. -/
theorem forest_extract_active (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666)
    (hi : index<2^31) (shared : BranchCompatible raw)
    (reaches : evalWithAnswerFn answers (SharedV3.forest w index raw ranks) =
      SharedForest.forestCommitment answers index) :
    HitIn answers (queried answers (SharedV3.forest w index raw ranks)) ∨
      (ForestOpenings answers w index raw ranks ∧
       ∀ (coord : Fin 9) (t : Fin 6), 0<WCT9.digit (ranks coord) t →
        (.inl (.inr (honestInput answers
          (.wctChain index coord.val (raw coord).val t.val (4-WCT9.digit (ranks coord) t)))) : Spec.Domain) ∈
          queried answers (SharedV3.forest w index raw ranks)) := by
  rcases forest_extract answers w index raw ranks hi shared reaches with hhon|hhit
  · exact Or.inr ⟨hhon,active_slot_queried answers w index raw ranks hi hhon⟩
  · exact Or.inl hhit

#print axioms active_slot_queried
#print axioms forest_extract_active
end ClaudeWCT.W9.T3M.Extract.Paired


namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3M.WctExtract
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PathStepGood.sibling_eq (answers : Answers) (w : SharedV3.WBytes)
    (index coord physical level : Nat) (hp : physical<128) (hl : level<6) (padR : Digest)
    (hg : PathStepGood answers w index coord physical padR level) :
    SharedV3.sibling w coord physical level =
      SharedForest.authAt (nodes answers index coord) physical level := by
  have he := hg.1
  simp only [SharedV3.childInput, V3.nodeInput] at he
  change pad64 (block4 _ (V3.nodeHdr _ _ _ _) _ _) = _ at he
  rw [pad64_block4] at he
  simp only [pathPos, honestInput, WctExtract.wctTopInput_block4, pad64_block4] at he
  obtain ⟨hleft,hhdr,hpad,hright⟩ := block4_injective he
  have hh := W9Drv.heap_eq physical level hp hl
  have hs := heap_path_pair6 (fun j => (nodes answers index coord).getD j 0) physical level hp hl
  rw [hh] at hs
  unfold SharedForest.authAt
  by_cases hb : physical/2^level%2=0
  · have href := congrArg Prod.snd hs
    simp only [if_pos hb, Prod.snd] at href hright
    exact hright.trans href.symm
  · have href := congrArg Prod.fst hs
    simp only [if_neg hb, Prod.fst] at href hleft
    exact hleft.trans href.symm
#print axioms PathStepGood.sibling_eq
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] sharedNodes firstNodes secondNodes expectedPairRoot chainValue

theorem buildForest_opening (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    (evalWithAnswerFn answers (buildForest index selected words)).1 =
      ⟨fun pair => expectedPairOpening answers index pair.val (selected.pairs pair)
        (words.first pair) (words.second pair) (pairPrev answers index pair.val),
       ⟨fun i => chainValue answers index 8 (rawChild false selected.singleton.val) words.singleton i,
        fun i => authAt (nodes answers index 8) selected.singleton.val i.val⟩⟩ := by
  have hfour : List.finRange 4 = [0,1,2,3] := by decide
  simp only [buildForest,hfour,List.foldlM_cons,List.foldlM_nil,
    evalWithAnswerFn_bind,evalWithAnswerFn_pure,buildPair_result,
    buildSingleton,buildSharedCoordinate_result]
  apply congrArg₂ ForestOpening.mk
  · funext pair
    fin_cases pair <;> rfl
  · apply congrArg₂ SingletonOpening.mk
    · funext i
      fin_cases i <;> rfl
    · rfl
#print axioms buildForest_opening
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] sharedNodes firstNodes secondNodes expectedPairRoot chainValue

theorem raw_selected_first (output : HashOutput) (pair : Fin 4) :
    rawChild true (firstChild ((forestSelectionFromOutput output).pairs pair)).val =
      (rawChildFromOutput output ⟨2*pair.val,by have := pair.isLt;omega⟩).val := by
  rw [← physicalFromOutput_first output pair]
  change rawChild true (physicalChild (firstCoord (2*pair.val)) _)=_
  have hf : firstCoord (2*pair.val)=true := by simp [firstCoord];omega
  rw [hf]
  exact raw_physical_child true _ (rawChildFromOutput output _).isLt

theorem raw_selected_second (output : HashOutput) (pair : Fin 4) :
    rawChild false (secondChild ((forestSelectionFromOutput output).pairs pair)).val =
      (rawChildFromOutput output ⟨2*pair.val+1,by have := pair.isLt;omega⟩).val := by
  rw [← physicalFromOutput_second output pair]
  change rawChild false (physicalChild (firstCoord (2*pair.val+1)) _)=_
  have hf : firstCoord (2*pair.val+1)=false := by simp [firstCoord]
  rw [hf]
  exact raw_physical_child false _ (rawChildFromOutput output _).isLt

theorem raw_selected_singleton (output : HashOutput) :
    rawChild false (forestSelectionFromOutput output).singleton.val =
      (rawChildFromOutput output 8).val := by
  exact raw_physical_child false _ (rawChildFromOutput output 8).isLt

theorem buildForest_coordinateValues (answers : Answers) (output : HashOutput) (coord : Fin 9) (i : Fin 6) :
    T3M.Paired.coordinateValues (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 coord i =
      chainValue answers (digestIndex output) coord.val (rawChildFromOutput output coord).val
        (forestRank output coord.val) i := by
  rw [buildForest_opening]
  fin_cases coord <;> fin_cases i <;>
    simp [T3M.Paired.coordinateValues,expectedPairOpening,forestWordsFromOutput,
      raw_selected_first,raw_selected_second,raw_selected_singleton,List.getD_eq_getElem]

theorem buildForest_coordinatePath (answers : Answers) (output : HashOutput) (coord : Fin 9)
    (level : Nat) (hl : level < (if coord.val < 8 ∧ coord.val % 2 = 0 then 6 else 7)) :
    T3M.Paired.coordinatePath (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 coord level =
      authAt (nodes answers (digestIndex output) coord.val)
        (W9Machine.SharedV3.physical coord.val (rawChildFromOutput output coord).val) level := by
  rw [buildForest_opening]
  fin_cases coord
  · change authAt (firstNodes answers (digestIndex output) 0 (pairPrev answers (digestIndex output) 0))
      (firstChild ((forestSelectionFromOutput output).pairs 0)).val (level % 6) = _
    have hb : level < 6 := hl
    have hp := congrArg Fin.val (physicalFromOutput_first output 0)
    change W9Machine.SharedV3.physical 0 (rawChildFromOutput output 0).val =
      (firstChild ((forestSelectionFromOutput output).pairs 0)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (secondNodes answers (digestIndex output) 0 (pairPrev answers (digestIndex output) 0))
      (secondChild ((forestSelectionFromOutput output).pairs 0)).val (level % 7) = _
    have hb : level < 7 := hl
    have hp := congrArg Fin.val (physicalFromOutput_second output 0)
    change W9Machine.SharedV3.physical 1 (rawChildFromOutput output 1).val =
      (secondChild ((forestSelectionFromOutput output).pairs 0)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (firstNodes answers (digestIndex output) 1 (pairPrev answers (digestIndex output) 1))
      (firstChild ((forestSelectionFromOutput output).pairs 1)).val (level % 6) = _
    have hb : level < 6 := hl
    have hp := congrArg Fin.val (physicalFromOutput_first output 1)
    change W9Machine.SharedV3.physical 2 (rawChildFromOutput output 2).val =
      (firstChild ((forestSelectionFromOutput output).pairs 1)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (secondNodes answers (digestIndex output) 1 (pairPrev answers (digestIndex output) 1))
      (secondChild ((forestSelectionFromOutput output).pairs 1)).val (level % 7) = _
    have hb : level < 7 := hl
    have hp := congrArg Fin.val (physicalFromOutput_second output 1)
    change W9Machine.SharedV3.physical 3 (rawChildFromOutput output 3).val =
      (secondChild ((forestSelectionFromOutput output).pairs 1)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (firstNodes answers (digestIndex output) 2 (pairPrev answers (digestIndex output) 2))
      (firstChild ((forestSelectionFromOutput output).pairs 2)).val (level % 6) = _
    have hb : level < 6 := hl
    have hp := congrArg Fin.val (physicalFromOutput_first output 2)
    change W9Machine.SharedV3.physical 4 (rawChildFromOutput output 4).val =
      (firstChild ((forestSelectionFromOutput output).pairs 2)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (secondNodes answers (digestIndex output) 2 (pairPrev answers (digestIndex output) 2))
      (secondChild ((forestSelectionFromOutput output).pairs 2)).val (level % 7) = _
    have hb : level < 7 := hl
    have hp := congrArg Fin.val (physicalFromOutput_second output 2)
    change W9Machine.SharedV3.physical 5 (rawChildFromOutput output 5).val =
      (secondChild ((forestSelectionFromOutput output).pairs 2)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (firstNodes answers (digestIndex output) 3 (pairPrev answers (digestIndex output) 3))
      (firstChild ((forestSelectionFromOutput output).pairs 3)).val (level % 6) = _
    have hb : level < 6 := hl
    have hp := congrArg Fin.val (physicalFromOutput_first output 3)
    change W9Machine.SharedV3.physical 6 (rawChildFromOutput output 6).val =
      (firstChild ((forestSelectionFromOutput output).pairs 3)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (secondNodes answers (digestIndex output) 3 (pairPrev answers (digestIndex output) 3))
      (secondChild ((forestSelectionFromOutput output).pairs 3)).val (level % 7) = _
    have hb : level < 7 := hl
    have hp := congrArg Fin.val (physicalFromOutput_second output 3)
    change W9Machine.SharedV3.physical 7 (rawChildFromOutput output 7).val =
      (secondChild ((forestSelectionFromOutput output).pairs 3)).val at hp
    rw [Nat.mod_eq_of_lt hb, ← hp]
    rfl
  · change authAt (nodes answers (digestIndex output) 8)
      (forestSelectionFromOutput output).singleton.val (level % 7) = _
    have hb : level < 7 := hl
    rw [Nat.mod_eq_of_lt hb]
    rfl
#print axioms buildForest_coordinateValues
#print axioms buildForest_coordinatePath
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M.WctExtract W9Machine
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def FtsPosition : Pos → Prop
  | .wctChain .. | .wctLeaf .. | .wctNode .. => True
  | _ => False

def FtsQuery : Spec.Domain → Prop
  | .inl (.inr input) => ∃ p, FtsPosition p ∧ p.Bounded ∧ posOf input=some p
  | _ => False

def FtsQueries (answers : Answers) {α : Type} (program : M α) : Prop :=
  ∀ q ∈ queried answers program, FtsQuery q

theorem FtsQueries.pure' (answers : Answers) {α : Type} (value : α) :
    FtsQueries answers (pure value : M α) := by
  intro q hq;simpa only [queried_pure,List.not_mem_nil] using hq

theorem FtsQueries.bind (answers : Answers) {α β : Type} {p : M α} {f : α → M β}
    (hp:FtsQueries answers p) (hf:FtsQueries answers (f (evalWithAnswerFn answers p))) :
    FtsQueries answers (p >>= f) := by
  intro q hq
  rw [queried_bind,List.mem_append] at hq
  exact hq.elim (hp q) (hf q)

theorem FtsQueries.fold (answers : Answers) {α β : Type} (items : List α)
    (f : β → α → M β) (hf:∀ x ∈ items,∀ state,FtsQueries answers (f state x)) (initial : β) :
    FtsQueries answers (items.foldlM f initial) := by
  induction items generalizing initial with
  | nil=>exact FtsQueries.pure' answers _
  | cons x xs ih=>
    rw [List.foldlM_cons]
    exact FtsQueries.bind answers (hf x (List.mem_cons_self ..) initial)
      (ih (fun y hy=>hf y (List.mem_cons_of_mem x hy)) _)

theorem posOf_sameHeader (answers : Answers) (p : Pos) (hp : p.Bounded) (input : HashInput)
    (hs : SameHeader input (honestInput answers p)) : posOf input=some p := by
  apply posOf_key_eq hp
  rw [hs,hdrBlock_honestInput,Pos.canonicalHeader_eq hp]

theorem posOf_padded_chain (index coord raw t step : Nat)
    (pa : Digest) (pb : BitVec 64) (pc value : Digest)
    (hb : (Pos.wctChain index coord raw t step).Bounded) :
    posOf (pad64 (wctChainInputP index coord raw t step pa pb pc value)) =
      some (.wctChain index coord raw t step) := by
  apply posOf_key_eq hb
  rw [wctChainInputP_block4,pad64_block4,hdrBlock_block4W,
    canonicalHeader_ftsChainHeaderP]
  simpa only [Pos.hdr] using (Pos.canonicalHeader_eq hb)

theorem chainV3_ftsQueries (answers : Answers) (index coord raw t start count : Nat)
    (pa : Digest) (pb : BitVec 64) (pc value : Digest)
    (hi : index<2^31) (hc : coord<9) (hr : raw<128) (ht : t<6) (hn : start+count≤4) :
    FtsQueries answers (V3.chainP index coord raw t start count pa pb pc value) := by
  have he := W9Machine.chainP_canonical index coord raw t start count pa pc value pb hi hc hr ht hn
  rw [he,wctChainP_eq_hashPath]
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨step,hstep,rfl⟩:=List.mem_map.mp hq
  have hs : step<count := List.mem_range.mp hstep
  have hb : (Pos.wctChain index coord raw t (start+step)).Bounded := ⟨hi,hc,hr,ht,by omega⟩
  refine ⟨.wctChain index coord raw t (start+step),trivial,hb,?_⟩
  exact posOf_padded_chain index coord raw t (start+step) pa pb pc _ hb

theorem chainProgram_ftsQueries (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (rank : Fin 666) (hi:index<2^31) :
    FtsQueries answers (V3.chainProgram w index coord raw rank) := by
  intro q hq
  rw [V3.chainProgram,queried_mapM] at hq
  obtain ⟨t,ht,hq⟩:=List.mem_flatMap.mp hq
  exact chainV3_ftsQueries answers _ _ _ _ _ _ _ _ _ _ hi coord.isLt raw.isLt t.isLt
    (by have:=ClaudeWCT.WCT9.digit_le_four rank t;omega) q hq

theorem leafV3_ftsQueries (answers : Answers) (index : Nat) (coord : Fin 9) (raw : Fin 128)
    (pad : Digest) (ends : List Digest) (hlen:ends.length=6) (hi:index<2^31) :
    FtsQueries answers (SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) 0)
      (V3.leafInput coord.val index raw.val pad ends)) := by
  rw [leafV3_eq _ _ _ _ _ hlen,leafHashH_eq_ftsHash]
  intro q hq
  rw [queried_ftsHash,List.mem_singleton] at hq
  subst hq
  have hb : (Pos.wctLeaf index coord.val raw.val).Bounded := ⟨hi,coord.isLt,raw.isLt⟩
  refine ⟨.wctLeaf index coord.val raw.val,trivial,hb,?_⟩
  apply posOf_eq hb
  exact hdrBlock_wctLeafInputP ..

theorem path_ftsQueries (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (physical : Nat) (padR value : Digest) (hi:index<2^31) (hp:physical<128) :
    FtsQueries answers
      (projectedPath (pathPos index coord.val physical)
        (fun level value=>SharedV3.childInput w index coord.val physical padR value level)
        (SharedV3.lastLevel coord.val+1) value) := by
  intro q hq
  rw [queried_projectedPath] at hq
  obtain ⟨level,hl,rfl⟩:=List.mem_map.mp hq
  have hl':level<6 := by have:=SharedV3.lastLevel_cases coord.val;have:=List.mem_range.mp hl;omega
  have hb : (pathPos index coord.val physical level).Bounded :=
    (pathPos_bounded index coord.val physical level hi coord.isLt hp (by have:=List.mem_range.mp hl;omega)).legacy
  refine ⟨pathPos index coord.val physical level,trivial,hb,?_⟩
  apply posOf_sameHeader answers _ hb
  exact childInput_sameHeader w answers index coord physical level hp hl' padR _

theorem coordinate_ftsQueries (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (coord : Fin 9) (raw : Fin 128) (rank : Fin 666) (prev : SharedV3.PairRoot) (hi:index<2^31) :
    FtsQueries answers (SharedV3.coordinate w index coord raw rank prev) := by
  unfold SharedV3.coordinate
  refine FtsQueries.bind answers (chainProgram_ftsQueries answers w index coord raw rank hi) ?_
  rw [childN_eq_projectedPath,bind_assoc]
  refine FtsQueries.bind answers (leafV3_ftsQueries answers index coord raw prev.1 _ ?_ hi) ?_
  · rw [V3.chainProgram,Correctness.eval_mapM];simp
  · exact FtsQueries.bind answers (path_ftsQueries answers w index coord _ _ _ hi (SharedV3.physical_lt _ _ raw.isLt))
      (FtsQueries.pure' answers _)

theorem forest_ftsQueries (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9→Fin 128) (rank : Fin 9→Fin 666) (hi:index<2^31) :
    FtsQueries answers (SharedV3.forest w index raw rank) := by
  unfold SharedV3.forest
  exact FtsQueries.fold answers (List.finRange 9) _
    (fun k _ prev=>coordinate_ftsQueries answers w index k (raw k) (rank k) prev hi) _

def FtsHitIn (answers : Answers) (qs : List Spec.Domain) : Prop :=
  ∃ p input, FtsPosition p ∧ Bounded p ∧ .inl (.inr input)∈qs ∧
    HashHitAt answers p (honestInput answers p) input ∧ SameHeader input (honestInput answers p)

theorem FtsHitIn.hitIn {answers : Answers} {qs : List Spec.Domain} (h:FtsHitIn answers qs) : HitIn answers qs := by
  obtain ⟨p,x,_,hb,hq,hh,hs⟩:=h
  exact ⟨p,x,hb,hq,hh,hs⟩

theorem forest_hit_fts (answers : Answers) (w : SharedV3.WBytes) (index : Nat)
    (raw : Fin 9→Fin 128) (rank : Fin 9→Fin 666) (hi:index<2^31)
    (hit:HitIn answers (queried answers (SharedV3.forest w index raw rank))) :
    FtsHitIn answers (queried answers (SharedV3.forest w index raw rank)) := by
  obtain ⟨p,x,hb,hq,hh,hs⟩:=hit
  obtain ⟨p',hfts,_,hpos⟩:=forest_ftsQueries answers w index raw rank hi _ hq
  have hp:=posOf_sameHeader answers p hb.legacy x hs
  have he:p'=p := Option.some.inj (hpos.symm.trans hp)
  subst p'
  exact ⟨p,x,hfts,hb,hq,hh,hs⟩

#print axioms forest_hit_fts
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
theorem FtsHitIn.mono {answers : Answers} {queries queries' : List Spec.Domain}
    (hit : FtsHitIn answers queries) (hsub : ∀ query ∈ queries, query ∈ queries') :
    FtsHitIn answers queries' := by
  obtain ⟨p,x,hfts,hb,hq,hh,hs⟩ := hit
  exact ⟨p,x,hfts,hb,hsub _ hq,hh,hs⟩
end ClaudeWCT.W9.T3M.Extract.Paired
