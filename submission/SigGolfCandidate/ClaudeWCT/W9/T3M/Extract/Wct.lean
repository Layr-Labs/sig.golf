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
theorem queried_hashPath (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) :
    ∀ count, queried answers (hashPath high input count initial) =
      (List.range count).map fun step => .inl (.inr (pad64 (pathInput answers high input initial step)))
  | 0 => rfl
  | count + 1 => by
      rw [hashPath_succ, queried_bind, queried_hashPath answers high input initial count, List.range_succ,
        List.map_append, queried_projHash]
      rfl
theorem pathValue_honest (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput)
    (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (projHash (high step) (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) : ∀ step, step ≤ count → pathValue answers high input initial step = target step := by
  intro step
  induction step with
  | zero => intro _; exact h0
  | succ step ih =>
      intro hs
      rw [pathValue_succ, pathInput, ih (by omega), honest step (by omega), reference step (by omega)]
theorem queried_hashPath_honest (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (projHash (high step) (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) :
    ∀ q ∈ queried answers (hashPath high input count initial), ∃ step, step < count ∧
      q = .inl (.inr (pad64 (honestInput step))) := by
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  refine ⟨step, hs, ?_⟩
  rw [pathInput, pathValue_honest answers high input honestInput target initial count reference honest h0 step
    hs.le, honest step hs]
/-! ### C1: hash paths whose step `s` uses the half of FTS heap `sel s` -/
section pathF
variable (sel : Nat → Nat)
def hashPathF (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => WCT9.ftsHash (sel step) (input step value)) initial
def pathValueF (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) (count : Nat) : Digest :=
  evalWithAnswerFn answers (hashPathF sel input count initial)
def pathInputF (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) (step : Nat) : HashInput :=
  input step (pathValueF sel answers input initial step)
theorem queried_ftsHash (answers : Answers) (heap : Nat) (input : HashInput) :
    queried answers (WCT9.ftsHash heap input) = [.inl (.inr (pad64 input))] := by
  unfold WCT9.ftsHash
  cases WCT9.ftsHighHeap heap <;> rfl
theorem hashPathF_succ (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPathF sel input (count + 1) initial =
      (hashPathF sel input count initial >>= fun value => WCT9.ftsHash (sel count) (input count value)) := by
  simp [hashPathF, List.range_succ, List.foldlM_append]
@[simp] theorem pathValueF_zero (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) :
    pathValueF sel answers input initial 0 = initial := rfl
theorem pathValueF_succ (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) (step : Nat) :
    pathValueF sel answers input initial (step + 1) =
      WCT9.ftsHalf (sel step) (answers (.inl (.inr (pad64 (pathInputF sel answers input initial step))))) := by
  simp only [pathValueF, hashPathF_succ, evalWithAnswerFn_bind, pathInputF, WCT9.eval_ftsHash]
theorem queried_hashPathF (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) :
    ∀ count, queried answers (hashPathF sel input count initial) =
      (List.range count).map fun step => .inl (.inr (pad64 (pathInputF sel answers input initial step)))
  | 0 => rfl
  | count + 1 => by
      rw [hashPathF_succ, queried_bind, queried_hashPathF answers input initial count, List.range_succ,
        List.map_append, queried_ftsHash]
      rfl
theorem pathInputF_queried (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest)
    (count step : Nat) (hstep : step < count) :
    .inl (.inr (pad64 (pathInputF sel answers input initial step))) ∈
      queried answers (hashPathF sel input count initial) := by
  rw [queried_hashPathF]
  exact List.mem_map.mpr ⟨step, List.mem_range.mpr hstep, rfl⟩
theorem pathValueF_honest (answers : Answers) (input : Nat → Digest → HashInput) (honestInput : Nat → HashInput)
    (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (WCT9.ftsHash (sel step) (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) : ∀ step, step ≤ count → pathValueF sel answers input initial step = target step := by
  intro step
  induction step with
  | zero => intro _; exact h0
  | succ step ih =>
      intro hs
      rw [pathValueF_succ, pathInputF, ih (by omega), honest step (by omega), ← WCT9.eval_ftsHash,
        reference step (by omega)]
theorem queried_hashPathF_honest (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (WCT9.ftsHash (sel step) (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) :
    ∀ q ∈ queried answers (hashPathF sel input count initial), ∃ step, step < count ∧
      q = .inl (.inr (pad64 (honestInput step))) := by
  intro q hq
  rw [queried_hashPathF] at hq
  obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  refine ⟨step, hs, ?_⟩
  rw [pathInputF, pathValueF_honest sel answers input honestInput target initial count reference honest h0 step hs.le,
    honest step hs]
/-- `hashPath_extract` for FTS paths (C1): a hit agrees with the honest output on the half of heap `sel step`. -/
theorem hashPathF_extract (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (WCT9.ftsHash (sel step) (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValueF sel answers input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count → Good step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputF sel answers input initial step))) ∈
          queried answers (hashPathF sel input count initial) ∧
        pad64 (pathInputF sel answers input initial step) ≠ pad64 (honestInput step) ∧
        WCT9.ftsHalf (sel step) (answers (.inl (.inr (pad64 (pathInputF sel answers input initial step))))) =
          WCT9.ftsHalf (sel step) (answers (.inl (.inr (pad64 (honestInput step))))) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInputF sel answers input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hne, hhit⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact hgood
        · exact Or.inr ⟨step, by omega, pathInputF_queried sel answers input initial _ _ (by omega), hne, hhit⟩
      · right
        refine ⟨count, by omega, pathInputF_queried sel answers input initial _ _ (by omega), heq, ?_⟩
        rw [pathValueF_succ] at reaches
        have hr := reference count (by omega)
        rw [WCT9.eval_ftsHash] at hr
        exact reaches.trans hr.symm
theorem merkleHPathF_extract (answers : Answers) (tag lay tree height leaf count : Nat)
    (path pads honestPath target : Nat → Digest) (hpads : Nat → BitVec 64) (value : Digest)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (WCT9.ftsHash (sel step)
        (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step))) =
          target (step + 1))
    (reaches : pathValueF sel answers (merkleInputH tag lay tree height leaf path pads hpads) value count =
      target count) :
    (value = target 0 ∧ ∀ step, step < count → path step = honestPath step ∧ pads step = 0 ∧
        HighOK tag lay tree height leaf hpads step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputF sel answers (merkleInputH tag lay tree height leaf path pads hpads) value
          step))) ∈ queried answers (hashPathF sel (merkleInputH tag lay tree height leaf path pads hpads) count value) ∧
        pad64 (pathInputF sel answers (merkleInputH tag lay tree height leaf path pads hpads) value step) ≠
          pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step)) ∧
        WCT9.ftsHalf (sel step) (answers (.inl (.inr (pad64 (pathInputF sel answers
          (merkleInputH tag lay tree height leaf path pads hpads) value step))))) =
          WCT9.ftsHalf (sel step) (answers (.inl (.inr (pad64
            (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step)))))) :=
  hashPathF_extract sel answers _ _ target _ value count reference
    (fun step _ current => merkleInputH_parse tag lay tree height leaf step path pads honestPath hpads current
      (target step)) reaches
end pathF
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
theorem canonicalHeader_ftsChainHeaderP (len step : Nat) (pb : BitVec 64) :
    Extract.canonicalHeaderL len (bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step pb)) =
      Extract.canonicalHeaderL len (bytesLE 16 (WCT9.ftsChainHeader index coord child t step)) := by
  unfold WCT9.ftsChainHeader WCT9.ftsChainHeaderP
  apply SigGolfCandidate.T3M.Extract.canonicalHeaderL_high_irrelevant
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (WCT9.ftsChainLow_lt ..) (by decide))]
  have := WCT9.ftsChainLow_byte0 index coord child t step
  unfold SigGolfCandidate.T3M.Extract.padLabel
  omega
theorem wctChainP_eq_hashPath (start count : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainP index coord child t start count pa pb pc v =
      hashPath (fun _ => false) (fun step value => wctChainInputP index coord child t (start + step) pa pb pc value)
        count v :=
  foldlM_range'_eq_hashPath (fun _ => false) (fun step value => wctChainInputP index coord child t step pa pb pc value)
    start count v
theorem wctValue_succ (s : Nat) :
    evalWithAnswerFn answers (projHash false (WCT9.chainInput index coord child t s
      (Extract.wctValue answers index coord child t s))) = Extract.wctValue answers index coord child t (s + 1) := by
  unfold Extract.wctValue
  rw [WCT9.eval_chain_add answers index coord child t 0 s 1, projHash_false]
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
      evalWithAnswerFn answers (projHash ((fun _ => false) step) (WCT9.chainInput index coord child t (4 - d + step)
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
  have h := hashPath_extract answers (fun _ => false)
    (fun step value => wctChainInputP index coord child t (4 - d + step) pa pb pc value)
    (fun step => WCT9.chainInput index coord child t (4 - d + step)
      (Extract.wctValue answers index coord child t (4 - d + step)))
    (fun step => Extract.wctValue answers index coord child t (4 - d + step))
    (fun _ => pa = 0 ∧ pb = 0 ∧ pc = 0) v d href hparse
    (by rw [show 4 - d + d = 4 by omega]; exact reaches)
  rcases h with ⟨hv, hgood⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by simpa using hv, fun hd0 => hgood 0 hd0, fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPath_honest answers (fun _ => false)
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
    · unfold Extract.SameHeader Extract.keyOf
      rw [Extract.hdrBlock_honestInput, Extract.length_honestInput, pathInput]
      simp only [wctChainInputP_block4, pad64_block4, hdrBlock_block4W, Extract.Pos.hdr, block4_length,
        Extract.Pos.len]
      rw [canonicalHeader_ftsChainHeaderP index coord child t _ _ _]
end chain
theorem leafHash_eq_shortHash (index coord child : Nat) (ends : List Digest) :
    WCT9.leafHash index coord child ends = shortHash (Extract.wctLeafInput index coord child ends) := by
  unfold WCT9.leafHash Extract.wctLeafInput Extract.listInput
  simp only [List.flatMap_cons, WCT9.bytesLE_zero16, List.append_assoc]
/-- The padded FTS leaf (campaign T8) as a list input: the pad is the first digest after the header. C1: the leaf
is FTS heap `128 + child`. -/
theorem leafHashP_eq_ftsHash (index coord child : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashP index coord child pad ends =
      WCT9.ftsHash (128 + child) (Extract.wctLeafInputP index coord child pad ends) := by
  unfold WCT9.leafHashP WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
  simp only [List.flatMap_cons, List.append_assoc]
theorem childRoot_eq_out (answers : Answers) (index coord child : Nat) :
    WCT9.childRoot answers index coord child (Extract.ftsPrev answers index coord).1 =
      WCT9.ftsHalf (128 + child) (answers (.inl (.inr (Extract.honestInput answers (.wctLeaf index coord child))))) := by
  unfold WCT9.childRoot
  rw [leafHashP_eq_ftsHash, WCT9.eval_ftsHash]
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
  rw [leafHashP_eq_ftsHash] at reaches ⊢
  rw [queried_ftsHash]
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
    refine ⟨.wctLeaf index coord child, _, hb, List.mem_singleton_self _, ⟨heq, ?_⟩, ?_⟩
    · rw [WCT9.eval_ftsHash] at reaches
      simp only [Extract.Pos.proj, Extract.Pos.high, Extract.projHalf_ftsHalf]
      show WCT9.ftsHalf (128 + child) _ = WCT9.ftsHalf (128 + child) _
      rw [reaches, childRoot_eq_out]
    · unfold Extract.SameHeader Extract.keyOf
      rw [Extract.hdrBlock_honestInput, Extract.length_honestInput, Extract.hdrBlock_wctLeafInputP]
      have hl : (pad64 (Extract.wctLeafInputP index coord child pad ends)).length = 128 := by
        rw [Cost.pad64_length, Extract.wctLeafInputP, Extract.listInput_length']
        simp [hlen]
      rw [hl]
      rfl
theorem merkleInput_tree_reference_le (answers : Answers) (tag lay tree height completed leaf : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves completed levels)
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < completed) (hc : completed ≤ height) :
    evalWithAnswerFn answers (projHash (merkleHigh tag lay height leaf step)
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInput merkleHigh
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rw [← nodeHash_eq_projHash]
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2 ^ (step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub] using hp.symm
/-- C1: `merkleInput_tree_reference_le` for an FTS tree, whose node at heap `h` is `wctNodeHash` (half of `h`). -/
theorem merkleInput_ftsReference (answers : Answers) (coord index leaf completed : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : WCT9.TreeLevelsF answers (WCT9.wctNodeHash coord index) 7 leaves completed levels)
    (hleaf : leaf < 2 ^ 7) (step : Nat) (hstep : step < completed) (hc : completed ≤ 7) :
    evalWithAnswerFn answers (WCT9.ftsHash (2 ^ (7 - step - 1) + leaf / 2 ^ (step + 1))
      (merkleInput 3 (WCT9.nodeLayer coord) index 7 leaf
        (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInput
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (7 - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := 7) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2 ^ (step + 1)) hparent
  simp only [WCT9.wctNodeHash, WCT9.wctNodeHeader] at hp
  simp only [nodeInputP, block4, WCT9.bytesLE_zero16, Nat.sub_sub]
  simpa only [treeValue] using hp.symm
section merkle
variable (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat)
def mTarget (step : Nat) : Digest := treeValue (Extract.ftsLevels answers index c.val) step (j / 2 ^ step)
def mPath (l : Nat) : Digest := treeValue (Extract.ftsLevels answers index c.val) l (j / 2 ^ l ^^^ 1)
theorem ftsLevels_treeLevels :
    WCT9.TreeLevelsF answers (WCT9.wctNodeHash c.val index) 7 (WCT9.coordLeaves answers index c) 5
      ((Extract.ftsLevels answers index c.val).take 6) :=
  WCT9.coordinate_treeLevels answers index c
/-- C1: the heap of the node computed at fold step `step` of child `j` (the half its parent reads). -/
def msel (step : Nat) : Nat := 2 ^ (7 - step - 1) + j / 2 ^ (step + 1)
theorem merkle_reference (hj : j < 128) : ∀ step, step < 5 →
    evalWithAnswerFn answers (WCT9.ftsHash (msel j step) (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j
      (mPath answers index c j) (fun _ => 0) step (mTarget answers index c j step))) =
        mTarget answers index c j (step + 1) := by
  intro step hstep
  have h := merkleInput_ftsReference answers c.val index j 5 _ _
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
theorem merkle_extract (hidx : index < 2 ^ 31) (hj : j < 128) (path pads : Nat → Digest)
    (hpads : Nat → BitVec 64) (leaf : Digest)
    (reaches : evalWithAnswerFn answers (hashPathF (msel j) (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5
      leaf) = mTarget answers index c j 5) :
    (leaf = WCT9.childRoot answers index c.val j (Extract.ftsPrev answers index c.val).1 ∧
      (∀ l, l < 5 → path l = mPath answers index c j l ∧ pads l = 0) ∧
      ∀ q ∈ queried answers (hashPathF (msel j) (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5 leaf),
        ∃ l, l < 5 ∧ q = .inl (.inr (Extract.honestInput answers (.wctNode index c.val l (j / 2 ^ (l + 1)))))) ∨
    Extract.HitIn answers (queried answers
      (hashPathF (msel j) (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5 leaf)) := by
  have hR := merkle_reference answers index c j hj
  have h := merkleHPathF_extract (msel j) answers 3 (WCT9.nodeLayer c.val) index 7 j 5 path pads
    (mPath answers index c j) (mTarget answers index c j) hpads leaf hR reaches
  rcases h with ⟨h0, hall⟩ | ⟨step, hstep, hq, hne, hhit⟩
  · left
    refine ⟨by rw [h0, mTarget_zero answers index c j hj], fun l hl => ⟨(hall l hl).1, (hall l hl).2.1⟩,
      fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPathF_honest (msel j) answers
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
    · refine ⟨by rw [← merkle_honestInput answers index c j step hstep]; exact hne, ?_⟩
      simp only [Extract.Pos.proj, Extract.Pos.high, Extract.projHalf_ftsHalf]
      show WCT9.ftsHalf (msel j step) _ = WCT9.ftsHalf (msel j step) _
      rw [← merkle_honestInput answers index c j step hstep]; exact hhit
    · rw [← merkle_honestInput answers index c j step hstep, pathInputF]
      exact Extract.sameHeader_merkleInputH _ _ _ _ (by unfold WCT9.nodeLayer; have := c.isLt; omega) _ _ _ _ _ _ _
        (fun _ => by
          have hpos : 0 < 2 ^ (7 - step - 1) + j / 2 ^ (step + 1) := by positivity
          have h2 : 2 ^ (7 - step - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
          have h3 : j / 2 ^ (step + 1) ≤ j := Nat.div_le_self _ _
          have hlt : 2 ^ (7 - step - 1) + j / 2 ^ (step + 1) < 2 ^ 64 :=
            lt_of_le_of_lt (Nat.add_le_add h2 h3) (by norm_num; omega)
          rw [Nat.mod_eq_of_lt hlt]
          exact Nat.pos_iff_ne_zero.mp hpos)
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
    · simp only [Extract.Pos.proj, Extract.Pos.high, Extract.projHalf_ftsHalf]
      show WCT9.ftsHalf (2 ^ (7 - 5 - 1) + j / 2 ^ 6) _ = WCT9.ftsHalf (2 ^ (7 - 5 - 1) + j / 2 ^ 6) _
      rw [WCT9.ftsHalf_of_high (WCT9.ftsHighHeap_top (by have := top_lt j hj; norm_num; omega)),
        WCT9.ftsHalf_of_high (WCT9.ftsHighHeap_top (by have := top_lt j hj; norm_num; omega))]
      rw [← top_honestInput answers index c j]
      exact reaches.trans (top_reference answers index c j hj).symm
    · unfold Extract.SameHeader Extract.keyOf
      rw [Extract.hdrBlock_honestInput, Extract.length_honestInput, wctTopInput_block4, pad64_block4,
        hdrBlock_block4W, block4_length]
      rfl
end merkle
theorem recoverCoordinateP_dec (N : HashOutput) (w : WBytes) (index : Nat) (c : WCT9.Coord) (prev : Digest × Digest) :
    recoverCoordinateP (witDecP N w).signature (padDecP N w) index N c prev =
      ((List.finRange 6).mapM (fun t => wctChainP index c.val (WCT9.child N c).val t.val
          (4 - WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit (WCT9.rank N c) t)
          (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
          (wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t))) >>= fun ends =>
        WCT9.leafHashP index c.val (WCT9.child N c).val prev.1 ends >>= fun leaf =>
          hashPathF (msel (WCT9.child N c).val) (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 (WCT9.child N c).val
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
  generalize hV : evalWithAnswerFn answers (hashPathF (msel (WCT9.child N c).val) (merkleInputH 3 (WCT9.nodeLayer c.val) (WCT9.digestIndex N) 7
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
