import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import SigGolfCandidate.Merge000
import SigGolfCandidate.Merge001
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge043
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge053
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge056

-- ==== merged from ClaudeWCT_W9_T3M_Extract_Wct ====
section

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
/-! Witness stack (charge 86): FTS chains 1, 3 are G chains (`value | header | padA | padC`, interior steps
`< 3` keep the HIGH half). The chain walk is a half-aware path (`Extract.hashPathW` with `ftsChainHigh`). -/
theorem wctChainInputPW_block4 (step : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainInputPW index coord child t step pa pb pc v =
      if WCT9.ftsIsG t then block4 v (WCT9.ftsChainHeaderP index coord child t step pb) pa pc
      else block4 pa (WCT9.ftsChainHeaderP index coord child t step pb) pc v := by
  unfold wctChainInputPW; split <;> rfl
theorem pad64_wctChainInputPW (step : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    pad64 (wctChainInputPW index coord child t step pa pb pc v) = wctChainInputPW index coord child t step pa pb pc v := by
  rw [wctChainInputPW_block4]; split <;> exact pad64_block4 _ _ _ _
theorem wctChainInputPW_length (step : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    (wctChainInputPW index coord child t step pa pb pc v).length = 64 := by
  rw [wctChainInputPW_block4]; split <;> exact block4_length _ _ _ _
theorem hdrBlock_wctChainInputPW (step : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    Extract.hdrBlock (wctChainInputPW index coord child t step pa pb pc v) =
      bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step pb) := by
  rw [wctChainInputPW_block4]; split <;> exact hdrBlock_block4W _ _ _ _
/-- Same-position parse of the padded FTS step input (either format): an input equal to the honest one has the
honest value and zero pads. -/
theorem wctChainInputPW_parse {step : Nat} {pa : Digest} {pb : BitVec 64} {pc v w : Digest}
    (heq : pad64 (wctChainInputPW index coord child t step pa pb pc v) =
      pad64 (WCT9.ftsChainInputW index coord child t step w)) :
    v = w ∧ (pa = 0 ∧ pb = 0 ∧ pc = 0) := by
  rw [wctChainInputPW_block4, Extract.ftsChainInputW_block4] at heq
  cases hG : WCT9.ftsIsG t
  · simp only [hG, Bool.false_eq_true, if_false, pad64_block4] at heq
    obtain ⟨h0, hh, h1, hv⟩ := block4_injective heq
    have hpb := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) hh
    simp only [WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_high] at hpb
    exact ⟨hv, h0, hpb, h1⟩
  · simp only [hG, if_true, pad64_block4] at heq
    obtain ⟨hv, hh, h0, h1⟩ := block4_injective heq
    have hpb := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) hh
    simp only [WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_high] at hpb
    exact ⟨hv, h0, hpb, h1⟩
theorem wctChainP_eq_hashPathW (start count : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainP index coord child t start count pa pb pc v =
      Extract.hashPathW (fun s => WCT9.ftsChainHigh t (start + s))
        (fun step value => wctChainInputPW index coord child t (start + step) pa pb pc value) count v := by
  unfold wctChainP Extract.hashPathW
  rw [List.range'_eq_map_range, List.foldlM_map]
  simp only [WCT9.halfHash_eq_projHash]
theorem wctValue_succ (s : Nat) :
    evalWithAnswerFn answers (WCT9.halfHash (WCT9.ftsChainHigh t s) (WCT9.ftsChainInputW index coord child t s
      (Extract.wctValue answers index coord child t s))) = Extract.wctValue answers index coord child t (s + 1) := by
  unfold Extract.wctValue
  rw [WCT9.eval_chain_add answers index coord child t 0 s 1]
  simp [WCT9.chain, WCT9.halfHash_eq_projHash]
theorem honestInput_wctChain (s : Nat) :
    Extract.honestInput answers (.wctChain index coord child t s) =
      WCT9.ftsChainInputW index coord child t s (Extract.wctValue answers index coord child t s) := by
  simp only [Extract.honestInput, WCT9.ftsChainInputW_padded]
theorem queried_hashPathW (high : Nat → Bool) (input : Nat → Digest → HashInput) (initial : Digest) :
    ∀ count, queried answers (Extract.hashPathW high input count initial) =
      (List.range count).map fun step => .inl (.inr (pad64 (Extract.pathInputW answers high input initial step)))
  | 0 => rfl
  | count + 1 => by
      rw [Extract.hashPathW_succ, queried_bind, queried_hashPathW high input initial count, List.range_succ,
        List.map_append, Extract.queried_halfHash]
      rfl
theorem pathValueW_honest (high : Nat → Bool) (input : Nat → Digest → HashInput) (honestInput : Nat → HashInput)
    (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (WCT9.halfHash (high step) (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) :
    ∀ step, step ≤ count → Extract.pathValueW answers high input initial step = target step := by
  intro step
  induction step with
  | zero => intro _; exact h0
  | succ step ih =>
      intro hs
      rw [Extract.pathValueW_succ, Extract.pathInputW, ih (by omega), honest step (by omega),
        reference step (by omega)]
theorem queried_hashPathW_honest (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (WCT9.halfHash (high step) (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) :
    ∀ q ∈ queried answers (Extract.hashPathW high input count initial), ∃ step, step < count ∧
      q = .inl (.inr (pad64 (honestInput step))) := by
  intro q hq
  rw [queried_hashPathW] at hq
  obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  refine ⟨step, hs, ?_⟩
  rw [Extract.pathInputW,
    pathValueW_honest answers high input honestInput target initial count reference honest h0 step hs.le,
    honest step hs]
/-- The FTS chain walk from `4 - d` to the end: either the revealed value and the pads are honest and every query
is an honest chain input, or some step is a hit on its used half. -/
theorem chain_walk (d : Nat) (hd : d ≤ 4) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (reaches : evalWithAnswerFn answers (wctChainP index coord child t (4 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 4) :
    (v = Extract.wctValue answers index coord child t (4 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d pa pb pc v), ∃ s, 4 - d ≤ s ∧ s < 4 ∧
        q = .inl (.inr (Extract.honestInput answers (.wctChain index coord child t s)))) ∨
    ∃ step, step < d ∧
      .inl (.inr (pad64 (wctChainInputPW index coord child t (4 - d + step) pa pb pc
        (Extract.pathValueW answers (fun s => WCT9.ftsChainHigh t (4 - d + s))
          (fun step value => wctChainInputPW index coord child t (4 - d + step) pa pb pc value) v step)))) ∈
        queried answers (wctChainP index coord child t (4 - d) d pa pb pc v) ∧
      Extract.HashHitH answers (WCT9.ftsChainHigh t (4 - d + step))
        (Extract.honestInput answers (.wctChain index coord child t (4 - d + step)))
        (pad64 (wctChainInputPW index coord child t (4 - d + step) pa pb pc
          (Extract.pathValueW answers (fun s => WCT9.ftsChainHigh t (4 - d + s))
            (fun step value => wctChainInputPW index coord child t (4 - d + step) pa pb pc value) v step))) := by
  rw [wctChainP_eq_hashPathW] at reaches ⊢
  have href : ∀ step, step < d →
      evalWithAnswerFn answers (WCT9.halfHash (WCT9.ftsChainHigh t (4 - d + step))
        (WCT9.ftsChainInputW index coord child t (4 - d + step)
          (Extract.wctValue answers index coord child t (4 - d + step)))) =
        Extract.wctValue answers index coord child t (4 - d + (step + 1)) := by
    intro step _
    rw [wctValue_succ, Nat.add_assoc]
  have hparse : ∀ step, step < d → ∀ value,
      pad64 (wctChainInputPW index coord child t (4 - d + step) pa pb pc value) =
        pad64 (WCT9.ftsChainInputW index coord child t (4 - d + step)
          (Extract.wctValue answers index coord child t (4 - d + step))) →
      value = Extract.wctValue answers index coord child t (4 - d + step) ∧ (pa = 0 ∧ pb = 0 ∧ pc = 0) :=
    fun _ _ _ heq => wctChainInputPW_parse index coord child t heq
  have h := Extract.hashPathW_extract answers (fun s => WCT9.ftsChainHigh t (4 - d + s))
    (fun step value => wctChainInputPW index coord child t (4 - d + step) pa pb pc value)
    (fun step => WCT9.ftsChainInputW index coord child t (4 - d + step)
      (Extract.wctValue answers index coord child t (4 - d + step)))
    (fun step => Extract.wctValue answers index coord child t (4 - d + step))
    (fun _ => pa = 0 ∧ pb = 0 ∧ pc = 0) v d href hparse
    (by rw [show 4 - d + d = 4 by omega]; exact reaches)
  rcases h with ⟨hv, hgood⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by simpa using hv, fun hd0 => hgood 0 hd0, fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPathW_honest answers (fun s => WCT9.ftsChainHigh t (4 - d + s))
      (fun step value => wctChainInputPW index coord child t (4 - d + step) pa pb pc value)
      (fun step => WCT9.ftsChainInputW index coord child t (4 - d + step)
        (Extract.wctValue answers index coord child t (4 - d + step)))
      (fun step => Extract.wctValue answers index coord child t (4 - d + step)) v d href
      (fun step hs => by
        obtain ⟨h0, hB, h1⟩ := hgood step hs
        simp only [h0, hB, h1, wctChainInputPW_zero]) hv q hq
    refine ⟨4 - d + step, by omega, by omega, ?_⟩
    rw [honestInput_wctChain, WCT9.ftsChainInputW_padded]
  · right
    refine ⟨step, hstep, hq, ?_⟩
    rw [honestInput_wctChain, ← WCT9.ftsChainInputW_padded]
    exact hhit
/-- The SameHeader side of a chain hit (either format: header in bytes 16..32). -/
theorem chain_sameHeader (s : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    Extract.SameHeader (pad64 (wctChainInputPW index coord child t s pa pb pc v))
      (Extract.honestInput answers (.wctChain index coord child t s)) := by
  refine Extract.SameHeader.of_canonical ?_ (by rw [Extract.honestInput_length]; simp [Extract.Pos.len]) ?_
  · rw [Extract.honestInput_length, pad64_wctChainInputPW, wctChainInputPW_length]; rfl
  rw [Extract.hdrBlock_honestInput, pad64_wctChainInputPW, hdrBlock_wctChainInputPW]
  simp only [Extract.Pos.hdr]
  exact canonicalHeader_ftsChainHeaderP index coord child t _ _
theorem chain_extract (d : Nat) (hd : d ≤ 4) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6)
    (reaches : evalWithAnswerFn answers (wctChainP index coord child t (4 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 4) :
    (v = Extract.wctValue answers index coord child t (4 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d pa pb pc v), ∃ s, 4 - d ≤ s ∧ s < 4 ∧
        q = .inl (.inr (Extract.honestInput answers (.wctChain index coord child t s)))) ∨
    Extract.HitIn answers (queried answers (wctChainP index coord child t (4 - d) d pa pb pc v)) := by
  rcases chain_walk answers index coord child t d hd pa pb pc v reaches with h | ⟨step, hstep, hq, hhit⟩
  · exact Or.inl h
  · right
    obtain ⟨hi, hc, hj, ht⟩ := hb
    exact ⟨.wctChain index coord child t (4 - d + step), _, ⟨hi, hc, hj, ht, by omega⟩, hq, hhit,
      chain_sameHeader answers index coord child t _ pa pb pc _⟩
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
    · refine Extract.SameHeader.of_hdrBlock ?_ (by rw [Extract.hdrBlock_honestInput, Extract.hdrBlock_wctLeafInputP]; rfl)
      rw [Extract.honestInput_length]
      simp [Extract.wctLeafInputP, Extract.listInput, pad64, bytesLE_length, digest_list_bytes_length, hlen,
        Extract.Pos.len]
theorem merkleInput_tree_reference_le (answers : Answers) (tag lay tree height completed leaf : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves completed levels) (htop : ¬ (tag = 3 ∧ lay = 0))
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < completed) (hc : completed ≤ height) :
    evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInput
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rw [← nodeHash_eq_shortHash (nodeHalfHigh_of_ne htop _)]
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
    (ftsLevels_treeLevels answers index c) (by simp [WCT9.nodeLayer]) (by norm_num; omega) step hstep (by decide)
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
    · apply Extract.hashHitAt_of_low
        (Extract.Pos.proj_of_low (p := .wctNode index c.val step (j / 2 ^ (step + 1)))
          (decide_eq_false (show ¬step = 5 by omega)))
      rw [← merkle_honestInput answers index c j step hstep]; exact hhit
    · refine Extract.SameHeader.of_canonical ?_ (by rw [Extract.honestInput_length]; simp [Extract.Pos.len]) ?_
      · rw [Extract.honestInput_length, pathInput]
        simp only [merkleInputH, pad64_nodeInputPH, SigGolfCandidate.T3M.SecurityInputs.nodeInputPH, pad64_block4,
          block4_length, Extract.Pos.len]
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
    · show WCT9.halfOf true _ = WCT9.halfOf true _
      simp only [WCT9.halfOf_true]
      rw [← top_honestInput answers index c j]
      exact reaches.trans (top_reference answers index c j hj).symm
    · refine Extract.SameHeader.of_hdrBlock ?_
        (by rw [Extract.hdrBlock_honestInput, wctTopInput_block4, pad64_block4, hdrBlock_block4W]; rfl)
      rw [Extract.honestInput_length, wctTopInput_block4, pad64_block4]
      simp [block4, bytesLE_length, Extract.Pos.len]
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

/-- Stage 2 (C3 length-aware decoding): every paired honest input has its position's length. -/
theorem honestInput_length (answers : Answers) (p : Pos) : (honestInput answers p).length = p.len := by
  cases p with
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.len]
      rw [Extract.pad64_length_of_mod] <;>
        simp [Extract.wctLeafInputP, Extract.listInput, bytesLE_length, Extract.wctEnds]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.len]
      rw [wctTopInput_block4, pad64_block4]
      simp [block4, bytesLE_length]
  | chain lay tree lf i step => exact Extract.honestInput_length answers (.chain lay tree lf i step)
  | leaf lay tree lf => exact Extract.honestInput_length answers (.leaf lay tree lf)
  | node lay tree level nd => exact Extract.honestInput_length answers (.node lay tree level nd)
  | forest index => exact Extract.honestInput_length answers (.forest index)
  | wctChain index coord child t step => exact Extract.honestInput_length answers (.wctChain index coord child t step)

section chain
variable (answers : Answers) (index coord child t : Nat)
theorem honestInput_wctChain (s : Nat) :
    honestInput answers (.wctChain index coord child t s) =
      WCT9.ftsChainInputW index coord child t s (Extract.wctValue answers index coord child t s) :=
  WctExtract.honestInput_wctChain answers index coord child t s
/-- Witness stack: an FTS chain position projects onto the half `ftsChainHigh` of its step. -/
theorem proj_wctChain (s : Nat) : proj (.wctChain index coord child t s) = WCT9.halfOf (WCT9.ftsChainHigh t s) := by
  funext a
  cases h : WCT9.ftsChainHigh t s <;> simp [proj, WCT9.halfOf, h]
theorem chain_extract (d : Nat) (hd : d ≤ 4) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6)
    (reaches : evalWithAnswerFn answers (wctChainP index coord child t (4 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 4) :
    (v = Extract.wctValue answers index coord child t (4 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d pa pb pc v), ∃ s, 4 - d ≤ s ∧ s < 4 ∧
        q = .inl (.inr (honestInput answers (.wctChain index coord child t s)))) ∨
    HitIn answers (queried answers (wctChainP index coord child t (4 - d) d pa pb pc v)) := by
  rcases WctExtract.chain_walk answers index coord child t d hd pa pb pc v reaches with h | ⟨step, hstep, hq, hhit⟩
  · exact Or.inl h
  · right
    obtain ⟨hi, hc, hj, ht⟩ := hb
    refine ⟨.wctChain index coord child t (4 - d + step), _, ⟨hi, hc, hj, ht, by omega⟩, hq, ?_,
      WctExtract.chain_sameHeader answers index coord child t _ pa pb pc _⟩
    refine ⟨hhit.1, ?_⟩
    rw [proj_wctChain]
    exact hhit.2
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
    · refine Extract.SameHeader.of_hdrBlock ?_ (by rw [hdrBlock_honestInput, Extract.hdrBlock_wctLeafInputP]; rfl)
      rw [honestInput_length]
      simp [Extract.wctLeafInputP, Extract.listInput, pad64, bytesLE_length, digest_list_bytes_length, hlen,
        Extract.Pos.len]

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
    refine SameHeader.of_canonical ?_ (by rw [honestInput_length]; simp [Pos.len]) ?_
    · rw [honestInput_length, block4_length]; rfl
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
  have hs : ¬singletonHigh coord level (physical/2^(level+1)) := by
    have hlast := SharedV3.lastLevel_cases coord
    exact not_singletonHigh_of_level (by omega)
  have he : highNodeAt coord level (physical/2^(level+1)) ↔ SharedV3.hiOut physical (level+1) = true := by
    unfold highNodeAt SharedV3.hiOut
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | h) | h)
      · exact absurd h hp
      · exact absurd h hs
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
  · -- Stage 2 (merged singleton "Cm"): the left top node (direction 0, heap 2) keeps the high half, the right one
    -- (direction 1, heap 3) the low half; `highNodeAt` marks exactly node 0 of level 5.
    have hl5 : SharedV3.lastLevel coord.val = 5 := by simp [SharedV3.lastLevel, SharedV3.first, hc]
    have hj := SharedV3.physical_lt coord.val raw.val raw.isLt
    have h64 : (2:Nat)^(SharedV3.lastLevel coord.val+1) = 64 := by simp [hl5]
    have hiff : highNodeAt coord.val (SharedV3.lastLevel coord.val)
        (SharedV3.physical coord.val raw.val/2^(SharedV3.lastLevel coord.val+1)) ↔
        SharedV3.direction coord.val (SharedV3.physical coord.val raw.val) = 0 := by
      unfold SharedV3.direction highNodeAt highPosition singletonHigh
      rw [h64]
      omega
    by_cases hd : SharedV3.direction coord.val (SharedV3.physical coord.val raw.val) = 0
    · have hp := hiff.mpr hd
      simp only [if_pos hc, posHash, pathPos, proj, if_pos hp, decide_eq_true hd, SharedV3.hashSel, ↓reduceIte]
      rfl
    · have hp : ¬highNodeAt coord.val (SharedV3.lastLevel coord.val)
          (SharedV3.physical coord.val raw.val/2^(SharedV3.lastLevel coord.val+1)) := fun h => hd (hiff.mp h)
      simp only [if_pos hc, posHash, pathPos, proj, if_neg hp, decide_eq_false hd, SharedV3.hashSel,
        Bool.false_eq_true, ↓reduceIte]
      rfl
  · have hp : highNodeAt coord.val (SharedV3.lastLevel coord.val)
        (SharedV3.physical coord.val raw.val/2^(SharedV3.lastLevel coord.val+1)) :=
      Or.inl (Or.inl ((high_last _ coord.isLt).mpr hc))
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
  refine SameHeader.of_canonical ?_ (by rw [honestInput_length]; simp [pathPos, Pos.len]) ?_
  · rw [honestInput_length, pad64_block4, block4_length]; rfl
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
    exact List.mem_append_left _ (by simp only [SigGolfCandidate.T3M.SecurityExtraction.queried_projHash,
      List.mem_singleton])

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
      wctChainInputPW_zero, WCT9.ftsChainInputW_padded,
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
  apply posOf_key_eq hp (hs.1.trans (honestInput_length answers p))
  rw [hs.2]
  exact hdrKey_of_hdrBlock hp (honestInput_length answers p) (hdrBlock_honestInput answers p)

theorem posOf_padded_chain (index coord raw t step : Nat)
    (pa : Digest) (pb : BitVec 64) (pc value : Digest)
    (hb : (Pos.wctChain index coord raw t step).Bounded) :
    posOf (pad64 (wctChainInputP index coord raw t step pa pb pc value)) =
      some (.wctChain index coord raw t step) := by
  have hlen : (pad64 (wctChainInputP index coord raw t step pa pb pc value)).length = 64 := by
    rw [wctChainInputP_block4,pad64_block4,block4_length]
  apply posOf_key_eq hb hlen
  -- C4: an FTS chain word is at least 2^16 (coordinate nibble `coord + 1`), so it is no top label.
  have hT : ¬ TopLow (hdrBlock (pad64 (wctChainInputP index coord raw t step pa pb pc value))) := by
    rw [wctChainInputP_block4, pad64_block4, hdrBlock_block4W, topLow_bytesLE_iff]
    unfold SigGolfCandidate.T3.tweakLow
    rw [ClaudeWCT.WCT9.ftsChainHeaderP_toNat]
    have hge := ClaudeWCT.WCT9.ftsChainLow_ge (coord := coord) (by have := hb.2.1; omega) index raw t step
    have hlt := ClaudeWCT.WCT9.ftsChainLow_lt index coord raw t step
    omega
  rw [hdrKey_of_len64 hlen hT,wctChainInputP_block4,pad64_block4,hdrBlock_block4W,
    canonicalHeader_ftsChainHeaderP]
  simpa only [Pos.hdr] using (Pos.canonicalHeader_eq hb)

/-- Witness stack: the same position for the G/F FTS chain input (header in bytes `16..32` either way). -/
theorem posOf_padded_chainW (index coord raw t step : Nat)
    (pa : Digest) (pb : BitVec 64) (pc value : Digest)
    (hb : (Pos.wctChain index coord raw t step).Bounded) :
    posOf (pad64 (wctChainInputPW index coord raw t step pa pb pc value)) =
      some (.wctChain index coord raw t step) := by
  have hlen : (pad64 (wctChainInputPW index coord raw t step pa pb pc value)).length = 64 := by
    rw [pad64_wctChainInputPW, wctChainInputPW_length]
  apply posOf_key_eq hb hlen
  have hT : ¬ TopLow (hdrBlock (pad64 (wctChainInputPW index coord raw t step pa pb pc value))) := by
    rw [pad64_wctChainInputPW, hdrBlock_wctChainInputPW, topLow_bytesLE_iff]
    unfold SigGolfCandidate.T3.tweakLow
    rw [ClaudeWCT.WCT9.ftsChainHeaderP_toNat]
    have hge := ClaudeWCT.WCT9.ftsChainLow_ge (coord := coord) (by have := hb.2.1; omega) index raw t step
    have hlt := ClaudeWCT.WCT9.ftsChainLow_lt index coord raw t step
    omega
  rw [hdrKey_of_len64 hlen hT, pad64_wctChainInputPW, hdrBlock_wctChainInputPW,
    canonicalHeader_ftsChainHeaderP]
  simpa only [Pos.hdr] using (Pos.canonicalHeader_eq hb)

theorem chainV3_ftsQueries (answers : Answers) (index coord raw t start count : Nat)
    (pa : Digest) (pb : BitVec 64) (pc value : Digest)
    (hi : index<2^31) (hc : coord<9) (hr : raw<128) (ht : t<6) (hn : start+count≤4) :
    FtsQueries answers (V3.chainP index coord raw t start count pa pb pc value) := by
  have he := W9Machine.chainP_canonical index coord raw t start count pa pc value pb hi hc hr ht hn
  rw [he,wctChainP_eq_hashPathW]
  intro q hq
  rw [queried_hashPathW] at hq
  obtain ⟨step,hstep,rfl⟩:=List.mem_map.mp hq
  have hs : step<count := List.mem_range.mp hstep
  have hb : (Pos.wctChain index coord raw t (start+step)).Bounded := ⟨hi,hc,hr,ht,by omega⟩
  refine ⟨.wctChain index coord raw t (start+step),trivial,hb,?_⟩
  exact posOf_padded_chainW index coord raw t (start+step) pa pb pc _ hb

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
  refine posOf_eq hb ?_ (hdrBlock_wctLeafInputP ..)
  simp [Extract.wctLeafInputP, Extract.listInput, pad64, SphincsSecurity.bytesLE_length, digest_list_bytes_length, hlen, Pos.len]

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
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_VerifyP ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem keygen_pk (answers : Answers) : (evalWithAnswerFn answers WCT9.Rev3.keygen).1 = honestRoot answers 0 0 := by
  unfold WCT9.Rev3.keygen WCT9.keygen keygen keygenPayload
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [Correctness.eval_buildTopTree answers]
  unfold honestRoot
  rw [WCT9.wotsTree_top]
  rfl
theorem layersWalkSpec_holds : WctExtract.LayersWalkSpec
    (fun answers w index qs => HitIn answers qs ∨
      ∃ lay : Layer, Diverge answers w index lay qs ∧ ∀ l : Layer, l.val < lay.val → Good answers w index l)
    (fun answers w index => ∀ l : Layer, Good answers w index l) := by
  intro answers w index root qs hidx hq h
  rcases layersBC_walk answers w index root hidx h with hhit | ⟨lay, hdiv, hgood⟩ | ⟨hgood, hroot⟩
  · exact Or.inl (Or.inl (hhit.mono hq))
  · exact Or.inl (Or.inr ⟨lay, hdiv.mono hq, hgood⟩)
  · exact Or.inr ⟨hgood, hroot⟩
theorem verifyP_walk_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (WCT9.digestIndex N) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (WCT9.digestIndex N) l) ∨
       ((∀ l : Layer, Good answers w (WCT9.digestIndex N) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
            honestTop answers (WCT9.digestIndex N) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
            q ∈ queried answers (verifyP m pk w))) := by
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases layersWalkSpec_holds answers w (WCT9.digestIndex N) _ _ (WCT9.digestIndex_lt N) hqL (hpk ▸ hlay) with
    (hhit | hdiv) | ⟨hgood, hroot⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  · exact Or.inr (Or.inr ⟨hgood, hroot, hqF⟩)
theorem verifyP_extract_normal (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (WCT9.digestIndex N) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (WCT9.digestIndex N) l) ∨
       ((∀ l : Layer, Good answers w (WCT9.digestIndex N) l) ∧ WctExtract.WctHonest answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WctExtract.verifyP_extract layersWalkSpec_holds answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hhit | hev | hgood
  · exact Or.inl hhit
  · rcases hev with hhit | hdiv
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hdiv)
  · exact Or.inr (Or.inr hgood)
theorem wctEnds_eq (answers : Answers) (index coord child : Nat) :
    wctEnds answers index coord child = List.ofFn (WCT9.chainEnd answers index coord child) := rfl
theorem ftsNodes_eq (answers : Answers) (index : Nat) (c : WCT9.Coord) :
    ftsNodes answers index c.val = WCT9.coordNodes answers index c := rfl
theorem ftsPair_eq (answers : Answers) (index : Nat) (c : WCT9.Coord) :
    ftsPair answers index c.val = WCT9.coordinatePair answers index c := by
  unfold ftsPair ftsLevels WCT9.coordinatePair
  rw [WCT9.heapLevels_value _ 6 0 (by decide) (by decide), WCT9.heapLevels_value _ 6 1 (by decide) (by decide),
    ftsNodes_eq]
  rfl
theorem ftsPairsHonest_eq (answers : Answers) (index : Nat) :
    ftsPairsHonest answers index = List.ofFn (WCT9.coordinatePair answers index) := by
  apply List.ext_getElem (by simp [ftsPairsHonest])
  intro i hi _
  simp only [ftsPairsHonest, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact ftsPair_eq answers index ⟨i, by simpa [ftsPairsHonest] using hi⟩
theorem honestTop_eq (answers : Answers) (index : Nat) :
    honestTop answers index = WCT9.honestTop answers index :=
  WctExtract.ftsPair_eq_prev answers index 8
theorem honestPair_eq (answers : Answers) (lay : Layer) (tree : Nat) :
    honestPair answers lay tree = WCT9.builtPair answers lay tree := rfl
theorem honestRoot_top (answers : Answers) :
    honestRoot answers 0 0 = treeValue (builtTree answers 0 0) 12 0 := by
  unfold honestRoot
  rw [WCT9.wotsTree_top]
  rfl
end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_New_G3b_Shared ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low dummyDigits_valid)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem referenceSearch_producerDecode (answers : Answers) (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (c, digits)) :
    WCT9.producerDecode L.lay (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L (leafMsg answers L) c 0))))) = some digits := by
  have hs := (WCT9.layerCounterSearch_some_search answers L.lay L.tree L.leaf (leafMsg answers L)
    (WCT9.searchLimit L.lay) 0 c digits
    (by have := WCT9.searchLimit_le L.lay; unfold counterLimit at this; omega) h).2.2
  rw [encRow_zero]
  exact hs
theorem referenceSearch_decode (answers : Answers) (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (c, digits)) :
    decode L.lay (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L (leafMsg answers L) c 0))))) = some digits :=
  WCT9.producerDecode_decode (referenceSearch_producerDecode answers L h)
theorem referenceDigits_decode (answers : Answers) (L : LeafAddr) :
    ∃ value : Digest, decode L.lay value = some (referenceDigits answers L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers L with
  | none => exact SigGolfCandidate.T3.Security.Wots.dummyDigits_valid L.lay
  | some s =>
      obtain ⟨c, digits⟩ := s
      exact ⟨_, referenceSearch_decode answers L hs⟩
theorem dummyDigits_credit (lay : Layer) :
    WCT9.producerFloor lay + WCT9.dispatchPenalty lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) ≤
      WCT9.wordCredit lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) +
        4 * WCT9.savedCopies lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) := by
  fin_cases lay <;> decide +kernel
theorem dummyDigits_zeroBound (lay : Layer) :
    WCT9.producerZeroBound lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) := by
  fin_cases lay <;> decide +kernel
theorem dummyDigest_rankBound (lay : Layer) :
    WCT9.producerRankBound lay (SigGolfCandidate.T3.Security.WotsExtract.dummyDigest lay) := by
  fin_cases lay <;> decide +kernel
theorem dummyDigest_producerDecode (lay : Layer) :
    WCT9.producerDecode lay (SigGolfCandidate.T3.Security.WotsExtract.dummyDigest lay) =
      some (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) :=
  WCT9.producerDecode_of (SigGolfCandidate.T3.Security.WotsExtract.dummyDigest_decode lay)
    (dummyDigits_credit lay) (dummyDigits_zeroBound lay) (dummyDigest_rankBound lay)
theorem referenceDigits_producerDecode (answers : Answers) (L : LeafAddr) :
    ∃ value : Digest, WCT9.producerDecode L.lay value = some (referenceDigits answers L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers L with
  | none => exact ⟨_, dummyDigest_producerDecode L.lay⟩
  | some s =>
      obtain ⟨c, digits⟩ := s
      exact ⟨_, referenceSearch_producerDecode answers L hs⟩
theorem referenceDigits_credit (answers : Answers) (L : LeafAddr) :
    WCT9.producerFloor L.lay + WCT9.dispatchPenalty L.lay (referenceDigits answers L) ≤
      WCT9.wordCredit L.lay (referenceDigits answers L) + 4 * WCT9.savedCopies L.lay (referenceDigits answers L) := by
  obtain ⟨u, hu⟩ := referenceDigits_producerDecode answers L
  exact WCT9.producerDecode_credit hu
theorem producerDecode_canonical {lay : Layer} {a b : Digest} {ds : List Nat}
    (ha : WCT9.producerDecode lay a = some ds) (hb : decode lay b = some ds) :
    WCT9.producerDecode lay b = some ds := by
  have hab := decode_some_injective (WCT9.producerDecode_decode ha) hb
  subst b
  exact ha
theorem producerDecode_of_reference (answers : Answers) (L : LeafAddr) {v : Digest}
    (h : decode L.lay v = some (referenceDigits answers L)) :
    WCT9.producerDecode L.lay v = some (referenceDigits answers L) := by
  obtain ⟨value, hp⟩ := referenceDigits_producerDecode answers L
  exact producerDecode_canonical hp h
theorem depth_le (answers : Answers) (a : ChainAddr) (ha : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers a.key
  have := decode_digit_max hv a.chain ha
  unfold depth
  omega
theorem referenceDigits_length (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers L
  exact (decode_length_sum hv).1
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    ContactAt answers trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, ClaudeWCT.W9.T3.Security.Wots.seenRowW_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    TwoEdgeAt answers trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, ClaudeWCT.W9.T3.Security.Wots.seenRowW_mono h1 hsub,
    ClaudeWCT.W9.T3.Security.Wots.seenRowW_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers trace L) (hsub : ∀ e ∈ trace, e ∈ trace') :
    EncodingMatchAt answers trace' L := by
  obtain ⟨message, counter, pad, answer, hfit, hm, hne, hd⟩ := h
  exact ⟨message, counter, pad, answer, hfit, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    MarkerAt answers trace' a := by
  obtain ⟨message, counter, pad, answer, digits, hfit, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, pad, answer, digits, hfit, hsub _ hm, hne, hd, hl, hu⟩
theorem structuralHit_mono (h : StructuralHit answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    StructuralHit answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hc, hh⟩
end mono
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
theorem WotsPrimitive.mono {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitive answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') : WotsPrimitive answers trace' := by
  rcases h with ⟨L, h⟩ | h | ⟨a, h⟩ | ⟨a, b, hab, h1, h2⟩ | ⟨a, hm, hc⟩
  · exact Or.inl ⟨L, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHit_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end ClaudeWCT.W9.T3.Security.Wots
namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] verifyP expandB
theorem check_hashOnly (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    Security.SourceReplay.HashOnly (checkForgeryP publicKey log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3.Security.PaddedGame.check_public publicKey log forgery)
  intro input h
  rcases input with (coin | input) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem check_accepting (answers : Answers) (publicKey : Digest) (log : QueryLog Requests)
    (forgery : ForgeryP) (hw : evalWithAnswerFn answers (checkForgeryP publicKey log forgery) = true) :
    Fresh log forgery ∧ ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
      evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
      ∀ input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (verifyP message publicKey witness),
        input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (checkForgeryP publicKey log forgery) := by
  cases forgery with
  | witness message witness =>
      simp only [checkForgeryP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.and_eq_true,
        decide_eq_true_eq] at hw
      refine ⟨hw.1, message, witness, ⟨rfl, rfl⟩, hw.2, ?_⟩
      intro input hi
      simpa only [checkForgeryP, SigGolfCandidate.T3M.SecurityExtraction.queried_bind, SigGolfCandidate.T3M.SecurityExtraction.queried_pure,
        List.append_nil] using hi
  | signature message signature =>
      cases he : evalWithAnswerFn answers (expandB message publicKey signature) with
      | none => simp [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure] at hw
      | some witness =>
          simp only [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure, Bool.and_eq_true,
            decide_eq_true_eq] at hw
          refine ⟨hw.1, message, witness, ⟨rfl, he⟩, hw.2, ?_⟩
          intro input hi
          simp only [checkForgeryP, SigGolfCandidate.T3M.SecurityExtraction.queried_bind, he, SigGolfCandidate.T3M.SecurityExtraction.queried_pure,
            List.append_nil]
          exact List.mem_append_right _ hi
end ClaudeWCT.W9.T3.Security.PaddedExtraction

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem eval_publicHash (answers : Answers) (input : HashInput) :
    evalWithAnswerFn answers (publicHash input) = answers (.inl (.inr (pad64 input))) := rfl

theorem counterSearch_decode (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) : ∀ fuel start c found,
    evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg start fuel) =
      some (c, found) →
    WCT9.CanonicalPolicy.producerDecodeOut lay floor
      (evalWithAnswerFn answers (publicHash (WCT9.layerEncodingInput lay tree leaf msg c))) =
      some found := by
  intro fuel
  induction fuel with
  | zero => intro start c found h; simp [WCT9.CanonicalPolicy.layerCounterSearchAt] at h
  | succ fuel ih =>
      intro start c found h
      rw [WCT9.CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind] at h
      cases hd : WCT9.CanonicalPolicy.producerDecodeOut lay floor
        (evalWithAnswerFn answers (publicHash
          (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 start)))) with
      | none => rw [hd] at h; exact ih (start + 1) c found h
      | some ds =>
          rw [hd, evalWithAnswerFn_pure] at h
          cases h
          exact hd

theorem counterSearch_accepted (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) (fuel start : Nat) (c : BitVec 32) (digits : List Nat) (low : Bool)
    (h : evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg start fuel) =
      some (c, digits, low)) :
    ∃ value, WCT9.CanonicalPolicy.producerDecodeAt lay floor low value = some digits :=
  ⟨_, (WCT9.CanonicalPolicy.producerDecodeOut_spec
    (counterSearch_decode answers lay floor tree leaf msg fuel start c (digits, low) h)).2⟩

theorem referenceSearch_decode (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {c : BitVec 32} {digits : List Nat} {low : Bool}
    (h : referenceSearch answers messages L = some (c, digits, low)) :
    WCT9.CanonicalPolicy.decode L.lay
      (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L (messages L) c 0))))) = some digits := by
  obtain ⟨remaining, _, hs⟩ := Option.bind_eq_some_iff.mp h
  have hd := counterSearch_decode answers L.lay
    (WCT9.CanonicalPolicy.threshold L.lay.val remaining) L.tree L.leaf (messages L)
    (WCT9.searchLimit L.lay) 0 c (digits, low) hs
  rw [encRow_zero]
  exact (WCT9.CanonicalPolicy.producerDecodeAt_spec (WCT9.CanonicalPolicy.producerDecodeOut_spec hd).2).1

theorem referenceDigits_decode (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) :
    ∃ value : Digest, WCT9.CanonicalPolicy.decode L.lay value = some (referenceDigits answers messages L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers messages L with
  | none => exact dummyDigits_valid (WCT9.CanonicalPolicy.normalLayer L.lay)
  | some found =>
      obtain ⟨c, digits, low⟩ := found
      exact ⟨_, referenceSearch_decode answers messages L hs⟩

theorem normalLayer_chainCount (lay : Layer) :
    chainCount (WCT9.CanonicalPolicy.normalLayer lay) = chainCount lay := by
  fin_cases lay <;> rfl

theorem normalLayer_maxDigit (lay : Layer) (i : Nat) :
    maxDigit (WCT9.CanonicalPolicy.normalLayer lay) i = maxDigit lay i := by
  fin_cases lay <;> rfl

theorem referenceDigits_length (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : (referenceDigits answers messages L).length = chainCount L.lay := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers messages L
  exact (decode_length_sum hv).1.trans (normalLayer_chainCount L.lay)

theorem depth_le (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (ha : a.chain < chainCount a.key.lay) :
    depth answers messages a ≤ maxDigit a.key.lay a.chain := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers messages a.key
  have hi : a.chain < chainCount (WCT9.CanonicalPolicy.normalLayer a.key.lay) := by
    rw [normalLayer_chainCount]; exact ha
  have hd := decode_digit_max hv a.chain hi
  rw [normalLayer_maxDigit] at hd
  exact hd

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceInput_ne (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    {digits : List Nat}
    (hd : WCT9.CanonicalPolicy.decode L.lay
      (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L msg ctr pad))))) = some digits)
    (hne : msg ≠ messages L ∨ digits ≠ referenceDigits answers messages L) :
    referenceInput answers messages L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers messages L with
  | none => rw [hs] at h; simp at h
  | some s =>
      obtain ⟨c, w', low⟩ := s
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hm, hc, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit h
      rw [← h] at hd
      subst hm hc
      have hdec := referenceSearch_decode answers messages L hs
      have hw : referenceDigits answers messages L = w' := by unfold referenceDigits; rw [hs]; rfl
      have hdw : digits = w' := Option.some.inj (hd.symm.trans hdec)
      rcases hne with hne | hne
      · exact hne rfl
      · exact hne (hdw.trans hw.symm)

theorem referenceInput_ne_pad (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    (hpad : pad.1 ≠ 0) : referenceInput answers messages L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers messages L with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨-, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit h
      exact hpad hp.symm
/-- Stage 2 (C3, #866 `WotsExtract.xor_one_inj`). -/
theorem xor_one_inj' {a b : BitVec 64} (h : a ^^^ 1 = b ^^^ 1) : a = b := by
  have := congrArg (· ^^^ (1 : BitVec 64)) h
  simpa [BitVec.xor_assoc] using this
/-- Stage 2 (C3, #866 `referenceInput_ne_pad`): a row whose 12-byte pad is nonzero or whose high-word mask is
nonzero (row high word `≠ 1`) is not the reference row. -/
theorem referenceInput_ne_padW (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    (hpad : pad.1 ≠ 0 ∨ pad.2.2 ≠ 0) : referenceInput answers messages L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers messages L with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨-, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit h
      have hh := BC.layerEncodingRow_hi_eq h
      rcases hpad with hpad | hpad
      · exact hpad hp.symm
      · exact hpad (xor_one_inj' hh).symm

/-- Equality with the reference row fixes the authenticated message and the pads, whichever permitted half a
witness opens (configuration (1)+(2)). -/
theorem referenceInput_eq_msg_pad (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    (h : referenceInput answers messages L = some (encRow L msg ctr pad)) :
    msg = messages L ∧ pad.1 = 0 ∧ pad.2.2 = 0 := by
  unfold referenceInput at h
  cases hs : referenceSearch answers messages L with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hm, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit h
      have hh := BC.layerEncodingRow_hi_eq h
      exact ⟨hm.symm, hp.symm, (xor_one_inj' hh).symm⟩

theorem referenceInput_ne_msg (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    (hne : msg ≠ messages L) : referenceInput answers messages L ≠ some (encRow L msg ctr pad) :=
  fun h => hne (referenceInput_eq_msg_pad answers messages L msg ctr pad hfitRef hfit h).1

/-- A row with a non-honest message or nonzero pads is none of the search's honest rows. -/
theorem notSearched_of_ne (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    (hne : msg ≠ messages L ∨ pad.1 ≠ 0 ∨ pad.2.2 ≠ 0) :
    NotSearched answers messages L (encRow L msg ctr pad) := by
  intro found _ c _ heq
  obtain ⟨hm, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit heq.symm
  have hh := BC.layerEncodingRow_hi_eq heq.symm
  rcases hne with hne | hne | hne
  · exact hne hm.symm
  · exact hne hp.symm
  · exact hne (xor_one_inj' hh).symm

theorem canonical_word_cases {lay : Layer} {refDigest candDigest : Digest} {refDigits candDigits : List Nat}
    (hr : WCT9.CanonicalPolicy.decode lay refDigest = some refDigits)
    (hc : WCT9.CanonicalPolicy.decode lay candDigest = some candDigits) :
    candDigits = refDigits ∨
      (∃ i, i < chainCount lay ∧ candDigits.getD i 0 + 1 = refDigits.getD i 0 ∧
        ∀ j, j < chainCount lay → j ≠ i → refDigits.getD j 0 ≤ candDigits.getD j 0) ∨
      (∃ i, i < chainCount lay ∧ candDigits.getD i 0 + 2 ≤ refDigits.getD i 0) ∨
      (∃ i j, i < chainCount lay ∧ j < chainCount lay ∧ i ≠ j ∧
        candDigits.getD i 0 < refDigits.getD i 0 ∧ candDigits.getD j 0 < refDigits.getD j 0) := by
  rcases word_cases hr hc with he | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hi, hj⟩
  · exact Or.inl he
  · refine Or.inr (Or.inl ⟨i.val, ?_, hi.2.2.1, ?_⟩)
    · simpa only [normalLayer_chainCount] using (show i.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from i.isLt)
    · intro j hj hji
      have hj' : j < chainCount (WCT9.CanonicalPolicy.normalLayer lay) := by
        rw [normalLayer_chainCount]; exact hj
      exact hi.2.2.2 ⟨j, hj'⟩ (fun h => hji (congrArg Fin.val h))
  · refine Or.inr (Or.inr (Or.inl ⟨i.val, ?_, hi⟩))
    simpa only [normalLayer_chainCount] using (show i.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from i.isLt)
  · refine Or.inr (Or.inr (Or.inr ⟨i.val, j.val, ?_, ?_, ?_, hi, hj⟩))
    · simpa only [normalLayer_chainCount] using (show i.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from i.isLt)
    · simpa only [normalLayer_chainCount] using (show j.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from j.isLt)
    · exact fun h => hij (Fin.ext h)

section mono
variable {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace trace' : List Entry}
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers messages trace a)
    (hsub : ∀ e ∈ trace, e ∈ trace') : ContactAt answers messages trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, ClaudeWCT.W9.T3.Security.Wots.seenRowW_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers messages trace a)
    (hsub : ∀ e ∈ trace, e ∈ trace') : TwoEdgeAt answers messages trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, ClaudeWCT.W9.T3.Security.Wots.seenRowW_mono h1 hsub,
    ClaudeWCT.W9.T3.Security.Wots.seenRowW_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers messages trace L)
    (hsub : ∀ e ∈ trace, e ∈ trace') : EncodingMatchAt answers messages trace' L := by
  obtain ⟨message, counter, pad, answer, hfit, hm, hne, hd⟩ := h
  exact ⟨message, counter, pad, answer, hfit, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers messages trace a)
    (hsub : ∀ e ∈ trace, e ∈ trace') : MarkerAt answers messages trace' a := by
  obtain ⟨message, counter, pad, answer, digits, hfit, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, pad, answer, digits, hfit, hsub _ hm, hne, hd, hl, hu⟩
end mono
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_SeccLaw ====
section

namespace ClaudeWCT.W9.T3.Security.SeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.SeccLaw
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9SeccLaw : Fintype Coordinate := coordinateFintype
noncomputable def completedExperiment (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    PMF (PaddedGame.TraceResult × Correctness.Answers) :=
  (PaddedGame.tracedExperiment adversary q hq).bind fun result =>
    (PMF.uniformOfFintype CompletionTables).map fun tables =>
      (result, completeWith result.2.2.base.source.2 tables)
theorem completed_agrees (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (completedExperiment adversary q hq).support) :
    z.1 ∈ (PaddedGame.tracedExperiment adversary q hq).support ∧
      ∀ input answer, SourceReplay.known z.1.2.2.base.source.2 input = some answer → z.2 input = answer := by
  unfold completedExperiment at hz
  rw [PMF.mem_support_bind_iff] at hz
  obtain ⟨result, hresult, hz⟩ := hz
  rw [PMF.support_map] at hz
  obtain ⟨tables, -, rfl⟩ := hz
  exact ⟨hresult, fun input answer h => completeWith_agrees _ tables input answer h⟩
theorem completed_trace_event (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : PaddedGame.TraceResult → Prop) :
    Pr[fun z => event z.1 | completedExperiment adversary q hq] =
      Pr[event | PaddedGame.tracedExperiment adversary q hq] := by
  have hmap : (Prod.fst <$> completedExperiment adversary q hq : PMF _) =
      PaddedGame.tracedExperiment adversary q hq := by
    unfold completedExperiment
    rw [PMF.monad_map_eq_map, PMF.map_bind]
    conv_rhs => rw [← PMF.bind_pure (PaddedGame.tracedExperiment adversary q hq)]
    congr 1
    funext result
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  rw [← hmap, probEvent_map]
  rfl
abbrev SampleClass := PaddedGame.TraceResult × Correctness.Answers → SigGolfCandidate.T3.Spec.Domain → Prop
noncomputable def sampleCharge (cls : SampleClass) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Nat :=
  classCharge (cls z) q (QueryRecorded.recordedTrace z.1).events
noncomputable def expectedCharge (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (cls : SampleClass) : ENNReal :=
  ∑' z, completedExperiment adversary q hq z * (sampleCharge cls q z : ENNReal)
theorem expectedCharge_four_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (A B C D : SampleClass)
    (hAB : ∀ z input, ¬(A z input ∧ B z input)) (hAC : ∀ z input, ¬(A z input ∧ C z input))
    (hAD : ∀ z input, ¬(A z input ∧ D z input)) (hBC : ∀ z input, ¬(B z input ∧ C z input))
    (hBD : ∀ z input, ¬(B z input ∧ D z input)) (hCD : ∀ z input, ¬(C z input ∧ D z input)) :
    expectedCharge adversary q hq A + expectedCharge adversary q hq B + expectedCharge adversary q hq C +
      expectedCharge adversary q hq D ≤ q := by
  have hpoint : ∀ z, (sampleCharge A q z : ENNReal) + sampleCharge B q z + sampleCharge C q z + sampleCharge D q z ≤ q := by
    intro z
    have h1 := classCharge_or (A z) (B z) (hAB z) q (QueryRecorded.recordedTrace z.1).events
    have h2 := classCharge_or (fun input => A z input ∨ B z input) (C z)
      (fun input h => h.1.elim (fun ha => hAC z input ⟨ha, h.2⟩) (fun hb => hBC z input ⟨hb, h.2⟩)) q
      (QueryRecorded.recordedTrace z.1).events
    have h3 := classCharge_or (fun input => (A z input ∨ B z input) ∨ C z input) (D z)
      (fun input h => h.1.elim (fun h' => h'.elim (fun ha => hAD z input ⟨ha, h.2⟩)
        (fun hb => hBD z input ⟨hb, h.2⟩)) (fun hc => hCD z input ⟨hc, h.2⟩)) q
      (QueryRecorded.recordedTrace z.1).events
    have hle := classCharge_le (fun input => ((A z input ∨ B z input) ∨ C z input) ∨ D z input) q
      (QueryRecorded.recordedTrace z.1).events
    unfold sampleCharge
    exact_mod_cast (show _ ≤ q by omega)
  unfold expectedCharge
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ = ∑' z, completedExperiment adversary q hq z *
          ((sampleCharge A q z : ENNReal) + sampleCharge B q z + sampleCharge C q z + sampleCharge D q z) := by
      congr 1; funext z; ring
    _ ≤ ∑' z, completedExperiment adversary q hq z * (q : ENNReal) :=
      ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hpoint z)
    _ = q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
end ClaudeWCT.W9.T3.Security.SeccLaw

namespace ClaudeWCT.W9.T3.Security.PairedSeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.SeccLaw
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9SeccLaw : Fintype Coordinate := coordinateFintype
noncomputable def completedExperiment (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    PMF (PairedOuter.PaddedGame.TraceResult × Correctness.Answers) :=
  (PairedOuter.PaddedGame.tracedExperiment adversary q hq).bind fun result =>
    (PMF.uniformOfFintype CompletionTables).map fun tables =>
      (result, completeWith result.2.2.base.source.2 tables)
theorem completed_agrees (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PairedOuter.PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (completedExperiment adversary q hq).support) :
    z.1 ∈ (PairedOuter.PaddedGame.tracedExperiment adversary q hq).support ∧
      ∀ input answer, SourceReplay.known z.1.2.2.base.source.2 input = some answer → z.2 input = answer := by
  unfold completedExperiment at hz
  rw [PMF.mem_support_bind_iff] at hz
  obtain ⟨result, hresult, hz⟩ := hz
  rw [PMF.support_map] at hz
  obtain ⟨tables, -, rfl⟩ := hz
  exact ⟨hresult, fun input answer h => completeWith_agrees _ tables input answer h⟩
theorem completed_trace_event (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : PairedOuter.PaddedGame.TraceResult → Prop) :
    Pr[fun z => event z.1 | completedExperiment adversary q hq] =
      Pr[event | PairedOuter.PaddedGame.tracedExperiment adversary q hq] := by
  have hmap : (Prod.fst <$> completedExperiment adversary q hq : PMF _) =
      PairedOuter.PaddedGame.tracedExperiment adversary q hq := by
    unfold completedExperiment
    rw [PMF.monad_map_eq_map, PMF.map_bind]
    conv_rhs => rw [← PMF.bind_pure (PairedOuter.PaddedGame.tracedExperiment adversary q hq)]
    congr 1
    funext result
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  rw [← hmap, probEvent_map]
  rfl
abbrev SampleClass := PairedOuter.PaddedGame.TraceResult × Correctness.Answers → SigGolfCandidate.T3.Spec.Domain → Prop
noncomputable def sampleCharge (cls : SampleClass) (q : Nat) (z : PairedOuter.PaddedGame.TraceResult × Correctness.Answers) : Nat :=
  classCharge (cls z) q (QueryRecorded.recordedTrace z.1).events
noncomputable def expectedCharge (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (cls : SampleClass) : ENNReal :=
  ∑' z, completedExperiment adversary q hq z * (sampleCharge cls q z : ENNReal)
theorem expectedCharge_four_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (A B C D : SampleClass)
    (hAB : ∀ z input, ¬(A z input ∧ B z input)) (hAC : ∀ z input, ¬(A z input ∧ C z input))
    (hAD : ∀ z input, ¬(A z input ∧ D z input)) (hBC : ∀ z input, ¬(B z input ∧ C z input))
    (hBD : ∀ z input, ¬(B z input ∧ D z input)) (hCD : ∀ z input, ¬(C z input ∧ D z input)) :
    expectedCharge adversary q hq A + expectedCharge adversary q hq B + expectedCharge adversary q hq C +
      expectedCharge adversary q hq D ≤ q := by
  have hpoint : ∀ z, (sampleCharge A q z : ENNReal) + sampleCharge B q z + sampleCharge C q z + sampleCharge D q z ≤ q := by
    intro z
    have h1 := classCharge_or (A z) (B z) (hAB z) q (QueryRecorded.recordedTrace z.1).events
    have h2 := classCharge_or (fun input => A z input ∨ B z input) (C z)
      (fun input h => h.1.elim (fun ha => hAC z input ⟨ha, h.2⟩) (fun hb => hBC z input ⟨hb, h.2⟩)) q
      (QueryRecorded.recordedTrace z.1).events
    have h3 := classCharge_or (fun input => (A z input ∨ B z input) ∨ C z input) (D z)
      (fun input h => h.1.elim (fun h' => h'.elim (fun ha => hAD z input ⟨ha, h.2⟩)
        (fun hb => hBD z input ⟨hb, h.2⟩)) (fun hc => hCD z input ⟨hc, h.2⟩)) q
      (QueryRecorded.recordedTrace z.1).events
    have hle := classCharge_le (fun input => ((A z input ∨ B z input) ∨ C z input) ∨ D z input) q
      (QueryRecorded.recordedTrace z.1).events
    unfold sampleCharge
    exact_mod_cast (show _ ≤ q by omega)
  unfold expectedCharge
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ = ∑' z, completedExperiment adversary q hq z *
          ((sampleCharge A q z : ENNReal) + sampleCharge B q z + sampleCharge C q z + sampleCharge D q z) := by
      congr 1; funext z; ring
    _ ≤ ∑' z, completedExperiment adversary q hq z * (q : ENNReal) :=
      ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hpoint z)
    _ = q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
end ClaudeWCT.W9.T3.Security.PairedSeccLaw
end
-- ==== merged from ClaudeWCT_W9_New_G5_PaddedExtraction ====
section

namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped verifyP)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP checkForgeryP)
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem verifyP_hashOnly (message : Message) (publicKey : Digest) (witness : WBytes) :
    Security.SourceReplay.HashOnly (verifyP message publicKey witness) := by
  apply SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3M.publicOnly_verifyP message publicKey witness)
  intro input h
  rcases input with (sample | query) | coordinate
  · exact h.elim
  · trivial
  · trivial
def ActualHit (answers : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∃ (position : ClaudeWCT.W9.T3M.Extract.Pos) (actual : HashInput) (prior : LazyPrivate.State),
    position.Bounded ∧ ClaudeWCT.W9.T3M.Extract.posOf actual = some position ∧
    (⟨prior, .inl (.inr actual), answers (.inl (.inr actual))⟩ : FirstHit.QueryEvent) ∈ events ∧
    ClaudeWCT.W9.T3M.Extract.HashHitAt answers position
      (ClaudeWCT.W9.T3M.Extract.honestInput answers position) actual
theorem hit_recorded {α : Type} (program : M α) (hp : Security.SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hit : ClaudeWCT.W9.T3M.Extract.HitIn answers (SigGolfCandidate.T3M.SecurityExtraction.queried answers program)) :
    ActualHit answers result.events := by
  obtain ⟨position, actual, hbounded, hquery, hpos, hhit⟩ := ClaudeWCT.W9.T3M.Extract.hitIn_posOf hit
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence program hp before
    result hr answers ha actual hquery
  exact ⟨position, actual, prior, hbounded, hpos, hevent, hhit⟩
/-- A good layer whose encoding row carries a nonzero 12-byte pad or (C2/C3 FULL) a row high word other than the
honest 1. -/
def PadAt (answers : Answers) (witness : WBytes) (index : Nat) : Prop :=
  ∃ lay : Layer, ClaudeWCT.W9.T3M.Extract.Good answers witness index lay ∧
    ¬ (ClaudeWCT.W9.T3M.wbcPad witness index lay = 0 ∧ ClaudeWCT.W9.T3M.wbcHigh witness index lay = 1)
def Conclusion (answers : Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
      (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
        FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧
      (ActualHit answers events ∨
        (∃ lay : Layer, ClaudeWCT.W9.T3M.Extract.Diverge answers witness (WCT9.digestIndex digestAnswer) lay
          (events.map FirstHit.QueryEvent.input) ∧
          ∀ above : Layer, above.val < lay.val →
            ClaudeWCT.W9.T3M.Extract.Good answers witness (WCT9.digestIndex digestAnswer) above) ∨
        PadAt answers witness (WCT9.digestIndex digestAnswer) ∨
        ((∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ answers witness (WCT9.digestIndex digestAnswer) lay) ∧
          ClaudeWCT.W9.T3M.WctExtract.WctHonest answers digestAnswer witness))
theorem verifyP_extracted_in {α : Type} (program : M α) (hp : Security.SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (message : Message) (publicKey : Digest) (witness : WBytes)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP message publicKey witness) = true)
    (hsub : ∀ input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (verifyP message publicKey witness),
      input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers program) :
    Conclusion answers message witness result.events := by
  obtain ⟨N, hcounter, hdigest, hquery, hshape, halt⟩ :=
    ClaudeWCT.W9.T3M.Extract.verifyP_extract_normal answers message publicKey witness hpk hv
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence program hp before
    result hr answers ha _ (hsub _ hquery)
  have hans : answers (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness))))) = N := hdigest
  refine ⟨N, hcounter, hdigest, ⟨prior, by simpa only [hans] using hevent⟩, hshape, ?_⟩
  rcases halt with hhit | ⟨lay, hdiv, hgood⟩ | ⟨hgood, hfts⟩
  · exact Or.inl (hit_recorded program hp before result hr answers ha (hhit.mono hsub))
  · refine Or.inr (Or.inl ⟨lay, hdiv.mono ?_, hgood⟩)
    intro input hin
    rw [FirstHit.recorded_inputs program hp before result hr answers ha,
      SigGolfCandidate.T3.Security.PaddedExtraction.queried_eq]
    exact hsub _ hin
  · by_cases hz : ∀ lay : Layer, ClaudeWCT.W9.T3M.wbcPad witness (WCT9.digestIndex N) lay = 0 ∧
        ClaudeWCT.W9.T3M.wbcHigh witness (WCT9.digestIndex N) lay = 1
    · exact Or.inr (Or.inr (Or.inr ⟨fun lay => ⟨hgood lay, hz lay⟩, hfts⟩))
    · obtain ⟨lay, hlay⟩ := not_forall.mp hz
      exact Or.inr (Or.inr (Or.inl ⟨lay, hgood lay, hlay⟩))
theorem verifyP_recorded (message : Message) (publicKey : Digest) (witness : WBytes)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (verifyP message publicKey witness) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0) (hwin : result.value = true) :
    Conclusion answers message witness result.events := by
  have hp := verifyP_hashOnly message publicKey witness
  have hv := (SourceReplay.resolves_of_run (verifyP message publicKey witness) hp before
    (result.value, result.state) (FirstHit.recorded_support _ _ _ hr)).eval answers ha
  rw [hwin] at hv
  exact verifyP_extracted_in _ hp before result hr answers ha message publicKey witness hpk hv (fun _ h => h)
noncomputable def reference : FirstHit.Reference := fun state input =>
  (ClaudeWCT.W9.T3M.Extract.posOf input).map (ClaudeWCT.W9.T3M.Extract.honestInput (SourceReplay.answers state))
theorem reference_of_pos (state : LazyPrivate.State) (input : HashInput) (position : ClaudeWCT.W9.T3M.Extract.Pos)
    (hpos : ClaudeWCT.W9.T3M.Extract.posOf input = some position) :
    reference state input = some (ClaudeWCT.W9.T3M.Extract.honestInput (SourceReplay.answers state) position) := by
  simp only [reference, hpos, Option.map_some]
theorem ActualHit.mono {answers : Answers} {events events' : List FirstHit.QueryEvent}
    (hit : ActualHit answers events) (hsub : ∀ event ∈ events, event ∈ events') :
    ActualHit answers events' := by
  obtain ⟨position, actual, prior, hbounded, hpos, hevent, hhit⟩ := hit
  exact ⟨position, actual, prior, hbounded, hpos, hsub _ hevent, hhit⟩
theorem Conclusion.mono {answers : Answers} {message : Message} {witness : WBytes}
    {events events' : List FirstHit.QueryEvent} (h : Conclusion answers message witness events)
    (hsub : ∀ event ∈ events, event ∈ events') : Conclusion answers message witness events' := by
  obtain ⟨N, hcounter, hdigest, ⟨prior, hevent⟩, hshape, halt⟩ := h
  refine ⟨N, hcounter, hdigest, ⟨prior, hsub _ hevent⟩, hshape, ?_⟩
  rcases halt with hhit | ⟨lay, hdiv, hgood⟩ | hpad | hgood
  · exact Or.inl (hhit.mono hsub)
  · refine Or.inr (Or.inl ⟨lay, hdiv.mono ?_, hgood⟩)
    intro input hin
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hin
    exact List.mem_map.mpr ⟨event, hsub _ hevent, rfl⟩
  · exact Or.inr (Or.inr (Or.inl hpad))
  · exact Or.inr (Or.inr (Or.inr hgood))
theorem padded_known_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun result => result.2.2.base.source.1 ≤ q ∧
      FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) |
      PaddedGame.tracedExperiment adversary q hq] ≤ q / (2 : ENNReal) ^ 128 :=
  GameWith.Recorded.known_public_hit_bound PaddedGame.checker reference adversary q hq
theorem check_recorded (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (checkForgeryP publicKey log forgery) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0) (hwin : result.value = true) :
    Fresh log forgery ∧ ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
      Conclusion answers message witness result.events := by
  have hp := check_hashOnly publicKey log forgery
  have hw := (SourceReplay.resolves_of_run _ hp before (result.value, result.state)
    (FirstHit.recorded_support _ _ _ hr)).eval answers ha
  rw [hwin] at hw
  obtain ⟨hfresh, message, witness, hof, hv, hsub⟩ := check_accepting answers publicKey log forgery hw
  exact ⟨hfresh, message, witness, hof,
    verifyP_extracted_in _ hp before result hr answers ha message publicKey witness hpk hv hsub⟩
theorem verdict_recorded (publicKey : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker publicKey interaction) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0) (hwin : result.value = true) :
    interaction.2.length ≤ 2 ^ 32 ∧ ∃ forgery, interaction.1 = some forgery ∧ Fresh interaction.2 forgery ∧
      ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
        Conclusion answers message witness result.events := by
  cases hf : interaction.1 with
  | none =>
      simp only [GameWith.verdict, hf, FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [GameWith.verdict, hf, PaddedGame.checker] at hr
      obtain ⟨checked, hchecked, last, hlast, hvalue, hevents, hstate⟩ :=
        FirstHit.record_bind_support _ _ before result hr
      rw [FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hlast
      subst last
      simp only [List.append_nil] at hevents
      have hand : (decide (interaction.2.length ≤ 2 ^ 32) && checked.value) = true := hvalue.symm.trans hwin
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hand
      obtain ⟨hlength, hcheckedWin⟩ := hand
      have hcheck := check_recorded publicKey interaction.2 forgery before checked hchecked answers
        (by simpa only [hstate] using ha) hpk hcheckedWin
      obtain ⟨hfresh, message, witness, hof, hconclusion⟩ := hcheck
      exact ⟨hlength, forgery, rfl, hfresh, message, witness, hof, hevents ▸ hconclusion⟩
def GameConclusion (adversary : AdversaryP) (answers : Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ Fresh interaction.value.2 forgery ∧
      ∃ message witness, WitnessOf answers generated.value.1 forgery message witness ∧
        Conclusion answers message witness result.events
theorem game_recorded (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) : GameConclusion adversary answers result := by
  unfold GameWith.idealGame at hr
  obtain ⟨generated, hgenerated, rest, hrest, hvalue, hevents, hstate⟩ :=
    FirstHit.record_bind_support _ _ (∅, ∅) result hr
  obtain ⟨interaction, hinteraction, checked, hchecked, hrestValue, hrestEvents, hrestState⟩ :=
    FirstHit.record_bind_support _ _ generated.state rest hrest
  have hgeneratedState : SourceReplay.Extends generated.state result.state := by
    rw [hstate]
    exact SourceReplay.run_extends _ generated.state (rest.value, rest.state)
      (FirstHit.recorded_support _ _ _ hrest)
  have hgen : evalWithAnswerFn answers keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hgenerated)).eval answers
        (fun input answer hk => ha input answer
          (SourceReplay.known_mono generated.state result.state hgeneratedState hk))
  have hpk : generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 := by
    rw [← hgen]
    exact ClaudeWCT.W9.T3M.Extract.keygen_pk answers
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
    simpa only [hstate, hrestState] using ha
  have hw : checked.value = true := hrestValue.symm.trans (hvalue.symm.trans hwin)
  obtain ⟨hlength, forgery, hforgery, hfresh, message, witness, hof, hconclusion⟩ :=
    verdict_recorded generated.value.1 interaction.value interaction.state checked hchecked answers hac hpk hw
  refine ⟨generated, hgenerated, interaction, hinteraction, hpk, hlength, forgery, hforgery, hfresh, message,
    witness, hof, hconclusion.mono ?_⟩
  intro event he
  rw [hevents, hrestEvents]
  exact List.mem_append_right _ (List.mem_append_right _ he)
theorem traced_record_support (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.recordedTrace result ∈ support
      (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)) := by
  have hm : QueryRecorded.recordedTrace result ∈
      (QueryRecorded.recordedTrace <$> PaddedGame.tracedExperiment adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map, PMF.support_map]
    exact ⟨result, hr, rfl⟩
  rw [PaddedGame.traced_record_erasure, MonitoredPrivate.pmf_support] at hm
  exact hm
theorem traced_game (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer)
    (hwin : result.1 = true) : GameConclusion adversary answers (QueryRecorded.recordedTrace result) :=
  game_recorded adversary _ (traced_record_support adversary budget hbudget result hr) answers ha hwin
end ClaudeWCT.W9.T3.Security.PaddedExtraction
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_SeccSufSigned ====
section

namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9seccSufSigned : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def SignerComplete (answers : Correctness.Answers) : Prop :=
  (∀ (rho : Digest) (m : Message),
      (evalWithAnswerFn answers (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit)).isSome) ∧
    ∀ (lay : Layer), lay ≠ 0 → ∀ (tree leaf : Nat) (msg : WCT9.LayerMsg), tree < 2 ^ 25 → leaf < 2 ^ height lay →
      (evalWithAnswerFn answers (WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay))).isSome
def CaseCAt (answers : Correctness.Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < WCT9.digestVerifyWindow ∧
    evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
    (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
      FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧
    (∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ answers witness (WCT9.digestIndex digestAnswer) lay) ∧
    ClaudeWCT.W9.T3M.WctExtract.WctHonest answers digestAnswer witness ∧ SignerComplete answers
def SignedDigest (log : QueryLog Requests) (message : Message) (witness : WBytes) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ ∃ signature, entry.2 = some signature ∧
    signature.rho = wrho witness
def GameCaseC (adversary : AdversaryP) (answers : Correctness.Answers) (signed : Prop → Prop)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        signed (SignedDigest interaction.value.2 message witness) ∧
        CaseCAt answers message witness result.events
abbrev CaseCSigned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseC adversary z.2 id (QueryRecorded.recordedTrace z.1)
theorem logged_resolves {α : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : LazyPrivate.State) (result : (α × QueryLog Requests) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.loggedWith (FullGame.authenticatedSign published) program)
      before)) :
    ∀ entry ∈ result.1.2, SourceReplay.Resolves result.2 (FullGame.authenticatedSign published entry.1) entry.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FullGame.loggedWith_pure, LazyPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [FullGame.loggedWith_world, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, _, hr⟩ := hr
          exact ih middle.1 middle.2 result hr
      | inr request =>
          rw [FullGame.loggedWith_request, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, hm, hr⟩ := hr
          rw [LazyPrivate.run_map, support_map] at hr
          obtain ⟨last, hl, rfl⟩ := hr
          intro entry he
          rcases List.mem_cons.mp he with he | he
          · subst entry
            exact (SourceReplay.resolves_of_run _ (CountedPrivate.authenticatedSign_hashOnly published request)
              before middle hm).mono (SourceReplay.run_extends _ middle.2 last hl)
          · exact ih middle.1 middle.2 last hl entry he
def payloadForNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (message : Message) :
    M (Option Signature) := do
  let some (_, output) ← WCT9.digestSearch rho message 0 WCT9.digestAttemptLimit | pure none
  let forest ← WCT9.signForest (WCT9.digestIndex output) output
  let some pieces ← WCT9.signLayersBC cache (WCT9.digestIndex output) 4 (.pair forest.2.1 forest.2.2) | pure none
  pure (some (WCT9.assembledSignature rho forest.1 pieces))
theorem signPayload_nonce (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    WCT9.Rev3.signPayload cache message =
      (privateNonce message >>= fun rho => payloadForNonce cache rho message) := by
  rw [WCT9.Rev3.signPayload_eq]
  rfl
theorem eval_authenticatedSign (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) :
    evalWithAnswerFn answers (FullGame.authenticatedSign published request) =
      if request.cache = published then
        evalWithAnswerFn answers (payloadForNonce published
          (evalWithAnswerFn answers (privateNonce request.message)) request.message)
      else none := by
  unfold FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    show evalWithAnswerFn answers (WCT9.Rev3.signPayload request.cache request.message) = _
    rw [signPayload_nonce, evalWithAnswerFn_bind, hc]
  · rw [if_neg hc, if_neg hc, evalWithAnswerFn_pure]
theorem authenticatedSign_payload (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (sig : Signature)
    (h : evalWithAnswerFn answers (FullGame.authenticatedSign published request) = some sig) :
    request.cache = published ∧ sig.rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      evalWithAnswerFn answers (payloadForNonce published sig.rho request.message) = some sig := by
  rw [eval_authenticatedSign] at h
  by_cases hc : request.cache = published
  · rw [if_pos hc] at h
    have hrho : sig.rho = evalWithAnswerFn answers (privateNonce request.message) := by
      unfold payloadForNonce at h
      simp only [evalWithAnswerFn_bind] at h
      generalize evalWithAnswerFn answers (WCT9.digestSearch (evalWithAnswerFn answers (privateNonce request.message))
        request.message 0 WCT9.digestAttemptLimit) = found at h
      rcases found with _ | ⟨_, output⟩
      · simp at h
      · simp only [evalWithAnswerFn_bind] at h
        generalize evalWithAnswerFn answers (WCT9.signLayersBC published (WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn answers (WCT9.signForest (WCT9.digestIndex output) output)).2.1
            (evalWithAnswerFn answers (WCT9.signForest (WCT9.digestIndex output) output)).2.2)) = layers at h
        rcases layers with _ | pieces
        · simp at h
        · simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          rw [← h]
          rfl
    exact ⟨hc, hrho, by rw [hrho]; exact h⟩
  · rw [if_neg hc] at h
    cases h
end ClaudeWCT.W9.T3.Security.BPB
end
-- ==== merged from T3_Secc_WotsTransport ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
noncomputable def completionComp : ProbComp SeccLaw.CompletionTables :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun publicTable => pure (privateTable, publicTable)
theorem completionComp_eq :
    (liftM completionComp : PMF SeccLaw.CompletionTables) = PMF.uniformOfFintype SeccLaw.CompletionTables := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.uniformOfFintype_apply, ← PMF.probOutput_eq_apply]
  have hl : Pr[= (a, b) | (liftM completionComp : PMF SeccLaw.CompletionTables)] = Pr[= (a, b) | completionComp] := by
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, MonitoredPrivate.event_lift]
  rw [hl]
  unfold completionComp
  change Pr[=(a, b) | (($ᵗ FullGame.FullTable : ProbComp _) >>= fun x =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun y => pure (id x, id y))] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map, probOutput_uniformSample]
  rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)), ← Nat.cast_mul]
  congr 2
  rw [← Fintype.card_prod]
theorem pmf_probEvent_mono {α : Type} (p : PMF α) {E F : α → Prop} (h : ∀ x ∈ p.support, E x → F x) :
    Pr[E | p] ≤ Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hE : E x
    · rw [if_pos hE, if_pos (h x hx hE)]
    · rw [if_neg hE]
      exact zero_le
  · have hz' : p x = 0 := (PMF.apply_eq_zero_iff p x).mpr hx
    have hz : Pr[= x | p] = 0 := by
      rw [PMF.probOutput_eq_apply]
      exact hz'
    split_ifs <;> simp [hz, hz']
theorem restrict_uniform {β : Type} (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V)
    (k : SeccLaw.PublicTable → ProbComp β) :
    𝒮[($ᵗ (V → HashOutput) : ProbComp _) >>= fun table =>
        k (table ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub)] =
      𝒮[($ᵗ SeccLaw.PublicTable : ProbComp _) >>= k] := by
  rw [FiniteRowSplit.public_table_bind SeccLaw.publicUniverse V hsub]
  apply evalSPMF_bind_congr'
  intro chainTable
  have hc : ∀ extra, (FiniteRowSplit.publicTableEquiv SeccLaw.publicUniverse V hsub).symm (chainTable, extra) ∘
      FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub = chainTable := by
    intro extra
    funext query
    rw [Function.comp_apply]
    exact FiniteRowSplit.publicTableEquiv_reconstruct SeccLaw.publicUniverse V hsub chainTable extra query
  simp only [hc]
  exact evalSPMF_bind_const_neverFails _ (by simp) _
theorem completeWith_eq_cut (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : V → HashOutput) :
    SeccLaw.completeWith state (privateTable, publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) =
      cut state (fillAnswers V state privateTable publicTable) := by
  funext query
  rcases query with (n | x) | c
  · rfl
  · change (state.2 x).getD (SeccLaw.publicFill (publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) x) =
      (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then
        (state.2 x).getD (SphincsSecurity.Concrete.finiteHashAnswer ∅ V publicTable x) else (0 : HashOutput))
    cases hx : state.2 x with
    | some v =>
        rw [if_pos (show x ∈ SeccLaw.publicUniverse ∨ (some v).isSome = true from Or.inr rfl),
          Option.getD_some, Option.getD_some]
    | none =>
        rw [Option.getD_none, Option.getD_none]
        unfold SeccLaw.publicFill
        by_cases hu : x ∈ SeccLaw.publicUniverse
        · rw [dif_pos hu, if_pos (Or.inl hu), SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x (hsub hu) rfl,
            Function.comp_apply]
          rfl
        · rw [dif_neg hu, if_neg (fun h => h.elim hu (fun h' => by simp at h'))]
  · rfl
end Ref
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsReference ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9WotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_w9WotsReference :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def signCharge (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : SigGolfCandidate.T3.Cache) :
    QueryImpl (OracleWorld + Requests) (WriterT (QueryLog Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + Requests) α) : OracleComp RefWorld (α × QueryLog Requests) :=
  (simulateQ (offlineImpl T published) program).run
noncomputable def offlineGame (T : Answers) (adversary : AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)
noncomputable def referenceGame (T : Answers) (adversary : AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q
noncomputable def offlineRun (T : Answers) (adversary : AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))
noncomputable def referenceInputs (adversary : AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (GameWith.idealGame PaddedGame.checker adversary)
noncomputable def referenceComp (adversary : AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q
noncomputable def referenceExperiment (adversary : AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9WotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_w9WotsReference :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def signCharge (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (PairedOuter.FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option SigGolfCandidate.Research.SharedForest.Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : SigGolfCandidate.T3.Cache) :
    QueryImpl (OracleWorld + ClaudeWCT.W9.T3M.Final.Paired.Requests) (WriterT (QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + ClaudeWCT.W9.T3M.Final.Paired.Requests) α) : OracleComp RefWorld (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :=
  (simulateQ (offlineImpl T published) program).run
noncomputable def offlineGame (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 result)
noncomputable def referenceGame (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q
noncomputable def offlineRun (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))
noncomputable def referenceInputs (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary)
noncomputable def referenceComp (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q
noncomputable def referenceExperiment (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem referenceGame_congr (T T' : Answers)
    (hkey : evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen)
    (hkeyCharge : (SigGolfCandidate.T3.Security.SourceReplay.queried T keygen).length =
      (SigGolfCandidate.T3.Security.SourceReplay.queried T' keygen).length)
    (hsign : ∀ published request,
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) =
        evalWithAnswerFn T' (PairedOuter.FullGame.authenticatedSign published request))
    (hsignCharge : ∀ published request,
      (SigGolfCandidate.T3.Security.SourceReplay.queried T (PairedOuter.FullGame.authenticatedSign published request)).length =
        (SigGolfCandidate.T3.Security.SourceReplay.queried T' (PairedOuter.FullGame.authenticatedSign published request)).length)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    referenceGame T adversary q = referenceGame T' adversary q := by
  have hs (published : SigGolfCandidate.T3.Cache) (request : Request) :
      offlineSign T published request = offlineSign T' published request := by
    unfold offlineSign signCharge
    rw [hsignCharge published request,hsign published request]
  have hi (published : SigGolfCandidate.T3.Cache) :
      offlineImpl T published = offlineImpl T' published := by
    unfold offlineImpl
    have he : offlineSign T published = offlineSign T' published := funext (hs published)
    rw [he]
  have hk : keygenCharge T = keygenCharge T' := hkeyCharge
  unfold referenceGame offlineGame offlineInteraction
  rw [hk,hkey,hi]
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTransportR3 ====
section

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem offlineInteraction_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, []) := rfl
theorem offlineInteraction_world (T : Answers) (published : T3.Cache) {α : Type}
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind', WriterT.run_liftM, bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem offlineInteraction_request (T : Answers) (published : T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun answer =>
        (fun result => (result.1, ⟨request, answer⟩ :: result.2)) <$> offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp
theorem authenticatedSign_hashOnly (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SourceReplay.IsHash
  · exact SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) request.cache.region
  · intro tag
    rcases Classical.em (request.cache = published) with h | h
    · rw [if_pos h]
      exact ClaudeWCT.W9.T3.Security.Signer.signPayload_hashOnly request.cache request.message
    · rw [if_neg h]
      exact SourceQueries.pure_allowed _ _
theorem interaction_counted (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
        (FullGame.loggedWith (FullGame.authenticatedSign published) program)) =
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (offlineInteraction T published program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world, offlineInteraction_world]
        change simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
          (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer))) = _
        rw [SphincsSecurity.QueryCap.counted_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
        rcases input with n | x
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
      · rw [FullGame.loggedWith_request, offlineInteraction_request]
        rw [SphincsSecurity.QueryCap.counted_bind]
        unfold offlineSign
        simp only [bind_assoc, pure_bind]
        rw [SphincsSecurity.QueryCap.counted_bind]
        simp only [simulateQ_bind, fixedWorld_counted_hashOnly T _ (authenticatedSign_hashOnly published request),
          ticks_counted, pure_bind, SphincsSecurity.QueryCap.counted_map, simulateQ_map, simulateQ_pure, ih]
        rfl
end ClaudeWCT.W9.T3.Security.Wots.Ref

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem offlineInteraction_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp PairedOuter.LazyPrivate.Interaction α) = pure (value, []) := rfl
theorem offlineInteraction_world (T : Answers) (published : T3.Cache) {α : Type}
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp PairedOuter.LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind', WriterT.run_liftM, bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem offlineInteraction_request (T : Answers) (published : T3.Cache) {α : Type}
    (request : Request) (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun answer =>
        (fun result => (result.1, ⟨request, answer⟩ :: result.2)) <$> offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp
theorem shared_digest_hashOnly (rho : Digest) (message : Message) : ∀ fuel counter,
    Security.SourceReplay.HashOnly (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter;exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter
      unfold SigGolfCandidate.Research.SharedForest.sharedDigestSearch
      refine SourceQueries.bind_allowed _ (SourceQueries.digest_allowed _ (fun _ => trivial) _ _ _) ?_
      intro output
      split
      · exact SourceQueries.pure_allowed _ _
      · exact ih _

theorem shared_signPayload_hashOnly (cache : T3.Cache) (message : Message) :
    Security.SourceReplay.HashOnly (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  have ht := ClaudeWCT.Bank.Paired.tail_public SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
    (SourceQueries.signTop_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial))
  have hf := ClaudeWCT.Bank.Paired.forest_public SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
  have hout (rho : Digest) (counter : BitVec 32) (output : HashOutput) : Security.SourceReplay.HashOnly
      (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) :=
    SharedQueries.signFromOutput_allowed _ ht (ClaudeWCT.Bank.Paired.forest_allowed _ hf) cache rho counter output
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine SourceQueries.bind_allowed _ (SourceQueries.privateNonce_allowed _ (fun _ => trivial) _) ?_
  intro rho
  refine SourceQueries.bind_allowed _ (shared_digest_hashOnly rho message _ _) ?_
  intro found
  cases found with
  | none => exact SourceQueries.pure_allowed _ _
  | some value =>
      refine SourceQueries.bind_allowed _ (hout rho value.1 value.2) ?_
      intro result
      cases result <;> exact SourceQueries.pure_allowed _ _

theorem authenticatedSign_hashOnly (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SourceReplay.IsHash
  · exact SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) request.cache.region
  · intro tag
    rcases Classical.em (request.cache = published) with h | h
    · rw [if_pos h]
      exact shared_signPayload_hashOnly request.cache request.message
    · rw [if_neg h]
      exact SourceQueries.pure_allowed _ _
theorem interaction_counted (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
        (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program)) =
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (offlineInteraction T published program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [PairedOuter.FullGame.loggedWith_world, offlineInteraction_world]
        change simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
          (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer))) = _
        rw [SphincsSecurity.QueryCap.counted_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
        rcases input with n | x
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
      · rw [PairedOuter.FullGame.loggedWith_request, offlineInteraction_request]
        rw [SphincsSecurity.QueryCap.counted_bind]
        unfold offlineSign
        simp only [bind_assoc, pure_bind]
        rw [SphincsSecurity.QueryCap.counted_bind]
        simp only [simulateQ_bind, fixedWorld_counted_hashOnly T _ (authenticatedSign_hashOnly published request),
          ticks_counted, pure_bind, SphincsSecurity.QueryCap.counted_map, simulateQ_map, simulateQ_pure, ih]
        rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
end
-- ==== merged from ClaudeWCT_WCT9_Honest ====
section

namespace ClaudeWCT.WCT9.Wots
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
inductive FtsPos where
  | chain (coord : Coord) (child : Child) (t : Fin 6) (step : Nat)
  | leaf (coord : Coord) (child : Child)
  | node (coord : Coord) (heap : Nat)
  | forest
  deriving DecidableEq
def FtsPos.Bounded : FtsPos → Prop
  | .chain _ _ _ step => step < 4
  | .leaf _ _ => True
  | .node _ heap => 2 ≤ heap ∧ heap < 128
  | .forest => True
def ftsChainValue (T : Answers) (index : Nat) (coord : Coord) (child : Child) (t : Fin 6) (step : Nat) :
    Digest :=
  evalWithAnswerFn T (chain index coord.val child.val t.val 0 step (seed T index coord.val child.val t))
def ftsHonestInput (T : Answers) (index : Nat) : FtsPos → HashInput
  | .chain coord child t step =>
      pad64 (ftsChainInputW index coord.val child.val t.val step (ftsChainValue T index coord child t step))
  | .leaf coord child =>
      pad64 (leafInputP index coord.val child.val (ftsPrev T index coord.val).1
        (List.ofFn (chainEnd T index coord.val child.val)))
  | .node coord heap =>
      pad64 (wctTopInput coord.val index heap ((coordNodes T index coord).getD (2 * heap) 0)
        (if heap < 4 then (ftsPrev T index coord.val).2 else 0)
        ((coordNodes T index coord).getD (2 * heap + 1) 0))
  | .forest => pad64 (forestInput index (List.ofFn (coordinatePair T index)))
def FtsHonestQuery (T : Answers) (index : Nat) : Query → Prop
  | .inl (.inr input) => ∃ p : FtsPos, p.Bounded ∧ input = ftsHonestInput T index p
  | .inr (.inl tweak) => FtsSeed index tweak
  | _ => False
theorem ftsChainValue_end (T : Answers) (index : Nat) (coord : Coord) (child : Child) (t : Fin 6) :
    ftsChainValue T index coord child t 4 = chainEnd T index coord.val child.val t := rfl
theorem ftsChainValue_revealed (T : Answers) (index : Nat) (coord : Coord) (child : Child) (word : Rank)
    (t : Fin 6) :
    ftsChainValue T index coord child t (4 - wordDigit word t) = chainValue T index coord.val child.val word t := rfl
theorem wctTopInput_zero (coord index heap : Nat) (left right : Digest) :
    wctTopInput coord index heap left 0 right = nodeInput coord index heap left right := by
  unfold wctTopInput nodeInput
  rw [bytesLE_zero16]
theorem ftsHonestQuery_fts {T : Answers} {index : Nat} {q : Query} (h : FtsHonestQuery T index q) :
    FtsQuery index q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · obtain ⟨p, hp, rfl⟩ := (show ∃ p : FtsPos, p.Bounded ∧ input = ftsHonestInput T index p from h)
    cases p with
    | chain coord child t step => exact FtsInput.chain _ coord.isLt child.isLt t.isLt hp
    | leaf coord child => exact FtsInput.leaf coord.isLt child.isLt (by simp)
    | node coord heap =>
      simp only [ftsHonestInput]
      split
      · exact FtsInput.top _ _ _ coord.isLt hp.1 (by omega)
      · rw [wctTopInput_zero]; exact FtsInput.node _ _ coord.isLt hp.1 hp.2
    | forest => exact FtsInput.forest (by simp)
  · exact h
  · exact h.elim
theorem chain_zero' (index coord selected t start : Nat) (v : Digest) :
    chain index coord selected t start 0 v = pure v := rfl
theorem queried_chain_one (T : Answers) (index coord selected t s : Nat) (v : Digest) :
    SourceReplay.queried T (chain index coord selected t s 1 v) =
      [.inl (.inr (pad64 (ftsChainInputW index coord selected t s v)))] := rfl
theorem eval_ftsChain (T : Answers) (index : Nat) (coord : Coord) (child : Child) (t : Fin 6)
    (start count : Nat) :
    evalWithAnswerFn T (chain index coord.val child.val t.val start count
      (ftsChainValue T index coord child t start)) = ftsChainValue T index coord child t (start + count) := by
  unfold ftsChainValue
  rw [eval_chain_add, Nat.zero_add]
theorem eval_childRows_ends (T : Answers) (index coord selected : Nat) (word : Rank) :
    (evalWithAnswerFn T (childRows index coord selected word (List.ofFn (ftsCoef T index coord)))).1 =
      List.ofFn (fun i : Fin 6 => chainEnd T index coord selected i) := by
  obtain ⟨he, -, hend, -⟩ := eval_childRows T index coord selected word
  apply List.ext_getElem (by simpa only [List.length_ofFn] using he)
  intro i hi hj
  simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using hend ⟨i, by omega⟩ (by omega)
theorem eval_coordRows_leaves (T : Answers) (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    (evalWithAnswerFn T (coordRows index coord selected word (List.ofFn (ftsCoef T index coord.val))
      (ftsPrev T index coord.val).1)).1 = coordLeaves T index coord := by
  obtain ⟨hlen, hroot, -⟩ := eval_coordRows T index coord selected word (ftsPrev T index coord.val).1
  apply List.ext_getElem (by simpa only [coordLeaves, coordLeavesWith, List.length_ofFn] using hlen)
  intro j hj hk
  simpa only [coordLeaves, coordLeavesWith, List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using hroot j (by omega)
namespace Structural
variable (T : Answers) (index : Nat)
theorem sat_highHash {Q : Query → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : Wots.Structural.QueriesSat T Q (highHash input) := by
  unfold highHash
  exact Wots.Structural.QueriesSat.bind (Wots.Structural.sat_publicHash input h) (Wots.Structural.QueriesSat.pure' _)
/-- C1: an FTS hash (either half) makes the one query `pad64 input`. -/
theorem sat_ftsHash {Q : Query → Prop} (heap : Nat) (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : Wots.Structural.QueriesSat T Q (ftsHash heap input) := by
  rw [ftsHash_eq]
  split
  · exact sat_highHash T input h
  · exact Wots.Structural.sat_shortHash input h
theorem sat_query {q : Query} (h : FtsHonestQuery T index q) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (liftM (SigGolfCandidate.T3.Spec.query q)) :=
  Wots.Structural.QueriesSat.query h
theorem sat_seedPair (coord : Coord) (pair : Nat) (hpair : pair < ftsCoefPairs) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (ftsSeedPair index coord.val pair) := by
  unfold ftsSeedPair privatePair privateHash
  exact Wots.Structural.QueriesSat.bind
    (Wots.Structural.QueriesSat.query (show FtsHonestQuery T index (.inr (.inl _)) from
      ⟨coord.val, pair, coord.isLt, hpair, rfl⟩))
    (Wots.Structural.QueriesSat.pure' _)
theorem sat_ftsCoefs (coord : Coord) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (ftsCoefs index coord.val) := by
  unfold ftsCoefs
  refine Wots.Structural.QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun j hj acc _ => ⟨?_, trivial⟩)
  exact Wots.Structural.QueriesSat.bind (sat_seedPair T index coord j hj) (Wots.Structural.QueriesSat.pure' _)
theorem sat_chain (coord : Coord) (child : Child) (t : Fin 6) (start count : Nat) (hcount : start + count ≤ 4) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (chain index coord.val child.val t.val start count (ftsChainValue T index coord child t start)) := by
  induction count with
  | zero => rw [chain_zero']; exact Wots.Structural.QueriesSat.pure' _
  | succ count ih =>
      rw [chain_add index coord.val child.val t.val start count 1]
      refine Wots.Structural.QueriesSat.bind (ih (by omega)) ?_
      rw [eval_ftsChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      subst hq
      exact ⟨.chain coord child t (start + count), (by simp only [FtsPos.Bounded]; omega), rfl⟩
theorem sat_childStep (coord : Coord) (child : Child) (word : Rank)
    (t : Fin 6) (rows : List Digest × List Digest) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (childStep index coord.val child.val word (List.ofFn (ftsCoef T index coord.val)) rows t) := by
  unfold childStep
  have hd := wordDigit_le_four word t
  have hz : ftsFamilySeed (List.ofFn (ftsCoef T index coord.val)) child.val t.val =
      ftsChainValue T index coord child t 0 := rfl
  simp only []
  rw [hz]
  refine Wots.Structural.QueriesSat.bind (sat_chain T index coord child t 0 _ (by omega)) ?_
  rw [eval_ftsChain, Nat.zero_add]
  exact Wots.Structural.QueriesSat.bind (sat_chain T index coord child _ _ _ (by omega))
    (Wots.Structural.QueriesSat.pure' _)
theorem sat_childRows (coord : Coord) (child : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (childRows index coord.val child.val word (List.ofFn (ftsCoef T index coord.val))) := by
  unfold childRows
  refine Wots.Structural.QueriesSat.foldlM_list _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)
  have hi7 : i < 6 := by simpa using hi
  simp only [List.getElem_finRange, Fin.cast_mk]
  exact sat_childStep T index coord child word ⟨i, hi7⟩ rows
theorem sat_buildChildF (coord : Coord) (child : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (buildChildF index coord.val child.val word (List.ofFn (ftsCoef T index coord.val))
        (ftsPrev T index coord.val).1) := by
  rw [buildChildF_factor]
  refine Wots.Structural.QueriesSat.bind (sat_childRows T index coord child word) ?_
  rw [eval_childRows_ends T index coord.val child.val word]
  refine Wots.Structural.QueriesSat.bind ?_ (Wots.Structural.QueriesSat.pure' _)
  unfold leafHashP
  exact Wots.Structural.sat_shortHash _ ⟨.leaf coord child, trivial, rfl⟩
theorem sat_coordRows (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (coordRows index coord selected word (List.ofFn (ftsCoef T index coord.val)) (ftsPrev T index coord.val).1) := by
  unfold coordRows
  refine Wots.Structural.QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun j hj rows _ => ⟨?_, trivial⟩)
  exact Wots.Structural.QueriesSat.bind (sat_buildChildF T index coord ⟨j, hj⟩ word)
    (Wots.Structural.QueriesSat.pure' _)
def HeapAgree (final : Array Digest) (done : Nat) (nodes : Array Digest) : Prop :=
  nodes.size = 256 ∧ ∀ j, 128 - done ≤ j → nodes.getD j 0 = final.getD j 0
theorem sat_heapBuild (coord : Coord) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (heapBuild index coord.val (ftsPrev T index coord.val).2 (coordLeaves T index coord)) := by
  have hg := coordNodes_graph T index coord
  obtain ⟨hsize, hleaf, hnode⟩ := hg
  unfold heapBuild
  refine Wots.Structural.QueriesSat.foldlM_list _ _ (HeapAgree (coordNodes T index coord)) _ ?_ ?_
  refine ⟨by simp [coordLeaves, coordLeavesWith], ?_⟩
  · intro j hj
    by_cases hj' : j < 256
    · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
        List.length_replicate, ← hleaf j hj hj']
      simp only [Array.getD_eq_getD_getElem?]
    · have h1 : ((List.replicate 128 (0 : Digest) ++ coordLeaves T index coord).toArray).getD j 0 = 0 := by
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
        rw [List.getElem?_eq_none (by simp [coordLeaves, coordLeavesWith]; omega)]
        rfl
      have h2 : (coordNodes T index coord).getD j 0 = 0 := by
        simp only [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [h1, h2]
  · intro done hdone nodes ⟨hsz, hagree⟩
    have hd : done < 126 := by simpa only [List.length_reverse, List.length_range'] using hdone
    rw [heap_order done hd]
    have hl : nodes.getD (2 * (127 - done)) 0 = (coordNodes T index coord).getD (2 * (127 - done)) 0 :=
      hagree _ (by omega)
    have hr : nodes.getD (2 * (127 - done) + 1) 0 =
        (coordNodes T index coord).getD (2 * (127 - done) + 1) 0 := hagree _ (by omega)
    refine ⟨?_, ?_⟩
    · refine Wots.Structural.QueriesSat.bind ?_ (Wots.Structural.QueriesSat.pure' _)
      rw [hl, hr]
      unfold wctHeapNode
      split
      · rename_i hlt
        unfold wctTopHash
        exact sat_highHash T _ ⟨.node coord (127 - done), ⟨by omega, by omega⟩, by simp only [ftsHonestInput, if_pos hlt]⟩
      · rename_i hlt
        rw [nodeHash_eq]
        exact Wots.Structural.sat_shortHash _ ⟨.node coord (127 - done), ⟨by omega, by omega⟩,
          by simp only [ftsHonestInput, if_neg hlt, wctTopInput_zero]⟩
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      refine ⟨by rw [Array.size_set!, hsz], ?_⟩
      intro j hj
      by_cases he : j = 127 - done
      · subst he
        rw [getD_set_self nodes _ _ (by omega), hl, hr]
        exact (hnode (127 - done) (by omega) (by omega) (by omega)).symm
      · rw [getD_set_other nodes _ _ _ (Ne.symm he)]
        exact hagree j (by omega)
theorem sat_buildCoordinateF (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index)
      (buildCoordinateF index coord selected word (ftsPrev T index coord.val)) := by
  rw [buildCoordinateF_factor]
  refine Wots.Structural.QueriesSat.bind (sat_ftsCoefs T index coord) ?_
  rw [eval_ftsCoefs]
  refine Wots.Structural.QueriesSat.bind (sat_coordRows T index coord selected word) ?_
  rw [eval_coordRows_leaves]
  exact Wots.Structural.QueriesSat.bind (sat_heapBuild T index coord) (Wots.Structural.QueriesSat.pure' _)
theorem sat_forestRows (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (forestRows index output) := by
  unfold forestRows
  refine Wots.Structural.QueriesSat.foldlM_list _ _ (SignerRows T index output) _ (by simp [SignerRows])
    (fun i hi state hstate => ⟨?_, ?_⟩)
  · have hi9 : i < 9 := by simpa using hi
    unfold openingStep
    rw [prevPair_of_rows T index output i (by omega) state hstate]
    refine Wots.Structural.QueriesSat.bind (by simpa using sat_buildCoordinateF T index ⟨i, hi9⟩ _ _) ?_
    generalize evalWithAnswerFn T (buildCoordinateF index _ _ _ _) = x
    obtain ⟨levels, values⟩ := x
    exact Wots.Structural.QueriesSat.pure' _
  · have hi9 : i < 9 := by simpa using hi
    simp only [List.getElem_finRange, Fin.cast_mk]
    rw [eval_openingStep _ _ _ _ _ (prevPair_of_rows T index output i (by omega) state hstate)]
    exact signerRows_step T index output ⟨i, hi9⟩ state hstate
theorem sat_signForest (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsHonestQuery T index) (signForest index output) := by
  unfold signForest
  exact Wots.Structural.QueriesSat.bind (sat_forestRows T index output) (Wots.Structural.QueriesSat.pure' _)
end Structural
section Congr
variable {T T' : Answers} {index : Nat} (hTT : ∀ q, FtsQuery index q → T q = T' q)
include hTT
theorem eval_congr {α : Type} {p : M α} (hp : AllQueriesSatisfy p (FtsQuery index)) :
    evalWithAnswerFn T p = evalWithAnswerFn T' p :=
  (respects_of_allQueriesSatisfy hp T T' hTT).1
theorem ftsCoef_congr (coord : Coord) (j : Fin 54) : ftsCoef T index coord.val j = ftsCoef T' index coord.val j := by
  unfold ftsCoef
  rw [eval_congr hTT (allQueriesSatisfy_of_bound (ftsBound_seedPair index coord.val _ coord.isLt
    (by have := j.isLt; unfold ftsCoefPairs; omega)))]
theorem seed_congr (coord : Coord) (child : Child) (t : Fin 6) :
    seed T index coord.val child.val t = seed T' index coord.val child.val t := by
  unfold seed
  rw [show List.ofFn (ftsCoef T index coord.val) = List.ofFn (ftsCoef T' index coord.val) from
    congrArg List.ofFn (funext (ftsCoef_congr hTT coord))]
theorem ftsChainValue_congr (coord : Coord) (child : Child) (t : Fin 6) (step : Nat) (hstep : step ≤ 4) :
    ftsChainValue T index coord child t step = ftsChainValue T' index coord child t step := by
  unfold ftsChainValue
  rw [seed_congr hTT]
  exact eval_congr hTT (chain_queries index _ _ _ 0 step _ coord.isLt child.isLt t.isLt (by omega))
theorem chainEnd_congr (coord : Coord) (child : Child) (t : Fin 6) :
    chainEnd T index coord.val child.val t = chainEnd T' index coord.val child.val t :=
  ftsChainValue_congr hTT coord child t 4 le_rfl
theorem chainValue_congr (coord : Coord) (child : Child) (word : Rank) (t : Fin 6) :
    chainValue T index coord.val child.val word t = chainValue T' index coord.val child.val word t :=
  ftsChainValue_congr hTT coord child t _ (Nat.sub_le _ _)
theorem childRoot_congr (coord : Coord) (child : Child) (pad : Digest) :
    childRoot T index coord.val child.val pad = childRoot T' index coord.val child.val pad := by
  unfold childRoot
  rw [show List.ofFn (fun i : Fin 6 => chainEnd T index coord.val child.val i) =
      List.ofFn (fun i : Fin 6 => chainEnd T' index coord.val child.val i) from
    congrArg List.ofFn (funext (chainEnd_congr hTT coord child))]
  exact eval_congr hTT (allQueriesSatisfy_of_bound (ftsBound_leafHashP index _ _ _ _ coord.isLt child.isLt (by simp)))
/-- C1: the paired leaf of heap `heap` only reads FTS queries. -/
theorem childRootH_congr (heap : Nat) (coord : Coord) (child : Child) (pad : Digest) :
    childRootH T heap index coord.val child.val pad = childRootH T' heap index coord.val child.val pad := by
  unfold childRootH
  rw [show List.ofFn (fun i : Fin 6 => chainEnd T index coord.val child.val i) =
      List.ofFn (fun i : Fin 6 => chainEnd T' index coord.val child.val i) from
    congrArg List.ofFn (funext (chainEnd_congr hTT coord child))]
  exact eval_congr hTT (allQueriesSatisfy_of_bound
    (ftsBound_leafHashH index heap _ _ _ _ coord.isLt child.isLt (by simp)))
theorem coordNodesWith_congr (coord : Coord) (prev : Digest × Digest) :
    coordNodesWith T index coord.val prev = coordNodesWith T' index coord.val prev := by
  have hl : coordLeavesWith T index coord.val prev.1 = coordLeavesWith T' index coord.val prev.1 :=
    congrArg List.ofFn (funext fun j => childRoot_congr hTT coord j prev.1)
  unfold coordNodesWith
  rw [hl]
  exact eval_congr hTT (allQueriesSatisfy_of_bound (ftsBound_heapBuild index coord.val coord.isLt _ _))
theorem coordPairWith_congr (coord : Coord) (prev : Digest × Digest) :
    coordPairWith T index coord.val prev = coordPairWith T' index coord.val prev := by
  unfold coordPairWith
  rw [coordNodesWith_congr hTT]
theorem ftsPrev_congr : ∀ c, c ≤ 9 → ftsPrev T index c = ftsPrev T' index c
  | 0, _ => rfl
  | c + 1, hc => by
    show coordPairWith T index c (ftsPrev T index c) = coordPairWith T' index c (ftsPrev T' index c)
    rw [ftsPrev_congr c (by omega)]
    exact coordPairWith_congr hTT ⟨c, by omega⟩ _
theorem coordLeaves_congr (coord : Coord) : coordLeaves T index coord = coordLeaves T' index coord := by
  unfold coordLeaves coordLeavesWith
  rw [ftsPrev_congr hTT coord.val (by omega)]
  exact congrArg List.ofFn (funext fun j => childRoot_congr hTT coord j _)
theorem coordNodes_congr (coord : Coord) : coordNodes T index coord = coordNodes T' index coord := by
  unfold coordNodes
  rw [ftsPrev_congr hTT coord.val (by omega)]
  exact coordNodesWith_congr hTT coord _
theorem coordinatePair_congr (coord : Coord) : coordinatePair T index coord = coordinatePair T' index coord := by
  unfold coordinatePair
  rw [coordNodes_congr hTT]
theorem honestTop_congr : honestTop T index = honestTop T' index :=
  ftsPrev_congr hTT 9 le_rfl
theorem expectedOpening_congr (output : HashOutput) (coord : Coord) :
    expectedOpening T index output coord = expectedOpening T' index output coord := by
  unfold expectedOpening
  rw [ftsPrev_congr hTT coord.val (by omega), eval_congr hTT (buildCoordinateF_queries index coord _ _ _)]
theorem ftsHonestInput_congr (p : FtsPos) (hp : p.Bounded) :
    ftsHonestInput T index p = ftsHonestInput T' index p := by
  cases p with
  | chain coord child t step =>
      have hs : step < 4 := hp
      simp only [ftsHonestInput]
      rw [ftsChainValue_congr hTT coord child t step (by omega)]
  | leaf coord child =>
      simp only [ftsHonestInput]
      rw [show List.ofFn (chainEnd T index coord.val child.val) = List.ofFn (chainEnd T' index coord.val child.val)
        from congrArg List.ofFn (funext (chainEnd_congr hTT coord child)), ftsPrev_congr hTT coord.val (by omega)]
  | node coord heap =>
      simp only [ftsHonestInput]
      rw [coordNodes_congr hTT, ftsPrev_congr hTT coord.val (by omega)]
  | forest =>
      simp only [ftsHonestInput]
      rw [show List.ofFn (coordinatePair T index) = List.ofFn (coordinatePair T' index) from
        congrArg List.ofFn (funext (coordinatePair_congr hTT))]
theorem ftsHonestQuery_congr (q : Query) : FtsHonestQuery T index q ↔ FtsHonestQuery T' index q := by
  rcases q with (coin | input) | (tweak | other)
  · exact Iff.rfl
  · constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, ftsHonestInput_congr hTT p hp⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, (ftsHonestInput_congr hTT p hp).symm⟩
  · exact Iff.rfl
  · exact Iff.rfl
end Congr
namespace Mask
theorem ftsHonestInput_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) (p : FtsPos) (hp : p.Bounded) :
    ftsHonestInput (maskAt answers a) index p = ftsHonestInput answers index p :=
  ftsHonestInput_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq)) p hp
theorem honestTop_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) :
    honestTop (maskAt answers a) index = honestTop answers index :=
  honestTop_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq))
theorem coordinatePair_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) (coord : Coord) :
    coordinatePair (maskAt answers a) index coord = coordinatePair answers index coord :=
  coordinatePair_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq)) coord
theorem expectedOpening_maskAt (answers : Answers) (a : ChainAddr) (index : Nat) (output : HashOutput)
    (coord : Coord) :
    expectedOpening (maskAt answers a) index output coord = expectedOpening answers index output coord :=
  expectedOpening_congr (fun _ hq => Wots.Mask.maskAt_untouched answers a (ftsQuery_untouched a hq)) output coord
theorem respects_digestSearch (a : ChainAddr) (rho : Digest) (message : Message) :
    ∀ fuel counter, Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Wots.Mask.Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.digestSearch]
      refine Wots.Mask.Respects.bind (Wots.Mask.respects_digest a _ _ _) fun output => ?_
      split
      · exact Wots.Mask.Respects.pure' _
      · exact ih _
end Mask
namespace Enc
theorem ftsHonestInput_congr {T T' : Answers} (h : ∀ q, Wots.Enc.NonEnc q → T q = T' q) (index : Nat)
    (p : FtsPos) (hp : p.Bounded) : ftsHonestInput T index p = ftsHonestInput T' index p :=
  Wots.ftsHonestInput_congr (fun _ hq => h _ (ftsQuery_nonEnc hq)) p hp
theorem honestTop_congr {T T' : Answers} (h : ∀ q, Wots.Enc.NonEnc q → T q = T' q) (index : Nat) :
    honestTop T index = honestTop T' index :=
  Wots.honestTop_congr (fun _ hq => h _ (ftsQuery_nonEnc hq))
theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Wots.Mask.Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.digestSearch]
      refine Wots.Mask.Respects.bind (Wots.Enc.respects_digest _ _ _) fun output => ?_
      split
      · exact Wots.Mask.Respects.pure' _
      · exact ih _
end Enc
namespace Ref
theorem ftsHonestInput_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (index : Nat) (p : FtsPos)
    (hp : p.Bounded) : ftsHonestInput A index p = ftsHonestInput T index p :=
  Wots.ftsHonestInput_congr (fun _ hq => hAT _ (ftsQuery_short hq)) p hp
theorem coordinatePair_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (index : Nat) (coord : Coord) :
    coordinatePair A index coord = coordinatePair T index coord :=
  Wots.coordinatePair_congr (fun _ hq => hAT _ (ftsQuery_short hq)) coord
theorem expectedOpening_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (index : Nat)
    (output : HashOutput) (coord : Coord) :
    expectedOpening A index output coord = expectedOpening T index output coord :=
  Wots.expectedOpening_congr (fun _ hq => hAT _ (ftsQuery_short hq)) output coord
theorem ftsHonestInput_length (T : Answers) (index : Nat) (p : FtsPos) (hp : p.Bounded) :
    (ftsHonestInput T index p).length ≤ SeccLaw.maxInputLength := by
  have h := ftsHonestQuery_fts (T := T) (index := index) (q := .inl (.inr (ftsHonestInput T index p)))
    ⟨p, hp, rfl⟩
  exact ftsQuery_short h
end Ref
namespace Structural
theorem sat_digestSearch_of (T : Answers) (Q : Query → Prop) (rho : Digest) (message : Message)
    (hQ : ∀ counter : BitVec 32, Q (.inl (.inr (pad64 (digestInput rho message counter))))) :
    ∀ fuel counter, Wots.Structural.QueriesSat T Q (WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Wots.Structural.QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.digestSearch]
      refine Wots.Structural.QueriesSat.bind (Wots.Structural.sat_publicHash _ (hQ _)) ?_
      split
      · exact Wots.Structural.QueriesSat.pure' _
      · exact ih _
end Structural
end ClaudeWCT.WCT9.Wots
end
-- ==== merged from ClaudeWCT_W9_New_Positions_FtsBridge ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ClaudeWCT.WCT9.heapBuild
theorem wctValue_three (answers : Answers) (index coord child : Nat) (t : Fin 6) :
    wctValue answers index coord child t.val 4 = WCT9.chainEnd answers index coord child t := rfl
theorem wctSeed_eq (answers : Answers) (index coord child : Nat) (t : Fin 6) :
    wctSeed answers index coord child t.val = WCT9.seed answers index coord child t := rfl
theorem ftsLeaves_eq (answers : Answers) (index : Nat) (coord : WCT9.Coord) :
    ftsLeaves answers index coord.val = WCT9.coordLeaves answers index coord := rfl
theorem ftsPair_eq_coordinatePair (answers : Answers) (index : Nat) (coord : WCT9.Coord) :
    ftsPair answers index coord.val = WCT9.coordinatePair answers index coord := ftsPair_eq answers index coord
def heapLevel (heap : Nat) : Nat := 6 - Nat.log 2 heap
def heapNode (heap : Nat) : Nat := heap - 2 ^ Nat.log 2 heap
theorem heap_decomp {heap : Nat} (h1 : 2 ≤ heap) (h2 : heap < 128) :
    heapLevel heap < 6 ∧ heapNode heap < 2 ^ (7 - heapLevel heap - 1) ∧
      2 ^ (7 - heapLevel heap - 1) + heapNode heap = heap := by
  have hle : 2 ^ Nat.log 2 heap ≤ heap := Nat.pow_log_le_self 2 (by omega)
  have hlt : heap < 2 ^ (Nat.log 2 heap + 1) := Nat.lt_pow_succ_log_self (by decide) heap
  have hk : Nat.log 2 heap < 7 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr (by simpa using h2)
  have hk1 : 1 ≤ Nat.log 2 heap := Nat.le_log_of_pow_le (by decide) (by simpa using h1)
  have he : 7 - heapLevel heap - 1 = Nat.log 2 heap := by unfold heapLevel; omega
  refine ⟨by unfold heapLevel; omega, ?_, ?_⟩
  · rw [he]; unfold heapNode; rw [pow_succ] at hlt; omega
  · rw [he]; unfold heapNode; omega
noncomputable def Pos.ofFts (index : Nat) : WCT9.Wots.FtsPos → Pos
  | .chain coord child t step => .wctChain index coord.val child.val t.val step
  | .leaf coord child => .wctLeaf index coord.val child.val
  | .node coord heap => .wctNode index coord.val (heapLevel heap) (heapNode heap)
  | .forest => .forest index
theorem ofFts_bounded {index : Nat} (hidx : index < 2 ^ 31) (p : WCT9.Wots.FtsPos) (hp : p.Bounded) :
    (Pos.ofFts index p).Bounded := by
  cases p with
  | chain coord child t step => exact ⟨hidx, coord.isLt, child.isLt, t.isLt, hp⟩
  | leaf coord child => exact ⟨hidx, coord.isLt, child.isLt⟩
  | node coord heap =>
      obtain ⟨h1, h2, -⟩ := heap_decomp hp.1 hp.2
      exact ⟨hidx, coord.isLt, h1, h2⟩
  | forest => change index < 2 ^ 40; omega
private theorem bytesLE_zero'' : bytesLE 16 (0 : Digest) = zero16 := by decide
theorem honestInput_ofFts (T : Answers) (index : Nat) (p : WCT9.Wots.FtsPos) (hp : p.Bounded) :
    honestInput T (Pos.ofFts index p) = WCT9.Wots.ftsHonestInput T index p := by
  cases p with
  | chain coord child t step => rfl
  | leaf coord child =>
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput, wctLeafInputP, listInput, WCT9.leafInputP,
        List.flatMap_cons, List.append_assoc]
      rfl
  | node coord heap =>
      obtain ⟨h1, h2, h3⟩ := heap_decomp hp.1 hp.2
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput]
      have hpow : 2 ^ (7 - heapLevel heap) = 2 * 2 ^ (7 - heapLevel heap - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpos : 1 ≤ 2 ^ (7 - heapLevel heap - 1) := Nat.one_le_two_pow
      unfold ftsLevels
      rw [WCT9.heapLevels_value _ _ _ (by omega) (by omega), WCT9.heapLevels_value _ _ _ (by omega) (by omega),
        ftsNodes_eq]
      rw [show 2 ^ (7 - heapLevel heap) + 2 * heapNode heap = 2 * heap by omega,
        show 2 ^ (7 - heapLevel heap) + (2 * heapNode heap + 1) = 2 * heap + 1 by omega, h3]
      have hl5 : heapLevel heap = 5 ↔ heap < 4 := by
        clear hpow hpos
        have hb1 : 2 ^ (7 - heapLevel heap - 1) ≤ heap := by omega
        have hb2 : heap < 2 * 2 ^ (7 - heapLevel heap - 1) := by omega
        clear h2 h3
        generalize heapLevel heap = L at h1 hb1 hb2 ⊢
        interval_cases L <;> simp at hb1 hb2 ⊢ <;> omega
      by_cases hlt : heap < 4
      · simp only [if_pos (hl5.mpr hlt), if_pos hlt, nodeInputP, block4, WCT9.wctTopInput, WCT9.nodeLayer,
          WCT9.wctNodeHeader]
      · simp only [if_neg (fun h => hlt (hl5.mp h)), if_neg hlt, nodeInputP, block4, WCT9.wctTopInput,
          WCT9.nodeLayer, WCT9.wctNodeHeader]
  | forest =>
      simp only [Pos.ofFts, honestInput, WCT9.Wots.ftsHonestInput, forestInput, ftsPairsHonest_eq]
theorem ftsHonestQuery_pos {T : Answers} {index : Nat} (hidx : index < 2 ^ 31) {x : HashInput}
    (h : WCT9.Wots.FtsHonestQuery T index (.inl (.inr x))) : ∃ pos : Pos, pos.Bounded ∧ x = honestInput T pos := by
  obtain ⟨p, hp, rfl⟩ := (show ∃ p : WCT9.Wots.FtsPos, p.Bounded ∧ x = WCT9.Wots.ftsHonestInput T index p from h)
  exact ⟨Pos.ofFts index p, ofFts_bounded hidx p hp, (honestInput_ofFts T index p hp).symm⟩
theorem honestTop_eq_wct9 (answers : Answers) (index : Nat) :
    honestTop answers index = WCT9.honestTop answers index := honestTop_eq answers index
end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTransportShort ====
section

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
/-! C2/C3 (FULL): the half-keeping hashes of the current scheme. -/
theorem halfHash_respects (high : Bool) (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (WCT9.halfHash high input) := by
  intro A T hAT
  rw [eval_halfHash', eval_halfHash', hAT.public _ h]
theorem chainW_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (WCT9.chainW lay tree leaf i start count value) := by
  unfold WCT9.chainW
  exact ShortRespects.foldlM _ _ (fun step _ v => halfHash_respects _ _
    (short_of_le _ (by rw [WCT9.chainInputW_length]; omega))) value
theorem lowerLeafHash_respects (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    ShortRespects (WCT9.lowerLeafHash lay tree leaf ends) := by
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  apply halfHash_respects
  apply short_of_le
  rw [leafInput_length]
  split_ifs <;> omega
theorem lowerNodeHash_respects (lay tree heap : Nat) (left right : Digest) :
    ShortRespects (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  apply halfHash_respects
  apply short_of_le
  simp [WCT9.merkleNodeInput, zero16, bytesLE_length]
theorem lowerLevels_respects (lay tree h : Nat) (leaves : List Digest) :
    ShortRespects (WCT9.lowerLevels lay tree h leaves) := by
  unfold WCT9.lowerLevels
  exact ShortRespects.foldlM _ _ (fun level _ levels =>
    ShortRespects.bind (ShortRespects.mapM _ _ fun i _ => lowerNodeHash_respects _ _ _ _ _) fun _ =>
      ShortRespects.pure' _) _
/-! Top-nonce layer (r3-lean-nonsec): the img-v6 top tree (nonce-searched node levels) respects short agreement. -/
theorem topNodeHashN_respects (heap n : Nat) (left right : Digest) : ShortRespects (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  exact ShortRespects.projHash _ _ (short_of_le _ (by simp [topNodeInput, nonceBytes, bytesLE_length]))
theorem topNonceSearch_respects (h heap : Nat) (left right : Digest) :
    ∀ fuel n, ShortRespects (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact ShortRespects.bind (topNodeHashN_respects _ _ _ _) fun _ => ShortRespects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine ShortRespects.bind (topNodeHashN_respects _ _ _ _) fun _ => ?_
      split
      · exact ShortRespects.pure' _
      · exact topNonceSearch_respects h heap left right fuel (n + 1)
theorem buildTopLevels_respects (leaves : List Digest) : ShortRespects (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine ShortRespects.foldlM _ _ (fun level _ levels => ShortRespects.bind ?_ fun _ => ShortRespects.pure' _) _
  unfold buildTopLevel
  refine ShortRespects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact lowerNodeHash_respects _ _ _ _ _
  · unfold topNodeAt
    exact ShortRespects.map _ (topNonceSearch_respects _ _ _ _ _ _)
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem honestChainValueW_short (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    honestChainValueW A lay tree leaf i seed step = honestChainValueW T lay tree leaf i seed step :=
  chainW_respects lay tree leaf i 0 step seed A T hAT
theorem honestTop_short (index : Nat) : Extract.honestTop A index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq))
theorem wotsSeed_short (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsSeed A lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  rw [WCT9.wotsSeed_fam, WCT9.wotsSeed_fam]
  congr 2
  funext j
  unfold WCT9.famCoef WCT9.famCoefN WCT9.lowerSeedPair
  rw [ShortRespects.privatePair 0 lay.val tree _ 0 A T hAT]
theorem wotsEnd_short (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsEnd A lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_short hAT]
  exact chainW_respects _ _ _ _ _ _ _ A T hAT
theorem wotsRoot_short (lay : Layer) (tree leaf : Nat) :
    WCT9.wotsRoot A lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i _ => wotsEnd_short hAT lay tree leaf i)]
  apply lowerLeafHash_respects
  · simp only [List.length_map, List.length_range]
    have := chainCount_le lay
    omega
  · exact hAT
theorem wotsTree_short (lay : Layer) (tree : Nat) :
    WCT9.wotsTree A lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf _ => wotsRoot_short hAT lay tree leaf)]
  split_ifs
  · exact buildTopLevels_respects _ A T hAT
  · exact lowerLevels_respects _ _ _ _ A T hAT
theorem honestNonce_short (lay : Layer) (tree level c : Nat) :
    WCT9.honestNonce A lay tree level c = WCT9.honestNonce T lay tree level c := by
  unfold WCT9.honestNonce
  split_ifs
  · rw [wotsTree_short hAT]
    unfold topNodeAt
    exact congrArg Prod.fst (topNonceSearch_respects _ _ _ _ _ _ A T hAT)
  · rfl
theorem ftsLevels_short (index coord : Nat) (hc : coord < 9) :
    Extract.ftsLevels A index coord = Extract.ftsLevels T index coord := by
  unfold Extract.ftsLevels
  have h1 := Extract.ftsNodes_eq A index ⟨coord, hc⟩
  have h2 := Extract.ftsNodes_eq T index ⟨coord, hc⟩
  have h3 := ClaudeWCT.WCT9.Wots.coordNodes_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) ⟨coord, hc⟩
  rw [show Extract.ftsNodes A index coord = Extract.ftsNodes T index coord from h1.trans (h3.trans h2.symm)]
theorem ftsPairsHonest_short (index : Nat) : Extract.ftsPairsHonest A index = Extract.ftsPairsHonest T index := by
  rw [Extract.ftsPairsHonest_eq, Extract.ftsPairsHonest_eq]
  exact congrArg List.ofFn (funext fun coord => ClaudeWCT.WCT9.Wots.coordinatePair_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) coord)
theorem wctValue_short (index coord child chain step : Nat) (hc : coord < 9) (hch : child < 128) (ht : chain < 6)
    (hs : step ≤ 4) :
    Extract.wctValue A index coord child chain step = Extract.wctValue T index coord child chain step :=
  ClaudeWCT.WCT9.Wots.ftsChainValue_congr (index := index) (T := A) (T' := T)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) ⟨coord, hc⟩ ⟨child, hch⟩ ⟨chain, ht⟩ step hs
theorem ftsPrev_short (index coord : Nat) (hc : coord ≤ 9) :
    Extract.ftsPrev A index coord = Extract.ftsPrev T index coord :=
  ClaudeWCT.WCT9.Wots.ftsPrev_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) coord hc
theorem wctEnds_short (index coord child : Nat) (hc : coord < 9) (hch : child < 128) :
    Extract.wctEnds A index coord child = Extract.wctEnds T index coord child := by
  unfold Extract.wctEnds
  exact congrArg List.ofFn (funext fun t => wctValue_short hAT index coord child t.val 4 hc hch t.isLt le_rfl)
theorem leafMsg_short (L : LeafAddr) : leafMsg A L = leafMsg T L := by
  unfold leafMsg
  split_ifs
  · unfold Extract.honestPair
    rw [wotsTree_short hAT]
  · rw [honestTop_short hAT]
theorem referenceSearch_short (L : LeafAddr) : referenceSearch A L = referenceSearch T L := by
  unfold referenceSearch
  rw [leafMsg_short hAT]
  exact layerCounterSearch_respects _ _ _ _ _ _ A T hAT
theorem referenceDigits_short (L : LeafAddr) : referenceDigits A L = referenceDigits T L := by
  unfold referenceDigits
  rw [referenceSearch_short hAT]
theorem depth_short (a : ChainAddr) : depth A a = depth T a := by
  unfold depth
  rw [referenceDigits_short hAT]
theorem frontierValue_short (a : ChainAddr) : frontierValue A a = frontierValue T a := by
  unfold frontierValue
  rw [depth_short hAT, wotsSeed_short hAT]
  exact honestChainValueW_short hAT _ _ _ _ _ _
theorem referenceInput_short (L : LeafAddr) : referenceInput A L = referenceInput T L := by
  unfold referenceInput
  rw [referenceSearch_short hAT, leafMsg_short hAT]
theorem honestInput_short (position : Extract.Pos) (hb : position.Bounded) :
    Extract.honestInput A position = Extract.honestInput T position := by
  cases position with
  | chain lay tree leaf i step =>
      simp only [Extract.honestInput]
      rw [wotsSeed_short hAT]
      exact congrArg (fun v => pad64 (WCT9.chainInputW lay tree leaf i step v)) (honestChainValueW_short hAT _ _ _ _ _ _)
  | leaf lay tree leaf =>
      simp only [Extract.honestInput]
      rw [List.map_congr_left (fun i _ => wotsEnd_short hAT lay tree leaf i)]
  | node lay tree level node =>
      simp only [Extract.honestInput]
      rw [wotsTree_short hAT, honestNonce_short hAT]
  | forest index =>
      simp only [Extract.honestInput]
      rw [ftsPairsHonest_short hAT]
  | wctChain index coord child t step =>
      obtain ⟨-, hc, hch, ht, hs⟩ := hb
      simp only [Extract.honestInput]
      rw [wctValue_short hAT index coord child t step hc hch ht (by omega)]
  | wctLeaf index coord child =>
      obtain ⟨-, hc, hch⟩ := hb
      simp only [Extract.honestInput]
      rw [wctEnds_short hAT index coord child hc hch, ftsPrev_short hAT index coord (by omega)]
  | wctNode index coord level nd =>
      obtain ⟨-, hc, -, -⟩ := hb
      simp only [Extract.honestInput]
      rw [ftsLevels_short hAT index coord hc, ftsPrev_short hAT index coord (by omega)]
end objects
theorem honestInput_length (answers : Answers) (position : Extract.Pos) :
    (Extract.honestInput answers position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step =>
      apply short_of_le
      rw [WCT9.chainInputW_length]; omega
  | leaf lay tree leaf =>
      apply short_of_le
      simp only [Extract.leafInput, SigGolfCandidate.T3.leafInput_length, List.length_map, List.length_range]
      have := chainCount_le lay
      split_ifs <;> omega
  | node lay tree level node =>
      apply short_of_le
      simp [Extract.honestInput, WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]
  | forest index =>
      apply short_of_le
      rw [Extract.forestInput, ClaudeWCT.WCT9.forestInput_length _ _ (Extract.ftsPairsHonest_length _ _)]
      omega
  | wctChain index coord child t step =>
      apply short_of_le
      simp only [ClaudeWCT.WCT9.ftsChainInputW_padded, ClaudeWCT.WCT9.ftsChainInputW_length]
      omega
  | wctLeaf index coord child =>
      apply short_of_le
      simp only [Extract.wctLeafInputP, Extract.listInput_length', List.length_cons, List.length_drop,
        Extract.wctEnds, List.length_ofFn]
      omega
  | wctNode index coord level node =>
      apply short_of_le
      simp [nodeInputP]
end ClaudeWCT.W9.T3.Security.Wots.Ref
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTransportTable ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF
def GameSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
theorem verdict_hashOnly (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) :
    Security.SourceReplay.HashOnly (GameWith.verdict PaddedGame.checker publicKey result) := by
  unfold GameWith.verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (PaddedExtraction.check_hashOnly publicKey result.2 forgery)
        fun _ => SourceQueries.pure_allowed _ _
noncomputable def verdictCharge (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Nat :=
  (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)).length
theorem verdict_accepts (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests)
    (h : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true) :
    ∃ forgery, result.1 = some forgery ∧
      evalWithAnswerFn T (checkForgeryP publicKey result.2 forgery) = true ∧
      ∀ query ∈ SourceReplay.queried T (checkForgeryP publicKey result.2 forgery),
        query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result) := by
  cases hf : result.1 with
  | none =>
      simp only [GameWith.verdict, hf, evalWithAnswerFn_pure] at h
      exact absurd h (by decide)
  | some forgery =>
      refine ⟨forgery, rfl, ?_, ?_⟩
      · simp only [GameWith.verdict, hf, PaddedGame.checker, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2
      · intro query hq
        simp only [GameWith.verdict, hf, PaddedGame.checker, SourceReplay.queried_bind, SourceReplay.queried_pure,
          List.append_nil]
        exact hq
theorem witnessOf_unique {answers : Answers} {publicKey : Digest} {forgery : ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : PaddedExtraction.WitnessOf answers publicKey forgery m w)
    (h' : PaddedExtraction.WitnessOf answers publicKey forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, hw⟩ := h
      obtain ⟨rfl, hw'⟩ := h'
      exact ⟨rfl, Option.some.inj (hw.symm.trans hw')⟩
noncomputable def verdictRecord (T : Answers) (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :
    FirstHit.Recorded Bool :=
  pureRecord T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) interaction.state
noncomputable def combine (T : Answers) (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :
    FirstHit.Recorded Bool :=
  ⟨(verdictRecord T interaction).value,
    (pureRecord T keygen (∅, ∅)).events ++ (interaction.events ++ (verdictRecord T interaction).events),
    (verdictRecord T interaction).state⟩
noncomputable def fixedInteraction (adversary : AdversaryP) (T : Answers) :
    ProbComp (FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :=
  fixedRecord T (FullGame.loggedWith (FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)) (pureRecord T keygen (∅, ∅)).state
theorem fixed_game_eq (adversary : AdversaryP) (T : Answers) :
    fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) =
      combine T <$> fixedInteraction adversary T := by
  unfold GameWith.idealGame
  rw [fixedRecord_bind, fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, pure_bind]
  simp only [pureRecord_value]
  rw [fixedRecord_bind]
  simp only [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), pure_bind, bind_assoc]
  unfold fixedInteraction combine verdictRecord
  rw [map_eq_bind_pure_comp]
  rfl
end Ref
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF
def GameSplit (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
theorem check_hashOnly (pk : Digest) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)
    (forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP) :
    Security.SourceReplay.HashOnly (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP pk log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (PairedOuter.PaddedGame.check_public pk log forgery)
  intro input h
  rcases input with (sample | input) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem verdict_hashOnly (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :
    Security.SourceReplay.HashOnly (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) := by
  unfold PairedOuter.GameWith.verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (check_hashOnly publicKey result.2 forgery)
        fun _ => SourceQueries.pure_allowed _ _
noncomputable def verdictCharge (T : Answers) (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Nat :=
  (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result)).length
theorem verdict_accepts (T : Answers) (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)
    (h : evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) = true) :
    ∃ forgery, result.1 = some forgery ∧
      evalWithAnswerFn T (checkForgeryP publicKey result.2 forgery) = true ∧
      ∀ query ∈ SourceReplay.queried T (checkForgeryP publicKey result.2 forgery),
        query ∈ SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) := by
  cases hf : result.1 with
  | none =>
      simp only [PairedOuter.GameWith.verdict, hf, evalWithAnswerFn_pure] at h
      exact absurd h (by decide)
  | some forgery =>
      refine ⟨forgery, rfl, ?_, ?_⟩
      · simp only [PairedOuter.GameWith.verdict, hf, PairedOuter.PaddedGame.checker, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2
      · intro query hq
        simp only [PairedOuter.GameWith.verdict, hf, PairedOuter.PaddedGame.checker, SourceReplay.queried_bind, SourceReplay.queried_pure,
          List.append_nil]
        exact hq
theorem witnessOf_unique {answers : Answers} {publicKey : Digest} {forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : ClaudeWCT.W9.T3M.Final.Paired.WitnessOf answers publicKey forgery m w)
    (h' : ClaudeWCT.W9.T3M.Final.Paired.WitnessOf answers publicKey forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, hw⟩ := h
      obtain ⟨rfl, hw'⟩ := h'
      exact ⟨rfl, Option.some.inj (hw.symm.trans hw')⟩
noncomputable def verdictRecord (T : Answers) (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) :
    FirstHit.Recorded Bool :=
  pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) interaction.state
noncomputable def combine (T : Answers) (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) :
    FirstHit.Recorded Bool :=
  ⟨(verdictRecord T interaction).value,
    (pureRecord T keygen (∅, ∅)).events ++ (interaction.events ++ (verdictRecord T interaction).events),
    (verdictRecord T interaction).state⟩
noncomputable def fixedInteraction (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers) :
    ProbComp (FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) :=
  fixedRecord T (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)) (pureRecord T keygen (∅, ∅)).state
theorem fixed_game_eq (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers) :
    fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅) =
      combine T <$> fixedInteraction adversary T := by
  unfold PairedOuter.GameWith.idealGame
  rw [fixedRecord_bind, fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, pure_bind]
  simp only [pureRecord_value]
  rw [fixedRecord_bind]
  simp only [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), pure_bind, bind_assoc]
  unfold fixedInteraction combine verdictRecord
  rw [map_eq_bind_pure_comp]
  rfl
end Ref
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTransport ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
noncomputable def recordedCompleted (adversary : AdversaryP) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
    completionComp >>= fun tables => pure (result, SeccLaw.completeWith result.state tables)
theorem completed_map (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq =
      (liftM (recordedCompleted adversary) : PMF _) := by
  unfold SeccLaw.completedExperiment recordedCompleted
  rw [PMF.monad_map_eq_map, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have he := PaddedGame.traced_record_erasure adversary q hq
  rw [PMF.monad_map_eq_map] at he
  rw [show (PaddedGame.tracedExperiment adversary q hq).bind (fun result =>
      (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
        (QueryRecorded.recordedTrace result, SeccLaw.completeWith result.2.2.base.source.2 tables)) =
      ((PaddedGame.tracedExperiment adversary q hq).map QueryRecorded.recordedTrace).bind (fun result =>
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
          (result, SeccLaw.completeWith result.state tables)) from by rw [PMF.bind_map]; rfl]
  rw [he, ← completionComp_eq, liftM_bind]
  congr 1
  funext result
  rw [← PMF.monad_map_eq_map, ← liftM_map, map_eq_bind_pure_comp]
  rfl
theorem referenceInputs_universe (adversary : AdversaryP) : SeccLaw.publicUniverse ⊆ referenceInputs adversary :=
  Finset.subset_union_left
theorem referenceInputs_inputsIn (adversary : AdversaryP) :
    InputsIn (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) :=
  fun privateTable _ => (ChainGraph.program_subset_recordedInputs _ privateTable).trans Finset.subset_union_right
theorem recorded_eq_eager (adversary : AdversaryP) (event : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun pair => event pair.1 pair.2 | recordedCompleted adversary] =
      Pr[fun pair => event pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] := by
  have hlaw : 𝒮[recordedCompleted adversary] =
      𝒮[(fun pair : FirstHit.Recorded Bool × Answers => (pair.1, cut pair.1.state pair.2)) <$>
        (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
          ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
            ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
              pure (result, fillAnswers (referenceInputs adversary) result.state privateTable publicTable))] := by
    unfold recordedCompleted completionComp
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    apply evalSPMF_bind_congr'
    intro result
    apply evalSPMF_bind_congr'
    intro privateTable
    rw [← restrict_uniform (referenceInputs adversary) (referenceInputs_universe adversary)]
    apply evalSPMF_bind_congr'
    intro publicTable
    rw [completeWith_eq_cut]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
  have hc := record_completion (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)
    (referenceInputs_inputsIn adversary)
  exact probEvent_congr' (fun _ _ => Iff.rfl) hc
end Ref
noncomputable def eagerRecorded (adversary : AdversaryP) : PMF (FirstHit.Recorded Bool × Answers) :=
  liftM (($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun result => (result, eagerAnswers (referenceInputs adversary) privateTable publicTable)) <$>
        Ref.fixedRecord (eagerAnswers (referenceInputs adversary) privateTable publicTable)
          (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅))
theorem completed_eager_cut (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun z => event (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] =
      Pr[fun x => event x.1 (Ref.cut x.1.state x.2) | eagerRecorded adversary] := by
  calc _ = Pr[fun pair => event pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun pair => event pair.1 pair.2 | Ref.recordedCompleted adversary] := by
        rw [Ref.completed_map, MonitoredPrivate.event_lift]
    _ = _ := by
        rw [Ref.recorded_eq_eager adversary event]
        unfold eagerRecorded Ref.eagerSide
        rw [MonitoredPrivate.event_lift]
        simp only [Ref.fillAnswers_empty]
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF PairedOuter.GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
noncomputable def recordedCompleted (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  FirstHit.record (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
    completionComp >>= fun tables => pure (result, SeccLaw.completeWith result.state tables)
theorem completed_map (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> PairedSeccLaw.completedExperiment adversary q hq =
      (liftM (recordedCompleted adversary) : PMF _) := by
  unfold PairedSeccLaw.completedExperiment recordedCompleted
  rw [PMF.monad_map_eq_map, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have he := PairedOuter.PaddedGame.traced_record_erasure adversary q hq
  rw [PMF.monad_map_eq_map] at he
  rw [show (PairedOuter.PaddedGame.tracedExperiment adversary q hq).bind (fun result =>
      (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
        (QueryRecorded.recordedTrace result, SeccLaw.completeWith result.2.2.base.source.2 tables)) =
      ((PairedOuter.PaddedGame.tracedExperiment adversary q hq).map QueryRecorded.recordedTrace).bind (fun result =>
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
          (result, SeccLaw.completeWith result.state tables)) from by rw [PMF.bind_map]; rfl]
  rw [he, ← completionComp_eq, liftM_bind]
  congr 1
  funext result
  rw [← PMF.monad_map_eq_map, ← liftM_map, map_eq_bind_pure_comp]
  rfl
theorem referenceInputs_universe (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : SeccLaw.publicUniverse ⊆ referenceInputs adversary :=
  Finset.subset_union_left
theorem referenceInputs_inputsIn (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    InputsIn (referenceInputs adversary) (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅) :=
  fun privateTable _ => (ChainGraph.program_subset_recordedInputs _ privateTable).trans Finset.subset_union_right
theorem recorded_eq_eager (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (event : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun pair => event pair.1 pair.2 | recordedCompleted adversary] =
      Pr[fun pair => event pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] := by
  have hlaw : 𝒮[recordedCompleted adversary] =
      𝒮[(fun pair : FirstHit.Recorded Bool × Answers => (pair.1, cut pair.1.state pair.2)) <$>
        (FirstHit.record (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
          ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
            ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
              pure (result, fillAnswers (referenceInputs adversary) result.state privateTable publicTable))] := by
    unfold recordedCompleted completionComp
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    apply evalSPMF_bind_congr'
    intro result
    apply evalSPMF_bind_congr'
    intro privateTable
    rw [← restrict_uniform (referenceInputs adversary) (referenceInputs_universe adversary)]
    apply evalSPMF_bind_congr'
    intro publicTable
    rw [completeWith_eq_cut]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
  have hc := record_completion (referenceInputs adversary) (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)
    (referenceInputs_inputsIn adversary)
  exact probEvent_congr' (fun _ _ => Iff.rfl) hc
end Ref
noncomputable def eagerRecorded (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : PMF (FirstHit.Recorded Bool × Answers) :=
  liftM (($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun result => (result, eagerAnswers (referenceInputs adversary) privateTable publicTable)) <$>
        Ref.fixedRecord (eagerAnswers (referenceInputs adversary) privateTable publicTable)
          (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅))
theorem completed_eager_cut (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun z => event (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] =
      Pr[fun x => event x.1 (Ref.cut x.1.state x.2) | eagerRecorded adversary] := by
  calc _ = Pr[fun pair => event pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> PairedSeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun pair => event pair.1 pair.2 | Ref.recordedCompleted adversary] := by
        rw [Ref.completed_map, MonitoredPrivate.event_lift]
    _ = _ := by
        rw [Ref.recorded_eq_eager adversary event]
        unfold eagerRecorded Ref.eagerSide
        rw [MonitoredPrivate.event_lift]
        simp only [Ref.fillAnswers_empty]
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
end
-- ==== merged from ClaudeWCT_W9_New_C2_SignerCompleteBound ====
section

namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots.Ref (eagerSide cut fillAnswers)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_injective searchQuery_length)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_signerCompleteBound : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_signerCompleteBound :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) :=
  ClaudeWCT.W9.T3.Presampling.tableSampler
theorem signerComplete_of_searches (A : Correctness.Answers)
    (h : ClaudeWCT.W9.T3.Correctness.SearchesSucceed A) : SignerComplete A := by
  refine ⟨fun rho m => ?_, fun lay _ tree leaf msg htree hleaf => ?_⟩
  · obtain ⟨found, hf⟩ := h.1 (rho, m)
    rw [hf]
    rfl
  · have hr : tree * 2 ^ height lay + leaf < 2 ^ 32 := by
      rename_i hlay
      fin_cases lay
      · exact absurd rfl hlay
      all_goals simp only [height] at hleaf ⊢; norm_num at hleaf ⊢; omega
    obtain ⟨found, hf⟩ := ClaudeWCT.W9.T3.Correctness.encodingSearchesSucceedBC_msg A h.2 lay
      tree leaf hleaf hr msg
    change (evalWithAnswerFn A (WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay))).isSome
    rw [hf]
    rfl
theorem digestSearch_respects (rho : Digest) (m : Message) :
    ∀ fuel c, Wots.Ref.ShortRespects (WCT9.digestSearch rho m c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact Wots.Ref.ShortRespects.pure' _
  | succ fuel ih =>
      intro c
      simp only [WCT9.digestSearch, digest]
      refine Wots.Ref.ShortRespects.bind (fun A' T' hAT' => ?_) fun output => ?_
      · unfold publicHash
        change A' (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) =
          T' (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))))
        refine hAT'.public _ ?_
        rw [SigGolfCandidate.T3.Security.BPB.pad64_digestInput, SigGolfCandidate.T3.Security.BPB.digestInput_length]
        unfold SeccLaw.maxInputLength
        omega
      · split
        · exact Wots.Ref.ShortRespects.pure' _
        · exact ih _
theorem signerComplete_short {A T : Correctness.Answers} (h : Wots.Ref.ShortAgree A T) (hc : SignerComplete A) :
    SignerComplete T := by
  refine ⟨fun rho m => ?_, fun lay hl tree leaf msg ht hle => ?_⟩
  · rw [← digestSearch_respects rho m WCT9.digestAttemptLimit 0 A T h]
    exact hc.1 rho m
  · rw [← Wots.Ref.layerCounterSearch_respects lay tree leaf msg 0 (WCT9.searchLimit lay) A T h]
    exact hc.2 lay hl tree leaf msg ht hle
def searchTable (A : Correctness.Answers) : SearchKey → HashOutput := fun key => A (.inl (.inr (searchQuery key)))
theorem not_tableGood_of_incomplete (A : Correctness.Answers) (h : ¬SignerComplete A) :
    ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable A) := fun hg =>
  h (signerComplete_of_searches A
    ((ClaudeWCT.W9.T3.Budgets.tableGood_iff_searchesSucceed (searchTable A) A (fun _ => rfl)).mp hg))
theorem searchQuery_mem (adversary : AdversaryP) (key : SearchKey) :
    searchQuery key ∈ Wots.referenceInputs adversary :=
  Wots.Ref.referenceInputs_universe adversary
    (SeccLaw.mem_publicUniverse _ (by rw [searchQuery_length]; decide))
theorem searchTable_cut (state : LazyPrivate.State) (F : Correctness.Answers) :
    searchTable (cut state F) = searchTable F := by
  funext key
  unfold searchTable
  exact SigGolfCandidate.T3.Security.Wots.Ref.cut_shortAgree state F _
    (show (searchQuery key).length ≤ SeccLaw.maxInputLength by rw [searchQuery_length]; decide)
theorem searchTable_fill (adversary : AdversaryP) (privateTable : FullGame.FullTable)
    (publicTable : Wots.referenceInputs adversary → HashOutput) :
    searchTable (fillAnswers (Wots.referenceInputs adversary) (∅, ∅) privateTable publicTable) =
      fun key => publicTable ⟨searchQuery key, searchQuery_mem adversary key⟩ := by
  funext key
  unfold searchTable
  rw [SigGolfCandidate.T3.Security.Wots.Ref.fillAnswers_empty]
  exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (searchQuery_mem adversary key) rfl
theorem eager_incomplete_le (adversary : AdversaryP) :
    Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable (cut pair.1.state pair.2)) |
        eagerSide (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun outputs => ¬ClaudeWCT.W9.T3.Budgets.tableGood outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  unfold eagerSide
  refine probEvent_bind_le_of_forall_le fun privateTable _ => ?_
  refine (probEvent_bind_le_probEvent (p := fun publicTable : Wots.referenceInputs adversary → HashOutput =>
    ¬ClaudeWCT.W9.T3.Budgets.tableGood (fun key => publicTable ⟨searchQuery key, searchQuery_mem adversary key⟩))
    fun publicTable _ hgood => ?_).trans ?_
  · rw [probEvent_eq_zero_iff]
    intro pair _ hbad
    rw [support_map] at *
    obtain ⟨result, -, rfl⟩ := (Set.mem_image _ _ _).mp ‹pair ∈ _›
    apply hbad
    rw [searchTable_cut, searchTable_fill]
    exact not_not.mp hgood
  · let e : SearchKey → Wots.referenceInputs adversary := fun key => ⟨searchQuery key, searchQuery_mem adversary key⟩
    have he : Function.Injective e := fun k k' h => searchQuery_injective (congrArg Subtype.val h)
    have hlaw := evalSPMF_uniformSample_map_comp_injective (R := HashOutput) he
    have hp : Pr[fun publicTable : Wots.referenceInputs adversary → HashOutput =>
        ¬ClaudeWCT.W9.T3.Budgets.tableGood (fun key => publicTable (e key)) |
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] =
        Pr[fun outputs => ¬ClaudeWCT.W9.T3.Budgets.tableGood outputs |
          (do let g ← ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _); pure (g ∘ e))] := by
      rw [bind_pure_comp, probEvent_map]
      rfl
    rw [hp, probEvent_congr' (fun _ _ => Iff.rfl) hlaw]
theorem signerIncomplete_le_table (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => ¬SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun outputs => ¬ClaudeWCT.W9.T3.Budgets.tableGood outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  calc Pr[fun z => ¬SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq]
      ≤ Pr[fun z => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable z.2) |
          SeccLaw.completedExperiment adversary q hq] :=
        Wots.Ref.pmf_probEvent_mono _ fun z _ h => not_tableGood_of_incomplete z.2 h
    _ = Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable pair.2) |
          (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable pair.2) |
          Wots.Ref.recordedCompleted adversary] := by
        rw [Wots.Ref.completed_map, MonitoredPrivate.event_lift]
    _ = Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable (cut pair.1.state pair.2)) |
          eagerSide (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] :=
        Wots.Ref.recorded_eq_eager adversary fun _ A => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable A)
    _ ≤ _ := eager_incomplete_le adversary
end ClaudeWCT.W9.T3.Security.BPB

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_injective searchQuery_length)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

def outputs (A : Answers) : SearchKey → HashOutput := fun key => A (.inl (.inr (searchQuery key)))

theorem query_mem (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (key : SearchKey) :
    searchQuery key ∈ PairedReference.referenceInputs adversary := by
  apply Finset.mem_union_left
  exact SeccLaw.mem_publicUniverse _ (by rw[searchQuery_length];decide)

theorem outputs_eager (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (privateTable : FullGame.FullTable) (publicTable : PairedReference.referenceInputs adversary → HashOutput) :
    outputs (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)=
      fun key => publicTable ⟨searchQuery key,query_mem adversary key⟩ := by
  funext key
  exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (query_mem adversary key) rfl

theorem reference_event_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (event : (SearchKey → HashOutput) → Prop) :
    Pr[fun s => event (outputs s.answers) | PairedReference.referenceExperiment adversary q] ≤
      Pr[event | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  unfold PairedReference.referenceExperiment
  rw[MonitoredPrivate.event_lift]
  unfold PairedReference.referenceComp
  refine probEvent_bind_le_of_forall_le fun privateTable _ => ?_
  refine (probEvent_bind_le_probEvent (p:=fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
    event (fun key => publicTable ⟨searchQuery key,query_mem adversary key⟩))
    fun publicTable _ hgood => ?_).trans ?_
  · rw[probEvent_map,probEvent_eq_zero_iff]
    intro result _ hbad
    exact hgood ((congrArg event (outputs_eager adversary privateTable publicTable)).mp hbad)
  · let e : SearchKey → PairedReference.referenceInputs adversary := fun key => ⟨searchQuery key,query_mem adversary key⟩
    have he : Function.Injective e := fun k k' h => searchQuery_injective (congrArg Subtype.val h)
    have hlaw := evalSPMF_uniformSample_map_comp_injective (R:=HashOutput) he
    have hp : Pr[fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
        event (fun key => publicTable (e key)) |
        ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _)] =
        Pr[event | (do let g ← ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _); pure (g ∘ e))] := by
      rw[bind_pure_comp,probEvent_map]
      rfl
    rw[hp,probEvent_congr' (fun _ _ => Iff.rfl) hlaw]

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey)
open ClaudeWCT.W9.T3.CanonicalSearch
open SigGolfCandidate.T3.Budgets (zeroAnswers ofReal_inv_two_pow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

theorem context_failure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ¬ContextGood s.answers | PairedReference.referenceExperiment adversary q] ≤
      1/(2:ENNReal)^139 := by
  have hpoint (A : Correctness.Answers) :
      ¬ContextGood A ↔ ∃c,ContextFailed c (Presampling.tableAnswers (outputs A) zeroAnswers) := by
    rw [contextGood_agreement (outputs A) A zeroAnswers (fun _=>rfl)]
    simp only [ContextGood,not_forall,not_not]
  calc
    _ = Pr[fun s => ∃c,ContextFailed c (Presampling.tableAnswers (outputs s.answers) zeroAnswers) |
        PairedReference.referenceExperiment adversary q] := by simp_rw[hpoint]
    _ ≤ Pr[fun output => ∃c,ContextFailed c (Presampling.tableAnswers output zeroAnswers) |
        ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := reference_event_le adversary q _
    _ ≤ (2:ENNReal)^301*(1/(2:ENNReal)^440) := context_family_failure
    _ ≤ 1/(2:ENNReal)^139 := by
      have hr:(2:ℝ)^301*(1/(2:ℝ)^440)≤1/(2:ℝ)^139 := by
        set_option exponentiation.threshold 1024 in norm_num
      have h:=ENNReal.ofReal_le_ofReal hr
      rw[ENNReal.ofReal_mul (by positivity)] at h
      simpa only [ENNReal.ofReal_pow (show 0≤(2:ℝ) by norm_num),ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using h

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_injective)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

theorem eager_event_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (event : Answers → Prop) (bad : FullGame.FullTable → (SearchKey → HashOutput) → Prop) (bound : ENNReal)
    (hbad : ∀ privateTable publicTable state,
      event (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)) →
      bad privateTable (fun key=>publicTable ⟨searchQuery key,query_mem adversary key⟩))
    (hbound : ∀ privateTable,Pr[bad privateTable | ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤bound) :
    Pr[fun x=>event (Ref.cut x.1.state x.2) | PairedReference.eagerRecorded adversary]≤bound := by
  unfold PairedReference.eagerRecorded
  rw[MonitoredPrivate.event_lift]
  refine probEvent_bind_le_of_forall_le fun privateTable _ => ?_
  refine (probEvent_bind_le_probEvent (p:=fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
    bad privateTable (fun key=>publicTable ⟨searchQuery key,query_mem adversary key⟩))
    fun publicTable _ hgood => ?_).trans ?_
  · rw[probEvent_map,probEvent_eq_zero_iff]
    intro result _ he
    exact hgood (hbad privateTable publicTable result.state he)
  · let e : SearchKey → PairedReference.referenceInputs adversary := fun key=>⟨searchQuery key,query_mem adversary key⟩
    have he : Function.Injective e:=fun k k' h=>searchQuery_injective (congrArg Subtype.val h)
    have hlaw:=evalSPMF_uniformSample_map_comp_injective (R:=HashOutput) he
    have hp : Pr[fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
        bad privateTable (fun key=>publicTable (e key)) |
        ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _)] =
        Pr[bad privateTable | (do let g ← ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _);pure (g ∘ e))] := by
      rw[bind_pure_comp,probEvent_map];rfl
    rw[hp,probEvent_congr' (fun _ _ => Iff.rfl) hlaw]
    exact hbound privateTable

theorem completed_event_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq:q≤2^127) (event : Answers → Prop)
    (bad : FullGame.FullTable → (SearchKey → HashOutput) → Prop) (bound : ENNReal)
    (hbad : ∀ privateTable publicTable state,
      event (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)) →
      bad privateTable (fun key=>publicTable ⟨searchQuery key,query_mem adversary key⟩))
    (hbound : ∀ privateTable,Pr[bad privateTable | ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤bound) :
    Pr[fun z=>event z.2 | PairedSeccLaw.completedExperiment adversary q hq]≤bound := by
  rw[PairedReference.completed_eager_cut adversary q hq (fun _ A=>event A)]
  exact eager_event_le adversary event bad bound hbad hbound

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_length)
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

def privateNonces (table : FullGame.FullTable) (message : Message) : Digest :=
  (table (.inr (.inl message))).extractLsb' 0 128

theorem completed_signer_failure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>¬SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138 := by
  refine completed_event_le adversary q hq (fun A=>¬SigningComplete A (evalWithAnswerFn A keygen).2)
    (fun privateTable output=>¬TableGoodForNonces (privateNonces privateTable) output) (1/(2:ENNReal)^138) ?_ ?_
  · intro privateTable publicTable state hbad hgood
    apply hbad
    apply tableGoodForNonces_signing _ _ (privateNonces privateTable) hgood
    · intro key
      change (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable))
        (.inl (.inr (searchQuery key))) = _
      rw[(Ref.cut_shortAgree state _).public _ (by rw[searchQuery_length];decide)]
      exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (query_mem adversary key) rfl
    · intro message
      rfl
  · intro privateTable
    exact tableGoodForNonces_failure _

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_length)
open ClaudeWCT.W9.T3.CanonicalSearch
open SigGolfCandidate.T3.Budgets (zeroAnswers ofReal_inv_two_pow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

theorem completed_context_failure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun z => ¬ContextGood z.2 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      1/(2:ENNReal)^139 := by
  refine completed_event_le adversary q hq (fun A => ¬ContextGood A)
    (fun _ outputs => ∃context,ContextFailed context (Presampling.tableAnswers outputs zeroAnswers))
    (1/(2:ENNReal)^139) ?_ ?_
  · intro privateTable publicTable state hbad
    have ha : Budgets.SearchAgreement
        (fun key => publicTable ⟨searchQuery key,query_mem adversary key⟩)
        (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)) := by
      intro key
      change (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable))
        (.inl (.inr (searchQuery key))) = _
      rw [(Ref.cut_shortAgree state _).public _ (by rw [searchQuery_length];decide)]
      exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (query_mem adversary key) rfl
    rw [contextGood_agreement _ _ zeroAnswers ha] at hbad
    simpa only [ContextGood,not_forall,not_not] using hbad
  · intro _
    refine context_family_failure.trans ?_
    have hr : (2:ℝ)^301*(1/(2:ℝ)^440) ≤ 1/(2:ℝ)^139 := by
      set_option exponentiation.threshold 1024 in norm_num
    have h := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (by positivity)] at h
    simpa only [ENNReal.ofReal_pow (show 0≤(2:ℝ) by norm_num),ENNReal.ofReal_ofNat,
      ofReal_inv_two_pow] using h
end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
end
-- ==== merged from ClaudeWCT_WCT9_FamLayout ====
section

/-! # Seed-family layout: generic facts (r3-lean-seedfam, family port P7)

Facts about the layout of `Correctness` (`famGrp`, `famBase`, `famSize`, `famStride`, `famOf`, `famPoint`) used by the
security bridge (CanonGraph, large route). All proofs here go through the generic layout facts of `Correctness`
(`famGrp_pos`, `famStride_ge`, ...) except `famSize_pos`, which must be re-proved at the v6 flip. -/

namespace ClaudeWCT.WCT9
open SigGolfCandidate SigGolfCandidate.T3

/-- Every family has a coefficient (top 24, lower `5 r + 3 ≥ 3`). -/
theorem famSize_pos (lay : Layer) (f : Nat) : 0 < famSize lay f := by
  unfold famSize; split_ifs
  · decide
  · omega

theorem famSize_lt_58 (lay : Layer) (f : Nat) : famSize lay f < 58 := by
  have := famSize_le_base lay f; have := famBase_le lay; omega

theorem famOf_le (lay : Layer) (leaf : Nat) : famOf lay leaf ≤ leaf := Nat.div_le_self _ _

theorem famOf_lt {lay : Layer} {leaf : Nat} (h : leaf < 4096) : famOf lay leaf < 4096 :=
  lt_of_le_of_lt (famOf_le lay leaf) h

/-- `r·s + a` determines `(r, a)` when `a < s`. -/
theorem mul_add_inj {r r' s a a' : Nat} (ha : a < s) (ha' : a' < s) (h : r * s + a = r' * s + a') :
    r = r' ∧ a = a' := by
  rcases Nat.lt_or_ge r r' with hlt | hge
  · exfalso
    have : r * s + s ≤ r' * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
    omega
  · rcases Nat.lt_or_ge r' r with hlt' | hge'
    · exfalso
      have : r' * s + s ≤ r * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt'
      omega
    · have hrr : r = r' := by omega
      subst hrr
      exact ⟨rfl, by omega⟩

/-- Within a family the evaluation points of the address slots `i < 58` are distinct. -/
theorem famPoint_inj {lay : Layer} {l l' i i' : Nat} (hi : i < 58) (hi' : i' < 58)
    (hf : famOf lay l = famOf lay l') (h : famPoint lay l i = famPoint lay l' i') : l = l' ∧ i = i' := by
  have hg := famGrp_pos lay
  have hm : l % famGrp lay < famGrp lay := Nat.mod_lt _ hg
  have hm' : l' % famGrp lay < famGrp lay := Nat.mod_lt _ hg
  have hreal : ∀ r, r < famGrp lay → r * famStride lay + famStride lay ≤ famGrp lay * famStride lay := by
    intro r hr
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
  have hlt : ∀ k, k < 58 → (lay = 0 ∨ k < chainCount lay) → k < famStride lay := by
    intro k hk hc
    rcases hc with h0 | h0
    · subst h0; have := famStride_top; omega
    · have := famStride_ge lay; omega
  have hjunk : ∀ k, ¬(lay = 0 ∨ k < chainCount lay) → chainCount lay ≤ k := by
    intro k hk; by_contra hc; exact hk (Or.inr (by omega))
  have hrr : l % famGrp lay = l' % famGrp lay ∧ i = i' := by
    unfold famPoint at h
    split_ifs at h with h1 h2 h2
    · have a1 := hlt i hi h1
      have a2 := hlt i' hi' h2
      exact mul_add_inj a1 a2 (by omega : l % famGrp lay * famStride lay + i =
        l' % famGrp lay * famStride lay + i')
    · have a1 := hlt i hi h1; have := hreal _ hm; omega
    · have a2 := hlt i' hi' h2; have := hreal _ hm'; omega
    · have c1 := hjunk i h1
      have c2 := hjunk i' h2
      obtain ⟨e1, e2⟩ := mul_add_inj (s := 58 - chainCount lay) (a := i - chainCount lay)
        (a' := i' - chainCount lay) (by omega) (by omega) (by omega : l % famGrp lay * (58 - chainCount lay) +
          (i - chainCount lay) = l' % famGrp lay * (58 - chainCount lay) + (i' - chainCount lay))
      exact ⟨e1, by omega⟩
  refine ⟨?_, hrr.2⟩
  have e := Nat.div_add_mod l (famGrp lay)
  have e' := Nat.div_add_mod l' (famGrp lay)
  unfold famOf at hf
  rw [← e, ← e', hf, hrr.1]

end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_CanonGraph ====
section

namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure LeafPos where
  lay : Layer
  tree : Fin (2^31)
  leaf : Fin 4096
  deriving DecidableEq, Fintype
export ClaudeWCT.W9.T3M.Extract (treeBits)
def LeafPos.Source (L : LeafPos) : Prop := L.tree.val < 2 ^ treeBits L.lay ∧ L.leaf.val < 2 ^ height L.lay
instance instDecidablePredLeafPosSource : DecidablePred LeafPos.Source := fun L => by unfold LeafPos.Source; infer_instance
theorem LeafPos.Source.routed {L : LeafPos} (h : L.Source) :
    L.leaf.val < 2 ^ height L.lay ∧ L.tree.val * 2 ^ height L.lay + L.leaf.val < 2 ^ 32 :=
  ⟨h.2, lt_trans (ClaudeWCT.W9.T3M.Extract.routed_lt_of_treeBits h.1 h.2) (by norm_num)⟩
abbrev SrcLeaf := {L : LeafPos // L.Source}
/-- A tree node. Top-nonce layer (r3-lean-nonsec): `nonce` indexes the keygen nonce trials of a top node (rejection
sampling cell); every other position uses only `nonce = 0`, and every other `(position, nonce)` is a phantom node
(a 192-byte cell outside every position). -/
structure TreeNodeRaw where
  lay : Layer
  tree : Fin (2^31)
  level : Fin 12
  idx : Fin 2048
  nonce : Fin 212992
  deriving DecidableEq, Fintype
def TreeNodeRaw.Valid (n : TreeNodeRaw) : Prop :=
  n.level.val < height n.lay ∧ n.idx.val < 2 ^ (height n.lay - n.level.val - 1) ∧
    n.tree.val < 2 ^ treeBits n.lay ∧ (n.lay = 0 ∨ n.level.val + 1 < height n.lay)
instance instDecidablePredTreeNodeRawValid : DecidablePred TreeNodeRaw.Valid := fun n => by unfold TreeNodeRaw.Valid; infer_instance
abbrev TreeNode := {n : TreeNodeRaw // n.Valid}
abbrev WctAddr := Fin (2 ^ 31) × Fin 9 × Fin 128 × Fin 6
abbrev WctPoint := WctAddr × Fin 4
structure WctLeafPos where
  index : Fin (2^31)
  coord : Fin 9
  child : Fin 128
  deriving DecidableEq, Fintype
structure WctNodeRaw where
  index : Fin (2^31)
  coord : Fin 9
  level : Fin 6
  idx : Fin 64
  deriving DecidableEq, Fintype
def WctNodeRaw.Valid (n : WctNodeRaw) : Prop := n.idx.val < 2 ^ (7 - n.level.val - 1)
instance instDecidablePredWctNodeRawValid : DecidablePred WctNodeRaw.Valid := fun n => by unfold WctNodeRaw.Valid; infer_instance
abbrev WctNodePos := {n : WctNodeRaw // n.Valid}
inductive Node where
  | chain (point : Point)
  | leaf (pos : SrcLeaf)
  | node (pos : TreeNode)
  | wctChain (point : WctPoint)
  | wctLeaf (pos : WctLeafPos)
  | wctNode (pos : WctNodePos)
  | forest (index : Fin (2^31))
  deriving DecidableEq, Fintype
attribute [local irreducible] ChainGraph.instFintypeAddress
def Node.depth : Node → Nat
  | .chain p => p.2.val
  | .leaf _ => 7
  | .node n => 8 + n.1.level.val * 2 ^ 18 + n.1.nonce.val
  | .wctChain p => p.2.val
  | .wctLeaf L => 4 + 7 * L.coord.val
  | .wctNode n => 5 + 7 * n.1.coord.val + n.1.level.val
  | .forest _ => 70
/-- Coefficient index of the FTS seed families (campaign X1, stage A): `(index, coord, j)`, `j < 54`. -/
abbrev WctCoef := Fin (2 ^ 31) × Fin 9 × Fin 54
/-- Hidden secrets: leaf-family coefficients (by address: an address with chain `j < famCount layer` is coefficient
`j` of its leaf, campaign X1 stage B for lower leaves, campaign T8D for top leaves) and FTS family coefficients. WOTS and
FTS seeds are not secrets themselves but evaluations (`seedsOf`, `wctSeedsOf`) of the coefficient families. -/
abbrev SecretIndex := Address ⊕ WctCoef
abbrev Secrets := SecretIndex → Digest
abbrev Labels := Node → HashOutput
theorem chainCount_lower {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  revert h; fin_cases lay <;> decide
theorem famCount_lt_58 (lay : Layer) : WCT9.famCount lay < 58 := by
  have := WCT9.famCount_le lay; omega
/-- The family of a leaf, as an address slot (secret coefficient `j` of family `f` sits at address
`(lay, tree, f, j)`; today one family per leaf, `famOf_today`). -/
def famSlot (lay : Layer) (leaf : Fin 4096) : Fin 4096 :=
  ⟨WCT9.famOf lay leaf.val, WCT9.famOf_lt leaf.isLt⟩
/-- Packed ordinal of coefficient `j` of family `f` (`famOrdinal lay leaf j = famOrd lay (famOf lay leaf) j`). -/
def famOrd (lay : Layer) (f j : Nat) : Nat := WCT9.famBase lay * f + j
theorem famOrdinal_eq (lay : Layer) (leaf j : Nat) :
    WCT9.famOrdinal lay leaf j = famOrd lay (WCT9.famOf lay leaf) j := rfl
/-- The coefficient family of leaf `(lay, tree, leaf)`: the secrets `(lay, tree, famOf leaf, j)`, `j < famSize`. -/
def leafFamily (secrets : Secrets) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096) :
    Fin (WCT9.famSize lay (WCT9.famOf lay leaf.val)) → Digest :=
  fun j => secrets (.inl ⟨lay, tree, famSlot lay leaf, ⟨j.val, lt_trans j.isLt (WCT9.famSize_lt_58 lay _)⟩⟩)
/-- WOTS seeds: the leaf family at `famPoint layer leaf chain` (every layer). -/
def seedsOf (secrets : Secrets) : Seeds := fun a =>
  ClaudeWCT.Arith.familyEval (List.ofFn (leafFamily secrets a.layer a.tree a.leaf))
    (WCT9.famPoint a.layer a.leaf.val a.chain.val)
/-- The coefficient family of FTS coordinate `(index, coord)`. -/
def wctFamily (secrets : Secrets) (index : Fin (2 ^ 31)) (coord : Fin 9) : Fin 54 → Digest :=
  fun j => secrets (.inr (index, coord, j))
/-- FTS seed of chain `a`: its family evaluated at `ftsPoint child chain` in GF(2^128). -/
def wctSeedsOf (secrets : Secrets) : WctAddr → Digest := fun a =>
  ClaudeWCT.Arith.familyEval (List.ofFn (wctFamily secrets a.1 a.2.1)) (WCT9.ftsPoint a.2.2.1.val a.2.2.2.val)
def chainLabels (labels : Labels) : ChainGraph.Labels := fun point => labels (.chain point)
/-! ### Pairing stage 1: chain rows of the current scheme

A chain point's cell is `WCT9.chainInputW` (F rows `0 | hdr | 0 | v`, G rows `v | hdr | 0 | 0`), and its input value
is the half `chainHigh` of the previous step's label (the HIGH half for steps `0..5` of a G chain). -/
def rowW (point : Point) (value : Digest) : HashInput :=
  WCT9.chainInputW point.1.layer point.1.tree.val point.1.leaf.val point.1.chain.val point.2.val value
theorem rowW_length (point : Point) (value : Digest) : (rowW point value).length = 64 :=
  WCT9.chainInputW_length _ _ _ _ _ _
theorem rowW_pad64 (point : Point) (value : Digest) : pad64 (rowW point value) = rowW point value :=
  WCT9.chainInputW_padded _ _ _ _ _ _
/-- The half of step `m`'s output that chain `address` reads. -/
def stepHigh (address : Address) (m : Nat) : Bool := WCT9.chainHigh address.layer address.chain.val m
def priorW (seeds : Seeds) (point : Point) (labels : ChainGraph.Labels) : Digest :=
  if point.2.val = 0 then seeds point.1
  else WCT9.halfOf (stepHigh point.1 (point.2.val - 1)) (labels (ChainGraph.predecessor point))
def inputW (seeds : Seeds) (point : Point) (labels : ChainGraph.Labels) : HashInput :=
  rowW point (priorW seeds point labels)
def valueW (seeds : Seeds) (labels : ChainGraph.Labels) (address : Address) (step : Nat) : Digest :=
  if step = 0 then seeds address
  else WCT9.halfOf (stepHigh address (step - 1)) (labels (address, ⟨(step - 1) % 7, Nat.mod_lt _ (by decide)⟩))
theorem valueW_zero (seeds : Seeds) (labels : ChainGraph.Labels) (address : Address) :
    valueW seeds labels address 0 = seeds address := by simp [valueW]
theorem valueW_succ (seeds : Seeds) (labels : ChainGraph.Labels) (address : Address) (step : Fin 7) :
    valueW seeds labels address (step.val + 1) = WCT9.halfOf (stepHigh address step.val) (labels (address, step)) := by
  simp [valueW, Nat.mod_eq_of_lt step.isLt]
theorem priorW_eq_valueW (seeds : Seeds) (labels : ChainGraph.Labels) (point : Point) :
    priorW seeds point labels = valueW seeds labels point.1 point.2.val := by
  have hmod : (point.2.val - 1) % 7 = point.2.val - 1 := Nat.mod_eq_of_lt (by have := point.2.isLt; omega)
  simp only [priorW, valueW, ChainGraph.predecessor, hmod]
def AgreesW (answers : Answers) (seeds : Seeds) (labels : ChainGraph.Labels) : Prop :=
  ∀ point, answers (.inl (.inr (inputW seeds point labels))) = labels point
theorem sourceW_step (answers : Answers) (seeds : Seeds) (labels : ChainGraph.Labels) (h : AgreesW answers seeds labels)
    (address : Address) (step : Fin 7) :
    evalWithAnswerFn answers (WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val
      step.val 1 (valueW seeds labels address step.val)) = valueW seeds labels address (step.val + 1) := by
  have hin : inputW seeds (address, step) labels = rowW (address, step) (valueW seeds labels address step.val) := by
    rw [inputW, priorW_eq_valueW]
  have hh := h (address, step)
  rw [hin] at hh
  have hc : WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val step.val 1
      (valueW seeds labels address step.val) =
        WCT9.halfHash (stepHigh address step.val) (rowW (address, step) (valueW seeds labels address step.val)) := by
    simp [WCT9.chainW, List.range'_succ, rowW, stepHigh]
  rw [hc, valueW_succ]
  cases hs : stepHigh address step.val
  · change WCT9.halfOf false (answers (.inl (.inr (pad64 (rowW (address, step) _))))) = _
    rw [rowW_pad64, hh]
  · change WCT9.halfOf true (answers (.inl (.inr (pad64 (rowW (address, step) _))))) = _
    rw [rowW_pad64, hh]
theorem sourceW_chain (answers : Answers) (seeds : Seeds) (labels : ChainGraph.Labels) (h : AgreesW answers seeds labels)
    (address : Address) (start count : Nat) (hbound : start + count ≤ 7) :
    evalWithAnswerFn answers (WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val
      start count (valueW seeds labels address start)) = valueW seeds labels address (start + count) := by
  induction count with
  | zero => simp [WCT9.chainW]
  | succ count ih =>
      rw [show start + (count + 1) = start + count + 1 by omega]
      have hadd : WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val start (count + 1)
          (valueW seeds labels address start) =
          (WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val start count
            (valueW seeds labels address start) >>=
            WCT9.chainW address.layer address.tree.val address.leaf.val address.chain.val (start + count) 1) := by
        unfold WCT9.chainW
        rw [← List.range'_append_1, List.foldlM_append]
      rw [hadd, evalWithAnswerFn_bind, ih (by omega)]
      exact sourceW_step answers seeds labels h address ⟨start + count, by omega⟩
def fin58 (i : Nat) : Fin 58 := ⟨i % 58, Nat.mod_lt _ (by decide)⟩
def fin9 (i : Nat) : Fin 9 := ⟨i % 9, Nat.mod_lt _ (by decide)⟩
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.1.lay L.1.tree.val L.1.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .wctChain p => .wctChain p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
  | .wctLeaf L => .wctLeaf L.index.val L.coord.val L.child.val
  | .wctNode n => .wctNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val
/-- The last chain point of chain `i` of leaf `L` (step `maxDigit - 1`). -/
def endPt (L : LeafPos) (i : Nat) : Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
/-- The chain end the leaf reads: the used half (`Pos.proj`) of the last step's label (C3: the high half for chain
0 of a lower layer). -/
def endLabel (_secrets : Secrets) (labels : Labels) (L : LeafPos) (i : Nat) : Digest :=
  (Node.chain (endPt L i)).toPos.proj (labels (.chain (endPt L i)))
def wctValueL (secrets : Secrets) (labels : Labels) (a : WctAddr) (s : Nat) : Digest :=
  if s = 0 then wctSeedsOf secrets a
  else projHalf (WCT9.ftsChainHigh a.2.2.2.val ((s - 1) % 4))
    (labels (.wctChain (a, ⟨(s - 1) % 4, Nat.mod_lt _ (by decide)⟩)))
def wctEndLabel (labels : Labels) (a : WctAddr) : Digest := (labels (.wctChain (a, 3))).extractLsb' 0 128
/-- The chain end (campaign T8: position 4; the name is kept from the 3-step code). -/
theorem wctValueL_three (secrets : Secrets) (labels : Labels) (a : WctAddr) :
    wctValueL secrets labels a 4 = wctEndLabel labels a := by
  unfold wctValueL wctEndLabel
  rw [if_neg (by decide)]
  show projHalf (WCT9.ftsChainHigh a.2.2.2.val 3) (labels (.wctChain (a, 3))) = _
  rw [WCT9.ftsChainHigh_three]
  rfl
def treeNodeAt (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option TreeNode :=
  if h : level < height lay ∧ c < 2 ^ (height lay - level - 1) ∧ tree.val < 2 ^ treeBits lay ∧
      (lay = 0 ∨ level + 1 < height lay) then
    some ⟨⟨lay, tree, ⟨level, lt_of_lt_of_le h.1 (SigGolfCandidate.T3M.Extract.height_le lay)⟩,
      ⟨c, lt_of_lt_of_le h.2.1 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := SigGolfCandidate.T3M.Extract.height_le lay; omega)
          _ = 2048 := by norm_num)⟩, 0⟩, h⟩
  else none
theorem height_le_12 (lay : Layer) : 2 ^ height lay ≤ 4096 :=
  (Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)).trans (by norm_num)
def leafAt (lay : Layer) (tree : Fin (2^31)) (c : Nat) : Option SrcLeaf :=
  if h : c < 2 ^ height lay ∧ tree.val < 2 ^ treeBits lay then
    some ⟨⟨lay, tree, ⟨c, lt_of_lt_of_le h.1 (height_le_12 lay)⟩⟩, ⟨h.2, h.1⟩⟩
  else none
/-! ### Top-nonce layer: rejection-sampling cells (r3-lean-nonsec)
The nodes `(position, nonce)` of a top node at children level `level < 11` are its keygen nonce trials. With labels
`L`, trial `k` *fails* when the used half of its label misses the zero test; it is *active* when it is inside the cap
and every earlier trial failed. The selected trial `sel` is the first passing one (the last one when none passes),
and the tree value of the position is the used half of the selected trial's label. Every other position has only the
active trial `nonce = 0`. -/
/-- Trials of position `(lay, level)`: `cap_(level+1) = 104 · 2^(level+1)` on the top tree below the root, else 1. -/
def trialCap (lay : Layer) (level : Nat) : Nat := if lay = 0 ∧ level < 11 then topNonceCap (level + 1) else 1
theorem trialCap_pos (lay : Layer) (level : Nat) : 0 < trialCap lay level := by
  unfold trialCap topNonceCap; split_ifs <;> positivity
theorem trialCap_le (lay : Layer) (level : Nat) : trialCap lay level ≤ 212992 := by
  unfold trialCap topNonceCap topZeroBits topZeroAlloc
  split_ifs with h
  · obtain ⟨-, hl⟩ := h
    interval_cases level <;> simp
  · omega
/-- The trial `j` of the position of `n` (nonce `j % 212992`). -/
def withNonce (n : TreeNode) (j : Nat) : TreeNode :=
  ⟨{ n.1 with nonce := ⟨j % 212992, Nat.mod_lt _ (by decide)⟩ }, n.2⟩
theorem withNonce_nonce (n : TreeNode) {j : Nat} (hj : j < 212992) : (withNonce n j).1.nonce.val = j := by
  simp [withNonce, Nat.mod_eq_of_lt hj]
@[simp] theorem withNonce_lay (n : TreeNode) (j : Nat) : (withNonce n j).1.lay = n.1.lay := rfl
@[simp] theorem withNonce_tree (n : TreeNode) (j : Nat) : (withNonce n j).1.tree = n.1.tree := rfl
@[simp] theorem withNonce_level (n : TreeNode) (j : Nat) : (withNonce n j).1.level = n.1.level := rfl
@[simp] theorem withNonce_idx (n : TreeNode) (j : Nat) : (withNonce n j).1.idx = n.1.idx := rfl
theorem withNonce_withNonce (n : TreeNode) (i j : Nat) : withNonce (withNonce n i) j = withNonce n j := rfl
theorem withNonce_self (n : TreeNode) : withNonce n n.1.nonce.val = n := by
  obtain ⟨⟨lay, tree, level, idx, nonce⟩, hv⟩ := n
  simp [withNonce, Nat.mod_eq_of_lt nonce.isLt]
/-- Trial `j` of the position of `n` fails the zero test of height `level + 1`. -/
def trialFails (labels : Labels) (n : TreeNode) (j : Nat) : Prop :=
  topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj (labels (.node (withNonce n j)))) = false
instance (labels : Labels) (n : TreeNode) (j : Nat) : Decidable (trialFails labels n j) := by
  unfold trialFails; infer_instance
/-- Node `n` is an active trial: inside the cap, and every earlier trial of its position failed. -/
def Active (labels : Labels) (n : TreeNode) : Prop :=
  n.1.nonce.val < trialCap n.1.lay n.1.level.val ∧ ∀ j < n.1.nonce.val, trialFails labels n j
instance (labels : Labels) (n : TreeNode) : Decidable (Active labels n) := by unfold Active; infer_instance
/-- The selected nonce of the position of `n`: the first passing trial, the last trial when none passes. -/
def selNonce (labels : Labels) (n : TreeNode) : Nat :=
  ((List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFails labels n j)).getD
    (trialCap n.1.lay n.1.level.val - 1)
/-- The selected trial of the position of `n`. -/
def selNode (labels : Labels) (n : TreeNode) : TreeNode := withNonce n (selNonce labels n)
/-- The 192-byte phantom cell of an inactive node: unique per node, no position (`posOf = none`). -/
def phantomCode (n : TreeNode) : Nat :=
  n.1.lay.val + 4 * (n.1.level.val + 12 * (n.1.idx.val + 2048 * (n.1.nonce.val + 212992 * n.1.tree.val)))
def phantom (n : TreeNode) : HashInput :=
  List.replicate 16 255 ++ bytesLE 16 (BitVec.ofNat 128 (phantomCode n)) ++ List.replicate 160 0
def treeLabel (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  if level = 0 then
    (match leafAt lay tree c with
     | some L => (Node.leaf L).toPos.proj (labels (.leaf L))
     | none => 0)
  else
    match treeNodeAt lay tree (level - 1) c with
    | some n => (Node.node n).toPos.proj (labels (.node (selNode labels n)))
    | none => 0
def ftsNodeAt (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Option WctNodePos :=
  if h : level < 6 ∧ c < 2 ^ (7 - level - 1) then
    some ⟨⟨index, coord, ⟨level, h.1⟩, ⟨c, lt_of_lt_of_le h.2 (by
      calc 2 ^ (7 - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 64 := by norm_num)⟩⟩, h.2⟩
  else none
/-- FTS tree value from labels. The top values (level 6, nested FTS r1-1) are the high half of their label. -/
def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 128 then (labels (.wctLeaf ⟨index, coord, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match ftsNodeAt index coord (level - 1) c with
    | some n => if level = 6 then (labels (.wctNode n)).extractLsb' 128 128 else (labels (.wctNode n)).extractLsb' 0 128
    | none => 0
/-- Pads of coordinate `coord` (nested FTS r1-1): the previous coordinate's top pair, `(0, 0)` for coordinate 0. -/
def ftsPrevLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) : Digest × Digest :=
  if h : coord.val = 0 then (0, 0) else
    (ftsLabel labels index ⟨coord.val - 1, by omega⟩ 6 0, ftsLabel labels index ⟨coord.val - 1, by omega⟩ 6 1)
def cell (secrets : Secrets) : Node → Labels → HashInput
  | .chain p, labels => inputW (seedsOf secrets) p (chainLabels labels)
  | .leaf L, labels => pad64 (Extract.leafInput L.1.lay L.1.tree.val L.1.leaf.val
      ((List.range (chainCount L.1.lay)).map (endLabel secrets labels L.1)))
  | .node n, labels => if Active labels n then pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val) n.1.nonce.val
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1))) else phantom n
  | .wctChain p, labels => WCT9.ftsChainInputW p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
      (wctValueL secrets labels p.1 p.2.val)
  | .wctLeaf L, labels => pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
      (ftsPrevLabel labels L.index L.coord).1
      (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t)))
  | .wctNode n, labels => pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2 ^ (7 - n.1.level.val - 1) + n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val))
      (if n.1.level.val = 5 then (ftsPrevLabel labels n.1.index n.1.coord).2 else 0)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)))
  | .forest index, labels => pad64 (Extract.forestInput index.val
      ((List.range 9).map fun coord => (ftsLabel labels index (fin9 coord) 6 0, ftsLabel labels index (fin9 coord) 6 1)))
def SourcePos : Extract.Pos → Prop
  | .chain _ tree leaf i step => tree < 2 ^ 31 ∧ leaf < 4096 ∧ i < 58 ∧ step < 7
  | .leaf lay tree leaf => tree < 2 ^ treeBits lay ∧ leaf < 2 ^ height lay
  | .node lay tree level nd => tree < 2 ^ treeBits lay ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1) ∧
      (lay = 0 ∨ level + 1 < height lay)
  | .forest index => index < 2 ^ 31
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
theorem treeBits_lt (lay : Layer) : 2 ^ treeBits lay ≤ 2 ^ 31 :=
  Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide)
theorem source_routed_lt {lay : Layer} {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay) (hl : leaf < 2 ^ height lay) :
    tree * 2 ^ height lay + leaf < 2 ^ 31 := by
  fin_cases lay <;> simp [treeBits, Extract.treeBits, height] at ht hl ⊢ <;> omega
theorem source_tree_zero {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : lay = 0 → tree = 0 := by
  rintro rfl; simpa [treeBits, Extract.treeBits] using ht
theorem toPos_bounded (node : Node) : node.toPos.Bounded := by
  cases node with
  | chain p =>
      have := p.1.tree.isLt; have := p.1.leaf.isLt; have := p.1.chain.isLt; have := p.2.isLt
      exact ⟨by omega, by omega, by omega, by omega⟩
  | leaf L =>
      have := source_routed_lt L.2.1 L.2.2
      exact ⟨L.2.2, by omega⟩
  | node n =>
      have := n.1.tree.isLt
      exact ⟨by omega, n.2.1, n.2.2.2.2, source_tree_zero n.2.2.2.1, n.2.2.1⟩
  | wctChain p => exact ⟨p.1.1.isLt, p.1.2.1.isLt, p.1.2.2.1.isLt, p.1.2.2.2.isLt, p.2.isLt⟩
  | wctLeaf L => exact ⟨L.index.isLt, L.coord.isLt, L.child.isLt⟩
  | wctNode n => exact ⟨n.1.index.isLt, n.1.coord.isLt, n.1.level.isLt, n.2⟩
  | forest index => have := index.isLt; change index.val < 2 ^ 40; omega
/-- The position representative of a node (top-nonce layer: the trial index set to 0). -/
def Node.base : Node → Node
  | .node n => .node (withNonce n 0)
  | x => x
theorem toPos_base (node : Node) : node.base.toPos = node.toPos := by
  cases node <;> rfl
/-- `toPos` is injective up to the trial index (`Node.base`). -/
theorem toPos_injective_base {left right : Node} (h : left.toPos = right.toPos) : left.base = right.base := by
  cases left with
  | chain p =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i q
      simp only [Extract.Pos.chain.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hp : p = q := Prod.ext (ChainGraph.Address.ext h1 (Fin.ext h2) (Fin.ext h3) (Fin.ext h4)) (Fin.ext h5)
      rw [hp]
  | leaf L =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i M
      simp only [Extract.Pos.leaf.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨⟨lay, tree, leaf⟩, hL⟩ := L; obtain ⟨⟨lay', tree', leaf'⟩, hM⟩ := M
      simp only at h1 h2 h3
      subst h1
      have e2 := Fin.ext h2; have e3 := Fin.ext h3
      subst e2 e3
      rfl
  | node n =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i m
      simp only [Extract.Pos.node.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨⟨lay, tree, level, idx, k⟩, hn⟩ := n
      obtain ⟨⟨lay', tree', level', idx', k'⟩, hm⟩ := m
      simp only at h1 h2 h3 h4
      subst h1
      have e2 := Fin.ext h2; have e3 := Fin.ext h3; have e4 := Fin.ext h4
      subst e2 e3 e4
      rfl
  | wctChain p =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i q
      simp only [Extract.Pos.wctChain.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨⟨i, k, j, t⟩, s⟩ := p
      obtain ⟨⟨i', k', j', t'⟩, s'⟩ := q
      simp only at h1 h2 h3 h4 h5
      rw [Fin.ext h1, Fin.ext h2, Fin.ext h3, Fin.ext h4, Fin.ext h5]
  | wctLeaf L =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i M
      simp only [Extract.Pos.wctLeaf.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      cases L; cases M
      simp only at h1 h2 h3
      rw [Fin.ext h1, Fin.ext h2, Fin.ext h3]
  | wctNode n =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i m
      simp only [Extract.Pos.wctNode.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨⟨index, coord, level, idx⟩, hn⟩ := n
      obtain ⟨⟨index', coord', level', idx'⟩, hm⟩ := m
      simp only at h1 h2 h3 h4
      have e1 := Fin.ext h1; have e2 := Fin.ext h2; have e3 := Fin.ext h3; have e4 := Fin.ext h4
      subst e1 e2 e3 e4
      rfl
  | forest index =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i index'
      simp only [Extract.Pos.forest.injEq] at h
      rw [Fin.ext h]
theorem exists_toPos {p : Extract.Pos} (hp : SourcePos p) : ∃ node : Node, node.toPos = p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      exact ⟨.chain (⟨lay, ⟨tree, h1⟩, ⟨leaf, h2⟩, ⟨i, h3⟩⟩, ⟨step, h4⟩), rfl⟩
  | leaf lay tree leaf =>
      obtain ⟨h1, h2⟩ := hp
      exact ⟨.leaf ⟨⟨lay, ⟨tree, lt_of_lt_of_le h1 (treeBits_lt lay)⟩, ⟨leaf, lt_of_lt_of_le h2 (height_le_12 lay)⟩⟩,
        ⟨h1, h2⟩⟩, rfl⟩
  | node lay tree level nd =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hl : level < 12 := lt_of_lt_of_le h2 (SigGolfCandidate.T3M.Extract.height_le lay)
      have hn : nd < 2048 := lt_of_lt_of_le h3 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := SigGolfCandidate.T3M.Extract.height_le lay; omega)
          _ = 2048 := by norm_num)
      exact ⟨.node ⟨⟨lay, ⟨tree, lt_of_lt_of_le h1 (treeBits_lt lay)⟩, ⟨level, hl⟩, ⟨nd, hn⟩, 0⟩, h2, h3, h1, h4⟩, rfl⟩
  | forest index => exact ⟨.forest ⟨index, hp⟩, rfl⟩
  | wctChain index coord child t step =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hp
      exact ⟨.wctChain ((⟨index, h1⟩, ⟨coord, h2⟩, ⟨child, h3⟩, ⟨t, h4⟩), ⟨step, h5⟩), rfl⟩
  | wctLeaf index coord child =>
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨.wctLeaf ⟨⟨index, h1⟩, ⟨coord, h2⟩, ⟨child, h3⟩⟩, rfl⟩
  | wctNode index coord level nd =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hn : nd < 64 := lt_of_lt_of_le h4 (by
        calc 2 ^ (7 - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 64 := by norm_num)
      exact ⟨.wctNode ⟨⟨⟨index, h1⟩, ⟨coord, h2⟩, ⟨level, h3⟩, ⟨nd, hn⟩⟩, h4⟩, rfl⟩
theorem merkleNodeInput_length (lay tree heap : Nat) (left right : Digest) :
    (WCT9.merkleNodeInput lay tree heap left right).length = 64 := by
  simp only [WCT9.merkleNodeInput, zero16, List.length_append, List.length_replicate, bytesLE_length]
theorem pad64_merkleNodeInput (lay tree heap : Nat) (left right : Digest) :
    pad64 (WCT9.merkleNodeInput lay tree heap left right) = WCT9.merkleNodeInput lay tree heap left right := by
  unfold pad64; rw [merkleNodeInput_length]; simp
/-- Top-nonce layer: the cell of `node` is a phantom (an inactive tree node). -/
def PhantomAt (node : Node) (labels : Labels) : Prop := ∃ n, node = .node n ∧ ¬ Active labels n
theorem phantomCode_lt (n : TreeNode) : phantomCode n < 2 ^ 128 := by
  unfold phantomCode
  have := n.1.lay.isLt; have := n.1.level.isLt; have := n.1.idx.isLt; have := n.1.nonce.isLt; have := n.1.tree.isLt
  have h1 : n.1.lay.val + 4 * (n.1.level.val + 12 * (n.1.idx.val + 2048 * (n.1.nonce.val + 212992 * n.1.tree.val)))
      < 4 * 12 * 2048 * 212992 * 2 ^ 31 := by nlinarith
  calc _ < 4 * 12 * 2048 * 212992 * 2 ^ 31 := h1
    _ ≤ 2 ^ 128 := by norm_num
theorem phantomCode_injective : Function.Injective phantomCode := by
  intro a b h
  obtain ⟨⟨lay, tree, level, idx, k⟩, ha⟩ := a
  obtain ⟨⟨lay', tree', level', idx', k'⟩, hb⟩ := b
  unfold phantomCode at h
  simp only at h
  have := lay.isLt; have := lay'.isLt; have := level.isLt; have := level'.isLt; have := idx.isLt
  have := idx'.isLt; have := k.isLt; have := k'.isLt
  have e1 : lay.val = lay'.val := by omega
  have e2 : level.val = level'.val := by omega
  have e3 : idx.val = idx'.val := by omega
  have e4 : k.val = k'.val := by omega
  have e5 : tree.val = tree'.val := by omega
  have f1 := Fin.ext e1; have f2 := Fin.ext e2; have f3 := Fin.ext e3; have f4 := Fin.ext e4; have f5 := Fin.ext e5
  subst f1 f2 f3 f4 f5
  rfl
theorem phantom_length (n : TreeNode) : (phantom n).length = 192 := by
  simp [phantom, bytesLE_length]
theorem phantom_injective : Function.Injective phantom := by
  intro a b h
  unfold phantom at h
  have h1 := List.append_cancel_left (List.append_cancel_right h)
  have h2 := congrArg BitVec.toNat (bytesLE_injective h1)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (phantomCode_lt a),
    Nat.mod_eq_of_lt (phantomCode_lt b)] at h2
  exact phantomCode_injective h2
theorem Pos.len_ne_192 (p : Extract.Pos) : p.len ≠ 192 := by
  cases p <;> simp only [Extract.Pos.len] <;> (try split_ifs) <;> omega
theorem posOf_phantom (n : TreeNode) : Extract.posOf (phantom n) = none :=
  Extract.posOf_eq_none fun p _ hl _ => Pos.len_ne_192 p (by rw [← hl, phantom_length])
theorem cell_node_active {secrets : Secrets} {n : TreeNode} {labels : Labels} (h : Active labels n) :
    cell secrets (.node n) labels = pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val) n.1.nonce.val
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1))) := by
  simp only [cell, if_pos h]
theorem cell_node_inactive {secrets : Secrets} {n : TreeNode} {labels : Labels} (h : ¬ Active labels n) :
    cell secrets (.node n) labels = phantom n := by
  simp only [cell, if_neg h]
theorem cell_of_phantomAt {secrets : Secrets} {node : Node} {labels : Labels} (h : PhantomAt node labels) :
    ∃ n, node = .node n ∧ cell secrets node labels = phantom n := by
  obtain ⟨n, rfl, hn⟩ := h
  exact ⟨n, rfl, cell_node_inactive hn⟩
theorem not_phantomAt_node {n : TreeNode} {labels : Labels} (h : Active labels n) : ¬ PhantomAt (.node n) labels := by
  rintro ⟨m, hm, hn⟩
  cases hm
  exact hn h
/-- Every non-phantom cell has its position's honest length (length-aware decoding, C3). -/
theorem cell_length (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    (cell secrets node labels).length = node.toPos.len := by
  cases node with
  | chain p =>
      change (rowW p _).length = _
      rw [rowW_length]; rfl
  | leaf L =>
      simp only [cell, Extract.leafInput, Node.toPos, Extract.Pos.len]
      rw [Cost.pad64_length, SigGolfCandidate.T3.leafInput_length]
      simp only [List.length_map, List.length_range]
      by_cases h0 : L.1.lay = 0
      · rw [if_pos h0, if_pos h0, h0]; decide
      · rw [if_neg h0, if_neg h0, chainCount_lower h0]
  | node n =>
      have ha : Active labels n := by
        by_contra ha; exact hp ⟨n, rfl, ha⟩
      rw [cell_node_active ha]
      simp only [Node.toPos, Extract.Pos.len]
      rw [WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]
  | wctChain p =>
      simp only [cell, WCT9.ftsChainInputW_length, Node.toPos, Extract.Pos.len]
  | wctLeaf L =>
      simp only [cell, Extract.wctLeafInputP, Node.toPos, Extract.Pos.len]
      rw [Cost.pad64_length, Extract.listInput_length']
      simp only [List.length_cons, List.length_drop, List.length_ofFn]
  | wctNode n =>
      simp only [cell, Node.toPos, Extract.Pos.len]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]
  | forest index =>
      simp only [cell, Extract.forestInput, Node.toPos, Extract.Pos.len]
      rw [Cost.pad64_length, WCT9.forestInput_length _ _ (by simp)]

theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.hdrBlock (cell secrets node labels) = bytesLE 16 node.toPos.hdr := by
  cases node with
  | chain p =>
      change Extract.hdrBlock (WCT9.chainInputW p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val _) = _
      exact WCT9.chainInputW_header _ _ _ _ _ _
  | leaf L =>
      simp only [cell]
      rw [Extract.hdrBlock_leafInput]
      rfl
  | node n =>
      have ha : Active labels n := by
        by_contra ha; exact hp ⟨n, rfl, ha⟩
      rw [cell_node_active ha, Extract.hdrBlock_merkleNodeInputN]
      rfl
  | wctChain p =>
      simp only [cell]
      rw [Extract.hdrBlock_ftsChainInputW]
      rfl
  | wctLeaf L =>
      simp only [cell]
      rw [Extract.hdrBlock_wctLeafInputP]
      rfl
  | wctNode n =>
      simp only [cell]
      rw [Extract.hdrBlock_nodeInputP]
      rfl
  | forest index =>
      simp only [cell]
      rw [Extract.hdrBlock_forestInput]
      rfl
/-- Two active trials of one position have different nonce slots. -/
theorem merkleNodeInputN_nonce_inj {lay tree heap k k' : Nat} {l r l' r' : Digest} (hk : k < 2 ^ 64)
    (hk' : k' < 2 ^ 64)
    (h : pad64 (WCT9.merkleNodeInputN lay tree heap k l r) = pad64 (WCT9.merkleNodeInputN lay tree heap k' l' r')) :
    k = k' := by
  rw [WCT9.pad64_merkleNodeInputN, WCT9.pad64_merkleNodeInputN] at h
  unfold WCT9.merkleNodeInputN at h
  have h1 := List.append_inj_left' h (by simp [bytesLE_length])
  have h2 := List.append_inj_right' h1 (by simp [bytesLE_length])
  exact WCT9.nonceDigest_inj hk hk' (bytesLE_injective h2)
/-- Separation of the trial-node graph (phantoms included). -/
theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  by_cases hl : PhantomAt left before
  · obtain ⟨n, rfl, hn⟩ := cell_of_phantomAt (secrets := secrets) hl
    by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      rw [hn, hm] at heq
      exact hne (congrArg Node.node (phantom_injective heq))
    · have h1 := cell_length secrets right after hr
      rw [← heq, hn, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
  · by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      have h1 := cell_length secrets left before hl
      rw [heq, hm, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
    · have h1 := hdrBlock_cell secrets left before hl
      have h2 := hdrBlock_cell secrets right after hr
      have hlen : left.toPos.len = right.toPos.len := by
        rw [← cell_length secrets left before hl, ← cell_length secrets right after hr, heq]
      rw [heq] at h1
      have hpos := Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right) hlen
        (bytesLE_injective (h1.symm.trans h2))
      have hb := toPos_injective_base hpos
      cases left with
      | node n =>
          cases right with
          | node m =>
              have ha : Active before n := by by_contra ha; exact hl ⟨n, rfl, ha⟩
              have hb' : Active after m := by by_contra hb'; exact hr ⟨m, rfl, hb'⟩
              rw [cell_node_active ha, cell_node_active hb'] at heq
              have hk := merkleNodeInputN_nonce_inj (lt_trans n.1.nonce.isLt (by norm_num))
                (lt_trans m.1.nonce.isLt (by norm_num)) (by
                  have he : (Node.node n).toPos = (Node.node m).toPos := hpos
                  simp only [Node.toPos, Extract.Pos.node.injEq] at he
                  obtain ⟨e1, e2, e3, e4⟩ := he
                  rw [e1, e2, e3, e4] at heq
                  exact heq)
              apply hne
              have hnm : n = m := by
                have hw : withNonce n 0 = withNonce m 0 := Node.node.inj hb
                rw [← withNonce_self n, ← withNonce_self m, ← withNonce_withNonce n 0,
                  ← withNonce_withNonce m 0, hw, hk]
              rw [hnm]
          | _ => simp [Node.base] at hb
      | _ =>
          cases right <;> first
            | exact hne hb
            | (simp [Node.base] at hb)
theorem treeNodeAt_level {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.level.val = level := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem ftsNodeAt_level {index : Fin (2^31)} {coord : Fin 9} {level c : Nat} {n : WctNodePos}
    (h : ftsNodeAt index coord level c = some n) : n.1.level.val = level := by
  unfold ftsNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
/-- Depth bound of the values of tree level `level` (levels are spaced by `2^18` trial depths, all layers). -/
def levelDepth (_lay : Layer) (level : Nat) : Nat := 8 + level * 2 ^ 18
theorem depth_node (n : TreeNode) :
    (Node.node n).depth = levelDepth n.1.lay n.1.level.val + n.1.nonce.val := rfl
theorem depth_withNonce_lt (n : TreeNode) {j : Nat} (hj : j < trialCap n.1.lay n.1.level.val) {level : Nat}
    (hl : n.1.level.val + 1 ≤ level) : (Node.node (withNonce n j)).depth < levelDepth n.1.lay level := by
  have hc := trialCap_le n.1.lay n.1.level.val
  rw [depth_node]
  simp only [withNonce_lay, withNonce_level]
  rw [withNonce_nonce n (by omega)]
  unfold levelDepth
  have : (n.1.level.val + 1) * 2 ^ 18 ≤ level * 2 ^ 18 := Nat.mul_le_mul_right _ hl
  have : n.1.level.val * 2 ^ 18 + 2 ^ 18 ≤ level * 2 ^ 18 := by rw [Nat.add_mul, one_mul] at this; exact this
  have h2 : (2 : Nat) ^ 18 = 262144 := by norm_num
  omega
theorem find?_congr' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.find?_cons, h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
theorem trialFails_congr {left right : Labels} {n : TreeNode} {j : Nat}
    (h : left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    trialFails left n j ↔ trialFails right n j := by
  unfold trialFails; rw [h]
theorem selNonce_congr {left right : Labels} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    selNonce left n = selNonce right n := by
  unfold selNonce
  congr 1
  apply find?_congr'
  intro j hj
  rw [List.mem_range] at hj
  simp only [decide_eq_decide.mpr (trialFails_congr (h j hj))]
theorem selNonce_lt (labels : Labels) (n : TreeNode) : selNonce labels n < trialCap n.1.lay n.1.level.val := by
  have hc := trialCap_pos n.1.lay n.1.level.val
  unfold selNonce
  cases hf : (List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFails labels n j) with
  | none => simp only [Option.getD_none]; omega
  | some j =>
      simp only [Option.getD_some]
      exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
theorem selNode_congr {left right : Labels} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    selNode left n = selNode right n := by
  unfold selNode; rw [selNonce_congr h]
theorem selNode_label_congr {left right : Labels} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    left (.node (selNode left n)) = right (.node (selNode right n)) := by
  rw [selNode_congr h]
  exact h _ (selNonce_lt right n)
/-- A single-trial position (lower trees, the root, any node off the top tree's nonce levels) selects nonce 0. -/
theorem selNonce_of_cap_one {labels : Labels} {n : TreeNode} (h : trialCap n.1.lay n.1.level.val = 1) :
    selNonce labels n = 0 := by
  have := selNonce_lt labels n; omega
theorem selNode_of_cap_one {labels : Labels} {n : TreeNode} (h : trialCap n.1.lay n.1.level.val = 1)
    (h0 : n.1.nonce.val = 0) : selNode labels n = n := by
  unfold selNode
  rw [selNonce_of_cap_one h, ← h0, withNonce_self]
theorem trialCap_lower {lay : Layer} (h : lay ≠ 0) (level : Nat) : trialCap lay level = 1 := by
  unfold trialCap; rw [if_neg (fun h' => h h'.1)]
theorem trialCap_root (lay : Layer) : trialCap lay 11 = 1 := by
  unfold trialCap; rw [if_neg (fun h' => by omega)]
theorem treeNodeAt_nonce {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.nonce.val = 0 := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem treeNodeAt_lay {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.lay = lay := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, other.depth < levelDepth lay level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L =>
        simp only
        rw [h _ (by simp only [Node.depth, levelDepth]; omega)]
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        have hl := treeNodeAt_level hn
        have hlay := treeNodeAt_lay hn
        rw [selNode_label_congr (fun j hj => h _ (by
          have := depth_withNonce_lt n hj (level := level) (by omega)
          rw [hlay] at this; exact this))]
theorem ftsNodeAt_coord {index : Fin (2^31)} {coord : Fin 9} {level c : Nat} {n : WctNodePos}
    (h : ftsNodeAt index coord level c = some n) : n.1.coord = coord := by
  unfold ftsNodeAt at h
  split_ifs at h with hv
  cases h
  rfl
theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (h : ∀ other : Node, other.depth < 5 + 7 * coord.val + level → left other = right other) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · have hd : (Node.wctLeaf ⟨index, coord, ⟨c, hc⟩⟩).depth < 5 + 7 * coord.val + level := by
      show 4 + 7 * coord.val < _; omega
    rw [h _ hd]
  · rfl
  all_goals
    cases hn : ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n =>
        have hd : (Node.wctNode n).depth < 5 + 7 * coord.val + level := by
          show 5 + 7 * n.1.coord.val + n.1.level.val < _
          rw [ftsNodeAt_level hn, ftsNodeAt_coord hn]; omega
        simp only [h _ hd]
theorem ftsPrevLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (h : ∀ other : Node, other.depth < 4 + 7 * coord.val → left other = right other) :
    ftsPrevLabel left index coord = ftsPrevLabel right index coord := by
  unfold ftsPrevLabel
  split_ifs with hz
  · rfl
  · have hc : 0 < coord.val := Nat.pos_of_ne_zero hz
    rw [ftsLabel_congr left right index _ 6 0 (fun other ho => h other (by simp only at ho; omega)),
      ftsLabel_congr left right index _ 6 1 (fun other ho => h other (by simp only at ho; omega))]
/-- An earlier trial is shallower. -/
theorem depth_trial_lt (n : TreeNode) {j : Nat} (hj : j < n.1.nonce.val) :
    (Node.node (withNonce n j)).depth < (Node.node n).depth := by
  have hk := n.1.nonce.isLt
  rw [depth_node, depth_node]
  simp only [withNonce_lay, withNonce_level]
  rw [withNonce_nonce n (by omega)]
  omega
theorem activeCongr (left right : Labels) (n : TreeNode)
    (h : ∀ j < n.1.nonce.val, left (.node (withNonce n j)) = right (.node (withNonce n j))) :
    Active left n ↔ Active right n := by
  unfold Active
  exact and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => trialFails_congr (h j hj)
theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀ other : Node, other.depth < node.depth → left other = right other) :
    cell secrets node left = cell secrets node right := by
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels left) =
        inputW (seedsOf secrets) p (chainLabels right)
      unfold inputW priorW
      split_ifs with hz
      · rfl
      · have hd := h (.chain (ChainGraph.predecessor p)) (by
          simp only [Node.depth, ChainGraph.predecessor]; omega)
        simp only [chainLabels, hd]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets left L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets right L.1) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel
        rw [h _ (by simp only [Node.depth, endPt]; exact Nat.mod_lt _ (by decide))]
      simp only [cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by rw [depth_node]; omega))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by rw [depth_node]; omega))
      have ha : Active left n ↔ Active right n := activeCongr left right n (fun j hj => h _ (depth_trial_lt n hj))
      simp only [cell, hl, hr, ha]
  | wctChain p =>
      have hv : wctValueL secrets left p.1 p.2.val = wctValueL secrets right p.1 p.2.val := by
        unfold wctValueL
        split_ifs with hz
        · rfl
        · rw [h _ (by simp only [Node.depth]; have := p.2.isLt; omega)]
      simp only [cell, hv]
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel left (L.index, L.coord, L.child, t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel right (L.index, L.coord, L.child, t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [h _ (by show 3 < 4 + 7 * L.coord.val; omega)]
      have hpad := ftsPrevLabel_congr left right L.index L.coord
        (fun other ho => h other (by show other.depth < 4 + 7 * L.coord.val; omega))
      simp only [cell, hends, hpad]
  | wctNode n =>
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hpad := ftsPrevLabel_congr left right n.1.index n.1.coord
        (fun other ho => h other (by show other.depth < 5 + 7 * n.1.coord.val + n.1.level.val; omega))
      simp only [cell, hl, hr, hpad]
  | forest index =>
      have hroots : ((List.range 9).map fun coord =>
            (ftsLabel left index (fin9 coord) 6 0, ftsLabel left index (fin9 coord) 6 1)) =
          ((List.range 9).map fun coord =>
            (ftsLabel right index (fin9 coord) 6 0, ftsLabel right index (fin9 coord) 6 1)) := by
        apply List.map_congr_left
        intro coord _
        have hc := (fin9 coord).isLt
        rw [ftsLabel_congr left right index (fin9 coord) 6 0
            (fun other ho => h other (show other.depth < 70 by omega)),
          ftsLabel_congr left right index (fin9 coord) 6 1
            (fun other ho => h other (show other.depth < 70 by omega))]
      simp only [cell, hroots]
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.posOf (cell secrets node labels) = some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (cell_length secrets node labels hp) (hdrBlock_cell secrets node labels hp)
theorem posOf_cell_phantom (secrets : Secrets) (node : Node) (labels : Labels) (hp : PhantomAt node labels) :
    Extract.posOf (cell secrets node labels) = none := by
  obtain ⟨n, -, hc⟩ := cell_of_phantomAt (secrets := secrets) hp
  rw [hc, posOf_phantom]
/-- A cell decoding to a position belongs to a non-phantom node of that position. -/
theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input = some node.toPos) (h : input = cell secrets node' labels) :
    node'.toPos = node.toPos ∧ ¬ PhantomAt node' labels := by
  subst h
  by_cases hp : PhantomAt node' labels
  · rw [posOf_cell_phantom secrets node' labels hp] at hpos; cases hpos
  · rw [posOf_cell secrets node' labels hp] at hpos
    exact ⟨Option.some.inj hpos, hp⟩
theorem height_pos (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
def rootNode : TreeNode :=
  ⟨⟨0, 0, ⟨height 0 - 1, by decide⟩, ⟨0, by decide⟩, 0⟩, by decide⟩
def ftsTopNode (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) : WctNodePos :=
  ⟨⟨index, coord, ⟨5, by decide⟩, ⟨b.val, by have := b.isLt; omega⟩⟩, show b.val < 2 ^ (7 - 5 - 1) by
    have := b.isLt; omega⟩
theorem height_ge_two (lay : Layer) : 2 ≤ height lay := by fin_cases lay <;> decide
def topNode (lay : Layer) (tree : Fin (2^31)) (ht : tree.val < 2 ^ treeBits lay) (b : Fin 2) : TreeNode :=
  ⟨⟨lay, tree, ⟨height lay - 2, by have := SigGolfCandidate.T3M.Extract.height_le lay; omega⟩,
    ⟨b.val, by have := b.isLt; omega⟩, 0⟩,
    ⟨show height lay - 2 < height lay by have := height_ge_two lay; omega, by
      have := height_ge_two lay
      show b.val < 2 ^ (height lay - (height lay - 2) - 1)
      rw [show height lay - (height lay - 2) - 1 = 1 by omega]
      have := b.isLt; omega, ht, Or.inr (by have := height_ge_two lay; show height lay - 2 + 1 < height lay; omega)⟩⟩
theorem treeLabel_top (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (ht : tree.val < 2 ^ treeBits lay)
    (b : Fin 2) :
    treeLabel labels lay tree (height lay - 1) b.val =
      (Node.node (topNode lay tree ht b)).toPos.proj (labels (.node (selNode labels (topNode lay tree ht b)))) := by
  have h2 := height_ge_two lay
  unfold treeLabel
  rw [if_neg (by omega)]
  have hv : height lay - 1 - 1 < height lay ∧ b.val < 2 ^ (height lay - (height lay - 1 - 1) - 1) ∧
      tree.val < 2 ^ treeBits lay ∧ (lay = 0 ∨ height lay - 1 - 1 + 1 < height lay) := by
    refine ⟨by omega, ?_, ht, Or.inr (by omega)⟩
    rw [show height lay - (height lay - 1 - 1) - 1 = 1 by omega]
    have := b.isLt; omega
  unfold treeNodeAt
  rw [dif_pos hv]
  have e : height lay - 1 - 1 = height lay - 2 := by omega
  simp only [e]
  rfl
theorem selNode_rootNode (labels : Labels) : selNode labels rootNode = rootNode :=
  selNode_of_cap_one (trialCap_root 0) rfl
theorem treeLabel_root (labels : Labels) :
    treeLabel labels 0 0 (height 0) 0 = (labels (.node rootNode)).extractLsb' 0 128 := by
  unfold treeLabel
  rw [if_neg (by decide)]
  unfold treeNodeAt
  rw [dif_pos (by decide)]
  change (Node.node rootNode).toPos.proj (labels (.node (selNode labels rootNode))) = _
  rw [selNode_rootNode]
  rfl
theorem ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    ftsLabel labels index coord 6 b.val = (labels (.wctNode (ftsTopNode index coord b))).extractLsb' 128 128 := by
  unfold ftsLabel
  rw [if_neg (by omega)]
  unfold ftsNodeAt
  rw [dif_pos (show 6 - 1 < 6 ∧ b.val < 2 ^ (7 - (6 - 1) - 1) by have := b.isLt; omega)]
  rfl
noncomputable def canonInputs : Finset HashInput :=
  (Finset.univ : Finset (Secrets × Labels × Node)).image fun x => cell x.1 x.2.2 x.2.1
attribute [irreducible] canonInputs
theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels ∈ canonInputs := by
  rw [canonInputs]
  exact Finset.mem_image.mpr ⟨(secrets, labels, node), Finset.mem_univ _, rfl⟩
theorem cell_length_le (secrets : Secrets) (node : Node) (labels : Labels) :
    (cell secrets node labels).length ≤ 4096 := by
  cases node with
  | chain p =>
      change (rowW p _).length ≤ 4096
      rw [rowW_length]; omega
  | leaf L =>
      simp only [cell, Extract.leafInput]
      rw [Cost.pad64_length, SigGolfCandidate.T3.leafInput_length]
      have hc : chainCount L.1.lay ≤ 58 := chainCount_bound L.1.lay
      simp only [List.length_map, List.length_range]
      split_ifs <;> omega
  | node n =>
      by_cases ha : Active labels n
      · rw [cell_node_active ha, WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]; omega
      · rw [cell_node_inactive ha, phantom_length]; omega
  | wctChain p =>
      simp only [cell, WCT9.ftsChainInputW_length]
      omega
  | wctLeaf L =>
      simp only [cell, Extract.wctLeafInputP]
      rw [Cost.pad64_length, Extract.listInput_length']
      simp only [List.length_cons, List.length_drop, List.length_ofFn]
      omega
  | wctNode n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]; omega
  | forest index =>
      simp only [cell, Extract.forestInput]
      rw [Cost.pad64_length, WCT9.forestInput_length _ _ (by simp)]
      omega
theorem canonInputs_subset_publicUniverse : canonInputs ⊆ SeccLaw.publicUniverse := by
  intro input hinput
  rw [canonInputs, Finset.mem_image] at hinput
  obtain ⟨x, -, rfl⟩ := hinput
  exact SeccLaw.mem_publicUniverse _ (cell_length_le _ _ _)
noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩
theorem cellIn_separated (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) :
    Separated (cellIn U hU secrets) := by
  intro left right hne before after heq
  exact cell_separated secrets left right hne before after (congrArg Subtype.val heq)
theorem cellIn_injective (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) (labels : Labels) :
    Function.Injective (fun node => cellIn U hU secrets node labels) := by
  intro left right heq
  by_contra hne
  exact cellIn_separated U hU secrets left right hne labels labels heq
noncomputable def order : List Node :=
  (Finset.univ : Finset Node).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))
attribute [irreducible] order
theorem order_nodup : order.Nodup := by
  unfold order
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
theorem mem_order (node : Node) : node ∈ order := by
  rw [order, List.mem_mergeSort]
  simp
theorem order_sorted : order.Pairwise (fun left right => left.depth ≤ right.depth) := by
  have h := List.pairwise_mergeSort
    (le := fun left right : Node => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    (Finset.univ : Finset Node).toList
  simpa only [order, decide_eq_true_eq] using h
def advance (node : Node) (output : HashOutput) (labels : Labels) : Labels := Function.update labels node output
noncomputable def graph (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (table : U → HashOutput) : Labels :=
  read (cellIn U hU secrets) advance table order (fun _ => 0)
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order
section Laws
variable (U : Finset HashInput) (hU : canonInputs ⊆ U)
noncomputable local instance instSampleableTypeHashOutput_canonGraph : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem programmed_at (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (node : Node) :
    programmed U hU secrets labels residual (cellIn U hU secrets node labels) = labels node :=
  patch_at _ (cellIn_injective U hU secrets labels) labels residual order node (mem_order node)
theorem programmed_other (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, query.val ≠ cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node _ heq
  exact hquery node (congrArg Subtype.val heq)
theorem read_eq_plant (secrets : Secrets) (nodes : List Node) (hnodup : nodes.Nodup) (before : Labels) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (read (cellIn U hU secrets) advance table nodes before, table)] =
      𝒮[plant (cellIn U hU secrets) advance nodes before] :=
  evalDist_read_eq_plant (cellIn U hU secrets) advance (cellIn_separated U hU secrets) nodes hnodup before
theorem replay_eq_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) (hagrees : ∀ node, node ∉ nodes → before node = labels node) :
    replay (cellIn U hU secrets) advance labels residual nodes before =
      (labels, patch (fun node => cellIn U hU secrets node labels) labels residual nodes) := by
  induction nodes generalizing before with
  | nil =>
      have hbefore : before = labels := funext fun node => hagrees node (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cellIn U hU secrets first before = cellIn U hU secrets first labels := by
        apply Subtype.ext
        apply cell_congr
        intro other hother
        apply hagrees
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · rw [heq] at hother; omega
        · have := hdepth _ hmem; omega
      have hafter : ∀ node, node ∉ rest → advance first (labels first) before node = labels node := by
        intro node hnode
        unfold advance
        by_cases heq : node = first
        · subst node; rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees node (fun hmem => (List.mem_cons.mp hmem).elim heq hnode)
      rw [replay, ih hsorted _ hafter, patch, hinput]
theorem plant_eq_uniform_programmed (secrets : Secrets) :
    𝒮[plant (cellIn U hU secrets) advance order (fun _ => 0)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] := by
  rw [evalDist_plant_eq_replay _ _ _ order_nodup]
  apply evalSPMF_bind_congr_left
  intro labels
  apply evalSPMF_bind_congr_left
  intro residual
  rw [replay_eq_programmed U hU secrets labels residual order order_sorted _
    (fun node hnode => (hnode (mem_order node)).elim)]
  rfl
theorem graph_eq_uniform_programmed (secrets : Secrets) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (graph U hU secrets table, table)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] :=
  (read_eq_plant U hU secrets order order_nodup _).trans (plant_eq_uniform_programmed U hU secrets)
theorem graph_bind_eq_uniform_programmed {Result : Type} (secrets : Secrets)
    (next : Labels → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (graph U hU secrets table) table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next labels (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
    law >>= fun result => 𝒮[next result.1 result.2]) (graph_eq_uniform_programmed U hU secrets)
  simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
theorem uniform_bind_programmed {Result : Type} (secrets : Secrets) (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] :=
  graph_bind_eq_uniform_programmed U hU secrets (fun _ table => next table)
end Laws
def fullHalf (n : Nat) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩
/-- Half-cell of FTS coefficient `(index, coord, j)`: half `j % 2` of `ftsSeedPair index coord (j / 2)`. -/
def wctCoefCoordinate (c : WctCoef) : ChainGraph.HalfCoordinate :=
  (.inl (WCT9.ftsSeedHeader c.2.1.val c.1.val (c.2.2.val / 2)), fullHalf c.2.2.val)
/-- Half-cell of secret `a`: for an address `(lay, tree, f, j)` with `j < famSize lay f` it is the packed half
`famOrd lay f j` of `lowerSeedPair lay tree` (coefficient `j` of family `f`); other addresses get distinct unused
cells. -/
def seedCoordinateP (a : Address) : ChainGraph.HalfCoordinate :=
  if a.chain.val < WCT9.famSize a.layer a.leaf.val then
    (.inl (WCT9.lowerSeedHeader a.layer a.tree.val (famOrd a.layer a.leaf.val a.chain.val / 2)),
      fullHalf (famOrd a.layer a.leaf.val a.chain.val))
  else (.inl (header 0 a.layer.val a.tree.val (a.chain.val / 2) (a.leaf.val + 1)), fullHalf a.chain.val)
def secretCoordinate : SecretIndex → ChainGraph.HalfCoordinate := Sum.elim seedCoordinateP wctCoefCoordinate
theorem fullHalf_val (n : Nat) : (fullHalf n).val = n % 2 := rfl
theorem famOrd_pair_lt' (a : Address) : famOrd a.layer a.leaf.val a.chain.val / 2 < 2 ^ 32 := by
  have h1 := a.leaf.isLt; have h2 := a.chain.isLt
  have h3 := WCT9.famBase_le a.layer
  have : WCT9.famBase a.layer * a.leaf.val ≤ 39 * 4096 := Nat.mul_le_mul h3 (by omega)
  unfold famOrd
  omega
theorem famOrd_inj {lay : Layer} {f f' j j' : Nat} (hj : j < WCT9.famBase lay) (hj' : j' < WCT9.famBase lay)
    (h : famOrd lay f j = famOrd lay f' j') : f = f' ∧ j = j' := by
  unfold famOrd at h
  rcases Nat.lt_or_ge f f' with hlt | hge
  · exfalso
    have : WCT9.famBase lay * f + WCT9.famBase lay ≤ WCT9.famBase lay * f' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge f' f with hlt' | hge'
    · exfalso
      have : WCT9.famBase lay * f' + WCT9.famBase lay ≤ WCT9.famBase lay * f := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hff : f = f' := by omega
      subst hff
      exact ⟨rfl, by omega⟩
theorem wctCoefCoordinate_injective : Function.Injective wctCoefCoordinate := by
  intro left right heq
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  simp only [wctCoefCoordinate, fullHalf_val, Sum.inl.injEq] at hp hh
  obtain ⟨⟨i, hi⟩, ⟨k, hk⟩, ⟨j, hj⟩⟩ := left
  obtain ⟨⟨i', hi'⟩, ⟨k', hk'⟩, ⟨j', hj'⟩⟩ := right
  simp only at hp hh
  obtain ⟨e1, e2, e3⟩ := WCT9.ftsSeedHeader_injective (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hp
  have e4 : j = j' := by omega
  subst e1 e2 e4
  rfl
theorem seedCoordinateP_injective : Function.Injective seedCoordinateP := by
  intro left right heq
  have hl := left.layer.isLt; have hr := right.layer.isLt
  have hlt := left.tree.isLt; have hrt := right.tree.isLt
  have hli := left.leaf.isLt; have hri := right.leaf.isLt
  have hlc := left.chain.isLt; have hrc := right.chain.isLt
  have pl := famOrd_pair_lt' left; have pr := famOrd_pair_lt' right
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  unfold seedCoordinateP at hp hh
  by_cases hc : left.chain.val < WCT9.famSize left.layer left.leaf.val <;>
    by_cases hc' : right.chain.val < WCT9.famSize right.layer right.leaf.val
  · rw [if_pos hc, if_pos hc'] at hp hh
    simp only [fullHalf_val, Sum.inl.injEq] at hp hh
    unfold WCT9.lowerSeedHeader at hp
    obtain ⟨-, e1, e2, e3, -⟩ := header_injective (by decide) (by omega) (by omega) pl (by omega)
      (by decide) (by omega) (by omega) pr (by omega) hp
    have elay : left.layer = right.layer := Fin.ext e1
    rw [elay] at e3 hh hc
    have eo : famOrd right.layer left.leaf.val left.chain.val =
        famOrd right.layer right.leaf.val right.chain.val := by omega
    obtain ⟨e4, e5⟩ := famOrd_inj (lt_of_lt_of_le hc (WCT9.famSize_le_base _ _))
      (lt_of_lt_of_le hc' (WCT9.famSize_le_base _ _)) eo
    exact ChainGraph.Address.ext elay (Fin.ext e2) (Fin.ext e4) (Fin.ext e5)
  · exfalso
    rw [if_pos hc, if_neg hc'] at hp
    simp only [Sum.inl.injEq, WCT9.lowerSeedHeader] at hp
    have := (header_injective (by decide) (by omega) (by omega) pl (by omega)
      (by decide) (by omega) (by omega) (by omega) (by omega) hp).2.2.2.2
    omega
  · exfalso
    rw [if_neg hc, if_pos hc'] at hp
    simp only [Sum.inl.injEq, WCT9.lowerSeedHeader] at hp
    have := (header_injective (by decide) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by omega) (by omega) pr (by omega) hp).2.2.2.2
    omega
  · rw [if_neg hc, if_neg hc'] at hp hh
    simp only [fullHalf_val, Sum.inl.injEq] at hp hh
    obtain ⟨-, e1, e2, e3, e4⟩ := header_injective (by decide) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by omega) (by omega) (by omega) (by omega) hp
    exact ChainGraph.Address.ext (Fin.ext e1) (Fin.ext e2) (Fin.ext (by omega)) (Fin.ext (by omega))
theorem seedCoordinateP_ne_wct (a : Address) (g : WctCoef) : seedCoordinateP a ≠ wctCoefCoordinate g := by
  intro heq
  have hp := congrArg Prod.fst heq
  unfold seedCoordinateP wctCoefCoordinate at hp
  split_ifs at hp
  · exact WCT9.ftsSeedHeader_ne_lowerSeedHeader _ _ _ _ _ _ (Sum.inl.inj hp).symm
  · exact WCT9.ftsSeedHeader_ne_tag _ _ _ 0 _ _ _ _ (by decide) (Sum.inl.inj hp).symm
theorem secretCoordinate_injective : Function.Injective secretCoordinate := by
  intro left right heq
  cases left with
  | inl a =>
      cases right with
      | inl b => exact congrArg Sum.inl (seedCoordinateP_injective heq)
      | inr g => exact (seedCoordinateP_ne_wct a g heq).elim
  | inr f =>
      cases right with
      | inl b => exact (seedCoordinateP_ne_wct b f heq.symm).elim
      | inr g => exact congrArg Sum.inr (wctCoefCoordinate_injective heq)
def privateSecrets (table : FullGame.FullTable) : Secrets := ChainGraph.halves table ∘ secretCoordinate
abbrev OtherHalf := {coordinate : ChainGraph.HalfCoordinate // coordinate ∉ Set.range secretCoordinate}
abbrev OtherHalves := OtherHalf → Digest
noncomputable def splitEquiv : ChainGraph.HalfTable ≃ Secrets × OtherHalves :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range secretCoordinate)).symm.trans
    ((Equiv.ofInjective secretCoordinate secretCoordinate_injective).symm.sumCongr (Equiv.refl OtherHalf)))
    (Equiv.refl Digest)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
theorem splitEquiv_fst (table : ChainGraph.HalfTable) : (splitEquiv table).1 = table ∘ secretCoordinate := by
  funext index
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
noncomputable def privateEquiv : FullGame.FullTable ≃ Secrets × OtherHalves :=
  ChainGraph.halvesEquiv.trans splitEquiv
theorem privateEquiv_fst (table : FullGame.FullTable) : (privateEquiv table).1 = privateSecrets table :=
  splitEquiv_fst (ChainGraph.halves table)
theorem privateSecrets_symm (secrets : Secrets) (other : OtherHalves) :
    privateSecrets (privateEquiv.symm (secrets, other)) = secrets := by
  rw [← privateEquiv_fst, Equiv.apply_symm_apply]
def layerMsgEquiv : WCT9.LayerMsg ≃ Digest ⊕ (Digest × Digest) where
  toFun
    | .forest d => .inl d
    | .pair l r => .inr (l, r)
  invFun
    | .inl d => .forest d
    | .inr p => .pair p.1 p.2
  left_inv m := by cases m <;> rfl
  right_inv x := by rcases x with d | ⟨l, r⟩ <;> rfl
set_option warn.classDefReducibility false in
noncomputable def layerMsgFintype : Fintype WCT9.LayerMsg := Fintype.ofEquiv _ layerMsgEquiv.symm
attribute [irreducible] layerMsgFintype
abbrev EncKey := (Layer × Fin (2^31) × Fin 4096 × WCT9.LayerMsg) × Fin (2^22)
def encQuery (key : EncKey) : HashInput :=
  pad64 (WCT9.layerEncodingInput key.1.1 key.1.2.1.val key.1.2.2.1.val key.1.2.2.2 (BitVec.ofNat 32 key.2.val))
set_option warn.classDefReducibility false in
noncomputable def encodingKeyFintype : Fintype EncKey :=
  @instFintypeProd _ _ (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance layerMsgFintype))) inferInstance
attribute [irreducible] encodingKeyFintype
noncomputable def encInputs : Finset HashInput :=
  (@Finset.univ _ encodingKeyFintype).image encQuery
attribute [irreducible] encInputs
theorem encQuery_mem (key : EncKey) : encQuery key ∈ encInputs := by
  rw [encInputs]
  exact Finset.mem_image_of_mem _ (@Finset.mem_univ _ encodingKeyFintype key)
theorem encQuery_length (key : EncKey) : (encQuery key).length = 64 := by
  obtain ⟨⟨lay, tree, leaf, msg⟩, c⟩ := key
  cases msg <;> simp [encQuery, WCT9.layerEncodingInput, encodingInput, WCT9.pairEncodingInputP, pad64,
    bytesLE_length]
theorem encInputs_subset_publicUniverse : encInputs ⊆ SeccLaw.publicUniverse := by
  intro input hinput
  rw [encInputs, Finset.mem_image] at hinput
  obtain ⟨key, -, rfl⟩ := hinput
  apply SeccLaw.mem_publicUniverse
  rw [encQuery_length]
  unfold SeccLaw.maxInputLength
  omega
section PrivateLaws
noncomputable local instance instFintypeCoordinate_canonGraph : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonGraph : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeHashOutput_canonGraph_1 : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels_1 : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance instFintypeSecrets_canonGraph : Fintype Secrets := inferInstance
noncomputable local instance instFintypeOtherHalves_canonGraph : Fintype OtherHalves := inferInstance
noncomputable local instance instSampleableTypeProdSecretsOtherHalves : SampleableType (Secrets × OtherHalves) :=
  @SampleableType.ofFintype _ (instFintypeProd Secrets OtherHalves) _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem uniform_private_split :
    𝒮[privateEquiv <$> ($ᵗ FullGame.FullTable : ProbComp _)] =
      𝒮[do let secrets ← ($ᵗ Secrets : ProbComp _); let other ← ($ᵗ OtherHalves : ProbComp _); pure (secrets, other)] :=
  (evalSPMF_map_bijective_uniform_cross (α := FullGame.FullTable) (β := Secrets × OtherHalves)
    privateEquiv privateEquiv.bijective).trans (FullGame.uniform_product (A := Secrets) (B := OtherHalves)).symm
theorem private_bind {Result : Type} (next : FullGame.FullTable → ProbComp Result) :
    𝒮[do let table ← ($ᵗ FullGame.FullTable : ProbComp _); next table] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        next (privateEquiv.symm (secrets, other))] := by
  have h := congrArg (fun law : SPMF (Secrets × OtherHalves) =>
    law >>= fun result => 𝒮[next (privateEquiv.symm result)]) uniform_private_split
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply] using h
theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (programmed U hU secrets labels residual)] := by
  rw [private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)]
  apply evalSPMF_bind_congr_left
  intro secrets
  apply evalSPMF_bind_congr_left
  intro other
  exact uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)
abbrev LowLabels := Node → Digest
/-- The nodes whose used half is the HIGH half of their output (`Pos.high`): on the paired tree's legacy (unpaired)
FTS positions the top FTS nodes (`wctNode` level 5, nested FTS r1-1; the paired forest's own halves are
`CanonGraph.Paired.highNode`), the left children of the lower trees (C2) and the last step of lower chain 0 (C3).
The name is historical. -/
def Node.isTop (N : Node) : Bool := N.toPos.high
theorem proj_toPos (N : Node) (y : HashOutput) :
    N.toPos.proj y = if N.isTop then y.extractLsb' 128 128 else y.extractLsb' 0 128 := by
  rw [Extract.Pos.proj_eq]; rfl
theorem high_chain (q : Point) : (Node.chain q).toPos.high = WCT9.chainHigh q.1.layer q.1.chain.val q.2.val := rfl
/-- C3: a point of an F chain (`isG = false`) below the last step uses the low half. -/
theorem proj_chain_of_lt {q : Point} (hG : WCT9.isG q.1.layer q.1.chain.val = false) (h : q.2.val < 6)
    (y : HashOutput) : (Node.chain q).toPos.proj y = y.extractLsb' 0 128 := by
  rw [Extract.Pos.proj_of_low (by rw [high_chain]; exact WCT9.chainHigh_eq_false_F hG (Or.inr (by omega)))]
theorem isTop_wctNode (n : WctNodePos) : (Node.wctNode n).isTop = decide (n.1.level.val = 5) := rfl
theorem isTop_wctLeaf (L : WctLeafPos) : (Node.wctLeaf L).isTop = false := rfl
theorem proj_toPos_of_not_top {N : Node} (h : N.isTop = false) (y : HashOutput) :
    N.toPos.proj y = y.extractLsb' 0 128 := by
  rw [proj_toPos, h]; rfl
/-- The two halves of an output, swapped. -/
noncomputable def swapOut : HashOutput ≃ HashOutput :=
  (ChainGraph.outputEquiv.trans (Equiv.prodComm _ _)).trans ChainGraph.outputEquiv.symm
theorem proj_top (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) (y : HashOutput) :
    (Node.wctNode (ftsTopNode index coord b)).toPos.proj y = y.extractLsb' 128 128 := by
  rw [proj_toPos]; rfl
theorem swapOut_low (y : HashOutput) : (swapOut y).extractLsb' 0 128 = y.extractLsb' 128 128 :=
  ChainGraph.joinOutput_low _ _
theorem swapOut_high (y : HashOutput) : (swapOut y).extractLsb' 128 128 = y.extractLsb' 0 128 :=
  ChainGraph.joinOutput_high _ _
/-- How node `N` stores its value: an output whose low half is the value, presented with the halves swapped for the
top FTS nodes, so that the value always sits in the half that `N.toPos.proj` reads. -/
noncomputable def presentEquiv (N : Node) : HashOutput ≃ HashOutput := if N.isTop then swapOut else Equiv.refl _
theorem proj_presentEquiv (N : Node) (y : HashOutput) : N.toPos.proj (presentEquiv N y) = y.extractLsb' 0 128 := by
  rw [proj_toPos]
  unfold presentEquiv
  cases N.isTop
  · rfl
  · exact swapOut_high y
/-- Witness stack: an FTS chain node reads the half `ftsChainHigh t step` (HIGH for G chains 1, 3 on steps < 3). -/
theorem proj_wctChain (p : WctPoint) (y : HashOutput) :
    (Node.wctChain p).toPos.proj y = projHalf (WCT9.ftsChainHigh p.1.2.2.2.val p.2.val) y := by
  simp only [Node.toPos, Extract.Pos.proj, Extract.Pos.high]
  cases WCT9.ftsChainHigh p.1.2.2.2.val p.2.val <;> rfl
/-- The used half of a presented FTS chain label is its stored low half. -/
theorem projHalf_presentEquiv_wctChain (p : WctPoint) (low high : Digest) :
    projHalf (WCT9.ftsChainHigh p.1.2.2.2.val p.2.val)
      (presentEquiv (Node.wctChain p) (ChainGraph.joinOutput low high)) = low := by
  rw [← proj_wctChain, proj_presentEquiv, ChainGraph.joinOutput_low]
noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  ((Equiv.piCongrRight fun N => (presentEquiv N).symm).trans
    (Equiv.arrowCongr (Equiv.refl Node) ChainGraph.outputEquiv)).trans
    (Equiv.arrowProdEquivProdArrow Node (fun _ => Digest) (fun _ => Digest))
/-- Labels from used halves `low` and other halves `high` (nested FTS r1-1: `low node` is the half that the node's
parents read, the high half for the top FTS nodes). -/
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => presentEquiv node (ChainGraph.joinOutput (low node) (high node))
theorem labelPairEquiv_symm (low high : LowLabels) : labelPairEquiv.symm (low, high) = joinLabels low high := rfl
theorem joinLabels_val (low high : LowLabels) (node : Node) :
    node.toPos.proj (joinLabels low high node) = low node :=
  (proj_presentEquiv node _).trans (ChainGraph.joinOutput_low _ _)
theorem joinLabels_low {low high : LowLabels} {node : Node} (h : node.isTop = false) :
    (joinLabels low high node).extractLsb' 0 128 = low node := by
  rw [← proj_toPos_of_not_top h]; exact joinLabels_val low high node
theorem joinLabels_not_top {low high : LowLabels} {node : Node} (h : node.isTop = false) :
    joinLabels low high node = ChainGraph.joinOutput (low node) (high node) := by
  unfold joinLabels presentEquiv; rw [h]; rfl
noncomputable local instance instSampleableTypeLowLabels : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdLowLabels : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _
theorem labels_bind {Result : Type} (next : Labels → ProbComp Result) :
    𝒮[do let labels ← ($ᵗ Labels : ProbComp _); next labels] =
      𝒮[do
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        next (joinLabels low high)] := by
  have hpair : 𝒮[labelPairEquiv <$> ($ᵗ Labels : ProbComp _)] =
      𝒮[do let low ← ($ᵗ LowLabels : ProbComp _); let high ← ($ᵗ LowLabels : ProbComp _); pure (low, high)] :=
    (evalSPMF_map_bijective_uniform_cross (α := Labels) (β := LowLabels × LowLabels)
      labelPairEquiv labelPairEquiv.bijective).trans (FullGame.uniform_product (A := LowLabels) (B := LowLabels)).symm
  have h := congrArg (fun law : SPMF (LowLabels × LowLabels) =>
    law >>= fun result => 𝒮[next (labelPairEquiv.symm result)]) hpair
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply, labelPairEquiv_symm] using h
end PrivateLaws
noncomputable def eagerAnswers (privateTable : FullGame.FullTable) (U : Finset HashInput)
    (publicTable : U → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => finiteHashAnswer ∅ U publicTable input
  | .inr coordinate => privateTable coordinate
def halfAnswer (answers : Answers) (c : ChainGraph.HalfCoordinate) : Digest :=
  if c.2.val = 0 then (answers (.inr c.1)).extractLsb' 0 128 else (answers (.inr c.1)).extractLsb' 128 128
def secretsOf (answers : Answers) : Secrets := fun idx => halfAnswer answers (secretCoordinate idx)
def wctSeedOf (answers : Answers) (a : WctAddr) : Digest := wctSeedsOf (secretsOf answers) a
def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ node, answers (.inl (.inr (cell (secretsOf answers) node labels))) = labels node
theorem secretsOf_eager (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput) :
    secretsOf (eagerAnswers privateTable U publicTable) = privateSecrets privateTable := rfl
theorem eagerAnswers_mem (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput)
    (x : U) : eagerAnswers privateTable U publicTable (.inl (.inr x.val)) = publicTable x :=
  finiteHashAnswer_none ∅ U publicTable x.val x.property rfl
theorem agrees_of_programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (answers : Answers)
    (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node
  have h := hpub (cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at] at h
  exact h
theorem eager_programmed_agrees (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (other : OtherHalves) (labels : Labels) (residual : U → HashOutput) :
    Agrees (eagerAnswers (privateEquiv.symm (secrets, other)) U (programmed U hU secrets labels residual)) labels := by
  apply agrees_of_programmed U hU _ labels residual
  intro x
  rw [secretsOf_eager, privateSecrets_symm, eagerAnswers_mem]
theorem agrees_chain {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    AgreesW answers (seedsOf (secretsOf answers)) (chainLabels labels) :=
  fun point => h (.chain point)
theorem halfAnswer_pair (answers : Answers) (tag lay tree position index : Nat) (i : Fin 2) :
    halfAnswer answers (.inl (header tag lay tree position index), i) =
      if i.val = 0 then (evalWithAnswerFn answers (privatePair tag lay tree position index)).1
      else (evalWithAnswerFn answers (privatePair tag lay tree position index)).2 := rfl
theorem secretsOf_coef (answers : Answers) (c : WctCoef) :
    secretsOf answers (.inr c) = WCT9.ftsCoef answers c.1.val c.2.1.val c.2.2 := by
  change halfAnswer answers (wctCoefCoordinate c) = _
  unfold wctCoefCoordinate WCT9.ftsCoef WCT9.seedHalf WCT9.ftsSeedHeader WCT9.ftsSeedPair
  rw [halfAnswer_pair, fullHalf_val]
theorem wctFamily_secretsOf (answers : Answers) (index : Fin (2 ^ 31)) (coord : Fin 9) :
    wctFamily (secretsOf answers) index coord = WCT9.ftsCoef answers index.val coord.val :=
  funext fun j => secretsOf_coef answers (index, coord, j)
theorem secretsOf_wct (answers : Answers) (a : WctAddr) :
    wctSeedsOf (secretsOf answers) a = WCT9.seed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2 := by
  unfold wctSeedsOf WCT9.seed
  rw [wctFamily_secretsOf]
/-- Coefficient `j` of family `f` as the signer reads it (`famCoefN lay tree leaf j = famCoefF lay tree (famOf leaf) j`). -/
def famCoefF (answers : Answers) (lay : Layer) (tree f j : Nat) : Digest :=
  WCT9.seedHalf (evalWithAnswerFn answers (WCT9.lowerSeedPair lay tree (famOrd lay f j / 2))) (famOrd lay f j)
theorem famCoefN_eq (answers : Answers) (lay : Layer) (tree leaf j : Nat) :
    WCT9.famCoefN answers lay tree leaf j = famCoefF answers lay tree (WCT9.famOf lay leaf) j := rfl
/-- A coefficient secret is the packed half the signer reads (stage B lower, T8D top). -/
theorem secretsOf_fam (answers : Answers) (a : Address) (hc : a.chain.val < WCT9.famSize a.layer a.leaf.val) :
    secretsOf answers (.inl a) = famCoefF answers a.layer a.tree.val a.leaf.val a.chain.val := by
  change halfAnswer answers (seedCoordinateP a) = _
  unfold seedCoordinateP famCoefF WCT9.seedHalf WCT9.lowerSeedHeader WCT9.lowerSeedPair
  rw [if_pos hc, halfAnswer_pair, fullHalf_val]
theorem leafFamily_secretsOf (answers : Answers) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096) :
    leafFamily (secretsOf answers) lay tree leaf = WCT9.famCoef answers lay tree.val leaf.val :=
  funext fun j => secretsOf_fam answers
    ⟨lay, tree, famSlot lay leaf, ⟨j.val, lt_trans j.isLt (WCT9.famSize_lt_58 lay _)⟩⟩ j.isLt
theorem seedsOf_secretsOf (answers : Answers) (a : Address) :
    seedsOf (secretsOf answers) a = WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val := by
  unfold seedsOf
  rw [leafFamily_secretsOf answers, WCT9.wotsSeed_fam]
end ClaudeWCT.W9.T3.Security.CanonGraph

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def first (coord : Nat) : Prop := coord<8 ∧ coord%2=0
instance (coord : Nat) : Decidable (first coord) := by unfold first;infer_instance
/-- Inverse of the fixed physical placement used by B and C trees. -/
def rawLeaf (coord physical : Nat) : Nat :=
  if first coord then physical else 2*(physical%64)+physical/64

def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level physical : Nat) : Digest :=
  if level=0 then
    if h:rawLeaf coord.val physical<128 then
      Extract.Paired.proj (.wctLeaf index.val coord.val (rawLeaf coord.val physical))
        (labels (.wctLeaf ⟨index,coord,⟨rawLeaf coord.val physical,h⟩⟩))
    else 0
  else
    match ftsNodeAt index coord (level-1) physical with
    | some n=>Extract.Paired.proj (.wctNode index.val coord.val (level-1) physical) (labels (.wctNode n))
    | none=>0

/-- A and C bind the preceding pair; B binds the selected A branch. -/
def pads (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) : Digest×Digest :=
  if h:coord.val=0 then (0,0) else
    let previous : Fin 9:=⟨coord.val-1,by have:=coord.isLt;omega⟩
    if coord.val%2=1 then
      (ftsLabel labels index previous 5 (2*branch),ftsLabel labels index previous 5 (2*branch+1))
    else (ftsLabel labels index previous 6 0,ftsLabel labels index previous 6 1)

def cell (secrets : Secrets) : Node→Labels→HashInput
  | .wctLeaf L,labels=>pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
      (pads labels L.index L.coord (L.child.val%2)).1
      (List.ofFn fun t:Fin 6=>wctEndLabel labels (L.index,L.coord,L.child,t)))
  | .wctNode n,labels=>pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2^(7-n.1.level.val-1)+n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val))
      (if n.1.level.val=4 then (pads labels n.1.index n.1.coord (n.1.idx.val/2)).2 else 0)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)))
  | node,labels=>CanonGraph.cell secrets node labels

theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.hdrBlock (cell secrets node labels)=bytesLE 16 node.toPos.hdr := by
  cases node with
  | wctLeaf L=>
    simp only [cell]
    rw [Extract.hdrBlock_wctLeafInputP]
    rfl
  | wctNode n=>
    simp only [cell]
    rw [Extract.hdrBlock_nodeInputP]
    rfl
  | chain v=>exact CanonGraph.hdrBlock_cell secrets (.chain v) labels hp
  | leaf v=>exact CanonGraph.hdrBlock_cell secrets (.leaf v) labels hp
  | node v=>exact CanonGraph.hdrBlock_cell secrets (.node v) labels hp
  | wctChain v=>exact CanonGraph.hdrBlock_cell secrets (.wctChain v) labels hp
  | forest v=>exact CanonGraph.hdrBlock_cell secrets (.forest v) labels hp

theorem cell_length (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    (cell secrets node labels).length=node.toPos.len := by
  cases node with
  | wctLeaf L=>
    simp only [cell,Extract.wctLeafInputP,Node.toPos,Extract.Pos.len]
    rw [Cost.pad64_length,Extract.listInput_length']
    simp only [List.length_cons,List.length_drop,List.length_ofFn]
  | wctNode n=>
    simp only [cell,Node.toPos,Extract.Pos.len]
    rw [pad64_nodeInputP,nodeInputP,block4]
    simp only [List.length_append,bytesLE_length]
  | chain v=>exact CanonGraph.cell_length secrets (.chain v) labels hp
  | leaf v=>exact CanonGraph.cell_length secrets (.leaf v) labels hp
  | node v=>exact CanonGraph.cell_length secrets (.node v) labels hp
  | wctChain v=>exact CanonGraph.cell_length secrets (.wctChain v) labels hp
  | forest v=>exact CanonGraph.cell_length secrets (.forest v) labels hp

/-- The Paired cell differs from the base cell only on FTS leaves and nodes (never phantoms). -/
theorem cell_node (secrets : Secrets) (n : TreeNode) (labels : Labels) :
    cell secrets (.node n) labels = CanonGraph.cell secrets (.node n) labels := rfl
theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  -- A tree node with the same cell: both are tree nodes (phantoms only collide with phantoms; a non-phantom
  -- tree-node cell decodes to a tree position). Reduce to the base separation there.
  by_cases hl : PhantomAt left before
  · obtain ⟨n, rfl, hn⟩ := cell_of_phantomAt (secrets := secrets) hl
    by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      exact CanonGraph.cell_separated secrets _ _ hne before after heq
    · have h1 := cell_length secrets right after hr
      rw [← heq, cell_node, hn, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
  · by_cases hr : PhantomAt right after
    · obtain ⟨m, rfl, hm⟩ := cell_of_phantomAt (secrets := secrets) hr
      have h1 := cell_length secrets left before hl
      rw [heq, cell_node, hm, phantom_length] at h1
      exact Pos.len_ne_192 _ h1.symm
    · have h1 := hdrBlock_cell secrets left before hl
      have h2 := hdrBlock_cell secrets right after hr
      have hlen : left.toPos.len = right.toPos.len := by
        rw [← cell_length secrets left before hl, ← cell_length secrets right after hr, heq]
      rw [heq] at h1
      have hpos := Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right) hlen
        (bytesLE_injective (h1.symm.trans h2))
      have hb := toPos_injective_base hpos
      cases left with
      | node n =>
          cases right with
          | node m => exact CanonGraph.cell_separated secrets _ _ hne before after heq
          | _ => simp [Node.base] at hb
      | _ =>
          cases right <;> first
            | exact hne hb
            | (simp [Node.base] at hb)

theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (h : ∀other:Node,other.depth<5+7*coord.val+level→left other=right other) :
    ftsLabel left index coord level c=ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [h _ (by simp only [Node.depth];omega)]
  · rfl
  all_goals
    cases hn:ftsNodeAt index coord (level-1) c with
    | none=>rfl
    | some n=>
      have hd:(Node.wctNode n).depth<5+7*coord.val+level := by
        show 5+7*n.1.coord.val+n.1.level.val<_
        rw [ftsNodeAt_level hn,ftsNodeAt_coord hn]
        omega
      simp only [h _ hd]

theorem pads_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat)
    (h : ∀other:Node,other.depth<4+7*coord.val→left other=right other) :
    pads left index coord branch=pads right index coord branch := by
  unfold pads
  split_ifs with hz hodd
  · rfl
  all_goals
    dsimp only
    apply Prod.ext
    all_goals dsimp only;apply ftsLabel_congr;intro other ho;apply h;dsimp at ho;omega

theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀other:Node,other.depth<node.depth→left other=right other) :
    cell secrets node left=cell secrets node right := by
  cases node with
  | wctLeaf L=>
    have hends : (List.ofFn fun t:Fin 6=>wctEndLabel left (L.index,L.coord,L.child,t))=
        (List.ofFn fun t:Fin 6=>wctEndLabel right (L.index,L.coord,L.child,t)) := by
      congr 1
      funext t
      unfold wctEndLabel
      rw [h _ (by show 3<4+7*L.coord.val;omega)]
    have hpad:=pads_congr left right L.index L.coord (L.child.val%2)
      (fun other ho=>h other ho)
    simp only [cell,hends,hpad]
  | wctNode n=>
    have hl:=ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)
      (fun other ho=>h other ho)
    have hr:=ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)
      (fun other ho=>h other ho)
    have hpad:=pads_congr left right n.1.index n.1.coord (n.1.idx.val/2)
      (fun other ho=>h other (by show other.depth<5+7*n.1.coord.val+n.1.level.val;omega))
    simp only [cell,hl,hr,hpad]
  | _=>exact CanonGraph.cell_congr secrets _ left right h

/-- Every paired cell has its position's honest length (length-aware decoding, C3). -/
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.posOf (cell secrets node labels)=some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (cell_length secrets node labels hp) (hdrBlock_cell secrets node labels hp)

theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input=some node.toPos) (h : input=cell secrets node' labels) :
    node'.toPos = node.toPos ∧ ¬ PhantomAt node' labels := by
  subst h
  by_cases hp : PhantomAt node' labels
  · obtain ⟨n, rfl, hc⟩ := cell_of_phantomAt (secrets := secrets) hp
    rw [cell_node, hc, posOf_phantom] at hpos; cases hpos
  · rw [posOf_cell secrets node' labels hp] at hpos
    exact ⟨Option.some.inj hpos, hp⟩

noncomputable def canonInputs : Finset HashInput := SeccLaw.publicUniverse
attribute [irreducible] canonInputs

theorem cell_length_le (secrets : Secrets) (node : Node) (labels : Labels) :
    (cell secrets node labels).length≤4096 := by
  cases node with
  | wctLeaf L=>
    simp only [cell,Extract.wctLeafInputP]
    rw [Cost.pad64_length,Extract.listInput_length']
    simp only [List.length_cons,List.length_drop,List.length_ofFn]
    omega
  | wctNode n=>
    simp only [cell]
    rw [pad64_nodeInputP,nodeInputP,block4]
    simp only [List.length_append,bytesLE_length]
    omega
  | chain v=>exact CanonGraph.cell_length_le secrets (.chain v) labels
  | leaf v=>exact CanonGraph.cell_length_le secrets (.leaf v) labels
  | node v=>exact CanonGraph.cell_length_le secrets (.node v) labels
  | wctChain v=>exact CanonGraph.cell_length_le secrets (.wctChain v) labels
  | forest v=>exact CanonGraph.cell_length_le secrets (.forest v) labels

theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels∈canonInputs := by
  rw [canonInputs]
  exact SeccLaw.mem_publicUniverse _ (cell_length_le secrets node labels)
theorem canonInputs_subset_publicUniverse : canonInputs⊆SeccLaw.publicUniverse := by
  rw [canonInputs]
noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩
theorem cellIn_separated (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) :
    Separated (cellIn U hU secrets) := by
  intro left right hne before after heq
  exact cell_separated secrets left right hne before after (congrArg Subtype.val heq)
theorem cellIn_injective (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) (labels : Labels) :
    Function.Injective (fun node => cellIn U hU secrets node labels) := by
  intro left right heq
  by_contra hne
  exact cellIn_separated U hU secrets left right hne labels labels heq
noncomputable def graph (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (table : U → HashOutput) : Labels :=
  read (cellIn U hU secrets) advance table order (fun _ => 0)
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order
section Laws
variable (U : Finset HashInput) (hU : canonInputs ⊆ U)
noncomputable local instance instSampleableTypeHashOutput_canonGraph : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem programmed_at (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (node : Node) :
    programmed U hU secrets labels residual (cellIn U hU secrets node labels) = labels node :=
  patch_at _ (cellIn_injective U hU secrets labels) labels residual order node (mem_order node)
theorem programmed_other (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, query.val ≠ cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node _ heq
  exact hquery node (congrArg Subtype.val heq)
theorem read_eq_plant (secrets : Secrets) (nodes : List Node) (hnodup : nodes.Nodup) (before : Labels) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (read (cellIn U hU secrets) advance table nodes before, table)] =
      𝒮[plant (cellIn U hU secrets) advance nodes before] :=
  evalDist_read_eq_plant (cellIn U hU secrets) advance (cellIn_separated U hU secrets) nodes hnodup before
theorem replay_eq_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) (hagrees : ∀ node, node ∉ nodes → before node = labels node) :
    replay (cellIn U hU secrets) advance labels residual nodes before =
      (labels, patch (fun node => cellIn U hU secrets node labels) labels residual nodes) := by
  induction nodes generalizing before with
  | nil =>
      have hbefore : before = labels := funext fun node => hagrees node (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cellIn U hU secrets first before = cellIn U hU secrets first labels := by
        apply Subtype.ext
        apply cell_congr
        intro other hother
        apply hagrees
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · rw [heq] at hother; omega
        · have := hdepth _ hmem; omega
      have hafter : ∀ node, node ∉ rest → advance first (labels first) before node = labels node := by
        intro node hnode
        unfold advance
        by_cases heq : node = first
        · subst node; rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees node (fun hmem => (List.mem_cons.mp hmem).elim heq hnode)
      rw [replay, ih hsorted _ hafter, patch, hinput]
theorem plant_eq_uniform_programmed (secrets : Secrets) :
    𝒮[plant (cellIn U hU secrets) advance order (fun _ => 0)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] := by
  rw [evalDist_plant_eq_replay _ _ _ order_nodup]
  apply evalSPMF_bind_congr_left
  intro labels
  apply evalSPMF_bind_congr_left
  intro residual
  rw [replay_eq_programmed U hU secrets labels residual order order_sorted _
    (fun node hnode => (hnode (mem_order node)).elim)]
  rfl
theorem graph_eq_uniform_programmed (secrets : Secrets) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (graph U hU secrets table, table)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] :=
  (read_eq_plant U hU secrets order order_nodup _).trans (plant_eq_uniform_programmed U hU secrets)
theorem graph_bind_eq_uniform_programmed {Result : Type} (secrets : Secrets)
    (next : Labels → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (graph U hU secrets table) table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next labels (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
    law >>= fun result => 𝒮[next result.1 result.2]) (graph_eq_uniform_programmed U hU secrets)
  simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
theorem uniform_bind_programmed {Result : Type} (secrets : Secrets) (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] :=
  graph_bind_eq_uniform_programmed U hU secrets (fun _ table => next table)
end Laws
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def Used : Node → Prop
  | .forest _ => False
  | .wctNode n => first n.1.coord.val → n.1.level.val < 5
  | _ => True
instance (n : Node) : Decidable (Used n) := by unfold Used; cases n <;> infer_instance

theorem used_iff_bounded (n : Node) : Used n ↔ Extract.Paired.Bounded n.toPos := by
  cases n with
  | forest i => rfl
  | wctNode n =>
      simp only [Used, Node.toPos, Extract.Paired.Bounded, Extract.Paired.first,
        decide_eq_true_eq]
      exact ⟨fun h => ⟨toPos_bounded (.wctNode n), h⟩, fun h => h.2⟩
  | chain p =>
      change True ↔ (Node.chain p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | leaf p =>
      change True ↔ (Node.leaf p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | node p =>
      change True ↔ (Node.node p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | wctChain p =>
      change True ↔ (Node.wctChain p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | wctLeaf p =>
      change True ↔ (Node.wctLeaf p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩

theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, Used other → other.depth < levelDepth lay level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L => simp only; rw [h (.leaf L) trivial (by simp only [Node.depth, levelDepth]; omega)]
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        have hl := treeNodeAt_level hn
        have hlay := treeNodeAt_lay hn
        rw [selNode_label_congr (fun j hj => h _ trivial (by
          have := depth_withNonce_lt n hj (level := level) (by omega)
          rw [hlay] at this; exact this))]

theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : first coord.val → level ≤ 5)
    (h : ∀ other : Node, Used other → other.depth < 5 + 7 * coord.val + level → left other = right other) :
    Paired.ftsLabel left index coord level c = Paired.ftsLabel right index coord level c := by
  unfold Paired.ftsLabel
  split_ifs with hzero hc
  · rw [h (.wctLeaf ⟨index,coord,⟨rawLeaf coord.val c,hc⟩⟩) trivial (by simp only [Node.depth]; omega)]
  · rfl
  all_goals
    cases hn : ftsNodeAt index coord (level-1) c with
    | none => rfl
    | some n =>
      have hu : Used (.wctNode n) := by
        change first n.1.coord.val → n.1.level.val < 5
        rw [ftsNodeAt_level hn, ftsNodeAt_coord hn]
        intro hf
        have := hl hf
        omega
      have hd : (Node.wctNode n).depth < 5+7*coord.val+level := by
        simp only [Node.depth]
        rw [ftsNodeAt_level hn,ftsNodeAt_coord hn]
        omega
      simp only [h _ hu hd]

theorem pads_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat)
    (h : ∀other : Node, Used other → other.depth<4+7*coord.val → left other=right other) :
    Paired.pads left index coord branch = Paired.pads right index coord branch := by
  unfold Paired.pads
  split_ifs with hz hodd
  · rfl
  · dsimp only
    apply Prod.ext
    all_goals
      dsimp only
      apply ftsLabel_congr
      · intro _; omega
      · intro other hu ho; apply h other hu; dsimp at ho; omega
  · dsimp only
    apply Prod.ext
    all_goals
      dsimp only
      apply ftsLabel_congr
      · intro hf
        unfold first at hf
        dsimp only at hf
        omega
      · intro other hu ho; apply h other hu; dsimp at ho; omega

theorem cell_congr_nonforest (secrets : Secrets) (node : Node)
    (hnf : ∀i, node≠.forest i) (left right : Labels)
    (h : ∀ other : Node, Used other → other.depth < node.depth → left other = right other) :
    Paired.cell secrets node left = Paired.cell secrets node right := by
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels left) =
        inputW (seedsOf secrets) p (chainLabels right)
      unfold inputW priorW
      split_ifs with hz
      · rfl
      · have hd := h (.chain (ChainGraph.predecessor p)) trivial (by
          simp only [Node.depth, ChainGraph.predecessor]; omega)
        simp only [chainLabels, hd]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets left L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets right L.1) := by
        apply List.map_congr_left
        intro i _
        -- C3 (#866): a leaf reads the used half of its chains' last-step labels (`endLabel` via `endPt`).
        unfold endLabel
        rw [h (.chain _) trivial (by simp only [Node.depth, endPt]; exact Nat.mod_lt _ (by decide))]
      simp only [Paired.cell, CanonGraph.cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val)
        (fun other ho hd => h other ho (by rw [depth_node]; omega))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val+1)
        (fun other ho hd => h other ho (by rw [depth_node]; omega))
      have ha : Active left n ↔ Active right n :=
        activeCongr left right n (fun j hj => h _ trivial (depth_trial_lt n hj))
      simp only [Paired.cell, CanonGraph.cell, hl, hr, ha]
  | wctChain p =>
      have hv : wctValueL secrets left p.1 p.2.val = wctValueL secrets right p.1 p.2.val := by
        unfold wctValueL
        split_ifs with hz
        · rfl
        · rw [h (.wctChain (p.1,⟨(p.2.val-1)%4,Nat.mod_lt _ (by decide)⟩)) trivial (by simp only [Node.depth]; have := p.2.isLt; omega)]
      simp only [Paired.cell, CanonGraph.cell, hv]
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel left (L.index,L.coord,L.child,t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel right (L.index,L.coord,L.child,t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [h (.wctChain ((L.index,L.coord,L.child,t),3)) trivial (by show 3<4+7*L.coord.val; omega)]
      have hpad := pads_congr left right L.index L.coord (L.child.val%2)
        (fun other ho hd => h other ho hd)
      simp only [Paired.cell,hends,hpad]
  | wctNode n =>
      have hh : first n.1.coord.val → n.1.level.val ≤ 5 := fun _ => Nat.le_of_lt_succ n.1.level.isLt
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val) hh
        (fun other ho hd => h other ho hd)
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1) hh
        (fun other ho hd => h other ho hd)
      have hpad := pads_congr left right n.1.index n.1.coord (n.1.idx.val/2)
        (fun other ho hd => h other ho (by change other.depth<5+7*n.1.coord.val+n.1.level.val; omega))
      simp only [Paired.cell,hl,hr,hpad]
  | forest i => exact (hnf i rfl).elim

theorem cell_congr (secrets : Secrets) (node : Node) (hu : Used node) (left right : Labels)
    (h : ∀ other : Node, Used other → other.depth < node.depth → left other = right other) :
    Paired.cell secrets node left = Paired.cell secrets node right := by
  apply cell_congr_nonforest secrets node _ left right h
  intro i hi
  subst node
  exact hu

end ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def order : List Node := CanonGraph.order.filter (fun n => decide (Used n))
theorem mem_order (n : Node) : n ∈ order ↔ Used n := by
  simp only [order, List.mem_filter, CanonGraph.mem_order, true_and, decide_eq_true_eq]
theorem order_nodup : order.Nodup := CanonGraph.order_nodup.filter _
theorem order_sorted : order.Pairwise (fun left right => left.depth ≤ right.depth) :=
  CanonGraph.order_sorted.filter _

noncomputable def programmed (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => Paired.cellIn U hU secrets node labels) labels residual order

theorem programmed_at (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) (node : Node) (hu : Used node) :
    programmed U hU secrets labels residual (Paired.cellIn U hU secrets node labels) = labels node :=
  patch_at _ (Paired.cellIn_injective U hU secrets labels) labels residual order node ((mem_order node).2 hu)

theorem programmed_other (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, Used node → query.val ≠ Paired.cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node hn heq
  exact hquery node ((mem_order node).1 hn) (congrArg Subtype.val heq)

theorem replay_snd (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
    (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (hused : ∀node∈nodes, Used node)
    (before : Labels) (hagrees : ∀node, Used node → node∉nodes → before node=labels node) :
    (replay (Paired.cellIn U hU secrets) advance labels residual nodes before).2 =
      patch (fun node => Paired.cellIn U hU secrets node labels) labels residual nodes := by
  induction nodes generalizing before with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨hdepth,hsorted⟩ := List.pairwise_cons.mp hsorted
    have hinput : Paired.cellIn U hU secrets first before = Paired.cellIn U hU secrets first labels := by
      apply Subtype.ext
      apply cell_congr secrets first (hused first (by simp))
      intro other hu ho
      apply hagrees other hu
      intro hmem
      rcases List.mem_cons.mp hmem with heq|hmem
      · rw [heq] at ho; omega
      · have := hdepth _ hmem; omega
    have hafter : ∀node, Used node → node∉rest → advance first (labels first) before node=labels node := by
      intro node hu hn
      unfold advance
      by_cases heq : node=first
      · subst node; rw [Function.update_self]
      · rw [Function.update_of_ne heq]
        exact hagrees node hu (fun hm => (List.mem_cons.mp hm).elim heq hn)
    simp only [replay, patch]
    rw [ih hsorted (fun node hn => hused node (List.mem_cons_of_mem _ hn)) _ hafter, hinput]

section Laws
variable (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem plant_bind_programmed {Result : Type} (secrets : Secrets)
    (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let result ← plant (Paired.cellIn U hU secrets) advance order (fun _ => 0); next result.2] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] := by
  rw [evalSPMF_bind, evalDist_plant_eq_replay _ _ _ order_nodup]
  simp only [evalSPMF_bind, bind_assoc, evalSPMF_pure, pure_bind]
  apply bind_congr
  intro labels
  apply bind_congr
  intro residual
  rw [replay_snd U hU secrets labels residual order order_sorted
    (fun node hn => (mem_order node).1 hn) _
    (fun node hu hn => (hn ((mem_order node).2 hu)).elim)]
  rfl

theorem uniform_bind_programmed {Result : Type} (secrets : Secrets)
    (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
      law >>= fun result => 𝒮[next result.2])
    (Paired.read_eq_plant U hU secrets order order_nodup (fun _ => 0))
  have h' : 𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do let result ← plant (Paired.cellIn U hU secrets) advance order (fun _ => 0); next result.2] := by
    simpa only [evalSPMF_bind,evalSPMF_pure,bind_assoc,pure_bind] using h
  exact h'.trans (plant_bind_programmed U hU secrets next)
end Laws

def Agrees (answers : Correctness.Answers) (labels : Labels) : Prop :=
  ∀node, Used node → answers (.inl (.inr (Paired.cell (secretsOf answers) node labels)))=labels node

theorem agrees_of_programmed (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
    (answers : Correctness.Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀x : U, answers (.inl (.inr x.val))=programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node hu
  have h := hpub (Paired.cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at _ _ _ _ _ _ hu] at h
  exact h
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SphincsSecurity.Concrete
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- C1: the nodes whose label is presented through the high output half: the top folds of
`highPosition`, the singleton's left top node (stage 2, `singletonHigh`), the even nodes of levels `0..2` and the
leaves of even physical children; on the lower trees the #866 rule (C2: left children, C3: the last step of lower chain
0; `Extract.Pos.high`). -/
def highNode : Node → Bool
  | .wctNode n => decide (Extract.Paired.highNodeAt n.1.coord.val n.1.level.val n.1.idx.val)
  | .wctLeaf L => decide (Extract.Paired.highLeafAt L.coord.val L.child.val)
  | .chain p => (Node.chain p).toPos.high
  | .leaf L => (Node.leaf L).toPos.high
  | .node n => (Node.node n).toPos.high
  | .wctChain p => (Node.wctChain p).toPos.high
  | .forest _ => false

theorem proj_toPos (N : Node) (y : HashOutput) :
    Extract.Paired.proj N.toPos y = if highNode N then y.extractLsb' 128 128 else y.extractLsb' 0 128 := by
  cases N with
  | wctNode n =>
      simp only [Node.toPos,highNode,Extract.Paired.proj,decide_eq_true_eq,ite_apply]
  | wctLeaf L =>
      simp only [Node.toPos,highNode,Extract.Paired.proj,decide_eq_true_eq,ite_apply]
  | chain p => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | leaf L => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | node n => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | wctChain p => simp only [Node.toPos,highNode,Extract.Paired.proj,Extract.Pos.high,ite_apply] <;> rfl
  | forest i => rfl

/-- C2/C3: on the lower trees the paired projection is the legacy (#866) `Pos.proj`. -/
theorem pairedProj_chain (p : ChainGraph.Point) : Extract.Paired.proj (Node.chain p).toPos = (Node.chain p).toPos.proj :=
  Extract.Paired.proj_chain _ _ _ _ _
theorem pairedProj_leaf (L : SrcLeaf) : Extract.Paired.proj (Node.leaf L).toPos = (Node.leaf L).toPos.proj :=
  Extract.Paired.proj_leaf _ _ _
theorem pairedProj_node (n : TreeNode) : Extract.Paired.proj (Node.node n).toPos = (Node.node n).toPos.proj :=
  Extract.Paired.proj_node _ _ _ _

noncomputable def presentEquiv (N : Node) : HashOutput ≃ HashOutput :=
  if highNode N then CanonGraph.swapOut else Equiv.refl _

theorem proj_presentEquiv (N : Node) (y : HashOutput) :
    Extract.Paired.proj N.toPos (presentEquiv N y)=y.extractLsb' 0 128 := by
  rw [proj_toPos]
  unfold presentEquiv
  cases highNode N
  · rfl
  · exact CanonGraph.swapOut_high y

noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  ((Equiv.piCongrRight fun N => (presentEquiv N).symm).trans
    (Equiv.arrowCongr (Equiv.refl Node) ChainGraph.outputEquiv)).trans
    (Equiv.arrowProdEquivProdArrow Node (fun _ => Digest) (fun _ => Digest))

noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => presentEquiv node (ChainGraph.joinOutput (low node) (high node))

theorem labelPairEquiv_symm (low high : LowLabels) : labelPairEquiv.symm (low,high)=joinLabels low high := rfl

theorem joinLabels_val (low high : LowLabels) (node : Node) :
    Extract.Paired.proj node.toPos (joinLabels low high node)=low node :=
  (proj_presentEquiv node _).trans (ChainGraph.joinOutput_low _ _)

/-- C2/C3: the used half (`Pos.proj`) of a lower-tree label is its low label (the paired form of the legacy
`CanonGraph.joinLabels_val`, used where `CanonGraph.treeLabel`/`endLabel` read a label through `Pos.proj`). -/
theorem joinLabels_node (low high : LowLabels) (n : TreeNode) :
    (Node.node n).toPos.proj (joinLabels low high (.node n))=low (.node n) := by
  rw [←pairedProj_node]; exact joinLabels_val low high (.node n)
theorem joinLabels_leaf (low high : LowLabels) (L : SrcLeaf) :
    (Node.leaf L).toPos.proj (joinLabels low high (.leaf L))=low (.leaf L) := by
  rw [←pairedProj_leaf]; exact joinLabels_val low high (.leaf L)
theorem joinLabels_chain (low high : LowLabels) (p : ChainGraph.Point) :
    (Node.chain p).toPos.proj (joinLabels low high (.chain p))=low (.chain p) := by
  rw [←pairedProj_chain]; exact joinLabels_val low high (.chain p)

theorem joinLabels_not_high {low high : LowLabels} {node : Node} (h : highNode node=false) :
    joinLabels low high node=ChainGraph.joinOutput (low node) (high node) := by
  unfold joinLabels presentEquiv
  rw [h]
  rfl

theorem joinLabels_low {low high : LowLabels} {node : Node} (h : highNode node=false) :
    (joinLabels low high node).extractLsb' 0 128=low node := by
  rw [joinLabels_not_high h]
  exact ChainGraph.joinOutput_low _ _

section Laws
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _

theorem labels_bind {Result : Type} (next : Labels → ProbComp Result) :
    𝒮[do let labels ← ($ᵗ Labels : ProbComp _); next labels] =
      𝒮[do
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        next (joinLabels low high)] := by
  have hpair : 𝒮[labelPairEquiv <$> ($ᵗ Labels : ProbComp _)] =
      𝒮[do let low ← ($ᵗ LowLabels : ProbComp _); let high ← ($ᵗ LowLabels : ProbComp _); pure (low,high)] :=
    (evalSPMF_map_bijective_uniform_cross (α := Labels) (β := LowLabels × LowLabels)
      labelPairEquiv labelPairEquiv.bijective).trans (FullGame.uniform_product (A := LowLabels) (B := LowLabels)).symm
  have h := congrArg (fun law : SPMF (LowLabels × LowLabels) =>
    law >>= fun result => 𝒮[next (labelPairEquiv.symm result)]) hpair
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply,labelPairEquiv_symm] using h
end Laws
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_TopTrial ====
section

/-! # Top-nonce layer: the honest nonce search agrees with the trial graph (r3-lean-nonsec)

Under agreement on tree nodes, the keygen nonce search of a top position returns the selected trial `selNonce`, and
the honest tree value of a position is the used half of its selected trial's label (`tree_step`). Every trial up to
the selected one is active, so its cell is the honest trial input. -/
namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem trialFails_withNonce (labels : Labels) (n : TreeNode) (k j : Nat) :
    trialFails labels (withNonce n k) j ↔ trialFails labels n j := Iff.rfl

theorem selNonce_spec (labels : Labels) (n : TreeNode) :
    (∀ j < selNonce labels n, trialFails labels n j) ∧
      (¬ trialFails labels n (selNonce labels n) ∨
        selNonce labels n = trialCap n.1.lay n.1.level.val - 1) := by
  unfold selNonce
  cases hf : (List.range (trialCap n.1.lay n.1.level.val)).find? (fun j => !decide (trialFails labels n j)) with
  | none =>
      have hall : ∀ i, i < trialCap n.1.lay n.1.level.val → trialFails labels n i := by
        intro i hi
        have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
        simpa using this
      have hpos := trialCap_pos n.1.lay n.1.level.val
      refine ⟨fun j hj => hall j ?_, Or.inr rfl⟩
      simp only [Option.getD_none] at hj
      omega
  | some i =>
      rw [List.find?_range_eq_some] at hf
      obtain ⟨hp, -, hlt⟩ := hf
      simp only [Option.getD_some]
      exact ⟨fun j hj => by simpa using hlt j hj, Or.inl (by simpa using hp)⟩

/-- Every trial up to the selected one is active. -/
theorem active_trial_of_le {labels : Labels} {n : TreeNode} {k : Nat} (hk : k ≤ selNonce labels n) :
    Active labels (withNonce n k) := by
  have hs := selNonce_lt labels n
  have hc := trialCap_le n.1.lay n.1.level.val
  refine ⟨?_, fun j hj => ?_⟩
  · rw [withNonce_nonce n (by omega)]; exact lt_of_le_of_lt hk hs
  · rw [withNonce_nonce n (by omega)] at hj
    exact (trialFails_withNonce labels n k j).2 ((selNonce_spec labels n).1 j (by omega))

/-- The nonce search returns the first passing trial `s` (or the last one) once its values are known up to `s`. -/
theorem eval_topNonceSearch_eq (answers : Answers) (h heap : Nat) (left right : Digest) (v : Nat → Digest)
    (hv : ∀ k, evalWithAnswerFn answers (topNodeHashN heap k left right) = v k) :
    ∀ fuel n s, n ≤ s → s ≤ n + fuel → (∀ k, n ≤ k → k < s → topZeroOk h (v k) = false) →
      (topZeroOk h (v s) = true ∨ s = n + fuel) →
      evalWithAnswerFn answers (topNonceSearch h heap left right fuel n) = (s, v s) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n s h1 h2 _ _
      have : s = n := by omega
      subst this
      simp only [topNonceSearch, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hv]
  | succ fuel ih =>
      intro n s h1 h2 hfail hend
      simp only [topNonceSearch, evalWithAnswerFn_bind, hv]
      by_cases hs : s = n
      · subst hs
        have hok : topZeroOk h (v s) = true := by
          rcases hend with h' | h'
          · exact h'
          · omega
        rw [if_pos hok, evalWithAnswerFn_pure]
      · have hf : topZeroOk h (v n) = false := hfail n le_rfl (by omega)
        rw [if_neg (by rw [hf]; decide)]
        exact ih (n + 1) s (by omega) (by omega) (fun k hk1 hk2 => hfail k (by omega) hk2)
          (by rcases hend with h' | h'
              · exact Or.inl h'
              · right; omega)

/-- Agreement on tree nodes (implied by `Agrees`, `Paired.Agrees` and `Filtered.Agrees`). -/
def NodeAgrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ m : TreeNode, answers (.inl (.inr (cell (secretsOf answers) (.node m) labels))) = labels (.node m)

theorem proj_node_eq (n : TreeNode) (o : HashOutput) :
    (Node.node n).toPos.proj o =
      WCT9.halfOf (WCT9.lowerHigh n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)) o := by
  rfl

/-- One level of the honest tree under node agreement: the honest nonce is the selected trial, and the honest
value is the used half of the selected trial's label. -/
theorem tree_step {answers : Answers} {labels : Labels} (hag : NodeAgrees answers labels)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (n : TreeNode)
    (hn : treeNodeAt lay tree level c = some n)
    (hl : treeValue (WCT9.wotsTree answers lay tree.val) level (2 * c) = treeLabel labels lay tree level (2 * c))
    (hr : treeValue (WCT9.wotsTree answers lay tree.val) level (2 * c + 1) =
      treeLabel labels lay tree level (2 * c + 1)) :
    WCT9.honestNonce answers lay tree.val level c = selNonce labels n ∧
      treeValue (WCT9.wotsTree answers lay tree.val) (level + 1) c =
        (Node.node n).toPos.proj (labels (.node (selNode labels n))) := by
  have hlay := treeNodeAt_lay hn
  have hlev := treeNodeAt_level hn
  have hnon := treeNodeAt_nonce hn
  have hv : level < height lay ∧ c < 2 ^ (height lay - level - 1) := by
    unfold treeNodeAt at hn
    split_ifs at hn with hv
    exact ⟨hv.1, hv.2.1⟩
  have hidx : n.1.idx.val = c := by
    unfold treeNodeAt at hn
    split_ifs at hn with hv
    cases hn
    rfl
  have htree : n.1.tree = tree := by
    unfold treeNodeAt at hn
    split_ifs at hn with hv
    cases hn
    rfl
  set heap := 2 ^ (height lay - level - 1) + c with hheap
  set L := treeLabel labels lay tree level (2 * c)
  set R := treeLabel labels lay tree level (2 * c + 1)
  -- Trial values: for `k ≤ sel`, the honest trial hash is the used half of trial `k`'s label.
  have htrial : ∀ k ≤ selNonce labels n,
      evalWithAnswerFn answers (WCT9.halfHash (WCT9.lowerHigh lay.val heap)
        (WCT9.merkleNodeInputN lay.val tree.val heap k L R)) =
        (Node.node n).toPos.proj (labels (.node (withNonce n k))) := by
    intro k hk
    have hcap := trialCap_le n.1.lay n.1.level.val
    have hks := selNonce_lt labels n
    have ha := active_trial_of_le hk
    have hcell := cell_node_active (secrets := secretsOf answers) ha
    rw [withNonce_nonce n (by omega)] at hcell
    simp only [withNonce_lay, withNonce_tree, withNonce_level, withNonce_idx] at hcell
    rw [hlay, hlev, hidx, htree] at hcell
    rw [Wots.eval_halfHash', ← hcell, hag, proj_node_eq, hlay, hlev, hidx]
  have hsel : WCT9.honestNonce answers lay tree.val level c = selNonce labels n := by
    by_cases htop : lay = 0 ∧ level < 11
    · obtain ⟨h0, h11⟩ := htop
      have hcapeq : trialCap n.1.lay n.1.level.val = topNonceCap (level + 1) := by
        unfold trialCap; rw [hlay, hlev, if_pos ⟨h0, h11⟩]
      unfold WCT9.honestNonce
      rw [if_pos ⟨h0, h11⟩, hl, hr]
      unfold topNodeAt
      have hspec := selNonce_spec labels n
      have hslt := selNonce_lt labels n
      rw [hcapeq] at hspec hslt
      have hpos : 0 < topNonceCap (level + 1) := by unfold topNonceCap; positivity
      -- the search values below `sel` are the trial labels
      have hvals : ∀ k ≤ selNonce labels n, evalWithAnswerFn answers (topNodeHashN heap k L R) =
          (Node.node n).toPos.proj (labels (.node (withNonce n k))) := by
        intro k hk
        rw [← htrial k hk]
        subst h0
        unfold topNodeHashN
        rw [← WCT9.merkleNodeInputN_top tree.val heap k L R, ← WCT9.lowerHigh_top_eq_nodeHalfHigh,
          WCT9.halfHash_eq_projHash]
        rfl
      have hres := eval_topNonceSearch_eq answers (level + 1) heap L R
        (fun k => evalWithAnswerFn answers (topNodeHashN heap k L R)) (fun _ => rfl)
        (topNonceCap (level + 1) - 1) 0 (selNonce labels n) (Nat.zero_le _) (by omega)
        (fun k _ hk => by
          rw [hvals k (by omega)]
          have := hspec.1 k hk
          unfold trialFails at this
          rw [hlev] at this
          exact this)
        (by
          rcases hspec.2 with h' | h'
          · left
            rw [hvals _ le_rfl]
            unfold trialFails at h'
            rw [hlev] at h'
            simpa using h'
          · right; omega)
      exact congrArg Prod.fst hres
    · have hcap1 : trialCap n.1.lay n.1.level.val = 1 := by
        unfold trialCap; rw [hlay, hlev, if_neg htop]
      rw [selNonce_of_cap_one hcap1]
      unfold WCT9.honestNonce
      rw [if_neg htop]
  refine ⟨hsel, ?_⟩
  rw [WCT9.wotsTree_node_any answers lay tree.val level c hv.1 hv.2, hsel, hl, hr]
  exact htrial _ le_rfl

/-- The selected representative of a node's position (tree nodes: the selected trial; others: the node). -/
def Node.sel (labels : Labels) : Node → Node
  | .chain p => .chain p
  | .leaf L => .leaf L
  | .node n => .node (selNode labels n)
  | .wctChain p => .wctChain p
  | .wctLeaf L => .wctLeaf L
  | .wctNode n => .wctNode n
  | .forest i => .forest i
theorem toPos_sel (labels : Labels) (node : Node) : (node.sel labels).toPos = node.toPos := by
  cases node <;> rfl

theorem treeNodeAt_of_node (n : TreeNode) :
    treeNodeAt n.1.lay n.1.tree n.1.level.val n.1.idx.val = some (withNonce n 0) := by
  have hv : n.1.level.val < height n.1.lay ∧ n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) ∧
      n.1.tree.val < 2 ^ treeBits n.1.lay ∧ (n.1.lay = 0 ∨ n.1.level.val + 1 < height n.1.lay) := n.2
  unfold treeNodeAt
  rw [dif_pos hv]
  rfl

theorem selNonce_withNonce (labels : Labels) (n : TreeNode) (k : Nat) :
    selNonce labels (withNonce n k) = selNonce labels n := rfl

/-- The honest input of a tree position is the cell of its selected trial (given the children). -/
theorem honestInput_node_sel {answers : Answers} {labels : Labels} (hag : NodeAgrees answers labels) (n : TreeNode)
    (hl : treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val) =
      treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
    (hr : treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val + 1) =
      treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)) :
    Extract.honestInput answers (Node.node n).toPos =
      cell (secretsOf answers) (.node (selNode labels n)) labels := by
  obtain ⟨hsel, -⟩ := tree_step hag n.1.lay n.1.tree n.1.level.val n.1.idx.val (withNonce n 0)
    (treeNodeAt_of_node n) hl hr
  rw [selNonce_withNonce] at hsel
  have ha : Active labels (withNonce n (selNonce labels n)) := active_trial_of_le le_rfl
  have hs := selNonce_lt labels n
  have hc := trialCap_le n.1.lay n.1.level.val
  rw [show selNode labels n = withNonce n (selNonce labels n) from rfl, cell_node_active ha,
    withNonce_nonce n (by omega)]
  simp only [withNonce_lay, withNonce_tree, withNonce_level, withNonce_idx]
  change pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
    (WCT9.honestNonce answers n.1.lay n.1.tree.val n.1.level.val n.1.idx.val)
    (treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val))
    (treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val + 1))) = _
  rw [hsel, hl, hr]

end ClaudeWCT.W9.T3.Security.CanonGraph
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_CanonGraphHonest ====
section

namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree ClaudeWCT.WCT9.heapBuild
theorem wctSeed_eq (answers : Answers) (a : WctAddr) :
    Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = wctSeedOf answers a := by
  unfold wctSeedOf
  rw [secretsOf_wct]
  rfl
theorem wctSeed_secrets (answers : Answers) (a : WctAddr) :
    Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = wctSeedsOf (secretsOf answers) a :=
  wctSeed_eq answers a
section Honest
variable {answers : Answers} {labels : Labels}
/-- Pairing stage 1: the honest chain of the current scheme (`WCT9.chainW`, G chains on the high half) after `step`
steps is the label value `valueW`. -/
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    Wots.honestChainValueW answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      valueW (seedsOf (secretsOf answers)) (chainLabels labels) a step := by
  have hx := sourceW_chain answers (seedsOf (secretsOf answers)) (chainLabels labels) (agrees_chain h) a 0
    step (by omega)
  rw [valueW_zero, seedsOf_secretsOf, Nat.zero_add] at hx
  exact hx
theorem maxDigit_le_seven (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> decide
/-- C3: the honest chain of the current scheme after `m + 1` steps is the used half (`Pos.proj`: the high half for
the last step of a lower chain 0) of step `m`'s label. -/
theorem chainValueW_succ (h : Agrees answers labels) (a : Address) (m : Fin 7) :
    Wots.honestChainValueW answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) (m.val + 1) =
      (Node.chain (a, m)).toPos.proj (labels (.chain (a, m))) := by
  have hm := m.isLt
  rw [← Wots.honestChainValueW_succ, chainValue_eq h a m.val (by omega)]
  have hrow : pad64 (WCT9.chainInputW a.layer a.tree.val a.leaf.val a.chain.val m.val
      (valueW (seedsOf (secretsOf answers)) (chainLabels labels) a m.val)) =
      cell (secretsOf answers) (.chain (a, m)) labels := by
    simp only [cell]
    rw [inputW, priorW_eq_valueW]
    exact WCT9.chainInputW_padded _ _ _ _ _ _
  have hp : (Node.chain (a, m)).toPos.proj = WCT9.halfOf (WCT9.chainHigh a.layer a.chain.val m.val) := rfl
  rw [hp, hrow, h (.chain (a, m))]
/-- C3: a revealed chain value is the seed (digit 0) or the used half of the label of the step before it. -/
theorem leafValue_eq (h : Agrees answers labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hdigit : digits.getD i 0 ≤ 7) :
    WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      if digits.getD i 0 = 0 then seedsOf (secretsOf answers) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
      else (Node.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(digits.getD i 0 - 1) % 7, Nat.mod_lt _ (by decide)⟩)).toPos.proj
        (labels (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(digits.getD i 0 - 1) % 7, Nat.mod_lt _ (by decide)⟩))) := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have he : WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
        (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val) (digits.getD i 0) := by
    unfold WCT9.wotsValue Wots.honestChainValueW; rw [hval]
  rw [he]
  split_ifs with h0
  · rw [h0, Wots.honestChainValueW_zero, seedsOf_secretsOf]
  · obtain ⟨m, hm⟩ : ∃ m, digits.getD i 0 = m + 1 := ⟨digits.getD i 0 - 1, by omega⟩
    have hmod : (digits.getD i 0 - 1) % 7 = m := by rw [hm]; exact Nat.mod_eq_of_lt (by omega)
    have hx := chainValueW_succ h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ ⟨m, by omega⟩
    simp only [hmod]
    exact (congrArg (Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
      (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val)) hm).trans hx
/-- C3: a chain end is the used half (`Pos.proj`, the high half for lower chain 0) of its last step's label. -/
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (i : Nat) (hi : i < 58) :
    WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hm1 : 1 ≤ maxDigit L.lay i := by unfold maxDigit; split_ifs <;> decide
  have hm7 := maxDigit_le_seven L.lay i
  obtain ⟨m, hm⟩ : ∃ m, maxDigit L.lay i = m + 1 := ⟨maxDigit L.lay i - 1, by omega⟩
  have hmod : (maxDigit L.lay i - 1) % 7 = m := by rw [hm]; exact Nat.mod_eq_of_lt (by omega)
  have he : WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i =
      Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
        (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val) (maxDigit L.lay i) := by
    unfold WCT9.wotsEnd Wots.honestChainValueW; rw [hval]
  have hx := chainValueW_succ h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ ⟨m, by omega⟩
  rw [he, hm, hx]
  unfold endLabel endPt
  simp only [hmod]
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) :
    (List.range (chainCount L.lay)).map (WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
/-- C2: a leaf value is the used half (`Pos.proj`) of its leaf label. -/
theorem leafRoot_eq (h : Agrees answers labels) (L : SrcLeaf) :
    WCT9.wotsRoot answers L.1.lay L.1.tree.val L.1.leaf.val = (Node.leaf L).toPos.proj (labels (.leaf L)) := by
  unfold WCT9.wotsRoot
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  rw [Wots.eval_halfHash', leafEnds_eq h L.1]
  exact congrArg (WCT9.halfOf (WCT9.lowerHigh L.1.lay.val L.1.leaf.val)) (h (.leaf L))
theorem treeNodeAt_some (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hlevel : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) (ht : tree.val < 2 ^ treeBits lay)
    (hroot : lay = 0 ∨ level + 1 < height lay) :
    ∃ n : TreeNode, treeNodeAt lay tree level c = some n ∧ n.1.lay = lay ∧ n.1.tree = tree ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold treeNodeAt
  rw [dif_pos ⟨hlevel, hc, ht, hroot⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem builtTree_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (hlevel : level ≤ height lay) (hc : c < 2 ^ (height lay - level)) (ht : tree.val < 2 ^ treeBits lay)
    (hroot : lay = 0 ∨ level < height lay) :
    treeValue (WCT9.wotsTree answers lay tree.val) level c = treeLabel labels lay tree level c := by
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 2 ^ height lay := by simpa using hc
      have h4096 : c < 4096 := lt_of_lt_of_le hc' (by
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide)
              (SigGolfCandidate.T3M.Extract.height_le lay)
          _ = 4096 := by norm_num)
      rw [WCT9.wotsTree_leaf answers lay tree.val c hc']
      have hr := leafRoot_eq h ⟨⟨lay, tree, ⟨c, h4096⟩⟩, ⟨ht, hc'⟩⟩
      unfold treeLabel leafAt
      rw [if_pos rfl, dif_pos ⟨hc', ht⟩]
      exact hr
  | succ level ih =>
      intro c hc
      have hlt : level < height lay := by omega
      have hsub : height lay - (level + 1) = height lay - level - 1 := by omega
      have hc1 : c < 2 ^ (height lay - level - 1) := by rw [← hsub]; exact hc
      have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      obtain ⟨n, hn, -, -, -, -⟩ := treeNodeAt_some lay tree level c hlt hc1 ht (by omega)
      have hs := (tree_step (fun m => h (.node m)) lay tree level c n hn
        (ih (by omega) (by omega) (2 * c) (by omega)) (ih (by omega) (by omega) (2 * c + 1) (by omega))).2
      refine hs.trans ?_
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
theorem honestRoot_eq (h : Agrees answers labels) :
    Extract.honestRoot answers 0 0 = treeLabel labels 0 0 (height 0) 0 :=
  builtTree_eq h 0 0 (height 0) 0 le_rfl (by simp) (by decide) (Or.inl rfl)
theorem honestRoot_label (h : Agrees answers labels) :
    Extract.honestRoot answers 0 0 = (labels (.node rootNode)).extractLsb' 0 128 := by
  rw [honestRoot_eq h, treeLabel_root]
theorem honestPair_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31))
    (ht : tree.val < 2 ^ treeBits lay) :
    Extract.honestPair answers lay tree.val =
      (treeLabel labels lay tree (height lay - 1) 0, treeLabel labels lay tree (height lay - 1) 1) := by
  have hpos := height_pos lay
  have hpow : 2 ≤ 2 ^ (height lay - (height lay - 1)) := by
    rw [show height lay - (height lay - 1) = 1 by omega]; norm_num
  unfold Extract.honestPair
  rw [builtTree_eq h lay tree (height lay - 1) 0 (by omega) (by omega) ht (Or.inr (by omega)),
    builtTree_eq h lay tree (height lay - 1) 1 (by omega) (by omega) ht (Or.inr (by omega))]
theorem wctValue_eq (h : Agrees answers labels) (a : WctAddr) (s : Nat) (hs : s ≤ 4) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s = wctValueL (secretsOf answers) labels a s := by
  induction s with
  | zero =>
      unfold Extract.wctValue
      rw [WCT9.eval_chain_walk]
      change Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = _
      rw [wctSeed_secrets]
      rfl
  | succ s ih =>
      have ih' := ih (by omega)
      unfold Extract.wctValue at ih' ⊢
      rw [WCT9.eval_chain_walk] at ih' ⊢
      change WCT9.projAnswer answers (WCT9.ftsChainHigh a.2.2.2.val (0 + s))
        (WCT9.ftsChainInputW a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (0 + s) (WCT9.walk _ 0 s _)) = _
      rw [ih', Nat.zero_add]
      have hcell := h (.wctChain (a, ⟨s, by omega⟩))
      simp only [cell] at hcell
      unfold WCT9.projAnswer
      rw [hcell]
      have hnode : (Node.wctChain (a, ⟨(s + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩) : Node) =
          .wctChain (a, ⟨s, by omega⟩) := by
        congr
        simp only [Nat.add_sub_cancel]
        exact Nat.mod_eq_of_lt (by omega)
      have hs4 : (s + 1 - 1) % 4 = s := by omega
      unfold wctValueL
      rw [if_neg (by omega), hnode, hs4]
theorem wctEnd_eq (h : Agrees answers labels) (a : WctAddr) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 4 = wctEndLabel labels a := by
  rw [wctValue_eq h a 4 le_rfl, wctValueL_three]
theorem wctEnds_eq (h : Agrees answers labels) (L : WctLeafPos) :
    Extract.wctEnds answers L.index.val L.coord.val L.child.val =
      List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t) := by
  unfold Extract.wctEnds
  congr 1
  funext t
  exact wctEnd_eq h (L.index, L.coord, L.child, t)
theorem childRoot_eq (h : Agrees answers labels) (L : WctLeafPos)
    (hprev : Extract.ftsPrev answers L.index.val L.coord.val = ftsPrevLabel labels L.index L.coord) :
    WCT9.childRoot answers L.index.val L.coord.val L.child.val (Extract.ftsPrev answers L.index.val L.coord.val).1 =
      (labels (.wctLeaf L)).extractLsb' 0 128 := by
  have hends : (List.ofFn fun i : Fin 6 => WCT9.chainEnd answers L.index.val L.coord.val L.child.val i) =
      Extract.wctEnds answers L.index.val L.coord.val L.child.val := rfl
  have hleaf : ∀ pad ends, WCT9.leafHashP L.index.val L.coord.val L.child.val pad ends =
      shortHash (Extract.wctLeafInputP L.index.val L.coord.val L.child.val pad ends) := by
    intro pad ends
    unfold WCT9.leafHashP WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
    simp only [List.flatMap_cons, List.append_assoc]
  unfold WCT9.childRoot
  rw [hleaf, hends, wctEnds_eq h L, hprev]
  change (answers (.inl (.inr (pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
    (ftsPrevLabel labels L.index L.coord).1
    (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t))))))).extractLsb' 0 128 = _
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.wctLeaf L))
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hlevel : level < 6)
    (hc : c < 2 ^ (7 - level - 1)) :
    ∃ n : WctNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem eval_wctTopHash (coord index heap : Nat) (l p r : Digest) :
    evalWithAnswerFn answers (WCT9.wctTopHash coord index heap l p r) =
      (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord) index heap l p r))))).extractLsb' 128 128 :=
  rfl
theorem ftsTree_eqP (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9)
    (hprev : Extract.ftsPrev answers index.val coord.val = ftsPrevLabel labels index coord) (level c : Nat)
    (hlevel : level ≤ 6) (hc : c < 2 ^ (7 - level)) :
    treeValue (Extract.ftsLevels answers index.val coord.val) level c = ftsLabel labels index coord level c := by
  have hinv := WCT9.heap_complete answers index.val coord.val (Extract.ftsPrev answers index.val coord.val).2
    (Extract.ftsLeaves answers index.val coord.val) (by simp [Extract.ftsLeaves])
  have hleaves : ∀ j (hj : j < 128), (Extract.ftsLeaves answers index.val coord.val).getD j 0 =
      (labels (.wctLeaf ⟨index, coord, ⟨j, hj⟩⟩)).extractLsb' 0 128 := by
    intro j hj
    unfold Extract.ftsLeaves
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj), List.getElem_ofFn]
    exact childRoot_eq h ⟨index, coord, ⟨j, hj⟩⟩ hprev
  unfold Extract.ftsLevels Extract.ftsNodes
  generalize evalWithAnswerFn answers (WCT9.heapBuild index.val coord.val
    (Extract.ftsPrev answers index.val coord.val).2 (Extract.ftsLeaves answers index.val coord.val)) = X at hinv ⊢
  obtain ⟨-, hleaf, hnode⟩ := hinv
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 128 := by simpa using hc
      rw [WCT9.heapLevels_value X 0 c (by decide) (by simpa using hc)]
      rw [show 2 ^ (7 - 0) + c = 128 + c by norm_num, hleaf (128 + c) (by omega) (by omega),
        Nat.add_sub_cancel_left, hleaves c hc']
      unfold ftsLabel
      rw [if_pos rfl, dif_pos hc']
  | succ level ih =>
      intro c hc
      have hlt : level < 6 := by omega
      have hsub : 7 - (level + 1) = 7 - level - 1 := by omega
      have hc1 : c < 2 ^ (7 - level - 1) := by rw [← hsub]; exact hc
      have hpow : 2 ^ (7 - level) = 2 * 2 ^ (7 - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpos : 2 ≤ 2 ^ (7 - level - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (7 - level - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hle : 2 ^ (7 - level - 1) ≤ 64 :=
        (Nat.pow_le_pow_right (by decide) (by omega : 7 - level - 1 ≤ 6)).trans (by decide)
      have hchild : ∀ j, j < 2 * c + 2 → treeValue (WCT9.heapLevels X) level j = ftsLabel labels index coord level j := by
        intro j hj
        exact ih (by omega) j (by omega)
      obtain ⟨n, hn, hindex, hcoord, hlev, hidx⟩ := ftsNodeAt_some index coord level c hlt hc1
      have hrhs : ftsLabel labels index coord (level + 1) c = if level + 1 = 6 then
          (labels (.wctNode n)).extractLsb' 128 128 else (labels (.wctNode n)).extractLsb' 0 128 := by
        unfold ftsLabel
        rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      have hinput : cell (secretsOf answers) (.wctNode n) labels =
          pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2 ^ (7 - level - 1) + c)
            (ftsLabel labels index coord level (2 * c))
            (if level = 5 then (ftsPrevLabel labels index coord).2 else 0)
            (ftsLabel labels index coord level (2 * c + 1))) := by
        obtain ⟨⟨nindex, ncoord, nlevel, nidx⟩, hv⟩ := n
        simp only at hindex hcoord hlev hidx
        subst hindex hcoord
        simp only [cell]
        rw [hlev, hidx]
      rw [hrhs, WCT9.heapLevels_value X (level + 1) c (by omega) hc, hsub]
      have hl := WCT9.heapLevels_value X level (2 * c) (by omega) (by omega)
      have hr := WCT9.heapLevels_value X level (2 * c + 1) (by omega) (by omega)
      rw [hnode (2 ^ (7 - level - 1) + c) (by omega) (by omega) (by omega)]
      have e1 : 2 * (2 ^ (7 - level - 1) + c) = 2 ^ (7 - level) + 2 * c := by omega
      rw [e1, show 2 ^ (7 - level) + 2 * c + 1 = 2 ^ (7 - level) + (2 * c + 1) by omega, ← hl, ← hr,
        hchild (2 * c) (by omega), hchild (2 * c + 1) (by omega)]
      by_cases h5 : level = 5
      · subst h5
        rw [if_pos rfl, WCT9.wctHeapNode_top (by norm_num at hc1 ⊢; omega), eval_wctTopHash, hprev]
        rw [if_pos rfl] at hinput
        rw [← hinput]
        exact congrArg (fun output : HashOutput => output.extractLsb' 128 128) (h (.wctNode n))
      · rw [if_neg (by omega), WCT9.wctHeapNode_low (by
          have : 4 ≤ 2 ^ (7 - level - 1) := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (7 - level - 1) := Nat.pow_le_pow_right (by decide) (by omega)
          omega), WCT9.wctNodeHash,
          nodeHash_eq_shortHash (SigGolfCandidate.T3.nodeHalfHigh_of_ne (by simp [WCT9.nodeLayer]) _), eval_shortHash]
        rw [if_neg h5] at hinput
        rw [← hinput]
        exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.wctNode n))
theorem ftsPrev_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    ∀ c (hc : c < 9), Extract.ftsPrev answers index.val c = ftsPrevLabel labels index ⟨c, hc⟩
  | 0, _ => by
    unfold ftsPrevLabel
    rw [dif_pos rfl]; rfl
  | c + 1, hc => by
    have ih := ftsPrev_eq h index c (by omega)
    have hpair : Extract.ftsPair answers index.val c = Extract.ftsPrev answers index.val (c + 1) := by
      unfold Extract.ftsPair Extract.ftsLevels
      rw [WCT9.heapLevels_value _ 6 0 (by decide) (by decide), WCT9.heapLevels_value _ 6 1 (by decide) (by decide)]
      rfl
    rw [← hpair]
    unfold Extract.ftsPair
    rw [ftsTree_eqP h index ⟨c, by omega⟩ ih 6 0 le_rfl (by decide),
      ftsTree_eqP h index ⟨c, by omega⟩ ih 6 1 le_rfl (by decide)]
    unfold ftsPrevLabel
    rw [dif_neg (by simp)]
    rfl
theorem ftsTree_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hlevel : level ≤ 6) (hc : c < 2 ^ (7 - level)) :
    treeValue (Extract.ftsLevels answers index.val coord.val) level c = ftsLabel labels index coord level c :=
  ftsTree_eqP h index coord (ftsPrev_eq h index coord.val coord.isLt) level c hlevel hc
theorem ftsPair_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 9) :
    Extract.ftsPair answers index.val coord.val = (ftsLabel labels index coord 6 0, ftsLabel labels index coord 6 1) := by
  unfold Extract.ftsPair
  rw [ftsTree_eq h index coord 6 0 le_rfl (by decide), ftsTree_eq h index coord 6 1 le_rfl (by decide)]
theorem ftsPairs_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.ftsPairsHonest answers index.val =
      (List.range 9).map fun coord => (ftsLabel labels index (fin9 coord) 6 0, ftsLabel labels index (fin9 coord) 6 1) := by
  unfold Extract.ftsPairsHonest
  apply List.map_congr_left
  intro coord hcoord
  have hc : coord < 9 := List.mem_range.mp hcoord
  have hval : (fin9 coord).val = coord := Nat.mod_eq_of_lt hc
  have hx := ftsPair_eq h index (fin9 coord)
  rw [hval] at hx
  exact hx
/-- The honest L3 message (nested FTS r1-1) in labels: the high halves of coordinate 8's two top nodes. -/
theorem honestTop_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.honestTop answers index.val = (ftsLabel labels index 8 6 0, ftsLabel labels index 8 6 1) :=
  ftsPair_eq h index 8
theorem honestInput_eq (h : Agrees answers labels) (node : Node) :
    Extract.honestInput answers node.toPos = cell (secretsOf answers) (node.sel labels) labels := by
  cases node with
  | chain p =>
      simp only [Node.sel, Node.toPos, Extract.honestInput]
      change pad64 (rowW p (Wots.honestChainValueW answers _ _ _ _ (WCT9.wotsSeed answers _ _ _ _) _)) =
        rowW p (priorW _ p _)
      rw [chainValue_eq h p.1 p.2.val (by have := p.2.isLt; omega), rowW_pad64, priorW_eq_valueW]
  | leaf L =>
      simp only [Node.sel, Node.toPos, Extract.honestInput, cell]
      rw [leafEnds_eq h L.1]
  | node n =>
      have hv1 : n.1.level.val < height n.1.lay := n.2.1
      have hv2 : n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) := n.2.2.1
      have hv3 : n.1.tree.val < 2 ^ treeBits n.1.lay := n.2.2.2.1
      have hpow : 2 ^ (height n.1.lay - n.1.level.val) = 2 * 2 ^ (height n.1.lay - n.1.level.val - 1) := by
        rw [← pow_succ']; congr 1; omega
      exact honestInput_node_sel (fun m => h (.node m)) n
        (builtTree_eq h _ _ _ _ (by omega) (by omega) hv3 (by omega))
        (builtTree_eq h _ _ _ _ (by omega) (by omega) hv3 (by omega))
  | wctChain p =>
      simp only [Node.sel, Node.toPos, Extract.honestInput, cell]
      rw [wctValue_eq h p.1 p.2.val (by have := p.2.isLt; omega), WCT9.ftsChainInputW_padded]
  | wctLeaf L =>
      simp only [Node.sel, Node.toPos, Extract.honestInput, cell]
      rw [wctEnds_eq h L, ftsPrev_eq h L.index L.coord.val L.coord.isLt]
  | wctNode n =>
      obtain ⟨⟨index, coord, level, idx⟩, hv⟩ := n
      have hv' : idx.val < 2 ^ (7 - level.val - 1) := hv
      simp only [Node.sel, Node.toPos, Extract.honestInput, cell]
      have hpow : 2 ^ (7 - level.val) = 2 * 2 ^ (7 - level.val - 1) := by
        have := level.isLt
        rw [← pow_succ']; congr 1; omega
      rw [ftsTree_eq h index coord level.val (2 * idx.val) (by have := level.isLt; omega) (by omega),
        ftsTree_eq h index coord level.val (2 * idx.val + 1) (by have := level.isLt; omega) (by omega),
        ftsPrev_eq h index coord.val coord.isLt]
  | forest index =>
      simp only [Node.sel, Node.toPos, Extract.honestInput, cell]
      rw [ftsPairs_eq h index]
theorem honest_answer (h : Agrees answers labels) (node : Node) :
    answers (.inl (.inr (Extract.honestInput answers node.toPos))) = labels (node.sel labels) := by
  rw [honestInput_eq h node]
  exact h (node.sel labels)
end Honest
end ClaudeWCT.W9.T3.Security.CanonGraph

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open ChainGraph (Address Point Seeds)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree ClaudeWCT.WCT9.heapBuild
def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ node, answers (.inl (.inr (cell (secretsOf answers) node labels))) = labels node
theorem secretsOf_eager (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput) :
    secretsOf (eagerAnswers privateTable U publicTable) = privateSecrets privateTable := rfl
theorem eagerAnswers_mem (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput)
    (x : U) : eagerAnswers privateTable U publicTable (.inl (.inr x.val)) = publicTable x :=
  finiteHashAnswer_none ∅ U publicTable x.val x.property rfl
theorem agrees_of_programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (answers : Answers)
    (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node
  have h := hpub (cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at] at h
  exact h
theorem eager_programmed_agrees (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (other : OtherHalves) (labels : Labels) (residual : U → HashOutput) :
    Agrees (eagerAnswers (privateEquiv.symm (secrets, other)) U (programmed U hU secrets labels residual)) labels := by
  apply agrees_of_programmed U hU _ labels residual
  intro x
  rw [secretsOf_eager, privateSecrets_symm, eagerAnswers_mem]
theorem agrees_chain {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    AgreesW answers (seedsOf (secretsOf answers)) (chainLabels labels) :=
  fun point => h (.chain point)

section Honest
variable {answers : Answers} {labels : Labels}
-- Stage 2 (C2/C3, #866): the paired honest section follows the #866 legacy section above (`chainValueW_succ`,
-- `leafValue_eq`/`leafEnd_eq` through `Pos.proj` of the last chain step, `leafRoot_eq` through `Pos.proj` of the
-- leaf label, `builtTree_eq` with `lowerNodeHash`); `Paired.cell` is `CanonGraph.cell` on the lower nodes.
/-- Pairing stage 1: the honest chain of the current scheme (`WCT9.chainW`, G chains on the high half) after `step`
steps is the label value `valueW`. -/
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    Wots.honestChainValueW answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      valueW (seedsOf (secretsOf answers)) (chainLabels labels) a step := by
  have hx := sourceW_chain answers (seedsOf (secretsOf answers)) (chainLabels labels) (agrees_chain h) a 0
    step (by omega)
  rw [valueW_zero, seedsOf_secretsOf, Nat.zero_add] at hx
  exact hx
theorem maxDigit_le_seven (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> decide
/-- C3: the honest chain of the current scheme after `m + 1` steps is the used half (`Pos.proj`: the high half for
the last step of a lower chain 0) of step `m`'s label. -/
theorem chainValueW_succ (h : Agrees answers labels) (a : Address) (m : Fin 7) :
    Wots.honestChainValueW answers a.layer a.tree.val a.leaf.val a.chain.val
      (WCT9.wotsSeed answers a.layer a.tree.val a.leaf.val a.chain.val) (m.val + 1) =
      (Node.chain (a, m)).toPos.proj (labels (.chain (a, m))) := by
  have hm := m.isLt
  rw [← Wots.honestChainValueW_succ, chainValue_eq h a m.val (by omega)]
  have hrow : pad64 (WCT9.chainInputW a.layer a.tree.val a.leaf.val a.chain.val m.val
      (valueW (seedsOf (secretsOf answers)) (chainLabels labels) a m.val)) =
      cell (secretsOf answers) (.chain (a, m)) labels := by
    simp only [cell, CanonGraph.cell]
    rw [inputW, priorW_eq_valueW]
    exact WCT9.chainInputW_padded _ _ _ _ _ _
  have hp : (Node.chain (a, m)).toPos.proj = WCT9.halfOf (WCT9.chainHigh a.layer a.chain.val m.val) := rfl
  rw [hp, hrow, h (.chain (a, m))]
/-- C3: a revealed chain value is the seed (digit 0) or the used half of the label of the step before it. -/
theorem leafValue_eq (h : Agrees answers labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hdigit : digits.getD i 0 ≤ 7) :
    WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      if digits.getD i 0 = 0 then seedsOf (secretsOf answers) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
      else (Node.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(digits.getD i 0 - 1) % 7, Nat.mod_lt _ (by decide)⟩)).toPos.proj
        (labels (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(digits.getD i 0 - 1) % 7, Nat.mod_lt _ (by decide)⟩))) := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have he : WCT9.wotsValue answers L.lay L.tree.val L.leaf.val digits i =
      Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
        (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val) (digits.getD i 0) := by
    unfold WCT9.wotsValue Wots.honestChainValueW; rw [hval]
  rw [he]
  split_ifs with h0
  · rw [h0, Wots.honestChainValueW_zero, seedsOf_secretsOf]
  · obtain ⟨m, hm⟩ : ∃ m, digits.getD i 0 = m + 1 := ⟨digits.getD i 0 - 1, by omega⟩
    have hmod : (digits.getD i 0 - 1) % 7 = m := by rw [hm]; exact Nat.mod_eq_of_lt (by omega)
    have hx := chainValueW_succ h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ ⟨m, by omega⟩
    simp only [hmod]
    exact (congrArg (Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
      (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val)) hm).trans hx
/-- C3: a chain end is the used half (`Pos.proj`, the high half for lower chain 0) of its last step's label. -/
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (i : Nat) (hi : i < 58) :
    WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hm1 : 1 ≤ maxDigit L.lay i := by unfold maxDigit; split_ifs <;> decide
  have hm7 := maxDigit_le_seven L.lay i
  obtain ⟨m, hm⟩ : ∃ m, maxDigit L.lay i = m + 1 := ⟨maxDigit L.lay i - 1, by omega⟩
  have hmod : (maxDigit L.lay i - 1) % 7 = m := by rw [hm]; exact Nat.mod_eq_of_lt (by omega)
  have he : WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val i =
      Wots.honestChainValueW answers L.lay L.tree.val L.leaf.val (fin58 i).val
        (WCT9.wotsSeed answers L.lay L.tree.val L.leaf.val (fin58 i).val) (maxDigit L.lay i) := by
    unfold WCT9.wotsEnd Wots.honestChainValueW; rw [hval]
  have hx := chainValueW_succ h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ ⟨m, by omega⟩
  rw [he, hm, hx]
  unfold endLabel endPt
  simp only [hmod]
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) :
    (List.range (chainCount L.lay)).map (WCT9.wotsEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
/-- C2: a leaf value is the used half (`Pos.proj`) of its leaf label. -/
theorem leafRoot_eq (h : Agrees answers labels) (L : SrcLeaf) :
    WCT9.wotsRoot answers L.1.lay L.1.tree.val L.1.leaf.val = (Node.leaf L).toPos.proj (labels (.leaf L)) := by
  unfold WCT9.wotsRoot
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  rw [Wots.eval_halfHash', leafEnds_eq h L.1]
  exact congrArg (WCT9.halfOf (WCT9.lowerHigh L.1.lay.val L.1.leaf.val)) (h (.leaf L))
theorem treeNodeAt_some (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hlevel : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) (ht : tree.val < 2 ^ treeBits lay)
    (hroot : lay = 0 ∨ level + 1 < height lay) :
    ∃ n : TreeNode, treeNodeAt lay tree level c = some n ∧ n.1.lay = lay ∧ n.1.tree = tree ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold treeNodeAt
  rw [dif_pos ⟨hlevel, hc, ht, hroot⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem builtTree_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (hlevel : level ≤ height lay) (hc : c < 2 ^ (height lay - level)) (ht : tree.val < 2 ^ treeBits lay)
    (hroot : lay = 0 ∨ level < height lay) :
    treeValue (WCT9.wotsTree answers lay tree.val) level c = treeLabel labels lay tree level c := by
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 2 ^ height lay := by simpa using hc
      have h4096 : c < 4096 := lt_of_lt_of_le hc' (by
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide)
              (SigGolfCandidate.T3M.Extract.height_le lay)
          _ = 4096 := by norm_num)
      rw [WCT9.wotsTree_leaf answers lay tree.val c hc']
      have hr := leafRoot_eq h ⟨⟨lay, tree, ⟨c, h4096⟩⟩, ⟨ht, hc'⟩⟩
      unfold treeLabel leafAt
      rw [if_pos rfl, dif_pos ⟨hc', ht⟩]
      exact hr
  | succ level ih =>
      intro c hc
      have hlt : level < height lay := by omega
      have hsub : height lay - (level + 1) = height lay - level - 1 := by omega
      have hc1 : c < 2 ^ (height lay - level - 1) := by rw [← hsub]; exact hc
      have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      obtain ⟨n, hn, -, -, -, -⟩ := treeNodeAt_some lay tree level c hlt hc1 ht (by omega)
      have hs := (tree_step (fun m => h (.node m)) lay tree level c n hn
        (ih (by omega) (by omega) (2 * c) (by omega)) (ih (by omega) (by omega) (2 * c + 1) (by omega))).2
      refine hs.trans ?_
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
theorem honestRoot_eq (h : Agrees answers labels) :
    Extract.honestRoot answers 0 0 = treeLabel labels 0 0 (height 0) 0 :=
  builtTree_eq h 0 0 (height 0) 0 le_rfl (by simp) (by decide) (Or.inl rfl)
theorem honestRoot_label (h : Agrees answers labels) :
    Extract.honestRoot answers 0 0 = (labels (.node rootNode)).extractLsb' 0 128 := by
  rw [honestRoot_eq h, treeLabel_root]
theorem honestPair_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31))
    (ht : tree.val < 2 ^ treeBits lay) :
    Extract.honestPair answers lay tree.val =
      (treeLabel labels lay tree (height lay - 1) 0, treeLabel labels lay tree (height lay - 1) 1) := by
  have hpos := height_pos lay
  have hpow : 2 ≤ 2 ^ (height lay - (height lay - 1)) := by
    rw [show height lay - (height lay - 1) = 1 by omega]; norm_num
  unfold Extract.honestPair
  rw [builtTree_eq h lay tree (height lay - 1) 0 (by omega) (by omega) ht (Or.inr (by omega)),
    builtTree_eq h lay tree (height lay - 1) 1 (by omega) (by omega) ht (Or.inr (by omega))]
theorem wctValue_eq (h : Agrees answers labels) (a : WctAddr) (s : Nat) (hs : s ≤ 4) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s = wctValueL (secretsOf answers) labels a s := by
  induction s with
  | zero =>
      unfold Extract.wctValue
      rw [WCT9.eval_chain_walk]
      change Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = _
      rw [wctSeed_secrets]
      rfl
  | succ s ih =>
      have ih' := ih (by omega)
      unfold Extract.wctValue at ih' ⊢
      rw [WCT9.eval_chain_walk] at ih' ⊢
      change WCT9.projAnswer answers (WCT9.ftsChainHigh a.2.2.2.val (0 + s))
        (WCT9.ftsChainInputW a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (0 + s) (WCT9.walk _ 0 s _)) = _
      rw [ih', Nat.zero_add]
      have hcell := h (.wctChain (a, ⟨s, by omega⟩))
      simp only [cell,CanonGraph.cell] at hcell
      unfold WCT9.projAnswer
      rw [hcell]
      have hnode : (Node.wctChain (a, ⟨(s + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩) : Node) =
          .wctChain (a, ⟨s, by omega⟩) := by
        congr
        simp only [Nat.add_sub_cancel]
        exact Nat.mod_eq_of_lt (by omega)
      have hs4 : (s + 1 - 1) % 4 = s := by omega
      unfold wctValueL
      rw [if_neg (by omega), hnode, hs4]
theorem wctEnd_eq (h : Agrees answers labels) (a : WctAddr) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 4 = wctEndLabel labels a := by
  rw [wctValue_eq h a 4 le_rfl, wctValueL_three]
theorem wctEnds_eq (h : Agrees answers labels) (L : WctLeafPos) :
    Extract.wctEnds answers L.index.val L.coord.val L.child.val =
      List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t) := by
  unfold Extract.wctEnds
  congr 1
  funext t
  exact wctEnd_eq h (L.index, L.coord, L.child, t)

end Honest
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem rawLeaf_lt (coord child : Nat) (hc : child<128) : rawLeaf coord child<128 := by
  unfold rawLeaf
  split_ifs <;> omega

theorem pads_raw_branch (labels : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (child : Nat) (hc : child<128) :
    pads labels index coord (child/64)=pads labels index coord (rawLeaf coord.val child%2) := by
  unfold pads
  split_ifs with hz ho
  · rfl
  · have hn:¬first coord.val := by unfold first;omega
    have he:rawLeaf coord.val child%2=child/64 := by unfold rawLeaf;rw [if_neg hn];omega
    rw [he]
  · rfl


def topLevel (coord : Fin 9) : Nat := if first coord.val then 5 else 6

/-- The source heap recurrence, expressed with the fixed projection of its address. -/
def NodesRec (answers : Answers) (labels : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (nodes : Array Digest) : Prop :=
  ∀ level, level<topLevel coord → ∀ c,c<2^(6-level) →
    nodes.getD (2^(6-level)+c) 0 =
      Extract.Paired.proj (.wctNode index.val coord.val level c)
        (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val
          (2^(6-level)+c) (nodes.getD (2*(2^(6-level)+c)) 0)
          (if level=4 then (pads labels index coord (c/2)).2 else 0)
          (nodes.getD (2*(2^(6-level)+c)+1) 0))))))

theorem nodes_label (answers : Answers) (labels : Labels) (ha : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (nodes : Array Digest)
    (hleaf : ∀c,c<128 → nodes.getD (128+c) 0=ftsLabel labels index coord 0 c)
    (hnode : NodesRec answers labels index coord nodes)
    (level c : Nat) (hl : level≤topLevel coord) (hc : c<2^(7-level)) :
    nodes.getD (2^(7-level)+c) 0=ftsLabel labels index coord level c := by
  have ht:topLevel coord≤6 := by unfold topLevel;split_ifs <;> omega
  induction level generalizing c with
  | zero=> exact hleaf c (by simpa using hc)
  | succ level ih=>
    have hl6:level<6 := by omega
    have hsub:7-(level+1)=6-level := by omega
    have hc':c<2^(6-level) := by simpa only [hsub] using hc
    have hpow:2^(7-level)=2*2^(6-level) := by rw [←pow_succ'];congr 1;omega
    have hleft : nodes.getD (2^(7-level)+2*c) 0=ftsLabel labels index coord level (2*c) := by
      apply ih <;> omega
    have hright : nodes.getD (2^(7-level)+(2*c+1)) 0=ftsLabel labels index coord level (2*c+1) := by
      apply ih <;> omega
    have hrec:=hnode level (by omega) c hc'
    have haddr:2*(2^(6-level)+c)=2^(7-level)+2*c := by rw [hpow];omega
    have haddr':2*(2^(6-level)+c)+1=2^(7-level)+(2*c+1) := by rw [hpow];omega
    rw [haddr,hleft] at hrec
    rw [show 2^(7-level)+2*c+1=2^(7-level)+(2*c+1) by omega,hright] at hrec
    obtain ⟨n,hn,hindex,hcoord,hlevel,hidx⟩:=CanonGraph.ftsNodeAt_some index coord level c hl6
      (by simpa only [show 7-level-1=6-level by omega] using hc')
    have hcell:cell (secretsOf answers) (.wctNode n) labels =
        pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level)+c)
          (ftsLabel labels index coord level (2*c))
          (if level=4 then (pads labels index coord (c/2)).2 else 0)
          (ftsLabel labels index coord level (2*c+1))) := by
      simp only [cell,hindex,hcoord,hlevel,hidx,show 7-level-1=6-level by omega]
    have he:=ha (.wctNode n)
    rw [hcell] at he
    rw [he] at hrec
    rw [hsub,hrec]
    unfold ftsLabel
    rw [if_neg (by omega : level+1≠0),show level+1-1=level by omega,hn]

end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem sharedNode_eval (answers : Answers) (index : Fin (2^31)) (coord : Fin 9)
    (ps : Nat → Digest×Digest) (left right : Digest) (level c : Nat)
    (hl : level<topLevel coord) (hc : c<2^(6-level)) :
    evalWithAnswerFn answers (Research.SharedForest.sharedNode (decide (first coord.val)) coord.val index.val
      (2^(6-level)+c) ps left right) =
      Extract.Paired.proj (.wctNode index.val coord.val level c)
        (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val
          (2^(6-level)+c) left (if level=4 then (ps (c/2)).2 else 0) right))))) := by
  have hl6:level<6 := by unfold topLevel at hl;split_ifs at hl <;> omega
  have hu : Extract.Paired.first coord.val = true → level < 5 := by
    intro hf
    have hf' : first coord.val := of_decide_eq_true hf
    simp only [topLevel, if_pos hf'] at hl
    exact hl
  have hd : decide (first coord.val) = Extract.Paired.first coord.val := rfl
  rw [hd, Extract.Paired.sharedNode_eq_nodeProgramP index.val coord.val level c coord.isLt hl6 hc hu ps left right,
    Extract.Paired.eval_nodeProgram]
  have hpad : (if level=4 then (ps ((2^(6-level)+c)/2-2)).2 else (0:Digest)) =
      (if level=4 then (ps (c/2)).2 else 0) := by
    by_cases h4 : level=4
    · subst level
      rw [if_pos rfl, if_pos rfl, show (2^(6-4)+c)/2-2=c/2 by norm_num; omega]
    · rw [if_neg h4, if_neg h4]
  rw [hpad]
  rfl
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

/-- C1: the honest leaf (heap `128 + physical`) is the fixed projection of its label. -/
theorem childRoot_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels) (L : WctLeafPos) :
    WCT9.childRootH answers (128 + Extract.Paired.physical L.coord.val L.child.val)
      L.index.val L.coord.val L.child.val (pads labels L.index L.coord (L.child.val%2)).1 =
      Extract.Paired.proj (.wctLeaf L.index.val L.coord.val L.child.val) (labels (.wctLeaf L)) := by
  have hends : (List.ofFn fun i : Fin 6 => WCT9.chainEnd answers L.index.val L.coord.val L.child.val i) =
      Extract.wctEnds answers L.index.val L.coord.val L.child.val := rfl
  have hleaf : ∀ pad ends, WCT9.leafHashH (128 + Extract.Paired.physical L.coord.val L.child.val)
      L.index.val L.coord.val L.child.val pad ends =
      WCT9.ftsHash (128 + Extract.Paired.physical L.coord.val L.child.val)
        (Extract.wctLeafInputP L.index.val L.coord.val L.child.val pad ends) := by
    intro pad ends
    unfold WCT9.leafHashH WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
    simp only [List.flatMap_cons, List.append_assoc]
  unfold WCT9.childRootH
  rw [hleaf,hends,wctEnds_eq h L,WCT9.eval_ftsHash,Extract.Paired.proj_wctLeaf]
  exact congrArg (WCT9.ftsHalf (128 + Extract.Paired.physical L.coord.val L.child.val)) (h (.wctLeaf L))

theorem physical_rawLeaf (coord : Fin 9) (c : Nat) (hc : c<128) :
    Extract.Paired.physical coord.val (rawLeaf coord.val c)=c := by
  unfold Extract.Paired.physical Research.SharedForest.physicalChild Extract.Paired.first rawLeaf
  by_cases hf : first coord.val
  · have hf' : decide (coord.val<8 ∧ coord.val%2=0)=true := decide_eq_true hf
    simp only [hf', if_pos hf, ↓reduceIte]
  · have hf' : decide (coord.val<8 ∧ coord.val%2=0)=false := decide_eq_false hf
    simp only [hf', if_neg hf, Bool.false_eq_true, ↓reduceIte]
    omega

theorem rawChild_eq (coord child : Nat) :
    Research.SharedForest.rawChild (decide (first coord)) child=rawLeaf coord child := by
  simp only [Research.SharedForest.rawChild,rawLeaf,decide_eq_true_eq]

theorem source_leaves_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b) (c : Nat) (hc : c<128) :
    (Research.SharedForest.sharedLeaves answers (decide (first coord.val)) index.val coord.val ps).getD c 0 =
      ftsLabel labels index coord 0 c := by
  unfold Research.SharedForest.sharedLeaves
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact hc),List.getElem_ofFn]
  rw [rawChild_eq,hps _ (by omega),pads_raw_branch labels index coord c hc]
  have he:=childRoot_eq answers labels h ⟨index,coord,⟨rawLeaf coord.val c,rawLeaf_lt _ _ hc⟩⟩
  simp only [physical_rawLeaf coord c hc] at he
  unfold ftsLabel
  rw [if_pos rfl,dif_pos (rawLeaf_lt _ _ hc)]
  exact he

theorem source_nodes_rec (answers : Answers) (labels : Labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b) :
    NodesRec answers labels index coord
      (Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps) := by
  intro level hl c hc
  have hl6:level<6 := by unfold topLevel at hl;split_ifs at hl <;> omega
  have hr : Research.SharedForest.heapCut (decide (first coord.val))≤2^(6-level)+c ∧
      2^(6-level)+c<128 := by
    interval_cases level <;> norm_num at hc ⊢
    all_goals unfold Research.SharedForest.heapCut
    all_goals split_ifs with hf <;> try omega
    all_goals have hf':first coord.val := of_decide_eq_true hf
    all_goals simp only [topLevel,if_pos hf'] at hl
    all_goals omega
  have hg:=Research.SharedForest.sharedNodes_graph answers (decide (first coord.val)) index.val coord.val ps
  have he:=hg.2.2 (2^(6-level)+c) hr.1 hr.2 (by have:=Research.SharedForest.heapCut_bounds (decide (first coord.val));omega)
  have hpad : (if level=4 then (ps (c/2)).2 else (0:Digest))=
      (if level=4 then (pads labels index coord (c/2)).2 else 0) := by
    by_cases h4:level=4
    · subst level
      have hc4:c<4 := by simpa using hc
      rw [if_pos rfl,hps _ (by omega),if_pos rfl]
    · rw [if_neg h4,if_neg h4]
  exact he.trans ((sharedNode_eval answers index coord ps _ _ level c hl hc).trans
    (congrArg (fun pad:Digest=>Extract.Paired.proj (.wctNode index.val coord.val level c)
      (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level)+c)
        ((Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps).getD (2*(2^(6-level)+c)) 0)
        pad
        ((Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps).getD (2*(2^(6-level)+c)+1) 0))))))) hpad))

theorem source_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b)
    (level c : Nat) (hl : level≤topLevel coord) (hc : c<2^(7-level)) :
    (Research.SharedForest.sharedNodes answers (decide (first coord.val)) index.val coord.val ps).getD
      (2^(7-level)+c) 0=ftsLabel labels index coord level c := by
  apply nodes_label answers labels h index coord _ _ (source_nodes_rec answers labels index coord ps hps) level c hl hc
  intro j hj
  have hg:=Research.SharedForest.sharedNodes_graph answers (decide (first coord.val)) index.val coord.val ps
  rw [hg.2.1 (128+j) (by omega) (by omega),Nat.add_sub_cancel_left]
  exact source_leaves_label answers labels h index coord ps hps j hj
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

def pairLabel (labels : Labels) (index : Fin (2^31)) (pair : Fin 5) : Digest×Digest :=
  if h:pair.val=0 then WCT9.ftsStart else
    let coord:Fin 9:=⟨2*pair.val-1,by have:=pair.isLt;omega⟩
    (ftsLabel labels index coord 6 0,ftsLabel labels index coord 6 1)

theorem pads_even (labels : Labels) (index : Fin (2^31)) (pair : Fin 5) (branch : Nat) :
    pads labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ branch=pairLabel labels index pair := by
  fin_cases pair <;> rfl

theorem pads_odd (labels : Labels) (index : Fin (2^31)) (pair : Fin 4) (branch : Nat) :
    pads labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ branch=
      (ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ 5 (2*branch),
       ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ 5 (2*branch+1)) := by
  fin_cases pair <;> rfl

theorem firstNodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (pair : Fin 4) (prev : Digest×Digest)
    (hp : prev=pairLabel labels index ⟨pair.val,by have:=pair.isLt;omega⟩)
    (level c : Nat) (hl : level≤5) (hc : c<2^(7-level)) :
    (Research.SharedForest.firstNodes answers index.val pair.val prev).getD (2^(7-level)+c) 0=
      ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ level c := by
  let coord:Fin 9:=⟨2*pair.val,by have:=pair.isLt;omega⟩
  have hf:first coord.val := by dsimp[coord];unfold first;omega
  have hpads:∀b,b<2 → prev=pads labels index coord b := by
    intro b hb
    exact hp.trans (pads_even labels index ⟨pair.val,by have:=pair.isLt;omega⟩ b).symm
  have he:=source_nodes_label answers labels h index coord (fun _=>prev) hpads level c
    (by simpa only [topLevel,if_pos hf] using hl) hc
  simpa only [coord,Research.SharedForest.firstNodes,decide_eq_true hf] using he

theorem secondNodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (pair : Fin 4) (prev : Digest×Digest)
    (hp : prev=pairLabel labels index ⟨pair.val,by have:=pair.isLt;omega⟩)
    (level c : Nat) (hl : level≤6) (hc : c<2^(7-level)) :
    (Research.SharedForest.secondNodes answers index.val pair.val prev).getD (2^(7-level)+c) 0=
      ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ level c := by
  let coord:Fin 9:=⟨2*pair.val+1,by have:=pair.isLt;omega⟩
  have hf:¬first coord.val := by dsimp[coord];unfold first;omega
  have hpads:∀b,b<2 → Research.SharedForest.nodesPair
      (Research.SharedForest.firstNodes answers index.val pair.val prev) b=pads labels index coord b := by
    intro b hb
    rw [pads_odd labels index pair b]
    unfold Research.SharedForest.nodesPair
    apply Prod.ext
    · exact firstNodes_label answers labels h index pair prev hp 5 (2*b) (by decide) (by norm_num;omega)
    · simpa only [show 2^(7-5)+(2*b+1)=5+2*b by norm_num;omega] using firstNodes_label answers labels h index pair prev hp 5 (2*b+1) (by decide) (by norm_num;omega)
  have he:=source_nodes_label answers labels h index coord
    (Research.SharedForest.nodesPair (Research.SharedForest.firstNodes answers index.val pair.val prev))
    hpads level c (by simpa only [topLevel,if_neg hf] using hl) hc
  simpa only [coord,Research.SharedForest.secondNodes,decide_eq_false hf] using he
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

theorem pairLabel_succ (labels : Labels) (index : Fin (2^31)) (pair : Fin 4) :
    pairLabel labels index ⟨pair.val+1,by have:=pair.isLt;omega⟩ =
      (ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ 6 0,
       ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ 6 1) := by
  fin_cases pair <;> rfl

theorem pairPrev_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) : ∀n,(hn:n≤4) →
      Extract.Paired.pairPrev answers index.val n=pairLabel labels index ⟨n,by omega⟩
  | 0,_=>rfl
  | n+1,hn=>by
    have ih:=pairPrev_label answers labels h index n (by omega)
    rw [Extract.Paired.pairPrev,pairLabel_succ labels index ⟨n,by omega⟩]
    apply Prod.ext
    · exact secondNodes_label answers labels h index ⟨n,by omega⟩ _ ih 6 0 (by decide) (by decide)
    · exact secondNodes_label answers labels h index ⟨n,by omega⟩ _ ih 6 1 (by decide) (by decide)

theorem source_pads_even (answers : Answers) (index : Nat) (pair : Fin 5) (branch : Nat) :
    Extract.Paired.pads answers index (2*pair.val) branch=Extract.Paired.pairPrev answers index pair.val := by
  fin_cases pair <;> rfl

theorem source_pads_odd (answers : Answers) (index : Nat) (pair : Fin 4) (branch : Nat) :
    Extract.Paired.pads answers index (2*pair.val+1) branch=
      Research.SharedForest.nodesPair
        (Research.SharedForest.firstNodes answers index pair.val (Extract.Paired.pairPrev answers index pair.val)) branch := by
  fin_cases pair <;> rfl

theorem source_pads_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (hb:branch<2) :
    Extract.Paired.pads answers index.val coord.val branch=pads labels index coord branch := by
  by_cases he:coord.val%2=0
  · let p:Fin 5:=⟨coord.val/2,by have:=coord.isLt;omega⟩
    have hc:coord=⟨2*p.val,by have:=p.isLt;omega⟩:=by apply Fin.ext;dsimp[p];omega
    rw [hc]
    rw [source_pads_even,pads_even,pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)]
  · let p:Fin 4:=⟨coord.val/2,by have:=coord.isLt;omega⟩
    have hc:coord=⟨2*p.val+1,by have:=p.isLt;omega⟩:=by apply Fin.ext;dsimp[p];omega
    rw [hc]
    rw [source_pads_odd,pads_odd]
    unfold Research.SharedForest.nodesPair
    apply Prod.ext
    · exact firstNodes_label answers labels h index p _
        (pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)) 5 (2*branch) (by decide) (by norm_num;omega)
    · simpa only [show 2^(7-5)+(2*branch+1)=5+2*branch by norm_num;omega] using firstNodes_label answers labels h index p _
        (pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)) 5 (2*branch+1) (by decide) (by norm_num;omega)
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

theorem nodes_source (answers : Answers) (index : Nat) (coord : Fin 9) :
    Extract.Paired.nodes answers index coord.val = Research.SharedForest.sharedNodes (answers)
      (decide (first coord.val)) index coord.val (Extract.Paired.pads answers index coord.val) := by
  fin_cases coord <;> simp only [Extract.Paired.nodes,Extract.Paired.first,first,Research.SharedForest.firstNodes,Research.SharedForest.secondNodes]
  all_goals norm_num
  all_goals first | rfl | (congr 1;funext b;simp only [Extract.Paired.pads,Extract.Paired.first,Research.SharedForest.firstNodes];rfl)

theorem actual_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : level≤topLevel coord) (hc:c<2^(7-level)) :
    (Extract.Paired.nodes answers index.val coord.val).getD (2^(7-level)+c) 0=
      ftsLabel labels index coord level c := by
  rw [nodes_source]
  exact source_nodes_label answers labels h index coord _ (source_pads_label answers labels h index coord) level c hl hc

theorem actual_leaf_pad (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (raw : Fin 128) :
    Extract.Paired.pads answers index.val coord.val (Extract.Paired.physical coord.val raw.val/64)=
      pads labels index coord (raw.val%2) := by
  have hp:Extract.Paired.physical coord.val raw.val<128 :=
    Research.SharedForest.physicalChild_lt _ _ raw.isLt
  rw [source_pads_label answers labels h index coord _ (by omega),pads_raw_branch labels index coord _ hp]
  congr 1
  have he:rawLeaf coord.val (Extract.Paired.physical coord.val raw.val)=raw.val := by
    rw [←rawChild_eq]
    exact Research.SharedForest.raw_physical_child _ _ raw.isLt
  rw [he]
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open CanonGraph SigGolfCandidate.T3.Security.Wots SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Research.SharedForest.sharedNodes Research.SharedForest.firstNodes Research.SharedForest.secondNodes

theorem honestInput_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    Extract.Paired.honestInput answers node.toPos=cell (secretsOf answers) (node.sel labels) labels := by
  cases node with
  | chain p=>
      simp only [Node.sel,Node.toPos,Extract.Paired.honestInput,Extract.honestInput]
      change pad64 (rowW p (Wots.honestChainValueW answers _ _ _ _ (WCT9.wotsSeed answers _ _ _ _) _)) =
        rowW p (priorW _ p _)
      rw [chainValue_eq h p.1 p.2.val (by have := p.2.isLt; omega), rowW_pad64, priorW_eq_valueW]
  | leaf L=>
      simp only [Node.sel,Node.toPos,Extract.Paired.honestInput,Extract.honestInput,cell,CanonGraph.cell]
      rw [leafEnds_eq h L.1]
  | node n=>
      have hv1 : n.1.level.val < height n.1.lay := n.2.1
      have hv2 : n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) := n.2.2.1
      have hv3 : n.1.tree.val < 2 ^ treeBits n.1.lay := n.2.2.2.1
      have hpow : 2 ^ (height n.1.lay - n.1.level.val) = 2 * 2 ^ (height n.1.lay - n.1.level.val - 1) := by
        rw [← pow_succ']; congr 1; omega
      change Extract.honestInput answers (Node.node n).toPos =
        CanonGraph.cell (secretsOf answers) (.node (selNode labels n)) labels
      exact honestInput_node_sel (fun m => h (.node m)) n
        (builtTree_eq h _ _ _ _ (by omega) (by omega) hv3 (by omega))
        (builtTree_eq h _ _ _ _ (by omega) (by omega) hv3 (by omega))
  | wctChain p=>
      simp only [Node.sel,Node.toPos,Extract.Paired.honestInput,Extract.honestInput,cell,CanonGraph.cell]
      rw [wctValue_eq h p.1 p.2.val (by have:=p.2.isLt;omega),WCT9.ftsChainInputW_padded]
  | wctLeaf L=>
      simp only [Node.sel,Node.toPos,Extract.Paired.honestInput,cell]
      rw [wctEnds_eq h L,actual_leaf_pad answers labels h L.index L.coord L.child]
  | wctNode n=>
      obtain ⟨⟨index,coord,level,idx⟩,hv⟩:=n
      have hv':idx.val<2^(7-level.val-1):=hv
      have hl6:=level.isLt
      have ht:level.val≤topLevel coord := by
        unfold topLevel
        split_ifs with hf
        · have hused:=hb.2 (by change decide (first coord.val)=true;exact decide_eq_true hf)
          omega
        · omega
      have hpow:2^(7-level.val)=2*2^(6-level.val) := by
        rw [←pow_succ'];congr 1;omega
      have hsub:7-level.val-1=6-level.val := by omega
      rw [hsub] at hv'
      simp only [Node.sel,Node.toPos,Extract.Paired.honestInput,cell,hsub]
      change pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level.val)+idx.val)
        ((Extract.Paired.nodes answers index.val coord.val).getD (2*(2^(6-level.val)+idx.val)) 0)
        (if level.val=4 then (Extract.Paired.pads answers index.val coord.val ((2^(6-level.val)+idx.val)/2-2)).2 else 0)
        ((Extract.Paired.nodes answers index.val coord.val).getD (2*(2^(6-level.val)+idx.val)+1) 0))= _
      rw [show 2*(2^(6-level.val)+idx.val)=2^(7-level.val)+2*idx.val by omega,
        show 2^(7-level.val)+2*idx.val+1=2^(7-level.val)+(2*idx.val+1) by omega,
        actual_nodes_label answers labels h index coord level.val (2*idx.val) ht (by omega),
        actual_nodes_label answers labels h index coord level.val (2*idx.val+1) ht (by omega)]
      by_cases h4:level.val=4
      · rw [if_pos h4,h4]
        have hi:idx.val<4 := by simpa [h4] using hv'
        rw [show (2^(6-4)+idx.val)/2-2=idx.val/2 by norm_num;omega,
          source_pads_label answers labels h index coord _ (by omega),if_pos rfl]
      · rw [if_neg h4,if_neg h4]
  | forest index=>exact hb.elim

theorem honest_answer (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    answers (.inl (.inr (Extract.Paired.honestInput answers node.toPos)))=labels (node.sel labels) := by
  rw [honestInput_eq answers labels h node hb]
  exact h (node.sel labels)
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired

namespace ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open Correctness (Answers)
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def completeNonforest (answers : Answers) (labels : Labels) : Labels := fun node =>
  if Used node then labels node else answers (.inl (.inr (Paired.cell (secretsOf answers) node labels)))
noncomputable def completeLabels (answers : Answers) (labels : Labels) : Labels
  | .forest i => answers (.inl (.inr (Paired.cell (secretsOf answers) (.forest i) (completeNonforest answers labels))))
  | node => completeNonforest answers labels node

theorem completeNonforest_used (answers : Answers) (labels : Labels) (node : Node) (hu : Used node) :
    completeNonforest answers labels node=labels node := if_pos hu

theorem completeLabels_nonforest (answers : Answers) (labels : Labels) (node : Node)
    (hnf : ∀i,node≠.forest i) :
    completeLabels answers labels node=completeNonforest answers labels node := by
  cases node <;> first | rfl | exact (hnf _ rfl).elim

theorem completeLabels_used (answers : Answers) (labels : Labels) (node : Node) (hu : Used node) :
    completeLabels answers labels node=labels node := by
  rw [completeLabels_nonforest answers labels node (by intro i hi; subst node; exact hu)]
  exact completeNonforest_used answers labels node hu

theorem completeLabels_agrees {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    Paired.Agrees answers (completeLabels answers labels) := by
  intro node
  by_cases hnf : ∀i,node≠.forest i
  · have hc := cell_congr_nonforest (secretsOf answers) node hnf (completeLabels answers labels) labels
      (fun other hu _ => completeLabels_used answers labels other hu)
    rw [hc,completeLabels_nonforest answers labels node hnf]
    by_cases hu : Used node
    · rw [completeNonforest_used answers labels node hu]
      exact h node hu
    · simp only [completeNonforest, if_neg hu]
  · push_neg at hnf
    obtain ⟨i,hi⟩ := hnf
    subst node
    have hc : Paired.cell (secretsOf answers) (.forest i) (completeLabels answers labels) =
        Paired.cell (secretsOf answers) (.forest i) (completeNonforest answers labels) := by
      apply Paired.cell_congr
      intro other hd
      apply completeLabels_nonforest
      intro j hj
      subst other
      simp only [Node.depth,lt_self_iff_false] at hd
    change answers (.inl (.inr (Paired.cell _ _ _))) = answers (.inl (.inr (Paired.cell _ _ _)))
    rw [hc]

theorem sel_congr {left right : Labels} (h : ∀ m : TreeNode, left (.node m) = right (.node m)) (node : Node) :
    node.sel left = node.sel right := by
  cases node <;> try rfl
  exact congrArg Node.node (selNode_congr (fun j _ => h _))

theorem used_sel (labels : Labels) (node : Node) (hb : Extract.Paired.Bounded node.toPos) : Used (node.sel labels) :=
  (used_iff_bounded _).2 (by rw [toPos_sel]; exact hb)

theorem honestInput_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    Extract.Paired.honestInput answers node.toPos=Paired.cell (secretsOf answers) (node.sel labels) labels := by
  rw [Paired.honestInput_eq answers (completeLabels answers labels) (completeLabels_agrees h) node hb,
    sel_congr (fun m => completeLabels_used answers labels (.node m) trivial) node]
  exact cell_congr _ (node.sel labels) (used_sel labels node hb) _ _
    (fun other hu _ => completeLabels_used answers labels other hu)

theorem honest_answer (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    answers (.inl (.inr (Extract.Paired.honestInput answers node.toPos)))=labels (node.sel labels) := by
  rw [honestInput_eq answers labels h node hb]
  exact h (node.sel labels) (used_sel labels node hb)

theorem treeLabel_complete (answers : Answers) (labels : Labels)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel (completeLabels answers labels) lay tree level c=treeLabel labels lay tree level c :=
  treeLabel_congr _ _ _ _ _ _ (fun other hu _ => completeLabels_used answers labels other hu)

theorem ftsLabel_complete (answers : Answers) (labels : Labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hl : first coord.val → level≤5) :
    Paired.ftsLabel (completeLabels answers labels) index coord level c=Paired.ftsLabel labels index coord level c :=
  ftsLabel_congr _ _ _ _ _ _ hl (fun other hu _ => completeLabels_used answers labels other hu)

theorem honestPair_eq {answers : Answers} {labels : Labels} (h : Agrees answers labels)
    (lay : Layer) (tree : Fin (2^31)) (ht : tree.val<2^Extract.treeBits lay) :
    Extract.honestPair answers lay tree.val =
      (treeLabel labels lay tree (height lay-1) 0,treeLabel labels lay tree (height lay-1) 1) := by
  rw [Paired.honestPair_eq (completeLabels_agrees h) lay tree ht,
    treeLabel_complete,treeLabel_complete]

theorem actual_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : level≤Paired.topLevel coord) (hc : c<2^(7-level)) :
    (Extract.Paired.nodes answers index.val coord.val).getD (2^(7-level)+c) 0=
      Paired.ftsLabel labels index coord level c := by
  rw [Paired.actual_nodes_label answers (completeLabels answers labels) (completeLabels_agrees h) index coord level c hl hc]
  apply ftsLabel_complete
  intro hf
  unfold Paired.topLevel at hl
  rw [if_pos hf] at hl
  omega
end ClaudeWCT.W9.T3.Security.CanonGraph.Paired.Filtered
end
-- ==== merged from ClaudeWCT_W9_New_CanonTable_ChainTable ====
section

namespace ClaudeWCT.W9.CanonTable
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs
open ClaudeWCT.W9.T3.Security.CanonGraph
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem chainAddr_eq : Guess.ChainAddr = WctAddr := rfl
theorem gCoord_eq : Guess.GCoord = WctPoint := rfl
theorem cell_wctChain (secrets : Secrets) (labels : Labels) (p : WctPoint) :
    cell secrets (.wctChain p) labels = Guess.probeInput p.1 p.2 (wctValueL secrets labels p.1 p.2.val) := rfl
theorem probeInput_hdr (a : WctAddr) (p : Fin 4) (c : Digest) :
    Extract.hdrBlock (Guess.probeInput a p c) = bytesLE 16 (Node.toPos (.wctChain (a, p))).hdr :=
  Extract.hdrBlock_ftsChainInputW _ _ _ _ _ _
theorem probeInput_inj {a a' : WctAddr} {p p' : Fin 4} {c c' : Digest}
    (h : Guess.probeInput a p c = Guess.probeInput a' p' c') : a = a' ∧ p = p' ∧ c = c' := by
  have hh := probeInput_hdr a p c
  rw [h, probeInput_hdr] at hh
  have hn : (Node.wctChain (a', p') : Node) = .wctChain (a, p) :=
    toPos_injective_base (left := .wctChain (a', p')) (right := .wctChain (a, p))
      (Extract.Pos.hdr_injective (toPos_bounded _) (toPos_bounded _) rfl (bytesLE_injective hh))
  simp only [Node.wctChain.injEq, Prod.mk.injEq] at hn
  obtain ⟨rfl, rfl⟩ := hn
  refine ⟨rfl, rfl, ?_⟩
  exact (Guess.probeInput_injective h).2.2
theorem decodeProbe_probe (a : WctAddr) (p : Fin 4) (c : Digest) :
    Guess.decodeProbe (Guess.probeInput a p c) = some ((a, p), c) := by
  have h : ∃ q : Guess.GCoord × Digest, Guess.probeInput a p c = Guess.probeInput q.1.1 q.1.2 q.2 :=
    ⟨((a, p), c), rfl⟩
  delta Guess.decodeProbe
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := probeInput_inj (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext (Prod.ext h1 h2) h3)
theorem decodeProbe_none {x : HashInput} (h : Guess.decodeProbe x = none) (a : WctAddr) (p : Fin 4) (c : Digest) :
    x ≠ Guess.probeInput a p c := by
  intro hx
  rw [hx, decodeProbe_probe] at h
  cases h
theorem probeInput_mem (a : WctAddr) (p : Fin 4) (c : Digest) : Guess.probeInput a p c ∈ canonInputs := by
  obtain ⟨K, hK⟩ := ClaudeWCT.Arith.familyEval_surjective (n := 54) (t := 1) (by decide)
    (fun _ => WCT9.ftsPoint a.2.2.1.val a.2.2.2.val) (fun i j _ => Subsingleton.elim i j)
    (fun _ => Guess.Fam.ftsPoint_lt a.2.2.1 a.2.2.2) (fun _ => c)
  have hK0 := congrFun hK 0
  have h := cell_mem (fun i => match i with | .inl _ => c | .inr k => K k.2.2) (.wctChain (a, p))
    (fun N => presentEquiv N (ChainGraph.joinOutput c 0))
  have hv : wctValueL (fun i => match i with | .inl _ => c | .inr k => K k.2.2)
      (fun N => presentEquiv N (ChainGraph.joinOutput c 0)) a p.val = c := by
    unfold wctValueL
    split_ifs
    · exact hK0
    · exact projHalf_presentEquiv_wctChain (a, ⟨(p.val - 1) % 4, Nat.mod_lt _ (by decide)⟩) c 0
  rw [cell_wctChain, hv] at h
  exact h
theorem cell_ne_probe (secrets : Secrets) (labels : Labels) (node : Node) (hnode : ∀ q, node ≠ .wctChain q)
    (a : WctAddr) (p : Fin 4) (c : Digest) : cell secrets node labels ≠ Guess.probeInput a p c := by
  intro he
  by_cases hp : PhantomAt node labels
  · obtain ⟨n, rfl, hc⟩ := cell_of_phantomAt (secrets := secrets) hp
    have hl := congrArg List.length he
    rw [hc, phantom_length, Guess.probeInput_length] at hl
    exact absurd hl (by decide)
  have h1 := hdrBlock_cell secrets node labels hp
  have hl : node.toPos.len = (Node.wctChain (a, p)).toPos.len := by
    rw [← cell_length secrets node labels hp, he, Guess.probeInput_length]; rfl
  rw [he, probeInput_hdr] at h1
  have hb := toPos_injective_base (Extract.Pos.hdr_injective (toPos_bounded _) (toPos_bounded _) hl
    (bytesLE_injective h1).symm)
  cases node <;> first | exact hnode (a, p) hb | (simp [Node.base] at hb)
def Hidden (node : Node) : Prop := ∃ a : WctAddr, ∃ q : Fin 4, q.val < 3 ∧ node = .wctChain (a, q)
theorem treeLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L => simp only; rw [hn _ (fun _ => Node.noConfusion)]
  · cases treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n => simp only; rw [selNode_label_congr (fun j _ => hn _ (fun _ => Node.noConfusion))]
theorem ftsLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [hn _ (fun _ => Node.noConfusion)]
  · rfl
  all_goals
    cases ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n => simp only; rw [hn _ (fun _ => Node.noConfusion)]
theorem ftsPrevLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (index : Fin (2^31)) (coord : Fin 9) :
    ftsPrevLabel left index coord = ftsPrevLabel right index coord := by
  unfold ftsPrevLabel
  split_ifs
  · rfl
  · rw [ftsLabel_outer left right h, ftsLabel_outer left right h]
theorem cell_outer (secrets secrets' : Secrets) (labels labels' : Labels)
    (hs : ∀ a, secrets (.inl a) = secrets' (.inl a)) (hl : ∀ node, ¬Hidden node → labels node = labels' node)
    (node : Node) (hnode : ∀ q, node ≠ .wctChain q) :
    cell secrets node labels = cell secrets' node labels' := by
  have hseeds : seedsOf secrets = seedsOf secrets' := by
    have hf : leafFamily secrets = leafFamily secrets' :=
      funext fun lay => funext fun tree => funext fun leaf => funext fun j => hs _
    funext a
    unfold seedsOf
    rw [hf]
  have hchain : chainLabels labels = chainLabels labels' :=
    funext fun point => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he)
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels labels) =
        inputW (seedsOf secrets') p (chainLabels labels')
      rw [hseeds, hchain]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets labels L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets' labels' L.1) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel
        rw [hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he)]
      simp only [cell, hends]
  | node n =>
      have ha : Active labels n ↔ Active labels' n :=
        activeCongr labels labels' n (fun j _ => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he))
      simp only [cell, treeLabel_outer labels labels' hl, ha]
  | wctChain p => exact absurd rfl (hnode p)
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel labels' (L.index, L.coord, L.child, t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [hl _ (fun ⟨a, q, hq, he⟩ => by
          simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact absurd hq (by decide))]
      simp only [cell, hends, ftsPrevLabel_outer labels labels' hl]
  | wctNode n =>
      simp only [cell, ftsLabel_outer labels labels' hl, ftsPrevLabel_outer labels labels' hl]
  | forest index =>
      simp only [cell, ftsLabel_outer labels labels' hl]
def stepNode (c : WctAddr × Fin 3) : Node := .wctChain (c.1, ⟨c.2.val, by omega⟩)
def shiftCoord (c : WctAddr × Fin 3) : WctPoint := (c.1, ⟨c.2.val + 1, by omega⟩)
theorem stepNode_injective : Function.Injective stepNode := by
  rintro ⟨a, q⟩ ⟨a', q'⟩ h
  simp only [stepNode, Node.wctChain.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [Fin.ext h]
/-- Hidden parameter of the case-C world (campaign X1): FTS family coefficients and step-1..3 labels (T8). -/
abbrev HiddenF := (Guess.Fam.FamIdx → Guess.Fam.Coefs) × (Guess.Fam.LabelIdx → Digest)
/-- Coefficient secret `(index, coord, j)` of the hidden vectors `K`. -/
def coefOf (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (c : WctCoef) : Digest := K (c.1, c.2.1) c.2.2
theorem inr_injective : Function.Injective (Sum.inr : WctCoef → SecretIndex) := Sum.inr_injective
noncomputable def worldSecrets (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) : Secrets :=
  Function.extend Sum.inr (coefOf K) secrets
noncomputable def worldLow (low : LowLabels) (g12 : Guess.Fam.LabelIdx → Digest) : LowLabels :=
  Function.extend stepNode g12 low
structure Omega (U : Finset HashInput) where
  secrets : Secrets
  other : OtherHalves
  low : LowLabels
  high : LowLabels
  residual : U → HashOutput
variable {U : Finset HashInput} (hU : canonInputs ⊆ U)
noncomputable def worldLabels (ω : Omega U) (g12 : Guess.Fam.LabelIdx → Digest) : Labels :=
  joinLabels (worldLow ω.low g12) ω.high
noncomputable def worldAnswers (ω : Omega U) (h : HiddenF) : Answers :=
  eagerAnswers (privateEquiv.symm (worldSecrets ω.secrets h.1, ω.other)) U
    (programmed U hU (worldSecrets ω.secrets h.1) (worldLabels ω h.2) ω.residual)
theorem worldSecrets_inr (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (c : WctCoef) :
    worldSecrets secrets K (.inr c) = coefOf K c :=
  inr_injective.extend_apply _ _ c
theorem wctFamily_worldSecrets (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (i : Fin (2 ^ 31))
    (k : Fin 9) : wctFamily (worldSecrets secrets K) i k = K (i, k) := by
  funext j
  exact worldSecrets_inr secrets K (i, k, j)
theorem worldSecrets_inl (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (a : ChainGraph.Address) :
    worldSecrets secrets K (.inl a) = secrets (.inl a) := by
  unfold worldSecrets
  rw [Function.extend_apply']
  rintro ⟨b, hb⟩
  cases hb
theorem worldLabels_step (ω : Omega U) (g12 : Guess.Fam.LabelIdx → Digest) (a : WctAddr) (q : Fin 4)
    (hq : q.val < 3) :
    worldLabels ω g12 (.wctChain (a, q)) =
      presentEquiv (.wctChain (a, q)) (ChainGraph.joinOutput (g12 (a, ⟨q.val, hq⟩)) (ω.high (.wctChain (a, q)))) := by
  have hs : stepNode (a, ⟨q.val, hq⟩) = .wctChain (a, q) := rfl
  unfold worldLabels joinLabels worldLow
  rw [← hs, stepNode_injective.extend_apply]
theorem worldLabels_outer (ω : Omega U) (g12 : Guess.Fam.LabelIdx → Digest) (node : Node) (hnode : ¬Hidden node) :
    worldLabels ω g12 node = joinLabels ω.low ω.high node := by
  unfold worldLabels joinLabels worldLow
  rw [Function.extend_apply']
  rintro ⟨⟨a, q⟩, hc⟩
  exact hnode ⟨a, ⟨q.val, by omega⟩, q.isLt, hc.symm⟩
theorem not_hidden_top (a : WctAddr) : ¬Hidden (.wctChain (a, 3)) := by
  rintro ⟨b, q, hq, he⟩
  simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact absurd hq (by decide)
/-- The world's chain values are the family table `phi`. -/
theorem worldValueL (ω : Omega U) (h : HiddenF) (p : WctPoint) :
    wctValueL (worldSecrets ω.secrets h.1) (worldLabels ω h.2) p.1 p.2.val = Guess.Fam.phi h.1 h.2 p := by
  obtain ⟨a, ⟨s, hs⟩⟩ := p
  show wctValueL (worldSecrets ω.secrets h.1) (worldLabels ω h.2) a s = Guess.Fam.phi h.1 h.2 (a, ⟨s, hs⟩)
  unfold wctValueL
  split_ifs with h0
  · subst h0
    unfold wctSeedsOf
    rw [wctFamily_worldSecrets]
    rfl
  · have hq : (s - 1) % 4 < 3 := by omega
    rw [worldLabels_step ω h.2 a ⟨(s - 1) % 4, Nat.mod_lt _ (by decide)⟩ hq]
    rw [projHalf_presentEquiv_wctChain (a, ⟨(s - 1) % 4, Nat.mod_lt _ (by decide)⟩)]
    have hne : (⟨s, hs⟩ : Fin 4) ≠ 0 := fun he => h0 (congrArg Fin.val he)
    rw [Guess.Fam.phi_label' _ _ (a, ⟨s, hs⟩) hne]
    apply congrArg h.2
    refine Prod.ext rfl (Fin.ext ?_)
    rw [Fin.coe_pred]
    show (s - 1) % 4 = s - 1
    omega
theorem worldAnswers_public (ω : Omega U) (h : HiddenF) (x : HashInput) (hx : x ∈ U) :
    worldAnswers hU ω h (.inl (.inr x)) =
      programmed U hU (worldSecrets ω.secrets h.1) (worldLabels ω h.2) ω.residual ⟨x, hx⟩ :=
  eagerAnswers_mem _ U _ ⟨x, hx⟩
theorem programmed_outer (ω : Omega U) (h : HiddenF) (x : HashInput) (hx : x ∈ U)
    (hprobe : Guess.decodeProbe x = none) :
    programmed U hU (worldSecrets ω.secrets h.1) (worldLabels ω h.2) ω.residual ⟨x, hx⟩ =
      programmed U hU ω.secrets (joinLabels ω.low ω.high) ω.residual ⟨x, hx⟩ := by
  have hnot : ∀ (secrets : Secrets) (labels : Labels) (q : WctPoint), x ≠ cell secrets (.wctChain q) labels :=
    fun secrets labels q he => decodeProbe_none hprobe q.1 q.2 _ (he.trans (cell_wctChain secrets labels q))
  have hs : ∀ a, worldSecrets ω.secrets h.1 (.inl a) = ω.secrets (.inl a) := worldSecrets_inl ω.secrets h.1
  have hl : ∀ node, ¬Hidden node → worldLabels ω h.2 node = joinLabels ω.low ω.high node :=
    worldLabels_outer ω h.2
  have hcell : ∀ node, (∀ q, node ≠ .wctChain q) →
      cell (worldSecrets ω.secrets h.1) node (worldLabels ω h.2) = cell ω.secrets node (joinLabels ω.low ω.high) :=
    cell_outer _ _ _ _ hs hl
  by_cases hex : ∃ node, x = cell ω.secrets node (joinLabels ω.low ω.high)
  · obtain ⟨node, hnode⟩ := hex
    have hq : ∀ q, node ≠ .wctChain q := by
      rintro q rfl
      exact hnot _ _ q hnode
    have h1 : (⟨x, hx⟩ : U) = cellIn U hU (worldSecrets ω.secrets h.1) node (worldLabels ω h.2) :=
      Subtype.ext (hnode.trans (hcell node hq).symm)
    have h2 : (⟨x, hx⟩ : U) = cellIn U hU ω.secrets node (joinLabels ω.low ω.high) := Subtype.ext hnode
    rw [h1, programmed_at, ← h1, h2, programmed_at]
    exact hl node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  · push Not at hex
    rw [programmed_other U hU _ _ _ _ (fun node he => ?_), programmed_other U hU _ _ _ _ (fun node he => hex node he)]
    by_cases hq : ∀ q, node ≠ .wctChain q
    · exact hex node (he.trans (hcell node hq))
    · push Not at hq
      obtain ⟨q, rfl⟩ := hq
      exact hnot _ _ q he
theorem seedOf_worldAnswers (ω : Omega U) (h : HiddenF) (a : WctAddr) :
    Guess.seedOf (worldAnswers hU ω h) a = Guess.Fam.phi h.1 h.2 (a, 0) := by
  have hc : WCT9.ftsCoef (worldAnswers hU ω h) a.1.val a.2.1.val = h.1 (a.1, a.2.1) := by
    funext j
    rw [← secretsOf_coef (worldAnswers hU ω h) (a.1, a.2.1, j)]
    unfold worldAnswers
    rw [secretsOf_eager, privateSecrets_symm, worldSecrets_inr]
    rfl
  unfold Guess.seedOf
  rw [hc]
  rfl
noncomputable def chainTable (ω : Omega U) : Guess.ChainTable HiddenF where
  answers := worldAnswers hU ω
  view h := Guess.Fam.phi h.1 h.2
  base := 0
  step a p v := presentEquiv (.wctChain (a, p)) (ChainGraph.joinOutput v (ω.high (.wctChain (a, p))))
  top a := joinLabels ω.low ω.high (.wctChain (a, 3))
  miss x := SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual x
  answers_probe := by
    intro h a p c
    have hmem : Guess.probeInput a p c ∈ U := hU (probeInput_mem a p c)
    rw [worldAnswers_public hU ω h _ hmem]
    unfold Guess.probeAnswer
    by_cases hc : Guess.Fam.phi h.1 h.2 (a, p) = c
    · rw [if_pos hc]
      have hx : (⟨Guess.probeInput a p c, hmem⟩ : U) =
          cellIn U hU (worldSecrets ω.secrets h.1) (.wctChain (a, p)) (worldLabels ω h.2) := by
        apply Subtype.ext
        change Guess.probeInput a p c = cell _ (.wctChain (a, p)) _
        rw [cell_wctChain]
        exact congrArg _ ((worldValueL ω h (a, p)).trans hc).symm
      rw [hx, programmed_at]
      unfold Guess.succPos
      split_ifs with hp
      · simp only
        rw [worldLabels_step ω h.2 a p (by omega)]
        have hne : (⟨p.val + 1, hp⟩ : Fin 4) ≠ 0 := fun he => by simpa using congrArg Fin.val he
        rw [Guess.Fam.phi_label' _ _ (a, ⟨p.val + 1, hp⟩) hne]
        congr 3
      · simp only
        have hp2 : p = 3 := Fin.ext (by have := p.isLt; omega)
        subst hp2
        exact worldLabels_outer ω h.2 _ (not_hidden_top a)
    · rw [if_neg hc]
      rw [programmed_other U hU _ _ _ _ (fun node he => ?_)]
      · exact (SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U ω.residual _ hmem rfl).symm
      · by_cases hq : ∀ q, node ≠ .wctChain q
        · exact cell_ne_probe _ _ node hq a p c he.symm
        · push Not at hq
          obtain ⟨q, rfl⟩ := hq
          change Guess.probeInput a p c = cell _ (.wctChain q) _ at he
          rw [cell_wctChain, worldValueL] at he
          obtain ⟨h1, h2, h3⟩ := probeInput_inj he
          subst h1 h2
          exact hc h3.symm
  answers_public := by
    intro h h' x hx
    by_cases hU' : x ∈ U
    · rw [worldAnswers_public hU ω h x hU', worldAnswers_public hU ω h' x hU',
        programmed_outer hU ω h x hU' hx, programmed_outer hU ω h' x hU' hx]
    · change SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ x
      unfold SphincsSecurity.Concrete.finiteHashAnswer
      rw [dif_neg hU', dif_neg hU']
  step_low a p v := projHalf_presentEquiv_wctChain (a, p) v _
  seed := seedOf_worldAnswers hU ω
theorem worldAnswers_agrees (ω : Omega U) (h : HiddenF) :
    Agrees (worldAnswers hU ω h) (worldLabels ω h.2) :=
  eager_programmed_agrees U hU _ _ _ _
/-- The hidden values carried by `ω` itself. -/
def trueHidden (ω : Omega U) : HiddenF :=
  (fun f j => ω.secrets (.inr (f.1, f.2, j)), fun l => ω.low (stepNode l))
theorem worldSecrets_true (ω : Omega U) : worldSecrets ω.secrets (trueHidden ω).1 = ω.secrets := by
  funext i
  cases i with
  | inl a => exact worldSecrets_inl _ _ a
  | inr c => rw [worldSecrets_inr]; rfl
theorem worldLow_true (ω : Omega U) : worldLow ω.low (trueHidden ω).2 = ω.low := by
  funext node
  unfold worldLow
  by_cases hn : ∃ c, stepNode c = node
  · obtain ⟨c, rfl⟩ := hn
    rw [stepNode_injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hn]
theorem worldAnswers_true (ω : Omega U) :
    worldAnswers hU ω (trueHidden ω) =
      eagerAnswers (privateEquiv.symm (ω.secrets, ω.other)) U
        (programmed U hU ω.secrets (joinLabels ω.low ω.high) ω.residual) := by
  unfold worldAnswers worldLabels
  rw [worldSecrets_true, worldLow_true]
theorem chainTable_answers (ω : Omega U) : (chainTable hU ω).answers = worldAnswers hU ω := rfl
theorem chainTable_view (ω : Omega U) (h : HiddenF) : (chainTable hU ω).view h = Guess.Fam.phi h.1 h.2 := rfl
end ClaudeWCT.W9.CanonTable
end
-- ==== merged from T3M_Final_Relabel ====
section

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec privateInput realize realHandler Coordinate)
abbrev AHash := List UInt8 →ₒ BitVec 256
abbrev AW := unifSpec + AHash
def hHandler (sk : BitVec 256) : QueryImpl Spec (OracleComp AHash)
  | .inl (.inl n) => (Pure.pure (0 : Fin (n + 1)) : OracleComp AHash (Fin (n + 1)))
  | .inl (.inr input) => (AHash.query input : OracleComp AHash _)
  | .inr c => (AHash.query (privateInput sk c) : OracleComp AHash _)
def hrealize {α : Type} (sk : BitVec 256) (p : M α) : OracleComp AHash α :=
  simulateQ (hHandler sk) p
section basic
variable {α β : Type} (sk : BitVec 256)
@[simp] theorem hrealize_pure (a : α) : hrealize sk (Pure.pure a : M α) = Pure.pure a := rfl
theorem hrealize_bind (p : M α) (f : α → M β) :
    hrealize sk (p >>= f) = hrealize sk p >>= fun a => hrealize sk (f a) := by
  simp only [hrealize, simulateQ_bind]
theorem hrealize_map (f : α → β) (p : M α) : hrealize sk (f <$> p) = f <$> hrealize sk p := by
  simp only [hrealize, simulateQ_map]
theorem hrealize_query_bind (q : Spec.Domain) (k : Spec.Range q → M α) :
    hrealize sk ((liftM (Spec.query q) : M _) >>= k) = hHandler sk q >>= fun a => hrealize sk (k a) := by
  rw [hrealize_bind]
  congr 1
  simp [hrealize]
end basic
theorem mrealize_eq_relabel {α : Type} (sk : BitVec 256) (p : M α) :
    mrealize sk p = relabel toQ (hrealize sk p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [mrealize_bind, hrealize_query_bind, relabel_bind]
    have hq : mrealize sk (liftM (Spec.query q) : M _) = relabel toQ (hHandler sk q) := by
      rcases q with (n | input) | c
      · rfl
      · have e1 : mrealize sk (liftM (Spec.query (.inl (.inr input))) : M _) =
            (liftM (OracleSpec.query (spec := Legacy.HashSpec) (toQ input)) : OracleComp Legacy.HashSpec _) := by
          simp [mrealize, machineHandler]; exact id_map _
        exact e1.trans (relabel_query toQ input).symm
      · have e1 : mrealize sk (liftM (Spec.query (.inr c)) : M _) =
            (liftM (OracleSpec.query (spec := Legacy.HashSpec) (toQ (privateInput sk c))) :
              OracleComp Legacy.HashSpec _) := by
          simp [mrealize, machineHandler]
        exact e1.trans (relabel_query toQ (privateInput sk c)).symm
    rw [hq]
    exact bind_congr fun a => ih a
theorem relabel_ofQ_toQ {α : Type} {X : OracleComp AHash α} (h : AllQ Aligned X) :
    relabel ofQ (relabel toQ X) = X := by
  rw [relabel_relabel]
  exact relabel_eq_self_of_allQ Aligned _ (fun x hx => ofQ_toQ hx) h
theorem allQ_hrealize {α : Type} (sk : BitVec 256) {p : M α}
    (h : AllQueriesSatisfy p T3.Cost.GoodQuery) : AllQ Aligned (hrealize sk p) := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [hrealize_query_bind]
    rcases q with (n | input) | c
    · exact ih _ (h.2 _)
    · refine SigGolfCandidate.Bridge.allQ_bind Aligned ((allQ_query Aligned input).mpr ?_) fun a => ih a (h.2 a)
      exact h.1
    · exact SigGolfCandidate.Bridge.allQ_bind Aligned ((allQ_query Aligned _).mpr (privateInput_aligned sk c))
        fun a => ih a (h.2 a)
theorem realize_eq_liftM {α : Type} (sk : BitVec 256) {p : M α} (h : AllQueriesSatisfy p isHash) :
    @Eq (OracleComp AW α) (realize sk p) (liftM (hrealize sk p)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [hrealize_query_bind, liftM_bind]
    simp only [realize, simulateQ_bind, simulateQ_spec_query]
    rcases q with (n | input) | c
    · exact h.1.elim
    · exact bind_congr fun a => ih a (h.2 a)
    · exact bind_congr fun a => ih a (h.2 a)
theorem hrealize_public {α : Type} (sk sk' : BitVec 256) {p : M α} (h : AllQueriesSatisfy p isPublic) :
    hrealize sk p = hrealize sk' p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [hrealize_query_bind, hrealize_query_bind]
    rcases q with (n | input) | c
    · exact h.1.elim
    · exact bind_congr fun a => ih a (h.2 a)
    · exact h.1.elim
theorem mrealize_public {α : Type} (sk sk' : BitVec 256) {p : M α} (h : AllQueriesSatisfy p isPublic) :
    mrealize sk p = mrealize sk' p := by
  rw [mrealize_eq_relabel, mrealize_eq_relabel, hrealize_public sk sk' h]
theorem countCalls_eq {α : Type} (X : OracleComp Legacy.HashSpec α) :
    countCalls X = Bridge.countCalls X := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [countCalls_bind, countCalls_query]
    unfold Bridge.countCalls
    rw [countFrom_query_bind]
    simp only [bind_map_left]
    refine bind_congr fun a => ?_
    rw [ih a, Bridge.countCalls, countFrom_shift _ _ (0 + 1)]
end SigGolfCandidate.T3M.Final
end
-- ==== merged from T3M_Final_RO ====
section

open OracleSpec OracleComp SigGolfCandidate.Bridge
namespace SigGolfCandidate.T3M.Final
section relabel
variable {ι ι' R : Type} [DecidableEq ι] [DecidableEq ι'] [SampleableType R]
theorem run'_relabel_on (enc : ι' → ι) (S : Set ι') (henc : Set.InjOn enc S) {α : Type}
    (P : OracleComp (ι' →ₒ R) α) (hP : AllQ (· ∈ S) P)
    (cO : QueryCache (ι' →ₒ R)) (cA : QueryCache (ι →ₒ R)) (hc : ∀ x ∈ S, cO x = cA (enc x)) :
    (simulateQ randomOracle P).run' cO = (simulateQ randomOracle (relabel enc P)).run' cA := by
  induction P using OracleComp.inductionOn generalizing cO cA with
  | pure x => rfl
  | query_bind x k ih =>
    rw [allQ_query_bind] at hP
    obtain ⟨hxS, hk⟩ := hP
    rw [relabel_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rw [randomOracle.run_eq, randomOracle.run_eq]
    have hx := hc x hxS
    have hrel : ∀ u, ∀ y ∈ S, (cO.cacheQuery x u) y = (cA.cacheQuery (enc x) u) (enc y) := by
      intro u y hy
      by_cases hyx : y = x
      · subst hyx; simp [QueryCache.cacheQuery_self]
      · rw [QueryCache.cacheQuery_of_ne _ _ hyx,
          QueryCache.cacheQuery_of_ne _ _ (fun h => hyx (henc hy hxS h))]
        exact hc y hy
    revert hx
    cases cO x <;> cases cA (enc x) <;> intro hx <;> simp at hx
    · simp only [bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      have := ih u (hk u) _ _ (hrel u)
      simpa [StateT.run'_eq] using this
    · subst hx
      simp only [pure_bind]
      rename_i u
      have := ih u (hk u) cO cA hc
      simpa [StateT.run'_eq] using this
end relabel
section congr
theorem allQ_mono {ι R α : Type} {P Q : ι → Prop} (h : ∀ x, P x → Q x) :
    ∀ {p : OracleComp (ι →ₒ R) α}, AllQ P p → AllQ Q p := by
  intro p hp
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [allQ_query_bind] at hp ⊢
    exact ⟨h t hp.1, fun u => ih u (hp.2 u)⟩
theorem finite_query_domain {D R α : Type} [DecidableEq D] [Fintype R] (p : OracleComp (D →ₒ R) α) :
    ∃ s : Finset D, AllQ (· ∈ s) p := by
  classical
  induction p using OracleComp.inductionOn with
  | pure a => exact ⟨∅, trivial⟩
  | query_bind t k ih =>
    choose sets hsets using ih
    refine ⟨insert t (Finset.univ.biUnion sets), ?_⟩
    rw [allQ_query_bind]
    refine ⟨Finset.mem_insert_self _ _, fun u => ?_⟩
    exact allQ_mono (fun y hy => Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hy⟩))
      (hsets u)
theorem evalWithAnswerFn_relabel {ι ι' R : Type} (e : ι → ι') (h : QueryImpl (ι' →ₒ R) Id) {α : Type}
    (P : OracleComp (ι →ₒ R) α) :
    evalWithAnswerFn h (relabel e P) = evalWithAnswerFn (fun x => h (e x) : QueryImpl (ι →ₒ R) Id) P := by
  induction P using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind x k ih =>
    rw [relabel_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
    have e1 : evalWithAnswerFn h (((ι' →ₒ R).query (e x) : OracleComp (ι' →ₒ R) R)) = h (e x) :=
      evalWithAnswerFn_query h (e x)
    have e2 : evalWithAnswerFn (fun x => h (e x) : QueryImpl (ι →ₒ R) Id)
        (((ι →ₒ R).query x : OracleComp (ι →ₒ R) R)) = h (e x) :=
      evalWithAnswerFn_query _ x
    rw [e1, e2, ih]
theorem randomOracle_congr {D R α : Type} [DecidableEq D] [Fintype R] [Nonempty R] [SampleableType R]
    (p q : OracleComp (D →ₒ R) α)
    (h : ∀ hash : QueryImpl (D →ₒ R) Id, evalWithAnswerFn hash p = evalWithAnswerFn hash q) :
    𝒮[(simulateQ randomOracle p).run' ∅] = 𝒮[(simulateQ randomOracle q).run' ∅] := by
  classical
  obtain ⟨sp, hp⟩ := finite_query_domain p
  obtain ⟨sq, hq⟩ := finite_query_domain q
  let s := sp ∪ sq
  let enc : D → Option {x : D // x ∈ s} := fun x => if hx : x ∈ s then some ⟨x, hx⟩ else none
  have hi : Set.InjOn enc {x | x ∈ s} := by
    intro x hx y hy he
    change x ∈ s at hx
    change y ∈ s at hy
    simp only [enc, dif_pos hx, dif_pos hy] at he
    exact congrArg Subtype.val (Option.some.inj he)
  have hp' : AllQ (· ∈ {x | x ∈ s}) p :=
    allQ_mono (fun _ hx => Finset.mem_union_left _ hx) hp
  have hq' : AllQ (· ∈ {x | x ∈ s}) q :=
    allQ_mono (fun _ hx => Finset.mem_union_right _ hx) hq
  rw [run'_relabel_on enc _ hi p hp' ∅ ∅ (fun _ _ => rfl), run'_relabel_on enc _ hi q hq' ∅ ∅ (fun _ _ => rfl),
    evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable,
    evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable]
  congr 1
  refine bind_congr fun g => ?_
  rw [evalWithAnswerFn_relabel, evalWithAnswerFn_relabel, h]
theorem probEvent_congr_evalSPMF {α : Type} {X Y : ProbComp α} (h : 𝒮[X] = 𝒮[Y]) (E : α → Prop) :
    Pr[E | X] = Pr[E | Y] := by
  unfold probEvent; rw [h]
theorem probOutput_congr_evalSPMF {α : Type} {X Y : ProbComp α} (h : 𝒮[X] = 𝒮[Y]) (a : α) :
    Pr[= a | X] = Pr[= a | Y] := by
  unfold probOutput; rw [h]
theorem expectedValue_congr_evalSPMF {α : Type} {X Y : ProbComp α} (h : 𝒮[X] = 𝒮[Y])
    (g : α → ENNReal) : OracleComp.EvalDist.expectedValue X g = OracleComp.EvalDist.expectedValue Y g := by
  unfold OracleComp.EvalDist.expectedValue
  simp only [probOutput_congr_evalSPMF h]
end congr
section fold
variable {ι κ : Type} {spec : OracleSpec ι}
def foldAll (L : List κ) (P : κ → OracleComp spec Bool) (b : Bool) : OracleComp spec Bool :=
  L.foldlM (fun b k => (b && ·) <$> P k) b
@[simp] theorem foldAll_nil (P : κ → OracleComp spec Bool) (b : Bool) :
    foldAll [] P b = pure b := rfl
theorem foldAll_cons (k : κ) (L : List κ) (P : κ → OracleComp spec Bool) (b : Bool) :
    foldAll (k :: L) P b = P k >>= fun c => foldAll L P (b && c) := by
  simp [foldAll, List.foldlM_cons]
theorem evalWithAnswerFn_foldAll (h : QueryImpl spec Id) (L : List κ)
    (P : κ → OracleComp spec Bool) (b : Bool) :
    evalWithAnswerFn h (foldAll L P b) = (b && L.all fun k => evalWithAnswerFn h (P k)) := by
  induction L generalizing b with
  | nil => simp [foldAll_nil]
  | cons k L ih =>
    rw [foldAll_cons, evalWithAnswerFn_bind, ih]
    simp [Bool.and_assoc]
end fold
end SigGolfCandidate.T3M.Final
end
-- ==== merged from T3M_Final_Pipeline ====
section

open OracleComp OracleSpec
namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.Legacy
variable (sub : Submission)
def successPipe (sk : SecretKey) (m : Message) : OracleComp HashSpec Bool := do
  match (← (fun r => r.value) <$> sub.run .keygen sk) with
  | none => pure false
  | some (pk, cache) =>
    match (← (fun r => r.value) <$> sub.run .sign (sk, cache, m)) with
    | none => pure false
    | some σ =>
      match (← (fun r => r.value) <$> sub.run .expand (m, pk, σ)) with
      | none => pure false
      | some w => (fun r => r.value.isSome) <$> sub.run .verify (m, pk, w)
theorem success_honest_eq (sk : SecretKey) (m : Message) :
    HonestResult.success <$> sub.honest sk m = successPipe sub sk m := by
  unfold Submission.honest successPipe
  simp only [map_bind, bind_map_left]
  refine bind_congr fun k => ?_
  rcases k.value with _ | ⟨pk, cache⟩
  · simp
  simp only [map_bind]
  refine bind_congr fun s => ?_
  rcases s.value with _ | σ
  · simp
  simp only [map_bind]
  refine bind_congr fun e => ?_
  rcases e.value with _ | w
  · simp
  simp
theorem honest_success_verify (hash : Hash) (sk : SecretKey) (m : Message)
    (h : (evalWithAnswerFn hash (sub.honest sk m)).success = true) :
    ∃ input : Input sub.sizes .verify,
      (sub.runWith hash .verify input).value.isSome = true ∧
      (evalWithAnswerFn hash (sub.honest sk m)).verificationCycles =
        (sub.runWith hash .verify input).cycles + witnessCycles sub.sizes.witness := by
  unfold Submission.honest at h ⊢
  simp only [evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k at h ⊢
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [hk] at h
  simp only [hk, evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s at h ⊢
  rcases hs : s.value with _ | σ
  · simp [hs] at h
  simp only [hs, evalWithAnswerFn_bind] at h ⊢
  generalize he : evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e at h ⊢
  rcases he' : e.value with _ | w
  · simp [he'] at h
  simp only [he', evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h ⊢
  exact ⟨(m, pk, w), h, rfl⟩
theorem eval_costs_keygen (hash : Hash) (sk : SecretKey) (m : Message) :
    (evalWithAnswerFn hash (sub.honest sk m)).costs .keygen = (sub.runWith hash .keygen sk).hashCompressions := by
  unfold Submission.honest Submission.runWith
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s
  rcases hs : s.value with _ | σ
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e
  rcases he : e.value with _ | w
  · simp [recordCost]
  simp [recordCost]
theorem eval_costs_sign (hash : Hash) (sk : SecretKey) (m : Message) :
    (evalWithAnswerFn hash (sub.honest sk m)).costs .sign =
      match (sub.runWith hash .keygen sk).value with
      | none => 0
      | some (_, cache) => (sub.runWith hash .sign (sk, cache, m)).hashCompressions := by
  unfold Submission.honest Submission.runWith
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s
  rcases hs : s.value with _ | σ
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e
  rcases he : e.value with _ | w
  · simp [recordCost]
  simp [recordCost]
theorem eval_costs_expand (hash : Hash) (sk : SecretKey) (m : Message) :
    (evalWithAnswerFn hash (sub.honest sk m)).costs .expand =
      match (sub.runWith hash .keygen sk).value with
      | none => 0
      | some (pk, cache) =>
        match (sub.runWith hash .sign (sk, cache, m)).value with
        | none => 0
        | some σ => (sub.runWith hash .expand (m, pk, σ)).hashCompressions := by
  unfold Submission.honest Submission.runWith
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s
  rcases hs : s.value with _ | σ
  · simp [recordCost]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e
  rcases he : e.value with _ | w
  · simp [recordCost]
  simp [recordCost]
end SigGolfCandidate.T3M.Final
end
-- ==== merged from T3M_Final_Source ====
section

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec
open SigGolfCandidate.T3 (M Message Digest Signature Cache Witness keygen sign expand verify)
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgramCore message
    pure (accepted && result)) true
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  T3.Cost.countBlocks (sign keys.2 message)
def jointCounts {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ))
    (expander : κ → σ → M ω) : M (Nat × Nat) := do
  let keys ← initial
  let signed ← T3.Cost.countBlocks (signer keys)
  match signed.1 with
  | none => pure (signed.2, 0)
  | some sig =>
      let expanded ← T3.Cost.countBlocks (expander keys sig)
      pure (signed.2, expanded.2)
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
end SigGolfCandidate.T3M.Final
end
-- ==== merged from ClaudeWCT_W9_New_F1a_Clean ====
section

set_option Elab.async false
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal OracleComp.EvalDist
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize privateInput)
open SigGolfCandidate.T3.Security (forwardWorld)
open SphincsSecurity (OracleWorld)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
theorem calls_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)}
    {X : OracleComp HashSpec γ} {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) :
    (fun r => (r.value, r.hashCalls)) <$> run = (fun p => (F p.1, p.2)) <$> SigGolfCandidate.Bridge.countCalls X := by
  have h2 := congrArg (fun x => (fun t : Option β × Nat × Nat => (t.1, t.2.1)) <$> x) h
  simp only [Functor.map_map] at h2
  rw [h2, ← countCalls_eq, ← countBoth_calls, Functor.map_map]
theorem ofQ_countCalls {α : Type} {X : OracleComp AHash α} (h : AllQ Aligned X) :
    relabel ofQ (SigGolfCandidate.Bridge.countCalls (relabel toQ X)) = SigGolfCandidate.Bridge.countCalls X := by
  rw [relabel_countCalls, relabel_ofQ_toQ h]
def costW : AW.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1
theorem countHashQueries_eq {α : Type} (X : OracleComp SphincsSecurity.OracleWorld α) :
    SphincsSecurity.countHashQueries X = countFrom costW X 0 := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [SphincsSecurity.countHashQueries_query_bind, countFrom_query_bind]
    refine bind_congr fun u => ?_
    rw [ih u, countFrom_shift _ _ (0 + costW t)]
    rcases t with n | x <;> simp [costW]
theorem derivation_realize {α : Type} (secret : BitVec 256) (p : M α) :
    SigGolfCandidate.T3.Derivation.realize (privateInput secret) p = realize secret p := by
  unfold SigGolfCandidate.T3.Derivation.realize realize
  congr 1
  funext q
  rcases q with q | c <;> rfl
theorem sampleSecretKey_eq : (sampleSecretKey : ProbComp SecretKey) = SphincsSecurity.sampleMasterSeed := rfl
lemma relabel_ofQ_countCalls {α : Type} (X : OracleComp AHash α) (hX : AllQ Aligned X) :
    relabel ofQ (SigGolfCandidate.Bridge.countCalls (relabel toQ X)) = SigGolfCandidate.Bridge.countCalls X :=
  ofQ_countCalls hX
lemma relabelW_liftM_proj {α β γ : Type} (Y : OracleComp HashSpec α) (proj : α → β)
    (K' : β → OracleComp World γ) (K : α → OracleComp World γ) (hK : ∀ r, K r = K' (proj r)) :
    relabelW ofQ ((liftM Y : OracleComp World α) >>= K) =
      (liftM (relabel ofQ (proj <$> Y)) : OracleComp AW β) >>= fun p => relabelW ofQ (K' p) := by
  rw [relabelW_bind, relabelW_liftM_hash, relabel_map, liftM_map, bind_map_left]
  simp only [hK]
lemma bind_eq_of_proj {ι : Type} {spec : OracleSpec ι} {α β γ : Type} (Y : OracleComp spec α)
    (proj : α → β) (K' : β → OracleComp spec γ) (K : α → OracleComp spec γ)
    (hK : ∀ r, K r = K' (proj r)) : Y >>= K = (proj <$> Y) >>= K' := by
  rw [bind_map_left]; exact bind_congr hK
lemma liftM_map_bind {ι : Type} {spec : OracleSpec ι} {α β γ : Type} (X : OracleComp spec α)
    (f : α → β) (K : β → OracleComp (unifSpec + spec) γ) :
    (liftM (f <$> X) : OracleComp (unifSpec + spec) β) >>= K =
      (liftM X : OracleComp (unifSpec + spec) α) >>= fun x => K (f x) := by
  rw [liftM_map, bind_map_left]
def recordVC {sizes : Sizes} (T : Transcript sizes) (message : Message)
    (value : Option (Bytes sizes.signature)) (calls : ℕ) : Transcript sizes :=
  { signed := match value with
      | none => T.signed
      | some signature => (message, signature) :: T.signed
    signingRequests := T.signingRequests + 1
    hashCalls := T.hashCalls + calls }
lemma record_eq_recordVC {sizes : Sizes} (T : Transcript sizes) (message : Message)
    (r : RunResult (Bytes sizes.signature)) :
    T.record message r = recordVC T message r.value r.hashCalls := rfl
lemma ofQ_injective : Function.Injective ofQ := fun x y h => by
  rw [← toQ_ofQ x, ← toQ_ofQ y, h]
theorem realize_pure' {α : Type} (secret : SecretKey) (a : α) :
    realize secret (pure a : M α) = pure a := rfl
theorem realize_forward_bind {α : Type} (secret : SecretKey) (t : OracleWorld.Domain)
    (g : OracleWorld.Range t → M α) :
    realize secret ((forwardWorld t : M _) >>= g) =
      (liftM (OracleWorld.query t) : OracleComp OracleWorld _) >>= fun a => realize secret (g a) := by
  simp only [realize, simulateQ_bind, forwardWorld, simulateQ_spec_query]
  rfl
def RFin (r : AttackResult) (b : Bool × ℕ) : Prop :=
  r.won = true → b.1 = true ∧ b.2 = r.hashCalls
lemma rfin_false (h : ℕ) (b : Bool × ℕ) : RFin ⟨false, h⟩ b := fun h => by cases h
lemma liftM_countFrom_shift {α : Type} (X : OracleComp AHash α) (c : ℕ) :
    (liftM (countFrom (fun _ => 1) X c) : OracleComp AW (α × ℕ)) =
      (fun p => (p.1, c + p.2)) <$> (liftM (SigGolfCandidate.Bridge.countCalls X) : OracleComp AW (α × ℕ)) := by
  rw [countFrom_shift, liftM_map]
  rfl
lemma probEvent_bind_le' {α β γ : Type} (mx : ProbComp α) {f : α → ProbComp β}
    {g : α → ProbComp γ} {E₁ : β → Prop} {E₂ : γ → Prop}
    (h : ∀ x, Pr[E₁ | f x] ≤ Pr[E₂ | g x]) : Pr[E₁ | mx >>= f] ≤ Pr[E₂ | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
theorem value_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)} {X : OracleComp HashSpec γ}
    {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) :
    (fun r => r.value) <$> run = F <$> X := by
  have h2 := congrArg (fun x => Prod.fst <$> x) h
  simp only [Functor.map_map] at h2
  rw [h2]
  conv_rhs => rw [← fst_countBoth X]
  rw [Functor.map_map]
theorem allSucceed_foldlM (Pr : Message → OracleComp HashSpec HonestResult) (L : List Message)
    (s : HonestSummary) :
    HonestSummary.allSucceed <$> L.foldlM (fun summary message => do
        let result ← Pr message
        return (⟨summary.allSucceed && result.success,
          fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) s =
      foldAll L (fun m => HonestResult.success <$> Pr m) s.allSucceed := by
  induction L generalizing s with
  | nil => simp [foldAll]
  | cons m L ih =>
    rw [List.foldlM_cons, foldAll_cons, map_bind, bind_assoc, bind_map_left]
    refine bind_congr fun r => ?_
    rw [pure_bind, ih]
theorem allSucceed_allMessages (sub : Submission) (sk : SecretKey) :
    HonestSummary.allSucceed <$> sub.allMessages sk =
      foldAll (Finset.univ : Finset Message).toList
        (fun m => HonestResult.success <$> sub.honest sk m) true := by
  unfold Submission.allMessages
  exact allSucceed_foldlM _ _ {}
theorem mrealize_foldAll {κ : Type} (sk : BitVec 256) (L : List κ) (Pr : κ → M Bool) (b : Bool) :
    mrealize sk (foldAll L Pr b) = foldAll L (fun k => mrealize sk (Pr k)) b := by
  induction L generalizing b with
  | nil => rfl
  | cons k L ih =>
    rw [foldAll_cons, foldAll_cons, mrealize_bind]
    exact bind_congr fun c => ih _
noncomputable def msgs : List SigGolfCandidate.T3.Message := (Finset.univ : Finset SigGolfCandidate.T3.Message).toList
def machineAnswers (hash : Hash) (sk : BitVec 256) : SigGolfCandidate.T3.Correctness.Answers :=
  fun q => evalWithAnswerFn hash (machineHandler sk q)
theorem eval_mrealize {α : Type} (hash : Hash) (sk : BitVec 256) (p : M α) :
    evalWithAnswerFn hash (mrealize sk p) = evalWithAnswerFn (machineAnswers hash sk) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [mrealize_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
    have hq : evalWithAnswerFn hash (mrealize sk (liftM (Spec.query q) : M _)) = machineAnswers hash sk q := by
      rw [mrealize, simulateQ_spec_query]; rfl
    have hq' : evalWithAnswerFn (machineAnswers hash sk) (liftM (Spec.query q) : M _) =
        machineAnswers hash sk q := simulateQ_spec_query _ _
    rw [hq, hq']
    exact ih _
theorem allQ_foldAll' {κ : Type} {Q : Spec.Domain → Prop} (L : List κ) (Pr : κ → M Bool)
    (h : ∀ k, AllQueriesSatisfy (Pr k) Q) (b : Bool) : AllQueriesSatisfy (foldAll L Pr b) Q := by
  unfold foldAll
  exact SigGolfCandidate.T3M.allQ_foldlM _ _ (fun _ k => SigGolfCandidate.T3M.allQ_map _ (h k)) _
theorem withRandomOracle_map' {α β : Type} (f : α → β) (oa : OracleComp HashSpec α) :
    withRandomOracle (f <$> oa) = f <$> withRandomOracle oa := by
  unfold withRandomOracle
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]
theorem mrealize_query_coin (sk : BitVec 256) (n : ℕ) :
    mrealize sk (liftM (Spec.query (.inl (.inl n))) : M (Fin (n + 1))) = pure 0 := by
  simp [mrealize, machineHandler]
theorem mrealize_query_public (sk : BitVec 256) (input : List UInt8) :
    mrealize sk (liftM (Spec.query (.inl (.inr input))) : M _) =
      (liftM (OracleSpec.query (spec := HashSpec) (toQ input)) : OracleComp HashSpec _) := by
  simp [mrealize, machineHandler]
theorem mrealize_query_private (sk : BitVec 256) (c : SigGolfCandidate.T3.Coordinate) :
    mrealize sk (liftM (Spec.query (.inr c)) : M _) =
      (liftM (OracleSpec.query (spec := HashSpec) (toQ (privateInput sk c))) : OracleComp HashSpec _) := by
  simp [mrealize, machineHandler]
theorem countBlocks_query_bind {α : Type} (x : Query) (g : BitVec 256 → OracleComp HashSpec α) :
    countBlocks ((liftM (OracleSpec.query (spec := HashSpec) x) : OracleComp HashSpec _) >>= g) =
      (liftM (OracleSpec.query (spec := HashSpec) x) : OracleComp HashSpec _) >>= fun a =>
        (fun r => (r.1, x.blocks + r.2)) <$> countBlocks (g a) := by
  unfold countBlocks
  rw [countWith_bind, countWith_query, bind_map_left]
theorem mrealize_countBlocks {α : Type} (sk : BitVec 256) {p : M α}
    (h : AllQueriesSatisfy p SigGolfCandidate.T3.Cost.GoodQuery) :
    countBlocks (mrealize sk p) = mrealize sk (SigGolfCandidate.T3.Cost.countBlocks p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [mrealize_bind]
    unfold SigGolfCandidate.T3.Cost.countBlocks
    rw [SigGolfCandidate.T3.Cost.countWith_bind, SigGolfCandidate.T3.Cost.countWith_query, mrealize_bind, mrealize_map, bind_map_left]
    rcases q with (n | input) | c
    · rw [mrealize_query_coin, pure_bind, pure_bind]
      simp only [mrealize_map]
      rw [show SigGolfCandidate.T3.Cost.countWith SigGolfCandidate.T3.Cost.weight (k (0 : Fin (n + 1))) = SigGolfCandidate.T3.Cost.countBlocks (k (0 : Fin (n + 1)))
        from rfl, ← ih (0 : Fin (n + 1)) (h.2 _)]
      simp only [SigGolfCandidate.T3.Cost.weight, Nat.zero_add]
      exact (id_map _).symm
    · rw [mrealize_query_public, countBlocks_query_bind]
      refine bind_congr fun a => ?_
      simp only [mrealize_map]
      rw [show SigGolfCandidate.T3.Cost.countWith SigGolfCandidate.T3.Cost.weight (k a) = SigGolfCandidate.T3.Cost.countBlocks (k a) from rfl, ← ih a (h.2 a),
        blocks_toQ h.1]
      rfl
    · rw [mrealize_query_private, countBlocks_query_bind]
      refine bind_congr fun a => ?_
      simp only [mrealize_map]
      rw [show SigGolfCandidate.T3.Cost.countWith SigGolfCandidate.T3.Cost.weight (k a) = SigGolfCandidate.T3.Cost.countBlocks (k a) from rfl, ← ih a (h.2 a),
        blocks_toQ (privateInput_aligned sk c), SigGolfCandidate.T3.Cost.private_realization_weight]
theorem allQ_countWith {α : Type} {Q : Spec.Domain → Prop} (wt : SigGolfCandidate.T3.Cost.Query → ℕ) {p : M α}
    (h : AllQueriesSatisfy p Q) : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countWith wt p) Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [SigGolfCandidate.T3.Cost.countWith_bind, SigGolfCandidate.T3.Cost.countWith_query, bind_map_left]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨h.1, fun u => SigGolfCandidate.T3M.allQ_map _ (ih u (h.2 u))⟩
set_option maxRecDepth 100000 in
theorem withRandomOracle_mrealize {α : Type} (sk : SecretKey) {Y : M α}
    (hgood : AllQueriesSatisfy Y SigGolfCandidate.T3.Cost.GoodQuery) (hhash : AllQueriesSatisfy Y isHash) :
    withRandomOracle (mrealize sk Y) = Prod.fst <$> SigGolfCandidate.T3.Sampling.roRun sk Y ∅ := by
  unfold withRandomOracle SigGolfCandidate.T3.Sampling.roRun
  rw [mrealize_eq_relabel, ← run'_relabel_on toQ {l | Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _ => rfl), realize_eq_liftM sk hhash, SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right, StateT.run'_eq]
theorem eval_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)} {X : OracleComp HashSpec γ}
    {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) (hash : Hash) :
    (evalWithAnswerFn hash run).value = F (evalWithAnswerFn hash X) ∧
      (evalWithAnswerFn hash run).hashCompressions = (evalWithAnswerFn hash (countBlocks X)).2 := by
  have h1 := congrArg (evalWithAnswerFn hash) h
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map] at h1
  simp only [Prod.mk.injEq] at h1
  have h2 := congrArg (evalWithAnswerFn hash) (fst_countBoth X)
  rw [evalWithAnswerFn_map] at h2
  have h3 := congrArg (evalWithAnswerFn hash) (countBoth_blocks X)
  rw [evalWithAnswerFn_map] at h3
  refine ⟨h1.1.trans (by rw [h2]), h1.2.2.trans ?_⟩
  rw [← h3]
theorem abstract_count_refinement {α β : Type} (sk : SecretKey) (hash : Hash)
    (X : M α) (run : OracleComp HashSpec (RunResult β)) (F : α → Option β)
    (h : (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> run =
      (fun p => (F p.1,p.2.1,p.2.2)) <$> countBoth (mrealize sk X))
    (hg : AllQueriesSatisfy X SigGolfCandidate.T3.Cost.GoodQuery) :
    (evalWithAnswerFn hash run).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks X))).2 := by
  exact (eval_of_counts h hash).2.trans
    (congrArg (fun p => (evalWithAnswerFn hash p).2) (mrealize_countBlocks sk hg))
theorem eval_cost_fst {α : Type} (answers : SigGolfCandidate.T3.Correctness.Answers) (wt : SigGolfCandidate.T3.Cost.Query → ℕ) (p : M α) :
    (evalWithAnswerFn answers (SigGolfCandidate.T3.Cost.countWith wt p)).1 = evalWithAnswerFn answers p := by
  have := congrArg (evalWithAnswerFn answers) (SigGolfCandidate.T3.Cost.fst_countWith wt p)
  rw [evalWithAnswerFn_map] at this
  exact this
theorem countWith_map' {α β : Type} (wt : SigGolfCandidate.T3.Cost.Query → ℕ) (f : α → β) (p : M α) :
    SigGolfCandidate.T3.Cost.countWith wt (f <$> p) = (fun q => (f q.1, q.2)) <$> SigGolfCandidate.T3.Cost.countWith wt p := by
  rw [map_eq_bind_pure_comp, SigGolfCandidate.T3.Cost.countWith_bind, map_eq_bind_pure_comp]
  refine bind_congr fun q => ?_
  simp
theorem generic_outer_sign_cost {κ : Type} (sub : Submission) (hash : Hash)
    (sk : SecretKey) (message : Message) (keys : OracleComp HashSpec κ)
    (encode : κ → PublicKey × Bytes sub.sizes.cache)
    (counts : κ → OracleComp HashSpec Nat)
    (hkeys : (sub.runWith hash .keygen sk).value = some (encode (evalWithAnswerFn hash keys)))
    (hcounts : ∀ key, (sub.runWith hash .sign (sk, (encode key).2, message)).hashCompressions =
      evalWithAnswerFn hash (counts key)) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> sub.honest sk message) =
      evalWithAnswerFn hash (keys >>= counts) := by
  rw [evalWithAnswerFn_map, eval_costs_sign, hkeys, evalWithAnswerFn_bind]
  exact hcounts (evalWithAnswerFn hash keys)
theorem generic_count_pipeline {κ α : Type} (sk : SecretKey) (keys : SigGolfCandidate.T3.M κ)
    (signer : κ → SigGolfCandidate.T3.M α) (charge : α → Nat) :
    mrealize sk keys >>= (fun key => charge <$> mrealize sk (signer key)) =
      charge <$> mrealize sk (keys >>= signer) := by
  rw [mrealize_bind, map_bind]
theorem generic_outer_expand_cost {κ σ α : Type} (sub : Submission) (hash : Hash)
    (sk : SecretKey) (message : Message) (keys : OracleComp HashSpec κ)
    (encodeKey : κ → PublicKey × Bytes sub.sizes.cache)
    (signer : κ → OracleComp HashSpec α) (selected : α → Option σ)
    (encodeSig : σ → Bytes sub.sizes.signature)
    (counts : κ → σ → OracleComp HashSpec Nat)
    (hkeys : (sub.runWith hash .keygen sk).value = some (encodeKey (evalWithAnswerFn hash keys)))
    (hsign : ∀ key, (sub.runWith hash .sign (sk, (encodeKey key).2, message)).value =
      (selected (evalWithAnswerFn hash (signer key))).map encodeSig)
    (hexpand : ∀ key sig, (sub.runWith hash .expand (message, (encodeKey key).1, encodeSig sig)).hashCompressions =
      evalWithAnswerFn hash (counts key sig)) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> sub.honest sk message) =
      evalWithAnswerFn hash (keys >>= fun key => signer key >>= fun signed =>
        match selected signed with
        | none => pure 0
        | some sig => counts key sig) := by
  rw [evalWithAnswerFn_map, eval_costs_expand, hkeys, evalWithAnswerFn_bind]
  simp only
  rw [hsign, evalWithAnswerFn_bind]
  cases selected (evalWithAnswerFn hash (signer (evalWithAnswerFn hash keys))) with
  | none => rfl
  | some sig => exact hexpand _ sig
theorem generic_joint_count_pipeline {κ σ ω : Type} (sk : SecretKey)
    (initial : SigGolfCandidate.T3.M κ) (signer : κ → SigGolfCandidate.T3.M (Option σ)) (expander : κ → σ → SigGolfCandidate.T3.M ω) :
    (mrealize sk initial >>= fun key => mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (signer key)) >>= fun signed =>
      match signed.1 with
      | none => pure 0
      | some sig => Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (expander key sig))) =
      Prod.snd <$> mrealize sk (jointCounts initial signer expander) := by
  unfold jointCounts
  rw [mrealize_bind, map_bind]
  apply bind_congr
  intro key
  rw [mrealize_bind, map_bind]
  apply bind_congr
  intro signed
  rcases signed with ⟨_ | sig, count⟩
  · simp only [mrealize_pure, map_pure]
  · simp only [mrealize_bind, map_bind, mrealize_pure, map_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
theorem two_rpow_eq' (x : ℝ) : (2 : ℝ≥0∞) ^ x = ENNReal.ofReal (Real.rpow 2 x) := by
  rw [Real.rpow_eq_pow, ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
  simp
theorem withRandomOracle_pure {α : Type} (a : α) : withRandomOracle (pure a : OracleComp HashSpec α) = pure a := by
  simp [withRandomOracle]
end ClaudeWCT.W9.T3M.Final
end
-- ==== merged from ClaudeWCT_W9_New_G3a_ExtractSrc ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
def PosSource : Extract.Pos → Prop
  | .chain lay tree leaf i step => tree < 2 ^ Extract.treeBits lay ∧ leaf < 2 ^ height lay ∧ i < chainCount lay ∧
      step + 1 < 2 ^ width lay i
  | .leaf lay tree leaf => tree < 2 ^ Extract.treeBits lay ∧ leaf < 2 ^ height lay
  | .node lay tree level node => tree < 2 ^ Extract.treeBits lay ∧ level < height lay ∧
      node < 2 ^ (height lay - level - 1) ∧ (lay = 0 ∨ level + 1 < height lay)
  | .forest index => index < 2 ^ 31
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
def StructuralHitSrc (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ PosSource position ∧ StructuralClass answers input position ∧
    Extract.HashHitAt answers position (Extract.honestInput answers position) input
end ClaudeWCT.W9.T3.Security.WotsExtract
end
-- ==== merged from T3_Secc_PairGuessLazyEager ====
section

section

section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
theorem eval_nonce (ω : Omega U) (fts : FtsCoord → Digest) (m : Message) :
    evalWithAnswerFn (Omega.answers hU ω fts) (privateNonce m) = nonceOf ω m := by
  unfold privateNonce privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other) (.inr (.inl m))).extractLsb' 0 128 = _
  rw [privateEquiv_symm_apply, ChainGraph.joinOutput_low]
  exact splitEquiv_symm_other _ _ (nonceHalf m) (nonceHalf_not_secret m)
end Table
section Inline
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyCouple : DecidableEq T3.Cache := Classical.decEq _
theorem programL_pure (ω : Omega U) {β : Type} (value : β) : programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    programL hU ω (liftM (T3.Spec.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => programL hU ω (next coin)) := rfl
theorem programL_public (ω : Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programL hU ω (liftM (T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    programL hU ω (liftM (T3.Spec.query (.inr c)) >>= next) = programL hU ω (next 0) := rfl
end Inline
section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)
def Consistent (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ x a, mem.rows x = some a → a = rowVal D x) ∧ ∀ m v, mem.nonces m = some v → v = Nn m
theorem consistent_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Consistent D Nn LazyMem.empty :=
  by
  refine ⟨fun x a h => ?_, fun m v h => ?_⟩
  · simp [LazyMem.empty] at h
  · simp [LazyMem.empty] at h
theorem rowStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', Consistent D Nn mem' ∧ rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') := by
  have hreplay : Consistent D Nn (mem.replayRow x isBirth) := by
    unfold LazyMem.replayRow
    split
    · exact hm
    · exact hm
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
      change pure (a, mem.replayRow x isBirth) = _
      rw [hm.1 x a h]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ⟨?_, hm.2⟩, ?_⟩
        · intro y a hy
          change mem.rows.cacheQuery x (rowVal D x) y = some a at hy
          by_cases hyx : y = x
          · subst hyx
            rw [QueryCache.cacheQuery_self] at hy
            exact (Option.some.inj hy).symm
          · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
            exact hm.1 y a hy
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
      · refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (m : Message) :
    ∃ mem', Consistent D Nn mem' ∧ nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, hm, ?_⟩
      change pure (v, mem) = _
      rw [hm.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), ⟨hm.1, ?_⟩, map_pure _ _⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.2 m' v hv
theorem fixed_aux_pure {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem'))
    (next : AuxSpecL.Range input → OracleComp WSpecL α) :
    runWith (fixedImpl (envE D Nn) fts) (liftM (WSpecL.query (.inl input)) >>= next) s =
      runWith (fixedImpl (envE D Nn) fts) (next v) { s with memory := mem' } := by
  rw [SecretGuessObservation.runWith_query_bind]
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((envE D Nn).auxiliary s input) : SPMF _)) >>= _ = _
  rw [h, liftM_pure, map_pure, pure_bind]
end Run
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Ghost
open SecretGuessObservation (fixedRun fixedImpl runWith)
theorem runL_bind_nonzero {β γ : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL)
    (r : γ × WStateL) (hr : fixedRun E fts (first >>= next) s r ≠ 0) :
    ∃ mid, fixedRun E fts first s mid ≠ 0 ∧ fixedRun E fts (next mid.1) mid.2 r ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runL_pure_nonzero {β : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (v : β) (s : WStateL) (r : β × WStateL) (hr : fixedRun E fts (pure v) s r ≠ 0) :
    r = (v, s) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
structure Grows (m m' : LazyMem) : Prop where
  rows : ∀ x a, m.rows x = some a → m'.rows x = some a
  births : ∀ a ∈ m.births, a ∈ m'.births
  trials : ∀ x ∈ m.trials, x ∈ m'.trials
  exposures : ∀ o ∈ m.exposures, o ∈ m'.exposures
theorem Grows.refl (m : LazyMem) : Grows m m := ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
theorem Grows.trans {m1 m2 m3 : LazyMem} (h1 : Grows m1 m2) (h2 : Grows m2 m3) : Grows m1 m3 :=
  ⟨fun x a h => h2.rows x a (h1.rows x a h), fun a h => h2.births a (h1.births a h),
    fun x h => h2.trials x (h1.trials x h), fun o h => h2.exposures o (h1.exposures o h)⟩
def Good (D : digestInputs → HashOutput) (Nn : Message → Digest) (m : LazyMem) : Prop :=
  Consistent D Nn m ∧ ∀ x a, m.rows x = some a → a ∈ m.births ∨ x ∈ m.trials
theorem good_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Good D Nn LazyMem.empty :=
  ⟨consistent_empty D Nn, fun x a h => by simp [LazyMem.empty] at h⟩
theorem replayRow_true (mem : LazyMem) (x : HashInput) : mem.replayRow x true = mem := by
  simp [LazyMem.replayRow]
theorem replayRow_false (mem : LazyMem) (x : HashInput) :
    mem.replayRow x false = { mem with trials := mem.trials ++ [x] } := by
  simp [LazyMem.replayRow]
theorem readRow_true (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a true = { mem with rows := mem.rows.cacheQuery x a, births := mem.births ++ [a] } := by
  simp [LazyMem.readRow]
theorem readRow_false (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a false = { mem with rows := mem.rows.cacheQuery x a, trials := mem.trials ++ [x] } := by
  simp [LazyMem.readRow]
theorem cacheQuery_good (D : digestInputs → HashOutput) (mem : LazyMem) (x : HashInput) (y : HashInput) (b : HashOutput)
    (hy : mem.rows.cacheQuery x (rowVal D x) y = some b) :
    b = rowVal D x ∧ y = x ∨ mem.rows y = some b := by
  by_cases hyx : y = x
  · subst hyx
    rw [QueryCache.cacheQuery_self] at hy
    exact Or.inl ⟨(Option.some.inj hy).symm, rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
    exact Or.inr hy
theorem rowStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') ∧ Good D Nn mem' ∧
      Grows mem mem' ∧ (x ∈ digestInputs → mem'.rows x = some (rowVal D x)) := by
  have hreplay : Good D Nn (mem.replayRow x isBirth) ∧ Grows mem (mem.replayRow x isBirth) := by
    cases isBirth
    · rw [replayRow_false]
      refine ⟨⟨hm.1, fun y a hy => ?_⟩, ⟨fun _ _ h => h, fun _ h => h, fun y h => List.mem_append_left _ h,
        fun _ h => h⟩⟩
      rcases hm.2 y a hy with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · rw [replayRow_true]
      exact ⟨hm, Grows.refl mem⟩
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      have ha := hm.1.1 x a h
      refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun _ => ?_⟩
      · change pure (a, mem.replayRow x isBirth) = _
        rw [ha]
      · rw [hreplay.2.rows x a h, ha]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ?_, ?_, ?_, fun _ => ?_⟩
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
        · cases isBirth
          · rw [readRow_false]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl h
                · exact Or.inr (List.mem_append_left _ h)
          · rw [readRow_true]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl (List.mem_append_left _ h)
                · exact Or.inr h
        · have hrows : ∀ y b, mem.rows y = some b → mem.rows.cacheQuery x (rowVal D x) y = some b := by
            intro y b hy
            have hyx : y ≠ x := by
              rintro rfl
              rw [h] at hy
              cases hy
            rw [QueryCache.cacheQuery_of_ne _ _ hyx]
            exact hy
          cases isBirth
          · rw [readRow_false]
            exact ⟨hrows, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h⟩
          · rw [readRow_true]
            exact ⟨hrows, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩
        · cases isBirth
          · rw [readRow_false]
            exact QueryCache.cacheQuery_self _ _ _
          · rw [readRow_true]
            exact QueryCache.cacheQuery_self _ _ _
      · refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun h' => absurd h' hx⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (m : Message) :
    ∃ mem', nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') ∧ Good D Nn mem' ∧ Grows mem mem' := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, ?_, hm, Grows.refl mem⟩
      change pure (v, mem) = _
      rw [hm.1.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), map_pure _ _, ⟨⟨hm.1.1, ?_⟩, hm.2⟩,
        ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.1.2 m' v hv
theorem expose_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (o : Option HashOutput) : Good D Nn (mem.expose o) ∧ Grows mem (mem.expose o) :=
  ⟨hm, ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h⟩⟩
theorem fixed_aux_single (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem')) :
    fixedRun (envE D Nn) fts (liftM (WSpecL.query (.inl input))) s = pure (v, { s with memory := mem' }) := by
  rw [fixedRun, ← bind_pure (liftM (WSpecL.query (.inl input))), fixed_aux_pure D Nn fts s input v mem' h,
    SecretGuessObservation.runWith_pure]
theorem run_good {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : Good D Nn s.memory) (r : α × WStateL)
    (hr : fixedRun (envE D Nn) fts W s r ≠ 0) : Good D Nn r.2.memory ∧ Grows s.memory r.2.memory := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      rw [runL_pure_nonzero _ fts a s r hr]
      exact ⟨hs, Grows.refl _⟩
  | query_bind input next ih =>
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            unfold fixedRun at hr
            rw [SecretGuessObservation.runWith_query_bind, RetainedObservation.bind_nonzero] at hr
            obtain ⟨mid, hm, hr⟩ := hr
            have hmid : mid.2 = s := by
              change ((fun result => (result.1, { s with memory := result.2 })) <$>
                (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) mid ≠ 0 at hm
              rw [liftM_map, Functor.map_map] at hm
              simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
                SPMF.pure_apply_eq_zero_iff, not_not] at hm
              obtain ⟨c, _, rfl⟩ := hm
              rfl
            obtain ⟨h1, h2⟩ := ih mid.1 mid.2 (by rw [hmid]; exact hs) hr
            rw [hmid] at h2
            exact ⟨h1, h2⟩
        | birth x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn fts s (.birth x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | trial x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn fts s (.trial x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | nonce m =>
            obtain ⟨mem', heq, hg, hgr⟩ := nonceStep_ghost D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn fts s (.nonce m) (Nn m) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn fts s (.expose o) () (s.memory.expose o) rfl] at hr
            have he := expose_ghost D Nn s.memory hs o
            obtain ⟨h1, h2⟩ := ih () { s with memory := s.memory.expose o } he.1 hr
            exact ⟨h1, he.2.trans h2⟩
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (decide (fts f = c), SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) :
          SPMF (Bool × WStateL)) >>= fun mid => runWith (fixedImpl (envE D Nn) fts) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) hs hr
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (fts f, SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) : SPMF (Digest × WStateL)) >>=
          fun mid => runWith (fixedImpl (envE D Nn) fts) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) hs hr
end Ghost
end SigGolfCandidate.T3.Security.BPair
end
end

section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Uniform
theorem evalSPMF_uniform {X : Type} [Fintype X] [Nonempty X] (I : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = (liftM (PMF.uniformOfFintype X) : SPMF X) := by
  apply SPMF.ext
  intro x
  rw [SPMF.liftM_apply, PMF.uniformOfFintype_apply, ← SPMF.probOutput_eq_apply, probOutput_evalSPMF]
  exact @probOutput_uniformSample X I _ x
theorem uniform_update {ι β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β] (i : ι)
    (g : β → (ι → β) → SPMF γ) (hg : ∀ a T c, g a (Function.update T i c) = g a T) :
    ((liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g (T i) T) =
      ((liftM (PMF.uniformOfFintype β) : SPMF β) >>= fun a =>
        (liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g a T) := by
  let IT : SampleableType (ι → β) := SampleableType.ofFintype _
  let Ia : SampleableType β := SampleableType.ofFintype _
  let IP : SampleableType ((ι → β) × β) := SampleableType.ofFintype _
  let f : (ι → β) × β → (ι → β) × β := fun p => (Function.update p.1 i p.2, p.1 i)
  have hinv : ∀ p, f (f p) = p := by
    rintro ⟨T, a⟩
    simp only [f, Function.update_self, Function.update_idem, Function.update_eq_self]
  have hf : Function.Bijective f := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨f p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((ι → β) × β) IP ((ι → β) × β) IP _ f hf
  have hp := @FullGame.uniform_product (ι → β) β _ _ IT Ia IP
  rw [← evalSPMF_uniform IT, ← evalSPMF_uniform Ia]
  calc (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T => g (T i) T)
      = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun _ => g (T i) T) := by
        simp only [evalSPMF_uniform Ia, RetainedObservation.lift_bind_const]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g (p.1 i) p.1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hp]
    _ = (𝒮[f <$> (@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 (Function.update p.1 i p.2)) := by
        rw [evalSPMF_map, bind_map_left]
        simp only [f, Function.update_self]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 p.1) := by simp only [hg]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g p.2 p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun a => g a T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := RetainedObservation.bind_comm _ _ _
noncomputable def patch {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) : β :=
  @dite _ (∃ s, e s = a) (Classical.propDecidable _) (fun h => D (Classical.choose h)) (fun _ => T a)
theorem patch_e {α σ β : Type} {e : σ → α} (he : Function.Injective e) (T : α → β) (D : σ → β) (s : σ) :
    patch e T D (e s) = D s := by
  have h : ∃ s', e s' = e s := ⟨s, rfl⟩
  rw [patch, dif_pos h]
  exact congrArg D (he (Classical.choose_spec h))
theorem patch_of {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) (ha : ∀ s, e s ≠ a) :
    patch e T D a = T a := by
  rw [patch, dif_neg (fun h => ha _ (Classical.choose_spec h))]
theorem patch_uniform {α σ β γ : Type} [Fintype α] [Fintype σ] [Fintype β] [Nonempty β] [DecidableEq α]
    [DecidableEq σ] {e : σ → α} (he : Function.Injective e) (IT : SampleableType (α → β))
    (ID : SampleableType (σ → β)) (k : (α → β) → SPMF γ) :
    (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T => 𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>=
      fun D => k (patch e T D)) = 𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= k := by
  let IP : SampleableType ((α → β) × (σ → β)) := SampleableType.ofFintype _
  let Φ : (α → β) × (σ → β) → (α → β) × (σ → β) := fun p => (patch e p.1 p.2, p.1 ∘ e)
  have hinv : ∀ p, Φ (Φ p) = p := by
    rintro ⟨T, D⟩
    refine Prod.ext (funext fun a => ?_) (funext fun s => ?_)
    · change patch e (patch e T D) (T ∘ e) a = T a
      by_cases h : ∃ s, e s = a
      · obtain ⟨s, rfl⟩ := h
        rw [patch_e he]
        rfl
      · have h' : ∀ s, e s ≠ a := fun s hs => h ⟨s, hs⟩
        rw [patch_of e _ _ a h', patch_of e _ _ a h']
    · exact patch_e he T D s
  have hΦ : Function.Bijective Φ := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨Φ p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((α → β) × (σ → β)) IP ((α → β) × (σ → β)) IP _ Φ hΦ
  have hp := @FullGame.uniform_product (α → β) (σ → β) _ _ IT ID IP
  calc _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k (Φ p).1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
        rfl
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k (Φ p).1) := by rw [hp]
    _ = (𝒮[Φ <$> (@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by
        rw [evalSPMF_map, bind_map_left]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T =>
          𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>= fun _ => k T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := by simp only [evalSPMF_uniform ID, RetainedObservation.lift_bind_const]
end Uniform
noncomputable instance instSampleableDigestRows : SampleableType (digestInputs → HashOutput) :=
  SampleableType.ofFintype _
noncomputable instance instSampleableNonceTables : SampleableType (Message → Digest) := SampleableType.ofFintype _
section OmegaPatch
variable {U : Finset HashInput} (hsub : digestInputs ⊆ U)
def digestEmb : digestInputs → U := fun x => ⟨x.1, hsub x.2⟩
theorem digestEmb_injective : Function.Injective (digestEmb hsub) :=
  fun x y h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
end OmegaPatch
section Steps
open SecretGuessObservation (forcedRun forcedImpl lazyImpl runWith afterTrial afterDisclosure forcedTrial)
variable (slot : Nat)
theorem rowStep_some (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (a : HashOutput)
    (h : mem.rows x = some a) : rowStep mem x b src = pure (a, mem.replayRow x b) := by
  unfold rowStep
  rw [h]
theorem rowStep_out (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∉ digestInputs) : rowStep mem x b src = pure (0, mem.replayRow x b) := by
  unfold rowStep
  rw [h, if_neg hx]
theorem rowStep_in (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∈ digestInputs) : rowStep mem x b src = (fun a => (a, mem.readRow x a b)) <$> src := by
  unfold rowStep
  rw [h, if_pos hx]
theorem nonceStep_some (mem : LazyMem) (m : Message) (src : PMF Digest) (v : Digest) (h : mem.nonces m = some v) :
    nonceStep mem m src = pure (v, mem) := by
  unfold nonceStep
  rw [h]
theorem nonceStep_none (mem : LazyMem) (m : Message) (src : PMF Digest) (h : mem.nonces m = none) :
    nonceStep mem m src = (fun v => (v, mem.drawNonce m v)) <$> src := by
  unfold nonceStep
  rw [h]
variable (rs : HashInput → PMF HashOutput) (ns : Message → PMF Digest)
theorem step_aux (s : WStateL) (input : AuxL) :
    (forcedImpl (envWith rs ns) slot (.inl input)).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (auxWith rs ns s input) : SPMF (AuxSpecL.Range input × LazyMem)) := rfl
theorem step_coin (s : WStateL) (n : Nat) :
    (forcedImpl (envWith rs ns) slot (.inl (.coin n))).run s =
      (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) = _
  rw [liftM_map, Functor.map_map]
theorem step_expose (s : WStateL) (o : Option HashOutput) :
    (forcedImpl (envWith rs ns) slot (.inl (.expose o))).run s = pure ((), { s with memory := s.memory.expose o }) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM (pure ((), s.memory.expose o) : PMF _) : SPMF _) = _
  rw [liftM_pure, map_pure]
theorem step_birth (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.birth x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x true (rs x)) : SPMF (HashOutput × LazyMem)) := rfl
theorem step_trial (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.trial x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x false (rs x)) : SPMF (HashOutput × LazyMem)) := rfl
theorem step_nonce (s : WStateL) (m : Message) :
    (forcedImpl (envWith rs ns) slot (.inl (.nonce m))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (nonceStep s.memory m (ns m)) : SPMF (Digest × LazyMem)) := rfl
theorem step_guess (s : WStateL) (f : FtsCoord) (c : Digest) :
    (forcedImpl (envWith rs ns) slot (.inr (.inl (f, c)))).run s =
      (fun hit => (hit, { afterTrial (envWith rs ns) s f c hit with memory := s.memory })) <$> forcedTrial slot s f c := rfl
theorem step_disclose (s : WStateL) (f : FtsCoord) :
    (forcedImpl (envWith rs ns) slot (.inr (.inr f))).run s =
      (fun v => (v, { afterDisclosure (envWith rs ns) s f v with memory := s.memory })) <$>
        UniformTableCompletion.cell (s.allowed f) := rfl
theorem afterTrial_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : FtsCoord) (c : Digest) (hit : Bool) :
    afterTrial (envWith rs ns) s f c hit = afterTrial (envWith rs' ns') s f c hit := rfl
theorem afterDisclosure_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : FtsCoord) (v : Digest) :
    afterDisclosure (envWith rs ns) s f v = afterDisclosure (envWith rs' ns') s f v := rfl
end Steps
section Congr
open SecretGuessObservation (forcedRun forcedImpl runWith)
def Agree (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ y : digestInputs, mem.rows y.1 = none → D y = D' y) ∧ ∀ m, mem.nonces m = none → Nn m = Nn' m
theorem rowVal_agree {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (hx : mem.rows x = none) : rowVal D x = rowVal D' x := by
  unfold rowVal
  by_cases hd : x ∈ digestInputs
  · rw [dif_pos hd, dif_pos hd]
    exact h.1 ⟨x, hd⟩ hx
  · rw [dif_neg hd, dif_neg hd]
theorem agree_replay {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (b : Bool) : Agree D D' Nn Nn' (mem.replayRow x b) := by
  cases b
  · rw [replayRow_false]
    exact h
  · rw [replayRow_true]
    exact h
theorem agree_read {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (a : HashOutput) (b : Bool) :
    Agree D D' Nn Nn' (mem.readRow x a b) := by
  have hrows : ∀ y : digestInputs, (mem.rows.cacheQuery x a) y.1 = none → D y = D' y := by
    intro y hy
    by_cases hyx : y.1 = x
    · rw [hyx, QueryCache.cacheQuery_self] at hy
      cases hy
    · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
      exact h.1 y hy
  cases b
  · rw [readRow_false]
    exact ⟨hrows, h.2⟩
  · rw [readRow_true]
    exact ⟨hrows, h.2⟩
theorem agree_draw {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (m : Message) (v : Digest) : Agree D D' Nn Nn' (mem.drawNonce m v) := by
  refine ⟨h.1, fun m' hm' => ?_⟩
  change Function.update mem.nonces m (some v) m' = none at hm'
  by_cases hmm : m' = m
  · rw [hmm, Function.update_self] at hm'
    cases hm'
  · rw [Function.update_of_ne hmm] at hm'
    exact h.2 m' hm'
theorem forced_congr {α : Type} (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (slot : Nat)
    (W : OracleComp WSpecL α) (s : WStateL) (h : Agree D D' Nn Nn' s.memory) :
    forcedRun (envE D Nn) slot W s = forcedRun (envE D' Nn') slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            rw [envE, envE, step_coin, step_coin, bind_map_left, bind_map_left]
            exact bind_congr fun c => ih c s h
        | birth x =>
            rw [envE, envE, step_birth, step_birth]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x true)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) true }
                    (agree_read h x _ true)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x true)
        | trial x =>
            rw [envE, envE, step_trial, step_trial]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x false)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) false }
                    (agree_read h x _ false)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x false)
        | nonce m =>
            rw [envE, envE, step_nonce, step_nonce]
            cases hc : s.memory.nonces m with
            | some v =>
                rw [nonceStep_some _ _ _ v hc, nonceStep_some _ _ _ v hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih v _ h
            | none =>
                rw [nonceStep_none _ _ _ hc, nonceStep_none _ _ _ hc, liftM_map, liftM_map, liftM_pure, liftM_pure,
                  map_pure, map_pure, map_pure, map_pure, pure_bind, pure_bind, h.2 m hc]
                exact ih _ _ (agree_draw h m _)
        | expose o =>
            rw [envE, envE, step_expose, step_expose, pure_bind, pure_bind]
            exact ih () _ h
      · rw [envE, envE, step_guess, step_guess, bind_map_left, bind_map_left]
        refine bind_congr fun hit => ?_
        rw [afterTrial_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih hit _ h
      · rw [envE, envE, step_disclose, step_disclose, bind_map_left, bind_map_left]
        refine bind_congr fun v => ?_
        rw [afterDisclosure_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih v _ h
end Congr
section EagerLazy
open SecretGuessObservation (forcedRun forcedImpl runWith)
noncomputable def rowsLaw : SPMF (digestInputs → HashOutput) := liftM (PMF.uniformOfFintype (digestInputs → HashOutput))
noncomputable def noncesLaw : SPMF (Message → Digest) := liftM (PMF.uniformOfFintype (Message → Digest))
theorem avg_indep {α : Type} (slot : Nat) (input : WSpecL.Domain) (next : WSpecL.Range input → OracleComp WSpecL α)
    (s : WStateL)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s')
    (X : SPMF (WSpecL.Range input × WStateL)) (hE : ∀ D Nn, (forcedImpl (envE D Nn) slot input).run s = X)
    (hL : (forcedImpl envL slot input).run s = X) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => (forcedImpl (envE D Nn) slot input).run s >>= fun mid =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) =
      ((forcedImpl envL slot input).run s >>= fun mid => runWith (forcedImpl envL slot) (next mid.1) mid.2) := by
  simp only [hE, hL]
  calc _ = (rowsLaw >>= fun D => X >>= fun mid => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) :=
        bind_congr fun D => RetainedObservation.bind_comm _ _ _
    _ = (X >>= fun mid => rowsLaw >>= fun D => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) := RetainedObservation.bind_comm _ _ _
    _ = _ := bind_congr fun mid => ih mid.1 mid.2
theorem avg_fresh_row {α : Type} (slot : Nat) (x : HashInput) (hx : x ∈ digestInputs) (s : WStateL) (b : Bool) (next : HashOutput → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (rowVal D x))
        { s with memory := s.memory.readRow x (rowVal D x) b }) =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) >>= fun a =>
        forcedRun envL slot (next a) { s with memory := s.memory.readRow x a b }) := by
  have hrv : ∀ D : digestInputs → HashOutput, rowVal D x = D ⟨x, hx⟩ := fun D => by rw [rowVal, dif_pos hx]
  simp only [hrv]
  rw [rowsLaw, uniform_update (⟨x, hx⟩ : digestInputs) (fun a D => noncesLaw >>= fun Nn =>
    forcedRun (envE D Nn) slot (next a) { s with memory := s.memory.readRow x a b })]
  · refine bind_congr fun a => ?_
    rw [← rowsLaw]
    exact ih a _
  · intro a T c
    refine bind_congr fun Nn => forced_congr _ _ _ _ slot _ _ ⟨fun y hy => ?_, fun _ _ => rfl⟩
    have hyx : y ≠ ⟨x, hx⟩ := by
      rintro rfl
      have hcached : (s.memory.readRow x a b).rows x = some a := by
        cases b
        · rw [readRow_false]
          exact QueryCache.cacheQuery_self _ _ _
        · rw [readRow_true]
          exact QueryCache.cacheQuery_self _ _ _
      change (s.memory.readRow x a b).rows x = none at hy
      rw [hcached] at hy
      cases hy
    exact Function.update_of_ne hyx _ _
theorem avg_fresh_nonce {α : Type} (slot : Nat) (m : Message) (s : WStateL)
    (next : Digest → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m))
        { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v =>
        forcedRun envL slot (next v) { s with memory := s.memory.drawNonce m v }) := by
  have step : ∀ D : digestInputs → HashOutput,
      (noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m)) { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v => noncesLaw >>= fun Nn =>
        forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v }) := by
    intro D
    rw [noncesLaw]
    refine uniform_update m (fun v Nn => forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v })
      fun v T c => forced_congr _ _ _ _ slot _ _ ⟨fun _ _ => rfl, fun m' hm' => ?_⟩
    have hmm : m' ≠ m := by
      rintro rfl
      change Function.update s.memory.nonces m' (some v) m' = none at hm'
      rw [Function.update_self] at hm'
      cases hm'
    exact Function.update_of_ne hmm _ _
  simp only [step]
  rw [RetainedObservation.bind_comm]
  exact bind_congr fun v => ih v _
theorem eager_lazy_core {α : Type} (slot : Nat) (W : OracleComp WSpecL α) (s : WStateL) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      simp only [forcedRun, SecretGuessObservation.runWith_pure, rowsLaw, noncesLaw, RetainedObservation.lift_bind_const]
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_coin]) (by rw [envL, step_coin])
        | expose o =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_expose]) (by rw [envL, step_expose])
        | birth x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x true }))
                  (fun D Nn => by rw [envE, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.birth x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) true }) := fun D Nn => by
                    rw [envE, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.birth x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a true })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s true next ih
                · exact avg_indep slot _ next s ih (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x true }))
                    (fun D Nn => by rw [envE, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | trial x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x false }))
                  (fun D Nn => by rw [envE, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.trial x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) false }) := fun D Nn => by
                    rw [envE, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.trial x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a false })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s false next ih
                · exact avg_indep slot _ next s ih (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x false }))
                    (fun D Nn => by rw [envE, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | nonce m =>
            cases hc : s.memory.nonces m with
            | some v =>
                exact avg_indep slot _ next s ih (pure (v, { s with memory := s.memory }))
                  (fun D Nn => by rw [envE, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
                  (by rw [envL, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
            | none =>
                have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.nonce m))).run s =
                    pure (Nn m, { s with memory := s.memory.drawNonce m (Nn m) }) := fun D Nn => by
                  rw [envE, step_nonce, nonceStep_none _ _ _ hc, liftM_map, liftM_pure, map_pure, map_pure]
                have hL : (forcedImpl envL slot (.inl (.nonce m))).run s =
                    (fun v => (v, { s with memory := s.memory.drawNonce m v })) <$>
                      (liftM (PMF.uniformOfFintype Digest) : SPMF Digest) := by
                  rw [envL, step_nonce, nonceStep_none _ _ _ hc, liftM_map, Functor.map_map]
                simp only [hE, hL, pure_bind, bind_map_left]
                exact avg_fresh_nonce slot m s next ih
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_guess, step_guess]
        have hfun : (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f c hit with memory := s.memory })) =
            (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f c hit with
                memory := s.memory })) := by
          funext hit
          rw [afterTrial_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_disclose, step_disclose]
        have hfun : (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f v with memory := s.memory })) =
            (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f v with
                memory := s.memory })) := by
          funext v
          rw [afterDisclosure_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
theorem eager_lazy {α : Type} (W : OracleComp WSpecL α) (slot : Nat) (s : WStateL) :
    (𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
      forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  rw [evalSPMF_uniform, evalSPMF_uniform]
  exact eager_lazy_core slot W s
end EagerLazy
end SigGolfCandidate.T3.Security.BPair
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsExtractChain ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry chainRow low SeenRow encodingRow entriesOf)
open SigGolfCandidate.T3M (chainP chainInputP)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono height_le' chainCount_le'
  width_le' chainP_join chainP_frontier chainP_row chain_seen)
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem SourceLeaf7.source {L : LeafAddr} (h : SourceLeaf7 L) : SourceLeaf L :=
  ⟨lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by decide) (le_trans (Extract.treeBits_le _) (by decide))), h.2⟩
theorem SourceChain7.source {a : ChainAddr} (h : SourceChain7 a) : SourceChain a := ⟨h.1.source, h.2⟩
theorem routeLeaf_source7 (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    SourceLeaf7 ⟨lay, (route index lay).2, (route index lay).1⟩ :=
  ⟨Extract.route_tree_treeBits index hindex lay, route_leaf_bound index lay⟩
theorem structuralHitSrc_mono {answers : Answers} {trace trace' : List Entry} (h : StructuralHitSrc answers trace)
    (hsub : ∀ e ∈ trace, e ∈ trace') : StructuralHitSrc answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hs, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hs, hc, hh⟩
theorem otherChainRow_intro {answers : Answers} {input : HashInput} {a : ChainAddr} {step : Nat}
    (hpos : Extract.posOf input = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
    (h : (∀ value, input ≠ chainRowW a step value) ∨ depth answers a ≤ step) : OtherChainRow answers input :=
  ⟨a, step, hpos, h⟩
/-- A structural hit from a query whose header matches a source position (C2/C3: the hit compares the half
`pos.proj` that the position's honest value uses). -/
theorem structuralHit_intro {answers : Answers} {qs : List Spec.Domain} (pos : Extract.Pos) (actual : HashInput)
    (hb : pos.Bounded) (hsrc : PosSource pos) (hq : (.inl (.inr actual) : Spec.Domain) ∈ qs)
    (hhit : Extract.HashHitAt answers pos (Extract.honestInput answers pos) actual)
    (hsame : Extract.SameHeader actual (Extract.honestInput answers pos))
    (hclass : StructuralClass answers actual pos) :
    StructuralHitSrc answers (entriesOf answers qs) :=
  ⟨pos, actual, _, mem_entriesOf hq,
    Extract.posOf_key_eq hb (hsame.1.trans (Extract.honestInput_length answers pos))
      (hsame.2.trans (Extract.hdrKey_honestInput answers hb)),
    hb, hsrc, hclass, hhit⟩
/-- `structuralHit_intro` for a position whose honest value is the low half. -/
theorem structuralHit_intro_low {answers : Answers} {qs : List Spec.Domain} (pos : Extract.Pos) (actual : HashInput)
    (hb : pos.Bounded) (hsrc : PosSource pos) (hq : (.inl (.inr actual) : Spec.Domain) ∈ qs)
    (hhit : HashHit answers (Extract.honestInput answers pos) actual)
    (hsame : Extract.SameHeader actual (Extract.honestInput answers pos))
    (hclass : StructuralClass answers actual pos) (hp : pos.proj = fun a => a.extractLsb' 0 128) :
    StructuralHitSrc answers (entriesOf answers qs) :=
  structuralHit_intro pos actual hb hsrc hq (Extract.hashHitAt_of_low hp hhit) hsame hclass
/-! ### Half-aware hash paths (C2/C3 FULL)
`hashPathW high input` is `hashPath` whose step `s` keeps the half `high s` of its output. -/
def hashPathW (high : Nat → Bool) (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => WCT9.halfHash (high step) (input step value)) initial
noncomputable def pathValueW (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (count : Nat) : Digest :=
  evalWithAnswerFn answers (hashPathW high input count initial)
noncomputable def pathInputW (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) : HashInput := input step (pathValueW answers high input initial step)
/-- A different input whose output agrees with the honest one on the half `high`. -/
def HashHitH (high : Bool) (answers : Answers) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧
    WCT9.halfOf high (answers (.inl (.inr actual))) = WCT9.halfOf high (answers (.inl (.inr honest)))
theorem hashHitAt_iff (answers : Answers) (pos : Extract.Pos) (honest actual : HashInput) :
    Extract.HashHitAt answers pos honest actual ↔ HashHitH pos.high answers honest actual := by
  unfold Extract.HashHitAt HashHitH
  rw [Extract.Pos.proj_eq]
  rfl
theorem hashPathW_succ (high : Nat → Bool) (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPathW high input (count + 1) initial =
      (hashPathW high input count initial >>= fun value => WCT9.halfHash (high count) (input count value)) := by
  simp [hashPathW, List.range_succ, List.foldlM_append]
@[simp] theorem pathValueW_zero (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) : pathValueW answers high input initial 0 = initial := rfl
theorem pathValueW_succ (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) :
    pathValueW answers high input initial (step + 1) =
      WCT9.halfOf (high step) (answers (.inl (.inr (pad64 (pathInputW answers high input initial step))))) := by
  simp only [pathValueW, hashPathW_succ, evalWithAnswerFn_bind, pathInputW]
  exact eval_halfHash' _ _ _
theorem pathInputW_queried (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (count step : Nat) (hstep : step < count) :
    .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈
      queried answers (hashPathW high input count initial) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [hashPathW_succ, queried_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
      · exact List.mem_append_left _ (ih hlt)
      · apply List.mem_append_right
        rw [queried_halfHash']
        exact List.mem_singleton_self _
theorem hashPathW_join_core (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      WCT9.halfOf (high step) (answers (.inl (.inr (pad64 (honestInput step))))) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValueW answers high input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count →
        Good step ∧ pad64 (pathInputW answers high input initial step) = pad64 (honestInput step)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈
          queried answers (hashPathW high input count initial) ∧
        HashHitH (high step) answers (pad64 (honestInput step)) (pad64 (pathInputW answers high input initial step)) ∧
        ∀ later, step < later → later < count →
          Good later ∧ pad64 (pathInputW answers high input initial later) = pad64 (honestInput later) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInputW answers high input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit, hlater⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact ⟨hgood, heq⟩
        · refine Or.inr ⟨step, by omega, pathInputW_queried answers high input initial _ _ (by omega), hhit, ?_⟩
          intro later h1 h2
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with hlt | rfl
          · exact hlater later h1 hlt
          · exact ⟨hgood, heq⟩
      · right
        refine ⟨count, by omega, pathInputW_queried answers high input initial _ _ (by omega), ⟨heq, ?_⟩,
          fun later h1 h2 => by omega⟩
        rw [pathValueW_succ] at reaches
        exact reaches.trans (reference count (by omega)).symm
theorem pathValueW_succ_of_half (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (initial : Digest) (step : Nat) (next : Digest)
    (href : WCT9.halfOf (high step) (answers (.inl (.inr (pad64 (honestInput step))))) = next)
    (hhalf : WCT9.halfOf (high step) (answers (.inl (.inr (pad64 (pathInputW answers high input initial step))))) =
      WCT9.halfOf (high step) (answers (.inl (.inr (pad64 (honestInput step)))))) :
    pathValueW answers high input initial (step + 1) = next := by
  rw [pathValueW_succ, hhalf]
  exact href
theorem hashPathW_join (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      WCT9.halfOf (high step) (answers (.inl (.inr (pad64 (honestInput step))))) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValueW answers high input initial count = target count) :
    (initial = target 0 ∧
      (∀ step, step < count → Good step ∧ pad64 (pathInputW answers high input initial step) = pad64 (honestInput step)) ∧
      ∀ s, s ≤ count → pathValueW answers high input initial s = target s) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈ queried answers (hashPathW high input count initial) ∧
      HashHitH (high step) answers (pad64 (honestInput step)) (pad64 (pathInputW answers high input initial step)) ∧
      (∀ later, step < later → later < count →
        Good later ∧ pad64 (pathInputW answers high input initial later) = pad64 (honestInput later)) ∧
      ∀ s, step < s → s ≤ count → pathValueW answers high input initial s = target s := by
  rcases hashPathW_join_core answers high input honestInput target Good initial count reference parse reaches with
    ⟨hinit, hall⟩ | ⟨step, hstep, hq, hhit, hlater⟩
  · refine Or.inl ⟨hinit, hall, ?_⟩
    intro s hs
    induction s with
    | zero => exact hinit
    | succ s ih =>
        exact pathValueW_succ_of_half answers high input honestInput initial s _ (reference s (by omega))
          (by rw [(hall s (by omega)).2])
  · refine Or.inr ⟨step, hstep, hq, hhit, hlater, ?_⟩
    intro s hs hsc
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rcases Nat.lt_or_ge step k with hk | hk
    · exact pathValueW_succ_of_half answers high input honestInput initial k _ (reference k (by omega))
        (by rw [(hlater k hk (by omega)).2])
    · have hk' : k = step := by omega
      subst hk'
      exact pathValueW_succ_of_half answers high input honestInput initial k _ (reference k (by omega)) hhit.2
/-! ### The verifier chain `chainPW` (C3: chain 0 of a lower layer keeps the high half of its step 6) -/
def chainHighFrom (lay : Layer) (i start : Nat) : Nat → Bool := fun step => WCT9.chainHigh lay i (start + step)
theorem chainPW_eq_hashPathW (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (initial : Digest) :
    chainPW lay tree leaf i start count pad0 pad1 headerPad initial =
      hashPathW (chainHighFrom lay i start) (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) count initial := by
  unfold chainPW hashPathW
  rw [List.range'_eq_map_range, List.foldlM_map]
  rfl
theorem honestChainValueW_ref (answers : Answers) (lay : Layer) (tree leaf i start : Nat) (seed : Digest)
    (step : Nat) :
    WCT9.halfOf (chainHighFrom lay i start step) (answers (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i
      (start + step) (honestChainValueW answers lay tree leaf i seed (start + step))))))) =
      honestChainValueW answers lay tree leaf i seed (start + (step + 1)) := by
  rw [← Nat.add_assoc]
  exact honestChainValueW_succ answers lay tree leaf i seed (start + step)
theorem chainPW_join (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainPW lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValueW answers lay tree leaf i seed (start + count)) :
    (value = honestChainValueW answers lay tree leaf i seed start ∧ (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      ∀ s, s ≤ count → pathValueW answers (chainHighFrom lay i start)
        (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValueW answers lay tree leaf i seed (start + s)) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInputW answers (chainHighFrom lay i start)
        (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHitH (WCT9.chainHigh lay i (start + step)) answers
        (pad64 (WCT9.chainInputW lay tree leaf i (start + step)
          (honestChainValueW answers lay tree leaf i seed (start + step))))
        (pad64 (pathInputW answers (chainHighFrom lay i start)
          (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (step + 1 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      (∀ later, step < later → later < count →
        pathInputW answers (chainHighFrom lay i start) (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad)
            value later =
          WCT9.chainInputW lay tree leaf i (start + later)
            (honestChainValueW answers lay tree leaf i seed (start + later))) ∧
      ∀ s, step < s → s ≤ count → pathValueW answers (chainHighFrom lay i start)
          (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValueW answers lay tree leaf i seed (start + s) := by
  rw [chainPW_eq_hashPathW] at reaches ⊢
  have h := hashPathW_join answers (chainHighFrom lay i start) (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad)
    (fun step => WCT9.chainInputW lay tree leaf i (start + step)
      (honestChainValueW answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValueW answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => honestChainValueW_ref answers lay tree leaf i start seed step)
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [Extract.chainPathInputW, chainInputW_eq_zero _ _ _ _ _ _ ht hl hi hs, pad64_chainInputPW] at heq
      obtain ⟨hp0, hhp, hp1, hv⟩ := chainInputPW_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, hlater, hvals⟩
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => (hpads 0 hcount).1, hvals⟩
  · refine Or.inr ⟨step, hstep, hq, hhit, fun h => (hlater (step + 1) (by omega) h).1, ?_, hvals⟩
    intro later h1 h2
    have he := (hlater later h1 h2).2
    simp only [pathInputW, Extract.chainPathInputW, WCT9.chainInputW_padded, pad64_chainInputPW] at he ⊢
    exact he
theorem chainPW_frontier (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainPW lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValueW answers lay tree leaf i seed (start + count))
    (W : Nat) (hW : start < W) (hWc : W ≤ start + count) :
    (∃ step, step < count ∧
      .inl (.inr (pad64 (pathInputW answers (chainHighFrom lay i start)
        (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHitH (WCT9.chainHigh lay i (start + step)) answers
        (pad64 (WCT9.chainInputW lay tree leaf i (start + step)
          (honestChainValueW answers lay tree leaf i seed (start + step))))
        (pad64 (pathInputW answers (chainHighFrom lay i start)
          (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ W ≤ start + step)) ∨
    (pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0 ∧
      pathValueW answers (chainHighFrom lay i start) (Extract.chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value
        (W - start) = honestChainValueW answers lay tree leaf i seed W) := by
  rcases chainPW_join answers lay tree leaf i start count pad0 pad1 headerPad value seed ht hl hi hsteps reaches with
    ⟨_, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, _, _, hvals⟩
  · obtain ⟨h0, h1, hh⟩ := hpads (by omega)
    refine Or.inr ⟨h0, h1, hh, ?_⟩
    rw [hvals (W - start) (by omega), Nat.add_sub_cancel' (le_of_lt hW)]
  · by_cases hp : pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0
    · by_cases hs : W ≤ start + step
      · exact Or.inl ⟨step, hstep, hq, hhit, Or.inr hs⟩
      · refine Or.inr ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
        rw [hvals (W - start) (by omega) (by omega), Nat.add_sub_cancel' (le_of_lt hW)]
    · exact Or.inl ⟨step, hstep, hq, hhit, Or.inl hp⟩
theorem chainPW_row (answers : Answers) (a : ChainAddr) (start count : Nat) (value : Digest) (s : Nat)
    (ht : a.key.tree < 2^31) (hl : a.key.leaf < 4096) (hi : a.chain < 64)
    (hsteps : start + count ≤ 8) (hs : s < count) :
    (.inl (.inr (chainRowW a (start + s)
        (pathValueW answers (chainHighFrom a.key.lay a.chain start)
          (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))) : Spec.Domain) ∈
      queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value) ∧
    rowHalf a (start + s) (answers (.inl (.inr (chainRowW a (start + s)
        (pathValueW answers (chainHighFrom a.key.lay a.chain start)
          (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))))) =
      pathValueW answers (chainHighFrom a.key.lay a.chain start)
        (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (s + 1) := by
  have hrow : pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
      (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) =
      chainRowW a (start + s)
        (pathValueW answers (chainHighFrom a.key.lay a.chain start)
          (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) := by
    simp only [pathInputW, Extract.chainPathInputW, pad64_chainInputPW, chainRowW]
    exact (chainInputW_eq_zero a.key.lay a.key.tree a.key.leaf a.chain (start + s) _ ht hl hi (by omega)).symm
  constructor
  · rw [chainPW_eq_hashPathW, ← hrow]
    exact pathInputW_queried answers _ (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value
      count s hs
  · rw [pathValueW_succ, hrow]
    rfl
theorem chainW_seen (answers : Answers) (a : ChainAddr) (start count : Nat) (value out : Digest)
    (qs : List Spec.Domain)
    (ht : a.key.tree < 2^31) (hl : a.key.leaf < 4096) (hi : a.chain < 64)
    (hsteps : start + count ≤ 8)
    (hsub : ∀ q ∈ queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value), q ∈ qs)
    (W : Nat) (hW : start < W) (hWc : W ≤ start + count)
    (hval : pathValueW answers (chainHighFrom a.key.lay a.chain start)
      (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (W - start) = out) :
    (∃ x, SeenRowW (entriesOf answers qs) a (W - 1) x out) ∧
      (start + 2 ≤ W → ∃ y x, SeenRowW (entriesOf answers qs) a (W - 2) y x ∧
        SeenRowW (entriesOf answers qs) a (W - 1) x out) := by
  have hlast := chainPW_row answers a start count value (W - 1 - start) ht hl hi hsteps (by omega)
  have hstep1 : start + (W - 1 - start) = W - 1 := by omega
  have hsucc1 : W - 1 - start + 1 = W - start := by omega
  rw [hstep1, hsucc1, hval] at hlast
  have hcontact : SeenRowW (entriesOf answers qs) a (W - 1) _ out := ⟨_, mem_entriesOf (hsub _ hlast.1), hlast.2⟩
  refine ⟨⟨_, hcontact⟩, fun h2 => ?_⟩
  have hprev := chainPW_row answers a start count value (W - 2 - start) ht hl hi hsteps (by omega)
  have hstep2 : start + (W - 2 - start) = W - 2 := by omega
  have hsucc2 : W - 2 - start + 1 = W - 1 - start := by omega
  rw [hstep2, hsucc2] at hprev
  exact ⟨_, _, ⟨_, mem_entriesOf (hsub _ hprev.1), hprev.2⟩, hcontact⟩
theorem chain_bounded {a : ChainAddr} {step : Nat} (hsrc : SourceChain a)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain) :
    (Extract.Pos.chain a.key.lay a.key.tree a.key.leaf a.chain step).Bounded := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := hsrc
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' _)
  have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (width_le' _ _)
  have hcc := chainCount_le' a.key.lay
  refine ⟨by omega, by omega, by omega, by omega⟩
theorem structuralHit_chain {answers : Answers} {qs : List Spec.Domain} (a : ChainAddr) (step : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (v : Digest)
    (hq : (.inl (.inr (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) : Spec.Domain) ∈ qs)
    (hsrc : SourceChain a) (htb : a.key.tree < 2 ^ Extract.treeBits a.key.lay)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain)
    (hhit : HashHitH (WCT9.chainHigh a.key.lay a.chain step) answers
      (Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
      (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v))
    (hclass : ¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ step) :
    StructuralHitSrc answers (entriesOf answers qs) := by
  have hb := chain_bounded hsrc hstep
  have hlen : (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v).length = 64 := by
    exact chainInputPW_length _ _ _ _ _ _ _ _ _
  have hpos : Extract.posOf (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v) =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) := by
    apply Extract.posOf_key_eq hb (hlen.trans rfl)
    -- C4: a chain header's low word carries type byte 193, so it is no top label.
    have hT : ¬ Extract.TopLow
        (Extract.hdrBlock (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) := by
      rw [Extract.hdrBlock, chainInputPW_header, Extract.topLow_bytesLE_iff, SigGolfCandidate.T3M.chainHeaderP,
        append64_lowNat, chainHeader_low, chainHeaderFlaggedLow_toNat]
      have := chainHeaderLow_band a.key.lay a.key.tree a.key.leaf a.chain step
      split_ifs <;> omega
    rw [Extract.hdrKey_of_len64 hlen hT, Extract.hdrBlock, chainInputPW_header,
      Extract.canonicalHeader_chainHeaderP]
    exact Extract.Pos.canonicalHeader_eq (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb
  refine ⟨_, _, _, mem_entriesOf hq, hpos, hb, ⟨htb, hsrc.1.2, hsrc.2, hstep⟩, ?_,
    (hashHitAt_iff _ _ _ _).mpr hhit⟩
  refine otherChainRow_intro hpos ?_
  rcases hclass with hpad | hdepth
  · refine Or.inl fun value he => hpad ?_
    rw [chainRowW, chainInputW_eq_zero _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega)] at he
    obtain ⟨h0, hh, h1, _⟩ := chainInputPW_fields he
    exact ⟨h0, h1, hh⟩
  · exact Or.inr hdepth
theorem chain_cases (answers : Answers) (a : ChainAddr) (start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest)
    (qs : List Spec.Domain)
    (hsub : ∀ q ∈ queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value),
      q ∈ qs)
    (hsrc : SourceChain a) (htb : a.key.tree < 2 ^ Extract.treeBits a.key.lay)
    (hcount : start + count < 2 ^ width a.key.lay a.chain)
    (hdepth : depth answers a ≤ start + count)
    (reaches : evalWithAnswerFn answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) =
      honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + count)) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
      ((depth answers a ≤ start →
          value = honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) start ∧
          (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∧
        (start < depth answers a →
          ContactAt answers (entriesOf answers qs) a ∧
            (start + 2 ≤ depth answers a → TwoEdgeAt answers (entriesOf answers qs) a))) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers qs)
  · exact Or.inl hS
  right
  have ht := hsrc.1.1
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' a.key.lay)
  have hl : a.key.leaf < 4096 := lt_of_lt_of_le hsrc.1.2 hh
  have hi : a.chain < 64 := lt_of_lt_of_le hsrc.2 (by have := chainCount_le' a.key.lay; omega)
  have hc7 : start + count ≤ 7 := by
    have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by decide) (width_le' a.key.lay a.chain)
    omega
  have hc8 : start + count ≤ 8 := by omega
  have hit : ∀ step, step < count →
      .inl (.inr (pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
        (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) →
      HashHitH (WCT9.chainHigh a.key.lay a.chain (start + step)) answers
        (pad64 (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))))
        (pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
          (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step)) →
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ start + step) → False := by
    intro step hstep hq hhit hclass
    apply hS
    simp only [pathInputW, Extract.chainPathInputW, pad64_chainInputPW] at hq hhit
    refine structuralHit_chain a (start + step) pad0 pad1 headerPad _ (hsub _ hq) hsrc htb (by omega) ?_ hclass
    have he : Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain (start + step)) =
        pad64 (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))) := by
      simp only [Extract.honestInput]
      try rfl
    rw [he]
    exact hhit
  constructor
  · intro hle
    rcases chainPW_join answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches with
      ⟨hval, hpads, -⟩ | ⟨step, hstep, hq, hhit, -⟩
    · exact ⟨hval, hpads⟩
    · exact (hit step hstep hq hhit (Or.inr (by omega))).elim
  · intro hlt
    rcases chainPW_frontier answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches (depth answers a)
        hlt hdepth with
      ⟨step, hstep, hq, hhit, hclass⟩ | ⟨h0, h1, hh, hval⟩
    · exact (hit step hstep hq hhit hclass).elim
    · subst h0 h1 hh
      obtain ⟨⟨x, hx⟩, htwo⟩ := chainW_seen answers a start count value _ qs ht hl hi hc8 hsub (depth answers a)
        hlt hdepth hval
      exact ⟨⟨by omega, x, hx⟩, fun h2 => ⟨by omega, htwo h2⟩⟩
end ClaudeWCT.W9.T3.Security.WotsExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry chainRow low SeenRow encodingRow entriesOf)
open SigGolfCandidate.T3M (chainP chainInputP)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3.Security.WotsExtract (SourceLeaf7 SourceChain7 PosSource)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono height_le' chainCount_le'
  width_le' chainP_join chainP_frontier chainP_row chain_seen)
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open ClaudeWCT.W9.T3.Security.WotsExtract (SourceLeaf7.source SourceChain7.source routeLeaf_source7)
-- Stage 2 (C2/C3, #866): the half-aware chain extraction of the legacy section.
open ClaudeWCT.W9.T3.Security.WotsExtract (HashHitH hashHitAt_iff chainHighFrom pathInputW chainPW_join
  chainPW_frontier chainW_seen)
variable {messages : LeafAddr → WCT9.LayerMsg}
def MainPosition : Extract.Pos → Prop
  | .chain .. | .leaf .. | .node .. => True
  | _ => False

def StructuralHitSrc (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ PosSource position ∧ CanonicalRef.StructuralClass answers messages input position ∧
    MainPosition position ∧ Extract.HashHitAt answers position (Extract.honestInput answers position) input
theorem structuralHitSrc_mono {answers : Answers} {trace trace' : List Entry} (h : StructuralHitSrc answers messages trace)
    (hsub : ∀ e ∈ trace, e ∈ trace') : StructuralHitSrc answers messages trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hs, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hs, hc, hh⟩
theorem otherChainRow_intro {answers : Answers} {input : HashInput} {a : ChainAddr} {step : Nat}
    (hpos : Extract.posOf input = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
    (h : (∀ value, input ≠ chainRowW a step value) ∨ CanonicalRef.depth answers messages a ≤ step) : CanonicalRef.OtherChainRow answers messages input :=
  ⟨a, step, hpos, h⟩
/-- A structural hit from a query whose header matches a source position (C2/C3: the hit compares the half
`pos.proj` that the position's honest value uses). -/
theorem structuralHit_intro {answers : Answers} {qs : List Spec.Domain} (pos : Extract.Pos) (actual : HashInput)
    (hb : pos.Bounded) (hsrc : PosSource pos) (hq : (.inl (.inr actual) : Spec.Domain) ∈ qs)
    (hhit : Extract.HashHitAt answers pos (Extract.honestInput answers pos) actual)
    (hsame : Extract.SameHeader actual (Extract.honestInput answers pos))
    (hclass : CanonicalRef.StructuralClass answers messages actual pos) (hmain : MainPosition pos) :
    StructuralHitSrc answers messages (entriesOf answers qs) :=
  ⟨pos, actual, _, mem_entriesOf hq,
    Extract.posOf_key_eq hb (hsame.1.trans (Extract.honestInput_length answers pos))
      (hsame.2.trans (Extract.hdrKey_honestInput answers hb)),
    hb, hsrc, hclass, hmain, hhit⟩
/-- `structuralHit_intro` for a position whose honest value is the low half. -/
theorem structuralHit_intro_low {answers : Answers} {qs : List Spec.Domain} (pos : Extract.Pos) (actual : HashInput)
    (hb : pos.Bounded) (hsrc : PosSource pos) (hq : (.inl (.inr actual) : Spec.Domain) ∈ qs)
    (hhit : HashHit answers (Extract.honestInput answers pos) actual)
    (hsame : Extract.SameHeader actual (Extract.honestInput answers pos))
    (hclass : CanonicalRef.StructuralClass answers messages actual pos) (hmain : MainPosition pos) (hp : pos.proj = fun a => a.extractLsb' 0 128) :
    StructuralHitSrc answers messages (entriesOf answers qs) :=
  structuralHit_intro pos actual hb hsrc hq (Extract.hashHitAt_of_low hp hhit) hsame hclass hmain
theorem chain_bounded {a : ChainAddr} {step : Nat} (hsrc : SourceChain a)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain) :
    (Extract.Pos.chain a.key.lay a.key.tree a.key.leaf a.chain step).Bounded := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := hsrc
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' _)
  have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (width_le' _ _)
  have hcc := chainCount_le' a.key.lay
  refine ⟨by omega, by omega, by omega, by omega⟩
theorem structuralHit_chain {answers : Answers} {qs : List Spec.Domain} (a : ChainAddr) (step : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (v : Digest)
    (hq : (.inl (.inr (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) : Spec.Domain) ∈ qs)
    (hsrc : SourceChain a) (htb : a.key.tree < 2 ^ Extract.treeBits a.key.lay)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain)
    (hhit : HashHitH (WCT9.chainHigh a.key.lay a.chain step) answers
      (Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
      (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v))
    (hclass : ¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ CanonicalRef.depth answers messages a ≤ step) :
    StructuralHitSrc answers messages (entriesOf answers qs) := by
  have hb := chain_bounded hsrc hstep
  have hlen : (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v).length = 64 := by
    exact chainInputPW_length _ _ _ _ _ _ _ _ _
  have hpos : Extract.posOf (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v) =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) := by
    apply Extract.posOf_key_eq hb (hlen.trans rfl)
    -- C4: a chain header's low word carries type byte 193, so it is no top label.
    have hT : ¬ Extract.TopLow
        (Extract.hdrBlock (chainInputPW a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) := by
      rw [Extract.hdrBlock, chainInputPW_header, Extract.topLow_bytesLE_iff, SigGolfCandidate.T3M.chainHeaderP,
        append64_lowNat, chainHeader_low, chainHeaderFlaggedLow_toNat]
      have := chainHeaderLow_band a.key.lay a.key.tree a.key.leaf a.chain step
      split_ifs <;> omega
    rw [Extract.hdrKey_of_len64 hlen hT, Extract.hdrBlock, chainInputPW_header,
      Extract.canonicalHeader_chainHeaderP]
    exact Extract.Pos.canonicalHeader_eq (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb
  refine ⟨_, _, _, mem_entriesOf hq, hpos, hb, ⟨htb, hsrc.1.2, hsrc.2, hstep⟩, ?_, trivial,
    (hashHitAt_iff _ _ _ _).mpr hhit⟩
  refine otherChainRow_intro hpos ?_
  rcases hclass with hpad | hdepth
  · refine Or.inl fun value he => hpad ?_
    rw [chainRowW, chainInputW_eq_zero _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega)] at he
    obtain ⟨h0, hh, h1, _⟩ := chainInputPW_fields he
    exact ⟨h0, h1, hh⟩
  · exact Or.inr hdepth
theorem chain_cases (answers : Answers) (a : ChainAddr) (start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest)
    (qs : List Spec.Domain)
    (hsub : ∀ q ∈ queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value),
      q ∈ qs)
    (hsrc : SourceChain a) (htb : a.key.tree < 2 ^ Extract.treeBits a.key.lay)
    (hcount : start + count < 2 ^ width a.key.lay a.chain)
    (hdepth : CanonicalRef.depth answers messages a ≤ start + count)
    (reaches : evalWithAnswerFn answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) =
      honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + count)) :
    StructuralHitSrc answers messages (entriesOf answers qs) ∨
      ((CanonicalRef.depth answers messages a ≤ start →
          value = honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) start ∧
          (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∧
        (start < CanonicalRef.depth answers messages a →
          CanonicalRef.ContactAt answers messages (entriesOf answers qs) a ∧
            (start + 2 ≤ CanonicalRef.depth answers messages a → CanonicalRef.TwoEdgeAt answers messages (entriesOf answers qs) a))) := by
  classical
  by_cases hS : StructuralHitSrc answers messages (entriesOf answers qs)
  · exact Or.inl hS
  right
  have ht := hsrc.1.1
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (height_le' a.key.lay)
  have hl : a.key.leaf < 4096 := lt_of_lt_of_le hsrc.1.2 hh
  have hi : a.chain < 64 := lt_of_lt_of_le hsrc.2 (by have := chainCount_le' a.key.lay; omega)
  have hc7 : start + count ≤ 7 := by
    have hw : 2 ^ width a.key.lay a.chain ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by decide) (width_le' a.key.lay a.chain)
    omega
  have hc8 : start + count ≤ 8 := by omega
  have hit : ∀ step, step < count →
      .inl (.inr (pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
        (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) →
      HashHitH (WCT9.chainHigh a.key.lay a.chain (start + step)) answers
        (pad64 (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))))
        (pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
          (Extract.chainPathInputW a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step)) →
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ CanonicalRef.depth answers messages a ≤ start + step) → False := by
    intro step hstep hq hhit hclass
    apply hS
    simp only [pathInputW, Extract.chainPathInputW, pad64_chainInputPW] at hq hhit
    refine structuralHit_chain a (start + step) pad0 pad1 headerPad _ (hsub _ hq) hsrc htb (by omega) ?_ hclass
    have he : Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain (start + step)) =
        pad64 (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))) := by
      simp only [Extract.honestInput]
      try rfl
    rw [he]
    exact hhit
  constructor
  · intro hle
    rcases chainPW_join answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches with
      ⟨hval, hpads, -⟩ | ⟨step, hstep, hq, hhit, -⟩
    · exact ⟨hval, hpads⟩
    · exact (hit step hstep hq hhit (Or.inr (by omega))).elim
  · intro hlt
    rcases chainPW_frontier answers a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) ht hl hi (Or.inr hc8) reaches (CanonicalRef.depth answers messages a)
        hlt hdepth with
      ⟨step, hstep, hq, hhit, hclass⟩ | ⟨h0, h1, hh, hval⟩
    · exact (hit step hstep hq hhit hclass).elim
    · subst h0 h1 hh
      obtain ⟨⟨x, hx⟩, htwo⟩ := chainW_seen answers a start count value _ qs ht hl hi hc8 hsub (CanonicalRef.depth answers messages a)
        hlt hdepth hval
      exact ⟨⟨by omega, x, hx⟩, fun h2 => ⟨by omega, htwo h2⟩⟩
end ClaudeWCT.W9.T3.Security.CanonicalExtract
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsExtractWord ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf route_split route_tree_succ route_forest)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem referenceInput_ne (answers : Answers) (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfit : Extract.msgFits L.lay msg)
    {digits : List Nat} (hd : decode L.lay (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L msg ctr pad))))) = some digits)
    (hne : msg ≠ leafMsg answers L ∨ digits ≠ referenceDigits answers L) :
    referenceInput answers L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers L with
  | none => rw [hs] at h; simp at h
  | some s =>
      obtain ⟨c, w'⟩ := s
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hm, hc, -⟩ := BC.layerEncodingRow_injective_leaf (msgFits_leafMsg answers L) hfit h
      rw [← h] at hd
      subst hm hc
      have hdec := referenceSearch_decode answers L hs
      have hw : referenceDigits answers L = w' := by unfold referenceDigits; rw [hs]; rfl
      have hdw : digits = w' := Option.some.inj (hd.symm.trans hdec)
      rcases hne with hne | hne
      · exact hne rfl
      · exact hne (hdw.trans hw.symm)
/-- The verifier's encoding row as an `encRow` (the row pad's high component is the XOR mask `hi ^^^ 1`). -/
theorem encRow_wit (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96) (padR : Digest)
    (hi : BitVec 64) :
    encRow L msg counter (pad, padR, hi ^^^ 1) =
      pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad padR hi) := by
  show pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad padR ((hi ^^^ 1) ^^^ 1)) = _
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
theorem xor_one_inj {a b : BitVec 64} (h : a ^^^ 1 = b ^^^ 1) : a = b := by
  have := congrArg (· ^^^ (1 : BitVec 64)) h
  simpa [BitVec.xor_assoc] using this
/-- A row whose 12-byte pad is nonzero or whose high-word mask is nonzero (C2/C3 FULL: row high word `≠ 1`) is not
the reference row. -/
theorem referenceInput_ne_pad (answers : Answers) (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfit : Extract.msgFits L.lay msg) (hpad : pad.1 ≠ 0 ∨ pad.2.2 ≠ 0) :
    referenceInput answers L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers L with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨-, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf (msgFits_leafMsg answers L) hfit h
      have hh := BC.layerEncodingRow_hi_eq h
      rcases hpad with hpad | hpad
      · exact hpad hp.symm
      · exact hpad (xor_one_inj hh).symm
theorem leafMsg_route (answers : Answers) (index : Nat) (lay : Layer) (hindex : index < 2 ^ 31) :
    leafMsg answers (routeLeaf index lay) = Extract.honestMsg answers index lay := by
  unfold leafMsg Extract.honestMsg
  simp only [routeLeaf]
  by_cases h : lay.val < 3
  · rw [dif_pos h, dif_pos h, route_tree_succ index lay h]
  · rw [dif_neg h, dif_neg h, route_forest index lay h, Nat.mod_eq_of_lt hindex]
end ClaudeWCT.W9.T3.Security.WotsExtract
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsExtractLayer ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf word_cases)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (chainP)
open ClaudeWCT.W9.T3M (layerP wchainPads wchainHeaderPad wmerklePad wmerkleHigh wpath wvalueFor wbcCtr wbcPad wbcRight
  wbcHigh wleafHigh wtopLeafPad)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain seenRow_mono entriesOf_mono mem_entriesOf routeLeaf
  routeLeaf_source)
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def WotsPrimitiveSrc (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, SourceLeaf7 L ∧ EncodingMatchAt answers trace L) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain7 a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem WotsPrimitiveSrc.mono (h : WotsPrimitiveSrc answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveSrc answers trace' := by
  rcases h with ⟨L, hL, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨L, hL, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end mono
theorem leaf_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (qs : List Spec.Domain)
    (hsubL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ qs)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      treeValue (WCT9.wotsTree answers lay (route index lay).2) 0 (route index lay).1) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
    ((∀ i, i < chainCount lay →
      (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
        ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
            TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) ∧
      wleafHigh w lay = 0) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers qs)
  · exact Or.inl hS
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have hqC : ∀ q ∈ queried answers (Extract.layerChains w index lay digits), q ∈ qs := by
    intro q hq
    apply hsubL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  rw [WCT9.wotsTree_leaf answers lay _ _ hleafB, Extract.layerLeafP_eq, evalWithAnswerFn_bind] at hv0
  have hends : evalWithAnswerFn answers (Extract.layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i))) := by
    rw [Extract.layerChains, Correctness.eval_mapM]
    exact Extract.map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i)))
  rcases Extract.leafHashW_extract answers lay (route index lay).2 (route index lay).1 (wtopLeafPad w)
      (wleafHigh w lay) (evalWithAnswerFn answers (Extract.layerChains w index lay digits))
      ((List.range (chainCount lay)).map (WCT9.wotsEnd answers lay (route index lay).2 (route index lay).1))
      (by rw [hends]; simp) (by simp) hv0 with ⟨hE, hhi⟩ | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.leaf lay (route index lay).2 (route index lay).1) _
      ⟨hleafB, Extract.route_routed_bound index lay hidx⟩
      ⟨Extract.route_tree_treeBits index hidx lay, hleafB⟩ ?_ ((Extract.hashHitAt_iff _ _ _ _).mpr hhit) hsame trivial
    apply hsubL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_right _ hq
  refine ⟨?_, hhi⟩
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hw : 2 ^ width lay i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
  have hc := Extract.chainCount_le lay
  have hreach : evalWithAnswerFn answers
      (chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
        (wchainPads w lay i).1 (wchainPads w lay i).2 (wchainHeaderPad w lay i) (wvalueFor w lay digits i)) =
      honestChainValueW answers lay (route index lay).2 (route index lay).1 i
        (WCT9.wotsSeed answers lay (route index lay).2 (route index lay).1 i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    rw [hci, Nat.add_sub_cancel' hd]; rfl
  have hsrcC : SourceChain ⟨routeLeaf index lay, i⟩ := ⟨routeLeaf_source index lay hidx, hi⟩
  have hcount : digits.getD i 0 + (maxDigit lay i - digits.getD i 0) < 2 ^ width lay i := by
    have hm := Nonbinary.maxDigit_lt_pow_width lay i
    omega
  have hdepth : depth answers ⟨routeLeaf index lay, i⟩ ≤ maxDigit lay i := depth_le answers ⟨routeLeaf index lay, i⟩ hi
  rcases chain_cases answers ⟨routeLeaf index lay, i⟩ (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
      (wchainPads w lay i).1 (wchainPads w lay i).2 (wchainHeaderPad w lay i) (wvalueFor w lay digits i) qs
      (fun q hq => hqC q (Extract.layerChains_queried answers w index lay digits (route index lay).1
        (route index lay).2 rfl rfl i hi q hq))
      hsrcC (Extract.route_tree_treeBits index hidx lay) hcount (by omega) hreach with
    hS' | ⟨hhon, hlow⟩
  · exact (hS hS').elim
  refine ⟨fun hle => ?_, hlow⟩
  obtain ⟨hval, hpads⟩ := hhon hle
  refine ⟨hval, fun hlt => ?_⟩
  obtain ⟨h0, h1, hh⟩ := hpads (by omega)
  exact ⟨Prod.ext h0 h1, hh⟩
theorem layerP_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hlay0 : lay = 0) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    StructuralHitSrc answers (entriesOf answers (queried answers (layerP w index lay digits))) ∨
    ((∀ j, j < height lay →
        wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        wmerklePad w lay (route index lay).1 j =
          WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1))) ∧
        wmerkleHigh w lay (route index lay).1 j = 0) ∧
      (∀ i, i < chainCount lay →
        (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i →
              wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
          ContactAt answers (entriesOf answers (queried answers (layerP w index lay digits)))
              ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
              TwoEdgeAt answers (entriesOf answers (queried answers (layerP w index lay digits)))
                ⟨routeLeaf index lay, i⟩))) ∧
      wleafHigh w lay = 0) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers (queried answers (layerP w index lay digits)))
  · exact Or.inl hS
  right
  have hl0 : lay.val = 0 := by rw [hlay0]; rfl
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  -- C4: the top path is a half-aware hash path of `height lay` one-word folds (as the lower paths, C2).
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [Extract.layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (Extract.hashPathW (Extract.merkleHighW lay.val (height lay) (route index lay).1)
      (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (height lay) (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [Extract.layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_right _ hq
  have hM := Extract.merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay) (wpath w lay (route index lay).1)
    (fun j => treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (WCT9.wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (Extract.honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => Extract.merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1
      hleafB step hstep)
    (by
      have h := reaches
      rw [Extract.layerP_eq_hashPathW, evalWithAnswerFn_bind] at h
      unfold Extract.pathValueW
      rw [Nat.div_eq_of_lt hleafB]
      exact h)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)))
      (pad64 (Extract.pathInputW answers (Extract.merkleHighW lay.val (height lay) (route index lay).1)
        (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (evalWithAnswerFn answers (layerLeafP w index lay digits)) step))
      ⟨htreeB, hstep, Or.inl hlay0, Extract.tree_zero_of_treeBits (Extract.route_tree_treeBits index hidx lay), ?_⟩
      ⟨Extract.route_tree_treeBits index hidx lay, hstep, ?_, Or.inl hlay0⟩ (hqM _ hq) ?_ ?_ trivial
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [Extract.hashHitAt_iff, Extract.merkle_honestInputW' answers lay]; exact hhit
    · rw [Extract.merkle_honestInputW' answers lay, Extract.pathInputW, hl0]
      exact Extract.merkleInputW_sameHeader_top _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one] at hv0
  rcases leaf_wots answers w index lay digits hidx hvalid _ hqL hv0 with hS' | ⟨hchains, hhi⟩
  · exact (hS hS').elim
  · exact ⟨fun j hj => ⟨(hpath j hj).1, (hpath j hj).2.2, (hpath j hj).2.1⟩, hchains, hhi⟩
theorem layerPairP_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (hlay : lay.val ≠ 0)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    StructuralHitSrc answers (entriesOf answers (queried answers (layerPairP w index lay digits))) ∨
    ((∀ j, j < height lay →
        wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay → wmerklePad w lay (route index lay).1 j = 0 ∧ wmerkleHigh w lay (route index lay).1 j = 0)) ∧
      (∀ i, i < chainCount lay →
        (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i →
              wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
          ContactAt answers (entriesOf answers (queried answers (layerPairP w index lay digits)))
              ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
              TwoEdgeAt answers (entriesOf answers (queried answers (layerPairP w index lay digits)))
                ⟨routeLeaf index lay, i⟩))) ∧
      wleafHigh w lay = 0) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers (queried answers (layerPairP w index lay digits)))
  · exact Or.inl hS
  right
  have hh := Extract.height_pos lay
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [Extract.layerPairP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (Extract.hashPathW (Extract.merkleHighW lay.val (height lay) (route index lay).1)
      (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (height lay - 1) (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [Extract.layerPairP_eq_hashPathW, queried_bind, queried_bind]
    exact List.mem_append_right _ (List.mem_append_left _ hq)
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨ (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by rw [← pow_succ, Nat.sub_add_cancel hh]
      rw [Nat.mul_comm, he]
      exact hleafB
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  have reaches' := reaches
  rw [Extract.layerPairP_eq_hashPathW, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at reaches'
  generalize htop : evalWithAnswerFn answers (Extract.hashPathW (Extract.merkleHighW lay.val (height lay) (route index lay).1)
      (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (height lay - 1) (evalWithAnswerFn answers (layerLeafP w index lay digits))) = top at reaches'
  have hpair : top = treeValue (WCT9.wotsTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1)) ∧
      wpath w lay (route index lay).1 (height lay - 1) =
        treeValue (WCT9.wotsTree answers lay (route index lay).2) (height lay - 1)
          ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := by
    unfold Extract.honestPair at reaches'
    rcases hq2 with h | h <;> simp only [h] at reaches' ⊢ <;>
      simp only [Nat.one_mod, if_true, if_false, Prod.mk.injEq, one_ne_zero] at reaches' <;>
      exact ⟨by first | exact reaches'.1 | exact reaches'.2, by first | exact reaches'.2 | exact reaches'.1⟩
  have hM := Extract.merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay - 1) (wpath w lay (route index lay).1)
    (fun j => treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (WCT9.wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (Extract.honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => Extract.merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1
      hleafB step (by omega))
    (by unfold Extract.pathValueW; rw [htop]; exact hpair.1)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)))
      (pad64 (Extract.pathInputW answers (Extract.merkleHighW lay.val (height lay) (route index lay).1)
        (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (evalWithAnswerFn answers (layerLeafP w index lay digits)) step))
      ⟨htreeB, by omega, Or.inr (by omega), Extract.tree_zero_of_treeBits (Extract.route_tree_treeBits index hidx lay), ?_⟩
      ⟨Extract.route_tree_treeBits index hidx lay, by omega, ?_, Or.inr (by omega)⟩
      (hqM _ hq) ?_ ?_ trivial
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [Extract.hashHitAt_iff, Extract.merkle_honestInputW' answers lay]; exact hhit
    · rw [Extract.merkle_honestInputW' answers lay, Extract.pathInputW]
      exact Extract.merkleInputW_sameHeader (Extract.lower_heap_lt128 hlay hleafB) _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one] at hv0
  rcases leaf_wots answers w index lay digits hidx hvalid _ hqL hv0 with hS' | ⟨hchains, hhi⟩
  · exact (hS hS').elim
  refine ⟨fun j hj => ?_, hchains, hhi⟩
  by_cases hjt : j < height lay - 1
  · have hl' : lay ≠ 0 := fun h => hlay (by rw [h]; rfl)
    exact ⟨(hpath j hjt).1, fun _ => ⟨(hpath j hjt).2.2.trans
      (congrFun (Extract.honestPads_lower answers hl' _ _) j), (hpath j hjt).2.1⟩⟩
  · have hj1 : j = height lay - 1 := by omega
    subst hj1
    exact ⟨hpair.2, fun h => by omega⟩
theorem frame_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hmerkle : ∀ j, j < height lay →
      wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay (route index lay).1 j =
          WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1)))) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerkleHigh w lay (route index lay).1 j = 0))
    (hleaf : wleafHigh w lay = 0)
    (hchains : ∀ i, i < chainCount lay →
      (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
        ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
            TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  classical
  have hdec : decode (routeLeaf index lay).lay
      (WCT9.encodingAnswer (routeLeaf index lay).lay (answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1)))))) = some digits := by
    rw [encRow_wit]; exact hframe.2
  have hfit' : Extract.msgFits (routeLeaf index lay).lay msg := hfit
  have hencE : (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1),
      answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1))))) ∈
        entriesOf answers qs := by
    rw [encRow_wit]; exact mem_entriesOf henc
  have hsrc : SourceLeaf7 (routeLeaf index lay) := routeLeaf_source7 index hidx lay
  have hsrcC7 : ∀ i, i < chainCount lay → SourceChain7 ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => (hsrcC7 i hi).source
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    ((hchains i hi).2 hlt).1
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  ·
    have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_, hleaf⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · by_cases hp : wbcPad w index lay = 0 ∧ wbcHigh w index lay = 1
      · exact Or.inr ⟨hm, ⟨digits, hm ▸ hframe, hshape⟩, hp⟩
      · have hpad : (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1).1 ≠ 0 ∨
            (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1).2.2 ≠ 0 := by
          by_cases hp1 : wbcPad w index lay = 0
          · right
            intro h1
            apply hp
            refine ⟨hp1, ?_⟩
            simpa using h1
          · exact Or.inl hp1
        refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1),
          _, hfit', hencE, ?_, ?_⟩)
        · exact referenceInput_ne_pad answers _ msg _ _ hfit' hpad
        · rw [← heq]; exact hdec
    · refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1),
        _, hfit', hencE, ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inl (by rw [leafMsg_route _ _ _ hidx]; exact hm))
      · rw [← heq]; exact hdec
  ·
    have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC7 i.val i.isLt,
      ⟨msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, digits, hfit', hencE,
        referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  ·
    refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact ((hchains i.val i.isLt).2 hlt).2 h2
  ·
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)
theorem layer_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay0 : lay = 0) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerP_wots answers w index lay digits hidx hlay0 hvalid reaches with hS | ⟨hmerkle, hchains, hleaf⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  have hl0 : lay.val = 0 := by rw [hlay0]; rfl
  exact frame_wots answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun _ => (hmerkle j hj).2.1, fun _ => (hmerkle j hj).2.2⟩) hleaf
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layerPair_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay : lay.val ≠ 0) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerPairP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerPairP_wots answers w index lay digits hidx hvalid hlay reaches with hS | ⟨hmerkle, hchains, hleaf⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun h => by
        rw [WCT9.honestNonce_lower answers (fun h0 => hlay (by rw [h0]; rfl)), WCT9.nonceDigest_zero]
        exact ((hmerkle j hj).2 (h.resolve_right hlay)).1,
      fun h => ((hmerkle j hj).2 (h.resolve_right hlay)).2⟩) hleaf
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
end ClaudeWCT.W9.T3.Security.WotsExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf word_cases)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3.Security.WotsExtract (SourceLeaf7 SourceChain7 SourceLeaf7.source SourceChain7.source routeLeaf_source7)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (chainP)
open ClaudeWCT.W9.T3M (layerP wchainPads wchainHeaderPad wmerklePad wpath wvalueFor wbcCtr wbcPad wbcRight)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain seenRow_mono entriesOf_mono mem_entriesOf routeLeaf
  routeLeaf_source)
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {messages : LeafAddr → WCT9.LayerMsg}
def WotsPrimitiveSrc (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Prop :=
  (∃ L, SourceLeaf7 L ∧ CanonicalRef.EncodingMatchAt answers messages trace L) ∨ StructuralHitSrc answers messages trace ∨
    (∃ a, SourceChain7 a ∧ CanonicalRef.TwoEdgeAt answers messages trace a) ∨
    (∃ a b, SourceChain7 a ∧ SourceChain7 b ∧ a ≠ b ∧ CanonicalRef.ContactAt answers messages trace a ∧ CanonicalRef.ContactAt answers messages trace b) ∨
    (∃ a, SourceChain7 a ∧ CanonicalRef.MarkerAt answers messages trace a ∧ CanonicalRef.ContactAt answers messages trace a)
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem WotsPrimitiveSrc.mono (h : WotsPrimitiveSrc answers messages trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveSrc answers messages trace' := by
  rcases h with ⟨L, hL, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨L, hL, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end mono
theorem leaf_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (qs : List Spec.Domain)
    (hsubL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ qs)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      treeValue (WCT9.wotsTree answers lay (route index lay).2) 0 (route index lay).1) :
    StructuralHitSrc answers messages (entriesOf answers qs) ∨
    ((∀ i, i < chainCount lay →
      (CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
        CanonicalRef.ContactAt answers messages (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
            CanonicalRef.TwoEdgeAt answers messages (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) ∧
      wleafHigh w lay = 0) := by
  classical
  by_cases hS : StructuralHitSrc answers messages (entriesOf answers qs)
  · exact Or.inl hS
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have hqC : ∀ q ∈ queried answers (Extract.layerChains w index lay digits), q ∈ qs := by
    intro q hq
    apply hsubL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  rw [WCT9.wotsTree_leaf answers lay _ _ hleafB, Extract.layerLeafP_eq, evalWithAnswerFn_bind] at hv0
  have hends : evalWithAnswerFn answers (Extract.layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i))) := by
    rw [Extract.layerChains, Correctness.eval_mapM]
    exact Extract.map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i)))
  rcases Extract.leafHashW_extract answers lay (route index lay).2 (route index lay).1 (wtopLeafPad w)
      (wleafHigh w lay) (evalWithAnswerFn answers (Extract.layerChains w index lay digits))
      ((List.range (chainCount lay)).map (WCT9.wotsEnd answers lay (route index lay).2 (route index lay).1))
      (by rw [hends]; simp) (by simp) hv0 with ⟨hE, hhi⟩ | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.leaf lay (route index lay).2 (route index lay).1) _
      ⟨hleafB, Extract.route_routed_bound index lay hidx⟩
      ⟨Extract.route_tree_treeBits index hidx lay, hleafB⟩ ?_ ((Extract.hashHitAt_iff _ _ _ _).mpr hhit) hsame trivial trivial
    apply hsubL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_right _ hq
  refine ⟨?_, hhi⟩
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hw : 2 ^ width lay i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
  have hc := Extract.chainCount_le lay
  have hreach : evalWithAnswerFn answers
      (chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
        (wchainPads w lay i).1 (wchainPads w lay i).2 (wchainHeaderPad w lay i) (wvalueFor w lay digits i)) =
      honestChainValueW answers lay (route index lay).2 (route index lay).1 i
        (WCT9.wotsSeed answers lay (route index lay).2 (route index lay).1 i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    rw [hci, Nat.add_sub_cancel' hd]; rfl
  have hsrcC : SourceChain ⟨routeLeaf index lay, i⟩ := ⟨routeLeaf_source index lay hidx, hi⟩
  have hcount : digits.getD i 0 + (maxDigit lay i - digits.getD i 0) < 2 ^ width lay i := by
    have hm := Nonbinary.maxDigit_lt_pow_width lay i
    omega
  have hdepth : CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ ≤ maxDigit lay i := CanonicalRef.depth_le answers messages ⟨routeLeaf index lay, i⟩ hi
  rcases chain_cases (messages := messages) answers ⟨routeLeaf index lay, i⟩ (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
      (wchainPads w lay i).1 (wchainPads w lay i).2 (wchainHeaderPad w lay i) (wvalueFor w lay digits i) qs
      (fun q hq => hqC q (Extract.layerChains_queried answers w index lay digits (route index lay).1
        (route index lay).2 rfl rfl i hi q hq))
      hsrcC (Extract.route_tree_treeBits index hidx lay) hcount (by omega) hreach with
    hS' | ⟨hhon, hlow⟩
  · exact (hS hS').elim
  refine ⟨fun hle => ?_, hlow⟩
  obtain ⟨hval, hpads⟩ := hhon hle
  refine ⟨hval, fun hlt => ?_⟩
  obtain ⟨h0, h1, hh⟩ := hpads (by omega)
  exact ⟨Prod.ext h0 h1, hh⟩
theorem layerP_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hlay0 : lay = 0) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    StructuralHitSrc answers messages (entriesOf answers (queried answers (layerP w index lay digits))) ∨
    ((∀ j, j < height lay →
        wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        wmerklePad w lay (route index lay).1 j =
          WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1))) ∧
        wmerkleHigh w lay (route index lay).1 j = 0) ∧
      (∀ i, i < chainCount lay →
        (CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i →
              wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        (digits.getD i 0 < CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
          CanonicalRef.ContactAt answers messages (entriesOf answers (queried answers (layerP w index lay digits)))
              ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
              CanonicalRef.TwoEdgeAt answers messages (entriesOf answers (queried answers (layerP w index lay digits)))
                ⟨routeLeaf index lay, i⟩))) ∧
      wleafHigh w lay = 0) := by
  classical
  by_cases hS : StructuralHitSrc answers messages (entriesOf answers (queried answers (layerP w index lay digits)))
  · exact Or.inl hS
  right
  have hl0 : lay.val = 0 := by rw [hlay0]; rfl
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  -- C4: the top path is a half-aware hash path of `height lay` one-word folds (as the lower paths, C2).
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [Extract.layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (Extract.hashPathW (Extract.merkleHighW lay.val (height lay) (route index lay).1)
      (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (height lay) (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [Extract.layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_right _ hq
  have hM := Extract.merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay) (wpath w lay (route index lay).1)
    (fun j => treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (WCT9.wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (Extract.honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => Extract.merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1
      hleafB step hstep)
    (by
      have h := reaches
      rw [Extract.layerP_eq_hashPathW, evalWithAnswerFn_bind] at h
      unfold Extract.pathValueW
      rw [Nat.div_eq_of_lt hleafB]
      exact h)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)))
      (pad64 (Extract.pathInputW answers (Extract.merkleHighW lay.val (height lay) (route index lay).1)
        (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (evalWithAnswerFn answers (layerLeafP w index lay digits)) step))
      ⟨htreeB, hstep, Or.inl hlay0, Extract.tree_zero_of_treeBits (Extract.route_tree_treeBits index hidx lay), ?_⟩
      ⟨Extract.route_tree_treeBits index hidx lay, hstep, ?_, Or.inl hlay0⟩ (hqM _ hq) ?_ ?_ trivial trivial
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [Extract.hashHitAt_iff, Extract.merkle_honestInputW' answers lay]; exact hhit
    · rw [Extract.merkle_honestInputW' answers lay, Extract.pathInputW, hl0]
      exact Extract.merkleInputW_sameHeader_top _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one] at hv0
  rcases leaf_wots answers w index lay digits hidx hvalid _ hqL hv0 with hS' | ⟨hchains, hhi⟩
  · exact (hS hS').elim
  · exact ⟨fun j hj => ⟨(hpath j hj).1, (hpath j hj).2.2, (hpath j hj).2.1⟩, hchains, hhi⟩
theorem layerPairP_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (hlay : lay.val ≠ 0)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    StructuralHitSrc answers messages (entriesOf answers (queried answers (layerPairP w index lay digits))) ∨
    ((∀ j, j < height lay →
        wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay → wmerklePad w lay (route index lay).1 j = 0 ∧ wmerkleHigh w lay (route index lay).1 j = 0)) ∧
      (∀ i, i < chainCount lay →
        (CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i →
              wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        (digits.getD i 0 < CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
          CanonicalRef.ContactAt answers messages (entriesOf answers (queried answers (layerPairP w index lay digits)))
              ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
              CanonicalRef.TwoEdgeAt answers messages (entriesOf answers (queried answers (layerPairP w index lay digits)))
                ⟨routeLeaf index lay, i⟩))) ∧
      wleafHigh w lay = 0) := by
  classical
  by_cases hS : StructuralHitSrc answers messages (entriesOf answers (queried answers (layerPairP w index lay digits)))
  · exact Or.inl hS
  right
  have hh := Extract.height_pos lay
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [Extract.layerPairP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (Extract.hashPathW (Extract.merkleHighW lay.val (height lay) (route index lay).1)
      (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (height lay - 1) (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [Extract.layerPairP_eq_hashPathW, queried_bind, queried_bind]
    exact List.mem_append_right _ (List.mem_append_left _ hq)
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨ (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by rw [← pow_succ, Nat.sub_add_cancel hh]
      rw [Nat.mul_comm, he]
      exact hleafB
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  have reaches' := reaches
  rw [Extract.layerPairP_eq_hashPathW, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at reaches'
  generalize htop : evalWithAnswerFn answers (Extract.hashPathW (Extract.merkleHighW lay.val (height lay) (route index lay).1)
      (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (height lay - 1) (evalWithAnswerFn answers (layerLeafP w index lay digits))) = top at reaches'
  have hpair : top = treeValue (WCT9.wotsTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1)) ∧
      wpath w lay (route index lay).1 (height lay - 1) =
        treeValue (WCT9.wotsTree answers lay (route index lay).2) (height lay - 1)
          ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := by
    unfold Extract.honestPair at reaches'
    rcases hq2 with h | h <;> simp only [h] at reaches' ⊢ <;>
      simp only [Nat.one_mod, if_true, if_false, Prod.mk.injEq, one_ne_zero] at reaches' <;>
      exact ⟨by first | exact reaches'.1 | exact reaches'.2, by first | exact reaches'.2 | exact reaches'.1⟩
  have hM := Extract.merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay - 1) (wpath w lay (route index lay).1)
    (fun j => treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (WCT9.wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (Extract.honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => Extract.merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1
      hleafB step (by omega))
    (by unfold Extract.pathValueW; rw [htop]; exact hpair.1)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)))
      (pad64 (Extract.pathInputW answers (Extract.merkleHighW lay.val (height lay) (route index lay).1)
        (Extract.merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (evalWithAnswerFn answers (layerLeafP w index lay digits)) step))
      ⟨htreeB, by omega, Or.inr (by omega), Extract.tree_zero_of_treeBits (Extract.route_tree_treeBits index hidx lay), ?_⟩
      ⟨Extract.route_tree_treeBits index hidx lay, by omega, ?_, Or.inr (by omega)⟩
      (hqM _ hq) ?_ ?_ trivial trivial
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [Extract.hashHitAt_iff, Extract.merkle_honestInputW' answers lay]; exact hhit
    · rw [Extract.merkle_honestInputW' answers lay, Extract.pathInputW]
      exact Extract.merkleInputW_sameHeader (Extract.lower_heap_lt128 hlay hleafB) _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one] at hv0
  rcases leaf_wots answers w index lay digits hidx hvalid _ hqL hv0 with hS' | ⟨hchains, hhi⟩
  · exact (hS hS').elim
  refine ⟨fun j hj => ?_, hchains, hhi⟩
  by_cases hjt : j < height lay - 1
  · have hl' : lay ≠ 0 := fun h => hlay (by rw [h]; rfl)
    exact ⟨(hpath j hjt).1, fun _ => ⟨(hpath j hjt).2.2.trans
      (congrFun (Extract.honestPads_lower answers hl' _ _) j), (hpath j hjt).2.1⟩⟩
  · have hj1 : j = height lay - 1 := by omega
    subst hj1
    exact ⟨hpair.2, fun h => by omega⟩

end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3.Security.WotsExtract (SourceLeaf7 SourceChain7 SourceLeaf7.source SourceChain7.source routeLeaf_source7)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (SourceChain routeLeaf mem_entriesOf)
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {messages : LeafAddr → WCT9.LayerMsg}

/-- Configuration (1)+(2): the witness hint opens the producer's half at the honest encoding row of `lay`.
It always holds on lower layers (`honestHint_lower`); on the top layer a witness may open the other half. -/
def HonestHint (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  WCT9.verificationAnswer lay (wtopHigh w) (answers (.inl (.inr (pad64 (layerEncodingInputP lay (route index lay).2
      (route index lay).1 (messages (routeLeaf index lay)) (wbcCtr w index lay) (wbcPad w index lay) (wbcRight w)
      (wbcHigh w index lay)))))) =
    WCT9.encodingAnswer lay (answers (.inl (.inr (pad64 (layerEncodingInputP lay (route index lay).2
      (route index lay).1 (messages (routeLeaf index lay)) (wbcCtr w index lay) (wbcPad w index lay) (wbcRight w)
      (wbcHigh w index lay))))))

theorem honestHint_lower (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (w : WBytes) (index : Nat) {lay : Layer} (hl : lay ≠ 0) : HonestHint answers messages w index lay :=
  WCT9.verificationAnswer_lower lay hl _ _

/-- Stage 2 (C3, #866 `BC.GoodZ`): the honest row also has the row-tweak high word 1 (a witness pad).
Configuration (1)+(2): the frame and shape are claimed only when the witness hint is the producer's one (the
reference commit's `GoodZ`); a witness that opens the other half of the honest top row is covered by the
contact/marker analysis or yields this vacuous case. -/
def Good (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  (HonestHint answers messages w index lay →
    ∃ digits, Extract.CanonicalFrame answers w index lay (messages (routeLeaf index lay)) digits ∧
      Extract.LayerShaped answers w index lay digits) ∧ wbcPad w index lay = 0 ∧ wbcHigh w index lay = 1

theorem frame_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hfitRef : Extract.msgFits lay (messages (routeLeaf index lay)))
    (hframe : Extract.CanonicalFrame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hmerkle : ∀ j, j < height lay →
      wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay (route index lay).1 j =
          WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1)))) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerkleHigh w lay (route index lay).1 j = 0))
    (hleaf : wleafHigh w lay = 0)
    (hchains : ∀ i, i < chainCount lay →
      (CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
        CanonicalRef.ContactAt answers messages (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
            CanonicalRef.TwoEdgeAt answers messages (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) :
    WotsPrimitiveSrc answers messages (entriesOf answers qs) ∨
      (msg = messages (routeLeaf index lay) ∧ Good answers messages w index lay) := by
  classical
  have hdec : WCT9.CanonicalPolicy.decode (routeLeaf index lay).lay
      (WCT9.verificationAnswer (routeLeaf index lay).lay (wtopHigh w) (answers (.inl (.inr (encRow (routeLeaf index lay) msg
        (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1)))))) = some digits := by
    rw [ClaudeWCT.W9.T3.Security.WotsExtract.encRow_wit]; exact hframe.2
  have hencE : (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1),
      answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w index lay)
        (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1))))) ∈ entriesOf answers qs := by
    rw [ClaudeWCT.W9.T3.Security.WotsExtract.encRow_wit]; exact mem_entriesOf henc
  have hsrc : SourceLeaf7 (routeLeaf index lay) := routeLeaf_source7 index hidx lay
  have hsrcC7 : ∀ i, i < chainCount lay → SourceChain7 ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => (hsrcC7 i hi).source
  have hcontact : ∀ i, i < chainCount lay →
      digits.getD i 0 < CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ →
      CanonicalRef.ContactAt answers messages (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ :=
    fun i hi hlt => ((hchains i hi).2 hlt).1
  obtain ⟨refDigest, hr⟩ := CanonicalRef.referenceDigits_decode answers messages (routeLeaf index lay)
  rcases canonical_word_cases hr hdec with heq | ⟨i, hi, hlow, hother⟩ | ⟨i, hi, h2⟩ |
      ⟨i, j, hi, hj, hij, hli, hlj⟩
  · have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_, hleaf⟩
      have hdi : CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold CanonicalRef.depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = messages (routeLeaf index lay)
    · by_cases hp : wbcPad w index lay = 0 ∧ wbcHigh w index lay = 1
      · exact Or.inr ⟨hm, fun _ => ⟨digits, hm ▸ hframe, hshape⟩, hp⟩
      · have hpad : (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1).1 ≠ 0 ∨
            (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1).2.2 ≠ 0 := by
          by_cases hp1 : wbcPad w index lay = 0
          · right
            intro h1
            apply hp
            refine ⟨hp1, ?_⟩
            simpa using h1
          · exact Or.inl hp1
        refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, msg, wbcCtr w index lay,
          (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, hfit, hencE, ?_, ?_, ?_⟩)
        · exact CanonicalRef.referenceInput_ne_padW answers messages _ msg _ _ hfitRef hfit hpad
        · exact CanonicalRef.notSearched_of_ne answers messages _ msg _ _ hfitRef hfit (Or.inr hpad)
        · rw [← heq]; exact ⟨wtopHigh w, hdec⟩
    · refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, msg, wbcCtr w index lay,
        (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, hfit, hencE, ?_, ?_, ?_⟩)
      · exact CanonicalRef.referenceInput_ne_msg answers messages _ msg _ _ hfitRef hfit hm
      · exact CanonicalRef.notSearched_of_ne answers messages _ msg _ _ hfitRef hfit (Or.inl hm)
      · rw [← heq]; exact ⟨wtopHigh w, hdec⟩
  · have hne : digits ≠ CanonicalRef.referenceDigits answers messages (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    by_cases hri : CanonicalRef.referenceInput answers messages (routeLeaf index lay) = some
        (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1))
    · -- The honest row itself, read through the other half: the frame claim is vacuous.
      obtain ⟨hm, hp1, hp2⟩ := CanonicalRef.referenceInput_eq_msg_pad answers messages _ msg _ _ hfitRef hfit hri
      refine Or.inr ⟨hm, fun hh => ?_, hp1, ?_⟩
      · exfalso
        apply hne
        have hs : CanonicalRef.referenceSearch answers messages (routeLeaf index lay) ≠ none := by
          intro hs; unfold CanonicalRef.referenceInput at hri; rw [hs] at hri; cases hri
        obtain ⟨⟨c, rd, low⟩, hfound⟩ := Option.ne_none_iff_exists'.mp hs
        have hrow : encRow (routeLeaf index lay) (messages (routeLeaf index lay)) c 0 =
            encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1) := by
          unfold CanonicalRef.referenceInput at hri
          rw [hfound] at hri
          exact Option.some.inj hri
        have href := CanonicalRef.referenceSearch_decode answers messages (routeLeaf index lay) hfound
        rw [hrow, ClaudeWCT.W9.T3.Security.WotsExtract.encRow_wit] at href
        rw [ClaudeWCT.W9.T3.Security.WotsExtract.encRow_wit] at hdec
        subst hm
        have hh' : WCT9.verificationAnswer lay (wtopHigh w) _ = WCT9.encodingAnswer lay _ := hh
        have hcan := hdec
        erw [hh'] at hcan
        have hrd : CanonicalRef.referenceDigits answers messages (routeLeaf index lay) = rd := by
          simp only [CanonicalRef.referenceDigits, hfound, Option.map_some, Option.getD_some]
        rw [hrd]
        exact Option.some.inj (hcan.symm.trans href)
      · have hp2' : wbcHigh w index lay ^^^ 1 = 0 := hp2
        exact CanonicalRef.xor_one_inj' (hp2'.trans (by decide : (0 : BitVec 64) = 1 ^^^ 1))
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i⟩, hsrcC7 i hi,
      ⟨msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, digits, hfit, hencE,
        hri, ⟨wtopHigh w, hdec⟩, hlow, ?_⟩, hcontact i hi (by change digits.getD i 0 < (CanonicalRef.referenceDigits answers messages (routeLeaf index lay)).getD i 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hother k hkc hk
    · rw [List.getD_eq_default _ _ (by rw [CanonicalRef.referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i⟩, hsrcC7 i hi, ?_⟩)))
    have hlt : digits.getD i 0 < CanonicalRef.depth answers messages ⟨routeLeaf index lay, i⟩ := by
      change digits.getD i 0 < (CanonicalRef.referenceDigits answers messages (routeLeaf index lay)).getD i 0
      omega
    exact ((hchains i hi).2 hlt).2 h2
  · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i⟩, ⟨routeLeaf index lay, j⟩,
      hsrcC7 i hi, hsrcC7 j hj, ?_, hcontact i hi hli, hcontact j hj hlj⟩))))
    intro he
    exact hij (ChainAddr.mk.inj he).2
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3.Security.WotsExtract (SourceLeaf7 SourceChain7 SourceLeaf7.source SourceChain7.source routeLeaf_source7)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (SourceChain routeLeaf mem_entriesOf entriesOf_mono)
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {messages : LeafAddr → WCT9.LayerMsg}

theorem decode_valid {lay : Layer} {value : Digest} {digits : List Nat}
    (h : WCT9.CanonicalPolicy.decode lay value = some digits) : Cost.ValidDigits lay digits := by
  have hv := Cost.validDigits_decode h
  intro i hi
  rw [← normalLayer_maxDigit]
  exact hv i (by rw [normalLayer_chainCount]; exact hi)

theorem layer_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay0 : lay = 0) (hfit : Extract.msgFits lay msg)
    (hfitRef : Extract.msgFits lay (messages (routeLeaf index lay)))
    (hframe : Extract.CanonicalFrame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveSrc answers messages (entriesOf answers qs) ∨
      (msg = messages (routeLeaf index lay) ∧ Good answers messages w index lay) := by
  have hvalid := decode_valid hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerP_wots (messages := messages) answers w index lay digits hidx hlay0 hvalid reaches with hS | ⟨hmerkle, hchains, hleaf⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  have hl0 : lay.val = 0 := by rw [hlay0]; rfl
  exact frame_wots (messages := messages) answers w index lay msg digits hidx hfit hfitRef hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun _ => (hmerkle j hj).2.1, fun _ => (hmerkle j hj).2.2⟩) hleaf
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layerPair_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay : lay.val ≠ 0) (hfit : Extract.msgFits lay msg)
    (hfitRef : Extract.msgFits lay (messages (routeLeaf index lay)))
    (hframe : Extract.CanonicalFrame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerPairP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    WotsPrimitiveSrc answers messages (entriesOf answers qs) ∨
      (msg = messages (routeLeaf index lay) ∧ Good answers messages w index lay) := by
  have hvalid := decode_valid hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerPairP_wots (messages := messages) answers w index lay digits hidx hvalid hlay reaches with hS | ⟨hmerkle, hchains, hleaf⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots (messages := messages) answers w index lay msg digits hidx hfit hfitRef hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun h => by
        rw [WCT9.honestNonce_lower answers (fun h0 => hlay (by rw [h0]; rfl)), WCT9.nonceDigest_zero]
        exact ((hmerkle j hj).2 (h.resolve_right hlay)).1,
      fun h => ((hmerkle j hj).2 (h.resolve_right hlay)).2⟩) hleaf
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)

end ClaudeWCT.W9.T3.Security.CanonicalExtract
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsExtractVerify ====
section

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3M.WctExtract (wctChainP_eq_hashPathW queried_hashPathW pad64_wctChainInputPW wctChainInputPW_length
  hdrBlock_wctChainInputPW wctChainInputP_block4 queried_hashPath queried_mapM
  hdrBlock_block4W leafHash_eq_shortHash hdrBlock_merkleInput recoverCoordinateP_dec wctTopInput_block4)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc layerP)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono)
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layersBC_wots_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, Extract.msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersBC w index n msg) = some (Extract.honestRoot answers 0 0) →
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersBC w index n msg))) ∨
    ((∀ l : Layer, l.val < n → BC.GoodZ answers w index l) ∧
      msg = Extract.honestMsg answers index (Fin.ofNat 4 (n - 1)))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := Extract.layersBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := Extract.ofNat_val n (by omega)
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          (msg = Extract.honestMsg answers index (Fin.ofNat 4 n) ∧ BC.GoodZ answers w index (Fin.ofNat 4 n)) →
          (∀ l : Layer, l.val < n → BC.GoodZ answers w index l) →
          WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          ((∀ l : Layer, l.val < n + 1 → BC.GoodZ answers w index l) ∧
            msg = Extract.honestMsg answers index (Fin.ofNat 4 n)) := by
        intro hx hgood
        rcases hx with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          refine ⟨fun l hl => ?_, hmsg⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            Extract.honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        exact finish (layer_wots answers w index (Fin.ofNat 4 0) msg digits hidx rfl hfit hframe _ henc hq hroot)
          (fun l hl => absurd hl (by omega))
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : Extract.msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := trivial
        rcases layersBC_wots_walk answers w index hidx n (by omega) (by omega) _ hfit' hrest with
          hprim | ⟨hgood, hmsg⟩
        · exact Or.inl (hprim.mono (entriesOf_mono hqR))
        · rw [Extract.honestMsg_lower answers index n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          exact finish (layerPair_wots answers w index (Fin.ofNat 4 n) msg digits hidx (by rw [hval]; exact hn0)
            hfit hframe _ henc hqP hpair) hgood
theorem verifyP_walk_wots (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (WCT9.digestIndex N) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
            Extract.honestTop answers (WCT9.digestIndex N) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  rcases layersBC_wots_walk answers w (WCT9.digestIndex N) hidx 4 (by decide) le_rfl (.pair _ _) trivial (hpk ▸ hlay) with
    hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono hqL))
  · right
    refine ⟨fun l => hgood l l.isLt, ?_, hqF⟩
    rw [show (4 - 1 : Nat) = 3 from rfl, Extract.honestMsg_three] at hroot
    simp only [WCT9.LayerMsg.pair.injEq] at hroot
    exact Prod.ext hroot.1 hroot.2
def FtsPos : Extract.Pos → Prop
  | .wctChain .. => True
  | .wctLeaf .. => True
  | .wctNode .. => True
  | _ => False
/-- C4: the query also has the position's length (`Pos.hdr_injective` needs it). -/
def FtsQueryPos (actual : HashInput) : Prop :=
  ∃ pos : Extract.Pos, pos.Bounded ∧ PosSource pos ∧ FtsPos pos ∧ actual.length = pos.len ∧
    Extract.canonicalHeader (Extract.hdrBlock actual) = bytesLE 16 pos.hdr
theorem ftsQueryPos_of_hdr {actual : HashInput} {pos : Extract.Pos} (hb : pos.Bounded) (hsrc : PosSource pos)
    (hfts : FtsPos pos) (hlen : actual.length = pos.len) (hdr : Extract.hdrBlock actual = bytesLE 16 pos.hdr) :
    FtsQueryPos actual :=
  ⟨pos, hb, hsrc, hfts, hlen, by rw [hdr, Extract.Pos.canonicalHeader_eq hb]⟩
theorem chain_queries_pos (answers : Answers) (index coord child t d : Nat) (hd : d ≤ 4) (p0 : Digest)
    (pb : BitVec 64) (p1 v : Digest) (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6) :
    ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d p0 pb p1 v),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [wctChainP_eq_hashPathW, queried_hashPathW] at hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  obtain ⟨hi, hc, hj, ht⟩ := hb
  have hbd : (Extract.Pos.wctChain index coord child t (4 - d + s)).Bounded := ⟨hi, hc, hj, ht, by omega⟩
  refine ⟨_, rfl, .wctChain index coord child t (4 - d + s), hbd, ⟨hi, hc, hj, ht, by omega⟩, trivial, ?_, ?_⟩
  · simp only [Extract.pathInputW, pad64_wctChainInputPW, wctChainInputPW_length, Extract.Pos.len]
  simp only [Extract.pathInputW, pad64_wctChainInputPW, hdrBlock_wctChainInputPW, Extract.Pos.hdr]
  rw [WctExtract.canonicalHeader_ftsChainHeaderP]
  have hk := Extract.Pos.canonicalHeader_eq hbd
  simp only [Extract.Pos.hdr] at hk
  exact hk
theorem leaf_queries_pos (answers : Answers) (index coord child : Nat) (pad : Digest) (ends : List Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128) (hends : ends.length = 6) :
    ∀ q ∈ queried answers (WCT9.leafHashP index coord child pad ends),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [WctExtract.leafHashP_eq_shortHash, queried_shortHash] at hq
  rw [List.mem_singleton] at hq
  subst hq
  obtain ⟨hi, hc, hj⟩ := hb
  refine ⟨_, rfl, ftsQueryPos_of_hdr (pos := .wctLeaf index coord child) ⟨hi, hc, hj⟩ ⟨hi, hc, hj⟩ trivial ?_ ?_⟩
  · unfold Extract.wctLeafInputP
    rw [Extract.pad64_length_of_mod (by rw [Extract.listInput_length]; simp [hends]), Extract.listInput_length]
    simp [hends, Extract.Pos.len]
  rw [Extract.hdrBlock_wctLeafInputP]
  rfl
theorem merkle_queries_pos (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat) (hj : j < 128)
    (hidx : index < 2 ^ 31) (path pads : Nat → Digest) (hpads : Nat → BitVec 64) (leaf : Digest) :
    ∀ q ∈ queried answers (hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5 leaf),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  have hn : j / 2 ^ (s + 1) < 2 ^ (7 - s - 1) := by
    have := Correctness.div_pow_bound (node := j) (height := 7) (start := 0) (level := s + 1) (by omega)
      (by norm_num; omega)
    simpa [Nat.sub_sub] using this
  have hbd : (Extract.Pos.wctNode index c.val s (j / 2 ^ (s + 1))).Bounded := ⟨hidx, c.isLt, by omega, hn⟩
  refine ⟨_, rfl, .wctNode index c.val s (j / 2 ^ (s + 1)), hbd, hbd, trivial, ?_, ?_⟩
  · simp [pathInput, merkleInputH, nodeInputPH, block4, SphincsSecurity.bytesLE_length, pad64,
      Extract.Pos.len]
  have he : (Extract.Pos.wctNode index c.val s (j / 2 ^ (s + 1))).hdr =
      nodeTweak 3 (WCT9.nodeLayer c.val) index (2 ^ (7 - s - 1) + j / 2 ^ (s + 1)) := rfl
  have hk := Extract.Pos.canonicalHeader_eq hbd
  rw [he] at hk
  rw [he, pathInput, WctExtract.hdrBlock_merkleInputH, WctExtract.canonicalHeader_withHigh, hk]
theorem top_queries_pos (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat) (hj : j < 128)
    (hidx : index < 2 ^ 31) (l z r : Digest) :
    ∀ q ∈ queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6) l z r),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  have hqry : queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6) l z r) =
      [.inl (.inr (pad64 (WCT9.wctTopInput c.val index (2 + j / 2 ^ 6) l z r)))] := rfl
  rw [hqry, List.mem_singleton] at hq
  subst hq
  have hn : j / 2 ^ 6 < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by norm_num; omega)
  have hbd : (Extract.Pos.wctNode index c.val 5 (j / 2 ^ 6)).Bounded :=
    ⟨hidx, c.isLt, by norm_num, by norm_num; omega⟩
  refine ⟨_, rfl, ftsQueryPos_of_hdr (pos := .wctNode index c.val 5 (j / 2 ^ 6)) hbd hbd trivial ?_ ?_⟩
  · rw [wctTopInput_block4, pad64_block4]
    simp [block4, SphincsSecurity.bytesLE_length, Extract.Pos.len]
  rw [wctTopInput_block4, pad64_block4, hdrBlock_block4W]
  rfl
theorem coord_queries_pos (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord)
    (prev : Digest × Digest) :
    ∀ q ∈ queried answers
        (recoverCoordinateP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N c prev),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hj := (WCT9.child N c).isLt
  rw [recoverCoordinateP_dec] at hq
  rw [queried_bind, queried_bind, queried_bind, queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rw [queried_mapM] at hq
    obtain ⟨t, -, hq⟩ := List.mem_flatMap.mp hq
    exact chain_queries_pos answers (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val
      (WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit_le_four _ t) _ _ _ _ ⟨hidx, c.isLt, hj, t.isLt⟩ q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact leaf_queries_pos answers (WCT9.digestIndex N) c.val (WCT9.child N c).val _ _ ⟨hidx, c.isLt, hj⟩
      (by rw [SigGolfCandidate.T3.Correctness.eval_mapM]; simp) q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact merkle_queries_pos answers (WCT9.digestIndex N) c (WCT9.child N c).val hj hidx _ _ _ _ q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact top_queries_pos answers (WCT9.digestIndex N) c (WCT9.child N c).val hj hidx _ _ _ q hq
  · simp [queried_pure] at hq
theorem fts_queries_pos (answers : Answers) (N : HashOutput) (w : WBytes) :
    ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [WctExtract.recoverFtsP_nfold, queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨c, -, hq⟩ := WctExtract.queried_nfold answers _ _ 9 le_rfl q hq
    exact coord_queries_pos answers N w c _ q hq
  · simp [queried_pure] at hq
/-! C3 (FULL): an FTS query cannot decode as a lower/top leaf. The leaf key keeps only the low header word, and every
FTS header differs from every leaf tweak in its low word (marker and tag). -/
theorem canonicalHeader_take8 {hdr : HashInput} (h : 8 ≤ hdr.length) :
    (Extract.canonicalHeader hdr).take 8 = hdr.take 8 := by
  unfold SigGolfCandidate.T3M.Extract.canonicalHeader
  split
  · exact List.take_left' (by simp; omega)
  · rfl
theorem take8_bytesLE16 (a : BitVec 128) : (bytesLE 16 a).take 8 = bytesLE 8 (a.extractLsb' 0 64) := by
  have ha : a = a.extractLsb' 64 64 ++ a.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := a)).symm
  conv_lhs => rw [ha]
  rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (SphincsSecurity.bytesLE_length 8 _)]
/-- C4: the header of an FTS position (chain, leaf or node; the FTS recompute never queries the forest) has its low
word in `[2 ^ 16, 2 ^ 58)`: above every top label (coordinate nibble `coord + 1`) and below every WOTS leaf tweak
(type byte 193). -/
theorem ftsPos_low {p : Extract.Pos} (hb : p.Bounded) (h : FtsPos p) :
    2 ^ 16 ≤ tweakLow p.hdr ∧ tweakLow p.hdr < 2 ^ 58 := by
  cases p with
  | wctChain index coord child t step =>
      obtain ⟨-, hk, -, -, -⟩ := hb
      have h1 := WCT9.ftsChainLow_ge (show coord < 15 by omega) index child t step
      have h2 := WCT9.ftsChainLow_lt index coord child t step
      simp only [Extract.Pos.hdr, WCT9.ftsChainHeader]
      rw [Extract.tweakLow_eq_low, WCT9.ftsChainHeaderP_low, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (lt_trans h2 (by norm_num))]
      exact ⟨h1, h2⟩
  | wctLeaf index coord child =>
      obtain ⟨-, hk, -⟩ := hb
      have h1 := WCT9.ftsLeafLow_ge (show coord < 15 by omega) index child
      have h2 := WCT9.ftsLeafLow_lt index coord child
      simp only [Extract.Pos.hdr, WCT9.ftsLeafHeader]
      rw [append64_lowNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans h2 (by norm_num))]
      exact ⟨h1, h2⟩
  | wctNode index coord level nd =>
      obtain ⟨-, hk, -, -⟩ := hb
      have hlow := WCT9.wctNodeHeader_toNat hk index (2 ^ (7 - level - 1) + nd)
      have hge := WCT9.ftsLeafLow_ge (show coord < 15 by omega) index 0
      have hlt := WCT9.ftsLeafLow_lt index coord 0
      have hgeN : 2 ^ 16 ≤ WCT9.ftsNodeLowN index coord (2 ^ (7 - level - 1) + nd) := by
        rw [WCT9.ftsNodeLowN_eq, Nat.mod_eq_of_lt (show coord + 1 < 16 by omega)]; omega
      have hltN := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [Extract.Pos.hdr]
      unfold tweakLow
      rw [hlow]
      split_ifs <;> omega
  | _ => exact h.elim
theorem structuralHitSrc_of_fts_hitIn (answers : Answers) (N : HashOutput) (w : WBytes)
    (h : Extract.HitIn answers
      (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N))) :
    StructuralHitSrc answers (entriesOf answers
      (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N))) := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  obtain ⟨actual', hqe, pos', hb', hsrc', hfts', hlenQ, hdr'⟩ := fts_queries_pos answers N w _ hq
  have hae : actual = actual' := by simpa using hqe
  subst hae
  have hkey : Extract.hdrKey actual = bytesLE 16 pos.hdr := hs.2.trans (Extract.hdrKey_honestInput answers hb)
  have hlen : actual.length = pos.len := hs.1.trans (Extract.honestInput_length answers pos)
  have h16 : 8 ≤ (Extract.hdrBlock actual).length := by
    have : 64 ≤ actual.length := by
      rw [hlen]; cases pos <;> simp only [Extract.Pos.len] <;> (try split) <;> omega
    simp [Extract.hdrBlock]; omega
  -- C4: the actual header's low word is the FTS position's, in `[2 ^ 16, 2 ^ 58)`.
  have h8 : readLE ((Extract.hdrBlock actual).take 8) = tweakLow pos'.hdr := by
    rw [← canonicalHeader_take8 h16, hdr', Extract.readLE_take8]
  have hlo := ftsPos_low hb' hfts'
  by_cases hl : actual.length = 704 ∨ actual.length = 832
  · exfalso
    rw [hlenQ] at hl
    cases pos' <;> (try exact hfts'.elim) <;> simp [Extract.Pos.len] at hl
  · have hT : ¬ (actual.length = 64 ∧ Extract.TopLow (Extract.hdrBlock actual)) := by
      rintro ⟨-, ht⟩
      unfold Extract.TopLow at ht
      rw [h8] at ht
      omega
    have hkey' : Extract.hdrKey actual = bytesLE 16 pos'.hdr := by
      rw [Extract.hdrKey_of_not_leafLen hl hT, hdr']
    have hhdr : pos.hdr = pos'.hdr := bytesLE_injective (hkey.symm.trans hkey')
    have hpos : pos = pos' := Extract.Pos.hdr_injective hb hb' (hlen.symm.trans hlenQ) hhdr
    subst hpos
    refine ⟨pos, actual, _, mem_entriesOf hq, Extract.posOf_key_eq hb hlen hkey, hb, hsrc', ?_, hh⟩
    cases pos <;> first | trivial | exact hfts'.elim
theorem fts_structural (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
      Extract.honestTop answers (WCT9.digestIndex N)) :
    StructuralHitSrc answers (entriesOf answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N))) ∨
      WctExtract.WctHonest answers N w :=
  (WctExtract.wct_extract answers N w hS hrun).imp_left (structuralHitSrc_of_fts_hitIn answers N w)
theorem verifyP_wots_cases_src (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (WCT9.digestIndex N) l) ∧ WctExtract.WctHonest answers N w)) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_walk_wots answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Correctness (Answers)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3M.WctExtract (wctChainP_eq_hashPathW queried_hashPathW pad64_wctChainInputPW wctChainInputPW_length
  hdrBlock_wctChainInputPW wctChainInputP_block4 queried_hashPath queried_mapM
  hdrBlock_block4W leafHash_eq_shortHash hdrBlock_merkleInput recoverCoordinateP_dec wctTopInput_block4)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc layerP)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono)
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layersCanonicalBC_wots_walk (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31)
    (hfitRef : ∀ lay, Extract.msgFits lay (messages (routeLeaf index lay)))
    (hlower : ∀ n, 1 ≤ n → n < 4 → messages (routeLeaf index (Fin.ofNat 4 (n-1))) =
      WCT9.LayerMsg.pair
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, Extract.msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersCanonicalBC w index n msg) = some (Extract.honestRoot answers 0 0) →
    WotsPrimitiveSrc answers messages (entriesOf answers (queried answers (layersCanonicalBC w index n msg))) ∨
    ((∀ l : Layer, l.val < n → Good answers messages w index l) ∧
      msg = messages (routeLeaf index (Fin.ofNat 4 (n - 1))))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := Extract.layersCanonicalBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := Extract.ofNat_val n (by omega)
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : WotsPrimitiveSrc answers messages (entriesOf answers (queried answers (layersCanonicalBC w index (n + 1) msg))) ∨
          (msg = messages (routeLeaf index (Fin.ofNat 4 n)) ∧ Good answers messages w index (Fin.ofNat 4 n)) →
          (∀ l : Layer, l.val < n → Good answers messages w index l) →
          WotsPrimitiveSrc answers messages (entriesOf answers (queried answers (layersCanonicalBC w index (n + 1) msg))) ∨
          ((∀ l : Layer, l.val < n + 1 → Good answers messages w index l) ∧
            msg = messages (routeLeaf index (Fin.ofNat 4 n))) := by
        intro hx hgood
        rcases hx with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          refine ⟨fun l hl => ?_, hmsg⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            Extract.honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        exact finish (layer_wots (messages := messages) answers w index (Fin.ofNat 4 0) msg digits hidx rfl hfit (hfitRef _) hframe _ henc hq hroot)
          (fun l hl => absurd hl (by omega))
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : Extract.msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := trivial
        rcases layersCanonicalBC_wots_walk answers messages w index hidx hfitRef hlower n (by omega) (by omega) _ hfit' hrest with
          hprim | ⟨hgood, hmsg⟩
        · exact Or.inl (hprim.mono (entriesOf_mono hqR))
        · rw [hlower n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          exact finish (layerPair_wots (messages := messages) answers w index (Fin.ofNat 4 n) msg digits hidx (by rw [hval]; exact hn0)
            hfit (hfitRef _) hframe _ henc hqP hpair) hgood

end ClaudeWCT.W9.T3.Security.CanonicalExtract
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_SeccSufRoute ====
section

namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open Correctness (treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9seccSufRoute : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem digestSearch_succ (rho : Digest) (m : Message) (counter fuel : Nat) :
    WCT9.digestSearch rho m counter (fuel + 1) = (digest rho m (BitVec.ofNat 32 counter) >>= fun output =>
      if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 counter, output))
      else WCT9.digestSearch rho m (counter + 1) fuel) := rfl
theorem digestSearch_queried (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start (q : Spec.Domain), q ∈ queried answers (WCT9.digestSearch rho m start fuel) →
      ∃ c, start ≤ c ∧ c < start + fuel ∧ q = .inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) ∧
        ∀ c', start ≤ c' → c' < c →
          WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false := by
  intro fuel
  induction fuel with
  | zero => intro start q hq; simp [WCT9.digestSearch] at hq
  | succ fuel ih =>
      intro start q hq
      rw [digestSearch_succ, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest] at hq
      rcases List.mem_append.mp hq with hq | hq
      · rw [List.mem_singleton] at hq
        exact ⟨start, le_rfl, by omega, hq, fun c' h1 h2 => by omega⟩
      · by_cases hadm : WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 start))) = true
        · rw [if_pos hadm] at hq; simp at hq
        · rw [if_neg hadm] at hq
          obtain ⟨c, h1, h2, h3, h4⟩ := ih (start + 1) q hq
          refine ⟨c, by omega, by omega, h3, fun c' h1' h2' => ?_⟩
          by_cases hc' : c' = start
          · subst hc'; simpa using hadm
          · exact h4 c' (by omega) h2'
theorem honestMsg_lower (answers : Correctness.Answers) (index n : Nat) (hn : n + 1 < 4) :
    ClaudeWCT.W9.T3M.Extract.honestMsg answers index (Fin.ofNat 4 n) =
      .pair (ClaudeWCT.W9.T3M.Extract.honestPair answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2).1
        (ClaudeWCT.W9.T3M.Extract.honestPair answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2).2 := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
  have hl : (⟨n + 1, by omega⟩ : Layer) = Fin.ofNat 4 (n + 1) := Fin.ext (by simp; omega)
  simp only [ClaudeWCT.W9.T3M.Extract.honestMsg, hv, dif_pos (show n < 3 by omega), hl]
theorem honestMsg_three (answers : Correctness.Answers) (index : Nat) :
    ClaudeWCT.W9.T3M.Extract.honestMsg answers index (Fin.ofNat 4 3) = .pair (WCT9.honestTop answers index).1 (WCT9.honestTop answers index).2 := by
  rw [show (Fin.ofNat 4 3 : Layer) = 3 from rfl]
  simp only [ClaudeWCT.W9.T3M.Extract.honestMsg, show ¬((3 : Layer).val < 3) by decide, dite_false,
    ClaudeWCT.W9.T3M.Extract.honestTop_eq_wct9]
theorem route_tree_lower (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ 25 := by
  fin_cases lay <;> simp [route, height] <;> omega
theorem signLayers_complete (answers : Correctness.Answers) (hcomp : SignerComplete answers)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg : WCT9.LayerMsg,
      ∃ pieces, evalWithAnswerFn answers (WCT9.signLayersBC cache index n msg) = some pieces := by
  intro n
  induction n with
  | zero => intro _ msg; exact ⟨[], by simp [WCT9.signLayersBC]⟩
  | succ n ih =>
      intro hn msg
      by_cases hn0 : n = 0
      · subst hn0
        rw [WCT9.signLayersBC]
        simp only [evalWithAnswerFn_bind, ite_true, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
      · rw [WCT9.signLayersBC]
        simp only [evalWithAnswerFn_bind, hn0, ite_false]
        split
        · simp only [evalWithAnswerFn_bind]
          split
          · simp only [evalWithAnswerFn_pure]
            exact ⟨_, rfl⟩
          · rename_i hs'
            exfalso
            exact (ih (by omega) _).elim fun p hp => hs' p hp
        · rename_i hs
          exfalso
          refine (Option.isSome_iff_exists.mp (hcomp.2 _ ?_ _ _ _ ?_ ?_)).elim fun ⟨c, d⟩ hsome => hs c d hsome
          · intro h; rw [Fin.ext_iff, Fin.val_ofNat, Fin.val_zero] at h; omega
          · exact route_tree_lower index hindex _
          · exact route_leaf_bound index _
theorem payload_succeeds_of_complete (answers : Correctness.Answers) (hcomp : SignerComplete answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    ∃ sig, evalWithAnswerFn answers (payloadForNonce cache rho m) = some sig ∧ sig.rho = rho := by
  obtain ⟨⟨counter, N⟩, hds⟩ := Option.isSome_iff_exists.mp (hcomp.1 rho m)
  obtain ⟨pieces, hp⟩ := signLayers_complete answers hcomp cache (WCT9.digestIndex N) (WCT9.digestIndex_lt _)
    4 le_rfl (.pair (WCT9.honestTop answers (WCT9.digestIndex N)).1 (WCT9.honestTop answers (WCT9.digestIndex N)).2)
  unfold payloadForNonce
  simp only [evalWithAnswerFn_bind, hds, WCT9.eval_signForest, hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl, rfl⟩
theorem hdrBlock_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (WCT9.pairEncodingInputP lay tree leaf left right counter pad)) =
      SphincsSecurity.bytesLE 16 (rowTweak lay tree leaf) := by
  have hl : (WCT9.pairEncodingInputP lay tree leaf left right counter pad).length = 64 := by
    simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by omega)]
  unfold WCT9.pairEncodingInputP
  rw [List.append_assoc, List.append_assoc]
  exact SigGolfCandidate.T3M.Extract.hdrBlock_prefix _ _ _
/-- C2 (FULL): a lower node query of the honest tree shape (heap below `2 ^ height lay`) is no digest query: the
packed node word's marker is `128 + heap`. -/
theorem lowerNodeHash_notDigest (lay : Layer) (tree heap : Nat) (left right : Digest) (hh : heap < 2 ^ height lay) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerNodeHash lay.val tree heap left right)
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  by_cases h0 : lay.val = 0
  · rw [h0, ClaudeWCT.WCT9.lowerNodeHash_top]
    exact SigGolfCandidate.T3.Security.BPB.nodeHash_ok _ _ _ _ _ _ (by decide)
  · have h7 : heap < 128 := lt_of_lt_of_le hh
      ((Nat.pow_le_pow_right (by decide) (ClaudeWCT.W9.T3.Security.Signer.height_le_seven h0)).trans (by norm_num))
    unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
    refine ClaudeWCT.W9.T3.Security.Signer.halfHash_allowed_of_short _ _
      (SigGolfCandidate.T3.Security.BPB.shortHash_ok_marker
        (hdr := ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ?_ ?_)
    · unfold ClaudeWCT.WCT9.merkleNodeInput
      rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++
          SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap)),
        SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [SphincsSecurity.bytesLE_length, zero16]),
        SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
    · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]
      unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
      rw [SigGolfCandidate.T3.append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat,
        SigGolfCandidate.T3.hyperWord_toNat]
      omega
theorem layerEncoding_ok (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  cases msg with
  | forest root => exact SigGolfCandidate.T3.Security.BPB.encoding_ok lay tree leaf root counter
  | pair left right =>
      exact SigGolfCandidate.T3.Security.BPB.shortHash_ok_marker
        (hdrBlock_pairEncodingInputP lay tree leaf left right counter 0) (by rw [rowTweak_marker]; decide)
open SigGolfCandidate.T3.Security.BPB SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs in
/-- Pairing stage 1: a chain step of the current scheme (either format) is not a digest query. -/
theorem chainStepW_ok (lay : SigGolfCandidate.T3.Layer) (tree leaf i step : Nat) (v : SigGolfCandidate.T3.Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.shortHash (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  unfold SigGolfCandidate.T3.shortHash SigGolfCandidate.T3.publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (SigGolfCandidate.T3.pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v)) ≠ 0
    rw [ClaudeWCT.WCT9.chainInputW_padded]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [ClaudeWCT.WCT9.chainInputW_header, bytesLE16_first_toNat]
    have := SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem afterDigest_ok (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (do
      let forest ← WCT9.signForest (WCT9.digestIndex output) output
      let some pieces ← WCT9.signLayersBC cache (WCT9.digestIndex output) 4 (.pair forest.2.1 forest.2.2) | pure none
      pure (some (WCT9.assembledSignature rho forest.1 pieces)) : M (Option Signature))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  apply SourceQueries.bind_allowed _ (ClaudeWCT.WCT9.Wots.BPB.signForest_ok _ output)
  intro forest
  apply SourceQueries.bind_allowed _ (ClaudeWCT.W9.T3.Security.Signer.signLayersBC_allowed' _ _ layerEncoding_ok
    (ClaudeWCT.W9.T3.Security.Signer.buildTreeP_allowed' _ chainStepW_ok
      SigGolfCandidate.T3.Security.BPB.leafHash_ok
      (fun lay _ _ _ _ hh => lowerNodeHash_notDigest lay _ _ _ _ hh)
      (fun _ _ _ => SigGolfCandidate.T3.Security.BPB.privatePair_ok _ _ _ _ _))
    (SigGolfCandidate.T3.Security.BPB.signTop_ok _) _ _ _)
  intro layers
  rcases layers with _ | pieces
  · exact SourceQueries.pure_allowed _ _
  · exact SourceQueries.pure_allowed _ _
theorem signer_digest_query (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (rho : Digest) (m : Message) (ctr : BitVec 32)
    (hq : (.inl (.inr (pad64 (digestInput rho m ctr))) : Spec.Domain) ∈
      queried answers (FullGame.authenticatedSign published request)) :
    request.cache = published ∧ request.message = m ∧
      rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      (.inl (.inr (pad64 (digestInput rho m ctr))) : Spec.Domain) ∈
        queried answers (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) := by
  unfold FullGame.authenticatedSign at hq
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  by_cases hc : request.cache = published
  swap
  · rw [if_neg hc] at hq; simp at hq
  rw [if_pos hc] at hq
  change _ ∈ queried answers (WCT9.Rev3.signPayload request.cache request.message) at hq
  rw [signPayload_nonce, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateNonce] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  unfold payloadForNonce at hq
  rw [queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  ·
    obtain ⟨c, -, -, heq, -⟩ := digestSearch_queried answers _ _ WCT9.digestAttemptLimit 0 _ hq
    simp only [Sum.inl.injEq, Sum.inr.injEq] at heq
    obtain ⟨hrho, hctr, hm⟩ := SigGolfCandidate.T3.Security.BPB.digestInput_injective heq
    subst hrho hm
    exact ⟨hc, rfl, rfl, hq⟩
  ·
    exfalso
    generalize evalWithAnswerFn answers (WCT9.digestSearch (evalWithAnswerFn answers (privateNonce request.message))
      request.message 0 WCT9.digestAttemptLimit) = found at hq
    rcases found with _ | ⟨_, output⟩
    · simp at hq
    · have := SigGolfCandidate.T3.Security.BPB.allQ_queried answers _ _ (afterDigest_ok request.cache
        (evalWithAnswerFn answers (privateNonce request.message)) output) _ hq
      exact this (SigGolfCandidate.T3.Security.BPB.hdrMarker_digestInput rho m ctr)
theorem caseC_fresh_not_signer (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests) (state : LazyPrivate.State)
    (hres : ∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2)
    (hagree : ∀ input answer, SourceReplay.known state input = some answer → answers input = answer)
    (m : Message) (w : WBytes) (hcomp : SignerComplete answers) (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨sig, hsig, hsrho⟩ := payload_succeeds_of_complete answers hcomp published (wrho w) m
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [← (hres entry he).eval answers hagree, eval_authenticatedSign, if_pos hc, ← hrho, hm]
  exact hsig
theorem caseCAt_fresh_not_signer (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests) (state : LazyPrivate.State)
    (hres : ∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2)
    (hagree : ∀ input answer, SourceReplay.known state input = some answer → answers input = answer)
    (message : Message) (witness : WBytes) (events : List FirstHit.QueryEvent)
    (hC : CaseCAt answers message witness events) (hfresh : ¬SignedDigest log message witness) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))) : Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  obtain ⟨N, -, hN, -, hS, hgood, -, hcomp⟩ := hC
  exact caseC_fresh_not_signer answers published log state hres hagree message witness hcomp hfresh
end ClaudeWCT.W9.T3.Security.BPB
end
-- ==== merged from T3_Secc_WotsTransportSplit ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.verifyP ClaudeWCT.W9.T3M.expandB buildFts buildTree signPayload
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_CaseCLinkSplit ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCLinkSplit : DecidableEq T3.Cache := Classical.decEq _
theorem queryEvent_answer_eq {state : LazyPrivate.State} {input : T3.Spec.Domain} {a b : T3.Spec.Range input}
    (h : (⟨state, input, a⟩ : FirstHit.QueryEvent) = ⟨state, input, b⟩) : a = b := by
  simp only [FirstHit.QueryEvent.mk.injEq, heq_eq_eq, true_and] at h
  exact h
theorem record_prefix_unique {α : Type} (program : M α) (state : LazyPrivate.State)
    (r1 r2 : FirstHit.Recorded α) (h1 : r1 ∈ support (FirstHit.record program state))
    (h2 : r2 ∈ support (FirstHit.record program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : r1.events ++ rest1 = r2.events ++ rest2) : r1 = r2 := by
  induction program using OracleComp.inductionOn generalizing state r1 r2 rest1 rest2 with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at h1 h2
      obtain ⟨m1, hm1, h1⟩ := h1
      obtain ⟨m2, hm2, h2⟩ := h2
      rw [support_map] at h1 h2
      obtain ⟨l1, hl1, rfl⟩ := h1
      obtain ⟨l2, hl2, rfl⟩ := h2
      simp only [List.cons_append, List.cons.injEq] at heq
      have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
      have hs1 := FirstHit.query_advance state input m1 hm1
      have hs2 := FirstHit.query_advance state input m2 hm2
      have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
      subst hm
      have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
      rw [hl]
def genRecord (generated : (Digest × T3.Cache) × QueryRecorded.State) : FirstHit.Recorded (Digest × T3.Cache) :=
  ⟨generated.1, generated.2.events, lazyOf generated.2⟩
theorem genRecord_support (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    genRecord generated ∈ support (FirstHit.record keygen (∅, ∅)) := by
  obtain ⟨rec, hrec, hev, hstate, hvalue⟩ := recorded_new_events keygen QueryRecorded.initial generated hg
  have : genRecord generated = rec := by
    cases rec
    simp only [genRecord] at *
    rw [← hstate, ← hvalue, hev]
    rfl
  rw [this]
  exact hrec
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from T3_Secc_CaseCFull ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCFull : DecidableEq T3.Cache := Classical.decEq _
theorem queried_notDigest_keygen (A : Correctness.Answers) (input : T3.Spec.Domain)
    (h : input ∈ SourceReplay.queried A keygen) : BPB.NotDigestQ input :=
  BPB.allQ_queried A BPB.NotDigestQ keygen keygen_notDigest input h
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from T3_Secc_LargeContactWalk ====
section

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
end SigGolfCandidate.T3.Security.WotsExtract
end
-- ==== merged from T3_Secc_CaseCLeaf ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem mem_publicEntries {events : List FirstHit.QueryEvent} {prior : LazyPrivate.State} {input : HashInput}
    {answer : HashOutput} (h : (⟨prior, .inl (.inr input), answer⟩ : FirstHit.QueryEvent) ∈ events) :
    (input, answer) ∈ BPair.publicEntries events := by
  unfold BPair.publicEntries
  rw [List.mem_filterMap]
  exact ⟨_, h, rfl⟩
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_CaseCLeaf ====
section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
open ClaudeWCT.W9.T3M (WBytes Shaped verifyP wctChainP wctChainInputP wctChainInputPW recoverFtsP witDecP padDecP wreveal wcpads
  wcHeaderPad)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP checkForgeryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem wctChainP_first_queried (answers : Correctness.Answers) (index coord child t start count : Nat)
    (p0 : Digest) (pb : BitVec 64) (p1 v : Digest) (hc : 1 ≤ count) :
    (.inl (.inr (pad64 (wctChainInputPW index coord child t start p0 pb p1 v))) : Spec.Domain) ∈
      queried answers (wctChainP index coord child t start count p0 pb p1 v) := by
  obtain ⟨n, rfl⟩ : ∃ n, count = n + 1 := ⟨count - 1, by omega⟩
  unfold wctChainP
  rw [List.range'_succ, List.foldlM_cons, queried_bind]
  exact List.mem_append_left _ (by rw [SigGolfCandidate.T3M.SecurityExtraction.queried_projHash]; exact List.mem_singleton_self _)
theorem recoverFtsP_chain_queried (answers : Correctness.Answers) (N : HashOutput) (w : WBytes) (k : WCT9.Coord)
    (t : Fin 6) (hu : 1 ≤ WCT9.wordDigit (WCT9.rank N k) t) :
    (.inl (.inr (pad64 (wctChainInputPW (WCT9.digestIndex N) k.val (WCT9.child N k).val t.val
        (4 - WCT9.wordDigit (WCT9.rank N k) t) (wcpads w k.val t.val).1 (wcHeaderPad w k.val t.val)
        (wcpads w k.val t.val).2 (wreveal w k.val t.val (WCT9.wordDigit (WCT9.rank N k) t))))) : Spec.Domain) ∈
      queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) := by
  rw [ClaudeWCT.W9.T3M.WctExtract.recoverFtsP_nfold, queried_bind]
  apply List.mem_append_left
  refine ClaudeWCT.W9.T3M.WctExtract.queried_nfold_sub answers _ _ 9 le_rfl k k.isLt _ ?_
  rw [ClaudeWCT.W9.T3M.WctExtract.recoverCoordinateP_dec, queried_bind]
  apply List.mem_append_left
  rw [ClaudeWCT.W9.T3M.WctExtract.queried_mapM]
  refine List.mem_flatMap.mpr ⟨t, List.mem_finRange t, ?_⟩
  exact wctChainP_first_queried answers _ _ _ _ _ _ _ _ _ _ hu
theorem witnessOf_unique {answers : Correctness.Answers} {pk : Digest} {forgery : ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : PaddedExtraction.WitnessOf answers pk forgery m w)
    (h' : PaddedExtraction.WitnessOf answers pk forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, h1⟩ := h
      obtain ⟨rfl, h2⟩ := h'
      rw [h1] at h2
      exact ⟨rfl, Option.some.inj h2⟩
theorem verdict_accepting (pk : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (checked : FirstHit.Recorded Bool)
    (hr : checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker pk interaction) before))
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer)
    (hwin : checked.value = true) (forgery : ForgeryP) (hf : interaction.1 = some forgery) :
    ∃ check ∈ support (FirstHit.record (checkForgeryP pk interaction.2 forgery) before),
      check.events = checked.events ∧ check.state = checked.state ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers pk forgery message witness ∧
        evalWithAnswerFn answers (verifyP message pk witness) = true ∧
        ∀ input ∈ queried answers (verifyP message pk witness),
          input ∈ queried answers (checkForgeryP pk interaction.2 forgery) := by
  simp only [GameWith.verdict, hf, PaddedGame.checker] at hr
  obtain ⟨check, hcheck, last, hlast, hvalue, hevents, hstate⟩ := FirstHit.record_bind_support _ _ before checked hr
  rw [FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hlast
  subst last
  simp only [List.append_nil] at hevents
  have hand : (decide (interaction.2.length ≤ 2 ^ 32) && check.value) = true := hvalue.symm.trans hwin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hand
  have ha' : ∀ input answer, SourceReplay.known check.state input = some answer → answers input = answer := by
    simpa only [hstate] using ha
  have hw := (SourceReplay.resolves_of_run _ (PaddedExtraction.check_hashOnly pk interaction.2 forgery) before
    (check.value, check.state) (FirstHit.recorded_support _ _ _ hcheck)).eval answers ha'
  rw [hand.2] at hw
  obtain ⟨-, message, witness, hof, hv, hsub⟩ := PaddedExtraction.check_accepting answers pk interaction.2 forgery hw
  exact ⟨check, hcheck, hevents.symm, hstate.symm, message, witness, hof, hv, hsub⟩
theorem honestProbe_slot (answers : Correctness.Answers) (N : HashOutput) (k : WCT9.Coord) (t : Fin 6)
    (p : Fin 4) :
    Guess.honestProbe answers (Guess.chainOf N k t, p) =
      pad64 (wctChainInputPW (WCT9.digestIndex N) k.val (WCT9.child N k).val t.val p.val 0 0 0
        (ClaudeWCT.W9.T3M.Extract.wctValue answers (WCT9.digestIndex N) k.val (WCT9.child N k).val t.val p.val)) := by
  rw [ClaudeWCT.W9.T3M.wctChainInputPW_zero, ClaudeWCT.WCT9.ftsChainInputW_padded]
  rfl
theorem verdict_chain_entries (pk : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (checked : FirstHit.Recorded Bool)
    (hr : checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker pk interaction) before))
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer)
    (hwin : checked.value = true) (forgery : ForgeryP) (hf : interaction.1 = some forgery)
    (m : Message) (w : WBytes) (hof : PaddedExtraction.WitnessOf answers pk forgery m w)
    (hH : ClaudeWCT.W9.T3M.WctExtract.WctHonest answers (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w) :
    ∀ (k : WCT9.Coord) (t : Fin 6) (c : Guess.GCoord),
      c.1 = Guess.chainOf (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) k t →
      c.2.val = 4 - Guess.deficit (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) k t →
      ∃ answer, (Guess.honestProbe answers c, answer) ∈ BPair.publicEntries checked.events := by
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting pk interaction before checked hr answers ha hwin forgery hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  set N := evalWithAnswerFn answers (digest (wrho w) m (wdc w)) with hN
  obtain ⟨N', -, hN', -, -, -, hqF, -⟩ := ClaudeWCT.W9.T3M.WctExtract.verifyP_walk_wct answers m pk w hv
  rw [← hN] at hN'
  subst hN'
  intro k t c hc1 hc2
  obtain ⟨a, p⟩ := c
  simp only at hc1 hc2
  subst hc1
  have hu : 1 ≤ WCT9.wordDigit (WCT9.rank N k) t := by
    have := p.isLt
    unfold Guess.deficit at hc2
    omega
  have hq := recoverFtsP_chain_queried answers N w k t hu
  obtain ⟨hval, hpad⟩ := (hH.2.1 k).1 t
  rw [hval, (hpad hu).1, (hpad hu).2] at hq
  have hp : 4 - WCT9.wordDigit (WCT9.rank N k) t = p.val := by
    unfold Guess.deficit at hc2
    omega
  rw [hp] at hq
  have hq' : (.inl (.inr (Guess.honestProbe answers (Guess.chainOf N k t, p))) : Spec.Domain) ∈
      queried answers (checkForgeryP pk interaction.2 forgery) := by
    rw [honestProbe_slot]
    exact hsub _ (hqF _ hq)
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence _
    (PaddedExtraction.check_hashOnly pk interaction.2 forgery) before check hcheck answers
    (by rw [hst]; exact ha) _ hq'
  rw [hev] at hevent
  exact ⟨_, SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hevent⟩
end ClaudeWCT.W9.T3.Security.CaseC
end
-- ==== merged from T3_Secc_WotsEncodingResample ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Enc
theorem uniform_resample {Ω K : Type} [Fintype Ω] [Nonempty Ω] {X : K → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → K) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) :
    (PMF.uniformOfFintype Ω).bind (fun ω => (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω)) =
      PMF.uniformOfFintype Ω := by
  classical
  let _ : DecidableEq Ω := Classical.decEq Ω
  let _ : DecidableEq K := Classical.decEq K
  apply PMF.ext
  intro ω₀
  obtain ⟨k₀, hk₀⟩ : ∃ k, k = d ω₀ := ⟨_, rfl⟩
  let σ : Ω × X k₀ → Ω × X k₀ := fun p =>
    if h : d p.1 = k₀ then (ov k₀ p.1 p.2, rd k₀ p.1) else p
  have hov : ∀ ω (h : d ω = k₀) (x : X k₀), d (ov k₀ ω x) = k₀ := by
    intro ω h x
    subst h
    exact h3 ω x
  have hσ : Function.Involutive σ := by
    rintro ⟨ω, x⟩
    by_cases h : d ω = k₀
    · have h' := hov ω h x
      simp only [σ, dif_pos h, dif_pos h']
      subst h
      rw [h2 ω x, h1 ω x]
    · simp only [σ, dif_neg h]
  have hinner : ∀ ω, (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
      if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
      else 0 := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h]
      have hgen : ∀ k (hk : d ω = k), (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
          (PMF.uniformOfFintype (X k)).map (ov k ω) ω₀ := by
        rintro k rfl; rfl
      rw [hgen k₀ h, PMF.map_apply]
      apply tsum_congr
      intro x
      simp only [σ, dif_pos h]
      by_cases he : ω₀ = ov k₀ ω x
      · rw [if_pos he, if_pos he.symm, mul_one]
      · rw [if_neg he, if_neg (fun h' => he h'.symm), mul_zero]
    · rw [if_neg h, PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      rw [if_neg]
      intro he
      apply h
      rw [hk₀, he, h3 ω x]
  rw [PMF.bind_apply]
  simp only [hinner]
  have hconst : ∀ (ω : Ω) (x : X k₀), PMF.uniformOfFintype Ω ω * PMF.uniformOfFintype (X k₀) x =
      PMF.uniformOfFintype (Ω × X k₀) (ω, x) := by
    intro ω x
    simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
    rw [ENNReal.mul_inv (by simp) (by simp)]
  have hfiber : ∀ ω, PMF.uniformOfFintype Ω ω *
      (if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
        else 0) =
      ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω, x) * (if (σ (ω, x)).1 = ω₀ then 1 else 0) := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      rw [← mul_assoc, hconst]
    · rw [if_neg h, mul_zero]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      have : (σ (ω, x)).1 = ω := by simp only [σ, dif_neg h]
      rw [this, if_neg (fun he => h (by rw [he, hk₀])), mul_zero]
  simp only [hfiber]
  rw [← ENNReal.tsum_prod (f := fun ω x => PMF.uniformOfFintype (Ω × X k₀) (ω, x) *
    (if (σ (ω, x)).1 = ω₀ then 1 else 0))]
  have hc : ∀ p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p = PMF.uniformOfFintype (Ω × X k₀) (σ p) := by
    intro p
    simp only [PMF.uniformOfFintype_apply]
  calc (∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (p.1, p.2) * (if (σ (p.1, p.2)).1 = ω₀ then 1 else 0))
      = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (σ p) * (if (σ p).1 = ω₀ then 1 else 0) := by
        apply tsum_congr
        intro p
        rw [← hc p]
    _ = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0) :=
        (hσ.toPerm σ).tsum_eq (fun p => PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0))
    _ = ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω₀, x) := by
        rw [ENNReal.tsum_prod']
        rw [tsum_eq_single ω₀]
        · simp only [if_true, mul_one]
        · intro ω hω
          apply ENNReal.tsum_eq_zero.mpr
          intro x
          rw [if_neg hω, mul_zero]
    _ = PMF.uniformOfFintype Ω ω₀ := by
        simp only [← hconst, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
theorem tsum_bind_mul {α β : Type} (μ : PMF α) (g : α → PMF β) (F : β → ENNReal) :
    ∑' b, (μ.bind g) b * F b = ∑' a, μ a * ∑' b, g a b * F b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [mul_assoc]
theorem tsum_map_mul {α β : Type} (μ : PMF α) (f : α → β) (F : β → ENNReal) :
    ∑' b, (μ.map f) b * F b = ∑' a, μ a * F (f a) := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a)]
  · rw [if_pos rfl]
  · intro b hb
    rw [if_neg hb, zero_mul]
theorem uniform_resample_tsum {Ω K : Type} [Fintype Ω] [Nonempty Ω] {X : K → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → K) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) (F : Ω → ENNReal) :
    ∑' ω, PMF.uniformOfFintype Ω ω * F ω =
      ∑' ω, PMF.uniformOfFintype Ω ω * ∑' x, PMF.uniformOfFintype (X (d ω)) x * F (ov (d ω) ω x) := by
  conv_lhs => rw [← uniform_resample d ov rd h1 h2 h3]
  rw [tsum_bind_mul]
  refine tsum_congr fun ω => ?_
  rw [tsum_map_mul]
theorem encInput_short (e : EncIndex) : encInput e ∈ SeccLaw.publicUniverse :=
  SeccLaw.mem_publicUniverse _ (by rw [encInput_length]; unfold SeccLaw.maxInputLength; omega)
section Overwrite
variable {U : Finset HashInput}
noncomputable def ov (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) : U → HashOutput :=
  fun u => if h : ∃ e, e ∈ k ∧ encInput e = u.val then y ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else pub u
noncomputable def rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) :
    k → HashOutput :=
  fun e => pub ⟨encInput e.val, hU (encInput_short e.val)⟩
end Overwrite
section Tables
variable (U : Finset HashInput)
theorem eagerAnswers_public_mem (privateTable : FullGame.FullTable) (pub : U → HashOutput) (u : U) :
    eagerAnswers U privateTable pub (.inl (.inr u.val)) = pub u := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U pub u.val = pub u
  rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U pub u.val u.property (by simp)]
theorem eagerAnswers_public_not_mem (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (input : HashInput) (h : input ∉ U) : eagerAnswers U privateTable pub (.inl (.inr input)) = (0 : HashOutput) := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U pub input = 0
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  simp [h]
  rfl
theorem tsum_uniform_coe {α : Type} (A : Finset α) (hA : A.Nonempty) (iN : Nonempty ↥A) (G : α → ENNReal) :
    ∑' x : ↥A, @PMF.uniformOfFintype ↥A _ iN x * G x.val = ∑' y, PMF.uniformOfFinset A hA y * G y := by
  classical
  have hr : ∀ y, PMF.uniformOfFinset A hA y * G y =
      (↑A : Set α).indicator (fun y => ((A.card : ENNReal))⁻¹ * G y) y := by
    intro y
    by_cases h : y ∈ A
    · rw [PMF.uniformOfFinset_apply, if_pos h, Set.indicator_apply, if_pos (Finset.mem_coe.mpr h)]
    · rw [PMF.uniformOfFinset_apply, if_neg h, zero_mul, Set.indicator_apply,
        if_neg (fun hm => h (Finset.mem_coe.mp hm))]
  simp only [hr]
  rw [← tsum_subtype (↑A : Set α) (fun y => ((A.card : ENNReal))⁻¹ * G y)]
  refine tsum_congr fun x => ?_
  rw [PMF.uniformOfFintype_apply, Fintype.card_coe]
end Tables
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsMaskChain ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem chainInputW_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    WCT9.chainInputW lay tree leaf i = WCT9.chainInputW L.lay L.tree L.leaf i := by
  funext step value
  unfold WCT9.chainInputW
  rw [chainInput_alias h i, chainHeader_congr_old h.1 h.2.1 h.2.2 rfl rfl, h.1]
theorem chainW_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    WCT9.chainW lay tree leaf i = WCT9.chainW L.lay L.tree L.leaf i := by
  funext start count value
  unfold WCT9.chainW
  rw [chainInputW_alias h i, h.1]
theorem eval_chain_one_maskAt {s : Nat} (hs : s < depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v) =
      if s + 1 = depth answers a then frontierValue answers a else 0 := by
  rw [eval_chainW_one', pad64_chainInputW, ← chainRowW_eq, maskAt_prefix answers a v hs]
  split
  · exact halfOf_joinHalf _ _ _
  · exact halfOf_zero _
theorem eval_chain_prefix_maskAt (hd : 1 ≤ depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 (depth answers a) v) =
      frontierValue answers a := by
  have h1 := eval_chainW_add' (maskAt answers a) a.key.lay a.key.tree a.key.leaf a.chain 0
    (depth answers a - 1) 1 v
  rw [Nat.zero_add, eval_chain_one_maskAt answers a (by omega), if_pos (Nat.sub_add_cancel hd),
    Nat.sub_add_cancel hd] at h1
  exact h1
theorem eval_chain_maskAt (hd : 1 ≤ depth answers a) {count : Nat} (hc : depth answers a ≤ count)
    (hc' : count ≤ 256) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count v) =
      evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth answers a + e := ⟨count - depth answers a, by omega⟩
  rw [eval_chainW_add', eval_chainW_add' answers, Nat.zero_add,
    eval_chain_prefix_maskAt answers a hd]
  change _ = evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (depth answers a) e
    (frontierValue answers a))
  refine Respects.eval_eq (S := fun q => maskAt answers a q = answers q) ?_ (fun q hq => hq)
  refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW, ← chainRowW_eq]
  exact maskAt_row_ge answers a value hlo (by omega)
/-- A WOTS seed only reads the coefficient cells `lowerSeedHeader lay tree p` of its tree (every layer: the seeds
are leaf-family evaluations, campaign X1 stage B, top leaves since campaign T8D). -/
theorem wotsSeed_congr_cells {T T' : Answers} {lay : Layer} (tree leaf i : Nat)
    (h : ∀ p, T (.inr (.inl (WCT9.lowerSeedHeader lay tree p))) = T' (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  rw [WCT9.wotsSeed_fam, WCT9.wotsSeed_fam]
  congr 2
  funext j
  unfold WCT9.famCoef WCT9.famCoefN WCT9.lowerSeedPair privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change WCT9.seedHalf ((T (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 0 128,
      (T (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 128 128) _ =
    WCT9.seedHalf ((T' (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 0 128,
      (T' (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 128 128) _
  rw [show header 0 lay.val tree (WCT9.famOrdinal lay leaf j.val / 2) 0 =
    WCT9.lowerSeedHeader lay tree (WCT9.famOrdinal lay leaf j.val / 2) from rfl, h]
/-- A WOTS seed only reads private cells. -/
theorem wotsSeed_congr_private {T T' : Answers} (h : ∀ c, T (.inr c) = T' (.inr c)) (lay : Layer)
    (tree leaf i : Nat) : WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i :=
  wotsSeed_congr_cells tree leaf i fun _ => h _
/-- img-v6 top family (39 coefficients per 4 leaves): aliased top leaves no longer share seeds unless the leaves are
small, so slots need small leaves on every layer (r3-lean-nonsec; every masked address is a source chain, whose leaf
is `< 2^24`, Final.hsize). -/
def SlotOK (a : ChainAddr) (_lay : Layer) (leaf : Nat) : Prop := leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24
def MaskOK (a : ChainAddr) : Prop := a.key.leaf < 2 ^ 24
theorem slotOK_of {a : ChainAddr} {lay : Layer} {leaf : Nat} (h : MaskOK a) (hl : leaf < 2 ^ 24) :
    SlotOK a lay leaf := ⟨hl, h⟩
theorem maskOK_of_lt {a : ChainAddr} (h : a.key.leaf < 2 ^ 24) : MaskOK a := h
theorem wotsSeed_maskAt (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsSeed (maskAt answers a) lay tree leaf i = WCT9.wotsSeed answers lay tree leaf i :=
  wotsSeed_congr_private (fun c => maskAt_private answers a c) lay tree leaf i
/-- Seeds of aliased leaves agree: the coefficient cells only see `tree % 2 ^ 40` and, for the top layer (one
family of 24 coefficients per leaf, an even count), `leaf % 2 ^ 32`; lower leaves need small leaf indices. -/
theorem wotsSeed_alias (T : Answers) {lay : Layer} {tree leaf : Nat} {L : LeafAddr}
    (h : LeafAlias lay tree leaf L) (hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24) (i : Nat) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T L.lay L.tree L.leaf i := by
  obtain ⟨hlay, ht, hlf⟩ := h
  subst hlay
  obtain ⟨hl, hL⟩ := hb
  have he : leaf = L.leaf := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlf
    exact hlf
  rw [WCT9.wotsSeed_fam, WCT9.wotsSeed_fam, WCT9.ofFn_famCoef, WCT9.ofFn_famCoef, he]
  refine congrArg (ClaudeWCT.Arith.familyEval · _) ?_
  unfold WCT9.famCoefL
  apply List.map_congr_left
  intro j _
  unfold WCT9.lowerSeedPair privatePair
  rw [header_normal 0 _ tree, header_normal 0 _ L.tree, ht]
end Mask
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_honestChain_maskAt (lay : Layer) (tree leaf i count : Nat) (hi : i < chainCount lay)
    (hc : count ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ count) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed (maskAt answers a) lay tree leaf i)) =
      evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed answers lay tree leaf i)) := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  have hi' : i < 2 ^ 24 := by
    have := chainCount_le lay
    simp only [Nat.reducePow]; omega
  have hc' : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  by_cases hal' : LeafAlias lay tree leaf a.key ∧ i = a.chain
  · obtain ⟨hal', rfl⟩ := hal'
    have hb' : leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24 := hb
    rw [chainW_alias hal', wotsSeed_alias _ hal' hb', wotsSeed_alias _ hal' hb']
    exact eval_chain_maskAt answers a (by omega) (halias hal' rfl) hc _
  · rw [wotsSeed_maskAt answers a lay tree leaf i]
    apply eval_maskAt_of_respects
    refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
    rw [pad64_chainInputW]
    intro s' v' hs' heq
    have hstep' : step < 256 := by omega
    have h := chainInputW_eq_chainRowW hi' hc' hstep' (by omega) heq
    exact hal' ⟨h.1, h.2.1⟩
theorem wotsEnd_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) (hb : SlotOK a lay leaf) :
    WCT9.wotsEnd (maskAt answers a) lay tree leaf i = WCT9.wotsEnd answers lay tree leaf i := by
  unfold WCT9.wotsEnd
  apply eval_honestChain_maskAt answers a lay tree leaf i _ hi (by have := width_le lay i; omega) hb
  intro hal' hia
  obtain ⟨hl', -, -⟩ := hal'
  subst hl' hia
  exact depth_le_width answers a hi
theorem wotsValue_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) (hi : i < chainCount lay)
    (hdig : digits.getD i 0 ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ digits.getD i 0) :
    WCT9.wotsValue (maskAt answers a) lay tree leaf digits i = WCT9.wotsValue answers lay tree leaf digits i :=
  eval_honestChain_maskAt answers a lay tree leaf i _ hi hdig hb halias
theorem wotsRoot_maskAt (lay : Layer) (tree leaf : Nat) (hb : SlotOK a lay leaf) :
    WCT9.wotsRoot (maskAt answers a) lay tree leaf = WCT9.wotsRoot answers lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_maskAt answers a lay tree leaf i (List.mem_range.mp hi) hb)]
  exact eval_maskAt_of_respects answers a (respectsP_lowerLeafHash a _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))
theorem height_pow_le (lay : Layer) : 2 ^ height lay ≤ 2 ^ 12 :=
  Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
/-- Top-nonce layer: a top node trial input is the nonce-slot node input, whose header is the top merkle tweak. -/
theorem pad64_topNodeInput_block4 (heap n : Nat) (left right : Digest) :
    pad64 (topNodeInput heap n left right) = block4 left (WCT9.merkleTweak 0 0 heap) (WCT9.nonceDigest n) right := by
  have h : topNodeInput heap n left right = block4 left (WCT9.merkleTweak 0 0 heap) (WCT9.nonceDigest n) right := by
    unfold topNodeInput block4
    rw [WCT9.merkleTweak_top0, WCT9.bytesLE_nonceDigest]
  rw [h]
  unfold pad64
  simp
theorem respectsP_topNodeHashN (heap n : Nat) (left right : Digest) :
    Respects (UntouchedP a) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  rw [pad64_topNodeInput_block4]
  exact untouchedP_of_hdr a _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ _ right)
    fun l tr leaf c step hs => merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs
theorem respectsP_topNonceSearch (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (UntouchedP a) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respectsP_topNodeHashN a _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respectsP_topNodeHashN a _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respectsP_topNonceSearch h heap left right fuel (n + 1)
theorem respectsP_buildTopLevels (leaves : List Digest) :
    Respects (UntouchedP a) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact respectsP_lowerNodeHash a 0 0 _ _ _ (Or.inl rfl)
  · unfold topNodeAt
    exact Respects.map _ (respectsP_topNonceSearch a _ _ _ _ _ _)
theorem wotsTree_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    WCT9.wotsTree (maskAt answers a) lay tree = WCT9.wotsTree answers lay tree := by
  have hroots : (List.range (2 ^ height lay)).map (WCT9.wotsRoot (maskAt answers a) lay tree) =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot answers lay tree) :=
    List.map_congr_left (fun leaf hleaf => wotsRoot_maskAt answers a lay tree leaf
      (slotOK_of hal (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))
  unfold WCT9.wotsTree
  rw [hroots]
  split_ifs with h0
  · exact eval_maskAt_of_respects answers a (respectsP_buildTopLevels a _)
  · exact eval_maskAt_of_respects answers a (respectsP_lowerLevels a _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
theorem builtTree_maskAt_top (hal : MaskOK a) :
    builtTree (maskAt answers a) 0 0 = builtTree answers 0 0 := by
  rw [← WCT9.wotsTree_top, ← WCT9.wotsTree_top, wotsTree_maskAt answers a 0 0 hal]
theorem leafRoot_maskAt_top (leaf : Nat) (hl : leaf < 2 ^ 24) (hal : MaskOK a) :
    Correctness.leafRoot (maskAt answers a) 0 0 leaf = Correctness.leafRoot answers 0 0 leaf := by
  rw [← WCT9.wotsRoot_top, ← WCT9.wotsRoot_top, wotsRoot_maskAt answers a 0 0 leaf (slotOK_of hal hl)]
theorem honestPair_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    Extract.honestPair (maskAt answers a) lay tree = Extract.honestPair answers lay tree := by
  unfold Extract.honestPair
  rw [wotsTree_maskAt answers a lay tree hal]
theorem ftsQuery_untouchedP {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    UntouchedP a q :=
  untouchedP_of_untouched a ⟨ClaudeWCT.WCT9.Wots.ftsQuery_untouched a h,
    ClaudeWCT.WCT9.Wots.ftsQuery_untouched (slotAddr a) h⟩
theorem honestTop_maskAt (index : Nat) :
    Extract.honestTop (maskAt answers a) index = Extract.honestTop answers index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr
    (fun _ hq => maskAt_untouched answers a (ftsQuery_untouchedP a hq))
end Mask
theorem leafMsg_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    leafMsg (maskAt answers a) L = leafMsg answers L := by
  unfold leafMsg
  split
  · rw [Mask.honestPair_maskAt answers a _ _ hal]
  · rw [Mask.honestTop_maskAt]
theorem referenceSearch_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceSearch (maskAt answers a) L = referenceSearch answers L := by
  unfold referenceSearch
  rw [leafMsg_maskAt answers a hal]
  exact Mask.eval_maskAt_of_respects answers a (Mask.respectsP_layerCounterSearch a _ _ _ _ _ _)
theorem referenceDigits_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceDigits (maskAt answers a) L = referenceDigits answers L := by
  unfold referenceDigits
  rw [referenceSearch_maskAt answers a hal]
theorem referenceInput_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceInput (maskAt answers a) L = referenceInput answers L := by
  unfold referenceInput
  rw [referenceSearch_maskAt answers a hal, leafMsg_maskAt answers a hal]
theorem depth_maskAt_all (answers : Answers) (a b : ChainAddr) (hal : Mask.MaskOK a) :
    depth (maskAt answers a) b = depth answers b := by
  unfold depth
  rw [referenceDigits_maskAt answers a hal]
theorem frontierValue_maskAt_other (answers : Answers) (a b : ChainAddr) (hb : b.chain < chainCount b.key.lay)
    (hbl : b.key.leaf < 2 ^ 24) (hal : Mask.MaskOK a)
    (halias : Mask.LeafAlias b.key.lay b.key.tree b.key.leaf a.key → b.chain = a.chain → depth answers a ≤ depth answers b) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  unfold frontierValue honestChainValueW
  rw [depth_maskAt_all answers a b hal]
  exact Mask.eval_honestChain_maskAt answers a _ _ _ _ _ hb (by have := Mask.depth_le_seven answers b; omega)
    (Mask.slotOK_of hal hbl) halias
theorem frontierValue_maskAt_bounded (answers : Answers) (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 24) (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  apply frontierValue_maskAt_other answers a b hc hb.2 ha.2
  intro hal hch
  have hk : b.key = a.key := by
    have := hal.eq_of_lt hb.1 (by omega) ha.1 (by omega)
    cases hbk : b.key
    rw [hbk] at this
    exact this
  have : b = a := by
    cases b; cases a
    simp only at hk hch
    rw [hk, hch]
  rw [this]
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
noncomputable def prefixStep (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers messages a ∧ input = chainRowW a step value then some (Classical.choose h) else none
/-- Mask of chain `a`: its rows below `depth` answer `0` (the last one answers the frontier, in the half its step
reads, C3 #866). Seeds are evaluations
of their leaf family at every layer (campaign X1 stage B, top leaves since campaign T8D), so no private cell is
blanked. -/
noncomputable def maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers messages a input with
      | some step => if step + 1 = depth answers messages a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers messages a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr c => answers (.inr c)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Mask
theorem chain_lt_of_depth (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (hd : 1 ≤ depth answers messages a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := referenceDigits_length answers messages a.key
  have h0 : depth answers messages a = 0 := List.getD_eq_default _ _ (by omega)
  omega
theorem depth_le_seven (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) : depth answers messages a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers messages a
  · exact (depth_le answers messages a (chain_lt_of_depth answers messages a hd)).trans (width_le _ _)
  · omega
theorem prefixStep_spec {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers messages a input = some step) :
    step < depth answers messages a ∧ ∃ value, input = chainRowW a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_chainRow (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers messages a (chainRowW a s v) = if s < depth answers messages a then some s else none := by
  have h7 := depth_le_seven answers messages a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers messages a ∧ chainRowW a s v = chainRowW a step value)
    exact congrArg some (chainRowW_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers messages a (chainRowW a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRowW_inj hs (by omega) heq).1
        omega
theorem prefixStep_untouched {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg} {a : ChainAddr} {input : HashInput}
    (h : UntouchedP a (.inl (.inr input))) : prefixStep answers messages a input = none := by
  cases hp : prefixStep answers messages a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers messages a; omega))
theorem maskAt_public (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (input : HashInput) :
    maskAt answers messages a (.inl (.inr input)) = match prefixStep answers messages a input with
      | some step => if step + 1 = depth answers messages a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers messages a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_private (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (c : Coordinate) :
    maskAt answers messages a (.inr c) = answers (.inr c) := rfl
theorem maskAt_tweak (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers messages a (.inr (.inl tweak)) = answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {q : Spec.Domain} (h : UntouchedP a q) :
    maskAt answers messages a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rfl
  · rfl
theorem maskAt_prefix (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers messages a) :
    maskAt answers messages a (.inl (.inr (chainRowW a s v))) =
      if s + 1 = depth answers messages a then
        joinHalf (WCT9.chainHigh a.key.lay a.chain s) (frontierValue answers messages a) 0 else 0 := by
  have h7 := depth_le_seven answers messages a
  rw [maskAt_public, prefixStep_chainRow answers messages a v (by omega), if_pos hs]
  rfl
theorem maskAt_row_ge (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers messages a ≤ s)
    (hs' : s < 256) : maskAt answers messages a (.inl (.inr (chainRowW a s v))) = answers (.inl (.inr (chainRowW a s v))) := by
  rw [maskAt_public, prefixStep_chainRow answers messages a v hs', if_neg (by omega)]
theorem maskAt_of_depth_zero (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (hd : depth answers messages a = 0) :
    maskAt answers messages a = answers := by
  funext q
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public]
    cases hp : prefixStep answers messages a input with
    | none => rfl
    | some step => have := (prefixStep_spec hp).1; omega
  · rfl
  · rfl
theorem eval_maskAt_of_respects (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    evalWithAnswerFn (maskAt answers messages a) program = evalWithAnswerFn answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers messages a hq).1
theorem queried_maskAt_of_respects (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    SourceReplay.queried (maskAt answers messages a) program = SourceReplay.queried answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers messages a hq).2
end Mask
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Mask
variable (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr)
theorem eval_chain_one_maskAt {s : Nat} (hs : s < depth answers messages a) (v : Digest) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v) =
      if s + 1 = depth answers messages a then frontierValue answers messages a else 0 := by
  rw [eval_chainW_one', pad64_chainInputW, ← chainRowW_eq, maskAt_prefix answers messages a v hs]
  split
  · exact halfOf_joinHalf _ _ _
  · exact halfOf_zero _
theorem eval_chain_prefix_maskAt (hd : 1 ≤ depth answers messages a) (v : Digest) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 (depth answers messages a) v) =
      frontierValue answers messages a := by
  have h1 := eval_chainW_add' (maskAt answers messages a) a.key.lay a.key.tree a.key.leaf a.chain 0
    (depth answers messages a - 1) 1 v
  rw [Nat.zero_add, eval_chain_one_maskAt answers messages a (by omega), if_pos (Nat.sub_add_cancel hd),
    Nat.sub_add_cancel hd] at h1
  exact h1
theorem eval_chain_maskAt (hd : 1 ≤ depth answers messages a) {count : Nat} (hc : depth answers messages a ≤ count)
    (hc' : count ≤ 256) (v : Digest) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count v) =
      evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth answers messages a + e := ⟨count - depth answers messages a, by omega⟩
  rw [eval_chainW_add', eval_chainW_add' answers, Nat.zero_add,
    eval_chain_prefix_maskAt answers messages a hd]
  change _ = evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (depth answers messages a) e
    (frontierValue answers messages a))
  refine Respects.eval_eq (S := fun q => maskAt answers messages a q = answers q) ?_ (fun q hq => hq)
  refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW, ← chainRowW_eq]
  exact maskAt_row_ge answers messages a value hlo (by omega)
theorem wotsSeed_maskAt (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsSeed (maskAt answers messages a) lay tree leaf i = WCT9.wotsSeed answers lay tree leaf i :=
  wotsSeed_congr_private (fun c => maskAt_private answers messages a c) lay tree leaf i
theorem eval_honestChain_maskAt (lay : Layer) (tree leaf i count : Nat) (hi : i < chainCount lay)
    (hc : count ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers messages a ≤ count) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed (maskAt answers messages a) lay tree leaf i)) =
      evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed answers lay tree leaf i)) := by
  by_cases hd : depth answers messages a = 0
  · rw [maskAt_of_depth_zero answers messages a hd]
  have hi' : i < 2 ^ 24 := by
    have := chainCount_le lay
    simp only [Nat.reducePow]; omega
  have hc' : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers messages a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  by_cases hal' : LeafAlias lay tree leaf a.key ∧ i = a.chain
  · obtain ⟨hal', rfl⟩ := hal'
    have hb' : leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24 := hb
    rw [chainW_alias hal', wotsSeed_alias _ hal' hb', wotsSeed_alias _ hal' hb']
    exact eval_chain_maskAt answers messages a (by omega) (halias hal' rfl) hc _
  · rw [wotsSeed_maskAt answers messages a lay tree leaf i]
    apply eval_maskAt_of_respects
    refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
    rw [pad64_chainInputW]
    intro s' v' hs' heq
    have hstep' : step < 256 := by omega
    have h := chainInputW_eq_chainRowW hi' hc' hstep' (by omega) heq
    exact hal' ⟨h.1, h.2.1⟩
theorem wotsEnd_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) (hb : SlotOK a lay leaf) :
    WCT9.wotsEnd (maskAt answers messages a) lay tree leaf i = WCT9.wotsEnd answers lay tree leaf i := by
  unfold WCT9.wotsEnd
  apply eval_honestChain_maskAt answers messages a lay tree leaf i _ hi (by have := width_le lay i; omega) hb
  intro hal' hia
  obtain ⟨hl', -, -⟩ := hal'
  subst hl' hia
  exact depth_le answers messages a hi
theorem wotsValue_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) (hi : i < chainCount lay)
    (hdig : digits.getD i 0 ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers messages a ≤ digits.getD i 0) :
    WCT9.wotsValue (maskAt answers messages a) lay tree leaf digits i = WCT9.wotsValue answers lay tree leaf digits i :=
  eval_honestChain_maskAt answers messages a lay tree leaf i _ hi hdig hb halias
theorem wotsRoot_maskAt (lay : Layer) (tree leaf : Nat) (hb : SlotOK a lay leaf) :
    WCT9.wotsRoot (maskAt answers messages a) lay tree leaf = WCT9.wotsRoot answers lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_maskAt answers messages a lay tree leaf i (List.mem_range.mp hi) hb)]
  exact eval_maskAt_of_respects answers messages a (respectsP_lowerLeafHash a _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))
theorem wotsTree_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    WCT9.wotsTree (maskAt answers messages a) lay tree = WCT9.wotsTree answers lay tree := by
  have hroots : (List.range (2 ^ height lay)).map (WCT9.wotsRoot (maskAt answers messages a) lay tree) =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot answers lay tree) :=
    List.map_congr_left (fun leaf hleaf => wotsRoot_maskAt answers messages a lay tree leaf
      (slotOK_of hal (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))
  unfold WCT9.wotsTree
  rw [hroots]
  split_ifs with h0
  · exact eval_maskAt_of_respects answers messages a (respectsP_buildTopLevels a _)
  · exact eval_maskAt_of_respects answers messages a (respectsP_lowerLevels a _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
theorem builtTree_maskAt_top (hal : MaskOK a) :
    builtTree (maskAt answers messages a) 0 0 = builtTree answers 0 0 := by
  rw [← WCT9.wotsTree_top, ← WCT9.wotsTree_top, wotsTree_maskAt answers messages a 0 0 hal]
theorem leafRoot_maskAt_top (leaf : Nat) (hl : leaf < 2 ^ 24) (hal : MaskOK a) :
    Correctness.leafRoot (maskAt answers messages a) 0 0 leaf = Correctness.leafRoot answers 0 0 leaf := by
  rw [← WCT9.wotsRoot_top, ← WCT9.wotsRoot_top, wotsRoot_maskAt answers messages a 0 0 leaf (slotOK_of hal hl)]
theorem honestPair_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    Extract.honestPair (maskAt answers messages a) lay tree = Extract.honestPair answers lay tree := by
  unfold Extract.honestPair
  rw [wotsTree_maskAt answers messages a lay tree hal]
end Mask
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Mask

theorem respects_layerCounterSearchAt (a : ChainAddr) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) : ∀ fuel counter,
    Respects (Untouched a) (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.CanonicalPolicy.layerCounterSearchAt]
      refine Respects.bind (Respects.publicHash _ (untouched_layerEncoding a _ _ _ _ _)) fun answer => ?_
      split
      · exact ih _
      · exact Respects.pure' _

theorem respectsP_layerCounterSearchAt (a : ChainAddr) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (UntouchedP a) (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) :=
  Respects.untouchedP (fun c => respects_layerCounterSearchAt c lay floor tree leaf msg fuel counter) a
end Mask

theorem searchOf_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) (remaining : Nat) :
    searchOf (maskAt answers messages a) messages L remaining = searchOf answers messages L remaining := by
  unfold searchOf
  exact Mask.eval_maskAt_of_respects answers messages a
    (Mask.respectsP_layerCounterSearchAt a _ _ _ _ _ _ _)

theorem referenceContext_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) :
    referenceContext (maskAt answers messages a) messages = referenceContext answers messages :=
  referenceContext_congr (fun L remaining _ => searchOf_maskAt answers messages a L remaining)

theorem referenceSearch_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) :
    referenceSearch (maskAt answers messages a) messages L = referenceSearch answers messages L :=
  referenceSearch_congr (fun L remaining _ => searchOf_maskAt answers messages a L remaining) L

theorem referenceDigits_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) :
    referenceDigits (maskAt answers messages a) messages L = referenceDigits answers messages L := by
  unfold referenceDigits
  rw [referenceSearch_maskAt]

theorem referenceInput_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) :
    referenceInput (maskAt answers messages a) messages L = referenceInput answers messages L := by
  unfold referenceInput
  rw [referenceSearch_maskAt]

theorem depth_maskAt_all (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a b : ChainAddr) : depth (maskAt answers messages a) messages b = depth answers messages b := by
  unfold depth
  rw [referenceDigits_maskAt]

theorem frontierValue_maskAt_other (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a b : ChainAddr) (hb : b.chain < chainCount b.key.lay) (hbl : b.key.leaf < 2 ^ 24)
    (hal : Wots.Mask.MaskOK a)
    (halias : SigGolfCandidate.T3.Security.Wots.Mask.LeafAlias b.key.lay b.key.tree b.key.leaf a.key →
      b.chain = a.chain → depth answers messages a ≤ depth answers messages b) :
    frontierValue (maskAt answers messages a) messages b = frontierValue answers messages b := by
  -- C3 (#866): the frontier is the chain of the current scheme (`honestChainValueW`).
  unfold frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [depth_maskAt_all]
  exact Mask.eval_honestChain_maskAt answers messages a _ _ _ _ _ hb
    (by have := Mask.depth_le_seven answers messages b; omega)
    (Wots.Mask.slotOK_of hal hbl) halias

theorem frontierValue_maskAt_bounded (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 24)
    (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers messages a) messages b = frontierValue answers messages b := by
  apply frontierValue_maskAt_other answers messages a b hc hb.2 ha.2
  intro hal hch
  have hk : b.key = a.key := by
    have := hal.eq_of_lt hb.1 (by omega) ha.1 (by omega)
    cases hbk : b.key
    rw [hbk] at this
    exact this
  have : b = a := by
    cases b; cases a
    simp only at hk hch
    rw [hk, hch]
  rw [this]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
