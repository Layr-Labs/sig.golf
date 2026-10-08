import SigGolfCandidate.ClaudeWCT.WCT9.Queries

namespace ClaudeWCT.WCT9.Cost
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_buildChild (index coord selected : Nat) (word : Rank) (carry : Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    CBound (fun result : (Digest × List Digest) × Digest => result.1.2.length = 7) (childCost selected)
      (buildChild index coord selected word carry) :=
  cbound_of_ftsBound (ftsBound_buildChild index coord selected word carry hcoord hsel)
theorem bound_buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    CBound (fun _ => True) 3518 (buildCoordinate index coord selected word) :=
  cbound_of_ftsBound (ftsBound_buildCoordinate index coord selected word)
theorem bound_forestPk (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    CBound (fun _ => True) 5 (WCT9.forestPk index pairs) :=
  cbound_of_ftsBound (ftsBound_forestPk index pairs hlen)
theorem bound_forestRows (index : Nat) (output : HashOutput) :
    CBound (fun state : List Opening × List (Digest × Digest) => state.1.length = 9 ∧ state.2.length = 9) 31662
      (forestRows index output) :=
  cbound_of_ftsBound (ftsBound_forestRows index output)
theorem bound_signForest (index : Nat) (output : HashOutput) :
    CBound (fun result : List Opening × Digest => result.1.length = 9) 31667 (signForest index output) :=
  cbound_of_ftsBound (ftsBound_signForest index output)
theorem bound_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord) :
    CBound (fun _ => True) 14 (recoverCoordinate sig index output coord) :=
  cbound_of_ftsBound (ftsBound_recoverCoordinate index sig output coord)
theorem bound_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    CBound (fun _ => True) 131 (recoverFts sig index output) :=
  cbound_of_ftsBound (ftsBound_recoverFts index sig output)
theorem signForest_blocks : 9 * (64 * (4 + 21 + 2) + 64 * (3 + 21 + 2) + 126) + 5 = 31667 := by norm_num
theorem verifyFts_blocks : 9 * (6 + 2 + 6) + 5 + 1 = 132 := by norm_num
def DigestResult (out : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ counter output, out = some (counter, output) → producerAdmissible output = true
theorem bound_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, CBound DigestResult fuel (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [DigestResult])
  | succ fuel ih =>
      intro counter
      unfold digestSearch
      refine (bound_digest rho message (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun output _ => ?_) (by omega)
      split
      · rename_i hgood
        refine .pure (some (BitVec.ofNat 32 counter, output)) fuel ?_
        intro other value hv
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
        exact hgood
      · exact ih (counter + 1)
theorem bound_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : BitVec 32) :
    CBound (fun _ => True) 1 (shortHash (layerEncodingInput lay tree leaf msg counter)) := by
  cases msg <;> apply bound_shortHash <;>
    simp [layerEncodingInput, encodingInput, pairEncodingInputP, pad64_length, SphincsSecurity.bytesLE_length]
theorem bound_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, CBound (CounterResult lay) fuel (layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [CounterResult])
  | succ fuel ih =>
      intro counter
      unfold layerCounterSearch
      refine (bound_layerEncoding lay tree leaf msg (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun answer _ => ?_) (by omega)
      cases hs : producerDecode lay answer with
      | none => exact ih (counter + 1)
      | some digits =>
          have hd := producerDecode_decode hs
          refine .pure (some (BitVec.ofNat 32 counter, digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1, (decode_length_sum hd).2, validDigits_decode hd⟩
def leafSeedsP (lay : Layer) (leaf : Nat) : Nat :=
  (lowerOrdinal lay leaf (chainCount lay) + 1) / 2 - (lowerOrdinal lay leaf 0 + 1) / 2
theorem seedCost_sum (a n : Nat) :
    (∑ i ∈ Finset.range n, seedCost (a + i)) = (a + n + 1) / 2 - (a + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold seedCost
      split <;> omega
theorem leafSeedsP_eq (lay : Layer) (leaf : Nat) :
    leafSeedsP lay leaf = ∑ i ∈ Finset.range (chainCount lay), seedCost (lowerOrdinal lay leaf i) := by
  unfold leafSeedsP lowerOrdinal
  rw [seedCost_sum, Nat.add_zero]
def digitTotal (lay : Layer) : Nat := ∑ i ∈ Finset.range (chainCount lay), maxDigit lay i
def leafCostP (lay : Layer) (leaf : Nat) : Nat := leafSeedsP lay leaf + digitTotal lay + leafHashCost lay
theorem bound_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (hd : ValidDigits lay digits)
    (carry : Digest) :
    CBound (fun result : (Digest × List Digest) × Digest => result.1.2.length = chainCount lay) (leafCostP lay leaf)
      (buildLeafP lay tree leaf digits carry) := by
  unfold buildLeafP
  refine Bound.bind' (l := leafHashCost lay) (Bound.foldlM_range (chainCount lay) _
    (fun i (state : List Digest × List Digest × Digest) => state.1.length = i ∧ state.2.1.length = i)
    (fun i => seedCost (lowerOrdinal lay leaf i) + maxDigit lay i) ([], [], carry) ⟨rfl, rfl⟩
    (fun i hi state hstate => ?_)) (fun state hstate => ?_) ?_
  · refine (show CBound (fun _ => True) (seedCost (lowerOrdinal lay leaf i))
        (packedSecret (lowerSeedPair lay tree) (lowerOrdinal lay leaf i) state.2.2) by
      unfold packedSecret seedCost
      split
      · exact (bound_privatePair 0 lay.val tree _ 0).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega)
      · exact .pure _ 0 trivial).bind' (l := maxDigit lay i) (fun sc _ => ?_) (by omega)
    have hc := hd i hi
    refine (bound_chain lay tree leaf i 0 (digits.getD i 0) _).bind'
      (l := maxDigit lay i - digits.getD i 0) (fun value _ => ?_) (by omega)
    refine (bound_chain lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0) value).bind'
      (l := 0) (fun last _ => ?_) (by omega)
    exact .pure _ 0 ⟨by simp only [List.length_append, List.length_singleton]; omega,
      by simp only [List.length_append, List.length_singleton]; omega⟩
  · refine (bound_leafHash lay tree leaf state.1 hstate.1).bind' (l := 0) (fun root _ => ?_) (by omega)
    exact .pure _ 0 hstate.2
  · unfold leafCostP digitTotal
    rw [Finset.sum_add_distrib, leafSeedsP_eq]
theorem bound_buildLevelsBelow (tag lay tree h : Nat) (leaves : List Digest) (hlen : leaves.length = 2 ^ h)
    (hh : 1 ≤ h) : CBound (LevelShape h (h - 1)) (2 ^ h - 2) (buildLevelsBelow tag lay tree h leaves) := by
  unfold buildLevelsBelow
  refine Bound.foldlM_range'_le 1 (h - 1) _ (LevelShape h) (fun i => 2 ^ (h - i) / 2) [leaves]
    ⟨rfl, fun j hj => by
      have he : j = 0 := by omega
      subst j
      simpa using hlen⟩
    (fun i hi levels hlevels => ?_) (fun _ h => h) ?_
  · have hprevious : (levels.getD (1 + i - 1) []).length = 2 ^ (h - i) := by
      simpa using hlevels.2 i le_rfl
    refine (bound_buildLevel tag lay tree h (1 + i) (levels.getD (1 + i - 1) [])).bind' (l := 0)
      (fun nodes hnodes => ?_) (by rw [hprevious]; omega)
    have hnext : nodes.length = 2 ^ (h - (i + 1)) := by
      rw [hprevious, show h - i = h - (i + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
        at hnodes
      exact hnodes
    refine .pure (levels ++ [nodes]) 0 ⟨by simp [hlevels.1], ?_⟩
    intro j hj
    by_cases hold : j ≤ i
    · rw [List.getD_append levels [nodes] [] j (by have := hlevels.1; omega)]
      exact hlevels.2 j hold
    · have he : j = i + 1 := by omega
      subst j
      rw [List.getD_append_right levels [nodes] [] (i + 1) (by have := hlevels.1; omega)]
      simp only [hlevels.1, Nat.sub_self, List.getD_cons_zero]
      exact hnext
  · have hs := sum_levels h
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega] at hs
    simp only [Nat.add_sub_cancel]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    norm_num at hs
    omega
def treeCostP (lay : Layer) : Nat := (∑ leaf ∈ Finset.range (2 ^ height lay), leafCostP lay leaf) + (2 ^ height lay - 2)
theorem bound_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) (hd : ValidDigits lay digits) :
    CBound (fun result => LevelShape (height lay) (height lay - 1) result.1) (treeCostP lay)
      (buildTreeP lay tree selected digits) := by
  unfold buildTreeP
  refine Bound.bind' (l := 2 ^ height lay - 2) (Bound.foldlM_range (2 ^ height lay) _
    (fun i (state : List Digest × List Digest × Digest) => state.1.length = i)
    (leafCostP lay) ([], [], 0) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) le_rfl
  · have hd' : ValidDigits lay (if leaf = selected then digits else []) := by
      split <;> first | exact hd | exact validDigits_nil lay
    refine (bound_buildLeafP lay tree leaf _ hd' state.2.2).bind' (l := 0) (fun result _ => ?_) (by omega)
    exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hstate
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure (levels, state.2.1) 0 hlevels) (by omega)
theorem chainCount_lower {lay : Layer} (hlay : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay <;> first | exact absurd rfl hlay | rfl
theorem maxDigit_lower {lay : Layer} (hlay : lay ≠ 0) (i : Nat) : maxDigit lay i = 7 := by
  unfold maxDigit; rw [if_neg hlay]
theorem leafSeedsP_lower {lay : Layer} (hlay : lay ≠ 0) (leaf : Nat) :
    leafSeedsP lay leaf = if leaf % 2 = 0 then 22 else 21 := by
  unfold leafSeedsP lowerOrdinal
  rw [chainCount_lower hlay]
  split <;> omega
theorem digitTotal_lower {lay : Layer} (hlay : lay ≠ 0) : digitTotal lay = 301 := by
  unfold digitTotal
  rw [chainCount_lower hlay]
  simp only [maxDigit_lower hlay, Finset.sum_const, Finset.card_range, smul_eq_mul]
theorem leafCostP_lower {lay : Layer} (hlay : lay ≠ 0) (leaf : Nat) :
    leafCostP lay leaf = (if leaf % 2 = 0 then 22 else 21) + 312 := by
  unfold leafCostP
  rw [leafSeedsP_lower hlay, digitTotal_lower hlay]
  simp only [leafHashCost, if_neg hlay]
theorem parity_sum (m : Nat) :
    (∑ leaf ∈ Finset.range (2 * m), ((if leaf % 2 = 0 then 22 else 21) + 312)) = m * 667 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : (2 * m) % 2 = 0 := by omega
      have h2 : (2 * m + 1) % 2 = 1 := by omega
      simp only [h1, h2, if_true, show (1 : Nat) ≠ 0 by decide, if_false]
      ring
theorem treeCostP_lower_eq {lay : Layer} (hlay : lay ≠ 0) :
    treeCostP lay = 2 ^ height lay / 2 * 667 + (2 ^ height lay - 2) := by
  unfold treeCostP
  have hh : 2 ^ height lay = 2 * (2 ^ height lay / 2) := by
    fin_cases lay <;> first | exact absurd rfl hlay | decide
  rw [Finset.sum_congr rfl (fun leaf _ => leafCostP_lower hlay leaf)]
  conv_lhs => rw [hh]
  rw [parity_sum, ← hh]
theorem treeCostP_lower :
    treeCostP 1 + 65 = treeCost 1 ∧ treeCostP 2 + 33 = treeCost 2 ∧ treeCostP 3 + 33 = treeCost 3 := by
  rw [treeCostP_lower_eq (by decide), treeCostP_lower_eq (by decide), treeCostP_lower_eq (by decide)]
  decide
def layerFixedCostP : Nat → Nat
  | 0 => 0
  | n + 1 => if n = 0 then layerFixedCost 1 else treeCostP (Fin.ofNat 4 n) + layerFixedCostP n
theorem layerFixedCostP_succ (n : Nat) :
    layerFixedCostP (n + 1) = if n = 0 then layerFixedCost 1 else treeCostP (Fin.ofNat 4 n) + layerFixedCostP n := rfl
theorem layerFixedCostP_one : layerFixedCostP 1 = layerFixedCost 1 := (layerFixedCostP_succ 0).trans (if_pos rfl)
theorem layerFixedCostP_succ_succ (n : Nat) :
    layerFixedCostP (n + 2) = treeCostP (Fin.ofNat 4 (n + 1)) + layerFixedCostP (n + 1) := rfl
theorem layerFixedCost_succ_succ (n : Nat) :
    layerFixedCost (n + 2) = treeCost (Fin.ofNat 4 (n + 1)) + layerFixedCost (n + 1) := rfl
theorem layerFixedCostP_four : layerFixedCostP 4 + 131 = layerFixedCost 4 := by
  obtain ⟨h1, h2, h3⟩ := treeCostP_lower
  have e3 : (Fin.ofNat 4 3 : Layer) = 3 := rfl
  have e2 : (Fin.ofNat 4 2 : Layer) = 2 := rfl
  have e1 : (Fin.ofNat 4 1 : Layer) = 1 := rfl
  simp only [layerFixedCostP_succ_succ, layerFixedCost_succ_succ, e3, e2, e1, Nat.zero_add, layerFixedCostP_one]
  omega
theorem bound_signLayersBC (cache : Cache) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + layerFixedCostP n) (signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero =>
      intro msg
      exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold signLayersBC
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg (searchLimit (Fin.ofNat 4 n)) 0).bind'
        (l := n * counterLimit + layerFixedCostP (n + 1)) (fun out hout => ?_)
        (by have := searchLimit_le (Fin.ofNat 4 n); simp only [Nat.add_mul, Nat.one_mul]; omega)
      by_cases hn : n = 0
      · subst n
        simp only [ite_true]
        have hlen : ((out.map Prod.snd).getD dummyTop).length = 54 := by
          cases out with
          | none => decide
          | some pair =>
              obtain ⟨counter, digits⟩ := pair
              exact (hout counter digits rfl).1
        have hsum : ((out.map Prod.snd).getD dummyTop).sum = 126 ∨
            ((out.map Prod.snd).getD dummyTop).sum = target 0 := by
          cases out with
          | none => first | exact Or.inl (by decide) | exact Or.inr (by decide)
          | some pair =>
              obtain ⟨counter, digits⟩ := pair
              exact Or.inr (hout counter digits rfl).2.1
        have h126 : 126 ≤ target 0 := by decide
        have hle : ((out.map Prod.snd).getD dummyTop).sum ≤ target 0 := by
          rcases hsum with h | h <;> omega
        first
          | exact (bound_signTop cache _ _ hlen (le_of_le_of_eq hle (by decide))).bind'
              (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp [layerFixedCostP, layerFixedCost])
          | exact (bound_signTop cache _ _ hlen (hsum.elim id fun h => h.trans (by decide))).bind'
              (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp [layerFixedCostP, layerFixedCost])
      · simp only [hn, ite_false]
        cases out with
        | none => exact .pure _ _ trivial
        | some pair =>
            obtain ⟨counter, digits⟩ := pair
            have hd := hout counter digits rfl
            dsimp only
            refine (bound_buildTreeP (Fin.ofNat 4 n) _ _ digits hd.2.2).bind'
              (l := n * counterLimit + layerFixedCostP n) (fun result _ => ?_)
              (by simp only [layerFixedCostP, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun previous _ => ?_) (by omega)
            cases previous <;> exact .pure _ 0 trivial
def recoverLayerPairCost (lay : Layer) : Nat := capacity lay - target lay + leafHashCost lay + (height lay - 1)
theorem recoverLayerPairCost_succ (lay : Layer) : recoverLayerPairCost lay + 1 = recoverLayerCost lay := by
  have : 1 ≤ height lay := by fin_cases lay <;> decide
  unfold recoverLayerPairCost recoverLayerCost
  omega
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerPairCost lay) (recoverLayerPair sig index lay digits) := by
  unfold recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => bound_chain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + (height lay - 1)) (fun ends hends => ?_) ?_
  · refine (bound_leafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp))
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerPairCost]
    omega
def recoveryLayersCostBC : Nat → Nat
  | 0 => 0
  | n + 1 => (if n = 0 then recoverLayerCost (Fin.ofNat 4 n) else recoverLayerPairCost (Fin.ofNat 4 n)) +
      recoveryLayersCostBC n
theorem recoveryLayersCostBC_add : recoveryLayersCostBC 4 + 3 = recoveryLayersCost 4 := by
  have h1 := recoverLayerPairCost_succ (Fin.ofNat 4 1)
  have h2 := recoverLayerPairCost_succ (Fin.ofNat 4 2)
  have h3 := recoverLayerPairCost_succ (Fin.ofNat 4 3)
  simp only [recoveryLayersCostBC, recoveryLayersCost, if_true, show (3 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 0 by decide, show (1 : Nat) ≠ 0 by decide, if_false]
  omega
theorem recoveryLayersCostBC_four_le : recoveryLayersCostBC 4 ≤ 481 := by
  have h := recoveryLayersCostBC_add
  have h4 := recoveryLayersCost_four
  omega
theorem bound_topDecodeRun (run : Fin (chainCount 0) → Nat → M Digest) (finish : List Digest → M Digest)
    (answer : Digest) (F : Nat) (hrun : ∀ i digit, CBound (fun _ => True) (maxDigit 0 i.val - digit) (run i digit))
    (hfinish : ∀ ends : List Digest, ends.length = chainCount 0 → CBound (fun _ => True) F (finish ends))
    (hF : capacity 0 - target 0 + F ≤ capacity 0) :
    CBound (fun _ => True) (capacity 0) (topDecodeRun run finish answer) := by
  cases hd : decode 0 answer with
  | some digits =>
      rw [topDecodeRun_of_decode hd]
      refine Bound.map some ((Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
        (fun i => maxDigit 0 i.val - digits.getD i.val 0) (fun i _ => hrun i _)).bind' (l := F)
        (fun ends hends => hfinish ends (by simpa using hends)) ?_) (fun _ _ => trivial)
      rw [sum_finRange (chainCount 0) (fun i => maxDigit 0 i - digits.getD i 0),
        remaining_steps 0 digits (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2]
      exact hF
  | none =>
      rw [topDecodeRun_of_decode_none hd]
      unfold topRejectChains
      refine Bound.map _ ((Bound.mapM_list (P := GoodQuery) _ _ (fun i => maxDigit 0 i.val)
        (fun i _ => (hrun i _).mono_k (Nat.sub_le _ _))).mono_k ?_) (fun _ _ => trivial)
      have hsplit := congrArg (fun l : List (Fin (chainCount 0)) => (l.map fun i => maxDigit 0 i.val).sum)
        (List.take_append_drop (topRejectLength answer) (List.finRange (chainCount 0)))
      simp only [List.map_append, List.sum_append] at hsplit
      have htot : ((List.finRange (chainCount 0)).map fun i => maxDigit 0 i.val).sum = capacity 0 := by
        rw [sum_finRange (chainCount 0) (fun i => maxDigit 0 i), capacity_sum]
      omega
theorem bound_verifyTop (sig : Signature) (index : Nat) (answer : Digest) :
    CBound (fun _ => True) (capacity 0) (verifyTop sig index answer) := by
  unfold verifyTop
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  dsimp only
  refine bound_topDecodeRun _ _ answer (leafHashCost 0 + height 0) (fun i digit => bound_chain _ _ _ _ _ _ _)
    (fun ends hends => ?_) (by decide)
  refine (bound_leafHash 0 _ _ ends hends).bind (fun root _ => ?_)
  exact (Bound.foldlM_list (P := GoodQuery) (List.finRange (height 0)) _ (fun _ _ => True) (fun _ => 1) root
    trivial (fun i hi value _ => bound_nodeHash _ _ _ _ _ _)).mono_k (by simp)
def verifyLayersCostBC : Nat → Nat
  | 0 => 0
  | n + 1 => (if n = 0 then capacity 0 else recoverLayerPairCost (Fin.ofNat 4 n)) + verifyLayersCostBC n
theorem verifyLayersCostBC_four_le : verifyLayersCostBC 4 ≤ 573 := by decide
theorem bound_verifyLayersBC (w : Witness) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n + verifyLayersCostBC n) (verifyLayersBC w index n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold verifyLayersBC
      dsimp only
      split
      · exact .pure _ _ trivial
      · refine (bound_layerEncoding _ _ _ msg _).bind'
          (l := verifyLayersCostBC (n + 1) + n) (fun answer _ => ?_) (by simp only [verifyLayersCostBC]; omega)
        by_cases hn : n = 0
        · subst n
          rw [if_pos rfl]
          exact (bound_verifyTop w.signature index answer).mono_k (by simp [verifyLayersCostBC])
        · rw [if_neg hn]
          cases hd : decode (Fin.ofNat 4 n) answer with
          | none => exact .pure _ _ trivial
          | some digits =>
              dsimp only
              exact (bound_recoverLayerPair w.signature index (Fin.ofNat 4 n) digits
                (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2).bind'
                (l := n + verifyLayersCostBC n) (fun pair _ => ih _)
                (by simp only [verifyLayersCostBC, hn, ite_false]; omega)
theorem bound_expandLayersBC (sig : Signature) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + recoveryLayersCostBC n) (expandLayersBC sig index n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold expandLayersBC
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) _ _ msg (searchLimit (Fin.ofNat 4 n)) 0).bind'
        (l := recoveryLayersCostBC (n + 1) + n * counterLimit)
        (fun found hf => ?_)
        (by have := searchLimit_le (Fin.ofNat 4 n); simp only [recoveryLayersCostBC, Nat.add_mul, Nat.one_mul]; omega)
      cases found with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hf counter digits rfl
          dsimp only
          by_cases hn : n = 0
          · subst n
            simp only [ite_true]
            refine (bound_recoverLayer _ index (Fin.ofNat 4 0) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := 0) (fun value _ => .pure _ 0 trivial) (by simp [recoveryLayersCostBC])
          · simp only [hn, ite_false]
            refine (bound_recoverLayerPair sig index (Fin.ofNat 4 n) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := n * counterLimit + recoveryLayersCostBC n) (fun value _ => ?_)
              (by simp only [recoveryLayersCostBC, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun result _ => ?_) (by omega)
            cases result <;> exact .pure _ 0 trivial
def signPayloadFixed : Nat := 2 + 31667 + layerFixedCostP 4
theorem signPayloadFixed_eq : signPayloadFixed + 707 = 2 + 32243 + layerFixedCost 4 := by
  have h := layerFixedCostP_four
  unfold signPayloadFixed
  omega
theorem bound_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + limit + 4 * counterLimit) (signPayloadWith limit cache message) := by
  rw [signPayloadWith_eq]
  refine (bound_privateNonce message).bind' (l := signPayloadFixed - 2 + limit + 4 * counterLimit)
    (fun rho _ => ?_) (by unfold signPayloadFixed; omega)
  refine (bound_digestSearch rho message limit 0).bind' (l := signPayloadFixed - 2 + 4 * counterLimit)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_signForest _ output).bind' (l := layerFixedCostP 4 + 4 * counterLimit)
        (fun forest _ => ?_) (by unfold signPayloadFixed; omega)
      refine (bound_signLayersBC cache _ 4 (.forest forest.2)).bind' (l := 0) (fun layers _ => ?_)
        (by omega)
      cases layers <;> exact .pure _ 0 trivial
theorem bound_signWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + 2 + limit + 4 * counterLimit) (signWith limit cache message) := by
  unfold signWith
  refine (bound_privateMac cache.region).bind' (l := signPayloadFixed + limit + 4 * counterLimit)
    (fun tag _ => ?_) (by omega)
  split
  · exact .pure _ _ trivial
  · exact bound_signPayloadWith limit cache message
theorem bound_verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 709 (verifyWith limit message pk w) := by
  unfold verifyWith
  split
  · exact .pure _ _ trivial
  · refine (bound_digest w.signature.rho message w.digestCounter).bind' (l := 708)
      (fun output _ => ?_) (by decide)
    dsimp only
    split
    · exact .pure _ _ trivial
    · refine (bound_recoverFts w.signature _ output).bind' (l := 577) (fun root _ => ?_) (by decide)
      refine (bound_verifyLayersBC w _ 4 (.forest root)).bind' (l := 0) (fun r _ => ?_)
        (by have := verifyLayersCostBC_four_le; omega)
      cases r <;> exact .pure _ 0 trivial
theorem bound_expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (limit + 4 * counterLimit + 612) (expandWith limit message pk sig) := by
  unfold expandWith
  refine (bound_digestSearch sig.rho message limit 0).bind' (l := 4 * counterLimit + 612)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_recoverFts sig _ output).bind' (l := 4 * counterLimit + 481)
        (fun root _ => ?_) (by omega)
      refine (bound_expandLayersBC sig _ 4 (.forest root)).bind' (l := 0)
        (fun layers _ => ?_) (by have := recoveryLayersCostBC_four_le; omega)
      cases layers with
      | none => exact .pure _ 0 trivial
      | some pair =>
          obtain ⟨root, counters⟩ := pair
          dsimp only
          split <;> exact .pure _ 0 trivial
theorem bound_signPayload (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + digestAttemptLimit + 4 * counterLimit) (Rev3.signPayload cache message) :=
  bound_signPayloadWith digestAttemptLimit cache message
theorem bound_sign (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + 2 + digestAttemptLimit + 4 * counterLimit) (Rev3.sign cache message) :=
  bound_signWith digestAttemptLimit cache message
theorem bound_verify (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 709 (Rev3.verify message pk w) :=
  bound_verifyWith digestVerifyLimit message pk w
theorem sign_compression_ceiling (secret : BitVec 256) (cache : Cache) (message : Message) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.sign cache message))),
      result.2 ≤ 18992537 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_sign cache message).count_support result
    (realize_support_subset secret _ hr) |>.2
  have h := signPayloadFixed_eq
  rw [layerFixedCost_four] at h
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit]; omega)
theorem verify_compression_bound (secret : BitVec 256) (message : Message) (pk : Digest) (w : Witness) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.verify message pk w))), result.2 ≤ 709 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  exact (bound_verify message pk w).count_support result (realize_support_subset secret _ hr) |>.2
end ClaudeWCT.WCT9.Cost
