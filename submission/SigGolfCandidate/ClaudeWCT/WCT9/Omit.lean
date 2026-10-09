import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.WCT9.Cost

/-! # H2: two omitted signature bytes, recovered by a 2^16 search against the public key

`Limits.lean` defines the omission (`setTop`, `fillTop`, `proj`, `topSib`) and the expander `expandS`: it runs the
old expansion on `proj sig` (the omitted top 16 bits of the top layer's level-11 sibling read as zero), keeps the
level-11 node `v`, and if the root is not the public key it searches the completions `c = 1, 2, ...` with one node
hash each. This file relates `expandS` to the old expander `expandWith`: every answer of `expandS` is the answer of
`expandWith` on a completion `fillTop sig c` (`eval_expandS`), and whenever `expandWith` succeeds on a signature,
`expandS` succeeds on it too (`expandS_complete`). Exact recovery of the original bits is not claimed. -/

section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ### Bits -/

theorem setTop_toNat (d : Digest) (c : Nat) :
    (setTop d c).toNat = d.toNat % 2 ^ 112 + c % 2 ^ 16 * 2 ^ 112 := by
  unfold setTop
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 : d.toNat % 2 ^ 112 < 2 ^ 112 := Nat.mod_lt _ (by positivity)
  have h2 : c % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by positivity)
  have h3 : c % 2 ^ 16 * 2 ^ 112 ≤ (2 ^ 16 - 1) * 2 ^ 112 := Nat.mul_le_mul_right _ (by omega)
  have h4 : (2 ^ 16 - 1) * 2 ^ 112 + 2 ^ 112 = (2 : Nat) ^ 128 := by norm_num
  omega

theorem setTop_setTop (d : Digest) (a b : Nat) : setTop (setTop d a) b = setTop d b := by
  apply BitVec.eq_of_toNat_eq
  rw [setTop_toNat, setTop_toNat, setTop_toNat]
  congr 1
  rw [Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem setTop_self (d : Digest) : setTop d (d.toNat / 2 ^ 112) = d := by
  apply BitVec.eq_of_toNat_eq
  rw [setTop_toNat]
  have hd := d.isLt
  have h : d.toNat / 2 ^ 112 < 2 ^ 16 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num at hd ⊢
    omega
  rw [Nat.mod_eq_of_lt h]
  have := Nat.mod_add_div d.toNat (2 ^ 112)
  rw [Nat.mul_comm] at this
  omega

theorem top_lt (d : Digest) : d.toNat / 2 ^ 112 < 2 ^ 16 := by
  have hd := d.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at hd ⊢
  omega

/-! ### Completions -/

theorem fillLayer_values (lay : Layer) (ls : LayerSignature lay) (c : Nat) :
    (fillLayer lay ls c).values = ls.values := rfl

theorem fillLayer_path_ne (lay : Layer) (ls : LayerSignature lay) (c : Nat) (j : Fin (height lay))
    (hj : ¬(lay.val = 0 ∧ j.val = 11)) : (fillLayer lay ls c).path j = ls.path j := by
  simp only [fillLayer, if_neg hj]

theorem fillLayer_ne (lay : Layer) (ls : LayerSignature lay) (c : Nat) (h : lay.val ≠ 0) :
    fillLayer lay ls c = ls := by
  cases ls with
  | mk values path =>
    simp only [fillLayer, LayerSignature.mk.injEq, true_and]
    funext j
    rw [if_neg (fun h' => h h'.1)]

theorem fillLayer_fillLayer (lay : Layer) (ls : LayerSignature lay) (a b : Nat) :
    fillLayer lay (fillLayer lay ls a) b = fillLayer lay ls b := by
  cases ls with
  | mk values path =>
    simp only [fillLayer, LayerSignature.mk.injEq, true_and]
    funext j
    by_cases hj : lay.val = 0 ∧ j.val = 11
    · simp only [if_pos hj, setTop_setTop]
    · simp only [if_neg hj]

@[simp] theorem fillTop_rho (sig : Signature) (c : Nat) : (fillTop sig c).rho = sig.rho := rfl
@[simp] theorem fillTop_openings (sig : Signature) (c : Nat) : (fillTop sig c).openings = sig.openings := rfl
theorem fillTop_layers (sig : Signature) (c : Nat) (lay : Layer) :
    (fillTop sig c).layers lay = fillLayer lay (sig.layers lay) c := rfl

theorem fillTop_fillTop (sig : Signature) (a b : Nat) : fillTop (fillTop sig a) b = fillTop sig b := by
  unfold fillTop
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b

theorem proj_fillTop (sig : Signature) (c : Nat) : proj (fillTop sig c) = proj sig := by
  unfold proj; exact fillTop_fillTop sig c 0

theorem proj_proj (sig : Signature) : proj (proj sig) = proj sig := proj_fillTop sig 0

theorem fillTop_proj (sig : Signature) (c : Nat) : fillTop (proj sig) c = fillTop sig c := by
  unfold proj; exact fillTop_fillTop sig 0 c

theorem topSib_fillTop (sig : Signature) (c : Nat) : topSib (fillTop sig c) = setTop (topSib sig) c := by
  unfold topSib
  rw [fillTop_layers]
  simp only [fillLayer]
  rw [if_pos ⟨rfl, rfl⟩]

theorem fillTop_self (sig : Signature) : fillTop sig ((topSib sig).toNat / 2 ^ 112) = sig := by
  cases sig with
  | mk rho openings layers =>
    unfold fillTop
    simp only [Signature.mk.injEq, true_and]
    funext lay
    cases hls : layers lay with
    | mk values path =>
      simp only [fillLayer, LayerSignature.mk.injEq, true_and]
      funext j
      by_cases hj : lay.val = 0 ∧ j.val = 11
      · rw [if_pos hj]
        have hl : lay = 0 := Fin.ext hj.1
        subst hl
        have hjj : j = topJ := Fin.ext hj.2
        subst hjj
        have : topSib ⟨rho, openings, layers⟩ = path topJ := by
          unfold topSib; simp only [hls]
        rw [this, setTop_self]
      · rw [if_neg hj]

theorem fillLayer_rest (lay : Layer) (ls : LayerSignature lay) (a b : Nat) (j : Fin (height lay))
    (hj : ¬(lay.val = 0 ∧ j.val = 11)) : (fillLayer lay ls a).path j = (fillLayer lay ls b).path j := by
  rw [fillLayer_path_ne _ _ _ _ hj, fillLayer_path_ne _ _ _ _ hj]

/-! ### The top layer split at its last node -/

theorem recoverLayer_unfold (sig : SigGolfCandidate.T3.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    recoverLayer sig index lay digits =
      ((List.finRange (chainCount lay)).mapM fun i => SigGolfCandidate.T3.chain lay (route index lay).2
        (route index lay).1 i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        ((sig.layers lay).values i)) >>=
      fun ends => SigGolfCandidate.T3.leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
        (List.finRange (height lay)).foldlM (fun value j => do
          let other := (sig.layers lay).path j
          let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
          nodeHash 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
            pair.1 pair.2) value := rfl

theorem finRange_top_split : List.finRange (height (0 : Layer)) = (List.finRange (height 0)).take 11 ++ [topJ] := by
  decide

theorem take_top_lt : ∀ j ∈ (List.finRange (height (0 : Layer))).take 11, j.val < 11 := by
  decide

theorem recoverLayer_top (sig : Signature) (index : Nat) (digits : List Nat) :
    recoverLayer (toT3Signature sig) index 0 digits =
      topFold sig index digits >>= fun v => topNode index v (topSib sig) := by
  rw [recoverLayer_unfold]
  unfold topFold topEnds
  simp only [bind_assoc]
  refine bind_congr fun ends => ?_
  refine bind_congr fun value => ?_
  conv_lhs => rw [finRange_top_split]
  simp only [List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

theorem foldlM_congr_mem {m : Type → Type} [Monad m] {α β : Type} (f g : α → β → m α) :
    ∀ (l : List β), (∀ a, ∀ b ∈ l, f a b = g a b) → ∀ init, l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | b :: l, h, init => by
      rw [List.foldlM_cons, List.foldlM_cons, h init b (List.mem_cons_self ..)]
      refine bind_congr fun x => ?_
      exact foldlM_congr_mem f g l (fun a b' hb => h a b' (List.mem_cons_of_mem _ hb)) x

theorem topStep_fill (sig : Signature) (index : Nat) (a b : Nat) (value : Digest) (j : Fin (height 0))
    (hj : j.val < 11) : topStep (fillTop sig a) index value j = topStep (fillTop sig b) index value j := by
  unfold topStep
  rw [fillTop_layers, fillTop_layers, fillLayer_rest 0 (sig.layers 0) a b j (fun h => by omega)]

theorem topFold_fill (sig : Signature) (index : Nat) (digits : List Nat) (a b : Nat) :
    topFold (fillTop sig a) index digits = topFold (fillTop sig b) index digits := by
  unfold topFold topEnds
  rw [fillTop_layers, fillTop_layers, fillLayer_values, fillLayer_values]
  refine bind_congr fun ends => ?_
  refine bind_congr fun value => ?_
  exact foldlM_congr_mem _ _ _ (fun x j hj => topStep_fill sig index a b x j (take_top_lt j hj)) value

theorem topFold_proj (sig : Signature) (index : Nat) (digits : List Nat) :
    topFold (proj sig) index digits = topFold sig index digits := by
  have h := topFold_fill sig index digits 0 ((topSib sig).toNat / 2 ^ 112)
  rw [fillTop_self] at h
  exact h

theorem recoverLayerPair_fill (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) (c : Nat)
    (h : lay.val ≠ 0) : recoverLayerPair (fillTop sig c) index lay digits = recoverLayerPair sig index lay digits := by
  unfold recoverLayerPair
  rw [fillTop_layers, fillLayer_ne lay (sig.layers lay) c h]

theorem fin_ofNat_succ_ne (k : Nat) (hk : k + 1 < 4) : (Fin.ofNat 4 (k + 1) : Layer).val ≠ 0 := by
  simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hk]
  omega

/-- The old layer expansion is the new one on `proj sig` with the old sibling, with `v` dropped. -/
theorem expandLayersBC_eq_T (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg, expandLayersBC sig index n msg =
      (Option.map fun x => (x.2.1, x.2.2)) <$> expandLayersT (proj sig) index (topSib sig) n msg := by
  intro n
  induction n with
  | zero => intro _ msg; simp [expandLayersBC, expandLayersT]
  | succ n ih =>
    intro hn msg
    simp only [expandLayersBC, expandLayersT, map_bind]
    refine bind_congr fun r => ?_
    rcases r with _ | ⟨counter, digits⟩
    · simp
    · cases n with
      | zero =>
        simp only [if_true, map_bind, map_pure, Option.map_some]
        have h0 : (Fin.ofNat 4 0 : Layer) = 0 := rfl
        rw [h0, recoverLayer_top, topFold_proj, bind_assoc]
      | succ k =>
        have hne := fin_ofNat_succ_ne k (by omega)
        simp only [Nat.succ_ne_zero, if_false, map_bind]
        unfold proj
        rw [recoverLayerPair_fill sig index _ digits 0 hne]
        refine bind_congr fun pair => ?_
        rw [ih (by omega), bind_map_left]
        unfold proj
        refine bind_congr fun r' => ?_
        rcases r' with _ | ⟨v, root, counters⟩ <;> simp

/-- Changing the top sibling only changes the last node hash. -/
theorem eval_expandLayersT_other (answers : Answers) (s : Signature) (index : Nat) (o o' : Digest) :
    ∀ n msg, evalWithAnswerFn answers (expandLayersT s index o' n msg) =
      (evalWithAnswerFn answers (expandLayersT s index o n msg)).map
        (fun x => (x.1, evalWithAnswerFn answers (topNode index x.1 o'), x.2.2)) := by
  intro n
  induction n with
  | zero => intro msg; simp [expandLayersT]
  | succ n ih =>
    intro msg
    simp only [expandLayersT, evalWithAnswerFn_bind]
    cases evalWithAnswerFn answers (layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
    | none => simp
    | some found =>
      obtain ⟨counter, digits⟩ := found
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false, evalWithAnswerFn_bind, ih]
        cases evalWithAnswerFn answers (expandLayersT s index o n _) with
        | none => simp
        | some x => simp

theorem map_some_inv {α β : Type} {f : α → β} {x : Option α} {y : β} (h : x.map f = some y) :
    ∃ a, x = some a ∧ f a = y := by
  cases x with
  | none => simp at h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

/-! ### The search -/

theorem eval_searchTop (answers : Answers) (index : Nat) (v sib pk : Digest) :
    ∀ fuel c0 c, evalWithAnswerFn answers (searchTop index v sib pk fuel c0) = some c →
      c0 ≤ c ∧ c < c0 + fuel ∧ evalWithAnswerFn answers (topNode index v (setTop sib c)) = pk := by
  intro fuel
  induction fuel with
  | zero => intro c0 c h; simp [searchTop] at h
  | succ fuel ih =>
    intro c0 c h
    simp only [searchTop, evalWithAnswerFn_bind] at h
    split at h
    · rename_i hr
      simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
      subst h
      exact ⟨le_refl _, by omega, hr⟩
    · obtain ⟨h1, h2, h3⟩ := ih (c0 + 1) c h
      exact ⟨by omega, by omega, h3⟩

theorem searchTop_complete (answers : Answers) (index : Nat) (v sib pk : Digest) :
    ∀ fuel c0 c, c0 ≤ c → c < c0 + fuel → evalWithAnswerFn answers (topNode index v (setTop sib c)) = pk →
      ∃ c', evalWithAnswerFn answers (searchTop index v sib pk fuel c0) = some c' := by
  intro fuel
  induction fuel with
  | zero => intro c0 c h1 h2; omega
  | succ fuel ih =>
    intro c0 c h1 h2 h3
    simp only [searchTop, evalWithAnswerFn_bind]
    split
    · exact ⟨c0, rfl⟩
    · rename_i hne
      by_cases hc : c = c0
      · subst hc; exact absurd h3 hne
      · exact ih (c0 + 1) c (by omega) (by omega) h3

/-! ### The old expander with its digest output -/

/-- `expandWith` keeping the digest output (the W9 witness encoding needs it). -/
def expandWithN (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option (HashOutput × Witness)) := do
  let some (counter, output) ← digestSearch sig.rho message 0 limit | pure none
  let index := digestIndex output
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.forest root) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))

theorem expandWith_eq_N (limit : Nat) (m : Message) (pk : Digest) (σ : Signature) :
    expandWith limit m pk σ = Option.map Prod.snd <$> expandWithN limit m pk σ := by
  unfold expandWith expandWithN
  rw [map_bind]; congr 1; funext r
  rcases r with _ | ⟨counter, output⟩
  · simp
  · simp only
    rw [map_bind]; congr 1; funext root
    rw [map_bind]; congr 1; funext r
    rcases r with _ | ⟨root, counters⟩
    · simp
    · simp only
      split <;> simp

theorem recoverFts_fillTop (sig : Signature) (c : Nat) (index : Nat) (output : HashOutput) :
    recoverFts (fillTop sig c) index output = recoverFts sig index output := rfl

theorem eval_expandWithN_fill (answers : Answers) (limit : Nat) (m : Message) (pk : Digest) (σ : Signature)
    (c : Nat) :
    evalWithAnswerFn answers (expandWithN limit m pk (fillTop σ c)) =
      match evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
      | none => none
      | some (counter, output) =>
        match (evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
            (.forest (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output))))).map
            (fun x => (x.1, evalWithAnswerFn answers (topNode (digestIndex output) x.1 (setTop (topSib σ) c)),
              x.2.2)) with
        | none => none
        | some (_, root, counters) =>
          if root ≠ pk then none else some (output, ⟨fillTop σ c, counter, fun lay => counters.getD lay.val 0⟩) := by
  unfold expandWithN
  simp only [evalWithAnswerFn_bind, fillTop_rho]
  cases evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
  | none => rfl
  | some found =>
    obtain ⟨counter, output⟩ := found
    simp only [evalWithAnswerFn_bind, recoverFts_fillTop]
    rw [expandLayersBC_eq_T (fillTop σ c) _ 4 le_rfl, evalWithAnswerFn_map, proj_fillTop, topSib_fillTop,
      eval_expandLayersT_other answers (proj σ) _ (topSib (proj σ)) (setTop (topSib σ) c), Option.map_map]
    cases evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
        (.forest (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)))) with
    | none => rfl
    | some x =>
      obtain ⟨v, root, counters⟩ := x
      simp only [Option.map_some, Function.comp]
      split <;> simp_all

theorem topSib_proj (σ : Signature) : topSib (proj σ) = setTop (topSib σ) 0 := by
  unfold proj; exact topSib_fillTop σ 0

/-- Every answer of the H2 expander is the old expander's answer on some completion. -/
theorem eval_expandS (answers : Answers) (limit : Nat) (m : Message) (pk : Digest) (σ : Signature)
    (N : HashOutput) (w : Witness) (h : evalWithAnswerFn answers (expandS limit m pk σ) = some (N, w)) :
    ∃ c, c < 2 ^ 16 ∧ w.signature = fillTop σ c ∧
      evalWithAnswerFn answers (expandWithN limit m pk (fillTop σ c)) = some (N, w) := by
  unfold expandS at h
  simp only [evalWithAnswerFn_bind] at h
  have hrho : (proj σ).rho = σ.rho := rfl
  rw [hrho] at h
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
  | none => rw [hd] at h; simp at h
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [hd] at h
    simp only [evalWithAnswerFn_bind] at h
    have hfts : recoverFts (proj σ) (digestIndex output) output = recoverFts σ (digestIndex output) output :=
      recoverFts_fillTop σ 0 _ _
    rw [hfts] at h
    cases hl : evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
        (.forest (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)))) with
    | none => rw [hl] at h; simp at h
    | some x =>
      obtain ⟨v, root, counters⟩ := x
      rw [hl] at h
      simp only at h
      have hroot : evalWithAnswerFn answers (topNode (digestIndex output) v (topSib (proj σ))) = root := by
        have := eval_expandLayersT_other answers (proj σ) (digestIndex output) (topSib (proj σ))
          (topSib (proj σ)) 4 (.forest (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)))
        rw [hl] at this
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
        exact this.2.1.symm
      by_cases hpk : root = pk
      · rw [if_pos hpk] at h
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, by norm_num, rfl, ?_⟩
        rw [eval_expandWithN_fill, hd]
        simp only
        rw [hl]
        simp only [Option.map_some]
        rw [← topSib_proj, hroot, if_neg (not_not.mpr hpk)]
        rfl
      · rw [if_neg hpk] at h
        simp only [evalWithAnswerFn_bind] at h
        cases hs : evalWithAnswerFn answers (searchTop (digestIndex output) v (topSib (proj σ)) pk searchFuel 1) with
        | none => rw [hs] at h; simp at h
        | some c =>
          rw [hs] at h
          simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3⟩ := eval_searchTop answers _ v _ pk searchFuel 1 c hs
          refine ⟨c, by unfold searchFuel at h2; omega, fillTop_proj σ c, ?_⟩
          rw [fillTop_proj, eval_expandWithN_fill, hd]
          simp only
          rw [hl]
          simp only [Option.map_some]
          rw [topSib_proj, setTop_setTop] at h3
          rw [h3, if_neg (not_not.mpr rfl)]

/-- Whenever the old expander accepts a signature, the H2 expander returns something on it. -/
theorem expandS_complete (answers : Answers) (limit : Nat) (m : Message) (pk : Digest) (σ : Signature)
    (x : HashOutput × Witness) (h : evalWithAnswerFn answers (expandWithN limit m pk σ) = some x) :
    ∃ y, evalWithAnswerFn answers (expandS limit m pk σ) = some y := by
  have hσ := fillTop_self σ
  set ch := (topSib σ).toNat / 2 ^ 112 with hch
  rw [← hσ, eval_expandWithN_fill] at h
  unfold expandS
  simp only [evalWithAnswerFn_bind]
  have hrho : (proj σ).rho = σ.rho := rfl
  rw [hrho]
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
  | none => rw [hd] at h; simp at h
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [hd] at h
    simp only at h
    simp only [evalWithAnswerFn_bind]
    rw [show recoverFts (proj σ) = recoverFts σ from rfl]
    cases hl : evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
        (.forest (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)))) with
    | none => rw [hl] at h; simp at h
    | some y =>
      obtain ⟨v, root, counters⟩ := y
      rw [hl] at h
      simp only [Option.map_some] at h
      have hmatch : evalWithAnswerFn answers (topNode (digestIndex output) v (setTop (topSib σ) ch)) = pk := by
        by_contra hne
        rw [if_pos hne] at h
        simp at h
      simp only
      split
      · exact ⟨_, rfl⟩
      · rename_i hne
        have hroot : evalWithAnswerFn answers (topNode (digestIndex output) v (topSib (proj σ))) = root := by
          have := eval_expandLayersT_other answers (proj σ) (digestIndex output) (topSib (proj σ))
            (topSib (proj σ)) 4 (.forest (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)))
          rw [hl] at this
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
          exact this.2.1.symm
        have hch0 : ch ≠ 0 := by
          intro h0
          rw [h0, ← topSib_proj, hroot] at hmatch
          exact hne hmatch
        have hsib : setTop (topSib (proj σ)) ch = setTop (topSib σ) ch := by rw [topSib_proj, setTop_setTop]
        obtain ⟨c', hc'⟩ := searchTop_complete answers (digestIndex output) v (topSib (proj σ)) pk searchFuel 1 ch
          (by omega) (by have := top_lt (topSib σ); unfold searchFuel; omega) (by rw [hsib]; exact hmatch)
        simp only [evalWithAnswerFn_bind, hc', evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩

/-! ### Rev3: the H2 expander's correctness, from the old expander's -/

namespace Rev3

theorem eval_expand (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) :
    evalWithAnswerFn answers (expand message pk sig) =
      (evalWithAnswerFn answers (expandS digestAttemptLimit message pk sig)).map Prod.snd := by
  unfold expand; rw [evalWithAnswerFn_map]

theorem expand_completes (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    ∃ c, c < 2 ^ 16 ∧ w.signature = fillTop sig c ∧
      evalWithAnswerFn answers (expandWith digestAttemptLimit message pk (fillTop sig c)) = some w := by
  rw [eval_expand] at he
  obtain ⟨⟨N, w'⟩, hx, rfl⟩ := map_some_inv he
  obtain ⟨c, hc, hsig, hN⟩ := eval_expandS answers _ message pk sig N w' hx
  refine ⟨c, hc, hsig, ?_⟩
  rw [expandWith_eq_N, evalWithAnswerFn_map, hN]
  rfl

theorem expand_implies_verify (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness) (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  obtain ⟨c, -, -, h⟩ := expand_completes answers message pk sig w he
  exact verifyWith_mono digestAttemptLimit digestVerifyLimit digestAttemptLimit_le_digestVerifyLimit
    answers message pk w
    (expandWith_implies_verifyWith digestAttemptLimit digestAttemptLimit_le answers message pk _ w h)

theorem expand_of_expandWith (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (w : Witness) (he : evalWithAnswerFn answers (expandWith digestAttemptLimit message pk sig) = some w) :
    ∃ w', evalWithAnswerFn answers (expand message pk sig) = some w' ∧
      evalWithAnswerFn answers (verify message pk w') = true := by
  rw [expandWith_eq_N, evalWithAnswerFn_map] at he
  obtain ⟨x, hx, -⟩ := map_some_inv he
  obtain ⟨y, hy⟩ := expandS_complete answers _ message pk sig x hx
  have he' : evalWithAnswerFn answers (expand message pk sig) = some y.2 := by
    rw [eval_expand, hy]; rfl
  exact ⟨y.2, he', expand_implies_verify answers message pk sig y.2 he'⟩

def SigningCorrect (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (sign keys.2 message) = some sig →
    ∃ w : Witness, evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true
theorem signing_success_valid (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (htop : TopSearchesSucceedBC answers) : SigningCorrect answers keys :=
  fun message sig hsign => by
    obtain ⟨w, he, -⟩ :=
      signingWith_success_valid digestAttemptLimit digestAttemptLimit_le answers keys hkeys htop message sig hsign
    exact expand_of_expandWith answers message keys.1 sig w he
theorem honest_signing_success_valid (answers : Answers) (htop : TopSearchesSucceedBC answers) :
    SigningCorrect answers (evalWithAnswerFn answers keygen) :=
  signing_success_valid answers _ (ClaudeWCT.WCT9.keygen_correct answers) htop
def RealizedSigningCorrect (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ (message : Message) (sig : Signature),
    evalWithAnswerFn answers (realize secret (sign keys.2 message)) = some sig →
    ∃ w : Witness, evalWithAnswerFn answers (realize secret (expand message keys.1 sig)) = some w ∧
      evalWithAnswerFn answers (realize secret (verify message keys.1 w)) = true
theorem realized_honest_signing_success_valid (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (htop : TopSearchesSucceedBC (answers.compose (realHandler secret))) :
    RealizedSigningCorrect answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningCorrect
  simp only [realize_eval]
  exact honest_signing_success_valid (answers.compose (realHandler secret)) htop

end Rev3
end ClaudeWCT.WCT9
end

section
namespace ClaudeWCT.WCT9.Cost
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem take_top_length : ((List.finRange (height (0 : Layer))).take 11).length = 11 := by decide

theorem bound_topFold (s : Signature) (index : Nat) (digits : List Nat)
    (hd : ValidDigits 0 digits) (hlen : digits.length = chainCount 0) (hsum : digits.sum = target 0) :
    CBound (fun _ => True) (capacity 0 - target 0 + leafHashCost 0 + 11) (topFold s index digits) := by
  unfold topFold topEnds
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun i => maxDigit 0 i.val - digits.getD i.val 0) (fun i _ => bound_chain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost 0 + 11) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).mono_k (by rw [take_top_length]; simp)
    unfold topStep
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount 0) (fun i => maxDigit 0 i - digits.getD i 0),
      remaining_steps 0 digits hd hlen hsum]
    omega

theorem bound_topNode (index : Nat) (v o : Digest) : CBound (fun _ => True) 1 (topNode index v o) := by
  unfold topNode; exact bound_nodeHash _ _ _ _ _ _

theorem recoverLayerCost_top : capacity 0 - target 0 + leafHashCost 0 + 11 + 1 = recoverLayerCost 0 := by
  decide

theorem bound_expandLayersT (sig : Signature) (index : Nat) (o : Digest) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + recoveryLayersCostBC n) (expandLayersT sig index o n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold expandLayersT
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
            refine (bound_topFold sig index digits hd.2.2 hd.1 hd.2.1).bind' (l := 1)
              (fun v _ => (bound_topNode index v o).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega))
              (by decide)
          · simp only [hn, ite_false]
            refine (bound_recoverLayerPair sig index (Fin.ofNat 4 n) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := n * counterLimit + recoveryLayersCostBC n) (fun value _ => ?_)
              (by simp only [recoveryLayersCostBC, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun result _ => ?_) (by omega)
            cases result <;> exact .pure _ 0 trivial

theorem bound_searchTop (index : Nat) (v sib pk : Digest) :
    ∀ fuel c, CBound (fun _ => True) fuel (searchTop index v sib pk fuel c) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact .pure _ _ trivial
  | succ fuel ih =>
      intro c
      unfold searchTop
      refine (bound_topNode index v (setTop sib c)).bind' (l := fuel) (fun r _ => ?_) (by omega)
      split
      · exact .pure _ _ trivial
      · exact ih (c + 1)

theorem bound_expandS (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (limit + 4 * counterLimit + 621 + searchFuel) (expandS limit message pk sig) := by
  unfold expandS
  refine (bound_digestSearch (proj sig).rho message limit 0).bind' (l := 4 * counterLimit + 621 + searchFuel)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_recoverFts (proj sig) _ output).bind' (l := 4 * counterLimit + 481 + searchFuel)
        (fun root _ => ?_) (by omega)
      refine (bound_expandLayersT (proj sig) _ (topSib (proj sig)) 4 (.forest root)).bind' (l := searchFuel)
        (fun layers _ => ?_) (by have := recoveryLayersCostBC_four_le; omega)
      cases layers with
      | none => exact .pure _ _ trivial
      | some triple =>
          obtain ⟨v, root, counters⟩ := triple
          dsimp only
          split
          · exact .pure _ _ trivial
          · refine (bound_searchTop _ v _ pk searchFuel 1).bind' (l := 0) (fun c _ => ?_) (by omega)
            cases c <;> exact .pure _ 0 trivial

theorem bound_expand (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (digestAttemptLimit + 4 * counterLimit + 621 + searchFuel) (Rev3.expand message pk sig) := by
  unfold Rev3.expand
  exact Bound.map _ (bound_expandS digestAttemptLimit message pk sig) (fun _ _ => trivial)

theorem expand_compression_ceiling (secret : BitVec 256) (message : Message) (pk : Digest) (sig : Signature) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.expand message pk sig))),
      result.2 ≤ 18940524 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_expand message pk sig).count_support result
    (realize_support_subset secret _ hr) |>.2
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit, searchFuel])

end ClaudeWCT.WCT9.Cost
end
