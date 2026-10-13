import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layer
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.ExtractSrc

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
    (h : (∀ value, input ≠ chainRow a step value) ∨ depth answers a ≤ step) : OtherChainRow answers input :=
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
      hashPathW (chainHighFrom lay i start) (chainPathInput lay tree leaf i start pad0 pad1 headerPad) count initial := by
  unfold chainPW hashPathW
  rw [List.range'_eq_map_range, List.foldlM_map]
  rfl
theorem honestChainValueW_ref (answers : Answers) (lay : Layer) (tree leaf i start : Nat) (seed : Digest)
    (step : Nat) :
    WCT9.halfOf (chainHighFrom lay i start step) (answers (.inl (.inr (pad64 (chainInput lay tree leaf i
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
        (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValueW answers lay tree leaf i seed (start + s)) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInputW answers (chainHighFrom lay i start)
        (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHitH (WCT9.chainHigh lay i (start + step)) answers
        (pad64 (chainInput lay tree leaf i (start + step)
          (honestChainValueW answers lay tree leaf i seed (start + step))))
        (pad64 (pathInputW answers (chainHighFrom lay i start)
          (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (step + 1 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      (∀ later, step < later → later < count →
        pathInputW answers (chainHighFrom lay i start) (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
            value later =
          chainInput lay tree leaf i (start + later)
            (honestChainValueW answers lay tree leaf i seed (start + later))) ∧
      ∀ s, step < s → s ≤ count → pathValueW answers (chainHighFrom lay i start)
          (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValueW answers lay tree leaf i seed (start + s) := by
  rw [chainPW_eq_hashPathW] at reaches ⊢
  have h := hashPathW_join answers (chainHighFrom lay i start) (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
    (fun step => chainInput lay tree leaf i (start + step)
      (honestChainValueW answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValueW answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => honestChainValueW_ref answers lay tree leaf i start seed step)
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [chainPathInput, chainInput_eq_zero _ _ _ _ _ _ ht hl hi hs, pad64_chainInputP] at heq
      have hhp := chainInputP_headerPad_eq heq
      obtain ⟨hp0, _, hp1, hv⟩ := chainInputP_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, hlater, hvals⟩
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => (hpads 0 hcount).1, hvals⟩
  · refine Or.inr ⟨step, hstep, hq, hhit, fun h => (hlater (step + 1) (by omega) h).1, ?_, hvals⟩
    intro later h1 h2
    have he := (hlater later h1 h2).2
    simp only [pathInputW, chainPathInput, chainInput_padded, pad64_chainInputP] at he ⊢
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
        (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHitH (WCT9.chainHigh lay i (start + step)) answers
        (pad64 (chainInput lay tree leaf i (start + step)
          (honestChainValueW answers lay tree leaf i seed (start + step))))
        (pad64 (pathInputW answers (chainHighFrom lay i start)
          (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ W ≤ start + step)) ∨
    (pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0 ∧
      pathValueW answers (chainHighFrom lay i start) (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value
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
    (.inl (.inr (chainRow a (start + s)
        (pathValueW answers (chainHighFrom a.key.lay a.chain start)
          (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))) : Spec.Domain) ∈
      queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value) ∧
    rowHalf a (start + s) (answers (.inl (.inr (chainRow a (start + s)
        (pathValueW answers (chainHighFrom a.key.lay a.chain start)
          (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))))) =
      pathValueW answers (chainHighFrom a.key.lay a.chain start)
        (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (s + 1) := by
  have hrow : pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
      (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) =
      chainRow a (start + s)
        (pathValueW answers (chainHighFrom a.key.lay a.chain start)
          (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) := by
    simp only [pathInputW, chainPathInput, pad64_chainInputP, chainRow]
    exact (chainInput_eq_zero a.key.lay a.key.tree a.key.leaf a.chain (start + s) _ ht hl hi (by omega)).symm
  constructor
  · rw [chainPW_eq_hashPathW, ← hrow]
    exact pathInputW_queried answers _ (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value
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
      (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (W - start) = out) :
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
    (hq : (.inl (.inr (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v)) : Spec.Domain) ∈ qs)
    (hsrc : SourceChain a) (htb : a.key.tree < 2 ^ Extract.treeBits a.key.lay)
    (hstep : step + 1 < 2 ^ width a.key.lay a.chain)
    (hhit : HashHitH (WCT9.chainHigh a.key.lay a.chain step) answers
      (Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain step))
      (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v))
    (hclass : ¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ step) :
    StructuralHitSrc answers (entriesOf answers qs) := by
  have hb := chain_bounded hsrc hstep
  have hlen : (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v).length = 64 := by
    simp [chainInputP, bytesLE_length]
  have hpos : Extract.posOf (chainInputP a.key.lay a.key.tree a.key.leaf a.chain step pad0 pad1 headerPad v) =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) := by
    apply Extract.posOf_key_eq hb (hlen.trans rfl)
    rw [Extract.hdrKey_of_len64 hlen, ← pad64_chainInputP, Extract.hdrBlock_chainInputP,
      Extract.canonicalHeader_chainHeaderP]
    exact Extract.Pos.canonicalHeader_eq (p := .chain a.key.lay a.key.tree a.key.leaf a.chain step) hb
  refine ⟨_, _, _, mem_entriesOf hq, hpos, hb, ⟨htb, hsrc.1.2, hsrc.2, hstep⟩, ?_,
    (hashHitAt_iff _ _ _ _).mpr hhit⟩
  refine otherChainRow_intro hpos ?_
  rcases hclass with hpad | hdepth
  · refine Or.inl fun value he => hpad ?_
    rw [chainRow, chainInput_eq_zero _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega)] at he
    have hh := chainInputP_headerPad_eq he
    obtain ⟨h0, _, h1, _⟩ := chainInputP_fields he
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
        (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainPW a.key.lay a.key.tree a.key.leaf a.chain start count pad0 pad1 headerPad value) →
      HashHitH (WCT9.chainHigh a.key.lay a.chain (start + step)) answers
        (pad64 (chainInput a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))))
        (pad64 (pathInputW answers (chainHighFrom a.key.lay a.chain start)
          (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start pad0 pad1 headerPad) value step)) →
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ depth answers a ≤ start + step) → False := by
    intro step hstep hq hhit hclass
    apply hS
    simp only [pathInputW, chainPathInput, pad64_chainInputP] at hq hhit
    refine structuralHit_chain a (start + step) pad0 pad1 headerPad _ (hsub _ hq) hsrc htb (by omega) ?_ hclass
    have he : Extract.honestInput answers (.chain a.key.lay a.key.tree a.key.leaf a.chain (start + step)) =
        pad64 (chainInput a.key.lay a.key.tree a.key.leaf a.chain (start + step)
          (honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
            (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (start + step))) := by
      simp only [Extract.honestInput]
      rw [honestChainValueW_eq (Or.inr (Or.inr (by omega)))]
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
