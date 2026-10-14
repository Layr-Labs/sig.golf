import SigGolfCandidate.T3.Secc.LargeCouplingObserved
import SigGolfCandidate.T3.Secc.LargeCouplingSign
import SigGolfCandidate.T3.Secc.LargeCouplingTrace
import SigGolfCandidate.T3.Secc.WotsClasses

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingQuery : DecidableEq T3.Cache := Classical.decEq _
noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  joinLabels (fun N => vals (.inl N)) a.high
def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr ∧ PrefixRow a L ctr
structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : Agrees T (routerLabels vals a)
  secrets : secretsOf T = fun s => vals (.inr s)
  residual : ∀ (X : HashInput) (hX : X ∈ U), (∀ N : CanonGraph.Node, X ≠ cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X)) = τ ⟨X, hX⟩
  prefixRow : ∀ (L : EncLeaf) (ctr : BitVec 32), PrefixRow a L ctr →
    T (.inl (.inr (Wots.encodingRow L.toWots (vals (msgCoord L)) ctr))) = prefixValue a L ctr
  search : ∀ L : EncLeaf, Wots.referenceSearch T L.toWots =
    (a.sel L).bind fun r => (decode L.1.lay r.2).map fun d => (BitVec.ofNat 32 r.1.val, d)
  priv : ∀ c : Coordinate, (∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) → (∀ m : Message, c ≠ .inr (.inl m)) →
    T (.inr c) = a.priv c
  outside : ∀ X, X ∉ U → T (.inl (.inr X)) = (0 : HashOutput)
  nonce : ∀ m : Message, (T (.inr (.inr (.inl m)))).extractLsb' 0 128 = nv m
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.honestValue (h : Coherent U T vals nv τ a) : LargeResidual.honestValue T = vals := by
  rw [honestValue_eq h.agrees, h.secrets]
  funext c
  cases c with
  | inl N => exact joinLabels_low _ _ N
  | inr s => rfl
theorem Coherent.honestInput (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    Extract.honestInput T N.toPos = cellValues N vals := by
  rw [honestInput_eq h.agrees N, cell_eq_cellValues]
  congr 1
  rw [h.secrets]
  funext c
  cases c with
  | inl M => exact joinLabels_low _ _ M
  | inr s => rfl
theorem Coherent.cell (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    cell (secretsOf T) N (routerLabels vals a) = cellValues N vals := by
  rw [← honestInput_eq h.agrees N, h.honestInput N]
theorem Coherent.honest_answer (h : Coherent U T vals nv τ a) (N : CanonGraph.Node) :
    T (.inl (.inr (cellValues N vals))) = routerLabels vals a N := by
  rw [← h.honestInput N]
  exact CanonGraph.honest_answer h.agrees N
theorem Coherent.leafMsg (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.leafMsg T L.toWots = vals (msgCoord L) := by
  rw [leafMsg_eq h.agrees L]
  unfold msgLabel msgCoord
  by_cases hl : L.1.lay.val < 3
  · rw [dif_pos hl, dif_pos hl, treeLabel_root]
    exact joinLabels_low _ _ _
  · rw [dif_neg hl, dif_neg hl]
    exact joinLabels_low _ _ _
end Coherent
theorem low_eq (y : HashOutput) : low y = y.extractLsb' 0 128 := rfl
theorem dummyDigest_decode' (lay : Layer) : decode lay (dummyDigest lay) = some (Wots.dummyDigits lay) :=
  Classical.choose_spec (Wots.dummyDigits_valid lay)
section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.referenceDigits T L.toWots = ((a.sel L).bind fun r => decode L.1.lay r.2).getD (Wots.dummyDigits L.1.lay) := by
  unfold Wots.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases decode L.1.lay r.2 <;> rfl
theorem Coherent.referenceInput (h : Coherent U T vals nv τ a) (L : EncLeaf) (X : HashInput)
    (hX : Wots.referenceInput T L.toWots = some X) :
    ∃ r, a.sel L = some r ∧ X = Wots.encodingRow L.toWots (vals (msgCoord L)) (BitVec.ofNat 32 r.1.val) := by
  unfold Wots.referenceInput at hX
  rw [h.search, h.leafMsg] at hX
  cases hs : a.sel L with
  | none => rw [hs] at hX; cases hX
  | some r =>
      rw [hs] at hX
      simp only [Option.bind_some, Option.map_map] at hX
      cases hd : decode L.1.lay r.2 with
      | none => rw [hd] at hX; cases hX
      | some w =>
          rw [hd] at hX
          exact ⟨r, rfl, (Option.some.inj hX).symm⟩
end Reference
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
  hidden : ∀ c, ¬st.known c → 2 ^ 128 - ws.counters.probes ≤ (ws.candidates (.inl c)).card
  rowsEq : ∀ row v, ws.rows row = some v → v = τ row
  rowsSeen : ∀ row v, ws.rows row = some v → row.val ∈ st.seen ∨ IsDigestRow row.val
  seenCells : ∀ X ∈ st.seen, X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1
  seenEnc : ∀ X ∈ st.seen, X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32),
    X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr → st.known (msgCoord L)
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
theorem Rel.known (h : Rel U T vals nv τ a q mon st ws) : mon.known = st.known := by
  unfold Monitor.known RouterState.known
  rw [h.disclosed]
theorem Rel.query (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (y : HashOutput) :
    mon.query U T q X y =
      if X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X y then
        ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests, true⟩
      else ⟨mon.disclosed, X :: mon.seen, mon.calls + 1,
        mon.digests + (if X ∈ U ∧ IsDigestRow X then 1 else 0), false⟩ := by
  have hc : mon.calls + 1 ≤ q := by rw [h.calls]; omega
  unfold Monitor.query
  rw [if_neg (by rw [h.contact]; decide), h.known, h.seen]
  by_cases ht : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X y
  · rw [if_pos ⟨ht.1, ht.2.1, hc, ht.2.2⟩, if_pos ht]
  · rw [if_neg (fun h' => ht ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg ht]
    by_cases hd : X ∈ U ∧ IsDigestRow X
    · rw [if_pos ⟨hd.1, hd.2, hc⟩, if_pos hd]
    · rw [if_neg (fun h' => hd ⟨h'.1, h'.2.1⟩), if_neg hd]
theorem Rel.next (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (ws' : LargeResidual.State WCoord (Cell U)) (δ : Nat)
    (hcalls : ws'.counters.calls = st.calls + 1) (hmass : ws'.counters.mass = ws.counters.mass + δ)
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬st.known c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L))
    (st' : RouterState) (hd : st'.disclosed = st.disclosed) (hs : st'.seen = X :: st.seen)
    (hc : st'.calls = st.calls + 1) :
    Rel U T vals nv τ a q ⟨mon.disclosed, X :: mon.seen, mon.calls + 1, mon.digests + δ, false⟩ st' ws' := by
  have hk : st'.known = st.known := by unfold RouterState.known; rw [hd]
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
  · intro Y hY hYU N hN cs hcs
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hcell hYU N hN cs hcs
    · exact h.seenCells Y hY hYU N hN cs hcs
  · intro Y hY hYU L ctr hL
    rw [hk]
    rw [hs] at hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact henc hYU L ctr hL
    · exact h.seenEnc Y hY hYU L ctr hL
end Relation
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem keep_guess_label {C : Type} (vals : C → Digest) (c p : C) (m : Digest) (y : HashOutput) :
    (⟨some (c, m), .label p⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_label {C : Type} (vals : C → Digest) (p : C) (y : HashOutput) :
    (⟨none, .label p⟩ : Probe C).keep vals y ↔ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_target {C : Type} (vals : C → Digest) (t : Digest) (y : HashOutput) :
    (⟨none, .target t⟩ : Probe C).keep vals y ↔ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_guess_target {C : Type} (vals : C → Digest) (c : C) (m t : Digest) (y : HashOutput) :
    (⟨some (c, m), .target t⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem Rel.fresh (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) (hd : ¬IsDigestRow X)
    (hs : X ∉ st.seen) : ws.rows ⟨X, hX⟩ = none := by
  cases hr : ws.rows ⟨X, hX⟩ with
  | none => rfl
  | some v =>
      rcases hrel.rowsSeen _ v hr with h | h
      · exact absurd h hs
      · exact absurd h hd
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
end Cases
end SigGolfCandidate.T3.Security.LargeCoupling
