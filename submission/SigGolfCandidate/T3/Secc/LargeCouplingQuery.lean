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
theorem childSlots_ne (N : CanonGraph.Node) : ∀ cs ∈ childSlots N, cs.1 ≠ .inl N := by
  intro cs hcs
  cases N with
  | chain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      unfold chainChild
      split_ifs with h0
      · exact Sum.inl_ne_inr.symm
      · intro heq
        have h1 := congrArg (fun c : Coord => match c with | .inl (.chain x) => x.2.val | _ => 0) heq
        simp only [ChainGraph.predecessor] at h1
        omega
  | leaf L =>
      simp only [childSlots, List.mem_map] at hcs
      obtain ⟨i, -, rfl⟩ := hcs
      simp
  | node n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      · unfold treeChild at hc
        split_ifs at hc with hl
        · obtain ⟨⟩ := hc
          simp
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨m, hm, rfl⟩ := hc
          intro heq
          have hlev := treeNodeAt_level hm
          have hmn : m = n := by
            simp only [Sum.inl.injEq, CanonGraph.Node.node.injEq] at heq
            exact heq
          subst hmn
          omega
  | ftsLeaf f =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      exact Sum.inr_ne_inl
  | ftsNode n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      · unfold ftsChild at hc
        split_ifs at hc with hl
        · obtain ⟨⟩ := hc
          simp
        · simp only [Option.map_eq_some_iff] at hc
          obtain ⟨m, hm, rfl⟩ := hc
          intro heq
          have hlev := ftsNodeAt_level hm
          have hmn : m = n := by
            simp only [Sum.inl.injEq, CanonGraph.Node.ftsNode.injEq] at heq
            exact heq
          subst hmn
          omega
  | forest index =>
      simp only [childSlots, List.mem_map] at hcs
      obtain ⟨i, -, rfl⟩ := hcs
      simp
theorem firstUnknown_some {K : Coord → Prop} {N : CanonGraph.Node} {cs : Coord × Nat}
    (h : firstUnknown K N = some cs) : cs ∈ childSlots N ∧ ¬K cs.1 := by
  unfold firstUnknown at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm, hp⟩
theorem firstUnknown_none {K : Coord → Prop} {N : CanonGraph.Node} (h : firstUnknown K N = none) :
    ∀ cs ∈ childSlots N, K cs.1 := by
  unfold firstUnknown at h
  intro cs hcs
  have := List.find?_eq_none.mp h cs hcs
  simpa using this
theorem contactTest_other {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput}
    (hp : ¬Parsed X) (he : ¬EncRow X) : ¬ContactTest A K X y := by
  rintro (⟨N, hN, -⟩ | ⟨L, m, c, hX, -⟩)
  · exact hp ⟨N, hN⟩
  · exact he ⟨L, m, c, hX⟩
theorem low_eq (y : HashOutput) : low y = y.extractLsb' 0 128 := rfl
theorem sel_valid (a : AuxData) (L : EncLeaf) (r : Fin (2 ^ 22) × Digest) (hr : a.sel L = some r) :
    ∃ w, decode L.1.lay r.2 = some w := by
  have h := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hr
  obtain ⟨-, hs⟩ := (decodeAt_eq_some L _ r.2).mp h.1
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨w, Nonbinary.searchDecode_some hw⟩
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
theorem Coherent.decode_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (d : Digest) :
    decode L.1.lay d = some (Wots.referenceDigits T L.toWots) ↔ d = refDigest a L := by
  rw [h.referenceDigits L]
  unfold refDigest
  cases hs : a.sel L with
  | none =>
      simp only [Option.bind_none, Option.getD_none]
      constructor
      · intro hd
        exact decode_some_injective hd (dummyDigest_decode' L.1.lay)
      · rintro rfl
        exact dummyDigest_decode' L.1.lay
  | some r =>
      obtain ⟨w, hw⟩ := sel_valid a L r hs
      simp only [Option.bind_some, hw, Option.getD_some]
      constructor
      · intro hd
        exact decode_some_injective hd hw
      · rintro rfl
        exact hw
theorem Coherent.prefix_ref (h : Coherent U T vals nv τ a) (L : EncLeaf) (ctr : BitVec 32) (hp : PrefixRow a L ctr)
    (hd : decode L.1.lay ((prefixValue a L ctr).extractLsb' 0 128) = some (Wots.referenceDigits T L.toWots)) :
    Wots.referenceInput T L.toWots = some (Wots.encodingRow L.toWots (vals (msgCoord L)) ctr) := by
  obtain ⟨hlt, hle⟩ := hp
  have hpv : prefixValue a L ctr = a.rows L ⟨ctr.toNat, hlt⟩ := by unfold prefixValue; rw [dif_pos hlt]
  rw [hpv] at hd
  have hd' : searchDecode L.1.lay ((a.rows L ⟨ctr.toNat, hlt⟩).extractLsb' 0 128) =
      some (Wots.referenceDigits T L.toWots) := WotsExtract.searchDecode_of_reference T L.toWots hd
  cases hs : a.sel L with
  | none =>
      have hn := (SphincsSecurity.Concrete.FirstSuccessTable.select_none_iff _ _).mp hs ⟨ctr.toNat, hlt⟩
      rw [decodeAt_eq_none] at hn
      rw [hn] at hd'
      cases hd'
  | some r =>
      have hsel := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hs
      have hle' := hle r hs
      rcases Nat.lt_or_ge ctr.toNat r.1.val with hlt' | hge
      · have hn := hsel.2 ⟨ctr.toNat, hlt⟩ hlt'
        rw [decodeAt_eq_none] at hn
        rw [hn] at hd'
        cases hd'
      · have heq : ctr.toNat = r.1.val := by omega
        unfold Wots.referenceInput
        rw [h.search, h.leafMsg, hs]
        obtain ⟨w, hw⟩ := sel_valid a L r hs
        simp only [Option.bind_some, hw, Option.map_some]
        congr 2
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, ← heq]
        exact Nat.mod_eq_of_lt (by omega)
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
theorem Rel.two_le (h : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (hq : q ≤ 2 ^ 127) (c : Coord)
    (hc : ¬st.known c) : 2 ≤ (ws.candidates (.inl c)).card := by
  have h1 := h.hidden c hc
  have h2 := h.probes
  have h3 := h.wcalls
  omega
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
theorem _root_.SigGolfCandidate.T3.Security.LargeResidual.RouterState.next_of_not (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput)
    (h : ¬(X ∈ U ∧ IsDigestRow X)) : st.next U X y = st.after X := by
  unfold RouterState.next
  rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
def QueryOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U))
    (X : HashInput) (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))) : Prop :=
  ∃ ws' : LargeResidual.State WCoord (Cell U),
    ((mon.query U T q X (T (.inl (.inr X)))).contact = true ∧ out = pure (none, ws') ∧
        ws'.counters.mass = mon.digests ∧ ws'.counters.calls ≤ q) ∨
      ((mon.query U T q X (T (.inl (.inr X)))).contact = false ∧
        out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws') ∧
        Rel U T vals nv τ a q (mon.query U T q X (T (.inl (.inr X)))) (st.next U X (T (.inl (.inr X)))) ws')
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {mon : Monitor} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem observed_map {β γ : Type} (f : β → γ) (c : OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    observedRun aux q (Sum.elim vals nv) τ (f <$> c) s = (fun r => (r.1.map f, r.2)) <$> observedRun aux q (Sum.elim vals nv) τ c s :=
  runWith_map _ f c s
theorem observed_testReq (st' : RouterState) (X : HashInput) (hX : X ∈ U) (test : Probe WCoord)
    (hfresh : X ∉ st.seen → ws.rows ⟨X, hX⟩ = none) :
    observedRun aux q (Sum.elim vals nv) τ ((fun y => (y, st')) <$> testReq U (decide (X ∉ st.seen)) ⟨X, hX⟩ test) ws =
      if X ∉ st.seen then
        (if (test.effective ws.candidates).keep (Sum.elim vals nv) (τ ⟨X, hX⟩) then
          pure (some (τ ⟨X, hX⟩, st'), probeState ws ⟨X, hX⟩ (test.effective ws.candidates) (τ ⟨X, hX⟩))
        else pure (none, stoppedState ws))
      else pure (some (τ ⟨X, hX⟩, st'), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call) := by
  rw [observed_map]
  by_cases hs : X ∈ st.seen
  · have hd : decide (X ∉ st.seen) = false := by simp [hs]
    rw [hd, if_neg (not_not.mpr hs)]
    simp only [testReq, Bool.false_eq_true, if_false]
    rw [← bind_pure (readReq U ⟨X, hX⟩ .call), observed_readReq, observed_pure, map_pure]
    rfl
  · have hd : decide (X ∉ st.seen) = true := by simp [hs]
    rw [hd, if_pos hs]
    simp only [testReq, if_true]
    rw [← bind_pure (probeReq U ⟨X, hX⟩ test), observed_probeReq_fresh U aux q (Sum.elim vals nv) τ _ _ _ _ (hfresh hs)]
    split_ifs
    · rw [observed_pure, map_pure]; rfl
    · rw [map_pure]; rfl
theorem effective_self {C : Type} [DecidableEq C] (cand : C → Finset Digest) (test : Probe C)
    (h : ∀ g ∈ test.guess, 2 ≤ (cand g.1).card ∧ ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent) :
    test.effective cand = test := by
  obtain ⟨guess, hit⟩ := test
  unfold Probe.effective
  cases guess with
  | none => rfl
  | some g =>
      have hg' := h g rfl
      simp only [Option.filter_some, Probe.Admissible, decide_eq_true_eq]
      rw [if_pos hg']
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
theorem outcome_stop (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X))))
    (hout : out = pure (none, stoppedState ws)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨stoppedState ws, Or.inl ⟨?_, hout, ?_, ?_⟩⟩
  · rw [hrel.query hlt, if_pos hc]
  · exact hrel.digests.symm
  · show ws.counters.calls + 1 ≤ q
    rw [hrel.wcalls]
    omega
theorem outcome_continue (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (out : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U)))
    (hc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (ws' : LargeResidual.State WCoord (Cell U))
    (hout : out = pure (some (T (.inl (.inr X)), st.next U X (T (.inl (.inr X)))), ws'))
    (hcalls : ws'.counters.calls = st.calls + 1)
    (hmass : ws'.counters.mass = ws.counters.mass + (if X ∈ U ∧ IsDigestRow X then 1 else 0))
    (hprobes : ws'.counters.probes ≤ ws'.counters.calls)
    (hmem : ∀ c, Sum.elim vals nv c ∈ ws'.candidates c)
    (hhidden : ∀ c, ¬st.known c → 2 ^ 128 - ws'.counters.probes ≤ (ws'.candidates (.inl c)).card)
    (hrowsEq : ∀ row v, ws'.rows row = some v → v = τ row)
    (hrowsSeen : ∀ row v, ws'.rows row = some v → row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val)
    (hcell : X ∈ U → ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : X ∈ U → ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X out := by
  refine ⟨ws', Or.inr ⟨?_, hout, ?_⟩⟩
  · rw [hrel.query hlt, if_neg hc]
  · rw [hrel.query hlt, if_neg hc]
    refine hrel.next hlt X ws' _ hcalls hmass hprobes hmem hhidden hrowsEq hrowsSeen hcell henc _ ?_ ?_ ?_ <;>
    · unfold RouterState.next
      split_ifs <;> rfl
theorem Rel.fresh (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) (hd : ¬IsDigestRow X)
    (hs : X ∉ st.seen) : ws.rows ⟨X, hX⟩ = none := by
  cases hr : ws.rows ⟨X, hX⟩ with
  | none => rfl
  | some v =>
      rcases hrel.rowsSeen _ v hr with h | h
      · exact absurd h hs
      · exact absurd h hd
theorem not_prefix_enc {X : HashInput} (he : ¬EncRow X) : ¬HonestPrefix vals a X := by
  rintro ⟨L, ctr, rfl, -⟩
  exact he ⟨L, _, ctr, rfl⟩
theorem case_outside (hcoh : Coherent U T vals nv τ a) (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q)
    (X : HashInput) (hX : X ∉ U) :
    QueryOutcome U T vals nv τ a q mon st ws X (observedRun aux q (Sum.elim vals nv) τ (tickReq U .call >>= fun _ =>
      pure ((0 : HashOutput), st.after X)) ws) := by
  rw [observed_tickReq, observed_pure]
  apply outcome_continue hrel hlt X _ (fun h => hX h.2.1) (tickState q ws .call)
  · rw [hcoh.outside X hX, RouterState.next_of_not U st X _ (fun h' => hX h'.1)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hX h.1), Nat.add_zero]
  · show ws.counters.probes ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact hrel.mem
  · exact hrel.hidden
  · exact hrel.rowsEq
  · intro row v hv; exact Or.inr (hrel.rowsSeen row v hv)
  · intro h; exact absurd h hX
  · intro h; exact absurd h hX
theorem rows_update_eq (hrel : Rel U T vals nv τ a q mon st ws) (row0 : Cell U) :
    ∀ row v, Function.update ws.rows row0 (some (τ row0)) row = some v → v = τ row := by
  intro row v hv
  by_cases hr : row = row0
  · subst hr
    rw [Function.update_self] at hv
    exact (Option.some.inj hv).symm
  · rw [Function.update_of_ne hr] at hv
    exact hrel.rowsEq row v hv
theorem rows_update_seen (hrel : Rel U T vals nv τ a q mon st ws) (X : HashInput) (hX : X ∈ U) :
    ∀ row v, Function.update ws.rows ⟨X, hX⟩ (some (τ ⟨X, hX⟩)) row = some v →
      row.val = X ∨ row.val ∈ st.seen ∨ IsDigestRow row.val := by
  intro row v hv
  by_cases hr : row = ⟨X, hX⟩
  · exact Or.inl (by rw [hr])
  · rw [Function.update_of_ne hr] at hv
    exact Or.inr (hrel.rowsSeen row v hv)
theorem continue_read (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (ch : Charge) (hch : (ch = .call ∧ ¬IsDigestRow X) ∨ (ch = .mass ∧ IsDigestRow X))
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.next U X (τ ⟨X, hX⟩)),
        readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)) := by
  apply outcome_continue hrel hlt X _ hnc (readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) ch)
  · rw [hTX]
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    · show ws.counters.calls + 1 = st.calls + 1
      rw [hrel.wcalls]
  · rcases hch with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · show ws.counters.mass = ws.counters.mass + _
      rw [if_neg (fun h => hd h.2), Nat.add_zero]
    · show ws.counters.mass + (if ws.counters.calls + 1 ≤ q then 1 else 0) = ws.counters.mass + _
      rw [if_pos (show ws.counters.calls + 1 ≤ q by rw [hrel.wcalls]; omega),
        if_pos (show X ∈ U ∧ IsDigestRow X from ⟨hX, hd⟩)]
  · have := hrel.probes
    rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
    · show ws.counters.probes ≤ ws.counters.calls + 1
      omega
  · exact hrel.mem
  · rcases hch with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hrel.hidden
    · exact hrel.hidden
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem continue_read_call (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput)
    (hX : X ∈ U) (hnd : ¬IsDigestRow X) (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X), readState q ws ⟨X, hX⟩ (τ ⟨X, hX⟩) .call)) := by
  have h := continue_read hrel hlt X hX .call (Or.inl ⟨rfl, hnd⟩) hTX hnc hcell henc
  rwa [RouterState.next_of_not U st X _ (fun h' => hnd h'.2)] at h
theorem continue_probe (hrel : Rel U T vals nv τ a q mon st ws) (hlt : st.calls < q) (X : HashInput) (hX : X ∈ U)
    (test : Probe WCoord) (hk : test.keep (Sum.elim vals nv) (τ ⟨X, hX⟩))
    (hadm : ∀ g ∈ test.guess, ∀ parent, test.hit = Hit.label parent → g.1 ≠ parent)
    (hTX : T (.inl (.inr X)) = τ ⟨X, hX⟩) (hnd : ¬IsDigestRow X)
    (hnc : ¬(X ∉ st.seen ∧ X ∈ U ∧ ContactTest T st.known X (T (.inl (.inr X)))))
    (hcell : ∀ N : CanonGraph.Node, X = cellValues N vals → ∀ cs ∈ childSlots N, st.known cs.1)
    (henc : ∀ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr →
      st.known (msgCoord L)) :
    QueryOutcome U T vals nv τ a q mon st ws X
      (pure (some (τ ⟨X, hX⟩, st.after X),
        probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))) := by
  apply outcome_continue hrel hlt X _ hnc (probeState ws ⟨X, hX⟩ test (τ ⟨X, hX⟩))
  · rw [hTX, RouterState.next_of_not U st X _ (fun h' => hnd h'.2)]
  · show ws.counters.calls + 1 = st.calls + 1
    rw [hrel.wcalls]
  · show ws.counters.mass = ws.counters.mass + _
    rw [if_neg (fun h => hnd h.2), Nat.add_zero]
  · show ws.counters.probes + 1 ≤ ws.counters.calls + 1
    have := hrel.probes; omega
  · exact (mem_restrict test ws.candidates (τ ⟨X, hX⟩) (Sum.elim vals nv)).mpr ⟨hrel.mem, hk.1, by
      rcases test with ⟨g, hit⟩
      cases hit with
      | label p => exact hk.2
      | target t => trivial⟩
  · intro c hc
    have h1 := hrel.hidden c hc
    have h2 := card_restrict_ge test ws.candidates (τ ⟨X, hX⟩) hadm (.inl c)
    show 2 ^ 128 - (ws.counters.probes + 1) ≤ (test.restrict ws.candidates (τ ⟨X, hX⟩) (.inl c)).card
    omega
  · exact rows_update_eq hrel _
  · exact rows_update_seen hrel X hX
  · exact fun _ => hcell
  · exact fun _ => henc
theorem queryOutcome_congr {X : HashInput}
    {out out' : SPMF (Option (HashOutput × RouterState) × LargeResidual.State WCoord (Cell U))} (h : out = out')
    (h' : QueryOutcome U T vals nv τ a q mon st ws X out') : QueryOutcome U T vals nv τ a q mon st ws X out := h ▸ h'
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
theorem discloseStates_counters (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).counters = s.counters := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_rows (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) :
    (discloseStates U q (Sum.elim vals nv) s cs).rows = s.rows := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih => exact (ih _).trans rfl
theorem discloseStates_candidates (cs : List Coord) (s : LargeResidual.State WCoord (Cell U)) (c : WCoord) :
    (discloseStates U q (Sum.elim vals nv) s cs).candidates c =
      if c ∈ cs.map Sum.inl then {Sum.elim vals nv c} else s.candidates c := by
  induction cs generalizing s with
  | nil => simp [discloseStates]
  | cons d rest ih =>
      change (discloseStates U q (Sum.elim vals nv)
        (disclosedState q s (.inl d) (Sum.elim vals nv (.inl d)) .none) rest).candidates c = _
      rw [ih]
      change (if c ∈ rest.map Sum.inl then {Sum.elim vals nv c}
        else Function.update s.candidates (.inl d) {Sum.elim vals nv (.inl d)} c) = _
      by_cases hr : c ∈ rest.map Sum.inl
      · rw [if_pos hr, if_pos (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hr)]
      · rw [if_neg hr]
        by_cases hd : c = .inl d
        · subst hd
          rw [Function.update_self, if_pos (by rw [List.map_cons]; exact List.mem_cons_self)]
        · rw [Function.update_of_ne hd, if_neg (by simp only [List.map_cons, List.mem_cons]; tauto)]
theorem Rel.discloseStates (hrel : Rel U T vals nv τ a q mon st ws) (cs : List Coord) (hk : ∀ c ∈ cs, st.known c) :
    Rel U T vals nv τ a q mon st (discloseStates U q (Sum.elim vals nv) ws cs) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) cs ws
  refine ⟨hrel.disclosed, hrel.seen, hrel.calls, by rw [hc]; exact hrel.wcalls, by rw [hc]; exact hrel.digests,
    hrel.contact, by rw [hc]; exact hrel.probes, hrel.budget, ?_, ?_, by rw [hr]; exact hrel.rowsEq,
    by rw [hr]; exact hrel.rowsSeen, hrel.seenCells, hrel.seenEnc⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact hrel.mem c
  · intro c hck
    rw [discloseStates_candidates, hc]
    rw [if_neg (fun hm => hck (by
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      have hdc' := Sum.inl.inj hdc
      subst hdc'
      exact hk _ hd))]
    exact hrel.hidden c hck
theorem encRow_not_digest (L : EncLeaf) (m : Digest) (ctr : BitVec 32) :
    ¬IsDigestRow (Wots.encodingRow L.toWots m ctr) := by
  rintro ⟨rho, m', c, h⟩
  exact Wots.SmallA.encodingRow_ne_digest _ _ _ _ _ _ h
end Cases
end SigGolfCandidate.T3.Security.LargeCoupling
