import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeResidualT3
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCLinkInv
import SigGolfCandidate.T3.Secc.LargeResidualRouter
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.FamResidual

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow AuxQuery
  Cell dummyDigest World Probe Hit Charge)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeResidualRouter : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
structure AuxData where
  high : CanonGraph.Node → Digest
  rows : EncLeaf → Fin (2 ^ 22) → HashOutput
  priv : FullGame.FullTable
noncomputable def AuxData.sel (a : AuxData) : Selections := fun L =>
  capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) (a.rows L))
abbrev AuxSpec : OracleSpec AuxQuery
  | .coin n => Fin (n + 1)
  | .init => AuxData
noncomputable def auxLaw (initLaw : PMF AuxData) : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)
  | .coin n => PMF.uniformOfFintype (Fin (n + 1))
  | .init => initLaw
abbrev WCoord := Coord ⊕ Message
/-- Top-layer WOTS seed addresses as plain secrets: none since campaign T8D (top seeds are leaf-family evaluations);
the empty type keeps the shape of the plain coordinates. -/
abbrev WTopAddr := {_a : ChainGraph.Address // False}
/-- WOTS leaves `(layer, tree, leaf)` with a seed family: every leaf (stage B lower leaves, 17 coefficients; campaign
T8D top leaves, 24 coefficients). The name is kept from stage B. -/
abbrev LowerLeaf := {_L : Layer × Fin (2 ^ 31) × Fin 4096 // True}
/-- Secret cells that are not coefficients (`chain ≥ famCount layer`): unused, not observable. -/
abbrev WJunk := {a : ChainGraph.Address // WCT9.famCount a.layer ≤ a.chain.val}
/-- Plain (independently uniform) world coordinates: nodes, (no) top WOTS seeds, nonces. -/
abbrev WPlain := (CanonGraph.Node ⊕ WTopAddr) ⊕ Message
/-- Seed families: WOTS leaves (`famCount` coefficients) and FTS coordinates `(index, coord)` (54 coefficients). -/
abbrev WFam := LowerLeaf ⊕ (Fin (2 ^ 31) × Fin 9)
/-- Split of the world coordinates: WOTS seeds are their leaf family at `lowerPoint chain = chain + 1`, FTS seeds are
evaluations of their family `(index, coord)` at `ftsPoint`. -/
def wsplit : WCoord → WPlain ⊕ (WFam × ℕ)
  | .inl (.inl N) => .inl (.inl (.inl N))
  | .inl (.inr (.inl a)) => .inr (.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩, WCT9.lowerPoint a.chain.val)
  | .inl (.inr (.inr w)) => .inr (.inr (w.1, w.2.1), WCT9.ftsPoint w.2.2.1.val w.2.2.2.val)
  | .inr m => .inl (.inr m)
/-- Embedding of the plain coordinates. -/
def wembed : WPlain → WCoord
  | .inl (.inl N) => .inl (.inl N)
  | .inl (.inr a) => .inl (.inr (.inl a.1))
  | .inr m => .inr m
theorem wsplit_addr (a : ChainGraph.Address) :
    wsplit (.inl (.inr (.inl a))) = .inr (.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩, WCT9.lowerPoint a.chain.val) :=
  rfl
theorem wsplit_lower_eq {a a' : ChainGraph.Address}
    (he : (⟨(a.layer, a.tree, a.leaf), trivial⟩ : LowerLeaf) = ⟨(a'.layer, a'.tree, a'.leaf), trivial⟩)
    (hp : WCT9.lowerPoint a.chain.val = WCT9.lowerPoint a'.chain.val) : a = a' := by
  have h1 := congrArg Subtype.val he
  simp only [Prod.mk.injEq] at h1
  unfold WCT9.lowerPoint at hp
  exact ChainGraph.Address.ext h1.1 h1.2.1 h1.2.2 (Fin.ext (by omega))
theorem wsplit_inr {c : WCoord} {fp : WFam × ℕ} (h : wsplit c = .inr fp) :
    (∃ (a : ChainGraph.Address) (_ha : True), c = .inl (.inr (.inl a)) ∧
      fp = (.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩, WCT9.lowerPoint a.chain.val)) ∨
    (∃ w : WctAddr, c = .inl (.inr (.inr w)) ∧
      fp = (.inr (w.1, w.2.1), WCT9.ftsPoint w.2.2.1.val w.2.2.2.val)) := by
  rcases c with (N | a | w) | m
  · simp only [wsplit, reduceCtorEq] at h
  · rw [wsplit_addr, Sum.inr.injEq] at h
    exact Or.inl ⟨a, trivial, rfl, h.symm⟩
  · simp only [wsplit, Sum.inr.injEq] at h
    exact Or.inr ⟨w, rfl, h.symm⟩
  · simp only [wsplit, reduceCtorEq] at h
noncomputable instance instSeedsWCoord : ClaudeWCT.W9.T3.Security.FamResidual.Seeds WCoord where
  Plain := WPlain
  Fam := WFam
  plainDec := Classical.decEq _
  famDec := Classical.decEq _
  deg := Sum.elim (fun L => WCT9.famCount L.1.1 - 1) (fun _ => 53)
  split := wsplit
  embed := wembed
  split_embed p := by
    rcases p with (N | ⟨a, ha⟩) | m
    · rfl
    · exact ha.elim
    · rfl
  embed_of_split c p h := by
    rcases c with (N | a | w) | m
    · simp only [wsplit, Sum.inl.injEq] at h; subst h; rfl
    · rw [wsplit_addr] at h; cases h
    · simp only [wsplit, reduceCtorEq] at h
    · simp only [wsplit, Sum.inl.injEq] at h; subst h; rfl
  point_lt c f pt h := by
    rcases c with (N | a | w) | m
    · simp only [wsplit, reduceCtorEq] at h
    · rw [wsplit_addr, Sum.inr.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      have := a.chain.isLt
      unfold WCT9.lowerPoint
      omega
    · simp only [wsplit, Sum.inr.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      have := w.2.2.1.isLt; have := w.2.2.2.isLt
      unfold WCT9.ftsPoint WCT9.ftsOrdinal
      omega
    · simp only [wsplit, reduceCtorEq] at h
  seed_inj c c' fp h h' := by
    rcases wsplit_inr h with ⟨a, ha, rfl, rfl⟩ | ⟨w, rfl, rfl⟩ <;>
      rcases wsplit_inr h' with ⟨a', ha', rfl, he⟩ | ⟨w', rfl, he⟩
    · simp only [Prod.mk.injEq, Sum.inl.injEq] at he
      rw [wsplit_lower_eq he.1 he.2]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at he
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at he
    · simp only [Prod.mk.injEq, Sum.inr.injEq] at he
      obtain ⟨⟨h1, h2⟩, h3⟩ := he
      unfold WCT9.ftsPoint WCT9.ftsOrdinal at h3
      have := w.2.2.2.isLt; have := w'.2.2.2.isLt
      have h4 : w.2.2.1 = w'.2.2.1 := Fin.ext (by omega)
      have h5 : w.2.2.2 = w'.2.2.2 := Fin.ext (by omega)
      have : w = w' := Prod.ext h1 (Prod.ext h2 (Prod.ext h4 h5))
      rw [this]
abbrev RWorld (U : Finset HashInput) := World AuxSpec WCoord (Cell U)
section Requests
variable (U : Finset HashInput)
def coinReq (n : Nat) : OracleComp (RWorld U) (Fin (n + 1)) := liftM ((RWorld U).query (.inl (.coin n)))
def initReq : OracleComp (RWorld U) AuxData := liftM ((RWorld U).query (.inl .init))
def readReq (row : Cell U) (charge : Charge) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.read row charge)))
def probeReq (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.probe row test)))
def discloseReq (c : WCoord) (charge : Charge) : OracleComp (RWorld U) Digest :=
  liftM ((RWorld U).query (.inr (.disclose c charge)))
def tickReq (charge : Charge) : OracleComp (RWorld U) Unit := liftM ((RWorld U).query (.inr (.tick charge)))
def discloseAll : List Coord → OracleComp (RWorld U) (List (Coord × Digest))
  | [] => pure []
  | c :: rest => do
      let v ← discloseReq U (.inl c) .none
      let tail ← discloseAll rest
      pure ((c, v) :: tail)
end Requests
def lookupVal (pairs : List (Coord × Digest)) (c : Coord) : Digest :=
  ((pairs.find? fun p => decide (p.1 = c)).map Prod.snd).getD 0
structure RouterState where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  trials : List HashInput
  births : List (HashInput × HashOutput)
  exposures : List HashOutput
  reused : Bool
  memo : List (Message × Option (BitVec 32 × HashOutput))
def RouterState.initial : RouterState := ⟨[], [], 0, [], [], [], false, []⟩
def RouterState.after (st : RouterState) (X : HashInput) : RouterState :=
  { st with seen := X :: st.seen, calls := st.calls + 1 }
def RouterState.Fresh (st : RouterState) (X : HashInput) : Prop := X ∉ st.seen ∧ X ∉ st.trials
noncomputable def RouterState.next (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput) :
    RouterState :=
  if X ∈ U ∧ IsDigestRow X ∧ st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X
def RouterState.known (st : RouterState) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ st.disclosed
def cellValues : CanonGraph.Node → (Coord → Digest) → HashInput
  | .chain p, v => ChainGraph.row p (v (chainChild p))
  | .leaf L, v => pad64 (Extract.leafInput L.1.lay L.1.tree.val L.1.leaf.val
      ((List.range (chainCount L.1.lay)).map fun i => v (.inl (.chain (endPoint L.1 i)))))
  | .node n, v => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .wctChain p, v => WCT9.chainInput p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
      (v (wctItem p.1 p.2.val))
  | .wctLeaf L, v => pad64 (Extract.wctLeafInput L.index.val L.coord.val L.child.val
      (List.ofFn fun t : Fin 6 => v (wctItem (L.index, L.coord, L.child, t) 4)))
  | .wctNode n, v => pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2 ^ (7 - n.1.level.val - 1) + n.1.idx.val)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .forest index, v => pad64 (Extract.forestInput index.val
      ((List.range 9).map fun c => (v (.inl (.wctNode (ftsTopNode index (fin9 c) 0))),
        v (.inl (.wctNode (ftsTopNode index (fin9 c) 1))))))
/-- The canonical input of node `N` from coordinate values (`cell` with the seeds read from the values). -/
noncomputable def cellFrom (N : CanonGraph.Node) (v : Coord → Digest) : HashInput := cellValues N v
noncomputable def refDigest (a : AuxData) (L : EncLeaf) : Digest :=
  match a.sel L with
  | some r => r.2
  | none => dummyDigest L.1.lay
def PrefixRow (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : Prop :=
  ctr.toNat < WCT9.searchLimit L.1.lay ∧ ∀ r, a.sel L = some r → ctr.toNat ≤ r.1.val
def prefixValue (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : HashOutput :=
  if h : ctr.toNat < 2 ^ 22 then a.rows L ⟨ctr.toNat, h⟩ else 0
noncomputable def routerDigits (a : AuxData) (L : Wots.LeafAddr) : List Nat :=
  if h : ∃ L' : EncLeaf, L'.toWots = L then
    ((a.sel (Classical.choose h)).bind fun r => decode L.lay r.2).getD (Wots.dummyDigits L.lay)
  else Wots.dummyDigits L.lay
def RouteOkR (a : AuxData) (index : Nat) : Prop :=
  ∀ lay : Layer, lay ≠ 0 → ∃ (L : EncLeaf) (r : Fin (2 ^ 22) × Digest),
    L.toWots = routeAddr index lay ∧ a.sel L = some r ∧ (decode lay r.2).isSome
def maskOf (a : AuxData) (level node : Nat) : Digest :=
  let answer := a.priv (.inl (header 13 0 0 level (node/2)))
  if node%2=0 then answer.extractLsb' 0 128 else answer.extractLsb' 128 128
def macOf (a : AuxData) (region : Region) : HashOutput :=
  SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag
    (fun i => a.priv (.inl (header 14 0 0 0 i.val))) (List.ofFn region))
def topValue (v : Coord → Digest) (level node : Nat) : Digest :=
  ((treeChild 0 0 level node).map v).getD 0
def EncRow (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad), Extract.msgFits L.1.lay m ∧
    X = Wots.encRow L.toWots m ctr pad
def Parsed (X : HashInput) : Prop := ∃ N : CanonGraph.Node, Extract.posOf X = some N.toPos
section Route
variable (U : Finset HashInput)
def testReq (first : Bool) (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  if first then probeReq U row test else readReq U row .call
noncomputable def routeQuery (a : AuxData) (st : RouterState) (X : HashInput) :
    OracleComp (RWorld U) (HashOutput × RouterState) :=
  let st' : RouterState := st.after X
  let first : Bool := decide (X ∉ st.seen)
  if h : X ∈ U then
    if hp : Parsed X then
      let N := Classical.choose hp
      match firstUnknown st.known N with
      | some cs => (fun y => (y, st')) <$>
          testReq U first ⟨X, h⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
      | none => do
          let pairs ← discloseAll U ((childSlots N).map Prod.fst)
          if X = cellFrom N (lookupVal pairs) then do
            let v ← discloseReq U (.inl (.inl N)) .call
            pure (ChainGraph.joinOutput v (a.high N), st')
          else (fun y => (y, st')) <$> testReq U first ⟨X, h⟩ ⟨none, .label (.inl (.inl N))⟩
    else if he : EncRow X then
      let L := Classical.choose he
      let ctr := Classical.choose (Classical.choose_spec (Classical.choose_spec he))
      match firstUnknownMsg st.known L with
      | some cs => (fun y => (y, st')) <$>
          testReq U first ⟨X, h⟩ ⟨some (.inl cs.1, slotValue X cs.2), .target (refDigest a L)⟩
      | none => do
          let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
          if X = Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
            tickReq U .call
            pure (prefixValue a L ctr, st')
          else (fun y => (y, st')) <$> testReq U first ⟨X, h⟩ ⟨none, .target (refDigest a L)⟩
    else if IsDigestRow X then
      (fun y => (y, if st.Fresh X then { st' with births := (X, y) :: st.births } else st')) <$> readReq U ⟨X, h⟩ .mass
    else (fun y => (y, st')) <$> readReq U ⟨X, h⟩ .call
  else do
    tickReq U .call
    pure (0, st')
noncomputable def readImpl (a : AuxData) : QueryImpl SigGolfCandidate.T3.Spec (OracleComp (RWorld U))
  | .inl (.inl n) => coinReq U n
  | .inl (.inr X) => if h : X ∈ U then readReq U ⟨X, h⟩ .none else pure (0 : HashOutput)
  | .inr c => pure (a.priv c)
def assembleSig (rho : Digest) (N : HashOutput) (v : Coord → Digest) (digitsOf : Wots.LeafAddr → List Nat) :
    Signature :=
  let index := digestIndex N
  ⟨rho,
    fun k => ⟨fun t => v (wctItem (index, k, WCT9.child N k, t) (4 - WCT9.wordDigit (WCT9.rank N k) t)),
      fun l => ((wctPath index k N).map v).getD l.val 0⟩,
    fun lay => piecesSignature lay ((layerChains digitsOf index lay).map v, (layerPath index lay).map v)⟩
def trialRows (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : List HashInput :=
  (List.range (match found with | some (c, _) => c.toNat + 1 | none => WCT9.digestAttemptLimit)).map fun c =>
    pad64 (digestInput rho m (BitVec.ofNat 32 c))
def RouterState.cache (st : RouterState) : Sampling.RCache := fun X => st.births.lookup X
noncomputable def RouterState.signed (st : RouterState) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) :
    RouterState :=
  if CaseC.bankSpec.Reuse st.cache rho m then
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
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).disclosed = st.disclosed ∧ (st.signed rho m found).seen = st.seen ∧
      (st.signed rho m found).calls = st.calls ∧ (st.signed rho m found).births = st.births ∧
      (st.signed rho m found).trials = st.trials ++ trialRows rho m found ∧
      (st.signed rho m found).memo = (m, found) :: st.memo := by
  unfold RouterState.signed
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
noncomputable def signFinish (a : AuxData) (st : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) : OracleComp (RWorld U) (Option Signature × RouterState) :=
  match found with
  | none => pure (none, st)
  | some (_, N) =>
      if RouteOkR a (WCT9.digestIndex N) then do
        let items := signItemsWith (routerDigits a) N
        let pairs ← discloseAll U items
        pure (some (assembleSig rho N (lookupVal pairs) (routerDigits a)),
          { st with disclosed := st.disclosed ++ items })
      else pure (none, st)
noncomputable def routeSign (a : AuxData) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : SigGolfCandidate.T3.Security.Request) : OracleComp (RWorld U) (Option Signature × RouterState) :=
  if request.cache = published then do
    let rho ← discloseReq U (.inr request.message) .none
    match st.memo.lookup request.message with
    | some found => signFinish U a st rho found
    | none => do
        let found ← simulateQ (readImpl U a) (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit)
        signFinish U a (st.signed rho request.message found) rho found
  else pure (none, st)
noncomputable def routeInteraction (a : AuxData) (published : SigGolfCandidate.T3.Cache) (q : Nat) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    RouterState → OracleComp (RWorld U) (Option ((α × QueryLog Requests) × RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some ((value, []), st)))
    (fun input _ next st => match input, next with
      | .inl (.inl n), next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X), next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuery U a st X
            next r.1 r.2
      | .inr request, next => do
          let s ← routeSign U a published st request
          let rest ← next s.1 s.2
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2)))
    program
noncomputable def routeVerdict (a : AuxData) (q : Nat) {β : Type} (program : M β) :
    RouterState → OracleComp (RWorld U) (Option (β × RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some (value, st)))
    (fun input _ next st => match input, next with
      | .inl (.inl n), next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X), next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuery U a st X
            next r.1 r.2
      | .inr c, next => next (a.priv c) st)
    program
noncomputable def routerWith (adversary : Final.AdversaryP) (q : Nat) (a : AuxData) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) := do
  let pairs ← discloseAll U keygenDisclosed
  let v := lookupVal pairs
  let pk := v (.inl (.node rootNode))
  let region := Correctness.cacheRegion fun level node => topValue v level node ^^^ maskOf a level node
  let published : SigGolfCandidate.T3.Cache := ⟨macOf a region, region⟩
  let r ← routeInteraction U a published q (adversary pk published) RouterState.initial
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (GameWith.verdict PaddedGame.checker pk result) st
noncomputable def router (adversary : Final.AdversaryP) (q : Nat) : OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  initReq U >>= routerWith U adversary q
end Route
end ClaudeWCT.W9.T3.Security.LargeResidual
