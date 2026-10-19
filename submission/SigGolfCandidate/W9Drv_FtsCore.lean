import SigGolfCandidate.W9Drv_FtsCore_B

set_option Elab.async false


namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem steps (links : ∀ k : Fin 9, sliceChecked (start k.val) (words k.val) = true)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    Steps Frozen.image u (length k.val) (length k.val) ((result k.val).toState u) := by
  have hpc : u.pc = pcOf (start k.val) := by
    rw [hu.pc]; fin_cases k <;> rfl
  have hs := symRun_sound (rOK_eq (checked k)) (slice_at _ _ (links k)) u hpc
  have hcost : (result k.val).steps = length k.val ∧ (result k.val).cycles = length k.val := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (result k.val).st.obl
  rw [Oblig.all_iff]
  intro o ho
  by_cases hc : k.val = 8
  · have he : k = ⟨8, by decide⟩ := Fin.ext hc
    subst k
    change o ∈ [.valid ⟨some (.reg .x9), BitVec.ofNat 64 (2^64 - 240)⟩ 8] at ho
    simp only [List.mem_singleton] at ho
    subst o
    change accessValid (u.getReg .x9 + BitVec.ofNat 64 (2^64 - 240)) 8 = true
    rw [hu.pairPtr]
    decide +kernel
  · have ho' : (result k.val).st.obl = [] := by
      fin_cases k <;> first | rfl | exact (hc rfl).elim
    rw [ho'] at ho
    simp at ho

end W9Drv.SharedDispatch

namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem good (links : ∀ k : Fin 9, sliceChecked (SharedDispatch.start k.val) (SharedDispatch.words k.val) = true)
    (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List (Digest × Digest)) → OracleComp HashSpec Obs)
    (hu : Pre pk w a k.val pairs u) (hnone : K none = pure (false, 0))
    (hnext : ∀ pair t, Pre pk w a (k.val+1) (pairs ++ [pair]) t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some (pairs ++ [pair])))) :
    GoodQFor (P := P) Frozen.image u (N + (SharedDispatch.length k.val + 185))
      (C + (SharedDispatch.length k.val + 185)) Q
      (A + (SharedDispatch.length k.val + (N600.rankCost (SharedForest.forestRank a k.val) +
        SharedChild.cost k (SharedForest.rawChildFromOutput a k))))
      (ccM (stepN w a (some pairs) k) K) := by
  have ds := SharedDispatch.steps links pk w a k pairs u hu
  have hpc : ((SharedDispatch.result k.val).toState u).pc =
      pcOf (slotStart + 64 * SharedForest.rawForestRank a k.val) :=
    SharedDispatch.pc_eval pk w a k pairs u hu
  have hfb : SharedForest.rawForestRank a k.val < 1024 := Nat.mod_lt _ (by decide)
  by_cases hok : SharedForest.rawForestRank a k.val < 563
  · have hrank : (SharedForest.forestRank a k.val).val = SharedForest.rawForestRank a k.val :=
      Nat.mod_eq_of_lt hok
    have hst : SharedDispatch.chainEntryState k (SharedForest.forestRank a k.val) u =
        (SharedDispatch.result k.val).toState u := by
      unfold SharedDispatch.chainEntryState
      rw [SharedLayout.chain_eq, slot_entry, hrank, ← hpc]
    have hk := k.isLt
    have hreg : 0x1020 + V3.regionOffset k.val = regionAddr k.val := by
      unfold V3.regionOffset regionAddr; omega
    have core := core_good chains childs w (idxOf a) k (SharedForest.rawChildFromOutput a k)
      (SharedForest.forestRank a k.val) u (SharedDispatch.chainEntryState k (SharedForest.forestRank a k.val) u)
      (prevOf w pairs).1 (prevOf w pairs).2 N C A Q
      (fun top => K (some (pairs ++ [SharedV3.orderPair k.val
        (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val)
        top (SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val))])))
      (SharedDispatch.chain_pre pk w a k (SharedForest.forestRank a k.val) pairs u hu)
      (by rw [hreg]; simpa only [SharedV3.handL, if_neg (by omega : k.val ≠ 9)] using hu.prevL)
      (by rw [hreg]; simpa only [SharedV3.handR, if_neg (by omega : k.val ≠ 9)] using hu.prevR)
      (fun ends entry hp computed t ht => hnext _ _
        (next pk w a k (SharedForest.forestRank a k.val) pairs u entry t ends computed hu hp ht))
    rw [hst] at core
    have full := core.steps ds
    simp only [stepN, coordN, hok, not_true_eq_false, ↓reduceIte, SharedV3.coordinate,
      ccM_bind, ccM_pure, bind_assoc, pure_bind]
    simp only [N600.program, ccM_bind] at full
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · have hpast := fetch_invalid_slot _ _ hpc (by omega) hfb
    have rr : GoodQFor (P := P) Frozen.image ((SharedDispatch.result k.val).toState u) 1 0 Q 0
        (pure (false, 0)) := goodQFor_fault hpast
    have full := rr.steps ds
    simp only [stepN, hok, not_false_eq_true, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)

end W9Drv.SharedCoord


namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finishN (w : ClaudeWCT.W9.T3M.WBytes) (state : Option (List (Digest × Digest))) :
    M (Option (Digest × Digest)) :=
  match state with
  | none => pure none
  | some pairs => pure (some (prevOf w pairs))
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => SharedDispatch.length k.val + 185)).sum
def coordsAccept (a : HashOutput) (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => SharedDispatch.length k.val +
    (N600.rankCost (SharedForest.forestRank a k.val) + SharedChild.cost k (SharedForest.rawChildFromOutput a k)))).sum

theorem fold_none (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (stepN w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, stepN, pure_bind] using ih

theorem all_good
    (links : ∀ k : Fin 9, sliceChecked (SharedDispatch.start k.val) (SharedDispatch.words k.val) = true)
    (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (pairs : List (Digest × Digest)) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : Pre pk w a n pairs u) (hnone : K none = pure (false, 0))
    (hnext : ∀ pairs t, Pre pk w a 9 pairs t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some (prevOf w pairs)))) :
    GoodQFor (P := P) Frozen.image u (N + coordsCost ks) (C + coordsCost ks) Q (A + coordsAccept a ks)
      (ccM (ks.foldlM (stepN w a) (some pairs) >>= finishN w) K) := by
  induction ks generalizing n pairs u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishN, ccM_pure]
    simpa [coordsCost, coordsAccept] using hnext pairs u hu
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List (Digest × Digest)) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (stepN w a) state >>= finishN w) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishN, ccM_pure, hnone]
    have hstep := good links chains childs pk w a k pairs u (N + coordsCost ks)
      (C + coordsCost ks) (A + coordsAccept a ks) Q K' hu hkNone
      (fun pair t hh => ih (k.val + 1) (pairs ++ [pair]) t ht
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, coordsAccept, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind] <;> omega

end W9Drv.SharedCoord


namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option maxRecDepth 100000 in
/-- C1: the machine routine cost equals the fixed part (A 77, B and C 89) plus the source's per-child accounting
correction `2 - skips′`, for every coordinate and raw child (checked over all 9 x 128 cases). -/
theorem child_cost_all : ∀ k : Fin 9, ∀ raw : Fin 128,
    SharedChild.cost k raw = (if SharedV3.first k.val then 77 else 89) +
      SharedForest.accountingCorrection k.val raw := by
  decide +kernel

theorem child_cost_eq (k : Fin 9) (raw : Fin 128) :
    SharedChild.cost k raw = (if SharedV3.first k.val then 77 else 89) +
      SharedForest.accountingCorrection k.val raw :=
  child_cost_all k raw

theorem coordsAccept_all (a : HashOutput) :
    coordsAccept a (List.finRange 9) = 846 + SharedForest.jointAccountingCost a := by
  unfold coordsAccept
  simp_rw [child_cost_eq]
  have hfixed : ((List.finRange 9).map (fun k =>
      SharedDispatch.length k.val + (if SharedV3.first k.val then 77 else 89))).sum = 846 := by decide +kernel
  have hpoint : ∀ k : Fin 9,
      SharedDispatch.length k.val + (N600.rankCost (SharedForest.forestRank a k.val) +
        ((if SharedV3.first k.val then 77 else 89) + SharedForest.accountingCorrection k.val (SharedForest.rawChildFromOutput a k))) =
      (SharedDispatch.length k.val + (if SharedV3.first k.val then 77 else 89)) +
        SharedForest.coordinateAccountingCost a k := by
    intro k
    rw [N600.rankCost_eq_c1]
    unfold SharedForest.coordinateAccountingCost
    omega
  simp_rw [hpoint]
  rw [List.sum_map_add, hfixed]
  rfl

theorem final (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : Pre pk w a 9 pairs u) :
    FtsOut ⟨pk,w,a⟩ (prevOf w pairs) u := by
  refine ⟨hu.glob, hu.index, ?_, ?_, ?_, hu.layer, ?_, hu.hashLen,
    hu.heaps 6 (by decide) (by decide), hu.stepOne, hu.stepTwo,
    hu.heaps 7 (by decide) (by decide), hu.heaps 3 (by decide) (by decide),
    hu.heaps 4 (by decide) (by decide), hu.heaps 5 (by decide) (by decide),
    hu.coordStep, hu.pairPtr, hu.bank.top, hu.bank.top8, ?_, hu.d0⟩
  · exact hu.pc
  · have h := hu.prevL
    rwa [show regionAddr 9 + SharedV3.handL 9 = WIT by rfl] at h
  · have h := hu.prevR
    rwa [show regionAddr 9 + SharedV3.handR 9 = WIT + 48 by rfl] at h
  · rw [hu.baseReg]; rfl
  · exact hu.a2 (by decide)

end W9Drv.SharedCoord


namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def FtsGoodByCost (acceptCost : HashOutput → Nat) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs),
    SharedGate.Pre pk w a u → K none = pure (false, 0) →
    (∀ top t, FtsOut ⟨pk,w,a⟩ top t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some top))) →
    GoodQFor (P := P) Frozen.image u (N+2023) (C+2023) Q (A+acceptCost a)
      (ccM (if SharedGate.gateOk a then ftsN w a else pure none) K)

/-- C1 (stage 1) + coordinate-8 dispatch hoist: 24 (gate and setup) + 93 (dispatch) + 4 x 77 + 5 x 89 (child fixed
parts) = 870, plus the joint accounting cost (`≤ 777` on accepted digests, cap 777). -/
def ftsAcceptCost (a : HashOutput) : Nat := 870 + SharedForest.jointAccountingCost a

theorem fts_good_of
    (checkLink : sliceChecked 4 SharedGate.gCheckWords = true)
    (setupLink : sliceChecked 68 SharedGate.gSetupWords = true)
    (links : ∀ k : Fin 9, sliceChecked (SharedDispatch.start k.val) (SharedDispatch.words k.val) = true)
    (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw) :
    FtsGoodByCost ftsAcceptCost (P := P) := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ftsN w a) K else K none
  have hg := SharedGate.good checkLink setupLink pk w a u (N + 1758) (C + 1758)
    (A + (846 + SharedForest.jointAccountingCost a)) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := all_good links chains childs pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide) (by simp) ht hnone (fun pairs st hh => hnext _ st (final pk w a pairs st hh))
      rw [show coordsCost (List.finRange 9) = 1758 by decide, coordsAccept_all] at hc
      apply hc.congr
      change ccM (_ >>= finishN w) K = ccM (ftsN w a) K
      apply congrArg (fun p : M (Option (Digest × Digest)) => ccM p K)
      unfold ftsN
      apply congrArg (fun f : Option (List (Digest × Digest)) → M (Option (Digest × Digest)) =>
        (List.finRange 9).foldlM (stepN w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor (P := P) Frozen.image u (N + 1782) (C + 1782) Q
    (A + (846 + SharedForest.jointAccountingCost a) + 24) (KG (SharedGate.gateOk a)) at hg
  apply (hg.mono (by omega) (by omega) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)).congr
  cases SharedGate.gateOk a <;> simp [KG, ccM_pure]

end W9Drv.SharedCoord

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure ChainReadout (w : SharedV3.WBytes) (coord : Fin 9) (word : Rank)
    (values : Fin 6 → Digest) : Prop where
  padA : ∀ i : Fin 6, V3.chainPadA w coord.val i.val = 0
  padB : ∀ i : Fin 6, V3.chainPadB w coord.val i.val = 0
  padC : ∀ i : Fin 6, V3.chainPadC w coord.val i.val = 0
  reveal : ∀ i : Fin 6, V3.reveal w coord.val i.val (wordDigit word i) = values i

structure PathReadout (w : SharedV3.WBytes) (coord : Fin 9) (raw : Child)
    (path : Nat → Digest) : Prop where
  headerPads : ∀ l, l ≤ SharedV3.lastLevel coord.val →
    SharedV3.nodeHPad w coord.val (SharedV3.physical coord.val raw.val) l = 0
  nodePads : ∀ l, l ≤ SharedV3.lastLevel coord.val → l ≠ 4 →
    SharedV3.nodePad w coord.val (SharedV3.physical coord.val raw.val) l = 0
  siblings : ∀ l, l ≤ SharedV3.lastLevel coord.val →
    SharedV3.sibling w coord.val (SharedV3.physical coord.val raw.val) l = path l
  topOther : SharedV3.topOther w coord.val (SharedV3.physical coord.val raw.val) =
    path (SharedV3.lastLevel coord.val + 1)

theorem chainProgram_zero (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest)
    (hi : index < 2 ^ 31) (h : ChainReadout w coord word values) :
    V3.chainProgram w index coord raw (ClaudeWCT.WCT9.embed word) =
      (List.finRange 6).mapM (fun i =>
        ClaudeWCT.WCT9.chain index coord.val raw.val i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)) := by
  unfold V3.chainProgram
  congr 1
  funext i
  change V3.chainP index coord.val raw.val i.val (4 - wordDigit word i) (wordDigit word i)
    (V3.chainPadA w coord.val i.val) (V3.chainPadB w coord.val i.val)
    (V3.chainPadC w coord.val i.val) (V3.reveal w coord.val i.val (wordDigit word i)) = _
  rw [h.padA, h.padB, h.padC, h.reveal,
    W9Machine.chainP_canonical _ _ _ _ _ _ _ _ _ _ hi coord.isLt raw.isLt i.isLt
      (by have := wordDigit_le_four word i; omega),
    ClaudeWCT.W9.T3M.wctChainP_zero]

theorem nodeInput_zero_header (coord : Fin 9) (index heap : Nat)
    (left pad right : Digest) :
    V3.nodeInput coord.val index heap left 0 pad right =
      wctTopInput coord.val index heap left pad right := by
  unfold V3.nodeInput wctTopInput wctNodeHeader
  rw [W9Drv.nodeHdr_canonical, SigGolfCandidate.T3M.SecurityInputs.withHigh_nodeTweak_zero]

theorem short_topInput_zero (coord index heap : Nat) (left right : Digest) :
    shortHash (wctTopInput coord index heap left 0 right) =
      wctNodeHash coord index heap left right := by
  rw [ClaudeWCT.WCT9.wctNodeHash_eq_short]
  simp only [wctTopInput, wctNodeHeader, SigGolfCandidate.T3M.bytesLE_zero16]

/-- C1: the machine's half selector is the source's `ftsHash` rule once the selector agrees with
`ftsHighHeap` of the computed heap. -/
theorem hashSel_eq_ftsHash {hi : Bool} {heap : Nat} (h : hi = ftsHighHeap heap) (input : HashInput) :
    SharedV3.hashSel hi input = ftsHash heap input := by
  subst h
  rfl

/-- C1: a packed node (zero pad) with the half selected by `hi = ftsHighHeap heap` is the source's
`wctNodeHashH`. -/
theorem sel_topInput_zero {coord index heap : Nat} {hi : Bool} (h : hi = ftsHighHeap heap)
    (left right : Digest) :
    SharedV3.hashSel hi (wctTopInput coord index heap left 0 right) =
      wctNodeHashH coord index heap left right := by
  rw [hashSel_eq_ftsHash h]
  simp only [wctTopInput, wctNodeHashH, SigGolfCandidate.T3M.bytesLE_zero16]

set_option maxRecDepth 100000 in
/-- C1: the machine selector of the leaf (`m = 0`) and of the packed fold outputs (`m = 1..4`) is the source's
`ftsHighHeap` of heap `(128 + child) / 2 ^ m`. -/
theorem hiOut_heap_all : ∀ child : Fin 128, ∀ m : Fin 5,
    SharedV3.hiOut child.val m.val = ftsHighHeap ((128 + child.val) / 2 ^ m.val) := by
  decide +kernel

theorem hiOut_heap (child m : Nat) (hc : child < 128) (hm : m < 5) :
    SharedV3.hiOut child m = ftsHighHeap ((128 + child) / 2 ^ m) :=
  hiOut_heap_all ⟨child, hc⟩ ⟨m, hm⟩

/-- The verifier's leaf input is the source's padded leaf input. -/
theorem leafInput_eq (k index j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    V3.leafInput k index j pad ends = ClaudeWCT.WCT9.leafInputP index k j pad ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafInputP,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    all_goals rfl

/-- C1: the verifier's half-selected leaf of physical child `child` (raw child `raw` in the header) is the source's
`leafHashH` at heap `128 + child`. -/
theorem leafSel_eq (k index raw child : Nat) (hc : child < 128) (pad : Digest) (ends : List Digest)
    (h : ends.length = 6) :
    SharedV3.hashSel (SharedV3.hiOut child 0) (V3.leafInput k index raw pad ends) =
      leafHashH (128 + child) index k raw pad ends := by
  rw [leafInput_eq _ _ _ _ _ h, leafHashH_eq]
  exact hashSel_eq_ftsHash (by rw [hiOut_heap child 0 hc (by decide), Nat.pow_zero, Nat.div_one]) _

theorem childInput_readout (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (path : Nat → Digest) (padR value : Digest) (level : Nat)
    (h : PathReadout w coord raw path) (hl : level ≤ SharedV3.lastLevel coord.val) :
    SharedV3.childInput w index coord.val (SharedV3.physical coord.val raw.val) padR value level =
      let child := SharedV3.physical coord.val raw.val
      let other := path level
      let left := if child / 2 ^ level % 2 = 0 then value else other
      let right := if child / 2 ^ level % 2 = 0 then other else value
      wctTopInput coord.val index ((128 + child) / 2 ^ (level + 1)) left
        (if level = 4 then padR else 0) right := by
  simp only [SharedV3.childInput, h.siblings level hl, h.headerPads level hl,
    nodeInput_zero_header]
  by_cases he : level = 4
  · simp only [if_pos he]
  · simp only [if_neg he, h.nodePads level hl he]


def canonicalChildInput (index coord physical : Nat) (path : Nat → Digest)
    (padR value : Digest) (level : Nat) : HashInput :=
  let other := path level
  let left := if physical / 2 ^ level % 2 = 0 then value else other
  let right := if physical / 2 ^ level % 2 = 0 then other else value
  wctTopInput coord index ((128 + physical) / 2 ^ (level + 1)) left
    (if level = 4 then padR else 0) right

def canonicalChildN (index : Nat) (coord : Fin 9) (raw : Child)
    (ends : List Digest) (padL padR : Digest) (path : Nat → Digest) : M Digest := do
  let leaf ← leafHashH (128 + SharedV3.physical coord.val raw.val) index coord.val raw.val padL ends
  let child := SharedV3.physical coord.val raw.val
  let last := SharedV3.lastLevel coord.val
  let value ← (List.range last).foldlM
    (fun value level => SharedV3.hashSel (SharedV3.hiOut child (level + 1))
      (canonicalChildInput index coord.val child path padR value level)) leaf
  if coord.val = 8 then
    SharedV3.hashSel (decide (SharedV3.direction coord.val child = 0))
      (canonicalChildInput index coord.val child path padR value last)
  else highHash (canonicalChildInput index coord.val child path padR value last)

theorem childN_canonical (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (path : Nat → Digest) (ends : List Digest) (hlen : ends.length = 6)
    (padL padR : Digest) (h : PathReadout w coord raw path) :
    SharedV3.childN w index coord raw ends padL padR =
      canonicalChildN index coord raw ends padL padR path := by
  unfold SharedV3.childN canonicalChildN
  rw [leafSel_eq _ _ _ _ (SharedV3.physical_lt _ _ raw.isLt) _ _ hlen]
  apply bind_congr
  intro leaf
  dsimp only
  have hf : (List.range (SharedV3.lastLevel coord.val)).foldlM
      (fun value level => SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level + 1))
        (SharedV3.childInput w index coord.val (SharedV3.physical coord.val raw.val) padR value level)) leaf =
      (List.range (SharedV3.lastLevel coord.val)).foldlM
      (fun value level => SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level + 1))
        (canonicalChildInput index coord.val (SharedV3.physical coord.val raw.val) path padR value level)) leaf := by
    apply foldlM_congr_mem
    intro value level hl
    rw [childInput_readout _ _ _ _ _ _ _ _ h (by have := List.mem_range.mp hl; omega)]
    rfl
  rw [hf]
  apply bind_congr
  intro value
  rw [childInput_readout _ _ _ _ _ _ _ _ h le_rfl]
  rfl

theorem length_of_support_mapM {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [length_of_support_mapM f xs zs hzs]

def canonicalCoordinate (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M PairRoot := do
  let ends ← (List.finRange 6).mapM fun i =>
    ClaudeWCT.WCT9.chain index coord.val raw.val i.val (4 - wordDigit word i)
      (wordDigit word i) (values i)
  let computed ← canonicalChildN index coord raw ends prev.1 prev.2 path
  pure (SharedV3.orderPair coord.val (SharedV3.physical coord.val raw.val) computed
    (path (SharedV3.lastLevel coord.val + 1)))

theorem coordinate_canonical (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest)
    (prev : PairRoot) (hi : index < 2 ^ 31)
    (hc : ChainReadout w coord word values) (hp : PathReadout w coord raw path) :
    SharedV3.coordinate w index coord raw (ClaudeWCT.WCT9.embed word) prev =
      canonicalCoordinate index coord raw word values path prev := by
  unfold SharedV3.coordinate canonicalCoordinate
  rw [chainProgram_zero _ _ _ _ _ _ hi hc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ends hends
  have hlen : ends.length = 6 := by
    simpa using length_of_support_mapM _ (List.finRange 6) ends hends
  rw [childN_canonical _ _ _ _ _ _ hlen _ _ hp, hp.topOther]

#print axioms chainProgram_zero
#print axioms childInput_readout
#print axioms childN_canonical
#print axioms coordinate_canonical
end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def canonicalInnerStep (first : Bool) (index coord child : Nat) (path : Nat → Digest)
    (prev : PairRoot) (value : Digest) (level : Nat) : M Digest :=
  let other := path level
  let lr := if child / 2 ^ level % 2 = 0 then (value, other) else (other, value)
  sharedNode first coord index ((128 + child) / 2 ^ (level + 1)) (fun _ => prev) lr.1 lr.2

theorem canonicalInnerStep_eq (first : Bool) (index coord child : Nat) (hc : child < 128)
    (path : Nat → Digest) (prev : PairRoot) (value : Digest) (level : Nat) (hl : level < 5) :
    canonicalInnerStep first index coord child path prev value level =
      if level = 4 ∧ first then highHash (canonicalChildInput index coord child path prev.2 value level)
      else SharedV3.hashSel (SharedV3.hiOut child (level + 1))
        (canonicalChildInput index coord child path prev.2 value level) := by
  unfold canonicalInnerStep canonicalChildInput
  by_cases he : level = 4
  · subst level
    have hge : ¬(128 + child) / 2 ^ (4 + 1) < 4 := by norm_num; omega
    have hlt : (128 + child) / 2 ^ (4 + 1) < 8 := by norm_num; omega
    have h5 : SharedV3.hiOut child (4 + 1) = false := by simp [SharedV3.hiOut]
    simp only [sharedNode, if_neg hge, if_pos hlt, if_true, true_and, h5]
    cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      split_ifs <;> rfl
  · have hge : ¬(128 + child) / 2 ^ (level + 1) < 8 := by
      interval_cases level <;> norm_num at * <;> omega
    have hg4 : ¬(128 + child) / 2 ^ (level + 1) < 4 := by omega
    simp only [sharedNode, if_neg hg4, if_neg hge, he, false_and, ↓reduceIte]
    rw [sel_topInput_zero (hiOut_heap child (level + 1) hc (by omega))]
    split_ifs <;> rfl

def sourceCoordinate (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M PairRoot := do
  let child : Child := ⟨SharedV3.physical coord.val raw.val, SharedV3.physical_lt _ _ raw.isLt⟩
  let inner ← recoverSharedInner (SharedV3.first coord.val) index coord.val child word values path prev
  if SharedV3.first coord.val then
    pure (SharedV3.orderPair coord.val child.val inner (path 5))
  else
    let lr := if child.val / 32 % 2 = 0 then (inner, path 5) else (path 5, inner)
    let outer ← sharedOuterHash coord.val index (2 + child.val / 64) lr.1 lr.2
    pure (SharedV3.orderPair coord.val child.val outer (path 6))

theorem recoverSharedInner_false (index coord : Nat) (child : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    recoverSharedInner false index coord child word values path prev = (do
      let ends ← (List.finRange 6).mapM fun i =>
        ClaudeWCT.WCT9.chain index coord (rawChild false child.val) i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)
      let leaf ← leafHashH (128 + child.val) index coord (rawChild false child.val) prev.1 ends
      (List.range 5).foldlM (fun value level =>
        SharedV3.hashSel (SharedV3.hiOut child.val (level + 1))
          (canonicalChildInput index coord child.val path prev.2 value level)) leaf) := by
  unfold recoverSharedInner
  apply bind_congr
  intro ends
  apply bind_congr
  intro leaf
  apply foldlM_congr_mem
  intro value level hl
  exact (canonicalInnerStep_eq false index coord child.val child.isLt path prev value level
    (List.mem_range.mp hl)).trans (by simp)

theorem recoverSharedInner_true (index coord : Nat) (child : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    recoverSharedInner true index coord child word values path prev = (do
      let ends ← (List.finRange 6).mapM fun i =>
        ClaudeWCT.WCT9.chain index coord child.val i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)
      let leaf ← leafHashH (128 + child.val) index coord child.val prev.1 ends
      let value ← (List.range 4).foldlM (fun value level =>
        SharedV3.hashSel (SharedV3.hiOut child.val (level + 1))
          (canonicalChildInput index coord child.val path prev.2 value level)) leaf
      highHash (canonicalChildInput index coord child.val path prev.2 value 4)) := by
  unfold recoverSharedInner
  apply bind_congr
  intro ends
  apply bind_congr
  intro leaf
  change (List.range 5).foldlM (canonicalInnerStep true index coord child.val path prev) leaf = _
  rw [show List.range 5 = List.range 4 ++ [4] from rfl, List.foldlM_append]
  have hf : (List.range 4).foldlM (canonicalInnerStep true index coord child.val path prev) leaf =
      (List.range 4).foldlM (fun value level =>
        SharedV3.hashSel (SharedV3.hiOut child.val (level + 1))
          (canonicalChildInput index coord child.val path prev.2 value level)) leaf := by
    apply foldlM_congr_mem
    intro value level hl
    rw [canonicalInnerStep_eq _ _ _ _ child.isLt _ _ _ _ (by have := List.mem_range.mp hl; omega)]
    have he : level ≠ 4 := by have := List.mem_range.mp hl; omega
    simp [he]
  rw [hf]
  apply bind_congr
  intro value
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure_comp]
  rw [canonicalInnerStep_eq _ _ _ _ child.isLt _ _ _ _ (by decide)]
  simp

#print axioms canonicalInnerStep_eq
#print axioms recoverSharedInner_false
#print axioms recoverSharedInner_true
end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Stage 2 (merged singleton "Cm"): the top fold of a non-first tree. For tree 8 the left top node (heap 2,
direction 0) keeps the HIGH half and the right one (heap 3) the LOW half, which is `sharedOuterHash`'s
`coord = 8 ∧ heap = 3` rule at heap `2 + p / 64`. -/
theorem canonical_top_outer (coord : Fin 9) (p : Nat) (hp : p < 128) (hf : SharedV3.first coord.val = false)
    (input : HashInput) :
    (if coord.val = 8 then SharedV3.hashSel (decide (SharedV3.direction coord.val p = 0)) input
      else highHash input) =
      (if coord.val = 8 ∧ 2 + p / 64 = 3 then shortHash input else highHash input) := by
  have hdir : SharedV3.direction coord.val p = p / 64 := by
    unfold SharedV3.direction SharedV3.lastLevel
    rw [hf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  rw [hdir]
  by_cases h8 : coord.val = 8
  · rw [if_pos h8]
    by_cases h0 : p / 64 = 0
    · rw [if_neg (fun h => by have h2 := h.2; omega), decide_eq_true h0]
      rfl
    · rw [if_pos ⟨h8, by omega⟩, decide_eq_false h0]
      rfl
  · rw [if_neg h8, if_neg (fun h => h8 h.1)]

theorem canonicalCoordinate_eq_sourceCoordinate (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    canonicalCoordinate index coord raw word values path prev =
      sourceCoordinate index coord raw word values path prev := by
  have hraw : rawChild (SharedV3.first coord.val) (SharedV3.physical coord.val raw.val) = raw.val :=
    raw_physical_child _ _ raw.isLt
  unfold canonicalCoordinate sourceCoordinate
  cases hf : SharedV3.first coord.val with
  | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      rw [recoverSharedInner_false]
      simp only [hf] at hraw
      simp only [hraw, bind_assoc]
      apply bind_congr
      intro ends
      unfold canonicalChildN
      simp only [SharedV3.lastLevel, hf, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      apply bind_congr
      intro leaf
      apply bind_congr
      intro value
      rw [canonical_top_outer coord (SharedV3.physical coord.val raw.val)
        (SharedV3.physical_lt _ _ raw.isLt) hf]
      have heap : (128 + SharedV3.physical coord.val raw.val) / 2 ^ (5 + 1) =
          2 + SharedV3.physical coord.val raw.val / 64 := by norm_num; omega
      simp only [canonicalChildInput, sharedOuterHash, heap, show (5 : Nat) ≠ 4 by decide,
        if_false, show 2 ^ 5 = 32 by decide]
      split_ifs <;> rfl
  | true =>
      have hn : coord.val ≠ 8 := by
        intro he
        simp [SharedV3.first, he] at hf
      have hp : SharedV3.physical coord.val raw.val = raw.val := by
        simp [SharedV3.physical, hf, physicalChild]
      simp only [hf, ↓reduceIte]
      rw [recoverSharedInner_true]
      simp only [hp, bind_assoc]
      apply bind_congr
      intro ends
      unfold canonicalChildN
      simp only [SharedV3.lastLevel, hf, hp, ↓reduceIte, hn, bind_assoc]

#print axioms canonicalCoordinate_eq_sourceCoordinate
end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def rawOfPhysical (first : Bool) (child : Child) : Child :=
  ⟨rawChild first child.val, by
    have h := child.isLt
    cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega⟩

theorem physical_rawOfPhysical (first : Bool) (child : Child) :
    physicalChild first (rawOfPhysical first child).val = child.val := by
  have h := child.isLt
  cases first <;> simp only [physicalChild, rawOfPhysical, rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega

def sourcePair (index : Nat) (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : M PairRoot := do
  let a ← sourceCoordinate index ⟨2 * pair.val, by omega⟩
    (rawOfPhysical true (firstChild s)) aWord opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩) prev
  sourceCoordinate index ⟨2 * pair.val + 1, by omega⟩
    (rawOfPhysical false (secondChild s)) bWord opened.secondValues
    (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩) a

theorem sourcePair_eq_recoverPair (index : Nat) (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) :
    sourcePair index pair s aWord bWord opened prev =
      recoverPair index pair.val s aWord bWord opened prev := by
  have hfirst : SharedV3.first (2 * pair.val) = true := by simp [SharedV3.first]; omega
  have hsecond : SharedV3.first (2 * pair.val + 1) = false := by simp [SharedV3.first]
  have ha : SharedV3.physical (2 * pair.val) (rawOfPhysical true (firstChild s)).val = (firstChild s).val := by
    simp only [SharedV3.physical, hfirst, physical_rawOfPhysical]
  have hb : SharedV3.physical (2 * pair.val + 1) (rawOfPhysical false (secondChild s)).val = (secondChild s).val := by
    simp only [SharedV3.physical, hsecond, physical_rawOfPhysical]
  unfold sourcePair sourceCoordinate recoverPair
  simp only [ha, hb, hfirst, hsecond, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
    SharedV3.orderPair, SharedV3.direction, SharedV3.lastLevel]
  rfl

def sourceSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : M PairRoot :=
  sourceCoordinate index 8 (rawOfPhysical false selected) word opened.values
    (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) prev

theorem sourceSingleton_eq_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    sourceSingleton index selected word opened prev = recoverSingleton index selected word opened prev := by
  have hf : SharedV3.first 8 = false := by decide
  have hp : SharedV3.physical 8 (rawOfPhysical false selected).val = selected.val := by
    simp only [SharedV3.physical, hf, physical_rawOfPhysical]
  unfold sourceSingleton sourceCoordinate recoverSingleton
  simp only [show (8 : Fin 9).val = 8 from rfl, hp, hf, Bool.false_eq_true, ↓reduceIte, SharedV3.orderPair, SharedV3.direction,
    SharedV3.lastLevel]
  rfl

def sourceGroupedForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : M PairRoot := do
  let prev ← (List.finRange 4).foldlM (fun prev pair =>
    sourcePair index pair (selected.pairs pair) (words.first pair) (words.second pair)
      (opened.pairs pair) prev) ftsStart
  sourceSingleton index selected.singleton words.singleton opened.singleton prev

theorem sourceGroupedForest_eq_recoverForest (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (opened : ForestOpening) :
    sourceGroupedForest index selected words opened = recoverForest index selected words opened := by
  unfold sourceGroupedForest recoverForest
  simp only [sourcePair_eq_recoverPair, sourceSingleton_eq_recoverSingleton]

#print axioms sourcePair_eq_recoverPair
#print axioms sourceSingleton_eq_recoverSingleton
#print axioms sourceGroupedForest_eq_recoverForest
end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def coordinateChild (selected : ForestSelection) (coord : Fin 9) : Child :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then firstChild (selected.pairs pair) else secondChild (selected.pairs pair)
  else selected.singleton

def coordinateRaw (selected : ForestSelection) (coord : Fin 9) : Child :=
  rawOfPhysical (SharedV3.first coord.val) (coordinateChild selected coord)

def coordinateWord (words : ForestWords) (coord : Fin 9) : Rank :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then words.first pair else words.second pair
  else words.singleton

def coordinateValues (opened : ForestOpening) (coord : Fin 9) : Fin 6 → Digest :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then (opened.pairs pair).firstValues else (opened.pairs pair).secondValues
  else opened.singleton.values

def coordinatePath (opened : ForestOpening) (coord : Fin 9) : Nat → Digest :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then fun level => (opened.pairs pair).firstPath ⟨level % 6, Nat.mod_lt _ (by decide)⟩
    else fun level => (opened.pairs pair).secondPath ⟨level % 7, Nat.mod_lt _ (by decide)⟩
  else fun level => opened.singleton.path ⟨level % 7, Nat.mod_lt _ (by decide)⟩

def sourceNineForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : M PairRoot :=
  (List.finRange 9).foldlM (fun prev coord =>
    sourceCoordinate index coord (coordinateRaw selected coord) (coordinateWord words coord)
      (coordinateValues opened coord) (coordinatePath opened coord) prev) ftsStart

attribute [local irreducible] sourceCoordinate rawOfPhysical

theorem sourceNineForest_eq_grouped (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (opened : ForestOpening) :
    sourceNineForest index selected words opened = sourceGroupedForest index selected words opened := by
  have hnine : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [sourceNineForest, sourceGroupedForest, hnine, hfour, List.foldlM_cons, List.foldlM_nil,
    sourcePair, sourceSingleton, bind_assoc, pure_bind]
  simp only [coordinateRaw, coordinateChild, coordinateWord, coordinateValues, coordinatePath]
  norm_num [SharedV3.first]
  rfl

theorem forest_canonical (w : SharedV3.WBytes) (index : Nat) (hi : index < 2 ^ 31)
    (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (hstart : SharedV3.initialPair w = ftsStart)
    (hc : ∀ coord, ChainReadout w coord (coordinateWord words coord) (coordinateValues opened coord))
    (hp : ∀ coord, PathReadout w coord (coordinateRaw selected coord) (coordinatePath opened coord)) :
    SharedV3.forest w index (coordinateRaw selected)
      (fun coord => ClaudeWCT.WCT9.embed (coordinateWord words coord)) =
        recoverForest index selected words opened := by
  rw [← sourceGroupedForest_eq_recoverForest, ← sourceNineForest_eq_grouped]
  unfold SharedV3.forest sourceNineForest
  rw [hstart]
  apply foldlM_congr_mem
  intro prev coord _
  exact (coordinate_canonical w index coord _ _ _ _ prev hi (hc coord) (hp coord)).trans
    (canonicalCoordinate_eq_sourceCoordinate index coord _ _ _ _ prev)

#print axioms sourceNineForest_eq_grouped
#print axioms forest_canonical
end W9Drv.SharedCanonical

namespace W9Drv.SharedAcceptedFold
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
def step (init : β) (f : β → α → m β) (ok : α → Bool)
    (state : Option (List β)) (k : α) : m (Option (List β)) := do
  let some hist := state | pure none
  if !ok k then return none
  let p ← f (hist.getLastD init) k
  pure (some (hist ++ [p]))
def finish (init : β) (state : Option (List β)) : m (Option β) :=
  match state with | none => pure none | some hist => pure (some (hist.getLastD init))
theorem accepted (init : β) (f : β → α → m β) (ok : α → Bool)
    (ks : List α) (hok : ∀ k ∈ ks, ok k = true) (hist : List β) :
    (ks.foldlM (step init f ok) (some hist) >>= finish init) = (ks.foldlM f (hist.getLastD init) >>= fun p => pure (some p)) := by
  induction ks generalizing hist with
  | nil => simp [finish]
  | cons k ks ih =>
    have hk := hok k (by simp)
    have hks : ∀ a ∈ ks, ok a = true := fun a ha => hok a (by simp [ha])
    simp only [List.foldlM_cons, step, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind_assoc, pure_bind]
    congr 1
    funext p
    rw [ih hks]
    simp
end W9Drv.SharedAcceptedFold

namespace W9Drv.SharedCoord
open W9Machine SigGolfCandidate.T3 SigGolfCandidate.Research

theorem ftsN_accepted (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (hr : ∀ k : Fin 9, SharedForest.rawForestRank a k.val < 563) :
    ftsN w a = (do
      let p ← SharedV3.forest w (idxOf a) (SharedForest.rawChildFromOutput a)
        (fun k => N600.embed (SharedForest.forestRank a k.val))
      pure (some p)) := by
  have hs : stepN w a = SharedAcceptedFold.step (SharedV3.initialPair w)
      (fun prev k => coordN w (idxOf a) k (SharedForest.rawChildFromOutput a k)
        (SharedForest.forestRank a k.val) prev)
      (fun k => decide (SharedForest.rawForestRank a k.val < 563)) := by
    funext state k
    cases state <;> simp [stepN, SharedAcceptedFold.step, hr k, prevOf]
  have h := SharedAcceptedFold.accepted (m := M) (SharedV3.initialPair w)
    (fun prev k => coordN w (idxOf a) k (SharedForest.rawChildFromOutput a k)
      (SharedForest.forestRank a k.val) prev)
    (fun k => decide (SharedForest.rawForestRank a k.val < 563))
    (List.finRange 9) (fun k _ => by simp [hr k]) []
  have he : ftsN w a =
      ((List.finRange 9).foldlM (stepN w a) (some []) >>=
        SharedAcceptedFold.finish (SharedV3.initialPair w)) := by
    unfold ftsN
    congr 1
    funext state
    cases state <;> rfl
  rw [he, hs]
  simpa only [List.getLastD_nil, SharedV3.forest, coordN] using h
end W9Drv.SharedCoord


namespace W9Drv.SharedCanonical
open W9Machine SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem coordinateRaw_output (a : HashOutput) :
    coordinateRaw (forestSelectionFromOutput a) = rawChildFromOutput a := by
  funext k
  have hc : coordinateChild (forestSelectionFromOutput a) k = physicalChildFromOutput a k := by
    fin_cases k
    · exact (physicalFromOutput_first a 0).symm
    · exact (physicalFromOutput_second a 0).symm
    · exact (physicalFromOutput_first a 1).symm
    · exact (physicalFromOutput_second a 1).symm
    · exact (physicalFromOutput_first a 2).symm
    · exact (physicalFromOutput_second a 2).symm
    · exact (physicalFromOutput_first a 3).symm
    · exact (physicalFromOutput_second a 3).symm
    · exact (physicalFromOutput_singleton a).symm
  unfold coordinateRaw
  rw [hc]
  apply Fin.ext
  exact raw_physical_child (firstCoord k.val) (rawChildFromOutput a k).val
    (rawChildFromOutput a k).isLt

theorem coordinateWord_output (a : HashOutput) (k : Fin 9) :
    coordinateWord (forestWordsFromOutput a) k = forestRank a k.val := by
  fin_cases k <;> rfl
end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
open W9Machine SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem chainReadout_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (word : Rank) :
    ChainReadout (Paired.witEnc output witness) k word (coordinateValues witness.signature.forest k) := by
  refine ⟨PairedReadout.chainPadA_witEnc output witness k,
    PairedReadout.chainPadB_witEnc output witness k,
    PairedReadout.chainPadC_witEnc output witness k,?_⟩
  intro i
  unfold V3.reveal
  split_ifs
  · exact Paired.wleafValue_witEnc output witness k i
  · exact Paired.wchainValue_witEnc output witness k i

theorem pathReadout_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) :
    PathReadout (Paired.witEnc output witness) k (rawChildFromOutput output k)
      (coordinatePath witness.signature.forest k) := by
  refine ⟨?_,?_,?_,Paired.wtopOther_witEnc output witness k⟩
  · intro l hl;exact PairedReadout.nodeHPad_witEnc output witness k l
  · intro l hl hne;exact PairedReadout.nodePad_witEnc output witness k l hl hne
  · intro l hl;exact Paired.wsibling_witEnc output witness k l (by omega)

theorem forest_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (hi:index<2^31) :
    SharedV3.forest (Paired.witEnc output witness) index (rawChildFromOutput output)
      (fun k=>ClaudeWCT.WCT9.embed (forestRank output k.val)) =
      recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest := by
  have hp:∀k,PathReadout (Paired.witEnc output witness) k
      (coordinateRaw (forestSelectionFromOutput output) k) (coordinatePath witness.signature.forest k):=by
    intro k;rw[coordinateRaw_output];exact pathReadout_witEnc output witness k
  have h:=forest_canonical (Paired.witEnc output witness) index hi
    (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest
    (PairedReadout.initialPair_witEnc output witness)
    (fun k=>chainReadout_witEnc output witness k _) hp
  simpa only[coordinateRaw_output,coordinateWord_output] using h
#print axioms chainReadout_witEnc
#print axioms pathReadout_witEnc
#print axioms forest_witEnc
end W9Drv.SharedCanonical
