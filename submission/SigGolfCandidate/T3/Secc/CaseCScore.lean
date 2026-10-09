import SigGolfCandidate.T3.BPORS

section
namespace SigGolfCandidate.T3.Sampling.WeightedSelection
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
open DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem acceptanceProbability_ne_zero : acceptanceProbability ≠ 0 := by
  rw [DigestCounting.acceptanceProbability_eq_p0]
  norm_num [DigestCounting.p0, SigGolfResearch.Gate6.Budget.p0]
noncomputable def freshPrice (weight : HashOutput → ENNReal) : ENNReal :=
  acceptedWeight digestDecode weight / acceptanceProbability
theorem digest_nonce_trials_injective (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) :
    Function.Injective (fun point : Digest × Fin fuel => digestTrial point.1 message point.2.val) := by
  intro left right heq
  dsimp only at heq
  have hrho := digestTrial_nonce_injective heq
  apply Prod.ext hrho
  apply Fin.ext
  rw [hrho] at heq
  exact digestTrial_injective right.1 message (left.2.isLt.trans_le hlimit)
    (right.2.isLt.trans_le hlimit) heq
end SigGolfCandidate.T3.Sampling.WeightedSelection
end
section
namespace SigGolfCandidate.T3.Security.LazyPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling.WeightedSelection
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
end SigGolfCandidate.T3.Security.LazyPrivate
end
section
namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]
noncomputable def score (values : Source → Value) (target : Target → Value) : ENNReal :=
  ∑ embedding : Target ↪ Source,
    if (fun slot => values (embedding slot)) = target then 1 else 0
theorem score_card (values : Source → Value) (target : Target → Value) :
    score values target =
      (Fintype.card {embedding : Target ↪ Source //
        (fun slot => values (embedding slot)) = target} : ENNReal) := by
  classical
  simp [score, Fintype.card_subtype]
theorem one_le_score (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) (hcovered : ∀ slot, ∃ source, values source = target slot) :
    1 ≤ score values target := by
  classical
  choose chosen hchosen using hcovered
  let embedding : Target ↪ Source := ⟨chosen, fun first second heq =>
    hinj ((hchosen first).symm.trans ((congrArg values heq).trans (hchosen second)))⟩
  have hmatch : (fun slot => values (embedding slot)) = target := funext hchosen
  have h := Finset.single_le_sum
    (f := fun e : Target ↪ Source =>
      if (fun slot => values (e slot)) = target then (1 : ENNReal) else 0)
    (fun _ _ => bot_le) (Finset.mem_univ embedding)
  simpa only [hmatch, if_true, score] using h
theorem average_score (values : Source → Value) :
    finiteAverage (fun target : Target → Value => score values target) =
      ((Fintype.card Source).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal) ^ Fintype.card Target := by
  classical
  unfold finiteAverage score
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq, Fintype.card_fun, Nat.cast_pow]
end SigGolfCandidate.T3.BPORS.InjectiveCover
end
section
namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]
end SigGolfCandidate.T3.BPORS.InjectiveCover
end
section
namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling.WeightedSelection
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]
theorem score_source_le (embed : Source ↪ New) (oldValues : Source → Value)
    (newValues : New → Value) (target : Target → Value)
    (hvalues : ∀ source, newValues (embed source) = oldValues source) :
    score oldValues target ≤ score newValues target := by
  classical
  let liftMatch :
      {e : Target ↪ Source // (fun slot => oldValues (e slot)) = target} →
      {e : Target ↪ New // (fun slot => newValues (e slot)) = target} := fun e =>
    ⟨e.val.trans embed, funext (fun slot => (hvalues (e.val slot)).trans (congrFun e.property slot))⟩
  have hinj : Function.Injective liftMatch := by
    intro first second h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    apply embed.injective
    exact congrArg (fun e => e.val slot) h
  rw [score_card, score_card]
  exact_mod_cast Fintype.card_le_of_injective liftMatch hinj
theorem score_append_mono (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score oldValues target ≤ score (Sum.elim oldValues newValues) target :=
  score_source_le Function.Embedding.inl oldValues (Sum.elim oldValues newValues) target (fun _ => rfl)
end SigGolfCandidate.T3.BPORS.InjectiveCover
end
section
namespace SigGolfCandidate.T3.DigestSampling
open OracleComp ENNReal
open SigGolfResearch.Gate6
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
def rawRecordViewEquiv : RawRecord ≃ RawView × (Padding × Unused) where
  toFun r := ((r.1.1,fun c => (r.1.2 c,r.2.1 c)),r.2.2)
  invFun r := ((r.1.1,fun c => (r.1.2 c).1),(fun c => (r.1.2 c).2,r.2))
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def gateCoordinatesEquiv : HashOutput ≃ RawView × (Padding × Unused) :=
  (Equiv.ofBijective digestRecord digestRecord_bijective).trans rawRecordViewEquiv
theorem gateCoordinates_view (output : HashOutput) :
    (gateCoordinatesEquiv output).1=rawView output := rfl
theorem gateCoordinates_gate (output : HashOutput) :
    digestGate output=true ↔ (gateCoordinatesEquiv output).2.1=0 := by
  change digestGate output=true ↔ (digestRecord output).2.2.1=0
  rw [digestGate,decide_eq_true_eq,digestRecord_gate_zero]
theorem finiteAverage_div {α : Type} [Fintype α] (f : α → ENNReal) (d : ENNReal) :
    BPORS.finiteAverage (fun x => f x/d)=BPORS.finiteAverage f/d := by
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring
theorem average_gate_weight (payoff : RawView → ENNReal) :
    BPORS.finiteAverage (fun output : HashOutput =>
      if digestGate output=true then payoff (rawView output) else 0)=
        BPORS.finiteAverage payoff/8 := by
  have he (output : HashOutput) :
      (if digestGate output=true then payoff (rawView output) else 0)=
        (if (gateCoordinatesEquiv output).2.1=0 then payoff (gateCoordinatesEquiv output).1 else 0) := by
    simp only [gateCoordinates_view,gateCoordinates_gate]
  simp_rw [he]
  rw [BPORS.finiteAverage_equiv gateCoordinatesEquiv
    (fun p => if p.2.1=0 then payoff p.1 else 0),BPORS.finiteAverage_pair]
  have hi (view : RawView) : BPORS.finiteAverage
      (fun suffix : Padding × Unused => if suffix.1=0 then payoff view else 0)=payoff view/8 := by
    rw [BPORS.finiteAverage_pair]
    change BPORS.finiteAverage (fun gate : Padding =>
      BPORS.finiteAverage (fun _ : Unused => if gate=0 then payoff view else 0))=_
    simp_rw [BPORS.History.finiteAverage_constant]
    unfold BPORS.finiteAverage
    simp [Padding]
  simp_rw [hi]
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro view _
  ring
end SigGolfCandidate.T3.DigestSampling
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def outIdx (x : HashOutput) : Fin (2 ^ 31) := (rawView x).1
def outBucket (x : HashOutput) (c : Fin 7) : Fin 16 := ((rawView x).2 c).1
def outLeaves (x : HashOutput) (c : Fin 7) : Fin 3 → Fin 128 := ((rawView x).2 c).2
def label (x : HashOutput) : BPORS.History.Proposal := (outIdx x, fun c => outBucket x c)
def labels (X : List HashOutput) : List BPORS.History.Proposal := X.map label
abbrev Slot (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) : Type :=
  {s : Fin X.length × Fin 3 // outIdx (X.get s.1) = i ∧ outBucket (X.get s.1) c = b}
def slotValue (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) (s : Slot X i c b) : Fin 128 :=
  outLeaves (X.get s.1.1) c s.1.2
noncomputable def coordScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) : ENNReal :=
  BPORS.InjectiveCover.score (slotValue X i c b) target
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal :=
  if digestGate N=true then
    ∏ c : Fin 7, coordScore X (outIdx N) c (outBucket N c) (outLeaves N c) else 0
def CoordCovered (X : List HashOutput) (N : HashOutput) (c : Fin 7) : Prop :=
  ∀ j, ∃ s : Slot X (outIdx N) c (outBucket N c), slotValue X (outIdx N) c (outBucket N c) s = outLeaves N c j
theorem one_le_score (X : List HashOutput) (N : HashOutput)
    (hinj : ∀ c, Function.Injective (outLeaves N c)) (hgate : digestGate N=true)
    (hcov : ∀ c, CoordCovered X N c) : 1 ≤ score X N := by
  simp only [score,hgate,if_true]
  apply Finset.one_le_prod''
  intro c
  exact BPORS.InjectiveCover.one_le_score _ _ (hinj c) (hcov c)
def slotEmbed (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    Slot X i c b ↪ Slot (X ++ Y) i c b where
  toFun s := ⟨(Fin.castLE (by simp) s.1.1, s.1.2), by
    have h := s.2
    simp only [List.get_eq_getElem, Fin.val_castLE] at h ⊢
    rw [List.getElem_append_left s.1.1.isLt]
    exact h⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    have h1 := congrArg (fun u : Slot (X ++ Y) i c b => u.1) h
    simp only [Prod.mk.injEq] at h1
    exact Prod.ext (Fin.castLE_injective _ h1.1) h1.2
theorem coordScore_append_mono (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) : coordScore X i c b target ≤ coordScore (X ++ Y) i c b target := by
  unfold coordScore
  apply BPORS.InjectiveCover.score_source_le (slotEmbed X Y i c b)
  intro s
  simp only [slotValue, slotEmbed, Function.Embedding.coeFn_mk, List.get_eq_getElem, Fin.val_castLE]
  rw [List.getElem_append_left s.1.1.isLt]
theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X ++ Y) N := by
  unfold score
  split_ifs with hg
  · exact Finset.prod_le_prod' fun c _ => coordScore_append_mono X Y _ c _ _
  · exact le_rfl
noncomputable def hits (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) : Nat :=
  (Finset.univ.filter fun k : Fin X.length => outIdx (X.get k) = i ∧ outBucket (X.get k) c = b).card
theorem card_slot (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    Fintype.card (Slot X i c b) = 3 * hits X i c b := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun s : Fin X.length × Fin 3 =>
      outIdx (X.get s.1) = i ∧ outBucket (X.get s.1) c = b) =
      (Finset.univ.filter fun k : Fin X.length => outIdx (X.get k) = i ∧ outBucket (X.get k) c = b) ×ˢ
        (Finset.univ : Finset (Fin 3)) := by
    ext s
    simp
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, hits, Nat.mul_comm]
theorem hits_eq_count (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    hits X i c b = ((BPORS.History.atIndex i (labels X)).map fun row => row c).count b := by
  induction X with
  | nil => simp [hits, labels, BPORS.History.atIndex]
  | cons x X ih =>
      have hsplit : hits (x :: X) i c b =
          (if outIdx x = i ∧ outBucket x c = b then 1 else 0) + hits X i c b := by
        unfold hits
        rw [Finset.card_filter, Finset.card_filter]
        exact Fin.sum_univ_succ (n := X.length) _
      rw [hsplit, ih]
      simp only [labels, List.map_cons, BPORS.History.atIndex_cons, label]
      by_cases hi : outIdx x = i
      · simp only [hi, if_true, true_and, List.map_cons, List.count_cons]
        by_cases hb : outBucket x c = b
        · simp [hb, Nat.add_comm]
        · simp [hb]
      · simp [hi]
theorem average_coordScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    BPORS.finiteAverage (fun target : Fin 3 → Fin 128 => coordScore X i c b target) =
      BPORS.bucketMass ((BPORS.History.atIndex i (labels X)).map fun row => row c) b / 128 ^ 3 := by
  unfold coordScore
  rw [BPORS.InjectiveCover.average_score, card_slot, hits_eq_count, BPORS.bucketMass]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
theorem average_coordinate (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) :
    BPORS.finiteAverage (fun d : Fin 16 × (Fin 3 → Fin 128) => coordScore X i c d.1 d.2) =
      BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c) / 128 ^ 3 := by
  rw [BPORS.finiteAverage_pair]
  simp_rw [average_coordScore]
  unfold BPORS.finiteAverage BPORS.coordinateEnvelope
  simp only [Fintype.card_fin, Nat.cast_ofNat, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring
theorem average_at_index (X : List HashOutput) (i : Fin (2 ^ 31)) :
    BPORS.finiteAverage (fun v : Fin 7 → Fin 16 × (Fin 3 → Fin 128) =>
        ∏ c : Fin 7, coordScore X i c (v c).1 (v c).2)/8 =
      BPORS.History.wordEnvelope (BPORS.History.atIndex i (labels X)) := by
  rw [BPORS.finiteAverage_product 7
    (fun c (d : Fin 16 × (Fin 3 → Fin 128)) => coordScore X i c d.1 d.2)]
  simp_rw [average_coordinate]
  unfold BPORS.History.wordEnvelope
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv]
theorem average_score (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => score X N) = BPORS.History.fullPrice (labels X) / 2 ^ 128 := by
  change BPORS.finiteAverage (fun N : HashOutput => if digestGate N=true then
    (fun p : RawView => ∏ c : Fin 7, coordScore X p.1 c (p.2 c).1 (p.2 c).2) (rawView N) else 0)=_
  rw [average_gate_weight (fun p : RawView => ∏ c : Fin 7, coordScore X p.1 c (p.2 c).1 (p.2 c).2),
    BPORS.finiteAverage_pair,←finiteAverage_div]
  simp_rw [average_at_index]
  unfold BPORS.finiteAverage BPORS.History.fullPrice
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (2 ^ 97 : ENNReal), mul_assoc]
  congr 1
  rw [show (2 : ENNReal) ^ 128 = 2 ^ 97 * 2 ^ 31 by rw [← pow_add]]
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
end SigGolfCandidate.T3.Security.CaseC
end
