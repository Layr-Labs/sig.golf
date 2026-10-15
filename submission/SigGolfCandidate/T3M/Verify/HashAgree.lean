import SigGolfCandidate.T3M.Verify.HashOk

namespace SigGolfCandidate.T3M.Verify
open OracleComp OracleSpec SigGolfCandidate.Legacy
def Agree (f g : Hash) {α : Type} (oa : OracleComp HashSpec α) : Prop :=
  OracleComp.recOn oa (fun _ => True) (fun t _ ih => f t = g t ∧ ih (f t))
variable {f g : Hash}
theorem agree_pure {α : Type} (a : α) : Agree f g (pure a : OracleComp HashSpec α) := trivial
theorem agree_query_bind {α : Type} (q : Query) (k : BitVec 256 → OracleComp HashSpec α) :
    Agree f g ((liftM (HashSpec.query q) : OracleComp HashSpec _) >>= k) ↔ f q = g q ∧ Agree f g (k (f q)) :=
  Iff.rfl
theorem eval_liftQ (h : Hash) (q : Query) :
    evalWithAnswerFn h (liftM (OracleSpec.query q) : OracleComp HashSpec _) = h q := by
  simp [evalWithAnswerFn]
theorem agree_eval {α : Type} {oa : OracleComp HashSpec α} (h : Agree f g oa) :
    evalWithAnswerFn f oa = evalWithAnswerFn g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    obtain ⟨hq, hk⟩ : f q = g q ∧ Agree f g (k (f q)) := h
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_liftQ, eval_liftQ, ← hq]
    exact ih _ hk
theorem agree_bind_iff {α β : Type} (oa : OracleComp HashSpec α) (ob : α → OracleComp HashSpec β) :
    Agree f g (oa >>= ob) ↔ Agree f g oa ∧ Agree f g (ob (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind, evalWithAnswerFn_pure]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | query_bind q k ih =>
    rw [bind_assoc]
    show (f q = g q ∧ Agree f g (k (f q) >>= ob)) ↔ (f q = g q ∧ Agree f g (k (f q))) ∧ _
    rw [ih, evalWithAnswerFn_bind, eval_liftQ]
    tauto
theorem agree_bind {α β : Type} {oa : OracleComp HashSpec α} {ob : α → OracleComp HashSpec β}
    (h1 : Agree f g oa) (h2 : Agree f g (ob (evalWithAnswerFn f oa))) : Agree f g (oa >>= ob) :=
  (agree_bind_iff oa ob).mpr ⟨h1, h2⟩
theorem agree_map_iff {α β : Type} (h : α → β) (oa : OracleComp HashSpec α) :
    Agree f g (h <$> oa) ↔ Agree f g oa := by
  rw [map_eq_bind_pure_comp, agree_bind_iff]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', trivial⟩⟩
theorem agree_of_allQ {α : Type} {oa : OracleComp HashSpec α} (h : AllQueriesSatisfy oa (fun q => f q = g q)) :
    Agree f g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    exact ⟨h.1, ih _ (h.2 _)⟩
def BadAns (lay : T3.Layer) (a : BitVec 256) : Prop :=
  (∃ ds, T3.decode lay (a.extractLsb' 0 128) = some ds ∧
    ClaudeWCT.WCT9.wordCredit lay ds < ClaudeWCT.WCT9.producerFloor lay)
open Classical in
noncomputable def okHash (hash : Hash) : Hash :=
  fun q => if ∃ lay : T3.Layer, EncQ lay.val q ∧ BadAns lay (hash q) then BitVec.allOnes 256 else hash q
theorem okHash_eq (hash : Hash) {q : Query} (h : ¬ ∃ lay : T3.Layer, EncQ lay.val q ∧ BadAns lay (hash q)) :
    okHash hash q = hash q := by
  unfold okHash
  rw [if_neg h]
theorem okHash_eq_of_not_enc (hash : Hash) {q : Query} (h : ∀ lay : T3.Layer, ¬ EncQ lay.val q) :
    okHash hash q = hash q :=
  okHash_eq hash (fun ⟨lay, h', _⟩ => h lay h')
theorem decode_allOnes (lay : T3.Layer) : T3.decode lay ((BitVec.allOnes 256).extractLsb' 0 128) = none := by
  revert lay
  decide +kernel
theorem hashOk_okHash (hash : Hash) : HashOk (okHash hash) := by
  intro lay q hq ds hds
  by_cases hb : ∃ lay' : T3.Layer, EncQ lay'.val q ∧ BadAns lay' (hash q)
  · unfold okHash at hds
    rw [if_pos hb, decode_allOnes] at hds
    cases hds
  · rw [okHash_eq hash hb] at hds
    by_contra hc
    exact hb ⟨lay, hq, ds, hds, by omega⟩
end SigGolfCandidate.T3M.Verify
