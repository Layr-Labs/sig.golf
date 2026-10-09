import SigGolfCandidate.W9Machine.WctRoutineReady
import SigGolfCandidate.W9Machine.WctN600Contract

section


section
namespace W9Machine
instance chainWordLawfulBEq : LawfulBEq ChainWord := by
  refine { rfl := ?_, eq_of_beq := ?_ }
  · intro a
    cases a <;> simp [BEq.beq, instBEqChainWord.beq]
  · intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqChainWord.beq]
end W9Machine
end
section
namespace W9Machine.Chain
theorem ready_of_checks (rank : Fin 666) (r : ChainRoutine) (hrank : r.rank = rank.val)
    (hc : r.checked = true) (hg : planGuard r.pieces {} = true) (hl : PlanLinked r.pieces)
    (ht : terminalChecked r = true) : RoutineReady rank r := by
  have hcost := r.checked_cycles hc
  simp only [ChainRoutine.checked, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hd⟩, he⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  have hd' : r.digits = ClaudeWCT.WCT9.codeword rank := by
    rw [hrank] at hd
    have hb : rank.val < (ClaudeWCT.WCT9.compositions 5 6 7).length := by
      simpa only [ClaudeWCT.WCT9.codebook_card] using rank.isLt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb,
      Option.getD_some, ClaudeWCT.WCT9.codeword] using hd
  simp only [terminalChecked, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨hq, hend⟩, h720⟩, h728⟩ := ht
  refine ⟨hg, hl, by simpa only [hrank] using he, hq.trans (congrArg expectedQueries hd'),
    ?_, ⟨h720, h728⟩, (planCycles_eq r).trans_le hcost⟩
  intro t ht6 word hw2
  have h := List.all_eq_true.mp (List.all_eq_true.mp hend t (List.mem_range.mpr ht6))
    word (List.mem_range.mpr hw2)
  simpa only [beq_iff_eq, hd'] using h
end W9Machine.Chain
end
end

section


namespace W9Machine.N600
def exactChecked (r : ChainRoutine) (cost : Nat) : Bool :=
  r.checked && planGuard r.pieces {} && Chain.terminalChecked r &&
    (r.pieces.all fun p => sliceChecked p.pc p.words && p.checked) &&
    decide (planCycles r.pieces ≤ cost)
theorem ready_exact (rank : Fin 563) (r : ChainRoutine)
    (hrank : r.rank = (embed rank).val) (h : exactChecked r (rankCost rank) = true) :
    Chain.RoutineReady (embed rank) r ∧ planCycles r.pieces ≤ rankCost rank := by
  simp only [exactChecked, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hg⟩, ht⟩, hl⟩, hcost⟩ := h
  refine ⟨Chain.ready_of_checks _ _ hrank hc hg ?_ ht, hcost⟩
  intro p hp
  simpa only [Bool.and_eq_true] using (List.all_eq_true.mp hl p hp)
end W9Machine.N600
end
