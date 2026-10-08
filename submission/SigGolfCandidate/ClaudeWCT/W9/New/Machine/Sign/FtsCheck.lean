import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckA
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckB
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckC

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.T3M.Verify
theorem okCoord_all {c : Nat} (hc : c < 9) : okCoord c = true := by
  match c, hc with
  | 0, _ => exact okCoord_0
  | 1, _ => exact okCoord_1
  | 2, _ => exact okCoord_2
  | 3, _ => exact okCoord_3
  | 4, _ => exact okCoord_4
  | 5, _ => exact okCoord_5
  | 6, _ => exact okCoord_6
  | 7, _ => exact okCoord_7
  | 8, _ => exact okCoord_8
theorem okCoord_parts {c : Nat} (hc : c < 9) :
    okF c = true ∧ okC c = true ∧ okQ c = true ∧ okS c = true ∧ okChk c = true ∧ okStp c = true ∧
      okLc c = true ∧ okTail c = true := by
  have h := okCoord_all hc
  simp only [okCoord, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
theorem runF_eq {c : Nat} (hc : c < 9) : runF c = some (expF c) := by
  have h := (okCoord_parts hc).1
  simp only [okF, Bool.and_eq_true] at h
  exact optBeq_eq h.1
theorem runZ_eq {c : Nat} (hc : c < 9) : runZ c = some (expZ c) := by
  have h := (okCoord_parts hc).1
  simp only [okF, Bool.and_eq_true] at h
  exact optBeq_eq h.2
theorem runCL_eq {c : Nat} (hc : c < 9) (b : Bool) : runCL c b = some (expCL c b) := by
  have h := (okCoord_parts hc).2.1
  simp only [okC, Bool.and_eq_true] at h
  cases b
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem runQ_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runQ c i = some (expQ c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.1 i (List.mem_range.mpr hi))
theorem runS_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runS c i = some (expS c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.1 i (List.mem_range.mpr hi))
theorem runChk_eq {c i s v : Nat} (hc : c < 9) (hi : i < 6) (hs : s < 5) (hv : v < 3) :
    runChk c i s v = some (expChk c i s v) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.1 i
    (List.mem_range.mpr hi)) s (List.mem_range.mpr hs)) v (List.mem_range.mpr hv))
theorem runStp_eq {c i s : Nat} (hc : c < 9) (hi : i < 6) (hs1 : 1 ≤ s) (hs : s < 5) :
    runStp c i s = some (expStp c i s) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.1 i (List.mem_range.mpr hi)) s
    (List.mem_range'_1.mpr ⟨hs1, by omega⟩))
theorem runLc_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runLc c i = some (expLc c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.2.1 i (List.mem_range.mpr hi))
theorem okTail_parts {c : Nat} (hc : c < 9) :
    optBeq (runL c) (expL c) = true ∧ optBeq (runT c true) (expT c true) = true ∧
      optBeq (runT c false) (expT c false) = true ∧ optBeq (runN c) (expN c) = true ∧
      optBeq (runNT c true) (expNT c true) = true ∧ optBeq (runNT c false) (expNT c false) = true ∧
      optBeq (runR0 c) (expR0 c) = true ∧ ((List.range 7).all fun l => optBeq (runPC c l) (expPC c l)) = true := by
  have h := (okCoord_parts hc).2.2.2.2.2.2.2
  simp only [okTail, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
theorem runL_eq {c : Nat} (hc : c < 9) : runL c = some (expL c) := optBeq_eq (okTail_parts hc).1
theorem runT_eq {c : Nat} (hc : c < 9) (b : Bool) : runT c b = some (expT c b) := by
  cases b
  · exact optBeq_eq (okTail_parts hc).2.2.1
  · exact optBeq_eq (okTail_parts hc).2.1
theorem runN_eq {c : Nat} (hc : c < 9) : runN c = some (expN c) := optBeq_eq (okTail_parts hc).2.2.2.1
theorem runNT_eq {c : Nat} (hc : c < 9) (b : Bool) : runNT c b = some (expNT c b) := by
  cases b
  · exact optBeq_eq (okTail_parts hc).2.2.2.2.2.1
  · exact optBeq_eq (okTail_parts hc).2.2.2.2.1
theorem runR0_eq {c : Nat} (hc : c < 9) : runR0 c = some (expR0 c) := optBeq_eq (okTail_parts hc).2.2.2.2.2.2.1
theorem runPC_eq {c l : Nat} (hc : c < 9) (hl : l < 7) : runPC c l = some (expPC c l) :=
  optBeq_eq (List.all_eq_true.mp (okTail_parts hc).2.2.2.2.2.2.2 l (List.mem_range.mpr hl))
theorem okGlobal_parts : optBeq runSK expSK = true ∧ optBeq runFor expFor = true ∧ optBeq runJ expJ = true ∧
    okHorn = true := by
  have h := okGlobal_ok
  simp only [okGlobal, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
theorem okHorn_parts : optBeq runH0 expH0 = true ∧ optBeq runHK expHK = true ∧
    (∀ b1 b2, optBeq (runHB b1 b2) (expHB b1 b2) = true) ∧ ∀ b, optBeq (runHF b) (expHF b) = true := by
  have h := okGlobal_parts.2.2.2
  simp only [okHorn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, fun b1 b2 => ?_, fun b => ?_⟩
  · cases b1 <;> cases b2
    · exact h6
    · exact h5
    · exact h4
    · exact h3
  · cases b
    · exact h8
    · exact h7
theorem runH0_eq : runH0 = some expH0 := optBeq_eq okHorn_parts.1
theorem runHK_eq : runHK = some expHK := optBeq_eq okHorn_parts.2.1
theorem runHB_eq (b1 b2 : Bool) : runHB b1 b2 = some (expHB b1 b2) := optBeq_eq (okHorn_parts.2.2.1 b1 b2)
theorem runHF_eq (b : Bool) : runHF b = some (expHF b) := optBeq_eq (okHorn_parts.2.2.2 b)
theorem runSK_eq : runSK = some expSK := optBeq_eq okGlobal_parts.1
theorem runFor_eq : runFor = some expFor := optBeq_eq okGlobal_parts.2.1
theorem runJ_eq : runJ = some expJ := optBeq_eq okGlobal_parts.2.2.1
end ClaudeWCT.W9.Machine.Sign
