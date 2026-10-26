import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge061

-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheck ====
section

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
      optBeq (runNT c 0 true) (expNT c 0 true) = true ∧
      optBeq (runNT c (if c = 0 then 0 else 2) false) (expNT c (if c = 0 then 0 else 2) false) = true ∧
      optBeq (runNT c 1 true) (expNT c 1 true) = true ∧
      optBeq (runR0 c) (expR0 c) = true ∧ ((List.range 7).all fun l => optBeq (runPC c l) (expPC c l)) = true := by
  have h := (okCoord_parts hc).2.2.2.2.2.2.2
  simp only [okTail, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
theorem runL_eq {c : Nat} (hc : c < 9) : runL c = some (expL c) := optBeq_eq (okTail_parts hc).1
theorem runT_eq {c : Nat} (hc : c < 9) (b : Bool) : runT c b = some (expT c b) := by
  cases b
  · exact optBeq_eq (okTail_parts hc).2.2.1
  · exact optBeq_eq (okTail_parts hc).2.1
theorem runN_eq {c : Nat} (hc : c < 9) : runN c = some (expN c) := optBeq_eq (okTail_parts hc).2.2.2.1
theorem runNT_eq0 {c : Nat} (hc : c < 9) : runNT c 0 true = some (expNT c 0 true) :=
  optBeq_eq (okTail_parts hc).2.2.2.2.1
theorem runNT_eqX {c : Nat} (hc : c < 9) :
    runNT c (if c = 0 then 0 else 2) false = some (expNT c (if c = 0 then 0 else 2) false) :=
  optBeq_eq (okTail_parts hc).2.2.2.2.2.1
theorem runNT_eq1 {c : Nat} (hc : c < 9) : runNT c 1 true = some (expNT c 1 true) :=
  optBeq_eq (okTail_parts hc).2.2.2.2.2.2.1
theorem runR0_eq {c : Nat} (hc : c < 9) : runR0 c = some (expR0 c) := optBeq_eq (okTail_parts hc).2.2.2.2.2.2.2.1
theorem runPC_eq {c l : Nat} (hc : c < 9) (hl : l < 7) : runPC c l = some (expPC c l) :=
  optBeq_eq (List.all_eq_true.mp (okTail_parts hc).2.2.2.2.2.2.2.2 l (List.mem_range.mpr hl))
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

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.T3M.Verify
set_option maxRecDepth 100000
theorem leaf_run0 : runLeaf 0 = some (expected 0) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run1 : runLeaf 1 = some (expected 1) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run2 : runLeaf 2 = some (expected 2) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run3 : runLeaf 3 = some (expected 3) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run4 : runLeaf 4 = some (expected 4) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run5 : runLeaf 5 = some (expected 5) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run6 : runLeaf 6 = some (expected 6) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run7 : runLeaf 7 = some (expected 7) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run8 : runLeaf 8 = some (expected 8) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run {c : Nat} (hc:c<9) : runLeaf c = some (expected c) := by
  match c,hc with
  | 0,_ => exact leaf_run0
  | 1,_ => exact leaf_run1
  | 2,_ => exact leaf_run2
  | 3,_ => exact leaf_run3
  | 4,_ => exact leaf_run4
  | 5,_ => exact leaf_run5
  | 6,_ => exact leaf_run6
  | 7,_ => exact leaf_run7
  | 8,_ => exact leaf_run8
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
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
theorem okCoord_parts {c : Nat} (hc : c<9) :
  optBeq (runZ c) (expZ c) = true ∧ okC c=true ∧ okQ c=true ∧ okS c=true ∧
  okChk c=true ∧ okStp c=true ∧ okLc c=true := by
  have h := okCoord_all hc
  simp only [okCoord, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hz,hc⟩,hq⟩,hs⟩,hch⟩,hst⟩,hl⟩
  exact ⟨hz,hc,hq,hs,hch,hst,hl⟩
theorem runZ_eq {c : Nat} (hc : c<9) : runZ c = some (expZ c) := optBeq_eq (okCoord_parts hc).1
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
theorem okStp_at {c i s : Nat} (hc : c < 9) (hi : i < 6) (hs1 : 1 ≤ s) (hs : s < 5) :
    (if WCT9.ftsIsG i then optBeq (runStp c i s) (expStpG c i s) && optBeq (runPostG c i s) (expPostG c i s)
      else optBeq (runStp c i s) (expStp c i s)) = true :=
  List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.1 i (List.mem_range.mpr hi)) s
    (List.mem_range'_1.mpr ⟨hs1, by omega⟩)
theorem runStp_eq {c i s : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = false) (hs1 : 1 ≤ s) (hs : s < 5) :
    runStp c i s = some (expStp c i s) := by
  have h := okStp_at hc hi hs1 hs
  rw [hG, if_neg (by decide)] at h
  exact optBeq_eq h
theorem runStpG_eq {c i s : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = true) (hs1 : 1 ≤ s) (hs : s < 5) :
    runStp c i s = some (expStpG c i s) ∧ runPostG c i s = some (expPostG c i s) := by
  have h := okStp_at hc hi hs1 hs
  rw [hG, if_pos rfl, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1, optBeq_eq h.2⟩
set_option maxRecDepth 100000 in
theorem lwu_wordW : ∀ c, c < 9 → coordLookW c (lwuI c) = some 0x000e6c83 := by decide +kernel
theorem runLc_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runLc c i = some (expLc c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.2 i (List.mem_range.mpr hi))
theorem okHorn_parts : optBeq runH0 expH0 = true ∧ optBeq runHK expHK = true ∧
    (∀ b1 b2, optBeq (runHB b1 b2) (expHB b1 b2) = true) ∧ ∀ b, optBeq (runHF b) (expHF b) = true := by
  have h := okHorn_ok
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
end ClaudeWCT.W9.Machine.Sign.SharedReuse


set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.T3M.Verify
theorem node_run_0 : ∀ mode,mode<3 → optBeq (runNode 0 mode) (expected 0 mode)=true := by decide +kernel
theorem node_run_1 : ∀ mode,mode<3 → optBeq (runNode 1 mode) (expected 1 mode)=true := by decide +kernel
theorem node_run_2 : ∀ mode,mode<3 → optBeq (runNode 2 mode) (expected 2 mode)=true := by decide +kernel
theorem node_run_3 : ∀ mode,mode<3 → optBeq (runNode 3 mode) (expected 3 mode)=true := by decide +kernel
theorem node_run_4 : ∀ mode,mode<3 → optBeq (runNode 4 mode) (expected 4 mode)=true := by decide +kernel
theorem node_run_5 : ∀ mode,mode<3 → optBeq (runNode 5 mode) (expected 5 mode)=true := by decide +kernel
theorem node_run_6 : ∀ mode,mode<3 → optBeq (runNode 6 mode) (expected 6 mode)=true := by decide +kernel
theorem node_run_7 : ∀ mode,mode<3 → optBeq (runNode 7 mode) (expected 7 mode)=true := by decide +kernel
theorem node_run_8 : ∀ mode,mode<3 → optBeq (runNode 8 mode) (expected 8 mode)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem hook_run : ∀c,c<9 → optBeq (runHook c) (expectedHook c)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem next_run_0 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 0 mode odd) (expected 0 mode odd)=true := by decide +kernel
theorem next_run_1 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 1 mode odd) (expected 1 mode odd)=true := by decide +kernel
theorem next_run_2 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 2 mode odd) (expected 2 mode odd)=true := by decide +kernel
theorem next_run_3 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 3 mode odd) (expected 3 mode odd)=true := by decide +kernel
theorem next_run_4 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 4 mode odd) (expected 4 mode odd)=true := by decide +kernel
theorem next_run_5 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 5 mode odd) (expected 5 mode odd)=true := by decide +kernel
theorem next_run_6 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 6 mode odd) (expected 6 mode odd)=true := by decide +kernel
theorem next_run_7 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 7 mode odd) (expected 7 mode odd)=true := by decide +kernel
theorem next_run_8 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 8 mode odd) (expected 8 mode odd)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem tail_run_0 : ∀ k,k<4 → ∀ back,optBeq (runTail 0 k back) (expected 0 k back)=true := by decide +kernel
theorem tail_run_1 : ∀ k,k<4 → ∀ back,optBeq (runTail 1 k back) (expected 1 k back)=true := by decide +kernel
theorem tail_run_2 : ∀ k,k<4 → ∀ back,optBeq (runTail 2 k back) (expected 2 k back)=true := by decide +kernel
theorem tail_run_3 : ∀ k,k<4 → ∀ back,optBeq (runTail 3 k back) (expected 3 k back)=true := by decide +kernel
theorem tail_run_4 : ∀ k,k<4 → ∀ back,optBeq (runTail 4 k back) (expected 4 k back)=true := by decide +kernel
theorem tail_run_5 : ∀ k,k<4 → ∀ back,optBeq (runTail 5 k back) (expected 5 k back)=true := by decide +kernel
theorem tail_run_6 : ∀ k,k<4 → ∀ back,optBeq (runTail 6 k back) (expected 6 k back)=true := by decide +kernel
theorem tail_run_7 : ∀ k,k<4 → ∀ back,optBeq (runTail 7 k back) (expected 7 k back)=true := by decide +kernel
theorem tail_run_8 : ∀ k,k<4 → ∀ back,optBeq (runTail 8 k back) (expected 8 k back)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.T3M.Verify
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem finish_run_0 : optBeq (runFinish 0) (expected 0)=true := by decide +kernel
theorem finish_run_1 : optBeq (runFinish 1) (expected 1)=true := by decide +kernel
theorem finish_run_2 : optBeq (runFinish 2) (expected 2)=true := by decide +kernel
theorem finish_run_3 : optBeq (runFinish 3) (expected 3)=true := by decide +kernel
theorem finish_run_4 : optBeq (runFinish 4) (expected 4)=true := by decide +kernel
theorem finish_run_5 : optBeq (runFinish 5) (expected 5)=true := by decide +kernel
theorem finish_run_6 : optBeq (runFinish 6) (expected 6)=true := by decide +kernel
theorem finish_run_7 : optBeq (runFinish 7) (expected 7)=true := by decide +kernel
theorem finish_run_8 : optBeq (runFinish 8) (expected 8)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem path_run_0 : ∀ level,level<levels 0 → optBeq (runPath 0 level) (expected 0 level)=true := by decide +kernel
theorem path_run_1 : ∀ level,level<levels 1 → optBeq (runPath 1 level) (expected 1 level)=true := by decide +kernel
theorem path_run_2 : ∀ level,level<levels 2 → optBeq (runPath 2 level) (expected 2 level)=true := by decide +kernel
theorem path_run_3 : ∀ level,level<levels 3 → optBeq (runPath 3 level) (expected 3 level)=true := by decide +kernel
theorem path_run_4 : ∀ level,level<levels 4 → optBeq (runPath 4 level) (expected 4 level)=true := by decide +kernel
theorem path_run_5 : ∀ level,level<levels 5 → optBeq (runPath 5 level) (expected 5 level)=true := by decide +kernel
theorem path_run_6 : ∀ level,level<levels 6 → optBeq (runPath 6 level) (expected 6 level)=true := by decide +kernel
theorem path_run_7 : ∀ level,level<levels 7 → optBeq (runPath 7 level) (expected 7 level)=true := by decide +kernel
theorem path_run_8 : ∀ level,level<levels 8 → optBeq (runPath 8 level) (expected 8 level)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem end_run_0 : optBeq (runEnd 0) (expected 0)=true := by decide +kernel
theorem end_run_1 : optBeq (runEnd 1) (expected 1)=true := by decide +kernel
theorem end_run_2 : optBeq (runEnd 2) (expected 2)=true := by decide +kernel
theorem end_run_3 : optBeq (runEnd 3) (expected 3)=true := by decide +kernel
theorem end_run_4 : optBeq (runEnd 4) (expected 4)=true := by decide +kernel
theorem end_run_5 : optBeq (runEnd 5) (expected 5)=true := by decide +kernel
theorem end_run_6 : optBeq (runEnd 6) (expected 6)=true := by decide +kernel
theorem end_run_7 : optBeq (runEnd 7) (expected 7)=true := by decide +kernel
theorem end_run_8 : optBeq (runEnd 8) (expected 8)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem field_run_0 : optBeq (runField 0) (expected 0)=true := by decide +kernel
theorem field_run_1 : optBeq (runField 1) (expected 1)=true := by decide +kernel
theorem field_run_2 : optBeq (runField 2) (expected 2)=true := by decide +kernel
theorem field_run_3 : optBeq (runField 3) (expected 3)=true := by decide +kernel
theorem field_run_4 : optBeq (runField 4) (expected 4)=true := by decide +kernel
theorem field_run_5 : optBeq (runField 5) (expected 5)=true := by decide +kernel
theorem field_run_6 : optBeq (runField 6) (expected 6)=true := by decide +kernel
theorem field_run_7 : optBeq (runField 7) (expected 7)=true := by decide +kernel
theorem field_run_8 : optBeq (runField 8) (expected 8)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
def globalCheck (m : Bool) : Bool :=
  optBeq (run (look m) [trial m+3,fail m] (trial m) [.br false]) (expectedHead m false) &&
  optBeq (run (look m) [trial m+3,fail m] (trial m) [.br true]) (expectedHead m true) &&
  optBeq (run (look m) [] (trial m+3) []) (expectedTrial m) &&
  optBeq (run (look m) [next m,base m+21] (base m+15) [.br false]) (expectedGate m false) &&
  optBeq (run (look m) [next m,base m+21] (base m+15) [.br true]) (expectedGate m true) &&
  optBeq (run (look m) [firstField m] (base m+21) []) (expectedInit m) &&
  optBeq (run (look m) [next m,accepted m] (cap m) [.br false]) (expectedCap m false) &&
  optBeq (run (look m) [next m,accepted m] (cap m) [.br true]) (expectedCap m true) &&
  optBeq (run (look m) [trial m] (next m) []) (expectedNext m)
def fieldCheck (m : Bool) (k : Nat) : Bool :=
  optBeq (run (look m) [next m,field m k+5] (field m k) [.br false]) (expectedRank m k false) &&
  optBeq (run (look m) [next m,field m k+5] (field m k) [.br true]) (expectedRank m k true) &&
  optBeq (run (look m) [rankLoad m k] (field m k+5) []) (expectedRankAddr m k) &&
  optBeq (run (look m) [corrLoad m k] (rankLoad m k+1) []) (expectedCorrPrep m k) &&
  optBeq (run (look m) [field m (k+1)] (corrLoad m k+1) []) (expectedSum m k) &&
  (look m (rankLoad m k)==some (rankLbuWord m)) &&
  (look m (corrLoad m k)==some (corrLbuWord m k))
theorem global_sign : globalCheck false=true := by decide +kernel
theorem global_expand : globalCheck true=true := by decide +kernel
theorem fields_sign : (List.range 9).all (fieldCheck false)=true := by decide +kernel
theorem fields_expand : (List.range 9).all (fieldCheck true)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedDigest
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsBase ====
section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
section pres
variable (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k : Nat)
  (brs : List Br) (s : MachineState)
theorem pres_pc : ((pres regs mem obl pc ec k brs).toState s).pc = pcOf pc := rfl
theorem pres_getReg (x : Reg) :
    ((pres regs mem obl pc ec k brs).toState s).getReg x = ((regsOf regs).get x).eval s :=
  SymState.toState_getReg _ _ _ _
theorem pres_getMem (a : Word) : ((pres regs mem obl pc ec k brs).toState s).getMem a = memEval s mem a := rfl
theorem pres_steps : (pres regs mem obl pc ec k brs).steps = k := rfl
theorem pres_cycles : (pres regs mem obl pc ec k brs).cycles = k := rfl
theorem pres_ecall : (pres regs mem obl pc ec k brs).ecall = ec := rfl
theorem pres_obl : (pres regs mem obl pc ec k brs).st.obl = obl := rfl
theorem pres_brs : (pres regs mem obl pc ec k brs).brs = brs := rfl
theorem pres2_getMem (cyc : Nat) (a : Word) : ((pres2 regs mem obl pc ec k cyc brs).toState s).getMem a = memEval s mem a := rfl
theorem pres2_getReg (cyc : Nat) (x : Reg) :
    ((pres2 regs mem obl pc ec k cyc brs).toState s).getReg x = ((regsOf regs).get x).eval s :=
  SymState.toState_getReg _ _ _ _
end pres
theorem foldl_set_get_ne (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    ∀ rf : RegFile, (l.foldl (fun rf p => rf.set p.1 p.2) rf).get x = rf.get x := by
  induction l with
  | nil => intro rf; rfl
  | cons p l ih =>
    intro rf
    simp only [List.foldl_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)), RegFile.get_set_ne _ _ (fun he => h p (by simp) he.symm)]
theorem regsOf_get_ne (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    (regsOf l).get x = RegFile.init.get x := foldl_set_get_ne l x h _
theorem pres_regsExcept (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k : Nat)
    (brs : List Br) (s : MachineState) :
    RegsExcept s ((pres regs mem obl pc ec k brs).toState s) (regs.map Prod.fst) := by
  intro x hx
  rw [pres_getReg, regsOf_get_ne _ _ (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]
theorem pres2_regsExcept (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool)
    (k cyc : Nat) (brs : List Br) (s : MachineState) :
    RegsExcept s ((pres2 regs mem obl pc ec k cyc brs).toState s) (regs.map Prod.fst) := by
  intro x hx
  rw [pres2_getReg, regsOf_get_ne _ _ (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]
theorem memEval_mwc (s : MachineState) (a A : Nat) (e : E) (ws : SymMem) (hA : A < 2 ^ 64) (ha : a < 2 ^ 64) :
    memEval s (mwc a e :: ws) (BitVec.ofNat 64 A) = if A = a then e.eval s else memEval s ws (BitVec.ofNat 64 A) :=
  memEval_cons_ofNat s a A e ws hA ha
theorem memEval_nil' (s : MachineState) (a : Word) : memEval s [] a = s.getMem a := rfl
set_option maxRecDepth 100000 in
theorem pathIdx_eq : ∀ sel, sel < 128 → ∀ l, l < 7 → (sel + 128) / 2 ^ l ^^^ 1 = 2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) := by
  decide +kernel
theorem ofNat_or_hi (lo hi : Nat) (hlo : lo < 2 ^ 32) :
    BitVec.ofNat 64 (hi * 2 ^ 32) ||| BitVec.ofNat 64 lo = BitVec.ofNat 64 (lo + 2 ^ 32 * hi) := by
  rw [ofNat_or_add lo hi 32 hlo]; congr 1; ring
theorem eval_bin (s : MachineState) (op : BinOp) (a b : E) : (E.bin op a b).eval s = op.eval (a.eval s) (b.eval s) :=
  rfl
theorem eval_cE (s : MachineState) (n : Nat) : (cE n).eval s = BitVec.ofNat 64 n := rfl
theorem binop_sll (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .sll x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem binop_srl (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem ofNat_shl_lt (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := ofNat_shl a k
theorem eval_w1E (s : MachineState) {j index : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    w1E.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * j) := by
  show BinOp.eval .or (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [binop_sll _ _ (by norm_num), h18, h22, ofNat_shl]
  exact ofNat_or_hi index j hidx
theorem ofNat_and_one (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, toNat_ofNat_lt (by norm_num), toNat_ofNat_lt (by omega),
    Nat.and_one_is_mod]
theorem eval_dE (s : MachineState) {w : Nat} (i : Nat) (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64)
    (hi : 3 * i < 64) (hd : w / 8 ^ i % 8 ≤ 4) : (dE i).eval s = BitVec.ofNat 64 (4 - w / 8 ^ i % 8) := by
  show BinOp.eval .sub (BitVec.ofNat 64 4) (BinOp.eval .and (BinOp.eval .srl (s.getReg .x25)
    (BitVec.ofNat 64 (3 * i))) (BitVec.ofNat 64 7)) = _
  rw [binop_srl _ _ hi, h25]
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Nat) ^ i = 2 ^ (3 * i) := by rw [pow_mul]; norm_num
  simp only [BinOp.eval, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hw, ← h8]
  have e : w / 8 ^ i &&& 7 = w / 8 ^ i % 8 := by
    rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (show 7 < 2 ^ 64 by norm_num), e]
  omega
theorem eval_x18p1 (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    x18p1.eval s = BitVec.ofNat 64 (j + 1) := by
  show s.getReg .x18 + BitVec.ofNat 64 1 = _
  rw [h18, ofNat_add_ofNat]
theorem eval_x18m1 (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hh : 1 ≤ h)
    (hh' : h < 2 ^ 64) : x18m1.eval s = BitVec.ofNat 64 (h - 1) := by
  show s.getReg .x18 + BitVec.ofNat 64 (2 ^ 64 - 1) = _
  rw [h18, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem eval_sll_reg (s : MachineState) {x : Reg} {a : Nat} (hx : s.getReg x = BitVec.ofNat 64 a) (k : Nat)
    (hk : k < 64) : (E.bin .sll (.reg x) (cE k)).eval s = BitVec.ofNat 64 (a * 2 ^ k) := by
  show BinOp.eval .sll (s.getReg x) (BitVec.ofNat 64 k) = _
  rw [binop_sll _ _ hk, hx, ofNat_shl]
theorem eval_sh5 (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    sh5.eval s = BitVec.ofNat 64 (32 * h) := by
  rw [sh5, eval_sll_reg s h18 5 (by norm_num)]; congr 1; ring
theorem eval_sh4 (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    sh4.eval s = BitVec.ofNat 64 (16 * h) := by
  rw [sh4, eval_sll_reg s h18 4 (by norm_num)]; congr 1; ring
theorem eval_heapLeafE (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    heapLeafE.eval s = BitVec.ofNat 64 (16 * (j + 128)) := by
  show BinOp.eval .sll (s.getReg .x18 + BitVec.ofNat 64 128) (BitVec.ofNat 64 4) = _
  rw [binop_sll _ _ (by norm_num), h18, ofNat_add_ofNat, ofNat_shl,
    show (j + 128) * 2 ^ 4 = 16 * (j + 128) by ring]
theorem eval_pathE (s : MachineState) {sel : Nat} (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (hsel : sel < 128)
    (l : Nat) (hl : l < 7) : (pathE l).eval s = BitVec.ofNat 64 (16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1))) := by
  show BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .srl (s.getReg .x24 + BitVec.ofNat 64 128) (BitVec.ofNat 64 l))
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 4) = _
  rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by omega), h24, ofNat_add_ofNat,
    ofNat_shr _ _ (by omega)]
  simp only [BinOp.eval]
  rw [show BitVec.ofNat 64 ((sel + 128) / 2 ^ l) ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 ((sel + 128) / 2 ^ l ^^^ 1) by
    apply BitVec.eq_of_toNat_eq
    have h1 : (sel + 128) / 2 ^ l < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have h2 : (sel + 128) / 2 ^ l ^^^ 1 < 2 ^ 64 := Nat.xor_lt_two_pow h1 (by norm_num)
    simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2],
    pathIdx_eq sel hsel l hl, ofNat_shl]
  congr 1; ring
theorem chainK_lt (c i : Nat) (hc : c < 9) (hi : i < 6) : chainK c i < 2 ^ 20 := by unfold chainK; omega
theorem eval_qE (s : MachineState) {c i j index : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128) (hk : chainK c i < 2 ^ 20) :
    (qE c i).eval s = BitVec.ofNat 64 (index * 2 ^ 27 + j * 2 ^ 20 + chainK c i) := by
  show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (s.getReg .x22) (BitVec.ofNat 64 27))
    (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 20))) (BitVec.ofNat 64 (chainK c i)) = _
  rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), h18, h22, ofNat_shl, ofNat_shl]
  simp only [BinOp.eval]
  rw [ofNat_or_add (j * 2 ^ 20) index 27 (by omega),
    show index * 2 ^ 27 + j * 2 ^ 20 = (index * 2 ^ 7 + j) * 2 ^ 20 by ring,
    ofNat_or_add (chainK c i) (index * 2 ^ 7 + j) 20 hk]
theorem nodeK_lt (c : Nat) (hc : c < 9) : nodeK c < 2 ^ 32 := by unfold nodeK; omega
theorem eval_nodeHiE (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hh : h < 128) :
    nodeHiE.eval s = BitVec.ofNat 64 (if 8 ≤ h then 0 else h) := by
  show BinOp.eval .mul (BinOp.eval .sltu (s.getReg .x18) (BitVec.ofNat 64 8)) (s.getReg .x18) = _
  rw [h18]
  simp only [BinOp.eval]
  have hu : BitVec.ult (BitVec.ofNat 64 h) (BitVec.ofNat 64 8) = decide (h < 8) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show h < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 < 2 ^ 64 by norm_num)]
  rw [hu]
  by_cases h8 : h < 8
  · have : ¬ 8 ≤ h := by omega
    simp [h8, this]
  · have : 8 ≤ h := by omega
    simp [h8, this]
theorem eval_nodeLoE (s : MachineState) {c index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hc : c < 9) (_hidx : index < 2 ^ 31) :
    (nodeLoE c).eval s = BitVec.ofNat 64 (nodeLo7 c index) := by
  unfold nodeLoE nodeLo7
  show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (s.getReg .x22) (BitVec.ofNat 64 27))
    (BitVec.ofNat 64 (65536 * (c + 1)))) (BitVec.ofNat 64 1537) = _
  rw [binop_sll _ _ (by norm_num), h22, ofNat_shl]
  simp only [BinOp.eval]
  rw [ofNat_or_disjoint (65536 * (c + 1)) (index * 2 ^ 27) 27 (by omega) (by omega),
    ofNat_or_disjoint 1537 (index * 2 ^ 27 + 65536 * (c + 1)) 16 (by norm_num) (by omega)]
  exact congrArg (BitVec.ofNat 64) (by ring)
/-- Packed FTS node low word: `nodeLo7 - h` for heaps `8..127`, `nodeLo7` below. -/
def nodeLoN (c index h : Nat) : Nat := if 8 ≤ h then nodeLo7 c index - h else nodeLo7 c index
theorem eval_nodeLoNE (s : MachineState) {c index h : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hc : c < 9) (hidx : index < 2 ^ 31) (hh : h < 128) :
    (nodeLoNE c).eval s = BitVec.ofNat 64 (nodeLoN c index h) := by
  show BinOp.eval .add ((nodeLoE c).eval s) (BinOp.eval .sub (nodeHiE.eval s) (s.getReg .x18)) = _
  rw [eval_nodeLoE s h22 hc hidx, eval_nodeHiE s h18 hh, h18]
  simp only [BinOp.eval]
  have hlo : 1537 ≤ nodeLo7 c index ∧ nodeLo7 c index < 2 ^ 64 := by unfold nodeLo7; omega
  unfold nodeLoN
  apply BitVec.eq_of_toNat_eq
  by_cases h8 : 8 ≤ h
  · rw [if_pos h8, if_pos h8]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hlo.2, Nat.mod_eq_of_lt (show h < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show nodeLo7 c index - h < 2 ^ 64 by omega)]
    omega
  · rw [if_neg h8, if_neg h8]
    simp only [BitVec.sub_self, BitVec.add_zero]
theorem eval_leafLoE (s : MachineState) {c index j : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (hc : c < 9) (hj : j < 128) :
    (leafLoE c).eval s = BitVec.ofNat 64 (leafLo7 c index j) := by
  unfold leafLoE leafLo7
  by_cases h0 : c = 0
  · subst h0
    rw [if_pos rfl]
    show BinOp.eval .or (BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (s.getReg .x22) (BitVec.ofNat 64 27))
      (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 20))) (BitVec.ofNat 64 65536)) (BitVec.ofNat 64 1537) = _
    rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), h22, h18, ofNat_shl, ofNat_shl]
    simp only [BinOp.eval]
    rw [ofNat_or_disjoint (j * 2 ^ 20) (index * 2 ^ 27) 27 (by omega) (by omega),
      ofNat_or_disjoint 65536 (index * 2 ^ 27 + j * 2 ^ 20) 20 (by omega) (by omega),
      ofNat_or_disjoint 1537 (index * 2 ^ 27 + j * 2 ^ 20 + 65536) 16 (by omega) (by omega)]
    congr 1; ring
  · rw [if_neg h0]
    show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (s.getReg .x22) (BitVec.ofNat 64 27))
      (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 20))) (BitVec.ofNat 64 (1537 + 65536 * (c + 1))) = _
    rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), h22, h18, ofNat_shl, ofNat_shl]
    simp only [BinOp.eval]
    rw [ofNat_or_disjoint (j * 2 ^ 20) (index * 2 ^ 27) 27 (by omega) (by omega),
      ofNat_or_disjoint (1537 + 65536 * (c + 1)) (index * 2 ^ 27 + j * 2 ^ 20) 20 (by omega) (by omega)]
    congr 1; ring
theorem replaceByte_toNat8 (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def physical (c j : Nat) : Nat := if first c then j else j/2+64*(j%2)
def padBase (c j : Nat) : Nat := if c%2=1 then 0x67000+64*(c/2)+32*(j%2) else FORW+32*c
def PadAt (c j : Nat) (pad : Digest) (s : MachineState) : Prop :=
  if c=0 then pad=0 else DigAt s (padBase c j) pad

theorem branchShift_eval (s : MachineState) {j : Nat} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) (k : Nat) (hk:k<64) :
    (branchShift k).eval s = BitVec.ofNat 64 ((j%2)*2^k) := by
  unfold branchShift branchE
  change BinOp.eval .sll (BinOp.eval .and (s.getReg .x18) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 k) = _
  rw [binop_sll _ _ hk, h18]
  change (BitVec.ofNat 64 j &&& BitVec.ofNat 64 1) <<< k = _
  rw [ofNat_and_one j (by omega),ofNat_shl]

theorem physicalE_eval (s : MachineState) {c j : Nat} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    (physicalE c).eval s = BitVec.ofNat 64 (physical c j) := by
  unfold physicalE physical
  split
  · exact h18
  · rw [eval_bin, branchShift_eval s hj h18 6 (by decide)]
    change ((E.bin .srl (.reg .x18) (cE 1)).eval s) + BitVec.ofNat 64 ((j%2)*2^6) = _
    rw [eval_bin,eval_cE]
    change BinOp.eval .srl (s.getReg .x18) (BitVec.ofNat 64 1) + _ = _
    rw [binop_srl _ _ (by decide),h18,ofNat_shr _ _ (by omega),ofNat_add_ofNat]
    congr 1
    norm_num
    omega

theorem outOffset_eval (s : MachineState) {c j : Nat} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    (outOffset c).eval s = BitVec.ofNat 64 (16*(128+physical c j)) := by
  unfold outOffset
  rw [eval_bin,eval_cE,binop_sll _ _ (by decide),eval_bin,physicalE_eval s hj h18,eval_cE]
  change (BitVec.ofNat 64 (physical c j)+BitVec.ofNat 64 128) <<< 4 = _
  rw [ofNat_add_ofNat,ofNat_shl]
  congr 1
  ring

theorem padAddr_eval (s : MachineState) {c j : Nat} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) (off : Nat) :
    (padAddr c off).eval s = BitVec.ofNat 64 (padBase c j+off) := by
  unfold padAddr padBase
  split
  · rw [eval_bin,branchShift_eval s hj h18 5 (by decide),eval_cE]
    change BitVec.ofNat 64 ((j%2)*2^5)+BitVec.ofNat 64 (0x67000+64*(c/2)+off) = _
    rw [ofNat_add_ofNat]
    congr 1
    ring
  · rfl

theorem padLoad_eval (s : MachineState) {c j : Nat} {pad : Digest} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) (hp:PadAt c j pad s) :
    (padLoad c 0).eval s=pad.extractLsb' 0 64 ∧ (padLoad c 8).eval s=pad.extractLsb' 64 64 := by
  unfold PadAt at hp
  unfold padLoad
  by_cases h0:c=0
  · simp only [if_pos h0] at hp ⊢
    subst pad
    exact ⟨rfl,rfl⟩
  · simp only [if_neg h0] at hp ⊢
    change s.getMem ((padAddr c 0).eval s) = _ ∧ s.getMem ((padAddr c 8).eval s) = _
    rw [padAddr_eval s hj h18,padAddr_eval s hj h18,Nat.add_zero]
    exact hp

theorem headerE_eval (s : MachineState) {c j index : Nat}
    (h18:s.getReg .x18=BitVec.ofNat 64 j) (h22:s.getReg .x22=BitVec.ofNat 64 index) :
    (headerE c).eval s = BitVec.ofNat 64 (leafLo7 c index j) := by
  unfold headerE
  rw [eval_bin,eval_bin,eval_sll_reg s h22 27 (by decide),eval_sll_reg s h18 20 (by decide),eval_cE]
  change (BitVec.ofNat 64 (index*2^27)+BitVec.ofNat 64 (j*2^20))+BitVec.ofNat 64 (1537+65536*(c+1)) = _
  rw [ofNat_add_ofNat,ofNat_add_ofNat]
  congr 1
  unfold leafLo7
  ring

end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def mode (h : Nat) : Nat := if 8≤h then 0 else if 4≤h then 1 else 2
theorem mode_lt (h : Nat) : mode h<3 := by unfold mode;split_ifs <;> omega
theorem mode_one {h : Nat} (hm:mode h=1) : 4≤h ∧ h<8 := by unfold mode at hm;split_ifs at hm <;> omega

def padBase (c h : Nat) : Nat := if c%2=1 then 0x67000+64*(c/2)+16+32*(h/2-2) else FORW+32*c+16
def PadAt (c h : Nat) (pad : Digest) (s : MachineState) : Prop :=
  if mode h=1 ∧ c≠0 then DigAt s (padBase c h) pad else pad=0

theorem loE_eval (s : MachineState) {c index : Nat} (h22:s.getReg .x22=BitVec.ofNat 64 index) :
    (loE c).eval s=BitVec.ofNat 64 (nodeLo7 c index) := by
  unfold loE
  rw[eval_bin,eval_bin,eval_cE,binop_sll _ _ (by decide)]
  change ((s.getReg .x22) <<< 27)+BitVec.ofNat 64 (1537+65536*(c+1))=_
  rw[h22,ofNat_shl,ofNat_add_ofNat]
  congr 1
  unfold nodeLo7
  ring

theorem hdrLo_eval (s : MachineState) {c index h : Nat}
    (h22:s.getReg .x22=BitVec.ofNat 64 index) (h18:s.getReg .x18=BitVec.ofNat 64 h)
    (hc:c<9) (hi:index<2^31) (hh:h<128) :
    (hdrLo c (mode h)).eval s=BitVec.ofNat 64 (nodeLoN c index h) := by
  by_cases h8:8≤h
  · have hm:mode h=0:=by simp only[mode,if_pos h8]
    rw[hdrLo,if_pos hm,nodeLoN,if_pos h8,eval_bin,loE_eval s h22]
    change BitVec.ofNat 64 (nodeLo7 c index)-s.getReg .x18=_
    rw[h18]
    have hlo:1537≤nodeLo7 c index ∧ nodeLo7 c index<2^64:=by unfold nodeLo7;omega
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  · have hm:mode h≠0:=by unfold mode;split_ifs <;> omega
    rw[hdrLo,if_neg hm,nodeLoN,if_neg h8]
    exact loE_eval s h22

theorem hdrHi_eval (s : MachineState) {h : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) :
    (hdrHi (mode h)).eval s=BitVec.ofNat 64 (if 8≤h then 0 else h) := by
  by_cases h8:8≤h
  · have hm:mode h=0:=by simp only[mode,if_pos h8]
    rw[hdrHi,if_pos hm,if_pos h8]
    rfl
  · have hm:mode h≠0:=by unfold mode;split_ifs <;> omega
    rw[hdrHi,if_neg hm,if_neg h8]
    exact h18

theorem padShift_eval (s : MachineState) {h : Nat} (h4:4≤h) (h8:h<8)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : padShift.eval s=BitVec.ofNat 64 (32*(h/2-2)) := by
  unfold padShift
  rw[eval_bin,eval_cE,binop_sll _ _ (by decide),eval_bin,eval_bin,eval_cE,binop_srl _ _ (by decide)]
  change (((s.getReg .x18 >>> 1)+BitVec.ofNat 64 (2^64-2)) <<< 5)=_
  rw[h18,ofNat_shr _ _ (by omega),ofNat_add_ofNat]
  have he:BitVec.ofNat 64 (h/2+(2^64-2))=BitVec.ofNat 64 (h/2-2):=by
    apply BitVec.eq_of_toNat_eq
    simp only[BitVec.toNat_ofNat]
    omega
  change (BitVec.ofNat 64 (h/2+(2^64-2)) <<< 5)=_
  rw[he,ofNat_shl]
  congr 1
  ring

theorem padAddr_eval (s : MachineState) {c h : Nat} (h4:4≤h) (h8:h<8)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) (off : Nat) :
    (padAddr c off).eval s=BitVec.ofNat 64 (padBase c h+off) := by
  unfold padAddr padBase
  split
  · rw[eval_bin,padShift_eval s h4 h8 h18,eval_cE]
    change BitVec.ofNat 64 (32*(h/2-2))+BitVec.ofNat 64 (0x67000+64*(c/2)+16+off)=_
    rw[ofNat_add_ofNat]
    congr 1
    ring
  · rfl

theorem padWord_eval (s : MachineState) {c h : Nat} {pad : Digest}
    (h18:s.getReg .x18=BitVec.ofNat 64 h) (hp:PadAt c h pad s) :
    (padWord c (mode h) 0).eval s=pad.extractLsb' 0 64 ∧
    (padWord c (mode h) 8).eval s=pad.extractLsb' 64 64 := by
  unfold PadAt at hp
  unfold padWord
  split_ifs at hp ⊢ with hm
  · have hh:=mode_one hm.1
    change s.getMem ((padAddr c 0).eval s)=_ ∧ s.getMem ((padAddr c 8).eval s)=_
    rw[padAddr_eval s hh.1 hh.2 h18,padAddr_eval s hh.1 hh.2 h18,Nat.add_zero]
    exact hp
  · subst pad
    exact ⟨rfl,rfl⟩
end ClaudeWCT.W9.Machine.Sign.SharedNode
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsTableCheck ====
section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-- Packed codeword table of the N563fix subcode (campaign T8E; T8 layout): word `r` of `WCT9.codeWords` (rank = field), digit `t`
in bits `3t .. 3t+2`. -/
def pk : List Nat := [143360,114688,139776,111104,82432,136192,107520,78848,50176,132608,103936,75264,46592,17920,100352,71680,43008,14336,139328,110656,81984,135744,107072,78400,49728,132160,103488,74816,46144,17472,99904,71232,42560,13888,67648,38976,10304,135296,106624,77952,49280,131712,103040,74368,45696,17024,99456,70784,42112,13440,67200,38528,9856,34944,6272,131264,102592,73920,45248,16576,99008,70336,41664,12992,66752,38080,9408,34496,5824,2240,98560,69888,41216,12544,66304,37632,8960,34048,5376,1792,139272,110600,81928,135688,107016,78344,49672,132104,103432,74760,46088,17416,99848,71176,42504,13832,67592,38920,10248,135240,106568,77896,49224,131656,102984,45640,16968,99400,13384,67144,38472,9800,34888,6216,131208,102536,73864,45192,16520,98952,12936,66696,9352,34440,5768,2184,98504,69832,41160,12488,66248,37576,8904,33992,5320,1736,65800,37128,8456,33544,4872,1288,135184,106512,77840,49168,131600,102928,74256,45584,16912,99344,70672,42000,13328,67088,38416,9744,34832,6160,131152,102480,73808,45136,16464,98896,12880,66640,9296,34384,5712,2128,98448,69776,41104,12432,66192,8848,33936,5264,1680,65744,37072,8400,33488,4816,1232,33040,4368,784,131096,102424,73752,45080,16408,98840,70168,41496,12824,66584,37912,9240,34328,5656,2072,98392,69720,41048,12376,66136,37464,8792,33880,5208,1624,65688,37016,8344,33432,4760,1176,32984,4312,728,280,98336,69664,40992,12320,66080,37408,8736,33824,5152,1568,65632,36960,8288,33376,4704,1120,32928,4256,672,224,139265,110593,81921,135681,107009,78337,49665,132097,103425,74753,46081,17409,99841,71169,42497,13825,67585,38913,10241,135233,106561,77889,49217,131649,102977,45633,16961,99393,13377,67137,38465,9793,34881,6209,131201,102529,73857,45185,16513,98945,12929,66689,9345,34433,5761,2177,98497,69825,41153,12481,66241,37569,8897,33985,5313,1729,65793,37121,8449,33537,4865,1281,135177,106505,77833,49161,131593,16905,99337,34825,6153,131145,16457,12873,34377,2121,98441,12425,1673,65737,37065,8393,1225,33033,4361,777,131089,102417,73745,45073,16401,12817,34321,5649,2065,98385,1617,65681,1169,32977,721,273,98329,69657,40985,12313,37401,8729,33817,5145,1561,65625,8281,1113,32921,665,217,65569,36897,8225,33313,4641,1057,32865,4193,609,161,135170,106498,77826,49154,131586,102914,74242,45570,16898,99330,70658,41986,13314,67074,38402,9730,34818,6146,131138,102466,73794,45122,16450,98882,12866,66626,9282,34370,5698,2114,98434,69762,41090,12418,66178,8834,33922,5250,1666,65730,37058,8386,33474,4802,1218,33026,4354,770,131082,102410,73738,45066,16394,12810,34314,2058,98378,12362,1610,65674,1162,32970,4298,714,266,98322,69650,40978,12306,8722,33810,1554,65618,1106,32914,658,210,65562,36890,8218,33306,4634,1050,32858,4186,602,154,32802,4130,546,98,131075,102403,73731,45059,16387,98819,70147,41475,12803,66563,37891,9219,34307,5635,2051,98371,69699,41027,12355,66115,37443,8771,33859,5187,1603,65667,36995,8323,33411,4739,1155,32963,4291,707,259,98315,69643,40971,12299,37387,8715,33803,1547,65611,8267,4683,1099,32907,4235,651,203,65555,36883,8211,33299,4627,1043,32851,595,147,32795,4123,539,91,35,98308,69636,40964,12292,66052,37380,8708,33796,5124,1540,65604,36932,8260,33348,4676,1092,32900,4228,644,196,65548,36876,8204,33292,4620,1036,32844,4172,588,140,32788,4116,532,84,28]
def pkAt (v : Nat) : Nat := if v < 563 then pk.getD v 0 else 0
def packW (w : List Nat) : Nat := (List.range 6).foldl (fun acc i => acc + w.getD i 0 * 8 ^ i) 0
theorem pk_eq : WCT9.codeWords.map packW = pk := by decide +kernel
theorem pk_length : pk.length = 563 := by decide +kernel
set_option maxRecDepth 100000 in
theorem pk_digits_all : (WCT9.codeWords.zip pk).all
    (fun p => (List.range 6).all fun i => p.2 / 8 ^ i % 8 == p.1.getD i 0) = true := by decide +kernel
def tblChk : Nat → List (BitVec 8) → Bool
  | k, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      (extractWord32 (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]) 0 == BitVec.ofNat 32 (pkAt (2 * k))) &&
      (extractWord32 (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]) 1 == BitVec.ofNat 32 (pkAt (2 * k + 1))) &&
      tblChk (k + 1) rest
  | _, [] => true
  | _, _ => false
set_option maxRecDepth 100000 in
theorem tbl_chk : tblChk 0 tblBytes = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem tblBytes_length : tblBytes.length = 65536 := by decide +kernel
theorem pk_lt_all : ∀ r, r < 563 → pk.getD r 0 < 2 ^ 32 := by decide +kernel
theorem lwu_word : ∀ c, c < 9 → coordLook c (lwuI c) = some 0x000e6c83 := by decide +kernel
theorem lwuI_lt : ∀ c, c < 9 → lwuI c < 2 ^ 20 := by decide +kernel
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsTable ====
section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem pk_digit (r : Fin 563) (i : Fin 6) : pk.getD r.val 0 / 8 ^ i.val % 8 = WCT9.wordDigit r i := by
  have hl : WCT9.codeWords.length = 563 := WCT9.codeWords_length
  have hr2 : r.val < pk.length := by rw [pk_length]; exact r.isLt
  have hz : r.val < (WCT9.codeWords.zip pk).length := by simp [hl, pk_length]
  have h := List.all_eq_true.mp pk_digits_all _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at h
  have h2 := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simp only [beq_iff_eq] at h2
  rw [List.getD_eq_getElem _ _ hr2, h2]
  unfold WCT9.wordDigit WCT9.digit
  rw [WCT9.codeword_embed]
theorem tblChk_get : ∀ (m k : Nat) (l : List (BitVec 8)), tblChk k l = true → 8 * m + 8 ≤ l.length →
    extractWord32 (bytesToWordLE ((l.drop (8 * m)).take 8)) 0 = BitVec.ofNat 32 (pkAt (2 * (k + m))) ∧
    extractWord32 (bytesToWordLE ((l.drop (8 * m)).take 8)) 1 = BitVec.ofNat 32 (pkAt (2 * (k + m) + 1))
  | m, k, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h, hl => by
    simp only [tblChk, Bool.and_eq_true, beq_iff_eq] at h
    rcases m with _ | m
    · simpa using ⟨h.1.1, h.1.2⟩
    · have := tblChk_get m (k + 1) rest h.2 (by simp at hl; omega)
      rw [show 8 * (m + 1) = 8 + 8 * m by omega, ← List.drop_drop]
      simpa [show k + 1 + m = k + (m + 1) by omega] using this
  | m, k, [], _, hl => by simp at hl
  | m, k, [_], _, hl => by simp at hl <;> omega
  | m, k, [_, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _, _, _], _, hl => by simp at hl <;> omega
theorem table_word {t : MachineState} (h : TableAt t) {f : Nat} (hf : f < 16384) :
    t.getWord32 (BitVec.ofNat 64 (TBL + 4 * f)) = BitVec.ofNat 32 (pkAt f) := by
  have hk : f / 2 < 8192 := by omega
  have hlt : TBL + 4 * f < 2 ^ 64 := by unfold TBL; omega
  unfold MachineState.getWord32
  have ha : alignToDword (BitVec.ofNat 64 (TBL + 4 * f)) = BitVec.ofNat 64 (TBL + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt hlt, toNat_ofNat_lt (by unfold TBL; omega)]
    unfold TBL; omega
  have hb : byteOffset (BitVec.ofNat 64 (TBL + 4 * f)) / 4 = f % 2 := by
    rw [byteOffset_eq, toNat_ofNat_lt hlt]; unfold TBL; omega
  rw [ha, hb, h (f / 2) hk]
  have hr := tblChk_get (f / 2) 0 tblBytes tbl_chk (by rw [tblBytes_length]; omega)
  rw [Nat.zero_add] at hr
  rcases Nat.mod_two_eq_zero_or_one f with h0 | h1
  · rw [h0, hr.1, show 2 * (f / 2) = f by omega]
  · rw [h1, hr.2, show 2 * (f / 2) + 1 = f by omega]
theorem pkAt_lt (f : Nat) : pkAt f < 2 ^ 32 := by
  unfold pkAt
  split_ifs with h
  · exact pk_lt_all _ h
  · norm_num
theorem pkAt_digit (f : Nat) (hf : f < 563) (i : Fin 6) :
    pkAt f / 8 ^ i.val % 8 = WCT9.wordDigit ⟨f, hf⟩ i := by
  unfold pkAt; rw [if_pos hf]; exact pk_digit ⟨f, hf⟩ i
theorem decode_lwu : decodeInstruction 0x000e6c83 = some (.base (.LWU .x25 .x28 0)) := by rfl
theorem step_lwu {im : Image} (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState)
    (hpc : s.pc = pcOf (lwuI c)) {f : Nat} (hf : f < 16384) (h28 : s.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * f))
    (ht : TableAt s) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (lwuI c + 1) ∧ t.getReg .x25 = BitVec.ofNat 64 (pkAt f) ∧
      RegsExcept s t [.x25] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  have hlw := lwuI_lt c hc
  have hpc' : (s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : coordLook c ((s.pc.toNat - 0x1000) / 4) = some 0x000e6c83 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * lwuI c - 0x1000) / 4 = lwuI c by omega]
    exact lwu_word c hc
  have hf' : fetch im s = some (.base (.LWU .x25 .x28 0)) :=
    (fetch_of_look hl hpc' hw s rfl).trans decode_lwu
  have hcl : classify (.base (.LWU .x25 .x28 0)) = some (.load .wu .x25 .x28 (signExtend12 0)) := rfl
  have hacc : accessValid (s.getReg .x28 + signExtend12 0) LoadKind.wu.width = true := by
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show TBL + 4 * f < 2 ^ 64 by unfold TBL; omega), MEMORY_BYTES]
    unfold TBL; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact SigGolfCandidate.T3M.pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    simp only [LoadKind.read, e, table_word ht hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := pkAt_lt f
    omega
  · intro r hr
    have hne : Reg.x25 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsChain ====
section

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem run_pres {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k : Nat} {brs : List Br} (h : run look stops n dirs = some (pres regs mem obl pc ec k brs)) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k k ((pres regs mem obl pc ec k brs).toState s) ∧
      (ec = true → fetch im ((pres regs mem obl pc ec k brs).toState s) = some (.base .ECALL)) :=
  run_sound hl h s hpc hobl hbr
theorem runA_pres {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k : Nat} {brs : List Br} (h : runA look stops n dirs = some (pres regs mem obl pc ec k brs)) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k k ((pres regs mem obl pc ec k brs).toState s) ∧
      (ec = true → fetch im ((pres regs mem obl pc ec k brs).toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem no_obl (s : MachineState) : ∀ o ∈ ([] : List Oblig), o.holds s := by intro o ho; cases ho
theorem runA_pres2 {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k cyc : Nat} {brs : List Br} (h : runA look stops n dirs = some (pres2 regs mem obl pc ec k cyc brs))
    (s : MachineState) (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k cyc ((pres2 regs mem obl pc ec k cyc brs).toState s) ∧
      (ec = true → fetch im ((pres2 regs mem obl pc ec k cyc brs).toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem no_br (s : MachineState) : ∀ b ∈ ([] : List Br), b.holds s := by intro b hb; cases hb
theorem valid_ofNat {s : MachineState} {b : E} {B off w : Nat} (hb : b.eval s = BitVec.ofNat 64 B)
    (hal : (B + off) % w = 0) (hhi : B + off + w ≤ MEMORY_BYTES) :
    (Oblig.valid ⟨some b, BitVec.ofNat 64 off⟩ w).holds s := by
  unfold MEMORY_BYTES at hhi
  simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat, accessValid, rangeValid, Bool.and_eq_true,
    decide_eq_true_eq, toNat_ofNat_lt (show B + off < 2 ^ 64 by omega), MEMORY_BYTES]
  exact ⟨hhi, hal⟩
theorem ne_ofNat {s : MachineState} {b : E} {B off K : Nat} (hb : b.eval s = BitVec.ofNat 64 B)
    (hlt : B + off < 2 ^ 64) (hk : K < 2 ^ 64) (hne : B + off ≠ K) :
    (Oblig.ne ⟨some b, BitVec.ofNat 64 off⟩ ⟨none, BitVec.ofNat 64 K⟩).holds s := by
  simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]
  intro h
  exact hne ((ofNat_inj hlt hk).mp h)
theorem br_ne_holds (s : MachineState) (x y : E) (d : Bool) :
    Br.holds s ⟨.ne, x, y, d⟩ ↔ ((x.eval s != y.eval s) = d) := Iff.rfl
theorem br_ltu_holds (s : MachineState) (x y : E) (d : Bool) :
    Br.holds s ⟨.ltu, x, y, d⟩ ↔ (BitVec.ult (x.eval s) (y.eval s) = d) := Iff.rfl
theorem ofNat_bne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he => h ((ofNat_inj ha hb).mp he)
    simp [h, this]
theorem ofNat_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, toNat_ofNat_lt ha, toNat_ofNat_lt hb]
theorem frame_of_memEval {s t : MachineState} {ws : SymMem} (ht : ∀ a, t.getMem a = memEval s ws a)
    (W : Nat → Prop) (hW : ∀ p ∈ ws, p.1.base = none ∧ W p.1.off.toNat) : Frame s t W := by
  intro A hA hn
  rw [ht, memEval_frame_ofNat s ws A hA (fun p hp => ⟨(hW p hp).1, fun he => hn (he ▸ (hW p hp).2)⟩)]
theorem off_mwc (a : Nat) (e : E) (ha : a < 2 ^ 64) : (mwc a e).1.off.toNat = a := toNat_ofNat_lt ha
theorem memEval_mwc_self (s : MachineState) (a : Nat) (e : E) (ws : SymMem) (ha : a < 2 ^ 64) :
    memEval s (mwc a e :: ws) (BitVec.ofNat 64 a) = e.eval s := by
  rw [memEval_mwc s a a e ws ha ha, if_pos rfl]
theorem memEval_mwc_ne (s : MachineState) {a A : Nat} (e : E) (ws : SymMem) (hA : A < 2 ^ 64) (ha : a < 2 ^ 64)
    (hne : A ≠ a) : memEval s (mwc a e :: ws) (BitVec.ofNat 64 A) = memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_mwc s a A e ws hA ha, if_neg hne]
macro "ao" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr6, hdr8, chainK, nodeK, true_or, or_true,
  and_true, true_and]) <;> omega))
macro "aoh" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr6, hdr8, chainK, nodeK, true_or, or_true,
  and_true, true_and] at *) <;> omega))
section pieces
variable {im : Image}
theorem step_SK (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 11175) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (cbase 0) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 8 * k))) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 32 + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 16 + 8 * k))) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = PRIVW + 40 ∨ A = PRIVW + 32 ∨ A = PRIVW + 8 ∨ A = PRIVW) := by
  obtain ⟨hst, -⟩ := run_pres (headLook_ok hcode) runSK_eq s hpc (no_obl s) (no_br s)
  have hm : ∀ a, ((expSK).toState s).getMem a = memEval s expSK.st.mem a := fun a => rfl
  refine ⟨_, hst, rfl, fun k hk => ?_, fun k hk => ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · refine frame_of_memEval hm _ (fun p hp => ?_)
    simp only [expSK, pres, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [mwc, PRIVW, BitVec.toNat_ofNat] <;> decide
def fk (c : Nat) : Nat := if fhas c then 13 else 12
theorem fsrcE_eq (c : Nat) : fsrcE c = SearchM.grpE c := rfl
theorem fieldE_eq (c : Nat) : fieldE c = SearchM.fieldEOld c := rfl
theorem fchildE_eq (c : Nat) : fchildE c = SearchM.childE c := rfl
theorem childE_eval (s : MachineState) (N : BitVec 256) (hN : OutAt s NBUF N) (c : Nat) (hc : c < 9) :
    (fchildE c).eval s = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase c % 128) := by
  rw [fchildE_eq]; exact SearchM.childE_eval s N hN c hc
theorem step_F (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (cbase c))
    {N : BitVec 256} (hN : OutAt s NBUF N) :
    ∃ t, Steps im s (fk c) (fk c) t ∧ t.pc = pcOf (lwuI c) ∧
      t.getReg .x24 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase c % 128) ∧
      t.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * (N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runF_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
  · rw [pres_getReg]; exact childE_eval s N hN c hc
  · rw [pres_getReg]
    show BinOp.eval .add (BinOp.eval .sll ((fieldE c).eval s) (BitVec.ofNat 64 2)) (BitVec.ofNat 64 TBL) = _
    rw [fieldE_eq, SearchM.fieldEOld_eval s N hN c hc, binop_sll _ _ (by norm_num), ofNat_shl]
    simp only [BinOp.eval, ofNat_add_ofNat]
    congr 1; ring
theorem eval_orIdx (s : MachineState) {index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    orIdx.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * 0) := by
  show BitVec.ofNat 64 0 ||| s.getReg .x22 = _
  rw [h22, Nat.mul_zero, Nat.add_zero]
  exact BitVec.zero_or
theorem step_Z (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lwuI c + 1))
    {index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 14 14 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * 0) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * 0) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 16 ∨ A = PRIVW + 24) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runZ_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_orIdx s h22
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expZ, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_x7p1 (s : MachineState) {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) :
    x7p1.eval s = BitVec.ofNat 64 (j + 1) := by
  show s.getReg .x7 + BitVec.ofNat 64 1 = _; rw [h7, ofNat_add_ofNat]
theorem eval_pairWE (s : MachineState) {j index : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    pairWE.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) := by
  show BinOp.eval .or (BinOp.eval .sll (x7p1.eval s) (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [eval_x7p1 s h7, binop_sll _ _ (by norm_num), ofNat_shl, h22]
  exact ofNat_or_hi index (j + 1) hidx
theorem step_CLc (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j index B : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 < 27)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 B) (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 10 10 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 (j + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (B + 32) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 24) := by
  have hb : ∀ b ∈ (expCL c true).brs, b.holds s := by
    intro b hb
    simp only [expCL, if_true, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc true) s hpc (no_obl s) hb
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; exact eval_x7p1 s h7, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getReg]; show s.getReg .x12 + BitVec.ofNat 64 32 = _; rw [h12, ofNat_add_ofNat]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_pairWE s h7 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expCL, if_true, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; exact ⟨rfl, by rw [off_mwc _ _ (by ao)]⟩
theorem step_CLx (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 = 27) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x12, .x18] ∧ Frame s t (fun _ => False) := by
  have hb : ∀ b ∈ (expCL c false).brs, b.holds s := by
    intro b hb
    simp only [expCL, Bool.false_eq_true, if_false, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc false) s hpc (no_obl s) hb
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp),
    fun A _ _ => rfl⟩
theorem eval_ptE (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (_hj : j < 2 ^ 32)
    (i : Nat) : (ptE i).eval s = BitVec.ofNat 64 (6 * j + i + 1) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1))
    (s.getReg .x18)) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 (i + 1)) = _
  have e1 : BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1)) (s.getReg .x18) =
      BitVec.ofNat 64 (3 * j) := by
    rw [binop_sll _ _ (by norm_num), h18, ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
  rw [e1, binop_sll _ _ (by norm_num), ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
theorem step_Q (hcode : NewCodeAt im) {c i j : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (hj : j < 128) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf hornI ∧ t.getReg .x1 = pcOf (qI c i + 5) ∧
      t.getReg .x6 = BitVec.ofNat 64 (6 * j + i + 1) ∧ RegsExcept s t [.x1, .x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runQ_eq hc hi) s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; exact eval_ptE s h18 (by omega) i,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
def chainW0 (c i j index p : Nat) : Nat := index * 2 ^ 27 + j * 2 ^ 20 + chainK c i + 256 * p
theorem chainW0_merge (c i j index p q : Nat) (hc : c < 9) (hi : i < 6) (hp : p < 4) (hq : q < 4) :
    StoreKind.merge .b (BitVec.ofNat 64 (chainW0 c i j index p)) 1 (BitVec.ofNat 64 q) =
      BitVec.ofNat 64 (chainW0 c i j index q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat8 _ _ (by omega)]
  simp only [chainW0, chainK, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem step_S (hcode : NewCodeAt im) {c i j index w : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i + 5)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) (hd : w / 8 ^ i % 8 ≤ 4) :
    ∃ t, Steps im s (if c = 0 then 17 else 15) (if c = 0 then 17 else 15) t ∧ t.pc = pcOf (chkI c i 0) ∧
      t.getReg .x26 = BitVec.ofNat 64 (4 - w / 8 ^ i % 8) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index 0) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x26, .x29] ∧ Frame s t (fun A => A = CHAINW + 24 ∨ A = CHAINW + 16) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runS_eq hc hi) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]; exact eval_dE s i h25 hw (by omega) hd
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_qE s h18 h22 hj (chainK_lt c i hc hi)]
    simp only [chainW0, Nat.mul_zero, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expS, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_Chk (hcode : NewCodeAt im) {c i st j sel e : Nat} (hc : c < 9) (hi : i < 6) (hst : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (chkI c i st)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (h26 : s.getReg .x26 = BitVec.ofNat 64 e) (hj : j < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (he : e < 2 ^ 64) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t k, Steps im s k k t ∧ k ≤ 11 ∧ t.pc = pcOf (skipI c i st) ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = slotV c i + 8 ∨ A = slotV c i) ∧ (j = sel → e = st → DigAt t (slotV c i) v) ∧
      (¬ (j = sel ∧ e = st) → Frame s t (fun _ => False)) := by
  have hl := coordLook_ok hcode hc
  by_cases hjs : j = sel
  · subst hjs
    by_cases hes : e = st
    · subst hes
      obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 2 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      refine ⟨_, 11, hst', le_rfl, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_, fun _ _ => ⟨?_, ?_⟩, ?_⟩
      · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
        simp only [expChk, pres, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
          List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
      · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
      · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
      · intro h; exact absurd ⟨rfl, rfl⟩ h
    · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 1 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp [hes]
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      exact ⟨_, 3, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
        fun _ h => absurd h hes, fun _ A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 0 < 3)) s hpc (no_obl s) (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hsel]; simp [hjs])
    exact ⟨_, 1, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
      fun h => absurd h hjs, fun _ A _ _ => rfl⟩
theorem step_Stp (hcode : NewCodeAt im) {c i st j index : Nat} (hc : c < 9) (hi : i < 6) (h1 : 1 ≤ st) (h4 : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (skipI c i (st - 1))) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv)) :
    ∃ t, Steps im s 9 9 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (chkI c i st - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAINW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAINW + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (st - 1)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = CHAINW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runStp_eq hc hi h1 h4) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (st - 1)) = _
    rw [h16, chainW0_merge c i j index pv (st - 1) hc hi hpv (by omega)]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expStp, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; refine ⟨rfl, ?_⟩; rw [off_mwc _ _ (by ao)]
theorem step_Lc (hcode : NewCodeAt im) {c i : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (skipI c i 4)) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) v ∧
      t.getReg .x29 = BitVec.ofNat 64 LEAFW ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFW + leafOff i + 8 ∨ A = LEAFW + leafOff i) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runLc_eq hc hi) s hpc (no_obl s) (no_br s)
  have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
  refine ⟨_, hst', rfl, ⟨?_, ?_⟩, rfl, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expLc, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem padE_eval (s : MachineState) (c off : Nat) :
    (padE c off).eval s = if c = 0 then 0 else s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + off)) := by
  unfold padE; split_ifs <;> rfl
/-- The leaf header block (nested FTS r1-1): for `c >= 1` the pad slot `LEAFW + 32` gets `L_{c-1}` from the previous
forest pair (`padE`), for `c = 0` it is zero. -/
theorem step_L (hcode : NewCodeAt im) {c j index : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lI c))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 LEAFW) :
    ∃ t, Steps im s (if c = 0 then 21 else 23) (if c = 0 then 21 else 23) t ∧ fetch im t = some (.base .ECALL) ∧
      t.pc = pcOf (tI c - 1) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFW ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 (HEAPW + 16 * (j + 128)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 16)) = BitVec.ofNat 64 (leafLo7 c index j) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 24)) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFW + 32)) = (padE c 0).eval s ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 40)) = (padE c 8).eval s ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12] ∧
      Frame s t (fun A => A = LEAFW + 24 ∨ A = LEAFW + 16 ∨ A = LEAFW + 40 ∨ A = LEAFW + 32) := by
  have hx : ∀ a, memEval s [(x29A 24, cE 0), (x29A 16, leafLoE c), (x29A 40, padE c 8), (x29A 32, padE c 0)] a =
      memEval s [mwc (LEAFW + 24) (cE 0), mwc (LEAFW + 16) (leafLoE c), mwc (LEAFW + 40) (padE c 8),
        mwc (LEAFW + 32) (padE c 0)] a := by
    intro a
    simp only [memEval, Addr.eval, x29A, mwc, E.eval, h29, ofNat_add_ofNat]
    rfl
  have hv : ∀ off, off % 8 = 0 → off ≤ 120 → (Oblig.valid (x29A off) 8).holds s := fun off h1 h2 =>
    valid_ofNat (b := .reg .x29) (B := LEAFW) (by simp only [E.eval]; exact h29) (by ao) (by unfold MEMORY_BYTES; ao)
  obtain ⟨hst', hec⟩ := runA_pres (coordLook_ok hcode hc) (runL_eq hc) s hpc (by
    intro o ho
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ((rfl | rfl | rfl) | ho) | rfl
    · exact hv 24 (by norm_num) (by norm_num)
    · exact hv 16 (by norm_num) (by norm_num)
    · exact hv 40 (by norm_num) (by norm_num)
    · split_ifs at ho with hc0
      · simp at ho
      · simp only [List.mem_singleton] at ho
        subst ho
        simp only [Oblig.holds, Addr.eval, x29A, E.eval, h29, ofNat_add_ofNat]
        intro he
        have hfo : forOff (c - 1) ≤ 288 := by unfold forOff; omega
        have := (ofNat_inj (by ao) (by ao)).mp he
        unfold forOff at this; aoh
    · exact hv 32 (by norm_num) (by norm_num)) (no_br s)
  have ht : ∀ a, ((expL c).toState s).getMem a = memEval s [mwc (LEAFW + 24) (cE 0), mwc (LEAFW + 16) (leafLoE c),
      mwc (LEAFW + 40) (padE c 8), mwc (LEAFW + 32) (padE c 0)] a :=
    fun a => hx a
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]
    show BinOp.eval .add (heapLeafE.eval s) (BitVec.ofNat 64 HEAPW) = _
    rw [eval_heapLeafE s h18]; simp only [BinOp.eval, ofNat_add_ofNat]
    rw [Nat.add_comm]
  · refine (ht _).trans ?_
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact eval_leafLoE s h22 h18 hc hj
  · refine (ht _).trans ?_
    rw [memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine (ht _).trans ?_
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
  · refine (ht _).trans ?_
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]
  · refine frame_of_memEval ht _ (fun q hq => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_T (hcode : NewCodeAt im) {c j : Nat} (hc : c < 9) (hj : j < 128) (s : MachineState)
    (hpc : s.pc = pcOf (tI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ (j + 1 < 128 → t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 (j + 1)) ∧
      (j + 1 = 128 → t.pc = pcOf (nodeI c) ∧ t.getReg .x18 = BitVec.ofNat 64 127) ∧
      RegsExcept s t [.x6, .x18] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  by_cases hb : j + 1 < 128
  · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc true) s hpc (no_obl s) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'
      rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]; simp [hb])
    exact ⟨_, 3, hst', by norm_num, fun _ => ⟨rfl, by rw [pres_getReg]; exact eval_x18p1 s h18⟩,
      fun h => absurd h (by omega), pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc false) s hpc (no_obl s) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'
      rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]; simp [hb])
    exact ⟨_, 4, hst', le_rfl, fun h => absurd h hb, fun _ => ⟨rfl, rfl⟩, pres_regsExcept _ _ _ _ _ _ _ s,
      fun A _ _ => rfl⟩
theorem eval_nodeLd (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (off : Nat) :
    (nodeLd off).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + off)) := by
  show s.getMem (sh5.eval s + BitVec.ofNat 64 (HEAPW + off)) = _
  rw [eval_sh5 s h18, ofNat_add_ofNat]; congr 2; ring
theorem step_N (hcode : NewCodeAt im) {c h index : Nat} (hc : c < 9) (hh1 : 1 ≤ h) (hh : h < 128)
    (s : MachineState) (hpc : s.pc = pcOf (nodeI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 31) :
    ∃ t, Steps im s (if c = 0 then 29 else 25) (if c = 0 then 32 else 28) t ∧ fetch im t = some (.base .ECALL) ∧
      t.pc = pcOf (ntI c - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODEW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUTW ∧
      t.getMem (BitVec.ofNat 64 NODEW) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 48)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 56)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (nodeLoN c index h) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 (if 8 ≤ h then 0 else h) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29] ∧
      Frame s t (fun A => A = NODEW + 24 ∨ A = NODEW + 16 ∨ A = NODEW + 56 ∨ A = NODEW + 48 ∨ A = NODEW + 8 ∨
        A = NODEW) := by
  have hb := eval_sh5 s h18
  obtain ⟨hst', hec⟩ := runA_pres2 (coordLook_ok hcode hc) (runN_eq hc) s hpc (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)) (no_br s)
  have m : ∀ A, A < 2 ^ 64 → ((expN c).toState s).getMem (BitVec.ofNat 64 A) =
      memEval s (expN c).st.mem (BitVec.ofNat 64 A) := fun A _ => rfl
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, pres2_regsExcept _ _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres2_getMem]; simp only [memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 24 < 2 ^ 64 by ao)
      (by ao), memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 16 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 56 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 48 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 8 < 2 ^ 64 by ao) (by ao)]
    rw [memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18, Nat.add_zero]
  · rw [pres2_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres2_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres2_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres2_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact eval_nodeLoNE s h22 h18 hc hidx hh
  · rw [pres2_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_nodeHiE s h18 hh
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expN, pres2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
/-- Nested FTS (r1-1): the fold output half kept for heap `h` (HIGH half for heaps 2 and 3). -/
def hiOff (h : Nat) : Nat := if h < 4 then 16 else 0
/-- Cycles of the fold post-hash block (nested FTS r1-1). -/
def ntC (c h : Nat) : Nat := if c = 0 then 18 else if h = 4 ∨ h = 2 then 25 else 22
/-- The fold pad word `NODEW + 32 + off` after the post-hash block of heap `h` (nested FTS r1-1): `R_{c-1}` after
heap 4, zero after heap 2 (coordinates `c >= 1`), unchanged otherwise. -/
def ntPad (c h off : Nat) (s : MachineState) : Word :=
  if 1 ≤ c ∧ h = 4 then s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + 16 + off))
  else if 1 ≤ c ∧ h = 2 then 0 else s.getMem (BitVec.ofNat 64 (NODEW + 32 + off))
theorem eval_hiSelE (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hh : h < 128) :
    hiSelE.eval s = BitVec.ofNat 64 (hiOff h) := by
  show BinOp.eval .sll (BinOp.eval .sltu (s.getReg .x18) (BitVec.ofNat 64 4)) (BitVec.ofNat 64 4) = _
  rw [h18]
  unfold hiOff
  simp only [BinOp.eval, ofNat_ult (show h < 2 ^ 64 by omega) (show 4 < 2 ^ 64 by norm_num)]
  by_cases h4 : h < 4 <;> simp [h4] <;> rfl
theorem step_NT (hcode : NewCodeAt im) {c h : Nat} (hc : c < 9) (hh1 : 2 ≤ h) (hh : h < 128) (s : MachineState)
    (hpc : s.pc = pcOf (ntI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s (ntC c h) (ntC c h) t ∧ (3 ≤ h → t.pc = pcOf (nodeI c)) ∧ (h = 2 → t.pc = pcOf (rI c)) ∧
      t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h)) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 32)) = ntPad c h 0 s ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 40)) = ntPad c h 8 s ∧
      RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
      Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h ∨ A = NODEW + 32 ∨ A = NODEW + 40) := by
  have hl := coordLook_ok hcode hc
  have hb := eval_sh4 s h18
  have hm1 := eval_x18m1 s h18 (by omega) (by omega)
  have hsel := eval_hiSelE s h18 hh
  have hho : hiOff h ≤ 16 := by unfold hiOff; split_ifs <;> omega
  have hea : ∀ off, Addr.eval s (heapAddr off) = BitVec.ofNat 64 (HEAPW + 16 * h + off) := by
    intro off
    show sh4.eval s + BitVec.ofNat 64 (HEAPW + off) = _
    rw [hb, ofNat_add_ofNat]; congr 1; ring
  have hout : ∀ off, (outLd off).eval s = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h + off)) := by
    intro off
    show s.getMem (hiSelE.eval s + BitVec.ofNat 64 (NOUTW + off)) = _
    rw [hsel, ofNat_add_ofNat]; congr 2; ring
  have hfo : ∀ c', c' < 9 → forOff c' ≤ 288 := fun c' hc' => by unfold forOff; omega
  -- one symbolic result covers each (kind, direction) pair; the caller picks the consistent ones
  have post : ∀ (kd : Nat) (b : Bool), (b = true ↔ 3 ≤ h) →
      (1 ≤ c → (kd = 1 ↔ h = 4) ∧ (kd = 2 ↔ h = 2) ∧ kd < 3) →
      runNT c kd b = some (expNT c kd b) →
      ∃ t, Steps im s (if c = 0 then 18 else if kd = 0 then 22 else 25)
          (if c = 0 then 18 else if kd = 0 then 22 else 25) t ∧ t.pc = pcOf (if b then nodeI c else rI c) ∧
        t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
        t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h)) ∧
        t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h + 8)) ∧
        t.getMem (BitVec.ofNat 64 (NODEW + 32)) = ntPad c h 0 s ∧
        t.getMem (BitVec.ofNat 64 (NODEW + 40)) = ntPad c h 8 s ∧
        RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
        Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h ∨ A = NODEW + 32 ∨ A = NODEW + 40) := by
    intro kd b hbh hkd hrun
    have hva : ∀ off, off = 0 ∨ off = 8 → (Oblig.valid (outAddr off) 8).holds s := fun off hoff =>
      valid_ofNat hsel (by unfold hiOff at *; split_ifs <;> rcases hoff with rfl | rfl <;> ao)
        (by unfold MEMORY_BYTES; rcases hoff with rfl | rfl <;> ao)
    have hne : ∀ off K, off ≤ 8 → (K = NODEW + 32 ∨ K = NODEW + 40) →
        (Oblig.ne (outAddr off) ⟨none, BitVec.ofNat 64 K⟩).holds s := fun off K hoff hK =>
      ne_ofNat hsel (by ao) (by rcases hK with rfl | rfl <;> ao) (by rcases hK with rfl | rfl <;> ao)
    obtain ⟨hst', -⟩ := runA_pres hl hrun s hpc (by
      intro o ho
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with (rfl | rfl) | ho
      · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
      · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
      · unfold ntOutObl at ho
        split_ifs at ho
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl
          · exact hva 8 (Or.inr rfl)
          · exact hva 0 (Or.inl rfl)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hne 8 _ (by norm_num) (Or.inl rfl)
          · exact hne 8 _ (by norm_num) (Or.inr rfl)
          · exact hva 8 (Or.inr rfl)
          · exact hne 0 _ (by norm_num) (Or.inl rfl)
          · exact hne 0 _ (by norm_num) (Or.inr rfl)
          · exact hva 0 (Or.inl rfl)) (by
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [br_ne_holds, hm1, eval_cE, ofNat_bne (by omega) (by norm_num)]
        cases b <;> simp_all <;> omega
      · unfold ntBrs at hq
        have e4 : ∀ d, Br.holds s ⟨.ne, .reg .x18, cE 4, d⟩ ↔ (decide (h ≠ 4) = d) := fun d => by
          rw [br_ne_holds]; simp only [E.eval, h18, eval_cE]; rw [ofNat_bne (by omega) (by norm_num)]
        have e2 : ∀ d, Br.holds s ⟨.ne, .reg .x18, cE 2, d⟩ ↔ (decide (h ≠ 2) = d) := fun d => by
          rw [br_ne_holds]; simp only [E.eval, h18, eval_cE]; rw [ofNat_bne (by omega) (by norm_num)]
        split_ifs at hq with c0 k1 k2
        · simp at hq
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq
          rw [e4]; have := (hkd (by omega)).1.mp k1; simp [this]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          have := (hkd (by omega)).2.1.mp k2
          rcases hq with rfl | rfl
          · rw [e2]; simp [this]
          · rw [e4]; simp [this]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          have hk := hkd (by omega)
          have n4 : h ≠ 4 := fun e => k1 (hk.1.mpr e)
          have n2 : h ≠ 2 := fun e => k2 (hk.2.1.mpr e)
          rcases hq with rfl | rfl
          · rw [e2]; simp [n2]
          · rw [e4]; simp [n4])
    have hpad0 : memEval s (ntPadMem c kd) (BitVec.ofNat 64 (NODEW + 32)) = ntPad c h 0 s := by
      simp only [ntPad, Nat.add_zero]
      by_cases c0 : c = 0
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => by omega
        have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => by omega
        simp only [ntPadMem, if_pos c0, if_neg n4, if_neg n2]; rfl
      have hk := hkd (by omega)
      by_cases k1 : kd = 1
      · have p4 : 1 ≤ c ∧ h = 4 := ⟨by omega, hk.1.mp k1⟩
        simp only [ntPadMem, if_neg c0, if_pos k1, if_pos p4]
        rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => k1 (hk.1.mpr h'.2)
        by_cases k2 : kd = 2
        · have p2 : 1 ≤ c ∧ h = 2 := ⟨by omega, hk.2.1.mp k2⟩
          simp only [ntPadMem, if_neg c0, if_neg k1, if_pos k2, if_neg n4, if_pos p2]
          rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
        · have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => k2 (hk.2.1.mpr h'.2)
          simp only [ntPadMem, if_neg c0, if_neg k1, if_neg k2, if_neg n4, if_neg n2]; rfl
    have hpad8 : memEval s (ntPadMem c kd) (BitVec.ofNat 64 (NODEW + 40)) = ntPad c h 8 s := by
      simp only [ntPad]
      by_cases c0 : c = 0
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => by omega
        have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => by omega
        simp only [ntPadMem, if_pos c0, if_neg n4, if_neg n2]; rfl
      have hk := hkd (by omega)
      by_cases k1 : kd = 1
      · have p4 : 1 ≤ c ∧ h = 4 := ⟨by omega, hk.1.mp k1⟩
        simp only [ntPadMem, if_neg c0, if_pos k1, if_pos p4]
        rw [memEval_mwc_self _ _ _ _ (by ao), show FORW + forOff (c - 1) + 16 + 8 = FORW + forOff (c - 1) + 24 by omega]
        rfl
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => k1 (hk.1.mpr h'.2)
        by_cases k2 : kd = 2
        · have p2 : 1 ≤ c ∧ h = 2 := ⟨by omega, hk.2.1.mp k2⟩
          simp only [ntPadMem, if_neg c0, if_neg k1, if_pos k2, if_neg n4, if_pos p2]
          rw [memEval_mwc_self _ _ _ _ (by ao)]; rfl
        · have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => k2 (hk.2.1.mpr h'.2)
          simp only [ntPadMem, if_neg c0, if_neg k1, if_neg k2, if_neg n4, if_neg n2]; rfl
    have hmem : ∀ A, A < 2 ^ 64 → A ≠ HEAPW + 16 * h + 8 → A ≠ HEAPW + 16 * h →
        memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) (BitVec.ofNat 64 A) =
          memEval s (ntPadMem c kd) (BitVec.ofNat 64 A) := by
      intro A hA h1 h2
      rw [memEval_cons, memEval_cons, hea, hea, if_neg (fun he => h1 ((ofNat_inj hA (by ao)).mp he)),
        if_neg (fun he => h2 (by rw [(ofNat_inj hA (by ao)).mp he, Nat.add_zero]))]
    refine ⟨_, hst', rfl, by rw [pres_getReg]; exact hm1, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
    · rw [pres_getMem]
      show memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) _ = _
      rw [memEval_cons, memEval_cons, hea, hea, if_neg (by
        intro he; have := (ofNat_inj (by ao) (by ao)).mp he; omega), if_pos (by rw [Nat.add_zero])]
      rw [hout 0, Nat.add_zero]
    · rw [pres_getMem]
      show memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) _ = _
      rw [memEval_cons, hea, if_pos rfl, hout 8]
    · rw [pres_getMem]; exact (hmem _ (by ao) (by ao) (by ao)).trans hpad0
    · rw [pres_getMem]; exact (hmem _ (by ao) (by ao) (by ao)).trans hpad8
    · intro A hA hn
      simp only [not_or] at hn
      rw [pres_getMem]
      show memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) _ = _
      rw [hmem A hA hn.1 hn.2.1]
      unfold ntPadMem
      split_ifs
      · rfl
      · rw [memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.2, memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.1]; rfl
      · rw [memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.2, memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.1]; rfl
      · rfl
  have hC : ∀ kd, (1 ≤ c → (kd = 1 ↔ h = 4) ∧ (kd = 2 ↔ h = 2) ∧ kd < 3) →
      (if c = 0 then 18 else if kd = 0 then 22 else 25) = ntC c h := by
    intro kd hk
    unfold ntC
    by_cases c0 : c = 0
    · simp [c0]
    · have := hk (by omega)
      simp only [c0, if_false]
      by_cases k0 : kd = 0
      · subst k0; simp only [if_true]; rw [if_neg (by omega)]
      · rw [if_neg k0, if_pos (by omega)]
  obtain ⟨kd, b, hbh, hk, hrun⟩ : ∃ kd b, (b = true ↔ 3 ≤ h) ∧
      (1 ≤ c → (kd = 1 ↔ h = 4) ∧ (kd = 2 ↔ h = 2) ∧ kd < 3) ∧ runNT c kd b = some (expNT c kd b) := by
    by_cases c0 : c = 0
    · subst c0
      by_cases h3 : 3 ≤ h
      · exact ⟨0, true, by simp [h3], fun h' => absurd h' (by norm_num), runNT_eq0 hc⟩
      · exact ⟨0, false, by simp [h3], fun h' => absurd h' (by norm_num), runNT_eqX hc⟩
    · by_cases e4 : h = 4
      · exact ⟨1, true, by simp; omega, fun _ => ⟨by simp [e4], by simp; omega, by norm_num⟩, runNT_eq1 hc⟩
      · by_cases e2 : h = 2
        · have := runNT_eqX hc; rw [if_neg c0] at this
          exact ⟨2, false, by simp; omega, fun _ => ⟨by simp; omega, by simp [e2], by norm_num⟩, this⟩
        · exact ⟨0, true, by simp; omega, fun _ => ⟨by simp; omega, by simp; omega, by norm_num⟩, runNT_eq0 hc⟩
  obtain ⟨t, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ := post kd b hbh hk hrun
  rw [hC kd hk] at h1'
  refine ⟨t, h1', fun h3 => ?_, fun h2 => ?_, h3', h4', h5', h6', h7', h8', h9'⟩
  · rw [h2', if_pos (hbh.mpr h3)]
  · rw [h2', if_neg (fun hb' => by have := hbh.mp hb'; omega)]
theorem step_R0 (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (rI c)) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (pcI c 0) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 40)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 16)) = s.getMem (BitVec.ofNat 64 (HEAPW + 48)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 24)) = s.getMem (BitVec.ofNat 64 (HEAPW + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = FORW + forOff c + 24 ∨ A = FORW + forOff c + 16 ∨ A = FORW + forOff c + 8 ∨
        A = FORW + forOff c) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runR0_eq hc) s hpc (no_obl s) (no_br s)
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expR0, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_pathLd (s : MachineState) {sel : Nat} (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (hsel : sel < 128)
    {l : Nat} (hl : l < 7) (off : Nat) :
    (pathLd l off).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) + off)) := by
  show s.getMem ((pathE l).eval s + BitVec.ofNat 64 (HEAPW + off)) = _
  rw [eval_pathE s h24 hsel l hl, ofNat_add_ofNat]; congr 2; ring
set_option maxRecDepth 100000 in
theorem pathHeap_lt_all : ∀ sel, sel < 128 → ∀ l, l < 7 → 2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) < 256 := by
  decide +kernel
theorem pathHeap_lt (sel l : Nat) (hsel : sel < 128) (hl : l < 7) :
    2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) < 256 := pathHeap_lt_all sel hsel l hl
theorem step_PC (hcode : NewCodeAt im) {c l sel : Nat} (hc : c < 9) (hl : l < 7) (hsel : sel < 128) (s : MachineState)
    (hpc : s.pc = pcOf (pcI c l)) (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (pcI c (l + 1)) ∧
      t.getMem (BitVec.ofNat 64 (slotP c l)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)))) ∧
      t.getMem (BitVec.ofNat 64 (slotP c l + 8)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun A => A = slotP c l + 8 ∨ A = slotP c l) := by
  have hb := eval_pathE s h24 hsel l hl
  have hlt := pathHeap_lt sel l hsel hl
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runPC_eq hc hl) s hpc (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_pathLd s h24 hsel hl, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao), eval_pathLd s h24 hsel hl]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expPC, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
/-- Nested FTS (r1-1): the forest hash is replaced by copying the last top pair `(L8, R8)` (forest-buffer slot 8) to
`FOUT` (the L3 message, copied to the encoding block at 370) and to the encoding R slot `0x20290`. -/
theorem step_For (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 20715) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 370 ∧
      t.getMem (BitVec.ofNat 64 FOUT) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8)) ∧
      t.getMem (BitVec.ofNat 64 (FOUT + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 8)) ∧
      t.getMem (BitVec.ofNat 64 0x20290) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 16)) ∧
      t.getMem (BitVec.ofNat 64 (0x20290 + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = 0x20290 + 8 ∨ A = 0x20290 ∨ A = FOUT + 8 ∨ A = FOUT) := by
  obtain ⟨hst', -⟩ := run_pres (forLook_ok hcode) runFor_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expFor, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_J (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 20729) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 370 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst', -⟩ := run_pres (tailLook_ok hcode) runJ_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst', rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
end pieces
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest header pad64 privateInput zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem readWords_of_getD (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_getD t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]
theorem hashInput_of_words (t : MachineState) (l : List UInt8) (n A : Nat) (hl : l.length = 64 * (n + 1))
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 * (n + 1) < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hw : ∀ j < 8 * (n + 1), t.getMem (BitVec.ofNat 64 (A + 8 * j)) = (wordsOf l).getD j 0) :
    hashInput t = toQ l :=
  hashInput_toQ t l n A hl h10 hA (by omega) h11 (by omega)
    (readWords_of_getD t A _ _ (length_wordsOf _ _ (by rw [hl]; ring)) hw)
theorem header_words (tag lay tree pos idx : Nat) (ht : ¬ SigGolfCandidate.T3.packedNodeTag tag) (htag : tag < 256)
    (hlay : lay < 256) (htree : tree < 2 ^ 32) (hpos : pos < 2 ^ 32) (hidx : idx < 2 ^ 32) :
    wordsOf (bytesLE 16 (header tag lay tree pos idx)) =
      [BitVec.ofNat 64 (1 + 256 * tag + 65536 * lay + 2 ^ 32 * pos), BitVec.ofNat 64 (tree + 2 ^ 32 * idx)] := by
  rw [wordsOf_header, if_neg ht, if_neg ht, hdr0_eq tag lay tree pos htag hlay htree hpos, hdr1_eq tree idx htree hidx]
theorem wordsOf_priv (sk : BitVec 256) (c index q : Nat) (hc : c < 256) (hidx : index < 2 ^ 32) (hq : q < 2 ^ 32) :
    wordsOf (privateInput sk (.inl (header 8 c index 0 q))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 (hdr8 c), BitVec.ofNat 64 (index + 2 ^ 32 * q),
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  rw [wordsOf_privateInput_tweak, header_lo, header_hi, if_neg (by decide), if_neg (by decide),
    hdr0_eq 8 c index 0 (by norm_num) hc hidx (by norm_num), hdr1_eq index q hidx hq]
  simp only [hdr8]; congr 3
theorem chainInput_len (index c j i st : Nat) (v : Digest) : (WCT9.chainInput index c j i st v).length = 64 := by
  simp only [WCT9.chainInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem ftsChainLow_eq (index c j i st : Nat) (hc : c < 9) (hidx : index < 2 ^ 31) (hst : st < 4) (hi : i < 6)
    (hj : j < 128) : WCT9.ftsChainLow index c j i st = chainW0 c i j index st := by
  unfold WCT9.ftsChainLow chainW0 chainK
  rw [Nat.mod_eq_of_lt (show i < 8 by omega), Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt (show c + 1 < 16 by omega),
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hidx]
  ring
theorem wordsOf_chain (index c j i st : Nat) (v : Digest) (hc : c < 9) (hidx : index < 2 ^ 31) (hst : st < 4)
    (hi : i < 6) (hj : j < 128) :
    wordsOf (pad64 (WCT9.chainInput index c j i st v)) =
      [0, 0, BitVec.ofNat 64 (chainW0 c i j index st), 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_len]), WCT9.chainInput_eq,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  unfold WCT9.ftsChainHeader
  rw [WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high, ftsChainLow_eq index c j i st hc hidx hst hi hj]
  rfl
/-- Witness stack: the G input `value | header | 0 | 0` of FTS chains 1, 3. -/
theorem wordsOf_chainG (index c j i st : Nat) (v : Digest) (hG : WCT9.ftsIsG i = true) (hc : c < 9)
    (hidx : index < 2 ^ 31) (hst : st < 4) (hi : i < 6) (hj : j < 128) :
    wordsOf (pad64 (WCT9.ftsChainInputW index c j i st v)) =
      [v.extractLsb' 0 64, v.extractLsb' 64 64, BitVec.ofNat 64 (chainW0 c i j index st), 0, 0, 0, 0, 0] := by
  rw [WCT9.ftsChainInputW_padded, WCT9.ftsChainInputW_G hG,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  unfold WCT9.ftsChainHeader
  rw [WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high, ftsChainLow_eq index c j i st hc hidx hst hi hj]
  rfl
/-- FTS leaf input with the pad slot (nested FTS r1-1: `L_{c-1}`, zero for coordinate 0). -/
def leafIn (index c j : Nat) (pad : Digest) (ends : List Digest) : List UInt8 :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.ftsLeafHeader index c j) ++ bytesLE 16 pad ++
    (ends.drop 1).flatMap (bytesLE 16)
theorem leafHashP_eq (index c j : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashP index c j pad ends = SigGolfCandidate.T3.shortHash (leafIn index c j pad ends) := rfl
/-- C1: the paired leaf of heap `heap` hashes the same input; its half follows `ftsHighHeap heap`. -/
theorem leafHashH_eq' (heap index c j : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashH heap index c j pad ends = WCT9.ftsHash heap (leafIn index c j pad ends) := rfl
theorem leafIn_len (index c j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    (leafIn index c j pad ends).length = 128 := by
  have : ((ends.drop 1).flatMap (bytesLE 16)).length = 80 := by
    rw [List.length_flatMap]; simp [bytesLE_length, h]
  simp only [leafIn, List.length_append, bytesLE_length, this]
theorem ftsLeafHeader_words (index c j : Nat) (hc : c < 9) (hidx : index < 2 ^ 31) (hj : j < 128) :
    wordsOf (bytesLE 16 (WCT9.ftsLeafHeader index c j)) = [BitVec.ofNat 64 (leafLo7 c index j), 0] := by
  rw [wordsOf_bytesLE16]
  unfold WCT9.ftsLeafHeader
  rw [SigGolfCandidate.T3.append64_low]
  congr 1
  · unfold WCT9.ftsLeafLow leafLo7
    congr 1
    rw [Nat.mod_eq_of_lt (show c + 1 < 16 by omega), Nat.mod_eq_of_lt (show j < 128 from hj), Nat.mod_eq_of_lt hidx]
    ring
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.append64_toNat]
    have := (BitVec.ofNat 64 (WCT9.ftsLeafLow index c j)).isLt
    have h0' : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0']
    omega
theorem wordsOf_leaf (index c j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) (hc : c < 9)
    (hidx : index < 2 ^ 31) (hj : j < 128) :
    wordsOf (pad64 (leafIn index c j pad ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [BitVec.ofNat 64 (leafLo7 c index j), 0] ++
        [pad.extractLsb' 0 64, pad.extractLsb' 64 64] ++
        (ends.drop 1).flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ _ h]), leafIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]),
    ftsLeafHeader_words index c j hc hidx hj, wordsOf_bytesLE16 pad, wordsOf_flatMap16]
/-- FTS node input with the pad slot (nested FTS r1-1: `R_{c-1}` for heaps 2 and 3, zero otherwise). -/
def nodeIn (c index h : Nat) (pad L R : Digest) : List UInt8 :=
  bytesLE 16 L ++ bytesLE 16 (WCT9.wctNodeHeader c index h) ++ bytesLE 16 pad ++ bytesLE 16 R
theorem nodeHash_eq (c index h : Nat) (L R : Digest) :
    WCT9.wctNodeHash c index h L R = SigGolfCandidate.T3.shortHash (nodeIn c index h 0 L R) := by
  unfold nodeIn; rw [WCT9.bytesLE_zero16, WCT9.wctNodeHash_eq_short]
/-- C1: the paired node of heap `h ≥ 8` hashes the same input as the legacy node; its half follows `ftsHighHeap h`. -/
theorem nodeHashH_eq (c index h : Nat) (L R : Digest) :
    WCT9.wctNodeHashH c index h L R = WCT9.ftsHash h (nodeIn c index h 0 L R) := by
  unfold nodeIn WCT9.wctNodeHashH; rw [WCT9.bytesLE_zero16]
theorem topHash_eq (c index h : Nat) (L pad R : Digest) :
    WCT9.wctTopHash c index h L pad R =
      (SigGolfCandidate.T3.publicHash (nodeIn c index h pad L R) >>= fun o => pure (o.extractLsb' 128 128)) := rfl
theorem nodeIn_len (c index h : Nat) (pad L R : Digest) : (nodeIn c index h pad L R).length = 64 := by
  simp only [nodeIn, List.length_append, bytesLE_length]
theorem hdr0_node (c index : Nat) (hc : c < 9) (hidx : index < 2 ^ 32) :
    hdr0 3 (4 + c) index index = nodeK c + 2 ^ 32 * index := by
  unfold hdr0 nodeK
  rw [Nat.mod_eq_of_lt (show 3 < 256 by norm_num), Nat.mod_eq_of_lt (show 4 + c < 256 by omega),
    Nat.div_eq_of_lt hidx, Nat.mod_eq_of_lt hidx]
  ring
theorem wordsOf_node (c index h : Nat) (pad L R : Digest) (hc : c < 9) (hidx : index < 2 ^ 31) (hh : h < 128) :
    wordsOf (pad64 (nodeIn c index h pad L R)) =
      [L.extractLsb' 0 64, L.extractLsb' 64 64, BitVec.ofNat 64 (nodeLoN c index h),
        BitVec.ofNat 64 (if 8 ≤ h then 0 else h), pad.extractLsb' 0 64, pad.extractLsb' 64 64,
        R.extractLsb' 0 64, R.extractLsb' 64 64] := by
  have hlo : (WCT9.wctNodeHeader c index h).extractLsb' 0 64 = BitVec.ofNat 64 (nodeLoN c index h) := by
    rw [WCT9.wctNodeHeader_low hc]
    unfold nodeLoN
    by_cases h8 : 8 ≤ h
    · rw [if_pos (show SigGolfCandidate.T3.FtsNew h from ⟨h8, hh⟩), if_pos h8]
      unfold nodeLo7 WCT9.ftsNodeLowN
      rw [Nat.mod_eq_of_lt (show c + 1 < 16 by omega), Nat.mod_eq_of_lt hidx]
      congr 1; omega
    · rw [if_neg (show ¬ SigGolfCandidate.T3.FtsNew h from fun h' => h8 h'.1), if_neg h8]
      unfold nodeLo7 WCT9.ftsLeafLow
      rw [Nat.mod_eq_of_lt (show c + 1 < 16 by omega), Nat.mod_eq_of_lt hidx]
      congr 1; omega
  have hhi : (WCT9.wctNodeHeader c index h).extractLsb' 64 64 = BitVec.ofNat 64 (if 8 ≤ h then 0 else h) := by
    rw [WCT9.wctNodeHeader_high hc]
    by_cases h8 : 8 ≤ h
    · rw [if_pos (show SigGolfCandidate.T3.FtsNew h from ⟨h8, hh⟩), if_pos h8]
    · rw [if_neg (show ¬ SigGolfCandidate.T3.FtsNew h from fun h' => h8 h'.1), if_neg h8]
  rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16,
    wordsOf_bytesLE16, hlo, hhi]
  rfl
theorem forestPk_eq (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = SigGolfCandidate.T3.shortHash (WCT9.forestInput index pairs) := rfl
def pairWords (p : Digest × Digest) : List Word :=
  [p.1.extractLsb' 0 64, p.1.extractLsb' 64 64, p.2.extractLsb' 0 64, p.2.extractLsb' 64 64]
theorem wordsOf_pairs (ps : List (Digest × Digest)) :
    wordsOf (ps.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = ps.flatMap pairWords := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ih]
    rfl
theorem pairs_bytes_len (ps : List (Digest × Digest)) :
    (ps.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2).length = 32 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_append, bytesLE_length, bytesLE_length,
      List.length_cons]
    ring
theorem forestIn_len (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (WCT9.forestInput index pairs).length = 320 := by
  simp only [WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_len, h]
theorem wordsOf_forest (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9)
    (hidx : index < 2 ^ 32) :
    wordsOf (pad64 (WCT9.forestInput index pairs)) =
      [0, 0, BitVec.ofNat 64 3841, BitVec.ofNat 64 index] ++ pairs.flatMap pairWords := by
  rw [pad64_of_aligned _ (by rw [forestIn_len _ _ h]), WCT9.forestInput,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_zero16, header_words 15 0 index 0 0 (by decide) (by norm_num) (by norm_num) hidx (by norm_num)
      (by norm_num), wordsOf_pairs]
  rfl
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
def chainRest (index c j i d : Nat) : Nat → List Digest → M (Digest × Digest)
  | 0, L => pure (L.getD (4 - d) 0, L.getD 4 0)
  | r + 1, L => SigGolfCandidate.T3.projHash (WCT9.ftsChainHigh i (3 - r))
      (WCT9.ftsChainInputW index c j i (3 - r) (L.getD (3 - r) 0)) >>= fun v => chainRest index c j i d r (L ++ [v])
theorem chain4_eq (index c j i d : Nat) (hd : d ≤ 4) (seed : Digest) :
    (WCT9.chain index c j i 0 (4 - d) seed >>= fun value =>
      WCT9.chain index c j i (4 - d) d value >>= fun last => pure (value, last)) =
      chainRest index c j i d 4 [seed] := by
  interval_cases d <;>
    simp only [WCT9.chain, chainRest, show List.range' 0 4 = [0, 1, 2, 3] from rfl,
      show List.range' 0 3 = [0, 1, 2] from rfl,
      show List.range' 0 2 = [0, 1] from rfl, show List.range' 0 1 = [0] from rfl,
      show List.range' 0 0 = [] from rfl, show List.range' 4 0 = [] from rfl, show List.range' 3 1 = [3] from rfl,
      show List.range' 2 2 = [2, 3] from rfl, show List.range' 1 3 = [1, 2, 3] from rfl, List.foldlM_cons,
      List.foldlM_nil, bind_assoc, pure_bind, Nat.sub_self, Nat.sub_zero] <;> rfl
def chainW (c i : Nat) (A : Nat) : Prop :=
  (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨ (CHAINW + 48 ≤ A ∧ A < CHAINW + 112) ∨ A = LEAFW + leafOff i ∨
    A = LEAFW + leafOff i + 8 ∨ A = slotV c i ∨ A = slotV c i + 8
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x26, .x28, .x29]
structure ChkSt (c i j index sel w d r : Nat) (L : List Digest) (s0 t : MachineState) : Prop where
  pc : t.pc = pcOf (chkI c i (4 - r))
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  x26 : t.getReg .x26 = BitVec.ofNat 64 (4 - d)
  len : L.length = 5 - r
  val : DigAt t (CHAINW + 48) (L.getD (4 - r) 0)
  h16 : t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (4 - r - 1))
  h24 : t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
  op : j = sel → 4 - d < 4 - r → DigAt t (slotV c i) (L.getD (4 - d) 0)
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (chainW c i)
  nosel : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
def ChainPost (c i j sel : Nat) (s0 : MachineState) (r : Digest × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) r.2 ∧ (j = sel → DigAt t (slotV c i) r.1) ∧
    RegsExcept s0 t chainRegs ∧ Frame s0 t (chainW c i) ∧
    (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
      t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)) ∧
    t.getReg .x29 = BitVec.ofNat 64 LEAFW
theorem chkI_pos : ∀ c, c < 9 → ∀ i, i < 6 → ∀ st, st < 5 → 1 ≤ chkI c i st := by decide +kernel
theorem blocks64 (l : List UInt8) (hl : l.length = 64) : (toQ (pad64 l)).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; norm_num, by rw [hl]⟩, hl]
theorem pcOf_pred4 (n : Nat) (hn : 1 ≤ n) : pcOf (n - 1) + 4 = pcOf n := by
  rw [SigGolfCandidate.T3M.pcOf_add4, Nat.sub_add_cancel hn]
theorem DigAt.frame' {s t : MachineState} {W : Nat → Prop} {A : Nat} {d : Digest} (h : DigAt s A d)
    (hf : Frame s t W) (hA : A + 8 < 2 ^ 64) (h0 : ¬ W A) (h1 : ¬ W (A + 8)) : DigAt t A d :=
  h.frame hf hA h0 h1
-- (witness stack) the reference-image chain_from (NewCodeAt) was removed: the old FTS code has no G chains.
end ClaudeWCT.W9.Machine.Sign
end

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def writes (A : Nat) : Prop := A=LEAFW+16 ∨ A=LEAFW+24 ∨ A=LEAFW+32 ∨ A=LEAFW+40

theorem leaf_obligations (s : MachineState) {c j : Nat} (hc:c<9) (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) : ∀ o∈leafObl c,o.holds s := by
  unfold leafObl
  split
  · intro o ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    have hb:=branchShift_eval s hj h18 5 (by decide)
    rcases ho with rfl|rfl
    · exact valid_ofNat hb (by omega) (by unfold MEMORY_BYTES; omega)
    · exact valid_ofNat hb (by omega) (by unfold MEMORY_BYTES; omega)
  · exact no_obl s

theorem leaf_mem16 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+16)) = (headerE c).eval s := by
  simp [leafMem,memEval_mwc,LEAFW]
theorem leaf_mem24 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+24)) = 0 := by
  simp [leafMem,memEval_mwc,LEAFW,cE,E.eval]
theorem leaf_mem32 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+32)) = (padLoad c 0).eval s := by
  simp [leafMem,memEval_mwc,LEAFW]
theorem leaf_mem40 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+40)) = (padLoad c 8).eval s := by
  simp [leafMem,memEval_mwc,LEAFW]

theorem step_leaf {im : Image} {c j index : Nat} {pad : Digest}
    (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c))
    (h18:s.getReg .x18=BitVec.ofNat 64 j) (h22:s.getReg .x22=BitVec.ofNat 64 index)
    (hp:PadAt c j pad s) :
    ∃t, Steps im s (cycles c) (cycles c) t ∧ fetch im t=some (.base .ECALL) ∧ t.pc=pcOf (hashPc c) ∧
      t.getReg .x10=BitVec.ofNat 64 LEAFW ∧ t.getReg .x11=BitVec.ofNat 64 128 ∧
      t.getReg .x12=BitVec.ofNat 64 (HEAPW+16*(128+physical c j)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW+16))=BitVec.ofNat 64 (leafLo7 c index j) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW+24))=0 ∧
      DigAt t (LEAFW+32) pad ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28,.x29] ∧ Frame s t writes := by
  obtain ⟨hst,hec⟩:=run_pres hlook (leaf_run hc) s hpc (leaf_obligations s hc hj h18) (no_br s)
  refine ⟨(expected c).toState s,hst,hec rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw[expected,pres_getReg];rfl
  · rw[expected,pres_getReg];rfl
  · rw[expected,pres_getReg]
    change BinOp.eval .add ((outOffset c).eval s) (BitVec.ofNat 64 HEAPW) = _
    rw[outOffset_eval s hj h18]
    change BitVec.ofNat 64 (16*(128+physical c j))+BitVec.ofNat 64 HEAPW = _
    rw[ofNat_add_ofNat]
    congr 1
    omega
  · rw[expected,pres_getMem,leaf_mem16,headerE_eval s h18 h22]
  · rw[expected,pres_getMem,leaf_mem24]
  · change memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+32)) = _ ∧
      memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+32+8)) = _
    rw[leaf_mem32,show LEAFW+32+8=LEAFW+40 by omega,leaf_mem40]
    exact padLoad_eval s hj h18 hp
  · exact (pres_regsExcept (leafRegs c) _ _ _ _ _ _ s).mono (by simp [leafRegs])
  · refine frame_of_memEval (ws := leafMem c) (fun a => (rfl : ((expected c).toState s).getMem a = memEval s (leafMem c) a)) _ (fun p hm => ?_)
    simp only [leafMem,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by decide)] <;> simp [writes]

end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}
theorem step_Z (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lwuI c + 1))
    {index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 14 14 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * 0) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * 0) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 16 ∨ A = PRIVW + 24) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runZ_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_orIdx s h22
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expZ, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_x7p1 (s : MachineState) {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) :
    x7p1.eval s = BitVec.ofNat 64 (j + 1) := by
  show s.getReg .x7 + BitVec.ofNat 64 1 = _; rw [h7, ofNat_add_ofNat]
theorem eval_pairWE (s : MachineState) {j index : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    pairWE.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) := by
  show BinOp.eval .or (BinOp.eval .sll (x7p1.eval s) (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [eval_x7p1 s h7, binop_sll _ _ (by norm_num), ofNat_shl, h22]
  exact ofNat_or_hi index (j + 1) hidx
theorem step_CLc (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j index B : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 < 27)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 B) (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 10 10 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 (j + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (B + 32) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 24) := by
  have hb : ∀ b ∈ (expCL c true).brs, b.holds s := by
    intro b hb
    simp only [expCL, if_true, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc true) s hpc (no_obl s) hb
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; exact eval_x7p1 s h7, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getReg]; show s.getReg .x12 + BitVec.ofNat 64 32 = _; rw [h12, ofNat_add_ofNat]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_pairWE s h7 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expCL, if_true, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; exact ⟨rfl, by rw [off_mwc _ _ (by ao)]⟩
theorem step_CLx (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 = 27) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x12, .x18] ∧ Frame s t (fun _ => False) := by
  have hb : ∀ b ∈ (expCL c false).brs, b.holds s := by
    intro b hb
    simp only [expCL, Bool.false_eq_true, if_false, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc false) s hpc (no_obl s) hb
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp),
    fun A _ _ => rfl⟩
theorem eval_ptE (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (_hj : j < 2 ^ 32)
    (i : Nat) : (ptE i).eval s = BitVec.ofNat 64 (6 * j + i + 1) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1))
    (s.getReg .x18)) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 (i + 1)) = _
  have e1 : BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1)) (s.getReg .x18) =
      BitVec.ofNat 64 (3 * j) := by
    rw [binop_sll _ _ (by norm_num), h18, ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
  rw [e1, binop_sll _ _ (by norm_num), ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
theorem step_Q (hcode : Fetch im) {c i j : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (hj : j < 128) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf hornI ∧ t.getReg .x1 = pcOf (qI c i + 5) ∧
      t.getReg .x6 = BitVec.ofNat 64 (6 * j + i + 1) ∧ RegsExcept s t [.x1, .x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runQ_eq hc hi) s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; exact eval_ptE s h18 (by omega) i,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
def chainW0 (c i j index p : Nat) : Nat := index * 2 ^ 27 + j * 2 ^ 20 + chainK c i + 256 * p
theorem chainW0_merge (c i j index p q : Nat) (hc : c < 9) (hi : i < 6) (hp : p < 4) (hq : q < 4) :
    StoreKind.merge .b (BitVec.ofNat 64 (chainW0 c i j index p)) 1 (BitVec.ofNat 64 q) =
      BitVec.ofNat 64 (chainW0 c i j index q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat8 _ _ (by omega)]
  simp only [chainW0, chainK, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem step_S (hcode : Fetch im) {c i j index w : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i + 5)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) (hd : w / 8 ^ i % 8 ≤ 4) :
    ∃ t, Steps im s (if c = 0 then 17 else 15) (if c = 0 then 17 else 15) t ∧ t.pc = pcOf (chkI c i 0) ∧
      t.getReg .x26 = BitVec.ofNat 64 (4 - w / 8 ^ i % 8) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index 0) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x26, .x29] ∧ Frame s t (fun A => A = CHAINW + 24 ∨ A = CHAINW + 16) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runS_eq hc hi) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]; exact eval_dE s i h25 hw (by omega) hd
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_qE s h18 h22 hj (chainK_lt c i hc hi)]
    simp only [chainW0, Nat.mul_zero, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expS, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_Chk (hcode : Fetch im) {c i st j sel e : Nat} (hc : c < 9) (hi : i < 6) (hst : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (chkI c i st)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (h26 : s.getReg .x26 = BitVec.ofNat 64 e) (hj : j < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (he : e < 2 ^ 64) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t k, Steps im s k k t ∧ k ≤ 11 ∧ t.pc = pcOf (skipI c i st) ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = slotV c i + 8 ∨ A = slotV c i) ∧ (j = sel → e = st → DigAt t (slotV c i) v) ∧
      (¬ (j = sel ∧ e = st) → Frame s t (fun _ => False)) := by
  have hl := coordLook_ok hcode hc
  by_cases hjs : j = sel
  · subst hjs
    by_cases hes : e = st
    · subst hes
      obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 2 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      refine ⟨_, 11, hst', le_rfl, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_, fun _ _ => ⟨?_, ?_⟩, ?_⟩
      · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
        simp only [expChk, pres, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
          List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
      · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
      · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
      · intro h; exact absurd ⟨rfl, rfl⟩ h
    · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 1 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp [hes]
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      exact ⟨_, 3, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
        fun _ h => absurd h hes, fun _ A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 0 < 3)) s hpc (no_obl s) (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hsel]; simp [hjs])
    exact ⟨_, 1, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
      fun h => absurd h hjs, fun _ A _ _ => rfl⟩
theorem step_Stp (hcode : Fetch im) {c i st j index : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = false)
    (h1 : 1 ≤ st) (h4 : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (skipI c i (st - 1))) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv)) :
    ∃ t, Steps im s 9 9 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (chkI c i st - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAINW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAINW + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (st - 1)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = CHAINW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runStp_eq hc hi hG h1 h4) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (st - 1)) = _
    rw [h16, chainW0_merge c i j index pv (st - 1) hc hi hpv (by omega)]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expStp, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; refine ⟨rfl, ?_⟩; rw [off_mwc _ _ (by ao)]
/-- Witness stack: a G chain step (chains 1, 3) from its HASH site to the stub's ECALL. -/
theorem step_StpG (hcode : Fetch im) {c i p j index : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = true)
    (hp : p < 4) (s : MachineState) (hpc : s.pc = pcOf (skipI c i p)) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv)) :
    ∃ t, Steps im s 16 16 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (stubAt (p + 1) + 11) ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAINW + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (stubOut (p + 1)) ∧ t.getReg .x28 = pcOf (chkI c i (p + 1) - 5) ∧
      t.getReg .x29 = BitVec.ofNat 64 CHAINW ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index p) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 64)) = BitVec.ofNat 64 (chainW0 c i j index p) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 72)) = s.getMem (BitVec.ofNat 64 (CHAINW + 24)) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 80)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAINW + 88)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 96)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAINW + 104)) = 0 ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28, .x29] ∧
      Frame s t (fun A => A = CHAINW + 16 ∨ (CHAINW + 64 ≤ A ∧ A < CHAINW + 112)) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc)
    (runStpG_eq hc hi hG (by omega : 1 ≤ p + 1) (by omega : p + 1 < 5)).1 s
    (by rw [hpc, Nat.add_sub_cancel]) (no_obl s) (no_br s)
  have hm : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (p + 1 - 1)) =
      BitVec.ofNat 64 (chainW0 c i j index p) := by
    rw [h16, Nat.add_sub_cancel, chainW0_merge c i j index pv p hc hi hpv hp]
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (p + 1 - 1)) = _
    exact hm
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (p + 1 - 1)) = _
    exact hm
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expStpG, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
/-- Witness stack: the G stub's tail after the ECALL (zero `CHAINW+32/40`, return to the site + 6). -/
theorem step_PostG (hcode : Fetch im) {c i p : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = true)
    (hp : p < 4) (s : MachineState) (hpc : s.pc = pcOf (stubAt (p + 1) + 12))
    (h28 : s.getReg .x28 = pcOf (chkI c i (p + 1) - 5)) (h29 : s.getReg .x29 = BitVec.ofNat 64 CHAINW) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (chkI c i (p + 1)) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = CHAINW + 32 ∨ A = CHAINW + 40) := by
  have hk : ∀ q ∈ knownG c i (p + 1), s.getReg q.1 = q.2 := by
    intro q hq
    simp only [knownG, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact h28
    · exact h29
  obtain ⟨hst, -⟩ := pathRun_sound (runStpG_eq hc hi hG (by omega : 1 ≤ p + 1) (by omega : p + 1 < 5)).2
    (coordLook_ok hcode hc) s hpc hk (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, fun r _ => ?_, ?_⟩
  · show memEval s [mwc (CHAINW + 40) (cE 0), mwc (CHAINW + 32) (cE 0)] (BitVec.ofNat 64 (CHAINW + 32)) = 0
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · show memEval s [mwc (CHAINW + 40) (cE 0), mwc (CHAINW + 32) (cE 0)] (BitVec.ofNat 64 (CHAINW + 40)) = 0
    rw [memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw [PRes.toState_getReg']
    exact RegFile.withKnown_eval s _ hk r
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expPostG, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
/-- Witness stack: the memory effect of a whole G step (stub + hash + tail): only `CHAINW+16` and `CHAINW+48..111`
change (`CHAINW+32/40` are restored to zero). -/
theorem frameG {s t2 t3 : MachineState} {a : BitVec 256} {B : Nat} (hB : B = CHAINW + 32 ∨ B = CHAINW + 48)
    (x12 : t2.getReg .x12 = BitVec.ofNat 64 B)
    (f2 : Frame s t2 (fun A => A = CHAINW + 16 ∨ (CHAINW + 64 ≤ A ∧ A < CHAINW + 112)))
    (f3 : Frame (writeHash t2 a) t3 (fun A => A = CHAINW + 32 ∨ A = CHAINW + 40))
    (z3a : t3.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0) (z3b : t3.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0)
    (h32 : s.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0) (h40 : s.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0) :
    Frame s t3 (fun A => A = CHAINW + 16 ∨ (CHAINW + 48 ≤ A ∧ A < CHAINW + 112)) := by
  intro A hA hn
  simp only [not_or, not_and, not_lt] at hn
  by_cases e32 : A = CHAINW + 32
  · rw [e32, z3a, h32]
  by_cases e40 : A = CHAINW + 40
  · rw [e40, z3b, h40]
  rw [f3.get hA (by intro h; rcases h with h | h; exact e32 h; exact e40 h)]
  rcases hB with rfl | rfl
  · rw [getMem_writeHash t2 a _ A x12 (by ao) hA, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    exact f2.get hA (by intro h; rcases h with h | h <;> omega)
  · rw [getMem_writeHash t2 a _ A x12 (by ao) hA, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    exact f2.get hA (by intro h; rcases h with h | h <;> omega)
theorem step_Lc (hcode : Fetch im) {c i : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (skipI c i 4)) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) v ∧
      t.getReg .x29 = BitVec.ofNat 64 LEAFW ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFW + leafOff i + 8 ∨ A = LEAFW + leafOff i) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runLc_eq hc hi) s hpc (no_obl s) (no_br s)
  have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
  refine ⟨_, hst', rfl, ⟨?_, ?_⟩, rfl, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expLc, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem padE_eval (s : MachineState) (c off : Nat) :
    (padE c off).eval s = if c = 0 then 0 else s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + off)) := by
  unfold padE; split_ifs <;> rfl


variable {sk : BitVec 256}
/-- Witness stack: one FTS chain step from its skip point to the next check point (at most 27 cycles): the F code
(`shortHash` of `chainInput`, 17) or, for chains 1, 3, the G stub (27) (`projHash (ftsChainHigh i p)` of the G input). -/
theorem hashStep (hcode : Fetch im) {β : Type} {c i j index p pv W : Nat} (hc : c < 9) (hi : i < 6) (hj : j < 128)
    (hidx : index < 2 ^ 31) (hp : p < 4) (hpv : pv < 4) {v : Digest} {f : Digest → M β}
    {Q : β → MachineState → Prop} (s : MachineState) (hpc : s.pc = pcOf (skipI c i p))
    (hx5 : s.getReg .x5 = 0)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv))
    (h0 : s.getMem (BitVec.ofNat 64 CHAINW) = 0) (h8 : s.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0)
    (h24 : s.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0)
    (h32 : s.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0) (h40 : s.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0)
    (hv : DigAt s (CHAINW + 48) v)
    (hk : ∀ (a : Digest) (t : MachineState), t.pc = pcOf (chkI c i (p + 1)) → DigAt t (CHAINW + 48) a →
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index p) →
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28, .x29] →
      Frame s t (fun A => A = CHAINW + 16 ∨ (CHAINW + 48 ≤ A ∧ A < CHAINW + 112)) → TBSim im sk t W (f a) Q) :
    TBSim im sk s (27 + W) (SigGolfCandidate.T3.projHash (WCT9.ftsChainHigh i p)
      (WCT9.ftsChainInputW index c j i p v) >>= f) Q := by
  have hpos := chkI_pos c hc i hi (p + 1) (by omega)
  by_cases hG : WCT9.ftsIsG i = true
  · obtain ⟨t2, s2, e2, p2, x10, x11, x12, x28, x29, m16, m64, m72, m80, m88, m96, m104, r2, f2⟩ :=
      step_StpG (j := j) (index := index) hcode hc hi hG hp s hpc hpv h16
    have hx5' : t2.getReg .x5 = 0 := by rw [r2.get (by simp)]; exact hx5
    have g2 : ∀ A, A < 2 ^ 64 → A ≠ CHAINW + 16 → A < CHAINW + 64 →
        t2.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 =>
      f2.get hA (by intro h; rcases h with h | h <;> omega)
    have hq : hashInput t2 = toQ (pad64 (WCT9.ftsChainInputW index c j i p v)) := by
      refine hashInput_of_words t2 _ 0 (CHAINW + 48)
        (by rw [WCT9.ftsChainInputW_padded, WCT9.ftsChainInputW_length]) x10 (by ao) (by ao) x11 ?_
      rw [wordsOf_chainG index c j i p v hG hc hidx hp hi hj]
      intro k hk
      interval_cases k
      · rw [g2 _ (by ao) (by ao) (by ao)]; exact hv.1
      · rw [g2 _ (by ao) (by ao) (by ao)]; exact hv.2
      · exact m64
      · exact m72.trans h24
      · exact m80
      · exact m88
      · exact m96
      · exact m104
    have hbl := blocks64 _ (WCT9.ftsChainInputW_length index c j i p v)
    have hpc3 : ∀ a, (writeHash t2 a).pc = pcOf (stubAt (p + 1) + 12) := fun a => by
      rw [pc_writeHash, p2]; exact SigGolfCandidate.T3M.pcOf_add4 _
    by_cases hint : p < 3
    · have hhigh : WCT9.ftsChainHigh i p = true :=
        WCT9.ftsChainHigh_eq_true.mpr ⟨WCT9.ftsIsG_eq_true.mp hG, hint⟩
      have hout : stubOut (p + 1) = CHAINW + 32 := if_neg (by omega)
      rw [hout] at x12
      have e : (SigGolfCandidate.T3.projHash true (WCT9.ftsChainInputW index c j i p v) >>= f) =
          (SigGolfCandidate.T3.publicHash (WCT9.ftsChainInputW index c j i p v) >>= fun a =>
            f (a.extractLsb' 128 128)) := by
        simp only [SigGolfCandidate.T3.projHash, bind_assoc, pure_bind]; rfl
      rw [hhigh, e]
      refine (TBSim.steps s2 (TBSim.publicHash_bind' (W := 3 + W) e2 hx5'
        (hashArgs_const t2 (CHAINW + 48) 64 (CHAINW + 32) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao))
        hq (fun a => ?_))).mono (by rw [hbl]; omega) (fun _ _ h => h)
      obtain ⟨t3, s3, p3, z3a, z3b, r3, f3⟩ := step_PostG hcode hc hi hG hp (writeHash t2 a) (hpc3 a)
        (by rw [getReg_writeHash]; exact x28) (by rw [getReg_writeHash]; exact x29)
      refine TBSim.steps s3 (hk _ t3 p3 ?_ ?_ ?_ ?_)
      · exact (DigAt.writeHash_hi t2 a (CHAINW + 32) x12 (by ao)).frame f3 (by ao) (by ao) (by ao)
      · rw [f3.get (by ao) (by ao), getMem_writeHash t2 a (CHAINW + 32) _ x12 (by ao) (by ao), if_neg (by ao),
          if_neg (by ao), if_neg (by ao), if_neg (by ao)]
        exact m16
      · exact ((r2.trans (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).trans r3).mono
          (by simp)
      · exact frameG (Or.inl rfl) x12 f2 f3 z3a z3b h32 h40
    · have hp3 : p = 3 := by omega
      subst hp3
      have hout : stubOut (3 + 1) = CHAINW + 48 := by unfold stubOut; simp
      rw [hout] at x12
      rw [WCT9.ftsChainHigh_three, SigGolfCandidate.T3.projHash_false]
      refine (TBSim.steps s2 (TBSim.shortHash_bind' (W := 3 + W) e2 hx5'
        (hashArgs_const t2 (CHAINW + 48) 64 (CHAINW + 48) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao))
        hq (fun a => ?_))).mono (by rw [hbl]; omega) (fun _ _ h => h)
      obtain ⟨t3, s3, p3, z3a, z3b, r3, f3⟩ := step_PostG hcode hc hi hG hp (writeHash t2 a) (hpc3 a)
        (by rw [getReg_writeHash]; exact x28) (by rw [getReg_writeHash]; exact x29)
      refine TBSim.steps s3 (hk _ t3 p3 ?_ ?_ ?_ ?_)
      · exact (DigAt.writeHash_lo t2 a (CHAINW + 48) x12 (by ao)).frame f3 (by ao) (by ao) (by ao)
      · rw [f3.get (by ao) (by ao), getMem_writeHash t2 a (CHAINW + 48) _ x12 (by ao) (by ao), if_neg (by ao),
          if_neg (by ao), if_neg (by ao), if_neg (by ao)]
        exact m16
      · exact ((r2.trans (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).trans r3).mono
          (by simp)
      · exact frameG (Or.inr rfl) x12 f2 f3 z3a z3b h32 h40
  · have hG' : WCT9.ftsIsG i = false := by simpa using hG
    rw [WCT9.ftsChainHigh_of_F hG', WCT9.ftsChainInputW_F hG', SigGolfCandidate.T3.projHash_false]
    obtain ⟨t2, s2, e2, p2, x10, x11, x12, m16, r2, f2⟩ :=
      step_Stp (j := j) (index := index) hcode hc hi hG' (by omega : 1 ≤ p + 1) (by omega : p + 1 < 5) s
        (by rw [hpc, Nat.add_sub_cancel]) hpv h16
    rw [Nat.add_sub_cancel] at m16
    have hx5' : t2.getReg .x5 = 0 := by rw [r2.get (by simp)]; exact hx5
    have g2 : ∀ A, A < 2 ^ 64 → A ≠ CHAINW + 16 → t2.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 => f2.get hA h1
    have hq : hashInput t2 = toQ (pad64 (WCT9.chainInput index c j i p v)) := by
      refine hashInput_of_words t2 _ 0 CHAINW (by rw [pad64_of_aligned _ (by rw [chainInput_len]), chainInput_len])
        x10 (by ao) (by ao) x11 ?_
      rw [wordsOf_chain index c j i p _ hc hidx hp hi hj]
      intro k hk
      interval_cases k
      · rw [g2 _ (by ao) (by ao)]; exact h0
      · rw [g2 _ (by ao) (by ao)]; exact h8
      · exact m16
      · rw [g2 _ (by ao) (by ao)]; exact h24
      · rw [g2 _ (by ao) (by ao)]; exact h32
      · rw [g2 _ (by ao) (by ao)]; exact h40
      · rw [g2 _ (by ao) (by ao)]; exact hv.1
      · rw [g2 _ (by ao) (by ao)]; exact hv.2
    have hbl := blocks64 _ (chainInput_len index c j i p v)
    have fw := fun a => Frame.writeHash t2 a (CHAINW + 48) x12 (by ao)
    refine (TBSim.steps s2 (TBSim.shortHash_bind' (W := W) e2 hx5'
      (hashArgs_const t2 CHAINW 64 (CHAINW + 48) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => hk _ _ ?_ ?_ ?_ ?_ ?_))).mono (by rw [hbl]; omega) (fun _ _ h => h)
    · rw [pc_writeHash, p2, pcOf_pred4 _ hpos]
    · exact DigAt.writeHash_lo t2 a (CHAINW + 48) x12 (by ao)
    · rw [(fw a).get (by ao) (by ao)]; exact m16
    · exact (r2.trans (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).mono (by simp)
    · exact (f2.trans (fw a)).mono (fun A _ hA => by
        rcases hA with hA | hA
        · left; exact hA
        · right; obtain ⟨h3, h4⟩ := hA; constructor <;> omega)
theorem chain_from (hcode : Fetch im) {c i j index sel w d : Nat} (hc : c < 9) (hi : i < 6) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hd : d ≤ 4) {s0 : MachineState} :
    ∀ r, r ≤ 4 → ∀ (L : List Digest) (t : MachineState), ChkSt c i j index sel w d r L s0 t →
      TBSim im sk t (11 + 38 * r + 8) (chainRest index c j i d r L) (ChainPost c i j sel s0) := by
  intro r
  induction r with
  | zero =>
    intro _ L t h
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by norm_num : 4 < 5) t h.pc h.x18 h.x24 h.x26 (by omega) (by omega) (by omega) h.val
    obtain ⟨t2, s2, p2, l2, x29_2, r2, f2⟩ := step_Lc hcode hc hi t1 p1 (h.val.frame f1 (by ao) (by ao) (by ao))
    have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
    refine (TBSim.pure_steps' (s1.trans s2) ⟨p2, l2, fun hjs => ?_, ?_, ?_, ?_, x29_2⟩).mono (by omega)
      (fun _ _ h => h)
    · by_cases hd0 : d = 0
      · subst hd0
        have := o1 hjs rfl
        exact this.frame f2 (by ao) (by ao) (by ao)
      · have := h.op hjs (by omega)
        exact (this.frame (n1 (fun h' => hd0 (by omega))) (by ao) (fun h => h) (fun h => h)).frame f2
          (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact ((h.regs.trans r1).trans r2).mono (by simp [chainRegs])
    · refine ((h.frame.trans f1).trans f2).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with (hA | hA) | hA <;> [exact hA; (rcases hA with rfl | rfl <;> simp); (rcases hA with rfl | rfl <;> simp)]
    · intro hjs A hA h1 h2
      rw [f2.get hA (by intro h'; unfold slotV at h1 h2; rcases h' with rfl | rfl <;> aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
  | succ r ih =>
    intro hr L t h
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by omega : 3 - r < 5) t (by rw [h.pc]; congr 2; omega) h.x18 h.x24 h.x26
        (by omega) (by omega) (by omega) h.val
    have m1 : ∀ A, A < 2 ^ 64 → A ≠ slotV c i → A ≠ slotV c i + 8 →
        t1.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 =>
      f1.get hA (by intro h'; rcases h' with h' | h'; exact h2 h'; exact h1 h')
    have hlen : L.length = 4 - r := by have := h.len; omega
    have hv1 : DigAt t1 (CHAINW + 48) (L.getD (3 - r) 0) := by
      have hv := h.val
      rw [show 4 - (r + 1) = 3 - r by omega] at hv
      exact hv.frame f1 (by ao) (by intro h'; unfold slotV at h'; aoh) (by intro h'; unfold slotV at h'; aoh)
    have hm : ∀ A, CHAINW ≤ A → A < CHAINW + 112 →
        t1.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
      fun A hA0 hA => m1 A (by aoh) (by unfold slotV; aoh) (by unfold slotV; aoh)
    refine (TBSim.steps s1 (hashStep (W := 11 + 38 * r + 8) hcode hc hi hj hidx (p := 3 - r) (by omega)
      (pv := 4 - (r + 1) - 1) (by omega) t1 p1 (by rw [r1.get (by simp)]; exact h.x5)
      (by rw [hm _ (by ao) (by ao)]; exact h.h16) (by rw [hm _ (by ao) (by ao)]; exact h.z0) (by rw [hm _ (by ao) (by ao)]; exact h.z8)
      (by rw [hm _ (by ao) (by ao)]; exact h.h24) (by rw [hm _ (by ao) (by ao)]; exact h.z32) (by rw [hm _ (by ao) (by ao)]; exact h.z40)
      hv1 (fun a t2 p2 v2 m2 r2 f2 => ih (by omega) (L ++ [a]) t2 ?_))).mono (by omega) (fun _ _ h => h)
    have g : ∀ A, A < 2 ^ 64 → A ≠ CHAINW + 16 → (A < CHAINW + 48 ∨ CHAINW + 112 ≤ A) →
        t2.getMem (BitVec.ofNat 64 A) = t1.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 =>
      f2.get hA (by intro h'; rcases h' with h' | ⟨h3, h4⟩ <;> omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [p2]; congr 2; omega
    · rw [r2.get (by simp), r1.get (by simp)]; exact h.x5
    · rw [r2.get (by simp), r1.get (by simp)]; exact h.x18
    · rw [r2.get (by simp), r1.get (by simp)]; exact h.x22
    · rw [r2.get (by simp), r1.get (by simp)]; exact h.x24
    · rw [r2.get (by simp), r1.get (by simp)]; exact h.x25
    · rw [r2.get (by simp), r1.get (by simp)]; exact h.x26
    · simp [hlen]; omega
    · refine v2.congr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show 4 - r - L.length = 0 by omega]
      rfl
    · rw [show 4 - r - 1 = 3 - r by omega]; exact m2
    · rw [g _ (by ao) (by ao) (by ao), hm _ (by ao) (by ao)]; exact h.h24
    · rw [g _ (by ao) (by ao) (by ao), hm _ (by ao) (by ao)]; exact h.z0
    · rw [g _ (by ao) (by ao) (by ao), hm _ (by ao) (by ao)]; exact h.z8
    · rw [g _ (by ao) (by ao) (by ao), hm _ (by ao) (by ao)]; exact h.z32
    · rw [g _ (by ao) (by ao) (by ao), hm _ (by ao) (by ao)]; exact h.z40
    · intro hjs hlt
      have e : (L ++ [a]).getD (4 - d) 0 = L.getD (4 - d) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [e]
      have hslot : DigAt t1 (slotV c i) (L.getD (4 - d) 0) := by
        by_cases hlt' : 4 - d < 4 - (r + 1)
        · exact (h.op hjs hlt').frame (n1 (fun h' => by omega)) (by unfold slotV; ao) (fun h => h) (fun h => h)
        · have heq : 4 - d = 3 - r := by omega
          have := o1 hjs heq
          rw [heq]
          rw [show 4 - (r + 1) = 3 - r by omega] at this
          exact this
      exact hslot.frame f2 (by unfold slotV; ao) (by intro h'; unfold slotV at h'; aoh)
        (by intro h'; unfold slotV at h'; aoh)
    · exact ((h.regs.trans r1).trans r2).mono (by simp [chainRegs])
    · refine ((h.frame.trans f1).trans f2).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with (hA | hA) | hA
      · exact hA
      · rcases hA with rfl | rfl <;> simp
      · rcases hA with hA | ⟨h3, h4⟩
        · left; constructor <;> omega
        · right; left; constructor <;> omega
    · intro hjs A hA h1 h2
      rw [f2.get hA (by intro h'; unfold slotV at h1 h2; aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
end ClaudeWCT.W9.Machine.Sign.SharedReuse


namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem node_run {c m : Nat} (hc:c<9) (hm:m<3) : runNode c m=some (expected c m) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact node_run_0 m hm
  |1,_=>exact node_run_1 m hm
  |2,_=>exact node_run_2 m hm
  |3,_=>exact node_run_3 m hm
  |4,_=>exact node_run_4 m hm
  |5,_=>exact node_run_5 m hm
  |6,_=>exact node_run_6 m hm
  |7,_=>exact node_run_7 m hm
  |8,_=>exact node_run_8 m hm

theorem readObl_holds (s : MachineState) {h : Nat} (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀o∈readObl,o.holds s := by
  have hb:=eval_sh5 s h18
  intro o ho
  simp only[readObl,List.mem_cons,List.not_mem_nil,or_false]at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)

theorem padReadObl_holds (s : MachineState) {c h off : Nat} (hc:c<9) (h4:4≤h) (h8:h<8)
    (ho:off=0 ∨ off=8) (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀o∈padReadObl c off,o.holds s := by
  have hb:=padShift_eval s h4 h8 h18
  intro o hm
  simp only[padReadObl,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]at hm
  rcases hm with hm|rfl
  · obtain ⟨n,hn,rfl⟩:=List.mem_map.mp hm
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hn
    rcases hn with rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ne_ofNat hb (by rcases ho with rfl|rfl <;> ao) (by ao) (by rcases ho with rfl|rfl <;> ao)
  · exact valid_ofNat hb (by rcases ho with rfl|rfl <;> omega)
      (by unfold MEMORY_BYTES;rcases ho with rfl|rfl <;> omega)

theorem obligations_hold (s : MachineState) {c h : Nat} (hc:c<9) (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀o∈obligations c (mode h),o.holds s := by
  unfold obligations
  split_ifs with hp
  · intro o ho
    rcases List.mem_append.mp ho with ho|ho
    · rcases List.mem_append.mp ho with ho|ho
      · exact padReadObl_holds s hc (mode_one hp.1).1 (mode_one hp.1).2 (Or.inr rfl) h18 o ho
      · exact padReadObl_holds s hc (mode_one hp.1).1 (mode_one hp.1).2 (Or.inl rfl) h18 o ho
    · exact readObl_holds s hh h18 o ho
  · simpa only[List.nil_append] using readObl_holds s hh h18

theorem branches_hold (s : MachineState) {h : Nat} (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀b∈branches (mode h),b.holds s := by
  unfold branches mode
  by_cases h8:8≤h
  · simp only[if_pos h8,ite_true]
    intro b hb
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
    subst b
    rw[br_ltu_holds]
    change BitVec.ult (s.getReg .x18) (BitVec.ofNat 64 8)=false
    rw[h18,ofNat_ult (by omega) (by decide)]
    simp[show ¬h<8 by omega]
  · simp only[if_neg h8]
    by_cases h4:4≤h
    all_goals simp only[h4,↓reduceIte,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide]
    all_goals intro b hb
    all_goals simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
    all_goals rcases hb with rfl|rfl <;> rw[br_ltu_holds]
    all_goals change BitVec.ult (s.getReg .x18) (BitVec.ofNat 64 _) = _
    all_goals rw[h18,ofNat_ult (by omega) (by decide)]
    all_goals simp_all

def writes (A : Nat) : Prop := ∃k<8,A=NODEW+8*k

def value (c m off : Nat) : E :=
  if off=0 then nodeLd 0 else if off=8 then nodeLd 8 else if off=16 then hdrLo c m else
  if off=24 then hdrHi m else if off=32 then padWord c m 0 else if off=40 then padWord c m 8 else
  if off=48 then nodeLd 16 else nodeLd 24

theorem mem_read (s : MachineState) (c m : Nat) {k : Nat} (hk:k<8) :
    memEval s (mem c m) (BitVec.ofNat 64 (NODEW+8*k))=(value c m (8*k)).eval s := by
  interval_cases k <;> simp[mem,value,memEval_mwc,NODEW]

theorem step_node {im : Image} {c h index : Nat}
    (hlook:LookOK im (look c)) (hc:c<9) (hh:h<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h18:s.getReg .x18=BitVec.ofNat 64 h)
    (h22:s.getReg .x22=BitVec.ofNat 64 index) :
    ∃t,Steps im s (cycles c (mode h)) (cycles c (mode h)) t ∧
      fetch im t=some (.base .ECALL) ∧ t.pc=pcOf (hashPc c) ∧
      t.getReg .x10=BitVec.ofNat 64 NODEW ∧ t.getReg .x11=BitVec.ofNat 64 64 ∧
      t.getReg .x12=BitVec.ofNat 64 NOUTW ∧
      (∀k,k<8 → t.getMem (BitVec.ofNat 64 (NODEW+8*k))=(value c (mode h) (8*k)).eval s) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28] ∧ Frame s t writes := by
  obtain ⟨hs,he⟩:=runA_pres hlook (node_run hc (mode_lt h)) s hpc
    (obligations_hold s hc hh h18) (branches_hold s hh h18)
  refine ⟨(expected c (mode h)).toState s,hs,he rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · intro k hk
    rw[expected,pres_getMem,mem_read s c (mode h) hk]
  · exact (pres_regsExcept (regs c (mode h)) _ _ _ _ _ _ s).mono (by simp[regs])
  · refine frame_of_memEval (ws:=mem c (mode h)) (fun _=>rfl) _ (fun p hm=>?_)
    simp only[mem,List.mem_cons,List.not_mem_nil,or_false]at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by ao)]
    all_goals unfold writes
    · exact ⟨5,by omega,by omega⟩
    · exact ⟨4,by omega,by omega⟩
    · exact ⟨3,by omega,by omega⟩
    · exact ⟨2,by omega,by omega⟩
    · exact ⟨7,by omega,by omega⟩
    · exact ⟨6,by omega,by omega⟩
    · exact ⟨1,by omega,by omega⟩
    · exact ⟨0,by omega,by omega⟩

end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def raw (c p : Nat) : Nat := if first c then p else 2*(p%64)+p/64
def mode (c j : Nat) : Nat := if j=127 then 2 else if j=126 ∧ first c=false then 1 else 0
def advance (c j : Nat) : Nat := if first c then j+1 else if j=126 then 1 else j+2

theorem raw_lt (c : Nat) {p : Nat} (hp:p<128) : raw c p<128 := by unfold raw;split <;> omega
theorem raw_eq127 (c : Nat) {p : Nat} (hp:p<128) : raw c p=127 ↔ p=127 := by
  unfold raw
  split <;> omega
theorem raw_advance (c : Nat) {p : Nat} (hp:p+1<128) : advance c (raw c p)=raw c (p+1) := by
  unfold raw advance
  split_ifs <;> omega

theorem mode_lt (c j : Nat) : mode c j<3 := by unfold mode;split_ifs <;> omega

theorem next_run {c m : Nat} (hc:c<9) (hm:m<3) (odd : Bool) : runNext c m odd=some (expected c m odd) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact next_run_0 m hm odd
  |1,_=>exact next_run_1 m hm odd
  |2,_=>exact next_run_2 m hm odd
  |3,_=>exact next_run_3 m hm odd
  |4,_=>exact next_run_4 m hm odd
  |5,_=>exact next_run_5 m hm odd
  |6,_=>exact next_run_6 m hm odd
  |7,_=>exact next_run_7 m hm odd
  |8,_=>exact next_run_8 m hm odd

/-- C1: the leaf stub tests the parity of the physical child (raw bit 0 on A, raw bit 1 on B/C). -/
theorem parityE_eval (s : MachineState) {c j : Nat} (hj:j<128) (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    (parityE c).eval s=BitVec.ofNat 64 (SharedLeaf.physical c j%2) := by
  have hfe:SharedLeaf.first c=first c:=rfl
  unfold parityE SharedLeaf.physical
  rw[hfe]
  by_cases hf:first c=true
  · rw[if_pos hf,if_pos hf]
    change s.getReg .x18 &&& BitVec.ofNat 64 1=_
    rw[h18]
    exact ofNat_and_one j (by omega)
  · rw[if_neg hf,if_neg hf]
    change BinOp.eval .srl (s.getReg .x18) (BitVec.ofNat 64 1) &&& BitVec.ofNat 64 1=_
    rw[binop_srl _ _ (by decide),h18,ofNat_shr _ _ (by omega),ofNat_and_one _ (by omega)]
    congr 1
    omega

theorem parity_holds (s : MachineState) {c j : Nat} (hj:j<128) (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    Br.holds s ⟨.ne,parityE c,cE 0,decide (SharedLeaf.physical c j%2=1)⟩ := by
  rw[br_ne_holds,parityE_eval s hj h18,eval_cE,ofNat_bne (by omega) (by decide),
    show decide (SharedLeaf.physical c j%2≠0)=decide (SharedLeaf.physical c j%2=1) from
      decide_eq_decide.mpr (by omega)]

theorem stub_obligations (s : MachineState) {A : Nat} (h12:s.getReg .x12=BitVec.ofNat 64 A)
    (hal:A%16=0) (hA:A+32≤MEMORY_BYTES) (odd : Bool) : ∀o∈stubObl odd,o.holds s := by
  cases odd
  · intro o ho
    simp only[stubObl,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false]at ho
    have hb:(E.reg .x12).eval s=BitVec.ofNat 64 A:=h12
    rcases ho with rfl|rfl|rfl|rfl <;> exact valid_ofNat hb (by omega) (by omega)
  · intro o ho
    simp only[stubObl,↓reduceIte,List.not_mem_nil]at ho

theorem memEval_stub (s : MachineState) {A : Nat} (h12:s.getReg .x12=BitVec.ofNat 64 A) (hA:A+32<2^64)
    (B : Nat) (hB:B<2^64) :
    memEval s (stubMem false) (BitVec.ofNat 64 B)=
      (if B=A+8 then s.getMem (BitVec.ofNat 64 (A+24))
       else if B=A then s.getMem (BitVec.ofNat 64 (A+16)) else s.getMem (BitVec.ofNat 64 B)) := by
  have ha:∀off,off<32 → Addr.eval s (a2A off)=BitVec.ofNat 64 (A+off):=by
    intro off _
    change s.getReg .x12+BitVec.ofNat 64 off=_
    rw[h12,ofNat_add_ofNat]
  have hl:∀off,off<32 → (a2Ld off).eval s=s.getMem (BitVec.ofNat 64 (A+off)):=by
    intro off _
    change s.getMem (s.getReg .x12+BitVec.ofNat 64 off)=_
    rw[h12,ofNat_add_ofNat]
  simp only[stubMem,Bool.false_eq_true,↓reduceIte,memEval]
  rw[ha 8 (by decide),ha 0 (by decide),hl 24 (by decide),hl 16 (by decide),Nat.add_zero]
  by_cases h8:B=A+8
  · subst h8;simp
  · have h8':BitVec.ofNat 64 B≠BitVec.ofNat 64 (A+8):=fun e=>h8 ((ofNat_inj hB (by omega)).mp e)
    rw[if_neg h8',if_neg h8]
    by_cases h0:B=A
    · subst h0;simp
    · have h0':BitVec.ofNat 64 B≠BitVec.ofNat 64 A:=fun e=>h0 ((ofNat_inj hB (by omega)).mp e)
      have h0'':BitVec.ofNat 64 B≠BitVec.ofNat 64 (A+0):=h0'
      first
      | rw[if_neg h0'',if_neg h0]
      | rw[if_neg h0',if_neg h0]

theorem branch_eq_holds (s : MachineState) {h k : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h)
    (hh:h<2^64) (hk:k<2^64) (b : Bool) :
    Br.holds s ⟨.eq,.reg .x18,cE k,b⟩ ↔ decide (h=k)=b := by
  change ((s.getReg .x18)==BitVec.ofNat 64 k)=b ↔ _
  rw[h18]
  have he:((BitVec.ofNat 64 h)==(BitVec.ofNat 64 k))=decide (h=k):=by
    by_cases he:h=k
    · subst k;simp
    · have hv:BitVec.ofNat 64 h≠BitVec.ofNat 64 k:=fun e=>he ((ofNat_inj hh hk).mp e)
      simp[he,hv]
  rw[he]

theorem branches_hold (s : MachineState) {c j : Nat} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) : ∀b∈branches c (mode c j),b.holds s := by
  unfold branches
  by_cases hf:first c=true
  · rw[if_pos hf]
    intro b hb
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
    subst b
    rw[br_ltu_holds,eval_x18p1 s h18,eval_cE,ofNat_ult (by omega) (by decide)]
    unfold mode
    split_ifs <;> simp_all <;> omega
  · have hf':first c=false:=Bool.eq_false_iff.mpr hf
    rw[if_neg hf]
    unfold mode
    by_cases h127:j=127
    · simp only[if_pos h127,ite_true]
      intro b hb
      simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
      subst b
      rw[branch_eq_holds s h18 (by omega) (by decide)]
      simp[h127]
    · simp only[if_neg h127]
      by_cases h126:j=126
      all_goals simp only[h126,hf',and_true,↓reduceIte,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (1:Nat)≠2 by decide,show (0:Nat)≠2 by decide]
      all_goals intro b hb
      all_goals simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
      all_goals rcases hb with rfl|rfl <;> rw[branch_eq_holds s h18 (by omega) (by decide)]
      all_goals simp_all

theorem nextE_eval (s : MachineState) {c j : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    (nextE c (mode c j)).eval s=BitVec.ofNat 64 (if j=127 then 127 else advance c j) := by
  unfold nextE mode advance
  by_cases h127:j=127
  · simp only[if_pos h127,ite_true]
    rfl
  · simp only[if_neg h127]
    by_cases hf:first c=true
    · have hm:¬(j=126 ∧ first c=false):=by simp[hf]
      rw[if_neg hm]
      simp only[show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (1:Nat)≠2 by decide,show (0:Nat)≠2 by decide,if_false,if_pos hf]
      exact eval_x18p1 s h18
    · have hf':first c=false:=Bool.eq_false_iff.mpr hf
      by_cases h126:j=126
      all_goals simp only[h126,hf',Bool.false_eq_true,and_true,↓reduceIte,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (1:Nat)≠2 by decide,show (0:Nat)≠2 by decide]
      · rfl
      · change s.getReg .x18+BitVec.ofNat 64 2=_
        rw[h18,ofNat_add_ofNat]

theorem step_next {im : Image} {c j : Nat} (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h18:s.getReg .x18=BitVec.ofNat 64 j)
    {A : Nat} (h12:s.getReg .x12=BitVec.ofNat 64 A) (hal:A%16=0) (hA:A+32≤MEMORY_BYTES) :
    ∃t k,Steps im s k k t ∧ k≤16 ∧
      t.pc=pcOf (if j=127 then nodePc c else leafI c) ∧
      t.getReg .x18=BitVec.ofNat 64 (if j=127 then 127 else advance c j) ∧
      (SharedLeaf.physical c j%2=0 → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 (A+16)) ∧
        t.getMem (BitVec.ofNat 64 (A+8))=s.getMem (BitVec.ofNat 64 (A+24))) ∧
      RegsExcept s t [.x6,.x18] ∧ Frame s t (fun B=>SharedLeaf.physical c j%2=0 ∧ (B=A ∨ B=A+8)) := by
  have hAl:A+32<2^64:=by unfold MEMORY_BYTES at hA;omega
  obtain ⟨hs,_⟩:=run_pres hlook (next_run hc (mode_lt c j) (decide (SharedLeaf.physical c j%2=1))) s hpc
    (stub_obligations s h12 hal hA _) (by
      intro b hb
      rcases List.mem_append.mp hb with hb|hb
      · exact branches_hold s hj h18 b hb
      · simp only[List.mem_singleton]at hb
        subst hb
        exact parity_holds s hj h18)
  refine ⟨(expected c (mode c j) (decide (SharedLeaf.physical c j%2=1))).toState s,
    cycles c (mode c j)+stubCycles c (decide (SharedLeaf.physical c j%2=1)),hs,?_,?_,?_,?_,
    pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · unfold cycles stubCycles;split_ifs <;> omega
  · change pcOf (if mode c j=2 then nodePc c else leafI c)=_
    by_cases h127:j=127
    · have hm:mode c j=2:=by unfold mode;rw[if_pos h127]
      rw[if_pos hm,if_pos h127]
    · have hm:mode c j≠2:=by
        unfold mode
        rw[if_neg h127]
        split <;> decide
      rw[if_neg hm,if_neg h127]
  · rw[expected,pres_getReg]
    exact nextE_eval s h18
  · intro hev
    have ho:decide (SharedLeaf.physical c j%2=1)=false:=decide_eq_false (by omega)
    rw[ho,expected,pres_getMem,pres_getMem,memEval_stub s h12 hAl A (by omega),
      memEval_stub s h12 hAl (A+8) (by omega),if_neg (show ¬A=A+8 by omega),if_pos (rfl:A=A),
      if_pos (rfl:A+8=A+8)]
    exact ⟨rfl,rfl⟩
  · intro B hB hn
    rw[expected,pres_getMem]
    by_cases hev:SharedLeaf.physical c j%2=0
    · have ho:decide (SharedLeaf.physical c j%2=1)=false:=decide_eq_false (by omega)
      rw[ho,memEval_stub s h12 hAl B hB,if_neg (fun h=>hn ⟨hev,Or.inr h⟩),if_neg (fun h=>hn ⟨hev,Or.inl h⟩)]
    · have ho:decide (SharedLeaf.physical c j%2=1)=true:=decide_eq_true (by omega)
      rw[ho]
      rfl
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem tail_run {c k : Nat} (hc:c<9) (hk:k<4) (back : Bool) : runTail c k back=some (expected c k back) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact tail_run_0 k hk back
  |1,_=>exact tail_run_1 k hk back
  |2,_=>exact tail_run_2 k hk back
  |3,_=>exact tail_run_3 k hk back
  |4,_=>exact tail_run_4 k hk back
  |5,_=>exact tail_run_5 k hk back
  |6,_=>exact tail_run_6 k hk back
  |7,_=>exact tail_run_7 k hk back
  |8,_=>exact tail_run_8 k hk back

theorem cls_lt (c h : Nat) : cls c h<4 := by unfold cls;split_ifs <;> omega

theorem ltB_holds (s : MachineState) {h n : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (hh:h<2^64)
    (hn:n<2^64) (d : Bool) : (ltB n d).holds s ↔ decide (h<n)=d := by
  unfold ltB
  rw[br_ne_holds,eval_cE]
  change ((if BitVec.ult (s.getReg .x18) (BitVec.ofNat 64 n) then (1:Word) else 0) != BitVec.ofNat 64 0)=d ↔ _
  rw[h18,ofNat_ult hh hn]
  by_cases hl:h<n
  · rw[if_pos (decide_eq_true hl),show ((1:Word) != BitVec.ofNat 64 0)=true by decide,decide_eq_true hl]
  · rw[if_neg (show ¬decide (h<n)=true from fun hd=>hl (of_decide_eq_true hd)),
      show ((0:Word) != BitVec.ofNat 64 0)=false by decide,decide_eq_false hl]

theorem oddB_holds (s : MachineState) {h : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (hh:h<2^64) (d : Bool) :
    (oddB d).holds s ↔ decide (h%2=1)=d := by
  unfold oddB
  rw[br_ne_holds,eval_cE]
  change ((s.getReg .x18 &&& BitVec.ofNat 64 1) != BitVec.ofNat 64 0)=d ↔ _
  rw[h18,ofNat_and_one h hh,ofNat_bne (by omega) (by decide),
    show decide (h%2≠0)=decide (h%2=1) from decide_eq_decide.mpr (by omega)]

/-- Stage 2 (C stub): `addi t1,s2,-2; beq t1,zero` tests `heap = 2`. -/
theorem eq2B_holds (s : MachineState) {h : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (hh:h<2^64) (d : Bool) :
    (eq2B d).holds s ↔ decide (h=2)=d := by
  unfold eq2B
  change ((s.getReg .x18+BitVec.ofNat 64 (2^64-2) == BitVec.ofNat 64 0)=d) ↔ _
  rw[h18,ofNat_add_ofNat]
  have e:(BitVec.ofNat 64 (h+(2^64-2)) == BitVec.ofNat 64 0)=decide (h=2):=by
    by_cases h2:h=2
    · subst h2
      rw[decide_eq_true rfl]
      decide
    · have hne:BitVec.ofNat 64 (h+(2^64-2))≠BitVec.ofNat 64 0:=by
        intro he
        have ht:=congrArg BitVec.toNat he
        simp only[BitVec.toNat_ofNat] at ht
        omega
      rw[decide_eq_false h2]
      exact beq_eq_false_iff_ne.mpr hne
  rw[e]

/-- The stub's first test of coordinate `c`: the class-0 (HIGH top heap) condition of `cls`. -/
theorem topB_holds (s : MachineState) {c h : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (hh:h<2^64) (d : Bool) :
    (topB c d).holds s ↔ decide ((c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2))=d := by
  have hl:halfLimit c<2^64:=by unfold halfLimit;split <;> omega
  unfold topB
  by_cases hc:c=8
  · rw[if_pos hc,eq2B_holds s h18 hh]
    have e:decide ((c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2))=decide (h=2):=
      decide_eq_decide.mpr ⟨fun hx=>by rcases hx with hx|hx <;> omega,fun hx=>Or.inr ⟨hc,hx⟩⟩
    rw[e]
  · rw[if_neg hc,ltB_holds s h18 hh hl]
    have e:decide ((c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2))=decide (h<halfLimit c):=
      decide_eq_decide.mpr ⟨fun hx=>by rcases hx with hx|hx <;> omega,fun hx=>Or.inl ⟨hc,hx⟩⟩
    rw[e]

theorem stub_branches_hold (s : MachineState) {c h : Nat} (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀b∈stubBranches c (cls c h),b.holds s := by
  -- (case split by hand, no split_ifs: see the stage-1 notes on `False` literals)
  have L16:=ltB_holds s h18 (show h<2^64 by omega) (show 16<2^64 by decide)
  have T:=topB_holds s (c:=c) h18 (show h<2^64 by omega)
  have O:=oddB_holds s h18 (show h<2^64 by omega)
  have e0:stubBranches c 0=[topB c true]:=rfl
  have e1:stubBranches c 1=[ltB 16 true,topB c false]:=rfl
  have e2:stubBranches c 2=[oddB true,ltB 16 false,topB c false]:=rfl
  have e3:stubBranches c 3=[oddB false,ltB 16 false,topB c false]:=rfl
  intro b hb
  by_cases hP:(c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2)
  · have hk:cls c h=0:=by unfold cls;rw[if_pos hP]
    rw[hk,e0] at hb
    simp only[List.mem_cons,List.not_mem_nil,or_false] at hb
    subst hb
    exact (T true).mpr (decide_eq_true hP)
  · have hn:=(T false).mpr (decide_eq_false hP)
    by_cases h16:h<16
    · have hk:cls c h=1:=by unfold cls;rw[if_neg hP,if_pos h16]
      rw[hk,e1] at hb
      simp only[List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl
      · exact (L16 true).mpr (decide_eq_true h16)
      · exact hn
    · by_cases hodd:h%2=1
      · have hk:cls c h=2:=by unfold cls;rw[if_neg hP,if_neg h16,if_pos hodd]
        rw[hk,e2] at hb
        simp only[List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl
        · exact (O true).mpr (decide_eq_true hodd)
        · exact (L16 false).mpr (decide_eq_false h16)
        · exact hn
      · have hk:cls c h=3:=by unfold cls;rw[if_neg hP,if_neg h16,if_neg hodd]
        rw[hk,e3] at hb
        simp only[List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl
        · exact (O false).mpr (decide_eq_false hodd)
        · exact (L16 false).mpr (decide_eq_false h16)
        · exact hn

theorem cycles_le (c k : Nat) : cycles c k≤22 := by unfold cycles;split_ifs <;> omega

theorem step_tail {im : Image} {c h : Nat} (hlook:LookOK im (look c)) (hc:c<9)
    (hh1:1≤h) (hh:h<128) (back : Bool) (hback:back=decide (h-1≠limit c))
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h18:s.getReg .x18=BitVec.ofNat 64 h) :
    ∃t,Steps im s (cycles c (cls c h)) (cycles c (cls c h)) t ∧ cycles c (cls c h)≤22 ∧
      t.pc=pcOf (if back then nodePc c else finishPc c) ∧ t.getReg .x18=BitVec.ofNat 64 (h-1) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW+16*h))=
        s.getMem (BitVec.ofNat 64 (NOUTW+halfOff (clsHigh c (cls c h)))) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW+16*h+8))=
        s.getMem (BitVec.ofNat 64 (NOUTW+halfOff (clsHigh c (cls c h))+8)) ∧
      RegsExcept s t [.x6,.x7,.x18,.x28,.x29] ∧
      Frame s t (fun A=>A=HEAPW+16*h+8 ∨ A=HEAPW+16*h) := by
  have hb:=eval_sh4 s h18
  have hm1:=eval_x18m1 s h18 hh1 (by omega)
  have hlim:limit c<2^64:=by unfold limit;split <;> omega
  obtain ⟨hs,_⟩:=run_pres hlook (tail_run hc (cls_lt c h) back) s hpc (by
    intro o ho
    simp only[List.mem_cons,List.not_mem_nil,or_false]at ho
    rcases ho with rfl|rfl <;> exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)) (by
    intro b hbm
    simp only[branches,List.mem_cons]at hbm
    rcases hbm with rfl|hbm
    · rw[br_ne_holds,hm1,eval_cE,ofNat_bne (by omega) hlim,hback]
    · exact stub_branches_hold s hh h18 b hbm)
  have hm:∀a,((expected c (cls c h) back).toState s).getMem a=
      memEval s [mwc (HEAPW+16*h+8) (outWord (clsHigh c (cls c h)) 8),
        mwc (HEAPW+16*h) (outWord (clsHigh c (cls c h)) 0)] a:=by
    intro a
    change memEval s [(heapAddr 8,outWord (clsHigh c (cls c h)) 8),(heapAddr 0,outWord (clsHigh c (cls c h)) 0)] a=_
    simp only[memEval,Addr.eval,heapAddr,mwc,hb,ofNat_add_ofNat]
    rw[show 16*h+(HEAPW+8)=HEAPW+16*h+8 by omega,show 16*h+(HEAPW+0)=HEAPW+16*h by omega]
    rfl
  refine ⟨(expected c (cls c h) back).toState s,hs,cycles_le c _,rfl,?_,?_,?_,pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · rw[expected,pres_getReg]
    exact hm1
  · rw[hm,memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw[hm,memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · refine frame_of_memEval hm _ (fun p hp=>?_)
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hp
    rcases hp with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by ao)] <;> simp
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem finish_run {c : Nat} (hc:c<9) : runFinish c=some (expected c) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact finish_run_0
  |1,_=>exact finish_run_1
  |2,_=>exact finish_run_2
  |3,_=>exact finish_run_3
  |4,_=>exact finish_run_4
  |5,_=>exact finish_run_5
  |6,_=>exact finish_run_6
  |7,_=>exact finish_run_7
  |8,_=>exact finish_run_8

def physical (c j : Nat) : Nat := if first c then j else j/2+64*(j%2)

theorem physical_eval (s : MachineState) {c j : Nat} (hj:j<128) (h24:s.getReg .x24=BitVec.ofNat 64 j) :
    (physicalE c).eval s=BitVec.ofNat 64 (physical c j) := by
  unfold physicalE physical
  split
  · exact h24
  · unfold loBit
    rw[eval_bin,eval_bin,eval_cE,binop_srl _ _ (by decide),eval_bin,eval_cE,binop_sll _ _ (by decide)]
    change ((s.getReg .x24 >>> 1) + ((s.getReg .x24 &&& BitVec.ofNat 64 1) <<< 6))=_
    rw[h24,ofNat_shr _ _ (by omega),ofNat_and_one j (by omega),ofNat_shl,ofNat_add_ofNat]
    congr 1
    ring

theorem target_bound {c : Nat} (hc:c<9) : target c+64<2^64 := by
  unfold target FORW;split <;> omega

theorem mem_read (s : MachineState) {c k : Nat} (hc:c<9) (hk:k<nwords c) :
    memEval s (mem c) (BitVec.ofNat 64 (target c+8*k))=s.getMem (BitVec.ofNat 64 (source c+8*k)) := by
  have hb:=target_bound hc
  unfold mem nwords at *
  split_ifs at hk ⊢ with hf
  all_goals interval_cases k
  all_goals simp (disch:=omega) [List.range_succ,memEval_mwc,memEval_nil'] <;> rfl

def writes (c A : Nat) : Prop := ∃k<nwords c,A=target c+8*k

theorem step_finish {im : Image} {c j : Nat} (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h24:s.getReg .x24=BitVec.ofNat 64 j) :
    ∃t,Steps im s (words c).length (words c).length t ∧ (words c).length≤21 ∧
      t.pc=pcOf (pathPc c) ∧ t.getReg .x24=BitVec.ofNat 64 (128+physical c j) ∧
      (∀k,k<nwords c→t.getMem (BitVec.ofNat 64 (target c+8*k))=s.getMem (BitVec.ofNat 64 (source c+8*k))) ∧
      RegsExcept s t [.x6,.x7,.x24,.x28,.x29] ∧ Frame s t (writes c) := by
  obtain ⟨hs,_⟩:=runA_pres hlook (finish_run hc) s hpc (no_obl s) (no_br s)
  refine ⟨(expected c).toState s,hs,?_,rfl,?_,?_,pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · have h:∀c,c<9→(words c).length≤21:=by decide +kernel
    exact h c hc
  · rw[expected,pres_getReg]
    change (physicalE c).eval s+BitVec.ofNat 64 128=_
    rw[physical_eval s hj h24,ofNat_add_ofNat,Nat.add_comm]
  · intro k hk
    rw[expected,pres_getMem,mem_read s hc hk]
  · refine frame_of_memEval (ws:=mem c) (fun _=>rfl) _ (fun p hp=>?_)
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hp
    have hk':k<nwords c:=List.mem_range.mp (List.mem_reverse.mp hk)
    have hb:=target_bound hc
    have hn:nwords c≤8:=by unfold nwords;split <;> omega
    refine ⟨rfl,?_⟩
    rw[off_mwc _ _ (by omega)]
    exact ⟨k,hk',rfl⟩
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem path_run {c level : Nat} (hc:c<9) (hl:level<levels c) : runPath c level=some (expected c level) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact path_run_0 level hl
  |1,_=>exact path_run_1 level hl
  |2,_=>exact path_run_2 level hl
  |3,_=>exact path_run_3 level hl
  |4,_=>exact path_run_4 level hl
  |5,_=>exact path_run_5 level hl
  |6,_=>exact path_run_6 level hl
  |7,_=>exact path_run_7 level hl
  |8,_=>exact path_run_8 level hl

theorem eval_offset (s : MachineState) {sel : Nat} (h24:s.getReg .x24=BitVec.ofNat 64 (128+sel)) (hsel:sel<128)
    (l : Nat) (hl:l<7) : (offsetE l).eval s=BitVec.ofNat 64 (16*(2^(7-l)+(sel/2^l ^^^1))) := by
  show BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .srl (s.getReg .x24) (BitVec.ofNat 64 l))
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 4)=_
  rw[binop_sll _ _ (by norm_num),binop_srl _ _ (by omega),h24,ofNat_shr _ _ (by omega),Nat.add_comm 128 sel]
  simp only[BinOp.eval]
  rw[show BitVec.ofNat 64 ((sel+128)/2^l) ^^^ BitVec.ofNat 64 1=BitVec.ofNat 64 ((sel+128)/2^l ^^^1) by
    apply BitVec.eq_of_toNat_eq
    have h1:(sel+128)/2^l<2^64:=lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have h2:(sel+128)/2^l ^^^1<2^64:=Nat.xor_lt_two_pow h1 (by norm_num)
    simp only[BitVec.toNat_xor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2],
    pathIdx_eq sel hsel l hl,ofNat_shl]
  congr 1
  ring

theorem eval_word (s : MachineState) {sel l : Nat} (h24:s.getReg .x24=BitVec.ofNat 64 (128+sel))
    (hsel:sel<128) (hl:l<7) (off : Nat) :
    (word l off).eval s=s.getMem (BitVec.ofNat 64 (HEAPW+16*(2^(7-l)+(sel/2^l ^^^1))+off)) := by
  change s.getMem ((offsetE l).eval s+BitVec.ofNat 64 (HEAPW+off))=_
  rw[eval_offset s h24 hsel l hl,ofNat_add_ofNat]
  congr 2
  ring

theorem levels_bound (c : Nat) : levels c≤7 := by unfold levels;split <;> omega

theorem step_path {im : Image} {c l sel : Nat} (hlook:LookOK im (look c)) (hc:c<9)
    (hl:l<levels c) (hsel:sel<128) (s : MachineState)
    (hpc:s.pc=pcOf (entry c l)) (h24:s.getReg .x24=BitVec.ofNat 64 (128+sel)) :
    ∃t,Steps im s 12 12 t ∧ t.pc=pcOf (entry c (l+1)) ∧
      t.getMem (BitVec.ofNat 64 (target c l))=s.getMem (BitVec.ofNat 64 (HEAPW+16*(2^(7-l)+(sel/2^l ^^^1)))) ∧
      t.getMem (BitVec.ofNat 64 (target c l+8))=s.getMem (BitVec.ofNat 64 (HEAPW+16*(2^(7-l)+(sel/2^l ^^^1))+8)) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun A=>A=target c l+8∨A=target c l) := by
  have hl7:l<7:=lt_of_lt_of_le hl (levels_bound c)
  have hb:=eval_offset s h24 hsel l hl7
  have hlt:=pathHeap_lt sel l hsel hl7
  obtain ⟨hs,_⟩:=runA_pres hlook (path_run hc hl) s hpc (by
    intro o ho
    simp only[List.mem_cons,List.not_mem_nil,or_false]at ho
    rcases ho with rfl|rfl
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)) (no_br s)
  have tb:target c l+8<2^64:=by unfold target slotV;ao
  refine ⟨_,hs,rfl,?_,?_,pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · rw[pres_getMem,memEval_mwc_ne _ _ _ (by omega) (by omega) (by omega),memEval_mwc_self _ _ _ _ (by omega),eval_word s h24 hsel hl7,Nat.add_zero]
  · rw[pres_getMem,memEval_mwc_self _ _ _ _ (by omega),eval_word s h24 hsel hl7]
  · refine frame_of_memEval (fun _=>rfl) _ (fun p hp=>?_)
    simp only[expected,pres,List.mem_cons,List.not_mem_nil,or_false]at hp
    rcases hp with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by omega)] <;> simp
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem end_run {c : Nat} (hc:c<9) : runEnd c=some (expected c) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact end_run_0
  |1,_=>exact end_run_1
  |2,_=>exact end_run_2
  |3,_=>exact end_run_3
  |4,_=>exact end_run_4
  |5,_=>exact end_run_5
  |6,_=>exact end_run_6
  |7,_=>exact end_run_7
  |8,_=>exact end_run_8

theorem step_end {im : Image} {c : Nat} (hlook:LookOK im (look c)) (hc:c<9)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) :
    ∃t k,Steps im s k k t ∧ k≤5 ∧ t.pc=pcOf (nextPc c) ∧
      (first c=true → DigAt t (target c) 0) ∧ RegsExcept s t [.x29] ∧
      Frame s t (fun A=>first c=true ∧ (A=target c+8 ∨ A=target c)) := by
  obtain ⟨hs,_⟩:=run_pres hlook (end_run hc) s hpc (no_obl s) (no_br s)
  refine ⟨_,_,hs,?_,rfl,?_,?_,?_⟩
  · split <;> omega
  · intro hf
    change DigAt ((expected c).toState s) (target c) 0
    simp only[expected,if_pos hf]
    refine ⟨?_,?_⟩
    · rw[pres_getMem,memEval_mwc_ne _ _ _ (by unfold target slotP;ao) (by unfold target slotP;ao) (by omega),memEval_mwc_self _ _ _ _ (by unfold target slotP;ao)]
      rfl
    · rw[pres_getMem,memEval_mwc_self _ _ _ _ (by unfold target slotP;ao)]
      rfl
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by split <;> simp)
  · refine frame_of_memEval (fun _=>rfl) _ (fun p hp=>?_)
    change p∈(if first c then [mwc (target c+8) (cE 0),mwc (target c) (cE 0)] else []) at hp
    split_ifs at hp with hf
    · simp only[List.mem_cons,List.not_mem_nil,or_false]at hp
      rcases hp with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by unfold target slotP;ao)] <;> simp[hf]
    · simp at hp
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem lwu_inside (c : Nat) (hc:c < 9) : cbase c < lwuI c ∧ lwuI c < lI c := by
  have h:∀c,c < 9 → cbase c < lwuI c ∧ lwuI c < lI c:=by decide +kernel
  exact h c hc
theorem step_lwu {im : Image} (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState)
    (hpc : s.pc = pcOf (lwuI c)) {f : Nat} (hf : f < 16384) (h28 : s.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * f))
    (ht : TableAt s) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (lwuI c + 1) ∧ t.getReg .x25 = BitVec.ofNat 64 (pkAt f) ∧
      RegsExcept s t [.x25] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  have hlw := lwuI_lt c hc
  have hpc' : (s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : coordLook c ((s.pc.toNat - 0x1000) / 4) = some 0x000e6c83 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * lwuI c - 0x1000) / 4 = lwuI c by omega]
    rw [coordLook, if_pos (lwu_inside c hc)]
    exact lwu_wordW c hc
  have hf' : fetch im s = some (.base (.LWU .x25 .x28 0)) :=
    (fetch_of_look hl hpc' hw s rfl).trans decode_lwu
  have hcl : classify (.base (.LWU .x25 .x28 0)) = some (.load .wu .x25 .x28 (signExtend12 0)) := rfl
  have hacc : accessValid (s.getReg .x28 + signExtend12 0) LoadKind.wu.width = true := by
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show TBL + 4 * f < 2 ^ 64 by unfold TBL; omega), MEMORY_BYTES]
    unfold TBL; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact SigGolfCandidate.T3M.pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    simp only [LoadKind.read, e, table_word ht hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := pkAt_lt f
    omega
  · intro r hr
    have hne : Reg.x25 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp

end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem field_run {c : Nat} (hc:c < 9) : runField c=some (expected c) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact field_run_0
  |1,_=>exact field_run_1
  |2,_=>exact field_run_2
  |3,_=>exact field_run_3
  |4,_=>exact field_run_4
  |5,_=>exact field_run_5
  |6,_=>exact field_run_6
  |7,_=>exact field_run_7
  |8,_=>exact field_run_8

theorem fields_bounded (c : Nat) (hc:c < 9) :
    rawBit c < 256 ∧ rankBit c < 256 ∧ rawBit c%64+7 ≤ 64 ∧ rankBit c%64+10 ≤ 64 ∧ (words c).length+1 ≤ 18 := by
  have h:∀c,c < 9 → rawBit c < 256 ∧ rankBit c < 256 ∧ rawBit c%64+7 ≤ 64 ∧ rankBit c%64+10 ≤ 64 ∧ (words c).length+1 ≤ 18:=by decide +kernel
  exact h c hc

theorem field_eval (s : MachineState) (a : BitVec 256) (ha:OutAt s NBUF a) {bit width : Nat}
    (hb:bit < 256) (hw:width ≤ 64) (hfit:bit%64+width ≤ 64) :
    (fieldE bit width).eval s=BitVec.ofNat 64 (a.toNat/2^bit%2^width) := by
  have hm:=ha (bit/64) (by omega)
  simp only[fieldE,ldc,E.eval,cE,hm]
  rw[SearchM.srl_eval _ _ (by omega),SearchM.and_eval,SearchM.ofNat_and_mask _ width hw]
  congr 1
  rw[BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    SearchM.mod64_div_mod _ _ _ hfit,Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega

theorem step_field {im : Image} {c : Nat} (hl:LookOK im (look c)) (hc:c < 9)
    (s : MachineState) (hpc:s.pc=pcOf (cbase c)) {a : BitVec 256} (ha:OutAt s NBUF a) :
    ∃t n,Steps im s n n t ∧ n ≤ 18 ∧ t.pc=pcOf (lwuI c) ∧
      t.getReg .x24=BitVec.ofNat 64 (a.toNat/2^(rawBit c)%128) ∧
      t.getReg .x28=BitVec.ofNat 64 (TBL+4*(a.toNat/2^(rankBit c)%1024)) ∧
      RegsExcept s t [.x6,.x24,.x25,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨st,_⟩:=run_pres hl (field_run hc) s hpc (no_obl s) (no_br s)
  obtain ⟨hr,ht,hfr,hft,hn⟩:=fields_bounded c hc
  refine ⟨_,_,st,hn,rfl,?_,?_,?_,fun A _ _=>rfl⟩
  · rw[pres_getReg];exact field_eval s a ha hr (by decide) hfr
  · rw[pres_getReg]
    change BinOp.eval .add (BinOp.eval .sll ((fieldE (rankBit c) 10).eval s) (BitVec.ofNat 64 2)) (BitVec.ofNat 64 TBL)=_
    rw[field_eval s a ha ht (by decide) hft,binop_sll _ _ (by decide),ofNat_shl]
    simp only[BinOp.eval,ofNat_add_ofNat]
    congr 1
    ring
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedBoundary
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
def forLook (n : Nat) : Option (BitVec 32) :=
  if 20715≤n ∧ n<20743 then tailCode[n-20715]? else trampLook n
def runFor : Option PRes := run forLook [370] 20715 []
theorem runFor_eq : runFor=some expFor := optBeq_eq (show optBeq runFor expFor=true by decide +kernel)
variable {im : Image}
theorem step_SK (hcode : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11175) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (cbase 0) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 8 * k))) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 32 + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 16 + 8 * k))) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = PRIVW + 40 ∨ A = PRIVW + 32 ∨ A = PRIVW + 8 ∨ A = PRIVW) := by
  obtain ⟨hst, -⟩ := run_pres hcode runSK_eq s hpc (no_obl s) (no_br s)
  have hm : ∀ a, ((expSK).toState s).getMem a = memEval s expSK.st.mem a := fun a => rfl
  refine ⟨_, hst, rfl, fun k hk => ?_, fun k hk => ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · refine frame_of_memEval hm _ (fun p hp => ?_)
    simp only [expSK, pres, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [mwc, PRIVW, BitVec.toNat_ofNat] <;> decide
theorem step_For (hcode : LookOK im forLook) (s : MachineState) (hpc : s.pc = pcOf 20715) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 370 ∧
      t.getMem (BitVec.ofNat 64 FOUT) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8)) ∧
      t.getMem (BitVec.ofNat 64 (FOUT + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 8)) ∧
      t.getMem (BitVec.ofNat 64 0x20290) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 16)) ∧
      t.getMem (BitVec.ofNat 64 (0x20290 + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = 0x20290 + 8 ∨ A = 0x20290 ∨ A = FOUT + 8 ∨ A = FOUT) := by
  obtain ⟨hst', -⟩ := run_pres hcode runFor_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expFor, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao

end ClaudeWCT.W9.Machine.Sign.SharedBoundary


namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
theorem global_checked (m : Bool) : globalCheck m=true := by cases m;exact global_sign;exact global_expand
theorem field_checked (m : Bool) (k : Nat) (hk:k < 9) : fieldCheck m k=true := by
  have h:(List.range 9).all (fieldCheck m)=true:=by cases m;exact fields_sign;exact fields_expand
  exact List.all_eq_true.mp h k (List.mem_range.mpr hk)
theorem head_run (m d : Bool) : run (look m) [trial m+3,fail m] (trial m) [.br d]=some (expectedHead m d) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem trial_run (m : Bool) : run (look m) [] (trial m+3) []=some (expectedTrial m) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem gate_run (m d : Bool) : run (look m) [next m,base m+21] (base m+15) [.br d]=some (expectedGate m d) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem init_run (m : Bool) : run (look m) [firstField m] (base m+21) []=some (expectedInit m) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem cap_run (m d : Bool) : run (look m) [next m,accepted m] (cap m) [.br d]=some (expectedCap m d) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem next_run (m : Bool) : run (look m) [trial m] (next m) []=some (expectedNext m) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem rank_run (m : Bool) (k : Nat) (hk:k < 9) (d : Bool) :
    run (look m) [next m,field m k+5] (field m k) [.br d]=some (expectedRank m k d) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem rankAddr_run (m : Bool) (k : Nat) (hk:k < 9) :
    run (look m) [rankLoad m k] (field m k+5) []=some (expectedRankAddr m k) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem corrPrep_run (m : Bool) (k : Nat) (hk:k < 9) :
    run (look m) [corrLoad m k] (rankLoad m k+1) []=some (expectedCorrPrep m k) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem sum_run (m : Bool) (k : Nat) (hk:k < 9) :
    run (look m) [field m (k+1)] (corrLoad m k+1) []=some (expectedSum m k) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

theorem field_eval (s : MachineState) (a : BitVec 256) (ha:OutAt s NBUF a)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) {bit width : Nat}
    (hb:bit < 256) (hw:width ≤ 64) (hfit:bit%64+width ≤ 64) :
    (fieldE bit width).eval s=BitVec.ofNat 64 (a.toNat/2^bit%2^width) := by
  have hm:=ha (bit/64) (by omega)
  simp only[fieldE,E.eval,Addr.toE_eval,fieldAddr,Addr.eval,h17,ofNat_add_ofNat,hm,cE]
  rw[SearchM.srl_eval _ _ (by omega),SearchM.and_eval,SearchM.ofNat_and_mask _ width hw]
  congr 1
  rw[BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    SearchM.mod64_div_mod _ _ _ hfit,Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega

theorem head_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (trial m))
    (i : Nat) (hi:i ≤ 2^21) (h19:s.getReg .x19=BitVec.ofNat 64 i) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if i < 2^21 then pcOf (trial m+3) else pcOf (fail m)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hbr : ∀b∈(expectedHead m (decide (2^21 ≤ i))).brs,b.holds s := by
    intro b hb
    simp only[expectedHead,pres,pres2,List.mem_singleton] at hb
    subst hb
    simp only [Br.holds,CmpOp.eval,E.eval,cE,h19,BitVec.ult,toNat_ofNat_lt (by omega : i < 2^64),
      toNat_ofNat_lt (by decide : 2^21 < 2^64)]
    change (!decide (i < 2097152))=decide (2097152 ≤ i)
    by_cases h:i < 2097152
    · have h2:¬2097152 ≤ i:=by omega
      simp [h,h2]
    · have h2:2097152 ≤ i:=by omega
      simp [h,h2]
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (head_run m _) s hpc rfl hbr rfl
  refine ⟨_,hs,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · rw[hp];simp only[expectedHead,pres,pres2]
    simp only [decide_eq_true_eq]
    split_ifs <;> first | rfl | omega
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)

theorem trial_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (trial m+3))
    (i : Nat) (h19:s.getReg .x19=BitVec.ofNat 64 i) :
    ∃t,Steps im s 9 9 t ∧ fetch im t=some (.base .ECALL) ∧ t.pc=pcOf (base m+14) ∧
      t.getReg .x10=BitVec.ofNat 64 DIG ∧ t.getReg .x11=BitVec.ofNat 64 64 ∧
      t.getReg .x12=BitVec.ofNat 64 NBUF ∧
      t.getMem (BitVec.ofNat 64 (DIG+16))=0 ∧ t.getMem (BitVec.ofNat 64 (DIG+24))=BitVec.ofNat 64 i ∧
      RegsExcept s t [.x10,.x11,.x12,.x28] ∧ Frame s t (fun A=>A=DIG+24 ∨ A=DIG+16) := by
  obtain ⟨hs,hp,he,hr,hm⟩:=SearchM.piece hl (trial_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,he rfl,hp,by rw[hr];rfl,by rw[hr];rfl,by rw[hr];rfl,?_,?_,?_,?_⟩
  · rw[hm]
    change memEval s [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] _=0
    rw[memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw[hm]
    change memEval s [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] _=BitVec.ofNat 64 i
    rw[memEval_mwc_self _ _ _ _ (by ao)]
    exact h19
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)
  · refine frame_of_memEval (fun a=>rfl) _ (fun q hq=>?_)
    simp only[expectedTrial,pres,pres2,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by ao)] <;> ao

theorem next_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (next m))
    (i : Nat) (h19:s.getReg .x19=BitVec.ofNat 64 i) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf (trial m) ∧ t.getReg .x19=BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (next_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · rw[hr]
    change s.getReg .x19+BitVec.ofNat 64 1=_
    rw[h19,ofNat_add_ofNat]
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {im : Image}

theorem lbu_spec (s : MachineState) (r : Reg) (off : BitVec 12) (A value : Nat)
    (hf:fetch im s=some (.base (.LBU .x6 r off)))
    (hA:s.getReg r+signExtend12 off=BitVec.ofNat 64 A) (hbound:A < MEMORY_BYTES)
    (hbyte:s.getByte (BitVec.ofNat 64 A)=BitVec.ofNat 8 value) (hv:value < 256) :
    ∃t,Steps im s 1 1 t ∧ t.pc=s.pc+4 ∧ t.getReg .x6=BitVec.ofNat 64 value ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hclass:classify (.base (.LBU .x6 r off))=some (.load .bu .x6 r (signExtend12 off)):=rfl
  have hacc:accessValid (s.getReg r+signExtend12 off) LoadKind.bu.width=true := by
    rw[hA]
    simp only[accessValid,rangeValid,LoadKind.width,Bool.and_eq_true,decide_eq_true_eq,
      toNat_ofNat_lt (by unfold MEMORY_BYTES at hbound;omega : A < 2^64),MEMORY_BYTES]
    unfold MEMORY_BYTES at hbound
    omega
  refine ⟨_,Steps.step hf (by rw[classify_sound hclass];simp only[Micro.exec,hacc,if_true];rfl) (Steps.refl _),rfl,?_,?_,?_⟩
  · rw[MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide)]
    simp only[LoadKind.read,hA,hbyte]
    apply BitVec.eq_of_toNat_eq
    simp only[BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro reg hr
    have hn:Reg.x6 ≠ reg:=fun h=>hr (by simp[h])
    rw[MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ hn]
  · intro A _ _;simp

theorem rank_lbu (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (rankLoad m k)) :
    fetch im s=some (.base (.LBU .x6 (addrReg m) 0)) := by
  have hb:rankLoad m k < 50000:=by cases m <;> simp [rankLoad,field,firstField] <;> omega
  have hlook:look m (rankLoad m k)=some (rankLbuWord m) := by
    have h:=field_checked m k hk
    simp only[fieldCheck,Bool.and_eq_true]at h
    have he:(look m (rankLoad m k)==some (rankLbuWord m))=true:=by tauto
    exact eq_of_beq he
  have hpc':(s.pc.toNat < 0x1000 || s.pc.toNat%4 != 0)=false:=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega)];simp
  have hw:look m ((s.pc.toNat-0x1000)/4)=some (rankLbuWord m):=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega),show (0x1000+4*rankLoad m k-0x1000)/4=rankLoad m k by omega]
    exact hlook
  apply (fetch_of_look hl hpc' hw s rfl).trans
  cases m <;> rfl

theorem corr_lbu (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (corrLoad m k)) :
    fetch im s=some (.base (.LBU .x6 (addrReg m)
      (BitVec.ofNat 12 (if m then 0 else correctionOffset m k)))) := by
  have hb:corrLoad m k < 50000:=by cases m <;> simp [corrLoad,field,firstField] <;> omega
  have hlook:look m (corrLoad m k)=some (corrLbuWord m k) := by
    have h:=field_checked m k hk
    simp only[fieldCheck,Bool.and_eq_true]at h
    have he:(look m (corrLoad m k)==some (corrLbuWord m k))=true:=by tauto
    exact eq_of_beq he
  have hpc':(s.pc.toNat < 0x1000 || s.pc.toNat%4 != 0)=false:=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega)];simp
  have hw:look m ((s.pc.toNat-0x1000)/4)=some (corrLbuWord m k):=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega),show (0x1000+4*corrLoad m k-0x1000)/4=corrLoad m k by omega]
    exact hlook
  apply (fetch_of_look hl hpc' hw s rfl).trans
  cases m <;> simp only[corrLbuWord,correctionOffset,addrReg,Bool.false_eq_true,if_false,if_true]
  · split <;> rfl
  · rfl

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

def gateN (a : BitVec 256) : Nat := a.toNat/2^242%16384
def rankN (a : BitVec 256) (k : Nat) : Nat := a.toNat/2^(SharedField.rankBit k)%1024
def costN (a : BitVec 256) (k : Nat) : Nat := a.toNat/2^(costBit k)%32

theorem geu_holds (s : MachineState) (e : E) (v bound : Nat) (hv:v < 2^64) (hb:bound < 2^64)
    (he:e.eval s=BitVec.ofNat 64 v) : (Br.mk .geu e (cE bound) (decide (¬v < bound))).holds s := by
  simp only[Br.holds,CmpOp.eval,E.eval,cE,he,BitVec.ult,toNat_ofNat_lt hv,toNat_ofNat_lt hb]
  by_cases h:v < bound <;> simp only[h,not_true_eq_false,not_false_eq_true,decide_true,decide_false,
    Bool.not_true,Bool.not_false]

theorem gate_eval (s : MachineState) (a : BitVec 256) (ha:OutAt s NBUF a) :
    gateE.eval s=BitVec.ofNat 64 (gateN a) := by
  have h3:s.getMem (BitVec.ofNat 64 (NBUF+24))=a.extractLsb' 192 64:=ha 3 (by decide)
  simp only[gateE,ldc,cE,E.eval,h3]
  rw[SearchM.srl_eval _ 50 (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw[SigGolfCandidate.Research.V7Composed198Gate.gate_shift50_toNat,toNat_ofNat_lt (by unfold gateN;omega)]
  rfl

theorem gate_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (base m+15))
    (a : BitVec 256) (ha:OutAt s NBUF a) :
    ∃t,Steps im s 6 6 t ∧ t.pc=(if gateN a < 791 then pcOf (base m+21) else pcOf (next m)) ∧
      (m=true → t.getReg .x17=BitVec.ofNat 64 NBUF) ∧
      RegsExcept s t [.x6,.x7,.x17,.x28] ∧ Frame s t (fun _=>False) := by
  have hbr:∀b∈(expectedGate m (decide (¬gateN a < 791))).brs,b.holds s:=by
    intro b hb
    simp only[expectedGate,pres,pres2,List.mem_singleton]at hb
    subst hb
    exact geu_holds s gateE (gateN a) 791 (by unfold gateN;omega) (by decide) (gate_eval s a ha)
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (gate_run m _) s hpc rfl hbr rfl
  refine ⟨_,hs,?_,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · rw[hp];simp only[expectedGate,pres,pres2,decide_eq_true_eq]
    split_ifs <;> first | rfl | contradiction
  · intro hm;subst m;rw[hr];rfl
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem init_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (base m+21))
    (h17:m=true → s.getReg .x17=BitVec.ofNat 64 NBUF) :
    ∃t,Steps im s (if m then 3 else 5) (if m then 3 else 5) t ∧ t.pc=pcOf (firstField m) ∧
      t.getReg (sumReg m)=0 ∧ t.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m) ∧
      t.getReg .x17=BitVec.ofNat 64 NBUF ∧ RegsExcept s t [.x17,.x20,.x21] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (init_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,?_,?_,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · cases m <;> rw[hr] <;> rfl
  · cases m <;> rw[hr] <;> rfl
  · cases m
    · rw[hr];rfl
    · rw[hr];exact h17 rfl
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem fields_bounded (k : Nat) (hk:k < 9) :
    SharedField.rankBit k < 256 ∧ SharedField.rankBit k%64+10 ≤ 64 ∧ costBit k < 256 ∧ costBit k%64+5 ≤ 64 := by
  have h:∀k,k < 9 → SharedField.rankBit k < 256 ∧ SharedField.rankBit k%64+10 ≤ 64 ∧ costBit k < 256 ∧ costBit k%64+5 ≤ 64:=by decide +kernel
  exact h k hk

theorem field_valid (s : MachineState) (h17:s.getReg .x17=BitVec.ofNat 64 NBUF)
    (bit : Nat) (hb:bit < 256) : (Oblig.valid (fieldAddr bit) 8).holds s := by
  exact valid_ofNat h17 (by unfold NBUF;omega) (by unfold NBUF MEMORY_BYTES;omega)

theorem rank_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (field m k)) (a : BitVec 256) (ha:OutAt s NBUF a)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) :
    ∃t,Steps im s 5 5 t ∧ t.pc=(if rankN a k < 563 then pcOf (field m k+5) else pcOf (next m)) ∧
      t.getReg (rankReg m)=BitVec.ofNat 64 (rankN a k) ∧ RegsExcept s t [.x6,.x24,.x25] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hb,hfit,-,-⟩:=fields_bounded k hk
  have he:(rankE k).eval s=BitVec.ofNat 64 (rankN a k):=field_eval s a ha h17 hb (by decide) hfit
  have hbr:∀b∈(expectedRank m k (decide (¬rankN a k < 563))).brs,b.holds s:=by
    intro b hb
    simp only[expectedRank,pres,pres2,List.mem_singleton]at hb
    subst hb
    exact geu_holds s (rankE k) (rankN a k) 563 (by unfold rankN;omega) (by decide) he
  obtain ⟨hst,-⟩:=run_pres hl (rank_run m k hk _) s hpc (by
    intro ob ho
    simp only[expectedRank,pres,pres2,List.mem_singleton]at ho
    subst ho
    exact field_valid s h17 _ hb) hbr
  refine ⟨_,hst,?_,?_,?_,fun A _ _=>rfl⟩
  · change pcOf (if decide (¬rankN a k < 563) then next m else field m k+5)=_
    simp only[decide_eq_true_eq]
    split_ifs <;> first | rfl | contradiction
  · cases m <;> rw[pres_getReg] <;> exact he
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem cap_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (cap m))
    (total : Nat) (ht:total < 2^64) (hs:s.getReg (sumReg m)=BitVec.ofNat 64 total) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if total ≤ 777 then pcOf (accepted m) else pcOf (next m)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hbr:∀b∈(expectedCap m (decide (¬total < 778))).brs,b.holds s:=by
    intro b hb
    simp only[expectedCap,pres,pres2,List.mem_singleton]at hb
    subst hb
    exact geu_holds s (.reg (sumReg m)) total 778 ht (by decide) hs
  obtain ⟨st,hp,-,hr,hm⟩:=SearchM.piece hl (cap_run m _) s hpc rfl hbr rfl
  refine ⟨_,st,?_,(pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg]),fun A _ _=>by rw[hm];rfl⟩
  rw[hp];simp only[expectedCap,pres,pres2,decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
/-- C1 (stage 1): `2 - skips′` per class `p mod 32`, the same table for A and for B/C. -/
def correctionA : List Nat := [2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 2]
def correctionB : List Nat := [2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 2]
def rankByte (f : Nat) : Nat := WCT9.routineCosts.getD f 0
 def correctionByte (k j : Nat) : Nat := (if SharedLeaf.first k then correctionA else correctionB).getD j 0
 structure TablesAt (m : Bool) (s : MachineState) : Prop where
   ranks : ∀f,f < 563 → s.getByte (BitVec.ofNat 64 (tableBase m+f))=BitVec.ofNat 8 (rankByte f)
   corrections : ∀k,k < 9 → ∀j,j < 32 →
     s.getByte (BitVec.ofNat 64 (tableBase m+correctionOffset m k+j))=BitVec.ofNat 8 (correctionByte k j)
 theorem rankByte_lt (f : Nat) (hf:f < 563) : rankByte f < 256 := by
   unfold rankByte
   have hfl:f < WCT9.routineCosts.length:=by rw[WCT9.routineCosts_length];exact hf
   rw[List.getD_eq_getElem _ _ hfl]
   have h:=(WCT9.routineCosts_bounds _ (List.getElem_mem hfl)).2
   omega
 theorem correctionByte_lt (k j : Nat) (hk:k < 9) (hj:j < 32) : correctionByte k j < 256 := by
   have h:∀k,k < 9 → ∀j,j < 32 → correctionByte k j < 256:=by decide +kernel
   exact h k hk j hj
 def writes (A : Nat) : Prop := A=DIG+16 ∨ A=DIG+24 ∨ (NBUF ≤ A ∧ A < NBUF+32)
 def regs : List Reg := [.x6,.x7,.x10,.x11,.x12,.x17,.x19,.x20,.x21,.x24,.x25,.x28]
 theorem TablesAt.frame {m : Bool} {s t : MachineState} (hs:TablesAt m s) (hf:Frame s t writes) : TablesAt m t := by
   constructor
   · intro f hff
     rw[hf.getByte (by cases m <;> unfold tableBase <;> simp <;> omega) (by cases m <;> simp[tableBase,writes,DIG,NBUF] <;> omega)]
     exact hs.ranks f hff
   · intro k hk j hj
     have ho:correctionOffset m k ≤ 1568:=by unfold correctionOffset;split <;> split <;> omega
     rw[hf.getByte (by cases m <;> unfold tableBase <;> simp <;> omega) (by cases m <;> simp only[tableBase,writes,DIG,NBUF,Bool.false_eq_true,if_false,if_true] <;> omega)]
     exact hs.corrections k hk j hj
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

theorem rankAddr_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (field m k+5)) (r : Nat)
    (ht:s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m)) (hr:s.getReg (rankReg m)=BitVec.ofNat 64 r) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf (rankLoad m k) ∧
      t.getReg (addrReg m)=BitVec.ofNat 64 (tableBase m+r) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hreg,hm⟩:=SearchM.piece hl (rankAddr_run m k hk) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · cases m <;> rw[hreg] <;> change s.getReg _+s.getReg _=_ <;> rw[ht,hr,ofNat_add_ofNat]
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem corrPrep_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (rankLoad m k+1)) (a : BitVec 256) (ha:OutAt s NBUF a)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) (ht:s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m))
    (sum value : Nat) (hsum:s.getReg (sumReg m)=BitVec.ofNat 64 sum) (h6:s.getReg .x6=BitVec.ofNat 64 value) :
    ∃t,Steps im s (if m then 7 else 5) (if m then 7 else 5) t ∧ t.pc=pcOf (corrLoad m k) ∧
      t.getReg (sumReg m)=BitVec.ofNat 64 (sum+value) ∧
      t.getReg (addrReg m)=BitVec.ofNat 64 (tableBase m+costN a k+(if m then correctionOffset m k else 0)) ∧
      RegsExcept s t [sumReg m,.x6,.x24,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨-, -, hb,hfit⟩:=fields_bounded k hk
  have he:(costE k).eval s=BitVec.ofNat 64 (costN a k):=field_eval s a ha h17 hb (by decide) hfit
  obtain ⟨st,-⟩:=run_pres hl (corrPrep_run m k hk) s hpc (by
    intro ob ho
    simp only[expectedCorrPrep,pres,pres2,List.mem_singleton]at ho
    subst ho
    exact field_valid s h17 _ hb) (no_br s)
  refine ⟨_,st,rfl,?_,?_,?_,fun A _ _=>rfl⟩
  · cases m <;> rw[pres_getReg] <;> change s.getReg _+s.getReg .x6=_ <;> rw[hsum,h6,ofNat_add_ofNat]
  · cases m
    · rw[pres_getReg]
      change s.getReg (tableReg false)+(costE k).eval s=_
      rw[ht,he,ofNat_add_ofNat]
      rfl
    · rw[pres_getReg]
      change (costE k).eval s+BitVec.ofNat 64 (tableBase true+correctionOffset true k)=_
      rw[he,ofNat_add_ofNat]
      congr 1
      simp only[if_true]
      omega
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem sum_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (corrLoad m k+1)) (total value : Nat)
    (hs:s.getReg (sumReg m)=BitVec.ofNat 64 total) (hv:s.getReg .x6=BitVec.ofNat 64 value) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf (field m (k+1)) ∧ t.getReg (sumReg m)=BitVec.ofNat 64 (total+value) ∧
      RegsExcept s t [sumReg m] ∧ Frame s t (fun _=>False) := by
  obtain ⟨st,hp,-,hr,hm⟩:=SearchM.piece hl (sum_run m k hk) s hpc rfl (no_br s) rfl
  refine ⟨_,st,hp,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · cases m <;> rw[hr] <;> change s.getReg _+s.getReg .x6=_ <;> rw[hs,hv,ofNat_add_ofNat]
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

theorem out_frame {s t : MachineState} {a : BitVec 256} (h:OutAt s NBUF a) (hf:Frame s t (fun _=>False)) :
    OutAt t NBUF a := fun j hj=>by rw[hf.get (by unfold NBUF;omega) (fun h=>h)];exact h j hj
theorem TablesAt.frameEmpty {m : Bool} {s t : MachineState} (h:TablesAt m s) (hf:Frame s t (fun _=>False)) :
    TablesAt m t := h.frame (hf.mono (fun _ _ h=>h.elim))

theorem cost_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (field m k+5)) (a : BitVec 256) (ha:OutAt s NBUF a) (hc:TablesAt m s)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) (ht:s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m))
    (hr:s.getReg (rankReg m)=BitVec.ofNat 64 (rankN a k)) (hf:rankN a k < 563)
    (total : Nat) (hs:s.getReg (sumReg m)=BitVec.ofNat 64 total) :
    ∃t n,Steps im s n n t ∧ n ≤ 11 ∧ t.pc=pcOf (field m (k+1)) ∧
      t.getReg (sumReg m)=BitVec.ofNat 64 (total+rankByte (rankN a k)+correctionByte k (costN a k)) ∧
      RegsExcept s t [sumReg m,.x6,.x24,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t1,st1,p1,addr1,r1,f1⟩:=rankAddr_spec m k hk hl s hpc _ ht hr
  have c1:=hc.frameEmpty f1
  obtain ⟨t2,st2,p2,v2,r2,f2⟩:=lbu_spec t1 (addrReg m) 0 (tableBase m+rankN a k) (rankByte (rankN a k))
    (rank_lbu m k hk hl t1 p1) (by rw[addr1];simp [signExtend12])
    (by cases m <;> simp [tableBase,MEMORY_BYTES] <;> omega) (c1.ranks _ hf) (rankByte_lt _ hf)
  have p2':t2.pc=pcOf (rankLoad m k+1):=by rw[p2,p1];exact SigGolfCandidate.T3M.pcOf_add4 _
  have c2:=c1.frameEmpty f2
  have r12:=r1.trans r2
  obtain ⟨t3,st3,p3,sum3,addr3,r3,f3⟩:=corrPrep_spec m k hk hl t2 p2' a (out_frame (out_frame ha f1) f2)
    (by rw[r12.get (by simp)];exact h17)
    (by rw[r12.get (by cases m <;> simp [tableReg])];exact ht)
    total (rankByte (rankN a k)) (by rw[r12.get (by cases m <;> simp [sumReg])];exact hs) v2
  have c3:=c2.frameEmpty f3
  have hlo:costN a k < 32:=Nat.mod_lt _ (by decide)
  have hoff:signExtend12 (BitVec.ofNat 12 (if m then 0 else correctionOffset m k))=
      BitVec.ofNat 64 (if m then 0 else correctionOffset m k) := by
    cases m <;> simp only[correctionOffset,Bool.false_eq_true,if_false,if_true]
    · split <;> decide +kernel
    · decide +kernel
  have ho:correctionOffset m k ≤ 1568:=by unfold correctionOffset;split <;> split <;> omega
  obtain ⟨t4,st4,p4,v4,r4,f4⟩:=lbu_spec t3 (addrReg m)
    (BitVec.ofNat 12 (if m then 0 else correctionOffset m k))
    (tableBase m+correctionOffset m k+costN a k) (correctionByte k (costN a k))
    (corr_lbu m k hk hl t3 p3) (by rw[addr3,hoff,ofNat_add_ofNat];congr 1;cases m <;> simp <;> omega)
    (by cases m <;> simp [tableBase,MEMORY_BYTES] <;> omega)
    (c3.corrections k hk _ hlo) (correctionByte_lt k _ hk hlo)
  have p4':t4.pc=pcOf (corrLoad m k+1):=by rw[p4,p3];exact SigGolfCandidate.T3M.pcOf_add4 _
  obtain ⟨t5,st5,p5,sum5,r5,f5⟩:=sum_spec m k hk hl t4 p4' (total+rankByte (rankN a k)) _
    (by rw[r4.get (by cases m <;> simp[sumReg])];exact sum3) v4
  refine ⟨t5,1+1+(if m then 7 else 5)+1+1,(((st1.trans st2).trans st3).trans st4).trans st5,?_,p5,sum5,?_,?_⟩
  · cases m <;> decide
  · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by simp)
  · exact ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun A _ h=>by simpa using h)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}
attribute [local instance] Classical.propDecidable

def psum (a : BitVec 256) (n : Nat) : Nat :=
  ((List.range n).map (fun k=>rankByte (rankN a k)+correctionByte k (costN a k))).sum
theorem psum_succ (a : BitVec 256) (k : Nat) :
    psum a (k+1)=psum a k+rankByte (rankN a k)+correctionByte k (costN a k) := by
  simp [psum,List.range_succ,List.map_append,List.sum_append,Nat.add_assoc]
theorem rankByte_lt_all (f : Nat) : rankByte f < 256 := by
  by_cases hf:f < 563
  · exact rankByte_lt f hf
  · unfold rankByte
    rw[List.getD_eq_default _ _ (by rw[WCT9.routineCosts_length];omega)]
    decide
theorem psum_le (a : BitVec 256) (n : Nat) (hn:n ≤ 9) : psum a n ≤ 512*n := by
  induction n with
  | zero=>simp [psum]
  | succ n ih=>
    rw[psum_succ]
    have h1:=rankByte_lt_all (rankN a n)
    have h2:=correctionByte_lt n (costN a n) (by omega) (Nat.mod_lt _ (by decide))
    have h3:=ih (by omega)
    omega

theorem fields_from (m : Bool) (hl:LookOK im (look m)) (a : BitVec 256) :
    ∀ n k,k+n=9 → ∀s : MachineState,s.pc=pcOf (field m k) → OutAt s NBUF a → TablesAt m s →
      s.getReg .x17=BitVec.ofNat 64 NBUF → s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m) →
      s.getReg (sumReg m)=BitVec.ofNat 64 (psum a k) →
      ∃t c,Steps im s c c t ∧ c ≤ 16*n ∧ RegsExcept s t [sumReg m,.x6,.x24,.x25,.x28] ∧
        Frame s t (fun _=>False) ∧
        (if ∀k',k' < 9 → k ≤ k' → rankN a k' < 563 then
          t.pc=pcOf (cap m) ∧ t.getReg (sumReg m)=BitVec.ofNat 64 (psum a 9) else t.pc=pcOf (next m)) := by
  intro n
  induction n with
  | zero=>
    intro k hk s hpc _ _ _ _ hs
    have h:k=9:=by omega
    subst k
    refine ⟨s,0,Steps.refl _,by omega,RegsExcept.refl _ _,Frame.refl _ _,?_⟩
    rw[if_pos (by intro k' hk' hle;omega)]
    exact ⟨hpc,hs⟩
  | succ n ih=>
    intro k hk s hpc ha hc h17 ht hs
    have hk9:k < 9:=by omega
    obtain ⟨t1,s1,p1,v1,r1,f1⟩:=rank_spec m k hk9 hl s hpc a ha h17
    by_cases hrank:rankN a k < 563
    · rw[if_pos hrank]at p1
      obtain ⟨t2,c2,s2,hc2,p2,v2,r2,f2⟩:=cost_spec m k hk9 hl t1 p1 a (out_frame ha f1)
        (hc.frameEmpty f1) (by rw[r1.get (by simp)];exact h17)
        (by rw[r1.get (by cases m <;> simp[tableReg])];exact ht) v1 hrank (psum a k)
        (by rw[r1.get (by cases m <;> simp[sumReg])];exact hs)
      have r12:=r1.trans r2
      obtain ⟨t3,c3,s3,hc3,r3,f3,p3⟩:=ih (k+1) (by omega) t2 p2 (out_frame (out_frame ha f1) f2)
        ((hc.frameEmpty f1).frameEmpty f2) (by rw[r12.get (by cases m <;> simp[sumReg])];exact h17)
        (by rw[r12.get (by cases m <;> simp[tableReg,sumReg])];exact ht) (by rw[v2,psum_succ])
      refine ⟨t3,5+c2+c3,(s1.trans s2).trans s3,by omega,(r12.trans r3).mono (by simp),
        ((f1.trans f2).trans f3).mono (fun A _ h=>by simpa using h),?_⟩
      have hiff:(∀j,j < 9 → k ≤ j → rankN a j < 563) ↔ (∀j,j < 9 → k+1 ≤ j → rankN a j < 563) := by
        constructor
        · intro h j hj hle;exact h j hj (by omega)
        · intro h j hj hle
          by_cases he:j=k
          · subst j;exact hrank
          · exact h j hj (by omega)
      by_cases hall:∀j,j < 9 → k+1 ≤ j → rankN a j < 563
      · rw[if_pos hall]at p3
        rw[if_pos (hiff.mpr hall)]
        exact p3
      · rw[if_neg hall]at p3
        rw[if_neg (fun h=>hall (hiff.mp h))]
        exact p3
    · rw[if_neg hrank]at p1
      refine ⟨t1,5,s1,by omega,r1.mono (by simp),f1,?_⟩
      rw[if_neg (fun h=>hrank (h k hk9 le_rfl))]
      exact p1

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
variable {im : Image}

def acceptedTest (a : BitVec 256) : Bool := decide (gateN a < 791) &&
  (List.range 9).all (fun k=>decide (rankN a k < 563)) && decide (psum a 9 ≤ 777)
theorem acceptedTest_iff (a : BitVec 256) : acceptedTest a=true ↔
    gateN a < 791 ∧ (∀k,k < 9 → rankN a k < 563) ∧ psum a 9 ≤ 777 := by
  simp only[acceptedTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,and_assoc]

theorem checks_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (base m+15)) (a : BitVec 256) (ha:OutAt s NBUF a) (hc:TablesAt m s) :
    ∃t c,Steps im s c c t ∧ c ≤ 157 ∧ RegsExcept s t [.x6,.x7,.x17,.x20,.x21,.x24,.x25,.x28] ∧
      Frame s t (fun _=>False) ∧ t.pc=(if acceptedTest a then pcOf (accepted m) else pcOf (next m)) ∧
      (acceptedTest a=true → t.getReg .x17=BitVec.ofNat 64 NBUF) := by
  obtain ⟨t1,s1,p1,r17,r1,f1⟩:=gate_spec m hl s hpc a ha
  by_cases hg:gateN a < 791
  · rw[if_pos hg]at p1
    obtain ⟨t2,s2,p2,sm2,tb2,r172,r2,f2⟩:=init_spec m hl t1 p1 r17
    obtain ⟨t3,c3,s3,b3,r3,f3,p3⟩:=fields_from m hl a 9 0 rfl t2 p2
      (out_frame (out_frame ha f1) f2) ((hc.frameEmpty f1).frameEmpty f2) r172 tb2 sm2
    have hall:(∀k,k < 9 → 0 ≤ k → rankN a k < 563) ↔ (∀k,k < 9 → rankN a k < 563) := by simp
    by_cases hf:∀k,k < 9 → rankN a k < 563
    · rw[if_pos (hall.mpr hf)]at p3
      obtain ⟨t4,s4,p4,r4,f4⟩:=cap_spec m hl t3 p3.1 (psum a 9) (by have:=psum_le a 9 (by omega);omega) p3.2
      refine ⟨t4,6+(if m then 3 else 5)+c3+2,((s1.trans s2).trans s3).trans s4,?_,?_,?_,?_,?_⟩
      · cases m <;> simp at * <;> omega
      · exact (((r1.trans r2).trans r3).trans r4).mono (by cases m <;> simp [sumReg])
      · exact (((f1.trans f2).trans f3).trans f4).mono (fun A _ h=>by simpa using h)
      · rw[p4]
        have he:(acceptedTest a=true) ↔ psum a 9 ≤ 777:=by
          constructor
          · intro h;exact ((acceptedTest_iff a).mp h).2.2
          · intro h;exact (acceptedTest_iff a).mpr ⟨hg,hf,h⟩
        simp only[he]
      · intro _
        rw [r4.get (by cases m <;> simp [sumReg]),r3.get (by cases m <;> simp [sumReg])]
        exact r172
    · rw[if_neg (fun h=>hf (hall.mp h))]at p3
      refine ⟨t3,6+(if m then 3 else 5)+c3,(s1.trans s2).trans s3,?_,?_,?_,?_,?_⟩
      · cases m <;> simp at * <;> omega
      · exact ((r1.trans r2).trans r3).mono (by cases m <;> simp [sumReg])
      · exact ((f1.trans f2).trans f3).mono (fun A _ h=>by simpa using h)
      · rw[if_neg (fun h=>hf ((acceptedTest_iff a).mp h).2.1)]
        exact p3
      · intro ha
        exact False.elim (hf ((acceptedTest_iff a).mp ha).2.1)
  · rw[if_neg hg]at p1
    refine ⟨t1,6,s1,by omega,r1.mono (by simp),f1,?_,?_⟩
    · rw[if_neg (fun h=>hg ((acceptedTest_iff a).mp h).1)]
      exact p1
    · intro ha
      exact False.elim (hg ((acceptedTest_iff a).mp ha).1)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem correctionByte_canonical (k : Fin 9) (j : Fin 32) :
    correctionByte k.val j.val=(if SharedForest.firstCoord k.val then SharedForest.aCorrection j.val
      else SharedForest.bCorrection j.val) := by
  have h:∀k : Fin 9,∀j : Fin 32,correctionByte k.val j.val=(if SharedForest.firstCoord k.val then
    SharedForest.aCorrection j.val else SharedForest.bCorrection j.val):=by decide +kernel
  exact h k j
theorem correctionByte_field (a : BitVec 256) (k : Fin 9) :
    correctionByte k.val (costN a k.val)=SharedForest.accountingCorrection k.val (SharedForest.rawChildFromOutput a k) := by
  rw[SharedForest.accountingCorrection_field]
  exact correctionByte_canonical k (SharedForest.costField a k)
theorem rankByte_source (a : BitVec 256) (k : Fin 9) (hk:rankN a k.val < 563) :
    rankByte (rankN a k.val)=WCT9.routineCost (SharedForest.forestRank a k.val) := by
  have hr:(SharedForest.forestRank a k.val).val=rankN a k.val := by
    change rankN a k.val % 563=rankN a k.val
    exact Nat.mod_eq_of_lt hk
  unfold rankByte WCT9.routineCost
  simp only [hr]
  rw[List.getD_eq_getElem _ _ (by rw[WCT9.routineCosts_length];exact hk)]

theorem psum_source (a : BitVec 256) (h:∀k,k < 9 → rankN a k < 563) :
    psum a 9=SharedForest.jointAccountingCost a := by
  unfold psum SharedForest.jointAccountingCost SharedForest.coordinateAccountingCost
  have hr:List.range 9=(List.finRange 9).map Fin.val:=by decide
  rw[hr,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  simp only[Function.comp_def,rankByte_source a k (h k.val k.isLt),correctionByte_field]

theorem acceptedTest_source (a : BitVec 256) : acceptedTest a=SharedForest.digestAccepted a := by
  apply Bool.eq_iff_iff.mpr
  rw[acceptedTest_iff]
  have hr:SharedForest.ranksAccepted a=true ↔ (∀k,k < 9 → rankN a k < 563) := by
    simp only[SharedForest.ranksAccepted,List.all_eq_true,decide_eq_true_eq,List.mem_finRange,forall_const]
    constructor
    · intro h k hk;exact h ⟨k,hk⟩
    · intro h k;exact h k.val k.isLt
  simp only[SharedForest.digestAccepted,Bool.and_eq_true,decide_eq_true_eq,hr,and_assoc]
  constructor
  · rintro ⟨hg,hf,hc⟩
    exact ⟨hg,hf,by rwa[←psum_source a hf]⟩
  · rintro ⟨hg,hf,hc⟩
    exact ⟨hg,hf,by rwa[psum_source a hf]⟩

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Pre (m : Bool) (rho : BitVec 128) (msg : SigGolfCandidate.T3.Message) (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  rho : DigAt s DIG rho
  msg : ∀k,k < 4 → s.getMem (BitVec.ofNat 64 (DIG+32+8*k))=msg.extractLsb' (64*k) 64
  tables : TablesAt m s
structure LoopInv (m : Bool) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (trial m)
  hi : i ≤ 2^21
  x19 : t.getReg .x19=BitVec.ofNat 64 i
  regs : RegsExcept s0 t regs
  frame : Frame s0 t writes
structure Post (m : Bool) (s0 : MachineState) (r : Option (BitVec 32 × BitVec 256)) (t : MachineState) : Prop where
  x5 : t.getReg .x5=0
  regs : RegsExcept s0 t regs
  frame : Frame s0 t writes
  result : match r with
    | none => t.pc=pcOf (fail m) ∧ t.getReg .x19=BitVec.ofNat 64 (2^21)
    | some (c,a) => t.pc=pcOf (accepted m) ∧ t.getReg .x19=BitVec.ofNat 64 c.toNat ∧
      c.toNat < 2^21 ∧ SharedForest.digestAccepted a=true ∧ OutAt t NBUF a

  resultR17 : match r with
    | none => True
    | some _ => t.getReg .x17=BitVec.ofNat 64 NBUF

variable {im : Image} {sk : BitVec 256}
theorem loop (m : Bool) (hl : LookOK im (look m)) {s0 : MachineState} {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message}
    (hpre : Pre m rho msg s0) :
    ∀F i t,i+F=2^21 → LoopInv m s0 i t →
      TBSim im sk t (F*200+10) (SharedForest.sharedDigestSearch rho msg i F) (Post m s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1,s1,p1,r1,f1⟩:=head_spec m hl t hI.pc i hI.hi hI.x19
    rw[if_neg (by omega)] at p1
    have rr : RegsExcept s0 t1 regs := (hI.regs.trans r1).mono (by simp[regs])
    have ff : Frame s0 t1 writes := (hI.frame.trans f1).mono (fun A _ hh=>hh.elim id False.elim)
    have hp : Post m s0 none t1 := ⟨by rw[rr.get (by decide),hpre.x5],rr,ff,⟨p1,by
      have hiEq:i=2^21:=by omega
      rw[r1.get (by decide),hI.x19,hiEq]⟩,trivial⟩
    exact (TBSim.pure_steps' (sk:=sk) s1 hp).mono (by omega) (fun _ _ hh=>hh)
  | succ F ih =>
    intro i t h hI
    have hi:i < 2^21:=by omega
    have hc:(BitVec.ofNat 32 i).toNat=i:=by rw[BitVec.toNat_ofNat];omega
    obtain ⟨t1,s1,p1,r1,f1⟩:=head_spec m hl t hI.pc i hI.hi hI.x19
    rw[if_pos hi]at p1
    obtain ⟨u,s2,hfu,p2,h10,h11,h12,h16,h24,r2,f2⟩:=trial_spec m hl t1 p1 i
      (by rw[r1.get (by decide),hI.x19])
    have ru : RegsExcept s0 u regs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have fu : Frame s0 u writes := ((hI.frame.trans f1).trans f2).mono (fun A _ hA=>by
      rcases hA with (hA|hA)|hA
      · exact hA
      · exact hA.elim
      · unfold writes;rcases hA with hA|hA <;> simp[hA])
    have mem : ∀A,A < 2^64 → ¬writes A → u.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A):=
      fun A hA hn=>fu.get hA hn
    have nw:∀A,A=DIG ∨ A=DIG+8 ∨ A=DIG+32 ∨ A=DIG+40 ∨ A=DIG+48 ∨ A=DIG+56 → ¬writes A:=by
      intro A hA;simp only[writes,DIG,NBUF]at hA ⊢;omega
    have hm0:s0.getMem (BitVec.ofNat 64 (DIG+32))=msg.extractLsb' 0 64:=hpre.msg 0 (by decide)
    have hm1:s0.getMem (BitVec.ofNat 64 (DIG+40))=msg.extractLsb' 64 64:=hpre.msg 1 (by decide)
    have hm2:s0.getMem (BitVec.ofNat 64 (DIG+48))=msg.extractLsb' 128 64:=hpre.msg 2 (by decide)
    have hm3:s0.getMem (BitVec.ofNat 64 (DIG+56))=msg.extractLsb' 192 64:=hpre.msg 3 (by decide)
    have hq:hashInput u=toQ (SigGolfCandidate.T3.pad64
        (SigGolfCandidate.T3.digestInput rho msg (BitVec.ofNat 32 i))):=by
      refine hashInput_toQ u _ 0 DIG (by rw[SearchM.pad64_digestInput',SearchM.digestInput_length']) h10
        (by decide) (by decide) h11 (by decide) ?_
      rw[SigGolfCandidate.T3M.readWords_eight,SearchM.wordsOf_digestInput',hc,h16,h24,
        mem DIG (by decide) (nw _ (by omega)),mem (DIG+8) (by decide) (nw _ (by omega)),
        mem (DIG+32) (by decide) (nw _ (by omega)),mem (DIG+40) (by decide) (nw _ (by omega)),
        mem (DIG+48) (by decide) (nw _ (by omega)),mem (DIG+56) (by decide) (nw _ (by omega)),
        hpre.rho.1,hpre.rho.2,hm0,hm1,hm2,hm3]
      rfl
    have hv:hashArgumentsValid u=true:=hashArgs_const u DIG 64 NBUF h10 h11 h12
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5:u.getReg .x5=0:=by rw[ru.get (by decide),hpre.x5]
    have prog:SharedForest.sharedDigestSearch rho msg i (F+1)=
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho msg (BitVec.ofNat 32 i)) >>= fun output=>
          if SharedForest.digestAccepted output=true then pure (some (BitVec.ofNat 32 i,output))
          else SharedForest.sharedDigestSearch rho msg (i+1) F):=rfl
    rw[prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind' hfu h5 hv hq
      (W:=159+(F*200+10)) (fun a=>?_))).mono ?_ (fun _ _ hh=>hh)
    swap
    · rw[SearchM.blocks_digestInput'];omega
    have pw:(writeHash u a).pc=pcOf (base m+15):=by rw[pc_writeHash,p2,SigGolfCandidate.T3M.pcOf_add4]
    have hN:OutAt (writeHash u a) NBUF a:=SearchM.outAt_writeHash u a h12
    have fw:=Frame.writeHash u a NBUF h12 (by decide)
    have fuw:Frame s0 (writeHash u a) writes:=(fu.trans fw).mono (fun A _ hA=>by
      rcases hA with hA|hA
      · exact hA
      · exact Or.inr (Or.inr hA))
    obtain ⟨v,c,sv,hcv,rv,fv,pv,vr17⟩:=checks_spec m hl (writeHash u a) pw a hN (hpre.tables.frame fuw)
    rw[acceptedTest_source]at pv vr17
    have rv':RegsExcept s0 v regs:=
      ((ru.trans (fun r _=>getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans rv).mono (by decide)
    have fv':Frame s0 v writes:=(fuw.trans fv).mono (fun A _ hA=>hA.elim id False.elim)
    have hNv:OutAt v NBUF a:=out_frame hN fv
    have x19v:v.getReg .x19=BitVec.ofNat 64 i:=by
      rw[rv.get (by decide),getReg_writeHash,r2.get (by decide),r1.get (by decide),hI.x19]
    by_cases hadm:SharedForest.digestAccepted a=true
    · rw[if_pos hadm]at pv
      simp only[hadm,↓reduceIte]
      have hp:Post m s0 (some (BitVec.ofNat 32 i,a)) v:=⟨by rw[rv'.get (by decide),hpre.x5],rv',fv',
        ⟨pv,by rw[hc];exact x19v,by rw[hc];exact hi,hadm,hNv⟩,vr17 hadm⟩
      exact (TBSim.pure_steps' sv hp).mono (by omega) (fun _ _ hh=>hh)
    · rw[if_neg hadm]at pv
      simp only[hadm,↓reduceIte]
      obtain ⟨w,sw,pw',x19w,rw',fw'⟩:=next_spec m hl v pv i x19v
      have hI':LoopInv m s0 (i+1) w:=⟨pw',by omega,x19w,(rv'.trans rw').mono (by decide),
        (fv'.trans fw').mono (fun A _ hA=>hA.elim id False.elim)⟩
      exact (TBSim.steps (sv.trans sw) (ih (i+1) w (by omega) hI')).mono (by omega) (fun _ _ hh=>hh)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {im : Image} {sk : BitVec 256}
def expectedEntry (m : Bool) : PRes := pres [(.x5,cE 0),(.x19,cE 0)] [] [] (trial m) false 2 []
theorem entry_run (m : Bool) : run (look m) [trial m] (base m) []=some (expectedEntry m) := by
  cases m <;> apply optBeq_eq <;> decide +kernel

theorem entry_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (base m)) (h5:s.getReg .x5=0) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf (trial m) ∧ t.getReg .x19=0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (entry_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,by rw[hr];rfl,?_,fun A _ _=>by rw[hm];rfl⟩
  intro r hx
  have rr:=pres_regsExcept [(.x5,cE 0),(.x19,cE 0)] [] [] (trial m) false 2 [] s
  by_cases h:r=.x5
  · subst r
    rw[hr,h5]
    rfl
  · exact rr r (by simpa[h]using hx)

theorem search_good (m : Bool) (hl:LookOK im (look m)) {s0 : MachineState}
    {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message} (hpre:Pre m rho msg s0)
    (hpc:s0.pc=pcOf (base m)) :
    TBSim im sk s0 (2^21*200+12) (SharedForest.sharedDigestSearch rho msg 0 (2^21)) (Post m s0) := by
  obtain ⟨t,ss,hp,h19,rr,ff⟩:=entry_spec m hl s0 hpc hpre.x5
  have hi:LoopInv m s0 0 t:=⟨hp,by decide,h19,rr.mono (by simp[regs]),ff.mono (fun _ _ h=>h.elim)⟩
  exact (TBSim.steps ss (loop m hl hpre (2^21) 0 t (by omega) hi)).mono (by omega) (fun _ _ h=>h)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def signCode : List (BitVec 32) := [0x20e37,0x160e0e13,0xe3b03,0x21b5b13,0x20e37,0x550e0e13,0x16e3023,0xaf9f406f]
sym_block signRun := symRun {noAlias:=true} signCode (pcOf 22754) 30
def expandCode : List (BitVec 32) := [0x180006f]
def failureCode : List (BitVec 32) := [0x100293,0x100513]
sym_block failRun := symRun {noAlias:=true} failureCode (pcOf 543) 10
sym_block failExpandRun := symRun {noAlias:=true} failureCode (pcOf 45229) 10
def failPC (m : Bool) : Word := pcOf (if m then 45229 else 543)
def failResult (m : Bool) : Result := if m then failExpandRun.res else failRun.res
theorem failure_run (m : Bool) : symRun {noAlias:=true} failureCode (failPC m) 10=some (failResult m) := by
  cases m
  · exact failRun
  · exact failExpandRun

theorem sign_steps {im : Image} (hc : CodeAt im (pcOf 22754) signCode)
    (s : MachineState) (hp : s.pc=pcOf 22754) (h17 : s.getReg .x17=0x20160) :
    ∃t,Steps im s 8 8 t ∧ t.pc=pcOf 11175 ∧
      t.getReg .x22=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      RegsExcept s t [.x22,.x28] ∧ Frame s t (fun A=>A=0x20550) := by
  refine ⟨_,symRun_sound signRun hc s hp ?_,?_,?_,?_,?_,?_⟩
  · simp [signRun.res,rv_simp,h17,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [signRun.res,rv_simp,h17]
  · simp [signRun.res,rv_simp,h17]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,signRun.res]
    t3n [h17]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA),if_neg hn]


theorem failure_steps {im : Image} (m : Bool) (hc : CodeAt im (failPC m) failureCode)
    (s : MachineState) (hp : s.pc=failPC m) :
    ∃t,Steps im s 2 2 t ∧ t.pc=failPC m+8 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      RegsExcept s t [.x5,.x10] ∧ Frame s t (fun _=>False) := by
  cases m <;>
    refine ⟨_,symRun_sound (failure_run _) hc s hp ?_,?_,rfl,rfl,?_,?_⟩
  all_goals first
    | solve | simp [failResult,failRun.res,failExpandRun.res,failPC,rv_simp]
    | rfl
    | (intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl)
    | (intro A hA hn;rfl)
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem correction_cost (k j : Nat) (hk:k<9) (hj:j<32) :
    SearchM.costByte (correctionOffset false k+j)=correctionByte k j := by
  have h:∀k,k<9 → ∀j,j<32 → SearchM.costByte (correctionOffset false k+j)=correctionByte k j := by decide +kernel
  exact h k hk j hj

theorem tables_of_costAt {s : MachineState} (hc : CostAt s) : TablesAt false s := by
  constructor
  · intro f hf
    rw [show tableBase false=COST by rfl,SearchM.cost_byte hc (by omega)]
    simp only [SearchM.costByte,if_pos hf,rankByte]
  · intro k hk j hj
    have ho:correctionOffset false k≤1056:=by simp only [correctionOffset,Bool.false_eq_true,if_false];split <;> omega
    rw [show tableBase false=COST by rfl,Nat.add_assoc,SearchM.cost_byte hc (by omega),correction_cost k j hk hj]
end ClaudeWCT.W9.Machine.Sign.SharedDigest
end
-- ==== merged from T3M_Sign_TopBlocks ====
section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
theorem ofNat_and_mask (x k : Nat) (hk : k ≤ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (x % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk; omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk), Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) this)]
theorem ofNat_xor (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]
theorem ofNat_sub_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt hb ha), Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le a b) ha)]
  omega
theorem blk427_spec (s : MachineState) (hpc : s.pc = pcOf 427) (index : Nat) (hidx : index < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 441 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x9 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 54 ∧ t.getReg .x27 = BitVec.ofNat 64 51 ∧
      t.getReg .x17 = BitVec.ofNat 64 145 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 19 % 4096) ∧
      t.getReg .x14 = BitVec.ofNat 64 (index / 2 ^ 19 % 4096) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 19 &&& 4095#64) = BitVec.ofNat 64 (x / 2 ^ 19 % 4096) := by
    intro x hx
    rw [ofNat_shr x 19 hx]
    exact ofNat_and_mask (x / 2 ^ 19) 12 (by norm_num)
  refine ⟨_, symRun_sound blk_427 codeAt_427 s hpc (by simp [blk_427.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_427.res, E.eval]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp [blk_427.res, rv_simp]
  · simp only [Result.toState_getReg, blk_427.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand index (by omega)]
    rfl
  · simp only [Result.toState_getReg, blk_427.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand index (by omega)]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_427.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_427.res, rv_simp]
theorem blk441_spec (s : MachineState) (hpc : s.pc = pcOf 441) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 447 ∧
      t.getReg .x31 = BitVec.ofNat 64 1 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = BitVec.ofNat 64 (SIG + 2192) ∧
      RegsExcept s t [.x1, .x22, .x23, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_441 codeAt_441 s hpc (by simp [blk_441.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_441.res, E.eval]
  · simp [blk_441.res, rv_simp]
  · simp [blk_441.res, rv_simp]
  · simp [blk_441.res, rv_simp]
  · simp [blk_441.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_441.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_441.res, rv_simp]
theorem fetch_542 (s : MachineState) (hpc : s.pc = pcOf 542) : fetch image s = some (.base .ECALL) :=
  (codeAt_542.fetch s hpc).trans rfl
theorem blk447_spec (s : MachineState) (hpc : s.pc = pcOf 447) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1433 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_447 codeAt_447 s hpc (by simp [blk_447.res,rv_simp]),?_,?_,?_⟩
  · simp [blk_447.res,E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [blk_447.res,rv_simp]
theorem blk1433_spec (s : MachineState) (hpc : s.pc = pcOf 1433) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 1438 ∧
      t.getReg .x22 = 0 ∧ t.getReg .x24 = BitVec.ofNat 64 (SIG+3056) ∧
      t.getReg .x20 = BitVec.ofNat 64 4096 ∧
      RegsExcept s t [.x20,.x22,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_1433 codeAt_1433 s hpc (by simp [blk_1433.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [blk_1433.res,E.eval]
  · simp [blk_1433.res,rv_simp]
  · simp [blk_1433.res,rv_simp,SIG]
  · simp [blk_1433.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1433.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_1433.res,rv_simp]
theorem blk1438_spec (s : MachineState) (hpc : s.pc = pcOf 1438) (leaf lv : Nat)
    (hl : leaf < 4096) (hlv : lv < 12)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf 1456 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getReg .x23 = BitVec.ofNat 64 (leaf/2^lv ^^^ 1) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = BitVec.ofNat 64 (hdr0 13 0 0 lv) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (hdr1 0 ((leaf/2^lv ^^^ 1)/2)) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x23,.x28] ∧
      Frame s t (fun A => A=PRIV+16 ∨ A=PRIV+24) := by
  have hq : leaf/2^lv < 2^12 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hsib := Nat.xor_lt_two_pow hq (show 1<2^12 by norm_num)
  have hs : (BitVec.ofNat 64 leaf >>> (lv%18446744073709551616%64) ^^^ 1#64) =
      BitVec.ofNat 64 (leaf/2^lv ^^^ 1) := by
    rw [Nat.mod_eq_of_lt (by omega : lv<18446744073709551616), Nat.mod_eq_of_lt (by omega : lv<64),
      ofNat_shr leaf lv (by omega), ofNat_xor _ 1 (by omega) (by norm_num)]
  refine ⟨_,symRun_sound blk_1438 codeAt_1438 s hpc (by simp [blk_1438.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_1438.res,E.eval]
  · simp [blk_1438.res,rv_simp]
  · simp [blk_1438.res,rv_simp]
  · simp [blk_1438.res,rv_simp,MOUT]
  · simp only [Result.toState_getReg,blk_1438.res]; t3n [h14,h22]; exact hs
  · simp only [Result.toState_getMem,blk_1438.res,PRIV]; t3n [h22]
    rw [ofNat_or_disjoint' 3329 (lv*4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 lv (by norm_num) (by norm_num) (by norm_num) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem,blk_1438.res,PRIV]; t3n [h14,h22]
    rw [hs,ofNat_shr _ 1 (by omega),pow_one,ofNat_shl,
      hdr1_eq 0 _ (by norm_num) (by omega)]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1438.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem,blk_1438.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]
theorem fetch_1456 (s : MachineState) (hpc : s.pc = pcOf 1456) :
    fetch image s = some (.base .ECALL) := (codeAt_1456.fetch s hpc).trans rfl
theorem blk1457_spec (s : MachineState) (hpc : s.pc = pcOf 1457) (sib lo lv out : Nat)
    (hlo2 : 2≤lo) (hlo : lo≤4096) (hsib : sib<lo) (hlv : lv<12)
    (hout0 : SIG+3056≤out) (hout : out+16≤SIG+3248) (hout8 : out%8=0)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 sib) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) (h24 : s.getReg .x24 = BitVec.ofNat 64 out)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 MOUT) :
    ∃ t, Steps image s 25 25 t ∧ t.pc = (if lv+1<12 then pcOf 1438 else pcOf 1482) ∧
      t.getMem (BitVec.ofNat 64 out) =
        s.getMem (BitVec.ofNat 64 (REGION+16*(8192-2*lo+sib))) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+16*(sib%2))) ∧
      t.getMem (BitVec.ofNat 64 (out+8)) =
        s.getMem (BitVec.ofNat 64 (REGION+16*(8192-2*lo+sib)+8)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+16*(sib%2)+8)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (out+16) ∧ t.getReg .x20 = BitVec.ofNat 64 (lo/2) ∧
      t.getReg .x22 = BitVec.ofNat 64 (lv+1) ∧
      RegsExcept s t [.x6,.x7,.x20,.x22,.x24,.x28,.x29] ∧
      Frame s t (fun A => A=out ∨ A=out+8) := by
  have hmod : sib%2<2 := Nat.mod_lt _ (by decide)
  have ha : (8192#64-BitVec.ofNat 64 (lo*2)+BitVec.ofNat 64 sib) <<< 4 =
      BitVec.ofNat 64 (16*(8192-2*lo+sib)) := by
    rw [show (8192#64 : Word)=BitVec.ofNat 64 8192 from rfl,
      ofNat_sub_ofNat _ _ (by norm_num) (by omega), ofNat_add_ofNat,ofNat_shl]
    congr 1; omega
  have hm : (BitVec.ofNat 64 sib &&& 1#64) <<< 4 = BitVec.ofNat 64 (16*(sib%2)) := by
    rw [show (1#64 : Word)=BitVec.ofNat 64 (2^1-1) from rfl,
      ofNat_and_mask sib 1 (by norm_num),ofNat_shl]
    congr 1; omega
  have hobl : Oblig.all s blk_1457.res.st.obl := by
    simp only [blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    repeat' constructor <;> omega
  refine ⟨_,symRun_sound blk_1457 codeAt_1457 s hpc hobl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_1457.res,E.eval,CmpOp.eval,BinOp.eval,h22]
    have hx : (BitVec.ofNat 64 lv+1#64).toNat=lv+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,hx]
    rfl
  · simp only [Result.toState_getMem,blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    rw [if_neg (by omega),if_pos (by omega)]
    congr 3 <;> omega
  · simp only [Result.toState_getMem,blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    congr 3 <;> omega
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h24]
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h20]
    rw [ofNat_shr lo 1 (by omega),pow_one]
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1457.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG] at *
    simp only [Result.toState_getMem,blk_1457.res]
    t3n [h24]
    rw [if_neg (by omega),if_neg (by omega)]
theorem blk1482_spec (s : MachineState) (hpc : s.pc = pcOf 1482) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 540 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_1482 codeAt_1482 s hpc (by simp [blk_1482.res,rv_simp]),?_,?_,?_⟩
  · simp [blk_1482.res,E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [blk_1482.res,rv_simp]
end SigGolfCandidate.T3M.Sign

namespace SigGolfCandidate.T3M.Sign.SharedTopBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
/-- Campaign T51: the top-signing call at 441 with word 445 `addi s7,s7,-1856` (51 top values at `SIG + 2240`,
slot 140; #938 `-1904`, slot 137, 54 values; the top path stays at slot 191). -/
def seg_441S : List (BitVec 32) := [1052563,133943,1108019987,35767,0x8c0b8b93,344981743]
sym_block blk_441S := symRun { noAlias := true } seg_441S (pcOf 441) 100
structure Code (im : Image) : Prop where
  codeAt_441 : CodeAt im (pcOf 441) seg_441S
  codeAt_447 : CodeAt im (pcOf 447) seg_447
  codeAt_1433 : CodeAt im (pcOf 1433) seg_1433
  codeAt_1438 : CodeAt im (pcOf 1438) seg_1438
  codeAt_1456 : CodeAt im (pcOf 1456) seg_1456
  codeAt_1457 : CodeAt im (pcOf 1457) seg_1457
  codeAt_1482 : CodeAt im (pcOf 1482) seg_1482
variable {im : Image}
theorem blk441_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 441) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 447 ∧
      t.getReg .x31 = BitVec.ofNat 64 1 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = BitVec.ofNat 64 (SIG + 2240) ∧
      RegsExcept s t [.x1, .x22, .x23, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_441S hcode.codeAt_441 s hpc (by simp [blk_441S.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_441S.res, E.eval]
  · simp [blk_441S.res, rv_simp]
  · simp [blk_441S.res, rv_simp]
  · simp [blk_441S.res, rv_simp]
  · simp [blk_441S.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_441S.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_441S.res, rv_simp]
theorem blk447_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 447) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1433 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_447 hcode.codeAt_447 s hpc (by simp [blk_447.res,rv_simp]),?_,?_,?_⟩
  · simp [blk_447.res,E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [blk_447.res,rv_simp]
theorem blk1433_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1433) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 1438 ∧
      t.getReg .x22 = 0 ∧ t.getReg .x24 = BitVec.ofNat 64 (SIG+3056) ∧
      t.getReg .x20 = BitVec.ofNat 64 4096 ∧
      RegsExcept s t [.x20,.x22,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_1433 hcode.codeAt_1433 s hpc (by simp [blk_1433.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [blk_1433.res,E.eval]
  · simp [blk_1433.res,rv_simp]
  · simp [blk_1433.res,rv_simp,SIG]
  · simp [blk_1433.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1433.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_1433.res,rv_simp]
theorem blk1438_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1438) (leaf lv : Nat)
    (hl : leaf < 4096) (hlv : lv < 12)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 leaf) (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf 1456 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getReg .x23 = BitVec.ofNat 64 (leaf/2^lv ^^^ 1) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = BitVec.ofNat 64 (hdr0 13 0 0 lv) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (hdr1 0 ((leaf/2^lv ^^^ 1)/2)) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x23,.x28] ∧
      Frame s t (fun A => A=PRIV+16 ∨ A=PRIV+24) := by
  have hq : leaf/2^lv < 2^12 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hsib := Nat.xor_lt_two_pow hq (show 1<2^12 by norm_num)
  have hs : (BitVec.ofNat 64 leaf >>> (lv%18446744073709551616%64) ^^^ 1#64) =
      BitVec.ofNat 64 (leaf/2^lv ^^^ 1) := by
    rw [Nat.mod_eq_of_lt (by omega : lv<18446744073709551616), Nat.mod_eq_of_lt (by omega : lv<64),
      ofNat_shr leaf lv (by omega), ofNat_xor _ 1 (by omega) (by norm_num)]
  refine ⟨_,symRun_sound blk_1438 hcode.codeAt_1438 s hpc (by simp [blk_1438.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_1438.res,E.eval]
  · simp [blk_1438.res,rv_simp]
  · simp [blk_1438.res,rv_simp]
  · simp [blk_1438.res,rv_simp,MOUT]
  · simp only [Result.toState_getReg,blk_1438.res]; t3n [h14,h22]; exact hs
  · simp only [Result.toState_getMem,blk_1438.res,PRIV]; t3n [h22]
    rw [ofNat_or_disjoint' 3329 (lv*4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 lv (by norm_num) (by norm_num) (by norm_num) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem,blk_1438.res,PRIV]; t3n [h14,h22]
    rw [hs,ofNat_shr _ 1 (by omega),pow_one,ofNat_shl,
      hdr1_eq 0 _ (by norm_num) (by omega)]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1438.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem,blk_1438.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]
theorem fetch_1456 (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1456) :
    fetch im s = some (.base .ECALL) := (hcode.codeAt_1456.fetch s hpc).trans rfl
theorem blk1457_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1457) (sib lo lv out : Nat)
    (hlo2 : 2≤lo) (hlo : lo≤4096) (hsib : sib<lo) (hlv : lv<12)
    (hout0 : SIG+3056≤out) (hout : out+16≤SIG+3248) (hout8 : out%8=0)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 sib) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 lv) (h24 : s.getReg .x24 = BitVec.ofNat 64 out)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 MOUT) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = (if lv+1<12 then pcOf 1438 else pcOf 1482) ∧
      t.getMem (BitVec.ofNat 64 out) =
        s.getMem (BitVec.ofNat 64 (REGION+16*(8192-2*lo+sib))) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+16*(sib%2))) ∧
      t.getMem (BitVec.ofNat 64 (out+8)) =
        s.getMem (BitVec.ofNat 64 (REGION+16*(8192-2*lo+sib)+8)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+16*(sib%2)+8)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (out+16) ∧ t.getReg .x20 = BitVec.ofNat 64 (lo/2) ∧
      t.getReg .x22 = BitVec.ofNat 64 (lv+1) ∧
      RegsExcept s t [.x6,.x7,.x20,.x22,.x24,.x28,.x29] ∧
      Frame s t (fun A => A=out ∨ A=out+8) := by
  have hmod : sib%2<2 := Nat.mod_lt _ (by decide)
  have ha : (8192#64-BitVec.ofNat 64 (lo*2)+BitVec.ofNat 64 sib) <<< 4 =
      BitVec.ofNat 64 (16*(8192-2*lo+sib)) := by
    rw [show (8192#64 : Word)=BitVec.ofNat 64 8192 from rfl,
      ofNat_sub_ofNat _ _ (by norm_num) (by omega), ofNat_add_ofNat,ofNat_shl]
    congr 1; omega
  have hm : (BitVec.ofNat 64 sib &&& 1#64) <<< 4 = BitVec.ofNat 64 (16*(sib%2)) := by
    rw [show (1#64 : Word)=BitVec.ofNat 64 (2^1-1) from rfl,
      ofNat_and_mask sib 1 (by norm_num),ofNat_shl]
    congr 1; omega
  have hobl : Oblig.all s blk_1457.res.st.obl := by
    simp only [blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    repeat' constructor <;> omega
  refine ⟨_,symRun_sound blk_1457 hcode.codeAt_1457 s hpc hobl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_1457.res,E.eval,CmpOp.eval,BinOp.eval,h22]
    have hx : (BitVec.ofNat 64 lv+1#64).toNat=lv+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,hx]
    rfl
  · simp only [Result.toState_getMem,blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    rw [if_neg (by omega),if_pos (by omega)]
    congr 3 <;> omega
  · simp only [Result.toState_getMem,blk_1457.res]
    t3n [h20,h23,h24,h12]
    rw [ha,hm]
    t3n []
    simp only [SIG,REGION,MOUT] at *
    congr 3 <;> omega
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h24]
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h20]
    rw [ofNat_shr lo 1 (by omega),pow_one]
  · simp only [Result.toState_getReg,blk_1457.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1457.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG] at *
    simp only [Result.toState_getMem,blk_1457.res]
    t3n [h24]
    rw [if_neg (by omega),if_neg (by omega)]
theorem blk1482_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1482) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 540 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_1482 hcode.codeAt_1482 s hpc (by simp [blk_1482.res,rv_simp]),?_,?_,?_⟩
  · simp [blk_1482.res,E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [blk_1482.res,rv_simp]

end SigGolfCandidate.T3M.Sign.SharedTopBlocks

namespace SigGolfCandidate.T3M.Sign.SharedTopBlocks
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> exact codeAt_sign_current_slice (by decide +kernel) (by decide +kernel)

end SigGolfCandidate.T3M.Sign.SharedTopBlocks
end
-- ==== merged from W9Machine_WctN600Evidence ====
section

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
end
-- ==== merged from W9Machine_WctN600Check00 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine0 : ChainRoutine := ⟨0, [0, 0, 0, 0, 3, 4], [⟨195584, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨195589, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195591, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨195594, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨195599, [0x7508a3, 0x73], .rung 1 none⟩, ⟨195601, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195603, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195606, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine1 : ChainRoutine := ⟨1, [0, 0, 0, 0, 4, 3], [⟨195648, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨195653, [0x7508a3, 0x73], .rung 1 none⟩, ⟨195655, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195657, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨195660, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨195665, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195667, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195670, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine2 : ChainRoutine := ⟨2, [0, 0, 0, 1, 2, 4], [⟨195712, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨195717, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨195722, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨195725, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨195730, [0x7508a3, 0x73], .rung 1 none⟩, ⟨195732, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195734, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195737, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine3 : ChainRoutine := ⟨3, [0, 0, 0, 1, 3, 3], [⟨195776, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨195781, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨195786, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195788, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨195791, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨195796, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195798, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195801, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine4 : ChainRoutine := ⟨4, [0, 0, 0, 1, 4, 2], [⟨195840, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨195845, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨195850, [0x7508a3, 0x73], .rung 1 none⟩, ⟨195852, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195854, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨195857, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨195862, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195865, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine5 : ChainRoutine := ⟨5, [0, 0, 0, 2, 1, 4], [⟨195904, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨195909, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨195912, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨195917, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨195922, [0x7508a3, 0x73], .rung 1 none⟩, ⟨195924, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195926, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195929, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine6 : ChainRoutine := ⟨6, [0, 0, 0, 2, 2, 3], [⟨195968, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨195973, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨195976, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨195981, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨195984, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨195989, [0xd508a3, 0x73], .rung 2 none⟩, ⟨195991, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨195994, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine7 : ChainRoutine := ⟨7, [0, 0, 0, 2, 3, 2], [⟨196032, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨196037, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196040, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨196045, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196047, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196050, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨196055, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196058, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch0 : List (ChainRoutine × Nat) := [(routine0, 76), (routine1, 76), (routine2, 79), (routine3, 79), (routine4, 79), (routine5, 79), (routine6, 80), (routine7, 80)]
theorem batch0_checked : (batch0.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready0 : Chain.RoutineReady (embed ⟨0, by decide⟩) routine0 ∧ planCycles routine0.pieces ≤ rankCost ⟨0, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine0, 76) (by unfold batch0; exact List.mem_cons_self)
theorem ready1 : Chain.RoutineReady (embed ⟨1, by decide⟩) routine1 ∧ planCycles routine1.pieces ≤ rankCost ⟨1, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine1, 76) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready2 : Chain.RoutineReady (embed ⟨2, by decide⟩) routine2 ∧ planCycles routine2.pieces ≤ rankCost ⟨2, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine2, 79) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready3 : Chain.RoutineReady (embed ⟨3, by decide⟩) routine3 ∧ planCycles routine3.pieces ≤ rankCost ⟨3, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine3, 79) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready4 : Chain.RoutineReady (embed ⟨4, by decide⟩) routine4 ∧ planCycles routine4.pieces ≤ rankCost ⟨4, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine4, 79) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready5 : Chain.RoutineReady (embed ⟨5, by decide⟩) routine5 ∧ planCycles routine5.pieces ≤ rankCost ⟨5, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine5, 79) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready6 : Chain.RoutineReady (embed ⟨6, by decide⟩) routine6 ∧ planCycles routine6.pieces ≤ rankCost ⟨6, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine6, 80) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready7 : Chain.RoutineReady (embed ⟨7, by decide⟩) routine7 ∧ planCycles routine7.pieces ≤ rankCost ⟨7, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch0_checked (routine7, 80) (by unfold batch0; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check01 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine8 : ChainRoutine := ⟨8, [0, 0, 0, 2, 4, 1], [⟨196096, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨196101, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196104, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨196109, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196111, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196113, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196116, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨196121, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine9 : ChainRoutine := ⟨9, [0, 0, 0, 3, 0, 4], [⟨196160, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196165, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196167, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196169, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨196173, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨196178, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196180, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196182, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196185, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine10 : ChainRoutine := ⟨10, [0, 0, 0, 3, 1, 3], [⟨196224, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196229, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196231, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196234, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨196239, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨196244, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196246, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196249, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine11 : ChainRoutine := ⟨11, [0, 0, 0, 3, 2, 2], [⟨196288, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196293, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196295, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196298, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨196303, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196306, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨196311, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196314, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine12 : ChainRoutine := ⟨12, [0, 0, 0, 3, 3, 1], [⟨196352, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196357, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196359, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196362, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨196367, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196369, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196372, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨196377, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine13 : ChainRoutine := ⟨13, [0, 0, 0, 3, 4, 0], [⟨196416, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨196421, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196423, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196426, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨196431, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196433, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196435, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196437, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨196441, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine14 : ChainRoutine := ⟨14, [0, 0, 0, 4, 0, 3], [⟨196480, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨196485, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196487, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196489, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196491, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨196495, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨196500, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196502, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196505, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine15 : ChainRoutine := ⟨15, [0, 0, 0, 4, 1, 2], [⟨196544, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨196549, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196551, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196553, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196556, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨196561, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨196566, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196569, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch1 : List (ChainRoutine × Nat) := [(routine8, 79), (routine9, 79), (routine10, 79), (routine11, 80), (routine12, 79), (routine13, 79), (routine14, 79), (routine15, 79)]
theorem batch1_checked : (batch1.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready8 : Chain.RoutineReady (embed ⟨8, by decide⟩) routine8 ∧ planCycles routine8.pieces ≤ rankCost ⟨8, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine8, 79) (by unfold batch1; exact List.mem_cons_self)
theorem ready9 : Chain.RoutineReady (embed ⟨9, by decide⟩) routine9 ∧ planCycles routine9.pieces ≤ rankCost ⟨9, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine9, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready10 : Chain.RoutineReady (embed ⟨10, by decide⟩) routine10 ∧ planCycles routine10.pieces ≤ rankCost ⟨10, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine10, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready11 : Chain.RoutineReady (embed ⟨11, by decide⟩) routine11 ∧ planCycles routine11.pieces ≤ rankCost ⟨11, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine11, 80) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready12 : Chain.RoutineReady (embed ⟨12, by decide⟩) routine12 ∧ planCycles routine12.pieces ≤ rankCost ⟨12, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine12, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready13 : Chain.RoutineReady (embed ⟨13, by decide⟩) routine13 ∧ planCycles routine13.pieces ≤ rankCost ⟨13, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine13, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready14 : Chain.RoutineReady (embed ⟨14, by decide⟩) routine14 ∧ planCycles routine14.pieces ≤ rankCost ⟨14, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine14, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready15 : Chain.RoutineReady (embed ⟨15, by decide⟩) routine15 ∧ planCycles routine15.pieces ≤ rankCost ⟨15, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch1_checked (routine15, 79) (by unfold batch1; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check02 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine16 : ChainRoutine := ⟨16, [0, 0, 0, 4, 2, 1], [⟨196608, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨196613, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196615, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196617, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196620, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨196625, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196628, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨196633, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine17 : ChainRoutine := ⟨17, [0, 0, 0, 4, 3, 0], [⟨196672, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨196677, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196679, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196681, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨196684, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨196689, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196691, [0x13508a3, 0x73], .rung 3 none⟩, ⟨196693, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨196697, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine18 : ChainRoutine := ⟨18, [0, 0, 1, 0, 2, 4], [⟨196736, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨196741, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨196745, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨196750, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196753, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨196758, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196760, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196762, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196765, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine19 : ChainRoutine := ⟨19, [0, 0, 1, 0, 3, 3], [⟨196800, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨196805, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨196809, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨196814, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196816, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196819, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨196824, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196826, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196829, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine20 : ChainRoutine := ⟨20, [0, 0, 1, 0, 4, 2], [⟨196864, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨196869, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨196873, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨196878, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196880, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196882, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨196885, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨196890, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196893, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine21 : ChainRoutine := ⟨21, [0, 0, 1, 1, 1, 4], [⟨196928, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨196933, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨196938, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨196943, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨196948, [0x7508a3, 0x73], .rung 1 none⟩, ⟨196950, [0xd508a3, 0x73], .rung 2 none⟩, ⟨196952, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨196955, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine22 : ChainRoutine := ⟨22, [0, 0, 1, 1, 2, 3], [⟨196992, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨196997, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨197002, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨197007, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨197010, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨197015, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197017, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197020, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine23 : ChainRoutine := ⟨23, [0, 0, 1, 1, 3, 2], [⟨197056, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197061, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨197066, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨197071, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197073, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨197076, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨197081, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197084, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch2 : List (ChainRoutine × Nat) := [(routine16, 79), (routine17, 79), (routine18, 83), (routine19, 83), (routine20, 83), (routine21, 81), (routine22, 82), (routine23, 82)]
theorem batch2_checked : (batch2.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready16 : Chain.RoutineReady (embed ⟨16, by decide⟩) routine16 ∧ planCycles routine16.pieces ≤ rankCost ⟨16, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine16, 79) (by unfold batch2; exact List.mem_cons_self)
theorem ready17 : Chain.RoutineReady (embed ⟨17, by decide⟩) routine17 ∧ planCycles routine17.pieces ≤ rankCost ⟨17, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine17, 79) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready18 : Chain.RoutineReady (embed ⟨18, by decide⟩) routine18 ∧ planCycles routine18.pieces ≤ rankCost ⟨18, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine18, 83) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready19 : Chain.RoutineReady (embed ⟨19, by decide⟩) routine19 ∧ planCycles routine19.pieces ≤ rankCost ⟨19, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine19, 83) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready20 : Chain.RoutineReady (embed ⟨20, by decide⟩) routine20 ∧ planCycles routine20.pieces ≤ rankCost ⟨20, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine20, 83) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready21 : Chain.RoutineReady (embed ⟨21, by decide⟩) routine21 ∧ planCycles routine21.pieces ≤ rankCost ⟨21, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine21, 81) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready22 : Chain.RoutineReady (embed ⟨22, by decide⟩) routine22 ∧ planCycles routine22.pieces ≤ rankCost ⟨22, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine22, 82) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready23 : Chain.RoutineReady (embed ⟨23, by decide⟩) routine23 ∧ planCycles routine23.pieces ≤ rankCost ⟨23, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch2_checked (routine23, 82) (by unfold batch2; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check03 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine24 : ChainRoutine := ⟨24, [0, 0, 1, 1, 4, 1], [⟨197120, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197125, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨197130, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨197135, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197137, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197139, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨197142, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨197147, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine25 : ChainRoutine := ⟨25, [0, 0, 1, 2, 0, 4], [⟨197184, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197189, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨197194, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197196, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨197200, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨197205, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197207, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197209, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197212, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine26 : ChainRoutine := ⟨26, [0, 0, 1, 2, 1, 3], [⟨197248, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197253, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨197258, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197261, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨197266, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨197271, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197273, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197276, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine27 : ChainRoutine := ⟨27, [0, 0, 1, 2, 2, 2], [⟨197312, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197317, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨197322, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197325, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨197330, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨197333, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨197338, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197341, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine28 : ChainRoutine := ⟨28, [0, 0, 1, 2, 3, 1], [⟨197376, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197381, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨197386, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197389, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨197394, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197396, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨197399, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨197404, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine29 : ChainRoutine := ⟨29, [0, 0, 1, 2, 4, 0], [⟨197440, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197445, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨197450, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197453, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨197458, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197460, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197462, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197464, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨197468, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine30 : ChainRoutine := ⟨30, [0, 0, 1, 3, 0, 3], [⟨197504, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197509, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨197514, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197516, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197518, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨197522, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨197527, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197529, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197532, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine31 : ChainRoutine := ⟨31, [0, 0, 1, 3, 1, 2], [⟨197568, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197573, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨197578, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197580, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197583, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨197588, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨197593, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197596, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch3 : List (ChainRoutine × Nat) := [(routine24, 81), (routine25, 82), (routine26, 82), (routine27, 83), (routine28, 82), (routine29, 82), (routine30, 82), (routine31, 82)]
theorem batch3_checked : (batch3.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready24 : Chain.RoutineReady (embed ⟨24, by decide⟩) routine24 ∧ planCycles routine24.pieces ≤ rankCost ⟨24, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine24, 81) (by unfold batch3; exact List.mem_cons_self)
theorem ready25 : Chain.RoutineReady (embed ⟨25, by decide⟩) routine25 ∧ planCycles routine25.pieces ≤ rankCost ⟨25, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine25, 82) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready26 : Chain.RoutineReady (embed ⟨26, by decide⟩) routine26 ∧ planCycles routine26.pieces ≤ rankCost ⟨26, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine26, 82) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready27 : Chain.RoutineReady (embed ⟨27, by decide⟩) routine27 ∧ planCycles routine27.pieces ≤ rankCost ⟨27, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine27, 83) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready28 : Chain.RoutineReady (embed ⟨28, by decide⟩) routine28 ∧ planCycles routine28.pieces ≤ rankCost ⟨28, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine28, 82) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready29 : Chain.RoutineReady (embed ⟨29, by decide⟩) routine29 ∧ planCycles routine29.pieces ≤ rankCost ⟨29, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine29, 82) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready30 : Chain.RoutineReady (embed ⟨30, by decide⟩) routine30 ∧ planCycles routine30.pieces ≤ rankCost ⟨30, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine30, 82) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready31 : Chain.RoutineReady (embed ⟨31, by decide⟩) routine31 ∧ planCycles routine31.pieces ≤ rankCost ⟨31, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch3_checked (routine31, 82) (by unfold batch3; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check04 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine32 : ChainRoutine := ⟨32, [0, 0, 1, 3, 2, 1], [⟨197632, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197637, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨197642, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197644, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197647, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨197652, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨197655, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨197660, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine33 : ChainRoutine := ⟨33, [0, 0, 1, 3, 3, 0], [⟨197696, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197701, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨197706, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197708, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197711, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨197716, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197718, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197720, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨197724, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine34 : ChainRoutine := ⟨34, [0, 0, 1, 4, 0, 2], [⟨197760, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197765, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨197770, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197772, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197774, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197776, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨197780, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨197785, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197788, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine35 : ChainRoutine := ⟨35, [0, 0, 1, 4, 1, 1], [⟨197824, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197829, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨197834, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197836, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197838, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197841, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨197846, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨197851, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine36 : ChainRoutine := ⟨36, [0, 0, 1, 4, 2, 0], [⟨197888, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨197893, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨197898, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197900, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197902, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨197905, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨197910, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197912, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨197916, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine37 : ChainRoutine := ⟨37, [0, 0, 2, 0, 1, 4], [⟨197952, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨197957, [0x13508a3, 0x73], .rung 3 none⟩, ⟨197959, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨197963, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨197968, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨197973, [0x7508a3, 0x73], .rung 1 none⟩, ⟨197975, [0xd508a3, 0x73], .rung 2 none⟩, ⟨197977, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨197980, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine38 : ChainRoutine := ⟨38, [0, 0, 2, 0, 2, 3], [⟨198016, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198021, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198023, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨198027, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨198032, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨198035, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨198040, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198042, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198045, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine39 : ChainRoutine := ⟨39, [0, 0, 2, 0, 3, 2], [⟨198080, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198085, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198087, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨198091, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨198096, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198098, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨198101, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨198106, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198109, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch4 : List (ChainRoutine × Nat) := [(routine32, 82), (routine33, 82), (routine34, 82), (routine35, 81), (routine36, 82), (routine37, 82), (routine38, 83), (routine39, 83)]
theorem batch4_checked : (batch4.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready32 : Chain.RoutineReady (embed ⟨32, by decide⟩) routine32 ∧ planCycles routine32.pieces ≤ rankCost ⟨32, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine32, 82) (by unfold batch4; exact List.mem_cons_self)
theorem ready33 : Chain.RoutineReady (embed ⟨33, by decide⟩) routine33 ∧ planCycles routine33.pieces ≤ rankCost ⟨33, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine33, 82) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready34 : Chain.RoutineReady (embed ⟨34, by decide⟩) routine34 ∧ planCycles routine34.pieces ≤ rankCost ⟨34, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine34, 82) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready35 : Chain.RoutineReady (embed ⟨35, by decide⟩) routine35 ∧ planCycles routine35.pieces ≤ rankCost ⟨35, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine35, 81) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready36 : Chain.RoutineReady (embed ⟨36, by decide⟩) routine36 ∧ planCycles routine36.pieces ≤ rankCost ⟨36, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine36, 82) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready37 : Chain.RoutineReady (embed ⟨37, by decide⟩) routine37 ∧ planCycles routine37.pieces ≤ rankCost ⟨37, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine37, 82) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready38 : Chain.RoutineReady (embed ⟨38, by decide⟩) routine38 ∧ planCycles routine38.pieces ≤ rankCost ⟨38, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine38, 83) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready39 : Chain.RoutineReady (embed ⟨39, by decide⟩) routine39 ∧ planCycles routine39.pieces ≤ rankCost ⟨39, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch4_checked (routine39, 83) (by unfold batch4; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check05 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine40 : ChainRoutine := ⟨40, [0, 0, 2, 0, 4, 1], [⟨198144, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198149, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198151, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨198155, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨198160, [0x7508a3, 0x73], .rung 1 none⟩, ⟨198162, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198164, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨198167, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨198172, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine41 : ChainRoutine := ⟨41, [0, 0, 2, 1, 0, 4], [⟨198208, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198213, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198216, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨198221, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨198225, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨198230, [0x7508a3, 0x73], .rung 1 none⟩, ⟨198232, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198234, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198237, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine42 : ChainRoutine := ⟨42, [0, 0, 2, 1, 1, 3], [⟨198272, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198277, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198280, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨198285, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨198290, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨198295, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198297, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198300, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine43 : ChainRoutine := ⟨43, [0, 0, 2, 1, 2, 2], [⟨198336, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198341, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198344, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨198349, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨198354, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨198357, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨198362, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198365, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine44 : ChainRoutine := ⟨44, [0, 0, 2, 1, 3, 1], [⟨198400, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198405, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198408, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨198413, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨198418, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198420, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨198423, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨198428, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine45 : ChainRoutine := ⟨45, [0, 0, 2, 1, 4, 0], [⟨198464, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198469, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198472, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨198477, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨198482, [0x7508a3, 0x73], .rung 1 none⟩, ⟨198484, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198486, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198488, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨198492, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine46 : ChainRoutine := ⟨46, [0, 0, 2, 2, 0, 3], [⟨198528, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198533, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198536, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨198541, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198543, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨198547, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨198552, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198554, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198557, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine47 : ChainRoutine := ⟨47, [0, 0, 2, 2, 1, 2], [⟨198592, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198597, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198600, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨198605, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨198608, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨198613, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨198618, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198621, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch5 : List (ChainRoutine × Nat) := [(routine40, 82), (routine41, 83), (routine42, 82), (routine43, 83), (routine44, 82), (routine45, 82), (routine46, 83), (routine47, 83)]
theorem batch5_checked : (batch5.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready40 : Chain.RoutineReady (embed ⟨40, by decide⟩) routine40 ∧ planCycles routine40.pieces ≤ rankCost ⟨40, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine40, 82) (by unfold batch5; exact List.mem_cons_self)
theorem ready41 : Chain.RoutineReady (embed ⟨41, by decide⟩) routine41 ∧ planCycles routine41.pieces ≤ rankCost ⟨41, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine41, 83) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready42 : Chain.RoutineReady (embed ⟨42, by decide⟩) routine42 ∧ planCycles routine42.pieces ≤ rankCost ⟨42, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine42, 82) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready43 : Chain.RoutineReady (embed ⟨43, by decide⟩) routine43 ∧ planCycles routine43.pieces ≤ rankCost ⟨43, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine43, 83) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready44 : Chain.RoutineReady (embed ⟨44, by decide⟩) routine44 ∧ planCycles routine44.pieces ≤ rankCost ⟨44, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine44, 82) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready45 : Chain.RoutineReady (embed ⟨45, by decide⟩) routine45 ∧ planCycles routine45.pieces ≤ rankCost ⟨45, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine45, 82) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready46 : Chain.RoutineReady (embed ⟨46, by decide⟩) routine46 ∧ planCycles routine46.pieces ≤ rankCost ⟨46, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine46, 83) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready47 : Chain.RoutineReady (embed ⟨47, by decide⟩) routine47 ∧ planCycles routine47.pieces ≤ rankCost ⟨47, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch5_checked (routine47, 83) (by unfold batch5; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check06 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine48 : ChainRoutine := ⟨48, [0, 0, 2, 2, 2, 1], [⟨198656, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198661, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198664, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨198669, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨198672, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨198677, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨198680, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨198685, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine49 : ChainRoutine := ⟨49, [0, 0, 2, 2, 3, 0], [⟨198720, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198725, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198728, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨198733, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨198736, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨198741, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198743, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198745, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨198749, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine50 : ChainRoutine := ⟨50, [0, 0, 2, 3, 0, 2], [⟨198784, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198789, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198792, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨198797, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198799, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198801, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨198805, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨198810, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨198813, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine51 : ChainRoutine := ⟨51, [0, 0, 2, 3, 1, 1], [⟨198848, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198853, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198856, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨198861, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198863, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨198866, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨198871, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨198876, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine52 : ChainRoutine := ⟨52, [0, 0, 2, 3, 2, 0], [⟨198912, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198917, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198920, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨198925, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198927, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨198930, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨198935, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198937, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨198941, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine53 : ChainRoutine := ⟨53, [0, 0, 2, 4, 0, 1], [⟨198976, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨198981, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨198984, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨198989, [0x7508a3, 0x73], .rung 1 none⟩, ⟨198991, [0xd508a3, 0x73], .rung 2 none⟩, ⟨198993, [0x13508a3, 0x73], .rung 3 none⟩, ⟨198995, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨198999, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨199004, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine54 : ChainRoutine := ⟨54, [0, 0, 2, 4, 1, 0], [⟨199040, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨199045, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199048, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨199053, [0x7508a3, 0x73], .rung 1 none⟩, ⟨199055, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199057, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨199060, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨199065, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨199069, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine55 : ChainRoutine := ⟨55, [0, 0, 3, 0, 0, 4], [⟨199104, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199109, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199111, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199113, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨199117, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨199122, [0x7508a3, 0x73], .rung 1 none⟩, ⟨199124, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199126, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨199129, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch6 : List (ChainRoutine × Nat) := [(routine48, 83), (routine49, 83), (routine50, 83), (routine51, 82), (routine52, 83), (routine53, 82), (routine54, 83), (routine55, 79)]
theorem batch6_checked : (batch6.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready48 : Chain.RoutineReady (embed ⟨48, by decide⟩) routine48 ∧ planCycles routine48.pieces ≤ rankCost ⟨48, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine48, 83) (by unfold batch6; exact List.mem_cons_self)
theorem ready49 : Chain.RoutineReady (embed ⟨49, by decide⟩) routine49 ∧ planCycles routine49.pieces ≤ rankCost ⟨49, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine49, 83) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready50 : Chain.RoutineReady (embed ⟨50, by decide⟩) routine50 ∧ planCycles routine50.pieces ≤ rankCost ⟨50, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine50, 83) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready51 : Chain.RoutineReady (embed ⟨51, by decide⟩) routine51 ∧ planCycles routine51.pieces ≤ rankCost ⟨51, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine51, 82) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready52 : Chain.RoutineReady (embed ⟨52, by decide⟩) routine52 ∧ planCycles routine52.pieces ≤ rankCost ⟨52, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine52, 83) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready53 : Chain.RoutineReady (embed ⟨53, by decide⟩) routine53 ∧ planCycles routine53.pieces ≤ rankCost ⟨53, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine53, 82) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready54 : Chain.RoutineReady (embed ⟨54, by decide⟩) routine54 ∧ planCycles routine54.pieces ≤ rankCost ⟨54, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine54, 83) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready55 : Chain.RoutineReady (embed ⟨55, by decide⟩) routine55 ∧ planCycles routine55.pieces ≤ rankCost ⟨55, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch6_checked (routine55, 79) (by unfold batch6; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check07 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine56 : ChainRoutine := ⟨56, [0, 0, 3, 0, 1, 3], [⟨199168, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199173, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199175, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199177, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨199181, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨199186, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨199191, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199193, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨199196, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine57 : ChainRoutine := ⟨57, [0, 0, 3, 0, 2, 2], [⟨199232, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199237, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199239, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199241, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨199245, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨199250, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨199253, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨199258, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨199261, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine58 : ChainRoutine := ⟨58, [0, 0, 3, 0, 3, 1], [⟨199296, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199301, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199303, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199305, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨199309, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨199314, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199316, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨199319, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨199324, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine59 : ChainRoutine := ⟨59, [0, 0, 3, 0, 4, 0], [⟨199360, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199365, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199367, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199369, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨199373, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨199378, [0x7508a3, 0x73], .rung 1 none⟩, ⟨199380, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199382, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199384, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨199388, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine60 : ChainRoutine := ⟨60, [0, 0, 3, 1, 0, 3], [⟨199424, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199429, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199431, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199434, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨199439, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨199443, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨199448, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199450, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨199453, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine61 : ChainRoutine := ⟨61, [0, 0, 3, 1, 1, 2], [⟨199488, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199493, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199495, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199498, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨199503, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨199508, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨199513, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨199516, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine62 : ChainRoutine := ⟨62, [0, 0, 3, 1, 2, 1], [⟨199552, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199557, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199559, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199562, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨199567, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨199572, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨199575, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨199580, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine63 : ChainRoutine := ⟨63, [0, 0, 3, 1, 3, 0], [⟨199616, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199621, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199623, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199626, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨199631, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨199636, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199638, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199640, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨199644, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch7 : List (ChainRoutine × Nat) := [(routine56, 82), (routine57, 83), (routine58, 82), (routine59, 82), (routine60, 83), (routine61, 82), (routine62, 82), (routine63, 82)]
theorem batch7_checked : (batch7.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready56 : Chain.RoutineReady (embed ⟨56, by decide⟩) routine56 ∧ planCycles routine56.pieces ≤ rankCost ⟨56, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine56, 82) (by unfold batch7; exact List.mem_cons_self)
theorem ready57 : Chain.RoutineReady (embed ⟨57, by decide⟩) routine57 ∧ planCycles routine57.pieces ≤ rankCost ⟨57, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine57, 83) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready58 : Chain.RoutineReady (embed ⟨58, by decide⟩) routine58 ∧ planCycles routine58.pieces ≤ rankCost ⟨58, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine58, 82) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready59 : Chain.RoutineReady (embed ⟨59, by decide⟩) routine59 ∧ planCycles routine59.pieces ≤ rankCost ⟨59, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine59, 82) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready60 : Chain.RoutineReady (embed ⟨60, by decide⟩) routine60 ∧ planCycles routine60.pieces ≤ rankCost ⟨60, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine60, 83) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready61 : Chain.RoutineReady (embed ⟨61, by decide⟩) routine61 ∧ planCycles routine61.pieces ≤ rankCost ⟨61, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine61, 82) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready62 : Chain.RoutineReady (embed ⟨62, by decide⟩) routine62 ∧ planCycles routine62.pieces ≤ rankCost ⟨62, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine62, 82) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready63 : Chain.RoutineReady (embed ⟨63, by decide⟩) routine63 ∧ planCycles routine63.pieces ≤ rankCost ⟨63, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch7_checked (routine63, 82) (by unfold batch7; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check08 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine64 : ChainRoutine := ⟨64, [0, 0, 3, 2, 0, 2], [⟨199680, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199685, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199687, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199690, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨199695, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199697, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨199701, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨199706, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨199709, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine65 : ChainRoutine := ⟨65, [0, 0, 3, 2, 1, 1], [⟨199744, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199749, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199751, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199754, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨199759, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨199762, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨199767, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨199772, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine66 : ChainRoutine := ⟨66, [0, 0, 3, 2, 2, 0], [⟨199808, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199813, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199815, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199818, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨199823, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨199826, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨199831, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199833, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨199837, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine67 : ChainRoutine := ⟨67, [0, 0, 3, 3, 0, 1], [⟨199872, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199877, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199879, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199882, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨199887, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199889, [0x13508a3, 0x73], .rung 3 none⟩, ⟨199891, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨199895, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨199900, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine68 : ChainRoutine := ⟨68, [0, 0, 3, 3, 1, 0], [⟨199936, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨199941, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199943, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨199946, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨199951, [0xd508a3, 0x73], .rung 2 none⟩, ⟨199953, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨199956, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨199961, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨199965, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine69 : ChainRoutine := ⟨69, [0, 0, 3, 4, 0, 0], [⟨200000, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨200005, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200007, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200010, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨200015, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200017, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200019, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200021, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨200025, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine70 : ChainRoutine := ⟨70, [0, 0, 4, 0, 0, 3], [⟨200064, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200069, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200071, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200073, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200075, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨200079, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨200084, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200086, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200089, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine71 : ChainRoutine := ⟨71, [0, 0, 4, 0, 1, 2], [⟨200128, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200133, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200135, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200137, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200139, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨200143, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨200148, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨200153, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200156, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch8 : List (ChainRoutine × Nat) := [(routine64, 83), (routine65, 82), (routine66, 83), (routine67, 82), (routine68, 83), (routine69, 79), (routine70, 79), (routine71, 82)]
theorem batch8_checked : (batch8.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready64 : Chain.RoutineReady (embed ⟨64, by decide⟩) routine64 ∧ planCycles routine64.pieces ≤ rankCost ⟨64, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine64, 83) (by unfold batch8; exact List.mem_cons_self)
theorem ready65 : Chain.RoutineReady (embed ⟨65, by decide⟩) routine65 ∧ planCycles routine65.pieces ≤ rankCost ⟨65, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine65, 82) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready66 : Chain.RoutineReady (embed ⟨66, by decide⟩) routine66 ∧ planCycles routine66.pieces ≤ rankCost ⟨66, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine66, 83) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready67 : Chain.RoutineReady (embed ⟨67, by decide⟩) routine67 ∧ planCycles routine67.pieces ≤ rankCost ⟨67, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine67, 82) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready68 : Chain.RoutineReady (embed ⟨68, by decide⟩) routine68 ∧ planCycles routine68.pieces ≤ rankCost ⟨68, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine68, 83) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready69 : Chain.RoutineReady (embed ⟨69, by decide⟩) routine69 ∧ planCycles routine69.pieces ≤ rankCost ⟨69, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine69, 79) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready70 : Chain.RoutineReady (embed ⟨70, by decide⟩) routine70 ∧ planCycles routine70.pieces ≤ rankCost ⟨70, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine70, 79) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready71 : Chain.RoutineReady (embed ⟨71, by decide⟩) routine71 ∧ planCycles routine71.pieces ≤ rankCost ⟨71, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch8_checked (routine71, 82) (by unfold batch8; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check09 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine72 : ChainRoutine := ⟨72, [0, 0, 4, 0, 2, 1], [⟨200192, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200197, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200199, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200201, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200203, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨200207, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨200212, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨200215, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨200220, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine73 : ChainRoutine := ⟨73, [0, 0, 4, 0, 3, 0], [⟨200256, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200261, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200263, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200265, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200267, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨200271, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨200276, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200278, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200280, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨200284, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine74 : ChainRoutine := ⟨74, [0, 0, 4, 1, 0, 2], [⟨200320, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200325, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200327, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200329, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200332, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨200337, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨200341, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨200346, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200349, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine75 : ChainRoutine := ⟨75, [0, 0, 4, 1, 1, 1], [⟨200384, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200389, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200391, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200393, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200396, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨200401, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨200406, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨200411, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine76 : ChainRoutine := ⟨76, [0, 0, 4, 1, 2, 0], [⟨200448, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200453, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200455, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200457, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200460, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨200465, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨200470, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200472, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨200476, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine77 : ChainRoutine := ⟨77, [0, 0, 4, 2, 0, 1], [⟨200512, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200517, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200519, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200521, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200524, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨200529, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200531, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨200535, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨200540, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine78 : ChainRoutine := ⟨78, [0, 0, 4, 2, 1, 0], [⟨200576, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200581, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200583, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200585, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200588, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨200593, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨200596, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨200601, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨200605, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine79 : ChainRoutine := ⟨79, [0, 0, 4, 3, 0, 0], [⟨200640, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨200645, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200647, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200649, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨200652, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨200657, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200659, [0x13508a3, 0x73], .rung 3 none⟩, ⟨200661, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨200665, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch9 : List (ChainRoutine × Nat) := [(routine72, 82), (routine73, 82), (routine74, 83), (routine75, 81), (routine76, 82), (routine77, 82), (routine78, 83), (routine79, 79)]
theorem batch9_checked : (batch9.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready72 : Chain.RoutineReady (embed ⟨72, by decide⟩) routine72 ∧ planCycles routine72.pieces ≤ rankCost ⟨72, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine72, 82) (by unfold batch9; exact List.mem_cons_self)
theorem ready73 : Chain.RoutineReady (embed ⟨73, by decide⟩) routine73 ∧ planCycles routine73.pieces ≤ rankCost ⟨73, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine73, 82) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready74 : Chain.RoutineReady (embed ⟨74, by decide⟩) routine74 ∧ planCycles routine74.pieces ≤ rankCost ⟨74, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine74, 83) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready75 : Chain.RoutineReady (embed ⟨75, by decide⟩) routine75 ∧ planCycles routine75.pieces ≤ rankCost ⟨75, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine75, 81) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready76 : Chain.RoutineReady (embed ⟨76, by decide⟩) routine76 ∧ planCycles routine76.pieces ≤ rankCost ⟨76, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine76, 82) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready77 : Chain.RoutineReady (embed ⟨77, by decide⟩) routine77 ∧ planCycles routine77.pieces ≤ rankCost ⟨77, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine77, 82) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready78 : Chain.RoutineReady (embed ⟨78, by decide⟩) routine78 ∧ planCycles routine78.pieces ≤ rankCost ⟨78, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine78, 83) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready79 : Chain.RoutineReady (embed ⟨79, by decide⟩) routine79 ∧ planCycles routine79.pieces ≤ rankCost ⟨79, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch9_checked (routine79, 79) (by unfold batch9; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check10 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine80 : ChainRoutine := ⟨80, [0, 1, 0, 0, 2, 4], [⟨200704, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨200709, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨200713, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨200718, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨200721, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨200726, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200728, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200730, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200733, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine81 : ChainRoutine := ⟨81, [0, 1, 0, 0, 3, 3], [⟨200768, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨200773, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨200777, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨200782, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200784, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨200787, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨200792, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200794, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200797, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine82 : ChainRoutine := ⟨82, [0, 1, 0, 0, 4, 2], [⟨200832, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨200837, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨200841, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨200846, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200848, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200850, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨200853, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨200858, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200861, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine83 : ChainRoutine := ⟨83, [0, 1, 0, 1, 1, 4], [⟨200896, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨200901, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨200905, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨200910, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨200915, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨200920, [0x7508a3, 0x73], .rung 1 none⟩, ⟨200922, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200924, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200927, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine84 : ChainRoutine := ⟨84, [0, 1, 0, 1, 2, 3], [⟨200960, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨200965, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨200969, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨200974, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨200979, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨200982, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨200987, [0xd508a3, 0x73], .rung 2 none⟩, ⟨200989, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨200992, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine85 : ChainRoutine := ⟨85, [0, 1, 0, 1, 3, 2], [⟨201024, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201029, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201033, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨201038, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨201043, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201045, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨201048, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨201053, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201056, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine86 : ChainRoutine := ⟨86, [0, 1, 0, 1, 4, 1], [⟨201088, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201093, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201097, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨201102, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨201107, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201109, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201111, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨201114, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨201119, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine87 : ChainRoutine := ⟨87, [0, 1, 0, 2, 0, 4], [⟨201152, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201157, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201161, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨201166, [0x13508a3, 0x73], .rung 3 none⟩, ⟨201168, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨201172, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨201177, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201179, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201181, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201184, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch10 : List (ChainRoutine × Nat) := [(routine80, 83), (routine81, 83), (routine82, 83), (routine83, 85), (routine84, 86), (routine85, 86), (routine86, 85), (routine87, 86)]
theorem batch10_checked : (batch10.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready80 : Chain.RoutineReady (embed ⟨80, by decide⟩) routine80 ∧ planCycles routine80.pieces ≤ rankCost ⟨80, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine80, 83) (by unfold batch10; exact List.mem_cons_self)
theorem ready81 : Chain.RoutineReady (embed ⟨81, by decide⟩) routine81 ∧ planCycles routine81.pieces ≤ rankCost ⟨81, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine81, 83) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready82 : Chain.RoutineReady (embed ⟨82, by decide⟩) routine82 ∧ planCycles routine82.pieces ≤ rankCost ⟨82, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine82, 83) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready83 : Chain.RoutineReady (embed ⟨83, by decide⟩) routine83 ∧ planCycles routine83.pieces ≤ rankCost ⟨83, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine83, 85) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready84 : Chain.RoutineReady (embed ⟨84, by decide⟩) routine84 ∧ planCycles routine84.pieces ≤ rankCost ⟨84, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine84, 86) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready85 : Chain.RoutineReady (embed ⟨85, by decide⟩) routine85 ∧ planCycles routine85.pieces ≤ rankCost ⟨85, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine85, 86) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready86 : Chain.RoutineReady (embed ⟨86, by decide⟩) routine86 ∧ planCycles routine86.pieces ≤ rankCost ⟨86, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine86, 85) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready87 : Chain.RoutineReady (embed ⟨87, by decide⟩) routine87 ∧ planCycles routine87.pieces ≤ rankCost ⟨87, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch10_checked (routine87, 86) (by unfold batch10; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check11 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine88 : ChainRoutine := ⟨88, [0, 1, 0, 2, 1, 3], [⟨201216, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201221, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201225, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨201230, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201233, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨201238, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨201243, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201245, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201248, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine89 : ChainRoutine := ⟨89, [0, 1, 0, 2, 2, 2], [⟨201280, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201285, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201289, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨201294, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201297, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨201302, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨201305, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨201310, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201313, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine90 : ChainRoutine := ⟨90, [0, 1, 0, 2, 3, 1], [⟨201344, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201349, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201353, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨201358, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201361, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨201366, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201368, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨201371, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨201376, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine91 : ChainRoutine := ⟨91, [0, 1, 0, 2, 4, 0], [⟨201408, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201413, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201417, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨201422, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201425, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨201430, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201432, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201434, [0x13508a3, 0x73], .rung 3 none⟩, ⟨201436, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨201440, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine92 : ChainRoutine := ⟨92, [0, 1, 0, 3, 0, 3], [⟨201472, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201477, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201481, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨201486, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201488, [0x13508a3, 0x73], .rung 3 none⟩, ⟨201490, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨201494, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨201499, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201501, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201504, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine93 : ChainRoutine := ⟨93, [0, 1, 0, 3, 1, 2], [⟨201536, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201541, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201545, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨201550, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201552, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201555, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨201560, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨201565, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201568, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine94 : ChainRoutine := ⟨94, [0, 1, 0, 3, 2, 1], [⟨201600, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201605, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201609, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨201614, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201616, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201619, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨201624, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨201627, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨201632, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine95 : ChainRoutine := ⟨95, [0, 1, 0, 3, 3, 0], [⟨201664, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201669, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201673, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨201678, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201680, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201683, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨201688, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201690, [0x13508a3, 0x73], .rung 3 none⟩, ⟨201692, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨201696, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch11 : List (ChainRoutine × Nat) := [(routine88, 86), (routine89, 87), (routine90, 86), (routine91, 86), (routine92, 86), (routine93, 86), (routine94, 86), (routine95, 86)]
theorem batch11_checked : (batch11.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready88 : Chain.RoutineReady (embed ⟨88, by decide⟩) routine88 ∧ planCycles routine88.pieces ≤ rankCost ⟨88, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine88, 86) (by unfold batch11; exact List.mem_cons_self)
theorem ready89 : Chain.RoutineReady (embed ⟨89, by decide⟩) routine89 ∧ planCycles routine89.pieces ≤ rankCost ⟨89, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine89, 87) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready90 : Chain.RoutineReady (embed ⟨90, by decide⟩) routine90 ∧ planCycles routine90.pieces ≤ rankCost ⟨90, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine90, 86) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready91 : Chain.RoutineReady (embed ⟨91, by decide⟩) routine91 ∧ planCycles routine91.pieces ≤ rankCost ⟨91, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine91, 86) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready92 : Chain.RoutineReady (embed ⟨92, by decide⟩) routine92 ∧ planCycles routine92.pieces ≤ rankCost ⟨92, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine92, 86) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready93 : Chain.RoutineReady (embed ⟨93, by decide⟩) routine93 ∧ planCycles routine93.pieces ≤ rankCost ⟨93, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine93, 86) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready94 : Chain.RoutineReady (embed ⟨94, by decide⟩) routine94 ∧ planCycles routine94.pieces ≤ rankCost ⟨94, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine94, 86) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready95 : Chain.RoutineReady (embed ⟨95, by decide⟩) routine95 ∧ planCycles routine95.pieces ≤ rankCost ⟨95, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch11_checked (routine95, 86) (by unfold batch11; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check12 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine96 : ChainRoutine := ⟨96, [0, 1, 0, 4, 0, 2], [⟨201728, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201733, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201737, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨201742, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201744, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201746, [0x13508a3, 0x73], .rung 3 none⟩, ⟨201748, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨201752, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨201757, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201760, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine97 : ChainRoutine := ⟨97, [0, 1, 0, 4, 1, 1], [⟨201792, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201797, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201801, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨201806, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201808, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201810, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201813, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨201818, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨201823, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine98 : ChainRoutine := ⟨98, [0, 1, 0, 4, 2, 0], [⟨201856, [0x1f840513, 0x1e840613, 0xd83f8c93, 0x1953823, 0x73], .head 504 488 1 3⟩, ⟨201861, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨201865, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨201870, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201872, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201874, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨201877, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨201882, [0x13508a3, 0x73], .rung 3 none⟩, ⟨201884, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨201888, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine99 : ChainRoutine := ⟨99, [0, 1, 1, 0, 1, 4], [⟨201920, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨201925, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨201930, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨201934, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨201939, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨201944, [0x7508a3, 0x73], .rung 1 none⟩, ⟨201946, [0xd508a3, 0x73], .rung 2 none⟩, ⟨201948, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨201951, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine100 : ChainRoutine := ⟨100, [0, 1, 1, 0, 2, 3], [⟨201984, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨201989, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨201994, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨201998, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨202003, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨202006, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨202011, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202013, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202016, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine101 : ChainRoutine := ⟨101, [0, 1, 1, 0, 3, 2], [⟨202048, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202053, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨202058, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨202062, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨202067, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202069, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨202072, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨202077, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202080, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine102 : ChainRoutine := ⟨102, [0, 1, 1, 0, 4, 1], [⟨202112, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202117, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨202122, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨202126, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨202131, [0x7508a3, 0x73], .rung 1 none⟩, ⟨202133, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202135, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨202138, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨202143, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine103 : ChainRoutine := ⟨103, [0, 1, 1, 1, 0, 4], [⟨202176, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202181, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202186, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨202191, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨202195, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨202200, [0x7508a3, 0x73], .rung 1 none⟩, ⟨202202, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202204, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202207, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch12 : List (ChainRoutine × Nat) := [(routine96, 86), (routine97, 85), (routine98, 86), (routine99, 85), (routine100, 86), (routine101, 86), (routine102, 85), (routine103, 85)]
theorem batch12_checked : (batch12.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready96 : Chain.RoutineReady (embed ⟨96, by decide⟩) routine96 ∧ planCycles routine96.pieces ≤ rankCost ⟨96, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine96, 86) (by unfold batch12; exact List.mem_cons_self)
theorem ready97 : Chain.RoutineReady (embed ⟨97, by decide⟩) routine97 ∧ planCycles routine97.pieces ≤ rankCost ⟨97, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine97, 85) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready98 : Chain.RoutineReady (embed ⟨98, by decide⟩) routine98 ∧ planCycles routine98.pieces ≤ rankCost ⟨98, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine98, 86) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready99 : Chain.RoutineReady (embed ⟨99, by decide⟩) routine99 ∧ planCycles routine99.pieces ≤ rankCost ⟨99, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine99, 85) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready100 : Chain.RoutineReady (embed ⟨100, by decide⟩) routine100 ∧ planCycles routine100.pieces ≤ rankCost ⟨100, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine100, 86) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready101 : Chain.RoutineReady (embed ⟨101, by decide⟩) routine101 ∧ planCycles routine101.pieces ≤ rankCost ⟨101, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine101, 86) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready102 : Chain.RoutineReady (embed ⟨102, by decide⟩) routine102 ∧ planCycles routine102.pieces ≤ rankCost ⟨102, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine102, 85) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready103 : Chain.RoutineReady (embed ⟨103, by decide⟩) routine103 ∧ planCycles routine103.pieces ≤ rankCost ⟨103, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch12_checked (routine103, 85) (by unfold batch12; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check13 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine104 : ChainRoutine := ⟨104, [0, 1, 1, 1, 1, 3], [⟨202240, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202245, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202250, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨202255, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨202260, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨202265, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202267, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202270, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine105 : ChainRoutine := ⟨106, [0, 1, 1, 1, 3, 1], [⟨202304, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202309, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202314, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨202319, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨202324, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202326, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨202329, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨202334, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine106 : ChainRoutine := ⟨107, [0, 1, 1, 1, 4, 0], [⟨202368, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202373, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202378, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨202383, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨202388, [0x7508a3, 0x73], .rung 1 none⟩, ⟨202390, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202392, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202394, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨202398, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine107 : ChainRoutine := ⟨108, [0, 1, 1, 2, 0, 3], [⟨202432, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202437, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202442, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨202447, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202449, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨202453, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨202458, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202460, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202463, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine108 : ChainRoutine := ⟨111, [0, 1, 1, 2, 3, 0], [⟨202496, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202501, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202506, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨202511, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨202514, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨202519, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202521, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202523, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨202527, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine109 : ChainRoutine := ⟨112, [0, 1, 1, 3, 0, 2], [⟨202560, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202565, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202570, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨202575, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202577, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202579, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨202583, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨202588, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202591, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine110 : ChainRoutine := ⟨113, [0, 1, 1, 3, 1, 1], [⟨202624, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202629, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202634, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨202639, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202641, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨202644, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨202649, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨202654, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine111 : ChainRoutine := ⟨114, [0, 1, 1, 3, 2, 0], [⟨202688, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202693, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202698, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨202703, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202705, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨202708, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨202713, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202715, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨202719, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch13 : List (ChainRoutine × Nat) := [(routine104, 84), (routine105, 84), (routine106, 84), (routine107, 85), (routine108, 85), (routine109, 85), (routine110, 84), (routine111, 85)]
theorem batch13_checked : (batch13.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready104 : Chain.RoutineReady (embed ⟨104, by decide⟩) routine104 ∧ planCycles routine104.pieces ≤ rankCost ⟨104, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine104, 84) (by unfold batch13; exact List.mem_cons_self)
theorem ready105 : Chain.RoutineReady (embed ⟨105, by decide⟩) routine105 ∧ planCycles routine105.pieces ≤ rankCost ⟨105, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine105, 84) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready106 : Chain.RoutineReady (embed ⟨106, by decide⟩) routine106 ∧ planCycles routine106.pieces ≤ rankCost ⟨106, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine106, 84) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready107 : Chain.RoutineReady (embed ⟨107, by decide⟩) routine107 ∧ planCycles routine107.pieces ≤ rankCost ⟨107, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine107, 85) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready108 : Chain.RoutineReady (embed ⟨108, by decide⟩) routine108 ∧ planCycles routine108.pieces ≤ rankCost ⟨108, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine108, 85) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready109 : Chain.RoutineReady (embed ⟨109, by decide⟩) routine109 ∧ planCycles routine109.pieces ≤ rankCost ⟨109, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine109, 85) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready110 : Chain.RoutineReady (embed ⟨110, by decide⟩) routine110 ∧ planCycles routine110.pieces ≤ rankCost ⟨110, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine110, 84) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready111 : Chain.RoutineReady (embed ⟨111, by decide⟩) routine111 ∧ planCycles routine111.pieces ≤ rankCost ⟨111, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch13_checked (routine111, 85) (by unfold batch13; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check14 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine112 : ChainRoutine := ⟨115, [0, 1, 1, 4, 0, 1], [⟨202752, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202757, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202762, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨202767, [0x7508a3, 0x73], .rung 1 none⟩, ⟨202769, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202771, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202773, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨202777, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨202782, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine113 : ChainRoutine := ⟨116, [0, 1, 1, 4, 1, 0], [⟨202816, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202821, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨202826, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨202831, [0x7508a3, 0x73], .rung 1 none⟩, ⟨202833, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202835, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨202838, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨202843, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨202847, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine114 : ChainRoutine := ⟨117, [0, 1, 2, 0, 0, 4], [⟨202880, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202885, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨202890, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202892, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨202896, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨202901, [0x7508a3, 0x73], .rung 1 none⟩, ⟨202903, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202905, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202908, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine115 : ChainRoutine := ⟨118, [0, 1, 2, 0, 1, 3], [⟨202944, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨202949, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨202954, [0x13508a3, 0x73], .rung 3 none⟩, ⟨202956, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨202960, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨202965, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨202970, [0xd508a3, 0x73], .rung 2 none⟩, ⟨202972, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨202975, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine116 : ChainRoutine := ⟨119, [0, 1, 2, 0, 2, 2], [⟨203008, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203013, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203018, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203020, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203024, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨203029, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨203032, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨203037, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨203040, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine117 : ChainRoutine := ⟨120, [0, 1, 2, 0, 3, 1], [⟨203072, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203077, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203082, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203084, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203088, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨203093, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203095, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨203098, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨203103, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine118 : ChainRoutine := ⟨121, [0, 1, 2, 0, 4, 0], [⟨203136, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203141, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203146, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203148, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203152, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨203157, [0x7508a3, 0x73], .rung 1 none⟩, ⟨203159, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203161, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203163, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨203167, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine119 : ChainRoutine := ⟨122, [0, 1, 2, 1, 0, 3], [⟨203200, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203205, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203210, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203213, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨203218, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨203222, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨203227, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203229, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨203232, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch14 : List (ChainRoutine × Nat) := [(routine112, 84), (routine113, 85), (routine114, 82), (routine115, 85), (routine116, 86), (routine117, 85), (routine118, 85), (routine119, 86)]
theorem batch14_checked : (batch14.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready112 : Chain.RoutineReady (embed ⟨112, by decide⟩) routine112 ∧ planCycles routine112.pieces ≤ rankCost ⟨112, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine112, 84) (by unfold batch14; exact List.mem_cons_self)
theorem ready113 : Chain.RoutineReady (embed ⟨113, by decide⟩) routine113 ∧ planCycles routine113.pieces ≤ rankCost ⟨113, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine113, 85) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready114 : Chain.RoutineReady (embed ⟨114, by decide⟩) routine114 ∧ planCycles routine114.pieces ≤ rankCost ⟨114, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine114, 82) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready115 : Chain.RoutineReady (embed ⟨115, by decide⟩) routine115 ∧ planCycles routine115.pieces ≤ rankCost ⟨115, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine115, 85) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready116 : Chain.RoutineReady (embed ⟨116, by decide⟩) routine116 ∧ planCycles routine116.pieces ≤ rankCost ⟨116, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine116, 86) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready117 : Chain.RoutineReady (embed ⟨117, by decide⟩) routine117 ∧ planCycles routine117.pieces ≤ rankCost ⟨117, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine117, 85) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready118 : Chain.RoutineReady (embed ⟨118, by decide⟩) routine118 ∧ planCycles routine118.pieces ≤ rankCost ⟨118, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine118, 85) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready119 : Chain.RoutineReady (embed ⟨119, by decide⟩) routine119 ∧ planCycles routine119.pieces ≤ rankCost ⟨119, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch14_checked (routine119, 86) (by unfold batch14; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check15 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine120 : ChainRoutine := ⟨125, [0, 1, 2, 1, 3, 0], [⟨203264, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203269, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203274, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203277, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨203282, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨203287, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203289, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203291, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨203295, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine121 : ChainRoutine := ⟨126, [0, 1, 2, 2, 0, 2], [⟨203328, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203333, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203338, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203341, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨203346, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203348, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨203352, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨203357, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨203360, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine122 : ChainRoutine := ⟨128, [0, 1, 2, 2, 2, 0], [⟨203392, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203397, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203402, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203405, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨203410, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨203413, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨203418, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203420, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨203424, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine123 : ChainRoutine := ⟨129, [0, 1, 2, 3, 0, 1], [⟨203456, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203461, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203466, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203469, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨203474, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203476, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203478, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨203482, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨203487, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine124 : ChainRoutine := ⟨130, [0, 1, 2, 3, 1, 0], [⟨203520, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203525, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203530, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203533, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨203538, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203540, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨203543, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨203548, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨203552, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine125 : ChainRoutine := ⟨131, [0, 1, 2, 4, 0, 0], [⟨203584, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203589, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨203594, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203597, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨203602, [0x7508a3, 0x73], .rung 1 none⟩, ⟨203604, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203606, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203608, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨203612, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine126 : ChainRoutine := ⟨132, [0, 1, 3, 0, 0, 3], [⟨203648, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203653, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨203658, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203660, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203662, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203666, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨203671, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203673, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨203676, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine127 : ChainRoutine := ⟨133, [0, 1, 3, 0, 1, 2], [⟨203712, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203717, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨203722, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203724, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203726, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203730, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨203735, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨203740, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨203743, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch15 : List (ChainRoutine × Nat) := [(routine120, 85), (routine121, 86), (routine122, 86), (routine123, 85), (routine124, 86), (routine125, 82), (routine126, 82), (routine127, 85)]
theorem batch15_checked : (batch15.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready120 : Chain.RoutineReady (embed ⟨120, by decide⟩) routine120 ∧ planCycles routine120.pieces ≤ rankCost ⟨120, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine120, 85) (by unfold batch15; exact List.mem_cons_self)
theorem ready121 : Chain.RoutineReady (embed ⟨121, by decide⟩) routine121 ∧ planCycles routine121.pieces ≤ rankCost ⟨121, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine121, 86) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready122 : Chain.RoutineReady (embed ⟨122, by decide⟩) routine122 ∧ planCycles routine122.pieces ≤ rankCost ⟨122, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine122, 86) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready123 : Chain.RoutineReady (embed ⟨123, by decide⟩) routine123 ∧ planCycles routine123.pieces ≤ rankCost ⟨123, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine123, 85) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready124 : Chain.RoutineReady (embed ⟨124, by decide⟩) routine124 ∧ planCycles routine124.pieces ≤ rankCost ⟨124, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine124, 86) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready125 : Chain.RoutineReady (embed ⟨125, by decide⟩) routine125 ∧ planCycles routine125.pieces ≤ rankCost ⟨125, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine125, 82) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready126 : Chain.RoutineReady (embed ⟨126, by decide⟩) routine126 ∧ planCycles routine126.pieces ≤ rankCost ⟨126, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine126, 82) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready127 : Chain.RoutineReady (embed ⟨127, by decide⟩) routine127 ∧ planCycles routine127.pieces ≤ rankCost ⟨127, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch15_checked (routine127, 85) (by unfold batch15; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check16 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine128 : ChainRoutine := ⟨134, [0, 1, 3, 0, 2, 1], [⟨203776, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203781, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨203786, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203788, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203790, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203794, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨203799, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨203802, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨203807, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine129 : ChainRoutine := ⟨135, [0, 1, 3, 0, 3, 0], [⟨203840, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203845, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨203850, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203852, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203854, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨203858, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨203863, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203865, [0x13508a3, 0x73], .rung 3 none⟩, ⟨203867, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨203871, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine130 : ChainRoutine := ⟨136, [0, 1, 3, 1, 0, 2], [⟨203904, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203909, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨203914, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203916, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203919, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨203924, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨203928, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨203933, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨203936, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine131 : ChainRoutine := ⟨137, [0, 1, 3, 1, 1, 1], [⟨203968, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨203973, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨203978, [0xd508a3, 0x73], .rung 2 none⟩, ⟨203980, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨203983, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨203988, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨203993, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨203998, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine132 : ChainRoutine := ⟨138, [0, 1, 3, 1, 2, 0], [⟨204032, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204037, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨204042, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204044, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204047, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨204052, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨204057, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204059, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨204063, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine133 : ChainRoutine := ⟨139, [0, 1, 3, 2, 0, 1], [⟨204096, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204101, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨204106, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204108, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204111, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨204116, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204118, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨204122, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨204127, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine134 : ChainRoutine := ⟨140, [0, 1, 3, 2, 1, 0], [⟨204160, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204165, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨204170, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204172, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204175, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨204180, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨204183, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨204188, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨204192, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine135 : ChainRoutine := ⟨141, [0, 1, 3, 3, 0, 0], [⟨204224, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204229, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨204234, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204236, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204239, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨204244, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204246, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204248, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨204252, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch16 : List (ChainRoutine × Nat) := [(routine128, 85), (routine129, 85), (routine130, 86), (routine131, 84), (routine132, 85), (routine133, 85), (routine134, 86), (routine135, 82)]
theorem batch16_checked : (batch16.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready128 : Chain.RoutineReady (embed ⟨128, by decide⟩) routine128 ∧ planCycles routine128.pieces ≤ rankCost ⟨128, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine128, 85) (by unfold batch16; exact List.mem_cons_self)
theorem ready129 : Chain.RoutineReady (embed ⟨129, by decide⟩) routine129 ∧ planCycles routine129.pieces ≤ rankCost ⟨129, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine129, 85) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready130 : Chain.RoutineReady (embed ⟨130, by decide⟩) routine130 ∧ planCycles routine130.pieces ≤ rankCost ⟨130, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine130, 86) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready131 : Chain.RoutineReady (embed ⟨131, by decide⟩) routine131 ∧ planCycles routine131.pieces ≤ rankCost ⟨131, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine131, 84) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready132 : Chain.RoutineReady (embed ⟨132, by decide⟩) routine132 ∧ planCycles routine132.pieces ≤ rankCost ⟨132, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine132, 85) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready133 : Chain.RoutineReady (embed ⟨133, by decide⟩) routine133 ∧ planCycles routine133.pieces ≤ rankCost ⟨133, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine133, 85) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready134 : Chain.RoutineReady (embed ⟨134, by decide⟩) routine134 ∧ planCycles routine134.pieces ≤ rankCost ⟨134, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine134, 86) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready135 : Chain.RoutineReady (embed ⟨135, by decide⟩) routine135 ∧ planCycles routine135.pieces ≤ rankCost ⟨135, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch16_checked (routine135, 82) (by unfold batch16; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check17 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine136 : ChainRoutine := ⟨142, [0, 1, 4, 0, 0, 2], [⟨204288, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204293, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨204298, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204300, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204302, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204304, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨204308, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨204313, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨204316, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine137 : ChainRoutine := ⟨143, [0, 1, 4, 0, 1, 1], [⟨204352, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204357, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨204362, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204364, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204366, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204368, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨204372, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨204377, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨204382, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine138 : ChainRoutine := ⟨144, [0, 1, 4, 0, 2, 0], [⟨204416, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204421, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨204426, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204428, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204430, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204432, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨204436, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨204441, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204443, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨204447, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine139 : ChainRoutine := ⟨145, [0, 1, 4, 1, 0, 1], [⟨204480, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204485, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨204490, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204492, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204494, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204497, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨204502, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨204506, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨204511, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine140 : ChainRoutine := ⟨146, [0, 1, 4, 1, 1, 0], [⟨204544, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204549, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨204554, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204556, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204558, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204561, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨204566, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨204571, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨204575, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine141 : ChainRoutine := ⟨147, [0, 1, 4, 2, 0, 0], [⟨204608, [0x1f840513, 0x2b040613, 0xd83f8c93, 0x1953823, 0x73], .head 504 688 1 3⟩, ⟨204613, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨204618, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204620, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204622, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨204625, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨204630, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204632, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨204636, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine142 : ChainRoutine := ⟨148, [0, 2, 0, 0, 1, 4], [⟨204672, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨204677, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204679, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨204683, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨204688, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨204693, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204695, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204697, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨204700, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine143 : ChainRoutine := ⟨149, [0, 2, 0, 0, 2, 3], [⟨204736, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨204741, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204743, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨204747, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨204752, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨204755, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨204760, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204762, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨204765, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch17 : List (ChainRoutine × Nat) := [(routine136, 82), (routine137, 84), (routine138, 85), (routine139, 85), (routine140, 85), (routine141, 82), (routine142, 82), (routine143, 83)]
theorem batch17_checked : (batch17.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready136 : Chain.RoutineReady (embed ⟨136, by decide⟩) routine136 ∧ planCycles routine136.pieces ≤ rankCost ⟨136, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine136, 82) (by unfold batch17; exact List.mem_cons_self)
theorem ready137 : Chain.RoutineReady (embed ⟨137, by decide⟩) routine137 ∧ planCycles routine137.pieces ≤ rankCost ⟨137, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine137, 84) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready138 : Chain.RoutineReady (embed ⟨138, by decide⟩) routine138 ∧ planCycles routine138.pieces ≤ rankCost ⟨138, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine138, 85) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready139 : Chain.RoutineReady (embed ⟨139, by decide⟩) routine139 ∧ planCycles routine139.pieces ≤ rankCost ⟨139, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine139, 85) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready140 : Chain.RoutineReady (embed ⟨140, by decide⟩) routine140 ∧ planCycles routine140.pieces ≤ rankCost ⟨140, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine140, 85) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready141 : Chain.RoutineReady (embed ⟨141, by decide⟩) routine141 ∧ planCycles routine141.pieces ≤ rankCost ⟨141, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine141, 82) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready142 : Chain.RoutineReady (embed ⟨142, by decide⟩) routine142 ∧ planCycles routine142.pieces ≤ rankCost ⟨142, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine142, 82) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready143 : Chain.RoutineReady (embed ⟨143, by decide⟩) routine143 ∧ planCycles routine143.pieces ≤ rankCost ⟨143, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch17_checked (routine143, 83) (by unfold batch17; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check18 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine144 : ChainRoutine := ⟨150, [0, 2, 0, 0, 3, 2], [⟨204800, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨204805, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204807, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨204811, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨204816, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204818, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨204821, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨204826, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨204829, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine145 : ChainRoutine := ⟨151, [0, 2, 0, 0, 4, 1], [⟨204864, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨204869, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204871, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨204875, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨204880, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204882, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204884, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨204887, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨204892, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine146 : ChainRoutine := ⟨152, [0, 2, 0, 1, 0, 4], [⟨204928, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨204933, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204935, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨204939, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨204944, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨204948, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨204953, [0x7508a3, 0x73], .rung 1 none⟩, ⟨204955, [0xd508a3, 0x73], .rung 2 none⟩, ⟨204957, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨204960, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine147 : ChainRoutine := ⟨153, [0, 2, 0, 1, 1, 3], [⟨204992, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨204997, [0x13508a3, 0x73], .rung 3 none⟩, ⟨204999, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205003, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨205008, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨205013, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨205018, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205020, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205023, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine148 : ChainRoutine := ⟨154, [0, 2, 0, 1, 2, 2], [⟨205056, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205061, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205063, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205067, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨205072, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨205077, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨205080, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨205085, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205088, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine149 : ChainRoutine := ⟨155, [0, 2, 0, 1, 3, 1], [⟨205120, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205125, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205127, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205131, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨205136, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨205141, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205143, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨205146, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨205151, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine150 : ChainRoutine := ⟨156, [0, 2, 0, 1, 4, 0], [⟨205184, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205189, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205191, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205195, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨205200, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨205205, [0x7508a3, 0x73], .rung 1 none⟩, ⟨205207, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205209, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205211, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨205215, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine151 : ChainRoutine := ⟨157, [0, 2, 0, 2, 0, 3], [⟨205248, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205253, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205255, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205259, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨205264, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205266, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨205270, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨205275, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205277, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205280, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch18 : List (ChainRoutine × Nat) := [(routine144, 83), (routine145, 82), (routine146, 86), (routine147, 85), (routine148, 86), (routine149, 85), (routine150, 85), (routine151, 86)]
theorem batch18_checked : (batch18.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready144 : Chain.RoutineReady (embed ⟨144, by decide⟩) routine144 ∧ planCycles routine144.pieces ≤ rankCost ⟨144, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine144, 83) (by unfold batch18; exact List.mem_cons_self)
theorem ready145 : Chain.RoutineReady (embed ⟨145, by decide⟩) routine145 ∧ planCycles routine145.pieces ≤ rankCost ⟨145, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine145, 82) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready146 : Chain.RoutineReady (embed ⟨146, by decide⟩) routine146 ∧ planCycles routine146.pieces ≤ rankCost ⟨146, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine146, 86) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready147 : Chain.RoutineReady (embed ⟨147, by decide⟩) routine147 ∧ planCycles routine147.pieces ≤ rankCost ⟨147, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine147, 85) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready148 : Chain.RoutineReady (embed ⟨148, by decide⟩) routine148 ∧ planCycles routine148.pieces ≤ rankCost ⟨148, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine148, 86) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready149 : Chain.RoutineReady (embed ⟨149, by decide⟩) routine149 ∧ planCycles routine149.pieces ≤ rankCost ⟨149, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine149, 85) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready150 : Chain.RoutineReady (embed ⟨150, by decide⟩) routine150 ∧ planCycles routine150.pieces ≤ rankCost ⟨150, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine150, 85) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready151 : Chain.RoutineReady (embed ⟨151, by decide⟩) routine151 ∧ planCycles routine151.pieces ≤ rankCost ⟨151, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch18_checked (routine151, 86) (by unfold batch18; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check19 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine152 : ChainRoutine := ⟨158, [0, 2, 0, 2, 1, 2], [⟨205312, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205317, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205319, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205323, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨205328, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨205331, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨205336, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨205341, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205344, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine153 : ChainRoutine := ⟨159, [0, 2, 0, 2, 2, 1], [⟨205376, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205381, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205383, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205387, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨205392, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨205395, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨205400, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨205403, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨205408, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine154 : ChainRoutine := ⟨160, [0, 2, 0, 2, 3, 0], [⟨205440, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205445, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205447, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205451, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨205456, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨205459, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨205464, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205466, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205468, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨205472, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine155 : ChainRoutine := ⟨161, [0, 2, 0, 3, 0, 2], [⟨205504, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205509, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205511, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205515, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨205520, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205522, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205524, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨205528, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨205533, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205536, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine156 : ChainRoutine := ⟨162, [0, 2, 0, 3, 1, 1], [⟨205568, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205573, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205575, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205579, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨205584, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205586, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨205589, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨205594, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨205599, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine157 : ChainRoutine := ⟨163, [0, 2, 0, 3, 2, 0], [⟨205632, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205637, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205639, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205643, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨205648, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205650, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨205653, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨205658, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205660, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨205664, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine158 : ChainRoutine := ⟨164, [0, 2, 0, 4, 0, 1], [⟨205696, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205701, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205703, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205707, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨205712, [0x7508a3, 0x73], .rung 1 none⟩, ⟨205714, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205716, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205718, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨205722, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨205727, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine159 : ChainRoutine := ⟨165, [0, 2, 0, 4, 1, 0], [⟨205760, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205765, [0x13508a3, 0x73], .rung 3 none⟩, ⟨205767, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨205771, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨205776, [0x7508a3, 0x73], .rung 1 none⟩, ⟨205778, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205780, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨205783, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨205788, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨205792, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch19 : List (ChainRoutine × Nat) := [(routine152, 86), (routine153, 86), (routine154, 86), (routine155, 86), (routine156, 85), (routine157, 86), (routine158, 85), (routine159, 86)]
theorem batch19_checked : (batch19.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready152 : Chain.RoutineReady (embed ⟨152, by decide⟩) routine152 ∧ planCycles routine152.pieces ≤ rankCost ⟨152, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine152, 86) (by unfold batch19; exact List.mem_cons_self)
theorem ready153 : Chain.RoutineReady (embed ⟨153, by decide⟩) routine153 ∧ planCycles routine153.pieces ≤ rankCost ⟨153, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine153, 86) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready154 : Chain.RoutineReady (embed ⟨154, by decide⟩) routine154 ∧ planCycles routine154.pieces ≤ rankCost ⟨154, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine154, 86) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready155 : Chain.RoutineReady (embed ⟨155, by decide⟩) routine155 ∧ planCycles routine155.pieces ≤ rankCost ⟨155, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine155, 86) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready156 : Chain.RoutineReady (embed ⟨156, by decide⟩) routine156 ∧ planCycles routine156.pieces ≤ rankCost ⟨156, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine156, 85) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready157 : Chain.RoutineReady (embed ⟨157, by decide⟩) routine157 ∧ planCycles routine157.pieces ≤ rankCost ⟨157, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine157, 86) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready158 : Chain.RoutineReady (embed ⟨158, by decide⟩) routine158 ∧ planCycles routine158.pieces ≤ rankCost ⟨158, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine158, 85) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready159 : Chain.RoutineReady (embed ⟨159, by decide⟩) routine159 ∧ planCycles routine159.pieces ≤ rankCost ⟨159, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch19_checked (routine159, 86) (by unfold batch19; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check20 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine160 : ChainRoutine := ⟨166, [0, 2, 1, 0, 0, 4], [⟨205824, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205829, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨205832, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨205837, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨205841, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨205846, [0x7508a3, 0x73], .rung 1 none⟩, ⟨205848, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205850, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205853, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine161 : ChainRoutine := ⟨167, [0, 2, 1, 0, 1, 3], [⟨205888, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205893, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨205896, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨205901, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨205905, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨205910, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨205915, [0xd508a3, 0x73], .rung 2 none⟩, ⟨205917, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205920, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine162 : ChainRoutine := ⟨168, [0, 2, 1, 0, 2, 2], [⟨205952, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨205957, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨205960, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨205965, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨205969, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨205974, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨205977, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨205982, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨205985, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine163 : ChainRoutine := ⟨169, [0, 2, 1, 0, 3, 1], [⟨206016, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206021, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206024, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨206029, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨206033, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨206038, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206040, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨206043, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨206048, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine164 : ChainRoutine := ⟨170, [0, 2, 1, 0, 4, 0], [⟨206080, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206085, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206088, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨206093, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨206097, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨206102, [0x7508a3, 0x73], .rung 1 none⟩, ⟨206104, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206106, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206108, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨206112, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine165 : ChainRoutine := ⟨171, [0, 2, 1, 1, 0, 3], [⟨206144, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206149, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206152, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206157, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨206162, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨206166, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨206171, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206173, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨206176, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine166 : ChainRoutine := ⟨174, [0, 2, 1, 1, 3, 0], [⟨206208, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206213, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206216, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206221, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨206226, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨206231, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206233, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206235, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨206239, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine167 : ChainRoutine := ⟨175, [0, 2, 1, 2, 0, 2], [⟨206272, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206277, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206280, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206285, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨206290, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206292, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨206296, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨206301, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨206304, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch20 : List (ChainRoutine × Nat) := [(routine160, 83), (routine161, 86), (routine162, 87), (routine163, 86), (routine164, 86), (routine165, 86), (routine166, 85), (routine167, 86)]
theorem batch20_checked : (batch20.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready160 : Chain.RoutineReady (embed ⟨160, by decide⟩) routine160 ∧ planCycles routine160.pieces ≤ rankCost ⟨160, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine160, 83) (by unfold batch20; exact List.mem_cons_self)
theorem ready161 : Chain.RoutineReady (embed ⟨161, by decide⟩) routine161 ∧ planCycles routine161.pieces ≤ rankCost ⟨161, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine161, 86) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready162 : Chain.RoutineReady (embed ⟨162, by decide⟩) routine162 ∧ planCycles routine162.pieces ≤ rankCost ⟨162, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine162, 87) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready163 : Chain.RoutineReady (embed ⟨163, by decide⟩) routine163 ∧ planCycles routine163.pieces ≤ rankCost ⟨163, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine163, 86) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready164 : Chain.RoutineReady (embed ⟨164, by decide⟩) routine164 ∧ planCycles routine164.pieces ≤ rankCost ⟨164, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine164, 86) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready165 : Chain.RoutineReady (embed ⟨165, by decide⟩) routine165 ∧ planCycles routine165.pieces ≤ rankCost ⟨165, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine165, 86) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready166 : Chain.RoutineReady (embed ⟨166, by decide⟩) routine166 ∧ planCycles routine166.pieces ≤ rankCost ⟨166, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine166, 85) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready167 : Chain.RoutineReady (embed ⟨167, by decide⟩) routine167 ∧ planCycles routine167.pieces ≤ rankCost ⟨167, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch20_checked (routine167, 86) (by unfold batch20; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check21 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine168 : ChainRoutine := ⟨177, [0, 2, 1, 2, 2, 0], [⟨206336, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206341, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206344, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206349, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨206354, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨206357, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨206362, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206364, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨206368, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine169 : ChainRoutine := ⟨178, [0, 2, 1, 3, 0, 1], [⟨206400, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206405, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206408, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206413, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨206418, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206420, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206422, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨206426, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨206431, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine170 : ChainRoutine := ⟨179, [0, 2, 1, 3, 1, 0], [⟨206464, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206469, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206472, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206477, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨206482, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206484, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨206487, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨206492, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨206496, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine171 : ChainRoutine := ⟨180, [0, 2, 1, 4, 0, 0], [⟨206528, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206533, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206536, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨206541, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨206546, [0x7508a3, 0x73], .rung 1 none⟩, ⟨206548, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206550, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206552, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨206556, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine172 : ChainRoutine := ⟨181, [0, 2, 2, 0, 0, 3], [⟨206592, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206597, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206600, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206605, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206607, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨206611, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨206616, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206618, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨206621, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine173 : ChainRoutine := ⟨182, [0, 2, 2, 0, 1, 2], [⟨206656, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206661, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206664, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206669, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206671, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨206675, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨206680, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨206685, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨206688, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine174 : ChainRoutine := ⟨183, [0, 2, 2, 0, 2, 1], [⟨206720, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206725, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206728, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206733, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206735, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨206739, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨206744, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨206747, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨206752, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine175 : ChainRoutine := ⟨184, [0, 2, 2, 0, 3, 0], [⟨206784, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206789, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206792, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206797, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206799, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨206803, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨206808, [0xd508a3, 0x73], .rung 2 none⟩, ⟨206810, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206812, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨206816, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch21 : List (ChainRoutine × Nat) := [(routine168, 86), (routine169, 85), (routine170, 86), (routine171, 82), (routine172, 83), (routine173, 86), (routine174, 86), (routine175, 86)]
theorem batch21_checked : (batch21.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready168 : Chain.RoutineReady (embed ⟨168, by decide⟩) routine168 ∧ planCycles routine168.pieces ≤ rankCost ⟨168, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine168, 86) (by unfold batch21; exact List.mem_cons_self)
theorem ready169 : Chain.RoutineReady (embed ⟨169, by decide⟩) routine169 ∧ planCycles routine169.pieces ≤ rankCost ⟨169, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine169, 85) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready170 : Chain.RoutineReady (embed ⟨170, by decide⟩) routine170 ∧ planCycles routine170.pieces ≤ rankCost ⟨170, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine170, 86) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready171 : Chain.RoutineReady (embed ⟨171, by decide⟩) routine171 ∧ planCycles routine171.pieces ≤ rankCost ⟨171, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine171, 82) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready172 : Chain.RoutineReady (embed ⟨172, by decide⟩) routine172 ∧ planCycles routine172.pieces ≤ rankCost ⟨172, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine172, 83) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready173 : Chain.RoutineReady (embed ⟨173, by decide⟩) routine173 ∧ planCycles routine173.pieces ≤ rankCost ⟨173, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine173, 86) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready174 : Chain.RoutineReady (embed ⟨174, by decide⟩) routine174 ∧ planCycles routine174.pieces ≤ rankCost ⟨174, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine174, 86) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready175 : Chain.RoutineReady (embed ⟨175, by decide⟩) routine175 ∧ planCycles routine175.pieces ≤ rankCost ⟨175, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch21_checked (routine175, 86) (by unfold batch21; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check22 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine176 : ChainRoutine := ⟨185, [0, 2, 2, 1, 0, 2], [⟨206848, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206853, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206856, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206861, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨206864, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨206869, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨206873, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨206878, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨206881, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine177 : ChainRoutine := ⟨187, [0, 2, 2, 1, 2, 0], [⟨206912, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206917, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206920, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206925, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨206928, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨206933, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨206938, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206940, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨206944, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine178 : ChainRoutine := ⟨188, [0, 2, 2, 2, 0, 1], [⟨206976, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨206981, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨206984, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨206989, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨206992, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨206997, [0x13508a3, 0x73], .rung 3 none⟩, ⟨206999, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨207003, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨207008, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine179 : ChainRoutine := ⟨189, [0, 2, 2, 2, 1, 0], [⟨207040, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207045, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207048, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨207053, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨207056, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨207061, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨207064, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨207069, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨207073, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine180 : ChainRoutine := ⟨190, [0, 2, 2, 3, 0, 0], [⟨207104, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207109, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207112, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨207117, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨207120, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨207125, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207127, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207129, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨207133, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine181 : ChainRoutine := ⟨191, [0, 2, 3, 0, 0, 2], [⟨207168, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207173, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207176, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨207181, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207183, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207185, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨207189, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨207194, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨207197, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine182 : ChainRoutine := ⟨192, [0, 2, 3, 0, 1, 1], [⟨207232, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207237, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207240, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨207245, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207247, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207249, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨207253, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨207258, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨207263, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine183 : ChainRoutine := ⟨193, [0, 2, 3, 0, 2, 0], [⟨207296, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207301, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207304, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨207309, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207311, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207313, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨207317, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨207322, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207324, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨207328, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch22 : List (ChainRoutine × Nat) := [(routine176, 87), (routine177, 86), (routine178, 86), (routine179, 87), (routine180, 83), (routine181, 83), (routine182, 85), (routine183, 86)]
theorem batch22_checked : (batch22.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready176 : Chain.RoutineReady (embed ⟨176, by decide⟩) routine176 ∧ planCycles routine176.pieces ≤ rankCost ⟨176, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine176, 87) (by unfold batch22; exact List.mem_cons_self)
theorem ready177 : Chain.RoutineReady (embed ⟨177, by decide⟩) routine177 ∧ planCycles routine177.pieces ≤ rankCost ⟨177, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine177, 86) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready178 : Chain.RoutineReady (embed ⟨178, by decide⟩) routine178 ∧ planCycles routine178.pieces ≤ rankCost ⟨178, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine178, 86) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready179 : Chain.RoutineReady (embed ⟨179, by decide⟩) routine179 ∧ planCycles routine179.pieces ≤ rankCost ⟨179, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine179, 87) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready180 : Chain.RoutineReady (embed ⟨180, by decide⟩) routine180 ∧ planCycles routine180.pieces ≤ rankCost ⟨180, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine180, 83) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready181 : Chain.RoutineReady (embed ⟨181, by decide⟩) routine181 ∧ planCycles routine181.pieces ≤ rankCost ⟨181, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine181, 83) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready182 : Chain.RoutineReady (embed ⟨182, by decide⟩) routine182 ∧ planCycles routine182.pieces ≤ rankCost ⟨182, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine182, 85) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready183 : Chain.RoutineReady (embed ⟨183, by decide⟩) routine183 ∧ planCycles routine183.pieces ≤ rankCost ⟨183, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch22_checked (routine183, 86) (by unfold batch22; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check23 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine184 : ChainRoutine := ⟨194, [0, 2, 3, 1, 0, 1], [⟨207360, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207365, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207368, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨207373, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207375, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨207378, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨207383, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨207387, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨207392, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine185 : ChainRoutine := ⟨195, [0, 2, 3, 1, 1, 0], [⟨207424, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207429, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207432, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨207437, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207439, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨207442, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨207447, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨207452, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨207456, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine186 : ChainRoutine := ⟨196, [0, 2, 3, 2, 0, 0], [⟨207488, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207493, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207496, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨207501, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207503, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨207506, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨207511, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207513, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨207517, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine187 : ChainRoutine := ⟨197, [0, 2, 4, 0, 0, 1], [⟨207552, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207557, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207560, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨207565, [0x7508a3, 0x73], .rung 1 none⟩, ⟨207567, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207569, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207571, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨207575, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨207580, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine188 : ChainRoutine := ⟨198, [0, 2, 4, 0, 1, 0], [⟨207616, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207621, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207624, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨207629, [0x7508a3, 0x73], .rung 1 none⟩, ⟨207631, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207633, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207635, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨207639, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨207644, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨207648, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine189 : ChainRoutine := ⟨199, [0, 2, 4, 1, 0, 0], [⟨207680, [0x1f840513, 0x1e840613, 0xc83f8c93, 0x1953823, 0x73], .head 504 488 1 2⟩, ⟨207685, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨207688, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨207693, [0x7508a3, 0x73], .rung 1 none⟩, ⟨207695, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207697, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨207700, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨207705, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨207709, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine190 : ChainRoutine := ⟨200, [0, 3, 0, 0, 0, 4], [⟨207744, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨207749, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207751, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207753, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨207757, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨207762, [0x7508a3, 0x73], .rung 1 none⟩, ⟨207764, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207766, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨207769, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine191 : ChainRoutine := ⟨201, [0, 3, 0, 0, 1, 3], [⟨207808, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨207813, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207815, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207817, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨207821, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨207826, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨207831, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207833, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨207836, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch23 : List (ChainRoutine × Nat) := [(routine184, 86), (routine185, 86), (routine186, 83), (routine187, 82), (routine188, 86), (routine189, 83), (routine190, 79), (routine191, 82)]
theorem batch23_checked : (batch23.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready184 : Chain.RoutineReady (embed ⟨184, by decide⟩) routine184 ∧ planCycles routine184.pieces ≤ rankCost ⟨184, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine184, 86) (by unfold batch23; exact List.mem_cons_self)
theorem ready185 : Chain.RoutineReady (embed ⟨185, by decide⟩) routine185 ∧ planCycles routine185.pieces ≤ rankCost ⟨185, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine185, 86) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready186 : Chain.RoutineReady (embed ⟨186, by decide⟩) routine186 ∧ planCycles routine186.pieces ≤ rankCost ⟨186, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine186, 83) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready187 : Chain.RoutineReady (embed ⟨187, by decide⟩) routine187 ∧ planCycles routine187.pieces ≤ rankCost ⟨187, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine187, 82) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready188 : Chain.RoutineReady (embed ⟨188, by decide⟩) routine188 ∧ planCycles routine188.pieces ≤ rankCost ⟨188, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine188, 86) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready189 : Chain.RoutineReady (embed ⟨189, by decide⟩) routine189 ∧ planCycles routine189.pieces ≤ rankCost ⟨189, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine189, 83) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready190 : Chain.RoutineReady (embed ⟨190, by decide⟩) routine190 ∧ planCycles routine190.pieces ≤ rankCost ⟨190, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine190, 79) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready191 : Chain.RoutineReady (embed ⟨191, by decide⟩) routine191 ∧ planCycles routine191.pieces ≤ rankCost ⟨191, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch23_checked (routine191, 82) (by unfold batch23; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check24 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine192 : ChainRoutine := ⟨202, [0, 3, 0, 0, 2, 2], [⟨207872, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨207877, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207879, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207881, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨207885, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨207890, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨207893, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨207898, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨207901, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine193 : ChainRoutine := ⟨203, [0, 3, 0, 0, 3, 1], [⟨207936, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨207941, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207943, [0x13508a3, 0x73], .rung 3 none⟩, ⟨207945, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨207949, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨207954, [0xd508a3, 0x73], .rung 2 none⟩, ⟨207956, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨207959, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨207964, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine194 : ChainRoutine := ⟨204, [0, 3, 0, 0, 4, 0], [⟨208000, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208005, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208007, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208009, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208013, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨208018, [0x7508a3, 0x73], .rung 1 none⟩, ⟨208020, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208022, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208024, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨208028, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine195 : ChainRoutine := ⟨205, [0, 3, 0, 1, 0, 3], [⟨208064, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208069, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208071, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208073, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208077, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨208082, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨208086, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨208091, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208093, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨208096, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine196 : ChainRoutine := ⟨206, [0, 3, 0, 1, 1, 2], [⟨208128, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208133, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208135, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208137, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208141, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨208146, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨208151, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨208156, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨208159, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine197 : ChainRoutine := ⟨207, [0, 3, 0, 1, 2, 1], [⟨208192, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208197, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208199, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208201, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208205, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨208210, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨208215, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨208218, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨208223, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine198 : ChainRoutine := ⟨208, [0, 3, 0, 1, 3, 0], [⟨208256, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208261, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208263, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208265, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208269, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨208274, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨208279, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208281, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208283, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨208287, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine199 : ChainRoutine := ⟨209, [0, 3, 0, 2, 0, 2], [⟨208320, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208325, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208327, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208329, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208333, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨208338, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208340, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨208344, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨208349, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨208352, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch24 : List (ChainRoutine × Nat) := [(routine192, 83), (routine193, 82), (routine194, 82), (routine195, 86), (routine196, 85), (routine197, 85), (routine198, 85), (routine199, 86)]
theorem batch24_checked : (batch24.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready192 : Chain.RoutineReady (embed ⟨192, by decide⟩) routine192 ∧ planCycles routine192.pieces ≤ rankCost ⟨192, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine192, 83) (by unfold batch24; exact List.mem_cons_self)
theorem ready193 : Chain.RoutineReady (embed ⟨193, by decide⟩) routine193 ∧ planCycles routine193.pieces ≤ rankCost ⟨193, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine193, 82) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready194 : Chain.RoutineReady (embed ⟨194, by decide⟩) routine194 ∧ planCycles routine194.pieces ≤ rankCost ⟨194, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine194, 82) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready195 : Chain.RoutineReady (embed ⟨195, by decide⟩) routine195 ∧ planCycles routine195.pieces ≤ rankCost ⟨195, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine195, 86) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready196 : Chain.RoutineReady (embed ⟨196, by decide⟩) routine196 ∧ planCycles routine196.pieces ≤ rankCost ⟨196, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine196, 85) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready197 : Chain.RoutineReady (embed ⟨197, by decide⟩) routine197 ∧ planCycles routine197.pieces ≤ rankCost ⟨197, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine197, 85) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready198 : Chain.RoutineReady (embed ⟨198, by decide⟩) routine198 ∧ planCycles routine198.pieces ≤ rankCost ⟨198, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine198, 85) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready199 : Chain.RoutineReady (embed ⟨199, by decide⟩) routine199 ∧ planCycles routine199.pieces ≤ rankCost ⟨199, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch24_checked (routine199, 86) (by unfold batch24; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check25 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine200 : ChainRoutine := ⟨210, [0, 3, 0, 2, 1, 1], [⟨208384, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208389, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208391, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208393, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208397, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨208402, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨208405, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨208410, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨208415, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine201 : ChainRoutine := ⟨211, [0, 3, 0, 2, 2, 0], [⟨208448, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208453, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208455, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208457, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208461, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨208466, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨208469, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨208474, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208476, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨208480, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine202 : ChainRoutine := ⟨212, [0, 3, 0, 3, 0, 1], [⟨208512, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208517, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208519, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208521, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208525, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨208530, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208532, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208534, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨208538, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨208543, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine203 : ChainRoutine := ⟨213, [0, 3, 0, 3, 1, 0], [⟨208576, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208581, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208583, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208585, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208589, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨208594, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208596, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨208599, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨208604, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨208608, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine204 : ChainRoutine := ⟨214, [0, 3, 0, 4, 0, 0], [⟨208640, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208645, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208647, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208649, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨208653, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨208658, [0x7508a3, 0x73], .rung 1 none⟩, ⟨208660, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208662, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208664, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨208668, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine205 : ChainRoutine := ⟨215, [0, 3, 1, 0, 0, 3], [⟨208704, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208709, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208711, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨208714, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨208719, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨208723, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨208728, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208730, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨208733, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine206 : ChainRoutine := ⟨216, [0, 3, 1, 0, 1, 2], [⟨208768, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208773, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208775, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨208778, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨208783, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨208787, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨208792, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨208797, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨208800, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine207 : ChainRoutine := ⟨217, [0, 3, 1, 0, 2, 1], [⟨208832, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208837, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208839, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨208842, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨208847, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨208851, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨208856, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨208859, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨208864, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch25 : List (ChainRoutine × Nat) := [(routine200, 85), (routine201, 86), (routine202, 85), (routine203, 86), (routine204, 82), (routine205, 83), (routine206, 86), (routine207, 86)]
theorem batch25_checked : (batch25.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready200 : Chain.RoutineReady (embed ⟨200, by decide⟩) routine200 ∧ planCycles routine200.pieces ≤ rankCost ⟨200, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine200, 85) (by unfold batch25; exact List.mem_cons_self)
theorem ready201 : Chain.RoutineReady (embed ⟨201, by decide⟩) routine201 ∧ planCycles routine201.pieces ≤ rankCost ⟨201, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine201, 86) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready202 : Chain.RoutineReady (embed ⟨202, by decide⟩) routine202 ∧ planCycles routine202.pieces ≤ rankCost ⟨202, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine202, 85) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready203 : Chain.RoutineReady (embed ⟨203, by decide⟩) routine203 ∧ planCycles routine203.pieces ≤ rankCost ⟨203, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine203, 86) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready204 : Chain.RoutineReady (embed ⟨204, by decide⟩) routine204 ∧ planCycles routine204.pieces ≤ rankCost ⟨204, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine204, 82) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready205 : Chain.RoutineReady (embed ⟨205, by decide⟩) routine205 ∧ planCycles routine205.pieces ≤ rankCost ⟨205, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine205, 83) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready206 : Chain.RoutineReady (embed ⟨206, by decide⟩) routine206 ∧ planCycles routine206.pieces ≤ rankCost ⟨206, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine206, 86) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready207 : Chain.RoutineReady (embed ⟨207, by decide⟩) routine207 ∧ planCycles routine207.pieces ≤ rankCost ⟨207, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch25_checked (routine207, 86) (by unfold batch25; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check26 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine208 : ChainRoutine := ⟨218, [0, 3, 1, 0, 3, 0], [⟨208896, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208901, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208903, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨208906, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨208911, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨208915, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨208920, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208922, [0x13508a3, 0x73], .rung 3 none⟩, ⟨208924, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨208928, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine209 : ChainRoutine := ⟨219, [0, 3, 1, 1, 0, 2], [⟨208960, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨208965, [0xd508a3, 0x73], .rung 2 none⟩, ⟨208967, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨208970, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨208975, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨208980, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨208984, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨208989, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨208992, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine210 : ChainRoutine := ⟨220, [0, 3, 1, 1, 1, 1], [⟨209024, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209029, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209031, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209034, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨209039, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨209044, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨209049, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨209054, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine211 : ChainRoutine := ⟨221, [0, 3, 1, 1, 2, 0], [⟨209088, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209093, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209095, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209098, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨209103, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨209108, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨209113, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209115, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨209119, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine212 : ChainRoutine := ⟨222, [0, 3, 1, 2, 0, 1], [⟨209152, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209157, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209159, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209162, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨209167, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨209172, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209174, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨209178, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨209183, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine213 : ChainRoutine := ⟨223, [0, 3, 1, 2, 1, 0], [⟨209216, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209221, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209223, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209226, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨209231, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨209236, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨209239, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨209244, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨209248, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine214 : ChainRoutine := ⟨224, [0, 3, 1, 3, 0, 0], [⟨209280, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209285, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209287, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209290, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨209295, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨209300, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209302, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209304, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨209308, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine215 : ChainRoutine := ⟨225, [0, 3, 2, 0, 0, 2], [⟨209344, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209349, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209351, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209354, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨209359, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209361, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨209365, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨209370, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨209373, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch26 : List (ChainRoutine × Nat) := [(routine208, 86), (routine209, 86), (routine210, 84), (routine211, 85), (routine212, 85), (routine213, 86), (routine214, 82), (routine215, 83)]
theorem batch26_checked : (batch26.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready208 : Chain.RoutineReady (embed ⟨208, by decide⟩) routine208 ∧ planCycles routine208.pieces ≤ rankCost ⟨208, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine208, 86) (by unfold batch26; exact List.mem_cons_self)
theorem ready209 : Chain.RoutineReady (embed ⟨209, by decide⟩) routine209 ∧ planCycles routine209.pieces ≤ rankCost ⟨209, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine209, 86) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready210 : Chain.RoutineReady (embed ⟨210, by decide⟩) routine210 ∧ planCycles routine210.pieces ≤ rankCost ⟨210, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine210, 84) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready211 : Chain.RoutineReady (embed ⟨211, by decide⟩) routine211 ∧ planCycles routine211.pieces ≤ rankCost ⟨211, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine211, 85) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready212 : Chain.RoutineReady (embed ⟨212, by decide⟩) routine212 ∧ planCycles routine212.pieces ≤ rankCost ⟨212, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine212, 85) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready213 : Chain.RoutineReady (embed ⟨213, by decide⟩) routine213 ∧ planCycles routine213.pieces ≤ rankCost ⟨213, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine213, 86) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready214 : Chain.RoutineReady (embed ⟨214, by decide⟩) routine214 ∧ planCycles routine214.pieces ≤ rankCost ⟨214, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine214, 82) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready215 : Chain.RoutineReady (embed ⟨215, by decide⟩) routine215 ∧ planCycles routine215.pieces ≤ rankCost ⟨215, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch26_checked (routine215, 83) (by unfold batch26; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check27 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine216 : ChainRoutine := ⟨226, [0, 3, 2, 0, 1, 1], [⟨209408, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209413, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209415, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209418, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨209423, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209425, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨209429, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨209434, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨209439, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine217 : ChainRoutine := ⟨227, [0, 3, 2, 0, 2, 0], [⟨209472, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209477, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209479, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209482, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨209487, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209489, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨209493, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨209498, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209500, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨209504, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine218 : ChainRoutine := ⟨228, [0, 3, 2, 1, 0, 1], [⟨209536, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209541, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209543, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209546, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨209551, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨209554, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨209559, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨209563, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨209568, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine219 : ChainRoutine := ⟨229, [0, 3, 2, 1, 1, 0], [⟨209600, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209605, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209607, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209610, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨209615, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨209618, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨209623, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨209628, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨209632, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine220 : ChainRoutine := ⟨230, [0, 3, 2, 2, 0, 0], [⟨209664, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209669, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209671, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209674, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨209679, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨209682, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨209687, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209689, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨209693, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine221 : ChainRoutine := ⟨231, [0, 3, 3, 0, 0, 1], [⟨209728, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209733, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209735, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209738, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨209743, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209745, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209747, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨209751, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨209756, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine222 : ChainRoutine := ⟨232, [0, 3, 3, 0, 1, 0], [⟨209792, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209797, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209799, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209802, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨209807, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209809, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209811, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨209815, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨209820, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨209824, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine223 : ChainRoutine := ⟨233, [0, 3, 3, 1, 0, 0], [⟨209856, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209861, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209863, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209866, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨209871, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209873, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨209876, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨209881, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨209885, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch27 : List (ChainRoutine × Nat) := [(routine216, 85), (routine217, 86), (routine218, 86), (routine219, 86), (routine220, 83), (routine221, 82), (routine222, 86), (routine223, 83)]
theorem batch27_checked : (batch27.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready216 : Chain.RoutineReady (embed ⟨216, by decide⟩) routine216 ∧ planCycles routine216.pieces ≤ rankCost ⟨216, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine216, 85) (by unfold batch27; exact List.mem_cons_self)
theorem ready217 : Chain.RoutineReady (embed ⟨217, by decide⟩) routine217 ∧ planCycles routine217.pieces ≤ rankCost ⟨217, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine217, 86) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready218 : Chain.RoutineReady (embed ⟨218, by decide⟩) routine218 ∧ planCycles routine218.pieces ≤ rankCost ⟨218, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine218, 86) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready219 : Chain.RoutineReady (embed ⟨219, by decide⟩) routine219 ∧ planCycles routine219.pieces ≤ rankCost ⟨219, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine219, 86) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready220 : Chain.RoutineReady (embed ⟨220, by decide⟩) routine220 ∧ planCycles routine220.pieces ≤ rankCost ⟨220, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine220, 83) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready221 : Chain.RoutineReady (embed ⟨221, by decide⟩) routine221 ∧ planCycles routine221.pieces ≤ rankCost ⟨221, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine221, 82) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready222 : Chain.RoutineReady (embed ⟨222, by decide⟩) routine222 ∧ planCycles routine222.pieces ≤ rankCost ⟨222, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine222, 86) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready223 : Chain.RoutineReady (embed ⟨223, by decide⟩) routine223 ∧ planCycles routine223.pieces ≤ rankCost ⟨223, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch27_checked (routine223, 83) (by unfold batch27; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check28 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine224 : ChainRoutine := ⟨234, [0, 3, 4, 0, 0, 0], [⟨209920, [0x1f840513, 0x1e840613, 0xb83f8c93, 0x1953823, 0x73], .head 504 488 1 1⟩, ⟨209925, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209927, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨209930, [0x21040513, 0x24040613, 0xa87f8c93, 0x1953823, 0x73], .head 528 576 2 0⟩, ⟨209935, [0x7508a3, 0x73], .rung 1 none⟩, ⟨209937, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209939, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209941, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨209945, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine225 : ChainRoutine := ⟨235, [0, 4, 0, 0, 0, 3], [⟨209984, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨209989, [0x7508a3, 0x73], .rung 1 none⟩, ⟨209991, [0xd508a3, 0x73], .rung 2 none⟩, ⟨209993, [0x13508a3, 0x73], .rung 3 none⟩, ⟨209995, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨209999, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨210004, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210006, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨210009, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine226 : ChainRoutine := ⟨236, [0, 4, 0, 0, 1, 2], [⟨210048, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210053, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210055, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210057, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210059, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210063, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨210068, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨210073, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨210076, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine227 : ChainRoutine := ⟨237, [0, 4, 0, 0, 2, 1], [⟨210112, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210117, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210119, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210121, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210123, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210127, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨210132, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨210135, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨210140, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine228 : ChainRoutine := ⟨238, [0, 4, 0, 0, 3, 0], [⟨210176, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210181, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210183, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210185, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210187, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210191, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨210196, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210198, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210200, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨210204, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine229 : ChainRoutine := ⟨239, [0, 4, 0, 1, 0, 2], [⟨210240, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210245, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210247, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210249, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210251, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210255, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨210260, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨210264, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨210269, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨210272, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine230 : ChainRoutine := ⟨240, [0, 4, 0, 1, 1, 1], [⟨210304, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210309, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210311, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210313, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210315, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210319, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨210324, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨210329, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨210334, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine231 : ChainRoutine := ⟨241, [0, 4, 0, 1, 2, 0], [⟨210368, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210373, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210375, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210377, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210379, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210383, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨210388, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨210393, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210395, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨210399, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch28 : List (ChainRoutine × Nat) := [(routine224, 79), (routine225, 79), (routine226, 82), (routine227, 82), (routine228, 82), (routine229, 86), (routine230, 84), (routine231, 85)]
theorem batch28_checked : (batch28.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready224 : Chain.RoutineReady (embed ⟨224, by decide⟩) routine224 ∧ planCycles routine224.pieces ≤ rankCost ⟨224, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine224, 79) (by unfold batch28; exact List.mem_cons_self)
theorem ready225 : Chain.RoutineReady (embed ⟨225, by decide⟩) routine225 ∧ planCycles routine225.pieces ≤ rankCost ⟨225, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine225, 79) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready226 : Chain.RoutineReady (embed ⟨226, by decide⟩) routine226 ∧ planCycles routine226.pieces ≤ rankCost ⟨226, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine226, 82) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready227 : Chain.RoutineReady (embed ⟨227, by decide⟩) routine227 ∧ planCycles routine227.pieces ≤ rankCost ⟨227, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine227, 82) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready228 : Chain.RoutineReady (embed ⟨228, by decide⟩) routine228 ∧ planCycles routine228.pieces ≤ rankCost ⟨228, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine228, 82) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready229 : Chain.RoutineReady (embed ⟨229, by decide⟩) routine229 ∧ planCycles routine229.pieces ≤ rankCost ⟨229, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine229, 86) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready230 : Chain.RoutineReady (embed ⟨230, by decide⟩) routine230 ∧ planCycles routine230.pieces ≤ rankCost ⟨230, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine230, 84) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready231 : Chain.RoutineReady (embed ⟨231, by decide⟩) routine231 ∧ planCycles routine231.pieces ≤ rankCost ⟨231, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch28_checked (routine231, 85) (by unfold batch28; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check29 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine232 : ChainRoutine := ⟨242, [0, 4, 0, 2, 0, 1], [⟨210432, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210437, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210439, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210441, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210443, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210447, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨210452, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210454, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨210458, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨210463, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine233 : ChainRoutine := ⟨243, [0, 4, 0, 2, 1, 0], [⟨210496, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210501, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210503, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210505, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210507, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210511, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨210516, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨210519, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨210524, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨210528, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine234 : ChainRoutine := ⟨244, [0, 4, 0, 3, 0, 0], [⟨210560, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210565, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210567, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210569, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210571, [0x1e843183, 0x1f043703, 0x2a343823, 0x2ae43c23], .copy 440 688⟩, ⟨210575, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨210580, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210582, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210584, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨210588, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine235 : ChainRoutine := ⟨245, [0, 4, 1, 0, 0, 2], [⟨210624, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210629, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210631, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210633, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨210636, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨210641, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨210645, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨210650, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨210653, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine236 : ChainRoutine := ⟨246, [0, 4, 1, 0, 1, 1], [⟨210688, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210693, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210695, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210697, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨210700, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨210705, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨210709, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨210714, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨210719, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine237 : ChainRoutine := ⟨247, [0, 4, 1, 0, 2, 0], [⟨210752, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210757, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210759, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210761, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨210764, [0x21040513, 0x24040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 576 2 3⟩, ⟨210769, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨210773, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨210778, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210780, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨210784, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine238 : ChainRoutine := ⟨248, [0, 4, 1, 1, 0, 1], [⟨210816, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210821, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210823, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210825, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨210828, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨210833, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨210838, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨210842, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨210847, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine239 : ChainRoutine := ⟨249, [0, 4, 1, 1, 1, 0], [⟨210880, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210885, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210887, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210889, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨210892, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨210897, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨210902, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨210907, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨210911, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch29 : List (ChainRoutine × Nat) := [(routine232, 85), (routine233, 86), (routine234, 82), (routine235, 83), (routine236, 85), (routine237, 86), (routine238, 85), (routine239, 85)]
theorem batch29_checked : (batch29.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready232 : Chain.RoutineReady (embed ⟨232, by decide⟩) routine232 ∧ planCycles routine232.pieces ≤ rankCost ⟨232, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine232, 85) (by unfold batch29; exact List.mem_cons_self)
theorem ready233 : Chain.RoutineReady (embed ⟨233, by decide⟩) routine233 ∧ planCycles routine233.pieces ≤ rankCost ⟨233, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine233, 86) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready234 : Chain.RoutineReady (embed ⟨234, by decide⟩) routine234 ∧ planCycles routine234.pieces ≤ rankCost ⟨234, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine234, 82) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready235 : Chain.RoutineReady (embed ⟨235, by decide⟩) routine235 ∧ planCycles routine235.pieces ≤ rankCost ⟨235, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine235, 83) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready236 : Chain.RoutineReady (embed ⟨236, by decide⟩) routine236 ∧ planCycles routine236.pieces ≤ rankCost ⟨236, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine236, 85) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready237 : Chain.RoutineReady (embed ⟨237, by decide⟩) routine237 ∧ planCycles routine237.pieces ≤ rankCost ⟨237, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine237, 86) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready238 : Chain.RoutineReady (embed ⟨238, by decide⟩) routine238 ∧ planCycles routine238.pieces ≤ rankCost ⟨238, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine238, 85) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready239 : Chain.RoutineReady (embed ⟨239, by decide⟩) routine239 ∧ planCycles routine239.pieces ≤ rankCost ⟨239, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch29_checked (routine239, 85) (by unfold batch29; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check30 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine240 : ChainRoutine := ⟨250, [0, 4, 1, 2, 0, 0], [⟨210944, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨210949, [0x7508a3, 0x73], .rung 1 none⟩, ⟨210951, [0xd508a3, 0x73], .rung 2 none⟩, ⟨210953, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨210956, [0x21040513, 0x2c040613, 0xd87f8c93, 0x1953823, 0x73], .head 528 704 2 3⟩, ⟨210961, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨210966, [0x13508a3, 0x73], .rung 3 none⟩, ⟨210968, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨210972, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine241 : ChainRoutine := ⟨251, [0, 4, 2, 0, 0, 1], [⟨211008, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨211013, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211015, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211017, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨211020, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨211025, [0x13508a3, 0x73], .rung 3 none⟩, ⟨211027, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨211031, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨211036, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine242 : ChainRoutine := ⟨252, [0, 4, 2, 0, 1, 0], [⟨211072, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨211077, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211079, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211081, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨211084, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨211089, [0x13508a3, 0x73], .rung 3 none⟩, ⟨211091, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨211095, [0x1a840513, 0x1d840613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 472 4 3⟩, ⟨211100, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨211104, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine243 : ChainRoutine := ⟨253, [0, 4, 2, 1, 0, 0], [⟨211136, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨211141, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211143, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211145, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨211148, [0x21040513, 0x24040613, 0xc87f8c93, 0x1953823, 0x73], .head 528 576 2 2⟩, ⟨211153, [0x13508a3, 0x2c040613, 0x73], .rung 3 (some 704)⟩, ⟨211156, [0x19040513, 0x18040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 384 3 3⟩, ⟨211161, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨211165, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine244 : ChainRoutine := ⟨254, [0, 4, 3, 0, 0, 0], [⟨211200, [0x1f840513, 0x1e840613, 0xa83f8c93, 0x1953823, 0x73], .head 504 488 1 0⟩, ⟨211205, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211207, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211209, [0x13508a3, 0x2b040613, 0x73], .rung 3 (some 688)⟩, ⟨211212, [0x21040513, 0x24040613, 0xb87f8c93, 0x1953823, 0x73], .head 528 576 2 1⟩, ⟨211217, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211219, [0x13508a3, 0x73], .rung 3 none⟩, ⟨211221, [0x24043183, 0x24843703, 0x2c343023, 0x2ce43423], .copy 528 704⟩, ⟨211225, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine245 : ChainRoutine := ⟨255, [1, 0, 0, 0, 2, 4], [⟨211264, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211269, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨211274, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211277, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨211282, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211284, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211286, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211289, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine246 : ChainRoutine := ⟨256, [1, 0, 0, 0, 3, 3], [⟨211328, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211333, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨211338, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211340, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211343, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨211348, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211350, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211353, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine247 : ChainRoutine := ⟨257, [1, 0, 0, 0, 4, 2], [⟨211392, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211397, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨211402, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211404, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211406, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211409, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨211414, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211417, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch30 : List (ChainRoutine × Nat) := [(routine240, 82), (routine241, 82), (routine242, 86), (routine243, 83), (routine244, 79), (routine245, 79), (routine246, 79), (routine247, 79)]
theorem batch30_checked : (batch30.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready240 : Chain.RoutineReady (embed ⟨240, by decide⟩) routine240 ∧ planCycles routine240.pieces ≤ rankCost ⟨240, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine240, 82) (by unfold batch30; exact List.mem_cons_self)
theorem ready241 : Chain.RoutineReady (embed ⟨241, by decide⟩) routine241 ∧ planCycles routine241.pieces ≤ rankCost ⟨241, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine241, 82) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready242 : Chain.RoutineReady (embed ⟨242, by decide⟩) routine242 ∧ planCycles routine242.pieces ≤ rankCost ⟨242, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine242, 86) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready243 : Chain.RoutineReady (embed ⟨243, by decide⟩) routine243 ∧ planCycles routine243.pieces ≤ rankCost ⟨243, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine243, 83) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready244 : Chain.RoutineReady (embed ⟨244, by decide⟩) routine244 ∧ planCycles routine244.pieces ≤ rankCost ⟨244, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine244, 79) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready245 : Chain.RoutineReady (embed ⟨245, by decide⟩) routine245 ∧ planCycles routine245.pieces ≤ rankCost ⟨245, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine245, 79) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready246 : Chain.RoutineReady (embed ⟨246, by decide⟩) routine246 ∧ planCycles routine246.pieces ≤ rankCost ⟨246, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine246, 79) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready247 : Chain.RoutineReady (embed ⟨247, by decide⟩) routine247 ∧ planCycles routine247.pieces ≤ rankCost ⟨247, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch30_checked (routine247, 79) (by unfold batch30; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check31 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine248 : ChainRoutine := ⟨258, [1, 0, 0, 1, 1, 4], [⟨211456, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211461, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨211466, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨211471, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨211476, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211478, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211480, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211483, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine249 : ChainRoutine := ⟨259, [1, 0, 0, 1, 2, 3], [⟨211520, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211525, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨211530, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨211535, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211538, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨211543, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211545, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211548, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine250 : ChainRoutine := ⟨260, [1, 0, 0, 1, 3, 2], [⟨211584, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211589, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨211594, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨211599, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211601, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211604, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨211609, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211612, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine251 : ChainRoutine := ⟨261, [1, 0, 0, 1, 4, 1], [⟨211648, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211653, [0x19040513, 0x2d040613, 0xd8bf8c93, 0x1953823, 0x73], .head 400 720 3 3⟩, ⟨211658, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨211663, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211665, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211667, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211670, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨211675, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine252 : ChainRoutine := ⟨262, [1, 0, 0, 2, 0, 4], [⟨211712, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211717, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨211722, [0x13508a3, 0x73], .rung 3 none⟩, ⟨211724, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨211728, [0x14040513, 0x17040613, 0xa93f8c93, 0x1953823, 0x73], .head 320 368 5 0⟩, ⟨211733, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211735, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211737, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211740, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine253 : ChainRoutine := ⟨263, [1, 0, 0, 2, 1, 3], [⟨211776, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211781, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨211786, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨211789, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨211794, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨211799, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211801, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211804, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine254 : ChainRoutine := ⟨264, [1, 0, 0, 2, 2, 2], [⟨211840, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211845, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨211850, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨211853, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨211858, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211861, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨211866, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨211869, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine255 : ChainRoutine := ⟨265, [1, 0, 0, 2, 3, 1], [⟨211904, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211909, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨211914, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨211917, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨211922, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211924, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨211927, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨211932, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch31 : List (ChainRoutine × Nat) := [(routine248, 81), (routine249, 82), (routine250, 82), (routine251, 81), (routine252, 82), (routine253, 82), (routine254, 83), (routine255, 82)]
theorem batch31_checked : (batch31.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready248 : Chain.RoutineReady (embed ⟨248, by decide⟩) routine248 ∧ planCycles routine248.pieces ≤ rankCost ⟨248, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine248, 81) (by unfold batch31; exact List.mem_cons_self)
theorem ready249 : Chain.RoutineReady (embed ⟨249, by decide⟩) routine249 ∧ planCycles routine249.pieces ≤ rankCost ⟨249, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine249, 82) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready250 : Chain.RoutineReady (embed ⟨250, by decide⟩) routine250 ∧ planCycles routine250.pieces ≤ rankCost ⟨250, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine250, 82) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready251 : Chain.RoutineReady (embed ⟨251, by decide⟩) routine251 ∧ planCycles routine251.pieces ≤ rankCost ⟨251, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine251, 81) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready252 : Chain.RoutineReady (embed ⟨252, by decide⟩) routine252 ∧ planCycles routine252.pieces ≤ rankCost ⟨252, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine252, 82) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready253 : Chain.RoutineReady (embed ⟨253, by decide⟩) routine253 ∧ planCycles routine253.pieces ≤ rankCost ⟨253, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine253, 82) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready254 : Chain.RoutineReady (embed ⟨254, by decide⟩) routine254 ∧ planCycles routine254.pieces ≤ rankCost ⟨254, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine254, 83) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready255 : Chain.RoutineReady (embed ⟨255, by decide⟩) routine255 ∧ planCycles routine255.pieces ≤ rankCost ⟨255, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch31_checked (routine255, 82) (by unfold batch31; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
-- ==== merged from W9Machine_WctN600Check32 ====
section

namespace W9Machine.N600.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def routine256 : ChainRoutine := ⟨266, [1, 0, 0, 2, 4, 0], [⟨211968, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨211973, [0x19040513, 0x18040613, 0xc8bf8c93, 0x1953823, 0x73], .head 400 384 3 2⟩, ⟨211978, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨211981, [0x1a840513, 0x1d840613, 0xa8ff8c93, 0x1953823, 0x73], .head 424 472 4 0⟩, ⟨211986, [0x7508a3, 0x73], .rung 1 none⟩, ⟨211988, [0xd508a3, 0x73], .rung 2 none⟩, ⟨211990, [0x13508a3, 0x73], .rung 3 none⟩, ⟨211992, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨211996, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine257 : ChainRoutine := ⟨267, [1, 0, 0, 3, 0, 3], [⟨212032, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212037, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨212042, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212044, [0x13508a3, 0x73], .rung 3 none⟩, ⟨212046, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨212050, [0x14040513, 0x17040613, 0xb93f8c93, 0x1953823, 0x73], .head 320 368 5 1⟩, ⟨212055, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212057, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨212060, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine258 : ChainRoutine := ⟨268, [1, 0, 0, 3, 1, 2], [⟨212096, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212101, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨212106, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212108, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨212111, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨212116, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨212121, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨212124, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine259 : ChainRoutine := ⟨269, [1, 0, 0, 3, 2, 1], [⟨212160, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212165, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨212170, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212172, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨212175, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨212180, [0x13508a3, 0x2e040613, 0x73], .rung 3 (some 736)⟩, ⟨212183, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨212188, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine260 : ChainRoutine := ⟨270, [1, 0, 0, 3, 3, 0], [⟨212224, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212229, [0x19040513, 0x18040613, 0xb8bf8c93, 0x1953823, 0x73], .head 400 384 3 1⟩, ⟨212234, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212236, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨212239, [0x1a840513, 0x1d840613, 0xb8ff8c93, 0x1953823, 0x73], .head 424 472 4 1⟩, ⟨212244, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212246, [0x13508a3, 0x73], .rung 3 none⟩, ⟨212248, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨212252, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine261 : ChainRoutine := ⟨271, [1, 0, 0, 4, 0, 2], [⟨212288, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212293, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨212298, [0x7508a3, 0x73], .rung 1 none⟩, ⟨212300, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212302, [0x13508a3, 0x73], .rung 3 none⟩, ⟨212304, [0x18043183, 0x18843703, 0x2c343823, 0x2ce43c23], .copy 336 720⟩, ⟨212308, [0x14040513, 0x17040613, 0xc93f8c93, 0x1953823, 0x73], .head 320 368 5 2⟩, ⟨212313, [0x13508a3, 0x2f040613, 0x73], .rung 3 (some 752)⟩, ⟨212316, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine262 : ChainRoutine := ⟨272, [1, 0, 0, 4, 1, 1], [⟨212352, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212357, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨212362, [0x7508a3, 0x73], .rung 1 none⟩, ⟨212364, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212366, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨212369, [0x1a840513, 0x2e040613, 0xd8ff8c93, 0x1953823, 0x73], .head 424 736 4 3⟩, ⟨212374, [0x14040513, 0x2f040613, 0xd93f8c93, 0x1953823, 0x73], .head 320 752 5 3⟩, ⟨212379, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def routine263 : ChainRoutine := ⟨273, [1, 0, 0, 4, 2, 0], [⟨212416, [0x25040513, 0x28040613, 0xd7ff8c93, 0x1953823, 0x73], .head 592 640 0 3⟩, ⟨212421, [0x19040513, 0x18040613, 0xa8bf8c93, 0x1953823, 0x73], .head 400 384 3 0⟩, ⟨212426, [0x7508a3, 0x73], .rung 1 none⟩, ⟨212428, [0xd508a3, 0x73], .rung 2 none⟩, ⟨212430, [0x13508a3, 0x2d040613, 0x73], .rung 3 (some 720)⟩, ⟨212433, [0x1a840513, 0x1d840613, 0xc8ff8c93, 0x1953823, 0x73], .head 424 472 4 2⟩, ⟨212438, [0x13508a3, 0x73], .rung 3 none⟩, ⟨212440, [0x1d843183, 0x1e043703, 0x2e343023, 0x2ee43423], .copy 424 736⟩, ⟨212444, [0x29f43823, 0x28043c23, 0x28040513, 0x8000593, 0x4b8067], .leaf⟩]⟩
def batch32 : List (ChainRoutine × Nat) := [(routine256, 82), (routine257, 82), (routine258, 82), (routine259, 82), (routine260, 82), (routine261, 82), (routine262, 81), (routine263, 82)]
theorem batch32_checked : (batch32.all fun rc => exactChecked rc.1 rc.2) = true := by decide +kernel
theorem ready256 : Chain.RoutineReady (embed ⟨256, by decide⟩) routine256 ∧ planCycles routine256.pieces ≤ rankCost ⟨256, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine256, 82) (by unfold batch32; exact List.mem_cons_self)
theorem ready257 : Chain.RoutineReady (embed ⟨257, by decide⟩) routine257 ∧ planCycles routine257.pieces ≤ rankCost ⟨257, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine257, 82) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_self))
theorem ready258 : Chain.RoutineReady (embed ⟨258, by decide⟩) routine258 ∧ planCycles routine258.pieces ≤ rankCost ⟨258, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine258, 82) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem ready259 : Chain.RoutineReady (embed ⟨259, by decide⟩) routine259 ∧ planCycles routine259.pieces ≤ rankCost ⟨259, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine259, 82) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem ready260 : Chain.RoutineReady (embed ⟨260, by decide⟩) routine260 ∧ planCycles routine260.pieces ≤ rankCost ⟨260, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine260, 82) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem ready261 : Chain.RoutineReady (embed ⟨261, by decide⟩) routine261 ∧ planCycles routine261.pieces ≤ rankCost ⟨261, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine261, 82) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem ready262 : Chain.RoutineReady (embed ⟨262, by decide⟩) routine262 ∧ planCycles routine262.pieces ≤ rankCost ⟨262, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine262, 81) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem ready263 : Chain.RoutineReady (embed ⟨263, by decide⟩) routine263 ∧ planCycles routine263.pieces ≤ rankCost ⟨263, by decide⟩ := by
  apply ready_exact _ _ rfl
  exact List.all_eq_true.mp batch32_checked (routine263, 82) (by unfold batch32; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
end W9Machine.N600.Checks
end
