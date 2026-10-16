import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.HornRun
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FamilySpec

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
theorem fChildStep_eq (index c j : Nat) (word : WCT9.Rank) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Fin 6) :
    fChildStep index c j word coefs state i =
      (chainRest index c j i.val (WCT9.wordDigit word i) 4 [WCT9.ftsFamilySeed coefs j i.val] >>= fun r =>
        pure (state.1 ++ [r.2], state.2 ++ [r.1])) := by
  have hd := WCT9.wordDigit_le_four word i
  unfold fChildStep
  dsimp only
  rw [← chain4_eq index c j i.val _ hd]
  simp only [bind_assoc, pure_bind]
def bodyRegs : List Reg := [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x26, .x28, .x29]
def bodyW (c : Nat) (A : Nat) : Prop :=
  (PRIVW + 16 ≤ A ∧ A < PRIVW + 32) ∨ (PAIRW ≤ A ∧ A < PAIRW + 32) ∨ (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨
    (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) ∨ (LEAFW ≤ A ∧ A < LEAFW + 128) ∨ (slotV c 0 ≤ A ∧ A < slotV c 6)
structure BodySt (sk : BitVec 256) (j index sel w : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
theorem BodySt.of {sk : BitVec 256} {j index sel w : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (h : BodySt sk j index sel w s) (hr : RegsExcept s t l)
    (hl : .x5 ∉ l ∧ .x18 ∉ l ∧ .x22 ∉ l ∧ .x24 ∉ l ∧ .x25 ∉ l) (hf : Frame s t W)
    (hW : ¬ W PRIVW ∧ ¬ W (PRIVW + 8) ∧ ¬ W (PRIVW + 32) ∧ ¬ W (PRIVW + 40) ∧ ¬ W (PRIVW + 48) ∧
      ¬ W (PRIVW + 56) ∧ ¬ W CHAINW ∧ ¬ W (CHAINW + 8) ∧ ¬ W (CHAINW + 32) ∧ ¬ W (CHAINW + 40)) :
    BodySt sk j index sel w t := by
  obtain ⟨l5, l18, l22, l24, l25⟩ := hl
  obtain ⟨w0, w8, w32, w40, w48, w56, c0, c8, c32, c40⟩ := hW
  exact ⟨by rw [hr.get l5]; exact h.x5, by rw [hr.get l18]; exact h.x18, by rw [hr.get l22]; exact h.x22,
    by rw [hr.get l24]; exact h.x24, by rw [hr.get l25]; exact h.x25,
    by rw [hf.get (by ao) w0]; exact h.p0, by rw [hf.get (by ao) w8]; exact h.p8,
    by rw [hf.get (by ao) w32]; exact h.p32, by rw [hf.get (by ao) w40]; exact h.p40,
    by rw [hf.get (by ao) w48]; exact h.p48, by rw [hf.get (by ao) w56]; exact h.p56,
    by rw [hf.get (by ao) c0]; exact h.z0, by rw [hf.get (by ao) c8]; exact h.z8,
    by rw [hf.get (by ao) c32]; exact h.z32, by rw [hf.get (by ao) c40]; exact h.z40⟩
structure RowsAt (c j sel n : Nat) (rows : List Digest × List Digest) (t : MachineState) : Prop where
  len1 : rows.1.length = n
  len2 : rows.2.length = n
  leaf : ∀ i < n, DigAt t (LEAFW + leafOff i) (rows.1.getD i 0)
  sig : j = sel → ∀ i < n, DigAt t (slotV c i) (rows.2.getD i 0)
theorem leafOff_lt (i : Nat) (hi : i < 6) : leafOff i + 16 ≤ 128 := by unfold leafOff; split_ifs <;> omega
theorem leafOff_ne (i i' : Nat) (hi : i < 6) (hi' : i' < 6) (hne : i ≠ i') :
    leafOff i ≠ leafOff i' ∧ leafOff i ≠ leafOff i' + 8 ∧ leafOff i + 8 ≠ leafOff i' ∧ leafOff i + 8 ≠ leafOff i' + 8 := by
  unfold leafOff; split_ifs <;> omega
theorem hashInput_priv (t : MachineState) (sk : BitVec 256) {c index q : Nat} (hc : c < 9) (hidx : index < 2 ^ 32)
    (hq : q < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 PRIVW) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64)
    (p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64)
    (p16 : t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c))
    (p24 : t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * q))
    (p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64)
    (p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64)
    (p48 : t.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0) (p56 : t.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0) :
    hashInput t = toQ (privateInput sk (.inl (header 8 c index 0 q))) := by
  refine hashInput_of_words t _ 0 PRIVW (by rw [privateInput_tweak_length]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_priv sk c index q (by omega) hidx hq]
  intro k hk
  interval_cases k
  · exact p0
  · exact p8
  · exact p16
  · exact p24
  · exact p32
  · exact p40
  · exact p48
  · exact p56
theorem slotV_lt (c i : Nat) (hi : i < 6) : slotV c i + 16 ≤ slotV c 6 := by unfold slotV; omega
theorem chainW_bodyW {c i A : Nat} (hi : i < 6) (h : chainW c i A) : bodyW c A := by
  have := leafOff_lt i hi
  have := slotV_lt c i hi
  unfold chainW at h; unfold bodyW
  rcases h with h | h | h | h | h | h
  · right; right; left; exact h
  · right; right; right; left; exact h
  · right; right; right; right; left; subst h; constructor <;> omega
  · right; right; right; right; left; subst h; constructor <;> omega
  · right; right; right; right; right; subst h; unfold slotV at *; constructor <;> omega
  · right; right; right; right; right; subst h; unfold slotV at *; constructor <;> omega
theorem BodySt.of_body {sk : BitVec 256} {j index sel w c : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (hc : c < 9) (h : BodySt sk j index sel w s) (hr : RegsExcept s t l) (hl : ∀ r ∈ l, r ∈ bodyRegs) (hf : Frame s t W)
    (hW : ∀ A, W A → bodyW c A) : BodySt sk j index sel w t := by
  have nb : ∀ A, (A = PRIVW ∨ A = PRIVW + 8 ∨ A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ A = PRIVW + 48 ∨ A = PRIVW + 56 ∨
      A = CHAINW ∨ A = CHAINW + 8 ∨ A = CHAINW + 32 ∨ A = CHAINW + 40) → ¬ W A := by
    intro A hA hw
    have := hW A hw
    unfold bodyW slotV at this
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [PRIVW, PAIRW, CHAINW, LEAFW, SIG] at this <;> omega
  refine h.of hr ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩ hf
    ⟨nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp),
      nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp)⟩ <;>
    · have := hl _ m; simp [bodyRegs] at this
theorem RowsAt.frame {c j sel n : Nat} {rows : List Digest × List Digest} {s t : MachineState} {W : Nat → Prop}
    (h : RowsAt c j sel n rows s) (hc : c < 9) (hn : n ≤ 6) (hf : Frame s t W)
    (hW : ∀ i < n, ¬ W (LEAFW + leafOff i) ∧ ¬ W (LEAFW + leafOff i + 8) ∧ ¬ W (slotV c i) ∧ ¬ W (slotV c i + 8)) :
    RowsAt c j sel n rows t := by
  refine ⟨h.len1, h.len2, fun i hi => ?_, fun hjs i hi => ?_⟩
  · have := leafOff_lt i (by omega)
    exact (h.leaf i hi).frame hf (by ao) (hW i hi).1 (hW i hi).2.1
  · exact (h.sig hjs i hi).frame hf (by unfold slotV; ao) (hW i hi).2.2.1 (hW i hi).2.2.2
theorem RowsAt.snoc {c j sel n : Nat} {rows : List Digest × List Digest} {t : MachineState} {x y : Digest}
    (h : RowsAt c j sel n rows t) (hl : DigAt t (LEAFW + leafOff n) x) (hs : j = sel → DigAt t (slotV c n) y) :
    RowsAt c j sel (n + 1) (rows.1 ++ [x], rows.2 ++ [y]) t := by
  refine ⟨by simp [h.len1], by simp [h.len2], fun i hi => ?_, fun hjs i hi => ?_⟩
  · by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len1]; exact hin), ← List.getD_eq_getElem?_getD]
      exact h.leaf i hin
    · have : i = n := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len1]), h.len1, Nat.sub_self]; exact hl
  · by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len2]; exact hin), ← List.getD_eq_getElem?_getD]
      exact h.sig hjs i hin
    · have : i = n := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len2]), h.len2, Nat.sub_self]; exact hs hjs
theorem chainW_other {c i i' : Nat} (hc : c < 9) (hi : i < 6) (hi' : i' < 6) (hne : i' ≠ i) :
    ¬ chainW c i (LEAFW + leafOff i') ∧ ¬ chainW c i (LEAFW + leafOff i' + 8) ∧ ¬ chainW c i (slotV c i') ∧
      ¬ chainW c i (slotV c i' + 8) := by
  have h1 := leafOff_lt i hi
  have h2 := leafOff_lt i' hi'
  have h3 := leafOff_ne i' i hi' hi hne
  unfold chainW slotV
  refine ⟨?_, ?_, ?_, ?_⟩ <;> aoh
theorem coef_not_bodyW {c A : Nat} (hc : c < 9) (h1 : COEF ≤ A) (h2 : A < COEF + 864) : ¬ bodyW c A := by
  intro h; unfold bodyW slotV at h; simp only [PRIVW, PAIRW, CHAINW, LEAFW, SIG, COEF] at *; omega
theorem pcOf_ret (n : Nat) : pcOf n &&& BitVec.ofNat 64 (2 ^ 64 - 2) = pcOf n := pcOf_and_max n
def stepC : Nat := 5 + (hornC + (17 + (11 + 28 * 4 + 8)))
section step
variable {im : Image} {sk : BitVec 256}
theorem step_unit (hcode : NewCodeAt im) {c i j index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hc : c < 9) (hi : i < 6) (hj : j < 128) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 6, w / 8 ^ i.val % 8 = WCT9.wordDigit word i) (hlen : coefs.length = 54)
    {rows : List Digest × List Digest} {s : MachineState} (hpc : s.pc = pcOf (qI c i))
    (hb : BodySt sk j index sel w s) (hr : RowsAt c j sel i rows s) (hcoef : CoefAt s coefs) :
    TBSim im sk s stepC (fChildStep index c j word coefs rows ⟨i, hi⟩) (fun rows' t =>
      t.pc = pcOf (lcEnd c i) ∧ BodySt sk j index sel w t ∧ RowsAt c j sel (i + 1) rows' t ∧
        RegsExcept s t bodyRegs ∧ Frame s t (bodyW c) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) ∧
        t.getReg .x29 = BitVec.ofNat 64 LEAFW) := by
  have hdig : WCT9.wordDigit word ⟨i, hi⟩ = w / 8 ^ i % 8 := (hword ⟨i, hi⟩).symm
  have hd4 : w / 8 ^ i % 8 ≤ 4 := by rw [← hdig]; exact WCT9.wordDigit_le_four word ⟨i, hi⟩
  rw [fChildStep_eq, hdig]
  obtain ⟨t1, s1, p1, x1, x6, r1, f1⟩ := step_Q hcode hc hi s hpc hb.x18 hj
  obtain ⟨t2, n2, c2, s2, hc2, p2, seed2, r2, f2⟩ :=
    horn_run hcode t1 p1 (d := 6 * j + i + 1) (by omega) x6 hlen (hcoef.frame f1 (fun _ _ _ h => h))
  have p2' : t2.pc = pcOf (qI c i + 5) := by rw [p2, x1, pcOf_ret]
  have g2 : ∀ r, r ∉ [Reg.x1, .x6] ++ hornRegs → t2.getReg r = s.getReg r := r1.trans r2
  obtain ⟨t3, s3, p3, x26, m16, m24, r3, f3⟩ := step_S hcode hc hi t2 p2'
    (by rw [g2 _ (by simp [hornRegs])]; exact hb.x18) (by rw [g2 _ (by simp [hornRegs])]; exact hb.x22) hj
    (by rw [g2 _ (by simp [hornRegs])]; exact hb.x25) hw hd4
  have g3 : ∀ r, r ∉ ([Reg.x1, .x6] ++ hornRegs) ++ [.x6, .x7, .x26, .x29] → t3.getReg r = s.getReg r :=
    (r1.trans r2).trans r3
  have f13 : Frame s t3 (fun A => (False ∨ (A = CHAINW + 48 ∨ A = CHAINW + 56)) ∨
      (A = CHAINW + 24 ∨ A = CHAINW + 16)) := (f1.trans f2).trans f3
  have m3 : ∀ A, A < 2 ^ 64 → A ≠ CHAINW + 48 → A ≠ CHAINW + 56 → A ≠ CHAINW + 24 → A ≠ CHAINW + 16 →
      t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 h3 h4 =>
    f13.get hA (by simp [h1, h2, h3, h4])
  have hseed : DigAt t3 (CHAINW + 48) (WCT9.ftsFamilySeed coefs j i) := by
    have : DigAt t2 (CHAINW + 48) (WCT9.ftsFamilySeed coefs j i) := by
      unfold WCT9.ftsFamilySeed WCT9.ftsPoint WCT9.ftsOrdinal; exact seed2
    exact this.frame f3 (by ao) (by ao) (by ao)
  have hst : ChkSt c i j index sel w (w / 8 ^ i % 8) 4 [WCT9.ftsFamilySeed coefs j i] t3 t3 :=
    { pc := p3
      x5 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x5
      x18 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x18
      x22 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x22
      x24 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x24
      x25 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x25
      x26 := x26
      len := rfl
      val := hseed
      h16 := m16
      h24 := m24
      z0 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z0
      z8 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z8
      z32 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z32
      z40 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z40
      op := fun _ h => absurd h (by omega)
      regs := RegsExcept.refl _ _
      frame := Frame.refl _ _
      nosel := fun _ _ _ _ _ => rfl }
  have hk3 : (if c = 0 then 17 else 15) ≤ 17 := by split <;> omega
  refine (TBSim.steps ((s1.trans s2).trans s3) (TBSim.bind (W₂ := 0)
    (chain_from hcode hc hi hj hsel hidx hw hd4 4 le_rfl _ t3 hst) (fun r t ht => ?_))).mono
    (by unfold stepC; omega) (fun _ _ h => h)
  obtain ⟨tpc, tleaf, tsig, tregs, tframe, tnos, tx29⟩ := ht
  have fst : Frame s t (bodyW c) := (f13.trans tframe).mono (fun A _ hA => by
    rcases hA with ((hA | hA) | hA) | hA
    · exact hA.elim
    · unfold bodyW; right; right; right; left; rcases hA with rfl | rfl <;> constructor <;> ao
    · unfold bodyW; right; right; left; rcases hA with rfl | rfl <;> constructor <;> ao
    · exact chainW_bodyW hi hA)
  have rst : RegsExcept s t bodyRegs := (((r1.trans r2).trans r3).trans tregs).mono
    (by simp [hornRegs, chainRegs, bodyRegs])
  refine TBSim.pure ⟨tpc, hb.of_body hc rst (fun _ h => h) fst (fun _ h => h), ?_, rst, fst, ?_, tx29⟩
  · have hr3 : RowsAt c j sel i rows t3 := hr.frame hc (by omega) f13 (fun i' hi' => by
      have := leafOff_lt i' (by omega)
      unfold slotV
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; simp only [false_or] at h; rcases h with (h | h) | (h | h) <;> aoh))
    exact (hr3.frame hc (by omega) tframe (fun i' hi' => chainW_other hc hi (by omega) (by omega))).snoc tleaf tsig
  · intro hjs A hA h1 h2
    rw [tnos hjs A hA h1 h2, m3 A hA (by unfold slotV at h1 h2; aoh) (by unfold slotV at h1 h2; aoh)
      (by unfold slotV at h1 h2; aoh) (by unfold slotV at h1 h2; aoh)]
end step
end ClaudeWCT.W9.Machine.Sign
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
/-- Nested FTS (r1-1): the pad value `pad` of coordinate `c` (word offset `off` = 0 for `L`, 16 for `R`) sits in
the previous forest pair (zero for coordinate 0). -/
def PadAt (c off : Nat) (pad : Digest) (t : MachineState) : Prop :=
  if c = 0 then pad = 0 else DigAt t (FORW + forOff (c - 1) + off) pad
theorem PadAt.frame {c off : Nat} {pad : Digest} {s t : MachineState} {W : Nat → Prop} (hc : c < 9) (hoff : off ≤ 16)
    (h : PadAt c off pad s) (hf : Frame s t W)
    (hW : ∀ A, FORW + 32 ≤ A → A < FORW + 320 → ¬ W A) : PadAt c off pad t := by
  unfold PadAt at *
  split_ifs at h ⊢ with c0
  · exact h
  · have : forOff (c - 1) ≤ 256 := by unfold forOff; omega
    have : 32 ≤ forOff (c - 1) := by unfold forOff; omega
    exact h.frame hf (by ao) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))
theorem PadAt.of_eq {c off : Nat} {pad : Digest} {s t : MachineState} (hc : c < 9) (hoff : off ≤ 16)
    (h : PadAt c off pad s)
    (he : ∀ A, FORW + 32 ≤ A → A < FORW + 320 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) :
    PadAt c off pad t := by
  unfold PadAt at *
  split_ifs at h ⊢ with c0
  · exact h
  · have : forOff (c - 1) ≤ 256 := by unfold forOff; omega
    have : 32 ≤ forOff (c - 1) := by unfold forOff; omega
    exact ⟨(he _ (by omega) (by omega)).trans h.1, (he _ (by omega) (by omega)).trans h.2⟩
theorem PadAt.zero {off : Nat} {pad : Digest} {s : MachineState} (h : PadAt 0 off pad s) : pad = 0 := by
  unfold PadAt at h; rw [if_pos rfl] at h; exact h
theorem padE_pad {c : Nat} {pad : Digest} {s : MachineState} (h : PadAt c 0 pad s) :
    (padE c 0).eval s = pad.extractLsb' 0 64 ∧ (padE c 8).eval s = pad.extractLsb' 64 64 := by
  rw [padE_eval, padE_eval]
  unfold PadAt at h
  split_ifs at h ⊢ with c0
  · subst h; exact ⟨rfl, rfl⟩
  · exact ⟨by rw [Nat.add_zero]; exact h.1, h.2⟩
theorem hashInput_leaf (t : MachineState) {c j index : Nat} {pad : Digest} (ends : List Digest)
    (hlen : ends.length = 6) (hc : c < 9)
    (hidx : index < 2 ^ 31) (hj : j < 128) (h10 : t.getReg .x10 = BitVec.ofNat 64 LEAFW)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 128) (he : ∀ i < 6, DigAt t (LEAFW + leafOff i) (ends.getD i 0))
    (m16 : t.getMem (BitVec.ofNat 64 (LEAFW + 16)) = BitVec.ofNat 64 (leafLo7 c index j))
    (m24 : t.getMem (BitVec.ofNat 64 (LEAFW + 24)) = 0)
    (m32 : t.getMem (BitVec.ofNat 64 (LEAFW + 32)) = pad.extractLsb' 0 64)
    (m40 : t.getMem (BitVec.ofNat 64 (LEAFW + 40)) = pad.extractLsb' 64 64) :
    hashInput t = toQ (pad64 (leafIn index c j pad ends)) := by
  refine hashInput_of_words t _ 1 LEAFW (by rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ _ hlen]),
    leafIn_len _ _ _ _ _ hlen]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_leaf index c j pad ends hlen hc hidx hj]
  match ends, hlen with
  | [e0, e1, e2, e3, e4, e5], _ =>
    have d0 := he 0 (by norm_num); have d1 := he 1 (by norm_num); have d2 := he 2 (by norm_num)
    have d3 := he 3 (by norm_num); have d4 := he 4 (by norm_num); have d5 := he 5 (by norm_num)
    simp only [leafOff, List.getD_cons_zero, List.getD_cons_succ] at d0 d1 d2 d3 d4 d5
    simp only [if_true, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
      show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, if_false,
      Nat.add_zero] at d0 d1 d2 d3 d4 d5
    intro k hk
    interval_cases k <;> simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, wordsOf_bytesLE16, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    · exact d0.1
    · exact d0.2
    · exact m16
    · exact m24
    · exact m32
    · exact m40
    · exact d1.1
    · exact d1.2
    · exact d2.1
    · exact d2.2
    · exact d3.1
    · exact d3.2
    · exact d4.1
    · exact d4.2
    · exact d5.1
    · exact d5.2
theorem leafI_qI : ∀ c, c < 9 → leafI c = qI c 0 := by decide +kernel
theorem tI_pos : ∀ c, c < 9 → 1 ≤ tI c := by decide +kernel
def childW (c j : Nat) (A : Nat) : Prop :=
  bodyW c A ∨ (HEAPW + 16 * (128 + j) ≤ A ∧ A < HEAPW + 16 * (128 + j) + 32)
def childC : Nat := 6 * stepC + (23 + (16 + 0))
theorem fChildRows_fold (index c j : Nat) (word : WCT9.Rank) (coefs : List Digest) :
    fChildRows index c j word coefs = (List.range' 0 6).foldlM
      (fun st k => if h : k < 6 then fChildStep index c j word coefs st ⟨k, h⟩ else pure st) ([], []) := by
  unfold fChildRows
  rw [show List.finRange 6 = [0, 1, 2, 3, 4, 5] from rfl, show List.range' 0 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.foldlM_cons, List.foldlM_nil]
  rfl
structure StepInv (sk : BitVec 256) (c j index sel w : Nat) (s0 : MachineState) (k : Nat)
    (rows : List Digest × List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 6 then qI c k else lI c)
  body : BodySt sk j index sel w t
  rws : RowsAt c j sel k rows t
  regs : RegsExcept s0 t bodyRegs
  frame : Frame s0 t (bodyW c)
  nos : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
  x29 : 0 < k → t.getReg .x29 = BitVec.ofNat 64 LEAFW
section child
variable {im : Image} {sk : BitVec 256}
theorem child_unit (hcode : NewCodeAt im) {c j index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hc : c < 9) (hj : j < 128) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 6, w / 8 ^ i.val % 8 = WCT9.wordDigit word i) (hlen : coefs.length = 54) {s : MachineState}
    (hpc : s.pc = pcOf (leafI c)) (hb : BodySt sk j index sel w s) (hcoef : CoefAt s coefs)
    {padL : Digest} (hpad : PadAt c 0 padL s) :
    TBSim im sk s childC (WCT9.buildChildF index c j word coefs padL) (fun rv t =>
      t.pc = pcOf (tI c) ∧ BodySt sk j index sel w t ∧ DigAt t (HEAPW + 16 * (128 + j)) rv.1 ∧
        (j = sel → rv.2.length = 6 ∧ ∀ i < 6, DigAt t (slotV c i) (rv.2.getD i 0)) ∧
        RegsExcept s t bodyRegs ∧ Frame s t (childW c j) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A))) := by
  rw [buildChildF_factor, fChildRows_fold]
  have h0 : StepInv sk c j index sel w s 0 ([], []) s :=
    ⟨by rw [if_pos (by norm_num), ← leafI_qI c hc]; exact hpc, hb,
      ⟨rfl, rfl, fun i hi => absurd hi (by omega), fun _ i hi => absurd hi (by omega)⟩,
      RegsExcept.refl _ _, Frame.refl _ _, fun _ _ _ _ _ => rfl, fun h => absurd h (by omega)⟩
  refine (TBSim.bind (W₂ := 23 + (16 + 0))
    (TBSim.foldlM_range' 0 6 _ _ (StepInv sk c j index sel w s) stepC (fun k hk rows t ht => ?_) h0)
    (fun rows t4 h4 => ?_)).mono (by unfold childC; omega) (fun _ _ h => h)
  · simp only [Nat.zero_add, dif_pos hk]
    have hpc' : t.pc = pcOf (qI c k) := by rw [ht.pc, if_pos hk]
    refine (step_unit hcode hc hk hj hsel hidx hw hword hlen hpc' ht.body ht.rws
      (hcoef.frame ht.frame (fun A h1 h2 => coef_not_bodyW hc h1 h2))).mono le_rfl (fun rows' u hu => ?_)
    obtain ⟨upc, ub, ur, ureg, ufr, unos, ux29⟩ := hu
    refine ⟨?_, ub, ur, (ht.regs.trans ureg).mono (by simp [bodyRegs]),
      (ht.frame.trans ufr).mono (fun A _ hA => by rcases hA with hA | hA <;> exact hA),
      fun hjs A hA h1 h2 => by rw [unos hjs A hA h1 h2, ht.nos hjs A hA h1 h2], fun _ => ux29⟩
    rw [upc]; unfold lcEnd
    by_cases h6 : k = 5
    · subst h6; rw [if_pos rfl, if_neg (by omega)]
    · rw [if_neg h6, if_pos (by omega)]
  · have p4 : t4.pc = pcOf (lI c) := by rw [h4.pc, if_neg (by omega)]
    have b4 := h4.body
    obtain ⟨t5, s5, e5, p5, x10, x11, x12, m16, m24, m32, m40, r5, f5⟩ :=
      step_L hcode hc t4 p4 b4.x18 b4.x22 hj (h4.x29 (by norm_num))
    have hp4 : PadAt c 0 padL t4 := hpad.frame hc (by norm_num) h4.frame (fun A h1 h2 hw => by
      unfold bodyW slotV at hw; aoh)
    rw [(padE_pad hp4).1] at m32
    rw [(padE_pad hp4).2] at m40
    have hrows : RowsAt c j sel 6 rows t5 := h4.rws.frame hc (by norm_num) f5 (fun i hi => by
      have := leafOff_lt i (by omega)
      have := leafOff_ne i 1 (by omega) (by norm_num)
      unfold slotV leafOff at *
      refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs at * <;> aoh)
    have hq := hashInput_leaf t5 rows.1 hrows.len1 hc (by omega) (by omega) x10 x11 hrows.leaf m16 m24 m32 m40
    have hb5 : BodySt sk j index sel w t5 := b4.of_body hc r5 (by simp [bodyRegs]) f5 (fun A hA => by
      unfold bodyW; rcases hA with rfl | rfl | rfl | rfl <;> (right; right; right; right; left; constructor <;> ao))
    have hbl : (toQ (pad64 (leafIn index c j padL rows.1))).blocks = 2 := by
      rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ _ hrows.len1]),
        blocks_toQ ⟨by rw [leafIn_len _ _ _ _ _ hrows.len1]; norm_num, by rw [leafIn_len _ _ _ _ _ hrows.len1]⟩,
        leafIn_len _ _ _ _ _ hrows.len1]
    rw [leafHashP_eq]
    refine (TBSim.steps s5 (TBSim.shortHash_bind' (W := 0) (f := fun root => pure (root, rows.2)) e5
      hb5.x5 (hashArgs_const t5 LEAFW 128 (HEAPW + 16 * (j + 128)) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao)
        (by ao)) hq (fun a => TBSim.pure ?_))).mono (by rw [hbl]; split <;> omega) (fun _ _ h => h)
    have fh := Frame.writeHash t5 a (HEAPW + 16 * (j + 128)) x12 (by ao)
    refine ⟨?_, ?_, ?_, fun hjs => ⟨by rw [hrows.len2], fun i hi => ?_⟩, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p5, pcOf_pred4 _ (tI_pos c hc)]
    · exact hb5.of (fun x _ => getReg_writeHash t5 a x : RegsExcept t5 (writeHash t5 a) []) (by simp) fh
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ao)
    · rw [show 128 + j = j + 128 by omega]; exact DigAt.writeHash_lo t5 a _ x12 (by ao)
    · exact (hrows.sig hjs i hi).frame fh (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact (h4.regs.trans (r5.trans (fun x _ => getReg_writeHash t5 a x : RegsExcept t5 (writeHash t5 a) []))).mono
        (by simp [bodyRegs])
    · refine ((h4.frame.trans f5).trans fh).mono (fun A _ hA => ?_)
      unfold childW
      rcases hA with (hA | hA) | hA
      · left; exact hA
      · left; unfold bodyW; rcases hA with rfl | rfl | rfl | rfl <;> (right; right; right; right; left; constructor <;> ao)
      · right; constructor <;> omega
    · intro hjs A hA h1 h2
      rw [fh.get hA (by unfold slotV at h1 h2; intro h'; aoh), f5.get hA (by unfold slotV at h1 h2; intro h'; aoh),
        h4.nos hjs A hA h1 h2]
end child
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
def loopW (c : Nat) (A : Nat) : Prop := bodyW c A ∨ (HEAPW + 16 * 128 ≤ A ∧ A < SCREND)
structure LoopInv (sk : BitVec 256) (c index sel w : Nat) (s0 : MachineState) (j : Nat)
    (acc : List Digest × List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if j < 128 then leafI c else nodeI c)
  body : BodySt sk (if j < 128 then j else 127) index sel w t
  len : acc.1.length = j
  leaves : ∀ j' < j, DigAt t (HEAPW + 16 * (128 + j')) (acc.1.getD j' 0)
  vals : sel < j → acc.2.length = 6 ∧ ∀ i < 6, DigAt t (slotV c i) (acc.2.getD i 0)
  nosig : j ≤ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
  regs : RegsExcept s0 t (.x18 :: bodyRegs)
  frame : Frame s0 t (loopW c)
def loopStepC : Nat := childC + 4
theorem BodySt.with18 {sk : BitVec 256} {j j' index sel w : Nat} {u v : MachineState} (h : BodySt sk j index sel w u)
    (hr : RegsExcept u v [.x6, .x18]) (hf : Frame u v (fun _ => False)) (h18 : v.getReg .x18 = BitVec.ofNat 64 j') :
    BodySt sk j' index sel w v := by
  have g : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := fun A hA => hf.get hA id
  exact ⟨by rw [hr.get (by simp)]; exact h.x5, h18, by rw [hr.get (by simp)]; exact h.x22,
    by rw [hr.get (by simp)]; exact h.x24, by rw [hr.get (by simp)]; exact h.x25,
    by rw [g _ (by ao)]; exact h.p0, by rw [g _ (by ao)]; exact h.p8, by rw [g _ (by ao)]; exact h.p32,
    by rw [g _ (by ao)]; exact h.p40, by rw [g _ (by ao)]; exact h.p48, by rw [g _ (by ao)]; exact h.p56,
    by rw [g _ (by ao)]; exact h.z0, by rw [g _ (by ao)]; exact h.z8, by rw [g _ (by ao)]; exact h.z32,
    by rw [g _ (by ao)]; exact h.z40⟩
section loop
variable {im : Image} {sk : BitVec 256}
theorem coef_not_loopW {c A : Nat} (hc : c < 9) (h1 : COEF ≤ A) (h2 : A < COEF + 864) : ¬ loopW c A := by
  intro h; rcases h with h | h
  · exact coef_not_bodyW hc h1 h2 h
  · simp only [HEAPW, SCREND, COEF] at *; omega
theorem child_step (hcode : NewCodeAt im) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hc : c < 9) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 6, w / 8 ^ i.val % 8 = WCT9.wordDigit word i) (hlen : coefs.length = 54)
    {s0 : MachineState} (hcoef : CoefAt s0 coefs) {padL : Digest} (hpad : PadAt c 0 padL s0) (j : Nat) (hj : j < 128)
    (acc : List Digest × List Digest) (t : MachineState) (h : LoopInv sk c index sel w s0 j acc t) :
    TBSim im sk t loopStepC (do
        let (root, values) ← WCT9.buildChildF index c j word coefs padL
        pure (acc.1 ++ [root], (if j = sel then values else acc.2)))
      (LoopInv sk c index sel w s0 (j + 1)) := by
  have hpc : t.pc = pcOf (leafI c) := by rw [h.pc, if_pos hj]
  have hb : BodySt sk j index sel w t := by have := h.body; rwa [if_pos hj] at this
  refine (TBSim.bind (W₂ := 4) (child_unit hcode hc hj hsel hidx hw hword hlen hpc hb
    (hcoef.frame h.frame (fun A h1 h2 => coef_not_loopW hc h1 h2))
    (hpad.frame hc (by norm_num) h.frame (fun A h1 h2 hw => by unfold loopW bodyW slotV at hw; aoh)))
    (fun rv u hu => ?_)).mono
    (by unfold loopStepC; omega) (fun _ _ h => h)
  obtain ⟨root, values⟩ := rv
  obtain ⟨upc, ub, uroot, usel, uregs, uframe, unos⟩ := hu
  obtain ⟨v, k, sv, hk, vp1, vp2, vregs, vframe⟩ := step_T hcode hc hj u upc ub.x18
  refine TBSim.pure_steps' sv ?_ |>.mono hk (fun _ _ h => h)
  have hheap : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
    fun A hA => vframe.get hA (fun h => h)
  have fuv : Frame t v (childW c j) := (uframe.trans vframe).mono (fun A _ hA => by
    rcases hA with hA | hA
    · exact hA
    · exact hA.elim)
  refine ⟨?_, ?_, ?_, fun j' hj' => ?_, fun hs => ?_, fun hs A hA h1 h2 => ?_, ?_, ?_⟩
  · by_cases h1 : j + 1 < 128
    · rw [if_pos h1]; exact (vp1 h1).1
    · rw [if_neg h1]; exact (vp2 (by omega)).1
  · by_cases h1 : j + 1 < 128
    · rw [if_pos h1]; exact ub.with18 vregs vframe (vp1 h1).2
    · rw [if_neg h1]; exact ub.with18 vregs vframe (vp2 (by omega)).2
  · simp [h.len]
  · by_cases hlt : j' < j
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      refine (h.leaves j' hlt).frame fuv (by ao) ?_ ?_ <;> (unfold childW bodyW slotV; aoh)
    · have : j' = j := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len]), h.len, Nat.sub_self]
      exact uroot.frame vframe (by ao) (fun h => h) (fun h => h)
  · by_cases hjs : j = sel
    · subst hjs
      rw [if_pos rfl]
      obtain ⟨hl, hd⟩ := usel rfl
      exact ⟨hl, fun i hi => (hd i hi).frame vframe (by unfold slotV; ao) (fun h => h) (fun h => h)⟩
    · rw [if_neg hjs]
      obtain ⟨hl, hd⟩ := h.vals (by omega)
      refine ⟨hl, fun i hi => ⟨?_, ?_⟩⟩
      · rw [hheap _ (by unfold slotV; ao), unos hjs _ (by unfold slotV; ao) (by unfold slotV; omega)
          (by unfold slotV; omega)]
        exact (hd i hi).1
      · rw [hheap _ (by unfold slotV; ao), unos hjs _ (by unfold slotV; ao) (by unfold slotV; omega)
          (by unfold slotV; omega)]
        exact (hd i hi).2
  · rw [hheap A hA, unos (by omega) A hA h1 h2]; exact h.nosig (by omega) A hA h1 h2
  · exact (h.regs.trans (uregs.trans vregs)).mono (by simp [bodyRegs])
  · refine (h.frame.trans fuv).mono (fun A _ hA => ?_)
    unfold loopW
    rcases hA with hA | hA
    · exact hA
    · unfold childW at hA
      rcases hA with hA | hA
      · left; exact hA
      · right; constructor <;> aoh
theorem LoopInv.init {c index sel w : Nat} {s0 : MachineState} (hpc : s0.pc = pcOf (leafI c))
    (hb : BodySt sk 0 index sel w s0) : LoopInv sk c index sel w s0 0 ([], []) s0 :=
  ⟨by rw [if_pos (by norm_num)]; exact hpc, by rw [if_pos (by norm_num)]; exact hb, rfl,
    fun j' hj' => absurd hj' (by omega), fun h => absurd h (by omega),
    fun _ _ _ _ _ => rfl, RegsExcept.refl _ _, Frame.refl _ _⟩
theorem child_loop (hcode : NewCodeAt im) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hc : c < 9) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 6, w / 8 ^ i.val % 8 = WCT9.wordDigit word i) (hlen : coefs.length = 54)
    {s0 : MachineState} (hcoef : CoefAt s0 coefs) {padL : Digest} (hpad : PadAt c 0 padL s0)
    (h0 : LoopInv sk c index sel w s0 0 ([], []) s0) :
    TBSim im sk s0 (128 * loopStepC) (fCoordRows index ⟨c, hc⟩ ⟨sel, hsel⟩ word coefs padL)
      (LoopInv sk c index sel w s0 128) := by
  unfold fCoordRows
  rw [List.range_eq_range']
  exact TBSim.foldlM_range' 0 128 _ _ (LoopInv sk c index sel w s0) loopStepC
    (fun j hj acc t ht => by
      simp only [Nat.zero_add]
      exact child_step hcode hc hsel hidx hw hword hlen hcoef hpad j hj acc t ht) h0
end loop
/-- One heap step of `WCT9.heapBuild` (nested FTS r1-1: heaps 2 and 3 are `wctTopHash` with pad `padR`). -/
def treeStep (index c : Nat) (padR : Digest) (nodes : Array Digest) (heap : Nat) : M (Array Digest) := do
  let value ← WCT9.wctHeapNode c index heap padR (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
  pure (nodes.set! heap value)
theorem heap_order_list : (List.range' 2 126).reverse = (List.range' 0 126).map (fun k => 127 - k) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem heapBuild_eq (index c : Nat) (padR : Digest) (leaves : List Digest) :
    WCT9.heapBuild index c padR leaves =
      (List.range' 0 126).foldlM (fun nodes k => treeStep index c padR nodes (127 - k))
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  unfold WCT9.heapBuild
  rw [heap_order_list, List.foldlM_map]
  rfl
def treeRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x28, .x29]
def treeW (A : Nat) : Prop :=
  (A = NODEW ∨ A = NODEW + 8 ∨ A = NODEW + 16 ∨ A = NODEW + 24 ∨ A = NODEW + 48 ∨ A = NODEW + 56) ∨
    (NOUTW ≤ A ∧ A < NOUTW + 32) ∨ (HEAPW + 16 ≤ A ∧ A < HEAPW + 2048) ∨ (A = NODEW + 32 ∨ A = NODEW + 40)
/-- The fold pad after `k` heap steps (nested FTS r1-1): `padR` while heaps 3 and 2 are folded, zero otherwise. -/
def treePad (k : Nat) (padR : Digest) : Digest := if 124 ≤ k ∧ k < 126 then padR else 0
structure TreeInv (c index : Nat) (padR : Digest) (s0 : MachineState) (k : Nat) (nodes : Array Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 126 then nodeI c else rI c)
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 (127 - k)
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  size : nodes.size = 256
  heap : ∀ m, 127 - k < m → m < 256 → DigAt t (HEAPW + 16 * m) (nodes.getD m 0)
  pad : DigAt t (NODEW + 32) (treePad k padR)
  regs : RegsExcept s0 t (.x18 :: treeRegs)
  frame : Frame s0 t treeW
def treeC : Nat := 32 + (8 + 25)
theorem hashInput_node (t : MachineState) {c index h : Nat} {pad L R : Digest} (hc : c < 9) (hidx : index < 2 ^ 31)
    (hh : h < 128) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODEW) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hL : DigAt t NODEW L) (m16 : t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (nodeLoN c index h))
    (m24 : t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 (if 8 ≤ h then 0 else h))
    (hP : DigAt t (NODEW + 32) pad)
    (hR : DigAt t (NODEW + 48) R) : hashInput t = toQ (pad64 (nodeIn c index h pad L R)) := by
  refine hashInput_of_words t _ 0 NODEW (by rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn_len]) h10 (by ao)
    (by ao) h11 ?_
  rw [wordsOf_node c index h pad L R hc hidx hh]
  intro k hk
  interval_cases k
  · exact hL.1
  · exact hL.2
  · exact m16
  · exact m24
  · exact hP.1
  · exact hP.2
  · exact hR.1
  · exact hR.2
theorem ntC_le (c h : Nat) : ntC c h ≤ 25 := by unfold ntC; split_ifs <;> omega
/-- Two memory words holding a digest. -/
def DigAt' (w0 w1 : Word) (d : Digest) : Prop := w0 = d.extractLsb' 0 64 ∧ w1 = d.extractLsb' 64 64
theorem treePad_zero (k : Nat) : treePad k (0 : Digest) = 0 := by unfold treePad; split_ifs <;> rfl
theorem treePad_next {c k : Nat} (hk : k < 126) {padR : Digest} (hc0 : c = 0 → padR = 0)
    (u : MachineState) (hR : PadAt c 16 padR u) (hP : DigAt u (NODEW + 32) (treePad k padR)) :
    DigAt' (ntPad c (127 - k) 0 u) (ntPad c (127 - k) 8 u) (treePad (k + 1) padR) := by
  unfold ntPad
  by_cases c0 : c = 0
  · have hp0 := hc0 c0
    subst hp0
    rw [treePad_zero] at hP
    rw [treePad_zero, if_neg (show ¬ (1 ≤ c ∧ 127 - k = 4) by omega), if_neg (show ¬ (1 ≤ c ∧ 127 - k = 2) by omega),
      if_neg (show ¬ (1 ≤ c ∧ 127 - k = 4) by omega), if_neg (show ¬ (1 ≤ c ∧ 127 - k = 2) by omega)]
    exact ⟨by rw [Nat.add_zero]; exact hP.1, hP.2⟩
  · unfold PadAt at hR
    rw [if_neg c0] at hR
    by_cases e4 : 127 - k = 4
    · have ht : treePad (k + 1) padR = padR := by unfold treePad; rw [if_pos (by omega)]
      have p4 : 1 ≤ c ∧ 127 - k = 4 := ⟨by omega, e4⟩
      simp only [if_pos p4, ht]
      exact ⟨by rw [Nat.add_zero]; exact hR.1, hR.2⟩
    · have n4 : ¬ (1 ≤ c ∧ 127 - k = 4) := fun h' => e4 h'.2
      by_cases e2 : 127 - k = 2
      · have ht : treePad (k + 1) padR = 0 := by unfold treePad; rw [if_neg (by omega)]
        have p2 : 1 ≤ c ∧ 127 - k = 2 := ⟨by omega, e2⟩
        simp only [if_neg n4, if_pos p2, ht]
        exact ⟨rfl, rfl⟩
      · have n2 : ¬ (1 ≤ c ∧ 127 - k = 2) := fun h' => e2 h'.2
        simp only [if_neg n4, if_neg n2]
        have ht : treePad (k + 1) padR = treePad k padR := by
          unfold treePad
          by_cases h1 : 124 ≤ k ∧ k < 126
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (by omega)]
        rw [ht]
        exact ⟨by rw [Nat.add_zero]; exact hP.1, hP.2⟩
section tree
variable {im : Image} {sk : BitVec 256}
theorem tree_step (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    {padR : Digest} (hc0 : c = 0 → padR = 0) (hR0 : PadAt c 16 padR s0)
    (k : Nat) (hk : k < 126) (nodes : Array Digest) (t : MachineState) (h : TreeInv c index padR s0 k nodes t) :
    TBSim im sk t treeC (treeStep index c padR nodes (127 - k)) (TreeInv c index padR s0 (k + 1)) := by
  have hpc : t.pc = pcOf (nodeI c) := by rw [h.pc, if_pos hk]
  have hRt : PadAt c 16 padR t := hR0.frame hc (by norm_num) h.frame (fun A h1 h2 hw => by unfold treeW at hw; aoh)
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, n0, n8, n48, n56, n16, n24, r1, f1⟩ :=
    step_N hcode hc (by omega : 1 ≤ 127 - k) (by omega) t hpc h.x18 h.x22 hidx
  have hL : DigAt t1 NODEW (nodes.getD (2 * (127 - k)) 0) := by
    have := h.heap (2 * (127 - k)) (by omega) (by omega)
    exact ⟨by rw [n0, show HEAPW + 32 * (127 - k) = HEAPW + 16 * (2 * (127 - k)) by ring]; exact this.1,
      by rw [n8, show HEAPW + 32 * (127 - k) + 8 = HEAPW + 16 * (2 * (127 - k)) + 8 by ring]; exact this.2⟩
  have hR : DigAt t1 (NODEW + 48) (nodes.getD (2 * (127 - k) + 1) 0) := by
    have := h.heap (2 * (127 - k) + 1) (by omega) (by omega)
    exact ⟨by rw [n48, show HEAPW + 32 * (127 - k) + 16 = HEAPW + 16 * (2 * (127 - k) + 1) by ring]; exact this.1,
      by rw [show NODEW + 48 + 8 = NODEW + 56 by ao, n56,
        show HEAPW + 32 * (127 - k) + 24 = HEAPW + 16 * (2 * (127 - k) + 1) + 8 by ring]; exact this.2⟩
  have hP1 : DigAt t1 (NODEW + 32) (treePad k padR) := h.pad.frame f1 (by ao) (by intro h'; aoh) (by intro h'; aoh)
  have hq := hashInput_node t1 hc hidx (by omega : 127 - k < 128) x10 x11 hL n16 n24 hP1 hR
  have hx5 : t1.getReg .x5 = 0 := by rw [r1.get (by simp)]; exact h.x5
  have hR1 : PadAt c 16 padR t1 := hRt.frame hc (by norm_num) f1 (fun A h1 h2 hw => by aoh)
  -- the post-hash block and the invariant, for either output half
  have tail : ∀ (a : BitVec 256) (v : Digest), DigAt (writeHash t1 a) (NOUTW + hiOff (127 - k)) v →
      TBSim im sk (writeHash t1 a) 25 (pure (nodes.set! (127 - k) v)) (TreeInv c index padR s0 (k + 1)) := by
    intro a v hv
    set u := writeHash t1 a with hu
    have fu := Frame.writeHash t1 a NOUTW x12 (by ao)
    have hntpc : u.pc = pcOf (ntI c) := by
      rw [hu, pc_writeHash, p1]
      have : 1 ≤ ntI c := by have : ∀ c, c < 9 → 1 ≤ ntI c := by decide +kernel
                             exact this c hc
      exact pcOf_pred4 _ this
    have u18 : u.getReg .x18 = BitVec.ofNat 64 (127 - k) := by rw [hu, getReg_writeHash, r1.get (by simp)]; exact h.x18
    obtain ⟨t2, s2, q1, q2, x18', w0, w8, w32, w40, r2, f2⟩ :=
      step_NT hcode hc (by omega : 2 ≤ 127 - k) (by omega) u hntpc u18
    have hPu : DigAt u (NODEW + 32) (treePad k padR) := hP1.frame fu (by ao) (by intro h'; aoh) (by intro h'; aoh)
    have hRu : PadAt c 16 padR u := hR1.frame hc (by norm_num) fu (fun A h1 h2 hw => by aoh)
    have hnext := treePad_next hk hc0 u hRu hPu
    refine (TBSim.pure_steps' s2 ⟨?_, ?_, ?_, ?_, ?_, fun m hm1 hm2 => ?_, ?_, ?_, ?_⟩).mono (ntC_le c _)
      (fun _ _ h => h)
    · by_cases hk1 : k + 1 < 126
      · rw [if_pos hk1]; exact q1 (by omega)
      · rw [if_neg hk1]; exact q2 (by omega)
    · rw [r2.get (by simp), hu, getReg_writeHash, r1.get (by simp)]; exact h.x5
    · rw [x18', show 127 - k - 1 = 127 - (k + 1) by omega]
    · rw [r2.get (by simp), hu, getReg_writeHash, r1.get (by simp)]; exact h.x22
    · simp [h.size]
    · by_cases hmk : m = 127 - k
      · subst hmk
        rw [WCT9.getD_set_self _ _ _ (by rw [h.size]; omega)]
        exact ⟨by rw [w0]; exact hv.1, by rw [w8]; exact hv.2⟩
      · rw [WCT9.getD_set_other _ _ _ _ (fun he => hmk he.symm)]
        have hd := h.heap m (by omega) hm2
        have g : ∀ A, (A = HEAPW + 16 * m ∨ A = HEAPW + 16 * m + 8) →
            t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
          intro A hA
          rw [f2.get (by aoh) (by intro h'; aoh), fu.get (by aoh) (by intro h'; aoh),
            f1.get (by aoh) (by intro h'; aoh)]
        exact ⟨by rw [g _ (Or.inl rfl)]; exact hd.1, by rw [g _ (Or.inr rfl)]; exact hd.2⟩
    · exact ⟨by rw [w32]; exact hnext.1, by rw [show NODEW + 32 + 8 = NODEW + 40 by ao, w40]; exact hnext.2⟩
    · exact (h.regs.trans ((r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])).trans r2)).mono
        (by simp [treeRegs])
    · refine (((h.frame.trans f1).trans fu).trans f2).mono (fun A _ hA => ?_)
      unfold treeW
      rcases hA with ((hA | hA) | hA) | hA
      · exact hA
      · left; rcases hA with h' | h' | h' | h' | h' | h' <;> simp [h']
      · right; left; exact hA
      · rcases hA with h' | h' | h' | h'
        · right; right; left; subst h'; constructor <;> omega
        · right; right; left; subst h'; constructor <;> omega
        · right; right; right; left; exact h'
        · right; right; right; right; exact h'
  unfold treeStep WCT9.wctHeapNode
  by_cases h4 : 127 - k < 4
  · rw [if_pos h4, topHash_eq]
    simp only [bind_assoc, pure_bind]
    have hpk : treePad k padR = padR := by unfold treePad; rw [if_pos (by omega)]
    rw [hpk] at hq
    refine (TBSim.steps s1 (TBSim.publicHash_bind' (W := 25) e1 hx5
      (hashArgs_const t1 NODEW 64 NOUTW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => tail a _ ?_))).mono (by rw [blocks64 _ (nodeIn_len _ _ _ _ _ _)]; unfold treeC; split <;> omega)
      (fun _ _ h => h)
    have : hiOff (127 - k) = 16 := by unfold hiOff; rw [if_pos h4]
    rw [this]
    exact DigAt.writeHash_hi t1 a NOUTW x12 (by ao)
  · rw [if_neg h4, nodeHash_eq]
    have hpk : treePad k padR = 0 := by unfold treePad; rw [if_neg (by omega)]
    rw [hpk] at hq
    refine (TBSim.steps s1 (TBSim.shortHash_bind' (W := 25) e1 hx5
      (hashArgs_const t1 NODEW 64 NOUTW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => tail a _ ?_))).mono (by rw [blocks64 _ (nodeIn_len _ _ _ _ _ _)]; unfold treeC; split <;> omega)
      (fun _ _ h => h)
    have : hiOff (127 - k) = 0 := by unfold hiOff; rw [if_neg h4]
    rw [this, Nat.add_zero]
    exact DigAt.writeHash_lo t1 a NOUTW x12 (by ao)
theorem tree_loop (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    {padR : Digest} (hc0 : c = 0 → padR = 0) (hR0 : PadAt c 16 padR s0)
    {leaves : List Digest} (h0 : TreeInv c index padR s0 0 ((List.replicate 128 (0 : Digest) ++ leaves).toArray) s0) :
    TBSim im sk s0 (126 * treeC) (WCT9.heapBuild index c padR leaves) (TreeInv c index padR s0 126) := by
  rw [heapBuild_eq]
  exact TBSim.foldlM_range' 0 126 _ _ (TreeInv c index padR s0) treeC
    (fun k hk nodes t ht => by
      simp only [Nat.zero_add]
      exact tree_step hcode hc hidx hc0 hR0 k hk nodes t ht) h0
end tree
end ClaudeWCT.W9.Machine.Sign
end

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}
variable {sk : BitVec 256}
theorem step_unit (hcode : Fetch im) {c i j index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hc : c < 9) (hi : i < 6) (hj : j < 128) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 6, w / 8 ^ i.val % 8 = WCT9.wordDigit word i) (hlen : coefs.length = 54)
    {rows : List Digest × List Digest} {s : MachineState} (hpc : s.pc = pcOf (qI c i))
    (hb : BodySt sk j index sel w s) (hr : RowsAt c j sel i rows s) (hcoef : CoefAt s coefs) :
    TBSim im sk s stepC (fChildStep index c j word coefs rows ⟨i, hi⟩) (fun rows' t =>
      t.pc = pcOf (lcEnd c i) ∧ BodySt sk j index sel w t ∧ RowsAt c j sel (i + 1) rows' t ∧
        RegsExcept s t bodyRegs ∧ Frame s t (bodyW c) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) ∧
        t.getReg .x29 = BitVec.ofNat 64 LEAFW) := by
  have hdig : WCT9.wordDigit word ⟨i, hi⟩ = w / 8 ^ i % 8 := (hword ⟨i, hi⟩).symm
  have hd4 : w / 8 ^ i % 8 ≤ 4 := by rw [← hdig]; exact WCT9.wordDigit_le_four word ⟨i, hi⟩
  rw [fChildStep_eq, hdig]
  obtain ⟨t1, s1, p1, x1, x6, r1, f1⟩ := step_Q hcode hc hi s hpc hb.x18 hj
  obtain ⟨t2, n2, c2, s2, hc2, p2, seed2, r2, f2⟩ :=
    horn_run hcode t1 p1 (d := 6 * j + i + 1) (by omega) x6 hlen (hcoef.frame f1 (fun _ _ _ h => h))
  change c2 ≤ Sign.hornC at hc2
  have p2' : t2.pc = pcOf (qI c i + 5) := by rw [p2, x1, pcOf_ret]
  have g2 : ∀ r, r ∉ [Reg.x1, .x6] ++ hornRegs → t2.getReg r = s.getReg r := r1.trans r2
  obtain ⟨t3, s3, p3, x26, m16, m24, r3, f3⟩ := step_S hcode hc hi t2 p2'
    (by rw [g2 _ (by simp [hornRegs])]; exact hb.x18) (by rw [g2 _ (by simp [hornRegs])]; exact hb.x22) hj
    (by rw [g2 _ (by simp [hornRegs])]; exact hb.x25) hw hd4
  have g3 : ∀ r, r ∉ ([Reg.x1, .x6] ++ hornRegs) ++ [.x6, .x7, .x26, .x29] → t3.getReg r = s.getReg r :=
    (r1.trans r2).trans r3
  have f13 : Frame s t3 (fun A => (False ∨ (A = CHAINW + 48 ∨ A = CHAINW + 56)) ∨
      (A = CHAINW + 24 ∨ A = CHAINW + 16)) := (f1.trans f2).trans f3
  have m3 : ∀ A, A < 2 ^ 64 → A ≠ CHAINW + 48 → A ≠ CHAINW + 56 → A ≠ CHAINW + 24 → A ≠ CHAINW + 16 →
      t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 h3 h4 =>
    f13.get hA (by simp [h1, h2, h3, h4])
  have hseed : DigAt t3 (CHAINW + 48) (WCT9.ftsFamilySeed coefs j i) := by
    have : DigAt t2 (CHAINW + 48) (WCT9.ftsFamilySeed coefs j i) := by
      unfold WCT9.ftsFamilySeed WCT9.ftsPoint WCT9.ftsOrdinal; exact seed2
    exact this.frame f3 (by ao) (by ao) (by ao)
  have hst : ChkSt c i j index sel w (w / 8 ^ i % 8) 4 [WCT9.ftsFamilySeed coefs j i] t3 t3 :=
    { pc := p3
      x5 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x5
      x18 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x18
      x22 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x22
      x24 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x24
      x25 := by rw [g3 _ (by simp [hornRegs])]; exact hb.x25
      x26 := x26
      len := rfl
      val := hseed
      h16 := m16
      h24 := m24
      z0 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z0
      z8 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z8
      z32 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z32
      z40 := by rw [m3 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hb.z40
      op := fun _ h => absurd h (by omega)
      regs := RegsExcept.refl _ _
      frame := Frame.refl _ _
      nosel := fun _ _ _ _ _ => rfl }
  have hk3 : (if c = 0 then 17 else 15) ≤ 17 := by split <;> omega
  refine (TBSim.steps ((s1.trans s2).trans s3) (TBSim.bind (W₂ := 0)
    (chain_from hcode hc hi hj hsel hidx hw hd4 4 le_rfl _ t3 hst) (fun r t ht => ?_))).mono
    (by unfold stepC; omega) (fun _ _ h => h)
  obtain ⟨tpc, tleaf, tsig, tregs, tframe, tnos, tx29⟩ := ht
  have fst : Frame s t (bodyW c) := (f13.trans tframe).mono (fun A _ hA => by
    rcases hA with ((hA | hA) | hA) | hA
    · exact hA.elim
    · unfold bodyW; right; right; right; left; rcases hA with rfl | rfl <;> constructor <;> ao
    · unfold bodyW; right; right; left; rcases hA with rfl | rfl <;> constructor <;> ao
    · exact chainW_bodyW hi hA)
  have rst : RegsExcept s t bodyRegs := (((r1.trans r2).trans r3).trans tregs).mono
    (by simp [hornRegs, chainRegs, bodyRegs])
  refine TBSim.pure ⟨tpc, hb.of_body hc rst (fun _ h => h) fst (fun _ h => h), ?_, rst, fst, ?_, tx29⟩
  · have hr3 : RowsAt c j sel i rows t3 := hr.frame hc (by omega) f13 (fun i' hi' => by
      have := leafOff_lt i' (by omega)
      unfold slotV
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; simp only [false_or] at h; rcases h with (h | h) | (h | h) <;> aoh))
    exact (hr3.frame hc (by omega) tframe (fun i' hi' => chainW_other hc hi (by omega) (by omega))).snoc tleaf tsig
  · intro hjs A hA h1 h2
    rw [tnos hjs A hA h1 h2, m3 A hA (by unfold slotV at h1 h2; aoh) (by unfold slotV at h1 h2; aoh)
      (by unfold slotV at h1 h2; aoh) (by unfold slotV at h1 h2; aoh)]
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {im : Image} {sk : BitVec 256}
/-- Compute six complete FTS chains and retain exactly the selected openings, ending before the new leaf hook. -/
theorem rows_unit (hcode : Fetch im) {c j index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hc : c < 9) (hj : j < 128) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 6, w / 8 ^ i.val % 8 = WCT9.wordDigit word i) (hlen : coefs.length = 54) {s : MachineState}
    (hpc : s.pc = pcOf (leafI c)) (hb : BodySt sk j index sel w s) (hcoef : CoefAt s coefs) :
    TBSim im sk s (6 * stepC) (fChildRows index c j word coefs) (StepInv sk c j index sel w s 6) := by
  rw [fChildRows_fold]
  have h0 : StepInv sk c j index sel w s 0 ([], []) s :=
    ⟨by rw [if_pos (by norm_num), ← leafI_qI c hc]; exact hpc, hb,
      ⟨rfl, rfl, fun i hi => absurd hi (by omega), fun _ i hi => absurd hi (by omega)⟩,
      RegsExcept.refl _ _, Frame.refl _ _, fun _ _ _ _ _ => rfl, fun h => absurd h (by omega)⟩
  refine TBSim.foldlM_range' 0 6 _ _ (StepInv sk c j index sel w s) stepC ?_ h0
  intro k hk rows t ht
  simp only [Nat.zero_add, dif_pos hk]
  have hpc' : t.pc = pcOf (qI c k) := by rw [ht.pc, if_pos hk]
  refine (step_unit hcode hc hk hj hsel hidx hw hword hlen hpc' ht.body ht.rws
    (hcoef.frame ht.frame (fun A h1 h2 => coef_not_bodyW hc h1 h2))).mono le_rfl (fun rows' u hu => ?_)
  obtain ⟨upc, ub, ur, ureg, ufr, unos, ux29⟩ := hu
  refine ⟨?_, ub, ur, (ht.regs.trans ureg).mono (by simp [bodyRegs]),
    (ht.frame.trans ufr).mono (fun A _ hA => by rcases hA with hA | hA <;> exact hA),
    fun hjs A hA h1 h2 => by rw [unos hjs A hA h1 h2, ht.nos hjs A hA h1 h2], fun _ => ux29⟩
  rw [upc]; unfold lcEnd
  by_cases h6 : k = 5
  · subst h6; rw [if_pos rfl, if_neg (by omega)]
  · rw [if_neg h6, if_pos (by omega)]
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def coefStepC : Nat := 8+10
def coefRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x29]
def coefW (A : Nat) : Prop := A = PRIVW + 16 ∨ A = PRIVW + 24 ∨ (COEF ≤ A ∧ A < COEF + 864)
structure CoefInv (im : Image) (c index : Nat) (s0 : MachineState) (j : Nat) (acc : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (if j < 27 then ecI c else leafI c)
  run : j < 27 → fetch im t = some (.base .ECALL) ∧ t.getReg .x7 = BitVec.ofNat 64 j ∧
    t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
    t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * j) ∧
    t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)
  done : 27 ≤ j → t.getReg .x18 = BitVec.ofNat 64 0
  p16 : t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c)
  len : acc.length = 2 * j
  coef : ∀ k < 2 * j, DigAt t (COEF + 16 * k) (acc.getD k 0)
  regs : RegsExcept s0 t coefRegs
  frame : Frame s0 t coefW
theorem paI_ecI : ∀ c, c < 9 → ecI c + 1 = paI c := by decide +kernel
theorem getD_append2 (acc : List Digest) (x y : Digest) (k : Nat) (hk : k < acc.length + 2) :
    (acc ++ [x, y]).getD k 0 = if k < acc.length then acc.getD k 0 else if k = acc.length then x else y := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : k - acc.length = 1 := by omega
    simp [this]
section coefs
variable {im : Image} {sk : BitVec 256}
theorem coef_step (hcode : Fetch im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    (h5 : s0.getReg .x5 = 0) (h22 : s0.getReg .x22 = BitVec.ofNat 64 index)
    (p0 : s0.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64)
    (p8 : s0.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64)
    (p32 : s0.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64)
    (p40 : s0.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64)
    (p48 : s0.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0) (p56 : s0.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0)
    (j : Nat) (hj : j < 27) (acc : List Digest) (t : MachineState) (h : CoefInv im c index s0 j acc t) :
    TBSim im sk t coefStepC (coefStep index c acc (0 + j)) (CoefInv im c index s0 (j + 1)) := by
  obtain ⟨ec, x7, x10, x11, x12, m24⟩ := h.run hj
  have gm : ∀ A, A < 2 ^ 64 → ¬ coefW A → t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => h.frame.get hA hn
  have nw : ∀ A, (A = PRIVW ∨ A = PRIVW + 8 ∨ A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ A = PRIVW + 48 ∨
      A = PRIVW + 56) → ¬ coefW A := by
    intro A hA hw; unfold coefW at hw; simp only [PRIVW, COEF] at *; omega
  have hq := hashInput_priv t sk hc (by omega : index < 2 ^ 32) (by omega : j < 2 ^ 32) x10 x11
    (by rw [gm _ (by ao) (nw _ (by simp))]; exact p0) (by rw [gm _ (by ao) (nw _ (by simp))]; exact p8) h.p16 m24
    (by rw [gm _ (by ao) (nw _ (by simp))]; exact p32) (by rw [gm _ (by ao) (nw _ (by simp))]; exact p40)
    (by rw [gm _ (by ao) (nw _ (by simp))]; exact p48) (by rw [gm _ (by ao) (nw _ (by simp))]; exact p56)
  have t5 : t.getReg .x5 = 0 := by rw [h.regs.get (by simp [coefRegs])]; exact h5
  have t22 : t.getReg .x22 = BitVec.ofNat 64 index := by rw [h.regs.get (by simp [coefRegs])]; exact h22
  unfold coefStep WCT9.ftsSeedPair
  simp only [Nat.zero_add]
  refine (TBSim.privatePair_bind' (W := 10) ec t5
    (hashArgs_const t PRIVW 64 (COEF + 32 * j) x10 x11 x12 (by ao) (by norm_num) (by ao)
      (by simp only [COEF]; omega) (by simp only [COEF]; omega)) hq (fun a => ?_)).mono
    (by unfold coefStepC; omega) (fun _ _ h => h)
  set u := writeHash t a with hu
  have fu := Frame.writeHash t a (COEF + 32 * j) x12 (by simp only [COEF]; omega)
  have dlo := DigAt.writeHash_lo t a (COEF + 32 * j) x12 (by simp only [COEF]; omega)
  have dhi := DigAt.writeHash_hi t a (COEF + 32 * j) x12 (by simp only [COEF]; omega)
  have upc : u.pc = pcOf (paI c) := by
    rw [hu, pc_writeHash, h.pc, if_pos hj, pcOf_add4, paI_ecI c hc]
  have hlen : (acc ++ [a.extractLsb' 0 128, a.extractLsb' 128 128]).length = 2 * (j + 1) := by
    simp [h.len]; omega
  -- facts common to both exits, at `u`
  have ucoef : ∀ k < 2 * (j + 1), DigAt u (COEF + 16 * k)
      ((acc ++ [a.extractLsb' 0 128, a.extractLsb' 128 128]).getD k 0) := by
    intro k hk
    rw [getD_append2 _ _ _ k (by rw [h.len]; omega), h.len]
    split_ifs with h1 h2
    · exact (h.coef k h1).frame fu (by simp only [COEF]; omega) (by simp only [COEF]; omega)
        (by simp only [COEF]; omega)
    · subst h2; rw [show COEF + 16 * (2 * j) = COEF + 32 * j by omega]; exact dlo
    · rw [show k = 2 * j + 1 by omega, show COEF + 16 * (2 * j + 1) = COEF + 32 * j + 16 by omega]; exact dhi
  have up16 : u.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) := by
    rw [fu.get (by ao) (by simp only [PRIVW, COEF]; omega)]; exact h.p16
  have uregs : RegsExcept s0 u coefRegs :=
    (h.regs.trans (fun x _ => getReg_writeHash t a x : RegsExcept t u [])).mono (by simp)
  have uframe : Frame s0 u coefW := (h.frame.trans fu).mono (fun A _ hA => by
    rcases hA with hA | hA
    · exact hA
    · unfold coefW; right; right; simp only [COEF] at *; omega)
  by_cases hj1 : j + 1 < 27
  · obtain ⟨v, sv, ev, vpc, v7, v10, v11, v12, v24, vregs, vframe⟩ := step_CLc hcode hc u upc
      (by rw [hu, getReg_writeHash]; exact x7) hj1 (by rw [hu, getReg_writeHash]; exact x12)
      (by rw [hu, getReg_writeHash]; exact t22) (by omega)
    refine TBSim.pure_steps' sv ⟨by rw [if_pos hj1]; exact vpc, fun _ => ⟨ev, v7, v10, v11, ?_, v24⟩,
      fun h' => absurd h' (by omega), ?_, hlen, fun k hk => (ucoef k hk).frame vframe (by simp only [COEF]; omega)
        (by simp only [PRIVW, COEF]; omega) (by simp only [PRIVW, COEF]; omega),
      (uregs.trans vregs).mono (by simp [coefRegs]), (uframe.trans vframe).mono (fun A _ hA => by
        rcases hA with hA | hA
        · exact hA
        · unfold coefW; right; left; exact hA)⟩
    · rw [v12, show COEF + 32 * j + 32 = COEF + 32 * (j + 1) by omega]
    · rw [vframe.get (by ao) (by simp only [PRIVW]; omega)]; exact up16
  · obtain ⟨v, sv, vpc, v18, vregs, vframe⟩ := step_CLx hcode hc u upc
      (by rw [hu, getReg_writeHash]; exact x7) (by omega)
    refine (TBSim.pure_steps' sv ⟨by rw [if_neg hj1]; exact vpc, fun h' => absurd h' hj1, fun _ => v18, ?_, hlen,
      fun k hk => (ucoef k hk).frame vframe (by simp only [COEF]; omega) id id,
      (uregs.trans vregs).mono (by simp [coefRegs]), (uframe.trans vframe).mono (fun A _ hA => by
        rcases hA with hA | hA
        · exact hA
        · exact hA.elim)⟩).mono (by norm_num) (fun _ _ h => h)
    rw [vframe.get (by ao) id]; exact up16
end coefs

end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {im : Image} {sk : BitVec 256}
/-- The unchanged coefficient prologue accepts any prior raw-child counter. -/
theorem coefs_unit (hcode : Fetch im) {c old index sel w : Nat} (hc:c<9) (hidx:index<2^31)
    {s : MachineState} (hpc:s.pc=pcOf (lwuI c+1)) (hb:BodySt sk old index sel w s) :
    TBSim im sk s (14+27*coefStepC) (WCT9.ftsCoefs index c) (fun coefs t =>
      t.pc=pcOf (leafI c) ∧ BodySt sk 0 index sel w t ∧ coefs.length=54 ∧ CoefAt t coefs ∧
      RegsExcept s t coefRegs ∧ Frame s t coefW) := by
  obtain ⟨u,su,ec,upc,x7,x10,x11,x12,m16,m24,ru,fu⟩ := step_Z hcode hc s hpc hb.x22
  have h0 : CoefInv im c index s 0 [] u :=
    ⟨by rw [if_pos (by decide)]; exact upc,fun _ => ⟨ec,x7,x10,x11,x12,m24⟩,
     fun h => absurd h (by omega),m16,rfl,fun k hk=>absurd hk (by omega),
     ru.mono (by simp [coefRegs]),fu.mono (fun A _ hA=>by unfold coefW;rcases hA with h|h<;>simp[h])⟩
  rw [ftsCoefs_eq]
  refine (TBSim.steps su
    (TBSim.foldlM_range' 0 27 (coefStep index c) [] (CoefInv im c index s) coefStepC
      (fun j hj acc t ht=>coef_step hcode hc hidx hb.x5 hb.x22 hb.p0 hb.p8 hb.p32 hb.p40 hb.p48 hb.p56 j hj acc t ht) h0)).mono
      (by omega) (fun coefs t ht=>?_)
  have hp:t.pc=pcOf (leafI c) := by rw[ht.pc,if_neg (by omega)]
  have hr:=ht.regs
  have hf:=ht.frame
  have hmem : ∀ A, A<2^64 → ¬coefW A → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn=>hf.get hA hn
  refine ⟨hp,?_,ht.len,ht.coef,hr,hf⟩
  refine ⟨by rw[hr.get (by simp[coefRegs])];exact hb.x5,ht.done (by omega),
    by rw[hr.get (by simp[coefRegs])];exact hb.x22,
    by rw[hr.get (by simp[coefRegs])];exact hb.x24,
    by rw[hr.get (by simp[coefRegs])];exact hb.x25,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.p0)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.p8)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.p32)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.p40)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.p48)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.p56)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.z0)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.z8)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.z32)
    | (rw[hmem _ (by ao) (by unfold coefW COEF;ao)];exact hb.z40)
end ClaudeWCT.W9.Machine.Sign.SharedReuse


namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest pad64)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem physical_lt (c : Nat) {j : Nat} (hj:j<128) : physical c j<128 := by
  unfold physical
  split <;> omega

theorem step_hook {im : Image} {c : Nat} (hlook:LookOK im (hookLook c)) (hc:c<9)
    (s : MachineState) (hpc:s.pc=pcOf (lI c)) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf (entry c) ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,_⟩:=run_pres hlook (optBeq_eq (hook_run c hc)) s hpc (no_obl s) (no_br s)
  exact ⟨_,hs,rfl,pres_regsExcept _ _ _ _ _ _ _ s,fun _ _ _=>rfl⟩

def hashW (c j : Nat) (A : Nat) : Prop := writes A ∨
  HEAPW+16*(128+physical c j) ≤ A ∧ A<HEAPW+16*(128+physical c j)+32

/-- C1: the leaf of physical child `p` uses the HIGH half of its answer iff `128 + p` is even. -/
theorem ftsHighHeap_leaf (p : Nat) : WCT9.ftsHighHeap (128+p)=decide (p%2=0) := by
  by_cases hx:p%2=0
  · rw[decide_eq_true hx];exact (WCT9.ftsHighHeap_iff (by omega)).mpr ⟨by omega,by omega⟩
  · rw[decide_eq_false hx]
    cases hy:WCT9.ftsHighHeap (128+p)
    · rfl
    · exact absurd ((WCT9.ftsHighHeap_iff (by omega)).mp hy).2 (by omega)

/-- C1: after the leaf `ecall` the answer is at `a2 = HEAPW + 16 (128 + p)`; the leaf value (`leafHashH`) is its
LOW half for odd `p` and its HIGH half (at `a2 + 16`) for even `p`. The hook stub then moves it to `a2`. -/
theorem hash_unit {im : Image} {sk : BitVec 256} {c j index sel w : Nat} {pad : Digest}
    (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128) (hidx:index<2^31)
    (rows : List Digest × List Digest) {s : MachineState} (hpc:s.pc=pcOf (entry c))
    (hb:BodySt sk j index sel w s) (hr:RowsAt c j sel 6 rows s) (hp:PadAt c j pad s) :
    TBSim im sk s 48 (WCT9.leafHashH (128+physical c j) index c j pad rows.1) (fun root t=>
      t.pc=pcOf (hashPc c)+4 ∧ BodySt sk j index sel w t ∧
      t.getReg .x12=BitVec.ofNat 64 (HEAPW+16*(128+physical c j)) ∧
      (physical c j%2=1 → DigAt t (HEAPW+16*(128+physical c j)) root) ∧
      (physical c j%2=0 → DigAt t (HEAPW+16*(128+physical c j)+16) root) ∧
      (j=sel → ∀i,i<6 → DigAt t (slotV c i) (rows.2.getD i 0)) ∧
      RegsExcept s t bodyRegs ∧ Frame s t (hashW c j)) := by
  obtain ⟨u,su,ec,upc,x10,x11,x12,m16,m24,hpad,ru,fu⟩:=step_leaf hlook hc hj s hpc hb.x18 hb.x22 hp
  have hphys:=physical_lt c hj
  have hrows:RowsAt c j sel 6 rows u:=hr.frame hc (by omega) fu (fun i hi=>by
    have hl:=leafOff_lt i (by omega)
    unfold writes slotV leafOff
    refine ⟨?_,?_,?_,?_⟩ <;> (try split_ifs) <;> ao)
  have hub:BodySt sk j index sel w u:=hb.of ru (by simp) fu (by
    unfold writes
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> ao)
  have hq:=hashInput_leaf u rows.1 hrows.len1 hc hidx hj x10 x11 hrows.leaf m16 m24 hpad.1 hpad.2
  have hbl:(toQ (pad64 (leafIn index c j pad rows.1))).blocks=2:=by
    rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ _ hrows.len1]),
      blocks_toQ ⟨by rw [leafIn_len _ _ _ _ _ hrows.len1];norm_num,
        by rw [leafIn_len _ _ _ _ _ hrows.len1]⟩,leafIn_len _ _ _ _ _ hrows.len1]
  have hargs:=hashArgs_const u LEAFW 128 (HEAPW+16*(128+physical c j)) x10 x11 x12
    (by ao) (by norm_num) (by ao) (by ao) (by ao)
  have post:∀(a:BitVec 256) (root:Digest),
      root=(if physical c j%2=0 then a.extractLsb' 128 128 else a.extractLsb' 0 128) →
      (writeHash u a).pc=pcOf (hashPc c)+4 ∧ BodySt sk j index sel w (writeHash u a) ∧
      (writeHash u a).getReg .x12=BitVec.ofNat 64 (HEAPW+16*(128+physical c j)) ∧
      (physical c j%2=1 → DigAt (writeHash u a) (HEAPW+16*(128+physical c j)) root) ∧
      (physical c j%2=0 → DigAt (writeHash u a) (HEAPW+16*(128+physical c j)+16) root) ∧
      (j=sel → ∀i,i<6 → DigAt (writeHash u a) (slotV c i) (rows.2.getD i 0)) ∧
      RegsExcept s (writeHash u a) bodyRegs ∧ Frame s (writeHash u a) (hashW c j) := by
    intro a root hroot
    have fh:=Frame.writeHash u a (HEAPW+16*(128+physical c j)) x12 (by ao)
    refine ⟨by rw[pc_writeHash,upc],?_,by rw[getReg_writeHash];exact x12,fun ho=>?_,fun he=>?_,?_,?_,?_⟩
    · exact hub.of (fun x _=>getReg_writeHash u a x : RegsExcept u (writeHash u a) []) (by simp) fh
        (by refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> ao)
    · rw[hroot,if_neg (by omega)]
      exact DigAt.writeHash_lo u a _ x12 (by ao)
    · rw[hroot,if_pos he]
      exact DigAt.writeHash_hi u a _ x12 (by ao)
    · intro hjs i hi
      exact (hrows.sig hjs i hi).frame fh (by unfold slotV;ao) (by unfold slotV;ao) (by unfold slotV;ao)
    · exact (ru.trans (fun x _=>getReg_writeHash u a x : RegsExcept u (writeHash u a) [])).mono (by simp[bodyRegs])
    · exact (fu.trans fh).mono (fun _ _ h=>h)
  rw [leafHashH_eq',WCT9.ftsHash_eq,ftsHighHeap_leaf]
  by_cases hev:physical c j%2=0
  · have hd:decide (physical c j%2=0)=true:=decide_eq_true hev
    rw[if_pos hd]
    unfold WCT9.highHash
    refine (TBSim.steps su (TBSim.publicHash_bind' (W:=0) (f:=fun o=>pure (o.extractLsb' 128 128)) ec hub.x5
      hargs hq (fun a=>TBSim.pure ?_))).mono
      (by rw[hbl];unfold cycles;split_ifs <;> omega) (fun _ _ h=>h)
    exact post a _ (by rw[if_pos hev])
  · have hd:¬decide (physical c j%2=0)=true:=fun hx=>hev (of_decide_eq_true hx)
    rw[if_neg hd]
    refine (TBSim.steps su (TBSim.shortHash_bind' (W:=0) (f:=fun root=>pure root) ec hub.x5 hargs hq
      (fun a=>TBSim.pure ?_))).mono
      (by rw[hbl];unfold cycles;split_ifs <;> omega) (fun _ _ h=>h)
    exact post a _ (by rw[if_neg hev])
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem padBase_bound {c j : Nat} (hc:c<9) (hj:j<128) : padBase c j+16<2^64 := by
  unfold padBase
  split_ifs <;> (try simp only[FORW]) <;> omega

theorem PadAt.frame {c j : Nat} {pad : Digest} {s t : MachineState} {W : Nat→Prop}
    (hp:PadAt c j pad s) (hc:c<9) (hj:j<128) (hf:Frame s t W)
    (h0:¬W (padBase c j)) (h8:¬W (padBase c j+8)) : PadAt c j pad t := by
  unfold PadAt at hp ⊢
  split_ifs at hp ⊢ with h
  · exact hp
  · exact hp.frame hf (by have:=padBase_bound hc hj;omega) h0 h8

theorem pad_not_bodyW {c j : Nat} (hc:c<9) (hj:j<128) (off : Nat) (ho:off=0∨off=8) :
    ¬bodyW c (padBase c j+off) := by
  unfold padBase
  split_ifs <;> rcases ho with rfl|rfl <;> unfold bodyW slotV <;> ao

def childW (c j : Nat) (A : Nat) : Prop := bodyW c A ∨
  HEAPW+16*(128+physical c j)≤A ∧ A<HEAPW+16*(128+physical c j)+32

theorem child_unit {im : Image} {sk : BitVec 256} (hfetch:SharedReuse.Fetch im)
    {c j index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest} {pad : Digest}
    (hlook:LookOK im (look c)) (hhook:LookOK im (hookLook c))
    (hc:c<9) (hj:j<128) (hsel:sel<128) (hidx:index<2^31) (hw:w<2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=54)
    {s : MachineState} (hpc:s.pc=pcOf (leafI c)) (hb:BodySt sk j index sel w s)
    (hcoef:CoefAt s coefs) (hpad:PadAt c j pad s) :
    TBSim im sk s (6*stepC+49) (WCT9.buildChildH (128+physical c j) index c j word coefs pad) (fun rv t=>
      t.pc=pcOf (hashPc c)+4 ∧ BodySt sk j index sel w t ∧
      t.getReg .x12=BitVec.ofNat 64 (HEAPW+16*(128+physical c j)) ∧
      (physical c j%2=1 → DigAt t (HEAPW+16*(128+physical c j)) rv.1) ∧
      (physical c j%2=0 → DigAt t (HEAPW+16*(128+physical c j)+16) rv.1) ∧
      (j=sel → rv.2.length=6 ∧ ∀i,i<6→DigAt t (slotV c i) (rv.2.getD i 0)) ∧
      RegsExcept s t bodyRegs ∧ Frame s t (childW c j) ∧
      (j≠sel → ∀A,A<2^64→slotV c 0≤A→A<slotV c 6→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))) := by
  rw[buildChildH_factorS]
  refine TBSim.bind (W₂:=49) (SharedReuse.rows_unit hfetch hc hj hsel hidx hw hword hlen hpc hb hcoef) (fun rows t4 h4=>?_)
  have p4:t4.pc=pcOf (lI c):=by rw[h4.pc,if_neg (by omega)]
  obtain ⟨t5,s5,p5,r5,f5⟩:=step_hook hhook hc t4 p4
  have hb5:BodySt sk j index sel w t5:=h4.body.of r5 (by simp) f5 (by simp)
  have hr5:RowsAt c j sel 6 rows t5:=h4.rws.frame hc (by omega) f5 (by simp)
  have hp4:=hpad.frame hc hj h4.frame (pad_not_bodyW hc hj 0 (Or.inl rfl)) (pad_not_bodyW hc hj 8 (Or.inr rfl))
  have hp5:=hp4.frame hc hj f5 (by simp) (by simp)
  refine TBSim.steps s5 (TBSim.bind (W₂:=0) (hash_unit hlook hc hj hidx rows p5 hb5 hr5 hp5) (fun root t ht=>?_))
  obtain ⟨pt,bt,x12t,dlo,dhi,vt,rt,ft⟩:=ht
  refine TBSim.pure ⟨pt,bt,x12t,dlo,dhi,fun h=>⟨h4.rws.len2,vt h⟩,?_,?_,?_⟩
  · exact ((h4.regs.trans r5).trans rt).mono (by simp[bodyRegs])
  · refine ((h4.frame.trans f5).trans ft).mono (fun A _ hA=>?_)
    rcases hA with (hA|hA)|hA
    · exact Or.inl hA
    · exact hA.elim
    · rcases hA with hA|hA
      · left;unfold bodyW;right;right;right;right;left
        unfold writes at hA
        rcases hA with rfl|rfl|rfl|rfl <;> constructor <;> ao
      · exact Or.inr hA
  · intro hjs A hA h0 h6
    rw[ft.get hA (by unfold hashW writes slotV at *;intro ha;rcases ha with (ha|ha|ha|ha)|ha <;> aoh),
      f5.get hA id,h4.nos hjs A hA h0 h6]
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaves
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SharedNext (raw)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

theorem physical_raw (c : Nat) {j : Nat} (hj:j<128) : SharedLeaf.physical c (raw c j)=j := by
  unfold SharedLeaf.physical raw SharedLeaf.first SharedNext.first
  split_ifs <;> omega

theorem raw_inj (c : Nat) {j k : Nat} (hj:j<128) (hk:k<128) : raw c j=raw c k ↔ j=k := by
  constructor
  · intro h
    have:=congrArg (SharedLeaf.physical c) h
    rwa[physical_raw c hj,physical_raw c hk]at this
  · rintro rfl;rfl

theorem raw_zero (c : Nat) : raw c 0=0 := by unfold raw;split <;> rfl

theorem hashPc_next (c : Nat) (hc:c<9) : pcOf (SharedLeaf.hashPc c)+4=pcOf (SharedNext.entry c) := by
  have h:∀c,c<9→pcOf (SharedLeaf.hashPc c)+4=pcOf (SharedNext.entry c):=by decide +kernel
  exact h c hc

/-- C1: the leaf of physical child `j` sits at heap `128 + j` (`buildChildH`), its header carries the raw child. -/
def leafRows (index c sel : Nat) (word : WCT9.Rank) (coefs : List Digest) (pads : Nat→Digest) : M (List Digest×List Digest) :=
  (List.range 128).foldlM (fun acc j=>do
    let (root,values)←WCT9.buildChildH (128+j) index c (raw c j) word coefs (pads j)
    pure (acc.1++[root],if j=sel then values else acc.2)) ([],[])

structure Inv (sk : BitVec 256) (c index sel w : Nat) (s0 : MachineState) (j : Nat)
    (acc : List Digest×List Digest) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if j<128 then leafI c else SharedNext.nodePc c)
  body : BodySt sk (if j<128 then raw c j else 127) index (raw c sel) w t
  len : acc.1.length=j
  leaves : ∀j',j'<j→DigAt t (HEAPW+16*(128+j')) (acc.1.getD j' 0)
  vals : sel<j→acc.2.length=6 ∧ ∀i,i<6→DigAt t (slotV c i) (acc.2.getD i 0)
  nosig : j ≤ sel→∀A,A<2^64→slotV c 0≤A→A<slotV c 6→t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A)
  regs : RegsExcept s0 t (.x18::bodyRegs)
  frame : Frame s0 t (loopW c)

/-- One child (`6*stepC+49`) and its next-step block with the C1 leaf stub (at most 16). -/
def cost : Nat := 6*stepC+65

theorem pad_not_loopW {c j : Nat} (hc:c<9) (hj:j<128) (off : Nat) (ho:off=0∨off=8) :
    ¬loopW c (SharedLeaf.padBase c j+off) := by
  unfold loopW
  intro h
  rcases h with h|h
  · exact SharedLeaf.pad_not_bodyW hc hj off ho h
  · unfold SharedLeaf.padBase at h
    split_ifs at h <;> rcases ho with rfl|rfl <;> aoh

/-- `BodySt.with18` for a step that may write the heap (the C1 leaf stub writes the leaf's own slot). -/
theorem body_with18 {j j' index sel w : Nat} {u v : MachineState} {W : Nat → Prop}
    (h : BodySt sk j index sel w u) (hr : RegsExcept u v [.x6, .x18]) (hf : Frame u v W)
    (hW : ∀ A, W A → HEAPW ≤ A) (h18 : v.getReg .x18 = BitVec.ofNat 64 j') : BodySt sk j' index sel w v := by
  have g : ∀ A, A < HEAPW → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
    fun A hA => hf.get (by aoh) (fun hw => by have := hW A hw; omega)
  exact ⟨by rw [hr.get (by simp)]; exact h.x5, h18, by rw [hr.get (by simp)]; exact h.x22,
    by rw [hr.get (by simp)]; exact h.x24, by rw [hr.get (by simp)]; exact h.x25,
    by rw [g _ (by ao)]; exact h.p0, by rw [g _ (by ao)]; exact h.p8, by rw [g _ (by ao)]; exact h.p32,
    by rw [g _ (by ao)]; exact h.p40, by rw [g _ (by ao)]; exact h.p48, by rw [g _ (by ao)]; exact h.p56,
    by rw [g _ (by ao)]; exact h.z0, by rw [g _ (by ao)]; exact h.z8, by rw [g _ (by ao)]; exact h.z32,
    by rw [g _ (by ao)]; exact h.z40⟩

theorem step (hf:SharedReuse.Fetch im) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hl:LookOK im (SharedLeaf.look c)) (hh:LookOK im (SharedLeaf.hookLook c))
    (hn:LookOK im (SharedNext.look c)) (hc:c<9) (hsel:sel<128) (hi:index<2^31) (hw:w<2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=54)
    {s0 : MachineState} (hcoef:CoefAt s0 coefs) {pads : Nat→Digest}
    (hpad:∀j,j<128→SharedLeaf.PadAt c (raw c j) (pads j) s0)
    (j : Nat) (hj:j<128) (acc : List Digest×List Digest) (t : MachineState)
    (h:Inv sk c index sel w s0 j acc t) :
    TBSim im sk t cost (do
      let (root,values)←WCT9.buildChildH (128+j) index c (raw c j) word coefs (pads j)
      pure (acc.1++[root],if j=sel then values else acc.2)) (Inv sk c index sel w s0 (j+1)) := by
  have hpc:t.pc=pcOf (leafI c):=by rw[h.pc,if_pos hj]
  have hb:BodySt sk (raw c j) index (raw c sel) w t:=by have:=h.body;rwa[if_pos hj]at this
  have hrj:=SharedNext.raw_lt c hj
  have hrs:=SharedNext.raw_lt c hsel
  have hphys:=physical_raw c hj
  have hcu:=SharedLeaf.child_unit hf hl hh hc hrj hrs hi hw hword hlen hpc hb
    (hcoef.frame h.frame (fun A h1 h2=>coef_not_loopW hc h1 h2))
    ((hpad j hj).frame hc hrj h.frame (pad_not_loopW hc hrj 0 (Or.inl rfl)) (pad_not_loopW hc hrj 8 (Or.inr rfl)))
  rw[hphys]at hcu
  refine (TBSim.bind (W₂:=16) hcu (fun rv u hu=>?_)).mono (by unfold cost;omega) (fun _ _ h=>h)
  obtain ⟨root,values⟩:=rv
  obtain ⟨upc,ub,u12,ulo,uhi,usel,uregs,uframe,unos⟩:=hu
  obtain ⟨v,k,sv,hk,vpc,v18,vmem,vr,vf⟩:=SharedNext.step_next hn hc hrj u (upc.trans (hashPc_next c hc)) ub.x18
    (A:=HEAPW+16*(128+j)) u12 (by ao) (by unfold MEMORY_BYTES;ao)
  rw[hphys]at vmem vf
  have hm:raw c j=127 ↔ j=127:=SharedNext.raw_eq127 c hj
  -- the stub writes only the leaf's own slot (and only for even `j`)
  have hlow:∀A,A<2^64→A<HEAPW→v.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A):=
    fun A hA hl=>vf.get hA (fun hw=>by rcases hw with ⟨_,hw|hw⟩ <;> aoh)
  have uroot:DigAt v (HEAPW+16*(128+j)) root:=by
    by_cases hev:j%2=0
    · obtain ⟨m0,m8⟩:=vmem hev
      have hd:=uhi hev
      exact ⟨by rw[m0];exact hd.1,by rw[m8,show HEAPW+16*(128+j)+24=HEAPW+16*(128+j)+16+8 by omega];exact hd.2⟩
    · exact (ulo (by omega)).frame vf (by ao) (fun hw=>hev hw.1) (fun hw=>hev hw.1)
  have fuv:Frame t v (Sign.childW c j):=(uframe.trans vf).mono (fun A _ ha=>by
    rcases ha with ha|ha
    · change bodyW c A ∨ _ at ha
      change bodyW c A ∨ _
      simpa only[hphys]using ha
    · right;rcases ha with ⟨_,ha|ha⟩ <;> constructor <;> aoh)
  refine (TBSim.pure_steps' sv ?_).mono hk (fun _ _ h=>h)
  refine ⟨?_,?_,?_,fun j' hj'=>?_,fun hs=>?_,fun hs A hA h0 h6=>?_,?_,?_⟩
  · rw[vpc]
    simp only[hm]
    congr 1
    split_ifs <;> first | rfl | omega
  · by_cases hj1:j+1<128
    · rw[if_pos hj1]
      apply body_with18 ub vr vf (fun A hw=>by rcases hw with ⟨_,rfl|rfl⟩ <;> omega)
      rw[v18,if_neg (fun he=>by have:=hm.mp he;omega),SharedNext.raw_advance c hj1]
    · rw[if_neg hj1]
      apply body_with18 ub vr vf (fun A hw=>by rcases hw with ⟨_,rfl|rfl⟩ <;> omega)
      rw[v18,if_pos (hm.mpr (by omega))]
  · simp[h.len]
  · by_cases hlt:j'<j
    · rw[List.getD_eq_getElem?_getD,List.getElem?_append_left (by rw[h.len];exact hlt),←List.getD_eq_getElem?_getD]
      refine (h.leaves j' hlt).frame fuv (by ao) ?_ ?_ <;> (unfold Sign.childW bodyW slotV;aoh)
    · have he:j'=j:=by omega
      subst j'
      rw[List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw[h.len]),h.len,Nat.sub_self]
      exact uroot
  · by_cases hjs:j=sel
    · rw[if_pos hjs]
      obtain ⟨len,mem⟩:=usel ((raw_inj c hj hsel).mpr hjs)
      exact ⟨len,fun i hi=>(mem i hi).frame vf (by unfold slotV;ao)
        (fun hw=>by rcases hw with ⟨_,hw|hw⟩ <;> (unfold slotV at hw;aoh))
        (fun hw=>by rcases hw with ⟨_,hw|hw⟩ <;> (unfold slotV at hw;aoh))⟩
    · rw[if_neg hjs]
      have hrjs:raw c j≠raw c sel:=fun he=>hjs ((raw_inj c hj hsel).mp he)
      obtain ⟨len,mem⟩:=h.vals (by omega)
      refine ⟨len,fun i hi=>⟨?_,?_⟩⟩
      · rw[hlow _ (by unfold slotV;ao) (by unfold slotV;ao),
          unos hrjs _ (by unfold slotV;ao) (by unfold slotV;omega) (by unfold slotV;omega)]
        exact (mem i hi).1
      · rw[hlow _ (by unfold slotV;ao) (by unfold slotV;ao),
          unos hrjs _ (by unfold slotV;ao) (by unfold slotV;omega) (by unfold slotV;omega)]
        exact (mem i hi).2
  · rw[hlow A hA (by unfold slotV at h6;aoh),
      unos (fun he=>by have: j=sel:=(raw_inj c hj hsel).mp he;omega) A hA h0 h6]
    exact h.nosig (by omega) A hA h0 h6
  · exact (h.regs.trans (uregs.trans vr)).mono (by simp[bodyRegs])
  · refine (h.frame.trans fuv).mono (fun A _ ha=>?_)
    rcases ha with ha|ha
    · exact ha
    · rcases ha with ha|ha
      · exact Or.inl ha
      · right;constructor <;> aoh


theorem Inv.init {c index sel w : Nat} {s0 : MachineState}
    (hpc:s0.pc=pcOf (leafI c)) (hb:BodySt sk 0 index (raw c sel) w s0) :
    Inv sk c index sel w s0 0 ([],[]) s0 :=
  ⟨by rw[if_pos (by norm_num)];exact hpc,
    by rw[if_pos (by norm_num),raw_zero];exact hb,rfl,
    fun j' hj'=>absurd hj' (by omega),fun h=>absurd h (by omega),
    fun _ _ _ _ _=>rfl,RegsExcept.refl _ _,Frame.refl _ _⟩

theorem leaf_loop (hf:SharedReuse.Fetch im) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hl:LookOK im (SharedLeaf.look c)) (hh:LookOK im (SharedLeaf.hookLook c))
    (hn:LookOK im (SharedNext.look c)) (hc:c<9) (hsel:sel<128) (hi:index<2^31) (hw:w<2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=54)
    {s0 : MachineState} (hcoef:CoefAt s0 coefs) {pads : Nat→Digest}
    (hpad:∀j,j<128→SharedLeaf.PadAt c (raw c j) (pads j) s0)
    (h0:Inv sk c index sel w s0 0 ([],[]) s0) :
    TBSim im sk s0 (128*cost) (leafRows index c sel word coefs pads)
      (Inv sk c index sel w s0 128) := by
  unfold leafRows
  rw[List.range_eq_range']
  exact TBSim.foldlM_range' 0 128 _ _ (Inv sk c index sel w s0) cost
    (fun j hj acc t ht=>by
      simp only[Nat.zero_add]
      exact step hf hl hh hn hc hsel hi hw hword hlen hcoef hpad j hj acc t ht) h0
end ClaudeWCT.W9.Machine.Sign.SharedLeaves

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest pad64 shortHash publicHash)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- C1: the fold of heap `h` keeps the HIGH half on the A/B top heaps (`h < halfLimit`, as in #884), on the
singleton's left top heap 2 (stage 2, "Cm") and on the even heaps `≥ 16`; this is exactly the class selected by
the machine's fold stub. -/
def high (c h : Nat) : Bool := SharedTail.clsHigh c (SharedTail.cls c h)
theorem high_lt8 (c h : Nat) (h8:h<8) :
    high c h=decide ((c≠8 ∧ h<SharedTail.halfLimit c) ∨ (c=8 ∧ h=2)) := by
  -- (split_ifs would leave `False` literals inside the `↔` goals, which omega does not use)
  have hk:SharedTail.cls c h=(if (c≠8 ∧ h<SharedTail.halfLimit c) ∨ (c=8 ∧ h=2) then 0 else 1):=by
    unfold SharedTail.cls
    rw[if_pos (show h<16 by omega)]
  unfold high SharedTail.clsHigh
  rw[hk]
  by_cases hA:(c≠8 ∧ h<SharedTail.halfLimit c) ∨ (c=8 ∧ h=2)
  · rw[if_pos hA,decide_eq_true hA]
    exact decide_eq_true (Or.inl rfl)
  · rw[if_neg hA,decide_eq_false hA]
    exact decide_eq_false (by omega)
theorem high_ge8 (c h : Nat) (h8:8≤h) : high c h=WCT9.ftsHighHeap h := by
  -- (case split by hand: split_ifs would leave `False` literals that omega ignores)
  have hL:SharedTail.halfLimit c≤8:=by unfold SharedTail.halfLimit;split <;> omega
  unfold high SharedTail.clsHigh SharedTail.cls
  rw[if_neg (show ¬((c≠8 ∧ h<SharedTail.halfLimit c) ∨ (c=8 ∧ h=2)) by omega)]
  by_cases hx:16≤h ∧ h%2=0
  · rw[if_neg (show ¬h<16 by omega),if_neg (show ¬h%2=1 by omega),(WCT9.ftsHighHeap_iff (by omega)).mpr hx]
    exact decide_eq_true (Or.inr rfl)
  · have hf:WCT9.ftsHighHeap h=false:=by
      cases hy:WCT9.ftsHighHeap h
      · rfl
      · exact absurd ((WCT9.ftsHighHeap_iff (by omega)).mp hy) hx
    rw[hf]
    by_cases h16:h<16
    · rw[if_pos h16]
      exact decide_eq_false (by omega)
    · rw[if_neg h16,if_pos (show h%2=1 by omega)]
      exact decide_eq_false (by omega)
def hashProgram (c index h : Nat) (pad L R : Digest) : M Digest :=
  if high c h then publicHash (nodeIn c index h pad L R) >>= fun o=>pure (o.extractLsb' 128 128)
  else shortHash (nodeIn c index h pad L R)

theorem cycles_le (c m : Nat) : cycles c m≤38 := by unfold cycles;split_ifs <;> omega

theorem hashPc_tail (c : Nat) (hc:c<9) : pcOf (hashPc c)+4=pcOf (SharedTail.entry c) := by
  have h:∀c,c<9→pcOf (hashPc c)+4=pcOf (SharedTail.entry c):=by decide +kernel
  exact h c hc

theorem node_read (s : MachineState) {h : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (off : Nat) :
    (nodeLd off).eval s=s.getMem (BitVec.ofNat 64 (HEAPW+32*h+off)) := by
  change s.getMem (sh5.eval s+BitVec.ofNat 64 (HEAPW+off))=_
  rw[eval_sh5 s h18,ofNat_add_ofNat]
  congr 2
  ring

theorem input_of_readout (s u : MachineState) {c index h : Nat} {pad L R : Digest}
    (hc:c<9) (hi:index<2^31) (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) (h22:s.getReg .x22=BitVec.ofNat 64 index)
    (hL:DigAt s (HEAPW+16*(2*h)) L) (hR:DigAt s (HEAPW+16*(2*h+1)) R)
    (hp:PadAt c h pad s) (x10:u.getReg .x10=BitVec.ofNat 64 NODEW) (x11:u.getReg .x11=BitVec.ofNat 64 64)
    (hm:∀k,k<8→u.getMem (BitVec.ofNat 64 (NODEW+8*k))=(value c (mode h) (8*k)).eval s) :
    hashInput u=toQ (pad64 (nodeIn c index h pad L R)) := by
  have hP:=padWord_eval s h18 hp
  refine hashInput_node u hc hi hh x10 x11 ⟨?_,?_⟩ ?_ ?_ ⟨?_,?_⟩ ⟨?_,?_⟩
  · rw[show NODEW=NODEW+8*0 by omega,hm 0 (by decide)]
    simp only[value,↓reduceIte]
    rw[node_read s h18,show HEAPW+32*h+0=HEAPW+16*(2*h) by ring]
    exact hL.1
  · rw[show NODEW+8=NODEW+8*1 by omega,hm 1 (by decide)]
    change (nodeLd 8).eval s = L.extractLsb' 64 64
    rw[node_read s h18,show HEAPW+32*h+8=HEAPW+16*(2*h)+8 by ring]
    exact hL.2
  · rw[show NODEW+16=NODEW+8*2 by omega,hm 2 (by decide)]
    simp only[value,↓reduceIte]
    exact hdrLo_eval s h22 h18 hc hi hh
  · rw[show NODEW+24=NODEW+8*3 by omega,hm 3 (by decide)]
    simp only[value,↓reduceIte]
    exact hdrHi_eval s h18
  · rw[show NODEW+32=NODEW+8*4 by omega,hm 4 (by decide)]
    simp only[value,↓reduceIte]
    exact hP.1
  · rw[show NODEW+32+8=NODEW+8*5 by omega,hm 5 (by decide)]
    simp only[value,↓reduceIte]
    exact hP.2
  · rw[show NODEW+48=NODEW+8*6 by omega,hm 6 (by decide)]
    change (nodeLd 16).eval s = R.extractLsb' 0 64
    rw[node_read s h18,show HEAPW+32*h+16=HEAPW+16*(2*h+1) by ring]
    exact hR.1
  · rw[show NODEW+48+8=NODEW+8*7 by omega,hm 7 (by decide)]
    change (nodeLd 24).eval s = R.extractLsb' 64 64
    rw[node_read s h18,show HEAPW+32*h+24=HEAPW+16*(2*h+1)+8 by ring]
    exact hR.2

def unitW (h A : Nat) : Prop := writes A ∨ (NOUTW≤A ∧ A<NOUTW+32) ∨ A=HEAPW+16*h ∨ A=HEAPW+16*h+8

theorem hash_unit {im : Image} {sk : BitVec 256} {c index h : Nat} {pad L R : Digest}
    (hn:LookOK im (look c)) (ht:LookOK im (SharedTail.look c))
    (hc:c<9) (hi:index<2^31) (hh1:1≤h) (hh:h<128)
    {s : MachineState} (hpc:s.pc=pcOf (entry c))
    (h5:s.getReg .x5=0) (h18:s.getReg .x18=BitVec.ofNat 64 h) (h22:s.getReg .x22=BitVec.ofNat 64 index)
    (hL:DigAt s (HEAPW+16*(2*h)) L) (hR:DigAt s (HEAPW+16*(2*h+1)) R) (hp:PadAt c h pad s) :
    TBSim im sk s 68 (hashProgram c index h pad L R) (fun root t=>
      t.pc=pcOf (if h-1≠SharedTail.limit c then SharedTail.nodePc c else SharedTail.finishPc c) ∧
      t.getReg .x18=BitVec.ofNat 64 (h-1) ∧ DigAt t (HEAPW+16*h) root ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x18,.x28,.x29] ∧ Frame s t (unitW h)) := by
  obtain ⟨u,su,ec,upc,x10,x11,x12,um,ru,fu⟩:=step_node hn hc hh s hpc h18 h22
  have hq:=input_of_readout s u hc hi hh h18 h22 hL hR hp x10 x11 um
  have hx5:u.getReg .x5=0:=by rw[ru.get (by simp)];exact h5
  have hx18:u.getReg .x18=BitVec.ofNat 64 h:=by rw[ru.get (by simp)];exact h18
  have tail:∀(a:BitVec 256) (v:Digest),DigAt (writeHash u a) (NOUTW+SharedTail.halfOff (high c h)) v→
      TBSim im sk (writeHash u a) 22 (pure v) (fun root t=>
        t.pc=pcOf (if h-1≠SharedTail.limit c then SharedTail.nodePc c else SharedTail.finishPc c) ∧
        t.getReg .x18=BitVec.ofNat 64 (h-1) ∧ DigAt t (HEAPW+16*h) root ∧
        RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x18,.x28,.x29] ∧ Frame s t (unitW h)):=by
    intro a v hv
    have fh:=Frame.writeHash u a NOUTW x12 (by ao)
    obtain ⟨t,st,hcost,tpc,t18,m0,m8,rt,ft⟩:=SharedTail.step_tail ht hc hh1 hh
      (decide (h-1≠SharedTail.limit c)) rfl (writeHash u a)
      (by rw[pc_writeHash,upc,hashPc_tail c hc]) (by rw[getReg_writeHash];exact hx18)
    refine (TBSim.pure_steps' st ?_).mono hcost (fun _ _ h=>h)
    refine ⟨?_,t18,⟨?_,?_⟩,?_,?_⟩
    · simpa only[decide_eq_true_eq]using tpc
    · rw[m0];exact hv.1
    · rw[m8];exact hv.2
    · exact ((ru.trans (fun x _=>getReg_writeHash u a x : RegsExcept u (writeHash u a) [])).trans rt).mono (by simp)
    · refine ((fu.trans fh).trans ft).mono (fun A _ hA=>?_)
      rcases hA with (hA|hA)|hA
      · exact Or.inl hA
      · exact Or.inr (Or.inl hA)
      · rcases hA with hA|hA
        · exact Or.inr (Or.inr (Or.inr hA))
        · exact Or.inr (Or.inr (Or.inl hA))
  unfold hashProgram
  by_cases hhig:high c h=true
  · rw[if_pos hhig]
    refine (TBSim.steps su (TBSim.publicHash_bind' (W:=22) ec hx5
      (hashArgs_const u NODEW 64 NOUTW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a=>tail a _ ?_))).mono (by rw[blocks64 _ (nodeIn_len ..)];have:=cycles_le c (mode h);omega) (fun _ _ h=>h)
    rw[SharedTail.halfOff,if_pos hhig]
    exact DigAt.writeHash_hi u a NOUTW x12 (by ao)
  · rw[if_neg hhig]
    refine (TBSim.steps su (TBSim.shortHash_bind' (W:=22) ec hx5
      (hashArgs_const u NODEW 64 NOUTW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a=>tail a _ ?_))).mono (by rw[blocks64 _ (nodeIn_len ..)];have:=cycles_le c (mode h);omega) (fun _ _ h=>h)
    have hoff:SharedTail.halfOff (high c h)=0:=by unfold SharedTail.halfOff;rw[if_neg hhig]
    rw[hoff,Nat.add_zero]
    exact DigAt.writeHash_lo u a NOUTW x12 (by ao)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedTree
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

def count (c : Nat) : Nat := 127-SharedTail.limit c

theorem limit_bounds (c : Nat) : 1≤SharedTail.limit c ∧ SharedTail.limit c≤3 := by
  unfold SharedTail.limit;split <;> omega

theorem nodePc_entry (c : Nat) (hc:c<9) : SharedTail.nodePc c=SharedNode.entry c := by
  have h:∀c,c<9→SharedTail.nodePc c=SharedNode.entry c:=by decide +kernel
  exact h c hc

def stepProgram (index c : Nat) (pads : Nat→Digest) (nodes : Array Digest) (heap : Nat) : M (Array Digest) := do
  let value←SharedNode.hashProgram c index heap (pads heap) (nodes.getD (2*heap) 0) (nodes.getD (2*heap+1) 0)
  pure (nodes.set! heap value)

def heapProgram (index c : Nat) (pads : Nat→Digest) (leaves : List Digest) : M (Array Digest) :=
  (List.range' 0 (count c)).foldlM (fun nodes k=>stepProgram index c pads nodes (127-k))
    ((List.replicate 128 (0:Digest)++leaves).toArray)

structure Inv (c index : Nat) (s0 : MachineState) (k : Nat) (nodes : Array Digest) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if k<count c then SharedNode.entry c else SharedTail.finishPc c)
  x5 : t.getReg .x5=0
  x18 : t.getReg .x18=BitVec.ofNat 64 (127-k)
  x22 : t.getReg .x22=BitVec.ofNat 64 index
  size : nodes.size=256
  heap : ∀ m, 127-k < m → m < 256 → DigAt t (HEAPW+16*m) (nodes.getD m 0)
  regs : RegsExcept s0 t [.x6,.x7,.x10,.x11,.x12,.x18,.x28,.x29]
  frame : Frame s0 t treeW

theorem padBase_bound {c h : Nat} (hc:c<9) (hh:4≤h ∧ h<8) :
    (0x50600≤SharedNode.padBase c h ∧ SharedNode.padBase c h+8<0x51000) ∨
    (0x67000≤SharedNode.padBase c h ∧ SharedNode.padBase c h+8<0x68000) := by
  unfold SharedNode.padBase FORW
  split <;> omega

theorem pad_treeFrame {c h : Nat} {pad : Digest} {s t : MachineState}
    (hp:SharedNode.PadAt c h pad s) (hc:c<9) (hf:Frame s t treeW) : SharedNode.PadAt c h pad t := by
  unfold SharedNode.PadAt at hp ⊢
  split_ifs at hp ⊢ with hm
  · have hb:=padBase_bound hc (SharedNode.mode_one hm.1)
    exact hp.frame hf (by rcases hb with hb|hb <;> omega)
      (by unfold treeW;intro hw;rcases hb with hb|hb <;> aoh)
      (by unfold treeW;intro hw;rcases hb with hb|hb <;> aoh)
  · exact hp

theorem unitW_treeW {h A : Nat} (hh1:1≤h) (hh:h<128) (hu:SharedNode.unitW h A) : treeW A := by
  rcases hu with hu|hu|hu|hu
  · obtain ⟨k,hk,rfl⟩:=hu
    interval_cases k <;> simp[treeW]
  · exact Or.inr (Or.inl hu)
  · right;right;left;rw[hu];constructor <;> omega
  · right;right;left;rw[hu];constructor <;> omega

theorem step {c index : Nat} (hn:LookOK im (SharedNode.look c)) (ht:LookOK im (SharedTail.look c))
    (hc:c<9) (hi:index<2^31) {s0 : MachineState} {pads : Nat→Digest}
    (hpad:∀h,h<128→SharedNode.PadAt c h (pads h) s0)
    (k : Nat) (hk:k<count c) (nodes : Array Digest) (t : MachineState) (h:Inv c index s0 k nodes t) :
    TBSim im sk t 68 (stepProgram index c pads nodes (127-k)) (Inv c index s0 (k+1)) := by
  have hl:=limit_bounds c
  have hk127:k<127:=by unfold count at hk;omega
  have hh1:1≤127-k:=by omega
  have hh:127-k<128:=by omega
  have hpc:t.pc=pcOf (SharedNode.entry c):=by rw[h.pc,if_pos hk]
  have hp:SharedNode.PadAt c (127-k) (pads (127-k)) t:=
    pad_treeFrame (hpad _ hh) hc h.frame
  unfold stepProgram
  refine (TBSim.bind (W₂:=0) (SharedNode.hash_unit hn ht hc hi hh1 hh hpc h.x5 h.x18 h.x22
    (h.heap _ (by omega) (by omega)) (h.heap _ (by omega) (by omega)) hp)
    (fun value u hu=>TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
  obtain ⟨upc,u18,uv,ur,uf⟩:=hu
  refine ⟨?_,?_,?_,?_,?_,fun m hm1 hm2=>?_,(h.regs.trans ur).mono (by simp),?_⟩
  · rw[upc,nodePc_entry c hc]
    congr 1
    unfold count at *
    split_ifs <;> first | rfl | omega
  · rw[ur.get (by simp)];exact h.x5
  · rw[u18,show 127-k-1=127-(k+1) by omega]
  · rw[ur.get (by simp)];exact h.x22
  · simp[h.size]
  · by_cases hm:m=127-k
    · subst m
      rw[WCT9.getD_set_self _ _ _ (by rw[h.size];omega)]
      exact uv
    · rw[WCT9.getD_set_other _ _ _ _ (fun he=>hm he.symm)]
      refine (h.heap m (by omega) hm2).frame uf (by ao) ?_ ?_
      all_goals unfold SharedNode.unitW SharedNode.writes
      all_goals rintro (⟨j,hj,he⟩|he|he|he) <;> aoh
  · exact (h.frame.trans uf).mono (fun A _ ha=>ha.elim id (unitW_treeW hh1 hh))

theorem heap_loop {c index : Nat} (hn:LookOK im (SharedNode.look c)) (ht:LookOK im (SharedTail.look c))
    (hc:c<9) (hi:index<2^31) {s0 : MachineState} {pads : Nat→Digest} {leaves : List Digest}
    (hpad:∀h,h<128→SharedNode.PadAt c h (pads h) s0)
    (h0:Inv c index s0 0 ((List.replicate 128 (0:Digest)++leaves).toArray) s0) :
    TBSim im sk s0 (count c*68) (heapProgram index c pads leaves) (Inv c index s0 (count c)) := by
  unfold heapProgram
  exact TBSim.foldlM_range' 0 (count c) _ _ (Inv c index s0) 68
    (fun k hk nodes t ht'=>by
      simp only[Nat.zero_add]
      exact step hn ht hc hi hpad k hk nodes t ht') h0
end ClaudeWCT.W9.Machine.Sign.SharedTree

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

def minHeap (c : Nat) : Nat := 2^(8-levels c)

theorem path_copies {c sel : Nat} (hlook:LookOK im (look c)) (hc:c < 9) (hsel:sel < 128) {heap : Array Digest} :
    ∀ n, n ≤ levels c  →  ∀ t : MachineState, t.pc=pcOf (entry c (levels c-n))  →  t.getReg .x24=BitVec.ofNat 64 (128+sel)  → 
      (∀ m, minHeap c ≤ m  →  m < 256  →  DigAt t (HEAPW+16*m) (heap.getD m 0))  → 
      ∃ u, Steps im t (12*n) (12*n) u ∧ u.pc=pcOf (entry c (levels c)) ∧
        (∀ l, levels c-n ≤ l  →  l < levels c  →  DigAt u (target c l) (heap.getD (2^(7-l)+(sel/2^l ^^^1)) 0)) ∧
        RegsExcept t u [.x6,.x7,.x28,.x29] ∧ Frame t u (fun A=>target c (levels c-n) ≤ A ∧ A < target c (levels c)) := by
  intro n
  induction n with
  | zero =>
    intro _ t hpc _ _
    exact ⟨t,Steps.refl t,hpc,fun l h1 h2=>absurd h2 (by omega),RegsExcept.refl _ _,fun _ _ _=>rfl⟩
  | succ n ih =>
    intro hn t hpc h24 hheap
    have hb:=levels_bound c
    have hl:levels c-(n+1) < levels c:=by omega
    have hl7:levels c-(n+1) < 7:=by omega
    obtain ⟨t1,s1,p1,m0,m8,r1,f1⟩:=step_path hlook hc hl hsel t hpc h24
    have hph:=pathHeap_lt sel (levels c-(n+1)) hsel hl7
    have hm:=hheap (2^(7-(levels c-(n+1)))+(sel/2^(levels c-(n+1)) ^^^1)) (by
      have hp:2^(8-levels c) ≤ 2^(7-(levels c-(n+1))):=Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold minHeap
      omega) hph
    have h24':t1.getReg .x24=BitVec.ofNat 64 (128+sel):=by rw[r1.get (by simp)];exact h24
    have hheap':∀ m, minHeap c ≤ m  →  m < 256  →  DigAt t1 (HEAPW+16*m) (heap.getD m 0):=fun m h1 h2=>
      (hheap m h1 h2).frame f1 (by ao) (by unfold target slotV;intro h;rcases h with h|h  <;> aoh)
        (by unfold target slotV;intro h;rcases h with h|h  <;> aoh)
    obtain ⟨u,su,pu,hu,ru,fu⟩:=ih (by omega) t1
      (by rw[p1,show levels c-(n+1)+1=levels c-n by omega]) h24' hheap'
    refine ⟨u,(s1.trans su).of_eq (by ring) (by ring),pu,fun l h1 h2=>?_,(r1.trans ru).mono (by simp),?_⟩
    · by_cases hle:levels c-n ≤ l
      · exact hu l hle h2
      · have he:l=levels c-(n+1):=by omega
        subst l
        have hd:DigAt t1 (target c (levels c-(n+1))) (heap.getD (2^(7-(levels c-(n+1)))+(sel/2^(levels c-(n+1)) ^^^1)) 0):=
          ⟨by rw[m0];exact hm.1,by rw[m8];exact hm.2⟩
        exact hd.frame fu (by unfold target slotV;ao) (by unfold target slotV;intro h;aoh) (by unfold target slotV;intro h;aoh)
    · refine (f1.trans fu).mono (fun A _ hA=>?_)
      unfold target slotV at *
      rcases hA with (h|h)|h  <;> aoh
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

def rowsHeap (index c sel : Nat) (word : WCT9.Rank) (coefs : List Digest)
    (leftPads rightPads : Nat → Digest) : M (Array Digest×List Digest) := do
  let rows←SharedLeaves.leafRows index c sel word coefs leftPads
  let nodes←SharedTree.heapProgram index c rightPads rows.1
  pure (nodes,rows.2)

def writes (c A : Nat) : Prop := loopW c A ∨ treeW A

structure Post (sk : BitVec 256) (c index sel w : Nat) (s0 : MachineState) (rv : Array Digest×List Digest)
    (t : MachineState) : Prop where
  tree : SharedTree.Inv c index t (SharedTree.count c) rv.1 t
  values : rv.2.length=6 ∧ ∀i, i < 6  →  DigAt t (slotV c i) (rv.2.getD i 0)
  x24 : t.getReg .x24=BitVec.ofNat 64 (SharedNext.raw c sel)
  regs : RegsExcept s0 t (.x18::bodyRegs)
  frame : Frame s0 t (writes c)

theorem initial_heap_getD (leaves : List Digest) (m : Nat) (hm:128 ≤ m) :
    ((List.replicate 128 (0:Digest)++leaves).toArray).getD m 0=leaves.getD (m-128) 0 := by
  rw[Array.getD_eq_getD_getElem?,List.getElem?_toArray,List.getElem?_append_right (by simp;omega)]
  simp[List.getD_eq_getElem?_getD]

theorem pad_leafFrame {c h : Nat} {pad : Digest} {s t : MachineState}
    (hp:SharedNode.PadAt c h pad s) (hc:c < 9) (hf:Frame s t (loopW c)) : SharedNode.PadAt c h pad t := by
  unfold SharedNode.PadAt at hp ⊢
  split_ifs at hp ⊢ with hm
  · have hb:=SharedTree.padBase_bound hc (SharedNode.mode_one hm.1)
    exact hp.frame hf (by rcases hb with hb|hb  <;> omega)
      (by unfold loopW bodyW slotV;intro hw;rcases hb with hb|hb  <;> aoh)
      (by unfold loopW bodyW slotV;intro hw;rcases hb with hb|hb  <;> aoh)
  · exact hp

theorem nextNode_eq (c : Nat) (hc:c < 9) : SharedNext.nodePc c=SharedNode.entry c := by
  have h:∀c,c < 9 → SharedNext.nodePc c=SharedNode.entry c:=by decide +kernel
  exact h c hc

theorem rows_heap (hf:SharedReuse.Fetch im) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hl:LookOK im (SharedLeaf.look c)) (hh:LookOK im (SharedLeaf.hookLook c))
    (hn:LookOK im (SharedNext.look c)) (hnode:LookOK im (SharedNode.look c)) (ht:LookOK im (SharedTail.look c))
    (hc:c < 9) (hsel:sel < 128) (hi:index < 2^31) (hw:w < 2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=54)
    {s : MachineState} (hcoef:CoefAt s coefs) {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128  →  SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128  →  SharedNode.PadAt c h (rightPads h) s)
    (hpc:s.pc=pcOf (leafI c)) (hb:BodySt sk 0 index (SharedNext.raw c sel) w s) :
    TBSim im sk s (128*SharedLeaves.cost+SharedTree.count c*68)
      (rowsHeap index c sel word coefs leftPads rightPads) (Post sk c index sel w s) := by
  unfold rowsHeap
  refine TBSim.bind (SharedLeaves.leaf_loop hf hl hh hn hc hsel hi hw hword hlen hcoef hpadL (SharedLeaves.Inv.init hpc hb))
    (fun rows u hu=>?_)
  have hupc:u.pc=pcOf (SharedNode.entry c):=by rw[hu.pc,if_neg (by omega),nextNode_eq c hc]
  have hub:BodySt sk 127 index (SharedNext.raw c sel) w u:=by have:=hu.body;rwa[if_neg (by omega)]at this
  have countpos:0 < SharedTree.count c:=by have:=SharedTree.limit_bounds c;unfold SharedTree.count;omega
  have h0:SharedTree.Inv c index u 0 ((List.replicate 128 (0:Digest)++rows.1).toArray) u:=
    ⟨by rw[if_pos countpos];exact hupc,hub.x5,hub.x18,hub.x22,by simp[hu.len],
      fun m hm1 hm2=>by
        rw[initial_heap_getD _ _ (by omega)]
        have hd:=hu.leaves (m-128) (by omega)
        rwa[show 128+(m-128)=m by omega]at hd,
      RegsExcept.refl _ _,Frame.refl _ _⟩
  refine (TBSim.bind (W₂:=0) (SharedTree.heap_loop hnode ht hc hi (fun h hh=>pad_leafFrame (hpadR h hh) hc hu.frame) h0)
    (fun nodes t ht'=>TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
  obtain ⟨hlen,hvals⟩:=hu.vals hsel
  refine ⟨?_,⟨hlen,fun i hi=>?_⟩,?_,?_,?_⟩
  · exact ⟨ht'.pc,ht'.x5,ht'.x18,ht'.x22,ht'.size,ht'.heap,RegsExcept.refl _ _,Frame.refl _ _⟩
  · exact (hvals i hi).frame ht'.frame (by unfold slotV;ao)
      (by unfold treeW slotV;intro h;aoh) (by unfold treeW slotV;intro h;aoh)
  · rw[ht'.regs.get (by simp)];exact hub.x24
  · exact (hu.regs.trans ht'.regs).mono (by simp[bodyRegs])
  · exact (hu.frame.trans ht'.frame).mono (fun A _ ha=>ha)
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def rootBase (c : Nat) : Nat := if SharedFinish.first c then 4 else 2
def rootCount (c : Nat) : Nat := if SharedFinish.first c then 4 else 2

def RootAt (c : Nat) (nodes : Array Digest) (s : MachineState) : Prop :=
  ∀ j, j < rootCount c  →  DigAt s (SharedFinish.target c+16*j) (nodes.getD (rootBase c+j) 0)

def FinalWrites (c A : Nat) : Prop := SharedFinish.writes c A ∨
  (SharedPath.target c 0 ≤ A ∧ A < SharedPath.target c (SharedPath.levels c)) ∨
  (SharedEnd.first c=true ∧ (A=SharedEnd.target c+8 ∨ A=SharedEnd.target c))

theorem layout (c : Nat) (hc:c < 9) :
    SharedTail.finishPc c=SharedFinish.entry c ∧
    SharedFinish.pathPc c=SharedPath.entry c 0 ∧
    SharedPath.entry c (SharedPath.levels c)=SharedEnd.entry c ∧
    SharedPath.minHeap c=SharedTail.limit c+1 ∧
    SharedFinish.nwords c=2*rootCount c ∧
    SharedFinish.source c=HEAPW+16*rootBase c := by
  have h:∀c,c < 9  → 
    SharedTail.finishPc c=SharedFinish.entry c ∧
    SharedFinish.pathPc c=SharedPath.entry c 0 ∧
    SharedPath.entry c (SharedPath.levels c)=SharedEnd.entry c ∧
    SharedPath.minHeap c=SharedTail.limit c+1 ∧
    SharedFinish.nwords c=2*rootCount c ∧
    SharedFinish.source c=HEAPW+16*rootBase c:=by decide +kernel
  exact h c hc

theorem physical_raw (c : Nat) {sel : Nat} (hsel:sel < 128) :
    SharedFinish.physical c (SharedNext.raw c sel)=sel := by
  unfold SharedFinish.physical SharedNext.raw SharedFinish.first SharedNext.first
  split_ifs  <;> omega

theorem root_bounds (c : Nat) : rootBase c=SharedTail.limit c+1 ∧ rootCount c ≤ 4 := by
  unfold rootBase rootCount SharedFinish.first SharedTail.limit SharedTail.first
  split_ifs  <;> omega

theorem target_range {c A : Nat} (hc:c < 9) (ha:SharedFinish.writes c A) :
    (0x50600 ≤ A ∧ A < 0x51000) ∨ (0x67000 ≤ A ∧ A < 0x68000) := by
  obtain ⟨k,hk,rfl⟩:=ha
  unfold SharedFinish.target SharedFinish.nwords SharedFinish.first FORW at *
  split_ifs at hk ⊢  <;> omega

theorem finish {im : Image} {c sel : Nat}
    (hf:LookOK im (SharedFinish.look c)) (hp:LookOK im (SharedPath.look c)) (he:LookOK im (SharedEnd.look c))
    (hc:c < 9) (hsel:sel < 128) {nodes : Array Digest} (s : MachineState)
    (hpc:s.pc=pcOf (SharedTail.finishPc c)) (h24:s.getReg .x24=BitVec.ofNat 64 (SharedNext.raw c sel))
    (hheap:∀m, SharedTail.limit c < m  →  m < 256  →  DigAt s (HEAPW+16*m) (nodes.getD m 0)) :
    ∃t n,Steps im s n n t ∧ n ≤ 110 ∧ t.pc=pcOf (SharedEnd.nextPc c) ∧ RootAt c nodes t ∧
      (∀l, l < SharedPath.levels c  →  DigAt t (SharedPath.target c l) (nodes.getD (2^(7-l)+(sel/2^l ^^^1)) 0)) ∧
      (SharedEnd.first c=true  →  DigAt t (SharedEnd.target c) 0) ∧
      RegsExcept s t [.x6,.x7,.x24,.x28,.x29] ∧ Frame s t (FinalWrites c) := by
  obtain ⟨el,ep,ee,em,en,es⟩:=layout c hc
  obtain ⟨u,su,hcu,upc,u24,um,ur,uf⟩:=SharedFinish.step_finish hf hc (SharedNext.raw_lt c hsel) s (hpc.trans (congrArg pcOf el)) h24
  have huRoots:RootAt c nodes u:=by
    intro j hj
    have hbr:=root_bounds c
    have hm:=hheap (rootBase c+j) (by omega) (by unfold rootBase;split  <;> omega)
    refine ⟨?_,?_⟩
    · rw[show SharedFinish.target c+16*j=SharedFinish.target c+8*(2*j) by ring,um _ (by rw[en];omega),es,
        show HEAPW+16*rootBase c+8*(2*j)=HEAPW+16*(rootBase c+j) by ring]
      exact hm.1
    · rw[show SharedFinish.target c+16*j+8=SharedFinish.target c+8*(2*j+1) by ring,um _ (by rw[en];omega),es,
        show HEAPW+16*rootBase c+8*(2*j+1)=HEAPW+16*(rootBase c+j)+8 by ring]
      exact hm.2
  have huHeap:∀m, SharedPath.minHeap c ≤ m  →  m < 256  →  DigAt u (HEAPW+16*m) (nodes.getD m 0):=by
    intro m hm hm2
    rw[em]at hm
    exact (hheap m (by omega) hm2).frame uf (by ao)
      (by intro h;have:=target_range hc h;aoh) (by intro h;have:=target_range hc h;aoh)
  obtain ⟨v,sv,vpc,vm,vr,vf⟩:=SharedPath.path_copies hp hc hsel (SharedPath.levels c) le_rfl u
    (by simpa only[Nat.sub_self]using upc.trans (congrArg pcOf ep))
    (by rwa[physical_raw c hsel]at u24) huHeap
  obtain ⟨t,n,st,hct,tpc,tzero,tr,tf⟩:=SharedEnd.step_end he hc v (vpc.trans (congrArg pcOf ee))
  have hl:=SharedPath.levels_bound c
  refine ⟨t,(SharedFinish.words c).length+12*SharedPath.levels c+n,(su.trans sv).trans st,by omega,tpc,?_,?_,tzero,?_,?_⟩
  · intro j hj
    refine ((huRoots j hj).frame vf ?_ ?_ ?_).frame tf ?_ ?_ ?_
    all_goals have hrc:=root_bounds c
    all_goals have ht:=SharedFinish.target_bound hc
    all_goals try omega
    all_goals simp only[SharedPath.target,SharedEnd.target,slotV,slotP]
    all_goals intro h
    all_goals unfold SharedFinish.target FORW at *
    all_goals split_ifs at *  <;> aoh
  · intro l hl'
    refine (vm l (by omega) hl').frame tf (by unfold SharedPath.target slotV;ao) ?_ ?_
    all_goals simp only[SharedPath.target,SharedEnd.target,slotV,slotP]
    all_goals rintro ⟨hf',hA|hA⟩
    all_goals have hl6:SharedPath.levels c=6:=if_pos (of_decide_eq_true hf')
    all_goals aoh
  · exact ((ur.trans vr).trans tr).mono (by simp)
  · refine ((uf.trans vf).trans tf).mono (fun A _ hA=>?_)
    rcases hA with (hA|hA)|hA
    · exact Or.inl hA
    · exact Or.inr (Or.inl (by simpa only[Nat.sub_self]using hA))
    · exact Or.inr (Or.inr hA)
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

def allWrites (c A : Nat) : Prop := writes c A ∨ FinalWrites c A
structure Out (c index : Nat) (s0 : MachineState) (rv : Array Digest×List Digest)
    (sel : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (SharedEnd.nextPc c)
  x5 : t.getReg .x5=0
  x22 : t.getReg .x22=BitVec.ofNat 64 index
  size : rv.1.size=256
  roots : RootAt c rv.1 t
  values : rv.2.length=6 ∧ ∀i, i < 6 → DigAt t (slotV c i) (rv.2.getD i 0)
  paths : ∀l, l < SharedPath.levels c → DigAt t (SharedPath.target c l) (rv.1.getD (2^(7-l)+(sel/2^l ^^^1)) 0)
  dummy : SharedEnd.first c=true → DigAt t (SharedEnd.target c) 0
  regs : RegsExcept s0 t (.x24::.x18::bodyRegs)
  frame : Frame s0 t (allWrites c)

theorem value_frame {c i : Nat} (hc:c < 9) (hi:i < 6) {s t : MachineState} {d : Digest}
    (hd:DigAt s (slotV c i) d) (hf:Frame s t (FinalWrites c)) : DigAt t (slotV c i) d := by
  refine hd.frame hf (by unfold slotV;ao) ?_ ?_
  all_goals intro h
  all_goals rcases h with h|(h|h)
  all_goals first
    | (have:=target_range hc h;unfold slotV at *;aoh)
    | (simp only[SharedPath.target,slotV]at h;omega)
    | (simp only[SharedEnd.target,slotP,slotV]at h ⊢;rcases h.2 with h|h <;> omega)

theorem rows_finish (hf:SharedReuse.Fetch im) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hl:LookOK im (SharedLeaf.look c)) (hh:LookOK im (SharedLeaf.hookLook c))
    (hn:LookOK im (SharedNext.look c)) (hnode:LookOK im (SharedNode.look c)) (ht:LookOK im (SharedTail.look c))
    (hfinish:LookOK im (SharedFinish.look c)) (hpath:LookOK im (SharedPath.look c)) (hend:LookOK im (SharedEnd.look c))
    (hc:c < 9) (hsel:sel < 128) (hi:index < 2^31) (hw:w < 2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=54)
    {s : MachineState} (hcoef:CoefAt s coefs) {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128 → SharedNode.PadAt c h (rightPads h) s)
    (hpc:s.pc=pcOf (leafI c)) (hb:BodySt sk 0 index (SharedNext.raw c sel) w s) :
    TBSim im sk s (128*SharedLeaves.cost+SharedTree.count c*68+110)
      (rowsHeap index c sel word coefs leftPads rightPads) (fun rv t=>Out c index s rv sel t) := by
  have hrun:=rows_heap hf hl hh hn hnode ht hc hsel hi hw hword hlen hcoef hpadL hpadR hpc hb
  have h: TBSim im sk s (128*SharedLeaves.cost+SharedTree.count c*68+110)
      (rowsHeap index c sel word coefs leftPads rightPads >>= pure) (fun rv t=>Out c index s rv sel t):=by
    refine TBSim.bind hrun (fun rv u hu=>?_)
    obtain ⟨t,n,st,hn,tpc,roots,paths,dummy,regs,frame⟩:=finish hfinish hpath hend hc hsel u
      (by simpa only[if_neg (Nat.lt_irrefl _)]using hu.tree.pc) hu.x24
      (fun m hm hm2=>hu.tree.heap m (by unfold SharedTree.count;have:=SharedTree.limit_bounds c;omega) hm2)
    refine (TBSim.steps st (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
    refine ⟨tpc,?_,?_,hu.tree.size,roots,⟨hu.values.1,?_⟩,paths,dummy,?_,?_⟩
    · rw[regs.get (by simp)];exact hu.tree.x5
    · rw[regs.get (by simp)];exact hu.tree.x22
    · intro i hi;exact value_frame hc hi (hu.values.2 i hi) frame
    · exact (hu.regs.trans regs).mono (by simp[bodyRegs])
    · exact (hu.frame.trans frame).mono (fun A _ h=>h)
  simpa only[bind_pure]using h
#print axioms rows_finish
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SharedReuse (coefW coefRegs coefStepC)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

def program (index c sel : Nat) (word : WCT9.Rank) (leftPads rightPads : Nat → Digest) : M (Array Digest×List Digest) := do
  let coefs←WCT9.ftsCoefs index c
  rowsHeap index c sel word coefs leftPads rightPads

def coordinateW (c A : Nat) : Prop := coefW A ∨ allWrites c A
structure FullOut (c index : Nat) (s0 : MachineState) (rv : Array Digest×List Digest)
    (sel : Nat) (t : MachineState) : Prop where
  out : Out c index t rv sel t
  regs : RegsExcept s0 t (.x25::.x24::.x18::bodyRegs)
  frame : Frame s0 t (coordinateW c)

theorem padL_coefFrame {c j : Nat} {pad : Digest} {s t : MachineState}
    (hp:SharedLeaf.PadAt c j pad s) (hc:c < 9) (hj:j < 128) (hf:Frame s t coefW) : SharedLeaf.PadAt c j pad t := by
  unfold SharedLeaf.PadAt at hp ⊢
  split_ifs at hp ⊢
  · exact hp
  · refine hp.frame hf ?_ ?_ ?_
    all_goals simp only[SharedLeaf.padBase,coefW,COEF,FORW]
    all_goals split_ifs <;> aoh

theorem padR_coefFrame {c h : Nat} {pad : Digest} {s t : MachineState}
    (hp:SharedNode.PadAt c h pad s) (hc:c < 9) (hf:Frame s t coefW) : SharedNode.PadAt c h pad t := by
  unfold SharedNode.PadAt at hp ⊢
  split_ifs at hp ⊢ with hm
  · have hmode:=SharedNode.mode_one hm.1
    have hb:=SharedTree.padBase_bound hc hmode
    refine hp.frame hf ?_ ?_ ?_
    all_goals simp only[SharedNode.padBase,FORW,coefW,COEF]
    all_goals split_ifs <;> aoh
  · exact hp

theorem coefs_rows_finish (hf:SharedReuse.Fetch im) {c old index sel w : Nat} {word : WCT9.Rank}
    (hl:LookOK im (SharedLeaf.look c)) (hh:LookOK im (SharedLeaf.hookLook c))
    (hn:LookOK im (SharedNext.look c)) (hnode:LookOK im (SharedNode.look c)) (ht:LookOK im (SharedTail.look c))
    (hfinish:LookOK im (SharedFinish.look c)) (hpath:LookOK im (SharedPath.look c)) (hend:LookOK im (SharedEnd.look c))
    (hc:c < 9) (hsel:sel < 128) (hi:index < 2^31) (hw:w < 2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i)
    {s : MachineState} {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128 → SharedNode.PadAt c h (rightPads h) s)
    (hpc:s.pc=pcOf (lwuI c+1)) (hb:BodySt sk old index (SharedNext.raw c sel) w s) :
    TBSim im sk s (14+27*coefStepC+(128*SharedLeaves.cost+SharedTree.count c*68+110))
      (program index c sel word leftPads rightPads) (fun rv t=>FullOut c index s rv sel t) := by
  unfold program
  refine TBSim.bind (SharedReuse.coefs_unit hf hc hi hpc hb) (fun coefs u hu=>?_)
  obtain ⟨upc,ub,ulen,ucoefs,ur,uf⟩:=hu
  refine (rows_finish hf hl hh hn hnode ht hfinish hpath hend hc hsel hi hw hword ulen ucoefs
    (fun j hj=>padL_coefFrame (hpadL j hj) hc (SharedNext.raw_lt c hj) uf)
    (fun h hh=>padR_coefFrame (hpadR h hh) hc uf) upc ub).mono le_rfl (fun rv t ht=>?_)
  refine ⟨⟨ht.pc,ht.x5,ht.x22,ht.size,ht.roots,ht.values,ht.paths,ht.dummy,RegsExcept.refl _ _,Frame.refl _ _⟩,?_,?_⟩
  · exact (ur.trans ht.regs).mono (by simp[coefRegs,bodyRegs])
  · exact (uf.trans ht.frame).mono (fun A _ h=>h)
#print axioms coefs_rows_finish
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def ZeroCell (A : Nat) : Prop := ScrZero A ∧ A ≠ NODEW+32 ∧ A ≠ NODEW+40
structure Ready (sk N : BitVec 256) (t : MachineState) : Prop where
  x5 : t.getReg .x5=0
  x22 : t.getReg .x22=BitVec.ofNat 64 (WCT9.digestIndex N)
  nbuf : OutAt t NBUF N
  table : TableAt t
  p0 : t.getMem (BitVec.ofNat 64 PRIVW)=sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW+8))=sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW+32))=sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW+40))=sk.extractLsb' 192 64
  zero : ∀A,ZeroCell A → t.getMem (BitVec.ofNat 64 A)=0

theorem writes_outside {c A : Nat} (hc:c < 9)
    (hA:(NBUF ≤ A ∧ A < NBUF+32) ∨ (TBL ≤ A ∧ A < TBL+65536) ∨
      A=PRIVW ∨ A=PRIVW+8 ∨ A=PRIVW+32 ∨ A=PRIVW+40 ∨ ZeroCell A) : ¬coordinateW c A := by
  have hl:=SharedPath.levels_bound c
  intro hw
  unfold coordinateW allWrites writes FinalWrites at hw
  rcases hw with hw|((hw|hw)|(hw|(hw|hw)))
  all_goals first
    | (have hb:=target_range hc hw;unfold ZeroCell ScrZero at hA;rcases hb with hb|hb <;> aoh)
    | (simp only[SharedReuse.coefW,COEF,loopW,bodyW,treeW,SharedPath.target,SharedEnd.target,slotV,slotP,ZeroCell,ScrZero]at *;aoh)

theorem Ready.frame {sk N : BitVec 256} {s t : MachineState} {c : Nat} {rs : List Reg}
    (hc:c < 9) (h:Ready sk N s) (hr:RegsExcept s t rs) (h5:.x5 ∉ rs) (h22:.x22 ∉ rs)
    (hf:Frame s t (coordinateW c)) : Ready sk N t := by
  refine ⟨by rw[hr.get h5];exact h.x5,by rw[hr.get h22];exact h.x22,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk;rw[hf.get (by ao) (writes_outside hc (by left;constructor <;> ao))];exact h.nbuf k hk
  · intro k hk;rw[hf.get (by ao) (writes_outside hc (by right;left;constructor <;> ao))];exact h.table k hk
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p0
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p8
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p32
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p40
  · intro A hA
    rw[hf.get (by unfold ZeroCell ScrZero at hA;aoh) (writes_outside hc (by simp[hA]))]
    exact h.zero A hA

theorem Ready.body {sk N : BitVec 256} {s : MachineState} (h:Ready sk N s) (sel w : Nat)
    (h24:s.getReg .x24=BitVec.ofNat 64 sel) (h25:s.getReg .x25=BitVec.ofNat 64 w) :
    BodySt sk (s.getReg .x18).toNat (WCT9.digestIndex N) sel w s := by
  refine ⟨h.x5,by simp,h.x22,h24,h25,h.p0,h.p8,h.p32,h.p40,?_,?_,?_,?_,?_,?_⟩
  all_goals exact h.zero _ (by simp[ZeroCell,ScrZero] <;> ao)
#print axioms Ready.frame
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

structure Code (im : Image) (c : Nat) : Prop where
  field : LookOK im (SharedField.look c)
  leaf : LookOK im (SharedLeaf.look c)
  hook : LookOK im (SharedLeaf.hookLook c)
  next : LookOK im (SharedNext.look c)
  node : LookOK im (SharedNode.look c)
  tail : LookOK im (SharedTail.look c)
  finish : LookOK im (SharedFinish.look c)
  path : LookOK im (SharedPath.look c)
  ending : LookOK im (SharedEnd.look c)

def chosen (c : Nat) (a : BitVec 256) : Nat := SharedLeaf.physical c (a.toNat/2^(SharedField.rawBit c)%128)
def rank (c : Nat) (a : BitVec 256) : Nat := a.toNat/2^(SharedField.rankBit c)%1024

theorem chosen_lt (c : Nat) (a : BitVec 256) : chosen c a < 128 := by
  have h: a.toNat/2^(SharedField.rawBit c)%128 < 128:=Nat.mod_lt _ (by decide)
  unfold chosen SharedLeaf.physical
  split_ifs <;> omega

theorem raw_chosen (c : Nat) (a : BitVec 256) : SharedNext.raw c (chosen c a)=a.toNat/2^(SharedField.rawBit c)%128 := by
  have h: a.toNat/2^(SharedField.rawBit c)%128 < 128:=Nat.mod_lt _ (by decide)
  unfold chosen SharedLeaf.physical SharedNext.raw SharedLeaf.first SharedNext.first
  split_ifs <;> omega

def cost (c : Nat) : Nat := 19+(14+27*SharedReuse.coefStepC+(128*SharedLeaves.cost+SharedTree.count c*68+110))

theorem coordinate (hf:SharedReuse.Fetch im) {c : Nat} (hc:c < 9) (hcode:Code im c)
    (a : BitVec 256) (hrank:rank c a < 563) (s : MachineState) (hpc:s.pc=pcOf (cbase c))
    (hs:Ready sk a s) {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128 → SharedNode.PadAt c h (rightPads h) s) :
    TBSim im sk s (cost c)
      (program (WCT9.digestIndex a) c (chosen c a) ⟨rank c a,hrank⟩ leftPads rightPads)
      (fun rv t=>FullOut c (WCT9.digestIndex a) s rv (chosen c a) t ∧ Ready sk a t) := by
  obtain ⟨u,n,su,hn,upc,u24,u28,ur,uf⟩:=SharedField.step_field hcode.field hc s hpc hs.nbuf
  have hu:Ready sk a u:=hs.frame hc ur (by simp) (by simp) (uf.mono (fun _ _ h=>h.elim))
  obtain ⟨v,sv,vpc,v25,vr,vf⟩:=SharedReuse.step_lwu hf hc u upc (f:=rank c a) (by omega) u28 hu.table
  have hv:Ready sk a v:=hu.frame hc vr (by simp) (by simp) (vf.mono (fun _ _ h=>h.elim))
  have huv:Frame s v (fun _=>False):=(uf.trans vf).mono (fun _ _ h=>h.elim id id)
  have v24:v.getReg .x24=BitVec.ofNat 64 (SharedNext.raw c (chosen c a)):=by rw[vr.get (by simp),u24,raw_chosen]
  have hb:=hv.body _ _ v24 v25
  refine (TBSim.steps (su.trans sv)
    ((coefs_rows_finish hf hcode.leaf hcode.hook hcode.next hcode.node hcode.tail hcode.finish hcode.path hcode.ending
      hc (chosen_lt c a) (WCT9.digestIndex_lt a) (lt_trans (pkAt_lt _) (by decide)) (pkAt_digit _ hrank)
      (fun j hj => ?_) (fun h hh => ?_) vpc hb).mono le_rfl (fun rv t ht=>?_))).mono ?_ (fun _ _ h=>h)
  · exact padL_coefFrame (hpadL j hj) hc (SharedNext.raw_lt c hj) (huv.mono (fun _ _ h=>h.elim))
  · exact padR_coefFrame (hpadR h hh) hc (huv.mono (fun _ _ h=>h.elim))
  · have hfull:FullOut c (WCT9.digestIndex a) s rv (chosen c a) t:=
      ⟨ht.out,((ur.trans vr).trans ht.regs).mono (by simp[bodyRegs]),
        (huv.trans ht.frame).mono (fun _ _ h=>h.elim False.elim id)⟩
    exact ⟨hfull,hs.frame hc hfull.regs (by simp[bodyRegs]) (by simp[bodyRegs]) hfull.frame⟩
  · unfold cost;omega
#print axioms coordinate
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def rightPads (pads : Nat → SharedForest.PairRoot) (h : Nat) : Digest :=
  if 4 ≤ h ∧ h < 8 then (pads (h/2-2)).2 else 0

theorem hashProgram_source (c index h : Nat) (hc:c < 9) (hh:SharedTail.limit c < h)
    (pads : Nat → SharedForest.PairRoot) (L R : Digest) :
    SharedNode.hashProgram c index h (rightPads pads h) L R=
      SharedForest.sharedNode (SharedLeaf.first c) c index h pads L R := by
  by_cases hh8:h < 8
  · -- (explicit rewrites, no simp sets: stage 2 adds the singleton's `c = 8 ∧ h = 2` HIGH case)
    unfold SharedNode.hashProgram SharedForest.sharedNode
    rw[SharedNode.high_lt8 c h hh8]
    by_cases hf:SharedLeaf.first c=true
    · have hc8:c ≠ 8:=by simp only[SharedLeaf.first,decide_eq_true_eq]at hf;omega
      have hh4:4 ≤ h:=by
        change (if SharedLeaf.first c then 3 else 1) < h at hh
        rw[if_pos hf]at hh
        omega
      have hhalf:SharedTail.halfLimit c=8:=by change (if SharedLeaf.first c then 8 else 4)=8;rw[if_pos hf]
      have hD:decide ((c≠8 ∧ h<SharedTail.halfLimit c) ∨ (c=8 ∧ h=2))=true:=
        decide_eq_true (Or.inl ⟨hc8,by omega⟩)
      have hr:rightPads pads h=(pads (h/2-2)).2:=by unfold rightPads;rw[if_pos ⟨hh4,hh8⟩]
      rw[if_pos hD,hr,if_neg (show ¬h < 4 by omega),if_pos hh8]
      (try dsimp only)
      rw[if_pos hf]
      rfl
    · have hh2:2 ≤ h:=by
        change (if SharedLeaf.first c then 3 else 1) < h at hh
        rw[if_neg hf]at hh
        omega
      have hhalf:SharedTail.halfLimit c=4:=by change (if SharedLeaf.first c then 8 else 4)=4;rw[if_neg hf]
      rw[hhalf]
      by_cases h4:h < 4
      · have hr:rightPads pads h=0:=by unfold rightPads;rw[if_neg (show ¬(4 ≤ h ∧ h < 8) by omega)]
        rw[hr,if_pos h4]
        unfold SharedForest.sharedOuterHash
        (try dsimp only)
        by_cases hD:(c≠8 ∧ h<4) ∨ (c=8 ∧ h=2)
        · rw[if_pos (decide_eq_true hD),if_neg (show ¬(c=8 ∧ h=3) by omega)]
          rfl
        · rw[if_neg (show ¬decide ((c≠8 ∧ h<4) ∨ (c=8 ∧ h=2))=true from fun hx=>hD (of_decide_eq_true hx)),
            if_pos (show c=8 ∧ h=3 by omega)]
          rfl
      · have hD:¬decide ((c≠8 ∧ h<4) ∨ (c=8 ∧ h=2))=true:=fun hx=>by
          have hx':=of_decide_eq_true hx
          omega
        have hr:rightPads pads h=(pads (h/2-2)).2:=by unfold rightPads;rw[if_pos ⟨by omega,hh8⟩]
        rw[if_neg hD,hr,if_neg h4,if_pos hh8]
        (try dsimp only)
        rw[if_neg hf]
        rfl
  · -- C1: heaps `≥ 8` are `wctNodeHashH`, whose half is `ftsHighHeap h`
    have hr:rightPads pads h=0:=by unfold rightPads;rw[if_neg (show ¬(4 ≤ h ∧ h < 8) by omega)]
    unfold SharedNode.hashProgram SharedForest.sharedNode
    rw[hr,SharedNode.high_ge8 c h (by omega),if_neg (show ¬h < 4 by omega),if_neg hh8,nodeHashH_eq,WCT9.ftsHash_eq]
    cases WCT9.ftsHighHeap h
    · rfl
    · rfl

theorem shared_order (c : Nat) :
    (List.range' (if SharedLeaf.first c then 4 else 2) (if SharedLeaf.first c then 124 else 126)).reverse=
      (List.range' 0 (SharedTree.count c)).map (fun k=>127-k) := by
  unfold SharedTree.count SharedTail.limit SharedTail.first SharedLeaf.first
  split_ifs <;> decide +kernel

theorem heapProgram_source (c index : Nat) (hc:c < 9) (pads : Nat → SharedForest.PairRoot) (leaves : List Digest) :
    SharedTree.heapProgram index c (rightPads pads) leaves=SharedForest.sharedHeap (SharedLeaf.first c) index c pads leaves := by
  unfold SharedTree.heapProgram SharedForest.sharedHeap
  rw[shared_order,List.foldlM_map]
  apply WCT9.foldlM_congr_mem
  intro nodes k hk
  have hk':k < SharedTree.count c:=by have:=List.mem_range'.mp hk;omega
  unfold SharedTree.stepProgram
  rw[hashProgram_source c index (127-k) hc (by unfold SharedTree.count at hk';have:=SharedTree.limit_bounds c;omega)]

 theorem program_source (c index : Nat) (hc:c < 9) (selected : WCT9.Child) (word : WCT9.Rank)
    (pads : Nat → SharedForest.PairRoot) :
    program index c selected.val word (fun j=>(pads (j/64)).1) (rightPads pads)=
      SharedForest.buildSharedCoordinate (SharedLeaf.first c) index c selected word pads := by
  unfold program rowsHeap SharedForest.buildSharedCoordinate
  apply bind_congr
  intro coefs
  have hraw:SharedNext.raw c=SharedForest.rawChild (SharedLeaf.first c):=rfl
  simp only[SharedLeaves.leafRows,hraw]
  apply bind_congr
  intro rows
  rw[heapProgram_source c index hc]
#print axioms program_source
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def priorPads (c : Nat) (nodes : Array Digest) (b : Nat) : SharedForest.PairRoot :=
  if c=0 then WCT9.ftsStart else if c%2=1 then SharedForest.nodesPair nodes b
  else (nodes.getD 2 0,nodes.getD 3 0)

theorem root_layout_prev (c : Nat) (hc:0 < c ∧ c < 9) :
    rootBase (c-1)=(if c%2=1 then 4 else 2) ∧ rootCount (c-1)=(if c%2=1 then 4 else 2) ∧
    SharedFinish.target (c-1)=(if c%2=1 then 0x67000+64*(c/2) else FORW+32*c) := by
  have h:∀c,c < 9 → 0 < c →
    rootBase (c-1)=(if c%2=1 then 4 else 2) ∧ rootCount (c-1)=(if c%2=1 then 4 else 2) ∧
    SharedFinish.target (c-1)=(if c%2=1 then 0x67000+64*(c/2) else FORW+32*c):=by decide +kernel
  exact h c hc.2 hc.1

theorem leaf_pads {c : Nat} (hc:c < 9) {nodes : Array Digest} {s : MachineState}
    (hr:c ≠ 0 → RootAt (c-1) nodes s) :
    ∀j,j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) ((priorPads c nodes (j/64)).1) s := by
  intro j hj
  unfold SharedLeaf.PadAt priorPads
  by_cases h0:c=0
  · simp only[h0,if_true,WCT9.ftsStart]
  · simp only[h0,if_false]
    obtain ⟨hb,hn,ht⟩:=root_layout_prev c ⟨by omega,hc⟩
    have hroot:=hr h0
    unfold RootAt at hroot
    by_cases ho:c%2=1
    · have hf:SharedNext.first c=false:=by apply decide_eq_false_iff_not.mpr;omega
      have hjd:(2*(j%64)+j/64)%2=j/64:=by omega
      have hh:=hroot (2*(j/64)) (by rw[hn,if_pos ho];omega)
      rw[hb,ht,if_pos ho]at hh
      simpa only[ho,if_true,SharedForest.nodesPair,SharedLeaf.padBase,SharedNext.raw,hf,Bool.false_eq_true,if_false,hjd,
        show 16*(2*(j/64))=32*(j/64) by omega]using hh
    · have hh:=hroot 0 (by rw[hn,if_neg ho];omega)
      rw[hb,ht,if_neg ho]at hh
      simpa only[ho,if_false,SharedLeaf.padBase,Nat.mul_zero,Nat.add_zero]using hh

theorem node_pads {c : Nat} (hc:c < 9) {nodes : Array Digest} {s : MachineState}
    (hr:c ≠ 0 → RootAt (c-1) nodes s) :
    ∀h,h < 128 → SharedNode.PadAt c h (rightPads (priorPads c nodes) h) s := by
  intro h hh
  unfold SharedNode.PadAt rightPads
  have hm:SharedNode.mode h=1 ↔ 4 ≤ h ∧ h < 8:=by
    unfold SharedNode.mode
    split_ifs <;> simp_all <;> omega
  by_cases hmid:4 ≤ h ∧ h < 8
  · rw[if_pos hmid]
    by_cases h0:c=0
    · simp only[h0,ne_eq,not_true_eq_false,and_false,if_false,priorPads,if_true,WCT9.ftsStart]
    · rw[if_pos ⟨hm.mpr hmid,h0⟩]
      obtain ⟨hb,hn,ht⟩:=root_layout_prev c ⟨by omega,hc⟩
      have hroot:=hr h0
      unfold RootAt at hroot
      by_cases ho:c%2=1
      · have hi:2*(h/2-2)+1 < rootCount (c-1):=by rw[hn,if_pos ho];omega
        have hd:=hroot (2*(h/2-2)+1) hi
        rw[hb,ht,if_pos ho]at hd
        simpa only[priorPads,h0,if_false,ho,if_true,SharedForest.nodesPair,SharedNode.padBase,
          show 16*(2*(h/2-2)+1)=16+32*(h/2-2) by omega,
          show 4+(2*(h/2-2)+1)=5+2*(h/2-2) by omega,Nat.add_assoc]using hd
      · have hd:=hroot 1 (by rw[hn,if_neg ho];omega)
        rw[hb,ht,if_neg ho]at hd
        simpa only[priorPads,h0,if_false,ho,SharedNode.padBase,Nat.mul_one,show 2+1=3 from rfl]using hd
  · rw[if_neg hmid,if_neg (fun h=>hmid (hm.mp h.1))]

#print axioms leaf_pads
#print axioms node_pads
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image} {sk : BitVec 256}

abbrev Row := Array Digest×List Digest
def emptyRow : Row := (#[],[])
def forestW (A : Nat) : Prop := ∃c,c < 9 ∧ coordinateW c A

def step (a : BitVec 256) (ranks : Nat → WCT9.Rank) (acc : List Row) (c : Nat) : M (List Row) := do
  let pads:=priorPads c (acc.getD (c-1) emptyRow).1
  let row←program (WCT9.digestIndex a) c (chosen c a) (ranks c) (fun j=>(pads (j/64)).1) (rightPads pads)
  pure (acc++[row])
def forestProgram (a : BitVec 256) (ranks : Nat → WCT9.Rank) : M (List Row) :=
  (List.range 9).foldlM (step a ranks) []

structure SigAt (c sel : Nat) (rv : Row) (s : MachineState) : Prop where
  values : rv.2.length=6 ∧ ∀i,i < 6 → DigAt s (slotV c i) (rv.2.getD i 0)
  paths : ∀l,l < SharedPath.levels c → DigAt s (SharedPath.target c l) (rv.1.getD (2^(7-l)+(sel/2^l ^^^1)) 0)
  dummy : SharedEnd.first c=true → DigAt s (SharedEnd.target c) 0

structure ForestInv (sk a : BitVec 256) (s0 : MachineState) (n : Nat) (rows : List Row) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if n < 9 then cbase n else 20715)
  ready : Ready sk a t
  length : rows.length=n
  prior : n ≠ 0 → RootAt (n-1) (rows.getD (n-1) emptyRow).1 t
  signatures : ∀j,j < n → SigAt j (chosen j a) (rows.getD j emptyRow) t
  regs : RegsExcept s0 t (.x25::.x24::.x18::bodyRegs)
  frame : Frame s0 t forestW

theorem writes_other_signature {c d A : Nat} (hc:c < 9) (hd:d < 9) (hne:c ≠ d)
    (ha:slotV d 0 ≤ A ∧ A < slotV d 0+208) : ¬coordinateW c A := by
  have hl:=SharedPath.levels_bound c
  intro hw
  unfold coordinateW allWrites writes FinalWrites at hw
  rcases hw with hw|((hw|hw)|(hw|(hw|hw)))
  all_goals first
    | (have hb:=target_range hc hw;unfold slotV at ha;rcases hb with hb|hb <;> aoh)
    | (simp only[SharedReuse.coefW,COEF,loopW,bodyW,treeW,SharedPath.target,SharedEnd.target,slotV,slotP]at *;aoh)

theorem SigAt.frame {c d sel : Nat} {rv : Row} {s t : MachineState} (hc:c < 9) (hd:d < 9) (hne:c ≠ d)
    (hs:SigAt d sel rv s) (hf:Frame s t (coordinateW c)) : SigAt d sel rv t := by
  have hl:=SharedPath.levels_bound d
  refine ⟨⟨hs.values.1,?_⟩,?_,?_⟩
  · intro i hi
    exact (hs.values.2 i hi).frame hf (by unfold slotV;ao)
      (writes_other_signature hc hd hne (by unfold slotV;constructor <;> omega))
      (writes_other_signature hc hd hne (by unfold slotV;constructor <;> omega))
  · intro l hll
    exact (hs.paths l hll).frame hf (by unfold SharedPath.target slotV;ao)
      (writes_other_signature hc hd hne (by unfold SharedPath.target slotV;constructor <;> omega))
      (writes_other_signature hc hd hne (by unfold SharedPath.target slotV;constructor <;> omega))
  · intro hfirst
    exact (hs.dummy hfirst).frame hf (by unfold SharedEnd.target slotP;ao)
      (writes_other_signature hc hd hne (by unfold SharedEnd.target slotP slotV;constructor <;> omega))
      (writes_other_signature hc hd hne (by unfold SharedEnd.target slotP slotV;constructor <;> omega))

theorem getD_append_old {α : Type} (xs : List α) (v z : α) (i : Nat) (hi:i < xs.length) :
    (xs++[v]).getD i z=xs.getD i z := by
  simp only[List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
theorem getD_append_new {α : Type} (xs : List α) (v z : α) : (xs++[v]).getD xs.length z=v := by
  rw[List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),Nat.sub_self]
  rfl

def forestStepBound : Nat := 19+(14+27*SharedReuse.coefStepC+(128*SharedLeaves.cost+126*68+110))
theorem cost_le (c : Nat) : cost c ≤ forestStepBound := by
  have:=SharedTree.limit_bounds c
  unfold cost forestStepBound SharedTree.count
  omega

theorem nextPc_eq (c : Nat) (hc:c < 9) : SharedEnd.nextPc c=(if c+1 < 9 then cbase (c+1) else 20715) := by
  have h:∀c,c < 9 → SharedEnd.nextPc c=(if c+1 < 9 then cbase (c+1) else 20715):=by decide +kernel
  exact h c hc

theorem forest_step (hf:SharedReuse.Fetch im) (hcode:∀c,c < 9 → Code im c)
    (a : BitVec 256) (ranks : Nat → WCT9.Rank) (hranks:∀c,c < 9 → (ranks c).val=rank c a)
    {s0 : MachineState} (c : Nat) (hc:c < 9) (acc : List Row) (s : MachineState)
    (hs:ForestInv sk a s0 c acc s) :
    TBSim im sk s forestStepBound (step a ranks acc c) (ForestInv sk a s0 (c+1)) := by
  have hrank:rank c a < 563:=(hranks c hc) ▸ (ranks c).isLt
  have he: (⟨rank c a,hrank⟩:WCT9.Rank)=ranks c:=Fin.ext (hranks c hc).symm
  unfold step
  have hrun:=coordinate hf hc (hcode c hc) a hrank s (by simpa only[if_pos hc]using hs.pc) hs.ready
    (leaf_pads hc hs.prior) (node_pads hc hs.prior)
  rw[he]at hrun
  refine (TBSim.bind (W₂:=0) hrun (fun rv t ht=>TBSim.pure ?_)).mono (by have:=cost_le c;omega) (fun _ _ h=>h)
  refine ⟨ht.1.out.pc.trans (congrArg pcOf (nextPc_eq c hc)),ht.2,by simp[hs.length],?_,?_,?_,?_⟩
  · intro _
    simpa only[Nat.add_sub_cancel_right,←hs.length,getD_append_new]using ht.1.out.roots
  · intro j hj
    by_cases hjc:j=c
    · subst j
      simpa only[←hs.length,getD_append_new]using (⟨ht.1.out.values,ht.1.out.paths,ht.1.out.dummy⟩:SigAt c (chosen c a) rv t)
    · rw[getD_append_old _ _ _ _ (by rw[hs.length];omega)]
      exact (hs.signatures j (by omega)).frame hc (by omega) (by omega) ht.1.frame
  · exact (hs.regs.trans ht.1.regs).mono (by simp[bodyRegs])
  · exact (hs.frame.trans ht.1.frame).mono (fun A _ h=>h.elim id (fun h=>⟨c,hc,h⟩))

theorem forest_loop (hf:SharedReuse.Fetch im) (hcode:∀c,c < 9 → Code im c)
    (a : BitVec 256) (ranks : Nat → WCT9.Rank) (hranks:∀c,c < 9 → (ranks c).val=rank c a)
    (s : MachineState) (hpc:s.pc=pcOf (cbase 0)) (hs:Ready sk a s) :
    TBSim im sk s (9*forestStepBound) (forestProgram a ranks) (ForestInv sk a s 9) := by
  unfold forestProgram
  rw[List.range_eq_range']
  exact TBSim.foldlM_range' 0 9 _ _ (ForestInv sk a s) forestStepBound
    (fun c hc acc t ht=>by simpa only[Nat.zero_add]using forest_step hf hcode a ranks hranks c hc acc t ht)
    ⟨by simpa using hpc,hs,rfl,by simp,by simp,RegsExcept.refl _ _,Frame.refl _ _⟩
#print axioms forest_loop
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def buildNine (index : Nat) (selected : Nat → WCT9.Child) (words : Nat → WCT9.Rank) : M (List Row) :=
  (List.range 9).foldlM (fun acc c=>do
    let built←SharedForest.buildSharedCoordinate (SharedLeaf.first c) index c (selected c) (words c)
      (priorPads c (acc.getD (c-1) emptyRow).1)
    pure (acc++[built])) []

def childFamily (selected : SharedForest.ForestSelection) (c : Nat) : WCT9.Child :=
  if h:c < 8 then
    if c%2=0 then SharedForest.firstChild (selected.pairs ⟨c/2,by omega⟩)
    else SharedForest.secondChild (selected.pairs ⟨c/2,by omega⟩)
  else selected.singleton

def wordFamily (words : SharedForest.ForestWords) (c : Nat) : WCT9.Rank :=
  if h:c < 8 then
    if c%2=0 then words.first ⟨c/2,by omega⟩ else words.second ⟨c/2,by omega⟩
  else words.singleton

def forestAssembly (selected : SharedForest.ForestSelection) (rows : List Row) :
    SharedForest.ForestOpening×SharedForest.PairRoot :=
  (⟨fun p=>⟨fun i=>(rows.getD (2*p.val) emptyRow).2.getD i.val 0,
    fun i=>SharedForest.authAt (rows.getD (2*p.val) emptyRow).1 (SharedForest.firstChild (selected.pairs p)).val i.val,
    fun i=>(rows.getD (2*p.val+1) emptyRow).2.getD i.val 0,
    fun i=>SharedForest.authAt (rows.getD (2*p.val+1) emptyRow).1 (SharedForest.secondChild (selected.pairs p)).val i.val⟩,
    ⟨fun i=>(rows.getD 8 emptyRow).2.getD i.val 0,
     fun i=>SharedForest.authAt (rows.getD 8 emptyRow).1 selected.singleton.val i.val⟩⟩,
   ((rows.getD 8 emptyRow).1.getD 2 0,(rows.getD 8 emptyRow).1.getD 3 0))

theorem forestProgram_source (a : BitVec 256) (ranks : Nat → WCT9.Rank) :
    forestProgram a ranks=buildNine (WCT9.digestIndex a) (fun c=>⟨chosen c a,chosen_lt c a⟩) ranks := by
  unfold forestProgram buildNine
  apply WCT9.foldlM_congr_mem
  intro acc c hc
  unfold step
  dsimp only
  rw[program_source c (WCT9.digestIndex a) (List.mem_range.mp hc) ⟨chosen c a,chosen_lt c a⟩ (ranks c) (priorPads c (acc.getD (c-1) emptyRow).1)]

theorem buildNine_grouped (index : Nat) (selected : SharedForest.ForestSelection) (words : SharedForest.ForestWords) :
    forestAssembly selected <$> buildNine index (childFamily selected) (wordFamily words)=
      SharedForest.buildForest index selected words := by
  have hn:List.range 9=[0,1,2,3,4,5,6,7,8]:=by decide
  have hp:List.finRange 4=[0,1,2,3]:=by decide
  simp only[buildNine,SharedForest.buildForest,hn,hp,List.foldlM_cons,List.foldlM_nil,
    SharedForest.buildPair,SharedForest.buildSingleton,bind_assoc,pure_bind,map_eq_bind_pure_comp,Function.comp_def]
  apply bind_congr
  intro row0
  apply bind_congr
  intro row1
  apply bind_congr
  intro row2
  apply bind_congr
  intro row3
  apply bind_congr
  intro row4
  apply bind_congr
  intro row5
  apply bind_congr
  intro row6
  apply bind_congr
  intro row7
  apply bind_congr
  intro row8
  apply congrArg pure
  unfold forestAssembly
  apply Prod.ext
  · refine congrArg₂ SharedForest.ForestOpening.mk ?_ rfl
    funext p
    fin_cases p <;> rfl
  · rfl
#print axioms buildNine_grouped
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

theorem childFamily_output (a : BitVec 256) (c : Nat) (hc:c < 9) :
    childFamily (SharedForest.forestSelectionFromOutput a) c = ⟨chosen c a,chosen_lt c a⟩ := by
  have hp : (⟨chosen c a,chosen_lt c a⟩ : WCT9.Child) =
      SharedForest.physicalChildFromOutput a ⟨c,hc⟩ := rfl
  rw [hp]
  interval_cases c
  all_goals first
    | exact (SharedForest.physicalFromOutput_first a 0).symm
    | exact (SharedForest.physicalFromOutput_first a 1).symm
    | exact (SharedForest.physicalFromOutput_first a 2).symm
    | exact (SharedForest.physicalFromOutput_first a 3).symm
    | exact (SharedForest.physicalFromOutput_second a 0).symm
    | exact (SharedForest.physicalFromOutput_second a 1).symm
    | exact (SharedForest.physicalFromOutput_second a 2).symm
    | exact (SharedForest.physicalFromOutput_second a 3).symm
    | exact (SharedForest.physicalFromOutput_singleton a).symm

theorem wordFamily_output (a : BitVec 256) (c : Nat) (hc:c < 9) :
    wordFamily (SharedForest.forestWordsFromOutput a) c = SharedForest.forestRank a c := by
  interval_cases c <;> rfl

theorem forestProgram_output (a : BitVec 256) :
    forestAssembly (SharedForest.forestSelectionFromOutput a) <$>
      forestProgram a (SharedForest.forestRank a) =
      SharedForest.buildForest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a) := by
  rw [forestProgram_source]
  have h : buildNine (WCT9.digestIndex a) (fun c=>⟨chosen c a,chosen_lt c a⟩)
      (SharedForest.forestRank a) = buildNine (WCT9.digestIndex a)
      (childFamily (SharedForest.forestSelectionFromOutput a))
      (wordFamily (SharedForest.forestWordsFromOutput a)) := by
    unfold buildNine
    apply WCT9.foldlM_congr_mem
    intro acc c hc
    rw [childFamily_output a c (List.mem_range.mp hc),wordFamily_output a c (List.mem_range.mp hc)]
  rw [h,buildNine_grouped]

theorem forestRank_val (a : BitVec 256) (c : Nat) (hc:rank c a < 563) :
    (SharedForest.forestRank a c).val = rank c a := Nat.mod_eq_of_lt hc

#print axioms forestProgram_output
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
variable {im : Image} {sk : BitVec 256}

def ForestPost (sk a : BitVec 256) (s0 : MachineState)
    (rv : SharedForest.ForestOpening × SharedForest.PairRoot) (t : MachineState) : Prop :=
  ∃ rows, rv=forestAssembly (SharedForest.forestSelectionFromOutput a) rows ∧ ForestInv sk a s0 9 rows t

theorem forest_good (hf:SharedReuse.Fetch im) (hcode:∀c,c < 9 → Code im c)
    (a : BitVec 256) (hranks:∀c,c < 9 → rank c a < 563)
    (s : MachineState) (hpc:s.pc=pcOf (cbase 0)) (hs:Ready sk a s) :
    TBSim im sk s (9*forestStepBound)
      (SharedForest.buildForest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a)) (ForestPost sk a s) := by
  rw [←forestProgram_output a,map_eq_bind_pure_comp]
  exact (TBSim.bind (W₂:=0)
    (forest_loop hf hcode a (SharedForest.forestRank a) (fun c hc=>forestRank_val a c (hranks c hc)) s hpc hs)
    (fun rows t ht=>TBSim.pure ⟨rows,rfl,ht⟩)).mono (by omega) (fun _ _ h=>h)

theorem ForestPost.roots {a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t) :
    t.pc=pcOf 20715 ∧ Ready sk a t ∧
    DigAt t (FORW+forOff 8) rv.2.1 ∧ DigAt t (FORW+forOff 8+16) rv.2.2 := by
  obtain ⟨rows,rfl,h⟩:=h
  have hp:=h.prior (by decide)
  exact ⟨h.pc,h.ready,hp 0 (by decide),hp 1 (by decide)⟩

#print axioms forest_good
#print axioms ForestPost.roots
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.Research
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

def openingValues (opened : SharedForest.ForestOpening) (coord : Fin 9) : Fin 6 → Digest :=
  if h:coord.val < 8 then
    if coord.val%2=0 then (opened.pairs ⟨coord.val/2,by omega⟩).firstValues
    else (opened.pairs ⟨coord.val/2,by omega⟩).secondValues
  else opened.singleton.values
def openingPath (opened : SharedForest.ForestOpening) (coord : Fin 9) (level : Nat) : Digest :=
  if h:coord.val < 8 then
    if coord.val%2=0 then (opened.pairs ⟨coord.val/2,by omega⟩).firstPath ⟨level%6,by omega⟩
    else (opened.pairs ⟨coord.val/2,by omega⟩).secondPath ⟨level%7,by omega⟩
  else opened.singleton.path ⟨level%7,by omega⟩

theorem assembly_values (selected : SharedForest.ForestSelection) (rows : List Row) (c : Fin 9) (i : Fin 6) :
    openingValues (forestAssembly selected rows).1 c i=(rows.getD c.val emptyRow).2.getD i.val 0 := by
  fin_cases c <;> rfl
theorem assembly_path (selected : SharedForest.ForestSelection) (rows : List Row) (c : Fin 9)
    (level : Nat) (hl:level < SharedPath.levels c.val) :
    openingPath (forestAssembly selected rows).1 c level=
      SharedForest.authAt (rows.getD c.val emptyRow).1 (childFamily selected c.val).val level := by
  fin_cases c <;> norm_num [SharedPath.levels] at hl <;>
    simp [openingPath,forestAssembly,childFamily,Nat.mod_eq_of_lt hl]

theorem ForestPost.values {sk a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t)
    (c : Fin 9) (i : Fin 6) : DigAt t (slotV c.val i.val) (openingValues rv.1 c i) := by
  obtain ⟨rows,rfl,h⟩:=h
  rw [assembly_values]
  exact (h.signatures c.val c.isLt).values.2 i.val i.isLt

theorem ForestPost.path {sk a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t)
    (c : Fin 9) (level : Nat) (hl:level < SharedPath.levels c.val) :
    DigAt t (SharedPath.target c.val level) (openingPath rv.1 c level) := by
  obtain ⟨rows,rfl,h⟩:=h
  rw [assembly_path _ _ c level hl,childFamily_output a c.val c.isLt]
  have h7:level < 7:=lt_of_lt_of_le hl (SharedPath.levels_bound c.val)
  unfold SharedForest.authAt
  rw [Nat.add_comm 128, pathIdx_eq _ (chosen_lt c.val a) level h7]
  exact (h.signatures c.val c.isLt).paths level hl

theorem ForestPost.dummy {sk a : BitVec 256} {s0 t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} (h:ForestPost sk a s0 rv t)
    (c : Fin 9) (hc:SharedEnd.first c.val=true) : DigAt t (SharedEnd.target c.val) 0 := by
  obtain ⟨rows,rfl,h⟩:=h
  exact (h.signatures c.val c.isLt).dummy hc

#print axioms ForestPost.path
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
structure Entry (sk a : BitVec 256) (s : MachineState) : Prop where
  pc : s.pc=pcOf 11175
  x5 : s.getReg .x5=0
  x22 : s.getReg .x22=BitVec.ofNat 64 (WCT9.digestIndex a)
  nbuf : OutAt s NBUF a
  table : TableAt s
  secret : ∀i,i<4 → s.getMem (BitVec.ofNat 64 (SK+8*i))=sk.extractLsb' (64*i) 64
  zero : ∀A,ZeroCell A → s.getMem (BitVec.ofNat 64 A)=0

def FinalW (A : Nat) : Prop := A=0x20290+8 ∨ A=0x20290 ∨ A=FOUT+8 ∨ A=FOUT
structure ClosedPost (sk a : BitVec 256) (s0 : MachineState)
    (rv : SharedForest.ForestOpening×SharedForest.PairRoot) (t : MachineState) : Prop where
  pc : t.pc=pcOf 370
  x5 : t.getReg .x5=0
  rootLeft : DigAt t FOUT rv.2.1
  rootRight : DigAt t 0x20290 rv.2.2
  values : ∀c : Fin 9,∀i : Fin 6,DigAt t (slotV c.val i.val) (openingValues rv.1 c i)
  paths : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt t (SharedPath.target c.val l) (openingPath rv.1 c l)
  dummy : ∀c : Fin 9,SharedEnd.first c.val=true → DigAt t (SharedEnd.target c.val) 0
  frame : Frame s0 t (fun A=>A=PRIVW+40 ∨ A=PRIVW+32 ∨ A=PRIVW+8 ∨ A=PRIVW ∨ forestW A ∨ FinalW A)

theorem forest_boundary_good {im : Image} {sk a : BitVec 256}
    (hf:SharedReuse.Fetch im) (hcode:∀c,c<9 → Code im c)
    (hfor:LookOK im SharedBoundary.forLook) (hranks:∀c,c<9 → rank c a<563)
    (s : MachineState) (hp:Entry sk a s) :
    TBSim im sk s (9*forestStepBound+23)
      (SharedForest.buildForest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a)) (ClosedPost sk a s) := by
  obtain ⟨u,su,pu,k1,k2,ru,fu⟩:=SharedBoundary.step_SK hf.head s hp.pc
  have gm : ∀A,A<2^64 → A≠PRIVW+40 → A≠PRIVW+32 → A≠PRIVW+8 → A≠PRIVW →
      u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4;exact fu.get hA (by simp [h1,h2,h3,h4])
  have hu : Ready sk a u := by
    refine ⟨(ru.get (by decide)).trans hp.x5,(ru.get (by decide)).trans hp.x22,?_,?_,?_,?_,?_,?_,?_⟩
    · intro k hk;rw [gm _ (by ao) (by ao) (by ao) (by ao) (by ao)];exact hp.nbuf k hk
    · intro k hk;rw [gm _ (by ao) (by ao) (by ao) (by ao) (by ao)];exact hp.table k hk
    · simpa only [Nat.mul_zero,Nat.add_zero] using (k1 0 (by decide)).trans (hp.secret 0 (by decide))
    · simpa only [Nat.mul_one] using (k1 1 (by decide)).trans (hp.secret 1 (by decide))
    · simpa only [Nat.mul_zero,Nat.add_zero] using (k2 0 (by decide)).trans (hp.secret 2 (by decide))
    · exact (k2 1 (by decide)).trans (hp.secret 3 (by decide))
    · intro A hA
      rw [gm _ (by unfold ZeroCell ScrZero at hA;aoh) (by unfold ZeroCell ScrZero at hA;aoh)
        (by unfold ZeroCell ScrZero at hA;aoh) (by unfold ZeroCell ScrZero at hA;aoh) (by unfold ZeroCell ScrZero at hA;aoh)]
      exact hp.zero A hA
  rw [←bind_pure (SharedForest.buildForest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a))]
  refine (TBSim.steps su (TBSim.bind (W₂:=12) (forest_good hf hcode a hranks u pu hu) (fun rv v hv=>?_))).mono (by omega) (fun _ _ h=>h)
  obtain ⟨pv,ready,l,r⟩:=hv.roots
  obtain ⟨t,vt,pt,m0,m8,m16,m24,rt,ft⟩:=SharedBoundary.step_For hfor v pv
  have hslot : ∀A,28672≤A → A<32000 → ¬FinalW A := by simp only [FinalW,FOUT];omega
  refine TBSim.pure_steps' vt ⟨pt,(rt.get (by decide)).trans ready.x5,⟨m0.trans l.1,m8.trans l.2⟩,
    ⟨m16.trans r.1,by simpa [Nat.add_assoc] using m24.trans r.2⟩,?_,?_,?_,?_⟩
  · intro c i
    have hc:=c.isLt;have hi:=i.isLt
    exact (hv.values c i).frame ft (by unfold slotV SIG;omega)
      (hslot _ (by unfold slotV SIG;omega) (by unfold slotV SIG;omega))
      (hslot _ (by unfold slotV SIG;omega) (by unfold slotV SIG;omega))
  · intro c l hl
    have hc:=c.isLt;have hb:=SharedPath.levels_bound c.val
    exact (hv.path c l hl).frame ft (by unfold SharedPath.target slotV SIG;omega)
      (hslot _ (by unfold SharedPath.target slotV SIG;omega) (by unfold SharedPath.target slotV SIG;omega))
      (hslot _ (by unfold SharedPath.target slotV SIG;omega) (by unfold SharedPath.target slotV SIG;omega))
  · intro c hc
    have hcb:=c.isLt
    exact (hv.dummy c hc).frame ft (by unfold SharedEnd.target slotP SIG;omega)
      (hslot _ (by unfold SharedEnd.target slotP SIG;omega) (by unfold SharedEnd.target slotP SIG;omega))
      (hslot _ (by unfold SharedEnd.target slotP SIG;omega) (by unfold SharedEnd.target slotP SIG;omega))
  · obtain ⟨rows,he,hv⟩:=hv
    exact ((fu.trans hv.frame).trans ft).mono (by intro A hA h;rcases h with ((h|h)|h)|h <;> tauto)
#print axioms forest_boundary_good
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate
