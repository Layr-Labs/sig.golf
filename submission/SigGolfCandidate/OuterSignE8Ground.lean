import SigGolfCandidate.OuterSignStubBlocks
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignE8Ground
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash nonceBytes pad64)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.FtsGrind
open OuterSignStubBlocks
variable {sk : BitVec 256} {tb ret heap A D : Nat} {pre mid right : List UInt8} {s : MachineState}
  (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
  (F : SignIn tb ret heap A D pre mid right s)
include hT F
theorem gexit {n : Nat} {a : HashOutput} {v : MachineState} (hg : 8 ≤ heap ∧ heap < 16)
    (hv : AtG s tb A D 25330 n v) (hh : HashedS v A D n a) :
    TBSim OuterImages.signImage sk v 11 (pure (n, a)) (SignOut s ret heap D (2 - signR tb)) := by
  have hb := F.hb; have hret := F.hret; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1
  have hD2 := F.hD2; have hAD := F.hAD
  obtain ⟨t1, s1, p1, x14, x17, x31, r1, m32, m04, m12, m28, f1⟩ :=
    d_spec v hv.pc A (tb + 2) (by rw [hv.regs.get (by decide)]; exact F.x10) F.hA hA1 hA2 hv.x16
  obtain ⟨t2, s2, p2, x16, r2, m36, f2⟩ := tramp_tail hT hb hret t1 p1
  have t2m : ∀ X, X < 2 ^ 64 → X ≠ 1136 → t2.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => f2.get hX h
  have t1m : ∀ X, X < 2 ^ 64 → X ≠ A + 32 → X ≠ 1104 → X ≠ 1112 → X ≠ 1128 →
      t1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) := fun X hX a b c d =>
    f1.get hX (by rintro (h | h | h | h) <;> contradiction)
  refine tb_pure_steps (s1.trans s2) ⟨p2, ?_, ?_, ?_, ?_, m36, fun _ => ?_, fun h => absurd hg h, ⟨fun _ => hv.hn, fun h => absurd hg h⟩, ?_⟩
  · intro r _
    by_cases h16 : r = .x16
    · subst h16; rw [x16, t1m _ (by decide) (by omega) (by decide) (by decide) (by decide), hv.sv4]
    rw [r2.get (by simpa using h16)]
    by_cases hr : r ∈ [Reg.x14, .x17, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x14, hv.sv0]
      · rw [x17, hv.sv1]
      · rw [x31, hv.sv3]
    · have hr' : r ∉ sgRegs := by
        simp only [sgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
      rw [r1.get hr, hv.regs.get hr']
  · intro k hk
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by omega) (by omega) (by omega), hh.ans k hk]
  · rw [t2m _ (by decide) (by decide)]; exact m04
  · rw [t2m _ (by decide) (by decide)]; exact m12
  · rw [t2m _ (by decide) (by decide)]; exact m28
  · intro X hX hn
    by_cases hp : X = A + 32
    · subst hp
      rw [t2m _ hX (by omega), m32, (F.ground (Or.inl hg)).1]
    · have h1 : ¬ GW A D X := by unfold GW; exact fun h => h.elim hp hn
      rw [t2m _ hX (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h))))),
        t1m _ hX hp (fun h => hn (Or.inr (Or.inl h))) (fun h => hn (Or.inr (Or.inr (Or.inl h))))
          (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h))))), hv.frame.get hX h1]

/-- One ground trial: pad `n`, then the hash of the trial block into `D`. -/
theorem gtrial {β : Type} {n : Nat} {u : MachineState} (hg : 8 ≤ heap ∧ heap < 16)
    (hu : AtG s tb A D 25319 n u) {W : Nat} {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a w, AtG s tb A D 25321 n w → HashedS w A D n a → TBSim OuterImages.signImage sk w W (f a) Q) :
    TBSim OuterImages.signImage sk u (1 + (8 + W)) (publicHash (trialInput pre n right) >>= f) Q := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1; have hD2 := F.hD2
  have hAD := F.hAD
  have hnF : n < 2 ^ 64 := by
    have h1 := hu.hn
    rw [fuelR _ (signR_lt tb)] at h1
    have := Nat.div_le_self 511 (2 ^ signR tb)
    omega
  have g10 : u.getReg .x10 = BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)]; exact F.x10
  obtain ⟨u1, s1, p1, r1, m32, f1, fe1⟩ := sg_sl_spec u hu.pc A g10 hA hA2
  rw [hu.x17] at m32
  have fs1 : Frame s u1 (GW A D) := (hu.frame.trans f1).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inl h)
  have g1 : ∀ x, x ∉ sgRegs → u1.getReg x = s.getReg x := fun x hx => by
    rw [r1.get (by simp), hu.regs.get hx]
  have h12 : u1.getReg .x12 = BitVec.ofNat 64 D := by rw [g1 _ (by decide)]; exact F.x12
  have hl := trialInput_length pre right n F.lpre F.lright
  have notW : ∀ X, A ≤ X → X < A + 64 → X ≠ A + 32 → ¬ GW A D X := fun X h1 h2 h3 hw => by
    unfold GW SignW at hw; omega
  have m40 : u1.getMem (BitVec.ofNat 64 (A + 40)) = 0 := by
    rw [fs1.get (by omega) (notW _ (by omega) (by omega) (by omega))]; exact (F.ground (Or.inl hg)).2
  have hq : hashInput u1 = toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u1 _ 0 A hl (by rw [g1 _ (by decide)]; exact F.x10) hA (by omega)
      (by rw [g1 _ (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_add, readWords_add,
      frame_readWordsG fs1 A 4 (by omega) (fun i hi => notW _ (by omega) (by omega) (by omega)),
      show A + 8 * 4 = A + 32 by ring, readWords_two, m32, m40, show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG fs1 (A + 48) 2 (by omega) (fun i hi => notW _ (by omega) (by omega) (by omega)),
      F.mpre, F.mright, trialInput, wordsOf_append _ _ (by rw [List.length_append, F.lpre]; simp [nonceBytes,
        bytesLE_length]), wordsOf_append _ _ (by rw [F.lpre]), nonce_words n hnF]
  have hv : hashArgumentsValid u1 = true := hashArgs_const u1 A 64 D (by rw [g1 _ (by decide)]; exact F.x10)
    (by rw [g1 _ (by decide)]; exact F.x11) h12 hA (by norm_num) hA2 F.hD hD2
  have h5 : u1.getReg .x5 = 0 := by rw [g1 _ (by decide)]; exact F.x5
  have e := tb_pub (sk := sk) (W := W) (f := f) (Q := Q) fe1 h5 hv hq (fun a => ?_)
  · have := TBSim.steps s1 e
    rwa [trial_blocks pre right n F.lpre F.lright] at this
  have hwf := Frame.writeHash u1 a D h12 (by omega)
  have fw : Frame s (writeHash u1 a) (GW A D) := (fs1.trans hwf).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inl h))
  have keep : ∀ X, X < 2 ^ 64 → ¬ (D ≤ X ∧ X < D + 32) →
      (writeHash u1 a).getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) := fun X hX h => hwf.get hX h
  have keepu : ∀ X, X < 2 ^ 64 → X ≠ A + 32 →
      u1.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := fun X hX h1 => f1.get hX h1
  refine h a (writeHash u1 a) ⟨by rw [pc_writeHash, p1, pcOf_add4], fun x hx => by rw [getReg_writeHash, g1 x hx],
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x16, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x17,
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x31,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv0,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv1,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv3,
    by rw [keep _ (by decide) (by omega), keepu _ (by decide) (by omega)]; exact hu.sv4,
    fw, hu.hn⟩ ⟨fun k hk => ?_, by rw [keep _ (by omega) (by omega)]; exact m32⟩
  rw [getMem_writeHash u1 a D _ h12 (by omega) (by omega)]
  interval_cases k <;> simp

theorem gloop (hg : 8 ≤ heap ∧ heap < 16) : ∀ fuel n u, AtG s tb A D 25319 n u →
    n + fuel = FUEL (2 - signR tb) →
    TBSim OuterImages.signImage sk u (18 * fuel + 27) (search (2 - signR tb) pre right fuel n) (SignOut s ret heap D (2 - signR tb)) := by
  have hr := signR_lt tb
  have hF := fuelR _ hr
  have hFl : FUEL (2 - signR tb) < 2 ^ 64 := by rw [hF]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)
  have hD := F.hD; have hD2 := F.hD2
  have test : ∀ n a w, AtG s tb A D 25321 n w → HashedS w A D n a → ∃ w1, Steps OuterImages.signImage w 4 4 w1 ∧
      AtG s tb A D (if zeroOk (2 - signR tb) a = true then 25330 else 25325) n w1 ∧ HashedS w1 A D n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := sc_spec w hw.pc D (by rw [hw.regs.get (by decide)]; exact F.x12) hD
      (by omega) _ hw.x31 hr
    have e : (w.getMem (BitVec.ofNat 64 (D + 8))).toNat < 2 ^ (62 + signR tb) ↔
        zeroOk (2 - signR tb) a = true := by
      rw [zeroOk_iff a _ hr]
      have := hh.ans 1 (by decide)
      simp only [Nat.mul_one] at this
      rw [this]
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move F f1⟩
    rw [p1]; by_cases hz : zeroOk (2 - signR tb) a = true
    · rw [if_pos (e.mpr hz), if_pos hz]
    · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
  have capT : ∀ n a w, AtG s tb A D 25325 n w → HashedS w A D n a → ∃ w1, Steps OuterImages.signImage w 3 3 w1 ∧
      AtG s tb A D (if n = FUEL (2 - signR tb) then 25330 else 25328) n w1 ∧ HashedS w1 A D n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := sg_sn_spec w hw.pc _ hw.x31 hr
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move F f1⟩
    have hnl : n < 2 ^ 64 := by have := hw.hn; omega
    rw [p1, hw.x17]
    by_cases hz : n = FUEL (2 - signR tb)
    · rw [if_pos (by rw [hz, hF]), if_pos hz]
    · rw [if_neg (fun h => hz ((ofNat_inj hnl hFl).mp (h.trans (congrArg _ hF.symm)))), if_neg hz]
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hn
    simp only [Nat.add_zero] at hn
    rw [search_eq]
    refine (gtrial hT F hg hu (W := 18) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOk (2 - signR tb) a = true
    · rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (gexit hT F hg hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_pos hn] at hw2
      exact TBSim.steps s1 (TBSim.steps s2 (gexit hT F hg hw2 hh2))
  | succ fuel ih =>
    intro n u hu hn
    rw [search_eq]
    refine (gtrial hT F hg hu (W := 18 * fuel + 36) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOk (2 - signR tb) a = true
    · rw [if_pos hz] at hw1
      simp only [sTail, hz, if_true]
      exact (TBSim.steps s1 (gexit hT F hg hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      simp only [sTail, hz, Bool.false_eq_true, if_false]
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_neg (by omega)] at hw2
      obtain ⟨w3, s3, p3, x17, r3, f3⟩ := sg_sj_spec w2 hw2.pc
      have hw3 : AtG s tb A D 25319 (n + 1) w3 := hw2.move p3 (r3.mono (by decide)) f3
        (by rw [x17, hw2.x17, ofNat_add_ofNat]) (by omega)
      have := TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (ih (n + 1) w3 hw3 (by omega))))
      exact this.mono (by omega) (fun _ _ h => h)

#print axioms gexit
#print axioms gtrial
#print axioms gloop
end OuterSignE8Ground
