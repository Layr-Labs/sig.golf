import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_PackedLeaf_A

set_option Elab.async false


namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest privateInput header)
open ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.T3M.Sign (LeafPreS)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (CoefW CoefSt coefC getD_append_last getD_append_lt getD_take_lt
  packedSecret_even packedSecret_odd lower_n lower_height pow_height_low famSize_low famGrp_low famBase_low hkLook
  lookOK_of_codeAt run_hk)
open ClaudeWCT.Arith
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem hook_spec {im : Image} (hh : CodeAt im (pcOf 1055) Sign.seedHookCode)
    (s : MachineState) (hp : s.pc=pcOf 1055) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 20746 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hl : LookOK im hkLook := lookOK_of_codeAt hh (by decide)
  obtain ⟨hs,hpc,_,hr,hm⟩ := piece hl run_hk s hp rfl (by intro b hb; cases hb) rfl
  exact ⟨_,hs,hpc,fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x,
    fun A _ _ => by rw [hm]; rfl⟩
section coef
variable {im : Image} (hsub : Sign.SharedLeafCode.Code im 1013) (hnew : SharedSeed.Code im)
  (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode)
variable (sk : BitVec 256) {s0 s t : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre hsub hnew hhook

theorem coef_phase (hlay : A.lay ≠ 0) (ht : LeafInv s A 0 ([], []) t) (hs : HybOf s0 s t)
    (hpc : t.pc = pcOf (1013 + 41)) {carry : List Digest}
    (hcar : A.leaf % 7 ≠ 0 → SharedSeed.FamBuf t carry) :
    TBSim im sk t coefC (WCT9.lowerCoefs A.lay A.tree A.leaf carry)
      (fun r u => u.pc = pcOf seedI ∧ SharedSeed.FamBuf u r.1 ∧ r.2 = r.1 ∧
        RegsExcept t u PackedLeaf.coefRegs ∧ Frame t u CoefW) := by
  have hn : A.n = 43 := lower_n hlay
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hlay0 : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hlh := hpre.hleafHeight
  have h2h := pow_height_low hlay
  have hleaf : A.leaf < (if A.lay.val = 1 then 128 else 64) := by rw [← h2h]; exact hlh
  have hleaf' : A.leaf < 128 := by split at hleaf <;> omega
  have htree := hpre.htree
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => by rw [ht.regs.get hr, hs.regs]
  have r8 : t.getReg .x8 = BitVec.ofNat 64 A.lay.val := by rw [g _ (by simp [leafRegs]), hpre.x8]
  have r18 : t.getReg .x18 = BitVec.ofNat 64 A.leaf := by rw [g _ (by simp [leafRegs]), hpre.x18]
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  -- the secret key words of the private input
  have hLP : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → ¬ LeafW A X := by
    intro X hX hw
    have h1 := hpre.hds; have h2 := hpre.hdv; have h3 := hpre.hvs
    unfold LeafW at hw
    rw [if_neg hlay] at hw
    simp only [PRIV, SEEDS, CHAIN, LEAFPK, LOUT] at hX hw h1 h2 h3
    omega
  have frT : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (ht.frame.get (by simp only [PRIV] at hX; omega) (hLP X hX)).trans
      (hs.base.get (by simp only [PRIV] at hX; omega) (not_bscr (by simp only [PRIV] at hX; omega)))
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.SharedLeaf.sub41_spec hsub t hpc 0 A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := hook_spec hhook t1 (by rw [t1pc])
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := SharedSeed.step_D0 hnew t2 t2pc (lay := A.lay.val)
    (by rw [t2r.get (by simp), t1r.get (by simp), r8]) hlay0 hlay'
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x19)
  have e13 : RegsExcept t t3 [] := ((t1r.trans t2r).trans t3r).mono (by simp)
  have f13 : Frame t t3 (fun _ => False) := ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)
  have q18 : t3.getReg .x18 = BitVec.ofNat 64 A.leaf := by rw [e13.get (by simp), r18]
  have q8 : t3.getReg .x8 = BitVec.ofNat 64 A.lay.val := by rw [e13.get (by simp), r8]
  unfold WCT9.lowerCoefs
  rw [famGrp_low hlay]
  by_cases h7 : A.leaf % 7 = 0
  swap
  · -- a later leaf of the family: the coefficients stay in `FB`
    rw [if_neg h7]
    obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := SharedSeed.step_QS hnew t3 t3pc q18 (by omega) h7
    refine TBSim.mono (TBSim.pure_steps' (st1.trans (st2.trans (st3.trans st4))) ⟨t4pc, ?_, rfl, ?_, ?_⟩)
      (by unfold coefC; omega) (fun _ _ h => h)
    · exact ((hcar h7).frame f13 (fun _ _ _ h => h)).frame t4f (fun _ _ _ h => h)
    · exact (e13.trans t4r).mono (by simp [PackedLeaf.coefRegs])
    · exact (f13.trans t4f).mono (fun X _ h => by simp_all)
  rw [if_pos h7]
  obtain ⟨N, hN⟩ : ∃ N, N = SharedSeed.famN A.lay.val A.leaf := ⟨_, rfl⟩
  obtain ⟨t4, k4, c4, st4, hc4, t4pc, t4x6, t4x17, t4x29, t4x30, t4end, t4r, t4f⟩ :=
    SharedSeed.step_QL hnew t3 t3pc q8 hlay' q18 hleaf h7
  rw [← hN] at t4x30 t4end
  have hNs : WCT9.famSize A.lay (A.leaf / 7) = N := by rw [hN]; exact famSize_low hlay A.leaf
  have hNb : 8 ≤ N ∧ N ≤ 38 := by
    have h7f : 7 * (A.leaf / 7) ≤ A.leaf := by omega
    rw [hN]; unfold SharedSeed.famN
    by_cases hl1 : A.lay.val = 1 <;> simp only [hl1, if_true, if_false] at hleaf ⊢ <;> omega
  have hPairs : WCT9.famPairs A.lay (A.leaf / 7) = (N + 1) / 2 := by unfold WCT9.famPairs; rw [hNs]
  have h0 : CoefSt t A.lay.val (A.leaf / 7) N 0 [] t4 := by
    refine ⟨?_, ?_, ?_, t4x17, t4x30, ?_, ?_, rfl, fun i hi => absurd hi (by omega), t4end⟩
    · rw [t4pc, if_pos (by omega)]
    · rw [t4x29, Nat.mul_zero, Nat.add_zero]
    · rw [t4x6, Nat.add_zero]
    · exact (e13.trans t4r).mono (by simp [PackedLeaf.coefRegs])
    · exact (f13.trans t4f).mono (fun X _ h => by
        rcases h with h | h
        · exact h.elim
        · left; subst h; simp only [SharedSeed.FB, SharedSeed.FEND]; omega)
  simp only [WCT9.lowerFamCoefs, WCT9.famOf, famGrp_low hlay, bind_assoc, pure_bind]
  rw [hPairs, hNs]
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) 0 ((N + 1) / 2)
    (fun (acc : List Digest) j => do
      let p ← WCT9.lowerSeedPair A.lay A.tree (WCT9.famBase A.lay * (A.leaf / 7) / 2 + j)
      pure (acc ++ [p.1, p.2])) [] (fun j acc u => CoefSt t A.lay.val (A.leaf / 7) N j acc u) 26
    (fun j hj acc u hu => ?_) h0
  · rw [show List.range' 0 ((N + 1) / 2) = List.range ((N + 1) / 2) from List.range_eq_range'.symm] at hloop
    refine TBSim.mono (TBSim.steps (st1.trans (st2.trans (st3.trans st4)))
      (TBSim.bind (W₂ := 0) hloop (fun acc u hu => TBSim.pure ?_))) (by unfold coefC; omega) (fun _ _ h => h)
    have hlen : (acc.take N).length = N := by rw [List.length_take, hu.len]; omega
    refine ⟨?_, ?_, rfl, hu.regs, hu.frame⟩
    · rw [hu.pc, if_neg (by omega)]
    show SharedSeed.FamBuf u (acc.take N)
    refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, fun k hk => ?_, ?_⟩
    · rw [hlen] at hk
      rw [getD_take_lt hk]
      exact hu.coefs k (by omega)
    · rw [hu.fend, hlen]
  -- one pair `19 f + j`
  simp only [Nat.zero_add]
  rw [famBase_low hlay, show 38 * (A.leaf / 7) / 2 + j = 19 * (A.leaf / 7) + j by omega]
  unfold WCT9.lowerSeedPair
  have g4 : ∀ r, r ∉ PackedLeaf.coefRegs → r ∉ leafRegs → u.getReg r = s0.getReg r := fun r h1 h2 => by
    rw [hu.regs.get h1, g r h2]
  obtain ⟨u1, su1, e1, u1pc, u1x10, u1x11, u1x12, u1x28, m16, m24, u1r, u1f⟩ :=
    SharedSeed.step_CQ hnew u (by rw [hu.pc, if_pos hj])
  have hm16 : u1.getMem (BitVec.ofNat 64 (PRIV + 16)) =
      BitVec.ofNat 64 (SigGolfCandidate.T3M.hdr0 0 A.lay.val A.tree (19 * (A.leaf / 7) + j)) := by
    show u1.getMem (BitVec.ofNat 64 0x20010) = _
    rw [m16, hu.x6, hdr0_eq 0 _ _ _ (by norm_num) hlay' htree (by omega)]
    (try simp only [hdrB, ClaudeWCT.W9.Machine.Sign.hdrB]); (try congr 1); (try ring)
  have hm24 : u1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (SigGolfCandidate.T3M.hdr1 A.tree 0) := by
    show u1.getMem (BitVec.ofNat 64 0x20018) = _
    rw [m24, g4 _ (by simp [PackedLeaf.coefRegs]) (by simp [leafRegs]), hpre.x9, hdr1_eq A.tree 0 htree (by norm_num)]
    congr 1
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → u1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX => by
    rw [u1f.get (by simp only [PRIV] at hX; omega) (by simp only [PRIV] at hX; omega),
      hu.frame.get (by simp only [PRIV] at hX; omega)
        (by unfold CoefW; simp only [SharedSeed.FB, SharedSeed.FEND, COEF, PRIV, SEEDS] at *; omega),
      frT X hX]
  have hqin : hashInput u1 =
      toQ (privateInput sk (.inl (header 0 A.lay.val A.tree (19 * (A.leaf / 7) + j) 0))) := by
    refine hashInput_toQ u1 _ 0 PRIV (privateInput_tweak_length _ _) u1x10 (by decide) (by decide) u1x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV + 8) (by simp), hm16, hm24, fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
      fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hpre.p0, hpre.p8, hpre.p32, hpre.p40,
      hpre.p48, hpre.p56]
    rfl
  have hva : hashArgumentsValid u1 = true :=
    hashArgs_const u1 PRIV 64 SEEDS u1x10 u1x11 u1x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : u1.getReg .x5 = 0 := by
    rw [u1r.get (by simp), g4 _ (by simp [PackedLeaf.coefRegs]) (by simp [leafRegs]), hpre.x5]
  refine TBSim.mono (TBSim.steps su1 (TBSim.privatePair_bind' (W := 12) e1 h5 hva hqin (fun a => ?_)))
    (by norm_num) (fun _ _ h => h)
  have hP8 : (SharedSeed.FB + 32 * j) % 8 = 0 := by unfold SharedSeed.FB COEF; omega
  obtain ⟨u3, k3, su3, hk3, u3pc, u3x29, u3x6, u3lo, u3hi, u3r, u3f⟩ := SharedSeed.step_CP hnew (writeHash u1 a)
    (by rw [pc_writeHash, u1pc, pcOf_add4]) (P := SharedSeed.FB + 32 * j)
    (Q := SharedSeed.FB + 32 * ((N + 1) / 2)) (by rw [getReg_writeHash]; exact u1x28)
    (by rw [getReg_writeHash, u1r.get (by simp), hu.x29]) (by rw [getReg_writeHash, u1r.get (by simp)]; exact hu.x30)
    hP8 (by unfold SharedSeed.FB COEF; omega) (by unfold SharedSeed.FB COEF; omega)
  have hwf := Frame.writeHash u1 a SEEDS u1x12 (by decide)
  have lo := DigAt.writeHash_lo u1 a SEEDS u1x12 (by decide)
  have hi := DigAt.writeHash_hi u1 a SEEDS u1x12 (by decide)
  have f13 : Frame u u3 (fun X => ((X = 0x20018 ∨ X = 0x20010) ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)) ∨
      (SharedSeed.FB + 32 * j ≤ X ∧ X < SharedSeed.FB + 32 * j + 32)) := (u1f.trans hwf).trans u3f
  refine TBSim.mono (TBSim.pure_steps' su3 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi' => ?_, ?_⟩)
    hk3 (fun _ _ h => h)
  · rw [u3pc]; congr 1; simp only [SharedSeed.cqI, SharedSeed.seedI]; split_ifs <;> omega
  · rw [u3x29, show SharedSeed.FB + 32 * j + 32 = SharedSeed.FB + 32 * (j + 1) by ring]
  · rw [u3x6, getReg_writeHash, getReg_writeHash, u1r.get (by simp), u1r.get (by simp), hu.x6, hu.x17,
      ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat 64) (by (try simp only [hdrB, ClaudeWCT.W9.Machine.Sign.hdrB]); ring)
  · rw [u3r.get (by simp), getReg_writeHash, u1r.get (by simp)]; exact hu.x17
  · rw [u3r.get (by simp), getReg_writeHash, u1r.get (by simp)]; exact hu.x30
  · exact ((hu.regs.trans u1r).trans ((show RegsExcept u1 (writeHash u1 a) [] from
      fun r _ => getReg_writeHash u1 a r).trans u3r)).mono (by simp [PackedLeaf.coefRegs])
  · exact (hu.frame.trans f13).mono (fun X _ h => by
      unfold CoefW at *
      simp only [SharedSeed.FB, SharedSeed.FEND, COEF, PRIV, SEEDS] at *
      omega)
  · simp [hu.len]; ring
  · by_cases hij : i < 2 * j
    · rw [List.getD_append _ _ _ _ (by rw [hu.len]; exact hij)]
      exact (hu.coefs i hij).frame f13 (by unfold SharedSeed.FB COEF; omega)
        (by unfold SharedSeed.FB COEF; simp only [SEEDS]; omega) (by unfold SharedSeed.FB COEF; simp only [SEEDS]; omega)
    · rw [List.getD_append_right _ _ _ _ (by rw [hu.len]; omega), hu.len]
      rcases (show i = 2 * j ∨ i = 2 * j + 1 by omega) with rfl | rfl
      · simp only [Nat.sub_self, List.getD_cons_zero]
        rw [show SharedSeed.FB + 16 * (2 * j) = SharedSeed.FB + 32 * j by ring]
        exact u3lo _ lo
      · simp only [show 2 * j + 1 - 2 * j = 1 by omega, List.getD_cons_succ, List.getD_cons_zero]
        rw [show SharedSeed.FB + 16 * (2 * j + 1) = SharedSeed.FB + 32 * j + 16 by ring]
        exact u3hi _ hi
  · rw [f13.get (by unfold SharedSeed.FEND COEF; omega)
      (by simp only [SharedSeed.FB, SharedSeed.FEND, COEF, SEEDS]; omega), hu.fend]
end coef

#print axioms coef_phase
end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Sign (LeafPreS)
set_option maxHeartbeats 1000000

def ends (prefixes : List (List Digest)) : List Digest := prefixes.map (fun vs => vs.getD 7 0)
def Selected (A : LeafArgs) (s : MachineState) : Prop :=
  SharedPrefixes.selectionWord (s.getMem 0x20550) A.lay.val = BitVec.ofNat 64 A.leaf

theorem LeafInv.selected {sk : BitVec 256} {s0 s t : MachineState} {A : LeafArgs}
    {j : Nat} {st : List Digest × List Digest} (hpre : LeafPreS sk s0 A)
    (hvi : A.valp+16*A.n≤0x20550 ∨ 0x20558≤A.valp)
    (hi : LeafInv s A j st t) (hs : HybOf s0 s t) (selected : Selected A s0) :
    SharedPrefixes.selectionWord (t.getMem 0x20550) A.lay.val=t.getReg .x18 := by
  have hindex : t.getMem 0x20550=s0.getMem 0x20550 := by
    have hd := hpre.hds
    have hc := chainCount_cases A.lay
    change t.getMem (BitVec.ofNat 64 0x20550)=s0.getMem (BitVec.ofNat 64 0x20550)
    rw [hi.frame.get (by decide) (by
      simp only [LeafW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT] at *
      split_ifs <;> omega),hs.base.get (by decide) (not_bscr (by decide))]
  rw [hindex,hi.regs.get (by decide),hs.regs,hpre.x18]
  exact selected

/-- The chain loop state of a lower leaf (v6: the family coefficients stay in the family buffer `FB`, `FamBuf`). -/
structure PSt (s0 : MachineState) (A : LeafArgs) (coefs : List Digest)
    (j : Nat) (prefixes : List (List Digest)) (u : MachineState) : Prop where
  pc : u.pc=pcOf (if j=0 then seedI else 1013+41)
  coef : SharedSeed.FamBuf u coefs
  inv : ∃ base values, HybOf s0 base u ∧ LeafInv base A j (ends prefixes,values) u
  len : prefixes.length=j
  saved : Selected A s0 → ∀ i, i<j → ∀ k, k≤7 →
    DigAt u (SharedPrefixes.buffer A.lay.val i k) ((prefixes.getD i []).getD k 0)
  /-- Pairing stage 1: after an F chain (even index) the F pads are zero. -/
  z : j % 2 = 1 → Sign.Seed.Z32 u

#print axioms LeafInv.selected
end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest M)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def prefixStep (A : LeafArgs) (coefs : List Digest) (prefixes : List (List Digest)) (j : Nat) : M (List (List Digest)) := do
  let vs ← chainPrefixes A.lay A.tree A.leaf j 0 7 (WCT9.lowerFamilySeed coefs A.lay A.leaf j)
  pure (prefixes++[vs])

def chainC : Nat := 5+lowerSeedC+679

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest M chainCount maxDigit)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.Packed (lowLeafC)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n lower_height lower_blocks coefC CoefW)
open SigGolfCandidate.Research.SharedForest (chainPrefixes buildLeafPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prefixEnds_eq (lay : Layer) (hlay : lay≠0) (prefixes : List (List Digest))
    (h : prefixes.length=43) :
    (List.range (chainCount lay)).map (fun i => (prefixes.getD i []).getD (maxDigit lay i) 0)=ends prefixes := by
  unfold ends
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,lower_n hlay,h]
  · intro i h1 h2
    have hi : i<43 := by simpa only [List.length_map,List.length_range,lower_n hlay] using h1
    simp only [List.getElem_map,List.getElem_range]
    have hm : maxDigit lay i=7 := by fin_cases lay <;> simp_all [maxDigit]
    rw [hm]
    exact congrArg (fun vs : List Digest => vs.getD 7 0) (List.getD_eq_getElem (l:=prefixes) (n:=i) (d:=[]) (by omega))

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n lower_e lower_sel)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A lower chain returns its retained source prefixes. The legacy reveal slots
are an internal ghost list; the canonical producer later reads its chosen prefix. -/
theorem chain_cont_unselected {im : Image}
    (hsub : Sign.SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Sign.Seed.sub61)
    (hc : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (sk : BitVec 256) {s0 s : MachineState} {A : LeafArgs}
    (hpre : LeafPreS sk s0 A) (hlay : A.lay ≠ 0) (hso : A.so=false)
    (hv : A.valp+16*A.n ≤ 0x50000) (hd : A.digp+A.n ≤ 0x50000)
    (hvi : A.valp+16*A.n ≤ 0x20550 ∨ 0x20558 ≤ A.valp)
    {j : Nat} (hj : j<A.n) {st : List Digest × List Digest}
    (t : MachineState) (seed carry : Digest)
    (hp : t.pc=pcOf (1013+61)) (ht : LeafInv s A j st t) (hs : HybOf s0 s t)
    (h28 : t.getReg .x28=0) (hseed : DigAt t SEEDS seed) (hcarry : DigAt t (SEEDS+16) carry)
    (hmiss : SharedPrefixes.selectionWord (t.getMem 0x20550) A.lay.val ≠ t.getReg .x18) :
    TBSim im sk t 679 (chainPrefixes A.lay A.tree A.leaf j 0 7 seed)
      (fun vs w => vs.length=8 ∧ w.pc=pcOf (1013+41) ∧
        ∃ base values, HybOf s0 base w ∧
          LeafInv base A (j+1) (st.1++[vs.getD 7 0],values) w ∧
          DigAt w (SEEDS+16) carry ∧
          Frame t w (fun X => Sign.Seed.ChainWS (A.valp+16*j) X ∨
            (slot A.lay j≤X ∧ X<slot A.lay j+16)) ∧
          (j % 2 = 0 → Sign.Seed.Z32 w)) := by
  have hn : A.n=43 := lower_n hlay
  have hvs := hpre.hvs
  have hl : 1≤A.lay.val := by
    have hz : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
    omega
  have preS : LeafPreS sk s A := LeafPreS.transfer hpre hs.regs hs.base hd
  obtain ⟨u,tu,upc,upre,uval,ur,uf⟩ := Sign.SharedLeaf.leaf_prechainFrom61S
    hsub sk preS hj (fun _ => (lower_e hlay hso j).le) ht hp seed 0 (by decide) (by simpa using h28) hcopy
    (by simpa using hseed)
  rw [lower_sel hlay,hso] at tu
  simp only [Bool.false_eq_true,if_false,Nat.add_zero] at tu
  have ue : A.e j=7 := lower_e hlay hso j
  rw [ue] at upre
  have umiss : SharedPrefixes.selectionWord (u.getMem 0x20550) A.lay.val ≠ u.getReg .x18 := by
    have idx : u.getMem 0x20550=t.getMem 0x20550 := uf 0x20550 (by decide) (by simp only [CHAIN]; omega)
    rw [idx,ur.get (by decide)]
    exact hmiss
  have run := SharedChain.unselected_chain hc hpref sk u upc A.lay A.tree A.leaf j 7 (A.d j)
    (A.valp+16*j) (1013+79) seed upre hl (by omega) (by omega) uval umiss
  refine (TBSim.steps tu (Sign.TBSim.of_eq (TBSim.bind (f := fun vs => pure vs) (W₂:=17) run (fun vs v ht' => ?_)) (bind_pure _) rfl)).mono (by omega) (fun _ _ h => h)
  have vr := ur.trans ht'.2.2.2.1
  have vf := uf.trans ht'.2.2.2.2.1
  have vS : HybOf s0 (hyb s0 v) v := hyb_of s0 v
  have vInv : LeafInv (hyb s0 v) A j st v := LeafInv.rebase_chain ht hs vS vr
    (by intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with h|h
        · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
        · simp only [SigGolfCandidate.T3M.Keygen.chainRegs,List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    vf (by
      intro X h
      change (X=CHAIN+48 ∨ X=CHAIN+56) ∨ Sign.Seed.ChainWS (A.valp+16*j) X at h
      unfold Sign.Seed.ChainWS at h; unfold BScr ChainW
      simp only [CHAIN] at *
      omega) hpre.hvs hv hj
  have preV : LeafPreS sk (hyb s0 v) A := LeafPreS.transfer hpre vS.regs vS.base hd
  obtain ⟨w,vw,wpc,winv,wf⟩ := Sign.SharedLeaf.leaf_postchainS hsub sk preV hj vInv ht'.2.1
    (RegsExcept.refl _ _) (Frame.refl _ _) (Sign.Packed.memDig v (A.valp+16*j))
    (vs.getD 7 0) (Sign.Packed.memDig_digAt _ _) ht'.2.2.1
  rw [hso] at vw winv
  simp only [Bool.false_eq_true,if_false] at vw winv
  have wc : 4+(11+slotK A.lay j)≤17 := by
    rw [Sign.Seed.slotK_low hlay]
    split_ifs <;> omega
  apply (TSim.pure_steps vw ?_).toTBSim (by omega) |>.mono wc (fun _ _ h => h)
  refine ⟨ht'.1,wpc,hyb s0 v,st.2++[Sign.Packed.memDig v (A.valp+16*j)],?_,winv,?_,?_,?_⟩
  · exact vS.frame wf (by
      intro X h
      have h1 := slot_ge A.lay j
      have h2 := slot_lt A.lay hj
      exact not_bscr (by simp only [LEAFPK] at *; omega))
  · refine ((hcarry.frame uf (by decide) (by simp only [SEEDS,CHAIN]; omega)
        (by simp only [SEEDS,CHAIN]; omega)).frame ht'.2.2.2.2.1 (by decide) ?_ ?_).frame
        wf (by decide) (by have := slot_ge A.lay j; simp only [SEEDS,LEAFPK] at *; omega)
        (by have := slot_ge A.lay j; simp only [SEEDS,LEAFPK] at *; omega)
    all_goals
      simp only [PRIV,LEAFPK] at hvs
      simp only [SharedChain.loopWrites,Sign.Seed.ChainWS,ChainW,CHAIN,SEEDS,SharedPrefixes.buffer]
      omega
  · exact (vf.trans wf).mono (by
      intro X hX h
      change ((X=CHAIN+48 ∨ X=CHAIN+56) ∨ Sign.Seed.ChainWS (A.valp+16*j) X) ∨ _ at h
      simp only [Sign.Seed.ChainWS,CHAIN] at *
      omega)
  · intro hj2
    have h1 := slot_ge A.lay j
    exact (ht'.2.2.2.2.2 (fun h => by omega) (by decide)).frame wf (by simp only [CHAIN,LEAFPK] at *; omega)
      (by simp only [CHAIN,LEAFPK] at *; omega)
end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open OracleComp SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest (chainPrefixes buildLeafPrefixes)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem mapM_bind_len {α γ β : Type} (f : γ → M α) :
    ∀ (xs : List γ) (g h : List α → M β), (∀ l : List α, l.length = xs.length → g l = h l) →
      (xs.mapM f >>= g) = (xs.mapM f >>= h)
  | [], g, h, H => by simp only [List.mapM_nil, pure_bind]; exact H [] rfl
  | x :: xs, g, h, H => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    congr 1
    funext a
    exact mapM_bind_len f xs (fun l => g (a :: l)) (fun l => h (a :: l))
      (fun l hl => H (a :: l) (by simp [hl]))

theorem chainPrefixes_bind_last {α : Type} (lay : Layer) (tree leaf i start count : Nat)
    (v : Digest) (f : Digest → M α) :
    (chainPrefixes lay tree leaf i start count v >>= fun vs => f (vs.getD count 0)) =
      (ClaudeWCT.WCT9.chainW lay tree leaf i start count v >>= f) := by
  induction count generalizing start v with
  | zero => simp only [chainPrefixes,ClaudeWCT.WCT9.chainW,List.range'_zero,List.foldlM_nil,pure_bind,List.getD_cons_zero]
  | succ count ih =>
    simp only [chainPrefixes,ClaudeWCT.WCT9.chainW,List.range'_succ,List.foldlM_cons,bind_assoc,pure_bind,List.getD_cons_succ]
    apply bind_congr
    intro v'
    exact ih _ _

theorem mapM_prefixEnds {α : Type} (lay : Layer) (tree leaf : Nat) (seed : Nat → Digest)
    (xs : List Nat) (k : List Digest → M α) :
    (xs.mapM (fun i => chainPrefixes lay tree leaf i 0 7 (seed i)) >>= fun ps => k (ends ps)) =
      (xs.mapM (fun i => ClaudeWCT.WCT9.chainW lay tree leaf i 0 7 (seed i)) >>= k) := by
  induction xs generalizing k with
  | nil => simp only [List.mapM_nil,pure_bind,ends,List.map_nil]
  | cons i xs ih =>
    simp only [List.mapM_cons,bind_assoc,pure_bind]
    change (chainPrefixes lay tree leaf i 0 7 (seed i) >>= fun vs =>
      xs.mapM (fun j => chainPrefixes lay tree leaf j 0 7 (seed j)) >>= fun ps =>
        k (vs.getD 7 0 :: ends ps)) = _
    have hh : ∀ vs : List Digest, ((xs.mapM (fun j => chainPrefixes lay tree leaf j 0 7 (seed j))) >>= fun ps =>
        k (vs.getD 7 0 :: ends ps)) =
      (xs.mapM (fun j => ClaudeWCT.WCT9.chainW lay tree leaf j 0 7 (seed j)) >>= fun ds => k (vs.getD 7 0 :: ds)) :=
      fun vs => ih (fun ds => k (vs.getD 7 0 :: ds))
    simp only [hh]
    exact chainPrefixes_bind_last lay tree leaf i 0 7 (seed i)
      (fun last => xs.mapM (fun j => ClaudeWCT.WCT9.chainW lay tree leaf j 0 7 (seed j)) >>= fun ds => k (last::ds))

theorem leafRows_forget {α : Type} (lay : Layer) (tree leaf : Nat) (seed : Nat → Digest)
    (xs : List Nat) (state : List Digest × List Digest) (k : List Digest → M α) :
    (xs.foldlM (fun st i => do
        let last ← ClaudeWCT.WCT9.chainW lay tree leaf i 0 7 (seed i)
        pure (st.1++[last],st.2++[seed i])) state >>= fun st => k st.1) =
      (xs.mapM (fun i => ClaudeWCT.WCT9.chainW lay tree leaf i 0 7 (seed i)) >>= fun ds => k (state.1++ds)) := by
  induction xs generalizing state with
  | nil => simp only [List.foldlM_nil,List.mapM_nil,pure_bind,List.append_nil]
  | cons i xs ih =>
    simp only [List.foldlM_cons,List.mapM_cons,bind_assoc,pure_bind]
    apply bind_congr
    intro v
    rw [ih]
    simp only [List.append_assoc,List.singleton_append]

theorem buildLeafPrefixes_forget {α : Type} (lay : Layer) (hlay : lay≠0)
    (tree leaf : Nat) (carry : List Digest) (k : Digest → List Digest → M α) :
    (buildLeafPrefixes lay tree leaf carry >>= fun r => k r.1.1 r.2) =
      (ClaudeWCT.WCT9.buildLeafPF lay tree leaf [] carry >>= fun r => k r.1.1 r.2) := by
  have hn : chainCount lay=43 := ClaudeWCT.W9.Machine.Sign.PackedLeaf.lower_n hlay
  have hm : ∀ i,maxDigit lay i=7 := by intro i; unfold maxDigit; rw [if_neg hlay]
  unfold buildLeafPrefixes ClaudeWCT.WCT9.buildLeafPF
  have hz : ∀ i v, ClaudeWCT.WCT9.chainW lay tree leaf i 0 0 v = pure v := fun _ _ => rfl
  simp only [bind_assoc,pure_bind,List.getD_nil,hz,Nat.sub_zero,hm]
  apply bind_congr
  intro cs
  rw [leafRows_forget (k := fun ds => ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ds >>= fun root => k root cs.2)]
  simp only [List.nil_append]
  -- The successful map has exactly one prefix list per chain.
  have hp : ∀ ps : List (List Digest), ps.length=43 →
      (List.range (chainCount lay)).map (fun i => (ps.getD i []).getD 7 0)=ends ps := by
    intro ps hps
    simpa only [hm] using prefixEnds_eq lay hlay ps hps
  -- Use the dependent-length fact in the map before forgetting its prefixes.
  have mapEq : ((List.range (chainCount lay)).mapM
      (fun i => chainPrefixes lay tree leaf i 0 7 (ClaudeWCT.WCT9.lowerFamilySeed cs.1 lay leaf i)) >>= fun ps =>
        (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ((List.range (chainCount lay)).map fun i => (ps.getD i []).getD 7 0) >>= fun root => k root cs.2)) =
      ((List.range (chainCount lay)).mapM
      (fun i => chainPrefixes lay tree leaf i 0 7 (ClaudeWCT.WCT9.lowerFamilySeed cs.1 lay leaf i)) >>= fun ps =>
        (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf (ends ps) >>= fun root => k root cs.2)) := by
    apply mapM_bind_len
    intro ps hps
    rw [hp ps (by simpa only [hn,List.length_range] using hps)]
  rw [mapEq]
  exact mapM_prefixEnds lay tree leaf (ClaudeWCT.WCT9.lowerFamilySeed cs.1 lay leaf) _
    (fun ds => ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ds >>= fun root => k root cs.2)

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n lower_e lower_sel)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem LeafInv.selected_iff {sk : BitVec 256} {s0 s t : MachineState} {A : LeafArgs}
    {j : Nat} {st : List Digest × List Digest} (hpre : LeafPreS sk s0 A)
    (hvi : A.valp+16*A.n≤0x20550 ∨ 0x20558≤A.valp)
    (hi : LeafInv s A j st t) (hs : HybOf s0 s t) :
    SharedPrefixes.selectionWord (t.getMem 0x20550) A.lay.val=t.getReg .x18 ↔ Selected A s0 := by
  have hindex : t.getMem 0x20550=s0.getMem 0x20550 := by
    have hd := hpre.hds
    have hc := chainCount_cases A.lay
    change t.getMem (BitVec.ofNat 64 0x20550)=s0.getMem (BitVec.ofNat 64 0x20550)
    rw [hi.frame.get (by decide) (by
      simp only [LeafW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT] at *
      split_ifs <;> omega),hs.base.get (by decide) (not_bscr (by decide))]
  rw [hindex,hi.regs.get (by decide),hs.regs,hpre.x18]
  rfl

theorem chain_cont_guarded {im : Image}
    (hsub : Sign.SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Sign.Seed.sub61)
    (hc : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (sk : BitVec 256) {s0 s : MachineState} {A : LeafArgs}
    (hpre : LeafPreS sk s0 A) (hlay : A.lay ≠ 0) (hso : A.so=false)
    (hv : A.valp+16*A.n ≤ 0x50000) (hd : A.digp+A.n ≤ 0x50000)
    (hvi : A.valp+16*A.n ≤ 0x20550 ∨ 0x20558 ≤ A.valp)
    {j : Nat} (hj : j<A.n) {st : List Digest × List Digest}
    (t : MachineState) (seed carry : Digest)
    (hp : t.pc=pcOf (1013+61)) (ht : LeafInv s A j st t) (hs : HybOf s0 s t)
    (h28 : t.getReg .x28=0) (hseed : DigAt t SEEDS seed) (hcarry : DigAt t (SEEDS+16) carry) :
    TBSim im sk t 679 (chainPrefixes A.lay A.tree A.leaf j 0 7 seed)
      (fun vs w => vs.length=8 ∧ w.pc=pcOf (1013+41) ∧
        ∃ base values, HybOf s0 base w ∧
          LeafInv base A (j+1) (st.1++[vs.getD 7 0],values) w ∧
          DigAt w (SEEDS+16) carry ∧
          Frame t w (fun X => Sign.Seed.ChainWS (A.valp+16*j) X ∨
            (Selected A s0 ∧ SharedPrefixes.buffer A.lay.val j 0≤X ∧ X<SharedPrefixes.buffer A.lay.val j 7+16) ∨
            (slot A.lay j≤X ∧ X<slot A.lay j+16)) ∧
          (SharedPrefixes.selectionWord (t.getMem 0x20550) A.lay.val=t.getReg .x18 →
            ∀ k, k≤7 → DigAt w (SharedPrefixes.buffer A.lay.val j k) (vs.getD k 0)) ∧
          (j % 2 = 0 → Sign.Seed.Z32 w)) := by
  by_cases hsel : Selected A s0
  · exact (chain_cont hsub hcopy hc hpref sk hpre hlay hso hv hd hvi hj t seed carry hp ht hs h28 hseed hcarry).mono
      (Nat.le_refl _) (fun vs w hw => by
        obtain ⟨hl,hpc,b,v,hb,hi,hc,hf,hp,hz⟩ := hw
        refine ⟨hl,hpc,b,v,hb,hi,hc,hf.mono ?_,hp,hz⟩
        intro X hX h
        rcases h with h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hsel,h⟩)
        · exact Or.inr (Or.inr h))
  · have hmiss : SharedPrefixes.selectionWord (t.getMem 0x20550) A.lay.val≠t.getReg .x18 :=
      fun h => hsel ((LeafInv.selected_iff hpre hvi ht hs).mp h)
    exact (chain_cont_unselected hsub hcopy hc hpref sk hpre hlay hso hv hd hvi hj t seed carry hp ht hs h28 hseed hcarry hmiss).mono
      (Nat.le_refl _) (fun vs w hw => by
        obtain ⟨hl,hpc,b,v,hb,hi,hc,hf,hz⟩ := hw
        refine ⟨hl,hpc,b,v,hb,hi,hc,hf.mono ?_,?_,hz⟩
        · intro X hX h
          rcases h with h|h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · intro h; exact (hmiss h).elim)

/-- All lower-leaf scratch is below the retained-prefix buffers. Only the
selected leaf may write the buffer block belonging to its own layer. -/
def Writes (A : LeafArgs) (s0 : MachineState) (X : Nat) : Prop :=
  X<0x66000 ∨ (Selected A s0 ∧ 0x6e000+8192*A.lay.val≤X ∧ X<0x6e000+8192*(A.lay.val+1))

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
