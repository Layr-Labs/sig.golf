import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.PackedHelper
import SigGolfCandidate.T3M.Sign.SeedLeafPhases
import SigGolfCandidate.T3M.Sign.PackedLowTree

namespace ClaudeWCT.W9.Machine.Sign.PackedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN LEAFPK LOUT LeafArgs LeafW leafRegs LeafInv ChainPre ChainW
  chainRegs chainProg n4 selectorExtra rungK rungC leafBlocks slot slot_ge slot_lt LeafW_of_c48 LeafW_of_chainW
  LeafW_of_slot chainCount_cases)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit privatePair header privateInput)
set_option maxRecDepth 10000
def KP (A : LeafArgs) (j : Nat) : Nat :=
  (if (j + A.leaf) % 2 = 1 then 7 else 25) + 16 + (rungK A.lay * A.e j + 10) + (4 + (11 + (if j = 0 then 0 else 1)))
def CP (A : LeafArgs) (j : Nat) : Nat :=
  (if (j + A.leaf) % 2 = 1 then 7 else 35) + 16 + (rungC A.lay * A.e j + 10) + (4 + (11 + (if j = 0 then 0 else 1)))
def NP (A : LeafArgs) (j : Nat) : Nat := (if (j + A.leaf) % 2 = 1 then 0 else 1) + A.e j
theorem LeafInv.of_step {sk : BitVec 256} {s0 t u : MachineState} {A : LeafArgs} {j : Nat} {st : List Digest × List Digest}
    (ht : LeafInv s0 A j st t) (hr : RegsExcept t u [.x6, .x7, .x10, .x11, .x12, .x28, .x30])
    (hf : Frame t u (fun X => X = PRIV + 24 ∨ X = PRIV + 16 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)))
    (hpre : LeafPreS sk s0 A) (hj : j ≤ A.n) : LeafInv s0 A j st u := by
  have hvs := hpre.hvs
  have hv := hpre.hv
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  refine ⟨by rw [hr.get (by simp)]; exact ht.x19, by rw [hr.get (by simp)]; exact ht.x23,
    by rw [hr.get (by simp)]; exact ht.x3, (ht.regs.trans hr).mono (by decide),
    (ht.frame.trans hf).mono (fun X _ h => ?_), ?_, ?_, ht.elen, ht.vlen, fun hso c hc => ?_, ?_⟩
  · rcases h with h | h | h | h
    · exact h
    · unfold LeafW; right; left; exact h
    · unfold LeafW; left; exact h
    · unfold LeafW; right; right; left; exact h
  · rw [hf.get (by decide) (by simp only [PRIV, SEEDS]; omega)]; exact ht.lh16
  · rw [hf.get (by decide) (by simp only [PRIV, SEEDS]; omega)]; exact ht.lh24
  · have h1 := slot_ge c; have h2 := slot_lt (show c < A.n by omega)
    exact (ht.ends hso c hc).frame hf (by omega) (by omega) (by omega)
  · exact ht.vals.frame hf (by rw [ht.vlen]; omega) (fun X h1 h2 => by rw [ht.vlen] at h2; omega)
theorem packedSecret_odd {q : Nat} (hq : q % 2 = 1) (pq : Nat → SigGolfCandidate.T3.M (Digest × Digest)) (carry : Digest) :
    WCT9.packedSecret pq q carry = pure (carry, carry) := by
  unfold WCT9.packedSecret; rw [if_neg (by omega)]
theorem packedSecret_even {q : Nat} (hq : q % 2 = 0) (pq : Nat → SigGolfCandidate.T3.M (Digest × Digest)) (carry : Digest) :
    WCT9.packedSecret pq q carry = (pq (q / 2) >>= fun seeds => pure (seeds.1, seeds.2)) := by
  unfold WCT9.packedSecret; rw [if_pos hq]
theorem lower_n {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem lower_height {lay : Layer} (h : lay ≠ 0) : 2 ^ SigGolfCandidate.T3.height lay ≤ 128 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide
theorem lower_sel {lay : Layer} (h : lay ≠ 0) (j : Nat) : selectorExtra lay j = 0 := by
  unfold selectorExtra; rw [if_neg h]
section lower
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre
theorem chainP_tsim (hlay : A.lay ≠ 0) (hso : A.so = false) {j : Nat} (hj : j < A.n)
    {st : List Digest × List Digest} {carry : Digest} {t : MachineState} (ht : LeafInv s0 A j st t)
    (hpc : t.pc = pcOf (1013 + 41)) (hcar : (j + A.leaf) % 2 = 1 → DigAt t (SEEDS + 16) carry) :
    TSim Sign.image sk t (KP A j) (CP A j) (NP A j) (NP A j)
      (WCT9.packedSecret (WCT9.lowerSeedPair A.lay A.tree) (WCT9.lowerOrdinal A.lay A.leaf j) carry >>= fun sc =>
        (fun r : Digest × Digest => (st.1 ++ [r.2], st.2 ++ [r.1], sc.2)) <$> chainProg A j sc.1)
      (fun st' u => u.pc = pcOf (1013 + 41) ∧ LeafInv s0 A (j + 1) (st'.1, st'.2.1) u ∧
        DigAt u (SEEDS + 16) st'.2.2) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 43 := lower_n hlay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLO : LOUT = 132032 := rfl
  have hvs := hpre.hvs
  have hv := hpre.hv
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hlh := hpre.hleafHeight
  have h2h := lower_height hlay
  have hleaf : A.leaf < 2 ^ 7 := by omega
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have cont : ∀ (u : MachineState) (half : Nat) (seed carry' : Digest), half < 2 → u.pc = pcOf (1013 + 61) →
      LeafInv s0 A j st u → u.getReg .x28 = BitVec.ofNat 64 half → DigAt u (SEEDS + 16 * half) seed →
      DigAt u (SEEDS + 16) carry' →
      TSim Sign.image sk u (16 + (rungK A.lay * A.e j + 10) + (4 + (11 + (if j = 0 then 0 else 1))))
        (16 + (rungC A.lay * A.e j + 10) + (4 + (11 + (if j = 0 then 0 else 1)))) (A.e j) (A.e j)
        ((fun r : Digest × Digest => (st.1 ++ [r.2], st.2 ++ [r.1], carry')) <$> chainProg A j seed)
        (fun st' u => u.pc = pcOf (1013 + 41) ∧ LeafInv s0 A (j + 1) (st'.1, st'.2.1) u ∧
          DigAt u (SEEDS + 16) st'.2.2) := by
    intro u half seed carry' hh upc hu h28 hseed hc'
    obtain ⟨u0, st0, u0pc, hcp, hcs, u0r, u0f⟩ := Sign.Seed.leaf_prechainFrom61S hsub sk hpre hj hu upc seed half hh
      h28 (Sign.SeedIndependent.codeAt_sub_61 hsub) hseed
    rw [lower_sel hlay, hso] at st0
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at st0
    have hch := Sign.Seed.chainRun_tsim hsub sk hcp u0pc seed hcs
    rw [map_eq_bind_pure_comp]
    refine (TSim.steps st0 (TSim.bind (k₂ := 4 + (11 + (if j = 0 then 0 else 1)))
      (c₂ := 4 + (11 + (if j = 0 then 0 else 1))) (n₂ := 0) (b₂ := 0) hch (fun r w hw => ?_))).of_eq
      (by unfold chainProg; rfl) (by split_ifs <;> omega) (by split_ifs <;> omega) (by simp) (by simp)
    obtain ⟨wpc, hwv, hwl, hwr, hwf⟩ := hw
    obtain ⟨x, stx, xpc, hx, hfx⟩ := Sign.Seed.leaf_postchainS hsub sk hpre hj hu wpc (u0r.trans hwr)
      (u0f.trans hwf) r.1 r.2 hwv hwl
    rw [hso] at stx hx
    simp only [Bool.false_eq_true, if_false] at stx hx
    refine TSim.pure_steps stx ⟨xpc, hx, ?_⟩
    have hsj := slot_ge j
    have hsj' := slot_lt hj
    have hvj : A.valp + 16 * j + 16 ≤ A.valp + 16 * A.n := by omega
    refine ((hc'.frame u0f (by omega) (by omega) (by omega)).frame hwf (by omega) ?_ ?_).frame hfx (by omega)
      (by omega) (by omega)
    · unfold ChainW; omega
    · unfold ChainW; omega
  have hq : WCT9.lowerOrdinal A.lay A.leaf j = 43 * A.leaf + j := by
    unfold WCT9.lowerOrdinal; rw [lower_n hlay]
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.Seed.sub41_spec hsub t hpc j A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := hook_spec t1 (by rw [t1pc])
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have r8 : t2.getReg .x8 = BitVec.ofNat 64 A.lay.val := by
    rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x8]
  have r9 : t2.getReg .x9 = BitVec.ofNat 64 A.tree := by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x9]
  have r18 : t2.getReg .x18 = BitVec.ofNat 64 A.leaf := by
    rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x18]
  have r19 : t2.getReg .x19 = BitVec.ofNat 64 j := by rw [e12.get (by simp)]; exact ht.x19
  have hlay0 : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  rw [hq]
  by_cases hpar : (j + A.leaf) % 2 = 1
  ·
    rw [packedSecret_odd (by omega), pure_bind]
    obtain ⟨t3, st3, t3pc, t3x28, t3r, t3f⟩ := odd_spec t2 t2pc hlay0 hlay' r8 r18 r19 (by omega) (by omega) hpar
    have hu : LeafInv s0 A j st t3 := LeafInv.of_step ht ((e12.trans t3r).mono (by decide))
      ((f12.trans t3f).mono (fun X _ h => by simp at h)) hpre (by omega)
    have hc3 : DigAt t3 (SEEDS + 16) carry := (hcar hpar).frame (f12.trans t3f) (by omega) (by simp) (by simp)
    refine (TSim.steps (st1.trans (st2.trans st3)) (cont t3 1 carry carry (by norm_num) (by rw [t3pc])
      hu t3x28 (by simpa using hc3) hc3)).of_eq rfl ?_ ?_ ?_ ?_
    all_goals ((try simp only [KP, CP, NP, hpar, if_true]) <;> (try split_ifs) <;> omega)
  ·
    rw [packedSecret_even (by omega), bind_assoc]
    simp only [pure_bind]
    obtain ⟨t3, st3, e3, t3pc, x10, x11, x12, m16, m24, t3r, t3f⟩ := even_spec t2 t2pc hlay0 hlay' hpre.htree
      hleaf (by omega) r8 r9 r18 r19 (by omega)
    have f13 : Frame t t3 (fun X => X = PRIV + 24 ∨ X = PRIV + 16) :=
      (f12.trans t3f).mono (fun X _ h => by rcases h with h | h; exact h.elim; exact h)
    have r13 : RegsExcept t t3 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (e12.trans t3r).mono (by simp)
    have hLP : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
        X = PRIV + 56) → ¬ LeafW A X := by
      intro X hX hw
      have := hpre.hds; have := hpre.hdv
      unfold LeafW at hw
      omega
    have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
        X = PRIV + 56) → t3.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
      (f13.get (by omega) (by omega)).trans (ht.frame.get (by omega) (hLP X hX))
    have hqin : hashInput t3 = toQ (privateInput sk (.inl (header 0 A.lay.val A.tree ((43 * A.leaf + j) / 2) 0))) := by
      refine hashInput_toQ t3 _ 0 PRIV (privateInput_tweak_length _ _) x10 (by decide) (by decide) x11
        (by decide) ?_
      rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
        fr (PRIV + 8) (by simp), m16, m24, fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
        fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hpre.p0, hpre.p8, hpre.p32, hpre.p40,
        hpre.p48, hpre.p56]
      rfl
    have hva : hashArgumentsValid t3 = true :=
      hashArgs_const t3 PRIV 64 SEEDS x10 x11 x12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [leafRegs]), hpre.x5]
    unfold WCT9.lowerSeedPair
    refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.privatePair_bind
      (k := 2 + (16 + (rungK A.lay * A.e j + 10) + (4 + (11 + (if j = 0 then 0 else 1)))))
      (c := 2 + (16 + (rungC A.lay * A.e j + 10) + (4 + (11 + (if j = 0 then 0 else 1)))))
      (n := A.e j) (b := A.e j) e3 h5 hva hqin (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
    rotate_left
    · (try simp only [KP, hpar, if_false]) <;> (try split_ifs) <;> omega
    · (try simp only [CP, hpar, if_false]) <;> (try split_ifs) <;> omega
    · (try simp only [NP, hpar, if_false]) <;> (try split_ifs) <;> omega
    · (try simp only [NP, hpar, if_false]) <;> (try split_ifs) <;> omega
    have hwf := Frame.writeHash t3 a SEEDS x12 (by decide)
    obtain ⟨t4, st4, t4pc, t4x28, t4r, t4f⟩ := tail_spec (writeHash t3 a) (by rw [pc_writeHash, t3pc, pcOf_add4])
    have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
    have hu : LeafInv s0 A j st t4 := LeafInv.of_step ht (((r13.trans hw0).trans t4r).mono (by decide))
      (((f13.trans hwf).trans t4f).mono (fun X _ h => by
        rcases h with (h | h) | h
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact h.elim)) hpre (by omega)
    have hlo : DigAt t4 SEEDS (a.extractLsb' 0 128) :=
      (DigAt.writeHash_lo t3 a SEEDS x12 (by decide)).frame t4f (by decide) (by simp) (by simp)
    have hhi : DigAt t4 (SEEDS + 16) (a.extractLsb' 128 128) :=
      (DigAt.writeHash_hi t3 a SEEDS x12 (by decide)).frame t4f (by decide) (by simp) (by simp)
    exact TSim.steps st4 (cont t4 0 _ _ (by norm_num) (by rw [t4pc]) hu t4x28 (by simpa using hlo) hhi)
theorem buildLeafP_tsim (hlay : A.lay ≠ 0) (hso : A.so = false) (hpc : s0.pc = pcOf (1013 + 27))
    (carry : Digest) (hcar : A.leaf % 2 = 1 → DigAt s0 (SEEDS + 16) carry) :
    TSim Sign.image sk s0 (14 + (sumTo (KP A) A.n + 19)) (14 + (sumTo (CP A) A.n + (18 + 8 * leafBlocks A.lay)))
      (sumTo (NP A) A.n + 1) (sumTo (NP A) A.n + leafBlocks A.lay)
      (WCT9.buildLeafP A.lay A.tree A.leaf A.digits carry)
      (fun r t => t.pc = pcOf A.ret ∧ DigAt t A.dest r.1.1 ∧ DigsAt t A.valp r.1.2 ∧ r.1.2.length = A.n ∧
        DigAt t (SEEDS + 16) r.2 ∧ RegsExcept s0 t leafRegs ∧ Frame s0 t (LeafW A)) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 43 := lower_n hlay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLO : LOUT = 132032 := rfl
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  obtain ⟨t1, st1, t1pc, t1x3, t1x19, t1c24, t1l24, t1l16, t1r, t1f⟩ :=
    Sign.Seed.sub27_spec hsub s0 hpc A.lay.val A.tree A.leaf hlay' hpre.htree hpre.hleaf hpre.x8 hpre.x9 hpre.x18
  have h0 : LeafInv s0 A 0 ([], []) t1 := by
    refine ⟨t1x19, ?_, by rw [t1x3, hpre.x1], t1r.mono (by decide), t1f.mono (fun X _ h => ?_), ?_,
      t1l24, by simp, rfl, fun _ c hc => absurd hc (by omega), DigsAt.nil _ _⟩
    · rw [t1r.get (by simp), hpre.x23]; simp
    · unfold LeafW; omega
    · rw [t1l16]
  have hc1 : A.leaf % 2 = 1 → DigAt t1 (SEEDS + 16) carry := fun h =>
    (hcar h).frame t1f (by omega) (by omega) (by omega)
  unfold WCT9.buildLeafP
  refine (TSim.steps st1 (TSim.bind (k₂ := 19) (c₂ := 18 + 8 * leafBlocks A.lay) (n₂ := 1)
    (b₂ := leafBlocks A.lay) (TSim.foldlM_range A.n _ ([], [], carry)
    (fun j st t => t.pc = pcOf (1013 + 41) ∧ LeafInv s0 A j (st.1, st.2.1) t ∧
      ((0 < j ∨ A.leaf % 2 = 1) → DigAt t (SEEDS + 16) st.2.2))
    (KP A) (CP A) (NP A) (NP A) (fun j hj st t ht => ?_) ⟨t1pc, h0, fun h => hc1 (by omega)⟩)
    (fun st t ht => ?_))).of_eq rfl rfl rfl rfl rfl
  · obtain ⟨tpc, hinv, hcr⟩ := ht
    refine ((chainP_tsim sk hpre hlay hso hj hinv tpc (fun hp => hcr (by omega))).mono
      (fun st' u hu => ⟨hu.1, hu.2.1, fun _ => hu.2.2⟩)).of_eq ?_ rfl rfl rfl rfl
    refine bind_congr fun sc => ?_
    obtain ⟨seed, carry'⟩ := sc
    simp only [chainProg, LeafArgs.e, LeafArgs.d, hso, Bool.false_eq_true, if_false, map_bind, map_pure]
  · obtain ⟨tpc, hinv, hcr⟩ := ht
    have hex := Sign.Seed.leaf_exitS hsub sk hpre hinv tpc
    simp only [hso, Bool.false_eq_true, if_false] at hex
    refine (TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (f := fun r => pure ((r.1, r.2), st.2.2)) hex
      (fun r u hu => TSim.pure ?_)).of_eq ?_ rfl rfl rfl rfl
    · obtain ⟨upc, udest, uvals, ulen, -, uregs, uframe, utf⟩ := hu
      refine ⟨upc, udest trivial, uvals, ulen, ?_, uregs, uframe⟩
      have hds := hpre.hds
      exact (hcr (Or.inl (by omega))).frame utf (by omega) (by omega) (by omega)
    · simp only [bind_assoc, pure_bind]
end lower
def cpG (p r j : Nat) : Nat :=
  (if (j + p) % 2 = 1 then 7 else 35) + 16 + (r * 7 + 10) + (4 + (11 + (if j = 0 then 0 else 1)))
theorem cpG_sums : sumTo (cpG 0 45) 43 = 16267 ∧ sumTo (cpG 1 45) 43 = 16239 ∧ sumTo (cpG 0 46) 43 = 16568 ∧
    sumTo (cpG 1 46) 43 = 16540 := by decide
theorem lower_e {A : LeafArgs} (hlay : A.lay ≠ 0) (hso : A.so = false) (j : Nat) : A.e j = 7 := by
  unfold LeafArgs.e; rw [hso]; simp only [Bool.false_eq_true, if_false]; unfold maxDigit; rw [if_neg hlay]
theorem lower_rungC {lay : Layer} (h : lay ≠ 0) : rungC lay = if lay = 1 then 45 else 46 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide
theorem lower_blocks {lay : Layer} (h : lay ≠ 0) : leafBlocks lay = 11 := by
  unfold leafBlocks; rw [lower_n h]
theorem leaf_cycles {A : LeafArgs} (hlay : A.lay ≠ 0) (hso : A.so = false) :
    14 + (sumTo (CP A) A.n + (18 + 8 * leafBlocks A.lay)) ≤ (if A.lay = 1 then 16387 else 16688) := by
  have hn : A.n = 43 := lower_n hlay
  have hc : sumTo (CP A) A.n = sumTo (cpG (A.leaf % 2) (rungC A.lay)) 43 := by
    rw [hn]
    refine sumTo_congr _ _ 43 (fun j _ => ?_)
    unfold CP cpG
    rw [lower_e hlay hso j, show (j + A.leaf) % 2 = (j + A.leaf % 2) % 2 by omega]
  rw [hc, lower_blocks hlay, lower_rungC hlay]
  obtain ⟨h1, h2, h3, h4⟩ := cpG_sums
  rcases Nat.mod_two_eq_zero_or_one A.leaf with hp | hp <;> rw [hp] <;> split_ifs <;> omega
theorem leaf_steps_le (A : LeafArgs) :
    14 + (sumTo (KP A) A.n + 19) ≤ 14 + (sumTo (CP A) A.n + (18 + 8 * leafBlocks A.lay)) := by
  have : sumTo (KP A) A.n ≤ sumTo (CP A) A.n := by
    refine SigGolfCandidate.T3M.Sign.Packed.sumTo_le_sumTo _ _ A.n (fun j _ => ?_)
    unfold KP CP
    have h1 : rungK A.lay ≤ rungC A.lay := by unfold rungK rungC; omega
    have := Nat.mul_le_mul_right (A.e j) h1
    split_ifs <;> omega
  have : 1 ≤ leafBlocks A.lay := by unfold leafBlocks; omega
  omega
def PackedLeafSpecV : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState) (carry : Digest),
    A.lay ≠ 0 → A.so = false → LeafPreS sk s A → s.pc = pcOf (1013 + 27) →
    (A.leaf % 2 = 1 → DigAt s (SEEDS + 16) carry) →
    TBSim Sign.image sk s (if A.lay = 1 then 16387 else 16688)
      (WCT9.buildLeafP A.lay A.tree A.leaf A.digits carry)
      (fun r t => t.pc = pcOf A.ret ∧
        (A.so = false → DigAt t A.dest r.1.1) ∧ DigsAt t A.valp r.1.2 ∧
        r.1.2.length = A.n ∧ DigAt t (SEEDS + 16) r.2 ∧
        RegsExcept s t leafRegs ∧ Frame s t (LeafW A))
theorem packedLeafSpecV : PackedLeafSpecV := by
  intro sk A s carry hlay hso hpre hpc hcar
  refine ((buildLeafP_tsim sk hpre hlay hso hpc carry hcar).toTBSim (leaf_steps_le A)).mono (leaf_cycles hlay hso)
    (fun r t ht => ⟨ht.1, fun _ => ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2⟩)
end ClaudeWCT.W9.Machine.Sign.PackedLeaf
