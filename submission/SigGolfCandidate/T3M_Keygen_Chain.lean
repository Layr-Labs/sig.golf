import SigGolfCandidate.T3M_Keygen_PackedInput
import SigGolfCandidate.T3M_Keygen_KPair

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 maxDigit topChain topIsG
  topChainHigh topChainInput)
open SphincsSecurity (bytesLE bytesLE_length)
macro "sc_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK] at *); omega))
theorem sub0_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_0 h) s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]
theorem sub1_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1)) (m cap : Nat) (hm : m < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h17 : s.getReg .x17 = BitVec.ofNat 64 cap) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = cap then pcOf (b + 2) else pcOf (b + 8)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_1 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_1 h) s hpc (by simp [st_1, blk117_1.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_1, rebase, blk117_1.res, E.eval, CmpOp.eval, h20, h17]
    by_cases hmc : m = cap
    · subst hmc; simp
    · rw [if_neg hmc]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 cap := fun he => hmc ((ofNat_inj hm hcap).mp he)
      simp [this]
  · intro r hr; cases r <;> simp_all [st_1, blk117_1.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_1, blk117_1.res, rv_simp]
theorem sub2_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 2)) (valp : Nat) (h23 : s.getReg .x23 = BitVec.ofNat 64 valp)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 8) ∧
      t.getMem (BitVec.ofNat 64 valp) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (valp + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = valp ∨ A = valp + 8) := by
  have hrun := run_2 h.2.1
  have hobl : Oblig.all s st_2.obl := by
    simp only [st_2, blk117_2.res]
    t3n [h23]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_2 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_2, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_2, blk117_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub8_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (b + 26) else pcOf (b + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_8 h) s hpc (by simp [st_8, blk117_8.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_8, rebase, blk117_8.res, E.eval, CmpOp.eval, h20, h21]
    by_cases hme : m = e
    · subst hme; simp
    · rw [if_neg hme]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 e := fun he' => hme ((ofNat_inj hm he).mp he')
      simp [this]
  · intro r hr; cases r <;> simp_all [st_8, blk117_8.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_8, blk117_8.res, rv_simp]
abbrev sub9_spec {image : Image} {b : Nat} := @shared_header_source image b
theorem sub24_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 24)) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_24 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_24 h) s hpc (by simp [st_24, blk117_24.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_24, Result.toState_pc, E.eval]
  · t3n [st_24, blk117_24.res, h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_24, blk117_24.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_24, blk117_24.res, rv_simp]
theorem sub26_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_26 h) s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]
theorem fetch_sub23 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 23)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_23 h).fetch s hpc).trans rfl
theorem chainInput_length (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, zero16]
theorem wordsOf_chainInput (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (chainInput lay tree leaf i step v) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] :=
  Packed.wordsOf_chainInput lay tree leaf i step v
theorem toQ_chainInput_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length]), blocks_toQ ⟨by rw [chainInput_length]; omega,
    by rw [chainInput_length]⟩, chainInput_length]
/-- Witness stack: the keygen chain routine runs top chains only (`lay = 0`, tree 0, `e = maxDigit 0 i`); the pad
words `CHAIN+32/40` are no longer assumed zero (the F path clears them, a G step overwrites them). -/
structure ChainPre (s : MachineState) (lay : Layer) (tree leaf i cap e valp ret : Nat) : Prop where
  x5 : s.getReg .x5 = 0
  x1 : s.getReg .x1 = pcOf ret
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 cap
  x19 : s.getReg .x19 = BitVec.ofNat 64 i
  x21 : s.getReg .x21 = BitVec.ofNat 64 e
  x23 : s.getReg .x23 = BitVec.ofNat 64 valp
  htree : tree < 2 ^ 32
  hi : i < 51
  hroute : tree * 2 ^ T3.height lay + leaf < 2 ^ 31
  hleaf : leaf < 2 ^ T3.height lay
  hcap : cap ≤ e
  he : e = maxDigit 0 i
  hv8 : valp % 8 = 0
  hv : valp + 16 ≤ 2 ^ 24
  hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 112 ≤ valp
  l0 : lay = 0
  t0 : tree = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x29, .x30]
/-- Witness stack: the chain scratch is `CHAIN+16/24` (header) and `CHAIN+32 .. CHAIN+112` (G input / F pads). -/
def ChainW (valp A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨
    (CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∨ (valp ≤ A ∧ A < valp + 16)
structure ChainHead (b : Nat) (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (b + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 m
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (ChainW valp)
  val : DigAt t (CHAIN + 48) v
/-- C4 (b3cc11b's `TSim.projHash_bind`, kept local to the keygen): a projected hash (`projHash high`) followed by `f`;
the continuation sees the chosen half. -/
theorem tsim_projHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState} {input : List UInt8}
    {high : Bool} {k c n b : Nat} {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TSim image sk (writeHash s a) k c n b (f (T3.projHalf high a)) Q) :
    TSim image sk s (1 + k) (8 * (toQ (pad64 input)).blocks + c) (1 + n) ((toQ (pad64 input)).blocks + b)
      (T3.projHash high input >>= f) Q := by
  have e : T3.projHash high input >>= f = T3.publicHash input >>= fun a => f (T3.projHalf high a) := by
    unfold T3.projHash; rw [bind_assoc]; simp only [pure_bind]
  rw [e]
  exact TSim.publicHash_bind hf ht0 hv hq h
theorem ksumTo_split (F : Nat → Nat) (a : Nat) : ∀ n, sumTo F (a + 1 + n) = sumTo F a + F a + sumTo (fun j => F (a + 1 + j)) n
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [show a + 1 + (n + 1) = (a + 1 + n) + 1 by omega, sumTo, ksumTo_split F a n, sumTo]; omega
/-- Witness stack: steps of one keygen chain rung (loop head 118 back to 118): `sub1; sub8`, the header (25) and the
step block (`3 + kgX`). -/
def kRungK (i m : Nat) : Nat := 30 + kgX i m
def kRungC (i m : Nat) : Nat := 37 + kgX i m
/-- Steps of one keygen chain run of `e` hashes (entry 1, per step `kRungK`, exit and value copy 9). -/
def kChainK (i e : Nat) : Nat := sumTo (fun m => kRungK i m) e + 10
def kChainCy (i e : Nat) : Nat := sumTo (fun m => kRungC i m) e + 10
section loop
variable {image : Image} {b : Nat} (hsub : SubAt image b) (sk : BitVec 256) {s0 : MachineState}
  {lay : Layer} {tree leaf i cap e valp ret : Nat} (hpre : ChainPre s0 lay tree leaf i cap e valp ret)
include hsub hpre
omit hpre in
theorem chain_entry (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    ∃ t, Steps image s0 1 1 t ∧ ChainHead b s0 valp 0 seed t := by
  obtain ⟨t, st, tpc, t20, tr, tf⟩ := sub0_spec hsub s0 (by simpa using hpc)
  exact ⟨t, st, ⟨tpc, t20, tr.mono (by simp [chainRegs]), tf.mono (fun _ _ h => h.elim),
    hseed.frame tf (by decide) (by simp) (by simp)⟩⟩
/-- Witness stack: the header from `b + 9` and the step block (`kpair_rung`), from a state `t2` that agrees with the
chain head `t` outside the header words and `valp`. -/
theorem kchain_rung {m : Nat} (hm : m < e) {v : Digest} {t t2 : MachineState}
    (ht : ChainHead b s0 valp m v t) (ht2 : t2.pc = pcOf (b + 9))
    (hr2 : RegsExcept t t2 [.x6, .x7, .x29]) (hf2 : Frame t t2 (fun A => valp ≤ A ∧ A < valp + 16)) :
    TSim image sk t2 (25 + (3 + kgX i m)) (25 + (10 + kgX i m)) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧
        Frame t2 u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112))) := by
  have he := hpre.he
  have hi := hpre.hi
  have hvc := hpre.hvc
  have hl0 := hpre.l0
  have ht0 := hpre.t0
  subst hl0 ht0
  obtain ⟨rfl, rfl⟩ := hsub.2.2.2.2
  have g : ∀ r, r ∉ chainRegs → r ∉ [.x6, .x7, .x29] → t2.getReg r = s0.getReg r := fun r hr hr' =>
    (hr2.get hr').trans (ht.regs.get hr)
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  obtain ⟨t3, st3, t3pc, t3x28, t3w, t3w24, t3r, t3f⟩ :=
    sub9_spec hsub t2 ht2 0 0 leaf i m hpre.hroute hpre.hleaf (by omega) (by omega)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x8)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x9)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x18)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x19)
    (by rw [hr2.get (by simp)]; exact ht.x20)
  have g3 : ∀ r, r ∉ chainRegs → t3.getReg r = s0.getReg r := fun r hr =>
    (t3r.get (fun h => hr (by simp [chainRegs] at h ⊢; rcases h with h | h | h | h <;> simp [h]))).trans
      (g r hr (fun h => hr (by simp [chainRegs] at h ⊢; rcases h with h | h | h <;> simp [h])))
  have f03 : Frame s0 t3 (fun A => ChainW valp A) := ((ht.frame.trans hf2).trans t3f).mono (fun A _ h => by
    unfold ChainW at *; rcases h with (h | h) | h
    · exact h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h)
  have hv3 : DigAt t3 (CHAIN + 48) v := (ht.val.frame hf2 (by decide) (by omega) (by omega)).frame t3f
    (by decide) (by simp) (by simp)
  have run := kpair_rung sk t3 (by rw [t3pc]) leaf i m v hi (by omega) (by omega)
    ((g3 _ (by simp [chainRegs])).trans hpre.x5)
    ((g3 _ (by simp [chainRegs])).trans hpre.x8)
    ((g3 _ (by simp [chainRegs])).trans hpre.x19)
    (by rw [t3r.get (by simp), hr2.get (by simp)]; exact ht.x20)
    ((g3 _ (by simp [chainRegs])).trans (hpre.x21.trans (by rw [hpre.he])))
    t3x28
    (by rw [f03.get (by decide) (by unfold ChainW; simp only [CHAIN] at *; omega)]; exact hpre.z0)
    (by rw [f03.get (by decide) (by unfold ChainW; simp only [CHAIN] at *; omega)]; exact hpre.z8)
    t3w t3w24 hv3
  refine (TSim.steps st3 run).mono ?_
  intro v' u hu
  refine ⟨⟨hu.1, hu.2.1, ?_, ?_, hu.2.2.1⟩, ?_⟩
  · exact (((ht.regs.trans hr2).trans t3r).trans hu.2.2.2.1).mono (by simp [chainRegs])
  · exact (f03.trans hu.2.2.2.2).mono (fun A _ h => by
      unfold ChainW at *; rcases h with h | h
      · exact h
      · exact Or.inr (Or.inl h))
  · exact (t3f.trans hu.2.2.2.2).mono (fun A _ h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h)
theorem chain_step {m : Nat} (hm : m < e) (hmc : m ≠ cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (kRungK i m) (kRungC i m) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧
        Frame t u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112))) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_neg hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc m e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20) (by rw [t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t2pc
  have run := kchain_rung hsub sk hpre hm ht t2pc ((t1r.trans t2r).mono (by simp))
    ((t1f.trans t2f).mono (fun A _ h => by simp_all))
  refine ((TSim.steps (st1.trans st2) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold kRungK; omega
  · unfold kRungC; omega
  · intro v' u hu
    exact ⟨hu.1, ((t1f.trans t2f).trans hu.2).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)⟩
theorem chain_step_cap {m : Nat} (hm : m < e) (hmc : m = cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (kRungK i m + 6) (kRungC i m + 6) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧ DigAt u valp v ∧ Frame t u (ChainW valp)) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hvc := hpre.hvc
  have hvb := hpre.hv
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 valp := by rw [g _ (by simp [chainRegs]), hpre.x23]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_pos hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp)]; exact h23) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc m e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t3pc
  have f13 : Frame t t3 (fun A => valp ≤ A ∧ A < valp + 16) :=
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by
      rcases h with (h | h | h) | h <;> first | exact h.elim | omega)
  have run := kchain_rung hsub sk hpre hm ht t3pc (((t1r.trans t2r).trans t3r).mono (by simp)) f13
  have hvv3 : DigAt t3 valp v := hvv.frame t3f (by omega) (by simp) (by simp)
  refine ((TSim.steps (st1.trans (st2.trans st3)) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold kRungK; omega
  · unfold kRungC; omega
  · intro v' u hu
    refine ⟨hu.1, hvv3.frame hu.2 (by omega) (by simp only [CHAIN] at *; omega)
      (by simp only [CHAIN] at *; omega), ?_⟩
    exact (f13.trans hu.2).mono (fun A _ h => by
      unfold ChainW; rcases h with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
theorem chain_exit {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e ≠ cap) :
    ∃ u, Steps image t 3 3 u ∧ u.pc = pcOf ret ∧ RegsExcept t u [] ∧ Frame t u (fun _ => False) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_neg hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc e e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20)
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t2pc
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub26_spec hsub t2 t2pc ret
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  exact ⟨t3, st1.trans (st2.trans st3), t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by simp_all)⟩
theorem chain_exit_cap {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e = cap) :
    ∃ u, Steps image t 9 9 u ∧ u.pc = pcOf ret ∧ DigAt u valp v ∧ RegsExcept t u [.x6, .x7, .x29] ∧
      Frame t u (fun A => valp ≤ A ∧ A < valp + 16) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_pos hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x23]) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc e e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t3pc
  obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := sub26_spec hsub t3 t3pc ret
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  refine ⟨t4, st1.trans (st2.trans (st3.trans st4)), t4pc, ?_, (((t1r.trans t2r).trans t3r).trans t4r).mono
    (by simp), (((t1f.trans t2f).trans t3f).trans t4f).mono (fun A _ h => by
      rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | omega)⟩
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  exact hvv.frame (t3f.trans t4f) (by have := hpre.hv; omega) (by simp) (by simp)
theorem chainRun_tsim (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    TSim image sk s0 (kChainK i e) (kChainCy i e) e e
      (do let v ← topChain leaf i 0 cap seed
          let last ← topChain leaf i cap (e - cap) v
          pure (v, last))
      (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
        RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
  have hcap := hpre.hcap
  have hvc := hpre.hvc
  have hvb := hpre.hv
  obtain ⟨t0, st0, h0⟩ := chain_entry hsub hpc seed hseed
  have p1 : TSim image sk t0 (sumTo (fun j => kRungK i (0 + j)) cap) (sumTo (fun j => kRungC i (0 + j)) cap)
      (sumTo (fun _ => 1) cap) (sumTo (fun _ => 1) cap)
      (topChain leaf i 0 cap seed) (fun v t => ChainHead b s0 valp cap v t) := by
    unfold topChain
    exact TSim.foldlM_range' 0 cap _ seed (fun j v t => ChainHead b s0 valp j v t) _ _ _ _
      (fun j hj v t ht => (chain_step hsub sk hpre (m := 0 + j) (by omega) (by omega)
        (by simpa using ht)).mono (fun v' u hu => by simpa using hu.1)) h0
  rcases Nat.lt_or_ge cap e with hlt | hge
  ·
    have hsplit : topChain leaf i cap (e - cap) = fun v =>
        T3.projHash (topChainHigh i cap) (topChainInput leaf i cap v) >>= fun v1 =>
          (List.range' (cap + 1) (e - cap - 1)).foldlM
            (fun value step => T3.projHash (topChainHigh i step) (topChainInput leaf i step value)) v1 := by
      funext v
      unfold topChain
      rw [show e - cap = e - cap - 1 + 1 by omega, List.range'_succ, List.foldlM_cons]
      rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t (kRungK i cap + 6 + (sumTo (fun j => kRungK i (cap + 1 + j)) (e - cap - 1) + 3))
          (kRungC i cap + 6 + (sumTo (fun j => kRungC i (cap + 1 + j)) (e - cap - 1) + 3))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (do let last ← topChain leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hsplit, bind_assoc]
      refine TSim.bind (chain_step_cap hsub sk hpre hlt rfl ht) (fun v1 u hu => ?_)
      have p2 := TSim.foldlM_range' (image := image) (sk := sk) (cap + 1) (e - cap - 1)
        (fun value step => T3.projHash (topChainHigh i step) (topChainInput leaf i step value)) v1
        (fun j v' w => ChainHead b s0 valp (cap + 1 + j) v' w ∧ DigAt w valp v)
        (fun j => kRungK i (cap + 1 + j)) (fun j => kRungC i (cap + 1 + j))
        (fun _ => 1) (fun _ => 1)
        (fun j hj v' w hw => (chain_step hsub sk hpre (m := cap + 1 + j) (by omega) (by omega)
          hw.1).mono (fun v'' w' hw' => ⟨by simpa [Nat.add_assoc] using hw'.1,
            hw.2.frame hw'.2 (by omega) (by simp; omega) (by simp; omega)⟩))
        ⟨by simpa using hu.1, hu.2.1⟩
      refine TSim.bind p2 (fun last w hw => ?_)
      have hw1 : ChainHead b s0 valp e last w := by
        have := hw.1; rwa [show cap + 1 + (e - cap - 1) = e by omega] at this
      obtain ⟨x, stx, xpc, xr, xf⟩ := chain_exit hsub hpre hw1 (by omega)
      exact TSim.pure_steps stx ⟨xpc, hw.2.frame xf (by omega) (by simp) (by simp),
        hw1.val.frame xf (by decide) (by simp) (by simp), (hw1.regs.trans xr).mono (by simp),
        (hw1.frame.trans xf).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold kChainK
      rw [show e = cap + 1 + (e - cap - 1) by omega, ksumTo_split]
      simp only [Nat.zero_add, show cap + 1 + (e - cap - 1) - cap - 1 = e - cap - 1 by omega]
      omega
    · unfold kChainCy
      rw [show e = cap + 1 + (e - cap - 1) by omega, ksumTo_split]
      simp only [Nat.zero_add, show cap + 1 + (e - cap - 1) - cap - 1 = e - cap - 1 by omega]
      omega
    all_goals simp only [sumTo_const]
    all_goals omega
  ·
    have he : cap = e := by omega
    have hz : topChain leaf i cap (e - cap) = fun v => pure v := by
      funext v; rw [show e - cap = 0 by omega]; rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t 9 9 0 0
          (do let last ← topChain leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hz]
      simp only [pure_bind]
      have ht' : ChainHead b s0 valp e v t := he ▸ ht
      obtain ⟨x, stx, xpc, xv, xr, xf⟩ := chain_exit_cap hsub hpre ht' he.symm
      exact TSim.pure_steps stx ⟨xpc, xv, ht'.val.frame xf (by decide) (by simp; omega)
        (by simp; omega), (ht'.regs.trans xr).mono (by simp [chainRegs]),
        (ht'.frame.trans xf).mono (fun A _ h => by
          unfold ChainW at *; rcases h with h | h; exact h; exact Or.inr (Or.inr h))⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold kChainK; subst he; simp only [Nat.zero_add]; omega
    · unfold kChainCy; subst he; simp only [Nat.zero_add]; omega
    all_goals simp only [sumTo_const]
    all_goals subst he; omega
end loop
end SigGolfCandidate.T3M.Keygen
