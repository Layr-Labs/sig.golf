import SigGolfCandidate.T3M_Images_Verify
import SigGolfCandidate.T3M_Keygen_Chain

section



namespace SigGolfCandidate.T3M.RevNet
open SigGolfCandidate.Rv SigGolfCandidate.T3.Rev
theorem tabRev_eq : ∀ n v, Images.tabRev n v = revBits n v
  | 0, _ => rfl
  | n + 1, v => by simp only [Images.tabRev, revBits, tabRev_eq n (v / 2)]
theorem verifyTabWord_eq (j : Nat) : Images.verifyTabWord j = revBits 64 (2048 + j) := tabRev_eq 64 _
def bvA (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .srl x 8#64) (BinOp.eval .sll (BinOp.eval .and x 255#64) 8#64)
def bvS (k M x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .and (BinOp.eval .srl x k) M) (BinOp.eval .sll (BinOp.eval .and x M) k)
def revNetBV (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .sll (bvS 1#64 21845#64 (bvS 2#64 13107#64 (bvS 4#64 3855#64 (bvA x)))) 48#64
@[irreducible] def ok1 (v : Nat) : Bool := revNetBV (BitVec.ofNat 64 v) == BitVec.ofNat 64 (revBits 64 v)
def chk (b : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => ok1 (b + n) && chk b n
theorem ok1_sound {v : Nat} (h : ok1 v = true) : revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  unfold ok1 at h; exact beq_iff_eq.mp h
theorem chk_succ (b n : Nat) : chk b (n + 1) = (ok1 (b + n) && chk b n) := by rw [chk]
theorem chk_sound (b : Nat) : ∀ n, chk b n = true → ∀ v, b ≤ v → v < b + n →
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v)
  | 0, _, v, _, h2 => absurd h2 (by omega)
  | n + 1, h, v, h1, h2 => by
    rw [chk_succ, Bool.and_eq_true] at h
    by_cases hv : v = b + n
    · subst hv; exact ok1_sound h.1
    · exact chk_sound b n h.2 v h1 (by omega)
theorem chk0 : chk 0 1024 = true := by decide +kernel
theorem chk1 : chk 1024 1024 = true := by decide +kernel
theorem chk2 : chk 2048 1024 = true := by decide +kernel
theorem chk3 : chk 3072 1024 = true := by decide +kernel
theorem revNetBV_eq (v : Nat) (hv : v < 2 ^ 12) :
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  rcases (show v < 1024 ∨ (1024 ≤ v ∧ v < 2048) ∨ (2048 ≤ v ∧ v < 3072) ∨ (3072 ≤ v ∧ v < 4096) by omega) with
    h | h | h | h
  · exact chk_sound 0 1024 chk0 v (by omega) (by omega)
  · exact chk_sound 1024 1024 chk1 v h.1 (by omega)
  · exact chk_sound 2048 1024 chk2 v h.1 (by omega)
  · exact chk_sound 3072 1024 chk3 v h.1 (by omega)
end SigGolfCandidate.T3M.RevNet
end

section



section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem sub116_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]
theorem sub117_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]
theorem sub118_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]
theorem slt_shl52n (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) 0#64 = decide (2048 ≤ h0 % 4096) := by
  have e : BitVec.ofNat 64 h0 <<< 52 = BitVec.ofNat 64 (h0 % 4096 * 2 ^ 52) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num
    omega
  rw [e, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have hr := Nat.mod_lt h0 (show 0 < 4096 by norm_num)
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show h0 % 4096 * 2 ^ 52 < 2 ^ 64 by omega)]
  by_cases hc : 2048 ≤ h0 % 4096
  · simp only [hc, decide_true]
    rw [if_neg (by omega)]
    simp <;> omega
  · simp only [hc, decide_false]
    rw [if_pos (by omega)]
    simp <;> omega
theorem slt_shl52n' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) (0 : Word) = decide (2048 ≤ h0 % 4096) := slt_shl52n h0
theorem slt_shl52 (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) (0 : Word) = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0
theorem slt_shl52' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) 0#64 = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0
/-- Node window (C4, b3cc11b's keygen words): left/right children copied to `NODE`/`NODE + 48`, one-word label
`(x21 ||| tree << 32) + k` at `NODE + 16`, zero high word, `x29 = k % 2` (the half selector). -/
theorem sub120_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x29 = BitVec.ofNat 64 (k % 2) ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32)) + BitVec.ofNat 64 k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  have hc := codeAt_sub120K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  have hobl : Oblig.all s st_120K.obl := by
    simp only [st_120K, kblk_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound run_120K hc s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_120K, kblk_120.res, rv_simp, h24]
    exact ofNat_and1 k
  · simp [st_120K, kblk_120.res, rv_simp]
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h9, h24]
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n []
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_120K, kblk_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, st_120K, kblk_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem sub214_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_rev h) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]
theorem valid8_ofNat (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem node48_m24 : BitVec.ofNat 64 (NODE + 48) + BitVec.ofNat 64 18446744073709551592 = BitVec.ofNat 64 (NODE + 24) := by
  rw [ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, NODE]
theorem sub140_obl (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    Oblig.all s st_140.obl := by
  simp only [st_140, blk117_140.res, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
    BitVec.ofNat_eq_ofNat]
  rw [h30, node48_m24]
  exact valid8_ofNat _ (by simp only [NODE]) (by simp only [NODE]; omega)
theorem sub140_m24 (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    memEval s st_140.mem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
theorem sub140_frame (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) (X : Nat)
    (hX : X < 2 ^ 64) (hn : X ≠ 131608) :
    memEval s st_140.mem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
  rw [if_neg (by omega)]
/-- C4 (b3cc11b's keygen word): the hash call setup also scales the half selector, `x29 = 16 p`. -/
theorem sub140_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (p : Nat) (h29 : s.getReg .x29 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4) ∧
      RegsExcept s t [.x10, .x11, .x12, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := codeAt_sub140K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  refine ⟨_, symRun_sound run_140K hc s hpc (by simp [st_140K, kblk_140.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp only [Result.toState_getReg, st_140K, kblk_140.res, rv_simp, h29]
    rw [ofNat_shl]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_140K, kblk_140.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_140K, kblk_140.res, rv_simp]
def revX (tag : Nat) : Nat := if tag = 10 then 28 else 0
/-- Base of the node label word in the `s5` register: the C4 top label is the heap itself (base 0; it was 64); the
lower trees (the sign's) keep `hyperWord (lay - 1) tree`. -/
def nodeLo (lay tree : Nat) : Nat := if lay = 0 then 0 else (T3.hyperWord (lay - 1) tree).toNat
theorem nodeLo_mod (lay tree : Nat) : nodeLo lay tree % 4096 < 2048 := by
  unfold nodeLo; split
  · decide
  · rw [T3.hyperWord_toNat]; simp only [Nat.reducePow]; omega
/-- C4: the top node tweak is the one-word label `0#64 ++ heap` (`nodeLo 0 tree = 0`). -/
theorem nodeTweak_3_top (tree heap : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) :
    T3.nodeTweak 3 0 tree heap = 0#64 ++ BitVec.ofNat 64 (nodeLo 0 tree + heap) := by
  rw [T3.nodeTweak_top, T3.topNodeWord_eq h1 h2]
  simp [nodeLo]
/-- The tree node block from `b + 120` to the hash call (C4: no reversed labels, one-word label). -/
theorem sub120_full {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (k % 2 * 2 ^ 4) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32)) + BitVec.ofNat 64 k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x29, t1x30, m0, m8, m16, m24, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree h0 ha8 hk htree hdis h2 h24 h9 h21
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tx29, tr, tf⟩ := sub140_spec h t1 t1pc (k % 2) t1x29
  have g : ∀ X, X < 2 ^ 64 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => tf.get hX (fun h => h)
  refine ⟨t, (st1.trans stt).of_eq (by omega) (by omega), tpc, tx10, tx11, tx12, tx29, ?_, ?_, ?_, ?_, ?_, ?_,
    t1r.trans tr, (t1f.trans tf).mono (fun X _ hX => by rcases hX with hX | hX; exact hX; exact hX.elim)⟩
  · rw [g NODE (by decide), m0]
  · rw [g (NODE + 8) (by decide), m8]
  · rw [g (NODE + 16) (by decide), m16]
  · rw [g (NODE + 24) (by decide), m24]
  · rw [g (NODE + 48) (by decide), m48]
  · rw [g (NODE + 56) (by decide), m56]
theorem fetch_sub146 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_146 h).fetch s hpc).trans rfl
theorem sub159_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]
end SigGolfCandidate.T3M.Keygen
end
section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
structure LevArgs where
  tag : Nat
  lay : Nat
  tree : Nat
  h : Nat
  arena : Nat
  ret : Nat
namespace LevArgs
variable (B : LevArgs)
def levK : Nat := 3 + sumTo (fun j => 6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
def levC : Nat := 3 + sumTo (fun j => 6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
def levN : Nat := sumTo (fun j => 2 ^ (B.h - 1 - j)) B.h
end LevArgs
def LevW (B : LevArgs) (X : Nat) : Prop :=
  X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨ X = NODE + 56 ∨
    (NOUT ≤ X ∧ X < NOUT + 32) ∨ (B.arena + 16 ≤ X ∧ X < B.arena + 16 * 2 ^ B.h)
def levRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x24, .x28, .x29, .x30]
structure LevPre (s : MachineState) (B : LevArgs) (leaves : List Digest) : Prop where
  x1 : s.getReg .x1 = pcOf B.ret
  x2 : s.getReg .x2 = BitVec.ofNat 64 B.arena
  x5 : s.getReg .x5 = 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 B.tree
  x15 : s.getReg .x15 = BitVec.ofNat 64 B.h
  x21 : s.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree)
  tag3 : B.tag = 3
  hlay : B.lay < 4
  htree : B.tree < 2 ^ 32
  hh1 : 1 ≤ B.h
  hh : B.h ≤ 12
  ha8 : B.arena % 8 = 0
  ha : B.arena + 16 * 2 ^ (B.h + 1) ≤ 2 ^ 24
  has : NOUT + 32 ≤ B.arena ∨ B.arena + 16 * 2 ^ (B.h + 1) ≤ NODE
  z32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  hlen : leaves.length = 2 ^ B.h
  hleaves : DigsAt s (B.arena + 16 * 2 ^ B.h) leaves
def HeapAt (t : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest)) : Prop :=
  levels.length = ℓ + 1 ∧ ∀ l ≤ ℓ, (levels.getD l []).length = 2 ^ (B.h - l) ∧
    DigsAt t (B.arena + 16 * 2 ^ (B.h - l)) (levels.getD l [])
structure LevInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ B.h / 2 ^ (ℓ + 1))
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
structure NodeInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (pre : List Digest) (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1) + pre.length)
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
  cur : DigsAt t (B.arena + 16 * 2 ^ (B.h - ℓ - 1)) pre
theorem nodeInput_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem wordsOf_nodeInput (tag lay tree heap : Nat) (l r : Digest)
    (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 tag lay tree tree),
        BitVec.ofNat 64 (T3.nodeWord tag 0 heap), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_packed_header _ _ _ _ _ hn, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl
theorem wordsOf_nodeInput_3 (lay tree heap : Nat) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header 3 lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 3 lay tree tree),
        BitVec.ofNat 64 (hdr1 heap 0), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_nodeInput 3 lay tree heap l r (by decide), nodeWord_3]
/-- C4: the words of a top node input (label `nodeLo 0 tree + heap`, zero high word, zero pad). -/
theorem wordsOf_nodeInputT (tree heap : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (T3.nodeTweak 3 0 tree heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (nodeLo 0 tree + heap),
        0, 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16, nodeTweak_3_top tree heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (nodeLo 0 tree + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]; rfl
theorem nodeInputT_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (T3.nodeTweak tag lay tree heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem two_pow_split {h l : Nat} (hl : l < h) : 2 ^ (h - l) = 2 * 2 ^ (h - l - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega
/-! The keygen top-tree level routine (top-bytes layer: node nonces) is proved in `TopTree.lean`
(`sub113`/`sub147`/`sub157` now hook into KINIT/KCHK/KNEXT). -/
end SigGolfCandidate.T3M.Keygen
end
end
