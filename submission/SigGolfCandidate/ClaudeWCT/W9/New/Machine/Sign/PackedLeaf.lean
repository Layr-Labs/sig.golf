import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.LowerRuns
import SigGolfCandidate.T3M.Sign.SeedLeafPhases
import SigGolfCandidate.T3M.Sign.PackedLowTree

/-!
# Stage B (campaign X1): the lower leaf of the sign image refines `WCT9.buildLeafPF`

Chain 0 of a lower leaf runs the coefficient loop (`coef_phase`: the 17 packed halves with ordinals
`17 L .. 17 L + 16` of `lowerSeedPair lay tree` into `COEF`, carry at `SEEDS + 16`); every chain `j` then evaluates
its seed `familyEval coefs (j + 1)` with the Horner loop (`lower_seed`) and runs the unchanged chain code
(`chain_cont`). The seed code writes the FTS scratch (`BScr`), outside `LeafW`; the shared leaf invariants
(`LeafInv`, `LeafPreS`, keygen-shared) are therefore used relative to the *hybrid* base state `hyb s0 t` (the leaf
entry state `s0` with the scratch of the current state `t`), which differs from `s0` only on `BScr`.
-/

namespace ClaudeWCT.W9.Machine.Sign.PackedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN LEAFPK LOUT LeafArgs LeafW leafRegs LeafInv ChainW chainRegs
  chainProg rungK rungC leafBlocks slot slotK slot_ge slot_lt chainCount_cases)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.Packed (BScr lowLeafC)
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit privatePair header privateInput)
open ClaudeWCT.Arith
set_option maxRecDepth 10000

set_option maxHeartbeats 0 in
theorem signCode_drop_new : Images.signImage.code.drop 11003 = signNew ++ Images.signImage.code.drop 20771 := by
  decide +kernel
theorem newCodeAt_image : NewCodeAt Sign.image := ⟨_, signCode_drop_new.symm⟩

/-! ### Hybrid base states -/

/-- `s0` with the scratch region `BScr` of `t`. -/
def hyb (s0 t : MachineState) : MachineState :=
  { s0 with mem := fun a => if 0x50000 ≤ a.toNat ∧ a.toNat < 0x52010 then t.mem a else s0.mem a }
/-- `s` is a base state for `t` relative to the leaf entry `s0`: registers of `s0`, memory of `s0` outside the
scratch, memory of `t` on the scratch. -/
structure HybOf (s0 s t : MachineState) : Prop where
  regs : ∀ r, s.getReg r = s0.getReg r
  base : Frame s0 s BScr
  scr : ∀ A, A < 2 ^ 64 → BScr A → s.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A)
theorem hyb_of (s0 t : MachineState) : HybOf s0 (hyb s0 t) t := by
  refine ⟨fun r => rfl, fun A hA hn => ?_, fun A hA h => ?_⟩
  · show (if 0x50000 ≤ (BitVec.ofNat 64 A).toNat ∧ (BitVec.ofNat 64 A).toNat < 0x52010 then t.mem _ else s0.mem _) =
      s0.mem _
    rw [toNat_ofNat_lt hA, if_neg (show ¬ (0x50000 ≤ A ∧ A < 0x52010) from hn)]
  · show (if 0x50000 ≤ (BitVec.ofNat 64 A).toNat ∧ (BitVec.ofNat 64 A).toNat < 0x52010 then t.mem _ else s0.mem _) =
      t.mem _
    rw [toNat_ofNat_lt hA, if_pos (show 0x50000 ≤ A ∧ A < 0x52010 from h)]
theorem HybOf.frame {s0 s t u : MachineState} {W : Nat → Prop} (h : HybOf s0 s t) (hf : Frame t u W)
    (hW : ∀ A, W A → ¬ BScr A) : HybOf s0 s u :=
  ⟨h.regs, h.base, fun A hA hb => (h.scr A hA hb).trans (hf.get hA (fun hw => hW A hw hb)).symm⟩
theorem HybOf.refl_of {s0 t : MachineState} (hf : Frame s0 t (fun A => ¬ BScr A)) : HybOf s0 s0 t :=
  ⟨fun _ => rfl, Frame.refl _ _, fun A hA hb => (hf.get hA (fun h => h hb)).symm⟩

theorem not_bscr {X : Nat} (h : X < 0x50000) : ¬ BScr X := fun hb => by unfold BScr at hb; omega

theorem LeafPreS.transfer {sk : BitVec 256} {s0 s : MachineState} {A : LeafArgs} (h : LeafPreS sk s0 A)
    (hr : ∀ r, s.getReg r = s0.getReg r) (hf : Frame s0 s BScr) (hd : A.digp + A.n ≤ 0x50000) :
    LeafPreS sk s A := by
  have g : ∀ X, X < 0x50000 → s.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) :=
    fun X hX => hf.get (by omega) (not_bscr hX)
  refine
    { x1 := by rw [hr]; exact h.x1
      x5 := by rw [hr]; exact h.x5
      x8 := by rw [hr]; exact h.x8
      x9 := by rw [hr]; exact h.x9
      x18 := by rw [hr]; exact h.x18
      x22 := by rw [hr]; exact h.x22
      x23 := by rw [hr]; exact h.x23
      x25 := by rw [hr]; exact h.x25
      x26 := by rw [hr]; exact h.x26
      x27 := by rw [hr]; exact h.x27
      x31 := by rw [hr]; exact h.x31
      htree := h.htree
      hleaf := h.hleaf
      hroute := h.hroute
      hleafHeight := h.hleafHeight
      hsteps := h.hsteps
      p0 := by rw [g _ (by decide)]; exact h.p0
      p8 := by rw [g _ (by decide)]; exact h.p8
      p32 := by rw [g _ (by decide)]; exact h.p32
      p40 := by rw [g _ (by decide)]; exact h.p40
      p48 := by rw [g _ (by decide)]; exact h.p48
      p56 := by rw [g _ (by decide)]; exact h.p56
      z0 := by rw [g _ (by decide)]; exact h.z0
      z8 := by rw [g _ (by decide)]; exact h.z8
      z32 := by rw [g _ (by decide)]; exact h.z32
      z40 := by rw [g _ (by decide)]; exact h.z40
      hsl := h.hsl
      hdig := fun i hi => by
        rw [hf.getByte (by omega) (not_bscr (by omega))]; exact h.hdig i hi
      hdigb := h.hdigb
      hdigp := h.hdigp
      hdigW := h.hdigW
      hv8 := h.hv8
      hv := h.hv
      hvs := h.hvs
      hd8 := h.hd8
      hd := h.hd
      hds := h.hds
      hdv := h.hdv }

/-- Writes of the seed code that stay inside the leaf write set or the scratch. -/
def SeedW (X : Nat) : Prop := BScr X ∨ X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)

theorem LeafW_of_seedW {A : LeafArgs} {X : Nat} (h : X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)) :
    LeafW A X := by
  rcases h with h | h | h
  · unfold LeafW; left; exact h
  · unfold LeafW; right; left; exact h
  · unfold LeafW; right; right; left; exact h

/-- Rebase a leaf invariant across a seed-code step. -/
theorem LeafInv.rebase {s0 s t s' u : MachineState} {A : LeafArgs} {j : Nat} {st : List Digest × List Digest}
    (ht : LeafInv s A j st t) (hs : HybOf s0 s t) (hs' : HybOf s0 s' u) {R : List Reg}
    (hr : RegsExcept t u R) (hR : ∀ r ∈ R, r ∈ leafRegs ∧ r ≠ .x19 ∧ r ≠ .x23 ∧ r ≠ .x3)
    {W : Nat → Prop} (hf : Frame t u W) (hW : ∀ X, W X → SeedW X)
    (hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hv : A.valp + 16 * A.n ≤ 0x50000)
    (hj : j ≤ A.n) : LeafInv s' A j st u := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have nW : ∀ X, X < 0x50000 → ¬ (X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)) → ¬ W X := by
    intro X h1 h2 hw
    rcases hW X hw with h | h
    · exact not_bscr h1 h
    · exact h2 h
  have gr : ∀ r, r = .x19 ∨ r = .x23 ∨ r = .x3 → u.getReg r = t.getReg r := fun r h =>
    hr.get (fun hm => by
      obtain ⟨-, h1, h2, h3⟩ := hR r hm
      rcases h with rfl | rfl | rfl <;> simp_all)
  have hlv : ∀ X, LEAFPK ≤ X → X < LEAFPK + 16 * (A.n + 2) → ¬ W X := fun X h1 h2 =>
    nW X (by simp only [LEAFPK] at *; omega) (by simp only [LEAFPK, PRIV, SEEDS] at *; omega)
  refine ⟨by rw [gr _ (by simp)]; exact ht.x19, by rw [gr _ (by simp)]; exact ht.x23,
    by rw [gr _ (by simp)]; exact ht.x3, fun r hr' => ?_, fun X hX hn' => ?_, ?_, ?_, ht.elen, ht.vlen,
    fun hso c hc => ?_, ?_⟩
  · rw [hr.get (fun h => hr' (hR r h).1), ht.regs.get hr', hs.regs, hs'.regs]
  · by_cases hb : BScr X
    · rw [hs'.scr X hX hb]
    · have hnw : ¬ W X := fun hw => by
        rcases hW X hw with h | h
        · exact hb h
        · exact hn' (LeafW_of_seedW h)
      rw [hf.get hX hnw, ht.frame.get hX hn', hs.base.get hX hb, hs'.base.get hX hb]
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh16
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh24
  · have h1 := slot_ge A.lay c; have h2 := slot_lt A.lay (show c < A.n by omega)
    exact (ht.ends hso c hc).frame hf (by omega) (hlv _ (by omega) (by omega)) (hlv _ (by omega) (by omega))
  · exact ht.vals.frame hf (by rw [ht.vlen]; omega) (fun X h1 h2 => by
      rw [ht.vlen] at h2
      exact nW X (by omega) (by simp only [PRIV, SEEDS, LEAFPK] at *; omega))

theorem LeafW_not_bscr {A : LeafArgs} (hv : A.valp + 16 * A.n ≤ 0x50000) (hd : A.dest + 16 ≤ 0x50000) {X : Nat}
    (h : LeafW A X) : ¬ BScr X := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  unfold LeafW at h
  intro hb; unfold BScr at hb
  simp only [PRIV, SEEDS, CHAIN, LEAFPK, LOUT] at h
  split_ifs at h <;> omega

/-! ### The coefficient loop (chain 0) -/

theorem packedSecret_odd {q : Nat} (hq : q % 2 = 1) (pq : Nat → SigGolfCandidate.T3.M (Digest × Digest))
    (carry : Digest) : WCT9.packedSecret pq q carry = pure (carry, carry) := by
  unfold WCT9.packedSecret; rw [if_neg (by omega)]
theorem packedSecret_even {q : Nat} (hq : q % 2 = 0) (pq : Nat → SigGolfCandidate.T3.M (Digest × Digest))
    (carry : Digest) : WCT9.packedSecret pq q carry = (pq (q / 2) >>= fun seeds => pure (seeds.1, seeds.2)) := by
  unfold WCT9.packedSecret; rw [if_pos hq]
theorem lower_n {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem lower_height {lay : Layer} (h : lay ≠ 0) : 2 ^ SigGolfCandidate.T3.height lay ≤ 128 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide

def nxt (L j : Nat) : Nat := j + (17 * L + j) % 2
def coefRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x17, .x28, .x29, .x30]
def CoefW (X : Nat) : Prop :=
  (COEF ≤ X ∧ X < COEF + 288) ∨ X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)
/-- State of the coefficient loop after `j` monadic coefficient steps (the machine is at the head of the
iteration that queries pair `(17 L + nxt L j) / 2`, or at `SEED` once all 17 are in place). -/
structure CoefSt (t : MachineState) (lay L j : Nat) (st : List Digest × Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (if nxt L j < 17 then cqI else seedI)
  x29 : u.getReg .x29 = BitVec.ofNat 64 (COEF + 16 * nxt L j)
  x6 : u.getReg .x6 = BitVec.ofNat 64 (hdrB lay ((17 * L + nxt L j) / 2))
  x17 : u.getReg .x17 = BitVec.ofNat 64 (2 ^ 32)
  x30 : u.getReg .x30 = BitVec.ofNat 64 (COEF + 272)
  regs : RegsExcept t u coefRegs
  frame : Frame t u CoefW
  len : st.1.length = j
  coefs : ∀ i < j, DigAt u (COEF + 16 * i) (st.1.getD i 0)
  odd : (17 * L + j) % 2 = 1 → DigAt u (COEF + 16 * j) st.2
  carry : (0 < j ∨ L % 2 = 1) → DigAt u (SEEDS + 16) st.2

def coefC : Nat := 1 + 1 + 24 + 4 + 17 * 26

theorem getD_append_last {l : List Digest} {d : Digest} {i : Nat} (hl : l.length = i) :
    (l ++ [d]).getD i 0 = d := by
  rw [List.getD_eq_getElem _ _ (by simp [hl]), List.getElem_append_right (by omega)]; simp [hl]
theorem getD_append_lt {l : List Digest} {d : Digest} {i : Nat} (hi : i < l.length) :
    (l ++ [d]).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

section coef
variable (sk : BitVec 256) {s0 s t : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre

theorem coef_phase (hlay : A.lay ≠ 0) (ht : LeafInv s A 0 ([], []) t) (hs : HybOf s0 s t)
    (hpc : t.pc = pcOf (1013 + 41)) {carry : Digest} (hcar : A.leaf % 2 = 1 → DigAt t (SEEDS + 16) carry) :
    TBSim Sign.image sk t coefC (WCT9.lowerCoefs A.lay A.tree A.leaf carry)
      (fun r u => u.pc = pcOf seedI ∧ CoefAtN 17 u r.1 ∧ r.1.length = 17 ∧ DigAt u (SEEDS + 16) r.2 ∧
        RegsExcept t u coefRegs ∧ Frame t u CoefW) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 43 := lower_n hlay
  have hvs := hpre.hvs
  have hv := hpre.hv
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hlay0 : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hlh := hpre.hleafHeight
  have h2h := lower_height hlay
  have hleaf : A.leaf < 2 ^ 7 := by omega
  have htree := hpre.htree
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => by rw [ht.regs.get hr, hs.regs]
  have r8 : t.getReg .x8 = BitVec.ofNat 64 A.lay.val := by rw [g _ (by simp [leafRegs]), hpre.x8]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 A.tree := by rw [g _ (by simp [leafRegs]), hpre.x9]
  have r18 : t.getReg .x18 = BitVec.ofNat 64 A.leaf := by rw [g _ (by simp [leafRegs]), hpre.x18]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [leafRegs]), hpre.x5]
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  -- the secret key words of the private input
  have hLP : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → ¬ LeafW A X := by
    intro X hX hw
    have := hpre.hds; have := hpre.hdv
    unfold LeafW at hw
    rw [if_neg hlay] at hw
    simp only [PRIV, SEEDS, CHAIN, LEAFPK, LOUT] at *
    omega
  have frT : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (ht.frame.get (by simp only [PRIV] at hX; omega) (hLP X hX)).trans
      (hs.base.get (by simp only [PRIV] at hX; omega) (not_bscr (by simp only [PRIV] at hX; omega)))
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.Seed.sub41_spec hsub t hpc 0 A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := hook_spec t1 (by rw [t1pc])
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  obtain ⟨t3, k3, c3, st3, hc3, t3pc, t3x6, t3x29, t3odd, t3r, t3f⟩ := step_D0 newCodeAt_image t2 t2pc
    (by rw [e12.get (by simp), r8]) hlay0 hlay' (by rw [e12.get (by simp), r18]) (by omega)
    (by rw [e12.get (by simp)]; exact ht.x19)
  obtain ⟨t4, st4, t4pc, t4x17, t4x30, t4r, t4f⟩ := step_C0 newCodeAt_image t3 t3pc
  have hL17 : (17 * A.leaf) % 2 = A.leaf % 2 := by omega
  have h0 : CoefSt t A.lay.val A.leaf 0 ([], carry) t4 := by
    have hnx : nxt A.leaf 0 = A.leaf % 2 := by unfold nxt; omega
    refine ⟨?_, ?_, ?_, t4x17, t4x30, ?_, ?_, rfl, fun i hi => absurd hi (by omega), fun h => ?_, fun h => ?_⟩
    · rw [t4pc, hnx, if_pos (by omega)]
    · rw [t4r.get (by simp), t3x29, hnx]
    · rw [t4r.get (by simp), t3x6, hnx]
    · exact ((e12.trans t3r).trans t4r).mono (by simp [coefRegs])
    · exact ((f12.trans t3f).trans t4f).mono (fun X _ h => by
        rcases h with (h | h) | h
        · exact h.elim
        · left; unfold COEF at *; omega
        · exact h.elim)
    · have hodd : A.leaf % 2 = 1 := by omega
      exact (t3odd hodd carry ((hcar hodd).frame f12 (by decide) (by simp) (by simp))).frame t4f (by decide)
        (by simp) (by simp)
    · have hodd : A.leaf % 2 = 1 := by omega
      exact (((hcar hodd).frame f12 (by decide) (by simp) (by simp)).frame t3f (by decide)
        (by decide) (by decide)).frame t4f (by decide) (by simp) (by simp)
  have hloop := TBSim.foldlM_range' (image := Sign.image) (sk := sk) 0 17
    (fun (state : List Digest × Digest) j => do
      let (coef, carry) ← WCT9.packedSecret (WCT9.lowerSeedPair A.lay A.tree) (WCT9.lowerCoefOrdinal A.leaf j)
        state.2
      pure (state.1 ++ [coef], carry)) ([], carry) (fun j st u => CoefSt t A.lay.val A.leaf j st u) 26
    (fun j hj st u hu => ?_) h0
  · rw [show List.range' 0 17 = List.range 17 from List.range_eq_range'.symm] at hloop
    refine TBSim.mono (TBSim.steps (st1.trans (st2.trans (st3.trans st4))) hloop) (by unfold coefC; omega)
      (fun r u hu => ⟨?_, fun k hk => hu.coefs k hk, hu.len, hu.carry (Or.inl (by norm_num)), hu.regs, hu.frame⟩)
    rw [hu.pc, if_neg (by unfold nxt; omega)]
  -- one coefficient step
  simp only [Nat.zero_add]
  have hq : WCT9.lowerCoefOrdinal A.leaf j = 17 * A.leaf + j := rfl
  have g4 : ∀ r, r ∉ coefRegs → r ∉ leafRegs → u.getReg r = s0.getReg r := fun r h1 h2 => by
    rw [hu.regs.get h1, g r h2]
  by_cases hpar : (17 * A.leaf + j) % 2 = 1
  · rw [hq, packedSecret_odd hpar, pure_bind]
    have hnx : nxt A.leaf (j + 1) = nxt A.leaf j := by unfold nxt; omega
    refine TBSim.mono (TBSim.pure ⟨?_, ?_, ?_, hu.x17, hu.x30, hu.regs, hu.frame, by simp [hu.len], fun i hi => ?_,
      fun h => absurd h (by omega), fun _ => ?_⟩) (by norm_num) (fun _ _ h => h)
    · rw [hnx]; exact hu.pc
    · rw [hnx]; exact hu.x29
    · rw [hnx]; exact hu.x6
    · by_cases hij : i < j
      · rw [getD_append_lt (by rw [hu.len]; exact hij)]; exact hu.coefs i hij
      · have hi' : i = j := by omega
        subst hi'
        rw [getD_append_last hu.len]; exact hu.odd hpar
    · exact hu.carry (by by_cases h : 0 < j; exact Or.inl h; exact Or.inr (by omega))
  · have hpar' : (17 * A.leaf + j) % 2 = 0 := by omega
    have hnx : nxt A.leaf j = j := by unfold nxt; omega
    have hnx1 : nxt A.leaf (j + 1) = j + 2 := by unfold nxt; omega
    have hpair : (17 * A.leaf + nxt A.leaf j) / 2 = (17 * A.leaf + j) / 2 := by rw [hnx]
    rw [hq, packedSecret_even hpar', bind_assoc]
    simp only [pure_bind]
    unfold WCT9.lowerSeedPair
    obtain ⟨u1, su1, e1, u1pc, u1x10, u1x11, u1x12, u1x28, m16, m24, u1r, u1f⟩ :=
      step_CQ newCodeAt_image u (by rw [hu.pc, hnx, if_pos hj])
    have hm16 : u1.getMem (BitVec.ofNat 64 (PRIV + 16)) =
        BitVec.ofNat 64 (SigGolfCandidate.T3M.hdr0 0 A.lay.val A.tree ((17 * A.leaf + j) / 2)) := by
      show u1.getMem (BitVec.ofNat 64 0x20010) = _
      rw [m16, hu.x6, hpair, hdr0_eq 0 _ _ _ (by norm_num) hlay' htree (by omega)]
      unfold hdrB; congr 1
    have hm24 : u1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (SigGolfCandidate.T3M.hdr1 A.tree 0) := by
      show u1.getMem (BitVec.ofNat 64 0x20018) = _
      rw [m24, g4 _ (by simp [coefRegs]) (by simp [leafRegs]), hpre.x9, hdr1_eq A.tree 0 htree (by norm_num)]
      congr 1
    have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
        X = PRIV + 56) → u1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX => by
      rw [u1f.get (by simp only [PRIV] at hX; omega) (by simp only [PRIV] at hX; omega),
        hu.frame.get (by simp only [PRIV] at hX; omega) (by unfold CoefW COEF; simp only [PRIV, SEEDS] at *; omega),
        frT X hX]
    have hqin : hashInput u1 =
        toQ (privateInput sk (.inl (header 0 A.lay.val A.tree ((17 * A.leaf + j) / 2) 0))) := by
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
      rw [u1r.get (by simp), g4 _ (by simp [coefRegs]) (by simp [leafRegs]), hpre.x5]
    refine TBSim.mono (TBSim.steps su1 (TBSim.privatePair_bind' (W := 12) e1 h5 hva hqin (fun a => ?_)))
      (by norm_num) (fun _ _ h => h)
    have hP : COEF + 16 * j + 32 ≤ COEF + 288 := by omega
    obtain ⟨u3, k3, su3, hk3, u3pc, u3x29, u3x6, u3lo, u3hi, u3r, u3f⟩ := step_CP newCodeAt_image (writeHash u1 a)
      (by rw [pc_writeHash, u1pc, pcOf_add4]) (P := COEF + 16 * j) (by rw [getReg_writeHash]; exact u1x28)
      (by rw [getReg_writeHash, u1r.get (by simp), hu.x29, hnx]) (by rw [getReg_writeHash, u1r.get (by simp)]; exact hu.x30)
      (by unfold COEF; omega) (by omega) hP
    have hwf := Frame.writeHash u1 a SEEDS u1x12 (by decide)
    have lo := DigAt.writeHash_lo u1 a SEEDS u1x12 (by decide)
    have hi := DigAt.writeHash_hi u1 a SEEDS u1x12 (by decide)
    have f13 : Frame u u3 (fun X => ((X = 0x20018 ∨ X = 0x20010) ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)) ∨
        (COEF + 16 * j ≤ X ∧ X < COEF + 16 * j + 32)) := (u1f.trans hwf).trans u3f
    refine TBSim.mono (TBSim.pure_steps' su3 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi' => ?_, fun _ => ?_, fun _ => ?_⟩)
      hk3 (fun _ _ h => h)
    · rw [u3pc, hnx1]; congr 1; unfold COEF; split_ifs <;> omega
    · rw [u3x29, hnx1, show COEF + 16 * j + 32 = COEF + 16 * (j + 2) by ring]
    · rw [u3x6, getReg_writeHash, getReg_writeHash, u1r.get (by simp), u1r.get (by simp), hu.x6, hu.x17,
        ofNat_add_ofNat, hnx1, hpair, show (17 * A.leaf + (j + 2)) / 2 = (17 * A.leaf + j) / 2 + 1 by omega]
      exact congrArg (BitVec.ofNat 64) (by unfold hdrB; ring)
    · rw [u3r.get (by simp), getReg_writeHash, u1r.get (by simp)]; exact hu.x17
    · rw [u3r.get (by simp), getReg_writeHash, u1r.get (by simp)]; exact hu.x30
    · exact ((hu.regs.trans u1r).trans ((show RegsExcept u1 (writeHash u1 a) [] from
        fun r _ => getReg_writeHash u1 a r).trans u3r)).mono (by simp [coefRegs])
    · exact (hu.frame.trans f13).mono (fun X _ h => by
        unfold CoefW at *
        rcases h with h | ((h | h) | h) | h
        · exact h
        · right; right; left; simp only [PRIV]; omega
        · right; left; simp only [PRIV]; omega
        · right; right; right; exact h
        · left; unfold COEF at *; omega)
    · simp [hu.len]
    · by_cases hij : i < j
      · rw [getD_append_lt (by rw [hu.len]; exact hij)]
        exact (hu.coefs i hij).frame f13 (by unfold COEF; omega)
          (by unfold COEF; simp only [SEEDS]; omega) (by unfold COEF; simp only [SEEDS]; omega)
      · have hi' : i = j := by omega
        subst hi'
        rw [getD_append_last hu.len]; exact u3lo _ lo
    · rw [show COEF + 16 * (j + 1) = COEF + 16 * j + 16 by ring]; exact u3hi _ hi
    · exact hi.frame u3f (by decide) (by unfold COEF; simp only [SEEDS]; omega)
        (by unfold COEF; simp only [SEEDS]; omega)
end coef

/-! ### One chain: Horner seed, then the unchanged chain code -/

theorem lower_sel {lay : Layer} (h : lay ≠ 0) (j : Nat) : SigGolfCandidate.T3M.Keygen.selectorExtra lay j = 0 := by
  unfold SigGolfCandidate.T3M.Keygen.selectorExtra; rw [if_neg h]
theorem lower_e {A : LeafArgs} (hlay : A.lay ≠ 0) (hso : A.so = false) (j : Nat) : A.e j = 7 := by
  unfold LeafArgs.e; rw [hso]; simp only [Bool.false_eq_true, if_false]; unfold maxDigit; rw [if_neg hlay]
theorem lower_rungC {lay : Layer} (h : lay ≠ 0) : rungC lay = if lay = 1 then 45 else 46 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide
theorem lower_blocks {lay : Layer} (h : lay ≠ 0) : leafBlocks lay = 11 := by
  unfold leafBlocks; rw [lower_n h]

/-- The chain body of `buildLeafPF` (= `WCT9.leafStepF`). -/
def leafStepB (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Nat) : SigGolfCandidate.T3.M (List Digest × List Digest) := do
  let digit := digits.getD i 0
  let value ← SigGolfCandidate.T3.chain lay tree leaf i 0 digit (WCT9.lowerFamilySeed coefs i)
  let last ← SigGolfCandidate.T3.chain lay tree leaf i digit (maxDigit lay i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])
theorem buildLeafPF_eq (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    WCT9.buildLeafPF lay tree leaf digits carry = (do
      let coefs ← WCT9.lowerCoefs lay tree leaf carry
      let rows ← (List.range (chainCount lay)).foldlM (leafStepB lay tree leaf digits coefs.1) ([], [])
      let root ← SigGolfCandidate.T3.leafHash lay tree leaf rows.1
      pure ((root, rows.2), coefs.2)) := rfl

section chain
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre

theorem chain_cont (hlay : A.lay ≠ 0) (hso : A.so = false) {j : Nat} (hj : j < A.n)
    {st : List Digest × List Digest} (u : MachineState) (seed carry : Digest) (upc : u.pc = pcOf (1013 + 61))
    (hu : LeafInv s0 A j st u) (h28 : u.getReg .x28 = BitVec.ofNat 64 0) (hseed : DigAt u SEEDS seed)
    (hc : DigAt u (SEEDS + 16) carry) :
    TSim Sign.image sk u (16 + (rungK A.lay * A.e j + 10) + (4 + (11 + slotK A.lay j)))
      (16 + (rungC A.lay * A.e j + 10) + (4 + (11 + slotK A.lay j))) (A.e j) (A.e j)
      ((fun r : Digest × Digest => (st.1 ++ [r.2], st.2 ++ [r.1])) <$> chainProg A j seed)
      (fun st' w => w.pc = pcOf (1013 + 41) ∧ LeafInv s0 A (j + 1) st' w ∧ DigAt w (SEEDS + 16) carry) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 43 := lower_n hlay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLO : LOUT = 132032 := rfl
  have hvs := hpre.hvs
  have hv := hpre.hv
  obtain ⟨u0, st0, u0pc, hcp, hcs, u0r, u0f⟩ := Sign.Seed.leaf_prechainFrom61S hsub sk hpre hj hu upc seed 0
    (by norm_num) h28 (Sign.SeedIndependent.codeAt_sub_61 hsub) (by simpa using hseed)
  rw [lower_sel hlay, hso] at st0
  simp only [Bool.false_eq_true, if_false, Nat.add_zero] at st0
  have hch := Sign.Seed.chainRun_tsim hsub sk hcp u0pc seed hcs
  rw [map_eq_bind_pure_comp]
  refine (TSim.steps st0 (TSim.bind (k₂ := 4 + (11 + slotK A.lay j))
    (c₂ := 4 + (11 + slotK A.lay j)) (n₂ := 0) (b₂ := 0) hch (fun r w hw => ?_))).of_eq
    (by unfold chainProg; rfl) (by omega) (by omega) (by simp) (by simp)
  obtain ⟨wpc, hwv, hwl, hwr, hwf⟩ := hw
  obtain ⟨x, stx, xpc, hx, hfx⟩ := Sign.Seed.leaf_postchainS hsub sk hpre hj hu wpc (u0r.trans hwr)
    (u0f.trans hwf) r.1 r.2 hwv hwl
  rw [hso] at stx hx
  simp only [Bool.false_eq_true, if_false] at stx hx
  refine TSim.pure_steps stx ⟨xpc, hx, ?_⟩
  have hsj := slot_ge A.lay j
  have hsj' := slot_lt A.lay hj
  have hvj : A.valp + 16 * j + 16 ≤ A.valp + 16 * A.n := by omega
  refine ((hc.frame u0f (by omega) (by omega) (by omega)).frame hwf (by omega) ?_ ?_).frame hfx (by omega)
    (by omega) (by omega)
  · unfold ChainW; omega
  · unfold ChainW; omega

def chainC : Nat := 5 + lowerSeedC + 364
/-- State before chain `j` of a lower leaf (`j = 0`: at `SEED` after the coefficient loop). -/
structure FSt (s0 : MachineState) (A : LeafArgs) (coefs : List Digest) (carry : Digest) (j : Nat)
    (st : List Digest × List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (if j = 0 then seedI else 1013 + 41)
  coef : CoefAtN 17 u coefs
  inv : ∃ s, HybOf s0 s u ∧ LeafInv s A j st u
  carry : DigAt u (SEEDS + 16) carry

theorem chain_step (hlay : A.lay ≠ 0) (hso : A.so = false) (hvS : A.valp + 16 * A.n ≤ 0x50000)
    (hdS : A.digp + A.n ≤ 0x50000) (hdestS : A.dest + 16 ≤ 0x50000) {coefs : List Digest} (hlen : coefs.length = 17)
    {carry : Digest} {j : Nat} (hj : j < 43) {st : List Digest × List Digest} {u : MachineState}
    (hu : FSt s0 A coefs carry j st u) :
    TBSim Sign.image sk u chainC (leafStepB A.lay A.tree A.leaf A.digits coefs st j)
      (FSt s0 A coefs carry (j + 1)) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 43 := lower_n hlay
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hlay0 : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨s, hs, hinv⟩ := hu.inv
  have g : ∀ r, r ∉ leafRegs → u.getReg r = s0.getReg r := fun r hr => by rw [hinv.regs.get hr, hs.regs]
  obtain ⟨v, c0, sv, hc0, vpc, vr, vf⟩ : ∃ v c0, Steps Sign.image u c0 c0 v ∧ c0 ≤ 5 ∧ v.pc = pcOf seedI ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := by
    by_cases hj0 : j = 0
    · exact ⟨u, 0, Steps.refl u, by norm_num, by rw [hu.pc, if_pos hj0], RegsExcept.refl _ _, Frame.refl _ _⟩
    · have hpc : u.pc = pcOf (1013 + 41) := by rw [hu.pc, if_neg hj0]
      obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.Seed.sub41_spec hsub u hpc j A.n (by omega) (by omega) hinv.x19
        (by rw [g _ (by simp [leafRegs]), hpre.x26])
      rw [if_pos (by omega)] at t1pc
      obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := hook_spec t1 (by rw [t1pc])
      obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := step_D1 newCodeAt_image t2 t2pc (lay := A.lay.val) (j := j)
        (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [leafRegs]), hpre.x8]) hlay0 hlay'
        (by rw [t2r.get (by simp), t1r.get (by simp)]; exact hinv.x19) hj0 (by omega)
      exact ⟨t3, _, st1.trans (st2.trans st3), by norm_num, t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
        ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)⟩
  have hv19 : v.getReg .x19 = BitVec.ofNat 64 j := by rw [vr.get (by simp)]; exact hinv.x19
  have hcv : CoefAtN 17 v coefs := fun k hk => (hu.coef k hk).frame vf (by unfold COEF; omega) (by simp) (by simp)
  obtain ⟨w, kw, cw, sw, hcw, wpc, w28, wseed, wr, wf⟩ := lower_seed newCodeAt_image v vpc hv19 hj hlen hcv
  have hs' : HybOf s0 (hyb s0 w) w := hyb_of s0 w
  have hinvw : LeafInv (hyb s0 w) A j st w := LeafInv.rebase hinv hs hs' (vr.trans wr) (by
      intro r hr
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (vf.trans wf) (fun X h => by
      rcases h with h | h
      · exact h.elim
      · unfold SeedW BScr; simp only [COEF, CHAINW, PRIV, SEEDS] at *; omega)
    hpre.hvs hvS (by omega)
  have hpre' : LeafPreS sk (hyb s0 w) A := LeafPreS.transfer hpre hs'.regs hs'.base hdS
  have hcw' : DigAt w (SEEDS + 16) carry :=
    (hu.carry.frame vf (by decide) (by simp) (by simp)).frame wf (by decide) (by decide) (by decide)
  have hcont := chain_cont sk hpre' hlay hso (j := j) (by omega) (st := st) w (WCT9.lowerFamilySeed coefs j) carry
    (by rw [wpc]) hinvw w28 wseed hcw'
  have hk : 16 + (rungK A.lay * A.e j + 10) + (4 + (11 + slotK A.lay j)) ≤
      16 + (rungC A.lay * A.e j + 10) + (4 + (11 + slotK A.lay j)) := by
    have h1 : rungK A.lay ≤ rungC A.lay := by unfold rungK rungC; omega
    have := Nat.mul_le_mul_right (A.e j) h1
    omega
  have hc364 : 16 + (rungC A.lay * A.e j + 10) + (4 + (11 + slotK A.lay j)) ≤ 364 := by
    rw [lower_e hlay hso j, lower_rungC hlay, Sign.Seed.slotK_low hlay j]
    split_ifs <;> omega
  have heq : leafStepB A.lay A.tree A.leaf A.digits coefs st j =
      (fun r : Digest × Digest => (st.1 ++ [r.2], st.2 ++ [r.1])) <$> chainProg A j (WCT9.lowerFamilySeed coefs j) := by
    simp only [leafStepB, chainProg, LeafArgs.e, LeafArgs.d, hso, Bool.false_eq_true, if_false, map_bind, map_pure]
  rw [heq]
  refine TBSim.mono (TBSim.steps (sv.trans sw) ((hcont.toTBSim hk).mono hc364 (fun st' x hx => ?_)))
    (by unfold chainC; omega) (fun _ _ h => h)
  obtain ⟨xpc, hxinv, hxc⟩ := hx
  have hxs : ∀ X, X < 2 ^ 64 → BScr X → x.getMem (BitVec.ofNat 64 X) = w.getMem (BitVec.ofNat 64 X) :=
    fun X hX hb => (hxinv.frame.get hX (fun hl => LeafW_not_bscr hvS hdestS hl hb)).trans (hs'.scr X hX hb)
  refine ⟨by rw [if_neg (by omega)]; exact xpc, fun k hk => ?_, ⟨hyb s0 w, ⟨hs'.regs, hs'.base,
    fun X hX hb => (hs'.scr X hX hb).trans (hxs X hX hb).symm⟩, hxinv⟩, hxc⟩
  have hwk : DigAt w (COEF + 16 * k) (coefs.getD k 0) :=
    (hcv k hk).frame wf (by unfold COEF; omega) (by simp only [COEF, CHAINW]; omega)
      (by simp only [COEF, CHAINW]; omega)
  exact ⟨by rw [hxs _ (by unfold COEF; omega) (by unfold BScr COEF; omega)]; exact hwk.1,
    by rw [hxs _ (by unfold COEF; omega) (by unfold BScr COEF; omega)]; exact hwk.2⟩

theorem buildLeafPF_tbsim (hlay : A.lay ≠ 0) (hso : A.so = false) (hpc : s0.pc = pcOf (1013 + 27))
    (h15 : s0.getReg .x15 = BitVec.ofNat 64 (SigGolfCandidate.T3.height A.lay))
    (hvS : A.valp + 16 * A.n ≤ 0x50000) (hdS : A.digp + A.n ≤ 0x50000) (hdestS : A.dest + 16 ≤ 0x50000)
    (carry : Digest) (hcar : A.leaf % 2 = 1 → DigAt s0 (SEEDS + 16) carry) :
    TBSim Sign.image sk s0 lowLeafC (WCT9.buildLeafPF A.lay A.tree A.leaf A.digits carry)
      (fun r t => t.pc = pcOf A.ret ∧ (A.so = false → DigAt t A.dest r.1.1) ∧ DigsAt t A.valp r.1.2 ∧
        r.1.2.length = A.n ∧ DigAt t (SEEDS + 16) r.2 ∧ RegsExcept s0 t leafRegs ∧
        Frame s0 t (fun X => LeafW A X ∨ BScr X)) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 43 := lower_n hlay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLO : LOUT = 132032 := rfl
  obtain ⟨t1, st1, t1pc, t1x3, t1x19, t1l16, t1l24, t1r, t1f⟩ :=
    Sign.Seed.sub27_spec hsub s0 hpc A.lay A.tree A.leaf (by have := hpre.hroute; omega) hpre.x8 hpre.x9 hpre.x18
      (Or.inr h15) hlay
  have h0 : LeafInv s0 A 0 ([], []) t1 := by
    refine ⟨t1x19, ?_, by rw [t1x3, hpre.x1], t1r.mono (by decide), t1f.mono (fun X _ h => ?_), t1l16,
      t1l24, by simp, rfl, fun _ c hc => absurd hc (by omega), DigsAt.nil _ _⟩
    · rw [t1r.get (by simp), hpre.x23]; simp
    · unfold LeafW; rw [if_neg hlay]; omega
  have hs1 : HybOf s0 s0 t1 := HybOf.refl_of (t1f.mono (fun X _ h => by
    rcases h with h | h <;> (subst h; unfold BScr; omega)))
  have hc1 : A.leaf % 2 = 1 → DigAt t1 (SEEDS + 16) carry := fun h =>
    (hcar h).frame t1f (by omega) (by omega) (by omega)
  rw [buildLeafPF_eq]
  refine TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 43 * chainC + 106)
    (coef_phase sk hpre hlay h0 hs1 t1pc hc1) (fun cs u hu => ?_))) (by unfold lowLeafC coefC chainC lowerSeedC hornStepC; omega)
    (fun _ _ h => h)
  obtain ⟨upc, ucoef, ulen, ucarry, ur, uf⟩ := hu
  have hinvu : LeafInv (hyb s0 u) A 0 ([], []) u := LeafInv.rebase h0 hs1 (hyb_of s0 u) ur (by
      intro r hr
      simp only [coefRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    uf (fun X h => by
      unfold CoefW at h; unfold SeedW BScr
      rcases h with h | h | h | h
      · left; unfold COEF at h; omega
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h)
    hpre.hvs hvS (by omega)
  have hF0 : FSt s0 A cs.1 cs.2 0 ([], []) u := ⟨by rw [if_pos rfl]; exact upc, ucoef, ⟨_, hyb_of s0 u, hinvu⟩, ucarry⟩
  have hfold := TBSim.foldlM_range' (image := Sign.image) (sk := sk) 0 43
    (leafStepB A.lay A.tree A.leaf A.digits cs.1) ([], []) (FSt s0 A cs.1 cs.2) chainC
    (fun j hj st x hx => by simpa using chain_step sk hpre hlay hso hvS hdS hdestS ulen hj hx) hF0
  rw [show List.range' 0 43 = List.range (chainCount A.lay) by rw [lower_n hlay]; exact List.range_eq_range'.symm]
    at hfold
  refine TBSim.bind (W₁ := 43 * chainC) (W₂ := 106) hfold (fun rows x hx => ?_)
  obtain ⟨xpc, -, ⟨s3, hs3, hinv3⟩, xcarry⟩ := hx
  have hpre3 := LeafPreS.transfer hpre hs3.regs hs3.base hdS
  rw [show (43 : Nat) = A.n from hn.symm] at hinv3
  have hex := Sign.Seed.leaf_exitS hsub sk hpre3 hinv3 (by rw [xpc, if_neg (by omega)])
  simp only [hso, Bool.false_eq_true, if_false] at hex
  have hds := hpre.hds
  refine TBSim.of_eq' (TBSim.bind (W₂ := 0) (f := fun r => pure ((r.1, r.2), cs.2))
    (hex.toTBSim (by rw [lower_blocks hlay]; norm_num)) (fun r y hy => TBSim.pure ?_)) (by simp only [bind_assoc, pure_bind])
    (by rw [lower_blocks hlay])
  obtain ⟨ypc, ydest, yvals, ylen, -, yregs, yframe, yf⟩ := hy
  refine ⟨ypc, fun _ => ydest trivial, yvals, ylen, xcarry.frame yf (by omega) (by omega) (by omega),
    fun r hr => by rw [yregs.get hr, hs3.regs], fun X hX hn' => ?_⟩
  rw [yframe.get hX (fun h => hn' (Or.inl h)), hs3.base.get hX (fun h => hn' (Or.inr h))]

end chain

theorem packedLeafSpecV : SigGolfCandidate.T3M.Sign.Packed.PackedLeafSpec WCT9.buildLeafPF := by
  intro sk A s carry hlay hso hpre hpc h15 hv hd hdest hcar
  exact buildLeafPF_tbsim sk hpre hlay hso hpc h15 hv hd hdest carry hcar
end ClaudeWCT.W9.Machine.Sign.PackedLeaf
