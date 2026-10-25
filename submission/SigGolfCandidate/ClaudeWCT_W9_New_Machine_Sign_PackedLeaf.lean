import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_LowerRuns
import SigGolfCandidate.T3M_Sign_SeedLeafPhases
import SigGolfCandidate.T3M_Sign_PackedLowTree
-- serialization only (no declarations used): keeps this ~14 GB module from building in parallel with the other heavy ones under the verifier's 2-job / 24 GiB limit
import SigGolfCandidate.ClaudeWCT_Numerics_N600Price

/-!
# Stage B (campaign X1): the lower leaf of the sign image refines `WCT9.buildLeafPF`

Chain 0 of a lower leaf runs the coefficient loop (`coef_phase`: the 8 packed halves with ordinals
`8 L .. 8 L + 7` of `lowerSeedPair lay tree` into `COEF`, carry at `SEEDS + 16`); every chain `j` then evaluates
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

-- Campaign T51 (as R6): the legacy `newCodeAt_image : NewCodeAt Sign.image` over the reference image (and its
-- `signCode_drop_new` / `arena_signImage`) was removed: dead, and false once `tailCode` reads the current image.

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
      hsl := h.hsl
      hdig := fun i hi => by
        rw [hf.getByte (by omega) (not_bscr (by omega))]; exact h.hdig i hi
      hdigb := h.hdigb
      hdigp := h.hdigp
      hdigW := h.hdigW
      hdigC := h.hdigC
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
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
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
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
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

def coefRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x17, .x28, .x29, .x30]
/-- Writes of the v6 family prologue: the family buffer (with its end pointer) and the query cells. -/
def CoefW (X : Nat) : Prop :=
  (SharedSeed.FB ≤ X ∧ X < SharedSeed.FEND + 8) ∨ X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)
/-- State of the v6 pair loop (family `f` of layer `lay`, size `N`) after `j` pairs: the machine is at the head of
the iteration querying pair `19 f + j`, or at `SEED` once all `⌈N/2⌉` pairs are in `FB`. -/
structure CoefSt (t : MachineState) (lay f N j : Nat) (acc : List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (if j < (N + 1) / 2 then cqI else seedI)
  x29 : u.getReg .x29 = BitVec.ofNat 64 (SharedSeed.FB + 32 * j)
  x6 : u.getReg .x6 = BitVec.ofNat 64 (hdrB lay (19 * f + j))
  x17 : u.getReg .x17 = BitVec.ofNat 64 (2 ^ 32)
  x30 : u.getReg .x30 = BitVec.ofNat 64 (SharedSeed.FB + 32 * ((N + 1) / 2))
  regs : RegsExcept t u coefRegs
  frame : Frame t u CoefW
  len : acc.length = 2 * j
  coefs : ∀ i < 2 * j, DigAt u (SharedSeed.FB + 16 * i) (acc.getD i 0)
  fend : u.getMem (BitVec.ofNat 64 SharedSeed.FEND) = BitVec.ofNat 64 (SharedSeed.FB + 16 * N)

/-- Cycle bound of the chain-0 coefficient phase (sub41, hook, `20746..20749`, `qd` ≤ 47 cycles, ≤ 19 pairs). -/
def coefC : Nat := 1 + 1 + 3 + 47 + 19 * 26

theorem getD_append_last {l : List Digest} {d : Digest} {i : Nat} (hl : l.length = i) :
    (l ++ [d]).getD i 0 = d := by
  rw [List.getD_eq_getElem _ _ (by simp [hl]), List.getElem_append_right (by omega)]; simp [hl]
theorem getD_append_lt {l : List Digest} {d : Digest} {i : Nat} (hi : i < l.length) :
    (l ++ [d]).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]
theorem getD_take_lt {l : List Digest} {n k : Nat} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem pow_height_low {lay : Layer} (h : lay ≠ 0) :
    2 ^ SigGolfCandidate.T3.height lay = if lay.val = 1 then 128 else 64 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide
theorem famSize_low {lay : Layer} (h : lay ≠ 0) (L : Nat) :
    WCT9.famSize lay (L / 7) = SharedSeed.famN lay.val L := by
  unfold WCT9.famSize SharedSeed.famN
  rw [if_neg h, pow_height_low h]
theorem famGrp_low {lay : Layer} (h : lay ≠ 0) : WCT9.famGrp lay = 7 := by
  unfold WCT9.famGrp; rw [if_neg h]
theorem famBase_low {lay : Layer} (h : lay ≠ 0) : WCT9.famBase lay = 38 := by
  unfold WCT9.famBase; rw [if_neg h]
/-- The v6 lower family seed of chain `j < 43` is the family at `(leaf % 7) · 43 + j + 1`. -/
theorem lowerFamilySeed_eq {lay : Layer} (h : lay ≠ 0) (coefs : List Digest) (leaf : Nat) {j : Nat} (hj : j < 43) :
    WCT9.lowerFamilySeed coefs lay leaf j = familyEval coefs (leaf % 7 * 43 + j + 1) := by
  unfold WCT9.lowerFamilySeed WCT9.famPoint
  rw [if_pos (Or.inr (by rw [lower_n h]; exact hj)), famGrp_low h]
  unfold WCT9.famStride; rw [if_neg h]

section coef
variable (sk : BitVec 256) {s0 s t : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre


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

section chain
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre

/-! Pairing stage 1: the legacy reference-image lower-leaf run (`chain_cont`, `chain_step`, `buildLeafPF_tbsim`,
`packedLeafSpecV`, over `Sign.image`) was removed: it is not on the `SignLink` route (the installed producer is proved
by `SharedLeafMemory.buildLeafPrefixes_precise`), and its `LeafInv` frames cannot absorb the G chains' scratch. -/
end chain
end ClaudeWCT.W9.Machine.Sign.PackedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN LEAFPK LOUT LeafArgs LeafW leafRegs LeafInv ChainW chainRegs
  chainProg rungK rungC leafBlocks slot slotK slot_ge slot_lt chainCount_cases)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.Packed (lowLeafC)
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit privatePair header privateInput)
open ClaudeWCT.Arith
set_option maxRecDepth 10000


/-- The leaf scratch (the widened `LeafW` now covers the whole G-chain scratch `CHAIN+32 .. CHAIN+112`). -/
def BScr (X : Nat) : Prop :=
  (0x50000 ≤ X ∧ X < 0x75580)
instance : DecidablePred BScr := fun X => by unfold BScr; infer_instance
/-- `s0` with the scratch region `BScr` of `t`. -/
def hyb (s0 t : MachineState) : MachineState :=
  { s0 with mem := fun a => if BScr a.toNat then t.mem a else s0.mem a }
/-- `s` is a base state for `t` relative to the leaf entry `s0`: registers of `s0`, memory of `s0` outside the
scratch, memory of `t` on the scratch. -/
structure HybOf (s0 s t : MachineState) : Prop where
  regs : ∀ r, s.getReg r = s0.getReg r
  base : Frame s0 s BScr
  scr : ∀ A, A < 2 ^ 64 → BScr A → s.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A)
theorem hyb_of (s0 t : MachineState) : HybOf s0 (hyb s0 t) t := by
  refine ⟨fun r => rfl, fun A hA hn => ?_, fun A hA h => ?_⟩
  · show (if BScr (BitVec.ofNat 64 A).toNat then t.mem _ else s0.mem _) = s0.mem _
    rw [toNat_ofNat_lt hA, if_neg hn]
  · show (if BScr (BitVec.ofNat 64 A).toNat then t.mem _ else s0.mem _) = t.mem _
    rw [toNat_ofNat_lt hA, if_pos h]
theorem HybOf.frame {s0 s t u : MachineState} {W : Nat → Prop} (h : HybOf s0 s t) (hf : Frame t u W)
    (hW : ∀ A, W A → ¬ BScr A) : HybOf s0 s u :=
  ⟨h.regs, h.base, fun A hA hb => (h.scr A hA hb).trans (hf.get hA (fun hw => hW A hw hb)).symm⟩
theorem HybOf.refl_of {s0 t : MachineState} (hf : Frame s0 t (fun A => ¬ BScr A)) : HybOf s0 s0 t :=
  ⟨fun _ => rfl, Frame.refl _ _, fun A hA hb => (hf.get hA (fun h => h hb)).symm⟩

theorem not_bscr {X : Nat} (h : X < 0x201C0 ∨ (0x201D0 ≤ X ∧ X < 0x201F0) ∨ (0x20210 ≤ X ∧ X < 0x50000)) :
    ¬ BScr X := fun hb => by unfold BScr at hb; omega

theorem LeafPreS.transfer {sk : BitVec 256} {s0 s : MachineState} {A : LeafArgs} (h : LeafPreS sk s0 A)
    (hr : ∀ r, s.getReg r = s0.getReg r) (hf : Frame s0 s BScr) (hd : A.digp + A.n ≤ 0x50000) :
    LeafPreS sk s A := by
  have g : ∀ X, X < 0x201C0 → s.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) :=
    fun X hX => hf.get (by omega) (not_bscr (Or.inl hX))
  have hdc := h.hdigC
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
      hsl := h.hsl
      hdig := fun i hi => by
        rw [hf.getByte (by omega) (not_bscr (by omega))]; exact h.hdig i hi
      hdigb := h.hdigb
      hdigp := h.hdigp
      hdigW := h.hdigW
      hdigC := h.hdigC
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
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have nW : ∀ X, (X < 0x201C0 ∨ (0x20210 ≤ X ∧ X < 0x50000)) →
      ¬ (X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32)) → ¬ W X := by
    intro X h1 h2 hw
    rcases hW X hw with h | h
    · exact not_bscr (by omega) h
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

theorem LeafW_not_bscr {A : LeafArgs} (hv : A.valp + 16 * A.n ≤ 0x50000) (hd : A.dest + 16 ≤ 0x50000)
    (hdc : A.dest + 16 ≤ 0x201C0 ∨ 0x20210 ≤ A.dest) (hvc : A.valp + 16 * A.n ≤ 0x201C0 ∨ 0x20210 ≤ A.valp) {X : Nat}
    (h : LeafW A X) : ¬ BScr X := by
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
  unfold LeafW at h
  intro hb; unfold BScr at hb
  simp only [PRIV, SEEDS, CHAIN, LEAFPK, LOUT] at h
  split_ifs at h <;> omega


end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000

/-- Rebase after the prefix-retaining chain. Only the current reveal slot and
chain scratch are low writes; earlier endpoints and reveals are preserved. -/
theorem LeafInv.rebase_chain {s0 s t s' u : MachineState} {A : LeafArgs} {j : Nat}
    {st : List Digest × List Digest} (ht : LeafInv s A j st t)
    (hs : HybOf s0 s t) (hs' : HybOf s0 s' u) {R : List Reg}
    (hr : RegsExcept t u R) (hR : ∀ r ∈ R, r ∈ leafRegs ∧ r ≠ .x19 ∧ r ≠ .x23 ∧ r ≠ .x3)
    {W : Nat → Prop} (hf : Frame t u W)
    (hW : ∀ X, W X → BScr X ∨ ChainW (A.valp + 16*j) X)
    (hvs : A.valp + 16*A.n ≤ PRIV ∨ LEAFPK+960 ≤ A.valp)
    (hv : A.valp + 16*A.n ≤ 0x50000) (hj : j < A.n) :
    LeafInv s' A j st u := by
  have hn : A.n=51 ∨ A.n=43 := chainCount_cases A.lay
  have nW : ∀ X, (X<0x201C0 ∨ (0x20210≤X ∧ X<0x50000)) → ¬ChainW (A.valp+16*j) X → ¬W X := by
    intro X hX hC h
    exact (hW X h).elim (not_bscr (by omega)) hC
  have gr : ∀ r, r=.x19 ∨ r=.x23 ∨ r=.x3 → u.getReg r=t.getReg r := by
    intro r h
    apply hr.get
    intro hm
    obtain ⟨_,h1,h2,h3⟩ := hR r hm
    rcases h with rfl|rfl|rfl <;> simp_all
  have hlv : ∀ X, LEAFPK≤X → X<LEAFPK+16*(A.n+2) → ¬W X := by
    intro X h1 h2
    apply nW X
    · simp only [LEAFPK] at *; omega
    · simp only [ChainW,CHAIN,LEAFPK,PRIV] at *; omega
  refine ⟨by rw [gr _ (by simp)]; exact ht.x19,
    by rw [gr _ (by simp)]; exact ht.x23,
    by rw [gr _ (by simp)]; exact ht.x3,?_,?_,?_,?_,ht.elen,ht.vlen,?_,?_⟩
  · intro r hr'
    rw [hr.get (fun h => hr' (hR r h).1),ht.regs.get hr',hs.regs,hs'.regs]
  · intro X hX hn'
    by_cases hb : BScr X
    · rw [hs'.scr X hX hb]
    · have hnw : ¬W X := fun hw => (hW X hw).elim hb (fun h => hn' (LeafW_of_chainW hj h))
      rw [hf.get hX hnw,ht.frame.get hX hn',hs.base.get hX hb,hs'.base.get hX hb]
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh16
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh24
  · intro hso c hc
    have h1 := slot_ge A.lay c
    have h2 := slot_lt A.lay (show c<A.n by omega)
    exact (ht.ends hso c hc).frame hf (by simp only [LEAFPK] at *; omega) (hlv _ (by omega) (by omega))
      (hlv _ (by omega) (by omega))
  · exact ht.vals.frame hf (by rw [ht.vlen]; omega) (by
      intro X h1 h2
      rw [ht.vlen] at h2
      apply nW X (by simp only [PRIV,LEAFPK] at *; omega)
      simp only [ChainW,CHAIN,PRIV,LEAFPK] at *
      omega)

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
theorem chain_cont {im : Image}
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
            (SharedPrefixes.buffer A.lay.val j 0≤X ∧ X<SharedPrefixes.buffer A.lay.val j 7+16) ∨
            (slot A.lay j≤X ∧ X<slot A.lay j+16)) ∧
          (SharedPrefixes.selectionWord (t.getMem 0x20550) A.lay.val=t.getReg .x18 →
            ∀ k, k≤7 → DigAt w (SharedPrefixes.buffer A.lay.val j k) (vs.getD k 0)) ∧
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
  have run := SharedChain.retained_chain hc hpref sk u upc A.lay A.tree A.leaf j 7 (A.d j)
    (A.valp+16*j) (1013+79) seed upre hl (by omega) (by decide) (by omega)
    (by omega) uval
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
      change (X=CHAIN+48 ∨ X=CHAIN+56) ∨ SharedChain.loopWrites A.lay.val j 0 7 (A.valp+16*j) X at h
      rcases h with h|h
      · right; simp only [ChainW,CHAIN] at *; omega
      · change Sign.Seed.ChainWS (A.valp+16*j) X ∨
          (SharedPrefixes.buffer A.lay.val j 0≤X ∧ X<SharedPrefixes.buffer A.lay.val j 7+16) at h
        rcases h with h|h
        · unfold Sign.Seed.ChainWS at h; unfold BScr ChainW; simp only [CHAIN] at *; omega
        · left
          have hb0 := SharedPrefixes.buffer_bounds hl (by omega) (by omega : j<43) (by decide : 0<8)
          have hb7 := SharedPrefixes.buffer_bounds hl (by omega) (by omega : j<43) (by decide : 7<8)
          unfold BScr
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
  refine ⟨ht'.1,wpc,hyb s0 v,st.2++[Sign.Packed.memDig v (A.valp+16*j)],?_,winv,?_,?_,?_,?_⟩
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
      change ((X=CHAIN+48 ∨ X=CHAIN+56) ∨ SharedChain.loopWrites A.lay.val j 0 7 (A.valp+16*j) X) ∨ _ at h
      simp only [SharedChain.loopWrites,Sign.Seed.ChainWS,ChainW] at *
      omega)
  · intro selected k hk
    have uselected : SharedPrefixes.selectionWord (u.getMem 0x20550) A.lay.val=u.getReg .x18 := by
      have idx := uf 0x20550 (by decide) (by simp only [CHAIN]; omega)
      exact (congrArg (fun x => SharedPrefixes.selectionWord x A.lay.val) idx).trans
        (selected.trans (ur.get (by decide)).symm)
    have saved := ht'.2.2.2.2.2.1 uselected k hk
    have hb := SharedPrefixes.buffer_bounds hl (by omega) (by omega : j<43) (by omega : k<8)
    have h1 := slot_ge A.lay j
    have h2 := slot_lt A.lay hj
    exact saved.frame wf (by omega) (by simp only [LEAFPK] at *; omega)
      (by simp only [LEAFPK] at *; omega)
  · intro hj2
    have h1 := slot_ge A.lay j
    exact (ht'.2.2.2.2.2.2 (fun h => by omega) (by decide)).frame wf (by simp only [CHAIN,LEAFPK] at *; omega)
      (by simp only [CHAIN,LEAFPK] at *; omega)

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open OracleComp SigGolfCandidate.T3
set_option maxHeartbeats 1000000

theorem foldlM_append_eq {α β : Type} (f : α → M β) (xs : List α) (acc : List β) :
    xs.foldlM (fun acc x => do let y ← f x; pure (acc++[y])) acc =
      (do let ys ← xs.mapM f; pure (acc++ys)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons,List.mapM_cons,bind_assoc,pure_bind,ih]
      apply bind_congr
      intro y
      apply bind_congr
      intro ys
      simp only [List.append_assoc,List.singleton_append]

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

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
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, SigGolfCandidate.T3M.readWords_eight, fr PRIV (by simp),
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
    (by rw [pc_writeHash, u1pc, SigGolfCandidate.T3M.pcOf_add4]) (P := SharedSeed.FB + 32 * j)
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

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest M)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem chain_step_precise {im : Image} (hsub : Sign.SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Sign.Seed.sub61)
    (hc : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hnew : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode)
    (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
    (hlay : A.lay≠0) (hso : A.so=false) (hvS : A.valp+16*A.n≤0x50000)
    (hdS : A.digp+A.n≤0x50000) (hdestS : A.dest+16≤0x50000)
    (hvi : A.valp+16*A.n≤0x20550 ∨ 0x20558≤A.valp)
    {coefs : List Digest}
    {j : Nat} (hj : j<43) {prefixes : List (List Digest)} {u : MachineState}
    (hu0 : PSt s0 A coefs j prefixes u ∧ Frame s0 u (Writes A s0)) :
    TBSim im sk u chainC (prefixStep A coefs prefixes j) (fun ps x => PSt s0 A coefs (j+1) ps x ∧ Frame s0 x (Writes A s0)) := by
  obtain ⟨hu,huf⟩ := hu0
  have hcost : SharedSeed.lowerSeedC=lowerSeedC := rfl
  have plen := hu.len
  have hl := A.lay.isLt
  have hn : A.n = 43 := lower_n hlay
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hlay0 : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨s, values, hs, hinv⟩ := hu.inv
  have g : ∀ r, r ∉ leafRegs → u.getReg r = s0.getReg r := fun r hr => by rw [hinv.regs.get hr, hs.regs]
  obtain ⟨v, c0, sv, hc0, vpc, vr, vf⟩ : ∃ v c0, Steps im u c0 c0 v ∧ c0 ≤ 5 ∧ v.pc = pcOf seedI ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := by
    by_cases hj0 : j = 0
    · exact ⟨u, 0, Steps.refl u, by norm_num, by rw [hu.pc, if_pos hj0], RegsExcept.refl _ _, Frame.refl _ _⟩
    · have hpc : u.pc = pcOf (1013 + 41) := by rw [hu.pc, if_neg hj0]
      obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.SharedLeaf.sub41_spec hsub u hpc j A.n (by omega) (by omega) hinv.x19
        (by rw [g _ (by simp [leafRegs]), hpre.x26])
      rw [if_pos (by omega)] at t1pc
      obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := hook_spec hhook t1 (by rw [t1pc])
      obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := SharedSeed.step_D1 hnew t2 t2pc (lay := A.lay.val) (j := j)
        (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [leafRegs]), hpre.x8]) hlay0 hlay'
        (by rw [t2r.get (by simp), t1r.get (by simp)]; exact hinv.x19) hj0 (by omega)
      exact ⟨t3, _, st1.trans (st2.trans st3), by norm_num, t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
        ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)⟩
  have hv19 : v.getReg .x19 = BitVec.ofNat 64 j := by rw [vr.get (by simp)]; exact hinv.x19
  have hv18 : v.getReg .x18 = BitVec.ofNat 64 A.leaf := by
    rw [vr.get (by simp), g _ (by simp [leafRegs]), hpre.x18]
  have hcv : SharedSeed.FamBuf v coefs := hu.coef.frame vf (fun _ _ _ h => h)
  obtain ⟨w, kw, cw, sw, hcw, wpc, w28, wseed, wr, wf⟩ :=
    SharedSeed.lower_seed hnew v vpc hv18 (by have := hpre.hleaf; omega) hv19 hj hcv
  rw [← PackedLeaf.lowerFamilySeed_eq hlay coefs A.leaf hj] at wseed
  have hs' : HybOf s0 (hyb s0 w) w := hyb_of s0 w
  have hinvw : LeafInv (hyb s0 w) A j (ends prefixes,values) w := LeafInv.rebase hinv hs hs' (vr.trans wr) (by
      intro r hr
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (vf.trans wf) (fun X h => by
      rcases h with h | h
      · exact h.elim
      · unfold SeedW BScr; simp only [COEF, CHAINW, PRIV, SEEDS] at *; omega)
    hpre.hvs hvS (by omega)
  have hpre' : LeafPreS sk (hyb s0 w) A := LeafPreS.transfer hpre hs'.regs hs'.base hdS
  have hcw' : DigAt w (SEEDS + 16) (Sign.Packed.memDig w (SEEDS + 16)) := Sign.Packed.memDig_digAt _ _
  have hcont := chain_cont_guarded hsub hcopy hc hpref sk hpre hlay hso hvS hdS hvi (by omega)
    w (WCT9.lowerFamilySeed coefs A.lay A.leaf j) _ (by rw [wpc]) hinvw hs' w28 wseed hcw'
  unfold prefixStep
  refine (TBSim.steps (sv.trans sw) (TBSim.bind (W₂:=0) hcont (fun vs x hx => TBSim.pure ?_))).mono
    (by unfold chainC; omega) (fun _ _ h => h)
  obtain ⟨vlen,xpc,base,vals,hsx,hinvx,-,xf,xsaved,xz⟩ := hx
  have hxcoef : SharedSeed.FamBuf x coefs := by
    have hslot := slot_lt A.lay (by omega : j<A.n)
    refine (hcv.frame wf ?_).frame xf ?_
    · intro X h1 h2 h; simp only [SharedSeed.FB, SharedSeed.FEND, COEF, CHAINW] at *; omega
    · intro X h1 h2 h
      simp only [SharedSeed.FB, SharedSeed.FEND, COEF, Sign.Seed.ChainWS, CHAIN, SharedPrefixes.buffer, LEAFPK] at *
      omega
  have hprecise : Frame s0 x (Writes A s0) := by
    apply ((huf.trans vf).trans (wf.trans xf)).mono
    intro X hX h
    rcases h with (h|h)|(h|h)
    · exact h
    · exact h.elim
    · left
      simp only [COEF,CHAINW] at h
      omega
    · rcases h with h|h|h
      · left; simp only [Sign.Seed.ChainWS,CHAIN] at h; omega
      · right
        refine ⟨h.1,?_,?_⟩ <;> simp only [SharedPrefixes.buffer] at * <;> omega
      · left
        have hs := slot_lt A.lay (by omega : j<A.n)
        simp only [LEAFPK] at hs
        omega
  refine ⟨?_,hprecise⟩
  refine ⟨by rw [if_neg (by omega)]; exact xpc,hxcoef,
    ⟨base,vals,hsx,by simpa only [ends,List.map_append,List.map_singleton] using hinvx⟩,
    by simp only [List.length_append,List.length_singleton,hu.len],?_,fun hj2 => xz (by omega)⟩
  intro hsel i hi k hk
  by_cases hij : i=j
  · subst i
    have hws : SharedPrefixes.selectionWord (w.getMem 0x20550) A.lay.val=w.getReg .x18 :=
      LeafInv.selected hpre hvi hinvw hs' hsel
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : prefixes.length≤j),
      hu.len,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] using xsaved hws k hk
  · have hij' : i<j := by omega
    have hi43 : i<43 := by omega
    have hb := SharedPrefixes.buffer_bounds (lay := A.lay.val) (by
      have hz : A.lay.val≠0 := fun h => hlay (Fin.ext h); omega)
      (by omega) hi43 (by omega : k<8)
    have saved := hu.saved hsel i hij' k hk
    have vSaved := saved.frame vf (by omega) (by simp) (by simp)
    have wSaved := vSaved.frame wf (by omega)
      (by simp only [COEF,CHAINW]; omega) (by simp only [COEF,CHAINW]; omega)
    have hslot := slot_lt A.lay (by omega : j<A.n)
    have xSaved := wSaved.frame xf (by omega)
      (by simp only [Sign.Seed.ChainWS,CHAIN,SharedPrefixes.buffer,LEAFPK] at *; omega)
      (by simp only [Sign.Seed.ChainWS,CHAIN,SharedPrefixes.buffer,LEAFPK] at *; omega)
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : i<prefixes.length)] using xSaved

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

theorem buildLeafPrefixes_precise {im : Image} (hsub : Sign.SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Sign.Seed.sub61)
    (hc : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hnew : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode)
    (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
    (hlay : A.lay ≠ 0) (hso : A.so = false) (hpc : s0.pc = pcOf (1013+27))
    (h15 : s0.getReg .x15 = BitVec.ofNat 64 (SigGolfCandidate.T3.height A.lay))
    (hvS : A.valp+16*A.n≤0x50000) (hdS : A.digp+A.n≤0x50000) (hdestS : A.dest+16≤0x50000)
    (hvi : A.valp+16*A.n≤0x20550 ∨ 0x20558≤A.valp)
    (carry : List Digest) (hcar : A.leaf % 7 ≠ 0 → SharedSeed.FamBuf s0 carry) :
    TBSim im sk s0 lowLeafC (buildLeafPrefixes A.lay A.tree A.leaf carry)
      (fun r t => t.pc=pcOf A.ret ∧ DigAt t A.dest r.1.1 ∧ r.1.2.length=43 ∧
        SharedSeed.FamBuf t r.2 ∧ RegsExcept s0 t leafRegs ∧
        Frame s0 t (fun X => LeafW A X ∨ BScr X) ∧
        Frame s0 t (Writes A s0) ∧
        (Selected A s0 → ∀ i, i<43 → ∀ k, k≤7 →
          DigAt t (SharedPrefixes.buffer A.lay.val i k) ((r.1.2.getD i []).getD k 0)) ∧
        Sign.Seed.Z32 t) := by
  have hn : A.n = 43 := lower_n hlay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLO : LOUT = 132032 := rfl
  obtain ⟨t1, st1, t1pc, t1x3, t1x19, t1l16, t1l24, t1r, t1f⟩ :=
    Sign.SharedLeaf.sub27_spec hsub s0 hpc A.lay A.tree A.leaf (by have := hpre.hroute; omega) hpre.x8 hpre.x9 hpre.x18
      (Or.inr h15) hlay
  have h0 : LeafInv s0 A 0 ([], []) t1 := by
    refine ⟨t1x19, ?_, by rw [t1x3, hpre.x1], t1r.mono (by decide), t1f.mono (fun X _ h => ?_), t1l16,
      t1l24, by simp, rfl, fun _ c hc => absurd hc (by omega), DigsAt.nil _ _⟩
    · rw [t1r.get (by simp), hpre.x23]; simp
    · unfold LeafW; rw [if_neg hlay]; omega
  have hs1 : HybOf s0 s0 t1 := HybOf.refl_of (t1f.mono (fun X _ h => by
    rcases h with h | h <;> (subst h; unfold BScr; omega)))
  have hc1 : A.leaf % 7 ≠ 0 → SharedSeed.FamBuf t1 carry := fun h =>
    (hcar h).frame t1f (fun X h1 h2 hx => by
      simp only [SharedSeed.FB, SharedSeed.FEND, COEF] at h1 h2; omega)
  unfold SigGolfCandidate.Research.SharedForest.buildLeafPrefixes
  refine TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 43 * chainC + 112)
    (coef_phase hsub hnew hhook sk hpre hlay h0 hs1 t1pc hc1) (fun cs u hu => ?_))) (by unfold lowLeafC coefC chainC lowerSeedC hornStepC; omega)
    (fun _ _ h => h)
  obtain ⟨upc, ucoef, ucarry, ur, uf⟩ := hu
  have hinvu : LeafInv (hyb s0 u) A 0 ([], []) u := LeafInv.rebase h0 hs1 (hyb_of s0 u) ur (by
      intro r hr
      simp only [PackedLeaf.coefRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    uf (fun X h => by
      unfold CoefW at h; unfold SeedW BScr
      rcases h with h | h | h | h
      · left; simp only [SharedSeed.FB, SharedSeed.FEND, COEF] at h; omega
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h)
    hpre.hvs hvS (by omega)
  have hF00 : PSt s0 A cs.1 0 [] u :=
    ⟨by rw [if_pos rfl]; exact upc,ucoef,⟨_,[],hyb_of s0 u,hinvu⟩,rfl,by intros; omega,
      fun h => absurd h (by decide)⟩
  have hF0 : PSt s0 A cs.1 0 [] u ∧ Frame s0 u (Writes A s0) := by
    refine ⟨hF00,(t1f.trans uf).mono ?_⟩
    intro X hX h
    left
    simp only [CoefW,SharedSeed.FB,SharedSeed.FEND,COEF,PRIV,SEEDS,LEAFPK] at h
    omega
  have hfold := TBSim.foldlM_range' (image:=im) (sk:=sk) 0 43
    (prefixStep A cs.1) [] (fun j ps x => PSt s0 A cs.1 j ps x ∧ Frame s0 x (Writes A s0)) chainC
    (fun j hj st x hx => by
      simpa using (chain_step_precise hsub hcopy hc hpref hnew hhook sk hpre
        hlay hso hvS hdS hdestS hvi hj hx)) hF0
  rw [show List.range' 0 43 = List.range (chainCount A.lay) by rw [lower_n hlay]; exact List.range_eq_range'.symm]
    at hfold
  have heq : (List.range (chainCount A.lay)).foldlM (prefixStep A cs.1) [] =
      (List.range (chainCount A.lay)).mapM (fun i => chainPrefixes A.lay A.tree A.leaf i 0
        (maxDigit A.lay i) (WCT9.lowerFamilySeed cs.1 A.lay A.leaf i)) := by
    unfold prefixStep
    rw [foldlM_append_eq]
    simp only [List.nil_append,bind_pure]
    apply congrArg (fun f => (List.range (chainCount A.lay)).mapM f)
    funext i
    have hm : maxDigit A.lay i=7 := by unfold maxDigit; rw [if_neg hlay]
    rw [hm]
  rw [heq] at hfold
  refine TBSim.bind (W₁:=43*chainC) (W₂:=112) hfold (fun rows x hx => ?_)
  obtain ⟨⟨xpc,xcoef,⟨s3,values,hs3,hinv3⟩,xlen,xsaved,xz⟩,xprecise⟩ := hx
  have hpre3 := LeafPreS.transfer hpre hs3.regs hs3.base hdS
  rw [show (43 : Nat)=A.n from hn.symm] at hinv3
  have hex := Sign.SharedLeaf.leaf_exitS hsub sk hpre3 hinv3 (by rw [xpc,if_neg (by omega)])
  simp only [hso,Bool.false_eq_true,if_false] at hex
  have hds := hpre.hds
  rw [prefixEnds_eq A.lay hlay rows xlen]
  refine Sign.TBSim.of_eq' (TBSim.bind (W₂:=0) (f:=fun r => pure ((r.1,rows),cs.2))
    (hex.toTBSim (by rw [lower_blocks hlay]; norm_num)) (fun r y hy => TBSim.pure ?_))
    (by simp only [bind_assoc,pure_bind]) (by rw [lower_blocks hlay])
  obtain ⟨ypc,ydest,_,_,_,yregs,yframe,yf⟩ := hy
  refine ⟨ypc,ydest trivial,xlen,by
      rw [ucarry]
      exact xcoef.frame yf (fun X h1 h2 hx => by simp only [SharedSeed.FB, SharedSeed.FEND, COEF, LOUT] at *; omega),
    fun r hr => by rw [yregs.get hr,hs3.regs],?_,?_,?_,?_⟩
  · intro X hX hn'
    rw [yframe.get hX (fun h => hn' (Or.inl h)),hs3.base.get hX (fun h => hn' (Or.inr h))]
  · exact (xprecise.trans yf).mono (by
      intro X hX h
      rcases h with h|h
      · exact h
      · left; simp only [LOUT] at h; omega)
  · intro hsel i hi k hk
    have hlay1 : 1≤A.lay.val := by have hz : A.lay.val≠0 := fun h => hlay (Fin.ext h); omega
    have hb := SharedPrefixes.buffer_bounds (lay:=A.lay.val) hlay1 (by have := A.lay.isLt; omega) hi (by omega : k<8)
    exact (xsaved hsel i hi k hk).frame yf (by omega) (by unfold LOUT; omega) (by unfold LOUT; omega)
  · exact (xz (by decide)).frame yf (by unfold LOUT; omega) (by unfold LOUT; omega)

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
/-- Pairing stage 1: `Base.frame` when the only base cells in the write set are the F pads `CHAIN+32/40`, which are
zero again at the end (`Z32`). -/
theorem Base.frame_z32 {cfFlag : Nat} {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : Base (cfFlag := cfFlag) sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l)
    (h5 : .x5 ∉ l) (hW : ∀ A, A < 2 ^ 64 → BaseA A → W A → A = CHAIN + 32 ∨ A = CHAIN + 40) (hz : Z32 u) :
    Base (cfFlag := cfFlag) sk cache u := by
  have hf' : Frame t u (fun A => W A ∧ A ≠ CHAIN + 32 ∧ A ≠ CHAIN + 40) := by
    intro A hA hn
    by_cases h32 : A = CHAIN + 32
    · subst h32; rw [hz.1, h.zero _ (by decide) (by unfold NeverW; simp)]
    by_cases h40 : A = CHAIN + 40
    · subst h40; rw [hz.2, h.zero _ (by decide) (by unfold NeverW; simp)]
    exact hf A hA (fun hw => hn ⟨hw, h32, h40⟩)
  exact h.frame hf' hr h5 (fun A hA hb hw => by
    rcases hW A hA hb hw.1 with h' | h'
    · exact hw.2.1 h'
    · exact hw.2.2 h')
end SigGolfCandidate.T3M.Sign.Seed

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- The lower tree loop invariant (v6: for a leaf inside a family the coefficients sit in `FB`, `FamBuf`). -/
structure Inv (s1 : MachineState) (lay : Layer) (sb sel l : Nat)
    (st : List Digest × List (List Digest) × List Digest) (t : MachineState) : Prop where
  pc : t.pc=pcOf 1175
  x13 : t.getReg .x13=BitVec.ofNat 64 l
  regs : RegsExcept s1 t btRegs
  frame : Frame s1 t (BtW sb (height lay))
  precise : Frame s1 t (TreeWrites lay)
  len : st.1.length=l
  roots : DigsAt t (LOW+16*2^height lay) st.1
  saved : sel<l → st.2.1.length=43 ∧ ∀ i, i<43 → ∀ k,k≤7 →
    DigAt t (SharedPrefixes.buffer lay.val i k) ((st.2.1.getD i []).getD k 0)
  carry : l % 7 ≠ 0 → SharedSeed.FamBuf t st.2.2
  z : Seed.Z32 t

def body (lay : Layer) (tree sel : Nat) (st : List Digest × List (List Digest) × List Digest) (leaf : Nat) :
    T3.M (List Digest × List (List Digest) × List Digest) := do
  let ((root,prefixes),carry) ← SigGolfCandidate.Research.SharedForest.buildLeafPrefixes lay tree leaf st.2.2
  pure (st.1++[root],if leaf=sel then prefixes else st.2.1,carry)

variable {im : Image} (hc : SharedLowCode.Code im)
    (hsub : SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
variable {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat} {sb : Nat}
  {s1 : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1)
  (hselection : SharedPrefixes.selectionWord (s1.getMem 0x20550) lay.val=BitVec.ofNat 64 sel)
include hc hsub hcopy hchain hpref hseed hhook hs hselection
theorem body_step
    {l : Nat} (hl : l < 2 ^ height lay) {st : List Digest × List (List Digest) × List Digest} {t : MachineState}
    (htp : Inv s1 lay sb sel l st t) :
    TBSim im sk t (lowLeafC + 18)
      (body lay tree sel st l) (Inv s1 lay sb sel (l+1)) := by
  have ht := htp
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1x6, t1r, t1f⟩ := blk1175_spec hc t ht.pc l (height lay) (by omega)
    (by rcases hH with h | h <;> omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_pos hl] at t1pc
  obtain ⟨t2, st2, t2pc, t2x18, t2x22, t2x23, t2r, t2f⟩ := blk1178_spec hc t1 t1pc l sel (by omega)
    (by have := hs.hsel; omega) (by rw [t1r.get (by simp)]; exact ht.x13)
    (by rw [t1r.get (by simp), g _ (by decide), hs.x14])
  obtain ⟨t3, k3, st3, hk3, t3pc, t3x22, t3x23, t3r, t3f⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧
      k3 = (if l = sel then 3 else 0) ∧ t3.pc = pcOf 1187 ∧
      t3.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG) ∧
      t3.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY) ∧
      RegsExcept t2 t3 [.x22, .x23] ∧ Frame t2 t3 (fun _ => False) := by
    by_cases hls : l = sel
    · rw [if_pos hls] at t2pc
      obtain ⟨u, stu, upc, u22, u23, ur, uf⟩ := blk1184_spec hc t2 t2pc
      refine ⟨u, 3, stu, by simp [hls], upc, by simp [hls, u22], ?_, ur, uf⟩
      rw [u23, t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x16]; simp [hls]
    · rw [if_neg hls] at t2pc
      exact ⟨t2, 0, Steps.refl _, by simp [hls], t2pc, by simp [hls, t2x22], by simp [hls, t2x23],
        RegsExcept.refl _ _, Frame.refl _ _⟩
  obtain ⟨t4, st4, t4pc, t4x1, t4x25, t4r, t4f⟩ := blk1187_spec hc t3 t3pc l (height lay) LOW hl
    (by rcases hH with h | h <;> omega) (by shared_tree_sgo)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp)]; exact ht.x13)
    (by rw [t3r.get (by simp), t2r.get (by simp)]; exact t1x6)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x2])
  have r14 : RegsExcept t t4 ([.x6] ++ [.x18, .x22, .x23] ++ [.x22, .x23] ++ [.x1, .x7, .x25]) :=
    ((t1r.trans t2r).trans t3r).trans t4r
  have f14 : Frame t t4 (fun _ => False) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  have hpre : LeafPreS sk t4 (btLeaf lay tree sel ds sb l) :=
    bt_leafPre hs hl ((ht.regs.trans r14).mono (by decide)) ((ht.frame.trans f14).mono
      (fun X _ h => by rcases h with h | h; exact h; exact h.elim)) t4x1
      (by rw [t4r.get (by simp), t3r.get (by simp)]; exact t2x18)
      (by rw [t4r.get (by simp)]; exact t3x22) (by rw [t4r.get (by simp)]; exact t3x23) t4x25
  have hcarry : l % 7 ≠ 0 → SharedSeed.FamBuf t4 st.2.2 := fun hp =>
    (htp.carry hp).frame f14 (fun _ _ _ h => h)
  have hvi : (btLeaf lay tree sel ds sb l).valp+16*(btLeaf lay tree sel ds sb l).n≤0x20550 ∨
      0x20558≤(btLeaf lay tree sel ds sb l).valp := by
    change (if l=sel then sb else DUMMY)+16*(btLeaf lay tree sel ds sb l).n≤0x20550 ∨ 0x20558≤(if l=sel then sb else DUMMY)
    rw [show (btLeaf lay tree sel ds sb l).n=43 from chainCount_low hlay]
    split_ifs <;> shared_tree_sgo
  have hleaf := SharedLeafMemory.buildLeafPrefixes_precise hsub hcopy hchain hpref hseed hhook sk hpre hlay rfl t4pc
    (by rw [(ht.regs.trans r14).get (by decide),hs.x15]; rfl)
    (by show (if l=sel then sb else DUMMY)+16*(btLeaf lay tree sel ds sb l).n≤0x50000
        rw [show (btLeaf lay tree sel ds sb l).n=43 from chainCount_low hlay]; split_ifs <;> shared_tree_sgo)
    (by show (if l=sel then DIGITS else ZDIG)+(btLeaf lay tree sel ds sb l).n≤0x50000
        rw [show (btLeaf lay tree sel ds sb l).n=43 from chainCount_low hlay]; split_ifs <;> shared_tree_sgo)
    (by show LOW+16*(2^height lay+l)+16≤0x50000; shared_tree_sgo) hvi st.2.2 hcarry
  have hselection4 : SharedLeafMemory.Selected (btLeaf lay tree sel ds sb l) t4 ↔ l=sel := by
    have idx : t4.getMem 0x20550=s1.getMem 0x20550 := by
      change t4.getMem (BitVec.ofNat 64 0x20550)=s1.getMem (BitVec.ofNat 64 0x20550)
      exact (ht.frame.trans f14).get (by decide) (by unfold BtW; shared_tree_sgo)
    unfold SharedLeafMemory.Selected
    change SharedPrefixes.selectionWord (t4.getMem 0x20550) lay.val=BitVec.ofNat 64 l ↔ _
    rw [idx,hselection]
    exact (ofNat_inj (by have := hs.hsel; omega) (by omega)).trans eq_comm
  unfold body
  refine TBSim.mono (TBSim.steps (st1.trans (st2.trans (st3.trans st4)))
    (TBSim.bind (W₂ := 2) hleaf (fun r u hu => ?_))) ?_ (fun _ _ h => h)
  rotate_left
  · rw [hk3]; unfold lowLeafC; split_ifs <;> omega
  obtain ⟨upc,uroot,ulen,ucarry,ur,uf,uprecise,usaved,uz⟩ := hu
  obtain ⟨⟨root, values⟩, carry⟩ := r
  obtain ⟨t5, st5, t5pc, t5x13, t5r, t5f⟩ := blk1191_spec hc u upc l
    (by rw [ur.get (by decide), r14.get (by simp)]; exact ht.x13)
  have hLW : ∀ X, (LeafW (btLeaf lay tree sel ds sb l) X ∨ SharedLeafMemory.BScr X) → BtW sb (height lay) X := by
    intro X h
    rcases h with h | h
    swap
    · unfold BtW BScr SharedLeafMemory.BScr at *; omega
    unfold LeafW at h
    rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
    change X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
      (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨ ((if (btLeaf lay tree sel ds sb l).lay = 0 then LEAFPK + 16 else LEAFPK) ≤ X ∧ X < LEAFPK + 16 * (43 + 2)) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
      ((if l = sel then sb else DUMMY) ≤ X ∧ X < (if l = sel then sb else DUMMY) + 16 * 43) ∨
      (LOW + 16 * (2 ^ height lay + l) ≤ X ∧ X < LOW + 16 * (2 ^ height lay + l) + 16) at h
    unfold BtW
    rw [show 2 ^ (height lay + 1) = 2 * 2 ^ height lay by rw [pow_succ]; ring]
    split_ifs at h <;> shared_tree_sgo
  have fU : Frame t t5 (BtW sb (height lay)) := ((f14.trans uf).trans t5f).mono (fun X _ h => by
    rcases h with (h | h) | h
    · exact h.elim
    · exact hLW X h
    · exact h.elim)
  have hc : SharedSeed.FamBuf t5 carry := ucarry.frame t5f (fun _ _ _ h => h)
  refine TBSim.pure_steps st5 ⟨t5pc,t5x13,?_,?_,?_,by simp [ht.len],?_,?_,fun _ => hc,
    uz.frame t5f (by simp) (by simp)⟩
  · exact (((ht.regs.trans r14).trans ur).trans t5r).mono (by decide)
  · exact (ht.frame.trans fU).mono (fun X _ h => by rcases h with h | h <;> exact h)
  · exact (((ht.precise.trans f14).trans uprecise).trans t5f).mono (by
      intro X hX h
      rcases h with ((h|h)|h)|h
      · exact h
      · exact h.elim
      · unfold SharedLeafMemory.Writes TreeWrites at *
        simp only [btLeaf] at h
        tauto
      · exact h.elim)
  ·
    have hd : DigAt u (LOW + 16 * 2 ^ height lay + 16 * st.1.length) root := by
      rw [ht.len, show LOW + 16 * 2 ^ height lay + 16 * l = LOW + 16 * (2 ^ height lay + l) by ring]
      exact uroot
    have hold : DigsAt u (LOW + 16 * 2 ^ height lay) st.1 := by
      refine ht.roots.frame ((f14.trans uf).mono (fun X _ h => h)) (by rw [ht.len]; shared_tree_sgo) ?_
      intro B h1 h2 h
      rw [ht.len] at h2
      rcases h with h | h | h
      · exact h
      swap
      · unfold SharedLeafMemory.BScr at h; shared_tree_sgo
      · unfold LeafW at h
        rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨ B = CHAIN + 24 ∨
          (CHAIN + 32 ≤ B ∧ B < CHAIN + 112) ∨ ((if (btLeaf lay tree sel ds sb l).lay = 0 then LEAFPK + 16 else LEAFPK) ≤ B ∧ B < LEAFPK + 16 * (43 + 2)) ∨ (LOUT ≤ B ∧ B < LOUT + 32) ∨
          ((if l = sel then sb else DUMMY) ≤ B ∧ B < (if l = sel then sb else DUMMY) + 16 * 43) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ B ∧ B < LOW + 16 * (2 ^ height lay + l) + 16) at h
        split_ifs at h <;> shared_tree_sgo
    exact (hold.snoc hd).frame t5f (by simp only [List.length_append, List.length_singleton, ht.len]; shared_tree_sgo)
      (fun _ _ _ h => h)
  · intro hsl
    by_cases hls : l=sel
    · simp only [hls,if_true]
      refine ⟨ulen,?_⟩
      intro i hi k hk
      have saved := usaved (hselection4.mpr hls) i hi k hk
      simp only [btLeaf] at saved
      have hb := SharedPrefixes.buffer_bounds (lay:=lay.val)
        (by have hz : lay.val≠0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hi (by omega : k<8)
      exact saved.frame t5f (by omega) (by simp) (by simp)
    · simp only [hls,if_false]
      obtain ⟨hlen,hsaved⟩ := ht.saved (by omega)
      refine ⟨hlen,?_⟩
      intro i hi k hk
      have hb := SharedPrefixes.buffer_bounds (lay:=lay.val)
        (by have hz : lay.val≠0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hi (by omega : k<8)
      refine (hsaved i hi k hk).frame ((f14.trans uprecise).trans t5f) (by omega) ?_ ?_
      all_goals
        have hnot : ¬ SharedLeafMemory.Selected (btLeaf lay tree sel ds sb l) t4 := fun h => hls (hselection4.mp h)
        simp only [SharedLeafMemory.Writes,hnot,false_and,or_false,false_or]
        omega

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {im : Image} (hc : SharedLowCode.Code im)
include hc
theorem path_loop (t0 : MachineState) (H hi : Nat) (hH : H ≤ 7) (hhi : hi < 2 ^ (H + 1)) :
    ∀ (n j : Nat), j + n = H → ∀ (t : MachineState) (ep : Nat), t.pc = pcOf 1202 →
      t.getReg .x13 = BitVec.ofNat 64 j → t.getReg .x15 = BitVec.ofNat 64 H →
      t.getReg .x19 = BitVec.ofNat 64 hi → t.getReg .x2 = BitVec.ofNat 64 LOW →
      t.getReg .x24 = BitVec.ofNat 64 ep → ep % 8 = 0 → ep + 16 * n ≤ LOW →
      (∀ A, LOW ≤ A → A < LOW + 4096 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
      ∃ u k, Steps im t k k u ∧ k ≤ 12 * n + 1 ∧ u.pc = pcOf 1214 ∧
        (∀ i < n, DigAt u (ep + 16 * i) (memDig t0 (LOW + 16 * (hi / 2 ^ (j + i) ^^^ 1)))) ∧
        RegsExcept t u [.x6, .x7, .x13, .x24, .x28] ∧ Frame t u (fun A => ep ≤ A ∧ A < ep + 16 * n)
  | 0, j, hjn, t, ep, hpc, h13, h15, _, _, _, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk1202_spec hc t hpc j H (by omega) (by omega) h13 h15
    rw [if_neg (by omega)] at upc
    exact ⟨u, 1, st, by omega, upc, fun i hi => absurd hi (by omega), ur.mono (by simp),
      uf.mono (fun _ _ h => h.elim)⟩
  | n + 1, j, hjn, t, ep, hpc, h13, h15, h19, h2, h24, hep8, hepl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk1202_spec hc t hpc j H (by omega) (by omega) h13 h15
    rw [if_pos (by omega)] at t1pc
    have hhi' : hi < 8192 := lt_of_lt_of_le hhi (by
      calc 2 ^ (H + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 8192 := by norm_num)
    obtain ⟨t2, st2, t2pc, t2x13, t2x24, m0, m8, t2r, t2f⟩ := blk1203_spec hc t1 t1pc j hi LOW ep (by omega)
      hhi' (by shared_tree_sgo) (by shared_tree_sgo) (by shared_tree_sgo) hep8 (by rw [t1r.get (by simp)]; exact h13)
      (by rw [t1r.get (by simp)]; exact h19) (by rw [t1r.get (by simp)]; exact h2)
      (by rw [t1r.get (by simp)]; exact h24)
    have hx : hi / 2 ^ j ^^^ 1 < 8192 :=
      Nat.xor_lt_two_pow (n := 13) (lt_of_le_of_lt (Nat.div_le_self _ _) hhi') (by norm_num)
    have hx' : hi / 2 ^ j ^^^ 1 < 256 := by
      have h1 : hi / 2 ^ j < 2 ^ 8 := lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hhi
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact Nat.xor_lt_two_pow h1 (by norm_num)
    have f12 : Frame t t2 (fun A => A = ep ∨ A = ep + 8) := (t1f.trans t2f).mono (fun _ _ h => by
      rcases h with h | h; exact h.elim; exact h)
    obtain ⟨u, k, st, hk, upc, uem, ur, uf⟩ := path_loop t0 H hi hH hhi n (j + 1) (by omega) t2 (ep + 16) t2pc
      t2x13 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h15)
      (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19) (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2)
      t2x24 (by omega) (by omega) (fun A h1 h2' => (f12.get (by shared_tree_sgo) (by shared_tree_sgo)).trans (hheap A h1 h2'))
    refine ⟨u, 1 + (11 + k), st1.trans (st2.trans st), by omega, upc, fun i hi' => ?_,
      ((t1r.trans t2r).trans ur).mono (by simp), (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩
    rcases i with _ | i
    · simp only [Nat.mul_zero, Nat.add_zero]
      refine ⟨?_, ?_⟩
      · rw [uf.get (by shared_tree_sgo) (by omega), m0, t1f.get (by shared_tree_sgo) (fun h => h), hheap _ (by shared_tree_sgo) (by shared_tree_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).1
      · rw [uf.get (by shared_tree_sgo) (by omega), m8, t1f.get (by shared_tree_sgo) (fun h => h), hheap _ (by shared_tree_sgo) (by shared_tree_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).2
    · have := uem i (by omega)
      rw [show ep + 16 + 16 * i = ep + 16 * (i + 1) by ring, show j + 1 + i = j + (i + 1) by ring] at this
      exact this

def AllW (lay : Layer) (tree sb : Nat) (A : Nat) : Prop :=
  BtW sb (height lay) A ∨ LevW (btLev lay tree) A ∨ (sb+16*43≤A ∧ A<sb+16*(43+height lay)) ∨
  A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56
structure Post (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel sb ret : Nat)
    (s : MachineState) (r : List (List Digest) × List (List Digest)) (u : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : u.pc=pcOf ret
  plen : r.2.length=43
  saved : ∀ i,i<43 → ∀ k,k≤7 → DigAt u (SharedPrefixes.buffer lay.val i k) ((r.2.getD i []).getD k 0)
  path : DigsAt u (sb+16*43) ((List.range (height lay)).map fun j => (r.1.getD j []).getD (sel/2^j ^^^ 1) 0)
  left : DigAt u ENC (topPair lay r.1).1
  right : DigAt u (ENC+48) (topPair lay r.1).2
  base : Base (cfFlag := cfFlag) sk cache u
  regs : RegsExcept s u btAllRegs
  frame : Frame s u (AllW lay tree sb)
  precise : Frame s u (TreeWrites lay)

theorem tail (hlevels : SharedTreeCode.Code im 1013) {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s s1 t : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1)
    (h4 : s1.getReg .x4 = pcOf ret) (hr0 : RegsExcept s s1 [.x4, .x13]) (hf0 : Frame s s1 (fun _ => False))
    {st : List Digest × List (List Digest) × List Digest} (ht : Inv s1 lay sb sel (2^height lay) st t) :
    TBSim im sk t 19000 (do
      let levels ← ClaudeWCT.WCT9.buildLevelsBelow 3 lay.val tree (height lay) st.1
      pure (levels, st.2.1)) (Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hH7 : height lay ≤ 7 := by rcases hH with h | h <;> omega
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  have hsb8 := hs.hsb8
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, -, t1r, t1f⟩ := blk1175_spec hc t ht.pc (2 ^ height lay) (height lay) (by omega)
    (by omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x21, t2r, t2f⟩ := blk1193_spec hc t1 t1pc lay.val tree
    (by have : lay.val ≠ 0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hs.htree
    (by rw [t1r.get (by simp), g _ (by decide), hs.x8]) (by rw [t1r.get (by simp), g _ (by decide), hs.x9])
  have g2 : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x6, .x21] → t2.getReg r = s1.getReg r := fun r hr =>
    ((ht.regs.trans t1r).trans t2r).get hr
  have f2 : Frame s1 t2 (BtW sb (height lay)) := (ht.frame.trans (t1f.trans t2f)).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact h.elim
    · exact h.elim)
  have hlp : LevPre t2 (btLev lay tree) st.1 :=
    { x1 := t2x1
      x2 := by rw [g2 _ (by decide), hs.x2]; rfl
      x5 := by rw [g2 _ (by decide), hs.base.x5]
      x9 := by rw [g2 _ (by decide), hs.x9]; rfl
      x15 := by rw [g2 _ (by decide), hs.x15]; rfl
      x21 := t2x21
      tag3 := rfl
      hlay := lay.isLt
      htree := hs.htree
      hh1 := by show 1 ≤ height lay; omega
      hh := by show height lay ≤ 12; omega
      ha8 := by show LOW % 8 = 0; decide
      ha := by
        show LOW + 16 * 2 ^ (height lay + 1) ≤ 2 ^ 24
        rcases hH with h | h <;> rw [h] <;> norm_num
      has := Or.inl (by show NOUT + 32 ≤ LOW; decide)
      z32 := by
        rw [f2.get (by shared_tree_sgo) (by unfold BtW; shared_tree_sgo)]
        exact hs.base.zero _ (by shared_tree_sgo) (by unfold NeverW; simp)
      z40 := by
        rw [f2.get (by shared_tree_sgo) (by unfold BtW; shared_tree_sgo)]
        exact hs.base.zero _ (by shared_tree_sgo) (by unfold NeverW; simp)
      hlen := ht.len
      hleaves := by
        show DigsAt t2 (LOW + 16 * 2 ^ height lay) st.1
        exact ht.roots.frame (t1f.trans t2f) (by rw [ht.len]; shared_tree_sgo) (fun _ _ _ h => by
          rcases h with h | h <;> exact h) }
  have hlev := SharedTree.buildLevelsBelow_tsim hlevels sk hlp
    (by show 1 ≤ lay.val; exact Nat.pos_of_ne_zero (fun h => hlay (Fin.ext h)))
    (by show 2 ≤ height lay; rcases hH with h | h <;> omega) t2pc
  obtain ⟨hlk, hlc⟩ := btLev_costs lay hlay tree
  change SharedTree.levKB (btLev lay tree)≤SharedTree.levCB (btLev lay tree) at hlk
  change SharedTree.levCB (btLev lay tree)≤6609 at hlc
  -- Stage 2 (C2): `WCT9.buildLevelsBelow` is `Seed.levelsBelowW` by definition (`lowerLevel` halves).
  rw [SigGolfCandidate.T3M.Sign.Seed.buildLevelsBelow_eq_levelsBelowW]
  refine TBSim.mono (TBSim.steps (st1.trans st2) (TBSim.bind (W₂ := 120) (TSim.toTBSim hlev hlk)
    (fun levels u hu => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨upc, uheap, ur, uf⟩ := hu
  have gu : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs → u.getReg r = s1.getReg r := fun r hr =>
    (((ht.regs.trans t1r).trans t2r).trans ur).get hr
  obtain ⟨v, stv, vpc, vx13, vx19, vx24, vr, vf⟩ := blk1196_spec hc u upc (height lay) sel sb 43 (by omega)
    (by omega) (by shared_tree_sgo) (by rw [gu _ (by decide), hs.x15]) (by rw [gu _ (by decide), hs.x14])
    (by rw [gu _ (by decide), hs.x16]) (by rw [gu _ (by decide), hs.x26])
  have gv : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] →
      v.getReg r = s1.getReg r := fun r hr => ((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).get hr
  obtain ⟨w, k, stw, hk, wpc, wem, wr, wf⟩ := path_loop hc u (height lay) (2 ^ height lay + sel) hH7
    (by rw [pow_succ]; omega) (height lay) 0 (by omega) v (sb + 16 * 43) vpc vx13
    (by rw [gv _ (by decide), hs.x15]) vx19 (by rw [gv _ (by decide), hs.x2]) vx24 (by omega) (by shared_tree_sgo)
    (fun A h1 h2 => vf.get (by shared_tree_sgo) (fun h => h))
  obtain ⟨x, stx, xpc, xm0, xm8, xm48, xm56, xr, xf⟩ := BCBlocks.blk1214_pair_spec hc w wpc LOW ret (by decide) (by decide) (by decide)
    (by rw [wr.get (by simp), gv _ (by decide), hs.x2])
    (by rw [wr.get (by simp), gv _ (by decide), h4])
  refine TBSim.mono (TBSim.pure_steps (stv.trans (stw.trans stx)) ?_) (by omega) (fun _ _ h => h)
  have fux : Frame u x (fun A => (sb + 16 * 43 ≤ A ∧ A < sb + 16 * 43 + 16 * height lay) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) :=
    ((vf.trans wf).trans xf).mono (fun A _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact Or.inl h
      · exact Or.inr h)
  have f1x : Frame s1 x (AllW lay tree sb) := (f2.trans (uf.trans fux)).mono (fun A _ h => by
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr h)))
  have hW : ∀ A, A < 2 ^ 64 → BaseA A → AllW lay tree sb A → A = CHAIN + 32 ∨ A = CHAIN + 40 := by
    intro A _ hb hw
    unfold BaseA NeverW Search.TOP_DATA at hb
    unfold AllW BtW LevW at hw
    simp only [btLev] at hw
    rcases hH with h | h <;> rw [h] at hw <;> shared_tree_sgo
  have hzx : Seed.Z32 x := by
    have fx := (t1f.trans t2f).trans (uf.trans fux)
    refine ht.z.frame fx ?_ ?_ <;>
    · intro h
      simp only [LevW, btLev] at h
      rcases hH with hh | hh <;> rw [hh] at h <;> shared_tree_sgo
  have r1x : RegsExcept s1 x (btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
      [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]) :=
    (((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).trans wr).trans xr
  obtain ⟨-, hlv⟩ := uheap
  refine ⟨xpc,(ht.saved hsel).1,?_,?_,?_,?_,Seed.Base.frame_z32 hs.base f1x r1x (by decide) hW hzx,?_,?_,?_⟩
  · intro i hi k hk
    have hb := SharedPrefixes.buffer_bounds (lay:=lay.val)
      (by have hz : lay.val≠0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hi (by omega : k<8)
    refine ((ht.saved hsel).2 i hi k hk).frame ((t1f.trans t2f).trans (uf.trans fux)) (by omega) ?_ ?_
    all_goals
      simp only [LevW,btLev]
      shared_tree_sgo
  ·
    intro i hi
    rw [List.length_map, List.length_range] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    have he := wem i hi
    rw [Nat.zero_add, heapH_sib hi] at he
    obtain ⟨hlen, hd⟩ := hlv i (by show i ≤ height lay - 1; omega)
    have hq : sel / 2 ^ i < 2 ^ (height lay - i) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i), ← pow_add, Nat.sub_add_cancel hi.le]; exact hsel
    have h2i : 2 ^ 1 ≤ 2 ^ (height lay - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkq : sel / 2 ^ i ^^^ 1 < 2 ^ (height lay - i) := Nat.xor_lt_two_pow hq (by omega)
    have hdi := hd _ (by rw [hlen]; exact hkq)
    simp only [btLev] at hdi
    rw [show LOW + 16 * (2 ^ (height lay - i) + (sel / 2 ^ i ^^^ 1)) =
      LOW + 16 * 2 ^ (height lay - i) + 16 * (sel / 2 ^ i ^^^ 1) by ring, memDig_eq hdi] at he
    exact he.frame xf (by shared_tree_sgo) (by shared_tree_sgo) (by shared_tree_sgo)
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by change height lay - 1 ≤ height lay - 1; omega)
    have he : height lay - (height lay - 1) = 1 := by rcases hH with h | h <;> omega
    have hd0 := hd 0 (by rw [hl0]; simp only [btLev, he]; norm_num)
    simp only [btLev, he, pow_one, Nat.mul_zero, Nat.add_zero] at hd0
    change DigAt x ENC ((levels.getD (height lay - 1) []).getD 0 0)
    refine ⟨?_, ?_⟩
    · rw [xm0, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd0.1
    · rw [xm8, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd0.2
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by change height lay - 1 ≤ height lay - 1; omega)
    have he : height lay - (height lay - 1) = 1 := by rcases hH with h | h <;> omega
    have hd1 := hd 1 (by rw [hl0]; simp only [btLev, he]; norm_num)
    simp only [btLev, he, pow_one, Nat.mul_one] at hd1
    change DigAt x (ENC + 48) ((levels.getD (height lay - 1) []).getD 1 0)
    refine ⟨?_, ?_⟩
    · rw [xm48, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd1.1
    · rw [xm56, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd1.2
  · exact (hr0.trans r1x).mono (by decide)
  · exact (hf0.trans f1x).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  · exact (hf0.trans ((ht.precise.trans (t1f.trans t2f)).trans (uf.trans fux))).mono (by
      intro A hA h
      rcases h with h|((h|h|h)|h|h|h)
      · exact h.elim
      · exact h
      · exact h.elim
      · exact h.elim
      · left; unfold LevW btLev at h; shared_tree_sgo
      · left; shared_tree_sgo
      · left; shared_tree_sgo)

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def treeProgram (lay : Layer) (tree sel : Nat) : T3.M (List (List Digest) × List (List Digest)) := do
  let st ← (List.range (2^height lay)).foldlM (body lay tree sel) ([],[],[])
  let levels ← ClaudeWCT.WCT9.buildLevelsBelow 3 lay.val tree (height lay) st.1
  pure (levels,st.2.1)
variable {im : Image} (hc : SharedLowCode.Code im)
    (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
include hc hlevels hsub hcopy hchain hpref hseed hhook
theorem tree_tbsim {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s) (hpc : s.pc = pcOf 1173)
    (h1 : s.getReg .x1 = pcOf ret)
    (hselection : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val=BitVec.ofNat 64 sel) :
    TBSim im sk s btCost (treeProgram lay tree sel) (Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  obtain ⟨s1, st1, s1pc, s1x4, s1x13, s1r, s1f⟩ := blk1173_spec hc s hpc
  have g1 : ∀ r, r ∉ [.x4, .x13] → s1.getReg r = s.getReg r := fun r hr => s1r.get hr
  have hs1 : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1 :=
    { x2 := by rw [g1 _ (by decide), hs.x2]
      x8 := by rw [g1 _ (by decide), hs.x8]
      x9 := by rw [g1 _ (by decide), hs.x9]
      x14 := by rw [g1 _ (by decide), hs.x14]
      x15 := by rw [g1 _ (by decide), hs.x15]
      x16 := by rw [g1 _ (by decide), hs.x16]
      x26 := by rw [g1 _ (by decide), hs.x26]
      x27 := by rw [g1 _ (by decide), hs.x27]
      x31 := by rw [g1 _ (by decide), hs.x31]
      base := hs.base.frame s1f s1r (by decide) (fun _ _ _ h => h)
      hlay := hlay
      htree := hs.htree
      hsel := hsel
      hroute := hs.hroute
      hdb := hs.hdb
      digits := fun i hi => by rw [s1f.getByte (by shared_tree_sgo) (fun h => h)]; exact hs.digits i hi
      hsb := hsb
      hsb8 := hs.hsb8 }
  have h0 : Inv s1 lay sb sel 0 ([],[],[]) s1 :=
    ⟨s1pc,s1x13,RegsExcept.refl _ _,Frame.refl _ _,Frame.refl _ _,rfl,DigsAt.nil _ _,
      fun h => absurd h (by omega),fun h => absurd h (by decide),
      ⟨(s1f.get (by decide) (by simp)).trans (hs.base.zero _ (by decide) (by unfold NeverW; simp)),
        (s1f.get (by decide) (by simp)).trans (hs.base.zero _ (by decide) (by unfold NeverW; simp))⟩⟩
  have hselection1 : SharedPrefixes.selectionWord (s1.getMem 0x20550) lay.val=BitVec.ofNat 64 sel := by
    have idx : s1.getMem 0x20550=s.getMem 0x20550 := s1f.get (by decide) (by simp)
    rw [idx]; exact hselection
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) 0 (2 ^ height lay)
    (body lay tree sel) ([],[],[]) (Inv s1 lay sb sel)
    (lowLeafC + 18)
    (fun l hl st t ht => by simpa using body_step hc hsub hcopy hchain hpref hseed hhook hs1 hselection1 hl ht) h0
  have hcost : 2 + (2 ^ height lay * (lowLeafC + 18) + 19000) ≤ btCost := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals decide
  unfold treeProgram
  have heq : List.range' 0 (2 ^ height lay) = List.range (2 ^ height lay) := List.range_eq_range'.symm
  rw [heq] at hloop
  exact TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 19000) hloop
    (fun st t ht => tail hc hlevels hs1 (by rw [s1x4, h1]) s1r s1f ht))) hcost (fun _ _ h => h)
end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open OracleComp SigGolfCandidate.T3
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000

theorem body_eq (lay : Layer) (hlay : lay≠0) (tree sel : Nat)
    (st : List Digest × List (List Digest) × List Digest) (leaf : Nat) :
    body lay tree sel st leaf = (do
      let ((root,prefixes),carry) ← if leaf=sel then SigGolfCandidate.Research.SharedForest.buildLeafPrefixes lay tree leaf st.2.2
        else do
          let ((root,_),carry) ← ClaudeWCT.WCT9.buildLeafPF lay tree leaf [] st.2.2
          pure ((root,[]),carry)
      pure (st.1++[root],if leaf=sel then prefixes else st.2.1,carry)) := by
  by_cases h : leaf=sel
  · simp only [body,h,if_true]
  · simp only [body,h,if_false,bind_assoc,pure_bind]
    exact SharedLeafMemory.buildLeafPrefixes_forget lay hlay tree leaf st.2.2
      (fun root carry => pure (st.1++[root],st.2.1,carry))

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open OracleComp SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000

theorem treeProgram_eq (lay : Layer) (hlay : lay≠0) (tree sel : Nat) :
    (treeProgram lay tree sel >>= fun r => pure (PreparedLower.mk r.1 r.2)) =
      buildTreePrefixes lay tree sel := by
  unfold treeProgram buildTreePrefixes
  simp only [bind_assoc,pure_bind]
  congr 1
  apply congrArg (fun f => (List.range (2^height lay)).foldlM f ([],[],[]))
  funext st leaf
  exact body_eq lay hlay tree sel st leaf

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem buildTreePrefixes_tbsim {im : Image} (hc : SharedLowCode.Code im)
    (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s)
    (hpc : s.pc = pcOf 1173) (h1 : s.getReg .x1 = pcOf ret)
    (hselection : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val=BitVec.ofNat 64 sel) :
    TBSim im sk s btCost (buildTreePrefixes lay tree sel)
      (fun r => Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s (r.levels,r.prefixes)) := by
  have h := tree_tbsim hc hlevels hsub hcopy hchain hpref hseed hhook hs hpc h1 hselection
  rw [← treeProgram_eq lay hs.hlay tree sel]
  have ht : TBSim im sk s (btCost+0)
      (treeProgram lay tree sel >>= fun r => pure (PreparedLower.mk r.1 r.2))
      (fun r => Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s (r.levels,r.prefixes)) :=
    TBSim.bind (W₂:=0) h (fun r t ht => TBSim.pure ht)
  simpa using ht
end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem TreeWrites.not_metadata (lay : Layer) (hl : lay≠0) {A : Nat}
    (ha : 0x66000≤A) (hb : A<0x6e000) : ¬TreeWrites lay A := by
  have := lay.isLt
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  unfold TreeWrites
  omega

theorem Post.metadata {sk : SecretKey} {cache : Bytes 131072} {lay : Layer}
    {tree sel sb ret : Nat} {s u : MachineState} {r : List (List Digest) × List (List Digest)}
    (h : Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s r u) (hl : lay≠0) (A : Nat)
    (ha : 0x66000≤A) (hb : A<0x6e000) :
    u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=
  h.precise.get (by omega) (TreeWrites.not_metadata lay hl ha hb)

theorem TreeWrites.not_other_prefix (lay other : Layer) (hne : lay≠other)
    (ho : other≠0) {i k : Nat} (hi : i<43) (hk : k<8) (half : Nat) (hh : half<2) :
    ¬TreeWrites lay (SharedPrefixes.buffer other.val i k+8*half) := by
  have hsame : lay.val≠other.val := fun h => hne (Fin.ext h)
  have hl := lay.isLt
  have hother := other.isLt
  have h0 : other.val≠0 := fun h => ho (Fin.ext h)
  unfold TreeWrites SharedPrefixes.buffer
  omega

end SigGolfCandidate.T3M.Sign.SharedLowTree
