import SigGolfCandidate.Merge042
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge094
import SigGolfCandidate.Merge095

-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_PackedLeaf ====
section
-- serialization only (no declarations used): keeps this ~14 GB module from building in parallel with the other heavy ones under the verifier's 2-job / 24 GiB limit

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
end
-- ==== merged from T3M_Sign_PackedBoundaryEntry ====
section

section


namespace SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3
open ClaudeWCT
def signLayersP (leafFn : LeafFn) (cache : Cache) (index : Nat) : Nat → WCT9.LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreeP leafFn lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := WCT9.topPair lay levels
        let some previous ← signLayersP leafFn cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))
end SigGolfCandidate.T3M.Sign.Packed
end

section









namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest counterLimit buildLeaf)
open Keygen (LeafArgs LeafW leafRegs)
theorem blk370_spec (s : MachineState) (hpc : s.pc = pcOf 370) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 396 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (FOUT + 8)) ∧
      t.getReg .x2 = BitVec.ofNat 64 LOW ∧ t.getReg .x31 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4832) ∧ t.getReg .x17 = BitVec.ofNat 64 202 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx % 64) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx % 64) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 64) ∧
      RegsExcept s t [.x1, .x2, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x26, .x27, .x28, .x29, .x30,
        .x31] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 0 &&& 63#64) = BitVec.ofNat 64 (x % 64) := by
    intro x hx
    rw [ofNat_shr x 0 hx, pow_zero, Nat.div_one]
    exact ofNat_and_mask x 6 (by norm_num)
  refine ⟨_, symRun_sound blk_370 codeAt_370 s hpc (by simp [blk_370.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_370.res, E.eval]
  · simp [blk_370.res, rv_simp]
  · simp only [Result.toState_getMem, blk_370.res, ENC, FOUT]; t3n []
  · simp only [Result.toState_getMem, blk_370.res, ENC, FOUT]; t3n []
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 6 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_370.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, blk_370.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem blkBT_spec {a : Nat} {seg : List (BitVec 32)} {r : Result} (hc : CodeAt image (pcOf a) seg)
    (hrun : symRun { noAlias := true } seg (pcOf a) 100 = some r) (s : MachineState) (hpc : s.pc = pcOf a)
    (hobl : r.obligs s) (hpcE : (r.toState s).pc = pcOf 1173) (h1 : (r.toState s).getReg .x1 = pcOf (a + 1))
    (hregs : RegsExcept s (r.toState s) [.x1]) (hfr : Frame s (r.toState s) (fun _ => False)) :
    ∃ t, Steps image s r.steps r.cycles t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (a + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  ⟨_, symRun_sound hrun hc s hpc hobl, hpcE, h1, hregs, hfr⟩
theorem blk396_spec (s : MachineState) (hpc : s.pc = pcOf 396) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 397 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_396 blk_396 s hpc (by simp [blk_396.res, rv_simp]) (by simp [blk_396.res, E.eval])
    (by simp [blk_396.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_396.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_396.res, rv_simp])
theorem blk411_spec (s : MachineState) (hpc : s.pc = pcOf 411) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 412 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_411 blk_411 s hpc (by simp [blk_411.res, rv_simp]) (by simp [blk_411.res, E.eval])
    (by simp [blk_411.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_411.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_411.res, rv_simp])
theorem blk426_spec (s : MachineState) (hpc : s.pc = pcOf 426) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 427 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_426 blk_426 s hpc (by simp [blk_426.res, rv_simp]) (by simp [blk_426.res, E.eval])
    (by simp [blk_426.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_426.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_426.res, rv_simp])
theorem blk397_spec (s : MachineState) (hpc : s.pc = pcOf 397) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 411 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4048) ∧ t.getReg .x17 = BitVec.ofNat 64 202 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx / 64 % 64) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx / 64 % 64) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 4096) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 6 &&& 63#64) = BitVec.ofNat 64 (x / 64 % 64) := by
    intro x hx
    rw [ofNat_shr x 6 hx]
    exact ofNat_and_mask (x / 2 ^ 6) 6 (by norm_num)
  refine ⟨_, symRun_sound blk_397 codeAt_397 s hpc (by simp [blk_397.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_397.res, E.eval]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 12 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_397.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_397.res, rv_simp]
theorem blk412_spec (s : MachineState) (hpc : s.pc = pcOf 412) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 426 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 3248) ∧ t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx / 4096 % 128) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx / 4096 % 128) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 12 &&& 127#64) = BitVec.ofNat 64 (x / 4096 % 128) := by
    intro x hx
    rw [ofNat_shr x 12 hx]
    exact ofNat_and_mask (x / 2 ^ 12) 7 (by norm_num)
  refine ⟨_, symRun_sound blk_412 codeAt_412 s hpc (by simp [blk_412.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_412.res, E.eval]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 19 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_412.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_412.res, rv_simp]
def L0W (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 3248 ≤ A ∧ A < SIG + 5616)
/-- Campaign T8D: the scratch of the top seed routines (COEFGEN/HORN register saves at `0x60000`, the 40 top
coefficients at `0x61000`). -/
def TopScr (A : Nat) : Prop := 0x60000 ≤ A ∧ A < 0x61280
/-- Cycle bound of one signature-only top leaf (prologue, COEFGEN, 54 x (HORN + chain), exit). -/
def topLeafC : Nat := 225300
def L0Cost : Nat := counterLimit * 270 + topLeafC + 38800
/-- Campaign T8D (NF17): the top leaf with family seeds (`T3.buildLeafTop`). -/
def TopLeafSpec : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState),
    A.lay = 0 → A.so = true → A.tree = 0 → (∀ i < A.n, A.d i ≤ 7) →
    A.valp + 16 * A.n ≤ 0x60000 → A.digp + A.n ≤ 0x60000 → A.dest + 16 ≤ 0x60000 →
    LeafPreS sk s A → s.pc = pcOf (1013 + 27) →
    TBSim image sk s topLeafC (T3.buildLeafTop A.leaf A.digits A.so)
      (fun r t => t.pc = pcOf A.ret ∧ DigsAt t A.valp r.2 ∧ r.2.length = A.n ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ TopScr X))
end SigGolfCandidate.T3M.Sign.Packed
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer counterLimit)
open ClaudeWCT
abbrev CsPre := Search.BC.CsPreS 543
abbrev DummyRet := Search.BC.DummyOutS
def CsPost (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if lay = 0 then DummyRet s ret t else Failed t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧
      (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) =
        BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧
      RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay
abbrev csCost := Search.BC.csCostS
def CounterSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (ret : Nat),
    CsPre s lay tree leaf msg ret →
      TBSim image sk s (csCost lay) (WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay))
        (CsPost s lay ret)
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Pieces signLayers)
open ClaudeWCT
structure L0Pre (sk : SecretKey) (cache : Bytes 131072) (index : Nat) (message : WCT9.LayerMsg)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 427
  base : Base sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC (Search.BC.left message)
  right : DigAt t (ENC + 48) (Search.BC.right message)
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
def L0Post (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => ∃ vals path : List Digest, ps = [(vals, path)] ∧ u.pc = pcOf 540 ∧
      (∀ i < 54, DigAt u (SIG + 2192 + 16 * i) (vals.getD i 0)) ∧
      (∀ j < 12, DigAt u (SIG + 3056 + 16 * j) (path.getD j 0)) ∧ Frame t u L0W
def L0Spec (leafFn : LeafFn) (sk : SecretKey) (cache : Bytes 131072) : Prop :=
  ∀ (index : Nat) (root : WCT9.LayerMsg) (t : MachineState), L0Pre sk cache index root t →
    TBSim image sk t L0Cost (signLayersP leafFn (cacheDec cache) index 1 root) (L0Post t)
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3 (Layer Digest decode dataDigits dataCount chainCount maxDigit)
theorem dataDigits_getD (lay : Layer) (v : Digest) (i : Nat) (hi : i < dataCount lay) :
    (dataDigits lay v).getD i 0 ≤ maxDigit lay i := by
  rw [T3.dataDigits_getD lay v i hi]
  exact T3.Nonbinary.coreDigit_le lay v i
theorem length_dataDigits (lay : Layer) (v : Digest) : (dataDigits lay v).length = dataCount lay := by
  simp [dataDigits]
theorem decode_digits {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ds.length = chainCount lay ∧ ∀ i < chainCount lay, ds.getD i 0 ≤ maxDigit lay i :=
  ⟨(T3.decode_length_sum h).1, T3.decode_digit_max h⟩
end SigGolfCandidate.T3M.Sign.Packed
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open ClaudeWCT
open SigGolfCandidate.T3 (Layer Digest Pieces counterLimit buildTree height chainCount
  target route decode width Cache)
open SigGolfCandidate.T3M.Keygen (LevW n4)
def lstart : Nat → Nat
  | 0 => 137
  | 1 => 203
  | 2 => 253
  | 3 => 302
  | _ => 351
theorem lstart_mono (n : Nat) : lstart n ≤ lstart (n + 1) := by
  rcases n with _ | _ | _ | _ | n <;> simp [lstart]
def LayW (n : Nat) (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 16 * lstart n ≤ A ∧ A < SIG + 5616)
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (layIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (layIdx lay + chainCount lay + j)) (p.2.getD j 0)
def SLPost (t : MachineState) (n : Nat) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => u.pc = pcOf 540 ∧ ps.length = n ∧ (∀ lay : Layer, lay.val < n → PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (LayW n)
theorem SLPost.pre {s t : MachineState} {n : Nat} (hf : Frame s t (fun _ => False)) :
    ∀ r u, SLPost t n r u → SLPost s n r u
  | none, _, h => h
  | some _, _, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (hf.trans h4).mono (fun _ _ h => by
      rcases h with h | h
      · exact h.elim
      · exact h)⟩
theorem lay_cases {lay : Layer} (hlay : lay ≠ 0) :
    (lay.val = 1 ∧ layIdx lay = 203 ∧ height lay = 7) ∨ (lay.val = 2 ∧ layIdx lay = 253 ∧ height lay = 6) ∨
      (lay.val = 3 ∧ layIdx lay = 302 ∧ height lay = 6) := by
  fin_cases lay
  · exact absurd rfl hlay
  · left; exact ⟨rfl, rfl, rfl⟩
  · right; left; exact ⟨rfl, rfl, rfl⟩
  · right; right; exact ⟨rfl, rfl, rfl⟩
theorem lay_facts {lay : Layer} (hlay : lay ≠ 0) :
    lstart lay.val = layIdx lay ∧ lstart (lay.val + 1) = layIdx lay + 43 + height lay ∧ 203 ≤ layIdx lay ∧
      layIdx lay + 43 + height lay ≤ 351 := by
  rcases lay_cases hlay with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> simp [lstart]
theorem csW_layW {n A : Nat} (h : CsW A) : LayW n A := by
  have := lstart_mono n
  unfold CsW at h
  unfold LayW
  constructor <;> packed_sgo
theorem btAllW_layW {lay : Layer} (hlay : lay ≠ 0) {tree A : Nat} (h : BtAllW lay tree (SIG + 16 * layIdx lay) A) :
    LayW (lay.val + 1) A := by
  unfold BtAllW BtW LevW at h
  simp only [btLev] at h
  unfold LayW
  obtain ⟨-, hls, -, -⟩ := lay_facts hlay
  rw [hls]
  rcases lay_cases hlay with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ <;> rw [h2, h3] at h <;> rw [h2, h3] <;>
    simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at h ⊢ <;> constructor <;> packed_sgo
theorem layW_succ {n A : Nat} (h : LayW n A) : LayW (n + 1) A := by
  have := lstart_mono n
  exact ⟨h.1, fun h2 => h.2 ⟨by omega, h2.2⟩⟩
theorem route_lt {index : Nat} (h : index < 2 ^ 31) (lay : Layer) :
    (route index lay).1 < 2 ^ height lay ∧ (route index lay).2 < 2 ^ 32 := by
  simp only [route]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
theorem route_3 (index : Nat) : route index 3 = (index % 64, index / 64) := by
  show (index / 2 ^ 0 % 2 ^ 6, index / 2 ^ (0 + 6)) = _
  simp
theorem route_2 (index : Nat) : route index 2 = (index / 64 % 64, index / 4096) := by
  show (index / 2 ^ 6 % 2 ^ 6, index / 2 ^ (6 + 6)) = _
  simp
theorem route_1 (index : Nat) : route index 1 = (index / 4096 % 128, index / 2 ^ 19) := by
  show (index / 2 ^ 12 % 2 ^ 7, index / 2 ^ (12 + 7)) = _
  simp
def jalBT (lay : Layer) : Nat := (![0, 426, 411, 396] : Layer → Nat) lay
theorem blkJal_spec {lay : Layer} (hlay : lay ≠ 0) (s : MachineState) (hpc : s.pc = pcOf (jalBT lay)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (jalBT lay + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  fin_cases lay
  · exact absurd rfl hlay
  · exact blk426_spec s hpc
  · exact blk411_spec s hpc
  · exact blk396_spec s hpc
structure LayEntry (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (index : Nat) (msg : WCT9.LayerMsg)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 646
  x1 : t.getReg .x1 = pcOf (jalBT lay)
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : t.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x14 : t.getReg .x14 = BitVec.ofNat 64 (route index lay).1
  x15 : t.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : t.getReg .x16 = BitVec.ofNat 64 (SIG + 16 * layIdx lay)
  x17 : t.getReg .x17 = BitVec.ofNat 64 (target lay)
  x18 : t.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache t
  hlay : lay ≠ 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC (Search.BC.left msg)
  right : DigAt t (ENC + 48) (Search.BC.right msg)
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
structure LayNext (sk : SecretKey) (cache : Bytes 131072) (ret index : Nat) (root : WCT9.LayerMsg) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf ret
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC (Search.BC.left root)
  right : DigAt t (ENC + 48) (Search.BC.right root)
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
theorem signLayers_low (cache : Cache) (index : Nat) {lay : Layer} (hlay : lay ≠ 0) (msg : WCT9.LayerMsg) :
    signLayersP leafFn cache index (lay.val + 1) msg = (do
      let some (_, digits) ← WCT9.layerCounterSearch lay (route index lay).2 (route index lay).1 msg 0
        (WCT9.searchLimit lay)
        | pure none
      let (levels, values) ← Packed.buildTreeP leafFn lay (route index lay).2 (route index lay).1 digits
      let some previous ← signLayersP leafFn cache index lay.val (.pair (WCT9.topPair lay levels).1 (WCT9.topPair lay levels).2) | pure none
      pure (some (previous ++ [(values, (List.range (height lay)).map fun j =>
        (levels.getD j []).getD ((route index lay).1 / 2 ^ j ^^^ 1) 0)]))) := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals rfl
section layer
variable {sk : SecretKey} {cache : Bytes 131072}
-- (witness stack) removed: legacy reference-image lower tree (LeafW now covers CHAIN+32..112; no users).
theorem entry2 {index : Nat} {root : WCT9.LayerMsg} {v : MachineState} (h : LayNext sk cache 397 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 2 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk397_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_2]
      x14 := by rw [tx14, route_2]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_2]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      right := h.right.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      c32 := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.c32 }
theorem entry1 {index : Nat} {root : WCT9.LayerMsg} {v : MachineState} (h : LayNext sk cache 412 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 1 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk412_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_1]
      x14 := by rw [tx14, route_1]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_1]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      right := h.right.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      c32 := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.c32 }
def layW1 : Nat := L0Cost
def layW2 : Nat := 14 + (csCost 1 + (1 + (btCost + layW1)))
def layW3 : Nat := 14 + (csCost 2 + (1 + (btCost + layW2)))
def layersC : Nat := csCost 3 + (1 + (btCost + layW3))
-- (witness stack) removed: legacy reference-image lower tree (LeafW now covers CHAIN+32..112; no users).
end layer
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest Cache readDigest readLE mask header privateInput)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
def topSlot (leaf level : Nat) : Nat := 8192 - 2 ^ (13 - level) + (leaf / 2 ^ level ^^^ 1)
def topNode (cache : Bytes 131072) (leaf level : Nat) : Digest :=
  readDigest (List.ofFn fun i : Fin 16 =>
    (cacheDec cache).region ⟨(16 * topSlot leaf level + i.val) % 131040, Nat.mod_lt _ (by decide)⟩)
theorem topSlot_lt {leaf level : Nat} (hl : leaf < 4096) (h11 : level ≤ 11) :
    leaf / 2 ^ level ^^^ 1 < 2 ^ (12 - level) ∧ topSlot leaf level < 8190 := by
  have hp : 2 ^ level * 2 ^ (12 - level) = 2 ^ 12 := by rw [← Nat.pow_add]; congr 1; omega
  have hq : leaf / 2 ^ level < 2 ^ (12 - level) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [Nat.mul_comm, hp]; omega
  have hx : leaf / 2 ^ level ^^^ 1 < 2 ^ (12 - level) :=
    Nat.xor_lt_two_pow hq (Nat.one_lt_two_pow (by omega))
  have h13 : 2 ^ (13 - level) = 2 * 2 ^ (12 - level) := by
    rw [show 13 - level = (12 - level) + 1 by omega, Nat.pow_succ]; ring
  have hc2 : 2 ≤ 2 ^ (12 - level) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤ 12 - level by omega); simpa using this
  refine ⟨hx, ?_⟩
  unfold topSlot
  have : 2 ^ (13 - level) ≤ 8192 := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 13 - level ≤ 13 by omega); simpa using this
  omega
theorem topNode_toNat (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).toNat = cache.toNat / 2 ^ (8 * (32 + 16 * topSlot leaf level)) % 2 ^ 128 := by
  have e : (List.ofFn fun i : Fin 16 =>
      (cacheDec cache).region ⟨(16 * topSlot leaf level + i.val) % 131040, Nat.mod_lt _ (by decide)⟩) =
      List.ofFn fun i : Fin 16 =>
        UInt8.ofNat (cache.toNat / 256 ^ (32 + 16 * topSlot leaf level) / 256 ^ i.val % 256) := by
    refine congrArg List.ofFn (funext fun i => ?_)
    show UInt8.ofNat (cache.toNat / 256 ^ (32 + (16 * topSlot leaf level + i.val) % 131040) % 256) = _
    rw [Nat.mod_eq_of_lt (show 16 * topSlot leaf level + i.val < 131040 by have := i.isLt; omega),
      ← Nat.add_assoc, pow_add, ← Nat.div_div_eq_div_mul]
  unfold topNode readDigest
  rw [e, readLE_ofFn_digits, BitVec.toNat_ofNat, show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num,
    Nat.mod_mod, show (256 : Nat) ^ (32 + 16 * topSlot leaf level) = 2 ^ (8 * (32 + 16 * topSlot leaf level)) by
      rw [pow_mul]; norm_num]
theorem topNode_lo (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).extractLsb' 0 64 = cache.extractLsb' (64 * (2 * topSlot leaf level + 4)) 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, topNode_toNat cache leaf level hq,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 64 ∣ 2 ^ 128)]
  congr 3; ring
theorem topNode_hi (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).extractLsb' 64 64 = cache.extractLsb' (64 * (2 * topSlot leaf level + 5)) 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, topNode_toNat cache leaf level hq,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3; ring
def TMW (X : Nat) : Prop :=
  X=PRIV+16 ∨ X=PRIV+24 ∨ (MOUT≤X ∧ X<MOUT+32) ∨ (SIG+3056≤X ∧ X<SIG+3248)
def tmRegs : List Reg := [.x6,.x7,.x10,.x11,.x12,.x20,.x22,.x23,.x24,.x28,.x29]
structure MInv (w0 : MachineState) (pre : List Digest) (w : MachineState) : Prop where
  pc : w.pc = if pre.length<12 then pcOf 1438 else pcOf 1482
  x22 : w.getReg .x22 = BitVec.ofNat 64 pre.length
  x24 : w.getReg .x24 = BitVec.ofNat 64 (SIG+3056+16*pre.length)
  x20 : w.getReg .x20 = BitVec.ofNat 64 (2^(12-pre.length))
  regs : RegsExcept w0 w tmRegs
  frame : Frame w0 w TMW
  out : DigsAt w (SIG+3056) pre
section masks
variable {sk : SecretKey} {cache : Bytes 131072} {w0 : MachineState} {leaf : Nat}
  (hb : Base sk cache w0) (hl : leaf<4096) (h14 : w0.getReg .x14=BitVec.ofNat 64 leaf)
include hb hl h14
theorem tp_mask_one {pre : List Digest} (hpl : pre.length<12) {w : MachineState}
    (hw : MInv w0 pre w) :
    TSim image sk w 44 51 1 1
      (mask pre.length (leaf/2^pre.length ^^^ 1) >>= fun m =>
        pure (topNode cache leaf pre.length ^^^ m))
      (fun d v => MInv w0 (pre++[d]) v) := by
  set lv := pre.length with hlv
  have g : ∀ r, r∉tmRegs → w.getReg r=w0.getReg r := fun r hr => hw.regs.get hr
  obtain ⟨hsib,hslot⟩ := topSlot_lt hl (show lv≤11 by omega)
  obtain ⟨t2,st2,t2pc,t2x10,t2x11,t2x12,t2x23,t2a,t2b,t2r,t2f⟩ :=
    blk1438_spec w (by rw [hw.pc, if_pos hpl]) leaf lv hl (by omega)
      (by rw [g _ (by decide),h14]) hw.x22
  have fr : ∀ X, X<2^64 → BaseA X → t2.getMem (BitVec.ofNat 64 X)=w0.getMem (BitVec.ofNat 64 X) :=
    fun X hX hba => (t2f.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; sg_omega)).trans
      (hw.frame.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; unfold TMW; sg_omega))
  have hq : hashInput t2=toQ (privateInput sk (.inl (header 13 0 0 lv ((leaf/2^lv ^^^ 1)/2)))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak,header_lo,header_hi,readWords_eight,
      fr PRIV (by decide) (by unfold BaseA; simp),fr (PRIV+8) (by decide) (by unfold BaseA; simp),t2a,t2b,
      fr (PRIV+32) (by decide) (by unfold BaseA; simp),fr (PRIV+40) (by decide) (by unfold BaseA; simp),
      fr (PRIV+48) (by decide) (by unfold BaseA; simp),fr (PRIV+56) (by decide) (by unfold BaseA; simp),
      hb.p0,hb.p8,hb.p32,hb.p40,hb.p48,hb.p56]
    rfl
  have hv : hashArgumentsValid t2=true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t2.getReg .x5=0 := by rw [t2r.get (by decide),g _ (by decide),hb.x5]
  refine (TSim.steps st2 (TSim.mask_bind (k:=25) (c:=25) (n:=0) (b:=0)
    (fetch_1456 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc=pcOf 1457 := by rw [pc_writeHash,t2pc,pcOf_add4]
  have hmo : DigAt (writeHash t2 a) (MOUT+16*((leaf/2^lv ^^^ 1)%2))
      (if (leaf/2^lv ^^^ 1)%2=0 then a.extractLsb' 0 128 else a.extractLsb' 128 128) := by
    have hmod := Nat.mod_lt (leaf/2^lv ^^^ 1) (by decide : 0<2)
    by_cases hz : (leaf/2^lv ^^^ 1)%2=0
    · simpa [hz] using DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
    · have ho : (leaf/2^lv ^^^ 1)%2=1 := by omega
      simpa [ho] using DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have rw2 : RegsExcept w (writeHash t2 a) [.x6,.x7,.x10,.x11,.x12,.x23,.x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hlo2 : 2≤2^(12-lv) := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 1≤12-lv by omega); simpa using this
  have hlo : 2^(12-lv)≤4096 := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 12-lv≤12 by omega); simpa using this
  obtain ⟨t3,st3,t3pc,t3a,t3b,t3x24,t3x20,t3x22,t3r,t3f⟩ :=
    blk1457_spec (writeHash t2 a) upc (leaf/2^lv ^^^ 1) (2^(12-lv)) lv
      (SIG+3056+16*pre.length) hlo2 hlo hsib (by omega)
      (by sg_omega) (by sg_omega) (by sg_omega)
      (by rw [getReg_writeHash]; exact t2x23)
      (by rw [rw2.get (by decide)]; exact hw.x20)
      (by rw [rw2.get (by decide)]; exact hw.x22)
      (by rw [rw2.get (by decide)]; exact hw.x24)
      (by rw [getReg_writeHash]; exact t2x12)
  have hst : 2*2^(12-lv)=2^(13-lv) := by
    rw [show 13-lv=(12-lv)+1 by omega,Nat.pow_succ]; ring
  have hslot' : REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))=REGION+8*(2*topSlot leaf lv) := by
    unfold topSlot; rw [hst]; ring
  have fsu := hw.frame.trans (t2f.trans hwf)
  have reg : ∀ k<16380, (writeHash t2 a).getMem (BitVec.ofNat 64 (REGION+8*k))=
      cache.extractLsb' (64*(k+4)) 64 := fun k hk => by
    rw [fsu.get (by sg_omega) (by unfold TMW; sg_omega)]; exact hb.region k hk
  refine TSim.pure_steps st3 ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append,List.length_singleton] using t3pc
  · rw [t3x22,List.length_append,List.length_singleton]
  · rw [t3x24,List.length_append,List.length_singleton]; congr 1
  · rw [t3x20,List.length_append,List.length_singleton,
      show 12-lv=(12-(pre.length+1))+1 by omega,Nat.pow_succ,Nat.mul_div_cancel _ (by norm_num)]
  · exact (hw.regs.trans (rw2.trans t3r)).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold TMW at h ⊢
    sg_omega
  · refine DigsAt.snoc (hw.out.frame ((t2f.trans hwf).trans t3f) (by sg_omega)
      (fun B h1 h2 h => by sg_omega)) ?_
    constructor
    · rw [t3a,hslot',reg _ (by omega),hmo.1,BitVec.extractLsb'_xor,topNode_lo cache leaf lv hslot]
    · rw [t3b,
        show REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))+8=REGION+8*(2*topSlot leaf lv+1) by
          rw [hslot']; ring,
        reg _ (by omega),hmo.2,BitVec.extractLsb'_xor,topNode_hi cache leaf lv hslot]
theorem tp_masks {w : MachineState} (hw : MInv w0 [] w) :
    TSim image sk w 528 612 12 12
      ((List.range 12).mapM fun level => mask level (leaf/2^level ^^^ 1) >>= fun m =>
        pure (topNode cache leaf level ^^^ m))
      (fun ds v => ds.length=12 ∧ MInv w0 ds v) := by
  refine (TSim.mapM_range 12 _ (fun _ => 44) (fun _ => 51) (fun _ => 1) (fun _ => 1) (MInv w0)
    (fun pre t hpl ht => tp_mask_one hb hl h14 hpl ht) hw).of_eq rfl ?_ ?_ ?_ ?_ <;> simp [sumTo_const]
end masks
end SigGolfCandidate.T3M.Sign.Packed
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open ClaudeWCT
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signTop topPath counterLimit buildLeaf
  nodeHash mask route height chainCount width maxDigit target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION
  LeafArgs LeafW leafRegs n4)
open SphincsSecurity (bytesLE bytesLE_length)
private theorem extractByte_zero_top (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
theorem signLayers_one (cache : Cache) (index : Nat) (root : WCT9.LayerMsg) :
    signLayersP leafFn cache index 1 root = (do
      let found ← WCT9.layerCounterSearch 0 (route index 0).2 (route index 0).1 root 0 (WCT9.searchLimit 0)
      let part ← signTop cache (route index 0).1 ((found.map Prod.snd).getD T3.dummyTop)
      pure (some [part])) := by
  simp only [signLayersP, Fin.ofNat_zero, if_true]
  try rfl
theorem route_0 {index : Nat} (h : index < 2 ^ 31) : route index 0 = (index / 2 ^ 19 % 4096, 0) := by
  show (index / 2 ^ 19 % 2 ^ 12, index / 2 ^ (19 + 12)) = _
  rw [Nat.div_eq_of_lt (by omega : index < 2 ^ (19 + 12))]
  rfl
def tl0 (leaf : Nat) (ds : List Nat) (dest : Nat) : LeafArgs :=
  ⟨0, 0, leaf, ds, true, DIGITS, SIG + 2240, dest, 447⟩
section top
variable {sk : SecretKey} {cache : Bytes 131072}
structure TopRegs (leaf : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x14 : s.getReg .x14 = BitVec.ofNat 64 leaf
  x26 : s.getReg .x26 = BitVec.ofNat 64 51
  x27 : s.getReg .x27 = BitVec.ofNat 64 51
theorem TopRegs.of {leaf : Nat} {s t : MachineState} {l : List Reg} (h : TopRegs leaf s) (hr : RegsExcept s t l)
    (hl : Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x14 ∉ l ∧ Reg.x26 ∉ l ∧ Reg.x27 ∉ l) : TopRegs leaf t :=
  ⟨by rw [hr.get hl.1, h.x8], by rw [hr.get hl.2.1, h.x9], by rw [hr.get hl.2.2.1, h.x14],
    by rw [hr.get hl.2.2.2.1, h.x26], by rw [hr.get hl.2.2.2.2, h.x27]⟩
theorem zdig_byte {s : MachineState} (hb : Base sk cache s) {i : Nat} (hi : i < 54) :
    s.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0 := by
  rw [getByte_eq_word s _ (by packed_sgo), hb.zero _ (by packed_sgo) (by unfold NeverW; packed_sgo), extractByte_zero_top]
  rfl
theorem frame_l0 {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (hW : ∀ A, W A → L0W A) :
    Frame s t L0W := h.mono (fun A _ hA => hW A hA)
theorem frame_l0_trans {s t u : MachineState} (h1 : Frame s t L0W) (h2 : Frame t u L0W) : Frame s u L0W :=
  (h1.trans h2).mono (fun A _ h => by rcases h with h | h <;> exact h)
theorem leafW_l0 {A : LeafArgs} (hlay : A.lay = 0)
    (hv : A.valp + 16 * 51 ≤ SIG ∨ (SIG + 2192 ≤ A.valp ∧ A.valp + 16 * 51 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.valp)
    (hd : A.dest + 16 ≤ SIG ∨ (SIG + 2192 ≤ A.dest ∧ A.dest + 16 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.dest) :
    ∀ X, (LeafW A X ∨ TopScr X) → L0W X := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hlay]; rfl
  intro X hX
  rcases hX with hX | hX
  swap
  · unfold TopScr at hX; unfold L0W; constructor <;> packed_sgo
  unfold LeafW at hX
  rw [hn, if_pos hlay] at hX
  unfold L0W
  constructor <;> packed_sgo
def KeepI (s t : MachineState) (lo hi : Nat) : Prop :=
  ∀ A, A < 2 ^ 64 → lo ≤ A → A < hi → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
theorem KeepI.of_frame {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {lo hi : Nat}
    (hW : ∀ A, lo ≤ A → A < hi → ¬ W A) : KeepI s t lo hi := fun A hA h1 h2 => h.get hA (hW A h1 h2)
theorem KeepI.trans {s t u : MachineState} {lo hi : Nat} (h1 : KeepI s t lo hi) (h2 : KeepI t u lo hi) :
    KeepI s u lo hi := fun A hA a b => (h2 A hA a b).trans (h1 A hA a b)
theorem KeepI.mono {s t : MachineState} {lo hi lo' hi' : Nat} (h : KeepI s t lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : KeepI s t lo' hi' := fun A hA a b => h A hA (by omega) (by omega)
theorem KeepI.digAt {s t : MachineState} {lo hi A : Nat} {d : Digest} (h : KeepI s t lo hi) (hd : DigAt s A d)
    (h1 : lo ≤ A) (h2 : A + 16 ≤ hi) (h3 : A + 16 ≤ 2 ^ 64) : DigAt t A d :=
  ⟨(h A (by omega) h1 (by omega)).trans hd.1, (h (A + 8) (by omega) (by omega) (by omega)).trans hd.2⟩
-- r3-lean-sign: legacy `l0Spec_of` (old BC top search, target 145) removed; it had no users.
end top
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
-- r3-lean-sign: legacy `counterSearchSpec`/`layers_checked`/`entry370`/`layers_from370` (old BC search) removed.
end
namespace SigGolfCandidate.T3M.Sign.SharedTopPath
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest Cache readDigest readLE mask header privateInput)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
open SigGolfCandidate.T3M.Sign.Packed
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure StateBase (sk : SecretKey) (cache : Bytes 131072) (t : MachineState)  : Prop where
  x5 : t.getReg .x5 = 0
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  region : ∀ k < 16380, t.getMem (BitVec.ofNat 64 (REGION + 8 * k)) = cache.extractLsb' (64 * (k + 4)) 64
  /-- (witness stack) the F pads `CHAIN+32/40` are not tracked: the top leaf's G chains (even `i ≤ 52`) write them. -/
  zero : ∀ A < 2 ^ 64, NeverW A → A ≠ CHAIN + 32 → A ≠ CHAIN + 40 → t.getMem (BitVec.ofNat 64 A) = 0
theorem StateBase.frame {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : StateBase sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → ¬ W A) : StateBase sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (hW A hA hb)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn h32 h40 => ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega),
      h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn), h.zero A hA hn h32 h40]

/-- `StateBase.frame` when the only base cells written are the untracked F pads `CHAIN+32/40`. -/
theorem StateBase.frame_pads {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : StateBase sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → W A → A = CHAIN + 32 ∨ A = CHAIN + 40) : StateBase sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → A ≠ CHAIN + 32 → A ≠ CHAIN + 40 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb h32 h40 => hf.get hA (fun hw => by rcases hW A hA hb hw with h' | h' <;> contradiction)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn h32 h40 => ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega)
      (by packed_sgo) (by packed_sgo), h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn) h32 h40,
      h.zero A hA hn h32 h40]

variable {im : Image} (hcode : SharedTopBlocks.Code im)
section masks
variable {sk : SecretKey} {cache : Bytes 131072} {w0 : MachineState} {leaf : Nat}
  (hb : StateBase sk cache w0) (hl : leaf<4096) (h14 : w0.getReg .x14=BitVec.ofNat 64 leaf)
include hcode hb hl h14
theorem tp_mask_one {pre : List Digest} (hpl : pre.length<12) {w : MachineState}
    (hw : MInv w0 pre w) :
    TSim im sk w 44 51 1 1
      (mask pre.length (leaf/2^pre.length ^^^ 1) >>= fun m =>
        pure (topNode cache leaf pre.length ^^^ m))
      (fun d v => MInv w0 (pre++[d]) v) := by
  set lv := pre.length with hlv
  have g : ∀ r, r∉tmRegs → w.getReg r=w0.getReg r := fun r hr => hw.regs.get hr
  obtain ⟨hsib,hslot⟩ := topSlot_lt hl (show lv≤11 by omega)
  obtain ⟨t2,st2,t2pc,t2x10,t2x11,t2x12,t2x23,t2a,t2b,t2r,t2f⟩ :=
    SharedTopBlocks.blk1438_spec hcode w (by rw [hw.pc, if_pos hpl]) leaf lv hl (by omega)
      (by rw [g _ (by decide),h14]) hw.x22
  have fr : ∀ X, X<2^64 → BaseA X → t2.getMem (BitVec.ofNat 64 X)=w0.getMem (BitVec.ofNat 64 X) :=
    fun X hX hba => (t2f.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; sg_omega)).trans
      (hw.frame.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; unfold TMW; sg_omega))
  have hq : hashInput t2=toQ (privateInput sk (.inl (header 13 0 0 lv ((leaf/2^lv ^^^ 1)/2)))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak,header_lo,header_hi,readWords_eight,
      fr PRIV (by decide) (by unfold BaseA; simp),fr (PRIV+8) (by decide) (by unfold BaseA; simp),t2a,t2b,
      fr (PRIV+32) (by decide) (by unfold BaseA; simp),fr (PRIV+40) (by decide) (by unfold BaseA; simp),
      fr (PRIV+48) (by decide) (by unfold BaseA; simp),fr (PRIV+56) (by decide) (by unfold BaseA; simp),
      hb.p0,hb.p8,hb.p32,hb.p40,hb.p48,hb.p56]
    rfl
  have hv : hashArgumentsValid t2=true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t2.getReg .x5=0 := by rw [t2r.get (by decide),g _ (by decide),hb.x5]
  refine (TSim.steps st2 (TSim.mask_bind (k:=25) (c:=25) (n:=0) (b:=0)
    (SharedTopBlocks.fetch_1456 hcode t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc=pcOf 1457 := by rw [pc_writeHash,t2pc,pcOf_add4]
  have hmo : DigAt (writeHash t2 a) (MOUT+16*((leaf/2^lv ^^^ 1)%2))
      (if (leaf/2^lv ^^^ 1)%2=0 then a.extractLsb' 0 128 else a.extractLsb' 128 128) := by
    have hmod := Nat.mod_lt (leaf/2^lv ^^^ 1) (by decide : 0<2)
    by_cases hz : (leaf/2^lv ^^^ 1)%2=0
    · simpa [hz] using DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
    · have ho : (leaf/2^lv ^^^ 1)%2=1 := by omega
      simpa [ho] using DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have rw2 : RegsExcept w (writeHash t2 a) [.x6,.x7,.x10,.x11,.x12,.x23,.x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hlo2 : 2≤2^(12-lv) := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 1≤12-lv by omega); simpa using this
  have hlo : 2^(12-lv)≤4096 := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 12-lv≤12 by omega); simpa using this
  obtain ⟨t3,st3,t3pc,t3a,t3b,t3x24,t3x20,t3x22,t3r,t3f⟩ :=
    SharedTopBlocks.blk1457_spec hcode (writeHash t2 a) upc (leaf/2^lv ^^^ 1) (2^(12-lv)) lv
      (SIG+3056+16*pre.length) hlo2 hlo hsib (by omega)
      (by sg_omega) (by sg_omega) (by sg_omega)
      (by rw [getReg_writeHash]; exact t2x23)
      (by rw [rw2.get (by decide)]; exact hw.x20)
      (by rw [rw2.get (by decide)]; exact hw.x22)
      (by rw [rw2.get (by decide)]; exact hw.x24)
      (by rw [getReg_writeHash]; exact t2x12)
  have hst : 2*2^(12-lv)=2^(13-lv) := by
    rw [show 13-lv=(12-lv)+1 by omega,Nat.pow_succ]; ring
  have hslot' : REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))=REGION+8*(2*topSlot leaf lv) := by
    unfold topSlot; rw [hst]; ring
  have fsu := hw.frame.trans (t2f.trans hwf)
  have reg : ∀ k<16380, (writeHash t2 a).getMem (BitVec.ofNat 64 (REGION+8*k))=
      cache.extractLsb' (64*(k+4)) 64 := fun k hk => by
    rw [fsu.get (by sg_omega) (by unfold TMW; sg_omega)]; exact hb.region k hk
  refine TSim.pure_steps st3 ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append,List.length_singleton] using t3pc
  · rw [t3x22,List.length_append,List.length_singleton]
  · rw [t3x24,List.length_append,List.length_singleton]; congr 1
  · rw [t3x20,List.length_append,List.length_singleton,
      show 12-lv=(12-(pre.length+1))+1 by omega,Nat.pow_succ,Nat.mul_div_cancel _ (by norm_num)]
  · exact (hw.regs.trans (rw2.trans t3r)).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold TMW at h ⊢
    sg_omega
  · refine DigsAt.snoc (hw.out.frame ((t2f.trans hwf).trans t3f) (by sg_omega)
      (fun B h1 h2 h => by sg_omega)) ?_
    constructor
    · rw [t3a,hslot',reg _ (by omega),hmo.1,BitVec.extractLsb'_xor,topNode_lo cache leaf lv hslot]
    · rw [t3b,
        show REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))+8=REGION+8*(2*topSlot leaf lv+1) by
          rw [hslot']; ring,
        reg _ (by omega),hmo.2,BitVec.extractLsb'_xor,topNode_hi cache leaf lv hslot]
theorem tp_masks {w : MachineState} (hw : MInv w0 [] w) :
    TSim im sk w 528 612 12 12
      ((List.range 12).mapM fun level => mask level (leaf/2^level ^^^ 1) >>= fun m =>
        pure (topNode cache leaf level ^^^ m))
      (fun ds v => ds.length=12 ∧ MInv w0 ds v) := by
  refine (TSim.mapM_range 12 _ (fun _ => 44) (fun _ => 51) (fun _ => 1) (fun _ => 1) (MInv w0)
    (fun pre t hpl ht => tp_mask_one hcode hb hl h14 hpl ht) hw).of_eq rfl ?_ ?_ ?_ ?_ <;> simp [sumTo_const]
end masks

end SigGolfCandidate.T3M.Sign.SharedTopPath

namespace SigGolfCandidate.T3M.Sign.SharedTopContinuation
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open ClaudeWCT
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signTop topPath counterLimit buildLeaf nodeHash mask route height chainCount width maxDigit target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION LeafArgs LeafW leafRegs n4)
open SigGolfCandidate.T3M.Sign.Packed SigGolfCandidate.T3M.Sign.Packed.Boundary
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} {sk : SecretKey} {cache : Bytes 131072}
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : SharedTopPath.StateBase sk cache s) (hlay : A.lay = 0) (hso : A.so = true)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 51)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 51, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 51, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 51 ≤ 2 ^ 24) (hdigW : ∀ i < 51, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hdigC : A.digp + 51 ≤ 0x201C0 ∨ 0x20210 ≤ A.digp)
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 51 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 51 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 51 ≤ A.dest)
    (hroute : A.tree * 2 ^ height A.lay + A.leaf < 2 ^ 31)
    (hleafHeight : A.leaf < 2 ^ height A.lay)
    (hsteps : ∀ i < A.n, A.e i ≤ 8) : LeafPreS sk s A := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hlay]; rfl
  have h4 : n4 A.lay = 51 := by rw [hlay]; rfl
  exact
    { x1 := h1
      x5 := hb.x5
      x8 := by rw [h8, hlay]; rfl
      x9 := h9
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [h26, hn]
      x27 := by rw [h27, h4]
      x31 := h31
      htree := htree
      hleaf := hleaf
      hroute := hroute
      hleafHeight := hleafHeight
      hsteps := hsteps
      p0 := hb.p0
      p8 := hb.p8
      p32 := hb.p32
      p40 := hb.p40
      p48 := hb.p48
      p56 := hb.p56
      z0 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp) (by packed_sgo) (by packed_sgo)
      z8 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp) (by packed_sgo) (by packed_sgo)
      hsl := fun h => absurd (h.symm.trans hso) (by decide)
      hdig := fun i hi => hdig i (by rw [hn] at hi; exact hi)
      hdigb := fun i hi => by rw [hlay]; exact hdigb i (by rw [hn] at hi; exact hi)
      hdigp := by rw [hn]; exact hdigp
      hdigW := fun i hi => hdigW i (by rw [hn] at hi; exact hi)
      hdigC := by rw [hn]; exact hdigC
      hv8 := hv8
      hv := by rw [hn]; exact hv
      hvs := by rw [hn]; exact hvs
      hd8 := hd8
      hd := hd
      hds := hds
      hdv := by rw [hn]; exact hdv }
theorem base_leaf {s t : MachineState} {A : LeafArgs} (hb : SharedTopPath.StateBase sk cache s) (hlay : A.lay = 0)
    (hf : Frame s t (fun X => LeafW A X ∨ TopScr X)) (hr : RegsExcept s t leafRegs)
    (hvB : A.valp + 16 * 51 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 51 ≤ REGION ∨ REGION + 131040 ≤ A.valp)
    (hdB : A.dest + 16 ≤ PRIV) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 51 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp)
    (hvT : A.valp + 16 * 51 ≤ 16691072) : SharedTopPath.StateBase sk cache t := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hlay]; rfl
  refine hb.frame_pads hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseA NeverW Search.TOP_DATA at hB
  rcases hW with hW | hW
  · unfold LeafW at hW
    rw [hn, if_pos hlay] at hW
    packed_sgo
  · unfold TopScr at hW
    packed_sgo
def topLeafC : Nat := 305000
def LeafSpec (im : Image) : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState),
    A.lay = 0 → A.so = true → A.tree = 0 → (∀ i < A.n, A.d i ≤ SigGolfCandidate.T3.maxDigit 0 i) →
    A.valp + 16*A.n ≤ 0x60000 → A.digp+A.n ≤ 0x60000 → A.dest+16 ≤ 0x60000 →
    LeafPreS sk s A → s.pc=pcOf (1013+27) →
    TBSim im sk s topLeafC (SigGolfCandidate.T3.buildLeafTop A.leaf A.digits A.so)
      (fun r t => t.pc=pcOf A.ret ∧ DigsAt t A.valp r.2 ∧ r.2.length=A.n ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ SigGolfCandidate.T3M.Sign.Packed.TopScr X))

def Post (s : MachineState) (p : Pieces) (t : MachineState) : Prop :=
  t.pc=pcOf 540 ∧ (∀ i<51,DigAt t (SIG+2240+16*i) (p.1.getD i 0)) ∧
    (∀ j<12,DigAt t (SIG+3056+16*j) (p.2.getD j 0)) ∧ Frame s t L0W ∧
    (∀ A, (A=0x66000 ∨ A=0x66008) → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))

theorem top_only (hcode : SharedTopBlocks.Code im) (hTop : LeafSpec im)
    (leaf : Nat) (hl : leaf<4096) (ds : List Nat) (u : MachineState) (upc : u.pc=pcOf 441)
    (hbu : SharedTopPath.StateBase sk cache u) (hregs : TopRegs leaf u)
    (h18 : u.getReg .x18=BitVec.ofNat 64 leaf) (hx25 : (u.getReg .x25).toNat≤201)
    (hdm : ∀ i<51,ds.getD i 0≤SigGolfCandidate.T3.maxDigit 0 i)
    (udig : ∀ i<51,u.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 (ds.getD i 0)) :
    TBSim im sk u (topLeafC+30006) (signTop (cacheDec cache) leaf ds) (Post u) := by
  have hd7 : ∀ i<51,ds.getD i 0≤7 := fun i hi =>
    (hdm i hi).trans (by unfold SigGolfCandidate.T3.maxDigit; split_ifs <;> omega)
  have hSIG : SIG=28672 := rfl
  set dest0 := (u.getReg .x25).toNat with hdest0
  obtain ⟨u1, su1, u1pc, u1x1, u1x31, u1x22, u1x23, u1r, u1f⟩ := SharedTopBlocks.blk441_spec hcode u upc
  have g1 : ∀ r, r ∉ [.x1, .x22, .x23, .x31] → u1.getReg r = u.getReg r := fun r hr => u1r.get hr
  have hbu1 : SharedTopPath.StateBase sk cache u1 := hbu.frame u1f u1r (by decide) (fun _ _ _ h => h)
  have tr1 : TopRegs leaf u1 :=
    ⟨by rw [g1 _ (by decide)]; exact hregs.x8, by rw [g1 _ (by decide)]; exact hregs.x9,
      by rw [g1 _ (by decide)]; exact hregs.x14, by rw [g1 _ (by decide)]; exact hregs.x26,
      by rw [g1 _ (by decide)]; exact hregs.x27⟩
  have hp0 : LeafPreS sk u1 (tl0 leaf ds dest0) :=
    leafPreS_of hbu1 rfl rfl u1x1 tr1.x8 tr1.x9 (by rw [g1 _ (by decide)]; exact h18) u1x22 u1x23
      (by rw [g1 _ (by decide)]; show u.getReg .x25 = BitVec.ofNat 64 (u.getReg .x25).toNat
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      tr1.x26 tr1.x27 u1x31 (by show 0 < 2 ^ 32; norm_num) (by show leaf < 2 ^ 32; omega)
      (fun i hi => by
        show u1.getByte (BitVec.ofNat 64 (DIGITS + i)) = _
        rw [u1f.getByte (by packed_sgo) (fun h => h)]; exact udig i hi)
      (fun i hi => ⟨by show ds.getD i 0 < 256; have := hd7 i hi; omega, fun h => by simp [tl0] at h⟩)
      (by show DIGITS + 51 ≤ 2 ^ 24; packed_sgo) (fun i hi => by unfold LeafW; simp only [tl0, LeafArgs.n, chainCount, Matrix.cons_val_zero, ↓reduceIte]; packed_sgo)
      (Or.inr (by show 0x20210 ≤ DIGITS; packed_sgo))
      (by show (SIG + 2240) % 8 = 0; packed_sgo) (by show SIG + 2240 + 16 * 51 ≤ 2 ^ 24; packed_sgo)
      (Or.inl (by show SIG + 2240 + 16 * 51 ≤ PRIV; packed_sgo)) (fun h => by simp [tl0] at h)
      (by show dest0 + 16 ≤ 2 ^ 24; omega) (Or.inl (by show dest0 + 16 ≤ PRIV; packed_sgo))
      (Or.inl (by show dest0 + 16 ≤ SIG + 2240; packed_sgo))
      (by change 0 * 2 ^ 12 + leaf < 2 ^ 31; omega)
      (by change leaf < 4096; omega)
      (fun i hi => by have := hd7 i hi; change ds.getD i 0 ≤ 8; omega)
  have hL0 := hTop sk (tl0 leaf ds dest0) u1 rfl rfl rfl hdm (by show SIG + 2240 + 16 * 51 ≤ 0x60000; packed_sgo)
    (by show DIGITS + 51 ≤ 0x60000; packed_sgo) (by show dest0 + 16 ≤ 0x60000; omega) hp0 u1pc
  try dsimp only
  rw [signTop]
  refine TBSim.mono (TBSim.steps su1 (TBSim.bind (W₂ := 30000) hL0 (fun r0 v0 hv0 => ?_)))
    (Nat.le_of_eq (by ring)) (fun _ _ h => h)
  obtain ⟨root0, values⟩ := r0
  obtain ⟨v0pc, v0vals, v0len, v0r, v0f⟩ := hv0
  have hbv0 : SharedTopPath.StateBase sk cache v0 := base_leaf hbu1 rfl v0f v0r (Or.inl (by show SIG + 2240 + 16 * 51 ≤ PRIV; packed_sgo))
    (Or.inl (by show SIG + 2240 + 16 * 51 ≤ REGION; packed_sgo)) (by show dest0 + 16 ≤ PRIV; packed_sgo)
    (Or.inl (by show dest0 + 16 ≤ ZDIG; packed_sgo)) (Or.inl (by show SIG + 2240 + 16 * 51 ≤ ZDIG; packed_sgo))
    (by show SIG + 2240 + 16 * 51 ≤ 16691072; packed_sgo)
  have trv0 : TopRegs leaf v0 := tr1.of v0r (by decide)
  have fv0 : Frame u v0 L0W := frame_l0_trans (frame_l0 u1f (fun _ h => h.elim))
    (frame_l0 v0f (leafW_l0 rfl (by simp only [tl0]; packed_sgo) (by simp only [tl0]; packed_sgo)))
  show TBSim im sk v0 30000 (topPath (cacheDec cache) leaf >>= fun path => pure (values,path)) (Post u)
  simp only [topPath, bind_assoc, pure_bind]
  obtain ⟨v1,s447,v1pc,v1r,v1f⟩ := SharedTopBlocks.blk447_spec hcode v0 v0pc
  obtain ⟨w,s1433,wpc,wx22,wx24,wx20,wr,wf⟩ := SharedTopBlocks.blk1433_spec hcode v1 v1pc
  have hbw : SharedTopPath.StateBase sk cache w := (hbv0.frame v1f v1r (by decide) (fun _ _ _ h => h)).frame wf wr
    (by decide) (fun _ _ _ h => h)
  have w14 : w.getReg .x14=BitVec.ofNat 64 leaf := by
    rw [wr.get (by decide),v1r.get (by decide),trv0.x14]
  have hm := SharedTopPath.tp_masks hcode hbw hl w14 (w:=w)
    ⟨wpc,wx22,by simpa using wx24,wx20,RegsExcept.refl _ _,Frame.refl _ _,DigsAt.nil _ _⟩
  refine TBSim.mono (TBSim.steps (s447.trans s1433)
    (TBSim.bind (W₂:=3) (TSim.toTBSim hm (by norm_num)) (fun path x hx => ?_)))
      (by omega) (fun _ _ h => h)
  obtain ⟨hlen,hx⟩ := hx
  obtain ⟨x1,s1482,x1pc,x1r,x1f⟩ := SharedTopBlocks.blk1482_spec hcode x (by simpa [hlen] using hx.pc)
  refine TBSim.mono (TBSim.pure_steps s1482 ?_) (by omega) (fun _ _ h => h)
  have fwx := hx.frame.trans x1f
  have keep : KeepI v0 x1 SIG (SIG+3056) :=
    ((KeepI.of_frame v1f (fun _ _ _ h => h)).trans
      (KeepI.of_frame wf (fun _ _ _ h => h))).trans
      (KeepI.of_frame fwx (fun A h1 h2 hA => by
        rcases hA with hA | hA
        · unfold TMW at hA; packed_sgo
        · exact hA))
  refine ⟨x1pc, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact keep.digAt (v0vals i (by rw [v0len]; exact hi)) (by omega) (by omega) (by packed_sgo)
  · intro j hj
    have hd := hx.out j (by rw [hlen]; exact hj)
    exact hd.frame x1f (by packed_sgo) (fun h => h) (fun h => h)
  · exact frame_l0_trans (frame_l0_trans (frame_l0_trans fv0
      (frame_l0 v1f (fun _ h => h.elim))) (frame_l0 wf (fun _ h => h.elim)))
      (frame_l0 fwx (fun A hA => by
        rcases hA with hA | hA
        · unfold TMW at hA; unfold L0W; constructor <;> packed_sgo
        · exact hA.elim))

  · intro A hA
    have ha : A < 2^64 := by rcases hA with rfl | rfl <;> decide
    have n0 : ¬ (LeafW (tl0 leaf ds dest0) A ∨ TopScr A) := by
      unfold LeafW TopScr tl0 LeafArgs.n chainCount
      simp only [Matrix.cons_val_zero, ↓reduceIte]
      rcases hA with rfl | rfl <;> packed_sgo
    have n1 : ¬ TMW A := by
      unfold TMW
      rcases hA with rfl | rfl <;> packed_sgo
    rw [x1f.get ha (fun h => h), hx.frame.get ha n1,
      wf.get ha (fun h => h), v1f.get ha (fun h => h),
      v0f.get ha n0, u1f.get ha (fun h => h)]

end SigGolfCandidate.T3M.Sign.SharedTopContinuation
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_TopLeafP ====
section

/-!
# Campaign T8D / img-v6 Phase T: the top-leaf seed routines of the sign image

* PRE (1554): `bne s0,zero,1053; jal ra,COEFGEN; j 1053` (reached from the leaf prologue's `j 1554`).
* COEFGEN (1559..1563 -> cgFam 24785..24793 -> loop 1569..1589 -> exit 1590..1595): the 16
  `privatePair 0 0 0 (31 f / 2 + j) 0` queries (`f = leaf / 4`, `j < 16`) of `SigGolfCandidate.T3.topCoefs leaf`,
  both halves copied to `TCOEF + 32 j` (buffer slot `k` at `TCOEF + 16 k`, `k < 32`); `tp/s8/a4` saved at `TSAVE`;
  `s3 := 0`; returns via `ra`. The family's 31 coefficients are the slots `f % 2 .. f % 2 + 30`.
* TOPSEED (1557): `jal ra,HORN; j 1084` (reached through `20746 beq s0 → 20769 j 1557` once per top chain).
* HORN (1597..1604 -> hnFam 24794..24806 -> 1610..1652): `familyEval coefs (topPoint leaf s3)` over the 31
  coefficients at `TCOEF + 16 (f % 2)` into `CHAIN + 48`, `a3..a6/s8/tp` saved at `TSAVE + 32`. Horner loop `HK`
  (1610): `a0` walks down the coefficients, `(a4, a5)` hold the accumulator; bit loop `HB` (1616..1629):
  `(a4, a5, a2)` hold `acc * 2^k`, `(a6, s8, tp)` hold `clmulSmall acc d k`, `t4 = d >> k` (`d < 2^8`);
  `HF` (1630..1641) folds once with 0x87 and adds the coefficient.
-/

namespace ClaudeWCT.W9.Machine.Sign.SharedTopSeed
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN)
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.W9.Machine.Sign.Gf ClaudeWCT.Arith
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Top coefficient buffer (32 x 16 bytes: the 16 pairs of a family; T51). -/
abbrev TCOEF : Nat := 0x61000
/-- Register save area of COEFGEN (`+0..+24`) and HORN (`+32..+80`). -/
abbrev TSAVE : Nat := 0x60000
/-- The scratch the top seed routines write outside the leaf write set. -/
def TScr (A : Nat) : Prop := TSAVE ≤ A ∧ A < TCOEF + 640

/-! ### Code -/

def cgHead : List (BitVec 32) := [0x60f37,0x4f3023,0x18f3423,0xef3823,0x2d91606f]
def cgFam : List (BitVec 32) := [0x61c37,0x295f13,0x1f00e93,0x3df0733,0x175713,0x2071713,0x176713,0xe93,0xd20e906f]
def cgCall : List (BitVec 32) := [0x20537,0xe53823,0x53c23,0x4000593,0x4050613,0x73]
def cgCopy : List (BitVec 32) := [0x4053203,0x4c3023,0x4853203,0x4c3423,0x5053203,0x4c3823,0x5853203,0x4c3c23,0x20c0c13,0x100f13,0x20f1f13,0x1e70733,0x1e8e93,0x1000f13,0xfbee98e3]
def cgExit : List (BitVec 32) := [0x60f37,0xf3203,0x8f3c03,0x10f3703,0x993,0x8067]
def hnEntry : List (BitVec 32) := [0x60f37,0x2df3023,0x2ef3423,0x2ff3823,0x30f3c23,0x58f3023,0x44f3423,0x2591606f]
def hnFam : List (BitVec 32) := [0x198693,0x397f13,0x6f1f13,0x1e686b3,0x713,0x793,0x295f13,0x1f7f13,0x4f1f13,0x615b7,0x1e585b3,0x1f058513,0xd90e906f]
def hnHK : List (BitVec 32) := [0xff050513,0x813,0xc13,0x213,0x613,0x68e93]
def hnHB : List (BitVec 32) := [0x1eff13,0xf0863]
def hnX : List (BitVec 32) := [0xe84833,0xfc4c33,0xc24233]
def hnHS : List (BitVec 32) := [0x3f7df13,0x161613,0x1e66633,0x3f75f13,0x179793,0x1e7e7b3,0x171713,0x1ede93,0xfc0e96e3]
def hnHF : List (BitVec 32) := [0x121f13,0x1e84833,0x221f13,0x1e84833,0x721f13,0x1e84833,0x484833,0x53f03,0x1e84733,0x853f03,0x1ec47b3,0xf8b512e3]
def hnExit : List (BitVec 32) := [0x20f37,0x1cef3823,0x1cff3c23,0x60f37,0x20f3683,0x28f3703,0x30f3783,0x38f3803,0x40f3c03,0x48f3203,0x8067]

structure Code (im : Image) : Prop where
  codeAt_1554 : CodeAt im (pcOf 1554) [0x820416e3]
  codeAt_1555 : CodeAt im (pcOf 1555) [0x10000ef]
  codeAt_1556 : CodeAt im (pcOf 1556) [0x825ff06f]
  codeAt_1557 : CodeAt im (pcOf 1557) [0xa0000ef]
  codeAt_1558 : CodeAt im (pcOf 1558) [0x899ff06f]
  codeAt_cgHead : CodeAt im (pcOf 1559) cgHead
  codeAt_cgFam : CodeAt im (pcOf 24785) cgFam
  codeAt_cgCall : CodeAt im (pcOf 1569) cgCall
  codeAt_cgCopy : CodeAt im (pcOf 1575) cgCopy
  codeAt_cgExit : CodeAt im (pcOf 1590) cgExit
  codeAt_hnEntry : CodeAt im (pcOf 1597) hnEntry
  codeAt_hnFam : CodeAt im (pcOf 24794) hnFam
  codeAt_hnHK : CodeAt im (pcOf 1610) hnHK
  codeAt_hnHB : CodeAt im (pcOf 1616) hnHB
  codeAt_hnX : CodeAt im (pcOf 1618) hnX
  codeAt_hnHS : CodeAt im (pcOf 1621) hnHS
  codeAt_hnHF : CodeAt im (pcOf 1630) hnHF
  codeAt_hnExit : CodeAt im (pcOf 1642) hnExit
variable {im : Image}

sym_block bPre := symRun { noAlias := true } [0x820416e3] (pcOf 1554) 100
sym_block bJal := symRun { noAlias := true } [0x10000ef] (pcOf 1555) 100
sym_block bJ1053 := symRun { noAlias := true } [0x825ff06f] (pcOf 1556) 100
sym_block bTsJal := symRun { noAlias := true } [0xa0000ef] (pcOf 1557) 100
sym_block bTsJ := symRun { noAlias := true } [0x899ff06f] (pcOf 1558) 100
sym_block bCgHead := symRun { noAlias := true } cgHead (pcOf 1559) 100
sym_block bCgFam := symRun { noAlias := true } cgFam (pcOf 24785) 100
sym_block bCgCall := symRun { noAlias := true } cgCall (pcOf 1569) 100
sym_block bCgCopy := symRun { noAlias := true } cgCopy (pcOf 1575) 100
sym_block bCgExit := symRun { noAlias := true } cgExit (pcOf 1590) 100
sym_block bEntry := symRun { noAlias := true } hnEntry (pcOf 1597) 100
sym_block bFam := symRun { noAlias := true } hnFam (pcOf 24794) 100
sym_block bHK := symRun { noAlias := true } hnHK (pcOf 1610) 100
sym_block bHB := symRun { noAlias := true } hnHB (pcOf 1616) 100
sym_block bX := symRun { noAlias := true } hnX (pcOf 1618) 100
sym_block bHS := symRun { noAlias := true } hnHS (pcOf 1621) 100
sym_block bHF := symRun { noAlias := true } hnHF (pcOf 1630) 100
sym_block bExit := symRun { noAlias := true } hnExit (pcOf 1642) 100

/-! ### Family arithmetic (img-v6 Phase T) -/

theorem famAnd3 (x : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x &&& 3#64 = BitVec.ofNat 64 (x % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, show (3#64).toNat = 2 ^ 2 - 1 from rfl, toNat_ofNat_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]
theorem famAnd1 (x : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, show (1#64).toNat = 1 from rfl, toNat_ofNat_lt (by omega),
    Nat.and_one_is_mod]

/-- The COEFGEN header of family `leaf / 4`: pair `31 f / 2`, slot 1. -/
theorem hdrFam_word (leaf : Nat) (hl : leaf < 4096) :
    ((BitVec.ofNat 64 leaf >>> 2 * 31#64) >>> 1 <<< 32 ||| 1#64) =
      BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + 0)) := by
  rw [ofNat_shr leaf 2 (by omega)]
  have e1 : BitVec.ofNat 64 (leaf / 2 ^ 2) * 31#64 = BitVec.ofNat 64 (31 * (leaf / 4)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [e1, ofNat_shr _ 1 (by omega), ofNat_shl, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
    ofNat_or_add 1 _ 32 (by norm_num)]
  congr 1; omega

theorem topPoint_word (leaf i : Nat) (hl : leaf < 4096) (hi : i < 64) :
    BitVec.ofNat 64 i + 1#64 + (BitVec.ofNat 64 leaf &&& 3#64) <<< 6 =
      BitVec.ofNat 64 (SigGolfCandidate.T3.topPoint leaf i) := by
  rw [famAnd3 leaf (by omega), ofNat_shl, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat,
    ofNat_add_ofNat]
  unfold SigGolfCandidate.T3.topPoint; congr 1; omega

theorem famOff_word (leaf : Nat) (hl : leaf < 4096) :
    (BitVec.ofNat 64 leaf >>> 2 &&& 1#64) <<< 4 = BitVec.ofNat 64 (16 * (leaf / 4 % 2)) := by
  rw [ofNat_shr leaf 2 (by omega), famAnd1 _ (by omega), ofNat_shl]
  congr 1; omega

theorem cgHead5_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1559) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 24785 ∧
      t.getMem (BitVec.ofNat 64 TSAVE) = s.getReg .x4 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 8)) = s.getReg .x24 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 16)) = s.getReg .x14 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => TSAVE ≤ A ∧ A < TSAVE + 24) := by
  refine ⟨_, symRun_sound bCgHead (hcode.codeAt_cgHead) s hpc (by simp [bCgHead.res, rv_simp]), ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [bCgHead.res, E.eval]
  · simp only [Result.toState_getMem, bCgHead.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bCgHead.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bCgHead.res]; t3n [TSAVE]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgHead.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TSAVE] at hn
    simp only [Result.toState_getMem, bCgHead.res]
    t3n []
    split_ifs <;> first | rfl | omega

theorem cgFam_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 24785) (leaf : Nat) (hl : leaf < 4096)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 9 12 t ∧ t.pc = pcOf 1569 ∧ t.getReg .x24 = BitVec.ofNat 64 TCOEF ∧
      t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + 0)) ∧ t.getReg .x29 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x14, .x24, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bCgFam (hcode.codeAt_cgFam) s hpc (by simp [bCgFam.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bCgFam.res, E.eval]
  · simp only [Result.toState_getReg, bCgFam.res]; t3n [TCOEF]
  · simp only [Result.toState_getReg, bCgFam.res]; simp only [rv_simp, h18]
    rw [show ((2#64 : BitVec 64).toNat % 64) = 2 from rfl, show ((1#64 : BitVec 64).toNat % 64) = 1 from rfl,
      show ((32#64 : BitVec 64).toNat % 64) = 32 from rfl, hdrFam_word leaf hl]
  · simp [bCgFam.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgFam.res, rv_simp] <;> rfl
  · intro A _ _; simp [bCgFam.res, rv_simp]

theorem entry8_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1597) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf 24794 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 32)) = s.getReg .x13 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 40)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 48)) = s.getReg .x15 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 56)) = s.getReg .x16 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 64)) = s.getReg .x24 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 72)) = s.getReg .x4 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => TSAVE + 32 ≤ A ∧ A < TSAVE + 80) := by
  refine ⟨_, symRun_sound bEntry (hcode.codeAt_hnEntry) s hpc (by simp [bEntry.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [bEntry.res, E.eval]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · intro r hr; simp at hr; cases r <;> simp_all [bEntry.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TSAVE] at hn
    simp only [Result.toState_getMem, bEntry.res]
    t3n []
    split_ifs <;> first | rfl | omega

theorem hnFam_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 24794) (leaf i : Nat) (hl : leaf < 4096)
    (hi : i < 64) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 1610 ∧
      t.getReg .x13 = BitVec.ofNat 64 (SigGolfCandidate.T3.topPoint leaf i) ∧
      t.getReg .x14 = 0 ∧ t.getReg .x15 = 0 ∧
      t.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * (leaf / 4 % 2 + 31)) ∧
      t.getReg .x11 = BitVec.ofNat 64 (TCOEF + 16 * (leaf / 4 % 2)) ∧
      RegsExcept s t [.x10, .x11, .x13, .x14, .x15, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bFam (hcode.codeAt_hnFam) s hpc (by simp [bFam.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [bFam.res, E.eval]
  · simp only [Result.toState_getReg, bFam.res]; simp only [rv_simp, h18, h19]
    rw [show ((6#64 : BitVec 64).toNat % 64) = 6 from rfl, topPoint_word leaf i hl hi]
  · simp [bFam.res, rv_simp]
  · simp [bFam.res, rv_simp]
  · simp only [Result.toState_getReg, bFam.res]; simp only [rv_simp, h18]
    rw [show ((2#64 : BitVec 64).toNat % 64) = 2 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
      famOff_word leaf hl, show (397808#64 : BitVec 64) = BitVec.ofNat 64 397808 from rfl, ofNat_add_ofNat]
    unfold TCOEF; congr 1; omega
  · simp only [Result.toState_getReg, bFam.res]; simp only [rv_simp, h18]
    rw [show ((2#64 : BitVec 64).toNat % 64) = 2 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
      famOff_word leaf hl, show (397312#64 : BitVec 64) = BitVec.ofNat 64 397312 from rfl, ofNat_add_ofNat]
    unfold TCOEF; congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [bFam.res, rv_simp] <;> rfl
  · intro A _ _; simp [bFam.res, rv_simp]

/-! ### HORN pieces -/

/-- The registers HORN's entry changes (the saved ones are restored at the exit). -/
def entryRegs : List Reg := [.x10, .x11, .x13, .x14, .x15, .x30]
def SaveW (A : Nat) : Prop := TSAVE + 32 ≤ A ∧ A < TSAVE + 80

theorem entry_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1597) (leaf i : Nat) (hl : leaf < 4096)
    (hi : i < 64) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 21 21 t ∧ t.pc = pcOf 1610 ∧
      t.getReg .x13 = BitVec.ofNat 64 (SigGolfCandidate.T3.topPoint leaf i) ∧
      t.getReg .x14 = 0 ∧ t.getReg .x15 = 0 ∧ t.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * (leaf / 4 % 2 + 31)) ∧
      t.getReg .x11 = BitVec.ofNat 64 (TCOEF + 16 * (leaf / 4 % 2)) ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 32)) = s.getReg .x13 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 40)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 48)) = s.getReg .x15 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 56)) = s.getReg .x16 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 64)) = s.getReg .x24 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 72)) = s.getReg .x4 ∧
      RegsExcept s t entryRegs ∧ Frame s t SaveW := by
  obtain ⟨t1, s1, p1, m32, m40, m48, m56, m64, m72, r1, f1⟩ := entry8_spec hcode s hpc
  obtain ⟨t, s2, p2, x13, x14, x15, x10, x11, r2, f2⟩ := hnFam_spec hcode t1 p1 leaf i hl hi
    (by rw [r1.get (by decide)]; exact h18) (by rw [r1.get (by decide)]; exact h19)
  refine ⟨t, s1.trans s2, p2, x13, x14, x15, x10, x11, by rw [f2.get (by decide) id, m32],
    by rw [f2.get (by decide) id, m40], by rw [f2.get (by decide) id, m48], by rw [f2.get (by decide) id, m56],
    by rw [f2.get (by decide) id, m64], by rw [f2.get (by decide) id, m72], (r1.trans r2).mono (by simp [entryRegs]),
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩

/-- Registers the Horner loop changes. -/
def loopRegs : List Reg := [.x4, .x10, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

theorem hk_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1610) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 1616 ∧
      t.getReg .x10 = s.getReg .x10 - 16#64 ∧ t.getReg .x16 = 0 ∧ t.getReg .x24 = 0 ∧
      t.getReg .x4 = 0 ∧ t.getReg .x12 = 0 ∧ t.getReg .x29 = s.getReg .x13 ∧
      RegsExcept s t [.x4, .x10, .x12, .x16, .x24, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHK (hcode.codeAt_hnHK) s hpc (by simp [bHK.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bHK.res, E.eval]
  · simp only [Result.toState_getReg, bHK.res]; t3n []
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bHK.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHK.res, rv_simp]

theorem hb_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1616) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x29 &&& 1#64 = 0#64 then pcOf 1621 else pcOf 1618) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHB (hcode.codeAt_hnHB) s hpc (by simp [bHB.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bHB.res, E.eval, CmpOp.eval, BinOp.eval]
    split_ifs <;> simp_all
  · intro r hr; simp at hr; cases r <;> simp_all [bHB.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHB.res, rv_simp]

theorem x_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1618) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1621 ∧ t.getReg .x16 = s.getReg .x16 ^^^ s.getReg .x14 ∧
      t.getReg .x24 = s.getReg .x24 ^^^ s.getReg .x15 ∧ t.getReg .x4 = s.getReg .x4 ^^^ s.getReg .x12 ∧
      RegsExcept s t [.x4, .x16, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bX (hcode.codeAt_hnX) s hpc (by simp [bX.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bX.res, E.eval]
  · simp [bX.res, rv_simp]
  · simp [bX.res, rv_simp]
  · simp [bX.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bX.res, rv_simp] <;> rfl
  · intro A _ _; simp [bX.res, rv_simp]

theorem hs_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1621) :
    ∃ t, Steps im s 9 9 t ∧
      t.pc = (if s.getReg .x29 >>> 1 = 0#64 then pcOf 1630 else pcOf 1616) ∧
      t.getReg .x14 = s.getReg .x14 <<< 1 ∧
      t.getReg .x15 = (s.getReg .x15 <<< 1) ||| (s.getReg .x14 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x15 >>> 63) ∧
      t.getReg .x29 = s.getReg .x29 >>> 1 ∧
      RegsExcept s t [.x12, .x14, .x15, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHS (hcode.codeAt_hnHS) s hpc (by simp [bHS.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bHS.res, E.eval, CmpOp.eval, BinOp.eval]
    split_ifs <;> simp_all
  · simp [bHS.res, rv_simp]
  · simp [bHS.res, rv_simp]
  · simp [bHS.res, rv_simp]
  · simp [bHS.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bHS.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHS.res, rv_simp]

theorem hf_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1630) {A : Nat}
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ 2 ^ 24) :
    ∃ t, Steps im s 12 12 t ∧
      t.pc = (if s.getReg .x10 = s.getReg .x11 then pcOf 1642 else pcOf 1610) ∧
      t.getReg .x14 = foldLo (s.getReg .x16) (s.getReg .x4) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x15 = s.getReg .x24 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t [.x14, .x15, .x16, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHF (hcode.codeAt_hnHF) s hpc (by simp [bHF.res, rv_simp, h10]; t3n []; omega),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bHF.res, E.eval, CmpOp.eval, BinOp.eval]
    split_ifs <;> simp_all
  · simp only [Result.toState_getReg, bHF.res]; simp only [rv_simp, h10, foldLo]; t3n []
  · simp only [Result.toState_getReg, bHF.res]; simp only [rv_simp, h10]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bHF.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHF.res, rv_simp]

theorem exit_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1642) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getReg .x15 ∧
      t.getReg .x13 = s.getMem (BitVec.ofNat 64 (TSAVE + 32)) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 (TSAVE + 40)) ∧
      t.getReg .x15 = s.getMem (BitVec.ofNat 64 (TSAVE + 48)) ∧
      t.getReg .x16 = s.getMem (BitVec.ofNat 64 (TSAVE + 56)) ∧
      t.getReg .x24 = s.getMem (BitVec.ofNat 64 (TSAVE + 64)) ∧
      t.getReg .x4 = s.getMem (BitVec.ofNat 64 (TSAVE + 72)) ∧
      RegsExcept s t [.x4, .x13, .x14, .x15, .x16, .x24, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  refine ⟨_, symRun_sound bExit (hcode.codeAt_hnExit) s hpc (by simp [bExit.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [bExit.res, E.eval, BinOp.eval]
  · simp only [Result.toState_getMem, bExit.res]; t3n [CHAIN]
  · simp only [Result.toState_getMem, bExit.res]; t3n [CHAIN]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · intro r hr; simp at hr; cases r <;> simp_all [bExit.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, bExit.res]
    t3n []
    split_ifs <;> first | rfl | omega

/-! ### The Horner loop -/

def hbRegsT : List Reg := [.x4, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

structure HbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1616
  sh : lim3 (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d k
  dd : t.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t hbRegsT
  frame : Frame t0 t (fun _ => False)

structure HfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1630
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d 10
  regs : RegsExcept t0 t hbRegsT
  frame : Frame t0 t (fun _ => False)

theorem and1_ofNat (x : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, show (1#64).toNat = 1 from rfl, toNat_ofNat_lt (by omega),
    Nat.and_one_is_mod]

theorem lim3_ite' (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 ^^^ x0 else a0) (if b then a1 ^^^ x1 else a1) (if b then a2 ^^^ x2 else a2) =
      if b then lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 else lim3 a0 a1 a2 := by
  cases b
  · rfl
  · simp only [if_true]; exact lim3_xor ..

/-- One bit iteration (`HB`, `X` if the bit is set, `HS`): at most 14 cycles. -/
theorem bit_step (hcode : Code im) {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) {k : Nat} (hk : k ≤ 9)
    {t : MachineState} (ht : HbSt t0 d a k t) :
    ∃ u m, Steps im t m m u ∧ m ≤ 14 ∧
      u.pc = (if d / 2 ^ (k + 1) = 0 then pcOf 1630 else pcOf 1616) ∧
      lim3 (u.getReg .x14) (u.getReg .x15) (u.getReg .x12) = a * 2 ^ (k + 1) ∧
      lim3 (u.getReg .x16) (u.getReg .x24) (u.getReg .x4) = clmulSmall a d (k + 1) ∧
      u.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) ∧
      RegsExcept t0 u hbRegsT ∧ Frame t0 u (fun _ => False) := by
  have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk
  have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
    have := lim3_lt (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) (n := 9) (by
      rw [ht.sh, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
    omega
  have hshr : t.getReg .x29 >>> 1 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
    rw [ht.dd, ofNat_shr _ _ hdk, Nat.div_div_eq_div_mul, pow_one, ← Nat.pow_succ]
  have hz : (t.getReg .x29 >>> 1 = 0#64) ↔ d / 2 ^ (k + 1) = 0 := by
    rw [hshr, show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      ofNat_inj (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num)]
  -- the bit
  obtain ⟨t1, s1, p1, r1, f1⟩ := hb_spec hcode t ht.pc
  have hand : t.getReg .x29 &&& 1#64 = BitVec.ofNat 64 (d / 2 ^ k % 2) := by rw [ht.dd]; exact and1_ofNat _ hdk
  -- `X` when the bit is set
  obtain ⟨t2, m2, s2, hm2, p2, x16, x24, x4, r2, f2⟩ : ∃ t2 m2, Steps im t1 m2 m2 t2 ∧ m2 ≤ 3 ∧
      t2.pc = pcOf 1621 ∧
      t2.getReg .x16 = (if d.testBit k then t.getReg .x16 ^^^ t.getReg .x14 else t.getReg .x16) ∧
      t2.getReg .x24 = (if d.testBit k then t.getReg .x24 ^^^ t.getReg .x15 else t.getReg .x24) ∧
      t2.getReg .x4 = (if d.testBit k then t.getReg .x4 ^^^ t.getReg .x12 else t.getReg .x4) ∧
      RegsExcept t t2 [.x30, .x4, .x16, .x24] ∧ Frame t t2 (fun _ => False) := by
    rw [hand] at p1
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h
    · rw [h] at p1
      rw [if_pos rfl] at p1
      simp only [h, show ¬ (0 = 1) by omega, decide_false, Bool.false_eq_true, if_false]
      exact ⟨t1, 0, Steps.refl _, by omega, p1, r1.get (by decide), r1.get (by decide), r1.get (by decide),
        r1.mono (by simp), f1⟩
    · rw [h] at p1
      rw [if_neg (by decide)] at p1
      simp only [h, decide_true, if_true]
      obtain ⟨t2, s2, p2, a16, a24, a4, r2, f2⟩ := x_spec hcode t1 p1
      refine ⟨t2, 3, s2, le_rfl, p2, ?_, ?_, ?_, (r1.trans r2).mono (by simp), (f1.trans f2).mono (by simp)⟩
      · rw [a16, r1.get (by decide), r1.get (by decide)]
      · rw [a24, r1.get (by decide), r1.get (by decide)]
      · rw [a4, r1.get (by decide), r1.get (by decide)]
  have g : ∀ r, r ∉ [Reg.x30, .x4, .x16, .x24] → t2.getReg r = t.getReg r := fun r hr => r2.get hr
  obtain ⟨u, s3, p3, u14, u15, u12, u29, r3, f3⟩ := hs_spec hcode t2 p2
  refine ⟨u, _, s1.trans (s2.trans s3), by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3, g _ (by decide)]
    by_cases h0 : d / 2 ^ (k + 1) = 0
    · rw [if_pos (hz.mpr h0), if_pos h0]
    · rw [if_neg (fun h => h0 (hz.mp h)), if_neg h0]
  · rw [u14, u15, u12, g _ (by decide), g _ (by decide), g _ (by decide), lim3_shl1 _ _ _ hlt12, ht.sh,
      Nat.pow_succ]
    ring
  · rw [r3.get (by decide), r3.get (by decide), r3.get (by decide), x16, x24, x4, lim3_ite', ht.pr, ht.sh]
    rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
  · rw [u29, g _ (by decide), hshr]
  · exact ((ht.regs.trans r2).trans r3).mono (by simp [hbRegsT])
  · exact ((ht.frame.trans f2).trans f3).mono (fun _ _ h => by simp_all)

theorem hb_loop (hcode : Code im) {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 8) :
    ∀ n k, k + n = 8 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, HbSt t0 d a k t →
      ∃ u m, Steps im t m m u ∧ m ≤ 14 * n ∧ HfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 8 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    obtain ⟨u, m, su, hm, upc, ush, upr, udd, ur, uf⟩ := bit_step hcode ha (lt_of_lt_of_le hd (by norm_num)) (by omega) ht
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      refine ⟨u, m, su, by omega, ⟨by rw [upc, if_pos hz], ?_, ur, uf⟩⟩
      rw [upr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      obtain ⟨v, m', sv, hm', hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u
        ⟨by rw [upc, if_neg hz], ush, upr, udd, ur, uf⟩
      exact ⟨v, _, su.trans sv, by omega, hv⟩

/-- The 31 family coefficients of the buffer, from slot `b` (`b = f % 2`). -/
def CoefAtT (t : MachineState) (b : Nat) (coefs : List Digest) : Prop :=
  ∀ k < 31, DigAt t (TCOEF + 16 * (b + k)) (coefs.getD k 0)

theorem CoefAtT.frame {s t : MachineState} {b : Nat} {coefs : List Digest} {W : Nat → Prop} (h : CoefAtT s b coefs)
    (hb : b ≤ 1) (hf : Frame s t W) (hW : ∀ A, TCOEF ≤ A → A < TCOEF + 640 → ¬ W A) : CoefAtT t b coefs :=
  fun k hk => (h k hk).frame hf (by unfold TCOEF; omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

structure HkSt (s0 : MachineState) (d b : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1610
  x13 : t.getReg .x13 = BitVec.ofNat 64 d
  x10 : t.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * (b + m))
  x11 : t.getReg .x11 = BitVec.ofNat 64 (TCOEF + 16 * b)
  acc : lim2 (t.getReg .x14) (t.getReg .x15) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t loopRegs
  frame : Frame s0 t (fun _ => False)

/-- Cycle bound of one Horner step (HK, at most eight bit iterations (`d < 2^8`), HF). -/
def hstepC : Nat := 6 + 14 * 8 + 12

theorem lim3_zero_hi' (a b : BitVec 64) : lim3 a b 0 = lim2 a b := by
  unfold lim3 lim2; simp

theorem familyEval_drop' (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, ClaudeWCT.Arith.familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coef_limbsT {s0 u : MachineState} {b : Nat} {coefs : List Digest} (hcoef : CoefAtT s0 b coefs) (hb : b ≤ 1)
    (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < 31) :
    lim2 (u.getMem (BitVec.ofNat 64 (TCOEF + 16 * (b + m))))
      (u.getMem (BitVec.ofNat 64 (TCOEF + 16 * (b + m) + 8))) = (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by unfold TCOEF; omega) id, hf.get (by unfold TCOEF; omega) id, h.1, h.2, lim2_toNat]

theorem horner_step (hcode : Code im) {s0 : MachineState} {d b : Nat} {coefs : List Digest} (hd : d < 2 ^ 8)
    (hb : b ≤ 1) (hcoef : CoefAtT s0 b coefs) (hlen : coefs.length = 31)
    {m : Nat} (hm : m < 31) {t : MachineState} (ht : HkSt s0 d b coefs (m + 1) t) :
    ∃ u n, Steps im t n n u ∧ n ≤ hstepC ∧
      u.pc = (if m = 0 then pcOf 1642 else pcOf 1610) ∧
      u.getReg .x13 = BitVec.ofNat 64 d ∧ u.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * (b + m)) ∧
      u.getReg .x11 = BitVec.ofNat 64 (TCOEF + 16 * b) ∧
      lim2 (u.getReg .x14) (u.getReg .x15) = (familyEval (coefs.drop m) d).toNat ∧
      RegsExcept s0 u loopRegs ∧ Frame s0 u (fun _ => False) := by
  obtain ⟨t1, s1, p1, x10, x16, x24, x4, x12, x29, r1, f1⟩ := hk_spec hcode t ht.pc
  have h10 : t1.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * (b + m)) := by
    rw [x10, ht.x10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    unfold TCOEF; omega
  have ha := (familyEval (coefs.drop (m + 1)) d).isLt
  have h0 : HbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi', r1.get (by decide), r1.get (by decide), ht.acc]; simp
    · rw [x16, x24, x4]; unfold lim3; simp [clmulSmall]
    · rw [x29, ht.x13]; simp
  obtain ⟨u, n, su, hn, hu⟩ := hb_loop hcode ha hd 8 0 (by norm_num) (Or.inl rfl) t1 h0
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * (b + m)) := by rw [hu.regs.get (by decide), h10]
  have u11 : u.getReg .x11 = BitVec.ofNat 64 (TCOEF + 16 * b) := by
    rw [hu.regs.get (by decide), r1.get (by decide), ht.x11]
  obtain ⟨v, sv, vpc, v14, v15, vr, vf⟩ := hf_spec hcode u hu.pc u10 (by unfold TCOEF; omega) (by unfold TCOEF; omega)
  have hf0 : Frame s0 u (fun _ => False) := ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simp_all)
  have hl := horner_limbs hu.pr (coef_limbsT hcoef hb hf0 hm)
  rw [← familyEval_drop' coefs m (by omega)] at hl
  refine ⟨v, _, (s1.trans su).trans sv, by unfold hstepC; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vpc, u10, u11]
    by_cases hm0 : m = 0
    · subst hm0; simp
    · rw [if_neg hm0, if_neg]
      rw [ofNat_inj (by unfold TCOEF; omega) (by unfold TCOEF; omega)]; omega
  · rw [vr.get (by decide), hu.regs.get (by decide), r1.get (by decide), ht.x13]
  · rw [vr.get (by decide), u10]
  · rw [vr.get (by decide), u11]
  · rw [v14, v15]; exact hl
  · exact (((ht.regs.trans r1).trans hu.regs).trans vr).mono (by simp [loopRegs, hbRegsT])
  · exact (hf0.trans vf).mono (fun _ _ h => by simp_all)

theorem horner_loop (hcode : Code im) {s0 : MachineState} {d b : Nat} {coefs : List Digest} (hd : d < 2 ^ 8)
    (hb : b ≤ 1) (hcoef : CoefAtT s0 b coefs) (hlen : coefs.length = 31) :
    ∀ m, m < 31 → ∀ t, HkSt s0 d b coefs (m + 1) t →
      ∃ u n, Steps im t n n u ∧ n ≤ hstepC * (m + 1) ∧ u.pc = pcOf 1642 ∧
        lim2 (u.getReg .x14) (u.getReg .x15) = (familyEval coefs d).toNat ∧
        RegsExcept s0 u loopRegs ∧ Frame s0 u (fun _ => False) := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    obtain ⟨u, n, su, hn, upc, -, -, -, uacc, ur, uf⟩ := horner_step hcode hd hb hcoef hlen (by norm_num) ht
    exact ⟨u, n, su, by omega, by rw [upc, if_pos rfl], by simpa using uacc, ur, uf⟩
  | succ m ih =>
    intro hm t ht
    obtain ⟨u, n, su, hn, upc, u13, u10, u11, uacc, ur, uf⟩ := horner_step hcode hd hb hcoef hlen hm ht
    rw [if_neg (by omega)] at upc
    obtain ⟨v, n', sv, hn', vpc, vacc, vr, vf⟩ := ih (by omega) u ⟨upc, u13, u10, u11, uacc, ur, uf⟩
    exact ⟨v, _, su.trans sv, by unfold hstepC at *; omega, vpc, vacc, vr, vf⟩

/-- Cycle bound of HORN (entry 8 + family setup 13, 31 Horner steps, exit 11). -/
def hornCT : Nat := 21 + hstepC * 31 + 11

/-- HORN: `familyEval coefs (topPoint leaf i)` into `CHAIN + 48`; `a3..a6, s8, tp` restored. -/
theorem horn_run (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1597) {leaf i : Nat} (hl : leaf < 4096)
    (hi : i < 51) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    {coefs : List Digest} (hlen : coefs.length = 31) (hcoef : CoefAtT s (leaf / 4 % 2) coefs) :
    ∃ u n, Steps im s n n u ∧ n ≤ hornCT ∧ u.pc = s.getReg .x1 &&& ~~~1#64 ∧
      DigAt u (CHAIN + 48) (familyEval coefs (SigGolfCandidate.T3.topPoint leaf i)) ∧
      RegsExcept s u [.x10, .x11, .x12, .x29, .x30] ∧
      Frame s u (fun A => SaveW A ∨ A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  obtain ⟨t, st, tpc, t13, t14, t15, t10, t11, m32, m40, m48, m56, m64, m72, tr, tf⟩ :=
    entry_spec hcode s hpc leaf i hl (by omega) h18 h19
  have hb : leaf / 4 % 2 ≤ 1 := by omega
  have hd : SigGolfCandidate.T3.topPoint leaf i < 2 ^ 8 := by unfold SigGolfCandidate.T3.topPoint; omega
  have hc : CoefAtT t (leaf / 4 % 2) coefs :=
    hcoef.frame hb tf (fun A h1 h2 h => by unfold SaveW TSAVE at h; unfold TCOEF at h1; omega)
  have ht : HkSt t (SigGolfCandidate.T3.topPoint leaf i) (leaf / 4 % 2) coefs (30 + 1) t := by
    refine ⟨tpc, t13, t10, t11, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    rw [t14, t15, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, n, su, hn, upc, uacc, ur, uf⟩ := horner_loop hcode hd hb hc hlen 30 (by norm_num) t ht
  obtain ⟨v, sv, vpc, v48, v56, v13, v14, v15, v16, v24, v4, vr, vf⟩ := exit_spec hcode u upc
  obtain ⟨l0, l1⟩ := limbs_of_lim2 uacc
  have keep : ∀ A, SaveW A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA => uf.get (by unfold SaveW TSAVE at hA; omega) id
  refine ⟨v, _, (st.trans su).trans sv, by unfold hornCT; omega, ?_, ⟨by rw [v48, l0], by rw [v56, ← l1]⟩, ?_, ?_⟩
  · rw [vpc, ur.get (by decide), tr.get (by decide)]
  · intro r hr
    by_cases h13 : r = .x13
    · subst h13; rw [v13, keep _ (by unfold SaveW; omega), m32]
    by_cases h14 : r = .x14
    · subst h14; rw [v14, keep _ (by unfold SaveW; omega), m40]
    by_cases h15 : r = .x15
    · subst h15; rw [v15, keep _ (by unfold SaveW; omega), m48]
    by_cases h16 : r = .x16
    · subst h16; rw [v16, keep _ (by unfold SaveW; omega), m56]
    by_cases h24 : r = .x24
    · subst h24; rw [v24, keep _ (by unfold SaveW; omega), m64]
    by_cases h4 : r = .x4
    · subst h4; rw [v4, keep _ (by unfold SaveW; omega), m72]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [vr.get (by simp [*]), ur.get (by simp [loopRegs, *]), tr.get (by simp [entryRegs, *])]
  · exact ((tf.trans uf).trans vf).mono (fun A _ h => by
      rcases h with (h | h) | h
      · left; exact h
      · exact h.elim
      · right; exact h)

/-! ### COEFGEN pieces -/

def CgSaveW (A : Nat) : Prop := TSAVE ≤ A ∧ A < TSAVE + 24

theorem cgHead_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1559) (leaf : Nat) (hl : leaf < 4096)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 14 17 t ∧ t.pc = pcOf 1569 ∧ t.getReg .x24 = BitVec.ofNat 64 TCOEF ∧
      t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + 0)) ∧ t.getReg .x29 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 TSAVE) = s.getReg .x4 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 8)) = s.getReg .x24 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 16)) = s.getReg .x14 ∧
      RegsExcept s t [.x14, .x24, .x29, .x30] ∧ Frame s t CgSaveW := by
  obtain ⟨t1, s1, p1, m0, m8, m16, r1, f1⟩ := cgHead5_spec hcode s hpc
  obtain ⟨t, s2, p2, x24, x14, x29, r2, f2⟩ := cgFam_spec hcode t1 p1 leaf hl (by rw [r1.get (by decide)]; exact h18)
  refine ⟨t, s1.trans s2, p2, x24, x14, x29, by rw [f2.get (by decide) id, m0], by rw [f2.get (by decide) id, m8],
    by rw [f2.get (by decide) id, m16], (r1.trans r2).mono (by simp),
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩

theorem cgCall_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1569) (H : Nat)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 1574 ∧ fetch im t = some (.base .ECALL) ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 H ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  have hobl : bCgCall.res.obligs s := by simp [bCgCall.res, rv_simp]
  refine ⟨_, symRun_sound bCgCall (hcode.codeAt_cgCall) s hpc hobl, ?_,
    symRun_ecall bCgCall (hcode.codeAt_cgCall) s hobl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bCgCall.res, E.eval]
  · simp only [Result.toState_getReg, bCgCall.res]; t3n [PRIV]
  · simp only [Result.toState_getReg, bCgCall.res]; t3n []
  · simp only [Result.toState_getReg, bCgCall.res]; t3n [SEEDS]
  · simp only [Result.toState_getMem, bCgCall.res]; t3n [PRIV, h14]
  · simp only [Result.toState_getMem, bCgCall.res]; t3n [PRIV]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgCall.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, bCgCall.res]
    t3n []
    split_ifs <;> first | rfl | omega

theorem cgCopy_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1575) {P H j : Nat}
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h24 : s.getReg .x24 = BitVec.ofNat 64 P)
    (hP : P % 8 = 0) (hP' : TCOEF ≤ P ∧ P + 32 ≤ TCOEF + 640)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 j) (hj : j < 16)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 H) (hH : H + 2 ^ 32 < 2 ^ 64) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = (if j + 1 = 16 then pcOf 1590 else pcOf 1569) ∧
      t.getMem (BitVec.ofNat 64 P) = s.getMem (BitVec.ofNat 64 SEEDS) ∧
      t.getMem (BitVec.ofNat 64 (P + 8)) = s.getMem (BitVec.ofNat 64 (SEEDS + 8)) ∧
      t.getMem (BitVec.ofNat 64 (P + 16)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16)) ∧
      t.getMem (BitVec.ofNat 64 (P + 24)) = s.getMem (BitVec.ofNat 64 (SEEDS + 24)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (P + 32) ∧ t.getReg .x14 = BitVec.ofNat 64 (H + 2 ^ 32) ∧
      t.getReg .x29 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x4, .x14, .x24, .x29, .x30] ∧ Frame s t (fun A => P ≤ A ∧ A < P + 32) := by
  have hobl : bCgCopy.res.obligs s := by
    simp [bCgCopy.res, rv_simp, h10, h24]
    t3n [PRIV]
    unfold TCOEF at hP'
    simp only [and_true, true_and]
    omega
  refine ⟨_, symRun_sound bCgCopy (hcode.codeAt_cgCopy) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bCgCopy.res, E.eval, CmpOp.eval, BinOp.eval, h29]
    t3n []
    split_ifs <;> first | rfl | omega
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getReg, bCgCopy.res]; t3n [h24]
  · simp only [Result.toState_getReg, bCgCopy.res]; t3n [h14]
  · simp only [Result.toState_getReg, bCgCopy.res]; t3n [h29]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgCopy.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TCOEF] at hP'
    simp only [Result.toState_getMem, bCgCopy.res]
    t3n [h24]
    all_goals (split_ifs <;> first | rfl | omega)

theorem cgExit_spec (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 1590) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      t.getReg .x4 = s.getMem (BitVec.ofNat 64 TSAVE) ∧
      t.getReg .x24 = s.getMem (BitVec.ofNat 64 (TSAVE + 8)) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 (TSAVE + 16)) ∧ t.getReg .x19 = 0 ∧
      RegsExcept s t [.x4, .x14, .x19, .x24, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bCgExit (hcode.codeAt_cgExit) s hpc (by simp [bCgExit.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bCgExit.res, E.eval, BinOp.eval]
  · simp only [Result.toState_getReg, bCgExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bCgExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bCgExit.res]; t3n [TSAVE]
  · simp [bCgExit.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgExit.res, rv_simp] <;> rfl
  · intro A _ _; simp [bCgExit.res, rv_simp]

/-! ### COEFGEN as a refinement of `SigGolfCandidate.T3.topCoefs` -/

/-- Writes of COEFGEN. -/
def CgW (A : Nat) : Prop :=
  A = PRIV + 16 ∨ A = PRIV + 24 ∨ (SEEDS ≤ A ∧ A < SEEDS + 32) ∨ CgSaveW A ∨ (TCOEF ≤ A ∧ A < TCOEF + 640)
def cgRegs : List Reg := [.x4, .x10, .x11, .x12, .x14, .x24, .x29, .x30]

/-- The secret-key words of the private input block. -/
structure SkAt (sk : BitVec 256) (s : MachineState) : Prop where
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0

theorem SkAt.frame {sk : BitVec 256} {s t : MachineState} {W : Nat → Prop} (h : SkAt sk s) (hf : Frame s t W)
    (hW : ∀ A, A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 → ¬ W A) :
    SkAt sk t :=
  ⟨(hf.get (by decide) (hW _ (by simp))).trans h.p0, (hf.get (by decide) (hW _ (by simp))).trans h.p8,
    (hf.get (by decide) (hW _ (by simp))).trans h.p32, (hf.get (by decide) (hW _ (by simp))).trans h.p40,
    (hf.get (by decide) (hW _ (by simp))).trans h.p48, (hf.get (by decide) (hW _ (by simp))).trans h.p56⟩

structure CgSt (s0 : MachineState) (leaf j : Nat) (acc : List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (if j < 16 then 1569 else 1590)
  x29 : u.getReg .x29 = BitVec.ofNat 64 j
  x24 : u.getReg .x24 = BitVec.ofNat 64 (TCOEF + 32 * j)
  x14 : u.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + j))
  len : acc.length = 2 * j
  coefs : ∀ k < 2 * j, DigAt u (TCOEF + 16 * k) (acc.getD k 0)
  m0 : u.getMem (BitVec.ofNat 64 TSAVE) = s0.getReg .x4
  m8 : u.getMem (BitVec.ofNat 64 (TSAVE + 8)) = s0.getReg .x24
  m16 : u.getMem (BitVec.ofNat 64 (TSAVE + 16)) = s0.getReg .x14
  regs : RegsExcept s0 u cgRegs
  frame : Frame s0 u CgW

theorem getD_append2_lt {l : List Digest} {a b : Digest} {k : Nat} (hk : k < l.length) :
    (l ++ [a, b]).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk, List.getElem_append_left hk]
theorem getD_append2_0 {l : List Digest} {a b : Digest} : (l ++ [a, b]).getD l.length 0 = a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]; simp
theorem getD_append2_1 {l : List Digest} {a b : Digest} : (l ++ [a, b]).getD (l.length + 1) 0 = b := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]; simp

/-- Cycles of one COEFGEN iteration (5 + the hash + 15). -/
def cgStepC : Nat := 5 + 8 + 15

theorem cg_step (hcode : Code im) (sk : BitVec 256) {s0 : MachineState} (hsk : SkAt sk s0) (h5 : s0.getReg .x5 = 0)
    {leaf : Nat} (hl : leaf < 4096) {j : Nat} (hj : j < 16) {acc : List Digest} {u : MachineState}
    (hu : CgSt s0 leaf j acc u) :
    TBSim im sk u cgStepC
      (SigGolfCandidate.T3.topSeedPair (31 * (leaf / 4) / 2 + j) >>= fun p => pure (acc ++ [p.1, p.2]))
      (CgSt s0 leaf (j + 1)) := by
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  obtain ⟨u1, su1, u1pc, e1, u1x10, u1x11, u1x12, m16, m24, u1r, u1f⟩ :=
    cgCall_spec hcode u (by rw [hu.pc, if_pos hj]) _ hu.x14
  have hcgw : ∀ A, A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 →
      ¬ CgW A := by
    intro A hA hw; unfold CgW CgSaveW TSAVE TCOEF at hw; simp only [PRIV, SEEDS] at hA hw; omega
  have hsk1 : SkAt sk u1 := (hsk.frame hu.frame hcgw).frame u1f (fun A hA hw => by
    simp only [PRIV] at hA hw; omega)
  have hqin : hashInput u1 = toQ (SigGolfCandidate.T3.privateInput sk
      (.inl (SigGolfCandidate.T3.header 0 0 0 (31 * (leaf / 4) / 2 + j) 0))) := by
    refine hashInput_toQ u1 _ 0 PRIV (privateInput_tweak_length _ _) u1x10 (by decide) (by decide) u1x11
      (by decide) ?_
    have m16' : u1.getMem (BitVec.ofNat 64 (PRIV + 16)) =
        BitVec.ofNat 64 (hdr0 0 0 0 (31 * (leaf / 4) / 2 + j)) := by
      rw [m16, hdr0_eq 0 0 0 _ (by norm_num) (by norm_num) (by norm_num) (by omega)]
    have m24' : u1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 0) := by
      rw [m24, hdr1_eq 0 0 (by norm_num) (by norm_num)]; rfl
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, hsk1.p0, hsk1.p8, m16', m24',
      hsk1.p32, hsk1.p40, hsk1.p48, hsk1.p56]
    rfl
  have hva : hashArgumentsValid u1 = true :=
    hashArgs_const u1 PRIV 64 SEEDS u1x10 u1x11 u1x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5' : u1.getReg .x5 = 0 := by rw [u1r.get (by decide), hu.regs.get (by decide), h5]
  unfold SigGolfCandidate.T3.topSeedPair
  refine TBSim.mono (TBSim.steps su1 (TBSim.privatePair_bind' (W := 15) e1 h5' hva hqin (fun a => ?_)))
    (by unfold cgStepC; omega) (fun _ _ h => h)
  have hwf := Frame.writeHash u1 a SEEDS u1x12 (by decide)
  have lo := DigAt.writeHash_lo u1 a SEEDS u1x12 (by decide)
  have hi := DigAt.writeHash_hi u1 a SEEDS u1x12 (by decide)
  have hP' : TCOEF ≤ TCOEF + 32 * j ∧ TCOEF + 32 * j + 32 ≤ TCOEF + 640 := by omega
  obtain ⟨u3, su3, u3pc, c0, c8, c16, c24, u3x24, u3x14, u3x29, u3r, u3f⟩ := cgCopy_spec hcode (writeHash u1 a)
    (by rw [pc_writeHash, u1pc, pcOf_add4]) (by rw [getReg_writeHash]; exact u1x10)
    (by rw [getReg_writeHash, u1r.get (by decide)]; exact hu.x24) (by unfold TCOEF; omega) hP'
    (by rw [getReg_writeHash, u1r.get (by decide)]; exact hu.x29) hj
    (by rw [getReg_writeHash, u1r.get (by decide)]; exact hu.x14) (by omega)
  have f13 : Frame u u3 (fun A => ((A = PRIV + 16 ∨ A = PRIV + 24) ∨ (SEEDS ≤ A ∧ A < SEEDS + 32)) ∨
      (TCOEF + 32 * j ≤ A ∧ A < TCOEF + 32 * j + 32)) := (u1f.trans hwf).trans u3f
  refine TBSim.pure_steps' su3 ⟨?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u3pc]
    by_cases h : j + 1 = 16
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  · exact u3x29
  · rw [u3x24, show TCOEF + 32 * j + 32 = TCOEF + 32 * (j + 1) by ring]
  · rw [u3x14, show 1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + j) + 2 ^ 32 = 1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + (j + 1)) by ring]
  · simp [hu.len]; ring
  · by_cases hkj : k < 2 * j
    · rw [getD_append2_lt (by rw [hu.len]; exact hkj)]
      exact (hu.coefs k hkj).frame f13 (by unfold TCOEF; omega) (by unfold TCOEF; simp only [PRIV, SEEDS]; omega)
        (by unfold TCOEF; simp only [PRIV, SEEDS]; omega)
    · by_cases hk0 : k = 2 * j
      · subst hk0
        rw [← hu.len, getD_append2_0]
        refine ⟨?_, ?_⟩
        · rw [show TCOEF + 16 * acc.length = TCOEF + 32 * j by rw [hu.len]; ring, c0, lo.1]
        · rw [show TCOEF + 16 * acc.length + 8 = TCOEF + 32 * j + 8 by rw [hu.len]; ring, c8, lo.2]
      · have hk1 : k = 2 * j + 1 := by omega
        subst hk1
        rw [← hu.len, getD_append2_1]
        refine ⟨?_, ?_⟩
        · rw [show TCOEF + 16 * (acc.length + 1) = TCOEF + 32 * j + 16 by rw [hu.len]; ring, c16, hi.1]
        · rw [show TCOEF + 16 * (acc.length + 1) + 8 = TCOEF + 32 * j + 24 by rw [hu.len]; ring, c24]
          rw [show SEEDS + 24 = SEEDS + 16 + 8 from rfl]; exact hi.2
  · rw [f13.get (by decide) (by unfold TSAVE TCOEF; simp only [PRIV, SEEDS]; omega), hu.m0]
  · rw [f13.get (by decide) (by unfold TSAVE TCOEF; simp only [PRIV, SEEDS]; omega), hu.m8]
  · rw [f13.get (by decide) (by unfold TSAVE TCOEF; simp only [PRIV, SEEDS]; omega), hu.m16]
  · exact ((hu.regs.trans u1r).trans ((show RegsExcept u1 (writeHash u1 a) [] from
      fun r _ => getReg_writeHash u1 a r).trans u3r)).mono (by simp [cgRegs])
  · exact (hu.frame.trans f13).mono (fun A _ h => by
      unfold CgW at *
      rcases h with h | ((h | h) | h) | h
      · exact h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; right; unfold TCOEF at *; omega)

/-- Cycle bound of COEFGEN (entry to return). -/
def cgC : Nat := 17 + (16 * cgStepC + 6)

theorem getD_take_drop (r : List Digest) (b k : Nat) (hk : k < 31) :
    ((r.drop b).take 31).getD k 0 = r.getD (b + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk, List.getElem?_drop]

/-- The signer form `T3.topCoefs leaf` as the 16-pair loop COEFGEN runs. -/
theorem topCoefs_eq (leaf : Nat) :
    SigGolfCandidate.T3.topCoefs leaf =
      (List.range' 0 16).foldlM (fun (acc : List Digest) j =>
        SigGolfCandidate.T3.topSeedPair (31 * (leaf / 4) / 2 + j) >>= fun p => pure (acc ++ [p.1, p.2])) [] >>=
        fun acc => pure ((acc.drop (leaf / 4 % 2)).take 31) := by
  unfold SigGolfCandidate.T3.topCoefs SigGolfCandidate.T3.topPairsFrom SigGolfCandidate.T3.topCoefCount
    SigGolfCandidate.T3.topCoefPairs
  rfl

theorem coefgen_tbsim (hcode : Code im) (sk : BitVec 256) (s : MachineState) (hpc : s.pc = pcOf 1559)
    (h1 : s.getReg .x1 = pcOf 1556) {leaf : Nat} (hl : leaf < 4096) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h5 : s.getReg .x5 = 0) (hsk : SkAt sk s) :
    TBSim im sk s cgC (SigGolfCandidate.T3.topCoefs leaf)
      (fun r u => u.pc = pcOf 1556 ∧ r.length = 31 ∧ CoefAtT u (leaf / 4 % 2) r ∧ u.getReg .x19 = 0 ∧
        RegsExcept s u [.x10, .x11, .x12, .x19, .x29, .x30] ∧ Frame s u CgW) := by
  obtain ⟨t0, s0, p0, x24, x14, x29, m0, m8, m16, r0, f0⟩ := cgHead_spec hcode s hpc leaf hl h18
  have h0 : CgSt s leaf 0 [] t0 :=
    ⟨by rw [p0]; rfl, x29, by rw [x24], x14, rfl, fun k hk => absurd hk (by omega), m0, m8, m16,
      r0.mono (by simp [cgRegs]), f0.mono (fun A _ h => by unfold CgW; right; right; right; left; exact h)⟩
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) 0 16
    (fun (acc : List Digest) j => SigGolfCandidate.T3.topSeedPair (31 * (leaf / 4) / 2 + j) >>=
      fun p => pure (acc ++ [p.1, p.2])) [] (fun j acc u => CgSt s leaf j acc u) cgStepC
    (fun j hj acc u hu => by simpa using cg_step hcode sk hsk h5 hl hj hu) h0
  rw [topCoefs_eq]
  refine TBSim.mono (TBSim.steps s0 (TBSim.bind (W₂ := 6) hloop (fun r u hu => ?_))) (by unfold cgC; omega)
    (fun _ _ h => h)
  obtain ⟨v, sv, vpc, v4, v24, v14, v19, vr, vf⟩ := cgExit_spec hcode u (by rw [hu.pc]; rfl)
  refine TBSim.pure_steps' sv ⟨?_, by simp only [List.length_take, List.length_drop, hu.len]; omega, fun k hk => ?_, v19, fun r hr => ?_, ?_⟩
  · rw [vpc, hu.regs.get (by decide), h1, pcOf_and_not1]
  · rw [getD_take_drop _ _ _ hk]
    exact (hu.coefs (leaf / 4 % 2 + k) (by omega)).frame vf (by unfold TCOEF; omega) id id
  · by_cases h4 : r = .x4
    · subst h4; rw [v4, hu.m0]
    by_cases h14 : r = .x14
    · subst h14; rw [v14, hu.m16]
    by_cases h24 : r = .x24
    · subst h24; rw [v24, hu.m8]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [vr.get (by simp [*]), hu.regs.get (by simp [cgRegs, *])]
  · exact (hu.frame.trans vf).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)


end ClaudeWCT.W9.Machine.Sign.SharedTopSeed

namespace ClaudeWCT.W9.Machine.Sign.SharedTopSeed
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> exact codeAt_sign_current_slice (by decide +kernel) (by decide +kernel)
end ClaudeWCT.W9.Machine.Sign.SharedTopSeed

namespace ClaudeWCT.W9.Machine.Sign.SharedTopLeafP
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit chain)
open ClaudeWCT.W9.Machine.Sign.SharedTopSeed
open ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.Arith
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {im : Image}

/-! ### Hybrid base states (scratch `TScr = [0x60000, 0x61280)`) -/

theorem tscr_iff (A : Nat) : TScr A ↔ SigGolfCandidate.T3M.Sign.Packed.TopScr A := by
  unfold TScr TSAVE TCOEF SigGolfCandidate.T3M.Sign.Packed.TopScr; omega

def hybT (s0 t : MachineState) : MachineState :=
  { s0 with mem := fun a => if 0x60000 ≤ a.toNat ∧ a.toNat < 0x61280 then t.mem a else s0.mem a }
structure HybOfT (s0 s t : MachineState) : Prop where
  regs : ∀ r, s.getReg r = s0.getReg r
  base : Frame s0 s TScr
  scr : ∀ A, A < 2 ^ 64 → TScr A → s.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A)
theorem hybT_of (s0 t : MachineState) : HybOfT s0 (hybT s0 t) t := by
  refine ⟨fun r => rfl, fun A hA hn => ?_, fun A hA h => ?_⟩
  · show (if 0x60000 ≤ (BitVec.ofNat 64 A).toNat ∧ (BitVec.ofNat 64 A).toNat < 0x61280 then t.mem _ else s0.mem _) =
      s0.mem _
    rw [toNat_ofNat_lt hA, if_neg (show ¬ (0x60000 ≤ A ∧ A < 0x61280) by unfold TScr TSAVE TCOEF at hn; omega)]
  · show (if 0x60000 ≤ (BitVec.ofNat 64 A).toNat ∧ (BitVec.ofNat 64 A).toNat < 0x61280 then t.mem _ else s0.mem _) =
      t.mem _
    rw [toNat_ofNat_lt hA, if_pos (show 0x60000 ≤ A ∧ A < 0x61280 by unfold TScr TSAVE TCOEF at h; omega)]
theorem HybOfT.refl_of {s0 t : MachineState} (hf : Frame s0 t (fun A => ¬ TScr A)) : HybOfT s0 s0 t :=
  ⟨fun _ => rfl, Frame.refl _ _, fun A hA hb => (hf.get hA (fun h => h hb)).symm⟩

theorem not_tscr {X : Nat} (h : X < 0x60000) : ¬ TScr X := fun hb => by unfold TScr TSAVE at hb; omega

theorem LeafPreS.transferT {sk : BitVec 256} {s0 s : MachineState} {A : LeafArgs} (h : LeafPreS sk s0 A)
    (hr : ∀ r, s.getReg r = s0.getReg r) (hf : Frame s0 s TScr) (hd : A.digp + A.n ≤ 0x60000) :
    LeafPreS sk s A := by
  have g : ∀ X, X < 0x60000 → s.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) :=
    fun X hX => hf.get (by omega) (not_tscr hX)
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
        rw [hf.getByte (by omega) (not_tscr (by omega))]; exact h.hdig i hi
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

/-- Writes of the top seed routines: the scratch, the private-pair header/answer and the chain seed slot. -/
def SeedWT (X : Nat) : Prop :=
  TScr X ∨ X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 64)

theorem LeafInv.rebaseT {s0 s t s' u : MachineState} {A : LeafArgs} {j : Nat} {st : List Digest × List Digest}
    (ht : LeafInv s A j st t) (hs : HybOfT s0 s t) (hs' : HybOfT s0 s' u) {R : List Reg}
    (hr : RegsExcept t u R) (hR : ∀ r ∈ R, r ∈ leafRegs ∧ r ≠ .x19 ∧ r ≠ .x23 ∧ r ≠ .x3)
    {W : Nat → Prop} (hf : Frame t u W) (hW : ∀ X, W X → SeedWT X)
    (hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hv : A.valp + 16 * A.n ≤ 0x60000)
    (hj : j ≤ A.n) : LeafInv s' A j st u := by
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLW : ∀ X, (X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 64)) →
      LeafW A X := by
    intro X h
    unfold LeafW
    rcases h with h | h | h | h
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; right; right; left; omega
  have nW : ∀ X, X < 0x60000 → ¬ (X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨
      (CHAIN + 48 ≤ X ∧ X < CHAIN + 64)) → ¬ W X := by
    intro X h1 h2 hw
    rcases hW X hw with h | h
    · exact not_tscr h1 h
    · exact h2 h
  have gr : ∀ r, r = .x19 ∨ r = .x23 ∨ r = .x3 → u.getReg r = t.getReg r := fun r h =>
    hr.get (fun hm => by
      obtain ⟨-, h1, h2, h3⟩ := hR r hm
      rcases h with rfl | rfl | rfl <;> simp_all)
  have hlv : ∀ X, LEAFPK ≤ X → X < LEAFPK + 16 * (A.n + 2) → ¬ W X := fun X h1 h2 =>
    nW X (by omega) (by omega)
  refine ⟨by rw [gr _ (by simp)]; exact ht.x19, by rw [gr _ (by simp)]; exact ht.x23,
    by rw [gr _ (by simp)]; exact ht.x3, fun r hr' => ?_, fun X hX hn' => ?_, ?_, ?_, ht.elen, ht.vlen,
    fun hso c hc => ?_, ?_⟩
  · rw [hr.get (fun h => hr' (hR r h).1), ht.regs.get hr', hs.regs, hs'.regs]
  · by_cases hb : TScr X
    · rw [hs'.scr X hX hb]
    · have hnw : ¬ W X := fun hw => by
        rcases hW X hw with h | h
        · exact hb h
        · exact hn' (hLW X h)
      rw [hf.get hX hnw, ht.frame.get hX hn', hs.base.get hX hb, hs'.base.get hX hb]
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh16
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh24
  · have h1 := slot_ge A.lay c; have h2 := slot_lt A.lay (show c < A.n by omega)
    exact (ht.ends hso c hc).frame hf (by omega) (hlv _ (by omega) (by omega)) (hlv _ (by omega) (by omega))
  · exact ht.vals.frame hf (by rw [ht.vlen]; omega) (fun X h1 h2 => by
      rw [ht.vlen] at h2
      exact nW X (by omega) (by omega))

theorem LeafW_not_tscr {A : LeafArgs} (hv : A.valp + 16 * A.n ≤ 0x60000) (hd : A.dest + 16 ≤ 0x60000) {X : Nat}
    (h : LeafW A X) : ¬ TScr X := by
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
  unfold LeafW at h
  intro hb; unfold TScr TSAVE TCOEF at hb
  simp only [PRIV, SEEDS, CHAIN, LEAFPK, LOUT] at h
  split_ifs at h <;> omega

/-! ### Single-word blocks around COEFGEN and TOPSEED -/

theorem pre0_spec (hcode : SharedTopSeed.Code im) (s : MachineState) (hpc : s.pc = pcOf 1554) (h8 : s.getReg .x8 = BitVec.ofNat 64 0) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1555 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bPre hcode.codeAt_1554 s hpc (by simp [bPre.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bPre.res, E.eval, CmpOp.eval, h8]
  · intro r hr; cases r <;> simp_all [bPre.res, rv_simp] <;> rfl
  · intro A _ _; simp [bPre.res, rv_simp]
theorem jal_spec (hcode : SharedTopSeed.Code im) (s : MachineState) (hpc : s.pc = pcOf 1555) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1559 ∧ t.getReg .x1 = pcOf 1556 ∧ RegsExcept s t [.x1] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bJal hcode.codeAt_1555 s hpc (by simp [bJal.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bJal.res, E.eval]
  · simp [bJal.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bJal.res, rv_simp] <;> rfl
  · intro A _ _; simp [bJal.res, rv_simp]
theorem j1053_spec (hcode : SharedTopSeed.Code im) (s : MachineState) (hpc : s.pc = pcOf 1556) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (1013 + 40) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bJ1053 hcode.codeAt_1556 s hpc (by simp [bJ1053.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bJ1053.res, E.eval]
  · intro r hr; cases r <;> simp_all [bJ1053.res, rv_simp] <;> rfl
  · intro A _ _; simp [bJ1053.res, rv_simp]
theorem li19_spec (hsub : Sign.SharedLeafCode.Code im 1013) (s : MachineState) (hpc : s.pc = pcOf (1013 + 40)) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (1013 + 41) ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound Sign.SeedIndependent.blkS_40 (Sign.SharedLeafCode.Code.codeAt_sub40S hsub) s hpc
    (by simp [Sign.SeedIndependent.blkS_40.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Sign.SeedIndependent.blkS_40.res, E.eval]
  · simp [Sign.SeedIndependent.blkS_40.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [Sign.SeedIndependent.blkS_40.res, rv_simp] <;> rfl
  · intro A _ _; simp [Sign.SeedIndependent.blkS_40.res, rv_simp]
theorem tsJal_spec (hcode : SharedTopSeed.Code im) (s : MachineState) (hpc : s.pc = pcOf 1557) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1597 ∧ t.getReg .x1 = pcOf 1558 ∧ RegsExcept s t [.x1] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bTsJal hcode.codeAt_1557 s hpc (by simp [bTsJal.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bTsJal.res, E.eval]
  · simp [bTsJal.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bTsJal.res, rv_simp] <;> rfl
  · intro A _ _; simp [bTsJal.res, rv_simp]
theorem tsJ_spec (hcode : SharedTopSeed.Code im) (s : MachineState) (hpc : s.pc = pcOf 1558) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (1013 + 71) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bTsJ hcode.codeAt_1558 s hpc (by simp [bTsJ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bTsJ.res, E.eval]
  · intro r hr; cases r <;> simp_all [bTsJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [bTsJ.res, rv_simp]

theorem run_top : run SharedSeed.tailLook [1557] 20746 [.br true] = some PackedLeaf.resTop := by
  apply optBeq_eq; decide +kernel
theorem top_spec (hseedcode : SharedSeed.Code im) (s : MachineState) (hpc : s.pc = pcOf 20746)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 0) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1557 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece (SharedSeed.tailLook_ok hseedcode) run_top s hpc rfl (by
    intro b hb
    simp only [PackedLeaf.resTop, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h8]; decide) rfl
  exact ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x,
    fun A _ _ => by rw [hm]; rfl⟩

/-! ### One top chain -/

section chain
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre

/-- One signature-only chain from `b + 71` (seed already at `CHAIN + 48`). Witness stack: the chain is
`WCT9.chainW 0` (top G chains: even `j ≤ 52`), each rung costs `SharedChain.topRungK j m`. -/
theorem leaf_iter71 (hsub : Sign.SharedLeafCode.Code im 1013) (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im) (hlay : A.lay = 0) (hso : A.so = true) {j : Nat} (hj : j < A.n) {st : List Digest × List Digest}
    {t : MachineState} (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (1013 + 71)) (seed : Digest)
    (hseed : DigAt t (CHAIN + 48) seed) (hdj : A.e j ≤ maxDigit 0 j) :
    TSim im sk t (24 + selectorExtra A.lay j + sumTo (SharedChain.topRungK j) (A.e j))
      (24 + selectorExtra A.lay j + sumTo (SharedChain.topRungC j) (A.e j)) (A.e j) (A.e j)
      (halfUpd A st <$> SigGolfCandidate.T3M.Sign.Seed.chainProgW A j seed)
      (fun st' u => u.pc = pcOf (1013 + 41) ∧ LeafInv s0 A (j + 1) st' u ∧
        Frame t u (fun X => (X = CHAIN + 16 ∨ X = CHAIN + 24) ∨ (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨
          (slot A.lay j ≤ X ∧ X < slot A.lay j + 16) ∨ (A.valp + 16 * j ≤ X ∧ X < A.valp + 16 * j + 16))) := by
  obtain ⟨u0, st0, u0pc, hcp, hcs, u0r, u0f⟩ := Sign.SharedLeaf.leaf_prechainFrom71S hsub sk hpre hj
    (fun h => absurd (by rw [hlay]; rfl) h) ht hpc seed hseed
  have hcp' : Sign.Seed.ChainPreS u0 0 A.tree A.leaf j (A.e j) (A.e j) (A.valp+16*j) (1013+79) := by
    simpa only [hlay,LeafArgs.e,hso,if_true] using hcp
  have hch := SharedChain.top_chain hchain hpref sk hcp' u0pc hcs hdj
  rw [map_eq_bind_pure_comp]
  refine (TSim.steps st0 (TSim.bind (f := fun r => pure (halfUpd A st r)) (k₂ := 4 + (if A.so then 0 else 11 + slotK A.lay j))
    (c₂ := 4 + (if A.so then 0 else 11 + slotK A.lay j)) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq (by unfold SigGolfCandidate.T3M.Sign.Seed.chainProgW; simp only [hlay,LeafArgs.e,hso,if_true,Nat.sub_self,SharedChain.chainW_zero,bind_assoc,pure_bind,Function.comp_apply]) ?_ ?_ ?_ ?_
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw, hfw⟩ := Sign.SharedLeaf.leaf_postchainS hsub sk hpre hj ht hupc (u0r.trans hur)
      (u0f.trans huf) r.1 r.2 hv hl
    refine TSim.pure_steps stw ⟨wpc, by simpa [halfUpd] using hw, ?_⟩
    refine ((u0f.trans huf).trans hfw).mono (fun X _ h => ?_)
    unfold ChainW at h
    rcases h with ((h | h) | h | h | h) | h
    · right; left; simp only [CHAIN] at h ⊢; omega
    · right; left; simp only [CHAIN] at h ⊢; omega
    · left; exact h
    · right; left; exact h
    · right; right; right; exact h
    · right; right; left; exact h
  all_goals (try simp only [hso, if_true])
  all_goals omega

/-- Cycles of one top chain: `b+41`, hook, `20746`, `jal`, HORN, `j`, then the chain from `b + 71`.
Stage 2 (C3, #866): every rung also runs the chain-0 trampoline, so 350 -> 365.
Pairing stage 1: every rung also runs the F step block (3 more steps), so 365 -> 386.
Witness stack: the top step block 1760.. (G chains even `j ≤ 52`; `e ≤ maxDigit 0 j`), so 386 -> 469
(`topChain_cost`). -/
def topChainC : Nat := 5 + hornCT + 1 + 469

omit hpre in
/-- Witness stack: the cycle bound of one top chain from `b + 71` (`e ≤ maxDigit 0 j`, at most 7 rungs). -/
theorem topChain_cost : ∀ j, j < 51 → ∀ e, e ≤ maxDigit 0 j →
    24 + selectorExtra 0 j + sumTo (SharedChain.topRungC j) e ≤ 469 := by
  decide +kernel

structure FStT (s0 : MachineState) (A : LeafArgs) (coefs : List Digest) (j : Nat)
    (st : List Digest × List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (1013 + 41)
  coef : CoefAtT u (A.leaf / 4 % 2) coefs
  inv : ∃ s, HybOfT s0 s u ∧ LeafInv s A j st u

/-- The chain body of the signature-only `T3.buildLeafTop` (witness stack: `T3.topChain`). -/
def topStepT (leaf : Nat) (digits : List Nat) (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    SigGolfCandidate.T3.M (List Digest × List Digest) := do
  let value ← SigGolfCandidate.T3.topChain leaf i 0 (digits.getD i 0) (SigGolfCandidate.T3.topSeed coefs leaf i)
  pure (state.1, state.2 ++ [value])

omit hpre in
theorem topStep_eq (hlay : A.lay = 0) (hso : A.so = true) (htree : A.tree = 0) (coefs : List Digest)
    (st : List Digest × List Digest) (j : Nat) :
    topStepT A.leaf A.digits coefs st j =
      halfUpd A st <$> SigGolfCandidate.T3M.Sign.Seed.chainProgW A j
        (familyEval coefs (SigGolfCandidate.T3.topPoint A.leaf j)) := by
  unfold topStepT SigGolfCandidate.T3M.Sign.Seed.chainProgW halfUpd
  simp only [hso, if_true, LeafArgs.e, Nat.sub_self, SharedChain.chainW_zero, map_bind, pure_bind, map_pure, hlay,
    htree, ClaudeWCT.WCT9.chainW_top_eq]
  rfl

theorem top_chain_step (hcode : SharedTopSeed.Code im) (hsub : Sign.SharedLeafCode.Code im 1013) (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im) (hseedcode : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode) (hlay : A.lay = 0) (hso : A.so = true) (htree : A.tree = 0)
    (hd7 : ∀ i < A.n, A.d i ≤ maxDigit 0 i) (hvS : A.valp + 16 * A.n ≤ 0x60000) (hdS : A.digp + A.n ≤ 0x60000)
    (hdestS : A.dest + 16 ≤ 0x60000) {coefs : List Digest} (hlen : coefs.length = 31) {j : Nat} (hj : j < 51)
    {st : List Digest × List Digest} {u : MachineState} (hu : FStT s0 A coefs j st u) :
    TBSim im sk u topChainC (topStepT A.leaf A.digits coefs st j) (FStT s0 A coefs (j + 1)) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hlay]; rfl
  have hleaf : A.leaf < 4096 := by have := hpre.hleafHeight; rw [hlay] at this; exact this
  have hb : A.leaf / 4 % 2 ≤ 1 := by omega
  obtain ⟨s, hs, hinv⟩ := hu.inv
  have g : ∀ r, r ∉ leafRegs → u.getReg r = s0.getReg r := fun r hr => by rw [hinv.regs.get hr, hs.regs]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.SharedLeaf.sub41_spec hsub u hu.pc j A.n (by omega) (by omega) hinv.x19
    (by rw [g _ (by simp [leafRegs]), hpre.x26])
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := SharedLeafMemory.hook_spec hhook t1 (by rw [t1pc])
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := top_spec hseedcode t2 t2pc
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [leafRegs]), hpre.x8, hlay]; rfl)
  obtain ⟨t4, st4, t4pc, t4x1, t4r, t4f⟩ := tsJal_spec hcode t3 t3pc
  have e14 : RegsExcept u t4 [.x1] := (((t1r.trans t2r).trans t3r).trans t4r).mono (by simp)
  have f14 : Frame u t4 (fun _ => False) := (((t1f.trans t2f).trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  obtain ⟨w, n, sw, hnw, wpc, wseed, wr, wf⟩ := SharedTopSeed.horn_run hcode t4 t4pc (i := j) hleaf (by omega)
    (by rw [e14.get (by simp), g _ (by simp [leafRegs]), hpre.x18])
    (by rw [e14.get (by simp)]; exact hinv.x19) hlen (hu.coef.frame hb f14 (fun _ _ _ h => h))
  obtain ⟨w2, sw2, w2pc, w2r, w2f⟩ := tsJ_spec hcode w (by rw [wpc, t4x1, pcOf_and_not1])
  have hs' : HybOfT s0 (hybT s0 w2) w2 := hybT_of s0 w2
  have hinvw : LeafInv (hybT s0 w2) A j st w2 := LeafInv.rebaseT hinv hs hs' ((e14.trans wr).trans w2r) (by
      intro r hr
      simp only [List.nil_append, List.cons_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    ((f14.trans wf).trans w2f) (fun X h => by
      unfold SeedWT TScr SaveW TSAVE TCOEF at *
      simp only [CHAIN, PRIV, SEEDS, false_or, or_false] at *
      omega)
    hpre.hvs hvS (by omega)
  have hpre' : LeafPreS sk (hybT s0 w2) A := LeafPreS.transferT hpre hs'.regs hs'.base hdS
  have hseed : DigAt w2 (CHAIN + 48) (familyEval coefs (SigGolfCandidate.T3.topPoint A.leaf j)) := wseed.frame w2f (by decide) (by simp) (by simp)
  have hej : A.e j = A.d j := by unfold LeafArgs.e; rw [hso, if_pos rfl]
  have hdj : A.e j ≤ maxDigit 0 j := by rw [hej]; exact hd7 j (by omega)
  have hit := leaf_iter71 sk hpre' hsub hchain hpref hlay hso (j := j) (by omega) hinvw (by rw [w2pc]) _ hseed hdj
  have hk : 24 + selectorExtra A.lay j + sumTo (SharedChain.topRungK j) (A.e j) ≤
      24 + selectorExtra A.lay j + sumTo (SharedChain.topRungC j) (A.e j) := by
    have : sumTo (SharedChain.topRungK j) (A.e j) ≤ sumTo (SharedChain.topRungC j) (A.e j) :=
      SigGolfCandidate.T3M.Sign.Packed.sumTo_le_sumTo _ _ _
        (fun m _ => by unfold SharedChain.topRungK SharedChain.topRungC; omega)
    omega
  have hc : 24 + selectorExtra A.lay j + sumTo (SharedChain.topRungC j) (A.e j) ≤ 469 := by
    rw [hlay]; exact topChain_cost j hj (A.e j) hdj
  rw [topStep_eq hlay hso htree]
  refine TBSim.mono (TBSim.steps (((((st1.trans st2).trans st3).trans st4).trans sw).trans sw2)
    ((hit.toTBSim hk).mono hc (fun st' x hx => ?_))) (by unfold topChainC; omega) (fun _ _ h => h)
  obtain ⟨xpc, hxinv, hxf⟩ := hx
  have hxs : ∀ X, X < 2 ^ 64 → TScr X → x.getMem (BitVec.ofNat 64 X) = w2.getMem (BitVec.ofNat 64 X) :=
    fun X hX hb => (hxinv.frame.get hX (fun hl => LeafW_not_tscr hvS hdestS hl hb)).trans (hs'.scr X hX hb)
  refine ⟨xpc, fun k hk => ?_, ⟨hybT s0 w2, ⟨hs'.regs, hs'.base,
    fun X hX hb => (hs'.scr X hX hb).trans (hxs X hX hb).symm⟩, hxinv⟩⟩
  have hwk : DigAt w2 (TCOEF + 16 * (A.leaf / 4 % 2 + k)) (coefs.getD k 0) :=
    ((hu.coef k hk).frame (f14.trans wf) (by unfold TCOEF; omega)
      (by simp only [SaveW, TSAVE, TCOEF, CHAIN, false_or, not_or]; omega)
      (by simp only [SaveW, TSAVE, TCOEF, CHAIN, false_or, not_or]; omega)).frame w2f (by unfold TCOEF; omega)
      (by simp) (by simp)
  exact ⟨by rw [hxs _ (by unfold TCOEF; omega) (by unfold TScr TSAVE TCOEF; omega)]; exact hwk.1,
    by rw [hxs _ (by unfold TCOEF; omega) (by unfold TScr TSAVE TCOEF; omega)]; exact hwk.2⟩

end chain

/-! ### The top leaf -/

theorem buildLeafTop_so (leaf : Nat) (digits : List Nat) :
    SigGolfCandidate.T3.buildLeafTop leaf digits true = (SigGolfCandidate.T3.topCoefs leaf >>= fun coefs =>
      (List.range' 0 51).foldlM (topStepT leaf digits coefs) ([], []) >>= fun st => pure (0, st.2)) := by
  rw [← List.range_eq_range']
  rfl

def topLeafC : Nat := 305000
def Spec (im : Image) : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState),
    A.lay = 0 → A.so = true → A.tree = 0 → (∀ i < A.n, A.d i ≤ maxDigit 0 i) →
    A.valp + 16*A.n ≤ 0x60000 → A.digp+A.n ≤ 0x60000 → A.dest+16 ≤ 0x60000 →
    LeafPreS sk s A → s.pc=pcOf (1013+27) →
    TBSim im sk s topLeafC (SigGolfCandidate.T3.buildLeafTop A.leaf A.digits A.so)
      (fun r t => t.pc=pcOf A.ret ∧ DigsAt t A.valp r.2 ∧ r.2.length=A.n ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ SigGolfCandidate.T3M.Sign.Packed.TopScr X))

theorem topLeafSpec (hcode : SharedTopSeed.Code im) (hsub : Sign.SharedLeafCode.Code im 1013) (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im) (hseedcode : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode) : Spec im := by
  intro sk A s0 hlay hso htree hd7 hvS hdS hdestS hpre hpc
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hlay]; rfl
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hleaf : A.leaf < 4096 := by have := hpre.hleafHeight; rw [hlay] at this; exact this
  obtain ⟨t1, st1, t1pc, t1x3, t1l16, t1l24, t1r, t1f⟩ :=
    Sign.SharedLeaf.sub27_pre_spec hsub s0 hpc A.lay A.tree A.leaf (by have := hpre.hroute; omega) hpre.x8 hpre.x9
      hpre.x18 (Or.inl htree)
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := pre0_spec hcode t1 t1pc (by rw [t1r.get (by decide), hpre.x8, hlay]; rfl)
  obtain ⟨t3, st3, t3pc, t3x1, t3r, t3f⟩ := jal_spec hcode t2 t2pc
  have e13 : RegsExcept s0 t3 [.x3, .x6, .x28, .x30, .x1] := ((t1r.trans t2r).trans t3r).mono (by simp)
  have f13 : Frame s0 t3 (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) :=
    ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)
  have hsk : SkAt sk t3 := ⟨by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p0,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p8,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p32,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p40,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p48,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p56⟩
  have hcg := SharedTopSeed.coefgen_tbsim hcode sk t3 t3pc t3x1 hleaf (by rw [e13.get (by decide), hpre.x18])
    (by rw [e13.get (by decide), hpre.x5]) hsk
  rw [hso, buildLeafTop_so]
  refine TBSim.mono (TBSim.steps ((st1.trans st2).trans st3) (TBSim.bind
    (W₂ := 2 + (51 * topChainC + 3)) hcg (fun coefs u hu => ?_))) (by
      unfold topLeafC cgC cgStepC topChainC hornCT hstepC; omega) (fun _ _ h => h)
  obtain ⟨upc, ulen, ucoef, u19, ur, uf⟩ := hu
  obtain ⟨v1, sv1, v1pc, v1r, v1f⟩ := j1053_spec hcode u upc
  obtain ⟨v, sv, vpc, v19, vr, vf⟩ := li19_spec hsub v1 v1pc
  have euv : RegsExcept s0 v ([.x3, .x6, .x28, .x30, .x1] ++ [.x10, .x11, .x12, .x19, .x29, .x30] ++ [] ++ [.x19]) :=
    ((e13.trans ur).trans v1r).trans vr
  have fuv : Frame s0 v (fun X => (((X = LEAFPK + 16 ∨ X = LEAFPK + 24) ∨ CgW X) ∨ False) ∨ False) :=
    ((f13.trans uf).trans v1f).trans vf
  have hs1 : HybOfT s0 (hybT s0 v) v := hybT_of s0 v
  have h0 : LeafInv (hybT s0 v) A 0 ([], []) v := by
    refine ⟨v19, ?_, ?_, fun r hr => ?_, fun X hX hn' => ?_, ?_, ?_, by simp [hso], rfl,
      fun h => absurd h (by rw [hso]; decide), DigsAt.nil _ _⟩
    · rw [euv.get (by simp), hpre.x23]; simp
    · rw [vr.get (by decide), v1r.get (by decide), ur.get (by decide), t3r.get (by decide), t2r.get (by decide),
        t1x3, hpre.x1]
    · rw [euv.get (fun h => hr (by simp [leafRegs] at h ⊢; rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp [h])), hs1.regs]
    · by_cases hb : TScr X
      · rw [hs1.scr X hX hb]
      · have hW : ¬ ((((X = LEAFPK + 16 ∨ X = LEAFPK + 24) ∨ CgW X) ∨ False) ∨ False) := by
          intro h
          apply hn'
          unfold LeafW; rw [if_pos hlay, hn]
          rcases h with (((h | h) | h) | h) | h
          · right; right; right; right; right; right; left; omega
          · right; right; right; right; right; right; left; omega
          · unfold CgW at h
            rcases h with h | h | h | h | h
            · left; exact h
            · right; left; exact h
            · right; right; left; exact h
            · exact absurd (by unfold TScr TSAVE TCOEF; unfold CgSaveW TSAVE at h; omega) hb
            · exact absurd (by unfold TScr TSAVE TCOEF; unfold TCOEF at h; omega) hb
          · exact h.elim
          · exact h.elim
        rw [fuv.get hX hW, hs1.base.get hX hb]
    · rw [vf.get (by decide) (by simp), v1f.get (by decide) (by simp),
        uf.get (by decide) (by unfold CgW CgSaveW TSAVE TCOEF; simp only [PRIV, SEEDS, LEAFPK]; omega),
        t3f.get (by decide) (by simp), t2f.get (by decide) (by simp), t1l16]
    · rw [vf.get (by decide) (by simp), v1f.get (by decide) (by simp),
        uf.get (by decide) (by unfold CgW CgSaveW TSAVE TCOEF; simp only [PRIV, SEEDS, LEAFPK]; omega),
        t3f.get (by decide) (by simp), t2f.get (by decide) (by simp), t1l24]
  have hF0 : FStT s0 A coefs 0 ([], []) v := ⟨vpc, (ucoef.frame (by omega) v1f (fun _ _ _ h => h)).frame (by omega) vf (fun _ _ _ h => h),
    ⟨_, hs1, h0⟩⟩
  have hfold := TBSim.foldlM_range' (image := im) (sk := sk) 0 51
    (topStepT A.leaf A.digits coefs) ([], []) (FStT s0 A coefs) topChainC
    (fun j hj st x hx => by simpa using top_chain_step sk hpre hcode hsub hchain hpref hseedcode hhook hlay hso htree hd7 hvS hdS hdestS ulen hj hx) hF0
  refine TBSim.steps (sv1.trans sv) (TBSim.bind (W₁ := 51 * topChainC) (W₂ := 3) hfold (fun rows x hx => ?_))
  obtain ⟨xpc, -, ⟨s3, hs3, hinv3⟩⟩ := hx
  have hpre3 := LeafPreS.transferT hpre hs3.regs hs3.base hdS
  rw [show (51 : Nat) = A.n from hn.symm] at hinv3
  have hex := Sign.SharedLeaf.leaf_exitS hsub sk hpre3 hinv3 xpc
  simp only [hso, if_true] at hex
  refine TBSim.mono ((hex.toTBSim (by norm_num)).mono le_rfl (fun r y hy => ?_)) le_rfl (fun _ _ h => h)
  obtain ⟨ypc, -, yvals, ylen, -, yregs, yframe, -⟩ := hy
  refine ⟨ypc, yvals, ylen, fun r hr => by rw [yregs.get hr, hs3.regs], fun X hX hn' => ?_⟩
  have hl : ¬ LeafW A X := fun h => hn' (Or.inl h)
  have ht : ¬ TScr X := fun h => hn' (Or.inr ((tscr_iff X).mp h))
  rw [yframe.get hX hl, hs3.base.get hX ht]

end ClaudeWCT.W9.Machine.Sign.SharedTopLeafP

namespace ClaudeWCT.W9.Machine.Sign.SharedTopLeafP
open SigGolfCandidate.T3M
theorem installed_topLeafSpec : Spec Images.signImage :=
  topLeafSpec SharedTopSeed.installed_code Sign.SharedLeafCode.installed_code
    Sign.SharedChain.installed_code Sign.SharedChain.installed_prefix_code
    SharedSeed.installed_code SharedSeed.installed_seed_hook

theorem installed_continuation_leaf : Sign.SharedTopContinuation.LeafSpec Images.signImage :=
  installed_topLeafSpec
end ClaudeWCT.W9.Machine.Sign.SharedTopLeafP
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FamilySpec ====
section

/-!
# Machine-side unfoldings of the stage-A FTS signer (`buildCoordinateF`, `buildChildF`, `ftsCoefs`)

Kept local to the sign machine (stream A-SIGN) so that the spec-level files owned by A-SPEC can change freely.
All factorizations hold by `rfl`.
-/

namespace ClaudeWCT.W9.Machine.Sign
open OracleComp
open SigGolfCandidate.T3 (M Digest)

/-- One chain of `WCT9.buildChildF`: the seed is the family value at `ftsPoint sel i`. -/
def fChildStep (index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Fin 6) : M (List Digest × List Digest) := do
  let secret := WCT9.ftsFamilySeed coefs sel i.val
  let deficit := WCT9.wordDigit word i
  let value ← WCT9.chain index coord sel i.val 0 (4 - deficit) secret
  let last ← WCT9.chain index coord sel i.val (4 - deficit) deficit value
  pure (state.1 ++ [last], state.2 ++ [value])

/-- The six chains of one child. -/
def fChildRows (index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.finRange 6).foldlM (fChildStep index coord sel word coefs) ([], [])

theorem buildChildF_factor (index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    WCT9.buildChildF index coord sel word coefs padL = (do
      let rows ← fChildRows index coord sel word coefs
      let root ← WCT9.leafHashP index coord sel padL rows.1
      pure (root, rows.2)) := rfl

/-- C1: `WCT9.buildChildH` (leaf of heap `heap`) factors through the same six chains. -/
theorem buildChildH_factorS (heap index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    WCT9.buildChildH heap index coord sel word coefs padL = (do
      let rows ← fChildRows index coord sel word coefs
      let root ← WCT9.leafHashH heap index coord sel padL rows.1
      pure (root, rows.2)) := rfl

/-- The 128 children of one coordinate (leaf roots, selected child's chain values). -/
def fCoordRows (index : Nat) (coord : WCT9.Coord) (selected : WCT9.Child) (word : WCT9.Rank)
    (coefs : List Digest) (padL : Digest) : M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
      let (root, values) ← WCT9.buildChildF index coord.val j word coefs padL
      pure (state.1 ++ [root], (if j = selected.val then values else state.2))) ([], [])

theorem buildCoordinateF_factor (index : Nat) (coord : WCT9.Coord) (selected : WCT9.Child) (word : WCT9.Rank)
    (prev : Digest × Digest) :
    WCT9.buildCoordinateF index coord selected word prev = (do
      let coefs ← WCT9.ftsCoefs index coord.val
      let rows ← fCoordRows index coord selected word coefs prev.1
      let nodes ← WCT9.heapBuild index coord.val prev.2 rows.1
      pure (WCT9.heapLevels nodes, rows.2)) := rfl

/-- One coefficient query of `WCT9.ftsCoefs`. -/
def coefStep (index coord : Nat) (acc : List Digest) (j : Nat) : M (List Digest) := do
  let p ← WCT9.ftsSeedPair index coord j
  pure (acc ++ [p.1, p.2])

theorem ftsCoefs_eq (index coord : Nat) :
    WCT9.ftsCoefs index coord = (List.range' 0 27).foldlM (coefStep index coord) [] := by
  unfold WCT9.ftsCoefs WCT9.ftsCoefPairs
  rw [List.range_eq_range']
  rfl

end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsLoop ====
section

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
    (CHAINW + 48 ≤ A ∧ A < CHAINW + 112) ∨ (LEAFW ≤ A ∧ A < LEAFW + 128) ∨ (slotV c 0 ≤ A ∧ A < slotV c 6)
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
/-- Witness stack: G chain steps (chains 1, 3) cost 38 (F: 28); `stepC` uses the G bound for every chain. -/
def stepC : Nat := 5 + (hornC + (17 + (11 + 38 * 4 + 8)))
section step
variable {im : Image} {sk : BitVec 256}
-- (witness stack) removed: reference-image (NewCodeAt) version, the old FTS code has no G chains.
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
-- (witness stack) removed: reference-image (NewCodeAt) version, the old FTS code has no G chains.
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
-- (witness stack) removed: reference-image (NewCodeAt) version, the old FTS code has no G chains.
theorem LoopInv.init {c index sel w : Nat} {s0 : MachineState} (hpc : s0.pc = pcOf (leafI c))
    (hb : BodySt sk 0 index sel w s0) : LoopInv sk c index sel w s0 0 ([], []) s0 :=
  ⟨by rw [if_pos (by norm_num)]; exact hpc, by rw [if_pos (by norm_num)]; exact hb, rfl,
    fun j' hj' => absurd hj' (by omega), fun h => absurd h (by omega),
    fun _ _ _ _ _ => rfl, RegsExcept.refl _ _, Frame.refl _ _⟩
-- (witness stack) removed: reference-image (NewCodeAt) version, the old FTS code has no G chains.
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
    rw [hu, pc_writeHash, h.pc, if_pos hj, SigGolfCandidate.T3M.pcOf_add4, paI_ecI c hc]
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

namespace SigGolfCandidate.T3M.Sign.SharedTier
open SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (EOUT)

/-- The digest acceptance helper stores its cost tier for the subsequent top
search and residual initialization. -/
structure At (extra : Nat) (s : MachineState) : Prop where
  low : s.getMem (BitVec.ofNat 64 (EOUT + 32)) = BitVec.ofNat 64 (12 + extra)
  high : s.getMem (BitVec.ofNat 64 (EOUT + 40)) = BitVec.ofNat 64 (14 + extra)
  pool : s.getMem (0x66028#64) = BitVec.ofNat 64 (69 + extra)

theorem At.frame {extra : Nat} {s t : MachineState} {W : Nat → Prop}
    (h : At extra s) (hf : Frame s t W)
    (hlow : ¬ W (EOUT + 32)) (hhigh : ¬ W (EOUT + 40))
    (hpool : ¬ W 0x66028) : At extra t := by
  refine ⟨(hf.get (A := EOUT + 32) (by unfold EOUT; decide) hlow).trans h.low,
    (hf.get (A := EOUT + 40) (by unfold EOUT; decide) hhigh).trans h.high,
    (hf.get (A := 0x66028) (by decide) hpool).trans h.pool⟩
end SigGolfCandidate.T3M.Sign.SharedTier

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

theorem forestW_not_tier_cell (A : Nat)
    (hA : A = SigGolfCandidate.T3M.Search.EOUT + 32 ∨
      A = SigGolfCandidate.T3M.Search.EOUT + 40 ∨ A = 0x66028) :
    ¬ forestW A := by
  intro ⟨c,hc,hw⟩
  rcases hA with rfl | rfl | rfl
  all_goals interval_cases c <;> decide at hw

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
  tierBound : SharedForest.conditionalExtra a ≤ 4
  tier : SigGolfCandidate.T3M.Sign.SharedTier.At (SharedForest.conditionalExtra a) s

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

theorem closedW_not_tier_cell (A : Nat)
    (hA : A = SigGolfCandidate.T3M.Search.EOUT + 32 ∨
      A = SigGolfCandidate.T3M.Search.EOUT + 40 ∨ A = 0x66028) :
    ¬ (A=PRIVW+40 ∨ A=PRIVW+32 ∨ A=PRIVW+8 ∨ A=PRIVW ∨ forestW A ∨ FinalW A) := by
  have hn := forestW_not_tier_cell A hA
  rcases hA with rfl | rfl | rfl
  all_goals intro hw
  all_goals rcases hw with h | h | h | h | h | h
  all_goals first | exact hn h | (simp_all [FinalW, SigGolfCandidate.T3M.Search.EOUT, PRIVW, FOUT])

theorem ClosedPost.tierPreserved {sk a : BitVec 256} {s t : MachineState}
    {rv : SharedForest.ForestOpening × SharedForest.PairRoot} {extra : Nat}
    (h : ClosedPost sk a s rv t)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s) :
    SigGolfCandidate.T3M.Sign.SharedTier.At extra t :=
  htier.frame h.frame
    (closedW_not_tier_cell _ (Or.inl rfl))
    (closedW_not_tier_cell _ (Or.inr (Or.inl rfl)))
    (closedW_not_tier_cell _ (Or.inr (Or.inr rfl)))

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
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_Main ====
section

macro "sign_slice_fast" : tactic => `(tactic|
  first
  | (apply SigGolfCandidate.T3M.codeAt_sign_last <;> decide +kernel)
  | (apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel))

-- Campaign T51 (as R6, D6): the dead legacy `ClaudeWCT.W9.Machine.Sign` cluster (coefs/coord/fts/rest/compaction,
-- `final_digests`, `rest_tbsim`, `sign_tbsim_w`, ...; no user) was removed.

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def code22128 : List (BitVec 32) := bv_list% 32 [0x21137,0x10113,0xf93,0x2b00d13,0xd93,0x8837,0xcb080813,0x700793,0xfff40313,0x2030063]
sym_block blk22128 := symRun { noAlias := true } code22128 (pcOf 22128) 100
def code22138 : List (BitVec 32) := bv_list% 32 [0x600793,0x8837,0xfd080813,0xffe40313,0x30663]
sym_block blk22138 := symRun { noAlias := true } code22138 (pcOf 22138) 100
def code22143 : List (BitVec 32) := bv_list% 32 [0x8837,0x2e080813]
sym_block blk22143 := symRun { noAlias := true } code22143 (pcOf 22143) 100
def code22145 : List (BitVec 32) := bv_list% 32 [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38c63]
sym_block blk22145 := symRun { noAlias := true } code22145 (pcOf 22145) 100
def code22150 : List (BitVec 32) := bv_list% 32 [0xffe40393,0x2038063]
sym_block blk22150 := symRun { noAlias := true } code22150 (pcOf 22150) 100
def code22152 : List (BitVec 32) := bv_list% 32 [0x3f37913,0x635493,0x200006f]
sym_block blk22152 := symRun { noAlias := true } code22152 (pcOf 22152) 100
def code22155 : List (BitVec 32) := bv_list% 32 [0xc35913,0x7f97913,0x1335493,0x100006f]
sym_block blk22155 := symRun { noAlias := true } code22155 (pcOf 22155) 100
def code22159 : List (BitVec 32) := bv_list% 32 [0x635913,0x3f97913,0xc35493]
sym_block blk22159 := symRun { noAlias := true } code22159 (pcOf 22159) 100
def code22162 : List (BitVec 32) := bv_list% 32 [0x90713,0x809eb0ef]
sym_block blk22162 := symRun { noAlias := true } code22162 (pcOf 22162) 100
structure Code (im : Image) : Prop where
  at22128 : CodeAt im (pcOf 22128) code22128
  at22138 : CodeAt im (pcOf 22138) code22138
  at22143 : CodeAt im (pcOf 22143) code22143
  at22145 : CodeAt im (pcOf 22145) code22145
  at22150 : CodeAt im (pcOf 22150) code22150
  at22152 : CodeAt im (pcOf 22152) code22152
  at22155 : CodeAt im (pcOf 22155) code22155
  at22159 : CodeAt im (pcOf 22159) code22159
  at22162 : CodeAt im (pcOf 22162) code22162
def sigBase (lay : Nat) : Nat := if lay=1 then 0x7cb0 else if lay=2 then 0x7fd0 else 0x82e0
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 1173
  ret : t.getReg .x1=pcOf 22164
  rootBase : t.getReg .x2=BitVec.ofNat 64 LOW
  so : t.getReg .x31=0
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  sigBase : t.getReg .x16=BitVec.ofNat 64 (SharedRootControl.sigBase lay)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  regs : RegsExcept s t [.x1,.x2,.x6,.x7,.x9,.x14,.x15,.x16,.x18,.x26,.x27,.x28,.x31]
  frame : Frame s t (fun _ => False)
theorem setup1 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=1)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 21 21 t ∧ Post 1 index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  let s1 := blk22128.res.toState s
  have st1 : Steps im s 10 10 s1 := symRun_sound blk22128 hc.at22128 s hp (by simp [blk22128.res,rv_simp])
  let s2 := blk22145.res.toState s1
  have st2 : Steps im s1 5 5 s2 := symRun_sound blk22145 hc.at22145 s1 (by simp [s1,s2,blk22128.res,blk22145.res,rv_simp,h8]) (by simp [blk22145.res,rv_simp])
  let s3 := blk22155.res.toState s2
  have st3 : Steps im s2 4 4 s3 := symRun_sound blk22155 hc.at22155 s2 (by simp [s1,s2,s3,blk22128.res,blk22145.res,blk22155.res,rv_simp,h8]) (by simp [blk22155.res,rv_simp])
  let s4 := blk22162.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22162 hc.at22162 s3 (by simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8]) (by simp [blk22162.res,rv_simp])
  refine ⟨s4, st1.trans (st2.trans (st3.trans (st4))), ?_⟩
  constructor
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change (BitVec.ofNat 64 index >>> (12 : Nat) &&& 127) = BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact ofNat_and_mask (index/2^12) 7 (by decide)
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change BitVec.ofNat 64 index >>> (19 : Nat) = BitVec.ofNat 64 (index/2^19)
    exact ofNat_shr index 19 (by omega)
  · intro r hr; cases r <;> simp_all [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW] <;> rfl
  · intro A hA hn; simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
theorem setup2 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=2)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 27 27 t ∧ Post 2 index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  let s1 := blk22128.res.toState s
  have st1 : Steps im s 10 10 s1 := symRun_sound blk22128 hc.at22128 s hp (by simp [blk22128.res,rv_simp])
  let s2 := blk22138.res.toState s1
  have st2 : Steps im s1 5 5 s2 := symRun_sound blk22138 hc.at22138 s1 (by simp [s1,s2,blk22128.res,blk22138.res,rv_simp,h8]) (by simp [blk22138.res,rv_simp])
  let s3 := blk22145.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22145 hc.at22145 s2 (by simp [s1,s2,s3,blk22128.res,blk22138.res,blk22145.res,rv_simp,h8]) (by simp [blk22145.res,rv_simp])
  let s4 := blk22150.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22150 hc.at22150 s3 (by simp [s1,s2,s3,s4,blk22128.res,blk22138.res,blk22145.res,blk22150.res,rv_simp,h8]) (by simp [blk22150.res,rv_simp])
  let s5 := blk22159.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22159 hc.at22159 s4 (by simp [s1,s2,s3,s4,s5,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,rv_simp,h8]) (by simp [blk22159.res,rv_simp])
  let s6 := blk22162.res.toState s5
  have st6 : Steps im s5 2 2 s6 := symRun_sound blk22162 hc.at22162 s5 (by simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8]) (by simp [blk22162.res,rv_simp])
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change (BitVec.ofNat 64 index >>> (6 : Nat) &&& 63) = BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact ofNat_and_mask (index/2^6) 6 (by decide)
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change BitVec.ofNat 64 index >>> (12 : Nat) = BitVec.ofNat 64 (index/2^12)
    exact ofNat_shr index 12 (by omega)
  · intro r hr; cases r <;> simp_all [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW] <;> rfl
  · intro A hA hn; simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
theorem setup3 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=3)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 29 29 t ∧ Post 3 index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  let s1 := blk22128.res.toState s
  have st1 : Steps im s 10 10 s1 := symRun_sound blk22128 hc.at22128 s hp (by simp [blk22128.res,rv_simp])
  let s2 := blk22138.res.toState s1
  have st2 : Steps im s1 5 5 s2 := symRun_sound blk22138 hc.at22138 s1 (by simp [s1,s2,blk22128.res,blk22138.res,rv_simp,h8]) (by simp [blk22138.res,rv_simp])
  let s3 := blk22143.res.toState s2
  have st3 : Steps im s2 2 2 s3 := symRun_sound blk22143 hc.at22143 s2 (by simp [s1,s2,s3,blk22128.res,blk22138.res,blk22143.res,rv_simp,h8]) (by simp [blk22143.res,rv_simp])
  let s4 := blk22145.res.toState s3
  have st4 : Steps im s3 5 5 s4 := symRun_sound blk22145 hc.at22145 s3 (by simp [s1,s2,s3,s4,blk22128.res,blk22138.res,blk22143.res,blk22145.res,rv_simp,h8]) (by simp [blk22145.res,rv_simp])
  let s5 := blk22150.res.toState s4
  have st5 : Steps im s4 2 2 s5 := symRun_sound blk22150 hc.at22150 s4 (by simp [s1,s2,s3,s4,s5,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,rv_simp,h8]) (by simp [blk22150.res,rv_simp])
  let s6 := blk22152.res.toState s5
  have st6 : Steps im s5 3 3 s6 := symRun_sound blk22152 hc.at22152 s5 (by simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,rv_simp,h8]) (by simp [blk22152.res,rv_simp])
  let s7 := blk22162.res.toState s6
  have st7 : Steps im s6 2 2 s7 := symRun_sound blk22162 hc.at22162 s6 (by simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8]) (by simp [blk22162.res,rv_simp])
  refine ⟨s7, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6.trans (st7)))))), ?_⟩
  constructor
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change (BitVec.ofNat 64 index &&& 63) = BitVec.ofNat 64 (index%2^6)
    exact ofNat_and_mask index 6 (by decide)
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change BitVec.ofNat 64 index >>> (6 : Nat) = BitVec.ofNat 64 (index/2^6)
    exact ofNat_shr index 6 (by omega)
  · intro r hr; cases r <;> simp_all [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW] <;> rfl
  · intro A hA hn; simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open Packed
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem setup {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (lay : Layer) (hlay : lay≠0) (index : Nat) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t k, Steps im s k k t ∧ k≤29 ∧ Post lay.val index s t := by
  fin_cases lay
  · exact (hlay rfl).elim
  · obtain ⟨t,hs,hp⟩ := setup1 hc s hp index hi h8 hidx
    exact ⟨t,21,hs,by decide,hp⟩
  · obtain ⟨t,hs,hp⟩ := setup2 hc s hp index hi h8 hidx
    exact ⟨t,27,hs,by decide,hp⟩
  · obtain ⟨t,hs,hp⟩ := setup3 hc s hp index hi h8 hidx
    exact ⟨t,29,hs,by decide,hp⟩

theorem Post.btPre {sk : SecretKey} {cache : Bytes 131072} {s t : MachineState}
    {lay : Layer} (hlay : lay≠0) {index : Nat} (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0)
    (h : Post lay.val index s t) :
    BtPre (cfFlag := cfFlag) sk cache lay (route index lay).2 (route index lay).1 [] (SharedRootControl.sigBase lay.val) t := by
  have leafEq : (if lay.val=1 then index/4096%128 else if lay.val=2 then index/64%64 else index%64)=(route index lay).1 := by
    fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height]
  have treeEq : (if lay.val=1 then index/524288 else if lay.val=2 then index/4096 else index/64)=(route index lay).2 := by
    fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height]
  have heightEq : (if lay.val=1 then 7 else 6)=SigGolfCandidate.T3.height lay := by
    fin_cases lay <;> simp_all [SigGolfCandidate.T3.height]
  refine
    { x2 := h.rootBase
      x8 := (h.regs.get (by decide)).trans h8
      x9 := by rw [h.tree,treeEq]
      x14 := by rw [h.selected,h.leaf,leafEq]
      x15 := by rw [h.height,heightEq]
      x16 := h.sigBase
      x26 := h.chains
      x27 := h.n4
      x31 := h.so
      base := hb.frame h.frame h.regs (by decide) (fun _ _ _ he => he)
      hlay := hlay
      htree := by fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height] <;> omega
      hroute := by intro l hl; fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height] <;> omega
      hsel := by fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height] <;> omega
      hdb := by simp
      digits := by intro i hi; rw [h.frame.getByte (by unfold DIGITS; omega) (fun he => he)]; simpa using hz i hi
      hsb := by fin_cases lay <;> simp_all [SharedRootControl.sigBase,SigGolfCandidate.T3.height,SIG] <;> decide
      hsb8 := by fin_cases lay <;> decide }
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def frontCode : List (BitVec 32) := bv_list% 32 [0x300413,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block front := symRun { noAlias := true } frontCode (pcOf 22100) 100
def zeroCode : List (BitVec 32) := bv_list% 32 [0x20e37,0x420e0e13,0xe3023,0xe3423,0xe3823,0xe3c23,0x20e3023,0x20e3423,0x20e3823]
sym_block zero := symRun { noAlias := true } zeroCode (pcOf 22115) 100
def hintCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xe3023,0x100413]
sym_block hint := symRun { noAlias := true } hintCode (pcOf 22124) 100
def donePrepCode : List (BitVec 32) := bv_list% 32 [0xfff40f13,0x66eb7,0x40e8e93,0x5f1393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block donePrep := symRun { noAlias := true } donePrepCode (pcOf 22164) 100
def doneExitCode : List (BitVec 32) := bv_list% 32 [0x140413,0x400313,0xf26466e3]
sym_block doneExit := symRun { noAlias := true } doneExitCode (pcOf 22179) 100
theorem front_steps {im : Image} (hc : CodeAt im (pcOf 22100) frontCode)
    (s : MachineState) (hp : s.pc=pcOf 22100) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=pcOf 22107 ∧ t.getReg .x8=3 ∧
      t.getReg .x28=BitVec.ofNat 64 ENC ∧ t.getReg .x29=BitVec.ofNat 64 (0x66000+160) ∧
      RegsExcept s t [.x7,.x8,.x28,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound front hc s hp (by simp [front.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [front.res,rv_simp]
  · simp [front.res,rv_simp]
  · simp [front.res,rv_simp,ENC]
  · simp [front.res,rv_simp]
  · intro r hr; cases r <;> simp_all [front.res,rv_simp] <;> rfl
  · intro A hA hn; simp [front.res,rv_simp]

theorem zero_steps {im : Image} (hc : CodeAt im (pcOf 22115) zeroCode)
    (s : MachineState) (hp : s.pc=pcOf 22115) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 22124 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=0) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56) := by
  refine ⟨_,symRun_sound zero hc s hp (by simp [zero.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero.res,rv_simp]
  · intro i hi; interval_cases i <;> simp [zero.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp_all [zero.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,zero.res]
    t3n [DIGITS]
    repeat rw [if_neg (by unfold DIGITS at hn; omega)]

theorem hint_steps {im : Image} (hc : CodeAt im (pcOf 22124) hintCode)
    (s : MachineState) (hp : s.pc=pcOf 22124) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf 22128 ∧ t.getReg .x8=1 ∧ t.getMem (0x66000#64)=0 ∧
      RegsExcept s t [.x8,.x28] ∧ Frame s t (fun A => A=0x66000) := by
  refine ⟨_,symRun_sound hint hc s hp (by simp [hint.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [hint.res,rv_simp]
  · simp [hint.res,rv_simp]
  · simp [hint.res,rv_simp]
  · intro r hr; cases r <;> simp_all [hint.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,hint.res]
    t3n []
    rw [if_neg (by omega)]

theorem donePrep_steps {im : Image} (hc : CodeAt im (pcOf 22164) donePrepCode)
    (s : MachineState) (hp : s.pc=pcOf 22164) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=pcOf 22171 ∧ t.getReg .x28=BitVec.ofNat 64 ENC ∧
      t.getReg .x29=BitVec.ofNat 64 (0x66000+64+32*(lay-1)) ∧
      RegsExcept s t [.x7,.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound donePrep hc s hp (by simp [donePrep.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [donePrep.res,rv_simp]
  · simp [donePrep.res,rv_simp,ENC]
  · interval_cases lay <;> simp_all [donePrep.res,rv_simp]
  · intro r hr; cases r <;> simp_all [donePrep.res,rv_simp] <;> rfl
  · intro A hA hn; simp [donePrep.res,rv_simp]

theorem doneExit_steps {im : Image} (hc : CodeAt im (pcOf 22179) doneExitCode)
    (s : MachineState) (hp : s.pc=pcOf 22179) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22128 else pcOf 22182) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧
      RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound doneExit hc s hp (by simp [doneExit.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [doneExit.res,rv_simp,pcOf]
  · interval_cases lay <;> simp_all [doneExit.res,rv_simp]
  · intro r hr; cases r <;> simp_all [doneExit.res,rv_simp] <;> rfl
  · intro A hA hn; simp [doneExit.res,rv_simp]
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def copy22107Code : List (BitVec 32) := bv_list% 32 [0xe3303,0x8e3383,0x6eb023,0x7eb423,0x30e3303,0x38e3383,0x6eb823,0x7ebc23]
sym_block copy22107 := symRun { noAlias := true } copy22107Code (pcOf 22107) 100
theorem copy22107_steps {im : Image} (hc : CodeAt im (pcOf 22107) copy22107Code)
    (s : MachineState) (hp : s.pc=pcOf 22107) (dest : Nat) (ha : 0x66000≤dest) (hb : dest+32≤0x66200) (ha8 : dest%8=0)
    (hd : dest=0x66040 ∨ dest=0x66060 ∨ dest=0x66080 ∨ dest=0x660a0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 dest)
    (left right : Digest) (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 8 8 t ∧ t.pc=pcOf 22115 ∧ DigAt t dest left ∧ DigAt t (dest+16) right ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => dest≤A ∧ A<dest+32) := by
  rcases hd with rfl|rfl|rfl|rfl
  all_goals
    have ho : Oblig.all s copy22107.res.st.obl := by
      simp [copy22107.res,rv_simp,h28,h29,ENC]
      decide
    refine ⟨_,symRun_sound copy22107 hc s hp ho,?_,?_,?_,?_,?_⟩
    · simp [copy22107.res,rv_simp]
    · constructor
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.1
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.2
    · constructor
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.1
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.2
    · intro r hr; cases r <;> simp at hr <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem,copy22107.res]
      t3n [h28,h29,ENC]
      repeat rw [if_neg (by omega)]
def copy22171Code : List (BitVec 32) := bv_list% 32 [0xe3303,0x8e3383,0x6eb023,0x7eb423,0x30e3303,0x38e3383,0x6eb823,0x7ebc23]
sym_block copy22171 := symRun { noAlias := true } copy22171Code (pcOf 22171) 100
theorem copy22171_steps {im : Image} (hc : CodeAt im (pcOf 22171) copy22171Code)
    (s : MachineState) (hp : s.pc=pcOf 22171) (dest : Nat) (ha : 0x66000≤dest) (hb : dest+32≤0x66200) (ha8 : dest%8=0)
    (hd : dest=0x66040 ∨ dest=0x66060 ∨ dest=0x66080 ∨ dest=0x660a0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 dest)
    (left right : Digest) (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 8 8 t ∧ t.pc=pcOf 22179 ∧ DigAt t dest left ∧ DigAt t (dest+16) right ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => dest≤A ∧ A<dest+32) := by
  rcases hd with rfl|rfl|rfl|rfl
  all_goals
    have ho : Oblig.all s copy22171.res.st.obl := by
      simp [copy22171.res,rv_simp,h28,h29,ENC]
      decide
    refine ⟨_,symRun_sound copy22171 hc s hp ho,?_,?_,?_,?_,?_⟩
    · simp [copy22171.res,rv_simp]
    · constructor
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.1
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.2
    · constructor
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.1
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.2
    · intro r hr; cases r <;> simp at hr <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem,copy22171.res]
      t3n [h28,h29,ENC]
      repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure ExtraCode (im : Image) : Prop where
  front : CodeAt im (pcOf 22100) frontCode
  copyA : CodeAt im (pcOf 22107) copy22107Code
  zero : CodeAt im (pcOf 22115) zeroCode
  hint : CodeAt im (pcOf 22124) hintCode
  donePrep : CodeAt im (pcOf 22164) donePrepCode
  copyB : CodeAt im (pcOf 22171) copy22171Code
  doneExit : CodeAt im (pcOf 22179) doneExitCode

theorem entry_steps {im : Image} (hc : ExtraCode im)
    (s : MachineState) (hp : s.pc=pcOf 22100) (left right : Digest)
    (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 28 28 t ∧ t.pc=pcOf 22128 ∧ t.getReg .x8=1 ∧
      DigAt t (0x66000+160) left ∧ DigAt t (0x66000+176) right ∧
      t.getMem (0x66000#64)=0 ∧
      (∀ i,i<43 → t.getByte (BitVec.ofNat 64 (DIGITS+i))=0) ∧
      RegsExcept s t [.x6,.x7,.x8,.x28,.x29] ∧
      Frame s t (fun A => A=0x66000 ∨ 0x66000+160≤A ∧ A<0x66000+192 ∨ DIGITS≤A ∧ A<DIGITS+56) := by
  obtain ⟨a,sa,pa,a8,a28,a29,ar,af⟩ := front_steps hc.front s hp
  obtain ⟨b,ab,pb,bl,br,brs,bf⟩ := copy22107_steps hc.copyA a pa (0x66000+160)
    (by decide) (by decide) (by decide) (by decide) a28 a29 left right
    (hl.frame af (by decide) (fun h => h) (fun h => h))
    (hr.frame af (by decide) (fun h => h) (fun h => h))
  obtain ⟨c,bc,pc,cz,cr,cf⟩ := zero_steps hc.zero b pb
  obtain ⟨t,ct,pt,t8,th,tr,tf⟩ := hint_steps hc.hint c pc
  have ft : Frame b t (fun A => DIGITS≤A ∧ A<DIGITS+56 ∨ A=0x66000) := (cf.trans tf).mono (by tauto)
  refine ⟨t,sa.trans (ab.trans (bc.trans ct)),pt,t8,?_,?_,th,?_,?_,?_⟩
  · exact bl.frame ft (by decide) (by unfold DIGITS; omega) (by unfold DIGITS; omega)
  · exact br.frame ft (by decide) (by unfold DIGITS; omega) (by unfold DIGITS; omega)
  · intro i hi
    rw [tf.getByte (by unfold DIGITS; omega) (by unfold DIGITS; omega)]
    rw [getByte_eq_word c (DIGITS+i) (by unfold DIGITS; omega)]
    rw [show (DIGITS+i)/8*8=DIGITS+8*(i/8) by unfold DIGITS; omega,cz _ (by omega)]
    simp [extractByte]
  · exact (((ar.trans brs).trans cr).trans tr).mono (by simp)
  · exact (((af.trans bf).trans cf).trans tf).mono (by intros A hA hw; rcases hw with ((hw|hw)|hw)|hw <;> tauto)

theorem done_steps {im : Image} (hc : ExtraCode im)
    (s : MachineState) (hp : s.pc=pcOf 22164) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (left right : Digest)
    (hleft : DigAt s ENC left) (hright : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=(if lay<3 then pcOf 22128 else pcOf 22182) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧
      DigAt t (0x66000+64+32*(lay-1)) left ∧ DigAt t (0x66000+80+32*(lay-1)) right ∧
      RegsExcept s t [.x6,.x7,.x8,.x28,.x29,.x30] ∧
      Frame s t (fun A => 0x66000+64+32*(lay-1)≤A ∧ A<0x66000+96+32*(lay-1)) := by
  obtain ⟨a,sa,pa,a28,a29,ar,af⟩ := donePrep_steps hc.donePrep s hp lay hl hh h8
  obtain ⟨b,ab,pb,bl,br,brs,bf⟩ := copy22171_steps hc.copyB a pa (0x66000+64+32*(lay-1))
    (by omega) (by omega) (by omega) (by interval_cases lay <;> decide) a28 a29 left right
    (hleft.frame af (by decide) (fun h => h) (fun h => h))
    (hright.frame af (by decide) (fun h => h) (fun h => h))
  have b8 : b.getReg .x8=BitVec.ofNat 64 lay := (brs.get (by decide)).trans ((ar.get (by decide)).trans h8)
  obtain ⟨t,bt,pt,t8,tr,tf⟩ := doneExit_steps hc.doneExit b pb lay hl hh b8
  refine ⟨t,sa.trans (ab.trans bt),pt,t8,bl.frame tf (by omega) (fun h => h) (fun h => h),?_,?_,?_⟩
  · have h := br.frame tf (by omega) (fun h => h) (fun h => h)
    convert h using 1 <;> omega
  · exact ((ar.trans brs).trans tr).mono (by simp)
  · exact ((af.trans bf).trans tf).mono (by
      intros A hA hw
      rcases hw with (hw|hw)|hw
      · exact hw.elim
      · omega
      · exact hw.elim)
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_extraCode : ExtraCode Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
abbrev buffer (lay i d : Nat) : Nat := 0x6e000+8192*lay+128*i+16*d
def stepCode : List (BitVec 32) := bv_list% 32 [0x431313,0x6c0e33,0xe3303,0x8e3383,0x6bb023,0x7bb423,0x1b0b13,0x10b8b93,0x80c0c13,0x1a8a93,0x2b00313,0xfc6ae8e3]
sym_block step := symRun { noAlias := true } stepCode (pcOf 22436) 100

theorem step_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (s : MachineState) (hp : s.pc=pcOf 22436) (lay i d sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hi : i<43) (hd : d<8)
    (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (h6 : s.getReg .x6=BitVec.ofNat 64 d) (h21 : s.getReg .x21=BitVec.ofNat 64 i)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (h23 : s.getReg .x23=BitVec.ofNat 64 (sb+16*i))
    (h24 : s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0)) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=(if i+1<43 then pcOf 22435 else pcOf 22448) ∧
      t.getReg .x21=BitVec.ofNat 64 (i+1) ∧ t.getReg .x22=BitVec.ofNat 64 (DIGITS+i+1) ∧
      t.getReg .x23=BitVec.ofNat 64 (sb+16*(i+1)) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay (i+1) 0) ∧
      t.getMem (BitVec.ofNat 64 (sb+16*i))=s.getMem (BitVec.ofNat 64 (buffer lay i d)) ∧
      t.getMem (BitVec.ofNat 64 (sb+16*i+8))=s.getMem (BitVec.ofNat 64 (buffer lay i d+8)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => A=sb+16*i ∨ A=sb+16*i+8) := by
  have ho : Oblig.all s step.res.st.obl := by
    simp only [step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    omega
  refine ⟨_,symRun_sound step hc s hp ho,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS,pcOf]
    simp [BitVec.ult,toNat_ofNat_lt (show i+1<2^64 by omega)]
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    omega
  · simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    rw [if_neg (by omega),if_pos (by omega)]
    simp [Nat.mul_comm]
  · simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    simp [Nat.mul_comm]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    rw [if_neg (by omega),if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem byte_steps {im : Image} (hc : CodeAt im (pcOf 22435) [0xb4303])
    (s : MachineState) (hp : s.pc=pcOf 22435) (i d : Nat) (hi : i<43) (hd : d<8)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 d) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22436 ∧ t.getReg .x6=BitVec.ofNat 64 d ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x22+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 (DIGITS+i) := by
    rw [h22]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x6) (rs := .x22) (off := 0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by unfold DIGITS; omega)]; simp [MEMORY_BYTES,DIGITS]; omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 22436; rw [hp]; rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn; simp

theorem iteration_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303])
    (s : MachineState) (hp : s.pc=pcOf 22435) (lay i d sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hi : i<43) (hd : d<8)
    (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (h21 : s.getReg .x21=BitVec.ofNat 64 i)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (h23 : s.getReg .x23=BitVec.ofNat 64 (sb+16*i))
    (h24 : s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 d)
    (v : Digest) (hv : DigAt s (buffer lay i d) v) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=(if i+1<43 then pcOf 22435 else pcOf 22448) ∧
      t.getReg .x21=BitVec.ofNat 64 (i+1) ∧ t.getReg .x22=BitVec.ofNat 64 (DIGITS+i+1) ∧
      t.getReg .x23=BitVec.ofNat 64 (sb+16*(i+1)) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay (i+1) 0) ∧
      DigAt t (sb+16*i) v ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => A=sb+16*i ∨ A=sb+16*i+8) := by
  obtain ⟨a,sa,ap,a6,ar,af⟩ := byte_steps hbcode s hp i d hi hd h22 hb
  obtain ⟨t,aToT,tp,t21,t22,t23,t24,tl,tr,ts,tf⟩ := step_steps hc a ap lay i d sb hl hh hi hd hsb hsb' hsb8
    a6 ((ar.get (by decide)).trans h21) ((ar.get (by decide)).trans h22)
    ((ar.get (by decide)).trans h23) ((ar.get (by decide)).trans h24)
  have va := hv.frame af (by unfold buffer; omega) (fun h => h) (fun h => h)
  exact ⟨t,sa.trans aToT,tp,t21,t22,t23,t24,⟨tl.trans va.1,tr.trans va.2⟩,
    (ar.trans ts).mono (by simp),(af.trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem loop_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (lay sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (digits : Nat→Nat) (prefixes : Nat→Nat→Digest) (hd : ∀ j,j<43 → digits j<8) :
    ∀ count i, i+count=43 → ∀ s : MachineState,
      s.pc=(if i<43 then pcOf 22435 else pcOf 22448) →
      s.getReg .x21=BitVec.ofNat 64 i → s.getReg .x22=BitVec.ofNat 64 (DIGITS+i) →
      s.getReg .x23=BitVec.ofNat 64 (sb+16*i) →
      s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0) →
      (∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits j)) →
      (∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay j d) (prefixes j d)) →
      ∃ t, Steps im s (13*count) (13*count) t ∧ t.pc=pcOf 22448 ∧
        (∀ j,i≤j → j<43 → DigAt t (sb+16*j) (prefixes j (digits j))) ∧
        RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
        Frame s t (fun A => sb+16*i≤A ∧ A<sb+16*43) := by
  intro count
  induction count with
  | zero =>
      intro i hi s hp h21 h22 h23 h24 hb hv
      have hi' : i=43 := by omega
      refine ⟨s,Steps.refl _,by simpa [hi'] using hp,?_,?_,?_⟩
      · intro j hj hj'; omega
      · intro r hr; rfl
      · intro A hA hn; rfl
  | succ count ih =>
      intro i hcount s hp h21 h22 h23 h24 hb hv
      have hi : i<43 := by omega
      obtain ⟨a,sa,ap,a21,a22,a23,a24,av,ar,af⟩ := iteration_steps hc hbcode s
        (by simpa [hi] using hp) lay i (digits i) sb hl hh hi (hd i hi) hsb hsb' hsb8
        h21 h22 h23 h24 (hb i hi) (prefixes i (digits i)) (hv i hi _ (hd i hi))
      obtain ⟨t,aToT,tp,tv,tr,tf⟩ := ih (i+1) (by omega) a ap a21
        (by simpa [Nat.add_assoc] using a22) a23 a24
        (by
          intro j hj
          rw [af.getByte (by unfold DIGITS; omega) (by unfold DIGITS; omega)]
          exact hb j hj)
        (by
          intro j hj d hd
          exact (hv j hj d hd).frame af (by unfold buffer; omega)
            (by unfold buffer; omega) (by unfold buffer; omega))
      refine ⟨t,?_,tp,?_,(ar.trans tr).mono (by simp),?_⟩
      · convert sa.trans aToT using 1 <;> omega
      · intro j hij hj
        by_cases he : j=i
        · subst j
          exact av.frame tf (by omega) (by omega) (by omega)
        · exact tv j (by omega) hj
      · exact (af.trans tf).mono (by intro A hA h; rcases h with h|h <;> omega)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def metaAddr (lay : Layer) : Nat := 0x66000+64+32*(lay.val-1)
def metaW (lay : Layer) (A : Nat) : Prop := metaAddr lay≤A ∧ A < metaAddr lay+32
structure Stored (lay : Layer) (index : Nat) (p : PreparedLower) (t : MachineState) : Prop where
  plen : p.prefixes.length=43
  saved : ∀ i,i<43 → ∀ k,k≤7 → DigAt t (SharedPrefixes.buffer lay.val i k) ((p.prefixes.getD i []).getD k 0)
  path : DigsAt t (sigBase lay.val+16*43) ((List.range (height lay)).map fun j => (p.levels.getD j []).getD ((route index lay).1/2^j ^^^ 1) 0)
  left : DigAt t (metaAddr lay) (topPair lay p.levels).1
  right : DigAt t (metaAddr lay+16) (topPair lay p.levels).2
structure OnePost (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (index : Nat)
    (s : MachineState) (p : PreparedLower) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=(if lay.val<3 then pcOf 22128 else pcOf 22182)
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  zero : ∀ i,i<43 → t.getByte (BitVec.ofNat 64 (DIGITS+i))=0
  stored : Stored lay index p t
  frame : Frame s t (fun A => SharedLowTree.AllW lay (route index lay).2 (sigBase lay.val) A ∨ metaW lay A)
  precise : Frame s t (fun A => SharedLowTree.TreeWrites lay A ∨ metaW lay A)

theorem one_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hlay : lay≠0) {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (btCost+47) (buildTreePrefixes lay (route index lay).2 (route index lay).1)
      (OnePost (cfFlag := cfFlag) sk cache lay index s) := by
  have h0 : lay.val≠0 := fun h => hlay (Fin.ext h)
  have hl := lay.isLt
  obtain ⟨a,k,sa,hk,ha⟩ := setup hc s hpc lay hlay index hi h8 hidx
  have hpre := ha.btPre hlay hi h8 hb hz
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (ha.frame.get (by decide) (fun h => h)).trans hidx
  have hsel : SharedPrefixes.selectionWord (a.getMem 0x20550) lay.val=BitVec.ofNat 64 (route index lay).1 := by
    rw [aidx]; exact SharedPrefixes.selection_route index hi lay hlay
  have ht := SharedLowTree.buildTreePrefixes_tbsim hlow hlevels hsub hcopy hchain hpref hseed hhook
    hpre ha.pc ha.ret hsel
  refine TBSim.mono (TBSim.steps sa (TBSim.post_steps (k := 18) (c := 18) ht (fun p u hu => ?_))) (by omega) (fun _ _ h => h)
  have u8 : u.getReg .x8=BitVec.ofNat 64 lay.val := (hu.regs.get (by decide)).trans hpre.x8
  obtain ⟨t,ut,pt,t8,tl,tr,trs,tf⟩ := done_steps he u hu.pc lay.val (by omega) (by omega) u8
    (topPair lay p.levels).1 (topPair lay p.levels).2 hu.left hu.right
  have tf' : Frame u t (metaW lay) := tf.mono (by unfold metaW metaAddr; intros A hA h; omega)
  have fm : Frame s t (fun A => SharedLowTree.AllW lay (route index lay).2 (sigBase lay.val) A ∨ metaW lay A) :=
    ((ha.frame.trans hu.frame).trans tf').mono (by intros A hA h; rcases h with (h|h)|h <;> tauto)
  refine ⟨t,ut,pt,t8,?_,?_,?_,?_,fm,?_⟩
  · exact hu.base.frame tf' trs (by decide) (by
      intro A hA hb hw
      unfold BaseA NeverW at hb
      unfold metaW metaAddr at hw
      simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA] at hb
      omega)
  · change t.getMem (BitVec.ofNat 64 0x20550)=BitVec.ofNat 64 index
    rw [fm.get (A := 0x20550) (by decide) ?_]; exact hidx
    unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
    fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT]
  · intro i hI
    rw [fm.getByte (by unfold DIGITS; omega) ?_]; exact hz i hI
    unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
    fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT,DIGITS] <;> omega
  · refine ⟨hu.plen,?_,?_,?_,?_⟩
    · intro i hI j hj
      have hbound := SharedPrefixes.buffer_bounds (by omega : 1≤lay.val) (by omega : lay.val≤3) hI (by omega : j<8)
      exact (hu.saved i hI j hj).frame tf' (by omega) (by unfold metaW metaAddr; omega) (by unfold metaW metaAddr; omega)
    · refine hu.path.frame tf' ?_ ?_
      · simp only [List.length_map,List.length_range]; fin_cases lay <;> decide
      · intro A hA hA'
        simp only [List.length_map,List.length_range] at hA'
        unfold metaW metaAddr
        fin_cases lay <;> simp_all [sigBase,height] <;> omega
    · exact tl
    · convert tr using 1 <;> unfold metaAddr <;> omega
  · exact ((ha.frame.trans hu.precise).trans tf').mono (by intros A hA h; rcases h with (h|h)|h <;> tauto)
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def setupACode : List (BitVec 32) := bv_list% 32 [0xa93,0x20b37,0x420b0b13,0x8bb7,0xcb0b8b93,0xfff40313,0x30e63]
sym_block setupA := symRun { noAlias := true } setupACode (pcOf 22418) 100
def setupBCode : List (BitVec 32) := bv_list% 32 [0x8bb7,0xfd0b8b93,0xffe40313,0x30663]
sym_block setupB := symRun { noAlias := true } setupBCode (pcOf 22425) 100
def setupCCode : List (BitVec 32) := bv_list% 32 [0x8bb7,0x2e0b8b93]
sym_block setupC := symRun { noAlias := true } setupCCode (pcOf 22429) 100
def setupDCode : List (BitVec 32) := bv_list% 32 [0x6ec37,0xc0c13,0xd41313,0x6c0c33]
sym_block setupD := symRun { noAlias := true } setupDCode (pcOf 22431) 100
def sigBase (lay : Nat) : Nat := if lay=1 then 0x7cb0 else if lay=2 then 0x7fd0 else 0x82e0
structure SetupCode (im : Image) : Prop where
  a : CodeAt im (pcOf 22418) setupACode
  b : CodeAt im (pcOf 22425) setupBCode
  c : CodeAt im (pcOf 22429) setupCCode
  d : CodeAt im (pcOf 22431) setupDCode
theorem setupA_steps {im : Image} (hc : CodeAt im (pcOf 22418) setupACode)
    (s : MachineState) (hp : s.pc=pcOf 22418) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=(if lay=1 then pcOf 22431 else pcOf 22425) ∧ t.getReg .x21=0 ∧ t.getReg .x22=BitVec.ofNat 64 DIGITS ∧ t.getReg .x23=BitVec.ofNat 64 0x7cb0 ∧ RegsExcept s t [.x6,.x21,.x22,.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupA hc s hp (by simp [setupA.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupA.res,rv_simp]
theorem setupB_steps {im : Image} (hc : CodeAt im (pcOf 22425) setupBCode)
    (s : MachineState) (hp : s.pc=pcOf 22425) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=(if lay=2 then pcOf 22431 else pcOf 22429) ∧ t.getReg .x23=BitVec.ofNat 64 0x7fd0 ∧ RegsExcept s t [.x6,.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupB hc s hp (by simp [setupB.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupB.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupB.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupB.res,rv_simp]
theorem setupC_steps {im : Image} (hc : CodeAt im (pcOf 22429) setupCCode)
    (s : MachineState) (hp : s.pc=pcOf 22429)  :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22431 ∧ t.getReg .x23=BitVec.ofNat 64 0x82e0 ∧ RegsExcept s t [.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupC hc s hp (by simp [setupC.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [setupC.res,rv_simp]
  · simp [setupC.res,rv_simp]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupC.res,rv_simp]
theorem setupD_steps {im : Image} (hc : CodeAt im (pcOf 22431) setupDCode)
    (s : MachineState) (hp : s.pc=pcOf 22431) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf 22435 ∧ t.getReg .x24=BitVec.ofNat 64 (buffer lay 0 0) ∧ RegsExcept s t [.x6,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupD hc s hp (by simp [setupD.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupD.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupD.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupD.res,rv_simp]
theorem setup_steps {im : Image} (hc : SetupCode im)
    (s : MachineState) (hp : s.pc=pcOf 22418) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t k, Steps im s k k t ∧ k≤17 ∧ t.pc=pcOf 22435 ∧ t.getReg .x21=0 ∧
      t.getReg .x22=BitVec.ofNat 64 DIGITS ∧ t.getReg .x23=BitVec.ofNat 64 (sigBase lay) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay 0 0) ∧
      RegsExcept s t [.x6,.x21,.x22,.x23,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨a,sa,ap,a21,a22,a23,ar,af⟩ := setupA_steps hc.a s hp lay hl hh h8
  have a8 := (ar.get (by decide)).trans h8
  interval_cases lay
  · obtain ⟨t,at',tp,t24,tr,tf⟩ := setupD_steps hc.d a (by simpa using ap) 1 (by decide) (by decide) a8
    exact ⟨t,11,sa.trans at',by decide,tp,(tr.get (by decide)).trans a21,(tr.get (by decide)).trans a22,
      (tr.get (by decide)).trans a23,t24,(ar.trans tr).mono (by simp),(af.trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b23,br,bf⟩ := setupB_steps hc.b a (by simpa using ap) 2 (by decide) (by decide) a8
    obtain ⟨t,bt,tp,t24,tr,tf⟩ := setupD_steps hc.d b (by simpa using bp) 2 (by decide) (by decide) ((br.get (by decide)).trans a8)
    exact ⟨t,15,sa.trans (ab.trans bt),by decide,tp,
      (tr.get (by decide)).trans ((br.get (by decide)).trans a21),
      (tr.get (by decide)).trans ((br.get (by decide)).trans a22),
      (tr.get (by decide)).trans b23,t24,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b23,br,bf⟩ := setupB_steps hc.b a (by simpa using ap) 3 (by decide) (by decide) a8
    obtain ⟨c,bc,cp,c23,cr,cf⟩ := setupC_steps hc.c b (by simpa using bp)
    obtain ⟨t,ct,tp,t24,tr,tf⟩ := setupD_steps hc.d c cp 3 (by decide) (by decide)
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a8))
    exact ⟨t,17,sa.trans (ab.trans (bc.trans ct)),by decide,tp,
      (tr.get (by decide)).trans ((cr.get (by decide)).trans ((br.get (by decide)).trans a21)),
      (tr.get (by decide)).trans ((cr.get (by decide)).trans ((br.get (by decide)).trans a22)),
      (tr.get (by decide)).trans c23,t24,(((ar.trans br).trans cr).trans tr).mono (by simp),
      (((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem reveal_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (hsetup : SetupCode im)
    (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (digits : Nat→Nat) (prefixes : Nat→Nat→Digest) (hd : ∀ j,j<43 → digits j<8)
    (s : MachineState) (hp : s.pc=pcOf 22418) (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits j))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay j d) (prefixes j d)) :
    ∃ t k, Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (sigBase lay) ((List.range 43).map fun i => prefixes i (digits i)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => sigBase lay≤A ∧ A<sigBase lay+688) := by
  obtain ⟨a,k,sa,hk,ap,a21,a22,a23,a24,ar,af⟩ := setup_steps hsetup s hp lay hl hh h8
  obtain ⟨t,aToT,tp,tv,tr,tf⟩ := loop_steps hc hbcode lay (sigBase lay) hl hh
    (by interval_cases lay <;> decide) (by interval_cases lay <;> decide) (by interval_cases lay <;> decide)
    digits prefixes hd 43 0 (by decide) a (by simpa using ap) a21
    (by simpa using a22) (by simpa using a23) a24
    (by intro j hj; rw [af.getByte (by unfold DIGITS; omega) (fun h => h)]; exact hb j hj)
    (by intro j hj d hd; exact (hv j hj d hd).frame af (by unfold buffer; omega) (fun h => h) (fun h => h))
  refine ⟨t,k+559,sa.trans aToT,by omega,tp,?_,(ar.trans tr).mono (by simp),?_⟩
  · intro i hi
    have hi' : i<43 := by simpa using hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,List.getElem_range]
    exact tv i (by omega) hi'
  · exact (af.trans tf).mono (by intro A hA h; rcases h with h|h; exact h.elim; simpa using h)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_setupCode : SetupCode Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
theorem installed_byteCode : CodeAt Images.signImage (pcOf 22435) [0xb4303] := by
  sign_slice_fast
theorem installed_stepCode : CodeAt Images.signImage (pcOf 22436) stepCode := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem Stored.after {sk : SecretKey} {cache : Bytes 131072} {index : Nat} {lay other : Layer}
    (hl : lay≠0) (ho : other≠0) (hne : lay≠other) {s t : MachineState} {p q : PreparedLower}
    (h : Stored other index p s) (ht : OnePost (cfFlag := cfFlag) sk cache lay index s q t) : Stored other index p t := by
  have hl0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have ho0 : other.val≠0 := fun h => ho (Fin.ext h)
  have hlb := lay.isLt
  have hob := other.isLt
  refine ⟨h.plen,?_,?_,?_,?_⟩
  · intro i hi k hk
    have b := SharedPrefixes.buffer_bounds (by omega : 1≤other.val) (by omega : other.val≤3) hi (by omega : k<8)
    refine (h.saved i hi k hk).frame ht.precise (by omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_other_prefix lay other hne ho (i := i) (k := k) hi (by omega) 0 (by decide) (by simpa using ha)
      · unfold metaW metaAddr at ha; omega
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_other_prefix lay other hne ho (i := i) (k := k) hi (by omega) 1 (by decide) (by simpa using ha)
      · unfold metaW metaAddr at ha; omega
  · refine h.path.frame ht.frame ?_ ?_
    · simp only [List.length_map,List.length_range]; fin_cases other <;> decide
    · intro A ha hw
      simp only [List.length_map,List.length_range] at hw
      unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
      fin_cases lay <;> fin_cases other <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT] <;> omega
  · refine h.left.frame ht.precise (by unfold metaAddr; omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
  · refine h.right.frame ht.precise (by unfold metaAddr; omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def RootsWrites (A : Nat) : Prop := A < 0x66000 ∨ (0x66040≤A ∧ A<0x660a0) ∨ (0x70000≤A ∧ A<0x76000)
structure RootsPost (sk : SecretKey) (cache : Bytes 131072) (index : Nat)
    (s : MachineState) (p : PreparedRoots) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=pcOf 22182
  layer : t.getReg .x8=4
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  one : Stored 1 index p.one t
  two : Stored 2 index p.two t
  three : Stored 3 index p.three t
  frame : Frame s t RootsWrites
  counterMem : t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32))
  tier : ∀ extra, SigGolfCandidate.T3M.Sign.SharedTier.At extra s →
    SigGolfCandidate.T3M.Sign.SharedTier.At extra t

theorem OnePost.counterMem {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) :
    t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32)) := by
  apply h.frame.get (by unfold ENC; decide)
  unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
  fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT] <;> omega

theorem OnePost.tierPreserved {sk : SecretKey} {cache : Bytes 131072}
    {lay : Layer} (hl : lay ≠ 0) {index : Nat} {s t : MachineState}
    {p : PreparedLower} {extra : Nat}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s) :
    SigGolfCandidate.T3M.Sign.SharedTier.At extra t := by
  refine ⟨?_,?_,?_⟩
  · exact (h.frame.get (A := EOUT + 32) (by unfold EOUT; decide) (by
      unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
      fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,EOUT,NODE,NOUT]
        <;> omega)).trans htier.low
  · exact (h.frame.get (A := EOUT + 40) (by unfold EOUT; decide) (by
      unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
      fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,EOUT,NODE,NOUT]
        <;> omega)).trans htier.high
  · exact (h.precise.get (A := 0x66028) (by decide) (by
      unfold SharedLowTree.TreeWrites metaW metaAddr
      fin_cases lay <;> simp_all <;> omega)).trans htier.pool

theorem OnePost.rootsFrame {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower} (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) :
    Frame s t RootsWrites := by
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have hbound := lay.isLt
  exact h.precise.mono (by unfold SharedLowTree.TreeWrites metaW metaAddr RootsWrites; intros A hA h; omega)

theorem prepareRoots_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=1) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (3*(btCost+47)) (prepareRoots index) (RootsPost (cfFlag := cfFlag) sk cache index s) := by
  have r1 := one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    (lay := 1) (by decide) hi s hpc h8 hidx hb hz
  unfold prepareRoots
  refine TBSim.mono (TBSim.bind r1 (fun p1 t1 h1 =>
    TBSim.bind (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
      (lay := 2) (by decide) hi t1 (by simpa using h1.pc) h1.layer h1.indexMem h1.base h1.zero)
      (fun p2 t2 h2 => TBSim.bind
        (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
          (lay := 3) (by decide) hi t2 (by simpa using h2.pc) h2.layer h2.indexMem h2.base h2.zero)
        (fun p3 t3 h3 => TBSim.pure ?_)))) (by omega) (fun _ _ h => h)
  refine ⟨by simpa using h3.pc,by simpa using h3.layer,h3.base,h3.indexMem,?_,?_,h3.stored,?_,?_,?_⟩
  · exact (h1.stored.after (by decide) (by decide) (by decide) h2).after
      (by decide) (by decide) (by decide) h3
  · exact h2.stored.after (by decide) (by decide) (by decide) h3
  · exact (((h1.rootsFrame (by decide)).trans (h2.rootsFrame (by decide))).trans
      (h3.rootsFrame (by decide))).mono (by intro A hA h; rcases h with (h|h)|h <;> exact h)
  · exact (h3.counterMem (by decide)).trans ((h2.counterMem (by decide)).trans (h1.counterMem (by decide)))
  · intro extra htier
    exact h3.tierPreserved (by decide)
      (h2.tierPreserved (by decide) (h1.tierPreserved (by decide) htier))
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def introCode : List (BitVec 32) := bv_list% 32 [0x413,0x493,0xc00793,0x3300d13,0x3300d93,0x9800893,0x20e37,0x550e0e13,0xe3903,0x1395913,0x90713,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block introBlock := symRun { noAlias := true } introCode (pcOf 22182) 100
def copyCode : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xf1dea0ef]
sym_block copyBlock := symRun { noAlias := true } copyCode (pcOf 22199) 100
structure IntroPost (index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22199
  x8 : t.getReg .x8=0
  x9 : t.getReg .x9=0
  x14 : t.getReg .x14=BitVec.ofNat 64 (index/2^19)
  x15 : t.getReg .x15=12
  x17 : t.getReg .x17=152
  x18 : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  x26 : t.getReg .x26=51
  x27 : t.getReg .x27=51
  x28 : t.getReg .x28=BitVec.ofNat 64 ENC
  x29 : t.getReg .x29=BitVec.ofNat 64 0x66040
  regs : RegsExcept s t [.x7,.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun _ => False)
theorem intro_steps {im : Image} (hc : CodeAt im (pcOf 22182) introCode)
    (s : MachineState) (hp : s.pc=pcOf 22182) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 17 17 t ∧ IntroPost index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  refine ⟨_,symRun_sound introBlock hc s hp (by simp [introBlock.res,rv_simp]),?_⟩
  constructor
  all_goals first
    | solve | (simp only [Result.toState_getReg,introBlock.res]; t3n [hidx,ENC])
    | solve | (simp [introBlock.res,rv_simp])
    | solve | (intro r hr; cases r <;> simp at hr <;> rfl)
    | solve | (intro A hA hn; simp [introBlock.res,rv_simp])
    | (simp only [Result.toState_getReg,introBlock.res]; t3n [hidx,ENC];
       apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight,toNat_ofNat_lt (show index<2^64 by omega),Nat.shiftRight_eq_div_pow]; omega)

theorem copy_steps {im : Image} (hc : CodeAt im (pcOf 22199) copyCode)
    (s : MachineState) (hp : s.pc=pcOf 22199)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 0x66040)
    (left right : Digest) (hl : DigAt s 0x66040 left) (hr : DigAt s 0x66050 right) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 646 ∧ t.getReg .x1=pcOf 22208 ∧
      DigAt t ENC left ∧ DigAt t (ENC+48) right ∧
      RegsExcept s t [.x1,.x6,.x7] ∧
      Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) := by
  have ho : Oblig.all s copyBlock.res.st.obl := by
    simp [copyBlock.res,rv_simp,h28,h29,ENC]
    decide
  refine ⟨_,symRun_sound copyBlock hc s hp ho,?_,?_,?_,?_,?_,?_⟩
  · simp [copyBlock.res,rv_simp]
  · simp [copyBlock.res,rv_simp,pcOf]
  · constructor
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hl.1
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hl.2
  · constructor
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hr.1
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hr.2
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,copyBlock.res]
    t3n [h28,h29,ENC]
    unfold ENC at hn
    repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Code (im : Image) : Prop where
  intro : CodeAt im (pcOf 22182) introCode
  copy : CodeAt im (pcOf 22199) copyCode
structure Post (index : Nat) (left right : Digest) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22208
  x8 : t.getReg .x8=0
  x9 : t.getReg .x9=0
  x14 : t.getReg .x14=BitVec.ofNat 64 (index/2^19)
  x15 : t.getReg .x15=12
  x17 : t.getReg .x17=152
  x18 : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  x26 : t.getReg .x26=51
  x27 : t.getReg .x27=51
  left : DigAt t ENC left
  right : DigAt t (ENC+48) right
  regs : RegsExcept s t [.x1,.x6,.x7,.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)
theorem steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 22182) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (left right : Digest)
    (hl : DigAt s 0x66040 left) (hr : DigAt s 0x66050 right) :
    ∃ t, Steps im s 26 26 t ∧ Post index left right s t := by
  obtain ⟨a,sa,ha⟩ := intro_steps hc.intro s hp index hi hidx
  obtain ⟨t,at',tp,tret,tl,tr,trs,tf⟩ := copy_steps hc.copy a ha.pc ha.x28 ha.x29 left right
    (hl.frame ha.frame (by decide) (fun h => h) (fun h => h))
    (hr.frame ha.frame (by decide) (fun h => h) (fun h => h))
  refine ⟨t,sa.trans at',tp,tret,?_,?_,?_,?_,?_,?_,?_,?_,tl,tr,?_,?_⟩
  · exact (trs.get (by decide)).trans ha.x8
  · exact (trs.get (by decide)).trans ha.x9
  · exact (trs.get (by decide)).trans ha.x14
  · exact (trs.get (by decide)).trans ha.x15
  · exact (trs.get (by decide)).trans ha.x17
  · exact (trs.get (by decide)).trans ha.x18
  · exact (trs.get (by decide)).trans ha.x26
  · exact (trs.get (by decide)).trans ha.x27
  · exact (ha.regs.trans trs).mono (by simp)
  · exact (ha.frame.trans tf).mono (by tauto)
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast

end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedResidual
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def read22230Code : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3303,0x18e3383,0x63e663]
sym_block read22230 := symRun { noAlias := true } read22230Code (pcOf 22230) 100
def zero22230Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22230 := symRun { noAlias := true } zero22230Code (pcOf 22235) 100
def sub22230Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22230 := symRun { noAlias := true } sub22230Code (pcOf 22237) 100
def store22230Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22230 := symRun { noAlias := true } store22230Code (pcOf 22238) 100
structure Code22230 (im : Image) : Prop where
  read : CodeAt im (pcOf 22230) read22230Code
  zero : CodeAt im (pcOf 22235) zero22230Code
  sub : CodeAt im (pcOf 22237) sub22230Code
  store : CodeAt im (pcOf 22238) store22230Code

theorem read22230_steps {im : Image} (hc : CodeAt im (pcOf 22230) read22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22230) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=(if c<r then pcOf 22237 else pcOf 22235) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧ t.getReg .x7=BitVec.ofNat 64 c ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound read22230 hc s hp (by simp [read22230.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [read22230.res,rv_simp,hrm,hcm,pcOf,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),toNat_ofNat_lt (show c<2^64 by omega)]
  · simp [read22230.res,rv_simp,hrm]
  · simp [read22230.res,rv_simp,hcm]
  · simp [read22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [read22230.res,rv_simp]

theorem zero22230_steps {im : Image} (hc : CodeAt im (pcOf 22235) zero22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22235) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22230 hc s hp (by simp [zero22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22230.res,rv_simp]
  · simp [zero22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22230.res,rv_simp]

theorem sub22230_steps {im : Image} (hc : CodeAt im (pcOf 22237) sub22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22237) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22230 hc s hp (by simp [sub22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22230.res,rv_simp]
  · simp only [Result.toState_getReg,sub22230.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22230.res,rv_simp]

theorem store22230_steps {im : Image} (hc : CodeAt im (pcOf 22238) store22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22238) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22230 hc s hp (by simp [store22230.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22230.res,rv_simp]
  · simp [store22230.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22230.res]; t3n [h28]
    rw [if_neg (by omega)]

theorem residual22230_steps {im : Image} (hc : Code22230 im)
    (s : MachineState) (hp : s.pc=pcOf 22230) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t k, Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩ := read22230_steps hc.read s hp r c hr hc' hrm hcm
  by_cases hcr : c<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := sub22230_steps hc.sub a (by simpa [hcr] using ap) r c hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,7,sa.trans (ab.trans bt),by decide,tp,tv,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := zero22230_steps hc.zero a (by simpa [hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,8,sa.trans (ab.trans bt),by decide,tp,by simpa [Nat.sub_eq_zero_of_le (by omega : r≤c)] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
def read22448Code : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3303,0x18e3383,0x63e663]
sym_block read22448 := symRun { noAlias := true } read22448Code (pcOf 22448) 100
def zero22448Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22448 := symRun { noAlias := true } zero22448Code (pcOf 22453) 100
def sub22448Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22448 := symRun { noAlias := true } sub22448Code (pcOf 22455) 100
def store22448Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22448 := symRun { noAlias := true } store22448Code (pcOf 22456) 100
structure Code22448 (im : Image) : Prop where
  read : CodeAt im (pcOf 22448) read22448Code
  zero : CodeAt im (pcOf 22453) zero22448Code
  sub : CodeAt im (pcOf 22455) sub22448Code
  store : CodeAt im (pcOf 22456) store22448Code

theorem read22448_steps {im : Image} (hc : CodeAt im (pcOf 22448) read22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22448) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=(if c<r then pcOf 22455 else pcOf 22453) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧ t.getReg .x7=BitVec.ofNat 64 c ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound read22448 hc s hp (by simp [read22448.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [read22448.res,rv_simp,hrm,hcm,pcOf,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),toNat_ofNat_lt (show c<2^64 by omega)]
  · simp [read22448.res,rv_simp,hrm]
  · simp [read22448.res,rv_simp,hcm]
  · simp [read22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [read22448.res,rv_simp]

theorem zero22448_steps {im : Image} (hc : CodeAt im (pcOf 22453) zero22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22453) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22448 hc s hp (by simp [zero22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22448.res,rv_simp]
  · simp [zero22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22448.res,rv_simp]

theorem sub22448_steps {im : Image} (hc : CodeAt im (pcOf 22455) sub22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22455) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22448 hc s hp (by simp [sub22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22448.res,rv_simp]
  · simp only [Result.toState_getReg,sub22448.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22448.res,rv_simp]

theorem store22448_steps {im : Image} (hc : CodeAt im (pcOf 22456) store22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22456) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22448 hc s hp (by simp [store22448.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22448.res,rv_simp]
  · simp [store22448.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22448.res]; t3n [h28]
    rw [if_neg (by omega)]

theorem residual22448_steps {im : Image} (hc : Code22448 im)
    (s : MachineState) (hp : s.pc=pcOf 22448) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t k, Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩ := read22448_steps hc.read s hp r c hr hc' hrm hcm
  by_cases hcr : c<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := sub22448_steps hc.sub a (by simpa [hcr] using ap) r c hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,7,sa.trans (ab.trans bt),by decide,tp,tv,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := zero22448_steps hc.zero a (by simpa [hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,8,sa.trans (ab.trans bt),by decide,tp,by simpa [Nat.sub_eq_zero_of_le (by omega : r≤c)] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedResidual

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def EntryWrites (A : Nat) : Prop := A=0x66000 ∨ 0x660a0≤A ∧ A<0x660c0 ∨ DIGITS≤A ∧ A<DIGITS+56
structure BuiltPost (sk : SecretKey) (cache : Bytes 131072) (index : Nat) (forest : Digest×Digest)
    (s : MachineState) (p : PreparedRoots) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=pcOf 22182
  layer : t.getReg .x8=4
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  one : Stored 1 index p.one t
  two : Stored 2 index p.two t
  three : Stored 3 index p.three t
  hintZero : t.getMem (0x66000#64)=0
  forestL : DigAt t 0x660a0 forest.1
  forestR : DigAt t 0x660b0 forest.2
  frame : Frame s t (fun A => EntryWrites A ∨ RootsWrites A)
  counterMem : t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32))
  tier : ∀ extra, SigGolfCandidate.T3M.Sign.SharedTier.At extra s →
    SigGolfCandidate.T3M.Sign.SharedTier.At extra t

theorem entry_roots_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat} (hi : index<2^31)
    (forest : Digest×Digest) (s : MachineState) (hpc : s.pc=pcOf 22100)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hl : DigAt s ENC forest.1) (hr : DigAt s (ENC+48) forest.2) :
    TBSim im sk s (28+3*(btCost+47)) (prepareRoots index) (BuiltPost (cfFlag := cfFlag) sk cache index forest s) := by
  obtain ⟨a,sa,ap,a8,al,ar,az,ad,ars,af⟩ := entry_steps he s hpc forest.1 forest.2 hl hr
  have af' : Frame s a EntryWrites := af.mono (by unfold EntryWrites; intros A hA h; exact h)
  have abase : Base (cfFlag := cfFlag) sk cache a := hb.frame af' ars (by decide) (by
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold EntryWrites at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA,DIGITS] at hbase hw
    omega)
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (af'.get (A := 0x20550) (by decide) (by unfold EntryWrites DIGITS; omega)).trans hidx
  refine (TBSim.steps sa (prepareRoots_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    hi a ap a8 aidx abase ad)).mono (le_refl _) ?_
  intro p t ht
  refine ⟨ht.pc,ht.layer,ht.base,ht.indexMem,ht.one,ht.two,ht.three,?_,?_,?_,af'.trans ht.frame,?_,?_⟩
  · exact (ht.frame.get (A := 0x66000) (by decide) (by unfold RootsWrites; decide)).trans az
  · exact al.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
  · exact ar.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
  · exact ht.counterMem.trans (af'.get (A := ENC+32) (by unfold ENC; decide) (by unfold EntryWrites ENC DIGITS; decide))
  · intro extra htier
    apply ht.tier extra
    exact htier.frame af'
      (by unfold EntryWrites EOUT DIGITS; omega)
      (by unfold EntryWrites EOUT DIGITS; omega)
      (by unfold EntryWrites EOUT DIGITS; omega)
end SigGolfCandidate.T3M.Sign.SharedRootControl


namespace SigGolfCandidate.T3M.Sign.SharedTopDigits
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def saveCode : List (BitVec 32) := bv_list% 32 [0x20e37,0x420e0e13,0x66eb7,0x100e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x20e3303,0x26eb023,0x28e3303,0x26eb423,0x30e3303,0x26eb823]
sym_block save := symRun { noAlias := true } saveCode (pcOf 22208) 100
theorem save_steps {im : Image} (hc : CodeAt im (pcOf 22208) saveCode)
    (s : MachineState) (hp : s.pc=pcOf 22208) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56) := by
  refine ⟨_,symRun_sound save hc s hp (by simp [save.res,rv_simp]; try decide),?_,?_,?_,?_⟩
  · simp [save.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [save.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,save.res]
    t3n [DIGITS]
    try unfold DIGITS at hn
    repeat rw [if_neg (by omega)]
def restoreCode : List (BitVec 32) := bv_list% 32 [0x66e37,0x100e0e13,0x20eb7,0x420e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x20e3303,0x26eb023,0x28e3303,0x26eb423,0x30e3303,0x26eb823]
sym_block restore := symRun { noAlias := true } restoreCode (pcOf 22460) 100
theorem restore_steps {im : Image} (hc : CodeAt im (pcOf 22460) restoreCode)
    (s : MachineState) (hp : s.pc=pcOf 22460) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22478 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56) := by
  refine ⟨_,symRun_sound restore hc s hp (by simp [restore.res,rv_simp]; try decide),?_,?_,?_,?_⟩
  · simp [restore.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [restore.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,restore.res]
    t3n [DIGITS]
    try unfold DIGITS at hn
    repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedTopDigits


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def cst (n : Nat) : E := .c (BitVec.ofNat 64 n)
def rfs (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def thCode : List (BitVec 32) := bv_list% 32 [0xfff40313,0x30e63,0xffe40313,0xc030c63,0x1600313,0x1c6a7263,0xa0e93,0x1c00006f,0x3800313,0x1a6a7a63,0xe93,0x2600313,0x1a6a6663,0x100e93,0x2700313,0x1a6a6063,0x200e93,0x2800313,0x186a6a63,0x300e93,0x2900313,0x186a6463,0x400e93,0x2a00313,0x166a6e63,0x500e93,0x2b00313,0x166a6863,0x600e93,0x2c00313,0x166a6263,0x700e93,0x2d00313,0x146a6c63,0x800e93,0x2f00313,0x146a6663,0x900e93,0x3000313,0x146a6063,0xa00e93,0x3100313,0x126a6a63,0xb00e93,0x3300313,0x126a6463,0xc00e93,0x3400313,0x106a6e63,0xd00e93,0x3600313,0x106a6863,0xe00e93,0x3700313,0x106a6263,0xf00e93,0xfc0006f,0x2900313,0xe6a7863,0xe93,0x1400313,0xe6a6463,0x100e93,0x1500313,0xc6a6e63,0x200e93,0x1600313,0xc6a6863,0x300e93,0x1700313,0xc6a6263,0x400e93,0x1800313,0xa6a6c63,0x500e93,0x1900313,0xa6a6663,0x600e93,0x1a00313,0xa6a6063,0x700e93,0x1b00313,0x86a6a63,0x800e93,0x1c00313,0x86a6463,0x900e93,0x1d00313,0x66a6e63,0xa00e93,0x1e00313,0x66a6863,0xb00e93,0x1f00313,0x66a6263,0xc00e93,0x2100313,0x46a6c63,0xd00e93,0x2200313,0x46a6663,0xe00e93,0x2300313,0x46a6063,0xf00e93,0x2500313,0x26a6a63,0x1000e93,0x2600313,0x26a6463,0x1100e93,0x2700313,0x6a6e63,0x1200e93,0x2800313,0x6a6863,0x1300e93,0x80006f,0x945fd06f,0xf44fd06f]
/-- The img-v6 threshold routine `th` (appended, 24851..24970): `t4 := threshold(s0, s4)`; L1 cascade at 24859
(residual < 56), L2 at 24908 (residual < 41), L3 at 24855 (floor = residual < 22), failure 24969 (`jal 22490`),
result 24970 (`jal 22363`). -/
def lookT (n : Nat) : Option (BitVec 32) := if 24851 ≤ n then thCode[n-24851]? else none
def ends1 : List Nat := [38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 51, 52, 54, 55]
def ends2 : List Nat := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39, 40]
def dirs (m v : Nat) : List Dir := [.br false] ++ List.replicate v (.br false) ++ (if v < m then [.br true] else [])
def resL (ends : List Nat) (m bound v : Nat) : PRes :=
  ⟨⟨rfs [(.x6,cst (ends.getD (if v < m then v else m-1) 0)),(.x29,cst v)],[],[]⟩,pcOf 22363,false,
    (if v < m then 6+3*v else 5+3*m),(if v < m then 6+3*v else 5+3*m),
    (if v < m then [⟨.ltu,.reg .x20,cst (ends.getD v 0),true⟩] else []) ++
    ((List.range v).reverse.map (fun i => ⟨.ltu,.reg .x20,cst (ends.getD i 0),false⟩)) ++
    [⟨.geu,.reg .x20,cst bound,false⟩],none⟩
theorem checked1 : (List.range 16).all (fun v =>
    optBeq (run lookT [22363] 24859 (dirs 15 v)) (resL ends1 15 56 v)) = true := by decide +kernel
theorem checked2 : (List.range 20).all (fun v =>
    optBeq (run lookT [22363] 24908 (dirs 19 v)) (resL ends2 19 41 v)) = true := by decide +kernel
theorem code_lookT {im : Image} (hc : CodeAt im (pcOf 24851) thCode) : LookOK im lookT := by
  intro n w hw
  unfold lookT at hw
  split at hw
  · rename_i hn
    have hlen := (List.getElem?_eq_some_iff.mp hw).1
    obtain ⟨rest,hrest⟩ := hc.2.2.2
    have hpref : thCode ++ rest = im.code.drop 24851 := by simpa [pcOf] using hrest
    have hget : (im.code.drop 24851)[n-24851]? = some w := by
      rw [← hpref,List.getElem?_append_left hlen]; exact hw
    simpa [List.getElem?_drop,Nat.add_sub_cancel' hn] using hget
  · cases hw
theorem floorL_steps {im : Image} (hc : CodeAt im (pcOf 24851) thCode) (ends : List Nat) (m bound start : Nat)
    (hchk : (List.range (m+1)).all (fun v =>
      optBeq (run lookT [22363] start (dirs m v)) (resL ends m bound v)) = true)
    (hm : 0 < m) (hlen : ends.length=m) (hlt : ∀ i, i < m → ends.getD i 0<2^64) (hb : bound<2^64)
    (s : MachineState) (hp : s.pc=pcOf start) (r v : Nat)
    (hv : v ≤ m) (hr : r<bound)
    (hupper : v < m → r<ends.getD v 0)
    (hlower : ∀ i,i < v → ends.getD i 0≤r)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t k, Steps im s k k t ∧ k≤5+3*m ∧ t.pc=pcOf 22363 ∧
      t.getReg .x29=BitVec.ofNat 64 v ∧ RegsExcept s t [.x6,.x29] ∧ Frame s t (fun _ => False) := by
  have hh := optBeq_eq (List.all_eq_true.mp hchk v (List.mem_range.mpr (by omega)))
  have hob : ∀ o∈(resL ends m bound v).st.obl,o.holds s := by simp [resL]
  have hbr : ∀ b∈(resL ends m bound v).brs,b.holds s := by
    intro b hb
    simp only [resL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with (hb|hb)|rfl
    · split at hb
      · rename_i hvm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        subst hb
        simp only [Br.holds,E.eval,cst,CmpOp.eval,h20]
        have he := hlt v hvm
        simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r<2^64 by omega),Nat.mod_eq_of_lt he,decide_eq_true_eq]
        exact hupper hvm
      · simp at hb
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
      have hi : i < v := List.mem_range.mp (List.mem_reverse.mp hi)
      have he := hlt i (by omega)
      simp only [Br.holds,E.eval,cst,CmpOp.eval,h20]
      simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r<2^64 by omega),Nat.mod_eq_of_lt he,decide_eq_false_iff_not]
      exact Nat.not_lt.mpr (hlower i hi)
    · simp [Br.holds,E.eval,cst,CmpOp.eval,h20,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega)]
      omega
  refine ⟨(resL ends m bound v).toState s,_,(run_sound (code_lookT hc) hh s hp hob hbr).1,?_,rfl,rfl,?_,?_⟩
  · simp only [resL]; split <;> omega
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
end SigGolfCandidate.T3M.Sign.SharedFloor


namespace SigGolfCandidate.T3M.Sign.SharedResidual
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed22230 : Code22230 Images.signImage := by
  constructor <;> sign_slice_fast
theorem installed22448 : Code22448 Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedResidual
namespace SigGolfCandidate.T3M.Sign.SharedTopDigits
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_save : CodeAt Images.signImage (pcOf 22208) saveCode := by
  sign_slice_fast
theorem installed_restore : CodeAt Images.signImage (pcOf 22460) restoreCode := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedTopDigits


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def selectACode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3a03,0x0c10206f]
sym_block selectA := symRun { noAlias := true } selectACode (pcOf 22240) 100
def dispACode : List (BitVec 32) := bv_list% 32 [0xfff40313,0x30e63]
sym_block dispA := symRun { noAlias := true } dispACode (pcOf 24851) 100
def selectBCode : List (BitVec 32) := bv_list% 32 [0xffe40313,0xc030c63]
sym_block selectB := symRun { noAlias := true } selectBCode (pcOf 24853) 100
def guard3Code : List (BitVec 32) := bv_list% 32 [0x1600313,0x1c6a7263]
sym_block guard3 := symRun { noAlias := true } guard3Code (pcOf 24855) 100
def return3Code : List (BitVec 32) := bv_list% 32 [0xa0e93,0x1c00006f]
sym_block return3 := symRun { noAlias := true } return3Code (pcOf 24857) 100
def finCode : List (BitVec 32) := bv_list% 32 [0xf44fd06f]
sym_block fin := symRun { noAlias := true } finCode (pcOf 24970) 100

theorem selectA_steps {im : Image} (hc : CodeAt im (pcOf 22240) selectACode)
    (s : MachineState) (hp : s.pc=pcOf 22240) (r : Nat)
    (hr : s.getMem (0x66008#64)=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 24851 ∧
      t.getReg .x20=BitVec.ofNat 64 r ∧ RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound selectA hc s hp (by simp [selectA.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [selectA.res,rv_simp]
  · simp [selectA.res,rv_simp,hr]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem dispA_steps {im : Image} (hc : CodeAt im (pcOf 24851) dispACode)
    (s : MachineState) (hp : s.pc=pcOf 24851) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=(if lay=1 then pcOf 24859 else pcOf 24853) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound dispA hc s hp (by simp [dispA.res,rv_simp]),?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩
    interval_cases lay <;> simp [dispA.res,rv_simp,h8]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem selectB_steps {im : Image} (hc : CodeAt im (pcOf 24853) selectBCode)
    (s : MachineState) (hp : s.pc=pcOf 24853) (lay : Nat) (hl : lay=2 ∨ lay=3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=(if lay=2 then pcOf 24908 else pcOf 24855) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound selectB hc s hp (by simp [selectB.res,rv_simp]),?_,?_,?_⟩
  · rcases hl with rfl|rfl <;> simp [selectB.res,rv_simp,h8]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem guard3_steps {im : Image} (hc : CodeAt im (pcOf 24855) guard3Code)
    (s : MachineState) (hp : s.pc=pcOf 24855) (r : Nat) (hr : r<22)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 24857 ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound guard3 hc s hp (by simp [guard3.res,rv_simp]),?_,?_,?_⟩
  · simp [guard3.res,rv_simp,h20,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),hr]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem return3_steps {im : Image} (hc : CodeAt im (pcOf 24857) return3Code)
    (s : MachineState) (hp : s.pc=pcOf 24857) (r : Nat)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 24970 ∧ t.getReg .x29=BitVec.ofNat 64 r ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound return3 hc s hp (by simp [return3.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [return3.res,rv_simp]
  · simp [return3.res,rv_simp,h20]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem fin_steps {im : Image} (hc : CodeAt im (pcOf 24970) finCode)
    (s : MachineState) (hp : s.pc=pcOf 24970) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22363 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound fin hc s hp (by simp [fin.res,rv_simp]),?_,?_,?_⟩
  · simp [fin.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
end SigGolfCandidate.T3M.Sign.SharedFloor

namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem threshold1_range : ∀ r,r<56 →
    CanonicalPolicy.threshold 1 r≤15 ∧ (CanonicalPolicy.threshold 1 r<15 → r<ends1.getD (CanonicalPolicy.threshold 1 r) 0) ∧
      ∀ i,i<CanonicalPolicy.threshold 1 r → ends1.getD i 0≤r := by decide +kernel
theorem threshold2_range : ∀ r,r<41 →
    CanonicalPolicy.threshold 2 r≤19 ∧ (CanonicalPolicy.threshold 2 r<19 → r<ends2.getD (CanonicalPolicy.threshold 2 r) 0) ∧
      ∀ i,i<CanonicalPolicy.threshold 2 r → ends2.getD i 0≤r := by decide +kernel
theorem ends1_lt : ∀ i, i<15 → ends1.getD i 0<2^64 := by decide +kernel
theorem ends2_lt : ∀ i, i<19 → ends2.getD i 0<2^64 := by decide +kernel

structure DispatchCode (im : Image) : Prop where
  selectA : CodeAt im (pcOf 22240) selectACode
  dispA : CodeAt im (pcOf 24851) dispACode
  selectB : CodeAt im (pcOf 24853) selectBCode
  guard3 : CodeAt im (pcOf 24855) guard3Code
  return3 : CodeAt im (pcOf 24857) return3Code
  fin : CodeAt im (pcOf 24970) finCode
  th : CodeAt im (pcOf 24851) thCode

theorem threshold_steps {im : Image} (hc : DispatchCode im)
    (s : MachineState) (hp : s.pc=pcOf 22240) (lay r : Nat) (hl : 1≤lay ∧ lay≤3)
    (hr : r < if lay=1 then 56 else if lay=2 then 41 else 22)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) :
    ∃ t k,Steps im s k k t ∧ k≤70 ∧ t.pc=pcOf 22363 ∧
      t.getReg .x29=BitVec.ofNat 64 (CanonicalPolicy.threshold lay r) ∧
      RegsExcept s t [.x6,.x20,.x28,.x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨a,sa,ap,a20,ar,af⟩ := selectA_steps hc.selectA s hp r hrm
  have a8 := (ar.get (by decide : RiscvZkvm.Rv64.Reg.x8 ∉ [.x20,.x28])).trans h8
  obtain ⟨b,ab,bp,br,bf⟩ := dispA_steps hc.dispA a ap lay hl a8
  have b20 := (br.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans a20
  have b8 := (br.get (by decide : RiscvZkvm.Rv64.Reg.x8 ∉ [.x6])).trans a8
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · have ht := threshold1_range r (by simpa using hr)
    obtain ⟨t,k,bt,hk,tp,t29,tr,tf⟩ := floorL_steps hc.th ends1 15 56 24859 checked1 (by decide) rfl ends1_lt
      (by decide) b (by simpa using bp) r _ ht.1 (by simpa using hr) ht.2.1 ht.2.2 b20
    exact ⟨t,4+2+k,(sa.trans ab).trans bt,by omega,tp,t29,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨c,bc,cp,cr,cf⟩ := selectB_steps hc.selectB b (by simpa using bp) 2 (by simp) b8
    have c20 := (cr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans b20
    have ht := threshold2_range r (by simpa using hr)
    obtain ⟨t,k,ct,hk,tp,t29,tr,tf⟩ := floorL_steps hc.th ends2 19 41 24908 checked2 (by decide) rfl ends2_lt
      (by decide) c (by simpa using cp) r _ ht.1 (by simpa using hr) ht.2.1 ht.2.2 c20
    exact ⟨t,4+2+2+k,((sa.trans ab).trans bc).trans ct,by omega,tp,t29,
      (((ar.trans br).trans cr).trans tr).mono (by simp),(((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
  · obtain ⟨c,bc,cp,cr,cf⟩ := selectB_steps hc.selectB b (by simpa using bp) 3 (by simp) b8
    have c20 := (cr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans b20
    obtain ⟨d,cd,dp,dr,df⟩ := guard3_steps hc.guard3 c (by simpa using cp) r (by simpa using hr) c20
    have d20 := (dr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans c20
    obtain ⟨e,de,ep,e29,er,ef⟩ := return3_steps hc.return3 d dp r d20
    obtain ⟨t,et,tp,tr,tf⟩ := fin_steps hc.fin e ep
    refine ⟨t,13,((((sa.trans ab).trans bc).trans cd).trans de).trans et,by decide,tp,?_,
      (((((ar.trans br).trans cr).trans dr).trans er).trans tr).mono (by simp),
      (((((af.trans bf).trans cf).trans df).trans ef).trans tf).mono (by tauto)⟩
    rw [tr.get (by decide),e29]
    simp [CanonicalPolicy.threshold,show r≤21 by simp at hr;omega]
end SigGolfCandidate.T3M.Sign.SharedFloor

namespace SigGolfCandidate.T3M.Sign.SharedHints
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x1de3823,0xe3303,0x1e400393,0xfff40f13,0xf0a63]
sym_block first := symRun { noAlias := true } firstCode (pcOf 22363) 100
def secondCode : List (BitVec 32) := bv_list% 32 [0x1600393,0xffe40f13,0xf0463]
sym_block second := symRun { noAlias := true } secondCode (pcOf 22370) 100
def thirdCode : List (BitVec 32) := bv_list% 32 [0x100393]
sym_block third := symRun { noAlias := true } thirdCode (pcOf 22373) 100
def addHintCode : List (BitVec 32) := bv_list% 32 [0x3d383b3,0x730333,0x6e3023]
sym_block addHint := symRun { noAlias := true } addHintCode (pcOf 22374) 100

theorem first_steps {im : Image} (hc : CodeAt im (pcOf 22363) firstCode)
    (s : MachineState) (hp : s.pc=pcOf 22363) (lay h f : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h29 : s.getReg .x29=BitVec.ofNat 64 f)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 h) :
    ∃ t,Steps im s 7 7 t ∧ t.pc=(if lay=1 then pcOf 22374 else pcOf 22370) ∧
      t.getReg .x6=BitVec.ofNat 64 h ∧ t.getReg .x7=484 ∧ t.getReg .x28=0x66000 ∧
      t.getMem (0x66010#64)=BitVec.ofNat 64 f ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧ Frame s t (fun A => A=0x66010) := by
  refine ⟨_,symRun_sound first hc s hp (by simp [first.res,rv_simp];try decide),?_,?_,?_,?_,?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩;interval_cases lay <;> simp [first.res,rv_simp,h8]
  · simp [first.res,rv_simp,hm]
  · simp [first.res,rv_simp]
  · simp [first.res,rv_simp]
  · simp [first.res,rv_simp,h29]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,first.res]; t3n []
    rw [if_neg (by omega)]

theorem second_steps {im : Image} (hc : CodeAt im (pcOf 22370) secondCode)
    (s : MachineState) (hp : s.pc=pcOf 22370) (lay : Nat) (hl : lay=2 ∨ lay=3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay=2 then pcOf 22374 else pcOf 22373) ∧
      t.getReg .x7=22 ∧ RegsExcept s t [.x7,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound second hc s hp (by simp [second.res,rv_simp]),?_,?_,?_,?_⟩
  · rcases hl with rfl|rfl <;> simp [second.res,rv_simp,h8]
  · simp [second.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem third_steps {im : Image} (hc : CodeAt im (pcOf 22373) thirdCode)
    (s : MachineState) (hp : s.pc=pcOf 22373) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22374 ∧ t.getReg .x7=1 ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound third hc s hp (by simp [third.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [third.res,rv_simp]
  · simp [third.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem add_steps {im : Image} (hc : CodeAt im (pcOf 22374) addHintCode)
    (s : MachineState) (hp : s.pc=pcOf 22374) (h f mul : Nat)
    (h6 : s.getReg .x6=BitVec.ofNat 64 h) (h7 : s.getReg .x7=BitVec.ofNat 64 mul)
    (h29 : s.getReg .x29=BitVec.ofNat 64 f) (h28 : s.getReg .x28=0x66000) :
    ∃ t,Steps im s 3 6 t ∧ t.pc=pcOf 22377 ∧
      t.getMem (0x66000#64)=BitVec.ofNat 64 (h+mul*f) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=0x66000) := by
  refine ⟨_,symRun_sound addHint hc s hp (by simp [addHint.res,rv_simp,h28];try decide),?_,?_,?_,?_⟩
  · simp [addHint.res,rv_simp]
  · simp only [Result.toState_getMem,addHint.res];t3n [h6,h7,h29,h28]
    simp [← BitVec.ofNat_mul,← BitVec.ofNat_add]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,addHint.res];t3n [h28]
    rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedHints
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Code (im : Image) : Prop where
  first : CodeAt im (pcOf 22363) firstCode
  second : CodeAt im (pcOf 22370) secondCode
  third : CodeAt im (pcOf 22373) thirdCode
  add : CodeAt im (pcOf 22374) addHintCode

/-- Hint weight of layer `lay` (img-v4/v6 radix 484 / 22 / 1). -/
def hintWeight (lay : Nat) : Nat := if lay = 1 then 484 else if lay = 2 then 22 else 1
theorem steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22363)
    (lay h f : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h29 : s.getReg .x29=BitVec.ofNat 64 f)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 h) :
    ∃ t k,Steps im s k (k+3) t ∧ k≤14 ∧ t.pc=pcOf 22377 ∧
      t.getMem (0x66000#64)=BitVec.ofNat 64 (h+hintWeight lay*f) ∧
      t.getMem (0x66010#64)=BitVec.ofNat 64 f ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧ Frame s t (fun A => A=0x66000 ∨ A=0x66010) := by
  obtain ⟨a,sa,ap,a6,a7,a28,am,ar,af⟩ := first_steps hc.first s hp lay h f hl h8 h29 hm
  have a8 := (ar.get (by decide : Reg.x8 ∉ [.x6,.x7,.x28,.x30])).trans h8
  have a29 := (ar.get (by decide : Reg.x29 ∉ [.x6,.x7,.x28,.x30])).trans h29
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,aToT,tp,tm,tr,tf⟩ := add_steps hc.add a (by simpa using ap) h f 484 a6 a7 a29 a28
    exact ⟨t,10,sa.trans aToT,by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans am,
      (ar.trans tr).mono (by simp),(af.trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b7,br,bf⟩ := second_steps hc.second a (by simpa using ap) 2 (by simp) a8
    obtain ⟨t,bt,tp,tm,tr,tf⟩ := add_steps hc.add b (by simpa using bp) h f 22
      ((br.get (by decide)).trans a6) b7 ((br.get (by decide)).trans a29) ((br.get (by decide)).trans a28)
    exact ⟨t,13,sa.trans (ab.trans bt),by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans ((bf.get (by decide) (by simp)).trans am),
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b7,br,bf⟩ := second_steps hc.second a (by simpa using ap) 3 (by simp) a8
    obtain ⟨c,bc,cp,c7,cr,cf⟩ := third_steps hc.third b (by simpa using bp)
    obtain ⟨t,ct,tp,tm,tr,tf⟩ := add_steps hc.add c cp h f 1
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a6)) c7
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a29))
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a28))
    exact ⟨t,14,sa.trans (ab.trans (bc.trans ct)),by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans ((cf.get (by decide) (by simp)).trans ((bf.get (by decide) (by simp)).trans am)),
      (((ar.trans br).trans cr).trans tr).mono (by simp),(((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_dispatch : DispatchCode Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedFloor
namespace SigGolfCandidate.T3M.Sign.SharedHints
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedControlTail
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def initResidualCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x28e3303,0x6e3423]
sym_block initResidual := symRun { noAlias := true } initResidualCode (pcOf 22226) 100
def firstLayerCode : List (BitVec 32) := bv_list% 32 [0x100413]
sym_block firstLayer := symRun { noAlias := true } firstLayerCode (pcOf 22239) 100
def nextLayerCode : List (BitVec 32) := bv_list% 32 [0x140413,0x400313,0xc8646ae3]
sym_block nextLayer := symRun { noAlias := true } nextLayerCode (pcOf 22457) 100
def topProduceCode : List (BitVec 32) := bv_list% 32 [0x413,0x493,0xc00793,0x3300d13,0x3300d93,0x9800893,0x20e37,0x550e0e13,0xe3903,0x1395913,0x90713,0xf80ea06f]
sym_block topProduce := symRun { noAlias := true } topProduceCode (pcOf 22478) 100

theorem initResidual_steps {im : Image} (hc : CodeAt im (pcOf 22226) initResidualCode)
    (s : MachineState) (hp : s.pc=pcOf 22226) (extra : Nat)
    (hpool : s.getMem (0x66028#64) = BitVec.ofNat 64 (69 + extra)) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22230 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (69 + extra) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound initResidual hc s hp (by simp [initResidual.res,rv_simp];try decide),?_,?_,?_,?_⟩
  · simpa [initResidual.res,rv_simp] using hpool
  · simp [initResidual.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,initResidual.res];t3n []
    rw [if_neg (by omega)]

theorem firstLayer_steps {im : Image} (hc : CodeAt im (pcOf 22239) firstLayerCode)
    (s : MachineState) (hp : s.pc=pcOf 22239) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound firstLayer hc s hp (by simp [firstLayer.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [firstLayer.res,rv_simp]
  · simp [firstLayer.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem nextLayer_steps {im : Image} (hc : CodeAt im (pcOf 22457) nextLayerCode)
    (s : MachineState) (hp : s.pc=pcOf 22457) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22240 else pcOf 22460) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧ RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound nextLayer hc s hp (by simp [nextLayer.res,rv_simp]),?_,?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩;interval_cases lay <;> simp [nextLayer.res,rv_simp,h8]
  · simp [nextLayer.res,rv_simp,h8,BitVec.ofNat_add]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

structure TopPost (index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=51
  n4 : t.getReg .x27=51
  target : t.getReg .x17=152
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  regs : RegsExcept s t [.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28]
  frame : Frame s t (fun _ => False)
theorem topProduce_steps {im : Image} (hc : CodeAt im (pcOf 22478) topProduceCode)
    (s : MachineState) (hp : s.pc=pcOf 22478) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 12 12 t ∧ TopPost index s t := by
  refine ⟨_,symRun_sound topProduce hc s hp (by simp [topProduce.res,rv_simp]),?_⟩
  constructor
  all_goals first
    | solve | simp [topProduce.res,rv_simp,hidx]
    | skip
  · simp only [topProduce.res,rv_simp,hidx]
    exact ofNat_shr index 19 (by omega)
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
end SigGolfCandidate.T3M.Sign.SharedControlTail


namespace SigGolfCandidate.T3M.Sign.SharedLowerRegisters
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def code22377 : List (BitVec 32) := bv_list% 32 [0x2b00d13,0xd93,0xc900893,0x600793,0xfff40313,0x30463]
sym_block blk22377 := symRun { noAlias := true } code22377 (pcOf 22377) 100
def code22383 : List (BitVec 32) := bv_list% 32 [0x80006f]
sym_block blk22383 := symRun { noAlias := true } code22383 (pcOf 22383) 100
def code22384 : List (BitVec 32) := bv_list% 32 [0x700793]
sym_block blk22384 := symRun { noAlias := true } code22384 (pcOf 22384) 100
def code22385 : List (BitVec 32) := bv_list% 32 [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38c63]
sym_block blk22385 := symRun { noAlias := true } code22385 (pcOf 22385) 100
def code22390 : List (BitVec 32) := bv_list% 32 [0xffe40393,0x2038063]
sym_block blk22390 := symRun { noAlias := true } code22390 (pcOf 22390) 100
def code22392 : List (BitVec 32) := bv_list% 32 [0x3f37913,0x635493,0x200006f]
sym_block blk22392 := symRun { noAlias := true } code22392 (pcOf 22392) 100
def code22395 : List (BitVec 32) := bv_list% 32 [0xc35913,0x7f97913,0x1335493,0x100006f]
sym_block blk22395 := symRun { noAlias := true } code22395 (pcOf 22395) 100
def code22399 : List (BitVec 32) := bv_list% 32 [0x635913,0x3f97913,0xc35493]
sym_block blk22399 := symRun { noAlias := true } code22399 (pcOf 22399) 100
def code22402 : List (BitVec 32) := bv_list% 32 [0x90713,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block blk22402 := symRun { noAlias := true } code22402 (pcOf 22402) 100
def code22409 : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xbd5ea0ef]
sym_block blk22409 := symRun { noAlias := true } code22409 (pcOf 22409) 100
structure Code (im : Image) : Prop where
  at22377 : CodeAt im (pcOf 22377) code22377
  at22383 : CodeAt im (pcOf 22383) code22383
  at22384 : CodeAt im (pcOf 22384) code22384
  at22385 : CodeAt im (pcOf 22385) code22385
  at22390 : CodeAt im (pcOf 22390) code22390
  at22392 : CodeAt im (pcOf 22392) code22392
  at22395 : CodeAt im (pcOf 22395) code22395
  at22399 : CodeAt im (pcOf 22399) code22399
  at22402 : CodeAt im (pcOf 22402) code22402
  at22409 : CodeAt im (pcOf 22409) code22409
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22409
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  dst : t.getReg .x28=BitVec.ofNat 64 ENC
  src : t.getReg .x29=BitVec.ofNat 64 (0x66040+32*lay)
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun _ => False)
theorem setup1 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=1)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 23 23 t ∧ Post 1 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22384.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22384 hc.at22384 s1 (by simp [s1,blk22377.res,s2,blk22384.res,rv_simp,h8]) (by simp [blk22384.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22395.res.toState s3
  have st4 : Steps im s3 4 4 s4 := symRun_sound blk22395 hc.at22395 s3 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,rv_simp,h8]) (by simp [blk22395.res,rv_simp];try decide)
  let s5 := blk22402.res.toState s4
  have st5 : Steps im s4 7 7 s5 := symRun_sound blk22402 hc.at22402 s4 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s5, st1.trans (st2.trans (st3.trans (st4.trans (st5)))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index >>> (12:Nat) &&& 127)=BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact ofNat_and_mask (index/2^12) 7 (by decide)
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (19:Nat)=BitVec.ofNat 64 (index/2^19)
    exact ofNat_shr index 19 (by omega)
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
theorem setup2 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=2)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 24 24 t ∧ Post 2 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22383.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22383 hc.at22383 s1 (by simp [s1,blk22377.res,s2,blk22383.res,rv_simp,h8]) (by simp [blk22383.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22390.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22390 hc.at22390 s3 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,rv_simp,h8]) (by simp [blk22390.res,rv_simp];try decide)
  let s5 := blk22399.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22399 hc.at22399 s4 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,rv_simp,h8]) (by simp [blk22399.res,rv_simp];try decide)
  let s6 := blk22402.res.toState s5
  have st6 : Steps im s5 7 7 s6 := symRun_sound blk22402 hc.at22402 s5 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index >>> (6:Nat) &&& 63)=BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact ofNat_and_mask (index/2^6) 6 (by decide)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (12:Nat)=BitVec.ofNat 64 (index/2^12)
    exact ofNat_shr index 12 (by omega)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
theorem setup3 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=3)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 24 24 t ∧ Post 3 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22383.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22383 hc.at22383 s1 (by simp [s1,blk22377.res,s2,blk22383.res,rv_simp,h8]) (by simp [blk22383.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22390.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22390 hc.at22390 s3 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,rv_simp,h8]) (by simp [blk22390.res,rv_simp];try decide)
  let s5 := blk22392.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22392 hc.at22392 s4 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,rv_simp,h8]) (by simp [blk22392.res,rv_simp];try decide)
  let s6 := blk22402.res.toState s5
  have st6 : Steps im s5 7 7 s6 := symRun_sound blk22402 hc.at22402 s5 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index &&& 63)=BitVec.ofNat 64 (index%2^6)
    exact ofNat_and_mask index 6 (by decide)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (6:Nat)=BitVec.ofNat 64 (index/2^6)
    exact ofNat_shr index 6 (by omega)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
end SigGolfCandidate.T3M.Sign.SharedLowerRegisters


namespace SigGolfCandidate.T3M.Sign.SharedLowerCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def code : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xbd5ea0ef]
sym_block block := symRun { noAlias := true } code (pcOf 22409) 100

structure Post (lay : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  regs : RegsExcept s t [.x1,.x6,.x7]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)
theorem steps {im : Image} (hc : CodeAt im (pcOf 22409) code)
    (s : MachineState) (hp : s.pc=pcOf 22409) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC)
    (h29 : s.getReg .x29=BitVec.ofNat 64 (0x66040+32*lay)) :
    ∃ t,Steps im s 9 9 t ∧ Post lay s t := by
  rcases hl with ⟨hlo,hhi⟩
  have hob : block.res.obligs s := by
    interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC] <;> decide
  refine ⟨_,symRun_sound block hc s hp hob,?_⟩
  constructor
  · simp [block.res,rv_simp]
  · simp [block.res,rv_simp]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n [h28,ENC]
    unfold ENC at hn
    repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedLowerCopy


namespace SigGolfCandidate.T3M.Sign.SharedLowerSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)

theorem registers {im : Image} (hc : SharedLowerRegisters.Code im) (s : MachineState)
    (hp : s.pc=pcOf 22377) (lay index : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k,Steps im s k k t ∧ k≤24 ∧ SharedLowerRegisters.Post lay index s t := by
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup1 hc s hp index hi h8 hidx
    exact ⟨t,23,ht,by decide,hp⟩
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup2 hc s hp index hi h8 hidx
    exact ⟨t,24,ht,by decide,hp⟩
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup3 hc s hp index hi h8 hidx
    exact ⟨t,24,ht,by decide,hp⟩

theorem setup {im : Image} (hc : SharedLowerRegisters.Code im) (s : MachineState)
    (hp : s.pc=pcOf 22377) (lay index : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k,Steps im s k k t ∧ k≤33 ∧ Post lay index s t := by
  obtain ⟨a,k,sa,hk,ha⟩ := registers hc s hp lay index hl hi h8 hidx
  obtain ⟨t,aToT,ht⟩ := SharedLowerCopy.steps hc.at22409 a ha.pc lay hl ha.dst ha.src
  refine ⟨t,k+9,sa.trans aToT,by omega,?_⟩
  refine ⟨ht.pc,ht.ret,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (ht.regs.get (by decide)).trans ha.chains
  · exact (ht.regs.get (by decide)).trans ha.n4
  · exact (ht.regs.get (by decide)).trans ha.target
  · exact (ht.regs.get (by decide)).trans ha.height
  · exact (ht.regs.get (by decide)).trans ha.leaf
  · rw [ht.regs.get (by decide),ht.regs.get (by decide)];exact ha.selected
  · exact (ht.regs.get (by decide)).trans ha.tree
  · exact ht.leftLo.trans (ha.frame.get (by omega) (by simp))
  · exact ht.leftHi.trans (ha.frame.get (by omega) (by simp))
  · exact ht.rightLo.trans (ha.frame.get (by omega) (by simp))
  · exact ht.rightHi.trans (ha.frame.get (by omega) (by simp))
  · exact (ha.regs.trans ht.regs).mono (by simp)
  · exact (ha.frame.trans ht.frame).mono (by tauto)
end SigGolfCandidate.T3M.Sign.SharedLowerSetup


namespace SigGolfCandidate.T3M.Sign.SharedLowerSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure CallPost (lay index residual hints : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  floor : t.getMem (0x66010#64)=BitVec.ofNat 64 (ClaudeWCT.WCT9.CanonicalPolicy.threshold lay residual)
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (hints+SharedHints.hintWeight lay*ClaudeWCT.WCT9.CanonicalPolicy.threshold lay residual)
  layer : t.getReg .x8=BitVec.ofNat 64 lay
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x20,.x26,.x27,.x28,.x29,.x30]
  frame : Frame s t (fun A => A=0x66000 ∨ A=0x66010 ∨ A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)


theorem call_steps {im : Image} (hf : SharedFloor.DispatchCode im) (hh : SharedHints.Code im)
    (hc : SharedLowerRegisters.Code im) (s : MachineState) (hp : s.pc=pcOf 22240)
    (lay index residual hints : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (hr : residual < if lay=1 then 56 else if lay=2 then 41 else 22)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual)
    (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t k c,Steps im s k c t ∧ c≤120 ∧ CallPost lay index residual hints s t := by
  obtain ⟨a,ka,sa,hka,ap,a29,ar,af⟩ := SharedFloor.threshold_steps hf s hp lay residual hl hr h8 hrm
  have a8 := (ar.get (by decide : Reg.x8 ∉ [.x6,.x20,.x28,.x29])).trans h8
  obtain ⟨b,kb,ab,hkb,bp,bhints,bfloor,br,bf⟩ := SharedHints.steps hh a ap lay hints _ hl a8 a29
    ((af.get (A:=0x66000) (by decide) (by simp)).trans hhm)
  have b8 := (br.get (by decide : Reg.x8 ∉ [.x6,.x7,.x28,.x30])).trans a8
  have bidx : b.getMem (0x20550#64)=BitVec.ofNat 64 index :=
    (bf.get (A:=0x20550) (by decide) (by decide)).trans ((af.get (by decide) (by simp)).trans hidx)
  obtain ⟨t,kc,bt,hkc,ht⟩ := setup hc b bp lay index hl hi b8 bidx
  refine ⟨t,ka+kb+kc,ka+(kb+3)+kc,(sa.trans ab).trans bt,by omega,?_⟩
  refine ⟨ht.pc,ht.ret,ht.chains,ht.n4,ht.target,ht.height,ht.leaf,ht.selected,ht.tree,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ht.leftLo.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.leftHi.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.rightLo.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.rightHi.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact (ht.frame.get (A:=0x66010) (by decide) (by unfold ENC;decide)).trans bfloor
  · exact (ht.frame.get (A:=0x66000) (by decide) (by unfold ENC;decide)).trans bhints
  · exact (ht.regs.get (by decide)).trans b8
  · exact ((ar.trans br).trans ht.regs).mono (by simp)
  · exact ((af.trans bf).trans ht.frame).mono (by tauto)
end SigGolfCandidate.T3M.Sign.SharedLowerSetup


namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest Pieces chainCount height)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prepared_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (hsetup : SetupCode im)
    (lay : Layer) (hl : lay≠0) (leaf : Nat) (p : PreparedLower) (digits : List Nat)
    (hd : ∀ j,j<43 → digits.getD j 0<8)
    (s : MachineState) (hp : s.pc=pcOf 22418) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits.getD j 0))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay.val j d) ((p.prefixes.getD j []).getD d 0))
    (ha : DigsAt s (sigBase lay.val+688) (preparedPieces lay leaf p digits).2) :
    ∃ t k,Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (sigBase lay.val) (preparedPieces lay leaf p digits).1 ∧
      DigsAt t (sigBase lay.val+688) (preparedPieces lay leaf p digits).2 ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => sigBase lay.val≤A ∧ A<sigBase lay.val+688) := by
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have hbound := lay.isLt
  obtain ⟨t,k,hs,hk,tp,tv,tr,tf⟩ := reveal_steps hc hbcode hsetup lay.val (by omega) (by omega)
    (fun j => digits.getD j 0) (fun j d => (p.prefixes.getD j []).getD d 0) hd s hp h8 hb hv
  refine ⟨t,k,hs,hk,tp,?_,?_,tr,tf⟩
  · have hcc : chainCount lay=43 := by fin_cases lay <;> simp_all [chainCount]
    simpa [preparedPieces,hcc] using tv
  · intro j hj
    have hj' : j<height lay := by simpa [preparedPieces] using hj
    have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
    exact (ha j hj).frame tf
      (by unfold sigBase;split_ifs <;> omega)
      (by intro h;omega)
      (by intro h;omega)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_hooks : CanonicalHooks.Code Images.signImage := by
  constructor
  · constructor <;> sign_slice_fast
  all_goals sign_slice_fast


end SigGolfCandidate.T3M.Sign.SharedSearchCode

namespace SigGolfCandidate.T3M.Sign.SharedControlTail
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_initResidual : CodeAt Images.signImage (pcOf 22226) initResidualCode := by
  sign_slice_fast
theorem installed_firstLayer : CodeAt Images.signImage (pcOf 22239) firstLayerCode := by
  sign_slice_fast
theorem installed_nextLayer : CodeAt Images.signImage (pcOf 22457) nextLayerCode := by
  sign_slice_fast
theorem installed_topProduce : CodeAt Images.signImage (pcOf 22478) topProduceCode := by
  sign_slice_fast

end SigGolfCandidate.T3M.Sign.SharedControlTail
namespace SigGolfCandidate.T3M.Sign.SharedLowerRegisters
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedLowerRegisters
namespace SigGolfCandidate.T3M.Sign.SharedLowerCopy
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : CodeAt Images.signImage (pcOf 22409) code := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedLowerCopy

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def code : List (BitVec 32) := bv_list% 32 [0xfffe37,0xe0e13,0x260e0ba3,0xff0fd06f]
sym_block block := symRun {noAlias:=true} code (pcOf 24661) 6

theorem steps {im : Image} (hc : CodeAt im (pcOf 24661) code)
    (s : MachineState) (hp : s.pc=pcOf 24661) (flag : Nat) (hf : CfTableOK flag s) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22100 ∧ CfTableOK 0 t ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=TOP_DATA+624) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [block.res,rv_simp]
  · intro i hi hj
    have old:=hf i hi hj
    rw [getByte_eq_word _ _ (by unfold TOP_DATA;omega)]
    rw [getByte_eq_word _ _ (by unfold TOP_DATA;omega)] at old
    interval_cases i <;> simp only [cfByte] at old ⊢ <;>
      simp [block.res,rv_simp,TOP_DATA] at old ⊢ <;> try exact old
    all_goals first
      | exact extractByte_replaceByte_same _ _ (by decide) _
      | rw [extractByte_replaceByte_diff _ _ _ (by decide) (by decide) (by decide)];exact old
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n []
    rw [if_neg (by unfold TOP_DATA at hn;omega)]
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : CodeAt Images.signImage (pcOf 24661) code := by
  sign_slice_fast
theorem installed_jump : CodeAt Images.signImage (pcOf 378) [0x36d1706f] := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem byte_result (s : MachineState) (A : Nat) (ha : A<2^64) :
    (block.res.toState s).getByte (BitVec.ofNat 64 A) =
      if A=TOP_DATA+631 then 0 else s.getByte (BitVec.ofNat 64 A) := by
  rw [getByte_eq_word _ _ ha,getByte_eq_word _ _ ha]
  simp only [Result.toState_getMem,block.res];t3n []
  rw [Nat.mod_eq_of_lt (show A/8*8<18446744073709551616 by omega)]
  by_cases he : A/8*8=16773744
  · rw [if_pos he]
    by_cases hf : A=TOP_DATA+631
    · rw [if_pos hf]
      subst A
      exact extractByte_replaceByte_same _ _ (by decide) _
    · rw [if_neg hf]
      have hm : A%8≠7 := by unfold TOP_DATA at hf;omega
      rw [extractByte_replaceByte_diff _ _ _ (Nat.mod_lt _ (by decide)) (by decide) hm]
      rw [show BitVec.ofNat 64 (A/8*8)=16773744#64 by rw [he]]
  · rw [if_neg he,if_neg (by unfold TOP_DATA;omega)]
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem tables_result (s : MachineState) (flag : Nat) (ht : TableOK s)
    (hf : CfFlagOK flag s) (hr : Reward.LowerTablesOK s) (h51 : T51.T51TableW 0xFFF800 s) :
    TableOK (block.res.toState s) ∧ CfFlagOK 0 (block.res.toState s) ∧
      Reward.LowerTablesOK (block.res.toState s) ∧ T51.T51TableW 0xFFF800 (block.res.toState s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_neg (by omega)]
    exact ht i hi
  · unfold CfFlagOK
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_pos rfl]
    rfl
  · intro i hi hj
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_neg (by omega)]
    exact hr i hi hj
  · refine h51.frame (W:=fun A=>A=TOP_DATA+624) ?_ (by decide) (by decide) (fun k hk => by unfold TOP_DATA;omega)
    intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n []
    rw [if_neg (by unfold TOP_DATA at hn;omega)]
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_kernel (P : Prop) (hP : P) : KernAt Images.signImage 543 P := by
  refine ⟨⟨?_,?_,?_⟩,Or.inr rfl,?_,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  all_goals sign_slice_fast


theorem installed_searchKernel : KernAt Images.signImage 543 (CanonicalHooks.Code Images.signImage) :=
  installed_kernel _ installed_hooks
end SigGolfCandidate.T3M.Sign.SharedSearchCode

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

structure Tables (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  z40 : s.getMem (BitVec.ofNat 64 (ENC+40))=0
  table : TableOK s
  /-- Campaign T51: only the choice flag byte. -/
  cf : CfFlagOK 0 s
  /-- Campaign T51: only the lower reward tables. -/
  reward : Reward.LowerTablesOK s
  zt : ZeroCap.ZtOK 543 s
  /-- Campaign T51: the packed top tables at `0xFFF800` (473 `lwu` words). -/
  t51 : T51.T51TableW 0xFFF800 s

def TableCells (A : Nat) : Prop := A=ENC+40 ∨ TOP_DATA≤A ∧ A<TOP_DATA+3944 ∨ 16691072≤A ∧ A<16691200

theorem Tables.frame {s t : MachineState} {W : Nat→Prop} {regs : List Reg}
    (h : Tables s) (hf : Frame s t W) (hr : RegsExcept s t regs) (h5 : .x5∉regs)
    (hw : ∀ A, TableCells A → ¬W A) : Tables t := by
  refine ⟨(hr.get h5).trans h.x5,?_,?_,?_,?_,?_,?_⟩
  · exact (hf.get (by unfold ENC;decide) (hw _ (Or.inl rfl))).trans h.z40
  · exact h.table.frame hf (fun i hi => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.cf.frame hf (fun i hi hj => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.reward.frame hf (fun i hi hj => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.zt.frame hf (fun r hr => hw _ (Or.inr (Or.inr (by
      simp only [ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; omega))))
  · exact h.t51.frame hf (by decide) (by decide) (fun k hk => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))

def topArgs (index : Nat) (pair : Digest×Digest) (extra : Nat) : Canonical.CsArgs :=
  ⟨0,(route index 0).2,(route index 0).1,.pair pair.1 pair.2,22208,14 + extra⟩

theorem top_pre (index : Nat) (hi : index<2^31) (pair : Digest×Digest)
    (extra : Nat) (he : extra ≤ 4)
    (s t : MachineState) (h : SharedTopSetup.Post index pair.1 pair.2 s t)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    Canonical.CsPre 543 (topArgs index pair extra) t := by
  have hr : (route index 0).2=0 := T3.route_top_tree index hi
  have hl : (route index 0).1=index/2^19 := by
    change index/2^19%2^12=index/2^19
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨h.pc,h.ret,ht.x5,h.x8,?_,?_,h.x17,h.x26,h.x27,?_,?_,?_,Or.inl hr,
    h.left.1,h.left.2,hc,ht.z40,h.right.1,h.right.2,ht.table,ht.cf,ht.reward,ht.zt,
    (show 14 + extra < 22 by omega),?_,?_,fun _ => ht.t51⟩
  · simpa [topArgs,hr] using h.x9
  · simpa only [topArgs,hl] using h.x18
  · change (route index 0).2<2^32;rw [hr];decide
  · change (route index 0).1<2^32;rw [hl];omega
  · change (route index 0).2*2^12+(route index 0).1<2^32;rw [hr,hl];omega
  · intro _
    refine ⟨extra,he,rfl,?_,?_⟩
    · exact (h.frame.get (A := EOUT + 32) (by unfold EOUT; decide)
        (by unfold EOUT ENC; decide)).trans htier.low
    · exact (h.frame.get (A := EOUT + 40) (by unfold EOUT; decide)
        (by unfold EOUT ENC; decide)).trans htier.high
  · intro hn;exact (hn rfl).elim

def lowerArgs (lay : Layer) (index floor : Nat) (pair : Digest×Digest) : Canonical.CsArgs :=
  ⟨lay,(route index lay).2,(route index lay).1,.pair pair.1 pair.2,22418,floor⟩

theorem lower_pre (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31)
    (pair : Digest×Digest) (s t : MachineState) (h : SharedLowerSetup.CallPost lay.val index residual hints s t)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hp0 : DigAt s (0x66040+32*lay.val) pair.1)
    (hp1 : DigAt s (0x66050+32*lay.val) pair.2)
    (hf : CanonicalPolicy.threshold lay.val residual<22) :
    Canonical.CsPre 543 (lowerArgs lay index (CanonicalPolicy.threshold lay.val residual) pair) t := by
  have htree : (route index lay).2<2^32 := by fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  have hleaf : (route index lay).1<2^32 := by fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  have hroute : (route index lay).2*2^height lay+(route index lay).1<2^32 := by
    fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  refine ⟨h.pc,h.ret,ht.x5,h.layer,?_,?_,?_,?_,?_,htree,hleaf,hroute,Or.inr ?_,
    h.leftLo.trans hp0.1,?_,hc,ht.z40,h.rightLo.trans hp1.1,?_,ht.table,ht.cf,ht.reward,ht.zt,hf,?_,?_,?_⟩
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.tree
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.leaf
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.target
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.chains
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.n4
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.height
  · change t.getMem (BitVec.ofNat 64 (ENC+8))=pair.1.extractLsb' 64 64
    have he : 0x66048+32*lay.val=(0x66040+32*lay.val)+8 := by omega
    exact h.leftHi.trans (he ▸ hp0.2)
  · change t.getMem (BitVec.ofNat 64 (ENC+56))=pair.2.extractLsb' 64 64
    have he : 0x66058+32*lay.val=(0x66050+32*lay.val)+8 := by omega
    exact h.rightHi.trans (he ▸ hp1.2)
  · intro he;exact (hl he).elim
  · intro _;exact h.floor
  · intro he;exact (hl he).elim

theorem credit_small (lay : Layer) (low : Bool) (ds : List Nat) : CanonicalPolicy.credit lay low ds<2^32 := by
  have hword : wordCredit lay ds≤T3.chainCount lay := by
    simpa only [wordCredit,List.length_range] using List.length_filter_le (fun i => decide (ds.getD i 0+1=T3.maxDigit lay i)) (List.range (T3.chainCount lay))
  have hcopy : savedCopies lay ds≤T3.chainCount lay := by
    simpa only [savedCopies,List.length_range] using List.length_filter_le (fun i => decide (safeZeroCopy lay ds i)) (List.range (T3.chainCount lay))
  have hc : T3.chainCount lay≤54 := by fin_cases lay <;> decide
  have hb := CanonicalPolicy.pathBonus_le lay low
  unfold CanonicalPolicy.credit CanonicalPolicy.pathReward CanonicalPolicy.reward
  omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def ValueWrites (A : Nat) : Prop :=
  ∃ lay : Nat, 1≤lay ∧ lay≤3 ∧ SharedRootControl.sigBase lay≤A ∧ A<SharedRootControl.sigBase lay+688

def WorkWrites (A : Nat) : Prop :=
  (ENC≤A ∧ A<ENC+40) ∨ (ENC+48≤A ∧ A<ENC+64) ∨
  (EOUT≤A ∧ A<EOUT+32) ∨ (DIGITS≤A ∧ A<DIGITS+64) ∨
  (0x66000≤A ∧ A<0x66020 ∨ A=0x667F8) ∨ (0x66100≤A ∧ A<0x66138) ∨ ValueWrites A

theorem work_bound {A : Nat} (h : WorkWrites A) : A<0x66800 := by
  rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_table {A : Nat} (h : TableCells A) : ¬WorkWrites A := by
  rcases h with rfl|h
  · intro h
    rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
    all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
    unfold SharedRootControl.sigBase at hb he
    split_ifs at hb he <;> unfold ENC at * <;> omega
  · intro hw
    have := work_bound hw
    unfold TOP_DATA at h
    omega

theorem work_not_meta {A : Nat} (hl : 0x66040≤A) (hu : A<0x660c0) : ¬WorkWrites A := by
  intro h
  rcases h with h|h|h|h|h|h|⟨lay,hlay,ulay,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_index : ¬WorkWrites 0x20550 := by
  intro h
  rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_path (lay : Layer) (hl : lay≠0) (j half : Nat)
    (hj : j<height lay) (hh : half<2) :
    ¬WorkWrites (SharedRootControl.sigBase lay.val+688+16*j+8*half) := by
  intro h
  rcases h with h|h|h|h|h|h|⟨other,ho1,ho3,hlo,hhi⟩
  all_goals first
    | (fin_cases lay <;> simp_all [SharedRootControl.sigBase,height,ENC,EOUT,DIGITS] <;> omega)
    | skip
  interval_cases other <;> fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega

theorem stored_frame {s t : MachineState} (hf : Frame s t WorkWrites)
    (lay : Layer) (hl : lay≠0) (index : Nat) (p : PreparedLower)
    (h : SharedRootControl.Stored lay index p s) : SharedRootControl.Stored lay index p t := by
  have hln : 1≤lay.val := by have := lay.isLt;by_contra hh;apply hl;exact Fin.ext (by omega)
  have hlu : lay.val<4 := lay.isLt
  refine ⟨h.plen,?_,?_,?_,?_⟩
  · intro i hi k hk
    apply (h.saved i hi k hk).frame hf
    · unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer;omega
    · intro hw;have := work_bound hw
      unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer at this;omega
    · intro hw;have := work_bound hw
      unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer at this;omega
  · intro j hj
    have hj' : j<height lay := by simpa only [List.length_map,List.length_range] using hj
    apply (h.path j hj).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega
    · simpa only [Nat.mul_zero,Nat.add_zero] using work_not_path lay hl j 0 hj' (by decide)
    · simpa only [Nat.mul_one] using work_not_path lay hl j 1 hj' (by decide)
  · apply h.left.frame hf
    · unfold SharedRootControl.metaAddr;omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
  · apply h.right.frame hf
    · unfold SharedRootControl.metaAddr;omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega

structure Stable (index : Nat) (prepared : PreparedRoots) (forest : Digest×Digest) (s : MachineState) : Prop where
  tables : Tables s
  indexMem : s.getMem (0x20550#64)=BitVec.ofNat 64 index
  one : SharedRootControl.Stored 1 index prepared.one s
  two : SharedRootControl.Stored 2 index prepared.two s
  three : SharedRootControl.Stored 3 index prepared.three s
  forestL : DigAt s 0x660a0 forest.1
  forestR : DigAt s 0x660b0 forest.2

theorem Stable.frame {s t : MachineState} {index : Nat} {prepared : PreparedRoots} {forest : Digest×Digest}
    {regs : List Reg} (h : Stable index prepared forest s) (hf : Frame s t WorkWrites)
    (hr : RegsExcept s t regs) (h5 : .x5∉regs) : Stable index prepared forest t := by
  refine ⟨h.tables.frame hf hr h5 (fun _ => work_not_table),
    (hf.get (by decide) work_not_index).trans h.indexMem,
    stored_frame hf 1 (by decide) _ _ h.one,stored_frame hf 2 (by decide) _ _ h.two,
    stored_frame hf 3 (by decide) _ _ h.three,?_,?_⟩
  · exact h.forestL.frame hf (by decide) (work_not_meta (by decide) (by decide)) (work_not_meta (by decide) (by decide))
  · exact h.forestR.frame hf (by decide) (work_not_meta (by decide) (by decide)) (work_not_meta (by decide) (by decide))

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure TopTailSteps (im : Image) : Prop where
  save : ∀ s : MachineState, s.pc=pcOf 22208 →
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56)
  init : ∀ s : MachineState, s.pc=pcOf 22226 → ∀ extra : Nat,
    s.getMem (0x66028#64)=BitVec.ofNat 64 (69 + extra) →
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22230 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (69 + extra) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008)
  residual : ∀ s : MachineState, s.pc=pcOf 22230 → ∀ r c : Nat, r<2^32 → c<2^32 →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22239 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  first : ∀ s : MachineState, s.pc=pcOf 22239 →
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False)

def TopTailWrites (A : Nat) : Prop := (0x66100≤A ∧ A<0x66138) ∨ A=0x66008

theorem topTail_subset {A : Nat} (h : TopTailWrites A) : WorkWrites A := by
  rcases h with h|rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

structure TopTailPost (extra : Nat) (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64
    (CanonicalPolicy.nextResidual (69 + extra) 0 low ds)
  saved : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))
  regs : RegsExcept s t [.x6,.x7,.x8,.x28,.x29]
  frame : Frame s t TopTailWrites

theorem top_tail {im : Image} (hc : TopTailSteps im)
    (s : MachineState) (hp : s.pc=pcOf 22208) (extra : Nat) (he : extra ≤ 4)
    (low : Bool) (ds : List Nat)
    (hpool : s.getMem (0x66028#64)=BitVec.ofNat 64 (69 + extra))
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤31 ∧ TopTailPost extra low ds s t := by
  obtain ⟨a,sa,ap,asaved,ar,af⟩ := hc.save s hp
  have apool : a.getMem (0x66028#64)=BitVec.ofNat 64 (69 + extra) :=
    (af.get (A := 0x66028) (by decide) (by omega)).trans hpool
  obtain ⟨b,ab,bp,brm,br,bf⟩ := hc.init a ap extra apool
  have bcm : b.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds) :=
    (bf.get (by decide) (by decide)).trans ((af.get (by decide) (by omega)).trans hcm)
  obtain ⟨c,k,bc,hk,cp,crm,cr,cf⟩ := hc.residual b bp (69 + extra)
    (CanonicalPolicy.credit 0 low ds) (by omega) (credit_small _ _ _) brm bcm
  obtain ⟨t,ct,tp,t8,tr,tf⟩ := hc.first c cp
  refine ⟨t,18+4+k+1,((sa.trans ab).trans bc).trans ct,by omega,?_,t8,?_,?_,?_,?_⟩
  · exact tp
  · exact (tf.get (by decide) (by simp)).trans crm
  · intro i hi
    exact (tf.get (by omega) (by simp)).trans ((cf.get (by omega) (by omega)).trans
      ((bf.get (by omega) (by omega)).trans (asaved i hi)))
  · exact (((ar.trans br).trans cr).trans tr).mono (by simp)
  · exact (((af.trans bf).trans cf).trans tf).mono (by
      intro A hA h;rcases h with ((h|h)|h)|h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
      · exact h.elim)

theorem top_residual_small {extra : Nat} (he : extra ≤ 4) {low : Bool} {ds : List Nat}
    (h : 14 + extra ≤ CanonicalPolicy.credit 0 low ds) :
    CanonicalPolicy.nextResidual (69 + extra) 0 low ds<56 := by
  unfold CanonicalPolicy.nextResidual;omega

theorem words_bytes {s t : MachineState} (A B n : Nat) (hA : A%8=0) (hB : B%8=0)
    (hs : A+8*n<2^64) (ht : B+8*n<2^64)
    (hw : ∀ i,i<n → t.getMem (BitVec.ofNat 64 (B+8*i))=s.getMem (BitVec.ofNat 64 (A+8*i)))
    (j : Nat) (hj : j<8*n) :
    t.getByte (BitVec.ofNat 64 (B+j))=s.getByte (BitVec.ofNat 64 (A+j)) := by
  rw [getByte_eq_word t (B+j) (by omega),getByte_eq_word s (A+j) (by omega)]
  have ha : (A+j)/8*8=A+8*(j/8) := by omega
  have hb : (B+j)/8*8=B+8*(j/8) := by omega
  rw [ha,hb,hw _ (by omega)]
  congr 1
  omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure LowerTailSteps (im : Image) : Prop where
  reveal : ∀ (lay : Layer), lay≠0 → ∀ (leaf : Nat) (p : PreparedLower) (ds : List Nat),
    (∀ j,j<43 → ds.getD j 0<8) → ∀ s : MachineState, s.pc=pcOf 22418 →
    s.getReg .x8=BitVec.ofNat 64 lay.val →
    (∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)) →
    (∀ j,j<43 → ∀ d,d<8 → DigAt s (ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer lay.val j d) ((p.prefixes.getD j []).getD d 0)) →
    DigsAt s (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2 →
    ∃ t k,Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay leaf p ds).1 ∧
      DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2 ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688)
  residual : ∀ s : MachineState, s.pc=pcOf 22448 → ∀ r c : Nat, r<2^32 → c<2^32 →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22457 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  next : ∀ s : MachineState, s.pc=pcOf 22457 → ∀ lay : Nat, (1≤lay ∧ lay≤3) →
    s.getReg .x8=BitVec.ofNat 64 lay →
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22240 else pcOf 22460) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧ RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False)

def LowerTailWrites (lay : Layer) (A : Nat) : Prop :=
  (SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688) ∨ A=0x66008

theorem lowerTail_subset (lay : Layer) (hl : lay≠0) {A : Nat} (h : LowerTailWrites lay A) : WorkWrites A := by
  have hh := lay.isLt
  have hz : lay.val≠0 := fun h=>hl (Fin.ext h)
  rcases h with h|rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lay.val,by omega,by omega,h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

structure LowerTailPost (lay : Layer) (leaf residual : Nat) (p : PreparedLower) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=(if lay.val<3 then pcOf 22240 else pcOf 22460)
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual residual lay low ds)
  values : DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay leaf p ds).1
  path : DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2
  regs : RegsExcept s t [.x6,.x7,.x8,.x21,.x22,.x23,.x24,.x28]
  frame : Frame s t (LowerTailWrites lay)

theorem lower_tail {im : Image} (hc : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (leaf residual : Nat) (p : PreparedLower) (low : Bool) (ds : List Nat)
    (hd : ∀ j,j<43 → ds.getD j 0<8) (s : MachineState) (hp : s.pc=pcOf 22418)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer lay.val j d) ((p.prefixes.getD j []).getD d 0))
    (ha : DigsAt s (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2)
    (hr : residual<2^32) (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual)
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit lay low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤587 ∧ LowerTailPost lay leaf residual p low ds s t := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  have hsbase : SharedRootControl.sigBase lay.val+1024<0x66000 := by unfold SharedRootControl.sigBase;split_ifs <;> omega
  obtain ⟨a,ka,sa,hka,ap,av,aa,ar,af⟩ := hc.reveal lay hl leaf p ds hd s hp h8 hb hv ha
  obtain ⟨b,kb,ab,hkb,bp,brm,br,bf⟩ := hc.residual a ap residual (CanonicalPolicy.credit lay low ds) hr (credit_small _ _ _)
    ((af.get (by decide) (by omega)).trans hrm) ((af.get (by decide) (by omega)).trans hcm)
  have b8 := (br.get (by decide : Reg.x8∉[.x6,.x7,.x28])).trans ((ar.get (by decide)).trans h8)
  obtain ⟨t,bt,tp,t8,tr,tf⟩ := hc.next b bp lay.val hln b8
  refine ⟨t,ka+kb+3,(sa.trans ab).trans bt,by omega,tp,t8,?_,?_,?_,?_,?_⟩
  · exact (tf.get (by decide) (by simp)).trans brm
  · intro j hj
    have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
    have hj' : j<43 := by simpa [preparedPieces,hcc] using hj
    apply (av j hj).frame (bf.trans tf)
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro h;rcases h with h|h;omega;exact h.elim
    · intro h;rcases h with h|h;omega;exact h.elim
  · intro j hj
    have hj' : j<height lay := by simpa [preparedPieces] using hj
    have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
    apply (aa j hj).frame (bf.trans tf)
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro h;rcases h with h|h;omega;exact h.elim
    · intro h;rcases h with h|h;omega;exact h.elim
  · exact ((ar.trans br).trans tr).mono (by simp)
  · exact ((af.trans bf).trans tf).mono (by
      intro A hA h;rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def LowerWrites (lay : Layer) (A : Nat) : Prop :=
  (ENC≤A ∧ A<ENC+40) ∨ (ENC+48≤A ∧ A<ENC+64) ∨
  (EOUT≤A ∧ A<EOUT+32) ∨ (DIGITS≤A ∧ A<DIGITS+64) ∨
  (0x66000≤A ∧ A<0x66020 ∨ A=0x667F8) ∨ (SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688)

theorem lowerWrites_subset (lay : Layer) (hl : lay≠0) {A : Nat} (h : LowerWrites lay A) : WorkWrites A := by
  have hh := lay.isLt
  have hz : lay.val≠0 := fun h=>hl (Fin.ext h)
  rcases h with h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lay.val,by omega,by omega,h⟩)))))

theorem lowerWrites_saved (lay : Layer) (i : Nat) (hi : i<7) : ¬LowerWrites lay (0x66100+8*i) := by
  intro h
  rcases h with h|h|h|h|h|h
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at h;split_ifs at h <;> omega

theorem csWrites_subset {A : Nat} (h : Canonical.CsW A) : WorkWrites A := by
  unfold Canonical.CsW DigW CanonicalHooks.CreditW at h
  unfold WorkWrites
  simp only [Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG,ENC,EOUT,DIGITS] at *
  omega

theorem csWrites_lower (lay : Layer) {A : Nat} (h : Canonical.CsW A) : LowerWrites lay A := by
  unfold Canonical.CsW DigW CanonicalHooks.CreditW at h
  unfold LowerWrites
  simp only [Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG,ENC,EOUT,DIGITS] at *
  omega

theorem topSetupWrites_subset {A : Nat} (h : A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) : WorkWrites A := by
  unfold WorkWrites;omega

theorem lowerSetupWrites_subset (lay : Layer) {A : Nat}
    (h : A=0x66000 ∨ A=0x66010 ∨ A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) : LowerWrites lay A := by
  unfold LowerWrites;omega

def SavedTop (ds : List Nat) (t : MachineState) : Prop :=
  ∃ s : MachineState,
    (∀ j,j<51 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)) ∧
    (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i)))

theorem SavedTop.frame {ds : List Nat} {s t : MachineState} {W : Nat→Prop}
    (h : SavedTop ds s) (hf : Frame s t W) (hw : ∀ i,i<7 → ¬W (0x66100+8*i)) : SavedTop ds t := by
  obtain ⟨u,hu,hmem⟩ := h
  exact ⟨u,hu,fun i hi=>(hf.get (by omega) (hw i hi)).trans (hmem i hi)⟩

theorem SavedTop.restore {ds : List Nat} {s t : MachineState} (h : SavedTop ds s)
    (hw : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) :
    ∀ j,j<51 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0) := by
  obtain ⟨u,hu,hmem⟩ := h
  intro j hj
  exact (words_bytes DIGITS DIGITS 7 (by unfold DIGITS;decide) (by unfold DIGITS;decide)
    (by unfold DIGITS;decide) (by unfold DIGITS;decide) (fun i hi=>(hw i hi).trans (hmem i hi)) j (by omega)).trans (hu j hj)

theorem lower_decode_digits (lay : Layer) (hl : lay≠0) {ds : List Nat}
    (hd : ∃ v,CanonicalPolicy.decode lay v=some ds) : ∀ j,j<43 → ds.getD j 0<8 := by
  obtain ⟨v,hv⟩ := hd
  have he : CanonicalPolicy.normalLayer lay=1 := by simp [CanonicalPolicy.normalLayer,hl]
  change T3.decode (CanonicalPolicy.normalLayer lay) v=some ds at hv
  rw [he] at hv
  intro j hj
  have hb := T3.decode_digit_max hv j (by simpa [T3.chainCount] using hj)
  simpa [T3.maxDigit] using Nat.lt_succ_of_le hb

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure FinishSteps (im : Image) : Prop where
  restore : ∀ s : MachineState,s.pc=pcOf 22460 →
    ∃ t,Steps im s 18 18 t ∧ t.pc=pcOf 22478 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56)
  produce : ∀ s : MachineState,s.pc=pcOf 22478 → ∀ index : Nat,index<2^31 →
    s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    ∃ t,Steps im s 12 12 t ∧ SharedControlTail.TopPost index s t

structure Finished (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=51
  n4 : t.getReg .x27=51
  target : t.getReg .x17=152
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  stable : Stable index p forest t
  digits : ∀ j,j<51 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56)

theorem finish_steps {im : Image} (hc : FinishSteps im) (index : Nat) (hi : index<2^31)
    (p : PreparedRoots) (forest : Digest×Digest) (ds : List Nat) (s : MachineState)
    (hp : s.pc=pcOf 22460) (hstable : Stable index p forest s) (hsaved : SavedTop ds s)
    (hsum : (s.getReg .x25).toNat≤201) :
    ∃ t,Steps im s 30 30 t ∧ Finished index p forest ds s t := by
  obtain ⟨a,sa,ap,acopy,ar,af⟩ := hc.restore s hp
  have haf : Frame s a WorkWrites := af.mono (by intro A hA h;unfold WorkWrites;omega)
  have hsta : Stable index p forest a := hstable.frame haf ar (by decide)
  obtain ⟨t,at',ht⟩ := hc.produce a ap index hi hsta.indexMem
  have hstt : Stable index p forest t := hsta.frame (ht.frame.mono (by simp)) ht.regs (by decide)
  refine ⟨t,sa.trans at',ht.pc,ht.layer,ht.tree,ht.height,ht.chains,ht.n4,ht.target,ht.leaf,ht.selected,hstt,?_,?_,?_⟩
  · intro j hj
    rw [ht.frame.getByte (by unfold DIGITS;omega) (by simp)]
    exact hsaved.restore acopy j hj
  · rw [ht.regs.get (by decide),ar.get (by decide)];exact hsum
  · exact (af.trans ht.frame).mono (by tauto)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure SearchCalls (im : Image) (sk : BitVec 256) : Prop where
  call : ∀ (A : Canonical.CsArgs) (s : MachineState), Canonical.CsPre 543 A s →
    TBSim im sk s (Canonical.csCost A.lay)
      (CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (searchLimit A.lay))
      (Canonical.CsPost im 543 A s)

structure TopSetupSteps (im : Image) : Prop where
  setup : ∀ s : MachineState, s.pc=pcOf 22182 → ∀ index : Nat,index<2^31 →
    s.getMem 0x20550=BitVec.ofNat 64 index → ∀ left right : Digest,
    DigAt s 0x66040 left → DigAt s 0x66050 right →
    ∃ t,Steps im s 26 26 t ∧ SharedTopSetup.Post index left right s t

/-- Campaign T51 (as R6): no `x25` bound after the top stage (the T51 unpacker clobbers `s9 = x25`); the top leaf's
`x25` bound comes from the layer-3 search (`Finished.sum`). -/
structure TopReady (extra : Nat) (index : Nat) (p : PreparedRoots)
    (forest : Digest×Digest) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64
    (CanonicalPolicy.nextResidual (69 + extra) 0 low ds)
  small : CanonicalPolicy.nextResidual (69 + extra) 0 low ds<56
  hints : t.getMem (0x66000#64)=0
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some ds
  length : ds.length=51
  saved : SavedTop ds t
  frame : Frame s t WorkWrites

def SearchError (im : Image) (t : MachineState) : Prop :=
  t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)

def TopStagePost (im : Image) (extra : Nat) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => TopReady extra index p forest low ds s t

theorem top_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : TopSetupSteps im) (htailSteps : TopTailSteps im)
    (extra : Nat) (he : extra ≤ 4)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost 0+57)
      (CanonicalPolicy.layerCounterSearchAt 0 (14 + extra) (route index 0).2 (route index 0).1
        (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im extra index p forest s) := by
  obtain ⟨a,sa,ha⟩ := ht.setup s hp index hi hstable.indexMem _ _ hstable.one.left hstable.one.right
  have haf : Frame s a WorkWrites := ha.frame.mono (fun _ _=>topSetupWrites_subset)
  have hsta : Stable index p forest a := hstable.frame haf ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold ENC;omega) (by unfold ENC;omega)).trans hcv⟩
  have htiera : SigGolfCandidate.T3M.Sign.SharedTier.At extra a :=
    htier.frame ha.frame (by unfold EOUT ENC; decide)
      (by unfold EOUT ENC; decide) (by unfold EOUT ENC; decide)
  have H := hs.call (topArgs index (topPair 1 p.one.levels) extra) a
    (top_pre index hi _ extra he s a ha htier hsta.tables hac)
  have Htail : TBSim im sk a (Canonical.csCost 0+31)
      (CanonicalPolicy.layerCounterSearchAt 0 (14 + extra) (route index 0).2 (route index 0).1
        (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im extra index p forest s) := by
    have hb := TBSim.bind H (f:=fun r=>pure r) (W₂:=31)
      (Q₂:=TopStagePost im extra index p forest s) (by
      intro r u hu
      cases r with
      | none => exact (TBSim.pure (a:=none) (s:=u)
          (Q:=TopStagePost im extra index p forest s) hu).mono (by omega) (fun _ _ h=>h)
      | some pair =>
        obtain ⟨c,ds,low⟩ := pair
        rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
        have huf : Frame a u WorkWrites := uf.mono (fun _ _=>csWrites_subset)
        have hstu : Stable index p forest u := hsta.frame huf ur (by decide)
        have upool : u.getMem (0x66028#64)=BitVec.ofNat 64 (69 + extra) :=
          (uf.get (A := 0x66028) (by decide) (by
            unfold Canonical.CsW CanonicalHooks.CreditW DigW; omega)).trans htiera.pool
        obtain ⟨t,k,ut,hk,htail⟩ := top_tail htailSteps u up extra he low ds upool ucredit
        have htf : Frame u t WorkWrites := htail.frame.mono (fun _ _=>topTail_subset)
        have hstt : Stable index p forest t := hstu.frame htf htail.regs (by decide)
        refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
        refine ⟨htail.pc,htail.layer,htail.residual,top_residual_small he hfloor,
          ?_,?_,hstt,hdec,hlen,⟨u,hdigs,htail.saved⟩,?_⟩
        · exact (htail.frame.get (by decide) (by unfold TopTailWrites;omega)).trans
            ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
              ((ha.frame.get (by decide) (by unfold ENC;omega)).trans hh))
        · exact ⟨c.toNat,by omega,
            (htail.frame.get (by unfold ENC;omega) (by unfold TopTailWrites ENC;omega)).trans uc32⟩
        · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
    simpa only [bind_pure,topArgs,lowerArgs] using hb
  exact (TBSim.steps sa Htail).mono (by omega) (fun _ _ h=>h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def stageBound (lay : Layer) : Nat := if lay.val=1 then 56 else if lay.val=2 then 41 else 22

def preparedAt (p : PreparedRoots) (lay : Layer) : PreparedLower :=
  if lay.val=1 then p.one else if lay.val=2 then p.two else p.three

def messageAt (p : PreparedRoots) (forest : Digest×Digest) (lay : Layer) : Digest×Digest :=
  if lay.val=1 then topPair 2 p.two.levels else if lay.val=2 then topPair 3 p.three.levels else forest

theorem Stable.prepared {index : Nat} {p : PreparedRoots} {forest : Digest×Digest} {s : MachineState}
    (h : Stable index p forest s) (lay : Layer) (hl : lay≠0) :
    SharedRootControl.Stored lay index (preparedAt p lay) s := by
  fin_cases lay <;> first | exact (hl rfl).elim | exact h.one | exact h.two | exact h.three

theorem Stable.message {index : Nat} {p : PreparedRoots} {forest : Digest×Digest} {s : MachineState}
    (h : Stable index p forest s) (lay : Layer) (hl : lay≠0) :
    DigAt s (0x66040+32*lay.val) (messageAt p forest lay).1 ∧
    DigAt s (0x66050+32*lay.val) (messageAt p forest lay).2 := by
  fin_cases lay
  · exact (hl rfl).elim
  · exact ⟨h.two.left,h.two.right⟩
  · exact ⟨h.three.left,h.three.right⟩
  · exact ⟨h.forestL,h.forestR⟩

theorem floor_small (lay : Layer) (hl : lay≠0) (r : Nat) (hr : r<stageBound lay) :
    CanonicalPolicy.threshold lay.val r<22 ∧ (lay.val=1 → CanonicalPolicy.threshold lay.val r<16) := by
  fin_cases lay
  · exact (hl rfl).elim
  · change CanonicalPolicy.threshold 1 r<22 ∧ (1=1 → CanonicalPolicy.threshold 1 r<16)
    have : CanonicalPolicy.threshold 1 r<16 := CanonicalPolicy.lower_one_floor_lt ⟨r,hr⟩
    exact ⟨by omega, fun _ => this⟩
  · change CanonicalPolicy.threshold 2 r<22 ∧ (2=1 → _)
    have : CanonicalPolicy.threshold 2 r≤19 := (CanonicalPolicy.lower_two_progress ⟨r,hr⟩).1
    exact ⟨by omega, fun h => absurd h (by decide)⟩
  · change CanonicalPolicy.threshold 3 r<22 ∧ (3=1 → _)
    rw [CanonicalPolicy.lower_three_progress r hr];exact ⟨hr, fun h => absurd h (by decide)⟩

theorem next_stage_bound (lay : Layer) (hl : lay≠0) (r : Nat) (hr : r<stageBound lay)
    (low : Bool) (ds : List Nat) (hd : CanonicalPolicy.threshold lay.val r≤CanonicalPolicy.credit lay low ds) :
    (∀ hnext : lay.val<3, CanonicalPolicy.nextResidual r lay low ds<stageBound ⟨lay.val+1,by omega⟩) ∧
    (lay.val=3 → CanonicalPolicy.nextResidual r lay low ds=0) := by
  fin_cases lay
  · exact (hl rfl).elim
  · change CanonicalPolicy.threshold 1 r≤CanonicalPolicy.credit 1 low ds at hd
    change (∀ hnext : 1<3, r-CanonicalPolicy.credit 1 low ds<41) ∧ (1=3 → r-CanonicalPolicy.credit 1 low ds=0)
    have h : r-CanonicalPolicy.threshold 1 r<41 := (CanonicalPolicy.lower_one_progress ⟨r,hr⟩).2
    constructor <;> intro hnext <;> omega
  · change CanonicalPolicy.threshold 2 r≤CanonicalPolicy.credit 2 low ds at hd
    change (∀ hnext : 2<3, r-CanonicalPolicy.credit 2 low ds<22) ∧ (2=3 → r-CanonicalPolicy.credit 2 low ds=0)
    have h : r-CanonicalPolicy.threshold 2 r<22 := (CanonicalPolicy.lower_two_progress ⟨r,hr⟩).2
    constructor <;> intro hnext <;> omega
  · change CanonicalPolicy.threshold 3 r≤CanonicalPolicy.credit 3 low ds at hd
    rw [CanonicalPolicy.lower_three_progress r hr] at hd
    change (∀ hnext : 3<3, _) ∧ (3=3 → r-CanonicalPolicy.credit 3 low ds=0)
    constructor
    · intro hh;omega
    · intro _;exact Nat.sub_eq_zero_of_le hd

structure LowerSetupSteps (im : Image) : Prop where
  setup : ∀ s : MachineState,s.pc=pcOf 22240 → ∀ lay index residual hints : Nat,
    (1≤lay ∧ lay≤3) → index<2^31 → (residual<(if lay=1 then 56 else if lay=2 then 41 else 22)) →
    s.getReg .x8=BitVec.ofNat 64 lay → s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    s.getMem (0x66008#64)=BitVec.ofNat 64 residual → s.getMem (0x66000#64)=BitVec.ofNat 64 hints →
    ∃ t k c,Steps im s k c t ∧ c≤120 ∧ SharedLowerSetup.CallPost lay index residual hints s t

structure LowerReady (lay : Layer) (index residual hints : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=if lay.val<3 then pcOf 22240 else pcOf 22460
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  residualMem : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual residual lay low ds)
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (hints+SharedHints.hintWeight lay.val*CanonicalPolicy.threshold lay.val residual)
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  values : DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay (route index lay).1 (preparedAt p lay) ds).1
  path : DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay (route index lay).1 (preparedAt p lay) ds).2
  floor : CanonicalPolicy.threshold lay.val residual≤CanonicalPolicy.credit lay low ds
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t (LowerWrites lay)

def LowerStagePost (im : Image) (lay : Layer) (index residual hints : Nat) (p : PreparedRoots)
    (forest : Digest×Digest) (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => LowerReady lay index residual hints p forest low ds s t

theorem lower_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : LowerSetupSteps im) (htail : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31) (hr : residual<stageBound lay)
    (p : PreparedRoots) (forest : Digest×Digest) (s : MachineState) (hp : s.pc=pcOf 22240)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hstable : Stable index p forest s)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual) (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost lay+707)
      (CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val residual)
        (route index lay).2 (route index lay).1 (.pair (messageAt p forest lay).1 (messageAt p forest lay).2) 0 (searchLimit lay))
      (LowerStagePost im lay index residual hints p forest s) := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨a,ka,ca,sa,hca,ha⟩ := ht.setup s hp lay.val index residual hints hln hi hr h8 hstable.indexMem hrm hhm
  have haf : Frame s a (LowerWrites lay) := ha.frame.mono (fun _ _=>lowerSetupWrites_subset lay)
  have hsta : Stable index p forest a := hstable.frame (haf.mono (fun _ _=>lowerWrites_subset lay hl)) ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold ENC;omega) (by unfold ENC;omega)).trans hcv⟩
  obtain ⟨hp0,hp1⟩ := hstable.message lay hl
  have H := hs.call (lowerArgs lay index (CanonicalPolicy.threshold lay.val residual) (messageAt p forest lay)) a
    (lower_pre lay hl index residual hints hi _ s a ha hsta.tables hac hp0 hp1 (floor_small lay hl residual hr).1)
  have HB := TBSim.bind H (f:=fun r=>pure r) (W₂:=587) (Q₂:=LowerStagePost im lay index residual hints p forest s) (by
    intro r u hu
    cases r with
    | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=LowerStagePost im lay index residual hints p forest s) hu).mono (by omega) (fun _ _ h=>h)
    | some pair =>
      obtain ⟨c,ds,low⟩ := pair
      rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
      have huf : Frame a u (LowerWrites lay) := uf.mono (fun _ _=>csWrites_lower lay)
      have hstu : Stable index p forest u := hsta.frame (huf.mono (fun _ _=>lowerWrites_subset lay hl)) ur (by decide)
      have hsp := hstu.prepared lay hl
      have uh8 : u.getReg .x8=BitVec.ofNat 64 lay.val := (ur.get (by decide)).trans ha.layer
      have uhrm : u.getMem (0x66008#64)=BitVec.ofNat 64 residual :=
        (uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
          ((ha.frame.get (by decide) (by unfold ENC;omega)).trans hrm)
      have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
      obtain ⟨t,k,ut,hk,ht⟩ := lower_tail htail lay hl (route index lay).1 residual (preparedAt p lay) low ds
        (lower_decode_digits lay hl hdec) u up uh8 (by simpa only [lowerArgs,hcc,Search.DIGITS,DIGITS] using hdigs)
        (fun j hj d hd=>hsp.saved j hj d (by omega)) hsp.path (by unfold stageBound at hr;split_ifs at hr <;> omega) uhrm ucredit
      have htf : Frame u t (LowerWrites lay) := ht.frame.mono (by intro A hA h;unfold LowerWrites;rcases h with h|rfl;tauto;omega)
      have hstt : Stable index p forest t := hstu.frame (htf.mono (fun _ _=>lowerWrites_subset lay hl)) ht.regs (by decide)
      refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
      refine ⟨ht.pc,ht.layer,ht.residual,?_,?_,hstt,ht.values,ht.path,hfloor,?_,?_⟩
      · exact (ht.frame.get (by decide) (by unfold LowerTailWrites SharedRootControl.sigBase;split_ifs <;> omega)).trans
          ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans ha.hints)
      · exact ⟨c.toNat,by omega,(ht.frame.get (by unfold ENC;omega)
          (by unfold LowerTailWrites SharedRootControl.sigBase ENC;split_ifs <;> omega)).trans uc32⟩
      · rw [ht.regs.get (by decide)]
        simpa [lowerArgs,CanonicalPolicy.normalLayer,hl,T3.target] using usum
      · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
  have HC := TBSim.steps sa HB
  simpa only [bind_pure,topArgs,lowerArgs] using HC.mono (by change ca+(Canonical.csCost lay+587)≤Canonical.csCost lay+707;omega) (fun _ _ h=>h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def PiecesStored (lay : Layer) (pieces : T3.Pieces) (s : MachineState) : Prop :=
  DigsAt s (SharedRootControl.sigBase lay.val) pieces.1 ∧
  DigsAt s (SharedRootControl.sigBase lay.val+688) pieces.2

theorem lowerWrites_other_values (old current : Layer) (ho : old≠0) (hc : current≠0)
    (hne : old≠current) (j half : Nat) (hj : j<43) (hh : half<2) :
    ¬LowerWrites current (SharedRootControl.sigBase old.val+16*j+8*half) := by
  intro h
  rcases h with h|h|h|h|h|h
  all_goals fin_cases old <;> fin_cases current <;>
    simp_all [SharedRootControl.sigBase,ENC,EOUT,DIGITS] <;> omega

theorem PiecesStored.frame_lower {s t : MachineState} {old current : Layer} {pieces : T3.Pieces}
    (ho : old≠0) (hc : current≠0) (hne : old≠current)
    (hlen : pieces.1.length=43) (hpath : pieces.2.length=height old)
    (h : PiecesStored old pieces s) (hf : Frame s t (LowerWrites current)) : PiecesStored old pieces t := by
  constructor
  · intro j hj
    have hj' : j<43 := by simpa only [hlen] using hj
    apply (h.1 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · simpa using lowerWrites_other_values old current ho hc hne j 0 hj' (by decide)
    · simpa using lowerWrites_other_values old current ho hc hne j 1 hj' (by decide)
  · intro j hj
    have hj' : j<height old := by simpa only [hpath] using hj
    have hheight : height old≤12 := by fin_cases old <;> decide
    apply (h.2 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw
      exact work_not_path old ho j 0 hj' (by decide) (by simpa using lowerWrites_subset current hc hw)
    · intro hw
      exact work_not_path old ho j 1 hj' (by decide) (by simpa using lowerWrites_subset current hc hw)

theorem PiecesStored.frame_finish {s t : MachineState} {lay : Layer} {pieces : T3.Pieces}
    (hl : lay≠0) (hlen : pieces.1.length=43) (hpath : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) (hf : Frame s t (fun A=>DIGITS≤A ∧ A<DIGITS+56)) : PiecesStored lay pieces t := by
  have hsbase : SharedRootControl.sigBase lay.val+1024<DIGITS := by
    unfold SharedRootControl.sigBase DIGITS;split_ifs <;> omega
  have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
  constructor
  · intro j hj
    have hj' : j<43 := by simpa only [hlen] using hj
    apply (h.1 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw;omega
    · intro hw;omega
  · intro j hj
    have hj' : j<height lay := by simpa only [hpath] using hj
    apply (h.2 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw;omega
    · intro hw;omega

theorem prepared_length (lay : Layer) (hl : lay≠0) (leaf : Nat) (p : PreparedLower) (ds : List Nat) :
    (preparedPieces lay leaf p ds).1.length=43 ∧ (preparedPieces lay leaf p ds).2.length=height lay := by
  have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
  simp [preparedPieces,hcc]

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000

theorem work_not_base {A : Nat} (hb : BaseA A) : ¬WorkWrites A := by
  intro hw
  rcases hw with hw|hw|hw|hw|hw|hw|⟨lay,hlo,hhi,ha,hb'⟩
  all_goals unfold BaseA NeverW at hb
  all_goals simp only [PRIV,REGION,FLEAF,Keygen.NODE,CHAIN,ZDIG,ENC,EOUT,DIGITS,NBUF,TOP_DATA] at *
  all_goals first | omega | skip
  all_goals unfold SharedRootControl.sigBase at *
  all_goals split_ifs at * <;> omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000

theorem stateBase_frame {sk : SecretKey} {cache : Bytes 131072} {s t : MachineState}
    (h : SharedTopPath.StateBase sk cache s) (hf : Frame s t WorkWrites)
    (hx5 : t.getReg .x5=0) : SharedTopPath.StateBase sk cache t := by
  have g : ∀ A,A<2^64→BaseA A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (work_not_base hb)
  refine ⟨hx5,?_,?_,?_,?_,?_,?_,fun k hk=>?_,fun A hA hn h32 h40=>?_⟩
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p0
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p8
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p32
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p40
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p48
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p56
  · exact (g _ (by unfold REGION;omega) (by unfold BaseA;right;right;right;right;right;right;left;omega)).trans (h.region k hk)
  · exact (g _ hA (by unfold BaseA;right;right;right;right;right;right;right;left;exact hn)).trans (h.zero A hA hn h32 h40)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure Choices where
  c0 : BitVec 32
  c1 : BitVec 32
  c2 : BitVec 32
  c3 : BitVec 32
  d0 : List Nat
  d1 : List Nat
  d2 : List Nat
  d3 : List Nat
  l0 : Bool
  l1 : Bool
  l2 : Bool
  l3 : Bool
  extra : Nat

def Choices.r1 (a : Choices) := CanonicalPolicy.nextResidual (69 + a.extra) 0 a.l0 a.d0
def Choices.r2 (a : Choices) := CanonicalPolicy.nextResidual a.r1 1 a.l1 a.d1
def Choices.r3 (a : Choices) := CanonicalPolicy.nextResidual a.r2 2 a.l2 a.d2
def Choices.hints (a : Choices) := 484*CanonicalPolicy.threshold 1 a.r1 +
  22*CanonicalPolicy.threshold 2 a.r2 + CanonicalPolicy.threshold 3 a.r3

def prefixSearch (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (extra : Nat := 0) : T3.M (Option Choices) := do
  let some (c0,d0,l0) ← CanonicalPolicy.layerCounterSearchAt 0 (14 + extra) (route index 0).2 (route index 0).1
    (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0) | pure none
  let r1 := CanonicalPolicy.nextResidual (69 + extra) 0 l0 d0
  let f1 := CanonicalPolicy.threshold 1 r1
  if f1≥16 then return none
  let some (c1,d1,l1) ← CanonicalPolicy.layerCounterSearchAt 1 f1 (route index 1).2 (route index 1).1
    (.pair (topPair 2 p.two.levels).1 (topPair 2 p.two.levels).2) 0 (searchLimit 1) | pure none
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  let f2 := CanonicalPolicy.threshold 2 r2
  if f2≥22 then return none
  let some (c2,d2,l2) ← CanonicalPolicy.layerCounterSearchAt 2 f2 (route index 2).2 (route index 2).1
    (.pair (topPair 3 p.three.levels).1 (topPair 3 p.three.levels).2) 0 (searchLimit 2) | pure none
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  let f3 := CanonicalPolicy.threshold 3 r3
  if f3≥22 then return none
  let some (c3,d3,l3) ← CanonicalPolicy.layerCounterSearchAt 3 f3 (route index 3).2 (route index 3).1
    (.pair forest.1 forest.2) 0 (searchLimit 3) | pure none
  pure (some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3,extra⟩)

structure PrefixReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (a : Choices)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=51
  n4 : t.getReg .x27=51
  target : t.getReg .x17=152
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some a.d0
  digits : ∀ j,j<51 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (a.d0.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 a.hints
  residual : t.getMem (0x66008#64)=0
  credit : CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3=0
  frame : Frame s t WorkWrites

def PrefixPost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option Choices→MachineState→Prop
  | none,t => SearchError im t
  | some a,t => PrefixReady index p forest a s t

def prefixCost : Nat := Canonical.csCost 0+57+((Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)))

theorem prefix_good {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (extra : Nat) (he : extra ≤ 4)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s prefixCost (prefixSearch index p forest extra)
      (PrefixPost im index p forest s) := by
  unfold prefixSearch
  have H0 := top_stage hs htop htail extra he index hi p forest s hp hstable htier hh hc32
  refine (TBSim.bind H0 (W₂:=(Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30))) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=prefixCost) (by unfold prefixCost;omega) (fun _ _ h=>h)
  intro r0 t0 h0
  cases r0 with
  | none => exact (TBSim.pure (a:=none) (s:=t0) (Q:=PrefixPost im index p forest s) h0).mono (by omega) (fun _ _ h=>h)
  | some a0 =>
    obtain ⟨c0,d0,l0⟩ := a0
    change TopReady extra index p forest l0 d0 s t0 at h0
    let r1 := CanonicalPolicy.nextResidual (69 + extra) 0 l0 d0
    let f1 := CanonicalPolicy.threshold 1 r1
    have hf1 : f1<16 := (floor_small 1 (by decide) r1 h0.small).2 rfl
    dsimp only [f1,r1] at hf1
    simp only [if_neg (Nat.not_le.mpr hf1)]
    have H1 := lower_stage hs hlower hltail 1 (by decide) index r1 0 hi h0.small p forest t0
      h0.pc h0.layer h0.stable h0.residual h0.hints h0.c32
    refine (TBSim.bind H1 (W₂:=(Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30))) (by omega) (fun _ _ h=>h)
    intro r1out t1 h1
    cases r1out with
    | none => exact (TBSim.pure (a:=none) (s:=t1) (Q:=PrefixPost im index p forest s) h1).mono (by omega) (fun _ _ h=>h)
    | some a1 =>
      obtain ⟨c1,d1,l1⟩ := a1
      change LowerReady 1 index r1 0 p forest l1 d1 t0 t1 at h1
      let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
      let f2 := CanonicalPolicy.threshold 2 r2
      have hr2 : r2<41 := (next_stage_bound 1 (by decide) r1 h0.small l1 d1 h1.floor).1 (by decide)
      have hf2 : f2<22 := (floor_small 2 (by decide) r2 hr2).1
      have hints1 : t1.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1) := by simpa [SharedHints.hintWeight] using h1.hints
      have saved1 : SavedTop d0 t1 := h0.saved.frame h1.frame (lowerWrites_saved 1)
      dsimp only [f2,r2,r1] at hf2
      simp only [if_neg (Nat.not_le.mpr hf2)]
      have H2 := lower_stage hs hlower hltail 2 (by decide) index r2 (484*f1) hi hr2 p forest t1
        h1.pc h1.layer h1.stable h1.residualMem hints1 h1.c32
      refine (TBSim.bind H2 (W₂:=(Canonical.csCost 3+707)+30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)) (by omega) (fun _ _ h=>h)
      intro r2out t2 h2
      cases r2out with
      | none => exact (TBSim.pure (a:=none) (s:=t2) (Q:=PrefixPost im index p forest s) h2).mono (by omega) (fun _ _ h=>h)
      | some a2 =>
        obtain ⟨c2,d2,l2⟩ := a2
        change LowerReady 2 index r2 (484*f1) p forest l2 d2 t1 t2 at h2
        let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
        let f3 := CanonicalPolicy.threshold 3 r3
        have hr3 : r3<22 := (next_stage_bound 2 (by decide) r2 hr2 l2 d2 h2.floor).1 (by decide)
        have hf3 : f3<22 := (floor_small 3 (by decide) r3 hr3).1
        have hints2 : t2.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1+22*f2) := by simpa [SharedHints.hintWeight] using h2.hints
        have saved2 : SavedTop d0 t2 := saved1.frame h2.frame (lowerWrites_saved 2)
        have one1 : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one d1) t1 := ⟨h1.values,h1.path⟩
        have one2 := one1.frame_lower (current:=2) (by decide) (by decide) (by decide)
          (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h2.frame
        dsimp only [f3,r3,r2,r1] at hf3
        simp only [if_neg (Nat.not_le.mpr hf3)]
        have H3 := lower_stage hs hlower hltail 3 (by decide) index r3 (484*f1+22*f2) hi hr3 p forest t2
          h2.pc h2.layer h2.stable h2.residualMem hints2 h2.c32
        refine (TBSim.bind H3 (W₂:=30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 3+707)+30) (by omega) (fun _ _ h=>h)
        intro r3out t3 h3
        cases r3out with
        | none => exact (TBSim.pure (a:=none) (s:=t3) (Q:=PrefixPost im index p forest s) h3).mono (by omega) (fun _ _ h=>h)
        | some a3 =>
          obtain ⟨c3,d3,l3⟩ := a3
          change LowerReady 3 index r3 (484*f1+22*f2) p forest l3 d3 t2 t3 at h3
          have hz : CanonicalPolicy.nextResidual r3 3 l3 d3=0 :=
            (next_stage_bound 3 (by decide) r3 hr3 l3 d3 h3.floor).2 rfl
          have saved3 : SavedTop d0 t3 := saved2.frame h3.frame (lowerWrites_saved 3)
          have one3 := one2.frame_lower (current:=3) (by decide) (by decide) (by decide)
            (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h3.frame
          have two2 : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two d2) t2 := ⟨h2.values,h2.path⟩
          have two3 := two2.frame_lower (current:=3) (by decide) (by decide) (by decide)
            (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 h3.frame
          have three3 : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three d3) t3 := ⟨h3.values,h3.path⟩
          obtain ⟨t,st,ht⟩ := finish_steps hfinish index hi p forest d0 t3 h3.pc h3.stable saved3 h3.sum
          refine (TBSim.steps st (TBSim.pure (s:=t)
            (a:=some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3,extra⟩)
            (Q:=PrefixPost im index p forest s) ?_)).mono (W':=30) (by omega) (fun _ _ h=>h)
          refine ⟨ht.pc,ht.layer,ht.tree,ht.height,ht.chains,ht.n4,ht.target,ht.leaf,ht.selected,ht.stable,
            h0.decoded,ht.digits,ht.sum,?_,?_,?_,?_,?_,hz,?_⟩
          · exact one3.frame_finish (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 ht.frame
          · exact two3.frame_finish (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 ht.frame
          · exact three3.frame_finish (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 ht.frame
          · have hm := (ht.frame.get (A:=0x66000) (by decide) (by unfold DIGITS;omega)).trans h3.hints
            change t.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1+22*f2+f3)
            simpa [SharedHints.hintWeight] using hm
          · have hm := (ht.frame.get (A:=0x66008) (by decide) (by unfold DIGITS;omega)).trans h3.residualMem
            change t.getMem (0x66008#64)=BitVec.ofNat 64 0
            simpa only [hz] using hm
          · have F1 := h1.frame.mono (fun _ _=>lowerWrites_subset 1 (by decide))
            have F2 := h2.frame.mono (fun _ _=>lowerWrites_subset 2 (by decide))
            have F3 := h3.frame.mono (fun _ _=>lowerWrites_subset 3 (by decide))
            have F4 : Frame t3 t WorkWrites := ht.frame.mono (by intro A hA h;unfold WorkWrites;omega)
            exact ((((h0.frame.trans F1).trans F2).trans F3).trans F4).mono (by
              intro A hA h;rcases h with (((h|h)|h)|h)|h <;> exact h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open OracleComp
set_option maxHeartbeats 500000
set_option maxRecDepth 32768

def finishSource (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots)
    (a : Choices) : M (Option CanonicalLayers) := do
  let top ← signTop cache (route index 0).1 a.d0
  pure (some ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3,
    BitVec.ofNat 16 a.hints⟩)

theorem searchPreparedLayers_prefix (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots)
    (forest : Digest×Digest) (extra : Nat := 0) :
    searchPreparedLayers cache index p forest (69 + extra) (14 + extra) =
      prefixSearch index p forest extra >>= fun
        | none => pure none
        | some a => finishSource cache index p a := by
  unfold searchPreparedLayers prefixSearch
  simp only [CanonicalPolicy.totalCredit,CanonicalPolicy.topFloor,CanonicalPolicy.threshold_top]
  simp only [bind_assoc]
  congr 1
  funext o0
  cases o0 with
  | none => simp only [pure_bind]
  | some o0 =>
    obtain ⟨c0,d0,l0⟩ := o0
    dsimp only
    split
    · simp_all only [pure_bind, ite_true, ite_false]
    · simp_all only [bind_assoc, ite_true, ite_false]
      congr 1
      funext o1
      cases o1 with
      | none => simp only [pure_bind]
      | some o1 =>
        obtain ⟨c1,d1,l1⟩ := o1
        dsimp only
        split
        · simp_all only [pure_bind, ite_true, ite_false]
        · simp_all only [bind_assoc, ite_true, ite_false]
          congr 1
          funext o2
          cases o2 with
          | none => simp only [pure_bind]
          | some o2 =>
            obtain ⟨c2,d2,l2⟩ := o2
            dsimp only
            split
            · simp_all only [pure_bind, ite_true, ite_false]
            · simp_all only [bind_assoc, ite_true, ite_false]
              congr 1
              funext o3
              cases o3 with
              | none => simp only [pure_bind]
              | some o3 =>
                obtain ⟨c3,d3,l3⟩ := o3
                simp only [pure_bind,finishSource,Choices.r1,Choices.r2,Choices.r3,Choices.hints]

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open Packed.Boundary
open Packed (L0W)
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def TopFinishPost (s : MachineState) (top : T3.Pieces) (t : MachineState) : Prop :=
  t.pc=pcOf 540 ∧ (∀ i<51,DigAt t (SIG+2240+16*i) (top.1.getD i 0)) ∧
    (∀ j<12,DigAt t (SIG+3056+16*j) (top.2.getD j 0)) ∧ Frame s t L0W ∧
    t.getMem (0x66000#64)=s.getMem (0x66000#64) ∧
    t.getMem (0x66008#64)=s.getMem (0x66008#64)

structure TopCalls (im : Image) (sk : SecretKey) (cache : Bytes 131072) : Prop where
  call : ∀ (leaf : Nat),leaf<4096 → ∀ (ds : List Nat) (u : MachineState),u.pc=pcOf 441 →
    SharedTopPath.StateBase sk cache u → TopRegs leaf u →
    u.getReg .x18=BitVec.ofNat 64 leaf → (u.getReg .x25).toNat≤201 →
    (∀ i<51,ds.getD i 0≤T3.maxDigit 0 i) →
    (∀ i<51,u.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 (ds.getD i 0)) →
    TBSim im sk u 335006 (T3.signTop (cacheDec cache) leaf ds) (TopFinishPost u)

theorem PiecesStored.frame_top {s t : MachineState} {lay : Layer} {pieces : T3.Pieces}
    (hl : lay≠0) (hlen : pieces.1.length=43) (hpath : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) (hf : Frame s t L0W) : PiecesStored lay pieces t := by
  constructor
  · intro i hi
    have hi' : i<43 := by simpa only [hlen] using hi
    apply (h.1 i hi).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG] <;> omega
  · intro j hj
    have hj' : j<height lay := by simpa only [hpath] using hj
    apply (h.2 j hj).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG,height] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG,height] <;> omega

def layersValue (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces) : CanonicalLayers :=
  ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3,
    BitVec.ofNat 16 a.hints⟩

structure Completed (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf 540
  topValues : ∀ i<51,DigAt t (SIG+2240+16*i) (top.1.getD i 0)
  topPath : ∀ j<12,DigAt t (SIG+3056+16*j) (top.2.getD j 0)
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 a.hints
  residual : t.getMem (0x66008#64)=0
  credit : CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3=0

def LayersPost (im : Image) (index : Nat) (p : PreparedRoots) : Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => ∃ a top,layers=layersValue index p a top ∧ Completed index p a top t


end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem installed_searchCalls (sk : BitVec 256) : SearchCalls Images.signImage sk :=
  ⟨fun _ _ hp => Canonical.counterSearch_good SharedSearchCode.installed_searchKernel hp⟩

theorem installed_topSetup : TopSetupSteps Images.signImage :=
  ⟨SharedTopSetup.steps SharedTopSetup.installed_code⟩

theorem installed_topTail : TopTailSteps Images.signImage :=
  ⟨SharedTopDigits.save_steps SharedTopDigits.installed_save,
   SharedControlTail.initResidual_steps SharedControlTail.installed_initResidual,
   SharedResidual.residual22230_steps SharedResidual.installed22230,
   SharedControlTail.firstLayer_steps SharedControlTail.installed_firstLayer⟩

theorem installed_lowerSetup : LowerSetupSteps Images.signImage :=
  ⟨SharedLowerSetup.call_steps SharedFloor.installed_dispatch SharedHints.installed_code SharedLowerRegisters.installed_code⟩

theorem installed_lowerTail : LowerTailSteps Images.signImage :=
  ⟨SharedReveal.prepared_steps SharedReveal.installed_stepCode SharedReveal.installed_byteCode SharedReveal.installed_setupCode,
   SharedResidual.residual22448_steps SharedResidual.installed22448,
   SharedControlTail.nextLayer_steps SharedControlTail.installed_nextLayer⟩

theorem installed_finish : FinishSteps Images.signImage :=
  ⟨SharedTopDigits.restore_steps SharedTopDigits.installed_restore,
   SharedControlTail.topProduce_steps SharedControlTail.installed_topProduce⟩

theorem installed_prefix_good {sk : BitVec 256}
    (extra : Nat) (he : extra ≤ 4)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s prefixCost (prefixSearch index p forest extra)
      (PrefixPost Images.signImage index p forest s) :=
  prefix_good (installed_searchCalls sk) installed_topSetup installed_topTail installed_lowerSetup
    installed_lowerTail installed_finish extra he index hi p forest s hp hstable htier hh hc32

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem installed_topCalls (sk : SecretKey) (cache : Bytes 131072) :
    TopCalls Images.signImage sk cache := by
  constructor
  intro leaf hl ds u up hb hr h18 h25 hd ud
  have H := SharedTopContinuation.top_only SharedTopBlocks.installed_code
    ClaudeWCT.W9.Machine.Sign.SharedTopLeafP.installed_continuation_leaf leaf hl ds u up hb hr h18 h25 hd ud
  exact H.mono (le_refl _) (by
    intro top t ht
    rcases ht with ⟨tp,tv,ta,tf,tm⟩
    exact ⟨tp,tv,ta,tf,tm _ (Or.inl rfl),tm _ (Or.inr rfl)⟩)


end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

-- Campaign T51 (as R6, D6): the dead `searchPreparedLayers_good` / `installed_searchPreparedLayers_good` /
-- `from_built_good` were removed (the live route is `searchPreparedLayers_framed`).
theorem base_stateBase {sk : SecretKey} {cache : Bytes 131072} {s : MachineState} {flag : Nat}
    (h : Base (cfFlag:=flag) sk cache s) : SharedTopPath.StateBase sk cache s :=
  ⟨h.x5,h.p0,h.p8,h.p32,h.p40,h.p48,h.p56,h.region,fun A hA hn _ _ => h.zero A hA hn⟩

theorem base_tables {sk : SecretKey} {cache : Bytes 131072} {s : MachineState}
    (h : Base (cfFlag:=0) sk cache s) : Tables s :=
  ⟨h.x5,h.zero _ (by decide) (by unfold NeverW;tauto),h.table,h.cf,h.reward,h.zt,h.t51⟩

theorem built_stable {sk : SecretKey} {cache : Bytes 131072} {index : Nat} {forest : Digest×Digest}
    {s t : MachineState} {p : PreparedRoots}
    (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t) : Stable index p forest t :=
  ⟨base_tables h.base,h.indexMem,h.one,h.two,h.three,h.forestL,h.forestR⟩


end SigGolfCandidate.T3M.Sign.SharedSearches

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def innerCode (c : Nat) : List (BitVec 32) := ((coordCodesW.getD c []).drop 1).take (lI c-cbase c-1)
theorem inner_bounds (c : Fin 9) : cbase c.val+1≤lI c.val ∧ lI c.val-cbase c.val≤(coordCodesW.getD c.val []).length ∧ cbase c.val<2^20 := by
  fin_cases c <;> decide +kernel

theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

theorem fetch_of_code {im : Image}
    (hh : CodeAt im (pcOf 11003) headCode)
    (hi : ∀c : Fin 9,CodeAt im (pcOf (cbase c.val+1)) (innerCode c.val))
    (ha : CodeAt im (pcOf 1700) arenaCode) (hs : CodeAt im (pcOf 21200) ftsStub) : Fetch im := by
  constructor
  · intro n w hw
    unfold headLook at hw
    split at hw
    · rename_i hle
      have he:=codeAt_get_word (by decide : 11003<2^30) hh hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
  · intro c hc n w hw
    have hb:=inner_bounds ⟨c,hc⟩
    dsimp only at hb
    unfold coordLook at hw
    split at hw
    · rename_i hn
      unfold coordLookW at hw
      have hw' : (innerCode c)[n-(cbase c+1)]?=some w := by
        unfold innerCode
        rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop]
        rwa [show 1+(n-(cbase c+1))=n-cbase c by omega]
      have hf:=codeAt_get_word (by omega : cbase c+1<2^30) (hi ⟨c,hc⟩) hw'
      simpa [show cbase c+1+(n-(cbase c+1))=n by omega] using hf
    · split at hw
      · rename_i hn2
        have he := codeAt_get_word (by decide : 21200 < 2^30) hs hw
        simpa [show 21200 + (n - 21200) = n by omega] using he
      · unfold arenaLook at hw
        split at hw
        · rename_i hle
          have he := codeAt_get_word (by decide : 1700 < 2^30) ha hw
          simpa [Nat.add_sub_cancel' hle] using he
        · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedReuse


namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_fetch : Fetch Images.signImage := by
  apply fetch_of_code
  · sign_slice_fast
  · intro c
    fin_cases c <;> sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_c4Stub : CodeAt Images.signImage (pcOf c4StubPc) c4Stub := by
  sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hstub
      have he := SharedReuse.codeAt_get_word (by decide : c4StubPc < 2^30) installed_c4Stub hw
      simpa [Nat.add_sub_cancel' hstub.2] using he
    · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_c4Stub : CodeAt Images.signImage (pcOf c4StubPc) c4Stub := by
  sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hstub
      have he := SharedReuse.codeAt_get_word (by decide : c4StubPc < 2^30) installed_c4Stub hw
      simpa [Nat.add_sub_cancel' hstub.2] using he
    · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
/-- C1: the stub words in the former nop gaps of `signCode_85`. -/
theorem installed_stub (c : Fin 9) : CodeAt Images.signImage (pcOf (stubPc c.val)) (stubWords c.val) := by
  fin_cases c <;> apply codeAt_sign_last <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hle
      have hb : stubPc c<2^30 := by
        have h : ∀ c : Fin 9,stubPc c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he := SharedReuse.codeAt_get_word hb (installed_stub ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
/-- C1: the stub words in the former nop gaps of `signCode_85`. -/
theorem installed_stub (c : Fin 9) : CodeAt Images.signImage (pcOf (stubPc c.val)) (stubWords c.val) := by
  fin_cases c <;> apply codeAt_sign_last <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hle
      have hb : stubPc c<2^30 := by
        have h : ∀ c : Fin 9,stubPc c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he := SharedReuse.codeAt_get_word hb (installed_stub ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_hookCode (c : Fin 9) : CodeAt Images.signImage (pcOf (lI c.val)) [hookWords.getD c.val 0] := by
  fin_cases c <;> sign_slice_fast
theorem installed_hookLook (c : Nat) (hc : c<9) : LookOK Images.signImage (hookLook c) := by
  intro n w hw
  unfold hookLook at hw
  split at hw
  · rename_i he
    have hh : hookWords.getD c 0=w := Option.some.inj hw
    have hb : lI c<2^30 := by
      have h : ∀ c : Fin 9,lI c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have hx := SharedReuse.codeAt_get_word (i:=0) hb (installed_hookCode ⟨c,hc⟩) (by simpa [hh])
    simpa [he] using hx
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (basePc c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : basePc c<2^30 := by
      have h : ∀ c : Fin 9,basePc c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_hookCode (c : Fin 9) : CodeAt Images.signImage (pcOf (cbase c.val)) [hookWord c.val] := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i he
    have hh : hookWord c=w := Option.some.inj hw
    have hb : cbase c<2^30 := by
      have h : ∀ c : Fin 9,cbase c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have hx:=SharedReuse.codeAt_get_word (i:=0) (w:=w) hb (installed_hookCode ⟨c,hc⟩) (by simpa [hh])
    simpa [he] using hx
  · split at hw
    · rename_i hle
      have hb : entry c<2^30 := by
        have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he:=SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open SigGolfCandidate.T3M
theorem installed_Code (c : Nat) (hc : c<9) : Code Images.signImage c :=
  ⟨SharedField.installed_look c hc, SharedLeaf.installed_look c hc,
   SharedLeaf.installed_hookLook c hc, SharedNext.installed_look c hc,
   SharedNode.installed_look c hc, SharedTail.installed_look c hc,
   SharedFinish.installed_look c hc, SharedPath.installed_look c hc,
   SharedEnd.installed_look c hc⟩
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_forTail : CodeAt Images.signImage (pcOf 20715) (tailCode.take 28) := by
  sign_slice_fast

theorem installed_forTramp : CodeAt Images.signImage (pcOf 21450) signTramp := by
  sign_slice_fast
theorem installed_forLook : LookOK Images.signImage forLook := by
  intro n w hw
  unfold forLook at hw
  split at hw
  · rename_i hn
    have he:(tailCode.take 28)[n-20715]?=some w := by
      rw [List.getElem?_take,if_pos (by omega)];exact hw
    have hh:=SharedReuse.codeAt_get_word (by decide:20715<2^30) installed_forTail he
    simpa only[Nat.add_sub_cancel' hn.1]using hh
  · unfold trampLook at hw
    split at hw
    · rename_i hn
      have hh:=SharedReuse.codeAt_get_word (by decide:21450<2^30) installed_forTramp hw
      simpa only[Nat.add_sub_cancel' hn]using hh
    · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedBoundary

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_sign_code : CodeAt Images.signImage (pcOf (base false)) (words false) := by
  sign_slice_fast
theorem installed_sign_look : LookOK Images.signImage (look false) := look_of_code false installed_sign_code
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_sign_success : CodeAt Images.signImage (pcOf 22754) signCode := by
  sign_slice_fast
theorem installed_sign_tier : CodeAt Images.signImage (pcOf 24723) signTierCode := by
  sign_slice_fast
theorem installed_sign_failure_jump : CodeAt Images.signImage (pcOf 22764) [0xcccea06f] := by
  sign_slice_fast
theorem installed_sign_failure : CodeAt Images.signImage (failPC false) failureCode := by
  sign_slice_fast
theorem installed_sign_failure_ecall : CodeAt Images.signImage (pcOf 545) [0x73] := by
  sign_slice_fast
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open Packed.Boundary
open Packed (L0W)
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def FramedLayersPost (im : Image) (index : Nat) (p : PreparedRoots) (s : MachineState) :
    Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => LayersPost im index p (some layers) t ∧ Frame s t (fun A=>WorkWrites A ∨ L0W A)

theorem searchPreparedLayers_framed {im : Image} {sk : SecretKey} {cache : Bytes 131072}
    (hc : TopCalls im sk cache) (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (extra : Nat) (he : extra ≤ 4)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (prefixCost+335006)
      (searchPreparedLayers (cacheDec cache) index p forest (69 + extra) (14 + extra))
      (FramedLayersPost im index p s) := by
  rw [searchPreparedLayers_prefix (extra := extra)]
  refine TBSim.bind (prefix_good hs htop htail hlower hltail hfinish
    extra he index hi p forest s hp hstable htier hh hc32)
    (W₂:=335006) (Q₂:=FramedLayersPost im index p s) ?_
  intro a u hu
  cases a with
  | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=FramedLayersPost im index p s) hu).mono (by omega) (fun _ _ h=>h)
  | some a =>
    change PrefixReady index p forest a s u at hu
    have hb := stateBase_frame hbase hu.frame hu.stable.tables.x5
    have hleaf : index/2^19<4096 := by omega
    have hregs : TopRegs (index/2^19) u :=
      ⟨hu.layer,hu.tree,hu.selected.trans hu.leaf,hu.chains,hu.n4⟩
    have hd7 : ∀ i<51,a.d0.getD i 0≤T3.maxDigit 0 i := by
      obtain ⟨v,hv⟩ := hu.decoded
      change T3.decode 0 v=some a.d0 at hv
      intro i hi
      exact T3.decode_digit_max hv i hi
    have H := hc.call (index/2^19) hleaf a.d0 u hu.pc hb hregs hu.leaf hu.sum hd7 hu.digits
    unfold finishSource
    have hr : (route index 0).1=index/2^19 := by
      change index/2^19%2^12=index/2^19
      exact Nat.mod_eq_of_lt hleaf
    rw [hr]
    refine (TBSim.bind H (W₂:=0) (Q₂:=FramedLayersPost im index p s) ?_).mono (by omega) (fun _ _ h=>h)
    intro top t ht
    rcases ht with ⟨htpc,htv,htp,htf,hth,htr⟩
    refine TBSim.pure (a:=some (layersValue index p a top)) (s:=t) (Q:=FramedLayersPost im index p s) ?_
    refine ⟨⟨a,top,rfl,htpc,htv,htp,?_,?_,?_,hth.trans hu.hints,htr.trans hu.residual,hu.credit⟩,hu.frame.trans htf⟩
    · exact hu.one.frame_top (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 htf
    · exact hu.two.frame_top (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 htf
    · exact hu.three.frame_top (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 htf

end SigGolfCandidate.T3M.Sign.SharedSearches
namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def LowFrame (s t : MachineState) : Prop := Frame s t (fun A => ¬(SIG≤A ∧ A<SIG+2192))

theorem LowFrame.trans {s t u : MachineState} (h : LowFrame s t) (h' : LowFrame t u) : LowFrame s u :=
  (Frame.trans h h').mono (by intro A hA h;exact h.elim id id)

theorem OnePost.lowFrame {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) : LowFrame s t := by
  apply h.frame.mono
  intro A hA hw hsig
  unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr at hw
  fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT,SIG] <;> omega

theorem prepareRoots_framed {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=1) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (3*(btCost+47)) (prepareRoots index) (fun p t => RootsPost (cfFlag := cfFlag) sk cache index s p t ∧ LowFrame s t) := by
  have r1 := one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    (lay := 1) (by decide) hi s hpc h8 hidx hb hz
  unfold prepareRoots
  refine TBSim.mono (TBSim.bind r1 (fun p1 t1 h1 =>
    TBSim.bind (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
      (lay := 2) (by decide) hi t1 (by simpa using h1.pc) h1.layer h1.indexMem h1.base h1.zero)
      (fun p2 t2 h2 => TBSim.bind
        (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
          (lay := 3) (by decide) hi t2 (by simpa using h2.pc) h2.layer h2.indexMem h2.base h2.zero)
        (fun p3 t3 h3 => TBSim.pure ?_)))) (by omega) (fun _ _ h => h)
  refine ⟨?_, ((h1.lowFrame (by decide)).trans (h2.lowFrame (by decide))).trans (h3.lowFrame (by decide))⟩
  refine ⟨by simpa using h3.pc,by simpa using h3.layer,h3.base,h3.indexMem,?_,?_,h3.stored,?_,?_,?_⟩
  · exact (h1.stored.after (by decide) (by decide) (by decide) h2).after
      (by decide) (by decide) (by decide) h3
  · exact h2.stored.after (by decide) (by decide) (by decide) h3
  · exact (((h1.rootsFrame (by decide)).trans (h2.rootsFrame (by decide))).trans
      (h3.rootsFrame (by decide))).mono (by intro A hA h; rcases h with (h|h)|h <;> exact h)
  · exact (h3.counterMem (by decide)).trans ((h2.counterMem (by decide)).trans (h1.counterMem (by decide)))
  · intro extra htier
    exact h3.tierPreserved (by decide)
      (h2.tierPreserved (by decide) (h1.tierPreserved (by decide) htier))

theorem entry_roots_framed {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat} (hi : index<2^31)
    (forest : Digest×Digest) (s : MachineState) (hpc : s.pc=pcOf 22100)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hl : DigAt s ENC forest.1) (hr : DigAt s (ENC+48) forest.2) :
    TBSim im sk s (28+3*(btCost+47)) (prepareRoots index) (fun p t => BuiltPost (cfFlag := cfFlag) sk cache index forest s p t ∧ LowFrame s t) := by
  obtain ⟨a,sa,ap,a8,al,ar,az,ad,ars,af⟩ := entry_steps he s hpc forest.1 forest.2 hl hr
  have af' : Frame s a EntryWrites := af.mono (by unfold EntryWrites; intros A hA h; exact h)
  have abase : Base (cfFlag := cfFlag) sk cache a := hb.frame af' ars (by decide) (by
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold EntryWrites at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA,DIGITS] at hbase hw
    omega)
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (af'.get (A := 0x20550) (by decide) (by unfold EntryWrites DIGITS; omega)).trans hidx
  refine (TBSim.steps sa (prepareRoots_framed hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    hi a ap a8 aidx abase ad)).mono (le_refl _) ?_
  intro p t hpair
  rcases hpair with ⟨ht,hlo⟩
  refine ⟨?_, ?_⟩
  · refine ⟨ht.pc,ht.layer,ht.base,ht.indexMem,ht.one,ht.two,ht.three,?_,?_,?_,af'.trans ht.frame,?_,?_⟩
    · exact (ht.frame.get (A := 0x66000) (by decide) (by unfold RootsWrites; decide)).trans az
    · exact al.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
    · exact ar.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
    · exact ht.counterMem.trans (af'.get (A := ENC+32) (by unfold ENC; decide) (by unfold EntryWrites ENC DIGITS; decide))
    · intro extra htier
      apply ht.tier extra
      exact htier.frame af'
        (by unfold EntryWrites EOUT DIGITS; omega)
        (by unfold EntryWrites EOUT DIGITS; omega)
        (by unfold EntryWrites EOUT DIGITS; omega)
  · exact (show LowFrame s a from af'.mono (by unfold EntryWrites SIG DIGITS; intros A hA hw hsig; omega)).trans hlo

end SigGolfCandidate.T3M.Sign.SharedRootControl
namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
theorem installed_searchPreparedLayers_framed {sk : SecretKey} {cache : Bytes 131072}
    (extra : Nat) (he : extra ≤ 4)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s (prefixCost+335006)
      (searchPreparedLayers (cacheDec cache) index p forest (69 + extra) (14 + extra))
      (FramedLayersPost Images.signImage index p s) :=
  searchPreparedLayers_framed (installed_topCalls sk cache) (installed_searchCalls sk)
    installed_topSetup installed_topTail installed_lowerSetup installed_lowerTail installed_finish
    extra he index hi p forest s hp hstable htier hbase hh hc32


theorem from_built_framed {sk : SecretKey} {cache : Bytes 131072}
    (extra : Nat) (he : extra ≤ 4)
    {index : Nat} (hi : index<2^31) {p : PreparedRoots} {forest : Digest×Digest}
    {s t : MachineState} (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra t)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk t (prefixCost+335006)
      (searchPreparedLayers (cacheDec cache) index p forest (69 + extra) (14 + extra))
      (FramedLayersPost Images.signImage index p t) := by
  apply installed_searchPreparedLayers_framed extra he index hi p forest t h.pc
    (built_stable h) htier (base_stateBase h.base) h.hintZero
  obtain ⟨c,hc,hv⟩ := hc32
  exact ⟨c,hc,h.counterMem.trans hv⟩

end SigGolfCandidate.T3M.Sign.SharedSearches
namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open Packed.Boundary
open Packed (L0W)

theorem layers_lowFrame {s t : MachineState} (h : Frame s t (fun A=>WorkWrites A ∨ L0W A)) :
    Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)) := by
  apply h.mono
  intro A hA hw hlo
  rcases hw with hw|hw
  · rcases hw with hw|hw|hw|hw|hw|hw|⟨lay,hl,hu,ha,hb⟩
    all_goals first | (simp only [ENC,EOUT,DIGITS,SIG] at *;omega) | skip
    unfold SharedRootControl.sigBase at ha hb
    simp only [SIG] at hlo
    split_ifs at ha hb <;>omega
  · exact hw.1 hlo

end SigGolfCandidate.T3M.Sign.SharedSearches
end
-- ==== merged from ClaudeWCT_W9_New_Machine_ExpandLink_SignLink ====
section

namespace ClaudeWCT.W9.Machine.SignLink
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open ClaudeWCT.W9.Machine.Sign (TableAt CostAt TBL COST tblBytes costBytes HookPre)
set_option maxRecDepth 100000
theorem signPrefixData_split : Images.signPrefixData = costBytes ++ tblBytes := by
  unfold Images.signPrefixData ClaudeWCT.W9.Machine.Sign.costBytes ClaudeWCT.W9.Machine.Sign.tblBytes
  rw [← List.flatten_append]
  rfl
theorem signData_split : Images.signData = Images.signZtData ++ (costBytes ++ (tblBytes ++ Images.signLegacyData)) := by
  rw [Images.signData, signPrefixData_split, List.append_assoc]
theorem signData_split2 : Images.signData = (Images.signZtData ++ costBytes) ++ (tblBytes ++ Images.signLegacyData) := by
  rw [signData_split, List.append_assoc]
theorem slice_mid {α : Type} (l1 l2 l3 : List α) (n : Nat) (h : n + 8 ≤ l2.length) :
    ((l1 ++ (l2 ++ l3)).drop (l1.length + n)).take 8 = (l2.drop n).take 8 := by
  rw [List.drop_append, List.drop_eq_nil_of_le (show l1.length ≤ l1.length + n by omega), List.nil_append,
    Nat.add_sub_cancel_left, List.drop_append_of_le_length (show n ≤ l2.length by omega),
    List.take_append_of_le_length (show 8 ≤ (l2.drop n).length by rw [List.length_drop]; omega)]
theorem slice_head {α : Type} (l1 l2 : List α) (n : Nat) (h : n + 8 ≤ l1.length) :
    ((l1 ++ l2).drop n).take 8 = (l1.drop n).take 8 := by
  rw [List.drop_append_of_le_length (show n ≤ l1.length by omega),
    List.take_append_of_le_length (show 8 ≤ (l1.drop n).length by rw [List.length_drop]; omega)]
theorem sinit_wct_cost (sk : SecretKey) (cache : Bytes 131072) (m : Message) : CostAt (sinit sk cache m) := by
  intro k hk
  have hc := ClaudeWCT.W9.Machine.Sign.SearchM.costBytes_length
  rw [sinit_getMem _ _ _ _ (by unfold COST; omega), if_neg (by unfold COST; omega), if_neg (by unfold COST; omega),
    if_neg (by unfold COST; omega), sdata_getMem _ (by unfold COST; omega),
    if_pos (by unfold COST SIGN_DATA; omega), show COST + 8 * k - SIGN_DATA = Images.signZtData.length + 8 * k by
      rw [SigGolfCandidate.T3M.Search.signZtData_length]; unfold COST SIGN_DATA; omega,
    signData_split, slice_mid _ _ _ _ (by omega)]
theorem sinit_wct_table (sk : SecretKey) (cache : Bytes 131072) (m : Message) : TableAt (sinit sk cache m) := by
  intro k hk
  have hc := ClaudeWCT.W9.Machine.Sign.SearchM.costBytes_length
  have ht := ClaudeWCT.W9.Machine.Sign.tblBytes_length
  rw [sinit_getMem _ _ _ _ (by unfold TBL; omega), if_neg (by unfold TBL; omega), if_neg (by unfold TBL; omega),
    if_neg (by unfold TBL; omega), sdata_getMem _ (by unfold TBL; omega),
    if_pos (by unfold TBL SIGN_DATA; omega), show TBL + 8 * k - SIGN_DATA = (Images.signZtData ++ costBytes).length + 8 * k by
      rw [List.length_append, hc, SigGolfCandidate.T3M.Search.signZtData_length]; unfold TBL SIGN_DATA; omega,
    signData_split2, slice_mid _ _ _ _ (by omega)]
theorem hook_v7 {sk : SecretKey} {cache : Bytes 131072} {m : Message} {rho : SigGolfCandidate.T3.Digest}
    {t : MachineState} (h : NoncePost sk cache m rho t) : HookPre sk m rho t := by
  refine ⟨⟨h.search.pc, h.search.x5, h.search.x19, h.search.rho, h.search.msg, ?_⟩, h.rho, ?_, ?_, ?_⟩
  · intro k hk
    rw [h.frame.get (by unfold COST; omega) (by unfold FrontW COST; sg_omega)]
    exact sinit_wct_cost sk cache m k hk
  · intro k hk
    change t.getMem (BitVec.ofNat 64 (0x80 + 8 * k)) = _
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_sk sk cache m k hk
  · intro A hA
    simp only [ClaudeWCT.W9.Machine.Sign.ScrZero, ClaudeWCT.W9.Machine.Sign.PRIVW, ClaudeWCT.W9.Machine.Sign.CHAINW,
      ClaudeWCT.W9.Machine.Sign.NODEW] at hA
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold SIGN_DATA; omega) (by sg_omega)
  · intro k hk
    rw [h.frame.get (by unfold TBL; omega) (by unfold FrontW TBL; sg_omega)]
    exact sinit_wct_table sk cache m k hk
end ClaudeWCT.W9.Machine.SignLink

namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))
def preTailLook (n : Nat) := if n<20743 then tailLook n else none
def preHookLook (n : Nat) := if n=540 then hookLook n else none
def preCLook (n : Nat) := if n<20743 ∨ 20813≤n ∧ n<20832 then cLook n else none
def cHook : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 20730, false, 1, 1, [], none⟩
def cLoopRegs : RegFile :=
  (((RegFile.init.set .x6 (.ld (.reg .x28))).set .x7 (.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8))))).set .x28
    (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16)))).set .x29 (.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16)))
def cLoopMem : SymMem :=
  [(⟨some (.reg .x29), BitVec.ofNat 64 8⟩, .ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))), (⟨some (.reg .x29), BitVec.ofNat 64 0⟩, .ld (.reg .x28))]
def cLoopObl : List Oblig :=
  [.valid ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ 8, .valid ⟨some (.reg .x28), BitVec.ofNat 64 8⟩ 8,
    .valid ⟨some (.reg .x28), BitVec.ofNat 64 0⟩ 8]
def cBr (d : Bool) : Br := ⟨.ltu, .bin .add (.reg .x28) (.c (BitVec.ofNat 64 16)), .reg .x30, d⟩
def cBack : PRes := ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20736, false, 7, 7, [cBr true], none⟩
def cExit : PRes :=
  ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20743, false, 7, 7, [cBr false], none⟩
theorem run_cHook : run preHookLook [20730] 540 [] = some cHook := optBeq_eq (by decide +kernel)
theorem run_cBack : run preTailLook [20736] 20736 [.br true] = some cBack := optBeq_eq (by decide +kernel)
theorem run_cExit : run preTailLook [20736,20743] 20736 [.br false] = some cExit := optBeq_eq (by decide +kernel)
theorem cLoopMem_get (s : MachineState) (S D A : Nat) (hD : D + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s cLoopMem (BitVec.ofNat 64 A) =
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold cLoopMem
  rw [memEval_cons, memEval_cons, memEval_nil]
  have e1 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ = BitVec.ofNat 64 (D + 8) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 8
  have e0 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ = BitVec.ofNat 64 D := by
    simp only [Addr.eval, E.eval, h29, ofNat_add_ofNat, Nat.add_zero]
  have v1 : (E.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))).eval s = s.getMem (BitVec.ofNat 64 (S + 8)) := by
    simp only [E.eval, BinOp.eval, h28]; rw [ofNat_add_ofNat S 8]
  have v0 : (E.ld (.reg .x28)).eval s = s.getMem (BitVec.ofNat 64 S) := by
    simp only [E.eval, h28]
  rw [e1, e0, v1, v0]
  simp only [ofNat_inj hA (show D + 8 < 2 ^ 64 by so), ofNat_inj hA (show D < 2 ^ 64 by so)]
theorem cLoopObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 16 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ cLoopObl, o.holds s := by
  unfold MEMORY_BYTES at hS hD
  intro o ho
  simp only [cLoopObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, h28, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
theorem cBr_holds (s : MachineState) (S : Nat) (d : Bool) (hS : S + 16 < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h30 : s.getReg .x30 = BitVec.ofNat 64 (SIG + 5616))
    (hd : (decide (S + 16 < SIG + 5616)) = d) : (cBr d).holds s := by
  simp only [Br.holds, cBr, CmpOp.eval, E.eval, BinOp.eval, h28, h30]
  rw [ofNat_add_ofNat]
  rw [← hd]
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt (show SIG + 5616 < 2 ^ 64 by
    decide)]
structure CInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 20736
  x28 : t.getReg .x28 = BitVec.ofNat 64 (SIG + 2240 + 16 * k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 1888 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 2240 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 1888 ≤ A ∧ A < SIG + 1888 + 16 * k)
theorem cIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 211) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 1888 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 2240 + 16 * k + 8))
      else if A = SIG + 1888 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 2240 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem cIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 211) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (u : MachineState) (hu : u = r.toState t)
    (hpc : u.pc = pcOf 20736) (h28 : u.getReg .x28 = BitVec.ofNat 64 (SIG + 2240 + 16 * (k + 1)))
    (h29 : u.getReg .x29 = BitVec.ofNat 64 (SIG + 1888 + 16 * (k + 1)))
    (h30 : u.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)) : CInv s0 (k + 1) u := by
  subst hu
  refine ⟨hpc, h28, h29, h30, fun j hj => ?_, fun A hA hn => ?_⟩
  · rw [cIter_mem hk h r hmem _ (by so)]
    by_cases hj2 : j < 2 * k
    · rw [if_neg (by so), if_neg (by so)]; exact h.done j hj2
    · by_cases hje : j = 2 * k
      · subst hje; rw [if_neg (by so), if_pos (by so)]; congr 2; omega
      · have : j = 2 * k + 1 := by so
        subst this; rw [if_pos (by so)]; congr 2; omega
  · rw [cIter_mem hk h r hmem A hA, if_neg (by so), if_neg (by so)]
    exact h.frame.get hA (by so)
theorem cLoop {im : Image} (hl : LookOK im preTailLook) {s0 u : MachineState} (h0 : CInv s0 0 u) :
    ∀ k, k ≤ 210 → ∃ t, Steps im u (7 * k) (7 * k) t ∧ CInv s0 k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, st, ht⟩ := ih (by so)
    obtain ⟨st1, -⟩ := run_sound hl run_cBack t ht.pc
      (cLoopObl_holds t _ _ (by so) (by so) (by so)
        (by so) ht.x28 ht.x29)
      (by
        intro b hb
        simp only [cBack, List.mem_singleton] at hb
        subst hb
        exact cBr_holds t _ true (by so) ht.x28 ht.x30 (by simp; omega))
    refine ⟨_, (st.trans st1).of_eq (by simp [cBack]; ring) (by simp [cBack]; ring),
      cIter_inv (by so) ht cBack rfl _ rfl (PRes.toState_pc' _ _ rfl) ?_ ?_ ?_⟩
    · rw [PRes.toState_getReg']
      show (E.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16))).eval t = _
      simp only [E.eval, BinOp.eval, ht.x28]; rw [ofNat_add_ofNat]; congr 1
    · rw [PRes.toState_getReg']
      show (E.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16))).eval t = _
      simp only [E.eval, BinOp.eval, ht.x29]; rw [ofNat_add_ofNat]; congr 1
    · rw [PRes.toState_getReg']; exact ht.x30
/-- [h2 lane] the sign prepass (words 20813..20831, entered from the copy hook at 20730). -/
def pSetupRegs : RegFile :=
  ((((RegFile.init.set .x14 (.ld (.c (BitVec.ofNat 64 0x7ca0)))).set .x15 (.ld (.c (BitVec.ofNat 64 0x7ca8)))).set .x28
    (.c (BitVec.ofNat 64 0x7cb0))).set .x29 (.c (BitVec.ofNat 64 0x7ca0))).set .x30 (.c (BitVec.ofNat 64 0x85f0))
def pSetup : PRes := ⟨⟨pSetupRegs, [], []⟩, pcOf 20821, false, 9, 9, [], none⟩
def pBack : PRes := ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20821, false, 7, 7, [cBr true], none⟩
def pExitRegs : RegFile :=
  ((cLoopRegs.set .x28 (.c (BitVec.ofNat 64 0x78c0))).set .x29 (.c (BitVec.ofNat 64 0x7760))).set .x30
    (.c (BitVec.ofNat 64 0x85f0))
def pExitMem : SymMem :=
  (⟨some (.reg .x29), BitVec.ofNat 64 24⟩, .reg .x15) :: (⟨some (.reg .x29), BitVec.ofNat 64 16⟩, .reg .x14) :: cLoopMem
def pExitObl : List Oblig :=
  .valid ⟨some (.reg .x29), BitVec.ofNat 64 24⟩ 8 :: .valid ⟨some (.reg .x29), BitVec.ofNat 64 16⟩ 8 :: cLoopObl
def pExit : PRes := ⟨⟨pExitRegs, pExitMem, pExitObl⟩, pcOf 20736, false, 16, 16, [cBr false], none⟩
theorem run_pSetup : run preCLook [20821] 20730 [] = some pSetup := optBeq_eq (by decide +kernel)
theorem run_pBack : run preCLook [20821] 20821 [.br true] = some pBack := optBeq_eq (by decide +kernel)
theorem run_pExit : run preCLook [20736] 20821 [.br false] = some pExit := optBeq_eq (by decide +kernel)
theorem pExitMem_get (s : MachineState) (S D A : Nat) (hD : D + 32 < 2 ^ 64) (hA : A < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s pExitMem (BitVec.ofNat 64 A) =
      if A = D + 24 then s.getReg .x15 else if A = D + 16 then s.getReg .x14 else
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold pExitMem
  rw [memEval_cons, memEval_cons]
  have e24 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 24⟩ = BitVec.ofNat 64 (D + 24) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 24
  have e16 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 16⟩ = BitVec.ofNat 64 (D + 16) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 16
  have v15 : (E.reg .x15).eval s = s.getReg .x15 := rfl
  have v14 : (E.reg .x14).eval s = s.getReg .x14 := rfl
  rw [e24, e16, v15, v14, cLoopMem_get s S D A (by so) hA h28 h29]
  simp only [ofNat_inj hA (show D + 24 < 2 ^ 64 by so), ofNat_inj hA (show D + 16 < 2 ^ 64 by so)]
theorem pExitObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 32 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ pExitObl, o.holds s := by
  intro o ho
  simp only [pExitObl, List.mem_cons] at ho
  rcases ho with rfl | rfl | ho
  · unfold MEMORY_BYTES at hD
    simp only [Oblig.holds, Addr.eval, E.eval, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
  · unfold MEMORY_BYTES at hD
    simp only [Oblig.holds, Addr.eval, E.eval, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
  · exact cLoopObl_holds s S D hS (by so) hS8 hD8 h28 h29 o ho
structure PInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 20821
  x28 : t.getReg .x28 = BitVec.ofNat 64 (SIG + 3248 + 16 * k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 3232 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  x14 : t.getReg .x14 = s0.getMem (BitVec.ofNat 64 (SIG + 3232))
  x15 : t.getReg .x15 = s0.getMem (BitVec.ofNat 64 (SIG + 3240))
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 3232 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 3232 ≤ A ∧ A < SIG + 3232 + 16 * k)
theorem pIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 148) (h : PInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 3232 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 16 * k + 8))
      else if A = SIG + 3232 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem pIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 148) (h : PInv s0 k t) (u : MachineState)
    (hu : u = pBack.toState t) : PInv s0 (k + 1) u := by
  subst hu
  refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun A hA hn => ?_⟩
  · rw [PRes.toState_getReg']
    show (E.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16))).eval t = _
    simp only [E.eval, BinOp.eval, h.x28]; rw [ofNat_add_ofNat]; congr 1
  · rw [PRes.toState_getReg']
    show (E.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16))).eval t = _
    simp only [E.eval, BinOp.eval, h.x29]; rw [ofNat_add_ofNat]; congr 1
  · rw [PRes.toState_getReg']; exact h.x30
  · rw [PRes.toState_getReg']; exact h.x14
  · rw [PRes.toState_getReg']; exact h.x15
  · rw [pIter_mem hk h pBack rfl _ (by so)]
    by_cases hj2 : j < 2 * k
    · rw [if_neg (by so), if_neg (by so)]; exact h.done j hj2
    · by_cases hje : j = 2 * k
      · subst hje; rw [if_neg (by so), if_pos (by so)]; congr 2; omega
      · have : j = 2 * k + 1 := by so
        subst this; rw [if_pos (by so)]; congr 2; omega
  · rw [pIter_mem hk h pBack rfl A hA, if_neg (by so), if_neg (by so)]
    exact h.frame.get hA (by so)
theorem pLoop {im : Image} (hl : LookOK im preCLook) {s0 u : MachineState} (h0 : PInv s0 0 u) :
    ∀ k, k ≤ 147 → ∃ t, Steps im u (7 * k) (7 * k) t ∧ PInv s0 k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, st, ht⟩ := ih (by so)
    obtain ⟨st1, -⟩ := run_sound hl run_pBack t ht.pc
      (cLoopObl_holds t _ _ (by so) (by so) (by so) (by so) ht.x28 ht.x29)
      (by
        intro b hb
        simp only [pBack, List.mem_singleton] at hb
        subst hb
        exact cBr_holds t _ true (by so) ht.x28 ht.x30 (by simp; omega))
    exact ⟨_, (st.trans st1).of_eq (by simp [pBack]; ring) (by simp [pBack]; ring),
      pIter_inv (by so) ht _ rfl⟩
/-- Campaign T51: compact slot `118 + p` reads scratch slot `140 + cpIdxT p` (relative to the first T51 top value,
slot 140): the top sibling (relative slot 62) goes last, the 148 lower-layer slots move down one (#938: 65 / 213). -/
def cpIdxT (p : Nat) : Nat := if p < 62 then p else if p < 210 then p + 1 else 62
def preCost : Nat := 1 + 9 + 148 * 7 + 4 + 5 + 211 * 7

def PrePost (s t : MachineState) : Prop :=
  t.pc=pcOf 20743 ∧
  (∀ k < 422, t.getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * k)) =
    s.getMem (BitVec.ofNat 64 (SIG + 2240 + 16 * cpIdxT (k / 2) + 8 * (k % 2)))) ∧
  Frame s t (fun A => SIG + 1888 ≤ A ∧ A < SIG + 5616)

theorem pre_good {im : Image} (hlt : LookOK im preTailLook) (hlh : LookOK im preHookLook)
    (hlc : LookOK im preCLook) (s : MachineState) (hpc : s.pc=pcOf 540) :
    ∃t, Steps im s preCost preCost t ∧ PrePost s t := by
  obtain ⟨s1, -⟩ := run_sound hlh run_cHook s hpc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u1 := cHook.toState s with hu1
  have u1pc : u1.pc = pcOf 20730 := PRes.toState_pc' _ _ rfl
  obtain ⟨s2, -⟩ := run_sound hlc run_pSetup u1 u1pc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u2 := pSetup.toState u1 with hu2
  have h0 : PInv s 0 u2 := by
    refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => by so, fun A _ _ => rfl⟩
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
  obtain ⟨t, st, ht⟩ := pLoop hlc h0 147 le_rfl
  obtain ⟨s3, -⟩ := run_sound hlc run_pExit t ht.pc
    (pExitObl_holds t _ _ (by so) (by so) (by so) (by so) ht.x28 ht.x29)
    (by
      intro b hb
      simp only [pExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t _ false (by so) ht.x28 ht.x30 (by simp))
  set u3 := pExit.toState t with hu3
  have u3pc : u3.pc = pcOf 20736 := PRes.toState_pc' _ _ rfl
  have u3get : ∀ A, A < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 A) =
      if A = SIG + 5608 then s.getMem (BitVec.ofNat 64 (SIG + 3240))
      else if A = SIG + 5600 then s.getMem (BitVec.ofNat 64 (SIG + 3232))
      else if A = SIG + 5592 then s.getMem (BitVec.ofNat 64 (SIG + 5608))
      else if A = SIG + 5584 then s.getMem (BitVec.ofNat 64 (SIG + 5600))
      else t.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu3, PRes.toState_getMem']
    show memEval t pExitMem (BitVec.ofNat 64 A) = _
    rw [pExitMem_get t (SIG + 3248 + 16 * 147) (SIG + 3232 + 16 * 147) A (by so) hA ht.x28 ht.x29, ht.x15, ht.x14,
      ht.frame.get (A := SIG + 3248 + 16 * 147 + 8) (by so) (by so),
      ht.frame.get (A := SIG + 3248 + 16 * 147) (by so) (by so)]
    try rfl
  have u3frame : Frame s u3 (fun A => SIG + 3232 ≤ A ∧ A < SIG + 5616) := fun A hA hn => by
    rw [u3get A hA, if_neg (by so), if_neg (by so), if_neg (by so), if_neg (by so)]
    exact ht.frame.get hA (by so)
  have u3mem : ∀ k < 422, u3.getMem (BitVec.ofNat 64 (SIG + 2240 + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (SIG + 2240 + 16 * cpIdxT (k / 2) + 8 * (k % 2))) := by
    intro k hk
    rw [u3get _ (by so)]
    unfold cpIdxT
    by_cases k1 : k = 421
    · subst k1; rw [if_pos (by so)]; rfl
    by_cases k2 : k = 420
    · subst k2; rw [if_neg (by so), if_pos (by so)]; rfl
    by_cases k3 : k = 419
    · subst k3; rw [if_neg (by so), if_neg (by so), if_pos (by so)]; rfl
    by_cases k4 : k = 418
    · subst k4; rw [if_neg (by so), if_neg (by so), if_neg (by so), if_pos (by so)]; rfl
    rw [if_neg (by so), if_neg (by so), if_neg (by so), if_neg (by so)]
    by_cases hlo : k < 124
    · rw [ht.frame.get (by so) (by so), if_pos (show k / 2 < 62 by omega)]
      congr 2; omega
    · have hd := ht.done (k - 124) (by omega)
      rw [show SIG + 3232 + 8 * (k - 124) = SIG + 2240 + 8 * k by so] at hd
      rw [hd, if_neg (show ¬ k / 2 < 62 by omega), if_pos (show k / 2 < 210 by omega)]
      rw [show SIG + 3248 + 8 * (k - 124) = SIG + 2240 + 16 * (k / 2 + 1) + 8 * (k % 2) by so]
  have h0' : CInv u3 0 u3 := by
    refine ⟨u3pc, ?_, ?_, ?_, fun j hj => by so, Frame.refl _ _⟩
    · rw [hu3, PRes.toState_getReg']; rfl
    · rw [hu3, PRes.toState_getReg']; rfl
    · rw [hu3, PRes.toState_getReg']; rfl
  obtain ⟨t', st', ht'⟩ := cLoop hlt h0' 210 le_rfl
  obtain ⟨s4, -⟩ := run_sound hlt run_cExit t' ht'.pc
    (cLoopObl_holds t' _ _ (by so) (by so) (by so)
      (by so) ht'.x28 ht'.x29)
    (by
      intro b hb
      simp only [cExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t' _ false (by so) ht'.x28 ht'.x30 (by simp))
  have hfin : ∀ k < 422, (cExit.toState t').getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * k)) =
      u3.getMem (BitVec.ofNat 64 (SIG + 2240 + 8 * k)) := by
    intro k hk
    rw [cIter_mem (by so) ht' cExit rfl _ (by so)]
    by_cases hk2 : k < 2 * 210
    · rw [if_neg (by so), if_neg (by so)]; exact ht'.done k hk2
    · by_cases hke : k = 2 * 210
      · subst hke; rw [if_neg (by so), if_pos (by so)]
      · have : k = 2 * 210 + 1 := by so
        subst this; rw [if_pos (by so)]
  refine ⟨cExit.toState t', ((s1.trans s2).trans ((st.trans s3).trans (st'.trans s4))).of_eq
    (by simp [cHook, pSetup, pExit, cExit, preCost]) (by simp [cHook, pSetup, pExit, cExit, preCost]),
    PRes.toState_pc' _ _ rfl, fun k hk => (hfin k hk).trans (u3mem k hk), fun A hA hn => ?_⟩
  rw [cIter_mem (by so) ht' cExit rfl A hA, if_neg (by so), if_neg (by so),
      ht'.frame.get hA (by so), u3frame.get hA (by so)]

end ClaudeWCT.W9.Machine.Sign.SharedSerializer

namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def tailWords : List (BitVec 32) := bv_list% 32 [0xd00313,0x2690863,0x2700313,0x2690463,0x4100313,0x2690063,0x5b00313,0x690c63,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e8e93,0x10e0e13,0x190913,0x14800313,0xfc6960e3]
def tailLook (n : Nat) : Option (BitVec 32) := if 22509≤n then tailWords[n-22509]? else none

def iterDirs (kind : Fin 5) (back : Bool) : List Dir :=
  List.replicate kind.val (.br false) ++ (if kind.val<4 then [.br true] else []) ++ [.br back]
def iterRegs (kind : Fin 5) : RegFile :=
  regsOf ([ (.x6,cE 328), (.x18,x18p1), (.x28,.bin .add (.reg .x28) (cE 16)) ] ++
    if kind.val=4 then [(.x7,.ld (.bin .add (.reg .x28) (cE 8))),(.x29,.bin .add (.reg .x29) (cE 16))] else [])
def iterMem : SymMem :=
  [(⟨some (.reg .x29),BitVec.ofNat 64 8⟩,.ld (.bin .add (.reg .x28) (cE 8))),
   (⟨some (.reg .x29),BitVec.ofNat 64 0⟩,.ld (.reg .x28))]
def iterObl : List Oblig :=
  [.valid ⟨some (.reg .x29),BitVec.ofNat 64 8⟩ 8,.valid ⟨some (.reg .x29),BitVec.ofNat 64 0⟩ 8,
   .valid ⟨some (.reg .x28),BitVec.ofNat 64 8⟩ 8,.valid ⟨some (.reg .x28),BitVec.ofNat 64 0⟩ 8]
def iterBranches (kind : Fin 5) (back : Bool) : List Br :=
  ⟨.ltu,x18p1,cE 328,back⟩ ::
  ((List.range (if kind.val<4 then kind.val+1 else 4)).map fun k=>
    (⟨.eq,.reg .x18,cE (13+26*k),decide (k=kind.val)⟩ : Br)).reverse

def iterCost (kind : Fin 5) : Nat := if kind.val=4 then 17 else 6+2*kind.val

def iterResult (kind : Fin 5) (back : Bool) : PRes :=
  ⟨⟨iterRegs kind,if kind.val=4 then iterMem else [],if kind.val=4 then iterObl else []⟩,
    pcOf (if back then 22509 else 22526),false,iterCost kind,iterCost kind,iterBranches kind back,none⟩

theorem run_iter (kind : Fin 5) (back : Bool) :
    run tailLook [22509,22526] 22509 (iterDirs kind back)=some (iterResult kind back) := by
  fin_cases kind <;> cases back <;> exact optBeq_eq (by decide +kernel)

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))
theorem iterMem_get (s : MachineState) (S D A : Nat) (hD : D + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s iterMem (BitVec.ofNat 64 A) =
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold iterMem cE
  rw [memEval_cons, memEval_cons, memEval_nil]
  have e1 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ = BitVec.ofNat 64 (D + 8) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 8
  have e0 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ = BitVec.ofNat 64 D := by
    simp only [Addr.eval, E.eval, h29, ofNat_add_ofNat, Nat.add_zero]
  have v1 : (E.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))).eval s = s.getMem (BitVec.ofNat 64 (S + 8)) := by
    simp only [E.eval, BinOp.eval, h28]; rw [ofNat_add_ofNat S 8]
  have v0 : (E.ld (.reg .x28)).eval s = s.getMem (BitVec.ofNat 64 S) := by
    simp only [E.eval, h28]
  rw [e1, e0, v1, v0]
  simp only [ofNat_inj hA (show D + 8 < 2 ^ 64 by so), ofNat_inj hA (show D < 2 ^ 64 by so)]
theorem iterObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 16 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ iterObl, o.holds s := by
  unfold MEMORY_BYTES at hS hD
  intro o ho
  simp only [iterObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, h28, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so

def validKind (kind : Fin 5) (j : Nat) : Prop :=
  if kind.val=4 then ∀k,k<4 → j≠13+26*k else j=13+26*kind.val

theorem iterBranches_holds (kind : Fin 5) (j : Nat) (hj : j<328) (hk : validKind kind j)
    (s : MachineState) (h18 : s.getReg .x18=BitVec.ofNat 64 j) (back : Bool)
    (hb : decide (j+1<328)=back) :
    ∀b∈iterBranches kind back,b.holds s := by
  have hj64 : j<2^64 := by omega
  have hj164 : j+1<2^64 := by omega
  intro b hmem
  simp only [iterBranches,List.mem_cons,List.mem_reverse,List.mem_map,List.mem_range] at hmem
  rcases hmem with rfl | ⟨k,hkb,rfl⟩
  · simpa [Br.holds,CmpOp.eval,E.eval,BinOp.eval,cE,x18p1,h18,ofNat_add_ofNat,
      BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show j+1<18446744073709551616 by omega)] using hb
  · have hk4 : k<4 := by split_ifs at hkb <;> omega
    have he : (j=13+26*k) ↔ k=kind.val := by
      unfold validKind at hk
      by_cases hc : kind.val=4
      · have hn := (show ∀k,k<4 → j≠13+26*k by simpa [hc] using hk) k hk4
        omega
      · have hjk : j=13+26*kind.val := by simpa [hc] using hk
        omega
    simp only [Br.holds,CmpOp.eval,E.eval,cE,h18]
    change (BitVec.ofNat 64 j == BitVec.ofNat 64 (13+26*k))=decide (k=kind.val)
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,decide_eq_true_eq,ofNat_inj hj64 (show 13+26*k<2^64 by omega)] using he

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem iter_steps {im : Image} (hc : LookOK im tailLook)
    (kind : Fin 5) (j d : Nat) (hj : j<328) (hd : d≤j) (hk : validKind kind j)
    (s : MachineState) (hp : s.pc=pcOf 22509)
    (h18 : s.getReg .x18=BitVec.ofNat 64 j)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (SIG+16*j))
    (h29 : s.getReg .x29=BitVec.ofNat 64 (SIG+16*d)) :
    ∃t, Steps im s (iterCost kind) (iterCost kind) t ∧
      t.pc=pcOf (if j+1<328 then 22509 else 22526) ∧
      t.getReg .x18=BitVec.ofNat 64 (j+1) ∧
      t.getReg .x28=BitVec.ofNat 64 (SIG+16*(j+1)) ∧
      t.getReg .x29=BitVec.ofNat 64 (SIG+16*(d+if kind.val=4 then 1 else 0)) ∧
      (∀A,A<2^64 → t.getMem (BitVec.ofNat 64 A)=
        if kind.val=4 then
          if A=SIG+16*d+8 then s.getMem (BitVec.ofNat 64 (SIG+16*j+8))
          else if A=SIG+16*d then s.getMem (BitVec.ofNat 64 (SIG+16*j))
          else s.getMem (BitVec.ofNat 64 A)
        else s.getMem (BitVec.ofNat 64 A)) ∧
      RegsExcept s t [.x6,.x7,.x18,.x28,.x29] := by
  have ho : ∀o∈(iterResult kind (decide (j+1<328))).st.obl,o.holds s := by
    change ∀o∈(if kind.val=4 then iterObl else []),o.holds s
    split_ifs
    · exact iterObl_holds s (SIG+16*j) (SIG+16*d) (by simp [SIG,MEMORY_BYTES];omega)
        (by simp [SIG,MEMORY_BYTES];omega) (by simp [SIG];omega) (by simp [SIG];omega) h28 h29
    · simp
  have hs := (run_sound hc (run_iter kind (decide (j+1<328))) s hp ho
    (iterBranches_holds kind j hj hk s h18 _ rfl)).1
  refine ⟨_,hs,?_,?_,?_,?_,?_,?_⟩
  · simp [PRes.toState_pc',iterResult]
  · rw [PRes.toState_getReg']
    fin_cases kind <;> simp [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE,x18p1,h18,ofNat_add_ofNat]
  · rw [PRes.toState_getReg']
    fin_cases kind <;> simp [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE,h28,ofNat_add_ofNat] <;>
      congr 1 <;> omega
  · rw [PRes.toState_getReg']
    fin_cases kind <;> simp [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE,h29,ofNat_add_ofNat] <;>
      congr 1 <;> omega
  · intro A hA
    rw [PRes.toState_getMem']
    change memEval s (if kind.val=4 then iterMem else []) _ = _
    by_cases hk : kind.val=4
    · rw [if_pos hk,if_pos hk]
      exact iterMem_get s (SIG+16*j) (SIG+16*d) A (by simp [SIG];omega) hA h28 h29
    · rw [if_neg hk,if_neg hk]; rfl
  · intro r hr
    rw [PRes.toState_getReg']
    fin_cases kind <;> cases r <;> simp_all [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE] <;> rfl

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))

def kept (n : Nat) : Nat :=
  if n≤13 then n else if n≤39 then n-1 else if n≤65 then n-2 else if n≤91 then n-3 else n-4
def sourceIndex (n : Nat) : Nat :=
  if n<13 then n else if n<38 then n+1 else if n<63 then n+2 else if n<88 then n+3 else n+4

def kind (n : Nat) : Fin 5 :=
  if n=13 then 0 else if n=39 then 1 else if n=65 then 2 else if n=91 then 3 else 4

theorem kind_valid (n : Nat) : validKind (kind n) n := by
  unfold kind validKind
  split_ifs <;> simp_all
  intro k hk
  omega

theorem kept_le (n : Nat) : kept n≤n := by unfold kept;split_ifs <;> omega

theorem kept_succ (k : Fin 5) (n : Nat) (h : validKind k n) :
    kept (n+1)=kept n+(if k.val=4 then 1 else 0) := by
  unfold validKind at h
  by_cases hk : k.val=4
  · rw [if_pos hk] at h ⊢
    have h0:=h 0 (by decide);have h1:=h 1 (by decide)
    have h2:=h 2 (by decide);have h3:=h 3 (by decide)
    unfold kept
    split_ifs <;> omega
  · rw [if_neg hk] at h ⊢
    have := k.isLt
    unfold kept
    split_ifs <;> omega

theorem source_kept (n : Nat) (h : validKind 4 n) : sourceIndex (kept n)=n := by
  simp only [validKind,Fin.reduceFinMk,ite_true] at h
  have h0:=h 0 (by decide);have h1:=h 1 (by decide)
  have h2:=h 2 (by decide);have h3:=h 3 (by decide)
  unfold sourceIndex kept
  split_ifs <;> omega

structure TailInv (s : MachineState) (j : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if j<328 then 22509 else 22526)
  x18 : t.getReg .x18=BitVec.ofNat 64 j
  x28 : t.getReg .x28=BitVec.ofNat 64 (SIG+16*j)
  x29 : t.getReg .x29=BitVec.ofNat 64 (SIG+16*kept j)
  done : ∀k,k<2*kept j → t.getMem (BitVec.ofNat 64 (SIG+8*k))=
    s.getMem (BitVec.ofNat 64 (SIG+16*sourceIndex (k/2)+8*(k%2)))
  frame : Frame s t (fun A=>SIG≤A ∧ A<SIG+16*kept j)

theorem tail_iter {im : Image} (hc : LookOK im tailLook) {s t : MachineState} {j : Nat}
    (hj : j<328) (h : TailInv s j t) :
    ∃u, Steps im t (iterCost (kind j)) (iterCost (kind j)) u ∧ TailInv s (j+1) u := by
  have hk := kind_valid j
  have hd := kept_le j
  obtain ⟨u,st,pc,x18,x28,x29,mem,regs⟩:=iter_steps hc (kind j) j (kept j) hj hd hk t
    (by simpa [hj] using h.pc) h.x18 h.x28 h.x29
  have ksucc := kept_succ (kind j) j hk
  have mm (A : Nat) (hA : A<2^64) : u.getMem (BitVec.ofNat 64 A)=
      if (kind j).val=4 then
        if A=SIG+16*kept j+8 then s.getMem (BitVec.ofNat 64 (SIG+16*j+8))
        else if A=SIG+16*kept j then s.getMem (BitVec.ofNat 64 (SIG+16*j))
        else t.getMem (BitVec.ofNat 64 A)
      else t.getMem (BitVec.ofNat 64 A) := by
    rw [mem A hA,h.frame.get (by so) (by so),h.frame.get (by so) (by so)]
  refine ⟨u,st,pc,x18,x28,?_,?_,?_⟩
  · simpa only [ksucc] using x29
  · intro k hkbound
    rw [mm _ (by have:=kept_le (j+1);so)]
    by_cases hc : (kind j).val=4
    · rw [if_pos hc]
      have hkg : kind j=4 := Fin.ext hc
      have hsource := source_kept j (hkg ▸ hk)
      rw [hc,if_pos rfl] at ksucc
      by_cases hprior : k<2*kept j
      · rw [if_neg (by so),if_neg (by so)]
        exact h.done k hprior
      · have he : k=2*kept j ∨ k=2*kept j+1 := by omega
        rcases he with rfl | rfl
        · rw [if_neg (by so),if_pos (by so)]
          simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.mul_mod_right,Nat.mul_zero,Nat.add_zero,hsource]
        · rw [if_pos (by so)]
          have hdv : (2*kept j+1)/2=kept j := by omega
          have hmd : (2*kept j+1)%2=1 := by omega
          rw [hdv,hmd,hsource]
    · rw [if_neg hc]
      exact h.done k (by rw [ksucc,if_neg hc] at hkbound;omega)
  · intro A hA hn
    rw [mm A hA]
    by_cases hc : (kind j).val=4
    · rw [if_pos hc,if_neg (by rw [ksucc,if_pos hc] at hn;so),
        if_neg (by rw [ksucc,if_pos hc] at hn;so)]
      exact h.frame.get hA (by rw [ksucc,if_pos hc] at hn;so)
    · rw [if_neg hc]
      exact h.frame.get hA (by rw [ksucc,if_neg hc] at hn;simpa using hn)

theorem tail_loop {im : Image} (hc : LookOK im tailLook) {s u : MachineState}
    (h0 : TailInv s 0 u) : ∀j,j≤328 → ∃n≤17*j,∃t,Steps im u n n t ∧ TailInv s j t := by
  intro j
  induction j with
  | zero => intro _;exact ⟨0,by omega,u,Steps.refl u,h0⟩
  | succ j ih =>
    intro hj
    obtain ⟨n,hn,t,st,ht⟩:=ih (by omega)
    obtain ⟨v,sv,hv⟩:=tail_iter hc (by omega) ht
    refine ⟨n+iterCost (kind j),?_,v,st.trans sv,hv⟩
    have := (kind j).isLt
    unfold iterCost
    split_ifs <;> omega

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def setupWords : List (BitVec 32) := bv_list% 32 [0x7e37,0xe0e13,0x7eb7,0xe8e93,0x913]
/-- Campaign T51 (22526..22538): slot 324 = sibling bits 0..87 (the high word masked to 24 bits); `t1 = X` = sibling
bits 88..103 | hint << 16; `jal 24971`. -/
def finishWords : List (BitVec 32) := bv_list% 32 [0xe3303,0x8e3383,0x2839e13,0x28e5e13,0x6eb023,0x1ceb423,0x1839393,0x303d393,0x66f37,0xf3f03,0x10f1f13,0x1e3e333,0x6040206f]

sym_block setupRun := symRun {noAlias:=true} setupWords (pcOf 22504) 20
sym_block finishRun := symRun {noAlias:=true} finishWords (pcOf 22526) 20

theorem setup_steps {im : Image} (hc : CodeAt im (pcOf 22504) setupWords)
    (s : MachineState) (hp : s.pc=pcOf 22504) :
    ∃t, Steps im s 5 5 t ∧ TailInv s 0 t := by
  refine ⟨_,symRun_sound setupRun hc s hp ?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setupRun.res,rv_simp]
  · rfl
  · simp [setupRun.res,rv_simp]
  · simp [setupRun.res,rv_simp,SIG]
  · simp [setupRun.res,rv_simp,SIG,kept]
  · simp [kept]
  · intro A hA hn;rfl

theorem finish_steps {im : Image} (hc : CodeAt im (pcOf 22526) finishWords)
    (s : MachineState) (hp : s.pc=pcOf 22526)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (SIG+16*328))
    (h29 : s.getReg .x29=BitVec.ofNat 64 (SIG+16*324)) :
    ∃t, Steps im s 13 13 t ∧ t.pc=pcOf 24971 ∧
      t.getReg .x6=((s.getMem (BitVec.ofNat 64 (SIG+16*328+8))<<<24)>>>48) ||| (s.getMem 0x66000<<<16) ∧
      t.getMem (BitVec.ofNat 64 (SIG+16*324))=s.getMem (BitVec.ofNat 64 (SIG+16*328)) ∧
      t.getMem (BitVec.ofNat 64 (SIG+16*324+8))=(s.getMem (BitVec.ofNat 64 (SIG+16*328+8))<<<40)>>>40 ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧
      Frame s t (fun A=>A=SIG+16*324 ∨ A=SIG+16*324+8) := by
  refine ⟨_,symRun_sound finishRun hc s hp ?_,?_,?_,?_,?_,?_,?_⟩
  · simp [finishRun.res,rv_simp,h28,h29,SIG,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [finishRun.res,rv_simp,h28,h29,SIG]
  · simp [finishRun.res,rv_simp,h28,h29,SIG]
  · simp [finishRun.res,rv_simp,h28,h29,SIG]
  · intro r hr; simp at hr; cases r <;> simp_all [finishRun.res,rv_simp] <;> rfl
  · intro A hA hn
    have h0 : A≠SIG+16*324 := by tauto
    have h8 : A≠SIG+16*324+8 := by tauto
    simp [finishRun.res,rv_simp,h28,h29,SIG,ofNat_inj hA (by decide : 33856<2^64),
      ofNat_inj hA (by decide : 33864<2^64)]
    simp_all [SIG]

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))

/-- X from the finish block: sibling high word bits 24..39 (sibling bits 88..103) | hint word << 16. -/
def Xw (a h : Word) : Word := ((a <<< 24) >>> 48) ||| (h <<< 16)
def packedWord (read : Nat→Word) (k : Nat) : Word :=
  if k<648 then read (2*sourceIndex (k/2)+k%2)
  else if k=648 then read 656
  else (read 657<<<40)>>>40

theorem tail_readout {im : Image} (hs : CodeAt im (pcOf 22504) setupWords)
    (hl : LookOK im tailLook) (hf : CodeAt im (pcOf 22526) finishWords)
    (s : MachineState) (hp : s.pc=pcOf 22504) :
    ∃n≤5594,∃t,Steps im s n n t ∧ t.pc=pcOf 24971 ∧
      t.getReg .x6=Xw (s.getMem (BitVec.ofNat 64 (SIG+8*657))) (s.getMem 0x66000) ∧
      (∀k,k<650 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=packedWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) k) ∧
      Frame s t (fun A=>SIG≤A ∧ A<SIG+5200) := by
  obtain ⟨u,su,hu⟩:=setup_steps hs s hp
  obtain ⟨n,hn,v,sv,hv⟩:=tail_loop hl hu 328 (by omega)
  obtain ⟨t,st,pc,x6,lo,hi,regs,frame⟩:=finish_steps hf v
    (by simpa using hv.pc) hv.x28 (by simpa [kept] using hv.x29)
  have hframe : Frame s v (fun A=>SIG≤A ∧ A<SIG+5184) := by simpa [kept] using hv.frame
  have hh : v.getMem (0x66000 : Word)=s.getMem (0x66000 : Word) :=
    hframe.get (A:=0x66000) (by decide) (by simp [SIG])
  have r656 : v.getMem (BitVec.ofNat 64 (SIG+16*328))=s.getMem (BitVec.ofNat 64 (SIG+8*656)) :=
    hframe.get (by decide) (by simp [SIG])
  have r657 : v.getMem (BitVec.ofNat 64 (SIG+16*328+8))=s.getMem (BitVec.ofNat 64 (SIG+8*657)) :=
    hframe.get (by decide) (by simp [SIG])
  refine ⟨5+n+13,by omega,t,(su.trans sv).trans st,pc,?_,?_,?_⟩
  · rw [x6,r657,hh]; rfl
  · intro k hk
    unfold packedWord
    by_cases hk648 : k<648
    · rw [if_pos hk648,frame.get (by so) (by so)]
      have hdone:=hv.done k (by simpa [kept] using hk648)
      rw [hdone]
      congr 2
      omega
    · rw [if_neg hk648]
      by_cases he : k=648
      · subst k;rw [if_pos rfl,show SIG+8*648=SIG+16*324 by rfl,lo,r656]
      · have he' : k=649 := by omega
        subst k;rw [if_neg (by omega),show SIG+8*649=SIG+16*324+8 by rfl,hi,r657]
  · exact (hframe.trans frame).mono (fun A _ h=>by
      rcases h with h|h
      · omega
      · rcases h with h|h <;> so)

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## T51 signature post-pass (sign words 24665..24722, entered by 24971 `jal 24665`)

The finish block (22526..22538) leaves `t1 = X` = sibling bits 88..103 | hint << 16 (29 bits); the post-pass puts
`X >> xOff j` into the top `b_j` bits of the high word of path node `j = 3..10` (words `331 + 2 j`; the old top bits are
cleared first), then `jal 20744` (halt). `b_j` = 1, 1, 2, 3, 4, 5, 6, 7 and `xOff j` = 0, 1, 2, 4, 7, 11, 16, 22. -/
def postWords : List (BitVec 32) := bv_list% 32 [0x100293,0x8f37,0xa88f3383,0x139393,0x13d393,0x3f31e13,0x1c3e3b3,0xa87f3423,0x135313,0xa98f3383,0x139393,0x13d393,0x3f31e13,0x1c3e3b3,0xa87f3c23,0x135313,0xaa8f3383,0x239393,0x23d393,0x3e31e13,0x1c3e3b3,0xaa7f3423,0x235313,0xab8f3383,0x339393,0x33d393,0x3d31e13,0x1c3e3b3,0xaa7f3c23,0x335313,0xac8f3383,0x439393,0x43d393,0x3c31e13,0x1c3e3b3,0xac7f3423,0x435313,0xad8f3383,0x539393,0x53d393,0x3b31e13,0x1c3e3b3,0xac7f3c23,0x535313,0xae8f3383,0x639393,0x63d393,0x3a31e13,0x1c3e3b3,0xae7f3423,0x635313,0xaf8f3383,0x739393,0x73d393,0x3931e13,0x1c3e3b3,0xae7f3c23,0x9d8fc06f]
sym_block entryRun := symRun {noAlias:=true} (bv_list% 32 [0xb39ff06f]) (pcOf 24971) 100
sym_block postRun := symRun {noAlias:=true} postWords (pcOf 24665) 100

/-- Bits `b_j` of path node `j = 3..10` (T51 `topZeroBits`). -/
def bT : Nat → Nat
  | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 7 | _ => 0
/-- Offset `xOff j` of node `j`'s X bits. -/
def oT : Nat → Nat
  | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 4 | 7 => 7 | 8 => 11 | 9 => 16 | 10 => 22 | _ => 0
def postNode (j : Nat) (w X : Word) : Word := ((w <<< bT j) >>> bT j) ||| ((X >>> oT j) <<< (64 - bT j))
def postWord (r : Nat → Word) (X : Word) (k : Nat) : Word :=
  if 337 ≤ k ∧ k ≤ 351 ∧ k % 2 = 1 then postNode ((k - 331) / 2) (r k) X else r k
def postA (A : Nat) : Prop := A = 31368 ∨ A = 31384 ∨ A = 31400 ∨ A = 31416 ∨ A = 31432 ∨ A = 31448 ∨ A = 31464 ∨ A = 31480

theorem postWord_congr {r r' : Nat → Word} (X : Word) (h : ∀ j, j < 650 → r j = r' j) (k : Nat) (hk : k < 650) :
    postWord r X k = postWord r' X k := by
  unfold postWord
  rw [h k hk]

theorem entry_steps {im : Image} (hc : CodeAt im (pcOf 24971) [0xb39ff06f]) (s : MachineState)
    (hp : s.pc=pcOf 24971) :
    ∃t, Steps im s 1 1 t ∧ t.pc=pcOf 24665 ∧ (∀ r, t.getReg r=s.getReg r) ∧ (∀ A, t.getMem A=s.getMem A) := by
  refine ⟨_,symRun_sound entryRun hc s hp (by simp [entryRun.res,rv_simp]),?_,?_,?_⟩
  · simp [entryRun.res,rv_simp]
  · intro r; cases r <;> rfl
  · intro A; rfl

theorem ushr_ushr (x : Word) (a b : Nat) : x >>> a >>> b = x >>> (a+b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  congr 1; omega

theorem post_node (s : MachineState) (j : Nat) (h3 : 3 ≤ j) (h10 : j ≤ 10) :
    (postRun.res.toState s).getMem (BitVec.ofNat 64 (SIG+8*(331+2*j))) =
      postNode j (s.getMem (BitVec.ofNat 64 (SIG+8*(331+2*j)))) (s.getReg .x6) := by
  interval_cases j <;> simp [postRun.res, rv_simp, SIG, postNode, bT, oT, ushr_ushr]

theorem post_frame (s : MachineState) : Frame s (postRun.res.toState s) postA := by
  intro A hA hn
  simp only [postA] at hn
  simp [postRun.res, rv_simp, ofNat_inj hA (by decide : 31368<2^64),ofNat_inj hA (by decide : 31384<2^64),ofNat_inj hA (by decide : 31400<2^64),ofNat_inj hA (by decide : 31416<2^64),ofNat_inj hA (by decide : 31432<2^64),ofNat_inj hA (by decide : 31448<2^64),ofNat_inj hA (by decide : 31464<2^64),ofNat_inj hA (by decide : 31480<2^64)]
  simp_all

theorem post_steps {im : Image} (hc : CodeAt im (pcOf 24665) postWords) (s : MachineState)
    (hp : s.pc=pcOf 24665) :
    ∃t, Steps im s 58 58 t ∧ t.pc=pcOf 20744 ∧ t.getReg .x5=1 ∧
      ∀ k, k < 650 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=
        postWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) (s.getReg .x6) k := by
  refine ⟨_,symRun_sound postRun hc s hp (by simp [postRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_⟩
  · simp [postRun.res,rv_simp]
  · simp [postRun.res,rv_simp]
  · intro k hk
    unfold postWord
    split
    · rename_i h
      have e : k = 331+2*((k-331)/2) := by omega
      have hn := post_node s ((k-331)/2) (by omega) (by omega)
      rw [← e] at hn
      exact hn
    · rename_i h
      show _ = s.getMem _
      exact post_frame s _ (by simp only [SIG]; omega) (by unfold postA; simp only [SIG] at *; omega)

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

structure Code (im : Image) : Prop where
  preHook : CodeAt im (pcOf 540) [hook540]
  preTail : CodeAt im (pcOf 20715) (tailCode.take 28)
  preH2 : CodeAt im (pcOf 20813) h2SignTail
  jump : CodeAt im (pcOf 20743) [0x3850106f]
  setup : CodeAt im (pcOf 22504) setupWords
  loop : CodeAt im (pcOf 22509) tailWords
  finish : CodeAt im (pcOf 22526) finishWords
  entry : CodeAt im (pcOf 24971) [0xb39ff06f]
  post : CodeAt im (pcOf 24665) postWords
  halt : CodeAt im (pcOf 20744) [0x513,0x73]

theorem Code.pre_tail_look {im : Image} (h : Code im) : LookOK im preTailLook := by
  intro n w hw
  unfold preTailLook at hw
  split at hw
  · rename_i hn
    unfold Sign.tailLook at hw
    split at hw
    · rename_i hlo
      have he : (tailCode.take 28)[n-20715]?=some w := by
        rw [List.getElem?_take,if_pos (by omega)];exact hw
      have hh:=codeAt_get_word (by decide : 20715<2^30) h.preTail he
      simpa only [Nat.add_sub_cancel' hlo] using hh
    · cases hw
  · cases hw

theorem Code.pre_hook_look {im : Image} (h : Code im) : LookOK im preHookLook := by
  intro n w hw
  unfold preHookLook at hw
  split at hw
  · rename_i hn
    subst n
    have he : w=hook540 := by simpa [hookLook] using hw.symm
    subst w
    simpa using codeAt_get_word (by decide : 540<2^30) h.preHook (i:=0) (by rfl)
  · cases hw

theorem Code.pre_c_look {im : Image} (h : Code im) : LookOK im preCLook := by
  intro n w hw
  unfold preCLook at hw
  split at hw
  · rename_i hn
    unfold cLook at hw
    split at hw
    · rename_i w' hh
      cases hw
      have hb : n<20743 := by
        unfold Sign.tailLook at hh
        split at hh
        · have hlen := (List.getElem?_eq_some_iff.mp hh).1
          rw [tailCode_length] at hlen
          omega
        · cases hh
      exact h.pre_tail_look n _ (by simpa [preTailLook,hb] using hh)
    · unfold h2Look at hw
      split at hw
      · rename_i hlo
        have hh:=codeAt_get_word (by decide : 20813<2^30) h.preH2 hw
        simpa only [Nat.add_sub_cancel' hlo] using hh
      · cases hw
  · cases hw

theorem Code.tail_look {im : Image} (h : Code im) : LookOK im tailLook := by
  intro n w hw
  unfold tailLook at hw
  split at hw
  · rename_i hn
    have hh:=codeAt_get_word (by decide : 22509<2^30) h.loop hw
    simpa only [Nat.add_sub_cancel' hn] using hh
  · cases hw

theorem installed_code : Code Images.signImage := by
  constructor <;> sign_slice_fast

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))

def preWord (read : Nat→Word) (k : Nat) : Word :=
  if k<236 then read k else read (280+2*cpIdxT ((k-236)/2)+(k-236)%2)

theorem PrePost.read {s t : MachineState} (h : PrePost s t) (k : Nat) (hk : k<658) :
    t.getMem (BitVec.ofNat 64 (SIG+8*k))=preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) k := by
  unfold preWord
  split
  · exact h.2.2.get (by so) (by so)
  · rename_i he
    have hm:=h.2.1 (k-236) (by omega)
    rw [show SIG+1888+8*(k-236)=SIG+8*k by omega,
      show SIG+2240+16*cpIdxT ((k-236)/2)+8*((k-236)%2)=SIG+8*(280+2*cpIdxT ((k-236)/2)+(k-236)%2) by omega] at hm
    exact hm

sym_block jumpRun := symRun { noAlias := true } (bv_list% 32 [0x3850106f]) (pcOf 20743) 100
sym_block haltRun := symRun { noAlias := true } (bv_list% 32 [0x513]) (pcOf 20744) 100

theorem full_readout {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 540) :
    ∃n≤8280,∃t,Steps im s n n t ∧ t.pc=pcOf 20745 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      (∀k,k<650 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=postWord
        (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))))
        (Xw (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) 657) (s.getMem 0x66000)) k) := by
  obtain ⟨a,sa,ha⟩:=pre_good hc.pre_tail_look hc.pre_hook_look hc.pre_c_look s hp
  let b:=jumpRun.res.toState a
  have ab : Steps im a 1 1 b := symRun_sound jumpRun hc.jump a ha.1 (by simp [jumpRun.res,rv_simp])
  have bp : b.pc=pcOf 22504 := by simp [b,jumpRun.res,rv_simp]
  have bm (A : Word) : b.getMem A=a.getMem A := rfl
  obtain ⟨n,hn,u,bu,up,ux6,uw,uf⟩:=tail_readout hc.setup hc.tail_look hc.finish b bp
  have hh : b.getMem (0x66000 : Word)=s.getMem (0x66000 : Word) :=
    (bm _).trans (ha.2.2.get (A:=0x66000) (by decide) (by simp [SIG]))
  have huw : ∀k,k<650 → u.getMem (BitVec.ofNat 64 (SIG+8*k))=
      packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) k := by
    intro k hk
    rw [uw k hk]
    unfold packedWord
    split
    · rename_i hk648
      have hb : 2*sourceIndex (k/2)+k%2<658 := by unfold sourceIndex;split_ifs <;>omega
      exact (bm _).trans (ha.read _ hb)
    · split
      · exact (bm _).trans (ha.read _ (by omega))
      · dsimp only
        rw [bm,ha.read 657 (by omega)]
  have hux6 : u.getReg .x6=Xw (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) 657) (s.getMem 0x66000) := by
    rw [ux6,hh,bm,ha.read 657 (by omega)]
  obtain ⟨c,uc,cp,cr,cm⟩:=entry_steps hc.entry u up
  obtain ⟨v,cv,vp,vx5,vw⟩:=post_steps hc.post c cp
  have hc1 : CodeAt im (pcOf 20744) [0x513] := by
    rcases hc.halt with ⟨h1,h2,h3,rest,hrest⟩
    refine ⟨h1,h2,by simp_all,0x73::rest,?_⟩
    exact hrest
  let t:=haltRun.res.toState v
  have vt : Steps im v 1 1 t := symRun_sound haltRun hc1 v vp (by simp [haltRun.res,rv_simp])
  refine ⟨preCost+1+n+1+58+1,by unfold preCost;omega,t,
    (((((sa.trans ab).trans bu).trans uc).trans cv).trans vt),?_,?_,?_,?_⟩
  · simp [t,haltRun.res,rv_simp]
  · have : t.getReg .x5=v.getReg .x5 := by simp [t,haltRun.res,rv_simp]
    rw [this,vx5]
  · simp [t,haltRun.res,rv_simp]
  · intro k hk
    change v.getMem _=_
    rw [vw k hk,cr,hux6]
    apply postWord_congr _ _ k hk
    intro j hj
    rw [cm]
    exact huw j hj

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rawIndex (k : Nat) : Nat :=
  if k<13 then k else if k<38 then k+1 else if k<63 then k+2 else if k<88 then k+3
  else if k<114 then k+4 else k+26

def fullIndex (k : Nat) : Nat := if k<176 then k else k+1

def wordIndex (k : Nat) : Nat :=
  if k<236 then k else 280+2*cpIdxT ((k-236)/2)+(k-236)%2

theorem preWord_eq (read : Nat→Word) (k : Nat) : preWord read k=read (wordIndex k) := by
  unfold preWord wordIndex
  split <;>rfl

theorem indices (k i : Nat) (hk : k<324) (hi : i<2) :
    wordIndex (2*sourceIndex k+i)=2*rawIndex (fullIndex k)+i := by
  unfold wordIndex sourceIndex rawIndex fullIndex cpIdxT
  split_ifs <;>omega

def RawAt (s : MachineState) (sig : SharedSignature) : Prop :=
  ∀k,k<325 → DigAt s (SIG+16*rawIndex k) ((sigDigests sig).getD k 0)

theorem RawAt.word {s : MachineState} {sig : SharedSignature} (h : RawAt s sig)
    (k i : Nat) (hk : k<325) (hi : i<2) :
    s.getMem (BitVec.ofNat 64 (SIG+8*(2*rawIndex k+i)))=
      ((sigDigests sig).getD k 0).extractLsb' (64*i) 64 := by
  have hd:=h k hk
  have he : i=0 ∨ i=1 := by omega
  rcases he with rfl|rfl
  · simpa [←Nat.mul_assoc] using hd.1
  · simpa [Nat.mul_add,Nat.add_assoc,←Nat.mul_assoc] using hd.2

def sigWord (sig : SharedSignature) (k : Nat) : Word :=
  if k<648 then ((sigDigests sig).getD (fullIndex (k/2)) 0).extractLsb' (64*(k%2)) 64
  else if k=648 then ((sigDigests sig).getD 176 0).extractLsb' 0 64
  else (((sigDigests sig).getD 176 0).extractLsb' 64 64<<<40)>>>40

theorem packedWord_raw {s : MachineState} {sig : SharedSignature} (h : RawAt s sig) (k : Nat) (hk : k<650) :
    packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) k=sigWord sig k := by
  unfold packedWord sigWord
  split
  · rename_i hk648
    rw [preWord_eq,indices _ _ (by omega) (by omega)]
    exact h.word _ _ (by unfold fullIndex;split_ifs <;>omega) (by omega)
  · split
    · rw [preWord_eq]
      have hm:=h.word 176 0 (by omega) (by omega)
      change s.getMem (BitVec.ofNat 64 (SIG+8*404))=_ at hm
      rw [show wordIndex 656=404 by decide,hm]
    · rw [preWord_eq]
      have hm:=h.word 176 1 (by omega) (by omega)
      change s.getMem (BitVec.ofNat 64 (SIG+8*405))=_ at hm
      rw [show wordIndex 657=405 by decide,hm]

theorem Xw_raw {s : MachineState} {sig : SharedSignature} (h : RawAt s sig) (hint : Word) :
    Xw (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) 657) hint=
      Xw (((sigDigests sig).getD 176 0).extractLsb' 64 64) hint := by
  rw [preWord_eq]
  have hm:=h.word 176 1 (by omega) (by omega)
  change s.getMem (BitVec.ofNat 64 (SIG+8*405))=_ at hm
  rw [show wordIndex 657=405 by decide,hm]

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

/-! ## The post-pass output is the 5,195-byte `SharedCodec.sigBC` (T51) -/

theorem xField_testBit (s : SharedSignature) (i : Nat) :
    (xField s).testBit i = if i < 16 then ((sigDigests s).getD 176 0).toNat.testBit (i+88)
      else decide (i - 16 < 13) && s.policyHints.toNat.testBit (i-16) := by
  unfold xField
  rw [show ∀ a b : Nat, a + b * 2^16 = 2^16 * b + a from fun a b => by ring,
    Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  split
  · rename_i h; rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [h]
  · rw [Nat.testBit_mod_two_pow]

theorem packD_bit (j : Nat) (d : Digest) (x i : Nat) (hi : i < 128) (hj : topZeroBits j ≤ 128) :
    (packD j d x).getLsbD i = if i < 128 - topZeroBits j then d.getLsbD i
      else (x / 2 ^ xOff j).testBit (i - (128 - topZeroBits j)) := by
  unfold packD
  rw [BitVec.getLsbD_ofNat, show ∀ a b : Nat, a + b * 2^(128-topZeroBits j) = 2^(128-topZeroBits j) * b + a from
    fun a b => by ring, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  simp only [hi, decide_true, Bool.true_and]
  split
  · rename_i h; rw [Nat.testBit_mod_two_pow]; simp [h, BitVec.testBit_toNat]
  · rw [Nat.testBit_mod_two_pow]; simp; omega

theorem topZeroBits_le (j : Nat) (h : j ≤ 10) : topZeroBits j ≤ 7 := by
  interval_cases j <;> decide

theorem bT_eq (j : Nat) (h3 : 3 ≤ j) (h10 : j ≤ 10) : bT j = topZeroBits j := by
  interval_cases j <;> decide

theorem oT_eq (j : Nat) (h3 : 3 ≤ j) (h10 : j ≤ 10) : oT j = xOff j := by
  interval_cases j <;> decide

theorem packD_low (j : Nat) (hj : j ≤ 10) (d : Digest) (x : Nat) :
    (packD j d x).extractLsb' 0 64 = d.extractLsb' 0 64 := by
  have hb := topZeroBits_le j hj
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add]
  rw [packD_bit j d x i (by omega) (by omega), if_pos (by omega)]

theorem packD_zero (j : Nat) (hb : topZeroBits j = 0) (d : Digest) (x : Nat) : packD j d x = d := by
  unfold packD
  rw [hb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt d.isLt]

theorem packD_high (j : Nat) (hj : 3 ≤ j ∧ j ≤ 10) (d : Digest) (x : Nat) (X : Word)
    (hX : ∀ i, i < bT j → X.getLsbD (oT j + i) = (x / 2 ^ xOff j).testBit i) :
    (packD j d x).extractLsb' 64 64 = postNode j (d.extractLsb' 64 64) X := by
  have hb := bT_eq j hj.1 hj.2
  have hb7 : bT j ≤ 7 := by rw [hb]; exact topZeroBits_le j hj.2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold postNode
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rw [packD_bit j d x (64+i) (by omega) (by omega), ← hb]
  by_cases hl : i < 64 - bT j
  · rw [if_pos (by omega)]
    simp only [show bT j + i < 64 by omega, show ¬ (bT j + i < bT j) by omega, show bT j + i - bT j = i by omega, hi,
      decide_true, decide_false, Bool.not_false, Bool.true_and]
    simp [hl]
  · rw [if_neg (by omega), show 64 + i - (128 - bT j) = i - (64 - bT j) by omega, ← hX _ (by omega)]
    simp [show ¬ (bT j + i < 64) by omega]
    intro _; omega

theorem Xw_bit (sib : Digest) (h : Word) (p : Nat) (hp : p < 29) :
    (Xw (sib.extractLsb' 64 64) h).getLsbD p = if p < 16 then sib.getLsbD (88 + p) else h.getLsbD (p - 16) := by
  unfold Xw
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  interval_cases p <;> simp

theorem sigBC_tail_div (sig : SharedSignature) :
    (sigBC sig).toNat / 2^(128*324) = ((sigDigests sig).getD 176 0).toNat % 2^88 := by
  have hD := SigGolfCandidate.T3M.digNat_lt (encList sig)
  rw [encList_length] at hD
  rw [sigBC_toNat, ClaudeWCT.W9.T3M.split_div _ _ _ hD]

theorem enc_digest_word (sig : SharedSignature) (k : Nat) (hk : k < 648) :
    (sigBC sig).extractLsb' (64*k) 64 = ((encList sig).getD (k/2) 0).extractLsb' (64*(k%2)) 64 := by
  have h:=congrArg (fun d : Digest=>d.extractLsb' (64*(k%2)) 64) (cDig_sigBC sig (k/2) (by omega))
  rw [cDig,extract_digest_word _ _ _ (by omega)] at h
  rw [show 128*(k/2)+64*(k%2)=64*k by omega] at h
  exact h

theorem enc_word (sig : SharedSignature) (hint : Word) (hh : hint.setWidth 16 = sig.policyHints)
    (k : Nat) (hk : k < 650) :
    postWord (sigWord sig) (Xw (((sigDigests sig).getD 176 0).extractLsb' 64 64) hint) k =
      (sigBC sig).extractLsb' (64*k) 64 := by
  unfold postWord
  split
  · rename_i h
    obtain ⟨h1,h2,h3⟩ := h
    rw [enc_digest_word sig k (by omega), encList_getD sig _ (by omega), if_pos (by omega),
      ClaudeWCT.W9.T3M.getD_eraseIdx, if_pos (by omega), show k%2 = 1 by omega,
      show (k/2) - 165 = (k-331)/2 by omega]
    have hs : sigWord sig k = ((sigDigests sig).getD (k/2) 0).extractLsb' 64 64 := by
      unfold sigWord fullIndex; rw [if_pos (by omega), if_pos (by omega), show k%2 = 1 by omega]
    rw [hs]
    refine (packD_high _ ⟨by omega, by omega⟩ _ _ _ ?_).symm
    have hj3 : 3 ≤ (k-331)/2 := by omega
    have hj10 : (k-331)/2 ≤ 10 := by omega
    generalize (k-331)/2 = j at *
    intro i hi
    have hlt : oT j + i < 29 := by interval_cases j <;> simp only [bT, oT] at hi ⊢ <;> omega
    rw [Xw_bit _ _ _ hlt, Nat.testBit_div_two_pow, xField_testBit, ← oT_eq j hj3 hj10]
    generalize oT j = o at *
    by_cases h16 : o + i < 16
    · rw [if_pos h16, if_pos (by omega), ← BitVec.testBit_toNat]
      congr 1; omega
    · rw [if_neg h16, if_neg (by omega), ← hh]
      simp only [show i + o - 16 < 13 by omega, decide_true, Bool.true_and, BitVec.testBit_toNat,
        BitVec.getLsbD_setWidth, show i + o - 16 < 16 by omega]
      congr 1; omega
  · rename_i hn
    by_cases hk648 : k < 648
    · rw [enc_digest_word sig k hk648, encList_getD sig _ (by omega)]
      unfold sigWord fullIndex
      rw [if_pos hk648]
      by_cases hp : 166 ≤ k/2 ∧ k/2 ≤ 175
      · rw [if_pos hp, ClaudeWCT.W9.T3M.getD_eraseIdx, if_pos (by omega), if_pos (by omega)]
        by_cases he : k % 2 = 0
        · rw [he, Nat.mul_zero, packD_low _ (by omega)]
        · have hk2 : k/2 - 165 = 1 ∨ k/2 - 165 = 2 := by omega
          rw [packD_zero _ (by rcases hk2 with h | h <;> rw [h] <;> decide)]
      · rw [if_neg hp, ClaudeWCT.W9.T3M.getD_eraseIdx]
        by_cases hq : k/2 < 176 <;> simp [hq]
    · by_cases h648 : k = 648
      · subst h648
        unfold sigWord
        simp only [show ¬ (648 < 648) by omega, if_false, if_true]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add]
        rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat,
          show 64*648+i = i + 128*324 by omega, ← Nat.testBit_div_two_pow, sigBC_tail_div, Nat.testBit_mod_two_pow]
        simp only [show i < 88 by omega, decide_true, Bool.true_and]
      · have h649 : k = 649 := by omega
        subst h649
        unfold sigWord
        simp only [show ¬ (649 < 648) by omega, show ¬ (649 = 648) by omega, if_false]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi,
          decide_true, Bool.true_and]
        rw [← BitVec.testBit_toNat (x := sigBC sig),
          show 64*649+i = (64+i) + 128*324 by omega, ← Nat.testBit_div_two_pow, sigBC_tail_div,
          Nat.testBit_mod_two_pow]
        by_cases hi24 : i < 24
        · simp [show 40 + i < 64 by omega, show 64 + i < 88 by omega, BitVec.testBit_toNat]
          try (intro _; omega)
        · simp [show ¬ (40 + i < 64) by omega, show ¬ (64 + i < 88) by omega]

theorem sl_readBuffer_foldl_mod (t : MachineState) (A n : Nat) : ∀ m, n ≤ m →
    (List.range m).foldl
        (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0 % 2 ^ (8 * n) =
      (List.range n).foldl
        (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0 % 2 ^ (8 * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega : 8 * n ≤ 8 * m)) _),
      Nat.add_zero, Nat.mod_mod, ih]

theorem sl_readBuffer_trunc (t : MachineState) (A n m : Nat) (h : n ≤ m) :
    readBuffer t A n = BitVec.ofNat (8 * n) (readBuffer t A m).toNat := by
  unfold readBuffer
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * n ≤ 8 * m)), sl_readBuffer_foldl_mod t A n m h]

theorem words_map (t : MachineState) (A : Nat) : ∀n,
    t.readWords (BitVec.ofNat 64 A) n=(List.range n).map (fun j=>t.getMem (BitVec.ofNat 64 (A+8*j)))
  | 0 => rfl
  | n+1 => by
    rw [readWords_add,words_map t A n,readWords_one,List.range_succ,List.map_append]
    rfl

theorem sl_readBuffer_words (t : MachineState) (A n m : Nat) (b : BitVec (8*n))
    (hal : A%8=0) (haddr : A+8*m<2^64) (hsize : n≤8*m)
    (hw : ∀k,k < m → t.getMem (BitVec.ofNat 64 (A+8*k))=b.extractLsb' (64*k) 64) :
    readBuffer t A n=b := by
  let b' : BitVec (8*(8*m)):=b.setWidth _
  have hw' : t.readWords (BitVec.ofNat 64 A) m=wordsOf (SphincsSecurity.bytesLE (8*m) b') := by
    rw[words_map,wordsOf_bytesLE]
    apply List.map_congr_left
    intro k hk
    rw[show b'.extractLsb' (64*k) 64=b.extractLsb' (64*k) 64 from
      BitVec.extractLsb'_setWidth_of_le (by have h:=List.mem_range.mp hk;omega)]
    exact hw k (List.mem_range.mp hk)
  have h:=readBuffer_of_words t A m (SphincsSecurity.bytesLE (8*m) b') hal haddr
    (by rw[SphincsSecurity.bytesLE_length]) hw'
  rw[readLE_bytesLE] at h
  rw[sl_readBuffer_trunc t A n (8*m) hsize,h]
  apply BitVec.eq_of_toNat_eq
  simp only[BitVec.toNat_ofNat,BitVec.toNat_setWidth,b',Nat.mod_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8*n≤8*(8*m))),
    Nat.mod_eq_of_lt b.isLt]

theorem hint_shift (w : Word) : w<<<48=(w.setWidth 16).setWidth 64<<<48 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth]
  by_cases hj48 : j<48
  · simp [hj,hj48]
  · simp [hj,hj48,show j-48<64 by omega,show j-48<16 by omega]

theorem serialize_good {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 540)
    (sig : SharedSignature) (hraw : RawAt s sig)
    (hh : (s.getMem 0x66000).setWidth 16=sig.policyHints) :
    ∃n≤8280,∃t,Steps im s n n t ∧ t.pc=pcOf 20745 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t SIG 5195=sigBC sig := by
  obtain ⟨n,hn,t,st,tp,t5,t10,tw⟩:=full_readout hc s hp
  refine ⟨n,hn,t,st,tp,t5,t10,?_⟩
  apply sl_readBuffer_words t SIG 5195 650 (sigBC sig) (by unfold SIG; decide) (by unfold SIG; decide) (by omega)
  intro k hk
  rw [tw k hk, Xw_raw hraw, postWord_congr _ (fun j hj => packedWord_raw hraw j hj) k hk]
  exact enc_word sig _ hh k hk

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem pair_rawIndex (p : Fin 4) (j : Nat) (hj : j<25) :
    rawIndex (1+25*p.val+j)=1+26*p.val+j+(if j<12 then 0 else 1) := by
  fin_cases p <;>simp only [Fin.reduceFinMk] <;>unfold rawIndex <;>split_ifs <;>omega

theorem rawAt_of_layout (s : MachineState) (sig : SharedSignature)
    (hrho : DigAt s SIG sig.rho)
    (hpairs : ∀p : Fin 4,∀j,j<25 →
      DigAt s (SIG+16*(1+26*p.val+j+(if j<12 then 0 else 1))) ((pairList (sig.forest.pairs p)).getD j 0))
    (hsingle : ∀j,j<13 → DigAt s (SIG+16*(105+j)) ((singletonList sig.forest.singleton).getD j 0))
    (hlayers : ∀lay : Layer,∀j,j<chainCount lay+height lay →
      DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+26+j)) ((layerList sig lay).getD j 0)) : RawAt s sig := by
  intro k hk
  by_cases h0 : k=0
  · subst k
    rw [ClaudeWCT.W9.T3M.SharedCodec.sigDigests_rho]
    simpa [rawIndex] using hrho
  by_cases hp : k<101
  · let p : Fin 4 := ⟨(k-1)/25,by omega⟩
    let j:= (k-1)%25
    have hj : j<25 := Nat.mod_lt _ (by omega)
    have he : k=1+25*p.val+j := by dsimp [p,j];omega
    rw [he,pair_rawIndex p j hj,sigDigests_pair sig p j hj]
    exact hpairs p j hj
  by_cases hs : k<114
  · have he : rawIndex k=k+4 := by unfold rawIndex;split_ifs <;>omega
    rw [he,show k=101+(k-101) by omega,sigDigests_singleton sig _ (by omega)]
    convert hsingle (k-101) (by omega) using 1 <;>congr 1 <;>omega
  · have he : rawIndex k=k+26 := by unfold rawIndex;split_ifs <;>omega
    rw [he]
    have key (lay : Layer) (j : Nat) (hj : j<chainCount lay+height lay) (heq : k=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+j) :
        DigAt s (SIG+16*(k+26)) ((sigDigests sig).getD k 0) := by
      rw [heq,sigDigests_layer sig lay j hj,show ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+j+26=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+26+j by omega]
      exact hlayers lay j hj
    by_cases h1 : k<177
    · exact key 0 (k-114) (by change k-114<51+12;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
    by_cases h2 : k<227
    · exact key 1 (k-177) (by change k-177<43+7;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
    by_cases h3 : k<276
    · exact key 2 (k-227) (by change k-227<43+6;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
    · exact key 3 (k-276) (by change k-276<43+6;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem pair_layout (s : MachineState) (p : Fin 4) (op : PairOpening)
    (hfv : ∀i : Fin 6,DigAt s (SIG+16*(1+26*p.val+i.val)) (op.firstValues i))
    (hfp : ∀i : Fin 6,DigAt s (SIG+16*(7+26*p.val+i.val)) (op.firstPath i))
    (hsv : ∀i : Fin 6,DigAt s (SIG+16*(14+26*p.val+i.val)) (op.secondValues i))
    (hsp : ∀i : Fin 7,DigAt s (SIG+16*(20+26*p.val+i.val)) (op.secondPath i))
    (j : Nat) (hj : j<25) :
    DigAt s (SIG+16*(1+26*p.val+j+(if j<12 then 0 else 1))) ((pairList op).getD j 0) := by
  by_cases h6 : j<6
  · rw [if_pos (by omega)]
    rw [show (pairList op).getD j 0=op.firstValues ⟨j,h6⟩ from pairList_firstValue op ⟨j,h6⟩]
    simpa using hfv ⟨j,h6⟩
  by_cases h12 : j<12
  · rw [if_pos h12]
    have he : j=6+(j-6) := by omega
    rw [he,pairList_firstPath op ⟨j-6,by omega⟩]
    convert hfp ⟨j-6,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega
  by_cases h18 : j<18
  · rw [if_neg h12]
    have he : j=12+(j-12) := by omega
    rw [he,pairList_secondValue op ⟨j-12,by omega⟩]
    convert hsv ⟨j-12,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega
  · rw [if_neg h12]
    have he : j=18+(j-18) := by omega
    rw [he,pairList_secondPath op ⟨j-18,by omega⟩]
    convert hsp ⟨j-18,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega

theorem singleton_layout (s : MachineState) (op : SingletonOpening)
    (hv : ∀i : Fin 6,DigAt s (SIG+16*(105+i.val)) (op.values i))
    (hp : ∀i : Fin 7,DigAt s (SIG+16*(111+i.val)) (op.path i))
    (j : Nat) (hj : j<13) : DigAt s (SIG+16*(105+j)) ((singletonList op).getD j 0) := by
  unfold singletonList
  by_cases h6 : j<6
  · rw [getD_append_left' (by simp;omega),getD_ofFn' _ j h6]
    exact hv ⟨j,h6⟩
  · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (j-6) (by omega)]
    convert hp ⟨j-6,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega

theorem layer_layout (s : MachineState) (sig : SharedSignature) (lay : Layer)
    (hv : ∀i : Fin (chainCount lay),DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+26+i.val)) ((sig.layers lay).values i))
    (hp : ∀i : Fin (height lay),DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+26+chainCount lay+i.val)) ((sig.layers lay).path i))
    (j : Nat) (hj : j<chainCount lay+height lay) :
    DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+26+j)) ((ClaudeWCT.W9.T3M.SharedCodec.layerList sig lay).getD j 0) := by
  unfold ClaudeWCT.W9.T3M.SharedCodec.layerList
  by_cases hc : j<chainCount lay
  · rw [getD_append_left' (by simp;omega),getD_ofFn' _ j hc]
    exact hv ⟨j,hc⟩
  · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (j-chainCount lay) (by omega)]
    convert hp ⟨j-chainCount lay,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem forest_pair_layout (s : MachineState) (forest : ForestOpening)
    (hv : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i))
    (hp : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l))
    (p : Fin 4) (j : Nat) (hj : j<25) :
    DigAt s (SIG+16*(1+26*p.val+j+(if j<12 then 0 else 1))) ((pairList (forest.pairs p)).getD j 0) := by
  apply pair_layout s p (forest.pairs p) _ _ _ _ j hj
  · intro i
    have h:=hv ⟨2*p.val,by omega⟩ i
    fin_cases p <;>simpa [SharedCoordinate.openingValues,slotV,Nat.mul_add,Nat.add_assoc] using h
  · intro i
    have h:=hp ⟨2*p.val,by omega⟩ i.val (by fin_cases p <;>simpa [SharedPath.levels] using i.isLt)
    fin_cases p <;>simpa [SharedCoordinate.openingPath,SharedPath.target,slotV,Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt i.isLt] using h
  · intro i
    have h:=hv ⟨2*p.val+1,by omega⟩ i
    fin_cases p <;>simpa [SharedCoordinate.openingValues,slotV,Nat.mul_add,Nat.add_assoc] using h
  · intro i
    have h:=hp ⟨2*p.val+1,by omega⟩ i.val (by fin_cases p <;>simpa [SharedPath.levels] using i.isLt)
    fin_cases p <;>simpa [SharedCoordinate.openingPath,SharedPath.target,slotV,Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt i.isLt] using h

theorem forest_singleton_layout (s : MachineState) (forest : ForestOpening)
    (hv : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i))
    (hp : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l))
    (j : Nat) (hj : j<13) : DigAt s (SIG+16*(105+j)) ((singletonList forest.singleton).getD j 0) := by
  apply singleton_layout s forest.singleton _ _ j hj
  · intro i
    simpa [SharedCoordinate.openingValues,slotV,Nat.mul_add,Nat.add_assoc] using hv 8 i
  · intro i
    have h:=hp 8 i.val (by simpa [SharedPath.levels] using i.isLt)
    simpa [SharedCoordinate.openingPath,SharedPath.target,slotV,Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt i.isLt] using h

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedRootBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

abbrev enc : Nat := 0x20260

def words : List (BitVec 32) := bv_list% 32 [0x20eb7,0x3a0e8e93,0x20f37,0x260f0f13,0xeb303,0x8eb383,0x6f3023,0x7f3423,0x36d1706f]
sym_block block := symRun {noAlias:=true} words (pcOf 370) 100

theorem steps {im : Image} (hc : CodeAt im (pcOf 370) words) (s : MachineState) (hp : s.pc=pcOf 370) :
    ∃t,Steps im s 9 9 t ∧ t.pc=pcOf 24661 ∧
      t.getMem (BitVec.ofNat 64 enc)=s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (enc+8))=s.getMem (BitVec.ofNat 64 (FOUT+8)) ∧
      RegsExcept s t [.x6,.x7,.x29,.x30] ∧ Frame s t (fun A=>A=enc ∨ A=enc+8) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [block.res,rv_simp]
  · simp [block.res,rv_simp,enc,FOUT]
  · simp [block.res,rv_simp,enc,FOUT]
  · intro r hr;cases r <;>simp at hr <;>rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res]
    t3n [enc,FOUT]
    repeat rw [if_neg (by unfold enc at hn;omega)]

theorem installed_code : CodeAt Images.signImage (pcOf 370) words := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;>decide +kernel

end ClaudeWCT.W9.Machine.Sign.SharedRootBridge
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def LayerFields (s : MachineState) (pieces : List SigGolfCandidate.T3.Pieces) : Prop :=
  ∀lay : Layer,
    (∀i,i<chainCount lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+i)) ((pieces.getD lay.val ([],[])).1.getD i 0)) ∧
    (∀j,j<height lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+chainCount lay+j)) ((pieces.getD lay.val ([],[])).2.getD j 0))

theorem stored_layer_fields {s : MachineState} {lay : Layer} {pieces : SigGolfCandidate.T3.Pieces}
    (hl : lay≠0) (hn : pieces.1.length=43) (hh : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) :
    (∀i,i<chainCount lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+i)) (pieces.1.getD i 0)) ∧
    (∀j,j<height lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+chainCount lay+j)) (pieces.2.getD j 0)) := by
  constructor
  · intro i hi
    have hi' : i<43 := by fin_cases lay <;>simp_all [chainCount]
    have h':=h.1 i (by omega)
    fin_cases lay <;>simp_all [SharedRootControl.sigBase,SigGolfCandidate.T3M.layIdx,SIG,Nat.mul_add,←Nat.add_assoc]
  · intro j hj
    have h':=h.2 j (by omega)
    fin_cases lay <;>simp_all [SharedRootControl.sigBase,SigGolfCandidate.T3M.layIdx,SIG,chainCount,Nat.mul_add,←Nat.add_assoc]

theorem completed_layer_fields {index : Nat} {p : PreparedRoots} {a : Choices} {top : SigGolfCandidate.T3.Pieces}
    {s : MachineState} (h : Completed index p a top s) : LayerFields s (layersValue index p a top).pieces := by
  intro lay
  fin_cases lay
  · constructor
    · intro i hi
      simpa [layersValue,SigGolfCandidate.T3M.layIdx,Nat.mul_add,←Nat.add_assoc] using h.topValues i hi
    · intro j hj
      simpa [layersValue,SigGolfCandidate.T3M.layIdx,chainCount,Nat.mul_add,←Nat.add_assoc] using h.topPath j hj
  · exact stored_layer_fields (by decide) (prepared_length 1 (by decide) _ _ _).1
      (prepared_length 1 (by decide) _ _ _).2 h.one
  · exact stored_layer_fields (by decide) (prepared_length 2 (by decide) _ _ _).1
      (prepared_length 2 (by decide) _ _ _).2 h.two
  · exact stored_layer_fields (by decide) (prepared_length 3 (by decide) _ _ _).1
      (prepared_length 3 (by decide) _ _ _).2 h.three

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem shared_layIdx_eq (lay : Layer) :
    SigGolfCandidate.T3M.layIdx lay=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+26 := by
  fin_cases lay <;>rfl

theorem assembled_raw (s : MachineState) (rho : Digest) (hints : BitVec 16)
    (forest : ForestOpening) (pieces : List SigGolfCandidate.T3.Pieces)
    (hrho : DigAt s SIG rho)
    (hv : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i))
    (hp : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l))
    (hl : LayerFields s pieces) :
    RawAt s ⟨rho,hints,forest,fun lay=>piecesSignature lay (pieces.getD lay.val ([],[]))⟩ := by
  apply rawAt_of_layout s _ hrho
  · exact forest_pair_layout s forest hv hp
  · exact forest_singleton_layout s forest hv hp
  · intro lay j hj
    apply layer_layout s _ lay _ _ j hj
    · intro i
      rw [←shared_layIdx_eq]
      exact (hl lay).1 i.val i.isLt
    · intro i
      rw [←shared_layIdx_eq]
      exact (hl lay).2 i.val i.isLt

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def WriteArea (A : Nat) : Prop := (SIG+16≤A ∧ A<SIG+1888) ∨ (0x50000≤A ∧ A<0x68000)

theorem coordinate_write_area {c A : Nat} (hc : c<9) (h : coordinateW c A) : WriteArea A := by
  have hn : SharedFinish.nwords c≤8 := by unfold SharedFinish.nwords;split_ifs <;>omega
  have hlevels : SharedPath.levels c≤7 := SharedPath.levels_bound c
  have htarget : 0x50000≤SharedFinish.target c ∧ SharedFinish.target c+64<0x68000 := by
    unfold SharedFinish.target
    split_ifs <;> (try simp only [FORW]) <;> omega
  unfold coordinateW allWrites writes FinalWrites at h
  rcases h with h|((h|h)|(h|h|h))
  · unfold SharedReuse.coefW WriteArea at *
    simp only [PRIVW,COEF,SIG] at *
    omega
  · unfold loopW bodyW WriteArea at *
    simp only [PRIVW,PAIRW,CHAINW,LEAFW,HEAPW,SCREND,slotV,SIG] at *
    omega
  · unfold treeW WriteArea at *
    simp only [NODEW,NOUTW,HEAPW,SIG] at *
    omega
  · rcases h with ⟨k,hk,rfl⟩
    right
    omega
  · left
    simp only [SharedPath.target,slotV] at h
    omega
  · left
    simp only [SharedEnd.target,slotP] at h
    omega

theorem ClosedPost.write_frame {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : ClosedPost sk a s rv t) : Frame s t (fun A=>WriteArea A ∨ FinalW A) := by
  apply h.frame.mono
  intro A hA hw
  rcases hw with hw|hw|hw|hw|⟨c,hc,hw⟩|hw
  · left;right;subst A;decide
  · left;right;subst A;decide
  · left;right;subst A;decide
  · left;right;subst A;decide
  · exact Or.inl (coordinate_write_area hc hw)
  · exact Or.inr hw

end ClaudeWCT.W9.Machine.Sign.SharedCoordinate
namespace ClaudeWCT.W9.Machine.Sign.SharedNonceJump
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def words : List (BitVec 32) := [0x6bd1506f]
sym_block block := symRun {noAlias:=true} words (pcOf 153) 10

theorem steps {im : Image} (hc : CodeAt im (pcOf 153) words) (s : MachineState) (hp : s.pc=pcOf 153) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 22600 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr;cases r <;>rfl
  · intro A hA hn;rfl

theorem installed_code : CodeAt Images.signImage (pcOf 153) words := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;>decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedNonceJump
namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem sign_steps_free {im : Image} (hc : CodeAt im (pcOf 22755) signSuffixCode)
    (s : MachineState) (hp : s.pc=pcOf 22755) (h28 : s.getReg .x28=0x20000) :
    ∃t,Steps im s 7 7 t ∧ t.pc=pcOf 11175 ∧
      t.getReg .x22=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      RegsExcept s t [.x22,.x28] ∧ Frame s t (fun A=>A=0x20550) := by
  refine ⟨_,symRun_sound signRun hc s hp ?_,?_,?_,?_,?_,?_⟩
  · simp [signRun.res,rv_simp,h28,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [signRun.res,rv_simp,h28]
  · simp [signRun.res,rv_simp,h28]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,signRun.res]
    t3n [h28]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA),if_neg hn]

sym_block failJump := symRun {noAlias:=true} [0xcccea06f] (pcOf 22764) 2

theorem sign_failure_steps {im : Image}
    (hc : CodeAt im (pcOf 22764) [0xcccea06f])
    (hf : CodeAt im (pcOf 543) failureCode) (s : MachineState) (hp : s.pc=pcOf 22764) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      Frame s t (fun _=>False) := by
  have hs : Steps im s 1 1 (failJump.res.toState s) :=
    symRun_sound failJump hc s hp (by simp [failJump.res,rv_simp])
  obtain ⟨t,st,pt,h5,h10,rt,ft⟩:=failure_steps false hf (failJump.res.toState s) rfl
  refine ⟨t,hs.trans st,pt,h5,h10,?_⟩
  have ff : Frame s (failJump.res.toState s) (fun _=>False) :=fun A _ _=>rfl
  exact (ff.trans ft).mono (fun _ _ h=>h.elim id id)
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Search
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem frame_result (s : MachineState) : Frame s (block.res.toState s) (fun A=>A=TOP_DATA+624) := by
  intro A hA hn
  simp only [Result.toState_getMem,block.res];t3n []
  rw [if_neg (by unfold TOP_DATA at hn;omega)]

theorem base_result {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat} {s : MachineState}
    (hb : Base (cfFlag:=cfFlag) sk cache s) : Base (cfFlag:=0) sk cache (block.res.toState s) := by
  have ff:=frame_result s
  have ht:=tables_result s cfFlag hb.table hb.cf hb.reward hb.t51
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,ht.1,ht.2.1,ht.2.2.1,hb.zt.frame ff (fun r hr => by
    unfold SigGolfCandidate.T3M.Search.ZeroCap.ZT TOP_DATA; simp only [show (543:Nat) ≠ 354 by decide, if_false]; omega),ht.2.2.2⟩
  · exact hb.x5
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p0
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p8
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p32
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p40
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p48
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p56
  · intro k hk
    rw [ff.get (by unfold REGION;omega) (by unfold REGION TOP_DATA;omega)]
    exact hb.region k hk
  · intro A hA hn
    rw [ff.get hA (by unfold NeverW at hn;unfold TOP_DATA;sg_omega)]
    exact hb.zero A hA hn

theorem steps_base {im : Image} (hc : CodeAt im (pcOf 24661) code)
    {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat}
    (s : MachineState) (hp : s.pc=pcOf 24661) (hb : Base (cfFlag:=cfFlag) sk cache s) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 22100 ∧ Base (cfFlag:=0) sk cache t ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=TOP_DATA+624) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,base_result hb,?_,frame_result s⟩
  · simp [block.res,rv_simp]
  · intro r hr;cases r <;>first | exact (hr (by decide)).elim | rfl
end SigGolfCandidate.T3M.Sign.SharedFlagInit
namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def signTierHeadCode : List (BitVec 32) := signTierCode.take 2
def signTierZeroCode : List (BitVec 32) := (signTierCode.drop 2).take 1
def signTierBodyCode : List (BitVec 32) := signTierCode.drop 3
sym_block signTierHead := symRun {noAlias:=true} signTierHeadCode (pcOf 24723) 20
sym_block signTierZero := symRun {noAlias:=true} signTierZeroCode (pcOf 24725) 20
sym_block signTierBody := symRun {noAlias:=true} signTierBodyCode (pcOf 24726) 40

theorem signTier_headAt {im : Image} (h : CodeAt im (pcOf 24723) signTierCode) :
    CodeAt im (pcOf 24723) signTierHeadCode := by
  exact ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 0) h (by decide) (by decide)
theorem signTier_zeroAt {im : Image} (h : CodeAt im (pcOf 24723) signTierCode) :
    CodeAt im (pcOf 24725) signTierZeroCode := by
  simpa using ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 2) h (by decide) (by decide)
theorem signTier_bodyAt {im : Image} (h : CodeAt im (pcOf 24723) signTierCode) :
    CodeAt im (pcOf 24726) signTierBodyCode := by
  simpa using ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 3) h (by decide) (by decide)

theorem signTier_head_steps {im : Image} (hcode : CodeAt im (pcOf 24723) signTierHeadCode)
    (s : MachineState) (hp : s.pc = pcOf 24723) (j : Nat) (hj : j ≤ 777)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (if j < 773 then 24725 else 24726) ∧
      t.getReg .x22 = BitVec.ofNat 64 j + BitVec.ofNat 64 (2^64-773) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound signTierHead hcode s hp (by simp [signTierHead.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,signTierHead.res,E.eval,CmpOp.eval,rv_simp,h20]
    rw [SharedDigestBoundary.tier_slt_all ⟨j,by omega⟩]
    by_cases h : j < 773 <;> simp [h]
  · simp [signTierHead.res,rv_simp,h20]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A _ _;rfl

theorem signTier_zero_steps {im : Image} (hcode : CodeAt im (pcOf 24725) signTierZeroCode)
    (s : MachineState) (hp : s.pc = pcOf 24725) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 24726 ∧ t.getReg .x22 = 0 ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound signTierZero hcode s hp (by simp [signTierZero.res,rv_simp]),
    rfl,by simp [signTierZero.res,rv_simp],?_,fun _ _ _ => rfl⟩
  intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl

theorem signTier_body_steps {im : Image} (hcode : CodeAt im (pcOf 24726) signTierBodyCode)
    (s : MachineState) (hp : s.pc = pcOf 24726) (extra : Nat) (he : extra ≤ 4)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 extra) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 22755 ∧ t.getReg .x28 = 0x20000 ∧
      SigGolfCandidate.T3M.Sign.SharedTier.At extra t ∧
      RegsExcept s t [.x22,.x28] ∧
      Frame s t (fun A => A=0x202c0 ∨ A=0x202c8 ∨ A=0x66028) := by
  refine ⟨_,symRun_sound signTierBody hcode s hp
    (by simp [signTierBody.res,rv_simp,h22,accessValid_iff,MEMORY_BYTES];omega),
    rfl,by simp [signTierBody.res,rv_simp],?_,?_,?_⟩
  · constructor
    · simp only [Result.toState_getMem,signTierBody.res]
      t3n [h22]
      simp [BitVec.ofNat_add_ofNat]
    · simp only [Result.toState_getMem,signTierBody.res]
      t3n [h22]
      simp [BitVec.ofNat_add_ofNat]
    · simp only [Result.toState_getMem,signTierBody.res]
      t3n [h22]
      simp [BitVec.ofNat_add_ofNat]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,signTierBody.res]
    t3n [h22]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    simp only [if_neg (by omega)]

theorem signTier_jump_steps {im : Image} (hcode : CodeAt im (pcOf 22754) signCode)
    (s : MachineState) (hp : s.pc = pcOf 22754) :
    Steps im s 1 1 (s.setPC (pcOf 24723)) := by
  have hj : CodeAt im (pcOf 22754) [0x6c50106f] := by
    exact ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 0) hcode
      (by decide) (by decide)
  exact ClaudeWCT.W9.Machine.Expand.jal_x0_step (imm := 7876) hj (by rfl) (by decide) s hp

theorem signTier_steps {im : Image} (hs : CodeAt im (pcOf 22754) signCode)
    (htier : CodeAt im (pcOf 24723) signTierCode) (s : MachineState)
    (hp : s.pc = pcOf 22754) (j : Nat) (hj : j ≤ 777)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 14 ∧ t.pc = pcOf 22755 ∧
      t.getReg .x28 = 0x20000 ∧
      SigGolfCandidate.T3M.Sign.SharedTier.At (j-773) t ∧
      RegsExcept s t [.x22,.x28] ∧
      Frame s t (fun A => A=0x202c0 ∨ A=0x202c8 ∨ A=0x66028) := by
  let a := s.setPC (pcOf 24723)
  have sa := signTier_jump_steps hs s hp
  have ra : RegsExcept s a [] := fun _ _ => rfl
  have fa : Frame s a (fun _ => False) := fun _ _ _ => rfl
  obtain ⟨b,ab,bp,b22,br,bf⟩ := signTier_head_steps (signTier_headAt htier) a rfl j hj
    (by simpa [a] using h20)
  by_cases hlow : j < 773
  · have bp' : b.pc = pcOf 24725 := by simpa [hlow] using bp
    obtain ⟨c,bc,cp,c22,cr,cf⟩ := signTier_zero_steps (signTier_zeroAt htier) b bp'
    have he : j-773=0 := by omega
    obtain ⟨t,ct,tp,t28,ttier,tr,tf⟩ := signTier_body_steps (signTier_bodyAt htier) c cp (j-773)
      (by omega) (by simpa [he] using c22)
    refine ⟨t,14,((sa.trans ab).trans bc).trans ct,by decide,tp,t28,ttier,?_,?_⟩
    · exact (((ra.trans br).trans cr).trans tr).mono (by simp)
    · exact (((fa.trans bf).trans cf).trans tf).mono (by tauto)
  · have bp' : b.pc = pcOf 24726 := by simpa [hlow] using bp
    have bx22 : b.getReg .x22 = BitVec.ofNat 64 (j-773) := by
      have hslt : BitVec.slt (BitVec.ofNat 64 j + BitVec.ofNat 64 (2^64-773)) (0#64) = false := by
        simpa [hlow] using SharedDigestBoundary.tier_slt_all ⟨j,by omega⟩
      have he := SharedDigestBoundary.tier_extra_word j hj
      rw [hslt] at he
      simp only [if_false] at he
      exact b22.trans he
    obtain ⟨t,bt,tp,t28,ttier,tr,tf⟩ := signTier_body_steps (signTier_bodyAt htier) b bp' (j-773)
      (by omega) bx22
    refine ⟨t,13,(sa.trans ab).trans bt,by decide,tp,t28,ttier,?_,?_⟩
    · exact ((ra.trans br).trans tr).mono (by simp)
    · exact ((fa.trans bf).trans tf).mono (by tauto)

def JoinedPost (im : Image) (s : MachineState) : Option (BitVec 32×BitVec 256)→MachineState→Prop
  | none,t => t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)
  | some (c,a),t => c.toNat<2^21 ∧ SharedForest.digestAccepted a=true ∧
      t.pc=pcOf 11175 ∧ t.getReg .x5=0 ∧
      t.getReg .x22=BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      t.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) ∧ OutAt t NBUF a ∧
      SharedForest.conditionalExtra a ≤ 4 ∧
      SigGolfCandidate.T3M.Sign.SharedTier.At (SharedForest.conditionalExtra a) t ∧
      Frame s t (fun A=>SharedDigest.writes A ∨ A=0x20550 ∨
        A=SigGolfCandidate.T3M.Search.EOUT+32 ∨ A=SigGolfCandidate.T3M.Search.EOUT+40 ∨ A=0x66028)

theorem search_to_forest {im : Image} {sk : BitVec 256}
    (hl : LookOK im (SharedDigest.look false))
    (hs : CodeAt im (pcOf 22754) signCode)
    (htier : CodeAt im (pcOf 24723) signTierCode)
    (hj : CodeAt im (pcOf 22764) [0xcccea06f])
    (hf : CodeAt im (pcOf 543) failureCode)
    (he : CodeAt im (pcOf 545) [0x73])
    {s : MachineState} {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message}
    (hp : SharedDigest.Pre false rho msg s) (hpc : s.pc=pcOf 22600) :
    TBSim im sk s (2^21*200+33) (SharedForest.sharedDigestSearch rho msg 0 (2^21)) (JoinedPost im s) := by
  rw [←bind_pure (SharedForest.sharedDigestSearch rho msg 0 (2^21))]
  refine (TBSim.bind (SharedDigest.search_good false hl hp hpc) (W₂:=21) ?_).mono (by omega) (fun _ _ h=>h)
  intro r u hu
  cases r with
  | none =>
    obtain ⟨t,st,pt,h5,h10,ft⟩:=sign_failure_steps hj hf u hu.result.1
    have hp' : JoinedPost im s none t:=⟨pt,h5,h10,(he.fetch t pt).trans rfl⟩
    exact (TBSim.pure_steps' st hp').mono (by omega) (fun _ _ h=>h)
  | some r =>
    rcases r with ⟨c,a⟩
    obtain ⟨pcu,h19,hc,ha,hN⟩:=hu.result
    have hcost : SharedForest.jointAccountingCost a ≤ 777 := (SharedForest.accepted_conditions a ha).2.2
    obtain ⟨v,k,uv,hk,pv,v28,vtier,vr,vf⟩ := signTier_steps hs htier u pcu
      (SharedForest.jointAccountingCost a) hcost hu.resultCost
    have hsuf : CodeAt im (pcOf 22755) signSuffixCode := by
      change CodeAt im (pcOf 22754) ([0x6c50106f] ++ signSuffixCode ++ []) at hs
      simpa [pcOf,ofNat_add_ofNat] using
        (CodeAt.drop_prefix (pre := [0x6c50106f]) (seg := signSuffixCode) (post := []) hs)
    obtain ⟨t,vt,pt,h22,hidx,rt,ft⟩:=sign_steps_free hsuf v pv v28
    have hvN : OutAt v NBUF a := by
      intro j hj
      rw [vf.get (by unfold NBUF;omega) (by unfold NBUF;omega)]
      exact hN j hj
    have hword : v.getMem 0x20160 >>> 33=BitVec.ofNat 64 (WCT9.digestIndex a) := by
      have h0:=hvN 0 (by decide)
      change v.getMem 0x20160=a.extractLsb' 0 64 at h0
      rw [h0]
      simpa only [BitVec.shiftLeft_zero] using SearchM.shl0_shr33 a
    have hNt : OutAt t NBUF a := by
      intro j hj
      rw [ft.get (by unfold NBUF;omega) (by unfold NBUF;omega)]
      exact hvN j hj
    have hTier : SigGolfCandidate.T3M.Sign.SharedTier.At (SharedForest.conditionalExtra a) t := by
      change SigGolfCandidate.T3M.Sign.SharedTier.At
        (SharedForest.jointAccountingCost a - 773) t
      exact vtier.frame ft (by decide) (by decide) (by decide)
    have ht : JoinedPost im s (some (c,a)) t :=
      ⟨hc,ha,pt,(rt.get (by decide)).trans ((vr.get (by decide)).trans hu.x5),
       h22.trans hword,hidx.trans hword,hNt,(SharedForest.conditional_bounds_of_accepted a ha).1,
       hTier,((hu.frame.trans vf).trans ft).mono (by tauto)⟩
    exact (TBSim.pure_steps' (uv.trans vt) ht).mono (by omega) (fun _ _ h=>h)
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
namespace ClaudeWCT.W9.Machine.Sign.SharedState
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem base_frame_mem {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat}
    {s t : MachineState} {W : Nat→Prop} (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hf : Frame s t W) (h5 : t.getReg .x5=0)
    (hn : ∀ A,A<2^64 → BaseA A → ¬W A) : Base (cfFlag:=cfFlag) sk cache t := by
  apply hb.frame hf (l:=[.x0,.x1,.x2,.x3,.x4,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]) ?_ (by decide) hn
  intro r hr
  cases r <;>simp only [List.mem_cons,List.mem_singleton,not_or] at hr <;>
    first | contradiction | exact h5.trans hb.x5.symm

theorem forest_base {sk a : BitVec 256} {cache : Bytes 131072} {cfFlag : Nat}
    {s t : MachineState} {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (hb : Base (cfFlag:=cfFlag) sk cache s) (h : SharedCoordinate.ClosedPost sk a s rv t) :
    Base (cfFlag:=cfFlag) sk cache t := by
  apply base_frame_mem hb h.write_frame h.x5
  intro A hA hb hw
  unfold BaseA NeverW at hb
  unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW at hw
  simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,Search.TOP_DATA,SIG,FOUT] at hb hw
  omega

theorem forest_rho {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : SharedCoordinate.ClosedPost sk a s rv t) {rho : BitVec 128} (hr : DigAt s SIG rho) : DigAt t SIG rho := by
  exact hr.frame h.write_frame (by unfold SIG;decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT;decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT;decide)

theorem forest_counter {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : SharedCoordinate.ClosedPost sk a s rv t) :
    t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32)) :=
  h.write_frame.get (by unfold ENC;decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT ENC;decide)

theorem forest_index {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : SharedCoordinate.ClosedPost sk a s rv t) : t.getMem 0x20550=s.getMem 0x20550 :=
  h.write_frame.get (A:=0x20550) (by decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT;decide)
end ClaudeWCT.W9.Machine.Sign.SharedState
namespace ClaudeWCT.W9.Machine.Sign.SharedRootBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

structure Ready (sk : SecretKey) (cache : Bytes 131072) (index : Nat)
    (forest : BitVec 128×BitVec 128) (s : MachineState) : Prop where
  pc : s.pc=pcOf 22100
  base : Base (cfFlag:=0) sk cache s
  indexMem : s.getMem 0x20550=BitVec.ofNat 64 index
  counter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  rootLeft : DigAt s ENC forest.1
  rootRight : DigAt s (ENC+48) forest.2

theorem bridge_steps {im : Image}
    (hc : CodeAt im (pcOf 370) words) (hf : CodeAt im (pcOf 24661) SharedFlagInit.code)
    {sk : SecretKey} {cache : Bytes 131072} {cfFlag index : Nat} (forest : BitVec 128×BitVec 128)
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s FOUT forest.1) (hr : DigAt s (ENC+48) forest.2) :
    ∃t,Steps im s 13 13 t ∧ Ready sk cache index forest t ∧
      Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)) ∧
      ∀extra, SigGolfCandidate.T3M.Sign.SharedTier.At extra s →
        SigGolfCandidate.T3M.Sign.SharedTier.At extra t := by
  obtain ⟨u,su,pu,l0,l8,ru,fu⟩:=steps hc s hp
  have bu : Base (cfFlag:=cfFlag) sk cache u := hb.frame fu ru (by decide) (by
    intro A hA ha hw
    unfold BaseA NeverW at ha
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,Search.TOP_DATA] at ha
    unfold enc at hw
    omega)
  obtain ⟨t,st,pt,bt,rt,ft⟩:=SharedFlagInit.steps_base hf u pu bu
  have mem : ∀A,A<2^64 → A≠enc → A≠enc+8 → A≠Search.TOP_DATA+624 →
      t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h0 h8 ht
    rw [ft.get hA ht,fu.get hA (by simp [h0,h8])]
  refine ⟨t,su.trans st,⟨pt,bt,?_,?_,?_,?_⟩,?_,?_⟩
  · exact (mem 0x20550 (by decide) (by unfold enc;decide) (by unfold enc;decide) (by unfold Search.TOP_DATA;decide)).trans hi
  · obtain ⟨c,hc,hcv⟩:=hcounter
    exact ⟨c,hc,(mem (ENC+32) (by unfold ENC;decide) (by unfold ENC enc;decide)
      (by unfold ENC enc;decide) (by unfold ENC Search.TOP_DATA;decide)).trans hcv⟩
  · constructor
    · rw [ft.get (by unfold ENC;decide) (by unfold ENC Search.TOP_DATA;decide)]
      exact l0.trans hl.1
    · rw [ft.get (by unfold ENC;decide) (by unfold ENC Search.TOP_DATA;decide)]
      exact l8.trans hl.2
  · exact hr.frame (fu.trans ft) (by unfold ENC;decide)
      (by unfold ENC enc Search.TOP_DATA;decide) (by unfold ENC enc Search.TOP_DATA;decide)
  · apply (fu.trans ft).mono
    intro A hA hw hlo
    simp only [enc,SIG,Search.TOP_DATA] at hw hlo
    omega
  · intro extra htier
    apply htier.frame (fu.trans ft)
    all_goals simp only [enc,Search.TOP_DATA,Search.EOUT]
    all_goals omega
end ClaudeWCT.W9.Machine.Sign.SharedRootBridge
namespace ClaudeWCT.W9.Machine.Sign.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open SharedDigestBoundary
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem joined_prepend {im : Image} {s u t : MachineState} {r : Option (BitVec 32×BitVec 256)}
    (hf : Frame s u (fun _=>False)) (h : JoinedPost im u r t) : JoinedPost im s r t := by
  cases r with
  | none => exact h
  | some r =>
    rcases h with ⟨hc,ha,hp,h5,h22,hi,hN,hbound,htier,ff⟩
    refine ⟨hc,ha,hp,h5,h22,hi,hN,hbound,htier,(hf.trans ff).mono ?_⟩
    intro A hA hw
    exact hw.elim False.elim id

theorem nonce_search {sk : SecretKey} {cache : Bytes 131072} {msg : SigGolfCandidate.T3.Message}
    {α : Type} {W : Nat} {Q : Option α→MachineState→Prop}
    (hlook : LookOK Images.signImage (SharedDigest.look false))
    (hs : CodeAt Images.signImage (pcOf 22754) signCode)
    (ht : CodeAt Images.signImage (pcOf 24723) signTierCode)
    (hj : CodeAt Images.signImage (pcOf 22764) [0xcccea06f])
    (hf : CodeAt Images.signImage (pcOf 543) failureCode)
    (he : CodeAt Images.signImage (pcOf 545) [0x73])
    (htables : ∀rho t,NoncePost sk cache msg rho t → SharedDigest.TablesAt false t)
    (K : BitVec 128→BitVec 32→BitVec 256→SigGolfCandidate.T3.M (Option α))
    (hfail : ∀t,JoinedPost Images.signImage t none t → Q none t)
    (hrest : ∀rho s,NoncePost sk cache msg rho s → ∀c a t,
      JoinedPost Images.signImage s (some (c,a)) t → TBSim Images.signImage sk t W (K rho c a) Q) :
    TBSim Images.signImage sk (sinit sk cache msg) (frontC+(1+(2^21*200+33+W))) (do
      let tag ← SigGolfCandidate.T3.privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else do
        let rho ← SigGolfCandidate.T3.privateNonce msg
        let r ← SharedForest.sharedDigestSearch rho msg 0 (2^21)
        match r with
        | none => pure none
        | some (c,a) => K rho c a) Q := by
  apply Generic.sign_nonce_front
  · intro t ht
    exact hfail t ⟨ht.pc,ht.x5,ht.x10,(he.fetch t ht.pc).trans rfl⟩
  · intro rho s hn
    obtain ⟨u,su,pu,ru,fu⟩:=SharedNonceJump.steps SharedNonceJump.installed_code s hn.search.pc
    have hp : SharedDigest.Pre false rho msg u := by
      refine ⟨(ru.get (by simp)).trans hn.search.x5,?_,?_,?_⟩
      · exact hn.search.rho.frame fu (by unfold SigGolfCandidate.T3M.Sign.DIG;decide) (by tauto) (by tauto)
      · intro k hk
        rw [fu.get (by unfold DIG;omega) (by tauto)]
        exact hn.search.msg k hk
      · exact (htables rho s hn).frame (fu.mono (fun _ _ h=>h.elim))
    apply TBSim.steps su
    refine TBSim.bind (search_to_forest hlook hs ht hj hf he hp pu) (W₂:=W) ?_
    intro r t ht
    cases r with
    | none => exact (TBSim.pure (hfail t ht)).mono (by omega) (fun _ _ h=>h)
    | some r => exact hrest rho s hn r.1 r.2 t (joined_prepend fu ht)
end ClaudeWCT.W9.Machine.Sign.SharedFront
namespace ClaudeWCT.W9.Machine.Sign.SharedState
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem digest_state {im : Image} {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat}
    {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message} {s t : MachineState} {c : BitVec 32} {a : BitVec 256}
    (hp : HookPre sk msg rho s) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hj : SharedDigestBoundary.JoinedPost im s (some (c,a)) t) :
    SharedCoordinate.Entry sk a t ∧ Base (cfFlag:=cfFlag) sk cache t ∧ DigAt t SIG rho ∧
      t.getMem (BitVec.ofNat 64 (ENC+32))=0 ∧
      t.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      (∀k,k<9 → SharedCoordinate.rank k a<563) := by
  rcases hj with ⟨hc,ha,hpc,h5,h22,hidx,hN,hbound,htier,hf⟩
  have gm : ∀A,A<2^64 →
      ¬(SharedDigest.writes A ∨ A=0x20550 ∨ A=Search.EOUT+32 ∨
        A=Search.EOUT+40 ∨ A=0x66028) →
      t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=fun A hA hn=>hf.get hA hn
  refine ⟨⟨hpc,h5,h22,hN,?_,?_,?_,hbound,htier⟩,?_,?_,?_,hidx,?_⟩
  · intro k hk
    rw [gm _ (by unfold TBL;omega)
      (by unfold SharedDigest.writes DIG NBUF TBL Search.EOUT;omega)]
    exact hp.table k hk
  · intro k hk
    rw [gm _ (by unfold SK;omega)
      (by unfold SharedDigest.writes DIG NBUF SK Search.EOUT;omega)]
    exact hp.sk k hk
  · intro A hA
    have hzero:=hA.1
    rw [gm _ (by unfold ScrZero PRIVW CHAINW NODEW at hzero;omega)
      (by unfold SharedDigest.writes DIG NBUF Search.EOUT;
          unfold ScrZero PRIVW CHAINW NODEW at hzero;omega)]
    exact hp.zero A hzero
  · apply base_frame_mem hb hf h5
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold SharedDigest.writes at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,
      Search.TOP_DATA,Search.EOUT,DIG,NBUF] at hbase hw
    omega
  · exact hp.sigRho.frame hf (by unfold SIG;decide)
      (by unfold SharedDigest.writes DIG NBUF SIG Search.EOUT;decide)
      (by unfold SharedDigest.writes DIG NBUF SIG Search.EOUT;decide)
  · rw [gm _ (by unfold ENC;decide)
      (by unfold SharedDigest.writes DIG NBUF ENC Search.EOUT;decide)]
    exact hz
  · exact ((SharedDigest.acceptedTest_iff a).mp (by rw [SharedDigest.acceptedTest_source];exact ha)).2.1
end ClaudeWCT.W9.Machine.Sign.SharedState
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

structure ForestFields (rho : Digest) (forest : ForestOpening) (s : MachineState) : Prop where
  rho : DigAt s SIG rho
  values : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i)
  paths : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l)

theorem ForestFields.frame {rho : Digest} {forest : ForestOpening} {s t : MachineState}
    (h : ForestFields rho forest s) (hf : Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192))) : ForestFields rho forest t := by
  refine ⟨h.rho.frame hf (by unfold SIG;decide) (by unfold SIG;decide) (by unfold SIG;decide),?_,?_⟩
  · intro c i
    exact (h.values c i).frame hf (by unfold slotV SIG;omega)
      (by unfold slotV SIG;omega) (by unfold slotV SIG;omega)
  · intro c l hl
    have hh : SharedPath.levels c.val≤7 := by unfold SharedPath.levels;split_ifs <;>omega
    exact (h.paths c l hl).frame hf (by unfold SharedPath.target slotV SIG;omega)
      (by unfold SharedPath.target slotV SIG;omega) (by unfold SharedPath.target slotV SIG;omega)

def FinalPost (im : Image) : Option SharedSignature→MachineState→Prop
  | none,t => SearchError im t
  | some sig,t => t.pc=pcOf 20745 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t SIG 5195=sigBC sig ∧ fetch im t=some (.base .ECALL)

def assemble (rho : Digest) (forest : ForestOpening) (layers : CanonicalLayers) : SharedSignature :=
  ⟨rho,layers.policyHints,forest,fun lay=>piecesSignature lay (layers.pieces.getD lay.val ([],[]))⟩

theorem completed_serialize {im : Image} {sk : SecretKey} (hc : Code im)
    {rho : Digest} {forest : ForestOpening} {index : Nat} {p : PreparedRoots}
    {a : Choices} {top : SigGolfCandidate.T3.Pieces} {s : MachineState}
    (hs : Completed index p a top s) (hforest : ForestFields rho forest s) :
    TBSim im sk s 8280 (pure (some (assemble rho forest (layersValue index p a top)))) (FinalPost im) := by
  have hr := assembled_raw s rho (layersValue index p a top).policyHints forest _
    hforest.rho hforest.values hforest.paths (completed_layer_fields hs)
  have hh : (s.getMem 0x66000).setWidth 16=(layersValue index p a top).policyHints := by
    rw [show (0x66000 : Word)=(0x66000#64) by decide,hs.hints]
    apply BitVec.eq_of_toNat_eq
    simp [layersValue,BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_mod_of_dvd _ (show 2^16 ∣ 2^64 by norm_num)]
  obtain ⟨n,hn,t,st,pt,h5,h10,hbytes⟩:=serialize_good hc s hs.pc _ hr hh
  have hpost : FinalPost im (some (assemble rho forest (layersValue index p a top))) t :=
    ⟨pt,h5,h10,hbytes,(hc.halt.tail.fetch t pt).trans rfl⟩
  exact (TBSim.pure_steps' st hpost).mono hn (fun _ _ h=>h)
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem search_serialize {im : Image} {sk : SecretKey} {cache : Bytes 131072} {W : Nat}
    (hc : Code im) {rho : Digest} {forest : ForestOpening} {pair : Digest×Digest}
    {index extra : Nat} {p : PreparedRoots} {s : MachineState}
    (hsearch : TBSim im sk s W
      (searchPreparedLayers (cacheDec cache) index p pair (69 + extra) (14 + extra))
      (FramedLayersPost im index p s))
    (hfields : ForestFields rho forest s) :
    TBSim im sk s (W+8280) (do
      let layers ← searchPreparedLayers (cacheDec cache) index p pair (69 + extra) (14 + extra)
      pure (layers.map (assemble rho forest))) (FinalPost im) := by
  refine TBSim.bind hsearch (W₂:=8280) ?_
  intro layers t ht
  cases layers with
  | none => exact (TBSim.pure (a:=none) (s:=t) (Q:=FinalPost im) ht).mono (by omega) (fun _ _ h=>h)
  | some layers =>
    rcases ht with ⟨⟨a,top,rfl,ha⟩,hf⟩
    exact completed_serialize hc ha (hfields.frame (layers_lowFrame hf))
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem prepared_serialize {im : Image} {sk : SecretKey} {cache : Bytes 131072} {Wr Ws : Nat}
    (hc : Code im) {rho : Digest} {forest : ForestOpening} {pair : Digest×Digest}
    {index extra : Nat} {s : MachineState} {P : PreparedRoots→MachineState→Prop}
    (hroot : TBSim im sk s Wr (prepareRoots index) P)
    (hsearch : ∀p t,P p t → SigGolfCandidate.T3M.Sign.SharedTier.At extra t →
      TBSim im sk t Ws
      (searchPreparedLayers (cacheDec cache) index p pair (69 + extra) (14 + extra))
      (FramedLayersPost im index p t))
    (hptier : ∀p t,P p t → SigGolfCandidate.T3M.Sign.SharedTier.At extra s →
      SigGolfCandidate.T3M.Sign.SharedTier.At extra t)
    (hframe : ∀p t,P p t → Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)))
    (hfields : ForestFields rho forest s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s) :
    TBSim im sk s (Wr+(Ws+8280)) (do
      let prepared ← prepareRoots index
      let layers ← searchPreparedLayers (cacheDec cache) index prepared pair (69 + extra) (14 + extra)
      pure (layers.map (assemble rho forest))) (FinalPost im) := by
  refine TBSim.bind hroot (W₂:=Ws+8280) ?_
  intro p t hp
  exact search_serialize hc (hsearch p t hp (hptier p t hp htier))
    (hfields.frame (hframe p t hp))
end ClaudeWCT.W9.Machine.Sign.SharedSerializer

namespace ClaudeWCT.W9.Machine.Sign.SharedRootBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen SigGolfCandidate.Research.SharedForest

theorem roots_good {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) {forest : BitVec 128×BitVec 128} {s : MachineState}
    (h : Ready sk cache index forest s) :
    TBSim Images.signImage sk s (28+3*(Packed.btCost+47)) (prepareRoots index)
      (fun p t => SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t ∧
        SharedRootControl.LowFrame s t) :=
  SharedRootControl.entry_roots_framed SharedRootControl.installed_code
    SharedRootControl.installed_extraCode SharedLowCode.installed_code
    SharedTreeCode.installed_code SharedLeafCode.installed_code SharedLeaf.installed_copy
    SharedChain.installed_code SharedChain.installed_prefix_code
    SharedSeed.installed_code SharedSeed.installed_seed_hook
    hi forest s h.pc h.indexMem h.base h.rootLeft h.rootRight
end ClaudeWCT.W9.Machine.Sign.SharedRootBridge

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def layersProgram (cache : Bytes 131072) (rho : Digest) (index extra : Nat)
    (forest : ForestOpening×(Digest×Digest)) : SigGolfCandidate.T3.M (Option SharedSignature) := do
  let prepared ← prepareRoots index
  let layers ← searchPreparedLayers (cacheDec cache) index prepared forest.2 (69 + extra) (14 + extra)
  pure (layers.map (assemble rho forest.1))

theorem after_forest_with {im : Image} {sk : SecretKey} {cache : Bytes 131072} {cfFlag index Wr Ws : Nat}
    (hbridge : CodeAt im (pcOf 370) SharedRootBridge.words)
    (hflag : CodeAt im (pcOf 24661) SharedFlagInit.code) (hcodec : SharedSerializer.Code im)
    {rho : Digest} {forest : ForestOpening×(Digest×Digest)}
    {P : MachineState→PreparedRoots→MachineState→Prop}
    (extra : Nat)
    (hroot : ∀s,SharedRootBridge.Ready sk cache index forest.2 s → TBSim im sk s Wr (prepareRoots index) (P s))
    (hsearch : ∀s,SharedRootBridge.Ready sk cache index forest.2 s → ∀p t,P s p t →
      SigGolfCandidate.T3M.Sign.SharedTier.At extra t →
      TBSim im sk t Ws
        (searchPreparedLayers (cacheDec cache) index p forest.2 (69 + extra) (14 + extra))
        (FramedLayersPost im index p t))
    (hptier : ∀s p t,P s p t → SigGolfCandidate.T3M.Sign.SharedTier.At extra s →
      SigGolfCandidate.T3M.Sign.SharedTier.At extra t)
    (hframe : ∀s p t,P s p t → Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)))
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s FOUT forest.2.1) (hr : DigAt s (ENC+48) forest.2.2)
    (hfields : ForestFields rho forest.1 s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s) :
    TBSim im sk s (13+(Wr+(Ws+8280))) (layersProgram cache rho index extra forest) (FinalPost im) := by
  obtain ⟨t,st,ht,ff,ftier⟩:=SharedRootBridge.bridge_steps hbridge hflag forest.2 s hp hb hi hcounter hl hr
  exact TBSim.steps st (prepared_serialize hcodec (hroot t ht) (hsearch t ht)
    (hptier t) (hframe t) (hfields.frame ff) (ftier extra htier))
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def outputProgram (cache : Bytes 131072) (rho : Digest) (a : BitVec 256) :
    SigGolfCandidate.T3.M (Option SharedSignature) := do
  let forest ← buildForest (WCT9.digestIndex a) (forestSelectionFromOutput a) (forestWordsFromOutput a)
  layersProgram cache rho (WCT9.digestIndex a) (conditionalExtra a) forest

theorem forest_tbsim_with {im : Image} {sk a : BitVec 256} {cache : Bytes 131072}
    {cfFlag W : Nat} {rho : Digest}
    (hf : SharedReuse.Fetch im) (hc : ∀c,c<9 → SharedCoordinate.Code im c)
    (hl : LookOK im SharedBoundary.forLook)
    (hrest : ∀(forest : ForestOpening×PairRoot) (s : MachineState),s.pc=pcOf 370 →
      Base (cfFlag:=cfFlag) sk cache s → s.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) →
      (∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) →
      DigAt s FOUT forest.2.1 → DigAt s (ENC+48) forest.2.2 → ForestFields rho forest.1 s →
      SigGolfCandidate.T3M.Sign.SharedTier.At (conditionalExtra a) s →
      TBSim im sk s W
        (layersProgram cache rho (WCT9.digestIndex a) (conditionalExtra a) forest) (FinalPost im))
    (s : MachineState) (hp : SharedCoordinate.Entry sk a s) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hrho : DigAt s SIG rho) (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a))
    (hranks : ∀c,c<9 → SharedCoordinate.rank c a<563) :
    TBSim im sk s ((9*SharedCoordinate.forestStepBound+23)+W) (outputProgram cache rho a) (FinalPost im) := by
  refine TBSim.bind (SharedCoordinate.forest_boundary_good hf hc hl hranks s hp) (W₂:=W) ?_
  intro forest t ht
  exact hrest forest t ht.pc (SharedState.forest_base hb ht)
    ((SharedState.forest_index ht).trans hi)
    ⟨0,by decide,by simpa using (SharedState.forest_counter ht).trans hz⟩
    ht.rootLeft ht.rootRight ⟨SharedState.forest_rho ht hrho,ht.values,ht.paths⟩
    (ht.tierPreserved hp.tier)

theorem outputProgram_source (cache : Bytes 131072) (rho : Digest) (c : BitVec 32) (a : BitVec 256) :
    (do let w ← signFromOutput (cacheDec cache) rho c a
        pure (w.map Witness.signature))=outputProgram cache rho a := by
  simp only [signFromOutput,outputProgram,layersProgram,bind_assoc]
  simp only [conditionalCredit,conditionalTopFloor,CanonicalPolicy.totalCredit,
    CanonicalPolicy.topFloor]
  congr 1
  funext forest
  congr 1
  funext prepared
  congr 1
  funext layers
  cases layers <;> simp [assemble]
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

/-- The paired submission's sizes and layout (witness stack: W 22012, witness at 4128 = 0x1020, message at
26144 = 0x6620). -/
def runtimeSub (imgs : Phase→Image) : Submission :=
  ⟨⟨5195,22012,131072⟩,⟨0x6620,0x80,0xa0,0x80000,0x7000,0x1020⟩,imgs⟩

theorem initialState_of_wsub (imgs : Phase→Image)
    (hv : (imgs .sign).Valid (runtimeSub imgs).sizes (runtimeSub imgs).layout)
    (ho : (imgs .sign).Valid (wsub imgs).sizes (wsub imgs).layout)
    (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) {s : MachineState}
    (h : initialState (wsub imgs) .sign (sk,cache,msg)=some s) :
    initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s := by
  dsimp only [runtimeSub,wsub] at hv ho h ⊢
  simp only [initialState,hv,ho,↓reduceIte] at h ⊢
  exact h

theorem finalPost_halt {im : Image} {o : Option SharedSignature} {t : MachineState}
    (h : FinalPost im o t) : fetch im t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none => exact ⟨h.2.2.2,h.2.1⟩
  | some sig => exact ⟨h.2.2.2.2,h.2.1⟩

theorem finalPost_readout {imgs : Phase→Image} {o : Option SharedSignature} {t : MachineState}
    (h : FinalPost (imgs .sign) o t) :
    o.map sigBC=if t.getReg .x10=0 then some (readOutput (runtimeSub imgs).sizes
      (runtimeSub imgs).layout .sign t) else none := by
  cases o with
  | none => rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some sig =>
    rw [if_pos h.2.2.1]
    exact congrArg some h.2.2.2.1.symm

theorem runtime_refines {imgs : Phase→Image} {W : Nat}
    (hW : W<CYCLE_LIMIT) (program : SigGolfCandidate.T3.M (Option SharedSignature)) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    {s : MachineState} (hinit : initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s)
    (hsim : TBSim (imgs .sign) sk s W program
      (FinalPost (imgs .sign))) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> (runtimeSub imgs).run .sign (sk,cache,msg)=
      (fun p=>(p.1.map sigBC,p.2.1,p.2.2)) <$>
        countBoth (mrealize sk program) := by
  apply Sim.run_eq (runtimeSub imgs) .sign (sk,cache,msg) hinit hsim hW (fun o=>o.map sigBC)
  intro o t ht
  exact ⟨(finalPost_halt ht).1,(finalPost_halt ht).2,finalPost_readout ht⟩

theorem runtime_terminates {imgs : Phase→Image} {W : Nat}
    (hW : W+1<CYCLE_LIMIT) (program : SigGolfCandidate.T3.M (Option SharedSignature)) (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    {s : MachineState} (hinit : initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s)
    (hsim : TBSim (imgs .sign) sk s W program
      (FinalPost (imgs .sign))) :
    ((runtimeSub imgs).runWith hash .sign (sk,cache,msg)).finished=true ∧
      ((runtimeSub imgs).runWith hash .sign (sk,cache,msg)).cycles<CYCLE_LIMIT := by
  obtain ⟨hf,hc⟩:=Sim.runWith (runtimeSub imgs) .sign (sk,cache,msg) hinit hsim hW
    (fun _ _ h=>finalPost_halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc hW⟩
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer

def tailCost : Nat := 13+((28+3*(Packed.btCost+47))+((prefixCost+335006)+8280))

theorem after_forest {sk : SecretKey} {cache : Bytes 131072} {cfFlag index : Nat}
    (hib : index<2^31) {rho : Digest} {forest : ForestOpening×(Digest×Digest)}
    (extra : Nat) (he : extra ≤ 4)
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s FOUT forest.2.1) (hr : DigAt s (ENC+48) forest.2.2)
    (hfields : ForestFields rho forest.1 s)
    (htier : SigGolfCandidate.T3M.Sign.SharedTier.At extra s) :
    TBSim Images.signImage sk s tailCost
      (layersProgram cache rho index extra forest) (FinalPost Images.signImage) := by
  exact after_forest_with SharedRootBridge.installed_code SharedFlagInit.installed_code
    SharedSerializer.installed_code extra
    (fun _ h=>SharedRootBridge.roots_good hib h)
    (fun _ h _ _ hp ht=>SharedSearches.from_built_framed extra he hib hp.1 ht h.counter)
    (fun _ _ _ hp ht=>hp.1.tier extra ht)
    (fun _ _ _ hp=>hp.2) s hp hb hi hcounter hl hr hfields htier
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem option_bind_map {α β : Type} (program : SigGolfCandidate.T3.M (Option α)) (f : α→β) :
    (do let some a ← program | pure none
        pure (some (f a)))=(do let a ← program;pure (a.map f)) := by
  apply congrArg (fun k=>program >>= k)
  funext a
  cases a <;>rfl

theorem sign_program (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg=(do
      let tag ← SigGolfCandidate.T3.privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else do
        let rho ← SigGolfCandidate.T3.privateNonce msg
        let r ← sharedDigestSearch rho msg 0 (2^21)
        match r with
        | none => pure none
        | some (_,a) => outputProgram cache rho a) := by
  simp only [SigGolfCandidate.Research.SharedForest.sign,SigGolfCandidate.Research.SharedForest.signPayload,ClaudeWCT.WCT9.digestAttemptLimit]
  congr 1
  funext tag
  split <;>rename_i ht
  · rfl
  · congr 1
    funext rho
    congr 1
    funext r
    cases r with
    | none => rfl
    | some r =>
      rcases r with ⟨c,a⟩
      dsimp only
      refine Eq.trans ?_ (outputProgram_source cache rho c a)
      congr 1
      funext w
      cases w <;>rfl

end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem sign_tbsim_with {W : Nat}
    (hlook : LookOK Images.signImage (SharedDigest.look false))
    (hs : CodeAt Images.signImage (pcOf 22754) SharedDigestBoundary.signCode)
    (ht : CodeAt Images.signImage (pcOf 24723) SharedDigestBoundary.signTierCode)
    (hj : CodeAt Images.signImage (pcOf 22764) [0xcccea06f])
    (hf : CodeAt Images.signImage (pcOf 543) SharedDigestBoundary.failureCode)
    (he : CodeAt Images.signImage (pcOf 545) [0x73])
    (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    (htables : ∀rho s,NoncePost sk cache msg rho s → SharedDigest.TablesAt false s)
    (hfront : ∀rho s,NoncePost sk cache msg rho s → HookPre sk msg rho s ∧
      Base sk cache s ∧ s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (houtput : ∀rho a t,SharedCoordinate.Entry sk a t → Base sk cache t → DigAt t SIG rho →
      t.getMem (BitVec.ofNat 64 (ENC+32))=0 →
      t.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) →
      (∀k,k<9 → SharedCoordinate.rank k a<563) →
      TBSim Images.signImage sk t W (outputProgram cache rho a) (FinalPost Images.signImage)) :
    TBSim Images.signImage sk (sinit sk cache msg) (frontC+(1+(2^21*200+33+W)))
      (SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg) (FinalPost Images.signImage) := by
  rw [sign_program]
  refine SharedFront.nonce_search hlook hs ht hj hf he htables (fun rho _ a=>outputProgram cache rho a)
    (fun _ h=>h) ?_
  intro rho s hn c a t hj
  obtain ⟨hp,hb,hz⟩:=hfront rho s hn
  obtain ⟨he,hb,hr,hz,hi,hranks⟩:=SharedState.digest_state hp hb hz hj
  exact houtput rho a t he hb hr hz hi hranks
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def restCost : Nat := (9*SharedCoordinate.forestStepBound+23)+tailCost
def signCost : Nat := frontC+(1+(2^21*200+33+restCost))

theorem forest_tbsim {sk a : BitVec 256} {cache : Bytes 131072} {rho : Digest}
    (s : MachineState) (hp : SharedCoordinate.Entry sk a s) (hb : Base sk cache s)
    (hrho : DigAt s SIG rho) (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a))
    (hranks : ∀c,c<9 → SharedCoordinate.rank c a<563) :
    TBSim Images.signImage sk s restCost (outputProgram cache rho a) (FinalPost Images.signImage) := by
  exact forest_tbsim_with SharedReuse.installed_fetch SharedCoordinate.installed_Code
    SharedBoundary.installed_forLook
    (fun _ t=>after_forest (WCT9.digestIndex_lt a) (conditionalExtra a) hp.tierBound t)
    s hp hb hrho hz hi hranks

theorem sign_tbsim (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    TBSim Images.signImage sk (sinit sk cache msg) signCost
      (SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg) (FinalPost Images.signImage) := by
  exact sign_tbsim_with SharedDigest.installed_sign_look SharedDigestBoundary.installed_sign_success
    SharedDigestBoundary.installed_sign_tier
    SharedDigestBoundary.installed_sign_failure_jump SharedDigestBoundary.installed_sign_failure
    SharedDigestBoundary.installed_sign_failure_ecall sk cache msg
    (fun _ _ hn=>SharedDigest.tables_of_costAt (SignLink.hook_v7 hn).search.cost)
    (fun _ _ hn=>⟨SignLink.hook_v7 hn,hn.inv⟩)
    (fun _ _ t=>forest_tbsim t)

end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

/-- C1 (stage 1): the leaf stub adds at most 9 steps per leaf and the fold stub at most 6 per node
(`SharedLeaves.cost` 6·stepC+65, node bound 68); still far below `CYCLE_LIMIT`. -/
theorem signCost_lt : signCost+1<CYCLE_LIMIT := by decide +kernel

theorem initialState_paired (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    initialState Paired.submission .sign (sk,cache,msg)=some (sinit sk cache msg) := by
  exact initialState_of_wsub submission.image Paired.submission_sign_valid submission_sign_valid
    sk cache msg (initialState_sign sk cache msg)

theorem sign_refines (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> Paired.submission.run .sign (sk,cache,msg)=
      (fun p=>(p.1.map sigBC,p.2.1,p.2.2)) <$>
        countBoth (mrealize sk (SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg)) := by
  exact runtime_refines (imgs:=submission.image) (Nat.lt_of_succ_lt signCost_lt) _ sk cache msg
    (initialState_paired sk cache msg) (sign_tbsim sk cache msg)

theorem sign_terminates (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    (Paired.submission.runWith hash .sign (sk,cache,msg)).finished=true ∧
      (Paired.submission.runWith hash .sign (sk,cache,msg)).cycles<CYCLE_LIMIT := by
  exact runtime_terminates (imgs:=submission.image) signCost_lt _ hash sk cache msg
    (initialState_paired sk cache msg) (sign_tbsim sk cache msg)
end ClaudeWCT.W9.Machine.Sign.SharedController
end
