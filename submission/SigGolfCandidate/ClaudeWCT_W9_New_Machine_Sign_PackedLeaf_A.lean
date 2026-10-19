import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_LowerRuns
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_ExpandLink_Link
import SigGolfCandidate.T3M_Sign_SeedLeafPhases
import SigGolfCandidate.T3M_Sign_PackedLowTree

set_option Elab.async false

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

set_option maxHeartbeats 0 in
theorem signCode_drop_new : Images.signReferenceImage.code.drop 11003 = signNew ++ Images.signReferenceImage.code.drop 20771 := by
  decide +kernel
/-- C4: the coordinate-0 arena at sign words 1700..1725. -/
theorem arena_signImage : arenaCode <+: Images.signReferenceImage.code.drop 1700 :=
  List.prefix_iff_eq_take.mpr (by decide +kernel)
theorem newCodeAt_image : NewCodeAt Sign.image :=
  ⟨⟨_, signCode_drop_new.symm⟩, ⟨Images.signReferenceImage.code.drop 21667, by decide +kernel⟩, arena_signImage⟩

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
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
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
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
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
  have hn : A.n=54 ∨ A.n=43 := chainCount_cases A.lay
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

#print axioms LeafInv.rebase_chain
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

#print axioms chain_cont
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

#print axioms foldlM_append_eq
end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
