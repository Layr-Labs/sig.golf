import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.PackedHelper
import SigGolfCandidate.T3M.Sign.SeedLeafPhases
import SigGolfCandidate.T3M.Sign.PackedBoundaryEntry

namespace ClaudeWCT.W9.Machine.Sign.TopLeafP
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
def Top42 (image : Image) (b : Nat) : Prop :=
  ∀ (s : MachineState) (i : Nat), s.pc = pcOf (b + 42) → s.getReg .x8 = BitVec.ofNat 64 0 →
    s.getReg .x19 = BitVec.ofNat 64 i → i < 2 ^ 32 →
    ∃ t, Steps image s 5 5 t ∧ t.pc = (if i % 2 = 0 then pcOf (b + 44) else pcOf (b + 60)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False)
def pairK3 (A : LeafArgs) (p : Nat) : Nat := A.pairK p + 3 + (if 2 * p + 1 < A.n then 3 else 0)
def pairC3 (A : LeafArgs) (p : Nat) : Nat := A.pairC p + 3 + (if 2 * p + 1 < A.n then 3 else 0)
section leaf
variable {image : Image} {b : Nat} (hsub : SeedIndependentAt image b) (h42 : Top42 image b) (sk : BitVec 256)
  {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A) (hl0 : A.lay = 0)
include hsub h42 hpre hl0
theorem leaf_iterS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 60)) (seed : Digest)
    (hseed : DigAt t (SEEDS + 16 * (j % 2)) seed) :
    TSim image sk t (A.iterK j) (A.iterC j) (A.e j) (A.e j) (halfUpd A st <$> chainProg A j seed)
      (fun st' u => u.pc = pcOf (b + 41) ∧ LeafInv s0 A (j + 1) st' u ∧
        Frame t u (fun X => (X = CHAIN + 16 ∨ X = CHAIN + 24) ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨
          (slot A.lay j ≤ X ∧ X < slot A.lay j + 16) ∨ (A.valp + 16 * j ≤ X ∧ X < A.valp + 16 * j + 16))) := by
  obtain ⟨u0, st0, u0pc, hcp, hcs, u0r, u0f⟩ := Sign.Seed.leaf_prechainS hsub sk hpre hj ht hpc seed hseed
  have hch := Sign.Seed.chainRun_tsim hsub sk hcp u0pc seed hcs
  rw [map_eq_bind_pure_comp]
  refine (TSim.steps st0 (TSim.bind (k₂ := 4 + (if A.so then 0 else 11 + slotK A.lay j))
    (c₂ := 4 + (if A.so then 0 else 11 + slotK A.lay j)) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq (by unfold chainProg; rfl) ?_ ?_ ?_ ?_
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw, hfw⟩ := Sign.Seed.leaf_postchainS hsub sk hpre hj ht hupc (u0r.trans hur)
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
  all_goals (try unfold LeafArgs.iterK); (try unfold LeafArgs.iterC)
  all_goals first | omega | (split_ifs <;> omega)
theorem leaf_prfS {p : Nat} (hp : 2 * p < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A (2 * p) st t) (hpc : t.pc = pcOf (b + 41)) {β : Type} {f : Digest × Digest → SigGolfCandidate.T3.M β}
    {k c n bl : Nat} {Q : β → MachineState → Prop}
    (hk : ∀ a : BitVec 256, ∀ u, LeafInv s0 A (2 * p) st u → u.pc = pcOf (b + 60) →
      DigAt u SEEDS (a.extractLsb' 0 128) → DigAt u (SEEDS + 16) (a.extractLsb' 128 128) →
      TSim image sk u k c n bl (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TSim image sk t (22 + k) (29 + c) (1 + n) (1 + bl)
      (privatePair 0 A.lay.val A.tree p A.leaf >>= f) Q := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.Seed.sub41_spec hsub t hpc (2 * p) A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos hp] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := h42 t1 (2 * p) t1pc
    (by rw [t1r.get (by simp), g _ (by simp [leafRegs]), hpre.x8, hl0]; rfl) (by rw [t1r.get (by simp)]; exact ht.x19)
    (by omega)
  rw [if_pos (by omega)] at t2pc
  have e12 : RegsExcept t t2 [.x6] := (t1r.trans t2r).mono (by simp)
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3a, t3b, t3r, t3f⟩ := Sign.Seed.sub44_spec hsub t2 t2pc A.lay.val A.tree
    A.leaf (2 * p) hlay hpre.htree hpre.hleaf (by omega)
    (by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x8])
    (by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x9])
    (by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x18])
    (by rw [e12.get (by simp)]; exact ht.x19)
  rw [show 2 * p / 2 = p by omega] at t3a
  have f13 : Frame t t3 (fun X => X = PRIV + 16 ∨ X = PRIV + 24) :=
    ((t1f.trans t2f).trans t3f).mono (fun X _ h => by rcases h with (h | h) | h <;> simp_all)
  have r13 : RegsExcept t t3 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (e12.trans t3r).mono (by simp)
  have hLP : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → ¬ LeafW A X := by
    intro X hX hw
    have := hpre.hvs; have := hpre.hds; have := hpre.hdv
    unfold LeafW at hw
    rw [if_pos hl0] at hw
    sc_omega
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t3.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (f13.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))
      (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))).trans
      (ht.frame.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)) (hLP X hX))
  have hq : hashInput t3 = toQ (privateInput sk (.inl (header 0 A.lay.val A.tree p A.leaf))) := by
    refine hashInput_toQ t3 _ 0 PRIV (privateInput_tweak_length _ _) t3x10 (by decide) (by decide) t3x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV + 8) (by simp), t3a, t3b, fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
      fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hpre.p0, hpre.p8, hpre.p32, hpre.p40,
      hpre.p48, hpre.p56]
    rfl
  have hv : hashArgumentsValid t3 = true :=
    hashArgs_const t3 PRIV 64 SEEDS t3x10 t3x11 t3x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [leafRegs]), hpre.x5]
  refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.privatePair_bind (k := k) (c := c) (n := n) (b := bl)
    (Sign.Seed.fetch_sub59 hsub t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl (by omega) (by omega) rfl rfl
  have hwf := Frame.writeHash t3 a SEEDS t3x12 (by decide)
  refine hk a (writeHash t3 a) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by rw [pc_writeHash, t3pc,
    pcOf_add4]) (DigAt.writeHash_lo t3 a SEEDS t3x12 (by decide))
    (DigAt.writeHash_hi t3 a SEEDS t3x12 (by decide))
  · rw [getReg_writeHash, r13.get (by simp)]; exact ht.x19
  · rw [getReg_writeHash, r13.get (by simp)]; exact ht.x23
  · rw [getReg_writeHash, r13.get (by simp)]; exact ht.x3
  · have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
    exact ((ht.regs.trans r13).trans hw0).mono (by decide)
  · refine (ht.frame.trans (f13.trans hwf)).mono (fun X _ h => ?_)
    unfold LeafW at *
    rcases h with h | (h | h) | h
    · exact h
    · left; exact h
    · right; left; exact h
    · right; right; left; simp only [SEEDS] at h ⊢; omega
  · rw [(f13.trans hwf).get (by decide) (by simp only [LEAFPK, PRIV, SEEDS]; omega), ht.lh16]
  · rw [(f13.trans hwf).get (by decide) (by simp only [LEAFPK, PRIV, SEEDS]; omega), ht.lh24]
  · exact ht.elen
  · exact ht.vlen
  · intro hso c hc
    have h1 := slot_ge A.lay c
    have h2 := slot_lt A.lay (show c < A.n by omega)
    exact (ht.ends hso c hc).frame (f13.trans hwf) (by sc_omega) (by sc_omega) (by sc_omega)
  · have hvs := hpre.hvs
    have hvb := hpre.hv
    exact ht.vals.frame (f13.trans hwf) (by rw [ht.vlen]; omega) (fun X h1 h2 => by
      rw [ht.vlen] at h2; sc_omega)
theorem leaf_oddS {j : Nat} (hj : j < A.n) (hodd : j % 2 = 1) {st : List Digest × List Digest}
    {t : MachineState} (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 41)) :
    ∃ u, Steps image t 6 6 u ∧ u.pc = pcOf (b + 60) ∧ LeafInv s0 A j st u ∧ Frame t u (fun _ => False) := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [ht.regs.get (by simp [leafRegs]), hpre.x26]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.Seed.sub41_spec hsub t hpc j A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := h42 t1 j t1pc
    (by rw [t1r.get (by simp), ht.regs.get (by simp [leafRegs]), hpre.x8, hl0]; rfl)
    (by rw [t1r.get (by simp)]; exact ht.x19) (by omega)
  rw [if_neg (by omega)] at t2pc
  have r12 : RegsExcept t t2 [.x6] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  refine ⟨t2, st1.trans st2, t2pc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.elen, ht.vlen, ?_, ?_⟩, f12⟩
  · rw [r12.get (by simp)]; exact ht.x19
  · rw [r12.get (by simp)]; exact ht.x23
  · rw [r12.get (by simp)]; exact ht.x3
  · exact (ht.regs.trans r12).mono (by decide)
  · exact (ht.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  · rw [f12.get (by decide) (by simp)]; exact ht.lh16
  · rw [f12.get (by decide) (by simp)]; exact ht.lh24
  · intro hso c hc
    have h1 := slot_ge A.lay c; have h2 := slot_lt A.lay (show c < A.n by omega)
    exact (ht.ends hso c hc).frame f12 (by sc_omega) (by simp) (by simp)
  · exact ht.vals.frame f12 (by rw [ht.vlen]; have := hpre.hv; omega) (fun X _ _ => by simp)
theorem leaf_pairS {p : Nat} (hp : 2 * p < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A (2 * p) st t) (hpc : t.pc = pcOf (b + 41)) :
    TSim image sk t (pairK3 A p) (pairC3 A p) (A.pairN p) (A.pairN p)
      (privatePair 0 A.lay.val A.tree p A.leaf >>= fun seeds =>
        (List.range 2).foldlM (leafHalf A seeds p) st)
      (fun st' u => u.pc = pcOf (b + 41) ∧ LeafInv s0 A (min (2 * p + 2) A.n) st' u) := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have hfold : ∀ (seeds : Digest × Digest), (List.range 2).foldlM (leafHalf A seeds p) st =
      leafHalf A seeds p st 0 >>= fun st1 => leafHalf A seeds p st1 1 := by
    intro seeds; simp [List.range_succ, List.foldlM_append]
  have hd : ∀ i < A.n, A.so = false → A.d i ≤ maxDigit A.lay i := fun i hi => (hpre.hdigb i hi).2
  unfold pairK3 pairC3 LeafArgs.pairK LeafArgs.pairC LeafArgs.pairN
  refine (leaf_prfS hsub h42 sk hpre hl0 hp ht hpc
    (k := A.iterK (2 * p) + (if 2 * p + 1 < A.n then 6 + A.iterK (2 * p + 1) else 0))
    (c := A.iterC (2 * p) + (if 2 * p + 1 < A.n then 6 + A.iterC (2 * p + 1) else 0))
    (n := A.e (2 * p) + (if 2 * p + 1 < A.n then A.e (2 * p + 1) else 0))
    (bl := A.e (2 * p) + (if 2 * p + 1 < A.n then A.e (2 * p + 1) else 0))
    (fun a u hu upc hlo hhi => ?_)).of_eq rfl (by split_ifs <;> omega) (by split_ifs <;> omega) (by omega) (by omega)
  rw [hfold, leafHalf_lt A _ p st 0 (by omega) (hd _ (by omega))]
  simp only [if_pos rfl]
  have h1 := leaf_iterS hsub h42 sk hpre hl0 (j := 2 * p) (by omega) hu upc (a.extractLsb' 0 128)
    (by rw [show 2 * p % 2 = 0 by omega]; simpa using hlo)
  by_cases hq : 2 * p + 1 < A.n
  · simp only [if_pos hq]
    refine TSim.bind h1 (fun st1 w hw => ?_)
    obtain ⟨wpc, hw1, hwf⟩ := hw
    obtain ⟨x, stx, xpc, hx, xf⟩ := leaf_oddS hsub h42 sk hpre hl0 hq (by omega) hw1 wpc
    rw [leafHalf_lt A _ p st1 1 hq (hd _ hq), if_neg (by omega)]
    have hhi' : DigAt x (SEEDS + 16 * ((2 * p + 1) % 2)) (a.extractLsb' 128 128) := by
      rw [show (2 * p + 1) % 2 = 1 by omega, Nat.mul_one]
      refine (hhi.frame hwf (by decide) ?_ ?_).frame xf (by decide) (by simp) (by simp)
      · have := slot_ge A.lay (2 * p); have := slot_lt A.lay hp; have := hpre.hvs
        simp only [CHAIN, SEEDS, LEAFPK, PRIV] at *; omega
      · have := slot_ge A.lay (2 * p); have := slot_lt A.lay hp; have := hpre.hvs
        simp only [CHAIN, SEEDS, LEAFPK, PRIV] at *; omega
    refine (TSim.steps stx ((leaf_iterS hsub h42 sk hpre hl0 (j := 2 * p + 1) hq hx xpc _ hhi').mono
      (fun st2 y hy => ⟨hy.1, by rw [show min (2 * p + 2) A.n = 2 * p + 1 + 1 by omega]; exact hy.2.1⟩))).of_eq
      rfl (by omega) (by omega) (by omega) (by omega)
  · simp only [if_neg hq]
    rw [show (fun st1 => leafHalf A (a.extractLsb' 0 128, a.extractLsb' 128 128) p st1 1) =
      fun st1 => pure st1 from funext fun st1 => leafHalf_ge A _ p st1 1 (by omega), bind_pure]
    exact (h1.mono (fun st1 w hw => ⟨hw.1, by
      rw [show min (2 * p + 2) A.n = 2 * p + 1 by omega]; exact hw.2.1⟩)).of_eq rfl (by omega) (by omega)
      (by omega) (by omega)
theorem buildLeaf_tsimT (hpc : s0.pc = pcOf (b + 27))
    (h15 : A.tree = 0 ∨ s0.getReg .x15 = BitVec.ofNat 64 (SigGolfCandidate.T3.height A.lay)) :
    TSim image sk s0 (17 + sumTo (pairK3 A) ((A.n + 1) / 2) + (if A.so then 3 else 19))
      (17 + sumTo (pairC3 A) ((A.n + 1) / 2) + (if A.so then 3 else 18 + 8 * leafBlocks A.lay)) A.leafN A.leafB
      (buildLeaf A.lay A.tree A.leaf A.digits A.so)
      (fun r t => t.pc = pcOf A.ret ∧ (A.so = false → DigAt t A.dest r.1) ∧ DigsAt t A.valp r.2 ∧
        r.2.length = A.n ∧ t.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * A.n) ∧ RegsExcept s0 t leafRegs ∧
        Frame s0 t (LeafW A)) := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  obtain ⟨t1, st1, t1pc, t1x3, t1x19, t1l16, t1l24, t1r, t1f⟩ :=
    Sign.Seed.sub27_spec hsub s0 hpc A.lay A.tree A.leaf (by have := hpre.hroute; omega) hpre.x8 hpre.x9 hpre.x18 h15
  have h0 : LeafInv s0 A 0 ([], []) t1 := by
    refine ⟨t1x19, ?_, by rw [t1x3, hpre.x1], t1r.mono (by decide), t1f.mono (fun X _ h => ?_), t1l16,
      t1l24, by simp, rfl, fun _ c hc => absurd hc (by omega), DigsAt.nil _ _⟩
    · rw [t1r.get (by simp), hpre.x23]; simp
    · unfold LeafW; rw [if_pos hl0]; simp only [CHAIN, LEAFPK] at h ⊢; omega
  rw [buildLeaf_unfold]
  refine (TSim.steps st1 (TSim.bind (k₂ := if A.so then 3 else 19)
    (c₂ := if A.so then 3 else 18 + 8 * leafBlocks A.lay) (n₂ := if A.so then 0 else 1)
    (b₂ := if A.so then 0 else leafBlocks A.lay) (TSim.foldlM_range ((A.n + 1) / 2) _ ([], [])
    (fun p st t => t.pc = pcOf (b + 41) ∧ LeafInv s0 A (min (2 * p) A.n) st t)
    (pairK3 A) (pairC3 A) A.pairN A.pairN (fun p hp st t ht => ?_) ⟨t1pc, by simpa using h0⟩)
    (fun st t ht => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · have h2p : 2 * p < A.n := by omega
    rw [show min (2 * p) A.n = 2 * p by omega] at ht
    exact (leaf_pairS hsub h42 sk hpre hl0 h2p ht.2 ht.1).mono (fun st' u hu =>
      ⟨hu.1, by rw [show 2 * (p + 1) = 2 * p + 2 by ring]; exact hu.2⟩)
  · obtain ⟨tpc, hinv⟩ := ht
    rw [show min (2 * ((A.n + 1) / 2)) A.n = A.n by omega] at hinv
    exact (Sign.Seed.leaf_exitS hsub sk hpre hinv tpc).mono (fun r u hu =>
      ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1⟩)
  all_goals (try simp only [LeafArgs.leafN, LeafArgs.leafB])
  all_goals omega
end leaf
theorem top42_spec : Top42 Sign.image 1013 := by
  intro s i hpc h8 h19 hi
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := PackedLeaf.hook_spec s hpc
  obtain ⟨t2, st2, t2pc, t2x6, t2r, t2f⟩ := PackedLeaf.top_spec t1 t1pc (by rw [t1r.get (by simp)]; exact h8)
    (by rw [t1r.get (by simp)]; exact h19) hi
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := Sign.Seed.sub43_spec (Or.inr rfl)
    (Sign.SeedIndependent.codeAt_sub_43 Sign.SeedIndependent.seedIndependentAt_sign) t2 (by rw [t2pc])
  refine ⟨t3, st1.trans (st2.trans st3), ?_, ((t1r.trans t2r).trans t3r).mono (by simp),
    ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)⟩
  rw [t3pc, t2x6]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, if_pos (by decide), if_pos rfl]
  · rw [h, if_neg (by decide), if_neg (by decide)]
theorem top_cycles (A : LeafArgs) (hl0 : A.lay = 0) (hso : A.so = true) (hd : ∀ i < A.n, A.d i ≤ 7) :
    17 + sumTo (pairC3 A) ((A.n + 1) / 2) + (if A.so then 3 else 18 + 8 * leafBlocks A.lay) ≤ 18839 := by
  have hn : A.n = 54 := by unfold LeafArgs.n; rw [hl0]; rfl
  have hit : ∀ i < A.n, A.iterC i ≤ 331 := by
    intro i hi
    unfold LeafArgs.iterC LeafArgs.e selectorExtra
    rw [hso, hl0]
    simp only [if_true, rungC, headerK]
    have := hd i hi
    have h42 : (0 : Layer).val = 0 := rfl
    simp only [h42, if_true]
    split_ifs <;> omega
  have hp : ∀ p < (A.n + 1) / 2, pairC3 A p ≤ 697 := by
    intro p hp
    have h1 := hit (2 * p) (by omega)
    have h2 := hit (2 * p + 1) (by omega)
    unfold pairC3 LeafArgs.pairC
    rw [if_pos (by omega), if_pos (by omega)]
    omega
  have := SigGolfCandidate.T3M.Sign.Packed.sumTo_le_mul (pairC3 A) 697 ((A.n + 1) / 2) hp
  rw [hso, if_pos rfl]
  rw [hn] at this
  rw [hn]
  omega
theorem pair_steps_le (A : LeafArgs) (p : Nat) : pairK3 A p ≤ pairC3 A p := by
  have hit : ∀ i, A.iterK i ≤ A.iterC i := by
    intro i
    unfold LeafArgs.iterK LeafArgs.iterC
    have h1 : rungK A.lay ≤ rungC A.lay := by unfold rungK rungC; omega
    have := Nat.mul_le_mul_right (A.e i) h1
    omega
  unfold pairK3 pairC3 LeafArgs.pairK LeafArgs.pairC
  have := hit (2 * p); have := hit (2 * p + 1)
  split_ifs <;> omega
theorem topLeafSpec : SigGolfCandidate.T3M.Sign.Packed.TopLeafSpec := by
  intro sk A s hl0 hso hd hpre hpc h15
  have h := buildLeaf_tsimT Sign.SeedIndependent.seedIndependentAt_sign top42_spec sk hpre hl0 hpc h15
  refine (h.toTBSim ?_).mono (top_cycles A hl0 hso hd) (fun r t ht => ht)
  have := SigGolfCandidate.T3M.Sign.Packed.sumTo_le_sumTo (pairK3 A) (pairC3 A) ((A.n + 1) / 2)
    (fun p _ => pair_steps_le A p)
  split_ifs <;> omega
end ClaudeWCT.W9.Machine.Sign.TopLeafP
