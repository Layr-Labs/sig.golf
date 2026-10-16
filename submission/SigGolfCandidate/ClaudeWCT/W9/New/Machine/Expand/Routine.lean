import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns
import SigGolfCandidate.W9Drv.FtsCore
import SigGolfCandidate.W9Machine.WctChainCertified
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCode
import SigGolfCandidate.T3M.Expand.Layers
import SigGolfCandidate.T3M.Search.BCCounterSearch
import SigGolfCandidate.W9Machine.WctNestView
import SigGolfCandidate.W9Drv.ChildPrefix
import SigGolfCandidate.W9Machine.WctN600Assembly
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChainSem
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChildESem
import SigGolfCandidate.W9Machine.WctImageIdentity

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64 zero16)
open SphincsSecurity (bytesLE)
set_option linter.unusedSimpArgs false
/-- Chain-word base `t6 = child << 20 | a5`. C4 (FTS coordinate + 1, as b3cc11b's campaign S2): nibble `k + 1`. -/
def qQ (k index j : Nat) : Nat := j * 2 ^ 20 + index * 2 ^ 27 + 65536 * (k + 1)
theorem ftsChainLow_qQ (index k j t st : Nat) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128) (ht : t < 6)
    (hst : st < 4) : WCT9.ftsChainLow index k j t st = qQ k index j + qK t st := by
  unfold WCT9.ftsChainLow qQ qK
  rw [Nat.mod_eq_of_lt (show t < 8 by omega), Nat.mod_eq_of_lt (show st < 4 by omega),
    Nat.mod_eq_of_lt (show k + 1 < 16 by omega), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hidx]
  ring
theorem step_byte (Q t st st' : Nat) (hQ : Q % 65536 = 0) (hQb : Q < 2 ^ 63) (ht : t < 6) (hst : st < 4)
    (hst' : st' < 4) :
    replaceByte (BitVec.ofNat 64 (Q + qK t st)) 1 ((BitVec.ofNat 64 st').truncate 8) =
      BitVec.ofNat 64 (Q + qK t st') := by
  apply BitVec.eq_of_toNat_eq
  rw [ClaudeWCT.W9.Machine.VLib.replaceByte_toNat _ _ (by decide)]
  simp only [qK, BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega
theorem chainInput_blk4 (index k j t st : Nat) (val : Digest) :
    WCT9.chainInput index k j t st val = VLib.blk4 0 (WCT9.ftsChainHeader index k j t st) 0 val := by
  rw [WCT9.chainInput_eq]
  simp only [VLib.blk4, VLib.bytesLE16_zero]
theorem chain_hashIn {u : MachineState} {A : Nat} {k index j t st : Nat} {val : Digest} (hk : k < 9)
    (hidx : index < 2 ^ 31) (hj : j < 128) (ht : t < 6) (hst : st < 4)
    (h10 : u.getReg .x10 = BitVec.ofNat 64 A) (h11 : u.getReg .x11 = BitVec.ofNat 64 64)
    (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (p0 : u.getMem (BitVec.ofNat 64 A) = 0) (p0' : u.getMem (BitVec.ofNat 64 (A + 8)) = 0)
    (hh0 : u.getMem (BitVec.ofNat 64 (A + 16)) = BitVec.ofNat 64 (qQ k index j + qK t st))
    (hh1 : u.getMem (BitVec.ofNat 64 (A + 24)) = 0)
    (p1 : u.getMem (BitVec.ofNat 64 (A + 32)) = 0) (p1' : u.getMem (BitVec.ofNat 64 (A + 40)) = 0)
    (hv : DigAt u (A + 48) val) :
    hashInput u = toQ (pad64 (WCT9.chainInput index k j t st val)) := by
  rw [chainInput_blk4]
  apply ClaudeWCT.W9.Machine.Expand.hashInput_blk4 u A _ _ _ _ h10 h11 hA hA'
  · exact ⟨p0.trans rfl, p0'.trans rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [hh0]; unfold WCT9.ftsChainHeader
      rw [WCT9.ftsChainHeaderP_low, ftsChainLow_qQ index k j t st hk hidx hj ht hst]
    · rw [show A + 16 + 8 = A + 24 by omega, hh1]; unfold WCT9.ftsChainHeader
      rw [WCT9.ftsChainHeaderP_high]
  · exact ⟨p1.trans rfl, by rw [show A + 32 + 8 = A + 40 by omega]; exact p1'.trans rfl⟩
  · exact hv
theorem codeAt_left {im : Image} {p : Nat} {l1 l2 : List (BitVec 32)} (h : CodeAt im (pcOf p) (l1 ++ l2)) :
    CodeAt im (pcOf p) l1 := by
  have := CodeAt.drop_prefix (pre := []) (seg := l1) (post := l2) (by simpa using h)
  simpa using this
theorem codeAt_right {im : Image} {p : Nat} {l1 l2 : List (BitVec 32)} (h : CodeAt im (pcOf p) (l1 ++ l2)) :
    CodeAt im (pcOf (p + l1.length)) l2 := by
  have := CodeAt.drop_prefix (pre := l1) (seg := l2) (post := []) (by simpa using h)
  rwa [pcOf, ofNat_add_ofNat, show 0x1000 + 4 * p + 4 * l1.length = 0x1000 + 4 * (p + l1.length) by ring] at this
structure CRegs (B H X4 Q : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 B
  x28 : s.getReg .x28 = BitVec.ofNat 64 H
  x4 : s.getReg .x4 = BitVec.ofNat 64 X4
  x31 : s.getReg .x31 = BitVec.ofNat 64 Q
  x7 : s.getReg .x7 = BitVec.ofNat 64 1
  x13 : s.getReg .x13 = BitVec.ofNat 64 2
  x19 : s.getReg .x19 = BitVec.ofNat 64 3
  x5 : s.getReg .x5 = 0
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
def keepC (s u : MachineState) : Prop :=
  ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 → u.getReg r = s.getReg r
theorem keepC.refl (s : MachineState) : keepC s s := fun _ _ _ _ _ _ => rfl
theorem keepC.trans {s u w : MachineState} (h1 : keepC s u) (h2 : keepC u w) : keepC s w :=
  fun r a b c d e => (h2 r a b c d e).trans (h1 r a b c d e)
theorem CRegs.of_keep {B H X4 Q : Nat} {s u : MachineState} (h : CRegs B H X4 Q s) (hk : keepC s u) :
    CRegs B H X4 Q u :=
  ⟨(hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x8,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x28,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x4,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x31,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x7,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x13,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x19,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x5,
    (hk _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x11⟩
def chainWr (B t : Nat) (own : Bool) (A : Nat) : Prop :=
  A = B + offC t + 16 ∨ (B + offC t + 48 ≤ A ∧ A < B + offC t + 80) ∨
    (B + slotC t ≤ A ∧ A < B + slotC t + (if own then 16 else 32))
structure CMid (B H k index j t : Nat) (own : Bool) (s u : MachineState) (st : Nat) (val : Digest) (D : Nat) :
    Prop where
  regs : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) u
  x10 : u.getReg .x10 = BitVec.ofNat 64 (B + offC t)
  x12 : u.getReg .x12 = BitVec.ofNat 64 D
  keep : keepC s u
  hdr : u.getMem (BitVec.ofNat 64 (B + offC t + 16)) = BitVec.ofNat 64 (qQ k index j + qK t st)
  x4m : u.getMem (BitVec.ofNat 64 (B + offC t + 24)) = 0
  p0 : u.getMem (BitVec.ofNat 64 (B + offC t)) = 0
  p0' : u.getMem (BitVec.ofNat 64 (B + offC t + 8)) = 0
  p1 : u.getMem (BitVec.ofNat 64 (B + offC t + 32)) = 0
  p1' : u.getMem (BitVec.ofNat 64 (B + offC t + 40)) = 0
  val : DigAt u D val
  frame : Frame s u (chainWr B t own)
theorem offC_bounds (t : Nat) (ht : t < 6) : offC t % 64 = 0 ∧ 448 ≤ offC t ∧ offC t + 48 ≤ 816 := by
  unfold offC; omega
theorem slotC_bounds (t : Nat) (ht : t < 6) : slotC t % 16 = 0 ∧ 816 ≤ slotC t ∧ slotC t + 32 ≤ 960 := by
  unfold slotC; split <;> omega
theorem tb_chainHash {β : Type} {im : Image} {sk : BitVec 256} {u : MachineState} {A D : Nat}
    {k index j t st : Nat} {val : Digest} {W : Nat} {f : Digest → M β} {Q : β → MachineState → Prop}
    (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128) (ht : t < 6) (hst : st < 4)
    (hf : fetch im u = some (.base .ECALL)) (h5 : u.getReg .x5 = 0) (h10 : u.getReg .x10 = BitVec.ofNat 64 A)
    (h11 : u.getReg .x11 = BitVec.ofNat 64 64) (h12 : u.getReg .x12 = BitVec.ofNat 64 D)
    (hA8 : A % 8 = 0) (hAhi : A + 64 ≤ 2 ^ 24) (hD8 : D % 8 = 0) (hDhi : D + 32 ≤ 2 ^ 24)
    (p0 : u.getMem (BitVec.ofNat 64 A) = 0) (p0' : u.getMem (BitVec.ofNat 64 (A + 8)) = 0)
    (hh0 : u.getMem (BitVec.ofNat 64 (A + 16)) = BitVec.ofNat 64 (qQ k index j + qK t st))
    (hh1 : u.getMem (BitVec.ofNat 64 (A + 24)) = 0)
    (p1 : u.getMem (BitVec.ofNat 64 (A + 32)) = 0) (p1' : u.getMem (BitVec.ofNat 64 (A + 40)) = 0)
    (hv : DigAt u (A + 48) val)
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash u a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim im sk u (8 + W) (shortHash (WCT9.chainInput index k j t st val) >>= f) Q := by
  have hq := chain_hashIn hk hidx hj ht hst h10 h11 hA8 (by omega) p0 p0' hh0 hh1 p1 p1' hv
  have hv' : hashArgumentsValid u = true :=
    VLib.hashArgs_of u A 64 D h10 h11 h12 hA8 (by decide) (by omega) hD8 hDhi
  have := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk) (W := W) (f := f) (Q := Q)
    hf h5 hv' hq h
  have hb : (toQ (pad64 (WCT9.chainInput index k j t st val))).blocks = 1 := by
    rw [chainInput_blk4, VLib.blocks_blk4]
  exact this.mono (by rw [hb]) (fun _ _ h => h)
def PadsZ (B t : Nat) (u : MachineState) : Prop :=
  u.getMem (BitVec.ofNat 64 (B + offC t)) = 0 ∧ u.getMem (BitVec.ofNat 64 (B + offC t + 8)) = 0 ∧
    u.getMem (BitVec.ofNat 64 (B + offC t + 32)) = 0 ∧ u.getMem (BitVec.ofNat 64 (B + offC t + 40)) = 0 ∧
    u.getMem (BitVec.ofNat 64 (B + offC t + 24)) = 0
theorem writeHash_get_out {t : MachineState} {a : BitVec 256} {D A : Nat} (h12 : t.getReg .x12 = BitVec.ofNat 64 D)
    (hD : D + 32 < 2 ^ 64) (hA : A < 2 ^ 64) (hn : A + 8 ≤ D ∨ D + 32 ≤ A) :
    (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [getMem_writeHash t a D A h12 hD hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem head_hash {β : Type} {im : Image} {sk : BitVec 256} {p t st a2 : Nat} {own : Bool} (ht : t < 6)
    (hst : st < 4) (ha : a2 = offC t + 48 ∨ (a2 = slotC t ∧ (own = false ∨ t = 0)))
    (hc : CodeAt im (pcOf p) (headW t st a2))
    {B H k index j : Nat} (hb : Bnd B H) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    (s : MachineState) (hpc : s.pc = pcOf p) (hr : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) s)
    (hpad : PadsZ B t s) (v : Digest) (hv : DigAt s (B + offC t + 48) v)
    {W : Nat} {f : Digest → M β} {Q : β → MachineState → Prop}
    (hK : ∀ (v' : Digest) (w : MachineState), w.pc = pcOf (p + 5) →
      CMid B H k index j t own s w st v' (B + a2) → TBSim im sk w W (f v') Q) :
    TBSim im sk s (4 + (8 + W)) (shortHash (WCT9.chainInput index k j t st v) >>= f) Q := by
  have hob := offC_bounds t ht
  have hsb := slotC_bounds t ht
  have hbb := hb.bhi
  have hb8 := hb.b8
  have ha' : a2 = offC t + 48 ∨ a2 = slotC t := by rcases ha with h | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]
  have ha2 : a2 % 8 = 0 ∧ offC t + 48 ≤ a2 ∧ a2 + 32 ≤ 1024 := by
    rcases ha' with rfl | rfl <;> omega
  obtain ⟨u1, s1, p1, e1, x10_1, x12_1, keep1, m16, f1⟩ :=
    head_spec ht hst ha' hc s hpc hr.x8 hr.x31 hb.b8 hb.bhi
  have k1 : keepC s u1 := fun r h3 h10 h12 h14 h25 => keep1 r h10 h12 h25
  have r1 := hr.of_keep k1
  have fs1 : ∀ o, o + 8 ≤ 1024 → o ≠ offC t + 16 →
      u1.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) :=
    fun o ho h1 => f1 (B + o) (by omega) (by omega)
  refine TBSim.steps s1 (tb_chainHash (A := B + offC t) (D := B + a2) hk hidx hj ht hst e1 r1.x5 x10_1 r1.x11 x12_1
    (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun a => ?_))
  · rw [fs1 _ (by omega) (by omega)]; exact hpad.1
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.1
  · rw [m16]
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.2
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.2.1
  · rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.1
  · rw [Nat.add_assoc]
    exact ⟨(fs1 _ (by omega) (by omega)).trans hv.1,
      by rw [Nat.add_assoc, fs1 _ (by omega) (by omega)]; have := hv.2; rwa [Nat.add_assoc] at this⟩
  · set w := writeHash u1 a
    have hw : ∀ o, o + 8 ≤ 1024 → (o + 8 ≤ a2 ∨ a2 + 32 ≤ o) →
        w.getMem (BitVec.ofNat 64 (B + o)) = u1.getMem (BitVec.ofNat 64 (B + o)) :=
      fun o ho hn => writeHash_get_out x12_1 (by omega) (by omega) (by omega)
    refine hK _ w ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p1, pcOf_add4]
    · exact r1.of_keep (fun r _ _ _ _ _ => getReg_writeHash u1 a r)
    · rw [getReg_writeHash]; exact x10_1
    · rw [getReg_writeHash]; exact x12_1
    · exact k1.trans (fun r _ _ _ _ _ => getReg_writeHash u1 a r)
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), ← Nat.add_assoc, m16]
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.2
    · rw [hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.2.1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs1 _ (by omega) (by omega)]; exact hpad.2.2.2.1
    · exact DigAt.writeHash_lo u1 a _ x12_1 (by omega)
    · have fw := Frame.writeHash u1 a (B + a2) x12_1 (by omega)
      refine (f1.trans fw).mono (fun A _ hA => ?_)
      rcases hA with h | h
      · exact Or.inl h
      · rcases ha with rfl | ⟨rfl, ho⟩
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · rcases ho with ho | rfl
          · right; right; rw [ho]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
          · right; left; simp only [offC, slotC] at h ⊢; norm_num at h ⊢; omega
def rdst (t step : Nat) (own : Bool) : Nat :=
  match rungDst t step own with
  | some d => d
  | none => offC t + 48
theorem rdst_cases (t step : Nat) (own : Bool) :
    rdst t step own = offC t + 48 ∨ (rdst t step own = slotC t ∧ own = false ∧ t ≠ 0) := by
  unfold rdst rungDst
  split_ifs with h
  · exact Or.inr ⟨rfl, h.2.1, h.2.2⟩
  · exact Or.inl rfl
theorem rung_hash {β : Type} {im : Image} {sk : BitVec 256} {q t step : Nat} {own : Bool} (ht : t < 6)
    (hs : step = 1 ∨ step = 2 ∨ step = 3) (hc : CodeAt im (pcOf q) (rungW step (rungDst t step own)))
    {B H k index j : Nat} (hb : Bnd B H) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    {s u : MachineState} {val : Digest} (hpc : u.pc = pcOf q)
    (hm : CMid B H k index j t own s u (step - 1) val (B + offC t + 48))
    {W : Nat} {f : Digest → M β} {Q : β → MachineState → Prop}
    (hK : ∀ (v' : Digest) (w : MachineState), w.pc = pcOf (q + (rungW step (rungDst t step own)).length) →
      CMid B H k index j t own s w step v' (B + rdst t step own) → TBSim im sk w W (f v') Q) :
    TBSim im sk u (2 + (8 + W)) (shortHash (WCT9.chainInput index k j t step val) >>= f) Q := by
  have hob := offC_bounds t ht
  have hsb := slotC_bounds t ht
  have hbb := hb.bhi
  have hb8 := hb.b8
  have hrd := rdst_cases t step own
  have hrd' : rdst t step own % 8 = 0 ∧ offC t + 48 ≤ rdst t step own ∧ rdst t step own + 32 ≤ 1024 := by
    rcases hrd with h | ⟨h, _⟩ <;> rw [h] <;> omega
  obtain ⟨u2, s2, p2, e2, x12_2, keep2, m16, f2⟩ :=
    rung_spec own ht hs hc u hpc hm.regs.x8 hm.x10 (by omega) (by omega)
  have hL : 2 ≤ (rungW step (rungDst t step own)).length ∧ (rungW step (rungDst t step own)).length ≤ 3 := by
    cases rungDst t step own <;> simp [rungW]
  have k2 : keepC u u2 := fun r _ _ h12 _ _ => keep2 r h12
  have r2 := hm.regs.of_keep k2
  have x10_2 : u2.getReg .x10 = BitVec.ofNat 64 (B + offC t) := (keep2 _ (by decide)).trans hm.x10
  have x12' : u2.getReg .x12 = BitVec.ofNat 64 (B + rdst t step own) := by
    rw [x12_2]; unfold rdst
    cases h : rungDst t step own with
    | some d => rfl
    | none => have := hm.x12; rwa [Nat.add_assoc] at this
  have fs2 : ∀ o, o + 8 ≤ 1024 → o ≠ offC t + 16 →
      u2.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) :=
    fun o ho h1 => f2 (B + o) (by omega) (by omega)
  have hqm : qQ k index j % 65536 = 0 ∧ qQ k index j < 2 ^ 63 := by unfold qQ; omega
  have hdr2 : u2.getMem (BitVec.ofNat 64 (B + offC t + 16)) = BitVec.ofNat 64 (qQ k index j + qK t step) := by
    rw [m16, hm.hdr]
    rcases hs with rfl | rfl | rfl
    · simp only [if_true, hm.regs.x7]; exact step_byte _ t 0 1 hqm.1 hqm.2 ht (by decide) (by decide)
    · simp only [show ¬ (2 = 1) by decide, if_false, if_true, hm.regs.x13]
      exact step_byte _ t 1 2 hqm.1 hqm.2 ht (by decide) (by decide)
    · simp only [show ¬ (3 = 1) by decide, show ¬ (3 = 2) by decide, if_false, hm.regs.x19]
      exact step_byte _ t 2 3 hqm.1 hqm.2 ht (by decide) (by decide)
  refine (TBSim.steps s2 (tb_chainHash (A := B + offC t) (D := B + rdst t step own) (W := W) hk hidx hj ht
    (by rcases hs with rfl | rfl | rfl <;> decide) e2 r2.x5
    x10_2 r2.x11 x12' (by omega) (by omega) (by omega) (by omega) ?_ ?_ hdr2 ?_ ?_ ?_ ?_ (fun a => ?_))).mono
    (by omega) (fun _ _ h => h)
  · rw [fs2 _ (by omega) (by omega)]; exact hm.p0
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p0'
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.x4m
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1
  · rw [Nat.add_assoc, fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1'
  · rw [Nat.add_assoc]
    refine ⟨?_, ?_⟩
    · rw [fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.val.1
    · rw [Nat.add_assoc, fs2 _ (by omega) (by omega)]; have := hm.val.2; rwa [Nat.add_assoc, Nat.add_assoc] at this
  · set w := writeHash u2 a
    have hw : ∀ o, o + 8 ≤ 1024 → (o + 8 ≤ rdst t step own ∨ rdst t step own + 32 ≤ o) →
        w.getMem (BitVec.ofNat 64 (B + o)) = u2.getMem (BitVec.ofNat 64 (B + o)) :=
      fun o ho hn => writeHash_get_out x12' (by omega) (by omega) (by omega)
    refine hK _ w ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p2, pcOf_add4, show q + ((rungW step (rungDst t step own)).length - 1) + 1 = q + (rungW step (rungDst t step own)).length by omega]
    · exact r2.of_keep (fun r _ _ _ _ _ => getReg_writeHash u2 a r)
    · rw [getReg_writeHash]; exact x10_2
    · rw [getReg_writeHash]; exact x12'
    · exact (hm.keep.trans k2).trans (fun r _ _ _ _ _ => getReg_writeHash u2 a r)
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), ← Nat.add_assoc]; exact hdr2
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.x4m
    · rw [hw _ (by omega) (by omega), fs2 _ (by omega) (by omega)]; exact hm.p0
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p0'
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1
    · rw [Nat.add_assoc, hw _ (by omega) (by omega), fs2 _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.p1'
    · exact DigAt.writeHash_lo u2 a _ x12' (by omega)
    · have fw := Frame.writeHash u2 a (B + rdst t step own) x12' (by omega)
      refine ((hm.frame.trans f2).trans fw).mono (fun A _ hA => ?_)
      rcases hA with (h | h) | h
      · exact h
      · exact Or.inl h
      · rcases hrd with he | ⟨he, ho, _⟩
        · rw [he] at h; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · rw [he] at h; right; right; rw [ho]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
def dfin (t : Nat) (own : Bool) : Nat := if own then offC t + 48 else slotC t
theorem a2C_one (t : Nat) (own : Bool) : a2C t 1 own = dfin t own := by
  unfold a2C dfin; simp
theorem rdst_three (t : Nat) (own : Bool) : rdst t 3 own = dfin t own := by
  unfold rdst rungDst dfin
  cases own
  · by_cases h : t = 0
    · subst h; simp [offC, slotC]
    · simp [h]
  · simp
def ChainPost (B H k index j t : Nat) (own : Bool) (s : MachineState) (q : Nat) (e : Digest) (u : MachineState) : Prop :=
  u.pc = pcOf q ∧ DigAt u (B + slotC t) e ∧ CRegs B H (index + 2 ^ 32 * j) (qQ k index j) u ∧ keepC s u ∧ Frame s u (chainWr B t own)
theorem chain_finish {im : Image} {sk : BitVec 256} {q t : Nat} {own : Bool} (ht : t < 6)
    (hown : own = true → 0 < t ∧ t < 5) (hc : CodeAt im (pcOf q) (if own then copyW t else []))
    {B H k index j : Nat} (hb : Bnd B H) {s u : MachineState} {e : Digest} (hpc : u.pc = pcOf q)
    (hm : CMid B H k index j t own s u 3 e (B + dfin t own)) :
    TBSim im sk u 4 (pure e : M Digest)
      (ChainPost B H k index j t own s (q + (if own then copyW t else []).length)) := by
  cases own with
  | false =>
    simp only [dfin, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero] at hm ⊢
    exact (TBSim.pure ⟨hpc, hm.val, hm.regs, hm.keep, hm.frame⟩).mono (by omega) (fun _ _ h => h)
  | true =>
    obtain ⟨h1, h5⟩ := hown rfl
    simp only [dfin, ↓reduceIte] at hm hc ⊢
    have hob := offC_bounds t ht
    have hsb := slotC_bounds t ht
    have hbb := hb.bhi
    have hb8 := hb.b8
    obtain ⟨w, sw, pw, kw, m0, m8, fw⟩ := copy_spec h1 h5 hc u hpc hm.regs.x8 (by omega) hb.bhi
    have kk : keepC u w := fun r h3 _ _ h14 _ => kw r h3 h14
    have hv : DigAt u (B + offC t + 48) e := by have := hm.val; rwa [← Nat.add_assoc] at this
    have h56 : B + offC t + 48 + 8 = B + offC t + 56 := by omega
    refine TBSim.steps sw (TBSim.pure ⟨by rw [pw]; simp [copyW], ⟨?_, ?_⟩, hm.regs.of_keep kk, hm.keep.trans kk, ?_⟩)
    · rw [m0]; exact hv.1
    · rw [m8, ← h56]; exact hv.2
    · refine (hm.frame.trans fw).mono (fun A _ hA => ?_)
      rcases hA with h | h | h
      · exact h
      · right; right; simp only [↓reduceIte]; omega
      · right; right; simp only [↓reduceIte]; omega
def chainCost : Nat := 46
theorem chain_tb {im : Image} {sk : BitVec 256} {p t d : Nat} {own : Bool} (ht : t < 6) (hd1 : 1 ≤ d)
    (hd4 : d ≤ 4) (hown : own = true → 0 < t ∧ t < 5) (hc : CodeAt im (pcOf p) (chainW t d own))
    {B H k index j : Nat} (hb : Bnd B H) (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    (s : MachineState) (hpc : s.pc = pcOf p) (hr : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) s)
    (hpad : PadsZ B t s) (v : Digest) (hv : DigAt s (B + offC t + 48) v) :
    TBSim im sk s chainCost (WCT9.chain index k j t (4 - d) d v)
      (ChainPost B H k index j t own s (p + (chainW t d own).length)) := by
  have hc1 := codeAt_left (codeAt_left hc)
  have hc23 := codeAt_right (codeAt_left hc)
  have hc4 := codeAt_right hc
  have hlenW : (chainW t d own).length = 5 + (rungsW t d own).length + (if own then copyW t else []).length := by
    simp [chainW, headW]; omega
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  have hdn1 : rungDst t 1 own = none := by simp [rungDst]
  have hdn2 : rungDst t 2 own = none := by simp [rungDst]
  have hrd1 : rdst t 1 own = offC t + 48 := by simp [rdst, hdn1]
  have hrd2 : rdst t 2 own = offC t + 48 := by simp [rdst, hdn2]
  rcases hd with rfl | rfl | rfl | rfl
  ·
    have hsrc : WCT9.chain index k j t (4 - 1) 1 v =
        (shortHash (WCT9.chainInput index k j t 3 v) >>= fun v1 => pure v1) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have ha : a2C t 1 own = offC t + 48 ∨ (a2C t 1 own = slotC t ∧ (own = false ∨ t = 0)) := by
      unfold a2C; cases own <;> simp
    refine (head_hash (st := 3) (a2 := a2C t 1 own) (own := own) ht (by decide) ha hc1 hb hk hidx hj s hpc hr
      hpad v hv (W := 4) (fun v' w pw hw => ?_)).mono (by unfold chainCost; omega)
      (fun _ _ h => h)
    have hr0 : rungsW t 1 own = [] := by simp [rungsW]
    rw [a2C_one] at hw
    have := chain_finish (sk := sk) ht hown (by rw [hr0] at hc4; simpa [headW] using hc4) hb pw hw
    rw [hlenW, hr0]; simpa [headW, Nat.add_assoc] using this
  ·
    have hsrc : WCT9.chain index k j t (4 - 2) 2 v =
        (shortHash (WCT9.chainInput index k j t 2 v) >>= fun v1 =>
          shortHash (WCT9.chainInput index k j t 3 v1) >>= fun v2 => pure v2) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have hr2 : rungsW t 2 own = rungW 3 (rungDst t 3 own) := by simp [rungsW]
    have ha2 : a2C t 2 own = offC t + 48 := by simp [a2C]
    rw [ha2] at hc1
    rw [hr2] at hc23 hc4
    refine (head_hash (st := 2) (a2 := offC t + 48) (own := own) ht (by decide) (Or.inl rfl) hc1 hb hk hidx hj s hpc
      hr hpad v hv (W := 2 + (8 + 4)) (fun v1 w1 pw1 hw1 => ?_)).mono
      (by unfold chainCost; omega) (fun _ _ h => h)
    rw [← Nat.add_assoc] at hw1
    refine rung_hash (step := 3) (own := own) ht (Or.inr (Or.inr rfl)) (by simpa [headW] using hc23) hb hk hidx hj
      (by rw [pw1]) hw1 (fun v2 w2 pw2 hw2 => ?_)
    rw [rdst_three] at hw2
    have hc4' : CodeAt im (pcOf (p + 5 + (rungW 3 (rungDst t 3 own)).length)) (if own then copyW t else []) := by
      have e : p + 5 + (rungW 3 (rungDst t 3 own)).length =
          p + (headW t (4 - 2) (a2C t 2 own) ++ rungW 3 (rungDst t 3 own)).length := by
        simp only [headW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hc4
    have := chain_finish (sk := sk) ht hown hc4' hb pw2 hw2
    rw [hlenW, hr2]; simpa [headW, Nat.add_assoc] using this
  ·
    have hsrc : WCT9.chain index k j t (4 - 3) 3 v =
        (shortHash (WCT9.chainInput index k j t 1 v) >>= fun v1 =>
          shortHash (WCT9.chainInput index k j t 2 v1) >>= fun v2 =>
            shortHash (WCT9.chainInput index k j t 3 v2) >>= fun v3 => pure v3) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have hr3 : rungsW t 3 own = rungW 2 (rungDst t 2 own) ++ rungW 3 (rungDst t 3 own) := by
      simp [rungsW, List.range']
    have ha3 : a2C t 3 own = offC t + 48 := by simp [a2C]
    rw [ha3] at hc1
    rw [hr3] at hc23 hc4
    have hc2 := codeAt_left hc23
    have hc3 := codeAt_right hc23
    refine (head_hash (st := 1) (a2 := offC t + 48) (own := own) ht (by decide) (Or.inl rfl) hc1 hb hk hidx hj s hpc
      hr hpad v hv (W := 2 + (8 + (2 + (8 + 4)))) (fun v1 w1 pw1 hw1 => ?_)).mono
      (by unfold chainCost; omega) (fun _ _ h => h)
    rw [← Nat.add_assoc] at hw1
    refine rung_hash (step := 2) (own := own) ht (Or.inr (Or.inl rfl)) (by simpa [headW] using hc2) hb hk hidx hj
      (by rw [pw1]) hw1 (fun v2 w2 pw2 hw2 => ?_)
    rw [hrd2, ← Nat.add_assoc] at hw2
    refine rung_hash (step := 3) (own := own) ht (Or.inr (Or.inr rfl)) (by simpa [headW, Nat.add_assoc] using hc3) hb
      hk hidx hj (by rw [pw2]; simp [headW, Nat.add_assoc]) hw2 (fun v3 w3 pw3 hw3 => ?_)
    rw [rdst_three] at hw3
    have hc4' : CodeAt im (pcOf (p + 5 + (rungW 2 (rungDst t 2 own)).length + (rungW 3 (rungDst t 3 own)).length))
        (if own then copyW t else []) := by
      have e : p + 5 + (rungW 2 (rungDst t 2 own)).length + (rungW 3 (rungDst t 3 own)).length =
          p + (headW t (4 - 3) (a2C t 3 own) ++ (rungW 2 (rungDst t 2 own) ++ rungW 3 (rungDst t 3 own))).length := by
        simp only [headW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hc4
    have := chain_finish (sk := sk) ht hown hc4' hb pw3 hw3
    rw [hlenW, hr3]; simpa [headW, Nat.add_assoc] using this
  ·
    have hsrc : WCT9.chain index k j t (4 - 4) 4 v =
        (shortHash (WCT9.chainInput index k j t 0 v) >>= fun v1 =>
          shortHash (WCT9.chainInput index k j t 1 v1) >>= fun v2 =>
            shortHash (WCT9.chainInput index k j t 2 v2) >>= fun v3 =>
              shortHash (WCT9.chainInput index k j t 3 v3) >>= fun v4 => pure v4) := by
      simp [WCT9.chain, List.range', List.foldlM]
    rw [hsrc]
    have hr4 : rungsW t 4 own =
        rungW 1 (rungDst t 1 own) ++ (rungW 2 (rungDst t 2 own) ++ rungW 3 (rungDst t 3 own)) := by
      simp [rungsW, List.range']
    have ha4 : a2C t 4 own = offC t + 48 := by simp [a2C]
    rw [ha4] at hc1
    rw [hr4] at hc23 hc4
    have hc2 := codeAt_left hc23
    have hc3 := codeAt_left (codeAt_right hc23)
    have hc3' := codeAt_right (codeAt_right hc23)
    refine (head_hash (st := 0) (a2 := offC t + 48) (own := own) ht (by decide) (Or.inl rfl) hc1 hb hk hidx hj s hpc
      hr hpad v hv (W := 2 + (8 + (2 + (8 + (2 + (8 + 4)))))) (fun v1 w1 pw1 hw1 => ?_)).mono
      (by unfold chainCost; omega) (fun _ _ h => h)
    rw [← Nat.add_assoc] at hw1
    refine rung_hash (step := 1) (own := own) ht (Or.inl rfl) (by simpa [headW] using hc2) hb hk hidx hj
      (by rw [pw1]) hw1 (fun v2 w2 pw2 hw2 => ?_)
    rw [hrd1, ← Nat.add_assoc] at hw2
    refine rung_hash (step := 2) (own := own) ht (Or.inr (Or.inl rfl)) (by simpa [headW, Nat.add_assoc] using hc3) hb
      hk hidx hj (by rw [pw2]; simp [headW, Nat.add_assoc]) hw2 (fun v3 w3 pw3 hw3 => ?_)
    rw [hrd2, ← Nat.add_assoc] at hw3
    refine rung_hash (step := 3) (own := own) ht (Or.inr (Or.inr rfl)) (by simpa [headW, Nat.add_assoc] using hc3')
      hb hk hidx hj (by rw [pw3]; simp [headW, Nat.add_assoc]) hw3 (fun v4 w4 pw4 hw4 => ?_)
    rw [rdst_three] at hw4
    have hc4' : CodeAt im (pcOf (p + 5 + (rungW 1 (rungDst t 1 own)).length + (rungW 2 (rungDst t 2 own)).length +
        (rungW 3 (rungDst t 3 own)).length)) (if own then copyW t else []) := by
      have e : p + 5 + (rungW 1 (rungDst t 1 own)).length + (rungW 2 (rungDst t 2 own)).length +
          (rungW 3 (rungDst t 3 own)).length =
          p + (headW t (4 - 4) (a2C t 4 own) ++
            (rungW 1 (rungDst t 1 own) ++ (rungW 2 (rungDst t 2 own) ++ rungW 3 (rungDst t 3 own)))).length := by
        simp only [headW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [e]; exact hc4
    have := chain_finish (sk := sk) ht hown hc4' hb pw4 hw4
    rw [hlenW, hr4]; simpa [headW, Nat.add_assoc] using this
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M shortHash)
set_option linter.unusedSimpArgs false
def jalTo (w : BitVec 32) (n : Nat) : Option Nat :=
  match decodeInstruction w with
  | some (.base (.JAL .x0 imm)) =>
    let a := (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64
    if 0x1000 ≤ a ∧ a % 4 = 0 then some ((a - 0x1000) / 4) else none
  | _ => none
theorem jalTo_sound {w : BitVec 32} {n m : Nat} (h : jalTo w n = some m) :
    ∃ imm, decodeInstruction w = some (.base (.JAL .x0 imm)) ∧
      (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64 := by
  unfold jalTo at h
  split at h
  · rename_i imm hd
    refine ⟨imm, hd, ?_⟩
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
      rw [Nat.mod_eq_of_lt (a := 0x1000 + 4 * _) (by omega)]
      omega
    · cases h
  · cases h
def walk (z : List Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, t, n =>
    match expLook n with
    | none => none
    | some w =>
      match jalTo w n with
      | some m => (walk z fuel t m).map (· + 1)
      | none =>
        if t < 6 then
          if z.getD t 0 = 0 then walk z fuel (t + 1) n
          else if windowOK n (chainW t (z.getD t 0) (ownC z t)) then
            (walk z fuel (t + 1) (n + (chainW t (z.getD t 0) (ownC z t)).length)).map (· + chainCost)
          else none
        else if windowOK n leafW then some 6 else none
def chainsFrom (index k j : Nat) (z : List Nat) (vals : Nat → Digest) (t : Nat) : M (List Digest) :=
  (List.range' t (6 - t)).mapM fun i => WCT9.chain index k j i (4 - z.getD i 0) (z.getD i 0) (vals i)
theorem chainsFrom_succ (index k j : Nat) (z : List Nat) (vals : Nat → Digest) (t : Nat) (ht : t < 6) :
    chainsFrom index k j z vals t =
      (WCT9.chain index k j t (4 - z.getD t 0) (z.getD t 0) (vals t) >>= fun e =>
        chainsFrom index k j z vals (t + 1) >>= fun es => pure (e :: es)) := by
  unfold chainsFrom
  rw [show 6 - t = (6 - (t + 1)) + 1 by omega, List.range'_succ, List.mapM_cons]
theorem chainsFrom_six (index k j : Nat) (z : List Nat) (vals : Nat → Digest) :
    chainsFrom index k j z vals 6 = pure [] := rfl
theorem chain_zero (index k j t : Nat) (v : Digest) : WCT9.chain index k j t (4 - 0) 0 v = pure v := rfl
def chainsWr (B : Nat) (z : List Nat) (t : Nat) (A : Nat) : Prop :=
  ∃ t', t' < t ∧ z.getD t' 0 ≠ 0 ∧ chainWr B t' (ownC z t') A
structure RPre (B H k index j : Nat) (z : List Nat) (vals : Nat → Digest) (s0 : MachineState) : Prop where
  bnd : Bnd B H
  sep : B + 1024 + 2048 ≤ H
  hk : k < 9
  hidx : index < 2 ^ 31
  hj : j < 128
  regs : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) s0
  pads : ∀ t, t < 6 → PadsZ B t s0
  valAt : ∀ t, t < 6 → DigAt s0 (B + offC t + 48) (vals t)
  passive : ∀ t, t < 6 → z.getD t 0 = 0 → DigAt s0 (B + slotC t) (vals t)
  digits : ∀ t, t < 6 → z.getD t 0 ≤ 4
structure RInv (B H k index j : Nat) (z : List Nat) (s0 : MachineState) (t : Nat) (pre : List Digest)
    (u : MachineState) : Prop where
  len : pre.length = t
  regs : CRegs B H (index + 2 ^ 32 * j) (qQ k index j) u
  keep : keepC s0 u
  frame : Frame s0 u (chainsWr B z t)
  done : ∀ t', t' < t → DigAt u (B + slotC t') (pre.getD t' 0)
structure RPost (B k index j : Nat) (z : List Nat) (s0 : MachineState) (ends : List Digest) (w : MachineState) :
    Prop where
  pc : w.pc = s0.getReg .x23 &&& 0xfffffffffffffffe#64
  a0 : w.getReg .x10 = BitVec.ofNat 64 (B + 816)
  a1 : w.getReg .x11 = BitVec.ofNat 64 128
  keep : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 → w.getReg r = s0.getReg r
  len : ends.length = 6
  ends : ∀ t, t < 6 → DigAt w (B + slotC t) (ends.getD t 0)
  h0 : w.getMem (BitVec.ofNat 64 (B + 832)) = BitVec.ofNat 64 (qQ k index j + 1537)
  h1 : w.getMem (BitVec.ofNat 64 (B + 840)) = 0
  frame : Frame s0 w (fun A => chainsWr B z 6 A ∨ A = B + 832 ∨ A = B + 840)
theorem offC_lt_slot (t t' : Nat) (ht : t < 6) (ht' : t' < 6) : offC t + 80 ≤ slotC t' ∨ (t = 0 ∧ t' = 0) := by
  unfold offC slotC; split <;> omega
theorem slot_free_later {B t t'' : Nat} {own : Bool} (h : t < t'') (h7 : t'' < 6) (o : Nat) (ho : o < 16) :
    ¬ chainWr B t'' own (B + slotC t + o) := by
  unfold chainWr offC slotC
  split_ifs <;> omega
theorem block_free_earlier {B t' t : Nat} {own : Bool} (h : t' < t) (h7 : t < 6) (o : Nat) (ho : o < 64)
    : ¬ chainWr B t' own (B + offC t + o) := by
  unfold chainWr offC slotC
  split_ifs <;> omega
theorem passive_free_earlier {B t' t : Nat} (z : List Nat) (h : t' < t) (h7 : t < 6) (hp : z.getD t 0 = 0)
    (o : Nat) (ho : o < 16) : ¬ chainWr B t' (ownC z t') (B + slotC t + o) := by
  unfold chainWr offC slotC
  by_cases ht1 : t = t' + 1
  · subst ht1
    by_cases h0 : t' = 0
    · subst h0; norm_num; split_ifs <;> omega
    · have hown : ownC z t' = true := by
        simp only [ownC, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨by omega, by omega⟩, hp⟩
      rw [hown]; simp only [↓reduceIte]; split_ifs <;> omega
  · split_ifs <;> omega
theorem leafHdr_free {B t : Nat} (o : Nat) (ho : o < 16) :
    B + slotC t + o ≠ B + 832 ∧ B + slotC t + o ≠ B + 840 := by
  unfold slotC; split <;> omega
/-- The leaf pad slot (848..864) is never written by a chain. -/
theorem leafPad_free {B t : Nat} {own : Bool} (ht : t < 6) (o : Nat) (ho : o < 16) :
    ¬ chainWr B t own (B + 848 + o) := by
  unfold chainWr offC slotC
  split_ifs <;> omega
theorem expLook_lt {m : Nat} {w : BitVec 32} (h : expLook m = some w) : 1024 ≤ m ∧ m < 173 * 256 := by
  unfold expLook at h
  split at h
  · rename_i hm
    refine ⟨hm, ?_⟩
    by_contra hc
    rw [List.getD_eq_default _ _ (by rw [expChunks_length]; omega)] at h
    simp at h
  · cases h
theorem window_bound {n : Nat} {ws : List (BitVec 32)} (h : windowOK n ws = true) (hne : ws ≠ []) :
    n + ws.length ≤ 173 * 256 := by
  unfold windowOK at h
  have hl : 0 < ws.length := List.length_pos_of_ne_nil hne
  have := List.all_eq_true.mp h (ws.length - 1) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  have := expLook_lt this
  omega
theorem codeAt_win {im : Image} (hc : NewCodeAt im) {n : Nat} {ws : List (BitVec 32)} (h : windowOK n ws = true)
    (hne : ws ≠ []) : CodeAt im (pcOf n) ws :=
  codeAt_of_window hc (by have := window_bound h hne; omega) h
theorem codeAt_one {im : Image} (hc : NewCodeAt im) {n : Nat} {w : BitVec 32} (h : expLook n = some w) :
    CodeAt im (pcOf n) [w] :=
  codeAt_of_look (expLook_ok hc) n [w] (by have := expLook_lt h; simp; omega) (fun i hi => by
    simp at hi; subst hi; simpa using h)
theorem getD_append_lt {α : Type} (l1 l2 : List α) (d : α) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_len {α : Type} (l : List α) (a : α) (d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]
theorem chainNe (z : List Nat) (t : Nat) (h : z.getD t 0 ≠ 0) (h3 : z.getD t 0 ≤ 4) :
    1 ≤ z.getD t 0 ∧ z.getD t 0 ≤ 4 := ⟨by omega, h3⟩
theorem ownC_spec (z : List Nat) (t : Nat) : ownC z t = true → 0 < t ∧ t < 5 := by
  simp only [ownC, Bool.and_eq_true, decide_eq_true_eq]; exact fun h => h.1
theorem hbank_free {B H : Nat} {z : List Nat} {t A : Nat} (ht : t ≤ 6) (hs : B + 1024 + 2048 ≤ H) (hA : H - 2048 ≤ A) :
    ¬ chainsWr B z t A := by
  rintro ⟨t', ht', _, h⟩
  unfold chainWr offC slotC at h
  split_ifs at h <;> omega
theorem walk_tb {im : Image} (hcode : NewCodeAt im) {sk : BitVec 256} {B H k index j : Nat} {z : List Nat}
    {vals : Nat → Digest} {s0 : MachineState} (hpre : RPre B H k index j z vals s0) :
    ∀ fuel t n c (pre : List Digest) (u : MachineState), walk z fuel t n = some c → t ≤ 6 → u.pc = pcOf n →
      RInv B H k index j z s0 t pre u →
      TBSim im sk u c (chainsFrom index k j z vals t) (fun rest w => RPost B k index j z s0 (pre ++ rest) w) := by
  have hb := hpre.bnd
  have hbb := hb.bhi
  have hsep := hpre.sep
  intro fuel
  induction fuel with
  | zero => intro t n c pre u hw; simp [walk] at hw
  | succ fuel ih =>
    intro t n c pre u hw ht hpc hI
    simp only [walk] at hw
    split at hw
    · cases hw
    · rename_i w hlook
      split at hw
      ·
        rename_i m hjal
        obtain ⟨c', hw', rfl⟩ : ∃ c', walk z fuel t m = some c' ∧ c = c' + 1 := by
          cases h : walk z fuel t m <;> simp_all
        obtain ⟨imm, hd, hoff⟩ := jalTo_sound hjal
        have hs := jal_x0_step (codeAt_one hcode hlook) hd hoff u hpc
        have hI' : RInv B H k index j z s0 t pre (u.setPC (pcOf m)) :=
          ⟨hI.len, ⟨hI.regs.x8, hI.regs.x28, hI.regs.x4, hI.regs.x31, hI.regs.x7, hI.regs.x13, hI.regs.x19, hI.regs.x5,
            hI.regs.x11⟩,
            fun r a b c d e => hI.keep r a b c d e, fun A hA hn => hI.frame A hA hn,
            fun t' ht' => hI.done t' ht'⟩
        exact (TBSim.steps hs (ih t m c' pre _ hw' ht rfl hI')).mono (by omega) (fun _ _ h => h)
      · rename_i hjal
        split at hw
        · rename_i ht7
          split at hw
          ·
            rename_i hz
            rw [chainsFrom_succ _ _ _ _ _ _ ht7, hz, chain_zero, pure_bind]
            have hdone : DigAt u (B + slotC t) (vals t) := by
              have hP := hpre.passive t ht7 hz
              have hs := slotC_bounds t ht7
              refine ⟨(hI.frame _ (by omega) (fun ⟨t', h1, _, h2⟩ =>
                passive_free_earlier z h1 ht7 hz 0 (by omega) (by simpa using h2))).trans hP.1, ?_⟩
              rw [hI.frame _ (by omega) (fun ⟨t', h1, _, h2⟩ =>
                passive_free_earlier z h1 ht7 hz 8 (by omega) h2)]
              exact hP.2
            have hI' : RInv B H k index j z s0 (t + 1) (pre ++ [vals t]) u :=
              ⟨by simp [hI.len], hI.regs, hI.keep, hI.frame.mono (fun A _ ⟨t', h1, h2, h3⟩ => ⟨t', by omega, h2, h3⟩),
                fun t' ht' => by
                  rcases Nat.lt_or_ge t' t with h | h
                  · rw [getD_append_lt _ _ _ _ (by rw [hI.len]; exact h)]; exact hI.done t' h
                  · have : t' = t := by omega
                    subst this; rw [← hI.len, getD_append_len, hI.len]; exact hdone⟩
            refine (TBSim.bind (W₂ := 0) (ih (t + 1) n c _ u hw (by omega) hpc hI') (fun es w hw' =>
              TBSim.pure (by simpa using hw'))).mono (by omega) (fun _ _ h => h)
          · split at hw
            ·
              rename_i hz hwin
              obtain ⟨c', hw', rfl⟩ : ∃ c', walk z fuel (t + 1) (n + (chainW t (z.getD t 0) (ownC z t)).length)
                  = some c' ∧ c = c' + chainCost := by
                cases h : walk z fuel (t + 1) (n + (chainW t (z.getD t 0) (ownC z t)).length) <;> simp_all
              have hd := chainNe z t hz (hpre.digits t ht7)
              have hcw : CodeAt im (pcOf n) (chainW t (z.getD t 0) (ownC z t)) :=
                codeAt_win hcode hwin (by simp [chainW, headW])
              have hob := offC_bounds t ht7
              have hsb := slotC_bounds t ht7
              have hfree : ∀ o, o < 64 → (o < 16 ∨ 24 ≤ o) →
                  u.getMem (BitVec.ofNat 64 (B + offC t + o)) = s0.getMem (BitVec.ofNat 64 (B + offC t + o)) :=
                fun o ho _ => hI.frame _ (by omega) (fun ⟨t', h1, _, h2⟩ => block_free_earlier h1 ht7 o ho h2)
              have hpad : PadsZ B t u := by
                have hp := hpre.pads t ht7
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · have := hfree 0 (by omega) (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hp.1
                · rw [hfree 8 (by omega) (by omega)]; exact hp.2.1
                · rw [hfree 32 (by omega) (by omega)]; exact hp.2.2.1
                · rw [hfree 40 (by omega) (by omega)]; exact hp.2.2.2.1
                · rw [hfree 24 (by omega) (by omega)]; exact hp.2.2.2.2
              have hv : DigAt u (B + offC t + 48) (vals t) := by
                have hV := hpre.valAt t ht7
                exact ⟨(hfree 48 (by omega) (by omega)).trans hV.1, by
                  rw [show B + offC t + 48 + 8 = B + offC t + 56 by omega, hfree 56 (by omega) (by omega),
                    ← show B + offC t + 48 + 8 = B + offC t + 56 by omega]; exact hV.2⟩
              have hct := chain_tb (sk := sk) ht7 hd.1 hd.2 (ownC_spec z t) hcw hb hpre.hk hpre.hidx hpre.hj u hpc
                hI.regs hpad (vals t) hv
              rw [chainsFrom_succ _ _ _ _ _ _ ht7]
              refine (TBSim.bind (W₂ := c') hct (fun e w hw1 => ?_)).mono (by omega) (fun _ _ h => h)
              obtain ⟨pw, dw, rw', kw, fw⟩ := hw1
              have hI' : RInv B H k index j z s0 (t + 1) (pre ++ [e]) w := by
                refine ⟨by simp [hI.len], rw', hI.keep.trans kw, (hI.frame.trans fw).mono (fun A _ hA => ?_),
                  fun t' ht' => ?_⟩
                · rcases hA with ⟨t', h1, h2, h3⟩ | h
                  · exact ⟨t', by omega, h2, h3⟩
                  · exact ⟨t, by omega, hz, h⟩
                · rcases Nat.lt_or_ge t' t with h | h
                  · rw [getD_append_lt _ _ _ _ (by rw [hI.len]; exact h)]
                    have hD := hI.done t' h
                    have hs' := slotC_bounds t' (by omega)
                    exact ⟨(fw _ (by omega) (slot_free_later h ht7 0 (by omega) |> fun hh => by simpa using hh)).trans hD.1,
                      (fw _ (by omega) (slot_free_later h ht7 8 (by omega))).trans hD.2⟩
                  · have : t' = t := by omega
                    subst this; rw [← hI.len, getD_append_len, hI.len]; exact dw
              refine (TBSim.bind (W₂ := 0) (ih (t + 1) _ c' _ w hw' (by omega) pw hI') (fun es w' hw'' =>
                TBSim.pure (by simpa using hw''))).mono (by omega) (fun _ _ h => h)
            · cases hw
        ·
          rename_i ht7
          have h7 : t = 6 := by omega
          subst h7
          split at hw
          · rename_i hwin
            simp only [Option.some.injEq] at hw
            subst hw
            rw [chainsFrom_six]
            have hcw : CodeAt im (pcOf n) leafW := codeAt_win hcode hwin (by simp [leafW])
            obtain ⟨w, sw, pw, a0, a1, kw, m0, m1, fw⟩ := leaf_spec hcw u hpc hI.regs.x8 hI.regs.x28 hb
            refine (TBSim.steps sw (TBSim.pure ⟨?_, a0, a1, ?_, by simp [hI.len], ?_, ?_, ?_, ?_⟩)).mono
              (by omega) (fun _ _ h => h)
            · rw [pw, hI.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
            · intro r h3 h10 h11 h12 h14 h25
              rw [kw r h10 h11 h25, hI.keep r h3 h10 h12 h14 h25]
            · intro t' ht'
              rw [List.append_nil]
              have hD := hI.done t' ht'
              have hs' := slotC_bounds t' ht'
              have hl := leafHdr_free (B := B) (t := t') 0 (by omega)
              have hl8 := leafHdr_free (B := B) (t := t') 8 (by omega)
              simp only [Nat.add_zero] at hl
              exact ⟨(fw _ (by omega) (by rintro (h | h) <;> omega)).trans hD.1,
                (fw _ (by omega) (by rintro (h | h) <;> omega)).trans hD.2⟩
            · rw [m0, hI.regs.x31, show (0x601#64 : Word) = BitVec.ofNat 64 1537 from rfl, ofNat_add_ofNat]
            · rw [m1]
            · exact (hI.frame.trans fw).mono (fun A _ hA => by
                rcases hA with h | h
                · exact Or.inl h
                · exact Or.inr h)
          · cases hw
end ClaudeWCT.W9.Machine.Expand
end

namespace ClaudeWCT.W9.Machine.Expand.SharedCore
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def Post (L : W9Machine.Layout) (w : W9Machine.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (entry : MachineState) (computed : Digest) (result : MachineState) : Prop :=
  ∃ ends childEntry,Chain.Post L w index k raw entry ends childEntry ∧
    SharedChild.Post L k raw childEntry computed result

theorem core_tbsim (L : W9Machine.Layout) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072=(L.image.code.drop 195584).take 59072)
    (k : Fin 9) (raw : Fin 128) (rank : Fin 563)
    (hchild : ∀j,L.childWord j=(SharedLayout.layout k).childWord j)
    (hchain : ∀w index u,N600.Pre L w index k raw rank u→
      TBSim L.image sk u 89 (N600.program w index k raw rank) (N600.Post L w index k raw u))
    (w : W9Machine.WBytes) (index : Nat) (snapshot u : MachineState) (padL padR : Digest)
    (hu : N600.Pre L (SharedV3.viewW w k.val snapshot) index k raw rank u)
    (hL : DigAt snapshot (0x4c0+V3.regionOffset k.val+720) padL)
    (hR : DigAt snapshot (0x4c0+V3.regionOffset k.val+160) padR) :
    TBSim L.image sk u (89+SharedChild.cost k raw)
      (N600.program w index k raw rank >>=fun ends=>SharedV3.childN w index k raw ends padL padR)
      (Post L (SharedV3.viewW w k.val snapshot) index k raw u) := by
  have hspec : (N600.program w index k raw rank >>= fun ends=>SharedV3.childN w index k raw ends padL padR)=
      (N600.program (SharedV3.viewW w k.val snapshot) index k raw rank >>=fun ends=>
        SharedV3.childProgram (SharedV3.viewW w k.val snapshot) index k raw ends) := by
    unfold N600.program
    rw [SharedV3.chainProgram_view]
    simp only [fun ends=>SharedV3.childProgram_view w index k snapshot raw ends padL padR hL hR]
  rw [hspec]
  refine TBSim.bind (hchain _ _ _ hu) ?_
  intro ends childEntry hp
  exact (W9Drv.SharedBank.child_tbsim L sk k raw hwindow hchild _ index ends childEntry
    (hp.sharedChild hu)).mono le_rfl (fun computed t ht=>⟨ends,childEntry,hp,ht⟩)

#print axioms core_tbsim
end ClaudeWCT.W9.Machine.Expand.SharedCore

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xe3e03,0x1200e93,0xfff40f13,0xf0c63]
sym_block first := symRun {noAlias:=true} firstCode (pcOf 46905) 20
def middleCode : List (BitVec 32) := bv_list% 32 [0x3de5e33,0xffe40f13,0xf0663]
sym_block middle := symRun {noAlias:=true} middleCode (pcOf 46911) 20
def lastCode : List (BitVec 32) := bv_list% 32 [0x3de5e33,0xb40fc06f]
sym_block last := symRun {noAlias:=true} lastCode (pcOf 46914) 20
def remainderCode : List (BitVec 32) := bv_list% 32 [0x3de7e33,0xb38fc06f]
sym_block remainder := symRun {noAlias:=true} remainderCode (pcOf 46916) 20
def lowerCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x341e93,0x1de0e33,0x54e3023,0xf21d206f]
sym_block lowerCredit := symRun {noAlias:=true} lowerCreditCode (pcOf 46918) 20
def topCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xff4a0e93,0x5de3023,0xee1d206f]
sym_block topCredit := symRun {noAlias:=true} topCreditCode (pcOf 46924) 20
structure Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46905) firstCode
  middle : CodeAt im (pcOf 46911) middleCode
  last : CodeAt im (pcOf 46914) lastCode
  remainder : CodeAt im (pcOf 46916) remainderCode
  lowerCredit : CodeAt im (pcOf 46918) lowerCreditCode
  topCredit : CodeAt im (pcOf 46924) topCreditCode
theorem rem18 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 18#64=BitVec.ofNat 64 (n%18) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%18<2^64 by omega)]
  omega
theorem div18 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 18#64=BitVec.ofNat 64 (n/18) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/18<2^64 by omega)]
  omega
theorem floor1_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<5832) (h8 : s.getReg .x8=1)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 8 11 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/1%18) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=remainder.res.toState s1
  have st2 : Steps im s1 2 5 s2 := symRun_sound remainder hc.remainder s1 (by simp [s1, first.res, s2, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s2,st1.trans (st2),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, remainder.res,rv_simp,hm]
    simp only [div18 hints (by omega),div18 (hints/18) (by omega),rem18 hints (by omega),rem18 (hints/18) (by omega)]
    try rw [Nat.div_div_eq_div_mul]
    try rw [Nat.mod_eq_of_lt (show hints/324<18 by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor2_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<5832) (h8 : s.getReg .x8=2)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/18%18) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=middle.res.toState s1
  have st2 : Steps im s1 3 6 s2 := symRun_sound middle hc.middle s1 (by simp [s1, first.res, s2, middle.res, rv_simp, h8]) (by simp [middle.res,rv_simp])
  let s3:=remainder.res.toState s2
  have st3 : Steps im s2 2 5 s3 := symRun_sound remainder hc.remainder s2 (by simp [s1, first.res, s2, middle.res, s3, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s3,st1.trans (st2.trans (st3)),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, middle.res, s3, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, middle.res, s3, remainder.res,rv_simp,hm]
    simp only [div18 hints (by omega),div18 (hints/18) (by omega),rem18 hints (by omega),rem18 (hints/18) (by omega)]
    try rw [Nat.div_div_eq_div_mul]
    try rw [Nat.mod_eq_of_lt (show hints/324<18 by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor3_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<5832) (h8 : s.getReg .x8=3)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/324%18) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=middle.res.toState s1
  have st2 : Steps im s1 3 6 s2 := symRun_sound middle hc.middle s1 (by simp [s1, first.res, s2, middle.res, rv_simp, h8]) (by simp [middle.res,rv_simp])
  let s3:=last.res.toState s2
  have st3 : Steps im s2 2 5 s3 := symRun_sound last hc.last s2 (by simp [s1, first.res, s2, middle.res, s3, last.res, rv_simp, h8]) (by simp [last.res,rv_simp])
  refine ⟨s3,st1.trans (st2.trans (st3)),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, middle.res, s3, last.res,rv_simp,h8]
  · simp [s1, first.res, s2, middle.res, s3, last.res,rv_simp,hm]
    simp only [div18 hints (by omega),div18 (hints/18) (by omega),rem18 hints (by omega),rem18 (hints/18) (by omega)]
    try rw [Nat.div_div_eq_div_mul]
    try rw [Nat.mod_eq_of_lt (show hints/324<18 by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
def lowerPrepCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x341e93,0x1de0e33]
def lowerStoreCode : List (BitVec 32) := bv_list% 32 [0x54e3023,0xf21d206f]
sym_block lowerPrep := symRun {noAlias:=true} lowerPrepCode (pcOf 46918) 6
sym_block lowerStore := symRun {noAlias:=true} lowerStoreCode (pcOf 46922) 4

theorem lowerPrep_steps {im : Image} (hc : CodeAt im (pcOf 46918) lowerPrepCode)
    (s : MachineState) (hp : s.pc=pcOf 46918) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 46922 ∧ t.getReg .x28=BitVec.ofNat 64 (0x66000+8*lay) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerPrep hc s hp (by simp [lowerPrep.res,rv_simp]),rfl,?_,?_,?_⟩
  · rcases hl with ⟨hl,hu⟩;interval_cases lay <;> simp [lowerPrep.res,rv_simp,h8]
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl

theorem lowerStore_steps {im : Image} (hc : CodeAt im (pcOf 46922) lowerStoreCode)
    (s : MachineState) (hp : s.pc=pcOf 46922) (addr : Nat) (ha : addr+72<2^24) (hal : addr%8=0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 addr) (credit : BitVec 64) (h20 : s.getReg .x20=credit) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 787 ∧ t.getMem (BitVec.ofNat 64 (addr+64))=credit ∧
      RegsExcept s t [] ∧ Frame s t (fun A=>A=addr+64) := by
  refine ⟨_,symRun_sound lowerStore hc s hp (by simp [lowerStore.res,rv_simp,h28,accessValid_iff,MEMORY_BYTES];omega),rfl,?_,?_,?_⟩
  · simp only [Result.toState_getMem,lowerStore.res];t3n [h28,h20]
    try rw [Nat.mod_eq_of_lt (show addr+64<18446744073709551616 by omega),if_pos rfl]
  · intro r hr;cases r <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,lowerStore.res];t3n [h28]
    rw [Nat.mod_eq_of_lt (show addr+64<18446744073709551616 by omega),if_neg (by omega)]

theorem lowerCredit_steps {im : Image} (hc : CodeAt im (pcOf 46918) lowerCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 46918) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (credit : BitVec 64) (hc' : s.getReg .x20=credit) :
    ∃ t,Steps im s 6 6 t ∧ t.pc=pcOf 787 ∧ t.getMem (BitVec.ofNat 64 (0x66040+8*lay))=credit ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66040+8*lay) := by
  have prep : CodeAt im (pcOf 46918) lowerPrepCode := by
    simpa using (CodeAt.drop_prefix (pre:=[]) (seg:=lowerPrepCode) (post:=lowerStoreCode) hc)
  have store : CodeAt im (pcOf 46922) lowerStoreCode := by
    simpa [lowerPrepCode,pcOf] using (CodeAt.drop_prefix (pre:=lowerPrepCode) (seg:=lowerStoreCode) (post:=[]) hc)
  obtain ⟨u,su,up,ug,ur,uf⟩:=lowerPrep_steps prep s hp lay hl h8
  have u20 : u.getReg .x20=credit := (ur.get (by decide)).trans hc'
  obtain ⟨t,ut,tp,tg,tr,tf⟩:=lowerStore_steps store u up (0x66000+8*lay) (by omega) (by omega) ug credit u20
  refine ⟨t,su.trans ut,tp,?_,(ur.trans tr).mono (by decide),?_⟩
  · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tg
  · exact (uf.trans tf).mono (by intro A _ h;rcases h with h|h;exact False.elim h;simp_all [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm])

theorem topCredit_steps {im : Image} (hc : CodeAt im (pcOf 46924) topCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 46924) (acc : Nat) (ha : 12≤acc) (hb : acc<2^64)
    (hx : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ t,Steps im s 5 5 t ∧ t.pc=pcOf 776 ∧ t.getMem (0x66040#64)=BitVec.ofNat 64 (acc-12) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66040) := by
  refine ⟨_,symRun_sound topCredit hc s hp (by simp [topCredit.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp only [Result.toState_getMem,topCredit.res];t3n [hx];omega
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn
    simp only [Result.toState_getMem,topCredit.res];t3n []
    rw [if_neg (by omega)]
#print axioms floor1_steps
#print axioms floor2_steps
#print axioms floor3_steps
#print axioms lowerCredit_steps
#print axioms topCredit_steps
end ClaudeWCT.W9.Machine.Expand.SharedCounterHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem code_slice {im : Image} {base off : Nat} {words part : List (BitVec 32)}
    (hc : CodeAt im (pcOf base) words) (ho : off+part.length≤words.length)
    (he : (words.drop off).take part.length=part) :
    CodeAt im (pcOf (base+off)) part := by
  have hsplit : words=words.take off ++ part ++ words.drop (off+part.length) := by
    calc
      words = words.take off ++ words.drop off := (List.take_append_drop off words).symm
      _ = words.take off ++ (words.drop off).take part.length ++ (words.drop off).drop part.length := by
        simp only [List.append_assoc,List.take_append_drop]
      _ = words.take off ++ part ++ words.drop (off+part.length) := by rw [he,List.drop_drop]
  rw [hsplit] at hc
  have hh:=CodeAt.drop_prefix hc
  have hl : (words.take off).length=off := by rw [List.length_take,Nat.min_eq_left (by omega)]
  rw [hl] at hh
  convert hh using 1
  simp only [pcOf,←BitVec.ofNat_add]
  congr 1
  omega

theorem code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : Code im := by
  constructor
  · exact code_slice (off:=1849) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1855) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1858) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1860) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1862) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1868) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : Code Images.expandImage := code_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedCounterHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_kernel (P : Prop) (hP : P) : KernAt Images.expandImage 354 P := by
  refine ⟨⟨?_,?_⟩,Or.inl rfl,?_,⟨?_,?_,?_⟩,?_,?_,hP⟩
  all_goals apply codeAt_expand_current_chunk <;> decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedSearchCode

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
def creditAddr (lay : Layer) : Nat := 0x66040+8*lay.val
def CreditW (lay : Layer) (A : Nat) : Prop := A=creditAddr lay ∧ 0x66040≤A ∧ A<0x66060
def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay=0 then 16 else hints.toNat/18^(lay.val-1)%18
theorem creditAddr_align (lay : Layer) : creditAddr lay%8=0 := by simp [creditAddr,Nat.add_mod,Nat.mul_mod]
theorem creditAddr_lt (lay : Layer) : creditAddr lay<2^64 := by
  have := lay.isLt;unfold creditAddr;omega
theorem creditAddr_mem (lay : Layer) : CreditW lay (creditAddr lay) := by
  have := lay.isLt
  unfold CreditW creditAddr
  omega
theorem hintFloor_lt (hints : BitVec 16) (lay : Layer) : hintFloor hints lay<18 := by
  unfold hintFloor
  split_ifs
  · omega
  · omega

structure Contract (image : Image) : Prop where
  lower_spec_credit (s : MachineState) (lay : Layer) (hl : lay≠0)
      (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
      (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
      (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
      (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
      (hints : BitVec 16) (hh : hints.toNat<5832) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
      (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
      let good := floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤reward lay (lowDigits v++[T-S])
      ∃ t n c, c≤(if good then 103 else 97) ∧ Steps image s n c t ∧
        t.pc=(if good then pcOf 787 else pcOf 822) ∧
        (good → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (credit lay (lowDigits v++[T-S]))) ∧
        RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay)
  top_spec_credit (s : MachineState) (v : Digest)
      (ht : Reward.RewardTablesOK s) (hv : T3.topRanksValid (T3.topFlip v)=true)
      (hp : s.pc=pcOf (Reward.base 354 true))
      (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
      let good := 16+WCT9.dispatchPenalty 0 (topDigits (T3.topFlip v))≤reward 0 (topDigits (T3.topFlip v))
      ∃ t, Steps image s (if good then 103 else 98) (if good then 103 else 98) t ∧
        t.pc=(if good then pcOf 776 else pcOf 822) ∧
        (good → t.getMem (0x66040#64)=BitVec.ofNat 64 (credit 0 (topDigits (T3.topFlip v)))) ∧
        RegsExcept s t [.x10,.x11,.x20,.x28,.x29] ∧ Frame s t (CreditW 0)
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

def lowerAddCode : List (BitVec 32) := bv_list% 32 [0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33]
def lowerJumpCode : List (BitVec 32) := bv_list% 32 [0x4a50306f]
def lowerCreditJumpCode : List (BitVec 32) := bv_list% 32 [0x4c90306f]
def lowerBranchCode : List (BitVec 32) := bv_list% 32 [0x1ca6463]
def lowerBadCode : List (BitVec 32) := bv_list% 32 [0xc85d606f]
def topBranchCode : List (BitVec 32) := bv_list% 32 [0x1c00e13,0x1ca6463]
def topJumpCode : List (BitVec 32) := bv_list% 32 [0x64c0306f]
def topBadCode : List (BitVec 32) := bv_list% 32 [0xdf0d606f]
sym_block lowerAddRun := symRun {noAlias:=true} lowerAddCode (pcOf 43020) 6
sym_block lowerFloorJumpRun := symRun {noAlias:=true} lowerJumpCode (pcOf 43024) 2
sym_block lowerCreditJumpRun := symRun {noAlias:=true} lowerCreditJumpCode (pcOf 43028) 2
sym_block lowerBranchRun := symRun {noAlias:=true} lowerBranchCode (pcOf 43027) 2
sym_block lowerBadRun := symRun {noAlias:=true} lowerBadCode (pcOf 43029) 2
sym_block topBranchRun := symRun {noAlias:=true} topBranchCode (pcOf 43447) 3
sym_block topCreditJumpRun := symRun {noAlias:=true} topJumpCode (pcOf 43449) 2
sym_block topBadRun := symRun {noAlias:=true} topBadCode (pcOf 43450) 2

structure Code (image : Image) : Prop where
  scoring : CanonicalReward.PrefixAt image 354
  floorJump : CodeAt image (pcOf 43024) lowerJumpCode
  lowerBranch : CodeAt image (pcOf 43027) lowerBranchCode
  lowerJump : CodeAt image (pcOf 43028) lowerCreditJumpCode
  lowerBad : CodeAt image (pcOf 43029) lowerBadCode
  topBranch : CodeAt image (pcOf 43447) topBranchCode
  topJump : CodeAt image (pcOf 43449) topJumpCode
  topBad : CodeAt image (pcOf 43450) topBadCode
  hooks : ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.Code image

theorem lowerAdd_steps {image : Image} (hc : CodeAt image (pcOf 43020) lowerAddCode)
    (s : MachineState) (hp : s.pc=pcOf 43020) (a T S : Nat) (hs : S≤T)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hc8 : T-S<8) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf 43024 ∧
      t.getReg .x20=BitVec.ofNat 64 (a+if T-S=6 then 1 else 0) ∧
      RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _=>False) := by
  have hsub : s.getReg .x17-s.getReg .x25=BitVec.ofNat 64 (T-S) := by
    rw [h17,h25]
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hs,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hflag := Reward.eq_small (T-S) 6 hc8 (by decide) (by decide)
  change (if (BitVec.ofNat 64 (T-S)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=
    BitVec.ofNat 64 (if T-S=6 then 1 else 0) at hflag
  refine ⟨_,symRun_sound lowerAddRun hc s hp (by simp [lowerAddRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · change s.getReg .x20+(if ((s.getReg .x17-s.getReg .x25)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=_
    rw [hsub,hflag,h20,BitVec.ofNat_add]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem lowerFloorJump_steps {image : Image} (hc : CodeAt image (pcOf 43024) lowerJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43024) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46905 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerFloorJumpRun hc s hp (by simp [lowerFloorJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerCreditJump_steps {image : Image} (hc : CodeAt image (pcOf 43028) lowerCreditJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43028) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46918 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerCreditJumpRun hc s hp (by simp [lowerCreditJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBranch_steps {image : Image} (hc : CodeAt image (pcOf 43027) lowerBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 43027) (a floor : Nat) (ha : a<2^64) (hf : floor<2^64)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h28 : s.getReg .x28=BitVec.ofNat 64 floor) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=(if floor≤a then pcOf 43028 else pcOf 43029) ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBranchRun hc s hp (by simp [lowerBranchRun.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult (s.getReg .x28) then _ else _)=_
    rw [h20,h28,ofNat_ult a floor ha hf]
    split_ifs <;> simp_all [E.eval] <;> omega
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBad_steps {image : Image} (hc : CodeAt image (pcOf 43029) lowerBadCode)
    (s : MachineState) (hp : s.pc=pcOf 43029) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 822 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBadRun hc s hp (by simp [lowerBadRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem topBranch_steps {image : Image} (hc : CodeAt image (pcOf 43447) topBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 43447) (a : Nat) (ha : a<2^64)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if 28≤a then pcOf 43449 else pcOf 43450) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topBranchRun hc s hp (by simp [topBranchRun.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult 28#64 then _ else _)=_
    rw [h20,ofNat_ult a 28 ha (by decide)]
    split_ifs <;> simp_all [E.eval] <;> omega
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem topCreditJump_steps {image : Image} (hc : CodeAt image (pcOf 43449) topJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43449) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46924 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCreditJumpRun hc s hp (by simp [topCreditJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem topBad_steps {image : Image} (hc : CodeAt image (pcOf 43450) topBadCode)
    (s : MachineState) (hp : s.pc=pcOf 43450) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 822 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topBadRun hc s hp (by simp [topBadRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT LowerLUT
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1800000
set_option maxRecDepth 32768

theorem floor_steps {image : Image} (hC : SharedCounterHooks.Code image) (s : MachineState)
    (hp : s.pc=pcOf 46905) (lay : Layer) (hl : lay≠0) (hints : BitVec 16)
    (hh : hints.toNat<5832) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) :
    ∃ t n c, c≤17 ∧ Steps image s n c t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hintFloor hints lay) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  fin_cases lay
  · exact (hl rfl).elim
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor1_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,8,11,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor2_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor3_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩

theorem lower_spec {image : Image} (hC : Code image) (s : MachineState) (lay : Layer) (hl : lay≠0)
    (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hints : BitVec 16) (hh : hints.toNat<5832) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
    let a := partialScore v 14+(if T-S=6 then 1 else 0)
    ∃ t n c, c≤(if floor≤a then 103 else 97) ∧ Steps image s n c t ∧
      t.pc=(if floor≤a then pcOf 787 else pcOf 822) ∧
      (floor≤a → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 a) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay) := by
  dsimp only
  let a := partialScore v 14+(if T-S=6 then 1 else 0)
  have ha : a<2^64 := by have h := partial_bound v 14; dsimp [a];split_ifs <;> omega
  have hfloor : floor<2^64 := by have := hintFloor_lt hints lay;omega
  have hlow : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt; have hn : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨u,su,pu,ux11,ux20,ru,fu⟩ := CanonicalReward.Lower.init_spec (Or.inl rfl) hC.scoring s hp
  obtain ⟨v1,sv,pv,vx,rv,fv⟩ := CanonicalReward.Lower.loop_spec (Or.inl rfl) hC.scoring u v
    (ht.frame fu (by simp)) pu ((ru.get (by decide)).trans h6) ((ru.get (by decide)).trans h7) ux11 ux20 14 (by omega)
  have had : CodeAt image (pcOf 43020) lowerAddCode := by
    have h := CanonicalReward.lower_slice hC.scoring 73 4 (by decide)
    convert h using 1 <;> rfl
  obtain ⟨v2,s2,p2,x2,r2,f2⟩ := lowerAdd_steps had v1 (by simpa [Reward.base] using pv) (partialScore v 14) T S hST vx
    (((ru.trans rv).get (by decide)).trans h17) (((ru.trans rv).get (by decide)).trans h25) hc
  obtain ⟨v3,s3,p3,r3,f3⟩ := lowerFloorJump_steps hC.floorJump v2 p2
  obtain ⟨v4,n4,c4,hc4,s4,p4,x4,r4,f4⟩ := floor_steps hC.hooks v3 p3 lay hl hints hh
    (by rw [r3.get (by decide),r2.get (by decide),rv.get (by decide),ru.get (by decide),h8])
    (by rw [f3.get (by decide) (by simp),f2.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp),hm])
  have x20 : v4.getReg .x20=BitVec.ofNat 64 a := by rw [r4.get (by decide),r3.get (by decide),x2]
  obtain ⟨v5,s5,p5,r5,f5⟩ := lowerBranch_steps hC.lowerBranch v4 p4 a floor ha hfloor x20 (by simpa [hf] using x4)
  by_cases hg : floor≤partialScore v 14+(if T-S=6 then 1 else 0)
  · rw [if_pos hg] at p5
    obtain ⟨v6,s6,p6,r6,f6⟩ := lowerCreditJump_steps hC.lowerJump v5 p5
    obtain ⟨t,st,pt,mt,rt,ft⟩ := SharedCounterHooks.lowerCredit_steps hC.hooks.lowerCredit v6 p6 lay.val hlow
      (by rw [r6.get (by decide),r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),rv.get (by decide),ru.get (by decide),h8])
      (BitVec.ofNat 64 a) (by rw [r6.get (by decide),r5.get (by decide),x20])
    refine ⟨t,_,_,?_,((((((su.trans sv).trans s2).trans s3).trans s4).trans s5).trans s6).trans st,
      by simpa [hg] using pt,fun _=>mt,?_,?_⟩
    · simp only [if_pos hg];omega
    · exact ((((((ru.trans rv).trans r2).trans r3).trans r4).trans r5).trans r6).trans rt |>.mono (by decide)
    · exact ((((((fu.trans fv).trans f2).trans f3).trans f4).trans f5).trans f6).trans ft |>.mono (by
        intro A hA h; simp only [false_or] at h; subst A;exact creditAddr_mem lay)
  · rw [if_neg hg] at p5
    obtain ⟨t,st,pt,rt,ft⟩ := lowerBad_steps hC.lowerBad v5 p5
    refine ⟨t,_,_,?_,(((((su.trans sv).trans s2).trans s3).trans s4).trans s5).trans st,
      by simpa [hg] using pt,fun h=>False.elim (hg h),?_,?_⟩
    · simp only [if_neg hg];omega
    · exact (((((ru.trans rv).trans r2).trans r3).trans r4).trans r5).trans rt |>.mono (by decide)
    · exact (((((fu.trans fv).trans f2).trans f3).trans f4).trans f5).trans ft |>.mono (by simp [CreditW])
theorem top_spec {image : Image} (hC : Code image) (s : MachineState) (v : Digest)
    (ht : Reward.RewardTablesOK s) (hv : T3.topRanksValid (T3.topFlip v)=true)
    (hp : s.pc=pcOf (Reward.base 354 true))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    ∃ t, Steps image s (if 28≤Reward.packedTopScore v then 103 else 98)
        (if 28≤Reward.packedTopScore v then 103 else 98) t ∧
      t.pc=(if 28≤Reward.packedTopScore v then pcOf 776 else pcOf 822) ∧
      (28≤Reward.packedTopScore v → t.getMem (0x66040#64)=BitVec.ofNat 64 (Reward.packedTopScore v-12)) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29] ∧ Frame s t (CreditW 0) := by
  obtain ⟨t1,s1,p1,g11,g20,r1,f1⟩ := CanonicalReward.Top.init_spec (Or.inl rfl) hC.scoring s hp
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := CanonicalReward.Top.iter (Or.inl rfl) hC.scoring t1 v 18 (by decide)
    (ht.frame f1 (by simp)) p1 ((r1.get (by decide)).trans h6) ((r1.get (by decide)).trans h7) g11 g20
  rw [Reward.PackedTop.runningSum_eq] at g2
  have he := Reward.packedTopScore_reward v hv
  have hb := Reward.total_reward_bound 0 (topDigits (T3.topFlip v))
  have ha : Reward.packedTopScore v<2^64 := by omega
  obtain ⟨t3,s3,p3,r3,f3⟩ := topBranch_steps hC.topBranch t2 (by simpa [Reward.base,Reward.PackedTop.start] using p2)
    (Reward.packedTopScore v) ha g2
  by_cases hg : 28≤Reward.packedTopScore v
  · rw [if_pos hg] at p3
    obtain ⟨t4,s4,p4,r4,f4⟩ := topCreditJump_steps hC.topJump t3 p3
    obtain ⟨t,st,pt,mt,rt,ft⟩ := SharedCounterHooks.topCredit_steps hC.hooks.topCredit t4 p4 (Reward.packedTopScore v) (by omega) ha
      (by rw [r4.get (by decide),r3.get (by decide),g2])
    refine ⟨t,?_,by simpa [hg] using pt,fun _=>mt,?_,?_⟩
    · simpa [hg,Reward.PackedTop.start] using (((s1.trans s2).trans s3).trans s4).trans st
    · exact (((r1.trans r2).trans r3).trans r4).trans rt |>.mono (by decide)
    · exact (((f1.trans f2).trans f3).trans f4).trans ft |>.mono (by intro A hA h;simp only [false_or] at h;subst A;norm_num [CreditW,creditAddr])
  · rw [if_neg hg] at p3
    obtain ⟨t,st,pt,rt,ft⟩ := topBad_steps hC.topBad t3 p3
    refine ⟨t,?_,by simpa [hg] using pt,fun h=>False.elim (hg h),?_,?_⟩
    · simpa [hg,Reward.PackedTop.start] using ((s1.trans s2).trans s3).trans st
    · exact ((r1.trans r2).trans r3).trans rt |>.mono (by decide)
    · exact ((f1.trans f2).trans f3).trans ft |>.mono (by simp [CreditW])

#print axioms lower_spec
#print axioms top_spec
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

theorem lower_reward (lay : Layer) (hl : lay≠0) (v : Digest) (T S : Nat) :
    LowerLUT.partialScore v 14+(if T-S=6 then 1 else 0)=
      credit lay (lowDigits v++[T-S]) := by
  have h := LowerLUT.packed_reward lay hl v (T-S)
  simpa [LowerLUT.partialScore,credit,reward,WCT9.dispatchPenalty,hl] using h

theorem top_reward (v : Digest) (hv : T3.topRanksValid (T3.topFlip v)=true) :
    Reward.packedTopScore v-12=credit 0 (topDigits (T3.topFlip v)) := by
  have h := Reward.packedTopScore_reward v hv
  unfold credit reward
  omega

theorem lower_spec_credit {image : Image} (hC : Code image) (s : MachineState) (lay : Layer) (hl : lay≠0)
    (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hints : BitVec 16) (hh : hints.toNat<5832) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
    let good := floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤reward lay (lowDigits v++[T-S])
    ∃ t n c, c≤(if good then 103 else 97) ∧ Steps image s n c t ∧
      t.pc=(if good then pcOf 787 else pcOf 822) ∧
      (good → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (credit lay (lowDigits v++[T-S]))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay) := by
  have h := lower_spec hC s lay hl v ht hp h6 h7 T S floor h17 h25 hST hc hints hh h8 hm hf
  rw [lower_reward lay hl v T S] at h
  simpa [credit,WCT9.dispatchPenalty,hl] using h

theorem top_spec_credit {image : Image} (hC : Code image) (s : MachineState) (v : Digest)
    (ht : Reward.RewardTablesOK s) (hv : T3.topRanksValid (T3.topFlip v)=true)
    (hp : s.pc=pcOf (Reward.base 354 true))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    let good := 16+WCT9.dispatchPenalty 0 (topDigits (T3.topFlip v))≤reward 0 (topDigits (T3.topFlip v))
    ∃ t, Steps image s (if good then 103 else 98) (if good then 103 else 98) t ∧
      t.pc=(if good then pcOf 776 else pcOf 822) ∧
      (good → t.getMem (0x66040#64)=BitVec.ofNat 64 (credit 0 (topDigits (T3.topFlip v)))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29] ∧ Frame s t (CreditW 0) := by
  have he := Reward.packedTopScore_reward v hv
  have hi : (28≤Reward.packedTopScore v)↔
      16+WCT9.dispatchPenalty 0 (topDigits (T3.topFlip v))≤reward 0 (topDigits (T3.topFlip v)) := by
    unfold reward
    omega
  have h := top_spec hC s v ht hv hp h6 h7
  simpa only [hi,top_reward v hv] using h
#print axioms lower_spec_credit
#print axioms top_spec_credit
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
theorem contract_of_code {image : SigGolfCandidate.Legacy.Riscv.Image} (hC : Code image) : Contract image :=
  ⟨lower_spec_credit hC,top_spec_credit hC⟩
#print axioms contract_of_code
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def start (k : Nat) : Nat := [46513,46551,46590,46629,46668,46707,46746,46785,46824].getD k 0
def endWord (k : Nat) : Nat := [46551,46590,46629,46668,46707,46746,46785,46824,46862].getD k 0
def length (k : Nat) : Nat := endWord k-start k
/-- Dispatch code of coordinate `k` (`expandSharedDriver` offsets 1457..1805). Stage 2: coordinate 8 sets
`ra = pcOf (endWord 8 - 78)` (`addi ra,ra,-284`, was `-280`), since the merged singleton returns with
`jalr zero,312(ra)` (was 308) to the same word 46862. -/
def words (k : Nat) : List (BitVec 32) := [
[0x208b7,0x16088893,0x8b203,0x10337,0x7f27213,0x8b703,0xd75713,0x3ff77713,0x2437,0x17040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x8b203,0x625213,0x7f27213,0x88b703,0xd75713,0x3ff77713,0x2437,0xdf040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x20337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x88b203,0x25213,0x7f27213,0x88b703,0x1975713,0x3ff77713,0x2437,0xa7040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x30337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x88b203,0x625213,0x7f27213,0x88b703,0x2575713,0x3ff77713,0x1437,0x6f040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x40337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x108b203,0x25213,0x7f27213,0x108b703,0xd75713,0x3ff77713,0x1437,0x37040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x50337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x108b203,0x625213,0x7f27213,0x108b703,0x1975713,0x3ff77713,0x1437,0xff040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x60337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x188b203,0x25213,0x7f27213,0x108b703,0x2575713,0x3ff77713,0x1437,0xc7040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x70337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x188b203,0x625213,0x7f27213,0x188b703,0xd75713,0x3ff77713,0x1437,0x8f040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x80337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x188b203,0x2525213,0x7f27213,0x188b703,0x1975713,0x3ff77713,0x57000413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x90337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xe7337,0x40030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xedc08093,0x871713,0xc0337,0x30313,0x670733,0x70067]].getD k []
def rawPosition (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def rawWord (k : Nat) : Nat := [0,0,1,1,2,2,3,3,3].getD k 0
def rankPosition (k : Nat) : Nat := [13,13,25,37,13,25,37,13,25].getD k 0
def rankWord (k : Nat) : Nat := [0,1,1,1,2,2,2,3,3].getD k 0
def rawRead (k : Nat) (u : MachineState) : Word :=
  (u.getMem (BitVec.ofNat 64 (0x20160+8*rawWord k)) >>> rawPosition k) &&& 127#64
def rankRead (k : Nat) (u : MachineState) : Word :=
  (u.getMem (BitVec.ofNat 64 (0x20160+8*rankWord k)) >>> rankPosition k) &&& 1023#64

def result (k : Nat) : Result :=
  -- C4: coordinate 0 replaces its `srli tp,tp,0` no-op by the label `lui`, so its raw read has no shift.
  let raw := if k = 0 then mkBin .and (.ld (.c (BitVec.ofNat 64 (0x20160+8*rawWord k)))) (.c 127)
    else mkBin .and (mkBin .srl (.ld (.c (BitVec.ofNat 64 (0x20160+8*rawWord k)))) (.c (BitVec.ofNat 64 (rawPosition k)))) (.c 127)
  let rank := mkBin .and (mkBin .srl (.ld (.c (BitVec.ofNat 64 (0x20160+8*rankWord k)))) (.c (BitVec.ofNat 64 (rankPosition k)))) (.c 1023)
  let node := mkAdd (mkBin .sll (.ld (.c 0x66010)) (.c 27)) (.c (BitVec.ofNat 64 (1537+65536*(k+1))))
  let chainPC := mkAdd (mkBin .sll rank (.c 8)) (.c 0xc0000)
  let childPC := mkAdd (mkBin .sll raw (.c (if k<8 ∧ k%2=0 then 7 else 8)))
    (.c (BitVec.ofNat 64 (4096+4*(if k<8 ∧ k%2=0 then 231616 else if k=8 then 235776 else 246464))))
  let regs := RegFile.init.set .x17 (.c 0x20160)
  let regs := (regs.set .x4 raw).set .x14 chainPC
  let regs := (regs.set .x8 (.c (BitVec.ofNat 64 (8560-896*k)))).set .x28 (.c 0x66000)
  let regs := (regs.set .x15 node).set .x6 (.c 0xc0000)
  let regs := (regs.set .x31 (mkAdd (mkBin .sll raw (.c 20)) node)).set .x23 childPC
  let regs := (regs.set .x5 (.c 0)).set .x7 (.c 1)
  let regs := (regs.set .x13 (.c 2)).set .x19 (.c 3)
  let regs := (regs.set .x20 (.c 4)).set .x21 (.c 5)
  let regs := (regs.set .x26 (.c 6)).set .x30 (.c 7)
  let regs := (regs.set .x11 (.c 64)).set .x1 (.c (pcOf (endWord k-(if k=8 then 80 else 74))))
  ⟨⟨regs,[],[]⟩,mkBin .and chainPC (.c (~~~1#64)),.jump,length k,length k⟩
theorem checked0 : rOK (symRun {} (words 0) (pcOf (start 0)) (length 0)) (result 0)=true := by decide +kernel
#print axioms checked0
theorem checked1 : rOK (symRun {} (words 1) (pcOf (start 1)) (length 1)) (result 1)=true := by decide +kernel
#print axioms checked1
theorem checked2 : rOK (symRun {} (words 2) (pcOf (start 2)) (length 2)) (result 2)=true := by decide +kernel
#print axioms checked2
theorem checked3 : rOK (symRun {} (words 3) (pcOf (start 3)) (length 3)) (result 3)=true := by decide +kernel
#print axioms checked3
theorem checked4 : rOK (symRun {} (words 4) (pcOf (start 4)) (length 4)) (result 4)=true := by decide +kernel
#print axioms checked4
theorem checked5 : rOK (symRun {} (words 5) (pcOf (start 5)) (length 5)) (result 5)=true := by decide +kernel
#print axioms checked5
theorem checked6 : rOK (symRun {} (words 6) (pcOf (start 6)) (length 6)) (result 6)=true := by decide +kernel
#print axioms checked6
theorem checked7 : rOK (symRun {} (words 7) (pcOf (start 7)) (length 7)) (result 7)=true := by decide +kernel
#print axioms checked7
theorem checked8 : rOK (symRun {} (words 8) (pcOf (start 8)) (length 8)) (result 8)=true := by decide +kernel
#print axioms checked8
theorem checked (k : Fin 9) : symRun {} (words k.val) (pcOf (start k.val)) (length k.val)=some (result k.val) := by
  apply rOK_eq
  fin_cases k
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8

theorem result_mem (k : Fin 9) (u : MachineState) (a : Word) :
    ((result k.val).toState u).getMem a=u.getMem a := by fin_cases k <;> rfl

theorem result_raw (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x4=rawRead k.val u := by fin_cases k <;> rfl

theorem result_node (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x15=
      (u.getMem 0x66010 <<< 27)+BitVec.ofNat 64 (1537+65536*(k.val+1)) := by fin_cases k <;> rfl

theorem result_leaf (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x31=
      (rawRead k.val u <<< 20)+((result k.val).toState u).getReg .x15 := by fin_cases k <;> simp [result,rawRead,rawWord,rawPosition,Result.toState_getReg,RegFile.get,RegFile.set,mkAdd,addC,mkBin,E.eval,BinOp.eval,BitVec.add_assoc]

theorem result_base (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x8=BitVec.ofNat 64 (coordinateBase k) := by fin_cases k <;> rfl

theorem result_return (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x1=pcOf (endWord k.val-(if k.val=8 then 80 else 74)) := by fin_cases k <;> rfl

theorem result_pc (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).pc=((rankRead k.val u <<< 8)+0xc0000#64) &&& ~~~1#64 := by fin_cases k <;> rfl

#print axioms checked
#print axioms result_pc
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem reward_code_of_hooks (hH : SharedCounterHooks.Code Images.expandImage) :
    CanonicalExpandHooks.Code Images.expandImage := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,hH⟩
  all_goals apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_reward_code : CanonicalExpandHooks.Code Images.expandImage :=
  reward_code_of_hooks SharedCounterHooks.installed_code
theorem installed_reward_contract : CanonicalExpandHooks.Contract Images.expandImage :=
  CanonicalExpandHooks.contract_of_code installed_reward_code
theorem installed_searchKernel : KernAt Images.expandImage 354 (CanonicalExpandHooks.Contract Images.expandImage) :=
  installed_kernel _ installed_reward_contract
end ClaudeWCT.W9.Machine.Expand.SharedSearchCode

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
  floor : Nat
  hints : BitVec 16
def csT (lay : Layer) : Nat := if lay = 0 then 270 else 395
def csOk (lay : Layer) : Nat := if lay = 0 then 4096 else 4096
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by unfold capLimit; split_ifs <;> omega
theorem capLimit_eq (lay : Layer) : capLimit lay.val = WCT9.searchLimit lay := by
  fin_cases lay <;> rfl
theorem length_filter_range (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
def rewardOK (lay : Layer) (floor : Nat) (ds : List Nat) : Prop :=
  floor + WCT9.dispatchPenalty lay ds ≤ WCT9.wordCredit lay ds + 4 * WCT9.savedCopies lay ds
instance (lay : Layer) (floor : Nat) (ds : List Nat) : Decidable (rewardOK lay floor ds) := by unfold rewardOK; infer_instance
theorem reward_credit_le {lay : Layer} {floor : Nat} {ds : List Nat}
    (h : rewardOK lay floor ds) : floor ≤ WCT9.CanonicalPolicy.credit lay ds := by
  unfold rewardOK WCT9.CanonicalPolicy.credit WCT9.CanonicalPolicy.reward at *
  omega
theorem producerDecode_top (v : Digest) (floor : Nat) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 floor v = if rewardOK 0 floor ds then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.producerZeroBound,WCT9.producerRankBound,rewardOK,WCT9.CanonicalPolicy.reward]
theorem producerDecode_lower {lay : Layer} (hlz : lay≠0) (v : Digest) (floor c : Nat) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode lay v=some ds) (hds : ds=lowDigits v++[c]) :
    WCT9.CanonicalPolicy.producerDecodeAt lay floor v=
      if rewardOK lay floor ds ∧ (lowDigits v++[c]).count 0≤5 ∧ Rank.rankOK v then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.producerZeroBound,WCT9.producerRankBound,
    rewardOK,WCT9.CanonicalPolicy.reward,Rank.rankOK,Rank.rankFloor,WCT9.producerRankFloor,hlz,hds,filter_zero_count]
def cfFlag (_b : Nat) : Nat := 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (lay : Layer) (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨ (DigW A ∨ CanonicalExpandHooks.CreditW lay A)
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 32
  x15 : A.tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height A.lay)
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
  reward : Reward.RewardTablesOK s
  floorLt : A.floor<18
  floorTop : A.lay=0 → A.floor=16
  hintsLt : A.hints.toNat<5832
  floorEq : A.floor=CanonicalExpandHooks.hintFloor A.hints A.lay
  floorMem : s.getMem (0x66000#64)=BitVec.ofNat 64 A.hints.toNat
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (capBase b)
  hi : i ≤ capLimit A.lay.val
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t (CsW A.lay)
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t (CsW A.lay) ∧
    (t.getReg .x25).toNat ≤ 129
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, WCT9.CanonicalPolicy.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t (CsW A.lay) ∧ (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) ∧
      t.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay ds) ∧
      A.floor ≤ WCT9.CanonicalPolicy.credit A.lay ds
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u (CsW A.lay)
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.stepCredit {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' (CanonicalExpandHooks.CreditW A.lay)) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat) → MachineState → Prop}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < capLimit A.lay.val)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  have hcap := capLimit_le A.lay.val
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 54 else 43 := by
  fin_cases lay <;> rfl
theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
structure RewardReady (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (ds : List Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf A.ret
  trial : TrialSt b A s0 i t
  len : ds.length=T3.chainCount A.lay
  digs : ∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)
  credit : t.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay ds)
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} {ds : List Nat}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0) (hu : RewardReady b A s0 i ds u)
    (hi : i < capLimit A.lay.val) (answer : Digest) (hdec : WCT9.CanonicalPolicy.decode A.lay answer = some ds)
    (hfloor : A.floor ≤ WCT9.CanonicalPolicy.credit A.lay ds) :
    TBSim image sk u 0 (pure (some (BitVec.ofNat 32 i,ds))) (CsPost image b A s0) := by
  have hcap := capLimit_le A.lay.val
  have hc : (BitVec.ofNat 32 i).toNat=i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.pure ⟨hu.pc,?_,?_,?_,⟨answer,hdec⟩,hu.len,hu.digs,hu.trial.regs,hu.trial.frame,hu.sum,hu.credit,hfloor⟩
  · rw [hc]; omega
  · rw [hc]; exact hu.trial.x19
  · rw [hc]; exact hu.trial.c32

theorem cs_prepare {A : CsArgs} {s0 u : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 433)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (hv : T3.lowerSpare v) (S : Nat) (ds : List Nat) (hdec : WCT9.CanonicalPolicy.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) - S]) (hS : S ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S)
    (hcredit : u.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay ds)) :
    ∃ k t, Steps image u k k t ∧ k ≤ 815 ∧ RewardReady b A s0 i ds t := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨u1, su1, pu1, a6, a7, ru1, fu1⟩ := Credit.align_spec hK u hpc v hv h6 h7
  have hu1 := hu.step ru1 (by decide) fu1
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u1 pu1 (BitVec.ofNat 128 (T3.lowerWord v)) A.lay.val
    (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu1.reg (by decide), hpre.x1]) (by rw [hu1.reg (by decide), hpre.x8])
    (by rw [hu1.reg (by decide), hpre.x17]) (by rw [ru1.get (by decide), h25])
    (by rw [hu1.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu1.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) a6 a7
  rw [if_neg hl0] at kle tdig
  have hfr := (hu1.frame.trans tf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hregs : RegsExcept s0 t csRegs := (hu1.regs.trans tr).mono (by decide)
  refine ⟨5+k,t,su1.trans st,by omega,?_,?_,?_,?_,?_,?_⟩
  · simpa [hlz] using tpc
  · refine ⟨?_,?_,?_,?_,hregs,hfr⟩
    · rw [tr.get (by decide),hu1.x19]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h16]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h24]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.c32]
  · rw [hds,chainCount_eq,if_neg hlz]; simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq,if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length];exact hj),lowDigits_eq,getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]),lowDigits_length]
      simpa using tchk hl0
  · rw [tr.get (by decide),ru1.get (by decide),h25,BitVec.toNat_ofNat]
    have := target_lt (WCT9.CanonicalPolicy.normalLayer A.lay)
    omega
  · rw [tf.get (CanonicalExpandHooks.creditAddr_lt _) (by unfold CanonicalExpandHooks.creditAddr DigW DIGITS;omega),fu1.get (CanonicalExpandHooks.creditAddr_lt _) (by simp),hcredit]
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem TrialSt.cf {A : CsArgs} {s0 u : MachineState} {i : Nat} {flag : Nat}
    (hu : TrialSt b A s0 i u) (ht : CfTableOK flag s0) : CfTableOK flag u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem TrialSt.reward {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : Reward.RewardTablesOK s0) : Reward.RewardTablesOK u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem cs_top_prepare {A : CsArgs} {s0 u : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (hpre : CsPre b A s0) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 363))
    (hi : i < 2 ^ 22) (hlz : A.lay = 0) (v : Digest)
    (hvalid : T3.topRanksValid (T3.topFlip v) = true)
    (hdec : WCT9.CanonicalPolicy.decode A.lay (T3.topFlip v) = some (topDigits (T3.topFlip v)))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (h25 : u.getReg .x25 = 145#64) (h20 : u.getReg .x20 = 0)
    (hcredit : u.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay (topDigits (T3.topFlip v)))) :
    ∃ t, Steps image u 301 301 t ∧ RewardReady b A s0 i (topDigits (T3.topFlip v)) t := by
  obtain ⟨t, st, tpc, tdig, tr, tf⟩ := topUnpack_spec hK u v hvalid (hu.table hpre.table) hpc h6 h7 h30 h20 A.ret
    (by rw [hu.reg (by decide),hpre.x1])
  have hregs : RegsExcept s0 t csRegs := (hu.regs.trans tr).mono (by decide)
  have hfr : Frame s0 t (CsW A.lay) := (hu.frame.trans tf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  refine ⟨t,st,?_,?_,?_,?_,?_,?_⟩
  · simpa [hlz] using tpc
  · refine ⟨?_,?_,?_,?_,hregs,hfr⟩
    · rw [tr.get (by decide),hu.x19]
    · rw [tf.get (by unfold ENC;omega) (by unfold TopUnpack.Writes DIGITS ENC;omega),hu.h16]
    · rw [tf.get (by unfold ENC;omega) (by unfold TopUnpack.Writes DIGITS ENC;omega),hu.h24]
    · rw [tf.get (by unfold ENC;omega) (by unfold TopUnpack.Writes DIGITS ENC;omega),hu.c32]
  · rw [hlz,topDigits_length];rfl
  · intro j hj
    rw [hlz] at hj
    change j<54 at hj
    rw [tdig j hj]
    simp only [topDigits,getD_map_range hj]
  · rw [tr.get (by decide),h25,hlz];decide
  · rw [tf.get (CanonicalExpandHooks.creditAddr_lt _) (by unfold CanonicalExpandHooks.creditAddr TopUnpack.Writes DIGITS;omega),hcredit]
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < capLimit A.lay.val) :
    ∃ k t2, Steps image t k k t2 ∧ k ≤ (if A.lay = 0 then 14 else 12) ∧ t2.pc = pcOf (b + 123) ∧
      fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  have hcap := capLimit_le A.lay.val
  obtain ⟨k1, t1, s1, k1le, p1, r1, f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide), hpre.x8]) hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 (CsW A.lay) := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ addr, addr < 2 ^ 64 → ¬ CsW A.lay addr → t2.getMem (BitVec.ofNat 64 addr) = s0.getMem (BitVec.ofNat 64 addr) :=
    fun A hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  have hk : k1 + 8 ≤ (if A.lay = 0 then 14 else 12) := by
    have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
    by_cases h : A.lay = 0
    · rw [if_pos (hl0.2 h)] at k1le; rw [if_pos h]; omega
    · rw [if_neg (fun h' => h (hl0.1 h'))] at k1le; rw [if_neg h]; omega
  refine ⟨_, t2, s1.trans s2, hk, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (BC.encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, BC.wordsOf_encodingInput, hc]
  have nw : ∀ addr, addr = ENC ∨ addr = ENC + 8 ∨ addr = ENC + 40 ∨ addr = ENC + 48 ∨ addr = ENC + 56 → ¬ CsW A.lay addr := by
    intro A hA; simp only [CsW, CanonicalExpandHooks.CreditW, DigW, ENC, EOUT, DIGITS] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.r48, hpre.r56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cfFlag_lt (b : Nat) : cfFlag b < 256 := by change 0<256;decide
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i=capLimit A.lay.val) :
    TBSim image sk t (0*csT A.lay+csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i 0)
      (CsPost image b A s0) := by
  obtain ⟨k1,t1,s1,k1le,p1,r1,f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide),hpre.x8]) hI.x19
  rw [if_pos hi] at p1
  have hk1 : k1≤6 := by split_ifs at k1le <;> omega
  have h8 : t1.getReg .x8=BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide),hI.regs.get (by decide),hpre.x8]
  have fr1 : Frame s0 t1 (CsW A.lay) := (hI.frame.trans f1).mono (fun A _ h=>by simpa using h)
  have hcf : CfTableOK 0 t1 := hpre.cf.frame fr1
    (by intro j hj hj';unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS;omega)
  obtain ⟨n,t2,hn,s2,p2,r2,f2⟩ := Credit.exhaust_fail hK t1 p1 A.lay.val A.lay.isLt h8 0
    (by decide) hcf (Or.inr rfl)
  obtain ⟨t3,s3,p3,h5,h10,hf⟩ := cs0_spec hK t2 p2
  change TBSim image sk t _ (pure none) _
  refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h=>h)
  · exact ⟨p3,h5,h10,hf⟩
  · unfold csOk;split_ifs <;> omega

end trial
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
variable {image : Image} {sk : BitVec 256}
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image 354 (CanonicalExpandHooks.Contract image)) (hpre : CsPre 354 A s0) :
    ∀ F i t, i + F = capLimit A.lay.val → CsInv 354 A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i F)
        (CsPost image 354 A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h,fun h => by rw [h];rfl⟩
  have hcap := capLimit_le A.lay.val
  intro F
  induction F with
  | zero =>
    intro i t h hI
    exact cs_exhaust hK hpre hI (by omega)
  | succ F ih =>
    intro i t h hI
    have hi : i < capLimit A.lay.val := by omega
    have hi22 : i < 2 ^ 22 := by omega
    obtain ⟨k2,t2,s2,k2le,p2,hf,h5,hv,hq,h12,hT⟩ := cs_answer hK hpre hI hi
    have prog : WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i (F+1) =
        (WCT9.encodingHash A.lay (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor answer with
          | none => WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F
          | some digits => pure (some (BitVec.ofNat 32 i,digits))) := rfl
    have ih' : ∀ t, CsInv 354 A s0 (i+1) t → TBSim image sk t (F*csT A.lay+csOk A.lay)
        (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F) (CsPost image 354 A s0) :=
      fun t ht => ih (i+1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.encodingHash_bind hf h5 hv hq
      (W:=F*csT A.lay+csOk A.lay+(csT A.lay-(if A.lay=0 then 22 else 20))) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [BC.blocks_encodingInput,Nat.succ_mul];unfold csT at *;split_ifs at k2le ⊢ <;> omega
    set v := WCT9.encodingAnswer A.lay a with hvdef
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc=pcOf (354+124) := by rw [pc_writeHash,p2,pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    have hhi := DigAt.writeHash_hi t2 a EOUT h12 (by decide)
    obtain ⟨t4,s4,p4,h6,h7,h25,r4,f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide),hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    by_cases hlz : A.lay=0
    · rw [if_pos (hl0.2 hlz)] at p4
      obtain ⟨kg,tg,sg,hkg,pg,g6,g7,rg,fg⟩ := top_select_spec hK t4 p4 a h6 h7
        (by rw [r4.get (by decide),getReg_writeHash,h12])
        (by rw [f4.get (by unfold EOUT;omega) (by simp)];exact hhi.1)
        (by rw [f4.get (by unfold EOUT;omega) (by simp)];exact hhi.2)
      have he : v=T3.TopDualHalf.select a := by simp [hvdef,WCT9.encodingAnswer,hlz]
      rw [←he] at g6 g7
      obtain ⟨tc,sc,pcc,h6c,h7c,rc,fc⟩ := tc_spec hK tg pg v g6 g7
      have sc := sg.trans sc
      have hTc := (hT4.step rg (by decide) fg).step rc (by decide) fc
      clear_value v
      obtain ⟨w,rfl⟩ : ∃ w,v=T3.topFlip w := ⟨T3.topFlip v,(T3.topFlip_topFlip v).symm⟩
      rw [T3.topFlip_topFlip] at h6c h7c
      have hdec : WCT9.CanonicalPolicy.decode 0 (T3.topFlip w)=
          (if topLookupSum w=145 then some (topDigits (T3.topFlip w)) else none) := by
        simpa [WCT9.CanonicalPolicy.decode,WCT9.CanonicalPolicy.normalLayer] using decode_top_lookup w
      rw [←hlz] at hdec
      obtain ⟨t5,s5,p5,r5,f5⟩ := cs263_spec hK tc pcc
      have hT5 := hTc.step r5 (by decide) f5
      obtain ⟨t6,s6,p6,h25',h30',r6,f6⟩ := topCheck_spec hK t5 w p5
        (by rw [r5.get (by decide),h6c]) (by rw [r5.get (by decide),h7c])
        (by rw [hT5.reg (by decide),hpre.x17,hlz];rfl) (hT5.table hpre.table).sum
      have hT6 := hT5.step r6 (by decide) f6
      by_cases hs : topLookupSum w=145
      · rw [if_pos hs] at p6
        have hd' : WCT9.CanonicalPolicy.decode A.lay (T3.topFlip w)=some (topDigits (T3.topFlip w)) := by rw [hdec,if_pos hs]
        have hpd := producerDecode_top (T3.topFlip w) A.floor (by simpa [hlz] using hd')
        rw [←hlz] at hpd
        rw [hpd]
        have hvalid := ((topLookupSum_eq_iff w).mp hs).1
        obtain ⟨t7,s7,p7,r7,f7⟩ := TopUnpack.jump_spec hK t6 p6
        have hT7 := hT6.step r7 (by decide) f7
        obtain ⟨tf,sf,pf,mf,rf,ff⟩ := hK.2.2.2.2.2.2.top_spec_credit t7 w
          (hT7.reward hpre.reward) hvalid p7
          (by rw [r7.get (by decide),r6.get (by decide),r5.get (by decide),h6c])
          (by rw [r7.get (by decide),r6.get (by decide),r5.get (by decide),h7c])
        have hTf := hT7.stepCredit rf (by decide) (by simpa only [hlz] using ff)
        change tf.pc=(if rewardOK 0 16 (topDigits (T3.topFlip w)) then _ else _) at pf
        change Steps image t7 (if rewardOK 0 16 (topDigits (T3.topFlip w)) then 103 else 98)
          (if rewardOK 0 16 (topDigits (T3.topFlip w)) then 103 else 98) tf at sf
        change (rewardOK 0 16 (topDigits (T3.topFlip w)) → _) at mf
        rw [←hpre.floorTop hlz,←hlz] at pf sf mf
        by_cases hok : rewardOK A.lay A.floor (topDigits (T3.topFlip w))
        · rw [if_pos hok] at pf sf
          simp only [if_pos hok]
          obtain ⟨t8,s8,p8,g20,r8,f8⟩ := Credit.ok_spec hK tf pf
          have hT8 := hTf.step r8 (by decide) f8
          obtain ⟨t9,s9,hR⟩ := cs_top_prepare hK hpre hT8 p8 hi22 hlz w hvalid hd'
            (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide),r6.get (by decide),r5.get (by decide),h6c])
            (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide),r6.get (by decide),r5.get (by decide),h7c])
            (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide),h30'])
            (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide)];simpa only [hs] using h25') g20
            (by rw [f8.get (CanonicalExpandHooks.creditAddr_lt _) (by simp)];simpa [hlz,CanonicalExpandHooks.creditAddr] using mf hok)
          have done := cs_success (sk:=sk) hK hpre hR hi (T3.topFlip w) hd' (reward_credit_le hok)
          refine (TBSim.steps ((((((((s4.trans sc).trans s5).trans s6).trans s7).trans sf).trans s8).trans s9)) done).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_pos hlz];omega
        · rw [if_neg hok] at pf sf
          simp only [if_neg hok]
          refine (TBSim.steps ((((((s4.trans sc).trans s5).trans s6).trans s7).trans sf))
            (cs_next hK hTf pf hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_pos hlz];omega
      · rw [if_neg hs] at p6
        have hd' : WCT9.CanonicalPolicy.decode A.lay (T3.topFlip w)=none := by rw [hdec,if_neg hs]
        have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor (T3.topFlip w)=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
        rw [hpd]
        refine (TBSim.steps (((s4.trans sc).trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz];omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      obtain ⟨td,sd,pd,rd,fd⟩ := cs130_spec hK t4 p4
      have hTd := hT4.step rd (by decide) fd
      obtain ⟨ks,t5,ss,hs7,p5,h6s,h7s,r5,f5⟩ := selector_spec hK td pd a A.lay hlz
        ((rd.get (by decide)).trans h6) ((rd.get (by decide)).trans h7)
        (by rw [rd.get (by decide),r4.get (by decide),getReg_writeHash,h12])
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.1)
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.2)
      have s5 := sd.trans ss
      have hT5 := hTd.step r5 (by decide) f5
      change t5.pc=(if T3.lowerSpare v then _ else _) at p5
      change t5.getReg .x6=v.extractLsb' 0 64 at h6s
      change t5.getReg .x7=v.extractLsb' 64 64 at h7s
      have hnormal : WCT9.CanonicalPolicy.normalLayer A.lay≠0 := by
        simp [WCT9.CanonicalPolicy.normalLayer,hlz]
      have hdec := decode_low (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal v
      change WCT9.CanonicalPolicy.decode A.lay v=_ at hdec
      by_cases hr : T3.lowerSpare v
      · rw [if_pos hr] at p5
        obtain ⟨t6,s6,p6,h25',h28',r6,f6⟩ := cs132_spec hK t5 p5 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (target_lt _) h6s h7s
          (by rw [r5.get (by decide),rd.get (by decide),h25]) (by rw [hT5.reg (by decide),hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum≤T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) ∧ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum<8
        · rw [if_pos hs] at p6
          obtain ⟨t7,s7,p7,r7,f7⟩ := cs259_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=some (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) := by rw [hdec,if_pos ⟨hr,hs⟩]
          rw [producerDecode_lower hlz v A.floor _ hd' rfl]
          obtain ⟨k8,n8,t8,s8,n8le,p8,r8,f8⟩ := zero_rank_spec hK t7 p7 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
            (by
              have h : ∀ lay : T3.Layer,T3.target lay<256 := by decide
              exact h (WCT9.CanonicalPolicy.normalLayer A.lay)) hs.1
            (by rw [r7.get (by decide),r6.get (by decide),h6s])
            (by rw [r7.get (by decide),r6.get (by decide),h7s])
            (by rw [hT7.reg (by decide),hpre.x17]) (by rw [r7.get (by decide),h25'])
            (lowZeros_bound v (by
              have hmin : ∀ lay : T3.Layer,lay≠0 → 199≤T3.target lay := by decide
              have ht := hmin (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal;omega))
          have hT8 := hT7.step r8 (by decide) f8
          by_cases hok : (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v
          · rw [if_pos hok] at p8
            simp only [hok.1,hok.2,and_true]
            have hTables : Reward.RewardTablesOK t8 := hpre.reward.frame hT8.frame
              (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS; omega)
            obtain ⟨tR,nR,cR,hcR,sR,pR,mR,rR,fR⟩ := hK.2.2.2.2.2.2.lower_spec_credit t8 A.lay hlz v hTables p8
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
              (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (lowDigits v).sum A.floor
              (by rw [hT8.reg (by decide),hpre.x17])
              (by rw [r8.get (by decide),r7.get (by decide),h25']) hs.1 hs.2 A.hints hpre.hintsLt
              (by rw [hT8.reg (by decide),hpre.x8])
              (by rw [hT8.frame.get (by decide) (by unfold CsW CanonicalExpandHooks.CreditW ENC EOUT DigW DIGITS;omega),hpre.floorMem])
              hpre.floorEq
            have hTR := hT8.stepCredit rR (by decide) fR
            change tR.pc=(if rewardOK A.lay A.floor (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
              then pcOf (354+433) else pcOf (354+468)) at pR
            change cR≤(if rewardOK A.lay A.floor (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) then 103 else 97) at hcR
            change (rewardOK A.lay A.floor (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) → _) at mR
            by_cases hreward : rewardOK A.lay A.floor (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
            · rw [if_pos hreward] at pR hcR ⊢
              obtain ⟨k9,t9,s9,k9le,hR⟩ := cs_prepare hK hpre hTR pR hi22 hlz v hr _ _ hd' rfl hs.1
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),h25']) (mR hreward)
              have done := cs_success (sk:=sk) hK hpre hR hi v hd' (reward_credit_le hreward)
              refine (TBSim.steps ((((((s4.trans s5).trans s6).trans s7).trans s8).trans sR).trans s9) done).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
            · rw [if_neg hreward] at pR hcR ⊢
              refine (TBSim.steps (((((s4.trans s5).trans s6).trans s7).trans s8).trans sR)
                (cs_next hK hTR pR hi ih')).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
          · rw [if_neg hok] at p8
            have hno : ¬ (rewardOK A.lay A.floor (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) ∧
                (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v) := fun hh => hok hh.2
            simp only [if_neg hno]
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_ (fun _ _ h => h)
            simp only [csT,csOk,if_neg hlz];omega
        · rw [if_neg hs] at p6
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hs h.2)]
          have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
          rw [hpd]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_neg hlz];omega
      · rw [if_neg hr] at p5
        have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hr h.1)]
        have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
        rw [hpd]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_neg hlz];omega
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
variable {image : Image} {sk : BitVec 256}
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image 354 (CanonicalExpandHooks.Contract image)) (hpre : CsPre 354 A s0) :
    TBSim image sk s0 (18 + capLimit A.lay.val * csT A.lay + csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay)) (CsPost image 354 A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay A.tree A.leaf hpre.hroute
    hpre.x8 hpre.x9 hpre.x18 hpre.x15
  obtain ⟨t', st', pt', rt', ft'⟩ := cs113_spec hK t pt
  have hI : CsInv 354 A s0 0 t' := by
    refine ⟨pt', Nat.zero_le _, by rw [rt'.get (by decide), h19], by rw [ft'.get (by simp only [ENC]; omega) (by simp), h16],
      by rw [ft'.get (by simp only [ENC]; omega) (by simp), h24], ?_,
      (rt.trans rt').mono (by decide), (ft.trans ft').mono (fun A _ h => by
        rcases h with h | h
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd h id)⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft'.get (by simp only [ENC]; omega) (by simp), ft.get (by simp only [ENC]; omega)
      (by simp only [ENC]; omega), hx32]⟩
  rw [← capLimit_eq]
  have := TBSim.steps st (TBSim.steps st' (cs_loop (sk := sk) hK hpre (capLimit A.lay.val) 0 t' (by omega) hI))
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)

def csCost (lay : Layer) : Nat := (if lay=0 then T3.counterLimit*270 else WCT9.lowerSearchLimit*395)+8192

theorem counterSearch_good {A : CsArgs} {s0 : MachineState}
    (hK : KernAt image 354 (CanonicalExpandHooks.Contract image)) (hp : CsPre 354 A s0) :
    TBSim image sk s0 (csCost A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
      (CsPost image 354 A s0) := by
  refine (counterSearch_tbsim hK hp).mono ?_ (fun _ _ h=>h)
  have hl0 : (A.lay.val=0)↔A.lay=0 := ⟨fun h=>Fin.ext h,fun h=>by rw [h];rfl⟩
  unfold csCost capLimit csT csOk T3.counterLimit WCT9.lowerSearchLimit
  by_cases h : A.lay=0
  · rw [if_pos (hl0.2 h),if_pos h,if_pos h,if_pos h];norm_num
  · rw [if_neg (fun h'=>h (hl0.1 h')),if_neg h,if_neg h,if_neg h];norm_num
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

noncomputable def layout (image : Image) (k : Fin 9) : W9Machine.Layout :=
  ⟨image,Frozen.layout.chainWord,(SharedLayout.layout k).childWord,
    fun _=>endWord k.val-(if k.val=8 then 80 else 74)⟩

theorem steps (image : Image) (k : Fin 9) (u : MachineState)
    (hrun : symRun {} (words k.val) (pcOf (start k.val)) (length k.val)=some (result k.val))
    (hcode : CodeAt image (pcOf (start k.val)) (words k.val)) (hpc : u.pc=pcOf (start k.val)) :
    Steps image u (length k.val) (length k.val) ((result k.val).toState u) := by
  have h:=symRun_sound hrun hcode u hpc (by exact True.intro)
  exact h
#print axioms steps

theorem result_child_raw (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x23=
      (rawRead k.val u <<< (if k.val<8 ∧ k.val%2=0 then 7 else 8))+
        BitVec.ofNat 64 (4096+4*(if k.val<8 ∧ k.val%2=0 then 231616 else if k.val=8 then 235776 else 246464)) := by
  fin_cases k <;> rfl

#print axioms result_child_raw

theorem result_child (k : Fin 9) (u : MachineState) (raw : Fin 128)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val) :
    ((result k.val).toState u).getReg .x23=pcOf ((SharedLayout.layout k).childWord raw) := by
  change _=pcOf (SharedLayout.childWord k.val raw.val)
  rw [result_child_raw,hraw]
  unfold SharedLayout.childWord
  split_ifs <;> rw [BitVec.shiftLeft_eq_mul_twoPow]
  all_goals change BitVec.ofNat 64 raw.val * BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  all_goals rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]; congr 1 <;> norm_num [Nat.shiftLeft_eq] <;> omega

#print axioms result_child
theorem result_node_value (k : Fin 9) (u : MachineState) (index : Nat)
  (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index) : ((result k.val).toState u).getReg .x15=BitVec.ofNat 64 (V3.nodeLow k.val index) := by
  rw [result_node,hindex]
  apply BitVec.eq_of_toNat_eq
  simp only [V3.nodeLow,ClaudeWCT.WCT9.ftsLeafLow,Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (show k.val<16 by have := k.isLt; omega)]
  simp [BitVec.toNat_add,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega

#print axioms result_node_value
theorem result_hashMode (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x5=0 := by fin_cases k <;> rfl
theorem result_stepOne (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x7=1 := by fin_cases k <;> rfl
theorem result_stepTwo (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x13=2 := by fin_cases k <;> rfl
theorem result_hashLen (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x11=64 := by fin_cases k <;> rfl
theorem result_heaps (k : Fin 9) (u : MachineState) (h : Nat) (h2 : 2≤h) (h7 : h≤7) :
    ((result k.val).toState u).getReg (Child.heapReg h)=BitVec.ofNat 64 h := by
  interval_cases h <;> fin_cases k <;> rfl
#print axioms result_heaps

theorem result_pc_value (k : Fin 9) (u : MachineState) (rank : Nat)
    (hrank : rankRead k.val u=BitVec.ofNat 64 rank) :
    ((result k.val).toState u).pc=pcOf (195584+64*rank) := by
  have he : (BitVec.ofNat 64 rank <<< 8)+0xc0000#64=pcOf (195584+64*rank) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 rank * BitVec.ofNat 64 256 + BitVec.ofNat 64 786432 = BitVec.ofNat 64 _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    omega
  exact (result_pc k u).trans ((congrArg (fun x : Word=>((x <<< 8)+0xc0000#64) &&& ~~~1#64) hrank).trans
    ((congrArg (fun x : Word=>x &&& ~~~1#64) he).trans (pcOf_and_not1 _)))
#print axioms result_pc_value

theorem result_leaf_value (k : Fin 9) (u : MachineState) (index : Nat) (raw : Fin 128)
    (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val) :
    ((result k.val).toState u).getReg .x31=BitVec.ofNat 64 (V3.leafLow index k.val raw.val) := by
  have hp : (BitVec.ofNat 64 raw.val <<< 20)+BitVec.ofNat 64 (V3.nodeLow k.val index)=
      BitVec.ofNat 64 (V3.leafLow index k.val raw.val) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 raw.val * BitVec.ofNat 64 1048576 + BitVec.ofNat 64 _ = BitVec.ofNat 64 _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    simp only [V3.leafLow,V3.nodeLow,ClaudeWCT.WCT9.ftsLeafLow,Nat.zero_mod,Nat.zero_mul,Nat.add_zero,
      Nat.mod_eq_of_lt raw.isLt]
    omega
  exact (result_leaf k u).trans ((congrArg₂ (fun a b : Word=>(a <<< 20)+b) hraw
    (result_node_value k u index hi hindex)).trans hp)

#print axioms result_leaf_value

theorem chain_pre (image : Image) (k : Fin 9) (u : MachineState)
    (w : W9Machine.WBytes) (index : Nat) (raw : Fin 128) (rank : Fin 563)
    (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val)
    (hrank : rankRead k.val u=BitVec.ofNat 64 rank.val)
    (hslot : Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hW : ∀off,off<896 → off%8=0 → u.getMem (BitVec.ofNat 64 (coordinateBase k+off))=
      w.extractLsb' (8*(V3.regionOffset k.val+off)) 64) :
    N600.Pre (layout image k) w index k raw rank ((result k.val).toState u) := by
  have hk:=k.isLt
  have hj:=raw.isLt
  have hnode := result_node_value k u index hi hindex
  constructor
  all_goals try (case childIdx => exact (result_raw k u).trans hraw)
  case indexBound => exact hi
  case baseReg => exact result_base k u
  case nodeWord => exact hnode
  case childPC => exact result_child k u raw hraw
  case returnPC => exact result_return k u
  case pc =>
    exact (result_pc_value k u rank.val hrank).trans (congrArg pcOf hslot.symm)
  case leafWord => exact result_leaf_value k u index raw hi hindex hraw
  case hashMode => exact result_hashMode k u
  case stepOne => exact result_stepOne k u
  case stepTwo => exact result_stepTwo k u
  case hashLen => exact result_hashLen k u
  case heaps =>
    exact result_heaps k u
  case witness =>
    intro off ho h8
    rw [result_mem]
    exact hW off ho h8
#print axioms chain_pre
#print axioms steps
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def writes (addr : Nat) : Prop := 1200≤addr ∧ addr<9472
def isHand (n off : Nat) : Prop :=
  if n=9 then (720≤off ∧ off<752) ∨ (768≤off ∧ off<800) else SharedV3.isHand off
def pcWord (n : Nat) : Nat := if n<9 then SharedDispatch.start n else 46862
structure Fields (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563) (u : MachineState) : Prop where
  index : u.getMem 0x66010=BitVec.ofNat 64 index
  raw : ∀k,SharedDispatch.rawRead k.val u=BitVec.ofNat 64 (raw k).val
  rank : ∀k,SharedDispatch.rankRead k.val u=BitVec.ofNat 64 (ranks k).val
structure Inv (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (initial : MachineState) (n : Nat) (prev : Digest×Digest) (u : MachineState) : Prop where
  le : n≤9
  pc : u.pc=pcOf (pcWord n)
  fields : Fields index raw ranks u
  prevL : DigAt u (regionAddr n+720) prev.1
  prevR : DigAt u (regionAddr n+SharedV3.handR n) prev.2
  /-- Original witness words of the coordinates not yet run. Stage 2 (C3): region 9 (the L3 encoding row,
  `WIT + 0 .. WIT + 176`) excludes its offset `744` = `WIT + 24`, the row tweak's high word (a witness pad, honest
  LE64 1). No FTS routine reads it, and in the expander's first forest pass the cleared witness prefix still holds 0
  there (the final pass restores it, `SharedScatter.finishCode`). -/
  coords : ∀ (m : Nat), n ≤ m → m ≤ 9 → ∀ (off : Nat), off < 896 → off % 8 = 0 →
    (m = 9 → 720 ≤ off ∧ off ≠ 744) → (m = n → ¬ isHand n off) →
    W9Machine.OrigW w u (regionAddr m + off)
  frame : Frame initial u writes

theorem child_writes_bounds (k : Fin 9) (raw : Fin 128) (addr : Nat)
    (h : SharedChild.writes k raw addr) : writes addr := by
  have hk:=k.isLt
  unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr coordinateBase at h
  unfold writes
  split_ifs at h <;> omega

theorem fields_frame {index : Nat} {raw : Fin 9 → Fin 128} {ranks : Fin 9 → Fin 563}
    {u t : MachineState} (hf : Frame u t writes) (hu : Fields index raw ranks u) :
    Fields index raw ranks t := by
  have hm (addr : Nat) (ha : 9472≤addr) (hb : addr<2^64) :
      t.getMem (BitVec.ofNat 64 addr)=u.getMem (BitVec.ofNat 64 addr) :=
    hf addr hb (by unfold writes;omega)
  refine ⟨(hm 0x66010 (by decide) (by decide)).trans hu.index,?_,?_⟩
  · intro k
    rw [SharedDispatch.rawRead,hm _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    exact hu.raw k
  · intro k
    rw [SharedDispatch.rankRead,hm _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    exact hu.rank k

theorem witness_view {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {ranks : Fin 9 → Fin 563} {initial u : MachineState} {k : Fin 9} {prev : Digest×Digest}
    (hu : Inv w index raw ranks initial k.val prev u) :
    ∀off,off<896 → off%8=0 → u.getMem (BitVec.ofNat 64 (coordinateBase k+off))=
      (SharedV3.viewW w k.val u).extractLsb' (8*(V3.regionOffset k.val+off)) 64 := by
  intro off ho h8
  have hk:=k.isLt
  have hr8:=V3.regionOffset_mod k.val
  rw [SharedV3.view_word w k.val u _ (by omega) (by unfold V3.regionOffset;omega)]
  by_cases hh:SharedV3.isHand off
  · rw [if_pos ⟨by omega,by simpa only [Nat.add_sub_cancel_left] using hh⟩]
    congr 2
    unfold coordinateBase V3.regionOffset
    omega
  · rw [if_neg (fun h=>hh (by simpa only [Nat.add_sub_cancel_left] using h.2))]
    have hw:=hu.coords k.val (by omega) (by omega) off ho h8 (by omega)
      (fun _=>by simpa only [isHand,if_neg (by omega : k.val≠9)] using hh)
    have he:regionAddr k.val+off-0x4c0=V3.regionOffset k.val+off := by
      unfold regionAddr V3.regionOffset;omega
    have hb:coordinateBase k+off=regionAddr k.val+off := by unfold coordinateBase regionAddr;omega
    rw [hb]
    simpa only [W9Machine.OrigW,he] using hw

theorem core_frame {L : W9Machine.Layout} {w : W9Machine.WBytes} {index : Nat} {k : Fin 9}
    {raw : Fin 128} {u entry t : MachineState} {ends : List Digest} {computed : Digest}
    (hp : Chain.Post L w index k raw u ends entry) (ht : SharedChild.Post L k raw entry computed t) :
    Frame u t (SharedChild.writes k raw) := by
  intro addr ha hn
  rw [ht.frame addr ha hn]
  apply hp.frame addr ha
  intro h
  apply hn
  left
  unfold Chain.writes Chain.base at h
  omega

theorem core_frame_dispatch {L : W9Machine.Layout} {w : W9Machine.WBytes} {index : Nat} {k : Fin 9}
    {raw : Fin 128} {u entry t : MachineState} {ends : List Digest} {computed : Digest}
    (hp : Chain.Post L w index k raw ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : SharedChild.Post L k raw entry computed t) : Frame u t (SharedChild.writes k raw) := by
  intro addr ha hn
  exact (core_frame hp ht addr ha hn).trans (SharedDispatch.result_mem k u _)

theorem hand_address (k : Fin 9) (raw : Fin 128) :
    SharedChild.handAddr k raw=regionAddr (k.val+1)+
      (if SharedV3.direction k.val (SharedV3.physical k.val raw.val)=0 then 720 else SharedV3.handR (k.val+1)) := by
  have hk:=k.isLt
  unfold SharedChild.handAddr coordinateBase regionAddr SharedV3.handR
  split_ifs <;> omega

theorem next_other (w : W9Machine.WBytes) (k : Fin 9) (raw : Fin 128)
    (u t : MachineState) (hf : Frame u t (SharedChild.writes k raw)) (off : Nat)
    (hoff : off=720 ∨ off=SharedV3.handR (k.val+1))
    (hsel : if SharedV3.direction k.val (SharedV3.physical k.val raw.val)=0
      then off=SharedV3.handR (k.val+1) else off=720)
    (h0 : W9Machine.OrigW w u (regionAddr (k.val+1)+off))
    (h1 : W9Machine.OrigW w u (regionAddr (k.val+1)+(off+8))) :
    DigAt t (regionAddr (k.val+1)+off)
      (SharedV3.topOther w k.val (SharedV3.physical k.val raw.val)) := by
  have hk:=k.isLt
  have h1':W9Machine.OrigW w u (regionAddr (k.val+1)+off+8) := by rw [Nat.add_assoc];exact h1
  have hlo:0x4c0≤regionAddr (k.val+1)+off := by
    unfold SharedV3.handR at hoff
    unfold regionAddr
    split_ifs at hoff <;> omega
  have hd:=W9Machine.DigAt_origW h0 h1' hlo
  have he:regionAddr (k.val+1)+off-0x4c0=SharedV3.topOtherOff k.val (SharedV3.physical k.val raw.val) := by
    unfold SharedV3.topOtherOff V3.regionOffset regionAddr
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hd
  refine hd.frame hf (by unfold SharedV3.handR at hoff;unfold regionAddr;split_ifs at hoff <;> omega) ?_ ?_
  all_goals
    intro hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr coordinateBase at hw
    unfold SharedV3.handR at hoff hsel
    unfold regionAddr at hw
    split_ifs at hsel hw <;> omega

#print axioms witness_view
#print axioms fields_frame
#print axioms core_frame_dispatch
#print axioms next_other
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem next {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {ranks : Fin 9 → Fin 563} {initial u entry t : MachineState} {k : Fin 9} {prev : Digest×Digest}
    {ends : List Digest} {computed : Digest} (hu : Inv w index raw ranks initial k.val prev u)
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewW w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : SharedChild.Post (SharedDispatch.layout image k) k (raw k) entry computed t) :
    Inv w index raw ranks initial (k.val+1)
      (SharedV3.orderPair k.val (SharedV3.physical k.val (raw k).val) computed
        (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val))) t := by
  have hk:=k.isLt
  have hf:=core_frame_dispatch hp ht
  have hfg:Frame u t writes:=hf.mono (fun addr _ hw=>child_writes_bounds k (raw k) addr hw)
  have hother:∀off,(off=720 ∨ off=SharedV3.handR (k.val+1)) → 
      (if SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
        then off=SharedV3.handR (k.val+1) else off=720) → 
      DigAt t (regionAddr (k.val+1)+off) (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val)) := by
    intro off hoff hsel
    have ho:off≤768 ∧ off%8=0 ∧ (k.val+1=9 → off=720 ∨ off=768) := by
      unfold SharedV3.handR at hoff;split_ifs at hoff <;> omega
    exact next_other w k (raw k) u t hf off hoff hsel
      (hu.coords (k.val+1) (by omega) (by omega) off (by omega) (by omega)
        (fun h=>by have:=ho.2.2 h;omega) (fun h=>by omega))
      (hu.coords (k.val+1) (by omega) (by omega) (off+8) (by omega) (by omega)
        (fun h=>by have:=ho.2.2 h;omega) (fun h=>by omega))
  refine ⟨by omega,?_,fields_frame hfg hu.fields,?_,?_,?_,?_⟩
  · rw [ht.pc]
    fin_cases k <;> rfl
  · unfold SharedV3.orderPair
    by_cases hd:SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
    · rw [if_pos hd]
      have he:SharedChild.handAddr k (raw k)=regionAddr (k.val+1)+720:=by rw [hand_address,if_pos hd]
      rw [←he]
      exact ht.top
    · rw [if_neg hd]
      exact hother 720 (Or.inl rfl) (by rw [if_neg hd])
  · unfold SharedV3.orderPair
    by_cases hd:SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
    · rw [if_pos hd]
      exact hother (SharedV3.handR (k.val+1)) (Or.inr rfl) (by rw [if_pos hd])
    · rw [if_neg hd]
      have he:SharedChild.handAddr k (raw k)=regionAddr (k.val+1)+SharedV3.handR (k.val+1):=by
        rw [hand_address,if_neg hd]
      rw [←he]
      exact ht.top
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0:=hu.coords m (by omega) hm9 off hoff h8 hv (fun h=>by omega)
    unfold W9Machine.OrigW at h0 ⊢
    rw [←h0]
    apply hf _ (by unfold regionAddr;omega)
    intro hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr coordinateBase at hw
    have hmk:regionAddr m+896≤regionAddr k.val:=by unfold regionAddr;omega
    rcases Nat.lt_or_ge (k.val+1) m with hgt|hle
    · have :regionAddr m+896≤regionAddr (k.val+1):=by unfold regionAddr;omega
      unfold coordinateBase regionAddr at *
      split_ifs at hw <;> omega
    · have hm':m=k.val+1:=by omega
      subst hm'
      have hn:=hh rfl
      unfold isHand SharedV3.isHand at hn
      unfold coordinateBase regionAddr at *
      split_ifs at hn <;> split_ifs at hw <;> omega
  · intro addr ha hn
    exact (hfg addr ha hn).trans (hu.frame addr ha hn)
#print axioms next
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open SigGolfCandidate.T3M SigGolfCandidate.Rv SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
 theorem code_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver)
    (k : Fin 9) : CodeAt im (pcOf (start k.val)) (words k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=1457) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1495) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1534) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1573) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1612) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1651) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1690) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1729) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1768) hc (by decide +kernel) (by decide +kernel)
theorem installed_code (k : Fin 9) : CodeAt Images.expandImage (pcOf (start k.val)) (words k.val) :=
  code_of_driver codeAt_expand_shared_driver k
#print axioms installed_code
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem step_tbsim (image : Image) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072=(image.code.drop 195584).take 59072)
    (hchecked : ∀k:Fin 9,symRun {} (SharedDispatch.words k.val) (pcOf (SharedDispatch.start k.val))
      (SharedDispatch.length k.val)=some (SharedDispatch.result k.val))
    (hcode : ∀k:Fin 9,CodeAt image (pcOf (SharedDispatch.start k.val)) (SharedDispatch.words k.val))
    (hslot : ∀rank:Fin 563,Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hcore : ∀ (L:W9Machine.Layout) (k:Fin 9) (j:Fin 128) (rank:Fin 563),
      (Frozen.image.code.drop 195584).take 59072=(L.image.code.drop 195584).take 59072 → 
      (∀i,L.childWord i=(SharedLayout.layout k).childWord i) → 
      (∀r,L.chainWord r=Frozen.layout.chainWord r) → 
      ∀w index snapshot u padL padR,
      N600.Pre L (SharedV3.viewW w k.val snapshot) index k j rank u → 
      DigAt snapshot (0x4c0+V3.regionOffset k.val+720) padL → 
      DigAt snapshot (0x4c0+V3.regionOffset k.val+160) padR → 
      TBSim L.image sk u (89+SharedChild.cost k j)
        (N600.program w index k j rank >>=fun ends=>SharedV3.childN w index k j ends padL padR)
        (SharedCore.Post L (SharedV3.viewW w k.val snapshot) index k j u))
    (w : W9Machine.WBytes) (index : Nat) (hi : index<2^31) (raw : Fin 9 → Fin 128)
    (ranks : Fin 9 → Fin 563) (initial : MachineState) (k : Fin 9) (prev : Digest×Digest)
    (u : MachineState) (hu : Inv w index raw ranks initial k.val prev u) :
    TBSim image sk u 224 (SharedV3.coordinate w index k (raw k) (N600.embed (ranks k)) prev)
      (Inv w index raw ranks initial (k.val+1)) := by
  let L:=SharedDispatch.layout image k
  let v:=(SharedDispatch.result k.val).toState u
  have hs:=SharedDispatch.steps image k u (hchecked k) (hcode k)
    (by simpa only [pcWord,if_pos k.isLt] using hu.pc)
  have hc:=SharedDispatch.chain_pre image k u (SharedV3.viewW w k.val u) index (raw k) (ranks k)
    hi hu.fields.index (hu.fields.raw k) (hu.fields.rank k) (hslot _) (witness_view hu)
  have hL:DigAt u (0x4c0+V3.regionOffset k.val+720) prev.1 := by
    convert hu.prevL using 1 <;> unfold V3.regionOffset regionAddr <;> have:=k.isLt <;> omega
  have hR:DigAt u (0x4c0+V3.regionOffset k.val+160) prev.2 := by
    convert hu.prevR using 1 <;> unfold V3.regionOffset regionAddr SharedV3.handR <;>
      have:=k.isLt <;> simp only [if_neg (by omega : k.val≠9)] <;> omega
  have hb:=hcore L k (raw k) (ranks k) hwindow (fun _=>rfl) (fun _=>rfl)
    w index u v prev.1 prev.2 hc hL hR
  -- Use the explicit existential postcondition to attach the hand-off pair.
  have hj' : TBSim image sk v ((89+SharedChild.cost k (raw k))+0)
      ((N600.program w index k (raw k) (ranks k) >>=fun ends=>
        SharedV3.childN w index k (raw k) ends prev.1 prev.2) >>=fun computed=>
        pure (SharedV3.orderPair k.val (SharedV3.physical k.val (raw k).val) computed
          (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val))))
      (Inv w index raw ranks initial (k.val+1)) := by
    refine TBSim.bind hb ?_
    intro computed t ht
    obtain ⟨ends,entry,hp,ht⟩:=ht
    exact TBSim.pure (next hu hp ht)
  have hh:=TBSim.steps hs hj'
  have hlen:SharedDispatch.length k.val≤39:=by fin_cases k <;> decide
  have hcost:SharedChild.cost k (raw k)≤96:=by
    unfold SharedChild.cost SharedChild.spill
    split_ifs <;> omega
  simpa only [SharedV3.coordinate,N600.program,bind_assoc] using
    hh.mono (show SharedDispatch.length k.val+((89+SharedChild.cost k (raw k))+0)≤224 by omega)
      (fun _ _ h=>h)

#print axioms step_tbsim

 theorem forest_tbsim (image : Image) (sk : BitVec 256)
    (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (initial : MachineState)
    (hstep : ∀k:Fin 9,∀prev u,Inv w index raw ranks initial k.val prev u → 
      TBSim image sk u 224 (SharedV3.coordinate w index k (raw k) (N600.embed (ranks k)) prev)
        (Inv w index raw ranks initial (k.val+1)))
    (h0 : Inv w index raw ranks initial 0 (SharedV3.initialPair w) initial) :
    TBSim image sk initial 2016 (SharedV3.forest w index raw (fun k=>N600.embed (ranks k)))
      (fun pair t=>t.pc=pcOf 46862 ∧ DigAt t 1216 pair.1 ∧ DigAt t 1264 pair.2 ∧
        Frame initial t writes ∧ Fields index raw ranks t) := by
  have he {α:Type} (f:α → Fin 9 → M α) (init:α) :
      (List.finRange 9).foldlM f init=(List.range' 0 9).foldlM
        (fun st n=>if h:n<9 then f st ⟨n,h⟩ else pure st) init := by
    rw [show List.finRange 9=[0,1,2,3,4,5,6,7,8] from rfl,
      show List.range' 0 9=[0,1,2,3,4,5,6,7,8] from rfl]
    simp only [List.foldlM_cons,List.foldlM_nil]
    rfl
  unfold SharedV3.forest
  rw [he]
  have hs:=TBSim.foldlM_range' (image:=image) (sk:=sk) 0 9
    (fun (prev:Digest×Digest) (n:Nat)=>if h:n<9 then
      SharedV3.coordinate w index ⟨n,h⟩ (raw ⟨n,h⟩) (N600.embed (ranks ⟨n,h⟩)) prev else pure prev)
    (SharedV3.initialPair w)
    (fun n prev u=>Inv w index raw ranks initial n prev u) 224
    (fun n hn prev u hu=>by simpa only [Nat.zero_add,dif_pos hn] using hstep ⟨n,hn⟩ prev u hu) h0
  exact hs.mono (by decide) (fun pair t ht=>⟨ht.pc,ht.prevL,ht.prevR,ht.frame,ht.fields⟩)

#print axioms forest_tbsim
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem forest_tbsim_of_bank (image : Image) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072=(image.code.drop 195584).take 59072)
    (hcode : ∀k:Fin 9,CodeAt image (pcOf (SharedDispatch.start k.val)) (SharedDispatch.words k.val))
    (hslot : ∀rank:Fin 563,Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hchain : ∀ (L : W9Machine.Layout),
      (Frozen.image.code.drop 195584).take 59072=(L.image.code.drop 195584).take 59072 →
      (∀ rank,L.chainWord rank=Frozen.layout.chainWord rank) →
      ∀ (rank:Fin 563) (w:W9Machine.WBytes) (index:Nat) (k:Fin 9) (j:Fin 128) (u:MachineState),
      N600.Pre L w index k j rank u →
      TBSim L.image sk u 89 (N600.program w index k j rank) (N600.Post L w index k j u))
    (w : W9Machine.WBytes) (index : Nat) (hi:index<2^31) (raw : Fin 9 → Fin 128)
    (ranks : Fin 9 → Fin 563) (initial : MachineState)
    (h0 : Inv w index raw ranks initial 0 (SharedV3.initialPair w) initial) :
    TBSim image sk initial 2016 (SharedV3.forest w index raw (fun k=>N600.embed (ranks k)))
      (fun pair t=>t.pc=pcOf 46862 ∧ DigAt t 1216 pair.1 ∧ DigAt t 1264 pair.2 ∧
        Frame initial t writes ∧ Fields index raw ranks t) := by
  apply forest_tbsim image sk w index raw ranks initial ?_ h0
  intro k prev u hu
  apply step_tbsim image sk hwindow SharedDispatch.checked hcode hslot ?_ w index hi raw ranks initial k prev u hu
  intro L k j rank hw hc hcw w index snapshot u padL padR hpre hL hR
  exact SharedCore.core_tbsim L sk hw k j rank hc
    (fun w index u hu=>hchain L hw hcw rank w index k j u hu) w index snapshot u padL padR hpre hL hR
#print axioms forest_tbsim_of_bank
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost CsW csRegs csCost)
open SigGolfCandidate.T3M.Search.CanonicalExpandHooks (creditAddr CreditW hintFloor hintFloor_lt creditAddr_lt)
open ClaudeWCT
open SigGolfCandidate.T3M.Expand.BC
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
structure LInv (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (value : WCT9.LayerMsg) (s : MachineState) extends BC.LInv sig index n value s where
  hintsLt : hints.toNat<5832
  hintsMem : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat

def stage (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (value : WCT9.LayerMsg) :
    SigGolfCandidate.T3.M (Option (BitVec 32 × List Nat × WCT9.LayerMsg × Digest)) := do
  let lay : Layer := Fin.ofNat 4 n
  let some (c,ds) ← WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor hints lay)
    (route index lay).2 (route index lay).1 value 0 (WCT9.searchLimit lay) | pure none
  let mv ← BC.recoverMsg sig index lay ds
  pure (some (c,ds,mv.1,mv.2))
def stageCost (lay : Layer) : Nat := lK lay+csCost lay+10+rlCost lay

def StagePost (im : Image) (s : MachineState) (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) :
    Option (BitVec 32 × List Nat × WCT9.LayerMsg × Digest) → MachineState → Prop
  | none,t => t.pc=pcOf 356 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)
  | some (c,ds,msg,v),t =>
    let lay : Layer := Fin.ofNat 4 n
    LInv sig hints index n msg t ∧
    (∀ i<chainCount lay,DigAt t (lWC lay-64*i+48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j<height lay,DigAt t (lWM lay-64*j+sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j)) ∧
    Frame s t (fun A=>CsW lay A ∨ A=lD lay ∨ BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) ∧
    RegsExcept s t lRegs ∧
    t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit lay ds) ∧
    ds.length=chainCount lay ∧ (∃ a,WCT9.CanonicalPolicy.decode lay a=some ds) ∧
    (lay=0 → TopBlkG (WCT9.toT3Signature sig) index lay v t) ∧
    t.getMem (BitVec.ofNat 64 (lD lay))=replaceWord32 (s.getMem (BitVec.ofNat 64 (lD lay))) (lk lay) (BitVec.ofNat 32 c.toNat) ∧
    hintFloor hints lay ≤ WCT9.CanonicalPolicy.credit lay ds

theorem decode_digit_le {lay : Layer} {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode lay v = some ds) :
    ∀ i<chainCount lay,ds.getD i 0 ≤ maxDigit lay i := by
  fin_cases lay <;> exact fun i hi=>T3.decode_digit_max h i hi

variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] {sk : BitVec 256}
variable (hSearch : ∀ (A : CsArgs) (s0 : MachineState),CsPre 354 A s0 →
  TBSim im sk s0 (csCost A.lay)
    (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
    (CsPost im 354 A s0))
include hSearch in
theorem stage_good {sig : WCT9.Signature} {hints : BitVec 16} {index n : Nat} {value : WCT9.LayerMsg} {s : MachineState}
    (hn : n<4) (hI : LInv sig hints index (n+1) value s) :
    TBSim im sk s (stageCost (Fin.ofNat 4 n)) (stage sig hints index n value) (StagePost im s sig hints index n) := by
  set lay : Layer := Fin.ofNat 4 n with hlay
  have hlv : lay.val = n := fin_ofNat_val n hn
  have htab := ltable lay
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hI.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨t1, s1, p1, x1, x8, x15, x26, x27, x17, x18, x9, r1, f1⟩ :=
    SharedRecover.lentry_spec (im := im) lay s (by rw [hI.pc]; rfl) index hI.hidx hI.idx
  have g1 : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f1.get hA (fun h => h)
  obtain ⟨x, hx, hx32⟩ := hI.c32
  have htable1 : Search.TableOK t1 := hI.table.frame f1 (by intro i hi h; exact h)
  have hcs : CsPre 354 ⟨lay, tree, leaf, value, lR1 lay, hintFloor hints lay, hints⟩ t1 :=
    ⟨p1, x1, by rw [r1.get (by decide)]; exact hI.x5, x8, x9, x18, (by convert x17 using 2; clear_value lay; fin_cases lay <;> rfl), x26, x27, htree, hleaf32,
      route_routed index lay hI.hidx, Or.inr x15, by rw [g1 _ (by decide)]; exact hI.enc.1, by rw [g1 _ (by decide)]; exact hI.enc.2,
      ⟨x, hx, by rw [g1 _ (by decide)]; exact hx32⟩, by rw [g1 _ (by decide)]; exact hI.z.e40,
      by rw [g1 _ (by decide)]; exact (hI.right (by omega)).1, by rw [g1 _ (by decide)]; exact (hI.right (by omega)).2, htable1,
      hI.cf.frame f1 (by intro i hi hi' h; exact h),
      hI.reward.frame f1 (by intro i hi hi' h; exact h), hintFloor_lt hints lay, (fun he => by change lay=0 at he; change hintFloor hints lay=16;rw [he];rfl), hI.hintsLt, rfl, by rw [g1 _ (by decide)]; exact hI.hintsMem⟩
  unfold stage
  change TBSim im sk s _ (_ >>= _) _
  refine (TBSim.steps s1 (TBSim.bind (W₂ := 10 + rlCost lay)
    (hSearch _ _ hcs) (fun r t2 h2 => ?_))).mono
    (by simp only [stageCost, ← hlay]; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds⟩
  · exact (TBSim.pure (Q := StagePost im s sig hints index n) (a := none) h2).mono (by omega) (fun _ _ h => h)
  · obtain ⟨p2, hc, x19, e32, ⟨v, hdec⟩, hlen, hdig, r2, f2, _, credit2, creditFloor2⟩ := h2
    dsimp only at p2 hc x19 e32 hdec hlen hdig
    change Frame t1 t2 (CsW lay) at f2
    obtain ⟨t3, s3, p3, x1', hD, x16, x23, x24, r3, f3⟩ := SharedRecover.lpost_spec (im := im) lay t2 p2 c.toNat x19
    have g3 : ∀ r, r ∉ [Reg.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] → r ∉ csRegs →
        r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = s.getReg r :=
      fun r h1 h2 h3 => by rw [r3.get h3, r2.get h2, r1.get h1]
    have g3' : ∀ r, r ∉ csRegs → r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = t1.getReg r :=
      fun r h2 h3 => by rw [r3.get h3, r2.get h2]
    have m3 : ∀ A, A < 2 ^ 64 → ¬ CsW lay A → A ≠ lD lay → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 h2 => by rw [f3.get hA h2, f2.get hA h1, g1 A hA]
    have hcsw : ∀ A, (A < 0x20260 ∨ (0x20460 ≤ A ∧ A < 0x66040)) → ¬ CsW lay A := by
      intro A hA h; unfold CsW Search.DigW CreditW creditAddr at h; simp only [ENC, EOUT, DIGITS] at h; omega
    have hrl : RlPre t3 (WCT9.toT3Signature sig) index lay ds (lP lay) (lWC lay) (lWM lay) (lR2 lay) := by
      refine ⟨p3, x1', by rw [g3 _ (by decide) (by decide) (by decide)]; exact hI.x5,
        by rw [g3' _ (by decide) (by decide)]; exact x8, by rw [g3' _ (by decide) (by decide)]; exact x9,
        by rw [g3' _ (by decide) (by decide)]; exact x18, by rw [g3' _ (by decide) (by decide)]; exact x15,
        by rw [g3' _ (by decide) (by decide)]; exact x26, by rw [g3' _ (by decide) (by decide)]; exact x27,
        x16, x23, x24, hI.hidx, htab.1, htab.2.1, htab.2.2.1, htab.2.2.2.1, htab.2.2.2.2.1, htab.2.2.2.2.2.1,
        htab.2.2.2.2.2.2.1, htab.2.2.2.2.2.2.2.1, ?_, decode_digit_le hdec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [Frame.getByte f3 (by simp only [DIGITS]; omega)
          (by have := htab.2.2.2.2.2.2.2.2.1; simp only [DIGITS]; omega)]
        exact hdig i hi
      · intro i hi
        have hv := (hI.sigl lay).1 i hi
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      · intro j hj
        have hv := (hI.sigl lay).2 j hj
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      all_goals
        first
          | (rw [m3 _ (by decide) (hcsw _ (by simp only [CHAIN, NODE, LEAFPK]; omega))
              (by have := htab.2.2.2.2.2.2.2.2.1; simp only [CHAIN, NODE, LEAFPK]; omega)]
             first | exact hI.z.c0 | exact hI.z.c8 | exact hI.z.c32 | exact hI.z.c40 | exact hI.z.n32 |
               exact hI.z.n40)
    refine (TBSim.steps s3 (TBSim.bind (W₂ := 0) (SharedRecover.recoverMsg_tbsim (im := im) (sk := sk) hrl)
      (fun mv t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
    obtain ⟨p4, e4, er4, form4, cv4, pv4, r4, f4, blk4⟩ := h4
    have hfar4 : ∀ A, A < 2 ^ 64 → ¬ CsW lay A → A ≠ lD lay → (A < 0x2c48 ∨ 0x7000 ≤ A) → ¬ BC.RlScratch A →
        t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      have hw : ¬ (BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) := by
        rintro (h | h)
        · exact h4 h
        · have := rlWit_range h; have := ltable_lo lay; omega
      rw [f4.get hA hw, m3 A hA h1 h2]
    have hd8 := htab.2.2.2.2.2.2.2.2.1
    have hd0 := htab.2.2.2.2.2.2.2.2.2.1
    have ncs : ∀ A, (A < 0x20260 ∨ (0x20260 + 40 ≤ A ∧ A < EOUT) ∨ (0x20460 ≤ A ∧ A < 0x66040)) → ¬ CsW lay A := by
      intro A hA h; unfold CsW Search.DigW CreditW creditAddr at h; simp only [ENC, EOUT, DIGITS] at h hA; omega
    have nrl : ∀ A, ((A < CHAIN + 16 ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 48) ∨ CHAIN + 80 ≤ A) ∧
        (A < NODE ∨ (NODE + 32 ≤ A ∧ A < NODE + 48) ∨ NOUT + 32 ≤ A) ∧ (A < LEAFPK ∨ LEAFPK + 896 ≤ A) ∧
        A ≠ ENC ∧ A ≠ ENC + 8 ∧ A ≠ ENC + 48 ∧ A ≠ ENC + 56 ∧ (A % 8 = 0)) → ¬ BC.RlScratch A := by
      intro A hA h; unfold BC.RlScratch Expand.RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h hA; omega
    have hI4base : BC.LInv sig index n mv.1 t4 := by
      have hx5 : t4.getReg .x5 = 0 := by
        rw [r4.get (by decide), g3 _ (by decide) (by decide) (by decide)]; exact hI.x5
      refine ⟨by rw [p4, hlay, lR2_eq n hn], by omega, hx5, hI.hidx, ?_, e4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfar4 IDXV (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
        exact hI.idx
      · intro hn0
        exact er4 (by intro he; have hv := congrArg Fin.val he; change lay.val = 0 at hv; omega)
      · intro hn0
        exact form4 (Fin.ext (by simpa only [Fin.val_zero] using hlv.trans hn0))
      · refine ⟨c.toNat, by omega, ?_⟩
        have hw : ¬ (BC.RlScratch (ENC + 32) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (ENC + 32)) := by
          rintro (h | h)
          · exact nrl _ (by decide) h
          · have h1 := rlWit_range h; have := ltable_lo lay; have := htab.2.2.2.2.2.2.2.1
            simp only [ENC] at h1; omega
        rw [f4.get (by decide) hw, f3.get (by decide) (by simp only [ENC]; omega), e32]
      · intro lay'
        have htab' := ltable lay'
        have hb := htab'.2.1
        have hb0 := htab'.1
        have hb8 := htab'.2.2.1
        refine ⟨fun i hi => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
        · rw [hfar4 (lP lay' + 16 * i) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).1
        · rw [hfar4 (lP lay' + 16 * i + 8) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).2
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).1
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j + 8) (by omega) (ncs _ (by omega)) (by omega)
            (by omega) (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).2
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfar4 CHAIN (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c0
        · rw [hfar4 (CHAIN + 8) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c8
        · rw [hfar4 (CHAIN + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c32
        · rw [hfar4 (CHAIN + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c40
        · rw [hfar4 (NODE + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n32
        · rw [hfar4 (NODE + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n40
        · rw [hfar4 (ENC + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.e40
      · apply hI.table.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi h
        rcases h with ((h | h) | h) | h
        · exact h
        · unfold CsW Search.DigW CreditW creditAddr at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold BC.RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
      · apply hI.cf.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi hi' h
        rcases h with ((h | h) | h) | h
        · exact h
        · unfold CsW Search.DigW CreditW creditAddr at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold BC.RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
      · apply hI.reward.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi hi' h
        rcases h with ((h | h) | h) | h
        · exact h
        · unfold CsW Search.DigW CreditW creditAddr at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold BC.RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
    have frame4 : Frame s t4 (fun A => CsW lay A ∨ A=lD lay ∨ BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) :=
      (((f1.trans f2).trans f3).trans f4).mono (fun A _ h=>by
        rcases h with ((h|h)|h)|h|h
        · exact h.elim
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h)))
    have hint4 : t4.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat := by
      rw [frame4.get (by decide) ?_]
      · exact hI.hintsMem
      · intro h
        rcases h with h|h|h|h
        · unfold CsW Search.DigW CreditW creditAddr at h
          have := lay.isLt
          simp only [ENC,EOUT,DIGITS] at h
          omega
        · have := ltable lay; omega
        · unfold BC.RlScratch Expand.RlScratch at h
          simp only [ENC,NODE,NOUT,CHAIN,LEAFPK] at h
          omega
        · have := rlWit_range h; have := ltable lay; omega
    have credit4 : t4.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit lay ds) := by
      have ha := creditAddr_lt lay
      have hr : 0x66040≤creditAddr lay ∧ creditAddr lay<0x66060 := by unfold creditAddr;have:=lay.isLt;omega
      rw [f4.get ha ?_, f3.get ha ?_]
      · exact credit2
      · have := ltable lay; omega
      · rintro (h|h)
        · unfold BC.RlScratch Expand.RlScratch at h
          simp only [ENC,NODE,NOUT,CHAIN,LEAFPK] at h
          omega
        · have := rlWit_range h;have:=ltable lay;omega
    refine TBSim.pure ⟨⟨hI4base,hI.hintsLt,hint4⟩,cv4,pv4,frame4,?_,credit4,hlen,⟨v,hdec⟩,blk4,?_,creditFloor2⟩
    · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
    · have hw : ¬ (BC.RlScratch (lD lay) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (lD lay)) := by
        rintro (h|h)
        · unfold BC.RlScratch Expand.RlScratch at h; simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
        · exact counter_ne_wit lay lay _ h
      rw [f4.get (by omega) hw,hD,f2.get (by omega) (ncs _ (by omega)),g1 _ (by omega)]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp

#print axioms stage_good
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost CsW csRegs csCost)
open SigGolfCandidate.T3M.Search.CanonicalExpandHooks (creditAddr CreditW hintFloor)
open ClaudeWCT
open SigGolfCandidate.T3M.Expand.BC
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
abbrev Recovered := SigGolfCandidate.Research.SharedForest.RecoveredLayers
def run (sig : WCT9.Signature) (hints : BitVec 16) (index : Nat) :
    Nat → WCT9.LayerMsg → Digest → SigGolfCandidate.T3.M (Option Recovered)
  | 0,.forest root,v => pure (some ⟨v,root,[],[]⟩)
  | 0,.pair _ _,_ => pure none
  | n+1,msg,_ => do
    let some (c,ds,msg',v') ← stage sig hints index n msg | pure none
    let some previous ← run sig hints index n msg' v' | pure none
    pure (some {previous with counters:=previous.counters++[c],digits:=previous.digits++[ds]})
def cost : Nat → Nat
  | 0 => 0
  | n+1 => stageCost (Fin.ofNat 4 n)+cost n

def LW (index n : Nat) (A : Nat) : Prop :=
  Search.CsW A ∨ BC.RlScratch A ∨ ∃ lay : Layer,lay.val<n ∧
    (A=lD lay ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A ∨ CreditW lay A)
def Post (im : Image) (s : MachineState) (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (vin : Digest) :
    Option Recovered → MachineState → Prop
  | none,t => t.pc=pcOf 356 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)
  | some r,t => t.pc=pcOf 342 ∧ t.getReg .x5=0 ∧ DigAt t ENC r.root ∧
    r.counters.length=n ∧ r.digits.length=n ∧
    (∀ lay : Layer,lay.val<n → LayerOut t sig index lay (r.counters.getD lay.val 0)) ∧
    (∀ lay : Layer,lay.val<n → t.getMem (BitVec.ofNat 64 (creditAddr lay))=
      BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit lay (r.digits.getD lay.val []))) ∧
    HalfFrame s t n ∧ RegsExcept s t lRegs ∧ Frame s t (LW index n) ∧
    (n=0 → t=s ∧ r.foldedTop=vin) ∧
    (n≠0 → TopBlkG (WCT9.toT3Signature sig) index 0 r.foldedTop t) ∧
    t.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat ∧
    (∀ lay : Layer,lay.val<n → hintFloor hints lay ≤ WCT9.CanonicalPolicy.credit lay (r.digits.getD lay.val []))

theorem scoped_write {lay : Layer} {A : Nat} :
    CsW lay A ↔ Search.CsW A ∨ CreditW lay A := by
  unfold CsW Search.CsW
  tauto

theorem counter_not_scratch (lay : Layer) : ¬BC.RlScratch (lD lay) := by
  fin_cases lay <;> simp [BC.RlScratch,Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC,lD]

theorem stage_half {im : Image} {s t : MachineState} {sig : WCT9.Signature} {hints : BitVec 16}
    {index n : Nat} {c : BitVec 32} {ds : List Nat} {msg : WCT9.LayerMsg} {v : Digest}
    (h : StagePost im s sig hints index n (some (c,ds,msg,v)) t) :
    ∀D k,(D=0x3ce8 ∨ D=0x4968 ∨ D=0x55a8 ∨ D=0x820 ∨ D=0x810 ∨ D=0x818) → k<2 →
      ¬(lD (Fin.ofNat 4 n)=D ∧ lk (Fin.ofNat 4 n)=k) →
      (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32*k) 32=(s.getMem (BitVec.ofNat 64 D)).extractLsb' (32*k) 32 := by
  intro D k hD hk hn
  let lay : Layer:=Fin.ofNat 4 n
  obtain ⟨hi,cv,pv,ff,rr,credit,len,dec,blk,ctr,floor⟩:=h
  have ht:=ltable lay
  by_cases he : D=lD lay
  · rw [he,ctr,replaceWord32_other _ _ _ ht.2.2.2.2.2.2.2.2.2.2 hk (fun h=>hn ⟨he.symm,h⟩)]
  · rw [ff.get (by omega) ?_]
    rintro (hs|hd|hs|hw)
    · unfold CsW Search.DigW CreditW creditAddr at hs
      simp only [ENC,EOUT,DIGITS] at hs
      omega
    · exact he hd
    · unfold BC.RlScratch Expand.RlScratch at hs
      simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at hs
      omega
    · rcases hD with rfl|rfl|rfl|rfl|rfl|rfl
      · exact counter_ne_wit 0 lay _ hw
      · exact counter_ne_wit 1 lay _ hw
      · exact counter_ne_wit 2 lay _ hw
      · exact counter_ne_wit 3 lay _ hw
      · have:=rlWit_range hw;have:=ltable_lo (Fin.ofNat 4 n);omega
      · have:=rlWit_range hw;have:=ltable_lo (Fin.ofNat 4 n);omega

theorem old_wit_preserved {index n : Nat} {lay : Layer} (hn : n≤lay.val) {A : Nat}
    (hw : RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) : ¬LW index n A := by
  have hr:=rlWit_range hw
  have ht:=ltable lay
  intro h
  rcases h with h|h|⟨lay',hl,h|h|h⟩
  · unfold Search.CsW Search.DigW at h; simp only [ENC,EOUT,DIGITS] at h;omega
  · unfold BC.RlScratch Expand.RlScratch at h;simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h
    have:=ltable_lo lay;omega
  · rw [h] at hw;exact counter_ne_wit lay' lay _ hw
  · have hne : lay'≠lay := by intro he;subst he;omega
    have hr':=rlWit_range h
    rcases ltable_disj lay' lay hne with hd|hd <;> omega
  · unfold CreditW creditAddr at h;omega

theorem old_credit_preserved {index n : Nat} {lay : Layer} (hn : n≤lay.val) : ¬LW index n (creditAddr lay) := by
  have ha : 0x66040≤creditAddr lay ∧ creditAddr lay<0x66060 := by unfold creditAddr;have:=lay.isLt;omega
  intro h
  rcases h with h|h|⟨lay',hl,h|h|h⟩
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · unfold BC.RlScratch Expand.RlScratch at h;simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · have:=ltable lay';omega
  · have:=rlWit_range h;have:=ltable lay';omega
  · unfold CreditW creditAddr at h;unfold creditAddr at ha;omega
#print axioms stage_half
#print axioms old_wit_preserved
#print axioms old_credit_preserved
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount)
open SigGolfCandidate.T3M.Search (ENC)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost CsW csRegs csCost)
open SigGolfCandidate.T3M.Search.CanonicalExpandHooks (creditAddr CreditW hintFloor creditAddr_lt)
open ClaudeWCT
open SigGolfCandidate.T3M.Expand.BC
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] {sk : BitVec 256}
variable (hSearch : ∀ (A : CsArgs) (s0 : MachineState),CsPre 354 A s0 →
  TBSim im sk s0 (csCost A.lay)
    (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
    (CsPost im 354 A s0))
include hSearch in
theorem run_good {sig : WCT9.Signature} {hints : BitVec 16} {index : Nat} :
    ∀n value vin s,LInv sig hints index n value s →
      TBSim im sk s (cost n) (run sig hints index n value vin) (Post im s sig hints index n vin)
  | 0,value,vin,s,hI => by
    obtain ⟨root,rfl⟩:=hI.terminal rfl
    exact TBSim.pure ⟨hI.pc,hI.x5,hI.enc,rfl,rfl,
      (fun lay h=>False.elim (by omega)),(fun lay h=>False.elim (by omega)),
      (fun _ _ _ _ _=>rfl),RegsExcept.refl _ _,Frame.refl _ _,
      (fun _=>⟨rfl,rfl⟩),(fun h=>False.elim (h rfl)),hI.hintsMem,(fun lay h=>False.elim (by omega))⟩
  | n+1,value,vin,s,hI => by
    have hn : n<4 := by have:=hI.hn;omega
    set lay : Layer:=Fin.ofNat 4 n with hlay
    have hlv : lay.val=n := fin_ofNat_val n hn
    have ht:=ltable lay
    unfold run
    refine (TBSim.bind (W₂:=cost n) (stage_good hSearch hn hI) (fun r t hstage=>?_)).mono (by rfl) (fun _ _ h=>h)
    rcases r with _|⟨c,ds,msg,v⟩
    · exact (TBSim.pure (Q:=Post im s sig hints index (n+1) vin) (a:=none) hstage).mono (Nat.zero_le _) (fun _ _ h=>h)
    · have hs:=hstage
      simp only [StagePost,←hlay] at hstage
      obtain ⟨hIt,cv,pv,ff,rr,credit,len,dec,blk,ctr,floor⟩:=hstage
      refine (TBSim.bind (W₂:=0) (run_good n msg v t hIt) (fun r' u hpost=>?_)).mono (by omega) (fun _ _ h=>h)
      cases r' with
      | none => exact TBSim.pure hpost
      | some out =>
        obtain ⟨pc,x5,enc,clen,dlen,outs,credits,half,regs,frame,base,top,hintsEq,floors⟩:=hpost
        have hD : lD lay=0x3ce8 ∨ lD lay=0x4968 ∨ lD lay=0x55a8 ∨ lD lay=0x820 ∨ lD lay=0x810 ∨ lD lay=0x818 := by
          clear_value lay;fin_cases lay <;> simp [lD]
        have hk:=ht.2.2.2.2.2.2.2.2.2.2
        refine TBSim.pure ⟨pc,x5,enc,by simpa using clen,
          by simpa using dlen,?_,?_,?_,(rr.trans regs).mono (by decide),?_,
          (fun h=>False.elim (by omega)),?_,hintsEq,?_⟩
        · intro lay' hl
          by_cases hlt : lay'.val<n
          · rw [List.getD_append _ _ _ _ (by omega)]
            exact outs lay' hlt
          · have he : lay'=lay := Fin.ext (by omega)
            subst lay'
            rw [List.getD_append_right _ _ _ _ (by omega),show lay.val-out.counters.length=0 by omega]
            simp only [List.getD_cons_zero]
            refine ⟨?_,?_,?_⟩
            · unfold BC.HalfAt
              rw [half (lD lay) (lk lay) hD hk (fun other hother ⟨hd,hk'⟩=>by
                have he:=lhalf_inj _ _ hd hk';rw [he] at hother;omega),ctr,replaceWord32_get _ _ hk]
              exact BitVec.eq_of_toNat_eq (by simp)
            · intro i hi
              exact (cv i hi).frame frame (by omega)
                (old_wit_preserved (by omega) (Or.inl ⟨i,hi,Or.inl rfl⟩))
                (old_wit_preserved (by omega) (Or.inl ⟨i,hi,Or.inr (by omega)⟩))
            · intro j hj
              have hside:=sideOff_le (route index lay).1 j
              exact (pv j hj).frame frame (by omega)
                (old_wit_preserved (by omega) (Or.inr ⟨j,hj,Or.inl rfl⟩))
                (old_wit_preserved (by omega) (Or.inr ⟨j,hj,Or.inr rfl⟩))
        · intro lay' hl
          by_cases hlt : lay'.val<n
          · rw [List.getD_append _ _ _ _ (by omega)]
            exact credits lay' hlt
          · have he : lay'=lay := Fin.ext (by omega)
            subst lay'
            rw [List.getD_append_right _ _ _ _ (by omega),show lay.val-out.digits.length=0 by omega]
            simp only [List.getD_cons_zero]
            rw [frame.get (creditAddr_lt lay) (old_credit_preserved (by omega))]
            exact credit
        · intro D k hD' hk' hnot
          rw [half D k hD' hk' (fun other ho=>hnot other (by omega))]
          exact stage_half hs D k hD' hk' (hnot lay (by omega))
        · refine (ff.trans frame).mono (fun A hA h=>?_)
          rcases h with h|h
          · rcases h with h|h|h|h
            · rcases scoped_write.mp h with h|h
              · exact Or.inl h
              · exact Or.inr (Or.inr ⟨lay,by omega,Or.inr (Or.inr h)⟩)
            · exact Or.inr (Or.inr ⟨lay,by omega,Or.inl h⟩)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨lay,by omega,Or.inr (Or.inl h)⟩)
          · rcases h with h|h|⟨other,ho,h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨other,by omega,h⟩)
        · intro _
          by_cases hn0 : n=0
          · obtain ⟨rfl,hfold⟩:=base hn0
            have hl0 : lay=0 := Fin.ext (by omega)
            rw [hfold]
            simpa only [hl0] using blk hl0
          · exact top hn0
        · intro lay' hl
          by_cases hlt : lay'.val<n
          · rw [List.getD_append _ _ _ _ (by omega)]
            exact floors lay' hlt
          · have he : lay'=lay := Fin.ext (by omega)
            subst lay'
            rw [List.getD_append_right _ _ _ _ (by omega),show lay.val-out.digits.length=0 by omega]
            simp only [List.getD_cons_zero]
            exact floor
#print axioms run_good
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open OracleComp SigGolfCandidate.T3 ClaudeWCT
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem run_eq_recover (sig : SharedForest.Signature) (index : Nat) :
    ∀n,n<4 → ∀msg vin,
      run (SharedForest.mainSignature sig) sig.policyHints index (n+1) msg vin=
        SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) (n+1) msg := by
  intro n
  induction n with
  | zero =>
    intro hn msg vin
    conv_lhs => unfold run;unfold stage
    conv_rhs => unfold SharedForest.recoverHintedLayers
    simp only [bind_assoc]
    congr 1
    funext r
    rcases r with _|⟨c,ds⟩
    · rfl
    · simp only [BC.recoverMsg,Fin.ofNat_zero,ite_true,Nat.zero_eq,bind_assoc,pure_bind,run,List.nil_append]
  | succ n ih =>
    intro hn msg vin
    have hl : (Fin.ofNat 4 (n+1) : Layer)≠0 := by
      intro he
      have hv:=congrArg Fin.val he
      change (n+1)%4=0 at hv
      rw [Nat.mod_eq_of_lt hn] at hv
      omega
    conv_lhs => unfold run;unfold stage
    conv_rhs => unfold SharedForest.recoverHintedLayers
    simp only [bind_assoc]
    congr 1
    funext r
    rcases r with _|⟨c,ds⟩
    · rfl
    · simp only [BC.recoverMsg,if_neg hl,Nat.succ_ne_zero,ite_false,bind_assoc,pure_bind]
      congr 1
      funext pair
      rw [ih (by omega)]
      rfl

theorem cost_four : cost 4≤3618000000 := by decide +kernel
#print axioms run_eq_recover
#print axioms cost_four
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def policyCondition (hints : BitVec 16) (digits : List (List Nat)) : Prop :=
  let r1:=63-CanonicalPolicy.credit 0 (digits.getD 0 [])
  let r2:=r1-CanonicalPolicy.credit 1 (digits.getD 1 [])
  let r3:=r2-CanonicalPolicy.credit 2 (digits.getD 2 [])
  r1<48 ∧ r2<35 ∧ r3<18 ∧
    hints.toNat%18=CanonicalPolicy.threshold 1 r1 ∧
    hints.toNat/18%18=CanonicalPolicy.threshold 2 r2 ∧ hints.toNat/324=r3

theorem policyCondition_iff (hints : BitVec 16) (digits : List (List Nat))
    (hh : hints.toNat<5832) (hlen : digits.length=4)
    (hc0 : 16≤CanonicalPolicy.credit 0 (digits.getD 0 []))
    (hc1 : SharedForest.hintFloor hints 1≤CanonicalPolicy.credit 1 (digits.getD 1 []))
    (hc2 : SharedForest.hintFloor hints 2≤CanonicalPolicy.credit 2 (digits.getD 2 [])) :
    policyCondition hints digits ↔ SharedForest.policyHintsValid hints digits=true := by
  have hr1 : 63-CanonicalPolicy.credit 0 (digits.getD 0 [])<48 := by omega
  have h1 : SharedForest.hintFloor hints 1=hints.toNat%18 := by simp [SharedForest.hintFloor]
  have h2 : SharedForest.hintFloor hints 2=hints.toNat/18%18 := by simp [SharedForest.hintFloor]
  have h3 : SharedForest.hintFloor hints 3=hints.toNat/324 := by
    simp only [SharedForest.hintFloor,show (3:Layer)≠0 by decide,ite_false]
    norm_num
    omega
  rw [h1] at hc1
  rw [h2] at hc2
  simp only [SharedForest.policyHintsValid,decide_eq_true_eq,CanonicalPolicy.nextResidual,
    CanonicalPolicy.totalCredit,hh,hlen,true_and,h1,h2,h3]
  unfold policyCondition
  constructor
  · rintro ⟨hR1,hR2,hR3,he1,he2,he3⟩
    refine ⟨he1,he2,?_⟩
    rw [CanonicalPolicy.lower_three_progress _ hR3]
    exact he3
  · rintro ⟨he1,he2,he3⟩
    have ht1 := (CanonicalPolicy.lower_one_progress ⟨63-CanonicalPolicy.credit 0 (digits.getD 0 []),by omega⟩).2
    have hr2 : 63-CanonicalPolicy.credit 0 (digits.getD 0 [])-CanonicalPolicy.credit 1 (digits.getD 1 [])<35 := by
      simp only [Fin.val_mk] at ht1
      rw [←he1] at ht1
      omega
    have ht2 := (CanonicalPolicy.lower_two_progress ⟨_,hr2⟩).2
    have hr3 : 63-CanonicalPolicy.credit 0 (digits.getD 0 [])-CanonicalPolicy.credit 1 (digits.getD 1 [])-CanonicalPolicy.credit 2 (digits.getD 2 [])<18 := by
      simp only [Fin.val_mk] at ht2
      rw [←he2] at ht2
      omega
    refine ⟨hr1,hr2,hr3,he1,he2,?_⟩
    rw [CanonicalPolicy.lower_three_progress _ hr3] at he3
    exact he3
#print axioms policyCondition_iff
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost csCost)
open SigGolfCandidate.Research
open ClaudeWCT
variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] {sk : BitVec 256}
variable (hSearch : ∀ (A : CsArgs) (s0 : MachineState),CsPre 354 A s0 →
  TBSim im sk s0 (csCost A.lay)
    (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
    (CsPost im 354 A s0))
include hSearch in
theorem recover_good {sig : SharedForest.Signature} {index : Nat} {msg : WCT9.LayerMsg} {vin : Digest} {s : MachineState}
    (hI : LInv (SharedForest.mainSignature sig) sig.policyHints index 4 msg s) :
    TBSim im sk s 3618000000
      (SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) 4 msg)
      (Post im s (SharedForest.mainSignature sig) sig.policyHints index 4 vin) := by
  rw [←run_eq_recover sig index 3 (by decide) msg vin]
  exact (run_good hSearch 4 msg vin s hI).mono cost_four (fun _ _ h=>h)
#print axioms recover_good
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false

def Tables (s : MachineState) : Prop :=
  ∀i,i<2160 → s.getByte (BitVec.ofNat 64 (16747408+i))=Images.expandSharedData.getD i 0

theorem data1 (r : Fin 48) : Images.expandSharedData.getD (2048+r.val) 0=
    BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r.val) := by
  fin_cases r <;> decide +kernel
theorem data2 (r : Fin 35) : Images.expandSharedData.getD (2112+r.val) 0=
    BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r.val) := by
  fin_cases r <;> decide +kernel
theorem threshold1_lt (r : Nat) (hr : r<48) : CanonicalPolicy.threshold 1 r<18 := by
  have h : ∀r:Fin 48,CanonicalPolicy.threshold 1 r.val<18 := by decide +kernel
  exact h ⟨r,hr⟩
theorem threshold2_lt (r : Nat) (hr : r<35) : CanonicalPolicy.threshold 2 r<18 := by
  have h : ∀r:Fin 35,CanonicalPolicy.threshold 2 r.val<18 := by decide +kernel
  exact h ⟨r,hr⟩
theorem Tables.first {s : MachineState} (h : Tables s) (r : Nat) (hr : r<48) :
    s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r) := by
  have he:=h (2048+r) (by omega)
  rw [data1 ⟨r,hr⟩] at he
  rw [show 16747408+(2048+r)=16749456+r by omega] at he
  exact he
theorem Tables.second {s : MachineState} (h : Tables s) (r : Nat) (hr : r<35) :
    s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r) := by
  have he:=h (2112+r) (by omega)
  rw [data2 ⟨r,hr⟩] at he
  rw [show 16747408+(2112+r)=16749520+r by omega] at he
  exact he
#print axioms data1
#print axioms data2
#print axioms Tables.first
#print axioms Tables.second
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.Research ClaudeWCT
/-- Exact installed recovery entry, including all four dynamic canonical searches. -/
theorem installed_recover_good {sk : BitVec 256} {sig : SharedForest.Signature} {index : Nat}
    {msg : WCT9.LayerMsg} {vin : Digest} {s : MachineState}
    (hI : LInv (SharedForest.mainSignature sig) sig.policyHints index 4 msg s) :
    TBSim Images.expandImage sk s 3618000000
      (SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) 4 msg)
      (Post Images.expandImage s (SharedForest.mainSignature sig) sig.policyHints index 4 vin) := by
  letI := SharedRecover.installed_entry
  letI := SharedRecover.installed_code
  letI := SharedRecover.installed_bc
  letI := SharedRecover.installed_packed
  exact recover_good (fun _ _ hp => Search.CanonicalExpand.counterSearch_good
    ClaudeWCT.W9.Machine.Expand.SharedSearchCode.installed_searchKernel hp) hI
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_compact_chunks (c : Nat) (hc : compactChunkAllowed c) :
    CodeAt Images.expandImage (pcOf (256*c+compactChunkLo c))
      (((expChunks.getD (c-4) []).take (compactChunkLen c)).drop (compactChunkLo c)) := by
  rcases hc with rfl|rfl|rfl|hc|rfl|rfl|rfl|rfl
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · obtain ⟨hlo,hhi⟩ := hc
    interval_cases c <;> apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_compact : CompactCodeAt Images.expandImage := compactCode_of_chunks installed_compact_chunks
#print axioms installed_compact
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.SharedDigestCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign.SharedDigest
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
theorem of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) :
    CodeAt im (pcOf (base true)) (words true) := by
  exact SharedCounterHooks.code_slice (off:=0) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : CodeAt Images.expandImage (pcOf (base true)) (words true) := of_driver codeAt_expand_shared_driver
theorem installed_look : LookOK Images.expandImage (look true) := look_of_code true installed_code
end ClaudeWCT.W9.Machine.Expand.SharedDigestCode

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem initial_of_original (w : W9Machine.WBytes) (index : Nat)
    (raw : Fin 9→Fin 128) (ranks : Fin 9→Fin 563) (s : MachineState)
    (hp:s.pc=pcOf 46513) (hf:Fields index raw ranks s)
    (hw:∀A,1216≤A→A+8≤9472→A%8=0→A≠1240→W9Machine.OrigW w s A) :
    Inv w index raw ranks s 0 (SharedV3.initialPair w) s := by
  refine ⟨by decide,hp,hf,?_,?_,?_,Frame.refl _ _⟩
  · exact W9Machine.DigAt_origW (hw 9280 (by decide) (by decide) (by decide) (by decide))
      (hw 9288 (by decide) (by decide) (by decide) (by decide)) (by decide)
  · exact W9Machine.DigAt_origW (hw 8720 (by decide) (by decide) (by decide) (by decide))
      (hw 8728 (by decide) (by decide) (by decide) (by decide)) (by decide)
  · intro m hm hm9 off ho ha h9 hhand
    rcases (show m=9 ∨ m<9 by omega) with he|he
    · have hh:=h9 he
      subst he
      apply hw <;> unfold regionAddr <;> omega
    · apply hw <;> unfold regionAddr <;> omega
#print axioms initial_of_original
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem raw_output (u : MachineState) (a : HashOutput) (ha : OutAt u NBUF a) (k : Fin 9) :
    rawRead k.val u=BitVec.ofNat 64 (SharedForest.rawChildFromOutput a k).val := by
  have hm:=ha (rawWord k.val) (by fin_cases k <;> decide)
  unfold rawRead
  rw[hm]
  convert W9Drv.SharedDispatch.child_field a k using 1 <;> fin_cases k <;> rfl

theorem rank_output (u : MachineState) (a : HashOutput) (ha : OutAt u NBUF a) (k : Fin 9)
    (hr : SharedForest.rawForestRank a k.val<563) :
    rankRead k.val u=BitVec.ofNat 64 (SharedForest.forestRank a k.val).val := by
  have hm:=ha (rankWord k.val) (by fin_cases k <;> decide)
  unfold rankRead
  rw[hm]
  have hv:(SharedForest.forestRank a k.val).val=SharedForest.rawForestRank a k.val:=
    Nat.mod_eq_of_lt hr
  rw[hv]
  convert W9Drv.SharedDispatch.rank_field a k using 1 <;> fin_cases k <;> rfl
#print axioms raw_output
#print axioms rank_output
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Sign

theorem fields_of_output (u : MachineState) (a : HashOutput) (index : Nat)
    (hi : u.getMem 0x66010=BitVec.ofNat 64 index) (ha : OutAt u NBUF a)
    (hr : ∀k:Fin 9,SharedForest.rawForestRank a k.val<563) :
    Fields index (SharedForest.rawChildFromOutput a) (fun k=>SharedForest.forestRank a k.val) u :=
  ⟨hi,SharedDispatch.raw_output u a ha,fun k=>SharedDispatch.rank_output u a ha k (hr k)⟩
#print axioms fields_of_output
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem installed_forest_good (sk : BitVec 256) (output : HashOutput)
    (witness : SigGolfCandidate.Research.SharedForest.Witness) (index : Nat) (hi : index<2^31)
    (s : MachineState)
    (h0 : Inv (Paired.witEnc output witness) index (rawChildFromOutput output)
      (fun k=>forestRank output k.val) s 0 (SharedV3.initialPair (Paired.witEnc output witness)) s) :
    TBSim Images.expandImage sk s 2016
      (recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest)
      (fun pair t=>t.pc=pcOf 46862 ∧ DigAt t 1216 pair.1 ∧ DigAt t 1264 pair.2 ∧
        Frame s t writes ∧ Fields index (rawChildFromOutput output) (fun k=>forestRank output k.val) t) := by
  have hwin : (Frozen.image.code.drop 195584).take 59072=(Images.expandImage.code.drop 195584).take 59072 := by
    rw [W9Machine.Frozen.image_eq]
    exact Images.expand_banks_eq_verify.symm
  have hm:=forest_tbsim_of_bank Images.expandImage sk hwin
    SharedDispatch.installed_code W9Drv.slot_entry
    (fun L hw hc rank w index k j u hu=>N600.tbsim_sharedBank L sk hw hc rank w index k j u hu)
    (Paired.witEnc output witness) index hi (rawChildFromOutput output)
    (fun k=>forestRank output k.val) s h0
  rw[show N600.embed=ClaudeWCT.WCT9.embed from N600.embed_eq_c1] at hm
  rw[W9Drv.SharedCanonical.forest_witEnc output witness index hi] at hm
  exact hm
#print axioms installed_forest_good
end ClaudeWCT.W9.Machine.Expand.SharedForestRun
