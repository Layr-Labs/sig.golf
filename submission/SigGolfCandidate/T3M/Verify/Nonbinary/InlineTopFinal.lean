import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTopMerkle

/- The actual unchanged final comparison is reflected through prefixLook,
   and the new Merkle post is converted by its concrete fields. This closes
   the whole top stage with both genuine HALT outcomes, not a callback. The
   comparison field arguments follow the attributed W9Drv.Fts.cmp_good. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def cmpPc (c : Nat) : Nat := 7202 + 128 * c
def cmpDst (c : Nat) : Nat := 11336 + 48 * (c / 32 % 2)
def cmpK (c : Nat) : List (Reg × Word) := baseK ++ [(.x12, BitVec.ofNat 64 (cmpDst c))]
def cmpBr1 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c)), .ld (kw 160), d⟩
def cmpBr2 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c + 8)), .ld (kw 168), d⟩
def cmpDelta (c : Nat) : E := .bin .sub (.ld (kw (cmpDst c + 8))) (.ld (kw 168))
def cmpAcc (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, cmpDelta c)], [], cmpPc c + 7, true, 7, [cmpBr1 c false], none, 7⟩
def cmpRej1 (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], cmpPc c + 11, true, 5, [cmpBr1 c true], none, 5⟩

theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t
theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
def compareCheck (c : Nat) : Bool :=
  specB [] [] [] (prefixRunAt (cmpK c) [] (cmpPc c) [.br false]) (cmpAcc c) [] [] [] &&
  specB [] [] [] (prefixRunAt (cmpK c) [] (cmpPc c) [.br true]) (cmpRej1 c) [] [] []
set_option maxRecDepth 100000
theorem compareCheck_all : (List.range 64).all compareCheck = true := by decide +kernel
theorem compareCheck_at (c : Nat) (hc : c < 64) : compareCheck c = true :=
  List.all_eq_true.mp compareCheck_all c (List.mem_range.mpr hc)
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    Judg.GoodQ image t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := compareCheck_at c hc
  simp only [compareCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := prefix_spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := Judg.GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact Judg.GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := prefix_spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact Judg.GoodQ.steps' hu.steps (Judg.GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)

theorem top_end_compare (w : WBytes) (pk : Digest) (index : Nat)
    (ends : List Digest) (root : Digest) (t : MachineState)
    (h : TopMerkleEnd w pk index ends root t) : CmpIn pk root t := by
  obtain ⟨u,hu,ht⟩ := h
  change Merkle.MkEnd w pk 0 (route index 0).1 u root t at ht
  have hpc : t.pc=pcOf (7202+128*Merkle.mkSh 0 1 (route index 0).1) := by
    rw [ht.pc]
    congr 1
    simp [Merkle.mkFin,show Merkle.mkNch 0-1=1 from rfl,
      show Merkle.mkBits 0 1=6 from rfl,show Merkle.mkOff 0 1 6=33 from rfl,
      Merkle.BC.mkShp,Merkle.mkShp]
    omega
  refine ⟨⟨Merkle.mkSh 0 1 (route index 0).1, Merkle.mkSh_lt _ _ _, ?_, ?_, ?_⟩,ht.glob.2.2.1⟩
  · rw [hpc]; rfl
  · intro p hp
    simp only [cmpK,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg]
      congr 1
      exact (Merkle.mkDst_chunk _).symm
  · change DigAt t (11336+48*(Merkle.mkSh 0 1 (route index 0).1/32%2)) root
    rw [Merkle.mkDst_chunk]
    exact ht.root

def topBoolSource (c : NCtx) (index : Nat) (pk : Digest) : SigGolfCandidate.T3.M Bool := do
  let root ← topSource c index
  pure (root==pk)

theorem top_bool_good (c : NCtx) (pk : Digest) (index : Nat) (hc : c.ok)
    (hidx : index < 2^31) (hroute : (c.leaf,c.tree)=route index 0) (hS3 : c.S3=s3v)
    (s0 : MachineState) (v : Digest) (hk : KnownOK c.known s0)
    (hg : Glob baseK c.w pk s0) (hkeep : KnownOK (lfKeepK 0) s0)
    (h23 : s0.getReg .x23=BitVec.ofNat 64 (4096+c.leaf))
    (ho : Orig c.w (fun o => 9288 ≤ o ∧ o < layerBase 0+64*SigGolfCandidate.T3.height 0) s0)
    (h0 : c.Orig0 s0) (he : NCtx.Encoded v s0) (hf : c.Fit v)
    (hv : v.toNat<2^125) (hranks : topRanksValid v=true)
    (Q : Prop) (hQ : Q) (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Judg.GoodQ image s (9+2231+12+Merkle.mkFuel 0)
      (8+all54Cost c+12+Merkle.mkCyc 0) Q (8+all54Cost c+12+Merkle.mkCyc 0)
      (Judg.ccM (topBoolSource c index pk) Judg.Kb) := by
  have h := top_good c pk index hc hidx hroute hS3 s0 v hk hg hkeep h23 ho h0 he hf hv hranks
    (fun root => pure (root==pk,0)) 9 8 8 Q
    (fun ends root t ht => cmp_good pk root t (top_end_compare c.w pk index ends root t ht) Q hQ) s hs
  simpa [topBoolSource,Judg.ccM_bind,Judg.ccM_map,Judg.ccM_pure,Judg.Kb] using h

#print axioms compareCheck_all
#print axioms top_end_compare
#print axioms top_bool_good
end SigGolfCandidate.T3M.Nonbinary.InlineTail
