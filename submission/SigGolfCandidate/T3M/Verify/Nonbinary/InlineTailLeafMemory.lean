import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailLeafPacket
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

/- Concrete retained leaf setup, with endpoint/header/padding readback and frame.
   Memory-law arguments follow the attributed T3M.leafT_step proof. All Steps
   here come from the actual new image, not from its old selected counterpart. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def leafTarget : E := .bin .and
  (.bin .sll (addC (.bin .and (.reg .x23) (.c 63)) 1520) (.c 8)) (.c (~~~1#64))

def leafModel : Result :=
  ⟨⟨RegFile.init.set .x3 (addC (.reg .x27) (-512)) |>.set .x4 (addC (.reg .x27) (-256))
       |>.set .x10 (.c 512) |>.set .x11 (.c 896)
       |>.set .x14 (.bin .sll (addC (.bin .and (.reg .x23) (.c 63)) 1520) (.c 8)),
    [(⟨none,1400⟩,.c 0),(⟨none,1392⟩,.c 0),(⟨none,536⟩,.reg .x4),
      (⟨none,528⟩,addC (.reg .x27) (-512))],[]⟩,leafTarget,.jump,12,12⟩

theorem leaf_model_check : rOK (some leafResult) leafModel=true := by decide +kernel

theorem leaf_model : leafResult=leafModel := Option.some.inj (rOK_eq leaf_model_check)

def LeafWrites (A : Nat) : Prop := A=528 ∨ A=536 ∨ A=1392 ∨ A=1400

theorem leaf_obligations (s : MachineState) : leafResult.obligs s := by
  rw [leaf_model]
  trivial

theorem leaf_mem_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]
      intro he
      have hn:=congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hA,Nat.mod_eq_of_lt hk] at hn
      exact h hn
    rw [if_neg hne, if_neg h]

theorem leaf_memory (s : MachineState) (h27 : s.getReg .x27=1025#64) :
    ∀ A, A<2^64 → (leafResult.toState s).getMem (BitVec.ofNat 64 A)=
      if A=1400 then 0 else if A=1392 then 0 else if A=536 then s.getReg .x4
      else if A=528 then 513#64 else s.getMem (BitVec.ofNat 64 A) := by
  intro A hA
  rw [leaf_model,Result.toState_getMem]
  simp only [leafModel]
  have hEq (k : Nat) (hk : k<2^64) :
      (BitVec.ofNat 64 A=BitVec.ofNat 64 k) ↔ A=k := by
    constructor
    · intro he
      have hn:=congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hA,Nat.mod_eq_of_lt hk] using hn
    · intro he;rw [he]
  change memEval s
      [(⟨none,BitVec.ofNat 64 1400⟩,.c 0),(⟨none,BitVec.ofNat 64 1392⟩,.c 0),
       (⟨none,BitVec.ofNat 64 536⟩,.reg .x4),
       (⟨none,BitVec.ofNat 64 528⟩,addC (.reg .x27) (-512))]
      (BitVec.ofNat 64 A)=_
  simp only [memEval_cons,Addr.eval,E.eval,addC_eval,h27,memEval_nil,
    hEq 1400 (by norm_num),hEq 1392 (by norm_num),hEq 536 (by norm_num),hEq 528 (by norm_num)]
  rfl

theorem leaf_frame (s : MachineState) (h27 : s.getReg .x27=1025#64) :
    Frame s (leafResult.toState s) LeafWrites := by
  intro A hA hn
  rw [leaf_memory s h27 A hA]
  simp only [LeafWrites,not_or] at hn
  simp only [if_neg hn.2.2.2,if_neg hn.2.2.1,if_neg hn.2.1,if_neg hn.1]

theorem leaf_keeps (s : MachineState) (r : Reg)
    (hr : r ∉ ([.x3,.x4,.x10,.x11,.x14] : List Reg)) :
    (leafResult.toState s).getReg r=s.getReg r := by
  rw [leaf_model,Result.toState_getReg]
  have h : leafModel.st.regs.get r=RegFile.init.get r := by
    cases r <;> first | rfl | exact False.elim (hr (by simp))
  rw [h,RegFile.init_get_eval]

structure LeafPrepared (c : NCtx) (s0 : MachineState) (ends : List Digest) (t : MachineState) : Prop where
  length : ends.length=54
  ends : ∀ j<54,DigAt t (slot j) (ends.getD j 0)
  frame : Frame s0 t (c.Wr 54)
  x5 : t.getReg .x5=0
  x10 : t.getReg .x10=512#64
  x11 : t.getReg .x11=896#64
  header0 : t.getMem 528=513#64
  header1 : t.getMem 536=BitVec.ofNat 64 c.w1
  zero0 : t.getMem 1392=0
  zero1 : t.getMem 1400=0
  pc : t.pc=leafTarget.eval s0

structure LeafRegMem (s t : MachineState) : Prop where
  memory : s.getReg .x27=1025#64 → ∀ A,A<2^64 → t.getMem (BitVec.ofNat 64 A)=
    if A=1400 then 0 else if A=1392 then 0 else if A=536 then s.getReg .x4
    else if A=528 then 513#64 else s.getMem (BitVec.ofNat 64 A)
  frame : s.getReg .x27=1025#64 → Frame s t LeafWrites
  keeps : ∀ r,r ∉ ([.x3,.x4,.x10,.x11,.x14] : List Reg) → t.getReg r=s.getReg r
  x10 : t.getReg .x10=512#64
  x11 : t.getReg .x11=896#64
  pc : t.pc=leafTarget.eval s

theorem leaf_reg_mem (s : MachineState) : LeafRegMem s (leafResult.toState s) := by
  refine ⟨leaf_memory s,leaf_frame s,leaf_keeps s,?_,?_,?_⟩
  · rw [leaf_model,Result.toState_getReg];rfl
  · rw [leaf_model,Result.toState_getReg];rfl
  · rw [leaf_model,Result.toState_pc];rfl

theorem leaf_prepared_of_post (c : NCtx) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (rank : Nat) (hr : rank<64)
    (ends : List Digest) (s t : MachineState) (hp : LeafRegMem s t) (hs : c.Base s0 (c.Wr 54) ends s ∧ ends.length=54 ∧ s.pc=pcOf (leafPC rank)) :
    LeafPrepared c s0 ends t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩:=hs
  have h27 : s.getReg .x27=1025#64 :=
    (hR .x27 (by decide)).trans (hk (.x27,1025#64) (by simp [NCtx.known]))
  have h4 : s.getReg .x4=BitVec.ofNat 64 c.w1 :=
    (hR .x4 (by decide)).trans (hk (.x4,BitVec.ofNat 64 c.w1) (by simp [NCtx.known]))
  have fr:=hp.frame h27
  refine ⟨hlen,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    have hj' : j<ends.length := by omega
    have hslot : slot j=512 ∨ (544 ≤ slot j ∧ slot j≤1376) := by unfold slot;split <;> omega
    exact (hS j hj').frame fr (by omega) (by unfold LeafWrites;omega) (by unfold LeafWrites;omega)
  · exact (hF.trans fr).mono (by
      intro A _ h
      rcases h with h|h
      · exact h
      · left;unfold LeafWrites at h;omega)
  · rw [hp.keeps .x5 (by decide),hR .x5 (by decide)]
    exact hk (.x5,0) (by simp [NCtx.known])
  · exact hp.x10
  · exact hp.x11
  · simpa using hp.memory h27 528 (by norm_num)
  · simpa [h4] using hp.memory h27 536 (by norm_num)
  · simpa using hp.memory h27 1392 (by norm_num)
  · simpa using hp.memory h27 1400 (by norm_num)
  · rw [hp.pc]
    change leafTarget.eval s=leafTarget.eval s0
    simp only [leafTarget,E.eval,addC_eval]
    rw [hR .x23 (by decide)]

theorem leaf_prepared_state (c : NCtx) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (rank : Nat) (hr : rank<64)
    (ends : List Digest) (s : MachineState)
    (hs : c.Base s0 (c.Wr 54) ends s ∧ ends.length=54 ∧ s.pc=pcOf (leafPC rank)) :
    LeafPrepared c s0 ends (leafResult.toState s) :=
  leaf_prepared_of_post c s0 hk rank hr ends s (leafResult.toState s) (leaf_reg_mem s) hs

theorem leaf_prepared (c : NCtx) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (rank : Nat) (hr : rank<64)
    (ends : List Digest) (s : MachineState)
    (hs : c.Base s0 (c.Wr 54) ends s ∧ ends.length=54 ∧ s.pc=pcOf (leafPC rank)) :
    ∃ t,Steps image s 12 12 t ∧ LeafPrepared c s0 ends t :=
  ⟨leafResult.toState s,leaf_steps rank hr s hs.2.2 (leaf_obligations s),
    leaf_prepared_state c s0 hk rank hr ends s hs⟩

#print axioms leaf_model_check
#print axioms leaf_memory
#print axioms leaf_prepared
end SigGolfCandidate.T3M.Nonbinary.InlineTail
