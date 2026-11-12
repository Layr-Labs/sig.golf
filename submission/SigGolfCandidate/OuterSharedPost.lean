import SigGolfCandidate.OuterCopyChildFlatB
import SigGolfCandidate.OuterCopyChildFlatC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSharedPost
open RiscvZkvm.Rv64 SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open W9Machine

def record (coord : Nat) : Nat := 8323072+(coord-1)*4096
def Extra (coord X : Nat) : Prop := X=1152 ∨ X=1160 ∨ X=record coord

def Writes (L : W9Machine.Layout) (k : Fin 9) (raw : Fin 128) (X : Nat) : Prop :=
  (SharedChild.writes L k raw X ∨ SharedChild.recW (Chain.base L k) X ∨ SharedChild.scratchW X ∨ SharedChild.recW16 (Chain.base L k) X) ∨ Extra k.val X

structure Post (L : W9Machine.Layout) (k : Fin 9) (raw : Fin 128) (u : MachineState) (res : Digest×Nat×Nat×Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (L.returnWord k+(if k.val=8 then 79 else if k.val%2=1 then 76 else 75))
  hashLen : t.getReg .x11=64
  top : DigAt t (SharedChild.handAddr L k raw) res.1
  a2 : t.getReg .x12=BitVec.ofNat 64 (SharedChild.outputAddr L k raw)
  keep : ∀ r,r∉Child.clobbers → t.getReg r=u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slotA (Chain.base L k)))=
    BitVec.ofNat 64 (Chain.base L k+SharedV3.blkOff (SharedV3.physical k.val raw.val) 3+SigGolfCandidate.FtsGrind.WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slotA (Chain.base L k)+8))=BitVec.ofNat 64 res.2.1
  nle : res.2.1≤SigGolfCandidate.FtsGrind.FUEL (SigGolfCandidate.FtsGrind.ftsWidth k.val)
  rec0 : k.val<4 → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (Chain.base L k)))=
    BitVec.ofNat 64 (Chain.base L k+SharedV3.blkOff (SharedV3.physical k.val raw.val) 2+SigGolfCandidate.FtsGrind.WADJ)
  rec1 : k.val<4 → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (Chain.base L k)+8))=BitVec.ofNat 64 res.2.2.1
  nle16 : res.2.2.1≤255
  n0 : 4≤k.val → res.2.2.1=0
  outer : SharedV3.first k.val=false → t.getMem (BitVec.ofNat 64 (record k.val))=BitVec.ofNat 64 res.2.2.2
  outer0 : SharedV3.first k.val=true → res.2.2.2=0
  saves : ∀ i,i<5 → t.getMem (BitVec.ofNat 64 (1104+8*i))=0
  scr : ∀ i,i<4 → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.SCR+8*i))=0
  scr16 : k.val<4 → ∀ i,i<4 → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.SCR16+8*i))=0
  frame : Frame u t (Writes L k raw)

theorem of_first {L : W9Machine.Layout} {k : Fin 9} {raw : Fin 128} {u t : MachineState} {res : Digest×Nat×Nat}
    (hf : SharedV3.first k.val=true) (h : SharedChild.PostC L k raw u res t) :
    Post L k raw u (res.1,res.2.1,res.2.2,0) t := by
  refine ⟨h.pc,h.hashLen,h.top,h.a2,h.keep,h.slot0,h.slot1,h.nle,h.rec0,h.rec1,h.nle16,h.n0,?_,fun _=>rfl,h.saves,h.scr,h.scr16,?_⟩
  · intro he
    rw [hf] at he
    cases he
  · exact h.frame.mono (fun _ _ h=>Or.inl h)

#print axioms of_first
end OuterSharedPost
