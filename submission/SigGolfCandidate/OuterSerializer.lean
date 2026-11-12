import SigGolfCandidate.OuterSerializerPack
import SigGolfCandidate.OuterSignRebindNested
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
local macro "so" : tactic => `(tactic| ((try simp only [ClaudeWCT.W9.Machine.Sign.SIG, MEMORY_BYTES] at *) <;> omega))
structure Code (im : Image) : Prop where
  preHook : CodeAt im (pcOf 540) [hook540]
  preTail : CodeAt im (pcOf 20715) (tailCode.take 28)
  preH2 : CodeAt im (pcOf 20813) h2SignTail
  jump : CodeAt im (pcOf 20743) [0x3850106f]
  setup : CodeAt im (pcOf 22504) setupWords
  loop : CodeAt im (pcOf 22509) tailWords
  finish : CodeAt im (pcOf 22526) finishWords
  /-- N7g (C), Y5: the mod-R hint pack `N = rho * 360 + t` (25852.., the index code 26117.., 25861..). -/
  nx1 : CodeAt im (pcOf 25852) nxW1
  nt : CodeAt im (pcOf 26117) ntW
  nx3 : CodeAt im (pcOf 25861) nxW3
  post : CodeAt im (pcOf 24665) postWords
  /-- U16b: the success HALT `20744` is `jal 25385` (E8 P1 pack routine, ends `addi a0,zero,0; ecall`). -/
  packJal : CodeAt im (pcOf 20744) packJalW
  pack : CodeAt im (pcOf 25385) packWords
  /-- Y5: the heap-16..31 V slots and the final `ecall` (25930..25963). -/
  pack2 : CodeAt im (pcOf 25930) (packWords2.take 33)

theorem Code.pre_tail_look {im : Image} (h : Code im) : LookOK im preTailLook := by
  intro n w hw
  unfold preTailLook at hw
  split at hw
  · rename_i hn
    unfold ClaudeWCT.W9.Machine.Sign.tailLook at hw
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
        unfold ClaudeWCT.W9.Machine.Sign.tailLook at hh
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

theorem Code.tail_look {im : Image} (h : Code im) : LookOK im ClaudeWCT.W9.Machine.Sign.SharedSerializer.tailLook := by
  intro n w hw
  unfold ClaudeWCT.W9.Machine.Sign.SharedSerializer.tailLook at hw
  split at hw
  · rename_i hn
    have hh:=codeAt_get_word (by decide : 22509<2^30) h.loop hw
    simpa only [Nat.add_sub_cancel' hn] using hh
  · cases hw

theorem full_readout {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 540) (h : Nat)
    (hok : ClaudeWCT.W9.T3M.SharedCodec.HintOK h) (hm : s.getMem (BitVec.ofNat 64 417792)=BitVec.ofNat 64 h) :
    ∃n c,c≤8549 ∧ ∃t,Steps im s n c t ∧ t.pc=pcOf 25963 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      (∀k,k<650 → t.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*k))=packWord (postWord
        (nWord (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j))))) (nN (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) 0) (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) 1) h))
        (Xn (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j))) 657) ((nN (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) 0) (packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) 1) h) / 2 ^ 128))) k) := by
  obtain ⟨a,sa,ha⟩:=pre_good hc.pre_tail_look hc.pre_hook_look hc.pre_c_look s hp
  let b:=jumpRun.res.toState a
  have ab : Steps im a 1 1 b := symRun_sound jumpRun hc.jump a ha.1 (by simp [jumpRun.res,rv_simp])
  have bp : b.pc=pcOf 22504 := by simp [b,jumpRun.res,rv_simp]
  have bm (A : Word) : b.getMem A=a.getMem A := rfl
  obtain ⟨n,hn,u,bu,up,ux7,uw,uf⟩:=tail_readout hc.setup hc.tail_look hc.finish b bp
  have hu : u.getMem (BitVec.ofNat 64 417792)=BitVec.ofNat 64 h := by
    rw [uf.get (by decide) (by simp [ClaudeWCT.W9.Machine.Sign.SIG]),bm,ha.2.2.get (A:=417792) (by decide) (by simp [ClaudeWCT.W9.Machine.Sign.SIG])]; exact hm
  have huw : ∀k,k<650 → u.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*k))=
      packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) k := by
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
  have hux7 : u.getReg .x7=preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j))) 657 := by
    rw [ux7,bm,ha.read 657 (by omega)]
  have hu0 : u.getMem (BitVec.ofNat 64 ClaudeWCT.W9.Machine.Sign.SIG)=packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) 0 := huw 0 (by omega)
  have hu1 : u.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8))=packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (ClaudeWCT.W9.Machine.Sign.SIG+8*j)))) 1 := huw 1 (by omega)
  obtain ⟨nc,cc,c,uc,hcc,cp,cx6,c0,c1,cfr⟩:=nx_steps hc.nx1 hc.nt hc.nx3 u up h hok hu
  obtain ⟨v,cv,vp,vx5,vw⟩:=post_steps hc.post c cp
  obtain ⟨t,vt,tp,t10,tr,tw⟩:=OuterSerializerPack.pack_steps hc.packJal hc.pack hc.pack2 v vp
  refine ⟨preCost+1+n+nc+58+210,preCost+1+n+cc+58+210,by unfold preCost;omega,t,
    ((((sa.trans ab).trans bu).trans uc).trans cv).trans vt,tp,?_,t10,?_⟩
  · rw [tr.get (by simp),vx5]
  · intro k hk
    rw [tw k hk]
    apply packWord_congr _ k hk
    intro j hj
    change v.getMem _=_
    rw [vw j hj,cx6,hux7,hu0,hu1]
    apply postWord_congr _ _ j hj
    intro i hi
    unfold nWord
    split
    · rename_i h0; subst h0; rw [show ClaudeWCT.W9.Machine.Sign.SIG+8*0=ClaudeWCT.W9.Machine.Sign.SIG from rfl,c0,hu0,hu1]
    · split
      · rename_i h1; subst h1; rw [show ClaudeWCT.W9.Machine.Sign.SIG+8*1=ClaudeWCT.W9.Machine.Sign.SIG+8 from rfl,c1,hu0,hu1]
      · rw [cfr _ (by so) (by so) (by so)]
        exact huw i hi


#print axioms full_readout
end OuterSerializer
