import SigGolfCandidate.OuterSignTrampRun
import SigGolfCandidate.OuterSignLook
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignNode
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open ClaudeWCT
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedNode
open SphincsSecurity (bytesLE bytesLE_length)
def UnitWrites (h X : Nat) : Prop := unitW h X ∨ X=1152 ∨ X=1160
theorem hash_unit {sk : BitVec 256} {c index h : Nat} {pad L R : Digest}
    (hn:LookOK OuterImages.signImage (look c)) (ht:LookOK OuterImages.signImage (SharedTail.look c))
    (hfirst : SharedTail.first c=true→4≤h)
    (hc:c<9) (hi:index<2^31) (hh1:1≤h) (hh:h<128) (hne:h≠1)
    {s : MachineState} (hpc:s.pc=pcOf (entry c))
    (h5:s.getReg .x5=0) (h18:s.getReg .x18=BitVec.ofNat 64 h) (h22:s.getReg .x22=BitVec.ofNat 64 index)
    (hL:DigAt s (HEAPW+16*(2*h)) L) (hR:DigAt s (HEAPW+16*(2*h+1)) R) (hp:SharedNode.PadAt c h pad s) (hz:SaveZ s) :
    TBSim OuterImages.signImage sk s (unitC+77865) (OuterSignNodeModel.hashProgram c index h pad L R) (fun root t=>
      t.pc=pcOf (if h-1≠SharedTail.limit c then SharedTail.nodePc c else SharedTail.finishPc c) ∧
      t.getReg .x18=BitVec.ofNat 64 (h-1) ∧ DigAt t (HEAPW+16*h) root ∧
      RegsExcept s t [.x3,.x6,.x7,.x10,.x11,.x12,.x18,.x28,.x29] ∧ Frame s t (UnitWrites h)) := by
  obtain ⟨u,su,upc,x10,x11,x12,um,ru,fu⟩:=step_node hn hc hh s hpc h18 h22
  have hw:=input_of_readout s u hc hi hh hne h18 h22 hL hR hp um
  obtain ⟨hpcb,hent⟩:=hashPc_lt c hc
  have hTv:SigGolfCandidate.FtsGrind.SIGN_TRAMP+5*c < 25390:=by
    simp only[SigGolfCandidate.FtsGrind.SIGN_TRAMP];omega
  have cj:CodeAt OuterImages.signImage (pcOf (hashPc c)) [SigGolfCandidate.FtsGrind.encJal 0
      (SigGolfCandidate.FtsGrind.jOff (hashPc c) (SigGolfCandidate.FtsGrind.SIGN_TRAMP+5*c))]:=
    ClaudeWCT.W9.Machine.Expand.codeAt_of_look hn (hashPc c) _ (by simp only[List.length_singleton];omega) (fun i hi=>by
      have hi0:i=0:=by simpa using hi
      subst hi0
      simpa using site_look c hc)
  have sj:=SigGolfCandidate.FtsGrind.jal_step (r:=.x0) (by decide) rfl cj (by omega) (by omega) u upc
  have r1:∀r,((u.setReg .x0 (pcOf (hashPc c+1))).setPC
      (pcOf (SigGolfCandidate.FtsGrind.SIGN_TRAMP+5*c))).getReg r=u.getReg r:=fun r=>by cases r <;> rfl
  have m1:Frame u ((u.setReg .x0 (pcOf (hashPc c+1))).setPC
      (pcOf (SigGolfCandidate.FtsGrind.SIGN_TRAMP+5*c))) (fun _=>False):=fun _ _ _=>rfl
  have hsplit:u.readWords (BitVec.ofNat 64 NODEW) 4=wordsOf (SigGolfCandidate.FtsGrind.ftsPre c index h L) ∧
      u.readWords (BitVec.ofNat 64 (NODEW+32)) 2=wordsOf (bytesLE 16 pad) ∧
      u.readWords (BitVec.ofNat 64 (NODEW+48)) 2=wordsOf (bytesLE 16 R):=by
    rw[show (8:Nat)=4+(2+2) from rfl,readWords_add,readWords_add,show NODEW+8*4=NODEW+32 from rfl,
      show NODEW+32+8*2=NODEW+48 from rfl]at hw
    have e:nodeIn c index h pad L R=SigGolfCandidate.FtsGrind.ftsPre c index h L++(bytesLE 16 pad++bytesLE 16 R):=by
      simp only[nodeIn,SigGolfCandidate.FtsGrind.ftsPre,List.append_assoc]
    rw[e,wordsOf_append _ _ (by simp[SigGolfCandidate.FtsGrind.ftsPre,bytesLE_length]),
      wordsOf_append _ _ (by simp[bytesLE_length])]at hw
    obtain ⟨a1,a2⟩:=List.append_inj hw (by
      rw[readWords_length,length_wordsOf 4 _ (by simp[SigGolfCandidate.FtsGrind.ftsPre,bytesLE_length])])
    obtain ⟨b1,b2⟩:=List.append_inj a2 (by rw[readWords_length,length_wordsOf 2 _ (by simp[bytesLE_length])])
    exact ⟨a1,b1,b2⟩
  have F:SigGolfCandidate.FtsGrind.SignIn (SigGolfCandidate.FtsGrind.SIGN_TRAMP+5*c) (hashPc c+1) h NODEW NOUTW
      (SigGolfCandidate.FtsGrind.ftsPre c index h L) (bytesLE 16 pad) (bytesLE 16 R)
      ((u.setReg .x0 (pcOf (hashPc c+1))).setPC (pcOf (SigGolfCandidate.FtsGrind.SIGN_TRAMP+5*c))) :=
    { pc:=rfl
      x5:=by rw[r1,ru.get (by simp)];exact h5
      x10:=by rw[r1];exact x10
      x11:=by rw[r1];exact x11
      x12:=by rw[r1];exact x12
      x18:=by rw[r1,ru.get (by simp)];exact h18
      hheap:=by omega
      lpre:=by simp[SigGolfCandidate.FtsGrind.ftsPre,bytesLE_length]
      lmid:=by simp[bytesLE_length]
      lright:=by simp[bytesLE_length]
      mpre:=by rw[SigGolfCandidate.FtsGrind.frame_readWordsG m1 NODEW 4 (by ao) (fun _ _ h=>h)];exact hsplit.1
      mmid:=by rw[SigGolfCandidate.FtsGrind.frame_readWordsG m1 (NODEW+32) 2 (by ao) (fun _ _ h=>h)];exact hsplit.2.1
      mright:=by rw[SigGolfCandidate.FtsGrind.frame_readWordsG m1 (NODEW+48) 2 (by ao) (fun _ _ h=>h)];exact hsplit.2.2
      ground:=fun hg8=>by
        have h8:8 ≤ h:=by rcases hg8 with hx|⟨_,hx,_⟩ <;> omega
        have hp0:pad=0:=by
          unfold SharedNode.PadAt at hp
          rw[if_neg (by unfold mode;rw[if_pos h8];omega)]at hp
          exact hp
        have e:=hsplit.2.1
        rw[hp0,wordsOf_bytesLE16,readWords_two]at e
        simp only[List.cons.injEq,and_true]at e
        exact ⟨e.1.trans (by decide),e.2.trans (by decide)⟩
      hA:=by ao
      hA1:=by ao
      hA2:=by ao
      hD:=by ao
      hD1:=by ao
      hD2:=by ao
      hAD:=by ao
      hb:=by omega
      hret:=by omega }
  have houter : h<4→1≤c ∧ pad=0 := by
    intro hlt
    have hc1 : 1≤c := by
      by_contra hn
      have hc0 : c=0 := by omega
      subst c
      have hx:=hfirst (by decide)
      omega
    refine ⟨hc1,?_⟩
    unfold SharedNode.PadAt at hp
    have hm : mode h=2 := by unfold mode;rw [if_neg (by omega),if_neg (by omega)]
    rw [if_neg (by rw [hm];omega)] at hp
    exact hp
  have run:=OuterSignTrampRun.run (sk:=sk) hc hi (by omega) hh houter F
  rw[OuterSignNodeModel.trampoline c index h pad L R hc]
  refine (TBSim.steps su (TBSim.steps sj (TBSim.bind (W₂:=22) run (fun r t ho=>?_)))).mono ?_ (fun _ _ h=>h)
  · have t18:t.getReg .x18=BitVec.ofNat 64 h:=by rw[ho.regs.get (by simp),r1,ru.get (by simp)];exact h18
    have tpc:t.pc=pcOf (SharedTail.entry c):=by rw[ho.pc,hent]
    obtain ⟨t',st,hcost,tpc',t18',m0,m8,rt,ft⟩:=SharedTail.step_tail ht hc hh1 hh
      (decide (h-1≠SharedTail.limit c)) rfl t tpc t18
    have hv:=half_at (t:=t) (a:=r.2) (high c h) ho.ans
    refine (TBSim.pure_steps' st ?_).mono hcost (fun _ _ h=>h)
    refine ⟨?_,t18',⟨?_,?_⟩,?_,?_⟩
    · simpa only[decide_eq_true_eq]using tpc'
    · rw[m0];exact hv.1
    · rw[m8];exact hv.2
    · exact ((ru.trans (fun x _=>r1 x : RegsExcept u _ [])).trans (ho.regs.trans rt)).mono (by simp)
    · intro X hX hn
      have hnOld : ¬unitW h X := fun hx=>hn (Or.inl hx)
      have hn1152 : X≠1152 := fun hx=>hn (Or.inr (Or.inl hx))
      have hn1160 : X≠1160 := fun hx=>hn (Or.inr (Or.inr hx))
      have hn1:¬(X=HEAPW+16*h+8 ∨ X=HEAPW+16*h):=fun h'=>hnOld (by
        rcases h' with h'|h'
        · exact Or.inr (Or.inr (Or.inr h'))
        · exact Or.inr (Or.inr (Or.inl h')))
      rw[ft.get hX hn1]
      have hnw:¬writes X:=fun h'=>hnOld (Or.inl h')
      by_cases hsv:saveCell X
      · obtain ⟨z0,z1,z3,z4⟩:=hz
        rcases hsv with rfl|rfl|rfl|rfl
        · exact ho.sv0.trans z0.symm
        · exact ho.sv1.trans z1.symm
        · by_cases hg8:8 ≤ h ∧ h < 16
          · exact (ho.sv3 hg8).trans z3.symm
          · exact (ho.sv3p hg8).trans ((m1.get hX id).trans (fu.get hX hnw))
        · exact ho.sv4.trans z4.symm
      · have hns:¬SigGolfCandidate.FtsGrind.SignW NOUTW X:=by
          rintro (h'|h'|h'|h'|h')
          · exact hnOld (Or.inr (Or.inl h'))
          all_goals exact hsv (by simp only[saveCell];omega)
        rw[ho.frame.get hX (by unfold OuterSignInterface.Writes;tauto),m1.get hX id,fu.get hX hnw]
  · have:=cycles_le c (mode h)
    have:=signW_le c h (decide (c<4))
    unfold unitC
    omega

#print axioms hash_unit
end OuterSignNode
