import SigGolfCandidate.OuterFinalPost
import SigGolfCandidate.OuterPostFrame
import SigGolfCandidate.OuterLegacyPost
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSuffix
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

def work : Nat := suffixW+21

theorem suffix_done (ns : List Nat) {sk : BitVec 256} {r : Option (HashOutput × SharedForest.Witness)} {s : MachineState}
    (h : OuterLayersRecovery.SuffixDone ns r s) :
    TBSim OuterImages.expandImage sk s work (pure r) (OuterFinalPost.Post ns) := by
  cases r with
  | none =>
    rcases h with hp|⟨hp,h5,h10,hfetch⟩
    · obtain ⟨t,st,tp,t5,t10,tfetch⟩:=Search.cs0_spec OuterSearchCodes.code s hp
      exact (TBSim.steps st (TBSim.pure (Q:=(OuterFinalPost.Post ns)) (a:=none)
        ⟨Or.inl tp,t5,t10,tfetch⟩)).mono (by unfold work suffixW; omega) (fun _ _ h=>h)
    · exact (TBSim.pure (Q:=(OuterFinalPost.Post ns)) (a:=none)
        ⟨Or.inl hp,h5,h10,hfetch⟩).mono (by unfold work suffixW; omega) (fun _ _ h=>h)
  | some p =>
    rcases p with ⟨output,w⟩
    obtain ⟨hd,houter⟩:=h
    obtain ⟨hp,h5,ph,hn,hrec,hfts,hfts16⟩:=hd
    obtain ⟨t,st,tp,tr,tbuf,tm⟩:=OuterPostEnc.pp_witEnc s hp output w ph.fts ph.old ph.choice ph.leaf
    have touter : OuterForestCompactRecords.Inv 9 ns t := OuterPostFrame.of_memory houter (by
      intro m
      have hb:=OuterPostFrame.record_bounds m
      rw [tm _ (by omega),OuterPostFrame.pp_mem _ _ _ hb.1 hb.2])
    have hscr (A:Nat) (h1:0x66700 ≤ A) (h2:A<0x66760) : t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
      rw [tm A (by omega)]; exact PostEnc.ppMem_scratch _ _ A h1 h2
    have hl : (SigGolfCandidate.T3.route (WCT9.digestIndex output) 0).1<4096 := by
      unfold SigGolfCandidate.T3.route; simp [SigGolfCandidate.T3.height]; omega
    have tleaf : (t.getMem (BitVec.ofNat 64 0x66758)).toNat % 4096=(SigGolfCandidate.T3.route (WCT9.digestIndex output) 0).1 % 4096 := by
      rw [hscr _ (by norm_num) (by norm_num),hn.2.2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show _ < 2^64 by omega)]
    have tnon : ∀ j, j < 11 → t.getMem (PadWriter.nonceAddr j)=BitVec.ofNat 64 (w.topNonces.getD j 0) := by
      intro j hj
      unfold PadWriter.nonceAddr
      rw [hscr _ (by omega) (by omega)]
      exact hn.2.1 j hj
    have trec : PadWit.RecTable t.getMem output w := RecTable.frame hrec (fun A h1 h2 => by
      rw [tm A (by omega)]; exact ppMem_rec _ _ A h1 h2)
    have tfts : FtsRecsN output w.ftsNonces t := FtsRecsN.frame hfts (fun A h1 h2 => by
      rw [tm A (by omega)]; exact ppMem_fts _ _ A h1 h2)
    have tfts16 : FtsRecs16 output w.ftsNonces16 t := FtsRecs16.frame hfts16 (fun A h1 h2 => by
      rw [tm A (by omega)]; exact ppMem_fts16 _ _ A h1 h2)
    obtain ⟨u,su,up,u10,ur,ubuf,ukeep⟩:=OuterPadWitness.pad_hook_witEncG t tp output w tleaf tnon trec tbuf
    have uouter : OuterForestCompactRecords.Inv 9 ns u := OuterPostFrame.of_memory touter (by
      intro m
      have hb:=OuterPostFrame.record_bounds m
      apply ukeep _
      · intro j hj he
        have hc:=congrArg BitVec.toNat he
        have hn:=PairedNonce.noncePos_bounds output j hj
        simp only [BitVec.toNat_ofNat] at hc
        omega
      · intro e he' he
        have hc:=congrArg BitVec.toNat he
        obtain ⟨hl,_,hn⟩:=PairedNonce.lowerNoncePos_area output e he'
        have :=(PairedNonce.lower_area_ge e.1 hl).2
        simp only [BitVec.toNat_ofNat] at hc
        omega)
    have u5 : u.getReg .x5=1 := by rw [ur .x5 (by simp),tr .x5 (by simp)]; exact h5
    have ufts : FtsRecsN output w.ftsNonces u := FtsRecsN.frame tfts (fun A h1 h2 => ukeep _
      (fun j hj he => by
        have := congrArg BitVec.toNat he
        have hb := PairedNonce.noncePos_bounds output j hj
        simp only [BitVec.toNat_ofNat] at this
        omega)
      (fun e he' he => by
        have hc := congrArg BitVec.toNat he
        obtain ⟨hl, _, hb⟩ := PairedNonce.lowerNoncePos_area output e he'
        have := (PairedNonce.lower_area_ge e.1 hl).2
        simp only [BitVec.toNat_ofNat] at hc
        omega))
    have ufts16 : FtsRecs16 output w.ftsNonces16 u := FtsRecs16.frame tfts16 (fun A h1 h2 => ukeep _
      (fun j hj he => by
        have := congrArg BitVec.toNat he
        have hb := PairedNonce.noncePos_bounds output j hj
        simp only [BitVec.toNat_ofNat] at this
        omega)
      (fun e he' he => by
        have hc := congrArg BitVec.toNat he
        obtain ⟨hl, _, hb⟩ := PairedNonce.lowerNoncePos_area output e he'
        have := (PairedNonce.lower_area_ge e.1 hl).2
        simp only [BitVec.toNat_ofNat] at hc
        omega))
    -- E8 HALT hook: `60732: jal 61050`; POST stores the nine FTS nonces at their witness pads, then (Y5 #1)
    -- jumps to POST16, which stores the four level-2 nonces.
    obtain ⟨v,sv,vp,vr,vm⟩:=SigGolfCandidate.FtsGrind.post_run OuterLegacyPost.installed3 u up
      (fun k=>4256 + Paired.ftsNoncePos output k)
      (fun k hk=>by have := (ufts ⟨k, hk⟩).1; exact this)
      (fun k hk=>⟨by have := ftsNoncePos_mod output k; omega,
        by have := PairedNonce.ftsNoncePos_lt output k hk; unfold SigGolfCandidate.FtsGrind.SCR; omega⟩)
    have vouter : OuterForestCompactRecords.Inv 9 ns v := OuterPostFrame.of_memory uouter (by
      intro m
      have hb:=OuterPostFrame.record_bounds m
      rw [vm,postMem_miss _ _ (by
        intro k hk he
        unfold SigGolfCandidate.FtsGrind.sB at he
        have hh:=(ufts ⟨k,hk⟩).1
        dsimp only at hh
        rw [hh] at he
        have hc:=congrArg BitVec.toNat he
        have hn:=PairedNonce.ftsNoncePos_lt output k hk
        simp only [BitVec.toNat_ofNat] at hc
        omega)])
    have vrec16 : ∀ m : Fin 4,
        v.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (SigGolfCandidate.FtsGrind.sB m.val))) =
          BitVec.ofNat 64 (4256 + Paired.ftsNonce16Pos output m.val) ∧
        v.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (SigGolfCandidate.FtsGrind.sB m.val) + 8)) =
          BitVec.ofNat 64 (w.ftsNonces16.getD m.val 0) := by
      intro m
      have hm := m.isLt
      have far : ∀ o, o < 16 → ∀ k < 9, BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16
          (SigGolfCandidate.FtsGrind.sB m.val) + o) ≠
          u.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slotA (SigGolfCandidate.FtsGrind.sB k))) := by
        intro o ho k hk e
        unfold SigGolfCandidate.FtsGrind.sB at e
        rw [(ufts ⟨k, hk⟩).1] at e
        have := congrArg BitVec.toNat e
        have hb := PairedNonce.ftsNoncePos_lt output k hk
        have hm4 := m.isLt
        simp only [BitVec.toNat_ofNat, SigGolfCandidate.FtsGrind.slot16, SigGolfCandidate.FtsGrind.SCR16] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
      refine ⟨?_, ?_⟩
      · rw [vm, postMem_miss _ _ (by simpa using far 0 (by decide))]
        exact (ufts16 m).1
      · rw [vm, postMem_miss _ _ (far 8 (by decide))]
        exact (ufts16 m).2
    obtain ⟨v2,sv2,vp2,vr2,vm2⟩:=OuterLegacyPost.run16 OuterLegacyPost.installed16 v vp
      (fun k=>4256 + Paired.ftsNonce16Pos output k)
      (fun k hk=>by have := (vrec16 ⟨k, hk⟩).1; exact this)
      (fun k hk=>⟨by have := ftsNonce16Pos_mod output k; omega,
        by have := PairedNonce16.ftsNonce16Pos_lt output k (by omega); unfold SigGolfCandidate.FtsGrind.SCR; omega⟩)
    have v5 : v2.getReg .x5=1 := by rw [vr2 .x5 (by simp), vr .x5 (by simp)]; exact u5
    have v10 : v2.getReg .x10=0 := by rw [vr2 .x10 (by simp), vr .x10 (by simp)]; exact u10
    have v2outer : OuterForestCompactRecords.Inv 9 ns v2 := OuterPostFrame.of_memory vouter (by
      intro m
      have hb:=OuterPostFrame.record_bounds m
      rw [vm2,OuterPostFrame.post16_miss _ _ (by
        intro k hk he
        rw [(vrec16 ⟨k,hk⟩).1] at he
        have hc:=congrArg BitVec.toNat he
        have hn:=PairedNonce16.ftsNonce16Pos_lt output k (by omega)
        simp only [BitVec.toNat_ofNat] at hc
        omega)])
    have hbuf : ∀ k,k<2720 → v2.getMem (BitVec.ofNat 64 (4256+8*k))=(Paired.witEncF16 output w).extractLsb' (64*k) 64 :=
      fun k hk=>(vm2 _).trans (postMem16_witEncF16 output w v.getMem vrec16
        (fun k hk=>(vm _).trans (postMem_witEncF output w u.getMem (fun m=>ufts m) ubuf k hk)) k hk)
    obtain ⟨v3,sv3,hpost⟩:=OuterFinalPost.run v2 output w ns vp2 v5 v10 v2outer hbuf
    exact (TBSim.steps ((((st.trans su).trans sv).trans sv2).trans sv3)
      (TBSim.pure (Q:=OuterFinalPost.Post ns) (a:=some (output,w)) hpost)).mono
      (by unfold work suffixW;omega) (fun _ _ h=>h)


#print axioms suffix_done
end OuterSuffix
