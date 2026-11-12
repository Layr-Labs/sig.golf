import SigGolfCandidate.OuterSignatureCodec
import SigGolfCandidate.OuterCarrierBits
import SigGolfCandidate.Merge045
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCarrierSerialization
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec OuterCarrierBits

theorem byte_cDig (v : OuterSignatureCodec.OldSig) (k : Nat) (hk : k<324) :
    (OuterSignatureCodec.bytes 5184 (v.extractLsb' 0 (8*5184))) ⟨16*k+15,by omega⟩=highByte (cDig v k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hl : 8*(16*k+15)+i<8*5184 := by omega
  have hm : 120+i<128 := by omega
  have he : 8*(16*k+15)+i=128*k+(120+i) := by omega
  simp [OuterSignatureCodec.bytes,highByte,cDig,BitVec.getLsbD_extractLsb',hi,hl,hm,he] <;> omega

theorem cDig_plain (s : SharedSignature) (k : Nat) (hk : 0<k ∧ k<166) (hg : gBits k=0) :
    cDig (sigBC s) k=(sigDigests s).getD k 0 := by
  rw [cDig_sigBC s k (by omega),encList_getD s k (by omega),if_neg (by omega),if_neg (by omega),if_pos hg,
    ClaudeWCT.W9.T3M.getD_eraseIdx,if_pos (by omega)]

theorem pair_cDig (s : SharedSignature) (p : Fin 4) :
    cDig (sigBC s) (25*(p.val+1))=(s.forest.pairs p).secondPath 6 := by
  have hg : gBits (25*(p.val+1))=0 := by fin_cases p <;> rfl
  rw [cDig_plain s _ ⟨by omega,by have := p.isLt;omega⟩ hg]
  have h:=sigDigests_pair s p 24 (by decide)
  rw [show 1+25*p.val+24=25*(p.val+1) by omega] at h
  exact h.trans (pairList_secondPath (s.forest.pairs p) 6)

theorem singleton_cDig (s : SharedSignature) : cDig (sigBC s) 113=s.forest.singleton.path 6 := by
  rw [cDig_plain s 113 (by decide) rfl]
  have h:=sigDigests_singleton s 12 (by decide)
  change (sigDigests s).getD 113 0=_ at h
  rw [h]
  unfold singletonList
  rw [SigGolfCandidate.T3M.getD_append_right' (by simp),List.length_ofFn]
  exact SigGolfCandidate.T3M.getD_ofFn' _ 6 (by decide)

theorem read_carriers (s : SharedSignature) :
    OuterTailBytes.read (OuterSignatureCodec.splitOld (sigBC s)).1=
      carrierBytes ((s.forest.pairs 0).secondPath 6) ((s.forest.pairs 1).secondPath 6)
        ((s.forest.pairs 2).secondPath 6) ((s.forest.pairs 3).secondPath 6) (s.forest.singleton.path 6) := by
  apply OuterTailPacket.Five.ext
  · exact (byte_cDig (sigBC s) 25 (by decide)).trans (congrArg highByte (pair_cDig s 0))
  · exact (byte_cDig (sigBC s) 50 (by decide)).trans (congrArg highByte (pair_cDig s 1))
  · exact (byte_cDig (sigBC s) 75 (by decide)).trans (congrArg highByte (pair_cDig s 2))
  · exact (byte_cDig (sigBC s) 100 (by decide)).trans (congrArg highByte (pair_cDig s 3))
  · exact (byte_cDig (sigBC s) 113 (by decide)).trans (congrArg highByte (singleton_cDig s))

theorem compressed_roundtrip (s : SharedSignature)
    (ha : OuterGroundCore.zeroOk 1 ((s.forest.pairs 0).secondPath 6)=true)
    (hb : OuterGroundCore.zeroOk 3 ((s.forest.pairs 1).secondPath 6)=true)
    (hc : OuterGroundCore.zeroOk 5 ((s.forest.pairs 2).secondPath 6)=true)
    (hd : OuterGroundCore.zeroOk 7 ((s.forest.pairs 3).secondPath 6)=true)
    (he : OuterGroundCore.zeroOk 8 (s.forest.singleton.path 6)=true) :
    OuterSignatureCodec.expand (OuterSignatureCodec.compress (sigBC s))=sigBC s := by
  apply OuterSignatureCodec.expand_compress
  rw [read_carriers]
  exact five_clear _ _ _ _ _ ha hb hc hd he

#print axioms compressed_roundtrip
#print axioms read_carriers
#print axioms pair_cDig
#print axioms singleton_cDig
#print axioms byte_cDig
end OuterCarrierSerialization
