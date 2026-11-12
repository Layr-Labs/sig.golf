import SigGolfCandidate.OuterVerifierHash
import SigGolfCandidate.OuterReadout
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifierCoordinate
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical SigGolfCandidate.Research.SharedForest

def source (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank) (values : Fin 6→Digest)
    (path : Nat→Digest) (n3 n2 n5 : Nat) (prev : PairRoot) : M PairRoot := do
  let child : Child:=⟨SharedV3.physical coord.val raw.val,SharedV3.physical_lt _ _ raw.isLt⟩
  let inner←recoverSharedInnerN (SharedV3.first coord.val) index coord.val child word values path n3 n2 prev
  if SharedV3.first coord.val then
    pure (SharedV3.orderPair coord.val child.val inner (path 5))
  else
    let lr:=if child.val/32%2=0 then (inner,path 5) else (path 5,inner)
    let outer←OuterGroundCore.hashN coord.val index (2+child.val/64) n5 lr.1 lr.2
    pure (SharedV3.orderPair coord.val child.val outer (path 6))

theorem first (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (n3 n2 n5 : Nat) (prev : PairRoot)
    (hi : index<2^31) (hc : ChainReadout w coord word values)
    (hp : OuterReadout.Path w coord raw path (nDig n3) (pad16 coord.val n2))
    (hf : SharedV3.first coord.val=true) :
    SharedV3.coordinate w index coord raw (embed word) prev=source index coord raw word values path n3 n2 n5 prev := by
  rw [coordinate_canonical w index coord raw word values path prev _ _ hi hc (OuterReadout.to_old_first hp hf),
    canonicalCoordinate_eq_sourceN]
  unfold sourceCoordinateN source
  simp only [hf,if_true]

theorem second (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (n3 n2 n5 : Nat) (prev : PairRoot)
    (hi : index<2^31) (hc : ChainReadout w coord word values)
    (hp : OuterReadout.Path w coord raw path (nDig n3) (pad16 coord.val n2))
    (hf : SharedV3.first coord.val=false)
    (hp5 : SharedV3.nodePad w coord.val (SharedV3.physical coord.val raw.val) 5=nDig n5) :
    SharedV3.coordinate w index coord raw (embed word) prev=source index coord raw word values path n3 n2 n5 prev := by
  have hraw : rawChild false (SharedV3.physical coord.val raw.val)=raw.val:=by
    simpa only [SharedV3.physical,hf] using raw_physical_child (SharedV3.first coord.val) raw.val raw.isLt
  have hlast : SharedV3.lastLevel coord.val=5:=by simp only [SharedV3.lastLevel,hf,Bool.false_eq_true,if_false]
  unfold SharedV3.coordinate source
  dsimp only
  rw [chainProgram_zero _ _ _ _ _ _ hi hc]
  simp only [recoverSharedInnerN_canon]
  simp only [hf,hraw,Bool.false_eq_true,if_false,bind_assoc,pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ends hends
  have hlen : ends.length=6:=by simpa using length_of_support_mapM _ (List.finRange 6) ends hends
  unfold SharedV3.childN
  rw [leafSel_eq _ _ _ _ (SharedV3.physical_lt _ _ raw.isLt) _ _ hlen]
  simp only [hlast,bind_assoc]
  apply bind_congr
  intro leaf
  have hfold : (List.range 5).foldlM (fun value level=>SharedV3.hashSel
      (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level+1))
      (SharedV3.childInput w index coord.val (SharedV3.physical coord.val raw.val) prev.2 value level)) leaf=
      (List.range 5).foldlM (canonicalStepN false index coord.val (SharedV3.physical coord.val raw.val)
        path prev.2 (nDig n3) (pad16 coord.val n2)) leaf := by
    apply foldlM_congr_mem
    intro value level hl
    have hll:=List.mem_range.mp hl
    rw [OuterReadout.childInput _ _ _ _ _ _ _ _ _ _ hp (by omega) hll]
    simp only [canonicalStepN,canonicalChildInput,Bool.false_eq_true,and_false,if_false]
  rw [hfold]
  apply bind_congr
  intro value
  rw [hp.topOther]
  simp only [hlast]
  have he : (128+SharedV3.physical coord.val raw.val)/2^(5+1)=2+SharedV3.physical coord.val raw.val/64:=by omega
  simp only [SharedV3.childInput,hp.siblings 5 (by omega),hp.headerPads 5 (by omega),
    hp5,nodeInput_zero_header,show (5:Nat)≠4 by decide,if_false,he]
  have hhi : V3.hashHi=highHash:=rfl
  rw [hhi]
  rw [canonical_top_outer coord (SharedV3.physical coord.val raw.val) (SharedV3.physical_lt coord.val raw.val raw.isLt) hf,OuterVerifierHash.hashN_eq]
  simp only [ite_pair_fst,ite_pair_snd,show 2^5=32 from rfl]

#print axioms first
#print axioms second
end OuterVerifierCoordinate
