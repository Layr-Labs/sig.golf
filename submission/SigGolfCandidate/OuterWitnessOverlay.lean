import SigGolfCandidate.OuterExpand
import SigGolfCandidate.Merge097
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterWitnessOverlay
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open SphincsSecurity (bytesLE bytesLE_length)
open OuterExpand

def list (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat) : List UInt8 :=
  (witListF16 output w).mapIdx (fun i b=>outerNonceByte nonces i b)

theorem byte_free (nonces : List Nat) (i : Nat) (b : UInt8)
    (h : ∀ k, k < 5 → i < outerNoncePos k ∨ outerNoncePos k + 8 ≤ i) : outerNonceByte nonces i b=b := by
  unfold outerNonceByte
  rw [List.find?_eq_none.mpr]
  intro k hk
  have := h k (List.mem_range.mp hk)
  simp only [decide_eq_true_eq,not_and,not_lt]
  omega

theorem getElem (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat) (n : Nat) :
    (list output w nonces)[n]?=(witListF16 output w)[n]?.map (outerNonceByte nonces n) := by
  rw [list,List.getElem?_mapIdx]

theorem window_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (off k : Nat) (h : ∀ c,c<5 → off+k≤outerNoncePos c ∨ outerNoncePos c+8≤off) :
    ((list output w nonces).drop off).take k=((witListF16 output w).drop off).take k := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take,List.getElem?_take,List.getElem?_drop,List.getElem?_drop,getElem]
  split_ifs with hn
  · cases (witListF16 output w)[off+n]? with
    | none=>rfl
    | some b=>
      simp only [Option.map_some]
      rw [byte_free _ _ _ (fun c hc=>by have := h c hc;omega)]
  · rfl

theorem extract_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (off k : Nat) (hk : off+k≤21756) (h : ∀ c,c<5 → off+k≤outerNoncePos c ∨ outerNoncePos c+8≤off) :
    (witEncOuter output w nonces).extractLsb' (8*off) (8*k)=(witEncF16 output w).extractLsb' (8*off) (8*k) := by
  unfold witEncOuter witEncF16
  rw [ClaudeWCT.W9.T3M.PairedReadout.extract_readLE _ 21756 _ _ hk,ClaudeWCT.W9.T3M.PairedReadout.extract_readLE _ 21756 _ _ hk]
  exact congrArg (fun b=>BitVec.ofNat (8*k) (readLE b)) (window_free output w nonces off k h)

def WinFree (off n : Nat) : Prop := off+n≤848 ∧ (off+n≤816 ∨ 824≤off)

theorem region_free (coord : Fin 9) (o n : Nat) (h : WinFree o n) :
    ∀ c,c<5 → V3.regionOffset coord.val+o+n≤outerNoncePos c ∨ outerNoncePos c+8≤V3.regionOffset coord.val+o := by
  intro c hc
  unfold WinFree at h
  unfold outerNoncePos outerCoord V3.regionOffset
  interval_cases c <;> norm_num
  all_goals have := coord.isLt;omega

theorem extract_region (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (coord : Fin 9) (o n : Nat) (h : WinFree o n) :
    (witEncOuter output w nonces).extractLsb' (8*(V3.regionOffset coord.val+o)) (8*n)=
      (witEncF16 output w).extractLsb' (8*(V3.regionOffset coord.val+o)) (8*n) := by
  exact extract_free output w nonces _ n (by
    simp only [WinFree,V3.regionOffset] at h ⊢
    have := coord.isLt
    omega) (by simpa only [Nat.add_assoc] using region_free coord o n h)

#print axioms extract_region

theorem wdig_region (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (coord : Fin 9) (o : Nat) (h : WinFree o 16) :
    W9Machine.wdig (witEncOuter output w nonces) (V3.regionOffset coord.val+o)=W9Machine.wdig (witEncF16 output w) (V3.regionOffset coord.val+o) := by
  unfold W9Machine.wdig
  exact extract_free output w nonces _ 16 (by
    simp only [WinFree,V3.regionOffset] at h ⊢
    have := coord.isLt
    omega) (by simpa only [Nat.add_assoc] using region_free coord o 16 h)

#print axioms byte_free
#print axioms extract_free
#print axioms region_free
#print axioms wdig_region
end OuterWitnessOverlay
