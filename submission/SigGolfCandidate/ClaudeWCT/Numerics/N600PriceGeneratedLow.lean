import SigGolfCandidate.ClaudeWCT.Numerics.N600PriceGeneratedCommon

set_option Elab.async false

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked

certify_pair_chunk 5 0 1 Pair_5_0 pair_5_0_checked
certify_pair_chunk 5 1 1 Pair_5_1 pair_5_1_checked
certify_pair_chunk 5 2 1 Pair_5_2 pair_5_2_checked
certify_pair_chunk 5 3 1 Pair_5_3 pair_5_3_checked
certify_pair_chunk 5 4 1 Pair_5_4 pair_5_4_checked
certify_pair_chunk 5 5 1 Pair_5_5 pair_5_5_checked

noncomputable def Pair_5 : Nat := pair_sum_numeral% 5

noncomputable def chunks_5 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_5_0
  | 1 => Pair_5_1
  | 2 => Pair_5_2
  | 3 => Pair_5_3
  | 4 => Pair_5_4
  | 5 => Pair_5_5
  | _ => 0

theorem chunks_5_checked (t : Nat) (ht : t ≤ 5) :
    pairChunkWith cachedCoordinate 5 t 1 = chunks_5 t := by
  interval_cases t
  · exact pair_5_0_checked
  · exact pair_5_1_checked
  · exact pair_5_2_checked
  · exact pair_5_3_checked
  · exact pair_5_4_checked
  · exact pair_5_5_checked

theorem pair_5_checked : pairFirst 5 = Pair_5 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_5 5
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_5_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 6 0 1 Pair_6_0 pair_6_0_checked
certify_pair_chunk 6 1 1 Pair_6_1 pair_6_1_checked
certify_pair_chunk 6 2 1 Pair_6_2 pair_6_2_checked
certify_pair_chunk 6 3 1 Pair_6_3 pair_6_3_checked
certify_pair_chunk 6 4 1 Pair_6_4 pair_6_4_checked
certify_pair_chunk 6 5 1 Pair_6_5 pair_6_5_checked
certify_pair_chunk 6 6 1 Pair_6_6 pair_6_6_checked

noncomputable def Pair_6 : Nat := pair_sum_numeral% 6

noncomputable def chunks_6 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_6_0
  | 1 => Pair_6_1
  | 2 => Pair_6_2
  | 3 => Pair_6_3
  | 4 => Pair_6_4
  | 5 => Pair_6_5
  | 6 => Pair_6_6
  | _ => 0

theorem chunks_6_checked (t : Nat) (ht : t ≤ 6) :
    pairChunkWith cachedCoordinate 6 t 1 = chunks_6 t := by
  interval_cases t
  · exact pair_6_0_checked
  · exact pair_6_1_checked
  · exact pair_6_2_checked
  · exact pair_6_3_checked
  · exact pair_6_4_checked
  · exact pair_6_5_checked
  · exact pair_6_6_checked

theorem pair_6_checked : pairFirst 6 = Pair_6 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_6 6
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_6_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 7 0 1 Pair_7_0 pair_7_0_checked
certify_pair_chunk 7 1 1 Pair_7_1 pair_7_1_checked
certify_pair_chunk 7 2 1 Pair_7_2 pair_7_2_checked
certify_pair_chunk 7 3 1 Pair_7_3 pair_7_3_checked
certify_pair_chunk 7 4 1 Pair_7_4 pair_7_4_checked
certify_pair_chunk 7 5 1 Pair_7_5 pair_7_5_checked
certify_pair_chunk 7 6 1 Pair_7_6 pair_7_6_checked
certify_pair_chunk 7 7 1 Pair_7_7 pair_7_7_checked

noncomputable def Pair_7 : Nat := pair_sum_numeral% 7

noncomputable def chunks_7 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_7_0
  | 1 => Pair_7_1
  | 2 => Pair_7_2
  | 3 => Pair_7_3
  | 4 => Pair_7_4
  | 5 => Pair_7_5
  | 6 => Pair_7_6
  | 7 => Pair_7_7
  | _ => 0

theorem chunks_7_checked (t : Nat) (ht : t ≤ 7) :
    pairChunkWith cachedCoordinate 7 t 1 = chunks_7 t := by
  interval_cases t
  · exact pair_7_0_checked
  · exact pair_7_1_checked
  · exact pair_7_2_checked
  · exact pair_7_3_checked
  · exact pair_7_4_checked
  · exact pair_7_5_checked
  · exact pair_7_6_checked
  · exact pair_7_7_checked

theorem pair_7_checked : pairFirst 7 = Pair_7 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_7 7
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_7_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 8 0 1 Pair_8_0 pair_8_0_checked
certify_pair_chunk 8 1 1 Pair_8_1 pair_8_1_checked
certify_pair_chunk 8 2 1 Pair_8_2 pair_8_2_checked
certify_pair_chunk 8 3 1 Pair_8_3 pair_8_3_checked
certify_pair_chunk 8 4 1 Pair_8_4 pair_8_4_checked
certify_pair_chunk 8 5 1 Pair_8_5 pair_8_5_checked
certify_pair_chunk 8 6 1 Pair_8_6 pair_8_6_checked
certify_pair_chunk 8 7 1 Pair_8_7 pair_8_7_checked
certify_pair_chunk 8 8 1 Pair_8_8 pair_8_8_checked

noncomputable def Pair_8 : Nat := pair_sum_numeral% 8

noncomputable def chunks_8 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_8_0
  | 1 => Pair_8_1
  | 2 => Pair_8_2
  | 3 => Pair_8_3
  | 4 => Pair_8_4
  | 5 => Pair_8_5
  | 6 => Pair_8_6
  | 7 => Pair_8_7
  | 8 => Pair_8_8
  | _ => 0

theorem chunks_8_checked (t : Nat) (ht : t ≤ 8) :
    pairChunkWith cachedCoordinate 8 t 1 = chunks_8 t := by
  interval_cases t
  · exact pair_8_0_checked
  · exact pair_8_1_checked
  · exact pair_8_2_checked
  · exact pair_8_3_checked
  · exact pair_8_4_checked
  · exact pair_8_5_checked
  · exact pair_8_6_checked
  · exact pair_8_7_checked
  · exact pair_8_8_checked

theorem pair_8_checked : pairFirst 8 = Pair_8 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_8 8
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_8_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 9 0 1 Pair_9_0 pair_9_0_checked
certify_pair_chunk 9 1 1 Pair_9_1 pair_9_1_checked
certify_pair_chunk 9 2 1 Pair_9_2 pair_9_2_checked
certify_pair_chunk 9 3 1 Pair_9_3 pair_9_3_checked
certify_pair_chunk 9 4 1 Pair_9_4 pair_9_4_checked
certify_pair_chunk 9 5 1 Pair_9_5 pair_9_5_checked
certify_pair_chunk 9 6 1 Pair_9_6 pair_9_6_checked
certify_pair_chunk 9 7 1 Pair_9_7 pair_9_7_checked
certify_pair_chunk 9 8 1 Pair_9_8 pair_9_8_checked
certify_pair_chunk 9 9 1 Pair_9_9 pair_9_9_checked

noncomputable def Pair_9 : Nat := pair_sum_numeral% 9

noncomputable def chunks_9 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_9_0
  | 1 => Pair_9_1
  | 2 => Pair_9_2
  | 3 => Pair_9_3
  | 4 => Pair_9_4
  | 5 => Pair_9_5
  | 6 => Pair_9_6
  | 7 => Pair_9_7
  | 8 => Pair_9_8
  | 9 => Pair_9_9
  | _ => 0

theorem chunks_9_checked (t : Nat) (ht : t ≤ 9) :
    pairChunkWith cachedCoordinate 9 t 1 = chunks_9 t := by
  interval_cases t
  · exact pair_9_0_checked
  · exact pair_9_1_checked
  · exact pair_9_2_checked
  · exact pair_9_3_checked
  · exact pair_9_4_checked
  · exact pair_9_5_checked
  · exact pair_9_6_checked
  · exact pair_9_7_checked
  · exact pair_9_8_checked
  · exact pair_9_9_checked

theorem pair_9_checked : pairFirst 9 = Pair_9 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_9 9
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_9_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 10 0 1 Pair_10_0 pair_10_0_checked
certify_pair_chunk 10 1 1 Pair_10_1 pair_10_1_checked
certify_pair_chunk 10 2 1 Pair_10_2 pair_10_2_checked
certify_pair_chunk 10 3 1 Pair_10_3 pair_10_3_checked
certify_pair_chunk 10 4 1 Pair_10_4 pair_10_4_checked
certify_pair_chunk 10 5 1 Pair_10_5 pair_10_5_checked
certify_pair_chunk 10 6 1 Pair_10_6 pair_10_6_checked
certify_pair_chunk 10 7 1 Pair_10_7 pair_10_7_checked
certify_pair_chunk 10 8 1 Pair_10_8 pair_10_8_checked
certify_pair_chunk 10 9 1 Pair_10_9 pair_10_9_checked
certify_pair_chunk 10 10 1 Pair_10_10 pair_10_10_checked

noncomputable def Pair_10 : Nat := pair_sum_numeral% 10

noncomputable def chunks_10 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_10_0
  | 1 => Pair_10_1
  | 2 => Pair_10_2
  | 3 => Pair_10_3
  | 4 => Pair_10_4
  | 5 => Pair_10_5
  | 6 => Pair_10_6
  | 7 => Pair_10_7
  | 8 => Pair_10_8
  | 9 => Pair_10_9
  | 10 => Pair_10_10
  | _ => 0

theorem chunks_10_checked (t : Nat) (ht : t ≤ 10) :
    pairChunkWith cachedCoordinate 10 t 1 = chunks_10 t := by
  interval_cases t
  · exact pair_10_0_checked
  · exact pair_10_1_checked
  · exact pair_10_2_checked
  · exact pair_10_3_checked
  · exact pair_10_4_checked
  · exact pair_10_5_checked
  · exact pair_10_6_checked
  · exact pair_10_7_checked
  · exact pair_10_8_checked
  · exact pair_10_9_checked
  · exact pair_10_10_checked

theorem pair_10_checked : pairFirst 10 = Pair_10 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_10 10
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_10_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 11 0 1 Pair_11_0 pair_11_0_checked
certify_pair_chunk 11 1 1 Pair_11_1 pair_11_1_checked
certify_pair_chunk 11 2 1 Pair_11_2 pair_11_2_checked
certify_pair_chunk 11 3 1 Pair_11_3 pair_11_3_checked
certify_pair_chunk 11 4 1 Pair_11_4 pair_11_4_checked
certify_pair_chunk 11 5 1 Pair_11_5 pair_11_5_checked
certify_pair_chunk 11 6 1 Pair_11_6 pair_11_6_checked
certify_pair_chunk 11 7 1 Pair_11_7 pair_11_7_checked
certify_pair_chunk 11 8 1 Pair_11_8 pair_11_8_checked
certify_pair_chunk 11 9 1 Pair_11_9 pair_11_9_checked
certify_pair_chunk 11 10 1 Pair_11_10 pair_11_10_checked
certify_pair_chunk 11 11 1 Pair_11_11 pair_11_11_checked

noncomputable def Pair_11 : Nat := pair_sum_numeral% 11

noncomputable def chunks_11 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_11_0
  | 1 => Pair_11_1
  | 2 => Pair_11_2
  | 3 => Pair_11_3
  | 4 => Pair_11_4
  | 5 => Pair_11_5
  | 6 => Pair_11_6
  | 7 => Pair_11_7
  | 8 => Pair_11_8
  | 9 => Pair_11_9
  | 10 => Pair_11_10
  | 11 => Pair_11_11
  | _ => 0

theorem chunks_11_checked (t : Nat) (ht : t ≤ 11) :
    pairChunkWith cachedCoordinate 11 t 1 = chunks_11 t := by
  interval_cases t
  · exact pair_11_0_checked
  · exact pair_11_1_checked
  · exact pair_11_2_checked
  · exact pair_11_3_checked
  · exact pair_11_4_checked
  · exact pair_11_5_checked
  · exact pair_11_6_checked
  · exact pair_11_7_checked
  · exact pair_11_8_checked
  · exact pair_11_9_checked
  · exact pair_11_10_checked
  · exact pair_11_11_checked

theorem pair_11_checked : pairFirst 11 = Pair_11 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_11 11
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_11_checked
  exact h.trans (by decide +kernel)

end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 12 0 1 Pair_12_0 pair_12_0_checked
certify_pair_chunk 12 1 1 Pair_12_1 pair_12_1_checked
certify_pair_chunk 12 2 1 Pair_12_2 pair_12_2_checked
certify_pair_chunk 12 3 1 Pair_12_3 pair_12_3_checked
certify_pair_chunk 12 4 1 Pair_12_4 pair_12_4_checked
certify_pair_chunk 12 5 1 Pair_12_5 pair_12_5_checked
certify_pair_chunk 12 6 1 Pair_12_6 pair_12_6_checked
certify_pair_chunk 12 7 1 Pair_12_7 pair_12_7_checked
certify_pair_chunk 12 8 1 Pair_12_8 pair_12_8_checked
certify_pair_chunk 12 9 1 Pair_12_9 pair_12_9_checked
certify_pair_chunk 12 10 1 Pair_12_10 pair_12_10_checked
certify_pair_chunk 12 11 1 Pair_12_11 pair_12_11_checked
certify_pair_chunk 12 12 1 Pair_12_12 pair_12_12_checked

noncomputable def Pair_12 : Nat := pair_sum_numeral% 12

noncomputable def chunks_12 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_12_0
  | 1 => Pair_12_1
  | 2 => Pair_12_2
  | 3 => Pair_12_3
  | 4 => Pair_12_4
  | 5 => Pair_12_5
  | 6 => Pair_12_6
  | 7 => Pair_12_7
  | 8 => Pair_12_8
  | 9 => Pair_12_9
  | 10 => Pair_12_10
  | 11 => Pair_12_11
  | 12 => Pair_12_12
  | _ => 0

theorem chunks_12_checked (t : Nat) (ht : t ≤ 12) :
    pairChunkWith cachedCoordinate 12 t 1 = chunks_12 t := by
  interval_cases t
  · exact pair_12_0_checked
  · exact pair_12_1_checked
  · exact pair_12_2_checked
  · exact pair_12_3_checked
  · exact pair_12_4_checked
  · exact pair_12_5_checked
  · exact pair_12_6_checked
  · exact pair_12_7_checked
  · exact pair_12_8_checked
  · exact pair_12_9_checked
  · exact pair_12_10_checked
  · exact pair_12_11_checked
  · exact pair_12_12_checked

theorem pair_12_checked : pairFirst 12 = Pair_12 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_12 12
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_12_checked
  exact h.trans (by decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedPair
namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

elab "forest_numeral% " r:num : term => do
  let pInfo ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedPair.Pair_{r.getNat}").toName)
  let qInfo ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_128_{r.getNat}").toName)
  match pInfo.value!.nat?, qInfo.value!.getAppArgs[3]!.nat? with
  | some p, some q => return mkNatLit ((spread 11 p)^4 * spread 10 q)
  | _, _ => throwError "forest inputs are not Nat literals"

noncomputable def Forest_5 : Nat := forest_numeral% 5

theorem forest_5_checked : forest 5=Forest_5 := by
  exact (forest_eq_of_inputs 5 Pair_5 Coordinate_128_5
    pair_5_checked coordinate_128_5_checked).trans (by decide +kernel)

theorem convolution_5_checked : convolutionDots 5 (forest 5)=certifiedPayoff 5 := by
  have hf := congrArg (convolutionDots 5) forest_5_checked
  exact hf.trans ((convolutionDots_eq_of_fees 5 Forest_5 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_6 : Nat := forest_numeral% 6

theorem forest_6_checked : forest 6=Forest_6 := by
  exact (forest_eq_of_inputs 6 Pair_6 Coordinate_128_6
    pair_6_checked coordinate_128_6_checked).trans (by decide +kernel)

theorem convolution_6_checked : convolutionDots 6 (forest 6)=certifiedPayoff 6 := by
  have hf := congrArg (convolutionDots 6) forest_6_checked
  exact hf.trans ((convolutionDots_eq_of_fees 6 Forest_6 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))

noncomputable def Forest_7 : Nat := forest_numeral% 7

theorem forest_7_checked : forest 7=Forest_7 := by
  exact (forest_eq_of_inputs 7 Pair_7 Coordinate_128_7
    pair_7_checked coordinate_128_7_checked).trans (by decide +kernel)

theorem convolution_7_checked : convolutionDots 7 (forest 7)=certifiedPayoff 7 := by
  have hf := congrArg (convolutionDots 7) forest_7_checked
  exact hf.trans ((convolutionDots_eq_of_fees 7 Forest_7 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))

noncomputable def Forest_8 : Nat := forest_numeral% 8

theorem forest_8_checked : forest 8=Forest_8 := by
  exact (forest_eq_of_inputs 8 Pair_8 Coordinate_128_8
    pair_8_checked coordinate_128_8_checked).trans (by decide +kernel)

theorem convolution_8_checked : convolutionDots 8 (forest 8)=certifiedPayoff 8 := by
  have hf := congrArg (convolutionDots 8) forest_8_checked
  exact hf.trans ((convolutionDots_eq_of_fees 8 Forest_8 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))

noncomputable def Forest_9 : Nat := forest_numeral% 9

theorem forest_9_checked : forest 9=Forest_9 := by
  exact (forest_eq_of_inputs 9 Pair_9 Coordinate_128_9
    pair_9_checked coordinate_128_9_checked).trans (by decide +kernel)

theorem convolution_9_checked : convolutionDots 9 (forest 9)=certifiedPayoff 9 := by
  have hf := congrArg (convolutionDots 9) forest_9_checked
  exact hf.trans ((convolutionDots_eq_of_fees 9 Forest_9 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest
namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_10 : Nat := forest_numeral% 10

theorem forest_10_checked : forest 10=Forest_10 := by
  exact (forest_eq_of_inputs 10 Pair_10 Coordinate_128_10
    pair_10_checked coordinate_128_10_checked).trans (by decide +kernel)

theorem convolution_10_checked : convolutionDots 10 (forest 10)=certifiedPayoff 10 := by
  have hf := congrArg (convolutionDots 10) forest_10_checked
  exact hf.trans ((convolutionDots_eq_of_fees 10 Forest_10 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_11 : Nat := forest_numeral% 11

theorem forest_11_checked : forest 11=Forest_11 := by
  exact (forest_eq_of_inputs 11 Pair_11 Coordinate_128_11
    pair_11_checked coordinate_128_11_checked).trans (by decide +kernel)

theorem convolution_11_checked : convolutionDots 11 (forest 11)=certifiedPayoff 11 := by
  have hf := congrArg (convolutionDots 11) forest_11_checked
  exact hf.trans ((convolutionDots_eq_of_fees 11 Forest_11 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_12 : Nat := forest_numeral% 12

theorem forest_12_checked : forest 12=Forest_12 := by
  exact (forest_eq_of_inputs 12 Pair_12 Coordinate_128_12
    pair_12_checked coordinate_128_12_checked).trans (by decide +kernel)

theorem convolution_12_checked : convolutionDots 12 (forest 12)=certifiedPayoff 12 := by
  have hf := congrArg (convolutionDots 12) forest_12_checked
  exact hf.trans ((convolutionDots_eq_of_fees 12 Forest_12 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest
