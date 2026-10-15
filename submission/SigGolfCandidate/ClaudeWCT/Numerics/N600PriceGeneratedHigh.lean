-- Keep the two memory-heavy generated halves serial under the official 24 GiB
-- build limit.  Low already imports GeneratedCommon, so this changes only the
-- Lake dependency graph, not the declarations used below.
import SigGolfCandidate.ClaudeWCT.Numerics.N600PriceGeneratedLow

set_option Elab.async false

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 13 0 1 Pair_13_0 pair_13_0_checked
certify_pair_chunk 13 1 1 Pair_13_1 pair_13_1_checked
certify_pair_chunk 13 2 1 Pair_13_2 pair_13_2_checked
certify_pair_chunk 13 3 1 Pair_13_3 pair_13_3_checked
certify_pair_chunk 13 4 1 Pair_13_4 pair_13_4_checked
certify_pair_chunk 13 5 1 Pair_13_5 pair_13_5_checked
certify_pair_chunk 13 6 1 Pair_13_6 pair_13_6_checked
certify_pair_chunk 13 7 1 Pair_13_7 pair_13_7_checked
certify_pair_chunk 13 8 1 Pair_13_8 pair_13_8_checked
certify_pair_chunk 13 9 1 Pair_13_9 pair_13_9_checked
certify_pair_chunk 13 10 1 Pair_13_10 pair_13_10_checked
certify_pair_chunk 13 11 1 Pair_13_11 pair_13_11_checked
certify_pair_chunk 13 12 1 Pair_13_12 pair_13_12_checked
certify_pair_chunk 13 13 1 Pair_13_13 pair_13_13_checked

noncomputable def Pair_13 : Nat := pair_sum_numeral% 13

noncomputable def chunks_13 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_13_0
  | 1 => Pair_13_1
  | 2 => Pair_13_2
  | 3 => Pair_13_3
  | 4 => Pair_13_4
  | 5 => Pair_13_5
  | 6 => Pair_13_6
  | 7 => Pair_13_7
  | 8 => Pair_13_8
  | 9 => Pair_13_9
  | 10 => Pair_13_10
  | 11 => Pair_13_11
  | 12 => Pair_13_12
  | 13 => Pair_13_13
  | _ => 0

theorem chunks_13_checked (t : Nat) (ht : t ≤ 13) :
    pairChunkWith cachedCoordinate 13 t 1 = chunks_13 t := by
  interval_cases t
  · exact pair_13_0_checked
  · exact pair_13_1_checked
  · exact pair_13_2_checked
  · exact pair_13_3_checked
  · exact pair_13_4_checked
  · exact pair_13_5_checked
  · exact pair_13_6_checked
  · exact pair_13_7_checked
  · exact pair_13_8_checked
  · exact pair_13_9_checked
  · exact pair_13_10_checked
  · exact pair_13_11_checked
  · exact pair_13_12_checked
  · exact pair_13_13_checked

theorem pair_13_checked : pairFirst 13 = Pair_13 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_13 13
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_13_checked
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

noncomputable def Forest_13 : Nat := forest_numeral% 13

theorem forest_13_checked : forest 13=Forest_13 := by
  exact (forest_eq_of_inputs 13 Pair_13 Coordinate_128_13
    pair_13_checked coordinate_128_13_checked).trans (by decide +kernel)

theorem convolution_13_checked : convolutionDots 13 (forest 13)=certifiedPayoff 13 := by
  have hf := congrArg (convolutionDots 13) forest_13_checked
  exact hf.trans ((convolutionDots_eq_of_fees 13 Forest_13 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest
namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 14 0 1 Pair_14_0 pair_14_0_checked
certify_pair_chunk 14 1 1 Pair_14_1 pair_14_1_checked
certify_pair_chunk 14 2 1 Pair_14_2 pair_14_2_checked
certify_pair_chunk 14 3 1 Pair_14_3 pair_14_3_checked
certify_pair_chunk 14 4 1 Pair_14_4 pair_14_4_checked
certify_pair_chunk 14 5 1 Pair_14_5 pair_14_5_checked
certify_pair_chunk 14 6 1 Pair_14_6 pair_14_6_checked
certify_pair_chunk 14 7 1 Pair_14_7 pair_14_7_checked
certify_pair_chunk 14 8 1 Pair_14_8 pair_14_8_checked
certify_pair_chunk 14 9 1 Pair_14_9 pair_14_9_checked
certify_pair_chunk 14 10 1 Pair_14_10 pair_14_10_checked
certify_pair_chunk 14 11 1 Pair_14_11 pair_14_11_checked
certify_pair_chunk 14 12 1 Pair_14_12 pair_14_12_checked
certify_pair_chunk 14 13 1 Pair_14_13 pair_14_13_checked
certify_pair_chunk 14 14 1 Pair_14_14 pair_14_14_checked

noncomputable def Pair_14 : Nat := pair_sum_numeral% 14

noncomputable def chunks_14 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_14_0
  | 1 => Pair_14_1
  | 2 => Pair_14_2
  | 3 => Pair_14_3
  | 4 => Pair_14_4
  | 5 => Pair_14_5
  | 6 => Pair_14_6
  | 7 => Pair_14_7
  | 8 => Pair_14_8
  | 9 => Pair_14_9
  | 10 => Pair_14_10
  | 11 => Pair_14_11
  | 12 => Pair_14_12
  | 13 => Pair_14_13
  | 14 => Pair_14_14
  | _ => 0

theorem chunks_14_checked (t : Nat) (ht : t ≤ 14) :
    pairChunkWith cachedCoordinate 14 t 1 = chunks_14 t := by
  interval_cases t
  · exact pair_14_0_checked
  · exact pair_14_1_checked
  · exact pair_14_2_checked
  · exact pair_14_3_checked
  · exact pair_14_4_checked
  · exact pair_14_5_checked
  · exact pair_14_6_checked
  · exact pair_14_7_checked
  · exact pair_14_8_checked
  · exact pair_14_9_checked
  · exact pair_14_10_checked
  · exact pair_14_11_checked
  · exact pair_14_12_checked
  · exact pair_14_13_checked
  · exact pair_14_14_checked

theorem pair_14_checked : pairFirst 14 = Pair_14 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_14 14
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_14_checked
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

noncomputable def Forest_14 : Nat := forest_numeral% 14

theorem forest_14_checked : forest 14=Forest_14 := by
  exact (forest_eq_of_inputs 14 Pair_14 Coordinate_128_14
    pair_14_checked coordinate_128_14_checked).trans (by decide +kernel)

theorem convolution_14_checked : convolutionDots 14 (forest 14)=certifiedPayoff 14 := by
  have hf := congrArg (convolutionDots 14) forest_14_checked
  exact hf.trans ((convolutionDots_eq_of_fees 14 Forest_14 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 15 0 1 Pair_15_0 pair_15_0_checked
certify_pair_chunk 15 1 1 Pair_15_1 pair_15_1_checked
certify_pair_chunk 15 2 1 Pair_15_2 pair_15_2_checked
certify_pair_chunk 15 3 1 Pair_15_3 pair_15_3_checked
certify_pair_chunk 15 4 1 Pair_15_4 pair_15_4_checked
certify_pair_chunk 15 5 1 Pair_15_5 pair_15_5_checked
certify_pair_chunk 15 6 1 Pair_15_6 pair_15_6_checked
certify_pair_chunk 15 7 1 Pair_15_7 pair_15_7_checked
certify_pair_chunk 15 8 1 Pair_15_8 pair_15_8_checked
certify_pair_chunk 15 9 1 Pair_15_9 pair_15_9_checked
certify_pair_chunk 15 10 1 Pair_15_10 pair_15_10_checked
certify_pair_chunk 15 11 1 Pair_15_11 pair_15_11_checked
certify_pair_chunk 15 12 1 Pair_15_12 pair_15_12_checked
certify_pair_chunk 15 13 1 Pair_15_13 pair_15_13_checked
certify_pair_chunk 15 14 1 Pair_15_14 pair_15_14_checked
certify_pair_chunk 15 15 1 Pair_15_15 pair_15_15_checked

noncomputable def Pair_15 : Nat := pair_sum_numeral% 15

noncomputable def chunks_15 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_15_0
  | 1 => Pair_15_1
  | 2 => Pair_15_2
  | 3 => Pair_15_3
  | 4 => Pair_15_4
  | 5 => Pair_15_5
  | 6 => Pair_15_6
  | 7 => Pair_15_7
  | 8 => Pair_15_8
  | 9 => Pair_15_9
  | 10 => Pair_15_10
  | 11 => Pair_15_11
  | 12 => Pair_15_12
  | 13 => Pair_15_13
  | 14 => Pair_15_14
  | 15 => Pair_15_15
  | _ => 0

theorem chunks_15_checked (t : Nat) (ht : t ≤ 15) :
    pairChunkWith cachedCoordinate 15 t 1 = chunks_15 t := by
  interval_cases t
  · exact pair_15_0_checked
  · exact pair_15_1_checked
  · exact pair_15_2_checked
  · exact pair_15_3_checked
  · exact pair_15_4_checked
  · exact pair_15_5_checked
  · exact pair_15_6_checked
  · exact pair_15_7_checked
  · exact pair_15_8_checked
  · exact pair_15_9_checked
  · exact pair_15_10_checked
  · exact pair_15_11_checked
  · exact pair_15_12_checked
  · exact pair_15_13_checked
  · exact pair_15_14_checked
  · exact pair_15_15_checked

theorem pair_15_checked : pairFirst 15 = Pair_15 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_15 15
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_15_checked
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

noncomputable def Forest_15 : Nat := forest_numeral% 15

theorem forest_15_checked : forest 15=Forest_15 := by
  exact (forest_eq_of_inputs 15 Pair_15 Coordinate_128_15
    pair_15_checked coordinate_128_15_checked).trans (by decide +kernel)

theorem convolution_15_checked : convolutionDots 15 (forest 15)=certifiedPayoff 15 := by
  have hf := congrArg (convolutionDots 15) forest_15_checked
  exact hf.trans ((convolutionDots_eq_of_fees 15 Forest_15 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 16 0 1 Pair_16_0 pair_16_0_checked
certify_pair_chunk 16 1 1 Pair_16_1 pair_16_1_checked
certify_pair_chunk 16 2 1 Pair_16_2 pair_16_2_checked
certify_pair_chunk 16 3 1 Pair_16_3 pair_16_3_checked
certify_pair_chunk 16 4 1 Pair_16_4 pair_16_4_checked
certify_pair_chunk 16 5 1 Pair_16_5 pair_16_5_checked
certify_pair_chunk 16 6 1 Pair_16_6 pair_16_6_checked
certify_pair_chunk 16 7 1 Pair_16_7 pair_16_7_checked
certify_pair_chunk 16 8 1 Pair_16_8 pair_16_8_checked
certify_pair_chunk 16 9 1 Pair_16_9 pair_16_9_checked
certify_pair_chunk 16 10 1 Pair_16_10 pair_16_10_checked
certify_pair_chunk 16 11 1 Pair_16_11 pair_16_11_checked
certify_pair_chunk 16 12 1 Pair_16_12 pair_16_12_checked
certify_pair_chunk 16 13 1 Pair_16_13 pair_16_13_checked
certify_pair_chunk 16 14 1 Pair_16_14 pair_16_14_checked
certify_pair_chunk 16 15 1 Pair_16_15 pair_16_15_checked
certify_pair_chunk 16 16 1 Pair_16_16 pair_16_16_checked

noncomputable def Pair_16 : Nat := pair_sum_numeral% 16

noncomputable def chunks_16 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_16_0
  | 1 => Pair_16_1
  | 2 => Pair_16_2
  | 3 => Pair_16_3
  | 4 => Pair_16_4
  | 5 => Pair_16_5
  | 6 => Pair_16_6
  | 7 => Pair_16_7
  | 8 => Pair_16_8
  | 9 => Pair_16_9
  | 10 => Pair_16_10
  | 11 => Pair_16_11
  | 12 => Pair_16_12
  | 13 => Pair_16_13
  | 14 => Pair_16_14
  | 15 => Pair_16_15
  | 16 => Pair_16_16
  | _ => 0

theorem chunks_16_checked (t : Nat) (ht : t ≤ 16) :
    pairChunkWith cachedCoordinate 16 t 1 = chunks_16 t := by
  interval_cases t
  · exact pair_16_0_checked
  · exact pair_16_1_checked
  · exact pair_16_2_checked
  · exact pair_16_3_checked
  · exact pair_16_4_checked
  · exact pair_16_5_checked
  · exact pair_16_6_checked
  · exact pair_16_7_checked
  · exact pair_16_8_checked
  · exact pair_16_9_checked
  · exact pair_16_10_checked
  · exact pair_16_11_checked
  · exact pair_16_12_checked
  · exact pair_16_13_checked
  · exact pair_16_14_checked
  · exact pair_16_15_checked
  · exact pair_16_16_checked

theorem pair_16_checked : pairFirst 16 = Pair_16 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_16 16
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_16_checked
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

noncomputable def Forest_16 : Nat := forest_numeral% 16

theorem forest_16_checked : forest 16=Forest_16 := by
  exact (forest_eq_of_inputs 16 Pair_16 Coordinate_128_16
    pair_16_checked coordinate_128_16_checked).trans (by decide +kernel)

theorem convolution_16_checked : convolutionDots 16 (forest 16)=certifiedPayoff 16 := by
  have hf := congrArg (convolutionDots 16) forest_16_checked
  exact hf.trans ((convolutionDots_eq_of_fees 16 Forest_16 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 17 0 1 Pair_17_0 pair_17_0_checked
certify_pair_chunk 17 1 1 Pair_17_1 pair_17_1_checked
certify_pair_chunk 17 2 1 Pair_17_2 pair_17_2_checked
certify_pair_chunk 17 3 1 Pair_17_3 pair_17_3_checked
certify_pair_chunk 17 4 1 Pair_17_4 pair_17_4_checked
certify_pair_chunk 17 5 1 Pair_17_5 pair_17_5_checked
certify_pair_chunk 17 6 1 Pair_17_6 pair_17_6_checked
certify_pair_chunk 17 7 1 Pair_17_7 pair_17_7_checked
certify_pair_chunk 17 8 1 Pair_17_8 pair_17_8_checked
certify_pair_chunk 17 9 1 Pair_17_9 pair_17_9_checked
certify_pair_chunk 17 10 1 Pair_17_10 pair_17_10_checked
certify_pair_chunk 17 11 1 Pair_17_11 pair_17_11_checked
certify_pair_chunk 17 12 1 Pair_17_12 pair_17_12_checked
certify_pair_chunk 17 13 1 Pair_17_13 pair_17_13_checked
certify_pair_chunk 17 14 1 Pair_17_14 pair_17_14_checked
certify_pair_chunk 17 15 1 Pair_17_15 pair_17_15_checked
certify_pair_chunk 17 16 1 Pair_17_16 pair_17_16_checked
certify_pair_chunk 17 17 1 Pair_17_17 pair_17_17_checked

noncomputable def Pair_17 : Nat := pair_sum_numeral% 17

noncomputable def chunks_17 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_17_0
  | 1 => Pair_17_1
  | 2 => Pair_17_2
  | 3 => Pair_17_3
  | 4 => Pair_17_4
  | 5 => Pair_17_5
  | 6 => Pair_17_6
  | 7 => Pair_17_7
  | 8 => Pair_17_8
  | 9 => Pair_17_9
  | 10 => Pair_17_10
  | 11 => Pair_17_11
  | 12 => Pair_17_12
  | 13 => Pair_17_13
  | 14 => Pair_17_14
  | 15 => Pair_17_15
  | 16 => Pair_17_16
  | 17 => Pair_17_17
  | _ => 0

theorem chunks_17_checked (t : Nat) (ht : t ≤ 17) :
    pairChunkWith cachedCoordinate 17 t 1 = chunks_17 t := by
  interval_cases t
  · exact pair_17_0_checked
  · exact pair_17_1_checked
  · exact pair_17_2_checked
  · exact pair_17_3_checked
  · exact pair_17_4_checked
  · exact pair_17_5_checked
  · exact pair_17_6_checked
  · exact pair_17_7_checked
  · exact pair_17_8_checked
  · exact pair_17_9_checked
  · exact pair_17_10_checked
  · exact pair_17_11_checked
  · exact pair_17_12_checked
  · exact pair_17_13_checked
  · exact pair_17_14_checked
  · exact pair_17_15_checked
  · exact pair_17_16_checked
  · exact pair_17_17_checked

theorem pair_17_checked : pairFirst 17 = Pair_17 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_17 17
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_17_checked
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

noncomputable def Forest_17 : Nat := forest_numeral% 17

theorem forest_17_checked : forest 17=Forest_17 := by
  exact (forest_eq_of_inputs 17 Pair_17 Coordinate_128_17
    pair_17_checked coordinate_128_17_checked).trans (by decide +kernel)

theorem convolution_17_checked : convolutionDots 17 (forest 17)=certifiedPayoff 17 := by
  have hf := congrArg (convolutionDots 17) forest_17_checked
  exact hf.trans ((convolutionDots_eq_of_fees 17 Forest_17 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false
certify_pair_chunk 18 0 1 Pair_18_0 pair_18_0_checked
certify_pair_chunk 18 1 1 Pair_18_1 pair_18_1_checked
certify_pair_chunk 18 2 1 Pair_18_2 pair_18_2_checked
certify_pair_chunk 18 3 1 Pair_18_3 pair_18_3_checked
certify_pair_chunk 18 4 1 Pair_18_4 pair_18_4_checked
certify_pair_chunk 18 5 1 Pair_18_5 pair_18_5_checked
certify_pair_chunk 18 6 1 Pair_18_6 pair_18_6_checked
certify_pair_chunk 18 7 1 Pair_18_7 pair_18_7_checked
certify_pair_chunk 18 8 1 Pair_18_8 pair_18_8_checked
certify_pair_chunk 18 9 1 Pair_18_9 pair_18_9_checked
certify_pair_chunk 18 10 1 Pair_18_10 pair_18_10_checked
certify_pair_chunk 18 11 1 Pair_18_11 pair_18_11_checked
certify_pair_chunk 18 12 1 Pair_18_12 pair_18_12_checked
certify_pair_chunk 18 13 1 Pair_18_13 pair_18_13_checked
certify_pair_chunk 18 14 1 Pair_18_14 pair_18_14_checked
certify_pair_chunk 18 15 1 Pair_18_15 pair_18_15_checked
certify_pair_chunk 18 16 1 Pair_18_16 pair_18_16_checked
certify_pair_chunk 18 17 1 Pair_18_17 pair_18_17_checked
certify_pair_chunk 18 18 1 Pair_18_18 pair_18_18_checked

noncomputable def Pair_18 : Nat := pair_sum_numeral% 18

noncomputable def chunks_18 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_18_0
  | 1 => Pair_18_1
  | 2 => Pair_18_2
  | 3 => Pair_18_3
  | 4 => Pair_18_4
  | 5 => Pair_18_5
  | 6 => Pair_18_6
  | 7 => Pair_18_7
  | 8 => Pair_18_8
  | 9 => Pair_18_9
  | 10 => Pair_18_10
  | 11 => Pair_18_11
  | 12 => Pair_18_12
  | 13 => Pair_18_13
  | 14 => Pair_18_14
  | 15 => Pair_18_15
  | 16 => Pair_18_16
  | 17 => Pair_18_17
  | 18 => Pair_18_18
  | _ => 0

theorem chunks_18_checked (t : Nat) (ht : t ≤ 18) :
    pairChunkWith cachedCoordinate 18 t 1 = chunks_18 t := by
  interval_cases t
  · exact pair_18_0_checked
  · exact pair_18_1_checked
  · exact pair_18_2_checked
  · exact pair_18_3_checked
  · exact pair_18_4_checked
  · exact pair_18_5_checked
  · exact pair_18_6_checked
  · exact pair_18_7_checked
  · exact pair_18_8_checked
  · exact pair_18_9_checked
  · exact pair_18_10_checked
  · exact pair_18_11_checked
  · exact pair_18_12_checked
  · exact pair_18_13_checked
  · exact pair_18_14_checked
  · exact pair_18_15_checked
  · exact pair_18_16_checked
  · exact pair_18_17_checked
  · exact pair_18_18_checked

theorem pair_18_checked : pairFirst 18 = Pair_18 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_18 18
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_18_checked
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

noncomputable def Forest_18 : Nat := forest_numeral% 18

theorem forest_18_checked : forest 18=Forest_18 := by
  exact (forest_eq_of_inputs 18 Pair_18 Coordinate_128_18
    pair_18_checked coordinate_128_18_checked).trans (by decide +kernel)

theorem convolution_18_checked : convolutionDots 18 (forest 18)=certifiedPayoff 18 := by
  have hf := congrArg (convolutionDots 18) forest_18_checked
  exact hf.trans ((convolutionDots_eq_of_fees 18 Forest_18 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
end ClaudeWCT.Numerics.SharedGeneratedForest
