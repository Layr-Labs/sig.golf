import SigGolfCandidate.Merge042Head
set_option linter.all false

section
set_option Elab.async false
set_option maxRecDepth 100000
open Finset Polynomial
open Finset

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
noncomputable def Pair_15_8 : Nat := pair_copy% 15 7
theorem pair_15_8_checked : pairChunkWith cachedCoordinate 15 8 1 = Pair_15_8 :=
  (pairChunkWith_mirror cachedCoordinate 15 8 7 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_7_checked
noncomputable def Pair_15_9 : Nat := pair_copy% 15 6
theorem pair_15_9_checked : pairChunkWith cachedCoordinate 15 9 1 = Pair_15_9 :=
  (pairChunkWith_mirror cachedCoordinate 15 9 6 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_6_checked
noncomputable def Pair_15_10 : Nat := pair_copy% 15 5
theorem pair_15_10_checked : pairChunkWith cachedCoordinate 15 10 1 = Pair_15_10 :=
  (pairChunkWith_mirror cachedCoordinate 15 10 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_5_checked
noncomputable def Pair_15_11 : Nat := pair_copy% 15 4
theorem pair_15_11_checked : pairChunkWith cachedCoordinate 15 11 1 = Pair_15_11 :=
  (pairChunkWith_mirror cachedCoordinate 15 11 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_4_checked
noncomputable def Pair_15_12 : Nat := pair_copy% 15 3
theorem pair_15_12_checked : pairChunkWith cachedCoordinate 15 12 1 = Pair_15_12 :=
  (pairChunkWith_mirror cachedCoordinate 15 12 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_3_checked
noncomputable def Pair_15_13 : Nat := pair_copy% 15 2
theorem pair_15_13_checked : pairChunkWith cachedCoordinate 15 13 1 = Pair_15_13 :=
  (pairChunkWith_mirror cachedCoordinate 15 13 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_2_checked
noncomputable def Pair_15_14 : Nat := pair_copy% 15 1
theorem pair_15_14_checked : pairChunkWith cachedCoordinate 15 14 1 = Pair_15_14 :=
  (pairChunkWith_mirror cachedCoordinate 15 14 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_15_1_checked
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
    pair_15_checked coordinate_128_15_checked).trans (by rw [spread_eq_fast]; decide +kernel)



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
noncomputable def Pair_16_9 : Nat := pair_copy% 16 7
theorem pair_16_9_checked : pairChunkWith cachedCoordinate 16 9 1 = Pair_16_9 :=
  (pairChunkWith_mirror cachedCoordinate 16 9 7 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_7_checked
noncomputable def Pair_16_10 : Nat := pair_copy% 16 6
theorem pair_16_10_checked : pairChunkWith cachedCoordinate 16 10 1 = Pair_16_10 :=
  (pairChunkWith_mirror cachedCoordinate 16 10 6 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_6_checked
noncomputable def Pair_16_11 : Nat := pair_copy% 16 5
theorem pair_16_11_checked : pairChunkWith cachedCoordinate 16 11 1 = Pair_16_11 :=
  (pairChunkWith_mirror cachedCoordinate 16 11 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_5_checked
noncomputable def Pair_16_12 : Nat := pair_copy% 16 4
theorem pair_16_12_checked : pairChunkWith cachedCoordinate 16 12 1 = Pair_16_12 :=
  (pairChunkWith_mirror cachedCoordinate 16 12 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_4_checked
noncomputable def Pair_16_13 : Nat := pair_copy% 16 3
theorem pair_16_13_checked : pairChunkWith cachedCoordinate 16 13 1 = Pair_16_13 :=
  (pairChunkWith_mirror cachedCoordinate 16 13 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_3_checked
noncomputable def Pair_16_14 : Nat := pair_copy% 16 2
theorem pair_16_14_checked : pairChunkWith cachedCoordinate 16 14 1 = Pair_16_14 :=
  (pairChunkWith_mirror cachedCoordinate 16 14 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_2_checked
noncomputable def Pair_16_15 : Nat := pair_copy% 16 1
theorem pair_16_15_checked : pairChunkWith cachedCoordinate 16 15 1 = Pair_16_15 :=
  (pairChunkWith_mirror cachedCoordinate 16 15 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_16_1_checked
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
    pair_16_checked coordinate_128_16_checked).trans (by rw [spread_eq_fast]; decide +kernel)



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
noncomputable def Pair_17_9 : Nat := pair_copy% 17 8
theorem pair_17_9_checked : pairChunkWith cachedCoordinate 17 9 1 = Pair_17_9 :=
  (pairChunkWith_mirror cachedCoordinate 17 9 8 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_8_checked
noncomputable def Pair_17_10 : Nat := pair_copy% 17 7
theorem pair_17_10_checked : pairChunkWith cachedCoordinate 17 10 1 = Pair_17_10 :=
  (pairChunkWith_mirror cachedCoordinate 17 10 7 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_7_checked
noncomputable def Pair_17_11 : Nat := pair_copy% 17 6
theorem pair_17_11_checked : pairChunkWith cachedCoordinate 17 11 1 = Pair_17_11 :=
  (pairChunkWith_mirror cachedCoordinate 17 11 6 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_6_checked
noncomputable def Pair_17_12 : Nat := pair_copy% 17 5
theorem pair_17_12_checked : pairChunkWith cachedCoordinate 17 12 1 = Pair_17_12 :=
  (pairChunkWith_mirror cachedCoordinate 17 12 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_5_checked
noncomputable def Pair_17_13 : Nat := pair_copy% 17 4
theorem pair_17_13_checked : pairChunkWith cachedCoordinate 17 13 1 = Pair_17_13 :=
  (pairChunkWith_mirror cachedCoordinate 17 13 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_4_checked
noncomputable def Pair_17_14 : Nat := pair_copy% 17 3
theorem pair_17_14_checked : pairChunkWith cachedCoordinate 17 14 1 = Pair_17_14 :=
  (pairChunkWith_mirror cachedCoordinate 17 14 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_3_checked
noncomputable def Pair_17_15 : Nat := pair_copy% 17 2
theorem pair_17_15_checked : pairChunkWith cachedCoordinate 17 15 1 = Pair_17_15 :=
  (pairChunkWith_mirror cachedCoordinate 17 15 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_2_checked
noncomputable def Pair_17_16 : Nat := pair_copy% 17 1
theorem pair_17_16_checked : pairChunkWith cachedCoordinate 17 16 1 = Pair_17_16 :=
  (pairChunkWith_mirror cachedCoordinate 17 16 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_17_1_checked
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
    pair_17_checked coordinate_128_17_checked).trans (by rw [spread_eq_fast]; decide +kernel)



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
noncomputable def Pair_18_10 : Nat := pair_copy% 18 8
theorem pair_18_10_checked : pairChunkWith cachedCoordinate 18 10 1 = Pair_18_10 :=
  (pairChunkWith_mirror cachedCoordinate 18 10 8 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_8_checked
noncomputable def Pair_18_11 : Nat := pair_copy% 18 7
theorem pair_18_11_checked : pairChunkWith cachedCoordinate 18 11 1 = Pair_18_11 :=
  (pairChunkWith_mirror cachedCoordinate 18 11 7 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_7_checked
noncomputable def Pair_18_12 : Nat := pair_copy% 18 6
theorem pair_18_12_checked : pairChunkWith cachedCoordinate 18 12 1 = Pair_18_12 :=
  (pairChunkWith_mirror cachedCoordinate 18 12 6 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_6_checked
noncomputable def Pair_18_13 : Nat := pair_copy% 18 5
theorem pair_18_13_checked : pairChunkWith cachedCoordinate 18 13 1 = Pair_18_13 :=
  (pairChunkWith_mirror cachedCoordinate 18 13 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_5_checked
noncomputable def Pair_18_14 : Nat := pair_copy% 18 4
theorem pair_18_14_checked : pairChunkWith cachedCoordinate 18 14 1 = Pair_18_14 :=
  (pairChunkWith_mirror cachedCoordinate 18 14 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_4_checked
noncomputable def Pair_18_15 : Nat := pair_copy% 18 3
theorem pair_18_15_checked : pairChunkWith cachedCoordinate 18 15 1 = Pair_18_15 :=
  (pairChunkWith_mirror cachedCoordinate 18 15 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_3_checked
noncomputable def Pair_18_16 : Nat := pair_copy% 18 2
theorem pair_18_16_checked : pairChunkWith cachedCoordinate 18 16 1 = Pair_18_16 :=
  (pairChunkWith_mirror cachedCoordinate 18 16 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_2_checked
noncomputable def Pair_18_17 : Nat := pair_copy% 18 1
theorem pair_18_17_checked : pairChunkWith cachedCoordinate 18 17 1 = Pair_18_17 :=
  (pairChunkWith_mirror cachedCoordinate 18 17 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_18_1_checked
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
    pair_18_checked coordinate_128_18_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

end
