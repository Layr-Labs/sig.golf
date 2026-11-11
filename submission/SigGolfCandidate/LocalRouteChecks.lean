import SigGolfCandidate.Merge044
import SigGolfCandidate.LocalRouteNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
namespace ClaudeWCT.Numerics.LocalRoute.Checks
open ClaudeWCT.WCT9
def row1 (mask : Nat) : Array Nat := Tables.rows1[mask]?.getD #[]
def row2 (mask : Nat) : Array Nat := Tables.rows2[mask]?.getD #[]
def row3 (mask : Nat) : Array Nat := Tables.rows3[mask]?.getD #[]
theorem checks1 : (List.range 4).all (fun mask => (List.range 55).all (fun r => ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.lowerDen (ClaudeWCT.Numerics.CanonicalCompression.stageHistogram 1) (CanonicalPolicy.threshold 1 r) r (row2 mask) ((row1 mask)[r]?.getD 0))) = true := by decide +kernel

theorem check1_at (mask r : Nat) (hm : mask<4) (hr : r<55) :
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.lowerDen (ClaudeWCT.Numerics.CanonicalCompression.stageHistogram 1) (CanonicalPolicy.threshold 1 r) r (row2 mask) ((row1 mask)[r]?.getD 0) = true := by
  have h := (List.all_eq_true.mp checks1) mask (List.mem_range.mpr hm)
  exact (List.all_eq_true.mp h) r (List.mem_range.mpr hr)
#print axioms check1_at
theorem checks2 : (List.range 2).all (fun mask => (List.range 41).all (fun r => ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.lowerDen (ClaudeWCT.Numerics.CanonicalCompression.stageHistogram 2) (CanonicalPolicy.threshold 2 r) r (row3 mask) ((row2 mask)[r]?.getD 0))) = true := by decide +kernel

theorem check2_at (mask r : Nat) (hm : mask<2) (hr : r<41) :
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.lowerDen (ClaudeWCT.Numerics.CanonicalCompression.stageHistogram 2) (CanonicalPolicy.threshold 2 r) r (row3 mask) ((row2 mask)[r]?.getD 0) = true := by
  have h := (List.all_eq_true.mp checks2) mask (List.mem_range.mpr hm)
  exact (List.all_eq_true.mp h) r (List.mem_range.mpr hr)
#print axioms check2_at
theorem checks3 : (List.range 1).all (fun mask => (List.range 23).all (fun r => ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.lowerDen (ClaudeWCT.Numerics.CanonicalCompression.stageHistogram 3) (CanonicalPolicy.threshold 3 r) r (#[ClaudeWCT.Numerics.CanonicalCompression.scale]) ((row3 mask)[r]?.getD 0))) = true := by decide +kernel

theorem check3_at (mask r : Nat) (hm : mask<1) (hr : r<23) :
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.lowerDen (ClaudeWCT.Numerics.CanonicalCompression.stageHistogram 3) (CanonicalPolicy.threshold 3 r) r (#[ClaudeWCT.Numerics.CanonicalCompression.scale]) ((row3 mask)[r]?.getD 0) = true := by
  have h := (List.all_eq_true.mp checks3) mask (List.mem_range.mpr hm)
  exact (List.all_eq_true.mp h) r (List.mem_range.mpr hr)
#print axioms check3_at
theorem root_checks : (List.range 3).all (fun p => (List.range 8).all (fun mask =>
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram (max 18 ((72+p)-54)) (72+p)
      (row1 mask) (Tables.initialAt (72+p) mask))) = true := by decide +kernel

theorem root_check_at (pool mask : Nat) (hlo : 72≤pool) (hhi : pool≤74) (hm : mask<8) :
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram (max 18 (pool-54)) pool
      (row1 mask) (Tables.initialAt pool mask) = true := by
  have h := (List.all_eq_true.mp root_checks) (pool-72) (List.mem_range.mpr (by omega))
  have he : 72+(pool-72)=pool := by omega
  simpa only [he] using (List.all_eq_true.mp h) mask (List.mem_range.mpr hm)
#print axioms root_check_at
end ClaudeWCT.Numerics.LocalRoute.Checks
