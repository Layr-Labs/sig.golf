import SigGolfCandidate.OuterGroundNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
namespace OuterRootNumerics
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.LocalRoute

def initial72 (mask : Nat) : Nat :=
  match mask with
  | 0 => OuterGroundNumerics.initial72_0
  | 1 => OuterGroundNumerics.initial72_1
  | 2 => OuterGroundNumerics.initial72_2
  | 3 => OuterGroundNumerics.initial72_3
  | 4 => OuterGroundNumerics.initial72_4
  | 5 => OuterGroundNumerics.initial72_5
  | 6 => OuterGroundNumerics.initial72_6
  | _ => OuterGroundNumerics.initial72_7

def initialAt (pool mask : Nat) : Nat := if pool=72 then initial72 mask else Tables.initialAt pool mask

theorem root_checks72 : (List.range 8).all (fun mask => ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.topDen
    ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 72 (Checks.row1 mask) (initial72 mask))=true := by decide +kernel

theorem root_check_at (pool mask : Nat) (hlo : 72≤pool) (hhi : pool≤74) (hm : mask<8) :
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram (max 18 (pool-57)) pool
      (Checks.row1 mask) (initialAt pool mask)=true := by
  by_cases h : pool=72
  · subst pool
    rw [show (max 18 (72-57) : Nat)=18 by decide]
    simpa only [initialAt,↓reduceIte] using (List.all_eq_true.mp root_checks72) mask (List.mem_range.mpr hm)
  · simpa only [initialAt,if_neg h] using Checks.root_check_at pool mask (by omega) (by omega) hm

#print axioms root_check_at
end OuterRootNumerics
