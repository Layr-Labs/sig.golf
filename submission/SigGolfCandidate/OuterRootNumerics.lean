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

def initialAt (pool mask : Nat) : Nat := Tables.initialAt pool mask

theorem root_checks72 : (List.range 8).all (fun mask => ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.topDen
    ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 16 72 (Checks.row1 mask) (initial72 mask))=true := by decide +kernel

theorem root_check_at (pool mask : Nat) (hlo : 71≤pool) (hhi : pool≤73) (hm : mask<8) :
    ClaudeWCT.Numerics.CanonicalCompression.recurrenceCheck ClaudeWCT.Numerics.CanonicalCompression.topDen ClaudeWCT.Numerics.TopZero.topAcceptedHistogram (max 16 (pool-57)) pool
      (Checks.row1 mask) (initialAt pool mask)=true :=
  Checks.root_check_at pool mask hlo hhi hm

#print axioms root_check_at
end OuterRootNumerics
