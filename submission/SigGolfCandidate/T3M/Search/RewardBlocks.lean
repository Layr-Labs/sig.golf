import SigGolfCandidate.T3M.Search.Basic
import SigGolfCandidate.T3M.Search.TopWindow
import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Images.Slices
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace SigGolfCandidate.T3M.Search.Reward
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false
set_option linter.unusedSimpArgs false

/-- The frozen producer's reward routines share this entry and byte layout. -/
def base (b : Nat) (top : Bool) : Nat :=
  if b = 354 then (if top then 43352 else 42947) else (if top then 21343 else 20938)
def maximum (top : Bool) (i : Nat) : Nat := if top && decide (i < 51) then 4 else 7
def direct (top : Bool) (i : Nat) : Bool := decide (i = 0) || (!top && decide (i = 1))
theorem eq_small (d m : Nat) (hd : d < 8) (hm : m < 8) (hm0 : 0 < m) :
    (if ((BitVec.ofNat 64 d) + BitVec.ofNat 64 (2^64-m)).ult 1#64 then 1#64 else 0#64) =
      BitVec.ofNat 64 (if d = m then 1 else 0) := by
  interval_cases d <;> interval_cases m <;> decide

open SigGolfCandidate.T3 (Layer Digest)
open ClaudeWCT.WCT9

def credit (top : Bool) (ds : List Nat) (i : Nat) : Nat :=
  if ds.getD i 0 = maximum top i-1 then 1 else 0
def saved (top : Bool) (ds : List Nat) (i : Nat) : Prop :=
  ds.getD i 0 = maximum top i ∧
    (direct top i = true ∨ (i%3 ≠ 0 ∧ ds.getD (i-1) 0 = maximum top (i-1)))
instance (top : Bool) (ds : List Nat) (i : Nat) : Decidable (saved top ds i) := by
  unfold saved; infer_instance
def reward (top : Bool) (ds : List Nat) (i : Nat) : Nat :=
  credit top ds i + 4 * (if saved top ds i then 1 else 0)
theorem maximum_bounds (top : Bool) (i : Nat) : 2 ≤ maximum top i ∧ maximum top i < 8 := by
  unfold maximum; split <;> omega

/-- Lower layers only (campaign R6: the top layer is scored by the R6 kernel, `R6.trial`). -/
theorem maximum_layer (lay : Layer) (hl : lay ≠ 0) (i : Nat) : maximum (decide (lay=0)) i = T3.maxDigit lay i := by
  simp [maximum, T3.maxDigit, hl]

theorem saved_layer (lay : Layer) (hl : lay ≠ 0) (ds : List Nat) (i : Nat) :
    saved (decide (lay=0)) ds i ↔ safeZeroCopy lay ds i := by
  simp only [saved, maximum_layer lay hl, safeZeroCopy]
  have hdirect : direct (decide (lay=0)) i = true ↔ i=0 ∨ (lay≠0 ∧ i=1) := by
    simp [direct]
  rw [hdirect]
  constructor
  · rintro ⟨ha, (h0 | h1) | ⟨hm, hp⟩⟩
    · exact ⟨ha, Or.inl h0⟩
    · exact ⟨ha, Or.inr (Or.inl h1)⟩
    · exact ⟨ha, Or.inr (Or.inr ⟨by omega, hm, hp⟩)⟩
  · rintro ⟨ha, h0 | h1 | ⟨_, hm, hp⟩⟩
    · exact ⟨ha, Or.inl (Or.inl h0)⟩
    · exact ⟨ha, Or.inl (Or.inr h1)⟩
    · exact ⟨ha, Or.inr ⟨hm, hp⟩⟩

theorem credit_layer (lay : Layer) (hl : lay ≠ 0) (ds : List Nat) (i : Nat) :
    ds.getD i 0 = maximum (decide (lay=0)) i-1 ↔ ds.getD i 0+1 = T3.maxDigit lay i := by
  rw [← maximum_layer lay hl i]
  have := (maximum_bounds (decide (lay=0)) i).1
  omega

theorem reward_sum_counts (top : Bool) (ds : List Nat) (is : List Nat) :
    (is.map (reward top ds)).sum =
      (is.filter fun i => decide (ds.getD i 0 = maximum top i-1)).length +
      4 * (is.filter fun i => decide (saved top ds i)).length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases hc : ds.getD i 0 = maximum top i-1 <;>
      by_cases hs : saved top ds i <;>
      simp only [reward, credit, List.map_cons, List.sum_cons, List.filter_cons,
        hc, hs, decide_true, decide_false, if_true, if_false, Bool.false_eq_true,
        List.length_cons, ih] <;> omega

/-- Packed reward lookup data, before digit unpacking. -/
def tripleScore (m a b c : Nat) : Nat :=
  (if a=m-1 then 1 else 0) + (if b=m-1 then 1 else 0) + (if c=m-1 then 1 else 0) +
  4*((if a=m ∧ b=m then 1 else 0)+(if b=m ∧ c=m then 1 else 0))
def lowerLookup (first : Bool) (r : Nat) : Nat :=
  tripleScore 7 (r%8) (r/8%8) (r/64%8) +
  (if first then 4*((if r%8=7 then 1 else 0)+(if r/8%8=7 ∧ r%8≠7 then 1 else 0)) else 0)
def topLookup (kind r : Nat) : Nat :=
  if r<125 then tripleScore 4 (r%5) (r/5%5) (r/25%5) +
    (if kind<2 then 1-(if r%5+r/5%5+r/25%5<3 then 1 else 0) else 0) +
    (if kind=0 ∧ r%5=4 then 4 else 0)
  else 0
def tailLookup (r : Nat) : Nat := tripleScore 7 (r/8%8) (r/64%8) (r%8)
def rewardTableByte (i : Nat) : BitVec 8 := BitVec.ofNat 8 <|
  if i<1536 then lowerLookup true (i-1024)
  else if i<2048 then lowerLookup false (i-1536)
  else if i<2176 then topLookup 0 (i-2048)
  else if i<2304 then topLookup 1 (i-2176)
  else if i<2432 then topLookup 2 (i-2304)
  else tailLookup (i-2432)
def RewardTablesOK (s : MachineState) : Prop :=
  ∀ i, 1024 ≤ i → i < 2944 → s.getByte (BitVec.ofNat 64 (TOP_DATA+i)) = rewardTableByte i
theorem RewardTablesOK.frame {s t : MachineState} {W : Nat → Prop} (h : RewardTablesOK s)
    (hf : Frame s t W) (hd : ∀ i, 1024 ≤ i → i < 2944 → ¬ W ((TOP_DATA+i)/8*8)) : RewardTablesOK t := by
  intro i hi hj
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi hj)).trans (h i hi hj)
/-- Campaign R6: the lower reward tables only (TOP_DATA + 1024..2047); 2048.. is the R6 block in the sign image. -/
def LowerTablesOK (s : MachineState) : Prop :=
  ∀ i, 1024 ≤ i → i < 2048 → s.getByte (BitVec.ofNat 64 (TOP_DATA+i)) = rewardTableByte i
theorem LowerTablesOK.frame {s t : MachineState} {W : Nat → Prop} (h : LowerTablesOK s)
    (hf : Frame s t W) (hd : ∀ i, 1024 ≤ i → i < 2048 → ¬ W ((TOP_DATA+i)/8*8)) : LowerTablesOK t := by
  intro i hi hj
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi hj)).trans (h i hi hj)
theorem RewardTablesOK.lower {s : MachineState} (h : RewardTablesOK s) : LowerTablesOK s :=
  fun i hi hj => h i hi (by omega)
instance {s : MachineState} : Coe (RewardTablesOK s) (LowerTablesOK s) := ⟨RewardTablesOK.lower⟩
def fastSignLower : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x1ff57e13,0xbe0e33,0xc00e4e83,0x1da0a33,0x935513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1235513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2435513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3635513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x93d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x123d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x243d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x363d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33,0xfff40e13,0x1e3e13,0x9e0e13,0x1ca6463,0xed4ec06f,0xf5cec06f]
def fastSignTop : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x7f57e13,0xbe0e33,0xe4e83,0x1da0a33,0x735513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xe35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1535513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1c35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2335513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2a35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3135513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3835513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3f35513,0x139e13,0x1c56533,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x63d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xd3d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x143d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1b3d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x223d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x293d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x303d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x373d513,0x1ff57e13,0xbe0e33,0x180e4e83,0x1da0a33,0x2100e13,0x1ca6463,0x814ec06f,0x8c8ec06f]
def fastExpandLower : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x1ff57e13,0xbe0e33,0xc00e4e83,0x1da0a33,0x935513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1235513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2435513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3635513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x93d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x123d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x243d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x363d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33,0xfff40e13,0x1e3e13,0x9e0e13,0x1ca6463,0xbfdd606f,0xc85d606f]
def fastExpandTop : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x7f57e13,0xbe0e33,0xe4e83,0x1da0a33,0x735513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xe35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1535513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1c35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2335513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2a35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3135513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3835513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3f35513,0x139e13,0x1c56533,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x63d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xd3d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x143d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1b3d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x223d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x293d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x303d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x373d513,0x1ff57e13,0xbe0e33,0x180e4e83,0x1da0a33,0x2100e13,0x1ca6463,0xd3cd606f,0xdf0d606f]

def fastCode (b : Nat) (top : Bool) : List (BitVec 32) :=
  if b=354 then (if top then fastExpandTop else fastExpandLower)
  else (if top then fastSignTop else fastSignLower)
def RewardAt (image : Image) (b : Nat) : Prop :=
  CodeAt image (pcOf (base b false)) (fastCode b false) ∧ CodeAt image (pcOf (base b true)) (fastCode b true)
theorem fastCode_length (b : Nat) (top : Bool) : (fastCode b top).length = if top then 99 else 83 := by
  by_cases hb : b=354 <;> cases top <;> simp [fastCode, hb, fastExpandTop, fastExpandLower, fastSignTop, fastSignLower]
namespace PackedTop
end PackedTop

namespace PackedTop
end PackedTop

namespace PackedTop
end PackedTop

open ClaudeWCT.WCT9
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace PackedTop
end PackedTop

namespace PackedTop
end PackedTop

end SigGolfCandidate.T3M.Search.Reward
