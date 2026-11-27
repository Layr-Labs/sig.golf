import SigGolfCandidate.Merge011
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace SigGolfCandidate.Route16Guard
open ClaudeWCT.WCT9
/-- C39: the top floor `max 16 (pool-57)` for the root pool `75 - topPathSave leaf` (18/17/16/16 for saves 0..3). -/
def floor (leaf : Nat) : Nat := max 16 (18-CanonicalPolicy.topPathSave leaf)
theorem floor_eq_threshold (leaf : Nat) : floor leaf = max 16 ((75-CanonicalPolicy.topPathSave leaf)-57) := by
  have h := CanonicalPolicy.topPathSave_le_three leaf
  unfold floor;omega
/-- C39 `save_code(s2,t4,t5)`: 41 straight-line words computing `topPathSave leaf` of `x18` into `x29` with `x30` as
scratch (`d = leaf & 63`; two line-A mask bits of row `d` added at bit 6; `64*saveA + (leaf>>6 & 63)`; the line-B mask
bit of row `leaf>>6 & 63` added to `saveA`; the three 64-bit masks are built in-register). -/
def saveWords : List (BitVec 32) := [0x3f97e93,0x7e7f0f37,0xffef0f13,0xbf1f13,0x7fff0f13,0xbf1f13,0x7fff0f13,
  0xaf1f13,0x3fef0f13,0x1df5f33,0x1f7f13,0x6f1f13,0x1ee8eb3,0x6f37,0x666f0f13,0xbf1f13,0x333f0f13,0xbf1f13,0x199f0f13,
  0xaf1f13,0x260f0f13,0x1df5f33,0x1f7f13,0x6f1f13,0x1ee8eb3,0xfc0efe93,0x695f13,0x3ff7f13,0x1ee8eb3,0x6e66ff37,
  0xeeef0f13,0xbf1f13,0x333f0f13,0xbf1f13,0x3bbf0f13,0xaf1f13,0x2eef0f13,0x1df5f33,0x1f7f13,0x6ede93,0x1ee8eb3]
/-- `addi t5,zero,18; sub t4,t5,t4; sltiu t5,t4,16; add t4,t4,t5`: `x29 = max 16 (18 - x29)` for `x29 ≤ 3`. -/
def floorWords : List (BitVec 32) := [0x1200f13,0x41df0eb3,0x10ebf13,0x1ee8eb3]
end SigGolfCandidate.Route16Guard
