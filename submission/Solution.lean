import SigGolf
import SigGolfCandidate.Merge124

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5185 := rfl

theorem witness_bytes : submission.sizes.witness = 21756 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26016, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 4256 } := rfl

theorem certificate : SigGolf.Certificate submission 6958 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/- Z5R: C13R68 (R6 rho/hint codec, R1 ladder reward, skip-2 hint codec)
   plus #993 levers: Z5 pre/post-marker WOTS split (Merge112S0/SA/SB/S/T),
   cap 776, Route C gate 929, sign pool 71 (R0b), top floor 17.
   Claimed S = 5185, W = 21756, K = 131072, C = 6958;
   product = 36,077,230 (P1011T: 5185 x 6958; U123B: 5185 x 6959 = 36,082,415; A1R': 5185 x 6959; base U2 on R0b@929: 5185 x 6960 = 36,087,600). Independent acceptance remains required.
   U2 (port unit, #1009 shape on ASM1R/R0b): root credit pool 73 - pathSave (rootPool, 1:2:1 over 73/72/71), top floor
   max 18 (pool - 54) = 18/18/19 (#1009 top semantics: topFloor 18, floor-2 16, nominal pool 72; R0b's top 17/71 undone),
   top window 2^21 (cap 3 * 2^20 at layer 3), verify bound 6877 -> 6875, after-good budget 5232 -> 5230.
   r58: CreditFloors 74 -> 73 (routePool = 73 - topPathSave); Merge055 signCode_86/89 lengths 160/78; D4 top clip 19.
   L836 (a): the 128 top copies drop `or s7,s7,t1` (x31 already carries the marker bit 12): top head 5 -> 4 steps,
   lCycA_4 5303 -> 5302, after-good budget 5230 -> 5229 (5302 - 73), verify bound 6875 -> 6874, C 6960 -> 6959.
   Merged with U1 (#1008 lower credit: AllRoute* + usedSave) and U3 (r47 L1 relayout, l1Table 2/66/60, pair-consistent
   plan for the leaf/2 expand pad tables): full moment 199974.58e-5 < 2 (AllRouteNumerics.full_moment_checked).
   D1 (#992 port): dedicated constant-one initializer removed (verify word 77) using
   byte/control-word reuse and consistent root-label translations (verify -1 cycle).
   NBZ5R NB: hint radix H88 (N = rho*88 + t < 2^129, A1 {9,14}, A2 {8,13,16,19}, A3 {7,10,12,14..21}) and
   FTS c0/c1 ground width 2: tail 24 -> 16 bits, S 5187 -> 5186 (P4 provisional; T2 lane numbers to drop in).
   NBZ5R VR8: FTS node-8 return inlined into 128 slot L3 heads, 4 constant loads hoisted (verify -1 cycle;
   expand keeps the pre-VR8 bank copies expandSharedCode_921..952).
   S5185 POOL70: sign pool 71 -> 70 (top 17), f2 <= 18 (n2 40), A2 {7,12,15,18}; verify bound 6885 -> 6886.
   S5185 FTS16: heap-16..31 FTS ground slots (width 1, c0..c7): V 48 -> 56 bits, tail 16 -> 8 bits,
   S 5186 -> 5185 (A70 = P4c + VR8 + pool 70 + FTS16x8, claim 199889).
   A70Y4: PR #997 Y4 (L-hyper A', marker label words: -3 transitions + 1 L3 setup per run) on A70, the
   128 VR8 L3 slot heads included; verify bound 6886 -> 6884, C 6971 -> 6969.
   A70Y4Z6: PR #999 Z6 option F (marker-only label words, +513 folded into the label immediates, FTS node and
   leaf words biased by -2048 via one prologue addi; -4 ori +1 addi = -3 per run), the 128 VR8 L3 slot heads back
   to A70 geometry with a 3-word setup, NB Ta2 on the Y4 marker (fix2); verify bound 6884 -> 6881, C 6969 -> 6966.
   P1011T (PR #1011 pool+1 lever, EDITLIST v2): CreditFloors 73 -> 74 (routePool = 74 - topPathSave), after-good budget 5229 -> 5228,
   verify bound 6874 -> 6873, C 6959 -> 6958; FTS 27 -> 21 coefficient pairs; R52F K56 floor tables; FTS42 overflow (QueryOverflow40).
   Y6 (port of PR #1003 R-odd): odd FTS coordinates mask their child in place (child weight 2^26, instance field
   at bit 33; -4 dispatch srli +1 setup slli = -3 per run); verify bound 6881 -> 6878, C 6966 -> 6963. -/
