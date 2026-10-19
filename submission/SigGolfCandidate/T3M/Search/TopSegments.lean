import SigGolfCandidate.T3M.Search.KernelBlocks

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 16384
set_option linter.unusedVariables false
def topSeg265 : List (BitVec 32) := [0xffff37,200211]
def topSeg267 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg269 : List (BitVec 32) := [969859]
def topSeg270 : List (BitVec 32) := [8281619]
def topSeg271 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg273 : List (BitVec 32) := [970371]
def topSeg274 : List (BitVec 32) := [31231155,8281619]
def topSeg276 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg278 : List (BitVec 32) := [970371]
def topSeg279 : List (BitVec 32) := [31231155,8281619]
def topSeg281 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg283 : List (BitVec 32) := [970371]
def topSeg284 : List (BitVec 32) := [31231155,8281619]
def topSeg286 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg288 : List (BitVec 32) := [970371]
def topSeg289 : List (BitVec 32) := [31231155,8281619]
def topSeg291 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg293 : List (BitVec 32) := [970371]
def topSeg294 : List (BitVec 32) := [31231155,8281619]
def topSeg296 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg298 : List (BitVec 32) := [970371]
def topSeg299 : List (BitVec 32) := [31231155,8281619]
def topSeg301 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg303 : List (BitVec 32) := [970371]
def topSeg304 : List (BitVec 32) := [31231155,8281619]
def topSeg306 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg308 : List (BitVec 32) := [970371]
def topSeg309 : List (BitVec 32) := [31231155,8281619]
def topSeg311 : List (BitVec 32) := [1285779,30338611]
def topSeg313 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg315 : List (BitVec 32) := [970371]
def topSeg316 : List (BitVec 32) := [31231155,8281619]
def topSeg318 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg320 : List (BitVec 32) := [970371]
def topSeg321 : List (BitVec 32) := [31231155,8281619]
def topSeg323 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg325 : List (BitVec 32) := [970371]
def topSeg326 : List (BitVec 32) := [31231155,8281619]
def topSeg328 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg330 : List (BitVec 32) := [970371]
def topSeg331 : List (BitVec 32) := [31231155,8281619]
def topSeg333 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg335 : List (BitVec 32) := [970371]
def topSeg336 : List (BitVec 32) := [31231155,8281619]
def topSeg338 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg340 : List (BitVec 32) := [970371]
def topSeg341 : List (BitVec 32) := [31231155,8281619]
def topSeg343 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg345 : List (BitVec 32) := [970371]
def topSeg346 : List (BitVec 32) := [31231155,8281619]
def topSeg348 : List (BitVec 32) := [0x7fe7e93,32411315]
def topSeg350 : List (BitVec 32) := [970371]
def topSeg351 : List (BitVec 32) := [31231155,8281619]
def topSeg353 : List (BitVec 32) := [0x7e7e93,31231155,0x3e5e93,0x7efe93,31231155,0x3d3de93,31231155,0x411c8eb3,0xbe0e9ee3]
def topSeg362 (b : Nat) : List (BitVec 32) := (if b=354 then [0x2312906f] else [0x7591306f]) ++ [133815,0x420a8a93,0x80f0f13,0x7f37e13,3022355,32378419]
def topSeg369 : List (BitVec 32) := [945795]
def topSeg370 : List (BitVec 32) := [31096867]
def topSeg371 : List (BitVec 32) := [9363091]
def topSeg372 : List (BitVec 32) := [31096995]
def topSeg373 : List (BitVec 32) := [9363091]
def topSeg374 : List (BitVec 32) := [31097123]
def topSeg375 : List (BitVec 32) := [7557907,60005907,29582131,7590803,3836563,1706515,18497043,0xfc0e10e3]
def topSeg383 : List (BitVec 32) := [0x737e13]
def topSeg384 : List (BitVec 32) := [0x1ca8123]
def topSeg385 : List (BitVec 32) := [0x335313,0x737e13]
def topSeg387 : List (BitVec 32) := [0x1ca8023]
def topSeg388 : List (BitVec 32) := [0x335313,0x737e13]
def topSeg390 : List (BitVec 32) := [0x1ca80a3]
def topSeg391 (_b : Nat) : List (BitVec 32) := [0x8067]
/-- R6 expand (EXP image swap): offset 33 (`b + 425`) is `j 354`. -/
def topSeg392e : List (BitVec 32) := [197907,230803,1555,17828371,0x7f57e13,3022355,32378419,0x83e4e03,29754931,7689491,60136979,29713715,7722387,0xfffa0a13,0xfc0a1ce3,0x757e13,0xffae0e13,1981971,29754931,0x355513,0x757e13,0xffae0e13,1981971,29754931,0x355513,0xffa50e13,1981971,29754931,9846291,0xa0e1e63,2579,0xf11ff06f,0x960410e3,0x95dff06f,662654467,0x940e0ae3,663696131,672084867,0x8100c93,2579,0xeedff06f,1281555,66985491,29573939,1282963,2347923]
/-- R6 sign: `b + 430 li t3, 1` (d51 of the dummy word at T 153), `b + 431 j 1758` (the R6 unpacker). -/
def topSeg392s : List (BitVec 32) := [197907,230803,1555,17828371,0x7f57e13,3022355,32378419,0x83e4e03,29754931,7689491,60136979,29713715,7722387,0xfffa0a13,0xfc0a1ce3,0x757e13,0xffae0e13,1981971,29754931,0x355513,0x757e13,0xffae0e13,1981971,29754931,0x355513,0xffa50e13,1981971,29754931,9846291,0xa0e1e63,2579,0xf11ff06f,0x960410e3,0xffff37,662654467,0x940e0ae3,663696131,672084867,0x100e13,0x4410006f,0xeedff06f,1281555,66985491,29573939,1282963,2347923]
def topSeg392 (b : Nat) : List (BitVec 32) := if b = 354 then topSeg392e else topSeg392s
def topSegLayout (b : Nat) : Rv.Layout := [(0, topSeg265), (2, topSeg267), (4, topSeg269), (5, topSeg270), (6, topSeg271), (8, topSeg273), (9, topSeg274), (11, topSeg276), (13, topSeg278), (14, topSeg279), (16, topSeg281), (18, topSeg283), (19, topSeg284), (21, topSeg286), (23, topSeg288), (24, topSeg289), (26, topSeg291), (28, topSeg293), (29, topSeg294), (31, topSeg296), (33, topSeg298), (34, topSeg299), (36, topSeg301), (38, topSeg303), (39, topSeg304), (41, topSeg306), (43, topSeg308), (44, topSeg309), (46, topSeg311), (48, topSeg313), (50, topSeg315), (51, topSeg316), (53, topSeg318), (55, topSeg320), (56, topSeg321), (58, topSeg323), (60, topSeg325), (61, topSeg326), (63, topSeg328), (65, topSeg330), (66, topSeg331), (68, topSeg333), (70, topSeg335), (71, topSeg336), (73, topSeg338), (75, topSeg340), (76, topSeg341), (78, topSeg343), (80, topSeg345), (81, topSeg346), (83, topSeg348), (85, topSeg350), (86, topSeg351), (88, topSeg353), (97, topSeg362 b), (104, topSeg369), (105, topSeg370), (106, topSeg371), (107, topSeg372), (108, topSeg373), (109, topSeg374), (110, topSeg375), (118, topSeg383), (119, topSeg384), (120, topSeg385), (122, topSeg387), (123, topSeg388), (125, topSeg390), (126, topSeg391 b), (127, topSeg392 b)]
theorem topSegLayout_ok {b : Nat} (hb : b=354 ∨ b=543) : layoutOk 0 (topSegLayout b) = true := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem topSegLayout_code {b : Nat} (hb : b=354 ∨ b=543) : k_265 b = layoutCode (topSegLayout b) := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem codeAt_top392 {image : Image} {b : Nat} {rewardCondition : Prop} (h : KernAt image b rewardCondition) :
    CodeAt image (pcOf (b + 392)) (topSeg392 b) := by
  have hc := codeAt_k_265 h
  rw [topSegLayout_code h.2.1] at hc
  have hp := codeAt_sublayout hc (topSegLayout_ok h.2.1) (i := 69) (o := 127) (seg := topSeg392 b) (by rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hp
end SigGolfCandidate.T3M.Search
