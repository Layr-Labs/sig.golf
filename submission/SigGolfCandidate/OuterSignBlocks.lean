import SigGolfCandidate.OuterNodeHelper
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def saveCode : List (BitVec 32) := [0x48603023,0x48703423]
sym_block save := symRun {noAlias:=true} saveCode (pcOf 26156) 40
def dispatchCode : List (BitVec 32) := [0x50337,0x30030313,0xa651663,0x7b40006f,0x3539393,0xa039063,0x1053383,0x3039393,0x3b3d393,0x1700313,0x863e663,0x1853303,0x433313,0x8030063,0x1700313,0x13,0x2638863]
def b_startCode : List (BitVec 32) := [0x313,0x2053423]
sym_block b_start := symRun {noAlias:=true} b_startCode (pcOf 26175) 40
def b_preCode : List (BitVec 32) := [0x2653023,0x73]
sym_block b_pre := symRun {noAlias:=true} b_preCode (pcOf 26177) 40
def b_checkCode : List (BitVec 32) := [0x1863383,0x3b3d393,0x4038863]
sym_block b_check := symRun {noAlias:=true} b_checkCode (pcOf 26179) 40
def b_retryCode : List (BitVec 32) := [0x130313,0xc35393,0xfe0382e3]
sym_block b_retry := symRun {noAlias:=true} b_retryCode (pcOf 26182) 40
def b_exhaustCode : List (BitVec 32) := [0x4000063]
sym_block b_exhaust := symRun {noAlias:=true} b_exhaustCode (pcOf 26185) 40
def c_startCode : List (BitVec 32) := [0x313,0x2053423]
sym_block c_start := symRun {noAlias:=true} c_startCode (pcOf 26186) 40
def c_preCode : List (BitVec 32) := [0x2653023,0x73]
sym_block c_pre := symRun {noAlias:=true} c_preCode (pcOf 26188) 40
def c_checkCode : List (BitVec 32) := [0x1853383,0x13f393,0x439393,0x407603b3,0x183b383,0x3c3d393,0x38a63]
sym_block c_check := symRun {noAlias:=true} c_checkCode (pcOf 26190) 40
def c_retryCode : List (BitVec 32) := [0x130313,0xc35393,0xfc038ae3]
sym_block c_retry := symRun {noAlias:=true} c_retryCode (pcOf 26197) 40
def c_exhaustCode : List (BitVec 32) := [0x263]
sym_block c_exhaust := symRun {noAlias:=true} c_exhaustCode (pcOf 26200) 40
def cleanupCode : List (BitVec 32) := [0x2053023,0x463,0x73,0x48003303,0x48803383,0xa74ff06f]
sym_block cleanup := symRun {noAlias:=true} cleanupCode (pcOf 26201) 40
def doneCode : List (BitVec 32) := [0x48003303,0x48803383,0xa74ff06f]
sym_block done := symRun {noAlias:=true} doneCode (pcOf 26204) 40

def addrCode : List (BitVec 32) := dispatchCode.take 3
sym_block addr := symRun {noAlias:=true} addrCode (pcOf 26158) 40
/-- C31: the hook tests the low 11 bits (zero for a two-word FTS node word), then the coordinate field
(bits 11..15 = 31 - coordinate, at least 23), then the heap label (< 4), then the singleton (field 23). -/
def lowCode : List (BitVec 32) := (dispatchCode.drop 3).take 3
sym_block low := symRun {noAlias:=true} lowCode (pcOf 26161) 40
def fieldCode : List (BitVec 32) := (dispatchCode.drop 6).take 5
sym_block field := symRun {noAlias:=true} fieldCode (pcOf 26164) 40
def heapCode : List (BitVec 32) := (dispatchCode.drop 11).take 3
sym_block heap := symRun {noAlias:=true} heapCode (pcOf 26169) 40
def coordCode : List (BitVec 32) := dispatchCode.drop 14
sym_block coord := symRun {noAlias:=true} coordCode (pcOf 26172) 40

/-- C46: the hook word 26161 (`jal zero,26654`) enters the classifier appended at the end of the sign image (the old
tests 26162..26174 are dead). -/
def hookCode : List (BitVec 32) := (dispatchCode.drop 3).take 1
sym_block hook := symRun {noAlias:=true} hookCode (pcOf 26161) 40
/-- C46: the outer-root classifier (sign words 26654..26671): the heap label is `3` or `0xf1b02`, the header word has
zero low 11 bits and a coordinate field (bits 11..15 = 31 - coordinate / 2) of at least 27; field 27 (coordinate 8)
takes the `c` search (26186), the others the `b` search (26175); a reject jumps to the plain hash (26203). -/
def clsCode : List (BitVec 32) := [0x1853303,0xffd30313,0x30863,0xf23b7,0xaff38393,0x2731663,0x1053383,0x3539393,
  0x2039063,0x1053383,0x3039393,0x3b3d393,0x1b00313,0x63e663,0x638663,0x849ff06f,0x8b5ff06f,0x86dff06f]
def clsACode : List (BitVec 32) := clsCode.take 3
sym_block clsA := symRun {noAlias:=true} clsACode (pcOf 26654) 40
def clsBCode : List (BitVec 32) := (clsCode.drop 3).take 3
sym_block clsB := symRun {noAlias:=true} clsBCode (pcOf 26657) 40
def clsCCode : List (BitVec 32) := (clsCode.drop 6).take 3
sym_block clsC := symRun {noAlias:=true} clsCCode (pcOf 26660) 40
def clsDCode : List (BitVec 32) := (clsCode.drop 9).take 5
sym_block clsD := symRun {noAlias:=true} clsDCode (pcOf 26663) 40
def clsECode : List (BitVec 32) := (clsCode.drop 14).take 1
sym_block clsE := symRun {noAlias:=true} clsECode (pcOf 26668) 40
def clsBJCode : List (BitVec 32) := (clsCode.drop 15).take 1
sym_block clsBJ := symRun {noAlias:=true} clsBJCode (pcOf 26669) 40
def clsRJCode : List (BitVec 32) := (clsCode.drop 16).take 1
sym_block clsRJ := symRun {noAlias:=true} clsRJCode (pcOf 26670) 40
def clsCJCode : List (BitVec 32) := clsCode.drop 17
sym_block clsCJ := symRun {noAlias:=true} clsCJCode (pcOf 26671) 40

#print cleanup.res
#print done.res
#print hook.res
#print clsA.res
#print clsB.res
#print clsC.res
#print clsD.res
#print clsE.res
#print clsBJ.res
#print clsRJ.res
#print clsCJ.res
end OuterSignBlocks
