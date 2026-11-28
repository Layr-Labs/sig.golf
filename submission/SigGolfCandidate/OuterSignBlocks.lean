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
def dispatchCode : List (BitVec 32) := [0x50337,0x30030313,0xa651663,0x13d0006f,0x3539393,0xa039063,0x1053383,0x3039393,0x3b3d393,0x1700313,0x863e663,0x1853303,0x433313,0x8030063,0x1700313,0x13,0x2638863]
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
def c_checkCode : List (BitVec 32) := [0x1853383,0x7033b3,0x439393,0x407603b3,0x183b383,0x3c3d393,0x38a63]
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

/-- C47: the hook word 26161 (`jal zero,26752`) enters the classifier appended at the end of the sign image (the old
tests 26162..26174 are dead). -/
def hookCode : List (BitVec 32) := (dispatchCode.drop 3).take 1
sym_block hook := symRun {noAlias:=true} hookCode (pcOf 26161) 40
/-- C47: the outer-root classifier (sign words 26752..26781). High word `0`: a zero-low-11 low word takes the `c`
search (coordinate 8, heap 2: `(a5', 0)`), else plain. High word nonzero: low word `929 * 2^50` takes the `c` search
(coordinate 8, heap 3: `(T4, a5')`); else the high word must be `0xf1b02` or `K = 0xe7404003` (odd coordinates'
heaps 2 / 3), the low word must have zero low 11 bits and a pair field (bits 11..15) of at least 28 for the `b`
search (26175); any reject jumps to the plain hash (26203). -/
def clsCode : List (BitVec 32) := [0x1853303,0x31a63,0x1053383,0x3539393,0x6038063,0xf58ff06f,0x1053383,0x3a1337,
  0x2631313,0x4638663,0x1853303,0xf23b7,0xb0238393,0x730c63,0x73a023b7,0x138393,0x139393,0x138393,0x2731663,0x1053383,
  0x3539393,0x2039063,0x1053383,0x3039393,0x3b3d393,0x1c00313,0x63e663,0xe90ff06f,0xeb8ff06f,0xef8ff06f]
def clsACode : List (BitVec 32) := clsCode.take 2
sym_block clsA := symRun {noAlias:=true} clsACode (pcOf 26752) 40
def clsZCode : List (BitVec 32) := (clsCode.drop 2).take 3
sym_block clsZ := symRun {noAlias:=true} clsZCode (pcOf 26754) 40
def clsZRCode : List (BitVec 32) := (clsCode.drop 5).take 1
sym_block clsZR := symRun {noAlias:=true} clsZRCode (pcOf 26757) 40
def clsTCode : List (BitVec 32) := (clsCode.drop 6).take 4
sym_block clsT := symRun {noAlias:=true} clsTCode (pcOf 26758) 40
def clsHCode : List (BitVec 32) := (clsCode.drop 10).take 4
sym_block clsH := symRun {noAlias:=true} clsHCode (pcOf 26762) 40
def clsKCode : List (BitVec 32) := (clsCode.drop 14).take 5
sym_block clsK := symRun {noAlias:=true} clsKCode (pcOf 26766) 40
def clsCCode : List (BitVec 32) := (clsCode.drop 19).take 3
sym_block clsC := symRun {noAlias:=true} clsCCode (pcOf 26771) 40
def clsDCode : List (BitVec 32) := (clsCode.drop 22).take 5
sym_block clsD := symRun {noAlias:=true} clsDCode (pcOf 26774) 40
def clsBJCode : List (BitVec 32) := (clsCode.drop 27).take 1
sym_block clsBJ := symRun {noAlias:=true} clsBJCode (pcOf 26779) 40
def clsCJCode : List (BitVec 32) := (clsCode.drop 28).take 1
sym_block clsCJ := symRun {noAlias:=true} clsCJCode (pcOf 26780) 40
def clsRJCode : List (BitVec 32) := clsCode.drop 29
sym_block clsRJ := symRun {noAlias:=true} clsRJCode (pcOf 26781) 40

#print cleanup.res
#print done.res
#print hook.res
#print clsA.res
#print clsZ.res
#print clsT.res
#print clsH.res
#print clsK.res
#print clsC.res
#print clsD.res
#print clsBJ.res
#print clsRJ.res
#print clsCJ.res
#print c_check.res
end OuterSignBlocks
