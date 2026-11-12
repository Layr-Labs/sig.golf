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
def dispatchCode : List (BitVec 32) := [0x50337,0x30030313,0xa651663,0x1053383,0x3039393,0x303d393,0x10337,0x80030313,0x8639a63,0x1853383,0x400313,0x863f463,0x1053383,0x103d393,0xf3f393,0x700313,0x2638863]
def b_startCode : List (BitVec 32) := [0x313,0x2053423]
sym_block b_start := symRun {noAlias:=true} b_startCode (pcOf 26175) 40
def b_preCode : List (BitVec 32) := [0x2653023,0x73]
sym_block b_pre := symRun {noAlias:=true} b_preCode (pcOf 26177) 40
def b_checkCode : List (BitVec 32) := [0x1863383,0x3d3d393,0x4038863]
sym_block b_check := symRun {noAlias:=true} b_checkCode (pcOf 26179) 40
def b_retryCode : List (BitVec 32) := [0x130313,0xb35393,0xfe0382e3]
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
def headerCode : List (BitVec 32) := (dispatchCode.drop 3).take 6
sym_block header := symRun {noAlias:=true} headerCode (pcOf 26161) 40
def heapCode : List (BitVec 32) := (dispatchCode.drop 9).take 3
sym_block heap := symRun {noAlias:=true} heapCode (pcOf 26167) 40
def coordCode : List (BitVec 32) := dispatchCode.drop 12
sym_block coord := symRun {noAlias:=true} coordCode (pcOf 26170) 40

#print cleanup.res
#print done.res
end OuterSignBlocks
