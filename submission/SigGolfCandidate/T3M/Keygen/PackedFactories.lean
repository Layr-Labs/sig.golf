import SigGolfCandidate.T3M.Mem

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def keygen_entry : List (BitVec 32) := [0x7340006f]
sym_block run_keygen_entry := symRun { noAlias := true } keygen_entry (pcOf 126) 100
def keygen_layer0 : List (BitVec 32) := [0xc00393,264803]
sym_block run_keygen_layer0 := symRun { noAlias := true } keygen_layer0 (pcOf 587) 100
def keygen_layer1 : List (BitVec 32) := [1049491,7603299]
sym_block run_keygen_layer1 := symRun { noAlias := true } keygen_layer1 (pcOf 589) 100
def keygen_layer23 : List (BitVec 32) := [915,6521747]
sym_block run_keygen_layer23 := symRun { noAlias := true } keygen_layer23 (pcOf 591) 100
def keygen_inc : List (BitVec 32) := [6521747]
sym_block run_keygen_inc := symRun { noAlias := true } keygen_inc (pcOf 592) 100
def keygen_body : List (BitVec 32) := [7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,0xc100f13,59711251,31679283,0xffa7393,8622995,7562035,0x809e393,7562035,0x885ff06f]
sym_block run_keygen_body := symRun { noAlias := true } keygen_body (pcOf 593) 100
def keygen_store : List (BitVec 32) := [134711,437128723,7223331,132407,436536595,67110291,132663,486934035]
sym_block run_keygen_store := symRun { noAlias := true } keygen_store (pcOf 132) 100
def sign_entry : List (BitVec 32) := [0x7340006f]
sym_block run_sign_entry := symRun { noAlias := true } sign_entry (pcOf 1022) 100
def sign_layer0 : List (BitVec 32) := [0xc00393,264803]
sym_block run_sign_layer0 := symRun { noAlias := true } sign_layer0 (pcOf 1483) 100
def sign_layer1 : List (BitVec 32) := [1049491,7603299]
sym_block run_sign_layer1 := symRun { noAlias := true } sign_layer1 (pcOf 1485) 100
def sign_layer23 : List (BitVec 32) := [915,6521747]
sym_block run_sign_layer23 := symRun { noAlias := true } sign_layer23 (pcOf 1487) 100
def sign_inc : List (BitVec 32) := [6521747]
sym_block run_sign_inc := symRun { noAlias := true } sign_inc (pcOf 1488) 100
def sign_body : List (BitVec 32) := [7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,0xc100f13,59711251,31679283,0xffa7393,8622995,7562035,0x809e393,7562035,0x885ff06f]
sym_block run_sign_body := symRun { noAlias := true } sign_body (pcOf 1489) 100
def sign_store : List (BitVec 32) := [134711,437128723,7223331,132407,436536595,67110291,132663,486934035]
sym_block run_sign_store := symRun { noAlias := true } sign_store (pcOf 1028) 100
def expand_entry : List (BitVec 32) := [901775471]
sym_block run_expand_entry := symRun { noAlias := true } expand_entry (pcOf 1032) 100
def expand_layer0 : List (BitVec 32) := [0xc00393,264803]
sym_block run_expand_layer0 := symRun { noAlias := true } expand_layer0 (pcOf 1247) 100
def expand_layer1 : List (BitVec 32) := [1049491,7603299]
sym_block run_expand_layer1 := symRun { noAlias := true } expand_layer1 (pcOf 1249) 100
def expand_layer23 : List (BitVec 32) := [915,6521747]
sym_block run_expand_layer23 := symRun { noAlias := true } expand_layer23 (pcOf 1251) 100
def expand_inc : List (BitVec 32) := [6521747]
sym_block run_expand_inc := symRun { noAlias := true } expand_inc (pcOf 1252) 100
def expand_body : List (BitVec 32) := [7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,0xc100f13,59711251,31679283,0xffa7393,8622995,7562035,0x809e393,7562035,0xc5dff06f]
sym_block run_expand_body := symRun { noAlias := true } expand_body (pcOf 1253) 100
def expand_store : List (BitVec 32) := [134711,437128723,7223331,132407,436536595,67110291,132663,486934035]
sym_block run_expand_store := symRun { noAlias := true } expand_store (pcOf 1038) 100
end SigGolfCandidate.T3M.Keygen.PackedBlocks
