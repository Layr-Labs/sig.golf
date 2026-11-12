import SigGolfCandidate.OuterImageTransfers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterRecoveryCodes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand

namespace Entry
open SigGolfCandidate.T3M.Expand.SharedRecover

theorem code : SigGolfCandidate.T3M.Expand.SharedRecover.EntryCode OuterImages.expandImage := by
  constructor
  · exact OuterImageTransfers.code (b:=249) (words:=entryCode249) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code249
  · exact OuterImageTransfers.code (b:=272) (words:=entryCode272) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code272
  · exact OuterImageTransfers.code (b:=295) (words:=seg_295) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code295
  · exact OuterImageTransfers.code (b:=318) (words:=seg_318) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code318
  · exact OuterImageTransfers.code (b:=262) (words:=seg_262) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code262
  · exact OuterImageTransfers.code (b:=285) (words:=seg_285) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code285
  · exact OuterImageTransfers.code (b:=308) (words:=seg_308) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code308
  · exact OuterImageTransfers.code (b:=332) (words:=seg_332) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_entry.code332

#print axioms code
end Entry

namespace Core
open SigGolfCandidate.T3M.Expand.SharedRecover

theorem code : SigGolfCandidate.T3M.Expand.SharedRecover.Code OuterImages.expandImage := by
  constructor
  · exact OuterImageTransfers.code (b:=1119) (words:=e_hdrA) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrA_at
  · exact OuterImageTransfers.code (b:=42765) (words:=e_hdrB) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrB_at
  · exact OuterImageTransfers.code (b:=42768) (words:=e_hdrC) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrC_at
  · exact OuterImageTransfers.code (b:=245346) (words:=e_ndT) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_ndT_at
  · exact OuterImageTransfers.code (b:=42776) (words:=e_hdrD) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrD_at
  · exact OuterImageTransfers.code (b:=1125) (words:=ExpandLabel.window) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrWindow_at
  · exact OuterImageTransfers.code (b:=1129) (words:=e_hdrE) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrE_at
  · exact OuterImageTransfers.code (b:=42741) (words:=e_hpA) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hpA_at
  · exact OuterImageTransfers.code (b:=245335) (words:=e_hpT) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hpT_at
  · exact OuterImageTransfers.code (b:=42750) (words:=(e_hpA.drop 9)) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hpA2_at
  · exact OuterImageTransfers.code (b:=42755) (words:=e_hpZ) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hpZ_at
  · exact OuterImageTransfers.code (b:=42757) (words:=e_hpJ) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hpJ_at
  · exact OuterImageTransfers.code (b:=1009) (words:=e_w1009) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_w1009_at
  · exact OuterImageTransfers.code (b:=42758) (words:=e_slA) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_slA_at
  · exact OuterImageTransfers.code (b:=42760) (words:=e_slB) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_slB_at
  · exact OuterImageTransfers.code (b:=42761) (words:=e_slN) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_slN_at
  · exact OuterImageTransfers.code (b:=42764) (words:=e_slZ) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_slZ_at
  · exact OuterImageTransfers.code (b:=1010) (words:=seg_1010) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1010
  · exact OuterImageTransfers.code (b:=1011) (words:=seg_1011) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1011
  · exact OuterImageTransfers.code (b:=1027) (words:=seg_1027) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1027
  · exact OuterImageTransfers.code (b:=1028) (words:=seg_1028) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1028
  · exact OuterImageTransfers.code (b:=1030) (words:=seg_1030) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1030
  · exact OuterImageTransfers.code (b:=1031) (words:=seg_1031) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1031
  · exact OuterImageTransfers.code (b:=1041) (words:=seg_1041) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1041
  · exact OuterImageTransfers.code (b:=49300) (words:=seg_49300) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49300
  · exact OuterImageTransfers.code (b:=49301) (words:=seg_49301) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49301
  · exact OuterImageTransfers.code (b:=49303) (words:=seg_49303) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49303
  · exact OuterImageTransfers.code (b:=49306) (words:=seg_49306) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49306
  · exact OuterImageTransfers.code (b:=49309) (words:=seg_49309) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49309
  · exact OuterImageTransfers.code (b:=49311) (words:=seg_49311) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49311
  · exact OuterImageTransfers.code (b:=54543) (words:=e_gt0) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_gt0_at
  · exact OuterImageTransfers.code (b:=54551) (words:=e_gt1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_gt1_at
  · exact OuterImageTransfers.code (b:=54552) (words:=e_gt2) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_gt2_at
  · exact OuterImageTransfers.code (b:=49315) (words:=seg_49315) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49315
  · exact OuterImageTransfers.code (b:=49316) (words:=seg_49316) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49316
  · exact OuterImageTransfers.code (b:=49327) (words:=seg_49327) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49327
  · exact OuterImageTransfers.code (b:=49328) (words:=seg_49328) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49328
  · exact OuterImageTransfers.code (b:=49329) (words:=seg_49329) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49329
  · exact OuterImageTransfers.code (b:=49331) (words:=seg_49331) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49331
  · exact OuterImageTransfers.code (b:=49336) (words:=seg_49336) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49336
  · exact OuterImageTransfers.code (b:=49337) (words:=seg_49337) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_49337
  · exact OuterImageTransfers.code (b:=1049) (words:=seg_1049) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1049
  · exact OuterImageTransfers.code (b:=1052) (words:=seg_1052) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1052
  · exact OuterImageTransfers.code (b:=1063) (words:=seg_1063) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1063
  · exact OuterImageTransfers.code (b:=1072) (words:=seg_1072) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1072
  · exact OuterImageTransfers.code (b:=1073) (words:=seg_1073) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1073
  · exact OuterImageTransfers.code (b:=1076) (words:=seg_1076) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1076
  · exact OuterImageTransfers.code (b:=1077) (words:=seg_1077) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1077
  · exact OuterImageTransfers.code (b:=1080) (words:=seg_1080) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1080
  · exact OuterImageTransfers.code (b:=1099) (words:=seg_1099) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1099
  · exact OuterImageTransfers.code (b:=1138) (words:=seg_g1138) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1138
  · exact OuterImageTransfers.code (b:=54800) (words:=cStub) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_stub
  · exact OuterImageTransfers.code (b:=245358) (words:=eDecT1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_dec1
  · exact OuterImageTransfers.code (b:=245366) (words:=eDecT2) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_dec2
  · exact OuterImageTransfers.code (b:=60108) (words:=cE11s) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_e11s
  · exact OuterImageTransfers.code (b:=60968) (words:=cBR) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_brule
  · exact OuterImageTransfers.code (b:=1139) (words:=seg_n1139) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1139
  · exact OuterImageTransfers.code (b:=1140) (words:=seg_1140) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1140
  · exact OuterImageTransfers.code (b:=43195) (words:=nonce_A) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nA
  · exact OuterImageTransfers.code (b:=43197) (words:=nonce_B) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nB
  · exact OuterImageTransfers.code (b:=43199) (words:=nonce_C) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nC
  · exact OuterImageTransfers.code (b:=54553) (words:=nonce_Z0) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZ0
  · exact OuterImageTransfers.code (b:=54557) (words:=nonce_Z1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZ1
  · exact OuterImageTransfers.code (b:=54559) (words:=nonce_Z2) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZ2
  · exact OuterImageTransfers.code (b:=54560) (words:=nonce_Z3) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZ3
  · exact OuterImageTransfers.code (b:=54566) (words:=nonce_Z4) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZ4
  · exact OuterImageTransfers.code (b:=54568) (words:=nonce_Z5) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZ5
  · exact OuterImageTransfers.code (b:=54740) (words:=nonce_ZA0) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZA0
  · exact OuterImageTransfers.code (b:=54741) (words:=nonce_ZA1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZA1
  · exact OuterImageTransfers.code (b:=54743) (words:=nonce_ZA2) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZA2
  · exact OuterImageTransfers.code (b:=54745) (words:=nonce_ZA3) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nZA3
  · exact OuterImageTransfers.code (b:=43215) (words:=nonce_G) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nG
  · exact OuterImageTransfers.code (b:=43225) (words:=nonce_L) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nL
  · exact OuterImageTransfers.code (b:=43228) (words:=nonce_H) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nH
  · exact OuterImageTransfers.code (b:=43232) (words:=nonce_I) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nI
  · exact OuterImageTransfers.code (b:=43238) (words:=nonce_E43238) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_n43238
  · exact OuterImageTransfers.code (b:=43239) (words:=nonce_J) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nJ
  · exact OuterImageTransfers.code (b:=43240) (words:=nonce_K) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nK
  · exact OuterImageTransfers.code (b:=43248) (words:=nonce_S) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_nS
  · exact OuterImageTransfers.code (b:=1143) (words:=seg_1143) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1143
  · exact OuterImageTransfers.code (b:=1158) (words:=seg_1158) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_1158
  · exact OuterImageTransfers.code (b:=54532) (words:=e_kmax0) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_kmax0_at
  · exact OuterImageTransfers.code (b:=54535) (words:=e_kmax1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_kmax1_at
  · exact OuterImageTransfers.code (b:=54538) (words:=e_kmax2) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_kmax2_at
  · exact OuterImageTransfers.code (b:=54541) (words:=e_kmax3) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_kmax3_at
  · exact OuterImageTransfers.code (b:=54542) (words:=e_kmax4) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_kmax4_at
  · exact OuterImageTransfers.code (b:=997) (words:=seg_997) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.codeAt_997
  · exact OuterImageTransfers.code (b:=43467) (words:=e_hdrT) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrT_at
  · exact OuterImageTransfers.code (b:=43451) (words:=e_ct0) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_ct0_at
  · exact OuterImageTransfers.code (b:=43452) (words:=e_ct1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_ct1_at
  · exact OuterImageTransfers.code (b:=43453) (words:=e_ct2) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_ct2_at
  · exact OuterImageTransfers.code (b:=43455) (words:=e_ct3) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_ct3_at
  · exact OuterImageTransfers.code (b:=43460) (words:=e_ct4) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_ct4_at
  · exact OuterImageTransfers.code (b:=43462) (words:=e_lcA) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_lcA_at
  · exact OuterImageTransfers.code (b:=43465) (words:=e_lcB) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_lcB_at
  · exact OuterImageTransfers.code (b:=43466) (words:=e_lcC) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_lcC_at
  · exact OuterImageTransfers.code (b:=1105) (words:=e_lcD) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_lcD_at
  · exact OuterImageTransfers.code (b:=231593) (words:=ExpandLabel.remapCode) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_code.e_hdrRemap_at

#print axioms code
end Core

namespace BC
open SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open SigGolfCandidate.T3M.Expand.BCBlocks

theorem code : SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks.Code OuterImages.expandImage := by
  constructor
  · exact OuterImageTransfers.code (b:=1117) (words:=hookCode) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.hookCode_at
  · exact OuterImageTransfers.code (b:=40875) (words:=testCode) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.testCode_at
  · exact OuterImageTransfers.code (b:=40877) (words:=branch1Code) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.branch1Code_at
  · exact OuterImageTransfers.code (b:=40878) (words:=branch2Code) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.branch2Code_at
  · exact OuterImageTransfers.code (b:=40879) (words:=pairCode) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.pairCode_at
  · exact OuterImageTransfers.code (b:=40892) (words:=backCode) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.backCode_at
  · exact OuterImageTransfers.code (b:=40875) (words:=selectCode) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_bc.selectCode_at

#print axioms code
end BC

namespace Packed
open SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open SigGolfCandidate.T3M.Keygen.PackedBlocks

theorem code : SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks.Code OuterImages.expandImage := by
  constructor
  · exact OuterImageTransfers.code (b:=1032) (words:=expand_entry) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.entry
  · exact OuterImageTransfers.code (b:=1247) (words:=expand_layer0) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.layer0
  · exact OuterImageTransfers.code (b:=1249) (words:=expand_layer1) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.layer1
  · exact OuterImageTransfers.code (b:=1251) (words:=expand_layer23) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.layer23
  · exact OuterImageTransfers.code (b:=1252) (words:=expand_inc) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.inc
  · exact OuterImageTransfers.code (b:=1253) (words:=expand_bodyA) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.body
  · exact OuterImageTransfers.code (b:=245313) (words:=expand_hdrT) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.hdrT
  · exact OuterImageTransfers.code (b:=1266) (words:=(expand_bodyA.drop 13)) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.body2
  · exact OuterImageTransfers.code (b:=1038) (words:=expand_store) (by decide +kernel) SigGolfCandidate.T3M.Expand.SharedRecover.installed_packed.store

#print axioms code
end Packed

namespace Copy
open SigGolfCandidate.T3M.Expand.KCopy

theorem code : SigGolfCandidate.T3M.Expand.KCopy.Code OuterImages.expandImage := by
  constructor
  · exact OuterImageTransfers.code (b:=54522) (words:=headWords) (by decide +kernel) SigGolfCandidate.T3M.Expand.KCopy.installed_code.head
  · exact OuterImageTransfers.code (b:=54526) (words:=loopWords) (by decide +kernel) SigGolfCandidate.T3M.Expand.KCopy.installed_code.loop
  · exact OuterImageTransfers.code (b:=54531) (words:=tailWords) (by decide +kernel) SigGolfCandidate.T3M.Expand.KCopy.installed_code.tail

#print axioms code
end Copy
end OuterRecoveryCodes
