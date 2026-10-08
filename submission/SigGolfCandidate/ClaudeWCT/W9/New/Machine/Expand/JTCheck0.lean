import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheckParts

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
private theorem jtOK_part_0 : (List.range' 0 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_64 : (List.range' 64 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_128 : (List.range' 128 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_192 : (List.range' 192 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_256 : (List.range' 256 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_320 : (List.range' 320 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_384 : (List.range' 384 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_448 : (List.range' 448 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_512 : (List.range' 512 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_576 : (List.range' 576 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_640 : (List.range' 640 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_704 : (List.range' 704 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_768 : (List.range' 768 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_832 : (List.range' 832 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_896 : (List.range' 896 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_960 : (List.range' 960 64).all jtOK = true := by decide +kernel
theorem jtOK_0 : (List.range' 0 1024).all jtOK = true := by
  exact (@all_range'_add jtOK 0 64 960 jtOK_part_0 (@all_range'_add jtOK 64 64 896 jtOK_part_64 (@all_range'_add jtOK 128 64 832 jtOK_part_128 (@all_range'_add jtOK 192 64 768 jtOK_part_192 (@all_range'_add jtOK 256 64 704 jtOK_part_256 (@all_range'_add jtOK 320 64 640 jtOK_part_320 (@all_range'_add jtOK 384 64 576 jtOK_part_384 (@all_range'_add jtOK 448 64 512 jtOK_part_448 (@all_range'_add jtOK 512 64 448 jtOK_part_512 (@all_range'_add jtOK 576 64 384 jtOK_part_576 (@all_range'_add jtOK 640 64 320 jtOK_part_640 (@all_range'_add jtOK 704 64 256 jtOK_part_704 (@all_range'_add jtOK 768 64 192 jtOK_part_768 (@all_range'_add jtOK 832 64 128 jtOK_part_832 (@all_range'_add jtOK 896 64 64 jtOK_part_896 (jtOK_part_960))))))))))))))))
private theorem jtOK_part_4096 : (List.range' 4096 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4160 : (List.range' 4160 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4224 : (List.range' 4224 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4288 : (List.range' 4288 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4352 : (List.range' 4352 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4416 : (List.range' 4416 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4480 : (List.range' 4480 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4544 : (List.range' 4544 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4608 : (List.range' 4608 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4672 : (List.range' 4672 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4736 : (List.range' 4736 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4800 : (List.range' 4800 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4864 : (List.range' 4864 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4928 : (List.range' 4928 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4992 : (List.range' 4992 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5056 : (List.range' 5056 64).all jtOK = true := by decide +kernel
theorem jtOK_4096 : (List.range' 4096 1024).all jtOK = true := by
  exact (@all_range'_add jtOK 4096 64 960 jtOK_part_4096 (@all_range'_add jtOK 4160 64 896 jtOK_part_4160 (@all_range'_add jtOK 4224 64 832 jtOK_part_4224 (@all_range'_add jtOK 4288 64 768 jtOK_part_4288 (@all_range'_add jtOK 4352 64 704 jtOK_part_4352 (@all_range'_add jtOK 4416 64 640 jtOK_part_4416 (@all_range'_add jtOK 4480 64 576 jtOK_part_4480 (@all_range'_add jtOK 4544 64 512 jtOK_part_4544 (@all_range'_add jtOK 4608 64 448 jtOK_part_4608 (@all_range'_add jtOK 4672 64 384 jtOK_part_4672 (@all_range'_add jtOK 4736 64 320 jtOK_part_4736 (@all_range'_add jtOK 4800 64 256 jtOK_part_4800 (@all_range'_add jtOK 4864 64 192 jtOK_part_4864 (@all_range'_add jtOK 4928 64 128 jtOK_part_4928 (@all_range'_add jtOK 4992 64 64 jtOK_part_4992 (jtOK_part_5056))))))))))))))))
private theorem jtOK_part_8192 : (List.range' 8192 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8256 : (List.range' 8256 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8320 : (List.range' 8320 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8384 : (List.range' 8384 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8448 : (List.range' 8448 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8512 : (List.range' 8512 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8576 : (List.range' 8576 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8640 : (List.range' 8640 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8704 : (List.range' 8704 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8768 : (List.range' 8768 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8832 : (List.range' 8832 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8896 : (List.range' 8896 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8960 : (List.range' 8960 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9024 : (List.range' 9024 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9088 : (List.range' 9088 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9152 : (List.range' 9152 64).all jtOK = true := by decide +kernel
theorem jtOK_8192 : (List.range' 8192 1024).all jtOK = true := by
  exact (@all_range'_add jtOK 8192 64 960 jtOK_part_8192 (@all_range'_add jtOK 8256 64 896 jtOK_part_8256 (@all_range'_add jtOK 8320 64 832 jtOK_part_8320 (@all_range'_add jtOK 8384 64 768 jtOK_part_8384 (@all_range'_add jtOK 8448 64 704 jtOK_part_8448 (@all_range'_add jtOK 8512 64 640 jtOK_part_8512 (@all_range'_add jtOK 8576 64 576 jtOK_part_8576 (@all_range'_add jtOK 8640 64 512 jtOK_part_8640 (@all_range'_add jtOK 8704 64 448 jtOK_part_8704 (@all_range'_add jtOK 8768 64 384 jtOK_part_8768 (@all_range'_add jtOK 8832 64 320 jtOK_part_8832 (@all_range'_add jtOK 8896 64 256 jtOK_part_8896 (@all_range'_add jtOK 8960 64 192 jtOK_part_8960 (@all_range'_add jtOK 9024 64 128 jtOK_part_9024 (@all_range'_add jtOK 9088 64 64 jtOK_part_9088 (jtOK_part_9152))))))))))))))))
private theorem jtOK_part_12288 : (List.range' 12288 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12352 : (List.range' 12352 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12416 : (List.range' 12416 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12480 : (List.range' 12480 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12544 : (List.range' 12544 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12608 : (List.range' 12608 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12672 : (List.range' 12672 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12736 : (List.range' 12736 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12800 : (List.range' 12800 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12864 : (List.range' 12864 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12928 : (List.range' 12928 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12992 : (List.range' 12992 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13056 : (List.range' 13056 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13120 : (List.range' 13120 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13184 : (List.range' 13184 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13248 : (List.range' 13248 64).all jtOK = true := by decide +kernel
theorem jtOK_12288 : (List.range' 12288 1024).all jtOK = true := by
  exact (@all_range'_add jtOK 12288 64 960 jtOK_part_12288 (@all_range'_add jtOK 12352 64 896 jtOK_part_12352 (@all_range'_add jtOK 12416 64 832 jtOK_part_12416 (@all_range'_add jtOK 12480 64 768 jtOK_part_12480 (@all_range'_add jtOK 12544 64 704 jtOK_part_12544 (@all_range'_add jtOK 12608 64 640 jtOK_part_12608 (@all_range'_add jtOK 12672 64 576 jtOK_part_12672 (@all_range'_add jtOK 12736 64 512 jtOK_part_12736 (@all_range'_add jtOK 12800 64 448 jtOK_part_12800 (@all_range'_add jtOK 12864 64 384 jtOK_part_12864 (@all_range'_add jtOK 12928 64 320 jtOK_part_12928 (@all_range'_add jtOK 12992 64 256 jtOK_part_12992 (@all_range'_add jtOK 13056 64 192 jtOK_part_13056 (@all_range'_add jtOK 13120 64 128 jtOK_part_13120 (@all_range'_add jtOK 13184 64 64 jtOK_part_13184 (jtOK_part_13248))))))))))))))))
end ClaudeWCT.W9.Machine.Expand
