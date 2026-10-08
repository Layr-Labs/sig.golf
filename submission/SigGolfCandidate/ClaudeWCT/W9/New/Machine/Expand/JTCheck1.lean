import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck0

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
private theorem jtOK_part_1024 : (List.range' 1024 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1088 : (List.range' 1088 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1152 : (List.range' 1152 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1216 : (List.range' 1216 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1280 : (List.range' 1280 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1344 : (List.range' 1344 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1408 : (List.range' 1408 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1472 : (List.range' 1472 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1536 : (List.range' 1536 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1600 : (List.range' 1600 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1664 : (List.range' 1664 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1728 : (List.range' 1728 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1792 : (List.range' 1792 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1856 : (List.range' 1856 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1920 : (List.range' 1920 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_1984 : (List.range' 1984 64).all jtOK = true := by decide +kernel
theorem jtOK_1024 : (List.range' 1024 1024).all jtOK = true := by
  exact @all_range'_add jtOK 1024 64 960 jtOK_part_1024 (@all_range'_add jtOK 1088 64 896 jtOK_part_1088 (@all_range'_add jtOK 1152 64 832 jtOK_part_1152 (@all_range'_add jtOK 1216 64 768 jtOK_part_1216 (@all_range'_add jtOK 1280 64 704 jtOK_part_1280 (@all_range'_add jtOK 1344 64 640 jtOK_part_1344 (@all_range'_add jtOK 1408 64 576 jtOK_part_1408 (@all_range'_add jtOK 1472 64 512 jtOK_part_1472 (@all_range'_add jtOK 1536 64 448 jtOK_part_1536 (@all_range'_add jtOK 1600 64 384 jtOK_part_1600 (@all_range'_add jtOK 1664 64 320 jtOK_part_1664 (@all_range'_add jtOK 1728 64 256 jtOK_part_1728 (@all_range'_add jtOK 1792 64 192 jtOK_part_1792 (@all_range'_add jtOK 1856 64 128 jtOK_part_1856 (@all_range'_add jtOK 1920 64 64 jtOK_part_1920 (jtOK_part_1984)))))))))))))))
private theorem jtOK_part_5120 : (List.range' 5120 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5184 : (List.range' 5184 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5248 : (List.range' 5248 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5312 : (List.range' 5312 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5376 : (List.range' 5376 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5440 : (List.range' 5440 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5504 : (List.range' 5504 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5568 : (List.range' 5568 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5632 : (List.range' 5632 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5696 : (List.range' 5696 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5760 : (List.range' 5760 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5824 : (List.range' 5824 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5888 : (List.range' 5888 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_5952 : (List.range' 5952 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6016 : (List.range' 6016 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6080 : (List.range' 6080 64).all jtOK = true := by decide +kernel
theorem jtOK_5120 : (List.range' 5120 1024).all jtOK = true := by
  exact @all_range'_add jtOK 5120 64 960 jtOK_part_5120 (@all_range'_add jtOK 5184 64 896 jtOK_part_5184 (@all_range'_add jtOK 5248 64 832 jtOK_part_5248 (@all_range'_add jtOK 5312 64 768 jtOK_part_5312 (@all_range'_add jtOK 5376 64 704 jtOK_part_5376 (@all_range'_add jtOK 5440 64 640 jtOK_part_5440 (@all_range'_add jtOK 5504 64 576 jtOK_part_5504 (@all_range'_add jtOK 5568 64 512 jtOK_part_5568 (@all_range'_add jtOK 5632 64 448 jtOK_part_5632 (@all_range'_add jtOK 5696 64 384 jtOK_part_5696 (@all_range'_add jtOK 5760 64 320 jtOK_part_5760 (@all_range'_add jtOK 5824 64 256 jtOK_part_5824 (@all_range'_add jtOK 5888 64 192 jtOK_part_5888 (@all_range'_add jtOK 5952 64 128 jtOK_part_5952 (@all_range'_add jtOK 6016 64 64 jtOK_part_6016 (jtOK_part_6080)))))))))))))))
private theorem jtOK_part_9216 : (List.range' 9216 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9280 : (List.range' 9280 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9344 : (List.range' 9344 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9408 : (List.range' 9408 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9472 : (List.range' 9472 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9536 : (List.range' 9536 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9600 : (List.range' 9600 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9664 : (List.range' 9664 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9728 : (List.range' 9728 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9792 : (List.range' 9792 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9856 : (List.range' 9856 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9920 : (List.range' 9920 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_9984 : (List.range' 9984 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10048 : (List.range' 10048 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10112 : (List.range' 10112 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10176 : (List.range' 10176 64).all jtOK = true := by decide +kernel
theorem jtOK_9216 : (List.range' 9216 1024).all jtOK = true := by
  exact @all_range'_add jtOK 9216 64 960 jtOK_part_9216 (@all_range'_add jtOK 9280 64 896 jtOK_part_9280 (@all_range'_add jtOK 9344 64 832 jtOK_part_9344 (@all_range'_add jtOK 9408 64 768 jtOK_part_9408 (@all_range'_add jtOK 9472 64 704 jtOK_part_9472 (@all_range'_add jtOK 9536 64 640 jtOK_part_9536 (@all_range'_add jtOK 9600 64 576 jtOK_part_9600 (@all_range'_add jtOK 9664 64 512 jtOK_part_9664 (@all_range'_add jtOK 9728 64 448 jtOK_part_9728 (@all_range'_add jtOK 9792 64 384 jtOK_part_9792 (@all_range'_add jtOK 9856 64 320 jtOK_part_9856 (@all_range'_add jtOK 9920 64 256 jtOK_part_9920 (@all_range'_add jtOK 9984 64 192 jtOK_part_9984 (@all_range'_add jtOK 10048 64 128 jtOK_part_10048 (@all_range'_add jtOK 10112 64 64 jtOK_part_10112 (jtOK_part_10176)))))))))))))))
private theorem jtOK_part_13312 : (List.range' 13312 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13376 : (List.range' 13376 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13440 : (List.range' 13440 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13504 : (List.range' 13504 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13568 : (List.range' 13568 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13632 : (List.range' 13632 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13696 : (List.range' 13696 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13760 : (List.range' 13760 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13824 : (List.range' 13824 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13888 : (List.range' 13888 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_13952 : (List.range' 13952 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14016 : (List.range' 14016 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14080 : (List.range' 14080 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14144 : (List.range' 14144 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14208 : (List.range' 14208 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14272 : (List.range' 14272 64).all jtOK = true := by decide +kernel
theorem jtOK_13312 : (List.range' 13312 1024).all jtOK = true := by
  exact @all_range'_add jtOK 13312 64 960 jtOK_part_13312 (@all_range'_add jtOK 13376 64 896 jtOK_part_13376 (@all_range'_add jtOK 13440 64 832 jtOK_part_13440 (@all_range'_add jtOK 13504 64 768 jtOK_part_13504 (@all_range'_add jtOK 13568 64 704 jtOK_part_13568 (@all_range'_add jtOK 13632 64 640 jtOK_part_13632 (@all_range'_add jtOK 13696 64 576 jtOK_part_13696 (@all_range'_add jtOK 13760 64 512 jtOK_part_13760 (@all_range'_add jtOK 13824 64 448 jtOK_part_13824 (@all_range'_add jtOK 13888 64 384 jtOK_part_13888 (@all_range'_add jtOK 13952 64 320 jtOK_part_13952 (@all_range'_add jtOK 14016 64 256 jtOK_part_14016 (@all_range'_add jtOK 14080 64 192 jtOK_part_14080 (@all_range'_add jtOK 14144 64 128 jtOK_part_14144 (@all_range'_add jtOK 14208 64 64 jtOK_part_14208 (jtOK_part_14272)))))))))))))))
end ClaudeWCT.W9.Machine.Expand
