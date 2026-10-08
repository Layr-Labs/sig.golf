import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheckParts

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
private theorem jtOK_part_2048 : (List.range' 2048 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2112 : (List.range' 2112 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2176 : (List.range' 2176 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2240 : (List.range' 2240 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2304 : (List.range' 2304 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2368 : (List.range' 2368 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2432 : (List.range' 2432 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2496 : (List.range' 2496 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2560 : (List.range' 2560 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2624 : (List.range' 2624 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2688 : (List.range' 2688 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2752 : (List.range' 2752 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2816 : (List.range' 2816 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2880 : (List.range' 2880 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_2944 : (List.range' 2944 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3008 : (List.range' 3008 64).all jtOK = true := by decide +kernel
theorem jtOK_2048 : (List.range' 2048 1024).all jtOK = true := by
  exact @all_range'_add jtOK 2048 64 960 jtOK_part_2048 (@all_range'_add jtOK 2112 64 896 jtOK_part_2112 (@all_range'_add jtOK 2176 64 832 jtOK_part_2176 (@all_range'_add jtOK 2240 64 768 jtOK_part_2240 (@all_range'_add jtOK 2304 64 704 jtOK_part_2304 (@all_range'_add jtOK 2368 64 640 jtOK_part_2368 (@all_range'_add jtOK 2432 64 576 jtOK_part_2432 (@all_range'_add jtOK 2496 64 512 jtOK_part_2496 (@all_range'_add jtOK 2560 64 448 jtOK_part_2560 (@all_range'_add jtOK 2624 64 384 jtOK_part_2624 (@all_range'_add jtOK 2688 64 320 jtOK_part_2688 (@all_range'_add jtOK 2752 64 256 jtOK_part_2752 (@all_range'_add jtOK 2816 64 192 jtOK_part_2816 (@all_range'_add jtOK 2880 64 128 jtOK_part_2880 (@all_range'_add jtOK 2944 64 64 jtOK_part_2944 (jtOK_part_3008)))))))))))))))
private theorem jtOK_part_6144 : (List.range' 6144 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6208 : (List.range' 6208 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6272 : (List.range' 6272 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6336 : (List.range' 6336 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6400 : (List.range' 6400 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6464 : (List.range' 6464 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6528 : (List.range' 6528 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6592 : (List.range' 6592 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6656 : (List.range' 6656 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6720 : (List.range' 6720 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6784 : (List.range' 6784 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6848 : (List.range' 6848 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6912 : (List.range' 6912 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_6976 : (List.range' 6976 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7040 : (List.range' 7040 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7104 : (List.range' 7104 64).all jtOK = true := by decide +kernel
theorem jtOK_6144 : (List.range' 6144 1024).all jtOK = true := by
  exact @all_range'_add jtOK 6144 64 960 jtOK_part_6144 (@all_range'_add jtOK 6208 64 896 jtOK_part_6208 (@all_range'_add jtOK 6272 64 832 jtOK_part_6272 (@all_range'_add jtOK 6336 64 768 jtOK_part_6336 (@all_range'_add jtOK 6400 64 704 jtOK_part_6400 (@all_range'_add jtOK 6464 64 640 jtOK_part_6464 (@all_range'_add jtOK 6528 64 576 jtOK_part_6528 (@all_range'_add jtOK 6592 64 512 jtOK_part_6592 (@all_range'_add jtOK 6656 64 448 jtOK_part_6656 (@all_range'_add jtOK 6720 64 384 jtOK_part_6720 (@all_range'_add jtOK 6784 64 320 jtOK_part_6784 (@all_range'_add jtOK 6848 64 256 jtOK_part_6848 (@all_range'_add jtOK 6912 64 192 jtOK_part_6912 (@all_range'_add jtOK 6976 64 128 jtOK_part_6976 (@all_range'_add jtOK 7040 64 64 jtOK_part_7040 (jtOK_part_7104)))))))))))))))
private theorem jtOK_part_10240 : (List.range' 10240 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10304 : (List.range' 10304 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10368 : (List.range' 10368 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10432 : (List.range' 10432 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10496 : (List.range' 10496 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10560 : (List.range' 10560 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10624 : (List.range' 10624 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10688 : (List.range' 10688 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10752 : (List.range' 10752 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10816 : (List.range' 10816 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10880 : (List.range' 10880 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_10944 : (List.range' 10944 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11008 : (List.range' 11008 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11072 : (List.range' 11072 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11136 : (List.range' 11136 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11200 : (List.range' 11200 64).all jtOK = true := by decide +kernel
theorem jtOK_10240 : (List.range' 10240 1024).all jtOK = true := by
  exact @all_range'_add jtOK 10240 64 960 jtOK_part_10240 (@all_range'_add jtOK 10304 64 896 jtOK_part_10304 (@all_range'_add jtOK 10368 64 832 jtOK_part_10368 (@all_range'_add jtOK 10432 64 768 jtOK_part_10432 (@all_range'_add jtOK 10496 64 704 jtOK_part_10496 (@all_range'_add jtOK 10560 64 640 jtOK_part_10560 (@all_range'_add jtOK 10624 64 576 jtOK_part_10624 (@all_range'_add jtOK 10688 64 512 jtOK_part_10688 (@all_range'_add jtOK 10752 64 448 jtOK_part_10752 (@all_range'_add jtOK 10816 64 384 jtOK_part_10816 (@all_range'_add jtOK 10880 64 320 jtOK_part_10880 (@all_range'_add jtOK 10944 64 256 jtOK_part_10944 (@all_range'_add jtOK 11008 64 192 jtOK_part_11008 (@all_range'_add jtOK 11072 64 128 jtOK_part_11072 (@all_range'_add jtOK 11136 64 64 jtOK_part_11136 (jtOK_part_11200)))))))))))))))
private theorem jtOK_part_14336 : (List.range' 14336 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14400 : (List.range' 14400 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14464 : (List.range' 14464 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14528 : (List.range' 14528 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14592 : (List.range' 14592 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14656 : (List.range' 14656 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14720 : (List.range' 14720 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14784 : (List.range' 14784 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14848 : (List.range' 14848 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14912 : (List.range' 14912 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_14976 : (List.range' 14976 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15040 : (List.range' 15040 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15104 : (List.range' 15104 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15168 : (List.range' 15168 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15232 : (List.range' 15232 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15296 : (List.range' 15296 64).all jtOK = true := by decide +kernel
theorem jtOK_14336 : (List.range' 14336 1024).all jtOK = true := by
  exact @all_range'_add jtOK 14336 64 960 jtOK_part_14336 (@all_range'_add jtOK 14400 64 896 jtOK_part_14400 (@all_range'_add jtOK 14464 64 832 jtOK_part_14464 (@all_range'_add jtOK 14528 64 768 jtOK_part_14528 (@all_range'_add jtOK 14592 64 704 jtOK_part_14592 (@all_range'_add jtOK 14656 64 640 jtOK_part_14656 (@all_range'_add jtOK 14720 64 576 jtOK_part_14720 (@all_range'_add jtOK 14784 64 512 jtOK_part_14784 (@all_range'_add jtOK 14848 64 448 jtOK_part_14848 (@all_range'_add jtOK 14912 64 384 jtOK_part_14912 (@all_range'_add jtOK 14976 64 320 jtOK_part_14976 (@all_range'_add jtOK 15040 64 256 jtOK_part_15040 (@all_range'_add jtOK 15104 64 192 jtOK_part_15104 (@all_range'_add jtOK 15168 64 128 jtOK_part_15168 (@all_range'_add jtOK 15232 64 64 jtOK_part_15232 (jtOK_part_15296)))))))))))))))
end ClaudeWCT.W9.Machine.Expand
