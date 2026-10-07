import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheckParts

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
private theorem jtOK_part_3072 : (List.range' 3072 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3136 : (List.range' 3136 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3200 : (List.range' 3200 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3264 : (List.range' 3264 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3328 : (List.range' 3328 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3392 : (List.range' 3392 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3456 : (List.range' 3456 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3520 : (List.range' 3520 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3584 : (List.range' 3584 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3648 : (List.range' 3648 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3712 : (List.range' 3712 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3776 : (List.range' 3776 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3840 : (List.range' 3840 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3904 : (List.range' 3904 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_3968 : (List.range' 3968 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_4032 : (List.range' 4032 64).all jtOK = true := by decide +kernel
theorem jtOK_3072 : (List.range' 3072 1024).all jtOK = true := by
  exact @all_range'_add jtOK 3072 64 960 jtOK_part_3072 (@all_range'_add jtOK 3136 64 896 jtOK_part_3136 (@all_range'_add jtOK 3200 64 832 jtOK_part_3200 (@all_range'_add jtOK 3264 64 768 jtOK_part_3264 (@all_range'_add jtOK 3328 64 704 jtOK_part_3328 (@all_range'_add jtOK 3392 64 640 jtOK_part_3392 (@all_range'_add jtOK 3456 64 576 jtOK_part_3456 (@all_range'_add jtOK 3520 64 512 jtOK_part_3520 (@all_range'_add jtOK 3584 64 448 jtOK_part_3584 (@all_range'_add jtOK 3648 64 384 jtOK_part_3648 (@all_range'_add jtOK 3712 64 320 jtOK_part_3712 (@all_range'_add jtOK 3776 64 256 jtOK_part_3776 (@all_range'_add jtOK 3840 64 192 jtOK_part_3840 (@all_range'_add jtOK 3904 64 128 jtOK_part_3904 (@all_range'_add jtOK 3968 64 64 jtOK_part_3968 (jtOK_part_4032)))))))))))))))
private theorem jtOK_part_7168 : (List.range' 7168 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7232 : (List.range' 7232 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7296 : (List.range' 7296 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7360 : (List.range' 7360 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7424 : (List.range' 7424 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7488 : (List.range' 7488 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7552 : (List.range' 7552 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7616 : (List.range' 7616 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7680 : (List.range' 7680 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7744 : (List.range' 7744 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7808 : (List.range' 7808 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7872 : (List.range' 7872 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_7936 : (List.range' 7936 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8000 : (List.range' 8000 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8064 : (List.range' 8064 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_8128 : (List.range' 8128 64).all jtOK = true := by decide +kernel
theorem jtOK_7168 : (List.range' 7168 1024).all jtOK = true := by
  exact @all_range'_add jtOK 7168 64 960 jtOK_part_7168 (@all_range'_add jtOK 7232 64 896 jtOK_part_7232 (@all_range'_add jtOK 7296 64 832 jtOK_part_7296 (@all_range'_add jtOK 7360 64 768 jtOK_part_7360 (@all_range'_add jtOK 7424 64 704 jtOK_part_7424 (@all_range'_add jtOK 7488 64 640 jtOK_part_7488 (@all_range'_add jtOK 7552 64 576 jtOK_part_7552 (@all_range'_add jtOK 7616 64 512 jtOK_part_7616 (@all_range'_add jtOK 7680 64 448 jtOK_part_7680 (@all_range'_add jtOK 7744 64 384 jtOK_part_7744 (@all_range'_add jtOK 7808 64 320 jtOK_part_7808 (@all_range'_add jtOK 7872 64 256 jtOK_part_7872 (@all_range'_add jtOK 7936 64 192 jtOK_part_7936 (@all_range'_add jtOK 8000 64 128 jtOK_part_8000 (@all_range'_add jtOK 8064 64 64 jtOK_part_8064 (jtOK_part_8128)))))))))))))))
private theorem jtOK_part_11264 : (List.range' 11264 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11328 : (List.range' 11328 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11392 : (List.range' 11392 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11456 : (List.range' 11456 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11520 : (List.range' 11520 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11584 : (List.range' 11584 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11648 : (List.range' 11648 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11712 : (List.range' 11712 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11776 : (List.range' 11776 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11840 : (List.range' 11840 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11904 : (List.range' 11904 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_11968 : (List.range' 11968 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12032 : (List.range' 12032 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12096 : (List.range' 12096 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12160 : (List.range' 12160 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_12224 : (List.range' 12224 64).all jtOK = true := by decide +kernel
theorem jtOK_11264 : (List.range' 11264 1024).all jtOK = true := by
  exact @all_range'_add jtOK 11264 64 960 jtOK_part_11264 (@all_range'_add jtOK 11328 64 896 jtOK_part_11328 (@all_range'_add jtOK 11392 64 832 jtOK_part_11392 (@all_range'_add jtOK 11456 64 768 jtOK_part_11456 (@all_range'_add jtOK 11520 64 704 jtOK_part_11520 (@all_range'_add jtOK 11584 64 640 jtOK_part_11584 (@all_range'_add jtOK 11648 64 576 jtOK_part_11648 (@all_range'_add jtOK 11712 64 512 jtOK_part_11712 (@all_range'_add jtOK 11776 64 448 jtOK_part_11776 (@all_range'_add jtOK 11840 64 384 jtOK_part_11840 (@all_range'_add jtOK 11904 64 320 jtOK_part_11904 (@all_range'_add jtOK 11968 64 256 jtOK_part_11968 (@all_range'_add jtOK 12032 64 192 jtOK_part_12032 (@all_range'_add jtOK 12096 64 128 jtOK_part_12096 (@all_range'_add jtOK 12160 64 64 jtOK_part_12160 (jtOK_part_12224)))))))))))))))
private theorem jtOK_part_15360 : (List.range' 15360 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15424 : (List.range' 15424 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15488 : (List.range' 15488 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15552 : (List.range' 15552 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15616 : (List.range' 15616 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15680 : (List.range' 15680 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15744 : (List.range' 15744 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15808 : (List.range' 15808 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15872 : (List.range' 15872 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_15936 : (List.range' 15936 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_16000 : (List.range' 16000 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_16064 : (List.range' 16064 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_16128 : (List.range' 16128 64).all jtOK = true := by decide +kernel
private theorem jtOK_part_16192 : (List.range' 16192 8).all jtOK = true := by decide +kernel
theorem jtOK_15360 : (List.range' 15360 840).all jtOK = true := by
  exact @all_range'_add jtOK 15360 64 776 jtOK_part_15360 (@all_range'_add jtOK 15424 64 712 jtOK_part_15424 (@all_range'_add jtOK 15488 64 648 jtOK_part_15488 (@all_range'_add jtOK 15552 64 584 jtOK_part_15552 (@all_range'_add jtOK 15616 64 520 jtOK_part_15616 (@all_range'_add jtOK 15680 64 456 jtOK_part_15680 (@all_range'_add jtOK 15744 64 392 jtOK_part_15744 (@all_range'_add jtOK 15808 64 328 jtOK_part_15808 (@all_range'_add jtOK 15872 64 264 jtOK_part_15872 (@all_range'_add jtOK 15936 64 200 jtOK_part_15936 (@all_range'_add jtOK 16000 64 136 jtOK_part_16000 (@all_range'_add jtOK 16064 64 72 jtOK_part_16064 (@all_range'_add jtOK 16128 64 8 jtOK_part_16128 (jtOK_part_16192)))))))))))))
end ClaudeWCT.W9.Machine.Expand
