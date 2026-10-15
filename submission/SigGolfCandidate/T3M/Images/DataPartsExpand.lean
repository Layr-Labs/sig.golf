import SigGolfCandidate.T3M.Images.Expand

set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.Images
theorem expandPrefixData_length : expandPrefixData.length = 23552 := by
  simp only [expandPrefixData, List.length_flatten, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_append, List.length_replicate,
    decodePackedWords_length, expandPrefix_0, expandPrefix_1, expandPrefix_2, expandPrefix_3, expandPrefix_4, expandPrefix_5, expandPrefix_6, expandPrefix_7, expandPrefix_8, expandPrefix_9, expandPrefix_10, expandPrefix_11, expandPrefix_12, expandPrefix_13, expandPrefix_14, expandPrefix_15, expandPrefix_16, expandPrefix_17, expandPrefix_18, expandPrefix_19, expandPrefix_20, expandPrefix_21, expandPrefix_22, expandPrefix_23, expandPrefix_24, expandPrefix_25, expandPrefix_26, expandPrefix_27, expandPrefix_28, expandPrefix_29, expandPrefix_30, expandPrefix_31, expandPrefix_32, expandPrefix_33, expandPrefix_34, expandPrefix_35, expandPrefix_36, expandPrefix_37, expandPrefix_38, expandPrefix_39, expandPrefix_40, expandPrefix_41, expandPrefix_42, expandPrefix_43, expandPrefix_44, expandPrefix_45, expandPrefix_46, expandPrefix_47, expandPrefix_48, expandPrefix_49, expandPrefix_50, expandPrefix_51, expandPrefix_52, expandPrefix_53, expandPrefix_54, expandPrefix_55, expandPrefix_56, expandPrefix_57, expandPrefix_58, expandPrefix_59, expandPrefix_60, expandPrefix_61, expandPrefix_62, expandPrefix_63, expandPrefix_64, expandPrefix_65, expandPrefix_66, expandPrefix_67, expandPrefix_68, expandPrefix_69, expandPrefix_70, expandPrefix_71, expandPrefix_72, expandPrefix_73, expandPrefix_74, expandPrefix_75, expandPrefix_76, expandPrefix_77, expandPrefix_78, expandPrefix_79, expandPrefix_80, expandPrefix_81, expandPrefix_82, expandPrefix_83, expandPrefix_84, expandPrefix_85, expandPrefix_86, expandPrefix_87, expandPrefix_88, expandPrefix_89, expandPrefix_90, expandPrefix_91]
  decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by
  simp only [expandLegacyData, List.length_append, List.length_replicate, decodePackedWords_length]
end SigGolfCandidate.T3M.Images
