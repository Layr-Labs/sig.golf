import SigGolfCandidate.T3M.Images.Verify
import SigGolfCandidate.T3M.Mem

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
def lChunks : List (List (BitVec 32)) := [Images.verifyCode_0, Images.verifyCode_1, Images.verifyCode_2, Images.verifyCode_3, Images.verifyCode_4, Images.verifyCode_5, Images.verifyCode_6, Images.verifyCode_7, Images.verifyCode_8, Images.verifyCode_9, Images.verifyCode_10, Images.verifyCode_11, Images.verifyCode_12, Images.verifyCode_13, Images.verifyCode_14, Images.verifyCode_15, Images.verifyCode_16, Images.verifyCode_17, Images.verifyCode_18, Images.verifyCode_19, Images.verifyCode_20, Images.verifyCode_21, Images.verifyCode_22, Images.verifyCode_23, Images.verifyCode_24, Images.verifyCode_25, Images.verifyCode_26, Images.verifyCode_27, Images.verifyCode_28, Images.verifyCode_29, Images.verifyCode_30, Images.verifyCode_31, Images.verifyCode_32, Images.verifyCode_33, Images.verifyCode_34, Images.verifyCode_35, Images.verifyCode_36, Images.verifyCode_37, Images.verifyCode_38, Images.verifyCode_39, Images.verifyCode_40, Images.verifyCode_41, Images.verifyCode_42, Images.verifyCode_43, Images.verifyCode_44, Images.verifyCode_45, Images.verifyCode_46, Images.verifyCode_47, Images.verifyCode_48, Images.verifyCode_49, Images.verifyCode_50, Images.verifyCode_51, Images.verifyCode_52, Images.verifyCode_53, Images.verifyCode_54, Images.verifyCode_55, Images.verifyCode_56, Images.verifyCode_57, Images.verifyCode_58, Images.verifyCode_59, Images.verifyCode_60, Images.verifyCode_61, Images.verifyCode_62, Images.verifyCode_63, Images.verifyCode_64, Images.verifyCode_65, Images.verifyCode_66, Images.verifyCode_67, Images.verifyCode_68, Images.verifyCode_69, Images.verifyCode_70, Images.verifyCode_71, Images.verifyCode_72, Images.verifyCode_73, Images.verifyCode_74, Images.verifyCode_75, Images.verifyCode_76, Images.verifyCode_77, Images.verifyCode_78, Images.verifyCode_79, Images.verifyCode_80, Images.verifyCode_81, Images.verifyCode_82, Images.verifyCode_83, Images.verifyCode_84, Images.verifyCode_85, Images.verifyCode_86, Images.verifyCode_87, Images.verifyCode_88, Images.verifyCode_89, Images.verifyCode_90, Images.verifyCode_91, Images.verifyCode_92, Images.verifyCode_93, Images.verifyCode_94, Images.verifyCode_95, Images.verifyCode_96, Images.verifyCode_97, Images.verifyCode_98, Images.verifyCode_99, Images.verifyCode_100, Images.verifyCode_101, Images.verifyCode_102, Images.verifyCode_103, Images.verifyCode_104, Images.verifyCode_105, Images.verifyCode_106, Images.verifyCode_107, Images.verifyCode_108, Images.verifyCode_109, Images.verifyCode_110, Images.verifyCode_111, Images.verifyCode_112, Images.verifyCode_113, Images.verifyCode_114, Images.verifyCode_115, Images.verifyCode_116, Images.verifyCode_117, Images.verifyCode_118, Images.verifyCode_119, Images.verifyCode_120, Images.verifyCode_121, Images.verifyCode_122, Images.verifyCode_123, Images.verifyCode_124, Images.verifyCode_125, Images.verifyCode_126, Images.verifyCode_127, Images.verifyCode_128, Images.verifyCode_129, Images.verifyCode_130, Images.verifyCode_131, Images.verifyCode_132, Images.verifyCode_133, Images.verifyCode_134, Images.verifyCode_135, Images.verifyCode_136, Images.verifyCode_137, Images.verifyCode_138, Images.verifyCode_139, Images.verifyCode_140, Images.verifyCode_141, Images.verifyCode_142, Images.verifyCode_143, Images.verifyCode_144, Images.verifyCode_145, Images.verifyCode_146, Images.verifyCode_147, Images.verifyCode_148, Images.verifyCode_149, Images.verifyCode_150, Images.verifyCode_151, Images.verifyCode_152, Images.verifyCode_153, Images.verifyCode_154, Images.verifyCode_155, Images.verifyCode_156, Images.verifyCode_157, Images.verifyCode_158, Images.verifyCode_159, Images.verifyCode_160, Images.verifyCode_161, Images.verifyCode_162, Images.verifyCode_163, Images.verifyCode_164, Images.verifyCode_165, Images.verifyCode_166, Images.verifyCode_167, Images.verifyCode_168, Images.verifyCode_169, Images.verifyCode_170, Images.verifyCode_171, Images.verifyCode_172, Images.verifyCode_173, Images.verifyCode_174, Images.verifyCode_175, Images.verifyCode_176, Images.verifyCode_177, Images.verifyCode_178, Images.verifyCode_179, Images.verifyCode_180, Images.verifyCode_181, Images.verifyCode_182, Images.verifyCode_183, Images.verifyCode_184, Images.verifyCode_185, Images.verifyCode_186, Images.verifyCode_187, Images.verifyCode_188, Images.verifyCode_189, Images.verifyCode_190, Images.verifyCode_191, Images.verifyCode_192, Images.verifyCode_193, Images.verifyCode_194, Images.verifyCode_195, Images.verifyCode_196, Images.verifyCode_197, Images.verifyCode_198, Images.verifyCode_199, Images.verifyCode_200, Images.verifyCode_201, Images.verifyCode_202, Images.verifyCode_203, Images.verifyCode_204, Images.verifyCode_205, Images.verifyCode_206, Images.verifyCode_207, Images.verifyCode_208, Images.verifyCode_209, Images.verifyCode_210, Images.verifyCode_211, Images.verifyCode_212, Images.verifyCode_213, Images.verifyCode_214, Images.verifyCode_215, Images.verifyCode_216, Images.verifyCode_217, Images.verifyCode_218, Images.verifyCode_219, Images.verifyCode_220, Images.verifyCode_221, Images.verifyCode_222, Images.verifyCode_223, Images.verifyCode_224, Images.verifyCode_225, Images.verifyCode_226, Images.verifyCode_227, Images.verifyCode_228, Images.verifyCode_229, Images.verifyCode_230, Images.verifyCode_231, Images.verifyCode_232, Images.verifyCode_233, Images.verifyCode_234, Images.verifyCode_235, Images.verifyCode_236, Images.verifyCode_237, Images.verifyCode_238, Images.verifyCode_239, Images.verifyCode_240, Images.verifyCode_241, Images.verifyCode_242, Images.verifyCode_243, Images.verifyCode_244, Images.verifyCode_245, Images.verifyCode_246, Images.verifyCode_247, Images.verifyCode_248, Images.verifyCode_249, Images.verifyCode_250, Images.verifyCode_251, Images.verifyCode_252, Images.verifyCode_253, Images.verifyCode_254, Images.verifyCode_255, Images.verifyCode_256, Images.verifyCode_257, Images.verifyCode_258, Images.verifyCode_259, Images.verifyCode_260, Images.verifyCode_261, Images.verifyCode_262, Images.verifyCode_263, Images.verifyCode_264, Images.verifyCode_265, Images.verifyCode_266, Images.verifyCode_267, Images.verifyCode_268, Images.verifyCode_269, Images.verifyCode_270, Images.verifyCode_271, Images.verifyCode_272, Images.verifyCode_273, Images.verifyCode_274, Images.verifyCode_275, Images.verifyCode_276, Images.verifyCode_277, Images.verifyCode_278, Images.verifyCode_279, Images.verifyCode_280, Images.verifyCode_281, Images.verifyCode_282, Images.verifyCode_283, Images.verifyCode_284, Images.verifyCode_285, Images.verifyCode_286, Images.verifyCode_287, Images.verifyCode_288, Images.verifyCode_289, Images.verifyCode_290, Images.verifyCode_291, Images.verifyCode_292, Images.verifyCode_293, Images.verifyCode_294, Images.verifyCode_295, Images.verifyCode_296, Images.verifyCode_297, Images.verifyCode_298, Images.verifyCode_299, Images.verifyCode_300, Images.verifyCode_301, Images.verifyCode_302, Images.verifyCode_303, Images.verifyCode_304, Images.verifyCode_305, Images.verifyCode_306, Images.verifyCode_307, Images.verifyCode_308, Images.verifyCode_309, Images.verifyCode_310, Images.verifyCode_311, Images.verifyCode_312, Images.verifyCode_313, Images.verifyCode_314, Images.verifyCode_315, Images.verifyCode_316, Images.verifyCode_317, Images.verifyCode_318, Images.verifyCode_319, Images.verifyCode_320, Images.verifyCode_321, Images.verifyCode_322, Images.verifyCode_323, Images.verifyCode_324, Images.verifyCode_325, Images.verifyCode_326, Images.verifyCode_327, Images.verifyCode_328, Images.verifyCode_329, Images.verifyCode_330, Images.verifyCode_331, Images.verifyCode_332, Images.verifyCode_333, Images.verifyCode_334, Images.verifyCode_335, Images.verifyCode_336, Images.verifyCode_337, Images.verifyCode_338, Images.verifyCode_339, Images.verifyCode_340, Images.verifyCode_341, Images.verifyCode_342, Images.verifyCode_343, Images.verifyCode_344, Images.verifyCode_345, Images.verifyCode_346, Images.verifyCode_347, Images.verifyCode_348, Images.verifyCode_349, Images.verifyCode_350, Images.verifyCode_351, Images.verifyCode_352, Images.verifyCode_353, Images.verifyCode_354, Images.verifyCode_355, Images.verifyCode_356, Images.verifyCode_357, Images.verifyCode_358, Images.verifyCode_359, Images.verifyCode_360, Images.verifyCode_361, Images.verifyCode_362, Images.verifyCode_363, Images.verifyCode_364, Images.verifyCode_365, Images.verifyCode_366, Images.verifyCode_367, Images.verifyCode_368, Images.verifyCode_369, Images.verifyCode_370, Images.verifyCode_371, Images.verifyCode_372, Images.verifyCode_373, Images.verifyCode_374, Images.verifyCode_375, Images.verifyCode_376, Images.verifyCode_377, Images.verifyCode_378, Images.verifyCode_379, Images.verifyCode_380, Images.verifyCode_381, Images.verifyCode_382, Images.verifyCode_383, Images.verifyCode_384, Images.verifyCode_385, Images.verifyCode_386, Images.verifyCode_387, Images.verifyCode_388, Images.verifyCode_389, Images.verifyCode_390, Images.verifyCode_391, Images.verifyCode_392, Images.verifyCode_393, Images.verifyCode_394, Images.verifyCode_395, Images.verifyCode_396, Images.verifyCode_397, Images.verifyCode_398, Images.verifyCode_399, Images.verifyCode_400, Images.verifyCode_401, Images.verifyCode_402, Images.verifyCode_403, Images.verifyCode_404, Images.verifyCode_405, Images.verifyCode_406, Images.verifyCode_407, Images.verifyCode_408, Images.verifyCode_409, Images.verifyCode_410, Images.verifyCode_411, Images.verifyCode_412, Images.verifyCode_413, Images.verifyCode_414, Images.verifyCode_415, Images.verifyCode_416, Images.verifyCode_417, Images.verifyCode_418, Images.verifyCode_419, Images.verifyCode_420, Images.verifyCode_421, Images.verifyCode_422, Images.verifyCode_423, Images.verifyCode_424, Images.verifyCode_425, Images.verifyCode_426, Images.verifyCode_427, Images.verifyCode_428, Images.verifyCode_429, Images.verifyCode_430, Images.verifyCode_431, Images.verifyCode_432, Images.verifyCode_433, Images.verifyCode_434, Images.verifyCode_435, Images.verifyCode_436, Images.verifyCode_437, Images.verifyCode_438, Images.verifyCode_439, Images.verifyCode_440, Images.verifyCode_441, Images.verifyCode_442, Images.verifyCode_443, Images.verifyCode_444, Images.verifyCode_445, Images.verifyCode_446, Images.verifyCode_447, Images.verifyCode_448, Images.verifyCode_449, Images.verifyCode_450, Images.verifyCode_451, Images.verifyCode_452, Images.verifyCode_453, Images.verifyCode_454, Images.verifyCode_455, Images.verifyCode_456, Images.verifyCode_457, Images.verifyCode_458, Images.verifyCode_459, Images.verifyCode_460, Images.verifyCode_461, Images.verifyCode_462, Images.verifyCode_463, Images.verifyCode_464, Images.verifyCode_465, Images.verifyCode_466, Images.verifyCode_467, Images.verifyCode_468, Images.verifyCode_469, Images.verifyCode_470, Images.verifyCode_471, Images.verifyCode_472, Images.verifyCode_473, Images.verifyCode_474, Images.verifyCode_475, Images.verifyCode_476, Images.verifyCode_477, Images.verifyCode_478, Images.verifyCode_479, Images.verifyCode_480, Images.verifyCode_481, Images.verifyCode_482, Images.verifyCode_483, Images.verifyCode_484, Images.verifyCode_485, Images.verifyCode_486, Images.verifyCode_487, Images.verifyCode_488, Images.verifyCode_489, Images.verifyCode_490, Images.verifyCode_491, Images.verifyCode_492, Images.verifyCode_493, Images.verifyCode_494, Images.verifyCode_495, Images.verifyCode_496, Images.verifyCode_497, Images.verifyCode_498, Images.verifyCode_499, Images.verifyCode_500, Images.verifyCode_501, Images.verifyCode_502, Images.verifyCode_503, Images.verifyCode_504, Images.verifyCode_505, Images.verifyCode_506, Images.verifyCode_507, Images.verifyCode_508, Images.verifyCode_509, Images.verifyCode_510, Images.verifyCode_511, Images.verifyCode_512, Images.verifyCode_513, Images.verifyCode_514, Images.verifyCode_515, Images.verifyCode_516, Images.verifyCode_517, Images.verifyCode_518, Images.verifyCode_519, Images.verifyCode_520, Images.verifyCode_521, Images.verifyCode_522, Images.verifyCode_523, Images.verifyCode_524, Images.verifyCode_525, Images.verifyCode_526, Images.verifyCode_527, Images.verifyCode_528, Images.verifyCode_529, Images.verifyCode_530, Images.verifyCode_531, Images.verifyCode_532, Images.verifyCode_533, Images.verifyCode_534, Images.verifyCode_535, Images.verifyCode_536, Images.verifyCode_537, Images.verifyCode_538, Images.verifyCode_539, Images.verifyCode_540, Images.verifyCode_541, Images.verifyCode_542, Images.verifyCode_543, Images.verifyCode_544, Images.verifyCode_545, Images.verifyCode_546, Images.verifyCode_547, Images.verifyCode_548, Images.verifyCode_549, Images.verifyCode_550, Images.verifyCode_551, Images.verifyCode_552, Images.verifyCode_553, Images.verifyCode_554, Images.verifyCode_555, Images.verifyCode_556, Images.verifyCode_557, Images.verifyCode_558, Images.verifyCode_559, Images.verifyCode_560, Images.verifyCode_561, Images.verifyCode_562, Images.verifyCode_563, Images.verifyCode_564, Images.verifyCode_565, Images.verifyCode_566, Images.verifyCode_567, Images.verifyCode_568, Images.verifyCode_569, Images.verifyCode_570, Images.verifyCode_571, Images.verifyCode_572, Images.verifyCode_573, Images.verifyCode_574, Images.verifyCode_575, Images.verifyCode_576, Images.verifyCode_577, Images.verifyCode_578, Images.verifyCode_579, Images.verifyCode_580, Images.verifyCode_581, Images.verifyCode_582, Images.verifyCode_583, Images.verifyCode_584, Images.verifyCode_585, Images.verifyCode_586, Images.verifyCode_587, Images.verifyCode_588, Images.verifyCode_589, Images.verifyCode_590, Images.verifyCode_591, Images.verifyCode_592, Images.verifyCode_593, Images.verifyCode_594, Images.verifyCode_595, Images.verifyCode_596, Images.verifyCode_597, Images.verifyCode_598, Images.verifyCode_599, Images.verifyCode_600, Images.verifyCode_601, Images.verifyCode_602, Images.verifyCode_603, Images.verifyCode_604, Images.verifyCode_605, Images.verifyCode_606, Images.verifyCode_607, Images.verifyCode_608, Images.verifyCode_609, Images.verifyCode_610, Images.verifyCode_611, Images.verifyCode_612, Images.verifyCode_613, Images.verifyCode_614, Images.verifyCode_615, Images.verifyCode_616, Images.verifyCode_617, Images.verifyCode_618, Images.verifyCode_619, Images.verifyCode_620, Images.verifyCode_621, Images.verifyCode_622, Images.verifyCode_623, Images.verifyCode_624, Images.verifyCode_625, Images.verifyCode_626, Images.verifyCode_627, Images.verifyCode_628, Images.verifyCode_629, Images.verifyCode_630, Images.verifyCode_631, Images.verifyCode_632, Images.verifyCode_633, Images.verifyCode_634, Images.verifyCode_635, Images.verifyCode_636, Images.verifyCode_637, Images.verifyCode_638, Images.verifyCode_639, Images.verifyCode_640, Images.verifyCode_641, Images.verifyCode_642, Images.verifyCode_643, Images.verifyCode_644, Images.verifyCode_645, Images.verifyCode_646, Images.verifyCode_647, Images.verifyCode_648, Images.verifyCode_649, Images.verifyCode_650, Images.verifyCode_651, Images.verifyCode_652, Images.verifyCode_653, Images.verifyCode_654, Images.verifyCode_655, Images.verifyCode_656, Images.verifyCode_657, Images.verifyCode_658, Images.verifyCode_659, Images.verifyCode_660, Images.verifyCode_661, Images.verifyCode_662, Images.verifyCode_663, Images.verifyCode_664, Images.verifyCode_665, Images.verifyCode_666, Images.verifyCode_667, Images.verifyCode_668, Images.verifyCode_669, Images.verifyCode_670, Images.verifyCode_671, Images.verifyCode_672, Images.verifyCode_673, Images.verifyCode_674, Images.verifyCode_675, Images.verifyCode_676, Images.verifyCode_677, Images.verifyCode_678, Images.verifyCode_679, Images.verifyCode_680, Images.verifyCode_681, Images.verifyCode_682, Images.verifyCode_683, Images.verifyCode_684, Images.verifyCode_685, Images.verifyCode_686, Images.verifyCode_687, Images.verifyCode_688, Images.verifyCode_689, Images.verifyCode_690, Images.verifyCode_691, Images.verifyCode_692, Images.verifyCode_693, Images.verifyCode_694, Images.verifyCode_695, Images.verifyCode_696, Images.verifyCode_697, Images.verifyCode_698, Images.verifyCode_699, Images.verifyCode_700, Images.verifyCode_701, Images.verifyCode_702, Images.verifyCode_703, Images.verifyCode_704, Images.verifyCode_705, Images.verifyCode_706, Images.verifyCode_707, Images.verifyCode_708, Images.verifyCode_709, Images.verifyCode_710, Images.verifyCode_711, Images.verifyCode_712, Images.verifyCode_713, Images.verifyCode_714, Images.verifyCode_715, Images.verifyCode_716, Images.verifyCode_717, Images.verifyCode_718, Images.verifyCode_719, Images.verifyCode_720, Images.verifyCode_721, Images.verifyCode_722, Images.verifyCode_723, Images.verifyCode_724, Images.verifyCode_725, Images.verifyCode_726, Images.verifyCode_727, Images.verifyCode_728, Images.verifyCode_729, Images.verifyCode_730, Images.verifyCode_731, Images.verifyCode_732, Images.verifyCode_733, Images.verifyCode_734, Images.verifyCode_735, Images.verifyCode_736, Images.verifyCode_737, Images.verifyCode_738, Images.verifyCode_739, Images.verifyCode_740, Images.verifyCode_741, Images.verifyCode_742, Images.verifyCode_743, Images.verifyCode_744, Images.verifyCode_745, Images.verifyCode_746, Images.verifyCode_747, Images.verifyCode_748, Images.verifyCode_749, Images.verifyCode_750, Images.verifyCode_751, Images.verifyCode_752, Images.verifyCode_753, Images.verifyCode_754, Images.verifyCode_755, Images.verifyCode_756, Images.verifyCode_757, Images.verifyCode_758, Images.verifyCode_759, Images.verifyCode_760, Images.verifyCode_761, Images.verifyCode_762, Images.verifyCode_763, Images.verifyCode_764, Images.verifyCode_765, Images.verifyCode_766, Images.verifyCode_767, Images.verifyCode_768, Images.verifyCode_769, Images.verifyCode_770, Images.verifyCode_771, Images.verifyCode_772, Images.verifyCode_773, Images.verifyCode_774, Images.verifyCode_775, Images.verifyCode_776, Images.verifyCode_777, Images.verifyCode_778, Images.verifyCode_779, Images.verifyCode_780, Images.verifyCode_781, Images.verifyCode_782, Images.verifyCode_783, Images.verifyCode_784, Images.verifyCode_785, Images.verifyCode_786, Images.verifyCode_787, Images.verifyCode_788, Images.verifyCode_789, Images.verifyCode_790, Images.verifyCode_791, Images.verifyCode_792, Images.verifyCode_793, Images.verifyCode_794, Images.verifyCode_795, Images.verifyCode_796, Images.verifyCode_797, Images.verifyCode_798, Images.verifyCode_799, Images.verifyCode_800, Images.verifyCode_801, Images.verifyCode_802, Images.verifyCode_803, Images.verifyCode_804, Images.verifyCode_805, Images.verifyCode_806, Images.verifyCode_807, Images.verifyCode_808, Images.verifyCode_809, Images.verifyCode_810, Images.verifyCode_811, Images.verifyCode_812, Images.verifyCode_813, Images.verifyCode_814, Images.verifyCode_815, Images.verifyCode_816, Images.verifyCode_817, Images.verifyCode_818, Images.verifyCode_819, Images.verifyCode_820, Images.verifyCode_821, Images.verifyCode_822, Images.verifyCode_823, Images.verifyCode_824, Images.verifyCode_825, Images.verifyCode_826, Images.verifyCode_827, Images.verifyCode_828, Images.verifyCode_829, Images.verifyCode_830, Images.verifyCode_831, Images.verifyCode_832, Images.verifyCode_833, Images.verifyCode_834, Images.verifyCode_835, Images.verifyCode_836, Images.verifyCode_837, Images.verifyCode_838, Images.verifyCode_839, Images.verifyCode_840, Images.verifyCode_841, Images.verifyCode_842, Images.verifyCode_843, Images.verifyCode_844, Images.verifyCode_845, Images.verifyCode_846, Images.verifyCode_847, Images.verifyCode_848, Images.verifyCode_849, Images.verifyCode_850, Images.verifyCode_851, Images.verifyCode_852, Images.verifyCode_853, Images.verifyCode_854, Images.verifyCode_855, Images.verifyCode_856, Images.verifyCode_857, Images.verifyCode_858, Images.verifyCode_859, Images.verifyCode_860, Images.verifyCode_861, Images.verifyCode_862, Images.verifyCode_863, Images.verifyCode_864, Images.verifyCode_865, Images.verifyCode_866, Images.verifyCode_867, Images.verifyCode_868, Images.verifyCode_869, Images.verifyCode_870, Images.verifyCode_871, Images.verifyCode_872, Images.verifyCode_873, Images.verifyCode_874, Images.verifyCode_875, Images.verifyCode_876, Images.verifyCode_877, Images.verifyCode_878, Images.verifyCode_879, Images.verifyCode_880, Images.verifyCode_881, Images.verifyCode_882, Images.verifyCode_883, Images.verifyCode_884, Images.verifyCode_885, Images.verifyCode_886, Images.verifyCode_887, Images.verifyCode_888, Images.verifyCode_889, Images.verifyCode_890, Images.verifyCode_891, Images.verifyCode_892, Images.verifyCode_893, Images.verifyCode_894, Images.verifyCode_895, Images.verifyCode_896, Images.verifyCode_897, Images.verifyCode_898, Images.verifyCode_899, Images.verifyCode_900, Images.verifyCode_901, Images.verifyCode_902, Images.verifyCode_903, Images.verifyCode_904, Images.verifyCode_905, Images.verifyCode_906, Images.verifyCode_907, Images.verifyCode_908, Images.verifyCode_909, Images.verifyCode_910, Images.verifyCode_911, Images.verifyCode_912, Images.verifyCode_913, Images.verifyCode_914, Images.verifyCode_915, Images.verifyCode_916, Images.verifyCode_917, Images.verifyCode_918, Images.verifyCode_919, Images.verifyCode_920, Images.verifyCode_921, Images.verifyCode_922, Images.verifyCode_923, Images.verifyCode_924, Images.verifyCode_925, Images.verifyCode_926, Images.verifyCode_927, Images.verifyCode_928, Images.verifyCode_929, Images.verifyCode_930, Images.verifyCode_931, Images.verifyCode_932, Images.verifyCode_933, Images.verifyCode_934, Images.verifyCode_935, Images.verifyCode_936, Images.verifyCode_937, Images.verifyCode_938, Images.verifyCode_939, Images.verifyCode_940, Images.verifyCode_941, Images.verifyCode_942, Images.verifyCode_943, Images.verifyCode_944, Images.verifyCode_945, Images.verifyCode_946, Images.verifyCode_947, Images.verifyCode_948, Images.verifyCode_949, Images.verifyCode_950, Images.verifyCode_951, Images.verifyCode_952, Images.verifyCode_953, Images.verifyCode_954, Images.verifyCode_955, Images.verifyCode_956, Images.verifyCode_957, Images.verifyCode_958, Images.verifyCode_959, Images.verifyCode_960, Images.verifyCode_961, Images.verifyCode_962, Images.verifyCode_963, Images.verifyCode_964, Images.verifyCode_965, Images.verifyCode_966, Images.verifyCode_967, Images.verifyCode_968, Images.verifyCode_969, Images.verifyCode_970, Images.verifyCode_971, Images.verifyCode_972, Images.verifyCode_973, Images.verifyCode_974, Images.verifyCode_975, Images.verifyCode_976, Images.verifyCode_977, Images.verifyCode_978, Images.verifyCode_979, Images.verifyCode_980, Images.verifyCode_981, Images.verifyCode_982, Images.verifyCode_983, Images.verifyCode_984]
def lcode (i : Nat) : List (BitVec 32) := ((lChunks.drop (i / 256)).flatten).drop (i % 256)
theorem foldl_append_flatten' : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten' l (a ++ c)]
set_option maxRecDepth 200000 in
theorem lChunks_foldl : Images.verifyCode = lChunks.foldl (· ++ ·) [] := by
  delta Images.verifyCode lChunks
  rfl
theorem lChunks_flatten : Images.verifyCode = lChunks.flatten := by
  rw [lChunks_foldl, foldl_append_flatten', List.nil_append]
set_option maxRecDepth 200000 in
theorem lChunks_ok : (lChunks.dropLast.all fun c => c.length == 256) = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem lChunks_le : (lChunks.all fun c => decide (c.length ≤ 256)) = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem lChunks_length : lChunks.length = 985 := by decide +kernel
theorem drop_chunks' : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this
theorem flatten_len_le' : ∀ (cs : List (List (BitVec 32))),
    (cs.all fun c => decide (c.length ≤ 256)) = true → cs.flatten.length ≤ 256 * cs.length
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := flatten_len_le' cs h.2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega
theorem verifyCode_length_le : Images.verifyCode.length ≤ 256 * 985 := by
  rw [lChunks_flatten, ← lChunks_length]; exact flatten_len_le' _ lChunks_le
theorem lcode_eq (i : Nat) (hi : i / 256 < 985) : lcode i = Images.verifyCode.drop i := by
  unfold lcode
  rw [lChunks_flatten, ← drop_chunks' lChunks (i / 256) lChunks_ok (by rw [lChunks_length]; exact hi),
    List.drop_drop]
  congr 1; omega
theorem lcodeAt (i : Nat) (hi : i < 251927) : CodeAt Images.verifyImage (pcOf i) (lcode i) := by
  have hl := verifyCode_length_le
  have hp : (pcOf i).toNat = 0x1000 + 4 * i := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  rw [lcode_eq i (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; omega
  · rw [hp]; omega
  · rw [hp, List.length_drop]; omega
  · rw [hp, show (0x1000 + 4 * i - 0x1000) / 4 = i by omega]
    exact List.prefix_refl _
def lstBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lstBeq f as bs
  | _, _ => false
theorem lstBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lstBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [lstBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [lstBeq] at h
    | cons b bs =>
      simp only [lstBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]
def rfBeq (a b : RegFile) : Bool := lstBeq E.beq a.fields b.fields
theorem rfBeq_eq {a b : RegFile} (h : rfBeq a b = true) : a = b := by
  have := lstBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl
def wBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2
theorem wBeq_eq {a b : Addr × E} (h : wBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [wBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]
def stBeq (a b : SymState) : Bool :=
  rfBeq a.regs b.regs && lstBeq wBeq a.mem b.mem && lstBeq Oblig.beq a.obl b.obl
theorem stBeq_eq {a b : SymState} (h : stBeq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [stBeq, Bool.and_eq_true] at h
  rw [rfBeq_eq h.1.1, lstBeq_eq (fun _ _ => wBeq_eq) h.1.2, lstBeq_eq (fun _ _ => Oblig.beq_eq) h.2]
def resBeq (a b : Result) : Bool :=
  stBeq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles
theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [stBeq_eq h1, E.beq_eq h2, h3, h4, h5]
def rOK (o : Option Result) (r : Result) : Bool :=
  match o with
  | some r' => resBeq r' r
  | none => false
theorem rOK_eq {o : Option Result} {r : Result} (h : rOK o r = true) : o = some r := by
  cases o with
  | none => simp [rOK] at h
  | some r' => simp only [rOK] at h; rw [resBeq_eq h]
def vrun (p f : Nat) : Option Result := symRun {} (lcode p) (pcOf p) f
def ttabIdx : Nat := 64072
def ckSlot (c : Nat) : Nat := 63832 + 32 * c
def triBaseTab : List Nat :=
  [58411,58470,58527,58582,58635,58686,58735,58782,58826,58883,58938,58991,59042,59091,59138,59183,59225,59280,59333,59384,59433,59480,59525,59568,59608,59661,59712,59761,59808,59853,59896,59937,59975,60026,60075,60122,60167,60210,60251,60290,60326,60375,60422,60467,60510,60551,60590,60627,60661,60708,60753,60796,60837,60876,60913,60948,60980,61024,61066,61106,61144,61180,61214,61246,61275,61334,61391,61446,61499,61550,61599,61646,61690,61747,61802,61855,61906,61955,62002,62047,62089,62144,62197,62248,62297,62344,62389,62432,62472,62525,62576,62625,62672,62717,62760,62801,62839,62890,62939,62986,63031,63074,63115,63154,63190,63239,63286,63331,63374,63415,63454,63491,63525,63572,63617,63660,63701,63740,63777,150144,150176,150220,150262,150302,150340,150376,150410,150442,150471,150530,150587,150642,150695,150746,150795,150842,150886,150943,150998,151051,151102,151151,151198,151243,151285,151340,151393,151444,151493,151540,151585,151628,151668,151721,151772,151821,151868,151913,151956,151997,152035,152086,152135,152182,152227,152270,152311,152350,152386,152435,152482,152527,152570,152611,152650,152687,152721,152768,152813,152856,152897,152936,152973,153008,153040,153084,153126,153166,153204,153240,153274,153306,153335,153394,153451,153506,153559,153610,153659,153706,153750,153807,153862,153915,153966,154015,154062,154107,154149,154204,154257,154308,154357,154404,154449,154492,154532,154585,154636,154685,154732,154777,154820,154861,154899,154950,154999,155046,155091,155134,155175,155214,155250,155299,155346,155391,155434,155475,155514,155551,155585,155632,155677,155720,155761,155800,155837,155872,155904,155948,155990,156030,156068,156104,156138,156170,156199,156258,156315,156370,156423,156474,156523,156570,156614,156671,156726,156779,156830,156879,156926,156971,157013,157068,157121,157172,157221,157268,157313,157356,157396,157449,157500,157549,157596,157641,157684,157725,157763,157814,157863,157910,157955,157998,158039,158078,158114,158163,158210,158255,158298,158339,158378,158415,158449,158496,158541,158584,158625,158664,158701,158736,158768,158812,158854,158894,158932,158968,159002,159034,159063,159122,159179,159234,159287,159338,159387,159434,159478,159535,159590,159643,159694,159743,159790,159835,159877,159932,159985,160036,160085,160132,160177,160220,160260,160313,160364,160413,160460,160505,160548,160589,160627,160678,160727,160774,160819,160862,160903,160942,160978,161027,161074,161119,161162,161203,161242,161279,161313,161360,161405,161448,161489,161528,161565,161600,161632,161676,161718,161758,161796,161832,161866,161898,161927,161986,162043,162098,162151,162202,162251,162298,162342,162399,162454,162507,162558,162607,162654,162699,162741,162796,162849,162900,162949,162996,163041,163084,163124,163177,163228,163277,163324,163369,163412,163453,163491,163542,163591,163638,163683,163726,163767,163806,163842,163891,163938,163983,164026,164067,164106,164143,164177,164224,164269,164312,164353,164392,164429,164464,164496,164540,164582,164622,164660,164696,164730,164762,164791,164850,164907,164962,165015,165066,165115,165162,165206,165263,165318,165371,165422,165471,165518,165563,165605,165660,165713,165764,165813,165860,165905,165948,165988,166041,166092,166141,166188,166233,166276,166317,166355,166406,166455,166502,166547,166590,166631,166670,166706,166755,166802,166847,166890,166931,166970,167007,167041,167088,167133,167176,167217,167256,167293,167328,167360,167404,167446,167486,167524,167560,167594,167626,167655,167714,167771,167826,167879,167930,167979,168026,168070,168127,168182,168235,168286,168335,168382,168427,168469,168524,168577,168628,168677,168724,168769,168812,168852,168905,168956,169005,169052,169097,169140,169181,169219,169270,169319,169366,169411,169454,169495,169534,169570,169619,169666,169711,169754,169795,169834,169871,169905,169952,169997,170040,170081,170120,170157,170192,170224,170268,170310,170350,170388,170424,170458,170490,170519,170578,170635,170690,170743,170794,170843,170890,170934,170991,171046,171099,171150,171199,171246,171291,171333,171388,171441,171492,171541,171588,171633,171676,171716,171769,171820,171869,171916,171961,172004,172045,172083,172134,172183,172230,172275,172318,172359,172398,172434,172483,172530,172575,172618,172659,172698,172735,172769,172816,172861,172904,172945,172984,173021,173056,173088,173132,173174,173214,173252,173288,173322,173354,173383,173442,173499,173554,173607,173658,173707,173754,173798,173855,173910,173963,174014,174063,174110,174155,174197,174252,174305,174356,174405,174452,174497,174540,174580,174633,174684,174733,174780,174825,174868,174909,174947,174998,175047,175094,175139,175182,175223,175262,175298,175347,175394,175439,175482,175523,175562,175599,175633,175680,175725,175768,175809,175848,175885,175920,175952,175996,176038,176078,176116,176152,176186,176218,176247,176306,176363,176418,176471,176522,176571,176618,176662,176719,176774,176827,176878,176927,176974,177019,177061,177116,177169,177220,177269,177316,177361,177404,177444,177497,177548,177597,177644,177689,177732,177773,177811,177862,177911,177958,178003,178046,178087,178126,178162,178211,178258,178303,178346,178387,178426,178463,178497,178544,178589,178632,178673,178712,178749,178784,178816,178860,178902,178942,178980,179016,179050,179082,179111,179170,179227,179282,179335,179386,179435,179482,179526,179583,179638,179691,179742,179791,179838,179883,179925,179980,180033,180084,180133,180180,180225,180268,180308,180361,180412,180461,180508,180553,180596,180637,180675,180726,180775,180822,180867,180910,180951,180990,181026,181075,181122,181167,181210,181251,181290,181327,181361,181408,181453,181496,181537,181576,181613,181648,181680,181724,181766,181806,181844,181880,181914,181946,181975,182033,182089,182143,182195,182245,182293,182339,182382,182438,182492,182544,182594,182642,182688,182732,182773,182827,182879,182929,182977,183023,183067,183109,183148,183200,183250,183298,183344,183388,183430,183470,183507,183557,183605,183651,183695,183737,183777,183815,183850,183898,183944,183988,184030,184070,184108,184144,184177,184223,184267,184309,184349,184387,184423,184457,184488,184531,184572,184611,184648,184683,184716,184747]
def posReg (d : Nat) : Reg :=
  match d with
  | 0 => .x0 | 1 => .x7 | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | _ => .x26
def posE (d : Nat) : E := RegFile.init.get (posReg d)
def bumpE : E := .bin .add (.reg .x25) (.reg .x28)
def s9E (first : Bool) : E := if first then .reg .x27 else bumpE
def kAt (rb : Reg) (off : Word) (k : Nat) : Addr := ⟨some (.reg rb), off + BitVec.ofNat 64 k⟩
def lAt (rb : Reg) (off : Word) (k : Nat) : E := .ld (addC (.reg rb) (off + BitVec.ofNat 64 k))
def headJ (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (addC (.reg rb) off) 48)).set .x25 (s9E first),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, s9E first)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩, .c (pcOf tgt), .jump, 6, 6⟩
def headR (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 7 else 6
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 bumpE,
    [(kAt rb off 16, .bin (.st .b 4) bumpE (posE d)), (kAt rb off 24, .reg .x4)],
    [.align8 (.reg rb), .valid (kAt rb off 20) 1, .valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def rungR (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 2 else 1
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (posE d))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 17⟩ 1]⟩, .c (pcOf (p + n)), .ecall, n, n⟩
def copyRegs (rb : Reg) (off : Word) : RegFile :=
  (RegFile.init.set .x3 (lAt rb off 48)).set .x14 (lAt rb off 56)
def copyMem (rb : Reg) (off : Word) (slot : Nat) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (slot + 8)⟩, lAt rb off 56), (⟨none, BitVec.ofNat 64 slot⟩, lAt rb off 48)]
def copyObl (rb : Reg) (off : Word) : List Oblig := [.valid (kAt rb off 56) 8, .valid (kAt rb off 48) 8]
def copyJ (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 (s9E first), copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 6, 6⟩
def copyF (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 bumpE, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 5)), .fuel, 5, 5⟩
def copyN (rb : Reg) (off : Word) (slot : Nat) (tgt : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 5, 5⟩
def hOff (i d : Nat) : Word := BitVec.ofNat 64 (64 * i + 8 * d) - 2048
def hKey (i d : Nat) : Addr := ⟨some (.reg .x28), hOff i d⟩
def hLoad (i d : Nat) : E := addC (.reg .x28) (BitVec.ofNat 64 (i + 256 * d))
def headJH (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf tgt), .jump, 5, 5⟩
def ecallR (p : Nat) : Result := ⟨SymState.init, .c (pcOf p), .ecall, 0, 0⟩
def landOff (d : Nat) : Nat := if d = 6 then 2 else 1
def headRH (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  let n := if slot.isSome then 5 else 4
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def headRV (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + 4)), .ecall, 4, 4⟩
def copyFH (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 4)), .fuel, 4, 4⟩
def shE (w : Reg) (b : Nat) : E :=
  if b < 9 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (9 - b)))
  else if 9 < b then .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b - 9)))
  else .reg w
def xJ (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .add (.bin .and (shE w b) (.reg mreg)) (.reg .x15)), [], []⟩,
    .bin .and (.bin .add (.bin .add (.bin .and (shE w b) (.reg mreg)) (.reg .x15)) (.c imm)) (.c (~~~1#64)),
    .jump, (if b = 9 then 3 else 4), (if b = 9 then 3 else 4)⟩
def xbfJ (w : Reg) (imm : Word) : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .sll (.bin .srl (.reg w) (.c 54)) (.c 9)), [], []⟩,
    .bin .and (.bin .add (.bin .sll (.bin .srl (.reg w) (.c 54)) (.c 9)) (.c imm)) (.c (~~~1#64)),
    .jump, 3, 3⟩
def ctabX : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .sub (.reg .x15) (.bin .sll (.reg .x29) (.c 7))), [], []⟩,
    .bin .and (.bin .add (.bin .sub (.reg .x15) (.bin .sll (.reg .x29) (.c 7))) (.c (-1824))) (.c (~~~1#64)),
    .jump, 3, 3⟩
def retR : Result := ⟨⟨RegFile.init, [], []⟩, .bin .and (.reg .x1) (.c (~~~1#64)), .jump, 1, 1⟩
def offL (i : Nat) : Word := BitVec.ofNat 64 (64 * (42 - i)) - BitVec.ofNat 64 1024
def slotL (i : Nat) : Nat := if i = 0 then 768 else 784 + 16 * i
def hSlot (i d : Nat) : Option Nat := if d = 6 then some (slotL i) else none
def triBase (t dB dC : Nat) : Nat := triBaseTab.getD (64 * t + 8 * dB + dC) 0
def partLen (d : Nat) : Nat := if d = 7 then 4 else if d = 6 then 5 else 18 - 2 * d
def pcB (t dB dC : Nat) : Nat := triBase t dB dC + 15
def pcC (t dB dC : Nat) : Nat := pcB t dB dC + partLen dB
def pcX (t dB dC : Nat) : Nat := pcC t dB dC + partLen dC
def entW (t k : Nat) : Nat := ttabIdx + 128 * k + 8 * t
def rungsOK (d0 slot p : Nat) : Bool :=
  (List.range' d0 (7 - d0)).all fun m =>
    rOK (vrun (p + 2 * (m - d0)) 3) (rungR m (if m = 6 then some slot else none) (p + 2 * (m - d0)))
def partOK (i d p : Nat) : Bool :=
  if d = 7 then rOK (vrun p 4) (copyFH .x22 (offL i) (slotL i) p)
  else rOK (vrun p 8) (headRV .x22 (offL i) d (if d = 6 then some (slotL i) else none) p i) &&
    rungsOK (d + 1) (slotL i) (p + 5)
def entCheck (t k : Nat) : Bool :=
  if k % 8 = 7 then
    rOK (vrun (entW t k) 7) (copyN .x22 (offL (3 * t)) (slotL (3 * t)) (pcB t (k / 8 % 8) (k / 64)))
  else rOK (vrun (entW t k) 7) (headJH .x22 (offL (3 * t))
      (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)) (3 * t) (k % 8) (hSlot (3 * t) (k % 8))) &&
    rOK (vrun (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)) 1)
      (ecallR (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)))
def xOK (t dB dC : Nat) : Bool :=
  if t = 13 then rOK (vrun (pcX t dB dC) 4) ctabX
  else if t = 5 ∨ t = 12 then rOK (vrun (pcX t dB dC) 4)
    (xbfJ (if t + 1 < 7 then .x16 else .x17) (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760))
  else rOK (vrun (pcX t dB dC) 5)
    (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
      (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760))
def blkCheck (t dB dC : Nat) : Bool :=
  rungsOK 0 (slotL (3 * t)) (triBase t dB dC) && partOK (3 * t + 1) dB (pcB t dB dC) &&
    partOK (3 * t + 2) dC (pcC t dB dC) && xOK t dB dC
def triCheck (t lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => entCheck t k) &&
    ((List.range' (lo / 8) (n / 8)).all fun q => blkCheck t (q / 8) (q % 8))
def ckCheck : Bool :=
  (List.range 8).all fun c => partOK 42 c (ckSlot c)
end SigGolfCandidate.T3M
