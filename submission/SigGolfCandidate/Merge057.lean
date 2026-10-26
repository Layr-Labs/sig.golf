import SigGolfCandidate.Merge041
import SigGolfCandidate.Merge056

-- ==== merged from T3M_Verify_ChainCheckT0 ====
section
-- serialization only (no declarations used): keeps this ~14 GB module from building in parallel with the other heavy ones under the verifier's 2-job / 24 GiB limit

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_0_0 : triCheck 0 0 16 = true := by decide +kernel
private theorem triCheck_part_0_16 : triCheck 0 16 16 = true := by decide +kernel
private theorem triCheck_part_0_32 : triCheck 0 32 16 = true := by decide +kernel
private theorem triCheck_part_0_48 : triCheck 0 48 16 = true := by decide +kernel
private theorem triCheck_part_0_64 : triCheck 0 64 16 = true := by decide +kernel
private theorem triCheck_part_0_80 : triCheck 0 80 16 = true := by decide +kernel
private theorem triCheck_part_0_96 : triCheck 0 96 16 = true := by decide +kernel
private theorem triCheck_part_0_112 : triCheck 0 112 16 = true := by decide +kernel
private theorem triCheck_part_0_128 : triCheck 0 128 16 = true := by decide +kernel
private theorem triCheck_part_0_144 : triCheck 0 144 16 = true := by decide +kernel
private theorem triCheck_part_0_160 : triCheck 0 160 16 = true := by decide +kernel
private theorem triCheck_part_0_176 : triCheck 0 176 16 = true := by decide +kernel
private theorem triCheck_part_0_192 : triCheck 0 192 16 = true := by decide +kernel
private theorem triCheck_part_0_208 : triCheck 0 208 16 = true := by decide +kernel
private theorem triCheck_part_0_224 : triCheck 0 224 16 = true := by decide +kernel
private theorem triCheck_part_0_240 : triCheck 0 240 16 = true := by decide +kernel
theorem triCheck_0_0 : triCheck 0 0 256 = true := by
  exact @triCheck_add 0 0 16 240 (by decide +kernel) triCheck_part_0_0 (@triCheck_add 0 16 16 224 (by decide +kernel) triCheck_part_0_16 (@triCheck_add 0 32 16 208 (by decide +kernel) triCheck_part_0_32 (@triCheck_add 0 48 16 192 (by decide +kernel) triCheck_part_0_48 (@triCheck_add 0 64 16 176 (by decide +kernel) triCheck_part_0_64 (@triCheck_add 0 80 16 160 (by decide +kernel) triCheck_part_0_80 (@triCheck_add 0 96 16 144 (by decide +kernel) triCheck_part_0_96 (@triCheck_add 0 112 16 128 (by decide +kernel) triCheck_part_0_112 (@triCheck_add 0 128 16 112 (by decide +kernel) triCheck_part_0_128 (@triCheck_add 0 144 16 96 (by decide +kernel) triCheck_part_0_144 (@triCheck_add 0 160 16 80 (by decide +kernel) triCheck_part_0_160 (@triCheck_add 0 176 16 64 (by decide +kernel) triCheck_part_0_176 (@triCheck_add 0 192 16 48 (by decide +kernel) triCheck_part_0_192 (@triCheck_add 0 208 16 32 (by decide +kernel) triCheck_part_0_208 (@triCheck_add 0 224 16 16 (by decide +kernel) triCheck_part_0_224 (triCheck_part_0_240)))))))))))))))
private theorem triCheck_part_0_256 : triCheck 0 256 16 = true := by decide +kernel
private theorem triCheck_part_0_272 : triCheck 0 272 16 = true := by decide +kernel
private theorem triCheck_part_0_288 : triCheck 0 288 16 = true := by decide +kernel
private theorem triCheck_part_0_304 : triCheck 0 304 16 = true := by decide +kernel
private theorem triCheck_part_0_320 : triCheck 0 320 16 = true := by decide +kernel
private theorem triCheck_part_0_336 : triCheck 0 336 16 = true := by decide +kernel
private theorem triCheck_part_0_352 : triCheck 0 352 16 = true := by decide +kernel
private theorem triCheck_part_0_368 : triCheck 0 368 16 = true := by decide +kernel
private theorem triCheck_part_0_384 : triCheck 0 384 16 = true := by decide +kernel
private theorem triCheck_part_0_400 : triCheck 0 400 16 = true := by decide +kernel
private theorem triCheck_part_0_416 : triCheck 0 416 16 = true := by decide +kernel
private theorem triCheck_part_0_432 : triCheck 0 432 16 = true := by decide +kernel
private theorem triCheck_part_0_448 : triCheck 0 448 16 = true := by decide +kernel
private theorem triCheck_part_0_464 : triCheck 0 464 16 = true := by decide +kernel
private theorem triCheck_part_0_480 : triCheck 0 480 16 = true := by decide +kernel
private theorem triCheck_part_0_496 : triCheck 0 496 16 = true := by decide +kernel
theorem triCheck_0_1 : triCheck 0 256 256 = true := by
  exact @triCheck_add 0 256 16 240 (by decide +kernel) triCheck_part_0_256 (@triCheck_add 0 272 16 224 (by decide +kernel) triCheck_part_0_272 (@triCheck_add 0 288 16 208 (by decide +kernel) triCheck_part_0_288 (@triCheck_add 0 304 16 192 (by decide +kernel) triCheck_part_0_304 (@triCheck_add 0 320 16 176 (by decide +kernel) triCheck_part_0_320 (@triCheck_add 0 336 16 160 (by decide +kernel) triCheck_part_0_336 (@triCheck_add 0 352 16 144 (by decide +kernel) triCheck_part_0_352 (@triCheck_add 0 368 16 128 (by decide +kernel) triCheck_part_0_368 (@triCheck_add 0 384 16 112 (by decide +kernel) triCheck_part_0_384 (@triCheck_add 0 400 16 96 (by decide +kernel) triCheck_part_0_400 (@triCheck_add 0 416 16 80 (by decide +kernel) triCheck_part_0_416 (@triCheck_add 0 432 16 64 (by decide +kernel) triCheck_part_0_432 (@triCheck_add 0 448 16 48 (by decide +kernel) triCheck_part_0_448 (@triCheck_add 0 464 16 32 (by decide +kernel) triCheck_part_0_464 (@triCheck_add 0 480 16 16 (by decide +kernel) triCheck_part_0_480 (triCheck_part_0_496)))))))))))))))
private theorem triCheck_part_1_0 : triCheck 1 0 16 = true := by decide +kernel
private theorem triCheck_part_1_16 : triCheck 1 16 16 = true := by decide +kernel
private theorem triCheck_part_1_32 : triCheck 1 32 16 = true := by decide +kernel
private theorem triCheck_part_1_48 : triCheck 1 48 16 = true := by decide +kernel
private theorem triCheck_part_1_64 : triCheck 1 64 16 = true := by decide +kernel
private theorem triCheck_part_1_80 : triCheck 1 80 16 = true := by decide +kernel
private theorem triCheck_part_1_96 : triCheck 1 96 16 = true := by decide +kernel
private theorem triCheck_part_1_112 : triCheck 1 112 16 = true := by decide +kernel
private theorem triCheck_part_1_128 : triCheck 1 128 16 = true := by decide +kernel
private theorem triCheck_part_1_144 : triCheck 1 144 16 = true := by decide +kernel
private theorem triCheck_part_1_160 : triCheck 1 160 16 = true := by decide +kernel
private theorem triCheck_part_1_176 : triCheck 1 176 16 = true := by decide +kernel
private theorem triCheck_part_1_192 : triCheck 1 192 16 = true := by decide +kernel
private theorem triCheck_part_1_208 : triCheck 1 208 16 = true := by decide +kernel
private theorem triCheck_part_1_224 : triCheck 1 224 16 = true := by decide +kernel
private theorem triCheck_part_1_240 : triCheck 1 240 16 = true := by decide +kernel
theorem triCheck_1_0 : triCheck 1 0 256 = true := by
  exact @triCheck_add 1 0 16 240 (by decide +kernel) triCheck_part_1_0 (@triCheck_add 1 16 16 224 (by decide +kernel) triCheck_part_1_16 (@triCheck_add 1 32 16 208 (by decide +kernel) triCheck_part_1_32 (@triCheck_add 1 48 16 192 (by decide +kernel) triCheck_part_1_48 (@triCheck_add 1 64 16 176 (by decide +kernel) triCheck_part_1_64 (@triCheck_add 1 80 16 160 (by decide +kernel) triCheck_part_1_80 (@triCheck_add 1 96 16 144 (by decide +kernel) triCheck_part_1_96 (@triCheck_add 1 112 16 128 (by decide +kernel) triCheck_part_1_112 (@triCheck_add 1 128 16 112 (by decide +kernel) triCheck_part_1_128 (@triCheck_add 1 144 16 96 (by decide +kernel) triCheck_part_1_144 (@triCheck_add 1 160 16 80 (by decide +kernel) triCheck_part_1_160 (@triCheck_add 1 176 16 64 (by decide +kernel) triCheck_part_1_176 (@triCheck_add 1 192 16 48 (by decide +kernel) triCheck_part_1_192 (@triCheck_add 1 208 16 32 (by decide +kernel) triCheck_part_1_208 (@triCheck_add 1 224 16 16 (by decide +kernel) triCheck_part_1_224 (triCheck_part_1_240)))))))))))))))
private theorem triCheck_part_1_256 : triCheck 1 256 16 = true := by decide +kernel
private theorem triCheck_part_1_272 : triCheck 1 272 16 = true := by decide +kernel
private theorem triCheck_part_1_288 : triCheck 1 288 16 = true := by decide +kernel
private theorem triCheck_part_1_304 : triCheck 1 304 16 = true := by decide +kernel
private theorem triCheck_part_1_320 : triCheck 1 320 16 = true := by decide +kernel
private theorem triCheck_part_1_336 : triCheck 1 336 16 = true := by decide +kernel
private theorem triCheck_part_1_352 : triCheck 1 352 16 = true := by decide +kernel
private theorem triCheck_part_1_368 : triCheck 1 368 16 = true := by decide +kernel
private theorem triCheck_part_1_384 : triCheck 1 384 16 = true := by decide +kernel
private theorem triCheck_part_1_400 : triCheck 1 400 16 = true := by decide +kernel
private theorem triCheck_part_1_416 : triCheck 1 416 16 = true := by decide +kernel
private theorem triCheck_part_1_432 : triCheck 1 432 16 = true := by decide +kernel
private theorem triCheck_part_1_448 : triCheck 1 448 16 = true := by decide +kernel
private theorem triCheck_part_1_464 : triCheck 1 464 16 = true := by decide +kernel
private theorem triCheck_part_1_480 : triCheck 1 480 16 = true := by decide +kernel
private theorem triCheck_part_1_496 : triCheck 1 496 16 = true := by decide +kernel
theorem triCheck_1_1 : triCheck 1 256 256 = true := by
  exact @triCheck_add 1 256 16 240 (by decide +kernel) triCheck_part_1_256 (@triCheck_add 1 272 16 224 (by decide +kernel) triCheck_part_1_272 (@triCheck_add 1 288 16 208 (by decide +kernel) triCheck_part_1_288 (@triCheck_add 1 304 16 192 (by decide +kernel) triCheck_part_1_304 (@triCheck_add 1 320 16 176 (by decide +kernel) triCheck_part_1_320 (@triCheck_add 1 336 16 160 (by decide +kernel) triCheck_part_1_336 (@triCheck_add 1 352 16 144 (by decide +kernel) triCheck_part_1_352 (@triCheck_add 1 368 16 128 (by decide +kernel) triCheck_part_1_368 (@triCheck_add 1 384 16 112 (by decide +kernel) triCheck_part_1_384 (@triCheck_add 1 400 16 96 (by decide +kernel) triCheck_part_1_400 (@triCheck_add 1 416 16 80 (by decide +kernel) triCheck_part_1_416 (@triCheck_add 1 432 16 64 (by decide +kernel) triCheck_part_1_432 (@triCheck_add 1 448 16 48 (by decide +kernel) triCheck_part_1_448 (@triCheck_add 1 464 16 32 (by decide +kernel) triCheck_part_1_464 (@triCheck_add 1 480 16 16 (by decide +kernel) triCheck_part_1_480 (triCheck_part_1_496)))))))))))))))
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_ChainCheckT1 ====
section

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_2_0 : triCheck 2 0 16 = true := by decide +kernel
private theorem triCheck_part_2_16 : triCheck 2 16 16 = true := by decide +kernel
private theorem triCheck_part_2_32 : triCheck 2 32 16 = true := by decide +kernel
private theorem triCheck_part_2_48 : triCheck 2 48 16 = true := by decide +kernel
private theorem triCheck_part_2_64 : triCheck 2 64 16 = true := by decide +kernel
private theorem triCheck_part_2_80 : triCheck 2 80 16 = true := by decide +kernel
private theorem triCheck_part_2_96 : triCheck 2 96 16 = true := by decide +kernel
private theorem triCheck_part_2_112 : triCheck 2 112 16 = true := by decide +kernel
private theorem triCheck_part_2_128 : triCheck 2 128 16 = true := by decide +kernel
private theorem triCheck_part_2_144 : triCheck 2 144 16 = true := by decide +kernel
private theorem triCheck_part_2_160 : triCheck 2 160 16 = true := by decide +kernel
private theorem triCheck_part_2_176 : triCheck 2 176 16 = true := by decide +kernel
private theorem triCheck_part_2_192 : triCheck 2 192 16 = true := by decide +kernel
private theorem triCheck_part_2_208 : triCheck 2 208 16 = true := by decide +kernel
private theorem triCheck_part_2_224 : triCheck 2 224 16 = true := by decide +kernel
private theorem triCheck_part_2_240 : triCheck 2 240 16 = true := by decide +kernel
theorem triCheck_2_0 : triCheck 2 0 256 = true := by
  exact @triCheck_add 2 0 16 240 (by decide +kernel) triCheck_part_2_0 (@triCheck_add 2 16 16 224 (by decide +kernel) triCheck_part_2_16 (@triCheck_add 2 32 16 208 (by decide +kernel) triCheck_part_2_32 (@triCheck_add 2 48 16 192 (by decide +kernel) triCheck_part_2_48 (@triCheck_add 2 64 16 176 (by decide +kernel) triCheck_part_2_64 (@triCheck_add 2 80 16 160 (by decide +kernel) triCheck_part_2_80 (@triCheck_add 2 96 16 144 (by decide +kernel) triCheck_part_2_96 (@triCheck_add 2 112 16 128 (by decide +kernel) triCheck_part_2_112 (@triCheck_add 2 128 16 112 (by decide +kernel) triCheck_part_2_128 (@triCheck_add 2 144 16 96 (by decide +kernel) triCheck_part_2_144 (@triCheck_add 2 160 16 80 (by decide +kernel) triCheck_part_2_160 (@triCheck_add 2 176 16 64 (by decide +kernel) triCheck_part_2_176 (@triCheck_add 2 192 16 48 (by decide +kernel) triCheck_part_2_192 (@triCheck_add 2 208 16 32 (by decide +kernel) triCheck_part_2_208 (@triCheck_add 2 224 16 16 (by decide +kernel) triCheck_part_2_224 (triCheck_part_2_240)))))))))))))))
private theorem triCheck_part_2_256 : triCheck 2 256 16 = true := by decide +kernel
private theorem triCheck_part_2_272 : triCheck 2 272 16 = true := by decide +kernel
private theorem triCheck_part_2_288 : triCheck 2 288 16 = true := by decide +kernel
private theorem triCheck_part_2_304 : triCheck 2 304 16 = true := by decide +kernel
private theorem triCheck_part_2_320 : triCheck 2 320 16 = true := by decide +kernel
private theorem triCheck_part_2_336 : triCheck 2 336 16 = true := by decide +kernel
private theorem triCheck_part_2_352 : triCheck 2 352 16 = true := by decide +kernel
private theorem triCheck_part_2_368 : triCheck 2 368 16 = true := by decide +kernel
private theorem triCheck_part_2_384 : triCheck 2 384 16 = true := by decide +kernel
private theorem triCheck_part_2_400 : triCheck 2 400 16 = true := by decide +kernel
private theorem triCheck_part_2_416 : triCheck 2 416 16 = true := by decide +kernel
private theorem triCheck_part_2_432 : triCheck 2 432 16 = true := by decide +kernel
private theorem triCheck_part_2_448 : triCheck 2 448 16 = true := by decide +kernel
private theorem triCheck_part_2_464 : triCheck 2 464 16 = true := by decide +kernel
private theorem triCheck_part_2_480 : triCheck 2 480 16 = true := by decide +kernel
private theorem triCheck_part_2_496 : triCheck 2 496 16 = true := by decide +kernel
theorem triCheck_2_1 : triCheck 2 256 256 = true := by
  exact @triCheck_add 2 256 16 240 (by decide +kernel) triCheck_part_2_256 (@triCheck_add 2 272 16 224 (by decide +kernel) triCheck_part_2_272 (@triCheck_add 2 288 16 208 (by decide +kernel) triCheck_part_2_288 (@triCheck_add 2 304 16 192 (by decide +kernel) triCheck_part_2_304 (@triCheck_add 2 320 16 176 (by decide +kernel) triCheck_part_2_320 (@triCheck_add 2 336 16 160 (by decide +kernel) triCheck_part_2_336 (@triCheck_add 2 352 16 144 (by decide +kernel) triCheck_part_2_352 (@triCheck_add 2 368 16 128 (by decide +kernel) triCheck_part_2_368 (@triCheck_add 2 384 16 112 (by decide +kernel) triCheck_part_2_384 (@triCheck_add 2 400 16 96 (by decide +kernel) triCheck_part_2_400 (@triCheck_add 2 416 16 80 (by decide +kernel) triCheck_part_2_416 (@triCheck_add 2 432 16 64 (by decide +kernel) triCheck_part_2_432 (@triCheck_add 2 448 16 48 (by decide +kernel) triCheck_part_2_448 (@triCheck_add 2 464 16 32 (by decide +kernel) triCheck_part_2_464 (@triCheck_add 2 480 16 16 (by decide +kernel) triCheck_part_2_480 (triCheck_part_2_496)))))))))))))))
private theorem triCheck_part_3_0 : triCheck 3 0 16 = true := by decide +kernel
private theorem triCheck_part_3_16 : triCheck 3 16 16 = true := by decide +kernel
private theorem triCheck_part_3_32 : triCheck 3 32 16 = true := by decide +kernel
private theorem triCheck_part_3_48 : triCheck 3 48 16 = true := by decide +kernel
private theorem triCheck_part_3_64 : triCheck 3 64 16 = true := by decide +kernel
private theorem triCheck_part_3_80 : triCheck 3 80 16 = true := by decide +kernel
private theorem triCheck_part_3_96 : triCheck 3 96 16 = true := by decide +kernel
private theorem triCheck_part_3_112 : triCheck 3 112 16 = true := by decide +kernel
private theorem triCheck_part_3_128 : triCheck 3 128 16 = true := by decide +kernel
private theorem triCheck_part_3_144 : triCheck 3 144 16 = true := by decide +kernel
private theorem triCheck_part_3_160 : triCheck 3 160 16 = true := by decide +kernel
private theorem triCheck_part_3_176 : triCheck 3 176 16 = true := by decide +kernel
private theorem triCheck_part_3_192 : triCheck 3 192 16 = true := by decide +kernel
private theorem triCheck_part_3_208 : triCheck 3 208 16 = true := by decide +kernel
private theorem triCheck_part_3_224 : triCheck 3 224 16 = true := by decide +kernel
private theorem triCheck_part_3_240 : triCheck 3 240 16 = true := by decide +kernel
theorem triCheck_3_0 : triCheck 3 0 256 = true := by
  exact @triCheck_add 3 0 16 240 (by decide +kernel) triCheck_part_3_0 (@triCheck_add 3 16 16 224 (by decide +kernel) triCheck_part_3_16 (@triCheck_add 3 32 16 208 (by decide +kernel) triCheck_part_3_32 (@triCheck_add 3 48 16 192 (by decide +kernel) triCheck_part_3_48 (@triCheck_add 3 64 16 176 (by decide +kernel) triCheck_part_3_64 (@triCheck_add 3 80 16 160 (by decide +kernel) triCheck_part_3_80 (@triCheck_add 3 96 16 144 (by decide +kernel) triCheck_part_3_96 (@triCheck_add 3 112 16 128 (by decide +kernel) triCheck_part_3_112 (@triCheck_add 3 128 16 112 (by decide +kernel) triCheck_part_3_128 (@triCheck_add 3 144 16 96 (by decide +kernel) triCheck_part_3_144 (@triCheck_add 3 160 16 80 (by decide +kernel) triCheck_part_3_160 (@triCheck_add 3 176 16 64 (by decide +kernel) triCheck_part_3_176 (@triCheck_add 3 192 16 48 (by decide +kernel) triCheck_part_3_192 (@triCheck_add 3 208 16 32 (by decide +kernel) triCheck_part_3_208 (@triCheck_add 3 224 16 16 (by decide +kernel) triCheck_part_3_224 (triCheck_part_3_240)))))))))))))))
private theorem triCheck_part_3_256 : triCheck 3 256 16 = true := by decide +kernel
private theorem triCheck_part_3_272 : triCheck 3 272 16 = true := by decide +kernel
private theorem triCheck_part_3_288 : triCheck 3 288 16 = true := by decide +kernel
private theorem triCheck_part_3_304 : triCheck 3 304 16 = true := by decide +kernel
private theorem triCheck_part_3_320 : triCheck 3 320 16 = true := by decide +kernel
private theorem triCheck_part_3_336 : triCheck 3 336 16 = true := by decide +kernel
private theorem triCheck_part_3_352 : triCheck 3 352 16 = true := by decide +kernel
private theorem triCheck_part_3_368 : triCheck 3 368 16 = true := by decide +kernel
private theorem triCheck_part_3_384 : triCheck 3 384 16 = true := by decide +kernel
private theorem triCheck_part_3_400 : triCheck 3 400 16 = true := by decide +kernel
private theorem triCheck_part_3_416 : triCheck 3 416 16 = true := by decide +kernel
private theorem triCheck_part_3_432 : triCheck 3 432 16 = true := by decide +kernel
private theorem triCheck_part_3_448 : triCheck 3 448 16 = true := by decide +kernel
private theorem triCheck_part_3_464 : triCheck 3 464 16 = true := by decide +kernel
private theorem triCheck_part_3_480 : triCheck 3 480 16 = true := by decide +kernel
private theorem triCheck_part_3_496 : triCheck 3 496 16 = true := by decide +kernel
theorem triCheck_3_1 : triCheck 3 256 256 = true := by
  exact @triCheck_add 3 256 16 240 (by decide +kernel) triCheck_part_3_256 (@triCheck_add 3 272 16 224 (by decide +kernel) triCheck_part_3_272 (@triCheck_add 3 288 16 208 (by decide +kernel) triCheck_part_3_288 (@triCheck_add 3 304 16 192 (by decide +kernel) triCheck_part_3_304 (@triCheck_add 3 320 16 176 (by decide +kernel) triCheck_part_3_320 (@triCheck_add 3 336 16 160 (by decide +kernel) triCheck_part_3_336 (@triCheck_add 3 352 16 144 (by decide +kernel) triCheck_part_3_352 (@triCheck_add 3 368 16 128 (by decide +kernel) triCheck_part_3_368 (@triCheck_add 3 384 16 112 (by decide +kernel) triCheck_part_3_384 (@triCheck_add 3 400 16 96 (by decide +kernel) triCheck_part_3_400 (@triCheck_add 3 416 16 80 (by decide +kernel) triCheck_part_3_416 (@triCheck_add 3 432 16 64 (by decide +kernel) triCheck_part_3_432 (@triCheck_add 3 448 16 48 (by decide +kernel) triCheck_part_3_448 (@triCheck_add 3 464 16 32 (by decide +kernel) triCheck_part_3_464 (@triCheck_add 3 480 16 16 (by decide +kernel) triCheck_part_3_480 (triCheck_part_3_496)))))))))))))))
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_ChainCheckT2 ====
section

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_4_0 : triCheck 4 0 16 = true := by decide +kernel
private theorem triCheck_part_4_16 : triCheck 4 16 16 = true := by decide +kernel
private theorem triCheck_part_4_32 : triCheck 4 32 16 = true := by decide +kernel
private theorem triCheck_part_4_48 : triCheck 4 48 16 = true := by decide +kernel
private theorem triCheck_part_4_64 : triCheck 4 64 16 = true := by decide +kernel
private theorem triCheck_part_4_80 : triCheck 4 80 16 = true := by decide +kernel
private theorem triCheck_part_4_96 : triCheck 4 96 16 = true := by decide +kernel
private theorem triCheck_part_4_112 : triCheck 4 112 16 = true := by decide +kernel
private theorem triCheck_part_4_128 : triCheck 4 128 16 = true := by decide +kernel
private theorem triCheck_part_4_144 : triCheck 4 144 16 = true := by decide +kernel
private theorem triCheck_part_4_160 : triCheck 4 160 16 = true := by decide +kernel
private theorem triCheck_part_4_176 : triCheck 4 176 16 = true := by decide +kernel
private theorem triCheck_part_4_192 : triCheck 4 192 16 = true := by decide +kernel
private theorem triCheck_part_4_208 : triCheck 4 208 16 = true := by decide +kernel
private theorem triCheck_part_4_224 : triCheck 4 224 16 = true := by decide +kernel
private theorem triCheck_part_4_240 : triCheck 4 240 16 = true := by decide +kernel
theorem triCheck_4_0 : triCheck 4 0 256 = true := by
  exact @triCheck_add 4 0 16 240 (by decide +kernel) triCheck_part_4_0 (@triCheck_add 4 16 16 224 (by decide +kernel) triCheck_part_4_16 (@triCheck_add 4 32 16 208 (by decide +kernel) triCheck_part_4_32 (@triCheck_add 4 48 16 192 (by decide +kernel) triCheck_part_4_48 (@triCheck_add 4 64 16 176 (by decide +kernel) triCheck_part_4_64 (@triCheck_add 4 80 16 160 (by decide +kernel) triCheck_part_4_80 (@triCheck_add 4 96 16 144 (by decide +kernel) triCheck_part_4_96 (@triCheck_add 4 112 16 128 (by decide +kernel) triCheck_part_4_112 (@triCheck_add 4 128 16 112 (by decide +kernel) triCheck_part_4_128 (@triCheck_add 4 144 16 96 (by decide +kernel) triCheck_part_4_144 (@triCheck_add 4 160 16 80 (by decide +kernel) triCheck_part_4_160 (@triCheck_add 4 176 16 64 (by decide +kernel) triCheck_part_4_176 (@triCheck_add 4 192 16 48 (by decide +kernel) triCheck_part_4_192 (@triCheck_add 4 208 16 32 (by decide +kernel) triCheck_part_4_208 (@triCheck_add 4 224 16 16 (by decide +kernel) triCheck_part_4_224 (triCheck_part_4_240)))))))))))))))
private theorem triCheck_part_4_256 : triCheck 4 256 16 = true := by decide +kernel
private theorem triCheck_part_4_272 : triCheck 4 272 16 = true := by decide +kernel
private theorem triCheck_part_4_288 : triCheck 4 288 16 = true := by decide +kernel
private theorem triCheck_part_4_304 : triCheck 4 304 16 = true := by decide +kernel
private theorem triCheck_part_4_320 : triCheck 4 320 16 = true := by decide +kernel
private theorem triCheck_part_4_336 : triCheck 4 336 16 = true := by decide +kernel
private theorem triCheck_part_4_352 : triCheck 4 352 16 = true := by decide +kernel
private theorem triCheck_part_4_368 : triCheck 4 368 16 = true := by decide +kernel
private theorem triCheck_part_4_384 : triCheck 4 384 16 = true := by decide +kernel
private theorem triCheck_part_4_400 : triCheck 4 400 16 = true := by decide +kernel
private theorem triCheck_part_4_416 : triCheck 4 416 16 = true := by decide +kernel
private theorem triCheck_part_4_432 : triCheck 4 432 16 = true := by decide +kernel
private theorem triCheck_part_4_448 : triCheck 4 448 16 = true := by decide +kernel
private theorem triCheck_part_4_464 : triCheck 4 464 16 = true := by decide +kernel
private theorem triCheck_part_4_480 : triCheck 4 480 16 = true := by decide +kernel
private theorem triCheck_part_4_496 : triCheck 4 496 16 = true := by decide +kernel
theorem triCheck_4_1 : triCheck 4 256 256 = true := by
  exact @triCheck_add 4 256 16 240 (by decide +kernel) triCheck_part_4_256 (@triCheck_add 4 272 16 224 (by decide +kernel) triCheck_part_4_272 (@triCheck_add 4 288 16 208 (by decide +kernel) triCheck_part_4_288 (@triCheck_add 4 304 16 192 (by decide +kernel) triCheck_part_4_304 (@triCheck_add 4 320 16 176 (by decide +kernel) triCheck_part_4_320 (@triCheck_add 4 336 16 160 (by decide +kernel) triCheck_part_4_336 (@triCheck_add 4 352 16 144 (by decide +kernel) triCheck_part_4_352 (@triCheck_add 4 368 16 128 (by decide +kernel) triCheck_part_4_368 (@triCheck_add 4 384 16 112 (by decide +kernel) triCheck_part_4_384 (@triCheck_add 4 400 16 96 (by decide +kernel) triCheck_part_4_400 (@triCheck_add 4 416 16 80 (by decide +kernel) triCheck_part_4_416 (@triCheck_add 4 432 16 64 (by decide +kernel) triCheck_part_4_432 (@triCheck_add 4 448 16 48 (by decide +kernel) triCheck_part_4_448 (@triCheck_add 4 464 16 32 (by decide +kernel) triCheck_part_4_464 (@triCheck_add 4 480 16 16 (by decide +kernel) triCheck_part_4_480 (triCheck_part_4_496)))))))))))))))
private theorem triCheck_part_5_0 : triCheck 5 0 16 = true := by decide +kernel
private theorem triCheck_part_5_16 : triCheck 5 16 16 = true := by decide +kernel
private theorem triCheck_part_5_32 : triCheck 5 32 16 = true := by decide +kernel
private theorem triCheck_part_5_48 : triCheck 5 48 16 = true := by decide +kernel
private theorem triCheck_part_5_64 : triCheck 5 64 16 = true := by decide +kernel
private theorem triCheck_part_5_80 : triCheck 5 80 16 = true := by decide +kernel
private theorem triCheck_part_5_96 : triCheck 5 96 16 = true := by decide +kernel
private theorem triCheck_part_5_112 : triCheck 5 112 16 = true := by decide +kernel
private theorem triCheck_part_5_128 : triCheck 5 128 16 = true := by decide +kernel
private theorem triCheck_part_5_144 : triCheck 5 144 16 = true := by decide +kernel
private theorem triCheck_part_5_160 : triCheck 5 160 16 = true := by decide +kernel
private theorem triCheck_part_5_176 : triCheck 5 176 16 = true := by decide +kernel
private theorem triCheck_part_5_192 : triCheck 5 192 16 = true := by decide +kernel
private theorem triCheck_part_5_208 : triCheck 5 208 16 = true := by decide +kernel
private theorem triCheck_part_5_224 : triCheck 5 224 16 = true := by decide +kernel
private theorem triCheck_part_5_240 : triCheck 5 240 16 = true := by decide +kernel
theorem triCheck_5_0 : triCheck 5 0 256 = true := by
  exact @triCheck_add 5 0 16 240 (by decide +kernel) triCheck_part_5_0 (@triCheck_add 5 16 16 224 (by decide +kernel) triCheck_part_5_16 (@triCheck_add 5 32 16 208 (by decide +kernel) triCheck_part_5_32 (@triCheck_add 5 48 16 192 (by decide +kernel) triCheck_part_5_48 (@triCheck_add 5 64 16 176 (by decide +kernel) triCheck_part_5_64 (@triCheck_add 5 80 16 160 (by decide +kernel) triCheck_part_5_80 (@triCheck_add 5 96 16 144 (by decide +kernel) triCheck_part_5_96 (@triCheck_add 5 112 16 128 (by decide +kernel) triCheck_part_5_112 (@triCheck_add 5 128 16 112 (by decide +kernel) triCheck_part_5_128 (@triCheck_add 5 144 16 96 (by decide +kernel) triCheck_part_5_144 (@triCheck_add 5 160 16 80 (by decide +kernel) triCheck_part_5_160 (@triCheck_add 5 176 16 64 (by decide +kernel) triCheck_part_5_176 (@triCheck_add 5 192 16 48 (by decide +kernel) triCheck_part_5_192 (@triCheck_add 5 208 16 32 (by decide +kernel) triCheck_part_5_208 (@triCheck_add 5 224 16 16 (by decide +kernel) triCheck_part_5_224 (triCheck_part_5_240)))))))))))))))
private theorem triCheck_part_5_256 : triCheck 5 256 16 = true := by decide +kernel
private theorem triCheck_part_5_272 : triCheck 5 272 16 = true := by decide +kernel
private theorem triCheck_part_5_288 : triCheck 5 288 16 = true := by decide +kernel
private theorem triCheck_part_5_304 : triCheck 5 304 16 = true := by decide +kernel
private theorem triCheck_part_5_320 : triCheck 5 320 16 = true := by decide +kernel
private theorem triCheck_part_5_336 : triCheck 5 336 16 = true := by decide +kernel
private theorem triCheck_part_5_352 : triCheck 5 352 16 = true := by decide +kernel
private theorem triCheck_part_5_368 : triCheck 5 368 16 = true := by decide +kernel
private theorem triCheck_part_5_384 : triCheck 5 384 16 = true := by decide +kernel
private theorem triCheck_part_5_400 : triCheck 5 400 16 = true := by decide +kernel
private theorem triCheck_part_5_416 : triCheck 5 416 16 = true := by decide +kernel
private theorem triCheck_part_5_432 : triCheck 5 432 16 = true := by decide +kernel
private theorem triCheck_part_5_448 : triCheck 5 448 16 = true := by decide +kernel
private theorem triCheck_part_5_464 : triCheck 5 464 16 = true := by decide +kernel
private theorem triCheck_part_5_480 : triCheck 5 480 16 = true := by decide +kernel
private theorem triCheck_part_5_496 : triCheck 5 496 16 = true := by decide +kernel
theorem triCheck_5_1 : triCheck 5 256 256 = true := by
  exact @triCheck_add 5 256 16 240 (by decide +kernel) triCheck_part_5_256 (@triCheck_add 5 272 16 224 (by decide +kernel) triCheck_part_5_272 (@triCheck_add 5 288 16 208 (by decide +kernel) triCheck_part_5_288 (@triCheck_add 5 304 16 192 (by decide +kernel) triCheck_part_5_304 (@triCheck_add 5 320 16 176 (by decide +kernel) triCheck_part_5_320 (@triCheck_add 5 336 16 160 (by decide +kernel) triCheck_part_5_336 (@triCheck_add 5 352 16 144 (by decide +kernel) triCheck_part_5_352 (@triCheck_add 5 368 16 128 (by decide +kernel) triCheck_part_5_368 (@triCheck_add 5 384 16 112 (by decide +kernel) triCheck_part_5_384 (@triCheck_add 5 400 16 96 (by decide +kernel) triCheck_part_5_400 (@triCheck_add 5 416 16 80 (by decide +kernel) triCheck_part_5_416 (@triCheck_add 5 432 16 64 (by decide +kernel) triCheck_part_5_432 (@triCheck_add 5 448 16 48 (by decide +kernel) triCheck_part_5_448 (@triCheck_add 5 464 16 32 (by decide +kernel) triCheck_part_5_464 (@triCheck_add 5 480 16 16 (by decide +kernel) triCheck_part_5_480 (triCheck_part_5_496)))))))))))))))
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_ChainCheckT3 ====
section

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_6_0 : triCheck 6 0 16 = true := by decide +kernel
private theorem triCheck_part_6_16 : triCheck 6 16 16 = true := by decide +kernel
private theorem triCheck_part_6_32 : triCheck 6 32 16 = true := by decide +kernel
private theorem triCheck_part_6_48 : triCheck 6 48 16 = true := by decide +kernel
private theorem triCheck_part_6_64 : triCheck 6 64 16 = true := by decide +kernel
private theorem triCheck_part_6_80 : triCheck 6 80 16 = true := by decide +kernel
private theorem triCheck_part_6_96 : triCheck 6 96 16 = true := by decide +kernel
private theorem triCheck_part_6_112 : triCheck 6 112 16 = true := by decide +kernel
private theorem triCheck_part_6_128 : triCheck 6 128 16 = true := by decide +kernel
private theorem triCheck_part_6_144 : triCheck 6 144 16 = true := by decide +kernel
private theorem triCheck_part_6_160 : triCheck 6 160 16 = true := by decide +kernel
private theorem triCheck_part_6_176 : triCheck 6 176 16 = true := by decide +kernel
private theorem triCheck_part_6_192 : triCheck 6 192 16 = true := by decide +kernel
private theorem triCheck_part_6_208 : triCheck 6 208 16 = true := by decide +kernel
private theorem triCheck_part_6_224 : triCheck 6 224 16 = true := by decide +kernel
private theorem triCheck_part_6_240 : triCheck 6 240 16 = true := by decide +kernel
theorem triCheck_6_0 : triCheck 6 0 256 = true := by
  exact @triCheck_add 6 0 16 240 (by decide +kernel) triCheck_part_6_0 (@triCheck_add 6 16 16 224 (by decide +kernel) triCheck_part_6_16 (@triCheck_add 6 32 16 208 (by decide +kernel) triCheck_part_6_32 (@triCheck_add 6 48 16 192 (by decide +kernel) triCheck_part_6_48 (@triCheck_add 6 64 16 176 (by decide +kernel) triCheck_part_6_64 (@triCheck_add 6 80 16 160 (by decide +kernel) triCheck_part_6_80 (@triCheck_add 6 96 16 144 (by decide +kernel) triCheck_part_6_96 (@triCheck_add 6 112 16 128 (by decide +kernel) triCheck_part_6_112 (@triCheck_add 6 128 16 112 (by decide +kernel) triCheck_part_6_128 (@triCheck_add 6 144 16 96 (by decide +kernel) triCheck_part_6_144 (@triCheck_add 6 160 16 80 (by decide +kernel) triCheck_part_6_160 (@triCheck_add 6 176 16 64 (by decide +kernel) triCheck_part_6_176 (@triCheck_add 6 192 16 48 (by decide +kernel) triCheck_part_6_192 (@triCheck_add 6 208 16 32 (by decide +kernel) triCheck_part_6_208 (@triCheck_add 6 224 16 16 (by decide +kernel) triCheck_part_6_224 (triCheck_part_6_240)))))))))))))))
private theorem triCheck_part_6_256 : triCheck 6 256 16 = true := by decide +kernel
private theorem triCheck_part_6_272 : triCheck 6 272 16 = true := by decide +kernel
private theorem triCheck_part_6_288 : triCheck 6 288 16 = true := by decide +kernel
private theorem triCheck_part_6_304 : triCheck 6 304 16 = true := by decide +kernel
private theorem triCheck_part_6_320 : triCheck 6 320 16 = true := by decide +kernel
private theorem triCheck_part_6_336 : triCheck 6 336 16 = true := by decide +kernel
private theorem triCheck_part_6_352 : triCheck 6 352 16 = true := by decide +kernel
private theorem triCheck_part_6_368 : triCheck 6 368 16 = true := by decide +kernel
private theorem triCheck_part_6_384 : triCheck 6 384 16 = true := by decide +kernel
private theorem triCheck_part_6_400 : triCheck 6 400 16 = true := by decide +kernel
private theorem triCheck_part_6_416 : triCheck 6 416 16 = true := by decide +kernel
private theorem triCheck_part_6_432 : triCheck 6 432 16 = true := by decide +kernel
private theorem triCheck_part_6_448 : triCheck 6 448 16 = true := by decide +kernel
private theorem triCheck_part_6_464 : triCheck 6 464 16 = true := by decide +kernel
private theorem triCheck_part_6_480 : triCheck 6 480 16 = true := by decide +kernel
private theorem triCheck_part_6_496 : triCheck 6 496 16 = true := by decide +kernel
theorem triCheck_6_1 : triCheck 6 256 256 = true := by
  exact @triCheck_add 6 256 16 240 (by decide +kernel) triCheck_part_6_256 (@triCheck_add 6 272 16 224 (by decide +kernel) triCheck_part_6_272 (@triCheck_add 6 288 16 208 (by decide +kernel) triCheck_part_6_288 (@triCheck_add 6 304 16 192 (by decide +kernel) triCheck_part_6_304 (@triCheck_add 6 320 16 176 (by decide +kernel) triCheck_part_6_320 (@triCheck_add 6 336 16 160 (by decide +kernel) triCheck_part_6_336 (@triCheck_add 6 352 16 144 (by decide +kernel) triCheck_part_6_352 (@triCheck_add 6 368 16 128 (by decide +kernel) triCheck_part_6_368 (@triCheck_add 6 384 16 112 (by decide +kernel) triCheck_part_6_384 (@triCheck_add 6 400 16 96 (by decide +kernel) triCheck_part_6_400 (@triCheck_add 6 416 16 80 (by decide +kernel) triCheck_part_6_416 (@triCheck_add 6 432 16 64 (by decide +kernel) triCheck_part_6_432 (@triCheck_add 6 448 16 48 (by decide +kernel) triCheck_part_6_448 (@triCheck_add 6 464 16 32 (by decide +kernel) triCheck_part_6_464 (@triCheck_add 6 480 16 16 (by decide +kernel) triCheck_part_6_480 (triCheck_part_6_496)))))))))))))))
private theorem triCheck_part_7_0 : triCheck 7 0 16 = true := by decide +kernel
private theorem triCheck_part_7_16 : triCheck 7 16 16 = true := by decide +kernel
private theorem triCheck_part_7_32 : triCheck 7 32 16 = true := by decide +kernel
private theorem triCheck_part_7_48 : triCheck 7 48 16 = true := by decide +kernel
private theorem triCheck_part_7_64 : triCheck 7 64 16 = true := by decide +kernel
private theorem triCheck_part_7_80 : triCheck 7 80 16 = true := by decide +kernel
private theorem triCheck_part_7_96 : triCheck 7 96 16 = true := by decide +kernel
private theorem triCheck_part_7_112 : triCheck 7 112 16 = true := by decide +kernel
private theorem triCheck_part_7_128 : triCheck 7 128 16 = true := by decide +kernel
private theorem triCheck_part_7_144 : triCheck 7 144 16 = true := by decide +kernel
private theorem triCheck_part_7_160 : triCheck 7 160 16 = true := by decide +kernel
private theorem triCheck_part_7_176 : triCheck 7 176 16 = true := by decide +kernel
private theorem triCheck_part_7_192 : triCheck 7 192 16 = true := by decide +kernel
private theorem triCheck_part_7_208 : triCheck 7 208 16 = true := by decide +kernel
private theorem triCheck_part_7_224 : triCheck 7 224 16 = true := by decide +kernel
private theorem triCheck_part_7_240 : triCheck 7 240 16 = true := by decide +kernel
theorem triCheck_7_0 : triCheck 7 0 256 = true := by
  exact @triCheck_add 7 0 16 240 (by decide +kernel) triCheck_part_7_0 (@triCheck_add 7 16 16 224 (by decide +kernel) triCheck_part_7_16 (@triCheck_add 7 32 16 208 (by decide +kernel) triCheck_part_7_32 (@triCheck_add 7 48 16 192 (by decide +kernel) triCheck_part_7_48 (@triCheck_add 7 64 16 176 (by decide +kernel) triCheck_part_7_64 (@triCheck_add 7 80 16 160 (by decide +kernel) triCheck_part_7_80 (@triCheck_add 7 96 16 144 (by decide +kernel) triCheck_part_7_96 (@triCheck_add 7 112 16 128 (by decide +kernel) triCheck_part_7_112 (@triCheck_add 7 128 16 112 (by decide +kernel) triCheck_part_7_128 (@triCheck_add 7 144 16 96 (by decide +kernel) triCheck_part_7_144 (@triCheck_add 7 160 16 80 (by decide +kernel) triCheck_part_7_160 (@triCheck_add 7 176 16 64 (by decide +kernel) triCheck_part_7_176 (@triCheck_add 7 192 16 48 (by decide +kernel) triCheck_part_7_192 (@triCheck_add 7 208 16 32 (by decide +kernel) triCheck_part_7_208 (@triCheck_add 7 224 16 16 (by decide +kernel) triCheck_part_7_224 (triCheck_part_7_240)))))))))))))))
private theorem triCheck_part_7_256 : triCheck 7 256 16 = true := by decide +kernel
private theorem triCheck_part_7_272 : triCheck 7 272 16 = true := by decide +kernel
private theorem triCheck_part_7_288 : triCheck 7 288 16 = true := by decide +kernel
private theorem triCheck_part_7_304 : triCheck 7 304 16 = true := by decide +kernel
private theorem triCheck_part_7_320 : triCheck 7 320 16 = true := by decide +kernel
private theorem triCheck_part_7_336 : triCheck 7 336 16 = true := by decide +kernel
private theorem triCheck_part_7_352 : triCheck 7 352 16 = true := by decide +kernel
private theorem triCheck_part_7_368 : triCheck 7 368 16 = true := by decide +kernel
private theorem triCheck_part_7_384 : triCheck 7 384 16 = true := by decide +kernel
private theorem triCheck_part_7_400 : triCheck 7 400 16 = true := by decide +kernel
private theorem triCheck_part_7_416 : triCheck 7 416 16 = true := by decide +kernel
private theorem triCheck_part_7_432 : triCheck 7 432 16 = true := by decide +kernel
private theorem triCheck_part_7_448 : triCheck 7 448 16 = true := by decide +kernel
private theorem triCheck_part_7_464 : triCheck 7 464 16 = true := by decide +kernel
private theorem triCheck_part_7_480 : triCheck 7 480 16 = true := by decide +kernel
private theorem triCheck_part_7_496 : triCheck 7 496 16 = true := by decide +kernel
theorem triCheck_7_1 : triCheck 7 256 256 = true := by
  exact @triCheck_add 7 256 16 240 (by decide +kernel) triCheck_part_7_256 (@triCheck_add 7 272 16 224 (by decide +kernel) triCheck_part_7_272 (@triCheck_add 7 288 16 208 (by decide +kernel) triCheck_part_7_288 (@triCheck_add 7 304 16 192 (by decide +kernel) triCheck_part_7_304 (@triCheck_add 7 320 16 176 (by decide +kernel) triCheck_part_7_320 (@triCheck_add 7 336 16 160 (by decide +kernel) triCheck_part_7_336 (@triCheck_add 7 352 16 144 (by decide +kernel) triCheck_part_7_352 (@triCheck_add 7 368 16 128 (by decide +kernel) triCheck_part_7_368 (@triCheck_add 7 384 16 112 (by decide +kernel) triCheck_part_7_384 (@triCheck_add 7 400 16 96 (by decide +kernel) triCheck_part_7_400 (@triCheck_add 7 416 16 80 (by decide +kernel) triCheck_part_7_416 (@triCheck_add 7 432 16 64 (by decide +kernel) triCheck_part_7_432 (@triCheck_add 7 448 16 48 (by decide +kernel) triCheck_part_7_448 (@triCheck_add 7 464 16 32 (by decide +kernel) triCheck_part_7_464 (@triCheck_add 7 480 16 16 (by decide +kernel) triCheck_part_7_480 (triCheck_part_7_496)))))))))))))))
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_ChainCheckT4 ====
section

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_8_0 : triCheck 8 0 16 = true := by decide +kernel
private theorem triCheck_part_8_16 : triCheck 8 16 16 = true := by decide +kernel
private theorem triCheck_part_8_32 : triCheck 8 32 16 = true := by decide +kernel
private theorem triCheck_part_8_48 : triCheck 8 48 16 = true := by decide +kernel
private theorem triCheck_part_8_64 : triCheck 8 64 16 = true := by decide +kernel
private theorem triCheck_part_8_80 : triCheck 8 80 16 = true := by decide +kernel
private theorem triCheck_part_8_96 : triCheck 8 96 16 = true := by decide +kernel
private theorem triCheck_part_8_112 : triCheck 8 112 16 = true := by decide +kernel
private theorem triCheck_part_8_128 : triCheck 8 128 16 = true := by decide +kernel
private theorem triCheck_part_8_144 : triCheck 8 144 16 = true := by decide +kernel
private theorem triCheck_part_8_160 : triCheck 8 160 16 = true := by decide +kernel
private theorem triCheck_part_8_176 : triCheck 8 176 16 = true := by decide +kernel
private theorem triCheck_part_8_192 : triCheck 8 192 16 = true := by decide +kernel
private theorem triCheck_part_8_208 : triCheck 8 208 16 = true := by decide +kernel
private theorem triCheck_part_8_224 : triCheck 8 224 16 = true := by decide +kernel
private theorem triCheck_part_8_240 : triCheck 8 240 16 = true := by decide +kernel
theorem triCheck_8_0 : triCheck 8 0 256 = true := by
  exact @triCheck_add 8 0 16 240 (by decide +kernel) triCheck_part_8_0 (@triCheck_add 8 16 16 224 (by decide +kernel) triCheck_part_8_16 (@triCheck_add 8 32 16 208 (by decide +kernel) triCheck_part_8_32 (@triCheck_add 8 48 16 192 (by decide +kernel) triCheck_part_8_48 (@triCheck_add 8 64 16 176 (by decide +kernel) triCheck_part_8_64 (@triCheck_add 8 80 16 160 (by decide +kernel) triCheck_part_8_80 (@triCheck_add 8 96 16 144 (by decide +kernel) triCheck_part_8_96 (@triCheck_add 8 112 16 128 (by decide +kernel) triCheck_part_8_112 (@triCheck_add 8 128 16 112 (by decide +kernel) triCheck_part_8_128 (@triCheck_add 8 144 16 96 (by decide +kernel) triCheck_part_8_144 (@triCheck_add 8 160 16 80 (by decide +kernel) triCheck_part_8_160 (@triCheck_add 8 176 16 64 (by decide +kernel) triCheck_part_8_176 (@triCheck_add 8 192 16 48 (by decide +kernel) triCheck_part_8_192 (@triCheck_add 8 208 16 32 (by decide +kernel) triCheck_part_8_208 (@triCheck_add 8 224 16 16 (by decide +kernel) triCheck_part_8_224 (triCheck_part_8_240)))))))))))))))
private theorem triCheck_part_8_256 : triCheck 8 256 16 = true := by decide +kernel
private theorem triCheck_part_8_272 : triCheck 8 272 16 = true := by decide +kernel
private theorem triCheck_part_8_288 : triCheck 8 288 16 = true := by decide +kernel
private theorem triCheck_part_8_304 : triCheck 8 304 16 = true := by decide +kernel
private theorem triCheck_part_8_320 : triCheck 8 320 16 = true := by decide +kernel
private theorem triCheck_part_8_336 : triCheck 8 336 16 = true := by decide +kernel
private theorem triCheck_part_8_352 : triCheck 8 352 16 = true := by decide +kernel
private theorem triCheck_part_8_368 : triCheck 8 368 16 = true := by decide +kernel
private theorem triCheck_part_8_384 : triCheck 8 384 16 = true := by decide +kernel
private theorem triCheck_part_8_400 : triCheck 8 400 16 = true := by decide +kernel
private theorem triCheck_part_8_416 : triCheck 8 416 16 = true := by decide +kernel
private theorem triCheck_part_8_432 : triCheck 8 432 16 = true := by decide +kernel
private theorem triCheck_part_8_448 : triCheck 8 448 16 = true := by decide +kernel
private theorem triCheck_part_8_464 : triCheck 8 464 16 = true := by decide +kernel
private theorem triCheck_part_8_480 : triCheck 8 480 16 = true := by decide +kernel
private theorem triCheck_part_8_496 : triCheck 8 496 16 = true := by decide +kernel
theorem triCheck_8_1 : triCheck 8 256 256 = true := by
  exact @triCheck_add 8 256 16 240 (by decide +kernel) triCheck_part_8_256 (@triCheck_add 8 272 16 224 (by decide +kernel) triCheck_part_8_272 (@triCheck_add 8 288 16 208 (by decide +kernel) triCheck_part_8_288 (@triCheck_add 8 304 16 192 (by decide +kernel) triCheck_part_8_304 (@triCheck_add 8 320 16 176 (by decide +kernel) triCheck_part_8_320 (@triCheck_add 8 336 16 160 (by decide +kernel) triCheck_part_8_336 (@triCheck_add 8 352 16 144 (by decide +kernel) triCheck_part_8_352 (@triCheck_add 8 368 16 128 (by decide +kernel) triCheck_part_8_368 (@triCheck_add 8 384 16 112 (by decide +kernel) triCheck_part_8_384 (@triCheck_add 8 400 16 96 (by decide +kernel) triCheck_part_8_400 (@triCheck_add 8 416 16 80 (by decide +kernel) triCheck_part_8_416 (@triCheck_add 8 432 16 64 (by decide +kernel) triCheck_part_8_432 (@triCheck_add 8 448 16 48 (by decide +kernel) triCheck_part_8_448 (@triCheck_add 8 464 16 32 (by decide +kernel) triCheck_part_8_464 (@triCheck_add 8 480 16 16 (by decide +kernel) triCheck_part_8_480 (triCheck_part_8_496)))))))))))))))
private theorem triCheck_part_9_0 : triCheck 9 0 16 = true := by decide +kernel
private theorem triCheck_part_9_16 : triCheck 9 16 16 = true := by decide +kernel
private theorem triCheck_part_9_32 : triCheck 9 32 16 = true := by decide +kernel
private theorem triCheck_part_9_48 : triCheck 9 48 16 = true := by decide +kernel
private theorem triCheck_part_9_64 : triCheck 9 64 16 = true := by decide +kernel
private theorem triCheck_part_9_80 : triCheck 9 80 16 = true := by decide +kernel
private theorem triCheck_part_9_96 : triCheck 9 96 16 = true := by decide +kernel
private theorem triCheck_part_9_112 : triCheck 9 112 16 = true := by decide +kernel
private theorem triCheck_part_9_128 : triCheck 9 128 16 = true := by decide +kernel
private theorem triCheck_part_9_144 : triCheck 9 144 16 = true := by decide +kernel
private theorem triCheck_part_9_160 : triCheck 9 160 16 = true := by decide +kernel
private theorem triCheck_part_9_176 : triCheck 9 176 16 = true := by decide +kernel
private theorem triCheck_part_9_192 : triCheck 9 192 16 = true := by decide +kernel
private theorem triCheck_part_9_208 : triCheck 9 208 16 = true := by decide +kernel
private theorem triCheck_part_9_224 : triCheck 9 224 16 = true := by decide +kernel
private theorem triCheck_part_9_240 : triCheck 9 240 16 = true := by decide +kernel
theorem triCheck_9_0 : triCheck 9 0 256 = true := by
  exact @triCheck_add 9 0 16 240 (by decide +kernel) triCheck_part_9_0 (@triCheck_add 9 16 16 224 (by decide +kernel) triCheck_part_9_16 (@triCheck_add 9 32 16 208 (by decide +kernel) triCheck_part_9_32 (@triCheck_add 9 48 16 192 (by decide +kernel) triCheck_part_9_48 (@triCheck_add 9 64 16 176 (by decide +kernel) triCheck_part_9_64 (@triCheck_add 9 80 16 160 (by decide +kernel) triCheck_part_9_80 (@triCheck_add 9 96 16 144 (by decide +kernel) triCheck_part_9_96 (@triCheck_add 9 112 16 128 (by decide +kernel) triCheck_part_9_112 (@triCheck_add 9 128 16 112 (by decide +kernel) triCheck_part_9_128 (@triCheck_add 9 144 16 96 (by decide +kernel) triCheck_part_9_144 (@triCheck_add 9 160 16 80 (by decide +kernel) triCheck_part_9_160 (@triCheck_add 9 176 16 64 (by decide +kernel) triCheck_part_9_176 (@triCheck_add 9 192 16 48 (by decide +kernel) triCheck_part_9_192 (@triCheck_add 9 208 16 32 (by decide +kernel) triCheck_part_9_208 (@triCheck_add 9 224 16 16 (by decide +kernel) triCheck_part_9_224 (triCheck_part_9_240)))))))))))))))
private theorem triCheck_part_9_256 : triCheck 9 256 16 = true := by decide +kernel
private theorem triCheck_part_9_272 : triCheck 9 272 16 = true := by decide +kernel
private theorem triCheck_part_9_288 : triCheck 9 288 16 = true := by decide +kernel
private theorem triCheck_part_9_304 : triCheck 9 304 16 = true := by decide +kernel
private theorem triCheck_part_9_320 : triCheck 9 320 16 = true := by decide +kernel
private theorem triCheck_part_9_336 : triCheck 9 336 16 = true := by decide +kernel
private theorem triCheck_part_9_352 : triCheck 9 352 16 = true := by decide +kernel
private theorem triCheck_part_9_368 : triCheck 9 368 16 = true := by decide +kernel
private theorem triCheck_part_9_384 : triCheck 9 384 16 = true := by decide +kernel
private theorem triCheck_part_9_400 : triCheck 9 400 16 = true := by decide +kernel
private theorem triCheck_part_9_416 : triCheck 9 416 16 = true := by decide +kernel
private theorem triCheck_part_9_432 : triCheck 9 432 16 = true := by decide +kernel
private theorem triCheck_part_9_448 : triCheck 9 448 16 = true := by decide +kernel
private theorem triCheck_part_9_464 : triCheck 9 464 16 = true := by decide +kernel
private theorem triCheck_part_9_480 : triCheck 9 480 16 = true := by decide +kernel
private theorem triCheck_part_9_496 : triCheck 9 496 16 = true := by decide +kernel
theorem triCheck_9_1 : triCheck 9 256 256 = true := by
  exact @triCheck_add 9 256 16 240 (by decide +kernel) triCheck_part_9_256 (@triCheck_add 9 272 16 224 (by decide +kernel) triCheck_part_9_272 (@triCheck_add 9 288 16 208 (by decide +kernel) triCheck_part_9_288 (@triCheck_add 9 304 16 192 (by decide +kernel) triCheck_part_9_304 (@triCheck_add 9 320 16 176 (by decide +kernel) triCheck_part_9_320 (@triCheck_add 9 336 16 160 (by decide +kernel) triCheck_part_9_336 (@triCheck_add 9 352 16 144 (by decide +kernel) triCheck_part_9_352 (@triCheck_add 9 368 16 128 (by decide +kernel) triCheck_part_9_368 (@triCheck_add 9 384 16 112 (by decide +kernel) triCheck_part_9_384 (@triCheck_add 9 400 16 96 (by decide +kernel) triCheck_part_9_400 (@triCheck_add 9 416 16 80 (by decide +kernel) triCheck_part_9_416 (@triCheck_add 9 432 16 64 (by decide +kernel) triCheck_part_9_432 (@triCheck_add 9 448 16 48 (by decide +kernel) triCheck_part_9_448 (@triCheck_add 9 464 16 32 (by decide +kernel) triCheck_part_9_464 (@triCheck_add 9 480 16 16 (by decide +kernel) triCheck_part_9_480 (triCheck_part_9_496)))))))))))))))
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_ChainCheckT5 ====
section

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_10_0 : triCheck 10 0 16 = true := by decide +kernel
private theorem triCheck_part_10_16 : triCheck 10 16 16 = true := by decide +kernel
private theorem triCheck_part_10_32 : triCheck 10 32 16 = true := by decide +kernel
private theorem triCheck_part_10_48 : triCheck 10 48 16 = true := by decide +kernel
private theorem triCheck_part_10_64 : triCheck 10 64 16 = true := by decide +kernel
private theorem triCheck_part_10_80 : triCheck 10 80 16 = true := by decide +kernel
private theorem triCheck_part_10_96 : triCheck 10 96 16 = true := by decide +kernel
private theorem triCheck_part_10_112 : triCheck 10 112 16 = true := by decide +kernel
private theorem triCheck_part_10_128 : triCheck 10 128 16 = true := by decide +kernel
private theorem triCheck_part_10_144 : triCheck 10 144 16 = true := by decide +kernel
private theorem triCheck_part_10_160 : triCheck 10 160 16 = true := by decide +kernel
private theorem triCheck_part_10_176 : triCheck 10 176 16 = true := by decide +kernel
private theorem triCheck_part_10_192 : triCheck 10 192 16 = true := by decide +kernel
private theorem triCheck_part_10_208 : triCheck 10 208 16 = true := by decide +kernel
private theorem triCheck_part_10_224 : triCheck 10 224 16 = true := by decide +kernel
private theorem triCheck_part_10_240 : triCheck 10 240 16 = true := by decide +kernel
theorem triCheck_10_0 : triCheck 10 0 256 = true := by
  exact @triCheck_add 10 0 16 240 (by decide +kernel) triCheck_part_10_0 (@triCheck_add 10 16 16 224 (by decide +kernel) triCheck_part_10_16 (@triCheck_add 10 32 16 208 (by decide +kernel) triCheck_part_10_32 (@triCheck_add 10 48 16 192 (by decide +kernel) triCheck_part_10_48 (@triCheck_add 10 64 16 176 (by decide +kernel) triCheck_part_10_64 (@triCheck_add 10 80 16 160 (by decide +kernel) triCheck_part_10_80 (@triCheck_add 10 96 16 144 (by decide +kernel) triCheck_part_10_96 (@triCheck_add 10 112 16 128 (by decide +kernel) triCheck_part_10_112 (@triCheck_add 10 128 16 112 (by decide +kernel) triCheck_part_10_128 (@triCheck_add 10 144 16 96 (by decide +kernel) triCheck_part_10_144 (@triCheck_add 10 160 16 80 (by decide +kernel) triCheck_part_10_160 (@triCheck_add 10 176 16 64 (by decide +kernel) triCheck_part_10_176 (@triCheck_add 10 192 16 48 (by decide +kernel) triCheck_part_10_192 (@triCheck_add 10 208 16 32 (by decide +kernel) triCheck_part_10_208 (@triCheck_add 10 224 16 16 (by decide +kernel) triCheck_part_10_224 (triCheck_part_10_240)))))))))))))))
private theorem triCheck_part_10_256 : triCheck 10 256 16 = true := by decide +kernel
private theorem triCheck_part_10_272 : triCheck 10 272 16 = true := by decide +kernel
private theorem triCheck_part_10_288 : triCheck 10 288 16 = true := by decide +kernel
private theorem triCheck_part_10_304 : triCheck 10 304 16 = true := by decide +kernel
private theorem triCheck_part_10_320 : triCheck 10 320 16 = true := by decide +kernel
private theorem triCheck_part_10_336 : triCheck 10 336 16 = true := by decide +kernel
private theorem triCheck_part_10_352 : triCheck 10 352 16 = true := by decide +kernel
private theorem triCheck_part_10_368 : triCheck 10 368 16 = true := by decide +kernel
private theorem triCheck_part_10_384 : triCheck 10 384 16 = true := by decide +kernel
private theorem triCheck_part_10_400 : triCheck 10 400 16 = true := by decide +kernel
private theorem triCheck_part_10_416 : triCheck 10 416 16 = true := by decide +kernel
private theorem triCheck_part_10_432 : triCheck 10 432 16 = true := by decide +kernel
private theorem triCheck_part_10_448 : triCheck 10 448 16 = true := by decide +kernel
private theorem triCheck_part_10_464 : triCheck 10 464 16 = true := by decide +kernel
private theorem triCheck_part_10_480 : triCheck 10 480 16 = true := by decide +kernel
private theorem triCheck_part_10_496 : triCheck 10 496 16 = true := by decide +kernel
theorem triCheck_10_1 : triCheck 10 256 256 = true := by
  exact @triCheck_add 10 256 16 240 (by decide +kernel) triCheck_part_10_256 (@triCheck_add 10 272 16 224 (by decide +kernel) triCheck_part_10_272 (@triCheck_add 10 288 16 208 (by decide +kernel) triCheck_part_10_288 (@triCheck_add 10 304 16 192 (by decide +kernel) triCheck_part_10_304 (@triCheck_add 10 320 16 176 (by decide +kernel) triCheck_part_10_320 (@triCheck_add 10 336 16 160 (by decide +kernel) triCheck_part_10_336 (@triCheck_add 10 352 16 144 (by decide +kernel) triCheck_part_10_352 (@triCheck_add 10 368 16 128 (by decide +kernel) triCheck_part_10_368 (@triCheck_add 10 384 16 112 (by decide +kernel) triCheck_part_10_384 (@triCheck_add 10 400 16 96 (by decide +kernel) triCheck_part_10_400 (@triCheck_add 10 416 16 80 (by decide +kernel) triCheck_part_10_416 (@triCheck_add 10 432 16 64 (by decide +kernel) triCheck_part_10_432 (@triCheck_add 10 448 16 48 (by decide +kernel) triCheck_part_10_448 (@triCheck_add 10 464 16 32 (by decide +kernel) triCheck_part_10_464 (@triCheck_add 10 480 16 16 (by decide +kernel) triCheck_part_10_480 (triCheck_part_10_496)))))))))))))))
private theorem triCheck_part_11_0 : triCheck 11 0 16 = true := by decide +kernel
private theorem triCheck_part_11_16 : triCheck 11 16 16 = true := by decide +kernel
private theorem triCheck_part_11_32 : triCheck 11 32 16 = true := by decide +kernel
private theorem triCheck_part_11_48 : triCheck 11 48 16 = true := by decide +kernel
private theorem triCheck_part_11_64 : triCheck 11 64 16 = true := by decide +kernel
private theorem triCheck_part_11_80 : triCheck 11 80 16 = true := by decide +kernel
private theorem triCheck_part_11_96 : triCheck 11 96 16 = true := by decide +kernel
private theorem triCheck_part_11_112 : triCheck 11 112 16 = true := by decide +kernel
private theorem triCheck_part_11_128 : triCheck 11 128 16 = true := by decide +kernel
private theorem triCheck_part_11_144 : triCheck 11 144 16 = true := by decide +kernel
private theorem triCheck_part_11_160 : triCheck 11 160 16 = true := by decide +kernel
private theorem triCheck_part_11_176 : triCheck 11 176 16 = true := by decide +kernel
private theorem triCheck_part_11_192 : triCheck 11 192 16 = true := by decide +kernel
private theorem triCheck_part_11_208 : triCheck 11 208 16 = true := by decide +kernel
private theorem triCheck_part_11_224 : triCheck 11 224 16 = true := by decide +kernel
private theorem triCheck_part_11_240 : triCheck 11 240 16 = true := by decide +kernel
theorem triCheck_11_0 : triCheck 11 0 256 = true := by
  exact @triCheck_add 11 0 16 240 (by decide +kernel) triCheck_part_11_0 (@triCheck_add 11 16 16 224 (by decide +kernel) triCheck_part_11_16 (@triCheck_add 11 32 16 208 (by decide +kernel) triCheck_part_11_32 (@triCheck_add 11 48 16 192 (by decide +kernel) triCheck_part_11_48 (@triCheck_add 11 64 16 176 (by decide +kernel) triCheck_part_11_64 (@triCheck_add 11 80 16 160 (by decide +kernel) triCheck_part_11_80 (@triCheck_add 11 96 16 144 (by decide +kernel) triCheck_part_11_96 (@triCheck_add 11 112 16 128 (by decide +kernel) triCheck_part_11_112 (@triCheck_add 11 128 16 112 (by decide +kernel) triCheck_part_11_128 (@triCheck_add 11 144 16 96 (by decide +kernel) triCheck_part_11_144 (@triCheck_add 11 160 16 80 (by decide +kernel) triCheck_part_11_160 (@triCheck_add 11 176 16 64 (by decide +kernel) triCheck_part_11_176 (@triCheck_add 11 192 16 48 (by decide +kernel) triCheck_part_11_192 (@triCheck_add 11 208 16 32 (by decide +kernel) triCheck_part_11_208 (@triCheck_add 11 224 16 16 (by decide +kernel) triCheck_part_11_224 (triCheck_part_11_240)))))))))))))))
private theorem triCheck_part_11_256 : triCheck 11 256 16 = true := by decide +kernel
private theorem triCheck_part_11_272 : triCheck 11 272 16 = true := by decide +kernel
private theorem triCheck_part_11_288 : triCheck 11 288 16 = true := by decide +kernel
private theorem triCheck_part_11_304 : triCheck 11 304 16 = true := by decide +kernel
private theorem triCheck_part_11_320 : triCheck 11 320 16 = true := by decide +kernel
private theorem triCheck_part_11_336 : triCheck 11 336 16 = true := by decide +kernel
private theorem triCheck_part_11_352 : triCheck 11 352 16 = true := by decide +kernel
private theorem triCheck_part_11_368 : triCheck 11 368 16 = true := by decide +kernel
private theorem triCheck_part_11_384 : triCheck 11 384 16 = true := by decide +kernel
private theorem triCheck_part_11_400 : triCheck 11 400 16 = true := by decide +kernel
private theorem triCheck_part_11_416 : triCheck 11 416 16 = true := by decide +kernel
private theorem triCheck_part_11_432 : triCheck 11 432 16 = true := by decide +kernel
private theorem triCheck_part_11_448 : triCheck 11 448 16 = true := by decide +kernel
private theorem triCheck_part_11_464 : triCheck 11 464 16 = true := by decide +kernel
private theorem triCheck_part_11_480 : triCheck 11 480 16 = true := by decide +kernel
private theorem triCheck_part_11_496 : triCheck 11 496 16 = true := by decide +kernel
theorem triCheck_11_1 : triCheck 11 256 256 = true := by
  exact @triCheck_add 11 256 16 240 (by decide +kernel) triCheck_part_11_256 (@triCheck_add 11 272 16 224 (by decide +kernel) triCheck_part_11_272 (@triCheck_add 11 288 16 208 (by decide +kernel) triCheck_part_11_288 (@triCheck_add 11 304 16 192 (by decide +kernel) triCheck_part_11_304 (@triCheck_add 11 320 16 176 (by decide +kernel) triCheck_part_11_320 (@triCheck_add 11 336 16 160 (by decide +kernel) triCheck_part_11_336 (@triCheck_add 11 352 16 144 (by decide +kernel) triCheck_part_11_352 (@triCheck_add 11 368 16 128 (by decide +kernel) triCheck_part_11_368 (@triCheck_add 11 384 16 112 (by decide +kernel) triCheck_part_11_384 (@triCheck_add 11 400 16 96 (by decide +kernel) triCheck_part_11_400 (@triCheck_add 11 416 16 80 (by decide +kernel) triCheck_part_11_416 (@triCheck_add 11 432 16 64 (by decide +kernel) triCheck_part_11_432 (@triCheck_add 11 448 16 48 (by decide +kernel) triCheck_part_11_448 (@triCheck_add 11 464 16 32 (by decide +kernel) triCheck_part_11_464 (@triCheck_add 11 480 16 16 (by decide +kernel) triCheck_part_11_480 (triCheck_part_11_496)))))))))))))))
end SigGolfCandidate.T3M
end
