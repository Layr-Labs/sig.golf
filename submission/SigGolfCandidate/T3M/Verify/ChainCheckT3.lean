import SigGolfCandidate.T3M.Verify.ChainCheckT2

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
