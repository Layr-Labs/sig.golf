import SigGolfCandidate.T3M.Verify.ChainCheckT3

set_option Elab.async false

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
