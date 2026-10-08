import SigGolfCandidate.T3M.Verify.ChainCheckT1

set_option Elab.async false

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
