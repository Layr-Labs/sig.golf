import SigGolfCandidate.T3M.Verify.ChainCheckT5

set_option Elab.async false

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
private theorem triCheck_part_12_0 : triCheck 12 0 16 = true := by decide +kernel
private theorem triCheck_part_12_16 : triCheck 12 16 16 = true := by decide +kernel
private theorem triCheck_part_12_32 : triCheck 12 32 16 = true := by decide +kernel
private theorem triCheck_part_12_48 : triCheck 12 48 16 = true := by decide +kernel
private theorem triCheck_part_12_64 : triCheck 12 64 16 = true := by decide +kernel
private theorem triCheck_part_12_80 : triCheck 12 80 16 = true := by decide +kernel
private theorem triCheck_part_12_96 : triCheck 12 96 16 = true := by decide +kernel
private theorem triCheck_part_12_112 : triCheck 12 112 16 = true := by decide +kernel
private theorem triCheck_part_12_128 : triCheck 12 128 16 = true := by decide +kernel
private theorem triCheck_part_12_144 : triCheck 12 144 16 = true := by decide +kernel
private theorem triCheck_part_12_160 : triCheck 12 160 16 = true := by decide +kernel
private theorem triCheck_part_12_176 : triCheck 12 176 16 = true := by decide +kernel
private theorem triCheck_part_12_192 : triCheck 12 192 16 = true := by decide +kernel
private theorem triCheck_part_12_208 : triCheck 12 208 16 = true := by decide +kernel
private theorem triCheck_part_12_224 : triCheck 12 224 16 = true := by decide +kernel
private theorem triCheck_part_12_240 : triCheck 12 240 16 = true := by decide +kernel
theorem triCheck_12_0 : triCheck 12 0 256 = true := by
  exact @triCheck_add 12 0 16 240 (by decide +kernel) triCheck_part_12_0 (@triCheck_add 12 16 16 224 (by decide +kernel) triCheck_part_12_16 (@triCheck_add 12 32 16 208 (by decide +kernel) triCheck_part_12_32 (@triCheck_add 12 48 16 192 (by decide +kernel) triCheck_part_12_48 (@triCheck_add 12 64 16 176 (by decide +kernel) triCheck_part_12_64 (@triCheck_add 12 80 16 160 (by decide +kernel) triCheck_part_12_80 (@triCheck_add 12 96 16 144 (by decide +kernel) triCheck_part_12_96 (@triCheck_add 12 112 16 128 (by decide +kernel) triCheck_part_12_112 (@triCheck_add 12 128 16 112 (by decide +kernel) triCheck_part_12_128 (@triCheck_add 12 144 16 96 (by decide +kernel) triCheck_part_12_144 (@triCheck_add 12 160 16 80 (by decide +kernel) triCheck_part_12_160 (@triCheck_add 12 176 16 64 (by decide +kernel) triCheck_part_12_176 (@triCheck_add 12 192 16 48 (by decide +kernel) triCheck_part_12_192 (@triCheck_add 12 208 16 32 (by decide +kernel) triCheck_part_12_208 (@triCheck_add 12 224 16 16 (by decide +kernel) triCheck_part_12_224 (triCheck_part_12_240)))))))))))))))
private theorem triCheck_part_12_256 : triCheck 12 256 16 = true := by decide +kernel
private theorem triCheck_part_12_272 : triCheck 12 272 16 = true := by decide +kernel
private theorem triCheck_part_12_288 : triCheck 12 288 16 = true := by decide +kernel
private theorem triCheck_part_12_304 : triCheck 12 304 16 = true := by decide +kernel
private theorem triCheck_part_12_320 : triCheck 12 320 16 = true := by decide +kernel
private theorem triCheck_part_12_336 : triCheck 12 336 16 = true := by decide +kernel
private theorem triCheck_part_12_352 : triCheck 12 352 16 = true := by decide +kernel
private theorem triCheck_part_12_368 : triCheck 12 368 16 = true := by decide +kernel
private theorem triCheck_part_12_384 : triCheck 12 384 16 = true := by decide +kernel
private theorem triCheck_part_12_400 : triCheck 12 400 16 = true := by decide +kernel
private theorem triCheck_part_12_416 : triCheck 12 416 16 = true := by decide +kernel
private theorem triCheck_part_12_432 : triCheck 12 432 16 = true := by decide +kernel
private theorem triCheck_part_12_448 : triCheck 12 448 16 = true := by decide +kernel
private theorem triCheck_part_12_464 : triCheck 12 464 16 = true := by decide +kernel
private theorem triCheck_part_12_480 : triCheck 12 480 16 = true := by decide +kernel
private theorem triCheck_part_12_496 : triCheck 12 496 16 = true := by decide +kernel
theorem triCheck_12_1 : triCheck 12 256 256 = true := by
  exact @triCheck_add 12 256 16 240 (by decide +kernel) triCheck_part_12_256 (@triCheck_add 12 272 16 224 (by decide +kernel) triCheck_part_12_272 (@triCheck_add 12 288 16 208 (by decide +kernel) triCheck_part_12_288 (@triCheck_add 12 304 16 192 (by decide +kernel) triCheck_part_12_304 (@triCheck_add 12 320 16 176 (by decide +kernel) triCheck_part_12_320 (@triCheck_add 12 336 16 160 (by decide +kernel) triCheck_part_12_336 (@triCheck_add 12 352 16 144 (by decide +kernel) triCheck_part_12_352 (@triCheck_add 12 368 16 128 (by decide +kernel) triCheck_part_12_368 (@triCheck_add 12 384 16 112 (by decide +kernel) triCheck_part_12_384 (@triCheck_add 12 400 16 96 (by decide +kernel) triCheck_part_12_400 (@triCheck_add 12 416 16 80 (by decide +kernel) triCheck_part_12_416 (@triCheck_add 12 432 16 64 (by decide +kernel) triCheck_part_12_432 (@triCheck_add 12 448 16 48 (by decide +kernel) triCheck_part_12_448 (@triCheck_add 12 464 16 32 (by decide +kernel) triCheck_part_12_464 (@triCheck_add 12 480 16 16 (by decide +kernel) triCheck_part_12_480 (triCheck_part_12_496)))))))))))))))
private theorem triCheck_part_13_0 : triCheck 13 0 16 = true := by decide +kernel
private theorem triCheck_part_13_16 : triCheck 13 16 16 = true := by decide +kernel
private theorem triCheck_part_13_32 : triCheck 13 32 16 = true := by decide +kernel
private theorem triCheck_part_13_48 : triCheck 13 48 16 = true := by decide +kernel
private theorem triCheck_part_13_64 : triCheck 13 64 16 = true := by decide +kernel
private theorem triCheck_part_13_80 : triCheck 13 80 16 = true := by decide +kernel
private theorem triCheck_part_13_96 : triCheck 13 96 16 = true := by decide +kernel
private theorem triCheck_part_13_112 : triCheck 13 112 16 = true := by decide +kernel
private theorem triCheck_part_13_128 : triCheck 13 128 16 = true := by decide +kernel
private theorem triCheck_part_13_144 : triCheck 13 144 16 = true := by decide +kernel
private theorem triCheck_part_13_160 : triCheck 13 160 16 = true := by decide +kernel
private theorem triCheck_part_13_176 : triCheck 13 176 16 = true := by decide +kernel
private theorem triCheck_part_13_192 : triCheck 13 192 16 = true := by decide +kernel
private theorem triCheck_part_13_208 : triCheck 13 208 16 = true := by decide +kernel
private theorem triCheck_part_13_224 : triCheck 13 224 16 = true := by decide +kernel
private theorem triCheck_part_13_240 : triCheck 13 240 16 = true := by decide +kernel
theorem triCheck_13_0 : triCheck 13 0 256 = true := by
  exact @triCheck_add 13 0 16 240 (by decide +kernel) triCheck_part_13_0 (@triCheck_add 13 16 16 224 (by decide +kernel) triCheck_part_13_16 (@triCheck_add 13 32 16 208 (by decide +kernel) triCheck_part_13_32 (@triCheck_add 13 48 16 192 (by decide +kernel) triCheck_part_13_48 (@triCheck_add 13 64 16 176 (by decide +kernel) triCheck_part_13_64 (@triCheck_add 13 80 16 160 (by decide +kernel) triCheck_part_13_80 (@triCheck_add 13 96 16 144 (by decide +kernel) triCheck_part_13_96 (@triCheck_add 13 112 16 128 (by decide +kernel) triCheck_part_13_112 (@triCheck_add 13 128 16 112 (by decide +kernel) triCheck_part_13_128 (@triCheck_add 13 144 16 96 (by decide +kernel) triCheck_part_13_144 (@triCheck_add 13 160 16 80 (by decide +kernel) triCheck_part_13_160 (@triCheck_add 13 176 16 64 (by decide +kernel) triCheck_part_13_176 (@triCheck_add 13 192 16 48 (by decide +kernel) triCheck_part_13_192 (@triCheck_add 13 208 16 32 (by decide +kernel) triCheck_part_13_208 (@triCheck_add 13 224 16 16 (by decide +kernel) triCheck_part_13_224 (triCheck_part_13_240)))))))))))))))
private theorem triCheck_part_13_256 : triCheck 13 256 16 = true := by decide +kernel
private theorem triCheck_part_13_272 : triCheck 13 272 16 = true := by decide +kernel
private theorem triCheck_part_13_288 : triCheck 13 288 16 = true := by decide +kernel
private theorem triCheck_part_13_304 : triCheck 13 304 16 = true := by decide +kernel
private theorem triCheck_part_13_320 : triCheck 13 320 16 = true := by decide +kernel
private theorem triCheck_part_13_336 : triCheck 13 336 16 = true := by decide +kernel
private theorem triCheck_part_13_352 : triCheck 13 352 16 = true := by decide +kernel
private theorem triCheck_part_13_368 : triCheck 13 368 16 = true := by decide +kernel
private theorem triCheck_part_13_384 : triCheck 13 384 16 = true := by decide +kernel
private theorem triCheck_part_13_400 : triCheck 13 400 16 = true := by decide +kernel
private theorem triCheck_part_13_416 : triCheck 13 416 16 = true := by decide +kernel
private theorem triCheck_part_13_432 : triCheck 13 432 16 = true := by decide +kernel
private theorem triCheck_part_13_448 : triCheck 13 448 16 = true := by decide +kernel
private theorem triCheck_part_13_464 : triCheck 13 464 16 = true := by decide +kernel
private theorem triCheck_part_13_480 : triCheck 13 480 16 = true := by decide +kernel
private theorem triCheck_part_13_496 : triCheck 13 496 16 = true := by decide +kernel
theorem triCheck_13_1 : triCheck 13 256 256 = true := by
  exact @triCheck_add 13 256 16 240 (by decide +kernel) triCheck_part_13_256 (@triCheck_add 13 272 16 224 (by decide +kernel) triCheck_part_13_272 (@triCheck_add 13 288 16 208 (by decide +kernel) triCheck_part_13_288 (@triCheck_add 13 304 16 192 (by decide +kernel) triCheck_part_13_304 (@triCheck_add 13 320 16 176 (by decide +kernel) triCheck_part_13_320 (@triCheck_add 13 336 16 160 (by decide +kernel) triCheck_part_13_336 (@triCheck_add 13 352 16 144 (by decide +kernel) triCheck_part_13_352 (@triCheck_add 13 368 16 128 (by decide +kernel) triCheck_part_13_368 (@triCheck_add 13 384 16 112 (by decide +kernel) triCheck_part_13_384 (@triCheck_add 13 400 16 96 (by decide +kernel) triCheck_part_13_400 (@triCheck_add 13 416 16 80 (by decide +kernel) triCheck_part_13_416 (@triCheck_add 13 432 16 64 (by decide +kernel) triCheck_part_13_432 (@triCheck_add 13 448 16 48 (by decide +kernel) triCheck_part_13_448 (@triCheck_add 13 464 16 32 (by decide +kernel) triCheck_part_13_464 (@triCheck_add 13 480 16 16 (by decide +kernel) triCheck_part_13_480 (triCheck_part_13_496)))))))))))))))
end SigGolfCandidate.T3M
