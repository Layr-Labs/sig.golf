import SigGolfCandidate.T3M.Verify.ChainCheckParts

set_option Elab.async false

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
