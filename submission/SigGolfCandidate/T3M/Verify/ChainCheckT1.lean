import SigGolfCandidate.T3M.Verify.ChainCheckT0

set_option Elab.async false
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
