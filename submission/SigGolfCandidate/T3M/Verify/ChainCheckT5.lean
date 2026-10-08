import SigGolfCandidate.T3M.Verify.ChainCheckT4

set_option Elab.async false

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
