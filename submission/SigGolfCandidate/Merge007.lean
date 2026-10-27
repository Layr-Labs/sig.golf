import Mathlib
import SigGolfCandidate.Merge005

-- ==== merged from T3_FullCache_Primitives ====
section

namespace SphincsSecurity
def macPrime : Nat := 2 ^ 61 - 1
def polyMac (k : Nat) (chunks : List Nat) : Nat :=
  chunks.foldl (fun acc c => (acc + c) * k % macPrime) 0
def chunks32 : HashInput → List Nat
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat) :: chunks32 rest
  | _ => []
def answerOfWords (w0 w1 w2 w3 : BitVec 64) : HashOutput :=
  BitVec.ofNat 256 (w0.toNat + 2^64*w1.toNat + 2^128*w2.toNat + 2^192*w3.toNat)
end SphincsSecurity
end
-- ==== merged from T3_FullCache_MacDefs ====
section

namespace SiggolfT3Mac4
open SphincsSecurity
set_option autoImplicit false
abbrev MacTag := Fin 4 → BitVec 64
abbrev MacKey := Fin 2 → HashOutput
def macKeyWord (key : MacKey) (j : Fin 4) : Nat :=
  ((key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2)) 61).toNat
def macPadWord (key : MacKey) (j : Fin 4) : BitVec 64 :=
  (key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2) + 64) 64
def macTag (key : MacKey) (data : HashInput) : MacTag :=
  fun j => BitVec.ofNat 64 (polyMac (macKeyWord key j) (chunks32 data)) + macPadWord key j
def encodeTag (tag : MacTag) : HashOutput :=
  answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)
def decodeTag (tag : HashOutput) : MacTag :=
  fun i => tag.extractLsb' (64*i.val) 64
end SiggolfT3Mac4
end
