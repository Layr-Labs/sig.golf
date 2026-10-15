import Lean.Elab.Term

/-! Fixed-width literal lists are stored as a base-2^width natural numeral.
The decoder retains the exact List (BitVec width) definition while avoiding
large repeated term trees and kernel UTF-8 string decoding. -/

namespace SigGolfCandidate.T3M.Images

def decodePackedWords (width : Nat) : Nat → Nat → List (BitVec width)
  | 0, _ => []
  | count + 1, packed => BitVec.ofNat width packed :: decodePackedWords width count (packed / 2 ^ width)

@[simp] theorem decodePackedWords_length (width count packed : Nat) :
    (decodePackedWords width count packed).length = count := by
  induction count generalizing packed with
  | zero => simp [decodePackedWords]
  | succ count ih => simp [decodePackedWords, ih]

end SigGolfCandidate.T3M.Images

open Lean Elab Term in
elab "bv_list% " width:num " [" values:num,* "]" : term => do
  let radix := 2 ^ width.getNat
  let mut packed := 0
  for value in values.getElems.reverse do
    packed := value.getNat % radix + radix * packed
  return mkApp3 (Lean.mkConst ``SigGolfCandidate.T3M.Images.decodePackedWords)
    (mkNatLit width.getNat) (mkNatLit values.getElems.size) (mkNatLit packed)
