import Lean.Elab.Term
set_option debug.skipKernelTC false
set_option linter.all false

namespace SigGolfCandidate.ImageLiteral
/-- Decode a chunk of little-endian fixed-width words using kernel-reducible operations. -/
def unpack (width packed len : Nat) : List (BitVec width) :=
  (List.range len).map (fun i => BitVec.ofNat width (packed >>> (width * i)))
end SigGolfCandidate.ImageLiteral

open Lean Elab Term in
elab "bv_list% " width:num " [" values:num,* "]" : term => do
  let widthN := width.getNat
  unless widthN ≤ 32 ∧ widthN < 2 ^ 6 do
    throwError "bv_list%: word width must be at most 32"
  let w := mkNatLit widthN
  let ty := mkApp (mkConst ``BitVec) w
  let vals := values.getElems
  if vals.size < 128 then
    let xs := vals.map fun n => mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit n.getNat)
    return xs.foldr (fun x tail => mkApp3 (mkConst ``List.cons [0]) ty x tail)
      (mkApp (mkConst ``List.nil [0]) ty)
  let mut result := mkApp (mkConst ``List.nil [0]) ty
  let blockCount := (vals.size + 127) / 128
  for reverseIndex in [:blockCount] do
    let blockIndex := blockCount - 1 - reverseIndex
    let begin := blockIndex * 128
    let len := min 128 (vals.size - begin)
    let mut packed := 0
    for reverseItem in [:len] do
      let item := begin + len - 1 - reverseItem
      packed := (packed <<< widthN) + (vals[item]!.getNat % (2 ^ widthN))
    unless packed < 2 ^ 4096 ∧ len < 2 ^ 8 do
      throwError "bv_list%: a packed chunk must stay below 2 ^ 4096"
    let part := mkApp3 (mkConst ``SigGolfCandidate.ImageLiteral.unpack)
      w (mkNatLit packed) (mkNatLit len)
    result := mkApp3 (mkConst ``List.append [0]) ty part result
  return result
