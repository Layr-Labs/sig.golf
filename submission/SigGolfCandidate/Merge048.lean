import Lean.Elab.Term

-- ==== merged from T3M_Images_Literals ====
section

/-!
Large program images contain hundreds of thousands of fixed-width numerals.
Elaborate these lists directly instead of resolving `OfNat` for every element.
The result is an ordinary list of `BitVec.ofNat` terms, checked by Lean's kernel;
no evaluation, external data, or additional axioms are involved.
-/

open Lean Elab Term in
elab "bv_list% " width:num " [" values:num,* "]" : term => do
  let w := mkNatLit width.getNat
  let ty := mkApp (mkConst ``BitVec) w
  let xs := values.getElems.map fun n =>
    mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit n.getNat)
  return xs.foldr (fun x tail => mkApp3 (mkConst ``List.cons [0]) ty x tail)
    (mkApp (mkConst ``List.nil [0]) ty)
end
