import Mathlib.Tactic.IntervalCases
import Mathlib.Data.BitVec
set_option debug.skipKernelTC false
namespace OuterTailPacket
structure Five where
  a : BitVec 8
  b : BitVec 8
  c : BitVec 8
  d : BitVec 8
  e : BitVec 8
  deriving DecidableEq

theorem Five.ext {p q : Five} (ha : p.a=q.a) (hb : p.b=q.b) (hc : p.c=q.c)
    (hd : p.d=q.d) (he : p.e=q.e) : p=q := by
  cases p
  cases q
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  rfl

def clear (v : Five) : Five := ⟨v.a &&& 31,v.b &&& 31,v.c &&& 31,v.d &&& 31,v.e &&& 15⟩
def pack (v : Five) (tail : BitVec 16) : Five :=
  ⟨(v.a &&& 31) ||| ((tail.truncate 8 &&& 7) <<< 5),
   (v.b &&& 31) ||| (((tail >>> 3).truncate 8 &&& 7) <<< 5),
   (v.c &&& 31) ||| (((tail >>> 6).truncate 8 &&& 7) <<< 5),
   (v.d &&& 31) ||| (((tail >>> 9).truncate 8 &&& 7) <<< 5),
   (v.e &&& 15) ||| (((tail >>> 12).truncate 8 &&& 15) <<< 4)⟩
def unpack (v : Five) : Five × BitVec 16 :=
  (clear v,(v.a >>> 5).setWidth 16 ||| ((v.b >>> 5).setWidth 16 <<< 3) |||
    ((v.c >>> 5).setWidth 16 <<< 6) ||| ((v.d >>> 5).setWidth 16 <<< 9) |||
    ((v.e >>> 4).setWidth 16 <<< 12))

theorem unpack_pack (v : Five) (tail : BitVec 16) : unpack (pack v tail)=(clear v,tail) := by
  cases v
  apply Prod.ext
  · apply Five.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      interval_cases i <;> simp [unpack,pack,clear,BitVec.truncate]
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [unpack,pack,clear,BitVec.truncate]

theorem pack_unpack (v : Five) : pack (unpack v).1 (unpack v).2=v := by
  cases v
  apply Five.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    interval_cases i <;> simp [unpack,pack,clear,BitVec.truncate]

#print axioms unpack_pack
#print axioms pack_unpack
end OuterTailPacket
