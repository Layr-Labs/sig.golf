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

structure Four where
  a : BitVec 8
  b : BitVec 8
  c : BitVec 8
  d : BitVec 8
  deriving DecidableEq

theorem Four.ext {p q : Four} (ha : p.a=q.a) (hb : p.b=q.b) (hc : p.c=q.c)
    (hd : p.d=q.d) : p=q := by
  cases p
  cases q
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

def clear (v : Five) : Five := ⟨v.a &&& 7,v.b &&& 7,v.c &&& 7,v.d &&& 7,v.e &&& 15⟩
def packedWord (v : Five) (tail : BitVec 16) : BitVec 32 :=
  (v.a &&& 7).setWidth 32 ||| ((v.b &&& 7).setWidth 32 <<< 3) |||
  ((v.c &&& 7).setWidth 32 <<< 6) ||| ((v.d &&& 7).setWidth 32 <<< 9) |||
  ((v.e &&& 15).setWidth 32 <<< 12) ||| (tail.setWidth 32 <<< 16)
def pack (v : Five) (tail : BitVec 16) : Four :=
  let w := packedWord v tail
  ⟨w.extractLsb' 0 8,w.extractLsb' 8 8,w.extractLsb' 16 8,w.extractLsb' 24 8⟩
def unpack (v : Four) : Five × BitVec 16 :=
  let w : BitVec 32 := v.a.setWidth 32 ||| (v.b.setWidth 32 <<< 8) |||
    (v.c.setWidth 32 <<< 16) ||| (v.d.setWidth 32 <<< 24)
  (⟨(w.extractLsb' 0 3).setWidth 8,(w.extractLsb' 3 3).setWidth 8,
    (w.extractLsb' 6 3).setWidth 8,(w.extractLsb' 9 3).setWidth 8,
    (w.extractLsb' 12 4).setWidth 8⟩,w.extractLsb' 16 16)

theorem unpack_pack (v : Five) (tail : BitVec 16) : unpack (pack v tail)=(clear v,tail) := by
  cases v
  apply Prod.ext
  · apply Five.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      interval_cases i <;> simp [unpack,pack,clear,packedWord,BitVec.getLsbD_append,BitVec.getElem_append]
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [unpack,pack,clear,packedWord,BitVec.getLsbD_append,BitVec.getElem_append]

theorem pack_unpack (v : Four) : pack (unpack v).1 (unpack v).2=v := by
  cases v
  apply Four.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    interval_cases i <;> simp [unpack,pack,clear,packedWord,BitVec.getLsbD_append,BitVec.getElem_append]

#print axioms unpack_pack
#print axioms pack_unpack
end OuterTailPacket
