import SigGolfCandidate.OuterTailPacket
set_option debug.skipKernelTC false
namespace OuterTailBytes
open OuterTailPacket
abbrev Payload := Fin 5184 → BitVec 8
abbrev Old := Payload × BitVec 16

def read (b : Payload) : Five := ⟨b 415,b 815,b 1215,b 1615,b 1823⟩
def write (b : Payload) (v : Five) : Payload := fun i =>
  if i.val=415 then v.a else if i.val=815 then v.b else if i.val=1215 then v.c
  else if i.val=1615 then v.d else if i.val=1823 then v.e else b i

theorem read_write (b : Payload) (v : Five) : read (write b v)=v := by cases v;rfl

theorem write_write (b : Payload) (v w : Five) : write (write b v) w=write b w := by
  funext i
  unfold write
  split_ifs <;> rfl

theorem write_read (b : Payload) : write b (read b)=b := by
  funext i
  unfold write
  split_ifs with h0 h1 h2 h3 h4
  · have hi : i=(415 : Fin 5184) := Fin.ext h0
    subst i
    rfl
  · have hi : i=(815 : Fin 5184) := Fin.ext h1
    subst i
    rfl
  · have hi : i=(1215 : Fin 5184) := Fin.ext h2
    subst i
    rfl
  · have hi : i=(1615 : Fin 5184) := Fin.ext h3
    subst i
    rfl
  · have hi : i=(1823 : Fin 5184) := Fin.ext h4
    subst i
    rfl
  · rfl

def compress (b : Old) : Payload := write b.1 (pack (read b.1) b.2)
def expand (b : Payload) : Old := (write b (unpack (read b)).1,(unpack (read b)).2)

theorem compress_expand (b : Payload) : compress (expand b)=b := by
  unfold compress expand
  rw [read_write,pack_unpack,write_write,write_read]

theorem expand_compress_normalized (b : Old) : expand (compress b)=(write b.1 (clear (read b.1)),b.2) := by
  unfold compress expand
  rw [read_write,unpack_pack,write_write]

theorem expand_compress (b : Old) (hc : clear (read b.1)=read b.1) : expand (compress b)=b := by
  rw [expand_compress_normalized,hc,write_read]

#print axioms compress_expand
#print axioms expand_compress
end OuterTailBytes
