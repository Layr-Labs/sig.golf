import SigGolfCandidate.OuterTailPacket
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
namespace OuterTailBytes
open OuterTailPacket
abbrev OldPayload := Fin 5184 → BitVec 8
abbrev Payload := Fin 5183 → BitVec 8
abbrev Old := OldPayload × BitVec 16

def originalIndex (i : Fin 5183) : Fin 5184 := ⟨if i.val=1823 then 5183 else i.val,by split_ifs <;> omega⟩
def compactIndex (i : Fin 5184) : Fin 5183 := ⟨if i.val=5183 then 1823 else i.val,by split_ifs <;> omega⟩
theorem original_ne (i : Fin 5183) : (originalIndex i).val ≠ 1823 := by simp only [originalIndex,Fin.val_mk];split_ifs <;> omega
theorem compact_original (i : Fin 5183) : compactIndex (originalIndex i)=i := by
  apply Fin.ext;simp only [compactIndex,originalIndex,Fin.val_mk];split_ifs <;> omega
theorem original_compact (i : Fin 5184) (h : i.val≠1823) : originalIndex (compactIndex i)=i := by
  apply Fin.ext;simp only [compactIndex,originalIndex,Fin.val_mk];split_ifs <;> omega
theorem original_small (i : Fin 5183) (c : Nat) (hc : c<1823) : (originalIndex i).val=c ↔ i.val=c := by
  simp only [originalIndex,Fin.val_mk];split_ifs <;> omega
theorem compact_small (i : Fin 5184) (c : Nat) (hc : c<1822) : (compactIndex i).val=c ↔ i.val=c := by
  simp only [compactIndex,Fin.val_mk];split_ifs <;> omega

def keep (b : OldPayload) : Payload := fun i => b (originalIndex i)
def inflate (b : Payload) (e : BitVec 8) : OldPayload := fun i => if i.val=1823 then e else b (compactIndex i)
def read (b : OldPayload) : Five := ⟨b 415,b 815,b 1215,b 1615,b 1823⟩
def readNew (b : Payload) : Four := ⟨b 415,b 815,b 1215,b 1615⟩
def writeOld (b : OldPayload) (v : Five) : OldPayload := fun i =>
  if i.val=415 then v.a else if i.val=815 then v.b else if i.val=1215 then v.c
  else if i.val=1615 then v.d else if i.val=1823 then v.e else b i
def writeNew (b : Payload) (v : Four) : Payload := fun i =>
  if i.val=415 then v.a else if i.val=815 then v.b else if i.val=1215 then v.c
  else if i.val=1615 then v.d else b i
def write (b : OldPayload) (v : Four) : Payload := writeNew (keep b) v

theorem read_writeOld (b : OldPayload) (v : Five) : read (writeOld b v)=v := by cases v;rfl
theorem readNew_writeNew (b : Payload) (v : Four) : readNew (writeNew b v)=v := by cases v;rfl
theorem writeNew_writeNew (b : Payload) (v w : Four) : writeNew (writeNew b v) w=writeNew b w := by
  funext i;unfold writeNew;split_ifs <;> rfl
theorem writeOld_read (b : OldPayload) : writeOld b (read b)=b := by
  funext i;unfold writeOld;split_ifs with h0 h1 h2 h3 h4
  · have hi : i=(415 : Fin 5184) := Fin.ext h0;subst i;rfl
  · have hi : i=(815 : Fin 5184) := Fin.ext h1;subst i;rfl
  · have hi : i=(1215 : Fin 5184) := Fin.ext h2;subst i;rfl
  · have hi : i=(1615 : Fin 5184) := Fin.ext h3;subst i;rfl
  · have hi : i=(1823 : Fin 5184) := Fin.ext h4;subst i;rfl
  · rfl
theorem writeNew_readNew (b : Payload) : writeNew b (readNew b)=b := by
  funext i;unfold writeNew;split_ifs with h0 h1 h2 h3
  · have hi : i=(415 : Fin 5183) := Fin.ext h0;subst i;rfl
  · have hi : i=(815 : Fin 5183) := Fin.ext h1;subst i;rfl
  · have hi : i=(1215 : Fin 5183) := Fin.ext h2;subst i;rfl
  · have hi : i=(1615 : Fin 5183) := Fin.ext h3;subst i;rfl
  · rfl

theorem keep_inflate (b : Payload) (e : BitVec 8) : keep (inflate b e)=b := by
  funext i;simp only [keep,inflate,original_ne,if_false,compact_original]
theorem keep_writeOld (b : OldPayload) (v : Five) :
    keep (writeOld b v)=writeNew (keep b) ⟨v.a,v.b,v.c,v.d⟩ := by
  funext i
  simp only [keep,writeOld,writeNew,original_small i 415 (by decide),original_small i 815 (by decide),
    original_small i 1215 (by decide),original_small i 1615 (by decide),original_ne,if_false]
theorem restore_write (b : OldPayload) (v : Four) (w : Five) :
    writeOld (inflate (write b v) 0) w=writeOld b w := by
  funext i
  simp only [writeOld]
  split_ifs with h0 h1 h2 h3 h4 <;> try rfl
  simp only [inflate,h4,if_false,write,writeNew,compact_small i 415 (by decide),
    compact_small i 815 (by decide),compact_small i 1215 (by decide),compact_small i 1615 (by decide),
    h0,h1,h2,h3,if_false,keep,original_compact i h4]

def compress (b : Old) : Payload := write b.1 (pack (read b.1) b.2)
def expand (b : Payload) : Old :=
  let v := unpack (readNew b)
  (writeOld (inflate b 0) v.1,v.2)

theorem compress_expand (b : Payload) : compress (expand b)=b := by
  unfold compress expand write
  rw [read_writeOld,pack_unpack,keep_writeOld,keep_inflate,writeNew_writeNew,writeNew_readNew]

theorem expand_compress_normalized (b : Old) : expand (compress b)=(writeOld b.1 (clear (read b.1)),b.2) := by
  unfold compress expand
  simp only [write,readNew_writeNew,unpack_pack]
  exact Prod.ext (restore_write b.1 _ _) rfl

theorem expand_compress (b : Old) (hc : clear (read b.1)=read b.1) : expand (compress b)=b := by
  rw [expand_compress_normalized,hc,writeOld_read]

#print axioms compress_expand
#print axioms expand_compress
end OuterTailBytes
