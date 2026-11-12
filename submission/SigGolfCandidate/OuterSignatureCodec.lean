import SigGolfCandidate.OuterTailBytes
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace OuterSignatureCodec

def fromBits (n : Nat) (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem fromBits_get (n : Nat) (f : Fin n → Bool) (i : Fin n) :
    (fromBits n f).getLsbD i.val = f i := by
  simp only [fromBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

def bytes (n : Nat) (v : BitVec (8*n)) : Fin n → BitVec 8 := fun i => v.extractLsb' (8*i.val) 8

def ofBytes (n : Nat) (b : Fin n → BitVec 8) : BitVec (8*n) :=
  fromBits (8*n) fun i => (b ⟨i.val/8, by omega⟩).getLsbD (i.val%8)

theorem bytes_ofBytes (n : Nat) (b : Fin n → BitVec 8) : bytes n (ofBytes n b)=b := by
  funext i
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [bytes,BitVec.getLsbD_extractLsb']
  have hlt : 8*i.val+k<8*n := by omega
  simp only [hk, decide_true, Bool.true_and]
  change (fromBits (8*n) _).getLsbD (8*i.val+k)=_
  rw [fromBits_get (8*n) _ ⟨8*i.val+k,hlt⟩]
  have hd : (8*i.val+k)/8=i.val := by omega
  have hm : (8*i.val+k)%8=k := by omega
  simp only [hd,hm]

theorem ofBytes_bytes (n : Nat) (v : BitVec (8*n)) : ofBytes n (bytes n v)=v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold ofBytes
  rw [fromBits_get (8*n) _ ⟨i,hi⟩]
  simp only [bytes,BitVec.getLsbD_extractLsb']
  have hm : i%8<8 := Nat.mod_lt _ (by decide)
  have he : 8*(i/8)+i%8=i := by omega
  simp [hm,he]

abbrev OldSig := BitVec (8*5186)
abbrev NewSig := BitVec (8*5184)
def splitOld (v : OldSig) : OuterTailBytes.Old :=
  (bytes 5184 (v.extractLsb' 0 (8*5184)),v.extractLsb' (8*5184) 16)
def joinOld (b : OuterTailBytes.Old) : OldSig := b.2 ++ ofBytes 5184 b.1

theorem split_join (b : OuterTailBytes.Old) : splitOld (joinOld b)=b := by
  simp only [splitOld,joinOld,BitVec.extractLsb'_append_eq_left,BitVec.extractLsb'_append_eq_right,bytes_ofBytes]

theorem join_split (v : OldSig) : joinOld (splitOld v)=v := by
  simp only [joinOld,splitOld,ofBytes_bytes]
  exact BitVec.extractLsb'_append_extractLsb'

def compress (v : OldSig) : NewSig := ofBytes 5184 (OuterTailBytes.compress (splitOld v))
def expand (v : NewSig) : OldSig := joinOld (OuterTailBytes.expand (bytes 5184 v))

theorem compress_expand (v : NewSig) : compress (expand v)=v := by
  simp only [compress,expand,split_join,OuterTailBytes.compress_expand,ofBytes_bytes]

theorem expand_compress (v : OldSig)
    (hc : OuterTailPacket.clear (OuterTailBytes.read (splitOld v).1)=OuterTailBytes.read (splitOld v).1) :
    expand (compress v)=v := by
  simp only [expand,compress,bytes_ofBytes,OuterTailBytes.expand_compress _ hc,join_split]

#print axioms compress_expand
#print axioms expand_compress
#print axioms bytes_ofBytes
#print axioms ofBytes_bytes
end OuterSignatureCodec
