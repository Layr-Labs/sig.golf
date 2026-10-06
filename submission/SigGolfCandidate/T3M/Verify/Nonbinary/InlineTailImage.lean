import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailPackets

/- Unselected next image. Exactly64 unused JT windows are replaced by the
   complete inline macros; all other original chunks and all data are reused.
   OriginalImages.verifyImage remains the selected7539 candidate. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def patchRow (rank : Nat) (row : List (BitVec 32)) : List (BitVec 32) :=
  row.take 40 ++ words rank ++ List.replicate (64-(words rank).length) 19 ++ row.drop 104

def mapRows (start : Nat) : List (List (BitVec 32)) → List (List (BitVec 32))
  | [] => []
  | row::rows =>
      (if 691 ≤ start ∧ start<755 then patchRow (start-691) row else row)::
        mapRows (start+1) rows
def chunks : List (List (BitVec 32)) := mapRows 0 lChunks
def code : List (BitVec 32) := chunks.flatten
def image : Image := ⟨code,Images.verifyData⟩

-- The complete64-word allocation is important: it cannot change the next row.
theorem patchRow_length (rank : Nat) (hr : rank<64) (row : List (BitVec 32))
    (hlen : row.length=256) : (patchRow rank row).length=256 := by
  have h := List.all_eq_true.mp macro_length_check rank (List.mem_range.mpr hr)
  have he := of_decide_eq_true h
  have hl (d : Nat) : pieceLen d≤10 := by
    unfold pieceLen
    split_ifs <;> omega
  have hw : (words rank).length≤42 := by
    rw [he]
    have h0:=hl (digit rank 0)
    have h1:=hl (digit rank 1)
    have h2:=hl (digit rank 2)
    omega
  simp [patchRow,hlen,List.length_take,List.length_drop]
  omega

-- This proof needs no selected-image or execution assumption.
theorem patchRow_prefix (rank : Nat) (row : List (BitVec 32)) (hl : 40≤row.length) :
    words rank <+: (patchRow rank row).drop 40 := by
  refine ⟨List.replicate (64-(words rank).length) 19 ++ row.drop 104,?_⟩
  simp [patchRow,List.drop_append,List.length_take,Nat.min_eq_left hl,List.append_assoc]

-- Symbolic transport of alreadychecked chunk lengths avoids re-evaluating
-- the original250k native words merely to learn that each full chunk is256.
theorem mapRows_length (rows : List (List (BitVec 32))) (start : Nat) :
    (mapRows start rows).length=rows.length := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih => simp [mapRows,ih]

theorem mapRows_ok (rows : List (List (BitVec 32))) (start : Nat)
    (h : (rows.dropLast.all fun c => c.length==256)=true) :
    ((mapRows start rows).dropLast.all fun c => c.length==256)=true := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    cases rows with
    | nil => simp [mapRows]
    | cons row' rows =>
      simp only [List.dropLast_cons_cons,List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
      have htail:=ih (start+1) h.2
      have hhead : (if 691 ≤ start ∧ start<755 then patchRow (start-691) row else row).length=256 := by
        split_ifs with hs
        · exact patchRow_length (start-691) (by omega) row h.1
        · exact h.1
      simpa only [mapRows,List.dropLast_cons_cons,List.all_cons,Bool.and_eq_true,beq_iff_eq]
        using And.intro hhead htail

theorem chunks_length : chunks.length=985 := by
  rw [chunks,mapRows_length,lChunks_length]
theorem chunkLengthsOK : (chunks.dropLast.all fun c => c.length==256)=true :=
  mapRows_ok lChunks 0 lChunks_ok

theorem nativeRowLengths : ((List.range 64).all fun rank =>
    decide ((lChunks.getD (691+rank) []).length=256))=true := by
  decide +kernel

theorem nativeRow_length (rank : Nat) (hr : rank<64) :
    (lChunks.getD (691+rank) []).length=256 :=
  of_decide_eq_true (List.all_eq_true.mp nativeRowLengths rank (List.mem_range.mpr hr))

theorem mapRows_drop (rows : List (List (BitVec 32))) (start k : Nat) :
    (mapRows start rows).drop k=mapRows (start+k) (rows.drop k) := by
  induction k generalizing rows start with
  | zero => simp
  | succ k ih =>
    cases rows with
    | nil => simp [mapRows]
    | cons row rows => simpa [mapRows,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih rows (start+1)

theorem macro_prefix (rank : Nat) (hr : rank<64) :
    words rank <+: code.drop (armPC rank) := by
  let k:=691+rank
  have hk : k<chunks.length := by rw [chunks_length];dsimp [k];omega
  have ho : k<lChunks.length := by rw [lChunks_length];dsimp [k];omega
  have hp : armPC rank=256*k+40 := by dsimp [armPC,k];omega
  have hd:=drop_chunks' chunks k chunkLengthsOK hk
  have hrow : (lChunks.getD k []).length=256 := nativeRow_length rank hr
  have hg : lChunks[k]=lChunks.getD k [] := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ho]
  have hpat : (patchRow rank (lChunks[k])).length=256 := by
    rw [hg];exact patchRow_length rank hr _ hrow
  unfold code
  rw [hp,←List.drop_drop,hd,chunks,mapRows_drop]
  simp only [Nat.zero_add]
  rw [List.drop_eq_getElem_cons ho,mapRows,
    if_pos (show 691≤k ∧ k<755 by dsimp [k];omega),
    show k-691=rank by dsimp [k];omega,List.flatten_cons,List.drop_append,hpat]
  simp only [Nat.reduceSub,List.drop_zero]
  exact (patchRow_prefix rank (lChunks[k]) (by rw [hg,hrow];decide)).trans
    (List.prefix_append _ _)

theorem macro_codeAt (rank : Nat) (hr : rank<64) :
    CodeAt image (pcOf (armPC rank)) (words rank) := by
  have hlen:=List.all_eq_true.mp macro_length_check rank (List.mem_range.mpr hr)
  have he:=of_decide_eq_true hlen
  have hmax (d : Nat) : pieceLen d≤10 := by unfold pieceLen;split_ifs <;> omega
  have hw : (words rank).length≤42 := by
    rw [he];have h0:=hmax (digit rank 0);have h1:=hmax (digit rank 1);have h2:=hmax (digit rank 2);omega
  have hp : (pcOf (armPC rank)).toNat=0x1000+4*(armPC rank) := by
    simp only [pcOf,BitVec.toNat_ofNat];unfold armPC;omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [hp];omega
  · rw [hp];omega
  · rw [hp];unfold armPC;omega
  · rw [hp,show (0x1000+4*(armPC rank)-0x1000)/4=armPC rank by omega]
    exact macro_prefix rank hr

#print axioms patchRow_length
#print axioms patchRow_prefix
#print axioms chunks_length
#print axioms chunkLengthsOK
#print axioms nativeRowLengths
#print axioms macro_codeAt
end SigGolfCandidate.T3M.Nonbinary.InlineTail
