import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailImage

/- True unchanged instruction windows of the new image. JT rows are unaligned:
   only chunk offsets40..103 are replaced, so first51 entry windows at104+8*q
   remain intact. Leaf/Merkle banks below chunk691 are wholly untouched. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem words_length_le (rank : Nat) (hr : rank<64) : (words rank).length ≤ 42 := by
  have he:=of_decide_eq_true (List.all_eq_true.mp macro_length_check rank (List.mem_range.mpr hr))
  have hl (d : Nat) : pieceLen d ≤ 10 := by unfold pieceLen;split_ifs <;> omega
  rw [he]
  have h0:=hl (digit rank 0)
  have h1:=hl (digit rank 1)
  have h2:=hl (digit rank 2)
  omega

theorem mapRows_getD (rows : List (List (BitVec 32))) (start k : Nat) (hk : k<rows.length) :
    (mapRows start rows).getD k []=
      if 691 ≤ start+k ∧ start+k<755 then patchRow (start+k-691) (rows.getD k [])
      else rows.getD k [] := by
  induction rows generalizing start k with
  | nil => simp at hk
  | cons row rows ih =>
    cases k with
    | zero => simp [mapRows]
    | succ k =>
      have hh:=ih (start+1) k (by simp at hk;omega)
      simpa [mapRows,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem patchRow_suffix (rank : Nat) (hr : rank<64) (row : List (BitVec 32))
    (hlen : row.length=256) : (patchRow rank row).drop 104=row.drop 104 := by
  have hw:=words_length_le rank hr
  unfold patchRow
  have hl : (row.take 40 ++ words rank ++ List.replicate (64-(words rank).length) 19).length=104 := by
    simp only [List.length_append,List.length_take,List.length_replicate,hlen]
    omega
  have hd : (row.take 40 ++ words rank ++ List.replicate (64-(words rank).length) 19).drop 104=[] := by
    rw [←hl]
    exact List.drop_length
  rw [List.drop_append,hd,hl]
  simp

theorem unchanged_row_suffix (k off : Nat) (hk : k<lChunks.length)
    (hlen : (lChunks.getD k []).length=256)
    (safe : k<691 ∨ 755 ≤ k ∨ 104 ≤ off) :
    (chunks.getD k []).drop off=(lChunks.getD k []).drop off := by
  rw [chunks,mapRows_getD lChunks 0 k hk]
  simp only [Nat.zero_add]
  split_ifs with hpat
  · have hoff : 104 ≤ off := by rcases safe with h|h|h <;> omega
    have he:=patchRow_suffix (k-691) (by omega) (lChunks.getD k []) hlen
    rw [show off=104+(off-104) by omega,←List.drop_drop,he,List.drop_drop]
  · rfl

theorem row_codeAt (k off : Nat) (hk : k<985) (ho : off ≤ 256)
    (ws : List (BitVec 32)) (hw : ws.length ≤ 256)
    (hp : ws <+: (chunks.getD k []).drop off) :
    CodeAt image (pcOf (256*k+off)) ws := by
  have hc : k<chunks.length := by rw [chunks_length];exact hk
  have hg : chunks.getD k [] <+: (chunks.drop k).flatten := by
    rw [List.drop_eq_getElem_cons hc]
    simp only [List.flatten_cons]
    have hget : chunks.getD k []=chunks[k] := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hc]
    rw [hget]
    exact List.prefix_append _ _
  have hd:=drop_chunks' chunks k chunkLengthsOK hc
  have hpc : (pcOf (256*k+off)).toNat=0x1000+4*(256*k+off) := by
    simp only [pcOf,BitVec.toNat_ofNat];omega
  refine ⟨by rw [hpc];omega,by rw [hpc];omega,by rw [hpc];omega,?_⟩
  rw [hpc,show (0x1000+4*(256*k+off)-0x1000)/4=256*k+off by omega]
  change ws <+: code.drop (256*k+off)
  rw [code,←List.drop_drop,hd]
  exact hp.trans (hg.drop off)

theorem unchanged_row_codeAt (k off : Nat) (hk : k<985) (ho : off ≤ 256)
    (hlen : (lChunks.getD k []).length=256)
    (safe : k<691 ∨ 755 ≤ k ∨ 104 ≤ off)
    (ws : List (BitVec 32)) (hw : ws.length ≤ 256)
    (hp : ws <+: (lChunks.getD k []).drop off) :
    CodeAt image (pcOf (256*k+off)) ws := by
  apply row_codeAt k off hk ho ws hw
  rw [unchanged_row_suffix k off (by rw [lChunks_length];exact hk) hlen safe]
  exact hp

-- These are the exact relative positions of every unchanged first51 JT entry.
theorem first51_entry_geometry (q rank : Nat) (hq : q<17) :
    entW q rank=256*(690+rank)+(104+8*q) ∧ 104 ≤ 104+8*q ∧ 104+8*q+4 ≤ 256 := by
  simp only [entW,if_pos hq]
  constructor
  · omega
  · omega

#print axioms unchanged_row_suffix
#print axioms unchanged_row_codeAt
#print axioms first51_entry_geometry
end SigGolfCandidate.T3M.Nonbinary.InlineTail
