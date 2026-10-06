import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailWindows
import SigGolfCandidate.Rv.SymRunPrefix

/- Actual finite fetch windows before all modified tail-JT chunks. Generic
   prefix execution is the exact attributed Root Rv.SymRunPrefix theorem.
   No old whole-image CodeAt or desired machine result is assumed. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem mapRows_append (a b : List (List (BitVec 32))) (start : Nat) :
    mapRows start (a++b)=mapRows start a++mapRows (start+a.length) b := by
  induction a generalizing start with
  | nil => simp [mapRows]
  | cons row a ih => simp [mapRows,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem mapRows_before (rows : List (List (BitVec 32))) (start : Nat)
    (h : start+rows.length ≤ 691) : mapRows start rows=rows := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hh : ¬(691 ≤ start ∧ start<755) := by simp only [List.length_cons] at h;omega
    rw [mapRows,if_neg hh,ih (start+1) (by simp only [List.length_cons] at h;omega)]

theorem flatten_take_length : ∀ (rows : List (List (BitVec 32))) (k : Nat),
    (rows.dropLast.all fun row=>row.length==256)=true → k<rows.length →
      (rows.take k).flatten.length=256*k := by
  intro rows k
  induction k generalizing rows with
  | zero => simp
  | succ k ih =>
    intro hall hk
    cases rows with
    | nil => simp at hk
    | cons row rows =>
      cases rows with
      | nil => simp at hk
      | cons row' rows =>
        simp only [List.dropLast_cons_cons,List.all_cons,Bool.and_eq_true,beq_iff_eq] at hall
        have hh:=ih (row'::rows) hall.2 (by simp at hk ⊢;omega)
        simp only [List.take_succ_cons,List.flatten_cons,List.length_append,hall.1,hh]
        omega

def codePrefix : List (BitVec 32) := (lChunks.take 691).flatten

theorem codePrefix_length : codePrefix.length=176896 := by
  exact flatten_take_length lChunks 691 lChunks_ok (by rw [lChunks_length];decide)

theorem new_code_prefix : code=codePrefix++(mapRows 691 (lChunks.drop 691)).flatten := by
  have ht : (lChunks.take 691).length=691 := by simp [lChunks_length]
  have hm : mapRows 0 (lChunks.take 691)=lChunks.take 691 :=
    mapRows_before _ 0 (by rw [ht])
  unfold code chunks
  conv_lhs => rw [←List.take_append_drop 691 lChunks]
  rw [mapRows_append,hm,ht]
  simp only [List.flatten_append,Nat.zero_add,codePrefix]

theorem old_code_prefix : Images.verifyCode=codePrefix++(lChunks.drop 691).flatten := by
  rw [lChunks_flatten]
  conv_lhs => rw [←List.take_append_drop 691 lChunks]
  simp only [List.flatten_append,codePrefix]

theorem prefix_window_equal (p n : Nat) (h : p+n ≤ 176896) :
    (code.drop p).take n=(Images.verifyCode.drop p).take n := by
  rw [List.take_drop,List.take_drop,new_code_prefix,old_code_prefix]
  have hh : p+n ≤ codePrefix.length := by rw [codePrefix_length];exact h
  rw [List.take_append_of_le_length hh,List.take_append_of_le_length hh]

theorem prefix_codeAt (p n : Nat) (h : p+n ≤ 176896) :
    CodeAt image (pcOf p) ((lcode p).take n) := by
  have hp : (pcOf p).toNat=0x1000+4*p := by simp only [pcOf,BitVec.toNat_ofNat];omega
  have hl : ((lcode p).take n).length ≤ n := List.length_take_le ..
  refine ⟨by rw [hp];omega,by rw [hp];omega,by rw [hp];omega,?_⟩
  rw [hp,show (0x1000+4*p-0x1000)/4=p by omega]
  change (lcode p).take n <+: code.drop p
  rw [lcode_eq p (by omega),←prefix_window_equal p n h]
  exact List.take_prefix _ _

theorem prefix_piece_steps {p fuel : Nat} {r : Result}
    (hr : vrun p fuel=some r) (hb : p+fuel ≤ 176896)
    (s : MachineState) (hp : s.pc=pcOf p) (ho : r.obligs s) :
    Steps image s r.steps r.cycles (r.toState s) :=
  symRun_prefix_sound hr (le_refl _) (prefix_codeAt p fuel hb) s hp ho

theorem prefix_piece_ecall {p fuel : Nat} {r : Result}
    (hr : vrun p fuel=some r) (hb : p+fuel ≤ 176896)
    (s : MachineState) (ho : r.obligs s) (hs : r.stop=.ecall) :
    fetch image (r.toState s)=some (.base .ECALL) :=
  symRun_prefix_ecall hr (le_refl _) (prefix_codeAt p fuel hb) s ho hs

-- JT entry windows are in the unchanged suffix of their unaligned chunk.
theorem row_lcode_window (k off n : Nat) (hk : k<985) (ho : off<256)
    (hlen : (lChunks.getD k []).length=256) (hn : off+n ≤ 256) :
    (lcode (256*k+off)).take n=((lChunks.getD k []).drop off).take n := by
  have hlk : k<lChunks.length := by rw [lChunks_length];exact hk
  have he : lChunks.getD k []=lChunks[k] := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlk]
  unfold lcode
  rw [show (256*k+off)/256=k by omega,show (256*k+off)%256=off by omega,
    List.drop_eq_getElem_cons hlk,List.flatten_cons,List.drop_append,←he,hlen]
  simp only [show off-256=0 by omega,List.drop_zero]
  rw [List.take_append_of_le_length (by simp only [List.length_drop,hlen];omega)]

theorem jt_prefix_codeAt (k off n : Nat) (hk : k<985) (ho : off<256)
    (hlen : (lChunks.getD k []).length=256) (hn : off+n ≤ 256) (hs : 104 ≤ off) :
    CodeAt image (pcOf (256*k+off)) ((lcode (256*k+off)).take n) := by
  apply unchanged_row_codeAt k off hk (by omega) hlen (Or.inr (Or.inr hs))
    ((lcode (256*k+off)).take n) (by have hh:=List.length_take_le n (lcode (256*k+off));omega)
  rw [row_lcode_window k off n hk ho hlen hn]
  exact List.take_prefix _ _

theorem first51_entry_codeAt (q rank n : Nat) (hq : q<17) (hr : rank<128) (hn : n ≤ 10)
    (hlen : (lChunks.getD (690+rank) []).length=256) :
    CodeAt image (pcOf (entW q rank)) ((lcode (entW q rank)).take n) := by
  have he:=first51_entry_geometry q rank hq
  rw [he.1]
  apply jt_prefix_codeAt (690+rank) (104+8*q) n (by omega) (by omega) hlen (by omega) (by omega)

-- Logical fetch equality is derived from the same actual one-word windows.
-- It transports pure NCtx.PreHash data invariants; machine execution remains
-- the new-image symRun_prefix_sound result above.
theorem prefix_fetch_equal (p : Nat) (h : p+1 ≤ 176896) (s : MachineState)
    (hp : s.pc=pcOf p) : fetch image s=fetch Images.verifyImage s := by
  have he:=congrArg (fun ws : List (BitVec 32)=>ws[0]?) (prefix_window_equal p 1 h)
  simp only [List.getElem?_take,List.getElem?_drop,Nat.add_zero] at he
  simp only [show (0<1 : Prop) from by decide,if_true] at he
  have hn : (pcOf p).toNat=0x1000+4*p := by simp only [pcOf,BitVec.toNat_ofNat];omega
  unfold Riscv.fetch
  rw [hp,hn]
  have hz : (decide (0x1000+4*p<0x1000) || (0x1000+4*p)%4!=0)=false := by
    simp
  simp only [hz,Bool.false_eq_true,if_false]
  rw [show (0x1000+4*p-0x1000)/4=p by omega]
  change Option.bind (code[p]?) decodeInstruction =
    Option.bind (Images.verifyCode[p]?) decodeInstruction
  rw [he]

#print axioms prefix_codeAt
#print axioms prefix_piece_steps
#print axioms prefix_piece_ecall
end SigGolfCandidate.T3M.Nonbinary.InlineTail
