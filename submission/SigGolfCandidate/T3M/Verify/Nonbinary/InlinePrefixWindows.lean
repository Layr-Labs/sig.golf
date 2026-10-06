import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixCode
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

/- Literal fetch obligations for the first seventeen triples. The old terminal
   triple is deliberately excluded: its entry is now the actual inline macro.
   This interface contains CodeAt/fetch facts, never completed executions. -/
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace InlineTail
theorem base51_check : ((List.range 17).all fun q=>
    ((List.range 5).all fun b=>((List.range 5).all fun d=>
      decide (base q b d<96000))))=true := by decide +kernel

theorem base51_lt (q b d : Nat) (hq : q<17) (hb : b<5) (hd : d<5) :
    base q b d<96000 := by
  have h:=List.all_eq_true.mp base51_check q (List.mem_range.mpr hq)
  have h:=List.all_eq_true.mp h b (List.mem_range.mpr hb)
  exact of_decide_eq_true (List.all_eq_true.mp h d (List.mem_range.mpr hd))

theorem first51_row_check : ((List.range 128).all fun rank=>
    decide ((lChunks.getD (690+rank) []).length=256))=true := by decide +kernel

theorem first51_row_length (rank : Nat) (hr : rank<128) :
    (lChunks.getD (690+rank) []).length=256 :=
  of_decide_eq_true (List.all_eq_true.mp first51_row_check rank (List.mem_range.mpr hr))
theorem prefix_partLen_le (q d : Nat) : partLen q d ≤ 14 := by
  have hm : 3 ≤ mx q ∧ mx q ≤ 4 := by unfold mx;split <;> omega
  unfold partLen
  split_ifs <;> omega
end InlineTail

namespace NCtx

theorem prefix_digit_group (c : NCtx) (hd : ∀ j,j<54 → c.dig j ≤ topMax j)
    (q k : Nat) (hq : q<18) (hk : k<3) : c.dig (3*q+k) ≤ mx q := by
  have h:=hd (3*q+k) (by omega)
  simpa only [topMax,show (3*q+k)/3=q by omega] using h

theorem prefix_rank_le (c : NCtx) (hd : ∀ j,j<54 → c.dig j ≤ topMax j)
    (q : Nat) (hq : q<18) : c.kOf q<(mx q+1)^3 := by
  have h0:=c.prefix_digit_group hd q 0 hq (by decide)
  have h1:=c.prefix_digit_group hd q 1 hq (by decide)
  have h2:=c.prefix_digit_group hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> omega
structure PrefixWindows (c : NCtx) : Prop where
  start : ∀ i, i<51 → ∀ f,f ≤ 8 → CodeAt InlineTail.image (pcOf (c.startPc i)) ((lcode (c.startPc i)).take f)
  rung : ∀ i, i<51 → ∀ m,m ≤ last i → ∀ f,f ≤ 3 → 
    CodeAt InlineTail.image (pcOf (c.rungPc i m)) ((lcode (c.rungPc i m)).take f)
  tail : ∀ i, i<51 → ∀ m,m ≤ last i → ∀ f,f ≤ 2 → 
    CodeAt InlineTail.image (pcOf (c.rungPc i m+1)) ((lcode (c.rungPc i m+1)).take f)
  prehash : ∀ i, i<51 → ∀ m,m ≤ last i → ∀ s : MachineState,
    s.pc=pcOf (c.rungPc i m+(if m=last i then 2 else 1)) → 
    fetch InlineTail.image s=fetch Images.verifyImage s
  dispatch : ∀ i, i<51 → ∀ f,f ≤ 5 → 
    CodeAt InlineTail.image (pcOf (c.qX i)) ((lcode (c.qX i)).take f)

theorem prefix_body_bound (c : NCtx) (hds : ∀ j,j<54 → c.dig j ≤ topMax j) (i : Nat) (hi : i<51) :
    c.qb i<96000 ∧ c.qB i<96010 ∧ c.qC i<96030 ∧ c.qX i<96050 := by
  have hb:=c.prefix_digit_group hds (i/3) 1 (by omega) (by decide)
  have hd:=c.prefix_digit_group hds (i/3) 2 (by omega) (by decide)
  have hq : i/3<17 := by omega
  rw [mx,if_pos hq] at hb hd
  have hx:=InlineTail.base51_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2)) hq (by omega) (by omega)
  have h1:=InlineTail.prefix_partLen_le (i/3) (c.dig (3*(i/3)+1))
  have h2:=InlineTail.prefix_partLen_le (i/3) (c.dig (3*(i/3)+2))
  simp only [qb,qB,qC,qX,pcB,pcC,pcX,mx,if_pos hq]
  omega

theorem prefix_rung_bound (c : NCtx) (hds : ∀ j,j<54 → c.dig j ≤ topMax j) (i m : Nat)
    (hi : i<51) (hm : m ≤ last i) : c.rungPc i m<96100 := by
  have hb:=c.prefix_body_bound hds i hi
  have hl:=last_bounds i
  unfold rungPc startPc
  split_ifs <;> omega

theorem prefix_windows (c : NCtx) (hds : ∀ j,j<54 → c.dig j ≤ topMax j) : c.PrefixWindows := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi f hf
    by_cases ht : i%3=0
    · have hq : i/3<17 := by omega
      have hk:=c.prefix_rank_le hds (i/3) (by omega)
      have hk125 : c.kOf (i/3)<125 := by simpa [mx,if_pos hq] using hk
      have hk' : c.kOf (i/3)<128 := by omega
      rw [startPc,if_pos ht]
      exact InlineTail.first51_entry_codeAt (i/3) (c.kOf (i/3)) f hq hk' (by omega)
        (InlineTail.first51_row_length _ hk')
    · have hb:=c.prefix_body_bound hds i hi
      apply InlineTail.prefix_codeAt
      unfold startPc
      rw [if_neg ht]
      split <;> omega
  · intro i hi m hm f hf
    exact InlineTail.prefix_codeAt _ _ (by have h:=c.prefix_rung_bound hds i m hi hm;omega)
  · intro i hi m hm f hf
    exact InlineTail.prefix_codeAt _ _ (by have h:=c.prefix_rung_bound hds i m hi hm;omega)
  · intro i hi m hm s hp
    exact InlineTail.prefix_fetch_equal _ (by have h:=c.prefix_rung_bound hds i m hi hm;split <;> omega) s hp
  · intro i hi f hf
    exact InlineTail.prefix_codeAt _ _ (by have h:=c.prefix_body_bound hds i hi;omega)

#print axioms prefix_windows
end NCtx
end SigGolfCandidate.T3M.Nonbinary
