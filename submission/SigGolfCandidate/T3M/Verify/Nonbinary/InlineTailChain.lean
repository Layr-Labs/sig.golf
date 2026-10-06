import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailRung
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailJudg

/- Finite native HASH semantics on the new 64-arm image. The source program
   remains the actual NCtx.rest chain. Every arbitrary HASH answer follows
   the new physical header/rung/endpoint frame, rather than an outcome callback. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def preCost (_ordinal m : Nat) : Nat := 8+9*(2-m)+(if m<2 then 1 else 0)

theorem finite_hash_chain (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank ordinal : Nat) (hr : rank<64) (ho : ordinal<3)
    (hdig : c.dig (index ordinal)=digit rank ordinal)
    (acc : List Digest) (K : List Digest→OracleComp Legacy.HashSpec Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ v t,End c s0 rank ordinal (acc++[v]) t→
      Judg.GoodQ image t N C Q A (K (acc++[v]))) :
    ∀ k m,m+k=2→c.dig (index ordinal) ≤ m→∀ v s,Pre c s0 rank ordinal m acc v s→
      Judg.GoodQ image s (N+3*(3-m)+5) (C+preCost ordinal m) Q (A+preCost ordinal m)
        (Judg.ccM (c.rest (index ordinal) m v) (fun v=>K (acc++[v]))) := by
  let i:=index ordinal
  have hi : i<54 := by dsimp [i,index];omega
  have hiLast : NCtx.last i=2 := last_index ordinal ho
  have hmax:=NCtx.topMax_bounds i
  have hlastEq : 3=NCtx.topMax i := by unfold NCtx.last at hiLast;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=2 := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := prehash_stage c hc s0 hk h0 rank ordinal 2 hr ho (le_refl _) hdig hd acc v s hs
      rw [NCtx.rest_succ c i 2 (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Judg.GoodQ image (writeHash s a) N C Q A
          (Judg.ccM (c.rest i (2+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        change Judg.GoodQ image (writeHash s a) N C Q A
          (Judg.ccM (c.rest i 3 (a.extractLsb' 0 128)) (fun v=>K (acc++[v])))
        rw [hlastEq,NCtx.rest_max,Judg.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := Judg.GoodQ.shortHash_bind (f:=c.rest i (2+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [NCtx.chainInputP_pad];exact hin) H
      rw [NCtx.chainInputP_pad,NCtx.chainInputP_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := prehash_stage c hc s0 hk h0 rank ordinal m hr ho (by omega) hdig hd acc v s hs
      rw [NCtx.rest_succ c i m (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Judg.GoodQ image (writeHash s a) (N+3*(3-(m+1))+5+2)
          (C+preCost ordinal (m+1)+(if m+1=2 then 2 else 1)) Q
          (A+preCost ordinal (m+1)+(if m+1=2 then 2 else 1))
          (Judg.ccM (c.rest i (m+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        obtain ⟨u,hu,hp⟩:=rung_stage c hc s0 hk rank ordinal (m+1) hr ho (by omega)
          (by rw [←hdig];omega) acc _ _ ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact Judg.GoodQ.steps' hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := Judg.GoodQ.shortHash_bind (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [NCtx.chainInputP_pad];exact hin) H
      rw [NCtx.chainInputP_pad,NCtx.chainInputP_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=2
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=2
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
def nativeChainCost (ordinal d : Nat) : Nat :=
  if d=3 then 4 else 4+preCost ordinal d

theorem one_chain (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank ordinal : Nat) (hr : rank<64) (ho : ordinal<3)
    (hdig : c.dig (index ordinal)=digit rank ordinal)
    (acc : List Digest) (K : List Digest→OracleComp Legacy.HashSpec Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ v t,End c s0 rank ordinal (acc++[v]) t→
      Judg.GoodQ image t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : Input c s0 rank ordinal acc s) :
    Judg.GoodQ image s (N+40) (C+nativeChainCost ordinal (c.dig (index ordinal))) Q
      (A+nativeChainCost ordinal (c.dig (index ordinal)))
      (Judg.ccM (chainP 0 c.tree c.leaf (index ordinal) (c.dig (index ordinal))
        (NCtx.topMax (index ordinal)-c.dig (index ordinal))
        (c.pad0 (index ordinal)) (c.pad1 (index ordinal))
        (c.padHeader (index ordinal)) (c.val (index ordinal)))
        (fun v=>K (acc++[v]))) := by
  let i:=index ordinal
  have hi : i<54 := by dsimp [i,index];omega
  have hmax:=NCtx.topMax_bounds i
  have hlast : NCtx.last i=2 := last_index ordinal ho
  have hcap : NCtx.topMax i=3 := by unfold NCtx.last at hlast;omega
  have hbound : c.dig i ≤ 3 := by rw [hdig];have h:=digit_lt rank ordinal;omega
  by_cases hm : c.dig i=3
  · rw [hcap,hm,Nat.sub_self]
    have hp : chainP 0 c.tree c.leaf i 3 0 (c.pad0 i) (c.pad1 i)
        (c.padHeader i) (c.val i)=pure (c.val i) := rfl
    rw [hp,Judg.ccM_pure]
    obtain ⟨t,hst,ht⟩:=copy_stage c hc s0 hk h0 rank ordinal hr ho
      (by rw [←hdig];exact hm) acc s hs
    exact Judg.GoodQ.steps' hst (hK _ _ ht) (by omega)
      (by simp [nativeChainCost]) (fun hq=>⟨hq,by simp [nativeChainCost]⟩)
  · have hd : c.dig i<3 := by omega
    have hcost : nativeChainCost ordinal (c.dig (index ordinal))=4+preCost ordinal (c.dig i) := by
      change nativeChainCost ordinal (c.dig i)=4+preCost ordinal (c.dig i)
      simp [nativeChainCost,hm]
    rw [NCtx.chainP_rest]
    have H:=finite_hash_chain c hc s0 hk h0 rank ordinal hr ho hdig acc K N C A Q hK
      (2-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩:=head_stage c hc s0 hk h0 rank ordinal hr ho hdig hd acc s hs
    exact Judg.GoodQ.steps' hst (H _ _ ht) (by omega)
      (by rw [hcost];omega)
      (fun hq=>⟨hq,by rw [hcost];omega⟩)

theorem next_input (c : NCtx) (s0 : MachineState) (rank ordinal : Nat)
    (ends : List Digest) (s : MachineState)
    (hs : End c s0 rank ordinal ends s) :
    Input c s0 rank (ordinal+1) ends s := by
  simpa [End,Input,index,Nat.add_assoc] using hs

#print axioms finite_hash_chain
#print axioms one_chain
end SigGolfCandidate.T3M.Nonbinary.InlineTail
