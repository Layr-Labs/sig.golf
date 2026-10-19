import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_PackedLeaf_C

set_option Elab.async false


namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {im : Image} (hc : SharedLowCode.Code im)
include hc
theorem path_loop (t0 : MachineState) (H hi : Nat) (hH : H ≤ 7) (hhi : hi < 2 ^ (H + 1)) :
    ∀ (n j : Nat), j + n = H → ∀ (t : MachineState) (ep : Nat), t.pc = pcOf 1202 →
      t.getReg .x13 = BitVec.ofNat 64 j → t.getReg .x15 = BitVec.ofNat 64 H →
      t.getReg .x19 = BitVec.ofNat 64 hi → t.getReg .x2 = BitVec.ofNat 64 LOW →
      t.getReg .x24 = BitVec.ofNat 64 ep → ep % 8 = 0 → ep + 16 * n ≤ LOW →
      (∀ A, LOW ≤ A → A < LOW + 4096 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
      ∃ u k, Steps im t k k u ∧ k ≤ 12 * n + 1 ∧ u.pc = pcOf 1214 ∧
        (∀ i < n, DigAt u (ep + 16 * i) (memDig t0 (LOW + 16 * (hi / 2 ^ (j + i) ^^^ 1)))) ∧
        RegsExcept t u [.x6, .x7, .x13, .x24, .x28] ∧ Frame t u (fun A => ep ≤ A ∧ A < ep + 16 * n)
  | 0, j, hjn, t, ep, hpc, h13, h15, _, _, _, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk1202_spec hc t hpc j H (by omega) (by omega) h13 h15
    rw [if_neg (by omega)] at upc
    exact ⟨u, 1, st, by omega, upc, fun i hi => absurd hi (by omega), ur.mono (by simp),
      uf.mono (fun _ _ h => h.elim)⟩
  | n + 1, j, hjn, t, ep, hpc, h13, h15, h19, h2, h24, hep8, hepl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk1202_spec hc t hpc j H (by omega) (by omega) h13 h15
    rw [if_pos (by omega)] at t1pc
    have hhi' : hi < 8192 := lt_of_lt_of_le hhi (by
      calc 2 ^ (H + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 8192 := by norm_num)
    obtain ⟨t2, st2, t2pc, t2x13, t2x24, m0, m8, t2r, t2f⟩ := blk1203_spec hc t1 t1pc j hi LOW ep (by omega)
      hhi' (by shared_tree_sgo) (by shared_tree_sgo) (by shared_tree_sgo) hep8 (by rw [t1r.get (by simp)]; exact h13)
      (by rw [t1r.get (by simp)]; exact h19) (by rw [t1r.get (by simp)]; exact h2)
      (by rw [t1r.get (by simp)]; exact h24)
    have hx : hi / 2 ^ j ^^^ 1 < 8192 :=
      Nat.xor_lt_two_pow (n := 13) (lt_of_le_of_lt (Nat.div_le_self _ _) hhi') (by norm_num)
    have hx' : hi / 2 ^ j ^^^ 1 < 256 := by
      have h1 : hi / 2 ^ j < 2 ^ 8 := lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hhi
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact Nat.xor_lt_two_pow h1 (by norm_num)
    have f12 : Frame t t2 (fun A => A = ep ∨ A = ep + 8) := (t1f.trans t2f).mono (fun _ _ h => by
      rcases h with h | h; exact h.elim; exact h)
    obtain ⟨u, k, st, hk, upc, uem, ur, uf⟩ := path_loop t0 H hi hH hhi n (j + 1) (by omega) t2 (ep + 16) t2pc
      t2x13 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h15)
      (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19) (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2)
      t2x24 (by omega) (by omega) (fun A h1 h2' => (f12.get (by shared_tree_sgo) (by shared_tree_sgo)).trans (hheap A h1 h2'))
    refine ⟨u, 1 + (11 + k), st1.trans (st2.trans st), by omega, upc, fun i hi' => ?_,
      ((t1r.trans t2r).trans ur).mono (by simp), (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩
    rcases i with _ | i
    · simp only [Nat.mul_zero, Nat.add_zero]
      refine ⟨?_, ?_⟩
      · rw [uf.get (by shared_tree_sgo) (by omega), m0, t1f.get (by shared_tree_sgo) (fun h => h), hheap _ (by shared_tree_sgo) (by shared_tree_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).1
      · rw [uf.get (by shared_tree_sgo) (by omega), m8, t1f.get (by shared_tree_sgo) (fun h => h), hheap _ (by shared_tree_sgo) (by shared_tree_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).2
    · have := uem i (by omega)
      rw [show ep + 16 + 16 * i = ep + 16 * (i + 1) by ring, show j + 1 + i = j + (i + 1) by ring] at this
      exact this

def AllW (lay : Layer) (tree sb : Nat) (A : Nat) : Prop :=
  BtW sb (height lay) A ∨ LevW (btLev lay tree) A ∨ (sb+16*43≤A ∧ A<sb+16*(43+height lay)) ∨
  A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56
structure Post (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel sb ret : Nat)
    (s : MachineState) (r : List (List Digest) × List (List Digest)) (u : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : u.pc=pcOf ret
  plen : r.2.length=43
  saved : ∀ i,i<43 → ∀ k,k≤7 → DigAt u (SharedPrefixes.buffer lay.val i k) ((r.2.getD i []).getD k 0)
  path : DigsAt u (sb+16*43) ((List.range (height lay)).map fun j => (r.1.getD j []).getD (sel/2^j ^^^ 1) 0)
  left : DigAt u ENC (topPair lay r.1).1
  right : DigAt u (ENC+48) (topPair lay r.1).2
  base : Base (cfFlag := cfFlag) sk cache u
  regs : RegsExcept s u btAllRegs
  frame : Frame s u (AllW lay tree sb)
  precise : Frame s u (TreeWrites lay)

theorem tail (hlevels : SharedTreeCode.Code im 1013) {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s s1 t : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1)
    (h4 : s1.getReg .x4 = pcOf ret) (hr0 : RegsExcept s s1 [.x4, .x13]) (hf0 : Frame s s1 (fun _ => False))
    {st : List Digest × List (List Digest) × List Digest} (ht : Inv s1 lay sb sel (2^height lay) st t) :
    TBSim im sk t 19000 (do
      let levels ← ClaudeWCT.WCT9.buildLevelsBelow 3 lay.val tree (height lay) st.1
      pure (levels, st.2.1)) (Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hH7 : height lay ≤ 7 := by rcases hH with h | h <;> omega
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  have hsb8 := hs.hsb8
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, -, t1r, t1f⟩ := blk1175_spec hc t ht.pc (2 ^ height lay) (height lay) (by omega)
    (by omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x21, t2r, t2f⟩ := blk1193_spec hc t1 t1pc lay.val tree
    (by have : lay.val ≠ 0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hs.htree
    (by rw [t1r.get (by simp), g _ (by decide), hs.x8]) (by rw [t1r.get (by simp), g _ (by decide), hs.x9])
  have g2 : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x6, .x21] → t2.getReg r = s1.getReg r := fun r hr =>
    ((ht.regs.trans t1r).trans t2r).get hr
  have f2 : Frame s1 t2 (BtW sb (height lay)) := (ht.frame.trans (t1f.trans t2f)).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact h.elim
    · exact h.elim)
  have hlp : LevPre t2 (btLev lay tree) st.1 :=
    { x1 := t2x1
      x2 := by rw [g2 _ (by decide), hs.x2]; rfl
      x5 := by rw [g2 _ (by decide), hs.base.x5]
      x9 := by rw [g2 _ (by decide), hs.x9]; rfl
      x15 := by rw [g2 _ (by decide), hs.x15]; rfl
      x21 := t2x21
      tag3 := rfl
      hlay := lay.isLt
      htree := hs.htree
      hh1 := by show 1 ≤ height lay; omega
      hh := by show height lay ≤ 12; omega
      ha8 := by show LOW % 8 = 0; decide
      ha := by
        show LOW + 16 * 2 ^ (height lay + 1) ≤ 2 ^ 24
        rcases hH with h | h <;> rw [h] <;> norm_num
      has := Or.inl (by show NOUT + 32 ≤ LOW; decide)
      z32 := by
        rw [f2.get (by shared_tree_sgo) (by unfold BtW; shared_tree_sgo)]
        exact hs.base.zero _ (by shared_tree_sgo) (by unfold NeverW; simp)
      z40 := by
        rw [f2.get (by shared_tree_sgo) (by unfold BtW; shared_tree_sgo)]
        exact hs.base.zero _ (by shared_tree_sgo) (by unfold NeverW; simp)
      hlen := ht.len
      hleaves := by
        show DigsAt t2 (LOW + 16 * 2 ^ height lay) st.1
        exact ht.roots.frame (t1f.trans t2f) (by rw [ht.len]; shared_tree_sgo) (fun _ _ _ h => by
          rcases h with h | h <;> exact h) }
  have hlev := SharedTree.buildLevelsBelow_tsim hlevels sk hlp
    (by show 1 ≤ lay.val; exact Nat.pos_of_ne_zero (fun h => hlay (Fin.ext h)))
    (by show 2 ≤ height lay; rcases hH with h | h <;> omega) t2pc
  obtain ⟨hlk, hlc⟩ := btLev_costs lay hlay tree
  change SharedTree.levKB (btLev lay tree)≤SharedTree.levCB (btLev lay tree) at hlk
  change SharedTree.levCB (btLev lay tree)≤6609 at hlc
  -- Stage 2 (C2): `WCT9.buildLevelsBelow` is `Seed.levelsBelowW` by definition (`lowerLevel` halves).
  rw [SigGolfCandidate.T3M.Sign.Seed.buildLevelsBelow_eq_levelsBelowW]
  refine TBSim.mono (TBSim.steps (st1.trans st2) (TBSim.bind (W₂ := 120) (TSim.toTBSim hlev hlk)
    (fun levels u hu => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨upc, uheap, ur, uf⟩ := hu
  have gu : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs → u.getReg r = s1.getReg r := fun r hr =>
    (((ht.regs.trans t1r).trans t2r).trans ur).get hr
  obtain ⟨v, stv, vpc, vx13, vx19, vx24, vr, vf⟩ := blk1196_spec hc u upc (height lay) sel sb 43 (by omega)
    (by omega) (by shared_tree_sgo) (by rw [gu _ (by decide), hs.x15]) (by rw [gu _ (by decide), hs.x14])
    (by rw [gu _ (by decide), hs.x16]) (by rw [gu _ (by decide), hs.x26])
  have gv : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] →
      v.getReg r = s1.getReg r := fun r hr => ((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).get hr
  obtain ⟨w, k, stw, hk, wpc, wem, wr, wf⟩ := path_loop hc u (height lay) (2 ^ height lay + sel) hH7
    (by rw [pow_succ]; omega) (height lay) 0 (by omega) v (sb + 16 * 43) vpc vx13
    (by rw [gv _ (by decide), hs.x15]) vx19 (by rw [gv _ (by decide), hs.x2]) vx24 (by omega) (by shared_tree_sgo)
    (fun A h1 h2 => vf.get (by shared_tree_sgo) (fun h => h))
  obtain ⟨x, stx, xpc, xm0, xm8, xm48, xm56, xr, xf⟩ := BCBlocks.blk1214_pair_spec hc w wpc LOW ret (by decide) (by decide) (by decide)
    (by rw [wr.get (by simp), gv _ (by decide), hs.x2])
    (by rw [wr.get (by simp), gv _ (by decide), h4])
  refine TBSim.mono (TBSim.pure_steps (stv.trans (stw.trans stx)) ?_) (by omega) (fun _ _ h => h)
  have fux : Frame u x (fun A => (sb + 16 * 43 ≤ A ∧ A < sb + 16 * 43 + 16 * height lay) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) :=
    ((vf.trans wf).trans xf).mono (fun A _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact Or.inl h
      · exact Or.inr h)
  have f1x : Frame s1 x (AllW lay tree sb) := (f2.trans (uf.trans fux)).mono (fun A _ h => by
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr h)))
  have hW : ∀ A, A < 2 ^ 64 → BaseA A → AllW lay tree sb A → A = CHAIN + 32 ∨ A = CHAIN + 40 := by
    intro A _ hb hw
    unfold BaseA NeverW Search.TOP_DATA at hb
    unfold AllW BtW LevW at hw
    simp only [btLev] at hw
    rcases hH with h | h <;> rw [h] at hw <;> shared_tree_sgo
  have hzx : Seed.Z32 x := by
    have fx := (t1f.trans t2f).trans (uf.trans fux)
    refine ht.z.frame fx ?_ ?_ <;>
    · intro h
      simp only [LevW, btLev] at h
      rcases hH with hh | hh <;> rw [hh] at h <;> shared_tree_sgo
  have r1x : RegsExcept s1 x (btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
      [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]) :=
    (((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).trans wr).trans xr
  obtain ⟨-, hlv⟩ := uheap
  refine ⟨xpc,(ht.saved hsel).1,?_,?_,?_,?_,Seed.Base.frame_z32 hs.base f1x r1x (by decide) hW hzx,?_,?_,?_⟩
  · intro i hi k hk
    have hb := SharedPrefixes.buffer_bounds (lay:=lay.val)
      (by have hz : lay.val≠0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hi (by omega : k<8)
    refine ((ht.saved hsel).2 i hi k hk).frame ((t1f.trans t2f).trans (uf.trans fux)) (by omega) ?_ ?_
    all_goals
      simp only [LevW,btLev]
      shared_tree_sgo
  ·
    intro i hi
    rw [List.length_map, List.length_range] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    have he := wem i hi
    rw [Nat.zero_add, heapH_sib hi] at he
    obtain ⟨hlen, hd⟩ := hlv i (by show i ≤ height lay - 1; omega)
    have hq : sel / 2 ^ i < 2 ^ (height lay - i) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i), ← pow_add, Nat.sub_add_cancel hi.le]; exact hsel
    have h2i : 2 ^ 1 ≤ 2 ^ (height lay - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkq : sel / 2 ^ i ^^^ 1 < 2 ^ (height lay - i) := Nat.xor_lt_two_pow hq (by omega)
    have hdi := hd _ (by rw [hlen]; exact hkq)
    simp only [btLev] at hdi
    rw [show LOW + 16 * (2 ^ (height lay - i) + (sel / 2 ^ i ^^^ 1)) =
      LOW + 16 * 2 ^ (height lay - i) + 16 * (sel / 2 ^ i ^^^ 1) by ring, memDig_eq hdi] at he
    exact he.frame xf (by shared_tree_sgo) (by shared_tree_sgo) (by shared_tree_sgo)
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by change height lay - 1 ≤ height lay - 1; omega)
    have he : height lay - (height lay - 1) = 1 := by rcases hH with h | h <;> omega
    have hd0 := hd 0 (by rw [hl0]; simp only [btLev, he]; norm_num)
    simp only [btLev, he, pow_one, Nat.mul_zero, Nat.add_zero] at hd0
    change DigAt x ENC ((levels.getD (height lay - 1) []).getD 0 0)
    refine ⟨?_, ?_⟩
    · rw [xm0, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd0.1
    · rw [xm8, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd0.2
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by change height lay - 1 ≤ height lay - 1; omega)
    have he : height lay - (height lay - 1) = 1 := by rcases hH with h | h <;> omega
    have hd1 := hd 1 (by rw [hl0]; simp only [btLev, he]; norm_num)
    simp only [btLev, he, pow_one, Nat.mul_one] at hd1
    change DigAt x (ENC + 48) ((levels.getD (height lay - 1) []).getD 1 0)
    refine ⟨?_, ?_⟩
    · rw [xm48, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd1.1
    · rw [xm56, wf.get (by shared_tree_sgo) (by shared_tree_sgo), vf.get (by shared_tree_sgo) (fun h => h)]; exact hd1.2
  · exact (hr0.trans r1x).mono (by decide)
  · exact (hf0.trans f1x).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  · exact (hf0.trans ((ht.precise.trans (t1f.trans t2f)).trans (uf.trans fux))).mono (by
      intro A hA h
      rcases h with h|((h|h|h)|h|h|h)
      · exact h.elim
      · exact h
      · exact h.elim
      · exact h.elim
      · left; unfold LevW btLev at h; shared_tree_sgo
      · left; shared_tree_sgo
      · left; shared_tree_sgo)

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def treeProgram (lay : Layer) (tree sel : Nat) : T3.M (List (List Digest) × List (List Digest)) := do
  let st ← (List.range (2^height lay)).foldlM (body lay tree sel) ([],[],[])
  let levels ← ClaudeWCT.WCT9.buildLevelsBelow 3 lay.val tree (height lay) st.1
  pure (levels,st.2.1)
variable {im : Image} (hc : SharedLowCode.Code im)
    (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
include hc hlevels hsub hcopy hchain hpref hseed hhook
theorem tree_tbsim {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s) (hpc : s.pc = pcOf 1173)
    (h1 : s.getReg .x1 = pcOf ret)
    (hselection : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val=BitVec.ofNat 64 sel) :
    TBSim im sk s btCost (treeProgram lay tree sel) (Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  obtain ⟨s1, st1, s1pc, s1x4, s1x13, s1r, s1f⟩ := blk1173_spec hc s hpc
  have g1 : ∀ r, r ∉ [.x4, .x13] → s1.getReg r = s.getReg r := fun r hr => s1r.get hr
  have hs1 : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1 :=
    { x2 := by rw [g1 _ (by decide), hs.x2]
      x8 := by rw [g1 _ (by decide), hs.x8]
      x9 := by rw [g1 _ (by decide), hs.x9]
      x14 := by rw [g1 _ (by decide), hs.x14]
      x15 := by rw [g1 _ (by decide), hs.x15]
      x16 := by rw [g1 _ (by decide), hs.x16]
      x26 := by rw [g1 _ (by decide), hs.x26]
      x27 := by rw [g1 _ (by decide), hs.x27]
      x31 := by rw [g1 _ (by decide), hs.x31]
      base := hs.base.frame s1f s1r (by decide) (fun _ _ _ h => h)
      hlay := hlay
      htree := hs.htree
      hsel := hsel
      hroute := hs.hroute
      hdb := hs.hdb
      digits := fun i hi => by rw [s1f.getByte (by shared_tree_sgo) (fun h => h)]; exact hs.digits i hi
      hsb := hsb
      hsb8 := hs.hsb8 }
  have h0 : Inv s1 lay sb sel 0 ([],[],[]) s1 :=
    ⟨s1pc,s1x13,RegsExcept.refl _ _,Frame.refl _ _,Frame.refl _ _,rfl,DigsAt.nil _ _,
      fun h => absurd h (by omega),fun h => absurd h (by decide),
      ⟨(s1f.get (by decide) (by simp)).trans (hs.base.zero _ (by decide) (by unfold NeverW; simp)),
        (s1f.get (by decide) (by simp)).trans (hs.base.zero _ (by decide) (by unfold NeverW; simp))⟩⟩
  have hselection1 : SharedPrefixes.selectionWord (s1.getMem 0x20550) lay.val=BitVec.ofNat 64 sel := by
    have idx : s1.getMem 0x20550=s.getMem 0x20550 := s1f.get (by decide) (by simp)
    rw [idx]; exact hselection
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) 0 (2 ^ height lay)
    (body lay tree sel) ([],[],[]) (Inv s1 lay sb sel)
    (lowLeafC + 18)
    (fun l hl st t ht => by simpa using body_step hc hsub hcopy hchain hpref hseed hhook hs1 hselection1 hl ht) h0
  have hcost : 2 + (2 ^ height lay * (lowLeafC + 18) + 19000) ≤ btCost := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals decide
  unfold treeProgram
  have heq : List.range' 0 (2 ^ height lay) = List.range (2 ^ height lay) := List.range_eq_range'.symm
  rw [heq] at hloop
  exact TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 19000) hloop
    (fun st t ht => tail hc hlevels hs1 (by rw [s1x4, h1]) s1r s1f ht))) hcost (fun _ _ h => h)
end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open OracleComp SigGolfCandidate.T3
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000

theorem body_eq (lay : Layer) (hlay : lay≠0) (tree sel : Nat)
    (st : List Digest × List (List Digest) × List Digest) (leaf : Nat) :
    body lay tree sel st leaf = (do
      let ((root,prefixes),carry) ← if leaf=sel then SigGolfCandidate.Research.SharedForest.buildLeafPrefixes lay tree leaf st.2.2
        else do
          let ((root,_),carry) ← ClaudeWCT.WCT9.buildLeafPF lay tree leaf [] st.2.2
          pure ((root,[]),carry)
      pure (st.1++[root],if leaf=sel then prefixes else st.2.1,carry)) := by
  by_cases h : leaf=sel
  · simp only [body,h,if_true]
  · simp only [body,h,if_false,bind_assoc,pure_bind]
    exact SharedLeafMemory.buildLeafPrefixes_forget lay hlay tree leaf st.2.2
      (fun root carry => pure (st.1++[root],st.2.1,carry))

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open OracleComp SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000

theorem treeProgram_eq (lay : Layer) (hlay : lay≠0) (tree sel : Nat) :
    (treeProgram lay tree sel >>= fun r => pure (PreparedLower.mk r.1 r.2)) =
      buildTreePrefixes lay tree sel := by
  unfold treeProgram buildTreePrefixes
  simp only [bind_assoc,pure_bind]
  congr 1
  apply congrArg (fun f => (List.range (2^height lay)).foldlM f ([],[],[]))
  funext st leaf
  exact body_eq lay hlay tree sel st leaf

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem buildTreePrefixes_tbsim {im : Image} (hc : SharedLowCode.Code im)
    (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s)
    (hpc : s.pc = pcOf 1173) (h1 : s.getReg .x1 = pcOf ret)
    (hselection : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val=BitVec.ofNat 64 sel) :
    TBSim im sk s btCost (buildTreePrefixes lay tree sel)
      (fun r => Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s (r.levels,r.prefixes)) := by
  have h := tree_tbsim hc hlevels hsub hcopy hchain hpref hseed hhook hs hpc h1 hselection
  rw [← treeProgram_eq lay hs.hlay tree sel]
  have ht : TBSim im sk s (btCost+0)
      (treeProgram lay tree sel >>= fun r => pure (PreparedLower.mk r.1 r.2))
      (fun r => Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s (r.levels,r.prefixes)) :=
    TBSim.bind (W₂:=0) h (fun r t ht => TBSim.pure ht)
  simpa using ht
end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem TreeWrites.not_metadata (lay : Layer) (hl : lay≠0) {A : Nat}
    (ha : 0x66000≤A) (hb : A<0x6e000) : ¬TreeWrites lay A := by
  have := lay.isLt
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  unfold TreeWrites
  omega

theorem Post.metadata {sk : SecretKey} {cache : Bytes 131072} {lay : Layer}
    {tree sel sb ret : Nat} {s u : MachineState} {r : List (List Digest) × List (List Digest)}
    (h : Post (cfFlag := cfFlag) sk cache lay tree sel sb ret s r u) (hl : lay≠0) (A : Nat)
    (ha : 0x66000≤A) (hb : A<0x6e000) :
    u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=
  h.precise.get (by omega) (TreeWrites.not_metadata lay hl ha hb)

theorem TreeWrites.not_other_prefix (lay other : Layer) (hne : lay≠other)
    (ho : other≠0) {i k : Nat} (hi : i<43) (hk : k<8) (half : Nat) (hh : half<2) :
    ¬TreeWrites lay (SharedPrefixes.buffer other.val i k+8*half) := by
  have hsame : lay.val≠other.val := fun h => hne (Fin.ext h)
  have hl := lay.isLt
  have hother := other.isLt
  have h0 : other.val≠0 := fun h => ho (Fin.ext h)
  unfold TreeWrites SharedPrefixes.buffer
  omega

end SigGolfCandidate.T3M.Sign.SharedLowTree
