import SigGolfCandidate.W9Machine.WctV3Source

/-!
Nested FTS (r1-1): the witness view of one coordinate.

Tree `n - 1` hands its computed top node to region `n` (the leaf pad or the level-5 Z slot, with junk on the header
in front of it), and the verifier reads tree `n`'s pads from memory. The chain and child contracts are stated for a
witness `w`; for coordinate `n` they are used with `viewW w n u`, the witness whose eight hand-off words of region
`n` are replaced by the memory of `u`. Everything else is the witness itself.
-/

set_option autoImplicit false
namespace W9Machine.V3
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3 (Digest M shortHash)

def setW64 {n : Nat} (w : BitVec n) (off : Nat) (x : BitVec 64) : BitVec n :=
  w ^^^ (((w.extractLsb' off 64) ^^^ x).setWidth n <<< off)

theorem extract_setW64 {n : Nat} (w : BitVec n) (off o : Nat) (x : BitVec 64) (hoff : off + 64 ≤ n)
    (ho : o + 64 ≤ n) (hdis : o = off ∨ o + 64 ≤ off ∨ off + 64 ≤ o) :
    (setW64 w off x).extractLsb' o 64 = if o = off then x else w.extractLsb' o 64 := by
  unfold setW64
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  split
  · subst o
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    have h1 : off + i < n := by omega
    simp only [h1, show ¬ (off + i < off) by omega, show off + i - off = i by omega, hi, show i < n by omega,
      decide_true, Bool.true_and]
    cases w.getLsbD (off + i) <;> cases x.getLsbD i <;> simp
  · rename_i hne
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    have h1 : o + i < n := by omega
    by_cases hlt : o + i < off
    · simp [h1, hlt]
    · have h2 : ¬ (o + i - off < 64) := by omega
      simp [h1, hlt, h2]
      rw [BitVec.getLsbD_of_ge x (o + i - off) (by omega)]
      simp

theorem extract128_of_halves {n : Nat} (v : BitVec n) (d : BitVec 128) (b : Nat)
    (h0 : v.extractLsb' b 64 = d.extractLsb' 0 64) (h1 : v.extractLsb' (b + 64) 64 = d.extractLsb' 64 64) :
    v.extractLsb' b 128 = d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hl : i < 64
  · have := congrArg (fun x => x.getLsbD i) h0
    simp only [BitVec.getLsbD_extractLsb', hl, decide_true, Bool.true_and, Nat.zero_add] at this
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact this
  · have := congrArg (fun x => x.getLsbD (i - 64)) h1
    simp only [BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega, decide_true, Bool.true_and] at this
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    rw [show b + i = b + 64 + (i - 64) by omega, this, show 64 + (i - 64) = i by omega]

theorem extract128_eq {n : Nat} (v w : BitVec n) (b : Nat)
    (h0 : v.extractLsb' b 64 = w.extractLsb' b 64) (h1 : v.extractLsb' (b + 64) 64 = w.extractLsb' (b + 64) 64) :
    v.extractLsb' b 128 = w.extractLsb' b 128 := by
  apply extract128_of_halves
  · rw [h0]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show i < 128 by omega]
  · rw [h1]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show 64 + i < 128 by omega, Nat.add_assoc]

def setWords {n : Nat} (w : BitVec n) (vals : Nat → BitVec 64) : List Nat → BitVec n
  | [] => w
  | o :: os => setW64 (setWords w vals os) o (vals o)

theorem extract_setWords {n : Nat} (w : BitVec n) (vals : Nat → BitVec 64) (os : List Nat) (p : Nat)
    (hos : ∀ o ∈ os, o % 64 = 0 ∧ o + 64 ≤ n) (hp : p % 64 = 0) (hpn : p + 64 ≤ n) :
    (setWords w vals os).extractLsb' p 64 = if p ∈ os then vals p else w.extractLsb' p 64 := by
  induction os with
  | nil => simp [setWords]
  | cons o os ih =>
    have ho := hos o (by simp)
    simp only [setWords]
    rw [extract_setW64 _ _ _ _ ho.2 hpn (by omega)]
    by_cases h : p = o
    · subst h; simp
    · rw [if_neg h, ih (fun o' h' => hos o' (List.mem_cons_of_mem _ h'))]
      simp [h]

/-- Hand-off words of a region: leaf header and pad (`704..736`), level-5 header and Z slot (`848..880`). -/
def handSlots : List Nat := [704, 712, 720, 728, 848, 856, 864, 872]
def isHand (o : Nat) : Prop := (704 ≤ o ∧ o < 736) ∨ (848 ≤ o ∧ o < 880)
instance (o : Nat) : Decidable (isHand o) := by unfold isHand; infer_instance
theorem mem_handSlots {o : Nat} (h8 : o % 8 = 0) : o ∈ handSlots ↔ isHand o := by
  unfold handSlots isHand
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega
def handBits (n : Nat) : List Nat := handSlots.map fun o => 8 * (regionOffset n + o)
/-- The witness seen by coordinate `n` at state `u`: region `n`'s hand-off words read from memory. -/
def viewW (w : WBytes) (n : Nat) (u : MachineState) : WBytes :=
  setWords w (fun b => u.getMem (BitVec.ofNat 64 (0x4c0 + b / 8))) (handBits n)

theorem regionOffset_mod (n : Nat) : regionOffset n % 8 = 0 := by unfold regionOffset; omega
theorem regionOffset_le (n : Nat) : regionOffset n ≤ 7344 := by unfold regionOffset; omega

/-- A 64-bit witness word of the view: memory on region `n`'s hand-off words, the witness elsewhere. -/
theorem view_word (w : WBytes) (n : Nat) (u : MachineState) (p : Nat) (hp : p % 8 = 0) (hpn : p + 8 ≤ 24028) :
    (viewW w n u).extractLsb' (8 * p) 64 =
      if regionOffset n ≤ p ∧ isHand (p - regionOffset n) then u.getMem (BitVec.ofNat 64 (0x4c0 + p))
      else w.extractLsb' (8 * p) 64 := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold viewW
  rw [extract_setWords _ _ _ _ ?_ (by omega) (by omega)]
  · have hmem : 8 * p ∈ handBits n ↔ regionOffset n ≤ p ∧ isHand (p - regionOffset n) := by
      unfold handBits
      simp only [List.mem_map]
      constructor
      · rintro ⟨o, ho, he⟩
        have h8 : o % 8 = 0 := by unfold handSlots at ho; simp at ho; omega
        have hh := (mem_handSlots h8).mp ho
        refine ⟨by omega, ?_⟩
        rw [show p - regionOffset n = o by omega]; exact hh
      · rintro ⟨hle, hh⟩
        refine ⟨p - regionOffset n, (mem_handSlots (by omega)).mpr hh, by omega⟩
    by_cases h : regionOffset n ≤ p ∧ isHand (p - regionOffset n)
    · rw [if_pos (hmem.mpr h), if_pos h, show 8 * p / 8 = p by omega]
    · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]
  · intro o ho
    unfold handBits handSlots at ho
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    omega

/-- Outside region `n`'s hand-off words the view is the witness. -/
theorem view_dig (w : WBytes) (n : Nat) (u : MachineState) (off : Nat) (h8 : off % 8 = 0)
    (hb : off + 16 ≤ 24028)
    (h0 : ¬ (regionOffset n ≤ off ∧ isHand (off - regionOffset n)))
    (h1 : ¬ (regionOffset n ≤ off + 8 ∧ isHand (off + 8 - regionOffset n))) :
    wdig (viewW w n u) off = wdig w off := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_eq
  · rw [view_word w n u off h8 (by omega), if_neg h0]
  · rw [show 8 * off + 64 = 8 * (off + 8) by omega, view_word w n u (off + 8) (by omega) (by omega), if_neg h1]

/-- On a hand-off slot pair the view holds the memory digest. -/
theorem view_dig_hand (w : WBytes) (n : Nat) (u : MachineState) (o : Nat) (ho : o = 720 ∨ o = 864) (hn : n ≤ 8)
    (d : Digest) (hd : DigAt u (0x4c0 + regionOffset n + o) d) :
    wdig (viewW w n u) (regionOffset n + o) = d := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_of_halves
  · rw [view_word w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.1, Nat.add_assoc]
  · rw [show 8 * (regionOffset n + o) + 64 = 8 * (regionOffset n + o + 8) by omega,
      view_word w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.2]
    congr 2
    omega

theorem child_low_bounds : ∀ j : Fin 128, ∀ l : Fin 5,
    sibOff j.val l.val + 16 ≤ 352 ∧ padOff j.val l.val + 16 ≤ 352 ∧ blkOff j.val l.val + 32 ≤ 352 ∧
    sibOff j.val l.val % 8 = 0 ∧ padOff j.val l.val % 8 = 0 ∧ blkOff j.val l.val % 8 = 0 := by
  decide +kernel

theorem view_dig_low (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (c : Nat) (hc8 : c % 8 = 0)
    (hc : c + 16 ≤ 704 ∨ (736 ≤ c ∧ c + 16 ≤ 848) ∨ (880 ≤ c ∧ c + 16 ≤ 896)) :
    wdig (viewW w n u) (regionOffset n + c) = wdig w (regionOffset n + c) := by
  have hr := regionOffset_mod n
  have hrl : regionOffset n ≤ 7344 := regionOffset_le n
  apply view_dig w n u _ (by omega) (by omega)
  · intro h; unfold isHand at h; omega
  · intro h; unfold isHand at h; omega

theorem sibling_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (l : Nat) :
    sibling (viewW w n u) n j.val l = sibling w n j.val l := by
  unfold sibling
  by_cases hl : l < 5
  · have hb := child_low_bounds j ⟨l, hl⟩
    simp only [Fin.val_mk] at hb
    exact view_dig_low w n u hn _ hb.2.2.2.1 (Or.inl (by omega))
  · have hs : sibOff j.val l = 832 ∨ sibOff j.val l = 880 := by
      unfold sibOff blkOff; rw [if_neg hl]; omega
    rcases hs with hs | hs <;> rw [hs]
    · exact view_dig_low w n u hn _ (by decide) (Or.inr (Or.inl ⟨by decide, by decide⟩))
    · exact view_dig_low w n u hn _ (by decide) (Or.inr (Or.inr ⟨by decide, by decide⟩))

theorem nodePad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (l : Nat) (hl : l < 5) :
    nodePad (viewW w n u) n j.val l = nodePad w n j.val l := by
  have hb := child_low_bounds j ⟨l, hl⟩
  simp only [Fin.val_mk] at hb
  exact view_dig_low w n u hn _ hb.2.2.2.2.1 (Or.inl (by omega))

theorem nodeHPad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (l : Nat) :
    nodeHPad (viewW w n u) n j.val l = nodeHPad w n j.val l := by
  unfold nodeHPad
  by_cases hl : l < 4 ∧ j.val / 2 ^ l % 2 = 1
  · rw [if_pos hl, if_pos hl]
    have hb := child_low_bounds j ⟨l, by omega⟩
    simp only [Fin.val_mk] at hb
    unfold nodeTw
    rw [show regionOffset n + blkOff j.val l + 16 = regionOffset n + (blkOff j.val l + 16) by omega,
      view_dig_low w n u hn _ (by omega) (Or.inl (by omega))]
  · rw [if_neg hl, if_neg hl]

theorem leafPad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (d : Digest)
    (hd : DigAt u (0x4c0 + regionOffset n + 720) d) : leafPad (viewW w n u) n = d :=
  view_dig_hand w n u 720 (Or.inl rfl) hn d hd

theorem nodePad5_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (d : Digest)
    (hd : DigAt u (0x4c0 + regionOffset n + 864) d) : nodePad (viewW w n u) n j.val 5 = d := by
  unfold nodePad padOff blkOff
  rw [if_neg (by decide), show regionOffset n + (832 + 32) = regionOffset n + 864 by omega]
  exact view_dig_hand w n u 864 (Or.inr rfl) hn d hd

/-- The nested child of coordinate `n` read through the view is the tree with the hand-off pads. -/
theorem childProgram_view (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState) (j : Fin 128)
    (ends : List Digest) (padL padZ : Digest)
    (hL : DigAt u (0x4c0 + regionOffset k.val + 720) padL) (hZ : DigAt u (0x4c0 + regionOffset k.val + 864) padZ) :
    childProgram (viewW w k.val u) index k j ends = childN w index k j ends padL padZ := by
  have hn : k.val ≤ 8 := by omega
  unfold childProgram childN
  rw [leafPad_view w k.val u hn padL hL, nodePad5_view w k.val u hn j padZ hZ]
  simp only [sibling_view w k.val u hn j, nodeHPad_view w k.val u hn j,
    show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.foldlM_cons, List.foldlM_nil,
    nodePad_view w k.val u hn j 0 (by decide), nodePad_view w k.val u hn j 1 (by decide),
    nodePad_view w k.val u hn j 2 (by decide), nodePad_view w k.val u hn j 3 (by decide),
    nodePad_view w k.val u hn j 4 (by decide)]

/-- The chains of coordinate `n` do not read the hand-off words. -/
theorem chainProgram_view (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState) (j : Fin 128)
    (rank : Fin 666) :
    chainProgram (viewW w k.val u) index k j rank = chainProgram w index k j rank := by
  have hn : k.val ≤ 8 := by omega
  unfold chainProgram
  congr 1
  funext t
  have ht := t.isLt
  have hA : chainPadA (viewW w k.val u) k.val t.val = chainPadA w k.val t.val := by
    unfold chainPadA chainOffset
    exact view_dig_low w k.val u hn _ (by omega) (Or.inl (by omega))
  have hC : chainPadC (viewW w k.val u) k.val t.val = chainPadC w k.val t.val := by
    unfold chainPadC chainOffset
    rw [Nat.add_assoc]
    exact view_dig_low w k.val u hn _ (by omega) (Or.inl (by omega))
  have hB : chainPadB (viewW w k.val u) k.val t.val = chainPadB w k.val t.val := by
    unfold chainPadB chainOffset
    have hr := regionOffset_mod k.val
    have hrl := regionOffset_le k.val
    rw [view_word w k.val u _ (by omega) (by omega), if_neg (by unfold isHand; omega)]
  have hR : ∀ d, reveal (viewW w k.val u) k.val t.val d = reveal w k.val t.val d := by
    intro d
    unfold reveal
    split
    · unfold leafSlot
      split
      · exact view_dig_low w k.val u hn _ (by decide) (Or.inl (by decide))
      · exact view_dig_low w k.val u hn _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · unfold chainOffset
      rw [Nat.add_assoc]
      exact view_dig_low w k.val u hn _ (by omega) (Or.inl (by omega))
  simp only [hA, hB, hC, hR]

end W9Machine.V3
