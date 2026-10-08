import SigGolfCandidate.T3M.Sign.PackedSourceBridge
import SigGolfCandidate.T3M.Sign.BoundaryInvariant
import SigGolfCandidate.T3M.Sign.InitState
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Main
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.PackedLeaf
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.TopLeafP

namespace ClaudeWCT.W9.Machine.SignLink
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open ClaudeWCT.W9.Machine.Sign (TableAt CostAt TBL COST tblBytes costBytes HookPre SignCodeAt SignRefinesW
  SignTerminatesW signNew)
set_option maxRecDepth 100000
theorem signPrefixData_split : Images.signPrefixData = costBytes ++ tblBytes := by
  unfold Images.signPrefixData ClaudeWCT.W9.Machine.Sign.costBytes ClaudeWCT.W9.Machine.Sign.tblBytes
  rw [← List.flatten_append]
  rfl
theorem signData_split : Images.signData = costBytes ++ (tblBytes ++ Images.signLegacyData) := by
  rw [Images.signData, signPrefixData_split, List.append_assoc]
theorem slice_mid {α : Type} (l1 l2 l3 : List α) (n : Nat) (h : n + 8 ≤ l2.length) :
    ((l1 ++ (l2 ++ l3)).drop (l1.length + n)).take 8 = (l2.drop n).take 8 := by
  rw [List.drop_append, List.drop_eq_nil_of_le (show l1.length ≤ l1.length + n by omega), List.nil_append,
    Nat.add_sub_cancel_left, List.drop_append_of_le_length (show n ≤ l2.length by omega),
    List.take_append_of_le_length (show 8 ≤ (l2.drop n).length by rw [List.length_drop]; omega)]
theorem slice_head {α : Type} (l1 l2 : List α) (n : Nat) (h : n + 8 ≤ l1.length) :
    ((l1 ++ l2).drop n).take 8 = (l1.drop n).take 8 := by
  rw [List.drop_append_of_le_length (show n ≤ l1.length by omega),
    List.take_append_of_le_length (show 8 ≤ (l1.drop n).length by rw [List.length_drop]; omega)]
theorem sinit_wct_cost (sk : SecretKey) (cache : Bytes 131072) (m : Message) : CostAt (sinit sk cache m) := by
  intro k hk
  have hc := ClaudeWCT.W9.Machine.Sign.SearchM.costBytes_length
  rw [sinit_getMem _ _ _ _ (by unfold COST; omega), if_neg (by unfold COST; omega), if_neg (by unfold COST; omega),
    if_neg (by unfold COST; omega), sdata_getMem _ (by unfold COST; omega),
    if_pos (by unfold COST SIGN_DATA; omega), show COST + 8 * k - SIGN_DATA = 8 * k by unfold COST SIGN_DATA; omega,
    signData_split, slice_head _ _ _ (by omega)]
theorem sinit_wct_table (sk : SecretKey) (cache : Bytes 131072) (m : Message) : TableAt (sinit sk cache m) := by
  intro k hk
  have hc := ClaudeWCT.W9.Machine.Sign.SearchM.costBytes_length
  have ht := ClaudeWCT.W9.Machine.Sign.tblBytes_length
  rw [sinit_getMem _ _ _ _ (by unfold TBL; omega), if_neg (by unfold TBL; omega), if_neg (by unfold TBL; omega),
    if_neg (by unfold TBL; omega), sdata_getMem _ (by unfold TBL; omega),
    if_pos (by unfold TBL SIGN_DATA; omega), show TBL + 8 * k - SIGN_DATA = costBytes.length + 8 * k by
      rw [hc]; unfold TBL SIGN_DATA; omega,
    signData_split, slice_mid _ _ _ _ (by omega)]
theorem hook_v7 {sk : SecretKey} {cache : Bytes 131072} {m : Message} {rho : SigGolfCandidate.T3.Digest}
    {t : MachineState} (h : NoncePost sk cache m rho t) : HookPre sk m rho t := by
  refine ⟨⟨h.search.pc, h.search.x5, h.search.x19, h.search.rho, h.search.msg, ?_⟩, h.rho, ?_, ?_, ?_⟩
  · intro k hk
    rw [h.frame.get (by unfold COST; omega) (by unfold FrontW COST; sg_omega)]
    exact sinit_wct_cost sk cache m k hk
  · intro k hk
    change t.getMem (BitVec.ofNat 64 (0x80 + 8 * k)) = _
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_sk sk cache m k hk
  · intro A hA
    simp only [ClaudeWCT.W9.Machine.Sign.ScrZero, ClaudeWCT.W9.Machine.Sign.PRIVW, ClaudeWCT.W9.Machine.Sign.CHAINW,
      ClaudeWCT.W9.Machine.Sign.NODEW] at hA
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold SIGN_DATA; omega) (by sg_omega)
  · intro k hk
    rw [h.frame.get (by unfold TBL; omega) (by unfold FrontW TBL; sg_omega)]
    exact sinit_wct_table sk cache m k hk
theorem wct_unchanged_v7 :
    ClaudeWCT.W9.Machine.Sign.Unchanged submission.image (fun sk cache _m => Inv sk cache) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sk cache m
    refine ⟨sinit sk cache m, initialState_sign sk cache m, ?_⟩
    intro α W Q K hfail hrest
    exact nonce_front K (fun t ht => hfail t ⟨ht.pc, ht.x5, ht.x10⟩)
      (fun rho t ht => hrest rho t (hook_v7 ht) ht.inv)
  · intro sk cache m t u h hf hr
    exact Inv.stable h hf hr (by simp [ClaudeWCT.W9.Machine.Sign.newRegs])
  · intro sk cache m index root s hp hi
    have hs := Sign.Packed.layers_from370_canonical ClaudeWCT.W9.Machine.Sign.PackedLeaf.packedLeafSpecV
      ClaudeWCT.W9.Machine.Sign.TopLeafP.topLeafSpec
      hp.pc hi.1 hp.hidx hp.idx hp.root (by rw [hi.2.1]; decide) (by exact ⟨hi.2.2.1, hi.2.2.2⟩)
    refine TBSim.mono hs (by rw [Sign.Packed.layers_entry_cost]; decide) (fun r u hu => ?_)
    cases r with
    | none => exact ⟨hu.pc, hu.x5, hu.x10⟩
    | some ps =>
      obtain ⟨hpc, hlen, hpieces, hf⟩ := hu
      exact ⟨hpc, hlen, fun lay => hpieces lay lay.isLt, hf.mono (fun A _ h => h.1)⟩
set_option maxHeartbeats 0 in
theorem signCode_drop_v7 : Images.signImage.code.drop 11003 = signNew ++ Images.signImage.code.drop 20771 := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem wct_signCodeAt_v7 : SignCodeAt Images.signImage := by
  refine ⟨?_, ?_⟩
  · exact ⟨_, signCode_drop_v7.symm⟩
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem wct_sign_certified_v7 :
    SignRefinesW submission.image ∧ SignTerminatesW submission.image :=
  ClaudeWCT.W9.Machine.Sign.signMain submission.image (fun sk cache _m => Inv sk cache) wct_signCodeAt_v7
    wct_unchanged_v7
end ClaudeWCT.W9.Machine.SignLink
