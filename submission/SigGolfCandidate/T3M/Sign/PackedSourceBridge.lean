import SigGolfCandidate.T3M.Sign.PackedBoundaryEntry

namespace SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT
theorem buildTreeP_eq (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    buildTreeP WCT9.buildLeafPF lay tree selected digits = WCT9.buildTreeP lay tree selected digits := rfl
theorem signLayersP_eq (cache : Cache) (index n : Nat) (msg : WCT9.LayerMsg) :
    signLayersP WCT9.buildLeafPF cache index n msg = WCT9.signLayersBC cache index n msg := by
  induction n generalizing msg with
  | zero => rfl
  | succ n ih =>
    simp only [signLayersP, WCT9.signLayersBC, buildTreeP_eq, ih]
    rfl
theorem layers_entry_cost : 26 + Boundary.layersC = 3059126125 := by decide +kernel
theorem layers_from370_canonical
    (hPacked : PackedLeafSpec WCT9.buildLeafPF) (hTop : TopLeafSpec)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    {root : Digest} {s : MachineState} (hp : s.pc = pcOf 370)
    (hb : Base sk cache s) (hi : index < 2 ^ 31)
    (hx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index)
    (hr : DigAt s FOUT root)
    (hc : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32)
    (hz : DigAt s (ENC + 48) 0) :
    TBSim image sk s (26 + Boundary.layersC)
      (WCT9.signLayersBC (cacheDec cache) index 4 (.forest root)) (Boundary.SLPost s 4) := by
  rw [← signLayersP_eq]
  exact Boundary.layers_from370 hPacked hTop hp hb hi hx hr hc hz
end SigGolfCandidate.T3M.Sign.Packed
