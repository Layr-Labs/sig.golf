import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros)
open SphincsSecurity (bytesLE bytesLE_length)

/-- The established compact producer's output before moving its digest header. -/
def legacyDigestBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12

def legacyHeaderBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++
    bytesLE 4 (w.counters 3) ++ zeros 28

def legacyWitList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  legacyHeaderBytes w ++ wctBytes N w.signature ++ zeros 8 ++
    (List.finRange 4).flatMap (layerRegion N w)

theorem legacyHeaderBytes_eq (w : WCT9.Witness) :
    legacyHeaderBytes w = legacyDigestBytes w ++ headerBytes w := by
  simp only [legacyHeaderBytes, legacyDigestBytes, headerBytes, List.append_assoc]

theorem legacyHeaderBytes_length (w : WCT9.Witness) :
    (legacyHeaderBytes w).length = 64 := by
  simp [legacyHeaderBytes, bytesLE_length, zeros]

theorem legacyWitList_eq (N : HashOutput) (w : WCT9.Witness) :
    legacyWitList N w = legacyDigestBytes w ++ witBody N w := by
  simp only [legacyWitList, legacyHeaderBytes_eq, witBody, List.append_assoc]

/-- Move the body forward, then retain nonce and counter with the new zero header. -/
def rotateWitBytes (l : List UInt8) : List UInt8 :=
  l.drop 32 ++ (l.drop 16).take 4 ++ zeros 12 ++ l.take 16

theorem legacyDigestBytes_length (w : WCT9.Witness) :
    (legacyDigestBytes w).length = 32 := by
  simp [legacyDigestBytes, zeros, bytesLE_length]

theorem legacyWitList_length_eq (N : HashOutput) (w : WCT9.Witness) :
    (legacyWitList N w).length = 21832 := by
  rw [legacyWitList_eq]
  simp only [List.length_append, legacyDigestBytes_length, witBody_length_eq]

theorem rotate_legacy_parts (nonce counter body : List UInt8)
    (hn : nonce.length = 16) (hc : counter.length = 4) :
    rotateWitBytes ((nonce ++ counter ++ zeros 12) ++ body) =
      body ++ counter ++ zeros 12 ++ nonce := by
  have hh : (nonce ++ counter ++ zeros 12).length = 32 := by
    simp [hn, hc, zeros]
  have hb : (((nonce ++ counter ++ zeros 12) ++ body).drop 32) = body :=
    List.drop_left' hh
  have hn' : (((nonce ++ counter ++ zeros 12) ++ body).take 16) = nonce := by
    simpa only [List.append_assoc] using
      (List.take_left' (l₂ := counter ++ zeros 12 ++ body) hn)
  have hd : (((nonce ++ counter ++ zeros 12) ++ body).drop 16) =
      counter ++ zeros 12 ++ body := by
    simpa only [List.append_assoc] using
      (List.drop_left' (l₂ := counter ++ zeros 12 ++ body) hn)
  have hc' : (counter ++ zeros 12 ++ body).take 4 = counter := by
    simpa only [List.append_assoc] using
      (List.take_left' (l₂ := zeros 12 ++ body) hc)
  rw [rotateWitBytes, hb, hn', hd, hc']

theorem rotate_legacy_witness (N : HashOutput) (w : WCT9.Witness) :
    rotateWitBytes (legacyWitList N w) = witList N w := by
  rw [legacyWitList_eq]
  unfold legacyDigestBytes
  rw [rotate_legacy_parts _ _ _ (bytesLE_length _ _) (bytesLE_length _ _)]
  simp only [witList, digestBytes, List.append_assoc]

#print axioms rotate_legacy_witness
end ClaudeWCT.W9.T3M
