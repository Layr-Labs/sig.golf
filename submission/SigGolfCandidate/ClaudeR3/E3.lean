import SigGolfCandidate.ClaudeR3.E2

namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM tabS)
open ClaudeR3.BonfData

noncomputable def sumsL (lit : List ℕ) (x y : ℕ) : SN :=
  ⟨lit.getD 0 0,
    nsum 15 fun m => x ^ m * lit.getD (1 + m) 0,
    nsum 15 fun l => y ^ l * lit.getD (1 + l) 0,
    nsum 15 fun l => y ^ l * nsum 15 fun m => x ^ m * lit.getD (sidx (min l m) (max l m)) 0⟩

noncomputable def dTermL (P Q : List (List ℕ)) (k L x j : ℕ) : ℕ :=
  nsum 4 fun e => nsum 4 fun f => nPairN e f *
    nineN e f x (x ^ L) (sumsL (P.getD j []) x (x ^ L)) (sumsL (Q.getD (k - j) []) x (x ^ L))

noncomputable def famDPL0 (k L x : ℕ) : ℕ :=
  nsum (k + 1) fun j => k.choose j * (dTermL tqPA tqPB k L x j + dTermL tqNA tqNB k L x j)
noncomputable def famDNL0 (k L x : ℕ) : ℕ :=
  nsum (k + 1) fun j => k.choose j * (dTermL tqPA tqNB k L x j + dTermL tqNA tqPB k L x j)

structure N9 where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  c6 : ℕ
  c7 : ℕ
  c8 : ℕ

def pairsN (P Q : SN) : N9 :=
  ⟨P.s0 * Q.s0, P.s1y * Q.s0, P.s0 * Q.s1y, P.s1x * Q.s0, P.s2 * Q.s0, P.s1x * Q.s1y, P.s0 * Q.s1x,
    P.s1y * Q.s1x, P.s0 * Q.s2⟩

noncomputable def nine9 (e f x y : ℕ) (c : N9) : ℕ :=
  AN2 e f x * AN2 e f y * c.c0 + AN2 e f x * y ^ e * c.c1 + AN2 e f x * y ^ f * c.c2
    + x ^ e * AN2 e f y * c.c3 + x ^ e * y ^ e * c.c4 + x ^ e * y ^ f * c.c5
    + x ^ f * AN2 e f y * c.c6 + x ^ f * y ^ e * c.c7 + x ^ f * y ^ f * c.c8

noncomputable def convN (P Q : List (List ℕ)) (k L x : ℕ) : N9 :=
  let g := fun j => pairsN (sumsL (P.getD j []) x (x ^ L)) (sumsL (Q.getD (k - j) []) x (x ^ L))
  ⟨nsum (k + 1) fun j => k.choose j * (g j).c0, nsum (k + 1) fun j => k.choose j * (g j).c1,
    nsum (k + 1) fun j => k.choose j * (g j).c2, nsum (k + 1) fun j => k.choose j * (g j).c3,
    nsum (k + 1) fun j => k.choose j * (g j).c4, nsum (k + 1) fun j => k.choose j * (g j).c5,
    nsum (k + 1) fun j => k.choose j * (g j).c6, nsum (k + 1) fun j => k.choose j * (g j).c7,
    nsum (k + 1) fun j => k.choose j * (g j).c8⟩

noncomputable def dSumL (P Q : List (List ℕ)) (k L x : ℕ) : ℕ :=
  nsum 4 fun e => nsum 4 fun f => nPairN e f * nine9 e f x (x ^ L) (convN P Q k L x)

noncomputable def famDPL (k L x : ℕ) : ℕ := dSumL tqPA tqPB k L x + dSumL tqNA tqNB k L x
noncomputable def famDNL (k L x : ℕ) : ℕ := dSumL tqPA tqNB k L x + dSumL tqNA tqPB k L x

noncomputable def Wv2L (k B : ℕ) : ℕ :=
  (famP tabS k 154 B + famDPL k 154 B) - (famN tabS k 154 B + famDNL k 154 B)

noncomputable def Wv2L1 (k : ℕ) : ℕ :=
  (famP1 tabS k + famDPL k 154 1) - (famN1 tabS k + famDNL k 154 1)

noncomputable def diagCheckL (r : ℕ) : Bool :=
  decide (Wv2L1 (r - 2) ^ 9 * ((153 - 104) * 154) < 2 ^ diagBB.getD r 0) &&
    Nat.ble (bonfNF (Wv2L1 (r - 2) ^ 9) (Wv2L (r - 2) (2 ^ diagBB.getD r 0) ^ 9) 104 (diagRp.getD r 0)
      (2 ^ diagBB.getD r 0)) (diagD.getD r 0)

end ClaudeR3.Ev
