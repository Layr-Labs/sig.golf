import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.ProducerDecodeV5
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.Numerics.CoverageHistogramWork
import SigGolfCandidate.ClaudeWCT.Numerics.N600Data
import SigGolfCandidate.ClaudeWCT.Numerics.Kernel

-- Keep the independent kernel certificates sequential to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

section


namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (wpos wneg fact HB packPos packNeg)
def Nn : Nat := 563
def Kc : Nat := 128
def Q : Nat := 72064
def B1 : Nat := 71501
def B2 : Nat := 70938
def xNum (r : Nat) : Nat := wpos w1Data B1 r - wneg w1Data B1 r
def xfNum (t r : Nat) : Nat := wpos (wfData t) B1 r - wneg (wfData t) B1 r
def xfSum (r : Nat) : Nat := xfNum 0 r + xfNum 1 r + xfNum 2 r + xfNum 3 r + xfNum 4 r + xfNum 5 r
def yPos (r : Nat) : Nat := wpos w2Data B1 r + (Kc - 1) * wpos wwData B2 r
def yNeg (r : Nat) : Nat := wneg w2Data B1 r + (Kc - 1) * wneg wwData B2 r
def yNum (r : Nat) : Nat := yPos r - yNeg r
def poissonCheckQ (Qv un ud ln ld : Nat) (f : Nat → Nat) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Qv ^ (9 * (R - r)) + s) 0
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R)) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Qv ^ (9 * R)
def A : Nat := 1353 * 2 ^ 24 * 563 ^ 9
def LN : Nat := 203317755
def LD : Nat := 100000000
def MN : Nat := 675
def MD : Nat := 1000
def DN : Nat := 3200
def DD : Nat := 1000000
def NN : Nat := 291
def ND : Nat := 1
def meanCheck : Bool := poissonCheckQ Q 13533529 100000000 LN LD (fun r => xNum r ^ 9) (Nn ^ 9) A 1 MN MD 80
def diagCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => yNum r ^ 9) ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31) DN DD 80
def nearCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => xNum r ^ 8 * xfSum r) (6 * Nn ^ 9) (54 * A) 1 NN ND 80
def convCheck : Bool :=
  Nat.beq (packPos w1Data ^ 2 + packNeg w1Data ^ 2 + packNeg wwData) (packPos wwData + 2 * packPos w1Data * packNeg w1Data)
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem mean_ok : meanCheck = true := by decide +kernel
theorem near_ok : nearCheck = true := by decide +kernel
theorem diag_ok : diagCheck = true := by decide +kernel
theorem conv_ok : convCheck = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end


namespace ClaudeWCT.Numerics.N600
-- Certify the shared prefix-count tree once for the eight finite histogram checks.
private def cntCached0 : T6 := .leaf 0
private def cntCached1 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached0
private def cntCached2 : T6 := .node cntCached1 cntCached1 cntCached1 cntCached1 cntCached1 cntCached1
private def cntCached3 : T6 := .node cntCached2 cntCached2 cntCached2 cntCached2 cntCached2 cntCached2
private def cntCached4 : T6 := .node cntCached3 cntCached3 cntCached3 cntCached3 cntCached3 cntCached3
private def cntCached5 : T6 := .node cntCached4 cntCached4 cntCached4 cntCached4 cntCached4 cntCached4
private def cntCached6 : T6 := .leaf 1
private def cntCached7 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached6
private def cntCached8 : T6 := .leaf 2
private def cntCached9 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached8
private def cntCached10 : T6 := .node cntCached1 cntCached1 cntCached1 cntCached1 cntCached7 cntCached9
private def cntCached11 : T6 := .leaf 3
private def cntCached12 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached11
private def cntCached13 : T6 := .leaf 5
private def cntCached14 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached11 cntCached13
private def cntCached15 : T6 := .node cntCached1 cntCached1 cntCached1 cntCached7 cntCached12 cntCached14
private def cntCached16 : T6 := .leaf 6
private def cntCached17 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached11 cntCached16
private def cntCached18 : T6 := .leaf 9
private def cntCached19 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached16 cntCached18
private def cntCached20 : T6 := .node cntCached1 cntCached1 cntCached7 cntCached12 cntCached17 cntCached19
private def cntCached21 : T6 := .leaf 10
private def cntCached22 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached16 cntCached21
private def cntCached23 : T6 := .leaf 14
private def cntCached24 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached16 cntCached21 cntCached23
private def cntCached25 : T6 := .node cntCached1 cntCached7 cntCached12 cntCached17 cntCached22 cntCached24
private def cntCached26 : T6 := .leaf 18
private def cntCached27 : T6 := .node cntCached0 cntCached8 cntCached13 cntCached18 cntCached23 cntCached26
private def cntCached28 : T6 := .node cntCached1 cntCached9 cntCached14 cntCached19 cntCached24 cntCached27
private def cntCached29 : T6 := .node cntCached2 cntCached10 cntCached15 cntCached20 cntCached25 cntCached28
private def cntCached30 : T6 := .leaf 4
private def cntCached31 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached30
private def cntCached32 : T6 := .leaf 8
private def cntCached33 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached30 cntCached32
private def cntCached34 : T6 := .leaf 12
private def cntCached35 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached32 cntCached34
private def cntCached36 : T6 := .node cntCached1 cntCached1 cntCached7 cntCached31 cntCached33 cntCached35
private def cntCached37 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached30 cntCached18
private def cntCached38 : T6 := .leaf 15
private def cntCached39 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached18 cntCached38
private def cntCached40 : T6 := .leaf 21
private def cntCached41 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached38 cntCached40
private def cntCached42 : T6 := .node cntCached1 cntCached7 cntCached31 cntCached37 cntCached39 cntCached41
private def cntCached43 : T6 := .leaf 16
private def cntCached44 : T6 := .leaf 23
private def cntCached45 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached43 cntCached44
private def cntCached46 : T6 := .leaf 30
private def cntCached47 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached38 cntCached44 cntCached46
private def cntCached48 : T6 := .node cntCached1 cntCached12 cntCached33 cntCached39 cntCached45 cntCached47
private def cntCached49 : T6 := .leaf 37
private def cntCached50 : T6 := .node cntCached0 cntCached13 cntCached34 cntCached40 cntCached46 cntCached49
private def cntCached51 : T6 := .node cntCached1 cntCached14 cntCached35 cntCached41 cntCached47 cntCached50
private def cntCached52 : T6 := .node cntCached2 cntCached15 cntCached36 cntCached42 cntCached48 cntCached51
private def cntCached53 : T6 := .leaf 17
private def cntCached54 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached21 cntCached53
private def cntCached55 : T6 := .leaf 26
private def cntCached56 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached26 cntCached55
private def cntCached57 : T6 := .leaf 34
private def cntCached58 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached53 cntCached55 cntCached57
private def cntCached59 : T6 := .node cntCached1 cntCached12 cntCached37 cntCached54 cntCached56 cntCached58
private def cntCached60 : T6 := .leaf 28
private def cntCached61 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached60 cntCached49
private def cntCached62 : T6 := .leaf 46
private def cntCached63 : T6 := .node cntCached0 cntCached16 cntCached38 cntCached55 cntCached49 cntCached62
private def cntCached64 : T6 := .node cntCached1 cntCached17 cntCached39 cntCached56 cntCached61 cntCached63
private def cntCached65 : T6 := .leaf 55
private def cntCached66 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached57 cntCached62 cntCached65
private def cntCached67 : T6 := .node cntCached1 cntCached19 cntCached41 cntCached58 cntCached63 cntCached66
private def cntCached68 : T6 := .node cntCached2 cntCached20 cntCached42 cntCached59 cntCached64 cntCached67
private def cntCached69 : T6 := .leaf 40
private def cntCached70 : T6 := .leaf 50
private def cntCached71 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached60 cntCached69 cntCached70
private def cntCached72 : T6 := .leaf 60
private def cntCached73 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached49 cntCached70 cntCached72
private def cntCached74 : T6 := .node cntCached1 cntCached22 cntCached45 cntCached61 cntCached71 cntCached73
private def cntCached75 : T6 := .leaf 70
private def cntCached76 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached62 cntCached72 cntCached75
private def cntCached77 : T6 := .node cntCached1 cntCached24 cntCached47 cntCached63 cntCached73 cntCached76
private def cntCached78 : T6 := .node cntCached2 cntCached25 cntCached48 cntCached64 cntCached74 cntCached77
private def cntCached79 : T6 := .leaf 80
private def cntCached80 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached65 cntCached75 cntCached79
private def cntCached81 : T6 := .node cntCached1 cntCached27 cntCached50 cntCached66 cntCached76 cntCached80
private def cntCached82 : T6 := .node cntCached2 cntCached28 cntCached51 cntCached67 cntCached77 cntCached81
private def cntCached83 : T6 := .node cntCached3 cntCached29 cntCached52 cntCached68 cntCached78 cntCached82
private def cntCached84 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached13
private def cntCached85 : T6 := .leaf 11
private def cntCached86 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached30 cntCached85
private def cntCached87 : T6 := .leaf 19
private def cntCached88 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached85 cntCached87
private def cntCached89 : T6 := .leaf 27
private def cntCached90 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached85 cntCached87 cntCached89
private def cntCached91 : T6 := .node cntCached1 cntCached7 cntCached84 cntCached86 cntCached88 cntCached90
private def cntCached92 : T6 := .leaf 20
private def cntCached93 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached21 cntCached92
private def cntCached94 : T6 := .leaf 32
private def cntCached95 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached40 cntCached94
private def cntCached96 : T6 := .leaf 43
private def cntCached97 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached92 cntCached94 cntCached96
private def cntCached98 : T6 := .node cntCached1 cntCached31 cntCached86 cntCached93 cntCached95 cntCached97
private def cntCached99 : T6 := .leaf 35
private def cntCached100 : T6 := .leaf 47
private def cntCached101 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached40 cntCached99 cntCached100
private def cntCached102 : T6 := .leaf 59
private def cntCached103 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached94 cntCached100 cntCached102
private def cntCached104 : T6 := .node cntCached1 cntCached33 cntCached88 cntCached95 cntCached101 cntCached103
private def cntCached105 : T6 := .leaf 71
private def cntCached106 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached96 cntCached102 cntCached105
private def cntCached107 : T6 := .node cntCached1 cntCached35 cntCached90 cntCached97 cntCached103 cntCached106
private def cntCached108 : T6 := .node cntCached2 cntCached36 cntCached91 cntCached98 cntCached104 cntCached107
private def cntCached109 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached32 cntCached40 cntCached57
private def cntCached110 : T6 := .leaf 51
private def cntCached111 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached40 cntCached49 cntCached110
private def cntCached112 : T6 := .leaf 65
private def cntCached113 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached110 cntCached112
private def cntCached114 : T6 := .node cntCached1 cntCached37 cntCached93 cntCached109 cntCached111 cntCached113
private def cntCached115 : T6 := .leaf 56
private def cntCached116 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached49 cntCached115 cntCached105
private def cntCached117 : T6 := .leaf 86
private def cntCached118 : T6 := .node cntCached0 cntCached38 cntCached94 cntCached110 cntCached105 cntCached117
private def cntCached119 : T6 := .node cntCached1 cntCached39 cntCached95 cntCached111 cntCached116 cntCached118
private def cntCached120 : T6 := .leaf 101
private def cntCached121 : T6 := .node cntCached0 cntCached40 cntCached96 cntCached112 cntCached117 cntCached120
private def cntCached122 : T6 := .node cntCached1 cntCached41 cntCached97 cntCached113 cntCached118 cntCached121
private def cntCached123 : T6 := .node cntCached2 cntCached42 cntCached98 cntCached114 cntCached119 cntCached122
private def cntCached124 : T6 := .leaf 78
private def cntCached125 : T6 := .leaf 94
private def cntCached126 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached115 cntCached124 cntCached125
private def cntCached127 : T6 := .leaf 110
private def cntCached128 : T6 := .node cntCached0 cntCached44 cntCached100 cntCached105 cntCached125 cntCached127
private def cntCached129 : T6 := .node cntCached1 cntCached45 cntCached101 cntCached116 cntCached126 cntCached128
private def cntCached130 : T6 := .leaf 126
private def cntCached131 : T6 := .node cntCached0 cntCached46 cntCached102 cntCached117 cntCached127 cntCached130
private def cntCached132 : T6 := .node cntCached1 cntCached47 cntCached103 cntCached118 cntCached128 cntCached131
private def cntCached133 : T6 := .node cntCached2 cntCached48 cntCached104 cntCached119 cntCached129 cntCached132
private def cntCached134 : T6 := .leaf 142
private def cntCached135 : T6 := .node cntCached0 cntCached49 cntCached105 cntCached120 cntCached130 cntCached134
private def cntCached136 : T6 := .node cntCached1 cntCached50 cntCached106 cntCached121 cntCached131 cntCached135
private def cntCached137 : T6 := .node cntCached2 cntCached51 cntCached107 cntCached122 cntCached132 cntCached136
private def cntCached138 : T6 := .node cntCached3 cntCached52 cntCached108 cntCached123 cntCached133 cntCached137
private def cntCached139 : T6 := .leaf 39
private def cntCached140 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached92 cntCached139 cntCached65
private def cntCached141 : T6 := .leaf 61
private def cntCached142 : T6 := .node cntCached0 cntCached21 cntCached40 cntCached139 cntCached141 cntCached124
private def cntCached143 : T6 := .leaf 95
private def cntCached144 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached65 cntCached124 cntCached143
private def cntCached145 : T6 := .node cntCached1 cntCached54 cntCached109 cntCached140 cntCached142 cntCached144
private def cntCached146 : T6 := .leaf 104
private def cntCached147 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached141 cntCached117 cntCached146
private def cntCached148 : T6 := .leaf 122
private def cntCached149 : T6 := .node cntCached0 cntCached55 cntCached110 cntCached124 cntCached146 cntCached148
private def cntCached150 : T6 := .node cntCached1 cntCached56 cntCached111 cntCached142 cntCached147 cntCached149
private def cntCached151 : T6 := .leaf 140
private def cntCached152 : T6 := .node cntCached0 cntCached57 cntCached112 cntCached143 cntCached148 cntCached151
private def cntCached153 : T6 := .node cntCached1 cntCached58 cntCached113 cntCached144 cntCached149 cntCached152
private def cntCached154 : T6 := .node cntCached2 cntCached59 cntCached114 cntCached145 cntCached150 cntCached153
private def cntCached155 : T6 := .leaf 114
private def cntCached156 : T6 := .leaf 133
private def cntCached157 : T6 := .node cntCached0 cntCached60 cntCached115 cntCached117 cntCached155 cntCached156
private def cntCached158 : T6 := .leaf 152
private def cntCached159 : T6 := .node cntCached0 cntCached49 cntCached105 cntCached146 cntCached156 cntCached158
private def cntCached160 : T6 := .node cntCached1 cntCached61 cntCached116 cntCached147 cntCached157 cntCached159
private def cntCached161 : T6 := .leaf 171
private def cntCached162 : T6 := .node cntCached0 cntCached62 cntCached117 cntCached148 cntCached158 cntCached161
private def cntCached163 : T6 := .node cntCached1 cntCached63 cntCached118 cntCached149 cntCached159 cntCached162
private def cntCached164 : T6 := .node cntCached2 cntCached64 cntCached119 cntCached150 cntCached160 cntCached163
private def cntCached165 : T6 := .leaf 190
private def cntCached166 : T6 := .node cntCached0 cntCached65 cntCached120 cntCached151 cntCached161 cntCached165
private def cntCached167 : T6 := .node cntCached1 cntCached66 cntCached121 cntCached152 cntCached162 cntCached166
private def cntCached168 : T6 := .node cntCached2 cntCached67 cntCached122 cntCached153 cntCached163 cntCached167
private def cntCached169 : T6 := .node cntCached3 cntCached68 cntCached123 cntCached154 cntCached164 cntCached168
private def cntCached170 : T6 := .leaf 145
private def cntCached171 : T6 := .leaf 165
private def cntCached172 : T6 := .node cntCached0 cntCached69 cntCached124 cntCached155 cntCached170 cntCached171
private def cntCached173 : T6 := .leaf 185
private def cntCached174 : T6 := .node cntCached0 cntCached70 cntCached125 cntCached156 cntCached171 cntCached173
private def cntCached175 : T6 := .node cntCached1 cntCached71 cntCached126 cntCached157 cntCached172 cntCached174
private def cntCached176 : T6 := .leaf 205
private def cntCached177 : T6 := .node cntCached0 cntCached72 cntCached127 cntCached158 cntCached173 cntCached176
private def cntCached178 : T6 := .node cntCached1 cntCached73 cntCached128 cntCached159 cntCached174 cntCached177
private def cntCached179 : T6 := .node cntCached2 cntCached74 cntCached129 cntCached160 cntCached175 cntCached178
private def cntCached180 : T6 := .leaf 225
private def cntCached181 : T6 := .node cntCached0 cntCached75 cntCached130 cntCached161 cntCached176 cntCached180
private def cntCached182 : T6 := .node cntCached1 cntCached76 cntCached131 cntCached162 cntCached177 cntCached181
private def cntCached183 : T6 := .node cntCached2 cntCached77 cntCached132 cntCached163 cntCached178 cntCached182
private def cntCached184 : T6 := .node cntCached3 cntCached78 cntCached133 cntCached164 cntCached179 cntCached183
private def cntCached185 : T6 := .leaf 245
private def cntCached186 : T6 := .node cntCached0 cntCached79 cntCached134 cntCached165 cntCached180 cntCached185
private def cntCached187 : T6 := .node cntCached1 cntCached80 cntCached135 cntCached166 cntCached181 cntCached186
private def cntCached188 : T6 := .node cntCached2 cntCached81 cntCached136 cntCached167 cntCached182 cntCached187
private def cntCached189 : T6 := .node cntCached3 cntCached82 cntCached137 cntCached168 cntCached183 cntCached188
private def cntCached190 : T6 := .node cntCached4 cntCached83 cntCached138 cntCached169 cntCached184 cntCached189
private def cntCached191 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached30
private def cntCached192 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached11 cntCached21
private def cntCached193 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached11 cntCached18 cntCached53
private def cntCached194 : T6 := .leaf 25
private def cntCached195 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached53 cntCached194
private def cntCached196 : T6 := .node cntCached1 cntCached7 cntCached191 cntCached192 cntCached193 cntCached195
private def cntCached197 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached18 cntCached87
private def cntCached198 : T6 := .leaf 29
private def cntCached199 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached32 cntCached26 cntCached198
private def cntCached200 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached198 cntCached69
private def cntCached201 : T6 := .node cntCached1 cntCached31 cntCached192 cntCached197 cntCached199 cntCached200
private def cntCached202 : T6 := .leaf 7
private def cntCached203 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached11 cntCached202
private def cntCached204 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached32 cntCached43
private def cntCached205 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached202 cntCached53 cntCached60
private def cntCached206 : T6 := .leaf 41
private def cntCached207 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached43 cntCached198 cntCached206
private def cntCached208 : T6 := .leaf 53
private def cntCached209 : T6 := .node cntCached0 cntCached16 cntCached38 cntCached89 cntCached206 cntCached208
private def cntCached210 : T6 := .node cntCached1 cntCached203 cntCached204 cntCached205 cntCached207 cntCached209
private def cntCached211 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached202 cntCached85
private def cntCached212 : T6 := .leaf 24
private def cntCached213 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached43 cntCached212
private def cntCached214 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached53 cntCached60 cntCached139
private def cntCached215 : T6 := .leaf 38
private def cntCached216 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached215 cntCached208 cntCached112
private def cntCached217 : T6 := .node cntCached1 cntCached211 cntCached213 cntCached214 cntCached209 cntCached216
private def cntCached218 : T6 := .node cntCached2 cntCached36 cntCached196 cntCached201 cntCached210 cntCached217
private def cntCached219 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached34
private def cntCached220 : T6 := .leaf 22
private def cntCached221 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached32 cntCached220
private def cntCached222 : T6 := .leaf 36
private def cntCached223 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached18 cntCached40 cntCached222
private def cntCached224 : T6 := .leaf 13
private def cntCached225 : T6 := .node cntCached0 cntCached13 cntCached224 cntCached44 cntCached222 cntCached110
private def cntCached226 : T6 := .node cntCached1 cntCached191 cntCached219 cntCached221 cntCached223 cntCached225
private def cntCached227 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached11 cntCached26 cntCached222
private def cntCached228 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached26 cntCached49 cntCached115
private def cntCached229 : T6 := .leaf 75
private def cntCached230 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached222 cntCached115 cntCached229
private def cntCached231 : T6 := .node cntCached1 cntCached192 cntCached221 cntCached227 cntCached228 cntCached230
private def cntCached232 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached18 cntCached53
private def cntCached233 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached32 cntCached92 cntCached99
private def cntCached234 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached53 cntCached222 cntCached65
private def cntCached235 : T6 := .leaf 79
private def cntCached236 : T6 := .node cntCached0 cntCached32 cntCached92 cntCached222 cntCached102 cntCached235
private def cntCached237 : T6 := .leaf 99
private def cntCached238 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached65 cntCached235 cntCached237
private def cntCached239 : T6 := .node cntCached1 cntCached232 cntCached233 cntCached234 cntCached236 cntCached238
private def cntCached240 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached21 cntCached53 cntCached194
private def cntCached241 : T6 := .node cntCached0 cntCached30 cntCached224 cntCached220 cntCached99 cntCached70
private def cntCached242 : T6 := .leaf 74
private def cntCached243 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached99 cntCached65 cntCached242
private def cntCached244 : T6 := .leaf 119
private def cntCached245 : T6 := .node cntCached0 cntCached212 cntCached70 cntCached242 cntCached237 cntCached244
private def cntCached246 : T6 := .node cntCached1 cntCached240 cntCached241 cntCached243 cntCached238 cntCached245
private def cntCached247 : T6 := .node cntCached2 cntCached196 cntCached226 cntCached231 cntCached239 cntCached246
private def cntCached248 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached18 cntCached87 cntCached46
private def cntCached249 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached46 cntCached206
private def cntCached250 : T6 := .node cntCached1 cntCached31 cntCached192 cntCached197 cntCached248 cntCached249
private def cntCached251 : T6 := .leaf 57
private def cntCached252 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached215 cntCached251
private def cntCached253 : T6 := .leaf 76
private def cntCached254 : T6 := .node cntCached0 cntCached85 cntCached44 cntCached49 cntCached251 cntCached253
private def cntCached255 : T6 := .node cntCached1 cntCached192 cntCached221 cntCached227 cntCached252 cntCached254
private def cntCached256 : T6 := .node cntCached0 cntCached8 cntCached11 cntCached34 cntCached99 cntCached251
private def cntCached257 : T6 := .leaf 62
private def cntCached258 : T6 := .leaf 85
private def cntCached259 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached99 cntCached257 cntCached258
private def cntCached260 : T6 := .leaf 108
private def cntCached261 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached251 cntCached258 cntCached260
private def cntCached262 : T6 := .node cntCached1 cntCached197 cntCached227 cntCached256 cntCached259 cntCached261
private def cntCached263 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached87 cntCached46
private def cntCached264 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached49 cntCached115
private def cntCached265 : T6 := .leaf 84
private def cntCached266 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached57 cntCached141 cntCached265
private def cntCached267 : T6 := .leaf 92
private def cntCached268 : T6 := .leaf 116
private def cntCached269 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached141 cntCached267 cntCached268
private def cntCached270 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached265 cntCached268 cntCached151
private def cntCached271 : T6 := .node cntCached1 cntCached263 cntCached264 cntCached266 cntCached269 cntCached270
private def cntCached272 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached87 cntCached46 cntCached206
private def cntCached273 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached222 cntCached115 cntCached229
private def cntCached274 : T6 := .leaf 107
private def cntCached275 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached115 cntCached265 cntCached274
private def cntCached276 : T6 := .leaf 164
private def cntCached277 : T6 := .node cntCached0 cntCached69 cntCached229 cntCached274 cntCached151 cntCached276
private def cntCached278 : T6 := .node cntCached1 cntCached272 cntCached273 cntCached275 cntCached270 cntCached277
private def cntCached279 : T6 := .node cntCached2 cntCached250 cntCached255 cntCached262 cntCached271 cntCached278
private def cntCached280 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached21 cntCached26
private def cntCached281 : T6 := .leaf 31
private def cntCached282 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached92 cntCached281
private def cntCached283 : T6 := .leaf 33
private def cntCached284 : T6 := .leaf 45
private def cntCached285 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached92 cntCached283 cntCached284
private def cntCached286 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached281 cntCached284 cntCached251
private def cntCached287 : T6 := .node cntCached1 cntCached33 cntCached280 cntCached282 cntCached285 cntCached286
private def cntCached288 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached18 cntCached40 cntCached222
private def cntCached289 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached87 cntCached215 cntCached251
private def cntCached290 : T6 := .leaf 82
private def cntCached291 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached139 cntCached257 cntCached290
private def cntCached292 : T6 := .leaf 58
private def cntCached293 : T6 := .leaf 102
private def cntCached294 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached292 cntCached290 cntCached293
private def cntCached295 : T6 := .node cntCached1 cntCached193 cntCached288 cntCached289 cntCached291 cntCached294
private def cntCached296 : T6 := .leaf 63
private def cntCached297 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached222 cntCached296 cntCached117
private def cntCached298 : T6 := .leaf 118
private def cntCached299 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached296 cntCached125 cntCached298
private def cntCached300 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached117 cntCached298 cntCached134
private def cntCached301 : T6 := .node cntCached1 cntCached248 cntCached289 cntCached297 cntCached299 cntCached300
private def cntCached302 : T6 := .leaf 44
private def cntCached303 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached94 cntCached302
private def cntCached304 : T6 := .leaf 81
private def cntCached305 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached215 cntCached141 cntCached304
private def cntCached306 : T6 := .leaf 93
private def cntCached307 : T6 := .leaf 117
private def cntCached308 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached257 cntCached306 cntCached307
private def cntCached309 : T6 := .leaf 128
private def cntCached310 : T6 := .leaf 153
private def cntCached311 : T6 := .node cntCached0 cntCached281 cntCached141 cntCached306 cntCached309 cntCached310
private def cntCached312 : T6 := .leaf 178
private def cntCached313 : T6 := .node cntCached0 cntCached96 cntCached304 cntCached307 cntCached310 cntCached312
private def cntCached314 : T6 := .node cntCached1 cntCached303 cntCached305 cntCached308 cntCached311 cntCached313
private def cntCached315 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached46 cntCached302 cntCached115
private def cntCached316 : T6 := .node cntCached0 cntCached53 cntCached49 cntCached251 cntCached304 cntCached120
private def cntCached317 : T6 := .leaf 141
private def cntCached318 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached258 cntCached307 cntCached317
private def cntCached319 : T6 := .leaf 203
private def cntCached320 : T6 := .node cntCached0 cntCached65 cntCached120 cntCached317 cntCached312 cntCached319
private def cntCached321 : T6 := .node cntCached1 cntCached315 cntCached316 cntCached318 cntCached313 cntCached320
private def cntCached322 : T6 := .node cntCached2 cntCached287 cntCached295 cntCached301 cntCached314 cntCached321
private def cntCached323 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached85 cntCached26 cntCached55
private def cntCached324 : T6 := .leaf 42
private def cntCached325 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached92 cntCached281 cntCached324
private def cntCached326 : T6 := .leaf 69
private def cntCached327 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached324 cntCached251 cntCached326
private def cntCached328 : T6 := .node cntCached1 cntCached35 cntCached323 cntCached325 cntCached286 cntCached327
private def cntCached329 : T6 := .node cntCached0 cntCached30 cntCached224 cntCached44 cntCached222 cntCached110
private def cntCached330 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached49 cntCached251 cntCached253
private def cntCached331 : T6 := .leaf 52
private def cntCached332 : T6 := .leaf 77
private def cntCached333 : T6 := .node cntCached0 cntCached55 cntCached331 cntCached332 cntCached293 cntCached148
private def cntCached334 : T6 := .node cntCached1 cntCached195 cntCached329 cntCached330 cntCached294 cntCached333
private def cntCached335 : T6 := .leaf 109
private def cntCached336 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached292 cntCached117 cntCached335
private def cntCached337 : T6 := .leaf 166
private def cntCached338 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached335 cntCached134 cntCached337
private def cntCached339 : T6 := .node cntCached1 cntCached249 cntCached330 cntCached336 cntCached300 cntCached338
private def cntCached340 : T6 := .leaf 68
private def cntCached341 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached206 cntCached115 cntCached340
private def cntCached342 : T6 := .leaf 121
private def cntCached343 : T6 := .node cntCached0 cntCached194 cntCached331 cntCached253 cntCached120 cntCached342
private def cntCached344 : T6 := .node cntCached0 cntCached69 cntCached253 cntCached260 cntCached317 cntCached171
private def cntCached345 : T6 := .leaf 67
private def cntCached346 : T6 := .leaf 228
private def cntCached347 : T6 := .node cntCached0 cntCached345 cntCached342 cntCached171 cntCached319 cntCached346
private def cntCached348 : T6 := .node cntCached1 cntCached341 cntCached343 cntCached344 cntCached320 cntCached347
private def cntCached349 : T6 := .node cntCached2 cntCached328 cntCached334 cntCached339 cntCached321 cntCached348
private def cntCached350 : T6 := .node cntCached3 cntCached218 cntCached247 cntCached279 cntCached322 cntCached349
private def cntCached351 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached11
private def cntCached352 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached18
private def cntCached353 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached32 cntCached26
private def cntCached354 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached18 cntCached26 cntCached198
private def cntCached355 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached198 cntCached69
private def cntCached356 : T6 := .node cntCached1 cntCached351 cntCached352 cntCached353 cntCached354 cntCached355
private def cntCached357 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached202
private def cntCached358 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached202 cntCached53
private def cntCached359 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached16 cntCached53 cntCached46
private def cntCached360 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached53 cntCached281 cntCached284
private def cntCached361 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached46 cntCached284 cntCached102
private def cntCached362 : T6 := .node cntCached1 cntCached357 cntCached358 cntCached359 cntCached360 cntCached361
private def cntCached363 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached8 cntCached16 cntCached34
private def cntCached364 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached202 cntCached43 cntCached89
private def cntCached365 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached43 cntCached46 cntCached302
private def cntCached366 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached46 cntCached100 cntCached257
private def cntCached367 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached302 cntCached257 cntCached332
private def cntCached368 : T6 := .node cntCached1 cntCached363 cntCached364 cntCached365 cntCached366 cntCached367
private def cntCached369 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached202 cntCached34 cntCached26
private def cntCached370 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached89 cntCached215
private def cntCached371 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached198 cntCached302 cntCached292
private def cntCached372 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached292 cntCached332 cntCached267
private def cntCached373 : T6 := .node cntCached1 cntCached369 cntCached370 cntCached371 cntCached367 cntCached372
private def cntCached374 : T6 := .node cntCached2 cntCached42 cntCached356 cntCached362 cntCached368 cntCached373
private def cntCached375 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached202 cntCached40
private def cntCached376 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached11 cntCached53 cntCached99
private def cntCached377 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached26 cntCached222 cntCached65
private def cntCached378 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached222 cntCached65 cntCached242
private def cntCached379 : T6 := .node cntCached1 cntCached352 cntCached375 cntCached376 cntCached377 cntCached378
private def cntCached380 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached43 cntCached57
private def cntCached381 : T6 := .leaf 54
private def cntCached382 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached21 cntCached94 cntCached381
private def cntCached383 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached94 cntCached292 cntCached304
private def cntCached384 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached381 cntCached304 cntCached146
private def cntCached385 : T6 := .node cntCached1 cntCached358 cntCached380 cntCached382 cntCached383 cntCached384
private def cntCached386 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached32 cntCached53 cntCached60
private def cntCached387 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached53 cntCached99 cntCached381
private def cntCached388 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached94 cntCached292 cntCached304
private def cntCached389 : T6 := .leaf 88
private def cntCached390 : T6 := .leaf 112
private def cntCached391 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached292 cntCached389 cntCached390
private def cntCached392 : T6 := .leaf 136
private def cntCached393 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached304 cntCached390 cntCached392
private def cntCached394 : T6 := .node cntCached1 cntCached386 cntCached387 cntCached388 cntCached391 cntCached393
private def cntCached395 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached26 cntCached60 cntCached139
private def cntCached396 : T6 := .leaf 73
private def cntCached397 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached99 cntCached381 cntCached396
private def cntCached398 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached381 cntCached304 cntCached146
private def cntCached399 : T6 := .leaf 160
private def cntCached400 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached146 cntCached392 cntCached399
private def cntCached401 : T6 := .node cntCached1 cntCached395 cntCached397 cntCached398 cntCached393 cntCached400
private def cntCached402 : T6 := .node cntCached2 cntCached201 cntCached379 cntCached385 cntCached394 cntCached401
private def cntCached403 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached202 cntCached87 cntCached94
private def cntCached404 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached26 cntCached283 cntCached100
private def cntCached405 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached281 cntCached100 cntCached141
private def cntCached406 : T6 := .node cntCached1 cntCached37 cntCached197 cntCached403 cntCached404 cntCached405
private def cntCached407 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached85 cntCached283 cntCached65
private def cntCached408 : T6 := .leaf 83
private def cntCached409 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached57 cntCached72 cntCached408
private def cntCached410 : T6 := .leaf 106
private def cntCached411 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached115 cntCached408 cntCached410
private def cntCached412 : T6 := .node cntCached1 cntCached353 cntCached376 cntCached407 cntCached409 cntCached411
private def cntCached413 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached202 cntCached26 cntCached281
private def cntCached414 : T6 := .node cntCached0 cntCached8 cntCached11 cntCached85 cntCached283 cntCached65
private def cntCached415 : T6 := .node cntCached0 cntCached16 cntCached21 cntCached89 cntCached292 cntCached265
private def cntCached416 : T6 := .leaf 120
private def cntCached417 : T6 := .node cntCached0 cntCached53 cntCached94 cntCached292 cntCached306 cntCached416
private def cntCached418 : T6 := .leaf 147
private def cntCached419 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached265 cntCached416 cntCached418
private def cntCached420 : T6 := .node cntCached1 cntCached413 cntCached414 cntCached415 cntCached417 cntCached419
private def cntCached421 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached283 cntCached100
private def cntCached422 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached57 cntCached72 cntCached408
private def cntCached423 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached292 cntCached306 cntCached416
private def cntCached424 : T6 := .leaf 132
private def cntCached425 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached306 cntCached424 cntCached399
private def cntCached426 : T6 := .leaf 188
private def cntCached427 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached416 cntCached399 cntCached426
private def cntCached428 : T6 := .node cntCached1 cntCached421 cntCached422 cntCached423 cntCached425 cntCached427
private def cntCached429 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached94 cntCached100 cntCached141
private def cntCached430 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached115 cntCached408 cntCached410
private def cntCached431 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached265 cntCached416 cntCached418
private def cntCached432 : T6 := .leaf 105
private def cntCached433 : T6 := .leaf 216
private def cntCached434 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached418 cntCached426 cntCached433
private def cntCached435 : T6 := .node cntCached1 cntCached429 cntCached430 cntCached431 cntCached427 cntCached434
private def cntCached436 : T6 := .node cntCached2 cntCached406 cntCached412 cntCached420 cntCached428 cntCached435
private def cntCached437 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached18 cntCached87 cntCached46
private def cntCached438 : T6 := .leaf 48
private def cntCached439 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached87 cntCached57 cntCached438
private def cntCached440 : T6 := .leaf 66
private def cntCached441 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached283 cntCached110 cntCached440
private def cntCached442 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached100 cntCached440 cntCached304
private def cntCached443 : T6 := .node cntCached1 cntCached39 cntCached437 cntCached439 cntCached441 cntCached442
private def cntCached444 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached26 cntCached222 cntCached65
private def cntCached445 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached57 cntCached72 cntCached408
private def cntCached446 : T6 := .leaf 91
private def cntCached447 : T6 := .leaf 115
private def cntCached448 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached141 cntCached446 cntCached447
private def cntCached449 : T6 := .leaf 139
private def cntCached450 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached265 cntCached447 cntCached449
private def cntCached451 : T6 := .node cntCached1 cntCached354 cntCached444 cntCached445 cntCached448 cntCached450
private def cntCached452 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached283 cntCached100
private def cntCached453 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached57 cntCached72 cntCached408
private def cntCached454 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached102 cntCached125 cntCached342
private def cntCached455 : T6 := .leaf 161
private def cntCached456 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached125 cntCached156 cntCached455
private def cntCached457 : T6 := .leaf 189
private def cntCached458 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached342 cntCached455 cntCached457
private def cntCached459 : T6 := .node cntCached1 cntCached452 cntCached453 cntCached454 cntCached456 cntCached458
private def cntCached460 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached110 cntCached440
private def cntCached461 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached141 cntCached446 cntCached447
private def cntCached462 : T6 := .node cntCached0 cntCached281 cntCached72 cntCached125 cntCached156 cntCached455
private def cntCached463 : T6 := .leaf 90
private def cntCached464 : T6 := .leaf 176
private def cntCached465 : T6 := .node cntCached0 cntCached438 cntCached463 cntCached156 cntCached464 cntCached176
private def cntCached466 : T6 := .leaf 234
private def cntCached467 : T6 := .node cntCached0 cntCached296 cntCached155 cntCached455 cntCached176 cntCached466
private def cntCached468 : T6 := .node cntCached1 cntCached460 cntCached461 cntCached462 cntCached465 cntCached467
private def cntCached469 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached438 cntCached440 cntCached304
private def cntCached470 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached265 cntCached447 cntCached449
private def cntCached471 : T6 := .node cntCached0 cntCached284 cntCached408 cntCached342 cntCached455 cntCached457
private def cntCached472 : T6 := .leaf 138
private def cntCached473 : T6 := .leaf 263
private def cntCached474 : T6 := .node cntCached0 cntCached124 cntCached472 cntCached457 cntCached466 cntCached473
private def cntCached475 : T6 := .node cntCached1 cntCached469 cntCached470 cntCached471 cntCached467 cntCached474
private def cntCached476 : T6 := .node cntCached2 cntCached443 cntCached451 cntCached459 cntCached468 cntCached475
private def cntCached477 : T6 := .node cntCached0 cntCached11 cntCached21 cntCached87 cntCached46 cntCached206
private def cntCached478 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached94 cntCached438 cntCached257
private def cntCached479 : T6 := .leaf 96
private def cntCached480 : T6 := .node cntCached0 cntCached26 cntCached139 cntCached141 cntCached304 cntCached479
private def cntCached481 : T6 := .node cntCached1 cntCached41 cntCached477 cntCached478 cntCached442 cntCached480
private def cntCached482 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached222 cntCached65 cntCached242
private def cntCached483 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached115 cntCached408 cntCached410
private def cntCached484 : T6 := .leaf 163
private def cntCached485 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached274 cntCached449 cntCached484
private def cntCached486 : T6 := .node cntCached1 cntCached355 cntCached482 cntCached483 cntCached450 cntCached485
private def cntCached487 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached94 cntCached100 cntCached141
private def cntCached488 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached115 cntCached408 cntCached410
private def cntCached489 : T6 := .leaf 148
private def cntCached490 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached258 cntCached342 cntCached489
private def cntCached491 : T6 := .leaf 217
private def cntCached492 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached489 cntCached457 cntCached491
private def cntCached493 : T6 := .node cntCached1 cntCached487 cntCached488 cntCached490 cntCached458 cntCached492
private def cntCached494 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached257 cntCached304 cntCached479
private def cntCached495 : T6 := .node cntCached0 cntCached69 cntCached253 cntCached274 cntCached449 cntCached484
private def cntCached496 : T6 := .node cntCached0 cntCached102 cntCached410 cntCached489 cntCached457 cntCached491
private def cntCached497 : T6 := .leaf 162
private def cntCached498 : T6 := .leaf 292
private def cntCached499 : T6 := .node cntCached0 cntCached306 cntCached497 cntCached491 cntCached473 cntCached498
private def cntCached500 : T6 := .node cntCached1 cntCached494 cntCached495 cntCached496 cntCached474 cntCached499
private def cntCached501 : T6 := .node cntCached2 cntCached481 cntCached486 cntCached493 cntCached475 cntCached500
private def cntCached502 : T6 := .node cntCached3 cntCached374 cntCached402 cntCached436 cntCached476 cntCached501
private def cntCached503 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached16
private def cntCached504 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached32 cntCached43
private def cntCached505 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached26 cntCached198
private def cntCached506 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached281 cntCached96
private def cntCached507 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached46 cntCached96 cntCached65
private def cntCached508 : T6 := .node cntCached1 cntCached503 cntCached504 cntCached505 cntCached506 cntCached507
private def cntCached509 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached94 cntCached62
private def cntCached510 : T6 := .leaf 49
private def cntCached511 : T6 := .leaf 64
private def cntCached512 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached94 cntCached510 cntCached511
private def cntCached513 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached62 cntCached511 cntCached235
private def cntCached514 : T6 := .node cntCached1 cntCached363 cntCached386 cntCached509 cntCached512 cntCached513
private def cntCached515 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached16 cntCached34 cntCached87
private def cntCached516 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached198 cntCached206
private def cntCached517 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached281 cntCached438 cntCached296
private def cntCached518 : T6 := .node cntCached0 cntCached224 cntCached46 cntCached438 cntCached340 cntCached265
private def cntCached519 : T6 := .leaf 100
private def cntCached520 : T6 := .node cntCached0 cntCached92 cntCached324 cntCached296 cntCached265 cntCached519
private def cntCached521 : T6 := .node cntCached1 cntCached515 cntCached516 cntCached517 cntCached518 cntCached520
private def cntCached522 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached34 cntCached87 cntCached55
private def cntCached523 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached60 cntCached206 cntCached208
private def cntCached524 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached284 cntCached296 cntCached124
private def cntCached525 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached124 cntCached519 cntCached268
private def cntCached526 : T6 := .node cntCached1 cntCached522 cntCached523 cntCached524 cntCached520 cntCached525
private def cntCached527 : T6 := .node cntCached2 cntCached48 cntCached508 cntCached514 cntCached521 cntCached526
private def cntCached528 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached26 cntCached281 cntCached96
private def cntCached529 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached198 cntCached96 cntCached65
private def cntCached530 : T6 := .node cntCached1 cntCached33 cntCached193 cntCached248 cntCached528 cntCached529
private def cntCached531 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached202 cntCached38
private def cntCached532 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached202 cntCached26 cntCached283
private def cntCached533 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached53 cntCached99 cntCached381
private def cntCached534 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached222 cntCached292 cntCached124
private def cntCached535 : T6 := .leaf 98
private def cntCached536 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached65 cntCached124 cntCached535
private def cntCached537 : T6 := .node cntCached1 cntCached531 cntCached532 cntCached533 cntCached534 cntCached536
private def cntCached538 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached43 cntCached57 cntCached208
private def cntCached539 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached94 cntCached292 cntCached304
private def cntCached540 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached292 cntCached389 cntCached390
private def cntCached541 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached304 cntCached390 cntCached392
private def cntCached542 : T6 := .node cntCached1 cntCached364 cntCached538 cntCached539 cntCached540 cntCached541
private def cntCached543 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached99 cntCached251 cntCached332
private def cntCached544 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached292 cntCached389 cntCached390
private def cntCached545 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached389 cntCached148 cntCached418
private def cntCached546 : T6 := .leaf 172
private def cntCached547 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached390 cntCached418 cntCached546
private def cntCached548 : T6 := .node cntCached1 cntCached516 cntCached543 cntCached544 cntCached545 cntCached547
private def cntCached549 : T6 := .leaf 97
private def cntCached550 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached381 cntCached332 cntCached549
private def cntCached551 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached304 cntCached390 cntCached392
private def cntCached552 : T6 := .leaf 197
private def cntCached553 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached392 cntCached546 cntCached552
private def cntCached554 : T6 := .node cntCached1 cntCached523 cntCached550 cntCached551 cntCached547 cntCached553
private def cntCached555 : T6 := .node cntCached2 cntCached530 cntCached537 cntCached542 cntCached548 cntCached554
private def cntCached556 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached94 cntCached70 cntCached112
private def cntCached557 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached62 cntCached112 cntCached79
private def cntCached558 : T6 := .node cntCached1 cntCached39 cntCached199 cntCached404 cntCached556 cntCached557
private def cntCached559 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached32 cntCached53 cntCached60
private def cntCached560 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached43 cntCached57 cntCached208
private def cntCached561 : T6 := .leaf 89
private def cntCached562 : T6 := .leaf 113
private def cntCached563 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached102 cntCached561 cntCached562
private def cntCached564 : T6 := .leaf 137
private def cntCached565 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached290 cntCached562 cntCached564
private def cntCached566 : T6 := .node cntCached1 cntCached559 cntCached560 cntCached383 cntCached563 cntCached565
private def cntCached567 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached94 cntCached62
private def cntCached568 : T6 := .node cntCached0 cntCached53 cntCached94 cntCached251 cntCached267 cntCached244
private def cntCached569 : T6 := .leaf 131
private def cntCached570 : T6 := .leaf 159
private def cntCached571 : T6 := .node cntCached0 cntCached281 cntCached292 cntCached267 cntCached569 cntCached570
private def cntCached572 : T6 := .leaf 187
private def cntCached573 : T6 := .node cntCached0 cntCached284 cntCached304 cntCached244 cntCached570 cntCached572
private def cntCached574 : T6 := .node cntCached1 cntCached567 cntCached539 cntCached568 cntCached571 cntCached573
private def cntCached575 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached283 cntCached70 cntCached112
private def cntCached576 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached102 cntCached561 cntCached562
private def cntCached577 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached267 cntCached569 cntCached570
private def cntCached578 : T6 := .leaf 174
private def cntCached579 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached569 cntCached578 cntCached319
private def cntCached580 : T6 := .leaf 232
private def cntCached581 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached570 cntCached319 cntCached580
private def cntCached582 : T6 := .node cntCached1 cntCached575 cntCached576 cntCached577 cntCached579 cntCached581
private def cntCached583 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached100 cntCached112 cntCached79
private def cntCached584 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached290 cntCached562 cntCached564
private def cntCached585 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached244 cntCached570 cntCached572
private def cntCached586 : T6 := .leaf 261
private def cntCached587 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached572 cntCached580 cntCached586
private def cntCached588 : T6 := .node cntCached1 cntCached583 cntCached584 cntCached585 cntCached581 cntCached587
private def cntCached589 : T6 := .node cntCached2 cntCached558 cntCached566 cntCached574 cntCached582 cntCached588
private def cntCached590 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached26 cntCached281 cntCached96
private def cntCached591 : T6 := .leaf 87
private def cntCached592 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached70 cntCached105 cntCached591
private def cntCached593 : T6 := .leaf 103
private def cntCached594 : T6 := .node cntCached0 cntCached87 cntCached206 cntCached112 cntCached591 cntCached593
private def cntCached595 : T6 := .node cntCached1 cntCached45 cntCached590 cntCached441 cntCached592 cntCached594
private def cntCached596 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached46 cntCached324
private def cntCached597 : T6 := .node cntCached0 cntCached202 cntCached87 cntCached99 cntCached251 cntCached332
private def cntCached598 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached102 cntCached561 cntCached562
private def cntCached599 : T6 := .leaf 124
private def cntCached600 : T6 := .leaf 149
private def cntCached601 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached463 cntCached599 cntCached600
private def cntCached602 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached155 cntCached600 cntCached578
private def cntCached603 : T6 := .node cntCached1 cntCached596 cntCached597 cntCached598 cntCached601 cntCached602
private def cntCached604 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached283 cntCached70 cntCached112
private def cntCached605 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached102 cntCached561 cntCached562
private def cntCached606 : T6 := .leaf 175
private def cntCached607 : T6 := .leaf 204
private def cntCached608 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached424 cntCached606 cntCached607
private def cntCached609 : T6 := .leaf 233
private def cntCached610 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached399 cntCached607 cntCached609
private def cntCached611 : T6 := .node cntCached1 cntCached604 cntCached605 cntCached425 cntCached608 cntCached610
private def cntCached612 : T6 := .node cntCached0 cntCached43 cntCached283 cntCached110 cntCached105 cntCached591
private def cntCached613 : T6 := .node cntCached0 cntCached46 cntCached72 cntCached463 cntCached599 cntCached600
private def cntCached614 : T6 := .node cntCached0 cntCached438 cntCached463 cntCached424 cntCached606 cntCached607
private def cntCached615 : T6 := .leaf 222
private def cntCached616 : T6 := .leaf 252
private def cntCached617 : T6 := .node cntCached0 cntCached340 cntCached599 cntCached606 cntCached615 cntCached616
private def cntCached618 : T6 := .leaf 282
private def cntCached619 : T6 := .node cntCached0 cntCached265 cntCached600 cntCached607 cntCached616 cntCached618
private def cntCached620 : T6 := .node cntCached1 cntCached612 cntCached613 cntCached614 cntCached617 cntCached619
private def cntCached621 : T6 := .node cntCached0 cntCached44 cntCached284 cntCached440 cntCached591 cntCached593
private def cntCached622 : T6 := .node cntCached0 cntCached324 cntCached79 cntCached155 cntCached600 cntCached578
private def cntCached623 : T6 := .node cntCached0 cntCached296 cntCached155 cntCached399 cntCached607 cntCached609
private def cntCached624 : T6 := .leaf 312
private def cntCached625 : T6 := .node cntCached0 cntCached519 cntCached578 cntCached609 cntCached618 cntCached624
private def cntCached626 : T6 := .node cntCached1 cntCached621 cntCached622 cntCached623 cntCached619 cntCached625
private def cntCached627 : T6 := .node cntCached2 cntCached595 cntCached603 cntCached611 cntCached620 cntCached626
private def cntCached628 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached198 cntCached96 cntCached65
private def cntCached629 : T6 := .node cntCached0 cntCached55 cntCached208 cntCached79 cntCached593 cntCached244
private def cntCached630 : T6 := .node cntCached1 cntCached47 cntCached628 cntCached442 cntCached594 cntCached629
private def cntCached631 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached198 cntCached324 cntCached381
private def cntCached632 : T6 := .node cntCached0 cntCached38 cntCached57 cntCached381 cntCached332 cntCached549
private def cntCached633 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached290 cntCached562 cntCached564
private def cntCached634 : T6 := .leaf 199
private def cntCached635 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached472 cntCached578 cntCached634
private def cntCached636 : T6 := .node cntCached1 cntCached631 cntCached632 cntCached633 cntCached602 cntCached635
private def cntCached637 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached100 cntCached112 cntCached79
private def cntCached638 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached290 cntCached562 cntCached564
private def cntCached639 : T6 := .leaf 262
private def cntCached640 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached426 cntCached609 cntCached639
private def cntCached641 : T6 := .node cntCached1 cntCached637 cntCached638 cntCached427 cntCached610 cntCached640
private def cntCached642 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached304 cntCached593 cntCached244
private def cntCached643 : T6 := .node cntCached0 cntCached381 cntCached519 cntCached472 cntCached578 cntCached634
private def cntCached644 : T6 := .node cntCached0 cntCached124 cntCached472 cntCached426 cntCached609 cntCached639
private def cntCached645 : T6 := .leaf 342
private def cntCached646 : T6 := .node cntCached0 cntCached268 cntCached634 cntCached639 cntCached624 cntCached645
private def cntCached647 : T6 := .node cntCached1 cntCached642 cntCached643 cntCached644 cntCached625 cntCached646
private def cntCached648 : T6 := .node cntCached2 cntCached630 cntCached636 cntCached641 cntCached626 cntCached647
private def cntCached649 : T6 := .node cntCached3 cntCached527 cntCached555 cntCached589 cntCached627 cntCached648
private def cntCached650 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached21 cntCached43 cntCached212
private def cntCached651 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached87 cntCached198 cntCached69
private def cntCached652 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached206 cntCached65 cntCached345
private def cntCached653 : T6 := .node cntCached1 cntCached22 cntCached650 cntCached651 cntCached507 cntCached652
private def cntCached654 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached281 cntCached62 cntCached72
private def cntCached655 : T6 := .node cntCached0 cntCached87 cntCached69 cntCached72 cntCached235 cntCached125
private def cntCached656 : T6 := .node cntCached1 cntCached369 cntCached395 cntCached654 cntCached513 cntCached655
private def cntCached657 : T6 := .node cntCached0 cntCached13 cntCached34 cntCached26 cntCached55 cntCached283
private def cntCached658 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached139 cntCached208 cntCached112
private def cntCached659 : T6 := .node cntCached0 cntCached87 cntCached69 cntCached102 cntCached124 cntCached306
private def cntCached660 : T6 := .node cntCached0 cntCached57 cntCached440 cntCached306 cntCached268 cntCached424
private def cntCached661 : T6 := .node cntCached1 cntCached657 cntCached658 cntCached659 cntCached525 cntCached660
private def cntCached662 : T6 := .node cntCached2 cntCached51 cntCached653 cntCached656 cntCached526 cntCached661
private def cntCached663 : T6 := .node cntCached0 cntCached85 cntCached212 cntCached69 cntCached65 cntCached345
private def cntCached664 : T6 := .node cntCached1 cntCached35 cntCached195 cntCached249 cntCached529 cntCached663
private def cntCached665 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached38 cntCached44
private def cntCached666 : T6 := .node cntCached0 cntCached30 cntCached34 cntCached40 cntCached283 cntCached438
private def cntCached667 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached99 cntCached381 cntCached396
private def cntCached668 : T6 := .node cntCached0 cntCached194 cntCached70 cntCached242 cntCached535 cntCached298
private def cntCached669 : T6 := .node cntCached1 cntCached665 cntCached666 cntCached667 cntCached536 cntCached668
private def cntCached670 : T6 := .leaf 72
private def cntCached671 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached57 cntCached208 cntCached670
private def cntCached672 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached381 cntCached304 cntCached146
private def cntCached673 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached146 cntCached392 cntCached399
private def cntCached674 : T6 := .node cntCached1 cntCached370 cntCached671 cntCached672 cntCached541 cntCached673
private def cntCached675 : T6 := .node cntCached0 cntCached194 cntCached110 cntCached396 cntCached549 cntCached307
private def cntCached676 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached146 cntCached392 cntCached399
private def cntCached677 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached399 cntCached552 cntCached615
private def cntCached678 : T6 := .node cntCached1 cntCached658 cntCached675 cntCached676 cntCached553 cntCached677
private def cntCached679 : T6 := .node cntCached2 cntCached664 cntCached669 cntCached674 cntCached554 cntCached678
private def cntCached680 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached72 cntCached79 cntCached143
private def cntCached681 : T6 := .node cntCached1 cntCached41 cntCached200 cntCached405 cntCached557 cntCached680
private def cntCached682 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached26 cntCached60 cntCached139
private def cntCached683 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached57 cntCached208 cntCached670
private def cntCached684 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached432 cntCached564 cntCached455
private def cntCached685 : T6 := .node cntCached1 cntCached682 cntCached683 cntCached384 cntCached565 cntCached684
private def cntCached686 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached281 cntCached62 cntCached72
private def cntCached687 : T6 := .leaf 146
private def cntCached688 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached408 cntCached244 cntCached687
private def cntCached689 : T6 := .leaf 215
private def cntCached690 : T6 := .node cntCached0 cntCached102 cntCached146 cntCached687 cntCached572 cntCached689
private def cntCached691 : T6 := .node cntCached1 cntCached686 cntCached672 cntCached688 cntCached573 cntCached690
private def cntCached692 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached141 cntCached79 cntCached143
private def cntCached693 : T6 := .node cntCached0 cntCached69 cntCached229 cntCached432 cntCached564 cntCached455
private def cntCached694 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached687 cntCached572 cntCached689
private def cntCached695 : T6 := .leaf 290
private def cntCached696 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached689 cntCached586 cntCached695
private def cntCached697 : T6 := .node cntCached1 cntCached692 cntCached693 cntCached694 cntCached587 cntCached696
private def cntCached698 : T6 := .node cntCached2 cntCached681 cntCached685 cntCached691 cntCached588 cntCached697
private def cntCached699 : T6 := .node cntCached0 cntCached21 cntCached212 cntCached69 cntCached65 cntCached345
private def cntCached700 : T6 := .leaf 135
private def cntCached701 : T6 := .node cntCached0 cntCached283 cntCached112 cntCached143 cntCached244 cntCached700
private def cntCached702 : T6 := .node cntCached1 cntCached50 cntCached699 cntCached480 cntCached629 cntCached701
private def cntCached703 : T6 := .node cntCached0 cntCached34 cntCached194 cntCached69 cntCached381 cntCached440
private def cntCached704 : T6 := .node cntCached0 cntCached44 cntCached510 cntCached396 cntCached549 cntCached307
private def cntCached705 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached432 cntCached564 cntCached455
private def cntCached706 : T6 := .leaf 224
private def cntCached707 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached497 cntCached634 cntCached706
private def cntCached708 : T6 := .node cntCached1 cntCached703 cntCached704 cntCached705 cntCached635 cntCached707
private def cntCached709 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached141 cntCached79 cntCached143
private def cntCached710 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached432 cntCached564 cntCached455
private def cntCached711 : T6 := .leaf 291
private def cntCached712 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached433 cntCached639 cntCached711
private def cntCached713 : T6 := .node cntCached1 cntCached709 cntCached710 cntCached434 cntCached640 cntCached712
private def cntCached714 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached479 cntCached244 cntCached700
private def cntCached715 : T6 := .node cntCached0 cntCached440 cntCached416 cntCached497 cntCached634 cntCached706
private def cntCached716 : T6 := .node cntCached0 cntCached306 cntCached497 cntCached433 cntCached639 cntCached711
private def cntCached717 : T6 := .leaf 372
private def cntCached718 : T6 := .node cntCached0 cntCached424 cntCached706 cntCached711 cntCached645 cntCached717
private def cntCached719 : T6 := .node cntCached1 cntCached714 cntCached715 cntCached716 cntCached646 cntCached718
private def cntCached720 : T6 := .node cntCached2 cntCached702 cntCached708 cntCached713 cntCached647 cntCached719
private def cntCached721 : T6 := .node cntCached3 cntCached662 cntCached679 cntCached698 cntCached648 cntCached720
private def cntCached722 : T6 := .node cntCached4 cntCached138 cntCached350 cntCached502 cntCached649 cntCached721
private def cntCached723 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached16 cntCached38 cntCached55
private def cntCached724 : T6 := .node cntCached0 cntCached6 cntCached16 cntCached38 cntCached198 cntCached96
private def cntCached725 : T6 := .node cntCached0 cntCached13 cntCached38 cntCached198 cntCached62 cntCached141
private def cntCached726 : T6 := .node cntCached0 cntCached85 cntCached55 cntCached96 cntCached141 cntCached253
private def cntCached727 : T6 := .node cntCached1 cntCached363 cntCached723 cntCached724 cntCached725 cntCached726
private def cntCached728 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached43 cntCached55 cntCached49
private def cntCached729 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached60 cntCached96 cntCached251
private def cntCached730 : T6 := .node cntCached0 cntCached53 cntCached49 cntCached251 cntCached253 cntCached446
private def cntCached731 : T6 := .node cntCached1 cntCached369 cntCached728 cntCached729 cntCached726 cntCached730
private def cntCached732 : T6 := .node cntCached2 cntCached42 cntCached356 cntCached362 cntCached727 cntCached731
private def cntCached733 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached49 cntCached115
private def cntCached734 : T6 := .node cntCached0 cntCached85 cntCached44 cntCached49 cntCached115 cntCached229
private def cntCached735 : T6 := .node cntCached1 cntCached352 cntCached375 cntCached376 cntCached733 cntCached734
private def cntCached736 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached283 cntCached102 cntCached290
private def cntCached737 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached65 cntCached290 cntCached432
private def cntCached738 : T6 := .node cntCached1 cntCached358 cntCached380 cntCached382 cntCached736 cntCached737
private def cntCached739 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached43 cntCached57 cntCached208
private def cntCached740 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached281 cntCached251 cntCached79
private def cntCached741 : T6 := .node cntCached1 cntCached386 cntCached739 cntCached740 cntCached391 cntCached393
private def cntCached742 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached57 cntCached208 cntCached670
private def cntCached743 : T6 := .node cntCached0 cntCached43 cntCached57 cntCached208 cntCached79 cntCached593
private def cntCached744 : T6 := .node cntCached1 cntCached395 cntCached742 cntCached743 cntCached393 cntCached400
private def cntCached745 : T6 := .node cntCached2 cntCached250 cntCached735 cntCached738 cntCached741 cntCached744
private def cntCached746 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached87 cntCached57 cntCached438
private def cntCached747 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached94 cntCached438 cntCached257
private def cntCached748 : T6 := .node cntCached1 cntCached37 cntCached197 cntCached403 cntCached746 cntCached747
private def cntCached749 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached99 cntCached141 cntCached265
private def cntCached750 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached251 cntCached265 cntCached274
private def cntCached751 : T6 := .node cntCached1 cntCached353 cntCached376 cntCached407 cntCached749 cntCached750
private def cntCached752 : T6 := .node cntCached0 cntCached26 cntCached283 cntCached102 cntCached125 cntCached342
private def cntCached753 : T6 := .node cntCached0 cntCached281 cntCached65 cntCached258 cntCached342 cntCached489
private def cntCached754 : T6 := .node cntCached1 cntCached413 cntCached414 cntCached415 cntCached752 cntCached753
private def cntCached755 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached283 cntCached102 cntCached290
private def cntCached756 : T6 := .node cntCached0 cntCached43 cntCached94 cntCached251 cntCached267 cntCached244
private def cntCached757 : T6 := .node cntCached1 cntCached421 cntCached755 cntCached756 cntCached425 cntCached427
private def cntCached758 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached65 cntCached290 cntCached432
private def cntCached759 : T6 := .node cntCached0 cntCached198 cntCached381 cntCached408 cntCached244 cntCached687
private def cntCached760 : T6 := .node cntCached1 cntCached429 cntCached758 cntCached759 cntCached427 cntCached434
private def cntCached761 : T6 := .node cntCached2 cntCached748 cntCached751 cntCached754 cntCached757 cntCached760
private def cntCached762 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached92 cntCached99 cntCached510
private def cntCached763 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached99 cntCached208 cntCached340
private def cntCached764 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached510 cntCached340 cntCached408
private def cntCached765 : T6 := .node cntCached1 cntCached39 cntCached282 cntCached762 cntCached763 cntCached764
private def cntCached766 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached87 cntCached49 cntCached115
private def cntCached767 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached99 cntCached141 cntCached265
private def cntCached768 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached296 cntCached306 cntCached307
private def cntCached769 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached117 cntCached307 cntCached317
private def cntCached770 : T6 := .node cntCached1 cntCached354 cntCached766 cntCached767 cntCached768 cntCached769
private def cntCached771 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached99 cntCached141 cntCached265
private def cntCached772 : T6 := .node cntCached0 cntCached26 cntCached57 cntCached72 cntCached143 cntCached148
private def cntCached773 : T6 := .node cntCached0 cntCached283 cntCached141 cntCached479 cntCached700 cntCached484
private def cntCached774 : T6 := .leaf 123
private def cntCached775 : T6 := .leaf 191
private def cntCached776 : T6 := .node cntCached0 cntCached100 cntCached265 cntCached774 cntCached484 cntCached775
private def cntCached777 : T6 := .node cntCached1 cntCached452 cntCached771 cntCached772 cntCached773 cntCached776
private def cntCached778 : T6 := .leaf 134
private def cntCached779 : T6 := .leaf 177
private def cntCached780 : T6 := .leaf 206
private def cntCached781 : T6 := .node cntCached0 cntCached510 cntCached446 cntCached778 cntCached779 cntCached780
private def cntCached782 : T6 := .leaf 235
private def cntCached783 : T6 := .node cntCached0 cntCached511 cntCached447 cntCached497 cntCached780 cntCached782
private def cntCached784 : T6 := .node cntCached1 cntCached460 cntCached461 cntCached462 cntCached781 cntCached783
private def cntCached785 : T6 := .leaf 264
private def cntCached786 : T6 := .node cntCached0 cntCached235 cntCached449 cntCached165 cntCached782 cntCached785
private def cntCached787 : T6 := .node cntCached1 cntCached469 cntCached470 cntCached471 cntCached783 cntCached786
private def cntCached788 : T6 := .node cntCached2 cntCached765 cntCached770 cntCached777 cntCached784 cntCached787
private def cntCached789 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached283 cntCached510 cntCached296
private def cntCached790 : T6 := .node cntCached0 cntCached92 cntCached206 cntCached296 cntCached408 cntCached535
private def cntCached791 : T6 := .node cntCached1 cntCached41 cntCached325 cntCached789 cntCached764 cntCached790
private def cntCached792 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached49 cntCached115 cntCached229
private def cntCached793 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached251 cntCached265 cntCached274
private def cntCached794 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached335 cntCached317 cntCached171
private def cntCached795 : T6 := .node cntCached1 cntCached355 cntCached792 cntCached793 cntCached769 cntCached794
private def cntCached796 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached251 cntCached265 cntCached274
private def cntCached797 : T6 := .node cntCached0 cntCached281 cntCached115 cntCached117 cntCached148 cntCached600
private def cntCached798 : T6 := .leaf 150
private def cntCached799 : T6 := .leaf 219
private def cntCached800 : T6 := .node cntCached0 cntCached141 cntCached274 cntCached798 cntCached775 cntCached799
private def cntCached801 : T6 := .node cntCached1 cntCached487 cntCached796 cntCached797 cntCached776 cntCached800
private def cntCached802 : T6 := .leaf 218
private def cntCached803 : T6 := .leaf 293
private def cntCached804 : T6 := .node cntCached0 cntCached125 cntCached484 cntCached802 cntCached785 cntCached803
private def cntCached805 : T6 := .node cntCached1 cntCached494 cntCached495 cntCached496 cntCached786 cntCached804
private def cntCached806 : T6 := .node cntCached2 cntCached791 cntCached795 cntCached801 cntCached787 cntCached805
private def cntCached807 : T6 := .node cntCached3 cntCached732 cntCached745 cntCached761 cntCached788 cntCached806
private def cntCached808 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached16
private def cntCached809 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached16 cntCached43
private def cntCached810 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached202 cntCached53 cntCached46
private def cntCached811 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached94 cntCached62
private def cntCached812 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached94 cntCached62 cntCached72
private def cntCached813 : T6 := .node cntCached1 cntCached808 cntCached809 cntCached810 cntCached811 cntCached812
private def cntCached814 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached6 cntCached13 cntCached34
private def cntCached815 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached23 cntCached89
private def cntCached816 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached23 cntCached46 cntCached62
private def cntCached817 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached281 cntCached70 cntCached345
private def cntCached818 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached100 cntCached345 cntCached265
private def cntCached819 : T6 := .node cntCached1 cntCached814 cntCached815 cntCached816 cntCached817 cntCached818
private def cntCached820 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached16 cntCached34 cntCached92
private def cntCached821 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached23 cntCached89 cntCached206
private def cntCached822 : T6 := .node cntCached0 cntCached13 cntCached38 cntCached198 cntCached438 cntCached112
private def cntCached823 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached510 cntCached105 cntCached561
private def cntCached824 : T6 := .node cntCached0 cntCached92 cntCached96 cntCached440 cntCached561 cntCached274
private def cntCached825 : T6 := .node cntCached1 cntCached820 cntCached821 cntCached822 cntCached823 cntCached824
private def cntCached826 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached224 cntCached92 cntCached60
private def cntCached827 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached89 cntCached206 cntCached65
private def cntCached828 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached284 cntCached112 cntCached290
private def cntCached829 : T6 := .leaf 125
private def cntCached830 : T6 := .node cntCached0 cntCached60 cntCached251 cntCached408 cntCached274 cntCached829
private def cntCached831 : T6 := .node cntCached1 cntCached826 cntCached827 cntCached828 cntCached824 cntCached830
private def cntCached832 : T6 := .node cntCached2 cntCached59 cntCached813 cntCached819 cntCached825 cntCached831
private def cntCached833 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached38 cntCached283
private def cntCached834 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached21 cntCached281 cntCached208
private def cntCached835 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached283 cntCached292 cntCached304
private def cntCached836 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached65 cntCached304 cntCached146
private def cntCached837 : T6 := .node cntCached1 cntCached809 cntCached833 cntCached834 cntCached835 cntCached836
private def cntCached838 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached13 cntCached38 cntCached60
private def cntCached839 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached32 cntCached198 cntCached110
private def cntCached840 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached44 cntCached208 cntCached235
private def cntCached841 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached381 cntCached389 cntCached447
private def cntCached842 : T6 := .node cntCached0 cntCached60 cntCached331 cntCached79 cntCached447 cntCached134
private def cntCached843 : T6 := .node cntCached1 cntCached838 cntCached839 cntCached840 cntCached841 cntCached842
private def cntCached844 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached46 cntCached302
private def cntCached845 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached46 cntCached65 cntCached124
private def cntCached846 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached208 cntCached591 cntCached155
private def cntCached847 : T6 := .leaf 154
private def cntCached848 : T6 := .node cntCached0 cntCached60 cntCached115 cntCached389 cntCached130 cntCached847
private def cntCached849 : T6 := .leaf 182
private def cntCached850 : T6 := .node cntCached0 cntCached324 cntCached235 cntCached447 cntCached847 cntCached849
private def cntCached851 : T6 := .node cntCached1 cntCached844 cntCached845 cntCached846 cntCached848 cntCached850
private def cntCached852 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached46 cntCached302 cntCached292
private def cntCached853 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached331 cntCached124 cntCached120
private def cntCached854 : T6 := .node cntCached0 cntCached89 cntCached331 cntCached235 cntCached155 cntCached317
private def cntCached855 : T6 := .leaf 210
private def cntCached856 : T6 := .node cntCached0 cntCached115 cntCached293 cntCached134 cntCached849 cntCached855
private def cntCached857 : T6 := .node cntCached1 cntCached852 cntCached853 cntCached854 cntCached850 cntCached856
private def cntCached858 : T6 := .node cntCached2 cntCached406 cntCached837 cntCached843 cntCached851 cntCached857
private def cntCached859 : T6 := .node cntCached0 cntCached0 cntCached30 cntCached43 cntCached57 cntCached70
private def cntCached860 : T6 := .node cntCached0 cntCached13 cntCached38 cntCached283 cntCached381 cntCached105
private def cntCached861 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached510 cntCached105 cntCached389
private def cntCached862 : T6 := .node cntCached1 cntCached54 cntCached403 cntCached859 cntCached860 cntCached861
private def cntCached863 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached194 cntCached65 cntCached304
private def cntCached864 : T6 := .node cntCached0 cntCached43 cntCached281 cntCached251 cntCached446 cntCached298
private def cntCached865 : T6 := .node cntCached0 cntCached198 cntCached208 cntCached408 cntCached298 cntCached170
private def cntCached866 : T6 := .node cntCached1 cntCached810 cntCached834 cntCached863 cntCached864 cntCached865
private def cntCached867 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached53 cntCached283 cntCached510
private def cntCached868 : T6 := .node cntCached0 cntCached16 cntCached21 cntCached194 cntCached65 cntCached304
private def cntCached869 : T6 := .node cntCached0 cntCached224 cntCached44 cntCached70 cntCached463 cntCached416
private def cntCached870 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached446 cntCached700 cntCached337
private def cntCached871 : T6 := .node cntCached0 cntCached62 cntCached79 cntCached342 cntCached337 cntCached552
private def cntCached872 : T6 := .node cntCached1 cntCached867 cntCached868 cntCached869 cntCached870 cntCached871
private def cntCached873 : T6 := .node cntCached0 cntCached21 cntCached40 cntCached99 cntCached381 cntCached105
private def cntCached874 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached115 cntCached463 cntCached307
private def cntCached875 : T6 := .node cntCached0 cntCached198 cntCached381 cntCached463 cntCached778 cntCached171
private def cntCached876 : T6 := .leaf 183
private def cntCached877 : T6 := .node cntCached0 cntCached510 cntCached561 cntCached700 cntCached876 cntCached689
private def cntCached878 : T6 := .leaf 247
private def cntCached879 : T6 := .node cntCached0 cntCached440 cntCached268 cntCached337 cntCached689 cntCached878
private def cntCached880 : T6 := .node cntCached1 cntCached873 cntCached874 cntCached875 cntCached877 cntCached879
private def cntCached881 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached110 cntCached105 cntCached389
private def cntCached882 : T6 := .leaf 144
private def cntCached883 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached290 cntCached307 cntCached882
private def cntCached884 : T6 := .leaf 196
private def cntCached885 : T6 := .node cntCached0 cntCached284 cntCached79 cntCached416 cntCached171 cntCached884
private def cntCached886 : T6 := .leaf 143
private def cntCached887 : T6 := .leaf 279
private def cntCached888 : T6 := .node cntCached0 cntCached408 cntCached886 cntCached552 cntCached878 cntCached887
private def cntCached889 : T6 := .node cntCached1 cntCached881 cntCached883 cntCached885 cntCached879 cntCached888
private def cntCached890 : T6 := .node cntCached2 cntCached862 cntCached866 cntCached872 cntCached880 cntCached889
private def cntCached891 : T6 := .node cntCached0 cntCached13 cntCached43 cntCached57 cntCached65 cntCached670
private def cntCached892 : T6 := .node cntCached0 cntCached34 cntCached46 cntCached381 cntCached124 cntCached479
private def cntCached893 : T6 := .node cntCached0 cntCached92 cntCached302 cntCached105 cntCached479 cntCached155
private def cntCached894 : T6 := .node cntCached1 cntCached56 cntCached439 cntCached891 cntCached892 cntCached893
private def cntCached895 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached283 cntCached292 cntCached304
private def cntCached896 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached251 cntCached446 cntCached298
private def cntCached897 : T6 := .node cntCached0 cntCached46 cntCached292 cntCached306 cntCached569 cntCached570
private def cntCached898 : T6 := .node cntCached0 cntCached302 cntCached304 cntCached416 cntCached570 cntCached572
private def cntCached899 : T6 := .node cntCached1 cntCached811 cntCached895 cntCached896 cntCached897 cntCached898
private def cntCached900 : T6 := .node cntCached0 cntCached21 cntCached92 cntCached99 cntCached381 cntCached105
private def cntCached901 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached251 cntCached446 cntCached298
private def cntCached902 : T6 := .leaf 167
private def cntCached903 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached267 cntCached392 cntCached902
private def cntCached904 : T6 := .node cntCached0 cntCached70 cntCached463 cntCached564 cntCached173 cntCached491
private def cntCached905 : T6 := .leaf 168
private def cntCached906 : T6 := .leaf 249
private def cntCached907 : T6 := .node cntCached0 cntCached345 cntCached307 cntCached905 cntCached491 cntCached906
private def cntCached908 : T6 := .node cntCached1 cntCached900 cntCached901 cntCached903 cntCached904 cntCached907
private def cntCached909 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached115 cntCached124 cntCached479
private def cntCached910 : T6 := .leaf 130
private def cntCached911 : T6 := .leaf 158
private def cntCached912 : T6 := .node cntCached0 cntCached281 cntCached72 cntCached267 cntCached910 cntCached911
private def cntCached913 : T6 := .leaf 184
private def cntCached914 : T6 := .node cntCached0 cntCached510 cntCached463 cntCached392 cntCached913 cntCached433
private def cntCached915 : T6 := .leaf 129
private def cntCached916 : T6 := .leaf 237
private def cntCached917 : T6 := .leaf 270
private def cntCached918 : T6 := .node cntCached0 cntCached670 cntCached915 cntCached173 cntCached916 cntCached917
private def cntCached919 : T6 := .leaf 157
private def cntCached920 : T6 := .leaf 303
private def cntCached921 : T6 := .node cntCached0 cntCached463 cntCached919 cntCached491 cntCached917 cntCached920
private def cntCached922 : T6 := .node cntCached1 cntCached909 cntCached912 cntCached914 cntCached918 cntCached921
private def cntCached923 : T6 := .node cntCached0 cntCached55 cntCached70 cntCached396 cntCached479 cntCached155
private def cntCached924 : T6 := .leaf 186
private def cntCached925 : T6 := .node cntCached0 cntCached284 cntCached408 cntCached244 cntCached911 cntCached924
private def cntCached926 : T6 := .leaf 248
private def cntCached927 : T6 := .node cntCached0 cntCached440 cntCached307 cntCached902 cntCached433 cntCached926
private def cntCached928 : T6 := .leaf 336
private def cntCached929 : T6 := .node cntCached0 cntCached260 cntCached173 cntCached906 cntCached920 cntCached928
private def cntCached930 : T6 := .node cntCached1 cntCached923 cntCached925 cntCached927 cntCached921 cntCached929
private def cntCached931 : T6 := .node cntCached2 cntCached894 cntCached899 cntCached908 cntCached922 cntCached930
private def cntCached932 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached70 cntCached670 cntCached561
private def cntCached933 : T6 := .node cntCached0 cntCached60 cntCached292 cntCached389 cntCached155 cntCached424
private def cntCached934 : T6 := .node cntCached1 cntCached58 cntCached478 cntCached932 cntCached893 cntCached933
private def cntCached935 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached65 cntCached304 cntCached146
private def cntCached936 : T6 := .node cntCached0 cntCached60 cntCached208 cntCached408 cntCached298 cntCached170
private def cntCached937 : T6 := .node cntCached0 cntCached292 cntCached146 cntCached418 cntCached572 cntCached689
private def cntCached938 : T6 := .node cntCached1 cntCached812 cntCached935 cntCached936 cntCached898 cntCached937
private def cntCached939 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached110 cntCached105 cntCached389
private def cntCached940 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached408 cntCached298 cntCached170
private def cntCached941 : T6 := .leaf 198
private def cntCached942 : T6 := .node cntCached0 cntCached62 cntCached304 cntCached148 cntCached902 cntCached941
private def cntCached943 : T6 := .leaf 281
private def cntCached944 : T6 := .node cntCached0 cntCached265 cntCached882 cntCached634 cntCached906 cntCached943
private def cntCached945 : T6 := .node cntCached1 cntCached939 cntCached940 cntCached942 cntCached907 cntCached944
private def cntCached946 : T6 := .node cntCached0 cntCached57 cntCached511 cntCached463 cntCached155 cntCached424
private def cntCached947 : T6 := .leaf 214
private def cntCached948 : T6 := .node cntCached0 cntCached102 cntCached410 cntCached687 cntCached924 cntCached947
private def cntCached949 : T6 := .leaf 280
private def cntCached950 : T6 := .node cntCached0 cntCached408 cntCached882 cntCached941 cntCached926 cntCached949
private def cntCached951 : T6 := .leaf 213
private def cntCached952 : T6 := .leaf 369
private def cntCached953 : T6 := .node cntCached0 cntCached130 cntCached951 cntCached943 cntCached928 cntCached952
private def cntCached954 : T6 := .node cntCached1 cntCached946 cntCached948 cntCached950 cntCached929 cntCached953
private def cntCached955 : T6 := .node cntCached2 cntCached934 cntCached938 cntCached945 cntCached930 cntCached954
private def cntCached956 : T6 := .node cntCached3 cntCached832 cntCached858 cntCached890 cntCached931 cntCached955
private def cntCached957 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached8 cntCached13 cntCached85
private def cntCached958 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached32 cntCached43 cntCached89
private def cntCached959 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached94 cntCached62
private def cntCached960 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached70 cntCached112
private def cntCached961 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached438 cntCached112 cntCached79
private def cntCached962 : T6 := .node cntCached1 cntCached957 cntCached958 cntCached959 cntCached960 cntCached961
private def cntCached963 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached43 cntCached198 cntCached96
private def cntCached964 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached94 cntCached110 cntCached340
private def cntCached965 : T6 := .node cntCached0 cntCached23 cntCached94 cntCached331 cntCached242 cntCached267
private def cntCached966 : T6 := .node cntCached0 cntCached220 cntCached62 cntCached326 cntCached267 cntCached127
private def cntCached967 : T6 := .node cntCached1 cntCached820 cntCached963 cntCached964 cntCached965 cntCached966
private def cntCached968 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached224 cntCached40 cntCached46
private def cntCached969 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached198 cntCached284 cntCached72
private def cntCached970 : T6 := .node cntCached0 cntCached224 cntCached281 cntCached70 cntCached670 cntCached463
private def cntCached971 : T6 := .node cntCached0 cntCached220 cntCached438 cntCached396 cntCached535 cntCached307
private def cntCached972 : T6 := .node cntCached0 cntCached281 cntCached296 cntCached446 cntCached307 cntCached392
private def cntCached973 : T6 := .node cntCached1 cntCached968 cntCached969 cntCached970 cntCached971 cntCached972
private def cntCached974 : T6 := .node cntCached0 cntCached16 cntCached38 cntCached40 cntCached46 cntCached139
private def cntCached975 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached96 cntCached72 cntCached229
private def cntCached976 : T6 := .node cntCached0 cntCached40 cntCached284 cntCached345 cntCached463 cntCached260
private def cntCached977 : T6 := .leaf 155
private def cntCached978 : T6 := .node cntCached0 cntCached69 cntCached124 cntCached335 cntCached392 cntCached977
private def cntCached979 : T6 := .node cntCached1 cntCached974 cntCached975 cntCached976 cntCached972 cntCached978
private def cntCached980 : T6 := .node cntCached2 cntCached64 cntCached962 cntCached967 cntCached973 cntCached979
private def cntCached981 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached283 cntCached110 cntCached440
private def cntCached982 : T6 := .node cntCached0 cntCached224 cntCached60 cntCached100 cntCached440 cntCached304
private def cntCached983 : T6 := .node cntCached1 cntCached39 cntCached248 cntCached746 cntCached981 cntCached982
private def cntCached984 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached202 cntCached38 cntCached55
private def cntCached985 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached43 cntCached283 cntCached331
private def cntCached986 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached94 cntCached251 cntCached79
private def cntCached987 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached102 cntCached389 cntCached390
private def cntCached988 : T6 := .node cntCached0 cntCached198 cntCached65 cntCached290 cntCached390 cntCached392
private def cntCached989 : T6 := .node cntCached1 cntCached984 cntCached985 cntCached986 cntCached987 cntCached988
private def cntCached990 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached43 cntCached198 cntCached96
private def cntCached991 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached46 cntCached65 cntCached124
private def cntCached992 : T6 := .node cntCached0 cntCached43 cntCached281 cntCached381 cntCached389 cntCached447
private def cntCached993 : T6 := .leaf 127
private def cntCached994 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached561 cntCached993 cntCached977
private def cntCached995 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached268 cntCached977 cntCached876
private def cntCached996 : T6 := .node cntCached1 cntCached990 cntCached991 cntCached992 cntCached994 cntCached995
private def cntCached997 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached281 cntCached100 cntCached257
private def cntCached998 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached115 cntCached258 cntCached335
private def cntCached999 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached389 cntCached130 cntCached847
private def cntCached1000 : T6 := .leaf 169
private def cntCached1001 : T6 := .node cntCached0 cntCached62 cntCached591 cntCached993 cntCached1000 cntCached941
private def cntCached1002 : T6 := .leaf 111
private def cntCached1003 : T6 := .leaf 227
private def cntCached1004 : T6 := .node cntCached0 cntCached141 cntCached1002 cntCached977 cntCached941 cntCached1003
private def cntCached1005 : T6 := .node cntCached1 cntCached997 cntCached998 cntCached999 cntCached1001 cntCached1004
private def cntCached1006 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached284 cntCached257 cntCached332
private def cntCached1007 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached235 cntCached335 cntCached156
private def cntCached1008 : T6 := .node cntCached0 cntCached96 cntCached79 cntCached447 cntCached847 cntCached849
private def cntCached1009 : T6 := .leaf 256
private def cntCached1010 : T6 := .node cntCached0 cntCached253 cntCached700 cntCached876 cntCached1003 cntCached1009
private def cntCached1011 : T6 := .node cntCached1 cntCached1006 cntCached1007 cntCached1008 cntCached1004 cntCached1010
private def cntCached1012 : T6 := .node cntCached2 cntCached983 cntCached989 cntCached996 cntCached1005 cntCached1011
private def cntCached1013 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached208 cntCached332 cntCached143
private def cntCached1014 : T6 := .node cntCached0 cntCached92 cntCached96 cntCached75 cntCached143 cntCached562
private def cntCached1015 : T6 := .node cntCached1 cntCached56 cntCached404 cntCached860 cntCached1013 cntCached1014
private def cntCached1016 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached281 cntCached284
private def cntCached1017 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached281 cntCached115 cntCached235
private def cntCached1018 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached65 cntCached561 cntCached268
private def cntCached1019 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached446 cntCached915 cntCached919
private def cntCached1020 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached298 cntCached919 cntCached173
private def cntCached1021 : T6 := .node cntCached1 cntCached1016 cntCached1017 cntCached1018 cntCached1019 cntCached1020
private def cntCached1022 : T6 := .node cntCached0 cntCached21 cntCached92 cntCached57 cntCached208 cntCached75
private def cntCached1023 : T6 := .node cntCached0 cntCached53 cntCached94 cntCached65 cntCached561 cntCached268
private def cntCached1024 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached463 cntCached778 cntCached171
private def cntCached1025 : T6 := .node cntCached0 cntCached70 cntCached561 cntCached700 cntCached876 cntCached689
private def cntCached1026 : T6 := .node cntCached0 cntCached345 cntCached268 cntCached337 cntCached689 cntCached878
private def cntCached1027 : T6 := .node cntCached1 cntCached1022 cntCached1023 cntCached1024 cntCached1025 cntCached1026
private def cntCached1028 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached65 cntCached332 cntCached143
private def cntCached1029 : T6 := .leaf 156
private def cntCached1030 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached463 cntCached309 cntCached1029
private def cntCached1031 : T6 := .node cntCached0 cntCached510 cntCached561 cntCached778 cntCached849 cntCached947
private def cntCached1032 : T6 := .leaf 268
private def cntCached1033 : T6 := .node cntCached0 cntCached670 cntCached309 cntCached876 cntCached782 cntCached1032
private def cntCached1034 : T6 := .leaf 301
private def cntCached1035 : T6 := .node cntCached0 cntCached463 cntCached1029 cntCached689 cntCached1032 cntCached1034
private def cntCached1036 : T6 := .node cntCached1 cntCached1028 cntCached1030 cntCached1031 cntCached1033 cntCached1035
private def cntCached1037 : T6 := .node cntCached0 cntCached55 cntCached70 cntCached670 cntCached143 cntCached562
private def cntCached1038 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached307 cntCached1029 cntCached913
private def cntCached1039 : T6 := .leaf 246
private def cntCached1040 : T6 := .node cntCached0 cntCached440 cntCached268 cntCached171 cntCached947 cntCached1039
private def cntCached1041 : T6 := .leaf 334
private def cntCached1042 : T6 := .node cntCached0 cntCached260 cntCached913 cntCached878 cntCached1034 cntCached1041
private def cntCached1043 : T6 := .node cntCached1 cntCached1037 cntCached1038 cntCached1040 cntCached1035 cntCached1042
private def cntCached1044 : T6 := .node cntCached2 cntCached1015 cntCached1021 cntCached1027 cntCached1036 cntCached1043
private def cntCached1045 : T6 := .node cntCached0 cntCached40 cntCached100 cntCached332 cntCached146 cntCached774
private def cntCached1046 : T6 := .node cntCached0 cntCached46 cntCached257 cntCached143 cntCached774 cntCached134
private def cntCached1047 : T6 := .node cntCached1 cntCached61 cntCached441 cntCached892 cntCached1045 cntCached1046
private def cntCached1048 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached283 cntCached510 cntCached511
private def cntCached1049 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached292 cntCached591 cntCached1002
private def cntCached1050 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached446 cntCached915 cntCached919
private def cntCached1051 : T6 := .leaf 173
private def cntCached1052 : T6 := .leaf 202
private def cntCached1053 : T6 := .node cntCached0 cntCached100 cntCached389 cntCached569 cntCached1051 cntCached1052
private def cntCached1054 : T6 := .leaf 231
private def cntCached1055 : T6 := .node cntCached0 cntCached257 cntCached390 cntCached570 cntCached1052 cntCached1054
private def cntCached1056 : T6 := .node cntCached1 cntCached1048 cntCached1049 cntCached1050 cntCached1053 cntCached1055
private def cntCached1057 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached65 cntCached332 cntCached143
private def cntCached1058 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached446 cntCached915 cntCached919
private def cntCached1059 : T6 := .node cntCached0 cntCached70 cntCached463 cntCached392 cntCached913 cntCached433
private def cntCached1060 : T6 := .node cntCached0 cntCached396 cntCached915 cntCached173 cntCached916 cntCached917
private def cntCached1061 : T6 := .node cntCached0 cntCached446 cntCached919 cntCached491 cntCached917 cntCached920
private def cntCached1062 : T6 := .node cntCached1 cntCached1057 cntCached1058 cntCached1059 cntCached1060 cntCached1061
private def cntCached1063 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached235 cntCached146 cntCached774
private def cntCached1064 : T6 := .leaf 201
private def cntCached1065 : T6 := .node cntCached0 cntCached438 cntCached463 cntCached910 cntCached546 cntCached1064
private def cntCached1066 : T6 := .leaf 236
private def cntCached1067 : T6 := .leaf 269
private def cntCached1068 : T6 := .node cntCached0 cntCached670 cntCached915 cntCached913 cntCached1066 cntCached1067
private def cntCached1069 : T6 := .leaf 327
private def cntCached1070 : T6 := .node cntCached0 cntCached535 cntCached546 cntCached916 cntCached803 cntCached1069
private def cntCached1071 : T6 := .leaf 361
private def cntCached1072 : T6 := .node cntCached0 cntCached307 cntCached1064 cntCached917 cntCached1069 cntCached1071
private def cntCached1073 : T6 := .node cntCached1 cntCached1063 cntCached1065 cntCached1068 cntCached1070 cntCached1072
private def cntCached1074 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached549 cntCached774 cntCached134
private def cntCached1075 : T6 := .leaf 230
private def cntCached1076 : T6 := .node cntCached0 cntCached296 cntCached155 cntCached911 cntCached1064 cntCached1075
private def cntCached1077 : T6 := .leaf 302
private def cntCached1078 : T6 := .node cntCached0 cntCached463 cntCached919 cntCached433 cntCached1067 cntCached1077
private def cntCached1079 : T6 := .leaf 395
private def cntCached1080 : T6 := .node cntCached0 cntCached392 cntCached1075 cntCached920 cntCached1071 cntCached1079
private def cntCached1081 : T6 := .node cntCached1 cntCached1074 cntCached1076 cntCached1078 cntCached1072 cntCached1080
private def cntCached1082 : T6 := .node cntCached2 cntCached1047 cntCached1056 cntCached1062 cntCached1073 cntCached1081
private def cntCached1083 : T6 := .node cntCached0 cntCached139 cntCached332 cntCached562 cntCached134 cntCached455
private def cntCached1084 : T6 := .node cntCached1 cntCached63 cntCached442 cntCached893 cntCached1046 cntCached1083
private def cntCached1085 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached100 cntCached511 cntCached235
private def cntCached1086 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached304 cntCached1002 cntCached700
private def cntCached1087 : T6 := .node cntCached0 cntCached96 cntCached79 cntCached298 cntCached919 cntCached173
private def cntCached1088 : T6 := .leaf 260
private def cntCached1089 : T6 := .node cntCached0 cntCached332 cntCached392 cntCached572 cntCached1054 cntCached1088
private def cntCached1090 : T6 := .node cntCached1 cntCached1085 cntCached1086 cntCached1087 cntCached1055 cntCached1089
private def cntCached1091 : T6 := .node cntCached0 cntCached55 cntCached510 cntCached670 cntCached143 cntCached562
private def cntCached1092 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached298 cntCached919 cntCached173
private def cntCached1093 : T6 := .node cntCached0 cntCached345 cntCached307 cntCached902 cntCached433 cntCached926
private def cntCached1094 : T6 := .node cntCached0 cntCached335 cntCached173 cntCached906 cntCached920 cntCached928
private def cntCached1095 : T6 := .node cntCached1 cntCached1091 cntCached1092 cntCached1093 cntCached1061 cntCached1094
private def cntCached1096 : T6 := .node cntCached0 cntCached62 cntCached265 cntCached447 cntCached134 cntCached455
private def cntCached1097 : T6 := .leaf 259
private def cntCached1098 : T6 := .node cntCached0 cntCached124 cntCached472 cntCached924 cntCached1075 cntCached1097
private def cntCached1099 : T6 := .leaf 335
private def cntCached1100 : T6 := .node cntCached0 cntCached260 cntCached173 cntCached926 cntCached1077 cntCached1099
private def cntCached1101 : T6 := .leaf 429
private def cntCached1102 : T6 := .node cntCached0 cntCached977 cntCached1097 cntCached928 cntCached1079 cntCached1101
private def cntCached1103 : T6 := .node cntCached1 cntCached1096 cntCached1098 cntCached1100 cntCached1080 cntCached1102
private def cntCached1104 : T6 := .node cntCached2 cntCached1084 cntCached1090 cntCached1095 cntCached1081 cntCached1103
private def cntCached1105 : T6 := .node cntCached3 cntCached980 cntCached1012 cntCached1044 cntCached1082 cntCached1104
private def cntCached1106 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached202 cntCached85 cntCached53
private def cntCached1107 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached26 cntCached89 cntCached215
private def cntCached1108 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached94 cntCached62 cntCached72
private def cntCached1109 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached257 cntCached79 cntCached143
private def cntCached1110 : T6 := .node cntCached1 cntCached1106 cntCached1107 cntCached1108 cntCached961 cntCached1109
private def cntCached1111 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached198 cntCached96 cntCached251
private def cntCached1112 : T6 := .node cntCached0 cntCached23 cntCached281 cntCached438 cntCached340 cntCached258
private def cntCached1113 : T6 := .node cntCached0 cntCached46 cntCached72 cntCached117 cntCached127 cntCached309
private def cntCached1114 : T6 := .node cntCached1 cntCached826 cntCached1111 cntCached1112 cntCached966 cntCached1113
private def cntCached1115 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached198 cntCached139 cntCached438
private def cntCached1116 : T6 := .node cntCached0 cntCached87 cntCached69 cntCached251 cntCached229 cntCached463
private def cntCached1117 : T6 := .node cntCached0 cntCached198 cntCached102 cntCached265 cntCached260 cntCached130
private def cntCached1118 : T6 := .node cntCached0 cntCached510 cntCached306 cntCached993 cntCached977 cntCached578
private def cntCached1119 : T6 := .node cntCached1 cntCached1115 cntCached1116 cntCached1117 cntCached978 cntCached1118
private def cntCached1120 : T6 := .node cntCached2 cntCached67 cntCached1110 cntCached1114 cntCached979 cntCached1119
private def cntCached1121 : T6 := .node cntCached0 cntCached87 cntCached139 cntCached141 cntCached304 cntCached479
private def cntCached1122 : T6 := .node cntCached1 cntCached41 cntCached249 cntCached747 cntCached982 cntCached1121
private def cntCached1123 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached55 cntCached49
private def cntCached1124 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached57 cntCached331 cntCached105
private def cntCached1125 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached381 cntCached79 cntCached593
private def cntCached1126 : T6 := .node cntCached0 cntCached69 cntCached242 cntCached432 cntCached392 cntCached399
private def cntCached1127 : T6 := .node cntCached1 cntCached1123 cntCached1124 cntCached1125 cntCached988 cntCached1126
private def cntCached1128 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached198 cntCached96 cntCached251
private def cntCached1129 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached331 cntCached124 cntCached120
private def cntCached1130 : T6 := .node cntCached0 cntCached198 cntCached208 cntCached79 cntCached447 cntCached134
private def cntCached1131 : T6 := .leaf 211
private def cntCached1132 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached886 cntCached876 cntCached1131
private def cntCached1133 : T6 := .node cntCached1 cntCached1128 cntCached1129 cntCached1130 cntCached995 cntCached1132
private def cntCached1134 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached102 cntCached332 cntCached267
private def cntCached1135 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached293 cntCached156 cntCached919
private def cntCached1136 : T6 := .node cntCached0 cntCached251 cntCached593 cntCached134 cntCached849 cntCached855
private def cntCached1137 : T6 := .leaf 285
private def cntCached1138 : T6 := .node cntCached0 cntCached446 cntCached570 cntCached1131 cntCached1009 cntCached1137
private def cntCached1139 : T6 := .node cntCached1 cntCached1134 cntCached1135 cntCached1136 cntCached1010 cntCached1138
private def cntCached1140 : T6 := .node cntCached2 cntCached1122 cntCached1127 cntCached1133 cntCached1011 cntCached1139
private def cntCached1141 : T6 := .node cntCached0 cntCached60 cntCached251 cntCached591 cntCached562 cntCached569
private def cntCached1142 : T6 := .node cntCached1 cntCached58 cntCached405 cntCached861 cntCached1014 cntCached1141
private def cntCached1143 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached281 cntCached284 cntCached102
private def cntCached1144 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached208 cntCached235 cntCached293
private def cntCached1145 : T6 := .node cntCached0 cntCached60 cntCached331 cntCached304 cntCached268 cntCached886
private def cntCached1146 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached170 cntCached173 cntCached951
private def cntCached1147 : T6 := .node cntCached1 cntCached1143 cntCached1144 cntCached1145 cntCached1020 cntCached1146
private def cntCached1148 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached70 cntCached75 cntCached591
private def cntCached1149 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached304 cntCached268 cntCached886
private def cntCached1150 : T6 := .node cntCached0 cntCached62 cntCached79 cntCached416 cntCached171 cntCached884
private def cntCached1151 : T6 := .node cntCached0 cntCached265 cntCached886 cntCached552 cntCached878 cntCached887
private def cntCached1152 : T6 := .node cntCached1 cntCached1148 cntCached1149 cntCached1150 cntCached1026 cntCached1151
private def cntCached1153 : T6 := .node cntCached0 cntCached57 cntCached511 cntCached561 cntCached562 cntCached569
private def cntCached1154 : T6 := .leaf 212
private def cntCached1155 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached882 cntCached913 cntCached1154
private def cntCached1156 : T6 := .leaf 278
private def cntCached1157 : T6 := .node cntCached0 cntCached408 cntCached886 cntCached884 cntCached1039 cntCached1156
private def cntCached1158 : T6 := .leaf 367
private def cntCached1159 : T6 := .node cntCached0 cntCached130 cntCached1154 cntCached887 cntCached1041 cntCached1158
private def cntCached1160 : T6 := .node cntCached1 cntCached1153 cntCached1155 cntCached1157 cntCached1042 cntCached1159
private def cntCached1161 : T6 := .node cntCached2 cntCached1142 cntCached1147 cntCached1152 cntCached1043 cntCached1160
private def cntCached1162 : T6 := .leaf 180
private def cntCached1163 : T6 := .node cntCached0 cntCached438 cntCached267 cntCached569 cntCached455 cntCached1162
private def cntCached1164 : T6 := .node cntCached1 cntCached66 cntCached480 cntCached933 cntCached1083 cntCached1163
private def cntCached1165 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached141 cntCached235 cntCached125
private def cntCached1166 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached146 cntCached700 cntCached570
private def cntCached1167 : T6 := .node cntCached0 cntCached251 cntCached593 cntCached170 cntCached173 cntCached951
private def cntCached1168 : T6 := .leaf 289
private def cntCached1169 : T6 := .node cntCached0 cntCached267 cntCached399 cntCached689 cntCached1088 cntCached1168
private def cntCached1170 : T6 := .node cntCached1 cntCached1165 cntCached1166 cntCached1167 cntCached1089 cntCached1169
private def cntCached1171 : T6 := .node cntCached0 cntCached57 cntCached296 cntCached561 cntCached562 cntCached569
private def cntCached1172 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached170 cntCached173 cntCached951
private def cntCached1173 : T6 := .node cntCached0 cntCached265 cntCached882 cntCached941 cntCached926 cntCached949
private def cntCached1174 : T6 := .node cntCached0 cntCached993 cntCached951 cntCached943 cntCached928 cntCached952
private def cntCached1175 : T6 := .node cntCached1 cntCached1171 cntCached1172 cntCached1173 cntCached1094 cntCached1174
private def cntCached1176 : T6 := .node cntCached0 cntCached65 cntCached237 cntCached156 cntCached455 cntCached1162
private def cntCached1177 : T6 := .leaf 288
private def cntCached1178 : T6 := .node cntCached0 cntCached306 cntCached497 cntCached947 cntCached1097 cntCached1177
private def cntCached1179 : T6 := .leaf 368
private def cntCached1180 : T6 := .node cntCached0 cntCached130 cntCached951 cntCached949 cntCached1099 cntCached1179
private def cntCached1181 : T6 := .leaf 463
private def cntCached1182 : T6 := .node cntCached0 cntCached578 cntCached1177 cntCached952 cntCached1101 cntCached1181
private def cntCached1183 : T6 := .node cntCached1 cntCached1176 cntCached1178 cntCached1180 cntCached1102 cntCached1182
private def cntCached1184 : T6 := .node cntCached2 cntCached1164 cntCached1170 cntCached1175 cntCached1103 cntCached1183
private def cntCached1185 : T6 := .node cntCached3 cntCached1120 cntCached1140 cntCached1161 cntCached1104 cntCached1184
private def cntCached1186 : T6 := .node cntCached4 cntCached169 cntCached807 cntCached956 cntCached1105 cntCached1185
private def cntCached1187 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached202 cntCached43 cntCached89
private def cntCached1188 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached53 cntCached281 cntCached284
private def cntCached1189 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached281 cntCached438 cntCached296
private def cntCached1190 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached284 cntCached296 cntCached124
private def cntCached1191 : T6 := .node cntCached1 cntCached363 cntCached1187 cntCached1188 cntCached1189 cntCached1190
private def cntCached1192 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached38 cntCached89 cntCached139
private def cntCached1193 : T6 := .node cntCached0 cntCached13 cntCached43 cntCached198 cntCached62 cntCached141
private def cntCached1194 : T6 := .node cntCached0 cntCached85 cntCached60 cntCached62 cntCached440 cntCached290
private def cntCached1195 : T6 := .node cntCached0 cntCached26 cntCached69 cntCached141 cntCached290 cntCached535
private def cntCached1196 : T6 := .node cntCached1 cntCached515 cntCached1192 cntCached1193 cntCached1194 cntCached1195
private def cntCached1197 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached55 cntCached139 cntCached110
private def cntCached1198 : T6 := .node cntCached0 cntCached85 cntCached89 cntCached96 cntCached141 cntCached253
private def cntCached1199 : T6 := .node cntCached0 cntCached194 cntCached331 cntCached253 cntCached535 cntCached155
private def cntCached1200 : T6 := .node cntCached1 cntCached522 cntCached1197 cntCached1198 cntCached1195 cntCached1199
private def cntCached1201 : T6 := .node cntCached2 cntCached48 cntCached508 cntCached1191 cntCached1196 cntCached1200
private def cntCached1202 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached94 cntCached302
private def cntCached1203 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached46 cntCached302 cntCached115
private def cntCached1204 : T6 := .node cntCached1 cntCached33 cntCached193 cntCached248 cntCached1202 cntCached1203
private def cntCached1205 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached32 cntCached87 cntCached57
private def cntCached1206 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached222 cntCached65
private def cntCached1207 : T6 := .node cntCached0 cntCached85 cntCached220 cntCached215 cntCached72 cntCached79
private def cntCached1208 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached251 cntCached79 cntCached519
private def cntCached1209 : T6 := .node cntCached1 cntCached531 cntCached1205 cntCached1206 cntCached1207 cntCached1208
private def cntCached1210 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached102 cntCached561 cntCached562
private def cntCached1211 : T6 := .node cntCached0 cntCached198 cntCached65 cntCached290 cntCached562 cntCached564
private def cntCached1212 : T6 := .node cntCached1 cntCached364 cntCached538 cntCached539 cntCached1210 cntCached1211
private def cntCached1213 : T6 := .node cntCached0 cntCached32 cntCached92 cntCached57 cntCached115 cntCached253
private def cntCached1214 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached251 cntCached591 cntCached1002
private def cntCached1215 : T6 := .node cntCached1 cntCached516 cntCached1213 cntCached1214 cntCached545 cntCached547
private def cntCached1216 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached208 cntCached253 cntCached479
private def cntCached1217 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached79 cntCached1002 cntCached700
private def cntCached1218 : T6 := .node cntCached1 cntCached523 cntCached1216 cntCached1217 cntCached547 cntCached553
private def cntCached1219 : T6 := .node cntCached2 cntCached1204 cntCached1209 cntCached1212 cntCached1215 cntCached1218
private def cntCached1220 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached57 cntCached331 cntCached345
private def cntCached1221 : T6 := .node cntCached0 cntCached23 cntCached198 cntCached438 cntCached345 cntCached290
private def cntCached1222 : T6 := .node cntCached1 cntCached39 cntCached248 cntCached746 cntCached1220 cntCached1221
private def cntCached1223 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached57 cntCached72 cntCached408
private def cntCached1224 : T6 := .node cntCached0 cntCached92 cntCached215 cntCached257 cntCached267 cntCached268
private def cntCached1225 : T6 := .node cntCached0 cntCached281 cntCached251 cntCached258 cntCached268 cntCached151
private def cntCached1226 : T6 := .node cntCached1 cntCached559 cntCached1206 cntCached1223 cntCached1224 cntCached1225
private def cntCached1227 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached283 cntCached102 cntCached290
private def cntCached1228 : T6 := .node cntCached0 cntCached26 cntCached283 cntCached292 cntCached306 cntCached416
private def cntCached1229 : T6 := .node cntCached0 cntCached283 cntCached72 cntCached125 cntCached156 cntCached455
private def cntCached1230 : T6 := .node cntCached0 cntCached100 cntCached408 cntCached342 cntCached455 cntCached457
private def cntCached1231 : T6 := .node cntCached1 cntCached567 cntCached1227 cntCached1228 cntCached1229 cntCached1230
private def cntCached1232 : T6 := .node cntCached0 cntCached510 cntCached463 cntCached424 cntCached606 cntCached607
private def cntCached1233 : T6 := .node cntCached0 cntCached511 cntCached155 cntCached399 cntCached607 cntCached609
private def cntCached1234 : T6 := .node cntCached1 cntCached575 cntCached576 cntCached577 cntCached1232 cntCached1233
private def cntCached1235 : T6 := .node cntCached0 cntCached235 cntCached472 cntCached426 cntCached609 cntCached639
private def cntCached1236 : T6 := .node cntCached1 cntCached583 cntCached584 cntCached585 cntCached1233 cntCached1235
private def cntCached1237 : T6 := .node cntCached2 cntCached1222 cntCached1226 cntCached1231 cntCached1234 cntCached1236
private def cntCached1238 : T6 := .node cntCached0 cntCached38 cntCached94 cntCached208 cntCached242 cntCached463
private def cntCached1239 : T6 := .node cntCached0 cntCached220 cntCached302 cntCached340 cntCached463 cntCached410
private def cntCached1240 : T6 := .node cntCached1 cntCached45 cntCached285 cntCached763 cntCached1238 cntCached1239
private def cntCached1241 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached215 cntCached72 cntCached79
private def cntCached1242 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached257 cntCached267 cntCached268
private def cntCached1243 : T6 := .node cntCached0 cntCached283 cntCached257 cntCached125 cntCached309 cntCached310
private def cntCached1244 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached298 cntCached310 cntCached312
private def cntCached1245 : T6 := .node cntCached1 cntCached596 cntCached1241 cntCached1242 cntCached1243 cntCached1244
private def cntCached1246 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached141 cntCached446 cntCached447
private def cntCached1247 : T6 := .node cntCached0 cntCached283 cntCached141 cntCached143 cntCached778 cntCached497
private def cntCached1248 : T6 := .leaf 207
private def cntCached1249 : T6 := .node cntCached0 cntCached110 cntCached267 cntCached700 cntCached312 cntCached1248
private def cntCached1250 : T6 := .node cntCached0 cntCached440 cntCached268 cntCached484 cntCached1248 cntCached1066
private def cntCached1251 : T6 := .node cntCached1 cntCached604 cntCached1246 cntCached1247 cntCached1249 cntCached1250
private def cntCached1252 : T6 := .node cntCached0 cntCached281 cntCached141 cntCached446 cntCached829 cntCached798
private def cntCached1253 : T6 := .node cntCached0 cntCached510 cntCached446 cntCached156 cntCached464 cntCached176
private def cntCached1254 : T6 := .leaf 254
private def cntCached1255 : T6 := .node cntCached0 cntCached75 cntCached130 cntCached779 cntCached706 cntCached1254
private def cntCached1256 : T6 := .leaf 151
private def cntCached1257 : T6 := .leaf 284
private def cntCached1258 : T6 := .node cntCached0 cntCached117 cntCached1256 cntCached780 cntCached1254 cntCached1257
private def cntCached1259 : T6 := .node cntCached1 cntCached612 cntCached1252 cntCached1253 cntCached1255 cntCached1258
private def cntCached1260 : T6 := .node cntCached0 cntCached96 cntCached304 cntCached447 cntCached798 cntCached606
private def cntCached1261 : T6 := .node cntCached0 cntCached511 cntCached447 cntCached455 cntCached176 cntCached466
private def cntCached1262 : T6 := .leaf 314
private def cntCached1263 : T6 := .node cntCached0 cntCached293 cntCached464 cntCached782 cntCached1257 cntCached1262
private def cntCached1264 : T6 := .node cntCached1 cntCached621 cntCached1260 cntCached1261 cntCached1258 cntCached1263
private def cntCached1265 : T6 := .node cntCached2 cntCached1240 cntCached1245 cntCached1251 cntCached1259 cntCached1264
private def cntCached1266 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached408 cntCached410 cntCached148
private def cntCached1267 : T6 := .node cntCached1 cntCached47 cntCached286 cntCached764 cntCached1239 cntCached1266
private def cntCached1268 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached251 cntCached79 cntCached519
private def cntCached1269 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached258 cntCached268 cntCached151
private def cntCached1270 : T6 := .node cntCached0 cntCached251 cntCached293 cntCached134 cntCached312 cntCached319
private def cntCached1271 : T6 := .node cntCached1 cntCached631 cntCached1268 cntCached1269 cntCached1244 cntCached1270
private def cntCached1272 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached265 cntCached447 cntCached449
private def cntCached1273 : T6 := .node cntCached0 cntCached100 cntCached265 cntCached148 cntCached497 cntCached165
private def cntCached1274 : T6 := .leaf 265
private def cntCached1275 : T6 := .node cntCached0 cntCached304 cntCached151 cntCached775 cntCached1066 cntCached1274
private def cntCached1276 : T6 := .node cntCached1 cntCached637 cntCached1272 cntCached1273 cntCached1250 cntCached1275
private def cntCached1277 : T6 := .leaf 200
private def cntCached1278 : T6 := .node cntCached0 cntCached65 cntCached120 cntCached449 cntCached606 cntCached1277
private def cntCached1279 : T6 := .node cntCached0 cntCached235 cntCached449 cntCached457 cntCached466 cntCached473
private def cntCached1280 : T6 := .leaf 344
private def cntCached1281 : T6 := .node cntCached0 cntCached298 cntCached1064 cntCached785 cntCached1262 cntCached1280
private def cntCached1282 : T6 := .node cntCached1 cntCached642 cntCached1278 cntCached1279 cntCached1263 cntCached1281
private def cntCached1283 : T6 := .node cntCached2 cntCached1267 cntCached1271 cntCached1276 cntCached1264 cntCached1282
private def cntCached1284 : T6 := .node cntCached3 cntCached1201 cntCached1219 cntCached1237 cntCached1265 cntCached1283
private def cntCached1285 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached38 cntCached60 cntCached324
private def cntCached1286 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached281 cntCached70 cntCached345
private def cntCached1287 : T6 := .node cntCached0 cntCached224 cntCached281 cntCached110 cntCached396 cntCached446
private def cntCached1288 : T6 := .node cntCached0 cntCached40 cntCached284 cntCached340 cntCached446 cntCached335
private def cntCached1289 : T6 := .node cntCached1 cntCached820 cntCached1285 cntCached1286 cntCached1287 cntCached1288
private def cntCached1290 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached60 cntCached302 cntCached102
private def cntCached1291 : T6 := .node cntCached0 cntCached34 cntCached46 cntCached510 cntCached105 cntCached561
private def cntCached1292 : T6 := .node cntCached0 cntCached40 cntCached100 cntCached670 cntCached549 cntCached268
private def cntCached1293 : T6 := .node cntCached0 cntCached46 cntCached257 cntCached463 cntCached268 cntCached700
private def cntCached1294 : T6 := .node cntCached1 cntCached968 cntCached1290 cntCached1291 cntCached1292 cntCached1293
private def cntCached1295 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached324 cntCached102 cntCached242
private def cntCached1296 : T6 := .node cntCached0 cntCached92 cntCached302 cntCached440 cntCached561 cntCached274
private def cntCached1297 : T6 := .node cntCached0 cntCached139 cntCached332 cntCached260 cntCached700 cntCached847
private def cntCached1298 : T6 := .node cntCached1 cntCached974 cntCached1295 cntCached1296 cntCached1293 cntCached1297
private def cntCached1299 : T6 := .node cntCached2 cntCached64 cntCached962 cntCached1289 cntCached1294 cntCached1298
private def cntCached1300 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached198 cntCached381 cntCached332
private def cntCached1301 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached208 cntCached591 cntCached155
private def cntCached1302 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached389 cntCached130 cntCached847
private def cntCached1303 : T6 := .node cntCached0 cntCached96 cntCached235 cntCached447 cntCached847 cntCached849
private def cntCached1304 : T6 := .node cntCached1 cntCached990 cntCached1300 cntCached1301 cntCached1302 cntCached1303
private def cntCached1305 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached65 cntCached265 cntCached260
private def cntCached1306 : T6 := .node cntCached0 cntCached60 cntCached115 cntCached591 cntCached829 cntCached310
private def cntCached1307 : T6 := .node cntCached0 cntCached284 cntCached117 cntCached130 cntCached905 cntCached552
private def cntCached1308 : T6 := .leaf 226
private def cntCached1309 : T6 := .node cntCached0 cntCached72 cntCached127 cntCached847 cntCached552 cntCached1308
private def cntCached1310 : T6 := .node cntCached1 cntCached997 cntCached1305 cntCached1306 cntCached1307 cntCached1309
private def cntCached1311 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached124 cntCached260 cntCached424
private def cntCached1312 : T6 := .leaf 181
private def cntCached1313 : T6 := .node cntCached0 cntCached324 cntCached235 cntCached155 cntCached310 cntCached1312
private def cntCached1314 : T6 := .leaf 255
private def cntCached1315 : T6 := .node cntCached0 cntCached229 cntCached778 cntCached849 cntCached1308 cntCached1314
private def cntCached1316 : T6 := .node cntCached1 cntCached1006 cntCached1311 cntCached1313 cntCached1309 cntCached1315
private def cntCached1317 : T6 := .node cntCached2 cntCached558 cntCached989 cntCached1304 cntCached1310 cntCached1316
private def cntCached1318 : T6 := .node cntCached0 cntCached43 cntCached281 cntCached115 cntCached463 cntCached307
private def cntCached1319 : T6 := .node cntCached0 cntCached281 cntCached292 cntCached267 cntCached910 cntCached911
private def cntCached1320 : T6 := .node cntCached0 cntCached284 cntCached304 cntCached244 cntCached911 cntCached924
private def cntCached1321 : T6 := .node cntCached1 cntCached1016 cntCached986 cntCached1318 cntCached1319 cntCached1320
private def cntCached1322 : T6 := .node cntCached2 cntCached1015 cntCached1321 cntCached1027 cntCached1036 cntCached1043
private def cntCached1323 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached102 cntCached389 cntCached390
private def cntCached1324 : T6 := .node cntCached0 cntCached46 cntCached292 cntCached267 cntCached910 cntCached911
private def cntCached1325 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached424 cntCached578 cntCached319
private def cntCached1326 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached399 cntCached319 cntCached580
private def cntCached1327 : T6 := .node cntCached1 cntCached1048 cntCached1323 cntCached1324 cntCached1325 cntCached1326
private def cntCached1328 : T6 := .node cntCached2 cntCached1047 cntCached1327 cntCached1062 cntCached1073 cntCached1081
private def cntCached1329 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached290 cntCached390 cntCached392
private def cntCached1330 : T6 := .node cntCached0 cntCached302 cntCached304 cntCached244 cntCached911 cntCached924
private def cntCached1331 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached426 cntCached580 cntCached586
private def cntCached1332 : T6 := .node cntCached1 cntCached1085 cntCached1329 cntCached1330 cntCached1326 cntCached1331
private def cntCached1333 : T6 := .node cntCached2 cntCached1084 cntCached1332 cntCached1095 cntCached1081 cntCached1103
private def cntCached1334 : T6 := .node cntCached3 cntCached1299 cntCached1317 cntCached1322 cntCached1328 cntCached1333
private def cntCached1335 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached16 cntCached85 cntCached26
private def cntCached1336 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached26 cntCached198 cntCached206
private def cntCached1337 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached57 cntCached70 cntCached112
private def cntCached1338 : T6 := .node cntCached0 cntCached43 cntCached57 cntCached331 cntCached105 cntCached591
private def cntCached1339 : T6 := .node cntCached0 cntCached44 cntCached62 cntCached345 cntCached591 cntCached593
private def cntCached1340 : T6 := .node cntCached1 cntCached1335 cntCached1336 cntCached1337 cntCached1338 cntCached1339
private def cntCached1341 : T6 := .node cntCached0 cntCached202 cntCached87 cntCached46 cntCached62 cntCached141
private def cntCached1342 : T6 := .node cntCached0 cntCached23 cntCached283 cntCached331 cntCached242 cntCached267
private def cntCached1343 : T6 := .node cntCached0 cntCached44 cntCached70 cntCached229 cntCached519 cntCached244
private def cntCached1344 : T6 := .node cntCached0 cntCached94 cntCached112 cntCached306 cntCached244 cntCached472
private def cntCached1345 : T6 := .node cntCached1 cntCached968 cntCached1341 cntCached1342 cntCached1343 cntCached1344
private def cntCached1346 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached220 cntCached94 cntCached324
private def cntCached1347 : T6 := .node cntCached0 cntCached224 cntCached281 cntCached62 cntCached112 cntCached304
private def cntCached1348 : T6 := .node cntCached0 cntCached220 cntCached510 cntCached396 cntCached535 cntCached307
private def cntCached1349 : T6 := .node cntCached0 cntCached283 cntCached326 cntCached237 cntCached993 cntCached418
private def cntCached1350 : T6 := .node cntCached0 cntCached96 cntCached258 cntCached298 cntCached418 cntCached902
private def cntCached1351 : T6 := .node cntCached1 cntCached1346 cntCached1347 cntCached1348 cntCached1349 cntCached1350
private def cntCached1352 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached281 cntCached324 cntCached331
private def cntCached1353 : T6 := .node cntCached0 cntCached92 cntCached96 cntCached141 cntCached304 cntCached549
private def cntCached1354 : T6 := .node cntCached0 cntCached281 cntCached511 cntCached446 cntCached307 cntCached392
private def cntCached1355 : T6 := .node cntCached0 cntCached208 cntCached120 cntCached564 cntCached902 cntCached572
private def cntCached1356 : T6 := .node cntCached1 cntCached1352 cntCached1353 cntCached1354 cntCached1350 cntCached1355
private def cntCached1357 : T6 := .node cntCached2 cntCached74 cntCached1340 cntCached1345 cntCached1351 cntCached1356
private def cntCached1358 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached70 cntCached105 cntCached591
private def cntCached1359 : T6 := .node cntCached0 cntCached92 cntCached206 cntCached112 cntCached591 cntCached593
private def cntCached1360 : T6 := .node cntCached1 cntCached45 cntCached528 cntCached981 cntCached1358 cntCached1359
private def cntCached1361 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached43 cntCached89 cntCached139
private def cntCached1362 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached65 cntCached229
private def cntCached1363 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached292 cntCached591 cntCached1002
private def cntCached1364 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached561 cntCached148 cntCached418
private def cntCached1365 : T6 := .node cntCached0 cntCached96 cntCached235 cntCached562 cntCached418 cntCached546
private def cntCached1366 : T6 := .node cntCached1 cntCached1361 cntCached1362 cntCached1363 cntCached1364 cntCached1365
private def cntCached1367 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached46 cntCached62 cntCached141
private def cntCached1368 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached65 cntCached265 cntCached260
private def cntCached1369 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached389 cntCached130 cntCached847
private def cntCached1370 : T6 := .node cntCached0 cntCached100 cntCached591 cntCached993 cntCached1000 cntCached941
private def cntCached1371 : T6 := .node cntCached0 cntCached257 cntCached1002 cntCached977 cntCached941 cntCached1003
private def cntCached1372 : T6 := .node cntCached1 cntCached1367 cntCached1368 cntCached1369 cntCached1370 cntCached1371
private def cntCached1373 : T6 := .node cntCached0 cntCached43 cntCached283 cntCached438 cntCached345 cntCached408
private def cntCached1374 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached258 cntCached298 cntCached886
private def cntCached1375 : T6 := .node cntCached0 cntCached62 cntCached591 cntCached130 cntCached905 cntCached552
private def cntCached1376 : T6 := .node cntCached0 cntCached440 cntCached342 cntCached1000 cntCached689 cntCached185
private def cntCached1377 : T6 := .leaf 275
private def cntCached1378 : T6 := .node cntCached0 cntCached290 cntCached687 cntCached941 cntCached185 cntCached1377
private def cntCached1379 : T6 := .node cntCached1 cntCached1373 cntCached1374 cntCached1375 cntCached1376 cntCached1378
private def cntCached1380 : T6 := .node cntCached0 cntCached44 cntCached284 cntCached296 cntCached408 cntCached237
private def cntCached1381 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached335 cntCached886 cntCached905
private def cntCached1382 : T6 := .node cntCached0 cntCached141 cntCached1002 cntCached847 cntCached552 cntCached1308
private def cntCached1383 : T6 := .leaf 305
private def cntCached1384 : T6 := .node cntCached0 cntCached535 cntCached161 cntCached1003 cntCached1377 cntCached1383
private def cntCached1385 : T6 := .node cntCached1 cntCached1380 cntCached1381 cntCached1382 cntCached1378 cntCached1384
private def cntCached1386 : T6 := .node cntCached2 cntCached1360 cntCached1366 cntCached1372 cntCached1379 cntCached1385
private def cntCached1387 : T6 := .node cntCached0 cntCached40 cntCached62 cntCached253 cntCached593 cntCached148
private def cntCached1388 : T6 := .node cntCached0 cntCached46 cntCached141 cntCached125 cntCached148 cntCached317
private def cntCached1389 : T6 := .node cntCached1 cntCached61 cntCached556 cntCached1013 cntCached1387 cntCached1388
private def cntCached1390 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached94 cntCached438 cntCached296
private def cntCached1391 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached251 cntCached117 cntCached127
private def cntCached1392 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached463 cntCached309 cntCached1029
private def cntCached1393 : T6 := .node cntCached0 cntCached438 cntCached389 cntCached910 cntCached546 cntCached1064
private def cntCached1394 : T6 := .node cntCached0 cntCached296 cntCached390 cntCached911 cntCached1064 cntCached1075
private def cntCached1395 : T6 := .node cntCached1 cntCached1390 cntCached1391 cntCached1392 cntCached1393 cntCached1394
private def cntCached1396 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached381 cntCached253 cntCached125
private def cntCached1397 : T6 := .node cntCached0 cntCached281 cntCached292 cntCached561 cntCached993 cntCached977
private def cntCached1398 : T6 := .node cntCached0 cntCached70 cntCached561 cntCached778 cntCached849 cntCached947
private def cntCached1399 : T6 := .node cntCached0 cntCached396 cntCached309 cntCached876 cntCached782 cntCached1032
private def cntCached1400 : T6 := .node cntCached0 cntCached446 cntCached1029 cntCached689 cntCached1032 cntCached1034
private def cntCached1401 : T6 := .node cntCached1 cntCached1396 cntCached1397 cntCached1398 cntCached1399 cntCached1400
private def cntCached1402 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached124 cntCached593 cntCached148
private def cntCached1403 : T6 := .leaf 170
private def cntCached1404 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached309 cntCached1403 cntCached634
private def cntCached1405 : T6 := .leaf 267
private def cntCached1406 : T6 := .node cntCached0 cntCached670 cntCached309 cntCached849 cntCached466 cntCached1405
private def cntCached1407 : T6 := .leaf 325
private def cntCached1408 : T6 := .node cntCached0 cntCached535 cntCached161 cntCached782 cntCached711 cntCached1407
private def cntCached1409 : T6 := .leaf 359
private def cntCached1410 : T6 := .node cntCached0 cntCached307 cntCached1277 cntCached1032 cntCached1407 cntCached1409
private def cntCached1411 : T6 := .node cntCached1 cntCached1402 cntCached1404 cntCached1406 cntCached1408 cntCached1410
private def cntCached1412 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached479 cntCached148 cntCached317
private def cntCached1413 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached1029 cntCached634 cntCached346
private def cntCached1414 : T6 := .leaf 300
private def cntCached1415 : T6 := .node cntCached0 cntCached463 cntCached1029 cntCached947 cntCached1405 cntCached1414
private def cntCached1416 : T6 := .leaf 229
private def cntCached1417 : T6 := .leaf 393
private def cntCached1418 : T6 := .node cntCached0 cntCached392 cntCached1416 cntCached1034 cntCached1409 cntCached1417
private def cntCached1419 : T6 := .node cntCached1 cntCached1412 cntCached1413 cntCached1415 cntCached1410 cntCached1418
private def cntCached1420 : T6 := .node cntCached2 cntCached1389 cntCached1395 cntCached1401 cntCached1411 cntCached1419
private def cntCached1421 : T6 := .node cntCached0 cntCached94 cntCached345 cntCached593 cntCached156 cntCached310
private def cntCached1422 : T6 := .node cntCached0 cntCached324 cntCached408 cntCached148 cntCached310 cntCached1051
private def cntCached1423 : T6 := .node cntCached1 cntCached71 cntCached592 cntCached1045 cntCached1421 cntCached1422
private def cntCached1424 : T6 := .node cntCached0 cntCached43 cntCached94 cntCached70 cntCached326 cntCached258
private def cntCached1425 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached389 cntCached342 cntCached687
private def cntCached1426 : T6 := .node cntCached0 cntCached100 cntCached389 cntCached910 cntCached546 cntCached1064
private def cntCached1427 : T6 := .leaf 220
private def cntCached1428 : T6 := .leaf 250
private def cntCached1429 : T6 := .node cntCached0 cntCached340 cntCached774 cntCached578 cntCached1427 cntCached1428
private def cntCached1430 : T6 := .node cntCached0 cntCached265 cntCached489 cntCached319 cntCached1428 cntCached949
private def cntCached1431 : T6 := .node cntCached1 cntCached1424 cntCached1425 cntCached1426 cntCached1429 cntCached1430
private def cntCached1432 : T6 := .node cntCached0 cntCached60 cntCached208 cntCached124 cntCached593 cntCached148
private def cntCached1433 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached915 cntCached161 cntCached1277
private def cntCached1434 : T6 := .node cntCached0 cntCached396 cntCached915 cntCached913 cntCached1066 cntCached1067
private def cntCached1435 : T6 := .node cntCached0 cntCached237 cntCached546 cntCached916 cntCached803 cntCached1069
private def cntCached1436 : T6 := .node cntCached0 cntCached298 cntCached1064 cntCached917 cntCached1069 cntCached1071
private def cntCached1437 : T6 := .node cntCached1 cntCached1432 cntCached1433 cntCached1434 cntCached1435 cntCached1436
private def cntCached1438 : T6 := .node cntCached0 cntCached69 cntCached229 cntCached432 cntCached156 cntCached310
private def cntCached1439 : T6 := .node cntCached0 cntCached340 cntCached599 cntCached546 cntCached802 cntCached926
private def cntCached1440 : T6 := .leaf 326
private def cntCached1441 : T6 := .node cntCached0 cntCached535 cntCached546 cntCached1066 cntCached498 cntCached1440
private def cntCached1442 : T6 := .leaf 353
private def cntCached1443 : T6 := .leaf 388
private def cntCached1444 : T6 := .node cntCached0 cntCached993 cntCached799 cntCached803 cntCached1442 cntCached1443
private def cntCached1445 : T6 := .leaf 423
private def cntCached1446 : T6 := .node cntCached0 cntCached418 cntCached906 cntCached1069 cntCached1443 cntCached1445
private def cntCached1447 : T6 := .node cntCached1 cntCached1438 cntCached1439 cntCached1441 cntCached1444 cntCached1446
private def cntCached1448 : T6 := .node cntCached0 cntCached70 cntCached446 cntCached599 cntCached310 cntCached1051
private def cntCached1449 : T6 := .node cntCached0 cntCached265 cntCached600 cntCached1064 cntCached926 cntCached1156
private def cntCached1450 : T6 := .leaf 360
private def cntCached1451 : T6 := .node cntCached0 cntCached307 cntCached1064 cntCached1067 cntCached1440 cntCached1450
private def cntCached1452 : T6 := .leaf 458
private def cntCached1453 : T6 := .node cntCached0 cntCached902 cntCached887 cntCached1071 cntCached1445 cntCached1452
private def cntCached1454 : T6 := .node cntCached1 cntCached1448 cntCached1449 cntCached1451 cntCached1446 cntCached1453
private def cntCached1455 : T6 := .node cntCached2 cntCached1423 cntCached1431 cntCached1437 cntCached1447 cntCached1454
private def cntCached1456 : T6 := .leaf 193
private def cntCached1457 : T6 := .node cntCached0 cntCached331 cntCached237 cntCached317 cntCached1051 cntCached1456
private def cntCached1458 : T6 := .node cntCached1 cntCached73 cntCached594 cntCached1046 cntCached1422 cntCached1457
private def cntCached1459 : T6 := .node cntCached0 cntCached44 cntCached302 cntCached112 cntCached258 cntCached120
private def cntCached1460 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached390 cntCached687 cntCached161
private def cntCached1461 : T6 := .node cntCached0 cntCached257 cntCached390 cntCached911 cntCached1064 cntCached1075
private def cntCached1462 : T6 := .leaf 310
private def cntCached1463 : T6 := .node cntCached0 cntCached519 cntCached1051 cntCached580 cntCached949 cntCached1462
private def cntCached1464 : T6 := .node cntCached1 cntCached1459 cntCached1460 cntCached1461 cntCached1430 cntCached1463
private def cntCached1465 : T6 := .node cntCached0 cntCached49 cntCached340 cntCached479 cntCached148 cntCached317
private def cntCached1466 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached919 cntCached1277 cntCached1416
private def cntCached1467 : T6 := .node cntCached0 cntCached446 cntCached919 cntCached433 cntCached1067 cntCached1077
private def cntCached1468 : T6 := .node cntCached0 cntCached564 cntCached1075 cntCached920 cntCached1071 cntCached1079
private def cntCached1469 : T6 := .node cntCached1 cntCached1465 cntCached1466 cntCached1467 cntCached1436 cntCached1468
private def cntCached1470 : T6 := .node cntCached0 cntCached72 cntCached274 cntCached886 cntCached1051 cntCached1456
private def cntCached1471 : T6 := .leaf 308
private def cntCached1472 : T6 := .node cntCached0 cntCached519 cntCached578 cntCached1075 cntCached1156 cntCached1471
private def cntCached1473 : T6 := .leaf 394
private def cntCached1474 : T6 := .node cntCached0 cntCached392 cntCached1075 cntCached1077 cntCached1450 cntCached1473
private def cntCached1475 : T6 := .leaf 309
private def cntCached1476 : T6 := .leaf 493
private def cntCached1477 : T6 := .node cntCached0 cntCached572 cntCached1475 cntCached1079 cntCached1452 cntCached1476
private def cntCached1478 : T6 := .node cntCached1 cntCached1470 cntCached1472 cntCached1474 cntCached1453 cntCached1477
private def cntCached1479 : T6 := .node cntCached2 cntCached1458 cntCached1464 cntCached1469 cntCached1454 cntCached1478
private def cntCached1480 : T6 := .node cntCached3 cntCached1357 cntCached1386 cntCached1420 cntCached1455 cntCached1479
private def cntCached1481 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached34 cntCached26 cntCached194
private def cntCached1482 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached198 cntCached206 cntCached208
private def cntCached1483 : T6 := .node cntCached0 cntCached38 cntCached94 cntCached438 cntCached112 cntCached79
private def cntCached1484 : T6 := .node cntCached0 cntCached46 cntCached292 cntCached290 cntCached593 cntCached244
private def cntCached1485 : T6 := .node cntCached1 cntCached1481 cntCached1482 cntCached1483 cntCached1339 cntCached1484
private def cntCached1486 : T6 := .node cntCached0 cntCached224 cntCached46 cntCached302 cntCached141 cntCached253
private def cntCached1487 : T6 := .node cntCached0 cntCached220 cntCached100 cntCached326 cntCached267 cntCached127
private def cntCached1488 : T6 := .node cntCached0 cntCached206 cntCached79 cntCached1002 cntCached472 cntCached919
private def cntCached1489 : T6 := .node cntCached1 cntCached974 cntCached1486 cntCached1487 cntCached1344 cntCached1488
private def cntCached1490 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached69 cntCached331 cntCached257
private def cntCached1491 : T6 := .node cntCached0 cntCached89 cntCached65 cntCached253 cntCached549 cntCached562
private def cntCached1492 : T6 := .node cntCached0 cntCached69 cntCached235 cntCached335 cntCached392 cntCached977
private def cntCached1493 : T6 := .node cntCached0 cntCached296 cntCached307 cntCached1029 cntCached572 cntCached1248
private def cntCached1494 : T6 := .node cntCached1 cntCached1490 cntCached1491 cntCached1492 cntCached1355 cntCached1493
private def cntCached1495 : T6 := .node cntCached2 cntCached77 cntCached1485 cntCached1489 cntCached1356 cntCached1494
private def cntCached1496 : T6 := .node cntCached0 cntCached89 cntCached208 cntCached79 cntCached593 cntCached244
private def cntCached1497 : T6 := .node cntCached1 cntCached47 cntCached529 cntCached982 cntCached1359 cntCached1496
private def cntCached1498 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached89 cntCached139 cntCached110
private def cntCached1499 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached208 cntCached229 cntCached143
private def cntCached1500 : T6 := .node cntCached0 cntCached198 cntCached65 cntCached304 cntCached1002 cntCached700
private def cntCached1501 : T6 := .node cntCached0 cntCached65 cntCached237 cntCached564 cntCached546 cntCached552
private def cntCached1502 : T6 := .node cntCached1 cntCached1498 cntCached1499 cntCached1500 cntCached1365 cntCached1501
private def cntCached1503 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached302 cntCached141 cntCached253
private def cntCached1504 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached124 cntCached260 cntCached424
private def cntCached1505 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached447 cntCached847 cntCached849
private def cntCached1506 : T6 := .node cntCached0 cntCached332 cntCached700 cntCached876 cntCached1003 cntCached1009
private def cntCached1507 : T6 := .node cntCached1 cntCached1503 cntCached1504 cntCached1505 cntCached1371 cntCached1506
private def cntCached1508 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached124 cntCached237 cntCached447
private def cntCached1509 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached156 cntCached905 cntCached1456
private def cntCached1510 : T6 := .node cntCached0 cntCached253 cntCached700 cntCached849 cntCached1308 cntCached1314
private def cntCached1511 : T6 := .node cntCached0 cntCached155 cntCached884 cntCached1009 cntCached1383 cntCached1099
private def cntCached1512 : T6 := .node cntCached1 cntCached1508 cntCached1509 cntCached1510 cntCached1384 cntCached1511
private def cntCached1513 : T6 := .node cntCached2 cntCached1497 cntCached1502 cntCached1507 cntCached1385 cntCached1512
private def cntCached1514 : T6 := .node cntCached0 cntCached139 cntCached253 cntCached390 cntCached317 cntCached399
private def cntCached1515 : T6 := .node cntCached1 cntCached63 cntCached557 cntCached1014 cntCached1388 cntCached1514
private def cntCached1516 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached62 cntCached296 cntCached124
private def cntCached1517 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached79 cntCached127 cntCached778
private def cntCached1518 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached307 cntCached1029 cntCached913
private def cntCached1519 : T6 := .node cntCached0 cntCached124 cntCached392 cntCached924 cntCached1075 cntCached1097
private def cntCached1520 : T6 := .node cntCached1 cntCached1516 cntCached1517 cntCached1518 cntCached1394 cntCached1519
private def cntCached1521 : T6 := .node cntCached0 cntCached55 cntCached510 cntCached105 cntCached125 cntCached390
private def cntCached1522 : T6 := .node cntCached0 cntCached284 cntCached304 cntCached268 cntCached977 cntCached876
private def cntCached1523 : T6 := .node cntCached0 cntCached345 cntCached268 cntCached171 cntCached947 cntCached1039
private def cntCached1524 : T6 := .node cntCached0 cntCached335 cntCached913 cntCached878 cntCached1034 cntCached1041
private def cntCached1525 : T6 := .node cntCached1 cntCached1521 cntCached1522 cntCached1523 cntCached1400 cntCached1524
private def cntCached1526 : T6 := .node cntCached0 cntCached62 cntCached265 cntCached155 cntCached317 cntCached399
private def cntCached1527 : T6 := .leaf 257
private def cntCached1528 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached913 cntCached346 cntCached1527
private def cntCached1529 : T6 := .leaf 333
private def cntCached1530 : T6 := .node cntCached0 cntCached260 cntCached913 cntCached1039 cntCached1414 cntCached1529
private def cntCached1531 : T6 := .leaf 258
private def cntCached1532 : T6 := .leaf 427
private def cntCached1533 : T6 := .node cntCached0 cntCached977 cntCached1531 cntCached1041 cntCached1417 cntCached1532
private def cntCached1534 : T6 := .node cntCached1 cntCached1526 cntCached1528 cntCached1530 cntCached1418 cntCached1533
private def cntCached1535 : T6 := .node cntCached2 cntCached1515 cntCached1520 cntCached1525 cntCached1419 cntCached1534
private def cntCached1536 : T6 := .node cntCached0 cntCached257 cntCached447 cntCached399 cntCached1456 cntCached951
private def cntCached1537 : T6 := .node cntCached1 cntCached76 cntCached629 cntCached1083 cntCached1457 cntCached1536
private def cntCached1538 : T6 := .node cntCached0 cntCached46 cntCached115 cntCached79 cntCached120 cntCached307
private def cntCached1539 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached392 cntCached161 cntCached884
private def cntCached1540 : T6 := .node cntCached0 cntCached332 cntCached392 cntCached924 cntCached1075 cntCached1097
private def cntCached1541 : T6 := .leaf 340
private def cntCached1542 : T6 := .node cntCached0 cntCached268 cntCached941 cntCached586 cntCached1462 cntCached1541
private def cntCached1543 : T6 := .node cntCached1 cntCached1538 cntCached1539 cntCached1540 cntCached1463 cntCached1542
private def cntCached1544 : T6 := .node cntCached0 cntCached62 cntCached408 cntCached155 cntCached317 cntCached399
private def cntCached1545 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached173 cntCached1416 cntCached1531
private def cntCached1546 : T6 := .node cntCached0 cntCached335 cntCached173 cntCached926 cntCached1077 cntCached1099
private def cntCached1547 : T6 := .node cntCached0 cntCached1029 cntCached1097 cntCached928 cntCached1079 cntCached1101
private def cntCached1548 : T6 := .node cntCached1 cntCached1544 cntCached1545 cntCached1546 cntCached1468 cntCached1547
private def cntCached1549 : T6 := .node cntCached0 cntCached75 cntCached774 cntCached497 cntCached1456 cntCached951
private def cntCached1550 : T6 := .leaf 338
private def cntCached1551 : T6 := .node cntCached0 cntCached268 cntCached634 cntCached1097 cntCached1471 cntCached1550
private def cntCached1552 : T6 := .leaf 428
private def cntCached1553 : T6 := .node cntCached0 cntCached977 cntCached1097 cntCached1099 cntCached1473 cntCached1552
private def cntCached1554 : T6 := .leaf 339
private def cntCached1555 : T6 := .leaf 528
private def cntCached1556 : T6 := .node cntCached0 cntCached1248 cntCached1554 cntCached1101 cntCached1476 cntCached1555
private def cntCached1557 : T6 := .node cntCached1 cntCached1549 cntCached1551 cntCached1553 cntCached1477 cntCached1556
private def cntCached1558 : T6 := .node cntCached2 cntCached1537 cntCached1543 cntCached1548 cntCached1478 cntCached1557
private def cntCached1559 : T6 := .node cntCached3 cntCached1495 cntCached1513 cntCached1535 cntCached1479 cntCached1558
private def cntCached1560 : T6 := .node cntCached4 cntCached184 cntCached1284 cntCached1334 cntCached1480 cntCached1559
private def cntCached1561 : T6 := .node cntCached0 cntCached11 cntCached21 cntCached53 cntCached89 cntCached215
private def cntCached1562 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached46 cntCached284 cntCached102
private def cntCached1563 : T6 := .node cntCached0 cntCached26 cntCached139 cntCached102 cntCached124 cntCached306
private def cntCached1564 : T6 := .node cntCached1 cntCached369 cntCached1561 cntCached1562 cntCached1190 cntCached1563
private def cntCached1565 : T6 := .node cntCached0 cntCached21 cntCached212 cntCached49 cntCached110 cntCached296
private def cntCached1566 : T6 := .node cntCached0 cntCached53 cntCached215 cntCached251 cntCached253 cntCached446
private def cntCached1567 : T6 := .node cntCached0 cntCached94 cntCached511 cntCached446 cntCached155 cntCached910
private def cntCached1568 : T6 := .node cntCached1 cntCached657 cntCached1565 cntCached1566 cntCached1199 cntCached1567
private def cntCached1569 : T6 := .node cntCached2 cntCached51 cntCached653 cntCached1564 cntCached1200 cntCached1568
private def cntCached1570 : T6 := .node cntCached0 cntCached34 cntCached194 cntCached206 cntCached115 cntCached340
private def cntCached1571 : T6 := .node cntCached1 cntCached35 cntCached195 cntCached249 cntCached1203 cntCached1570
private def cntCached1572 : T6 := .node cntCached0 cntCached13 cntCached224 cntCached220 cntCached57 cntCached510
private def cntCached1573 : T6 := .node cntCached0 cntCached85 cntCached44 cntCached222 cntCached65 cntCached242
private def cntCached1574 : T6 := .node cntCached0 cntCached89 cntCached331 cntCached253 cntCached519 cntCached416
private def cntCached1575 : T6 := .node cntCached1 cntCached665 cntCached1572 cntCached1573 cntCached1208 cntCached1574
private def cntCached1576 : T6 := .node cntCached0 cntCached69 cntCached242 cntCached432 cntCached564 cntCached455
private def cntCached1577 : T6 := .node cntCached1 cntCached370 cntCached671 cntCached672 cntCached1211 cntCached1576
private def cntCached1578 : T6 := .node cntCached0 cntCached212 cntCached70 cntCached670 cntCached479 cntCached268
private def cntCached1579 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached593 cntCached700 cntCached570
private def cntCached1580 : T6 := .node cntCached1 cntCached658 cntCached1578 cntCached1579 cntCached553 cntCached677
private def cntCached1581 : T6 := .node cntCached2 cntCached1571 cntCached1575 cntCached1577 cntCached1218 cntCached1580
private def cntCached1582 : T6 := .node cntCached0 cntCached92 cntCached69 cntCached257 cntCached290 cntCached549
private def cntCached1583 : T6 := .node cntCached1 cntCached41 cntCached249 cntCached747 cntCached1221 cntCached1582
private def cntCached1584 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached115 cntCached408 cntCached410
private def cntCached1585 : T6 := .node cntCached0 cntCached324 cntCached253 cntCached260 cntCached151 cntCached276
private def cntCached1586 : T6 := .node cntCached1 cntCached682 cntCached1573 cntCached1584 cntCached1225 cntCached1585
private def cntCached1587 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached65 cntCached290 cntCached432
private def cntCached1588 : T6 := .node cntCached0 cntCached281 cntCached65 cntCached265 cntCached416 cntCached418
private def cntCached1589 : T6 := .node cntCached0 cntCached141 cntCached410 cntCached489 cntCached457 cntCached491
private def cntCached1590 : T6 := .node cntCached1 cntCached686 cntCached1587 cntCached1588 cntCached1230 cntCached1589
private def cntCached1591 : T6 := .node cntCached0 cntCached125 cntCached497 cntCached433 cntCached639 cntCached711
private def cntCached1592 : T6 := .node cntCached1 cntCached692 cntCached693 cntCached694 cntCached1235 cntCached1591
private def cntCached1593 : T6 := .node cntCached2 cntCached1583 cntCached1586 cntCached1590 cntCached1236 cntCached1592
private def cntCached1594 : T6 := .node cntCached0 cntCached222 cntCached340 cntCached535 cntCached148 cntCached472
private def cntCached1595 : T6 := .node cntCached1 cntCached50 cntCached327 cntCached790 cntCached1266 cntCached1594
private def cntCached1596 : T6 := .node cntCached0 cntCached55 cntCached331 cntCached253 cntCached519 cntCached416
private def cntCached1597 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached260 cntCached151 cntCached276
private def cntCached1598 : T6 := .node cntCached0 cntCached326 cntCached148 cntCached337 cntCached319 cntCached346
private def cntCached1599 : T6 := .node cntCached1 cntCached703 cntCached1596 cntCached1597 cntCached1270 cntCached1598
private def cntCached1600 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached274 cntCached449 cntCached484
private def cntCached1601 : T6 := .node cntCached0 cntCached141 cntCached274 cntCached600 cntCached165 cntCached802
private def cntCached1602 : T6 := .leaf 294
private def cntCached1603 : T6 := .node cntCached0 cntCached479 cntCached276 cntCached799 cntCached1274 cntCached1602
private def cntCached1604 : T6 := .node cntCached1 cntCached709 cntCached1600 cntCached1601 cntCached1275 cntCached1603
private def cntCached1605 : T6 := .node cntCached0 cntCached345 cntCached342 cntCached484 cntCached1277 cntCached180
private def cntCached1606 : T6 := .node cntCached0 cntCached125 cntCached484 cntCached491 cntCached473 cntCached498
private def cntCached1607 : T6 := .leaf 374
private def cntCached1608 : T6 := .node cntCached0 cntCached778 cntCached1308 cntCached803 cntCached1280 cntCached1607
private def cntCached1609 : T6 := .node cntCached1 cntCached714 cntCached1605 cntCached1606 cntCached1281 cntCached1608
private def cntCached1610 : T6 := .node cntCached2 cntCached1595 cntCached1599 cntCached1604 cntCached1282 cntCached1609
private def cntCached1611 : T6 := .node cntCached3 cntCached1569 cntCached1581 cntCached1593 cntCached1283 cntCached1610
private def cntCached1612 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached60 cntCached324 cntCached115
private def cntCached1613 : T6 := .node cntCached0 cntCached224 cntCached46 cntCached100 cntCached345 cntCached265
private def cntCached1614 : T6 := .node cntCached0 cntCached198 cntCached102 cntCached258 cntCached335 cntCached993
private def cntCached1615 : T6 := .node cntCached1 cntCached826 cntCached1612 cntCached1613 cntCached1288 cntCached1614
private def cntCached1616 : T6 := .node cntCached0 cntCached26 cntCached139 cntCached115 cntCached242 cntCached561
private def cntCached1617 : T6 := .node cntCached0 cntCached60 cntCached292 cntCached408 cntCached274 cntCached829
private def cntCached1618 : T6 := .node cntCached0 cntCached438 cntCached267 cntCached130 cntCached847 cntCached1051
private def cntCached1619 : T6 := .node cntCached1 cntCached1115 cntCached1616 cntCached1617 cntCached1297 cntCached1618
private def cntCached1620 : T6 := .node cntCached2 cntCached67 cntCached1110 cntCached1615 cntCached1298 cntCached1619
private def cntCached1621 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached110 cntCached332 cntCached519
private def cntCached1622 : T6 := .node cntCached0 cntCached60 cntCached331 cntCached235 cntCached155 cntCached317
private def cntCached1623 : T6 := .node cntCached0 cntCached251 cntCached293 cntCached134 cntCached849 cntCached855
private def cntCached1624 : T6 := .node cntCached1 cntCached1128 cntCached1621 cntCached1622 cntCached1303 cntCached1623
private def cntCached1625 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached120 cntCached424 cntCached1029
private def cntCached1626 : T6 := .leaf 209
private def cntCached1627 : T6 := .node cntCached0 cntCached115 cntCached293 cntCached317 cntCached1312 cntCached1626
private def cntCached1628 : T6 := .node cntCached0 cntCached463 cntCached911 cntCached855 cntCached1314 cntCached1257
private def cntCached1629 : T6 := .node cntCached1 cntCached1134 cntCached1625 cntCached1627 cntCached1315 cntCached1628
private def cntCached1630 : T6 := .node cntCached2 cntCached681 cntCached1127 cntCached1624 cntCached1316 cntCached1629
private def cntCached1631 : T6 := .node cntCached0 cntCached198 cntCached208 cntCached290 cntCached307 cntCached882
private def cntCached1632 : T6 := .node cntCached0 cntCached102 cntCached146 cntCached687 cntCached924 cntCached947
private def cntCached1633 : T6 := .node cntCached1 cntCached1143 cntCached1125 cntCached1631 cntCached1320 cntCached1632
private def cntCached1634 : T6 := .node cntCached2 cntCached1142 cntCached1633 cntCached1152 cntCached1043 cntCached1160
private def cntCached1635 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached432 cntCached392 cntCached399
private def cntCached1636 : T6 := .node cntCached0 cntCached292 cntCached146 cntCached687 cntCached924 cntCached947
private def cntCached1637 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached433 cntCached586 cntCached695
private def cntCached1638 : T6 := .node cntCached1 cntCached1165 cntCached1635 cntCached1636 cntCached1331 cntCached1637
private def cntCached1639 : T6 := .node cntCached2 cntCached1164 cntCached1638 cntCached1175 cntCached1103 cntCached1183
private def cntCached1640 : T6 := .node cntCached3 cntCached1620 cntCached1630 cntCached1634 cntCached1333 cntCached1639
private def cntCached1641 : T6 := .node cntCached0 cntCached13 cntCached34 cntCached26 cntCached194 cntCached94
private def cntCached1642 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached69 cntCached208 cntCached112
private def cntCached1643 : T6 := .node cntCached0 cntCached40 cntCached96 cntCached257 cntCached79 cntCached143
private def cntCached1644 : T6 := .node cntCached0 cntCached49 cntCached75 cntCached549 cntCached244 cntCached700
private def cntCached1645 : T6 := .node cntCached1 cntCached1641 cntCached1642 cntCached1643 cntCached1484 cntCached1644
private def cntCached1646 : T6 := .node cntCached0 cntCached87 cntCached206 cntCached292 cntCached253 cntCached446
private def cntCached1647 : T6 := .node cntCached0 cntCached46 cntCached141 cntCached117 cntCached127 cntCached309
private def cntCached1648 : T6 := .node cntCached0 cntCached70 cntCached143 cntCached915 cntCached919 cntCached464
private def cntCached1649 : T6 := .node cntCached1 cntCached1115 cntCached1646 cntCached1647 cntCached1488 cntCached1648
private def cntCached1650 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached510 cntCached257 cntCached670
private def cntCached1651 : T6 := .node cntCached0 cntCached57 cntCached345 cntCached446 cntCached562 cntCached915
private def cntCached1652 : T6 := .node cntCached0 cntCached510 cntCached125 cntCached993 cntCached977 cntCached578
private def cntCached1653 : T6 := .node cntCached0 cntCached396 cntCached156 cntCached606 cntCached1248 cntCached1003
private def cntCached1654 : T6 := .node cntCached1 cntCached1650 cntCached1651 cntCached1652 cntCached1493 cntCached1653
private def cntCached1655 : T6 := .node cntCached2 cntCached81 cntCached1645 cntCached1649 cntCached1494 cntCached1654
private def cntCached1656 : T6 := .node cntCached0 cntCached57 cntCached112 cntCached143 cntCached244 cntCached700
private def cntCached1657 : T6 := .node cntCached1 cntCached50 cntCached663 cntCached1121 cntCached1496 cntCached1656
private def cntCached1658 : T6 := .node cntCached0 cntCached34 cntCached194 cntCached215 cntCached110 cntCached296
private def cntCached1659 : T6 := .node cntCached0 cntCached194 cntCached70 cntCached670 cntCached143 cntCached447
private def cntCached1660 : T6 := .node cntCached0 cntCached69 cntCached242 cntCached146 cntCached700 cntCached570
private def cntCached1661 : T6 := .node cntCached0 cntCached345 cntCached244 cntCached455 cntCached552 cntCached615
private def cntCached1662 : T6 := .node cntCached1 cntCached1658 cntCached1659 cntCached1660 cntCached1501 cntCached1661
private def cntCached1663 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached292 cntCached253 cntCached446
private def cntCached1664 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached120 cntCached424 cntCached1029
private def cntCached1665 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached134 cntCached849 cntCached855
private def cntCached1666 : T6 := .node cntCached0 cntCached267 cntCached570 cntCached1131 cntCached1009 cntCached1137
private def cntCached1667 : T6 := .node cntCached1 cntCached1663 cntCached1664 cntCached1665 cntCached1506 cntCached1666
private def cntCached1668 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached306 cntCached447 cntCached569
private def cntCached1669 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached919 cntCached1456 cntCached802
private def cntCached1670 : T6 := .node cntCached0 cntCached446 cntCached570 cntCached855 cntCached1314 cntCached1257
private def cntCached1671 : T6 := .leaf 221
private def cntCached1672 : T6 := .leaf 365
private def cntCached1673 : T6 := .node cntCached0 cntCached910 cntCached1671 cntCached1137 cntCached1099 cntCached1672
private def cntCached1674 : T6 := .node cntCached1 cntCached1668 cntCached1669 cntCached1670 cntCached1511 cntCached1673
private def cntCached1675 : T6 := .node cntCached2 cntCached1657 cntCached1662 cntCached1667 cntCached1512 cntCached1674
private def cntCached1676 : T6 := .leaf 179
private def cntCached1677 : T6 := .node cntCached0 cntCached438 cntCached446 cntCached910 cntCached399 cntCached1676
private def cntCached1678 : T6 := .node cntCached1 cntCached66 cntCached680 cntCached1141 cntCached1514 cntCached1677
private def cntCached1679 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached72 cntCached124 cntCached306
private def cntCached1680 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached593 cntCached778 cntCached911
private def cntCached1681 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached882 cntCached913 cntCached1154
private def cntCached1682 : T6 := .node cntCached0 cntCached306 cntCached399 cntCached947 cntCached1097 cntCached1177
private def cntCached1683 : T6 := .node cntCached1 cntCached1679 cntCached1680 cntCached1681 cntCached1519 cntCached1682
private def cntCached1684 : T6 := .node cntCached0 cntCached57 cntCached296 cntCached389 cntCached390 cntCached910
private def cntCached1685 : T6 := .node cntCached0 cntCached102 cntCached146 cntCached886 cntCached876 cntCached1131
private def cntCached1686 : T6 := .node cntCached0 cntCached265 cntCached886 cntCached884 cntCached1039 cntCached1156
private def cntCached1687 : T6 := .node cntCached0 cntCached993 cntCached1154 cntCached887 cntCached1041 cntCached1158
private def cntCached1688 : T6 := .node cntCached1 cntCached1684 cntCached1685 cntCached1686 cntCached1524 cntCached1687
private def cntCached1689 : T6 := .node cntCached0 cntCached65 cntCached237 cntCached424 cntCached399 cntCached1676
private def cntCached1690 : T6 := .leaf 286
private def cntCached1691 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached1154 cntCached1527 cntCached1690
private def cntCached1692 : T6 := .leaf 366
private def cntCached1693 : T6 := .node cntCached0 cntCached130 cntCached1154 cntCached1156 cntCached1529 cntCached1692
private def cntCached1694 : T6 := .leaf 287
private def cntCached1695 : T6 := .leaf 461
private def cntCached1696 : T6 := .node cntCached0 cntCached578 cntCached1694 cntCached1158 cntCached1532 cntCached1695
private def cntCached1697 : T6 := .node cntCached1 cntCached1689 cntCached1691 cntCached1693 cntCached1533 cntCached1696
private def cntCached1698 : T6 := .node cntCached2 cntCached1678 cntCached1683 cntCached1688 cntCached1534 cntCached1697
private def cntCached1699 : T6 := .node cntCached0 cntCached670 cntCached569 cntCached1676 cntCached951 cntCached609
private def cntCached1700 : T6 := .node cntCached1 cntCached80 cntCached701 cntCached1163 cntCached1536 cntCached1699
private def cntCached1701 : T6 := .node cntCached0 cntCached49 cntCached340 cntCached143 cntCached307 cntCached156
private def cntCached1702 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached399 cntCached884 cntCached1671
private def cntCached1703 : T6 := .node cntCached0 cntCached267 cntCached399 cntCached947 cntCached1097 cntCached1177
private def cntCached1704 : T6 := .leaf 223
private def cntCached1705 : T6 := .leaf 370
private def cntCached1706 : T6 := .node cntCached0 cntCached424 cntCached1704 cntCached695 cntCached1541 cntCached1705
private def cntCached1707 : T6 := .node cntCached1 cntCached1701 cntCached1702 cntCached1703 cntCached1542 cntCached1706
private def cntCached1708 : T6 := .node cntCached0 cntCached65 cntCached535 cntCached424 cntCached399 cntCached1676
private def cntCached1709 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached951 cntCached1531 cntCached1694
private def cntCached1710 : T6 := .node cntCached0 cntCached993 cntCached951 cntCached949 cntCached1099 cntCached1179
private def cntCached1711 : T6 := .node cntCached0 cntCached606 cntCached1177 cntCached952 cntCached1101 cntCached1181
private def cntCached1712 : T6 := .node cntCached1 cntCached1708 cntCached1709 cntCached1710 cntCached1547 cntCached1711
private def cntCached1713 : T6 := .node cntCached0 cntCached79 cntCached449 cntCached1312 cntCached951 cntCached609
private def cntCached1714 : T6 := .node cntCached0 cntCached424 cntCached706 cntCached1177 cntCached1550 cntCached1179
private def cntCached1715 : T6 := .leaf 462
private def cntCached1716 : T6 := .node cntCached0 cntCached578 cntCached1177 cntCached1179 cntCached1552 cntCached1715
private def cntCached1717 : T6 := .leaf 563
private def cntCached1718 : T6 := .node cntCached0 cntCached1003 cntCached952 cntCached1181 cntCached1555 cntCached1717
private def cntCached1719 : T6 := .node cntCached1 cntCached1713 cntCached1714 cntCached1716 cntCached1556 cntCached1718
private def cntCached1720 : T6 := .node cntCached2 cntCached1700 cntCached1707 cntCached1712 cntCached1557 cntCached1719
private def cntCached1721 : T6 := .node cntCached3 cntCached1655 cntCached1675 cntCached1698 cntCached1558 cntCached1720
private def cntCached1722 : T6 := .node cntCached4 cntCached189 cntCached1611 cntCached1640 cntCached1559 cntCached1721
private def cntCached1723 : T6 := .node cntCached5 cntCached190 cntCached722 cntCached1186 cntCached1560 cntCached1722

private theorem cntT_cached_eq : cntT = cntCached1723 := by rfl
private theorem coveragePacked_cached_eq (hb j : Nat) :
    coveragePacked hb j = maxHistT hb cntCached1723
      (dT (mapT (fun z => z ^ j) cntCached1723)) :=
  congrArg (fun c => maxHistT hb c (dT (mapT (fun z => z ^ j) c))) cntT_cached_eq
theorem coverageH1_packed : coveragePacked (2^128) 1 = coverageHPack (2^128) 1 := by
  exact (coveragePacked_cached_eq (2^128) 1).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 1) cntCached1723)) =
      coverageHPack (2^128) 1 by decide +kernel)
theorem coverageH2_packed : coveragePacked (2^128) 2 = coverageHPack (2^128) 2 := by
  exact (coveragePacked_cached_eq (2^128) 2).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 2) cntCached1723)) =
      coverageHPack (2^128) 2 by decide +kernel)
theorem coverageH3_packed : coveragePacked (2^128) 3 = coverageHPack (2^128) 3 := by
  exact (coveragePacked_cached_eq (2^128) 3).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 3) cntCached1723)) =
      coverageHPack (2^128) 3 by decide +kernel)
theorem coverageH4_packed : coveragePacked (2^128) 4 = coverageHPack (2^128) 4 := by
  exact (coveragePacked_cached_eq (2^128) 4).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 4) cntCached1723)) =
      coverageHPack (2^128) 4 by decide +kernel)
theorem coverageH5_packed : coveragePacked (2^128) 5 = coverageHPack (2^128) 5 := by
  exact (coveragePacked_cached_eq (2^128) 5).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 5) cntCached1723)) =
      coverageHPack (2^128) 5 by decide +kernel)
theorem coverageH6_packed : coveragePacked (2^128) 6 = coverageHPack (2^128) 6 := by
  exact (coveragePacked_cached_eq (2^128) 6).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 6) cntCached1723)) =
      coverageHPack (2^128) 6 by decide +kernel)
theorem coverageH7_packed : coveragePacked (2^128) 7 = coverageHPack (2^128) 7 := by
  exact (coveragePacked_cached_eq (2^128) 7).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 7) cntCached1723)) =
      coverageHPack (2^128) 7 by decide +kernel)
theorem coverageH8_packed : coveragePacked (2^128) 8 = coverageHPack (2^128) 8 := by
  exact (coveragePacked_cached_eq (2^128) 8).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 8) cntCached1723)) =
      coverageHPack (2^128) 8 by decide +kernel)
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (fact)
def winsorBinCheck : Bool :=
  (List.range 4096).all (fun c =>
    c * 50 ^ coverageBin c ≤ 51 ^ coverageBin c &&
      (c ≤ 1 || 51 ^ (coverageBin c - 1) < c * 50 ^ (coverageBin c - 1)))
def winsorMassCheck (r : Nat) : Bool :=
  coverageRetainedFastPack 1 r ≤ xNum r && xNum r < 2^512
def winsorRowDots (r : Nat) : Nat × Nat :=
  if r ≤ 20 then
    let v := winsorPackedSums winsorMGFPayData winsorResidualPayData (coverageProductLinear r)
    let missed := xNum r ^ 9 - v.1
    (v.2.1 + 3000 * winsorScale * missed, v.2.2 + winsorScale * missed)
  else (3000 * winsorScale * xNum r ^ 9, winsorScale * xNum r ^ 9)
def winsorRowBounds (r : Nat) : Nat × Nat :=
  let dots := winsorRowDots r
  let num := 1353 * 2^24 * 13533529 * LN^r
  let den := 100000000 * LD^r * fact r * Q^(9*r)
  (winsorCeil (num * dots.1) den, winsorCeil (num * dots.2) den)
def winsorTailBound : Nat := winsorCeil (winsorScale * A * LN^81) (LD^81 * fact 81)
def winsorBounds : Nat × Nat :=
  (List.range 81).foldr (fun r p =>
    let b := winsorRowBounds r
    (b.1 + p.1, b.2 + p.2)) (3000*winsorTailBound,winsorTailBound)
def winsorCheck : Bool := winsorBounds.1 ≤ 8*winsorScale && 5000*winsorBounds.2 ≤ winsorScale
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
theorem coverageH_packed (j : ℕ) (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    coveragePacked (2^128) j = coverageHPack (2^128) j := by
  interval_cases j
  · exact coverageH1_packed
  · exact coverageH2_packed
  · exact coverageH3_packed
  · exact coverageH4_packed
  · exact coverageH5_packed
  · exact coverageH6_packed
  · exact coverageH7_packed
  · exact coverageH8_packed
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
def winsorBinFastCheck : Bool := coverageBinData.toList.zipIdx.all (fun e =>
    e.2*50^e.1 ≤ 51^e.1 && (e.2≤1 || 51^(e.1-1)<e.2*50^(e.1-1)))
set_option maxHeartbeats 20000000 in
theorem winsor_bins_fast_ok : winsorBinFastCheck = true := by decide +kernel
theorem coverageBinData_length : coverageBinData.toList.length = 4096 := by decide +kernel

theorem winsor_bins_ok :
    (List.range 4096).all (fun c =>
      c*50^coverageBin c ≤ 51^coverageBin c &&
      (c≤1 || 51^(coverageBin c-1)<c*50^(coverageBin c-1))) = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have hcl : c < coverageBinData.toList.length := by rw [coverageBinData_length]; exact List.mem_range.mp hc
  have he : (coverageBinData.toList[c],c) ∈ coverageBinData.toList.zipIdx := by
    have hh := List.getElem_mem (l:=coverageBinData.toList.zipIdx) (n:=c) (by simpa using hcl)
    simpa only [List.getElem_zipIdx, Nat.zero_add] using hh
  have h := List.all_eq_true.mp winsor_bins_fast_ok _ he
  have hv : coverageBin c = coverageBinData.toList[c] := by
    unfold coverageBin
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hcl]
    rfl
  simpa only [hv] using h

set_option maxHeartbeats 50000000 in
theorem winsor_pay_ok : winsorPayChecks = true := by decide +kernel
set_option maxHeartbeats 10000000 in
theorem winsor_masses_ok : (List.range 31).all winsorMassCheck = true := by decide +kernel
 theorem winsor_mgf_length : winsorMGFPayData.length = 2201 := by decide +kernel
 theorem winsor_residual_length : winsorResidualPayData.length = 2201 := by decide +kernel
set_option maxHeartbeats 20000000 in
 theorem winsor_pay_bounds : (winsorMGFPayData.zip winsorResidualPayData).all (fun e =>
    e.1 ≤ 3000*winsorScale && e.2 ≤ winsorScale) = true := by decide +kernel

def winsorCertifiedDots : Nat → Nat × Nat
  | 0 => (0,0)
  | 1 => (4304737466716198510902241657960411531101456204344222518,0)
  | 2 => (350464637810563205369907563362523142509281712838984639932768546697035546336664706139336588019512066150,2888165470991626549199529039083531863264948425070934777887408472582447767798253060096)
  | 3 => (1895703571804125441214450143611836933078843758950134443446042258877697783652081956257407727728190683334704551063908457834398852571219726486921159996,62287870725601012024002656658515934843466026802510578737981090426695828618785279699684531970375057361187569703755677003792003834046208)
  | 4 => (3220580229176428969370891728583851897999938295872671679399914606894513100298639912517261082457313673860356696266069895581746799270647068774005068850559155716884979872182248647379227484467260050,10244491628795906586495039879542062987848972671687185128386860672648830086956288445437624598722629850381356980168615551174410216707866502124436788698838362301053728995085173112067072)
  | 5 => (2824450701398056004061588399518555732129048764845132424777153531334773954080030974285554067027764432860718547752880785851159213189784511244253124006859028224701520048499967739707675346128333059719716937550424279546152449064894080428826748,240784386167233085499040533825714364552977736060006293802912080753331833095717394732987844033955580739440361806384157018114772443009628429778799307057564711905256189484682874729305227996406295117588118543556593777925774620000000)
  | 6 => (1604232661042295161239019559395787050549041727028847825804676721305719216563973895671719424839936519971810578447191680235081746453229491647490077943438518492480067757601443423445962548965744796942697913646034712518069353742645665904466166276510387587190490211508374211717486886723210,1911608055636490856136213788713501870232755968024665606639179248330110910784362726997035999724114698955862222116107498854311665606439446939667069418124483407772515462313116438306547605710180449636764038052060469585246191023495491715929118641894291544190348896365414895256576)
  | 7 => (668251685456412308496042892300019187639448250676704603766840176909480245840076447916937857582541696653788901652472008729875965602336569804549285555716162000622947175330976310377754609741323852801196556390777171961491898361789635540736408012252600965509914401892788558245555121161380774377495042625328477081703112801925585576676,7399000317643339632052240559200041630603785025821163455064117274928459707400528301933091604006246506457830020155900844922254034497589601109897365096457440882524747971199441132952427872320568591849615431341786161220125082030070507001569389146079635616372301293729538490397777846305015444457039178294778284561684606879488)
  | 8 => (220493847321206163188491122369839907726174567156458082607227244288376302136203924576546496610665398217903665959210422088084117721605576910124478941136966196577295843935666377066748846278409490310290060549182841665371860123998902559152794096596944566065343513764810813667267157875855902707607279392414848586241605886479728470481211681758684142166794165956254317586461373810,17223773629393038673781156520736591286217487234574706977878614677364072649467692673923970693832247706855503383772797738158492019313682327490313449298237916264860328924508585707703154396798897669678984580467635645815804699713888749802864918472284782757191315782449043881614396738590560108446968399907556852615245131633606134255554436429854770291372541643051466662912)
  | 9 => (60816853358554839524738929113224518708098182734371075902081641185202861657114846025330880636446492500330824533219507870766913467959785953770792842180356776182449388193816490025112978764419120846523375024834211719840226687851035005780336301453108058508268435349449383330422493797204805928366276715489710550402607760226164464022218471390748694134210168834026838282449309115196898045600589616211524836207547913419795746,27039565886254044461175547684520086965285754920473846307253168795694495596443154063273942724081106826843372755671181685962507745286199972866936162439843001226546774497998507416933505973047441945394523636768945445169255509668356928969410269566075233454617708937155951608939363606076034966794056005572325688202862337411188048477828618537367135022044391427107151363919062193081259066965674907541199791251148161536)
  | 10 => (14690446871398049064096790850511336218965320377583419759507350231105235563705652886215426401012056292900745353403497279701457267240533825752116480283895608223888598784797256394921412437301699871432237909190501175427605643635907961920138714208757418135325050087431306528429486053300310813678018611109770369056054492556076617887140979994926503580531154069826062491710689256206005587847645735110890065532635657996924172648297872095383004534354274964274167414958710,30328680605417344013385102722347207157126213834718126184435271879955973985941984152850779012779099923942934028894909499547436031357029960845984616401590549804058536798515142193208106934551480184269155743587490047646097583843936259097445801260780497685197778350867918072156199424119068819565308653227407652446602078060393085825882226214345166065654123238773963202035215810490194458144463139103599103485101791358078764641438641426322335035480093214952986624)
  | 11 => (3289519751596440350026864900981033603842659155750872547330845651725211393352435754970764247900307039265695920464604090434283207318004578298605569110169951139976486076346482843546318230242141666366791052532609282176317490229008136403379169053330492770652982506961988120798047176170537954220032125926421575198006015722506647238941223779577944978545959232063823040945186014285728715599861855487798384124947393912886123365572616449594108517771437761837771497686668666777214063084484187571838154485610455049776,26205086785701927000731032922307448592413371068380472870262256500053506154512459343103537140166886490308061228680831011026979381055912527532865162233463911841592105787679301610776876815580391425989728764844325255829278996711373096059364510241765319427845836574534167200509199223217684891998608832270889120294934705685660117090864863735042148566924836893475972220077999509106472175619352643367304485659849328507352325551261348011083977683465781087981912581234236838965709900822132720874334100626080512)
  | 12 => (740875843093287362151553328439344903668157020723175996423145100787232888612225678983149151616007509905929878440347429431579957385141766876840271276152405374651422970246162408900135181666480754913364395799736636079241163530454591274108240875545591624061818608980738522759674301126784090045578896743210686511981261868377109747264765784357571532797188384430468701890480080148415922152978104537358770629351518847670289535453479867021025524635197414758083140033288701014227866960164424915712280117351648968548104652503493441019680424319528866632316668390,17942417285562655174924127938444548270748805353448345586556594987958284715435387102276031103278464349560365949322539451656508314238952340326021281847029308099342273524358819187838659533542472477947253186891550372043201550740253634937610445617288377381909098228223627385760144753375494311107758633719809891630991908880011265521916022186338580491408543826168331927708312874258098397306528999065094140558468344195756097850779573366243889895701176508342463752013952409939674158735420721726498287068083889212874851672387872536429659164970050954403840)
  | 13 => (182289338147689926588129026463508197385752847697803742051481847030950457879664103414315484249339722670488789503475725363096374282368427694529499479940321613025916854127713353576190652669830465406869048832887039011860407400509022829797743040583767977666834422407700044036266246166132980589042638618520082429767294744534407077105973972059524428508263343815785771191489322780104140709847172557126720153188725625393181515489266542833734449241409523770540491087734687930029441287467769637160730774837945122791708350123966397891092100152400586967950967526838472319876608861528094341366815288479364292,9942507328702050800397305032787122281775132342561141490757598755573099382972702231901504121856088284505202282000305341009795507781333786813623923057519509640864438077129489039546314060821216046612313686641549538187728890086702010175370965829245694622627536682336215390238567396545228825162682004777286801002466288280421361680873049551945397116079465942735677056090291970096083099329780686925224336521396675324509319420962049138773733252207201793626141825993654994992868542399730835627555584476498600240077831481627067782885569506693966293013732966526963352680502913555724222865790266302720)
  | 14 => (49615271378259362648583881291595926903586268982458990276984492242568972169415076656313186293127166001462382929085559322625964435746836711618152003900035387590637810682401814458761961358732331318631681729310649116590769456463872141893264396316472308046015196676084005160309200407422827281284353521219262262482343796234794811913805464249910035935687147200275423717893884546781944833112106211195353946982827231754025833853647474809885578817019681059373870495968752244172202059661983889277352265146259005488010840898394353908979873447831488908387176470688985223862335074456547214170208472338356812750778690265827405703059582796980334901645002,4586336298749263199088025113817169913552000632301119440911554808777237972237997781980454586381869314750606695679767056836571105551222351493250613330106508066379560179826818154468977710109851144101743199930976534315887794280123652049906096824240800143981761850787055865075673853921952487587332351478476153166306225191331741970127216285275726441723417850221434830545667499500226765322956990520689188127671975599193128048979382579743322885820597872972283235732210397563048440480849515469138744029858427554064956291554199056766707084321830120610138141528213634793171540789086270091803355067215819198786124696560277340290191375535187570688)
  | 15 => (13795966909242820928357530060669849399827652001316281146780354361366456422802246895561007069845684626219210966720851581788882568803342271364862682890494732267571075603247618470339307970931806904647995919374528534274295616183653630569832180112839030887591454334875089464681928962121415313024805385516776613114169618833941856253383098297217170642221331409598414940381275668665883305318914928520025412386282888928980978425872590347846479366026452409856974530031750340218949254435321003630010160537584464998625578358247968743522888088522899341428091717634869985719427829462692364113315244492053987740366805874286990233301670567679941592844998374073930671737428117345326295805566379233000,1774210322787691817459187110896701250816564836193406646209159428444989152369700089027575873519296058210213871057790789893280686797554764761464434789210024654669643559962458972848153991859129838442079064353896813815159356612096726156054076880144837539930886680759506845518262337273510636059622769471722035496656973122915855321493624857615654961434503552028721049067486480870824138110458667158976123937919504424321940395809293002799951019960888804178357733125832347878186992208157387050952352204694698356397177078531914618736663107555118252619287443724734959556669314486443085203553885078415799176323570292490340982709794056826587780598031523195198246153563342876296146498719329536)
  | 16 => (3639878196169738594555283241051445973401174973685744548758516107092130426550714930202708166634409538201157853960149079591137380233526468734017493886238451031469656353834289825205002616077981787526731159944563268540821296220669556184044827266850613627404674179990665725772769031017914927217835716808095677537900261153235652129322174071968871859670792336006143895828965487177605342177916859410841894520866464441029824989293146752484086061183641005267874638814060117033932832869535903487873679913514802586583545490103325374146061720358707098766680762944856641260741720573224478389708778500309835701767526896396822618431954069498370148622447540767573167425626577855798083137181326053222853959951775440990804361600671920782311424000,586814487932419726260091197114087682141579983367517766653381118913976355015792086584046524742868213679301407462833901687275198897558909400598627657599504127693932031383786582302117283091239654612647116010293484847144824291537466407805482286576233903061592201057113351784382799610013688904757553233878407544079633233834784521334429677225453385648447952020042246040174997058618078365992559302480724114125630712584552708873281460777336306838471574861808033895419712610845600090800652903998047711449433321520765778568374001423678506973009748973039627708763813065598197796800329197187172416535503782551700923947851257416563290857859703514360342062072792833607743422417414131179028349559537276215598001150311359823691383002103808)
  | 17 => (864280654566013794756687111209459137026700255886894438560154520319368609498258882367744560097248356998609995754319749521609616621873070276017886162498345773937880029257176202489114703887408718070096675718408094390821624710900584809633186270772147157178893341196794217121867131454598238042299762058209986223203086822758111869513842538761001950056783299345545441947550981694433161364791420153758794774635636617901407089336640588690415989451366992423310735999479762447855251121694419519231975821080679950550622928264932735763544571048310729370744943412074121663446196774083973805564765785783811926918853306589980181848399127570006461749520157700992834301064890738461476810720812482313341859098875473261090723100895393384485356167835937162823300007708777752632717505429504000,166616884870563827312143415520153158334807897838589988146983710421591428170352203088630665694389463257360508246446799673052657650652848209053175212891177562283063032431983240829605961678607126610510748690873390882223677359247930154706733597773685043563937803288432350076990692213237872721321886184583822126053484070131740186073628165965705997017318539514556548170282159498445560840001686136432880500154415536921916517788527807909483502645481093845694338319337886168754267595937179430643275357459029949252885537262419165236175179053302799863167880661895315138335046313698129446319589843047801058753976449857831248534215040497762516490159680673965166490814696103058133609630157421434644340874019605626677908887192612643763290313744242332990850372044201959210905835143168)
  | 18 => (182263087446801446972611730037172382535943134989387381412930171932393046374926477063897848849931974992777625010334636611935855599696692084079172979307888416184168990757767699914215426177442983131781441856611378846095391198088768692992877615769990095533574146962375547815803716209877350376154146702488798687439325159949565161667475014533787015017933857932415564412405958706828558835415161654229490255837139001735097967809096904404763796218013142933965298124036283952053774533025195701057476062867526938747624971795076254598807068110686674544419415211011717399389551368061568080436851247201655708590877453159458828621186105104479045651308206652951733652424993246716797524697399701064160736938779065670287079705245319381428274935341879499856327930376019217704758433941688563624496085017179325879935056216064000000000000,41118175635747575948447947039987594048246064945413237605745544902787954756244903178279610258666230431646397296960550051886443004459783230024716805638781042088782924642739961960356022103058436282703228247998209854711791601965063557590267595761156206660364680895045867485832500080714576920456742756573214686471637414922093151870560674126440731881222329395620034739941359294591382633610262008734037530018977541674135592933412343945778266094076675496353919128152783132574232252890374351701641874915936362498815345650196960022447145078650853711004469786573402523596634633594838149527198039799935240239833389284818238792195845194374962711746105453029463290609158424628348363170948392051259201784528514052715646348906813222521598500854224637339450255183562819436960083168775849045345314239316884626645018738688000000000)
  | 19 => (34215754086644492946339175535836859721585300726180214857791728148342135762441074631312000104354846869038375334918074411075633741405109134485617478295432970886590283910510457758376885217485789172996308027523893306297077589730446362423054327083077380781110708712875335210044892554808250814934370000462237035500659729575054516285500506149246234845439762215111273564152974003420388469335015976752379016837420494375327707844351466541703287262364207866981268531916275606440081012838724932066179494693613482602536763398847984214910693373360972757940517718322674867552833110186047010876105994139986219219034330806819757024209110988744263167784012755329951317383711800052091576797726624103048808999382425266109826044077326516208713444793479816046445197766683997024245724201853787834966077907734703078844046789206212416634519066134134895148639337148070419031442587648000,8904382739640950503983672145874164477445085239138020867809111433362909017860349717549868761583938013355832192513147716578861682714802252852830107229398391710620142017756822311256296223602518773704464939971186990399265008056820583875692911149665986843935173944811573107223363112948720418142195366131022416072016091224422226970345409227643003188514847841971185960837983208763682266998999861516457697575186078555759664326529741420264636003365238931037820117498207464503970290151650671365473191534112526645363642231991526792108353003995107989737868017722443432532561074901978036259719286980800843469499701864731773382205126188905121452446378165470499168148291816045523925660872609246833702554006954569070892178812163735890079238567765753785765830240642172459474401593544649635105896888264943033083489898196086277226903344187397285871477112382690139677147529216)
  | 20 => (5730187345873769274943575306763503803011898480138101612370930102135623167810324017329494034814280491215399378920280488144821810246273760172855680376594990747517040362427303982379049802522247981842440753897379511466179662985067036619776978838861793816585397784857810727334799178587258261924975416814530920584214572395528079444252150273609990683016757896461299250415051406418852788662705393791036643198982141412011992586936248588637326512309203389853291487149015541551611758396695925551371665503373058243977516427983515746571273888077895606930526134531445172399665277333646014627221888845923304287440544776579391280292085329280521240163051668506531073878114702582509599355075190028068056172996471200005093156315020398043809254949688966423090135848559792818483755032840083596367096741868385363473469220731556296081124485801073931700006781784101612797742675377896689961323206457753332103374242682769506304000,1699430106656201781472878608149629746794685977272550897136230222932275532960996409882749544791007956798278736141535281495159198007414196767043988442450613772296617187563767880022386178585238498391162409078982001028653645222742824922473050596981175934564922708592878386521474661109620757765869237147536615327354402478866906397566228353288913978105095479938418015808750428803608927312656728940995779983351948708699836525564125690778191420268571978579329956931075836868263756128540420365104255685778776235250147576726901827766805218734391226668695577136327971404873409533746220528367621998510493071564201209626107658921475891320505984504507895223078440810162353819398746284054484805103662837466555942301193533333943035930320631001603136898472120405410988185423454331758735000563823022473773256195097602801835918529779375249357417972641843789700536260714146926121804257401068819251110701124747560923168768)
  | r => (3000*winsorScale*xNum r^9,winsorScale*xNum r^9)
def winsorMGFFastCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => (winsorCertifiedDots r).1)
    (3000*winsorScale*Nn^9) (3000*A) 1 8 1 80
def winsorResidualFastCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => (winsorCertifiedDots r).2)
    (winsorScale*Nn^9) A 1 1 5000 80
set_option maxHeartbeats 50000000 in
theorem winsor_mgf_fast_ok : winsorMGFFastCheck = true := by decide +kernel
set_option maxHeartbeats 50000000 in
theorem winsor_residual_fast_ok : winsorResidualFastCheck = true := by decide +kernel
namespace StreamCheck
open ClaudeWCT.Numerics.N600

def sums : List Nat → List Nat → Nat → Nat × Nat × Nat
  | m :: ms, t :: ts, p =>
    let n := p &&& (2^4608-1)
    let v := sums ms ts (p >>> 4608)
    (n + v.1, n*m + v.2.1, n*t + v.2.2)
  | _, _, _ => (0,0,0)

theorem sums_eq (ms ts : List Nat) (p : Nat) : sums ms ts p = winsorPackedSums ms ts p := by
  induction ms generalizing ts p with
  | nil => rfl
  | cons m ms ih =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [sums, winsorPackedSums, ih, Nat.shiftRight_eq_div_pow,
        Nat.and_two_pow_sub_one_eq_mod]

def bins (bits : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, p =>
    if p = 0 then 0 else
    let n := p % (2^512)
    let rest := bins bits bs (p >>> 512)
    if n = 0 then rest else (n <<< (bits*b)) + rest

theorem bins_zero (bits : Nat) (bs : List Nat) : bins bits bs 0 = 0 := by
  cases bs <;> simp [bins]

theorem bins_eq_aux (bits : Nat) (bs : List Nat) (p c : Nat) :
    bins bits bs (p >>> (512*c)) =
    (bs.zipIdx c).foldr (fun e acc =>
      let n := (p >>> (512*e.2)) % (2^512)
      if n=0 then acc else (n <<< (bits*e.1))+acc) 0 := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    rw [List.zipIdx_cons, List.foldr_cons, ← ih (c+1)]
    have hs : p >>> (512*(c+1)) = (p >>> (512*c)) >>> 512 := by
      rw [← Nat.shiftRight_add]
      congr 1
    simp only [hs, bins]
    by_cases h : p >>> (512*c) = 0
    · simp [h, bins_zero]
    · simp [h]

theorem bins_eq (bits r : Nat) :
    bins bits coverageBinData.toList (coverageRetainedBits 512 r) = coverageBinnedLinear bits r := by
  simpa only [Nat.mul_zero, Nat.shiftRight_zero, coverageBinnedLinear] using
    bins_eq_aux bits coverageBinData.toList (coverageRetainedBits 512 r) 0

def row (r : Nat) : Nat × Nat :=
  if r ≤ 20 then
    let v := sums winsorMGFPayData winsorResidualPayData
      (bins 4608 coverageBinData.toList (coverageRetainedBits 512 r) ^ 9)
    let missed := xNum r ^ 9 - v.1
    (v.2.1 + 3000 * winsorScale * missed, v.2.2 + winsorScale * missed)
  else (3000 * winsorScale * xNum r ^ 9, winsorScale * xNum r ^ 9)

theorem row_eq (r : Nat) : row r = winsorRowDots r := by
  simp only [row, bins_eq, sums_eq, winsorRowDots, coverageProductLinear]



end StreamCheck

set_option maxHeartbeats 200000000 in
theorem winsor_row_0 : winsorRowDots 0 = (0,0) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_1 : winsorRowDots 1 = (4304737466716198510902241657960411531101456204344222518,0) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_2 : winsorRowDots 2 = (350464637810563205369907563362523142509281712838984639932768546697035546336664706139336588019512066150,2888165470991626549199529039083531863264948425070934777887408472582447767798253060096) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_3 : winsorRowDots 3 = (1895703571804125441214450143611836933078843758950134443446042258877697783652081956257407727728190683334704551063908457834398852571219726486921159996,62287870725601012024002656658515934843466026802510578737981090426695828618785279699684531970375057361187569703755677003792003834046208) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_4 : winsorRowDots 4 = (3220580229176428969370891728583851897999938295872671679399914606894513100298639912517261082457313673860356696266069895581746799270647068774005068850559155716884979872182248647379227484467260050,10244491628795906586495039879542062987848972671687185128386860672648830086956288445437624598722629850381356980168615551174410216707866502124436788698838362301053728995085173112067072) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_5 : winsorRowDots 5 = (2824450701398056004061588399518555732129048764845132424777153531334773954080030974285554067027764432860718547752880785851159213189784511244253124006859028224701520048499967739707675346128333059719716937550424279546152449064894080428826748,240784386167233085499040533825714364552977736060006293802912080753331833095717394732987844033955580739440361806384157018114772443009628429778799307057564711905256189484682874729305227996406295117588118543556593777925774620000000) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_6 : winsorRowDots 6 = (1604232661042295161239019559395787050549041727028847825804676721305719216563973895671719424839936519971810578447191680235081746453229491647490077943438518492480067757601443423445962548965744796942697913646034712518069353742645665904466166276510387587190490211508374211717486886723210,1911608055636490856136213788713501870232755968024665606639179248330110910784362726997035999724114698955862222116107498854311665606439446939667069418124483407772515462313116438306547605710180449636764038052060469585246191023495491715929118641894291544190348896365414895256576) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_7 : winsorRowDots 7 = (668251685456412308496042892300019187639448250676704603766840176909480245840076447916937857582541696653788901652472008729875965602336569804549285555716162000622947175330976310377754609741323852801196556390777171961491898361789635540736408012252600965509914401892788558245555121161380774377495042625328477081703112801925585576676,7399000317643339632052240559200041630603785025821163455064117274928459707400528301933091604006246506457830020155900844922254034497589601109897365096457440882524747971199441132952427872320568591849615431341786161220125082030070507001569389146079635616372301293729538490397777846305015444457039178294778284561684606879488) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_8 : winsorRowDots 8 = (220493847321206163188491122369839907726174567156458082607227244288376302136203924576546496610665398217903665959210422088084117721605576910124478941136966196577295843935666377066748846278409490310290060549182841665371860123998902559152794096596944566065343513764810813667267157875855902707607279392414848586241605886479728470481211681758684142166794165956254317586461373810,17223773629393038673781156520736591286217487234574706977878614677364072649467692673923970693832247706855503383772797738158492019313682327490313449298237916264860328924508585707703154396798897669678984580467635645815804699713888749802864918472284782757191315782449043881614396738590560108446968399907556852615245131633606134255554436429854770291372541643051466662912) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_9 : winsorRowDots 9 = (60816853358554839524738929113224518708098182734371075902081641185202861657114846025330880636446492500330824533219507870766913467959785953770792842180356776182449388193816490025112978764419120846523375024834211719840226687851035005780336301453108058508268435349449383330422493797204805928366276715489710550402607760226164464022218471390748694134210168834026838282449309115196898045600589616211524836207547913419795746,27039565886254044461175547684520086965285754920473846307253168795694495596443154063273942724081106826843372755671181685962507745286199972866936162439843001226546774497998507416933505973047441945394523636768945445169255509668356928969410269566075233454617708937155951608939363606076034966794056005572325688202862337411188048477828618537367135022044391427107151363919062193081259066965674907541199791251148161536) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_10 : winsorRowDots 10 = (14690446871398049064096790850511336218965320377583419759507350231105235563705652886215426401012056292900745353403497279701457267240533825752116480283895608223888598784797256394921412437301699871432237909190501175427605643635907961920138714208757418135325050087431306528429486053300310813678018611109770369056054492556076617887140979994926503580531154069826062491710689256206005587847645735110890065532635657996924172648297872095383004534354274964274167414958710,30328680605417344013385102722347207157126213834718126184435271879955973985941984152850779012779099923942934028894909499547436031357029960845984616401590549804058536798515142193208106934551480184269155743587490047646097583843936259097445801260780497685197778350867918072156199424119068819565308653227407652446602078060393085825882226214345166065654123238773963202035215810490194458144463139103599103485101791358078764641438641426322335035480093214952986624) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_11 : winsorRowDots 11 = (3289519751596440350026864900981033603842659155750872547330845651725211393352435754970764247900307039265695920464604090434283207318004578298605569110169951139976486076346482843546318230242141666366791052532609282176317490229008136403379169053330492770652982506961988120798047176170537954220032125926421575198006015722506647238941223779577944978545959232063823040945186014285728715599861855487798384124947393912886123365572616449594108517771437761837771497686668666777214063084484187571838154485610455049776,26205086785701927000731032922307448592413371068380472870262256500053506154512459343103537140166886490308061228680831011026979381055912527532865162233463911841592105787679301610776876815580391425989728764844325255829278996711373096059364510241765319427845836574534167200509199223217684891998608832270889120294934705685660117090864863735042148566924836893475972220077999509106472175619352643367304485659849328507352325551261348011083977683465781087981912581234236838965709900822132720874334100626080512) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_12 : winsorRowDots 12 = (740875843093287362151553328439344903668157020723175996423145100787232888612225678983149151616007509905929878440347429431579957385141766876840271276152405374651422970246162408900135181666480754913364395799736636079241163530454591274108240875545591624061818608980738522759674301126784090045578896743210686511981261868377109747264765784357571532797188384430468701890480080148415922152978104537358770629351518847670289535453479867021025524635197414758083140033288701014227866960164424915712280117351648968548104652503493441019680424319528866632316668390,17942417285562655174924127938444548270748805353448345586556594987958284715435387102276031103278464349560365949322539451656508314238952340326021281847029308099342273524358819187838659533542472477947253186891550372043201550740253634937610445617288377381909098228223627385760144753375494311107758633719809891630991908880011265521916022186338580491408543826168331927708312874258098397306528999065094140558468344195756097850779573366243889895701176508342463752013952409939674158735420721726498287068083889212874851672387872536429659164970050954403840) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_13 : winsorRowDots 13 = (182289338147689926588129026463508197385752847697803742051481847030950457879664103414315484249339722670488789503475725363096374282368427694529499479940321613025916854127713353576190652669830465406869048832887039011860407400509022829797743040583767977666834422407700044036266246166132980589042638618520082429767294744534407077105973972059524428508263343815785771191489322780104140709847172557126720153188725625393181515489266542833734449241409523770540491087734687930029441287467769637160730774837945122791708350123966397891092100152400586967950967526838472319876608861528094341366815288479364292,9942507328702050800397305032787122281775132342561141490757598755573099382972702231901504121856088284505202282000305341009795507781333786813623923057519509640864438077129489039546314060821216046612313686641549538187728890086702010175370965829245694622627536682336215390238567396545228825162682004777286801002466288280421361680873049551945397116079465942735677056090291970096083099329780686925224336521396675324509319420962049138773733252207201793626141825993654994992868542399730835627555584476498600240077831481627067782885569506693966293013732966526963352680502913555724222865790266302720) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_14 : winsorRowDots 14 = (49615271378259362648583881291595926903586268982458990276984492242568972169415076656313186293127166001462382929085559322625964435746836711618152003900035387590637810682401814458761961358732331318631681729310649116590769456463872141893264396316472308046015196676084005160309200407422827281284353521219262262482343796234794811913805464249910035935687147200275423717893884546781944833112106211195353946982827231754025833853647474809885578817019681059373870495968752244172202059661983889277352265146259005488010840898394353908979873447831488908387176470688985223862335074456547214170208472338356812750778690265827405703059582796980334901645002,4586336298749263199088025113817169913552000632301119440911554808777237972237997781980454586381869314750606695679767056836571105551222351493250613330106508066379560179826818154468977710109851144101743199930976534315887794280123652049906096824240800143981761850787055865075673853921952487587332351478476153166306225191331741970127216285275726441723417850221434830545667499500226765322956990520689188127671975599193128048979382579743322885820597872972283235732210397563048440480849515469138744029858427554064956291554199056766707084321830120610138141528213634793171540789086270091803355067215819198786124696560277340290191375535187570688) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_15 : winsorRowDots 15 = (13795966909242820928357530060669849399827652001316281146780354361366456422802246895561007069845684626219210966720851581788882568803342271364862682890494732267571075603247618470339307970931806904647995919374528534274295616183653630569832180112839030887591454334875089464681928962121415313024805385516776613114169618833941856253383098297217170642221331409598414940381275668665883305318914928520025412386282888928980978425872590347846479366026452409856974530031750340218949254435321003630010160537584464998625578358247968743522888088522899341428091717634869985719427829462692364113315244492053987740366805874286990233301670567679941592844998374073930671737428117345326295805566379233000,1774210322787691817459187110896701250816564836193406646209159428444989152369700089027575873519296058210213871057790789893280686797554764761464434789210024654669643559962458972848153991859129838442079064353896813815159356612096726156054076880144837539930886680759506845518262337273510636059622769471722035496656973122915855321493624857615654961434503552028721049067486480870824138110458667158976123937919504424321940395809293002799951019960888804178357733125832347878186992208157387050952352204694698356397177078531914618736663107555118252619287443724734959556669314486443085203553885078415799176323570292490340982709794056826587780598031523195198246153563342876296146498719329536) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_16 : winsorRowDots 16 = (3639878196169738594555283241051445973401174973685744548758516107092130426550714930202708166634409538201157853960149079591137380233526468734017493886238451031469656353834289825205002616077981787526731159944563268540821296220669556184044827266850613627404674179990665725772769031017914927217835716808095677537900261153235652129322174071968871859670792336006143895828965487177605342177916859410841894520866464441029824989293146752484086061183641005267874638814060117033932832869535903487873679913514802586583545490103325374146061720358707098766680762944856641260741720573224478389708778500309835701767526896396822618431954069498370148622447540767573167425626577855798083137181326053222853959951775440990804361600671920782311424000,586814487932419726260091197114087682141579983367517766653381118913976355015792086584046524742868213679301407462833901687275198897558909400598627657599504127693932031383786582302117283091239654612647116010293484847144824291537466407805482286576233903061592201057113351784382799610013688904757553233878407544079633233834784521334429677225453385648447952020042246040174997058618078365992559302480724114125630712584552708873281460777336306838471574861808033895419712610845600090800652903998047711449433321520765778568374001423678506973009748973039627708763813065598197796800329197187172416535503782551700923947851257416563290857859703514360342062072792833607743422417414131179028349559537276215598001150311359823691383002103808) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_17 : winsorRowDots 17 = (864280654566013794756687111209459137026700255886894438560154520319368609498258882367744560097248356998609995754319749521609616621873070276017886162498345773937880029257176202489114703887408718070096675718408094390821624710900584809633186270772147157178893341196794217121867131454598238042299762058209986223203086822758111869513842538761001950056783299345545441947550981694433161364791420153758794774635636617901407089336640588690415989451366992423310735999479762447855251121694419519231975821080679950550622928264932735763544571048310729370744943412074121663446196774083973805564765785783811926918853306589980181848399127570006461749520157700992834301064890738461476810720812482313341859098875473261090723100895393384485356167835937162823300007708777752632717505429504000,166616884870563827312143415520153158334807897838589988146983710421591428170352203088630665694389463257360508246446799673052657650652848209053175212891177562283063032431983240829605961678607126610510748690873390882223677359247930154706733597773685043563937803288432350076990692213237872721321886184583822126053484070131740186073628165965705997017318539514556548170282159498445560840001686136432880500154415536921916517788527807909483502645481093845694338319337886168754267595937179430643275357459029949252885537262419165236175179053302799863167880661895315138335046313698129446319589843047801058753976449857831248534215040497762516490159680673965166490814696103058133609630157421434644340874019605626677908887192612643763290313744242332990850372044201959210905835143168) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_18 : winsorRowDots 18 = (182263087446801446972611730037172382535943134989387381412930171932393046374926477063897848849931974992777625010334636611935855599696692084079172979307888416184168990757767699914215426177442983131781441856611378846095391198088768692992877615769990095533574146962375547815803716209877350376154146702488798687439325159949565161667475014533787015017933857932415564412405958706828558835415161654229490255837139001735097967809096904404763796218013142933965298124036283952053774533025195701057476062867526938747624971795076254598807068110686674544419415211011717399389551368061568080436851247201655708590877453159458828621186105104479045651308206652951733652424993246716797524697399701064160736938779065670287079705245319381428274935341879499856327930376019217704758433941688563624496085017179325879935056216064000000000000,41118175635747575948447947039987594048246064945413237605745544902787954756244903178279610258666230431646397296960550051886443004459783230024716805638781042088782924642739961960356022103058436282703228247998209854711791601965063557590267595761156206660364680895045867485832500080714576920456742756573214686471637414922093151870560674126440731881222329395620034739941359294591382633610262008734037530018977541674135592933412343945778266094076675496353919128152783132574232252890374351701641874915936362498815345650196960022447145078650853711004469786573402523596634633594838149527198039799935240239833389284818238792195845194374962711746105453029463290609158424628348363170948392051259201784528514052715646348906813222521598500854224637339450255183562819436960083168775849045345314239316884626645018738688000000000) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_19 : winsorRowDots 19 = (34215754086644492946339175535836859721585300726180214857791728148342135762441074631312000104354846869038375334918074411075633741405109134485617478295432970886590283910510457758376885217485789172996308027523893306297077589730446362423054327083077380781110708712875335210044892554808250814934370000462237035500659729575054516285500506149246234845439762215111273564152974003420388469335015976752379016837420494375327707844351466541703287262364207866981268531916275606440081012838724932066179494693613482602536763398847984214910693373360972757940517718322674867552833110186047010876105994139986219219034330806819757024209110988744263167784012755329951317383711800052091576797726624103048808999382425266109826044077326516208713444793479816046445197766683997024245724201853787834966077907734703078844046789206212416634519066134134895148639337148070419031442587648000,8904382739640950503983672145874164477445085239138020867809111433362909017860349717549868761583938013355832192513147716578861682714802252852830107229398391710620142017756822311256296223602518773704464939971186990399265008056820583875692911149665986843935173944811573107223363112948720418142195366131022416072016091224422226970345409227643003188514847841971185960837983208763682266998999861516457697575186078555759664326529741420264636003365238931037820117498207464503970290151650671365473191534112526645363642231991526792108353003995107989737868017722443432532561074901978036259719286980800843469499701864731773382205126188905121452446378165470499168148291816045523925660872609246833702554006954569070892178812163735890079238567765753785765830240642172459474401593544649635105896888264943033083489898196086277226903344187397285871477112382690139677147529216) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_20 : winsorRowDots 20 = (5730187345873769274943575306763503803011898480138101612370930102135623167810324017329494034814280491215399378920280488144821810246273760172855680376594990747517040362427303982379049802522247981842440753897379511466179662985067036619776978838861793816585397784857810727334799178587258261924975416814530920584214572395528079444252150273609990683016757896461299250415051406418852788662705393791036643198982141412011992586936248588637326512309203389853291487149015541551611758396695925551371665503373058243977516427983515746571273888077895606930526134531445172399665277333646014627221888845923304287440544776579391280292085329280521240163051668506531073878114702582509599355075190028068056172996471200005093156315020398043809254949688966423090135848559792818483755032840083596367096741868385363473469220731556296081124485801073931700006781784101612797742675377896689961323206457753332103374242682769506304000,1699430106656201781472878608149629746794685977272550897136230222932275532960996409882749544791007956798278736141535281495159198007414196767043988442450613772296617187563767880022386178585238498391162409078982001028653645222742824922473050596981175934564922708592878386521474661109620757765869237147536615327354402478866906397566228353288913978105095479938418015808750428803608927312656728940995779983351948708699836525564125690778191420268571978579329956931075836868263756128540420365104255685778776235250147576726901827766805218734391226668695577136327971404873409533746220528367621998510493071564201209626107658921475891320505984504507895223078440810162353819398746284054484805103662837466555942301193533333943035930320631001603136898472120405410988185423454331758735000563823022473773256195097602801835918529779375249357417972641843789700536260714146926121804257401068819251110701124747560923168768) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
theorem winsorRowDots_eq (r : ℕ) : winsorRowDots r = winsorCertifiedDots r := by
  by_cases hr : r ≤ 20
  · interval_cases r
    · exact winsor_row_0
    · exact winsor_row_1
    · exact winsor_row_2
    · exact winsor_row_3
    · exact winsor_row_4
    · exact winsor_row_5
    · exact winsor_row_6
    · exact winsor_row_7
    · exact winsor_row_8
    · exact winsor_row_9
    · exact winsor_row_10
    · exact winsor_row_11
    · exact winsor_row_12
    · exact winsor_row_13
    · exact winsor_row_14
    · exact winsor_row_15
    · exact winsor_row_16
    · exact winsor_row_17
    · exact winsor_row_18
    · exact winsor_row_19
    · exact winsor_row_20
  · rw [winsorRowDots, if_neg hr]
    unfold winsorCertifiedDots
    split <;> first | omega | rfl

theorem winsor_mgf_ok : poissonCheckQ Q 13533529 100000000 LN LD
    (fun r => (winsorRowDots r).1) (3000*winsorScale*Nn^9) (3000*A) 1 8 1 80 = true := by
  simp_rw [winsorRowDots_eq]
  exact winsor_mgf_fast_ok

theorem winsor_residual_ok : poissonCheckQ Q 13533529 100000000 LN LD
    (fun r => (winsorRowDots r).2) (winsorScale*Nn^9) A 1 1 5000 80 = true := by
  simp_rw [winsorRowDots_eq]
  exact winsor_residual_fast_ok
end ClaudeWCT.Numerics.N600


/-! Executable exact-integer reflector for paired forest coverage. These
functions are private research inputs; the generic histogram refinement and
all row checks must be proved before they can be used in the certificate. -/
namespace ClaudeWCT.Numerics.SharedPathReflection
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def profiles : List (List Nat) := [[0,0,0,0,0,0,0],[0,0,0,0,0,0,1],[0,0,0,0,0,0,2],[0,0,0,0,0,1,0],[0,0,0,0,0,1,1],[0,0,0,0,0,2,0],[0,0,0,0,1,0,0],[0,0,0,0,1,0,1],[0,0,0,0,1,1,0],[0,0,0,0,1,2,0],[0,0,0,0,2,0,0],[0,0,0,0,2,0,1],[0,0,0,0,2,1,0],[0,0,0,0,3,0,0],[0,0,0,1,0,0,0],[0,0,0,1,0,0,1],[0,0,0,1,0,1,0],[0,0,0,1,0,1,1],[0,0,0,1,0,2,0],[0,0,0,1,1,0,0],[0,0,0,1,1,0,1],[0,0,0,1,1,1,0],[0,0,0,1,2,0,0],[0,0,0,2,0,0,0],[0,0,0,2,0,0,1],[0,0,0,2,0,1,0],[0,0,0,2,1,0,0],[0,0,0,3,0,0,0],[0,0,0,4,0,0,0],[0,0,1,0,0,0,0],[0,0,1,0,0,0,1],[0,0,1,0,0,0,2],[0,0,1,0,0,1,0],[0,0,1,0,0,1,1],[0,0,1,0,0,2,0],[0,0,1,0,1,0,0],[0,0,1,0,1,0,1],[0,0,1,0,1,1,0],[0,0,1,0,2,0,0],[0,0,1,1,0,0,0],[0,0,1,1,0,0,1],[0,0,1,1,0,1,0],[0,0,1,1,1,0,0],[0,0,1,2,0,0,0],[0,0,1,2,1,0,0],[0,0,1,3,0,0,0],[0,0,2,0,0,0,0],[0,0,2,0,0,0,1],[0,0,2,0,0,1,0],[0,0,2,0,1,0,0],[0,0,2,0,2,0,0],[0,0,2,1,0,0,0],[0,0,2,1,0,1,0],[0,0,2,1,1,0,0],[0,0,2,2,0,0,0],[0,0,3,0,0,0,0],[0,0,3,0,0,0,1],[0,0,3,0,0,1,0],[0,0,3,0,1,0,0],[0,0,3,1,0,0,0],[0,0,4,0,0,0,0],[0,0,5,0,0,0,0],[0,1,0,0,0,0,0],[0,1,0,0,0,0,1],[0,1,0,0,0,0,2],[0,1,0,0,0,1,0],[0,1,0,0,0,1,1],[0,1,0,0,0,2,0],[0,1,0,0,1,0,0],[0,1,0,0,1,0,1],[0,1,0,0,1,1,0],[0,1,0,0,2,0,0],[0,1,0,1,0,0,0],[0,1,0,1,0,0,1],[0,1,0,1,0,1,0],[0,1,0,1,1,0,0],[0,1,0,1,2,0,0],[0,1,0,2,0,0,0],[0,1,0,2,0,1,0],[0,1,0,2,1,0,0],[0,1,0,3,0,0,0],[0,1,1,0,0,0,0],[0,1,1,0,0,0,1],[0,1,1,0,0,1,0],[0,1,1,0,1,0,0],[0,1,1,0,1,1,0],[0,1,1,0,2,0,0],[0,1,1,1,0,0,0],[0,1,1,1,0,0,1],[0,1,1,1,0,1,0],[0,1,1,1,1,0,0],[0,1,1,2,0,0,0],[0,1,2,0,0,0,0],[0,1,2,0,0,0,1],[0,1,2,0,0,1,0],[0,1,2,0,1,0,0],[0,1,2,1,0,0,0],[0,1,3,0,0,0,0],[0,1,3,1,0,0,0],[0,1,4,0,0,0,0],[0,2,0,0,0,0,0],[0,2,0,0,0,0,1],[0,2,0,0,0,1,0],[0,2,0,0,0,2,0],[0,2,0,0,1,0,0],[0,2,0,0,1,0,1],[0,2,0,0,1,1,0],[0,2,0,0,2,0,0],[0,2,0,1,0,0,0],[0,2,0,1,0,0,1],[0,2,0,1,0,1,0],[0,2,0,1,1,0,0],[0,2,0,2,0,0,0],[0,2,1,0,0,0,0],[0,2,1,0,0,0,1],[0,2,1,0,0,1,0],[0,2,1,0,1,0,0],[0,2,1,1,0,0,0],[0,2,1,2,0,0,0],[0,2,2,0,0,0,0],[0,2,2,0,1,0,0],[0,2,2,1,0,0,0],[0,2,3,0,0,0,0],[0,3,0,0,0,0,0],[0,3,0,0,0,0,1],[0,3,0,0,0,1,0],[0,3,0,0,1,0,0],[0,3,0,1,0,0,0],[0,3,0,1,1,0,0],[0,3,0,2,0,0,0],[0,3,1,0,0,0,0],[0,3,1,0,0,1,0],[0,3,1,0,1,0,0],[0,3,1,1,0,0,0],[0,3,2,0,0,0,0],[0,4,0,0,0,0,0],[0,4,0,0,0,0,1],[0,4,0,0,0,1,0],[0,4,0,0,1,0,0],[0,4,0,1,0,0,0],[0,4,1,0,0,0,0],[0,4,2,0,0,0,0],[0,5,0,0,0,0,0],[0,5,0,1,0,0,0],[0,5,1,0,0,0,0],[0,6,0,0,0,0,0],[1,0,0,0,0,0,0],[1,0,0,0,0,0,1],[1,0,0,0,0,0,2],[1,0,0,0,0,1,0],[1,0,0,0,0,1,1],[1,0,0,0,0,2,0],[1,0,0,0,1,0,0],[1,0,0,0,1,0,1],[1,0,0,0,1,1,0],[1,0,0,0,2,0,0],[1,0,0,0,3,0,0],[1,0,0,1,0,0,0],[1,0,0,1,0,0,1],[1,0,0,1,0,1,0],[1,0,0,1,1,0,0],[1,0,0,1,1,1,0],[1,0,0,1,2,0,0],[1,0,0,2,0,0,0],[1,0,0,2,0,0,1],[1,0,0,2,0,1,0],[1,0,0,2,1,0,0],[1,0,0,3,0,0,0],[1,0,1,0,0,0,0],[1,0,1,0,0,0,1],[1,0,1,0,0,1,0],[1,0,1,0,0,2,0],[1,0,1,0,1,0,0],[1,0,1,0,1,0,1],[1,0,1,0,1,1,0],[1,0,1,0,2,0,0],[1,0,1,1,0,0,0],[1,0,1,1,0,0,1],[1,0,1,1,0,1,0],[1,0,1,1,1,0,0],[1,0,1,2,0,0,0],[1,0,2,0,0,0,0],[1,0,2,0,0,0,1],[1,0,2,0,0,1,0],[1,0,2,0,1,0,0],[1,0,2,1,0,0,0],[1,0,2,2,0,0,0],[1,0,3,0,0,0,0],[1,0,3,0,1,0,0],[1,0,3,1,0,0,0],[1,0,4,0,0,0,0],[1,1,0,0,0,0,0],[1,1,0,0,0,0,1],[1,1,0,0,0,1,0],[1,1,0,0,0,1,1],[1,1,0,0,0,2,0],[1,1,0,0,1,0,0],[1,1,0,0,1,0,1],[1,1,0,0,1,1,0],[1,1,0,0,2,0,0],[1,1,0,1,0,0,0],[1,1,0,1,0,0,1],[1,1,0,1,0,1,0],[1,1,0,1,1,0,0],[1,1,0,2,0,0,0],[1,1,0,3,0,0,0],[1,1,1,0,0,0,0],[1,1,1,0,0,0,1],[1,1,1,0,0,1,0],[1,1,1,0,1,0,0],[1,1,1,1,0,0,0],[1,1,1,1,1,0,0],[1,1,1,2,0,0,0],[1,1,2,0,0,0,0],[1,1,2,0,0,1,0],[1,1,2,0,1,0,0],[1,1,2,1,0,0,0],[1,1,3,0,0,0,0],[1,2,0,0,0,0,0],[1,2,0,0,0,0,1],[1,2,0,0,0,1,0],[1,2,0,0,1,0,0],[1,2,0,0,2,0,0],[1,2,0,1,0,0,0],[1,2,0,1,0,1,0],[1,2,0,1,1,0,0],[1,2,0,2,0,0,0],[1,2,1,0,0,0,0],[1,2,1,0,0,0,1],[1,2,1,0,0,1,0],[1,2,1,0,1,0,0],[1,2,1,1,0,0,0],[1,2,2,0,0,0,0],[1,2,3,0,0,0,0],[1,3,0,0,0,0,0],[1,3,0,0,0,0,1],[1,3,0,0,0,1,0],[1,3,0,0,1,0,0],[1,3,0,1,0,0,0],[1,3,1,0,0,0,0],[1,3,1,1,0,0,0],[1,3,2,0,0,0,0],[1,4,0,0,0,0,0],[1,4,0,0,1,0,0],[1,4,0,1,0,0,0],[1,4,1,0,0,0,0],[1,5,0,0,0,0,0],[1,6,0,0,0,0,0],[2,0,0,0,0,0,0],[2,0,0,0,0,0,1],[2,0,0,0,0,0,2],[2,0,0,0,0,1,0],[2,0,0,0,0,1,1],[2,0,0,0,0,2,0],[2,0,0,0,1,0,0],[2,0,0,0,1,0,1],[2,0,0,0,1,1,0],[2,0,0,0,2,0,0],[2,0,0,1,0,0,0],[2,0,0,1,0,0,1],[2,0,0,1,0,1,0],[2,0,0,1,1,0,0],[2,0,0,2,0,0,0],[2,0,0,2,1,0,0],[2,0,0,3,0,0,0],[2,0,1,0,0,0,0],[2,0,1,0,0,0,1],[2,0,1,0,0,1,0],[2,0,1,0,1,0,0],[2,0,1,0,2,0,0],[2,0,1,1,0,0,0],[2,0,1,1,0,1,0],[2,0,1,1,1,0,0],[2,0,1,2,0,0,0],[2,0,2,0,0,0,0],[2,0,2,0,0,0,1],[2,0,2,0,0,1,0],[2,0,2,0,1,0,0],[2,0,2,1,0,0,0],[2,0,3,0,0,0,0],[2,0,4,0,0,0,0],[2,1,0,0,0,0,0],[2,1,0,0,0,0,1],[2,1,0,0,0,1,0],[2,1,0,0,1,0,0],[2,1,0,0,1,1,0],[2,1,0,0,2,0,0],[2,1,0,1,0,0,0],[2,1,0,1,0,0,1],[2,1,0,1,0,1,0],[2,1,0,1,1,0,0],[2,1,0,2,0,0,0],[2,1,1,0,0,0,0],[2,1,1,0,0,0,1],[2,1,1,0,0,1,0],[2,1,1,0,1,0,0],[2,1,1,1,0,0,0],[2,1,2,0,0,0,0],[2,1,2,1,0,0,0],[2,1,3,0,0,0,0],[2,2,0,0,0,0,0],[2,2,0,0,0,0,1],[2,2,0,0,0,1,0],[2,2,0,0,1,0,0],[2,2,0,1,0,0,0],[2,2,0,2,0,0,0],[2,2,1,0,0,0,0],[2,2,1,0,1,0,0],[2,2,1,1,0,0,0],[2,2,2,0,0,0,0],[2,3,0,0,0,0,0],[2,3,0,0,0,1,0],[2,3,0,0,1,0,0],[2,3,0,1,0,0,0],[2,3,1,0,0,0,0],[2,4,0,0,0,0,0],[2,4,1,0,0,0,0],[2,5,0,0,0,0,0],[3,0,0,0,0,0,0],[3,0,0,0,0,0,1],[3,0,0,0,0,1,0],[3,0,0,0,0,2,0],[3,0,0,0,1,0,0],[3,0,0,0,1,0,1],[3,0,0,0,1,1,0],[3,0,0,0,2,0,0],[3,0,0,1,0,0,0],[3,0,0,1,0,0,1],[3,0,0,1,0,1,0],[3,0,0,1,1,0,0],[3,0,0,2,0,0,0],[3,0,1,0,0,0,0],[3,0,1,0,0,0,1],[3,0,1,0,0,1,0],[3,0,1,0,1,0,0],[3,0,1,1,0,0,0],[3,0,1,2,0,0,0],[3,0,2,0,0,0,0],[3,0,2,0,1,0,0],[3,0,2,1,0,0,0],[3,0,3,0,0,0,0],[3,1,0,0,0,0,0],[3,1,0,0,0,0,1],[3,1,0,0,0,1,0],[3,1,0,0,1,0,0],[3,1,0,1,0,0,0],[3,1,0,1,1,0,0],[3,1,0,2,0,0,0],[3,1,1,0,0,0,0],[3,1,1,0,0,1,0],[3,1,1,0,1,0,0],[3,1,1,1,0,0,0],[3,1,2,0,0,0,0],[3,2,0,0,0,0,0],[3,2,0,0,0,0,1],[3,2,0,0,0,1,0],[3,2,0,0,1,0,0],[3,2,0,1,0,0,0],[3,2,1,0,0,0,0],[3,2,2,0,0,0,0],[3,3,0,0,0,0,0],[3,3,0,1,0,0,0],[3,3,1,0,0,0,0],[3,4,0,0,0,0,0],[4,0,0,0,0,0,0],[4,0,0,0,0,0,1],[4,0,0,0,0,1,0],[4,0,0,0,1,0,0],[4,0,0,0,2,0,0],[4,0,0,1,0,0,0],[4,0,0,1,0,1,0],[4,0,0,1,1,0,0],[4,0,0,2,0,0,0],[4,0,1,0,0,0,0],[4,0,1,0,0,0,1],[4,0,1,0,0,1,0],[4,0,1,0,1,0,0],[4,0,1,1,0,0,0],[4,0,2,0,0,0,0],[4,0,3,0,0,0,0],[4,1,0,0,0,0,0],[4,1,0,0,0,0,1],[4,1,0,0,0,1,0],[4,1,0,0,1,0,0],[4,1,0,1,0,0,0],[4,1,1,0,0,0,0],[4,1,1,1,0,0,0],[4,1,2,0,0,0,0],[4,2,0,0,0,0,0],[4,2,0,0,1,0,0],[4,2,0,1,0,0,0],[4,2,1,0,0,0,0],[4,3,0,0,0,0,0],[4,4,0,0,0,0,0],[5,0,0,0,0,0,0],[5,0,0,0,0,0,1],[5,0,0,0,0,1,0],[5,0,0,0,1,0,0],[5,0,0,1,0,0,0],[5,0,0,2,0,0,0],[5,0,1,0,0,0,0],[5,0,1,0,1,0,0],[5,0,1,1,0,0,0],[5,0,2,0,0,0,0],[5,1,0,0,0,0,0],[5,1,0,0,0,1,0],[5,1,0,0,1,0,0],[5,1,0,1,0,0,0],[5,1,1,0,0,0,0],[5,2,0,0,0,0,0],[5,2,1,0,0,0,0],[5,3,0,0,0,0,0],[6,0,0,0,0,0,0],[6,0,0,0,0,0,1],[6,0,0,0,0,1,0],[6,0,0,0,1,0,0],[6,0,0,1,0,0,0],[6,0,1,0,0,0,0],[6,0,2,0,0,0,0],[6,1,0,0,0,0,0],[6,1,0,1,0,0,0],[6,1,1,0,0,0,0],[6,2,0,0,0,0,0],[7,0,0,0,0,0,0],[7,0,0,0,1,0,0],[7,0,0,1,0,0,0],[7,0,1,0,0,0,0],[7,1,0,0,0,0,0],[7,2,0,0,0,0,0],[8,0,0,0,0,0,0],[8,0,1,0,0,0,0],[8,1,0,0,0,0,0],[9,0,0,0,0,0,0],[10,0,0,0,0,0,0]]

def binRuns : List (Nat × Nat × Nat) := [(1,1,0),(2,2,70),(3,3,111),(4,4,140),(5,5,162),(6,6,181),(7,7,196),(8,8,209),(9,9,221),(10,10,232),(11,11,241),(12,12,250),(13,13,258),(14,14,266),(15,15,273),(16,16,279),(17,17,285),(18,18,291),(19,19,296),(20,20,302),(21,21,306),(22,22,311),(23,23,316),(24,24,320),(25,25,324),(26,26,328),(27,27,332),(28,28,335),(29,29,339),(30,30,342),(31,31,346),(32,32,349),(33,33,352),(34,34,355),(35,35,358),(36,36,361),(37,37,363),(38,38,366),(39,39,369),(40,40,371),(41,41,374),(42,42,376),(43,43,378),(44,44,381),(45,45,383),(46,46,385),(47,47,387),(48,48,390),(49,49,392),(50,50,394),(51,51,396),(52,52,398),(53,53,400),(54,54,401),(55,55,403),(56,56,405),(57,57,407),(58,58,409),(59,59,410),(60,60,412),(61,61,414),(62,62,415),(63,63,417),(64,64,418),(65,65,420),(66,66,422),(67,67,423),(68,68,425),(69,69,426),(70,70,427),(71,71,429),(72,72,430),(73,73,432),(74,74,433),(75,75,434),(76,76,436),(77,77,437),(78,78,438),(79,79,440),(80,80,441),(81,81,442),(82,82,443),(83,83,445),(84,84,446),(85,85,447),(86,86,448),(87,87,449),(88,88,450),(89,89,452),(90,90,453),(91,91,454),(92,92,455),(93,93,456),(94,94,457),(95,95,458),(96,96,459),(97,97,460),(98,98,461),(99,99,462),(100,100,463),(101,101,464),(102,102,465),(103,103,466),(104,104,467),(105,105,468),(106,106,469),(107,107,470),(108,108,471),(109,109,472),(110,110,473),(111,111,474),(112,112,475),(113,114,476),(115,115,477),(116,116,478),(117,117,479),(118,118,480),(119,119,481),(120,121,482),(122,122,483),(123,123,484),(124,124,485),(125,125,486),(126,127,487),(128,128,488),(129,129,489),(130,131,490),(132,132,491),(133,133,492),(134,135,493),(136,136,494),(137,137,495),(138,139,496),(140,140,497),(141,141,498),(142,143,499),(144,144,500),(145,146,501),(147,147,502),(148,149,503),(150,150,504),(151,152,505),(153,153,506),(154,155,507),(156,156,508),(157,158,509),(159,159,510),(160,161,511),(162,163,512),(164,164,513),(165,166,514),(167,168,515),(169,169,516),(170,171,517),(172,173,518),(174,174,519),(175,176,520),(177,178,521),(179,180,522),(181,182,523),(183,183,524),(184,185,525),(186,187,526),(188,189,527),(190,191,528),(192,193,529),(194,195,530),(196,197,531),(198,199,532),(200,201,533),(202,203,534),(204,205,535),(206,207,536),(208,209,537),(210,211,538),(212,213,539),(214,215,540),(216,217,541),(218,219,542),(220,222,543),(223,224,544),(225,226,545),(227,228,546),(229,231,547),(232,233,548),(234,235,549),(236,238,550),(239,240,551),(241,242,552),(243,245,553),(246,247,554),(248,250,555),(251,252,556),(253,255,557),(256,257,558),(258,260,559),(261,263,560),(264,265,561),(266,268,562),(269,270,563),(271,273,564),(274,276,565),(277,279,566),(280,281,567),(282,284,568),(285,287,569),(288,290,570),(291,293,571),(294,296,572),(297,299,573),(300,302,574),(303,305,575),(306,308,576),(309,311,577),(312,314,578),(315,317,579),(318,320,580),(321,324,581),(325,327,582),(328,330,583),(331,333,584),(334,337,585),(338,340,586),(341,344,587),(345,347,588),(348,350,589),(351,354,590),(355,358,591),(359,361,592),(362,365,593),(366,368,594),(369,372,595),(373,376,596),(377,380,597),(381,383,598),(384,387,599),(388,391,600),(392,395,601),(396,399,602),(400,403,603),(404,407,604),(408,411,605),(412,415,606),(416,419,607),(420,424,608),(425,428,609),(429,432,610),(433,436,611),(437,441,612),(442,445,613),(446,450,614),(451,454,615),(455,459,616),(460,463,617),(464,468,618),(469,473,619),(474,477,620),(478,482,621),(483,487,622),(488,492,623),(493,497,624),(498,502,625),(503,507,626),(508,512,627),(513,517,628),(518,522,629),(523,527,630),(528,533,631),(534,538,632),(539,543,633),(544,549,634),(550,554,635),(555,560,636),(561,565,637),(566,571,638),(572,577,639),(578,583,640),(584,588,641),(589,594,642),(595,600,643),(601,606,644),(607,612,645),(613,618,646),(619,625,647),(626,631,648),(632,637,649),(638,644,650),(645,650,651),(651,656,652),(657,663,653),(664,670,654),(671,676,655),(677,683,656),(684,690,657),(691,697,658),(698,704,659),(705,711,660),(712,718,661),(719,725,662),(726,732,663),(733,740,664),(741,747,665),(748,755,666),(756,762,667),(763,770,668),(771,778,669),(779,785,670),(786,793,671),(794,801,672),(802,809,673),(810,817,674),(818,825,675),(826,834,676),(835,842,677),(843,850,678),(851,859,679),(860,868,680),(869,876,681),(877,885,682),(886,894,683),(895,903,684),(904,912,685),(913,921,686),(922,930,687),(931,939,688),(940,949,689),(950,958,690),(959,968,691),(969,978,692),(979,987,693),(988,997,694),(998,1007,695),(1008,1017,696),(1018,1028,697),(1029,1038,698),(1039,1048,699),(1049,1059,700),(1060,1069,701),(1070,1080,702),(1081,1091,703),(1092,1102,704),(1103,1113,705),(1114,1124,706),(1125,1135,707),(1136,1146,708),(1147,1158,709),(1159,1169,710),(1170,1181,711),(1182,1193,712),(1194,1205,713),(1206,1217,714),(1218,1229,715),(1230,1241,716),(1242,1254,717),(1255,1266,718),(1267,1279,719),(1280,1292,720),(1293,1305,721),(1306,1318,722),(1319,1331,723),(1332,1344,724),(1345,1358,725),(1359,1371,726),(1372,1385,727),(1386,1399,728),(1400,1413,729),(1414,1427,730),(1428,1441,731),(1442,1456,732),(1457,1470,733),(1471,1485,734),(1486,1500,735),(1501,1515,736),(1516,1530,737),(1531,1545,738),(1546,1561,739),(1562,1576,740),(1577,1592,741),(1593,1608,742),(1609,1624,743),(1625,1640,744),(1641,1657,745),(1658,1673,746),(1674,1690,747),(1691,1707,748),(1708,1724,749),(1725,1741,750),(1742,1759,751),(1760,1776,752),(1777,1794,753),(1795,1812,754),(1813,1830,755),(1831,1849,756),(1850,1867,757),(1868,1886,758),(1887,1905,759),(1906,1924,760),(1925,1943,761),(1944,1962,762),(1963,1982,763),(1983,2002,764),(2003,2022,765),(2023,2042,766),(2043,2062,767),(2063,2083,768),(2084,2104,769),(2105,2125,770),(2126,2146,771),(2147,2168,772),(2169,2189,773),(2190,2211,774),(2212,2233,775),(2234,2256,776),(2257,2278,777),(2279,2301,778),(2302,2324,779),(2325,2347,780),(2348,2371,781),(2372,2395,782),(2396,2418,783),(2419,2443,784),(2444,2467,785),(2468,2492,786),(2493,2517,787),(2518,2542,788),(2543,2567,789),(2568,2593,790),(2594,2619,791),(2620,2645,792),(2646,2672,793),(2673,2698,794),(2699,2725,795),(2726,2753,796),(2754,2780,797),(2781,2808,798),(2809,2836,799),(2837,2864,800),(2865,2893,801),(2894,2922,802),(2923,2951,803),(2952,2981,804),(2982,3010,805),(3011,3041,806),(3042,3071,807),(3072,3102,808),(3103,3133,809),(3134,3164,810),(3165,3196,811),(3197,3228,812),(3229,3260,813),(3261,3293,814),(3294,3325,815),(3326,3359,816),(3360,3392,817),(3393,3426,818),(3427,3461,819),(3462,3495,820),(3496,3530,821),(3531,3565,822),(3566,3601,823),(3602,3637,824),(3638,3673,825),(3674,3710,826),(3711,3747,827),(3748,3785,828),(3786,3823,829),(3824,3861,830),(3862,3899,831),(3900,3938,832),(3939,3978,833),(3979,4018,834),(4019,4058,835),(4059,4098,836),(4099,4139,837),(4140,4181,838),(4182,4223,839),(4224,4265,840),(4266,4307,841),(4308,4351,842),(4352,4394,843),(4395,4438,844),(4439,4482,845),(4483,4527,846),(4528,4573,847),(4574,4618,848),(4619,4664,849),(4665,4711,850),(4712,4758,851),(4759,4806,852),(4807,4854,853),(4855,4902,854),(4903,4951,855),(4952,5001,856),(5002,5051,857),(5052,5101,858),(5102,5152,859),(5153,5204,860),(5205,5256,861),(5257,5309,862),(5310,5362,863),(5363,5415,864),(5416,5470,865),(5471,5524,866),(5525,5579,867),(5580,5635,868),(5636,5692,869),(5693,5749,870),(5750,5806,871),(5807,5864,872),(5865,5923,873),(5924,5982,874),(5983,6042,875),(6043,6102,876),(6103,6163,877),(6164,6225,878),(6226,6287,879),(6288,6350,880),(6351,6414,881),(6415,6478,882),(6479,6542,883),(6543,6608,884),(6609,6674,885),(6675,6741,886),(6742,6808,887),(6809,6876,888),(6877,6945,889),(6946,7014,890),(7015,7085,891),(7086,7155,892),(7156,7227,893),(7228,7299,894),(7300,7372,895),(7373,7446,896),(7447,7520,897),(7521,7596,898),(7597,7672,899),(7673,7748,900),(7749,7826,901),(7827,7904,902),(7905,7983,903),(7984,8063,904),(8064,8144,905),(8145,8225,906),(8226,8307,907),(8308,8390,908),(8391,8474,909),(8475,8559,910),(8560,8645,911),(8646,8731,912),(8732,8818,913),(8819,8907,914),(8908,8996,915),(8997,9086,916),(9087,9176,917),(9177,9268,918),(9269,9361,919),(9362,9455,920),(9456,9549,921),(9550,9645,922),(9646,9741,923),(9742,9838,924),(9839,9937,925),(9938,10036,926),(10037,10137,927),(10138,10238,928),(10239,10340,929),(10341,10444,930),(10445,10548,931),(10549,10654,932),(10655,10760,933),(10761,10868,934),(10869,10977,935),(10978,11086,936),(11087,11197,937),(11198,11260,938)]

def binPairs : List (Nat × Nat) := binRuns.flatMap fun e =>
  (List.range' e.1 (e.2.1 - e.1 + 1)).map fun c => (c, e.2.2)

def bins : Array Nat := (0 :: binPairs.map Prod.snd).toArray


def additionBins : Array Nat := #[70,70,69,69,68,68,67,67,66,66,65,65,64,64,63,63,62,62,62,61,61,60,60,59,59,58,58,58,57,57,56,56,55,55,55,54,54,53,53,53,52,52,51,51,51,50,50,49,49,49,48,48,47,47,47,46,46,46,45,45,45,44,44,44,43,43,42,42,42,41,41,41,40,40,40,40,39,39,39,38,38,38,37,37,37,36,36,36,35,35,35,35,34,34,34,33,33,33,33,32,32,32,32,31,31,31,31,30,30,30,30,29,29,29,29,28,28,28,28,27,27,27,27,26,26,26,26,26,25,25,25,25,24,24,24,24,24,23,23,23,23,23,22,22,22,22,22,21,21,21,21,21,21,20,20,20,20,20,19,19,19,19,19,19,18,18,18,18,18,18,17,17,17,17,17,17,17,16,16,16,16,16,16,16,15,15,15,15,15,15,15,15,14,14,14,14,14,14,14,13,13,13,13,13,13,13,13,13,12,12,12,12,12,12,12,12,12,11,11,11,11,11,11,11,11,11,11,10,10,10,10,10,10,10,10,10,10,10,9,9,9,9,9,9,9,9,9,9,9,9,9,8,8,8,8,8,8,8,8,8,8,8,8,8,8,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]

def used (ms : List Nat) : Nat :=
  (ms.zipIdx 2).foldl (fun s e => s + e.1 * e.2) 0

def groups (ms : List Nat) : Nat := ms.sum

def profileWeight (K r : Nat) (ms : List Nat) : Nat :=
  let singles := r - used ms
  let count := singles + groups ms
  fact K * fact r /
    (fact (K - count) * fact singles *
      (ms.zipIdx 2).foldl (fun s e => s * fact e.2 ^ e.1 * fact e.1) 1)

def profilePacked (bits : Nat) (ms : List Nat) : Nat :=
  (ms.zipIdx 2).foldl (fun s e => s * coverageHPackBits bits e.2 ^ e.1) 1

def coordinatePacked (bits K r : Nat) : Nat :=
  profiles.foldl (fun acc ms =>
    if used ms ≤ r ∧ r - used ms + groups ms ≤ K then
      acc + profileWeight K r ms * 563 ^ (r - used ms) *
        (profilePacked bits ms <<< (bits * (r - used ms)))
    else acc) 0

def pack (bits : Nat) (xs : Array Nat) : Nat :=
  xs.toList.foldr (fun a s => a + (s <<< bits)) 0

def coefficient (bits p i : Nat) : Nat := (p >>> (bits * i)) % 2 ^ bits

def unpack (bits length p : Nat) : Array Nat :=
  Array.ofFn fun i : Fin length => coefficient bits p i.val

def multiply (bits : Nat) (a b : Array Nat) : Array Nat :=
  unpack bits (a.size + b.size - 1) (pack bits a * pack bits b)

structure Binned where
  probability : Array Nat
  first : Array Nat

def coordinateBinned (K r : Nat) : Binned :=
  let p := coordinatePacked 512 K r
  (List.range (563 * r + 1)).foldl (fun acc c =>
    let weight := coefficient 512 p c
    let b := bins[c]?.getD 0
    { probability := acc.probability.set! b (acc.probability[b]!.add weight)
      first := acc.first.set! b (acc.first[b]!.add (c * weight)) })
    { probability := Array.replicate 1024 0, first := Array.replicate 1024 0 }

def productBinned (a : Binned) : Binned :=
  { probability := multiply 1024 a.probability a.probability
    first := multiply 1024 a.first a.first }

def addBinned (a b : Binned) : Binned :=
  let nonzeroA := a.probability.toList.zipIdx.filter (fun e => e.1 != 0)
  let nonzeroB := b.probability.toList.zipIdx.filter (fun e => e.1 != 0)
  nonzeroA.foldl (fun outer ae =>
    nonzeroB.foldl (fun acc be =>
      let i := ae.2
      let j := be.2
      let label := max i j + (additionBins[i - j + (j - i)]?.getD 0)
      let probability := a.probability[i]! * b.probability[j]!
      let first := a.first[i]! * b.probability[j]! + a.probability[i]! * b.first[j]!
      { probability := acc.probability.set! label (acc.probability[label]! + probability)
        first := acc.first.set! label (acc.first[label]! + first) }) outer)
    { probability := Array.replicate 2118 0, first := Array.replicate 2118 0 }

def accumulate (weight : Nat) (a b : Binned) : Binned :=
  { probability := Array.ofFn fun i : Fin 2118 =>
      a.probability[i.val]?.getD 0 + weight * (b.probability[i.val]?.getD 0)
    first := Array.ofFn fun i : Fin 2118 =>
      a.first[i.val]?.getD 0 + weight * (b.first[i.val]?.getD 0) }

def pairBinned (r : Nat) : Binned :=
  let branches := (List.range (r + 1)).map fun t => productBinned (coordinateBinned 64 t)
  (List.range (r + 1)).foldl (fun acc t =>
    let empty : Binned := { probability := #[], first := #[] }
    let a := branches.getD t empty
    let b := branches.getD (r - t) empty
    let row := if t = 0 then b else if r - t = 0 then a else addBinned a b
    accumulate (fact r / (fact t * fact (r - t))) acc row)
    { probability := Array.replicate 2118 0, first := Array.replicate 2118 0 }

def forestPacked (r : Nat) : Nat :=
  pack 4096 (pairBinned r).first ^ 4 * pack 4096 (coordinateBinned 128 r).first

theorem profile_count : profiles.length = 434 := by decide +kernel

theorem profile_width : profiles.all (fun ms => ms.length == 7) = true := by decide +kernel

theorem bin_count : bins.size = 11261 := by decide +kernel

theorem addition_bin_count : additionBins.size = 2049 := by decide +kernel

#print axioms profile_count
#print axioms profile_width
#print axioms bin_count
#print axioms addition_bin_count


def binRunsCheck : Bool := binRuns.all fun e =>
  let lo := e.1
  let hi := e.2.1
  let b := e.2.2
  decide (1 ≤ lo ∧ lo ≤ hi ∧ hi * 100 ^ b ≤ 101 ^ b ∧
    100 * 101 ^ b ≤ 101 * lo * 100 ^ b)

theorem bin_indices_checked : binPairs.map Prod.fst = List.range' 1 11260 := by decide +kernel

theorem bin_runs_checked : binRunsCheck = true := by decide +kernel

def additionBounds : Bool := (List.range 2049).all fun d =>
  let b := additionBins[d]?.getD 0
  decide (100 ^ b * (101 ^ d + 100 ^ d) ≤ 101 ^ (b + d) ∧
    100 * 101 ^ (b + d) ≤ 101 * 100 ^ b * (101 ^ d + 100 ^ d))

def additionChunk (block : Nat) : Bool := (List.range 128).all fun j =>
  let d := 128 * block + j
  if d < 2049 then
    let b := additionBins[d]?.getD 0
    decide (100 ^ b * (101 ^ d + 100 ^ d) ≤ 101 ^ (b + d) ∧
      100 * 101 ^ (b + d) ≤ 101 * 100 ^ b * (101 ^ d + 100 ^ d))
  else true

theorem addition_chunk_0 : additionChunk 0 = true := by decide +kernel

theorem addition_chunk_1 : additionChunk 1 = true := by decide +kernel

theorem addition_chunk_2 : additionChunk 2 = true := by decide +kernel

theorem addition_chunk_3 : additionChunk 3 = true := by decide +kernel

theorem addition_chunk_4 : additionChunk 4 = true := by decide +kernel

theorem addition_chunk_5 : additionChunk 5 = true := by decide +kernel

theorem addition_chunk_6 : additionChunk 6 = true := by decide +kernel

theorem addition_chunk_7 : additionChunk 7 = true := by decide +kernel

theorem addition_chunk_8 : additionChunk 8 = true := by decide +kernel

theorem addition_chunk_9 : additionChunk 9 = true := by decide +kernel

theorem addition_chunk_10 : additionChunk 10 = true := by decide +kernel

theorem addition_chunk_11 : additionChunk 11 = true := by decide +kernel

theorem addition_chunk_12 : additionChunk 12 = true := by decide +kernel

theorem addition_chunk_13 : additionChunk 13 = true := by decide +kernel

theorem addition_chunk_14 : additionChunk 14 = true := by decide +kernel

theorem addition_chunk_15 : additionChunk 15 = true := by decide +kernel

theorem addition_chunk_16 : additionChunk 16 = true := by decide +kernel

theorem addition_chunks : ∀ b : Fin 17, additionChunk b.val = true := by
  intro b
  fin_cases b
  · exact addition_chunk_0
  · exact addition_chunk_1
  · exact addition_chunk_2
  · exact addition_chunk_3
  · exact addition_chunk_4
  · exact addition_chunk_5
  · exact addition_chunk_6
  · exact addition_chunk_7
  · exact addition_chunk_8
  · exact addition_chunk_9
  · exact addition_chunk_10
  · exact addition_chunk_11
  · exact addition_chunk_12
  · exact addition_chunk_13
  · exact addition_chunk_14
  · exact addition_chunk_15
  · exact addition_chunk_16

theorem addition_bounds_checked : additionBounds = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi : i < 2049 := List.mem_range.mp hi
  have h := addition_chunks (⟨i / 128, by omega⟩ : Fin 17)
  have h := List.all_eq_true.mp h (i % 128) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have he : 128 * (i / 128) + i % 128 = i := by omega
  simpa only [he, if_pos hi] using h

#print axioms bin_runs_checked
#print axioms addition_bounds_checked


open Finset

def profileList (i : Fin 434) : List Nat := profiles[i.val]?.getD []

def profileVector (K r : Nat) (ms : List Nat) (a : Fin 21) : Nat :=
  if a.val = 0 then K - ((r - used ms) + groups ms)
  else if a.val = 1 then r - used ms else ms[a.val - 2]?.getD 0

def profileChecks : Bool := [64, 128].all fun K => (List.range 21).all fun r =>
  profiles.all fun ms => if used ms ≤ r then
    decide ((∑ a : Fin 21, profileVector K r ms a) = K ∧
      (∑ a : Fin 21, profileVector K r ms a * a.val) = r ∧
      Nat.multinomial univ (profileVector K r ms) *
        (r.factorial / ∏ a : Fin 21, a.val.factorial ^ profileVector K r ms a) =
          profileWeight K r ms) else true

theorem profile_checks : profileChecks = true := by decide +kernel

theorem profile_nodup : profiles.Nodup := by decide +kernel

theorem profile_lengths : ∀ i : Fin 434, (profileList i).length = 7 := by decide +kernel

#print axioms profile_checks
#print axioms profile_nodup

end ClaudeWCT.Numerics.SharedPathReflection

/-! Outward-rounded integer certificate for the canonical ancestor-only search.
This certifies the finite recurrence and tail arithmetic. The correspondence
between these histogram coefficients and the scheme remains a separate theorem;
this packet alone is not a submission certificate. -/
namespace ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.WCT9.CanonicalPolicy
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

def scale : Nat := 2 ^ 128
def zNum : Nat := 1310720000000000
def zDen : Nat := 1310713068528192
def lowerDen : Nat := 4 * 2 ^ 128
def topDen : Nat := 2 * 2 ^ 128

def lowerHistogram : List (Nat × Nat) := [(0,153444473208033179429694980872),(1,2603151924714466294019052388963),(2,20986271764081333830008054779760),(3,107105760251148403612582579034786),(4,389802434875012227704943762352373),(5,1084398973647231389354278405741267),(6,2426499606200581437325783049510402),(7,4564961527394431065672251671168434),(8,7517836644877742650194231336400435),(9,11201368180903637473939834945902771),(10,15419888023436772838176646819197447),(11,19818393098787965059925970536881726),(12,23953640657767674089629450567686673),(13,27458954627662242550605832098078611),(14,30078502466085289971190669939022541),(15,31593870847544609627288425487795300),(16,31878638281679321027694572092317446),(17,31008828274191464437251452806915946),(18,29188027243074056504048492083317090),(19,26613342508999333159256613293731832),(20,23507025019922928195091905139266085),(21,20159558826306599057644917349782308),(22,16826924178639856623554235604383159),(23,13664362091837025981656732821836020),(24,10789476641754451330193792087267433),(25,8303015803263539580411735656653466),(26,6237182652151356306641212969523142),(27,4565566085205989179480097840900364),(28,3255243211876616911050183836109609),(29,2267539780294521492859788079725306),(30,1543597036475039405081434254153552),(31,1023596766466045320166293775631672),(32,661841297479006015919864807220632),(33,418869807034749922197622700752230),(34,258865867457849147684658418315136),(35,155587076563543255324396097304476),(36,91328672620483967731818332728032),(37,52532573965878370120026231305260),(38,29399368397825254083516976031751),(39,15972646411382546997357714321448),(40,8504671038034401955587712836301),(41,4430225920550691871251188239378),(42,2229085094874775410518945917966),(43,1090393841644836365148467134858),(44,525420092966156693595847927454),(45,245415626775696379215678387244),(46,109752971917660950253113254992),(47,48220428507323156420614645920),(48,20878085802935884848519247816),(49,8564929109887745930344539026),(50,3368619434520057818043756351),(51,1331358368941159429012841440),(52,506095199873329291763702962),(53,176458154514101793057253760),(54,61268491325112599100086010),(55,21648073447216482997109176),(56,6809479906811389214116794),(57,1970092178594006505324440),(58,625313570037967157321268),(59,185257596510871859200072),(60,43356202958295567950834),(61,10987535369414193077796),(62,3212438385103111352496),(63,652700522566208126472),(64,108697191930827702664),(65,29662450030490919642),(66,6031635597387741033),(67,511002482588476956),(68,100447039695304071),(69,27300612607404444),(70,2275028324796150),(71,44374330952952),(72,28037846052909),(73,587987786232),(76,276783507)]

def topAcceptedHistogram : List (Nat × Nat) := [(16,1629513920717367178462502201183008),(17,2377682533872567903895621729516690),(18,3319666487042959637100251799006221),(19,4450478968008844732578027780636155),(20,5745896184304563633680072635810908),(21,7161990307079117979381414214273959),(22,8637078121563446902903784488881047),(23,10095791788880322096405999312107710),(24,11455670028571828256859174942549805),(25,12635593167324231545568317609543376),(26,13563851991499452271014303975337494),(27,14184771298890755536649371829910588),(28,14464203659170457344066970785574733),(29,14392824498496276724879395520552778),(30,13985677745901162112237959532044883),(31,13278978309211897233587094426885101),(32,12325833183012903565021975601490982),(33,11190505137419017615005127806855772),(34,9941373292247253067330985431908193),(35,8644735630519553585760209281069574),(36,7360327074597161298878439303617970),(37,6137700875751372076828657436426827),(38,5013839040367872922959473862821436),(39,4012884846696203398038639053729846),(40,3147233939057428196804193939435396),(41,2419030040063890062400968075226934),(42,1822266690124357519873354528880354),(43,1345378193007425969240644190919725),(44,973531269563332143000391100367351),(45,690426881466441338864001907499071),(46,479843365501970304593216946564971),(47,326777055242828712504450611965989),(48,218041162417163084630070793964530),(49,142522389088599627942804717208956),(50,91239320795641956893781419319450),(51,57195484323739080377910476637049),(52,35102565478677636419889421431202),(53,21084796213879045945218908098346),(54,12391374241342393114830726461040),(55,7123622154332796577375860514930),(56,4004699190108601464270582379671),(57,2200526948312465096674414941948),(58,1181530221952819346404871106801),(59,619751735515552300777088762708),(60,317407610559516698027766577177),(61,158644802077785888775583444549),(62,77367850892329515698513515193),(63,36799709320344370135359745473),(64,17058651870432074398522351467),(65,7703749380118911572008627654),(66,3388874160104642349683744410),(67,1450871701748223263156539651),(68,603980931721268958009591244),(69,244469801170038102452347252),(70,96160597255736097875479137),(71,36693975949927599734321919),(72,13574923707192617498694155),(73,4869583637504887313001304),(74,1690246582884551909911192),(75,566303480573950359276107),(76,183224654575564010732939),(77,57182201957186505882715),(78,17126553569153293066872),(79,4915707191260638955639),(80,1354137641039914657344),(81,355801350862393048747),(82,88529954980792947901),(83,20929046317738944191),(84,4687550848624239522),(85,977691447281148006),(86,189555515672504256),(87,34539282906428655),(88,5798478800310011),(89,874534611695010),(90,120033569527014),(91,14633033422772),(92,1481594846676),(93,138895847313),(94,13140506641),(95,890409223),(96,35920071),(97,741573),(98,9900),(99,990),(100,18)]

def rowOne : Array Nat := #[358938938355342476006306828392166000982,358938938355342476006649155677955642836,358938938355342476024071718179531352924,358938938355342476460103541693963741599,358938938355342483614270800992826151754,358938938355342570186387039347955423221,358938938355343394384341387607427808298,358938938355349826005895150331848995098,358938938355392151663062705861577264043,358938938355632046478310942089134572620,358938938356822368967636623983777940510,358938938362061497613763735209811764136,358938938382742863278035911664712380562,358938938456656342906680347908385289809,358938938697811463606242176897573910924,358938939421464521648785751321345879685,358938941432264088474127772079313493202,358938946638440412470654753009046150192,358938959270794071381869856584577408113,358938988149889631434755974784180553093,358939050661467754232700550591662253451,358939179364484742792703841222833459645,358939432453971647412388614262298832668,358939909601114583763655256274363069437,358940774932976381067702508252438421136,358942288974991258921822339142017565861,358944851076498153583548132522079913267,358949052997287754273947955269904151259,358955742969019915770280260275223242755,358966098021747991882841177826821921880,358981701283591527136896902171745140798,359004620878316443501829142734895515306,359037488384583149899888008823375775280,359083577558922695601260127048554234210,359146884803380145244524946876042897299,359232200628027889980592053834889176560,359345130336732708795647454426356275763,359492012680055493094117078933326981184,359679769418310772222370724031597220454,359915858043363140750205364132211372509,360207803900926998362005224341130128763,360559413695008674955753027402768749845,360980106112868955155595135139762741982,361480532005205405347356006750681573936,362075683599516678063439738967209927385,362753430225354504665801543963710353342,363541026217329242936494798742744101604,364472269784683683081247143919245105873,365589621303686977459256023683271148011,366954019292159456808138860345676462592,368652676707825217809271789133631956138,370810254128953020536516235003870609218]

def rowTwo : Array Nat := #[352609111977080085841896220337467755047,352609111977080980396737639261752133886,352609111977111332355502258975196001661,352609111977613491147672427799718637635,352609111983013856719872646238355258076,352609112025486711474921329650659019815,352609112286167787285084301494856975123,352609113587872357252690166409203246890,352609119034874997090235693423343450779,352609138572917060099127302877746112574,352609199767188703746552883723348361883,352609369803210550839471970895947352614,352609794921718571128550429388240107346,352610763618033313872374923977963286042,352612798952542833900403606614017146650,352616783721995162127169016264149132685,352624120592920510669263921941832588212,352636928172418907324910793517771072606,352658273060639524750351070258838771318,352692429891568951138037114692259248574,352745126795242177044664423808627933093,352823670589163821016326792980657278852,352936832523009295345949749134176539664,353093608173228648195235806815127671202,353303379320283117317599959886660739291,353575562518686091283606268131598938469,353920291044397850112857727741087378638,354349563854177309615631241003674944464,354878865138414626149430401569560271243,355529284144049626953522749387217212184,356330146236129510312905823744025817568,357322821909304252458560912597433885848,358566467736001037114882884097600751696,360145563344758222585765479536385749436,362180767599513973002292945400978317534]

def rowThree : Array Nat := #[346390910997172446261317588447252241589,346390913334784426154069975066773243443,346390952992132987918612901307984409617,346391272723321708602527111263857300919,346392905028270648510669496391726414253,346398853036797739008098976531387127524,346415460997262312059166074154467095412,346452952410283847960051654871681405868,346524741576567340695496957691794468772,346646679787940123624990662955090074152,346837466204671079097269392975931523707,347119621244626147422091346075572776058,347520020780996969755587541231322045967,348071329062203720065906119396171465259,348816523835221856110121188376537665887,349815610358409162081576246163331713611,351152248739931451769968010626328709791,352943433860824388966925479988459495172]

def initialBound : Nat := 365364585468063845982778503300967050589

def ftsNum : Nat := 734 * 563 ^ 9 * 52061563476303414825532212503848335359868928

def ftsDen : Nat := 2 ^ 14 * 1024 ^ 9 * 52416169542617085727767971710947931910569984

def ftsBound : Nat := 349325989776095170129832986894036643760

def fixedBound : Nat := 617358996970638686225956552741729761734

def acceptedMass (hist : List (Nat × Nat)) (floor : Nat) : Nat :=
  (hist.filter (fun e => decide (floor ≤ e.1))).foldl (fun n e => n + e.2) 0

def nextMass (hist : List (Nat × Nat)) (floor residual : Nat) (next : Array Nat) : Nat :=
  (hist.filter (fun e => decide (floor ≤ e.1))).foldl
    (fun n e => n + e.2 * (next[residual - e.1]?.getD 0)) 0

def recurrenceCheck (den : Nat) (hist : List (Nat × Nat)) (floor residual : Nat)
    (next : Array Nat) (value : Nat) : Bool :=
  let mass := acceptedMass hist floor
  decide (scale ≤ value) && decide (mass ≤ den) &&
    hist.all (fun e => decide (floor ≤ e.1 → residual - e.1 < next.size)) &&
    decide (zNum * (den - mass) < zDen * den) &&
    decide (zNum * nextMass hist floor residual next ≤
      value * (zDen * den - zNum * (den - mass)))

def checkRows (stage : Nat) (row next : Array Nat) : Bool :=
  (List.range row.size).all fun residual =>
    recurrenceCheck lowerDen lowerHistogram (threshold stage residual) residual next row[residual]!

def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d
def mulUp (a b : Nat) : Nat := ceilDiv (a * b) scale
def mulDown (a b : Nat) : Nat := a * b / scale

def powerUp (base exponent : Nat) : Nat :=
  if exponent = 0 then scale else
    let half := powerUp (mulUp base base) (exponent / 2)
    if exponent % 2 = 0 then half else mulUp base half
termination_by exponent
decreasing_by omega

def powerDown (base exponent : Nat) : Nat :=
  if exponent = 0 then scale else
    let half := powerDown (mulDown base base) (exponent / 2)
    if exponent % 2 = 0 then half else mulDown base half
termination_by exponent
decreasing_by omega

def tailCheck (num den block : Nat) : Bool :=
  decide (powerDown (scale + block * num * scale / den) 4096 ≥ 2 ^ 400 * scale)

theorem row_three_checked : checkRows 3 rowThree #[scale] = true := by decide +kernel
theorem row_two_checked : checkRows 2 rowTwo rowThree = true := by decide +kernel
theorem row_one_checked : checkRows 1 rowOne rowTwo = true := by decide +kernel

theorem initial_checked :
    recurrenceCheck topDen topAcceptedHistogram 16 63 rowOne initialBound = true := by
  decide +kernel

theorem fts_moment_checked :
    ftsNum ≤ ftsDen ∧ zNum * (ftsDen - ftsNum) < zDen * ftsDen ∧
      zNum * ftsNum * scale ≤ ftsBound * (zDen * ftsDen - zNum * (ftsDen - ftsNum)) := by
  decide +kernel

theorem fixed_power_checked :
    powerUp (ceilDiv (zNum * scale) zDen) 112640 ≤ fixedBound := by
  decide +kernel

theorem full_moment_checked :
    mulUp (mulUp fixedBound ftsBound) initialBound * 100000 < 199976 * scale := by
  decide +kernel

theorem lower_thresholds_checked :
    (List.range rowOne.size).all (fun r => decide (threshold 1 r ≤ 17)) = true ∧
    (List.range rowTwo.size).all (fun r => decide (threshold 2 r ≤ 17)) = true ∧
    (List.range rowThree.size).all (fun r => decide (threshold 3 r ≤ 17)) = true := by
  decide +kernel

theorem lower_tail_checked : tailCheck (acceptedMass lowerHistogram 17) lowerDen 512 = true := by
  decide +kernel

theorem top_tail_checked : tailCheck (acceptedMass topAcceptedHistogram 16) topDen 1024 = true := by
  decide +kernel

theorem fts_tail_checked : tailCheck ftsNum ftsDen 512 = true := by decide +kernel

theorem union_bound_arithmetic : (5 : Nat) * 2 ^ 256 * 2 ^ 128 ≤ 2 ^ 400 := by decide +kernel

#print axioms row_three_checked
#print axioms row_two_checked
#print axioms row_one_checked
#print axioms initial_checked
#print axioms fts_moment_checked
#print axioms fixed_power_checked
#print axioms full_moment_checked
#print axioms lower_tail_checked
#print axioms top_tail_checked
#print axioms fts_tail_checked
end ClaudeWCT.Numerics.CanonicalCompression

/-! Exact coefficient checks for the canonical search histograms.
The polynomials imported here already have proofs counting the constrained
lower words and the weighted top encodings. These checks compare every
coefficient needed by the continuation rows, including zero coefficients. -/
namespace ClaudeWCT.Numerics.CanonicalHistogram
open CanonicalCompression
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 10000000
set_option Elab.async false

def coefficient (bits packed position : Nat) : Nat :=
  (packed >>> (bits * position)) % 2 ^ bits

def histogramWeight (hist : List (Nat × Nat)) (credit : Nat) : Nat :=
  hist.foldl (fun s e => if e.1 = credit then s + e.2 else s) 0

def packHistogram (bits start length : Nat) (hist : List (Nat × Nat)) : Nat :=
  hist.foldl (fun s e => if start ≤ e.1 ∧ e.1 < start + length then
    s + (e.2 <<< (bits * (e.1 - start))) else s) 0

def lowerHistogramCheck : Bool :=
  let p := SigGolfResearch.LowerEffectiveCounting.packed
  let actual := (List.range 6).foldl (fun s zeros =>
    s + ((p >>> (132 * (65536 * zeros + 128 * 201))) % 2 ^ (132 * 128))) 0
  decide (packHistogram 132 0 128 lowerHistogram = 7 * actual)

def topHistogramCheck : Bool :=
  let p := SigGolfResearch.NonbinaryTop.EffectiveCounting.packed
  let g := SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked
  let position := 256 * 145 + 16 + 12
  let actual := ((p >>> (136 * position)) % 2 ^ (136 * 204)) +
    2 * ((g >>> (136 * (65536 + position))) % 2 ^ (136 * 204))
  decide (packHistogram 136 16 204 topAcceptedHistogram = actual)

theorem top_histogram_checked : topHistogramCheck = true := by decide +kernel
theorem lower_histogram_checked : lowerHistogramCheck = true := by decide +kernel

#print axioms top_histogram_checked
#print axioms lower_histogram_checked
end ClaudeWCT.Numerics.CanonicalHistogram

/-! Exact finite cap count for the shared forest. The machine/source bridge
proves the listed child correction distributions and their independence. -/
namespace ClaudeWCT.Numerics.SharedFtsCount
open ClaudeWCT.WCT9
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def radix : Nat := 2 ^ 256

def rankPacked : Nat := routineCosts.foldl (fun s c => s + (1 <<< (256 * (c - 75)))) 0

def childA : Nat := 16 + 64 * radix + 20 * radix ^ 2 + 20 * radix ^ 3 +
  4 * radix ^ 5 + 4 * radix ^ 6

def childBC : Nat := 16 + 64 * radix + 20 * radix ^ 2 + 20 * radix ^ 3 +
  4 * radix ^ 4 + 4 * radix ^ 5

def forestPacked : Nat := (rankPacked * childA) ^ 4 * (rankPacked * childBC) ^ 5

def retained : Nat := forestPacked % radix ^ 114 % (radix - 1)

def count : Nat := 52061563476303414825532212503848335359868928

def total : Nat := 52416169542617085727767971710947931910569984

theorem retained_eq : retained = count := by decide +kernel

theorem total_eq : (128 * 563) ^ 9 = total := by decide +kernel

theorem mass_below_radix : total < radix - 1 := by decide +kernel

theorem retained_fraction : total * 9932347962 ≤ count * 10000000000 := by decide +kernel

#print axioms retained_eq
#print axioms total_eq


def fieldA : Nat := 4 + 16 * radix + 5 * radix ^ 2 + 5 * radix ^ 3 +
  radix ^ 5 + radix ^ 6

def fieldBC : Nat := 4 + 16 * radix + 5 * radix ^ 2 + 5 * radix ^ 3 +
  radix ^ 4 + radix ^ 5

def fieldForestPacked : Nat := (rankPacked * fieldA) ^ 4 * (rankPacked * fieldBC) ^ 5

def fieldRetained : Nat := fieldForestPacked % radix ^ 114 % (radix - 1)

theorem field_retained_eq : fieldRetained * 4 ^ 9 = count := by decide +kernel

theorem field_total_eq : (32 * 563) ^ 9 * 4 ^ 9 = total := by decide +kernel

#print axioms field_retained_eq

end ClaudeWCT.Numerics.SharedFtsCount


/-! Exact paired-selector first moments, normalized to the existing nine-field
Poisson certificate. All decimal entries are checked against the signed WOTS
coverage tables; the four shared selector bits account for the factor16^r. -/
namespace ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (wpos wneg fact)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option Elab.async false

def fieldSize : Nat := 72064

def alphabetSize : Nat := (2 * (64 * 563) ^ 2) ^ 4 * (128 * 563)

def priceScaleTotal : Nat := 734 * 2 ^ 24 * 563 ^ 9

def coordinateFormula (K r : Nat) : Nat :=
  K * (wpos w1Data ((K-1)*563) r - wneg w1Data ((K-1)*563) r)

def coordinateNearFormula (K r : Nat) : Nat := K *
  (List.range 6).foldr (fun j s =>
    (wpos (wfData j) ((K-1)*563) r - wneg (wfData j) ((K-1)*563) r) + s) 0

def coord64 : Array Nat := #[0,36032,3278122432,213980594896448,12046790225538909376,622075050192602697131072,30330681705970845631160719552,1419170048350818752486494985534528,64368995505291545994575519972962238656,2849245735332801592458161951282492392250432,123665043985691726375793238441920416051578747072,5281158736870397220249360328159480578025417078611008,222489514482922730757958309741247001459606081892501663936,9265412020734733545898585276316890255416414442632475409456192,382021549686117999037682494930429417314180747550698357997585868992,15614806201890636580593703645886279065094000855837484931715243101133888,633383211551531966834226123407494323233199760079203289760938646328093057216,25518483208338085705283218232135066679597039019228787623339214116334927244172352,1021921053938088268333226527314613987945898055985792132580197781366899423208802949312,40702509760297047071389737273695930586842271204205800296512495271194720087796476397231168,1613223185553831199810154464415135018275993070904590510192212065663415895492237356958075490496,63655131939283222071578150686001834219751561988925157200604686227745589452647413127639930421582912,2501544579512677659765757437342094677362169620698829421927751798123229055781652701838054046723372452032,97941650001393223162006692401693388663828040904730337206685532113876131709901946248051615887075570001910848,3821565392555617859413476029764445651907334362594087460436403705702819151580708255991000890001900274975222595776,148643173579813681429783015607896985204973647194772065574223861373490445183646332043036482157686626247348236615031872,5764750936032608803121815377350577111132152499920361267762631822643661449287864619079759495628832398901641184551929641152,222966212831958779218369448604328403496088235935844172104686872450223756562640811578734364923062634179802623620718033661860928,8602050456155607411020541666948540320708927782597599813925378465995504384760841106065432406697097342838972401862747050569059365056,331087344988469721545486091337021359264767752227859831321483961254989679773441589336039288193388594911287433536677893293878086639623232,12715309270562382575390069725758762358492018027013487643476543580872026573391645802999575780212841943020735818218231220883522433685077780672,487320693039110767671260012934646279468385376974712442495676408879573550579522654818489518874982606032168118131047855462490808375260806520249408,18640634740163493517862278424213326806978269641312413336785810632601452403709550507528527849830109346786775988266485887904627828654855111109618950336,711727854522157803005994260388380404634541596803410344806650541550933344945016382087267715842246528406061617420504605253677371185799547250004141549820992,27128131432201236593914319997692590635386153467193817403835699108270290658147214370307533061777478910377196962740600884058983537379583913431753699099647334592,1032333173966243769911821296254877831957872910476675790868545591740042920091456597201478444702732174483504434113954270563699661652640156100520217393526434345524288,39224012893407387870029595408645730658584979573930505117212633087782883029439014943921571571399018154803281939994790767666935586950290651943175989058043663516159463616,1488165832609271118305301500837191982683192902427556743841751546032528512277007795793216591894454889158819141576510830461375729253006741409651645027146380557276240681049152,56383252289149063240519982549609224184463545502572397805167335045369794499401990135927608453138822796397091520894054790063918334810556988809821194090830287824947569169179166912,2133429471268439610621576209452928581546199599491628143077684599959084567997873649917026690356155844873048076035767160547532076889882209634878924352641399260589807569263327784213568,80623847429462313371038264186372814671358076110633841827160371447696889529747974228884084284128268892163411660730613450071997654220394667816905157077946446037202870888152257158360776896,3043207136933816638382655008213569653255061704120395882574152626345983898058544458121455235083190180019597834172438107109237654721007355857518770272003048327485605580247251675533344075291712,114737710117576499703351719403618119713046745017176350022461542605846503364377577756562864134171892607070024558243450149410222938666374306826028010409174325466938708430843266071142150964071741632,4321253875140012206436712781680086616302318981269593352060680612697871748221807019270262058017483298856042770076194041706800846578747313766411562686231346863282466410857305361800923315031046917725248,162578497823220237580358488401004383036047274617737888399616165699513241030365297217471659116187809717594399439794004533825118726396096854847730798532685539293896206266522067005694860510497903583121322176,6110624186801788567927288326733153711146372561001911613699867749399488127779804496946249872592381680994075076673950226710399337159470229949219047852248844044913391101615028400639815173686838020578602330692672,229453860008785377068004627248930418354850567648700529121582689015369314013915446192278981726119950524184939439394049758541905885846799957402062443435628482638291899885144344434295479574122416679058238398832322752,8608144130155917476827465476105688103653996354788436250662301230354138348372931044104056098224005161192457142653240399791983634075417474267103067185960674449352897334901234318559509242379831013163661797026274203147328,322659205196042764617579190413084788923596432183052842143779024422364818092692206122755478549303215084881298105120050602474074829969987756291568122304301112379968108390072257983752643871820399543868948095793687113674891456,12084091245458739790278730111661647969988138790332897765435598916265695498246802926673704665104654647293936303637323611884605620572232091270703635055368790887336007199777151506754284134372740751458445240319491131442738515156032,452203055757881115923990864245457768558816644653170215326179409307473576234259537519547335283141189590504581870348661574197828342524461980100555799289527189387195376850982938205237884450399101485640798855700436861028794087872174272,16908920721589992843665369229483399478202073766556810276433271759495237739243414674329319910431601039834063154468418224235187185586672131414701110808790444845283221673439132668520912088763455441675249588316917937738300814705342678047808,631791479608661509208712205625157251612361981945397538114504523789619413944061504232648970812947496347275153480869849494436591467424841985628991279788597916746593189954133714942081097960176062974572922183531184355435966855108413129347436736,23589514784168323477446454277105349433699868222231257374504270873469202267469016866431698676444689915060903732281961781647487521366740474866393597833908542185776349810626860912411664710808663500705860884357426304684433990725289537604264383945792,880162487870025108217928362485574876453317682642016948946736776677715831553087622595830316892758677497996551220926485088295440782183069265608348365019510744176321728508802296408879226822198047095719119424610655531742496094350725844004750347285760192,32818289600149610954300137028027523939221088281906273401633975293083233164113111362324515431827029725733210954610482149418555747790722674057754727076402700834237576835080560503531843214797384010757643743798656725855378473811664029311354328701119109274688,1222892691472814844443503507745021847268845175443856521801624058197162641470596093017938369283130522757507893724016049559391800955970728327627743375859156755124062632720308219358757851616811823721664218846597045449867867963704866718263635002068719003873870016,45539644116054976718426097791297202617531126425140247037591054952116932183558494077363704855965953486219112675935858366021487832788639311763436655779825876944361077927748794644719857274685444772491949575646402331654115136168238066646221086948007983260326741285952,1694840623419491975683264407274801389179970894719297382102738865186488846396393949281248261342029605409162299631737221065307733983730093128243533141004606759304994582405331275041026379148143195188230314072836975899471354060492896333418666708848771764896148668053944512,63039777036725434944989177791412494720918919882014278022924428070881983916117318408664731872914640106959111086167749878415760789499118976205914228368152625404439484297969914635445448957928684228311359147509267494081929731252686062720513098735596364947337107710742565755968,2343447568464084862888383016725294949859008536680322885744617985672719120054831861919677141115791856969162432942202457481648768669461294373721249674713386432982109106025090321418298667236658310757918204949519788086780988201751032714526516241431091508634520924961169857794863296,87067963514543313358757942282690479024465267598441684324386885200642524794302676777720715570849665654469989680783766220630334241271439968202954240136711501792060151675398500004423315571636485253301826968245120127831887932053040801906782580680587365462207168718866945445429385960512,3233192315450129767029464620753569807029288152611380975691351770319544238749854827784167232383036748308064580938378928848516684651143909802011340854241717255765423542796875188037511803862550077173924995600640346540646315413324683796769372531954510650922104131213818324679295226111191232,120000147954458214464857547867844775827021283363798745341646021932161567189542417062930035497401057075002632582649953527826901437883359791251408542820011906990867484074205429461637755091470592191294262970745688095925800305851644849462122624933688587035729418346746197082817293846027695299648,4451597381566245535002193913949333805149937201450796353294953331541776575372156999969583357380609490910265285127574788983330709661230681786058946274115116552485157530996532844597628584185945040925103947954332312159605738048445034443318296307690793945947270248833953078708681290385550266053648576,165059408087831965569168320008701322112146070550614496275069360617417167699607681122828699477421600008693943280506800822613584043413002295779999917248334721582774457890594732608515452176930644823829819346695622304697710680271706445204596061553596754023952264103660577155360694577129116357541680913472,6117319509520929116275423598556469340151540907988716457476900537370320552820857011599890372639854832941732348785858008768628574327312161288259109599988551543237052030029365088726782982115304859105448124478855122180490116787313545566514278859433831429747529345956438747755773511844271810411310026716764352,226612790430460546977468372079925800302065366058006673763527285916884119347473047889243442261081227647963330238673110757431234140672362022533299191038895341262066790501780019875651714494440780533882344692918786680372113954919927351558355118315601027961467304292762779457228213978092984336539450902898785393728,8391038004440380238070782080807056613498419564662353559797423372482510081695803427245006946329023154756431220974482094590173764551491804498100539341803474843029427475861360958782156472033377658036147686579808239794821014066134361402984109284410310774613005579043898902175961781399251337616811679869171855512817856,310570624233795642542160454999676574636574305172258862639619529608996012183376475955950691735646124086404217388614925674539299462010207679317196492855592037239136290669497236248249900262903255287055825810986224032627547450769495966209297730726905458950910266934039690701867045757424449260502836748622371695226386848832,11490095927166029171702302638052938416168370152700414291455379681772347025760535522814046278728882600251516453047324978719043856869482377497962836422936682414394014868345802014181263764475837195388464381274895573278673874991778535630523753389898754638318705617858705627694969121141339156850127914661411454759608944569927872,424923243436569841495435247851914203343876343439015856681691029843881977113068565237071224513411084169099408898905470535332559128973639283979100065929486869250701366052771569921516680723642576009437800651034804215162070960937097548641001270603687011110677378225800953650776054589432072242035710655448070139786189693465488006208,15708171478208005663054994525648309604554187034877711359578813198938603887659855394524467835441996615919314055648224011705235937520588584440085461149271456423611308030781697573653005102187690948201698292122135865965462245184376015340078324844334085326339096787485464531338731260552192363790850494671821726174288342452844528711123136,580461820016061593064338020495348985933565647676414585973038183310667408985268664245428018376306335850508169019331955995318846345427563859053007276895985868225508244004665871196187660499618780148661661424202173226575634240714134306105117252073520073012251448991207929666849671865334346950240124027393774803737361656860578916836999830592,21441686933734374601435965971387523563692979987831253373214338767245600066793687657871886763406045122627801012270549509304755553700814556947556775838236828131791166905828118598583918702960813405941753586905457213950943336702964508997699910425176454682695400287726717100367831869046920925340662831453122007814643274941993966922723457109145792,791745716214456857062579564336109804352346421200404246337086014341894704865132565414815809830232839749927396518985140998319302051289432569894673668681629090876896819124978751678356908958108678059324954640875433050899954902893458892121404802161860572964388788132791543113696041912470922351770600417600350987488292160834458793083516956523888385088,29225235912103116478295397164116841830362188683033583214243148805136742892253726088016100433407785490840191162544937901478097275215846437640057339430713369219455042318833132766313499474932603457382748147323024502577292688075764914372761930853602088319289395861850051224572690434380717237737021532406085783210793972444767146551729181143972259780276416,1078399698049908507391332783536612417681784920010580455974570151239495565523223162025157236822639450676582434544095869303763962339973832048002429637627710856680242248478622147967192240885627526195572959980683529168072172030093917841379453600715632213874555490536083658436157870476574825016645061855035011594669130556011546925012354792797459819388432882752,39779073965465253202061619930743197224890524346823970443511637497487164561776303507034049591043108433864101849528049299407096015684696121240998207182883481039944516376830563000272357909704814176091763404997893337172429499832922067781800897674675310545713138724576302622075303864141539479731261950188958932387097013581379450273016677268325315799216916435282112,1466852246161398856303875075804421193788215446888042384097274661175291997361383574196339426228366189595241797494780598370647606093655767801675518106366133406257679290260334668109690576067790330427862187920054273514927171295802657832701201161970640448918654594511433492271288564286197724507577938317389412504913701750989981432066805223191925226369466178407397858368,54072735471844456480069386004336008520126005993023088332742974521992496594434193190930232148452919033310087475722019483931480584109380899418214990576668539842534950014976330402549628052103289736993182968753905709509480974996400672496391502772375628340006973501187929170831793677369711247748936980589021446797121376431888916578975397070969843869109921714242626041749696]

def coord128 : Array Nat := #[0,72064,11749464960,1417348194360448,150331572169329838464,14815490983914254307977344,1391282614234264868462551658880,126222466657639468345443099009505408,11157028040584465985583169661738129817984,966224314040872863763701472699988265771554944,82304363769090703059458840548090105989837455241600,6915481863812821481687259475620782773968978305043568768,574396434473486966894573428293704127922601507888380109906304,47240593300327057655682542855109860097537526072717856146992060544,3852186543883920612073310078437530072268811143769186097813504989761920,311781849366568344327251611746545319741661842920774937230712345495389542528,25068337530234321097249705162673107281813317671010133206156187772063695145943424,2003764955201426473931884702905585587917930694354470620482191401346089565577958742144,159323408301835961358154328642666406781894797435059603696683081917696053571035240271507840,12608081244749636785539035446996740357621005474549608244946512326523170105041074692500235458688,993454116091819204199183638806836444738440498231390881511725073045377076497323663532397186285609344,77972699157429503008945913517066543578772923220652147701734429799569097120708749361274274169834864367744,6097869891651141224858848693144330576155820152229499353369843553235936727008941375583324893982420236180607360,475314929295666743546105413149277791046795558171515135456548425125809491388275530000004337120649619967000767109248,36937223965170727107379556436051967016460122249994184363929710313582364233720203722458234943492436081166404317659464064,2862368548972761216126423152116306364630795498177395171560918598926674151187499645798521107539238514472830906959271078025344,221234818301388761911743028064049246729782630908357490064585293150274536697786795962111369404927104017719508897058610854708228480,17057949877041839255137237428940672650123156858612833874182521351000901044572672714319838692116509660004964511564550198948303017646208,1312249385672574467752971765469315692238725494284117460418770114410944271336677608560912371271873908634876277720388202626897768590692147584,100736276805914245387696496676585850125152553614204213521178242121594090562948491042792194360220776889584894839867639443515834791131637273122944,7717792387444556706393659774752389621903183598791394980218910168343210507161089729885009199287269442569681339604525130829425800636340464521151779200,590187964737617527095059427132118796137709800245339613421529494620035612140728431958421283942731682583913048183029573432546512850939140276916797221181568,45053171267669046919302603982664062358222232945331886780874887330867498293297058573364277990861290149138548836061647044513897299308804685441434483292121579904,3433536786074425269449740136745519895280363661201405578815134878261250122034724000710408738292283773948981279608843299603667882824362835544480185059748548115388544,261263811106345009559261686448415377046779208510537886549402120743999497755361391470069409831047555444588561172651488780920725528479156519558612642669096418028806107520,19850646394623337233693874214352952766798367838412802159691638346372014841272392143272251893216700959363789819854262324786137162840666417235328711789571601457912243790387328,1506127032465086548153560318180053293534164804643964011970918576245632482894113665261699556268935487166801376249101867845585736788200975925166702627226806175099552718059426161024,114122481980158651192656230473564012008929822540958970790258305847371785961418909907769080815154145359704349953840472249853202678307644606346929720912770567718959689672160311190870144,8636389487295023305207199420583053983268825294730066388740533530852426174721607449375032125248719616574398623965857611779387480965861188309157586749262144729079516180450143238850630701440,652786667082053475809283008169775648439786146454699463306457416838154138543658217540851471550463595724676264597941231663357483995747477662508368141944285811590371486640350330951732801438095488,49284811461224102132472490140262294369310536212915489268640616041606834441751826959322719582024720809681139810691289219146991565865126171298903927961329924866068792549066169035624618718999659970944,3716898354927494674705634312515398867473514473814146749567410904497069369743805692232041268198954233844395146154608104183539734310262757514500774587381053274431839047387612391914713953361473449053935744,280024126245238943185983519171561708657177108608752410198239024443894879912311966522489707906346020933852190187846822230839245689621630647263212389047573865163503740688798447358712486255194341979260772888960,21075475664233976815630010693285334790298212806694369364959950707724578612629682942177173539775710272759169685259566110641666729997120645282430449002811252188025492222528213680486958150430589046978652466562898048,1584693107906985172498753007890231650547099212858446784621940974446384348108703232384453434175364963919082918086245297439790498703192215746034715466259051724500786229792417036742255564548212970921706044766374495969664,119046406073578093137445765643544342414339662921236039343250129456998211040241390376972681295218167208268929950212398761347207849505501638288171287240517545966780355558943074363837360330577752717900628742681039328475273344,8935258819201108025089735865455272127555045821688537775924384018174700486923761228628989561201370002469910665917900633557733472968231215234718739572398052296706052430595725803081559748338052607091329392959985582152627227038080,670089944217770387834860975815378558275985870843584374471401451206040353300500593165479443446412107399189686787828391588549940128870238251506317478667553536213251620260427350745545587823800651524726213175365941290526155322618747008,50212130019208471516835111309933904990352907000535874992809620817498068444930002095362862000167867792863964084436038607615490308135000409863154173689422693795133290742084175002969169957949295348532392941103385961718230026329333077197184,3759649702090077845160917652229714885672201043479520456249758358851157171133660202812580211776963840852008097199262407346568156545749357623530463131042169545630857975279068401861008040140411850693394171426834028425602100304813537114169890944,281295083598109564730215720799351299323464194268727561645099855081581544573833978310000505130554452898016107114331440953240889852939701136790149577077057106954559343727159084825663983045379795680788294444469419900350496581007242805557227309756800,21031247093269255115810272776515703617125355442445588417944726374747722439601126796193747600989836136534993997470853358496187264351012114860653855247376560190994152659858771954811349035081065547744187684043777814605116242808354976462209714943788554368,1571330230355794696605290224686396996937663681131523086446666963239247440908155669087506872713199294837474572569301615578206820812224207053384435249620637497833080822560369504468754305008033181200028218685724716254689860762818612154259959119962115075973504,117322219455260063042902953207571240777502717768841982333863858753626662787239315195457366273844946817776294259894131858435685211629885643591357231292742992458905150233660895736450015597831751120361291438474774641834363203620026348329996848791461760187485116544,8754143662577628084844019122605269504024295953375954271150807405193803368931900138093980219938674152164038205452778446111943195315973370489197039420496347886999519458040651269996489241632831123682431624966333057045789033567098856951850035356791955464073520031093120,652795807900110851446610726837351868096977470120816093132141787152200508224930014558365897671746941513920305059863435391354272439509599879548365407782969817707751529076880079981394104426479804875923254221504097287055889540929604185680736519087338619604150743898881792128,48649740184833810721691889668904553233118434434957084222666297185429627218795725853448777332473647457391486480068891813800189221443267253528417859910171000110179525816667653936350019715726444767502137998003471890704362957690987289396446784827307003788565659812077839161098624,3623530335463628483741029215022302382275167719181884736424770580963695616719182266230454185725164057873315997860179657506907700639773898121530157054230622709856453111510451210668762268811280110000410615215853734795713520758011044767376251510145290942880597228959195231413728598144,269736536788566179512375993005384688383329137165006360007586670768207432297021850353745917804336947964957477289012647636334169062075519022796788187961066377285631480900105954909282421736560394426240291037559409929224913087849471174757610663018049778978168868286981694608108943841735040,20068367132636299329604953088527017877310883931031617817393160137271328608970413662907091269532622525766437229772847266315911446851044820231896747677985475655449532083560425312640601806088692049025921786955918240986563708133637887435031227405849467915545247972149119421037099526198976092288,1492300165324702417832015665033533117281464631987349695556467745803164848721414377358399997552559465693009655824461247601681991230228815050412901314117377909111299948376394704336361489014940332694958139936844788017222271215218295682112582463092832629373047681474901241649467931577643716873052544,110912214049722231147031388191517288916426649261496559905798643295561761774958551685559857502466192720941996947146134636306718023354269147761629692620147198572685364684042931307557109010128829251284083491767097016768930362657024958167138219884375754016468593734139294493999497557341226549205016303744,8239263941939408971538221575465383885200640514693192294241947554156803868369466123813557708128317964063199294806459099468660417295523496624590982949084856149909349432012278826273287914524424217316907222542319600803158383122375999041317660897811797935932552868568350241104772039179055601184117754636210560,611772302545365692590659880866384131261454552839489348050686805827419558200380224890919954363719452395281383680941212015571496005824591046356827350293875655439567989106988355699278525820652654938993066312739897538776820796834294644860442829360972992114137829284049002658181751999817940213658542012565922846848,45403545519671503235840988993297993956338759614227468740841039131861044271705201111187090078592210682608322461899733296550703572926559897350424695386259968140947468291134088155915299187620720769960723959044838841918412632994435928608593033665279776935001916085645571296643102945606411098027790779142874568707195264,3368171658578100933701147600922145415385429519583886059385343736070705706121836898032351513681224951428852146773300639420086517734875188925326754925673271227176826571092864614988346034314754443460425923741987934811736063949827406260202993741882071753992739528485416671455293243651297310046638064862453038956008720521344,249751916140760009375311451341299501864328279544251230691111222481427001465425464531697383846982236755997659700960936483038745017720138260293018625462321092563700840167308337410737041383537690130582609258188927391911114576304220458898845486067255187804702027229737994546785236228745004856076851559869980033075408737292087680,18511389872194819696885384075025063062320192349097472237087272736260188233639873239289476929331636526593339134661707685864454845162871186596874569549992504025131893340239755966944635717718734158800406529407651442540040092588749778290342219900525902282739280323916468118705177431432507851323567464169843488534358738011608436807808,1371481667640745319576001675696630976145298993631446930526405436312914007457324921374156971642930700143298200182913688130424861625457039515159830806597074529632790720820154155859100491853063607060446766300908643521930577684850595091856988188865268915909189327792690433725353013474798945893125938985996923008171862665749817148004966784,101570301444881502227363347710891235192850787605920812240725233460295612364471596431384553681765681546465403257433620286018536605927516149889720715277668214360033361080513425686517116300708037533229053481275458137363797321050171886860978927880826587157747283459460757275910811362328977675881017889548313418967607334713076912481254797858944,7519240919872566354800376481848356300060020671004583368706811190894855881473389169544085824825499983113745986519108480818535216063650600733339961254518794062434565103947425586242963863103257642501208448234562684089715868672510030530021865379281021652373033345790928360726489288137949464497555403247456037322568601018358109788414350174425174400,556437456378390755424720844790123934489618183330013571045003184177428099800476037179571336352049218226551690326518014558588553182604501242480434955013016738909601388137485763859441901586216745610968747800097597237272626907460726844653208747874054038259648792055128158565716300622973213918612463932340027137479759915432831990737228642991618089687168,41162164193094216634318029120534498814377929106061325905388733082144330052260435784027025325755942018006081181288063609466554167406773630383936457409893885396441168823634754872961025612469545738644238195614079777755370616137666993913481782504279743572435965827078886484595262076007584020214911001538433781854999726992379795058571877024265509279053087104,3043853505874304694657040909550650058120726318784314365311689920599659454009349169975408440224471200367251004562789386326323491099869826060016105589097818659676019351621222626680374511920290193639572496848529331283274423975244565597961587306403480690787260891663801151484164338031129486781733772397651441540981098286496492535174648245232375677236318477244544,225007526149908861782316746996349782424845966475120137280011334553206179853353489908843846907424951969051366961069265623487268459299037383327543133495534556030559927672084624575113324005334693435199681252829143662647938484085864092981127110191575391456836223347739600469325186608950826564879202471843505097642667928339801732691820533624341154013113125398440718720,16627309734727038772531403746891129402381167349101406710797057409413551858880432008902652736904868499123317137527755584393029304043585980891616226629139935430858479455020185363928114158152484955104747748833397058517960624383327589770291297811650930706087319938866920312073996684287906772874587638520475704454654984042279285309069224841264278662305318580271179127756928,1228293962174544335058426426914735654750661874850587255799071631315379575633639313830298710979270228808301186967669666533956719865076453834892743121268147642553521703845140856907006159267846104402839331493102986514154819193843536733249759059940649278695873373166162605790335930676892273791035982293591196249769104595292131423904289701363357055871065517967512902468590756224,90707174204034759286385954431879030031198673929296332488391621790516401031711612358471630752807837170284935713978817728188843226438837424712314241339314354004491722924509382071692040055150315636389906172309307688479148071562430846049596942885553537466548691326313818715652516848491608233364103147728682263399753756020830665209562508901307419220514049805454778311592897987926144,6696431287876762502092468313557832722856118697435362117310123823596712833382284065551639766062469914433762399813172792636455260022524656228625445340449509258854801345766232699342108301972296877052715387036544023826123774582849748490589533624548671535690865000069532606862958678655856143988067811435937829517465941282010347571952880002459689176982535364827869919774568200547360608640,494209393158033501821408793970201464636804018768501585775022992031763576772141375929948177477288317139555046556502797012557325683674078277907840330945184162225187556523687188499509658153624818899560311324278789576594813192267552459117238942914041217766046998462899439073746565330025604190881074653405833806797243204632623148921363151749851250826896420886587509801557085460022763633449088,36462596601602960685013794573938169971781153168593653348215778898113404105895557558001915641934542674312222574997190724840323610055612442741358252856961353719063759282826759792705269815441116423089752409514976787513240225496326810941923521070751930475542937831185544191176925977264346015531702478927388615997611482027843490688935795451418725769379571280396383868010058108491654363734724854144]

def near64 : Array Nat := #[0,3246720,239867393792,13280579404232064,653110678650744219392,30089930213561171909155200,1329951356917324077236795270912,57113562900783753856156841638978944,2401179708270772819700460737730196788992,99316141766902551736106570835559642514559360,4054905540013397349399207292981683015578324133632,163813007419726490973025216699345561342115322048445824,6559844113230982946918310653061388499219515716381984872192,260737344371488416703981672104873171785803589752652577170958720,10297585225391285516832580860770285916110346794869493592172366276352,404440118166181119647548786127247262485963301463589315494392841450296704,15807182643002015045419276057056547643971344339659959448636110310736446772992,615145919316214156728620168562190954892600243761013178933187851485201181448913280,23846605600482224059678935780036645261376506358884848203271602244526577358358591203072,921232161418528711433836867568996848623846292107289430045294055001170900093286858282675584,35477223569690484011882678656294047945999362860651871572621090413512896417260396846514604955392,1362358986033525748205873439283305151927299622811091722834486275514602542298802228106400639066823040,52179697145361283447080738513776881420148445224670749775470690395804666017699237543291869012648006657792,1993758117934979250421537572310321241158529338713302534938874628360242629664662737527449639931913724009006464,76012619076293434407972846259405590933950839293844116423068108715236547040305459316368987995170208567818886043392,2892098017572187036994386913148935541297104467191481155941580478571966976249573615145302846620200526373573858655728000,109829254701838655207585673765688190625852979944476606643842342243095410529507176726842796087803553480687545218528321824512,4163489672417974440217465375625882596705556649941379297183912244403563617576499940610419392471236050352408863816919527226793344,157573124475562990381390632344720855377120287367824081262987760123933258443321407861303075942998456393975901465494951362890560820992,5954395210328841724704990765380147343609829216749802729620146447055509648591276536881055169361474159489575805889290932108501724408908160,224680426690914691710372419213852477803374506380935106196706989921817957241269699626154708617108666926925427788117696873004722112611966527232,8466467532432005999424662451708644562916059746308156400418266580352703489001122474204062483826018704194792092597605512669817995550975869616420224,318627049433890727595400863748865682154781054456755936889265924678780662417976677427998059600366892085435364945497228542743199758948371268231600232192,11976706506487069882969656554915818479119037097099426932003230599209593751866058827172397889207803668907110367241677046156265678760665283783607655083483520,449671013492712190941051729442846658940504335974116897372952926773105200550027921681148509425706731758248405268739203365709344215942264665981230654622190429952,16864796860496357344596621324272447728984498980668780388104268804359282725488148060758143033362811840359185496072301209772168680924691998417039851937516327969951104,631858752387557860319592363014610146969402888613435068956296070889320637297286655769998673495612682878345801445743015117020935635567846757572772935042793168419587380992,23650136047461397712537168313027443544764758400839240259196756754984542698739521815219422629847204429079044260608057639724181703190545777216533717604987830222004458554014080,884387179468593429318126222250980024732412674820719204293158652506325524544381396864229410891282433577920141751051803403781330840923745555385037692961379171589039545947482236672,33041922072530473576869320841761046090577755566097540250316371321855636594395802620459172760895070171427562831976596361412550903784012478249104793777208820577111767975281740539929984,1233445025487208580209813578162819674684014822577392202394460884912052065275077818127538013975199278952852413772158469849162539725587388021234366397701432861061302221013721385001925531392,46006824976172560228630820768560038720180065743917588009887058495306151729270107200922436188607509584299455985181755719130786782885996248121953209929283897550406633119515849554439795518099840,1714699132210629546292487156248457900513972888287121248848298992214488401943964929354634862442311326237560006114114197479341766417358920733358330255052846437524816657563179183799786628748948891392,63860309129568822963787913467575721307964616365850008103582056605138452773015154763149672945484155664321503758012434648167384442720281041315173053513161696443392332323207898053331330477310052748180864,2376647826678044028328265964182998481939690573049870314183944540840612802587432769271797622916008119818805797827177785516421339930747908383964396152326383761350125771738116374667431258117029434505182107392,88389736913515459587963887446623710380127428237772433939552207592812645875115353650643883995499689381804868278309518562146533783113515900960344593099060334290795406332261520537824465367999635609910300353980800,3285138926314217238154100371470694050410895436150975883111043961941363260518475183926226877906785047256690089716475723449007160922693167645514779672615792804746799943986082416629433181985274647578530553611694778112,122020140978033460405022173972142023329398961432154144948081920080818470866829778398944026690454766781496160875799389955546981047711912832139980787040033297265685130999131681263936489134132790598639433139378502094607744,4529450656528486581646805432277430872245150308506765314534989598391395203678414871499180218967185661819384678089671924213501103574500106925237514781043649634664514727321869691824744476788185648902530318055363932005008692992,168037232565690935931229391983747109240036213041224736447416534034682013177611275262331472539104845986958075764586965499050996089066580735571209124663849321343691251157871445298317578371416232774478262695675982711757837530136960,6230468202603302109188342494212573402194234960823824430875719856998505929387269000461519987385232461620892646320174114529398119407017511108506318893998754344403584449279899840160906918088756914515349353353375103127315921049640920832,230887123690645443440848701558851427520362727117114758371520394633361721550619917986265966303902792850260351911852499900514749788964421013402173411490199236567090565249864405692070955954519731213768561843749424696073309815731214905994624,8551667934930981844494615471607912535979665348915446558757370016197148024491870385011076808471004428999576489583905347708435684657269513965792112574707853059009261011776796324842257154832128802866714070385432809928336912756044479831677032192,316578788383831135565364542512659461521715524217766205268051582185882680276629401246097900354803059485925230932490164220391316131262510124535636663152205774033328825342068400006797175660948268863797520614530643426544321421196110979682018366888320,11713860377575911596818834012222234361561961018103927951555492861083585993242176532638628699918628245711059011218391901373840546155774137994891974410920481270312616826919509273901828192498406728023354160083840714105018023355061346761711422403624183552,433224013411165935859597822620615778935588176763407085999579662650313139181842188908671820869938326664833706806814141080322625323488048320230247312277113209132335789868187218351423532761542301502848400329600251905041824426878172437563596589751028364805504,16014961435292380351591472966181884412678485396737716291294980971114169594302488989420622224727420676061786983719884546969008678769404961221263094628261589261443896446090676900391573277337607700484433252327999807971377614613016602656508256215579730195871028992,591761209603561121178342575445000533558744288363630328451032850293680450819899445119611745686596270317562335804177840232181518233741753136817080249239741060828989676303250672983187584088266565217090664528140308084790281656590456064512815919729404856376485349994880,21856485400922857421405448140796898961719305119812672469140384418480027812588828620125427864341692477757038701946901667855577771820323905341776675974650156451707932061507341167083459084503948204989387544153368090939718009702187974659151249863130640800150864815016470272,806924923633379770844950344289700512639749633427095880443784391546580926785821598135486082310059940220301417114425895659739698713467587198812185510967090763875054252217997503482720414880946310067603627692477969722087099827072787114543985872031177464823119742118140057984384,29779017522371455863738073565314737151342111499066544437978781305799116416641488964599761496222602203118548093840439305240276140256810308685890886997589738810006170071777893495950792909831667056915923317328913203287027116491627781984383553565263865781477882540150963568974747392,1098543470016726284987779622026630826671269730720704773739811553143786554894779460195461167054098450564750560514180475970994048089398898708607298568947666513611079143310681250708894074853790291088221017211266769498635149554347120265394742206897570845390593709277907393050109596256640,40509674417162710118379974122863501939579952594392035022049623523011186621658102709424935305600913303095163732275576979519472603913135796976943752703014278245705734587178818845125273584336432327293172988183348979631095462876647430058380825541770243441867103868578777685594937411503924992,1493274469219910791341610428844397144638296655102898276927712344118730186200056303445415506918584308678659088534658385092823306043225883990229587214462058701839015836222308423122192548602388143438828904853606414577398233673386524123119767753451234888932409089834318303309330858716024085755264,55025558360370481345915681176738193303224492860816816786314770954154308727175691832169302347450340830747453788964862817375477501843292543809589991695180596525940344049500141011048993039304626844414284758006217135930424851333287492093533419687056781193467704729269480243170513537745773701696411392,2026924449755344404876780517248344008248869687098845078244056015198341591833926561476966199513359448722485513064979457028870888867861468758827488542452260836800149567615010128179030270777186059328012612094499361107305241348254229595394284709979488151374098691847045060272046350905179819531661471113600,74638537236005726963114927052587610336617486686656149745771127763498816596944809226650596974182457438141847584190924462270935289387430961992434318259797968894925101813612124484897306490743317685999991221541821494511686283747984285928000347044700365403823077247074303624780743382728582889297558408066131712,2747546990763154946982696777669991663217734447652734807708399576752942120879454801158743020038392354280995676311337133413863793699228413851998350074838054147620105543916949866863542946381190945597599793128047979970098974657647917623141654057197453807620732649002611313211887297824207787037809692879337570422144,101108442751809382098303762860456928896723653245604406412765720903636897551118001073199930281807619277842877377391006145901718770896529503264918350675821331937956749282776237087305670527368352404564232037496611293183734673460325477939542562073655303243717380887416844489603139424592855325512047666701237774468404992,3719578041107882572060794340184644212095414440022688779839349665343564892359211623892006559534111343292359476730635089755410861831930946054552556504943077427330224411528173406942073269827390983735181437522962107187806381263125454461048331935384428396403022811289499132981701935412572763192515641226461797941224758245760,136794117070245553475258009121284852111296653682975183585241993742246414907386988138595247689991980536881247660646996349250112666775206472143782272784150651285675638039721088331735940737379959384620682156318365543807018237601929831667487477639584040717728773052272025528494434239979532249911069926635069111352558704595314432,5029352206767745410183420297612640848400123036611651364592117046786130537048282460597124100190730088673342771797810089579626321928580869519705140321730918656026450825168724452174675210326795937311394837068040831591653495434610424345488681471589974060023441834702565355703375785358620874070889528139912915217063663686074205169024,184854839849570968812296394289108815831117109898647965774114372592588067224199922221724995735793453749687717178082069278567563291697361676120588099144777736714952625862739004465039702770556042564928767948470121284965640129133270858002932826359089792908837579317905168326289482782706865327518165977757614138212356134956845302663272192,6792456772397193756244248738286991593716482193426519679076871938687858853855044493259424343124137343461038453457493841229619870212027415004253237396826453448310129918509754824257890254107745348926692080680994019615846122111510034427018365289651178793379118866942546498128748165579068609911877824773034543765846077640706375911151181173120,249518781958667997968283224375625821109848251846346199588870460415143908635485543526458134504163195598322382123567785827401155321039590682436326831785397368677362116882888990793173254249524795148824906660823538289775163374310677848317920982129522734196043663303107989741705435855298869228447641512697726295666394821203225429262780351995537152,9163530040203018553117250741071416193500557486870435642305434311814289864434664959843586375678591735857843719125163892179320164593489960763856586105131192869952948917257622644183873640048825875137018434209687435878274123830797148144786443171640206489190120358230812717542930952250960261960037488302925221489881117296491379306862222856202282859904,336440587029804298299444762570006647088135438428925398835153158388829953534565330232758524478357146311085831906390271399797334362926784977431933674138528058888423652356750620782728766873935268147269633171186267247110882428248246549127961105696279600988644050329401368752079097784945613489574103874182029970721854821072964596022012939983533429265716992,12349309164311241494132114190474899129767520911343646472498160470204175741091074642261405406892524010943824241238652569714276171910854882279110720880982101384263561414830860070833761479773734019787248365431113199538457199250045505502486148227697280860075438044268080748608138175123086316179335165223812646851626853828842384607026621200954309729214476855680,453177411495575606463931198550749985003453714404254829427001051772215884352827499464878296667411613304050805255373648073967499761610487209726169508469090232601634675889169841863729101401360475355246032173821467960232301149206148702585908005056479393344966956610747413855195033395698205529361685471301177556412315397406955106500545720421836209496765961001903872,16625995809097237365149901051449958466680455485140324478070235366805005873929335521526747042209424274933535208699198904371750395926298598490021177135518288981893912468150066035218608039258435943644098356770937233289197620037078490885143781042971404911971911724882780601133504687778330504936089524306568395414982354907836827859816181801189074694683031761053444838784,609822331408137936025420281652004510906850330583687478487880844811033571783588777830634058161254256917392234195959687271596831784532167943907051439304443744867030383777378941290892024695590849668612650084313130773626484454083145082441988395627162611838702234980527808227194914069879669086760701320486908315143183072513504095177524125820241193045954679939378887240603392]

def near128 : Array Nat := #[0,6493440,947678047744,103709967732271872,10086546734720420498944,919502599787463188853338880,80455188187194820648625545629184,6842932203919125920628825535729650432,570031924337433840247421991448968664559104,46735002957176032283953419859950611942816981760,3783709784182451920439543218766358780686829048385024,303220014889673013020004703899888609730951267841229748992,24094884915355680574810115862698979132831025057385838393470464,1901070216231715569043118741304167492164759199611047791806389277440,149083106849805515642067536000885171646760980775267197647902008588619264,11629826200178899640114625275295071033969243855741179723063935701045761911552,903069149174182554835988397120603198712041593053638742809083312923172584861249024,69840599626329460489125628815419624132147186594805203249170854658809289830302386225920,5381829421909266956795156352288929103844596640773403873521396555239957364101421570451131904,413381604236871318435963586429575776173546318737442371368765059455515322315784200585356684090112,31659985996340076740673333940734833505331014989969168973731281354469533671862357709891503220733750784,2418396609002017497667675647767941783980196125657958611189785817534633757809356253264600162149949243667200,184290938526751576275352187737075370242913566578178664270003184684170905506458204424964335930317816865348242944,14012930305795873959929534045595037164860469930896991549053109028947753285847242992071627813997539488964618305276672,1063359463735314421326237967806731123248355087070812836410045770944984040504903099427759130773319024152390237403763551744,80542596156263504040583757143072360596748283829429478956485091426198298459331771405297191357721644788733806471842014463681280,6090119643878488150348228793444925137462100736887789661919443223396012134223793884391731569369528799683414806136881214002730192384,459763248774526965801571169538598200167307474109012319343429926346786872144345864502016370752235310981083481413132493006241960039103232,34657616924500446181313361094579745526179198521843356409990765428450201738862248121082698518978875638628127027893646755751497022609359547904,2608927365535807786450461134813316939194674382289863011811539029964495562071300256957085280154330351433796694535620715373238154876868116355388160,196138418788978337920897089290032715926502718292886905074495630866427120508476614176432730278546880158875121529132258330958168680081539243977479540224,14727721325237538879500010294413002138662126405767046588061337205404809772907182826537507046303047967028313162363960930030887895373641691171758304077441792,1104618244360148985580244453722390195863997524901942354714390793961418977868436733763295470340984079099300985711792177046859077833129083606769525480594228555264,82760162224763733359253107955707501968212123020274505982027318536034343740102078172453657895985853450962832986829130997615277438950254519488905299907623258863747840,6194255352687230728631174761010296014897195110438641157777669516051364559043372998235120470283143017013181647995476189695177007276840357659765026548029811963370429566464,463168996274584278756184852625393423284941261647269848649274578151313398116856821370251157613030787383243419976293585299147812997857175667587972503167063234066889979624004352,34601460979142961169829475990534264654833770000916888570132636839470368476330915663472080816189719949497908629579504087205939654492681284662495505637999944664547590921302448909824,2582701311307420060315858965098665479722321336641039347531407557876387785560137831363637575596601468079592777762255341425427320705504481586357998897139839932433839564914976497886360320,192618215371390509863260634154553854067003704202758679278799993176156324693635163826571376623703705339924182699635185454730386649822994986443224896876478654807439173021418291274813106671104,14354271982624466193749728375687495873156289355227322293159267521459746771213430962314265223393946554511790207074621499124528670847200873141676040720169115144518849620705058290893790018407942912,1068911078119745347051955165019376055028774320903305399997300229884052482961728994565653953160232809091100173753319318164174785705434376044319217364110058121852204772447999002771618184859595736067584,79541426341266842500513086944275088406857305751932478861582112592474113908138896198859319243809030289036956954955997383101118285891170324708465324647515047497172747223164349940277279818081384899878265600,5914939674071615040269207436003429026751770513017607094288325621715171726900230006871707854610739035553679549023802150191257855923434234688328382888613983144374200455636232485168502984644051143384202296774144,439567151941715829655979677702263740857589063731332077936319431954684802964752210824218401240918277767836343854158011341763605167118076582358303858008448004361891258489491930322020395839145771103178210960597449472,32646006988820560823752324053158169728349498070927928181485546291414954983832847053813540274613530156418543397887205508796578941919040191712865239366529003878414404669842902923632071767441215196439812571043200860204544,2423126098489954156208253186327771531955212506972619183535428150350451958946175872303758118095169128467190442428546281753668013347942068931045081849984421476951833829395373681968822099003712148277422822739668108939944743680,179751919492554091748468748100190878551199881593665683213777013500077795969778194177199189143563921547174175273860337701986835190059245371090483032848522028402442028440296299169161414303335343916945161080249758859885909235715584,13327001587000731503791378995016151889176397912100148707464331332089669069273509709743381246221482667090921819088085209650812526381995018794847680356004928273218963721936631278369192720402365441576373403243099497255478874430633356032,987556543712994349036245948610895834100054737724002753071340642471791512581115140717913160383936900041335935719949295458650084506001451415159258746272866730014358073897605790798241378782691961410809713767638116539415922758149214375816704,73142663269144916224972045554265209251405137090639851594299532312895556409130573787252081915693032014164781609675641276691836279841400957278564762860078233319251443568675559447815144354203121276232732919032546989428255238020905188821022114560,5414607846043427814537611636363465081077878306826262900117599175456405202728790668484536571052980428658330157114035902324172358577215578131520158103646781357248164337122417502298572562999915271683368428234284636581828071035724078363618191423655424,400643759595221867257903740856027245504754343108958402674773669608173817826471995744908835111050580242067714362991356386763666368250045727256956889244965911663919273861005303944721849845611176161196233379037884840404250755019865460995961880748902734592,29631399129033139996824465450301197221069787091877830523513448178972636900906342951596884118814125054866364567504842726604427541040654463019690226582801556694427869265194748578118815541101462848800884717922390905900963835176458493235275546495267708023320064,2190560250537596901773897412436526829742974756064609814825703424848900251934514904291877292781914548114159971110639509238419842168864602822699356645046928438871758866074778045545102006475175189257570926006228941685038269447126106705372722556657739291858146538240,161872850216403704680297522045098767106873016485626725083649536521869979401876824367565829755523375012830443336243007447644754338612915250075268231342999309496131256332650736673413323904646465724408454735370114761031419380596454146959315397281946531881799322263473664,11956793989703193033274681990050612880427551609990548642747100645491138449298265207733860888062656848978328203781598753999756591666774456095279138636339484741235503571069153960912028698629260189528408499891152905599927365703997016604076744952665005590971012573227572497152,882842513243562720074040195744006607137515303598464680970969214425472767494679891483936409940451693517941500098096900180202568394142122886364457977598365562078244749658818190497842244298916047682941981029095208255886330526264379976554422778760325454023550578428326357362650624,65160593292244274889780422593084171402121530571832923482658937000307739696629463551575960911558165660119776764011085172284340779693528335448441477749962550699104736100593282306555937539173359531792768077155134000665192203178001626014614105474427092208873624702237820359542210814720,4807567447004309011810973250061798364451847819071093922097371665436854847268120151588970549025320451187759905154050955011022961349661560493713763603989126710196757997796914466151411830049152857356879362899546459876200836837771013982193071636867191222909505739332404473965909244923170304,354575981008111075143346898991557045796351417277493491728352179788211432511651017034260560595611573270533779697938639557625904334483708412869710151009426402660259049152116198050187148436248504758451907143080875503308238856397156379218322739793525271979107482628230553267866991038557302995712,26142166616883996536133922909362343834213325224007215358983676200702637726250735019955229712986718662782450369411078281629797991558705744116978743521624389773488431111797704733645771794581418010390612641788983898336719633749338905864351368994724365146794333896218624820702815269683771091398864384,1926756011335540054521535188418940872406567290311799703528149806408992947456667923051008551886057510999083659060419015621596181544852875423883674867742593317411678073263610941137783612341164365107607658970173790921887723515992759467247897373166585889235763140553530318279703431659637509909656009184000,141961008723486544534082595491652058086468613404046858502753420010963622414268155368162224005295908768460651843450967132729073185183314986765331722488068808188540689002411179437128798209348309083516172188085795155813606015130960370410471906665784730348099829041147997702609870507246682821390490472022265344,10456173313996352237570190579382273144329047268061334376289964201139919732458941779835819248554367811550880220535279478016675976176774340675155652696989888339825589935233868983343722234309996766269092457789167368442537326271317685080919611629410694736791108345981711726243402896892597485040570031632025961622272,769913189595762190713066588385730499113876144410069379809960715959149907643793071725104523813916423935322762617439303398677785146894422494359330060182575143029356971679656369275241892260129790055556507264505919164897739906256221251553462579689722683959564147235477478834417269590476030523588787056573597652159737344,56673470644529136047980567784607111986785946637576036985901618828997911613556109877036682745337094141781051998528123357671686280665841971032121093729458108916054996086442040542882148741820654367768538836958172171564903469318129649283412545042383162689229362516436707529500311469241140825896542788521807801920341770126080,4170523103095007744608306026726931187749249691799362386163514845292143162103905674898848087420887743747804198756184256501858624179947371164067044920545874880589425748689565917314273736695088829700493720568586814939241902838623514889359459397958262840491178568609128517791714077128109274121774838461570289235109266131942198784,306815559885518644467492087409073461753103115974127705125295512252615055295110249914112063748904680787441769292263388429890337970436668321577971395473074013894418598026902571933009885141379737553314952883039763059696792408510038554440145095245777722661687221943724218757907481328518563247383570306727631980186117276546620856408832,22565432765834249106422980974116816685440815314864305953338176773306415953239351368784982153822025197625895056881012037224841928468827362536498333439477432816086644202356545607217441078447773501220543344511195004092292414803204290742271018703214618494199704209086796787928761641161344772512794397702777932833559329847258874380385365504,1659176403140065799963477067709591593935454756677351371655232648698288981282660328639608609639159492914235134212114276648591821096071227010995295870675204489838954522915172063449857955818521620017419448179128636446293336097312954764159447304619407982224263813038528095869425592654781528787289480758984469152574067689456807644755793777160960,121962722542511048860363737056021069917304952144610965139006491446449425647367794405055661275902919467871964979052196274329115556242450455648819030364297395560643202299184631186083319314200299746891433799987512149248734703872332151828350287661943546600495602355318324921824610890221866759583665729795460620185172661698359268892333897145760730624,8962934678638683069079204902476541824292221510868947698457793255564274592485498274808960426942984771116551210246309224997655954054513828723309014916151593663881586618733566018788358828219758189454868333771735975026627007576959455271574408526118581623485835162031620398408372049369803903871271058795917052827173121976235729374841944027771952409627392,658513571864011292500804450529483166852252020819851393460373004999552451675941391876451963590572607554936236282787719089049679436600128937453719156818239210410504435962813026120238690115605887863664679266833303341326695996635864001179740287201777537500711384054007231578520708756151174270049602483916904933740333299587391916326561096754295679826689764864,48369689815625346895045238396862224484605506542071105290383644535193708217356671069681286261551049927434109203008638000076333066334368088920465511045982823874688707813690536285467207189040252604011967071570564553478337140015578271648127187993794694648379732719869660257417378624710203444695239043817306333203250648832852280879189291455344699865847752077648640,3552045659701000185247522045573953358771260573302907244092854938285579483418426225578258198697059858255214645168852921638057382421103841688616102249544529553647675595997766092801355065597443177718549337277524955443477668769332698016575700121459961985793615012036173093845440289041626490800279454089458927952828015481083825957962286099612509245109706805146010340864,260785197001534093815329704824528354936025076515443671818554357886125078092172186674135958822078584826166746654432800540135872585532942276037501958925499366488909212764625238729481754876799720427351018345127574640774453737157022516243738585122757505271820863829432496701065092642901095259317824501155806320690459910227347877522063102345798102589731619168441199591389952,19142069587364305335016920274272649488061200093109592405142698512622576651874594113147739082075652739362122860302266554412437009546150319068726718054726080805420242396675898398584680094751448006145071542792327314330931147273565517642938869188902426775211086752030962525960619402843875876846037793302014233636847737739072033865166275525797880225943163741161292029846754471424,1404748949582967765108204848335857476360827186678821714908262569365793314420660929951731763667280461248251465942464727648956590630732394581705322912185455744021499312886472927704846706257075935837309239016364678111478995088365559149409749326769437180705554659413448693179438879929344612874963533674537172974599753901666049523707150282591752976882021918864176843437171683679589120,103065814403266597547988287379235620479634153660345698643871038236119699084593744465970727312231066607553978263369040680160130948577969808895475022747554492546612229907485657648265559494998524602386469716694958334395983787936568387349590278211927739547460083794353891808754859755734080162117044823279223494128235022537476366533822082521955420237229709854255291675232871861559660629504,7560296153153349027726597059334571525836170731385256824916662384450875883206279672284481147514151394753435374704724074718885604547071315595054813786317031695177340990075923383534484760165658945734359622494433249337968526388501448015522792779257196148712547444246999176907120146668546540106379785384935339734166361277571384500322625914117040229272400973956962737546719646449749915833248512,554463923491146742120494879461519180615372049179847331271934569385296826517382353682966858293563016911191806701401450820147633227740108751510773801118408179131347415998504851189450178829225181798279805094773572443166584327378967438684052481980674070219873191502098461953248669059325861658714278114113497795387254216999240602298685266661262142810114932299951791604169815410630802867194314141184]

def pairData : Array Nat := #[0,2596610048,28234557099737751552,188416085955744985137335902208,1005914054628018559576197350930101641216,4708939361585162300547612102244088708734870888448,20189085958980579066597092663565410530822343544346495229952,81235516123475322988107263366563911382123113273709324226940192432128,311465600582630545277528090408968046017733992943713741182090648463239354064896,1149534832238464171628219927861675626143342290820628382699829373068701056771204914618368,4113326089078980930410800449654645976447905279339003028859882226840923476435101039548842992279552,14345201644807194353081455187682653350311974831664880441263949344631064393995177268581672512320157358235648,48954560884189451523140301012400017998077853615892860885394568665521144635520677999794273706118880452757194196197376,163982801140863019394130305382297803428451436601308909277968275309194181234669936904809456920629136515360115675077432353497088,540494231798568593112652468004009592746405787739459498528368942811765361796612758743260962389666754845434473254347852836148445353418752,1756450868931537541919284773352977978339892926556641360320569223407024825490225005361136051335485044728217217544878370263232478670329184748576768,5636936236181318638169905470532933080496449225288288301191151579974190166240084695757214912911094541593709246192240371636579076815893322494186949263302656,17889706073501329198211223077196929814512383163629040659062179083230001454358111230041835412487929097226933727658624334691371011034026649713482618945036790854852608,56209994029409033432398246559166660411253746825075769447954767448272298026490873808150271152206685562344268726838106419576563808913533811007714599643818977510593543365271552,175023734167865867987061685834764363939593408079196374726939596591219483497315158605054693078119254218917135473270747786296367201395747804251389120650865785641225164400044701321535488,540525470369374585978039390792291027925618235053590021704241878616064115290486663714068965677027823008919984665587028148473446370288699198789193817600457005882732548950397229001282435712884736,1656856452631649233407195602137250734517341266286613826490658116655719948047658527683769925682058743334741990227867228240779297183229939836849170090690606765807730139204774628961430259254451391304572928,5044014562109989872777267660472884612737886069010602728223007911980489848072246993557269767516381036658513942027409456587098134329883014731277747124086561263657704697452047119386542226270350638080210798758141952,15259139251030446152835377422497713439040637709974801038348806887222816455573551726079618820797355888285218917021514952661709131540403088459614746182765003735327025701400560290782179204842797575783738716268712056596471808,45894138542466791291487035117772306566774300290086250215224826196817529020178318072980480582739385211333104292935133242526746495844717897893791116518492264200801860300566123978124369930641001558895626031023907647153654867467247616,137291976714510016633675601683752493711855064545128611241668209630566892391606519873403942789225615197838285480472092490325910482383546435727018462409303444525138975001838763537826847275283517613218835518904896641473193282179685597839106048,408658643858412041386290383166647246940379505845754799778891148810744220824083966984580300063229030445995951945636157508133378209578750413828452213357166030585701024841462766981093455470467413528297816381664218190788981980089167246230684390902013952,1210746273275046619456773656236423589909414815688648150955298097434414012105713052373995728762175419598513720956956262145390900602859749347625449653305214015790803859018863320645924792488249705080132399037362493390732986736447787611947531485907065279537225728,3571549824240899287027524804797867054508065023918831151241722170694935383065987476423048530837214398337026076828603894472885914489049105992232799241621144713148489694750158129572457226989574907848250865092492046454616936011079432466564432769115306871066448656170295296,10492826230218218679397083858340639970771831178897074831169272461158405558904263484847604653410373501420786354037480752289398172962585320936177644459676093441109133271540956462150966780234388399685632897149301183707261903006693709985716505089420720962860798895281623911544659968,30709310722121679087588764904685185979540478650108282158843439336614589343408080191731508725551169388997117094280098876324116235194174308446351683206896878605906604445032597513637417713669504544306388408489609623419807361282544547032273136413444347258094374225962381556688550918054551552,89554840889630624777490052679391203681305364323106043680281742393221986624776689548293855139831116396886254857406861052252303400352498877702543150557862071928824833825811131456733495820810144023792973508026146800430818014491906606208729991605603730889188885575958760278160189158460164767691317248,260279658957578781078481855128281807518991470802968340851015862872378381796817871941451779320333174165071974957044807129399102651947413732785647262927038190765803628022144954386100990923899313795123895876694860647057177328797270262320729582788711943975885961086929198876522278817537313102826110402112331776,754061036511392842487675685369351020202378187011472040972783613475914118399175342663104759462201190928525223067109765552299835115139579579795252213754418370424881240433881343535998740038503254578491276586554750789417589494865978645201327107620799540775133454727882709894935644948346467915880975859575223254924402688,2178030194423265547347571917226543267676776995341966280267665018412446317741492767687345417221025665439993739562962113909013614040733513587515598594071180202709535593526122173364290671132866758809666575783188471908006923708064112128780337859069407897105875798741500232312727430318311050586719287474104106350908974604785098752,6273100676465989214040520046944388765395075414130810055104337541494628665170365357411582476326429279449097827047047456642066881841755320521356909920229252374679193569932921425304030942165652105608451458715571113556191961124214796707871160928027049662424515177580693456932484079019412861386591216648262808925759989774928184574025146368,18018801923420861737693644012200608818524494162138531792012417827753521589476588212027522138673042322141406322008610359188367832936560463384395702290750209120492379975656332594247389963674584653425732192696283142116457811899061423660284228003302910240551000618288808773989040380156232074349045488808703043750667770802683342448186816052962861056,51624307442805887507631199495254471307988941874942693408964818374522084948378640196270613823040718499495113151305269233925592875810236361842285071434455174631167524219001503665036139754324012447916267000483899368449672853189554520162439135809525901286382738694867378550321303180225304786885398539726324484207335420394383212900264487575870184260013662208,147544210941104723223107474543510266030545144359101656085316115819417045591799017274304166627731493473707973412459169460217809028595731248976383384362811745731145563699433024036759278727543463549275372537549543586706284503542062773424946691678299144315821103053860421544696246914904286492819273348406631670400896074278035096885947157100898631481490829961814679552,420707876497254029918077944565711025864621151846975002140525789412481624093724887048809630834001530069017108812310603538836243031857084382009807290798499285286733210482636586387025771136540517945604180251955940962546175745924785544522664079537160064183306031932984968772773146450645500704746861139004237429734974783970812952655521422348260278740514053992782157726655193088,1196952576271170991747248324485399657296770801472746825008231829512433420350686382144090777047036144450546274913217782129286244531689241613369332215055165180027543006357695909069680308264593708148127284031771035149136191342912776125020806814611435853679569131697231617563710634546083709515571052083933359760896434758970534129129050042073560010636654021617993569841383568784551387136,3398248145945112551155992367661605967540275889998163148856670103849434823019632639506571987443765578747879665484514898474854102604317611041670823512700696090135981119208581388562867865422798147917051972056110500478565782595966435415608317916816974300210034064071053104508755005886197173965925292781118570971864207344379560002570776066499309640102936282231681548256775543763263367756623126528,9628443850083201787866485535655450460525429824833765058065446503715164703058757243365239560176524838994405399155466655138796687164106692879247868607293292253084541304278667700017117651847804574355633157973311757423548948115589666064299206029037598791220731211577315936784845803271721184476901113224886724760203816873409662719130435442494453145266896712647286228027904767339602952679498795665311997952,27228159633618866977326084994092598957069543372450902057925264762816027107815201598969778660753645315967496770645586702082494542036911640410283882633106954563970779524519830831493137652892897818914663516429481685299660933419439204110328807003706741334295616771439255021209469273750449094486296256339536252239807155697864750667205276310877012874619664464052377824744676956366425178325475411443178008605475217408,76855945003439276410962954141172126282990959339994986071098598221921205891467420755632976065243376520768822946447219195452290436874333430068185774593883988758797389099020915973013242683711009861433021151348662856882513617013562807730455322912286202426626096163361298563352698530510489617663529715490757477552709570300399985875301911918304348481338543851833420564145240496340041878842039634421661712583557415421936214016,216554486919604124763612083049579214015565467900553815643325014493361629494649436050666571429980966946759134036488638033055391011941801806235287268648520960843972803422805460289935458835513049307348692886361329112532300411858493029876409979884303555657135218063020899926984684266407059129459843385703031146417002850520926083172272330747924919738763316109241257343271094197289871291467042030750783534179313068491566618970790043648,609142515656246039359125937641561763785578503255028726346860906018707927514836136234354266886804896362962433278305194529249423455593641486493596307009797382374570608789525286286233573486885562082315438238538455751652227583263611594189039010611364251369070030424024496913331089879761265050587757459890192437173133094905118115260061515709212941427839069699510174573889006183890285225216813932474429056274018370106588321487700271403485437952,1710654080842889043443503193134203613592311316924028414449154206336448960497958611539705097901858559889387346631168408557324370251664170336827870943589522768049019666851203358383737425093513256325926654380626507209699283047868923151400282079770489254912692619880151492642075474814453217120482275829162154109836694806644290530797448218239550521754797745581245357382316172031795503449614530288982725147800476361207417076480660135156995816580479459328,4796504270205253379222187071465548001008018987762966161929379474434622004713840994786379073431902380685402098066390341489337514478664523475800203988783340289040444739376977235308525380410251920994406201374290026323377955637958642574978374544054058318933030544718061565606868152918999703231037794084680231821726549795720098739896886081387235933289102895467651120226954122790950844362763386898797829398916059749406193347793014283741245904588781454691001245696,13428669863463611384778280041624313770458010266225707243188525356647686078289264199712044503869280285848031178894341719242196900238257518635303340549511569266161806231547773292204638985652532664183975606510013184686642018078641866426292667995504832246062412133793100471429068620831700394000115494618265233106861623242343775106507258176166877725278702806606900299636332253492817906765018117190519727996942614841568484240512610469028624851144886377895204726929117421568,37541477144308924986041413068741263590234660507448552512254098839848185551837628333548187659173577862320084557846439710186128144368004197680237009704552651534552920367494196118060491210426168747645487980978204967086769180080920520807185751893992647531570142674665298860451361712515867894937866521779905785931396947632876391421013208438418649084527954479620610650794274366841257461615930736291320476164660890686279640816142437829779250239977558617243878392471099886699111063552,104805290089656085093348624374445067083759804190313731724777194417538786037122713755779364991989939027522413743016427033058212818299461779392622676996890520985905754965005202459687096712654837432085899207978569229103309532630677311781181003068644506775147072077474572023377067651741580721581959723860334522118450394027451689499460863127092429550768546773595268330114098008167909395899681228605783463527807831517219271202363894958528423938142429690173512375705837368920955098649381838848,292193497831617977918844698427504192145570777391583418249603983367142138321040155979268260785386105269683392767074326660542331499278801884459477312875132247858715686891628780611887270471761897629521914428003347523178277125061335030723616208505801330314989537047747905546605471262035559369920593526594945713078051375772621092983375998027066997396643849457325289082879531749287933541589774153417080141233179626338053033879479634505128043052743791085553096968089702890031178476056050930750820786176,813568647976962693710885745163992090678486622439566172643781452936735809456146434397965551703115037401014252079562605259619482042266294621178112136081430952390908982650904104070437826818435311669756324079775272465319487239772998285415657742380591209734249535196584288927866225358178243955181071237076304832840842289118655915248989323896850926709860768334808623547680416942838338767520517534534088532196245826727458895536134055827845082733392896525784047904116797505121800836275835736926404912702281228288,2262423422530048036875510926242484223088390754229936688443196948237931500972756614852105573009296916505077619790394198398040878473685651603641747711591877980945288588813627027518218188675112093426267672963374118700012157503870977011341805868864557246699090437349123617115514477046720118631167041867884284744938792252467417975892289978951858200395232916468530927892121126060527500432192741642815216843701447961589180374013904692097506390706636389942549768284649408817754915302210170480265373003043602771817436618752,6283885840218499076266574629793592220428170711163630436182649328340994816014982099039401160187132881241927301294365326590937804333032810845502251500197696399035548592191961664033730949792901849194167398617658897502307235322015847413122856020021811222000387553784698085894435840564159765292411795171673180566074979581182461569055965308758766080542827696323238997910840750171381643269325128754020577026537465711182404188493499305282484070937984429799670969467928580462194649962143003161677670950953231949677929126856931155968,17433120360058038660775725002225208536380855614048447837909684890448481336532701194344291730819857680509629486850481421795144109001320710991839462376738192289662662279889062506951855972068780200430482281488510920498159141368416811902400215198524804244283181292974227534050489295167911814026652269141251579867369561856869824841200099023945924117138148002197141408293347672420197293370985539251639518545574821257669426315108726463646656380204885880751152847610074300301369636916098389209662626670959429948996296094393793035185032339456,48309356426490761607101033853254180707639514428196198862777338210908061199814176594710666600835100702110755310956101483344457464418081564982912219462147184005689032229190392527349957414178171489387589984367930651691251035315103728100474703263521537361465639938247002377846953955201205651769354840644555844923856959809436347071923802157066743546556892043226840382396117366738195226575682772744100601714890600321736023857803823666639627175258039741772051947942060818948702666174127887576485306375960205417938164210263087326241184964690585591808,133725016788204730720520633536479241441466667916039327887570440297852853093219005009103610374998577126973922594866550822917191257009593184144121165282300705466717301385824729667967826640530581411177559119409801901493951214385125317951984054626009466553008169540715689489982850104868227422944364409152379169845490121131769074874055207630095437068704414699754806861010470088484414306640074528387799297272688092326944140781493640871669431795831836701526001874658740454485296997408523851414911926305503518981437343175347925759243396266723636382769701527552,369772476707628475994672057704502992079147475350946391289840966879895167991743196175018036185664088862712264101563606079467970248378468438581477576541437929298467050048272859408621385901882633227844537607370595835377356745516164026377014011785201605727369559583068894148328673420133039839188727319414730421837526576711471647999729864837642376520119019452853207829751529831384325025966949214882486300474659627230526589443041818167024937993340181615308406771987797700941261189729702382064899890073101254471717881707561667006008730013244307459508803120995122290688,1021436828265325126792259537500106023928325190990345486550284695167069693716699178086928153359963079988501960228233155919766172819231263990034759511741076553022026703691575175962603890569493700756983343266587962001306174038323147881730998448226166359152934946648863482920865365593077755988815696287287449145654940375392034215894992115064217627051308629597337967425985883196221466165710166962807697144088110274121237823319602101672850406024512954554992855317908931749933856741697024140168381719078937687542008288015646398455528565901768251137276509390371636129206457409536,2818754591319151190050335658786911857038899930765203845704900977863956417006135455605236422303866572259973759702758484153536424043870684584919205229553426803092260103405726283230012339900724406818796651258271845710324122930370815161864549513872258973603621909651557133418750192389934108529891980537555756148780807285389313683100279516050582731192074203642872943235828469950203426387917148245032873151203505377279068755171046512381821934146496360508173158706267291907599812792301643978919516187320018532310325439191345584273145148927114383509702161375294092655152038080236046000128,7771145120797372241804568398825690885515910176621803610638601965019710115473205502564192219424409165711225897862463484416027223988531868402602196313466883955769154210845435259319687429252001461160943100290577125897158558543779214900304199896227407267562289191464337247007056548749479722661073035106305682017126269107050058512642754013494876054744358510127747363763406055797205433629614970237159112757272205158935778697077236699280046754953145261074248250599701687163127119307777246679038766345655316361626991983445222571626033225473717271067266979773732415251026268665833900122483312893952,21404611199741592655341779547432935026519800064455155052237742109113038763165558388460390465129576737942120418346922626689161781496305797433936182228699047093784907395967671411465394482948717499760470252357542250341799921100243285193779410363956988031375854210507602541590337185138484048903577827604283637473388470322138876345557170447087338407654100737100913267570936904560072699755475757719698115579798934087981464810704193246911118440970734797171799354428167757176234108172593705147245630763572527673089929606553566114214337588344172611733350784400821901064173131514678051211674332894632303403008,58902841843225916296779370530475527956369981669536346428340684509416905637827227495597224486487266643928055139310472300265749376422708339837801201352890899915152962736194226927210076539050374014015936718748291957008812308303455551855682021821458485312244273256610953081456503866154757965523997829177380791624190861568570766901424655633964280333587877759215405443589244107743916452231184285028878679443554220694303705662492365065029000683896191299999925328244282329256137450441461916840427051675540216521559878612355944704367104680582124610455026491121184833581863029409597842607869338620372760928933210300416,161950842217867486163644957120337367076462578972313279594397057411315309054437626650009067780438348949438804698642652156257579699949453637821291575528621646699598699925936670526988579286178675347740682259939008702188235029606454475462948268692493775684627825282927385307960176244549040055821319175241442124663344193115486313176387647145510648541876989554076982492150146163591839198150446980501912128345401023083652867605389222504926552321370196409481141511169593000000459741840017819388838900002167072219558865124779220848588187390514188153703657767075336783733442339003715635436723703029760338444686127505319080501248,444896724211856395337755395638948431597275277505499307669626745565008985066495225823602406396040224759073133981818386121485740183704358658046094145004960100431883954307391502890043762075351518105802887859594007823858773974806546666971173279704734429820638060100246587477135035843706722099259707624511203488106473025360919151673970402462662676028430504244342539671033920378163972964882959575641440258154077286494754964456241457497205314103249255951418654636216203144715476667595426820763219463865701963144487519887807169761089837121600181275947839958863907001052737017903981813664473701602484026580971438608366257964190517501952,1221166116125842739930743795121234458276662614663191720706850869986151958435651263122261243226024043370519425190255686195997953093902192922561625542645168007217115417952280580534049058160633859850711843118060431976083010992415179275330648162154968389483796401590747024702347416057363999126898754968642609923250488495328163030901915391517961834515116312396082087827781948738362615406217579683101712281369163251371461059233123554791779645272725799839809935448246752641276014240811975980634458034754902599293889447726376864428091959806193254396458197611799835742721539270467938778261983391908822889685805176170438567755372847171059979132928,3349190754389315652229022073908658664965141487752561485308596903944213992449184468690463941547763733887224263273532145562271398196116778949717907527998577641093906135622021944840485304913982058742074650581009537333392048441805205388848628095629780188672927583317396290252989080895028163208895844700163208894471585268546454930122814973081736361248227029916031654023889208298731417786121281882385156114274408980440134051795512607302961936281168014979398015121280400034764572381955161883645261986918689326273807484656589464742005705338283456038952068417690951704452342763918843839685674208895733091005310204941047243635869315733871321368306534916096,9178342584581741766657741249798237889908837000586425883488915353882878170818439959977004451228629686894553850441754238012257056216960736097490959145179227476709752832235216961733589516148633914690147978537790430224468210873713124440114784296687367052045709285667370135726001396455301624154037849639072581644960843801566589359301407087681128988633205702945394286854300134715096446228922871810132228758286725274630716700856183175760057432949071360024734629475190478552974248777179690586037956530583752248528117102267494292148959838068620878278900548459849244236965104652661491560020244022464524986959754837634864051647958462056902889875367432315643488903168,25133740699266953373334145364844234702696442863802866878666930708549211032469609236344013252434294654204622357155639401672816490722079076859351590899526920147161021151394455289700302577310067896847677700358460388478729042240046428396371911935156960993451768394135162148240629638135417156271682602728697831863188145657556148362996941573708704468549436211409054691710737338018013653808721437568016457081463811695847147290950637221516652961122308403092480233327610610025523394491967646196442188178038853023476516037926868778151134293840448838440027476628572210592928308134178530214974151698881159399316527654669006895622802750027969773638752721366372604573148209815552,68774485789368429676657761307853017607505641763019200528929407755810225291844384040653009551560290651822702603617081687170688488928408251529041297627832169395500337394326475783388447213197308758557789886213523567913177806560168339627519744803568579704612085053594985538348406731985832217715735794320331958765603613169239182635942659726695296025708349699193525575771636631597895668603745317897230204483778031001656875719218019161724185335206435423075591431455759839178182855544941800805323564773496608348386686056031534120380491773214905812944531268795113908990066262849384494336712915065262750014384966606670078121612679731669567234662029590468206634417294562673438909800448,188054375734815575727056378170990307907588607521810332316928011302030638744954341285167459383768679521024162013056330833031922414868598206804298994650449302321398846811766722692182058370648326569166944224989094294351838236979903924018058292990738603466608720202879369687722004138313224362053118057860751088789463114663388574827307018153710424858942050407144606127704970478646784049441062728382384918882256093807210894531855952550420207900658426658685126665549462155069715191921687819389838117604548081857971452159910683384487155825075017378241790917815315653144450438964102643537312446917686145630241429867188131921291857866262099049727869303931694137954804332292182195539020609560576,513846712189958599043366439990860627617438670820086633537907799217168950827376087478269289939927188882303610688057380225495194712025905018733069658116657142864723369281039357109032590040663465839932777066900540325400753201134209197961738696964153751580656195368320583536228609729087796636822881478232852928967058319811479614169367402680634165640045669996008010180506392854353174723581768319747408443724009335602834903191036368870973035812958535269274784422621478133119371256643637181076094097353171410980426376916942147787855687257028436250721257417950248471956633466590729414736597712939681692743116132931528112729399173503408012724222542819476872851307857705543839982700667764389510999973888,1403090318120414213261497747367358530003815865726538036410491761721418782188986601450894967563199203879117055820909841041192300663052333675129288199418902879123596452031741722736663303383067267061680200797546840545624919834899880955692984204195792559242827690020065864073609526333048203587849465926085602276164618972563757166972956889057652622077500880527021274253145214703260253890633431089662951816002176013301237559180054976946758427989176342795051663115620974466963046652118281870267517467622055448578348781036014649431331330711535455865555772810632000777384552367830382091677872545409429538453180079706812539875282014228998767096635557445178118325582985591584873595341146206244291496425502315978752,3828662968170607792722810423527209226354316949287506759309258778659046339951661677256081359948674417750384766022658574148960311454001907056785794850581457083616424484427854908514349079917945740509254308810100829900507230825733498149041266113847075162454424708769448973955479354907570107580282634208173020769927857913209421484882327135432412612199771615851207675680799944829507810714063133087253652686303123548408924408994670194039619672073180135991687476538990552497391270324608281736311557764394197927323093471415129441380666686650026354057042764294359887445665081454990027324626620238370791580770907305701987767364402389988138424522857787552834160446421839550911255471738318379862945940838254547346430906605568,10440598187257633854706501406630615012275891778342713703213276645157393411262801513756537831526974713304655764652715798046980984942607733722499506952796971000315621755995583114700458196564205349509311609713455048424301209017672204595689534575703645974615068933344957681151093009244484405028907859061979079472001409148703909345403334594965433179653912302983997492445689803039968648077749339270363706878621364088278154438657154350238357041628940577258192923783223618476615258787045529151349946861966191745723574911507412286744410489513740509316378492539771851286773512019741245593104608103065460704516843829315377135635102957106205626637973670553935663929311259258030488879795575379754454060102199323237451157091602559737856,28452953797748230647903150645328083835204064809836607457632328904182384395726185631669498861554200195629227724436383680899394677028505229397704197273383224069746459290980471777517223196609109528508111408376877467085140284676580788030753618835214114769252032465761240949860030755517912227905313858928311167372061475762833281358686306752480291223712881318512495533295274687838474601503941083771020097528909921852584775147660635175811726685440343784217923081358752300465193972670848005080986552310520565529441527374427303520826819048332910419895167715908944949456343345947678429581439158959380747224741369324274839983750797749394864488780141236285239816244358204722095578221871380525948034478718756955730447533930297230106816266641408,77492524035405894869249704212965220877641680255553534213979008033267809358850256993864917027716011430544019941247678150843374896036326793403699818877593444591931072692795721667831885716911384419035383039243192602556801546155100069242500497951978158339249689114739581626871710760360774207443491310538489325920331242583161855116995519805268544338930973983078430090570617072221553758560715986968893974902553996362776670143090712727908510837035900613656898656850558120269844731814001408855935652822992469682343761369200719603737794440851204061780246189921826523041462206992260369156893503142554723355549297083589255514882112761449594570808467137135164224882423664671615856660849599109929950976310101173961371722293970078957120104547410993815552,210925563893529112871051433554810611325871772396658482236921391061462682213819178480411232993633664419579320093242025208140977227828173297981997334594160508400264003416936402459712637335524109466142873555509547077939205635021149393705112560385726654310839540907182772328854668133550538459931923866946680944626409473000727928993222651247975193976180365800310773284487647261352170702916739437199989564169232031386720970414515645913007172293442695227715981292168988486765405540883395991972045369697898757481078234763361477632338113748013009679209758535665274381958517718586510083175483249025361138267231513824727245010248815872153165019403311854768569033181529100531915744480851984445044765049163800362766931421710400386048336851596975185297079522828288,573775306437002931152830242402451476725306444250612929072561587293976787439115196369673503094189432389347021935951201091976053244420341358158556401976773314382161976219912713503764499638588255949941010608118911274650415482172131542401806382009219864126462619255524907019537690730689821623985251050795211034590966279801809798771448628959472059050696410661710196653603992088986587571839188683144647247017420660487308338106272217910924226746238021603329207636254207013656987235683010318445358855968098623632727863534832137849108284615676164157033931027002191478331198653051516800994382771756556315975818221337209227018616377172772715829047089966840635163360934345284621629524132701287733692926452839693935061463660831670157778996971068547927875681087796918951936]

def pairNearData : Array Nat := #[0,467943260160,4360324908405065056256,25983950558620832202906086768640,126409669118030317278619397662563423813632,546254347543320935321484061857947259247460405575680,2182248605004616142613547119025511580619740013251840999489536,8241196384669908858398848140939356124018688963475091023296943037972480,29829238601444387132476175703424082785043175745786992764987495874623428438065152,104433546459264379615072406738157524797830598317442422886509406299772345695016423955988480,355936287567234637272511830497643261502705895957246215285810546258570520275072140975667209003401216,1186515389361289164618807059833272189387259774561243070797377638958769492380957728450831402189046677107998720,3882185747796138816225620735532421601702815724364489136142426150079070300249768457249229440061350296339483623678083072,12501632995162293984534398064426927828029525178969521720619934453812830785111820934505974649289398172152002167599380157065953280,39708349956710465029369766954111791507673465933677546652804976649611392195475525899003694523698510290023639453175662582563871214892548096,124616625329230575036626232161423220607310382702384776223415381838116931157447238219702488214048298990569374451588233315054511206468106406015631360,386959924099964661928894257451561497980480209280646958518569421201275143060751282086134010562858225359221049659471992128233267075248088041788956337307451392,1190318021712931614053958351807168684146361961940408351312763257153718047967578011678788507952542971037532184357115248995068861372705632624066952513380318793316270080,3630744299368238132326859040517496346262435856331851328227887580643389450681173239599772009613165237423566314520136272155594809406557801238378514089589516925747559732264370176,10990744268913437062417679364580688317363908670452839766709618676252954910346977562695075783428828209735992502167657784991977120787963421379073154183161759549881012007541432837658214400,33042115448212211257225153832618560966622114470876318371285767983015633704417653991296557384969911605540194678389207908598515945447718732648437523307395156340157690457288709321352173867009114112,98715555826513080180425361854742055321588646403494803048189830844621136279203349309959459590397786364328888850759441027743545106979323132907004288984435010316440498873830141677759184968589152502547578880,293233013336584154630866540211293877472542994279340703491557692753604471506874899547796089118465636097964869450604730922879153862292382473367936715268905287225452924444722303717625697718116457298344905962895507456,866468817125484832048844741423545922826228755637748254744480290922884556828733879232562254110806157209388216088781738932130254103031494952846556690135632306505771010790391904928460712127157214282151706407933381219770531840,2547913277613942805219935604940052963217814361894364464611404919882685205879773616820981442103194788348036527390130163642556128638410127083459831140535010123074265196606231025537622321312196412830450061712248342557111861026910175232,7458751728237340740307884072955257520142619647815826677629205072164280822481377338088213560175617993121527649525048408967933490163670539334665352845705869712377487750020203953160815397886831245696428534031710612292547010769235676205535559680,21743932396863276280712988672169852256271936867631095064362043931335233584246045851220269879285614204917300577221662467250100573930172453973932493984093102313534177294714516334505069521884265164009907445180719807146123023900191160917576105045714599936,63143123001640316563608235094721162183451643393440449271387732584749812566871617582038040159449912093464546626734124329522993395423943119129742733269797762578878551181611710938833901385019978921351791761200446735894974183034310094101948690280465274734203207680,182701759217382716581700524673106998397498368344641129545412384644510520689112078183695930574971721811478441211646874821586310267160100062490844460875699734927002509463350146889630400135353874573080461953597220378453527533083892987092669382927837930853801748559217098752,526853146435150866501262056423788143532298160878912586540502799823485013394974888710677024399048311106161802968276528050660557182608021282478658093304454881118536455208049508940131526648147441801546895520021044611154602070869259154053800104095064080886094710470241749352422932480,1514461841279657089681402351231531091729230251652286715061487857113751123842141207578365331874001968558277748147724605120872072607321311213083137067474885134855043044400982481245731379984506293139454385416165714205156407552040814181421859876903994459770872318639925238142658524989999087616,4340424527391419821591335758917950365467768199397540052004975024199892282645688859931766793648225048616887991442161916123928264880606513668797473275476869697412053117534121831731779429456124466950489483619405375792604874323596156244190534664662183566749053652480343601809501436424120594382465105920,12404718707901889851221516224891821135802807888281654072641652669213956101433836664704203682776103589591269201873716062182656184443030222404442795199689765510770833914536314919081513180247397717677899924973773808221988412056691938994344989893853550298408390665050300968429384289782827163697102635558074908672,35358317055581574619938248032099229150512913599981084946016333516888399577381237597995786932203055848380472667018267439167198824812417258298383992955467349898349145432398389552901955049070140097103329016508925442867296906616055627558460509269690089175601802265161171747521574366521296073786939074116024378979871457280,100533191498322052807604387218219773250702162717278136678944755444018795697477654316287433725469711794871689532106554491472122124135607862996435353193063556041814834174806842908300394161871156722335046833174036390608811932982419795292383761001468665381855634718861504512086119749153402276397502912789299909560448115239804010496,285166585931103371993187960170594132402522754412049848977814228585765040992760934712518040256584557967018516769008756298609124688726553197321245828089385748300247414540644107747991168118384693456824157096353622734422776971902681718966243163541424017289010227524771402260895257352507303414480261477627746316437687106654388213743969730560,807072423678873670439732868305723256163369292828650248167389025460838323444822136665814354220713218725248479449108151725231550163179140376190109023049245806074171115647810513610636062710726010760768638709239151979150577614222501893996521137141268837231488143238037369186746875603930725432453713218632796047172547354306378679847745456909490388992,2279294047967049494291567508685967156867275157078734087220969702749631250907229014554665390169426870532765197624377895198121198844032344219976220035908419966472936716905395199031393080974640780801845695049709150065053594915680128682723901906865272246020649986723964990324900478048157570235270575681254486427701377326695945531563183984983337859285333934080,6424032373754755152820172510808384512955846103494155210088285501952443366123473716631556068912382250724896211019442941411471170366166894233684873164474740705006241366484025467394563934992565568495365472807915099579759842227401153493703328746883224448897370179731539593200775910494851801799459867980715473534833302521008755686886110042450703809474741847039222808576,18070775256615307469549281282296635760442650324658918731140790544228072016905764077428868927366807014479901871315618627755947260166496819216394469592910589374748123083044123875257030904860921393265976298521206548923272865559113386827377503924102824370033122928507241850461315909479315373165348399332193043621687080917531127121375906862730129020574971689730909255218825625600,50739560181588443858451161719585572519875107874836883370736665934236267167519636954974801966048935096335702967202121235101831916094890652886409916805942000989779807597237603427656613005314709826223224091417728591708264076836759807514325434803217085397129105538101206632550231303881077423463014116247805982757252808022426209341983015045878500279377343176078018444291160854816759283712,142217770908270814571550842730965593021258973332632551250092349234764211380545965755446468276247166411045858052863045312481042781284546641733749745848066119255494052884533381996568300187005216727811250674391606574905770100962950311418800734349425751779703801899886466545802662317973278006367963217365114840555698720493843335026383994921754994250763346451822360609003712145288206334579246202880,397953386918091462136433376208622270785887582391055203160632327570798113614178385119396048716315924093963206222989314920425449568059264388323170997750507127094679643741196869866970679163434520433238913118050664473649331035800113834096068454035542367342917601694954141399419768120257240522519143909598586729204000249776930081996269967791131422935845707197379227357880621160324291654207821312728080121856,1111765925289512901614722209704947070808717374924473379867657456742182816103897769521126904979734143579371837860727288011424951654459612845967319800033158375052535827357663338973032682893280348592399073822828322780254779040920587346664392139854914612669169110245916608785171219717732665256775036205586199878019545403038488607983603969885926205138036182995039855348514554684680340030067584552897171363221410775040,3101179531680713607846911903960111746001303850247438580643071295892032490022112551863927608834909271658029067630350415840354925761097826898273652485042508409857790376982306880592097334150104941960061406100048420141324525519363697674346928846272518951601264908804777745807372185343061221091464283287724191265999212970195069411183137808905542202638369669930963469720028785951254858119062401325075450896112349730914437496832,8637748318158182819292859453986977205573588661759308099554569695279951793354246440878013401503425274473263814084410208418614545182723389616791071932869444690906463234944443852735157134700705613237371611780963492299822246040313050281971983058005414518113353716408036306528726547728952235216190878275109142601157040164756751548999016886339865464174609711058107403881010750272370349402463685432635790085397473010224585891970339143680,24024824899915080325761122242070618442189687935470414506466375885882610135336980792606486073872413373115598786726928347280751254119800163598576610843693067863169119545653596990906830976387792888999268247533219598545756629440193790554852198493806400769000624919023484403178865963263536086527489598220993010781304498538856040728492473280419314838428712727795923477669860282140970676401835633832103536253335643375116654451241380552025656590336,66731415923936936494712887842429765079398628763494748733761923609098970579673100625317609409350846646278952915952834845258284370444894251055317674566763439398673994705392913630139045364034866121831685258181657818621733578833953830231209907595116146591444340862501642737815056257598066192510066836006014709448777872719386751067384941390620935743241583971482458965565046675286738300475456936801618082623128968504329880615597422151236339082309371002880,185111665510862601399823104009199621608425355998264815930979620208013505850851280216487161625420336962765315222859783483011123249280139398657725630184603591241208767021059422351187951920258848885250454491699540911463873425427717867817182079192812235420359288883154058667780153854146061948311374643109792284240741330018474321704157898545273821222142106400522186439377898070289497824363327122750066829368103143414233348976111092636038583821978048210379496292352,512852113080799234537329039898311414501442894904239311114116862959302003816572082977615608870209587559091958100535096307157048563693000919832619746713423835547870632115838756162587503820907514267719186658832224876496503358873232110162738612667173470251090372824048724018352953564413214305892595899207016011066599276875897526059865339045982048985126260750950652219563027636455244593379968010077524735758561869165078450597110581578112891112236375671319895128193670676480,1419141684086052235204402960569070711872944680501925984323244990800290215947805511781566630244170071451601191096907559487346100509686152288217411333318377804088343675619566094248469020442640882193004331261257227286972522283848920842218777702753670384354976828503811201158106912569384309467616094075465581059122210359430780764618750587268435887718554408614525148634264947088462273650823619654763691512357292915589792509374526435096660433340263392279126216549747499190896045654016,3922417335230178123978815118714493148222855574772283228736702048139689466906422322965695462916205279006984028971657858119683354715435155000338922600594340502247341458042812239482116699569809262593868333532836504940087931294888003141785112287583687932996383138964699522478514194989251566428432949902186595073751588451410491969807745089779139977769322344664798318282930515702211229111600754960437728395597087448690031993295265141934648109344827465990852693798269096295083630121455082373120,10829150956781018953899437165418291934877514984421737183719507229184534164764577811883713524147171919159715552103689761057047500866147705353471364584186035791634398783562603334503634152756162824262584834769568679865533833908658410988619193614158713856764827912693784503671425623618157530943001772434041134172879366000671681238297997575736569229138615870566026347431326265775295342714807744835959646779144842934863451050375878462894052168159718820723237599103170100609655706291449555289665901494272,29865151949364444655948709673699466869962548745421650789861665768356215668170014093821214902687479321919235938832601970889673715034686168690219425099506647198131980826452770468947464852936489858273043024673371345250444227934955283753621393482201733747204600366134238269486285770830892986258635628190727178557036522314708110337107426409796128564816769935350285821726174002368427902767402291782344438466979889996064018286456571333937370543128614016710959009189322238916674284447802349805343282530805377761280,82277483222481774978056032977580608646738850729247774907428755771435573566542757703356487202516553285004614346383931755360560208349570701755196734003354899165011555177407569919104277589572353819650110058166512248456011612097766403900079817940114200868632508976764237138790616969531975774407632068717239768397375976954928079016048696081996146651778807573319658446616869397778595496077174501452475659841598777720655884451682120080617706792705296008221753516420779753171001895483710264547347481282172258117852742352896,226442846960673857291437246574661477113044745027252191549861535073095039225345139999676828915532205161949196656705409927592132842846552624535322275580012472405358417900891691853215117839150428378795939117569365143876116495285495236618662380971406262592264414374273598658065410227596837752192909477950047887603318434563168961881131417389162480814398749519466792838216976024892313767217664126751973148087562046486006221520732733799185068576490430799388576268973451816159694944645797500996681677718465644453619442817033017589760,622604352455101065556013402267335329982154704190582239701857190889718096406910634168952806508392397613618993775367649675241230339793556150698544326278240149731502626006030071089111676136578177074646048633151368673225180107506726393096332851624387664721473301182321125979356274440892973077476388703571734705124777471511162466027456515254631340418449454176510069879324081190807446735950732476408210318711604468539272391103164508870967253589893830220964208967279700456481724340442506618556347735162897055782554439579876250911258456686592,1710233865063744207270402226127317599066511052628291984282673752851496395989612486899095897889500824634194950067777713463988407644848928723929478759907370671551814973237375358303446516905972470731377779806031316468627322572790535595233584186849286959836179815727674368783486682581616197886564417758277698846258645122342209488373815503089414819318897113561293285226179415046274973657967006993900295653828999650081391012830112654209126467122482920193867690654073769072006288607983417542743559732751070243064891529932420135948528982434742548398080,4693554165890167718205804158298671130811357380500055096298140624837087221485275772548276735019303676348997982936424335757681704203980365153487716498115033629666231421167434104756931065365722777351932878412224429830071946589074704734185341553289458988598237083927060685341899884501766381884062718067090562879103787524303393456872037224536648502479900519993118651321157046664158698856193515939861339393933812741164659753039628808054252775115417936177361883788858718520501232108166938063700789157577949152689345114266416969016951534206596578756672064126976,12869559678216513322123605098715516039688548848658182734594553473721117800285121204836514745852983771063778209594474943858491482468389400184944759613885020113252856915865601894281787608858785317593135099380253837133450026117239671991845992965407728045795173723777598886345330841266257958935509254674137229183349619136527956310493771504909550159155836189622032539988126169490864515252662898952446061363214211766981302535694168838314905333132765517091573975340468054337945240383544733810348172463866468999833469215777056147387121031180729364971461637856446856396800,35257620817066791224078350223967951239620330060857746151459693434082320153024982887330320319280475641622989419754381424736636224553304116808501140833487516145316307373756395938683846600264817310956347336979626047632962473481465284436765972866247289574103032613389680112669802027669856352504838343776637111349024009059985267419472486592263599732186400025251758336465201454040746164331649883659627054702661278517588067468941532899293819210764015719400755990413675853136795996688388709775257097139554638802983112842116842186056117766259690058288363376632074008872803350413312,96511964554511650162009521791285339442819385133005020416536493146450702026379099665973803909991674186392166361720905612474983559510681631536017451044347412643952742221534076583356046872487775584600374921931749627542908230986029671922733257767257917375584278677312237997652658343327104876819573338960857908978132892279578685625025990262980809137894600723272046337099203026092014382625223242488145755506299695087387432954172229369141237336995412822564553520194133141188210520857310888264392495120302807313322148552192881033941196416533323177801306417278610955278500653900181013626880,263972690792810368919583882228005318625749880673161678685085832732621208439678047332921073496984788278319277189436894708591989044627650270289690588970836231182799441352377348866498635236730412779548908369318463860357570182563761050257528809298293406830737686130209500479527629072494812581665291329040178855037343795471720703545872392895772192159719760440497053161643455078836938802815590032769419386922400690540543853435440872284510385591655411238964323535885642047174562893184883224922686424539065991993664293253317908075353207926039017413530460346452113428675360959816583297504565003616256,721434472671091917194012591340983468597679857913561282606119876121186741122752680648682419558836396052144046791142998965242688261222451571616516904878336053939617289327947453645322742569545944817870772993049009307780721535941345396466657094974466656179125677959772025803861023887909364786221257985469583160710364278700244208106631612954210559018364913724890422258249218621655856643175886848307834030052128373452817347457139690956597263346194808456105063938217440708620877435338021473218580322739435609581743483377813004960649806093734905682996077989314227452139658059454674401755313199957894579978240,1970174634046817829218882750035916381954474199360149501796387413565527149605902508776569907970734726125142022988375556058018229496009121636266860376230820035147962939204633572900716133392971928119430145377740086625305522190344005830981709421141166720089654500835980906649025801143289026250896006529287048908956756186371590186177821239562127479018956802287105967709082723658601399742348297676929718920227391295327236190581433782970006383058731760732381060603062952355324811736333800102314414561813257666560554455371383307088164252714087850547655654674966191224139802946126257906281466686634134828265166447378432,5376404731676915847640060613756103795849773607852364291517074314815460452632106103828615538690362506765394292636031344014091010781578610754158418054638003864388790921869286098477007879051693122260016160277615326865172717203826161543754426489482924414752867194084639750498685370986999535426726496880194583200634392941002390106772746537275818263657739735219280046283651644108511739612214281899704824952487967119193087152993830636236566804975617128705335427159834239588120895754748350903904504032026199649641766374278655295736297606519607868668308564038475614030920315348056908909214036780332114288553132952001918259527680,14661136302466795806614427317839526950951586440911544515608652680333174906708461277523931751246089213895909277695212284015130450138976115408807262985674712915584094025139657504237231106876682393490290810644761783158329441552799444306299314683828285134146163473497215502934338420237530157785736131695232839802587968604592824491509199797534311519058055552323469977199284740014819082724902439982782203919715901379311081095826555657612971537445324201875321545141119457017866930666338177027762304375709073363931005589714131643959868354454926071276055802899078469972865338893172400212306557580141473409964754501749056453440025113460736,39952173673714897176726930396269064764396987274470500779128471598034189034797980008347571352704545138197028042241118938947401529056977202978030993301925845084939265700102696910083751118269929691969586240769131264748650811291270769929891843081031275049335806461680482495410747233683221565968491659923404017061759056531247969096789545398207638627577158625092979761181912289877216715674058847782146307780542375946752440843700591103742184300349066251748614001597971054501465176649533579448143915166667688780574342550319396494937250393158829414625503070454246623973195587822134317920712947055987866654492781565166640046339167421056208189358080,108797419306190173843772315775097384965974064535857632732249288542904843013444396971076138456060946601106853241234435841525709588753849112278534719193171442435431708414101897744533675924921035110133607944424290130161202113831280358734280857093357057070072682257928138645583189265501914060699646562449637687818355700773985110805603527500670971414860912201712884534154679232972755732278600934042939686010557960913420114007554345180204080583329225681523704905578647499000343330367062273784070955909001776026291811903402442063888572645385537321507546749918427404158261299712771048210075487149227630933671466057567681282668786239301113422321835963645952,296080717541171330447216382132529080493448411881883711281444090178377689903849728811518200104587214531019178013176788353155044548484597131273451804759460462683941944908757960413946028905451378371370813619065066192576086868114039332600510633666375034596557648866110609891851833308262037440387125023013613159781322964880236056686542445984490249209585849069649182307750363349000499167040537956267025760908680302804458930113961035613176883899539767665470939446941582093699010444783988055875718094872178333601612174660510915816736055971588316431433787381960715226011428283201030580018440357787556077362045520747579468821668031417404439078276693505959363059220480,805234974184472872804394987505441518570232068065207472615573672287199142075468680020993504059173562702132936630679956389765752169490096070937876009085433494114745568375887366313119384874180302549986012180319179002176647232948745043445253747742672959481818442487161121940658381033454728084054415093834555581845316680074800643191706315444228136979982583506157715632304151388086982609599923336101484796503751310392346834825746769624701696415597729302699928134995215558521956511515618170054700824181821804874542827415685585914288761484407931191268045748736943281363686497506357363390725786196132954394721221328325475654919998287969711596675787679649535279121946023100416,2188585038220938095899981072267694604639916406392428060642376447998971465263202555970314958116493087048964159594783157506867424459836633172392369961057447435621982645603195819820647451158753642752968894460740998077485705096496611058991902725789047260967939253987014823017103955171478761306716317272400216177030012181267695591502994482140621566107410382102746118022920666312226782875823194786669707571743458696300892866644763532079955717704892159603051938797647523419163073618836844541731714892365002384329626681210459854579031209560018225608381876016458889741160709917244386654916194627915967772041577066273468214010447987306185779687585113120006680790277384480251047087800320,5944831365267527934859952693587739493313163780589280689535311227412173104569581884185302841109454546095523147160283841016059168920513843102910738457919572734355921038626404505493080715496533888313725024604931506449800687390298287212563018575843202616174631743612937674902763426564171602024004374541257857497491917824560098967354798488191205085882907532125430069094286430323439780444280622581576487495501273074787999698783351937070604949947528894003175490088372723419351640472796656429287775849065278442781753345584322982315457769860775716011812378846494120918865883693605596329067539671947416695933108269090897866436958023213510893217269162368554328596267918834372033951070463765839872,16138297643347343816407121790634509703775536783071179839027283297674100062000928110585923944705084438898053268593891367152450069761306392118935152184617693719808823497035321363858611081463147765672648482271419717838764416677304214597313347871346826491877305025240081631509805566358275677377717949199525034063893010510507378870604604691074363211891985171579679162785976976105523618179579368001461341783830546986596802742714462998841628336360873652712478483638740021693013430708061107427714491126618863658244959808568266757440691499395322890928340152875699552596506752664494730184512099960914217004949272808425649942875940221326530830653806627081908191822706143355559897143569907689928827824865280,43784909767348774527959450688978716537599191602829875273607227584318091669016554775090808255765730528817212013713151858733516595327437638436701287434795831673935936456126866927073102911765036267989609864944749630231144820242321379404324572156941378704464029949197387924665973587242037329963778238990641605879508608189307092703865365755827255272200712455148462120269673251745726265028834494338308018472970869652381638131825914737033271734400501002280068950175118529475268332643860106725641008427878277655098405955121471572791095441467441557086297512588241232528485784657942450294926703292836573923383639634809379595983830397777522059890350004713738278744570553539052408101164039153811479807286306187575296,118726043402009404646382091474363186196880275765980606808031071873218657868730411076927652374687095176149701502641704068533932347368688549812957279129082034327583919931811914755640205570834335307324223068940022379703266579366094121321784084404402244415552323210125416226975580733439321814735710728043533606892765080461844827624215178575072319736575322290054055624439100677347488506347290319923573972620076517533405532078776069477621518723351768319960909634414965143561060255055428097060775113530067425943489357508507830350138308034426429699714889445447916536513493596271567262959586848808722309886891757980846289775409369510110448996331783566331857431307804223207173166183669325208833749292357762537121410567208960,321757245219422541130388386564608929351726181299121968391672412076771909240926446988970494323213319012115145505140881966507598750488717383517895306898815874017877870156104282109102331565152929396823127684985358783152817637725971996618487473102257082171419797285443919769053487968368497288500164777999917773881210019010831404489802251777792063271544631151848948000925154289090602050214263433564462934447262094584789466502232273473045637839998708385470817872870750451952102521165116821355480073289430858628730957241876779593775050669176171683650069312095781556592129240588755050909004570510202483693228651193182802058784966128456878946846397400444073945202689788476722791748971263578973378313576917772944559257584469134344192,871519807139507828615007699232987065378862780500102673296453934130403412003114335167542137997535352103539946979423558796210259538699258223321507268577017792973623149736949462307127555133201401641789667105084036830493161985782196097703627077728160082009539538633773888240299646800043917019110219214789836910371301399964299170485720987014589356710705226004639352378357911225229639080855523081397896173141778216122315294648247624485035717920471559435786753258747698029417575816073265151106910039335970638116001434568239286968042903319832917407707569435427255901960163571874614669885337228352814344957915581898465886997995956295392624525163680950551384449303104503468204697272894305640851691783404141999147474886442698133793394079662080,2359382457792526368836535957236388088518718708617049502809499801192474577420130238464549204802111127189184937904825749151196617935221673962880057008748070771512531534994343969515386734254721217381063236208918047222301005877546915064832642238280497517550920958395892541908667395109409887219620762388953961033090466058816742814822143047161846261943515625231006712335163781403169404443406116521714744839064675205879181905468496277243867955156988772770769690619936054904819003172775795237377256454312149532502162575205304570188439464214790452525544729346456867108882522482743266100301526128510826509588835688090493682101709052830220069475927527405549843659102841002537344287400799209411235339026320576636741926886783307161588910007511870468325376,6384059947438330309992471684474669132425988076041652993749780460344813147944990754569778953257102766783383925680049939726448309293973816752714437627531913686093502451057009074628958500943531146275796883496721667093017887476022493768954854299537186948177039657625771084418143696033358290793978646454546125399601074941686279227103792828307933674729604008587489617483080329622861822409562884470167907317134870348161394485106036914060133356957501522770084445388258541119093842950653846058880149283260727599321698273883245687530026356776825972834695703842318023799191940056925815230296710203683027360757121165842737203915118284424209244569798913121037793913597570252643663792403063373712448217864588364302398448914557606448713360492228759968451305238528000,17265464610474325804544957865039328353916779835551176839814838991880713379043034596187034545547443986346200030044046623238199105878980538911089618723875688519361057284572115817651536483565006972392490734841440396314004798832742503055929527655306381095029111928843169396096938006052288079202937137242307054343388583264771403280157454972881084807190094856088109679139682291484309678042166216605969053939070569924559249577743318295345976914173230836932063722392919499465092761648544469753866428473586536552361305464333453328664974502492503290508059407247080021433589244536957349462325757757350949150513195982096519923615032696696110633376556294124214935876842918072184036225587211101113675992985430325060731847909242654811688905003748254146534483072811150430502912]

def pairFormula (r : Nat) : Nat := 2 * (List.range (r+1)).foldr (fun t s =>
  (fact r / (fact t * fact (r-t))) * (coord64[t]?.getD 0)^2 *
    (64*563)^(2*(r-t)) + s) 0

def pairNearFormula (r : Nat) : Nat := 4 * (List.range (r+1)).foldr (fun t s =>
  (fact r / (fact t * fact (r-t))) * (coord64[t]?.getD 0) * (near64[t]?.getD 0) *
    (64*563)^(2*(r-t)) + s) 0

def forestMoment (r : Nat) : Nat := (pairData[r]?.getD 0)^4 * (coord128[r]?.getD 0)

def forestNearMoment (r : Nat) : Nat :=
  4 * (pairNearData[r]?.getD 0) * (pairData[r]?.getD 0)^3 * (coord128[r]?.getD 0) +
    (pairData[r]?.getD 0)^4 * (near128[r]?.getD 0)

def rowCheck (r : Nat) : Bool := decide (
  coord64[r]?.getD 0 = coordinateFormula 64 r ∧
  coord128[r]?.getD 0 = coordinateFormula 128 r ∧
  near64[r]?.getD 0 = coordinateNearFormula 64 r ∧
  near128[r]?.getD 0 = coordinateNearFormula 128 r ∧
  pairData[r]?.getD 0 = pairFormula r ∧ pairNearData[r]?.getD 0 = pairNearFormula r)

theorem alphabet_scale : 16 * alphabetSize = fieldSize ^ 9 := by decide +kernel

def rowChecks : Bool := (List.range 81).all rowCheck

theorem rows_checked : rowChecks = true := by decide +kernel

theorem first_moment_checked :
    poissonCheckQ fieldSize 13533529 100000000 2013623 1000000
      (fun r => 16^r * forestMoment r) alphabetSize priceScaleTotal 1 845 1000 80 = true := by
  decide +kernel

theorem near_moment_checked :
    poissonCheckQ fieldSize 13533529 100000000 2013623 1000000
      (fun r => 16^r * forestNearMoment r) (54*alphabetSize) (54*priceScaleTotal) 1 350 1 80 = true := by
  decide +kernel

#print axioms rows_checked
#print axioms first_moment_checked
#print axioms near_moment_checked
end ClaudeWCT.Numerics.SharedMoments

/-! Rational paired-forest payoff certificate. Retained histogram mass pays
interval-specific fees; the omitted first moment pays the global upper fee. -/
namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

def scale : Nat := 2 ^ 128

def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d

def taylorNum (S u : Nat) : Nat :=
  16 * (List.range 16).foldr (fun i acc =>
    (fact 16 / fact i) * u ^ i * S ^ (16-i) + acc) 0 + 17 * u ^ 16

def taylorDen (S : Nat) : Nat := fact 16 * 16 * S ^ 16

def expUpper (x : Nat) : Nat :=
  ceilDiv (scale * taylorNum scale (ceilDiv x 8) ^ 8) (taylorDen scale ^ 8)

def capExp : Nat := expUpper (ceilDiv (36 * scale) 5)

def maxFee : Nat := ceilDiv (5 * (capExp - scale)) 6

def feeRuns : Array (Nat × Nat × Nat × Nat) := #[(0,3199,2045763124425342226216672522168845155002,0),(3200,3200,2045803868219361084493517180801437890301,0),(3201,3201,2045845020549190886829408595801922551496,0),(3202,3202,2045886585522290722352570299622061746643,0),(3203,3203,2045928567287639525391454240907221692987,0),(3204,3204,2045970970036160254631003411397960749913,0),(3205,3205,2046013798001148495516629735954001182022,0),(3206,3206,2046057055458705533814332669451743418789,0),(3207,3207,2046100746728175948789226854370128238657,0),(3208,3208,2046144876172589775025657731446317860748,0),(3209,3209,2046189448199109282480164385642062015525,0),(3210,3210,2046234467259480424933903054655150478446,0),(3211,3211,2046279937850489007593878243042093427124,0),(3212,3212,2046325864514421625182548630678625157519,0),(3213,3213,2046372251839531422453191074100340017147,0),(3214,3214,2046419104460508729673928915587996729754,0),(3215,3215,2046466427058956626236673321408027485457,0),(3216,3216,2046514224363871486168503126479624672681,0),(3217,3217,2046562501152128559952336237068780311658,0),(3218,3218,2046611262248972647701242550506050298207,0),(3219,3219,2046660512528513919376535087527341109041,0),(3220,3220,2046710256914228938393975113142655407226,0),(3221,3221,2046760500379466945625163016361084806817,0),(3222,3222,2046811247947961461472586292289453091142,0),(3223,3223,2046862504694347264376987920046891340814,0),(3224,3224,2046914275744682804804833727767949081669,0),(3225,3225,2046966566276978114461829166755879491824,0),(3226,3226,2047019381521728271185799721039732699658,0),(3227,3227,2047072726762452480688942694367698014335,0),(3228,3228,2047126607336238837045621423166144385043,0),(3229,3229,2047181028634294824557648525373760512106,0),(3230,3230,2047235996102503624374537505503810344903,0),(3231,3231,2047291515241986290001639265890318684807,0),(3232,3232,2047347591609669856594571715681168083693,0),(3233,3233,2047404230818861449714049186138633061753,0),(3234,3234,2047461438539828460001278835890857750875,0),(3235,3235,2047519220500384851030671414716801096273,0),(3236,3236,2047577582486483668403874120874845702546,0),(3237,3237,2047636530342815818967237078224889389902,0),(3238,3238,2047696069973415189863938243352842398445,0),(3239,3239,2047756207342270177972283276058503559662,0),(3240,3240,2047816948473941701133338949045791735041,0),(3241,3241,2047878299454187763434225904480657569414,0),(3242,3242,2047940266430594647688266903559431344753,0),(3243,3243,2048002855613214809139941183519499904593,0),(3244,3244,2048066073275211545321418323433723049256,0),(3245,3245,2048129925753510517898523541146076658034,0),(3246,3246,2048194419449458203267511303288330142340,0),(3247,3247,2048259560829487349600189585489792500892,0),(3248,3248,2048325356425789518983940545155421295662,0),(3249,3249,2048391812836994794265225722786208078234,0),(3250,3250,2048458936728858731180449679385139219898,0),(3251,3251,2048526734834956637346793337119306308613,0),(3252,3252,2048595213957385260688029039137456815133,0),(3253,3253,2048664380967471970886609066253255403636,0),(3254,3254,2048734242806491518483697463505638756921,0),(3255,3255,2048804806486390457293514870266105139873,0),(3256,3256,2048876079090519316857614933514321915594,0),(3257,3257,2048948067774372612738740201373563527595,0),(3258,3258,2049020779766336783542950675370796064565,0),(3259,3259,2049094222368446144663019205260618260715,0),(3260,3260,2049168402957146949855888710715907745215,0),(3261,3261,2049243328984069652902535276857496229465,0),(3262,3262,2049319007976809462750131445454563017412,0),(3263,3263,2049395447539715286704213032208548132697,0),(3264,3264,2049472655354687157422882726478991673373,0),(3265,3265,2049550639181982240666201511361723090981,0),(3266,3266,2049629406861029521972096366486242944081,0),(3267,3267,2049708966311253271665626516084040248191,0),(3268,3268,2049789325532905388861582437671804150903,0),(3269,3269,2049870492607906726391428873660563352859,0),(3270,3270,2049952475700697499874837358386972391401,0),(3271,3271,2050035283059096885463782807974162379258,0),(3272,3272,2050118923015171912113705501280296961120,0),(3273,3273,2050203403986115755581872857446609446663,0),(3274,3274,2050288734475135542718129020826594001914,0),(3275,3275,2050374923072349775998014424437192472767,0),(3276,3276,2050461978455695489653098157828328275055,0),(3277,3277,2050549909391845250178625085255641120315,0),(3278,3278,2050638724737134115444575369503441743546,0),(3279,3279,2050728433438496668103310757797974840804,0),(3280,3280,2050819044534414240475490486260157603764,0),(3281,3281,2050910567155872449606237300657179927593,0),(3282,3282,2051003010527329162715984884105506293875,0),(3283,3283,2051096383967693014825412740718684187335,0),(3284,3284,2051190696891312601911751064072454623354,0),(3285,3285,2051285958808976474554901160760849499262,0),(3286,3286,2051382179328924058656658670880045641964,0),(3287,3287,2051479368157867631465246574226782325154,0),(3288,3288,2051577535102025482810769766315123302284,0),(3289,3289,2051676690068166393155507487219586679842,0),(3290,3290,2051776843064665561786586584083251636944,0),(3291,3291,2051878004202572120227957981694759853737,0),(3292,3292,2051980183696688367724169488019677422255,0),(3293,3293,2052083391866660867450637171064370072052,0),(3294,3294,2052187639138083543934420515224503296109,0),(3295,3295,2052292936043612924026367587841655895276,0),(3296,3296,2052399293224095665650388571791672858512,0),(3297,3297,2052506721429708520469021346463147135937,0),(3298,3298,2052615231521110878546862661577659243058,0),(3299,3299,2052724834470610045065353607520927855789,0),(3300,3300,2052835541363339401144338927706855116557,0),(3301,3301,2052947363398449602858286453324612607816,0),(3302,3302,2053060311890312974598585809159562378554,0),(3303,3303,2053174398269741255028485021725092169027,0),(3304,3304,2053289634085216856004520693202213629218,0),(3305,3305,2053406031004137796998313596449951492707,0),(3306,3306,2053523600814076479745909406096866955060,0),(3307,3307,2053642355424052470079027445049688271852,0),(3308,3308,2053762306865819456154233793983717145883,0),(3309,3309,2053883467295166554592785485456982226111,0),(3310,3310,2054005848993234138376318234090416563930,0),(3311,3311,2054129464367844362712301788435797943994,0),(3312,3312,2054254325954846567488907432680768060712,0),(3313,3313,2054380446419477737382276938843597256146,0),(3314,3314,2054507838557738203160819780176804383510,0),(3315,3315,2054636515297782770251777232075068380732,0),(3316,3316,2054766489701327463195573116821519197204,0),(3317,3317,2054897774965072077214130130009362454220,0),(3318,3318,2055030384422138730761090678090845531002,0),(3319,3319,2055164331543526615605479038835483535858,0),(3320,3320,2055299629939583143726529139265519233687,0),(3321,3321,2055436293361491693066945981985418530686,0),(3322,3322,2055574335702776157005550658647164109911,0),(3323,3323,2055713771000822505268876480146677461520,0),(3324,3324,2055854613438417566905650468624730732849,0),(3325,3325,2055996877345305248899040012249210868246,0),(3326,3326,2056140577199760406989915222200449701149,0),(3327,3327,2056285727630180588331036780951387159852,0),(3328,3328,2056432343416695868687907515678432017085,0),(3329,3329,2056580439492797010047921986617582505463,0),(3330,3330,2056730030946982167696328581773568605250,0),(3331,3331,2056881133024422379066318004082001587218,0),(3332,3332,2057033761128646069972224589590286291171,0),(3333,3333,2057187930823242817190345900840681671453,0),(3334,3334,2057343657833586609762244547667054266224,0),(3335,3335,2057500958048578854861607434274454201064,0),(3336,3336,2057659847522411377588835483166891931719,0),(3337,3337,2057820342476349667638576293457011723619,0),(3338,3338,2057982459300536629425469651687072657671,0),(3339,3339,2058146214555817095953549849219841201917,0),(3340,3340,2058311624975583370476160403011680626684,0),(3341,3341,2058478707467642063817030065355345217331,0),(3342,3342,2058647479116102499110501499577043446542,0),(3343,3343,2058817957183286959670987288464902627133,0),(3344,3344,2058990159111663059719768199489079626309,0),(3345,3345,2059164102525798521782487144902627664025,0),(3346,3346,2059339805234338648724396014853415362565,0),(3347,3347,2059517285232006782613874750162509253328,0),(3348,3348,2059696560701628046899282720985401030642,0),(3349,3349,2059877650016176672751169191706654646241,0),(3350,3350,2060060571740847214862637940941459783906,0),(3351,3351,2060245344635149966516635214570482583901,0),(3352,3352,2060431987655030888321543696964408231907,0),(3353,3353,2060620519955016369687181660814752547252,0),(3354,3354,2060810960890383146863620137955455396742,0),(3355,3355,2061003330019353706196667442683601508493,0),(3356,3356,2061197647105317506167987347280070174501,0),(3357,3357,2061393932119078356786205126943166039431,0),(3358,3358,2061592205241128299979638571267449308754,0),(3359,3359,2061792486863948339813127220226275548515,0),(3360,3360,2061994797594336376612515929388632407169,0),(3361,3361,2062199158255762704432407693550923247575,0),(3362,3362,2062405589890753436747601458197805726742,0),(3363,3363,2062614113763302230787976968414465950122,0),(3364,3364,2062824751361310686572322495601829205911,0),(3365,3365,2063037524399057802430603781858444037572,0),(3366,3366,2063252454819698874638365179173438113223,0),(3367,3367,2063469564797794234723299280551965622003,0),(3368,3368,2063688876741868224044523951754301179015,0),(3369,3369,2063910413296998811391813219728759531332,0),(3370,3370,2064134197347438265607032632108136720767,0),(3371,3371,2064360252019265301595467197236152936538,0),(3372,3372,2064588600683069124572783668246034136752,0),(3373,3373,2064819266956665803986268737452042238953,0),(3374,3374,2065052274707847415259008914028375518304,0),(3375,3375,2065287648057164394335154114859451140850,0),(3376,3376,2065525411380741556955713496157385218772,0),(3377,3377,2065765589313128241669898709248084497885,0),(3378,3378,2066008206750183042789339433718556051245,0),(3379,3379,2066253288851993606824085761709015986767,0),(3380,3380,2066500861045831973402774269805410649378,0),(3381,3381,2066750949029145949277318671095143464522,0),(3382,3382,2067003578772587011747699139447320176595,0),(3383,3383,2067258776523075245717633561867095783101,0),(3384,3384,2067516568806901826609946801756066681301,0),(3385,3385,2067776982432869569534200565723706707245,0),(3386,3386,2068040044495472073411560478962558191382,0),(3387,3387,2068305782378111997225977625911443512197,0),(3388,3388,2068574223756359014189635113464198144841,0),(3389,3389,2068845396601247998387410640824278776920,0),(3390,3390,2069119329182618007403058194858553656453,0),(3391,3391,2069396050072492633532212196177642990313,0),(3392,3392,2069675588148502305457535566027355558588,0),(3393,3393,2069957972597349131702814402692544998922,0),(3394,3394,2070243232918314886799068462883483917648,0),(3395,3395,2070531398926812750890399589393963289771,0),(3396,3396,2070822500757983423484021603959938187403,0),(3397,3397,2071116568870336242211469783016574018286,0),(3398,3398,2071413634049435947820225445129771335974,0),(3399,3399,2071713727411635747160847852718025522547,0),(3400,3400,2072016880407857336678206987924071719851,0),(3401,3401,2072323124827418559860673359896970612071,0),(3402,3402,2072632492801909383252354753628324530243,0),(3403,3403,2072945016809116886994980293320436674150,0),(3404,3404,2073260729676999977442222899979569469786,0),(3405,3405,2073579664587714541184626088646002807078,0),(3406,3406,2073901855081689771842466836578276267108,0),(3407,3407,2074227335061756413231555096832508156216,0),(3408,3408,2074556138797327674987962541424747399735,0),(3409,3409,2074888300928633589456919041571244616693,0),(3410,3410,2075223856471009591613659349558444402216,0),(3411,3411,2075562840819240116995004739335173374240,0),(3412,3412,2075905289751958026085204357137131950232,0),(3413,3413,2076251239436100677323440119664369909307,0),(3414,3414,2076600726431423484888943628571522196608,0),(3415,3415,2076953787695071811678538381836044772726,0),(3416,3416,2077310460586212062426391576270924179952,0),(3417,3417,2077670782870722856732757707353840505933,0),(3418,3418,2078034792725947176873579731492514303949,0),(3419,3419,2078402528745506400662183031656611122387,0),(3420,3420,2078774029944177145334298172757304958715,0),(3421,3421,2079149335762831864434774542172896410531,0),(3422,3422,2079528486073444156005245035671335513566,0),(3423,3423,2079911521184159757013474919338616867951,0),(3424,3424,2080298481844434215934139144940396827546,0),(3425,3425,2080689409250238252694449383412916540166,0),(3426,3426,2081084345049331832843691108685783327853,0),(3427,3427,2081483331346608000800801324379006824293,0),(3428,3428,2081886410709507535386265379093371919549,0),(3429,3429,2082293626173505509561664985069728433921,0),(3430,3430,2082705021247670855390183746226339022945,0),(3431,3431,2083120639920300054702477193005503271750,0),(3432,3432,2083540526664626095812943683278749914195,0),(3433,3433,2083964726444603856890193979576547490611,0),(3434,3434,2084393284720773097251220716855550063642,0),(3435,3435,2084826247456200258930435980968531183341,0),(3436,3436,2085263661122500302381614749145163278581,0),(3437,3437,2085705572705939822112315838956016790145,0),(3438,3438,2086152029713622710436240824741169705710,0),(3439,3439,2086603080179759660369160339014020052460,0),(3440,3440,2087058772672022821998652312639785654496,0),(3441,3441,2087519156297986950437371156004675569561,0),(3442,3442,2087984280711658407734567357506206697849,0),(3443,3443,2088454196120093405882030427186984199887,0),(3444,3444,2088928953290106903319728578724096944272,0),(3445,3445,2089408603555073593134634183863647367324,0),(3446,3446,2089893198821822447465304375988306150874,0),(3447,3447,2090382791577626309486769559665443164747,0),(3448,3448,2090877434897288051767503802777808228632,0),(3449,3449,2091377182450324847775349290061666840417,0),(3450,3450,2091882088508252131875193784636463466616,0),(3451,3451,2092392207951968852321227731589170995875,0),(3452,3452,2092907596279245651514337939750268890507,0),(3453,3453,2093428309612317638184567545576760373613,0),(3454,3454,2093954404705583447183874272953770354861,0),(3455,3455,2094485938953412314250294486849381496740,0),(3456,3456,2095022970398060925446078984689671287772,0),(3457,3457,2095565557737701833994793697599513674297,0),(3458,3458,2096113760334565270961546501555234323323,0),(3459,3459,2096667638223196210652578838996595880197,0),(3460,3460,2097227252118828586772023916548899263531,0),(3461,3461,2097792663425878591281676462383724016589,0),(3462,3462,2098363934246559024581566882513492692001,0),(3463,3463,2098941127389616703082851265534920300756,0),(3464,3464,2099524306379194968498337876721413978320,0),(3465,3465,2100113535463823382248656525463456618600,0),(3466,3466,2100708879625536728292904399097865001664,0),(3467,3467,2101310404589125488461327666593772039640,0),(3468,3468,2101918176831519996014485091177187171492,0),(3469,3469,2102532263591310515699170433022386000979,0),(3470,3470,2103152732878405542037460994065908079851,0),(3471,3471,2103779653483830651993475532065007158003,0),(3472,3472,2104413094989670293535195331357898803703,0),(3473,3473,2105053127779154937969036658992336493688,0),(3474,3474,2105699823046896071296366345737717164975,0),(3475,3475,2106353252809271548248042657736234287629,0),(3476,3476,2107013489914963882120188633441656244651,0),(3477,3477,2107680608055654094087259822122942808967,0),(3478,3478,2108354681776873797333213762224821288542,0),(3479,3479,2109035786489018244145069950890285182258,0),(3480,3480,2109723998478523118082915667378366388170,0),(3481,3481,2110419394919207908504737747892683706543,0),(3482,3482,2111122053883788761112360456568221359060,0),(3483,3483,2111832054355563755826027562570488550251,0),(3484,3484,2112549476240273622220352436695276519805,0),(3485,3485,2113274400378140962994852922926729324605,0),(3486,3486,2114006908556091117540300256071546422316,0),(3487,3487,2114747083520157860630712421291106301294,0),(3488,3488,2115495008988077195653962421946944027284,0),(3489,3489,2116250769662072567626507936936453422148,0),(3490,3490,2117014451241834888555470611570512771729,0),(3491,3491,2117786140437700836550950301006186258718,0),(3492,3492,2118565924984032960490789087623749368422,0),(3493,3493,2119353893652805194037755146293270075663,0),(3494,3494,2120150136267397456445096614022081894088,0),(3495,3495,2120954743716603092901495842787472387614,0),(3496,3496,2121767807968852984202617743262493610485,0),(3497,3497,2122589422086660234336815399688390920589,0),(3498,3498,2123419680241289425181428291974018267003,0),(3499,3499,2124258677727654509968987828237115547255,0),(3500,3500,2125106510979449501546279560581008309141,0),(3501,3501,2125963277584516197761629783573323698129,0),(3502,3502,2126829076300453274626332680984611673913,0),(3503,3503,2127704007070471168255516469215169038794,0),(3504,3504,2128588171039497259054064269320700830424,0),(3505,3505,2129481670570535966227998011798723144351,0),(3506,3506,2130384609261288457526023859946966330804,0),(3507,3507,2131297091961036778206274085667957125633,0),(3508,3508,2132219224787797304637783766276262474093,0),(3509,3509,2133151115145748531744651074096982846103,0),(3510,3510,2134092871742938309744555266968948384506,0),(3511,3511,2135044604609275754385473000056269099880,0),(3512,3512,2136006425114813166209937713774971759013,0),(3513,3513,2136978445988323408341748869151232715095,0),(3514,3514,2137960781336178308964257129055263130695,0),(3515,3515,2138953546661533774112763977930237825000,0),(3516,3516,2139956858883827418708710845212464615056,0),(3517,3517,2140970836358594648994780974703938710776,0),(3518,3518,2141995598897609257764503764767199348244,0),(3519,3519,2143031267789354725096327099190251345694,0),(3520,3520,2144077965819832551781550782628788511561,0),(3521,3521,2145135817293714090361456947179582441003,0),(3522,3522,2146204948055842479747287130161076443238,0),(3523,3523,2147285485513091433875723190954328075106,0),(3524,3524,2148377558656587782843096052174434215778,0),(3525,3525,2149481298084304816557160375875319720226,0),(3526,3526,2150596836024033636242126642129003113541,0),(3527,3527,2151724306356739878229715030029919883197,0),(3528,3528,2152863844640313337468144066172651367621,0),(3529,3529,2154015588133718185187013194483967694409,0),(3530,3530,2155179675821551646276863424469254867868,0),(3531,3531,2156356248439019177288840834606052434106,0),(3532,3532,2157545448497334365646636032828953759107,0),(3533,3533,2158747420309551954807379138514201868280,0),(3534,3534,2159962310016842588831549783189748689266,0),(3535,3535,2161190265615218063248905453679514589287,0),(3536,3536,2162431436982716067366318686054974130284,0),(3537,3537,2163685975907053606386430517662055366951,0),(3538,3538,2164954036113758500029289357350095898014,0),(3539,3539,2166235773294788567912821046261181206362,0),(3540,3540,2167531345137648330896422649837401435870,0),(3541,3541,2168840911355013282073864963058393375194,0),(3542,3542,2170164633714872011270162161041330641901,0),(3543,3543,2171502676071196702909861080828497530881,0),(3544,3544,2172855204395152769143810592990549822975,0),(3545,3545,2174222386806858628315295119092759760802,0),(3546,3546,2175604393607706893386925739143148949172,0),(3547,3547,2177001397313258496014581811677216604369,0),(3548,3548,2178413572686721539727095516994463160686,0),(3549,3549,2179841096773026950338964284110721200850,0),(3550,3550,2181284148933513273482621632044567029758,0),(3551,3551,2182742910881233258197112671172827222591,0),(3552,3552,2184217566716895162057977661235352731563,0),(3553,3553,2185708302965452017591675054420204342153,0),(3554,3554,2187215308613352411906473209113104674082,0),(3555,3555,2188738775146466651816694460900797011868,0),(3556,3556,2190278896588702515471808267683524990392,0),(3557,3557,2191835869541325128866692965617804882980,0),(3558,3558,2193409893222995851852462151101490533682,0),(3559,3559,2195001169510545413644370201047084702303,0),(3560,3560,2196609902980496902598265776673024364582,0),(3561,3561,2198236300951354589471922000478103566766,0),(3562,3562,2199880573526674947782963084088020160498,0),(3563,3563,2201542933638936629510501680352702633676,0),(3564,3564,2203223597094226559561618678910529658644,0),(3565,3565,2204922782617759728444536409555421485109,0),(3566,3566,2206640711900250689775618755533541790769,0),(3567,3567,2208377609645155207925156839204521691457,0),(3568,3568,2210133703616800951615711402144662972645,0),(3569,3569,2211909224689426591975853096324256900890,0),(3570,3570,2213704406897149138781939242945911617425,0),(3571,3571,2215519487484879836763146530870507603368,0),(3572,3572,2217354706960209445284388485790984031091,0),(3573,3573,2219210309146284239854434513839562555133,0),(3574,3574,2221086541235694603141801677929669932322,0),(3575,3575,2222983653845398616941384922478255826796,0),(3576,3576,2224901901072703625256651344942502678488,0),(3577,3577,2226841540552329312796108464782547260987,0),(3578,3578,2228802833514576433193959314868428743688,0),(3579,3579,2230786044844625927633927324235263197938,0),(3580,3580,2232791443142993797778514259916004684853,0),(3581,3581,2234819300787167737496141868019971478365,0),(3582,3582,2236869893994452186365354425250700145764,0),(3583,3583,2238943502886049144865695826484210918891,0),(3584,3584,2241040411552402787104356610000533544925,0),(3585,3585,2243160908119836622460364182651343382712,0),(3586,3586,2245305284818512693257604669634760128156,0),(3587,3587,2247473838051743052128150255533150566041,0),(3588,3588,2249666868466684540742974654754915988684,0),(3589,3589,2251884681026448691734601039518563778931,0),(3590,3590,2254127585083659398604433273848546837979,0),(3591,3591,2256395894455491844908643199016309962640,0),(3592,3592,2258689927500227054786821274365279597559,0),(3593,3593,2261010007195357322698450337718050009973,0),(3594,3594,2263356461217278701850861514631571170936,0),(3595,3595,2265729622022607679052781579089330780473,0),(3596,3596,2268129826931160139451850924122397597615,0),(3597,3597,2270557418210631728683441757584818759031,0),(3598,3598,2273012743163019753272559373164653707877,0),(3599,3599,2275496154212827823622459765836869738603,0),(3600,3600,2278008008997095538556986313111803149072,0),(3601,3601,2280548670457296637156067247099372379838,0),(3602,3602,2283118506933150203567552579826072941151,0),(3603,3603,2285717892258390704661809463702795425456,0),(3604,3604,2288347205858543869923772529250554422930,0),(3605,3605,2291006832850756688994728528920594468477,0),(3606,3606,2293697164145731105967467162426290463177,0),(3607,3607,2296418596551812332129734908259205699760,0),(3608,3608,2299171532881284081611670042479062325767,0),(3609,3609,2301956382058924458637507763373150210174,0),(3610,3610,2304773559232877692171421153447608472173,0),(3611,3611,2307623485887898425091451822757646574098,0),(3612,3612,2310506589961026822083935162632973562496,0),(3613,3613,2313423305959754364735731535837231251640,0),(3614,3614,2316374075082741855379283300471198725747,0),(3615,3615,2319359345343152854738726683918513399001,0),(3616,3616,2322379571694667534015230850493825610636,0),(3617,3617,2325435216160243731478457380981338677873,0),(3618,3618,2328526747963693868703753832323817821860,0),(3619,3619,2331654643664148304182283614872891857510,0),(3620,3620,2334819387293477684072837202001916342906,0),(3621,3621,2338021470496748893369549140377634084597,0),(3622,3622,2341261392675791317812831756012839104341,0),(3623,3623,2344539661135952299631797089288098536247,0),(3624,3624,2347856791236122910915169674622115006388,0),(3625,3625,2351213306542117479386880067880811376456,0),(3626,3626,2354609738983492685020942612583294405210,0),(3627,3627,2358046629013894504766150414826355551189,0),(3628,3628,2361524525775023819255956830398550929069,0),(3629,3629,2365043987264314112440883564828312933710,0),(3630,3630,2368605580506417395388860663006038090450,0),(3631,3631,2372209881728597271946818823841409645382,0),(3632,3632,2375857476540130939547409707099172192168,0),(3633,3633,2379548960115824886294172052164799592543,0),(3634,3634,2383284937383752108801108313641672716269,0),(3635,3635,2387066023217321837455691919814380673635,0),(3636,3636,2390892842631796020302904048091083850339,0),(3637,3637,2394766030985370187230271929856347137643,0),(3638,3638,2398686234184939796326950257821363008410,0),(3639,3639,2402654108896676758094902509396765491095,0),(3640,3640,2406670322761544544658764379935517163387,0),(3641,3641,2410735554615884124461118801512640524389,0),(3642,3642,2414850494717206922512848760027160397371,0),(3643,3643,2419015844975335096634981615070602600546,0),(3644,3644,2423232319189033645996973037650249983031,0),(3645,3645,2427500643288283234529049718076508360762,0),(3646,3646,2431821555582347123557512262823966122183,0),(3647,3647,2436195807013790270576492597238686036349,0),(3648,3648,2440624161418613469930953061227950563246,0),(3649,3649,2445107395792670392064634407599060835655,0),(3650,3650,2449646300564540526830921189923782111832,0),(3651,3651,2454241679875036359358366207193635644174,0),(3652,3652,2458894351863528610536638464242929610641,0),(3653,3653,2463605148961279065030809073609335989495,0),(3654,3654,2468374918191976394798241656003796322065,0),(3655,3655,2473204521479676472608746506505791095623,0),(3656,3656,2478094835964354965582792219080094118918,0),(3657,3657,2483046754325286511096667229895491602910,0),(3658,3658,2488061185112471514707536724660653613905,0),(3659,3659,2493139053086338580506966387763385407424,0),(3660,3660,2498281299565957797346439472534784342267,0),(3661,3661,2503488882786007568881757282800384654742,0),(3662,3662,2508762778262745400921287616690479313507,0),(3663,3663,2514103979169241056095982544447997502489,0),(3664,3664,2519513496720138763768398723021129364289,0),(3665,3665,2524992360566223743164650552470344153725,0),(3666,3666,2530541619199077171197019284857859512189,0),(3667,3667,2536162340366112915064252662729912121121,0),(3668,3668,2541855611496298865679543459955174592740,0),(3669,3669,2547622540136875564002588326003821587449,0),(3670,3670,2553464254401395021696558710250631932940,0),(3671,3671,2559381903429413214006719987991139349856,0),(3672,3672,2565376657858180680762491753536375203561,0),(3673,3673,2571449710306687025947401382833653227347,0),(3674,3674,2577602275872426873008703892459869697826,0),(3675,3675,2583835592641267028305287087641636741988,0),(3676,3676,2590150922210807245832138895296227249977,0),(3677,3677,2596549550227640090355953901332659133200,0),(3678,3678,2603032786938928981857469842880856561399,0),(3679,3679,2609601967758737591009522755737128132608,0),(3680,3680,2616258453849558363469966967932165146774,0),(3681,3681,2623003632719503101055547867230549603266,0),(3682,3682,2629838918835634242323096199630303054890,0),(3683,3683,2636765754253931786614036727645060406614,0),(3684,3684,2643785609266407718117690454441149698555,0),(3685,3685,2650899983065897334930558436868255079725,0),(3686,3686,2658110404429075098486614903503769639137,0),(3687,3687,2665418432418261518315280333437426211862,0),(3688,3688,2672825657102607204265486208251008418975,0),(3689,3689,2680333700299260582798643367156278319522,0),(3690,3690,2687944216335146916709791537022732766742,0),(3691,3691,2695658892830008221084663427541181561465,0),(3692,3692,2703479451501376466298221456853703539156,0),(3693,3693,2711407648992176136792626513794500573857,0),(3694,3694,2719445277721676809226615900403164944940,0),(3695,3695,2727594166760541964030602449213591554349,0),(3696,3696,2735856182730746790860686007836428581382,0),(3697,3697,2744233230731165333196070194697651272564,0),(3698,3698,2752727255289655984582249335727011811661,0),(3699,3699,2761340241342504145034552289164203871365,0),(3700,3700,2770074215242111819264981949823665800371,0),(3701,3701,2778931245793856139301208837580176008187,0),(3702,3702,2787913445323072275702396285924998122900,0),(3703,3703,2797022970773151019382613530088475815532,0),(3704,3704,2806262024835777528060680684562642734234,0),(3705,3705,2815632857114375398318464349403451677202,0),(3706,3706,2825137765321859409779202968247472060823,0),(3707,3707,2834779096513841058627144189591965472985,0),(3708,3708,2844559248358473423347841430319054209385,0),(3709,3709,2854480670444166059257777325479525745044,0),(3710,3710,2864545865626446576679018861193796921560,0),(3711,3711,2874757391415293400727463304382651047679,0),(3712,3712,2885117861404314022699426854544395091658,0),(3713,3713,2895629946743194922085853651775726822935,0),(3714,3714,2906296377654903356697668928710535659230,0),(3715,3715,2917119944999177483107968143933572479066,0),(3716,3716,2928103501883899882174432821576998753157,0),(3717,3717,2939249965326010631321090010209091790114,0),(3718,3718,2950562317963679698268794098508240351136,0),(3719,3719,2962043609821524747232701041742145414292,0),(3720,3720,2973696960130729571253083396749685729864,0),(3721,3721,2985525559205990422375212530239667501367,0),(3722,3722,2997532670381292640330649981992909380724,0),(3723,3723,3009721632006598322426382618852882335137,0),(3724,3724,3022095859507607481854119578930657955271,0),(3725,3725,3034658847510840365408361540389608428958,0),(3726,3726,3047414172036377509353400277403231140662,0),(3727,3727,3060365492760686876922209305213544149715,0),(3728,3728,3073516555352064224440729702867620351975,0),(3729,3729,3086871193881313876361527196445578943553,0),(3730,3730,3100433333310402553311778998388738311044,0),(3731,3731,3114206992061929002632863411588942316000,0),(3732,3732,3128196284672367149666330249393187202219,0),(3733,3733,3142405424532160553506278512552290465819,0),(3734,3734,3156838726715871358432960453718391305711,0),(3735,3735,3171500610905717939835435520050060058863,0),(3736,3736,3186395604411972322624841114057394483663,0),(3737,3737,3201528345293831486619549122030397659510,0),(3738,3738,3216903585584526167810345425586040565990,0),(3739,3739,3232526194624587033265560317159854551305,0),(3740,3740,3248401162507351483897906055955929467015,0),(3741,3741,3264533603640965174223364110618776541175,0),(3742,3742,3280928760431311001087215259823021001270,0),(3743,3743,3297592007090485193316855280915445156400,0),(3744,3744,3314528853575635641429125996749239163972,0),(3745,3745,3331744949663182172949700836139942401257,0),(3746,3746,3349246089163652559973450107211626942802,0),(3747,3747,3367038214282592121334016040387128613363,0),(3748,3748,3385127420133239358258331569908630823551,0),(3749,3749,3403519959406905673347202034059805119897,0),(3750,3750,3422222247207254431034649285100194687854,0),(3751,3751,3441240866054944017132582547182820795712,0),(3752,3752,3460582571069381772183008080241303435181,0),(3753,3753,3480254295334631369289481420290899414499,0),(3754,3754,3500263155456826079757661708550986987039,0),(3755,3755,3520616457320765155998512495773109825710,0),(3756,3756,3541321702053711038692806392656091865190,0),(3757,3757,3562386592204762085800975596011629655259,0),(3758,3758,3583819038148549892530498195910118101881,0),(3759,3759,3605627164722402940818127641060370285229,0),(3760,3760,3627819318106530253259034352601242597370,0),(3761,3761,3650404072957210953928048280100509441891,0),(3762,3762,3673390239803429239955812919242424377420,0),(3763,3763,3696786872717870387947503010619191564816,0),(3764,3764,3720603277273693269214952427515471830882,0),(3765,3765,3744849018799019708194691625361891928557,0),(3766,3766,3769533930941632244540049398925603742557,0),(3767,3767,3794668124556950885346924168651496310897,0),(3768,3768,3820261996932967777803063399755732282707,0),(3769,3769,3846326241366458001344214274988386302899,0),(3770,3770,3872871857105456573951865102423109309743,0),(3771,3771,3899910159673698091982252075078783633923,0),(3772,3772,3927452791593458086332041163518131416293,0),(3773,3773,3955511733524016203078660490881235317752,0),(3774,3774,3984099315833782848282681003118112654999,0),(3775,3775,4013228230624995247485349112795391276285,0),(3776,3776,4042911544230798370696055270087393228851,0),(3777,3777,4073162710205483419326214934859291211471,0),(3778,3778,4103995582829664273864069633777042016181,0),(3779,3779,4135424431153233336743436244817903784368,0),(3780,3780,4167463953600055626620620585256802991329,0),(3781,3781,4200129293159537028573326806047630104311,0),(3782,3782,4233436053191442719978264932459571871508,0),(3783,3783,4267400313871648627558394614745314094329,0),(3784,3784,4302038649307886208104027705235621305251,0),(3785,3785,4337368145355993006778255088777933395128,0),(3786,3786,4373406418168712714307117106434594076255,0),(3787,3787,4410171633510703475090158953334682093005,0),(3788,3788,4447682526875116944002785307736562926312,0),(3789,3789,4485958424438908316191418434975310960546,0),(3790,3790,4525019264895934862682409076342215805328,0),(3791,3791,4564885622208903354529698821973235242593,0),(3792,3792,4605578729323341491544148788902105251937,0),(3793,3793,4647120502889001819254192835078714215549,0),(3794,3794,4689533569036465807478385211086108123063,0),(3795,3795,4732841290259208430708953741963884916825,0),(3796,3796,4777067793454017888881953794945160734163,0),(3797,3797,4822237999175449725782254163519502453429,0),(3798,3798,4868377652162938801635136309448843401205,0),(3799,3799,4915513353202306228398832988595561481989,0),(3800,3800,4963672592386692007697115613232078541524,0),(3801,3801,5012883783845428950098298510969751110148,0),(3802,3802,5063176302013061479290164206864910137002,0),(3803,3803,5114580519514616918731939983274198334493,0),(3804,3804,5167127846747370466650858122506387381984,0),(3805,3805,5220850773243722856758418193294562474492,0),(3806,3806,5275782910904447236326012652972476388323,0),(3807,3807,5331959039196475692158701217475982720403,0),(3808,3808,5389415152414603880047546976103756205178,0),(3809,3809,5448188509112013348855547793664090208946,0),(3810,3810,5508317683810365693475108552045941867629,0),(3811,3811,5569842621106432327726391574142595195713,0),(3812,3812,5632804692298811658582101868382036081380,0),(3813,3813,5697246754665276612543215260413073100324,0),(3814,3814,5763213213528716406347861700569384397462,0),(3815,3815,5830750087257515638269947419737646516864,0),(3816,3816,5899905075354581693086422770264172995341,0),(3817,3817,5970727629798120765117028576545185555586,0),(3818,3818,6043269029806708507742063000253849235734,0),(3819,3819,6117582460211240927009827802168963210034,0),(3820,3820,6193723093627024870531996865755827163636,0),(3821,3821,6271748176630618454536384286262887812217,0),(3822,3822,6351717120158106294732484495879517667113,0),(3823,3823,6433691594354342116070591969838235049178,0),(3824,3824,6517735628116365513685077634891795014124,0),(3825,3825,6603915713588757553880720728485353046053,0),(3826,3826,6692300915884203010331410421322740381570,0),(3827,3827,6782962988319041369914659616865103468885,0),(3828,3828,6875976493471185292708046421095940323351,0),(3829,3829,6971418930386540276449308985499872406919,0),(3830,3830,7069370868280054914184036252519071657696,0),(3831,3831,7169916087098855615191336016138393708260,0),(3832,3832,7273141725337667967535018655296032632095,0),(3833,3833,7379138435521001296312137570602465538218,0),(3834,3834,7488000547792483501541632434229721090045,0),(3835,3835,7599826242079398516599548232112275500268,0),(3836,3836,7714717729330026466828398377959448565068,0),(3837,3837,7832781442352954520584441573933004880388,0),(3838,3838,7954128236821262962804580922265597262125,0),(3839,3839,8078873603040556288054321398269632672749,0),(3840,3840,8207137889118375834478438351132149524396,0),(3841,3841,8339046536213785073094847909957174298975,0),(3842,3842,8474730326590062373486688665092400545500,0),(3843,3843,8614325645240686220395735425641848712869,0),(3844,3844,8757974755909389243749370449706386653644,0),(3845,3845,8905826092379243778569018991052856837859,0),(3846,3846,9058034565963797289283245152885576347205,0),(3847,3847,9214761890195497510990216462714609838631,0),(3848,3848,9376176923773355483217734069712451065532,0),(3849,3849,9542456032903337062386672616784893780208,0),(3850,3850,9713783474241725959863387270581018969694,0),(3851,3851,9890351799734071019725977667529092471462,0),(3852,3852,10072362284730758422411527948457873926529,0),(3853,3853,10260025380855213820559035637082907489053,0),(3854,3854,10453561195202758354236429719332325335827,0),(3855,3855,10653199997557778149115262164597111282028,0),(3856,3856,10859182757434729121910960907123325250516,0),(3857,3857,11071761712875249610284337317651384986271,0),(3858,3858,11291200973070011190816933213038772110776,0),(3859,3859,11517777157020683669684147310950249134877,0),(3860,3860,11751780070615371849537397174148084840747,0),(3861,3861,11993513424661021327841667968563330868751,0),(3862,3862,12243295596599590925100544562096145219668,0),(3863,3863,12501460438832341134219187637604121061418,0),(3864,3864,12768358136789578290548458671038845846815,0),(3865,3865,13044356120112915375095022883866244644444,0),(3866,3866,13329840030564970100365414968416313924308,0),(3867,3867,13625214750548952929749785403193441119302,0),(3868,3868,13930905496409473786217052809228758800483,0),(3869,3869,14247358980997939530293303945585065676712,0),(3870,3870,14575044650323113729528355379179741695275,0),(3871,3871,14914455999471936457434380793788933180345,0),(3872,3872,15266111973379924860019133766319341024024,0),(3873,3873,15630558458456983775358778097567260936553,0),(3874,3874,16008369871536078689177347568259200201075,0),(3875,3875,16400150853112053395006072981073818499825,0),(3876,3876,16806538072379294314483530537697319770520,0),(3877,3877,17228202152163653463442248308416999341638,0),(3878,3878,17665849722480093755271085090525633650554,0),(3879,3879,18120225612137350341471503570056222334917,0),(3880,3880,18592115188559370834602820495611203549652,0),(3881,3881,19082346856805733518137495620173289473626,0),(3882,3882,19591794729655488659156888791366639070726,0),(3883,3883,20121381481577333716471363220296519680876,0),(3884,3884,20672081400450754052045617682297365944214,0),(3885,3885,21244923652035462339387605828259808063466,0),(3886,3886,21840995773418639638862588854005594896833,0),(3887,3887,22461447413010447750478698081879419978592,0),(3888,3888,23107494336118304088766285156064595517028,0),(3889,3889,23780422716720772483509157701016837089964,0),(3890,3890,24481593737795047751254163603015951513698,0),(3891,3891,25212448524441577555741730040600776082035,0),(3892,3892,25974513436110442659353028023027750168971,0),(3893,3893,26769405746483318271459570037138479080342,0),(3894,3894,27598839742020485025774843364350900145861,0),(3895,3895,28464633272864662105682228581186115388786,0),(3896,3896,29368714792724711748267750324335782314878,0),(3897,3897,30313130927567159676221713012822556292213,0),(3898,3898,31300054616449224498405322491473706533469,0),(3899,3899,32331793871663761316203042828359513901642,0),(3900,3900,33410801209567508012596502649904478056996,0),(3901,3901,34539683808066139649470119855704837387926,0),(3902,3902,35721214451773705886525944962097275954288,0),(3903,3903,36958343331395271758052850667864173670430,0),(3904,3904,38254210769950133344377584273510169636481,0),(3905,3905,39612160955114435198640668155148466743422,0),(3906,3906,41035756764278072482801716527074729203490,0),(3907,3907,42528795776949918680318405108004401556092,0),(3908,3908,44095327577983777048671860951372323284395,0),(3909,3909,45739672464819593820194426715533025579920,0),(3910,3910,47466441682634460862650217862691721072140,0),(3911,3911,49280559323080448622283667601739894192142,0),(3912,3912,51187286035267888184338673718337527130881,0),(3913,3913,53192244711963193139268266575702900470754,0),(3914,3914,55301448329754392024146420498986743604216,0),(3915,3915,57521330139356630273893400976157079312148,0),(3916,3916,59858776421464111000683566256568289672348,0),(3917,3917,62321162044805393011577017912523708757591,0),(3918,3918,64916389086550353176633517118615726533891,0),(3919,3919,67652928801200649509575150552820732027252,0),(3920,3920,70539867252852186422259346868946122973304,0),(3921,3921,73586954957562398802037025094237129544755,0),(3922,3922,76804660917839383689934331392974313019075,0),(3923,3923,80204231470388766926729776075535168949453,0),(3924,3924,83797754411650352743488303139535775960217,0),(3925,3925,87598228913826753257466341984287064663950,0),(3926,3926,91619641797607996324849164767669299365635,0),(3927,3927,95877050787256090894121584540287743662310,0),(3928,3928,100386675439836033294677016196381555596569,0),(3929,3929,105165996513957105477136357924025032094607,0),(3930,3930,110233864625312456818567745367906635428471,0),(3931,3931,115610619127580527094887215676823011298924,0),(3932,3932,121318218259011256008742417996907977531872,0),(3933,3933,127380381708540470487369244135230353752157,0),(3934,3934,133822746881998917146989762377742572893174,0),(3935,3935,140673040290536271549401494884575620930131,0),(3936,3936,147961265641605260313184457642084472679178,0),(3937,3937,155719910389827961736291265594813597290819,0),(3938,3938,163984172703150832839189480713947103634878,0),(3939,3939,172792211021554723652948548102165116120405,0),(3940,3940,182185418634244542817337619301563095866271,0),(3941,3941,192208725980129467099061641715907860530762,0),(3942,3942,202910933689410680110424508955837248304401,0),(3943,3943,214345079735640215739254491629266693737452,0),(3944,3944,226568844462726258787132017530139709614630,0),(3945,3945,239644997695752714561962876177531013335351,0),(3946,3946,253641892644660107796143743573953562936828,0),(3947,3947,268634011873212541222375819488061607668925,0),(3948,3948,284702571240701103347001037438234640319667,0),(3949,3949,301936188440147960353288894078546925737706,0),(3950,3950,320431623565384445583461864567390331915643,0),(3951,3951,340294600052858204975072477076339501237786,0),(3952,3952,361640715376761962520314233275120392901081,0),(3953,3953,379536990389944597429874025328168200988635,724511378186869947471383235643144092),(3954,3954,379536990389944597429874025328168200988635,4086470343956687705054583475208738818),(3955,3955,379536990389944597429874025328168200988635,7415142587293140930384484702501406864),(3956,3956,379536990389944597429874025328168200988635,10710857679705470856453693838434741563),(3957,3957,379536990389944597429874025328168200988635,13973941929618668803056871200744973938),(3958,3958,379536990389944597429874025328168200988635,17204718414681241027416452747586788171),(3959,3959,379536990389944597429874025328168200988635,20403507013753094714901186952380663649),(3960,3960,379536990389944597429874025328168200988635,23570624438576712227262309927424104717),(3961,3961,379536990389944597429874025328168200988635,26706384265134749368213916833407709734),(3962,3962,379536990389944597429874025328168200988635,29811096964697162379057091987846922622),(3963,3963,379536990389944597429874025328168200988635,32885069934560937637317661447687727462),(3964,3964,379536990389944597429874025328168200988635,35928607528485467595991492596044959977),(3965,3965,379536990389944597429874025328168200988635,38942011086826586366955681851844200091),(3966,3969,378728900125178676035310929142940809304342,50700207964899194408069962219105604702),(3970,3973,363951028907892326914357104142757252399477,61999604051286184249781489322735932449),(3974,3977,349749785134781795540416093671172045935125,72858101594830139881579916760691248177),(3978,3981,336102669001613587420652063094752100690656,83292904304790824764774271775674628577),(3982,3985,322988058638764603089173241889344728443475,93320544607619068606727518731722184458),(3986,3989,310385175854516073880181609034299923987454,102956909840180726563391790048577436515),(3990,3993,298274053215032367480672699920020415822984,112217267420930062669317685257125837225),(3994,3997,286635502408867680108855913326742240617291,121116289038912618882920874436214625005),(3998,4001,275451083845878779679943683214080868876756,129668073898921524877433800807782987287),(4002,4005,264703077442377701081455262904551817820675,137886171059635816180724979141382107554),(4006,4009,254374454546237719266001351373373832972762,145783600900132290246100893206521180261),(4010,4013,244448850957472015955427032587904243202646,153372875748781464743685151088766966251),(4014,4017,234910541001540072823116482693454394051831,160666019707211121859444543446140051898),(4018,4021,225744412614304717913893569075766288899841,167674587700745624110458733135235220431),(4022,4025,216935943399165565308453471244807416127462,174409683785503650606065058627960516130),(4026,4029,208471177618434860065985591622703256858822,180881978741159286120679619350944176071),(4030,4033,200336704082501911621487593174567198581994,187101726977239632874883036963166965738),(4034,4037,192519634901754714189009893566109935115309,193078782779744513433822472159291944795),(4038,4041,185007585067594265938884757484367117819731,198822615923828669479828325236991481102),(4042,4045,177788652830190675450966941290536750689286,204342326677282479489656994912884365953),(4046,4049,170851400841892465368230650284094860146994,209646660218582027249259295192212412029),(4050,4053,164184838036413549250334572787293852679867,214744020492351823465595517343929899717),(4054,4057,157778402215088090281657258640867482991745,219642483524192144949976710677710621635),(4058,4061,151621943312603696656576653631065176264076,224349810215966397755692107962966827709),(4062,4065,145705707315699943013458744629539892186344,228873458641820775162632330387495257186),(4066,4069,140020320809353735830269138237839283539174,233220595864417464374833446568595145008),(4070,4073,134556776125967202288860234391984789237145,237398109290102503981975760176535102708),(4074,4077,129306417074029151866193783350868299303507,241412617580998903282937817403222089721),(4078,4081,124260925223639251463382101853392146070571,245270481141313647121914622063706712505),(4082,4085,119412306727166322819938106766849904864872,248977812194472613748399950195860097906),(4086,4089,114752879654160013106174852013927857980163,252540484467049159582088721135877314832),(4090,4093,110275261820449849223793450511427356483265,255964142494829146547244439630578499892),(4094,4097,105972359092148654341427581574884913698590,259254210565756517819968747597353666423),(4098,4101,101837354146029722047128745520483736842981,262415901313928217900890315415235865945),(4102,4105,97863695668470201308496538967290484343799,265454223978254391390190599601035034183),(4106,4109,94045087975847989773263067636353317861817,268373992338868505772952092309293162303),(4110,4113,90375481039947164698378461597849616072281,271179832343861485170332554746928904376),(4114,4117,86849060902568657887815040802936763690066,273876189438423305470621866949017902739),(4118,4121,83460240464159520092388497333329287948878,276467335608004009181622665612179885329),(4122,4125,80203650631866698353765230381275666955081,278957376146653003731433019180932693220),(4126,4129,77074131812990705613142150375987564140832,281350256161260091926115599318936205133),(4130,4133,74066725740361797772759063628812620221234,283649766822003257998176555664860253526),(4134,4137,71176667616687156311034265213731609799628,285859551368906134215289111617747700493),(4138,4141,68399378565422937694651268174270835069741,287983110884021664297777027412813151920),(4142,4145,65730458376210694877729010648604780092791,290023809838387148707632334231268955706),(4146,4149,63165678533384370561602016744683484443611,291984881422539014901051391705836830747),(4150,4153,60700975516502546018059277654218807443987,293869432669032737516457282246819730709),(4154,4157,58332444362291613711981830297020292516432,295680449375083795896874142778601556114),(4158,4161,56056332477799709528297733829624866154833,297420800833128877214999046536931129921),(4162,4165,53869033694959247301283928196302901191817,299093244376802211049379430827713916552),(4166,4169,51767082557138375145492595397842932771143,300700429749529473396158571425858244893),(4170,4173,49747148828629225775799764021515670279949,302244903302660661451813998506275058145),(4174,4177,47806032218374043913015253536756667197493,303729112029793269806509294251307612125),(4178,4181,45940657309569702612442607766576516649680,305155407443677566057390833469124535567),(4182,4185,44148068687117304701182736905440636010692,306526049301846358094701490399820894735),(4186,4189,42425426255197022257470194551182477194847,307843209186871971283824850524770210631),(4190,4193,40770000737549552838519423494420780864422,309108973946922831734692573132286700881),(4194,4197,39179169353335043210644002317866121681027,310325349002070716904640863652055589961),(4198,4201,37650411661718508283130681302934938412376,311494261521587036248776670431974580549),(4202,4205,36181305568598095526395945084754130836354,312617563477262105523337515897022318148),(4206,4209,34769523489149436899052450398258729405011,313697034577584954821756849746262181830),(4210,4213,33412828660106198225252322829563888961956,314734385087432451275685884527936590025),(4214,4217,32109071595934171179344506686615486867056,315731258537735123522671589283845043803),(4218,4221,30856186683284231414161575916486701667670,316689234329412759136420285827795949565),(4222,4225,29652188908328569110704826052406526539978,317609830235705332056400381372450736895),(4226,4229,28495170711795132435348606865743796758940,318494504806863839239147155089625618174),(4230,4233,27383298966717543626752511616540663493061,319344659681010929238105331040893460472),(4234,4237,26314812074112172243841835297694714335247,320161641804832545108063564193644661477),(4238,4241,25288017171980888526310633088656571999225,320946745567618944393569136243815024557),(4242,4245,24301287453217567868406189486677619087035,321701214852036173657855338687115587160),(4246,4249,23353059588168959553025544737885085688875,322426245004877146531183207607494399273),(4250,4253,22441831247766342504316838773170868031612,323122984730914693583618522478497839009),(4254,4257,21566158723303730594231362584477132691052,323792537912857118591605292461253757598),(4258,4261,20724654639091512432506734799606559935370,324435965360289715942433077549988826560),(4262,4265,19915985754361558180528955293576621846163,325054286490373192509881424293083799798),(4266,4269,19138870850941231891398299813948076027654,325648480942961816080002345452223839281),(4270,4273,18392078703349636228480706905932522812068,326219490132700210005777166519019497203),(4274,4277,17674426128100002448078887285791376887032,326768218740557865605023628260787778416),(4278,4281,16984776109117629143173191583022418765265,327295536147164491692546067984778733643),(4282,4285,16322035996303367256073894605713098073939,327802277810217112532938985290556706982),(4286,4289,15685155774388537341955749916544236720690,328289246588141215324348483420184300230),(4290,4293,15073126399338531611035930869173026462477,328757214012103095685937228527583601187),(4294,4297,14484978199669374338693861913114313736382,329206921508388719610823646279711330310),(4298,4301,13919779340144359369414559447175601155316,329639081573085783314130361148249775710),(4302,4305,13376634345416715595219126098865985683944,330054378900930083763545998964731422172),(4306,4309,12854682681279227047394451323386679707245,330453471470104692699961338952208163169),(4310,4313,12353097391273004077117145957746866367779,330836991584710640582494811014723798676),(4314,4317,11871083786495310619759331849727223680196,331205546876560753559220195786704098374),(4318,4321,11407878186530638700651683871300115093922,331559721267883840020058824278997050136),(4322,4325,10962746709510218686022249588774999141048,331900075896464491425427354900258976430),(4326,4329,10534984109382990640236192813417083738749,332227150004684246801315759002470658561),(4330,4333,10123912658555861840505681708277372233794,332541461793872677255171500056372307595),(4334,4337,9728881074132956532144904677310797825769,332843509245321985483241600472285224396),(4338,4341,9349263486052640266247777266696096842611,333133770909265898430559668577666556534),(4342,4345,8984458445487482088645590810952282264039,333412706663072875349011163018266811512),(4346,4349,8633887971936108615077882326200417259625,333680758439854878061504548893841378036),(4350,4353,8296996637497205699868370030786655588253,333938350928646078003635644348273238743),(4354,4357,7973250686874833107618305286740780086224,334185892247260831316119127334689811082),(4358,4361,7662137191720828663362834135859980095814,334423774588896967537123583185687898568),(4362,4365,7363163237974480478278028292299181218621,334652374843508840713553545098863773688),(4366,4369,7075855144911925217622434774491385266352,334872055194934618110307918468207098744),(4370,4373,6799757714667969824200883844846403452119,335083163694723867814193235390388981414),(4374,4377,6534433511041313231342327659150961230794,335286034813574591543275652555187224572),(4378,4381,6279462166440539885428970871591164857027,335480989971253374396594098987849196687),(4382,4385,6034439715872841855980327109820732727166,335668338045838232909025207563590676017),(4386,4389,5798977956920271579561111925583231922359,335848375863090982600457886720517506744),(4390,4393,5572703834689500744438907097410889203049,336021388666734464323570484717258678947),(4394,4397,5355258850760627709323268029123671359914,336187650570379715241941054898648977648),(4398,4401,5146298495198598849646243463086089164614,336347424991819097277736371679515792394),(4402,4405,4945491700727348580605838202647411636069,336500965070373457293892101062940727251),(4406,4409,4752520318201876408880875062789169567075,336648514067954544854909408101210678620),(4410,4413,4567078612547222846931826702060440423514,336790305754478112605736456171369423606),(4414,4417,4388872778365732846764473550376228536266,336926564778238330242056200960896753013),(4418,4421,4217620474445156949534024523292225768250,337057507021830316435074758317337585302),(4422,4425,4053050376430085974331412122169532835309,337183339944184696169800705948887488986),(4426,4429,3894901746947992228409164137441227845460,337304262909256087481012304712138366410),(4430,4433,3742924022508804505192291289979968312307,337420467501886276664322869470822005756),(4434,4437,3596876416523519359868977719949367014555,337532137831342521199946525926541063907),(4438,4441,3456527537812889419740923081729588005869,337639450823011892660108068505758165090),(4442,4445,3321655024001771259502376011149128673710,337742576498713806839894424104385063696),(4446,4449,3192045189218299533078270581668360737635,337841678246074855525250110556743534432),(4450,4453,3067492685539717969257364846853089426049,337936913077392725120386195466082362308),(4454,4457,2947800177648477415782171401447020587639,338028431878399334344519480239162208382),(4458,4461,2832778030183140862374892637062796430737,338116379647317319990311182284477069388),(4462,4465,2722244007288748447524138060031881321250,338200895724588620958862804572877496564),(4466,4469,2616022983890623722970410290877008364834,338282114013639132083216075408726406253),(4470,4473,2513946668234176536539014769774919822608,338360163193029197209289605373163992544),(4474,4477,2415853335251107226214720016094229564432,338435166920326063118996728224283494083),(4478,4481,2321587570329569675802729240005743937534,338507244028021300531840373571296428945),(4482,4485,2231000023082334341381914567103911061744,338576508711803594829210653114052500836),(4486,4489,2143947170722832733829186922990918574054,338643070711485197341361533200278645488),(4490,4493,2060291090674187132749168363276745948782,338707035484868688831223157014534506996),(4494,4497,1979899242050957628684487159795536391199,338768504374829521761188152838696150874),(4498,4501,1902644255667396119955839070613937372007,338827574769879059317712652320647641604),(4502,4505,1828403732239505899997290103287164319121,338884340258462499964385251133669216189),(4506,4509,1757060048461187363670922336045163153966,338938890777236150131918815426796987804),(4510,4513,1688500170647225704685610750284503664334,338991312753558968806751294972140822885),(4514,4517,1622615475647865036274087344987747706579,339041689242424141135687908953999142922),(4518,4521,1559301578751234137829324091291698661222,339090100058047629199064307034435446484),(4522,4525,1498458168300960264250109983039272221546,339136621900322182862735464788705779886),(4526,4529,1439988846766946693055805140554159714939,339181328476337158687853760992725148793),(4530,4533,1383800978017513783226536999943100079865,339224290617156677368276966553906264083),(4534,4537,1329805540550928477804479150472522280464,339265576390041137692837128071236103404),(4538,4541,1277916986453788966087569805225450054208,339305251206289885691184896803484059397),(4542,4545,1228053105862804589891566730773457286800,339343377924875899979509394738340139754),(4546,4549,1180134896715230407281984941393275321705,339380016952036687384436363965429780085),(4550,4553,1134086439581594930892093084854896265204,339415226336979176127034010910005402402),(4554,4557,1089834777382411711917286466015921142956,339449061863850237043470078597824155201),(4558,4561,1047309799798303402576054330230690868620,339481577140118546749903045051430991484),(4562,4565,1006444132190402958927723457677902729415,339512823681507820952712398489927577984),(4566,4569,967173028855042523743228183099066406073,339542850993615982253003133904734009972),(4570,4573,929434270443607577240864354442634144830,339571706650349576139779272135074321641),(4574,4577,893168065385033041762797314650588502758,339599436369297703090372263056126328416),(4578,4581,858316955154759630190928549901118008144,339626084084164885805335076740701699960),(4582,4585,824825723240062884430868712394369889218,339651692014377630915708823700004087756),(4586,4589,792641307657523714934433812526217239177,339676300731974966630736240285975525437),(4590,4593,761712716884037103541849519228949770410,339699949225888934649202185449853413704),(4594,4597,731990949068163886416168547369858559751,339722674963716879419918516981074294034),(4598,4601,703428914393827760106525581589733216337,339744513951083403954757020564412282833),(4602,4605,675981360473354086062502855038712772534,339765500788686042575031512475449593558),(4606,4609,649604800651646620180238258969146940472,339785668727115031158570117050918518307),(4610,4613,624257445107910568382528392302800121318,339805049719534028836215626580973975953),(4614,4617,599899134645762674297717142472668466190,339823674472305256075331790980585945204),(4618,4621,576491277066828403148011261721611534238,339841572493639257314781333751050542252),(4622,4625,553996786027019445320041830053693079885,339858772140346366620894369746812846730),(4626,4629,532380022278618208784378824423032042597,339875300662763947258617489798754895732),(4630,4633,511606737205075933528623269886334613104,339891184247930585851258623338055834042),(4634,4637,491644018559063532273552616702231056272,339906448061075644356886651370833584254),(4638,4641,472460238317804995075458739297219368079,339921116285489904019049617697263318282),(4642,4645,454025002573077721539299795026947251605,339935212160840470525287630682077526356),(4646,4649,436309103376487778035085406817668568859,339948758019990644765187026211808579454),(4650,4653,419284472463725925902481777691466486717,339961775324383094915268031117537371617),(4654,4657,402924136784487238236264126727194225128,339974284698042389338014878792791661828),(4658,4661,387202175767597934046270037655528758849,339986305960250762360474063507305966084),(4662,4665,372093680253642241918969769927687246610,339997858156948882928411510446910114117),(4666,4669,357574713030024016454606752791282484689,340008959590911376084609752407945943714),(4670,4673,343622270905936655437842059431697255029,340019627850744905994030572303725347445),(4674,4677,330214248267154626319229789852239042428,340029879838754763758677106671567542989),(4678,4681,317329402052904472585330312010078687308,340039731797724110575480680557317027603),(4682,4685,304947318099326248594150922030445267367,340049199336648304051155999054071123922),(4686,4689,293048378796201495124116350493830277828,340058297455465079969283893349571769090),(4690,4693,281613732005704547615683655201204037094,340067040568819770883965160333638691115),(4694,4697,270625261193933461409286377054422495541,340075442528903214070659460102930299001),(4698,4701,260065556727898311106149184505278329209,340083516647398532176049328597951385731),(4702,4705,249917888292491118793737095540577754653,340091275716571558047235303073507257104),(4706,4709,240166178383736113791966932301729026254,340098732029538318449384795535635931174),(4710,4713,230794976836324236144320578105142057115,340105897399741687550518177158995881584),(4714,4717,221789436345074468956083090728376164066,340112783179668068096690953894076837509),(4718,4721,213135288941539317108804040384561043606,340119400278833754135295376276689946913),(4722,4725,204818823388485036790127341893061745558,340125759181069472060891706030034938736),(4726,4729,196826863456431459254253058176339091331,340131869961130484823658524267978296097),(4730,4733,189146747047833747300525065414978644307,340137742300658575593524785150389615424),(4734,4737,181766306135831388253563490895041471450,340143385503521200320356522885487637319),(4738,4741,174673847485780290481067328286618337604,340148808510552111845319546749962291703),(4742,4745,167858134129024056404575385296293772310,340154019913716809937308471398133361487),(4746,4749,161308367559552318469900366130910616335,340159027969725260348708408871150662069),(4750,4753,155014170625339333902720945819640476242,340163840613113450262948636979648245680),(4754,4757,148965571087256653856946933944296905258,340168465468814505954863785479313919284),(4758,4761,143152985819511356540848746051148606719,340172909864239289770481744225855433769),(4762,4765,137567205626577737809071815945768464528,340177180840885616374218317128876934219),(4766,4769,132199380652567096881619566261106820574,340181285165494481377281848378407195446),(4770,4773,127041006359918886802694106724715408865,340185229340770977768126557163961713180),(4774,4777,122083910055198506108672507157372388816,340189019615686885876961068368232891930),(4778,4781,117320237940653819034074745836672673226,340192661995381259828907026374171364865),(4782,4785,112742442671015479782818390096990567263,340196162250674696524337363996970332298),(4786,4789,108343271395826621677941054731271473058,340199525927212361121103945381563466274),(4790,4793,104115754268356722628755826850284262366,340202758354250254812063853737666316555),(4794,4797,100053193402893693085764513679208541937,340205864653098645460644871944681346491),(4798,4801,96149152262918622700449245510026952459,340208849745236038481627962531671329295),(4802,4805,92397445463350292778949838478930090284,340211718360106543373285155537289271133),(4806,4809,88792128970702594908268553067492109976,340214475042612989693492198565710756687),(4810,4813,85327490685628431230308782941834050760,340217124160317664231702985422491642582),(4814,4817,81998041392929507575421300694232430221,340219669910362077897003762859223686211),(4818,4821,78798506064693626901765735742487125551,340222116326116725685936247788560104613),(4822,4825,75723815502780569624910186289294739072,340224467283571375307104327785999686268),(4826,4829,72769098307415295876968786896462890886,340226726507476008944993230402701674236),(4830,4833,69929673159163874331955329382656223751,340228897577242147591613381920954989412),(4834,4837,67201041402064051561703408564278186618,340230983932613907735628348304039862567),(4838,4841,64578879916159511591449093651174942732,340232988879117775373054583460566765780),(4842,4845,62059034268145393358083536167782923239,340234915593299731713417172642331405733),(4846,4849,59637512129273260592262695747043030556,340236767127758028044951191218489535236),(4850,4853,57310476950087152357084128233412276160,340238546415979583458267365712337708569),(4854,4857,55074241881969253950005562859028648333,340240256276987667996896209256625197269),(4858,4861,52925263935864761803104682307565438205,340241899419808234812344905773071918149),(4862,4865,50860138368931291936021544167954377002,340243478447761977577038553759731820488),(4866,4869,48875593290219294788246630116247944308,340244995862588913295548468003344914329),(4870,4873,46968484476836962014250387249851117053,340246454068412025315374255762526328440),(4874,4877,45135790392386592873354761769418048901,340247855375546246352852083432228864095),(4878,4881,43374607399779857540001947301181406077,340249202004158816313521202581310882005),(4882,4885,41682145160847359736776285631631773240,340250496087786814211270144706838553102),(4886,4889,40055722215453849478031788126236197418,340251739676717437203727133341283341660),(4890,4893,38492761733114837293421335293755208014,340252934741236382304137604212373669822),(4894,4897,36990787430383664669350385545559456391,340254083174749477357855945035498431914),(4898,4901,35547419647540724611805393240373402358,340255186796782507053482757796987561762),(4902,4905,34160371578368917309674208578509516178,340256247355863986756436057738133406326),(4906,4909,32827445647041968740514663765815697922,340257266532295451500602573049895317145),(4910,4913,31546530026385318984610355062744470802,340258245940813649257851764614861428336),(4914,4917,30315595291993271277717212585740920604,340259187133148856343253243670247839148),(4918,4921,29132691206901337308624452240714429502,340260091600483368234478301562717819936),(4922,4925,27995943631719559978078935368233329700,340260960775814060926336233085074706479),(4926,4929,26903551555331369497681385417910632211,340261796036222765955118441527993244284),(4930,4933,25853784241453547250583231384924830542,340262598705058056171597819156874895244),(4934,4937,24844978486536436901279316985262079225,340263370054031898984753399471121090548),(4938,4941,23875535984659944661638692883051718420,340264111305234498918185887699036140870),(4942,4945,22943920795250389878507860913443643581,340264823633070521704060495493325776868),(4946,4949,22048656909606171783354804594154546436,340265508166119767579900055052864314490),(4950,4953,21188325912376766435250239516331045501,340266165988925241754307243392969344088),(4954,4957,20361564734290007622832665728754058426,340266798143711454979073875168782921434),(4958,4961,19567063492567175118643513327182026163,340267405632035676624891511193281402221),(4962,4965,18803563415604342249885730622143216768,340267989416374756430876148927378237757),(4966,4969,18069854848631942375357299096073266879,340268550421650029016059284762206354108),(4970,4973,17364775337192812062445635872644068400,340269089536692717142143995731971035634),(4974,4977,16687207785402260810474520343856899417,340269607615652155445754521862621523445),(4978,4981,16036078686072198405687981486691464332,340270105479349065765762347058923128905),(4982,4985,15410356419895209135017634120679070161,340270583916576028133520112278664695595),(4986,4989,14809049620993877522168720184615731166,340271043685347207833046510624699866734),(4990,4993,14231205606245816333312726888891895743,340271485514099318541832265107843912220),(4994,4997,13675908865895890919460061362719422677,340271910102845724303603022154171309599),(4998,5001,13142279613064234606841522129747916960,340272318124285508839673334862583222579),(5002,5005,12629472389851961657193231582634317313,340272710224869269357826933663737095684),(5006,5009,12136674727836155135701650412277689871,340273087025823323453922141677738380481),(5010,5013,11663105860831878915882373365328171156,340273449124133951813018324685913877323),(5014,5017,11208015487881772544661223595830820560,340273797093493236099359084614539846045),(5018,5021,10770682584513365986991750681251767000,340274131485207990577713208897249431914),(5022,5025,10350414260380724447709701485055556340,340274452829073227535962220721362608136),(5026,5029,9946544661480522689615333584055241474,340274761634211540387792391762230667275),(5030,5033,9558433915203269963965767904407019798,340275058389879734335872767736246046227),(5034,5037,9185467116548272732454459698273716818,340275343566243982584426389948422010216),(5038,5041,8827053353896140312254283642702584644,340275617615124736223414982940847595803),(5042,5045,8482624772795311746160082203318229231,340275880970712567985651410409953337176),(5046,5049,8151635676279309884804386063549985005,340276134050256084027105476562461957024),(5050,5053,7833561660289306289339002319960294026,340276377254722993626515982536303649070),(5054,5057,7527898782832199819544230201419552502,340276610969435384173051072261588959133),(5058,5061,7234162765557860784665081390008820457,340276835564680207942791388489358742630),(5062,5065,6951888226490555984562351811433842597,340277051396295947891497060138432806352),(5066,5069,6680627942698929234918431470808807086,340277258806236391950237206305151944521),(5070,5073,6419952141736345254827945042042272244,340277458123112409042214534132976803824),(5074,5077,6169447820728987249268763669325349077,340277649662712585186045968943443139912),(5078,5081,5928718092032902361455212602270626534,340277833728503544557643465296033916579),(5082,5085,5697381554423283801736659271830623192,340278010612110748196612237242810074655),(5086,5089,5475071688819730573339477398160923089,340278180593780532112752222083706620956),(5090,5093,5261436277590099401346221410544942153,340278343942824116824808045163704694673),(5094,5097,5056136846512920319561541388395132316,340278500918044291799970617408643548710),(5098,5101,4858848128514246566819919700669933336,340278651768145450813534837908753724181),(5102,5105,4669257548329307866899263342902102920,340278796732127627870073588417806803336),(5106,5109,4487064727272488472247251231428661245,340278936039665157978706122429522825029),(5110,5113,4311981007331010066208808124263004949,340279069911470562715357611992508481497),(5114,5117,4143728993828315216860261882195711459,340279198559644237095731650300304024653),(5118,5121,3982042115932568063869234832369819005,340279322188010491786960486049068382341),(5122,5125,3826664204313961911283846419513431439,340279440992440483067917433109808959046),(5126,5129,3677349085281693188251164263256521027,340279555161162542173721712165720512476),(5130,5133,3533860190757570872950186174332079527,340279664875060395696123839999065641935),(5134,5137,3395970183468321319413506944233358784,340279770307959749526599784285831488110),(5138,5141,3263460596762760235196005966028670968,340279871626903690392708828288809956522),(5142,5145,3136121488483174531679928819444652119,340279968992417341321373848523527741641),(5146,5149,3013751108342523619219888283387118717,340280062558762190337153655325077338898),(5150,5153,2896155578280467724912849685623562720,340280152474180495342320612928430796335),(5154,5157,2783148585291793873553158502265970241,340280238881130152402710912215624065402),(5158,5161,2674551086240570871481802671763652190,340280321916510399553969054385567528399),(5162,5165,2570191024192354276514658704576443243,340280401711878713723023757691913102636),(5166,5169,2469903055815011011263216931651496560,340280478393659244406405136653104665061),(5170,5173,2373528289416269894311878474936394451,340280552083343114338235765444542401712),(5174,5177,2280914033202956708106360723073126011,340280622897680904495156868210077330461),(5178,5181,2191913553363067194125420219237023708,340280690948867628402670066016738606683),(5182,5185,2106385841587394223212170995993974411,340280756344720488807766138831854201157),(5186,5189,2024195391662380988914477656100877808,340280819188849698347421932408044239549),(5190,5193,1945211984780244109298096646870386179,340280879580822634853457300824691066033),(5194,5197,1869310483226221768353647461795180069,340280937616321591373945212856326256910),(5198,5201,1796370632116074363728088518316568922,340280993387295370843128607634552405468),(5202,5205,1726276868869719581157570705802458826,340281046982104965579538853428460261501),(5206,5209,1658918140119140595237155299644154577,340281098485663552420281707949949041881),(5210,5213,1594187725760484620117075370144071016,340281147979571025293409358612652888640),(5214,5217,1531983069871587963722218762297553529,340281195542243278375662665192457291622),(5218,5221,1472205618227041008348813457193532754,340281241249036444665934126456386500372),(5222,5225,1414760662153359382450211254897559691,340281285172366286812392375511115021696),(5226,5229,1359557188476872564089207435302464086,340281327381822929350660365709162136009),(5230,5233,1306507735326594180709727839029242340,340281367944281114129583128267079930612),(5234,5237,1255528253563614636378085684129972111,340281406924006153608263171560318628205),(5238,5241,1206537973617471103516202752409124496,340281444382755749891944649294811211597),(5242,5245,1159459277518516484975108593334292932,340281480379877840824192236669082989957),(5246,5249,1114217575923541256558398802762919328,340281514972404628158259484184563713850),(5250,5253,1070741189939813182690309643110946044,340281548215142936781601467573115833588),(5254,5257,1028961237560302292790808718016516239,340281580160761048154574154261640241386),(5258,5261,988811524530164257958998945253455480,340281610859872145538268348067912819365),(5262,5265,950228439471575991677178858126306355,340281640361114503218299000463988611903),(5266,5269,913150853100764037683440080272520145,340281668711228546772706072560583542897),(5270,5273,877520021377549792147581749442345648,340281695955130906474747843566823400644),(5274,5277,843279492433966107960300623329661825,340281722135985581157427349103458664761),(5278,5281,810375017134487217630749494545635881,340281747295272325288539726362734519481),(5282,5285,778754463126167674128749027735954891,340281771472852367605609384069777042524),(5286,5289,748367732242515262005139714708532491,340281794707031565432330864517505206711),(5290,5293,719166681130236334573744064957555267,340281817034621094735337759952905426039),(5294,5297,691105044973098205314184850159817534,340281838490995772075863187522034454600),(5298,5301,664138364192060152943466794981712145,340281859110150100858937382641779407880),(5302,5305,638223914005540064124360615313900380,340281878924752130677248572043927640309),(5306,5309,613320636738215206497580780333433830,340281897966195215081960014009395592359),(5310,5313,589389076771110277095300430692587692,340281916264647749783139420348093011034),(5314,5317,566391318029910606528702912352401652,340281933849100970082741577693899720614),(5318,5321,544290923912459847746217038268381891,340281950747414883268221381241655326112),(5322,5325,523052879560266011031628677145287852,340281966986362408739971008218160640077),(5326,5329,502643536382553447042385198136309173,340281982591671795806190008254980903689),(5330,5333,483030558744967210958936433597165528,340281997588067386350011764272258084480),(5334,5337,464182872738465817519708033411446808,340282011999308786951400717229759354142),(5338,5341,446070616947234152518505126086768402,340282025848228512526347284039069717709),(5342,5345,428665095137615462887275560361110277,340282039156768161124228976623850708095),(5346,5349,411938730793104922675894320608192041,340282051946013177197040086187786551842),(5350,5353,395865023423372088173958046354436056,340282064236226258417831374089834751471),(5354,5357,380418506578090246042736320374583273,340282076046879458976602320880678080653),(5358,5361,365574707499051676768703130765932060,340282087396685040216646693562696987328),(5362,5365,351310108346643481384146435074694802,340282098303625117489695422907896134384),(5366,5369,337602108939252964616335117788653151,340282108784980150200984637856432751167),(5370,5373,324428990946568584351635467740176353,340282118857356320182579476173975479820),(5374,5377,311769883480045963259007110437885352,340282128536711841772002179165041916950),(5378,5381,299604730026022063146774833625603031,340282137838382245280655488113050330957),(5382,5385,287914256669087853262044256033188869,340282146777104673910017880199170020239),(5386,5389,276679941555374030570999102754936404,340282155367041232610538736433540757751),(5390,5393,265883985547368811860526179170630338,340282163621801425876102700803013769404),(5394,5397,255509284023774626681023628931268810,340282171554463720023483474753205458222),(5398,5401,245539399779724687665794819425372780,340282179177596264119081159361581788444),(5402,5405,235958536984423774866862966850735833,340282186503276802382236309617418617500),(5406,5409,226751516154952905540757013660494959,340282193543111809613426155076342833117),(5410,5413,217903750106587524625007944818985427,340282200308254879964644430180745146170),(5414,5417,209401220841525994720131767336727279,340282206809424398186295599009512501250),(5418,5421,201230457339411938956617865941845908,340282213056920521348122708275377578091),(5422,5425,193378514214462751259835973476448460,340282219060641497939234546548867487899),(5426,5429,185832951205389599891928124970850785,340282224830099350202471393265890911447),(5430,5433,178581813465613687085376621766862868,340282230374434944549486110917251320436),(5434,5437,171613612622551480543858966838752493,340282235702432473933420272050611174573),(5438,5441,164917308575960110459173578274748810,340282240822533375124387392322769124586),(5442,5445,158482292006505058979326418581405246,340282245742849702937661070051685381610),(5446,5449,152298367566837512935709731294813332,340282250471176982604086416355046500720),(5450,5453,146355737728550087881854050605487607,340282255015006560645425452040062858777),(5454,5457,140644987259418775334004383286479558,340282259381537473822801191429166652503),(5458,5461,135157068306337561906958616550477793,340282263577687854962862086821164799546),(5462,5465,129883286060311800938532436128588235,340282267610105893732538647448677802348),(5466,5469,124815284980798604589782847491226019,340282271485180369728144853720661131341),(5470,5473,119945035557568728367463092412286609,340282275209050774566971302478996522526),(5474,5477,115264821589116044601311013987238632,340282278787617039018351274345850457852),(5478,5481,110767227957459095896921456210070372,340282282226548880585423432627129746144),(5482,5485,106445128879965680602097099558621125,340282285531294786347474222995772750212),(5486,5489,102291676619587195903749303790037408,340282288707090645294866507567733033230),(5490,5493,98300290635615747726889216763673059,340282291758968043833232974723630580671),(5494,5497,94464647157774980827614931796844661,340282294691762237599953580726193983672),(5498,5501,90778669167126293149317127652472395,340282297510119812223100195356828938654),(5502,5505,87236516767916638289061684139072648,340282300218506045160206227295563207978),(5506,5509,83832577935113509978749442008274260,340282302821211980280623485671046759423),(5510,5513,80561459622967924156615004787723487,340282305322361226400112548927187345933),(5514,5517,77417979220518210531030920001666616,340282307725916490538955395838896427766),(5518,5521,74397156340497102765374621227595131,340282310035685856254587076819742428767),(5522,5525,71494204928632845423471529028218074,340282312255328816995850875121697848870),(5526,5529,68704525680842653511849842889052555,340282314388362074037848818510322134590),(5530,5533,66023698756304671084104166472559101,340282316438165108183371612900307510217),(5534,5537,63447476774863351799023113962975312,340282318407985534058458135380636387316),(5538,5541,60971778087673669255822984924856586,340282320300944245485186658635441908485),(5542,5545,58592680310422472094666428322582176,340282322120040360083792254297912516463),(5546,5549,56306414108881314127038995671929206,340282323868155970938112905688128289299),(5550,5553,54109357226944872264175683574320654,340282325548060712852686780326777599170),(5554,5557,51998028747693248139775747716290901,340282327162416150436070563980128415944),(5558,5561,49969083578385641757978376151261325,340282328713779994962658332610148222203),(5562,5565,48019307150647672170683232473091589,340282330204610156694004888376370770452),(5566,5569,46145610327455563207644406898923625,340282331637268639079967014128915725808),(5570,5573,44345024508848051822945028723196661,340282333014025281009457681527501817510),(5574,5577,42614696928611731779646927098807414,340282334337061353039864971038702232452),(5578,5581,40951886134488115012786590260023516,340282335608473013302837904913135807758),(5582,5585,39353957644741456466986505520023430,340282336830274628561819017117800073184),(5586,5589,37818379774205806171154871409753101,340282338004401965683056049641501635151),(5590,5593,36342719623198267486163993746048606,340282339132715258576514179332642804180),(5594,5597,34924639222943478265247117148864923,340282340217002155465810358088614702682),(5598,5601,33561891831402300924486267498493421,340282341258980551156690098938327456049),(5602,5605,32252318373636001003384820224259391,340282342260301308791363965753152389663),(5606,5609,30993844021066189244633816300841845,340282343222550875400927450728407226144),(5610,5613,29784474904210862347756872761658727,340282344147253795399826441109248480524),(5614,5617,28622294953688351006601322593076234,340282345035875126004634499057094803334),(5618,5621,27505462864484205674549843982511881,340282345889822758404021522318562268571),(5622,5625,26432209178671342689280857165360992,340282346710449648357469830922973148399),(5626,5629,25400833481961445342960822499003239,340282347499055959756796755104642292485),(5630,5633,24409701709645963542808971588532740,340282348256891124546645031954612478632),(5634,5637,23457243557658367607875133585668904,340282348985155822267585274006889584644),(5638,5641,22541949994655861078101297712343915,340282349685003882358128498083334481307),(5642,5645,21662370871178808044475340540292474,340282350357544112229569435617723664243),(5646,5649,20817112622099936021268398283697248,340282351003842054009979197381364362625),(5650,5653,20004836058723179455428389405973217,340282351624921672740652512549197223832),(5654,5657,19224254247034065778228539986092517,340282352221766978699711151164123242815),(5658,5661,18474130468740040486898123702302970,340282352795323586423199203660601724561),(5662,5665,17753276261870296354996867350437147,340282353346500212893712278558783677315),(5666,5669,17060549537830722327311488402237799,340282353876170117270222489102929046074),(5670,5673,16394852771930719666659259176060449,340282354385172484440141631105990680211),(5674,5677,15755131264515038402224933936263083,340282354874313754585659465505900050286),(5678,5681,15140371469945650509481444277985325,340282355344368900870861493893153113124),(5682,5685,14549599390786174761599702347855958,340282355796082657273935539693969374479),(5686,5689,13981879034644672147284635533795375,340282356230170698509788595652129925249),(5690,5693,13436310931229903820267457487306218,340282356647320773912489624988121577606),(5694,5697,12912030707271543014972100181803276,340282357048193797074010047474280988386),(5698,5701,12408207717046509377733514770717899,340282357433424892965635933565340171197),(5702,5705,11924043726341693972266659601588407,340282357803624404201063410047060804593),(5706,5709,11458771647768005403195265028421722,340282358159378858035454723301485639449),(5710,5713,11011654325422026197261401124546619,340282358501251895632524249541755302505),(5714,5717,10581983366969752689364901759841017,340282358829785165071942925470430287195),(5718,5721,10169078021302025051167063790039611,340282359145499179511901383759164908436),(5722,5725,9772284099983455811559926422001402,340282359448894141866465497238541776532),(5726,5729,9390972940786049643956231171933887,340282359740450737304305596931581464219),(5730,5733,9024540411665384264621689447394967,340282360020630894824398278193726213870),(5734,5737,8672405953601297639264036131664500,340282360289878519115306672119812227751),(5738,5741,8334011660786601849885275890551777,340282360548620193857563713706732514443),(5742,5745,8008821396706516487367058955069544,340282360797265857583438690478079269769),(5746,5749,7696319944708378057631220309317801,340282361036209453164888522457245634239),(5750,5753,7396012191715826712633194935812135,340282361265829551958712920634575706675),(5754,5757,7107422343794184218676223375126274,340282361486489953597780598431944633243),(5758,5761,6830093172324200652154149756857341,340282361698540262378608454166777835133),(5762,5765,6563585289589841819035609671403574,340282361902316441158495969432871420425),(5766,5769,6307476452632391661680805623076134,340282362098141343639784231301181523605),(5770,5773,6061360894267927779444945270849124,340282362286325225884566530254949828975),(5774,5777,5824848680208264601483656853147360,340282362467166237870271158621477366545),(5778,5781,5597565091266815896167512225084891,340282362640950895864914700660612443076),(5782,5785,5379150029670571705914829431692168,340282362807954536370435664431581456092),(5786,5789,5169257448537577426705120453737409,340282362968441752353315611022378288613),(5790,5793,4967554803616005118705164756896727,340282363122666812453631721269538332251),(5794,5797,4773722526416177387885680698940154,340282363270874063836716541639546365987),(5798,5801,4587453517900798198813091926236335,340282363413298319325684742300245370727),(5802,5805,4408452661931216466110957929362904,340282363550165229428182041595391278093),(5806,5809,4236436357698848831181188634246090,340282363681691639846778544308412638991),(5810,5813,4071132070400967252837309971778880,340282363808085935039429688054265935191),(5814,5817,3912277899448962581681104584421965,340282363929548368374326354218230934904),(5818,5821,3759622163524972944973664462836315,340282364046271379402216460238449903417),(5822,5825,3612923001829459551067523238581711,340282364158439898748869858220472833074),(5826,5829,3471947990887964722591760182225043,340282364266231641110744283422834805191),(5830,5833,3336473776309938227695048169404078,340282364369817386818061349404890719157),(5834,5837,3206285718916207355087021209349441,340282364469361252411388311485361573739),(5838,5841,3081177554674431203745814134763368,340282364565020950660414818773634328504),(5842,5845,2960951067903756399848789872300577,340282364656948040436886569337302399286),(5846,5849,2845415777230914572248082988168167,340282364745288166837583171076967106884),(5850,5853,2734388633800204721725109427714167,340282364830181291937780124709372105590),(5854,5857,2627693731259218116721565802647797,340282364911761916540790210776986815922),(5858,5861,2525162027060820298704754945781727,340282364990159293274914160643002333518),(5862,5865,2426631074639833743005425229700707,340282365065497631375421720541811024055),(5866,5869,2331944766040094101699094192132420,340282365137896293476010358383797324431),(5870,5873,2240953084584110051333642460336493,340282365207469984721529043096521332074),(5874,5877,2153511867193467812346449116928247,340282365274328934501588688179691833832),(5878,5881,2069482575983411607597446330163812,340282365338579071092989719858563128743),(5882,5885,1988732078769724909668036288043722,340282365400322189487662282843277453369),(5886,5889,1911132438140157570282701762838414,340282365459656112672018033100970891074),(5890,5893,1836560708756213201871768457665672,340282365516674846613237181639225551177),(5894,5897,1764898742564150989454450072382166,340282365571468729198044007953737504772),(5898,5901,1696033001606587110359540198564261,340282365624124573359942659790099305448),(5902,5905,1629854378138122983361884410347660,340282365674725804621677516872152833837),(5906,5909,1566258021759999736462561210337504,340282365723352593270834132251766380001),(5910,5913,1505143173299898908195213672430019,340282365770081981377993757150399574932),(5914,5917,1446413005173696100013312145923807,340282365814988004858683231812940222773),(5918,5921,1389974467976244008528577692030811,340282365858141810772509639864683794125),(5922,5925,1335738143058130256992357440589539,340282365899611770045323135991556850623),(5926,5929,1283618100854839351418948924278640,340282365939463585792999810932366521823),(5930,5933,1233531764743861934011717794820568,340282365977760397418467864760844149157),(5934,5937,1185399780214052734634107161301990,340282366014562880646903678522966425944),(5938,5941,1139145889139955106106219176785596,340282366049929343657588995565058428633),(5942,5945,1094696808961898105799360870025473,340282366083915819464736151419370389904),(5946,5949,1051982116580444568726350449125670,340282366116576154693645326826364988426),(5950,5953,1010934136781237820452325999710178,340282366147962094892846726604744276549),(5954,5957,971487835013472435544742903412584,340282366178123366517392359268969055121),(5958,5961,933580714352112131054293076780075,340282366207107755713188013241343021440),(5962,5965,897152716480606423046835151807723,340282366234961184027187739200859520247),(5966,5969,862146126537227569444821908583384,340282366261727781163402624591812894343),(5970,5973,828505481674270666557225652612452,340282366287449954899995168945887960896),(5974,5977,796177483185242258058592002362601,340282366312168458278232721916758279330),(5978,5981,765110912060815773772188329701517,340282366335922454169751103602477824495),(5982,5985,735256547839764497709544987916698,340282366358749577324425840715704540933),(5986,5989,706567090626303177237943747609331,340282366380685993997156841543989564012),(5990,5993,678997086150286098972407138436196,340282366401766459248036473295826675497),(5994,5997,652502853751530420272363873012748,340282366422024372006684819991931672715),(5998,6001,627042417174166396180199106683000,340282366441491827987993547310890396713),(6002,6005,602575438061368220347525959161930,340282366460199670543115670393001836971),(6006,6009,579063152045097558626096356443917,340282366478177539526267218196581260288),(6010,6013,556468307329603273992857625489947,340282366495453918254763130684540463248),(6014,6017,534755105671371835279452387935683,340282366512056178636688732228166268573),(6018,6021,513889145662019729560193015146735,340282366528010624537705009826045028741),(6022,6025,493837368224267874539704123518354,340282366543342533455696088486100125174),(6026,6029,474568004234644333668966087799676,340282366558076196569286318318152277685),(6030,6033,456050524189931128238652556989162,340282366572234957223678020914082263108),(6034,6037,438255589837608955820430248956240,340282366585841247914785104574013561493),(6038,6041,421155007693665293314053487989385,340282366598916625830258526264874908822),(6042,6045,404721684374121615497189452488641,340282366611481807003713183325884453970),(6046,6049,388929583669509033986126434866075,340282366623556699136268637403953541122),(6050,6053,373753685294283109658712957358366,340282366635160433137404625797914359275),(6054,6057,359169945245822288978795072448708,340282366646311393435103256032830346339),(6058,6061,345155257710204565691415193036502,340282366657027247103299893325162121098),(6062,6065,331687418454407614373324578132754,340282366667324971852790948325355494136),(6066,6069,318745089646932664014358908854055,340282366677220882929946085369458728986),(6070,6073,306307766051115509361105488007926,340282366686730658965841946508897577438),(6074,6077,294355742537562880774508535680087,340282366695869366816771582210992218081),(6078,6081,282870082864242355528217247288992,340282366704651485435485761202186611655),(6082,6085,271832589674762406045520857918847,340282366713090928810986667633629628653),(6086,6089,261225775667309225577096188509639,340282366721201068013218750548092947891),(6090,6093,251032835888561707134970764248390,340282366728994752377583330417877727251),(6094,6097,241237621108688315678286463885902,340282366736484329862840743436865400919),(6098,6101,231824612235242410490313663009911,340282366743681666614654157089756930395),(6102,6105,222778895725418558102917230743625,340282366750598165765770645342470399639),(6106,6109,214086139957714133835518499245092,340282366757244785502625674617932704694),(6110,6113,205732572525560548085451351705912,340282366763632056426994906363889848425),(6114,6117,197704958416949160214605891924164,340282366769770098240200327075229547886),(6118,6121,189990579045480672532297748808564,340282366775668635776304402545147926791),(6122,6125,182577212099615753481766564409610,340282366781337014409694519377311949400),(6126,6129,175453112178200959923041776871118,340282366786784214861468789238297803769),(6130,6133,168606992181589767199764852790753,340282366792018867428081779573579958186),(6134,6137,162028005428875646173768687274954,340282366797049265654793389434935532261),(6138,6141,155705728472904545287855163343984,340282366801883379475584460441240393679),(6142,6145,149630144585839665645585166776345,340282366806528867840357407074710373694),(6146,6149,143791627889113809628299593787213,340282366810993090849427828236618043082),(6150,6153,138180928102625521910394707961209,340282366815283121414532436243949928521),(6154,6157,132789155889016343412317532738711,340282366819405756464828473453466241492),(6158,6161,127607768769809318159669145171477,340282366823367527715638891923328098907),(6162,6165,122628557591094923956394464760401,340282366827174712017004805811995371498),(6166,6169,117843633517321275704477118784504,340282366830833341298440991983012791075),(6170,6173,113245415532582154574319888296898,340282366834349212125650456773579396307),(6174,6177,108826618429600472685397289884457,340282366837727894884339292491756770265),(6178,6181,104580241267377465406266587310630,340282366840974742605682241879562198728),(6182,6185,100499556279220436029519612662871,340282366844094899447421636471944586783),(6186,6189,96578098213575436855677322118786,340282366847093308844036775973840594328),(6190,6193,92809654090776987161213536087360,340282366849974721338896506047239031016),(6194,6197,89188253359485888547761348802951,340282366852743702110803900554971551370),(6198,6201,85708158437219445798369880203471,340282366855404638206857763068659654834),(6202,6205,82363855619986939891159827649973,340282366857961745493090364184321416953),(6206,6209,79150046346627993381612884280518,340282366860419075333893688703185958055),(6210,6213,76061638804013443482322237332641,340282366862780521010816771595077313637),(6214,6217,73093739859808385211125831941241,340282366865049823890903773077890507469),(6218,6221,70241647310016021571092957772900,340282366867230579354345626893938356287),(6222,6225,67500842429019682108560159952584,340282366869326242490836763244688963924),(6226,6229,64866982810319635524525952915157,340282366871340133573661954693596226580),(6230,6233,62335895486621885614803610948181,340282366873275443320186179070655145136),(6234,6237,59903570318378732381401846556580,340282366875135237947081980074784389800),(6238,6241,57566153640306202915172166746291,340282366876922464028303597704462027372),(6242,6245,55319942155812183459846716087796,340282366878639953163504621607567722276),(6246,6249,53161377069661862498345279380382,340282366880290426464295595787174905325),(6250,6253,51087038449584547053922345907913,340282366881876498865449397010377171332),(6254,6257,49093639807888638689680184787980,340282366883400683267884864487772598635),(6258,6261,47178022894500126604048147756014,340282366884865394519992635509523156085),(6262,6265,45337152693174925016912194828092,340282366886272953243611018473231471462),(6266,6269,43568112612957281432071547396874,340282366887625589510713605329213619153),(6270,6273,41868099867265821349344547881258,340282366888925446376633799943860690993),(6274,6277,40234421033286063686555030555050,340282366890174583275424142501398088759),(6278,6281,38664487784633910536780490164602,340282366891374979282729882710430531144),(6282,6285,37155812790529137531173352065597,340282366892528536251346350187845347549),(6286,6289,35706005774981721943559829320278,340282366893637081824427956395969431566),(6290,6293,34312769729747362729805192006014,340282366894702372331122819322861366199),(6294,6297,32973897275052171603495158553169,340282366895726095569220722603948986296),(6298,6301,31687267162320632998036552399187,340282366896709873479223109853146325154),(6302,6305,30450840913365914280915131587075,340282366897655264714071788986332962458),(6306,6309,29262659590717812322206149856250,340282366898563767108607707729512356227),(6310,6313,28120840693971391021456999628754,340282366899436820052672298392755518021),(6314,6317,27023575177239025843708789502699,340282366900275806771611225663699978243),(6318,6321,25969124582980442141202962981758,340282366901082056517793663756500005241),(6322,6325,24955818287669718033474580769449,340282366901856846676619246307157317236),(6326,6329,23982050854935412014676534611326,340282366902601404790349350567141201014),(6330,6333,23046279491980250983922822487803,340282366903316910502969182062874033889),(6334,6337,22147021605250445828978520357425,340282366904004497429162010683371885781),(6338,6341,21282852451481948285956076949410,340282366904665254950356675905253792513),(6342,6345,20452402880402073682145504080279,340282366905300229940693937071373944915),(6346,6349,19654357165510128758917144745847,340282366905910428425646211247330803281),(6350,6353,18887450919500232138176312376355,340282366906496817175918540272813665264),(6354,6357,18150469091023618233199305446031,340282366907060325239156091150099696464),(6358,6361,17442244039616585979905368081400,340282366907601845411884957414305262229),(6362,6365,16761653685744095854392650362168,340282366908122235654018337492482710118),(6366,6369,16107619733028028456658215608998,340282366908622320448169169256217166503),(6370,6373,15479105959843484032565101886354,340282366909102892105922853833825565672),(6374,6377,14875116577576405872744140094515,340282366909564712023139667727910405080),(6378,6381,14294694652941425694433120716607,340282366910008511886275707242196765950),(6382,6385,13736920591860323212124774261255,340282366910434994831633605213670430431),(6386,6389,13200910682499025937949993351702,340282366910844836559379684119779647214),(6390,6393,12685815695154803351132572852283,340282366911238686404092543631160173974),(6394,6397,12190819536775380436149359882135,340282366911617168363539211063645396436),(6398,6401,11715137957978251915586371690164,340282366911980882087308800835344644897),(6402,6405,11258017310521657432000835447639,340282366912330403826870029099013596606),(6406,6409,10818733353258611248289188744948,340282366912666287348557811431957856266),(6410,6413,10396590104682194380828100734445,340282366912989064810935437992270899515),(6414,6417,9990918740244134155151007667600,340282366913299247607922378836668609696),(6418,6421,9601076532699632932560972610129,340282366913597327179023532717862773248),(6422,6425,9226445833799576586833422456376,340282366913883775787943609703914521744),(6426,6429,8866433095716762216622077457087,340282366914159047270820248807055925644),(6430,6433,8520467930655737350677783239647,340282366914423577755261337116086566320),(6434,6437,8188002207156339279028708758913,340282366914677786351325740432224701013),(6438,6441,7868509181659158971556056908634,340282366914922075815542203826535601942),(6442,6445,7561482663957021433692204307991,340282366915156833189018463440709970662),(6446,6449,7266436215210261811015127942848,340282366915382430410651560562999907561),(6450,6453,6982902377255169150285253987103,340282366915599224906410900489327826381),(6454,6457,6710431931984549194928870192517,340282366915807560155627689425522603124),(6458,6461,6448593189627002489572253515069,340282366916007766235187952638610525727),(6462,6465,6196971304797299877378190686647,340282366916200160342491328504986365085),(6466,6469,5955167619234236736583583496518,340282366916385047298004190565142984468),(6470,6473,5722799030184629729212348025180,340282366916562720028203319876740216717),(6474,6477,5499497383432752415793927245370,340282366916733460029675281638253352005),(6478,6481,5284908890013553201466067044437,340282366916897537815106804011027156027),(6482,6485,5078693565685522585547279454014,340282366917055213341872765995715072060),(6486,6489,4880524692275136039065695560806,340282366917206736423900829662976854025),(6490,6493,4690088300039451163623418634343,340282366917352347127465256314822816030),(6494,6497,4507082670226737991931646154566,340282366917492276151536984283510887879),(6498,6501,4331217857047022134703907353352,340282366917626745193292577718796681030),(6502,6505,4162215228295172661023963720216,340282366917755967299361142105057111788),(6506,6509,3999807023898718842169331752062,340282366917880147203365706133462528714),(6510,6513,3843735931690979013399469556207,340282366917999481650293855130702522941),(6514,6517,3693754679737375808689675870274,340282366918114159708211534111432180351),(6518,6521,3549625644569038138426620007234,340282366918224363067813885615660630720),(6522,6525,3411120474702993061142076520764,340282366918330266330287717043840933782),(6526,6529,3278019728852470077587031901563,340282366918432037283941673680218207652),(6530,6533,3150112528254114720917740747091,340282366918529837170042397659147785168),(6534,6537,3027196222561274505292114670105,340282366918623820938277851584536346293),(6538,6541,2909076068774013762730084684283,340282366918714137492252551264377634936),(6542,6545,2795564922697168697946959366689,340282366918800929925403659032875748491),(6546,6549,2686482942437602847549049293678,340282366918884335747711712380179410674),(6550,6553,2581657303470897491111003208298,340282366918964487103565178048934292930),(6554,6557,2480921924826041647783966552558,340282366919041510981124006280583027645),(6558,6561,2384117205954301144566958330824,340282366919115529413513891297121388588),(6562,6565,2291089773865373769381263801611,340282366919186659672170001046821815883),(6566,6569,2201692240130204542822455394546,340282366919255014452636501218871342480),(6570,6573,2115782967365467429654105786644,340282366919320702053116245835701645293),(6574,6577,2033225844829742131835630526394,340282366919383826546053520425706639424),(6578,6581,1953890072775850759825181267939,340282366919444487943021685664667225528),(6582,6585,1877649955217692040053911831398,340282366919502782353176961963247495369),(6586,6589,1804384700783242263360018986855,340282366919558802135529401964492800816),(6590,6593,1733978231338203533695799410628,340282366919612636045272302149208892239),(6594,6597,1666318998077091336305536061338,340282366919664369374401891208466977765),(6598,6601,1601299804790384515532989404239,340282366919714084086850086616879910486),(6602,6605,1538817638027730179064934993128,340282366919761858948344417595301695274),(6606,6609,1478773503888121840953635180714,340282366919807769651200858614034445293),(6610,6613,1421072271178468590519495673205,340282366919851888934247289521726940172),(6614,6617,1365622520692062863105337901979,340282366919894286698067583571614846024),(6618,6621,1312336400368150477437942894319,340282366919935030115748910832585045294),(6622,6625,1261129486103124355092522557470,340282366919974183739307719971683211244),(6626,6629,1211920647992817512871704729900,340282366920011809601963014889389866967),(6630,6633,1164631921793975705390280717735,340282366920047967316418963331974338387),(6634,6637,1119188385401259125832391053091,340282366920082714169312551972464462407),(6638,6641,1075518040144068948794836042474,340282366920116105211975926525951070650),(6642,6645,1033551696715130810225146107667,340282366920148193347657216619659827590),(6646,6649,993222865550105664329648419928,340282366920179029415338034122668255301),(6650,6653,954467651484550462504606742701,340282366920208662270280441564485078312),(6654,6657,917224652521327937708607083593,340282366920237138861431005592983126297),(6658,6661,881434862548077186160955773746,340282366920264504305804570930770021800),(6662,6665,847041577850615034782496920943,340282366920290801959965605095713221954),(6666,6669,813990307274152282752107519692,340282366920316073488720365674565114092),(6670,6673,782228685889988337400417589869,340282366920340358931128722892842499105),(6674,6677,751706392030901685070786523174,340282366920363696763940223607967924207),(6678,6681,722375067563790845924941729923,340282366920386123962554901938032619135),(6682,6685,694188241273249413986922585397,340282366920407676059605420059776830872),(6686,6689,667101255234687606082665956089,340282366920428387201253354053173811667),(6690,6693,641071194060349244745526164260,340282366920448290201288818065461233849),(6694,6697,616056816906124784917488607660,340282366920467416593119139776682990703),(6698,6701,592018492131435073863965417219,340282366920485796679728955657770895462),(6702,6705,568918134508663938229457156541,340282366920503459581690880522050348660),(6706,6709,546719144882657081274804194288,340282366920520433283302817289696913080),(6710,6713,525386352184686546878484731466,340282366920536744676925004818694196513),(6714,6717,504885957709010314959755662931,340282366920552419605587049402778860413),(6718,6721,485185481563741345720698945732,340282366920567482903932444577726018170),(6722,6725,466253711211185267026502180913,340282366920581958437565449869476871366),(6726,6729,448060652016116358254762232670,340282366920595869140862667887838008756),(6730,6733,430577479723642769985829895726,340282366920609237053309226707423123933),(6734,6737,413776494791369072262012420773,340282366920622083354417136929280826727),(6738,6741,397631078503502088428443035476,340282366920634428397281146478751717959),(6742,6745,382115650797369201401062288311,340282366920646291740825257508528444682),(6746,6749,367205629735531387584276451434,340282366920657692180790995320529310143),(6750,6753,352877392559280439044508824672,340282366920668647779516525709366525427),(6754,6757,339108238261815307673577795142,340282366920679175894553801405466538806),(6758,6761,325876351621800215505202401769,340282366920689293206169077322095010552),(6762,6765,313160768640320937745764021963,340282366920699015743770365170897814749),(6766,6769,300941343326479145266568809362,340282366920708358911303697902147624363),(6770,6773,289198715779001414060059992813,340282366920717337511658440655108772009),(6774,6777,277914281513292855809829132614,340282366920725965770120314882329122281),(6778,6781,267070161985338549492836504267,340282366920734257356909293551765875913),(6782,6785,256649176265752185111064971071,340282366920742225408838075442042037382),(6786,6789,246634813819093571541267625012,340282366920749882550125453231674196756),(6790,6793,237011208345327798171052238221,340282366920757240912397551135306299206),(6794,6797,227763112641981648880107850268,340282366920764312153908621137460242904),(6798,6801,218875874447170013192730105151,340282366920771107478011850378479546393),(6802,6805,210335413225219085204880293658,340282366920777637650909443999149241380),(6806,6809,202128197858106548335211867633,340282366920783913018710105867317224884),(6810,6813,194241225207374079151599528848,340282366920789943523820942282571845614),(6814,6817,186661999512546640245600753401,340282366920795738720699759245092123362),(6818,6821,179378512593418355408413958928,340282366920801307790992710511463158918),(6822,6825,172379224824838369985153102503,340282366920806659558081279838013260870),(6826,6829,165653046853854013098751274755,340282366920811802501061644988201469304),(6830,6833,159189322030244735553874402958,340282366920816744768178571772087501450),(6834,6837,152977809522610561104674585060,340282366920821494189735122168127232400),(6838,6841,147008668093264950136675511235,340282366920826058290498630081228327359),(6842,6845,141272440506225754537189906884,340282366920830444301622600200372010996),(6846,6849,135760038543600994327505913497,340282366920834659172103418469699729268),(6850,6853,130462728606630099693259795816,340282366920838709579790025663657898112),(6854,6857,125372117878567563556919020344,340282366920842601941963997291883863572),(6858,6861,120480141027486107378078449212,340282366920846342425506792430858933888),(6862,6865,115779047427931886768414864375,340282366920849936956670280008592821647),(6866,6869,111261388881186309063343763565,340282366920853391230466022519458110125),(6870,6873,106920007814679004613237809419,340282366920856710719688193122918775703),(6874,6877,102748025941855638835408494552,340282366920859900683584421625306216606),(6878,6881,98738833364533775759146358231,340282366920862966176188307038343824354),(6882,6885,94886078100481061724090759780,340282366920865912054326798368045319305),(6886,6889,91183656019623700781328682157,340282366920868742985315130163635358353),(6890,6893,87625701172940608581095783166,340282366920871463454351504332124329531),(6894,6897,84206576498720784846000913610,340282366920874077771623234015819255114),(6898,6901,80920864891459321635711276579,340282366920876590079135608183678675128),(6902,6905,77763360619242012757293984076,340282366920879004357274296278739369747),(6906,6909,74729061076020659152845263470,340282366920881324431111690096836125514),(6910,6913,71813158855711750671463646839,340282366920883553976467174377640267108),(6914,6917,69011034135561086941673083538,340282366920885696525730927724894946237),(6918,6921,66318247356706886937398101645,340282366920887755473460480820942192038),(6922,6925,63730532190344804588440997498,340282366920889734081758898867637251190),(6926,6929,61243788778350762446553514145,340282366920891635485443109201109884216),(6930,6933,58854077237652353892575826365,340282366920893462697010562543397728202),(6934,6937,56557611418057435597020067571,340282366920895218611412096842970381190),(6938,6941,54350752903650097982055698182,340282366920896906010638565612365814317),(6942,6945,52230005248250098500058344174,340282366920898527568128497608106858144),(6946,6949,50192008435802682040460659165,340282366920900085853003771148270367437),(6950,6953,48233533556922082243812090600,340282366920901583334140013877301854923),(6954,6957,46351477693154461555277007437,340282366920903022384078176934189832402),(6958,6961,44542859000855149073735558099,340282366920904405282783480844068074634),(6962,6965,42804811986891295060198315110,340282366920905734221257688636019829877),(6966,6969,41134582968684980428048047893,340282366920907011305010429308191326932),(6970,6973,39529525711403880163836816171,340282366920908238557395071447107836638),(6974,6977,37987097235387244148556390986,340282366920909417922814432207515159790),(6978,6981,36504853787164671937557103000,340282366920910551269801400632139357762),(6982,6985,35080446967684347033755042901,340282366920911640393979356110731255531),(6986,6989,33711620011616471700656854956,340282366920912687020907072330652316347),(6990,6993,32396204211837000032948993686,340282366920913692808812614055329180523),(6994,6997,31132115483426784058759290853,340282366920914659351220558192193369790),(6998,7001,29917351061742289517757375212,340282366920915588179476701599582496867),(7002,7005,28749986329326454851694618410,340282366920916480765174255664734645452),(7006,7009,27628171766632395402449600794,340282366920917338522485371605131750576),(7010,7013,26550130021728818248979840847,340282366920918162810401690455754962304),(7014,7017,25514153094344522321204432844,340282366920918954934887467567668274774),(7018,7021,24518599629790512071161856126,340282366920919716150948682930381813107),(7022,7025,23561892318472338071387843418,340282366920920447664621415522209455913),(7026,7029,22642515396872570259831925324,340282366920921150634882631978436299403),(7030,7033,21759012246044074210161774529,340282366920921826175486416943888088783),(7034,7037,20909983083809252484200761949,340282366920922475356728554349693193627),(7038,7041,20094082747008876589088640884,340282366920923099207142255336493258759),(7042,7045,19310018560286805534305639360,340282366920923698715127719458239306165),(7046,7049,18556548288033990503559215921,340282366920924274830518110969171545803),(7050,7053,17832478166246918944276618655,340282366920924828466084431255533155767),(7054,7057,17136661011182264177779421256,340282366920925360498981671663401284166),(7058,7061,16467994401811179045696182985,340282366920925871772138537941350884225),(7062,7065,15825418933193596905028439190,340282366920926363095592948114101996398),(7066,7069,15207916538005265715849431707,340282366920926835247775419689193382191),(7070,7073,14614508873558219053806482743,340282366920927288976742379536956592131),(7074,7077,14044255771759152699984773981,340282366920927725001361350443827506398),(7078,7081,13496253749549891413530853087,340282366920928144012449892094624060861),(7082,7085,12969634577469955563145343911,340282366920928546673870100970041093380),(7086,7089,12463563904073323303016431689,340282366920928933623580403235181348336),(7090,7093,11977239934019976823860626569,340282366920929305474646307031900577735),(7094,7097,11509892157747861094500901038,340282366920929662816211715564892132705),(7098,7101,11060780130712605167167192675,340282366920930006214432339885753201624),(7102,7105,10629192300260889026525270333,340282366920930336213372690231761448238),(7106,7109,10214444878278807542290049731,340282366920930653335868067071610687925),(7110,7113,9815880757829106907141410815,340282366920930958084352917557483060920),(7114,7117,9432868472060862908976692119,340282366920931250941656869793715912834),(7118,7121,9064801193742144919253859226,340282366920931532371769706122525420222),(7122,7125,8711095773830570688704014533,340282366920931802820576487415641432131),(7126,7129,8371191817558506898992263669,340282366920932062716563993069320406431),(7130,7133,8044550796569106916080655569,340282366920932312471499595954109380384),(7134,7137,7730655195696494496576709876,340282366920932552481083647897930905686),(7138,7141,7429007693038290806294999647,340282366920932783125576409312353597851),(7142,7145,7139130372021428983629420808,340282366920933004770400516240812092034),(7146,7149,6860563964212889188875430923,340282366920933217766719939350145001660),(7150,7153,6592867121675697933237284875,340282366920933422451996352141724489834),(7154,7157,6335615717717345653162805778,340282366920933619150523789866646853119),(7158,7161,6088402174922760150773208896,340282366920933808173942446234233177608),(7162,7165,5850834819407201929553595412,340282366920933989821732421949958436528),(7166,7169,5622537260265989105263581881,340282366920934164381688207355518481332),(7170,7173,5403147793237880281917789151,340282366920934332130374650919732734941),(7174,7177,5192318827637306800228253158,340282366920934493333565135996005171762),(7178,7181,4989716335647511871714056875,340282366920934648246662660073653533718),(7182,7185,4795019323102081714747627078,340282366920934797115104483661906246637),(7186,7189,4607919320916399039003921461,340282366920934940174750989913840364129),(7190,7193,4428119896363266021821231941,340282366920935077652259371081748911293),(7194,7197,4255336183418384118874606240,340282366920935209765442733855748357215),(7198,7201,4089294431431591464724997783,340282366920935336723615192535779242279),(7202,7205,3929731571408793114995778061,340282366920935458727923496786914008773),(7206,7209,3776394799217420962077378561,340282366920935575971665719393892783047)]


def feeEntries : List (Nat × (Nat × Nat)) := feeRuns.toList.flatMap fun e =>
  (List.range' e.1 (e.2.1-e.1+1)).map fun i => (i, (e.2.2.1, e.2.2.2))

def fees : Array (Nat × Nat) := (feeEntries.map Prod.snd).toArray

def expectedRun (lo hi : Nat) : Nat × Nat :=
  let un := 734 * 101 ^ hi
  let ud := 2 ^ 66 * 100 ^ hi
  let ln := 734 * 101 ^ lo
  let ld := 2 ^ 66 * 100 ^ lo
  let lower := scale * ln * 100 ^ 13 / (ld * 101 ^ 13)
  let mgf := if un * 5 ≤ ud * 6 then
      ceilDiv ((expUpper (ceilDiv (6 * scale * un) ud) - scale) * ud) un
    else if ln * 100 ^ 13 * 5 ≥ ld * 101 ^ 13 * 6 then
      ceilDiv (scale * (capExp - scale)) lower
    else maxFee
  let res := ceilDiv (scale * (un * 5 - ud * 6)) (un * 5)
  (mgf, res)

def feeChunk (block : Nat) : Bool := (List.range 64).all fun j =>
  let i := 64 * block + j
  if i < feeRuns.size then
    let e := feeRuns[i]?.getD (0, 0, 0, 0)
    decide (e.1 ≤ e.2.1 ∧ (e.2.2.1, e.2.2.2) = expectedRun e.1 e.2.1 ∧
      e.2.2.1 ≤ maxFee ∧ e.2.2.2 ≤ scale)
  else true

theorem fee_runs_count : feeRuns.size = 1578 := by decide +kernel

theorem fee_count : fees.size = 7210 := by decide +kernel

theorem fee_indices : feeEntries.map Prod.fst = List.range 7210 := by decide +kernel

theorem max_fee_checked : maxFee = 379536990389944597429874025328168200988635 := by decide +kernel

theorem first_fee_chunk : feeChunk 0 = true := by decide +kernel

theorem fee_chunk_1 : feeChunk 1 = true := by decide +kernel

theorem fee_chunk_2 : feeChunk 2 = true := by decide +kernel

theorem fee_chunk_3 : feeChunk 3 = true := by decide +kernel

theorem fee_chunk_4 : feeChunk 4 = true := by decide +kernel

theorem fee_chunk_5 : feeChunk 5 = true := by decide +kernel

theorem fee_chunk_6 : feeChunk 6 = true := by decide +kernel

theorem fee_chunk_7 : feeChunk 7 = true := by decide +kernel

theorem fee_chunk_8 : feeChunk 8 = true := by decide +kernel

theorem fee_chunk_9 : feeChunk 9 = true := by decide +kernel

theorem fee_chunk_10 : feeChunk 10 = true := by decide +kernel

theorem fee_chunk_11 : feeChunk 11 = true := by decide +kernel

theorem fee_chunk_12 : feeChunk 12 = true := by decide +kernel

theorem fee_chunk_13 : feeChunk 13 = true := by decide +kernel

theorem fee_chunk_14 : feeChunk 14 = true := by decide +kernel

theorem fee_chunk_15 : feeChunk 15 = true := by decide +kernel

theorem fee_chunk_16 : feeChunk 16 = true := by decide +kernel

theorem fee_chunk_17 : feeChunk 17 = true := by decide +kernel

theorem fee_chunk_18 : feeChunk 18 = true := by decide +kernel

theorem fee_chunk_19 : feeChunk 19 = true := by decide +kernel

theorem fee_chunk_20 : feeChunk 20 = true := by decide +kernel

theorem fee_chunk_21 : feeChunk 21 = true := by decide +kernel

theorem fee_chunk_22 : feeChunk 22 = true := by decide +kernel

theorem fee_chunk_23 : feeChunk 23 = true := by decide +kernel

theorem fee_chunk_24 : feeChunk 24 = true := by decide +kernel

theorem fee_chunks : ∀ b : Fin 25, feeChunk b.val = true := by
  intro b
  fin_cases b
  · exact first_fee_chunk
  · exact fee_chunk_1
  · exact fee_chunk_2
  · exact fee_chunk_3
  · exact fee_chunk_4
  · exact fee_chunk_5
  · exact fee_chunk_6
  · exact fee_chunk_7
  · exact fee_chunk_8
  · exact fee_chunk_9
  · exact fee_chunk_10
  · exact fee_chunk_11
  · exact fee_chunk_12
  · exact fee_chunk_13
  · exact fee_chunk_14
  · exact fee_chunk_15
  · exact fee_chunk_16
  · exact fee_chunk_17
  · exact fee_chunk_18
  · exact fee_chunk_19
  · exact fee_chunk_20
  · exact fee_chunk_21
  · exact fee_chunk_22
  · exact fee_chunk_23
  · exact fee_chunk_24

#print axioms fee_chunks
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedMoments
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false

def paidDots : List (Nat × Nat) → Nat → Nat × Nat × Nat
  | (m,t) :: fs, p =>
    if p = 0 then (0,0,0) else
    let n := p &&& (2^4096-1)
    let v := paidDots fs (p >>> 4096)
    (n+v.1,n*m+v.2.1,n*t+v.2.2)
  | [], _ => (0,0,0)

def paidTree : Nat → List (Nat × Nat) → Nat → Nat × Nat × Nat
  | 0, fs, p => paidDots fs p
  | fuel+1, fs, p =>
    if p = 0 then (0,0,0) else
    let half := fs.length / 2
    let lower := p % 2^(4096*half)
    let higher := p >>> (4096*half)
    let a := paidTree fuel (fs.take half) lower
    let b := paidTree fuel (fs.drop half) higher
    (a.1+b.1,a.2.1+b.2.1,a.2.2+b.2.2)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
abbrev Cell := Nat × Nat

def bucket : List Nat → Nat → Nat → Cell
  | [], _, _ => (0,0)
  | b :: bs, c, p =>
    if p = 0 then (0,0) else
    let n := p &&& (2^512-1)
    let v := bucket bs (c+1) (p >>> 512)
    if n = 0 then v else
      ((n <<< (1024*b)) + v.1, ((c*n) <<< (1024*b)) + v.2)

def coordinate (K r : Nat) : Cell :=
  bucket (0 :: binPairs.map Prod.snd) 0 (coordinatePacked 512 K r)

def decode : Nat → Nat → Nat → List Cell
  | 0, _, _ => []
  | fuel+1, p, f =>
    if p = 0 then [] else
    (p &&& (2^1024-1),f &&& (2^1024-1)) :: decode fuel (p >>> 1024) (f >>> 1024)

def product (p : Cell) : List Cell := decode 2047 (p.1^2) (p.2^2)

def cellAdd (a b : Cell) : Cell := (a.1+b.1,a.2+b.2)
def cellSub (a b : Cell) : Cell := (a.1-b.1,a.2-b.2)
def cellScale (w : Nat) (a : Cell) : Cell := (w*a.1,w*a.2)
def cellCross (a b : Cell) : Cell := (a.1*b.1,a.2*b.1+a.1*b.2)

def plus : List Cell → List Cell → List Cell
  | [], bs => bs
  | as, [] => as
  | a::as,b::bs => cellAdd a b :: plus as bs

def prefixes : List Cell → Cell → List Cell
  | [], acc => [acc]
  | a::as, acc => acc :: prefixes as (cellAdd acc a)

def directed (lo hi shift : Nat) (a b : List Cell) : List Cell :=
  let pref := (prefixes (b ++ List.replicate (a.length-b.length) (0,0)) (0,0)).tail
  let win := List.zipWith cellSub
    (List.replicate lo (0,0) ++ pref)
    (List.replicate (hi+1) (0,0) ++ pref)
  List.replicate shift (0,0) ++ List.zipWith cellCross a win

-- Ranges inserted by the scratch generator.
def addRuns : List (Nat × Nat × Nat) := [(0,1,70),(2,3,69),(4,5,68),(6,7,67),(8,9,66),(10,11,65),(12,13,64),(14,15,63),(16,18,62),(19,20,61),(21,22,60),(23,24,59),(25,27,58),(28,29,57),(30,31,56),(32,34,55),(35,36,54),(37,39,53),(40,41,52),(42,44,51),(45,46,50),(47,49,49),(50,51,48),(52,54,47),(55,57,46),(58,60,45),(61,63,44),(64,65,43),(66,68,42),(69,71,41),(72,75,40),(76,78,39),(79,81,38),(82,84,37),(85,87,36),(88,91,35),(92,94,34),(95,98,33),(99,102,32),(103,106,31),(107,110,30),(111,114,29),(115,118,28),(119,122,27),(123,127,26),(128,131,25),(132,136,24),(137,141,23),(142,146,22),(147,152,21),(153,157,20),(158,163,19),(164,169,18),(170,176,17),(177,183,16),(184,191,15),(192,198,14),(199,207,13),(208,216,12),(217,226,11),(227,237,10),(238,250,9),(251,264,8),(265,280,7),(281,299,6),(300,321,5),(322,351,4),(352,392,3),(393,462,2),(463,2046,1)]

def add (a b : List Cell) : List Cell :=
  addRuns.foldl (fun acc e =>
    let forward := directed e.1 e.2.1 e.2.2 a b
    let reverse := if e.2.1 = 0 then [] else directed (max 1 e.1) e.2.1 e.2.2 b a
    plus acc (plus forward reverse)) []

def pair (r : Nat) : List Cell :=
  let branches := (List.range (r+1)).map fun t => product (coordinate 64 t)
  (List.range (r+1)).foldl (fun acc t =>
    let a := branches.getD t []
    let b := branches.getD (r-t) []
    let row := if t=0 then b else if r-t=0 then a else add a b
    let w := fact r / (fact t * fact (r-t))
    plus acc (row.map (cellScale w))) []

def packFirst (xs : List Cell) : Nat := xs.foldr (fun e acc => e.2 + (acc <<< 4096)) 0

def forest (r : Nat) : Nat :=
  packFirst (pair r)^4 * packFirst (decode 1024 (coordinate 128 r).1 (coordinate 128 r).2)
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate addRuns)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

def cutMask : Nat := (1 <<< (1024*2048))-1

def hadamard : Nat → Nat → Nat → Nat
  | 0, a, b => a*b
  | h+1, a, b =>
    if a = 0 ∨ b = 0 then 0 else
    let bits := 1024*(2^h)
    let mask := (1 <<< bits)-1
    hadamard h (a &&& mask) (b &&& mask) +
      (hadamard h (a >>> bits) (b >>> bits) <<< bits)

def spread : Nat → Nat → Nat
  | 0, a => a
  | h+1, a =>
    if a=0 then 0 else
    let bits := 1024*(2^h)
    spread h (a &&& ((1 <<< bits)-1)) +
      (spread h (a >>> bits) <<< (4096*(2^h)))

def prefixes (a : Nat) : Nat :=
  (a * (cutMask / ((1 <<< 1024)-1))) &&& cutMask

def window (a lo hi : Nat) : Nat :=
  ((a <<< (1024*lo)) &&& cutMask) - ((a <<< (1024*(hi+1))) &&& cutMask)

def directedFirst (a pref : Cell) (lo hi shift : Nat) : Nat :=
  ((hadamard 11 a.2 (window pref.1 lo hi) +
    hadamard 11 a.1 (window pref.2 lo hi)) <<< (1024*shift)) &&& cutMask

def addFirst (a b : Cell) : Nat :=
  let ap := (prefixes a.1, prefixes a.2)
  let bp := (prefixes b.1, prefixes b.2)
  addRuns.foldl (fun acc e => acc +
    directedFirst a bp e.1 e.2.1 e.2.2 +
    (if e.2.1=0 then 0 else directedFirst b ap (max 1 e.1) e.2.1 e.2.2)) 0

def product (a : Cell) : Cell := (a.1^2,a.2^2)

def pairFirst (r : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coordinate 64 t)
  (List.range (r+1)).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

def forest (r : Nat) : Nat :=
  (spread 11 (pairFirst r))^4 * spread 10 (coordinate 128 r).2
end ClaudeWCT.Numerics.SharedPathPacked

/-! Kernel-friendly evaluation of the packed paired-forest arithmetic.  The functions below compute
exactly the same natural numbers as `hadamard`, `spread`, `directedFirst`, `addFirst`, `pairFirst`
and `forest` (see the `*_eq_fast` theorems), but are written with an explicit `Nat.rec`, primitive
`Nat` operations (GMP-accelerated in the kernel) and one fused traversal for the two Hadamard
products of `directedFirst`, so that `decide +kernel` performs far fewer reduction steps. -/
namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate addRuns)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

/-- `had2 h a w c v = hadamard h a w + hadamard h c v` (theorem `had2_eq`). -/
def had2 (h : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun a w c v => Nat.add (Nat.mul a w) (Nat.mul c v))
    (fun h ih a w c v =>
      cond ((Nat.beq a 0 || Nat.beq w 0) && (Nat.beq c 0 || Nat.beq v 0)) 0
        (Nat.add
          (ih (Nat.land a (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1))
              (Nat.land w (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1))
              (Nat.land c (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1))
              (Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1)))
          (Nat.shiftLeft
            (ih (Nat.shiftRight a (Nat.mul 1024 (Nat.pow 2 h)))
                (Nat.shiftRight w (Nat.mul 1024 (Nat.pow 2 h)))
                (Nat.shiftRight c (Nat.mul 1024 (Nat.pow 2 h)))
                (Nat.shiftRight v (Nat.mul 1024 (Nat.pow 2 h))))
            (Nat.mul 1024 (Nat.pow 2 h))))) h

theorem hadamard_zero_left (h b : Nat) : hadamard h 0 b = 0 := by
  cases h with
  | zero => exact Nat.zero_mul b
  | succ h => rw [hadamard, if_pos (Or.inl rfl)]

theorem hadamard_zero_right (h a : Nat) : hadamard h a 0 = 0 := by
  cases h with
  | zero => exact Nat.mul_zero a
  | succ h => rw [hadamard, if_pos (Or.inr rfl)]

theorem hadamard_succ_split (h a b : Nat) :
    hadamard (h+1) a b =
      hadamard h (a &&& ((1 <<< (1024*2^h))-1)) (b &&& ((1 <<< (1024*2^h))-1)) +
        (hadamard h (a >>> (1024*2^h)) (b >>> (1024*2^h)) <<< (1024*2^h)) := by
  rw [hadamard]
  by_cases hz : a = 0 ∨ b = 0
  · rw [if_pos hz]
    rcases hz with rfl | rfl
    · simp only [Nat.zero_and, Nat.zero_shiftRight, hadamard_zero_left, Nat.zero_shiftLeft,
        Nat.add_zero]
    · simp only [Nat.zero_and, Nat.zero_shiftRight, hadamard_zero_right, Nat.zero_shiftLeft,
        Nat.add_zero]
  · rw [if_neg hz]

theorem had2_eq (h a w c v : Nat) : had2 h a w c v = hadamard h a w + hadamard h c v := by
  induction h generalizing a w c v with
  | zero => rfl
  | succ h ih =>
    cases hb : ((Nat.beq a 0 || Nat.beq w 0) && (Nat.beq c 0 || Nat.beq v 0)) with
    | true =>
      have e : had2 (h+1) a w c v = 0 := by
        show cond _ 0 _ = 0
        rw [hb]
        rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hb
      have h1 : hadamard (h+1) a w = 0 := by
        rcases hb.1 with h1 | h1
        · subst h1; exact hadamard_zero_left _ _
        · subst h1; exact hadamard_zero_right _ _
      have h2 : hadamard (h+1) c v = 0 := by
        rcases hb.2 with h2 | h2
        · subst h2; exact hadamard_zero_left _ _
        · subst h2; exact hadamard_zero_right _ _
      simp only [e, h1, h2, Nat.add_zero]
    | false =>
      have e : had2 (h+1) a w c v =
          had2 h (a &&& ((1 <<< (1024*2^h))-1)) (w &&& ((1 <<< (1024*2^h))-1))
              (c &&& ((1 <<< (1024*2^h))-1)) (v &&& ((1 <<< (1024*2^h))-1)) +
            (had2 h (a >>> (1024*2^h)) (w >>> (1024*2^h)) (c >>> (1024*2^h)) (v >>> (1024*2^h))
              <<< (1024*2^h)) := by
        show cond _ 0 _ = _
        rw [hb]
        rfl
      rw [e, ih, ih, hadamard_succ_split h a w, hadamard_succ_split h c v]
      simp only [Nat.shiftLeft_eq, Nat.add_mul]
      omega

/-- `spreadFast = spread` (theorem `spread_eq_fast`). -/
def spreadFast (h : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun h ih a =>
      cond (Nat.beq a 0) 0
        (Nat.add (ih (Nat.land a (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1)))
          (Nat.shiftLeft (ih (Nat.shiftRight a (Nat.mul 1024 (Nat.pow 2 h))))
            (Nat.mul 4096 (Nat.pow 2 h))))) h

theorem spread_eq_fast : spread = spreadFast := by
  funext h a
  induction h generalizing a with
  | zero => rfl
  | succ h ih =>
    rw [spread]
    by_cases hz : a = 0
    · subst hz
      rw [if_pos rfl]
      rfl
    · rw [if_neg hz]
      have hb : Nat.beq a 0 = false := by
        cases hc : Nat.beq a 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hc) hz
      have e : spreadFast (h+1) a =
          spreadFast h (a &&& ((1 <<< (1024*2^h))-1)) +
            (spreadFast h (a >>> (1024*2^h)) <<< (4096*2^h)) := by
        show cond _ 0 _ = _
        rw [hb]
        rfl
      rw [e]
      show spread h (a &&& ((1 <<< (1024*2^h))-1)) + (spread h (a >>> (1024*2^h)) <<< (4096*2^h)) = _
      rw [ih, ih]

def directedFirstFast (a pref : Cell) (lo hi shift : Nat) : Nat :=
  Nat.land (Nat.shiftLeft (had2 11 a.2 (window pref.1 lo hi) a.1 (window pref.2 lo hi))
    (Nat.mul 1024 shift)) cutMask

theorem directedFirst_eq_fast : directedFirst = directedFirstFast := by
  funext a pref lo hi shift
  unfold directedFirst directedFirstFast
  rw [had2_eq]
  rfl

def addFirstFast (a b : Cell) : Nat :=
  let ap := (prefixes a.1, prefixes a.2)
  let bp := (prefixes b.1, prefixes b.2)
  addRuns.foldl (fun acc e => acc +
    directedFirstFast a bp e.1 e.2.1 e.2.2 +
    (if e.2.1=0 then 0 else directedFirstFast b ap (max 1 e.1) e.2.1 e.2.2)) 0

theorem addFirst_eq_fast : addFirst = addFirstFast := by
  funext a b
  unfold addFirst addFirstFast
  rw [directedFirst_eq_fast]

def pairFirstFast (r : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coordinate 64 t)
  (List.range (r+1)).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirstFast a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

theorem pairFirst_eq_fast : pairFirst = pairFirstFast := by
  funext r
  unfold pairFirst pairFirstFast
  rw [addFirst_eq_fast]

def forestFast (r : Nat) : Nat :=
  (spreadFast 11 (pairFirstFast r))^4 * spreadFast 10 (coordinate 128 r).2

theorem forest_eq_fast : forest = forestFast := by
  funext r
  unfold forest forestFast
  rw [spread_eq_fast, pairFirst_eq_fast]

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false

def certifiedPayoff : Nat → Nat × Nat
  | 0 => (0,0)
  | 1 => (6701941673369549417326357257552673250106659135205158406257375974660698684415541248,0)
  | 2 => (15275568250522396109463584769678650139234349771341573027357569472028124329800048333654979997821202177129938063853104702808915968,26470994266056814356897687804534664909292969138957864448404223912208768321894490623229662441360539498077813739618304)
  | 3 => (3654314075048956541650548098032435241530529649133345299584258303726782379176835813298980912362969370328500466613870103868574137016289591771687976782140675087242750853120000,1297731794995600887037365272859993577421024033638903473641159726862973069787717590686016295451468718820281396699230626583133984369708516013214717224930754183561216)
  | 4 => (314906240154403436752534578873580793456315445195838548849807258060163458539769561436901042720057426336935985414875329648002419438622013614423690668470944930798332491776147745192497604010975521303032769512960205783040,2558733643812385324575731546304079302882648888291033927523758025460068872298241369018182040784395878359901073290804974498463503947098525079718411487842647803676304010584740298168123379004492238977701217566720)
  | 5 => (14910709112589913324766352345067781833278729399040680526156948969595591935256095607291422263704113370059180128855310444130188302713092951971428148982287732879787458718050225366917384921474069697073964169915201807776778162762803003750490354345184953536566263808,1149615644641955753124218617497295492331928301882240961691562552842784003428098615316959350503810251359299685381965158640693880696038711847654660164920308054318377089145804501084482257275089154068050312943609120241329706385043038805149247992422727680000)
  | 6 => (474097992729663181275354785814178458352721862437554663506371283375165034965861580567905567209103759095189356661708848503001715675447918783456591289576142714268024914843474131464519701948345599723263306522567925667954418664749213645335316255705975761387961794575964217918796336921666302084068279538679808,216084091385867356342697625620912877637244420718143830209207614480399458377728928084069310348570639576118620905686366518974944756591143697822247706347090455550085288143646932781240626947425231003634116036215545738213298226457491671703370822937194825276703446523345517990732073067581614506517725184)
  | 7 => (11354837172452373178593723842600954089013137315026124301089298331106519783833711483228335301619412229826220762286027192925601732142712944564623988742301127758794480600335428634078175951126344482301492998845703023354590038511602645120288517851364928608338648230721728258342461297277415684944423601283479414855790998072511885019498279955478159032320,22713542828572363343153616130863706975963256303695685541041026868882305889945438881613657543198610651677134279042254114582525425871640507670325876201437944371747164513167499847485176437992659060502739642764839818924310597980986051355495041622922631769634855932553812090978612533815344744620937335179863552827719126069713806812268645723406336)
  | 8 => (221332417750368166934669943044268157610167298533305776462209392053111249517664594006834016570913399302277150547298623890187395699199968843121606024953986140761225506797250709598276809876629954939009871727497265039561931488611764528091353956801041698331591234372891265407707151585518876459164217511268698959389033002036195988007142264993014157874006929627924209718389041490225602753755873280,1566980911553219536188497027209139997206186138725540259529784166164501629766872349956032921439203099138393030899759374960468514929760973615481761316414974314281970625766114326686006786212959021728287990237627654634945764936264849593544307761272651950301390634786888888052025802449006455778617859737484895988167954102079888730150456419131053370428487418148903929299811358931607040819200)
  | 9 => (3738672998173259637411169522234608590657222385181162994224695576430338827927060610440520790547572383273586210579600201562386781374745232565971863854178631964335425813119507326838074457814475005412830008288580330657035118432778010071750433866529802260663282025916533389508535672888101970901625593898949612099225428903165506237419822848465232526880489290782563977487679250023546835235366118753747853822781280809366855635445113883197440,78422951792143733848750924087342343522987341008086645100077573691206291611286360483258374853570206374763866591209754199252840186932257120589100565296504190452417616525046089073135791667919821689897996278914917229272157435185782950409523320326251800527000958835071255057754323915643315345351887052729633462589954895333293667777334279136182080250830636016036670357734576613261476549587565876869712853187321323715083281924110680064)
  | 10 => (58082178300330179586134447272563856500532738814611966668298055703390326000415437360773840728035122959077871545122500188078692657074429331205468567857752240107152755840290413409164938007115170109388211640956764267921338169934665934450332186143452186451980858114401971653099245227641357006538587185959228452077825803589342089432620946090674214757896203991111704662293351433373396224564182943842902266760258940976998421178041680259149742980819044254491884187216360465183639863296,3038912318511670186725706546087186313883540648123972226765536123959494356493488799409239731491186727006222890740844861181834653286111673201850801724318804313043166540910923931378037541347799227913399906194329941234507650964358982150372214065200811044768847790134768162040594946076141357826160178404394948782795692687093984454678499593304047016311447253825868066978107667900756453560668283605377052813961744090459029068586081209943612382230453451130534920299921793951465472)
  | 11 => (876432859935987335820003130828721772303485790394481966425679389641897312258998827073400622330386427344904141287815005311386512308797689186497098439055644104130225785161903649187185169772467627177081312524306329876109532659849740156959119578220143785438124207881409712054448087678418473535692673053037067678217225202431274877427517478985641350795979932312943384404355788817019557647981173997132758405896159676956827575385655727958955917977590168949270060936198123650258250115572467783453699732905439532803010051233021952,95357740417468611856789783161220992604380198441553770407565790976365583757332246448732391575522327348931260859977760548421639360266354845047237413112897264382753758493318247862018250307042122510462254368881335489973004204833897700663486991908128758879989147572455245925450724582205277411898177301558298338104807133840127589249075332705756133852087365551831239115443663044913065413098312453435164000843727072823651998940080172969091743651062578496957767192538111039080537571823106496694923790468726891138057446096896)
  | 12 => (13289933705982785446739601473946960207689951716733173575877892388147284445828230630572352482916371888006858879717988834753732134445559079974265819181060642579471951345583797790881434236988125587298440196006046053144842495395265969530526021075718745615279950746956764422660530002009493477840233565542366596338671753319764245465062171035680471191485433165891190788781708774683160679076276591626421841165827764690760258777570106312757432879781323300948272489750963999661953693664849369286634479970524611706959947407431110624821436530338589584464184286475858894389248,2504356822398098183117491184246760450134345206711899661524746803027343101848902074978062757842095800124439714516776340226179297218668104306257038635826686449170896584210377062858875588135167368074693836593625440110289078648088755895407162577360932060404299706880101894524925186329711376647745994735146191648271078248502784941457092083295164106393170378827325925057839967698293552049156243434359077234515891591675305307561503962601083067240248632077848613928917938287620775468429675446639752502031384422869729386117765686974352115442220166754442816578325053440)
  | 13 => (202176293154102417139102681797245597293914100036154720551947346020864245315400358246068751457863391473406008463599376466201431524104268902466866266416275037535086947133347337397756707149563801988663526890682948824095092369187776108512230585246681151118956911486973597978913566678148056826813385888954115488872042453406648680759783298125616783755255923048379854192152887070653897993044744648636529451884733824394879614759799265354395154339771565311579623353190448076226394491328130625891715142099063201304922992582371570574917727093607338206214188577454655958481615124259966996156771627735505290996238778368,56327004100701926381959919199557033152258450602506573136664491935426632792416956549656675551860077153644444060014642636197134995181337911490140008664007162107334406399580288597547095782075943670136913061984871922162342719075615840815949146310548995478922337306454482068537363052339635151684825306738779643799362628299819740736242136832993159316111379826866105555184542138340981470214308732666150935268207830712513576554801068377919704819309263006427727418975221617137769271235264877017624332019116831503922504150080969385547721131873618893463907200688473832600507220253519409725396529234955040746110976)
  | 14 => (3003986699548699880842826022155066240476289270806516557992149336767941542481265225164315346817673043461853853785695180233014964050842164563048788095438399930209206866230697725509780600984434220772419873489933994230862535802544873483766070304284688301014442909365698843053789875095654945734573713804200323903479107770920040170857378907134439580185729655435636568222921126999037999246877261195464300899605147134157347376839429588221221165845688893475897915981002279967658124047090860137707502142447704551862498823439244290915129569003206423374805252476391935588833420743181356013613646947055487471798156315026755291965002278961811158488981281915797504,1104736798390951919001611541924855522609168687681969031170768209726897974189673614647156060377177554892139185971016419471273519296016236692255141554052019939937272938857673646816730710997556075349100826751481752076807121963560115815266037039308033860894179378805067147436989580521253315293874149967195514568089936549094332239169403912284731316044826430486334255725643863953262345088291221552788248353163737985270853435504684495166008683213951734230742649930733956665589489807450954763123851208552195821582353911621415905670332883513157141230218040881364436657022099342300584458582851505471809579509307048500988176033644685665376780418240118521856)
  | 15 => (42245918587126749590192627346985922179255147471572727122177644057287981033840665377663192822516975441605217560071956117836611468277444683332466441756458458736334076676452961693429653874374552544806959752751178774070897700126045765700029025386306022733174773991729754000750310722011698251597406964524135350496491365748957633341822478296729276707504986166429188816865701863944052726430747795424618247898815701630967227338813864752448206544384625104542722673737080414585128734013375935940027900714851106937918435154372052572454502009585711714722765809394507247307253046037001565322592839601765840002192360071461193624557110761048262429679767947319935988487742537810488612842613710994565456986112,19133389897199997494373362305617979418208804613552145061450265294263813153801176602250000787850626363665252216817981797562899701234766605576244796579750646690163134048243273074067398261590318896320401746180153309062946557933528099277596459487325578356191470411910171878160044300389147564827790396723980373285272372975445593648483624314057001278818552216082856197808168299134224990363799432387347817857231327920906662364225630062775329720755882209971286869810625620193617152574885460196456485720820968768490905223392628980264818263943281805386179499124971002558949134007852774829437142226899828793558639968731441329792914049242620357920620820930681340298532409503991301196711408859864891392)
  | 16 => (550182242845413944842000056602729805919542143243043157893618686150351735514154892765580454910064950767526386269797948110634310254323610957434494583309597981580164717220358875954789365586914966910752182399190693814726210710957064493390099159898158141613788045197055657446442421317831901844966012377836435934365181505681171379414538508819437248888090821684191034673200202705254163013891680551335461165288633013266916069689681342347760681955643640245786123390531044843637420858671870024119590160921521710742461306462375748969681226946592044710202683254992106877307603782813424208924190650797223492100783938925376207881234613421284403322750197908555478020816301201464282634997911865986839648928357480434882630414485710939472406832480256000,295725162911772869456606828874172189283681232336696998541707805727536672434461884690523029898432923369376585337400996756966414671260653818934411802700009959315036422067048286172909389698320971405973232678698009203333195564354404816458947416047445632146287983141995395200367230176839493414231205643546147658783112547322440780838433744459183774558452211648830218497781168636336430741428318708362138479358350932352793977477926553468618153545962295497823966181105883664356472630795663498248040819781914256978166733833707711259879084553015582309291798212891090724321648021207575237876156597017995059801235100672583612246439791856546572234439177020032746404155154132703637221601974529630755232912136478611554752816920966184600267565039616)
  | 17 => (6555040808421832593650840811395543870888493598339745579467013113466137865804461001006640131704753124058304257850932531549453883262474855624711147387604349007103552065042649804650590184087569794082351963949508469064391110646239609449477079361952269142047029281973621717802130564586802389907386783136948391941637533649393847227444198803851029581389701752830838070646805340169724639982930658426016095574690370952244647939502641939965272791823395462986434378210248364438013920703935842902537293666645807536750903525459734332114664403719439023366544855798248038892469409619785506257513797411695977939827976744488090728953448431060383030723166280346231078464284597166136263531206896028023385165429005940450322104921266075868217734586265556174385769578890205921460872607825752966037504,4111981767394602006531972493315145942560586667478960475106431723018139239239836815461193958977388755915562154387246892794189686840211354557242123837701573972094787371544972140266474601063386457241493863022560505793355994096282802486214898071385470806215597178836713341281675006591183396255263204140572886562690465453817963107184921909810130187373291242145084363673482504045548062274015529378946437401784291894597974447483954978629786791698509786347353720149448219505160025238915664932869822316067008331731600421202350120439138116924248918346678357699788039010348359718887433785711744499915161186923018090896594322717837709931160217746722731307355963040612571855511321495321990927269923350771924975913619735449040103134438486353027114628373066118652952185234865885335605215232)
  | 18 => (71016209764664289202923697598090399040064299710695032210404295680963643264880271188233221950677520223406265198773748336642171889776317554871721489417330510475400551642987218609038733669352494996321618623499400206274666238746199234400831652482860712850165294991972105721703178498291608569391098326169646036522399576755102422130924507268397401926566582969327432465538814825812158727544456721307585827242667461124440930373928607493312106744893879474324708001555740871991383642718871065206110264644459220068224270142768737128255045238768040026976253423328355474271207272439903802632033310196543958042836183419294963483938325140906130305601976433920413674106429241215650424135341667596480809373388911553260925680120334948020150569905677107542120443598717745583987115623031219929476897638904695814148147398548134720576298156032,51765188934109154582632900168916829450991828308224720910489606010999801645115189189967744620090301175988935626021266525972929846391837436615399106877885601130236248938916977659776363831712080350435914793286136769616710758733636091398178078589382418099365206746501141457553320192069326981206494154320595741998972795993004463291028971550113862660926545093295779389037038892396749908446507541194830388151771047075572594444470623482832358458884119957732069217373557135838626139413956794724962363530973291266018604176934652399544172160873390505360124655087466768086433399812912953347037174148655756360406233344343421999051385892334354611012705414676653532668997640751080795854652091306614397052762093277161198496421825501956798176008897547270912601277744914236534680625962604707685648995135683033208903868746088512969768960)
  | r => (maxFee*forestMoment r, scale*forestMoment r)

def sharedMGFCheck : Bool :=
  poissonCheckQ fieldSize 13533529 100000000 2013623 1000000
    (fun r => 16^r * (certifiedPayoff r).1)
    (maxFee*alphabetSize) (maxFee*priceScaleTotal) scale 69 10 80

def sharedResidualCheck : Bool :=
  poissonCheckQ fieldSize 13533529 100000000 2013623 1000000
    (fun r => 16^r * (certifiedPayoff r).2)
    (scale*alphabetSize) priceScaleTotal 1 193 250000 80

theorem shared_mgf_checked : sharedMGFCheck = true := by decide +kernel

theorem shared_residual_checked : sharedResidualCheck = true := by decide +kernel

#print axioms shared_mgf_checked
#print axioms shared_residual_checked
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedMoments
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false

def rowDots (r : Nat) : Nat × Nat :=
  if r ≤ 20 then
    let p := paidTree 10 fees.toList (ClaudeWCT.Numerics.SharedPathPacked.forest r)
    let lost := forestMoment r - p.1
    (p.2.1 + maxFee*lost, p.2.2 + scale*lost)
  else (maxFee * forestMoment r, scale * forestMoment r)

/-- `rowDots` evaluated through `forestFast` (theorem `rowDots_eq_fast`). -/
def rowDotsFast (r : Nat) : Nat × Nat :=
  if r ≤ 20 then
    let p := paidTree 10 fees.toList (ClaudeWCT.Numerics.SharedPathPacked.forestFast r)
    let lost := forestMoment r - p.1
    (p.2.1 + maxFee*lost, p.2.2 + scale*lost)
  else (maxFee * forestMoment r, scale * forestMoment r)

theorem rowDots_eq_fast : rowDots = rowDotsFast := by
  funext r
  unfold rowDots rowDotsFast
  rw [ClaudeWCT.Numerics.SharedPathPacked.forest_eq_fast]

theorem row_4 : rowDots 4 = (314906240154403436752534578873580793456315445195838548849807258060163458539769561436901042720057426336935985414875329648002419438622013614423690668470944930798332491776147745192497604010975521303032769512960205783040,2558733643812385324575731546304079302882648888291033927523758025460068872298241369018182040784395878359901073290804974498463503947098525079718411487842647803676304010584740298168123379004492238977701217566720) := by
  rw [rowDots_eq_fast]; decide +kernel
#print axioms row_4
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option Elab.async false

def addEndpoint (d b : Nat) : Prop :=
  100^b*(101^d+100^d)≤101^(b+d) ∧
  100*101^(b+d)≤101*100^b*(101^d+100^d)
instance (d b : Nat) : Decidable (addEndpoint d b) := inferInstanceAs (Decidable (_ ∧ _))

def addRunsValid : Bool := addRuns.all fun e =>
  decide (e.1≤e.2.1 ∧ e.2.1<2047 ∧ e.2.2≤70 ∧
    addEndpoint e.1 e.2.2 ∧ addEndpoint e.2.1 e.2.2)

theorem addRuns_valid : addRunsValid=true := by decide +kernel

theorem addRuns_ordered : addRuns.Pairwise (fun a b => a.2.1<b.1) := by decide +kernel

#print axioms addRuns_valid
#print axioms addRuns_ordered
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
theorem row_0 : rowDots 0 = (0,0) := by
  rw [rowDots_eq_fast]; decide +kernel
#print axioms row_0
theorem row_1 : rowDots 1 = (6701941673369549417326357257552673250106659135205158406257375974660698684415541248,0) := by
  rw [rowDots_eq_fast]; decide +kernel
#print axioms row_1
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
theorem row_2 : rowDots 2 = (15275568250522396109463584769678650139234349771341573027357569472028124329800048333654979997821202177129938063853104702808915968,26470994266056814356897687804534664909292969138957864448404223912208768321894490623229662441360539498077813739618304) := by
  rw [rowDots_eq_fast]; decide +kernel
#print axioms row_2
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
theorem row_3 : rowDots 3 = (3654314075048956541650548098032435241530529649133345299584258303726782379176835813298980912362969370328500466613870103868574137016289591771687976782140675087242750853120000,1297731794995600887037365272859993577421024033638903473641159726862973069787717590686016295451468718820281396699230626583133984369708516013214717224930754183561216) := by
  rw [rowDots_eq_fast]; decide +kernel
#print axioms row_3
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000

theorem ceilDiv_mul_ge (n d : Nat) (hd : 0<d) : n≤ceilDiv n d*d := by
  have hm := Nat.mod_lt (n+d-1) hd
  have he := Nat.div_add_mod (n+d-1) d
  unfold ceilDiv
  rw [Nat.mul_comm]
  omega

theorem ceilDiv_ratio_le (n d : Nat) (hd : 0<d) : (n:ℝ)/(d:ℝ)≤ceilDiv n d := by
  apply (div_le_iff₀ (by exact_mod_cast hd : (0:ℝ)<d)).mpr
  exact_mod_cast ceilDiv_mul_ge n d hd

theorem mulUp_ratio_ge (a b : Nat) :
    ((a:ℝ)/scale)*((b:ℝ)/scale)≤(mulUp a b:ℝ)/scale := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have h := ceilDiv_ratio_le (a*b) scale (by norm_num [scale])
  unfold mulUp
  calc
    ((a:ℝ)/scale)*((b:ℝ)/scale) = (((a*b:Nat):ℝ)/scale)/scale := by push_cast; ring
    _ ≤ (ceilDiv (a*b) scale:ℝ)/scale := div_le_div_of_nonneg_right h hs.le

theorem powerUp_ratio_ge (base exponent : Nat) :
    ((base:ℝ)/scale)^exponent≤(powerUp base exponent:ℝ)/scale := by
  induction exponent using Nat.strong_induction_on generalizing base with
  | h exponent ih =>
    rw [powerUp]
    split_ifs with hz heven
    · subst exponent
      norm_num [scale]
    · have hlt : exponent/2<exponent := Nat.div_lt_self (by omega) (by decide)
      have hb : ((base:ℝ)/scale)^2≤(mulUp base base:ℝ)/scale := by
        simpa only [pow_two] using mulUp_ratio_ge base base
      have hp : ((base:ℝ)/scale)^(2*(exponent/2))≤
          (powerUp (mulUp base base) (exponent/2):ℝ)/scale := by
        calc
          _ = (((base:ℝ)/scale)^2)^(exponent/2) := pow_mul _ _ _
          _ ≤ ((mulUp base base:ℝ)/scale)^(exponent/2) := by gcongr
          _ ≤ _ := ih (exponent/2) hlt (mulUp base base)
      have hd := Nat.div_add_mod exponent 2
      have hx : exponent=2*(exponent/2) := by omega
      calc
        _ = ((base:ℝ)/scale)^(2*(exponent/2)) := congrArg _ hx
        _ ≤ _ := hp
    · have hlt : exponent/2<exponent := Nat.div_lt_self (by omega) (by decide)
      have hb : ((base:ℝ)/scale)^2≤(mulUp base base:ℝ)/scale := by
        simpa only [pow_two] using mulUp_ratio_ge base base
      have hp : ((base:ℝ)/scale)^(2*(exponent/2))≤
          (powerUp (mulUp base base) (exponent/2):ℝ)/scale := by
        calc
          _ = (((base:ℝ)/scale)^2)^(exponent/2) := pow_mul _ _ _
          _ ≤ ((mulUp base base:ℝ)/scale)^(exponent/2) := by gcongr
          _ ≤ _ := ih (exponent/2) hlt (mulUp base base)
      have hd := Nat.div_add_mod exponent 2
      have hm := Nat.mod_lt exponent (by decide : 0<2)
      have hx : exponent=2*(exponent/2)+1 := by omega
      calc
        _ = ((base:ℝ)/scale)*((base:ℝ)/scale)^(2*(exponent/2)) := by
          conv_lhs => rw [hx,pow_add,pow_one]
          ring
        _ ≤ ((base:ℝ)/scale)*((powerUp (mulUp base base) (exponent/2):ℝ)/scale) := by gcongr
        _ ≤ _ := mulUp_ratio_ge base _
#print axioms powerUp_ratio_ge
end ClaudeWCT.Numerics.CanonicalCompression

/-
Research-only helper for the paired source snapshot 596b027f64ffce574a59e35adc77cc64c733c600.
NOT compiled or Lean-certified locally. No production candidate is changed.
Inserted into N600PriceChecks before the generated coordinate namespace.
The helper proposes expressions only; every existing decide +kernel proof stays intact.
-/
namespace ClaudeWCT.Numerics.BoundedNatExpr
open Lean Elab Term

/-- Leaves have at most 4096 bits; both subtrees retain their allocated bit offset.
The fuel makes failure explicit instead of emitting an oversized fallback literal. -/
def encodeAux : Nat → Nat → Option Expr
  | 0, _ => none
  | fuel+1, n => do
    if n >>> 4096 == 0 then
      return mkNatLit n
    else
      let limbs := n.log2 / 4096 + 1
      let k := 4096 * (limbs / 2)
      if k >= 1073741824 then none else do
        let hi ← encodeAux fuel (n >>> k)
        let lo ← encodeAux fuel (n &&& ((1 <<< k) - 1))
        return mkApp2 (mkConst ``Nat.add)
          (mkApp2 (mkConst ``Nat.shiftLeft) hi (mkNatLit k)) lo

/-- 64 balanced levels exceed the size needed by these generated caches.
Exhaustion is a hard elaboration error, never a giant literal fallback. -/
def encode (n : Nat) : TermElabM Expr :=
  match encodeAux 64 n with
  | some e => pure e
  | none => throwError "bounded Nat expression exceeded 64 levels"

/-- Build the very same bounded syntax directly from little-endian 4096-bit
limbs. This avoids materializing a giant Nat only to split it back into limbs.
Trimming high zero limbs at *each* recursive call matches `n.log2` in encodeAux.
The fee-vector proofs are unchanged; this is only a host-side proposal. -/
def encodeLimbsAux : Nat → Array Nat → Option Expr
  | 0, _ => none
  | fuel+1, raw => do
    let mut used := 0
    for i in [:raw.size] do
      if raw[i]?.getD 0 != 0 then
        used := i+1
    if used == 0 then
      return mkNatLit 0
    else if used == 1 then
      let n ← raw[0]?
      if n >>> 4096 == 0 then return mkNatLit n else none
    else
      let middle := used / 2
      let k := 4096 * middle
      if k >= 1073741824 then none else do
        let hi ← encodeLimbsAux fuel (raw.extract middle used)
        let lo ← encodeLimbsAux fuel (raw.extract 0 middle)
        return mkApp2 (mkConst ``Nat.add)
          (mkApp2 (mkConst ``Nat.shiftLeft) hi (mkNatLit k)) lo

/-- Checked direct-limb proposal, with the same fuel and literal bounds as encode. -/
def encodeLimbs (limbs : Array Nat) : TermElabM Expr :=
  match encodeLimbsAux 64 limbs with
  | some e => pure e
  | none => throwError "bounded Nat limbs exceeded size, literal, or depth bounds"

/-- Read exactly our syntax, without whnf/reduce/evalExpr or kernel normalization. -/
def decodeAux : Nat → Expr → Option Nat
  | 0, _ => none
  | fuel+1, e => do
    match e.nat? with
    | some n =>
      if n >>> 4096 == 0 then return n else none
    | none =>
      if !(e.getAppFn.isConstOf ``Nat.add) then none else do
        let args := e.getAppArgs
        if args.size != 2 then none else do
          let shifted ← args[0]?
          let loExpr ← args[1]?
          if !(shifted.getAppFn.isConstOf ``Nat.shiftLeft) then none else do
            let shiftArgs := shifted.getAppArgs
            if shiftArgs.size != 2 then none else do
              let hiExpr ← shiftArgs[0]?
              let kExpr ← shiftArgs[1]?
              let k ← kExpr.nat?
              -- A bound on malformed input, not a trusted arithmetic premise.
              if k == 0 || k % 4096 != 0 || k >= 1073741824 then none else do
                let hi ← decodeAux fuel hiExpr
                let lo ← decodeAux fuel loExpr
                return (hi <<< k) + lo

def decode (e : Expr) : Option Nat := decodeAux 64 e

/-- Coordinate caches must be literal pairs of Nat expressions of the expected form. -/
def decodePair (e : Expr) : Option (Nat × Nat) := do
  if !(e.getAppFn.isConstOf ``Prod.mk) then none else do
    let args := e.getAppArgs
    if args.size != 4 then none else do
      let t1 ← args[0]?
      let t2 ← args[1]?
      if !(t1.isConstOf ``Nat) || !(t2.isConstOf ``Nat) then none else do
        let x ← args[2]?
        let y ← args[3]?
        return (← decode x, ← decode y)

/-- Generated caches are transparent definitions, not arbitrary declarations. -/
def readNat (info : ConstantInfo) : Option Nat :=
  match info with
  | .defnInfo val => decode val.value
  | _ => none

def readPair (info : ConstantInfo) : Option (Nat × Nat) :=
  match info with
  | .defnInfo val => decodePair val.value
  | _ => none

end ClaudeWCT.Numerics.BoundedNatExpr

namespace ClaudeWCT.Numerics.SharedGeneratedCoordinate
open Lean Elab Command
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

elab "coordinate_numeral% " k:num r:num : term => do
  let value := ClaudeWCT.Numerics.SharedPathList.coordinate k.getNat r.getNat
  let first ← ClaudeWCT.Numerics.BoundedNatExpr.encode value.1
  let second ← ClaudeWCT.Numerics.BoundedNatExpr.encode value.2
  return mkApp4 (mkConst ``Prod.mk [0,0]) (mkConst ``Nat) (mkConst ``Nat)
    first second

elab "certify_coordinate " k:num r:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat × Nat := coordinate_numeral% $k $r))
  elabCommand (← `(theorem $proof :
    ClaudeWCT.Numerics.SharedPathList.coordinate $k $r = $cached := by decide +kernel))

certify_coordinate 64 0 Coordinate_64_0 coordinate_64_0_checked
#print axioms coordinate_64_0_checked
certify_coordinate 64 1 Coordinate_64_1 coordinate_64_1_checked
#print axioms coordinate_64_1_checked
certify_coordinate 64 2 Coordinate_64_2 coordinate_64_2_checked
#print axioms coordinate_64_2_checked
certify_coordinate 64 3 Coordinate_64_3 coordinate_64_3_checked
#print axioms coordinate_64_3_checked
certify_coordinate 64 4 Coordinate_64_4 coordinate_64_4_checked
#print axioms coordinate_64_4_checked
certify_coordinate 64 5 Coordinate_64_5 coordinate_64_5_checked
#print axioms coordinate_64_5_checked
certify_coordinate 64 6 Coordinate_64_6 coordinate_64_6_checked
#print axioms coordinate_64_6_checked
certify_coordinate 64 7 Coordinate_64_7 coordinate_64_7_checked
#print axioms coordinate_64_7_checked
certify_coordinate 64 8 Coordinate_64_8 coordinate_64_8_checked
#print axioms coordinate_64_8_checked
certify_coordinate 64 9 Coordinate_64_9 coordinate_64_9_checked
#print axioms coordinate_64_9_checked
certify_coordinate 64 10 Coordinate_64_10 coordinate_64_10_checked
#print axioms coordinate_64_10_checked
certify_coordinate 64 11 Coordinate_64_11 coordinate_64_11_checked
#print axioms coordinate_64_11_checked
certify_coordinate 64 12 Coordinate_64_12 coordinate_64_12_checked
#print axioms coordinate_64_12_checked
certify_coordinate 64 13 Coordinate_64_13 coordinate_64_13_checked
#print axioms coordinate_64_13_checked
certify_coordinate 64 14 Coordinate_64_14 coordinate_64_14_checked
#print axioms coordinate_64_14_checked
certify_coordinate 64 15 Coordinate_64_15 coordinate_64_15_checked
#print axioms coordinate_64_15_checked
certify_coordinate 64 16 Coordinate_64_16 coordinate_64_16_checked
#print axioms coordinate_64_16_checked
certify_coordinate 64 17 Coordinate_64_17 coordinate_64_17_checked
#print axioms coordinate_64_17_checked
certify_coordinate 64 18 Coordinate_64_18 coordinate_64_18_checked
#print axioms coordinate_64_18_checked
certify_coordinate 128 0 Coordinate_128_0 coordinate_128_0_checked
#print axioms coordinate_128_0_checked
certify_coordinate 128 1 Coordinate_128_1 coordinate_128_1_checked
#print axioms coordinate_128_1_checked
certify_coordinate 128 2 Coordinate_128_2 coordinate_128_2_checked
#print axioms coordinate_128_2_checked
certify_coordinate 128 3 Coordinate_128_3 coordinate_128_3_checked
#print axioms coordinate_128_3_checked
certify_coordinate 128 4 Coordinate_128_4 coordinate_128_4_checked
#print axioms coordinate_128_4_checked
certify_coordinate 128 5 Coordinate_128_5 coordinate_128_5_checked
#print axioms coordinate_128_5_checked
certify_coordinate 128 6 Coordinate_128_6 coordinate_128_6_checked
#print axioms coordinate_128_6_checked
certify_coordinate 128 7 Coordinate_128_7 coordinate_128_7_checked
#print axioms coordinate_128_7_checked
certify_coordinate 128 8 Coordinate_128_8 coordinate_128_8_checked
#print axioms coordinate_128_8_checked
certify_coordinate 128 9 Coordinate_128_9 coordinate_128_9_checked
#print axioms coordinate_128_9_checked
certify_coordinate 128 10 Coordinate_128_10 coordinate_128_10_checked
#print axioms coordinate_128_10_checked
certify_coordinate 128 11 Coordinate_128_11 coordinate_128_11_checked
#print axioms coordinate_128_11_checked
certify_coordinate 128 12 Coordinate_128_12 coordinate_128_12_checked
#print axioms coordinate_128_12_checked
certify_coordinate 128 13 Coordinate_128_13 coordinate_128_13_checked
#print axioms coordinate_128_13_checked
certify_coordinate 128 14 Coordinate_128_14 coordinate_128_14_checked
#print axioms coordinate_128_14_checked
certify_coordinate 128 15 Coordinate_128_15 coordinate_128_15_checked
#print axioms coordinate_128_15_checked
certify_coordinate 128 16 Coordinate_128_16 coordinate_128_16_checked
#print axioms coordinate_128_16_checked
certify_coordinate 128 17 Coordinate_128_17 coordinate_128_17_checked
#print axioms coordinate_128_17_checked
certify_coordinate 128 18 Coordinate_128_18 coordinate_128_18_checked
#print axioms coordinate_128_18_checked

end ClaudeWCT.Numerics.SharedGeneratedCoordinate


namespace ClaudeWCT.Numerics.CanonicalCompression
open ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ftsBound_ge_scale : scale ≤ ftsBound := by norm_num [scale,ftsBound]
theorem initialBound_ge_scale : scale ≤ initialBound := by norm_num [scale,initialBound]

theorem fts_ratio_step : ((zNum:ENNReal)/zDen)*
    ((1-(ftsNum:ENNReal)/ftsDen)*((ftsBound:ENNReal)/scale)+
      (1-(1-(ftsNum:ENNReal)/ftsDen)))≤(ftsBound:ENNReal)/scale := by
  have hp : (ftsNum:ENNReal)/ftsDen ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num [ftsDen]) (by simp only [scale,zDen,ftsDen]; finiteness)).mpr
    norm_num [ftsNum,ftsDen]
  have hf : 1-(ftsNum:ENNReal)/ftsDen ≤ 1 := tsub_le_self
  apply (ENNReal.toReal_le_toReal (by simp only [scale,zDen,ftsDen]; finiteness) (by simp only [scale,zDen,ftsDen]; finiteness)).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp only [scale,zDen,ftsDen]; finiteness) (by simp only [scale,zDen,ftsDen]; finiteness),
    ENNReal.toReal_mul,ENNReal.toReal_sub_of_le hp (by simp),
    ENNReal.toReal_sub_of_le hf (by simp),ENNReal.toReal_sub_of_le hp (by simp)]
  norm_num [ENNReal.toReal_div,zNum,zDen,ftsNum,ftsDen,ftsBound,scale]

theorem fixed_ratio_bound : ((zNum:ℝ)/zDen)^112640≤(fixedBound:ℝ)/scale := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hz : (0:ℝ)<zDen := by norm_num [zDen]
  have hceil := ceilDiv_ratio_le (zNum*scale) zDen (by norm_num [zDen])
  have hc : ((zNum:ℝ)/zDen)≤(ceilDiv (zNum*scale) zDen:ℝ)/scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Nat.cast_mul,mul_div_assoc,div_mul_eq_mul_div] using hceil
  have hp := powerUp_ratio_ge (ceilDiv (zNum*scale) zDen) 112640
  calc
    _ ≤ ((ceilDiv (zNum*scale) zDen:ℝ)/scale)^112640 := by gcongr
    _ ≤ _ := hp.trans (div_le_div_of_nonneg_right (by exact_mod_cast fixed_power_checked) hs.le)

theorem envelope_ratio_le_two : ((fixedBound:ℝ)/scale)*
    (((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hmul := mulUp_ratio_ge fixedBound ftsBound
  have hmul2 := mulUp_ratio_ge (mulUp fixedBound ftsBound) initialBound
  have hnum : (mulUp (mulUp fixedBound ftsBound) initialBound:ℝ)/scale<199976/100000 := by
    have hn := full_moment_checked
    have hreal : (mulUp (mulUp fixedBound ftsBound) initialBound:ℝ)*100000<199976*(scale:ℝ) := by exact_mod_cast hn
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  calc
    _ = (((fixedBound:ℝ)/scale)*((ftsBound:ℝ)/scale))*((initialBound:ℝ)/scale) := by ring
    _ ≤ ((mulUp fixedBound ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale) := by gcongr
    _ ≤ _ := hmul2
    _ ≤ 2 := hnum.le.trans (by norm_num)
#print axioms fixed_ratio_bound
#print axioms envelope_ratio_le_two
end ClaudeWCT.Numerics.CanonicalCompression
