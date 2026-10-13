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
def A : Nat := 1418 * 2 ^ 24 * 563 ^ 9
def LN : Nat := 202893657
def LD : Nat := 100000000
def MN : Nat := 695
def MD : Nat := 1000
def DN : Nat := 3427
def DD : Nat := 1000000
def NN : Nat := 299
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
  let num := 1418 * 2^24 * 13533529 * LN^r
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
  | 1 => (4304737466716198511850267818490174064211728369504777804,0)
  | 2 => (350464637821611432538159751723592291174487825183961202340917482889766213185075038792661090339184702498,3760756779800306896986601668065735747779270902683954401537883603999489828682128588288)
  | 3 => (1895703581820066815846170570833272003517699205408934255080037955294235617529995195761058686985435283890130365603804752468778443243021592848397847030,74744019164127129337045859337351570675105325250975200693719717796095230633107201435448051329039154982397037527470607101254471414815488)
  | 4 => (3220580600471719335821782842701656566786932953433492684561139035110277084944694421348267093877095767019485500890446257695073880454141885482694221996079751313313804635668694723194375081676007502,12025809360209467619256641897977001527099233582756607410063098436297780029122234158775348956446159997036334511333509560368022566196718139029107793561643245673127381139461645355880960)
  | 5 => (2824453809055760360128888146751369152636578531845822258540121957167830848939287276159241690148046830370708167563607711203970228972749965069443030882424215289226342049959058569900104324634372854144822599984757023046220158957788597377671174,278653656786740642219383042348124170211908034711857027875919042023251624855405417616046346206881679622652685482793005424566608676831697447380219273261625763895287731913900404237691045301195815213464078232834834996857034700000000)
  | 6 => (1604244217318771028577368416808144302575418821097065512880393233602521718338061752682895669139877182875580937826728408457340201145606665816082609160688343547537391402757786152710506203528957515812820276321158680895464342246289938862622557801717137527544851338817486840209752105304918,2187659935032727100011529277022852211537492595011230328548897101780626411044819220205067532680782464784316058812285501114305948947275176060849513342312914700804117954693191238985370935364844428932168060632238464727430052698834902746230132987450834604277061280327823731388928)
  | 7 => (668277348543494892653166956857795510508818775414105867264171764714459151277913657251258313461516265714112347806313449521795461043760919071262294104348919256865558851273946105056976863804925255226230253042256955018617192913263725636952617915351969754539820723418480477835520613743909654947941559557503769132061599436531913563630,8387439663922501992272453284031994222450007504753882347418186980596018121323195361353877757292695396428469271919262054906327259423327325253165362366853796913695142228266273334369305403782773476914816041828456566924075272005821073859906576990653148736124077038817607642293508709583983529313298178571657646226254866330368)
  | 8 => (220532870042555279572181138510470358578213018582327256150629914240460737980351191918791571842775330578956327733407609088324979600887939006448766627835757755027806243848355593733788870205654322452344367880873442944964922713185728851969723241305978677830635400052232786152852265326620627406637946577610658368508783809200512727793479952253841436509048804558603378945593356942,19356783781223032941525715056301918593592384116225824836990691358553891282159107005319764737449511124127382493052982368389578356309673200913527684526521273858547316858751448141953947743093084350684011059361810008082276082316356478222119796094031030272893223637610048198352467641846313649696360797799726546692672604664072387253310698993822039626256292760709380293120)
  | 9 => (60860353284667646975131806839386509192134638228664972773010763927600892503779945254264985187078545382891124481271241500537761983379029092001314188013816226606911922366563085323764860702087579659687582459808296589238932902797771684078184499420032743490481923176681462596379579437577313346413344805094918617869054521768406535788041980805705504897785064535508376079043236539283012352060970722288456358063978588740006177,30145816349156440791749226463962178014964556900609982095597304453690329770990083101611489433375557037678042407853155322325690635323294840174901912934596402939385108172000081813329774614140278280563221147353216932348043652005692912685748875630144059458712856870510858116541382105625778430197726115971731771638896708802756753590010008851078467224606556562415918751156142158498338152699207780312581240692205960192)
  | 10 => (14727179314471729776550145315164934990745853071009276040329588685555381962707756260884221795054226494702579960966587406603807209981170873012216178405503420516035646318825218427450061640843748809561433802765601072077021694139140261553849164141447711137528767626660963777520506868524419152910507966192000709246736791410198930231607596681077279207517121266349133301872013445493139058586017179943437858469774321408922092782177579503203384809351594991753595453343827,33556320409097242480999436256055289897210600815629875889920542032259147450447277334421779840646456230533039207420297864359029733868990051213899358453491324548548663652905612993549417837147300869472313623962472048039204174098949207607021314103531615458823606571205617347167312186369890262438870463486804993939968192101145765022075962412721874005669212366542497869106824110719278360163568970977297715493927649542822292258307476446943144745161639531296986624)
  | 11 => (3314002644275427941304331221427937251138999551199524260036494443747267741901583987407519196820419904165053432926782496873497937147428850051100297272447932535175414641147964433853685858821561908880176484857716274044380483154757404052195725152371153874775245305777451140832340719120966761511075266854110693595062039033662511778267018166949700797847529496475672797854490486317060096864386524595504250264062614006348356323522220977384298455518405208445826424558995898901302950809062559217379885236858083494427,28782229095262601141843241443363218277535766800726039076999995488098859167951731837585726529398986021914137900683320059140293173742194777667279848576568882447666582195770981543103385922680570360717141335473898600238570526864982542940694281496135240934797544701596220709021160610366484550627684354011978565074983606167179194305242240942871712442151385893848443668335612149392628011179034624329354625711653107765771985517231533754640519909000280998641906687487074412424723234816041972764959739144112384)
  | 12 => (753921551262103985389105243975917101933913517239235250556931952213368848386758299188796756490926312783908238956079458843003683157561300268555409829829048772840824156576846554498706810783989621449697120430300280141924673150013661143726107510309146516920041735477749289979422548952232521637869364538640196308641958525161585863711775119845186204787221306705591498016441262554607009226168378658660785349514280344395433704181821436986717568335689973821311340582407423422774861611704208023046269773661925489895302534226064892308019964693891999484617060993,19565461180633981257688274516362507373947292744348971954210442443211902760517286324736841278924153450058352818068256514845824813593460264679508825766525600541491800409873655523157619326413773838489584629544423832635205362888513258546654033590307203913713924656186465206474269134102206636414674003752582111160002051104577549795743655723949953228996360389693412994567098182004445712339939354818847567222799290262242514101518380739638280339033795510186254975131789266567277753249079956458400148576906964257932430838343370179325656707306168308265472)
  | 13 => (187941116664077492431991328492712805135876886997217621836487303655189406846923335836054138501276894829792016899958661335638822952763031613027994676596595571996129197295457946659837691753332879623739726226263227717752307465121755346393392292115055024478829570775052877217984726440999363684466658426942728447772413970898891152569109605672188914682622927452666137006660402325183934755161546932981538631614356340278564552245839456235380200512473958008589724319646558739715387734184886811069821480313616230819330744699150531088851818051552072690981021952346251081012640900259155331175245851034646093,10766762360509737630741257406803966403735794381565783298961308113937767766293316992794299521265987137216356767885105171620020581195450247749428728756182760459317478785412481563624193995975024883669525193203903723695102011955697555496553653851169984467415618276609075431486174873878099817823964625881014109185420925315044933725014135634999056326127809081867276629829998070114034303057857214554583534891422901954446428698771470396596979194702632028765947932777608353516884793267512794963482728304245505925095414056727607097143760256715122547229662175986810667460854761507231686649181571189504)
  | 14 => (51637645232041433100699888876887273867025668304567949299456925777661300029290177171547680226576069401341836651858323750103719640340701302755536790112044298705088818805984670465889544928151310231705919323437045305638561651459743698877820533956727653481532902282442899330374305564120033012174623604529626801058497052293846136448500318043254089210576910120002599712664108736662435621279923300113604597491681058121022401819709779601453334161944333997416702804878882385874057961724387720978669166552566898279425522948173210889533115985870246431874471226796964510604866435060319920309108595275278452970148432454731744200204088801012153070215741,4932606926339103575498582616415740944245568001138868154852201180210942453806660469546500735323939295741280014489833069365037211941306996250926123012985810167439328580645557449732010239250535973463636899474211620515677001879979614424798397734471007301029974792072000629247569460848959395014884685576352156210626084387650751440345426961389765063087993851475319985346476938697705690086822738330846517020701943768062572066226937325660069132926416790432657825457929171961960989781899772915094106249496893138425592644550434950312438383070845128627384634106141969650285411618550774293778111668751070213970865968506981106460852803907103187456)
  | 15 => (14393334846907595542071702715409692205982835229731036053963625429918206949255484032372735314112998694559558005853680199717079434604755315658043330834648716373924475888598508290276896642277275119085045436744437023552703948758190434097794523663419256720216188970502326081061023060258698659153958466118224722132941623853142223775056303279011024688871251814876827307578549581337690876190770431541262256832118062290740890776719890146061783930341740405779103455323905450913128423678001079711346800433561890990405377691276182636070638479464392320187216378051326601025631996276725357094655746512006784767646346342556276967790228847343615478152750158831281848473839078804172822555047146811125,1895251228270237258820720846029617736937668104058899012510992930380791671535566713394353643600618158069036041291219453726735475027388189973623090054985971790579781813375914225588781546197335351638122000276763573845493355007206833567246582841931437251742960953269111791652423552596594495374919570823087065347851080478603882650291220054536753285464733818543833608625602403737668900387137421243699443491544214987972708331666151040326173004535515804406253503633080401542194090486819747965639359397173133087325869818832901739019999337839343162723020082003136409593249115231556216171356554717222360672109579802174178032880890833492580421454930831667953133752793290943858712451719329536)
  | 16 => (3787978316820465603430069641657514841491126863044193818813604890725310746091865274998449378297688726762475270411085566895622372341029120040296326081134128572125915007329406871896440007642290663995148310252718932838738186270606810833794463790192573820610843148720816983815837910034851913422155686779539115826910278728465270286066028582636474363769397625936614047553017497153051031756945215490787501884620401820204644300622681588194633195998172101318339630477392398007197559186488848452356762947107612812143367062330123957771895545267345714830022876089502235167710006122684882346944214378773952659374003571833342587273700647536492891594584874539429618937057492653507601221287498541441380151767321203298053777530463385742311424000,622700066615560873781206302401523756068266512945611525649318099127289367166287580863545634592837675468110652559641120956427694437012807758278334585081570998225243072216918774836142255081928204395664649528792842752687295322042382689572866118714708901082805046866904309519066579831086057693647242302051767371176141516364966319168249159690706087173289028911416714295145354519985200468393029970263908389185491292791423512670896612242868691654055762249407228357321707809767159808922600703527593569747179522036094929513994959238295501643600041057568709289057691361852828002366830061291010276260621446262501231130925717408391682527538233863954663769337066660856075251876297143847028283849154273073619576460917495048650359002103808)
  | 17 => (894748198672978553477392508437083855503734033187656681635599264985095498703180894551983189733452179049538421836432084014174250743032987553250982334148494562432076989562960945321779216473134896620671428383292752144333904965386126765342941645476071576726736356362778858166618647558639505234185853386932394020890345694465040501294252349786103466756073844683023660802914442558300330138104706178674953626809567814819968316116707943203475274710088222417042170409535202385935217492444425511785454276650139619928592749580072964486349368450558179946157013980879651446843012521579225920557958709874938849065043587442567238299905020424558765420226475662055983090109869532631083234679889476680762303847378865901571979865072334170544202040934077912530738711898230877632717505429504000,175641854666990956628488028097771104080162310363865782894500151585958344501369358121039086174785269361825073025091454118336621687183424102626853743068927464846425473234222024206299699387857986434548025251575064333668900983091785801323132180197393484669671730791521511811419318839766743445385539388374390161698484946032603076467371601478326525633812110749019302420064435985220682618771358916273952091103685103447257517947102003888577036958424242041033171110450472930116342104467195931512462780388249549242047986788904933532877548499581584991575624319636707653133015988583722321743880215368043512295901315883523514089861882784476109364699204255921441432736612924728290350540023752802033237338577566763260274733976297418004018622121870331278029372044201959210905835143168)
  | 18 => (187462945382714822331940461569373851522992143584912684754005217148167027379233049379812530160471890556016754185208229654250219849987564678064855921659355462011290630979896450926744817472110755411692372356591348448838555861654881771095924441709919314818135722170657297091071526244450055418755973305058463691085019014370275488979445906478571369596177599575381410728392267190025165465318193404799094088187836243525025714142062840155999559656779067226909362711293847774482941366594393079069458467809009016329893478813135862006242267085676993709584935397166917953672439510389578082489066935054887385603000456818809028719845431576995932418943002945501538773067323515016255743781436589695790529639353648201472727700776455785607295703615053268105250257046391423766230173346630087663316048996638397879935056216064000000000000,43063203080056038574711569476768857820447296351742799959888647920910034561415613485440646226314299665446465646414548828185277768437583173471343966706204925986617263152014083899310718740731193664536877036709771711695511776600130494870152286508364882561784455249800016824307877635450933562738767435295625061082446681953080424234547246252810789046461572264048075115717580628230600157436106322424574497259572176639558269098835827401666088533498896612524386480546196028654237331338562229171010892415125950270212878634437925849302316825562815845557085479963418792078074814295856047259043579108505652012205623674606100582217818043249491777040681255733321526677699735124239710669938084178904570557264418645241122007012474512380176310752388631559793535157886988550752552873530098831199654605652884626645018738688000000000)
  | 19 => (34949398767309750791180746066172498684490537717396080298973798932021751785458985452258268582752152427552250787713559017149748469229717121816762901540962371996288843583608684689248100067246723417379180871209280655791699265890317905819330103375702718620242122667937707146000337426047221783183343231997558325513083042360650741467780181266257477286874617482989415291291316925953559599001528828845283557346660725961199449994900784425076574585520722335472908243732750846824327126511618132561534801432569449306611732861676482276110086507156310973250371469732971474198440628534953152497962065548072354234300557592089174110608367862496870083283594957093209828263425310792562361668226686183231971863606340185094465959959454382395154845390941719925846464204846892277565278385931728452068724018223927509816595964667275500961776894234260576927327337148070419031442587648000,9266849324711034127331236327224653026061784998272300022124531670720785531620972715498773154110940732974053423715033120398342507783872395071662589926080056430019248726818873882362643812252197825908702825699296569017539441113081760824219673231377453374700632689809198517939176678175352566434946440589621660494328937846998794950004869586954106298180318517957084829572406452382540777483380224778576288637117324122969116402143568727430468994991434113894084557071000353122232646450158029050080618096185717072571232016279298638893058789110427302807957037380565789959811832209826222503066537397151863931619310352807093747301072348112225031816584111007088371621558609775520341208538103967390982600296368122032318121829474919008104952317583624125136985499902827658386138485045430029513482599743743407918910556479842763997575406368051079151477112382690139677147529216)
  | 20 => (5812903080121747874926199983955506657335898469518007703866117886026771125171041835590425615990952309211886619324031732574134558995406970646882269559451061717033975888758731224385913412384088211618849921817859013438702751295613326605679884840708293838544679950674745428474286701354389677452708789666556719825000695577480424524575391097452703245276307563442161226606987933371759352251369831273846659606990491719288421763908994973872038243447413925904940681222691882440653882301398040463952867429327739185435758344635474676700546695844767377083099204495546281558428610320860809380845111544412487613235519274927498170488529605639975178245139555455647695813637713746714189278683206919248238451562462278165463477604058406307879465117086679262707687289539421275129733362655391403409590667295078623486695424390413520761924845727864597846031993484553118451590381225590599649643206457753332103374242682769506304000,1757855689882122158647496884203411011557676135476974466166503247041100782879150300589918380778818551160754140468077165645866247843045612345528397714439692776079279182294525648687443922356474164337730571340811569003014657232936556602692188170049003188211972390777650112706674541647150596342700663313317022777643854719301386683436113443512104961667992826393868492803307909526778099834937658201408120764216946752365360444544494519483326970646361028629861367597441068584456634950061783978988409538152747326661557787854948251848821798352052943683080526133429593387918295247900120572315537812928944107065921595531888786479689884929634733904906536871183680307738064751167817491793370627659736245571655842394168396789027281858119520751123828662347961818101979645024800892138298174063695249049037268006694425566431561283193120757545728300331678443176019751159279855941280225401068819251110701124747560923168768)
  | r => (3000*winsorScale*xNum r^9,winsorScale*xNum r^9)
def winsorMGFFastCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => (winsorCertifiedDots r).1)
    (3000*winsorScale*Nn^9) (3000*A) 1 203 25 80
def winsorResidualFastCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => (winsorCertifiedDots r).2)
    (winsorScale*Nn^9) A 1 2097 10000000 80
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
theorem winsor_row_1 : winsorRowDots 1 = (4304737466716198511850267818490174064211728369504777804,0) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_2 : winsorRowDots 2 = (350464637821611432538159751723592291174487825183961202340917482889766213185075038792661090339184702498,3760756779800306896986601668065735747779270902683954401537883603999489828682128588288) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_3 : winsorRowDots 3 = (1895703581820066815846170570833272003517699205408934255080037955294235617529995195761058686985435283890130365603804752468778443243021592848397847030,74744019164127129337045859337351570675105325250975200693719717796095230633107201435448051329039154982397037527470607101254471414815488) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_4 : winsorRowDots 4 = (3220580600471719335821782842701656566786932953433492684561139035110277084944694421348267093877095767019485500890446257695073880454141885482694221996079751313313804635668694723194375081676007502,12025809360209467619256641897977001527099233582756607410063098436297780029122234158775348956446159997036334511333509560368022566196718139029107793561643245673127381139461645355880960) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_5 : winsorRowDots 5 = (2824453809055760360128888146751369152636578531845822258540121957167830848939287276159241690148046830370708167563607711203970228972749965069443030882424215289226342049959058569900104324634372854144822599984757023046220158957788597377671174,278653656786740642219383042348124170211908034711857027875919042023251624855405417616046346206881679622652685482793005424566608676831697447380219273261625763895287731913900404237691045301195815213464078232834834996857034700000000) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_6 : winsorRowDots 6 = (1604244217318771028577368416808144302575418821097065512880393233602521718338061752682895669139877182875580937826728408457340201145606665816082609160688343547537391402757786152710506203528957515812820276321158680895464342246289938862622557801717137527544851338817486840209752105304918,2187659935032727100011529277022852211537492595011230328548897101780626411044819220205067532680782464784316058812285501114305948947275176060849513342312914700804117954693191238985370935364844428932168060632238464727430052698834902746230132987450834604277061280327823731388928) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_7 : winsorRowDots 7 = (668277348543494892653166956857795510508818775414105867264171764714459151277913657251258313461516265714112347806313449521795461043760919071262294104348919256865558851273946105056976863804925255226230253042256955018617192913263725636952617915351969754539820723418480477835520613743909654947941559557503769132061599436531913563630,8387439663922501992272453284031994222450007504753882347418186980596018121323195361353877757292695396428469271919262054906327259423327325253165362366853796913695142228266273334369305403782773476914816041828456566924075272005821073859906576990653148736124077038817607642293508709583983529313298178571657646226254866330368) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_8 : winsorRowDots 8 = (220532870042555279572181138510470358578213018582327256150629914240460737980351191918791571842775330578956327733407609088324979600887939006448766627835757755027806243848355593733788870205654322452344367880873442944964922713185728851969723241305978677830635400052232786152852265326620627406637946577610658368508783809200512727793479952253841436509048804558603378945593356942,19356783781223032941525715056301918593592384116225824836990691358553891282159107005319764737449511124127382493052982368389578356309673200913527684526521273858547316858751448141953947743093084350684011059361810008082276082316356478222119796094031030272893223637610048198352467641846313649696360797799726546692672604664072387253310698993822039626256292760709380293120) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_9 : winsorRowDots 9 = (60860353284667646975131806839386509192134638228664972773010763927600892503779945254264985187078545382891124481271241500537761983379029092001314188013816226606911922366563085323764860702087579659687582459808296589238932902797771684078184499420032743490481923176681462596379579437577313346413344805094918617869054521768406535788041980805705504897785064535508376079043236539283012352060970722288456358063978588740006177,30145816349156440791749226463962178014964556900609982095597304453690329770990083101611489433375557037678042407853155322325690635323294840174901912934596402939385108172000081813329774614140278280563221147353216932348043652005692912685748875630144059458712856870510858116541382105625778430197726115971731771638896708802756753590010008851078467224606556562415918751156142158498338152699207780312581240692205960192) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_10 : winsorRowDots 10 = (14727179314471729776550145315164934990745853071009276040329588685555381962707756260884221795054226494702579960966587406603807209981170873012216178405503420516035646318825218427450061640843748809561433802765601072077021694139140261553849164141447711137528767626660963777520506868524419152910507966192000709246736791410198930231607596681077279207517121266349133301872013445493139058586017179943437858469774321408922092782177579503203384809351594991753595453343827,33556320409097242480999436256055289897210600815629875889920542032259147450447277334421779840646456230533039207420297864359029733868990051213899358453491324548548663652905612993549417837147300869472313623962472048039204174098949207607021314103531615458823606571205617347167312186369890262438870463486804993939968192101145765022075962412721874005669212366542497869106824110719278360163568970977297715493927649542822292258307476446943144745161639531296986624) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_11 : winsorRowDots 11 = (3314002644275427941304331221427937251138999551199524260036494443747267741901583987407519196820419904165053432926782496873497937147428850051100297272447932535175414641147964433853685858821561908880176484857716274044380483154757404052195725152371153874775245305777451140832340719120966761511075266854110693595062039033662511778267018166949700797847529496475672797854490486317060096864386524595504250264062614006348356323522220977384298455518405208445826424558995898901302950809062559217379885236858083494427,28782229095262601141843241443363218277535766800726039076999995488098859167951731837585726529398986021914137900683320059140293173742194777667279848576568882447666582195770981543103385922680570360717141335473898600238570526864982542940694281496135240934797544701596220709021160610366484550627684354011978565074983606167179194305242240942871712442151385893848443668335612149392628011179034624329354625711653107765771985517231533754640519909000280998641906687487074412424723234816041972764959739144112384) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_12 : winsorRowDots 12 = (753921551262103985389105243975917101933913517239235250556931952213368848386758299188796756490926312783908238956079458843003683157561300268555409829829048772840824156576846554498706810783989621449697120430300280141924673150013661143726107510309146516920041735477749289979422548952232521637869364538640196308641958525161585863711775119845186204787221306705591498016441262554607009226168378658660785349514280344395433704181821436986717568335689973821311340582407423422774861611704208023046269773661925489895302534226064892308019964693891999484617060993,19565461180633981257688274516362507373947292744348971954210442443211902760517286324736841278924153450058352818068256514845824813593460264679508825766525600541491800409873655523157619326413773838489584629544423832635205362888513258546654033590307203913713924656186465206474269134102206636414674003752582111160002051104577549795743655723949953228996360389693412994567098182004445712339939354818847567222799290262242514101518380739638280339033795510186254975131789266567277753249079956458400148576906964257932430838343370179325656707306168308265472) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_13 : winsorRowDots 13 = (187941116664077492431991328492712805135876886997217621836487303655189406846923335836054138501276894829792016899958661335638822952763031613027994676596595571996129197295457946659837691753332879623739726226263227717752307465121755346393392292115055024478829570775052877217984726440999363684466658426942728447772413970898891152569109605672188914682622927452666137006660402325183934755161546932981538631614356340278564552245839456235380200512473958008589724319646558739715387734184886811069821480313616230819330744699150531088851818051552072690981021952346251081012640900259155331175245851034646093,10766762360509737630741257406803966403735794381565783298961308113937767766293316992794299521265987137216356767885105171620020581195450247749428728756182760459317478785412481563624193995975024883669525193203903723695102011955697555496553653851169984467415618276609075431486174873878099817823964625881014109185420925315044933725014135634999056326127809081867276629829998070114034303057857214554583534891422901954446428698771470396596979194702632028765947932777608353516884793267512794963482728304245505925095414056727607097143760256715122547229662175986810667460854761507231686649181571189504) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_14 : winsorRowDots 14 = (51637645232041433100699888876887273867025668304567949299456925777661300029290177171547680226576069401341836651858323750103719640340701302755536790112044298705088818805984670465889544928151310231705919323437045305638561651459743698877820533956727653481532902282442899330374305564120033012174623604529626801058497052293846136448500318043254089210576910120002599712664108736662435621279923300113604597491681058121022401819709779601453334161944333997416702804878882385874057961724387720978669166552566898279425522948173210889533115985870246431874471226796964510604866435060319920309108595275278452970148432454731744200204088801012153070215741,4932606926339103575498582616415740944245568001138868154852201180210942453806660469546500735323939295741280014489833069365037211941306996250926123012985810167439328580645557449732010239250535973463636899474211620515677001879979614424798397734471007301029974792072000629247569460848959395014884685576352156210626084387650751440345426961389765063087993851475319985346476938697705690086822738330846517020701943768062572066226937325660069132926416790432657825457929171961960989781899772915094106249496893138425592644550434950312438383070845128627384634106141969650285411618550774293778111668751070213970865968506981106460852803907103187456) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_15 : winsorRowDots 15 = (14393334846907595542071702715409692205982835229731036053963625429918206949255484032372735314112998694559558005853680199717079434604755315658043330834648716373924475888598508290276896642277275119085045436744437023552703948758190434097794523663419256720216188970502326081061023060258698659153958466118224722132941623853142223775056303279011024688871251814876827307578549581337690876190770431541262256832118062290740890776719890146061783930341740405779103455323905450913128423678001079711346800433561890990405377691276182636070638479464392320187216378051326601025631996276725357094655746512006784767646346342556276967790228847343615478152750158831281848473839078804172822555047146811125,1895251228270237258820720846029617736937668104058899012510992930380791671535566713394353643600618158069036041291219453726735475027388189973623090054985971790579781813375914225588781546197335351638122000276763573845493355007206833567246582841931437251742960953269111791652423552596594495374919570823087065347851080478603882650291220054536753285464733818543833608625602403737668900387137421243699443491544214987972708331666151040326173004535515804406253503633080401542194090486819747965639359397173133087325869818832901739019999337839343162723020082003136409593249115231556216171356554717222360672109579802174178032880890833492580421454930831667953133752793290943858712451719329536) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_16 : winsorRowDots 16 = (3787978316820465603430069641657514841491126863044193818813604890725310746091865274998449378297688726762475270411085566895622372341029120040296326081134128572125915007329406871896440007642290663995148310252718932838738186270606810833794463790192573820610843148720816983815837910034851913422155686779539115826910278728465270286066028582636474363769397625936614047553017497153051031756945215490787501884620401820204644300622681588194633195998172101318339630477392398007197559186488848452356762947107612812143367062330123957771895545267345714830022876089502235167710006122684882346944214378773952659374003571833342587273700647536492891594584874539429618937057492653507601221287498541441380151767321203298053777530463385742311424000,622700066615560873781206302401523756068266512945611525649318099127289367166287580863545634592837675468110652559641120956427694437012807758278334585081570998225243072216918774836142255081928204395664649528792842752687295322042382689572866118714708901082805046866904309519066579831086057693647242302051767371176141516364966319168249159690706087173289028911416714295145354519985200468393029970263908389185491292791423512670896612242868691654055762249407228357321707809767159808922600703527593569747179522036094929513994959238295501643600041057568709289057691361852828002366830061291010276260621446262501231130925717408391682527538233863954663769337066660856075251876297143847028283849154273073619576460917495048650359002103808) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_17 : winsorRowDots 17 = (894748198672978553477392508437083855503734033187656681635599264985095498703180894551983189733452179049538421836432084014174250743032987553250982334148494562432076989562960945321779216473134896620671428383292752144333904965386126765342941645476071576726736356362778858166618647558639505234185853386932394020890345694465040501294252349786103466756073844683023660802914442558300330138104706178674953626809567814819968316116707943203475274710088222417042170409535202385935217492444425511785454276650139619928592749580072964486349368450558179946157013980879651446843012521579225920557958709874938849065043587442567238299905020424558765420226475662055983090109869532631083234679889476680762303847378865901571979865072334170544202040934077912530738711898230877632717505429504000,175641854666990956628488028097771104080162310363865782894500151585958344501369358121039086174785269361825073025091454118336621687183424102626853743068927464846425473234222024206299699387857986434548025251575064333668900983091785801323132180197393484669671730791521511811419318839766743445385539388374390161698484946032603076467371601478326525633812110749019302420064435985220682618771358916273952091103685103447257517947102003888577036958424242041033171110450472930116342104467195931512462780388249549242047986788904933532877548499581584991575624319636707653133015988583722321743880215368043512295901315883523514089861882784476109364699204255921441432736612924728290350540023752802033237338577566763260274733976297418004018622121870331278029372044201959210905835143168) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_18 : winsorRowDots 18 = (187462945382714822331940461569373851522992143584912684754005217148167027379233049379812530160471890556016754185208229654250219849987564678064855921659355462011290630979896450926744817472110755411692372356591348448838555861654881771095924441709919314818135722170657297091071526244450055418755973305058463691085019014370275488979445906478571369596177599575381410728392267190025165465318193404799094088187836243525025714142062840155999559656779067226909362711293847774482941366594393079069458467809009016329893478813135862006242267085676993709584935397166917953672439510389578082489066935054887385603000456818809028719845431576995932418943002945501538773067323515016255743781436589695790529639353648201472727700776455785607295703615053268105250257046391423766230173346630087663316048996638397879935056216064000000000000,43063203080056038574711569476768857820447296351742799959888647920910034561415613485440646226314299665446465646414548828185277768437583173471343966706204925986617263152014083899310718740731193664536877036709771711695511776600130494870152286508364882561784455249800016824307877635450933562738767435295625061082446681953080424234547246252810789046461572264048075115717580628230600157436106322424574497259572176639558269098835827401666088533498896612524386480546196028654237331338562229171010892415125950270212878634437925849302316825562815845557085479963418792078074814295856047259043579108505652012205623674606100582217818043249491777040681255733321526677699735124239710669938084178904570557264418645241122007012474512380176310752388631559793535157886988550752552873530098831199654605652884626645018738688000000000) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_19 : winsorRowDots 19 = (34949398767309750791180746066172498684490537717396080298973798932021751785458985452258268582752152427552250787713559017149748469229717121816762901540962371996288843583608684689248100067246723417379180871209280655791699265890317905819330103375702718620242122667937707146000337426047221783183343231997558325513083042360650741467780181266257477286874617482989415291291316925953559599001528828845283557346660725961199449994900784425076574585520722335472908243732750846824327126511618132561534801432569449306611732861676482276110086507156310973250371469732971474198440628534953152497962065548072354234300557592089174110608367862496870083283594957093209828263425310792562361668226686183231971863606340185094465959959454382395154845390941719925846464204846892277565278385931728452068724018223927509816595964667275500961776894234260576927327337148070419031442587648000,9266849324711034127331236327224653026061784998272300022124531670720785531620972715498773154110940732974053423715033120398342507783872395071662589926080056430019248726818873882362643812252197825908702825699296569017539441113081760824219673231377453374700632689809198517939176678175352566434946440589621660494328937846998794950004869586954106298180318517957084829572406452382540777483380224778576288637117324122969116402143568727430468994991434113894084557071000353122232646450158029050080618096185717072571232016279298638893058789110427302807957037380565789959811832209826222503066537397151863931619310352807093747301072348112225031816584111007088371621558609775520341208538103967390982600296368122032318121829474919008104952317583624125136985499902827658386138485045430029513482599743743407918910556479842763997575406368051079151477112382690139677147529216) := by
  rw [← StreamCheck.row_eq]
  decide +kernel
set_option maxHeartbeats 200000000 in
theorem winsor_row_20 : winsorRowDots 20 = (5812903080121747874926199983955506657335898469518007703866117886026771125171041835590425615990952309211886619324031732574134558995406970646882269559451061717033975888758731224385913412384088211618849921817859013438702751295613326605679884840708293838544679950674745428474286701354389677452708789666556719825000695577480424524575391097452703245276307563442161226606987933371759352251369831273846659606990491719288421763908994973872038243447413925904940681222691882440653882301398040463952867429327739185435758344635474676700546695844767377083099204495546281558428610320860809380845111544412487613235519274927498170488529605639975178245139555455647695813637713746714189278683206919248238451562462278165463477604058406307879465117086679262707687289539421275129733362655391403409590667295078623486695424390413520761924845727864597846031993484553118451590381225590599649643206457753332103374242682769506304000,1757855689882122158647496884203411011557676135476974466166503247041100782879150300589918380778818551160754140468077165645866247843045612345528397714439692776079279182294525648687443922356474164337730571340811569003014657232936556602692188170049003188211972390777650112706674541647150596342700663313317022777643854719301386683436113443512104961667992826393868492803307909526778099834937658201408120764216946752365360444544494519483326970646361028629861367597441068584456634950061783978988409538152747326661557787854948251848821798352052943683080526133429593387918295247900120572315537812928944107065921595531888786479689884929634733904906536871183680307738064751167817491793370627659736245571655842394168396789027281858119520751123828662347961818101979645024800892138298174063695249049037268006694425566431561283193120757545728300331678443176019751159279855941280225401068819251110701124747560923168768) := by
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
    (fun r => (winsorRowDots r).1) (3000*winsorScale*Nn^9) (3000*A) 1 203 25 80 = true := by
  simp_rw [winsorRowDots_eq]
  exact winsor_mgf_fast_ok

theorem winsor_residual_ok : poissonCheckQ Q 13533529 100000000 LN LD
    (fun r => (winsorRowDots r).2) (winsorScale*Nn^9) A 1 2097 10000000 80 = true := by
  simp_rw [winsorRowDots_eq]
  exact winsor_residual_fast_ok
end ClaudeWCT.Numerics.N600
