-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_0_0_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0115

theorem cover_p_0_0_0_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0116
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0117

theorem cover_p_0_0_0_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0118

theorem cover_p_0_0_0_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0119

theorem cover_p_0_0_1_1_1 (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0120
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0121
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0122
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0123
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0124
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0125
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0126

theorem cover_p_0_0_1_1_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0127
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0128
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0129
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0130
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0131
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0132

theorem cover_p_0_0_1_1_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0133
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0134
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0135
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0136
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0137

theorem cover_p_0_0_1_1_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0138
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0139
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0140
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0141

theorem cover_p_0_0_1_1_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0142
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0143
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0144

theorem cover_p_0_0_1_1_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0145
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0146

theorem cover_p_0_0_1_1_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0147

theorem cover_p_0_0_1_2_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0148
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0149
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0150
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0151
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0152
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0153

theorem cover_p_0_0_1_2_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0154
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0155
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0156
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0157
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0158

theorem cover_p_0_0_1_2_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0159
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0160
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0161
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0162

theorem cover_p_0_0_1_2_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0163
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0164
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0165

theorem cover_p_0_0_1_2_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0166
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0167

theorem cover_p_0_0_1_2_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0168

theorem cover_p_0_0_1_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0169
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0170
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0171
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0172
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0173

theorem cover_p_0_0_1_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0174
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0175
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0176
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0177

theorem cover_p_0_0_1_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0178
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0179
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0180

theorem cover_p_0_0_1_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0181
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0182

theorem cover_p_0_0_1_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0183

theorem cover_p_0_0_1_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0184
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0185
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0186
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0187

theorem cover_p_0_0_1_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0188
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0189
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0190

theorem cover_p_0_0_1_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0191
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0192

theorem cover_p_0_0_1_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0193

theorem cover_p_0_0_1_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0194
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0195
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0196

theorem cover_p_0_0_1_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0197
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0198

theorem cover_p_0_0_1_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0199

theorem cover_p_0_0_1_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0200
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0201

theorem cover_p_0_0_1_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0202

theorem cover_p_0_0_1_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0203

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001
