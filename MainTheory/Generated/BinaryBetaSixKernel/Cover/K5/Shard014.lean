-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_1_2_3_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1091

theorem cover_p_1_2_3_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1092

theorem cover_p_1_2_4_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1093
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1094
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1095
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1096

theorem cover_p_1_2_4_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1097
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1098
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1099

theorem cover_p_1_2_4_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1100
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1101

theorem cover_p_1_2_4_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1102

theorem cover_p_1_2_4_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1103
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1104
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1105

theorem cover_p_1_2_4_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1106
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1107

theorem cover_p_1_2_4_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1108

theorem cover_p_1_2_4_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1109
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1110

theorem cover_p_1_2_4_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1111

theorem cover_p_1_2_4_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1112

theorem cover_p_1_2_5_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1113
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1114
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1115

theorem cover_p_1_2_5_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1116
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1117

theorem cover_p_1_2_5_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1118

theorem cover_p_1_2_5_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069.canonicalBound_1119
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1120

theorem cover_p_1_2_5_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1121

theorem cover_p_1_2_5_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1122

theorem cover_p_1_2_6_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1123
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1124

theorem cover_p_1_2_6_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1125

theorem cover_p_1_2_6_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1126

theorem cover_p_1_2_7_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 7 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1127

theorem cover_p_1_3_3_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1128
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1129
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1130
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1131
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1132

theorem cover_p_1_3_3_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1133
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1134
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1135
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1136

theorem cover_p_1_3_3_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1137
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1138
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1139

theorem cover_p_1_3_3_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1140
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1141

theorem cover_p_1_3_3_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1142

theorem cover_p_1_3_3_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1143
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1144
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1145
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1146

theorem cover_p_1_3_3_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1147
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1148
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1149

theorem cover_p_1_3_3_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1150
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1151

theorem cover_p_1_3_3_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072.canonicalBound_1152

theorem cover_p_1_3_3_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072.canonicalBound_1153
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072.canonicalBound_1154
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072.canonicalBound_1155

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014
