-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_0_0_0_0 (a5 : Fin 8)
    (h45 : 0 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 a5.val)) 9 := by
  fin_cases a5
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0000
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0001
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0002
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0003
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0004
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0005
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0006
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0007

theorem cover_p_0_0_0_0_1 (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0008
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0009
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0010
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0011
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0012
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0013
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0014

theorem cover_p_0_0_0_0_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0015
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0016
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0017
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0018
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0019
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0020

theorem cover_p_0_0_0_0_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0021
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0022
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0023
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0024
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0025

theorem cover_p_0_0_0_0_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0026
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0027
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0028
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0029

theorem cover_p_0_0_0_0_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0030
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0031
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0032

theorem cover_p_0_0_0_0_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0033
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0034

theorem cover_p_0_0_0_0_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0035

theorem cover_p_0_0_0_1_1 (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0036
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0037
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0038
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0039
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0040
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0041
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0042

theorem cover_p_0_0_0_1_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0043
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0044
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0045
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0046
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0047
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0048

theorem cover_p_0_0_0_1_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0049
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0050
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0051
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0052
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0053

theorem cover_p_0_0_0_1_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0054
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0055
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0056
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0057

theorem cover_p_0_0_0_1_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0058
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0059
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0060

theorem cover_p_0_0_0_1_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0061
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0062

theorem cover_p_0_0_0_1_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0063

theorem cover_p_0_0_0_2_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0064
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0065
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0066
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0067
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0068
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0069

theorem cover_p_0_0_0_2_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0070
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0071
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0072
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0073
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0074

theorem cover_p_0_0_0_2_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0075
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0076
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0077
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0078

theorem cover_p_0_0_0_2_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0079
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0080
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0081

theorem cover_p_0_0_0_2_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0082
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0083

theorem cover_p_0_0_0_2_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0084

theorem cover_p_0_0_0_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0085
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0086
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0087
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0088
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0089

theorem cover_p_0_0_0_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0090
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0091
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0092
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0093

theorem cover_p_0_0_0_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0094
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0095
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0096

theorem cover_p_0_0_0_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0097
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0098

theorem cover_p_0_0_0_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0099

theorem cover_p_0_0_0_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0100
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0101
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0102
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0103

theorem cover_p_0_0_0_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0104
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0105
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0106

theorem cover_p_0_0_0_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0107
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0108

theorem cover_p_0_0_0_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0109

theorem cover_p_0_0_0_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0110
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0111
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0112

theorem cover_p_0_0_0_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0113
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0114

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000
