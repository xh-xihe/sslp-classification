-- Generated proof-only first-code coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001

open MainTheory.BinaryDetFiveFast

/-- Every canonical second and third code above `8` is covered. -/
theorem cover_first_08 (b c : Fin 32)
    (hab : 8 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 8 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_08_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_08_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_08_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_08_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard029.cover_pair_08_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard030.cover_pair_08_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_08_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_08_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_08_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_08_31 c hbc

/-- Every canonical second and third code above `9` is covered. -/
theorem cover_first_09 (b c : Fin 32)
    (hab : 9 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 9 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_09_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_09_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_09_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard031.cover_pair_09_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard032.cover_pair_09_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard033.cover_pair_09_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_09_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_09_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_09_31 c hbc

/-- Every canonical second and third code above `10` is covered. -/
theorem cover_first_10 (b c : Fin 32)
    (hab : 10 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 10 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_10_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_10_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_10_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_10_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard034.cover_pair_10_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard035.cover_pair_10_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard036.cover_pair_10_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_10_31 c hbc

/-- Every canonical second and third code above `11` is covered. -/
theorem cover_first_11 (b c : Fin 32)
    (hab : 11 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 11 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard037.cover_pair_11_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard038.cover_pair_11_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_11_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_11_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_11_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_11_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_11_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_11_31 c hbc

/-- Every canonical second and third code above `12` is covered. -/
theorem cover_first_12 (b c : Fin 32)
    (hab : 12 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 12 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_12_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard039.cover_pair_12_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040.cover_pair_12_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard041.cover_pair_12_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_12_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_12_31 c hbc

/-- Every canonical second and third code above `13` is covered. -/
theorem cover_first_13 (b c : Fin 32)
    (hab : 13 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 13 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_13_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_13_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_13_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_13_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_13_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard042.cover_pair_13_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard043.cover_pair_13_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_13_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_13_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_13_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_13_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_13_31 c hbc

/-- Every canonical second and third code above `14` is covered. -/
theorem cover_first_14 (b c : Fin 32)
    (hab : 14 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 14 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_14_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_14_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard044.cover_pair_14_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard045.cover_pair_14_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_14_31 c hbc

/-- Every canonical second and third code above `15` is covered. -/
theorem cover_first_15 (b c : Fin 32)
    (hab : 15 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 15 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard046.cover_pair_15_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard047.cover_pair_15_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard048.cover_pair_15_31 c hbc

end MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001
