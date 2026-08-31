-- Generated proof-only first-code coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002

open MainTheory.BinaryDetFiveFast

/-- Every canonical second and third code above `16` is covered. -/
theorem cover_first_16 (b c : Fin 32)
    (hab : 16 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 16 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard049.cover_pair_16_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard050.cover_pair_16_31 c hbc

/-- Every canonical second and third code above `17` is covered. -/
theorem cover_first_17 (b c : Fin 32)
    (hab : 17 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 17 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard051.cover_pair_17_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_17_31 c hbc

/-- Every canonical second and third code above `18` is covered. -/
theorem cover_first_18 (b c : Fin 32)
    (hab : 18 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 18 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard052.cover_pair_18_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard053.cover_pair_18_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_18_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_18_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_18_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_18_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_18_31 c hbc

/-- Every canonical second and third code above `19` is covered. -/
theorem cover_first_19 (b c : Fin 32)
    (hab : 19 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 19 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_19_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_19_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054.cover_pair_19_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard055.cover_pair_19_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_19_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_19_31 c hbc

/-- Every canonical second and third code above `20` is covered. -/
theorem cover_first_20 (b c : Fin 32)
    (hab : 20 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 20 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_20_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_20_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_20_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_20_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_20_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard056.cover_pair_20_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_20_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_20_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_20_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_20_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_20_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_20_31 c hbc

/-- Every canonical second and third code above `21` is covered. -/
theorem cover_first_21 (b c : Fin 32)
    (hab : 21 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 21 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_21_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard057.cover_pair_21_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard058.cover_pair_21_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_21_31 c hbc

/-- Every canonical second and third code above `22` is covered. -/
theorem cover_first_22 (b c : Fin 32)
    (hab : 22 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 22 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard059.cover_pair_22_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_22_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_22_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_22_31 c hbc

/-- Every canonical second and third code above `23` is covered. -/
theorem cover_first_23 (b c : Fin 32)
    (hab : 23 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 23 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_23_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_23_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_23_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_23_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard060.cover_pair_23_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_23_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_23_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_23_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_23_31 c hbc

end MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002
