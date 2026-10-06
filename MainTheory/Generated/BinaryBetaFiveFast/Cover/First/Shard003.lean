-- Generated proof-only first-code coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003

open MainTheory.BinaryDetFiveFast

/-- Every canonical second and third code above `24` is covered. -/
theorem cover_first_24 (b c : Fin 32)
    (hab : 24 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 24 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_24_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_24_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_24_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard061.cover_pair_24_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_24_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_24_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_24_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_24_31 c hbc

/-- Every canonical second and third code above `25` is covered. -/
theorem cover_first_25 (b c : Fin 32)
    (hab : 25 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 25 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_25_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_25_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_25_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard062.cover_pair_25_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_25_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_25_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_25_31 c hbc

/-- Every canonical second and third code above `26` is covered. -/
theorem cover_first_26 (b c : Fin 32)
    (hab : 26 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 26 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_26_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_26_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_26_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_26_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard063.cover_pair_26_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_26_31 c hbc

/-- Every canonical second and third code above `27` is covered. -/
theorem cover_first_27 (b c : Fin 32)
    (hab : 27 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 27 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_27_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_27_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_27_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_27_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_27_31 c hbc

/-- Every canonical second and third code above `28` is covered. -/
theorem cover_first_28 (b c : Fin 32)
    (hab : 28 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 28 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_28_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064.cover_pair_28_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_28_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_28_31 c hbc

/-- Every canonical second and third code above `29` is covered. -/
theorem cover_first_29 (b c : Fin 32)
    (hab : 29 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 29 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_29_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_29_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_29_31 c hbc

/-- Every canonical second and third code above `30` is covered. -/
theorem cover_first_30 (b c : Fin 32)
    (hab : 30 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 30 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_30_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_30_31 c hbc

/-- Every canonical second and third code above `31` is covered. -/
theorem cover_first_31 (b c : Fin 32)
    (hab : 31 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 31 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065.cover_pair_31_31 c hbc

end MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003
