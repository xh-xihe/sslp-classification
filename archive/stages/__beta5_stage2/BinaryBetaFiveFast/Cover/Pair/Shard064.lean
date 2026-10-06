-- Generated proof-only pair-coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0743
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064

open MainTheory.BinaryDetFiveFast

/-- Every canonical third code for the fixed pair `26,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_26_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 26 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0743.slice_26_31_31

/-- Every canonical third code for the fixed pair `27,27` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_27_27 (c : Fin 32) (hbc : 27 <= c.val) :
    FastLastCodeSlice 27 27 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0743.slice_27_27_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0743.slice_27_27_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0743.slice_27_27_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_27_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_27_31

/-- Every canonical third code for the fixed pair `27,28` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_27_28 (c : Fin 32) (hbc : 28 <= c.val) :
    FastLastCodeSlice 27 28 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_28_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_28_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_28_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_28_31

/-- Every canonical third code for the fixed pair `27,29` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_27_29 (c : Fin 32) (hbc : 29 <= c.val) :
    FastLastCodeSlice 27 29 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_29_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0744.slice_27_29_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_27_29_31

/-- Every canonical third code for the fixed pair `27,30` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_27_30 (c : Fin 32) (hbc : 30 <= c.val) :
    FastLastCodeSlice 27 30 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_27_30_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_27_30_31

/-- Every canonical third code for the fixed pair `27,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_27_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 27 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_27_31_31

/-- Every canonical third code for the fixed pair `28,28` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_28_28 (c : Fin 32) (hbc : 28 <= c.val) :
    FastLastCodeSlice 28 28 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_28_28_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_28_28_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_28_28_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0745.slice_28_28_31

/-- Every canonical third code for the fixed pair `28,29` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_28_29 (c : Fin 32) (hbc : 29 <= c.val) :
    FastLastCodeSlice 28 29 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_28_29_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_28_29_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_28_29_31

end MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard064
