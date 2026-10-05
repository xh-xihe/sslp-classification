-- Generated proof-only pair-coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065

open MainTheory.BinaryDetFiveFast

/-- Every canonical third code for the fixed pair `28,30` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_28_30 (c : Fin 32) (hbc : 30 <= c.val) :
    FastLastCodeSlice 28 30 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_28_30_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_28_30_31

/-- Every canonical third code for the fixed pair `28,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_28_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 28 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_28_31_31

/-- Every canonical third code for the fixed pair `29,29` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_29_29 (c : Fin 32) (hbc : 29 <= c.val) :
    FastLastCodeSlice 29 29 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_29_29_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0746.slice_29_29_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_29_29_31

/-- Every canonical third code for the fixed pair `29,30` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_29_30 (c : Fin 32) (hbc : 30 <= c.val) :
    FastLastCodeSlice 29 30 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_29_30_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_29_30_31

/-- Every canonical third code for the fixed pair `29,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_29_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 29 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_29_31_31

/-- Every canonical third code for the fixed pair `30,30` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_30_30 (c : Fin 32) (hbc : 30 <= c.val) :
    FastLastCodeSlice 30 30 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_30_30_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_30_30_31

/-- Every canonical third code for the fixed pair `30,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_30_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 30 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_30_31_31

/-- Every canonical third code for the fixed pair `31,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_31_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 31 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0747.slice_31_31_31

end MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard065
