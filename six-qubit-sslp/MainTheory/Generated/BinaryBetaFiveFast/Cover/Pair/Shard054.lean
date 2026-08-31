-- Generated proof-only pair-coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0695

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054

open MainTheory.BinaryDetFiveFast

/-- Every canonical third code for the fixed pair `18,27` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_18_27 (c : Fin 32) (hbc : 27 <= c.val) :
    FastLastCodeSlice 18 27 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689.slice_18_27_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689.slice_18_27_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689.slice_18_27_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689.slice_18_27_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689.slice_18_27_31

/-- Every canonical third code for the fixed pair `18,28` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_18_28 (c : Fin 32) (hbc : 28 <= c.val) :
    FastLastCodeSlice 18 28 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0689.slice_18_28_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_28_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_28_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_28_31

/-- Every canonical third code for the fixed pair `18,29` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_18_29 (c : Fin 32) (hbc : 29 <= c.val) :
    FastLastCodeSlice 18 29 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_29_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_29_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_29_31

/-- Every canonical third code for the fixed pair `18,30` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_18_30 (c : Fin 32) (hbc : 30 <= c.val) :
    FastLastCodeSlice 18 30 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_30_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0690.slice_18_30_31

/-- Every canonical third code for the fixed pair `18,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_18_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 18 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_18_31_31

/-- Every canonical third code for the fixed pair `19,19` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_19_19 (c : Fin 32) (hbc : 19 <= c.val) :
    FastLastCodeSlice 19 19 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0691.slice_19_19_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_19_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_19_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_19_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_19_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_19_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_19_31

/-- Every canonical third code for the fixed pair `19,20` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_19_20 (c : Fin 32) (hbc : 20 <= c.val) :
    FastLastCodeSlice 19 20 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_20_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0692.slice_19_20_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0693.slice_19_20_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_20_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_20_31

/-- Every canonical third code for the fixed pair `19,21` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_19_21 (c : Fin 32) (hbc : 21 <= c.val) :
    FastLastCodeSlice 19 21 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_21_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_21_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_21_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_21_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_21_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0694.slice_19_21_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0695.slice_19_21_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0695.slice_19_21_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0695.slice_19_21_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0695.slice_19_21_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0695.slice_19_21_31

end MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard054
