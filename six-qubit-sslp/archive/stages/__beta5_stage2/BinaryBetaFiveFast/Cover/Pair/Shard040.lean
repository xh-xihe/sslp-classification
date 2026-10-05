-- Generated proof-only pair-coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0560
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040

open MainTheory.BinaryDetFiveFast

/-- Every canonical third code for the fixed pair `12,14` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_14 (c : Fin 32) (hbc : 14 <= c.val) :
    FastLastCodeSlice 12 14 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0560.slice_12_14_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0560.slice_12_14_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0560.slice_12_14_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0560.slice_12_14_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0560.slice_12_14_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0561.slice_12_14_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_14_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_14_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_14_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_14_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_14_31

/-- Every canonical third code for the fixed pair `12,15` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_15 (c : Fin 32) (hbc : 15 <= c.val) :
    FastLastCodeSlice 12 15 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_15_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_15_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0562.slice_12_15_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0563.slice_12_15_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_15_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_15_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_15_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_15_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_15_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_15_31

/-- Every canonical third code for the fixed pair `12,16` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_16 (c : Fin 32) (hbc : 16 <= c.val) :
    FastLastCodeSlice 12 16 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_16_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0564.slice_12_16_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0565.slice_12_16_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_16_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_16_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_16_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_16_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_16_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_16_31

/-- Every canonical third code for the fixed pair `12,17` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_17 (c : Fin 32) (hbc : 17 <= c.val) :
    FastLastCodeSlice 12 17 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_17_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0566.slice_12_17_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0567.slice_12_17_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_17_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_17_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_17_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_17_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_17_31

/-- Every canonical third code for the fixed pair `12,18` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_18 (c : Fin 32) (hbc : 18 <= c.val) :
    FastLastCodeSlice 12 18 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_18_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_18_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0568.slice_12_18_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0569.slice_12_18_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_18_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_18_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_18_31

/-- Every canonical third code for the fixed pair `12,19` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_19 (c : Fin 32) (hbc : 19 <= c.val) :
    FastLastCodeSlice 12 19 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_19_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_19_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_19_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_19_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0570.slice_12_19_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0571.slice_12_19_31

/-- Every canonical third code for the fixed pair `12,20` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_20 (c : Fin 32) (hbc : 20 <= c.val) :
    FastLastCodeSlice 12 20 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0572.slice_12_20_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_20_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_20_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_20_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_20_31

/-- Every canonical third code for the fixed pair `12,21` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_12_21 (c : Fin 32) (hbc : 21 <= c.val) :
    FastLastCodeSlice 12 21 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_21_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_21_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_21_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0573.slice_12_21_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0574.slice_12_21_31

end MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard040
