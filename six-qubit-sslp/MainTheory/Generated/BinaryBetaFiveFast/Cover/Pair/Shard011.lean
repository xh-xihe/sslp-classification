-- Generated proof-only pair-coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0196

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011

open MainTheory.BinaryDetFiveFast

/-- Every canonical third code for the fixed pair `2,27` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_27 (c : Fin 32) (hbc : 27 <= c.val) :
    FastLastCodeSlice 2 27 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184.slice_02_27_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184.slice_02_27_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184.slice_02_27_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184.slice_02_27_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184.slice_02_27_31

/-- Every canonical third code for the fixed pair `2,28` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_28 (c : Fin 32) (hbc : 28 <= c.val) :
    FastLastCodeSlice 2 28 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0184.slice_02_28_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_28_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_28_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_28_31

/-- Every canonical third code for the fixed pair `2,29` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_29 (c : Fin 32) (hbc : 29 <= c.val) :
    FastLastCodeSlice 2 29 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_29_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_29_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_29_31

/-- Every canonical third code for the fixed pair `2,30` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_30 (c : Fin 32) (hbc : 30 <= c.val) :
    FastLastCodeSlice 2 30 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_30_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0185.slice_02_30_31

/-- Every canonical third code for the fixed pair `2,31` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_31 (c : Fin 32) (hbc : 31 <= c.val) :
    FastLastCodeSlice 2 31 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_02_31_31

/-- Every canonical third code for the fixed pair `3,3` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_03_03 (c : Fin 32) (hbc : 3 <= c.val) :
    FastLastCodeSlice 3 3 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode03 : c = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_03
  · have hcode04 : c = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_04
  · have hcode05 : c = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_05
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0186.slice_03_03_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0187.slice_03_03_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0188.slice_03_03_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_03_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_03_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_03_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_03_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_03_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_03_31

/-- Every canonical third code for the fixed pair `3,4` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_03_04 (c : Fin 32) (hbc : 4 <= c.val) :
    FastLastCodeSlice 3 4 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode04 : c = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_04_04
  · have hcode05 : c = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0189.slice_03_04_05
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0190.slice_03_04_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0191.slice_03_04_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0192.slice_03_04_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_04_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_04_31

/-- Every canonical third code for the fixed pair `3,5` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_03_05 (c : Fin 32) (hbc : 5 <= c.val) :
    FastLastCodeSlice 3 5 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode05 : c = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_05_05
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_05_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_05_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_05_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_05_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0193.slice_03_05_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0194.slice_03_05_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0195.slice_03_05_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0196.slice_03_05_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0196.slice_03_05_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0196.slice_03_05_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0196.slice_03_05_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0196.slice_03_05_31

end MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011
