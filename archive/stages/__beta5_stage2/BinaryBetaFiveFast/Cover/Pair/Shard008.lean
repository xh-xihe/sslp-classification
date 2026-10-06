-- Generated proof-only pair-coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0131
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156
import MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0157

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008

open MainTheory.BinaryDetFiveFast

/-- Every canonical third code for the fixed pair `2,3` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_03 (c : Fin 32) (hbc : 3 <= c.val) :
    FastLastCodeSlice 2 3 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode03 : c = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0131.slice_02_03_03
  · have hcode04 : c = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0131.slice_02_03_04
  · have hcode05 : c = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_05
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0132.slice_02_03_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0133.slice_02_03_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0134.slice_02_03_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_03_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_03_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_03_31

/-- Every canonical third code for the fixed pair `2,4` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_04 (c : Fin 32) (hbc : 4 <= c.val) :
    FastLastCodeSlice 2 4 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode04 : c = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_04_04
  · have hcode05 : c = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_04_05
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_04_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_04_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0135.slice_02_04_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0136.slice_02_04_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0137.slice_02_04_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_04_31

/-- Every canonical third code for the fixed pair `2,5` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_05 (c : Fin 32) (hbc : 5 <= c.val) :
    FastLastCodeSlice 2 5 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode05 : c = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0138.slice_02_05_05
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0139.slice_02_05_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0140.slice_02_05_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0141.slice_02_05_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_05_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_05_31

/-- Every canonical third code for the fixed pair `2,6` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_06 (c : Fin 32) (hbc : 6 <= c.val) :
    FastLastCodeSlice 2 6 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode06 : c = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_06_06
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_06_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_06_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_06_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_06_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0142.slice_02_06_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0143.slice_02_06_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0144.slice_02_06_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_06_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_06_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_06_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_06_31

/-- Every canonical third code for the fixed pair `2,7` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_07 (c : Fin 32) (hbc : 7 <= c.val) :
    FastLastCodeSlice 2 7 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode07 : c = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_07_07
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_07_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_07_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0145.slice_02_07_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0146.slice_02_07_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0147.slice_02_07_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_07_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_07_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_07_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_07_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_07_31

/-- Every canonical third code for the fixed pair `2,8` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_08 (c : Fin 32) (hbc : 8 <= c.val) :
    FastLastCodeSlice 2 8 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode08 : c = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_08_08
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_08_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0148.slice_02_08_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0149.slice_02_08_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0150.slice_02_08_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_08_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_08_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_08_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_08_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_08_31

/-- Every canonical third code for the fixed pair `2,9` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_09 (c : Fin 32) (hbc : 9 <= c.val) :
    FastLastCodeSlice 2 9 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode09 : c = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_09_09
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_09_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0151.slice_02_09_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0152.slice_02_09_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0153.slice_02_09_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_09_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_09_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_09_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_09_31

/-- Every canonical third code for the fixed pair `2,10` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem cover_pair_02_10 (c : Fin 32) (hbc : 10 <= c.val) :
    FastLastCodeSlice 2 10 c.val 5 := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
  · have hcode10 : c = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_10_10
  · have hcode11 : c = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_10_11
  · have hcode12 : c = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_10_12
  · have hcode13 : c = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0154.slice_02_10_13
  · have hcode14 : c = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_14
  · have hcode15 : c = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_15
  · have hcode16 : c = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_16
  · have hcode17 : c = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_17
  · have hcode18 : c = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_18
  · have hcode19 : c = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_19
  · have hcode20 : c = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_20
  · have hcode21 : c = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0155.slice_02_10_21
  · have hcode22 : c = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_22
  · have hcode23 : c = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_23
  · have hcode24 : c = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_24
  · have hcode25 : c = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_25
  · have hcode26 : c = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_26
  · have hcode27 : c = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_27
  · have hcode28 : c = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_28
  · have hcode29 : c = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0156.slice_02_10_29
  · have hcode30 : c = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0157.slice_02_10_30
  · have hcode31 : c = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst c
    exact MainTheory.Generated.BinaryBetaFiveFast.Arithmetic.Shard0157.slice_02_10_31

end MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008
