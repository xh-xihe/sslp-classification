-- Generated proof-only first-code coverage shard.
-- At most 8 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027
import MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028

namespace MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000

open MainTheory.BinaryDetFiveFast

/-- Every canonical second and third code above `0` is covered. -/
theorem cover_first_00 (b c : Fin 32)
    (hab : 0 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 0 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode00 : b = ⟨0, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_00 c hbc
  · have hcode01 : b = ⟨1, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_01 c hbc
  · have hcode02 : b = ⟨2, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_02 c hbc
  · have hcode03 : b = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_03 c hbc
  · have hcode04 : b = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_04 c hbc
  · have hcode05 : b = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_05 c hbc
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard000.cover_pair_00_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard001.cover_pair_00_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard002.cover_pair_00_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard003.cover_pair_00_31 c hbc

/-- Every canonical second and third code above `1` is covered. -/
theorem cover_first_01 (b c : Fin 32)
    (hab : 1 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 1 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode01 : b = ⟨1, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_01 c hbc
  · have hcode02 : b = ⟨2, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_02 c hbc
  · have hcode03 : b = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_03 c hbc
  · have hcode04 : b = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_04 c hbc
  · have hcode05 : b = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_05 c hbc
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard004.cover_pair_01_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard005.cover_pair_01_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard006.cover_pair_01_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_01_31 c hbc

/-- Every canonical second and third code above `2` is covered. -/
theorem cover_first_02 (b c : Fin 32)
    (hab : 2 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 2 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode02 : b = ⟨2, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard007.cover_pair_02_02 c hbc
  · have hcode03 : b = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_03 c hbc
  · have hcode04 : b = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_04 c hbc
  · have hcode05 : b = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_05 c hbc
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard008.cover_pair_02_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard009.cover_pair_02_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard010.cover_pair_02_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_02_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_02_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_02_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_02_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_02_31 c hbc

/-- Every canonical second and third code above `3` is covered. -/
theorem cover_first_03 (b c : Fin 32)
    (hab : 3 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 3 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode03 : b = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_03_03 c hbc
  · have hcode04 : b = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_03_04 c hbc
  · have hcode05 : b = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard011.cover_pair_03_05 c hbc
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard012.cover_pair_03_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard013.cover_pair_03_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard014.cover_pair_03_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_03_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_03_31 c hbc

/-- Every canonical second and third code above `4` is covered. -/
theorem cover_first_04 (b c : Fin 32)
    (hab : 4 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 4 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode04 : b = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_04_04 c hbc
  · have hcode05 : b = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_04_05 c hbc
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_04_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_04_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_04_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard015.cover_pair_04_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard016.cover_pair_04_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard017.cover_pair_04_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_04_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_04_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_04_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_04_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_04_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_04_31 c hbc

/-- Every canonical second and third code above `5` is covered. -/
theorem cover_first_05 (b c : Fin 32)
    (hab : 5 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 5 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode05 : b = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_05_05 c hbc
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard018.cover_pair_05_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard019.cover_pair_05_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard020.cover_pair_05_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard021.cover_pair_05_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_05_31 c hbc

/-- Every canonical second and third code above `6` is covered. -/
theorem cover_first_06 (b c : Fin 32)
    (hab : 6 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 6 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode06 : b = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_06 c hbc
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard022.cover_pair_06_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard023.cover_pair_06_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard024.cover_pair_06_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_06_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_06_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_06_31 c hbc

/-- Every canonical second and third code above `7` is covered. -/
theorem cover_first_07 (b c : Fin 32)
    (hab : 7 <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice 7 b.val c.val 5 := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
  · have hcode07 : b = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_07_07 c hbc
  · have hcode08 : b = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_07_08 c hbc
  · have hcode09 : b = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_07_09 c hbc
  · have hcode10 : b = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_07_10 c hbc
  · have hcode11 : b = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard025.cover_pair_07_11 c hbc
  · have hcode12 : b = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_12 c hbc
  · have hcode13 : b = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_13 c hbc
  · have hcode14 : b = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_14 c hbc
  · have hcode15 : b = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_15 c hbc
  · have hcode16 : b = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_16 c hbc
  · have hcode17 : b = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_17 c hbc
  · have hcode18 : b = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_18 c hbc
  · have hcode19 : b = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard026.cover_pair_07_19 c hbc
  · have hcode20 : b = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_20 c hbc
  · have hcode21 : b = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_21 c hbc
  · have hcode22 : b = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_22 c hbc
  · have hcode23 : b = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_23 c hbc
  · have hcode24 : b = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_24 c hbc
  · have hcode25 : b = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_25 c hbc
  · have hcode26 : b = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_26 c hbc
  · have hcode27 : b = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard027.cover_pair_07_27 c hbc
  · have hcode28 : b = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_07_28 c hbc
  · have hcode29 : b = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_07_29 c hbc
  · have hcode30 : b = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_07_30 c hbc
  · have hcode31 : b = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst b
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.Pair.Shard028.cover_pair_07_31 c hbc

end MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000
