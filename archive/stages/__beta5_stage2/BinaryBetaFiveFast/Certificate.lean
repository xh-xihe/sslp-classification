-- Generated semantic endpoint for the fully kernel-checked beta-five bound.
import MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000
import MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001
import MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002
import MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003
import MainTheory.BinaryBetaSmallLower

namespace MainTheory.Generated.BinaryBetaFiveFast.Certificate

open MainTheory.BinaryBeta
open MainTheory.BinaryDetFiveFast
open MainTheory.BinaryBetaSmallSemantic

/-- Every weakly increasing triple of five-bit row codes owns its complete
final-code arithmetic slice.  Coverage is by three nested `Fin 32`
enumerations in Lean, not by trusting the generator's list length. -/
theorem allCanonical (a b c : Fin 32)
    (hab : a.val <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice a.val b.val c.val 5 := by
  have hlt : a.val < 32 := a.isLt
  interval_cases hvalue : a.val
  · have hcode00 : a = ⟨0, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_00 b c hab hbc
  · have hcode01 : a = ⟨1, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_01 b c hab hbc
  · have hcode02 : a = ⟨2, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_02 b c hab hbc
  · have hcode03 : a = ⟨3, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_03 b c hab hbc
  · have hcode04 : a = ⟨4, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_04 b c hab hbc
  · have hcode05 : a = ⟨5, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_05 b c hab hbc
  · have hcode06 : a = ⟨6, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_06 b c hab hbc
  · have hcode07 : a = ⟨7, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard000.cover_first_07 b c hab hbc
  · have hcode08 : a = ⟨8, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_08 b c hab hbc
  · have hcode09 : a = ⟨9, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_09 b c hab hbc
  · have hcode10 : a = ⟨10, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_10 b c hab hbc
  · have hcode11 : a = ⟨11, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_11 b c hab hbc
  · have hcode12 : a = ⟨12, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_12 b c hab hbc
  · have hcode13 : a = ⟨13, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_13 b c hab hbc
  · have hcode14 : a = ⟨14, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_14 b c hab hbc
  · have hcode15 : a = ⟨15, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard001.cover_first_15 b c hab hbc
  · have hcode16 : a = ⟨16, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_16 b c hab hbc
  · have hcode17 : a = ⟨17, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_17 b c hab hbc
  · have hcode18 : a = ⟨18, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_18 b c hab hbc
  · have hcode19 : a = ⟨19, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_19 b c hab hbc
  · have hcode20 : a = ⟨20, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_20 b c hab hbc
  · have hcode21 : a = ⟨21, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_21 b c hab hbc
  · have hcode22 : a = ⟨22, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_22 b c hab hbc
  · have hcode23 : a = ⟨23, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard002.cover_first_23 b c hab hbc
  · have hcode24 : a = ⟨24, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_24 b c hab hbc
  · have hcode25 : a = ⟨25, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_25 b c hab hbc
  · have hcode26 : a = ⟨26, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_26 b c hab hbc
  · have hcode27 : a = ⟨27, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_27 b c hab hbc
  · have hcode28 : a = ⟨28, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_28 b c hab hbc
  · have hcode29 : a = ⟨29, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_29 b c hab hbc
  · have hcode30 : a = ⟨30, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_30 b c hab hbc
  · have hcode31 : a = ⟨31, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst a
    exact MainTheory.Generated.BinaryBetaFiveFast.Cover.First.Shard003.cover_first_31 b c hab hbc

/-- The complete fast table proves the exact sorted-prefix interface. -/
theorem monotonePrefix : MonotonePrefixCertificate 4 5 := by
  intro f hf
  have h01 : (f 0).toNat <= (f 1).toNat :=
    hf (show (0 : Fin 4) <= 1 by decide)
  have h12 : (f 1).toNat <= (f 2).toNat :=
    hf (show (1 : Fin 4) <= 2 by decide)
  have h23 : (f 2).toNat <= (f 3).toNat :=
    hf (show (2 : Fin 4) <= 3 by decide)
  have h0lt : (f 0).toNat < 32 := by simpa using (f 0).isLt
  have h1lt : (f 1).toNat < 32 := by simpa using (f 1).isLt
  have h2lt : (f 2).toNat < 32 := by simpa using (f 2).isLt
  have h3lt : (f 3).toNat < 32 := by simpa using (f 3).isLt
  let a : Fin 32 := ⟨(f 0).toNat, h0lt⟩
  let b : Fin 32 := ⟨(f 1).toNat, h1lt⟩
  let c : Fin 32 := ⟨(f 2).toNat, h2lt⟩
  have hs : FastLastCodeSlice a.val b.val c.val 5 :=
    allCanonical a b c (by simpa [a, b] using h01)
      (by simpa [b, c] using h12)
  have hp : FastPrefixBound
      ![a.val, b.val, c.val, (f 3).toNat] 5 :=
    hs.lookup (by simpa [c] using h23) h3lt
  apply FastPrefixBound.toReducedAtRowBits
  have hcodes : (fun i => (f i).toNat) =
      ![(f 0).toNat, (f 1).toNat, (f 2).toNat, (f 3).toNat] := by
    funext i
    fin_cases i <;> rfl
  rw [hcodes]
  simpa [a, b, c] using hp

theorem upper : BetaBound 5 5 := by
  simpa using betaBound_of_monotonePrefixCertificate monotonePrefix

theorem betaExact : BetaExact 5 5 :=
  ⟨upper, MainTheory.BinaryBetaSmallLower.Five.betaFiveAttained⟩

end MainTheory.Generated.BinaryBetaFiveFast.Certificate
