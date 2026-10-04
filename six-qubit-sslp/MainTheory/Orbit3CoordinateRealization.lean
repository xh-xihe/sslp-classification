import MainTheory.Orbit3CoordinateBlocks
import SixQubit.Generated.Orbit3ReducedCoordinates

/-! # The 269 reduced coordinates are entries of an actual cubic Gram matrix

Concrete checked permutation/transposition witnesses identify each present
table entry with its actual representative. Missing entries vanish by the
physical phase-block theorem. The 36-term certificate square is positive on
these coordinates without any PSD or row interpretation hypothesis.
-/

namespace MainTheory.Orbit3CoordinateRealization

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3CubicBasis MainTheory.Orbit3CoordinateBlocks
open SixQubit.Generated
open scoped Matrix

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

def coordinates (W : Encoder) (c : Fin 269) : ℝ :=
  64 * moment W (Orbit3Coordinates.Data.representative c).1
    (Orbit3Coordinates.Data.representative c).2

theorem entry_interpretation (W : Encoder) (i j : Fin 715)
    (e : Orbit3Coordinates.Data.Entry) (he : Orbit3Coordinates.Data.entry i j = some e) :
    coordinates W e.1 = 64 * moment W i j := by
  have hw := Orbit3ReducedCoordinates.entry_witness i j e he
  unfold coordinates
  split_ifs at hw with hs
  · have hm := congrArg (fun p : Fin 715 × Fin 715 => moment W p.1 p.2) hw
    change moment W (Orbit3Coordinates.Data.permuted e.2.1 i)
      (Orbit3Coordinates.Data.permuted e.2.1 j) =
      moment W (Orbit3Coordinates.Data.representative e.1).2
        (Orbit3Coordinates.Data.representative e.1).1 at hm
    rw [MainTheory.Orbit3CoordinateBlocks.moment_permuted,
      MainTheory.Orbit3CubicPermutation.moment_symmetric W
        (Orbit3Coordinates.Data.representative e.1).2
        (Orbit3Coordinates.Data.representative e.1).1] at hm
    exact congrArg (fun r : ℝ => 64 * r) hm.symm
  · have hm := congrArg (fun p : Fin 715 × Fin 715 => moment W p.1 p.2) hw
    change moment W (Orbit3Coordinates.Data.permuted e.2.1 i)
      (Orbit3Coordinates.Data.permuted e.2.1 j) =
      moment W (Orbit3Coordinates.Data.representative e.1).1
        (Orbit3Coordinates.Data.representative e.1).2 at hm
    rw [MainTheory.Orbit3CoordinateBlocks.moment_permuted] at hm
    exact congrArg (fun r : ℝ => 64 * r) hm.symm

theorem entry_none_iff (i j : Fin 715) :
    Orbit3Coordinates.Data.entry i j = none ↔
      Orbit3Coordinates.Data.blockTag i ≠ Orbit3Coordinates.Data.blockTag j := by
  have hc := Orbit3ReducedCoordinates.entry_coverage i j
  cases he : Orbit3Coordinates.Data.entry i j <;> simp_all

def tableMatrix (y : Fin 269 → ℝ) : Matrix (Fin 715) (Fin 715) ℝ :=
  fun i j => match Orbit3Coordinates.Data.entry i j with
    | none => 0
    | some e => y e.1

theorem tableMatrix_eq_scaled_moment (W : Encoder) :
    tableMatrix (coordinates W) = (64 : ℝ) • moment W := by
  ext i j
  change tableMatrix (coordinates W) i j = 64 * moment W i j
  unfold tableMatrix
  cases he : Orbit3Coordinates.Data.entry i j with
  | none =>
    rw [zero_outside_numeric_block W i j ((entry_none_iff i j).mp he)]
    simp
  | some e => exact entry_interpretation W i j e he

theorem tableMatrix_posSemidef (W : Encoder) :
    (tableMatrix (coordinates W)).PosSemidef := by
  rw [tableMatrix_eq_scaled_moment]
  exact (moment_posSemidef W).smul (by norm_num)

theorem representative_coordinates : ∀ c : Fin 269,
    (Orbit3Coordinates.Data.entry (Orbit3Coordinates.Data.representative c).1
      (Orbit3Coordinates.Data.representative c).2).map Prod.fst = some c := by
  decide +kernel

theorem square_coordinates : ∀ i j : Fin 36,
    (Orbit3Coordinates.Data.entry (squareIndex i) (squareIndex j)).map Prod.fst =
      some (Orbit3PositiveSquare.coordinate i j) := by
  decide +kernel

theorem square_entry_interpretation (W : Encoder) (i j : Fin 36) :
    coordinates W (Orbit3PositiveSquare.coordinate i j) =
      64 * MainTheory.Orbit3PositiveMoments.actualMoment (wave W) i j := by
  have hc := square_coordinates i j
  cases he : Orbit3Coordinates.Data.entry (squareIndex i) (squareIndex j) with
  | none => simp [he] at hc
  | some e =>
    have hcoord : e.1 = Orbit3PositiveSquare.coordinate i j := by
      simpa only [he, Option.map_some, Option.some.injEq] using hc
    rw [← hcoord, square_principal_submatrix]
    exact entry_interpretation W _ _ e he

theorem square_matrix_eq (W : Encoder) :
    Orbit3PositiveSquare.momentMatrix (coordinates W) =
      (64 : ℝ) • MainTheory.Orbit3PositiveMoments.actualMoment (wave W) := by
  ext i j
  exact square_entry_interpretation W i j

theorem square_matrix_posSemidef (W : Encoder) :
    (Orbit3PositiveSquare.momentMatrix (coordinates W)).PosSemidef := by
  rw [square_matrix_eq]
  exact (MainTheory.Orbit3PositiveMoments.actualMoment_posSemidef (wave W)).smul (by norm_num)

theorem reduced_square_nonneg (W : Encoder) :
    0 ≤ Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.square (coordinates W) :=
  Orbit3PositiveSquare.square_nonneg_of_psd _ (square_matrix_posSemidef W)

end
end MainTheory.Orbit3CoordinateRealization
