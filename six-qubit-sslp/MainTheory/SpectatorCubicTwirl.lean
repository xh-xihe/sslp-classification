import MainTheory.SpectatorCubicTwirlFactorization
import SixQubit.Generated.SpectatorCubicTwirl.Checks

/-! The literal 24-element Clifford average is invariant under every local unitary. -/

namespace MainTheory.SpectatorCubicTwirl
noncomputable section
open MainTheory.ThreeCopyPermutationCommutant
open MainTheory.SpectatorCubicTwirlFactorization
open SixQubit.Generated.SpectatorCubicTwirl
open SixQubit.Generated.SpectatorClifford
open scoped BigOperators
set_option maxHeartbeats 4000000

abbrev CubicMatrix := Matrix Triple Triple ℂ

def raw (A : CubicMatrix) : CubicMatrix :=
  ∑ g : Fin 24, copies (clifford g)*A*(copies (clifford g)).conjTranspose

theorem kernel (x z a b : Triple) :
    (∑ g : Fin 24, copies (clifford g) x a*star (copies (clifford g) z b))=
      (data (pair x z) (pair a b) : ℂ)/64 := by
  simp_rw [balanced_factorization]
  rw [← Finset.mul_sum, ← map_sum]
  have h := congrArg GaussianInt.toComplex (numerator_correct (pair x z) (pair a b))
  simp only [numerator, first_pair, second_pair, map_intCast] at h
  rw [h]
  ring

theorem data_span (x z a b : Triple) :
    (data (pair x z) (pair a b) : ℂ)/64=
      ∑ k : Fin 5, ((coefficient k (pair a b) : ℂ)/64)*permutation (sigma k) x z := by
  rw [permutation_span]
  simp only [Int.cast_sum, Int.cast_mul, integerPermutation, first_pair,
    second_pair, permutation, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Finset.sum_div, div_mul_eq_mul_div]

theorem raw_entry (A : CubicMatrix) (x z : Triple) :
    raw A x z=∑ b : Triple, ∑ a : Triple,
      ((data (pair x z) (pair a b) : ℂ)/64)*A a b := by
  simp only [raw, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have he : (∑ g : Fin 24, copies (clifford g) x a*A a b*
      star (copies (clifford g) z b))=
      (∑ g : Fin 24, copies (clifford g) x a*star (copies (clifford g) z b))*A a b := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [he, kernel]

def coefficients (A : CubicMatrix) (k : Fin 5) : ℂ :=
  ∑ b : Triple, ∑ a : Triple, ((coefficient k (pair a b) : ℂ)/64)*A a b

theorem permutation_image (A : CubicMatrix) :
    raw A=∑ k : Fin 5, coefficients A k • permutation (sigma k) := by
  ext x z
  rw [raw_entry]
  simp_rw [data_span]
  simp only [Finset.sum_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    coefficients]
  have hs (f : Triple → Triple → Fin 5 → ℂ) :
      (∑ b, ∑ a, ∑ k, f b a k)=(∑ k, ∑ b, ∑ a, f b a k) := by
    calc
      _=(∑ b, ∑ k, ∑ a, f b a k) := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem arbitrary_unitary_fixed (A : CubicMatrix) (U : Mat)
    (hU : U*U.conjTranspose=1) :
    copies U*raw A*(copies U).conjTranspose=raw A := by
  rw [permutation_image]
  exact span_fixed sigma (coefficients A) U hU

def average (A : CubicMatrix) : CubicMatrix := (1/24 : ℂ) • raw A

theorem average_fixed (A : CubicMatrix) (U : Mat) (hU : U*U.conjTranspose=1) :
    copies U*average A*(copies U).conjTranspose=average A := by
  simp only [average, Matrix.mul_smul, Matrix.smul_mul, arbitrary_unitary_fixed A U hU]

end
end MainTheory.SpectatorCubicTwirl
