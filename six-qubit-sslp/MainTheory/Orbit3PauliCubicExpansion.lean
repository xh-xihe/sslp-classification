import MainTheory.Orbit3CubicPhaseStability
import SixQubit.MacWilliams

/-! # Exact expansion of three physical Pauli expectations

The conjugated cubic is on the shifted indices, following `innerC_pauliAct`.
For an even total number of Y factors the phase is real, so the expansion
uses real cubic Gram entries. No normalization or averaging is assumed.
-/

namespace MainTheory.Orbit3PauliCubicExpansion

open SS.MacWilliams MainTheory.Orbit3CliffordAverage
open MainTheory.Orbit3CubicPhaseStability
open scoped BigOperators

noncomputable section

abbrev Triple := SS.BitString 6 × SS.BitString 6 × SS.BitString 6

def shifted (P : Fin 3 → SS.PauliString 6) (t : Triple) : Triple :=
  (SS.bxor t.1 (P 0).x, SS.bxor t.2.1 (P 1).x, SS.bxor t.2.2 (P 2).x)

def character (P : Fin 3 → SS.PauliString 6) (t : Triple) : ℝ :=
  chi (P 0).z t.1 * chi (P 1).z t.2.1 * chi (P 2).z t.2.2

def totalY (P : Fin 3 → SS.PauliString 6) : ℕ :=
  (P 0).numY + (P 1).numY + (P 2).numY

def phase (P : Fin 3 → SS.PauliString 6) : ℝ := (Complex.I ^ totalY P).re

theorem phase_im_zero (P : Fin 3 → SS.PauliString 6)
    (h : totalY P % 2 = 0) : (Complex.I ^ totalY P).im = 0 := by
  obtain ⟨k, hk⟩ := Nat.even_iff.mpr h
  rw [hk, ← two_mul, pow_mul, Complex.I_sq]
  norm_cast

theorem complex_expansion (P : Fin 3 → SS.PauliString 6) (w : SS.State 6 ℂ) :
    (∏ k : Fin 3, SS.innerC w (SS.pauliAct (P k) w)) =
      Complex.I ^ totalY P * ∑ a : SS.BitString 6, ∑ b : SS.BitString 6,
        ∑ c : SS.BitString 6, (character P (a, b, c) : ℂ) *
          (star (monomial (shifted P (a, b, c)) w) * monomial (a, b, c) w) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Fin.succ_zero_eq_one, SS.innerC_pauliAct, signC_bdot]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  rw [show Complex.I ^ totalY P =
    Complex.I ^ (P 0).numY * Complex.I ^ (P 1).numY * Complex.I ^ (P 2).numY by
      simp only [totalY, pow_add]]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  simp only [character, shifted, monomial, star_mul, Complex.ofReal_mul,
    show (1 : Fin 2).succ = (2 : Fin 3) from rfl]
  ring

theorem product_expansion (P : Fin 3 → SS.PauliString 6) (w : SS.State 6 ℂ)
    (h : totalY P % 2 = 0) :
    product P w = phase P * ∑ a : SS.BitString 6, ∑ b : SS.BitString 6,
      ∑ c : SS.BitString 6, character P (a, b, c) * entry (shifted P (a, b, c)) (a, b, c) w := by
  unfold product
  rw [complex_expansion]
  simp only [Complex.mul_re, phase_im_zero P h, zero_mul, sub_zero, phase,
    Complex.re_sum, Complex.ofReal_re, Complex.ofReal_im, entry]

end
end MainTheory.Orbit3PauliCubicExpansion
