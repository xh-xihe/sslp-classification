import Orbit2.SplitSeed
import Orbit2.HilbertBridge

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unnecessarySeqFocus false

namespace Orbit2.SplitSeed
open scoped BigOperators
open Orbit2.TensorPauli

noncomputable def code (a b : ℝ) : Matrix Bits (Fin 2) ℂ := fun s j =>
  ((a : ℂ) * (component 0 j s : ℂ) + (b : ℂ) * (component 1 j s : ℂ))/8

theorem code_action (a b : ℝ) (p : Label 6) :
    operator p * code a b = fun s j =>
      ((a : ℂ) * (act p (component 0 j) s : ℂ) +
       (b : ℂ) * (act p (component 1 j) s : ℂ))/8 := by
  ext s j
  simp_rw [Matrix.mul_apply, HilbertBridge.operator_row]
  simp only [code, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change ((∏ i, localC (p i) (s i) (flip p s i)) *
      (((a : ℂ) * (component 0 j (flip p s) : ℂ) +
        (b : ℂ) * (component 1 j (flip p s) : ℂ))/8)) = _
  have ha : (∏ i, localC (p i) (s i) (flip p s i)) = (amplitude p s : ℂ) := by
    simp [localC, Matrix.map_apply, amplitude, map_prod]
  rw [ha]
  simp only [act, GaussianInt.toComplex_mul]
  ring

theorem compression_polynomial (a b : ℝ) (p : Label 6) (j k : Fin 2) :
    ((code a b).conjTranspose * operator p * code a b) j k =
      ((a : ℂ)^2 * (entry 0 0 p j k : ℂ) +
       (a : ℂ)*(b : ℂ) * ((entry 0 1 p j k : ℂ) + (entry 1 0 p j k : ℂ)) +
       (b : ℂ)^2 * (entry 1 1 p j k : ℂ))/64 := by
  rw [Matrix.mul_assoc, code_action]
  calc
    _ = ∑ s, ((a : ℂ)^2 * (star (component 0 j s : ℂ) * (act p (component 0 k) s : ℂ)) +
        (a : ℂ)*(b : ℂ) * (star (component 0 j s : ℂ) * (act p (component 1 k) s : ℂ) +
          star (component 1 j s : ℂ) * (act p (component 0 k) s : ℂ)) +
        (b : ℂ)^2 * (star (component 1 j s : ℂ) * (act p (component 1 k) s : ℂ)))/64 := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, code]
      apply Finset.sum_congr rfl
      intro s _
      simp only [star_div₀, star_add, star_mul, Complex.star_def,
        Complex.conj_ofReal, star_ofNat]
      ring
    _ = _ := by
      simp only [entry, map_sum, GaussianInt.toComplex_mul, GaussianInt.toComplex_star,
        starRingEnd_apply, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]

noncomputable def scalar (a b : ℝ) (p : Label 6) : ℝ :=
  if p = (fun _ => 0) then a^2+b^2 else
    if p = splitZ then a^2-b^2 else if p = splitXX then 2*a*b else 0

theorem code_KL (a b : ℝ) (p : Label 6) (hp : weight p ≤ 2) :
    (code a b).conjTranspose * operator p * code a b = (scalar a b p : ℂ) • 1 := by
  ext j k
  rw [compression_polynomial]
  have hc := congrArg GaussianInt.toComplex (cross_components p hp j k)
  simp only [map_add] at hc
  rw [hc, diagonal_zero_component p hp, diagonal_one_component p hp]
  have hz0 : splitZ ≠ (fun _ => 0) := by decide +kernel
  have hx0 : splitXX ≠ (fun _ => 0) := by decide +kernel
  have hzx : splitZ ≠ splitXX := by decide +kernel
  by_cases hj : j = k <;> by_cases h0 : p = (fun _ => 0) <;>
    by_cases hz : p = splitZ <;> by_cases hx : p = splitXX <;>
    norm_num [scalar, hj, h0, hz, hx, hz0, hx0, hzx, Ne.symm hz0, Ne.symm hx0,
      Ne.symm hzx, Matrix.smul_apply,
      Matrix.one_apply, GaussianInt.toComplex_def] <;> try ring

theorem code_isometry (a b : ℝ) (hab : a^2+b^2=1) :
    (code a b).conjTranspose * code a b = 1 := by
  have h := code_KL a b (fun _ => 0) (by simp [weight])
  simpa [operator_zero, scalar, hab] using h

theorem code_logical (a b : ℝ) : operator ![0,0,3,3,3,3] * code a b =
    fun s j => (if j = 0 then 1 else -1) * code a b s j := by
  rw [code_action]
  ext s j
  rw [logical_components, logical_components]
  by_cases hj : j=0 <;> simp [hj, code] <;> ring

end Orbit2.SplitSeed
