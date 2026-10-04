import MainTheory.Orbit3PauliTranslationReduction
import MainTheory.Orbit3CoordinateRealization
import MainTheory.Orbit3CubicPermutation

/-! # Physical Pauli triple moments equal integer coordinate evaluations

The coordinates are already actual sampler moments. This module fixes the
coefficient sign and index conventions and proves the equality for any
Pauli triple with XOR-zero x and z and even total Y count.
-/

namespace MainTheory.Orbit3PauliMomentInterpretation

open MainTheory.Orbit3PauliCubicExpansion MainTheory.Orbit3PauliTranslationReduction
open MainTheory.Orbit3CubicPhaseStability MainTheory.Orbit3CubicBasis
open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3CliffordAverage MainTheory.Orbit3CoordinateRealization
open MainTheory.FiniteCubicMoments SS.MacWilliams
open SixQubit.Generated
open scoped BigOperators

noncomputable section

def bitLabel (a : SS.BitString 6) : Fin 64 := ⟨SixQubit.Realize.num a, SixQubit.Realize.num_lt a⟩

theorem bitLabel_nbit : ∀ a : Fin 64, bitLabel (SixQubit.Realize.nbit a.val) = a := by
  decide +kernel

def bitEquiv : Fin 64 ≃ SS.BitString 6 where
  toFun a := SixQubit.Realize.nbit a.val
  invFun := bitLabel
  left_inv := bitLabel_nbit
  right_inv := SixQubit.Realize.nbit_num

def pairIndex (a b : SS.BitString 6) : Fin 715 :=
  Orbit3CubicTriples.pairIndex (bitLabel a) (bitLabel b)

theorem pair_monomial (w : SS.State 6 ℂ) (a b : SS.BitString 6) :
    MainTheory.CubicTripleCanonical.monomial w (Orbit3CubicTriples.physical (pairIndex a b)) =
      monomial (pair a b) w := by
  simpa only [pairIndex, bitLabel, SixQubit.Realize.nbit_num, monomial, pair] using
    Orbit3CubicTriples.actual_cubic_pair w (bitLabel a) (bitLabel b)

theorem pair_moment (W : Encoder) (a b u v : SS.BitString 6) :
    moment W (pairIndex a b) (pairIndex u v) =
      ∑ g : Index, entry (pair a b) (pair u v) (wave W g) := by
  unfold moment
  rw [cubicMoment_apply]
  change (∑ g : Index,
    (star (MainTheory.CubicTripleCanonical.monomial (wave W g)
      (Orbit3CubicTriples.physical (pairIndex a b))) *
      MainTheory.CubicTripleCanonical.monomial (wave W g)
        (Orbit3CubicTriples.physical (pairIndex u v))).re) = _
  simp_rw [pair_monomial]
  rfl

theorem shifted_pair (P : Fin 3 → SS.PauliString 6)
    (hx : SS.bxor (P 0).x (P 1).x = (P 2).x) (a b : SS.BitString 6) :
    shifted P (pair a b) = pair (SS.bxor a (P 0).x) (SS.bxor b (P 1).x) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · change SS.bxor (SS.bxor a b) (P 2).x =
        SS.bxor (SS.bxor a (P 0).x) (SS.bxor b (P 1).x)
      rw [← hx]
      funext j
      dsimp only [shifted, pair, SS.bxor]
      cases a j <;> cases b j <;> cases (P 0).x j <;> cases (P 1).x j <;> rfl

def sign (b : Bool) : ℤ := if b then -1 else 1

theorem chi_sign (a b : SS.BitString 6) : chi a b = (sign (SS.bdot a b) : ℝ) := by
  have h := congrArg Complex.re (signC_bdot a b 1)
  cases hb : SS.bdot a b <;> simpa [hb, SS.signC, sign] using h.symm

def phaseSign (P : Fin 3 → SS.PauliString 6) : ℤ :=
  if totalY P % 4 = 0 then 1 else -1

theorem phase_sign (P : Fin 3 → SS.PauliString 6) (hy : totalY P % 2 = 0) :
    phase P = (phaseSign P : ℝ) := by
  have he : totalY P % 4 = 0 ∨ totalY P % 4 = 2 := by omega
  unfold phase phaseSign
  rw [Complex.I_pow_eq_pow_mod]
  rcases he with he | he <;> norm_num [he, Complex.I_sq]

def coefficient (P : Fin 3 → SS.PauliString 6) (a b : Fin 64) : ℤ :=
  let u := SixQubit.Realize.nbit a.val
  let v := SixQubit.Realize.nbit b.val
  phaseSign P * sign (SS.bdot (P 0).z u) * sign (SS.bdot (P 1).z v) *
    sign (SS.bdot (P 2).z (SS.bxor u v))

def rightIndex (P : Fin 3 → SS.PauliString 6) (a b : Fin 64) : Fin 715 :=
  pairIndex (SS.bxor (SixQubit.Realize.nbit a.val) (P 0).x)
    (SS.bxor (SixQubit.Realize.nbit b.val) (P 1).x)

def rawEvaluation (P : Fin 3 → SS.PauliString 6) (y : Fin 269 → ℝ) : ℝ :=
  ∑ a : Fin 64, ∑ b : Fin 64,
    (coefficient P a b : ℝ) * tableMatrix y (Orbit3CubicTriples.pairIndex a b) (rightIndex P a b)

theorem sampled_product_coordinates (W : Encoder) (P : Fin 3 → SS.PauliString 6)
    (hx : SS.bxor (P 0).x (P 1).x = (P 2).x)
    (hz : SS.bxor (P 0).z (P 1).z = (P 2).z) (hy : totalY P % 2 = 0) :
    (∑ g : Index, product P (wave W g)) = rawEvaluation P (coordinates W) := by
  rw [sampled_product_reduction W P hz hy]
  simp_rw [shifted_pair P hx, ← pair_moment,
    MainTheory.Orbit3CubicPermutation.moment_symmetric W]
  rw [phase_sign P hy]
  unfold rawEvaluation
  simp only [tableMatrix_eq_scaled_moment, Matrix.smul_apply, smul_eq_mul]
  rw [← bitEquiv.sum_comp (fun a => ∑ b : SS.BitString 6,
    character P (pair a b) * moment W (pairIndex a b)
      (pairIndex (SS.bxor a (P 0).x) (SS.bxor b (P 1).x)))]
  simp_rw [← bitEquiv.sum_comp (fun b => character P (pair _ b) *
    moment W (pairIndex _ b) (pairIndex (SS.bxor _ (P 0).x) (SS.bxor b (P 1).x)))]
  simp only [bitEquiv, Equiv.coe_fn_mk, character, pair, chi_sign, pairIndex,
    bitLabel_nbit, rightIndex, coefficient, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end MainTheory.Orbit3PauliMomentInterpretation
