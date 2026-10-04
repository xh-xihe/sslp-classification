import MainTheory.Orbit3CubicBasis
import MainTheory.Orbit3PermutationAverage
import MainTheory.Orbit3CubicPhaseStability

/-! # Actual permutation and transpose relations in the 715 cubic basis -/

namespace MainTheory.Orbit3CubicPermutation

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3PermutationAverage MainTheory.Orbit3CubicBasis
open MainTheory.CubicTripleCanonical MainTheory.FiniteCubicMoments
open SixQubit.CodeEquiv SixQubit.Generated
open scoped BigOperators

noncomputable section

def bitLabel (s : SS.BitString 6) : Fin 64 := ⟨SixQubit.Realize.num s, SixQubit.Realize.num_lt s⟩

def permuteIndex (σ : ActivePermutation) (i : Fin 715) : Fin 715 :=
  Orbit3CubicTriples.pairIndex
    (bitLabel (permStr σ.val (Orbit3CubicTriples.physical i).1))
    (bitLabel (permStr σ.val (Orbit3CubicTriples.physical i).2.1))

theorem monomial_permuted (σ : ActivePermutation) (w : SS.State 6 ℂ) (i : Fin 715) :
    monomial (permAct σ.val w) (Orbit3CubicTriples.physical i) =
      monomial w (Orbit3CubicTriples.physical (permuteIndex σ i)) := by
  have h := Orbit3CubicTriples.actual_cubic_pair w
    (bitLabel (permStr σ.val (Orbit3CubicTriples.physical i).1))
    (bitLabel (permStr σ.val (Orbit3CubicTriples.physical i).2.1))
  simp only [bitLabel, SixQubit.Realize.nbit_num] at h
  rw [← permStr_bxor, Orbit3CubicTriples.physical_xor] at h
  exact h.symm

theorem entry_permuted (σ : ActivePermutation) (w : SS.State 6 ℂ) (i j : Fin 715) :
    MainTheory.Orbit3CubicPhaseStability.entry (Orbit3CubicTriples.physical i)
      (Orbit3CubicTriples.physical j) (permAct σ.val w) =
    MainTheory.Orbit3CubicPhaseStability.entry (Orbit3CubicTriples.physical (permuteIndex σ i))
      (Orbit3CubicTriples.physical (permuteIndex σ j)) w := by
  change (star (monomial (permAct σ.val w) (Orbit3CubicTriples.physical i)) *
    monomial (permAct σ.val w) (Orbit3CubicTriples.physical j)).re =
    (star (monomial w (Orbit3CubicTriples.physical (permuteIndex σ i))) *
      monomial w (Orbit3CubicTriples.physical (permuteIndex σ j))).re
  rw [monomial_permuted, monomial_permuted]

theorem moment_permuted (σ : ActivePermutation) (W : Encoder) (i j : Fin 715) :
    moment W (permuteIndex σ i) (permuteIndex σ j) = moment W i j := by
  simp only [moment, cubicMoment_apply]
  change (∑ g : Index, MainTheory.Orbit3CubicPhaseStability.entry
    (Orbit3CubicTriples.physical (permuteIndex σ i))
    (Orbit3CubicTriples.physical (permuteIndex σ j)) (wave W g)) =
    ∑ g : Index, MainTheory.Orbit3CubicPhaseStability.entry
      (Orbit3CubicTriples.physical i) (Orbit3CubicTriples.physical j) (wave W g)
  have h := sampling_permutation_identity σ
    (MainTheory.Orbit3CubicPhaseStability.entry (Orbit3CubicTriples.physical i)
      (Orbit3CubicTriples.physical j)) W
  simp_rw [entry_permuted] at h
  exact h

theorem moment_symmetric (W : Encoder) (i j : Fin 715) : moment W i j = moment W j i := by
  simp only [moment, cubicMoment_apply]
  apply Finset.sum_congr rfl
  intro g _
  have he (a b : ℂ) : (star a * b).re = (star b * a).re := by
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  exact he _ _

end
end MainTheory.Orbit3CubicPermutation
