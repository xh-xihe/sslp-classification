import MainTheory.Orbit3SamplingHadamard

/-! # The actual sampled sextic target and recovery of the original encoder

Every summand is nonnegative. The sampler contains the original amplitude
vector up to the global sign of the canonical identity Clifford. Therefore
vanishing of the sampled target implies Aco3=0 for the original encoder;
no averaging-invariance of the original encoder is assumed.
-/

namespace MainTheory.Orbit3SamplingTarget

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3ActualSampling
open MainTheory.Orbit3CliffordAverage MainTheory.Orbit3SamplingHadamard
open MainTheory.CubicPhaseProjection MainTheory.FinitePhaseAverage
open MainTheory.PhysicalPauliCategories MainTheory.Orbit3Target
open SixQubit.CodeEquiv SixQubit.ParityLogicalState
open SixQubit.Generated.SpectatorClifford
open scoped BigOperators

noncomputable section

def term (w : SS.State 6 ℂ) : ℝ :=
  (∑ s, Complex.normSq (w s)) * ∑ P : SS.PauliString 6,
    if category P = targetCategory then (SS.innerC w (SS.pauliAct P w)).re ^ 2 else 0

theorem term_nonneg (w : SS.State 6 ℂ) : 0 ≤ term w := by
  apply mul_nonneg
  · exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · apply Finset.sum_nonneg
    intro P _
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

def target (W : Encoder) : ℝ := ∑ g : Index, term (wave W g)

theorem target_nonneg (W : Encoder) : 0 ≤ target W :=
  Finset.sum_nonneg fun _ _ => term_nonneg _

theorem target_eq_enumerator_sum (W : Encoder) :
    target W = 8 * ∑ g : Index, SS.MacWilliams.Aco (sampleEncoder W g).states 3 / 4 := by
  unfold target term
  have hs (g : Index) := MainTheory.Orbit3AmplitudeNormalization.homogeneous_target (sampleEncoder W g)
  simp_rw [show ∀ g : Index,
    (∑ s, Complex.normSq (wave W g s)) * ∑ P : SS.PauliString 6,
      (if category P = targetCategory then (SS.innerC (wave W g) (SS.pauliAct P (wave W g))).re ^ 2 else 0) =
      8 * (SS.MacWilliams.Aco (sampleEncoder W g).states 3 / 4) from hs]
  rw [Finset.mul_sum]

def originalIndex : Index :=
  ((⟨Equiv.refl _, by intro j; rfl⟩, (fun _ => false), 0), fun _ => 0)

theorem original_wave (W : Encoder) : wave W originalIndex = scal (-1) (superposition W.states) := by
  rw [wave_formula, baseWave_formula]
  have hp : permAct originalIndex.1.1.val (superposition W.states) = superposition W.states := rfl
  rw [hp]
  have hf : flipAct originalIndex.1.2.1 (superposition W.states) = superposition W.states := by
    funext s
    change superposition W.states (SS.bxor s (fun _ => false)) = superposition W.states s
    rw [SS.bxor_zero]
  rw [hf]
  have hc : clifford originalIndex.1.2.2 = (-1 : ℂ) • (1 : MainTheory.PauliTransferTwo.Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [originalIndex, clifford, C00, Matrix.smul_apply, Matrix.one_apply]
  rw [hc, act_smul, act_one]
  funext s
  simp [originalIndex, modulated, character]

theorem original_term (W : Encoder) : term (wave W originalIndex) = 8 * (SS.MacWilliams.Aco W.states 3 / 4) := by
  rw [original_wave]
  unfold term
  have hz : star (-1 : ℂ) * (-1 : ℂ) = 1 := by norm_num
  simp_rw [pauli_scalar_unit (-1) (superposition W.states) _ hz]
  simp only [scal, neg_one_mul, Complex.normSq_neg]
  exact MainTheory.Orbit3AmplitudeNormalization.homogeneous_target W

theorem original_Aco_zero_of_target_zero (W : Encoder) (h : target W = 0) :
    SS.MacWilliams.Aco W.states 3 = 0 := by
  have hz : term (wave W originalIndex) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => term_nonneg (wave W g))).mp h
      originalIndex (Finset.mem_univ _)
  rw [original_term] at hz
  linarith

end
end MainTheory.Orbit3SamplingTarget
