import MainTheory.Orbit3Translation
import MainTheory.Orbit3ActivePermutation
import MainTheory.Orbit3CliffordAverage
import MainTheory.Orbit3AmplitudeNormalization
import MainTheory.Orbit3SpinForm
import MainTheory.Orbit3PositiveMoments
import SixQubit.Generated.Orbit3PauliConstraints

/-! # Finite sampling of genuine orbit-3 encoders

Every sample is constructed as a normalized distance-three completion.
Consequently the KL products and spin multipliers vanish at every sample,
and the cubic Gram matrix is positive without caller-supplied row or PSD
hypotheses. Reduction to the 269 certificate coordinates is still separate.
-/

namespace MainTheory.Orbit3ActualSampling

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3PhaseBlocks
open MainTheory.OrderTwoScalarBridge MainTheory.CubicPhaseProjection
open MainTheory.ClassificationLevels MainTheory.Orbit3CliffordAverage
open MainTheory.FiniteCubicMoments SixQubit.ParityLogicalState SixQubit.CodeEquiv
open SixQubit.Generated.SpectatorClifford
open scoped Matrix BigOperators

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev ActivePermutation := {σ : Equiv.Perm (Fin 6) // ∀ j, orbit3Mask (σ j) = orbit3Mask j}

instance : Fintype ActivePermutation := Fintype.ofFinite _

abbrev BaseIndex := ActivePermutation × SS.BitString 6 × Fin 24
abbrev Index := BaseIndex × (PhaseSite → Fin 4)

def baseEncoder (W : Encoder) (g : BaseIndex) : Encoder :=
  MainTheory.Orbit3SpectatorUnitary.transform
    (MainTheory.Orbit3Translation.transform
      (MainTheory.Orbit3ActivePermutation.transform W g.1.val g.1.property) g.2.1)
    (clifford g.2.2) (clifford_unitary g.2.2)

def sampleEncoder (W : Encoder) (g : Index) : Encoder :=
  MainTheory.Orbit3PhasePreservation.transform (baseEncoder W g.1) g.2

def baseWave (W : Encoder) (g : BaseIndex) : SS.State 6 ℂ :=
  superposition (baseEncoder W g).states

def wave (W : Encoder) (g : Index) : SS.State 6 ℂ :=
  superposition (sampleEncoder W g).states

theorem spectator_superposition (W : Encoder) (U : MainTheory.PauliTransferTwo.Mat2)
    (hU : IsOneQubitUnitary U) :
    superposition (MainTheory.Orbit3SpectatorUnitary.transform W U hU).states =
      act U (superposition W.states) := by
  unfold superposition
  rw [MainTheory.Orbit3SpectatorUnitary.transform_states,
    MainTheory.Orbit3SpectatorUnitary.transform_states]
  change (oneQubitKernel 0 U) *ᵥ W.states 0 + (oneQubitKernel 0 U) *ᵥ W.states 1 =
    (oneQubitKernel 0 U) *ᵥ (W.states 0 + W.states 1)
  exact (Matrix.mulVec_add _ _ _).symm

theorem baseWave_formula (W : Encoder) (g : BaseIndex) :
    baseWave W g = act (clifford g.2.2)
      (flipAct g.2.1 (permAct g.1.val (superposition W.states))) := by
  unfold baseWave baseEncoder
  rw [spectator_superposition, MainTheory.Orbit3Translation.translated_superposition,
    MainTheory.Orbit3ActivePermutation.permuted_superposition]

theorem wave_formula (W : Encoder) (g : Index) :
    wave W g = modulated bits (baseWave W g.1) g.2 :=
  MainTheory.Orbit3PhasePreservation.transformed_superposition _ _

theorem sample_norm (W : Encoder) (g : Index) :
    (∑ s, Complex.normSq (wave W g s)) = 2 :=
  MainTheory.Orbit3AmplitudeNormalization.normSq_sum (sampleEncoder W g)

theorem sample_constrained_zero (W : Encoder) (g : Index) (P : SS.PauliString 6)
    (hP : MainTheory.Orbit3PauliZeros.Constrained P) :
    SS.innerC (wave W g) (SS.pauliAct P (wave W g)) = 0 :=
  MainTheory.Orbit3PauliZeros.constrained_expectation_zero (sampleEncoder W g) P hP

theorem kl_product_sum_zero (W : Encoder) (i : Fin 211)
    (hi : SixQubit.Generated.Orbit3PauliConstraints.kind i = 0) :
    (∑ g : Index, (∏ k : Fin 3, SS.innerC (wave W g)
      (SS.pauliAct (MainTheory.Orbit3PauliZeros.decode
        (SixQubit.Generated.Orbit3PauliConstraints.labels i k)) (wave W g))).re) = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  rw [show (∏ k : Fin 3, SS.innerC (wave W g)
      (SS.pauliAct (MainTheory.Orbit3PauliZeros.decode
        (SixQubit.Generated.Orbit3PauliConstraints.labels i k)) (wave W g))) = 0 from
    SixQubit.Generated.Orbit3PauliConstraints.all_kl_multiplier_products_zero
      (sampleEncoder W g) i hi]
  rfl

theorem spin_multiplier_sum_zero (W : Encoder)
    (t : SS.BitString 6 × SS.BitString 6 × SS.BitString 6) (v : SS.BitString 6) :
    (∑ g : Index, (star (wave W g t.1 * wave W g t.2.1 * wave W g t.2.2) *
      MainTheory.Orbit3SpinForm.spin (wave W g) * wave W g v).re) = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  rw [show star (wave W g t.1 * wave W g t.2.1 * wave W g t.2.2) *
      MainTheory.Orbit3SpinForm.spin (wave W g) * wave W g v = 0 from
    MainTheory.Orbit3SpinForm.spin_multiplier_zero (sampleEncoder W g) t v]
  rfl

def pairMoment (W : Encoder) : Matrix (SS.BitString 6 × SS.BitString 6)
    (SS.BitString 6 × SS.BitString 6) ℝ :=
  cubicMoment (fun t => triple t.1 t.2) (wave W)

theorem pairMoment_posSemidef (W : Encoder) : (pairMoment W).PosSemidef :=
  cubicMoment_posSemidef _ _

theorem pairMoment_formula (W : Encoder) (a b c d : SS.BitString 6) :
    pairMoment W (a, b) (c, d) = ∑ g : BaseIndex,
      if block a b = block c d then (4 : ℝ) ^ 7 *
        (star (baseWave W g a * baseWave W g b * baseWave W g (SS.bxor a b)) *
          (baseWave W g c * baseWave W g d * baseWave W g (SS.bxor c d))).re else 0 := by
  unfold pairMoment
  rw [cubicMoment_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  change (∑ p : PhaseSite → Fin 4,
    (star (wave W (g, p) a * wave W (g, p) b * wave W (g, p) (SS.bxor a b)) *
      (wave W (g, p) c * wave W (g, p) d * wave W (g, p) (SS.bxor c d))).re) = _
  simp_rw [wave_formula]
  have hm := physical_moment_apply (baseWave W g) a b c d
  rw [MainTheory.CubicPhaseProjection.moment, cubicMoment_apply] at hm
  exact hm

theorem pairMoment_zero_outside_block (W : Encoder) (a b c d : SS.BitString 6)
    (h : block a b ≠ block c d) : pairMoment W (a, b) (c, d) = 0 := by
  rw [pairMoment_formula]
  simp [h]

theorem positiveSquareMoment_posSemidef (W : Encoder) :
    (MainTheory.Orbit3PositiveMoments.actualMoment (wave W)).PosSemidef :=
  MainTheory.Orbit3PositiveMoments.actualMoment_posSemidef _

end
end MainTheory.Orbit3ActualSampling
