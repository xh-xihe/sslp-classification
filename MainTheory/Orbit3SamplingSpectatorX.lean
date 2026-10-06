import MainTheory.Orbit3SamplingTranslation

/-! # Spectator X and complete six-bit translation invariance

The complete average is invariant under S and H on the spectator.
The exact identity X = H S² H supplies the missing spectator translation;
the other five bit translations use the explicit sampler bijection.
-/

namespace MainTheory.Orbit3SamplingSpectatorX

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3PhaseBlocks MainTheory.CubicPhaseProjection
open MainTheory.Orbit3CliffordAverage MainTheory.Orbit3SamplingHadamard
open MainTheory.Orbit3SamplingTranslation MainTheory.Orbit3HadamardBridge
open MainTheory.ClassificationLevels MainTheory.PauliTransferTwo
open SixQubit.CodeEquiv SixQubit.Generated.SpectatorClifford
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem modulated_S (w : SS.State 6 ℂ) (p : PhaseSite → Fin 4) :
    act phaseGate (modulated bits w p) = modulated bits (act phaseGate w) p := by
  funext s
  simp only [act_S, modulated]
  ring

theorem sampling_S_identity (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (W : Encoder) :
    (∑ g : Index, F (act phaseGate (wave W g))) = ∑ g : Index, F (wave W g) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro f _
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [wave_formula, baseWave_formula, modulated_S]
  exact average_S (fun w => F (modulated bits w p)) (phase_stable_modulated F hF p) _

theorem sampling_S_power (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F)
    (n : ℕ) (W : Encoder) :
    (∑ g : Index, F (act (phaseGate ^ n) (wave W g))) = ∑ g : Index, F (wave W g) := by
  induction n with
  | zero => simp only [pow_zero, act_one]
  | succ n ih =>
    simp only [pow_succ, ← act_mul]
    exact (sampling_S_identity (fun w => F (act (phaseGate ^ n) w))
      (phase_stable_act F hF _) W).trans ih

theorem HSH_X : hadamard * phaseGate ^ 2 * hadamard = pauli 1 := by
  have hs : phaseGate ^ 2 = pauli 3 := by
    change phaseGate ^ 2 = !![1, 0; 0, -1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [phaseGate, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hh : star hadamard = hadamard := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamard, Matrix.star_apply, root_star]
  rw [hs, ← hh]
  simpa [hSign, hLetter, hh] using local_H (3 : Fin 4)

def spectatorFlip : SS.BitString 6 := fun j => decide (j = 0)

theorem spectator_flip_entry_relation : ∀ s t : SS.BitString 6,
    ((∀ j : Fin 6, j ≠ 0 → s j = t j) ∧ s 0 ≠ t 0) ↔
      t = SS.bxor s spectatorFlip := by
  decide +kernel

theorem spectator_X_kernel (s t : SS.BitString 6) :
    oneQubitKernel 0 (pauli 1) s t = if t = SS.bxor s spectatorFlip then 1 else 0 := by
  have he : pauli 1 (bitIndex (s 0)) (bitIndex (t 0)) = if s 0 ≠ t 0 then 1 else 0 := by
    cases s 0 <;> cases t 0 <;> simp [pauli, bitIndex]
  unfold oneQubitKernel
  rw [he, ← ite_and]
  simp only [spectator_flip_entry_relation]

theorem spectator_X_act (w : SS.State 6 ℂ) :
    act (pauli 1) w = flipAct spectatorFlip w := by
  funext s
  simp [act, kernelAction, spectator_X_kernel, flipAct]

theorem sampling_spectator_flip (F : SS.State 6 ℂ → ℝ)
    (hF : PhaseStable F) (W : Encoder) :
    (∑ g : Index, F (flipAct spectatorFlip (wave W g))) = ∑ g : Index, F (wave W g) := by
  have h : (∑ g : Index, F (act hadamard
      (act (phaseGate ^ 2) (act hadamard (wave W g))))) =
      ∑ g : Index, F (wave W g) := by
    calc
      _ = ∑ g : Index, F (act hadamard (act (phaseGate ^ 2) (wave W g))) :=
        sampling_H_identity (fun w => F (act hadamard (act (phaseGate ^ 2) w)))
          (phase_stable_act _ (phase_stable_act F hF hadamard) _) W
      _ = ∑ g : Index, F (act hadamard (wave W g)) :=
        sampling_S_power (fun w => F (act hadamard w))
          (phase_stable_act F hF hadamard) 2 W
      _ = _ := sampling_H_identity F hF W
  simpa only [act_mul, ← mul_assoc, HSH_X, spectator_X_act] using h

theorem phase_stable_flip (f : SS.BitString 6) (F : SS.State 6 ℂ → ℝ)
    (hF : PhaseStable F) : PhaseStable (fun w => F (flipAct f w)) := by
  intro z w hz
  change F (flipAct f (scal z w)) = F (flipAct f w)
  have he : flipAct f (scal z w) = scal z (flipAct f w) := rfl
  rw [he]
  exact hF _ _ hz

theorem sampling_translation_identity (f : SS.BitString 6)
    (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (W : Encoder) :
    (∑ g : Index, F (flipAct f (wave W g))) = ∑ g : Index, F (wave W g) := by
  cases hf : f 0 with
  | false => exact sampling_active_flip f hf F hF W
  | true =>
    let a : SS.BitString 6 := Function.update f 0 false
    have ha : a 0 = false := by simp [a]
    have hfa : SS.bxor a spectatorFlip = f := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp [a, SS.bxor, spectatorFlip, hf]
      · simp [a, SS.bxor, spectatorFlip, hj]
    calc
      _ = ∑ g : Index, F (flipAct a (flipAct spectatorFlip (wave W g))) := by
        simp_rw [flip_composed, hfa]
      _ = ∑ g : Index, F (flipAct a (wave W g)) :=
        sampling_spectator_flip (fun w => F (flipAct a w)) (phase_stable_flip a F hF) W
      _ = _ := sampling_active_flip a ha F hF W

end
end MainTheory.Orbit3SamplingSpectatorX
