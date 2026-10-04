import MainTheory.Orbit3ActualSampling
import MainTheory.Orbit3CubicPhaseStability
import SixQubit.Generated.Orbit3HadamardConstraints

/-! # Hadamard invariance after all actual orbit-3 sampling phases

The spectator phase is absorbed in the verified finite Clifford average.
The other six phase coordinates commute with every spectator matrix.
Consequently all three physical Ward rows vanish for the complete sampler,
before their separate interpretation in reduced certificate coordinates.
-/

namespace MainTheory.Orbit3SamplingHadamard

open MainTheory.ClassificationLevels MainTheory.PauliTransferTwo
open MainTheory.Orbit3ActualSampling MainTheory.Orbit3CliffordAverage
open MainTheory.Orbit3HadamardBridge MainTheory.Orbit3PhaseBlocks
open MainTheory.CubicPhaseProjection MainTheory.FinitePhaseAverage
open SixQubit.CodeEquiv SixQubit.Generated.SpectatorClifford
open SixQubit.ParityLogicalState MainTheory.Orbit3ScalarCategoryRealization
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem act_scalar (U : Mat2) (z : ℂ) (w : SS.State 6 ℂ) :
    act U (scal z w) = scal z (act U w) := by
  funext s
  unfold act kernelAction scal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem phase_stable_act (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (U : Mat2) :
    PhaseStable (fun w => F (act U w)) := by
  intro z w hz
  change F (act U (scal z w)) = F (act U w)
  rw [act_scalar]
  exact hF z _ hz

theorem act_one (w : SS.State 6 ℂ) : act (1 : Mat2) w = w := by
  unfold act
  rw [← MainTheory.LocalTensorKernel.tensorKernel_single]
  have hu : Function.update (fun _ : Fin 6 => (1 : Mat2)) 0 1 = fun _ => 1 :=
    Function.update_eq_self _ _
  rw [hu, MainTheory.LocalTensorKernel.tensorKernel_one]
  funext s
  simp [kernelAction, Matrix.one_apply]

theorem act_S (w : SS.State 6 ℂ) (s : SS.BitString 6) :
    act phaseGate w s = (if s 0 then Complex.I else 1) * w s := by
  have hk : oneQubitKernel (n := 6) 0 phaseGate =
      Matrix.diagonal (fun s => if s 0 then Complex.I else 1) := by
    ext s t
    by_cases hst : s = t
    · subst t
      cases hs : s 0 <;> simp [oneQubitKernel, phaseGate, bitIndex, hs]
    · rw [Matrix.diagonal_apply_ne _ hst]
      unfold oneQubitKernel
      split_ifs with hr
      · have h0 : s 0 ≠ t 0 := by
          intro he
          apply hst
          funext j
          by_cases hj : j = 0
          · subst j
            exact he
          · exact hr j hj
        cases hs : s 0 <;> cases ht : t 0 <;>
          simp_all [phaseGate, bitIndex]
      · rfl
  unfold act
  rw [hk]
  simp [kernelAction, Matrix.diagonal_apply]

theorem act_S_power (n : ℕ) (w : SS.State 6 ℂ) (s : SS.BitString 6) :
    act (phaseGate ^ n) w s = (if s 0 then Complex.I ^ n else 1) * w s := by
  induction n with
  | zero => rw [pow_zero, act_one]; simp
  | succ n ih =>
    rw [pow_succ', ← act_mul, act_S, ih]
    cases s 0 <;> simp [pow_succ', mul_assoc]

def eraseSpectatorPhase (p : PhaseSite → Fin 4) : PhaseSite → Fin 4 :=
  Function.update p (.inl 0) 0

theorem phase_character_split (p : PhaseSite → Fin 4) (s : SS.BitString 6) :
    character p (binaryProfile bits s) =
      (if s 0 then Complex.I ^ (p (.inl 0)).val else 1) *
        character (eraseSpectatorPhase p) (binaryProfile bits s) := by
  unfold character
  have hf : (fun j => Complex.I ^ ((eraseSpectatorPhase p j).val *
      (binaryProfile bits s j).val)) =
      Function.update (fun j => Complex.I ^ ((p j).val * (binaryProfile bits s j).val))
        (.inl 0) 1 := by
    funext j
    by_cases hj : j = (.inl (0 : Fin 6))
    · subst j
      simp [eraseSpectatorPhase]
    · simp only [eraseSpectatorPhase, Function.update_of_ne hj]
  rw [hf]
  let f : PhaseSite → ℂ := fun j => Complex.I ^ ((p j).val * (binaryProfile bits s j).val)
  change (∏ j, f j) = (if s 0 then Complex.I ^ (p (.inl 0)).val else 1) *
    ∏ j, Function.update f (.inl 0) 1 j
  rw [Finset.prod_update_of_mem (Finset.mem_univ (.inl (0 : Fin 6))) f 1]
  have hprod := Finset.prod_update_of_mem (Finset.mem_univ (.inl (0 : Fin 6)))
    f (f (.inl 0))
  rw [Function.update_eq_self] at hprod
  rw [hprod]
  have he : f (.inl 0) = if s 0 then Complex.I ^ (p (.inl 0)).val else 1 := by
    by_cases hs : s 0 = true <;> simp [f, binaryProfile, bits, hs]
  rw [he, one_mul]

theorem modulated_split (p : PhaseSite → Fin 4) (w : SS.State 6 ℂ) :
    modulated bits w p = modulated bits (act (phaseGate ^ (p (.inl 0)).val) w)
      (eraseSpectatorPhase p) := by
  funext s
  unfold modulated
  rw [phase_character_split, act_S_power]
  ring

theorem spectator_profile : ∀ s t : SS.BitString 6,
    (∀ j : Fin 6, j ≠ 0 → s j = t j) →
    ∀ j : PhaseSite, j ≠ .inl 0 → binaryProfile bits s j = binaryProfile bits t j := by
  decide +kernel

theorem erased_character_equal (p : PhaseSite → Fin 4) (s t : SS.BitString 6)
    (hr : ∀ j : Fin 6, j ≠ 0 → s j = t j) :
    character (eraseSpectatorPhase p) (binaryProfile bits s) =
      character (eraseSpectatorPhase p) (binaryProfile bits t) := by
  unfold character
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = (.inl (0 : Fin 6))
  · subst j
    simp [eraseSpectatorPhase]
  · rw [spectator_profile s t hr j hj]

theorem erased_phase_commutes (p : PhaseSite → Fin 4) (U : Mat2) (w : SS.State 6 ℂ) :
    act U (modulated bits w (eraseSpectatorPhase p)) =
      modulated bits (act U w) (eraseSpectatorPhase p) := by
  funext s
  unfold act kernelAction modulated
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hr : ∀ j : Fin 6, j ≠ 0 → s j = t j
  · rw [← erased_character_equal p s t hr]
    ring
  · simp only [oneQubitKernel, hr, if_false, zero_mul, mul_zero]

theorem phase_stable_modulated (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F)
    (p : PhaseSite → Fin 4) : PhaseStable (fun w => F (modulated bits w p)) := by
  intro z w hz
  change F (modulated bits (scal z w) p) = F (modulated bits w p)
  have hs : modulated bits (scal z w) p = scal z (modulated bits w p) := by
    funext s
    unfold modulated scal
    ring
  rw [hs]
  exact hF z _ hz

theorem average_S_power (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (n : ℕ)
    (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, F (act (phaseGate ^ n) (act (clifford g) w))) =
      ∑ g : Fin 24, F (act (clifford g) w) := by
  induction n with
  | zero => simp only [pow_zero, act_one]
  | succ n ih =>
    simp only [pow_succ, ← act_mul]
    exact (average_S (fun v => F (act (phaseGate ^ n) v)) (phase_stable_act F hF _) w).trans ih

theorem average_phases_H (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F)
    (p : PhaseSite → Fin 4) (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, F (act hadamard (modulated bits (act (clifford g) w) p))) =
      ∑ g : Fin 24, F (modulated bits (act (clifford g) w) p) := by
  let E : SS.State 6 ℂ → ℝ := fun v => F (modulated bits v (eraseSpectatorPhase p))
  have hE : PhaseStable E := phase_stable_modulated F hF _
  have hh (v : SS.State 6 ℂ) : F (act hadamard (modulated bits v p)) =
      E (act hadamard (act (phaseGate ^ (p (.inl 0)).val) v)) := by
    rw [modulated_split p v, erased_phase_commutes]
  have hr (v : SS.State 6 ℂ) : F (modulated bits v p) =
      E (act (phaseGate ^ (p (.inl 0)).val) v) := by
    rw [modulated_split p v]
  simp_rw [hh, hr]
  change (∑ g : Fin 24, E (act hadamard
    (act (phaseGate ^ (p (.inl 0)).val) (act (clifford g) w)))) =
      ∑ g : Fin 24, E (act (phaseGate ^ (p (.inl 0)).val) (act (clifford g) w))
  rw [average_S_power (fun v => E (act hadamard v)) (phase_stable_act E hE _) _ w,
    average_S_power E hE _ w]
  exact average_H E hE w

theorem sampling_H_identity (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (W : Encoder) :
    (∑ g : Index, F (act hadamard (wave W g))) = ∑ g : Index, F (wave W g) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro f _
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [wave_formula, baseWave_formula]
  exact average_phases_H F hF p (flipAct f (permAct σ.val (superposition W.states)))

theorem sampling_H_Ward (P : Fin 3 → SS.PauliString 6) (W : Encoder) :
    (∑ g : Index, (product P (wave W g) -
      (productSign P : ℝ) * product (fun k => hPauli (P k)) (wave W g))) = 0 := by
  have h := sampling_H_identity _ (product_phase_stable P) W
  simp_rw [product_H] at h
  rw [Finset.sum_sub_distrib, ← h]
  simp

end
end MainTheory.Orbit3SamplingHadamard
