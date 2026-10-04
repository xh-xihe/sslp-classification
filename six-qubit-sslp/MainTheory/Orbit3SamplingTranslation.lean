import MainTheory.Orbit3SamplingHadamard
import MainTheory.Orbit3PermutationAverage

/-! # Translations reindex the actual sampler up to verified unit phases -/

namespace MainTheory.Orbit3SamplingTranslation

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3PhaseBlocks MainTheory.CubicPhaseProjection MainTheory.FinitePhaseAverage
open MainTheory.Orbit3CliffordAverage MainTheory.Orbit3SamplingHadamard
open MainTheory.ClassificationLevels MainTheory.PauliTransferTwo
open SixQubit.CodeEquiv SixQubit.Generated.SpectatorClifford
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def invertPhase (p : Fin 4) : Fin 4 := ![0, 3, 2, 1] p

theorem invertPhase_involutive : ∀ p : Fin 4, invertPhase (invertPhase p) = p := by
  decide +kernel

def phaseEquiv (f : SS.BitString 6) : (PhaseSite → Fin 4) ≃ (PhaseSite → Fin 4) where
  toFun p j := if bits f j then invertPhase (p j) else p j
  invFun p j := if bits f j then invertPhase (p j) else p j
  left_inv p := by
    funext j
    cases h : bits f j <;> simp [h, invertPhase_involutive]
  right_inv p := by
    funext j
    cases h : bits f j <;> simp [h, invertPhase_involutive]

theorem one_phase_flip (p : Fin 4) (a b : Bool) :
    Complex.I ^ (p.val * (if xor a b then (1 : Fin 4) else 0).val) =
      Complex.I ^ (p.val * (if b then (1 : Fin 4) else 0).val) *
        Complex.I ^ ((if b then invertPhase p else p).val *
          (if a then (1 : Fin 4) else 0).val) := by
  fin_cases p <;> cases a <;> cases b <;>
    norm_num [invertPhase, pow_succ]

theorem character_flipped (p : PhaseSite → Fin 4) (s f : SS.BitString 6) :
    character p (binaryProfile bits (SS.bxor s f)) =
      character p (binaryProfile bits f) *
        character (phaseEquiv f p) (binaryProfile bits s) := by
  unfold character binaryProfile
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [bits_bxor]
  exact one_phase_flip (p j) (bits s j) (bits f j)

theorem modulated_flipped (f : SS.BitString 6) (p : PhaseSite → Fin 4)
    (w : SS.State 6 ℂ) :
    flipAct f (modulated bits w p) =
      scal (character p (binaryProfile bits f))
        (modulated bits (flipAct f w) (phaseEquiv f p)) := by
  funext s
  unfold flipAct modulated scal
  rw [character_flipped]
  ring

theorem flip_composed (f q : SS.BitString 6) (w : SS.State 6 ℂ) :
    flipAct f (flipAct q w) = flipAct (SS.bxor f q) w := by
  funext s
  unfold flipAct
  rw [SS.bxor_assoc]

theorem spectator_kernel_flipped (f : SS.BitString 6) (hf : f 0 = false)
    (U : Mat2) (s t : SS.BitString 6) :
    oneQubitKernel 0 U (SS.bxor s f) (SS.bxor t f) = oneQubitKernel 0 U s t := by
  have hr : (∀ j : Fin 6, j ≠ 0 → (SS.bxor s f) j = (SS.bxor t f) j) ↔
      (∀ j : Fin 6, j ≠ 0 → s j = t j) := by
    constructor
    · intro h j hj
      have he := h j hj
      cases hs : s j <;> cases ht : t j <;> cases hfj : f j <;>
        simp_all [SS.bxor]
    · intro h j hj
      simp only [SS.bxor_apply, h j hj]
  unfold oneQubitKernel
  by_cases hst : ∀ j : Fin 6, j ≠ 0 → s j = t j
  · rw [if_pos (hr.mpr hst), if_pos hst]
    simp only [SS.bxor_apply, hf, Bool.xor_false]
  · have hx : ¬ (∀ j : Fin 6, j ≠ 0 → (SS.bxor s f) j = (SS.bxor t f) j) :=
      fun h => hst (hr.mp h)
    rw [if_neg hx, if_neg hst]

theorem spectator_act_flipped (f : SS.BitString 6) (hf : f 0 = false)
    (U : Mat2) (w : SS.State 6 ℂ) :
    flipAct f (act U w) = act U (flipAct f w) := by
  funext s
  unfold flipAct act kernelAction
  rw [← (SS.bxorEquiv f).sum_comp
    (fun t => oneQubitKernel 0 U (SS.bxor s f) t * w t)]
  apply Finset.sum_congr rfl
  intro t _
  change oneQubitKernel 0 U (SS.bxor s f) (SS.bxor t f) * w (SS.bxor t f) =
    oneQubitKernel 0 U s t * w (SS.bxor t f)
  rw [spectator_kernel_flipped f hf]

def activeIndexEquiv (f : SS.BitString 6) : Index ≃ Index :=
  Equiv.prodCongr
    (Equiv.prodCongr (Equiv.refl ActivePermutation)
      (Equiv.prodCongr (SS.bxorEquiv f) (Equiv.refl (Fin 24))))
    (phaseEquiv f)

theorem active_wave_flipped (f : SS.BitString 6) (hf : f 0 = false)
    (W : Encoder) (g : Index) :
    flipAct f (wave W g) =
      scal (character g.2 (binaryProfile bits f)) (wave W (activeIndexEquiv f g)) := by
  rw [wave_formula, modulated_flipped, baseWave_formula, spectator_act_flipped f hf,
    flip_composed, SS.bxor_comm f g.1.2.1, wave_formula, baseWave_formula]
  rfl

theorem sampling_active_flip (f : SS.BitString 6) (hf : f 0 = false)
    (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (W : Encoder) :
    (∑ g : Index, F (flipAct f (wave W g))) = ∑ g : Index, F (wave W g) := by
  have hp (g : Index) : F (flipAct f (wave W g)) =
      F (wave W (activeIndexEquiv f g)) := by
    rw [active_wave_flipped f hf]
    exact hF _ _ (MainTheory.Orbit3PhasePreservation.character_unit _ _)
  simp_rw [hp]
  exact (activeIndexEquiv f).sum_comp (fun g => F (wave W g))

end
end MainTheory.Orbit3SamplingTranslation
