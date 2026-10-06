import MainTheory.Orbit3ActualSampling

/-! # Active permutations reindex the complete actual sampler

The physical permutation need not fix the input encoder. It induces an
explicit bijection of the sampler's permutation, translation and phase
parameters, while commuting with the spectator Clifford factor.
-/

namespace MainTheory.Orbit3PermutationAverage

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3PhaseBlocks MainTheory.CubicPhaseProjection MainTheory.FinitePhaseAverage
open MainTheory.OrderTwoScalarBridge MainTheory.Orbit3CliffordAverage
open MainTheory.ClassificationLevels MainTheory.PauliTransferTwo
open SixQubit.CodeEquiv
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem mask_zero : ∀ j : Fin 6, orbit3Mask j = false ↔ j = 0 := by decide +kernel

theorem fixes_zero (σ : ActivePermutation) : σ.val 0 = 0 := by
  apply (mask_zero _).mp
  exact (σ.property 0).trans (by decide)

theorem inverse_property (σ : ActivePermutation) (j : Fin 6) :
    orbit3Mask (σ.val.symm j) = orbit3Mask j := by
  have h := σ.property (σ.val.symm j)
  simpa only [Equiv.apply_symm_apply] using h.symm

def composeActive (σ : ActivePermutation) : ActivePermutation ≃ ActivePermutation where
  toFun τ := ⟨σ.val * τ.val, fun j => (σ.property (τ.val j)).trans (τ.property j)⟩
  invFun τ := ⟨σ.val.symm * τ.val, fun j => (inverse_property σ (τ.val j)).trans (τ.property j)⟩
  left_inv τ := by
    apply Subtype.ext
    ext j
    simp
  right_inv τ := by
    apply Subtype.ext
    ext j
    simp

def siteEquiv (σ : ActivePermutation) : PhaseSite ≃ PhaseSite :=
  Equiv.sumCongr σ.val (Equiv.refl Unit)

def phaseEquiv (σ : ActivePermutation) : (PhaseSite → Fin 4) ≃ (PhaseSite → Fin 4) where
  toFun p j := p ((siteEquiv σ).symm j)
  invFun p j := p (siteEquiv σ j)
  left_inv p := by funext j; simp
  right_inv p := by funext j; simp

def indexEquiv (σ : ActivePermutation) : Index ≃ Index :=
  Equiv.prodCongr
    (Equiv.prodCongr (composeActive σ)
      (Equiv.prodCongr (permStrEquiv σ.val.symm) (Equiv.refl (Fin 24))))
    (phaseEquiv σ)

theorem bits_permuted (σ : ActivePermutation) (s : SS.BitString 6) (j : PhaseSite) :
    bits (permStr σ.val s) j = bits s (siteEquiv σ j) := by
  cases j with
  | inl j => rfl
  | inr j => exact MainTheory.Orbit3ActivePermutation.parity_permutation σ.val σ.property s

theorem character_permuted (σ : ActivePermutation) (p : PhaseSite → Fin 4) (s : SS.BitString 6) :
    character p (binaryProfile bits (permStr σ.val s)) =
      character (phaseEquiv σ p) (binaryProfile bits s) := by
  unfold character binaryProfile
  simp_rw [bits_permuted]
  have h := (siteEquiv σ).prod_comp (fun j => Complex.I ^
    ((p ((siteEquiv σ).symm j)).val * (if bits s j then (1 : Fin 4) else 0).val))
  simpa only [Equiv.symm_apply_apply] using h

theorem modulated_permuted (σ : ActivePermutation) (p : PhaseSite → Fin 4) (w : SS.State 6 ℂ) :
    permAct σ.val (modulated bits w p) =
      modulated bits (permAct σ.val w) (phaseEquiv σ p) := by
  funext s
  unfold permAct modulated
  rw [character_permuted]

theorem spectator_kernel_permuted (σ : ActivePermutation) (U : Mat2) (s t : SS.BitString 6) :
    oneQubitKernel 0 U (permStr σ.val s) (permStr σ.val t) = oneQubitKernel 0 U s t := by
  have hr : (∀ j : Fin 6, j ≠ 0 → s (σ.val j) = t (σ.val j)) ↔
      (∀ j : Fin 6, j ≠ 0 → s j = t j) := by
    constructor
    · intro h j hj
      have hn : σ.val.symm j ≠ 0 := by
        intro he
        have hx := congrArg σ.val he
        apply hj
        simpa only [Equiv.apply_symm_apply, fixes_zero] using hx
      simpa only [Equiv.apply_symm_apply] using h (σ.val.symm j) hn
    · intro h j hj
      have hn : σ.val j ≠ 0 := by
        intro he
        apply hj
        apply σ.val.injective
        exact he.trans (fixes_zero σ).symm
      exact h (σ.val j) hn
  simp only [oneQubitKernel, permStr, hr, fixes_zero]

theorem act_permuted (σ : ActivePermutation) (U : Mat2) (w : SS.State 6 ℂ) :
    permAct σ.val (act U w) = act U (permAct σ.val w) := by
  funext s
  unfold permAct act kernelAction
  rw [← (permStrEquiv σ.val).sum_comp
    (fun t => oneQubitKernel 0 U (permStr σ.val s) t * w t)]
  apply Finset.sum_congr rfl
  intro t _
  change oneQubitKernel 0 U (permStr σ.val s) (permStr σ.val t) * w (permStr σ.val t) =
    oneQubitKernel 0 U s t * w (permStr σ.val t)
  rw [spectator_kernel_permuted]

theorem flip_permuted (σ : ActivePermutation) (f : SS.BitString 6) (w : SS.State 6 ℂ) :
    permAct σ.val (flipAct f w) = flipAct (permStr σ.val.symm f) (permAct σ.val w) := by
  funext s
  unfold permAct flipAct
  congr 1
  funext j
  simp [permStr, SS.bxor]

theorem act_composed (σ τ : Equiv.Perm (Fin 6)) (w : SS.State 6 ℂ) :
    permAct σ (permAct τ w) = permAct (σ * τ) w := rfl

theorem wave_permuted (σ : ActivePermutation) (W : Encoder) (g : Index) :
    permAct σ.val (wave W g) = wave W (indexEquiv σ g) := by
  calc
    _ = modulated bits (permAct σ.val (baseWave W g.1)) (phaseEquiv σ g.2) := by
      rw [wave_formula, modulated_permuted]
    _ = _ := by
      rw [baseWave_formula, act_permuted, flip_permuted, act_composed,
        wave_formula, baseWave_formula]
      rfl

theorem sampling_permutation_identity (σ : ActivePermutation) (F : SS.State 6 ℂ → ℝ) (W : Encoder) :
    (∑ g : Index, F (permAct σ.val (wave W g))) = ∑ g : Index, F (wave W g) := by
  simp_rw [wave_permuted]
  exact (indexEquiv σ).sum_comp (fun g => F (wave W g))

end
end MainTheory.Orbit3PermutationAverage
