import MainTheory.Orbit3AmplitudeNormalization
import MainTheory.HomogeneousCompletionNormalization

/-! Literal sqrt-two amplitude and positive-column-norm projector formulas.
These identities do not use the final orbit-three A3-vanishing theorem.
-/

namespace MainTheory.Orbit3PrintedAmplitudes
noncomputable section
open MainTheory.CodeSpec MainTheory.HomogeneousCompletionNormalization
open SixQubit.ParityLogicalState SixQubit.ParityPauliScalars SS.MacWilliams
open scoped BigOperators

def scale : ℝ := (Real.sqrt 2)⁻¹

theorem scale_product : scale * scale = 1/2 := by
  unfold scale
  rw [← pow_two, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sqrt_scale : Real.sqrt 2 * scale = 1 := by
  unfold scale
  exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

def w {n : ℕ} (psi : Fin 2 → SS.State n ℂ) : SS.State n ℂ :=
  (scale : ℂ) • superposition psi

def sector {n : ℕ} (mask : SS.BitString n) (k : Fin 2) (f : SS.State n ℂ) :
    SS.State n ℂ := fun s => if SS.bdot mask s = (k == 1) then f s else 0

theorem reconstruct {n : ℕ} (psi : Fin 2 → SS.State n ℂ) (mask : SS.BitString n)
    (hp : ParityPair mask psi) (k : Fin 2) :
    (Real.sqrt 2 : ℂ) • sector mask k (w psi) = psi k := by
  funext s
  have h0 : SS.bdot mask s = true → psi 0 s = 0 := by
    intro hs
    apply hp 0 s
    norm_num [chi_bdot, hs, logicalSign]
  have h1 : SS.bdot mask s = false → psi 1 s = 0 := by
    intro hs
    apply hp 1 s
    norm_num [chi_bdot, hs, logicalSign]
  have hc : (Real.sqrt 2 : ℂ) * (scale : ℂ) = 1 := by
    exact_mod_cast sqrt_scale
  fin_cases k <;> cases hs : SS.bdot mask s <;>
    simp [sector, w, superposition, hs, h0, h1, ← mul_assoc, hc]

theorem expectation {n : ℕ} (psi : Fin 2 → SS.State n ℂ) (P : SS.PauliString n) :
    SS.innerC (w psi) (SS.pauliAct P (w psi)) =
      (1/2 : ℂ) *
        (SS.innerC (psi 0) (SS.pauliAct P (psi 0)) +
         SS.innerC (psi 0) (SS.pauliAct P (psi 1)) +
         SS.innerC (psi 1) (SS.pauliAct P (psi 0)) +
         SS.innerC (psi 1) (SS.pauliAct P (psi 1))) := by
  rw [w, pauliAct_smul, innerC_smul_left, innerC_smul_right]
  have hc : star (scale : ℂ) * (scale : ℂ) = (1/2 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, scale_product]
    norm_num
  rw [← mul_assoc, hc]
  unfold superposition
  change (1/2 : ℂ) * SS.innerC (psi 0 + psi 1)
    (SS.pauliAct P (psi 0 + psi 1)) = _
  rw [pauliAct_add, innerC_add_left, innerC_add_right, innerC_add_right]
  ring

theorem commuting_expectation {n : ℕ} (psi : Fin 2 → SS.State n ℂ)
    {mask : SS.BitString n} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hP : chi mask P.x = 1) :
    SS.innerC (w psi) (SS.pauliAct P (w psi)) = trProj psi P / 2 := by
  obtain ⟨h01, h10⟩ := offdiag_zero hp P hP
  rw [expectation]
  simp only [SS.MacWilliams.trProj, Fin.sum_univ_two, innerC_eq_mel, h01, h10,
    mul_zero, add_zero]
  ring

theorem norm_common {n : ℕ} (psi : Fin 2 → SS.State n ℂ) (N : ℝ)
    (h0 : SS.innerC (psi 0) (psi 0) = N)
    (h1 : SS.innerC (psi 1) (psi 1) = N)
    (h01 : SS.innerC (psi 0) (psi 1) = 0)
    (h10 : SS.innerC (psi 1) (psi 0) = 0) :
    SS.innerC (w psi) (w psi) = N := by
  rw [w, innerC_smul_left, innerC_smul_right]
  have hc : star (scale : ℂ) * (scale : ℂ) = (1/2 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, scale_product]
    norm_num
  rw [← mul_assoc, hc]
  unfold superposition
  change (1/2 : ℂ) * SS.innerC (psi 0 + psi 1) (psi 0 + psi 1) = _
  rw [innerC_add_left, innerC_add_right, innerC_add_right, h0, h1, h01, h10]
  ring

theorem raw_orthogonal {n : ℕ} {F : MainTheory.CubeAction.FiberPair n} (R : Raw F) :
    SS.innerC (R.states 0) (R.states 1) = 0 ∧
    SS.innerC (R.states 1) (R.states 0) = 0 := by
  obtain ⟨c, hc⟩ := R.hasDistance MainTheory.CompletionCodeBridge.identity
    (by rw [MainTheory.CompletionCodeBridge.identity_weight]; decide)
  constructor
  · simpa only [MainTheory.CompletionCodeBridge.identity_act,
      show (0 : Fin 2) ≠ 1 from by decide, if_false] using hc 0 1
  · simpa only [MainTheory.CompletionCodeBridge.identity_act,
      show (1 : Fin 2) ≠ 0 from by decide, if_false] using hc 1 0

theorem raw_norm {n : ℕ} {F : MainTheory.CubeAction.FiberPair n} (R : Raw F) :
    SS.innerC (w R.states) (w R.states) = R.norm :=
  norm_common R.states R.norm (R.norms 0) (R.norms 1)
    (raw_orthogonal R).1 (raw_orthogonal R).2

theorem raw_projector {n : ℕ} {F : MainTheory.CubeAction.FiberPair n} (R : Raw F)
    (s t : SS.BitString n) :
    projectorKernel (MainTheory.CompletionCodeBridge.frame (completion R)) s t =
      (R.states 0 s * star (R.states 0 t) +
       R.states 1 s * star (R.states 1 t)) / (R.norm : ℂ) := by
  simp only [projectorKernel, MainTheory.CompletionCodeBridge.frame, completion,
    normalizedStates, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, star_mul,
    scalar_star]
  calc
    _ = (scalar R * scalar R) *
      (R.states 0 s * star (R.states 0 t) + R.states 1 s * star (R.states 1 t)) := by ring
    _ = _ := by rw [scalar_product]; ring

end
end MainTheory.Orbit3PrintedAmplitudes
