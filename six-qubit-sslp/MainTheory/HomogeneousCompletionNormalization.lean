import MainTheory.CompletionCodeBridge
import MainTheory.CubeCompletionTransport
import MainTheory.CodeSpec

/-! Normalize an arbitrary common positive column norm, preserving full KL. -/

namespace MainTheory.HomogeneousCompletionNormalization
noncomputable section
open MainTheory.CubeCompletionTransport MainTheory.CubeAction
open scoped BigOperators

variable {n : ℕ} {F : FiberPair n}

structure Raw (F : FiberPair n) where
  states : Fin 2 → SS.State n ℂ
  norm : ℝ
  positive : 0 < norm
  supported : ∀ k x, x ∉ F (finColor k) → states k x=0
  norms : ∀ k, SS.innerC (states k) (states k)=(norm : ℂ)
  hasDistance : SS.HasDistance states 3

def scalar (R : Raw F) : ℂ := ((Real.sqrt R.norm)⁻¹ : ℝ)

theorem scalar_star (R : Raw F) : star (scalar R)=scalar R := by simp [scalar]

theorem scalar_product (R : Raw F) : scalar R*scalar R=(R.norm : ℂ)⁻¹ := by
  have h : ((Real.sqrt R.norm)⁻¹)^2=R.norm⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt R.positive)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_mul,
    scalar, pow_two] using hc

def normalizedStates (R : Raw F) : Fin 2 → SS.State n ℂ :=
  fun k => scalar R • R.states k

theorem inner (R : Raw F) (j k : Fin 2) (P : SS.PauliString n) :
    SS.innerC (normalizedStates R j) (SS.pauliAct P (normalizedStates R k))=
      (R.norm : ℂ)⁻¹*SS.innerC (R.states j) (SS.pauliAct P (R.states k)) := by
  rw [normalizedStates, normalizedStates, MainTheory.CodeSpec.pauliAct_smul,
    MainTheory.CodeSpec.innerC_smul_left, MainTheory.CodeSpec.innerC_smul_right,
    scalar_star, ← mul_assoc, scalar_product]

theorem norms (R : Raw F) (k : Fin 2) :
    SS.innerC (normalizedStates R k) (normalizedStates R k)=1 := by
  rw [normalizedStates, MainTheory.CodeSpec.innerC_smul_left,
    MainTheory.CodeSpec.innerC_smul_right, scalar_star, ← mul_assoc, scalar_product,
    R.norms]
  have h : (R.norm : ℂ)≠0 := by exact_mod_cast ne_of_gt R.positive
  exact inv_mul_cancel₀ h

theorem full_KL (R : Raw F) : SS.HasDistance (normalizedStates R) 3 := by
  intro P hw
  obtain ⟨c,hc⟩ := R.hasDistance P hw
  refine ⟨(R.norm : ℂ)⁻¹*c, ?_⟩
  intro j k
  rw [inner, hc]
  by_cases h : j=k <;> simp [h]

def completion (R : Raw F) : Completion F where
  states := normalizedStates R
  supported := by
    intro k x hx
    simp only [normalizedStates, Pi.smul_apply, smul_eq_mul, R.supported k x hx,
      mul_zero]
  normalized := norms R
  hasDistance := full_KL R

theorem trProj (R : Raw F) (P : SS.PauliString n) :
    SS.MacWilliams.trProj (completion R).states P=
      (R.norm : ℂ)⁻¹*SS.MacWilliams.trProj R.states P := by
  unfold SS.MacWilliams.trProj
  change (∑ k, SS.innerC (normalizedStates R k)
    (SS.pauliAct P (normalizedStates R k)))=_
  simp only [inner, Finset.mul_sum]

theorem enumerator (R : Raw F) (w : ℕ) :
    SS.MacWilliams.Aco (completion R).states w=
      SS.MacWilliams.Aco R.states w/R.norm^2 := by
  unfold SS.MacWilliams.Aco
  simp_rw [trProj, Complex.normSq_mul]
  rw [← Finset.mul_sum]
  simp [Complex.normSq_ofReal, pow_two, div_eq_mul_inv]
  ring

end
end MainTheory.HomogeneousCompletionNormalization
