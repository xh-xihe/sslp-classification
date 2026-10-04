import Orbit2.CharacterBlocks

namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli

theorem localG_conjugation : ∀ s p, localG s * localG p * localG s =
    (character s p : GaussianInt) • localG p := by decide +kernel

theorem localC_conjugation (s p : Fin 4) : localC s * localC p * localC s =
    (character s p : ℂ) • localC p := by
  unfold localC
  rw [← Matrix.map_mul, ← Matrix.map_mul, localG_conjugation]
  ext x y
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, GaussianInt.toComplex_mul]

def signLabel (s p : Label 4) : ℤ := ∏ i, character (s i) (p i)

/-- Conjugation signs used in the coefficient shortcut follow from actual matrices. -/
theorem operator_conjugation (s p : Label 4) :
    operator s * operator p * operator s = (signLabel s p : ℂ) • operator p := by
  unfold operator
  rw [tensor_mul, tensor_mul]
  simp_rw [localC_conjugation]
  rw [tensor_smul]
  simp [signLabel]

theorem signLabel_single (site : Fin 4) (ax : Fin 4) (p : Label 4) :
    signLabel (single site ax) p = character ax (p site) := by
  unfold signLabel
  rw [Finset.prod_eq_single site]
  · simp [single]
  · intro i _ hi
    simp [single, hi, character]
  · simp

theorem single_conjugation (site : Fin 4) (ax : Fin 4) (p : Label 4) :
    operator (single site ax) * operator p * operator (single site ax) =
      (character ax (p site) : ℂ) • operator p := by
  rw [operator_conjugation, signLabel_single]

/-- The six-Pauli trace in J reduces to the stated four-Pauli trace and signs. -/
theorem J_trace_shortcut (site : Fin 4) (ax : Fin 4) (u v x y : Label 4) :
    tau (operator u * operator (single site ax) * operator x * operator v *
      operator (single site ax) * operator y) =
    (character ax (x site) * character ax (v site) : ℤ) *
      tau (operator u * operator x * operator v * operator y) := by
  let σ := operator (single site ax)
  have hs : σ * σ = 1 := by
    have hi := single_conjugation site ax (fun _ => 0)
    simpa [σ, operator_zero, character] using hi
  have hc : σ * operator x * operator v * σ =
      ((character ax (x site) * character ax (v site) : ℤ) : ℂ) • (operator x * operator v) := by
    calc
      σ * operator x * operator v * σ =
          (σ * operator x * σ) * (σ * operator v * σ) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc σ σ, hs, Matrix.one_mul]
      _ = _ := by
        rw [single_conjugation, single_conjugation, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul]
        simp
  calc
    _ = tau (operator u * (σ * operator x * operator v * σ) * operator y) := by
      simp only [σ, Matrix.mul_assoc]
    _ = _ := by
      rw [hc, Matrix.mul_smul, Matrix.smul_mul, tau_smul]
      simp [Matrix.mul_assoc]

end Orbit2.Quartic
