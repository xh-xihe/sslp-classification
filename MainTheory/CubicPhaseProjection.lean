import MainTheory.FinitePhaseAverage

/-! # Phase projection of actual cubic amplitudes

The phase Gram is identified with the cubic moment of explicitly modulated
state amplitudes. The projection therefore acts on actual cubic monomials,
not only on an abstract matrix with stipulated positivity.
-/

namespace MainTheory.CubicPhaseProjection

open MainTheory.FiniteCubicMoments MainTheory.FinitePhaseAverage
open scoped BigOperators

noncomputable section
variable {J I B : Type*} [Fintype J] [DecidableEq J] [Fintype I]

def binaryProfile (bits : B → J → Bool) (b : B) : J → Fin 4 :=
  fun j => if bits b j then 1 else 0

def occupation (bits : B → J → Bool) (t : B × B × B) : J → Fin 4 :=
  fun j => ⟨(binaryProfile bits t.1 j).val +
    (binaryProfile bits t.2.1 j).val + (binaryProfile bits t.2.2 j).val, by
      unfold binaryProfile
      cases bits t.1 j <;> cases bits t.2.1 j <;> cases bits t.2.2 j <;> decide⟩

omit [Fintype I] [DecidableEq J] in
theorem character_product (bits : B → J → Bool) (p : J → Fin 4) (t : B × B × B) :
    character p (binaryProfile bits t.1) * character p (binaryProfile bits t.2.1) *
      character p (binaryProfile bits t.2.2) = character p (occupation bits t) := by
  unfold character
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [occupation, Nat.mul_add, pow_add]

def modulated (bits : B → J → Bool) (w : B → ℂ) (p : J → Fin 4) (b : B) : ℂ :=
  character p (binaryProfile bits b) * w b

omit [Fintype I] [DecidableEq J] in
theorem cubic_modulated (bits : B → J → Bool) (t : I → B × B × B)
    (w : B → ℂ) (p : J → Fin 4) (i : I) :
    cubic t (modulated bits w) p i =
      character p (occupation bits (t i)) * (w (t i).1 * w (t i).2.1 * w (t i).2.2) := by
  unfold cubic modulated
  rw [← character_product]
  ring

def moment (bits : B → J → Bool) (t : I → B × B × B) (w : B → ℂ) : Matrix I I ℝ :=
  cubicMoment t (modulated bits w)

theorem moment_posSemidef (bits : B → J → Bool) (t : I → B × B × B) (w : B → ℂ) :
    (moment bits t w).PosSemidef := cubicMoment_posSemidef _ _

omit [Fintype I] in
theorem moment_eq_phaseGram (bits : B → J → Bool) (t : I → B × B × B) (w : B → ℂ) :
    moment bits t w = phaseGram (fun i => occupation bits (t i))
      (fun i => w (t i).1 * w (t i).2.1 * w (t i).2.2) := by
  unfold moment cubicMoment phaseGram
  congr 1
  funext p i
  exact cubic_modulated bits t w p i

omit [Fintype I] in
theorem moment_apply (bits : B → J → Bool) (t : I → B × B × B) (w : B → ℂ) (i k : I) :
    moment bits t w i k = if occupation bits (t i) = occupation bits (t k) then
      (4 : ℝ) ^ Fintype.card J *
        (star (w (t i).1 * w (t i).2.1 * w (t i).2.2) *
          (w (t k).1 * w (t k).2.1 * w (t k).2.2)).re else 0 := by
  rw [moment_eq_phaseGram, phaseGram_apply]

end
end MainTheory.CubicPhaseProjection
