import MainTheory.FiniteConnectedCover
import MainTheory.ClassificationLevels

namespace MainTheory.PhysicalTorusCells

open scoped BigOperators
open MainTheory.ClassificationLevels

noncomputable section

variable {n : ℕ}

abbrev Torus (n : ℕ) := Fin n → Circle

def phase (u : Torus n) (x : SS.BitString n) : Circle :=
  ∏ j, if x j then u j else 1

/-- Entrywise commutation constraints for the physical diagonal stabilizer. -/
abbrev Stabilizer (P : CodeProjector n) :=
  {u : Torus n // ∀ x y, P.kernel x y ≠ 0 → phase u x = phase u y}

def angle (θ : Fin n → ℝ) (x : SS.BitString n) : ℝ :=
  ∑ j, if x j then θ j else 0

def expAngles (θ : Fin n → ℝ) : Torus n := fun j => Circle.exp (2 * Real.pi * θ j)

theorem phase_expAngles (θ : Fin n → ℝ) (x : SS.BitString n) :
    phase (expAngles θ) x = Circle.exp (2 * Real.pi * angle θ x) := by
  have h := map_sum Circle.expHom (fun j : Fin n =>
    if x j then 2 * Real.pi * θ j else 0) Finset.univ
  change Circle.exp (∑ j : Fin n, if x j then 2 * Real.pi * θ j else 0) =
    ∏ j : Fin n, Circle.exp (if x j then 2 * Real.pi * θ j else 0) at h
  simpa only [phase, expAngles, angle, Finset.mul_sum, mul_ite, mul_zero,
    apply_ite, Circle.exp_zero] using h.symm

theorem angle_add (θ η : Fin n → ℝ) (x : SS.BitString n) :
    angle (θ + η) x = angle θ x + angle η x := by
  simp only [angle, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp

theorem angle_smul (a : ℝ) (θ : Fin n → ℝ) (x : SS.BitString n) :
    angle (a • θ) x = a * angle θ x := by
  simp only [angle, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp

abbrev Labels (n : ℕ) := SS.BitString n → SS.BitString n → Fin (2 * n + 1)

def cell (P : CodeProjector n) (h : Labels n) : Set (Fin n → ℝ) :=
  {θ | ∀ x y, P.kernel x y ≠ 0 → angle θ x - angle θ y = (h x y).val - (n : ℝ)}

theorem cell_convex (P : CodeProjector n) (h : Labels n) : Convex ℝ (cell P h) := by
  intro θ hθ η hη a b _ha _hb hab x y hxy
  rw [angle_add, angle_add, angle_smul, angle_smul, angle_smul, angle_smul]
  have ht := hθ x y hxy
  have he := hη x y hxy
  nlinarith

theorem expAngles_mem (P : CodeProjector n) (h : Labels n) (θ : cell P h) :
    ∀ x y, P.kernel x y ≠ 0 → phase (expAngles θ.val) x = phase (expAngles θ.val) y := by
  intro x y hxy
  rw [phase_expAngles, phase_expAngles, Circle.exp_eq_exp]
  refine ⟨((h x y).val : ℤ) - n, ?_⟩
  have he := θ.property x y hxy
  push_cast
  rw [← he]
  ring

def cellMap (P : CodeProjector n) (h : Labels n) : cell P h → Stabilizer P :=
  fun θ => ⟨expAngles θ.val, expAngles_mem P h θ⟩

theorem cellMap_continuous (P : CodeProjector n) (h : Labels n) :
    Continuous (cellMap P h) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact Circle.exp.continuous.comp
    (continuous_const.mul ((continuous_apply j).comp continuous_subtype_val))

end

end MainTheory.PhysicalTorusCells
