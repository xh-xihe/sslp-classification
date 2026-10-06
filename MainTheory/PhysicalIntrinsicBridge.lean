import MainTheory.PhysicalStabilizerTopology
import MainTheory.CodePreservingUnitary

namespace MainTheory.PhysicalIntrinsicBridge

open scoped BigOperators
open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells

noncomputable section

variable {n : ℕ}

def circleUnitary (z : Circle) : unitary ℂ :=
  ⟨z, by
    have hstar : star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) :=
      (Circle.coe_inv_eq_conj z).symm
    constructor <;> rw [hstar, Circle.coe_inv]
    · exact inv_mul_cancel₀ (Circle.coe_ne_zero z)
    · exact mul_inv_cancel₀ (Circle.coe_ne_zero z)⟩

def localPhase (u : Torus n) : LocalPhase n := fun j => circleUnitary (u j)

theorem localPhase_one : localPhase (1 : Torus n) = 1 := by
  funext j
  apply Subtype.ext
  rfl

theorem localPhase_mul (u v : Torus n) : localPhase (u * v) = localPhase u * localPhase v := by
  funext j
  apply Subtype.ext
  rfl

theorem localPhase_inv (u : Torus n) : localPhase u⁻¹ = (localPhase u)⁻¹ := by
  funext j
  apply Subtype.ext
  exact Circle.coe_inv_eq_conj (u j)

theorem diagonalValue_eq (u : Torus n) (x : SS.BitString n) :
    diagonalValue (localPhase u) x = (phase u x : ℂ) := by
  have hc := map_prod Circle.coeHom (fun j : Fin n => if x j then u j else 1) Finset.univ
  change (phase u x : ℂ) = ∏ j, ((if x j then u j else 1 : Circle) : ℂ) at hc
  rw [hc]
  simp only [diagonalValue, localPhase, circleUnitary]
  apply Finset.prod_congr rfl
  intro j _
  split <;> rfl

theorem diagonalKernel_eq (u : Torus n) : diagonalKernel (localPhase u) = operator u := by
  ext x y
  simp only [diagonalKernel, operator, Matrix.diagonal_apply, diagonalValue_eq]

theorem preserves_range (P : CodeProjector n) (u : Torus n)
    (hu : u ∈ stabilizerSubgroup P) : PreservesProjectorRange P (localPhase u) := by
  have hforward : ∀ (v : Torus n), v ∈ stabilizerSubgroup P →
      ∀ ψ, InProjectorRange P ψ → InProjectorRange P (diagonalAction (localPhase v) ψ) := by
    intro v hv ψ hψ
    have hd := kernelAction_diagonalKernel (localPhase v) ψ
    rw [diagonalKernel_eq] at hd
    rw [← hd]
    exact MainTheory.CodePreservingUnitary.mapsTo_of_preservesProjector
      ((mem_stabilizer_iff_conjugate P v).mp hv) (operator_unitary v).1 ψ hψ
  exact ⟨hforward u hu, by
    rw [← localPhase_inv]
    exact hforward u⁻¹ ((stabilizerSubgroup P).inv_mem hu)⟩

/-- The physical matrix stabilizer maps to the repository's actual symmetry
group defined by preservation of the entire code range. -/
def symmetryHom (P : CodeProjector n) : stabilizerSubgroup P →* diagonalSymmetryGroup P where
  toFun u := ⟨localPhase u.val, preserves_range P u.val u.property⟩
  map_one' := Subtype.ext localPhase_one
  map_mul' u v := Subtype.ext (localPhase_mul u.val v.val)

end

end MainTheory.PhysicalIntrinsicBridge
