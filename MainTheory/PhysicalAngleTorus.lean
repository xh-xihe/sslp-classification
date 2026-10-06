import MainTheory.PhysicalStabilizerTopology

namespace MainTheory.PhysicalTorusCells

open MainTheory.ClassificationLevels

noncomputable section

variable {n : ℕ}

/-- Real angles modulo integer periods, coordinate by coordinate. -/
abbrev AngleTorus (n : ℕ) := Fin n → AddCircle (1 : ℝ)

def angleTorusHomeomorph : AngleTorus n ≃ₜ Torus n :=
  Homeomorph.piCongrRight fun _ => AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)

theorem angleTorusHomeomorph_real (θ : Fin n → ℝ) :
    angleTorusHomeomorph (fun j => (θ j : AddCircle (1 : ℝ))) = expAngles θ := by
  funext j
  change AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0) (θ j) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  simp [expAngles]

/-- The stabilizer written in the manuscript's real-angle quotient model. -/
abbrev AngleStabilizer (P : CodeProjector n) :=
  {a : AngleTorus n // operator (angleTorusHomeomorph a) * P.kernel *
    star (operator (angleTorusHomeomorph a)) = P.kernel}

def angleStabilizerHomeomorph (P : CodeProjector n) : AngleStabilizer P ≃ₜ stabilizerSubgroup P :=
  angleTorusHomeomorph.subtype fun _ => (mem_stabilizer_iff_conjugate P _).symm

end

end MainTheory.PhysicalTorusCells
