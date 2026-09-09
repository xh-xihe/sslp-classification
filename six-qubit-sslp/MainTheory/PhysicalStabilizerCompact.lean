import MainTheory.PhysicalAngleTorus

namespace MainTheory.PhysicalTorusCells

open MainTheory.ClassificationLevels

noncomputable section

variable {n : ℕ}

theorem stabilizer_isClosed (P : CodeProjector n) :
    IsClosed (stabilizerSubgroup P : Set (Torus n)) := by
  have hc := isClosed_eq (conjugation_continuous P)
    (continuous_const : Continuous (fun _ : Torus n => P.kernel))
  convert hc using 1
  ext u
  exact mem_stabilizer_iff_conjugate P u

instance stabilizer_compactSpace (P : CodeProjector n) : CompactSpace (stabilizerSubgroup P) :=
  isCompact_iff_compactSpace.mp (stabilizer_isClosed P).isCompact

theorem angle_conjugation_continuous (P : CodeProjector n) :
    Continuous (fun a : AngleTorus n => operator (angleTorusHomeomorph a) * P.kernel *
      star (operator (angleTorusHomeomorph a))) :=
  (conjugation_continuous P).comp angleTorusHomeomorph.continuous

theorem one_parameter_continuous (h : Fin n → ℝ) :
    Continuous (fun t : ℝ => expAngles (t • h)) := by
  apply continuous_pi
  intro j
  exact Circle.exp.continuous.comp
    (continuous_const.mul (continuous_id.mul continuous_const))

end

end MainTheory.PhysicalTorusCells
