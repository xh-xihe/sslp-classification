import MainTheory.NormalizedRationalLift

namespace MainTheory.NormalizedPhaseEquations

open scoped BigOperators
open MainTheory.PhaseSectorFull MainTheory.FiniteLift

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

def rationalPhase {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (a : Fin t) : ℚ :=
  if h : a = baseSector D then 0 else -L.augmented (.inr ⟨a, h⟩)

def deltaAngle {D : SectorDecomposition n t theta} (L : RationalColoredLift D) : Fin n → ℝ :=
  fun j => (L.physical j : ℝ) - theta j

def deltaPhase {D : SectorDecomposition n t theta} (L : RationalColoredLift D) (a : Fin t) : ℝ :=
  (rationalPhase L a : ℝ) - D.phase a

theorem rationalPhase_eq {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (hbase : D.phase (baseSector D) = 0) (a : Fin t) :
    (rationalPhase L a : ℝ) = D.phase a := by
  unfold rationalPhase
  split
  · rename_i ha
    simp [ha, hbase]
  · rename_i ha
    rw [Rat.cast_neg, L.color_preserved]
    simp [realUnknown, hbase]

theorem deltaPhase_zero {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (hbase : D.phase (baseSector D) = 0) (a : Fin t) : deltaPhase L a = 0 := by
  rw [deltaPhase, rationalPhase_eq L hbase, sub_self]

theorem deltaAngle_apply_angle {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D) (x : SS.BitString n) :
    RealGate.angle (deltaAngle L) x =
      RealGate.angle (fun j => (L.physical j : ℝ)) x - RealGate.angle theta x := by
  simp only [RealGate.angle, deltaAngle, sub_mul, Finset.sum_sub_distrib]

theorem deltaAngle_support_zero {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D)
    (hzero : (fun _ => false) ∈ sectorSupport D (baseSector D))
    (a : Fin t) (x : SS.BitString n) (hx : x ∈ sectorSupport D a) :
    RealGate.angle (deltaAngle L) x = 0 := by
  rw [deltaAngle_apply_angle, NormalizedRationalLift.angle_preserved L hzero a x hx, sub_self]

theorem same_integer_phase_equations {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D) (hbase : D.phase (baseSector D) = 0)
    (hzero : (fun _ => false) ∈ sectorSupport D (baseSector D))
    (a : Fin t) (x : SS.BitString n) (hx : x ∈ sectorSupport D a) :
    ∃ k : ℤ, RealGate.angle theta x - D.phase a = (k : ℝ) ∧
      RealGate.angle (fun j => (L.physical j : ℝ)) x - (rationalPhase L a : ℝ) = (k : ℝ) := by
  obtain ⟨k, hk⟩ := phase_congruence D a x hx
  exact ⟨k, hk, by rw [rationalPhase_eq L hbase,
    NormalizedRationalLift.angle_preserved L hzero a x hx]; exact hk⟩

theorem weighted_angle_eq_mean (D : SectorDecomposition n t theta) (a : Fin t)
    (eta : Fin n → ℝ) :
    (∑ x, sectorProbability D a x * RealGate.angle eta x) =
      ∑ j, eta j * sectorMean D a j := by
  simp only [RealGate.angle, sectorMean, coordinate, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem deltaAngle_mean_zero {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D)
    (hzero : (fun _ => false) ∈ sectorSupport D (baseSector D)) (a : Fin t) :
    (∑ x, sectorProbability D a x * RealGate.angle (deltaAngle L) x) = 0 ∧
    (∑ j, deltaAngle L j * sectorMean D a j) = 0 := by
  have hs : (∑ x, sectorProbability D a x * RealGate.angle (deltaAngle L) x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ sectorSupport D a
    · rw [deltaAngle_support_zero L hzero a x hx, mul_zero]
    · rw [sectorProbability_eq_zero_of_not_mem D a x hx, zero_mul]
  exact ⟨hs, (weighted_angle_eq_mean D a (deltaAngle L)).symm.trans hs⟩

end

end MainTheory.NormalizedPhaseEquations
