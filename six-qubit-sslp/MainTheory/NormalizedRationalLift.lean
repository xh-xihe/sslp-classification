import MainTheory.NormalizedRealSectors

namespace MainTheory.NormalizedRationalLift

open scoped BigOperators
open MainTheory.PhaseSectorFull MainTheory.FiniteLift

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

theorem relative_angle_preserved {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D) (a : Fin t) (x : SupportIndex D a) :
    RealGate.angle (fun j => (L.physical j : ℝ)) x.val -
      RealGate.angle (fun j => (L.physical j : ℝ)) (basePoint D) =
        RealGate.angle theta x.val - RealGate.angle theta (basePoint D) := by
  have hq : (∑ j, physicalRow D a x j * L.augmented (.inl j)) +
      (∑ g, colorRow D a g * L.augmented (.inr g)) = coloredRhsQ D ⟨a, x⟩ := by
    simpa [coloredMatrix, ColoredSystem.augmentedMatrix, ColoredSystem.augmentedRow,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using congrFun L.solves ⟨a, x⟩
  have he := congrArg (algebraMap ℚ ℝ) hq
  simp only [map_add, map_sum, map_mul] at he
  have hc : (∑ g, (colorRow D a g : ℝ) * (L.augmented (.inr g) : ℝ)) =
      ∑ g, (colorRow D a g : ℝ) * realUnknown D (.inr g) := by
    apply Finset.sum_congr rfl
    intro g _
    rw [L.color_preserved]
  change (∑ j, (physicalRow D a x j : ℝ) * (L.physical j : ℝ)) +
    (∑ g, (colorRow D a g : ℝ) * (L.augmented (.inr g) : ℝ)) = _ at he
  rw [hc] at he
  have hr := congrFun (coloredMatrix_realSolution D) ⟨a, x⟩
  simp only [coloredMatrix, ColoredSystem.augmentedMatrix, ColoredSystem.augmentedRow,
    Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_sum_type] at hr
  have hp := add_right_cancel (he.trans hr.symm)
  change (∑ j, (physicalRow D a x j : ℝ) * (L.physical j : ℝ)) =
    ∑ j, (physicalRow D a x j : ℝ) * theta j at hp
  simpa only [physicalRow_dot_theta] using hp

/-- With 0 in the reference support, rationalization preserves the actual
angle on every supported string, not only its congruence class. -/
theorem angle_preserved {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (hzero : (fun _ => false) ∈ sectorSupport D (baseSector D))
    (a : Fin t) (x : SS.BitString n) (hx : x ∈ sectorSupport D a) :
    RealGate.angle (fun j => (L.physical j : ℝ)) x = RealGate.angle theta x := by
  have he := relative_angle_preserved L a ⟨x, hx⟩
  have hz := relative_angle_preserved L (baseSector D) ⟨fun _ => false, hzero⟩
  have hangle (eta : Fin n → ℝ) : RealGate.angle eta (fun _ => false) = 0 := by
    simp [RealGate.angle]
  simp only [hangle] at hz
  dsimp only at he hz
  linarith

theorem rational_replacement (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (hzero : (fun _ => false) ∈ sectorSupport D (baseSector D)) :
    ∃ eta : Fin n → ℚ, ∀ a x, x ∈ sectorSupport D a →
      RealGate.angle (fun j => (eta j : ℝ)) x = RealGate.angle theta x ∧
        ∃ k : ℤ, RealGate.angle (fun j => (eta j : ℝ)) x - D.phase a = (k : ℝ) := by
  obtain ⟨L⟩ := exists_rationalColoredLift D hZ
  refine ⟨L.physical, fun a x hx => ?_⟩
  have he := angle_preserved L hzero a x hx
  exact ⟨he, by rw [he]; exact phase_congruence D a x hx⟩

/-- The normalized real-angle sector construction and protected rational lift
are connected, including preservation of the Z-detection hypothesis. -/
theorem normalized_rational_replacement (D : SectorDecomposition n t theta) (hZ : ZDetects D) :
    let E := NormalizedRealSectors.shiftedSectors D (basePoint D)
    (fun _ => false) ∈ sectorSupport E (baseSector E) ∧
    E.phase (baseSector E) = 0 ∧
    (∀ a, E.phase a ∈ Set.Ico (0 : ℝ) 1) ∧
    ZDetects E ∧
    ∃ eta : Fin n → ℚ, ∀ a x, x ∈ sectorSupport E a →
      RealGate.angle (fun j => (eta j : ℝ)) x =
        RealGate.angle (RealXNormalization.flipAngle theta (basePoint D)) x ∧
      ∃ k : ℤ, RealGate.angle (fun j => (eta j : ℝ)) x - E.phase a = (k : ℝ) := by
  let E := NormalizedRealSectors.shiftedSectors D (basePoint D)
  have hz : (fun _ => false) ∈ sectorSupport E (baseSector E) :=
    NormalizedRealSectors.zero_mem_shifted_support D (baseSector D) _ (basePoint_mem D)
  have hp : E.phase (baseSector E) = 0 :=
    NormalizedRealSectors.shifted_reference_phase_zero D (baseSector D) _ (basePoint_mem D)
  have hZE : ZDetects E := NormalizedRealSectors.shifted_zDetects D hZ _
  exact ⟨hz, hp, NormalizedRealSectors.shifted_phase_mem_Ico D _, hZE,
    rational_replacement E hZE hz⟩

end

end MainTheory.NormalizedRationalLift
