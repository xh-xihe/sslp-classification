import MainTheory.RealXNormalization

namespace MainTheory.NormalizedRealSectors

open MainTheory.PhaseSectorFull MainTheory.RealXNormalization

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

def shiftedSectors (D : SectorDecomposition n t theta) (x₀ : SS.BitString n) :
    SectorDecomposition n t (flipAngle theta x₀) where
  sectorCount_pos := D.sectorCount_pos
  rank := D.rank
  rank_pos := D.rank_pos
  vec u x := D.vec u (SS.bxor x x₀)
  orthonormal u v := by rw [IntrinsicTransport.innerC_shift]; exact D.orthonormal u v
  phase a := Int.fract (D.phase a - RealGate.angle theta x₀)
  phaseDistinct := by
    intro a b hab
    simp only [phaseExp_fract, phaseExp_sub] at hab
    exact D.phaseDistinct ((div_left_inj' (phaseExp_ne_zero _)).mp hab)
  eigen u := by
    rw [gate_shift, flipAngle_flipAngle, D.eigen]
    funext x
    change phaseExp (RealGate.angle (flipAngle theta x₀) x₀) *
      (phaseExp (D.phase u.1) * D.vec u (SS.bxor x x₀)) =
        phaseExp (Int.fract (D.phase u.1 - RealGate.angle theta x₀)) * _
    rw [phaseExp_fract, phaseExp_sub, angle_flip_self]
    have hn (a : ℝ) : phaseExp (-a) = (phaseExp a)⁻¹ := by
      simpa [phaseExp] using phaseExp_sub 0 a
    rw [hn]
    ring

theorem shifted_probability (D : SectorDecomposition n t theta) (x₀ x : SS.BitString n)
    (a : Fin t) :
    sectorProbability (shiftedSectors D x₀) a x = sectorProbability D a (SS.bxor x x₀) := rfl

theorem zero_mem_shifted_support (D : SectorDecomposition n t theta) (a : Fin t)
    (x₀ : SS.BitString n) (hx₀ : x₀ ∈ sectorSupport D a) :
    (fun _ => false) ∈ sectorSupport (shiftedSectors D x₀) a := by
  change 0 < sectorProbability (shiftedSectors D x₀) a (fun _ => false)
  rw [shifted_probability]
  simpa [SS.bxor] using hx₀

theorem shifted_phase_mem_Ico (D : SectorDecomposition n t theta) (x₀ : SS.BitString n)
    (a : Fin t) : (shiftedSectors D x₀).phase a ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem shifted_reference_phase_zero (D : SectorDecomposition n t theta) (a : Fin t)
    (x₀ : SS.BitString n) (hx₀ : x₀ ∈ sectorSupport D a) :
    (shiftedSectors D x₀).phase a = 0 := by
  obtain ⟨k, hk⟩ := phase_congruence D a x₀ hx₀
  have he : D.phase a - RealGate.angle theta x₀ = ((-k : ℤ) : ℝ) := by
    push_cast
    linarith
  change Int.fract (D.phase a - RealGate.angle theta x₀) = 0
  rw [he]
  exact Int.fract_intCast _

theorem shifted_zDetects (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (x₀ : SS.BitString n) : ZDetects (shiftedSectors D x₀) := by
  intro j
  obtain ⟨c, hc⟩ := hZ j
  refine ⟨SS.signC (SS.bdot (SS.stdBasis j) x₀) c, fun u v => ?_⟩
  let P : SS.PauliString n := ⟨fun _ => false, SS.stdBasis j⟩
  change SS.innerC (fun x => D.vec u (SS.bxor x x₀))
    (SS.pauliAct P (fun x => D.vec v (SS.bxor x x₀))) = _
  rw [SixQubit.CodeEquiv.innerC_eq_corr]
  change (Complex.I ^ P.numY) * SixQubit.CodeEquiv.corr
    (SixQubit.CodeEquiv.flipAct x₀ (D.vec u))
    (SixQubit.CodeEquiv.flipAct x₀ (D.vec v)) P.x P.z = _
  rw [SixQubit.CodeEquiv.corr_flipAct]
  have ho := hc u v
  rw [SixQubit.CodeEquiv.innerC_eq_corr] at ho
  change Complex.I ^ P.numY * SixQubit.CodeEquiv.corr (D.vec u) (D.vec v) P.x P.z = _ at ho
  change Complex.I ^ P.numY * SS.signC (SS.bdot (SS.stdBasis j) x₀) _ = _
  cases hb : SS.bdot (SS.stdBasis j) x₀ <;> by_cases huv : u = v <;>
    simp_all [SS.signC]

end

end MainTheory.NormalizedRealSectors
