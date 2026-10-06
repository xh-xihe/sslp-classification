import MainTheory.GeneralSpectralSectors
import MainTheory.SpanProjectorBridge
import MainTheory.NumberKernelKL

namespace MainTheory.SectorProjectorIdentities

open scoped BigOperators Classical
open MainTheory.ClassificationLevels MainTheory.PhaseSectorFull

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

def sectorFrame (D : SectorDecomposition n t theta) (a : Fin t) :
    CodeSpec.OrthonormalFrame n (D.rank a) where
  vec r := D.vec ⟨a, r⟩
  orthonormal r s := by simpa using D.orthonormal ⟨a, r⟩ ⟨a, s⟩

abbrev sectorMatrix (D : SectorDecomposition n t theta) (a : Fin t) : OperatorKernel n :=
  sectorProjectorKernel D a

theorem sectorFrame_kernel (D : SectorDecomposition n t theta) (a : Fin t) :
    (CodeProjector.ofFrame (sectorFrame D a)).kernel = sectorMatrix D a := rfl

theorem sum_sectorProjector (D : SectorDecomposition n t theta) {K d : ℕ}
    (C : CodeSpec.ExactCode n K d) (link : FiniteLift.ExactCodeSectorLink C D) :
    (CodeProjector.ofFrame C.frame).kernel = ∑ a, sectorMatrix D a := by
  have he := SpanProjectorBridge.projectorKernel_eq_of_codeSpan_eq _ _ link.span_eq
  change CodeSpec.projectorKernel C.frame = _
  rw [he]
  ext x y
  simp only [CodeSpec.projectorKernel, FiniteLift.reindexedSectorFrame,
    Matrix.sum_apply, sectorMatrix, sectorProjectorKernel]
  exact (Equiv.sum_comp link.reindex (fun u => D.vec u x * star (D.vec u y))).trans
    (Fintype.sum_sigma (fun u : D.Index => D.vec u x * star (D.vec u y)))

theorem sectorProjector_trace (D : SectorDecomposition n t theta) (a : Fin t) :
    Matrix.trace (sectorMatrix D a) = (D.rank a : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, sectorMatrix, sectorProjectorKernel]
  rw [Finset.sum_comm]
  have hnorm (r : Fin (D.rank a)) :
      ∑ x, D.vec ⟨a, r⟩ x * star (D.vec ⟨a, r⟩ x) = 1 := by
    simpa [SS.innerC, mul_comm] using innerC_vec_self D ⟨a, r⟩
  simp only [hnorm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

def gateMatrix (theta : Fin n → ℝ) : OperatorKernel n :=
  Matrix.diagonal fun x => phaseExp (MainTheory.RealGate.angle theta x)

theorem gate_sectorProjector (D : SectorDecomposition n t theta) (a : Fin t) :
    gateMatrix theta * sectorMatrix D a =
      phaseExp (D.phase a) • sectorMatrix D a := by
  ext x y
  simp only [gateMatrix, Matrix.diagonal_mul, sectorMatrix, sectorProjectorKernel,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have he := congrFun (D.eigen ⟨a, r⟩) x
  change phaseExp (MainTheory.RealGate.angle theta x) * D.vec ⟨a, r⟩ x =
    phaseExp (D.phase a) * D.vec ⟨a, r⟩ x at he
  simpa only [mul_assoc] using congrArg (fun z => z * star (D.vec ⟨a, r⟩ y)) he

theorem sector_number_compression (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (a : Fin t) (j : Fin n) :
    sectorMatrix D a * DiagonalInfinitesimal.numberKernel j *
      sectorMatrix D a = (sectorMean D a j : ℂ) • sectorMatrix D a := by
  rw [← sectorFrame_kernel]
  apply (KLCodeBridge.projector_compression_iff (sectorFrame D a) _ _).mpr
  ext r s
  rw [PauliKernelBTrace.compressed_entry, DiagonalInfinitesimal.numberKernel_action]
  simpa [sectorFrame, Matrix.smul_apply, Matrix.one_apply] using
    NumberOperator.innerC_numberOp_eq_sectorMean D hZ a ⟨a, r⟩ ⟨a, s⟩ j

theorem sector_probability_support_sum (D : SectorDecomposition n t theta) (a : Fin t) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ sectorSupport D a), sectorProbability D a x = 1 := by
  classical
  rw [← sectorProbability_sum_eq_one D a]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hn : ¬ 0 < sectorProbability D a x := by simpa [sectorSupport] using hx
  exact le_antisymm (not_lt.mp hn) (sectorProbability_nonneg D a x)

theorem sector_occupation_trace (D : SectorDecomposition n t theta) (a : Fin t)
    (j : Fin n) :
    ∑ x, (coordinate x j : ℂ) * sectorMatrix D a x x =
      (sectorMean D a j : ℂ) * (D.rank a : ℂ) := by
  have hr : (D.rank a : ℝ) ≠ 0 := by exact_mod_cast (D.rank_pos a).ne'
  have he : ∑ x, coordinate x j * sectorProjectorDiag D a x =
      sectorMean D a j * (D.rank a : ℝ) := by
    dsimp only [sectorMean, sectorProbability]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, div_mul_cancel₀ _ hr]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp only [sectorMatrix, sectorProjectorKernel_diag]
  exact_mod_cast he

theorem sector_diag_zero_off_support (D : SectorDecomposition n t theta) (a : Fin t)
    (x : SS.BitString n) (hx : x ∉ sectorSupport D a) : sectorMatrix D a x x = 0 := by
  have hp := FiniteLift.sectorProbability_eq_zero_of_not_mem D a x hx
  have hr : (D.rank a : ℝ) ≠ 0 := by exact_mod_cast (D.rank_pos a).ne'
  have hz : sectorProjectorDiag D a x = 0 := by
    exact (div_eq_zero_iff).mp hp |>.resolve_right hr
  simp only [sectorMatrix, sectorProjectorKernel_diag, hz, Complex.ofReal_zero]

theorem sector_supported_occupation_trace (D : SectorDecomposition n t theta) (a : Fin t)
    (j : Fin n) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ sectorSupport D a),
      (coordinate x j : ℂ) * sectorMatrix D a x x =
        (sectorMean D a j : ℂ) * (D.rank a : ℂ) := by
  rw [← sector_occupation_trace D a j]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  rw [sector_diag_zero_off_support D a x (by simpa using hx), mul_zero]

theorem sector_diagonal_eigen (D : SectorDecomposition n t theta) (a : Fin t)
    (x : SS.BitString n) :
    phaseExp (MainTheory.RealGate.angle theta x) * sectorMatrix D a x x =
      phaseExp (D.phase a) * sectorMatrix D a x x := by
  simpa only [gateMatrix, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] using
    congrFun (congrFun (gate_sectorProjector D a) x) x

theorem supported_phase_exp_eq_one (D : SectorDecomposition n t theta) (a : Fin t)
    (x : SS.BitString n) (hx : x ∈ sectorSupport D a) :
    phaseExp (MainTheory.RealGate.angle theta x - D.phase a) = 1 := by
  obtain ⟨k, hk⟩ := phase_congruence D a x hx
  exact FiniteLift.phaseExp_eq_of_sub_int _ 0 k (by simpa using hk) |>.trans (by simp [phaseExp])

end

end MainTheory.SectorProjectorIdentities
