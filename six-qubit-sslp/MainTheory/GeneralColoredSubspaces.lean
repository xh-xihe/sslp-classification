import MainTheory.GeneralColoredExistence

/-! # Dimensions and ambient computational fibers of the colored sectors -/

namespace MainTheory.GeneralColoredSubspaces

open GeneralColoredConverse ColoredResidueArithmetic

noncomputable section

variable {n K q m t : ℕ}

/-- All states supported in one full subset-sum fiber. -/
def fiberSubspace (a : Fin n → ZMod q) (b : ZMod q) : Submodule ℂ (SS.State n ℂ) where
  carrier := {psi | SS.SSConditionState a b psi}
  zero_mem' := by simp [SS.SSConditionState]
  add_mem' := by
    intro psi phi hp hf x hx
    by_cases hpx : psi x = 0
    · exact hf x (by simpa [hpx] using hx)
    · exact hp x hpx
  smul_mem' := by
    intro c psi hp x hx
    exact hp x (by intro h; simp [h] at hx)

/-- The coordinate definition is exactly the paper's span of `|x⟩` over the fiber. -/
theorem fiberSubspace_eq_span (a : Fin n → ZMod q) (b : ZMod q) :
    fiberSubspace a b = Submodule.span ℂ
      ((fun x : SS.BitString n => Pi.single x (1 : ℂ)) '' (SS.Sk a b : Set (SS.BitString n))) := by
  classical
  apply le_antisymm
  · intro psi hp
    have hsum : psi = ∑ x : SS.BitString n,
        psi x • (Pi.single x (1 : ℂ) : SS.State n ℂ) := pi_eq_sum_univ' psi
    rw [hsum]
    apply Submodule.sum_mem
    intro x _
    by_cases hx : psi x = 0
    · simp [hx]
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨x, hp x hx, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩ y hy
    have hyx : y = x := by
      by_contra h
      simp [h] at hy
    subst y
    exact hx

theorem frame_linearIndependent (F : CodeSpec.OrthonormalFrame n K) :
    LinearIndependent ℂ F.vec := by
  apply LinearIndependent.of_comp (GeneralSpectral.stateEquiv n).toLinearMap
  exact (GeneralSpectral.orthonormal_euclideanFrame F).linearIndependent

theorem finrank_codeSpan (F : CodeSpec.OrthonormalFrame n K) :
    Module.finrank ℂ (CodeSpec.codeSpan F) = K := by
  simpa only [CodeSpec.codeSpan, Fintype.card_fin] using
    finrank_span_eq_card (frame_linearIndependent F)

theorem fiberSubspace_eq_eigenspace [NeZero q] (a : Fin n → ZMod q) (b : ZMod q)
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    fiberSubspace a b = Module.End.eigenspace
      (GlobalClassificationBridge.diagonalEnd
        (GlobalClassificationBridge.finiteLocalPhase zeta hzeta a)) (Cyclic.chi zeta b) := by
  ext psi
  rw [Module.End.mem_eigenspace_iff]
  change SS.SSConditionState a b psi ↔
    GlobalClassificationBridge.diagonalEnd
      (GlobalClassificationBridge.finiteLocalPhase zeta hzeta a) psi = Cyclic.chi zeta b • psi
  rw [GlobalClassificationBridge.diagonalEnd_apply,
    GlobalClassificationBridge.diagonalAction_finiteLocalPhase]
  constructor
  · exact PhaseSector.eigen_of_ssCondition zeta a psi b
  · intro h x hx
    apply Cyclic.chi_injective zeta hzeta
    exact PhaseSector.diag_eq_of_eigen zeta a psi _ h x hx

namespace ColoredFrame

variable [NeZero q] [NeZero m] (S : GeneralColoredConverse.ColoredFrame n K q m t)

def sectorFrame (alpha : Fin t) : CodeSpec.OrthonormalFrame n (S.rank alpha) where
  vec r := S.frame.vec (S.reindex.symm ⟨alpha, r⟩)
  orthonormal r s := by
    rw [S.frame.orthonormal]
    simp

def sectorSpace (alpha : Fin t) : Submodule ℂ (SS.State n ℂ) :=
  CodeSpec.codeSpan (sectorFrame S alpha)

theorem sectorSpace_finrank (alpha : Fin t) :
    Module.finrank ℂ (sectorSpace S alpha) = S.rank alpha :=
  finrank_codeSpan _

theorem sectorSpace_le_fiber (alpha : Fin t) :
    sectorSpace S alpha ≤ fiberSubspace S.angle (scaledColor q (S.color alpha)) := by
  apply Submodule.span_le.2
  rintro _ ⟨r, rfl⟩
  have h := S.fiber (S.reindex.symm ⟨alpha, r⟩)
  simpa only [Equiv.apply_symm_apply] using h

theorem sectorSpace_eigen (zeta : ℂ) (alpha : Fin t)
    {psi : SS.State n ℂ} (hp : psi ∈ sectorSpace S alpha) :
    Gate.gate zeta S.angle psi =
      Cyclic.chi zeta (scaledColor q (S.color alpha)) • psi :=
  PhaseSector.eigen_of_ssCondition _ _ _ _ (sectorSpace_le_fiber S alpha hp)

/-- The full ambient fiber in the manuscript's computational-basis notation. -/
theorem sectorSpace_le_computational_span (alpha : Fin t) :
    sectorSpace S alpha ≤ Submodule.span ℂ
      ((fun x : SS.BitString n => Pi.single x (1 : ℂ)) ''
        (SS.Sk S.angle (scaledColor q (S.color alpha)) : Set (SS.BitString n))) := by
  rw [← fiberSubspace_eq_span]
  exact sectorSpace_le_fiber S alpha

/-- The sector subspaces are precisely a decomposition of the actual code. -/
theorem iSup_sectorSpace : (⨆ alpha, sectorSpace S alpha) = CodeSpec.codeSpan S.frame := by
  apply le_antisymm
  · apply iSup_le
    intro alpha
    apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self _)
  · apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    apply (le_iSup (fun alpha => sectorSpace S alpha) (S.reindex j).1)
    have hmem := Submodule.subset_span
      (R := ℂ) (Set.mem_range_self (f := (sectorFrame S (S.reindex j).1).vec) (S.reindex j).2)
    change S.frame.vec (S.reindex.symm (S.reindex j)) ∈ sectorSpace S (S.reindex j).1 at hmem
    simpa only [Equiv.symm_apply_apply] using hmem

/-- These spaces are the actual gate eigenspaces inside the code, rather than
arbitrary proper subspaces with the right eigenvalues. -/
theorem sectorSpace_eq_code_inf_fiber (alpha : Fin t) :
    sectorSpace S alpha = CodeSpec.codeSpan S.frame ⊓
      fiberSubspace S.angle (scaledColor q (S.color alpha)) := by
  apply le_antisymm
  · exact le_inf (by rw [← iSup_sectorSpace S]; exact le_iSup _ alpha)
      (sectorSpace_le_fiber S alpha)
  · intro psi hp
    have hproj := (CodeSpec.mem_codeSpan_iff_projectorAction_eq S.frame psi).1 hp.1
    have hexp : psi = ∑ j, SS.innerC (S.frame.vec j) psi • S.frame.vec j := by
      calc psi = CodeSpec.projectorAction S.frame psi := hproj.symm
        _ = _ := by
          funext x
          simp only [CodeSpec.projectorAction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hexp]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (S.reindex j).1 = alpha
    · apply Submodule.smul_mem
      have hmem := Submodule.subset_span
        (R := ℂ) (Set.mem_range_self (f := (sectorFrame S (S.reindex j).1).vec) (S.reindex j).2)
      change S.frame.vec (S.reindex.symm (S.reindex j)) ∈ sectorSpace S (S.reindex j).1 at hmem
      simpa only [Equiv.symm_apply_apply, hj] using hmem
    · have hc : SS.innerC (S.frame.vec j) psi = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : S.frame.vec j x = 0
        · simp [hx]
        · have hz : psi x = 0 := by
            by_contra hz
            have heq := (S.fiber j x hx).symm.trans (hp.2 x hz)
            exact hj (S.color_distinct (scaledColor_injective S.modulus_dvd heq))
          simp [hz]
      simp [hc]

theorem sectorSpace_eq_code_inf_eigenspace (alpha : Fin t)
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    sectorSpace S alpha = CodeSpec.codeSpan S.frame ⊓ Module.End.eigenspace
      (GlobalClassificationBridge.diagonalEnd
        (GlobalClassificationBridge.finiteLocalPhase zeta hzeta S.angle))
      (Cyclic.chi zeta (scaledColor q (S.color alpha))) := by
  rw [sectorSpace_eq_code_inf_fiber, fiberSubspace_eq_eigenspace S.angle _ zeta hzeta]

theorem sectorSpace_orthogonal {alpha beta : Fin t} (hab : alpha ≠ beta)
    {psi phi : SS.State n ℂ} (hp : psi ∈ sectorSpace S alpha)
    (hf : phi ∈ sectorSpace S beta) : SS.innerC psi phi = 0 := by
  have hp' := sectorSpace_le_fiber S alpha hp
  have hf' := sectorSpace_le_fiber S beta hf
  apply Finset.sum_eq_zero
  intro x _
  by_cases hpx : psi x = 0
  · simp [hpx]
  · have hfx : phi x = 0 := by
      by_contra hfx
      have heq := (hp' x hpx).symm.trans (hf' x hfx)
      exact hab (S.color_distinct (scaledColor_injective S.modulus_dvd heq))
    simp [hfx]

theorem sectorSpace_disjoint {alpha beta : Fin t} (hab : alpha ≠ beta) :
    Disjoint (sectorSpace S alpha) (sectorSpace S beta) := by
  rw [Submodule.disjoint_def]
  intro psi hp hf
  have hinner := sectorSpace_orthogonal S hab hp hf
  rw [StateEuclidean.innerC_eq_inner, inner_self_eq_zero] at hinner
  exact congrArg StateEuclidean.ofEuclidean hinner

theorem rank_sum_and_dimensions :
    (∑ alpha, S.rank alpha) = K ∧
      (∀ alpha, Module.finrank ℂ (sectorSpace S alpha) = S.rank alpha) ∧
      Module.finrank ℂ (CodeSpec.codeSpan S.frame) = K :=
  ⟨S.sum_rank, sectorSpace_finrank S, finrank_codeSpan _⟩

end ColoredFrame

end

end MainTheory.GeneralColoredSubspaces
