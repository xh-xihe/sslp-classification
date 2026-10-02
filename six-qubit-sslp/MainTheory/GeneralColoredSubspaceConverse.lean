import MainTheory.SubspaceCode

/-! # The colored SSLP converse from arbitrary subspaces

The input contains subspaces and their dimensions, with no chosen frame or
assumed directness. Distinct full fibers imply orthogonality and independence.
Choosing an orthonormal basis in each supplied subspace then gives a colored
frame with exactly those sector spaces and exactly their sum as its code space.
-/

namespace MainTheory.GeneralColoredSubspaceConverse

open CodeSpec GeneralColoredConverse GeneralColoredSubspaces ColoredResidueArithmetic
open ClassificationLevels GlobalClassificationBridge

noncomputable section

variable {n K d q m t : ℕ}

/-- The subspace data in the converse of `thm:general-sslp-normal-form`. -/
structure ColoredSubspaces (n K q m t : ℕ) [NeZero q] [NeZero m] where
  modulus_dvd : m ∣ q
  angle : Fin n → ZMod q
  primitive : Gate.Primitive q angle
  sorted : Monotone fun j => (angle j).val
  rank : Fin t → ℕ
  rank_pos : ∀ alpha, 0 < rank alpha
  rank_sum : ∑ alpha, rank alpha = K
  base : Fin t
  color : Fin t → ZMod m
  color_zero : color base = 0
  color_distinct : Function.Injective color
  color_primitive : Gate.Primitive m color
  space : Fin t → Submodule ℂ (SS.State n ℂ)
  dimension : ∀ alpha, Module.finrank ℂ (space alpha) = rank alpha
  fiber : ∀ alpha, space alpha ≤ fiberSubspace angle (scaledColor q (color alpha))

namespace ColoredSubspaces

variable [NeZero q] [NeZero m] (S : ColoredSubspaces n K q m t)

theorem orthogonal {alpha beta : Fin t} (hab : alpha ≠ beta)
    {psi phi : SS.State n ℂ} (hp : psi ∈ S.space alpha)
    (hf : phi ∈ S.space beta) : SS.innerC psi phi = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hpx : psi x = 0
  · simp [hpx]
  · have hfx : phi x = 0 := by
      by_contra hfx
      have heq := (S.fiber alpha hp x hpx).symm.trans (S.fiber beta hf x hfx)
      exact hab (S.color_distinct (scaledColor_injective S.modulus_dvd heq))
    simp [hfx]

theorem independent : iSupIndep S.space := by
  let zeta := D3NormalizedFiniteToReal.canonicalRoot q
  have hzeta := D3NormalizedFiniteToReal.canonicalRoot_primitive q
  have hinj : Function.Injective (fun alpha => Cyclic.chi zeta (scaledColor q (S.color alpha))) :=
    (Cyclic.chi_injective zeta hzeta).comp
      ((scaledColor_injective S.modulus_dvd).comp S.color_distinct)
  apply ((diagonalEnd (finiteLocalPhase zeta hzeta S.angle)).eigenspaces_iSupIndep.comp hinj).mono
  intro alpha
  dsimp only [Function.comp_def]
  rw [← fiberSubspace_eq_eigenspace S.angle _ zeta hzeta]
  exact S.fiber alpha

def reindex : Fin K ≃ (Σ alpha, Fin (S.rank alpha)) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_sigma] using S.rank_sum.symm)

def sectorFrame (alpha : Fin t) : OrthonormalFrame n (S.rank alpha) :=
  SubspaceCode.frame (S.space alpha) (S.dimension alpha)

theorem sectorFrame_mem (alpha : Fin t) (i : Fin (S.rank alpha)) :
    (S.sectorFrame alpha).vec i ∈ S.space alpha :=
  SubspaceCode.frame_mem _ _ _

theorem codeSpan_sectorFrame (alpha : Fin t) :
    codeSpan (S.sectorFrame alpha) = S.space alpha :=
  SubspaceCode.codeSpan_frame _ _

theorem sigma_orthonormal (i j : Σ alpha, Fin (S.rank alpha)) :
    SS.innerC ((S.sectorFrame i.1).vec i.2) ((S.sectorFrame j.1).vec j.2) =
      if i = j then 1 else 0 := by
  classical
  obtain ⟨alpha, i⟩ := i
  obtain ⟨beta, j⟩ := j
  by_cases h : alpha = beta
  · subst beta
    rw [(S.sectorFrame alpha).orthonormal]
    simp
  · rw [S.orthogonal h (S.sectorFrame_mem alpha i) (S.sectorFrame_mem beta j)]
    simp [h]

def frame : OrthonormalFrame n K where
  vec i := (S.sectorFrame (S.reindex i).1).vec (S.reindex i).2
  orthonormal i j := by
    rw [S.sigma_orthonormal]
    simp

def coloredFrame : GeneralColoredConverse.ColoredFrame n K q m t where
  modulus_dvd := S.modulus_dvd
  angle := S.angle
  primitive := S.primitive
  sorted := S.sorted
  rank := S.rank
  rank_pos := S.rank_pos
  reindex := S.reindex
  frame := S.frame
  base := S.base
  color := S.color
  color_zero := S.color_zero
  color_distinct := S.color_distinct
  color_primitive := S.color_primitive
  fiber j := S.fiber (S.reindex j).1 (S.sectorFrame_mem _ _)

theorem sectorSpace_eq (alpha : Fin t) :
    GeneralColoredSubspaces.ColoredFrame.sectorSpace S.coloredFrame alpha = S.space alpha := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    change (S.sectorFrame (S.reindex (S.reindex.symm ⟨alpha, i⟩)).1).vec
      (S.reindex (S.reindex.symm ⟨alpha, i⟩)).2 ∈ S.space alpha
    rw [Equiv.apply_symm_apply]
    exact S.sectorFrame_mem alpha i
  · exact (GeneralColoredSubspaces.ColoredFrame.sectorSpace_finrank S.coloredFrame alpha).trans
      (S.dimension alpha).symm

theorem codeSpan_eq : codeSpan S.frame = ⨆ alpha, S.space alpha := by
  change codeSpan S.coloredFrame.frame = _
  rw [← GeneralColoredSubspaces.ColoredFrame.iSup_sectorSpace]
  simp only [S.sectorSpace_eq]

theorem finrank_sum :
    Module.finrank ℂ (⨆ alpha, S.space alpha : Submodule ℂ (SS.State n ℂ)) = K := by
  rw [← S.codeSpan_eq]
  exact finrank_codeSpan _

theorem frame_hasDistance (hKL : SubspaceCode.HasDistance (⨆ alpha, S.space alpha) d) :
    SS.HasDistance S.frame.vec d := by
  apply (SubspaceCode.hasDistance_iff _).1
  simpa only [S.codeSpan_eq] using hKL

/-- No orthonormal frame is assumed: the certified code is the supplied direct sum,
and the induced gate is the displayed `D(a;q)`, with exact projective order `m`. -/
theorem sslp_converse (hKL : SubspaceCode.HasDistance (⨆ alpha, S.space alpha) d)
    (hm : 2 ≤ m) :
    ∃ (C : ExactCode n K d) (u : diagonalSymmetryGroup (exactCodeProjector C)),
      codeSpan C.frame = (⨆ alpha, S.space alpha) ∧
      (u : LocalPhase n) = finiteLocalPhase
        (D3NormalizedFiniteToReal.canonicalRoot q)
        (D3NormalizedFiniteToReal.canonicalRoot_primitive q) S.angle ∧
      orderOf (intrinsicClass (exactCodeProjector C) u) = m ∧
      intrinsicClass (exactCodeProjector C) u ≠ 1 := by
  obtain ⟨C, u, hframe, hu, horder, hne⟩ :=
    S.coloredFrame.sslp_converse (S.frame_hasDistance hKL) hm
  exact ⟨C, u, hframe ▸ S.codeSpan_eq, hu, horder, hne⟩

end ColoredSubspaces

end

end MainTheory.GeneralColoredSubspaceConverse
