import MainTheory.GeneralSpectralRestrict

/-!
# General-rank spectral extraction, part three: assembling the sectors

Everything mathematical is in place: the code subspace is the internal
orthogonal direct sum of the eigenspaces of the restricted gate, for arbitrary
`n` and `K`.  What remains is to package that as the
`PhaseSectorFull.SectorDecomposition` the rest of the development consumes.

Mathlib's `subordinateOrthonormalBasis` does most of the work: it supplies an
orthonormal basis of the code subspace indexed by `Fin K`, each vector lying in
one eigenspace, together with the bijection
`(Sigma mu, Fin (finrank (eigenspace mu))) ≃ Fin K` that
`ExactCodeSectorLink` needs.
-/

namespace MainTheory.GeneralSpectral

open MainTheory.StateEuclidean
open MainTheory.UnitarySpectral

variable {n K : ℕ} {F : CodeSpec.OrthonormalFrame n K} {theta : Fin n → ℝ}
variable (hpres : CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta))

/-- The eigenvalues of the restricted gate, as a finite index type. -/
abbrev SectorIndex := Module.End.Eigenvalues (restrictedGate hpres)

/-- The eigenspace of one sector. -/
noncomputable abbrev sectorSpace (mu : SectorIndex hpres) :
    Submodule ℂ (euclideanCodeSpan F) :=
  Module.End.eigenspace (restrictedGate hpres) mu

/-- The orthogonal family of eigenspaces. -/
theorem sectorOrthogonalFamily :
    OrthogonalFamily ℂ (fun mu : SectorIndex hpres => sectorSpace hpres mu)
      fun mu => (sectorSpace hpres mu).subtypeₗᵢ :=
  orthogonalFamily_eigenspaces' (isUnitaryOn_restrictedGate hpres)

/-- **The bijection `ExactCodeSectorLink` needs**: the flattened sector index
is in bijection with `Fin K`. -/
noncomputable def sectorSigmaEquiv :
    (Σ mu : SectorIndex hpres, Fin (Module.finrank ℂ (sectorSpace hpres mu)))
      ≃ Fin K :=
  (directSum_isInternal_restricted hpres).sigmaOrthonormalBasisIndexEquiv
    (finrank_euclideanCodeSpan F) (sectorOrthogonalFamily hpres)

/-- The orthonormal basis of the code subspace subordinate to the sectors. -/
noncomputable def sectorBasis : OrthonormalBasis (Fin K) ℂ (euclideanCodeSpan F) :=
  (directSum_isInternal_restricted hpres).subordinateOrthonormalBasis
    (finrank_euclideanCodeSpan F) (sectorOrthogonalFamily hpres)

/-! ## The sector vectors -/

/-- The sector a given basis vector belongs to. -/
noncomputable def sectorOf (a : Fin K) : SectorIndex hpres :=
  (directSum_isInternal_restricted hpres).subordinateOrthonormalBasisIndex
    (finrank_euclideanCodeSpan F) a (sectorOrthogonalFamily hpres)

/-- Each basis vector lies in its own sector. -/
theorem sectorBasis_mem (a : Fin K) :
    sectorBasis hpres a ∈ sectorSpace hpres (sectorOf hpres a) :=
  (directSum_isInternal_restricted hpres).subordinateOrthonormalBasis_subordinate
    (finrank_euclideanCodeSpan F) a (sectorOrthogonalFamily hpres)

/-- A basis vector, back in the state space. -/
noncomputable def sectorVec (a : Fin K) : SS.State n ℂ :=
  ofEuclidean ((sectorBasis hpres a : euclideanCodeSpan F)
    : EuclideanSpace ℂ (SS.BitString n))

/-- **The sector vectors are orthonormal for the repository inner
product.** -/
theorem sectorVec_orthonormal (a b : Fin K) :
    SS.innerC (sectorVec hpres a) (sectorVec hpres b)
      = if a = b then 1 else 0 := by
  rw [StateEuclidean.innerC_eq_inner]
  have h : StateEuclidean.toEuclidean (sectorVec hpres a)
      = ((sectorBasis hpres a : euclideanCodeSpan F)
        : EuclideanSpace ℂ (SS.BitString n)) := rfl
  have h' : StateEuclidean.toEuclidean (sectorVec hpres b)
      = ((sectorBasis hpres b : euclideanCodeSpan F)
        : EuclideanSpace ℂ (SS.BitString n)) := rfl
  rw [h, h', ← Submodule.coe_inner]
  exact orthonormal_iff_ite.1 (sectorBasis hpres).orthonormal a b

/-- **Each sector vector is an eigenvector of the gate**, with the eigenvalue
of its sector. -/
theorem sectorVec_eigen (a : Fin K) :
    MainTheory.RealGate.realGate theta (sectorVec hpres a)
      = fun x => ((sectorOf hpres a : ℂ)) * sectorVec hpres a x := by
  have hmem := sectorBasis_mem hpres a
  rw [Module.End.mem_eigenspace_iff] at hmem
  have hcoe := congrArg (fun w : euclideanCodeSpan F =>
    (w : EuclideanSpace ℂ (SS.BitString n))) hmem
  simp only [restrictedGate_coe, Submodule.coe_smul] at hcoe
  funext x
  have hx := congrArg
    (fun w : EuclideanSpace ℂ (SS.BitString n) => StateEuclidean.ofEuclidean w x) hcoe
  simpa [sectorVec, euclideanGate_apply, StateEuclidean.toEuclidean,
    StateEuclidean.ofEuclidean] using hx

/-! ## Real arguments for the eigenvalues -/

/-- A unit-modulus complex number is `phaseExp` of a real number. -/
theorem exists_phaseExp {z : ℂ} (hz : ‖z‖= 1) :
    ∃ t : ℝ, MainTheory.PhaseSectorFull.phaseExp t = z := by
  obtain ⟨s, hs⟩ := (Complex.norm_eq_one_iff z).1 hz
  refine ⟨s / (2 * Real.pi), ?_⟩
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [MainTheory.PhaseSectorFull.phaseExp, ← hs]
  congr 1
  push_cast
  field_simp

/-- **Every sector eigenvalue has unit modulus.** -/
theorem norm_sectorEigenvalue (mu : SectorIndex hpres) :‖(mu : ℂ)‖= 1 := by
  have hev : Module.End.HasEigenvalue (restrictedGate hpres) (mu : ℂ) := mu.2
  have h := conj_mul_eigenvalue (isUnitaryOn_restrictedGate hpres) hev
  have hns : Complex.normSq ((mu : ℂ)) = 1 := by
    have hc : ((Complex.normSq ((mu : ℂ)) : ℝ) : ℂ) = 1 :=
      (Complex.normSq_eq_conj_mul_self).trans h
    exact_mod_cast hc
  have hsq :‖(mu : ℂ)‖^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  nlinarith [norm_nonneg ((mu : ℂ))]

/-- The real argument of a sector eigenvalue. -/
noncomputable def sectorPhase (mu : SectorIndex hpres) : ℝ :=
  Classical.choose (exists_phaseExp (norm_sectorEigenvalue hpres mu))

@[simp] theorem phaseExp_sectorPhase (mu : SectorIndex hpres) :
    MainTheory.PhaseSectorFull.phaseExp (sectorPhase hpres mu) = (mu : ℂ) :=
  Classical.choose_spec (exists_phaseExp (norm_sectorEigenvalue hpres mu))

/-! ## The sector of a flattened index -/

/-- The basis vector at a flattened index lies in the sector that index
names.  This is what lets the sector data be read off the `Sigma` type. -/
theorem sectorOf_sectorSigmaEquiv (mu : SectorIndex hpres)
    (r : Fin (Module.finrank ℂ (sectorSpace hpres mu))) :
    sectorOf hpres (sectorSigmaEquiv hpres ⟨mu, r⟩) = mu := by
  rw [sectorOf, DirectSum.IsInternal.subordinateOrthonormalBasisIndex_def,
    sectorSigmaEquiv] at *
  simp

/-! ## Assembling the sector decomposition -/

/-- The number of sectors. -/
noncomputable def sectorCount : ℕ := Fintype.card (SectorIndex hpres)

/-- Sectors indexed by `Fin t`, as `SectorDecomposition` requires. -/
noncomputable def sectorFin : Fin (sectorCount hpres) ≃ SectorIndex hpres :=
  (Fintype.equivFin (SectorIndex hpres)).symm

/-- The rank of one sector. -/
noncomputable def sectorRank (alpha : Fin (sectorCount hpres)) : ℕ :=
  Module.finrank ℂ (sectorSpace hpres (sectorFin hpres alpha))

/-- The flattened sector index is in bijection with `Fin K`.  Composing
Mathlib's subordinate-basis bijection with the `Fin t` reindexing of sectors. -/
noncomputable def flatEquiv :
    (Σ alpha : Fin (sectorCount hpres), Fin (sectorRank hpres alpha)) ≃ Fin K :=
  (Equiv.sigmaCongrLeft (β := fun mu : SectorIndex hpres =>
      Fin (Module.finrank ℂ (sectorSpace hpres mu))) (sectorFin hpres)).trans
    (sectorSigmaEquiv hpres)

/-- The sector frame vector at a flattened index. -/
noncomputable def sectorFrameVec
    (u : Σ alpha : Fin (sectorCount hpres), Fin (sectorRank hpres alpha)) :
    SS.State n ℂ :=
  sectorVec hpres (flatEquiv hpres u)

theorem sectorOf_flatEquiv
    (u : Σ alpha : Fin (sectorCount hpres), Fin (sectorRank hpres alpha)) :
    sectorOf hpres (flatEquiv hpres u) = sectorFin hpres u.1 :=
  sectorOf_sectorSigmaEquiv hpres _ _

theorem sectorFrameVec_eigen
    (u : Σ alpha : Fin (sectorCount hpres), Fin (sectorRank hpres alpha)) :
    MainTheory.RealGate.realGate theta (sectorFrameVec hpres u)
      = fun x => MainTheory.PhaseSectorFull.phaseExp
        (sectorPhase hpres (sectorFin hpres u.1)) * sectorFrameVec hpres u x := by
  rw [sectorFrameVec, sectorVec_eigen, phaseExp_sectorPhase, sectorOf_flatEquiv]

theorem sectorFrameVec_orthonormal
    (u v : Σ alpha : Fin (sectorCount hpres), Fin (sectorRank hpres alpha)) :
    SS.innerC (sectorFrameVec hpres u) (sectorFrameVec hpres v)
      = if u = v then 1 else 0 := by
  rw [sectorFrameVec, sectorFrameVec, sectorVec_orthonormal]
  simp only [(flatEquiv hpres).injective.eq_iff]

/-- Every sector has positive rank: its eigenspace is nonzero by definition. -/
theorem sectorRank_pos (alpha : Fin (sectorCount hpres)) :
    0 < sectorRank hpres alpha := by
  rw [sectorRank, Module.finrank_pos_iff]
  have hne : sectorSpace hpres (sectorFin hpres alpha) ≠ ⊥ :=
    (sectorFin hpres alpha).2
  exact Submodule.nontrivial_iff_ne_bot.2 hne

/-- The sector phases are distinct, because the eigenvalues are. -/
theorem sectorPhase_distinct :
    Function.Injective (fun alpha : Fin (sectorCount hpres) =>
      MainTheory.PhaseSectorFull.phaseExp (sectorPhase hpres (sectorFin hpres alpha))) := by
  intro a b hab
  simp only [phaseExp_sectorPhase] at hab
  exact (sectorFin hpres).injective (Subtype.ext hab)

/-- The number of sectors is positive: the code is nonzero, so the gate has an
eigenvalue on it. -/
theorem sectorCount_pos (C : CodeSpec.ExactCode n K d)
    (hF : F = C.frame) : 0 < sectorCount hpres := by
  subst hF
  rw [sectorCount, Fintype.card_pos_iff]
  haveI : Nontrivial (euclideanCodeSpan C.frame) := by
    rw [← Module.finrank_pos_iff (R := ℂ), finrank_euclideanCodeSpan]
    exact C.positiveRank
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue (restrictedGate hpres)
  exact ⟨⟨mu, hmu⟩⟩

/-- **The general-rank sector decomposition.** -/
noncomputable def sectorDecomposition (C : CodeSpec.ExactCode n K d)
    (hF : F = C.frame) :
    MainTheory.PhaseSectorFull.SectorDecomposition n (sectorCount hpres) theta where
  sectorCount_pos := sectorCount_pos hpres C hF
  rank := sectorRank hpres
  rank_pos := sectorRank_pos hpres
  vec := sectorFrameVec hpres
  orthonormal := sectorFrameVec_orthonormal hpres
  phase := fun alpha => sectorPhase hpres (sectorFin hpres alpha)
  phaseDistinct := sectorPhase_distinct hpres
  eigen := sectorFrameVec_eigen hpres

/-! ## The code-span link -/

/-- The sector vectors span the code subspace, inside the Euclidean space. -/
theorem span_sectorBasis :
    Submodule.span ℂ (Set.range fun a : Fin K =>
        ((sectorBasis hpres a : euclideanCodeSpan F)
          : EuclideanSpace ℂ (SS.BitString n)))
      = euclideanCodeSpan F := by
  have htop : Submodule.span ℂ
      (Set.range fun a : Fin K => (sectorBasis hpres a : euclideanCodeSpan F))
      = ⊤ := (sectorBasis hpres).toBasis.span_eq
  have := congrArg (Submodule.map (euclideanCodeSpan F).subtype) htop
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
  exact this

/-- **The sector vectors span the actual code.** -/
theorem span_sectorVec :
    CodeSpec.codeSpan F
      = Submodule.span ℂ (Set.range (sectorVec hpres)) := by
  have hmapback : Submodule.map (stateEquiv n).symm.toLinearMap
      (euclideanCodeSpan F) = CodeSpec.codeSpan F := by
    rw [euclideanCodeSpan, ← Submodule.map_comp]
    have : (stateEquiv n).symm.toLinearMap.comp (stateEquiv n).toLinearMap
        = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      simp
    rw [this, Submodule.map_id]
  calc CodeSpec.codeSpan F
      = Submodule.map (stateEquiv n).symm.toLinearMap (euclideanCodeSpan F) :=
        hmapback.symm
    _ = Submodule.map (stateEquiv n).symm.toLinearMap
          (Submodule.span ℂ (Set.range fun a : Fin K =>
            ((sectorBasis hpres a : euclideanCodeSpan F)
              : EuclideanSpace ℂ (SS.BitString n)))) := by
        rw [span_sectorBasis]
    _ = Submodule.span ℂ (Set.range (sectorVec hpres)) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl

/-! ## The link, and the extraction principle -/

/-- The reindexing required by `ExactCodeSectorLink`. -/
noncomputable def sectorReindex (C : CodeSpec.ExactCode n K d) (hF : F = C.frame) :
    Fin K ≃ (sectorDecomposition hpres C hF).Index :=
  (flatEquiv hpres).symm

/-- The reindexed sector frame is exactly the subordinate basis, carried back
to the state space. -/
theorem reindexedSectorFrame_vec (C : CodeSpec.ExactCode n K d)
    (hF : F = C.frame) (k : Fin K) :
    (MainTheory.FiniteLift.reindexedSectorFrame
      (sectorDecomposition hpres C hF) (sectorReindex hpres C hF)).vec k
      = sectorVec hpres k := by
  show sectorFrameVec hpres ((flatEquiv hpres).symm k) = _
  rw [sectorFrameVec, Equiv.apply_symm_apply]

/-- **The code-span link.** -/
noncomputable def sectorLink (C : CodeSpec.ExactCode n K d) (hF : F = C.frame) :
    MainTheory.FiniteLift.ExactCodeSectorLink C
      (sectorDecomposition hpres C hF) where
  reindex := sectorReindex hpres C hF
  span_eq := by
    subst hF
    rw [span_sectorVec hpres, CodeSpec.codeSpan]
    congr 1
    ext psi
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, reindexedSectorFrame_vec hpres C rfl k⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, (reindexedSectorFrame_vec hpres C rfl k).symm⟩

/-- **General-rank spectral extraction**: a code-preserving real diagonal gate
on an exact `((n, K, d))` code has a complete logical sector resolution, for
arbitrary `n`, `K` and `d`. -/
noncomputable def logicalSectorResolution (C : CodeSpec.ExactCode n K d)
    (hF : F = C.frame) :
    PhaseSectorBridge.LogicalSectorResolution C theta where
  sectorCount := sectorCount hpres
  sectors := sectorDecomposition hpres C hF
  link := sectorLink hpres C hF

/-- **The spectral extraction principle, for every code shape.**

This was the repository's last named semantic premise at general `(n, K, d)`:
`PhaseSectorBridge.SpectralExtractionPrinciple` had an inhabitant only at
`(6, 2, 3)`, by an argument special to rank two.  It is now a theorem for all
`n`, `K` and `d`. -/
theorem spectralExtractionPrinciple (n K d : ℕ) :
    PhaseSectorBridge.SpectralExtractionPrinciple n K d := by
  intro C theta hpres
  exact ⟨logicalSectorResolution (F := C.frame) hpres C rfl⟩

end MainTheory.GeneralSpectral
