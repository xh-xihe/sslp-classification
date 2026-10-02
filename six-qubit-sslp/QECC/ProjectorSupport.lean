import QECC.SectorProbabilities

namespace QECC

open scoped BigOperators ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A zero diagonal entry of a positive semidefinite complex matrix forces the
corresponding column to vanish. -/
theorem posSemidef_mulVec_computationalBasisState_eq_zero_of_diag_eq_zero
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ι)
    (hxx : A x x = 0) :
    A.mulVec (fun y => if y = x then 1 else 0) = 0 := by
  rw [← hA.dotProduct_mulVec_zero_iff]
  simp [dotProduct, Matrix.mulVec, hxx]

/-- A zero diagonal entry of a positive semidefinite complex matrix forces the
corresponding row to vanish. -/
theorem posSemidef_mulVec_apply_eq_zero_of_diag_eq_zero
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ι)
    (hxx : A x x = 0) (v : ι → ℂ) :
    A.mulVec v x = 0 := by
  have hcol :=
    posSemidef_mulVec_computationalBasisState_eq_zero_of_diag_eq_zero hA x hxx
  have hherm := hA.1
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _
  have hyx : A y x = 0 := by
    have := congrFun hcol y
    simpa [Matrix.mulVec, dotProduct] using this
  have hxy : A x y = 0 := by
    have hentry := congrFun (congrFun hherm y) x
    simp only [Matrix.conjTranspose_apply] at hentry
    rw [hyx] at hentry
    apply star_injective
    simpa using hentry
  simp [hxy]

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- The actual computational-basis support of an active phase sector.  It is
the positive support of the normalized diagonal of the sector projector. -/
def actualSectorSupport (a : Fin n → ZMod q) (b : C.ActiveResidue a) :
    Set (BitString n) :=
  {x | 0 < C.sectorDistribution a b x}

@[simp] theorem mem_actualSectorSupport_iff
    (a : Fin n → ZMod q) (b : C.ActiveResidue a) (x : BitString n) :
    x ∈ C.actualSectorSupport a b ↔ 0 < C.sectorDistribution a b x :=
  Iff.rfl

/-- Membership in actual sector support supplies the strict positivity used by
support averaging arguments. -/
theorem sectorDistribution_pos_of_mem_actualSectorSupport
    (a : Fin n → ZMod q) (b : C.ActiveResidue a) (x : BitString n)
    (hx : x ∈ C.actualSectorSupport a b) :
    0 < C.sectorDistribution a b x :=
  hx

/-- **Common first moments of logical phase sectors.**

If the code detects every one-site number operator, its detected scalars form
a vector `mu` such that every active-sector distribution is strictly positive
on its actual support, has total mass one, and has coordinate mean `mu j`.
The sums are over all bit strings, viewing each sector distribution as its
zero extension away from the actual support. -/
theorem phaseSectors_positive_probability_commonFirstMoments
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hdetect : C.DetectsNumberOps) :
    ∃ mu : Fin n → ℝ,
      (∀ j, C.proj * numberOp j * C.proj = (mu j : ℂ) • C.proj) ∧
      ∀ b : C.ActiveResidue a,
        (∀ x : BitString n, x ∈ C.actualSectorSupport a b →
          0 < C.sectorDistribution a b x) ∧
        (∑ x : BitString n, C.sectorDistribution a b x) = 1 ∧
        ∀ j : Fin n,
          (∑ x : BitString n,
            C.sectorDistribution a b x * bitReal (x j)) = mu j := by
  rcases hdetect with ⟨mu, hmu⟩
  refine ⟨mu, hmu, ?_⟩
  intro b
  refine ⟨fun x hx ↦
      C.sectorDistribution_pos_of_mem_actualSectorSupport a b x hx,
    C.sum_sectorDistribution hq a hpres b, ?_⟩
  intro j
  have hmonomial :
      binaryMonomial ({j} : Finset (Fin n)) = numberOp j := by
    classical
    ext x y
    simp [binaryMonomial, binaryMonomialValue, numberOp]
  calc
    (∑ x : BitString n,
        C.sectorDistribution a b x * bitReal (x j)) =
        ∑ x : BitString n,
          C.sectorDistribution a b x *
            binaryMonomialValue ({j} : Finset (Fin n)) x := by
              simp [binaryMonomialValue]
    _ = C.normalizedSectorTrace a b
          (binaryMonomial ({j} : Finset (Fin n))) :=
      C.sectorMoment_eq_normalizedSectorTrace a b
        ({j} : Finset (Fin n))
    _ = C.normalizedSectorTrace a b (numberOp j) := by rw [hmonomial]
    _ = mu j := by
      simpa using C.normalizedSectorTrace_eq_detectedScalar hq a hpres
        (numberOp j) (mu j : ℂ) (hmu j) b

/-- Every active sector has nonempty actual support. -/
theorem actualSectorSupport_nonempty [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b : C.ActiveResidue a) :
    (C.actualSectorSupport a b).Nonempty := by
  by_contra hempty
  have hnpos (x : BitString n) : ¬ 0 < C.sectorDistribution a b x := by
    intro hx
    exact hempty ⟨x, hx⟩
  have hzero (x : BitString n) : C.sectorDistribution a b x = 0 := by
    apply le_antisymm
    · exact le_of_not_gt (hnpos x)
    · exact C.sectorDistribution_nonneg hq a hpres b x
  have hsum := C.sum_sectorDistribution hq a hpres b
  simp only [hzero, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- Actual sector support is contained in the corresponding full subset-sum
fiber. -/
theorem actualSectorSupport_subset_fiber
    (a : Fin n → ZMod q) (b : C.ActiveResidue a) :
    C.actualSectorSupport a b ⊆ subsetSumFiber a b.1 := by
  intro x hx
  change subsetSum a x = b.1
  by_contra hne
  have hz := C.sectorDistribution_eq_zero_of_not_mem a b x hne
  exact (ne_of_gt hx) hz

/-- Distinct active sectors have disjoint actual supports. -/
theorem actualSectorSupport_disjoint
    (a : Fin n → ZMod q) {b c : C.ActiveResidue a} (hbc : b ≠ c) :
    Disjoint (C.actualSectorSupport a b) (C.actualSectorSupport a c) := by
  rw [Set.disjoint_left]
  intro x hxb hxc
  have hb := C.actualSectorSupport_subset_fiber a b hxb
  have hc := C.actualSectorSupport_subset_fiber a c hxc
  apply hbc
  apply Subtype.ext
  exact hb.symm.trans hc

/-- Every vector in a phase sector vanishes outside the actual support of
that sector. -/
theorem phaseSector_vanishes_off_actualSupport [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b : C.ActiveResidue a) (psi : C.phaseSector a b.1)
    (x : BitString n) (hx : x ∉ C.actualSectorSupport a b) :
    psi.1 x = 0 := by
  have hnonneg := C.sectorDistribution_nonneg hq a hpres b x
  have hdist : C.sectorDistribution a b x = 0 := by
    exact le_antisymm (le_of_not_gt hx) hnonneg
  have hk : (C.sectorDimension a b.1 : ℝ) ≠ 0 := by
    exact_mod_cast (C.sectorDimension_pos a b).ne'
  have hdiagRe : (C.sectorProjector a b.1 x x).re = 0 := by
    unfold sectorDistribution at hdist
    exact (div_eq_zero_iff.mp hdist).resolve_right hk
  have hdiag : C.sectorProjector a b.1 x x = 0 := by
    have hreal := C.sectorProjector_diag_eq_re hq a hpres b.1 x
    have hz : ((C.sectorProjector a b.1 x x).re : ℂ) = 0 := by
      rw [hdiagRe]
      norm_num
    exact hreal.symm.trans hz
  have hpsd := C.sectorProjector_posSemidef hq a hpres b.1
  have hrow := posSemidef_mulVec_apply_eq_zero_of_diag_eq_zero hpsd x hdiag
  have hrange := C.range_sectorProjector_mulVecLin hq a hpres b.1
  have hmem : psi.1 ∈ LinearMap.range (C.sectorProjector a b.1).mulVecLin := by
    rw [hrange]
    exact psi.2
  obtain ⟨v, hv⟩ := hmem
  rw [← hv]
  exact hrow v

/-- The actual computational-basis support of the whole code, expressed as
the union of its active phase-sector supports. -/
def actualCodeSupport [NeZero q] (a : Fin n → ZMod q) : Set (BitString n) :=
  {x | ∃ b : C.ActiveResidue a, x ∈ C.actualSectorSupport a b}

/-- The phase-sector components resolve every code vector. -/
theorem sum_phaseSectorComponent_coe_support [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (psi : C.CodeSpace) :
    ∑ b : ZMod q, (C.phaseSectorComponent hq a hpres b psi).1 = psi.1 := by
  funext x
  simp only [Finset.sum_apply, phaseSectorComponent_apply_coe,
    fiberProjector_mulVec_apply]
  rw [Finset.sum_eq_single (subsetSum a x)]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb h.symm
  · simp

/-- Every code vector vanishes away from the union of the actual supports of
its active sectors. -/
theorem codeSpace_vanishes_off_actualSupport [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (psi : C.CodeSpace) (x : BitString n)
    (hx : x ∉ C.actualCodeSupport a) :
    psi.1 x = 0 := by
  rw [← C.sum_phaseSectorComponent_coe_support hq a hpres psi]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : C.phaseSector a b = ⊥
  · have hcomponent : C.phaseSectorComponent hq a hpres b psi = 0 := by
      apply Subtype.ext
      exact (Submodule.mem_bot (R := ℂ)).mp
        (hb ▸ (C.phaseSectorComponent hq a hpres b psi).2)
    rw [hcomponent]
    rfl
  · let B : C.ActiveResidue a := ⟨b, hb⟩
    apply C.phaseSector_vanishes_off_actualSupport hq a hpres B
      (C.phaseSectorComponent hq a hpres b psi) x
    intro hxB
    apply hx
    exact ⟨B, hxB⟩

end CodeProjector

end

end QECC
