import QECC.ColoredSSLP

namespace QECC

open scoped BigOperators

noncomputable section

/--
An operator-level presentation of a finite orthogonal direct sum of subspaces,
with every summand supported in a distinct modular subset-sum fiber.

Each `component i` is the orthogonal projector onto the corresponding
summand.  The equations `hermitian`, `idempotent`, and `orthogonal` are the
matrix form of mutual orthogonality; `supported` records containment in the
fiber labelled by `residue i`.
-/
structure FiberProjectorFamily (n q : ℕ) (ι : Type*) [Fintype ι] where
  coefficient : Fin n → ZMod q
  residue : ι → ZMod q
  residue_injective : Function.Injective residue
  component : ι → Operator n
  hermitian : ∀ i, (component i).conjTranspose = component i
  idempotent : ∀ i, component i * component i = component i
  orthogonal : ∀ i j, i ≠ j → component i * component j = 0
  nonzero : ∀ i, component i ≠ 0
  supported : ∀ i x y, component i x y ≠ 0 →
    subsetSum coefficient x = residue i ∧
      subsetSum coefficient y = residue i

namespace FiberProjectorFamily

variable {n q ι : ℕ}

section GeneralIndex

variable {ι : Type*} [Fintype ι] (F : FiberProjectorFamily n q ι)

/-- The projector onto the direct sum is the sum of the component
projectors. -/
def totalProjector : Operator n := ∑ i, F.component i

theorem totalProjector_hermitian :
    F.totalProjector.conjTranspose = F.totalProjector := by
  classical
  rw [totalProjector, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact F.hermitian i

theorem totalProjector_idempotent :
    F.totalProjector * F.totalProjector = F.totalProjector := by
  classical
  simp only [totalProjector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact F.idempotent i
  · intro j _ hji
    exact F.orthogonal j i hji
  · simp

/-- The trace of a finite-dimensional idempotent is its rank. -/
private theorem trace_eq_rank_of_idempotent (P : Operator n)
    (hP : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  classical
  have hidem : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin * P.mulVecLin = P.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hP]
  have hp := LinearMap.IsIdempotentElem.isProj_range P.mulVecLin hidem
  calc
    P.trace = LinearMap.trace ℂ (State n) P.toLin' :=
      (Matrix.trace_toLin'_eq P).symm
    _ = LinearMap.trace ℂ (State n) P.mulVecLin := by
      rw [Matrix.toLin'_apply']
    _ = (Module.finrank ℂ (LinearMap.range P.mulVecLin) : ℂ) := hp.trace
    _ = (P.rank : ℂ) := rfl

/-- The multiplicity of a summand is the rank of its component projector. -/
def multiplicity (i : ι) : ℕ := Matrix.rank (F.component i)

/-- Every declared summand has strictly positive multiplicity. -/
theorem multiplicity_pos (i : ι) : 0 < F.multiplicity i := by
  classical
  rw [multiplicity, Matrix.rank, Module.finrank_pos_iff,
    Submodule.nontrivial_iff_ne_bot]
  intro hrange
  have hlin : (F.component i).mulVecLin = 0 :=
    LinearMap.range_eq_bot.mp hrange
  apply F.nonzero i
  ext x y
  have hv : (F.component i).mulVec (Pi.single y 1) = 0 := by
    change (F.component i).mulVecLin (Pi.single y 1) = 0
    rw [hlin]
    rfl
  rw [Matrix.mulVec_single_one] at hv
  exact congrFun hv x

/-- Orthogonal idempotent summands have additive rank. -/
theorem rank_totalProjector :
    Matrix.rank F.totalProjector = ∑ i, Matrix.rank (F.component i) := by
  classical
  apply Nat.cast_injective (R := ℂ)
  calc
    (Matrix.rank F.totalProjector : ℂ) = F.totalProjector.trace :=
      (trace_eq_rank_of_idempotent F.totalProjector
        F.totalProjector_idempotent).symm
    _ = ∑ i, (F.component i).trace := by
      simp [totalProjector, Matrix.trace_sum]
    _ = ∑ i, (Matrix.rank (F.component i) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact trace_eq_rank_of_idempotent (F.component i) (F.idempotent i)
    _ = ((∑ i, Matrix.rank (F.component i) : ℕ) : ℂ) := by
      simp

/-- The total projector rank is the sum of its positive multiplicities. -/
theorem rank_totalProjector_eq_sum_multiplicity :
    Matrix.rank F.totalProjector = ∑ i, F.multiplicity i := by
  simpa [multiplicity] using F.rank_totalProjector

/-- The code obtained from the orthogonal direct sum of all component
subspaces.  Its dimension is packaged as the sum of the strictly positive
component multiplicities. -/
def codeProjector : CodeProjector n (∑ i, F.multiplicity i) where
  proj := F.totalProjector
  hermitian := F.totalProjector_hermitian
  idempotent := F.totalProjector_idempotent
  rank_eq := F.rank_totalProjector_eq_sum_multiplicity

@[simp] theorem codeProjector_proj : F.codeProjector.proj = F.totalProjector :=
  rfl

/-- Every nonzero entry of the total projector lies inside one fiber block. -/
theorem subsetSum_eq_of_totalProjector_ne {x y : BitString n}
    (hxy : F.totalProjector x y ≠ 0) :
    subsetSum F.coefficient x = subsetSum F.coefficient y := by
  classical
  by_contra hne
  apply hxy
  rw [totalProjector]
  rw [Fintype.sum_apply, Fintype.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_contra hi
  obtain ⟨hx, hy⟩ := F.supported i x y hi
  exact hne (hx.trans hy.symm)

/-- The diagonal modular gate preserves the direct-sum code. -/
theorem codeProjector_preserves (hq : 0 < q) :
    F.codeProjector.Preserves (phaseHom n q hq F.coefficient) := by
  intro x y hxy
  rw [supportPhase_phaseHom, supportPhase_phaseHom]
  exact congrArg (zmodPhase q hq)
    (F.subsetSum_eq_of_totalProjector_ne hxy)

/-- Applying one component projector produces a vector supported in its
declared subset-sum fiber. -/
theorem component_mulVec_mem_fiber (i : ι) (v : State n) :
    (F.component i).mulVec v ∈
      fiberSubspace F.coefficient (F.residue i) := by
  classical
  intro x hx
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _
  have hentry : F.component i x y = 0 := by
    by_contra hne
    exact hx (F.supported i x y hne).1
  simp [hentry]

/-- A component range is contained in the range of the total projector. -/
theorem component_mulVec_mem_codeSpace (i : ι) (v : State n) :
    (F.component i).mulVec v ∈ F.codeProjector.CodeSpace := by
  rw [F.codeProjector.mem_codeSpace_iff]
  change F.totalProjector.mulVec ((F.component i).mulVec v) = _
  rw [Matrix.mulVec_mulVec]
  change ((∑ j, F.component j) * F.component i).mulVec v = _
  rw [Finset.sum_mul]
  have hmatrix : (∑ j, F.component j * F.component i) = F.component i := by
    rw [Finset.sum_eq_single i]
    · exact F.idempotent i
    · intro j _ hji
      exact F.orthogonal j i hji
    · simp
  rw [hmatrix]

/-- The subspace represented by one component projector. -/
abbrev componentRange (i : ι) : Submodule ℂ (State n) :=
  LinearMap.range (F.component i).mulVecLin

/-- Each component subspace is contained in its declared subset-sum fiber. -/
theorem componentRange_le_fiber (i : ι) :
    F.componentRange i ≤ fiberSubspace F.coefficient (F.residue i) := by
  rintro psi ⟨v, rfl⟩
  exact F.component_mulVec_mem_fiber i v

/-- Each component subspace is contained in the constructed code. -/
theorem componentRange_le_codeSpace (i : ι) :
    F.componentRange i ≤ F.codeProjector.CodeSpace := by
  rintro psi ⟨v, rfl⟩
  exact F.component_mulVec_mem_codeSpace i v

/-- Distinct component ranges have zero intersection.  Together with the
matrix equation `orthogonal`, this is the internal-direct-sum property. -/
theorem componentRange_disjoint {i j : ι} (hij : i ≠ j) :
    Disjoint (F.componentRange i) (F.componentRange j) := by
  rw [Submodule.disjoint_def]
  intro psi hpsi_i hpsi_j
  obtain ⟨v, hv⟩ := hpsi_i
  obtain ⟨w, hw⟩ := hpsi_j
  change (F.component i).mulVec v = psi at hv
  change (F.component j).mulVec w = psi at hw
  have hfix : (F.component i).mulVec psi = psi := by
    calc
      (F.component i).mulVec psi =
          (F.component i).mulVec ((F.component i).mulVec v) := by rw [hv]
      _ = (F.component i * F.component i).mulVec v :=
        Matrix.mulVec_mulVec _ _ _
      _ = (F.component i).mulVec v := by rw [F.idempotent i]
      _ = psi := hv
  calc
    psi = (F.component i).mulVec psi := hfix.symm
    _ = (F.component i).mulVec ((F.component j).mulVec w) := by rw [hw]
    _ = (F.component i * F.component j).mulVec w :=
      Matrix.mulVec_mulVec _ _ _
    _ = 0 := by rw [F.orthogonal i j hij]; simp

/-- The range of the total projector is exactly the sum of all component
ranges. -/
theorem iSup_componentRange_eq_codeSpace :
    (⨆ i, F.componentRange i) = F.codeProjector.CodeSpace := by
  classical
  apply le_antisymm
  · exact iSup_le fun i => F.componentRange_le_codeSpace i
  · intro psi hpsi
    obtain ⟨v, rfl⟩ := hpsi
    change F.totalProjector.mulVec v ∈ ⨆ i, F.componentRange i
    have hsum : F.totalProjector.mulVec v =
        ∑ i, (F.component i).mulVec v := by
      simpa [totalProjector] using
        Matrix.sum_mulVec (Finset.univ : Finset ι) F.component v
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun j => F.componentRange j) i) ⟨v, rfl⟩

/-- Every declared residue is an active residue of the direct-sum code. -/
def componentActiveResidue (i : ι) :
    F.codeProjector.ActiveResidue F.coefficient := by
  refine ⟨F.residue i, (Submodule.ne_bot_iff _).2 ?_⟩
  have hentry : ∃ x y, F.component i x y ≠ 0 := by
    by_contra h
    push_neg at h
    apply F.nonzero i
    ext x y
    exact h x y
  obtain ⟨x, y, hxy⟩ := hentry
  let psi := (F.component i).mulVec (Pi.single y 1)
  refine ⟨psi, ?_, ?_⟩
  · change psi ∈ F.codeProjector.CodeSpace ∧
      psi ∈ fiberSubspace F.coefficient (F.residue i)
    exact ⟨F.component_mulVec_mem_codeSpace i _,
      F.component_mulVec_mem_fiber i _⟩
  · intro hzero
    have hx := congrFun hzero x
    apply hxy
    simpa [psi, Matrix.mulVec, dotProduct] using hx

@[simp] theorem componentActiveResidue_value (i : ι) :
    (F.componentActiveResidue i).1 = F.residue i := rfl

theorem componentActiveResidue_injective :
    Function.Injective F.componentActiveResidue := by
  intro i j hij
  apply F.residue_injective
  exact congrArg Subtype.val hij

/-- Every active residue comes from one of the declared summands. -/
theorem componentActiveResidue_surjective :
    Function.Surjective F.componentActiveResidue := by
  classical
  intro b
  obtain ⟨psi, hpsi, hpsi_ne⟩ :=
    (Submodule.ne_bot_iff (F.codeProjector.phaseSector
      F.coefficient b.1)).1 b.2
  obtain ⟨x, hx⟩ : ∃ x, psi x ≠ 0 := Function.ne_iff.mp hpsi_ne
  have hxsum : subsetSum F.coefficient x = b.1 := by
    by_contra h
    exact hx (hpsi.2 x h)
  obtain ⟨v, hv⟩ := hpsi.1
  have htotal : F.totalProjector.mulVec v = psi := hv
  have hxnonzero : (∑ i, (F.component i).mulVec v x) ≠ 0 := by
    simpa [totalProjector, Matrix.sum_mulVec] using
      show F.totalProjector.mulVec v x ≠ 0 by rw [htotal]; exact hx
  have hexists : ∃ i, (F.component i).mulVec v x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxnonzero (by simp [h])
  obtain ⟨i, hi⟩ := hexists
  have hrow : subsetSum F.coefficient x = F.residue i := by
    by_contra h
    exact hi (F.component_mulVec_mem_fiber i v x h)
  refine ⟨i, Subtype.ext ?_⟩
  exact hrow.symm.trans hxsum

/-- The summand indices are canonically equivalent to the active residues of
the constructed code. -/
def activeResidueEquiv :
    ι ≃ F.codeProjector.ActiveResidue F.coefficient :=
  Equiv.ofBijective F.componentActiveResidue
    ⟨F.componentActiveResidue_injective,
      F.componentActiveResidue_surjective⟩

/-- Residues of the summands, measured relative to a chosen summand. -/
def relativeResidues (i0 : ι) : ι → ZMod q :=
  fun i => F.residue i - F.residue i0

@[simp] theorem relativeResidues_anchor (i0 : ι) :
    F.relativeResidues i0 i0 = 0 := by
  simp [relativeResidues]

/-- Reindexing the active residue differences along `activeResidueEquiv`
recovers exactly the declared residue differences. -/
theorem code_relativeResidues_comp_activeResidueEquiv (i0 : ι) :
    F.codeProjector.relativeResidues F.coefficient
        (F.componentActiveResidue i0) ∘ F.activeResidueEquiv =
      F.relativeResidues i0 := by
  funext i
  rfl

/-- A natural multiple kills every active residue difference exactly when it
kills every declared summand-label difference. -/
theorem nsmul_code_relativeResidues_eq_zero_iff (i0 : ι) (k : ℕ) :
    k • F.codeProjector.relativeResidues F.coefficient
        (F.componentActiveResidue i0) = 0 ↔
      k • F.relativeResidues i0 = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h (F.componentActiveResidue i)
    exact hi
  · intro h
    funext b
    obtain ⟨i, rfl⟩ := F.componentActiveResidue_surjective b
    exact congrFun h i

/-- The exact projective order of the induced logical gate is the additive
order of the declared residue-difference vector. -/
theorem projectiveOrder_eq_relativeResiduesOrder (hq : 0 < q) (i0 : ι) :
    addOrderOf
        (F.codeProjector.projectiveClassMap
          ⟨phaseHom n q hq F.coefficient, F.codeProjector_preserves hq⟩) =
      addOrderOf (F.relativeResidues i0) := by
  let hpres := F.codeProjector_preserves hq
  let b0 := F.componentActiveResidue i0
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    apply (F.codeProjector.nsmul_projectiveClass_eq_zero_iff
      hq F.coefficient hpres b0 _).2
    apply (F.nsmul_code_relativeResidues_eq_zero_iff i0 _).2
    exact addOrderOf_nsmul_eq_zero _
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    apply (F.nsmul_code_relativeResidues_eq_zero_iff i0 _).1
    apply (F.codeProjector.nsmul_projectiveClass_eq_zero_iff
      hq F.coefficient hpres b0 _).1
    exact addOrderOf_nsmul_eq_zero _

/-- If the declared residues are obtained from a primitive vector of colors,
then the induced projective logical gate has exactly the color modulus as its
order. -/
theorem projectiveOrder_eq_of_primitive_colors
    (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (hmq : m ∣ q)
    (i0 : ι) (gamma : ι → ZMod m)
    (hresidue : ∀ i, F.residue i = F.residue i0 +
      colorEmbed m q hmq (gamma i))
    (hprimitive : ColorPrimitive m gamma) :
    addOrderOf
        (F.codeProjector.projectiveClassMap
          ⟨phaseHom n q hq F.coefficient, F.codeProjector_preserves hq⟩) = m := by
  have hrelative : F.relativeResidues i0 =
      CodeProjector.colorVectorEmbed (ι := ι) m q hmq gamma := by
    funext i
    simp only [relativeResidues, CodeProjector.colorVectorEmbed]
    rw [hresidue i]
    simp
  rw [F.projectiveOrder_eq_relativeResiduesOrder hq i0, hrelative]
  rw [addOrderOf_injective
    (CodeProjector.colorVectorEmbed (ι := ι) m q hmq)
    (CodeProjector.colorVectorEmbed_injective m q hm hq hmq) gamma]
  exact hprimitive

/-- Full converse package: the fiber-supported orthogonal direct sum produces
a preserved code, primitive colors give projective order exactly `m`, and the
supplied Knill--Laflamme hypothesis is precisely the requested distance
conclusion. -/
theorem converse_order_and_distance
    (hq : 0 < q) (m d0 : ℕ) (hm : 2 ≤ m) (hmq : m ∣ q)
    (i0 : ι) (gamma : ι → ZMod m)
    (hresidue : ∀ i, F.residue i = F.residue i0 +
      colorEmbed m q hmq (gamma i))
    (hprimitive : ColorPrimitive m gamma)
    (hKL : F.codeProjector.HasDistanceAtLeast d0) :
    F.codeProjector.Preserves (phaseHom n q hq F.coefficient) ∧
      addOrderOf
        (F.codeProjector.projectiveClassMap
          ⟨phaseHom n q hq F.coefficient, F.codeProjector_preserves hq⟩) = m ∧
      F.codeProjector.HasDistanceAtLeast d0 := by
  exact ⟨F.codeProjector_preserves hq,
    F.projectiveOrder_eq_of_primitive_colors hq m hm hmq i0 gamma
      hresidue hprimitive,
    hKL⟩

end GeneralIndex

end FiberProjectorFamily

/-- **Direct-sum converse of the general SSLP theorem.**

The supplied orthogonal fiber projectors have positive multiplicities whose
sum is the rank of the constructed code.  Primitive colors give the modular
gate exact projective order `m`, while the supplied full KL hypothesis gives
the target distance. -/
theorem general_sslp_directSum_converse
    {n q : ℕ} {ι : Type*} [Fintype ι]
    (F : FiberProjectorFamily n q ι)
    (hq : 0 < q) (m d0 : ℕ) (hm : 2 ≤ m) (hmq : m ∣ q)
    (i0 : ι) (gamma : ι → ZMod m)
    (hresidue : ∀ i, F.residue i = F.residue i0 +
      colorEmbed m q hmq (gamma i))
    (hprimitive : ColorPrimitive m gamma)
    (hKL : F.codeProjector.HasDistanceAtLeast d0) :
    (∀ i, 0 < F.multiplicity i) ∧
      Matrix.rank F.totalProjector = ∑ i, F.multiplicity i ∧
      F.codeProjector.Preserves
        (phaseHom n q hq F.coefficient) ∧
      addOrderOf
        (F.codeProjector.projectiveClassMap
          ⟨phaseHom n q hq F.coefficient,
            F.codeProjector_preserves hq⟩) = m ∧
      F.codeProjector.HasDistanceAtLeast d0 := by
  obtain ⟨hpres, horder, hdistance⟩ :=
    F.converse_order_and_distance hq m d0 hm hmq i0 gamma
      hresidue hprimitive hKL
  exact ⟨F.multiplicity_pos, F.rank_totalProjector_eq_sum_multiplicity,
    hpres, horder, hdistance⟩

end

end QECC
