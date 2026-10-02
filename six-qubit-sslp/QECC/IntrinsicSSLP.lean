import QECC.ProjectiveSectorOrder
import QECC.PauliKL

namespace QECC

open scoped BigOperators

noncomputable section

namespace CodeProjector

variable {n K q d : ℕ} (C : CodeProjector n K)

/-- The positive dimensions of the active phase sectors add to the rank of
the code. -/
theorem sum_finrank_activeResidue [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    ∑ b : C.ActiveResidue a,
      Module.finrank ℂ (C.phaseSector a b.1) = K := by
  classical
  let p : ZMod q → Prop := fun b => C.phaseSector a b ≠ ⊥
  let s : Finset (ZMod q) := Finset.univ.filter p
  have hsub : ∑ b ∈ s, Module.finrank ℂ (C.phaseSector a b) =
      ∑ b : C.ActiveResidue a,
        Module.finrank ℂ (C.phaseSector a b.1) := by
    apply Finset.sum_subtype
    intro b
    simp [s, p]
  calc
    ∑ b : C.ActiveResidue a,
        Module.finrank ℂ (C.phaseSector a b.1) =
        ∑ b ∈ s, Module.finrank ℂ (C.phaseSector a b) := hsub.symm
    _ = ∑ b : ZMod q, Module.finrank ℂ (C.phaseSector a b) := by
      apply Finset.sum_subset (by simp [s])
      intro b _ hb
      have hbot : C.phaseSector a b = ⊥ := by
        simpa [s, p] using hb
      rw [Submodule.finrank_eq_zero.mpr hbot]
    _ = K := C.sum_finrank_phaseSector hq a hpres

/-- An intrinsic version of the general SSLP normal form, before the harmless
local-X translation and coordinate sorting.  The active residues are the
logical eigensectors, their dimensions are the multiplicities, and subtracting
one anchor removes the common logical scalar. -/
structure IntrinsicSSLPData
    (U : C.ProjectiveDiagonalGroup)
    (representative : ReducedDiagonalRepresentative n)
    (preserves : C.Preserves representative.phase)
    (anchor : C.ActiveResidue representative.a) : Prop where
  class_eq : C.projectiveClassMap ⟨representative.phase, preserves⟩ = U
  commonGCD_eq_one : representative.commonGCD = 1
  physicalOrder : orderOf (diagonalGate representative.phase) = representative.q
  logicalOrder_gt_one : 1 < addOrderOf U
  logicalOrder_dvd_physical : addOrderOf U ∣ representative.q
  relativeOrder :
    addOrderOf (C.relativeResidues representative.a anchor) = addOrderOf U
  relativeInjective : Function.Injective
    (C.relativeResidues representative.a anchor)
  multiplicityPositive : ∀ b : C.ActiveResidue representative.a,
    0 < Module.finrank ℂ (C.phaseSector representative.a b.1)
  multiplicitySum :
    letI : NeZero representative.q :=
      ⟨(lt_of_lt_of_le Nat.zero_lt_two representative.q_ge_two).ne'⟩
    ∑ b : C.ActiveResidue representative.a,
        Module.finrank ℂ (C.phaseSector representative.a b.1) = K
  supportedInFiber : ∀ (b : C.ActiveResidue representative.a)
    (psi : C.phaseSector representative.a b.1) (x : BitString n),
    subsetSum representative.a x ≠ b.1 → psi.1 x = 0

/-- Existence of the intrinsic normal-form data.  It is kept as a proposition
so witnesses obtained from the existence theorem for reduced representatives
remain usable directly in the statement. -/
def HasIntrinsicSSLPNormalForm (U : C.ProjectiveDiagonalGroup) : Prop :=
  ∃ (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a), C.IntrinsicSSLPData U R hpres b0

/-- A positive-rank code always has at least one active phase sector. -/
theorem exists_activeResidue [NeZero q] (hK : 0 < K) (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    Nonempty (C.ActiveResidue a) := by
  classical
  have hsum := C.sum_finrank_phaseSector hq a hpres
  by_contra hnone
  have hzero (b : ZMod q) :
      Module.finrank ℂ (C.phaseSector a b) = 0 := by
    apply Submodule.finrank_eq_zero.mpr
    by_contra hb
    exact hnone ⟨⟨b, hb⟩⟩
  have : K = 0 := by
    rw [← hsum]
    simp [hzero]
  omega

/-- A nonzero projective logical class forces the code rank to be positive.
For a rank-zero projector the code space is zero, hence the projector matrix
is zero and every preserving phase acts vacuously as a scalar. -/
theorem rank_pos_of_projectiveClass_ne_zero
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) : 0 < K := by
  classical
  by_contra hKpos
  have hKzero : K = 0 := Nat.eq_zero_of_not_pos hKpos
  have hspace : C.CodeSpace = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [C.codeSpace_finrank, hKzero]
  have hproj : C.proj = 0 := by
    ext x y
    let e : State n := computationalBasisState y
    have hmem : C.proj.mulVec e ∈ C.CodeSpace := ⟨e, rfl⟩
    rw [hspace, Submodule.mem_bot] at hmem
    have hentry := congrFun hmem x
    simpa [e, computationalBasisState, Matrix.mulVec, dotProduct] using hentry
  obtain ⟨theta, htheta⟩ :=
    (QuotientAddGroup.mk'_surjective C.scalarPhases) U
  apply hU
  rw [← htheta]
  apply (QuotientAddGroup.eq_zero_iff theta).2
  change C.ActsAsScalar theta.1
  refine ⟨0, fun x y hxy => ?_⟩
  exfalso
  exact hxy (by rw [hproj]; rfl)

/-- **Forward direction of the general SSLP theorem.**

For a distance-at-least-two code and a nonzero projective diagonal logical
class, the reduced physical representative supplied by the
first theorem decomposes the code into positive-dimensional subset-sum
sectors.  Relative active residues are distinct, have exact order equal to the
projective logical order, and their multiplicities add to `K`. -/
theorem intrinsic_sslp_normal_form
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    C.HasIntrinsicSSLPNormalForm U := by
  have hK : 0 < K := C.rank_pos_of_projectiveClass_ne_zero U hU
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp hd2)
  have hZ : C.DetectsSingleZ := C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo
  let H := C.finite_diagonal_logical_group_and_physical_representatives hZ
  letI : Finite C.ProjectiveDiagonalGroup := H.groupFinite
  obtain ⟨R, hpres, hclass, hgcd, hphysical, hdvd⟩ := H.representative U hU
  have hq : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  obtain ⟨b0⟩ := C.exists_activeResidue hK hq R.a hpres
  have hmpos : 0 < addOrderOf U := addOrderOf_pos U
  have hmne : addOrderOf U ≠ 1 := by
    intro hm
    apply hU
    exact AddMonoid.addOrderOf_eq_one_iff.mp hm
  have hmgt : 1 < addOrderOf U := by omega
  have hrelative := C.projectiveOrder_eq_relativeResiduesOrder hq R.a hpres b0
  have hrelative' :
      addOrderOf (C.relativeResidues R.a b0) = addOrderOf U := by
    rw [← hclass]
    exact hrelative.symm
  refine ⟨R, hpres, b0,
    { class_eq := hclass
      commonGCD_eq_one := hgcd
      physicalOrder := hphysical
      logicalOrder_gt_one := hmgt
      logicalOrder_dvd_physical := hdvd
      relativeOrder := hrelative'
      relativeInjective := ?_
      multiplicityPositive := fun b => C.activeResidue_finrank_pos R.a b
      multiplicitySum := C.sum_finrank_activeResidue hq R.a hpres
      supportedInFiber := fun _ psi _ hx => C.phaseSector_support psi hx }⟩
  intro b c hbc
  apply Subtype.ext
  change b.1 - b0.1 = c.1 - b0.1 at hbc
  exact sub_left_injective hbc

/-- **Converse order statement.**  Once a code is supported in modular phase
sectors and satisfies the full requested KL conditions, the residue-difference
order computes the exact projective logical order. -/
theorem sslp_converse_order_and_distance (hq : 0 < q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b0 : C.ActiveResidue a) (m d0 : ℕ)
    (horder : addOrderOf (C.relativeResidues a b0) = m)
    (hKL : C.HasDistanceAtLeast d0) :
    addOrderOf (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) = m ∧
      C.HasDistanceAtLeast d0 := by
  constructor
  · rw [C.projectiveOrder_eq_relativeResiduesOrder hq a hpres b0]
    exact horder
  · exact hKL

end CodeProjector

end

end QECC
