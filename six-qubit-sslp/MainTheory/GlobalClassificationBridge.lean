import MainTheory.ClassificationLevels
import MainTheory.ProjectiveGroupFinite
import MainTheory.RankTwoGlobal

/-!
# Operator and intrinsic-group bridges for the global classification

This module connects three semantic layers which were previously only adjacent:

* an orthonormal frame and its matrix-kernel projector;
* a finite diagonal generator and an element of the *intrinsic* projective
  diagonal group of that projector;
* the residue-gap order in `RankTwoGlobal.TwoFiberCertificate` and the actual
  group-theoretic `orderOf` of the resulting quotient element.

The last connection is important: `TwoFiberCertificate.logicalOrder` is not
merely copied into the intrinsic group.  The kernel proves that a power of the
intrinsic class is trivial exactly when the corresponding eigenvalue ratio is
one, and hence that its `orderOf` is exactly the certified logical order.

The module also packages the remaining *global* inputs honestly.  Finiteness
of the whole intrinsic group still requires a bounded lift cover, and cyclicity
still requires a faithful phase-ratio character.  Neither is manufactured
from one resolved generator.
-/

namespace MainTheory.GlobalClassificationBridge

open MainTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-! ## A frame span is exactly the range of its kernel projector -/

/-- The matrix action of `CodeProjector.ofFrame` is the bra--ket projector
action from `CodeSpec`. -/
theorem kernelAction_ofFrame {n K : ℕ}
    (F : CodeSpec.OrthonormalFrame n K) (phi : SS.State n ℂ) :
    ClassificationLevels.kernelAction
        (ClassificationLevels.CodeProjector.ofFrame F).kernel phi =
      CodeSpec.projectorAction F phi := by
  funext x
  exact (CodeSpec.projectorAction_eq_kernel F phi x).symm

/-- The fixed-vector definition of the projector range agrees exactly with
the code span used by `CodeSpec`. -/
theorem inProjectorRange_ofFrame_iff {n K : ℕ}
    (F : CodeSpec.OrthonormalFrame n K) (phi : SS.State n ℂ) :
    ClassificationLevels.InProjectorRange
        (ClassificationLevels.CodeProjector.ofFrame F) phi ↔
      phi ∈ CodeSpec.codeSpan F := by
  rw [ClassificationLevels.InProjectorRange, kernelAction_ofFrame]
  exact (CodeSpec.mem_codeSpan_iff_projectorAction_eq F phi).symm

/-- The level-(i) projector attached to an exact code. -/
abbrev exactCodeProjector {n K d : ℕ} (C : CodeSpec.ExactCode n K d) :
    ClassificationLevels.CodeProjector n :=
  ClassificationLevels.CodeProjector.ofFrame C.frame

/-- The actual intrinsic projective diagonal group attached to an exact code,
not an abstract stand-in group. -/
abbrev IntrinsicGroup {n K d : ℕ} (C : CodeSpec.ExactCode n K d) :=
  ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup
    (exactCodeProjector C)

/-- The canonical quotient class is one exactly when its representative is
projectively trivial on the code. -/
theorem _root_.MainTheory.ClassificationLevels.intrinsicClass_eq_one_iff
    {n : ℕ} (P : ClassificationLevels.CodeProjector n)
    (u : ClassificationLevels.diagonalSymmetryGroup P) :
    ClassificationLevels.intrinsicClass P u = 1 ↔
      ClassificationLevels.IsProjectivelyTrivial P u := by
  change
    (u : ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup P) = 1 ↔
      u ∈ ClassificationLevels.projectivelyTrivialSubgroup P
  exact QuotientGroup.eq_one_iff u

/-! ## Diagonal actions as linear endomorphisms -/

/-- The pointwise local diagonal action as a complex-linear endomorphism. -/
def diagonalEnd {n : ℕ} (u : ClassificationLevels.LocalPhase n) :
    Module.End ℂ (SS.State n ℂ) where
  toFun := ClassificationLevels.diagonalAction u
  map_add' := by
    intro phi chi
    funext x
    simp [ClassificationLevels.diagonalAction]
    ring
  map_smul' := by
    intro a phi
    funext x
    simp [ClassificationLevels.diagonalAction]
    ring

@[simp] theorem diagonalEnd_apply {n : ℕ}
    (u : ClassificationLevels.LocalPhase n) (phi : SS.State n ℂ) :
    diagonalEnd u phi = ClassificationLevels.diagonalAction u phi := rfl

/-- `SameProjectiveOnCode` depends only on the code span, not on the chosen
orthonormal frame which presents it. -/
theorem sameProjectiveOnCode_congr_span {n K L : ℕ}
    (F : CodeSpec.OrthonormalFrame n K)
    (G : CodeSpec.OrthonormalFrame n L)
    (hspan : CodeSpec.codeSpan F = CodeSpec.codeSpan G)
    (U V : Module.End ℂ (SS.State n ℂ)) :
    CodeSpec.SameProjectiveOnCode F U V ↔
      CodeSpec.SameProjectiveOnCode G U V := by
  unfold CodeSpec.SameProjectiveOnCode
  rw [hspan]

/-- Projective triviality in the quotient-group definition is exactly
`CodeSpec.SameProjectiveOnCode` against the identity endomorphism. -/
theorem isProjectivelyTrivial_iff_sameProjectiveOnCode {n K : ℕ}
    (F : CodeSpec.OrthonormalFrame n K)
    (u : ClassificationLevels.diagonalSymmetryGroup
      (ClassificationLevels.CodeProjector.ofFrame F)) :
    ClassificationLevels.IsProjectivelyTrivial
        (ClassificationLevels.CodeProjector.ofFrame F) u ↔
      CodeSpec.SameProjectiveOnCode F
        (diagonalEnd (u : ClassificationLevels.LocalPhase n)) LinearMap.id := by
  constructor
  · rintro ⟨lam, hlam, hscalar⟩
    refine ⟨lam, hlam, ?_⟩
    intro phi hphi
    have hrange : ClassificationLevels.InProjectorRange
        (ClassificationLevels.CodeProjector.ofFrame F) phi :=
      (inProjectorRange_ofFrame_iff F phi).2 hphi
    simpa using hscalar phi hrange
  · rintro ⟨lam, hlam, hscalar⟩
    refine ⟨lam, hlam, ?_⟩
    intro phi hphi
    have hspan : phi ∈ CodeSpec.codeSpan F :=
      (inProjectorRange_ofFrame_iff F phi).1 hphi
    simpa using hscalar phi hspan

/-! ## A finite-order preserving phase is an actual diagonal symmetry -/

/-- If one diagonal phase maps a projector range into itself, so do all of
its nonnegative powers. -/
theorem diagonalAction_pow_preserves {n : ℕ}
    (P : ClassificationLevels.CodeProjector n)
    (u : ClassificationLevels.LocalPhase n)
    (hpres : ∀ phi,
      ClassificationLevels.InProjectorRange P phi →
      ClassificationLevels.InProjectorRange P
        (ClassificationLevels.diagonalAction u phi)) :
    ∀ k phi,
      ClassificationLevels.InProjectorRange P phi →
      ClassificationLevels.InProjectorRange P
        (ClassificationLevels.diagonalAction (u ^ k) phi) := by
  intro k
  induction k with
  | zero =>
      intro phi hphi
      simpa using hphi
  | succ k ih =>
      intro phi hphi
      rw [pow_succ, ClassificationLevels.diagonalAction_mul]
      exact ih _ (hpres _ hphi)

/-- For a phase of positive finite order, forward preservation already gives
preservation by the inverse and hence membership in the full symmetry group. -/
theorem preservesProjectorRange_of_finiteOrder {n q : ℕ}
    (P : ClassificationLevels.CodeProjector n)
    (u : ClassificationLevels.LocalPhase n)
    (hq : 0 < q) (hpow : u ^ q = 1)
    (hpres : ∀ phi,
      ClassificationLevels.InProjectorRange P phi →
      ClassificationLevels.InProjectorRange P
        (ClassificationLevels.diagonalAction u phi)) :
    ClassificationLevels.PreservesProjectorRange P u := by
  constructor
  · exact hpres
  · intro phi hphi
    have hmul : u ^ (q - 1) * u = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hq.ne')]
      exact hpow
    have hinv : u⁻¹ = u ^ (q - 1) :=
      (eq_inv_of_mul_eq_one_left hmul).symm
    rw [hinv]
    exact diagonalAction_pow_preserves P u hpres (q - 1) phi hphi

/-- A finite-order local phase whose linear action preserves a frame span is
an element of the diagonal symmetry group of the corresponding projector. -/
def finiteOrderSymmetryOfCodePreserving {n K q : ℕ}
    (F : CodeSpec.OrthonormalFrame n K)
    (u : ClassificationLevels.LocalPhase n)
    (hq : 0 < q) (hpow : u ^ q = 1)
    (hpres : CodeSpec.CodePreserving F (diagonalEnd u)) :
    ClassificationLevels.diagonalSymmetryGroup
      (ClassificationLevels.CodeProjector.ofFrame F) := by
  refine ⟨u, preservesProjectorRange_of_finiteOrder _ u hq hpow ?_⟩
  intro phi hphi
  rw [inProjectorRange_ofFrame_iff] at hphi ⊢
  exact hpres phi hphi

/-! ## Exact transcription of a root-of-unity gate as a local phase -/

/-- A primitive complex root of unity, regarded as an element of the unitary
subgroup of `ℂ`. -/
def primitiveRootUnitary {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) : unitary ℂ := by
  have hnorm : ‖zeta‖ = 1 := hzeta.norm'_eq_one (NeZero.ne q)
  have hnormSq : Complex.normSq zeta = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  refine ⟨zeta, ?_⟩
  constructor
  · exact SixQubit.CodeEquiv.unit_of_normSq hnormSq
  · rw [mul_comm]
    exact SixQubit.CodeEquiv.unit_of_normSq hnormSq

/-- The unitary character value of a residue. -/
def residueUnitary {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) (r : ZMod q) : unitary ℂ :=
  primitiveRootUnitary zeta hzeta ^ r.val

@[simp] theorem coe_residueUnitary {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) (r : ZMod q) :
    ((residueUnitary zeta hzeta r : unitary ℂ) : ℂ) =
      Cyclic.chi zeta r := by
  simp [residueUnitary, primitiveRootUnitary, Cyclic.chi]

/-- Local unitary phases represented by a finite angle vector. -/
def finiteLocalPhase {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) : ClassificationLevels.LocalPhase n :=
  fun j ↦ residueUnitary zeta hzeta (a j)

private theorem prod_chi_eq_chi_sum {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (s : SS.BitString n) (T : Finset (Fin n)) :
    (∏ j ∈ T, if s j then Cyclic.chi zeta (a j) else 1) =
      Cyclic.chi zeta (∑ j ∈ T, a j * SS.bit (s j)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cyclic.chi]
  | @insert j T hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        Cyclic.chi_add zeta hzeta, ih]
      cases s j <;> simp [SS.bit, Cyclic.chi]

/-- The matrix-kernel level product phase is exactly `Gate.diag`; no phase
convention is left implicit. -/
theorem diagonalValue_finiteLocalPhase {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (s : SS.BitString n) :
    ClassificationLevels.diagonalValue
        (finiteLocalPhase zeta hzeta a) s = Gate.diag zeta a s := by
  rw [Cyclic.diag_eq_chi]
  simpa [ClassificationLevels.diagonalValue, finiteLocalPhase, SS.weight]
    using prod_chi_eq_chi_sum zeta hzeta a s Finset.univ

/-- Consequently the local-phase action and the repository's finite gate are
definitionally the same physical operation after the preceding transcription. -/
theorem diagonalAction_finiteLocalPhase {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (phi : SS.State n ℂ) :
    ClassificationLevels.diagonalAction
        (finiteLocalPhase zeta hzeta a) phi = Gate.gate zeta a phi := by
  funext s
  rw [ClassificationLevels.diagonalAction, Gate.gate,
    diagonalValue_finiteLocalPhase]

/-- Every coordinate phase, and hence the full local phase, has `q`-th power
one.  Primitivity is not needed for this direction. -/
theorem finiteLocalPhase_pow_order {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) :
    finiteLocalPhase zeta hzeta a ^ q = 1 := by
  funext j
  apply Subtype.ext
  change (zeta ^ (a j).val) ^ q = 1
  rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]

/-! ## A resolved finite generator inside the intrinsic quotient -/

/-- The intrinsic diagonal symmetry represented by a supplied finite generator
resolution.  Inverse preservation is derived from its finite physical order. -/
def _root_.MainTheory.RankTwoGlobal.FiniteGeneratorResolution.intrinsicSymmetry
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    ClassificationLevels.diagonalSymmetryGroup (exactCodeProjector C) :=
  finiteOrderSymmetryOfCodePreserving C.frame
    (finiteLocalPhase G.zeta G.primitiveRoot G.angle)
    (Nat.pos_of_ne_zero (NeZero.ne q))
    (finiteLocalPhase_pow_order G.zeta G.primitiveRoot G.angle)
    (by
      intro phi hphi
      have hgate := G.codePreserving phi hphi
      simpa [diagonalEnd_apply, diagonalAction_finiteLocalPhase] using hgate)

/-- The actual quotient-group element induced by a supplied finite generator. -/
def _root_.MainTheory.RankTwoGlobal.FiniteGeneratorResolution.intrinsicClass
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) : IntrinsicGroup C :=
  ClassificationLevels.intrinsicClass (exactCodeProjector C) G.intrinsicSymmetry

private theorem exists_frame_amplitude_ne_zero {n K : ℕ}
    (F : CodeSpec.OrthonormalFrame n K) (k : Fin K) :
    ∃ x, F.vec k x ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : F.vec k = 0 := funext h
  have hself := F.orthonormal k k
  rw [hz] at hself
  simp [SS.innerC] at hself

private theorem scalar_eq_of_pointwise_mul
    {n : ℕ} {a b : ℂ} {phi : SS.State n ℂ}
    (hphi : ∃ x, phi x ≠ 0)
    (h : (fun x ↦ a * phi x) = fun x ↦ b * phi x) : a = b := by
  obtain ⟨x, hx⟩ := hphi
  exact mul_right_cancel₀ hx (congrFun h x)

/-- Every logical eigenvalue stored in a finite generator resolution is
nonzero; this is derived from the root-of-unity action and a nonzero frame
amplitude. -/
theorem _root_.MainTheory.RankTwoGlobal.FiniteGeneratorResolution.eigenvalue_ne_zero
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (k : Fin 2) :
    G.eigenvalue k ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_frame_amplitude_ne_zero G.eigenFrame k
  have heigen := congrFun (G.eigen k) x
  have hleft : Gate.diag G.zeta G.angle x * G.eigenFrame.vec k x ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (G.primitiveRoot.ne_zero (NeZero.ne q))
    · exact hx
  intro hk
  rw [Gate.gate, hk, zero_mul] at heigen
  exact hleft heigen

/-- A global eigenvector remains an eigenvector under every nonnegative power
of the same local diagonal phase. -/
theorem diagonalAction_pow_eigen {n : ℕ}
    (u : ClassificationLevels.LocalPhase n) (phi : SS.State n ℂ) (lam : ℂ)
    (heigen : ClassificationLevels.diagonalAction u phi = lam • phi) :
    ∀ k,
      ClassificationLevels.diagonalAction (u ^ k) phi = lam ^ k • phi := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        ClassificationLevels.diagonalAction (u ^ (k + 1)) phi =
            ClassificationLevels.diagonalAction (u ^ k * u) phi := by
              rw [pow_succ]
        _ = ClassificationLevels.diagonalAction (u ^ k)
              (ClassificationLevels.diagonalAction u phi) :=
            ClassificationLevels.diagonalAction_mul _ _ _
        _ = ClassificationLevels.diagonalAction (u ^ k) (lam • phi) := by
            rw [heigen]
        _ = lam • ClassificationLevels.diagonalAction (u ^ k) phi :=
            ClassificationLevels.diagonalAction_smul _ _ _
        _ = lam • (lam ^ k • phi) := by rw [ih]
        _ = lam ^ (k + 1) • phi := by
            simp only [smul_smul, pow_succ]
            ring_nf

/-- The finite local-phase transcription acts on the stored eigenframe with
the stored eigenvalues. -/
theorem _root_.MainTheory.RankTwoGlobal.FiniteGeneratorResolution.diagonalEigen
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (k : Fin 2) :
    ClassificationLevels.diagonalAction
        (finiteLocalPhase G.zeta G.primitiveRoot G.angle)
        (G.eigenFrame.vec k) = G.eigenvalue k • G.eigenFrame.vec k := by
  rw [diagonalAction_finiteLocalPhase]
  simpa using G.eigen k

/-- A power of the finite generator is scalar on the actual code exactly when
the corresponding eigenvalue ratio has that power equal to one. -/
theorem _root_.MainTheory.RankTwoGlobal.FiniteGeneratorResolution.sameProjective_power_iff_ratio
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (k : ℕ) :
    CodeSpec.SameProjectiveOnCode C.frame
        (diagonalEnd
          (finiteLocalPhase G.zeta G.primitiveRoot G.angle ^ k)) LinearMap.id ↔
      (G.eigenvalue 1 / G.eigenvalue 0) ^ k = 1 := by
  let u := finiteLocalPhase G.zeta G.primitiveRoot G.angle
  have heigenPow : ∀ i : Fin 2,
      ClassificationLevels.diagonalAction (u ^ k) (G.eigenFrame.vec i) =
        G.eigenvalue i ^ k • G.eigenFrame.vec i :=
    fun i ↦ diagonalAction_pow_eigen u _ _ (G.diagonalEigen i) k
  constructor
  · intro hscalar
    have hscalar' : CodeSpec.SameProjectiveOnCode G.eigenFrame
        (diagonalEnd (u ^ k)) LinearMap.id :=
      (sameProjectiveOnCode_congr_span C.frame G.eigenFrame G.span_eq _ _).1
        hscalar
    obtain ⟨lam, hlam, hframe⟩ :=
      (CodeSpec.sameProjectiveOnCode_iff_frame G.eigenFrame
        (diagonalEnd (u ^ k)) LinearMap.id).1 hscalar'
    have heq : ∀ i : Fin 2, G.eigenvalue i ^ k = lam := by
      intro i
      apply scalar_eq_of_pointwise_mul
        (exists_frame_amplitude_ne_zero G.eigenFrame i)
      calc
        (fun x ↦ G.eigenvalue i ^ k * G.eigenFrame.vec i x) =
            ClassificationLevels.diagonalAction (u ^ k)
              (G.eigenFrame.vec i) := by
                simpa using (heigenPow i).symm
        _ = diagonalEnd (u ^ k) (G.eigenFrame.vec i) := rfl
        _ = lam • LinearMap.id (G.eigenFrame.vec i) := hframe i
        _ = fun x ↦ lam * G.eigenFrame.vec i x := by rfl
    rw [div_pow, heq 1, heq 0, div_self hlam]
  · intro hratio
    have hzero : G.eigenvalue 0 ^ k ≠ 0 :=
      pow_ne_zero _ (G.eigenvalue_ne_zero 0)
    have hpowers : G.eigenvalue 1 ^ k = G.eigenvalue 0 ^ k := by
      apply (div_eq_one_iff_eq hzero).1
      simpa [div_pow] using hratio
    have hscalar' : CodeSpec.SameProjectiveOnCode G.eigenFrame
        (diagonalEnd (u ^ k)) LinearMap.id := by
      apply (CodeSpec.sameProjectiveOnCode_iff_frame G.eigenFrame
        (diagonalEnd (u ^ k)) LinearMap.id).2
      refine ⟨G.eigenvalue 0 ^ k, hzero, ?_⟩
      intro i
      fin_cases i
      · simpa using heigenPow 0
      · simpa [hpowers] using heigenPow 1
    exact
      (sameProjectiveOnCode_congr_span C.frame G.eigenFrame G.span_eq _ _).2
        hscalar'

/-- Quotient triviality of a generator power is exactly scalar action on the
actual code. -/
theorem _root_.MainTheory.RankTwoGlobal.FiniteGeneratorResolution.intrinsicClass_pow_eq_one_iff
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (k : ℕ) :
    G.intrinsicClass ^ k = 1 ↔
      (G.eigenvalue 1 / G.eigenvalue 0) ^ k = 1 := by
  let s := G.intrinsicSymmetry
  have hclassPow :
      ClassificationLevels.intrinsicClass (exactCodeProjector C) (s ^ k) =
        (ClassificationLevels.intrinsicClass (exactCodeProjector C) s) ^ k := by
    change QuotientGroup.mk (s ^ k) = (QuotientGroup.mk s) ^ k
    simp
  calc
    G.intrinsicClass ^ k = 1 ↔
        ClassificationLevels.IsProjectivelyTrivial
          (exactCodeProjector C) (s ^ k) := by
            rw [← ClassificationLevels.intrinsicClass_eq_one_iff]
            change
              (ClassificationLevels.intrinsicClass
                (exactCodeProjector C) s) ^ k = 1 ↔ _
            rw [← hclassPow]
    _ ↔ CodeSpec.SameProjectiveOnCode C.frame
          (diagonalEnd
            ((s ^ k : ClassificationLevels.diagonalSymmetryGroup
              (exactCodeProjector C)) : ClassificationLevels.LocalPhase n))
          LinearMap.id :=
        isProjectivelyTrivial_iff_sameProjectiveOnCode C.frame (s ^ k)
    _ ↔ CodeSpec.SameProjectiveOnCode C.frame
          (diagonalEnd
            (finiteLocalPhase G.zeta G.primitiveRoot G.angle ^ k))
          LinearMap.id := by rfl
    _ ↔ (G.eigenvalue 1 / G.eigenvalue 0) ^ k = 1 :=
        G.sameProjective_power_iff_ratio k

/-- The central semantic bridge: the `logicalOrder` derived from the residue
gap is exactly the group-theoretic order of the corresponding element in the
intrinsic projective diagonal group of the code projector. -/
theorem _root_.MainTheory.RankTwoGlobal.TwoFiberCertificate.intrinsic_order_eq
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    orderOf G.intrinsicClass = T.logicalOrder := by
  apply Nat.dvd_antisymm
  · apply (orderOf_dvd_iff_pow_eq_one).2
    apply (G.intrinsicClass_pow_eq_one_iff T.logicalOrder).2
    exact (T.ratio_order T.logicalOrder).2 (by
      simp [T.logicalOrder_eq])
  · rw [T.logicalOrder_eq]
    apply (T.ratio_order (orderOf G.intrinsicClass)).1
    apply (G.intrinsicClass_pow_eq_one_iff
      (orderOf G.intrinsicClass)).1
    exact pow_orderOf_eq_one G.intrinsicClass

/-- The paper's `m ∣ q`, now for the actual intrinsic quotient element rather
than only for the auxiliary residue gap. -/
theorem _root_.MainTheory.RankTwoGlobal.TwoFiberCertificate.intrinsic_order_dvd_physical
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    orderOf G.intrinsicClass ∣ q := by
  rw [T.intrinsic_order_eq]
  exact T.logicalOrder_dvd_physical

/-- Projective nontriviality is also transferred to the actual quotient
element. -/
theorem _root_.MainTheory.RankTwoGlobal.TwoFiberCertificate.intrinsic_class_ne_one
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    G.intrinsicClass ≠ 1 := by
  intro h
  have horder : orderOf G.intrinsicClass = 1 := orderOf_eq_one_iff.2 h
  rw [T.intrinsic_order_eq] at horder
  have htwo := T.two_le_logicalOrder
  omega

/-- A supplied primitive finite generator therefore yields, without any
additional order convention, an actual nontrivial intrinsic quotient element
whose group-theoretic order divides the physical order. -/
theorem finiteGenerator_intrinsic_order_certificate
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    ∃ m : ℕ,
      2 ≤ m ∧ m ∣ q ∧ orderOf G.intrinsicClass = m ∧
        G.intrinsicClass ≠ 1 := by
  obtain ⟨T⟩ := RankTwoGlobal.finiteGenerator_twoFiber G
  exact ⟨T.logicalOrder, T.two_le_logicalOrder,
    T.logicalOrder_dvd_physical, T.intrinsic_order_eq,
    T.intrinsic_class_ne_one⟩

/-! ## Honest global finite/cyclic aggregation -/

/-- Precisely the two still-required inputs for upgrading the intrinsic group
of a rank-two code from a type to a finite cyclic group.  The bounded cover is
the global completeness statement; the faithful character is the common
eigenbasis/phase-ratio statement.

At this interface level `cover.actionOf` is an abstract map into the intrinsic
group.  A future constructor must prove that it is the class of the physical
root-of-unity gate encoded by its label; the structure below does not itself
establish that semantic transcription for every label. -/
structure IntrinsicFiniteCyclicInputs {n d B : ℕ}
    (C : CodeSpec.ExactCode n 2 d) where
  cover : ProjectiveGroupFinite.BoundedLiftCover n B (IntrinsicGroup C)
  character : IntrinsicGroup C →* ℂ
  faithful : Function.Injective character

/-- The explicit global inputs make the *actual intrinsic group* finite. -/
theorem IntrinsicFiniteCyclicInputs.finite {n d B : ℕ}
    {C : CodeSpec.ExactCode n 2 d}
    (I : IntrinsicFiniteCyclicInputs (B := B) C) : Finite (IntrinsicGroup C) :=
  ProjectiveGroupFinite.finite_of_boundedLiftCover I.cover

/-- The same inputs make the actual intrinsic group cyclic. -/
theorem IntrinsicFiniteCyclicInputs.isCyclic {n d B : ℕ}
    {C : CodeSpec.ExactCode n 2 d}
    (I : IntrinsicFiniteCyclicInputs (B := B) C) : IsCyclic (IntrinsicGroup C) :=
  ProjectiveGroupFinite.isCyclic_of_boundedLiftCover
    I.cover I.character I.faithful

/-- The exact order set claimed in the six-qubit theorem, including the
identity. -/
def SixQubitAllowedOrder (m : ℕ) : Prop :=
  m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 5

/-- Orbit-specific no-go and realization work enters the global group theorem
through this explicit audit: every element of this code's intrinsic group has
one of the allowed orders.  This field is not inferred from the number `66`. -/
structure SixQubitIntrinsicInputs (C : CodeSpec.ExactCode 6 2 3)
    extends IntrinsicFiniteCyclicInputs (B := 9) C where
  orderAudit : ∀ g : IntrinsicGroup C, SixQubitAllowedOrder (orderOf g)

/-- The inherited global finite/cyclic inputs, reconstructed explicitly so
downstream proofs do not depend on a compiler-generated parent projection
name. -/
def SixQubitIntrinsicInputs.finiteCyclicInputs
    {C : CodeSpec.ExactCode 6 2 3} (I : SixQubitIntrinsicInputs C) :
    IntrinsicFiniteCyclicInputs (B := 9) C where
  cover := I.cover
  character := I.character
  faithful := I.faithful

/-- In a finite cyclic group, one element has order equal to the group
cardinality.  Therefore the elementwise exact no-go audit controls the actual
intrinsic group order. -/
theorem SixQubitIntrinsicInputs.groupCard_allowed
    {C : CodeSpec.ExactCode 6 2 3}
    (I : SixQubitIntrinsicInputs C) :
    SixQubitAllowedOrder (Nat.card (IntrinsicGroup C)) := by
  letI : Finite (IntrinsicGroup C) :=
    IntrinsicFiniteCyclicInputs.finite I.finiteCyclicInputs
  letI : IsCyclic (IntrinsicGroup C) :=
    IntrinsicFiniteCyclicInputs.isCyclic I.finiteCyclicInputs
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := IntrinsicGroup C)
  rw [← hg]
  exact I.orderAudit g

/-- A certified order-five intrinsic element forces the finite cyclic
intrinsic group itself to have order five. -/
theorem SixQubitIntrinsicInputs.groupCard_eq_five_of_element
    {C : CodeSpec.ExactCode 6 2 3}
    (I : SixQubitIntrinsicInputs C)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    Nat.card (IntrinsicGroup C) = 5 := by
  letI : Finite (IntrinsicGroup C) :=
    IntrinsicFiniteCyclicInputs.finite I.finiteCyclicInputs
  have hdiv : 5 ∣ Nat.card (IntrinsicGroup C) := by
    rw [← hg]
    exact orderOf_dvd_natCard g
  obtain ⟨k, hk⟩ := hdiv
  rcases I.groupCard_allowed with h | h | h | h <;> omega

/-!
The file deliberately stops here.  Constructing
`IntrinsicFiniteCyclicInputs` from an arbitrary code requires the bounded
semantic entrance for *every* diagonal symmetry and a common faithful
phase-ratio character.  Constructing `SixQubitIntrinsicInputs.orderAudit`
requires transporting every intrinsic element through the finite orbit
classification and the orbit-specific exact no-go/construction results.
Those are mathematical obligations, not typeclass search or bookkeeping.
-/

end

end MainTheory.GlobalClassificationBridge
