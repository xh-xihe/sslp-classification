import MainTheory.SixQubitSemanticEntrance

/-!
# Fresh distance-three sparse phase assembly

This file implements the semantic step in `main.tex`,
`eq:binary-simplex-vectors`--`eq:phase-agreement-on-support`, without
identifying the denominator of the newly constructed rational phase with the
order of any previously supplied finite generator.

The output order is always

```
P.order = Denominator.lcmDen P.fullSolution
```

for the freshly constructed sparse system `P`.  Packaging that phase as a new
`RankTwoGlobal.FiniteGeneratorResolution`, and proving that it induces the
same projective action on the code, are deliberately separate downstream
steps.  Thus an old modulus can never be smuggled into the sharp `q <= 9`
bound through a type parameter.
-/

namespace MainTheory.D3FreshSparseAssembly

open MainTheory
open MainTheory.SixQubitSemanticEntrance
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The normalized real phase is integral on every point of the first actual
logical support.  This is exactly `main.tex` equation `eq:h-integers`; it is a
semantic input here, rather than an unproved consequence of a name attached
to a matrix. -/
def IntegralOnActualSupport (psi : SS.State n ℂ)
    (theta : Fin n → ℝ) : Prop :=
  ∀ x, x ∈ CodeAffineSpanBridge.actualSupport psi →
    ∃ h : ℤ, MainTheory.RealGate.angle theta x = (h : ℝ)

/-- Once normalization removes the common eigenphase of the first logical
state, integrality on its entire *actual* support is a theorem, not an extra
matrix certificate.  No distinguished supported word is required: the
eigenvalue-one equation itself says that every supported diagonal phase has
complex exponential one. -/
theorem integralOnActualSupport_of_normalizedEigen
    (psi : SS.State n ℂ) (theta : Fin n → ℝ)
    (heigen : MainTheory.RealGate.realGate theta psi = psi) :
    IntegralOnActualSupport psi theta := by
  intro x hx
  have heigen' : MainTheory.RealGate.realGate theta psi =
      fun s => (1 : ℂ) * psi s := by
    simpa using heigen
  have hexp := MainTheory.RealGate.exp_eq_of_eigen
    theta psi 1 heigen' x hx
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨k, ?_⟩
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htwoPiI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hk' :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle theta x : ℂ) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
    rw [hk]
    ring
  exact_mod_cast mul_left_cancel₀ htwoPiI hk'

/-- Integral right-hand side obtained from the actual supported basis rows. -/
noncomputable def integralRhs
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta) :
    Fin B.rank → ℤ :=
  fun i => Classical.choose
    (hintegral (B.vertex i) (B.vertex_supported i))

theorem integralRhs_spec
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta)
    (i : Fin B.rank) :
    MainTheory.RealGate.angle theta (B.vertex i) =
      (integralRhs B theta hintegral i : ℝ) :=
  Classical.choose_spec
    (hintegral (B.vertex i) (B.vertex_supported i))

/-- The sparse system attached to the supported basis.  Its coordinate minor
is selected internally from real linear independence by
`Data.ofBitRows`; neither the minor nor its nonsingularity is an input. -/
noncomputable def sparseData
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta) :
    D3SparseRationalization.Data n B.rank := by
  apply D3SparseRationalization.Data.ofBitRows B.vertex
    (integralRhs B theta hintegral)
  simpa only [CodeAffineSpanBridge.bitPoint] using B.independent

@[simp] theorem sparseData_row
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta) :
    (sparseData B theta hintegral).row =
      D3SparseRationalization.bitRows B.vertex :=
  rfl

@[simp] theorem sparseData_rhs
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta) :
    (sparseData B theta hintegral).rhs =
      integralRhs B theta hintegral :=
  rfl

/-- The original real phase solves the integral supported-row system from
which the fresh sparse phase is constructed. -/
theorem originalPhase_solves
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta) :
    (((sparseData B theta hintegral).row.map (Int.castRingHom ℝ)).mulVec
        theta) =
      fun i => ((sparseData B theta hintegral).rhs i : ℝ) := by
  funext i
  have hi := integralRhs_spec B theta hintegral i
  simpa [Matrix.mulVec, dotProduct, D3SparseRationalization.bitRows,
    CodeAffineSpanBridge.bitPoint, MainTheory.RealGate.angle, mul_comm]
    using hi

/-- The fresh sparse phase and the original real phase agree on every Boolean
vertex in the span of the selected actual-support basis. -/
theorem angle_eq_of_mem_basisSpan
    {psi : SS.State n ℂ} (B : SupportedBitBasis psi)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport psi theta)
    (x : SS.BitString n)
    (hx : CodeAffineSpanBridge.bitPoint x ∈
      Submodule.span ℝ
        (Set.range (fun i =>
          CodeAffineSpanBridge.bitPoint (B.vertex i)))) :
    MainTheory.RealGate.angle
        (sparseData B theta hintegral).fullSolutionReal x =
      MainTheory.RealGate.angle theta x := by
  obtain ⟨w, hw⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hxrow :
      CodeAffineSpanBridge.bitPoint x = fun j =>
        ∑ i, w i *
          ((sparseData B theta hintegral).row i j : ℝ) := by
    funext j
    have hj := congrFun hw.symm j
    simpa [D3SparseRationalization.bitRows,
      CodeAffineSpanBridge.bitPoint] using hj
  have hdot :=
    (sparseData B theta hintegral).dot_eq_on_rowSpan theta
      (originalPhase_solves B theta hintegral)
      (CodeAffineSpanBridge.bitPoint x) w hxrow
  simpa [MainTheory.RealGate.angle, CodeAffineSpanBridge.bitPoint,
    mul_comm] using hdot

/-- `main.tex` equation `eq:phase-agreement-on-support`, for the actual
nonzero supports.  The left support is contained in its linear span.  A point
of the right support lies in its affine span, hence by the common-affine-span
certificate in the affine span of the left support, and therefore in the
left linear span.  No support point is replaced by a declared larger fibre. -/
theorem angle_eq_on_common_actualSupports
    {c d : SS.State n ℂ} (B : SupportedBitBasis c)
    (H : CodeAffineSpanBridge.CommonAffineSpanCertificate c d)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport c theta) :
    (∀ x, x ∈ CodeAffineSpanBridge.actualSupport c →
      MainTheory.RealGate.angle
          (sparseData B theta hintegral).fullSolutionReal x =
        MainTheory.RealGate.angle theta x) ∧
    (∀ x, x ∈ CodeAffineSpanBridge.actualSupport d →
      MainTheory.RealGate.angle
          (sparseData B theta hintegral).fullSolutionReal x =
        MainTheory.RealGate.angle theta x) := by
  constructor
  · intro x hx
    apply angle_eq_of_mem_basisSpan B theta hintegral x
    rw [B.span_eq]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · intro x hx
    apply angle_eq_of_mem_basisSpan B theta hintegral x
    rw [B.span_eq]
    apply affineSpan_subset_span
    rw [H.affineSpan_eq]
    exact mem_affineSpan ℝ ⟨x, hx, rfl⟩

/-! ## The freshly constructed phase and its own order -/

/-- The complete output of the direct distance-three sparse rationalization.

Its order is `data.order`; there is intentionally no modulus parameter in
this structure.  In particular, a modulus used merely to prove that the two
input supports are distinct cannot be confused with the least denominator of
the new phase. -/
structure FreshSparsePhase (c d : SS.State n ℂ) (theta : Fin n → ℝ) where
  basis : SupportedBitBasis c
  rank_pos : 1 ≤ basis.rank
  data : D3SparseRationalization.Data n basis.rank
  data_row : data.row = D3SparseRationalization.bitRows basis.vertex
  agreement_left : ∀ x, x ∈ CodeAffineSpanBridge.actualSupport c →
    MainTheory.RealGate.angle data.fullSolutionReal x =
      MainTheory.RealGate.angle theta x
  agreement_right : ∀ x, x ∈ CodeAffineSpanBridge.actualSupport d →
    MainTheory.RealGate.angle data.fullSolutionReal x =
      MainTheory.RealGate.angle theta x

/-- Assemble the fresh phase.  The auxiliary modulus `oldq`, angle, and
nonzero right residue are used only to rule out a zero-dimensional common
support span.  The returned phase has the independent order `data.order`. -/
noncomputable def assembleFreshSparsePhase
    {oldq : ℕ} [NeZero oldq]
    {c d : SS.State n ℂ}
    (H : CodeAffineSpanBridge.CommonAffineSpanCertificate c d)
    (oldAngle : Fin n → ZMod oldq) (rightResidue : ZMod oldq)
    (hright : SS.SSConditionState oldAngle rightResidue d)
    (hresidue : rightResidue ≠ 0)
    (theta : Fin n → ℝ) (hintegral : IntegralOnActualSupport c theta) :
    FreshSparsePhase c d theta := by
  let B := supportedBitBasis c
  have hrank : 1 ≤ B.rank :=
    SupportedBitBasis.rank_pos_of_commonAffineSpan
      B H oldAngle rightResidue hright hresidue
  let P := sparseData B theta hintegral
  have hagreement :=
    angle_eq_on_common_actualSupports B H theta hintegral
  exact
    { basis := B
      rank_pos := hrank
      data := P
      data_row := sparseData_row B theta hintegral
      agreement_left := hagreement.1
      agreement_right := hagreement.2 }

/-- Code-facing form of `assembleFreshSparsePhase`: after the first logical
state has been normalized to eigenvalue one, the integral support equations
are derived internally.  Thus callers cannot substitute an unrelated integer
right-hand side or merely assert `IntegralOnActualSupport` by name.  The old
finite residue data is still used only to prove that the common support span
has positive rank; the returned phase keeps its own fresh denominator. -/
noncomputable def assembleFreshSparsePhase_of_normalizedEigen
    {oldq : ℕ} [NeZero oldq]
    {c d : SS.State n ℂ}
    (H : CodeAffineSpanBridge.CommonAffineSpanCertificate c d)
    (oldAngle : Fin n → ZMod oldq) (rightResidue : ZMod oldq)
    (hright : SS.SSConditionState oldAngle rightResidue d)
    (hresidue : rightResidue ≠ 0)
    (theta : Fin n → ℝ)
    (heigen : MainTheory.RealGate.realGate theta c = c) :
    FreshSparsePhase c d theta :=
  assembleFreshSparsePhase H oldAngle rightResidue hright hresidue theta
    (integralOnActualSupport_of_normalizedEigen c theta heigen)

/-- At most `n` rows occur in the fresh binary simplex: they are linearly
independent vectors in an `n`-dimensional space.  (At six qubits this is the
"at most six" of the paper.) -/
theorem FreshSparsePhase.rank_le_six
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) : F.basis.rank ≤ n :=
  F.basis.rank_le_six

/-- The selected square minor of the fresh system is entrywise zero--one. -/
theorem FreshSparsePhase.minor_isZeroOne
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    BinaryBeta.IsZeroOne F.data.minor := by
  intro i j
  change F.data.row i (F.data.coordinate j) = 0 ∨
    F.data.row i (F.data.coordinate j) = 1
  rw [F.data_row]
  exact D3SparseRationalization.bitRows_isZeroOne F.basis.vertex
    i (F.data.coordinate j)

/-- The fresh least denominator divides the sharp denominator of the fresh
binary minor. -/
theorem FreshSparsePhase.order_dvd_inverseDenominator
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    F.data.order ∣ SharpClearing.inverseDenominator F.data.minor :=
  F.data.order_dvd_inverseDenominator

/-- The modular angle attached to the fresh least denominator is primitive. -/
theorem FreshSparsePhase.angle_primitive
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    Gate.Primitive F.data.order F.data.angle :=
  F.data.angle_primitive

/-- **Any binary denominator bound at size `n` bounds the fresh order.**

The minor is a nonsingular zero--one matrix of size at most `n`, so its
inverse denominator obeys the bound, and the fresh order divides it. -/
theorem FreshSparsePhase.order_le_of_betaBound {B : ℕ}
    (beta : BinaryBeta.BetaBound n B)
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    F.data.order ≤ B := by
  have hden : SharpClearing.inverseDenominator F.data.minor ≤ B :=
    beta F.basis.rank F.rank_pos F.rank_le_six F.data.minor
      F.minor_isZeroOne F.data.minor_nonsingular
  have hord : F.data.order ≤
      SharpClearing.inverseDenominator F.data.minor :=
    Nat.le_of_dvd
      (SharpClearing.inverseDenominator_pos F.data.minor)
      F.order_dvd_inverseDenominator
  exact hord.trans hden

/-- The universal six-variable binary bound applies to the *fresh* order. -/
theorem FreshSparsePhase.order_le_nine
    (betaSix : BinaryBeta.BetaBound 6 9)
    {c d : SS.State 6 ℂ} {theta : Fin 6 → ℝ}
    (F : FreshSparsePhase c d theta) :
    F.data.order ≤ 9 :=
  F.order_le_of_betaBound betaSix

/-- Exact support-angle agreement upgrades to equality of the two real
diagonal actions on the entire left state. -/
theorem FreshSparsePhase.realGate_eq_left
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    MainTheory.RealGate.realGate F.data.fullSolutionReal c =
      MainTheory.RealGate.realGate theta c := by
  funext x
  by_cases hx : c x = 0
  · simp [MainTheory.RealGate.realGate, hx]
  · have hangle := F.agreement_left x hx
    simp only [MainTheory.RealGate.realGate]
    rw [hangle]

/-- The same exact action equality holds on the right logical state. -/
theorem FreshSparsePhase.realGate_eq_right
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    MainTheory.RealGate.realGate F.data.fullSolutionReal d =
      MainTheory.RealGate.realGate theta d := by
  funext x
  by_cases hx : d x = 0
  · simp [MainTheory.RealGate.realGate, hx]
  · have hangle := F.agreement_right x hx
    simp only [MainTheory.RealGate.realGate]
    rw [hangle]

end

end MainTheory.D3FreshSparseAssembly
