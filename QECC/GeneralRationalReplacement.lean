import QECC.AffineMoments
import QECC.SupportReplacement
import QECC.BinaryPhaseSystem
import QECC.SmithBounds
import QECC.PhaseTransport

namespace QECC

open scoped BigOperators

noncomputable section

/-- Regard a real vector of phase angles (measured in full turns) as a phase
vector in the circle. -/
def realVectorPhase {n : ℕ} (theta : Fin n → ℝ) : PhaseVector n :=
  fun j ↦ ((theta j : ℝ) : LocalPhase)

/-- Regard a rational vector of phase angles as a phase vector in the circle. -/
def rationalVectorPhase {n : ℕ} (theta : Fin n → ℚ) : PhaseVector n :=
  realVectorPhase fun j ↦ (theta j : ℝ)

@[simp] theorem realVectorPhase_zero {n : ℕ} :
    realVectorPhase (0 : Fin n → ℝ) = 0 := by
  rfl

@[simp] theorem realVectorPhase_add {n : ℕ} (theta phi : Fin n → ℝ) :
    realVectorPhase (theta + phi) = realVectorPhase theta + realVectorPhase phi := by
  funext j
  exact AddCircle.coe_add (1 : ℝ) (theta j) (phi j)

@[simp] theorem realVectorPhase_neg {n : ℕ} (theta : Fin n → ℝ) :
    realVectorPhase (-theta) = -realVectorPhase theta := by
  funext j
  exact AddCircle.coe_neg (1 : ℝ)

@[simp] theorem realVectorPhase_sub {n : ℕ} (theta phi : Fin n → ℝ) :
    realVectorPhase (theta - phi) = realVectorPhase theta - realVectorPhase phi := by
  rw [sub_eq_add_neg, realVectorPhase_add, realVectorPhase_neg]
  rfl

@[simp] theorem supportPhase_realVectorPhase {n : ℕ}
    (theta : Fin n → ℝ) (x : BitString n) :
    supportPhase (realVectorPhase theta) x =
      ((realSupportWeight theta x : ℝ) : LocalPhase) := by
  exact supportPhase_coe_real theta x

@[simp] theorem realSupportWeight_sub {n : ℕ}
    (theta phi : Fin n → ℝ) (x : BitString n) :
    realSupportWeight (theta - phi) x =
      realSupportWeight theta x - realSupportWeight phi x := by
  simp only [realSupportWeight, Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Expand the expectation of a linear support weight into its coordinate
first moments. -/
theorem weighted_realSupportWeight {n : ℕ} (p : BitString n → ℝ)
    (theta : Fin n → ℝ) :
    (∑ x : BitString n, p x * realSupportWeight theta x) =
      ∑ j : Fin n, theta j * ∑ x : BitString n, p x * bitReal (x j) := by
  classical
  simp only [realSupportWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- If a function is constant wherever a finite probability distribution is
positive, then its expectation is that constant. -/
theorem weighted_sum_eq_of_constant_on_positive_support
    {X : Type*} [Fintype X] (p f : X → ℝ) (c : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hmass : ∑ x, p x = 1)
    (hconstant : ∀ x, 0 < p x → f x = c) :
    ∑ x, p x * f x = c := by
  classical
  calc
    (∑ x, p x * f x) = ∑ x, p x * c := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : 0 < p x
      · rw [hconstant x hx]
      · have hpx : p x = 0 := le_antisymm (le_of_not_gt hx) (hp x)
        simp [hpx]
    _ = (∑ x, p x) * c := by rw [Finset.sum_mul]
    _ = c := by rw [hmass, one_mul]

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- Equality of the one-coordinate moments of two active-sector
distributions implies equality of the expectations of every real linear
support weight. -/
theorem sectorLinearExpectation_eq_of_commonFirstMoments
    (a : Fin n → ZMod q) (b c : C.ActiveResidue a)
    (hfirst : ∀ j : Fin n,
      (∑ x : BitString n,
          C.sectorDistribution a b x * bitReal (x j)) =
        ∑ x : BitString n,
          C.sectorDistribution a c x * bitReal (x j))
    (theta : Fin n → ℝ) :
    (∑ x : BitString n,
        C.sectorDistribution a b x * realSupportWeight theta x) =
      ∑ x : BitString n,
        C.sectorDistribution a c x * realSupportWeight theta x := by
  rw [weighted_realSupportWeight, weighted_realSupportWeight]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfirst j]

/-- Common first moments force the constants of a real linear functional on
two actual sector supports to agree.  No values on zero-probability basis
strings are needed. -/
theorem sectorConstants_eq_of_commonFirstMoments [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b c : C.ActiveResidue a)
    (hfirst : ∀ j : Fin n,
      (∑ x : BitString n,
          C.sectorDistribution a b x * bitReal (x j)) =
        ∑ x : BitString n,
          C.sectorDistribution a c x * bitReal (x j))
    (theta : Fin n → ℝ) (kb kc : ℝ)
    (hb : ∀ x ∈ C.actualSectorSupport a b,
      realSupportWeight theta x = kb)
    (hc : ∀ x ∈ C.actualSectorSupport a c,
      realSupportWeight theta x = kc) :
    kb = kc := by
  have hbavg :
      (∑ x : BitString n,
          C.sectorDistribution a b x * realSupportWeight theta x) = kb := by
    apply weighted_sum_eq_of_constant_on_positive_support
    · exact C.sectorDistribution_nonneg hq a hpres b
    · exact C.sum_sectorDistribution hq a hpres b
    · intro x hx
      exact hb x hx
  have hcavg :
      (∑ x : BitString n,
          C.sectorDistribution a c x * realSupportWeight theta x) = kc := by
    apply weighted_sum_eq_of_constant_on_positive_support
    · exact C.sectorDistribution_nonneg hq a hpres c
    · exact C.sum_sectorDistribution hq a hpres c
    · intro x hx
      exact hc x hx
  rw [← hbavg, ← hcavg]
  exact C.sectorLinearExpectation_eq_of_commonFirstMoments
    a b c hfirst theta

/-- Detection of all one-site number operators gives common first moments
for all active sectors. -/
theorem sectorFirstMoment_eq_of_detectsNumberOps [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hdetect : C.DetectsNumberOps) (j : Fin n)
    (b c : C.ActiveResidue a) :
    (∑ x : BitString n,
        C.sectorDistribution a b x * bitReal (x j)) =
      ∑ x : BitString n,
        C.sectorDistribution a c x * bitReal (x j) := by
  rcases hdetect with ⟨mu, hmu⟩
  have hoperator : binaryMonomial ({j} : Finset (Fin n)) = numberOp j := by
    classical
    ext x y
    simp [binaryMonomial, binaryMonomialValue, numberOp]
  have hdet : C.Detects (binaryMonomial ({j} : Finset (Fin n))) := by
    rw [hoperator]
    exact ⟨(mu j : ℂ), hmu j⟩
  have hmoment := C.sectorMoment_eq_of_detects_binaryMonomial
    hq a hpres ({j} : Finset (Fin n)) hdet b c
  simpa [binaryMonomialValue] using hmoment

/-- Under single-site number detection, a real linear functional that is
constant on each actual sector support has the same constant on every
active sector. -/
theorem sectorConstants_eq_of_detectsNumberOps [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hdetect : C.DetectsNumberOps)
    (theta : Fin n → ℝ) (k : C.ActiveResidue a → ℝ)
    (hconstant : ∀ (b : C.ActiveResidue a) x,
      x ∈ C.actualSectorSupport a b →
        realSupportWeight theta x = k b)
    (b c : C.ActiveResidue a) :
    k b = k c := by
  apply C.sectorConstants_eq_of_commonFirstMoments hq a hpres b c
    (fun j ↦ C.sectorFirstMoment_eq_of_detectsNumberOps
      hq a hpres hdetect j b c) theta
  · exact hconstant b
  · exact hconstant c

/-- A real physical vector and a real vector of sector phases solve an
integer affine system on the actual sector supports. -/
def SolvesActualSectorEquations
    (a : Fin n → ZMod q) (rhs : C.ActiveResidue a → BitString n → ℤ)
    (physical : Fin n → ℝ) (sectorPhase : C.ActiveResidue a → ℝ) : Prop :=
  ∀ (b : C.ActiveResidue a) x,
    x ∈ C.actualSectorSupport a b →
      realSupportWeight physical x - sectorPhase b = rhs b x

/-- Two solutions of the same actual-support equations differ by a constant
on each active sector support. -/
theorem supportWeight_sub_eq_sectorPhase_sub_of_solvesActualSectorEquations
    (a : Fin n → ZMod q) (rhs : C.ActiveResidue a → BitString n → ℤ)
    {physical physical' : Fin n → ℝ}
    {sectorPhase sectorPhase' : C.ActiveResidue a → ℝ}
    (hsol : C.SolvesActualSectorEquations a rhs physical sectorPhase)
    (hsol' : C.SolvesActualSectorEquations a rhs physical' sectorPhase')
    (b : C.ActiveResidue a) (x : BitString n)
    (hx : x ∈ C.actualSectorSupport a b) :
    realSupportWeight (physical' - physical) x =
      sectorPhase' b - sectorPhase b := by
  rw [realSupportWeight_sub]
  have h := hsol b x hx
  have h' := hsol' b x hx
  norm_num at h h' ⊢
  linarith

/-- If two actual-support solutions have common coordinate first moments,
then their circle-valued physical phases differ by one scalar on the code. -/
theorem actsAsScalar_realVectorPhase_sub_of_sameSectorEquations_of_commonFirstMoments
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hsupportPres : C.Preserves (phaseHom n q hq a))
    (hfirst : ∀ (b c : C.ActiveResidue a) (j : Fin n),
      (∑ x : BitString n,
          C.sectorDistribution a b x * bitReal (x j)) =
        ∑ x : BitString n,
          C.sectorDistribution a c x * bitReal (x j))
    (rhs : C.ActiveResidue a → BitString n → ℤ)
    (physical physical' : Fin n → ℝ)
    (sectorPhase sectorPhase' : C.ActiveResidue a → ℝ)
    (hsol : C.SolvesActualSectorEquations a rhs physical sectorPhase)
    (hsol' : C.SolvesActualSectorEquations a rhs physical' sectorPhase')
    (anchor : C.ActiveResidue a) :
    C.ActsAsScalar
      (realVectorPhase physical' - realVectorPhase physical) := by
  let delta : Fin n → ℝ := physical' - physical
  let k : C.ActiveResidue a → ℝ :=
    fun b ↦ sectorPhase' b - sectorPhase b
  have hconstant : ∀ (b : C.ActiveResidue a) x,
      x ∈ C.actualSectorSupport a b →
        realSupportWeight delta x = k b := by
    intro b x hx
    exact C.supportWeight_sub_eq_sectorPhase_sub_of_solvesActualSectorEquations
      a rhs hsol hsol' b x hx
  have hk (b : C.ActiveResidue a) : k b = k anchor :=
    C.sectorConstants_eq_of_commonFirstMoments hq a hsupportPres b anchor
      (hfirst b anchor) delta (k b) (k anchor) (hconstant b)
      (hconstant anchor)
  rw [← realVectorPhase_sub]
  apply C.actsAsScalar_of_constant_on_actualSectorSupports
    hq a hsupportPres (realVectorPhase delta) ((k anchor : ℝ) : LocalPhase)
  intro b x hx
  rw [supportPhase_realVectorPhase, hconstant b x hx, hk b]

/-- Number-operator detection supplies the common-first-moment hypothesis in
`actsAsScalar_realVectorPhase_sub_of_sameSectorEquations_of_commonFirstMoments`. -/
theorem actsAsScalar_realVectorPhase_sub_of_sameSectorEquations
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hsupportPres : C.Preserves (phaseHom n q hq a))
    (hdetect : C.DetectsNumberOps)
    (rhs : C.ActiveResidue a → BitString n → ℤ)
    (physical physical' : Fin n → ℝ)
    (sectorPhase sectorPhase' : C.ActiveResidue a → ℝ)
    (hsol : C.SolvesActualSectorEquations a rhs physical sectorPhase)
    (hsol' : C.SolvesActualSectorEquations a rhs physical' sectorPhase')
    (anchor : C.ActiveResidue a) :
    C.ActsAsScalar
      (realVectorPhase physical' - realVectorPhase physical) := by
  apply C.actsAsScalar_realVectorPhase_sub_of_sameSectorEquations_of_commonFirstMoments
    hq a hsupportPres
    (fun b c j ↦ C.sectorFirstMoment_eq_of_detectsNumberOps
      hq a hsupportPres hdetect j b c)
    rhs physical physical' sectorPhase sectorPhase' hsol hsol' anchor

/-- A rational physical solution of the same actual-support equations as a
preserving real solution represents the same projective logical class. -/
theorem rationalVectorPhase_same_projectiveClass_of_sameSectorEquations_of_commonFirstMoments
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hsupportPres : C.Preserves (phaseHom n q hq a))
    (hfirst : ∀ (b c : C.ActiveResidue a) (j : Fin n),
      (∑ x : BitString n,
          C.sectorDistribution a b x * bitReal (x j)) =
        ∑ x : BitString n,
          C.sectorDistribution a c x * bitReal (x j))
    (rhs : C.ActiveResidue a → BitString n → ℤ)
    (physical : Fin n → ℝ) (hphysical : C.Preserves (realVectorPhase physical))
    (sectorPhase : C.ActiveResidue a → ℝ)
    (rationalPhysical : Fin n → ℚ)
    (rationalSectorPhase : C.ActiveResidue a → ℚ)
    (hsol : C.SolvesActualSectorEquations a rhs physical sectorPhase)
    (hsolRat : C.SolvesActualSectorEquations a rhs
      (fun j ↦ (rationalPhysical j : ℝ))
      (fun b ↦ (rationalSectorPhase b : ℝ)))
    (anchor : C.ActiveResidue a) :
    ∃ hrat : C.Preserves (rationalVectorPhase rationalPhysical),
      C.projectiveClassMap ⟨rationalVectorPhase rationalPhysical, hrat⟩ =
        C.projectiveClassMap ⟨realVectorPhase physical, hphysical⟩ ∧
      C.ActsAsScalar
        (rationalVectorPhase rationalPhysical - realVectorPhase physical) := by
  let rationalPhysicalReal : Fin n → ℝ :=
    fun j ↦ (rationalPhysical j : ℝ)
  have hscalar : C.ActsAsScalar
      (realVectorPhase rationalPhysicalReal - realVectorPhase physical) :=
    C.actsAsScalar_realVectorPhase_sub_of_sameSectorEquations_of_commonFirstMoments
      hq a hsupportPres hfirst rhs physical rationalPhysicalReal
      sectorPhase (fun b ↦ (rationalSectorPhase b : ℝ))
      hsol hsolRat anchor
  have hscalar' : C.ActsAsScalar
      (rationalVectorPhase rationalPhysical - realVectorPhase physical) := by
    exact hscalar
  have hdiffPres : C.Preserves
      (rationalVectorPhase rationalPhysical - realVectorPhase physical) :=
    C.preserves_of_actsAsScalar hscalar'
  have hrat : C.Preserves (rationalVectorPhase rationalPhysical) := by
    have hadd := C.preserves_add hdiffPres hphysical
    simpa only [sub_add_cancel] using hadd
  refine ⟨hrat, ?_, hscalar'⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact hscalar'

/-- Under number-operator detection, a rational solution of the same
actual-support equations represents the same projective logical class. -/
theorem rationalVectorPhase_same_projectiveClass_of_sameSectorEquations
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hsupportPres : C.Preserves (phaseHom n q hq a))
    (hdetect : C.DetectsNumberOps)
    (rhs : C.ActiveResidue a → BitString n → ℤ)
    (physical : Fin n → ℝ) (hphysical : C.Preserves (realVectorPhase physical))
    (sectorPhase : C.ActiveResidue a → ℝ)
    (rationalPhysical : Fin n → ℚ)
    (rationalSectorPhase : C.ActiveResidue a → ℚ)
    (hsol : C.SolvesActualSectorEquations a rhs physical sectorPhase)
    (hsolRat : C.SolvesActualSectorEquations a rhs
      (fun j ↦ (rationalPhysical j : ℝ))
      (fun b ↦ (rationalSectorPhase b : ℝ)))
    (anchor : C.ActiveResidue a) :
    ∃ hrat : C.Preserves (rationalVectorPhase rationalPhysical),
      C.projectiveClassMap ⟨rationalVectorPhase rationalPhysical, hrat⟩ =
        C.projectiveClassMap ⟨realVectorPhase physical, hphysical⟩ ∧
      C.ActsAsScalar
        (rationalVectorPhase rationalPhysical - realVectorPhase physical) := by
  apply C.rationalVectorPhase_same_projectiveClass_of_sameSectorEquations_of_commonFirstMoments
    hq a hsupportPres
    (fun b c j ↦ C.sectorFirstMoment_eq_of_detectsNumberOps
      hq a hsupportPres hdetect j b c)
    rhs physical hphysical sectorPhase rationalPhysical rationalSectorPhase
    hsol hsolRat anchor

end CodeProjector

end

end QECC
