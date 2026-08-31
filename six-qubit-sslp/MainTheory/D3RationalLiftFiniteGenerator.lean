import MainTheory.D3NormalizedFiniteToReal
import MainTheory.GlobalClassificationBridge

/-!
# Packaging the qualitative rational lift as a finite generator

`FiniteLift.RationalColoredLift` already supplies exact rational physical
angles and proves projective agreement with the original real phase sectors.
This module performs the previously missing discrete packaging step: reduce
the least-denominator numerators modulo their own denominator, prove the angle
primitive, identify the standard-root gate with the rational real gate on the
full physical space, and build a `FiniteGeneratorResolution` spanning the
actual code.
-/

namespace MainTheory.D3RationalLiftFiniteGenerator

open MainTheory
open MainTheory.PhaseSectorFull
open scoped BigOperators

noncomputable section

/-- Modular physical angle of a qualitative rational lift. -/
def modularAngle {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) :
    Fin 6 → ZMod L.order :=
  fun j ↦ (L.numerator j : ZMod L.order)

/-- Least-denominator primitivity transported from integral numerators to
their canonical modular representatives. -/
theorem modularAngle_primitive {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) :
    Gate.Primitive L.order (modularAngle L) := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  intro d hdq hda
  apply L.primitive d hdq
  intro j
  have hdqZ : (d : ℤ) ∣ (L.order : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdq
  have hvalZ : (d : ℤ) ∣ ((modularAngle L j).val : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hda j)
  have hcast : (L.numerator j : ZMod L.order) =
      (((modularAngle L j).val : ℤ) : ZMod L.order) := by
    simp [modularAngle]
  have hqsub : (L.order : ℤ) ∣
      ((modularAngle L j).val : ℤ) - L.numerator j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (L.numerator j) ((modularAngle L j).val : ℤ) L.order).1 hcast
  have hnumZ := Int.dvd_sub hvalZ (hdqZ.trans hqsub)
  simpa using hnumZ

/-- Reduction of a possibly negative lift numerator does not change the
corresponding power of the standard root. -/
theorem canonicalRoot_pow_modularAngle_eq_zpow_numerator
    {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) (j : Fin 6) :
    D3NormalizedFiniteToReal.canonicalRoot L.order ^
        (modularAngle L j).val =
      D3NormalizedFiniteToReal.canonicalRoot L.order ^
        (L.numerator j : ℤ) := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  rw [← zpow_natCast]
  change D3NormalizedFiniteToReal.canonicalRoot L.order ^
      (((L.numerator j : ZMod L.order).val : ℕ) : ℤ) =
    D3NormalizedFiniteToReal.canonicalRoot L.order ^ L.numerator j
  rw [ZMod.val_intCast]
  have hroot : D3NormalizedFiniteToReal.canonicalRoot L.order ≠ 0 := by
    simp [D3NormalizedFiniteToReal.canonicalRoot]
  symm
  calc
    D3NormalizedFiniteToReal.canonicalRoot L.order ^ L.numerator j =
        D3NormalizedFiniteToReal.canonicalRoot L.order ^
          (L.numerator j % (L.order : ℤ) +
            (L.order : ℤ) * (L.numerator j / (L.order : ℤ))) := by
      rw [Int.emod_add_mul_ediv]
    _ = D3NormalizedFiniteToReal.canonicalRoot L.order ^
          (L.numerator j % (L.order : ℤ)) *
        D3NormalizedFiniteToReal.canonicalRoot L.order ^
          ((L.order : ℤ) * (L.numerator j / (L.order : ℤ))) := by
      rw [zpow_add₀ hroot]
    _ = D3NormalizedFiniteToReal.canonicalRoot L.order ^
          (L.numerator j % (L.order : ℤ)) := by
      rw [zpow_mul, zpow_natCast,
        (D3NormalizedFiniteToReal.canonicalRoot_primitive L.order).pow_eq_one,
        one_zpow, mul_one]

/-- Coordinate equality between the modular standard-root phase and the
rational real phase. -/
theorem canonicalRoot_pow_modularAngle
    {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) (j : Fin 6) :
    D3NormalizedFiniteToReal.canonicalRoot L.order ^
        (modularAngle L j).val =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          ((L.physical j : ℝ) : ℂ)) := by
  rw [canonicalRoot_pow_modularAngle_eq_zpow_numerator]
  rw [D3NormalizedFiniteToReal.canonicalRoot,
    ← Complex.exp_int_mul]
  apply congrArg Complex.exp
  have hreal : (L.numerator j : ℝ) =
      (L.order : ℝ) * (L.physical j : ℝ) := by
    exact_mod_cast (L.numerator_spec j).symm
  have hcomplex : (L.numerator j : ℂ) =
      (L.order : ℂ) * ((L.physical j : ℝ) : ℂ) := by
    exact_mod_cast hreal
  rw [hcomplex]
  have hq : (L.order : ℂ) ≠ 0 := by
    exact_mod_cast L.order_pos.ne'
  field_simp [hq]

private theorem prod_chi_eq_chi_sum {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin 6 → ZMod q) (s : SS.BitString 6) (S : Finset (Fin 6)) :
    (∏ j ∈ S, if s j then Cyclic.chi zeta (a j) else 1) =
      Cyclic.chi zeta (∑ j ∈ S, a j * SS.bit (s j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Cyclic.chi]
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        Cyclic.chi_add zeta hzeta, ih]
      cases s j <;> simp [SS.bit, Cyclic.chi]

/-- Equality of finite and rational-real diagonal values on every basis
string. -/
theorem finiteDiag_eq_rationalRealPhase
    {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) (s : SS.BitString 6) :
    Gate.diag (D3NormalizedFiniteToReal.canonicalRoot L.order)
        (modularAngle L) s =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle
            (fun j ↦ (L.physical j : ℝ)) s : ℂ)) := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  rw [Cyclic.diag_eq_chi]
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  calc
    Cyclic.chi (D3NormalizedFiniteToReal.canonicalRoot L.order)
        (SS.weight (modularAngle L) s) =
        ∏ j : Fin 6,
          if s j then
            D3NormalizedFiniteToReal.canonicalRoot L.order ^
              (modularAngle L j).val
          else 1 := by
      simpa [SS.weight, Cyclic.chi] using
        (prod_chi_eq_chi_sum
          (D3NormalizedFiniteToReal.canonicalRoot L.order)
          (D3NormalizedFiniteToReal.canonicalRoot_primitive L.order)
          (modularAngle L) s Finset.univ).symm
    _ = ∏ j : Fin 6,
          Complex.exp
            (A * ((if s j then (L.physical j : ℝ) else 0 : ℝ) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro j _
      cases s j <;> simp [A, canonicalRoot_pow_modularAngle]
    _ = Complex.exp
        (∑ j : Fin 6,
          A * ((if s j then (L.physical j : ℝ) else 0 : ℝ) : ℂ)) := by
      exact (Complex.exp_sum Finset.univ _).symm
    _ = Complex.exp
        (A *
          (MainTheory.RealGate.angle
            (fun j ↦ (L.physical j : ℝ)) s : ℂ)) := by
      congr 1
      simp only [MainTheory.RealGate.angle]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      cases s j <;> simp

/-- Equality of the full finite and rational-real gates. -/
theorem finiteGate_eq_rationalRealGate
    {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) :
    Gate.gate (D3NormalizedFiniteToReal.canonicalRoot L.order)
        (modularAngle L) =
      MainTheory.RealGate.realGate (fun j ↦ (L.physical j : ℝ)) := by
  funext psi s
  rw [Gate.gate, MainTheory.RealGate.realGate,
    finiteDiag_eq_rationalRealPhase]

/-! ## Code-linked generator packaging -/

/-- Common nonzero scalar from the qualitative projective-action theorem. -/
def projectiveScalar {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) : ℂ :=
  Classical.choose L.same_projective_sector_action

theorem projectiveScalar_ne_zero {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) :
    projectiveScalar L ≠ 0 :=
  (Classical.choose_spec L.same_projective_sector_action).1

theorem projectiveScalar_action {theta : Fin 6 → ℝ} {t : ℕ}
    {D : SectorDecomposition 6 t theta}
    (L : FiniteLift.RationalColoredLift D) (u : D.Index) :
    MainTheory.RealGate.realGate (fun j ↦ (L.physical j : ℝ)) (D.vec u) =
      fun x ↦ projectiveScalar L *
        MainTheory.RealGate.realGate theta (D.vec u) x :=
  (Classical.choose_spec L.same_projective_sector_action).2 u

/-- Eigenvalues of the rational lift on the reindexed logical frame. -/
def liftEigenvalue
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : FiniteLift.RationalColoredLift R.sectors) : Fin 2 → ℂ :=
  fun k ↦ projectiveScalar L *
    phaseExp (R.sectors.phase (R.link.reindex k).1)

theorem rationalRealGate_eigen
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : FiniteLift.RationalColoredLift R.sectors) (k : Fin 2) :
    MainTheory.RealGate.realGate (fun j ↦ (L.physical j : ℝ))
        ((FiniteLift.reindexedSectorFrame R.sectors R.link.reindex).vec k) =
      fun x ↦ liftEigenvalue R L k *
        (FiniteLift.reindexedSectorFrame R.sectors R.link.reindex).vec k x := by
  let u := R.link.reindex k
  calc
    MainTheory.RealGate.realGate (fun j ↦ (L.physical j : ℝ))
        ((FiniteLift.reindexedSectorFrame R.sectors R.link.reindex).vec k) =
        fun x ↦ projectiveScalar L *
          MainTheory.RealGate.realGate theta (R.sectors.vec u) x := by
      exact projectiveScalar_action L u
    _ = fun x ↦ projectiveScalar L *
          (phaseExp (R.sectors.phase u.1) * R.sectors.vec u x) := by
      funext x
      rw [congrFun (R.sectors.eigen u) x]
    _ = fun x ↦ liftEigenvalue R L k *
        (FiniteLift.reindexedSectorFrame R.sectors R.link.reindex).vec k x := by
      funext x
      simp only [liftEigenvalue, FiniteLift.reindexedSectorFrame, u]
      ring

/-- Projective nontriviality of the original real action forces the two lift
eigenvalues to remain distinct. -/
theorem liftEigenvalue_nontrivial
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : FiniteLift.RationalColoredLift R.sectors)
    (hnontrivial : SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    liftEigenvalue R L 0 ≠ liftEigenvalue R L 1 := by
  intro heq
  have hphase :
      phaseExp (R.sectors.phase (R.link.reindex 0).1) =
        phaseExp (R.sectors.phase (R.link.reindex 1).1) := by
    apply mul_left_cancel₀ (projectiveScalar_ne_zero L)
    exact heq
  let F := FiniteLift.reindexedSectorFrame R.sectors R.link.reindex
  let lambda := phaseExp (R.sectors.phase (R.link.reindex 0).1)
  have hlambda : lambda ≠ 0 := by
    exact Complex.exp_ne_zero _
  have hscalarF : CodeSpec.SameProjectiveOnCode F
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id := by
    apply (CodeSpec.sameProjectiveOnCode_iff_frame F _ _).2
    refine ⟨lambda, hlambda, ?_⟩
    intro k
    fin_cases k
    · simpa [F, lambda] using R.sectors.eigen (R.link.reindex 0)
    · simpa [F, lambda, hphase] using R.sectors.eigen (R.link.reindex 1)
  have hscalarC : CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id :=
    (MainTheory.GlobalClassificationBridge.sameProjectiveOnCode_congr_span
      C.frame F R.link.span_eq _ _).2 hscalarF
  exact hnontrivial hscalarC

/-- A qualitative rational lift is a genuine primitive finite generator on
the actual code. -/
def finiteGeneratorOfLift
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : FiniteLift.RationalColoredLift R.sectors)
    (hnontrivial : SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    @RankTwoGlobal.FiniteGeneratorResolution 6 3 C L.order
      ⟨L.order_pos.ne'⟩ := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  exact
    { zeta := D3NormalizedFiniteToReal.canonicalRoot L.order
      primitiveRoot := D3NormalizedFiniteToReal.canonicalRoot_primitive L.order
      angle := modularAngle L
      primitive := modularAngle_primitive L
      eigenFrame := FiniteLift.reindexedSectorFrame R.sectors R.link.reindex
      span_eq := R.link.span_eq
      eigenvalue := liftEigenvalue R L
      eigen := by
        intro k
        calc
          Gate.gate (D3NormalizedFiniteToReal.canonicalRoot L.order)
              (modularAngle L)
              ((FiniteLift.reindexedSectorFrame
                R.sectors R.link.reindex).vec k) =
              MainTheory.RealGate.realGate
                (fun j ↦ (L.physical j : ℝ))
                ((FiniteLift.reindexedSectorFrame
                  R.sectors R.link.reindex).vec k) :=
            congrFun (finiteGate_eq_rationalRealGate L)
              ((FiniteLift.reindexedSectorFrame
                R.sectors R.link.reindex).vec k)
          _ = fun x ↦ liftEigenvalue R L k *
              (FiniteLift.reindexedSectorFrame
                R.sectors R.link.reindex).vec k x :=
            rationalRealGate_eigen R L k
      projectively_nontrivial :=
        liftEigenvalue_nontrivial R L hnontrivial }

/-- The finite gate of `finiteGeneratorOfLift`, exposed without forcing a
caller to synthesize the denominator's dependent `NeZero` instance merely to
state a theorem. -/
def finiteGeneratorOfLiftEnd
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : FiniteLift.RationalColoredLift R.sectors)
    (hnontrivial : SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    Module.End ℂ (SS.State 6 ℂ) := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  exact RankTwoGlobal.finiteGateEnd
    (finiteGeneratorOfLift R L hnontrivial).zeta
    (finiteGeneratorOfLift R L hnontrivial).angle

/-- The packaged finite generator is tied to the original real operation: on
the actual code they differ by the single nonzero scalar supplied by the
qualitative rationalization theorem. -/
theorem finiteGeneratorOfLift_sameProjective
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : FiniteLift.RationalColoredLift R.sectors)
    (hnontrivial : SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    CodeSpec.SameProjectiveOnCode C.frame
      (finiteGeneratorOfLiftEnd R L hnontrivial)
      (PhaseSectorBridge.realGateEnd theta) := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  change CodeSpec.SameProjectiveOnCode C.frame
    (RankTwoGlobal.finiteGateEnd
      (finiteGeneratorOfLift R L hnontrivial).zeta
      (finiteGeneratorOfLift R L hnontrivial).angle)
    (PhaseSectorBridge.realGateEnd theta)
  let F := FiniteLift.reindexedSectorFrame R.sectors R.link.reindex
  have hframe : CodeSpec.SameProjectiveOnCode F
      (RankTwoGlobal.finiteGateEnd
        (finiteGeneratorOfLift R L hnontrivial).zeta
        (finiteGeneratorOfLift R L hnontrivial).angle)
      (PhaseSectorBridge.realGateEnd theta) := by
    apply (CodeSpec.sameProjectiveOnCode_iff_frame F _ _).2
    refine ⟨projectiveScalar L, projectiveScalar_ne_zero L, ?_⟩
    intro k
    calc
      RankTwoGlobal.finiteGateEnd
          (finiteGeneratorOfLift R L hnontrivial).zeta
          (finiteGeneratorOfLift R L hnontrivial).angle (F.vec k) =
          Gate.gate (D3NormalizedFiniteToReal.canonicalRoot L.order)
            (modularAngle L) (F.vec k) := rfl
      _ = MainTheory.RealGate.realGate
          (fun j ↦ (L.physical j : ℝ)) (F.vec k) :=
        congrFun (finiteGate_eq_rationalRealGate L) (F.vec k)
      _ = fun x ↦ projectiveScalar L *
          MainTheory.RealGate.realGate theta (F.vec k) x := by
        exact projectiveScalar_action L (R.link.reindex k)
      _ = projectiveScalar L •
          PhaseSectorBridge.realGateEnd theta (F.vec k) := rfl
  exact
    (MainTheory.GlobalClassificationBridge.sameProjectiveOnCode_congr_span
      C.frame F R.link.span_eq _ _).2 hframe

end

end MainTheory.D3RationalLiftFiniteGenerator
