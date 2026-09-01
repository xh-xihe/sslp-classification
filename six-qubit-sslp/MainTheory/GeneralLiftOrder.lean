import MainTheory.SectionTwoGeneral
import MainTheory.IntrinsicClassBridge
import MainTheory.LocalPhaseAngle
import MainTheory.SymmetryToEntrance

/-!
# `eq:qualitative-m-divides-q` at general `K`

`thm:qualitative-finite-lift` is stated at arbitrary rank, and one of its
displayed conclusions is that the projective logical order `m` of a diagonal
operation divides the order `q` of its finite lift.  In this repository that
divisibility existed only at `K = 2`, as a field of
`RankTwoGlobal.TwoFiberCertificate`, because the packaging that produced it --
`FiniteGeneratorResolution` -- carries a two-element eigenframe.

None of the mathematics needs two.  The rational coloured lift, the identity
between its finite gate and its rational real gate, the finite-order symmetry
constructor and the class comparison are all rank-generic; only the packaging
was not.  This file assembles them directly:

* `liftSymmetry` is the lift's gate as an element of the diagonal symmetry
  group of the code, at arbitrary `K`;
* `intrinsicClass_liftSymmetry` says it lands in the class it should, so the
  divisibility below is about the original operation and not about an
  unrelated gate;
* `orderOf_intrinsicClass_dvd_liftOrder` is `eq:qualitative-m-divides-q`.

What still does not generalize past `K = 2` is finiteness of the whole group
(`thm:finite-projective-group`), which needs the paper's compact-Lie-group
argument.  Divisibility for a single element does not.
-/

namespace MainTheory.GeneralLiftOrder

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.PhaseSectorBridge
open MainTheory.PhaseSectorFull
open MainTheory.D3RationalLiftFiniteGenerator

noncomputable section

variable {n K d : ℕ} {theta : Fin n → ℝ}

/-- The rational lift acts on the code by the same projective operation as the
original real gate.  `projectiveScalar_action` says this on the sector vectors;
both sides are linear, so it extends over their span, which is the code. -/
theorem rationalGate_eq_smul_on_code {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors)
    (phi : SS.State n ℂ) (hphi : phi ∈ CodeSpec.codeSpan C.frame) :
    realGateEnd (fun j => (L.physical j : ℝ)) phi
      = projectiveScalar L • realGateEnd theta phi := by
  rw [R.link.span_eq] at hphi
  refine Submodule.span_induction
    (p := fun psi _ => realGateEnd (fun j => (L.physical j : ℝ)) psi
      = projectiveScalar L • realGateEnd theta psi) ?_ ?_ ?_ ?_ hphi
  · rintro _ ⟨k, rfl⟩
    have h := projectiveScalar_action L (R.link.reindex k)
    funext x
    exact congrFun h x
  · funext x
    simp [MainTheory.RealGate.realGate]
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy, smul_add]
  · intro a x _ hx
    rw [map_smul, map_smul, hx, smul_comm]

/-- The lift's finite gate preserves the code. -/
theorem finiteGate_codePreserving {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    CodeSpec.CodePreserving C.frame
      (realGateEnd (fun j => (L.physical j : ℝ))) := by
  intro phi hphi
  rw [rationalGate_eq_smul_on_code R L phi hphi]
  exact Submodule.smul_mem _ _ (R.codePreserving phi hphi)

/-- The lift's gate, transcribed as a local phase. -/
def liftLocalPhase {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    LocalPhase n :=
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  finiteLocalPhase (D3NormalizedFiniteToReal.canonicalRoot L.order)
    (D3NormalizedFiniteToReal.canonicalRoot_primitive L.order)
    (modularAngle L)

theorem diagonalAction_liftLocalPhase {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors)
    (phi : SS.State n ℂ) :
    diagonalAction (liftLocalPhase R L) phi
      = MainTheory.RealGate.realGate (fun j => (L.physical j : ℝ)) phi := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  rw [liftLocalPhase, diagonalAction_finiteLocalPhase]
  exact congrFun (finiteGate_eq_rationalRealGate L) phi

/-- **The lift's gate is a diagonal symmetry of the code**, at arbitrary
`K`. -/
def liftSymmetry {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    diagonalSymmetryGroup (exactCodeProjector C) := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  refine finiteOrderSymmetryOfCodePreserving C.frame (liftLocalPhase R L)
    L.order_pos ?_ ?_
  · exact finiteLocalPhase_pow_order _ _ _
  · intro phi hphi
    have hgate := finiteGate_codePreserving R L phi hphi
    rw [diagonalEnd_apply, diagonalAction_liftLocalPhase R L phi]
    exact hgate

theorem liftSymmetry_coe {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    (liftSymmetry R L : LocalPhase n) = liftLocalPhase R L := rfl

/-- The lift's gate has physical order dividing `L.order`. -/
theorem liftSymmetry_pow_order {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    liftSymmetry R L ^ L.order = 1 := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  refine Subtype.ext ?_
  simpa [liftSymmetry_coe, liftLocalPhase] using
    finiteLocalPhase_pow_order
      (D3NormalizedFiniteToReal.canonicalRoot L.order)
      (D3NormalizedFiniteToReal.canonicalRoot_primitive L.order)
      (modularAngle L)

/-- **The lift represents the operation it was built from.**

Without this the divisibility below would be about an unrelated gate. -/
theorem intrinsicClass_liftSymmetry {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors)
    (v : diagonalSymmetryGroup (exactCodeProjector C))
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ))) :
    intrinsicClass (exactCodeProjector C) (liftSymmetry R L)
      = intrinsicClass (exactCodeProjector C) v := by
  refine IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
    (exactCodeProjector C) _ _ (projectiveScalar L)
    (projectiveScalar_ne_zero L) (fun phi hphi => ?_)
  have hmem : phi ∈ CodeSpec.codeSpan C.frame :=
    (inProjectorRange_ofFrame_iff C.frame phi).1 hphi
  have hsmul := rationalGate_eq_smul_on_code R L phi hmem
  rw [liftSymmetry_coe R L, diagonalAction_liftLocalPhase R L phi]
  rw [SymmetryToEntrance.realGateEnd_eq_diagonalAction
    (v : LocalPhase n) theta hexp phi] at hsmul
  exact hsmul

/-- **`eq:qualitative-m-divides-q`, at arbitrary `K`.**

The projective logical order of a diagonal symmetry divides the order of the
finite lift produced by the rationalization. -/
theorem orderOf_intrinsicClass_dvd_liftOrder {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors)
    (v : diagonalSymmetryGroup (exactCodeProjector C))
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ))) :
    orderOf (intrinsicClass (exactCodeProjector C) v) ∣ L.order := by
  rw [← intrinsicClass_liftSymmetry R L v hexp]
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [intrinsicClass, ← QuotientGroup.mk_pow, liftSymmetry_pow_order R L]
  rfl

/-- The angle vector of the lift is primitive, so the gate below is a
`D(a;q)` in the paper's sense (`eq:primitive`), not merely some root-of-unity
diagonal. -/
theorem modularAngle_primitive_lift {C : CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    Gate.Primitive L.order (modularAngle L) :=
  modularAngle_primitive L

/-! ## `eq:qmin`: the set of primitive moduli, and its minimum -/

/-- **A projective class has a primitive finite lift of modulus `q`.**

This is the membership condition of the set whose minimum the paper calls
`q_min`.  The gate is required to be `D(a;q)` for a primitive `a`, exactly as
in `eq:Daq` and `eq:primitive`; without primitivity the set would be closed
under `(q, a) |-> (rq, ra)` and its minimum would say nothing. -/
def HasPrimitiveLift (C : CodeSpec.ExactCode n K d)
    (g : IntrinsicGroup C) (q : ℕ) : Prop :=
  ∃ (_ : NeZero q) (a : Fin n → ZMod q)
    (u : diagonalSymmetryGroup (exactCodeProjector C)),
    Gate.Primitive q a ∧
    (u : LocalPhase n) = finiteLocalPhase
      (D3NormalizedFiniteToReal.canonicalRoot q)
      (D3NormalizedFiniteToReal.canonicalRoot_primitive q) a ∧
    intrinsicClass (exactCodeProjector C) u = g

/-- **`eq:qualitative-m-divides-q` in its sharpest form**: the projective
logical order divides the modulus of *any* primitive finite lift, not only of
the one the rationalization happens to produce. -/
theorem orderOf_dvd_of_hasPrimitiveLift {C : CodeSpec.ExactCode n K d}
    {g : IntrinsicGroup C} {q : ℕ} (h : HasPrimitiveLift C g q) :
    orderOf g ∣ q := by
  obtain ⟨hq, a, u, _, hcoe, hclass⟩ := h
  letI : NeZero q := hq
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← hclass, intrinsicClass, ← QuotientGroup.mk_pow]
  have hone : u ^ q = 1 := by
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, hcoe]
    exact finiteLocalPhase_pow_order _ _ _
  rw [hone]
  rfl

/-- **Any rational coloured lift of the resolution is a primitive lift of the
class**, of modulus its own order.

Factored out of `exists_hasPrimitiveLift` so that a lift carrying a bound --
the pivot lift of `ColoredBound` -- can be fed in instead of an arbitrary
one. -/
theorem hasPrimitiveLift_of_rationalLift {C : CodeSpec.ExactCode n K d}
    (v : diagonalSymmetryGroup (exactCodeProjector C)) {theta : Fin n → ℝ}
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (L : MainTheory.FiniteLift.RationalColoredLift
      (resolutionOf C theta hpres).sectors) :
    HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) L.order := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  exact ⟨inferInstance, modularAngle L,
    liftSymmetry (resolutionOf C theta hpres) L,
    modularAngle_primitive_lift _ L, rfl,
    intrinsicClass_liftSymmetry _ L v hexp⟩

/-- **The set in `eq:qmin` is nonempty**, for every projective diagonal class
of an exact code of distance at least two.  This is what
`thm:qualitative-finite-lift` asserts, here at arbitrary rank. -/
theorem exists_hasPrimitiveLift (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) :
    ∃ q : ℕ, 0 < q ∧ HasPrimitiveLift C g q := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  obtain ⟨L⟩ := MainTheory.FiniteLift.exists_rationalColoredLift
    (resolutionOf C theta hpres).sectors
    ((resolutionOf C theta hpres).zDetects hd)
  exact ⟨L.order, L.order_pos, hasPrimitiveLift_of_rationalLift v hexp hpres L⟩

/-- **The headline, from the code alone**: every projective diagonal class of
an exact code of distance at least two has a primitive finite lift, and its
projective logical order divides that lift's modulus.  `thm:qualitative-finite-lift`
at arbitrary rank. -/
theorem exists_lift_order_dvd (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) :
    ∃ q : ℕ, 0 < q ∧ HasPrimitiveLift C g q ∧ orderOf g ∣ q := by
  obtain ⟨q, hq, h⟩ := exists_hasPrimitiveLift C hd g
  exact ⟨q, hq, h, orderOf_dvd_of_hasPrimitiveLift h⟩

/-- **Every projective diagonal class has finite order**, at arbitrary rank.

`cor:quantitative-projective-group` opens with this, and at `K > 2` it does not
follow from finiteness of the group -- which is not available there.  It
follows from having a finite lift at all. -/
theorem orderOf_pos (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) : 0 < orderOf g := by
  obtain ⟨q, hq, _, hdvd⟩ := exists_lift_order_dvd C hd g
  rcases Nat.eq_zero_or_pos (orderOf g) with h | h
  · rw [h] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hq.ne'
  · exact h

/-- The order is also bounded by any primitive lift's modulus. -/
theorem orderOf_le_of_hasPrimitiveLift {C : CodeSpec.ExactCode n K d}
    {g : IntrinsicGroup C} {q : ℕ} (hq : 0 < q)
    (h : HasPrimitiveLift C g q) : orderOf g ≤ q :=
  Nat.le_of_dvd hq (orderOf_dvd_of_hasPrimitiveLift h)

open Classical in
/-- **`q_min`**, the paper's minimal primitive modulus of a projective
class. -/
noncomputable def qMin (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) : ℕ :=
  Nat.find (p := fun q => 0 < q ∧ HasPrimitiveLift C g q)
    (exists_hasPrimitiveLift C hd g)

open Classical in
theorem qMin_spec (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) :
    0 < qMin C hd g ∧ HasPrimitiveLift C g (qMin C hd g) :=
  Nat.find_spec (p := fun q => 0 < q ∧ HasPrimitiveLift C g q)
    (exists_hasPrimitiveLift C hd g)

open Classical in
/-- `q_min` really is the minimum: no smaller modulus carries a primitive
lift. -/
theorem qMin_le (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) {q : ℕ} (hq : 0 < q)
    (h : HasPrimitiveLift C g q) :
    qMin C hd g ≤ q :=
  Nat.find_le (p := fun q => 0 < q ∧ HasPrimitiveLift C g q) ⟨hq, h⟩

/-- The projective logical order divides `q_min`. -/
theorem orderOf_dvd_qMin (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) :
    orderOf g ∣ qMin C hd g :=
  orderOf_dvd_of_hasPrimitiveLift (qMin_spec C hd g).2

end

end MainTheory.GeneralLiftOrder
