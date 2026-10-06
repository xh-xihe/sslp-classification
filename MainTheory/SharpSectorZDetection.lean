import MainTheory.SharpSectorBound
import MainTheory.ZDetectionHypothesis

/-!
# The sharp colored lift bound from single-site Z detection

The number of colors below is the actual number of distinct eigenvalues of
the original diagonal operation on the code.  Only the corresponding
single-site Z detection equations are assumed; no lower bound on the
distance parameter of `ExactCode` is needed.

The final theorem also supplies an attained minimum primitive lift order.
Its minimality is stated directly over `HasPrimitiveLift`, so it does not
inherit the stronger distance hypothesis of `GeneralLiftOrder.qMin`.
-/

namespace MainTheory.SharpSectorZDetection

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.GeneralLiftOrder
open MainTheory.SectionTwoGeneral

variable {n K d : ℕ}

/-- A sharp bound indexed by the original operation's actual eigenvalue count,
under the paper's single-site Z detection hypothesis. -/
theorem hasPrimitiveLift_le_beta_sectorCount {B : ℕ}
    (C : CodeSpec.ExactCode n K d) (hZ : ZDetection.ZDetectsFrame C.frame)
    (v : diagonalSymmetryGroup (exactCodeProjector C)) (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id)
    (beta : BinaryBeta.BetaBound
      (n + GeneralSpectral.sectorCount hpres - 1) B) :
    ∃ q : ℕ,
      HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ∣ q ∧
      2 ≤ q ∧ q ≤ B := by
  set R := GeneralSpectral.logicalSectorResolution
    (F := C.frame) hpres C rfl
  have hcount : R.sectorCount = GeneralSpectral.sectorCount hpres := rfl
  have ht : 2 ≤ R.sectorCount := two_le_sectorCount_of_resolution hnt R
  have hbeta : BinaryBeta.BetaBound (n + R.sectorCount - 1) B := by
    rw [hcount]
    exact beta
  obtain ⟨L, hq, _, _, _, _, hle⟩ :=
    ColoredBound.quantitative_colored_finite_lift hbeta R.sectors
      (ZDetection.resolution_zDetects R hZ) ht
  have hlift := SharpSectorBound.hasPrimitiveLift_of_rationalLift' v hexp R L
  exact ⟨L.order, hlift, orderOf_dvd_of_hasPrimitiveLift hlift, hq, hle⟩

/-- The primitive lift of the chosen nonidentity projective class has
`2 ≤ m`, `m ∣ q` and `m ≤ q ≤ beta_(n+ell-1)`, where `ell` is its actual
logical eigenvalue count.  The binary denominator bound is supplied by the
finite maximum defining `betaOf`, not by an additional hypothesis. -/
theorem quantitative_colored_lift_of_zDetects
    (C : CodeSpec.ExactCode n K d) (hZ : ZDetection.ZDetectsFrame C.frame)
    (v : diagonalSymmetryGroup (exactCodeProjector C)) (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hg : intrinsicClass (exactCodeProjector C) v ≠ 1) :
    ∃ q : ℕ,
      HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ∣ q ∧
      2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ≤ q ∧
      2 ≤ q ∧ q ≤ BetaExists.betaOf
        (n + GeneralSpectral.sectorCount hpres - 1) := by
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg
  obtain ⟨q, hlift, hdvd, hq, hbound⟩ :=
    hasPrimitiveLift_le_beta_sectorCount C hZ v theta hexp hpres hnt
      (BetaExists.betaBound_betaOf _)
  have hm0 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 0 := by
    intro h
    rw [h] at hdvd
    have := Nat.eq_zero_of_zero_dvd hdvd
    omega
  have hm1 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 1 := by
    intro h
    exact hg (orderOf_eq_one_iff.mp h)
  exact ⟨q, hlift, hdvd, by omega, Nat.le_of_dvd (by omega) hdvd, hq, hbound⟩

/-- Primitive lifts have positive modulus, independently of any code-distance
hypothesis. -/
theorem positive_of_hasPrimitiveLift {C : CodeSpec.ExactCode n K d}
    {g : IntrinsicGroup C} {q : ℕ} (h : HasPrimitiveLift C g q) : 0 < q := by
  obtain ⟨hq, _⟩ := h
  exact Nat.pos_of_ne_zero hq.out

/-- An attained minimum of the primitive lift orders, once existence has been
proved.  No distance or detection hypothesis is part of this definition. -/
noncomputable def qMinOfExists (C : CodeSpec.ExactCode n K d)
    (g : IntrinsicGroup C) (h : ∃ q, HasPrimitiveLift C g q) : ℕ := by
  classical
  exact Nat.find h

theorem qMinOfExists_spec (C : CodeSpec.ExactCode n K d)
    (g : IntrinsicGroup C) (h : ∃ q, HasPrimitiveLift C g q) :
    HasPrimitiveLift C g (qMinOfExists C g h) := by
  classical
  exact Nat.find_spec h

theorem qMinOfExists_le (C : CodeSpec.ExactCode n K d)
    (g : IntrinsicGroup C) (h : ∃ q, HasPrimitiveLift C g q)
    {q : ℕ} (hq : HasPrimitiveLift C g q) : qMinOfExists C g h ≤ q := by
  classical
  exact Nat.find_min' h hq

/-- The hypothesis-free minimum agrees with the existing distance-two
minimum whenever that older interface applies. -/
theorem qMinOfExists_eq_qMin (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (h : ∃ q, HasPrimitiveLift C g q) :
    qMinOfExists C g h = GeneralLiftOrder.qMin C hd g := by
  apply Nat.le_antisymm
  · exact qMinOfExists_le C g h (GeneralLiftOrder.qMin_spec C hd g).2
  · exact GeneralLiftOrder.qMin_le C hd g
      (positive_of_hasPrimitiveLift (qMinOfExists_spec C g h))
      (qMinOfExists_spec C g h)

/-- The paper's `q_min` conclusion with an attained minimum and the sharp
actual-eigenvalue-count bound, assuming only single-site Z detection.
The same minimum is positive, divisible by the chosen logical order, and
no larger than any other primitive lift of that same class. -/
theorem exists_minimal_primitiveLift_le_betaOf_sectorCount
    (C : CodeSpec.ExactCode n K d) (hZ : ZDetection.ZDetectsFrame C.frame)
    (v : diagonalSymmetryGroup (exactCodeProjector C)) (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hg : intrinsicClass (exactCodeProjector C) v ≠ 1) :
    ∃ qmin : ℕ,
      HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) qmin ∧
      (∀ q, HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q →
        qmin ≤ q) ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ∣ qmin ∧
      2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ≤ qmin ∧
      2 ≤ qmin ∧ qmin ≤ BetaExists.betaOf
        (n + GeneralSpectral.sectorCount hpres - 1) := by
  obtain ⟨q, hlift, _, hm, _, _, hbound⟩ :=
    quantitative_colored_lift_of_zDetects C hZ v theta hexp hpres hg
  have hexists : ∃ q, HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q :=
    ⟨q, hlift⟩
  let qmin := qMinOfExists C (intrinsicClass (exactCodeProjector C) v) hexists
  have hmin : HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) qmin :=
    qMinOfExists_spec C _ hexists
  have hleast : ∀ q, HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q →
      qmin ≤ q := fun _ h => qMinOfExists_le C _ hexists h
  have hdvd := orderOf_dvd_of_hasPrimitiveLift hmin
  have hmle := Nat.le_of_dvd (positive_of_hasPrimitiveLift hmin) hdvd
  exact ⟨qmin, hmin, hleast, hdvd, hm, hmle, hm.trans hmle,
    (hleast q hlift).trans hbound⟩

end MainTheory.SharpSectorZDetection
