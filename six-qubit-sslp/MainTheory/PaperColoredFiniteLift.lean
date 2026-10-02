import MainTheory.BinaryPivotLift
import MainTheory.SharpSectorZDetection
import MainTheory.BetaAtPivotRank

/-! # The colored finite-lift theorem with one common construction

The binary matrix, its solved system, its Smith factor, and the physical
representative below all come from one pivot. The number of colors is the
actual spectral count of the supplied gate on the supplied code. Only
single-site Z detection is required, with no lower bound on code distance.
-/

namespace MainTheory.PaperColoredFiniteLift

open CodeSpec ClassificationLevels GlobalClassificationBridge GeneralLiftOrder
open FiniteLift PhaseSectorFull SharpClearing BinaryPivot BinaryPivotLift

noncomputable section

variable {n K d : ℕ}

/-- `thm:colored-finite-lift`, including the same binary-pivot/Smith witness
and the attained minimum primitive lift order. The lift's actual augmented
solution and intrinsic class are retained, so the arithmetic and physical
existential conclusions cannot refer to unrelated witnesses. -/
theorem colored_finite_lift_of_zDetects
    (C : ExactCode n K d) (hZ : ZDetection.ZDetectsFrame C.frame)
    (v : diagonalSymmetryGroup (exactCodeProjector C)) (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ)) =
      (((v : LocalPhase n) j : ℂ)))
    (hpres : CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hg : intrinsicClass (exactCodeProjector C) v ≠ 1) :
    2 ≤ GeneralSpectral.sectorCount hpres ∧
    GeneralSpectral.sectorCount hpres ≤ K ∧
    let R := GeneralSpectral.logicalSectorResolution (F := C.frame) hpres C rfl
    let hZR := ZDetection.resolution_zDetects R hZ
    ∃ (s : ℕ) (hs : NeZero s) (P : PivotData R.sectors (Fin s))
      (hdet : P.matrix.det ≠ 0) (W : SmithWitness (binMatrix P)),
      letI : NeZero s := hs
      let L := P.rationalLift hdet hZR
      s = (coloredMatrix R.sectors).rank ∧
      s ≤ n + GeneralSpectral.sectorCount hpres - 1 ∧
      BinaryBeta.IsZeroOne (binMatrix P) ∧ (binMatrix P).det ≠ 0 ∧
      (ratMatrix (binMatrix P)).mulVec (binarySolution P) = (fun i => (P.rhs i : ℚ)) ∧
      L.augmented = extendByZero P.column
        (fun i => (signColumn R.sectors (P.column i) : ℚ) * binarySolution P i) ∧
      Gate.Primitive L.order (D3RationalLiftFiniteGenerator.modularAngle L) ∧
      intrinsicClass (exactCodeProjector C) (liftSymmetry R L) =
        intrinsicClass (exactCodeProjector C) v ∧
      HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) L.order ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ∣ L.order ∧
      2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) ∧
      2 ≤ L.order ∧ L.order ∣ W.lastFactor ∧
      L.order ≤ BetaExists.betaOf (n + GeneralSpectral.sectorCount hpres - 1) ∧
      W.lastFactor ≤ BetaExists.betaOf (n + GeneralSpectral.sectorCount hpres - 1) ∧
      BetaExists.betaOf (n + GeneralSpectral.sectorCount hpres - 1) ≤
        BetaExists.betaOf (n + K - 1) ∧
      ∃ qmin : ℕ,
        HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) qmin ∧
        (∀ q, HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q → qmin ≤ q) ∧
        qmin ≤ L.order ∧
        qmin ≤ BetaExists.betaOf (n + GeneralSpectral.sectorCount hpres - 1) := by
  let R := GeneralSpectral.logicalSectorResolution (F := C.frame) hpres C rfl
  have hZR := ZDetection.resolution_zDetects R hZ
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg
  have ht : 2 ≤ R.sectorCount := SectionTwoGeneral.two_le_sectorCount_of_resolution hnt R
  have htK : R.sectorCount ≤ K := SectionTwoGeneral.sectorCount_le R.link
  have hcountle : GeneralSpectral.sectorCount hpres ≤ K := htK
  refine ⟨ht, htK, ?_⟩
  let s := (coloredMatrix R.sectors).rank
  have hs : 1 ≤ s := ColoredBound.rank_pos R.sectors hZR ht
  letI : NeZero s := ⟨by omega⟩
  let P := ColoredBound.canonicalPivot R.sectors
  have hdet : P.matrix.det ≠ 0 := ColoredBound.canonicalPivot_det R.sectors
  obtain ⟨W⟩ := PivotSmithNormalForm.nonempty_smithWitness_of_det (binMatrix P)
    (binMatrix_det_ne_zero P hdet)
  let L := P.rationalLift hdet hZR
  have hsize : s ≤ n + GeneralSpectral.sectorCount hpres - 1 := PivotSize.rank_le R.sectors
  have hlift := SharpSectorBound.hasPrimitiveLift_of_rationalLift' v hexp R L
  have hdvd := orderOf_dvd_of_hasPrimitiveLift hlift
  have hm : 2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) := by
    have h0 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 0 := by
      intro h
      rw [h] at hdvd
      exact L.order_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    have h1 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 1 := by
      intro h
      exact hg (orderOf_eq_one_iff.mp h)
    omega
  have hsmith : L.order ∣ W.lastFactor := rationalLift_order_dvd_smithLastFactor P hdet hZR W
  have hbound : W.lastFactor ≤ BetaExists.betaOf (n + GeneralSpectral.sectorCount hpres - 1) := by
    rw [← inverseDenominator_eq_smithLastFactor W]
    exact BetaExists.betaBound_betaOf _ s hs hsize (binMatrix P)
      (binMatrix_isZeroOne P) (binMatrix_det_ne_zero P hdet)
  have hqbound := (Nat.le_of_dvd W.lastFactor_pos hsmith).trans hbound
  have hexists : ∃ q, HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q :=
    ⟨L.order, hlift⟩
  let qmin := SharpSectorZDetection.qMinOfExists C (intrinsicClass (exactCodeProjector C) v) hexists
  have hmin := SharpSectorZDetection.qMinOfExists_spec C _ hexists
  have hleast : ∀ q, HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q → qmin ≤ q :=
    fun _ h => SharpSectorZDetection.qMinOfExists_le C _ hexists h
  exact ⟨s, inferInstance, P, hdet, W, rfl, hsize, binMatrix_isZeroOne P,
    binMatrix_det_ne_zero P hdet, binarySolution_solves P hdet,
    rationalLift_augmented_eq_binarySolution P hdet hZR,
    modularAngle_primitive_lift R L, intrinsicClass_liftSymmetry R L v hexp,
    hlift, hdvd, hm, L.two_le_order ht, hsmith, hqbound, hbound,
    BetaAtPivotRank.betaOf_mono (Nat.sub_le_sub_right (Nat.add_le_add_left hcountle n) 1),
    qmin, hmin, hleast, hleast L.order hlift, (hleast L.order hlift).trans hqbound⟩

end

end MainTheory.PaperColoredFiniteLift
