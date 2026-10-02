import QECC.SmithBounds
import MainTheory.BetaExactValue
import MainTheory.PivotSmithNormalForm

/-!
# The two encodings of the final Smith invariant agree

The manuscript defines `d_s(C)` as the last invariant factor of the Smith
normal form of a nonsingular binary matrix `C` (`eq:snf`), and `beta_nu` as its
maximum over sizes `1, ..., nu` (`eq:beta`). It then characterizes `d_s(C)` as
the exponent of the integer cokernel `Z^s / C Z^s`.

The two Lean libraries formalize the two characterizations:

* `QECC.NonsingularBinaryMatrix.finalSmithInvariant` is the cokernel exponent,
  and `QECC.smithBeta` is its maximum.
* `MainTheory.SharpClearing.SmithWitness` is an explicit Smith decomposition;
  every witness has last factor `inverseDenominator C`, and
  `MainTheory.BetaExists.betaOf` is built on that quantity.

This file proves they coincide, so QECC statements about `finalSmithInvariant`
and `smithBeta` are statements about the manuscript's `d_s(C)` and `beta_nu`.
-/

namespace MainTheory.QECCSmithBridge

open MainTheory.SharpClearing MainTheory.BinaryBeta

variable {s : ℕ}

theorem ratMatrix_det_isUnit (C : QECC.NonsingularBinaryMatrix s) :
    IsUnit (ratMatrix C.matrix).det :=
  isUnit_iff_ne_zero.mpr C.det_ratMatrix_ne_zero

/-- The cokernel exponent universally clears `C`, so the sharp inverse
denominator divides it. -/
theorem inverseDenominator_dvd_finalSmithInvariant (C : QECC.NonsingularBinaryMatrix s) :
    inverseDenominator C.matrix ∣ C.finalSmithInvariant := by
  apply inverseDenominator_dvd_of_universallyClears C.matrix _ C.finalSmithInvariant_pos
  intro h
  let z : Fin s → ℚ := (ratMatrix C.matrix)⁻¹.mulVec (fun j => (h j : ℚ))
  have hz : C.ratMatrix.mulVec z = fun i => (h i : ℚ) := by
    change (ratMatrix C.matrix).mulVec ((ratMatrix C.matrix)⁻¹.mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (ratMatrix_det_isUnit C),
      Matrix.one_mulVec]
  obtain ⟨k, hk⟩ := C.exists_integral_finalSmithInvariant_smul z h hz
  refine ⟨k, fun i => ?_⟩
  have hki := congrFun hk i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hki
  exact hki.symm

/-- The sharp inverse denominator annihilates the cokernel, so the cokernel
exponent divides it. -/
theorem finalSmithInvariant_dvd_inverseDenominator (C : QECC.NonsingularBinaryMatrix s) :
    C.finalSmithInvariant ∣ inverseDenominator C.matrix := by
  apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
  intro x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective C.imageLattice x
  rw [← Submodule.Quotient.mk_smul C.imageLattice, Submodule.Quotient.mk_eq_zero]
  obtain ⟨z, hz⟩ := inverseDenominator_universallyClears C.matrix h
  refine ⟨z, ?_⟩
  change C.matrix.mulVec z = inverseDenominator C.matrix • h
  funext i
  have hzq : (fun j => (z j : ℚ)) =
      (inverseDenominator C.matrix : ℚ) •
        (ratMatrix C.matrix)⁻¹.mulVec (fun j => (h j : ℚ)) := by
    funext j
    rw [← hz j]
    rfl
  have hq : ((C.matrix.mulVec z i : ℤ) : ℚ) =
      (((inverseDenominator C.matrix • h) i : ℤ) : ℚ) := by
    calc ((C.matrix.mulVec z i : ℤ) : ℚ)
        = (ratMatrix C.matrix).mulVec (fun j => (z j : ℚ)) i :=
          RingHom.map_mulVec (Int.castRingHom ℚ) C.matrix z i
      _ = (inverseDenominator C.matrix : ℚ) * (h i : ℚ) := by
          rw [hzq, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
            Matrix.mul_nonsing_inv _ (ratMatrix_det_isUnit C), Matrix.one_mulVec]
          rfl
      _ = (((inverseDenominator C.matrix • h) i : ℤ) : ℚ) := by
          simp
  exact_mod_cast hq

/-- **Bridge.** QECC's final Smith invariant, the exponent of the integer
cokernel, is the sharp inverse denominator of the same integer matrix. -/
theorem finalSmithInvariant_eq_inverseDenominator (C : QECC.NonsingularBinaryMatrix s) :
    C.finalSmithInvariant = inverseDenominator C.matrix :=
  Nat.dvd_antisymm (finalSmithInvariant_dvd_inverseDenominator C)
    (inverseDenominator_dvd_finalSmithInvariant C)

/-- Every nonsingular binary matrix has an explicit normalized Smith
decomposition. -/
theorem nonempty_smithWitness (C : QECC.NonsingularBinaryMatrix s) :
    Nonempty (SmithWitness C.matrix) :=
  MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det C.matrix C.det_ne_zero

/-- **Bridge to `eq:snf`.** QECC's final Smith invariant is the last diagonal
factor of every normalized Smith decomposition of the matrix. -/
theorem finalSmithInvariant_eq_lastFactor [Nonempty (Fin s)]
    (C : QECC.NonsingularBinaryMatrix s) (w : SmithWitness C.matrix) :
    C.finalSmithInvariant = w.lastFactor :=
  (finalSmithInvariant_eq_inverseDenominator C).trans (inverseDenominator_eq_smithLastFactor w)

/-- `QECC.smithBeta nu` is the exact binary constant `beta_nu` in the sense of
`MainTheory.BinaryBeta.BetaExact`: an upper bound for every nonsingular binary
matrix of size `1, ..., nu`, attained by one of them. -/
theorem smithBeta_betaExact {nu : ℕ} (hnu : 1 ≤ nu) : BetaExact nu (QECC.smithBeta nu) where
  upper := by
    intro t ht htnu M hM hdet
    let C : QECC.NonsingularBinaryMatrix t := ⟨M, hM, hdet⟩
    rw [show inverseDenominator M = C.finalSmithInvariant from
      (finalSmithInvariant_eq_inverseDenominator C).symm]
    exact QECC.finalSmithInvariant_le_smithBeta ht htnu C
  attained := by
    let D0 : QECC.boundedNonsingularBinaryMatrices nu :=
      ⟨⟨⟨1, by omega⟩, le_rfl⟩, QECC.binaryIdentityOne⟩
    obtain ⟨D, -, hD⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (QECC.boundedNonsingularBinaryMatrices nu)) ⟨D0, Finset.mem_univ _⟩
      (fun C => C.2.finalSmithInvariant)
    refine ⟨D.1.1.1, D.1.2, Nat.le_of_lt_succ D.1.1.2, D.2.matrix,
      D.2.entry_eq_zero_or_one, D.2.det_ne_zero, ?_⟩
    rw [← finalSmithInvariant_eq_inverseDenominator D.2]
    exact hD.symm

/-- **Bridge to `eq:beta`.** For `nu ≥ 1`, QECC's `smithBeta nu` equals
MainTheory's `betaOf nu`; both are the manuscript's `beta_nu`. -/
theorem smithBeta_eq_betaOf {nu : ℕ} (hnu : 1 ≤ nu) :
    QECC.smithBeta nu = MainTheory.BetaExists.betaOf nu :=
  (MainTheory.BetaExactValue.betaOf_eq_of_exact (smithBeta_betaExact hnu)).symm

end MainTheory.QECCSmithBridge
