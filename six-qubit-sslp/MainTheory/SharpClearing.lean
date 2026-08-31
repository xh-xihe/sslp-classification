import Mathlib
import MainTheory.Clearing
import MainTheory.Denominator

/-!
# The inverse-denominator invariant and Smith witnesses

For any integer matrix, `inverseDenominator C` is the least positive integer
which clears every entry of Mathlib's rational matrix inverse.  This definition
is useful on its own, but it is *not* named a Smith invariant: on singular
matrices Mathlib's inverse is zero, so such a name would be false.

The first part proves the universal property directly.  The second part defines
an explicit `SmithWitness`: integral two-sided inverses for the row and column
operations, positive diagonal factors in a divisibility chain, and the exact
identity `U * C * V = diag(d)`.  For a nonempty square matrix carrying such a
witness, we prove that its final factor is exactly `inverseDenominator C`.
Consequently the `q ∣ d_s(C)` assertion in Lemma 3.1 is a theorem about the
paper's Smith factor, rather than a definitional relabelling.
-/

namespace MainTheory.SharpClearing

open scoped BigOperators

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The entrywise cast of an integer matrix to the rationals. -/
def ratMatrix (C : Matrix s s ℤ) : Matrix s s ℚ :=
  C.map (Int.castRingHom ℚ)

/-- The entries of the rational inverse, packaged as one finite vector. -/
noncomputable def inverseEntries (C : Matrix s s ℤ) : s × s → ℚ :=
  fun p => (ratMatrix C)⁻¹ p.1 p.2

/-- The lcm of all denominators in Mathlib's rational inverse of `C`.

This is deliberately defined for every square matrix and deliberately is not
called a Smith invariant.  Its identification with the final Smith factor
requires the nonsingular, nonempty `SmithWitness` proved below. -/
noncomputable def inverseDenominator (C : Matrix s s ℤ) : ℕ :=
  Denominator.lcmDen (inverseEntries C)

theorem inverseDenominator_pos (C : Matrix s s ℤ) : 0 < inverseDenominator C :=
  Denominator.lcmDen_pos (inverseEntries C)

/-- Every inverse entry has denominator dividing `inverseDenominator C`. -/
theorem inverse_entry_den_dvd (C : Matrix s s ℤ) (i j : s) :
    ((ratMatrix C)⁻¹ i j).den ∣ inverseDenominator C := by
  exact Denominator.lcmDen_clears (inverseEntries C) (i, j)

/-- The integral numerator obtained after sharply clearing an inverse entry. -/
noncomputable def clearedInverseEntry (C : Matrix s s ℤ) (i j : s) : ℤ :=
  Denominator.liftNum (inverseEntries C) (i, j)

theorem clearedInverseEntry_spec (C : Matrix s s ℤ) (i j : s) :
    (inverseDenominator C : ℚ) * (ratMatrix C)⁻¹ i j =
      (clearedInverseEntry C i j : ℚ) := by
  exact Denominator.liftNum_spec (inverseEntries C) (i, j)

/-- The integral vector obtained after sharply clearing `C⁻¹ h`. -/
noncomputable def clearedInverseMulVec (C : Matrix s s ℤ) (h : s → ℤ) : s → ℤ :=
  fun i => ∑ j, clearedInverseEntry C i j * h j

/-- `inverseDenominator C` clears `C⁻¹ h` for every integral right-hand side. -/
theorem inverseDenominator_mul_inv_mulVec
    (C : Matrix s s ℤ) (h : s → ℤ) (i : s) :
    (inverseDenominator C : ℚ) *
        ((ratMatrix C)⁻¹.mulVec (fun j => (h j : ℚ))) i =
      (clearedInverseMulVec C h i : ℚ) := by
  simp only [Matrix.mulVec, dotProduct, clearedInverseMulVec]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, clearedInverseEntry_spec]

/-- A positive integer universally clears `C` when it clears `C⁻¹ h` for every
integral right-hand side `h`. -/
def UniversallyClears (C : Matrix s s ℤ) (q : ℕ) : Prop :=
  ∀ h : s → ℤ, ∃ z : s → ℤ, ∀ i,
    (q : ℚ) * ((ratMatrix C)⁻¹.mulVec (fun j => (h j : ℚ))) i = (z i : ℚ)

/-- The canonical multiplier has the universal clearing property. -/
theorem inverseDenominator_universallyClears (C : Matrix s s ℤ) :
    UniversallyClears C (inverseDenominator C) := by
  intro h
  exact ⟨clearedInverseMulVec C h, inverseDenominator_mul_inv_mulVec C h⟩

/--
**Sharpness.** Every positive universal clearing multiplier is a multiple of
`inverseDenominator C`.  Standard-basis right-hand sides recover each inverse
entry, so no smaller denominator can be hidden by taking linear combinations.
-/
theorem inverseDenominator_dvd_of_universallyClears
    (C : Matrix s s ℤ) (q : ℕ) (hq : 0 < q)
    (hclear : UniversallyClears C q) :
    inverseDenominator C ∣ q := by
  apply Denominator.lcmDen_dvd_of_clears (inverseEntries C) q
  intro p
  apply (Denominator.clears_iff q hq (inverseEntries C p)).2
  classical
  let e : s → ℤ := fun k => if k = p.2 then 1 else 0
  obtain ⟨z, hz⟩ := hclear e
  refine ⟨z p.1, ?_⟩
  simpa [inverseEntries, Matrix.mulVec, dotProduct, e] using hz p.1

/-- A positive `q` universally clears exactly when the sharp multiplier divides
it.  This packages existence and minimality into one usable statement. -/
theorem universallyClears_iff_dvd
    (C : Matrix s s ℤ) (q : ℕ) (hq : 0 < q) :
    UniversallyClears C q ↔ inverseDenominator C ∣ q := by
  constructor
  · exact inverseDenominator_dvd_of_universallyClears C q hq
  · rintro ⟨k, rfl⟩
    intro h
    refine ⟨fun i => (k : ℤ) * clearedInverseMulVec C h i, ?_⟩
    intro i
    rw [Nat.cast_mul]
    push_cast
    have hb := inverseDenominator_mul_inv_mulVec C h i
    linear_combination (k : ℚ) * hb

/-! ## From inverse vectors to arbitrary rational solutions -/

private theorem ratMatrix_det_ne_zero
    (C : Matrix s s ℤ) (hdet : C.det ≠ 0) :
    (ratMatrix C).det ≠ 0 := by
  have hm : (ratMatrix C).det = (C.det : ℚ) := by
    exact ((Int.castRingHom ℚ).map_det C).symm
  rw [hm]
  exact_mod_cast hdet

/-- A rational solution of a nonsingular integral system is its inverse-matrix
solution. -/
theorem solution_eq_inv_mulVec
    (C : Matrix s s ℤ) (h : s → ℤ) (x : s → ℚ)
    (hdet : C.det ≠ 0)
    (hx : (ratMatrix C).mulVec x = fun i => (h i : ℚ)) :
    x = (ratMatrix C)⁻¹.mulVec (fun i => (h i : ℚ)) := by
  have hu : IsUnit (ratMatrix C).det :=
    isUnit_iff_ne_zero.mpr (ratMatrix_det_ne_zero C hdet)
  have hstep := congrArg (fun v => (ratMatrix C)⁻¹.mulVec v) hx
  change (ratMatrix C)⁻¹.mulVec ((ratMatrix C).mulVec x) =
    (ratMatrix C)⁻¹.mulVec (fun i => (h i : ℚ)) at hstep
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec] at hstep
  exact hstep

/-- **Sharp clearing, solution form.** Every rational solution of `C x = h`
becomes integral after multiplication by `inverseDenominator C`. -/
theorem exists_sharply_cleared_solution
    (C : Matrix s s ℤ) (h : s → ℤ) (x : s → ℚ)
    (hdet : C.det ≠ 0)
    (hx : (ratMatrix C).mulVec x = fun i => (h i : ℚ)) :
    ∃ z : s → ℤ, ∀ i, (inverseDenominator C : ℚ) * x i = (z i : ℚ) := by
  refine ⟨clearedInverseMulVec C h, ?_⟩
  rw [solution_eq_inv_mulVec C h x hdet hx]
  exact inverseDenominator_mul_inv_mulVec C h

/-- The least common denominator of the coordinates of any solution divides
the inverse-entry denominator.  After the Smith identification below, this
becomes the divisibility `q ∣ d_s(C)` in Lemma 3.1. -/
theorem solution_lcmDen_dvd_inverseDenominator
    (C : Matrix s s ℤ) (h : s → ℤ) (x : s → ℚ)
    (hdet : C.det ≠ 0)
    (hx : (ratMatrix C).mulVec x = fun i => (h i : ℚ)) :
    Denominator.lcmDen x ∣ inverseDenominator C := by
  apply Denominator.lcmDen_dvd_of_clears x (inverseDenominator C)
  intro i
  apply (Denominator.clears_iff (inverseDenominator C) (inverseDenominator_pos C) (x i)).2
  obtain ⟨z, hz⟩ := exists_sharply_cleared_solution C h x hdet hx
  exact ⟨z i, hz i⟩

/-! ## Comparison with determinant clearing -/

/-- The determinant's absolute value universally clears a nonsingular integer
matrix.  This is the adjugate argument, now stated in the same interface as the
sharp multiplier. -/
theorem detNatAbs_universallyClears
    (C : Matrix s s ℤ) (hdet : C.det ≠ 0) :
    UniversallyClears C C.det.natAbs := by
  intro h
  let x : s → ℚ := (ratMatrix C)⁻¹.mulVec (fun i => (h i : ℚ))
  have hu : IsUnit (ratMatrix C).det :=
    isUnit_iff_ne_zero.mpr (ratMatrix_det_ne_zero C hdet)
  have hx : (ratMatrix C).mulVec x = fun i => (h i : ℚ) := by
    change (ratMatrix C).mulVec
      ((ratMatrix C)⁻¹.mulVec (fun i => (h i : ℚ))) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec]
  have hAdj (i : s) :
      (C.det : ℚ) * x i = (C.adjugate.mulVec h i : ℚ) :=
    Clearing.det_smul_eq_adjugate_mulVec C h x hx i
  refine ⟨fun i => if 0 ≤ C.det then C.adjugate.mulVec h i
      else -(C.adjugate.mulVec h i), ?_⟩
  intro i
  by_cases hd : 0 ≤ C.det
  · have hdQ : 0 ≤ (C.det : ℚ) := by exact_mod_cast hd
    simpa [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hdQ, hd] using hAdj i
  · have hdZ : C.det ≤ 0 := le_of_not_ge hd
    have hdQ : (C.det : ℚ) ≤ 0 := by exact_mod_cast hdZ
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonpos hdQ]
    simp only [hd, ↓reduceIte, Int.cast_neg]
    linear_combination -(hAdj i)

/-- The sharp multiplier always divides determinant clearing. -/
theorem inverseDenominator_dvd_detNatAbs
    (C : Matrix s s ℤ) (hdet : C.det ≠ 0) :
    inverseDenominator C ∣ C.det.natAbs := by
  apply inverseDenominator_dvd_of_universallyClears C C.det.natAbs
  · exact Int.natAbs_pos.mpr hdet
  · exact detNatAbs_universallyClears C hdet

/-! ## An explicit Smith witness

The following structure is intentionally stronger than merely exhibiting a
diagonal matrix equivalent to `C`.  `Uinv` and `Vinv` are integral two-sided
inverses, so unimodularity is kernel-checked without appealing to an external
determinant computation.  Positivity and the divisibility chain fix the usual
Smith normalization.
-/

section Smith

variable [LinearOrder s] [Nonempty s]

/-- Proof data that `C` has the displayed (normalized) Smith decomposition. -/
structure SmithWitness (C : Matrix s s ℤ) where
  factor : s → ℕ
  factor_pos : ∀ i, 0 < factor i
  factor_chain : ∀ ⦃i j : s⦄, i ≤ j → factor i ∣ factor j
  U : Matrix s s ℤ
  Uinv : Matrix s s ℤ
  V : Matrix s s ℤ
  Vinv : Matrix s s ℤ
  U_mul_Uinv : U * Uinv = 1
  Uinv_mul_U : Uinv * U = 1
  V_mul_Vinv : V * Vinv = 1
  Vinv_mul_V : Vinv * V = 1
  reduction : U * C * V = Matrix.diagonal (fun i ↦ (factor i : ℤ))

/-- Diagonal matrices with positive factors in a divisibility chain provide
concrete inhabitants of `SmithWitness`; the certificate interface is not
vacuous. -/
def diagonalSmithWitness (d : s → ℕ) (hd : ∀ i, 0 < d i)
    (hchain : ∀ ⦃i j : s⦄, i ≤ j → d i ∣ d j) :
    SmithWitness (Matrix.diagonal (fun i ↦ (d i : ℤ))) where
  factor := d
  factor_pos := hd
  factor_chain := hchain
  U := 1
  Uinv := 1
  V := 1
  Vinv := 1
  U_mul_Uinv := by simp
  Uinv_mul_U := by simp
  V_mul_Vinv := by simp
  Vinv_mul_V := by simp
  reduction := by simp

/-- The last index in the finite linear order used by a Smith witness. -/
noncomputable def lastIndex : s :=
  Finset.univ.max' Finset.univ_nonempty

/-- The final positive diagonal factor displayed by a Smith witness. -/
noncomputable def SmithWitness.lastFactor {C : Matrix s s ℤ}
    (w : SmithWitness C) : ℕ :=
  w.factor (lastIndex (s := s))

theorem SmithWitness.factor_dvd_lastFactor {C : Matrix s s ℤ}
    (w : SmithWitness C) (i : s) : w.factor i ∣ w.lastFactor := by
  apply w.factor_chain
  exact Finset.le_max' Finset.univ i (Finset.mem_univ i)

theorem SmithWitness.lastFactor_pos {C : Matrix s s ℤ}
    (w : SmithWitness C) : 0 < w.lastFactor :=
  w.factor_pos _

/-- The integral quotient `d_last / d_i`, stored through divisibility rather
than truncated natural-number division. -/
noncomputable def SmithWitness.quotient {C : Matrix s s ℤ}
    (w : SmithWitness C) (i : s) : ℕ :=
  (w.factor_dvd_lastFactor i).choose

theorem SmithWitness.factor_mul_quotient {C : Matrix s s ℤ}
    (w : SmithWitness C) (i : s) :
    w.factor i * w.quotient i = w.lastFactor :=
  (w.factor_dvd_lastFactor i).choose_spec.symm

/-- The rational diagonal matrix with entries `d_i`. -/
private noncomputable def smithDiagonalQ {C : Matrix s s ℤ}
    (w : SmithWitness C) : Matrix s s ℚ :=
  Matrix.diagonal (fun i ↦ (w.factor i : ℚ))

/-- The rational diagonal matrix with entries `1 / d_i`. -/
private noncomputable def smithDiagonalInvQ {C : Matrix s s ℤ}
    (w : SmithWitness C) : Matrix s s ℚ :=
  Matrix.diagonal (fun i ↦ (w.factor i : ℚ)⁻¹)

omit [Nonempty s] in
private theorem smithDiagonal_mul_inv {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    smithDiagonalQ w * smithDiagonalInvQ w = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [smithDiagonalQ, smithDiagonalInvQ,
      Nat.cast_ne_zero.mpr (w.factor_pos i).ne']
  · simp [smithDiagonalQ, smithDiagonalInvQ, hij]

omit [DecidableEq s] [LinearOrder s] [Nonempty s] in
private theorem ratMatrix_mul (A B : Matrix s s ℤ) :
    ratMatrix (A * B) = ratMatrix A * ratMatrix B := by
  exact Matrix.map_mul

omit [Fintype s] [LinearOrder s] [Nonempty s] in
private theorem ratMatrix_one :
    ratMatrix (1 : Matrix s s ℤ) = (1 : Matrix s s ℚ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ratMatrix]
  · simp [ratMatrix, hij]

omit [Nonempty s] in
private theorem SmithWitness.reductionQ {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    ratMatrix w.U * ratMatrix C * ratMatrix w.V = smithDiagonalQ w := by
  have h := congrArg ratMatrix w.reduction
  rw [ratMatrix_mul, ratMatrix_mul] at h
  rw [h]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ratMatrix, smithDiagonalQ]
  · simp [ratMatrix, smithDiagonalQ, hij]

omit [Nonempty s] in
private theorem SmithWitness.Uinv_mul_U_Q {C : Matrix s s ℤ}
    (w : SmithWitness C) : ratMatrix w.Uinv * ratMatrix w.U = 1 := by
  rw [← ratMatrix_mul, w.Uinv_mul_U, ratMatrix_one]

omit [Nonempty s] in
private theorem SmithWitness.U_mul_Uinv_Q {C : Matrix s s ℤ}
    (w : SmithWitness C) : ratMatrix w.U * ratMatrix w.Uinv = 1 := by
  rw [← ratMatrix_mul, w.U_mul_Uinv, ratMatrix_one]

omit [Nonempty s] in
private theorem SmithWitness.Vinv_mul_V_Q {C : Matrix s s ℤ}
    (w : SmithWitness C) : ratMatrix w.Vinv * ratMatrix w.V = 1 := by
  rw [← ratMatrix_mul, w.Vinv_mul_V, ratMatrix_one]

/-- The inverse matrix dictated by the Smith decomposition.  It is written as
an explicit single sum so denominator clearing is transparent. -/
private noncomputable def smithInverseCandidate {C : Matrix s s ℤ}
    (w : SmithWitness C) : Matrix s s ℚ :=
  fun i j ↦ ∑ k, (w.V i k : ℚ) * (w.factor k : ℚ)⁻¹ * (w.U k j : ℚ)

omit [Nonempty s] in
private theorem smithInverseCandidate_eq_mul {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    smithInverseCandidate w =
      ratMatrix w.V * smithDiagonalInvQ w * ratMatrix w.U := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [smithDiagonalInvQ, ratMatrix]

omit [Nonempty s] in
private theorem SmithWitness.C_mul_V_Q {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    ratMatrix C * ratMatrix w.V = ratMatrix w.Uinv * smithDiagonalQ w := by
  calc
    ratMatrix C * ratMatrix w.V =
        1 * (ratMatrix C * ratMatrix w.V) := by rw [one_mul]
    _ = (ratMatrix w.Uinv * ratMatrix w.U) *
        (ratMatrix C * ratMatrix w.V) := by rw [w.Uinv_mul_U_Q]
    _ = ratMatrix w.Uinv *
        (ratMatrix w.U * ratMatrix C * ratMatrix w.V) := by
          simp only [Matrix.mul_assoc]
    _ = ratMatrix w.Uinv * smithDiagonalQ w := by rw [w.reductionQ]

omit [Nonempty s] in
private theorem matrix_mul_smithInverseCandidate {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    ratMatrix C * smithInverseCandidate w = 1 := by
  rw [smithInverseCandidate_eq_mul]
  calc
    ratMatrix C *
        (ratMatrix w.V * smithDiagonalInvQ w * ratMatrix w.U) =
        (ratMatrix C * ratMatrix w.V) * smithDiagonalInvQ w *
          ratMatrix w.U := by simp only [Matrix.mul_assoc]
    _ = (ratMatrix w.Uinv * smithDiagonalQ w) *
        smithDiagonalInvQ w * ratMatrix w.U := by rw [w.C_mul_V_Q]
    _ = ratMatrix w.Uinv *
        (smithDiagonalQ w * smithDiagonalInvQ w) * ratMatrix w.U := by
          simp only [Matrix.mul_assoc]
    _ = ratMatrix w.Uinv * 1 * ratMatrix w.U := by
          rw [smithDiagonal_mul_inv]
    _ = 1 := by simpa using w.Uinv_mul_U_Q

omit [Nonempty s] in
/-- A Smith witness computes Mathlib's rational matrix inverse exactly. -/
theorem inverse_eq_smithInverseCandidate {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    (ratMatrix C)⁻¹ = smithInverseCandidate w := by
  exact Matrix.inv_eq_right_inv (matrix_mul_smithInverseCandidate w)

/-- Integral entry produced by clearing the Smith inverse with `d_last`. -/
noncomputable def SmithWitness.clearedEntry {C : Matrix s s ℤ}
    (w : SmithWitness C) (i j : s) : ℤ :=
  ∑ k, w.V i k * (w.quotient k : ℤ) * w.U k j

theorem SmithWitness.lastFactor_mul_inverse_entry {C : Matrix s s ℤ}
    (w : SmithWitness C) (i j : s) :
    (w.lastFactor : ℚ) * (ratMatrix C)⁻¹ i j =
      (w.clearedEntry i j : ℚ) := by
  rw [inverse_eq_smithInverseCandidate w]
  change (w.lastFactor : ℚ) *
      (∑ k, (w.V i k : ℚ) * (w.factor k : ℚ)⁻¹ * (w.U k j : ℚ)) =
    ((∑ k, w.V i k * (w.quotient k : ℤ) * w.U k j : ℤ) : ℚ)
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  have hk0 : (w.factor k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (w.factor_pos k).ne'
  have hfactor : (w.lastFactor : ℚ) =
      (w.factor k : ℚ) * (w.quotient k : ℚ) := by
    exact_mod_cast (w.factor_mul_quotient k).symm
  rw [hfactor]
  field_simp

/-- The final Smith factor clears every integral right-hand side. -/
theorem SmithWitness.lastFactor_universallyClears {C : Matrix s s ℤ}
    (w : SmithWitness C) : UniversallyClears C w.lastFactor := by
  intro h
  refine ⟨fun i ↦ ∑ j, w.clearedEntry i j * h j, ?_⟩
  intro i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, w.lastFactor_mul_inverse_entry]

/-- One divisibility direction follows from the universal minimality of the
inverse denominator. -/
theorem inverseDenominator_dvd_smithLastFactor {C : Matrix s s ℤ}
    (w : SmithWitness C) : inverseDenominator C ∣ w.lastFactor := by
  exact inverseDenominator_dvd_of_universallyClears C w.lastFactor
    w.lastFactor_pos w.lastFactor_universallyClears

omit [Nonempty s] in
private theorem inverse_mul_Uinv_Q {C : Matrix s s ℤ}
    (w : SmithWitness C) :
    (ratMatrix C)⁻¹ * ratMatrix w.Uinv =
      ratMatrix w.V * smithDiagonalInvQ w := by
  rw [inverse_eq_smithInverseCandidate w, smithInverseCandidate_eq_mul]
  calc
    (ratMatrix w.V * smithDiagonalInvQ w * ratMatrix w.U) *
        ratMatrix w.Uinv =
        ratMatrix w.V * smithDiagonalInvQ w *
          (ratMatrix w.U * ratMatrix w.Uinv) := by
            simp only [Matrix.mul_assoc]
    _ = ratMatrix w.V * smithDiagonalInvQ w * 1 := by rw [w.U_mul_Uinv_Q]
    _ = ratMatrix w.V * smithDiagonalInvQ w := by rw [Matrix.mul_one]

/-- Conversely, universal clearing forces a multiple of the final Smith
factor.  The proof probes the final Smith coordinate and uses the integral
inverse of `V`; no uniqueness theorem for Smith forms is assumed. -/
theorem SmithWitness.lastFactor_dvd_of_universallyClears
    {C : Matrix s s ℤ} (w : SmithWitness C) (q : ℕ) (hq : 0 < q)
    (hclear : UniversallyClears C q) : w.lastFactor ∣ q := by
  let ell : s := lastIndex (s := s)
  let h : s → ℤ := fun j ↦ w.Uinv j ell
  obtain ⟨z, hz⟩ := hclear h
  have hcoordinate (i : s) :
      ((ratMatrix C)⁻¹.mulVec (fun j ↦ (h j : ℚ))) i =
        (w.V i ell : ℚ) * (w.lastFactor : ℚ)⁻¹ := by
    calc
      ((ratMatrix C)⁻¹.mulVec (fun j ↦ (h j : ℚ))) i =
          ((ratMatrix C)⁻¹ * ratMatrix w.Uinv) i ell := by
            simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, h, ratMatrix]
      _ = (ratMatrix w.V * smithDiagonalInvQ w) i ell := by
            rw [inverse_mul_Uinv_Q w]
      _ = (w.V i ell : ℚ) * (w.lastFactor : ℚ)⁻¹ := by
            simp [smithDiagonalInvQ, ratMatrix, SmithWitness.lastFactor, ell]
  have hqz (i : s) :
      (q : ℚ) * ((w.V i ell : ℚ) * (w.lastFactor : ℚ)⁻¹) =
        (z i : ℚ) := by
    rw [← hcoordinate]
    exact hz i
  let a : ℤ := ∑ i, w.Vinv ell i * z i
  have hVV : ∑ i, (w.Vinv ell i : ℚ) * (w.V i ell : ℚ) = 1 := by
    have hentry := congrArg (fun M : Matrix s s ℚ ↦ M ell ell) w.Vinv_mul_V_Q
    simpa [Matrix.mul_apply, ratMatrix] using hentry
  have hqa : (q : ℚ) * (w.lastFactor : ℚ)⁻¹ = (a : ℚ) := by
    calc
      (q : ℚ) * (w.lastFactor : ℚ)⁻¹ =
          ((q : ℚ) * (w.lastFactor : ℚ)⁻¹) * 1 := by ring
      _ = ((q : ℚ) * (w.lastFactor : ℚ)⁻¹) *
          (∑ i, (w.Vinv ell i : ℚ) * (w.V i ell : ℚ)) := by rw [hVV]
      _ = ∑ i, (w.Vinv ell i : ℚ) *
          ((q : ℚ) * ((w.V i ell : ℚ) *
            (w.lastFactor : ℚ)⁻¹)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ i, (w.Vinv ell i : ℚ) * (z i : ℚ) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hqz]
      _ = (a : ℚ) := by
              simp [a]
  have hden : ((w.lastFactor : ℚ)⁻¹).den ∣ q :=
    (Denominator.clears_iff q hq ((w.lastFactor : ℚ)⁻¹)).2 ⟨a, hqa⟩
  simpa [Rat.inv_natCast_den_of_pos w.lastFactor_pos] using hden

/-- The inverse-entry denominator is exactly the final factor of every
explicit normalized Smith witness. -/
theorem inverseDenominator_eq_smithLastFactor {C : Matrix s s ℤ}
    (w : SmithWitness C) : inverseDenominator C = w.lastFactor := by
  apply Nat.dvd_antisymm
  · exact inverseDenominator_dvd_smithLastFactor w
  · exact w.lastFactor_dvd_of_universallyClears (inverseDenominator C)
      (inverseDenominator_pos C) (inverseDenominator_universallyClears C)

omit [Nonempty s] in
/-- A Smith witness is necessarily nonsingular; hence no singular or
zero-dimensional fake witness can enter the sharp solution theorem. -/
theorem SmithWitness.det_ne_zero {C : Matrix s s ℤ}
    (w : SmithWitness C) : C.det ≠ 0 := by
  intro hdet
  have hprod := congrArg Matrix.det (matrix_mul_smithInverseCandidate w)
  have hcast : (ratMatrix C).det = (C.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det C).symm
  rw [Matrix.det_mul, Matrix.det_one, hcast, hdet] at hprod
  norm_num at hprod

/-- **Lemma 3.1, Smith form.**  The least common denominator `q` of every
rational solution of `C x = h` divides the final Smith factor. -/
theorem solution_lcmDen_dvd_smithLastFactor
    {C : Matrix s s ℤ} (w : SmithWitness C) (h : s → ℤ) (x : s → ℚ)
    (hx : (ratMatrix C).mulVec x = fun i ↦ (h i : ℚ)) :
    Denominator.lcmDen x ∣ w.lastFactor := by
  rw [← inverseDenominator_eq_smithLastFactor w]
  exact solution_lcmDen_dvd_inverseDenominator C h x w.det_ne_zero hx

end Smith

end MainTheory.SharpClearing
