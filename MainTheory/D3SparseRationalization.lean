import MainTheory.D3Bound
import MainTheory.FiniteLift
import MainTheory.BinaryBeta
import MainTheory.Gate

/-!
# Sparse binary-pivot rationalization at distance three

This module formalizes the algebraic middle of the distance-three argument in
`main.tex`.  It deliberately does not choose the supported simplex.  Given
linearly independent Boolean support rows and an integral right-hand side,
`Data.ofBitRows` does construct a nonsingular physical-coordinate minor;
everything after that is constructed as well:

* solve the integral square pivot over `ℚ`;
* extend the solution by zero outside the selected physical coordinates;
* prove that the zero-extended solution has the supplied integral
  right-hand side on every selected row;
* prove agreement with any original real solution on the entire row span;
* prove that the least denominator of the sparse physical phase divides the
  sharp inverse denominator of the displayed binary minor.

The generic `Data` below does not itself assert that its rows are binary or
supported; `bitRows`, the coordinate-minor theorem, and `Data.ofBitRows` at the
end provide the binary construction.  The remaining semantic obligation is
to select linearly independent rows from the actual support, prove that they
span the relevant support geometry, and derive their integral right-hand sides
from the phase equations.  No denominator divisibility or phase agreement is
accepted as a field.
-/

namespace MainTheory.D3SparseRationalization

open MainTheory
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- A rectangular integral row system together with a nonsingular square
coordinate minor and an integral right-hand side. -/
structure Data (n r : ℕ) where
  row : Matrix (Fin r) (Fin n) ℤ
  coordinate : Fin r ↪ Fin n
  rhs : Fin r → ℤ
  nonsingular :
    (show Matrix (Fin r) (Fin r) ℤ from
      fun i j ↦ row i (coordinate j)).det ≠ 0

/-- The selected square coordinate minor. -/
def Data.minor {r : ℕ} (P : Data n r) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j ↦ P.row i (P.coordinate j)

theorem Data.minor_nonsingular {r : ℕ} (P : Data n r) :
    P.minor.det ≠ 0 :=
  P.nonsingular

/-- The exact rational solution on the selected coordinates. -/
def Data.selectedSolution {r : ℕ} (P : Data n r) : Fin r → ℚ :=
  (SharpClearing.ratMatrix P.minor)⁻¹.mulVec (fun i ↦ (P.rhs i : ℚ))

/-- Extend the selected solution by zero on the other physical coordinates. -/
def Data.fullSolution {r : ℕ} (P : Data n r) : Fin n → ℚ :=
  FiniteLift.extendByZero P.coordinate P.selectedSolution

theorem Data.minor_cast {r : ℕ} (P : Data n r) (i j : Fin r) :
    SharpClearing.ratMatrix P.minor i j = (P.row i (P.coordinate j) : ℚ) :=
  rfl

/-- Nonsingularity makes the inverse-matrix expression a genuine solution. -/
theorem Data.selectedSolution_solves {r : ℕ} (P : Data n r) :
    (SharpClearing.ratMatrix P.minor).mulVec P.selectedSolution =
      fun i ↦ (P.rhs i : ℚ) := by
  have hdetQ : (SharpClearing.ratMatrix P.minor).det ≠ 0 := by
    have hm : (SharpClearing.ratMatrix P.minor).det =
        (P.minor.det : ℚ) :=
      ((Int.castRingHom ℚ).map_det P.minor).symm
    rw [hm]
    exact_mod_cast P.minor_nonsingular
  have hu : IsUnit (SharpClearing.ratMatrix P.minor).det :=
    isUnit_iff_ne_zero.mpr hdetQ
  change (SharpClearing.ratMatrix P.minor).mulVec
    ((SharpClearing.ratMatrix P.minor)⁻¹.mulVec
      (fun i ↦ (P.rhs i : ℚ))) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]

/-- Every original rectangular row is solved by the zero-extended vector. -/
theorem Data.fullSolution_solves {r : ℕ} (P : Data n r) :
    (P.row.map (Int.castRingHom ℚ)).mulVec P.fullSolution =
      fun i ↦ (P.rhs i : ℚ) := by
  funext i
  change dotProduct (fun j ↦ (P.row i j : ℚ)) P.fullSolution =
    (P.rhs i : ℚ)
  rw [Data.fullSolution,
    FiniteLift.dotProduct_extendByZero P.coordinate]
  have hi := congrFun P.selectedSolution_solves i
  simpa [Matrix.mulVec, dotProduct, P.minor_cast] using hi

/-- Zero extension introduces no new coordinate denominator. -/
theorem Data.lcmDen_full_dvd_selected {r : ℕ} (P : Data n r) :
    Denominator.lcmDen P.fullSolution ∣
      Denominator.lcmDen P.selectedSolution := by
  apply Denominator.lcmDen_dvd_of_clears
  intro j
  by_cases hj : ∃ i, P.coordinate i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [Data.fullSolution, FiniteLift.extendByZero_apply_column]
    exact Denominator.lcmDen_clears P.selectedSolution i
  · have hzero : P.fullSolution j = 0 := by
      rw [Data.fullSolution]
      apply Finset.sum_eq_zero
      intro i _
      have hne : P.coordinate i ≠ j := by
        intro hi
        exact hj ⟨i, hi⟩
      simp [hne]
    rw [hzero]
    simp

/-- The sparse physical phase has denominator dividing the sharp inverse
denominator of the selected binary minor. -/
theorem Data.lcmDen_full_dvd_inverseDenominator {r : ℕ} (P : Data n r) :
    Denominator.lcmDen P.fullSolution ∣
      SharpClearing.inverseDenominator P.minor := by
  exact dvd_trans P.lcmDen_full_dvd_selected
    (SharpClearing.solution_lcmDen_dvd_inverseDenominator
      P.minor P.rhs P.selectedSolution P.minor_nonsingular
      P.selectedSolution_solves)

/-! ## Canonical primitive modular angle of the sparse solution -/

/-- The exact physical order attached to the sparse rational phase is its
least positive common denominator. -/
def Data.order {r : ℕ} (P : Data n r) : ℕ :=
  Denominator.lcmDen P.fullSolution

/-- Integral coordinate numerators at the least common denominator. -/
noncomputable def Data.numerator {r : ℕ} (P : Data n r) : Fin n → ℤ :=
  Denominator.liftNum P.fullSolution

/-- Reduce the integral numerators modulo the exact physical order. -/
noncomputable def Data.angle {r : ℕ} (P : Data n r) :
    Fin n → ZMod P.order :=
  fun j ↦ (P.numerator j : ZMod P.order)

theorem Data.order_pos {r : ℕ} (P : Data n r) : 0 < P.order :=
  Denominator.lcmDen_pos P.fullSolution

/-- The numerator is an exact integer representative of `q * theta_j`.
This is the congruence-level transcription used in `main.tex`; no choice of a
literal representative in `[0,q)` is required. -/
theorem Data.numerator_spec {r : ℕ} (P : Data n r) (j : Fin n) :
    (P.order : ℚ) * P.fullSolution j = (P.numerator j : ℚ) :=
  Denominator.liftNum_spec P.fullSolution j

/-- Every sparse coordinate has an integral representative whose residue is
the canonical modular angle. -/
theorem Data.exists_angle_representative {r : ℕ} (P : Data n r) (j : Fin n) :
    ∃ z : ℤ,
      (P.order : ℚ) * P.fullSolution j = (z : ℚ) ∧
      (z : ZMod P.order) = P.angle j :=
  ⟨P.numerator j, P.numerator_spec j, rfl⟩

/-- Minimality of the common denominator makes the modular angle primitive.
The proof transports divisibility from the canonical residue back to its
integer representative modulo `order`, using that the tested divisor already
divides `order`. -/
theorem Data.angle_primitive {r : ℕ} (P : Data n r) :
    Gate.Primitive P.order P.angle := by
  letI : NeZero P.order := ⟨Nat.ne_of_gt P.order_pos⟩
  intro d hdq hda
  apply Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum
    P.fullSolution d hdq
  intro j
  change (d : ℤ) ∣ P.numerator j
  have hdqZ : (d : ℤ) ∣ (P.order : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdq
  have hvalZ : (d : ℤ) ∣ ((P.angle j).val : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hda j)
  have hcast : (P.numerator j : ZMod P.order) =
      (((P.angle j).val : ℤ) : ZMod P.order) := by
    simp [Data.angle]
  have hqsub : (P.order : ℤ) ∣
      ((P.angle j).val : ℤ) - P.numerator j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (P.numerator j) ((P.angle j).val : ℤ) P.order).1 hcast
  have hnumZ := Int.dvd_sub hvalZ (hdqZ.trans hqsub)
  simpa using hnumZ

/-- The exact order of the internally constructed primitive modular angle
divides the sharp inverse denominator of the selected binary minor. -/
theorem Data.order_dvd_inverseDenominator {r : ℕ} (P : Data n r) :
    P.order ∣ SharpClearing.inverseDenominator P.minor := by
  simpa [Data.order] using P.lcmDen_full_dvd_inverseDenominator

/-! ## Agreement with the original real phase on the support span -/

/-- Cast the sparse rational phase to a real physical phase. -/
def Data.fullSolutionReal {r : ℕ} (P : Data n r) : Fin n → ℝ :=
  fun j ↦ (P.fullSolution j : ℝ)

/-- The cast sparse phase solves the same real row system. -/
theorem Data.fullSolutionReal_solves {r : ℕ} (P : Data n r) :
    (P.row.map (Int.castRingHom ℝ)).mulVec P.fullSolutionReal =
      fun i ↦ (P.rhs i : ℝ) := by
  funext i
  have hi := congrArg (algebraMap ℚ ℝ)
    (congrFun P.fullSolution_solves i)
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply,
    Data.fullSolutionReal, map_sum, map_mul] using hi

/-- If `theta` is the original real solution of the same supported vertex
equations, then it and the sparse rational phase give equal row values. -/
theorem Data.row_values_agree {r : ℕ} (P : Data n r)
    (theta : Fin n → ℝ)
    (hTheta : (P.row.map (Int.castRingHom ℝ)).mulVec theta =
      fun i ↦ (P.rhs i : ℝ)) :
    (P.row.map (Int.castRingHom ℝ)).mulVec P.fullSolutionReal =
      (P.row.map (Int.castRingHom ℝ)).mulVec theta := by
  rw [P.fullSolutionReal_solves, hTheta]

/-- Agreement on the selected supported rows propagates to every vector in
their real row span.  This is `eq:phase-agreement-on-support` once the common
affine-span theorem supplies the displayed coefficient vector `w`. -/
theorem Data.dot_eq_on_rowSpan {r : ℕ} (P : Data n r)
    (theta : Fin n → ℝ)
    (hTheta : (P.row.map (Int.castRingHom ℝ)).mulVec theta =
      fun i ↦ (P.rhs i : ℝ))
    (x : Fin n → ℝ) (w : Fin r → ℝ)
    (hx : x = fun j ↦ ∑ i, w i * (P.row i j : ℝ)) :
    (∑ j, P.fullSolutionReal j * x j) =
      ∑ j, theta j * x j := by
  exact D3Bound.dot_eq_of_mulVec_eq
    (P.row.map (Int.castRingHom ℝ)) P.fullSolutionReal theta
    (P.row_values_agree theta hTheta) x w (by simpa using hx)

/-! ## Binary rows obtained from actual cube vertices -/

/-!
The coordinate-minor choice is linear algebra, not an additional certificate:
the columns of a matrix with independent rows span a space of full row rank.
Choose a basis from those actual columns.  Independence of that basis forces
the chosen column indices to be distinct and the resulting square minor to be
nonsingular.
-/

/-- Any linearly independent family of six-coordinate real rows admits a
nonsingular square minor obtained by selecting actual physical coordinates.
The coordinate injection is constructed, rather than accepted as data. -/
theorem exists_nonsingular_coordinate_minor {r : ℕ}
    (v : Fin r → Fin n → ℝ) (hv : LinearIndependent ℝ v) :
    ∃ coordinate : Fin r ↪ Fin n,
      (show Matrix (Fin r) (Fin r) ℝ from
        fun i j ↦ v i (coordinate j)).det ≠ 0 := by
  classical
  let A : Matrix (Fin r) (Fin n) ℝ := fun i j ↦ v i j
  have hrow : LinearIndependent ℝ A.row := by
    simpa [A, Matrix.row] using hv
  have hdim : Module.finrank ℝ
      (Submodule.span ℝ (Set.range A.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    simpa using hrow.rank_matrix
  obtain ⟨f, hf_mem, _, hf_independent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.col)
  let e : Fin r ≃ Fin (Module.finrank ℝ
      (Submodule.span ℝ (Set.range A.col))) :=
    finCongr hdim.symm
  choose coordinate hcoordinate using fun i : Fin r ↦ hf_mem (e i)
  have hcoordinate_injective : Function.Injective coordinate := by
    intro i j hij
    apply e.injective
    apply hf_independent.injective
    rw [← hcoordinate i, ← hcoordinate j, hij]
  let coordinateEmbedding : Fin r ↪ Fin n :=
    ⟨coordinate, hcoordinate_injective⟩
  let M : Matrix (Fin r) (Fin r) ℝ :=
    fun i j ↦ v i (coordinateEmbedding j)
  have hcols : LinearIndependent ℝ M.col := by
    have hselected : LinearIndependent ℝ (fun j : Fin r ↦ f (e j)) :=
      hf_independent.comp e e.injective
    have hcol_eq : M.col = fun j : Fin r ↦ f (e j) := by
      funext j i
      simpa [M, A, coordinateEmbedding, Matrix.col] using
        congrFun (hcoordinate j) i
    rw [hcol_eq]
    exact hselected
  refine ⟨coordinateEmbedding, ?_⟩
  have hunit : IsUnit M :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (M.isUnit_iff_isUnit_det.mp hunit).ne_zero

/-- Integral zero--one row matrix of displayed Boolean-cube vertices. -/
def bitRows {r : ℕ} (vertex : Fin r → SS.BitString n) :
    Matrix (Fin r) (Fin n) ℤ :=
  fun i j ↦ if vertex i j then 1 else 0

theorem bitRows_isZeroOne {r : ℕ} (vertex : Fin r → SS.BitString n) :
    BinaryBeta.IsZeroOne (bitRows vertex) := by
  intro i j
  unfold bitRows
  split <;> simp

/-- For actual Boolean-cube rows, real linear independence constructs an
integer nonsingular coordinate minor.  Nonvanishing is transported through
the injective cast `ℤ → ℝ`; it is not assumed independently over `ℤ`. -/
theorem exists_nonsingular_bit_coordinate_minor {r : ℕ}
    (vertex : Fin r → SS.BitString n)
    (hv : LinearIndependent ℝ
      (fun i j ↦ if vertex i j then (1 : ℝ) else (0 : ℝ))) :
    ∃ coordinate : Fin r ↪ Fin n,
      (show Matrix (Fin r) (Fin r) ℤ from
        fun i j ↦ bitRows vertex i (coordinate j)).det ≠ 0 := by
  obtain ⟨coordinate, hreal⟩ :=
    exists_nonsingular_coordinate_minor
      (fun i j ↦ if vertex i j then (1 : ℝ) else (0 : ℝ)) hv
  refine ⟨coordinate, ?_⟩
  intro hinteger
  apply hreal
  let C : Matrix (Fin r) (Fin r) ℤ :=
    fun i j ↦ bitRows vertex i (coordinate j)
  have hC : C.det = 0 := by
    simpa [C] using hinteger
  calc
    (show Matrix (Fin r) (Fin r) ℝ from
      fun i j ↦ if vertex i (coordinate j) then (1 : ℝ) else (0 : ℝ)).det =
        (C.map (Int.castRingHom ℝ)).det := by
      congr 1
      funext i j
      simp [C, bitRows]
    _ = (C.det : ℝ) := ((Int.castRingHom ℝ).map_det C).symm
    _ = 0 := by rw [hC]; simp

/-- Package linearly independent actual Boolean rows and an integral
right-hand side as sparse rationalization data.  The physical coordinate
injection and nonsingular integer minor are chosen by the theorem above, so
neither is an additional premise. -/
noncomputable def Data.ofBitRows {r : ℕ}
    (vertex : Fin r → SS.BitString n) (rhs : Fin r → ℤ)
    (hv : LinearIndependent ℝ
      (fun i j ↦ if vertex i j then (1 : ℝ) else (0 : ℝ))) : Data n r := by
  let hminor := exists_nonsingular_bit_coordinate_minor vertex hv
  exact
    { row := bitRows vertex
      coordinate := Classical.choose hminor
      rhs := rhs
      nonsingular := Classical.choose_spec hminor }

@[simp] theorem Data.ofBitRows_row {r : ℕ}
    (vertex : Fin r → SS.BitString n) (rhs : Fin r → ℤ)
    (hv : LinearIndependent ℝ
      (fun i j ↦ if vertex i j then (1 : ℝ) else (0 : ℝ))) :
    (Data.ofBitRows vertex rhs hv).row = bitRows vertex :=
  rfl

@[simp] theorem Data.ofBitRows_rhs {r : ℕ}
    (vertex : Fin r → SS.BitString n) (rhs : Fin r → ℤ)
    (hv : LinearIndependent ℝ
      (fun i j ↦ if vertex i j then (1 : ℝ) else (0 : ℝ))) :
    (Data.ofBitRows vertex rhs hv).rhs = rhs :=
  rfl

@[simp] theorem bitRows_cast_real {r : ℕ}
    (vertex : Fin r → SS.BitString n) (i : Fin r) (j : Fin n) :
    ((bitRows vertex i j : ℤ) : ℝ) =
      (if vertex i j then 1 else 0 : ℝ) := by
  unfold bitRows
  split <;> simp

end

end MainTheory.D3SparseRationalization
