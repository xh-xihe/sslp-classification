import Mathlib

/-! # Tensor factorization of the category Fourier transform

The transform coefficients are derived by summing physical Pauli letters.
`AddMonoidAlgebra` records the two active-site counts. This avoids checking a
large, opaque table of pairs of six-qubit Pauli strings.
-/

namespace MainTheory.PauliCategoryFourier

open scoped BigOperators

noncomputable section

abbrev Polynomial := AddMonoidAlgebra ℤ (ℕ × ℕ)
abbrev Letter := Fin 4

def x (p : Letter) : Bool := p.val % 2 == 1
def z (p : Letter) : Bool := p.val / 2 == 1

def degree (p : Letter) : ℕ × ℕ :=
  (if p = 2 then 1 else 0, if x p then 1 else 0)

def sign (e p : Letter) : ℤ :=
  if xor (x e && z p) (z e && x p) then -1 else 1

def factor (p : Letter) : Polynomial :=
  ∑ e : Letter, AddMonoidAlgebra.single (degree e) (sign e p)

def identityFactor : Polynomial :=
  AddMonoidAlgebra.single (0, 0) 1 + AddMonoidAlgebra.single (1, 0) 1 +
    AddMonoidAlgebra.single (0, 1) 2

def zFactor : Polynomial :=
  AddMonoidAlgebra.single (0, 0) 1 + AddMonoidAlgebra.single (1, 0) 1 +
    AddMonoidAlgebra.single (0, 1) (-2)

def transverseFactor : Polynomial :=
  AddMonoidAlgebra.single (0, 0) 1 + AddMonoidAlgebra.single (1, 0) (-1)

def monomial (j k : ℕ) : Polynomial := AddMonoidAlgebra.single (j, k) 1

theorem monomial_pow_mul (j k : ℕ) :
    monomial 1 0 ^ j * monomial 0 1 ^ k = monomial j k := by
  simp [monomial, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]

theorem identityFactor_eq : identityFactor = 1 + monomial 1 0 + 2 * monomial 0 1 := by
  have hzero : (AddMonoidAlgebra.single (0, 0) 1 : Polynomial) = 1 := rfl
  unfold identityFactor monomial
  rw [show (2 : ℤ) = 1 + 1 from rfl, AddMonoidAlgebra.single_add]
  rw [hzero]
  ring

theorem zFactor_eq : zFactor = 1 + monomial 1 0 - 2 * monomial 0 1 := by
  have hzero : (AddMonoidAlgebra.single (0, 0) 1 : Polynomial) = 1 := rfl
  unfold zFactor monomial
  rw [show (-2 : ℤ) = -(1 + 1) from rfl, AddMonoidAlgebra.single_neg,
    AddMonoidAlgebra.single_add]
  rw [hzero]
  ring

theorem transverseFactor_eq : transverseFactor = 1 - monomial 1 0 := by
  have hzero : (AddMonoidAlgebra.single (0, 0) 1 : Polynomial) = 1 := rfl
  unfold transverseFactor monomial
  rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, AddMonoidAlgebra.single_neg,
    hzero]
  ring

theorem factor_formula (p : Letter) : factor p =
    if p = 0 then identityFactor else if p = 2 then zFactor else transverseFactor := by
  fin_cases p <;> ext t <;> by_cases h : (0, 1) = t <;>
    simp [factor, identityFactor, zFactor, transverseFactor, degree, sign, x, z,
      Fin.sum_univ_succ, AddMonoidAlgebra.single_apply, h] <;> ring

variable {I : Type*} [Fintype I]

def totalDegree (e : I → Letter) : ℕ × ℕ := ∑ i, degree (e i)
def totalSign (e p : I → Letter) : ℤ := ∏ i, sign (e i) (p i)

variable [DecidableEq I]

theorem tensor_factorization (p : I → Letter) :
    (∑ e : I → Letter, AddMonoidAlgebra.single (totalDegree e) (totalSign e p)) =
      ∏ i, factor (p i) := by
  classical
  unfold factor
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact (AddMonoidAlgebra.prod_single _ _ _).symm

theorem category_pairing_sum (p : I → Letter) (c : ℕ × ℕ) :
    (∑ e : I → Letter, if totalDegree e = c then totalSign e p else 0) =
      (∏ i, factor (p i)) c := by
  have h := congrArg (fun q : Polynomial => q c) (tensor_factorization p)
  dsimp only at h
  have hs : (∑ e : I → Letter, AddMonoidAlgebra.single (totalDegree e) (totalSign e p)) c =
      ∑ e : I → Letter, if totalDegree e = c then totalSign e p else 0 := by
    change (∑ e : I → Letter,
      Finsupp.single (totalDegree e) (totalSign e p)) c = _
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  rw [hs] at h
  exact h

def zCount (p : I → Letter) : ℕ := (Finset.univ.filter (fun i => p i = 2)).card
def transverseCount (p : I → Letter) : ℕ :=
  (Finset.univ.filter (fun i => x (p i) = true)).card
def identityCount (p : I → Letter) : ℕ := (Finset.univ.filter (fun i => p i = 0)).card

omit [DecidableEq I] in
theorem totalDegree_counts (p : I → Letter) :
    totalDegree p = (zCount p, transverseCount p) := by
  classical
  have h : totalDegree p =
      (∑ i, if p i = 2 then 1 else 0, ∑ i, if x (p i) then 1 else 0) := by
    unfold totalDegree degree
    have hsum (s : Finset I) :
        (∑ i ∈ s, (if p i = 2 then 1 else 0, if x (p i) then 1 else 0)) =
          (∑ i ∈ s, if p i = 2 then 1 else 0, ∑ i ∈ s, if x (p i) then 1 else 0) := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; rfl
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih]
        rfl
    exact hsum Finset.univ
  rw [h]
  simp [zCount, transverseCount, Finset.sum_boole]

omit [DecidableEq I] in
theorem factor_product (p : I → Letter) : (∏ i, factor (p i)) =
    identityFactor ^ identityCount p * zFactor ^ zCount p *
      transverseFactor ^ transverseCount p := by
  classical
  simp_rw [factor_formula]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.prod_const]
  have hZ : (Finset.filter (fun i => p i = 2)
      (Finset.univ.filter (fun i => ¬p i = 0))).card = zCount p := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; decide, h⟩
  have hX : (Finset.filter (fun i => ¬p i = 2)
      (Finset.univ.filter (fun i => ¬p i = 0))).card = transverseCount p := by
    congr 1
    ext i
    have hl : (p i ≠ 0 ∧ p i ≠ 2) ↔ x (p i) = true := by
      generalize p i = q
      fin_cases q <;> decide
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, transverseCount] using hl
  rw [hZ, hX]
  simp only [identityCount, mul_assoc]

end

end MainTheory.PauliCategoryFourier
