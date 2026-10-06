import SixQubit.BEnumerator

/-!
# The homogeneous quantum MacWilliams identity at arbitrary length

The coefficient arrays in `SS.MacWilliams` are unnormalised by a factor `K²`.
This file packages both arrays as homogeneous polynomials and proves the full
two-variable transform for arbitrary `n`, `K`, and frame amplitudes. The proof
uses the already established Pauli duality: its one-coordinate signed sum is
`x + 3*y` on the identity and `x - y` on each nonidentity Pauli.
-/

namespace MainTheory.MacWilliamsPolynomial

open scoped BigOperators
open SS.MacWilliams

noncomputable section

variable {n K : ℕ}

def monomial (n j : ℕ) (x y : ℝ) : ℝ := x ^ (n - j) * y ^ j

def rawA (psi : Fin K → SS.State n ℂ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), Aco psi j * monomial n j x y

def rawB (psi : Fin K → SS.State n ℂ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), Bco psi j * monomial n j x y

/-- The paper's homogeneous `A` polynomial, with its `1/K²` normalization. -/
def A (psi : Fin K → SS.State n ℂ) (x y : ℝ) : ℝ :=
  rawA psi x y / (K : ℝ) ^ 2

/-- The paper's homogeneous `B` polynomial; `Bco` already contains one `K`. -/
def B (psi : Fin K → SS.State n ℂ) (x y : ℝ) : ℝ :=
  rawB psi x y / (K : ℝ) ^ 2

private def coordinates : SS.PauliString n ≃ (Fin n → Bool × Bool) where
  toFun P i := (P.x i, P.z i)
  invFun p := ⟨fun i => (p i).1, fun i => (p i).2⟩
  left_inv _ := rfl
  right_inv p := by funext i; exact Prod.eta (p i)

private theorem sum_pauli_product (f : Fin n → Bool → Bool → ℝ) :
    ∑ P : SS.PauliString n, ∏ i, f i (P.x i) (P.z i) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, f i a b := by
  calc
    _ = ∑ p : Fin n → Bool × Bool, ∏ i, f i (p i).1 (p i).2 :=
      Fintype.sum_equiv coordinates _ _ (fun _ => rfl)
    _ = ∏ i, ∑ p : Bool × Bool, f i p.1 p.2 :=
      (Fintype.prod_sum (fun i (p : Bool × Bool) => f i p.1 p.2)).symm
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem monomial_eq_product (P : SS.PauliString n) (x y : ℝ) :
    monomial n P.wt x y = ∏ i, if P.x i || P.z i then y else x := by
  classical
  have hcount := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => (P.x i || P.z i) = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hcount
  have hneg : ((Finset.univ : Finset (Fin n)).filter
      (fun i => ¬ (P.x i || P.z i) = true)).card = n - P.wt := by
    unfold SS.PauliString.wt
    omega
  simp only [Finset.prod_ite, Finset.prod_const]
  rw [hneg]
  exact mul_comm _ _

private theorem one_coordinate (qx qz : Bool) (x y : ℝ) :
    (∑ a : Bool, ∑ b : Bool,
      (if a || b then y else x) *
        (if a && qz then (-1 : ℝ) else 1) *
        (if b && qx then (-1 : ℝ) else 1)) =
      if qx || qz then x - y else x + 3 * y := by
  cases qx <;> cases qz <;> simp <;> ring

private theorem signed_monomial_sum (Q : SS.PauliString n) (x y : ℝ) :
    ∑ P : SS.PauliString n,
      monomial n P.wt x y * chi P.x Q.z * chi P.z Q.x =
        monomial n Q.wt (x + 3 * y) (x - y) := by
  have hterm : ∀ P : SS.PauliString n,
      monomial n P.wt x y * chi P.x Q.z * chi P.z Q.x =
        ∏ i, (if P.x i || P.z i then y else x) *
          (if P.x i && Q.z i then (-1 : ℝ) else 1) *
          (if P.z i && Q.x i then (-1 : ℝ) else 1) := by
    intro P
    rw [monomial_eq_product, chi, chi, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [sum_pauli_product (fun i a b =>
    (if a || b then y else x) * (if a && Q.z i then (-1 : ℝ) else 1) *
      (if b && Q.x i then (-1 : ℝ) else 1))]
  simp_rw [one_coordinate]
  exact (monomial_eq_product Q _ _).symm

private theorem pauli_polynomial_duality (psi : Fin K → SS.State n ℂ) (x y : ℝ) :
    (2 : ℝ) ^ n * (∑ P : SS.PauliString n, monomial n P.wt x y * frob psi P) =
      ∑ Q : SS.PauliString n,
        monomial n Q.wt (x + 3 * y) (x - y) * Complex.normSq (trProj psi Q) := by
  calc
    _ = ∑ P : SS.PauliString n,
        monomial n P.wt x y * ((2 : ℝ) ^ n * frob psi P) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      ring
    _ = ∑ P : SS.PauliString n, monomial n P.wt x y *
        (∑ Q : SS.PauliString n,
          chi P.x Q.z * chi P.z Q.x * Complex.normSq (trProj psi Q)) := by
      simp_rw [pauli_duality]
    _ = ∑ Q : SS.PauliString n,
        (∑ P : SS.PauliString n, monomial n P.wt x y * chi P.x Q.z * chi P.z Q.x) *
          Complex.normSq (trProj psi Q) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro Q _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      ring
    _ = _ := by simp_rw [signed_monomial_sum]

private theorem sum_by_weight (c : ℕ → ℝ) (g : SS.PauliString n → ℝ) :
    ∑ P : SS.PauliString n, c P.wt * g P =
      ∑ j ∈ Finset.range (n + 1), c j *
        ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j), g P := by
  classical
  have hmap : ∀ P ∈ (Finset.univ : Finset (SS.PauliString n)),
      P.wt ∈ Finset.range (n + 1) := by
    intro P _
    have h : P.wt ≤ n := by
      simpa [SS.PauliString.wt] using Finset.card_le_univ
        ((Finset.univ : Finset (Fin n)).filter (fun i => P.x i || P.z i))
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun P => c P.wt * g P)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2])

/-- Homogeneous MacWilliams identity in the repository's `K²` convention. -/
theorem raw_macwilliams (psi : Fin K → SS.State n ℂ) (x y : ℝ) :
    (2 : ℝ) ^ n * rawB psi x y =
      (K : ℝ) * rawA psi (x + 3 * y) (x - y) := by
  have h := pauli_polynomial_duality psi x y
  rw [sum_by_weight (fun j => monomial n j x y) (frob psi),
    sum_by_weight (fun j => monomial n j (x + 3 * y) (x - y))
      (fun P => Complex.normSq (trProj psi P))] at h
  have hA : rawA psi (x + 3 * y) (x - y) =
      ∑ j ∈ Finset.range (n + 1), monomial n j (x + 3 * y) (x - y) *
        ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j),
          Complex.normSq (trProj psi P) := by
    simp only [rawA, Aco, mul_comm]
  have hB : rawB psi x y = (K : ℝ) *
      ∑ j ∈ Finset.range (n + 1), monomial n j x y *
        ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j), frob psi P := by
    unfold rawB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold Bco
    ring
  rw [hA, hB]
  calc
    _ = (K : ℝ) * ((2 : ℝ) ^ n *
        (∑ j ∈ Finset.range (n + 1), monomial n j x y *
          ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j), frob psi P)) := by
      ring
    _ = _ := congrArg (fun value : ℝ => (K : ℝ) * value) h

/-- `eq:quantum-MacWilliams`, for all lengths and all frame sizes. -/
theorem quantum_macwilliams (psi : Fin K → SS.State n ℂ) (x y : ℝ) :
    B psi x y = (K : ℝ) / (2 : ℝ) ^ n * A psi (x + 3 * y) (x - y) := by
  have htwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hraw : rawB psi x y =
      ((K : ℝ) * rawA psi (x + 3 * y) (x - y)) / (2 : ℝ) ^ n := by
    apply (eq_div_iff htwo).2
    simpa only [mul_comm] using raw_macwilliams psi x y
  rw [B, A, hraw]
  simp only [div_eq_mul_inv]
  ring

/-- The displayed finite sum defining the normalized `A` polynomial. -/
theorem A_eq_sum (psi : Fin K → SS.State n ℂ) (x y : ℝ) :
    A psi x y = ∑ j ∈ Finset.range (n + 1),
      (Aco psi j / (K : ℝ) ^ 2) * x ^ (n - j) * y ^ j := by
  simp only [A, rawA, Finset.sum_div, monomial]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The displayed finite sum defining the normalized `B` polynomial. -/
theorem B_eq_sum (psi : Fin K → SS.State n ℂ) (x y : ℝ) :
    B psi x y = ∑ j ∈ Finset.range (n + 1),
      (Bco psi j / (K : ℝ) ^ 2) * x ^ (n - j) * y ^ j := by
  simp only [B, rawB, Finset.sum_div, monomial]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem Bco_div_square (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Bco psi j / (K : ℝ) ^ 2 =
      (∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j),
        frob psi P) / (K : ℝ) := by
  by_cases hK : (K : ℝ) = 0
  · simp [Bco, hK]
  · simp only [Bco, pow_two]
    field_simp

/-- The `B` polynomial has precisely the paper's Frobenius normalization `1/K`. -/
theorem B_eq_frobenius_sum (psi : Fin K → SS.State n ℂ) (x y : ℝ) :
    B psi x y = ∑ j ∈ Finset.range (n + 1),
      ((∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j), frob psi P) /
        (K : ℝ)) * x ^ (n - j) * y ^ j := by
  rw [B_eq_sum]
  simp only [Bco_div_square]

/-- The Knill--Laflamme distance condition identifies both coefficient arrays. -/
theorem coefficients_equal_below_distance (psi : Fin K → SS.State n ℂ)
    {d j : ℕ} (hd : SS.HasDistance psi d) (hj : j < d) :
    Aco psi j = Bco psi j := by
  classical
  unfold Aco Bco
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply (frob_of_KL psi P ?_).symm
  apply hd P
  have hwt := (Finset.mem_filter.mp hP).2
  omega

/-- `eq:enumerator-distance`, in the normalized coefficient convention. -/
theorem normalized_coefficients_equal_below_distance
    (psi : Fin K → SS.State n ℂ) {d j : ℕ}
    (hd : SS.HasDistance psi d) (hj : j < d) :
    Aco psi j / (K : ℝ) ^ 2 = Bco psi j / (K : ℝ) ^ 2 := by
  rw [coefficients_equal_below_distance psi hd hj]

end

end MainTheory.MacWilliamsPolynomial
