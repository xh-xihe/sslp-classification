import MainTheory.SectorMeanValue

/-!
# `eq:Nj-detection` as a genuine equivalence

The paper introduces `N_j := (I - Z_j)/2` and asserts `P N_j P = mu_j P`, i.e.
`<psi_u| N_j |psi_v> = mu_j delta_uv` with `mu_j = (1 - lambda_j)/2`.

`SectorMeanValue` proved only the diagonal half, and never defined `N_j`: it
identified the occupation number of one sector vector with `(1 - lambda_j)/2`.
The off-diagonal half -- that distinct sector vectors have vanishing `N_j`
matrix element -- was available from `klScalar_spec` and orthonormality but had
not been assembled, so nothing in the repository stated the `delta_uv`.

This file defines `N_j`, proves it is the occupation-number operator (so the
name is earned, not asserted), gives the full matrix-element equivalence, and
then the operator identity `P N_j P = mu_j P` on the whole state space.
-/

namespace MainTheory.NumberOperator

open MainTheory.PhaseSectorFull
open MainTheory.SectorMeanValue
open SixQubit

variable {n t : ℕ} {theta : Fin n → ℝ}

/-- The single-site `Z_j` Pauli string. -/
def zPauli (j : Fin n) : SS.PauliString n := ⟨fun _ => false, SS.stdBasis j⟩

/-- **`N_j := (I - Z_j)/2`**, written literally as the paper does. -/
noncomputable def numberOp (j : Fin n) (psi : SS.State n ℂ) : SS.State n ℂ :=
  fun s => (psi s - SS.pauliAct (zPauli j) psi s) / 2

/-- **`N_j` is the occupation-number operator at site `j`.**  This is what
justifies the name; without it `(I - Z_j)/2` is only a formula. -/
theorem numberOp_apply (j : Fin n) (psi : SS.State n ℂ) (s : SS.BitString n) :
    numberOp j psi s = if s j then psi s else 0 := by
  have hbx : SS.bxor s (fun _ => false) = s := by
    funext i; simp [SS.bxor]
  have hact : SS.pauliAct (zPauli j) psi s
      = SS.signC (s j) (psi s) := by
    rw [SS.pauliAct, zPauli, numY_of_x_zero, pow_zero, one_mul, hbx,
      bdot_stdBasis]
  rw [numberOp, hact]
  cases hs : s j
  · simp
  · simp [SS.signC]

/-- Linearity of the inner product in its second argument, over a finite
sum. -/
private theorem innerC_sum {I : Type*} [Fintype I]
    (a : SS.State n ℂ) (f : I → SS.State n ℂ) :
    SS.innerC a (fun x => ∑ i, f i x) = ∑ i, SS.innerC a (f i) := by
  unfold SS.innerC
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]

private theorem innerC_numberOp_expand (a b : SS.State n ℂ) (j : Fin n) :
    SS.innerC a (numberOp j b)
      = (SS.innerC a b - SS.innerC a (SS.pauliAct (zPauli j) b)) / 2 := by
  unfold SS.innerC numberOp
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **`eq:Nj-detection`, both halves.**

`<psi_u| N_j |psi_v> = mu_j delta_uv` with `mu_j = (1 - lambda_j)/2`.  The
diagonal value is the paper's `mu_j`; the off-diagonal vanishing is what makes
this a detection statement rather than a mean value. -/
theorem innerC_numberOp (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (u v : D.Index) (j : Fin n) :
    SS.innerC (D.vec u) (numberOp j (D.vec v))
      = if u = v then (1 - klScalar D hZ j) / 2 else 0 := by
  rw [innerC_numberOp_expand, D.orthonormal u v]
  rw [show SS.innerC (D.vec u) (SS.pauliAct (zPauli j) (D.vec v))
      = if u = v then klScalar D hZ j else 0 from klScalar_spec D hZ j u v]
  by_cases h : u = v <;> simp [h]

/-- The same statement with the paper's `mu_j` written as the sector mean,
which `sectorMean_eq_klScalar` identifies with `(1 - lambda_j)/2`. -/
theorem innerC_numberOp_eq_sectorMean (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (alpha : Fin t) (u v : D.Index) (j : Fin n) :
    SS.innerC (D.vec u) (numberOp j (D.vec v))
      = if u = v then ((sectorMean D alpha j : ℝ) : ℂ) else 0 := by
  rw [innerC_numberOp D hZ u v j, sectorMean_eq_klScalar D hZ alpha j]

/-! ## The operator identity `P N_j P = mu_j P` -/

/-- The orthogonal projector onto the span of the sector vectors. -/
noncomputable def codeProj (D : SectorDecomposition n t theta)
    (psi : SS.State n ℂ) : SS.State n ℂ :=
  fun x => ∑ u : D.Index, SS.innerC (D.vec u) psi * D.vec u x

private theorem numberOp_codeProj (D : SectorDecomposition n t theta)
    (j : Fin n) (psi : SS.State n ℂ) :
    numberOp j (codeProj D psi)
      = fun x => ∑ u : D.Index,
          SS.innerC (D.vec u) psi * numberOp j (D.vec u) x := by
  funext x
  rw [numberOp_apply, codeProj]
  simp only [numberOp_apply]
  by_cases hx : x j
  · simp [hx]
  · simp [hx]

/-- **`P N_j P = mu_j P`.**  This is `eq:Nj-detection` in the paper's operator
form, on the whole state space, not merely on the sector vectors. -/
theorem codeProj_numberOp_codeProj (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (j : Fin n) (psi : SS.State n ℂ) :
    codeProj D (numberOp j (codeProj D psi))
      = fun x => ((1 - klScalar D hZ j) / 2) * codeProj D psi x := by
  funext x
  rw [codeProj, numberOp_codeProj]
  have hstep : ∀ u : D.Index,
      SS.innerC (D.vec u)
          (fun y => ∑ v : D.Index,
            SS.innerC (D.vec v) psi * numberOp j (D.vec v) y)
        = ((1 - klScalar D hZ j) / 2) * SS.innerC (D.vec u) psi := by
    intro u
    rw [innerC_sum (f := fun v : D.Index =>
      fun y => SS.innerC (D.vec v) psi * numberOp j (D.vec v) y)]
    have hterm : ∀ v : D.Index,
        SS.innerC (D.vec u)
            (fun y => SS.innerC (D.vec v) psi * numberOp j (D.vec v) y)
          = SS.innerC (D.vec v) psi *
              (if u = v then (1 - klScalar D hZ j) / 2 else 0) := by
      intro v
      rw [← innerC_numberOp D hZ u v j]
      unfold SS.innerC
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v),
      Finset.sum_eq_single_of_mem u (Finset.mem_univ u)
        (fun v _ hv => by simp [Ne.symm hv])]
    simp [mul_comm]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hstep u]), codeProj,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

end MainTheory.NumberOperator
