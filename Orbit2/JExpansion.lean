import Orbit2.ContractionExpansion

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem four_trace_operator (u v x y : Fin 32) :
    tau (operator (basis u) * operator (basis x) * operator (basis v) * operator (basis y)) =
      ((wordTrace [basis u,basis x,basis v,basis y]).re : ℂ) := by
  have h := wordTrace_correct [basis u,basis x,basis v,basis y]
  simpa only [wordOperator,List.foldl_cons,List.foldl_nil,Matrix.one_mul,four_trace_cast] using h

theorem triple_trace_pair (p : Label 4) (u v : Fin 32) :
    tau (operator p * operator (basis u) * operator (basis v)) =
      if product (basis u) (basis v)=p then (phase (basis u) (basis v) : ℂ) else 0 := by
  rw [Matrix.mul_assoc,operator_mul,Matrix.mul_smul,tau_smul,tau_operator_pair]
  simp [eq_comm,mul_ite]

theorem J_middle_trace (site ax : Fin 4) (u y : Fin 32) :
    tau (operator (basis u) * operator (single site ax) * operator (basis y)) =
      if product (basis u) (basis y)=single site ax then
        (character ax (basis u site) : ℂ) * (phase (basis u) (basis y) : ℂ) else 0 := by
  let σ := operator (single site ax)
  have hs : σ * σ=1 := by
    rw [operator_mul,phase_self,(product_eq_zero_iff _ _).mpr rfl,operator_zero]
    simp
  have he : operator (basis u) * σ = (character ax (basis u site) : ℂ) • (σ * operator (basis u)) := by
    have h := congrArg (fun M => σ * M) (single_conjugation site ax (basis u))
    change σ * (σ * operator (basis u) * σ) =
      σ * ((character ax (basis u site) : ℂ) • operator (basis u)) at h
    have h' : operator (basis u) * σ = (character ax (basis u site) : ℂ) • (σ * operator (basis u)) := by
      simpa only [Matrix.mul_smul,← Matrix.mul_assoc,hs,Matrix.one_mul] using h
    exact h'
  change tau (operator (basis u) * σ * operator (basis y)) = _
  rw [he,Matrix.smul_mul,tau_smul,triple_trace_pair]
  split_ifs <;> simp

theorem tau_three_fixed (A B C : Defects.ActiveMatrix) (a b c : Fin 32 → ℂ) :
    tau (A * expansion basis a * B * expansion basis b * C * expansion basis c) =
      ∑ y, ∑ v, ∑ x, a x * b v * c y *
        tau (A * operator (basis x) * B * operator (basis v) * C * operator (basis y)) := by
  unfold expansion
  simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    tau_sum,tau_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem J_second_trace (site ax : Fin 4) (u v x y : Fin 32) :
    tau (operator (basis u) * operator (single site ax) * operator (basis x) *
      operator (single site ax) * operator (basis v) * operator (basis y)) =
      (character ax (basis x site) : ℂ) *
        ((wordTrace [basis u,basis x,basis v,basis y]).re : ℂ) := by
  calc
    _ = tau (operator (basis u) * (operator (single site ax) * operator (basis x) *
      operator (single site ax)) * operator (basis v) * operator (basis y)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [single_conjugation,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,tau_smul,four_trace_operator]


def jLocalCoeff (site ax : Fin 4) (u v x y : Fin 32) : ℤ :=
  character ax (basis x site) * (character ax (basis v site) - 1) *
    (wordTrace [basis u,basis x,basis v,basis y]).re -
  4 * (if product (basis x) (basis v)=single site ax ∧
      product (basis u) (basis y)=single site ax then
    character ax (basis u site) * (phase (basis x) (basis v) * phase (basis u) (basis y)).re
    else 0)

theorem tau_sub (A B : Defects.ActiveMatrix) : tau (A-B)=tau A-tau B := by
  simp [tau, Matrix.trace_sub, sub_div]

theorem correlation_expansion (t : Fin 32 → ℂ) (p : Label 4) :
    Defects.correlation (expansion basis t) (operator p) =
      ∑ v, ∑ x, t x * star (t v) *
        (if product (basis x) (basis v)=p then (phase (basis x) (basis v) : ℂ) else 0) := by
  unfold Defects.correlation
  rw [expansion_conjTranspose]
  unfold expansion
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    tau_sum,tau_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  rw [triple_trace_pair]
  ring

theorem J_linear_trace (t : Fin 32 → ℂ) (site ax : Fin 4) (u : Fin 32) :
    tau (operator (basis u) * operator (single site ax) * expansion basis t) =
      ∑ y, t y * (if product (basis u) (basis y)=single site ax then
        (character ax (basis u site) : ℂ) * (phase (basis u) (basis y) : ℂ) else 0) := by
  simp only [expansion,Matrix.mul_sum,Matrix.mul_smul,tau_sum,tau_smul,J_middle_trace]

theorem J_cubic_difference (t : Fin 32 → ℂ) (site ax : Fin 4) (u : Fin 32) :
    tau (operator (basis u) * operator (single site ax) *
      (expansion basis t * (expansion basis t).conjTranspose * operator (single site ax) *
        expansion basis t - expansion basis t * operator (single site ax) *
        (expansion basis t).conjTranspose * expansion basis t)) =
    ∑ y, ∑ v, ∑ x, t x * star (t v) * t y *
      ((character ax (basis x site) * (character ax (basis v site)-1) *
        (wordTrace [basis u,basis x,basis v,basis y]).re : ℤ) : ℂ) := by
  rw [Matrix.mul_sub,tau_sub,expansion_conjTranspose]
  have h₁ := tau_three_fixed (operator (basis u) * operator (single site ax)) 1
    (operator (single site ax)) t (fun v => star (t v)) t
  have h₂ := tau_three_fixed (operator (basis u) * operator (single site ax))
    (operator (single site ax)) 1 t (fun v => star (t v)) t
  simp only [Matrix.mul_one,Matrix.mul_assoc] at h₁ h₂
  simp only [Matrix.mul_assoc]
  rw [h₁,h₂,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hfirst := J_trace_shortcut site ax (basis u) (basis v) (basis x) (basis y)
  have hsecond := J_second_trace site ax u v x y
  simp only [Matrix.mul_assoc] at hfirst hsecond
  rw [hfirst,hsecond]
  have hfour := four_trace_operator u v x y
  simp only [Matrix.mul_assoc] at hfour
  rw [hfour]
  push_cast
  ring

theorem J_correlation_product (t : Fin 32 → ℂ) (site ax : Fin 4) (u : Fin 32) :
    Defects.correlation (expansion basis t) (operator (single site ax)) *
      tau (operator (basis u) * operator (single site ax) * expansion basis t) =
    ∑ y, ∑ v, ∑ x, t x * star (t v) * t y *
      ((if product (basis x) (basis v)=single site ax ∧
        product (basis u) (basis y)=single site ax then
        character ax (basis u site) *
          (phase (basis x) (basis v) * phase (basis u) (basis y)).re else 0 : ℤ) : ℂ) := by
  rw [correlation_expansion,J_linear_trace]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : product (basis x) (basis v)=single site ax
  · by_cases hu : product (basis u) (basis y)=single site ax
    · simp only [hx,hu,and_self,if_true]
      have hr := gaussian_cast_of_im_zero _ (phase_product_im_zero x v u y (hx.trans hu.symm))
      rw [GaussianInt.toComplex_mul] at hr
      push_cast
      rw [← hr]
      push_cast
      ring
    · simp [hx,hu]
  · simp [hx]

theorem J_local_contraction (t : Fin 32 → ℂ) (site ax : Fin 4) (u : Fin 32) :
    star (t u) * tau (operator (basis u) * operator (single site ax) *
      Defects.compressionDefect (expansion basis t) (operator (single site ax))) =
    ∑ y, ∑ v, ∑ x, star (t u) * t x * star (t v) * t y *
      (jLocalCoeff site ax u v x y : ℂ) := by
  unfold Defects.compressionDefect
  rw [Matrix.mul_sub,tau_sub,Matrix.mul_smul,tau_smul,J_cubic_difference]
  have hp := J_correlation_product t site ax u
  rw [mul_assoc (4 : ℂ),hp]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  unfold jLocalCoeff
  push_cast
  ring

theorem jCoeff_eq_sum (u v x y : Fin 32) :
    jCoeff u v x y = ∑ site : Fin 4, ∑ ax : Fin 4,
      jWeight site ax u * jLocalCoeff site ax u v x y := by
  unfold jCoeff jLocalCoeff
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro site _
  apply Finset.sum_congr rfl
  intro ax _
  split_ifs <;> ring

theorem sum_rotate_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]


theorem sum_rotate_five {α β γ δ ε : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] [Fintype ε] (f : α → β → γ → δ → ε → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [sum_rotate_four]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]

theorem orderedPolynomial_sum {ι : Type*} [Fintype ι]
    (k : ι → Fin 32 → Fin 32 → Fin 32 → Fin 32 → ℤ) (t : Fin 32 → ℂ) :
    orderedPolynomial (fun u v x y => ∑ i, k i u v x y) t =
      ∑ i, orderedPolynomial (k i) t := by
  unfold orderedPolynomial
  simp only [Int.cast_sum,Finset.mul_sum]
  exact (sum_rotate_five _).symm

theorem J_weighted_local (t : Fin 32 → ℂ) (site ax : Fin 4) :
    orderedPolynomial (fun u v x y => jWeight site ax u * jLocalCoeff site ax u v x y) t =
    ∑ u, (jWeight site ax u : ℂ) * star (t u) *
      tau (operator (basis u) * operator (single site ax) *
        Defects.compressionDefect (expansion basis t) (operator (single site ax))) := by
  unfold orderedPolynomial
  calc
    _ = ∑ u, ∑ y, ∑ v, ∑ x, star (t u) * t x * star (t v) * t y *
      ((jWeight site ax u * jLocalCoeff site ax u v x y : ℤ) : ℂ) :=
        (sum_rotate_four _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc,J_local_contraction]
      simp only [Finset.mul_sum,Int.cast_mul]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem J_contraction_expansion (t : Fin 32 → ℂ) :
    (∑ site : Fin 4, ∑ ax : Fin 4, ∑ u : Fin 32,
      (jWeight site ax u : ℂ) * star (t u) *
      tau (operator (basis u) * operator (single site ax) *
        Defects.compressionDefect (expansion basis t) (operator (single site ax)))) =
    orderedPolynomial jCoeff t := by
  have hk : jCoeff = fun u v x y => ∑ site : Fin 4, ∑ ax : Fin 4,
      jWeight site ax u * jLocalCoeff site ax u v x y := by
    funext u v x y
    exact jCoeff_eq_sum u v x y
  rw [hk,orderedPolynomial_sum]
  simp_rw [orderedPolynomial_sum,J_weighted_local]

end Orbit2.Quartic
