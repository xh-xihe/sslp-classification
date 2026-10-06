import Mathlib

import SS.FullKL
import SixQubit.Common

set_option maxHeartbeats 2000000
/-!
# The `ℂ⁴` frame layer for orbit 5

Orbit 5 of `six_qubit_sslp.tex` has **two** zero-angle qubits, so its
amplitudes group into vectors of `ℂ⁴` rather than the `ℂ²` handled by
`SixQubit.Frame`.  This module isolates the two purely analytic steps of the
argument, in coordinates and with no matrix machinery.

* `cs_tight` -- the tightness step.  If the two logical marginals on the free
  pair agree, and the anchor `u` is orthogonal to all four top vectors, then
  sandwiching the marginal equality in `u` gives

  ```
  ‖u‖⁴ + Σᵢ |u†aᵢ|² = |u†v|² ≤ ‖u‖²‖v‖² = ‖u‖⁴ ,
  ```

  so Cauchy--Schwarz is tight: every `u†aᵢ` vanishes and `v` is a unit multiple
  of `u`, whence `v v† = u u†`.

* `bell_contradiction` -- the trace step.  Once the two anchors cancel, the
  four bottom vectors and the four top vectors have the same frame operator
  `R`.  If moreover `aᵢ†bⱼ = 0` for `i ≠ j`, then

  ```
  Tr(R²) = Σᵢⱼ |aᵢ†bⱼ|² = Σᵢ |aᵢ†bᵢ|² ≤ 4·(1/6)² = 1/9 ,
  ```

  while `Tr(R²) = Σᵢⱼ |aᵢ†aⱼ|² ≥ Σᵢ ‖aᵢ‖⁴ = 1/9`.  Equality forces the four
  `aᵢ` to be pairwise orthogonal, so `6R` is an idempotent of trace `4` in
  dimension four, i.e. the identity; but `R u = 0`, so `u = 0`, contradicting
  `‖u‖² = 1/3`.

The Cauchy--Schwarz inequality itself is proved from the Lagrange identity, so
the whole file is elementary algebra over `ℂ` plus `nlinarith`.  Neither
`native_decide` nor `sorry` occurs.
-/

namespace SixQubit.Trace5

open scoped ComplexConjugate

noncomputable section

/-! ## Coordinates -/

/-- The Hermitian inner product `x† y` of two vectors of `ℂ⁴`, written out. -/
def ip (x y : Fin 4 → ℂ) : ℂ :=
  star (x 0) * y 0 + star (x 1) * y 1 + star (x 2) * y 2 + star (x 3) * y 3

/-- The squared norm `‖x‖²` of a vector of `ℂ⁴`, written out. -/
def nsq (x : Fin 4 → ℂ) : Real :=
  Complex.normSq (x 0) + Complex.normSq (x 1) + Complex.normSq (x 2) + Complex.normSq (x 3)

theorem mul_star (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  simpa using (Complex.mul_conj z)

theorem ip_star (x y : Fin 4 → ℂ) : star (ip x y) = ip y x := by
  simp only [ip, star_add, star_mul', star_star]
  ring

theorem ip_self (x : Fin 4 → ℂ) : ip x x = (nsq x : ℂ) := by
  simp only [ip, nsq, SixQubit.star_mul_self]
  push_cast
  ring

theorem ip_mul_ip (x y : Fin 4 → ℂ) :
    ip x y * ip y x = (Complex.normSq (ip x y) : ℂ) := by
  have h : ip y x = star (ip x y) := (ip_star x y).symm
  rw [h, mul_star]

/-! ## Cauchy--Schwarz from the Lagrange identity -/

/-- The Lagrange identity in `ℂ⁴`, over `ℂ`. -/
theorem lagrange (x y : Fin 4 → ℂ) :
    (nsq x : ℂ) * (nsq y : ℂ) - (Complex.normSq (ip x y) : ℂ)
      = (Complex.normSq (x 0 * y 1 - x 1 * y 0) : ℂ)
        + (Complex.normSq (x 0 * y 2 - x 2 * y 0) : ℂ)
        + (Complex.normSq (x 0 * y 3 - x 3 * y 0) : ℂ)
        + (Complex.normSq (x 1 * y 2 - x 2 * y 1) : ℂ)
        + (Complex.normSq (x 1 * y 3 - x 3 * y 1) : ℂ)
        + (Complex.normSq (x 2 * y 3 - x 3 * y 2) : ℂ) := by
  simp only [nsq, ip, Complex.ofReal_add,
    ← SixQubit.star_mul_self, star_sub, star_add, star_mul', star_star]
  ring

/-- The Lagrange identity in `ℂ⁴`, over `ℝ`. -/
theorem lagrange_real (x y : Fin 4 → ℂ) :
    nsq x * nsq y - Complex.normSq (ip x y)
      = Complex.normSq (x 0 * y 1 - x 1 * y 0)
        + Complex.normSq (x 0 * y 2 - x 2 * y 0)
        + Complex.normSq (x 0 * y 3 - x 3 * y 0)
        + Complex.normSq (x 1 * y 2 - x 2 * y 1)
        + Complex.normSq (x 1 * y 3 - x 3 * y 1)
        + Complex.normSq (x 2 * y 3 - x 3 * y 2) := by
  have h : (nsq x : ℂ) * (nsq y : ℂ) - (Complex.normSq (ip x y) : ℂ)
      = ((Complex.normSq (x 0 * y 1 - x 1 * y 0)
          + Complex.normSq (x 0 * y 2 - x 2 * y 0)
          + Complex.normSq (x 0 * y 3 - x 3 * y 0)
          + Complex.normSq (x 1 * y 2 - x 2 * y 1)
          + Complex.normSq (x 1 * y 3 - x 3 * y 1)
          + Complex.normSq (x 2 * y 3 - x 3 * y 2) : Real) : ℂ) := by
    push_cast
    exact lagrange x y
  exact_mod_cast h

/-- Cauchy--Schwarz in `ℂ⁴`. -/
theorem cs (x y : Fin 4 → ℂ) : Complex.normSq (ip x y) ≤ nsq x * nsq y := by
  have h := lagrange_real x y
  have h1 := Complex.normSq_nonneg (x 0 * y 1 - x 1 * y 0)
  have h2 := Complex.normSq_nonneg (x 0 * y 2 - x 2 * y 0)
  have h3 := Complex.normSq_nonneg (x 0 * y 3 - x 3 * y 0)
  have h4 := Complex.normSq_nonneg (x 1 * y 2 - x 2 * y 1)
  have h5 := Complex.normSq_nonneg (x 1 * y 3 - x 3 * y 1)
  have h6 := Complex.normSq_nonneg (x 2 * y 3 - x 3 * y 2)
  linarith

/-- Tightness in Cauchy--Schwarz kills every `2 × 2` minor. -/
theorem wedges_zero {x y : Fin 4 → ℂ}
    (h : nsq x * nsq y ≤ Complex.normSq (ip x y)) :
    x 0 * y 1 = x 1 * y 0 ∧ x 0 * y 2 = x 2 * y 0 ∧ x 0 * y 3 = x 3 * y 0 ∧
      x 1 * y 2 = x 2 * y 1 ∧ x 1 * y 3 = x 3 * y 1 ∧ x 2 * y 3 = x 3 * y 2 := by
  have hl := lagrange_real x y
  have h1 := Complex.normSq_nonneg (x 0 * y 1 - x 1 * y 0)
  have h2 := Complex.normSq_nonneg (x 0 * y 2 - x 2 * y 0)
  have h3 := Complex.normSq_nonneg (x 0 * y 3 - x 3 * y 0)
  have h4 := Complex.normSq_nonneg (x 1 * y 2 - x 2 * y 1)
  have h5 := Complex.normSq_nonneg (x 1 * y 3 - x 3 * y 1)
  have h6 := Complex.normSq_nonneg (x 2 * y 3 - x 3 * y 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hz : Complex.normSq (x 0 * y 1 - x 1 * y 0) = 0 := by linarith
    linear_combination Complex.normSq_eq_zero.mp hz
  · have hz : Complex.normSq (x 0 * y 2 - x 2 * y 0) = 0 := by linarith
    linear_combination Complex.normSq_eq_zero.mp hz
  · have hz : Complex.normSq (x 0 * y 3 - x 3 * y 0) = 0 := by linarith
    linear_combination Complex.normSq_eq_zero.mp hz
  · have hz : Complex.normSq (x 1 * y 2 - x 2 * y 1) = 0 := by linarith
    linear_combination Complex.normSq_eq_zero.mp hz
  · have hz : Complex.normSq (x 1 * y 3 - x 3 * y 1) = 0 := by linarith
    linear_combination Complex.normSq_eq_zero.mp hz
  · have hz : Complex.normSq (x 2 * y 3 - x 3 * y 2) = 0 := by linarith
    linear_combination Complex.normSq_eq_zero.mp hz

/-- Tightness in Cauchy--Schwarz makes `y` a multiple of `x`:
`‖x‖² yₗ = xₗ (x†y)` for every coordinate `l`. -/
theorem par {x y : Fin 4 → ℂ}
    (h : nsq x * nsq y ≤ Complex.normSq (ip x y)) :
    ip x x * y 0 = x 0 * ip x y ∧ ip x x * y 1 = x 1 * ip x y ∧
      ip x x * y 2 = x 2 * ip x y ∧ ip x x * y 3 = x 3 * ip x y := by
  obtain ⟨e01, e02, e03, e12, e13, e23⟩ := wedges_zero h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [ip]
  · linear_combination (-star (x 1)) * e01 + (-star (x 2)) * e02 + (-star (x 3)) * e03
  · linear_combination (star (x 0)) * e01 + (-star (x 2)) * e12 + (-star (x 3)) * e13
  · linear_combination (star (x 0)) * e02 + (star (x 1)) * e12 + (-star (x 3)) * e23
  · linear_combination (star (x 0)) * e03 + (star (x 1)) * e13 + (star (x 2)) * e23

/-! ## The frame operator -/

/-- One entry of the frame operator `R = Σᵢ aᵢ aᵢ†` of a four-vector family. -/
def fr (a1 a2 a3 a4 : Fin 4 → ℂ) (k l : Fin 4) : ℂ :=
  a1 k * star (a1 l) + a2 k * star (a2 l) + a3 k * star (a3 l) + a4 k * star (a4 l)

/-- The diagonal entries of the frame operator are the real column masses. -/
theorem fr_diag (a1 a2 a3 a4 : Fin 4 → ℂ) (k : Fin 4) :
    fr a1 a2 a3 a4 k k = ((Complex.normSq (a1 k) + Complex.normSq (a2 k) + Complex.normSq (a3 k)
      + Complex.normSq (a4 k) : Real) : ℂ) := by
  simp only [fr]
  push_cast [← SixQubit.star_mul_self]
  ring

/-! ## The tightness step -/

/-- **Tightness.**  If the two marginals on the free pair agree and the anchor
`u` is orthogonal to all four top vectors, then `u` is orthogonal to all four
bottom vectors as well, and the two anchors contribute the same rank-one piece,
so the two frame operators agree. -/
theorem cs_tight (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)
    (hu : nsq u = 1/3) (hv : nsq v = 1/3)
    (hq1 : ip u b1 = 0) (hq2 : ip u b2 = 0) (hq3 : ip u b3 = 0) (hq4 : ip u b4 = 0)
    (hf : ∀ k l : Fin 4, u k * star (u l) + fr a1 a2 a3 a4 k l
            = fr b1 b2 b3 b4 k l + v k * star (v l)) :
    ip u a1 = 0 ∧ ip u a2 = 0 ∧ ip u a3 = 0 ∧ ip u a4 = 0 ∧
      ∀ k l : Fin 4, fr a1 a2 a3 a4 k l = fr b1 b2 b3 b4 k l := by
  simp only [fr] at hf
  have key : ip u u * ip u u + (ip u a1 * ip a1 u + ip u a2 * ip a2 u + ip u a3 * ip a3 u
        + ip u a4 * ip a4 u
      ) = (ip u b1 * ip b1 u + ip u b2 * ip b2 u + ip u b3 * ip b3 u + ip u b4 * ip b4 u) + ip u v * ip v u := by
    simp only [ip]
    linear_combination (star (u 0) * u 0) * hf 0 0 + (star (u 0) * u 1) * hf 0 1
      + (star (u 0) * u 2) * hf 0 2 + (star (u 0) * u 3) * hf 0 3 + (star (u 1) * u 0) * hf 1 0
      + (star (u 1) * u 1) * hf 1 1 + (star (u 1) * u 2) * hf 1 2 + (star (u 1) * u 3) * hf 1 3
      + (star (u 2) * u 0) * hf 2 0 + (star (u 2) * u 1) * hf 2 1 + (star (u 2) * u 2) * hf 2 2
      + (star (u 2) * u 3) * hf 2 3 + (star (u 3) * u 0) * hf 3 0 + (star (u 3) * u 1) * hf 3 1
      + (star (u 3) * u 2) * hf 3 2 + (star (u 3) * u 3) * hf 3 3
  rw [ip_mul_ip u u, ip_mul_ip u a1, ip_mul_ip u a2, ip_mul_ip u a3, ip_mul_ip u a4,
    ip_mul_ip u b1, ip_mul_ip u b2, ip_mul_ip u b3, ip_mul_ip u b4, ip_mul_ip u v] at key
  have keyR : Complex.normSq (ip u u) + (Complex.normSq (ip u a1) + Complex.normSq (ip u a2)
        + Complex.normSq (ip u a3) + Complex.normSq (ip u a4)
      ) = (Complex.normSq (ip u b1) + Complex.normSq (ip u b2) + Complex.normSq (ip u b3)
        + Complex.normSq (ip u b4)) + Complex.normSq (ip u v) := by
    exact_mod_cast key
  have huu : Complex.normSq (ip u u) = 1/9 := by
    rw [ip_self, hu, Complex.normSq_ofReal]; norm_num
  have hz1 : Complex.normSq (ip u b1) = 0 := by rw [hq1]; simp
  have hz2 : Complex.normSq (ip u b2) = 0 := by rw [hq2]; simp
  have hz3 : Complex.normSq (ip u b3) = 0 := by rw [hq3]; simp
  have hz4 : Complex.normSq (ip u b4) = 0 := by rw [hq4]; simp
  have hcs := cs u v
  rw [hu, hv] at hcs
  have hnn1 := Complex.normSq_nonneg (ip u a1)
  have hnn2 := Complex.normSq_nonneg (ip u a2)
  have hnn3 := Complex.normSq_nonneg (ip u a3)
  have hnn4 := Complex.normSq_nonneg (ip u a4)
  have hp1 : ip u a1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have hp2 : ip u a2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have hp3 : ip u a3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have hp4 : ip u a4 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have hnv : Complex.normSq (ip u v) = 1/9 := by linarith
  have huv : nsq u * nsq v ≤ Complex.normSq (ip u v) := by rw [hu, hv, hnv]; norm_num
  obtain ⟨w0, w1, w2, w3⟩ := par huv
  have hiu : ip u u = ((1/3 : Real) : ℂ) := by rw [ip_self, hu]
  rw [hiu] at w0 w1 w2 w3
  have hmu : ip u v * star (ip u v) = ((1/9 : Real) : ℂ) := by rw [mul_star, hnv]
  have hthird : star (((1/3 : Real)) : ℂ) = ((1/3 : Real) : ℂ) := by simp
  have hvl : ∀ l : Fin 4, ((1/3 : Real) : ℂ) * v l = u l * ip u v := by
    intro l; fin_cases l
    exacts [w0, w1, w2, w3]
  have hvv : ∀ k l : Fin 4, v k * star (v l) = u k * star (u l) := by
    intro k l
    have e1 := hvl k
    have e2 := congrArg star (hvl l)
    rw [star_mul', hthird, star_mul'] at e2
    push_cast at e1 e2 hmu
    linear_combination (3 * star (v l)) * e1 + (9 * u k * ip u v) * e2
      + (9 * u k * star (u l)) * hmu
  refine ⟨hp1, hp2, hp3, hp4, ?_⟩
  intro k l
  simp only [fr]
  linear_combination hf k l + hvv k l

/-! ## The trace identities -/

/-- Equality of the two frame operators transports the Gram sum of the bottom
family to the mixed Gram sum. -/
theorem frame_swap (a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)
    (hf : ∀ k l : Fin 4, fr a1 a2 a3 a4 k l = fr b1 b2 b3 b4 k l) :
    (ip a1 a1 * ip a1 a1 + ip a1 a2 * ip a2 a1 + ip a1 a3 * ip a3 a1 + ip a1 a4 * ip a4 a1
      + ip a2 a1 * ip a1 a2 + ip a2 a2 * ip a2 a2 + ip a2 a3 * ip a3 a2 + ip a2 a4 * ip a4 a2
      + ip a3 a1 * ip a1 a3 + ip a3 a2 * ip a2 a3 + ip a3 a3 * ip a3 a3 + ip a3 a4 * ip a4 a3
      + ip a4 a1 * ip a1 a4 + ip a4 a2 * ip a2 a4 + ip a4 a3 * ip a3 a4 + ip a4 a4 * ip a4 a4
      ) = (ip a1 b1 * ip b1 a1 + ip a1 b2 * ip b2 a1 + ip a1 b3 * ip b3 a1 + ip a1 b4 * ip b4 a1
      + ip a2 b1 * ip b1 a2 + ip a2 b2 * ip b2 a2 + ip a2 b3 * ip b3 a2 + ip a2 b4 * ip b4 a2
      + ip a3 b1 * ip b1 a3 + ip a3 b2 * ip b2 a3 + ip a3 b3 * ip b3 a3 + ip a3 b4 * ip b4 a3
      + ip a4 b1 * ip b1 a4 + ip a4 b2 * ip b2 a4 + ip a4 b3 * ip b3 a4 + ip a4 b4 * ip b4 a4) := by
  simp only [fr] at hf
  simp only [ip]
  linear_combination (star (a1 0) * a1 0 + star (a2 0) * a2 0 + star (a3 0) * a3 0
    + star (a4 0) * a4 0) * hf 0 0 + (star (a1 0) * a1 1 + star (a2 0) * a2 1 + star (a3 0) * a3 1
    + star (a4 0) * a4 1) * hf 0 1 + (star (a1 0) * a1 2 + star (a2 0) * a2 2 + star (a3 0) * a3 2
    + star (a4 0) * a4 2) * hf 0 2 + (star (a1 0) * a1 3 + star (a2 0) * a2 3 + star (a3 0) * a3 3
    + star (a4 0) * a4 3) * hf 0 3 + (star (a1 1) * a1 0 + star (a2 1) * a2 0 + star (a3 1) * a3 0
    + star (a4 1) * a4 0) * hf 1 0 + (star (a1 1) * a1 1 + star (a2 1) * a2 1 + star (a3 1) * a3 1
    + star (a4 1) * a4 1) * hf 1 1 + (star (a1 1) * a1 2 + star (a2 1) * a2 2 + star (a3 1) * a3 2
    + star (a4 1) * a4 2) * hf 1 2 + (star (a1 1) * a1 3 + star (a2 1) * a2 3 + star (a3 1) * a3 3
    + star (a4 1) * a4 3) * hf 1 3 + (star (a1 2) * a1 0 + star (a2 2) * a2 0 + star (a3 2) * a3 0
    + star (a4 2) * a4 0) * hf 2 0 + (star (a1 2) * a1 1 + star (a2 2) * a2 1 + star (a3 2) * a3 1
    + star (a4 2) * a4 1) * hf 2 1 + (star (a1 2) * a1 2 + star (a2 2) * a2 2 + star (a3 2) * a3 2
    + star (a4 2) * a4 2) * hf 2 2 + (star (a1 2) * a1 3 + star (a2 2) * a2 3 + star (a3 2) * a3 3
    + star (a4 2) * a4 3) * hf 2 3 + (star (a1 3) * a1 0 + star (a2 3) * a2 0 + star (a3 3) * a3 0
    + star (a4 3) * a4 0) * hf 3 0 + (star (a1 3) * a1 1 + star (a2 3) * a2 1 + star (a3 3) * a3 1
    + star (a4 3) * a4 1) * hf 3 1 + (star (a1 3) * a1 2 + star (a2 3) * a2 2 + star (a3 3) * a3 2
    + star (a4 3) * a4 2) * hf 3 2 + (star (a1 3) * a1 3 + star (a2 3) * a2 3 + star (a3 3) * a3 3
    + star (a4 3) * a4 3) * hf 3 3

/-- For a pairwise orthogonal family of squared norm `1/6` the frame operator
satisfies `R² = R/6`; this is the `k`-th diagonal entry of that identity. -/
theorem frame_idem (a1 a2 a3 a4 : Fin 4 → ℂ)
    (ho12 : ip a1 a2 = 0)
    (ho13 : ip a1 a3 = 0)
    (ho14 : ip a1 a4 = 0)
    (ho21 : ip a2 a1 = 0)
    (ho23 : ip a2 a3 = 0)
    (ho24 : ip a2 a4 = 0)
    (ho31 : ip a3 a1 = 0)
    (ho32 : ip a3 a2 = 0)
    (ho34 : ip a3 a4 = 0)
    (ho41 : ip a4 a1 = 0)
    (ho42 : ip a4 a2 = 0)
    (ho43 : ip a4 a3 = 0)
    (hs1 : ip a1 a1 = (1/6 : ℂ)) (hs2 : ip a2 a2 = (1/6 : ℂ))
    (hs3 : ip a3 a3 = (1/6 : ℂ)) (hs4 : ip a4 a4 = (1/6 : ℂ)) (k : Fin 4) :
    fr a1 a2 a3 a4 k 0 * star (fr a1 a2 a3 a4 k 0) + fr a1 a2 a3 a4 k 1 * star (fr a1 a2 a3 a4 k 1)
      + fr a1 a2 a3 a4 k 2 * star (fr a1 a2 a3 a4 k 2)
      + fr a1 a2 a3 a4 k 3 * star (fr a1 a2 a3 a4 k 3)
      = (1/6 : ℂ) * ((Complex.normSq (a1 k) + Complex.normSq (a2 k) + Complex.normSq (a3 k)
        + Complex.normSq (a4 k) : Real) : ℂ) := by
  simp only [ip] at ho12 ho13 ho14 ho21 ho23 ho24 ho31 ho32 ho34 ho41 ho42 ho43
  simp only [ip] at hs1 hs2 hs3 hs4
  simp only [fr, star_add, star_mul', star_star]
  push_cast [← SixQubit.star_mul_self]
  linear_combination (a1 k * star (a1 k)) * hs1 + (a1 k * star (a2 k)) * ho12
    + (a1 k * star (a3 k)) * ho13 + (a1 k * star (a4 k)) * ho14 + (a2 k * star (a1 k)) * ho21
    + (a2 k * star (a2 k)) * hs2 + (a2 k * star (a3 k)) * ho23 + (a2 k * star (a4 k)) * ho24
    + (a3 k * star (a1 k)) * ho31 + (a3 k * star (a2 k)) * ho32 + (a3 k * star (a3 k)) * hs3
    + (a3 k * star (a4 k)) * ho34 + (a4 k * star (a1 k)) * ho41 + (a4 k * star (a2 k)) * ho42
    + (a4 k * star (a3 k)) * ho43 + (a4 k * star (a4 k)) * hs4

/-- The frame operator annihilates every vector orthogonal to the family. -/
theorem frame_kernel (u a1 a2 a3 a4 : Fin 4 → ℂ)
    (hk1 : ip a1 u = 0) (hk2 : ip a2 u = 0) (hk3 : ip a3 u = 0) (hk4 : ip a4 u = 0)
    (k : Fin 4) :
    fr a1 a2 a3 a4 k 0 * u 0 + fr a1 a2 a3 a4 k 1 * u 1 + fr a1 a2 a3 a4 k 2 * u 2
      + fr a1 a2 a3 a4 k 3 * u 3 = 0 := by
  simp only [ip] at hk1 hk2 hk3 hk4
  simp only [fr]
  linear_combination (a1 k) * hk1 + (a2 k) * hk2 + (a3 k) * hk3 + (a4 k) * hk4

/-- A real with `e² ≤ e/6` is at most `1/6`. -/
theorem mass_le {e : Real} (h : e * e ≤ 1/6 * e) : e ≤ 1/6 := by
  nlinarith

/-! ## Five orthogonal vectors do not fit in `ℂ⁴` -/

/-- **Overflow.**  Four pairwise orthogonal vectors of squared norm `1/6`
together with a further orthogonal vector of squared norm `1/3` cannot live in
`ℂ⁴`: the frame operator of the four is `1/6` times an idempotent of trace `4`,
hence `1/6` times the identity, which cannot annihilate a nonzero vector. -/
theorem orthogonal_overflow (u a1 a2 a3 a4 : Fin 4 → ℂ)
    (hu : nsq u = 1/3)
    (ha1 : nsq a1 = 1/6) (ha2 : nsq a2 = 1/6) (ha3 : nsq a3 = 1/6) (ha4 : nsq a4 = 1/6)
    (hq1 : ip u a1 = 0) (hq2 : ip u a2 = 0) (hq3 : ip u a3 = 0) (hq4 : ip u a4 = 0)
    (ho12 : ip a1 a2 = 0)
    (ho13 : ip a1 a3 = 0)
    (ho14 : ip a1 a4 = 0)
    (ho21 : ip a2 a1 = 0)
    (ho23 : ip a2 a3 = 0)
    (ho24 : ip a2 a4 = 0)
    (ho31 : ip a3 a1 = 0)
    (ho32 : ip a3 a2 = 0)
    (ho34 : ip a3 a4 = 0)
    (ho41 : ip a4 a1 = 0)
    (ho42 : ip a4 a2 = 0)
    (ho43 : ip a4 a3 = 0)
    : False := by
  have hs1 : ip a1 a1 = (1/6 : ℂ) := by rw [ip_self, ha1]; norm_num
  have hs2 : ip a2 a2 = (1/6 : ℂ) := by rw [ip_self, ha2]; norm_num
  have hs3 : ip a3 a3 = (1/6 : ℂ) := by rw [ip_self, ha3]; norm_num
  have hs4 : ip a4 a4 = (1/6 : ℂ) := by rw [ip_self, ha4]; norm_num
  have hk1 : ip a1 u = 0 := by rw [← ip_star, hq1, star_zero]
  have hk2 : ip a2 u = 0 := by rw [← ip_star, hq2, star_zero]
  have hk3 : ip a3 u = 0 := by rw [← ip_star, hq3, star_zero]
  have hk4 : ip a4 u = 0 := by rw [← ip_star, hq4, star_zero]
  have hi0 := frame_idem a1 a2 a3 a4 ho12 ho13 ho14 ho21 ho23 ho24 ho31 ho32 ho34 ho41 ho42 ho43 hs1 hs2 hs3 hs4 0
  have hker0 := frame_kernel u a1 a2 a3 a4 hk1 hk2 hk3 hk4 0
  rw [mul_star, mul_star, mul_star, mul_star] at hi0
  push_cast at hi0
  have hi1 := frame_idem a1 a2 a3 a4 ho12 ho13 ho14 ho21 ho23 ho24 ho31 ho32 ho34 ho41 ho42 ho43 hs1 hs2 hs3 hs4 1
  have hker1 := frame_kernel u a1 a2 a3 a4 hk1 hk2 hk3 hk4 1
  rw [mul_star, mul_star, mul_star, mul_star] at hi1
  push_cast at hi1
  have hi2 := frame_idem a1 a2 a3 a4 ho12 ho13 ho14 ho21 ho23 ho24 ho31 ho32 ho34 ho41 ho42 ho43 hs1 hs2 hs3 hs4 2
  have hker2 := frame_kernel u a1 a2 a3 a4 hk1 hk2 hk3 hk4 2
  rw [mul_star, mul_star, mul_star, mul_star] at hi2
  push_cast at hi2
  have hi3 := frame_idem a1 a2 a3 a4 ho12 ho13 ho14 ho21 ho23 ho24 ho31 ho32 ho34 ho41 ho42 ho43 hs1 hs2 hs3 hs4 3
  have hker3 := frame_kernel u a1 a2 a3 a4 hk1 hk2 hk3 hk4 3
  rw [mul_star, mul_star, mul_star, mul_star] at hi3
  push_cast at hi3
  have hm0 : Complex.normSq (fr a1 a2 a3 a4 0 0) + Complex.normSq (fr a1 a2 a3 a4 0 1)
      + Complex.normSq (fr a1 a2 a3 a4 0 2) + Complex.normSq (fr a1 a2 a3 a4 0 3)
      = 1/6 * (Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0)
        + Complex.normSq (a4 0)) := by
    have h2 : ((Complex.normSq (fr a1 a2 a3 a4 0 0) + Complex.normSq (fr a1 a2 a3 a4 0 1)
        + Complex.normSq (fr a1 a2 a3 a4 0 2) + Complex.normSq (fr a1 a2 a3 a4 0 3)
        : Real) : ℂ) = ((1/6 * (Complex.normSq (a1 0) + Complex.normSq (a2 0)
          + Complex.normSq (a3 0) + Complex.normSq (a4 0)) : Real) : ℂ) := by
      push_cast
      linear_combination hi0
    exact_mod_cast h2
  have hw0 : Complex.normSq (fr a1 a2 a3 a4 0 0) = (Complex.normSq (a1 0) + Complex.normSq (a2 0)
        + Complex.normSq (a3 0) + Complex.normSq (a4 0)
      ) * (Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0)
        + Complex.normSq (a4 0)) := by
    rw [fr_diag, Complex.normSq_ofReal]
  have hm1 : Complex.normSq (fr a1 a2 a3 a4 1 0) + Complex.normSq (fr a1 a2 a3 a4 1 1)
      + Complex.normSq (fr a1 a2 a3 a4 1 2) + Complex.normSq (fr a1 a2 a3 a4 1 3)
      = 1/6 * (Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1)
        + Complex.normSq (a4 1)) := by
    have h2 : ((Complex.normSq (fr a1 a2 a3 a4 1 0) + Complex.normSq (fr a1 a2 a3 a4 1 1)
        + Complex.normSq (fr a1 a2 a3 a4 1 2) + Complex.normSq (fr a1 a2 a3 a4 1 3)
        : Real) : ℂ) = ((1/6 * (Complex.normSq (a1 1) + Complex.normSq (a2 1)
          + Complex.normSq (a3 1) + Complex.normSq (a4 1)) : Real) : ℂ) := by
      push_cast
      linear_combination hi1
    exact_mod_cast h2
  have hw1 : Complex.normSq (fr a1 a2 a3 a4 1 1) = (Complex.normSq (a1 1) + Complex.normSq (a2 1)
        + Complex.normSq (a3 1) + Complex.normSq (a4 1)
      ) * (Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1)
        + Complex.normSq (a4 1)) := by
    rw [fr_diag, Complex.normSq_ofReal]
  have hm2 : Complex.normSq (fr a1 a2 a3 a4 2 0) + Complex.normSq (fr a1 a2 a3 a4 2 1)
      + Complex.normSq (fr a1 a2 a3 a4 2 2) + Complex.normSq (fr a1 a2 a3 a4 2 3)
      = 1/6 * (Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2)
        + Complex.normSq (a4 2)) := by
    have h2 : ((Complex.normSq (fr a1 a2 a3 a4 2 0) + Complex.normSq (fr a1 a2 a3 a4 2 1)
        + Complex.normSq (fr a1 a2 a3 a4 2 2) + Complex.normSq (fr a1 a2 a3 a4 2 3)
        : Real) : ℂ) = ((1/6 * (Complex.normSq (a1 2) + Complex.normSq (a2 2)
          + Complex.normSq (a3 2) + Complex.normSq (a4 2)) : Real) : ℂ) := by
      push_cast
      linear_combination hi2
    exact_mod_cast h2
  have hw2 : Complex.normSq (fr a1 a2 a3 a4 2 2) = (Complex.normSq (a1 2) + Complex.normSq (a2 2)
        + Complex.normSq (a3 2) + Complex.normSq (a4 2)
      ) * (Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2)
        + Complex.normSq (a4 2)) := by
    rw [fr_diag, Complex.normSq_ofReal]
  have hm3 : Complex.normSq (fr a1 a2 a3 a4 3 0) + Complex.normSq (fr a1 a2 a3 a4 3 1)
      + Complex.normSq (fr a1 a2 a3 a4 3 2) + Complex.normSq (fr a1 a2 a3 a4 3 3)
      = 1/6 * (Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3)
        + Complex.normSq (a4 3)) := by
    have h2 : ((Complex.normSq (fr a1 a2 a3 a4 3 0) + Complex.normSq (fr a1 a2 a3 a4 3 1)
        + Complex.normSq (fr a1 a2 a3 a4 3 2) + Complex.normSq (fr a1 a2 a3 a4 3 3)
        : Real) : ℂ) = ((1/6 * (Complex.normSq (a1 3) + Complex.normSq (a2 3)
          + Complex.normSq (a3 3) + Complex.normSq (a4 3)) : Real) : ℂ) := by
      push_cast
      linear_combination hi3
    exact_mod_cast h2
  have hw3 : Complex.normSq (fr a1 a2 a3 a4 3 3) = (Complex.normSq (a1 3) + Complex.normSq (a2 3)
        + Complex.normSq (a3 3) + Complex.normSq (a4 3)
      ) * (Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3)
        + Complex.normSq (a4 3)) := by
    rw [fr_diag, Complex.normSq_ofReal]
  have hnn00 := Complex.normSq_nonneg (fr a1 a2 a3 a4 0 0)
  have hnn01 := Complex.normSq_nonneg (fr a1 a2 a3 a4 0 1)
  have hnn02 := Complex.normSq_nonneg (fr a1 a2 a3 a4 0 2)
  have hnn03 := Complex.normSq_nonneg (fr a1 a2 a3 a4 0 3)
  have hnn10 := Complex.normSq_nonneg (fr a1 a2 a3 a4 1 0)
  have hnn11 := Complex.normSq_nonneg (fr a1 a2 a3 a4 1 1)
  have hnn12 := Complex.normSq_nonneg (fr a1 a2 a3 a4 1 2)
  have hnn13 := Complex.normSq_nonneg (fr a1 a2 a3 a4 1 3)
  have hnn20 := Complex.normSq_nonneg (fr a1 a2 a3 a4 2 0)
  have hnn21 := Complex.normSq_nonneg (fr a1 a2 a3 a4 2 1)
  have hnn22 := Complex.normSq_nonneg (fr a1 a2 a3 a4 2 2)
  have hnn23 := Complex.normSq_nonneg (fr a1 a2 a3 a4 2 3)
  have hnn30 := Complex.normSq_nonneg (fr a1 a2 a3 a4 3 0)
  have hnn31 := Complex.normSq_nonneg (fr a1 a2 a3 a4 3 1)
  have hnn32 := Complex.normSq_nonneg (fr a1 a2 a3 a4 3 2)
  have hnn33 := Complex.normSq_nonneg (fr a1 a2 a3 a4 3 3)
  simp only [nsq] at ha1 ha2 ha3 ha4 hu
  have hqq0 : (Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0)
        + Complex.normSq (a4 0)
      ) * (Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0)
        + Complex.normSq (a4 0)) ≤ 1/6 * (
      Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0) + Complex.normSq (a4 0)) := by
    rw [← hw0, ← hm0]
    linarith [hnn01, hnn02, hnn03]
  have hle0 : (Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0)
        + Complex.normSq (a4 0)) ≤ 1/6 := mass_le hqq0
  have hqq1 : (Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1)
        + Complex.normSq (a4 1)
      ) * (Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1)
        + Complex.normSq (a4 1)) ≤ 1/6 * (
      Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1) + Complex.normSq (a4 1)) := by
    rw [← hw1, ← hm1]
    linarith [hnn10, hnn12, hnn13]
  have hle1 : (Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1)
        + Complex.normSq (a4 1)) ≤ 1/6 := mass_le hqq1
  have hqq2 : (Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2)
        + Complex.normSq (a4 2)
      ) * (Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2)
        + Complex.normSq (a4 2)) ≤ 1/6 * (
      Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2) + Complex.normSq (a4 2)) := by
    rw [← hw2, ← hm2]
    linarith [hnn20, hnn21, hnn23]
  have hle2 : (Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2)
        + Complex.normSq (a4 2)) ≤ 1/6 := mass_le hqq2
  have hqq3 : (Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3)
        + Complex.normSq (a4 3)
      ) * (Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3)
        + Complex.normSq (a4 3)) ≤ 1/6 * (
      Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3) + Complex.normSq (a4 3)) := by
    rw [← hw3, ← hm3]
    linarith [hnn30, hnn31, hnn32]
  have hle3 : (Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3)
        + Complex.normSq (a4 3)) ≤ 1/6 := mass_le hqq3
  have he0 : (Complex.normSq (a1 0) + Complex.normSq (a2 0) + Complex.normSq (a3 0)
        + Complex.normSq (a4 0)) = 1/6 := by linarith
  have he1 : (Complex.normSq (a1 1) + Complex.normSq (a2 1) + Complex.normSq (a3 1)
        + Complex.normSq (a4 1)) = 1/6 := by linarith
  have he2 : (Complex.normSq (a1 2) + Complex.normSq (a2 2) + Complex.normSq (a3 2)
        + Complex.normSq (a4 2)) = 1/6 := by linarith
  have he3 : (Complex.normSq (a1 3) + Complex.normSq (a2 3) + Complex.normSq (a3 3)
        + Complex.normSq (a4 3)) = 1/6 := by linarith
  rw [he0] at hm0 hw0
  rw [he1] at hm1 hw1
  rw [he2] at hm2 hw2
  rw [he3] at hm3 hw3
  have hzz0 : fr a1 a2 a3 a4 0 0 = ((1/6 : Real) : ℂ) := by rw [fr_diag, he0]
  have hzo01 : fr a1 a2 a3 a4 0 1 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw0, hm0, hnn00, hnn02, hnn03])
  have hzo02 : fr a1 a2 a3 a4 0 2 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw0, hm0, hnn00, hnn01, hnn03])
  have hzo03 : fr a1 a2 a3 a4 0 3 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw0, hm0, hnn00, hnn01, hnn02])
  have hzz1 : fr a1 a2 a3 a4 1 1 = ((1/6 : Real) : ℂ) := by rw [fr_diag, he1]
  have hzo10 : fr a1 a2 a3 a4 1 0 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw1, hm1, hnn11, hnn12, hnn13])
  have hzo12 : fr a1 a2 a3 a4 1 2 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw1, hm1, hnn10, hnn11, hnn13])
  have hzo13 : fr a1 a2 a3 a4 1 3 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw1, hm1, hnn10, hnn11, hnn12])
  have hzz2 : fr a1 a2 a3 a4 2 2 = ((1/6 : Real) : ℂ) := by rw [fr_diag, he2]
  have hzo20 : fr a1 a2 a3 a4 2 0 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw2, hm2, hnn21, hnn22, hnn23])
  have hzo21 : fr a1 a2 a3 a4 2 1 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw2, hm2, hnn20, hnn22, hnn23])
  have hzo23 : fr a1 a2 a3 a4 2 3 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw2, hm2, hnn20, hnn21, hnn22])
  have hzz3 : fr a1 a2 a3 a4 3 3 = ((1/6 : Real) : ℂ) := by rw [fr_diag, he3]
  have hzo30 : fr a1 a2 a3 a4 3 0 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw3, hm3, hnn31, hnn32, hnn33])
  have hzo31 : fr a1 a2 a3 a4 3 1 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw3, hm3, hnn30, hnn32, hnn33])
  have hzo32 : fr a1 a2 a3 a4 3 2 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [hw3, hm3, hnn30, hnn31, hnn33])
  have hux0 : u 0 = 0 := by
    have h := hker0
    rw [hzz0, hzo01, hzo02, hzo03] at h
    push_cast at h
    linear_combination 6 * h
  have hux1 : u 1 = 0 := by
    have h := hker1
    rw [hzz1, hzo10, hzo12, hzo13] at h
    push_cast at h
    linear_combination 6 * h
  have hux2 : u 2 = 0 := by
    have h := hker2
    rw [hzz2, hzo20, hzo21, hzo23] at h
    push_cast at h
    linear_combination 6 * h
  have hux3 : u 3 = 0 := by
    have h := hker3
    rw [hzz3, hzo30, hzo31, hzo32] at h
    push_cast at h
    linear_combination 6 * h
  rw [hux0, hux1, hux2, hux3] at hu
  simp at hu

/-! ## The trace contradiction -/

/-- **The trace contradiction.**  Four bottom vectors and four top vectors of
`ℂ⁴`, all of squared norm `1/6`, with a common frame operator, all orthogonal
to an anchor `u` of squared norm `1/3`, and with `aᵢ†bⱼ = 0` off the diagonal,
cannot exist. -/
theorem bell_contradiction (u a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)
    (hu : nsq u = 1/3)
    (ha1 : nsq a1 = 1/6) (ha2 : nsq a2 = 1/6) (ha3 : nsq a3 = 1/6) (ha4 : nsq a4 = 1/6)
    (hb1 : nsq b1 = 1/6) (hb2 : nsq b2 = 1/6) (hb3 : nsq b3 = 1/6) (hb4 : nsq b4 = 1/6)
    (hq1 : ip u a1 = 0) (hq2 : ip u a2 = 0) (hq3 : ip u a3 = 0) (hq4 : ip u a4 = 0)
    (hf : ∀ k l : Fin 4, fr a1 a2 a3 a4 k l = fr b1 b2 b3 b4 k l)
    (hx12 : ip a1 b2 = 0)
    (hx13 : ip a1 b3 = 0)
    (hx14 : ip a1 b4 = 0)
    (hx21 : ip a2 b1 = 0)
    (hx23 : ip a2 b3 = 0)
    (hx24 : ip a2 b4 = 0)
    (hx31 : ip a3 b1 = 0)
    (hx32 : ip a3 b2 = 0)
    (hx34 : ip a3 b4 = 0)
    (hx41 : ip a4 b1 = 0)
    (hx42 : ip a4 b2 = 0)
    (hx43 : ip a4 b3 = 0)
    : False := by
  have swap := frame_swap a1 a2 a3 a4 b1 b2 b3 b4 hf
  rw [ip_mul_ip a1 a1 , ip_mul_ip a1 a2 , ip_mul_ip a1 a3 , ip_mul_ip a1 a4 , ip_mul_ip a2 a1
    , ip_mul_ip a2 a2 , ip_mul_ip a2 a3 , ip_mul_ip a2 a4 , ip_mul_ip a3 a1 , ip_mul_ip a3 a2
    , ip_mul_ip a3 a3 , ip_mul_ip a3 a4 , ip_mul_ip a4 a1 , ip_mul_ip a4 a2 , ip_mul_ip a4 a3
    , ip_mul_ip a4 a4 , ip_mul_ip a1 b1 , ip_mul_ip a1 b2 , ip_mul_ip a1 b3 , ip_mul_ip a1 b4
    , ip_mul_ip a2 b1 , ip_mul_ip a2 b2 , ip_mul_ip a2 b3 , ip_mul_ip a2 b4 , ip_mul_ip a3 b1
    , ip_mul_ip a3 b2 , ip_mul_ip a3 b3 , ip_mul_ip a3 b4 , ip_mul_ip a4 b1 , ip_mul_ip a4 b2
    , ip_mul_ip a4 b3 , ip_mul_ip a4 b4] at swap
  have swapR : (Complex.normSq (ip a1 a1) + Complex.normSq (ip a1 a2) + Complex.normSq (ip a1 a3)
      + Complex.normSq (ip a1 a4) + Complex.normSq (ip a2 a1) + Complex.normSq (ip a2 a2)
      + Complex.normSq (ip a2 a3) + Complex.normSq (ip a2 a4) + Complex.normSq (ip a3 a1)
      + Complex.normSq (ip a3 a2) + Complex.normSq (ip a3 a3) + Complex.normSq (ip a3 a4)
      + Complex.normSq (ip a4 a1) + Complex.normSq (ip a4 a2) + Complex.normSq (ip a4 a3)
      + Complex.normSq (ip a4 a4)
      ) = (Complex.normSq (ip a1 b1) + Complex.normSq (ip a1 b2) + Complex.normSq (ip a1 b3)
      + Complex.normSq (ip a1 b4) + Complex.normSq (ip a2 b1) + Complex.normSq (ip a2 b2)
      + Complex.normSq (ip a2 b3) + Complex.normSq (ip a2 b4) + Complex.normSq (ip a3 b1)
      + Complex.normSq (ip a3 b2) + Complex.normSq (ip a3 b3) + Complex.normSq (ip a3 b4)
      + Complex.normSq (ip a4 b1) + Complex.normSq (ip a4 b2) + Complex.normSq (ip a4 b3)
      + Complex.normSq (ip a4 b4)) := by
    exact_mod_cast swap
  have hd1 : Complex.normSq (ip a1 a1) = 1/36 := by
    rw [ip_self, ha1, Complex.normSq_ofReal]; norm_num
  have hd2 : Complex.normSq (ip a2 a2) = 1/36 := by
    rw [ip_self, ha2, Complex.normSq_ofReal]; norm_num
  have hd3 : Complex.normSq (ip a3 a3) = 1/36 := by
    rw [ip_self, ha3, Complex.normSq_ofReal]; norm_num
  have hd4 : Complex.normSq (ip a4 a4) = 1/36 := by
    rw [ip_self, ha4, Complex.normSq_ofReal]; norm_num
  have hy12 : Complex.normSq (ip a1 b2) = 0 := by rw [hx12]; simp
  have hy13 : Complex.normSq (ip a1 b3) = 0 := by rw [hx13]; simp
  have hy14 : Complex.normSq (ip a1 b4) = 0 := by rw [hx14]; simp
  have hy21 : Complex.normSq (ip a2 b1) = 0 := by rw [hx21]; simp
  have hy23 : Complex.normSq (ip a2 b3) = 0 := by rw [hx23]; simp
  have hy24 : Complex.normSq (ip a2 b4) = 0 := by rw [hx24]; simp
  have hy31 : Complex.normSq (ip a3 b1) = 0 := by rw [hx31]; simp
  have hy32 : Complex.normSq (ip a3 b2) = 0 := by rw [hx32]; simp
  have hy34 : Complex.normSq (ip a3 b4) = 0 := by rw [hx34]; simp
  have hy41 : Complex.normSq (ip a4 b1) = 0 := by rw [hx41]; simp
  have hy42 : Complex.normSq (ip a4 b2) = 0 := by rw [hx42]; simp
  have hy43 : Complex.normSq (ip a4 b3) = 0 := by rw [hx43]; simp
  have hc1 := cs a1 b1
  rw [ha1, hb1] at hc1
  have hc2 := cs a2 b2
  rw [ha2, hb2] at hc2
  have hc3 := cs a3 b3
  rw [ha3, hb3] at hc3
  have hc4 := cs a4 b4
  rw [ha4, hb4] at hc4
  have hg12 := Complex.normSq_nonneg (ip a1 a2)
  have hg13 := Complex.normSq_nonneg (ip a1 a3)
  have hg14 := Complex.normSq_nonneg (ip a1 a4)
  have hg21 := Complex.normSq_nonneg (ip a2 a1)
  have hg23 := Complex.normSq_nonneg (ip a2 a3)
  have hg24 := Complex.normSq_nonneg (ip a2 a4)
  have hg31 := Complex.normSq_nonneg (ip a3 a1)
  have hg32 := Complex.normSq_nonneg (ip a3 a2)
  have hg34 := Complex.normSq_nonneg (ip a3 a4)
  have hg41 := Complex.normSq_nonneg (ip a4 a1)
  have hg42 := Complex.normSq_nonneg (ip a4 a2)
  have hg43 := Complex.normSq_nonneg (ip a4 a3)
  have ho12 : ip a1 a2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho13 : ip a1 a3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho14 : ip a1 a4 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho21 : ip a2 a1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho23 : ip a2 a3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho24 : ip a2 a4 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho31 : ip a3 a1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho32 : ip a3 a2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho34 : ip a3 a4 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho41 : ip a4 a1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho42 : ip a4 a2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have ho43 : ip a4 a3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  exact orthogonal_overflow u a1 a2 a3 a4 hu ha1 ha2 ha3 ha4 hq1 hq2 hq3 hq4
    ho12 ho13 ho14 ho21 ho23 ho24 ho31 ho32 ho34 ho41 ho42 ho43

end

end SixQubit.Trace5
