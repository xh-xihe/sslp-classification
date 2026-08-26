import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Trace5

set_option maxHeartbeats 4000000

/-!
# The two-qubit flip-kernel dichotomy for orbit 5

Orbit 5 has two zero-angle qubits, so each active tail carries a vector of
`C^4`, which we read as a `2 x 2` coefficient matrix by `x k` with
`k = 2 * (first bit) + (second bit)`.  Writing `U`, `A`, `B` for the matrices
of the anchor `u` and of a matching pair `a_i`, `b_i`, every one-qubit
operator `F` on either tensor factor gives an error `F X_i` of weight at most
two, so the Knill--Laflamme rows say

```
  B U^dag + V A^dag = 0 ,        U^dag B + A^dag V = 0 ,
```

with `V` the matrix of the top anchor `v`.  This file works those two matrix
equations out in raw coordinates: no Schmidt form, no normalisation, no
matrices are ever built -- every statement is a polynomial identity in the
sixteen scalars `u k`, `star (u k)`, `x k`, `star (x k)`.

The mechanism is the following chain, all of it division free.

* `interlace_b` / `interlace_a`.  Eliminating `B` between the two rows gives
  `A M = N A` and `B M = N B` for `M = U^dag U` and `N = U U^dag`; the two
  certificates are single `linear_combination`s with coefficients `u j`.

* `line`.  For `X` intertwining `M` and `N` and orthogonal to `u`, the
  polarisation identity `X adj(Y) + Y adj(X) = <X,Y> I` for `2 x 2` matrices
  turns the intertwining into `(2N - tau) X = - <X,U> adj(U^dag)`, and squaring
  `2N - tau` (whose square is the discriminant `Del` times the identity)
  yields the explicit projection

  ```
     Del * X  =  <X,U> * W ,      W = tau * adj(U^dag) - 2 * conj(det U) * U .
  ```

  So off the branch locus `Del = 0` every solution sits on the single line
  spanned by `W`.  This is branch (i) of the paper's dichotomy, with the branch
  polynomial made explicit: `Del u = (nsq u)^2 - 4 * normSq (det U)`.

* `bell_data`.  On the branch locus, `Del = 0` forces `U^dag U = 1/6` times the
  identity (`Del` is a sum of two squares, `Del_split`), and then `bell_sym`
  shows `ip a b' = ip a' b`, which together with the two-flip relation kills
  every cross inner product.  This is branch (ii).

`native_decide` is not used, and no bit strings are mentioned.
-/

namespace SixQubit.Kernel5

open scoped ComplexConjugate

open SixQubit.Trace5

noncomputable section

/-! ## The branch data -/

/-- The determinant of the `2 x 2` coefficient matrix of `u`. -/
def dt (u : Fin 4 -> ℂ) : ℂ := u 0 * u 3 - u 1 * u 2

/-- The squared norm of `u` as a complex polynomial in the coordinates. -/
def tw (u : Fin 4 -> ℂ) : ℂ :=
  star (u 0) * u 0 + star (u 1) * u 1 + star (u 2) * u 2 + star (u 3) * u 3

/-- **The branch polynomial**: the discriminant of the characteristic
polynomial of `U^dag U`.  It vanishes exactly on the Bell branch. -/
def Del (u : Fin 4 -> ℂ) : Real := nsq u * nsq u - 4 * Complex.normSq (dt u)

/-- The line vector `W = tau * adj(U^dag) - 2 * conj(det U) * U`. -/
def WW (u : Fin 4 -> ℂ) : Fin 4 -> ℂ :=
  ![tw u * star (u 3) - 2 * star (dt u) * u 0,
    -(tw u * star (u 2)) - 2 * star (dt u) * u 1,
    -(tw u * star (u 1)) - 2 * star (dt u) * u 2,
    tw u * star (u 0) - 2 * star (dt u) * u 3]

/-- The coordinate `<x, U>` of `x` in the determinant pairing. -/
def gg (u x : Fin 4 -> ℂ) : ℂ := x 0 * u 3 - x 1 * u 2 - x 2 * u 1 + x 3 * u 0

@[simp] theorem WW_0 (u : Fin 4 -> ℂ) :
    WW u 0 = tw u * star (u 3) - 2 * star (dt u) * u 0 := rfl
@[simp] theorem WW_1 (u : Fin 4 -> ℂ) :
    WW u 1 = -(tw u * star (u 2)) - 2 * star (dt u) * u 1 := rfl
@[simp] theorem WW_2 (u : Fin 4 -> ℂ) :
    WW u 2 = -(tw u * star (u 1)) - 2 * star (dt u) * u 2 := rfl
@[simp] theorem WW_3 (u : Fin 4 -> ℂ) :
    WW u 3 = tw u * star (u 0) - 2 * star (dt u) * u 3 := rfl

theorem tw_eq (u : Fin 4 -> ℂ) : tw u = ((nsq u : Real) : ℂ) := by
  simp only [tw, nsq, SixQubit.star_mul_self]
  push_cast
  ring

theorem Del_eq (u : Fin 4 -> ℂ) :
    ((Del u : Real) : ℂ) = tw u * tw u - 4 * (dt u * star (dt u)) := by
  have h : ((Del u : Real) : ℂ)
      = ((nsq u : Real) : ℂ) * ((nsq u : Real) : ℂ)
        - 4 * ((Complex.normSq (dt u) : Real) : ℂ) := by
    simp only [Del]
    push_cast
    ring
  rw [h, ← tw_eq, ← SixQubit.star_mul_self]
  ring

/-! ## The intertwining relation and the line

`M = U^dag U` and `N = U U^dag`; the four hypotheses `hk r s` are the entries
of `X M = N X`. -/

/-- **The projection onto the line.**  A solution of the intertwining
relation that is orthogonal to `u` is `Del`-proportional to `WW u`. -/
theorem line (u x : Fin 4 -> ℂ)
    (hk00 : x 0 * (star (u 0) * u 0 + star (u 2) * u 2) + x 1 * (star (u 1) * u 0 + star (u 3) * u 2)
        = (u 0 * star (u 0) + u 1 * star (u 1)) * x 0 + (u 0 * star (u 2) + u 1 * star (u 3)) * x 2)
    (hk01 : x 0 * (star (u 0) * u 1 + star (u 2) * u 3) + x 1 * (star (u 1) * u 1 + star (u 3) * u 3)
        = (u 0 * star (u 0) + u 1 * star (u 1)) * x 1 + (u 0 * star (u 2) + u 1 * star (u 3)) * x 3)
    (hk10 : x 2 * (star (u 0) * u 0 + star (u 2) * u 2) + x 3 * (star (u 1) * u 0 + star (u 3) * u 2)
        = (u 2 * star (u 0) + u 3 * star (u 1)) * x 0 + (u 2 * star (u 2) + u 3 * star (u 3)) * x 2)
    (hk11 : x 2 * (star (u 0) * u 1 + star (u 2) * u 3) + x 3 * (star (u 1) * u 1 + star (u 3) * u 3)
        = (u 2 * star (u 0) + u 3 * star (u 1)) * x 1 + (u 2 * star (u 2) + u 3 * star (u 3)) * x 3)
    (ho : ip u x = 0) :
    ((Del u : Real) : ℂ) * x 0 = gg u x * WW u 0 ∧
      ((Del u : Real) : ℂ) * x 1 = gg u x * WW u 1 ∧
      ((Del u : Real) : ℂ) * x 2 = gg u x * WW u 2 ∧
      ((Del u : Real) : ℂ) * x 3 = gg u x * WW u 3 := by
  simp only [ip] at ho
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Del_eq] <;>
    simp only [WW_0, WW_1, WW_2, WW_3, tw, dt, gg, star_sub, star_mul']
  · linear_combination (-(star (u 0))*(u 0) - (star (u 1))*(u 1) + (star (u 2))*(u 2) + (star (u 3))*(u 3)) * hk00
      + (-2*(star (u 2))*(u 0) - 2*(star (u 3))*(u 1)) * hk10 + ((star (u 0))*(u 0)^2 + (star (u 1))*(u 0)*(u 1) + (star (u 2))*(u 0)*(u 2) - (star (u 3))*(u 0)*(u 3) + 2*(star (u 3))*(u 1)*(u 2)) * ho
  · linear_combination (-(star (u 0))*(u 0) - (star (u 1))*(u 1) + (star (u 2))*(u 2) + (star (u 3))*(u 3)) * hk01
      + (-2*(star (u 2))*(u 0) - 2*(star (u 3))*(u 1)) * hk11 + ((star (u 0))*(u 0)*(u 1) + (star (u 1))*(u 1)^2 + 2*(star (u 2))*(u 0)*(u 3) - (star (u 2))*(u 1)*(u 2) + (star (u 3))*(u 1)*(u 3)) * ho
  · linear_combination (-2*(star (u 0))*(u 2) - 2*(star (u 1))*(u 3)) * hk00
      + ((star (u 0))*(u 0) + (star (u 1))*(u 1) - (star (u 2))*(u 2) - (star (u 3))*(u 3)) * hk10 + ((star (u 0))*(u 0)*(u 2) + 2*(star (u 1))*(u 0)*(u 3) - (star (u 1))*(u 1)*(u 2) + (star (u 2))*(u 2)^2 + (star (u 3))*(u 2)*(u 3)) * ho
  · linear_combination (-2*(star (u 0))*(u 2) - 2*(star (u 1))*(u 3)) * hk01
      + ((star (u 0))*(u 0) + (star (u 1))*(u 1) - (star (u 2))*(u 2) - (star (u 3))*(u 3)) * hk11 + (-(star (u 0))*(u 0)*(u 3) + 2*(star (u 0))*(u 1)*(u 2) + (star (u 1))*(u 1)*(u 3) + (star (u 2))*(u 2)*(u 3) + (star (u 3))*(u 3)^2) * ho

/-- `x` lies on the line spanned by `WW u`, with the factor `Del u` cleared. -/
def OnLine (u x : Fin 4 -> ℂ) : Prop :=
  ∀ k : Fin 4, ((Del u : Real) : ℂ) * x k = gg u x * WW u k

/-- Package the four coordinate identities produced by `line` as `OnLine`. -/
theorem onLine_of {u x : Fin 4 -> ℂ}
    (h : ((Del u : Real) : ℂ) * x 0 = gg u x * WW u 0 ∧
      ((Del u : Real) : ℂ) * x 1 = gg u x * WW u 1 ∧
      ((Del u : Real) : ℂ) * x 2 = gg u x * WW u 2 ∧
      ((Del u : Real) : ℂ) * x 3 = gg u x * WW u 3) : OnLine u x := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro k
  fin_cases k
  exacts [h0, h1, h2, h3]

/-- The squared norm of the line vector is `nsq u * Del u`; in particular it is
positive exactly off the branch locus. -/
theorem nsq_WW (u : Fin 4 -> ℂ) : nsq (WW u) = nsq u * Del u := by
  have h : ((nsq (WW u) : Real) : ℂ)
      = ((nsq u : Real) : ℂ) * ((Del u : Real) : ℂ) := by
    rw [← ip_self, ← tw_eq, Del_eq]
    simp only [ip, WW_0, WW_1, WW_2, WW_3, tw, dt, star_sub, star_add, star_neg,
      star_mul', star_star, star_ofNat]
    ring
  have h2 : ((nsq u * Del u : Real) : ℂ)
      = ((nsq u : Real) : ℂ) * ((Del u : Real) : ℂ) := by push_cast; ring
  exact_mod_cast h.trans h2.symm

/-- `Del` is a sum of two squares: the branch locus is exactly the locus where
`U^dag U` is a scalar. -/
theorem Del_split (u : Fin 4 -> ℂ) :
    Del u = (Complex.normSq (u 0) + Complex.normSq (u 2)
        - Complex.normSq (u 1) - Complex.normSq (u 3))
      * (Complex.normSq (u 0) + Complex.normSq (u 2)
        - Complex.normSq (u 1) - Complex.normSq (u 3))
      + 4 * Complex.normSq (star (u 0) * u 1 + star (u 2) * u 3) := by
  have h : ((Del u : Real) : ℂ)
      = (((Complex.normSq (u 0) + Complex.normSq (u 2)
        - Complex.normSq (u 1) - Complex.normSq (u 3))
      * (Complex.normSq (u 0) + Complex.normSq (u 2)
        - Complex.normSq (u 1) - Complex.normSq (u 3))
      + 4 * Complex.normSq (star (u 0) * u 1 + star (u 2) * u 3) : Real) : ℂ) := by
    rw [Del_eq]
    simp only [tw, dt]
    push_cast [← SixQubit.star_mul_self]
    simp only [star_add, star_sub, star_mul', star_star]
    ring
  exact_mod_cast h

/-- The branch polynomial is a sum of two squares, hence nonnegative. -/
theorem Del_nonneg (u : Fin 4 -> ℂ) : (0 : Real) ≤ Del u := by
  have hsp := Del_split u
  nlinarith [Complex.normSq_nonneg (star (u 0) * u 1 + star (u 2) * u 3),
    mul_self_nonneg (Complex.normSq (u 0) + Complex.normSq (u 2)
      - Complex.normSq (u 1) - Complex.normSq (u 3))]

/-- **On the branch locus** `U^dag U` is `1/6` times the identity. -/
theorem bell_data (u : Fin 4 -> ℂ) (hu : nsq u = 1/3) (hd : Del u = 0) :
    star (u 0) * u 0 + star (u 2) * u 2 = 1/6 ∧
      star (u 0) * u 1 + star (u 2) * u 3 = 0 ∧
      star (u 1) * u 0 + star (u 3) * u 2 = 0 ∧
      star (u 1) * u 1 + star (u 3) * u 3 = 1/6 := by
  have hsplit := Del_split u
  rw [hd] at hsplit
  have hnn := Complex.normSq_nonneg (star (u 0) * u 1 + star (u 2) * u 3)
  have hz : Complex.normSq (star (u 0) * u 1 + star (u 2) * u 3) = 0 := by nlinarith
  have hdiff : Complex.normSq (u 0) + Complex.normSq (u 2)
      - Complex.normSq (u 1) - Complex.normSq (u 3) = 0 := by nlinarith
  have hsum : Complex.normSq (u 0) + Complex.normSq (u 1) + Complex.normSq (u 2)
      + Complex.normSq (u 3) = 1/3 := by
    simpa [nsq] using hu
  have h02 : Complex.normSq (u 0) + Complex.normSq (u 2) = 1/6 := by linarith
  have h13 : Complex.normSq (u 1) + Complex.normSq (u 3) = 1/6 := by linarith
  have e01 : star (u 0) * u 1 + star (u 2) * u 3 = 0 := Complex.normSq_eq_zero.mp hz
  refine ⟨?_, e01, ?_, ?_⟩
  · rw [SixQubit.star_mul_self, SixQubit.star_mul_self]
    have : ((Complex.normSq (u 0) + Complex.normSq (u 2) : Real) : ℂ) = ((1/6 : Real) : ℂ) := by
      exact_mod_cast congrArg (fun t : Real => (t : ℂ)) h02
    push_cast at this ⊢
    linear_combination this
  · have := congrArg star e01
    simp only [star_add, star_mul', star_star, star_zero] at this
    linear_combination this
  · rw [SixQubit.star_mul_self, SixQubit.star_mul_self]
    have : ((Complex.normSq (u 1) + Complex.normSq (u 3) : Real) : ℂ) = ((1/6 : Real) : ℂ) := by
      exact_mod_cast congrArg (fun t : Real => (t : ℂ)) h13
    push_cast at this ⊢
    linear_combination this

/-! ## The Gram consequence of the line -/

/-- Two vectors on the line have their inner product determined by their two
coordinates along `WW u`. -/
theorem gram (u p q : Fin 4 -> ℂ) (hp : OnLine u p) (hq : OnLine u q) :
    ((Del u : Real) : ℂ) * (((Del u : Real) : ℂ) * ip p q)
      = star (gg u p) * (gg u q * ip (WW u) (WW u)) := by
  have ha0 := hp 0
  have ha1 := hp 1
  have ha2 := hp 2
  have ha3 := hp 3
  have hb0 := hq 0
  have hb1 := hq 1
  have hb2 := hq 2
  have hb3 := hq 3
  have hr : star (((Del u : Real) : ℂ)) = ((Del u : Real) : ℂ) := by simp
  have s0 := congrArg star ha0
  have s1 := congrArg star ha1
  have s2 := congrArg star ha2
  have s3 := congrArg star ha3
  simp only [star_mul', hr] at s0 s1 s2 s3
  simp only [ip]
  linear_combination (((Del u : Real) : ℂ) * q 0) * s0
    + (((Del u : Real) : ℂ) * q 1) * s1
    + (((Del u : Real) : ℂ) * q 2) * s2
    + (((Del u : Real) : ℂ) * q 3) * s3
    + (star (gg u p) * star (WW u 0)) * hb0
    + (star (gg u p) * star (WW u 1)) * hb1
    + (star (gg u p) * star (WW u 2)) * hb2
    + (star (gg u p) * star (WW u 3)) * hb3

/-- The squared modulus of the line coordinate of a vector on the line is
determined by its squared norm. -/
theorem gg_normSq (u p : Fin 4 -> ℂ) (hp : OnLine u p) :
    Del u * Del u * nsq p = Complex.normSq (gg u p) * (nsq u * Del u) := by
  have hg := gram u p p hp hp
  rw [ip_self, ip_self, nsq_WW] at hg
  have hc : ((Del u * Del u * nsq p : Real) : ℂ)
      = ((Complex.normSq (gg u p) * (nsq u * Del u) : Real) : ℂ) := by
    push_cast at hg ⊢
    rw [← SixQubit.star_mul_self (gg u p)]
    linear_combination hg
  exact_mod_cast hc

/-- Off the branch locus the line vector is nonzero. -/
theorem WW_ne (u : Fin 4 -> ℂ) (hu : nsq u = 1/3) (hD : (0 : Real) < Del u) :
    ip (WW u) (WW u) ≠ 0 := by
  have hp3 : (0 : Real) < nsq u * Del u := by rw [hu]; linarith
  rw [ip_self, nsq_WW]
  exact_mod_cast hp3.ne'

/-- Off the branch locus, a vector of the line with positive squared norm has a
nonzero line coordinate. -/
theorem gg_pos (u p : Fin 4 -> ℂ) (hp : OnLine u p) (hu : nsq u = 1/3)
    (hnp : nsq p = 1/6) (hD : (0 : Real) < Del u) :
    (0 : Real) < Complex.normSq (gg u p) := by
  have hn := gg_normSq u p hp
  rw [hnp, hu] at hn
  nlinarith [hn, hD, mul_pos hD hD, Complex.normSq_nonneg (gg u p)]

/-- **The two-flip relation on the line.**  A reciprocal relation between two
bottom and two top vectors of the line descends to their line coordinates. -/
theorem gg_flip (u p q p' q' : Fin 4 -> ℂ) (hW : ip (WW u) (WW u) ≠ 0)
    (hp : OnLine u p) (hq' : OnLine u q') (hp' : OnLine u p') (hq : OnLine u q)
    (htw : ip p q' + ip p' q = 0) :
    star (gg u p) * gg u q' + star (gg u p') * gg u q = 0 := by
  have g1 := gram u p q' hp hq'
  have g2 := gram u p' q hp' hq
  have h : (star (gg u p) * gg u q' + star (gg u p') * gg u q) * ip (WW u) (WW u) = 0 := by
    linear_combination -g1 - g2
      + (((Del u : Real) : ℂ) * ((Del u : Real) : ℂ)) * htw
  exact (mul_eq_zero.mp h).resolve_right hW

/-! ## From the Knill--Laflamme rows to the intertwining relation -/

/-- **The top vectors intertwine.**  `B M = N B`. -/
theorem interlace_b (u a b : Fin 4 -> ℂ) (zt : ℂ)
    (hP00 : b 0 * star (u 0) + b 1 * star (u 1) + zt * (u 0 * star (a 0) + u 1 * star (a 1)) = 0)
    (hP01 : b 0 * star (u 2) + b 1 * star (u 3) + zt * (u 0 * star (a 2) + u 1 * star (a 3)) = 0)
    (hP10 : b 2 * star (u 0) + b 3 * star (u 1) + zt * (u 2 * star (a 0) + u 3 * star (a 1)) = 0)
    (hP11 : b 2 * star (u 2) + b 3 * star (u 3) + zt * (u 2 * star (a 2) + u 3 * star (a 3)) = 0)
    (hQ00 : star (u 0) * b 0 + star (u 2) * b 2 + zt * (star (a 0) * u 0 + star (a 2) * u 2) = 0)
    (hQ01 : star (u 0) * b 1 + star (u 2) * b 3 + zt * (star (a 0) * u 1 + star (a 2) * u 3) = 0)
    (hQ10 : star (u 1) * b 0 + star (u 3) * b 2 + zt * (star (a 1) * u 0 + star (a 3) * u 2) = 0)
    (hQ11 : star (u 1) * b 1 + star (u 3) * b 3 + zt * (star (a 1) * u 1 + star (a 3) * u 3) = 0)
    :
    b 0 * (star (u 0) * u 0 + star (u 2) * u 2) + b 1 * (star (u 1) * u 0 + star (u 3) * u 2)
        = (u 0 * star (u 0) + u 1 * star (u 1)) * b 0 + (u 0 * star (u 2) + u 1 * star (u 3)) * b 2 ∧
      b 0 * (star (u 0) * u 1 + star (u 2) * u 3) + b 1 * (star (u 1) * u 1 + star (u 3) * u 3)
        = (u 0 * star (u 0) + u 1 * star (u 1)) * b 1 + (u 0 * star (u 2) + u 1 * star (u 3)) * b 3 ∧
      b 2 * (star (u 0) * u 0 + star (u 2) * u 2) + b 3 * (star (u 1) * u 0 + star (u 3) * u 2)
        = (u 2 * star (u 0) + u 3 * star (u 1)) * b 0 + (u 2 * star (u 2) + u 3 * star (u 3)) * b 2 ∧
      b 2 * (star (u 0) * u 1 + star (u 2) * u 3) + b 3 * (star (u 1) * u 1 + star (u 3) * u 3)
        = (u 2 * star (u 0) + u 3 * star (u 1)) * b 1 + (u 2 * star (u 2) + u 3 * star (u 3)) * b 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination ((u 0)) * hP00 + ((u 2)) * hP01
      + (-(u 0)) * hQ00 + (-(u 1)) * hQ10
  · linear_combination ((u 1)) * hP00 + ((u 3)) * hP01
      + (-(u 0)) * hQ01 + (-(u 1)) * hQ11
  · linear_combination ((u 0)) * hP10 + ((u 2)) * hP11
      + (-(u 2)) * hQ00 + (-(u 3)) * hQ10
  · linear_combination ((u 1)) * hP10 + ((u 3)) * hP11
      + (-(u 2)) * hQ01 + (-(u 3)) * hQ11

/-- **The bottom vectors intertwine.**  `A M = N A`. -/
theorem interlace_a (u a b : Fin 4 -> ℂ) (zt : ℂ) (hz : star zt * zt = 1)
    (hP00 : b 0 * star (u 0) + b 1 * star (u 1) + zt * (u 0 * star (a 0) + u 1 * star (a 1)) = 0)
    (hP01 : b 0 * star (u 2) + b 1 * star (u 3) + zt * (u 0 * star (a 2) + u 1 * star (a 3)) = 0)
    (hP10 : b 2 * star (u 0) + b 3 * star (u 1) + zt * (u 2 * star (a 0) + u 3 * star (a 1)) = 0)
    (hP11 : b 2 * star (u 2) + b 3 * star (u 3) + zt * (u 2 * star (a 2) + u 3 * star (a 3)) = 0)
    (hQ00 : star (u 0) * b 0 + star (u 2) * b 2 + zt * (star (a 0) * u 0 + star (a 2) * u 2) = 0)
    (hQ01 : star (u 0) * b 1 + star (u 2) * b 3 + zt * (star (a 0) * u 1 + star (a 2) * u 3) = 0)
    (hQ10 : star (u 1) * b 0 + star (u 3) * b 2 + zt * (star (a 1) * u 0 + star (a 3) * u 2) = 0)
    (hQ11 : star (u 1) * b 1 + star (u 3) * b 3 + zt * (star (a 1) * u 1 + star (a 3) * u 3) = 0)
    :
    a 0 * (star (u 0) * u 0 + star (u 2) * u 2) + a 1 * (star (u 1) * u 0 + star (u 3) * u 2)
        = (u 0 * star (u 0) + u 1 * star (u 1)) * a 0 + (u 0 * star (u 2) + u 1 * star (u 3)) * a 2 ∧
      a 0 * (star (u 0) * u 1 + star (u 2) * u 3) + a 1 * (star (u 1) * u 1 + star (u 3) * u 3)
        = (u 0 * star (u 0) + u 1 * star (u 1)) * a 1 + (u 0 * star (u 2) + u 1 * star (u 3)) * a 3 ∧
      a 2 * (star (u 0) * u 0 + star (u 2) * u 2) + a 3 * (star (u 1) * u 0 + star (u 3) * u 2)
        = (u 2 * star (u 0) + u 3 * star (u 1)) * a 0 + (u 2 * star (u 2) + u 3 * star (u 3)) * a 2 ∧
      a 2 * (star (u 0) * u 1 + star (u 2) * u 3) + a 3 * (star (u 1) * u 1 + star (u 3) * u 3)
        = (u 2 * star (u 0) + u 3 * star (u 1)) * a 1 + (u 2 * star (u 2) + u 3 * star (u 3)) * a 3 := by
  have sP00 := congrArg star hP00
  have sP01 := congrArg star hP01
  have sP10 := congrArg star hP10
  have sP11 := congrArg star hP11
  have sQ00 := congrArg star hQ00
  have sQ01 := congrArg star hQ01
  have sQ10 := congrArg star hQ10
  have sQ11 := congrArg star hQ11
  simp only [star_add, star_mul', star_star, star_zero] at sP00 sP01 sP10 sP11 sQ00 sQ01 sQ10 sQ11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination ((u 0)*zt) * sP00 + ((u 2)*zt) * sP10
      + (-(u 0)*zt) * sQ00 + (-(u 1)*zt) * sQ01
      + ((star (u 1))*(a 0)*(u 1) - (star (u 1))*(a 1)*(u 0) - (star (u 2))*(a 0)*(u 2) + (star (u 2))*(a 2)*(u 0) - (star (u 3))*(a 1)*(u 2) + (star (u 3))*(a 2)*(u 1)) * hz
  · linear_combination ((u 1)*zt) * sP00 + ((u 3)*zt) * sP10
      + (-(u 0)*zt) * sQ10 + (-(u 1)*zt) * sQ11
      + (-(star (u 0))*(a 0)*(u 1) + (star (u 0))*(a 1)*(u 0) - (star (u 2))*(a 0)*(u 3) + (star (u 2))*(a 3)*(u 0) - (star (u 3))*(a 1)*(u 3) + (star (u 3))*(a 3)*(u 1)) * hz
  · linear_combination ((u 0)*zt) * sP01 + ((u 2)*zt) * sP11
      + (-(u 2)*zt) * sQ00 + (-(u 3)*zt) * sQ01
      + ((star (u 0))*(a 0)*(u 2) - (star (u 0))*(a 2)*(u 0) + (star (u 1))*(a 0)*(u 3) - (star (u 1))*(a 3)*(u 0) + (star (u 3))*(a 2)*(u 3) - (star (u 3))*(a 3)*(u 2)) * hz
  · linear_combination ((u 1)*zt) * sP01 + ((u 3)*zt) * sP11
      + (-(u 2)*zt) * sQ10 + (-(u 3)*zt) * sQ11
      + ((star (u 0))*(a 1)*(u 2) - (star (u 0))*(a 2)*(u 1) + (star (u 1))*(a 1)*(u 3) - (star (u 1))*(a 3)*(u 1) - (star (u 2))*(a 2)*(u 3) + (star (u 2))*(a 3)*(u 2)) * hz

/-! ## The Bell branch -/

/-- **The Bell symmetry.**  On the branch locus the mixed inner products are
symmetric, `ip a q = ip p b`, so the two-flip relation makes them vanish. -/
theorem bell_sym (u a b p q : Fin 4 -> ℂ) (zt : ℂ)
    (hM00 : star (u 0) * u 0 + star (u 2) * u 2 = 1/6)
    (hM01 : star (u 0) * u 1 + star (u 2) * u 3 = 0)
    (hM10 : star (u 1) * u 0 + star (u 3) * u 2 = 0)
    (hM11 : star (u 1) * u 1 + star (u 3) * u 3 = 1/6)
    (hP00 : b 0 * star (u 0) + b 1 * star (u 1) + zt * (u 0 * star (a 0) + u 1 * star (a 1)) = 0)
    (hP01 : b 0 * star (u 2) + b 1 * star (u 3) + zt * (u 0 * star (a 2) + u 1 * star (a 3)) = 0)
    (hP10 : b 2 * star (u 0) + b 3 * star (u 1) + zt * (u 2 * star (a 0) + u 3 * star (a 1)) = 0)
    (hP11 : b 2 * star (u 2) + b 3 * star (u 3) + zt * (u 2 * star (a 2) + u 3 * star (a 3)) = 0)
    (hR00 : q 0 * star (u 0) + q 1 * star (u 1) + zt * (u 0 * star (p 0) + u 1 * star (p 1)) = 0)
    (hR01 : q 0 * star (u 2) + q 1 * star (u 3) + zt * (u 0 * star (p 2) + u 1 * star (p 3)) = 0)
    (hR10 : q 2 * star (u 0) + q 3 * star (u 1) + zt * (u 2 * star (p 0) + u 3 * star (p 1)) = 0)
    (hR11 : q 2 * star (u 2) + q 3 * star (u 3) + zt * (u 2 * star (p 2) + u 3 * star (p 3)) = 0)
    : ip a q = ip p b := by
  simp only [ip]
  linear_combination (6*(star (a 0))*(u 0) + 6*(star (a 1))*(u 1)) * hR00
    + (6*(star (a 0))*(u 2) + 6*(star (a 1))*(u 3)) * hR01
    + (6*(star (a 2))*(u 0) + 6*(star (a 3))*(u 1)) * hR10
    + (6*(star (a 2))*(u 2) + 6*(star (a 3))*(u 3)) * hR11
    + (-6*(star (p 0))*(u 0) - 6*(star (p 1))*(u 1)) * hP00
    + (-6*(star (p 0))*(u 2) - 6*(star (p 1))*(u 3)) * hP01
    + (-6*(star (p 2))*(u 0) - 6*(star (p 3))*(u 1)) * hP10
    + (-6*(star (p 2))*(u 2) - 6*(star (p 3))*(u 3)) * hP11
    + (-6*(star (a 0))*(q 0) - 6*(star (a 2))*(q 2) + 6*(star (p 0))*(b 0) + 6*(star (p 2))*(b 2)) * hM00
    + (-6*(star (a 1))*(q 0) - 6*(star (a 3))*(q 2) + 6*(star (p 1))*(b 0) + 6*(star (p 3))*(b 2)) * hM01
    + (-6*(star (a 0))*(q 1) - 6*(star (a 2))*(q 3) + 6*(star (p 0))*(b 1) + 6*(star (p 2))*(b 3)) * hM10
    + (-6*(star (a 1))*(q 1) - 6*(star (a 3))*(q 3) + 6*(star (p 1))*(b 1) + 6*(star (p 3))*(b 3)) * hM11

/-! ## The two anchors are parallel -/

/-- If the two anchors have the same rank-one marginal then the top one is a
unit multiple of the bottom one. -/
theorem rank_one (u v : Fin 4 -> ℂ) (hv : nsq v = 1/3)
    (h : ∀ k l : Fin 4, u k * star (u l) = v k * star (v l)) :
    ∀ l : Fin 4, v l = (3 * ip u v) * u l := by
  have h13 : star (v 0) * v 0 + star (v 1) * v 1 + star (v 2) * v 2 + star (v 3) * v 3
      = (1/3 : ℂ) := by
    have hs := ip_self v
    simp only [ip] at hs
    rw [hs, hv]
    norm_num
  intro l
  have hs : (1/3 : ℂ) * star (v l) = ip v u * star (u l) := by
    simp only [ip]
    linear_combination (-star (v l)) * h13 + (-star (v 0)) * h 0 l + (-star (v 1)) * h 1 l
      + (-star (v 2)) * h 2 l + (-star (v 3)) * h 3 l
  have hstar := congrArg star hs
  simp only [star_mul', star_star] at hstar
  rw [ip_star] at hstar
  have h3 : star ((1/3 : ℂ)) = (1/3 : ℂ) := by norm_num
  rw [h3] at hstar
  linear_combination 3 * hstar

/-- The unit modulus of the phase relating the two anchors. -/
theorem phase_unit (u v : Fin 4 -> ℂ) (hu : nsq u = 1/3) (hv : nsq v = 1/3)
    (hpar : ∀ l : Fin 4, v l = (3 * ip u v) * u l) :
    star (3 * ip u v) * (3 * ip u v) = 1 := by
  have hnn : nsq v = Complex.normSq (3 * ip u v) * nsq u := by
    simp only [nsq, hpar 0, hpar 1, hpar 2, hpar 3, Complex.normSq_mul]
    ring
  rw [hu, hv] at hnn
  have h1 : Complex.normSq (3 * ip u v) = 1 := by linarith
  rw [SixQubit.star_mul_self, h1]
  norm_num

end

end SixQubit.Kernel5
