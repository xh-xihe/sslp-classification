import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Trace5
import SixQubit.Triangle

set_option maxHeartbeats 4000000

/-!
# The two-qubit flip-kernel dichotomy of orbit 5

Orbit 5 has two zero-angle qubits, so a tail amplitude is a vector of `ℂ⁴`,
which we read as the `2 × 2` coefficient matrix `X` with `X r s = x (2*r+s)`.
For the anchor `u` write `G = U U†` and `H = U† U`.

For a one-qubit operator `F` on either factor the error `F Xᵢ` has weight two,
so the Knill--Laflamme rows for all such `F` say exactly that both one-qubit
partial traces of `|u⟩⟨bᵢ| + |aᵢ⟩⟨u|` vanish, i.e.

```
Bᵢ U† + U Aᵢ† = 0 ,      U† Bᵢ + Aᵢ† U = 0 .
```

Eliminating between the two gives the *intertwining relations*

```
G Bᵢ = Bᵢ H ,     G Aᵢ = Aᵢ H ,
```
whose solution space `S` is two-dimensional as soon as the two singular values
of `U` are distinct.  The discriminant that decides this is

```
dsc u = (u†u)² - 4 |det U|²   ( = (s² - t²)²/9 for the Schmidt values s,t ) ,
```

and the whole dichotomy is run off it, with no local-unitary normalisation:

* `line_key` -- if `dsc u ≠ 0` then every `X ∈ S` orthogonal to `u` satisfies
  `dsc u • X = τ(u,X) • w`, where `w = (u†u) (adj U)† - 2 conj(det U) U` is a
  fixed vector of `u^⊥`.  So all `aᵢ` and `bᵢ` lie on one line and the
  two-flip relations become the odd triangle of `SixQubit.Triangle`.
* `bell_pair` -- if `dsc u = 0` then `G = H = (1/6) I`, whence `Bᵢ = -6 U Aᵢ† U`
  and `aᵢ† bⱼ = aⱼ† bᵢ`; with the two-flip relations that gives the twelve
  cross orthogonalities wanted by `SixQubit.Trace5.bell_contradiction`.

Nothing here mentions bit strings; `native_decide` and `sorry` do not occur.
-/

namespace SixQubit.Flip5

open scoped ComplexConjugate
open SixQubit.Trace5

noncomputable section

/-! ## The invariants of the anchor -/

/-- `conj (det U)`. -/
def dcj (u : Fin 4 → ℂ) : ℂ := star (u 0) * star (u 3) - star (u 1) * star (u 2)

/-- `det U`. -/
def dtu (u : Fin 4 → ℂ) : ℂ := u 0 * u 3 - u 1 * u 2

/-- The discriminant `(u†u)² - 4 |det U|²` separating the two branches. -/
def dsc (u : Fin 4 → ℂ) : ℂ := ip u u * ip u u - 4 * dcj u * dtu u

/-- The bilinear pairing `Tr (adj U · X)`. -/
def tau (u x : Fin 4 → ℂ) : ℂ := u 3 * x 0 - u 2 * x 1 - u 1 * x 2 + u 0 * x 3

/-- The vector `w = (u†u) (adj U)† - 2 conj(det U) U`, which spans the flip
kernel line inside `u^⊥` whenever `dsc u ≠ 0`. -/
def ww (u : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![ip u u * star (u 3) - 2 * dcj u * u 0, -(ip u u * star (u 2)) - 2 * dcj u * u 1,
    -(ip u u * star (u 1)) - 2 * dcj u * u 2, ip u u * star (u 0) - 2 * dcj u * u 3]

@[simp] theorem ww_0 (u : Fin 4 → ℂ) : ww u 0 = ip u u * star (u 3) - 2 * dcj u * u 0 := rfl
@[simp] theorem ww_1 (u : Fin 4 → ℂ) : ww u 1 = -(ip u u * star (u 2)) - 2 * dcj u * u 1 := rfl
@[simp] theorem ww_2 (u : Fin 4 → ℂ) : ww u 2 = -(ip u u * star (u 1)) - 2 * dcj u * u 2 := rfl
@[simp] theorem ww_3 (u : Fin 4 → ℂ) : ww u 3 = ip u u * star (u 0) - 2 * dcj u * u 3 := rfl

/-- The four entries of the intertwiner `G X - X H`. -/
def cin (u x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![-star (u 1) * u 0 * x 1 + star (u 1) * u 1 * x 0 + star (u 2) * u 0 * x 2
      - star (u 2) * u 2 * x 0 + star (u 3) * u 1 * x 2 - star (u 3) * u 2 * x 1,
    star (u 0) * u 0 * x 1 - star (u 0) * u 1 * x 0 + star (u 2) * u 0 * x 3
      - star (u 2) * u 3 * x 0 + star (u 3) * u 1 * x 3 - star (u 3) * u 3 * x 1,
    -star (u 0) * u 0 * x 2 + star (u 0) * u 2 * x 0 - star (u 1) * u 0 * x 3
      + star (u 1) * u 3 * x 0 - star (u 3) * u 2 * x 3 + star (u 3) * u 3 * x 2,
    -star (u 0) * u 1 * x 2 + star (u 0) * u 2 * x 1 - star (u 1) * u 1 * x 3
      + star (u 1) * u 3 * x 1 + star (u 2) * u 2 * x 3 - star (u 2) * u 3 * x 2]

@[simp] theorem cin_0 (u x : Fin 4 → ℂ) :
    cin u x 0 = -star (u 1) * u 0 * x 1 + star (u 1) * u 1 * x 0 + star (u 2) * u 0 * x 2
      - star (u 2) * u 2 * x 0 + star (u 3) * u 1 * x 2 - star (u 3) * u 2 * x 1 := rfl
@[simp] theorem cin_1 (u x : Fin 4 → ℂ) :
    cin u x 1 = star (u 0) * u 0 * x 1 - star (u 0) * u 1 * x 0 + star (u 2) * u 0 * x 3
      - star (u 2) * u 3 * x 0 + star (u 3) * u 1 * x 3 - star (u 3) * u 3 * x 1 := rfl
@[simp] theorem cin_2 (u x : Fin 4 → ℂ) :
    cin u x 2 = -star (u 0) * u 0 * x 2 + star (u 0) * u 2 * x 0 - star (u 1) * u 0 * x 3
      + star (u 1) * u 3 * x 0 - star (u 3) * u 2 * x 3 + star (u 3) * u 3 * x 2 := rfl
@[simp] theorem cin_3 (u x : Fin 4 → ℂ) :
    cin u x 3 = -star (u 0) * u 1 * x 2 + star (u 0) * u 2 * x 1 - star (u 1) * u 1 * x 3
      + star (u 1) * u 3 * x 1 + star (u 2) * u 2 * x 3 - star (u 2) * u 3 * x 2 := rfl

/-! ## The discriminant is real -/

theorem dsc_star (u : Fin 4 → ℂ) : star (dsc u) = dsc u := by
  simp only [dsc, dcj, dtu, ip, star_sub, star_mul', star_add, star_star, star_ofNat]
  ring

/-! ## The line branch -/

/-- **The flip-kernel line.**  A vector of the intertwiner kernel that is
orthogonal to the anchor is carried onto the fixed vector `w` by the
discriminant. -/
theorem line_key (u x : Fin 4 → ℂ)
    (h0 : cin u x 0 = 0) (h1 : cin u x 1 = 0) (h2 : cin u x 2 = 0) (h3 : cin u x 3 = 0)
    (hs : ip u x = 0) :
    dsc u * x 0 = tau u x * ww u 0 ∧ dsc u * x 1 = tau u x * ww u 1 ∧
      dsc u * x 2 = tau u x * ww u 2 ∧ dsc u * x 3 = tau u x * ww u 3 := by
  simp only [cin_0, cin_1, cin_2, cin_3] at h0 h1 h2 h3
  simp only [ip] at hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [dsc, dcj, dtu, tau, ww_0, ww_1, ww_2, ww_3, ip]
  · linear_combination (-star (u 0) * u 0 + star (u 1) * u 1 - star (u 2) * u 2
      + star (u 3) * u 3) * h0 + (-2 * star (u 1) * u 0 - 2 * star (u 3) * u 2) * h1
      + (star (u 0) * u 0 * u 0 + star (u 1) * u 0 * u 1 + star (u 2) * u 0 * u 2
      - star (u 3) * u 0 * u 3 + 2 * star (u 3) * u 1 * u 2) * hs
  · linear_combination (-2 * star (u 0) * u 1 - 2 * star (u 2) * u 3) * h0 + (star (u 0) * u 0
      - star (u 1) * u 1 + star (u 2) * u 2 - star (u 3) * u 3) * h1 + (star (u 1) * u 1 * u 1
      + star (u 0) * u 0 * u 1 + 2 * star (u 2) * u 0 * u 3 - star (u 2) * u 1 * u 2
      + star (u 3) * u 1 * u 3) * hs
  · linear_combination (2 * star (u 0) * u 2 + 2 * star (u 1) * u 3) * h0 + (-star (u 0) * u 0
      - star (u 1) * u 1 + star (u 2) * u 2 + star (u 3) * u 3) * h2 + (star (u 2) * u 2 * u 2
      + star (u 0) * u 0 * u 2 + 2 * star (u 1) * u 0 * u 3 - star (u 1) * u 1 * u 2
      + star (u 3) * u 2 * u 3) * hs
  · linear_combination (2 * star (u 0) * u 2 + 2 * star (u 1) * u 3) * h1 + (-star (u 0) * u 0
      - star (u 1) * u 1 + star (u 2) * u 2 + star (u 3) * u 3) * h3 + (star (u 3) * u 3 * u 3
      - star (u 0) * u 0 * u 3 + 2 * star (u 0) * u 1 * u 2 + star (u 1) * u 1 * u 3
      + star (u 2) * u 2 * u 3) * hs

/-- Transporting the line identity through an inner product. -/
theorem line_ip (u x y : Fin 4 → ℂ)
    (e0 : dsc u * x 0 = tau u x * ww u 0) (e1 : dsc u * x 1 = tau u x * ww u 1)
    (e2 : dsc u * x 2 = tau u x * ww u 2) (e3 : dsc u * x 3 = tau u x * ww u 3) :
    dsc u * ip x y = star (tau u x) * ip (ww u) y := by
  have d0 := congrArg star e0
  have d1 := congrArg star e1
  have d2 := congrArg star e2
  have d3 := congrArg star e3
  simp only [star_mul', dsc_star] at d0 d1 d2 d3
  simp only [ip]
  linear_combination (y 0) * d0 + (y 1) * d1 + (y 2) * d2 + (y 3) * d3

/-! ## The Bell branch -/

/-- The entries of `U A† U`. -/
def uau (u a : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![u 0 * star (a 0) * u 0 + u 0 * star (a 2) * u 2 + u 1 * star (a 1) * u 0
      + u 1 * star (a 3) * u 2,
    u 0 * star (a 0) * u 1 + u 0 * star (a 2) * u 3 + u 1 * star (a 1) * u 1
      + u 1 * star (a 3) * u 3,
    u 2 * star (a 0) * u 0 + u 2 * star (a 2) * u 2 + u 3 * star (a 1) * u 0
      + u 3 * star (a 3) * u 2,
    u 2 * star (a 0) * u 1 + u 2 * star (a 2) * u 3 + u 3 * star (a 1) * u 1
      + u 3 * star (a 3) * u 3]

@[simp] theorem uau_0 (u a : Fin 4 → ℂ) :
    uau u a 0 = u 0 * star (a 0) * u 0 + u 0 * star (a 2) * u 2 + u 1 * star (a 1) * u 0
      + u 1 * star (a 3) * u 2 := rfl
@[simp] theorem uau_1 (u a : Fin 4 → ℂ) :
    uau u a 1 = u 0 * star (a 0) * u 1 + u 0 * star (a 2) * u 3 + u 1 * star (a 1) * u 1
      + u 1 * star (a 3) * u 3 := rfl
@[simp] theorem uau_2 (u a : Fin 4 → ℂ) :
    uau u a 2 = u 2 * star (a 0) * u 0 + u 2 * star (a 2) * u 2 + u 3 * star (a 1) * u 0
      + u 3 * star (a 3) * u 2 := rfl
@[simp] theorem uau_3 (u a : Fin 4 → ℂ) :
    uau u a 3 = u 2 * star (a 0) * u 1 + u 2 * star (a 2) * u 3 + u 3 * star (a 1) * u 1
      + u 3 * star (a 3) * u 3 := rfl

theorem dcj_eq (u : Fin 4 → ℂ) : dcj u = star (dtu u) := by
  simp only [dcj, dtu, star_sub, star_mul']

/-- The discriminant is the real number `‖u‖⁴ - 4 |det U|²`. -/
theorem dsc_real (u : Fin 4 → ℂ) (hu : nsq u = 1/3) :
    dsc u = ((1/9 - 4 * Complex.normSq (dtu u) : Real) : ℂ) := by
  have h1 : ip u u = ((1/3 : Real) : ℂ) := by rw [ip_self, hu]
  have h2 : dcj u * dtu u = ((Complex.normSq (dtu u) : Real) : ℂ) := by
    rw [dcj_eq]
    linear_combination mul_star (dtu u)
  push_cast at h1 h2
  simp only [dsc]
  push_cast
  linear_combination (ip u u + 1/3) * h1 - 4 * h2

/-- **The Bell branch.**  When the discriminant vanishes the reduced density
matrix `U U†` of the anchor is `1/6` times the identity. -/
theorem bell_G (u : Fin 4 → ℂ) (hu : nsq u = 1/3)
    (hd : Complex.normSq (dtu u) = 1/36) :
    u 0 * star (u 0) + u 1 * star (u 1) = 1/6 ∧
      u 2 * star (u 2) + u 3 * star (u 3) = 1/6 ∧
      u 0 * star (u 2) + u 1 * star (u 3) = 0 ∧
      u 2 * star (u 0) + u 3 * star (u 1) = 0 := by
  have hcs : u 2 * star (u 0) + u 3 * star (u 1)
      = star (u 0 * star (u 2) + u 1 * star (u 3)) := by
    simp only [star_add, star_mul', star_star]; ring
  have lagC : (u 0 * star (u 0) + u 1 * star (u 1)) * (u 2 * star (u 2) + u 3 * star (u 3))
      - (u 0 * star (u 2) + u 1 * star (u 3)) * (u 2 * star (u 0) + u 3 * star (u 1))
      = dtu u * star (dtu u) := by
    simp only [dtu, star_sub, star_mul']; ring
  rw [hcs] at lagC
  rw [mul_star, mul_star, mul_star, mul_star, mul_star, mul_star] at lagC
  have lagR : (Complex.normSq (u 0) + Complex.normSq (u 1))
      * (Complex.normSq (u 2) + Complex.normSq (u 3))
      - Complex.normSq (u 0 * star (u 2) + u 1 * star (u 3)) = Complex.normSq (dtu u) := by
    exact_mod_cast lagC
  have hsum : Complex.normSq (u 0) + Complex.normSq (u 1) + Complex.normSq (u 2)
      + Complex.normSq (u 3) = 1/3 := by
    simpa only [nsq] using hu
  have hnn := Complex.normSq_nonneg (u 0 * star (u 2) + u 1 * star (u 3))
  have hz : Complex.normSq (u 0 * star (u 2) + u 1 * star (u 3)) = 0 := by
    nlinarith [lagR, hsum, hd, hnn,
      sq_nonneg (Complex.normSq (u 0) + Complex.normSq (u 1) - Complex.normSq (u 2)
        - Complex.normSq (u 3))]
  have hg1 : Complex.normSq (u 0) + Complex.normSq (u 1) = 1/6 := by
    nlinarith [lagR, hsum, hd, hz,
      sq_nonneg (Complex.normSq (u 0) + Complex.normSq (u 1) - Complex.normSq (u 2)
        - Complex.normSq (u 3))]
  have hg2 : Complex.normSq (u 2) + Complex.normSq (u 3) = 1/6 := by linarith
  have hz0 : u 0 * star (u 2) + u 1 * star (u 3) = 0 := Complex.normSq_eq_zero.mp hz
  refine ⟨?_, ?_, hz0, ?_⟩
  · rw [mul_star, mul_star]
    have : ((Complex.normSq (u 0) + Complex.normSq (u 1) : Real) : ℂ) = ((1/6 : Real) : ℂ) := by
      exact_mod_cast congrArg (fun t : Real => (t : ℂ)) hg1
    push_cast at this ⊢
    linear_combination this
  · rw [mul_star, mul_star]
    have : ((Complex.normSq (u 2) + Complex.normSq (u 3) : Real) : ℂ) = ((1/6 : Real) : ℂ) := by
      exact_mod_cast congrArg (fun t : Real => (t : ℂ)) hg2
    push_cast at this ⊢
    linear_combination this
  · rw [hcs, hz0, star_zero]

/-- In the Bell branch the top vector is determined by the bottom one:
`Bᵢ = -6 U Aᵢ† U`, the coordinate form of `Bᵢ = -Aᵢ†` in Schmidt gauge. -/
theorem bell_step (u a b : Fin 4 → ℂ) (sc : ℂ)
    (g00 : u 0 * star (u 0) + u 1 * star (u 1) = 1/6)
    (g01 : u 0 * star (u 2) + u 1 * star (u 3) = 0)
    (g10 : u 2 * star (u 0) + u 3 * star (u 1) = 0)
    (g11 : u 2 * star (u 2) + u 3 * star (u 3) = 1/6)
    (k00 : sc * (star (u 0) * b 0 + star (u 2) * b 2) + star (a 0) * u 0 + star (a 2) * u 2 = 0)
    (k01 : sc * (star (u 1) * b 0 + star (u 3) * b 2) + star (a 1) * u 0 + star (a 3) * u 2 = 0)
    (k10 : sc * (star (u 0) * b 1 + star (u 2) * b 3) + star (a 0) * u 1 + star (a 2) * u 3 = 0)
    (k11 : sc * (star (u 1) * b 1 + star (u 3) * b 3) + star (a 1) * u 1 + star (a 3) * u 3 = 0)
    : sc * b 0 = -6 * uau u a 0 ∧ sc * b 1 = -6 * uau u a 1 ∧
      sc * b 2 = -6 * uau u a 2 ∧ sc * b 3 = -6 * uau u a 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [uau_0, uau_1, uau_2, uau_3]
  · linear_combination (6 * u 0) * k00 + (6 * u 1) * k01 + (-(6 * sc * b 0)) * g00
      + (-(6 * sc * b 2)) * g01
  · linear_combination (6 * u 0) * k10 + (6 * u 1) * k11 + (-(6 * sc * b 1)) * g00
      + (-(6 * sc * b 3)) * g01
  · linear_combination (6 * u 2) * k00 + (6 * u 3) * k01 + (-(6 * sc * b 0)) * g10
      + (-(6 * sc * b 2)) * g11
  · linear_combination (6 * u 2) * k10 + (6 * u 3) * k11 + (-(6 * sc * b 1)) * g10
      + (-(6 * sc * b 3)) * g11

/-- The Bell branch makes the mixed Gram matrix symmetric. -/
theorem bell_sym (u ai aj bi bj : Fin 4 → ℂ) (sc : ℂ)
    (i0 : sc * bi 0 = -6 * uau u ai 0) (i1 : sc * bi 1 = -6 * uau u ai 1)
    (i2 : sc * bi 2 = -6 * uau u ai 2) (i3 : sc * bi 3 = -6 * uau u ai 3)
    (j0 : sc * bj 0 = -6 * uau u aj 0) (j1 : sc * bj 1 = -6 * uau u aj 1)
    (j2 : sc * bj 2 = -6 * uau u aj 2) (j3 : sc * bj 3 = -6 * uau u aj 3) :
    sc * ip ai bj = sc * ip aj bi := by
  simp only [uau_0, uau_1, uau_2, uau_3] at i0 i1 i2 i3 j0 j1 j2 j3
  simp only [ip]
  linear_combination (star (ai 0)) * j0 + (star (ai 1)) * j1 + (star (ai 2)) * j2
    + (star (ai 3)) * j3 + (-(star (aj 0))) * i0 + (-(star (aj 1))) * i1 + (-(star (aj 2))) * i2
    + (-(star (aj 3))) * i3

/-! ## The anchor rescaling -/

/-- Tightness in Cauchy--Schwarz makes the two anchors parallel: there is a
unit scalar `sc` with `sc • v = u`.  This is the honest form of the paper`s
rephasing of `|1_L⟩`. -/
theorem anchor_scale (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)
    (hu : nsq u = 1/3) (hv : nsq v = 1/3)
    (hq1 : ip u b1 = 0) (hq2 : ip u b2 = 0) (hq3 : ip u b3 = 0) (hq4 : ip u b4 = 0)
    (hf : ∀ k l : Fin 4, u k * star (u l) + fr a1 a2 a3 a4 k l
            = fr b1 b2 b3 b4 k l + v k * star (v l)) :
    ∃ sc : ℂ, (∀ l : Fin 4, sc * v l = u l) ∧ star sc * sc = 1 := by
  simp only [fr] at hf
  have key : ip u u * ip u u + (ip u a1 * ip a1 u + ip u a2 * ip a2 u + ip u a3 * ip a3 u
        + ip u a4 * ip a4 u
      ) = (ip u b1 * ip b1 u + ip u b2 * ip b2 u + ip u b3 * ip b3 u + ip u b4 * ip b4 u)
        + ip u v * ip v u := by
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
  have hnv : Complex.normSq (ip u v) = 1/9 := by linarith
  have huv : nsq u * nsq v ≤ Complex.normSq (ip u v) := by rw [hu, hv, hnv]; norm_num
  obtain ⟨p0, p1, p2, p3⟩ := par huv
  have hiu : ip u u = ((1/3 : Real) : ℂ) := by rw [ip_self, hu]
  rw [hiu] at p0 p1 p2 p3
  have hmu : ip u v * star (ip u v) = ((1/9 : Real) : ℂ) := by rw [mul_star, hnv]
  push_cast at p0 p1 p2 p3 hmu
  have s0 : 3 * star (ip u v) * v 0 = u 0 := by
    linear_combination (9 * star (ip u v)) * p0 + (9 * u 0) * hmu
  have s1 : 3 * star (ip u v) * v 1 = u 1 := by
    linear_combination (9 * star (ip u v)) * p1 + (9 * u 1) * hmu
  have s2 : 3 * star (ip u v) * v 2 = u 2 := by
    linear_combination (9 * star (ip u v)) * p2 + (9 * u 2) * hmu
  have s3 : 3 * star (ip u v) * v 3 = u 3 := by
    linear_combination (9 * star (ip u v)) * p3 + (9 * u 3) * hmu
  refine ⟨3 * star (ip u v), ?_, ?_⟩
  · intro l
    fin_cases l
    exacts [s0, s1, s2, s3]
  · simp only [star_mul', star_star, star_ofNat]
    linear_combination 9 * hmu

/-! ## From the flip rows to the intertwiner -/

/-- **The eight weight-two flip rows of one active coordinate.**  After the
anchor rescaling they say `B U† + U A† = 0` and `U† B + A† U = 0`; eliminating
between the two gives the intertwining relations `G A = A H` and `G B = B H`.
The four `U† B + A† U` entries are returned as well, for the Bell branch. -/
theorem flip_reduce (u v a b : Fin 4 → ℂ) (sc : ℂ)
    (hsv : ∀ l : Fin 4, sc * v l = u l) (hsc : sc ≠ 0)
    (i00 : star (u 0) * b 0 + star (u 1) * b 1 + star (a 0) * v 0 + star (a 1) * v 1 = 0)
    (i01 : star (u 2) * b 0 + star (u 3) * b 1 + star (a 2) * v 0 + star (a 3) * v 1 = 0)
    (i10 : star (u 0) * b 2 + star (u 1) * b 3 + star (a 0) * v 2 + star (a 1) * v 3 = 0)
    (i11 : star (u 2) * b 2 + star (u 3) * b 3 + star (a 2) * v 2 + star (a 3) * v 3 = 0)
    (j00 : star (u 0) * b 0 + star (u 2) * b 2 + star (a 0) * v 0 + star (a 2) * v 2 = 0)
    (j01 : star (u 1) * b 0 + star (u 3) * b 2 + star (a 1) * v 0 + star (a 3) * v 2 = 0)
    (j10 : star (u 0) * b 1 + star (u 2) * b 3 + star (a 0) * v 1 + star (a 2) * v 3 = 0)
    (j11 : star (u 1) * b 1 + star (u 3) * b 3 + star (a 1) * v 1 + star (a 3) * v 3 = 0)
    : (cin u a 0 = 0 ∧ cin u a 1 = 0 ∧ cin u a 2 = 0 ∧ cin u a 3 = 0) ∧
      (cin u b 0 = 0 ∧ cin u b 1 = 0 ∧ cin u b 2 = 0 ∧ cin u b 3 = 0) ∧
      (sc * (star (u 0) * b 0 + star (u 2) * b 2) + star (a 0) * u 0 + star (a 2) * u 2 = 0 ∧
        sc * (star (u 1) * b 0 + star (u 3) * b 2) + star (a 1) * u 0 + star (a 3) * u 2 = 0 ∧
        sc * (star (u 0) * b 1 + star (u 2) * b 3) + star (a 0) * u 1 + star (a 2) * u 3 = 0 ∧
        sc * (star (u 1) * b 1 + star (u 3) * b 3) + star (a 1) * u 1 + star (a 3) * u 3 = 0) := by
  have cancel : ∀ z : ℂ, sc * z = 0 → z = 0 := by
    intro z hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hsc
    · exact h
  have s0 := hsv 0
  have s1 := hsv 1
  have s2 := hsv 2
  have s3 := hsv 3
  have p00 : sc * (star (u 0) * b 0 + star (u 1) * b 1) + star (a 0) * u 0 + star (a 1) * u 1 = 0 := by
    linear_combination sc * i00 - (star (a 0)) * s0 - (star (a 1)) * s1
  have p01 : sc * (star (u 2) * b 0 + star (u 3) * b 1) + star (a 2) * u 0 + star (a 3) * u 1 = 0 := by
    linear_combination sc * i01 - (star (a 2)) * s0 - (star (a 3)) * s1
  have p10 : sc * (star (u 0) * b 2 + star (u 1) * b 3) + star (a 0) * u 2 + star (a 1) * u 3 = 0 := by
    linear_combination sc * i10 - (star (a 0)) * s2 - (star (a 1)) * s3
  have p11 : sc * (star (u 2) * b 2 + star (u 3) * b 3) + star (a 2) * u 2 + star (a 3) * u 3 = 0 := by
    linear_combination sc * i11 - (star (a 2)) * s2 - (star (a 3)) * s3
  have q00 : sc * (star (u 0) * b 0 + star (u 2) * b 2) + star (a 0) * u 0 + star (a 2) * u 2 = 0 := by
    linear_combination sc * j00 - (star (a 0)) * s0 - (star (a 2)) * s2
  have q01 : sc * (star (u 1) * b 0 + star (u 3) * b 2) + star (a 1) * u 0 + star (a 3) * u 2 = 0 := by
    linear_combination sc * j01 - (star (a 1)) * s0 - (star (a 3)) * s2
  have q10 : sc * (star (u 0) * b 1 + star (u 2) * b 3) + star (a 0) * u 1 + star (a 2) * u 3 = 0 := by
    linear_combination sc * j10 - (star (a 0)) * s1 - (star (a 2)) * s3
  have q11 : sc * (star (u 1) * b 1 + star (u 3) * b 3) + star (a 1) * u 1 + star (a 3) * u 3 = 0 := by
    linear_combination sc * j11 - (star (a 1)) * s1 - (star (a 3)) * s3
  have pc00 : star sc * (u 0 * star (b 0) + u 1 * star (b 1)) + a 0 * star (u 0) + a 1 * star (u 1) = 0 := by
    have h := congrArg star p00
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have pc01 : star sc * (u 2 * star (b 0) + u 3 * star (b 1)) + a 2 * star (u 0) + a 3 * star (u 1) = 0 := by
    have h := congrArg star p01
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have pc10 : star sc * (u 0 * star (b 2) + u 1 * star (b 3)) + a 0 * star (u 2) + a 1 * star (u 3) = 0 := by
    have h := congrArg star p10
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have pc11 : star sc * (u 2 * star (b 2) + u 3 * star (b 3)) + a 2 * star (u 2) + a 3 * star (u 3) = 0 := by
    have h := congrArg star p11
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have qc00 : star sc * (u 0 * star (b 0) + u 2 * star (b 2)) + a 0 * star (u 0) + a 2 * star (u 2) = 0 := by
    have h := congrArg star q00
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have qc01 : star sc * (u 1 * star (b 0) + u 3 * star (b 2)) + a 1 * star (u 0) + a 3 * star (u 2) = 0 := by
    have h := congrArg star q01
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have qc10 : star sc * (u 0 * star (b 1) + u 2 * star (b 3)) + a 0 * star (u 1) + a 2 * star (u 3) = 0 := by
    have h := congrArg star q10
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have qc11 : star sc * (u 1 * star (b 1) + u 3 * star (b 3)) + a 1 * star (u 1) + a 3 * star (u 3) = 0 := by
    have h := congrArg star q11
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have ca0 : cin u a 0 = 0 := by
    simp only [cin_0]
    linear_combination (u 0) * qc00 + (u 1) * qc10 + (-(u 0)) * pc00 + (-(u 2)) * pc10
  have ca1 : cin u a 1 = 0 := by
    simp only [cin_1]
    linear_combination (u 0) * qc01 + (u 1) * qc11 + (-(u 1)) * pc00 + (-(u 3)) * pc10
  have ca2 : cin u a 2 = 0 := by
    simp only [cin_2]
    linear_combination (u 2) * qc00 + (u 3) * qc10 + (-(u 0)) * pc01 + (-(u 2)) * pc11
  have ca3 : cin u a 3 = 0 := by
    simp only [cin_3]
    linear_combination (u 2) * qc01 + (u 3) * qc11 + (-(u 1)) * pc01 + (-(u 3)) * pc11
  have cbs0 : sc * cin u b 0 = 0 := by
    simp only [cin_0]
    linear_combination (u 0) * q00 + (u 1) * q01 + (-(u 0)) * p00 + (-(u 2)) * p01
  have cb0 : cin u b 0 = 0 := cancel _ cbs0
  have cbs1 : sc * cin u b 1 = 0 := by
    simp only [cin_1]
    linear_combination (u 0) * q10 + (u 1) * q11 + (-(u 1)) * p00 + (-(u 3)) * p01
  have cb1 : cin u b 1 = 0 := cancel _ cbs1
  have cbs2 : sc * cin u b 2 = 0 := by
    simp only [cin_2]
    linear_combination (u 2) * q00 + (u 3) * q01 + (-(u 0)) * p10 + (-(u 2)) * p11
  have cb2 : cin u b 2 = 0 := cancel _ cbs2
  have cbs3 : sc * cin u b 3 = 0 := by
    simp only [cin_3]
    linear_combination (u 2) * q10 + (u 3) * q11 + (-(u 1)) * p10 + (-(u 3)) * p11
  have cb3 : cin u b 3 = 0 := cancel _ cbs3
  exact ⟨⟨ca0, ca1, ca2, ca3⟩, ⟨cb0, cb1, cb2, cb3⟩, q00, q01, q10, q11⟩

/-! ## Non-vanishing in the line branch -/

/-- A nonzero vector of the flip-kernel line has a nonzero `τ`. -/
theorem tau_ne (u x : Fin 4 → ℂ) (hd : dsc u ≠ 0) (hx : nsq x = 1/6)
    (e0 : dsc u * x 0 = tau u x * ww u 0) (e1 : dsc u * x 1 = tau u x * ww u 1)
    (e2 : dsc u * x 2 = tau u x * ww u 2) (e3 : dsc u * x 3 = tau u x * ww u 3) :
    tau u x ≠ 0 := by
  intro h
  rw [h, zero_mul] at e0 e1 e2 e3
  have z0 : x 0 = 0 := by
    rcases mul_eq_zero.mp e0 with h' | h'
    · exact absurd h' hd
    · exact h'
  have z1 : x 1 = 0 := by
    rcases mul_eq_zero.mp e1 with h' | h'
    · exact absurd h' hd
    · exact h'
  have z2 : x 2 = 0 := by
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact absurd h' hd
    · exact h'
  have z3 : x 3 = 0 := by
    rcases mul_eq_zero.mp e3 with h' | h'
    · exact absurd h' hd
    · exact h'
  rw [nsq, z0, z1, z2, z3] at hx
  norm_num at hx

/-- The projection of a top vector onto the line is nonzero. -/
theorem ipw_ne (u x : Fin 4 → ℂ) (hd : dsc u ≠ 0) (hx : nsq x = 1/6)
    (h : dsc u * ip x x = star (tau u x) * ip (ww u) x) : ip (ww u) x ≠ 0 := by
  intro hz
  rw [hz, mul_zero, ip_self, hx] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact hd h'
  · norm_num at h'

/-! ## The assembled contradiction -/

/-- **Orbit 5, the flip-kernel dichotomy.**  Ten vectors of `ℂ⁴` with the orbit-5
norms, the anchor orthogonalities, a common marginal on the free pair, the six
two-flip relations and the eight weight-two flip rows of each active coordinate
cannot exist.  If `dsc u = 0` the flip rows give `Bᵢ = -6 U Aᵢ† U`, hence the
twelve cross orthogonalities and `Trace5.bell_contradiction`; otherwise they
confine every `aᵢ` and `bᵢ` to one line and the two-flip relations become the
odd triangle of `Triangle.contradiction`. -/
theorem core (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)
    (hu : nsq u = 1/3) (hv : nsq v = 1/3)
    (ha1 : nsq a1 = 1/6) (ha2 : nsq a2 = 1/6) (ha3 : nsq a3 = 1/6) (ha4 : nsq a4 = 1/6)
    (hb1 : nsq b1 = 1/6) (hb2 : nsq b2 = 1/6) (hb3 : nsq b3 = 1/6) (hb4 : nsq b4 = 1/6)
    (hq1 : ip u b1 = 0) (hq2 : ip u b2 = 0) (hq3 : ip u b3 = 0) (hq4 : ip u b4 = 0)
    (hf : ∀ k l : Fin 4, u k * star (u l) + fr a1 a2 a3 a4 k l
            = fr b1 b2 b3 b4 k l + v k * star (v l))
    (x12 : ip a1 b2 + ip a2 b1 = 0)
    (x13 : ip a1 b3 + ip a3 b1 = 0)
    (x14 : ip a1 b4 + ip a4 b1 = 0)
    (x23 : ip a2 b3 + ip a3 b2 = 0)
    (x24 : ip a2 b4 + ip a4 b2 = 0)
    (x34 : ip a3 b4 + ip a4 b3 = 0)
    (m100 : star (u 0) * b1 0 + star (u 1) * b1 1 + star (a1 0) * v 0 + star (a1 1) * v 1 = 0)
    (m101 : star (u 2) * b1 0 + star (u 3) * b1 1 + star (a1 2) * v 0 + star (a1 3) * v 1 = 0)
    (m110 : star (u 0) * b1 2 + star (u 1) * b1 3 + star (a1 0) * v 2 + star (a1 1) * v 3 = 0)
    (m111 : star (u 2) * b1 2 + star (u 3) * b1 3 + star (a1 2) * v 2 + star (a1 3) * v 3 = 0)
    (n100 : star (u 0) * b1 0 + star (u 2) * b1 2 + star (a1 0) * v 0 + star (a1 2) * v 2 = 0)
    (n101 : star (u 1) * b1 0 + star (u 3) * b1 2 + star (a1 1) * v 0 + star (a1 3) * v 2 = 0)
    (n110 : star (u 0) * b1 1 + star (u 2) * b1 3 + star (a1 0) * v 1 + star (a1 2) * v 3 = 0)
    (n111 : star (u 1) * b1 1 + star (u 3) * b1 3 + star (a1 1) * v 1 + star (a1 3) * v 3 = 0)
    (m200 : star (u 0) * b2 0 + star (u 1) * b2 1 + star (a2 0) * v 0 + star (a2 1) * v 1 = 0)
    (m201 : star (u 2) * b2 0 + star (u 3) * b2 1 + star (a2 2) * v 0 + star (a2 3) * v 1 = 0)
    (m210 : star (u 0) * b2 2 + star (u 1) * b2 3 + star (a2 0) * v 2 + star (a2 1) * v 3 = 0)
    (m211 : star (u 2) * b2 2 + star (u 3) * b2 3 + star (a2 2) * v 2 + star (a2 3) * v 3 = 0)
    (n200 : star (u 0) * b2 0 + star (u 2) * b2 2 + star (a2 0) * v 0 + star (a2 2) * v 2 = 0)
    (n201 : star (u 1) * b2 0 + star (u 3) * b2 2 + star (a2 1) * v 0 + star (a2 3) * v 2 = 0)
    (n210 : star (u 0) * b2 1 + star (u 2) * b2 3 + star (a2 0) * v 1 + star (a2 2) * v 3 = 0)
    (n211 : star (u 1) * b2 1 + star (u 3) * b2 3 + star (a2 1) * v 1 + star (a2 3) * v 3 = 0)
    (m300 : star (u 0) * b3 0 + star (u 1) * b3 1 + star (a3 0) * v 0 + star (a3 1) * v 1 = 0)
    (m301 : star (u 2) * b3 0 + star (u 3) * b3 1 + star (a3 2) * v 0 + star (a3 3) * v 1 = 0)
    (m310 : star (u 0) * b3 2 + star (u 1) * b3 3 + star (a3 0) * v 2 + star (a3 1) * v 3 = 0)
    (m311 : star (u 2) * b3 2 + star (u 3) * b3 3 + star (a3 2) * v 2 + star (a3 3) * v 3 = 0)
    (n300 : star (u 0) * b3 0 + star (u 2) * b3 2 + star (a3 0) * v 0 + star (a3 2) * v 2 = 0)
    (n301 : star (u 1) * b3 0 + star (u 3) * b3 2 + star (a3 1) * v 0 + star (a3 3) * v 2 = 0)
    (n310 : star (u 0) * b3 1 + star (u 2) * b3 3 + star (a3 0) * v 1 + star (a3 2) * v 3 = 0)
    (n311 : star (u 1) * b3 1 + star (u 3) * b3 3 + star (a3 1) * v 1 + star (a3 3) * v 3 = 0)
    (m400 : star (u 0) * b4 0 + star (u 1) * b4 1 + star (a4 0) * v 0 + star (a4 1) * v 1 = 0)
    (m401 : star (u 2) * b4 0 + star (u 3) * b4 1 + star (a4 2) * v 0 + star (a4 3) * v 1 = 0)
    (m410 : star (u 0) * b4 2 + star (u 1) * b4 3 + star (a4 0) * v 2 + star (a4 1) * v 3 = 0)
    (m411 : star (u 2) * b4 2 + star (u 3) * b4 3 + star (a4 2) * v 2 + star (a4 3) * v 3 = 0)
    (n400 : star (u 0) * b4 0 + star (u 2) * b4 2 + star (a4 0) * v 0 + star (a4 2) * v 2 = 0)
    (n401 : star (u 1) * b4 0 + star (u 3) * b4 2 + star (a4 1) * v 0 + star (a4 3) * v 2 = 0)
    (n410 : star (u 0) * b4 1 + star (u 2) * b4 3 + star (a4 0) * v 1 + star (a4 2) * v 3 = 0)
    (n411 : star (u 1) * b4 1 + star (u 3) * b4 3 + star (a4 1) * v 1 + star (a4 3) * v 3 = 0)
    : False := by
  obtain ⟨hp1, hp2, hp3, hp4, hfr⟩ :=
    cs_tight u v a1 a2 a3 a4 b1 b2 b3 b4 hu hv hq1 hq2 hq3 hq4 hf
  obtain ⟨sc, hsv, hss⟩ :=
    anchor_scale u v a1 a2 a3 a4 b1 b2 b3 b4 hu hv hq1 hq2 hq3 hq4 hf
  have hsc : sc ≠ 0 := by
    intro h
    rw [h, mul_zero] at hss
    exact zero_ne_one hss
  obtain ⟨⟨ca10, ca11, ca12, ca13⟩, ⟨cb10, cb11, cb12, cb13⟩,
    k100, k101, k110, k111⟩ :=
    flip_reduce u v a1 b1 sc hsv hsc m100 m101 m110 m111 n100 n101 n110 n111
  obtain ⟨⟨ca20, ca21, ca22, ca23⟩, ⟨cb20, cb21, cb22, cb23⟩,
    k200, k201, k210, k211⟩ :=
    flip_reduce u v a2 b2 sc hsv hsc m200 m201 m210 m211 n200 n201 n210 n211
  obtain ⟨⟨ca30, ca31, ca32, ca33⟩, ⟨cb30, cb31, cb32, cb33⟩,
    k300, k301, k310, k311⟩ :=
    flip_reduce u v a3 b3 sc hsv hsc m300 m301 m310 m311 n300 n301 n310 n311
  obtain ⟨⟨ca40, ca41, ca42, ca43⟩, ⟨cb40, cb41, cb42, cb43⟩,
    k400, k401, k410, k411⟩ :=
    flip_reduce u v a4 b4 sc hsv hsc m400 m401 m410 m411 n400 n401 n410 n411
  by_cases hcase : Complex.normSq (dtu u) = 1/36
  · obtain ⟨g00, g11, g01, g10⟩ := bell_G u hu hcase
    obtain ⟨B10, B11, B12, B13⟩ :=
      bell_step u a1 b1 sc g00 g01 g10 g11 k100 k101 k110 k111
    obtain ⟨B20, B21, B22, B23⟩ :=
      bell_step u a2 b2 sc g00 g01 g10 g11 k200 k201 k210 k211
    obtain ⟨B30, B31, B32, B33⟩ :=
      bell_step u a3 b3 sc g00 g01 g10 g11 k300 k301 k310 k311
    obtain ⟨B40, B41, B42, B43⟩ :=
      bell_step u a4 b4 sc g00 g01 g10 g11 k400 k401 k410 k411
    have y12 : ip a1 b2 = ip a2 b1 :=
      mul_left_cancel₀ hsc (bell_sym u a1 a2 b1 b2 sc B10 B11 B12 B13 B20 B21 B22 B23)
    have y13 : ip a1 b3 = ip a3 b1 :=
      mul_left_cancel₀ hsc (bell_sym u a1 a3 b1 b3 sc B10 B11 B12 B13 B30 B31 B32 B33)
    have y14 : ip a1 b4 = ip a4 b1 :=
      mul_left_cancel₀ hsc (bell_sym u a1 a4 b1 b4 sc B10 B11 B12 B13 B40 B41 B42 B43)
    have y23 : ip a2 b3 = ip a3 b2 :=
      mul_left_cancel₀ hsc (bell_sym u a2 a3 b2 b3 sc B20 B21 B22 B23 B30 B31 B32 B33)
    have y24 : ip a2 b4 = ip a4 b2 :=
      mul_left_cancel₀ hsc (bell_sym u a2 a4 b2 b4 sc B20 B21 B22 B23 B40 B41 B42 B43)
    have y34 : ip a3 b4 = ip a4 b3 :=
      mul_left_cancel₀ hsc (bell_sym u a3 a4 b3 b4 sc B30 B31 B32 B33 B40 B41 B42 B43)
    have z12 : ip a1 b2 = 0 := by linear_combination (1/2) * x12 + (1/2) * y12
    have z21 : ip a2 b1 = 0 := by linear_combination (1/2) * x12 - (1/2) * y12
    have z13 : ip a1 b3 = 0 := by linear_combination (1/2) * x13 + (1/2) * y13
    have z31 : ip a3 b1 = 0 := by linear_combination (1/2) * x13 - (1/2) * y13
    have z14 : ip a1 b4 = 0 := by linear_combination (1/2) * x14 + (1/2) * y14
    have z41 : ip a4 b1 = 0 := by linear_combination (1/2) * x14 - (1/2) * y14
    have z23 : ip a2 b3 = 0 := by linear_combination (1/2) * x23 + (1/2) * y23
    have z32 : ip a3 b2 = 0 := by linear_combination (1/2) * x23 - (1/2) * y23
    have z24 : ip a2 b4 = 0 := by linear_combination (1/2) * x24 + (1/2) * y24
    have z42 : ip a4 b2 = 0 := by linear_combination (1/2) * x24 - (1/2) * y24
    have z34 : ip a3 b4 = 0 := by linear_combination (1/2) * x34 + (1/2) * y34
    have z43 : ip a4 b3 = 0 := by linear_combination (1/2) * x34 - (1/2) * y34
    exact bell_contradiction u a1 a2 a3 a4 b1 b2 b3 b4 hu ha1 ha2 ha3 ha4 hb1 hb2 hb3 hb4
      hp1 hp2 hp3 hp4 hfr z12 z13 z14 z21 z23 z24 z31 z32 z34 z41 z42 z43
  · have hdsc : dsc u ≠ 0 := by
      rw [dsc_real u hu]
      intro h
      apply hcase
      have hr : (1/9 - 4 * Complex.normSq (dtu u) : Real) = 0 := by exact_mod_cast h
      linarith
    obtain ⟨la10, la11, la12, la13⟩ := line_key u a1 ca10 ca11 ca12 ca13 hp1
    obtain ⟨lb10, lb11, lb12, lb13⟩ := line_key u b1 cb10 cb11 cb12 cb13 hq1
    obtain ⟨la20, la21, la22, la23⟩ := line_key u a2 ca20 ca21 ca22 ca23 hp2
    obtain ⟨lb20, lb21, lb22, lb23⟩ := line_key u b2 cb20 cb21 cb22 cb23 hq2
    obtain ⟨la30, la31, la32, la33⟩ := line_key u a3 ca30 ca31 ca32 ca33 hp3
    obtain ⟨lb30, lb31, lb32, lb33⟩ := line_key u b3 cb30 cb31 cb32 cb33 hq3
    have w11 := line_ip u a1 b1 la10 la11 la12 la13
    have w12 := line_ip u a1 b2 la10 la11 la12 la13
    have w13 := line_ip u a1 b3 la10 la11 la12 la13
    have w21 := line_ip u a2 b1 la20 la21 la22 la23
    have w22 := line_ip u a2 b2 la20 la21 la22 la23
    have w23 := line_ip u a2 b3 la20 la21 la22 la23
    have w31 := line_ip u a3 b1 la30 la31 la32 la33
    have w32 := line_ip u a3 b2 la30 la31 la32 la33
    have w33 := line_ip u a3 b3 la30 la31 la32 la33
    have d1 := line_ip u b1 b1 lb10 lb11 lb12 lb13
    have d2 := line_ip u b2 b2 lb20 lb21 lb22 lb23
    have d3 := line_ip u b3 b3 lb30 lb31 lb32 lb33
    have t12 : star (tau u a1) * ip (ww u) b2 + star (tau u a2) * ip (ww u) b1 = 0 := by
      linear_combination (-1 : ℂ) * w12 + (-1 : ℂ) * w21 + dsc u * x12
    have t13 : star (tau u a1) * ip (ww u) b3 + star (tau u a3) * ip (ww u) b1 = 0 := by
      linear_combination (-1 : ℂ) * w13 + (-1 : ℂ) * w31 + dsc u * x13
    have t23 : star (tau u a2) * ip (ww u) b3 + star (tau u a3) * ip (ww u) b2 = 0 := by
      linear_combination (-1 : ℂ) * w23 + (-1 : ℂ) * w32 + dsc u * x23
    have ta1 : tau u a1 ≠ 0 := tau_ne u a1 hdsc ha1 la10 la11 la12 la13
    have ta2 : tau u a2 ≠ 0 := tau_ne u a2 hdsc ha2 la20 la21 la22 la23
    have ta3 : tau u a3 ≠ 0 := tau_ne u a3 hdsc ha3 la30 la31 la32 la33
    have tb1 : ip (ww u) b1 ≠ 0 := ipw_ne u b1 hdsc hb1 d1
    have tb2 : ip (ww u) b2 ≠ 0 := ipw_ne u b2 hdsc hb2 d2
    exact Triangle.contradiction t12 t13 t23 (star_ne_zero.mpr ta3) tb1 tb2

end

end SixQubit.Flip5
