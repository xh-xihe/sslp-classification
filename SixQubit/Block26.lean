import Mathlib

/-!
# The block algebra behind the orbit 26 no-go

This REPLACES an earlier version that assumed per-edge matrix relations
`D_i C_k^dagger + D_k C_i^dagger = 0`.  Those do not exist: the weight-one masks
carry eight incidences with rank only four and admit no two-term relation, so
only the group-level sums are available.  The argument here uses the CROSS-ANCHOR
contraction of the outer identity, which closes the mixed-axis branch that the
old argument silently assumed away.

Pre-checks, all machine-verified against the Walsh row spaces: the outer
identity's relative sign is `+1` (so the contraction is not vacuous), its form is
the SYMMETRIC `J = [[0,1],[1,0]]` and not the symplectic one (on which the axis
lemma would be false), the anchor scalar's per-block ratio is `-1` uniformly, and
the flipped anchor scalar does not exist.

## Orbit 26, block algebra: the repaired argument

Scalar-level formalisation of the repaired orbit-26 argument.  Vectors in `C^2`
are carried as pairs of complex scalars, so every statement here is pure
commutative algebra over `ℂ` plus a little positivity.
-/

namespace SixQubit.Block26

open scoped ComplexConjugate

/-- Hermitian pairing on `C^2`, `⟪a, b⟫ = conj a . b`, written on components. -/
def ip (a1 a2 b1 b2 : ℂ) : ℂ := conj a1 * b1 + conj a2 * b2

/-- The symmetric antidiagonal form `r J sᵀ = r₁ s₂ + r₂ s₁` on rows of `C^2`. -/
def Jform (r1 r2 s1 s2 : ℂ) : ℂ := r1 * s2 + r2 * s1

@[simp] theorem ip_conj (a1 a2 b1 b2 : ℂ) : conj (ip a1 a2 b1 b2) = ip b1 b2 a1 a2 := by
  simp only [ip, map_add, map_mul, Complex.conj_conj]; ring

/-- `z * conj z` is the squared modulus, as a complex number. -/
theorem mul_conj_self (z : ℂ) : z * conj z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.normSq_eq_conj_mul_self]

/-! ## 1.  The axis lemma -/

/-- Three pairwise `J`-orthogonal rows of `C^2`, none of them zero, lie on one
common coordinate axis.  Self-isotropy of each row is a *consequence* here, not
a hypothesis: the three relations below involve only distinct pairs. -/
theorem axis_lemma (a0 b0 a1 b1 a2 b2 : ℂ)
    (h0 : ¬(a0 = 0 ∧ b0 = 0)) (h1 : ¬(a1 = 0 ∧ b1 = 0)) (h2 : ¬(a2 = 0 ∧ b2 = 0))
    (e01 : Jform a0 b0 a1 b1 = 0) (e02 : Jform a0 b0 a2 b2 = 0)
    (e12 : Jform a1 b1 a2 b2 = 0) :
    (b0 = 0 ∧ b1 = 0 ∧ b2 = 0) ∨ (a0 = 0 ∧ a1 = 0 ∧ a2 = 0) := by
  simp only [Jform] at e01 e02 e12
  by_cases ha0 : a0 = 0
  · -- then `b0 ≠ 0` and the two relations at `0` kill `a1` and `a2`.
    have hb0 : b0 ≠ 0 := fun h => h0 ⟨ha0, h⟩
    have k1 : b0 * a1 = 0 := by linear_combination e01 - b1 * ha0
    have k2 : b0 * a2 = 0 := by linear_combination e02 - b2 * ha0
    exact Or.inr ⟨ha0, (mul_eq_zero.mp k1).resolve_left hb0,
      (mul_eq_zero.mp k2).resolve_left hb0⟩
  · -- the derived consequence `a0 * (b1 * b2) = 0`
    have key : a0 * (b1 * b2) = 0 := by
      linear_combination (b2 / 2) * e01 + (b1 / 2) * e02 - (b0 / 2) * e12
    have hbb : b1 * b2 = 0 := (mul_eq_zero.mp key).resolve_left ha0
    refine Or.inl ?_
    rcases mul_eq_zero.mp hbb with hb1 | hb2
    · have ha1 : a1 ≠ 0 := fun h => h1 ⟨h, hb1⟩
      have k : b0 * a1 = 0 := by linear_combination e01 - a0 * hb1
      have hb0 : b0 = 0 := (mul_eq_zero.mp k).resolve_right ha1
      have k2 : a0 * b2 = 0 := by linear_combination e02 - a2 * hb0
      exact ⟨hb0, hb1, (mul_eq_zero.mp k2).resolve_left ha0⟩
    · have ha2 : a2 ≠ 0 := fun h => h2 ⟨h, hb2⟩
      have k : b0 * a2 = 0 := by linear_combination e02 - a0 * hb2
      have hb0 : b0 = 0 := (mul_eq_zero.mp k).resolve_right ha2
      have k1 : a0 * b1 = 0 := by linear_combination e01 - a1 * hb0
      exact ⟨hb0, (mul_eq_zero.mp k1).resolve_left ha0, hb2⟩

/-- Self-isotropy is a consequence of the axis lemma. -/
theorem axis_isotropic (a0 b0 a1 b1 a2 b2 : ℂ)
    (h0 : ¬(a0 = 0 ∧ b0 = 0)) (h1 : ¬(a1 = 0 ∧ b1 = 0)) (h2 : ¬(a2 = 0 ∧ b2 = 0))
    (e01 : Jform a0 b0 a1 b1 = 0) (e02 : Jform a0 b0 a2 b2 = 0)
    (e12 : Jform a1 b1 a2 b2 = 0) :
    Jform a0 b0 a0 b0 = 0 ∧ Jform a1 b1 a1 b1 = 0 ∧ Jform a2 b2 a2 b2 = 0 := by
  rcases axis_lemma a0 b0 a1 b1 a2 b2 h0 h1 h2 e01 e02 e12 with ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> simp [Jform, p0, p1, p2]

/-! ## 2.  The cross-anchor contraction -/

/-- The `R1` matrix relation for a pair of groups, contracted on the `a` index
with a vector `p` and on the `b` index with `conj q`.

The four hypotheses are the four matrix entries of

  `E_ab = Σ_c conj (C_{2g+c})_a (D_{2h+1-c})_b + Σ_c conj (C_{2h+c})_a (D_{2g+1-c})_b = 0`,

with local block names `c0 = C_{2g}`, `c1 = C_{2g+1}`, `c2 = C_{2h}`,
`c3 = C_{2h+1}` and likewise for `D`.  The conclusion is the literal double sum
`Σ_{a,b} p_a conj q_b E_ab`, rewritten through the two pairings. -/
theorem contract
    (c01 c02 c11 c12 c21 c22 c31 c32 : ℂ)
    (d01 d02 d11 d12 d21 d22 d31 d32 : ℂ) (p1 p2 q1 q2 : ℂ)
    (E11 : conj c01 * d31 + conj c11 * d21 + conj c21 * d11 + conj c31 * d01 = 0)
    (E12 : conj c01 * d32 + conj c11 * d22 + conj c21 * d12 + conj c31 * d02 = 0)
    (E21 : conj c02 * d31 + conj c12 * d21 + conj c22 * d11 + conj c32 * d01 = 0)
    (E22 : conj c02 * d32 + conj c12 * d22 + conj c22 * d12 + conj c32 * d02 = 0) :
    ip c01 c02 p1 p2 * ip q1 q2 d31 d32 + ip c11 c12 p1 p2 * ip q1 q2 d21 d22
      + ip c21 c22 p1 p2 * ip q1 q2 d11 d12 + ip c31 c32 p1 p2 * ip q1 q2 d01 d02 = 0 := by
  simp only [ip]
  linear_combination (p1 * conj q1) * E11 + (p1 * conj q2) * E12
    + (p2 * conj q1) * E21 + (p2 * conj q2) * E22

/-- **Cross-anchor relation.**  Contract `R1` with the `a` slot filled by `D_7`
(`= p`) and the `b` slot by `conj C_6` (`= q`), then substitute the anchor
scalar relations `R2` (`Y^7_i = -X^7_i`).  Writing
`R_g^{(j)} = (X^j_{2g}, X^j_{2g+1})`, the outcome is

  `R_g^{(7)} J R_h^{(6)ᵀ} + R_h^{(7)} J R_g^{(6)ᵀ} = 0`.

Here `X6i := ip C_6 D_i` are definitionally the `b`-slot pairings, while the
`X7i` are abstract scalars tied to the contraction by `R2`. -/
theorem cross_anchor
    (c01 c02 c11 c12 c21 c22 c31 c32 : ℂ)
    (d01 d02 d11 d12 d21 d22 d31 d32 : ℂ) (p1 p2 q1 q2 : ℂ)
    (X70 X71 X72 X73 : ℂ)
    (E11 : conj c01 * d31 + conj c11 * d21 + conj c21 * d11 + conj c31 * d01 = 0)
    (E12 : conj c01 * d32 + conj c11 * d22 + conj c21 * d12 + conj c31 * d02 = 0)
    (E21 : conj c02 * d31 + conj c12 * d21 + conj c22 * d11 + conj c32 * d01 = 0)
    (E22 : conj c02 * d32 + conj c12 * d22 + conj c22 * d12 + conj c32 * d02 = 0)
    (R20 : ip c01 c02 p1 p2 + X70 = 0) (R21 : ip c11 c12 p1 p2 + X71 = 0)
    (R22 : ip c21 c22 p1 p2 + X72 = 0) (R23 : ip c31 c32 p1 p2 + X73 = 0) :
    Jform X70 X71 (ip q1 q2 d21 d22) (ip q1 q2 d31 d32)
      + Jform X72 X73 (ip q1 q2 d01 d02) (ip q1 q2 d11 d12) = 0 := by
  have h := contract c01 c02 c11 c12 c21 c22 c31 c32 d01 d02 d11 d12 d21 d22 d31 d32
    p1 p2 q1 q2 E11 E12 E21 E22
  simp only [Jform]
  linear_combination (-1 : ℂ) * h + (ip q1 q2 d31 d32) * R20 + (ip q1 q2 d21 d22) * R21
    + (ip q1 q2 d11 d12) * R22 + (ip q1 q2 d01 d02) * R23

/-- Putting the **same** anchor in both slots of `cross_anchor` reproduces the
per-anchor relation `R_g^{(j)} J R_h^{(j)ᵀ} = 0`: the cross-anchor relation is
the genuine off-diagonal member of that family. -/
theorem per_anchor
    (c01 c02 c11 c12 c21 c22 c31 c32 : ℂ)
    (d01 d02 d11 d12 d21 d22 d31 d32 : ℂ) (p1 p2 q1 q2 : ℂ)
    (E11 : conj c01 * d31 + conj c11 * d21 + conj c21 * d11 + conj c31 * d01 = 0)
    (E12 : conj c01 * d32 + conj c11 * d22 + conj c21 * d12 + conj c31 * d02 = 0)
    (E21 : conj c02 * d31 + conj c12 * d21 + conj c22 * d11 + conj c32 * d01 = 0)
    (E22 : conj c02 * d32 + conj c12 * d22 + conj c22 * d12 + conj c32 * d02 = 0)
    (R20 : ip c01 c02 p1 p2 + ip q1 q2 d01 d02 = 0)
    (R21 : ip c11 c12 p1 p2 + ip q1 q2 d11 d12 = 0)
    (R22 : ip c21 c22 p1 p2 + ip q1 q2 d21 d22 = 0)
    (R23 : ip c31 c32 p1 p2 + ip q1 q2 d31 d32 = 0) :
    Jform (ip q1 q2 d01 d02) (ip q1 q2 d11 d12) (ip q1 q2 d21 d22) (ip q1 q2 d31 d32)
      = 0 := by
  have h := cross_anchor c01 c02 c11 c12 c21 c22 c31 c32 d01 d02 d11 d12 d21 d22 d31 d32
    p1 p2 q1 q2 (ip q1 q2 d01 d02) (ip q1 q2 d11 d12) (ip q1 q2 d21 d22)
    (ip q1 q2 d31 d32) E11 E12 E21 E22 R20 R21 R22 R23
  simp only [Jform] at h ⊢
  linear_combination h / 2

/-! ## 3.  Branch closures -/

/-- The algebraic core of the mixed branch: `b_g a_h + b_h a_g = 0` for the three
pairs forces one of the six entries to vanish. -/
theorem mixed_core (a0 a1 a2 b0 b1 b2 : ℂ)
    (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (hb1 : b1 ≠ 0)
    (h01 : b0 * a1 + b1 * a0 = 0) (h02 : b0 * a2 + b2 * a0 = 0)
    (h12 : b1 * a2 + b2 * a1 = 0) : False := by
  have key : a0 * (a2 * b1) = 0 := by
    linear_combination (a2 / 2) * h01 - (a1 / 2) * h02 + (a0 / 2) * h12
  rcases mul_eq_zero.mp key with h | h
  · exact ha0 h
  · rcases mul_eq_zero.mp h with h | h
    · exact ha2 h
    · exact hb1 h

/-- **Branch 4a (mixed).**  Anchor 6 sits on the axis `e₁` (rows `(a_g, 0)`),
anchor 7 on `e₂` (rows `(0, b_g)`); the three cross-anchor relations then read
`b_g a_h + b_h a_g = 0`, which is impossible with all six entries nonzero. -/
theorem branch4a (a0 a1 a2 b0 b1 b2 : ℂ)
    (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (hb1 : b1 ≠ 0)
    (h01 : Jform 0 b0 a1 0 + Jform 0 b1 a0 0 = 0)
    (h02 : Jform 0 b0 a2 0 + Jform 0 b2 a0 0 = 0)
    (h12 : Jform 0 b1 a2 0 + Jform 0 b2 a1 0 = 0) : False := by
  simp only [Jform, mul_zero, zero_add] at h01 h02 h12
  exact mixed_core a0 a1 a2 b0 b1 b2 ha0 ha2 hb1 h01 h02 h12

/-- **Branch 3, closing step.**  If one anchor's row for the group `g` vanishes,
the cross-anchor relation degenerates to `d_g J R_h ᵀ = 0`; once the axis lemma
has put `d_g = (p, 0)` with `p ≠ 0`, the second coordinate of every partner row
dies. -/
theorem branch3_step (p s1 s2 : ℂ) (hp : p ≠ 0) (h : Jform p 0 s1 s2 = 0) : s2 = 0 := by
  simp only [Jform, zero_mul, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hp

/-- **Branch 2, step 2.**  If `n nᴴ + m mᴴ = I` with `m` a unit vector and
`n ≠ 0`, then `n ⟂ m`.  Only the first column of the identity and `‖m‖ = 1` are
used for the first coordinate, the second column for the second. -/
theorem unit_pair_orthogonal (n1 n2 m1 m2 : ℂ)
    (M11 : n1 * conj n1 + m1 * conj m1 = 1)
    (M12 : n1 * conj n2 + m1 * conj m2 = 0)
    (M21 : n2 * conj n1 + m2 * conj m1 = 0)
    (M22 : n2 * conj n2 + m2 * conj m2 = 1)
    (hm : ip m1 m2 m1 m2 = 1) (hn : ¬(n1 = 0 ∧ n2 = 0)) :
    ip n1 n2 m1 m2 = 0 := by
  simp only [ip] at hm ⊢
  have k1 : n1 * (conj n1 * m1 + conj n2 * m2) = 0 := by
    linear_combination m1 * M11 + m2 * M12 - m1 * hm
  have k2 : n2 * (conj n1 * m1 + conj n2 * m2) = 0 := by
    linear_combination m1 * M21 + m2 * M22 - m2 * hm
  by_cases h1 : n1 = 0
  · have h2 : n2 ≠ 0 := fun h => hn ⟨h1, h⟩
    exact (mul_eq_zero.mp k2).resolve_left h2
  · exact (mul_eq_zero.mp k1).resolve_left h1

/-- **Branch 2, step 6.**  The final polynomial system
`γ₀c₁₁ + γ₁c₁₀ = 0`, `γ₀c₂₁ + γ₁c₂₀ = 0`, `c₁₀c₂₁ + c₁₁c₂₀ = 0`
has no solution with all six entries nonzero. -/
theorem branch2_step6 (g0 g1 c10 c11 c20 c21 : ℂ)
    (hg1 : g1 ≠ 0) (hc10 : c10 ≠ 0) (hc20 : c20 ≠ 0)
    (h1 : g0 * c11 + g1 * c10 = 0) (h2 : g0 * c21 + g1 * c20 = 0)
    (h3 : c10 * c21 + c11 * c20 = 0) : False := by
  have key : g1 * (c10 * c20) = 0 := by
    linear_combination (-g0 / 2) * h3 + (c20 / 2) * h1 + (c10 / 2) * h2
  rcases mul_eq_zero.mp key with h | h
  · exact hg1 h
  · rcases mul_eq_zero.mp h with h | h
    · exact hc10 h
    · exact hc20 h

/-! ## 4.  Positivity input -/

/-- Lagrange's identity on `C^2`. -/
theorem lagrange (u1 u2 v1 v2 : ℂ) :
    Complex.normSq (ip u1 u2 v1 v2) + Complex.normSq (u1 * v2 - u2 * v1)
      = (Complex.normSq u1 + Complex.normSq u2) * (Complex.normSq v1 + Complex.normSq v2) := by
  simp only [ip, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Cauchy-Schwarz on `C^2` for a unit vector `u`. -/
theorem cauchy_schwarz_unit (u1 u2 v1 v2 : ℂ)
    (hu : Complex.normSq u1 + Complex.normSq u2 = 1) :
    Complex.normSq (ip u1 u2 v1 v2) ≤ Complex.normSq v1 + Complex.normSq v2 := by
  have h := lagrange u1 u2 v1 v2
  rw [hu, one_mul] at h
  nlinarith [Complex.normSq_nonneg (u1 * v2 - u2 * v1)]

/-- **Branch 4b (aligned), analytic core.**  Sandwiching the anchor-group moment
identity with a unit vector `w` orthogonal to `m` gives `2A = e + 3/8 + A` with
`e ≥ 0` the even-block contribution, while Cauchy-Schwarz caps
`A ≤ P₆ + P₇ = 1/4`. -/
theorem branch4b_core (A e P6 P7 : ℝ) (he : 0 ≤ e)
    (hsand : 2 * A = e + 3 / 8 + A) (hcs : A ≤ P6 + P7)
    (hP6 : P6 = 1 / 8) (hP7 : P7 = 1 / 8) : False := by
  subst hP6; subst hP7; linarith

/-- **Branch 4b (aligned), assembled.**  `w` is a unit vector, `C₆`, `C₇` the two
anchor blocks with `P₆ = P₇ = 1/8`, `A` the Rayleigh contribution of the anchor
group at `w`, and `e ≥ 0` the even-block contribution. -/
theorem branch4b (w1 w2 c61 c62 c71 c72 : ℂ) (e : ℝ) (he : 0 ≤ e)
    (hw : Complex.normSq w1 + Complex.normSq w2 = 1)
    (hP6 : Complex.normSq c61 + Complex.normSq c62 = 1 / 8)
    (hP7 : Complex.normSq c71 + Complex.normSq c72 = 1 / 8)
    (hsand : 2 * (Complex.normSq (ip w1 w2 c61 c62) + Complex.normSq (ip w1 w2 c71 c72))
      = e + 3 / 8 + (Complex.normSq (ip w1 w2 c61 c62) + Complex.normSq (ip w1 w2 c71 c72))) :
    False := by
  have h6 := cauchy_schwarz_unit w1 w2 c61 c62 hw
  have h7 := cauchy_schwarz_unit w1 w2 c71 c72 hw
  rw [hP6] at h6
  rw [hP7] at h7
  linarith

/-- **Branch 1.**  Two blocks whose outer products sum to `(5/8) v vᴴ - (1/8) I`
cannot exist: sandwiching with a unit vector `u ⟂ v` makes a sum of two squared
moduli equal to `-1/8`. -/
theorem branch1 (u1 u2 v1 v2 k1 k2 j1 j2 : ℂ)
    (hu : ip u1 u2 u1 u2 = 1) (huv : ip u1 u2 v1 v2 = 0)
    (M11 : k1 * conj k1 + j1 * conj j1 = 5 / 8 * (v1 * conj v1) - 1 / 8)
    (M12 : k1 * conj k2 + j1 * conj j2 = 5 / 8 * (v1 * conj v2))
    (M21 : k2 * conj k1 + j2 * conj j1 = 5 / 8 * (v2 * conj v1))
    (M22 : k2 * conj k2 + j2 * conj j2 = 5 / 8 * (v2 * conj v2) - 1 / 8) : False := by
  have key : ip u1 u2 k1 k2 * ip k1 k2 u1 u2 + ip u1 u2 j1 j2 * ip j1 j2 u1 u2
      = 5 / 8 * (ip u1 u2 v1 v2 * ip v1 v2 u1 u2) - 1 / 8 * ip u1 u2 u1 u2 := by
    simp only [ip]
    linear_combination (conj u1 * u1) * M11 + (conj u1 * u2) * M12
      + (conj u2 * u1) * M21 + (conj u2 * u2) * M22
  rw [← ip_conj u1 u2 k1 k2, ← ip_conj u1 u2 j1 j2, ← ip_conj u1 u2 v1 v2,
    mul_conj_self, mul_conj_self, mul_conj_self, huv, hu] at key
  simp only [map_zero, Complex.ofReal_zero, mul_zero, mul_one, zero_sub] at key
  have hcast : ((Complex.normSq (ip u1 u2 k1 k2) + Complex.normSq (ip u1 u2 j1 j2) : ℝ) : ℂ)
      = ((-(1 / 8 : ℝ) : ℝ) : ℂ) := by push_cast; linear_combination key
  have hre : Complex.normSq (ip u1 u2 k1 k2) + Complex.normSq (ip u1 u2 j1 j2)
      = -(1 / 8 : ℝ) := Complex.ofReal_inj.mp hcast
  nlinarith [Complex.normSq_nonneg (ip u1 u2 k1 k2), Complex.normSq_nonneg (ip u1 u2 j1 j2)]

/-! ## 5.  Assembled branches 4 and 3 -/

/-- **Branch 4, assembled.**  Both anchors have all three rows nonzero, so each
one has an axis by `axis_lemma`; the cross-anchor relations then rule out the
mixed configuration, and the two anchors must share an axis.

Rows are `R_g^{(6)} = (X6 (2g), X6 (2g+1))` and likewise for anchor 7.  `A6*`
and `A7*` are the per-anchor `R1` contractions, `C*` the cross-anchor ones. -/
theorem branch4_aligned
    (X60 X61 X62 X63 X64 X65 X70 X71 X72 X73 X74 X75 : ℂ)
    (n60 : ¬(X60 = 0 ∧ X61 = 0)) (n61 : ¬(X62 = 0 ∧ X63 = 0))
    (n62 : ¬(X64 = 0 ∧ X65 = 0)) (n70 : ¬(X70 = 0 ∧ X71 = 0))
    (n71 : ¬(X72 = 0 ∧ X73 = 0)) (n72 : ¬(X74 = 0 ∧ X75 = 0))
    (A601 : Jform X60 X61 X62 X63 = 0) (A602 : Jform X60 X61 X64 X65 = 0)
    (A612 : Jform X62 X63 X64 X65 = 0)
    (A701 : Jform X70 X71 X72 X73 = 0) (A702 : Jform X70 X71 X74 X75 = 0)
    (A712 : Jform X72 X73 X74 X75 = 0)
    (C01 : Jform X70 X71 X62 X63 + Jform X72 X73 X60 X61 = 0)
    (C02 : Jform X70 X71 X64 X65 + Jform X74 X75 X60 X61 = 0)
    (C12 : Jform X72 X73 X64 X65 + Jform X74 X75 X62 X63 = 0) :
    (X61 = 0 ∧ X63 = 0 ∧ X65 = 0 ∧ X71 = 0 ∧ X73 = 0 ∧ X75 = 0)
      ∨ (X60 = 0 ∧ X62 = 0 ∧ X64 = 0 ∧ X70 = 0 ∧ X72 = 0 ∧ X74 = 0) := by
  simp only [Jform] at C01 C02 C12
  rcases axis_lemma X60 X61 X62 X63 X64 X65 n60 n61 n62 A601 A602 A612 with
    ⟨u0, u1, u2⟩ | ⟨u0, u1, u2⟩ <;>
  rcases axis_lemma X70 X71 X72 X73 X74 X75 n70 n71 n72 A701 A702 A712 with
    ⟨v0, v1, v2⟩ | ⟨v0, v1, v2⟩
  · exact Or.inl ⟨u0, u1, u2, v0, v1, v2⟩
  · -- mixed: anchor 6 on `e₁`, anchor 7 on `e₂`
    exfalso
    have ha0 : X60 ≠ 0 := fun h => n60 ⟨h, u0⟩
    have ha2 : X64 ≠ 0 := fun h => n62 ⟨h, u2⟩
    have hb1 : X73 ≠ 0 := fun h => n71 ⟨v1, h⟩
    refine mixed_core X60 X62 X64 X71 X73 X75 ha0 ha2 hb1 ?_ ?_ ?_
    · linear_combination C01 - X63 * v0 - X72 * u0
    · linear_combination C02 - X65 * v0 - X74 * u0
    · linear_combination C12 - X65 * v1 - X74 * u1
  · -- mixed: anchor 6 on `e₂`, anchor 7 on `e₁`
    exfalso
    have ha0 : X61 ≠ 0 := fun h => n60 ⟨u0, h⟩
    have ha2 : X65 ≠ 0 := fun h => n62 ⟨u2, h⟩
    have hb1 : X72 ≠ 0 := fun h => n71 ⟨h, v1⟩
    refine mixed_core X61 X63 X65 X70 X72 X74 ha0 ha2 hb1 ?_ ?_ ?_
    · linear_combination C01 - X62 * v0 - X73 * u0
    · linear_combination C02 - X64 * v0 - X75 * u0
    · linear_combination C12 - X64 * v1 - X75 * u1
  · exact Or.inr ⟨u0, u1, u2, v0, v1, v2⟩

/-- **Branch 3, assembled.**  Anchor 6 kills exactly the group `0`
(`R_0^{(6)} = 0`, the other two rows nonzero) while `d := R_0^{(7)} ≠ 0`.  The
cross-anchor relations degenerate to `d J R_h^{(6)ᵀ} = 0`, so `d` together with
the two surviving anchor-6 rows is a pairwise `J`-orthogonal triple; the axis
lemma puts them on a common axis, and the per-anchor relations for anchor 7 then
propagate that axis to the whole of anchor 7.  The outcome is the aligned
configuration of branch 4b. -/
theorem branch3_aligned
    (X60 X61 X62 X63 X64 X65 X70 X71 X72 X73 X74 X75 : ℂ)
    (hZ0 : X60 = 0) (hZ1 : X61 = 0)
    (n61 : ¬(X62 = 0 ∧ X63 = 0)) (n62 : ¬(X64 = 0 ∧ X65 = 0))
    (n70 : ¬(X70 = 0 ∧ X71 = 0))
    (A612 : Jform X62 X63 X64 X65 = 0)
    (A701 : Jform X70 X71 X72 X73 = 0) (A702 : Jform X70 X71 X74 X75 = 0)
    (C01 : Jform X70 X71 X62 X63 + Jform X72 X73 X60 X61 = 0)
    (C02 : Jform X70 X71 X64 X65 + Jform X74 X75 X60 X61 = 0) :
    (X61 = 0 ∧ X63 = 0 ∧ X65 = 0 ∧ X71 = 0 ∧ X73 = 0 ∧ X75 = 0)
      ∨ (X60 = 0 ∧ X62 = 0 ∧ X64 = 0 ∧ X70 = 0 ∧ X72 = 0 ∧ X74 = 0) := by
  simp only [Jform] at C01 C02 A701 A702
  -- the cross relations reduce to `d J R_h^{(6)ᵀ} = 0`
  have D1 : Jform X70 X71 X62 X63 = 0 := by
    simp only [Jform]; linear_combination C01 - X73 * hZ0 - X72 * hZ1
  have D2 : Jform X70 X71 X64 X65 = 0 := by
    simp only [Jform]; linear_combination C02 - X75 * hZ0 - X74 * hZ1
  rcases axis_lemma X70 X71 X62 X63 X64 X65 n70 n61 n62 D1 D2 A612 with
    ⟨w0, w1, w2⟩ | ⟨w0, w1, w2⟩
  · -- common axis `e₁`
    have h70 : X70 ≠ 0 := fun h => n70 ⟨h, w0⟩
    have k1 : X73 = 0 := by
      have : X70 * X73 = 0 := by linear_combination A701 - X72 * w0
      exact (mul_eq_zero.mp this).resolve_left h70
    have k2 : X75 = 0 := by
      have : X70 * X75 = 0 := by linear_combination A702 - X74 * w0
      exact (mul_eq_zero.mp this).resolve_left h70
    exact Or.inl ⟨hZ1, w1, w2, w0, k1, k2⟩
  · -- common axis `e₂`
    have h71 : X71 ≠ 0 := fun h => n70 ⟨w0, h⟩
    have k1 : X72 = 0 := by
      have : X71 * X72 = 0 := by linear_combination A701 - X73 * w0
      exact (mul_eq_zero.mp this).resolve_left h71
    have k2 : X74 = 0 := by
      have : X71 * X74 = 0 := by linear_combination A702 - X75 * w0
      exact (mul_eq_zero.mp this).resolve_left h71
    exact Or.inr ⟨hZ0, w1, w2, w0, k1, k2⟩

/-- **Branch 1, from more primitive input.**  With `rho = (1/2)(w wᴴ + v vᴴ)`
supplied by the group moment identity `(M)` plus `(T)`, the anchor block `x`
orthogonal to `v` with `‖x‖² = 1/8` giving `x xᴴ = (1/8)(I - v vᴴ)`, and the
remaining two blocks `k`, `j`, the subtraction step of branch 1 produces exactly
the matrix identity fed to `branch1`. -/
theorem branch1_full (u1 u2 v1 v2 w1 w2 k1 k2 j1 j2 x1 x2 : ℂ)
    (hu : ip u1 u2 u1 u2 = 1) (huv : ip u1 u2 v1 v2 = 0)
    (S11 : k1 * conj k1 + j1 * conj j1 + 1 / 2 * (w1 * conj w1) + x1 * conj x1
      = 1 / 2 * (w1 * conj w1 + v1 * conj v1))
    (S12 : k1 * conj k2 + j1 * conj j2 + 1 / 2 * (w1 * conj w2) + x1 * conj x2
      = 1 / 2 * (w1 * conj w2 + v1 * conj v2))
    (S21 : k2 * conj k1 + j2 * conj j1 + 1 / 2 * (w2 * conj w1) + x2 * conj x1
      = 1 / 2 * (w2 * conj w1 + v2 * conj v1))
    (S22 : k2 * conj k2 + j2 * conj j2 + 1 / 2 * (w2 * conj w2) + x2 * conj x2
      = 1 / 2 * (w2 * conj w2 + v2 * conj v2))
    (A11 : x1 * conj x1 = 1 / 8 * (1 - v1 * conj v1))
    (A12 : x1 * conj x2 = -(1 / 8) * (v1 * conj v2))
    (A21 : x2 * conj x1 = -(1 / 8) * (v2 * conj v1))
    (A22 : x2 * conj x2 = 1 / 8 * (1 - v2 * conj v2)) : False := by
  refine branch1 u1 u2 v1 v2 k1 k2 j1 j2 hu huv ?_ ?_ ?_ ?_
  · linear_combination S11 - A11
  · linear_combination S12 - A12
  · linear_combination S21 - A21
  · linear_combination S22 - A22

end SixQubit.Block26
