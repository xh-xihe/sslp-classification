import Mathlib
import MainTheory.Gate

/-!
# The residue character, and cyclicity

Theorem 2.6 of `main.tex` begins by dividing the second logical eigenvalue by
the first, observing that this embeds the projective diagonal group into `U(1)`,
and concluding that the group is cyclic because every finite subgroup of `U(1)`
is.  It then identifies the projective order `m` with the additive order of the
residue gap.

Both steps run through one object: the character

    chi(x) = zeta ^ x.val,    x in Z_q,

which converts addition of residues into multiplication of phases.  It is the
algebraic content of the whole SSLP picture -- the gate's eigenvalue on a fiber
is `chi` of that fiber's residue -- and once it is available, cyclicity is one
application of `isCyclic_of_subgroup_isDomain` and the order statement is one
application of `addOrderOf`.

The paper treats both as standard and gives no argument, which is fair; the
point of recording them here is that the identification of `m` with the additive
order of the gap is what makes `m | q` a theorem rather than a convention.
-/

namespace MainTheory.Cyclic

open MainTheory.Gate

variable {q : ℕ} [NeZero q]

/-! ## The character -/

/-- `chi(x) = zeta ^ x.val`: the phase attached to a residue. -/
def chi (zeta : ℂ) (x : ZMod q) : ℂ := zeta ^ x.val

omit [NeZero q] in
@[simp] theorem chi_zero (zeta : ℂ) : chi zeta (0 : ZMod q) = 1 := by
  simp [chi]

omit [NeZero q] in
/-- The gate's eigenvalue on a fiber is `chi` of that fiber's residue. -/
theorem diag_eq_chi {n : ℕ} (zeta : ℂ) (a : Fin n → ZMod q)
    (s : SS.BitString n) : diag zeta a s = chi zeta (SS.weight a s) := rfl

omit [NeZero q] in
/-- `zeta` has order `q`, so its powers only see the exponent modulo `q`. -/
theorem pow_mod (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) (m : ℕ) :
    zeta ^ (m % q) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m q]
  rw [pow_add, pow_mul, hz.pow_eq_one, one_pow, one_mul]

/-- **The character turns residue addition into phase multiplication.** -/
theorem chi_add (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) (x y : ZMod q) :
    chi zeta (x + y) = chi zeta x * chi zeta y := by
  rw [chi, chi, chi, ← pow_add, ZMod.val_add, pow_mod zeta hz]

/-- A power of the character is the character of the multiple. -/
theorem chi_pow (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) (x : ZMod q) (k : ℕ) :
    chi zeta x ^ k = chi zeta (k • x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, succ_nsmul, chi_add zeta hz, mul_comm]

/-- **The character is faithful.** -/
theorem chi_eq_one_iff (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) (x : ZMod q) :
    chi zeta x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hd : q ∣ x.val := (hz.pow_eq_one_iff_dvd _).1 h
    have hv : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x)
    have hx0 : x.val = (0 : ZMod q).val := by rw [hv, ZMod.val_zero]
    exact ZMod.val_injective q hx0
  · rintro rfl
    simp

theorem chi_ne_zero (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) (x : ZMod q) :
    chi zeta x ≠ 0 :=
  pow_ne_zero _ (hz.ne_zero (NeZero.ne q))

theorem chi_injective (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) :
    Function.Injective (chi (q := q) zeta) := by
  intro x y hxy
  have h1 : chi zeta (x - y) * chi zeta y = 1 * chi zeta y := by
    rw [one_mul, ← chi_add zeta hz, sub_add_cancel, hxy]
  have h2 := mul_right_cancel₀ (chi_ne_zero zeta hz y) h1
  exact sub_eq_zero.1 ((chi_eq_one_iff zeta hz _).1 h2)

/-! ## The projective order -/

/-- **The projective logical order is the additive order of the residue gap.**

This is what turns `main.tex`'s `m | q` from a convention into a theorem: the
gap's additive order divides the order of the group `Z_q` it lives in. -/
theorem chi_pow_eq_one_iff (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (delta : ZMod q) (k : ℕ) :
    chi zeta delta ^ k = 1 ↔ addOrderOf delta ∣ k := by
  rw [chi_pow zeta hz, chi_eq_one_iff zeta hz]
  exact (addOrderOf_dvd_iff_nsmul_eq_zero).symm

/-- Hence the projective order divides `q`. -/
theorem addOrderOf_dvd_card (delta : ZMod q) : addOrderOf delta ∣ q := by
  have : addOrderOf delta ∣ Nat.card (ZMod q) := addOrderOf_dvd_natCard delta
  simpa [Nat.card_eq_fintype_card, ZMod.card] using this

/-! ## Cyclicity -/

/-- **Every finite group with a faithful character in a domain is cyclic.**

This is `main.tex`'s "every finite subgroup of `U(1)` is cyclic", which is the
step that makes the projective diagonal group a `C_m`.  Mathlib proves it for
any integral domain. -/
theorem isCyclic_of_faithful {G : Type*} [Group G] [Finite G]
    (f : G →* ℂ) (hf : Function.Injective f) : IsCyclic G :=
  isCyclic_of_subgroup_isDomain f hf

/-! ## Non-vacuity

The order statement is instantiated at a gap the six-qubit development actually
has: orbit 21 sits at `q = 4` with the two fibers at residues `0` and `2`, so
the gap is `2` and the projective order is two. -/

/-- Orbit 21's residue gap has additive order two. -/
theorem addOrderOf_orbit21_gap : addOrderOf ((2 : ZMod 4) - 0) = 2 := by
  rw [sub_zero]
  apply addOrderOf_eq_prime <;> decide

/-- Hence its character has exact projective order two: the gate squares to the
identity on the code and nothing smaller does. -/
theorem orbit21_projective_order (zeta : ℂ) (hz : IsPrimitiveRoot zeta 4) (k : ℕ) :
    chi zeta ((2 : ZMod 4) - 0) ^ k = 1 ↔ 2 ∣ k := by
  rw [chi_pow_eq_one_iff zeta hz, addOrderOf_orbit21_gap]

end MainTheory.Cyclic
