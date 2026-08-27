import Mathlib
import SS.Basic
import SS.Pauli
import SS.DiagonalAction

/-!
# The diagonal gate `D(a;q)` and primitivity

`main.tex` works throughout with the diagonal gate

    D(a;q) |x> = zeta_q ^ (A_a(x)) |x>,    A_a(x) = sum_j a_j x_j  mod q,

and calls the angle vector *primitive* when `gcd(q, a_1, ..., a_n) = 1`
(eq. 2.5).  It then uses, repeatedly and without proof, that primitivity is
exactly what makes the physical order of the gate equal to `q` rather than a
proper divisor.

This file supplies the gate, the subset-sum eigenvalue, and that equivalence.

The subset-sum residue `A_a` is already in the repository as `SS.weight`, and it
is already generic in `n`; what is added here is the gate itself, its order, and
the two directions of the primitivity criterion.  Note that the whole argument
stays inside `ZMod q`: the eigenvalue condition is turned into a linear condition
on residues before any natural-number divisibility appears, which avoids the
usual `ZMod.val` bookkeeping.
-/

namespace MainTheory.Gate

open SS

variable {n q : ℕ} [NeZero q]

/-! ## The gate -/

/-- The eigenvalue of `D(a;q)` on the basis string `s`. -/
def diag (zeta : ℂ) (a : Fin n → ZMod q) (s : BitString n) : ℂ :=
  zeta ^ (SS.weight a s).val

/-- The gate itself, as a map on amplitude vectors. -/
def gate (zeta : ℂ) (a : Fin n → ZMod q) (psi : SS.State n ℂ) : SS.State n ℂ :=
  fun s => diag zeta a s * psi s

/-! ## The subset-sum residue on a single coordinate -/

omit [NeZero q] in
/-- On a one-hot string the residue is the corresponding angle. -/
@[simp] theorem weight_stdBasis (a : Fin n → ZMod q) (j : Fin n) :
    SS.weight a (SS.stdBasis j) = a j := by
  classical
  rw [SS.weight, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [SS.stdBasis_apply_ne hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ## Iterating the gate

The `k`-th power of the gate is the gate of the scaled angle vector, so the
whole order question is a statement about residues. -/

omit [NeZero q] in
theorem diag_pow (zeta : ℂ) (a : Fin n → ZMod q) (s : BitString n) (k : ℕ) :
    diag zeta a s ^ k = zeta ^ (k * (SS.weight a s).val) := by
  rw [diag, ← pow_mul, mul_comm]

omit [NeZero q] in
/-- The scaled residue, which is what the `k`-th power sees. -/
theorem natCast_mul_weight (a : Fin n → ZMod q) (s : BitString n) (k : ℕ) :
    (k : ZMod q) * SS.weight a s = SS.weight (fun i => (k : ZMod q) * a i) s := by
  rw [SS.weight, SS.weight, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Primitivity -/

/-- `main.tex` eq. 2.5: the angle vector is primitive when no `d > 1` divides `q`
and every angle.  Stated as a descent, which is the form the proofs use. -/
def Primitive (q : ℕ) (a : Fin n → ZMod q) : Prop :=
  ∀ d : ℕ, d ∣ q → (∀ j, d ∣ (a j).val) → d = 1

/-- The cancellation, with the gcd already split off so that no rewrite has to
touch `Nat.gcd k q` -- rewriting `k` inside it is what makes the direct version
fail. -/
private theorem dvd_of_split {g k' q' v : ℕ} (hgpos : 0 < g)
    (hcop : Nat.Coprime k' q') (h : g * q' ∣ g * k' * v) : q' ∣ v := by
  rw [mul_assoc] at h
  exact hcop.symm.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hgpos).1 h)

/-- The pure arithmetic behind primitivity. -/
private theorem dvd_div_gcd_of_dvd_mul {k q v : ℕ} (hqpos : 0 < q)
    (h : q ∣ k * v) : q / Nat.gcd k q ∣ v := by
  have hgpos : 0 < Nat.gcd k q := Nat.gcd_pos_of_pos_right k hqpos
  refine dvd_of_split hgpos (Nat.coprime_div_gcd_div_gcd hgpos) ?_
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right k q),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left k q)]
  exact h

/-- The key step: against a primitive angle vector, `k` annihilates every angle
only if `q` divides `k`. -/
theorem dvd_of_forall_mul_eq_zero (a : Fin n → ZMod q) (hprim : Primitive q a)
    (k : ℕ) (h : ∀ j, (k : ZMod q) * a j = 0) : q ∣ k := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hkey : ∀ j, q / Nat.gcd k q ∣ (a j).val := by
    intro j
    refine dvd_div_gcd_of_dvd_mul hqpos ?_
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact h j
  have hone : q / Nat.gcd k q = 1 :=
    hprim _ (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right k q)) hkey
  have hq : q = Nat.gcd k q := by
    conv_lhs => rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right k q)]
    rw [hone, mul_one]
  rw [hq]
  exact Nat.gcd_dvd_left k q

/-! ## The order of the gate -/

/-- **Primitivity is exactly exactness of the physical order.**

For a primitive `q`-th root of unity `zeta` and a primitive angle vector, the
gate `D(a;q)` acts trivially on every basis string only when `q` divides the
exponent.  This is the fact `main.tex` uses whenever it says `D(a;q)` has exact
physical order `q`. -/
theorem pow_eq_one_iff (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (hprim : Primitive q a) (k : ℕ) :
    (∀ s : BitString n, diag zeta a s ^ k = 1) ↔ q ∣ k := by
  constructor
  · intro hk
    refine dvd_of_forall_mul_eq_zero a hprim k (fun j => ?_)
    have := hk (SS.stdBasis j)
    rw [diag_pow] at this
    have hdvd : q ∣ k * (SS.weight a (SS.stdBasis j)).val :=
      (hz.pow_eq_one_iff_dvd _).1 this
    have : ((k * (SS.weight a (SS.stdBasis j)).val : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at this
    rw [ZMod.natCast_val, ZMod.cast_id, weight_stdBasis] at this
    exact this
  · intro hk s
    rw [diag_pow]
    refine (hz.pow_eq_one_iff_dvd _).2 ?_
    exact Dvd.dvd.mul_right hk _

/-! ## The criterion has content

Both directions are exhibited: an angle vector that is primitive, and one that
is not.  Without the second, `Primitive` could be a predicate that happens to
hold everywhere and the order theorem would say nothing. -/

/-- Orbit 21's angle vector `(1,1,1,2,2,3)` at `q = 4` is primitive. -/
theorem primitive_orbit21 : Primitive 4 ![(1 : ZMod 4), 1, 1, 2, 2, 3] := by
  intro d _ hd
  have h0 := hd 0
  have hv : ((![(1 : ZMod 4), 1, 1, 2, 2, 3] : Fin 6 → ZMod 4) 0).val = 1 := by
    decide
  rw [hv] at h0
  exact Nat.dvd_one.1 h0

/-- An imprimitive one: every angle even at `q = 4`, so `d = 2` witnesses
failure and the gate has order two, not four. -/
theorem not_primitive_allEven : ¬ Primitive 4 ![(2 : ZMod 4), 2, 2, 2, 2, 2] := by
  intro h
  have h2 := h 2 (by norm_num) (by decide)
  norm_num at h2

/-- The two halves combined: orbit 21's gate has exact physical order four.

This instantiates `pow_eq_one_iff` at a vector the six-qubit development
actually uses, so the order theorem is known to apply to something. -/
theorem orbit21_order (zeta : ℂ) (hz : IsPrimitiveRoot zeta 4) (k : ℕ) :
    (∀ s : BitString 6, diag zeta ![(1 : ZMod 4), 1, 1, 2, 2, 3] s ^ k = 1)
      ↔ 4 ∣ k :=
  pow_eq_one_iff zeta hz _ primitive_orbit21 k

end MainTheory.Gate
