import MainTheory.Gate

/-!
# `six:eq:primitive` is a biconditional

The paper writes

  "The displayed physical operation has exact order `q` precisely when
   `gcd(q, a_1, ..., a_6) = 1`",

and uses both directions: the primitivity reduction of
`lem:six-primitivity-reduction` discards a vector *because* a nonprimitive one
"does not have exact physical order `q`".

`Gate.pow_eq_one_iff` proves one direction only, and takes primitivity as a
hypothesis: for a primitive angle vector, `k` annihilates every basis string
exactly when `q | k`.  Nothing anywhere concluded primitivity *from* the order,
so the reduction's stated justification was unbacked in that direction.

The converse is elementary once the right divisibility is isolated.  If some
`d | q` divides every `(a j).val`, then it divides every subset-sum residue --
`ZMod.val_add` reduces modulo `q`, and `d | q` lets `Nat.dvd_mod_iff` push the
divisibility through the reduction -- so the gate is killed by the exponent
`q / d`, which is smaller than `q` unless `d = 1`.
-/

namespace MainTheory.GatePrimitiveConverse

open MainTheory.Gate

variable {n q : ℕ} [NeZero q]

/-- A divisor of the modulus that divides two residues divides their sum. -/
private theorem dvd_val_add {d : ℕ} (hdq : d ∣ q) {x y : ZMod q}
    (hx : d ∣ x.val) (hy : d ∣ y.val) : d ∣ (x + y).val := by
  rw [ZMod.val_add]
  exact (Nat.dvd_mod_iff hdq).2 (Nat.dvd_add hx hy)

/-- **A common divisor of the modulus and the angle divides every subset-sum
residue.**  This is the arithmetic content of the primitivity reduction. -/
theorem dvd_val_weight {d : ℕ} (hdq : d ∣ q) (a : Fin n → ZMod q)
    (hd : ∀ j, d ∣ (a j).val) (s : SS.BitString n) :
    d ∣ (SS.weight a s).val := by
  classical
  unfold SS.weight
  refine Finset.sum_induction _ (fun z : ZMod q => d ∣ z.val)
    (fun x y hx hy => dvd_val_add hdq hx hy) ?_ ?_
  · simp
  · intro j _
    cases hs : s j
    · simp [SS.bit]
    · simpa [SS.bit, hs] using hd j

/-- **Exact physical order forces primitivity**, the direction of
`six:eq:primitive` that the reduction uses and that nothing proved.

If a nontrivial `d` divided the modulus and every angle, the exponent `q / d`
would already annihilate the gate, so the order could not be `q`. -/
theorem primitive_of_order (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q)
    (h : ∀ k : ℕ, (∀ s : SS.BitString n, diag zeta a s ^ k = 1) → q ∣ k) :
    Primitive q a := by
  intro d hdq hd
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdle : d ≤ q := Nat.le_of_dvd hqpos hdq
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hqpos
  have hkill : ∀ s : SS.BitString n, diag zeta a s ^ (q / d) = 1 := by
    intro s
    obtain ⟨t, ht⟩ := dvd_val_weight hdq a hd s
    rw [diag, ← pow_mul, ht]
    have hexp : d * t * (q / d) = q * t := by
      calc d * t * (q / d) = t * (d * (q / d)) := by ring
        _ = t * q := by rw [Nat.mul_div_cancel' hdq]
        _ = q * t := by ring
    rw [hexp, pow_mul, hz.pow_eq_one, one_pow]
  have hqd : q ∣ q / d := h _ hkill
  have hle : q ≤ q / d := Nat.le_of_dvd (Nat.div_pos hdle hdpos) hqd
  have heq : q / d = q := le_antisymm (Nat.div_le_self q d) hle
  rcases Nat.div_eq_self.1 heq with h0 | h1
  · omega
  · exact h1

/-- **`six:eq:primitive`, both directions.**

The gate `D(a;q)` has exact physical order `q` -- meaning an exponent
annihilates it on every basis string exactly when `q` divides that exponent --
if and only if the angle vector is primitive. -/
theorem primitive_iff_exact_order (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) :
    Primitive q a ↔
      ∀ k : ℕ, (∀ s : SS.BitString n, diag zeta a s ^ k = 1) ↔ q ∣ k := by
  constructor
  · intro hprim k
    exact pow_eq_one_iff zeta hz a hprim k
  · intro h
    exact primitive_of_order zeta hz a fun k hk => (h k).1 hk

end MainTheory.GatePrimitiveConverse
