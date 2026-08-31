import Mathlib
import MainTheory.Gate
import MainTheory.PhaseSector
import MainTheory.Normalize
import MainTheory.Cyclic

/-!
# The two-fiber normal form

Theorem 2.6 of `main.tex` is the result that licenses everything the six-qubit
development does: an exact `((n,2,d))` code with a nontrivial projective diagonal
group can be put, up to a list of equivalences, in the form where the two
logical words are supported in two residue fibers of a primitive angle vector.

**What is proved here, and what is not.**  An adversarial audit of an earlier
draft of this file found the omissions understated, so they are listed in full.

Not proved, and not assumed silently:

* Finiteness of the projective diagonal group.  The paper gets it from its
  Theorem 2.5 by compact-Lie-group theory, which needs Cartan's closed-subgroup
  theorem; Mathlib does not have it.  The gate is given as data here.
* Theorem 2.4 itself.  The *existence* of the primitive finite lift `D(a;q)`,
  obtained by rationalizing the augmented system, is likewise assumed by taking
  `zeta`, `q` and `a` as data.  `MainTheory/Rationalize.lean` and
  `MainTheory/Denominator.lean` supply its ingredients but are not wired in.
* The code-theoretic layer.  No projector, no Knill-Laflamme system, no
  distance, no `((n,2,d))` code appears; `d >= 2` and the `Z_j` detection it
  buys are nowhere used.  The eigenvector structure is a hypothesis, not a
  consequence of a gate preserving a code.
* The projective group as a group.  `addOrderOf delta` is the order of *one*
  gate's action, which in general only divides the paper's `m`, the order of the
  whole group; identifying them needs cyclicity plus a choice of generator.
* The sorted canonical form `0 <= a_1 <= ... <= a_n < q` and the qubit
  permutation that produces it.
* Orthonormality of the pair, and hence that the span is a code.

Proved here: the geometric content of the forward direction
(`normal_form_core`), that distinct eigenvalues force a nonzero gap
(`gap_ne_zero`), the coprime-power normalization that puts the second fiber at
`q/m` (`exists_unit_mul_eq_div`), and the converse's arithmetic core
(`order_of_two_fiber`).

The coprime-power step deserves a word.  An earlier draft filed it under "the
quotient by equivalences" and dropped it.  That was wrong: it is a proved
arithmetic lemma, and it is the only reason the paper may write `S_{q/m}` rather
than `S_{(q/m)c}`.  It is also entirely elementary, so it is proved below.
-/

namespace MainTheory.RankTwo

open SS MainTheory.Gate MainTheory.Cyclic MainTheory.Normalize

variable {n q : ℕ} [NeZero q]

/-! ## The forward direction, geometric content -/

/-- **The two-fiber form.**

Given a gate acting diagonally on the two logical words, conjugation by an `X`
string drawn from the first word's support puts that word in the residue-zero
fiber and the other in a single fiber `delta`; the ratio of the two eigenvalues
is the character of `delta`, and its multiplicative order is the additive order
of `delta`.

This is Theorem 2.6's content minus the canonicalization; see the module
docstring for exactly what is left out. -/
theorem normal_form_core (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (c d : SS.State n ℂ) (lc ld : ℂ)
    (hc : gate zeta a c = fun s => lc * c s)
    (hd : gate zeta a d = fun s => ld * d s)
    (x0 y0 : BitString n) (hx0 : c x0 ≠ 0) (hy0 : d y0 ≠ 0) :
    ∃ delta : ZMod q,
      delta = SS.weight a y0 - SS.weight a x0 ∧
      SS.SSConditionState (flip a x0) 0 (fun s => c (SS.bxor s x0)) ∧
      SS.SSConditionState (flip a x0) delta (fun s => d (SS.bxor s x0)) ∧
      ld / lc = chi zeta delta ∧
      ∀ k : ℕ, (ld / lc) ^ k = 1 ↔ addOrderOf delta ∣ k := by
  have hssc : SS.SSConditionState a (SS.weight a x0) c :=
    PhaseSector.ssCondition_of_eigen zeta hz a c lc hc x0 hx0
  have hssd : SS.SSConditionState a (SS.weight a y0) d :=
    PhaseSector.ssCondition_of_eigen zeta hz a d ld hd y0 hy0
  have hlc : lc = chi zeta (SS.weight a x0) := by
    rw [← diag_eq_chi]
    exact (PhaseSector.diag_eq_of_eigen zeta a c lc hc x0 hx0).symm
  have hld : ld = chi zeta (SS.weight a y0) := by
    rw [← diag_eq_chi]
    exact (PhaseSector.diag_eq_of_eigen zeta a d ld hd y0 hy0).symm
  have hratio : ld / lc = chi zeta (SS.weight a y0 - SS.weight a x0) := by
    rw [chi_sub zeta hz, hlc, hld]
  refine ⟨ SS.weight a y0 - SS.weight a x0, rfl, ?_, ?_, hratio, ?_ ⟩
  · have h := Normalize.ssCondition_bxor a x0 (SS.weight a x0) c hssc
    simpa using h
  · exact Normalize.ssCondition_bxor a x0 (SS.weight a y0) d hssd
  · intro k
    rw [hratio]
    exact chi_pow_eq_one_iff zeta hz _ k

/-! ## The converse direction -/

/-- The additive order of `q / m` in `Z_q` is `m`.  This is what makes `q / m`
the right second residue in the normal form. -/
theorem addOrderOf_div (m : ℕ) (hmq : m ∣ q) :
    addOrderOf (((q / m : ℕ)) : ZMod q) = m := by
  rw [ZMod.addOrderOf_coe _ (NeZero.ne q), Nat.gcd_eq_right (Nat.div_dvd_of_dvd hmq)]
  exact Nat.div_div_self hmq (NeZero.ne q)

/-- **The converse of the normal form.**

A pair supported in the residue-`0` and residue-`q/m` fibers is acted on
diagonally by the gate, and the projective order of that action is exactly `m`.
This is the second half of Theorem 2.6, and unlike the first half it is
complete. -/
theorem order_of_two_fiber (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (m : ℕ) (hmq : m ∣ q)
    (a : Fin n → ZMod q) (c d : SS.State n ℂ)
    (hc : SS.SSConditionState a 0 c)
    (hd : SS.SSConditionState a (((q / m : ℕ)) : ZMod q) d) :
    gate zeta a c = (fun s => (1 : ℂ) * c s) ∧
      gate zeta a d = (fun s => chi zeta (((q / m : ℕ)) : ZMod q) * d s) ∧
      ∀ k : ℕ, chi zeta (((q / m : ℕ)) : ZMod q) ^ k = 1 ↔ m ∣ k := by
  refine ⟨ ?_, ?_, ?_ ⟩
  · have h := PhaseSector.eigen_of_ssCondition zeta a c 0 hc
    simpa using h
  · exact PhaseSector.eigen_of_ssCondition zeta a d _ hd
  · intro k
    rw [chi_pow_eq_one_iff zeta hz, addOrderOf_div m hmq]

/-! ## Non-vacuity, and one caveat

`normal_form_core` has satisfiable hypotheses: any two basis strings give a pair
of eigenvectors to feed it.

The caveat concerns `order_of_two_fiber`.  Its third conclusion -- that the
character of `q/m` has multiplicative order exactly `m` -- does not mention `c`
or `d` at all, and holds whether or not they are nonzero.  The paper's converse
assumes an *orthonormal* pair satisfying the full Knill-Laflamme system;
orthonormality is not imposed here, so the first two conclusions are weak when
the states vanish.  The order statement, which is the point, is unaffected. -/

omit [NeZero q] in
/-- The hypotheses of `normal_form_core` are satisfiable. -/
theorem normal_form_nonvacuous (zeta : ℂ) (a : Fin n → ZMod q)
    (x0 y0 : BitString n) :
    ∃ (c d : SS.State n ℂ) (lc ld : ℂ),
      gate zeta a c = (fun s => lc * c s) ∧ gate zeta a d = (fun s => ld * d s) ∧
        c x0 ≠ 0 ∧ d y0 ≠ 0 := by
  obtain ⟨ c, hcx, hc ⟩ := PhaseSector.exists_eigen zeta a x0
  obtain ⟨ d, hdy, hd ⟩ := PhaseSector.exists_eigen zeta a y0
  exact ⟨ c, d, _, _, hc, hd, hcx, hdy ⟩

omit [NeZero q] in
/-- **Nontriviality.**  Distinct logical eigenvalues force a nonzero gap.

Theorem 2.6 assumes projective nontriviality -- "its two logical eigenvalues are
distinct" -- and concludes `C_m` with `m >= 2`.  `normal_form_core` does not
assume it, so it admits `delta = 0`, which is the projectively trivial case the
paper excludes; this is what recovers the paper's situation. -/
theorem gap_ne_zero (zeta : ℂ)
    (a : Fin n → ZMod q) (c d : SS.State n ℂ) (lc ld : ℂ)
    (hc : gate zeta a c = fun s => lc * c s)
    (hd : gate zeta a d = fun s => ld * d s)
    (x0 y0 : BitString n) (hx0 : c x0 ≠ 0) (hy0 : d y0 ≠ 0)
    (hne : lc ≠ ld) :
    SS.weight a y0 - SS.weight a x0 ≠ 0 := by
  intro hzero
  apply hne
  have hlc : lc = chi zeta (SS.weight a x0) := by
    rw [← diag_eq_chi]
    exact (PhaseSector.diag_eq_of_eigen zeta a c lc hc x0 hx0).symm
  have hld : ld = chi zeta (SS.weight a y0) := by
    rw [← diag_eq_chi]
    exact (PhaseSector.diag_eq_of_eigen zeta a d ld hd y0 hy0).symm
  rw [hlc, hld, sub_eq_zero.1 hzero]

/-! ## The coprime-power normalization

`main.tex` writes the residue gap as `(q/m) c` with `gcd(c,m) = 1`, then replaces
the generator by a `u`-th power to make the gap exactly `q/m`.  The audit of an
earlier draft of this file was right that calling that step "bookkeeping" was
wrong: it is a proved arithmetic lemma, and it is the only reason the paper may
write `S_{q/m}` rather than `S_{(q/m)c}` in the normal form.  It is also fully
elementary, so there is no excuse for leaving it out. -/

/-- **Any gap of additive order `m` can be scaled to `q/m` by a unit.** -/
theorem exists_unit_mul_eq_div (delta : ZMod q) (m : ℕ)
    (hm : addOrderOf delta = m) :
    ∃ u : (ZMod q)ˣ, (u : ZMod q) * delta = (((q / m : ℕ)) : ZMod q) := by
  have hqne : q ≠ 0 := NeZero.ne q
  have hmq : m ∣ q := hm ▸ addOrderOf_dvd_card delta
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmq (Nat.pos_of_ne_zero hqne)
  set dv := delta.val with hdv
  have hcast : ((dv : ℕ) : ZMod q) = delta := by
    rw [hdv, ZMod.natCast_val, ZMod.cast_id]
  -- the additive order pins the gcd
  have hord : q / Nat.gcd q dv = m := by
    rw [← hm, ← hcast, ZMod.addOrderOf_coe _ hqne]
  set g := Nat.gcd q dv with hg
  have hgq : g ∣ q := Nat.gcd_dvd_left q dv
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left dv (Nat.pos_of_ne_zero hqne)
  have hgm : g * m = q := by rw [← hord]; exact Nat.mul_div_cancel' hgq
  have hgeq : q / m = g := by
    rw [← hgm, Nat.mul_div_cancel _ hmpos]
  -- the cofactor is coprime to m
  set cc := dv / g with hcc
  have hdvc : g * cc = dv := Nat.mul_div_cancel' (Nat.gcd_dvd_right q dv)
  have hcop : Nat.Coprime cc m := by
    have := Nat.coprime_div_gcd_div_gcd (m := q) (n := dv) hgpos
    rw [← hg] at this
    have hqg : q / g = m := by rw [← hord]
    rw [hqg] at this
    exact this.symm
  -- lift the inverse of the cofactor
  have hunit : IsUnit ((cc : ℕ) : ZMod m) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hcop
  obtain ⟨ u, hu ⟩ := Normalize.exists_unit_mul_eq_one hmq hunit.unit
  refine ⟨ u, ?_ ⟩
  -- transport the congruence up
  have hmodm : ((u : ZMod q).val * cc) ≡ 1 [MOD  m ] := by
    have h1 : (((u : ZMod q).val * cc : ℕ) : ZMod m) = 1 := by
      push_cast
      rw [ZMod.natCast_val]
      simpa [IsUnit.unit_spec] using hu
    simpa [Nat.ModEq] using (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using h1)
  have hmodq : (g * ((u : ZMod q).val * cc)) ≡ (g * 1) [MOD  g * m ] :=
    Nat.ModEq.mul_left' g hmodm
  rw [hgm] at hmodq
  have hfin : ((g * ((u : ZMod q).val * cc) : ℕ) : ZMod q) = ((g * 1 : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmodq
  rw [hgeq, ← hcast, ← hdvc]
  push_cast at hfin ⊢
  rw [ZMod.natCast_val, ZMod.cast_id] at hfin
  linear_combination hfin

/-- In `ZMod q` every additive order divides `q`.

**This is Lagrange, and it is not `main.tex` eq. `eq:K2-bound`.**  It holds for
every element of every `ZMod q` and says nothing about a gate or a code.  The
paper's `m | q` is the much stronger statement that the projective *logical*
order of a code-preserving `D(theta)` with real angles divides the exact
*physical* order of its primitive lift, and its proof runs through the whole
rationalization chain -- the common first moment, the row-span relation, the
binary pivot solve, and the minimality of `q`.  None of that is established
here.  Recorded under its true name so the two are not confused. -/
theorem addOrderOf_dvd_q (delta : ZMod q) : addOrderOf delta ∣ q :=
  addOrderOf_dvd_card delta

end MainTheory.RankTwo
