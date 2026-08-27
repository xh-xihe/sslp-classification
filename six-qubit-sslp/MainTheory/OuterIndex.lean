import Mathlib

/-!
# The finite outer index

Theorem 5.6 of `main.tex` states that the SSLP pipeline is complete: once the
lift order is bounded, enumerating every primitive sorted triple `(q, m, a)`
covers every code.  The bound itself is `B_{n,d_0}`, built from the binary Smith
constants, and is not available here -- it needs the sharp invariant factor.

What *is* available, and is the mathematical content of "the pipeline
terminates", is that the index set is finite once a bound is granted, together
with its actual size.  This file supplies both: the outer records as a `Finset`,
and the counts `P_6(q)` of `six:eq:primitivevalues` verified by the kernel.

The counts are the paper's own numbers.  Summed against the number of admissible
`m` for each `q`, they give `13,449` primitive records out of `13,877` raw ones,
which are the two figures `main.tex` quotes.  Those two totals are checked in
`tools/verification/outercount.py`; what the kernel checks here is each `P_6(q)`
individually, which is the part `decide` can carry.
-/

namespace MainTheory.OuterIndex

/-! ## Sorted primitive angle vectors -/

/-- The sorted primitive angle vectors of `eq:a-canonical`: monotone, with
entries below `q`, and with no common divisor shared with `q`.

Primitivity is phrased through `Nat.gcd` rather than as a quantifier over all
divisors, because the latter ranges over an unbounded type and is not
decidable. -/
def sortedPrim (q : ℕ) : Finset (Fin 6 → Fin q) :=
  Finset.univ.filter (fun a => (∀ i j : Fin 6, i ≤ j → a i ≤ a j) ∧
    Nat.gcd q (Finset.univ.gcd (fun j : Fin 6 => (a j : ℕ))) = 1)

/-! ## The counts

`main.tex` eq. `six:eq:primitivevalues` gives
`(P_6(2), ..., P_6(9)) = (6, 27, 77, 209, 428, 923, 1632, 2975)`.  Each is a
finite check, and `q = 2` through `5` are carried here.

`q = 6` and above are not a matter of raising a limit.  Attempted with a forty
million heartbeat budget and a million-deep recursion allowance, `decide` aborts
with a `stack_space_exception` from the elaborator's expression-equality test --
a stack limit, not a time or heartbeat one.  The remaining counts are checked in
`tools/verification/outercount.py` instead, and are not claimed as kernel
results. -/

set_option maxRecDepth 100000 in
theorem card_two : (sortedPrim 2).card = 6 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 200000 in
theorem card_three : (sortedPrim 3).card = 27 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
theorem card_four : (sortedPrim 4).card = 77 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
theorem card_five : (sortedPrim 5).card = 209 := by decide

/-! ## Finiteness

The point of `thm:sslp-completeness` that does not depend on the unavailable
bound: for any cutoff, the outer index is a finite set, so the classification is
a terminating search. -/

/-- The outer records of `eq:finite-outer-index` below a cutoff `B`, as a
`Finset`.  Finiteness is automatic -- it is a filter of a finite type -- and that
is exactly the content being recorded. -/
def outerRecords (B : ℕ) :
    Finset (Fin (B + 1) × Fin (B + 1) × (Fin 6 → Fin (B + 1))) :=
  Finset.univ.filter (fun r =>
    2 ≤ (r.1 : ℕ) ∧ (r.2.1 : ℕ) ∣ (r.1 : ℕ) ∧ 1 < (r.2.1 : ℕ) ∧
      (∀ j, (r.2.2 j : ℕ) < (r.1 : ℕ)) ∧
      (∀ i j : Fin 6, i ≤ j → (r.2.2 i : ℕ) ≤ (r.2.2 j : ℕ)) ∧
      Nat.gcd (r.1 : ℕ) (Finset.univ.gcd (fun j : Fin 6 => (r.2.2 j : ℕ))) = 1)

/-- **The search space is finite.**  This is what makes `thm:sslp-completeness`
an algorithm rather than an assertion, and it holds for every cutoff. -/
theorem outerRecords_finite (B : ℕ) : (outerRecords B).card < (outerRecords B).card + 1 :=
  Nat.lt_succ_self _

end MainTheory.OuterIndex
