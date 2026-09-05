import MainTheory.Generated.FiniteOrbitBase

/-!
# Which controlled lift orders survive at each logical order

The orbit-reduction table of `main.tex` has three columns.  Two of them are
kernel theorems already: `Generated.FiniteOrbitDistribution` proves the
labelled-pair counts `73, 36, 31, 30, 13, 18, 9, 5` and the orbit counts
`25, 11, 10, 8, 4, 5, 2, 1`, both sliced by the targeted logical order `m`.

The third column, "surviving controlled lift orders `q`", was not proved, and
that file cannot prove it: its own docstring says it slices by `.m` because
counting `.q` "checks a different statement and is a false-green hazard", and
it never inspects `.q` at all.  The two labels differ precisely in the rows
where a lift of order `4` or `6` realizes logical order `2` or `3`, which is
exactly what this column displays.

`survivingQ m` is the set of lift orders occurring among the 215 rank-compatible
inputs at logical order `m`, read off the same generated `inputAt` the other two
columns use.
-/

namespace MainTheory.SurvivingLiftOrders

open MainTheory.Generated.FiniteOrbitBase

/-- The controlled lift orders occurring at a given targeted logical order. -/
def survivingQ (m : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin 215 => (inputAt i).m = m)).image
    (fun i => (inputAt i).q)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- **The third column of the orbit-reduction table.**

At logical order two a lift of order four or six can occur; at order three a
lift of order six can; from order four upward the only new phenomenon is
`m = 4` with `q = 8`, and at every order above four the lift order equals the
logical order. -/
theorem survivingQ_table :
    survivingQ 2 = {2, 4, 6} ∧
    survivingQ 3 = {3, 6} ∧
    survivingQ 4 = {4, 8} ∧
    survivingQ 5 = {5} ∧
    survivingQ 6 = {6} ∧
    survivingQ 7 = {7} ∧
    survivingQ 8 = {8} ∧
    survivingQ 9 = {9} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- The reading the table is for: `q = m` except at `(q, m)` in
`(4,2), (6,2), (6,3), (8,4)`. -/
theorem q_eq_m_or_exception (i : Fin 215) :
    (inputAt i).q = (inputAt i).m ∨
      ((inputAt i).q = 4 ∧ (inputAt i).m = 2) ∨
      ((inputAt i).q = 6 ∧ (inputAt i).m = 2) ∨
      ((inputAt i).q = 6 ∧ (inputAt i).m = 3) ∨
      ((inputAt i).q = 8 ∧ (inputAt i).m = 4) := by
  revert i
  decide

end MainTheory.SurvivingLiftOrders
