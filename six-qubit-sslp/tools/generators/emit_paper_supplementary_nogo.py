"""Emit the label-facing interface for the supplementary no-go results.

Every statement emitted here is already proved.  What was missing is the map
from the manuscript's labels to the Lean declarations: a sweep of
`documents/20260905/supplementary.tex` found 83 of its 87 named results with no
label anywhere in the Lean sources, so a reader checking the manuscript against
the package could find the parts and not the results.

The per-orbit no-gos are all instances of one statement -- an orbit key admits
an exact normalized distance-three completion exactly when its manuscript orbit
number is one of the fifteen -- so they are emitted from a table rather than
written out, and each carries its own label.  The order-level results are
instances of `IntrinsicOrderAudit.orderOf_mem`.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

REALIZED = [1, 2, 3, 4, 7, 8, 9, 10, 11, 16, 21, 22, 23, 36, 45]

# (label, manuscript orbit numbers, projective order)
PER_ORBIT = [
    ('prop:o12-nogo', [12], 2), ('prop:o13-nogo', [13], 2),
    ('prop:o14-nogo', [14], 2), ('prop:o15-nogo', [15], 2),
    ('prop:o17-nogo', [17], 2), ('prop:o18-nogo', [18], 2),
    ('prop:o19-nogo', [19], 2), ('prop:o20-nogo', [20], 2),
    ('prop:o24-nogo', [24], 2), ('prop:o41-nogo', [41], 2),
    ('prop:o42o43-nogo', [42, 43], 2), ('prop:o44-nogo', [44], 2),
    ('prop:o46-nogo', [46], 2),
    ('prop:o5-nogo', [5], 3), ('prop:o6-nogo', [6], 3),
    ('prop:o47-nogo', [47], 3), ('prop:o48-nogo', [48], 3),
    ('prop:o49-nogo', [49], 3), ('prop:o50-nogo', [50], 3),
    ('prop:o51-nogo', [51], 3), ('prop:o52-nogo', [52], 3),
    ('thm:q4o26nogo', [26], 4), ('thm:q4o30nogo', [30], 4),
    ('thm:q4o31nogo', [31], 4), ('thm:q4o32nogo', [32], 4),
    ('prop:q6no53', [53], 6), ('prop:q6no54', [54], 6),
    ('prop:q6no55', [55], 6), ('prop:q6no56', [56], 6),
    ('prop:q7no57', [57], 7), ('prop:q7no58', [58], 7),
    ('prop:q7no59', [59], 7), ('prop:q7no60', [60], 7),
    ('prop:q7no61', [61], 7),
]

AGGREGATE = [
    ('thm:m2-fourteen-nogos', 'm2_fourteen_nogos',
     [12, 13, 14, 15, 17, 18, 19, 20, 24, 41, 42, 43, 44, 46],
     'None of the fourteen rank-compatible order-two moment orbits admits an '
     'exact completion.'),
    ('thm:m3-complete-nogos', 'm3_complete_nogos',
     [5, 6, 47, 48, 49, 50, 51, 52],
     'None of the eight rank-compatible order-three moment orbits admits an '
     'exact six-qubit distance-three completion.'),
    ('thm:m5-other-seven', 'm5_other_seven',
     [33, 34, 35, 37, 38, 39, 40],
     'None of the other seven order-five moment orbits admits an exact '
     '((6,2,3)) completion.'),
]

ORDER_LEVEL = [
    ('thm:q4nogo', 'q4_no_go', 4,
     'No exact `((6,2,d))` code with `d >= 3` admits a projective diagonal\n'
     'transversal logical element of order `4`.'),
    ('thm:q6nogo', 'q6_no_go', 6, 'The order-six no-go.'),
    ('thm:q7nogo', 'q7_no_go', 7, 'The order-seven no-go.'),
    ('thm:q8nogo', 'q8_no_go', 8,
     'The order-eight no-go.  The manuscript reaches it through `prop:q8Ano`\n'
     'and `prop:q8Bno`, the two order-eight moment orbits;\n'
     '`OrderEightNoCompletion.paperOrbitId_of_orderEight` records that those\n'
     'are manuscript orbits `64` and `65`.  Which of the two is the\n'
     "manuscript's `A` is deliberately not asserted: the key stores a\n"
     'cube-orbit representative and the manuscript picks a readable one, and\n'
     'no Lean theorem matches the two choices.'),
    ('thm:q9nogo', 'q9_no_go', 9, 'The order-nine no-go.'),
]


def name_of(label):
    for prefix in ('prop:', 'thm:', 'cor:', 'lem:'):
        label = label.replace(prefix, '')
    return label.replace('-', '_').replace(':', '_')


def lean_list(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def per_orbit_block():
    out = []
    for label, ids, order in PER_ORBIT:
        plural = 's' if len(ids) > 1 else ''
        verb = '' if len(ids) > 1 else 's'
        which = ' and '.join(str(i) for i in ids)
        hyp = ' ∨ '.join('paperOrbitId k = %d' % i for i in ids)
        proof = ('rcases hk with h | h <;> rw [h] <;> decide'
                 if len(ids) > 1 else 'rw [hk]; decide')
        out.append(
            '/-- **`%s`.**  Manuscript orbit%s %s, of projective order %d,\n'
            'admit%s no exact `((6,2,d))` completion with `d >= 3`. -/\n'
            'theorem %s (k : Fin 66) (hk : %s) :\n'
            '    NoCompletion (keyAt k).fibers :=\n'
            '  no_completion_of_paperOrbitId k (by %s)\n'
            % (label, plural, which, order, verb, name_of(label), hyp, proof))
    return '\n'.join(out)


def aggregate_block():
    out = []
    for label, name, ids, prose in AGGREGATE:
        out.append(
            '/-- **`%s`.**  %s\n\n'
            'The %d orbits really are %d distinct orbits: `paperOrbitId` is\n'
            'injective, so distinct manuscript numbers name distinct keys. -/\n'
            'theorem %s (k : Fin 66)\n'
            '    (hk : paperOrbitId k ∈\n'
            '      (%s : List ℕ)) :\n'
            '    NoCompletion (keyAt k).fibers :=\n'
            '  no_completion_of_paperOrbitId k (by\n'
            '    revert hk\n'
            '    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]\n'
            '    omega)\n'
            % (label, prose, len(ids), len(ids), name, lean_list(ids)))
    return '\n'.join(out)


def order_level_block():
    out = []
    for label, name, order, prose in ORDER_LEVEL:
        out.append(
            '/-- **`%s`.**  %s -/\n'
            'theorem %s (C : CodeSpec.ExactCode 6 2 3)\n'
            '    (g : GlobalClassificationBridge.IntrinsicGroup C) :\n'
            '    orderOf g ≠ %d := by\n'
            '  rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with\n'
            '    h | h | h | h <;> omega\n'
            % (label, prose, name, order))
    return '\n'.join(out)


HEADER = '''-- Generated by tools/generators/emit_paper_supplementary_nogo.py.
import MainTheory.CodeOrbitStatus
import MainTheory.IntrinsicOrderAudit
import MainTheory.OrderEightNoCompletion
import MainTheory.OrderFourNoCompletion
import MainTheory.OrderSevenNoCompletion
import MainTheory.RealizationOrbits15

/-!
# `supplementary.tex`: the no-go results, by label

A sweep of the 20260905 supplementary manuscript found 83 of its 87 named
results with no label anywhere in the Lean sources.  None of them was unproved;
what was missing was the interface, exactly as it was for
`thm:general-sslp-normal-form` before `PaperGeneralSSLP`.  A reader checking
the manuscript against the package could find the parts and not the results.

This file is that interface for the no-go half.  Nothing new is proved: every
theorem here is a named instance of one of three facts.

* `hasCompletion_iff_paperOrbitId` -- an orbit key admits an exact normalized
  distance-three completion exactly when its *manuscript* orbit number is one
  of the fifteen.  This is
  `RealizationOrbits15.hasCompletion_iff_mem_realizationKeys` pushed through
  `paperOrbitId`, which is what lets the statements be indexed the way the
  manuscript indexes them.
* `paperOrbitId_injective` -- distinct manuscript numbers name distinct keys.
  Without it "orbit 12" would not denote, and a per-orbit statement quantified
  over `k` with `paperOrbitId k = 12` could be satisfied vacuously.
* `IntrinsicOrderAudit.orderOf_mem` -- every element of the intrinsic
  projective diagonal logical group has order `1`, `2`, `3` or `5`, which is
  the order-level content of `thm:q4nogo` through `thm:q9nogo` and of
  `cor:completeorderclassification`.

The per-orbit statements are quantified over the key rather than applied to a
numeral because `paperOrbitId` is the only bridge between the manuscript's
numbering and the generated key order; writing `keyAt 12` would silently
assert that the two orderings agree, and they do not.
-/

namespace MainTheory.PaperSupplementaryNoGo

open MainTheory
open MainTheory.CubeCompletionTransport
open MainTheory.Generated.FiniteOrbitBase
open MainTheory.RealizationOrbits15

set_option maxRecDepth 100000

/-! ## The two facts the rest of the file is built from -/

/-- Distinct manuscript orbit numbers name distinct generated keys, so
"manuscript orbit `N`" denotes at most one key. -/
theorem paperOrbitId_injective : Function.Injective paperOrbitId := by decide

/-- Every manuscript orbit number from `1` to `66` is the number of some key,
so "manuscript orbit `N`" denotes at least one.

Together with injectivity this is what keeps the per-orbit statements below
from being vacuous: each is quantified over a key `k` with
`paperOrbitId k = N`, and without this there would be no guarantee that such a
`k` exists at all. -/
theorem paperOrbitId_range :
    Finset.univ.image paperOrbitId = Finset.Icc 1 66 := by decide

theorem exists_key_of_paperOrbitId {i : ℕ} (hi : i ∈ Finset.Icc 1 66) :
    ∃! k : Fin 66, paperOrbitId k = i := by
  rw [← paperOrbitId_range] at hi
  obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hi
  exact ⟨k, hk, fun j hj => paperOrbitId_injective (hj.trans hk.symm)⟩

/-- **The manuscript's existence column, in one statement.**

An orbit key admits an exact normalized distance-three completion exactly when
its manuscript orbit number is one of the fifteen realized ones. -/
theorem hasCompletion_iff_paperOrbitId (k : Fin 66) :
    HasCompletion (keyAt k).fibers ↔
      paperOrbitId k ∈ (%(realized)s : List ℕ) := by
  rw [hasCompletion_iff_mem_realizationKeys]
  revert k
  decide

theorem no_completion_of_paperOrbitId (k : Fin 66)
    (h : paperOrbitId k ∉
      (%(realized)s : List ℕ)) :
    NoCompletion (keyAt k).fibers :=
  fun hc => h ((hasCompletion_iff_paperOrbitId k).1 hc)

/-! ## The per-orbit no-gos -/

'''

FOOTER_HEAD = '''
/-! ## The order-level no-gos

`thm:q4nogo`, `thm:q6nogo`, `thm:q7nogo`, `thm:q8nogo` and `thm:q9nogo` all say
that a given nontrivial projective order is impossible.  Each is the
corresponding case of the order audit, stated on an actual element of the
intrinsic group rather than on a normal form's own `m`, which is what the
manuscript claims. -/

'''

FOOTER_TAIL = '''
/-- **`cor:completeorderclassification`, `eq:exactnontrivialorders`.**

Including the identity the possible orders are `{1, 2, 3, 5}`, so the
nontrivial ones are exactly `{2, 3, 5}`.  Attainment of each of `2`, `3` and
`5` is `OrderRange.logicalOrders_attained`. -/
theorem complete_order_classification (C : CodeSpec.ExactCode 6 2 3)
    (g : GlobalClassificationBridge.IntrinsicGroup C) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5 :=
  MainTheory.IntrinsicOrderAudit.orderOf_mem C g

/-- **`cor:q6range`, `eq:M36exact`.**  `M_3(6) = 5`: no order exceeds five. -/
theorem max_order_le_five (C : CodeSpec.ExactCode 6 2 3)
    (g : GlobalClassificationBridge.IntrinsicGroup C) : orderOf g ≤ 5 := by
  rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with
    h | h | h | h <;> omega

open scoped Classical in
/-- **`cor:m2-eleven-remaining` (`eq:m2-eleven-remaining`) and
`cor:m3-complete-status` (`eq:m3-realizable-orbits`).**

Both corollaries read the same column.  The order-two survivors are
`1, 2, 3, 4, 10, 11, 16, 21, 22, 23, 45`, the order-three survivors are
`7, 8, 9`, and `36` is the order-five survivor; together those are the
fifteen. -/
theorem realized_paperOrbitIds :
    (Finset.univ.filter fun k : Fin 66 =>
        HasCompletion (keyAt k).fibers).image paperOrbitId
      = (%(realizedFinset)s : Finset ℕ) := by
  have h : (Finset.univ.filter fun k : Fin 66 =>
        HasCompletion (keyAt k).fibers)
      = (Finset.univ.filter fun k : Fin 66 =>
        paperOrbitId k ∈ (%(realized)s : List ℕ)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hasCompletion_iff_paperOrbitId k
  rw [h]
  decide

end MainTheory.PaperSupplementaryNoGo
'''


def main():
    fields = {'realized': lean_list(REALIZED),
              'realizedFinset': '{' + ', '.join(map(str, REALIZED)) + '}'}
    text = (HEADER % fields
            + per_orbit_block()
            + '\n' + aggregate_block()
            + FOOTER_HEAD
            + order_level_block()
            + FOOTER_TAIL % fields)
    destination = ROOT / 'MainTheory/PaperSupplementaryNoGo.lean'
    destination.write_text(text, encoding='utf-8')
    print(destination.relative_to(ROOT))


if __name__ == '__main__':
    main()
