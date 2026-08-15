"""Generate the per-position Knill--Laflamme check module.

Two facts about the kernel shape this file.

First, the kernel keeps one weak-head-normal-form cache per declaration and
frees it only when that declaration is finished.  Proving all 211 (resp. 352)
weight-<=2 Pauli conditions inside a single `decide +kernel` therefore
accumulates every intermediate term of every check -- measured at about 4.5 GB
per minute, which exhausts memory well before the nine-qubit rung completes.
One declaration per support position bounds the live cache by the cost of a
single position.

Second, the assembly must never let `exact` fail.  A failed `exact` against a
`klAtZ ... = true` goal lets the unifier unfold `klAtZ` and begin evaluating it,
which is exactly the computation we are trying to do only once.  So the goals
produced by `fin_cases` are discharged positionally with `exacts`, and the
positions are written as `Fin.mk` applications so that matching them is proof
irrelevance rather than numeral reduction.
"""

import io

HEADER = r'''import DyadicLifts.Seed.Defs
import SS.PauliSites

/-!
# The seed's Knill--Laflamme checks, one support position at a time

GENERATED FILE -- do not edit by hand; regenerate with `gen_checks.py`.

`KLmatK_of_sites` reduces the Knill--Laflamme conditions for all Paulis of
weight at most two to three statements: one at the identity, one per single
site, and one per ordered pair of sites.  Each is decided by the kernel on the
integer mirror of the code.

The split into one declaration per position is not cosmetic.  The kernel holds a
single reduction cache for the whole of a declaration and frees it only when
that declaration is complete, so proving every position inside one `decide`
accumulates the intermediate terms of all of them -- measured at about 4.5 GB
per minute, which exhausts memory long before the nine-qubit rung finishes.  One
declaration per position bounds the live cache by the cost of a single position.

The assembly lemmas at the end perform no computation: they case on the index
and hand each goal the corresponding declaration, positionally, so that no
`exact` is ever attempted against a goal it does not match.

No `sorry`, no `native_decide`.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

open DyadicLifts SS SS.ZSqrt235i

namespace BD16Kernel

'''


def fin(k, n):
    return u'(⟨%d, by omega⟩ : Fin %d)' % (k, n)


def gen(n, tag, S, p0, p1, rung):
    out = []
    out.append('/-! ## Rung %d: %d qubits -/\n' % (rung, n))

    out.append(
        '/-- The identity Pauli. -/\n'
        'theorem %s_id : klAtZ %s %s %s (fun _ => SQ.I) = true := by\n'
        '  decide +kernel\n' % (tag, S, p0, p1))

    for i in range(n):
        out.append(
            u'theorem %s_o%d : ∀ A : SQ, A ≠ SQ.I →\n'
            u'    klAtZ %s %s %s (oneSite %s A) = true := by\n'
            u'  decide +kernel\n' % (tag, i, S, p0, p1, fin(i, n)))

    out.append(
        u'/-- Every weight-one Pauli. -/\n'
        u'theorem %s_one : ∀ (i : Fin %d) (A : SQ), A ≠ SQ.I →\n'
        u'    klAtZ %s %s %s (oneSite i A) = true := by\n'
        u'  intro i A hA\n'
        u'  fin_cases i\n'
        u'  exacts [%s]\n'
        % (tag, n, S, p0, p1,
           ', '.join('%s_o%d A hA' % (tag, i) for i in range(n))))

    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for (i, j) in pairs:
        out.append(
            u'theorem %s_p%d_%d : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →\n'
            u'    klAtZ %s %s %s (twoSite %s %s A B) = true := by\n'
            u'  decide +kernel\n'
            % (tag, i, j, S, p0, p1, fin(i, n), fin(j, n)))

    cells = []
    for a in range(n):
        for b in range(n):
            if a < b:
                cells.append('%s_p%d_%d A B hA hB' % (tag, a, b))
            else:
                cells.append('absurd hij (by decide)')

    out.append(
        u'/-- Every weight-two Pauli.  The cells with `i ≥ j` are discharged from\n'
        u'the ordering hypothesis. -/\n'
        u'theorem %s_two : ∀ (i j : Fin %d) (A B : SQ), i < j → A ≠ SQ.I → B ≠ SQ.I →\n'
        u'    klAtZ %s %s %s (twoSite i j A B) = true := by\n'
        u'  intro i j A B hij hA hB\n'
        u'  fin_cases i <;> fin_cases j\n'
        u'  exacts [%s]\n'
        % (tag, n, S, p0, p1, ',\n    '.join(cells)))

    return '\n'.join(out)


body = HEADER
body += gen(7, 'k7', 'S7Z', u'ψ0Z', u'ψ1Z', 0)
body += '\n'
body += gen(9, 'k9', 'S9Z', u'ψ0Z1', u'ψ1Z1', 1)
body += '\nend BD16Kernel\n'

io.open('DyadicLifts/Seed/Checks.lean', 'w', encoding='utf-8').write(body)
print('wrote DyadicLifts/Seed/Checks.lean:',
      body.count('decide +kernel'), 'kernel decisions')
