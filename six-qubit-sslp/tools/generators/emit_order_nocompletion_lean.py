#!/usr/bin/env python3
"""Emit the logical-order no-completion layers that were missing.

`MainTheory/OrderSixNoCompletion.lean`, `OrderEightNoCompletion.lean` and
`OrderNineNoCompletion.lean` do this for logical orders 6, 8 and 9, and
`OrderFiveUniqueCompletion.lean` handles order 5.  Orders 4 and 7 -- fifteen of
the sixty-six directory keys, more than all the others put together -- had no
such layer, even though every one of their fifteen paper no-gos was already
proved in `SixQubit/CodeOrbit*.lean` and aggregated in `WImageNoGo51`.  Without
them `M_3(6) = 5` could not be stated: nothing ruled out logical order 4.

Each key is handled exactly as the order-six module does it: identify the
generated fibre pair with the paper orbit's two literal supports, transport the
paper no-go along the stored, kernel-checked cube action, and only then consult
the numerical paper-orbit table.

Usage:  python tools/generators/emit_order_nocompletion_lean.py
"""
import io
import os
import re

ROOT = os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASE = 'MainTheory.Generated.FiniteOrbitBase'
WORD = {4: 'Four', 7: 'Seven'}


def read(rel):
    return io.open(os.path.join(ROOT, rel), encoding='utf-8').read()


def key_table():
    """(key index) -> (q, m, paper orbit id, representative input index)."""
    src = read('MainTheory/Generated/FiniteOrbitBase.lean')
    keys = {int(a): (int(q), int(m)) for a, q, m in re.findall(
        r'^def key(\d\d) : MainTheory\.FiniteOrbitPipeline\.OrbitKey := '
        r'⟨(\d+), (\d+),', src, re.M)}
    ids = [int(x) for x in re.findall(
        r'\d+', re.search(r'def paperOrbitId[^\n]*\n(.*?)\n\]',
                          src, re.S).group(1))]
    rep = [int(x) for x in re.findall(
        r'\d+', re.search(r'def representativeAt : Fin 66 . Fin 215 :=\s*!\['
                          r'(.*?)\n\]', src, re.S).group(1))]
    return {k: (keys[k][0], keys[k][1], ids[k], rep[k]) for k in keys}


def fibre_lemma_names():
    """The two support-equals-fibre lemma names each no-go actually uses.

    They are not uniform -- several orbits call the second one `S1_residue` --
    so they are read off the aggregation rather than guessed."""
    src = read('MainTheory/WImageNoGo51.lean')
    out = {}
    for block in src.split('theorem WImage_orbit')[1:]:
        o = int(re.match(r'(\d+)_empty', block).group(1))
        names = re.findall(r'SixQubit\.Orbit%d\.(S[01]\w+)' % o, block)
        s0 = [x for x in names if x.startswith('S0') and x != 'S0']
        s1 = [x for x in names if x.startswith('S1') and x != 'S1']
        if s0 and s1:
            out[o] = (s0[0], s1[0])
    return out


def module(m, rows):
    word = WORD[m]
    ns = 'MainTheory.Order%sNoCompletion' % word
    shards = sorted(v[3] for v in rows.values())
    lines = [
        'import MainTheory.CubeCompletionTransport',
    ]
    lines += ['import MainTheory.Generated.FiniteOrbitWitnessShard%03d' % i
              for i in shards]
    lines += [
        'import MainTheory.WImageNoGo51',
        '',
        '/-!',
        '# The generated logical-order-%d keys are no-gos' % m,
        '',
        'There are %d of them, and they had no layer of their own: orders 5,'
        % len(rows),
        '6, 8 and 9 did, but orders 4 and 7 -- fifteen of the sixty-six keys',
        'between them -- did not, so nothing connected their paper no-gos to',
        'the directory and `M_3(6) = 5` could not be stated.',
        '',
        'Each key is bound to its paper support pair by an exact mask equality',
        'and its stored, kernel-checked cube action.  The numerical',
        'paper-orbit table is consulted only after those payload-level',
        'identifications.',
        '-/',
        '',
        'namespace %s' % ns,
        '',
        'open MainTheory.CubeCompletionTransport',
        'open MainTheory.FiniteOrbitPipeline',
        '',
        'namespace Base',
    ]
    for k, (q, mm, o, i) in rows_sorted(rows):
        lines.append('abbrev input%03d := %s.input%03d' % (i, BASE, i))
    for k, (q, mm, o, i) in rows_sorted(rows):
        lines.append('abbrev key%02d := %s.key%02d' % (k, BASE, k))
    lines += ['end Base', '']
    names = fibre_lemma_names()
    for k, (q, mm, o, i) in rows_sorted(rows):
        r1 = q // m
        n0, n1 = names[o]
        lines += [
            'def paper%dFibers : MainTheory.CubeAction.FiberPair 6' % o,
            '  | false => SixQubit.Orbit%d.S0' % o,
            '  | true => SixQubit.Orbit%d.S1' % o,
            '',
            'theorem input%03d_fibers_eq_paper%d :' % (i, o),
            '    fibersOfPair Base.input%03d = paper%dFibers := by' % (i, o),
            '  funext c',
            '  cases c <;> decide',
            '',
            'theorem paper%d_equivalent_key%02d :' % (o, k),
            '    MainTheory.DistanceSignature.LabeledEquivalent',
            '      %d %d paper%dFibers %d %d Base.key%02d.fibers := by'
            % (q, m, o, q, m, k),
            '  change MainTheory.DistanceSignature.LabeledEquivalent',
            '    Base.input%03d.q Base.input%03d.m paper%dFibers' % (i, i, o),
            '      Base.key%02d.q Base.key%02d.m Base.key%02d.fibers'
            % (k, k, k),
            '  rw [← input%03d_fibers_eq_paper%d]' % (i, o),
            '  exact OrbitWitness.labeledEquivalent_of_validFor',
            '    MainTheory.Generated.FiniteOrbitWitnessShard%03d'
            '.witness_validFor' % i,
            '',
            'theorem paper%d_noCompletion : NoCompletion paper%dFibers := by'
            % (o, o),
            '  apply not_completion_of_WImage_empty SixQubit.Orbit%d.av 0 %d'
            % (o, r1),
            '    paper%dFibers' % o,
            '  · simpa [paper%dFibers] using SixQubit.Orbit%d.%s'
            % (o, o, n0),
            '  · simpa [paper%dFibers] using SixQubit.Orbit%d.%s'
            % (o, o, n1),
            '  · exact MainTheory.WImageNoGo51.WImage_orbit%d_empty' % o,
            '',
            'theorem key%02d_noCompletion : NoCompletion Base.key%02d.fibers :='
            % (k, k),
            '  not_completion_of_fiberEquivalent paper%d_noCompletion' % o,
            '    paper%d_equivalent_key%02d.2.2' % (o, k),
            '',
            'theorem keyAt%02d_eq : %s.keyAt %d = Base.key%02d := by decide'
            % (k, BASE, k, k),
            '',
            'theorem paperOrbitId%02d_eq : %s.paperOrbitId %d = %d := by decide'
            % (k, BASE, k, o),
            '',
            'theorem directoryKey%02d_noCompletion :' % k,
            '    NoCompletion (%s.keyAt %d).fibers := by' % (BASE, k),
            '  simpa only [keyAt%02d_eq] using key%02d_noCompletion' % (k, k),
            '',
        ]
    ks = [k for k, _ in rows_sorted(rows)]
    disj = ' ∨ '.join('k = %d' % k for k in ks)
    lines += [
        '/-- Exactly these keys carry logical order %d. -/' % m,
        'theorem key_m_eq_%s_iff (k : Fin 66) :' % word.lower(),
        '    (%s.keyAt k).m = %d ↔' % (BASE, m),
        '      %s := by' % disj,
        '  fin_cases k <;> decide',
        '',
        '/-- **No exact distance-three code completes a logical-order-%d' % m,
        'orbit.** -/',
        'theorem noCompletion_of_order%s (k : Fin 66)' % word,
        '    (hm : (%s.keyAt k).m = %d) :' % (BASE, m),
        '    NoCompletion (%s.keyAt k).fibers := by' % BASE,
        '  rcases (key_m_eq_%s_iff k).1 hm with %s'
        % (word.lower(), ' | '.join('h' for _ in ks)),
    ]
    for k in ks:
        lines.append('  · subst k; exact directoryKey%02d_noCompletion' % k)
    lines += ['', 'end %s' % ns, '']
    return '\n'.join(lines)


def rows_sorted(rows):
    return sorted(rows.items())


def main():
    table = key_table()
    for m in (4, 7):
        rows = {k: v for k, v in table.items() if v[1] == m}
        path = os.path.join(ROOT, 'MainTheory',
                            'Order%sNoCompletion.lean' % WORD[m])
        io.open(path, 'w', encoding='utf-8',
                newline='\n').write(module(m, rows))
        print('wrote', os.path.relpath(path, ROOT), '(%d keys)' % len(rows))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
