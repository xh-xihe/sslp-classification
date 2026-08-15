"""Re-derive every number of the theorem-hypothesis sweep from the stored results.

Asserts each figure the manuscript prints; exits nonzero on any mismatch.
"""

import io
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _check import expect, finish                                    # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir))
SRC = os.path.join(ROOT, 'data', 'thm44_verification_results.json')
if not os.path.exists(SRC):
    raise SystemExit('sweep results not found at %s' % SRC)

rows = json.load(io.open(SRC, encoding='utf-8'))
if isinstance(rows, dict):
    rows = rows.get('results', list(rows.values()))


def hyps_hold(r):
    h = r['hypotheses']
    return all(bool(h[k]) for k in h if isinstance(h[k], bool))


confirm = [r for r in rows if r['thm44_status'] == 'CONFIRMS']
notlift = [r for r in rows if not r.get('bell_liftable', True)]
failhyp = [r for r in rows if r.get('bell_liftable', True) and not hyps_hold(r)]
counterex = [r for r in rows if hyps_hold(r) and r.get('bell_liftable', True)
             and not r['conclusion_all_rungs_distance3']]
alsofail = [r for r in failhyp if not r['conclusion_all_rungs_distance3']]
viol = sorted(r['worst_violation_across_rungs'] for r in confirm)

print('theorem-hypothesis sweep over the 43 test instances:')
print()
expect('total instances', len(rows), 43)
expect('hypotheses hold and every rung keeps d>=3', len(confirm), 30)
expect('counterexamples', len(counterex), 0)
expect('a hypothesis fails', len(failhyp), 9)
expect('not a subset-sum code, lift undefined', len(notlift), 4)
expect('of those failing a hypothesis, also fail the conclusion', len(alsofail), 8)
expect('worst violation among confirmations', viol[-1], 8.0e-14, 5e-15)
expect('confirmations below 1.6e-15', sum(1 for v in viol if v <= 1.6e-15), 29)
expect('median violation', viol[len(viol) // 2], 3.3e-16, 5e-17)

seed = [r for r in rows if r['n'] == 7 and r['m'] == 8
        and list(r['a']) == [1, 2, 2, 2, 2, 3, 3]]
expect("paper's seed present exactly once", len(seed), 1)
if seed:
    expect("paper's seed confirms", seed[0]['thm44_status'], 'CONFIRMS')
    expect("paper's seed worst violation", seed[0]['worst_violation_across_rungs'],
           4.2e-16, 5e-17)
    expect("paper's seed rungs checked", len(seed[0]['rungs']), 6)

expect('block lengths present', sorted({r['n'] for r in rows}), [6, 7, 8])
expect('smallest modulus', min(r['m'] for r in rows), 2)
expect('largest modulus', max(r['m'] for r in rows), 42)

# the sweep report also states where the failures happen: four at
# rung 1, three at rung 2, one at rung 3.


def first_fail(r):
    for rung in r['rungs']:
        if not rung.get('passed', True):
            return rung['rung']
    return None


ff = [first_fail(r) for r in failhyp if not r['conclusion_all_rungs_distance3']]
expect('failures first appearing at rung 1', ff.count(1), 4)
expect('failures first appearing at rung 2', ff.count(2), 3)
expect('failures first appearing at rung 3', ff.count(3), 1)

finish('sweep')
