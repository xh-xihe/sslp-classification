"""Rebuild `SixQubit/Trace5.lean` = hand-written head + generated tail + footer.

Run:  python tools/run.py generators/build5.py
"""
import io
import os
import runpy
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
HEAD = os.path.join(ROOT, 'build_zh', 'trace5_head.lean')
OUT = os.path.join(ROOT, 'SixQubit', 'Trace5.lean')

sys.path.insert(0, HERE)
import gen5algebra  # noqa: E402  (its module body builds the tail)

head = io.open(HEAD, encoding='utf-8').read().rstrip('\n')
tail = '\n'.join(gen5algebra.L)
body = head + '\n\n' + tail + '\n\nend\n\nend SixQubit.Trace5\n'
io.open(OUT, 'w', encoding='utf-8', newline='\n').write(body)
print('wrote %s (%d lines)' % (OUT, body.count('\n')))
