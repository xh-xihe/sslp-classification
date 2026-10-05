#!/usr/bin/env python3
"""Record the finite-rotation/Clifford conclusion that still needs its own proof."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
path = ROOT / 'results/prose-review-20261003.json'
data = json.loads(path.read_text(encoding='utf8'))
for source, expected in data['sources_sha256'].items():
    if hashlib.sha256((ROOT / source).read_bytes()).hexdigest() != expected:
        raise ValueError('Changed manuscript: ' + source)
rows = [
    dict(id='small-transversal-group-clifford-conjugacy', source='supplementary.tex',
         locator='after-cor:main-order-five-minimum-length', line=7720,
         statement='Every full finite projective transversal logical group below six qubits is conjugate into the single-qubit Clifford group.',
         kind='gap', declarations=[],
         reason='The actual transversal image is kernel-proved finite, and the order-five minimum-length theorem and diagonal lift bound give the stated element-order restriction. The current library has no finite PU(2)/SO(3) subgroup classification or simultaneous Clifford conjugacy theorem. This additional semantic obligation is separate from the five author-held main-text errata; neither the correct mathematical claim nor a reference to it counts as a kernel proof.'),
    dict(id='main-small-nonclifford-minimum', source='main.tex',
         locator='after-cor:six-C5-minimum-length', line=2633,
         statement='The same minimum six applies in the logical-basis-independent non-Clifford sense.',
         kind='gap', declarations=[],
         reason='This prose conclusion invokes the SI finite-rotation-group/Clifford-conjugacy argument. The order-five minimum itself is proved; the simultaneous finite-group conjugacy connection remains a separate kernel obligation.'),
]
index = {r['id']: i for i, r in enumerate(data['assertions'])}
for row in rows:
    if row['id'] in index:
        data['assertions'][index[row['id']]] = row
    else:
        data['assertions'].append(row)
data['status'] = 'partial'
path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
print('Recorded two prose obligations; no manuscript edited and no coverage assumed.')
