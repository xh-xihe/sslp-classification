"""Bind the completed common logical basis theorem to its current prose obligations."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
path=ROOT/'results/prose-review-20261003.json'
data=json.loads(path.read_text(encoding='utf8'))
for source,sha in data['sources_sha256'].items():
    if hashlib.sha256((ROOT/source).read_bytes()).hexdigest()!=sha:
        raise ValueError('Changed manuscript: '+source)
for name in ('small-transversal-clifford-build.json',
             'bounded-projective-clifford-group-build.json',
             'nonclifford-rank-build.json'):
    record=json.loads((ROOT/'artifacts/orbit-certification-20261003'/name).read_text(encoding='utf8'))
    if record['status']!='PASS':
        raise ValueError('Unpassed common-basis theorem: '+name)
for row in data['assertions']:
    if row['id']=='main-small-nonclifford-minimum':
        row.update(kind='covered',declarations=[
            'MainTheory.SmallTransversalClifford.minimum_length',
            'MainTheory.SmallNonCliffordMinimum.minimum_attained',
            'MainTheory.CliffordProjectiveOrder.order_five_no_clifford_basis'],
            reason='The full actual transversal logical group below six has a common Pauli-normalizing basis. Conversely the literal six-qubit canonical code implements a projective order-five logical matrix, while every literal Clifford has projective order at most four. Conjugation preserves the actual adjoint order, so no logical basis makes this six-qubit group Clifford. Both the lower bound and its attained endpoint are kernel proved.')
    if row['id']=='small-transversal-group-clifford-conjugacy':
        row.update(kind='covered',declarations=[
            'MainTheory.SmallTransversalClifford.common_basis',
            'MainTheory.BoundedProjectiveCliffordGroup.common_basis',
            'MainTheory.QuaternionBoundedGroup.bounded_group',
            'MainTheory.QuaternionCliffordMatrixBridge.normalizer_clifford'],
            reason='For the full group of literal tensor-product logical U(2) operations on every actual rank-two code with distance at least three and n at most five, the kernel proves one common logical U(2) basis sends every group member to a literal Pauli normalizer. The proof uses a unit-quaternion subgroup and its short-order axis geometry. This certifies the simultaneous conjugacy conclusion independently of the cited finite-rotation-group classification route; it does not assert a separate classification by abstract group names.')
path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded the kernel-proved common Clifford basis; other gaps and author-held main errata remain unchanged.')
