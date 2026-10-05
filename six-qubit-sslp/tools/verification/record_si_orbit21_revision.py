"""Bind the SI orbit-21 prose correction to its actual kernel proofs."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
path=ROOT/'results/errata-20261003.json'
data=json.loads(path.read_text(encoding='utf8'))
for source,expected in data['sources_sha256'].items():
    assert hashlib.sha256((ROOT/source).read_bytes()).hexdigest()==expected
row=dict(id='orbit21-unsigned-count-and-residual',status='resolved_in_review_revision',
    locator='supplementary.tex:after-eq:o21-R4',origin='current-source-review',
    reason='The two stated unsigned actions, after eliminating anticommuting labels, have 640 classes rather than 512. The boxed identity itself is kernel-proved for actual full-KL completions with the prescribed fibers. The review revision retains every displayed formula and adds the support-pair Walsh residual elimination used by that proof. It does not assert that the few listed affine constraints alone imply the identity. The authoritative SI and held main text remain byte-identical.',
    declarations=['MainTheory.Orbit21UnsignedClasses.classes_count',
      'MainTheory.Orbit21UnsignedClasses.orbit_operations',
      'MainTheory.Orbit21UnsignedClasses.representative_exists',
      'SixQubit.Orbit21Residual.walsh_zero_on_pairs',
      'SixQubit.Orbit21Residual.residual_vanishes',
      'MainTheory.Orbit21FarkasDisplay.identity'],
    revision_source='documents/20261003/revisions/si-review-20261003/supplementary-revised.tex')
data['issues']=[r for r in data['issues'] if r['id']!=row['id']]+[row]
path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded the kernel-supported SI revision; authoritative manuscripts unchanged')
