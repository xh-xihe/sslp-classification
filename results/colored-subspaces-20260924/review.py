"""Record the bounded semantic review; kernel validation is archived separately."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / 'tools'))
import paper_claims
import paper_release

version = '20260924'
assert paper_release.source_hashes(version) == {
    'documents/20260924/main.tex': '0015798c22359efffe64afd26bda2d057b71fd4b6b408062a6672193b487e542',
    'documents/20260924/supplementary.tex': 'a0f59088de371644a396fdd40ac218e4be803949b174a095c3233606c324cb37',
}, 'Semantic review must be repeated if either manuscript changes'
paths = paper_release.paths(version)
ledger = json.loads(paths['ledger'].read_text(encoding='utf8'))
paper_claims.validate(ledger, sources=paper_claims.sources_for_version(version))
rows = {row['id']: row for row in ledger['claims']}
reviews = {}


def record(key, names, reason):
    row = rows[key]
    row.update(status='covered', lean_declarations=names,
               review='2026-09-26 arbitrary-subspace semantic review of the unchanged 20260924 source. ' + reason)
    reviews[key] = dict(status='covered', reason=reason, lean_declarations=names,
                        statement_sha256=row['statement_sha256'])


forward = 'MainTheory.PaperGeneralSSLP.general_sslp_normal_form'
converse = 'MainTheory.PaperGeneralSSLP.general_sslp_converse'
subspaces = 'MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.'
record('main.tex:thm:general-sslp-normal-form', [
    forward, converse, 'MainTheory.SubspaceCode.codeSpan_frame',
    'MainTheory.SubspaceCode.hasDistance_iff', subspaces + 'independent',
    subspaces + 'sectorSpace_eq', subspaces + 'codeSpan_eq', subspaces + 'sslp_converse',
], 'The existing forward theorem retains the original projective class and the actual local-X/physical-'
   'permutation frame transport, sorted primitive angles, colors, multiplicities, fibers and distance. '
   'The new paper-facing converse takes arbitrary subspaces with the manuscript dimensions and full '
   'computational-basis fiber containments. Euclidean orthonormal bases are transported back to the '
   'original state type; each chosen sector spans exactly the supplied subspace. Distinct colors imply '
   'orthogonality and independence, not additional assumptions. The assembled frame spans their '
   'supremum, has dimension K, and satisfies the full KL predicate from basis-independent scalar '
   'compression for all Pauli weights strictly below d. The d=0 boundary follows from the identity '
   'Pauli and frame orthonormality, avoiding a hidden positive-distance restriction. The final '
   'ExactCode retains that same span, the literal finite diagonal gate with angle a, and an intrinsic '
   'class of exact order m. The zero color is a designated finite index; including it in the gcd '
   'does not change the gcd of the other colors. No supplied frame or assumed directness remains.')

record('main.tex:eq:general-sslp-outer-data', [
    forward, 'MainTheory.ColoredResidueArithmetic.primitive_iff_gcd_eq_one',
], 'The forward conclusion includes 2<=q, m dividing q, sorted ZMod representatives and primitive '
   'angle. ZMod representatives have values in [0,q), and primitive_iff_gcd_eq_one identifies '
   'Gate.Primitive with the displayed gcd. The new converse accepts the literal gcd condition.')
record('main.tex:eq:general-sslp-colors', [
    forward, 'MainTheory.GeneralColoredConverse.ColoredFrame.sum_rank',
    'MainTheory.ColoredResidueArithmetic.primitive_iff_gcd_eq_one',
], 'ColoredFrame has positive multiplicities, a zero base color and injective color labels. The '
   'forward conclusion and sum_rank give their sum K. The arithmetic equivalence gives the displayed '
   'gcd with m; the designated zero contributes nothing. The converse accepts these same data.')
record('main.tex:eq:general-colored-fibers', [
    'MainTheory.GeneralColoredSubspaces.ColoredFrame.sectorSpace_finrank',
    'MainTheory.GeneralColoredSubspaces.ColoredFrame.sectorSpace_le_computational_span',
    subspaces + 'sectorSpace_eq',
], 'The forward sector spaces have the declared dimensions and lie in the full computational-basis '
   'fiber spans. The new converse accepts arbitrary subspaces satisfying exactly those properties, '
   'and sectorSpace_eq identifies every reconstructed sector with its original input subspace.')

paper_claims.validate(ledger, sources=paper_claims.sources_for_version(version))
paths['ledger'].write_text(json.dumps(ledger, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
priority_path = root / 'results/paper-review-20260924-priority.json'
priority = json.loads(priority_path.read_text(encoding='utf8'))
key = 'main.tex:thm:general-sslp-normal-form'
priority['reviews'][key] = reviews[key]
priority['scope'] = ('19 priority named statements plus Singleton display; follow-up reviews in '
    'results/minimum-length-20260924/review.json and results/colored-subspaces-20260924/review.json; '
    'kernel validation recorded separately')
priority_path.write_text(json.dumps(priority, ensure_ascii=False, indent=2)+'\n', encoding='utf8')

prose = json.loads(paths['prose'].read_text(encoding='utf8'))
row = dict(source='main.tex', line=1000, kind='covered', severity=None,
           declarations=[converse, subspaces+'independent', subspaces+'sectorSpace_eq',
                         subspaces+'finrank_sum', subspaces+'frame_hasDistance'],
           reason='The converse paragraph at lines 1000-1007 now has an arbitrary-subspace entrance: '
                  'the same supplied direct sum is the rank-K code, its complete KL equations give '
                  'the target distance, and the displayed D(a;q) has exact intrinsic order m. '
                  'No orthonormal frame is required from the caller. This is a bounded review '
                  'of that paragraph, not the remainder of the subsequent forward proof.')
prose['assertions'] = [r for r in prose['assertions']
                       if (r['source'], r['line']) != (row['source'], row['line'])] + [row]
note = (' Follow-up arbitrary-subspace review closes the converse paragraph at main lines 1000-1007; '
        'see results/colored-subspaces-20260924/review.json.')
if note not in prose['method']:
    prose['method'] += note
paper_release.validate_review(prose, version)
paths['prose'].write_text(json.dumps(prose, ensure_ascii=False, indent=2)+'\n', encoding='utf8')

files = ['MainTheory/SubspaceCode.lean', 'MainTheory/GeneralColoredSubspaceConverse.lean',
         'MainTheory/PaperGeneralSSLPConverse.lean']
record_data = dict(paper_version=version, sources_sha256=paper_release.source_hashes(version),
    scope='General SSLP theorem and three nested displays; arbitrary-subspace converse paragraph only',
    reviews=reviews, lean_sources_sha256={f: hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files},
    claims_counts=dict(Counter(e['status'] for e in ledger['claims'])))
(Path(__file__).parent/'review.json').write_text(
    json.dumps(record_data, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
print(record_data['claims_counts'])
