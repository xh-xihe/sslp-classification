"""Record the common-pivot semantic review against unchanged manuscript bytes."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root/'tools'))
import paper_claims
import paper_release

version = '20260924'
assert paper_release.source_hashes(version) == {
    'documents/20260924/main.tex': '0015798c22359efffe64afd26bda2d057b71fd4b6b408062a6672193b487e542',
    'documents/20260924/supplementary.tex': 'a0f59088de371644a396fdd40ac218e4be803949b174a095c3233606c324cb37',
}, 'Repeat semantic review if either manuscript changes'
paths = paper_release.paths(version)
ledger = json.loads(paths['ledger'].read_text(encoding='utf8'))
paper_claims.validate(ledger, sources=paper_claims.sources_for_version(version))
rows = {row['id']: row for row in ledger['claims']}
reviews = {}
headline = 'MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects'
bridge = 'MainTheory.BinaryPivotLift.'


def record(key, names, reason):
    row = rows[key]
    row.update(status='covered', lean_declarations=names,
               review='2026-09-26 common binary-pivot/physical-lift semantic review. ' + reason)
    reviews[key] = dict(status='covered', reason=reason, lean_declarations=names,
                        statement_sha256=row['statement_sha256'])


record('main.tex:thm:colored-finite-lift', [
    headline, bridge+'binarySolution_solves', bridge+'rationalLift_augmented_eq_binarySolution',
    bridge+'rationalLift_order_dvd_smithLastFactor',
    'MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det',
], 'The single combined theorem assumes only single-site Z detection, an actual diagonal symmetry, '
   'its real-angle representative and nontrivial intrinsic class. Its spectral resolution is the '
   'canonical one, so ell is the actual number of distinct logical eigenvalues, not an unrelated '
   'existential sector count. It chooses one nonsingular pivot P of the colored matrix and uses '
   'L=P.rationalLift throughout. Its zero-one partner uses the same rows and columns. The literal '
   'binary solution solves the selected integral-right-hand-side system, and undoing column signs '
   'and extending by zero gives exactly L.augmented. An actual normalized Smith witness W is '
   'constructed for that binary matrix, with L.order dividing W.lastFactor. The same L gives the '
   'primitive modular angle and actual symmetry in the original intrinsic class; its projective '
   'order divides L.order. The bound s<=n+ell-1, the Smith-factor beta bound and ell<=K all occur '
   'in the same conclusion. An attained minimum over HasPrimitiveLift is bounded by this very '
   'L.order and hence beta_(n+ell-1). There is no supplied pivot/Smith witness, stronger distance '
   'assumption, or separately chosen physical lift. The root uses the existing repository '
   'constructions rather than re-proving Smith existence or rationalization.')
record('main.tex:eq:general-q-bound', [headline],
       'The same representative has m dividing q, q<=beta_(n+ell-1), and '
       'beta_(n+ell-1)<=beta_(n+K-1); ell is the actual spectral count of the input operation.')
record('main.tex:eq:q-divides-smith', [headline, bridge+'rationalLift_order_dvd_smithLastFactor'],
       'The combined witness includes s equal to the colored-matrix rank, s<=n+ell-1, '
       'an invertible zero-one matrix and its actual Smith decomposition W. Its physical lift '
       'has q dividing W.lastFactor. The supporting theorem proves this for every Smith witness '
       'of the same binary matrix, not just a specially chosen last factor.')
record('main.tex:eq:qmin-general', [headline],
       'An attained minimum is taken over precisely HasPrimitiveLift for the original intrinsic '
       'class. Its universal minimality and bound by the constructed q are explicit, followed '
       'by the beta bound with the original gate spectral count. No d>=2 premise is added.')
record('main.tex:eq:pivot-solve', [bridge+'binarySolution_solves',
       bridge+'rationalLift_augmented_eq_binarySolution', headline],
       'binarySolution is the exact rational inverse of the selected zero-one matrix applied '
       'to the selected integral right-hand side, and binarySolution_solves proves the literal '
       'matrix equation. The next bridge identifies its sign-restored zero extension with the '
       'actual rational lift used in the paper-facing theorem. The zero-one partner is precisely '
       'the local-X-normalized support matrix; the signs undo that normalization.')

paper_claims.validate(ledger, sources=paper_claims.sources_for_version(version))
paths['ledger'].write_text(json.dumps(ledger, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
priority_path = root/'results/paper-review-20260924-priority.json'
priority = json.loads(priority_path.read_text(encoding='utf8'))
key = 'main.tex:thm:colored-finite-lift'
priority['reviews'][key] = reviews[key]
priority['scope'] = ('19 priority named statements plus Singleton display; follow-up reviews in '
    'results/minimum-length-20260924, results/colored-subspaces-20260924 and '
    'results/colored-lift-smith-20260924; kernel validation recorded separately')
priority_path.write_text(json.dumps(priority, ensure_ascii=False, indent=2)+'\n', encoding='utf8')

prose = json.loads(paths['prose'].read_text(encoding='utf8'))
assertion = dict(source='main.tex', line=1336, kind='covered', severity=None,
    declarations=[headline, bridge+'rationalLift_augmented_eq_binarySolution',
                  bridge+'rationalLift_order_dvd_smithLastFactor'],
    reason='The common-construction claim at lines 1336-1343 is now explicit: the representative '
           'comes from the solved binary pivot whose actual Smith factor is divisible by its '
           'modulus. The same witness also carries the actual eigenvalue-count bound and '
           'original projective action. This bounded review does not mark all subsequent '
           'normalization/common-mean proof prose complete.')
prose['assertions'] = [r for r in prose['assertions']
                      if (r['source'], r['line']) != ('main.tex', 1336)] + [assertion]
note = (' Follow-up common-witness review closes the binary-pivot/Smith/physical-lift claim '
        'at main lines 1336-1343; see results/colored-lift-smith-20260924/review.json.')
if note not in prose['method']:
    prose['method'] += note
paper_release.validate_review(prose, version)
paths['prose'].write_text(json.dumps(prose, ensure_ascii=False, indent=2)+'\n', encoding='utf8')

files = ['MainTheory/BinaryPivotLift.lean', 'MainTheory/PaperColoredFiniteLift.lean']
data = dict(paper_version=version, sources_sha256=paper_release.source_hashes(version),
    scope='Colored finite-lift theorem, three nested bounds and the binary pivot equation; not full prose review',
    reviews=reviews, lean_sources_sha256={f: hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files},
    claims_counts=dict(Counter(row['status'] for row in ledger['claims'])))
(Path(__file__).parent/'review.json').write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
print(data['claims_counts'])
