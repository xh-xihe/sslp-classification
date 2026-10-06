"""Record explicitly checked prose blocks without claiming source-wide completion."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
import paper_release
from review_sources_20261005 import SOURCES

C = 'MainTheory.PrimitiveOrderTwoCatCompression.'
E = 'MainTheory.PrimitiveOrderTwoCatEncoder.'
K = 'MainTheory.PrimitiveOrderTwoCatKL.'
S = 'MainTheory.PrimitiveOrderTwoCatSpinFlip.'
H = 'MainTheory.Orbit3PrintedHomogeneousTarget.'
ROWS = [
    ('supplementary.tex',4369,4370,'covered',
     [E+'encoder_apply',E+'encoder_isometry'],
     'The literal cat coefficients give two orthonormal actual physical '
     'columns under the printed real quadratic parameter constraint.'),
    ('supplementary.tex',4373,4377,'covered',
     [C+'cats',C+'single_zero',C+'ZZ',C+'XX_YY',C+'mixed_zero',K+'small_label'],
     'The actual five-cat embedding kills all nonidentity single-site '
     'Paulis. The only nonzero two-site types are ZZ and equal XX/YY; '
     'constructive support classification exhausts all weight-at-most-two labels.'),
    ('supplementary.tex',4406,4418,'covered',
     [K+'real_tail_KL',K+'first_pauli_KL',K+'one_tail_zero',K+'weight_split',K+'full_KL'],
     'Tail-only, first-site-only and first/tail Pauli factors exhaust the '
     'actual weight-at-most-two matrix compressions. The constructive '
     'proof retains all real normalized parameters and uses no nonzero '
     'individual amplitude premise or division by an amplitude.'),
    ('supplementary.tex',4440,4441,'covered',
     [S+'overlap_zero',S+'projectors_orthogonal',S+'spin_trace_zero'],
     'The actual six-qubit code projector is orthogonal to its conjugate '
     'six-Y spin flip and their product has zero trace. The subsequent '
     'enumerator conclusion is outside this reviewed prose block.'),
    ('supplementary.tex',5607,5607,'covered',
     [H+'raw_expectation',H+'homogeneous_target'],
     'The target identity retains arbitrary raw amplitudes and only '
     'divides by the positive common column norm. No amplitude or '
     'Schmidt coefficient is required to be nonzero.'),
    ('main.tex',274,277,'gap',[],
     'Author-held frozen main issue: the unrestricted Singleton statement '
     'includes rank one and is false there. The repository carries both '
     'the corrected rank-at-least-two theorem and a kernel counterexample. '
     'A proof of a corrected statement cannot certify this frozen wording.'),
    ('main.tex',172,176,'gap',[],
     'Author-held frozen main issue: the introductory diagonal-group '
     'finiteness claim needs the fixed-product-basis and single-site '
     'detection hypotheses used by the actual theorem.'),
    ('main.tex',269,272,'gap',[],
     'Author-held frozen main issue: probability moment rows implement '
     'diagonal Z detection; full X/Y KL conditions also involve complex phases.'),
    ('main.tex',1825,1827,'gap',[],
     'Author-held frozen main issue: physical-order minimization in this '
     'sentence has a broader representative scope than the reduced '
     'diagonal definition used by its corresponding result.'),
    ('main.tex',684,686,'gap',[],
     'Author-held frozen main issue: rational homogeneous replacement '
     'preserves the specified image/kernel information; this must not be '
     'read as equality of the entire homogeneous component.'),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    if paper_release.source_hashes('20261003',ROOT) != SOURCES:
        raise ValueError('Reviewed source context changed')
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-physical-formulas.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Type evidence belongs to another manuscript')
    missing = {n for row in ROWS for n in row[4]}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected declaration types: '+str(missing))
    record_path = ROOT/'results/prose-review-20261003.json'
    record = json.loads(record_path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    reviewed = []
    for source,line,end_line,kind,declarations,reason in ROWS:
        lines = (ROOT/'documents/20261003'/source).read_text(encoding='utf8').splitlines()
        context = '\n'.join(lines[line-1:end_line])
        reviewed.append({'source':source,'line':line,'end_line':end_line,
                         'kind':kind,'reason':reason,'declarations':declarations,
                         'origin':'20261005 explicit current context/type review',
                         'context_sha256_lf':hashlib.sha256(context.encode()).hexdigest()})
    keys = {(r['source'],r['line'],r.get('end_line',r['line'])) for r in reviewed}
    retained = [r for r in record['assertions']
                if (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]
    record['assertions'] = sorted(retained+reviewed,key=lambda r:(r['source'],r['line']))
    record['status'] = 'partial'
    record['method'] = ('Explicit review of the frozen 20261003 main source and current SI. '
                        'Reviewed prose blocks bind their exact current line ranges and '
                        'kernel-inspected physical theorem types. All other running text '
                        'still requires review. Five author-held main issues remain gaps; '
                        'the main source is unchanged. No source-wide coverage is inherited.')
    record['remaining'] = ('Complete all other current prose/context review and the remaining '
                           'display/named-result obligations. Preserve the five frozen '
                           'main issues until the author changes their disposition.')
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        record_path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        ledger_path = ROOT/'results/paper-claims-20261003.json'
        ledger = json.loads(ledger_path.read_text(encoding='utf8'))
        if ledger['sources'] != SOURCES:
            raise ValueError('Ledger source context changed')
        for relative in ledger['prose_review']:
            ledger['prose_review'][relative] = {
                'status':'partial',
                'review':'Explicit reviewed blocks are recorded in results/prose-review-20261003.json; '
                         'the rest of this current source remains under review.'}
        ledger_path.write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (path.parent/'current-prose-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(path.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'reviewed_blocks':reviewed,'scope':'partial current prose only'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Explicitly reviewed prose blocks:',len(reviewed),'status:',record['status'])

if __name__ == '__main__':
    main()
