"""Archive actual completed build/audit evidence for this bounded increment."""
import hashlib
import json
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / 'tools'))
import verify

folder = Path(__file__).parent
run = root / 'tmp/verification/20260924'


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


review = read(folder/'review.json')
build = read(folder/'build.json')
axioms = read(run/'axioms.json')
report = read(run/'report.json')
assert build == read(root/'.lake/build/certification/success.json')
assert axioms['passed'] and axioms['exit_code'] == 0
assert set(axioms['axiom_union']) <= verify.ALLOWED
roots, targets, input_hashes = verify.axiom_inventory(paper_version='20260924')
assert roots == axioms['roots'] and input_hashes == axioms['audit_sources_sha256']
assert set(targets) <= set(build['modules'])
assert all(sha(root/name) == digest for name, digest in {
    **review['sources_sha256'], **review['lean_sources_sha256']}.items())
checks = {row['check']: row for row in report['checks']}
assert all(checks[name]['passed'] for name in
           ['release', 'axioms', 'audit-names', 'named-results', 'readme'])
assert all(not checks[name]['passed'] for name in ['claims', 'prose-review', 'errata'])
assert not report['full_suite'] and not report['passed']

certificates = {}
for source, digest in review['lean_sources_sha256'].items():
    name = source.removesuffix('.lean').replace('/', '.')
    stamp = read(root/'.lake/build/certification/stamps'/source.replace('.lean', '.json'))
    assert stamp['source_sha256'] == digest and build['modules'][name] == stamp['key']
    assert all(sha(root/path) == expected for path, expected in stamp['outputs'].items())
    certificates[name] = stamp
(folder/'module-certificates.json').write_text(json.dumps(certificates, indent=2)+'\n', encoding='utf8')

swept = [*review['lean_sources_sha256'], 'MainTheory.lean', 'MainTheory/Audit.lean']
hits = {name: verify.FORBIDDEN.findall(verify.code_only((root/name).read_text(encoding='utf8')))
        for name in swept}
assert not any(hits.values())
(folder/'source-sweep.json').write_text(json.dumps(dict(passed=True, scope=swept, hits=hits), indent=2)+'\n', encoding='utf8')

for name in ['report.json', 'axioms.json', 'axioms.log', 'axiom-union.lean', 'release.json',
             'audit-names.log', 'named-results.log', 'readme-names.log', 'claims.log', 'prose-review.log']:
    shutil.copyfile(run/name, folder/name)
shutil.copyfile(root/'tmp/build-colored-subspaces-20260924.log', folder/'build.log')

validation = dict(
    validated_at_utc=datetime.now(timezone.utc).isoformat(),
    platform='Windows; native PowerShell, lake and Lean; no WSL',
    paper_version='20260924', proof_increment_passed=True,
    full_manuscript_certification=False,
    source_hashes=review['sources_sha256'],
    build=dict(scope='Complete current audit import dependency closure; content-validated reuse',
               modules=len(build['modules']), rebuilt=build['rebuilt'], reused=build['reused'],
               context=build['context'],
               note='The three new leaf modules were compiled by the serial source driver before '
                    'the shared-state kernel audit. Individual-print audit wrappers were not built.'),
    axioms=dict(roots=len(roots), allowed_union=axioms['axiom_union'], passed=True),
    acceptance_checks=report, source_sweep_passed=True,
    tooling_sources_sha256={name: sha(root/name) for name in
        ['tools/check-readme-names.py', 'tools/build_lean.py', 'tools/verify.py',
         'tools/paper_claims.py', 'tools/paper_release.py']},
    ledger_counts=review['claims_counts'], unchanged_manuscripts=True,
    artifacts={p.name: sha(p) for p in sorted(folder.iterdir())
               if p.is_file() and p.name not in {'validation.json', 'README.md'}})
(folder/'validation.json').write_text(json.dumps(validation, indent=2)+'\n', encoding='utf8')
print(json.dumps({key: validation[key] for key in
    ['proof_increment_passed', 'full_manuscript_certification', 'build', 'axioms', 'ledger_counts']}, indent=2))
