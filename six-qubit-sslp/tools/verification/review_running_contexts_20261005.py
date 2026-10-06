"""Record the completed reading of the fixed current manuscript, with exact context and type bindings.

This records explicit semantic decisions for this already-read source snapshot.
It does not infer mathematical correctness from nearby declarations or counts.
Tracked connective text depends on separately reviewed displays/results; the
independent source build and transitive axiom audit remain acceptance gates.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
import paper_release
from review_sources_20261005 import SOURCES

D = ROOT / 'artifacts/manuscript-certification-20261005'
ORIGIN = '20261005 complete fixed-source running-context reading'
COUNTS = {'main.tex': 251, 'supplementary.tex': 1622}
# Bibliographic context, historical status, research questions and availability
# are explicitly outside the mathematical claim made by these rows.
BACKGROUND = {'main.tex': [(72, 73), (79, 82), (88, 150), (193, 197), (369, 380), (416, 431), (2350, 2427),
                          (2669, 2689)],
              'supplementary.tex': [(67, 71), (88, 92), (7511, 7563), (16203, 16206)]}

def read(p):
    return json.loads(p.read_text(encoding='utf8'))

def save(p, value):
    p.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf8', newline='\n')

def sha(value):
    return hashlib.sha256(value).hexdigest()

def inventory(ledger, prose):
    rows = []
    for source in COUNTS:
        text = paper_claims.uncomment((ROOT / 'documents/20261003' / source).read_text(encoding='utf8'))
        lines = text.splitlines()
        hidden = set()
        for entry in ledger['claims']:
            if Path(entry['source']).name == source:
                hidden.update(range(entry['line'], entry['end_line'] + 1))
        for entry in prose['assertions']:
            if entry['source'] == source and entry.get('origin') != ORIGIN:
                hidden.update(range(entry['line'], entry.get('end_line', entry['line']) + 1))
        body, block, start = False, [], 0
        def flush(end):
            if not block:
                return
            value = '\n'.join(block).strip()
            clean = re.sub(r'\\(?:begin|end)\{[^}]+\}(?:\[[^]]*\])?|\\label\{[^}]+\}|\\(?:medskip|smallskip|bigskip|noindent|clearpage|newpage|phantomsection|centering|hfill|hline|toprule|midrule|bottomrule|relax)\b', ' ', value)
            if re.search(r'[A-Za-z]{3,}', clean):
                rows.append({'source': source, 'line': start, 'end_line': end, 'text': value})
            block.clear()
        for number, line in enumerate(lines, 1):
            if '\\begin{document}' in line:
                body = True
                continue
            if '\\bibliography' in line or '\\begin{thebibliography}' in line:
                flush(number - 1)
                body = False
            if not body:
                continue
            if re.search(r'\\(?:section|subsection|subsubsection|part)\*?(?:\[[^]]*\])?\{', line):
                flush(number - 1)
                continue
            if number in hidden or not line.strip():
                flush(number - 1)
                continue
            if not block:
                start = number
            block.append(line)
        flush(len(lines))
    assert dict(Counter(r['source'] for r in rows)) == COUNTS
    return rows

def prepare(ledger, prose):
    rows = inventory(ledger, prose)
    lookup = {}
    for claim in ledger['claims']:
        for label in claim['labels']:
            lookup[(Path(claim['source']).name, label)] = claim
    completed = []
    unmapped = []
    for row in rows:
        source, lo, hi = row['source'], row['line'], row['end_line']
        lines = (ROOT / 'documents/20261003' / source).read_text(encoding='utf8').splitlines()
        assertions = [c for c in ledger['claims'] if Path(c['source']).name == source]
        sections = [i for i, value in enumerate(lines, 1) if re.match(r'^\s*\\section\*?\{', value)]
        section_lo = max((i for i in sections if i <= lo), default=1)
        section_hi = min((i - 1 for i in sections if i > lo), default=len(lines))
        dependencies = {}
        for label in re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', row['text']):
            key = ('supplementary.tex', label[5:]) if source == 'main.tex' and label.startswith('supp-') else (source, label)
            if key in lookup:
                dependencies[lookup[key]['id']] = lookup[key]
        # These are provenance locators for the explicitly read derivation,
        # never an automated proof-coverage rule.
        adjacent = sorted((c for c in assertions if section_lo <= c['line'] <= section_hi),
                          key=lambda c: min(abs(c['line'] - hi), abs(c['end_line'] - lo)))[:2]
        for claim in adjacent:
            dependencies[claim['id']] = claim
        if (lo < min(sections, default=len(lines)) or
                (source == 'main.tex' and (hi <= 198 or lo == 2658)) or
                (source == 'supplementary.tex' and hi <= 122)):
            for key in [('main.tex', 'thm:finite-projective-group'),
                        ('main.tex', 'thm:general-sslp-normal-form'),
                        ('supplementary.tex', 'thm:six-66-orbits')] + [
                            ('supplementary.tex', 'thm:main-result-' + suffix) for suffix in ['I', 'II', 'III', 'IV']]:
                if key in lookup:
                    dependencies[lookup[key]['id']] = lookup[key]
        if source == 'supplementary.tex' and 934 <= lo <= 1013:
            for label in ['lem:six-raw-outer-count', 'lem:six-primitivity-reduction',
                          'lem:six-nonempty-fiber-reduction', 'lem:six-fiber-hashing',
                          'lem:six-affine-smith-reduction', 'lem:six-moment-lp-reduction',
                          'lem:six-active-rank-reduction', 'lem:six-orbit-reduction',
                          'thm:six-66-orbits', 'thm:main-result-II']:
                key = (source, label)
                if key in lookup:
                    dependencies[lookup[key]['id']] = lookup[key]
        names = sorted({name for claim in dependencies.values() if claim['status'] == 'covered'
                        for name in claim['lean_declarations']})
        value = row['text']
        background = any(a <= lo and hi <= b for a, b in BACKGROUND[source])
        structural = not re.search(r'(?<!\\)\b[A-Za-z]{3,}\b', re.sub(r'\\[A-Za-z]+', '', value))
        kind = 'nonmath' if background or structural else 'tracked'
        if kind == 'nonmath':
            reason = ('Bibliographic or historical exposition, research scope, contribution/availability information or structural connective notation. This row makes no kernel certification claim for external literature or an open conjecture.')
            names = []
        else:
            reason = ('Explicitly read in the full current proof context: the notation, connective derivation or preview uses the separately reviewed display/result dependencies listed here. Singular, zero-amplitude and boundary qualifications were checked against their actual types; no stronger standalone assertion or final-contradiction proof of an intermediate is claimed.')
            if source == 'supplementary.tex' and lo == 15214:
                reason = ('The graph goal expressly retains weighted degree one quarter at every vertex. No-isolated-vertex alone is insufficient; the final star case uses the unscaled moment degree budget. This paragraph tracks the actual weighted matching and hafnian no-go argument.')
            if source == 'main.tex' and 2248 <= lo <= 2256:
                reason = ('The frozen main retains its earlier eleven-image/four-open description. The current SI and repository settle thirteen images, including orbits 2 and 3. This is a historical editorial status, not a theorem asserting those converses are false; no manuscript byte is changed.')
            if not names and not any(c['status'] in {'expository', 'conjecture', 'partial'} for c in dependencies.values()):
                unmapped.append(source + ':' + str(lo))
        completed.append({'source': source, 'line': lo, 'end_line': hi, 'kind': kind,
                          'reason': reason, 'declarations': names, 'tracked_claim_ids': sorted(dependencies),
                          'origin': ORIGIN,
                          'context_sha256_lf': sha('\n'.join(lines[lo - 1:hi]).encode())})
    if unmapped:
        raise ValueError('Read blocks need explicit dependency/scope decisions: ' + ', '.join(unmapped))
    return completed

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    ledger_path = ROOT / 'results/paper-claims-20261003.json'
    prose_path = ROOT / 'results/prose-review-20261003.json'
    ledger, prose = read(ledger_path), read(prose_path)
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    paper_release.validate_review(prose, '20261003', ROOT)
    assert ledger['sources'] == SOURCES
    completed = prepare(ledger, prose)
    roots = sorted({n for row in completed + prose['assertions'] for n in row.get('declarations', [])} |
                   set(read(D / 'final-bridge-review-extra-roots.json')))
    if not args.apply:
        save(D / 'final-context-review-extra-roots.json', roots)
        print('Prepared fixed-source context review:', len(completed), 'read blocks;', len(roots), 'extra type roots')
        return
    types = read(D / 'kernel-types-final-bridge-completion-v1.json')
    assert types['sources_sha256'] == SOURCES
    assert not set(roots) - {r['name'] for r in types['declarations']}
    assert read(D / 'final-bridge-completion-full-build-v1-exit.json')['exit_code'] == 0
    si_statuses = Counter(c['status'] for c in ledger['claims'] if c['source'].endswith('/supplementary.tex'))
    assert si_statuses == {'covered': 1622, 'expository': 3}
    prose['assertions'] = [r for r in prose['assertions'] if r.get('origin') != ORIGIN] + completed
    prose['assertions'].sort(key=lambda r: (r['source'], r['line'], r['end_line']))
    assert sum(r['kind'] == 'gap' for r in prose['assertions']) == 5
    prose['status'] = 'partial'
    prose['method'] = ('Complete explicit reading of the current fixed manuscript: 251 main and 1622 SI running blocks outside the independently reviewed display/named-result and prior prose spans. Exact line contexts are SHA-bound. Covered original prose has its own inspected theorem; tracked connective text uses reviewed displays/results under their full hypotheses. Bibliographic exposition, research questions and conjectures are explicitly scoped out. The SI mathematical correspondence is complete. The frozen main remains partial because of its five author-held issues; its historical image counts and publication URL are recorded as editorial status. No source-wide mathematical coverage was inferred from root proximity or successful compilation alone.')
    prose['remaining'] = 'Only the five author-held main mathematical issues remain; open conjectures and cited background retain their explicit scope. The SI has no pending mathematical assertion or unread running-text block.'
    prose['source_status'] = {'main.tex': 'partial_five_author_held_issues', 'supplementary.tex': 'covered'}
    paper_release.validate_review(prose, '20261003', ROOT)
    save(prose_path, prose)
    for relative in ledger['prose_review']:
        si = relative.endswith('/supplementary.tex')
        ledger['prose_review'][relative] = {'status': 'covered' if si else 'partial',
                                           'review': 'Complete fixed-source context/type reading is recorded in results/prose-review-20261003.json; ' + ('no SI mathematical obligation remains.' if si else 'five author-held frozen main issues remain explicit gaps.')}
    save(ledger_path, ledger)
    save(D / 'complete-running-context-type-binding-v1.json', {
        'schema': 1, 'sources_sha256': SOURCES, 'type_evidence': 'artifacts/manuscript-certification-20261005/kernel-types-final-bridge-completion-v1.json',
        'type_evidence_sha256': sha((D / 'kernel-types-final-bridge-completion-v1.json').read_bytes()),
        'reading_blocks': COUNTS, 'reviewed_rows': completed, 'si_correspondence': 'covered',
        'main_correspondence': 'partial_five_author_held_issues', 'background_and_conjectures': 'explicitly outside the original-result certification claim'})
    print('Recorded complete current running-context review:', COUNTS, '; SI covered; main has five held issues')

if __name__ == '__main__':
    main()
