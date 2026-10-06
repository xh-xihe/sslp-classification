"""Negative controls for cross-version acceptance and incomplete reviews."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import subprocess
import unittest
from unittest.mock import patch
import uuid

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_release as release
import paper_claims
import verify
import named_results_doc


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.root = ROOT / 'tmp' / ('test-release-' + uuid.uuid4().hex)
        self.root.mkdir(parents=True)
        self.addCleanup(self.cleanup)
        for v in ('20260908', '20260924'):
            for name in ('main', 'supplementary'):
                self.write(f'documents/{v}/{name}.tex', v + name)
            hashes = release.source_hashes(v, self.root)
            self.write(f'results/paper-claims-{v}.json', {'sources': hashes, 'claims': []})
            self.write(f'results/named-results-{v}.md', 'review pending')
            self.write(f'results/prose-review-{v}.md', 'review pending')
            self.write(f'results/prose-review-{v}.json', {
                'paper_version': v, 'sources_sha256': hashes, 'status': 'unreviewed',
                'method': 'No coverage transferred.', 'assertions': []})
            self.write(f'results/errata-{v}.json', {
                'paper_version': v, 'sources_sha256': hashes, 'status': 'partial',
                'issues': [{'id': 'singleton', 'status': 'present'}]})
            p = release.paths(v, self.root)
            self.write(p['manifest'].relative_to(self.root), {
                '1': {'q': 2}, '_no_go': {}, '_paper': {'sources_sha256': hashes}})
        self.write('results/errata-20260908.md', 'historical')
        for i, name in enumerate(verify.AUDIT_FILES):
            self.write(name, f'import Lean\n#print axioms Test.root{i}\n')

    def cleanup(self):
        if self.root.resolve().parent == (ROOT / 'tmp').resolve():
            shutil.rmtree(self.root)

    def write(self, name, data):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(data) if isinstance(data, dict) else data, encoding='utf-8')
        return p

    def test_version_selects_only_its_ledger_axioms(self):
        for v in ('20260908', '20260924'):
            self.write(f'results/paper-claims-{v}.json', {'claims': [
                {'status': 'covered', 'lean_declarations': ['Test.v' + v]}]})
        roots, _, hashes = verify.axiom_inventory(self.root, '20260924')
        self.assertIn('Test.v20260924', roots)
        self.assertNotIn('Test.v20260908', roots)
        self.assertIn('results/paper-claims-20260924.json', hashes)
        (self.root / 'results/paper-claims-20260924.json').unlink()
        with self.assertRaisesRegex(ValueError, 'missing selected'):
            verify.axiom_inventory(self.root, '20260924')

    def test_old_orbit_provenance_cannot_validate_new_release(self):
        release.binding('20260924', self.root)
        old = release.paths('20260908', self.root)['manifest'].read_text()
        self.write('results/orbit-manifest-20260924.json', old)
        with self.assertRaisesRegex(ValueError, 'manifest source hashes'):
            release.binding('20260924', self.root)

    def test_shared_math_data_cannot_silently_disagree(self):
        p = release.paths('20260924', self.root)['manifest']
        manifest = json.loads(p.read_text())
        manifest['1']['q'] = 3
        self.write(p.relative_to(self.root), manifest)
        with self.assertRaisesRegex(ValueError, 'shared mathematical'):
            release.binding('20260924', self.root)

    def test_private_directory_override_must_match_selected_release(self):
        with self.assertRaisesRegex(ValueError, 'source-dir differs'):
            release.binding('20260924', self.root, self.root / 'documents/20260908')

    def test_private_directory_works_without_default_manuscript_directory(self):
        private = self.root / 'private-author-input'
        source = self.root / 'documents/20260924'
        source.rename(private)
        report = release.binding('20260924', self.root, private)
        self.assertEqual(report['sources_sha256'], release.source_hashes('20260924', self.root, private))
        record = json.loads(release.paths('20260924', self.root)['prose'].read_text())
        release.validate_review(record, '20260924', self.root, source_dir=private)
        ok, detail = release.check_errata('20260924', self.root, private)
        self.assertFalse(ok)
        self.assertIn('singleton', detail)
        (private / 'main.tex').write_text('changed private manuscript', encoding='utf8')
        with self.assertRaisesRegex(ValueError, 'source-dir differs'):
            release.binding('20260924', self.root, private)

    def test_incomplete_and_stale_prose_cannot_pass(self):
        record = json.loads(release.paths('20260924', self.root)['prose'].read_text())
        release.validate_review(record, '20260924', self.root)
        with self.assertRaisesRegex(ValueError, 'not complete'):
            release.validate_review(record, '20260924', self.root, True)
        record['status'] = 'covered'
        with self.assertRaisesRegex(ValueError, 'not complete'):
            release.validate_review(record, '20260924', self.root, True)
        record['paper_version'] = '20260908'
        with self.assertRaisesRegex(ValueError, 'version or manuscript'):
            release.validate_review(record, '20260924', self.root)

    def test_unresolved_erratum_blocks_acceptance(self):
        ok, detail = release.check_errata('20260924', self.root)
        self.assertFalse(ok)
        self.assertIn('singleton', detail)

    def test_rebinding_source_hash_does_not_hide_stale_prose_context(self):
        path = self.root / 'documents/20260924/main.tex'
        path.write_bytes(b'first\r\nsecond\r\n')
        record = {'paper_version': '20260924',
                  'sources_sha256': release.source_hashes('20260924', self.root),
                  'status': 'partial', 'method': 'Explicit paragraph review.',
                  'assertions': [{'source': 'main.tex', 'line': 1, 'end_line': 2,
                                  'kind': 'nonmath', 'reason': 'Fixture context.',
                                  'context_sha256_lf': hashlib.sha256(b'first\nsecond').hexdigest()}]}
        release.validate_review(record, '20260924', self.root)
        path.write_bytes(b'first\r\nchanged\r\n')
        record['sources_sha256'] = release.source_hashes('20260924', self.root)
        with self.assertRaisesRegex(ValueError, 'prose context changed'):
            release.validate_review(record, '20260924', self.root)
        record['assertions'][0]['end_line'] = 3
        with self.assertRaisesRegex(ValueError, 'invalid line range'):
            release.validate_review(record, '20260924', self.root)

    def test_selected_version_reaches_all_manuscript_subcommands(self):
        with patch.object(verify, 'ROOT', self.root), \
             patch.object(verify, 'recorded_command', return_value=(True, 'fixture')) as command:
            checks = verify.checks(paper_version='20260924')
            for key in ('claims', 'named-results', 'prose-review', 'readme', 'audit-names'):
                checks[key]()
                self.assertIn('20260924', command.call_args.args[1])
            for key in ('paper', 'table-kernel', 'table-kernel-selftest'):
                checks[key]()
                args = command.call_args.args[1]
                self.assertIn(str(self.root / 'documents/20260924'), args)
                self.assertIn(str(self.root / 'results/orbit-manifest-20260924.json'), args)

    def test_private_source_directory_reaches_named_results_check(self):
        private = self.root / 'private-author-input'
        with patch.object(verify, 'ROOT', self.root), \
             patch.object(verify, 'recorded_command', return_value=(True, 'fixture')) as command:
            checks = verify.checks(source_dir=private, paper_version='20260924')
            for key in ('claims', 'named-results', 'prose-review'):
                checks[key]()
                self.assertIn('--source-dir', command.call_args.args[1])
                self.assertIn(str(private), command.call_args.args[1])

    def test_named_results_generator_accepts_private_source_directory(self):
        private = self.root / 'private-author-input'
        (self.root / 'documents/20260924').rename(private)
        ledger = paper_claims.snapshot(sources=paper_claims.sources_for_version('20260924'),
                                       source_dir=private)
        self.write('results/paper-claims-20260924.json', ledger)
        with patch.object(named_results_doc, 'ROOT', str(self.root)):
            code = named_results_doc.main(['--paper-version', '20260924', '--source-dir', str(private)])
        self.assertEqual(code, 0)
        self.assertTrue(release.paths('20260924', self.root)['named'].is_file())

    def test_new_named_report_does_not_inherit_historical_coverage(self):
        record = {'claims': [{'id': 'main.tex:thm:new', 'kind': 'theorem',
            'source': 'documents/20260924/main.tex', 'line': 1,
            'status': 'unreviewed', 'lean_declarations': [], 'review': ''}]}
        text = named_results_doc.render_version(record, '20260924')
        self.assertIn('unreviewed=1', text)
        self.assertIn('No review recorded', text)
        self.assertNotIn('no unreviewed', text)

    def test_path_traversal_rejected(self):
        with self.assertRaises(ValueError):
            release.paths('../20260924', self.root)

    def test_changed_context_invalidates_unchanged_statement(self):
        source = ('documents/20260924/main.tex', 'documents/20260924/supplementary.tex')
        self.write(source[0], '\\begin{theorem}\\label{thm:a}A\\end{theorem}')
        self.write(source[1], 'Definition of A: old assumption.')
        with patch.object(paper_claims, 'ROOT', self.root):
            old = paper_claims.snapshot(sources=source)
            old['claims'][0].update(status='covered', lean_declarations=['Test.result'], review='Reviewed.')
            self.write(source[1], 'Definition of A: a different assumption.')
            fresh = paper_claims.snapshot(old, sources=source)
            self.assertEqual(old['claims'][0]['statement_sha256'], fresh['claims'][0]['statement_sha256'])
            self.assertEqual(fresh['claims'][0]['status'], 'unreviewed')
            with self.assertRaisesRegex(ValueError, 'drift'):
                paper_claims.validate(old, sources=source)

    def test_portable_source_sweep_import_needs_no_release_records(self):
        for name in ('verify.py', 'lean_source.py', 'lean_audit.py'):
            shutil.copyfile(ROOT / 'tools' / name, self.root / name)
        proc = subprocess.run([sys.executable, '-I', '-c',
            'import sys; sys.path.insert(0, sys.argv[1]); from verify import FORBIDDEN; '
            'assert FORBIDDEN.search("sorry")', str(self.root)],
            cwd=self.root, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_prose_proof_roots_are_included_in_kernel_audit(self):
        p = release.paths('20260924', self.root)['prose']
        record = json.loads(p.read_text())
        record['assertions'] = [{'kind': 'covered', 'declarations': ['Test.proseOnly']}]
        self.write(p.relative_to(self.root), record)
        roots, _, hashes = verify.axiom_inventory(self.root, '20260924')
        self.assertIn('Test.proseOnly', roots)
        self.assertIn('results/prose-review-20260924.json', hashes)


if __name__ == '__main__':
    unittest.main()
