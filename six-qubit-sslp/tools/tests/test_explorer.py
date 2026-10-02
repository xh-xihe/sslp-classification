"""Boundary, independent arithmetic, migration and evidence-integrity tests."""
import copy
import json
import math
from pathlib import Path
import shutil
import sys
import unittest
from unittest.mock import patch
import uuid

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from explorer import class36
import paper_claims
import paper_migration
import sslp_explorer


class Workspace(unittest.TestCase):
    def setUp(self):
        self.root = TOOLS.parent / 'tmp' / 'explorer-tests' / uuid.uuid4().hex
        self.root.mkdir(parents=True)
        self.addCleanup(self.cleanup)

    def cleanup(self):
        if self.root.resolve().is_relative_to((TOOLS.parent / 'tmp/explorer-tests').resolve()):
            shutil.rmtree(self.root)


class VersionMigration(Workspace):
    def test_source_date_change_does_not_inherit_coverage(self):
        for date in ('20260908', '20260924'):
            path = self.root / f'documents/{date}/main.tex'
            path.parent.mkdir(parents=True)
            path.write_text('\\begin{theorem}\\label{thm:a}A\\end{theorem}', encoding='utf-8')
        old_source = ('documents/20260908/main.tex',)
        new_source = ('documents/20260924/main.tex',)
        with patch.object(paper_claims, 'ROOT', self.root):
            old = paper_claims.snapshot(sources=old_source)
            old['claims'][0].update(status='covered', lean_declarations=['Old.result'], review='old review')
            new = paper_claims.snapshot(old, sources=new_source)
            self.assertEqual(new['claims'][0]['status'], 'unreviewed')
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                paper_claims.validate(new, require_complete=True, sources=new_source)

    def test_cross_document_move_is_candidate_not_new_proof(self):
        before = {'id': 'main.tex:thm:a', 'source': 'documents/old/main.tex', 'labels': ['thm:a'],
                  'line': 1, 'kind': 'theorem', 'statement_sha256': 'a', 'status': 'covered',
                  'lean_declarations': ['Old.result']}
        after = dict(before, id='supplementary.tex:thm:a', source='documents/new/supplementary.tex',
                     line=99, status='unreviewed', lean_declarations=[])
        result = paper_migration.compare({'sources': {}, 'claims': [before]}, {'sources': {}, 'claims': [after]})
        row = result['claims'][0]
        self.assertTrue(row['cross_document_candidate'])
        self.assertEqual(row['category'], 'same_statement_review_required')
        self.assertFalse(row['certification_transferred'])

    def test_duplicate_unlabelled_statements_are_ambiguous(self):
        def entry(line):
            return {'id': f'main.tex:equation@{line}', 'source': 'main.tex', 'labels': [], 'line': line,
                    'kind': 'equation', 'statement_sha256': 'same', 'status': 'unreviewed', 'lean_declarations': []}
        report = paper_migration.compare({'sources': {}, 'claims': [entry(1), entry(2)]},
                                         {'sources': {}, 'claims': [entry(3)]})
        self.assertEqual(report['claims'][0]['category'], 'ambiguous')
        self.assertEqual(paper_migration.stable_key(entry(1)), paper_migration.stable_key(entry(3)))

    def test_version_path_traversal_is_rejected(self):
        with self.assertRaises(ValueError):
            paper_claims.sources_for_version('../20260924')


class ExactCase(unittest.TestCase):
    def test_all_154_matrices_match_independent_complex_action(self):
        data = class36.example()
        exact = class36.exact_checks(data)
        roots = [1, math.sqrt(2), math.sqrt(3), math.sqrt(6), 1j,
                 1j * math.sqrt(2), 1j * math.sqrt(3), 1j * math.sqrt(6)]
        def number(coords):
            return sum(c * r for c, r in zip(coords, roots))
        vectors = []
        for rows in data['words']:
            state = [0j] * 64
            for row in rows:
                # Independently reconstruct the little-endian mask.
                mask = sum((int(bit) << i) for i, bit in enumerate(row['bits']))
                state[mask] = number(row['coordinates']) / math.sqrt(120)
            vectors.append(state)
        self.assertEqual(len(exact['kl']), 154)
        self.assertTrue(exact['passed'])
        for row in exact['kl']:
            x, z = row['x_mask'], row['z_mask']
            for j in range(2):
                for k in range(2):
                    reference = sum(vectors[j][s ^ x].conjugate() *
                                    (1j ** (x & z).bit_count()) * ((-1) ** (z & s).bit_count()) *
                                    vectors[k][s] for s in range(64))
                    actual = number(row['matrix_coordinates'][j][k]) / 120
                    self.assertLess(abs(actual - reference), 1e-12)
        yy = next(r for r in exact['kl'] if r['pauli'] == 'Y5Y6')
        self.assertAlmostEqual((number(yy['matrix_coordinates'][0][0]) / 120).real, -1 / 5)

    def test_wrong_single_amplitude_phase_breaks_kl_without_changing_norm(self):
        data = class36.example()
        data['words'][0][0]['coordinates'] = [-x for x in data['words'][0][0]['coordinates']]
        result = class36.exact_checks(data)
        self.assertTrue(result['normalization_and_orthogonality'])
        self.assertFalse(result['passed'])
        self.assertTrue(any(not row['passed'] for row in result['kl']))

    def test_whole_logical_phase_preserves_kl(self):
        data = class36.example()
        for row in data['words'][1]:
            row['coordinates'] = [-x for x in row['coordinates']]
        self.assertTrue(class36.exact_checks(data)['passed'])
        # Kernel adapter deliberately requires the documented canonical logical basis.
        self.assertIn('data1_matches', class36.lean_certificate(data))

    def test_wrong_gate_is_separate_from_kl(self):
        data = class36.example()
        data['gate']['angles'][0] = 2
        result = class36.exact_checks(data)
        self.assertTrue(all(r['passed'] for r in result['kl']))
        self.assertFalse(result['support_matches_gate'])
        self.assertFalse(result['passed'])

    def test_boundary_inputs_are_rejected(self):
        for mutate in (lambda d: d['words'][0].append(copy.deepcopy(d['words'][0][0])),
                       lambda d: d['words'][0][0]['coordinates'].__setitem__(0, 0.0),
                       lambda d: d['words'][0][0]['coordinates'].__setitem__(0, True),
                       lambda d: d.__setitem__('gate', []),
                       lambda d: d['conventions'].__setitem__('bitstring', 'opposite bit order')):
            data = class36.example()
            mutate(data)
            with self.assertRaises(ValueError):
                class36.validate(data)

    def test_metadata_cannot_inject_lean(self):
        data = class36.example()
        data['id'] = 'AXIOM_INJECTION_SENTINEL'
        self.assertNotIn(data['id'], class36.lean_certificate(data))

    def test_examples_do_not_share_mutable_conventions(self):
        data = class36.example()
        data['conventions']['qubit_labels'][0] = 6
        self.assertEqual(class36.example()['conventions']['qubit_labels'], [1, 2, 3, 4, 5, 6])
        with self.assertRaises(ValueError):
            class36.validate(data)

    def test_class_label_cannot_misrepresent_the_canonical_pair(self):
        data = class36.example()
        data['orbit']['id'] = 61
        with self.assertRaisesRegex(ValueError, 'class-36'):
            class36.validate(data)


class EvidenceBundles(Workspace):
    def test_exact_only_status_and_bundle_tamper_detection(self):
        run, bundle = self.root / 'run', self.root / 'bundle'
        result = sslp_explorer.verify_case(class36.example(), run)
        self.assertTrue(result['passed_requested_checks'])
        self.assertEqual(result['kernel']['status'], 'not_run')
        sslp_explorer.export_bundle(run, bundle)
        self.assertTrue(sslp_explorer.check_bundle(bundle)['hashes_match'])
        path = bundle / 'case.json'
        path.write_text(path.read_text(encoding='utf-8') + ' ', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'hash mismatch'):
            sslp_explorer.check_bundle(bundle)

    def test_changed_run_cannot_be_exported(self):
        run = self.root / 'run'
        sslp_explorer.verify_case(class36.example(), run)
        data = sslp_explorer.read_json(run / 'case.json')
        data['gate']['angles'][0] = 2
        sslp_explorer.write_json(run / 'case.json', data)
        with self.assertRaisesRegex(ValueError, 'changed after'):
            sslp_explorer.export_bundle(run, self.root / 'bundle')

    def test_existing_output_is_not_reused(self):
        run = self.root / 'run'
        sslp_explorer.verify_case(class36.example(), run)
        with self.assertRaisesRegex(ValueError, 'new or empty'):
            sslp_explorer.verify_case(class36.example(), run)

    def test_missing_manifest_entry_is_not_accepted(self):
        run, bundle = self.root / 'run', self.root / 'bundle'
        sslp_explorer.verify_case(class36.example(), run)
        sslp_explorer.export_bundle(run, bundle)
        path = bundle / 'bundle-manifest.json'
        manifest = sslp_explorer.read_json(path)
        del manifest['files_sha256']['case.json']
        sslp_explorer.write_json(path, manifest)
        with self.assertRaisesRegex(ValueError, 'required bundle files'):
            sslp_explorer.check_bundle(bundle)

    def test_duplicate_json_keys_rejected(self):
        path = self.root / 'bad.json'
        path.write_text('{"schema": "first", "schema": "second"}')
        with self.assertRaisesRegex(ValueError, 'duplicate JSON'):
            sslp_explorer.read_json(path)


if __name__ == '__main__':
    unittest.main()
