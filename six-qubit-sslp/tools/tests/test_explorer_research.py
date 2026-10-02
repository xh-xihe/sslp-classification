"""Generic input semantics, independent matrix oracle, API and portable bundles."""
import copy
import json
import math
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from explorer import class36, research
from explorer.jobs import validate_request
from explorer.providers import load_config
from explorer.agent import ToolSession
from tools.tests.test_explorer import Workspace
import sslp_explorer

ROOT = Path(__file__).resolve().parents[2]

def fixture(name='01-pass-four-qubit'):
    return json.loads((ROOT / 'artifacts/workbench-acceptance-20260929' / (name + '.json')).read_text())


class ResearchInput(unittest.TestCase):
    def test_acceptance_positive_and_negative(self):
        good = research.exact_checks(fixture())
        bad = research.exact_checks(fixture('02-fail-kl-four-qubit'))
        self.assertTrue(good['passed'])
        self.assertEqual(good['logical_residues'], [0, 2])
        self.assertEqual(good['pauli_count'], 13)
        self.assertEqual(sum(row['passed'] for row in bad['kl']), 9)
        self.assertTrue(bad['normalization_and_orthogonality'])
        self.assertTrue(bad['support_matches_gate'])
        self.assertEqual(bad['kernel_status'], 'not_run')

    def test_changed_gate_does_not_change_kl(self):
        data = fixture()
        data['angles'][0] = 2
        result = research.exact_checks(data)
        self.assertTrue(all(row['passed'] for row in result['kl']))
        self.assertFalse(result['support_matches_gate'])
        self.assertFalse(result['passed'])

    def test_invalid_and_forged_inputs_rejected(self):
        for change in [lambda x: x.update(n=7), lambda x: x.update(k=0),
                       lambda x: x.update(denominator=0), lambda x: x.update(q=True),
                       lambda x: x.update(kernel_status='passed'),
                       lambda x: x['words'][0].append(copy.deepcopy(x['words'][0][0])),
                       lambda x: x['words'][0][0]['coordinates'].__setitem__(0, 1.0),
                       lambda x: x['words'][0][0].update(bits='bad injection')]:
            data = fixture()
            change(data)
            with self.assertRaises(ValueError):
                research.lean_certificate(data)

    def test_arbitrary_complex_amplitudes_match_independent_pauli_oracle(self):
        rng = random.Random(301)
        data = {'schema': research.SCHEMA, 'n': 3, 'k': 4, 'distance': 3,
                'denominator': 17, 'q': 7, 'angles': [1, 2, 4], 'words': []}
        for _ in range(4):
            data['words'].append([{'bits': ''.join(str(m >> i & 1) for i in range(3)),
                                   'coordinates': [rng.randrange(-2, 3) for _ in range(8)]} for m in range(8)])
        basis = [1, math.sqrt(2), math.sqrt(3), math.sqrt(6), 1j, 1j*math.sqrt(2), 1j*math.sqrt(3), 1j*math.sqrt(6)]
        value = lambda a: sum(c * b for c, b in zip(a, basis))
        vectors = [[value(row['coordinates']) / math.sqrt(17) for row in word] for word in data['words']]
        result = research.exact_checks(data)
        self.assertEqual(result['pauli_count'], 37)
        for row in result['kl']:
            x, z = row['x_mask'], row['z_mask']
            for j in range(4):
                for k in range(4):
                    expected = sum(vectors[j][s ^ x].conjugate() * vectors[k][s]
                                   * (-1)**((z & s).bit_count()) * 1j**((x & z).bit_count()) for s in range(8))
                    self.assertAlmostEqual(abs(value(row['matrix_coordinates'][j][k]) / 17 - expected), 0, places=11)

    def test_all_k_gram_entries_checked_and_rank_one_scope_kept_separate(self):
        data = fixture()
        data.update(k=3, distance=1)
        data['words'].append(copy.deepcopy(data['words'][0]))
        self.assertFalse(research.exact_checks(data)['normalization_and_orthogonality'])
        rank_one = fixture()
        rank_one.update(k=1)
        rank_one['words'] = rank_one['words'][:1]
        self.assertTrue(research.exact_checks(rank_one)['passed'])
        self.assertIn('rank-one', research.SCOPE)

    def test_generic_certificate_has_no_canonical_equality_and_input_changes_source(self):
        data = fixture()
        first = research.lean_certificate(data)
        data['words'][0][0]['coordinates'][0] = -1
        self.assertNotEqual(first, research.lean_certificate(data))
        self.assertNotIn('SixQubit', first)
        self.assertNotIn('native_decide', first)
        self.assertNotIn('sorry', first)
        self.assertIn('gram_check', first)
        self.assertIn('finite_kl', first)

    def test_new_schema_direct_jobs_and_existing_model_boundary(self):
        default, providers = load_config(ROOT / 'tools/explorer/models.example.json')
        for kind in ['exact', 'lean', 'agent']:
            request = validate_request({'kind': kind, 'input': fixture(), **({'question': 'check'} if kind == 'agent' else {})}, default, providers)
            self.assertEqual(request['input'], fixture())


class ResearchBundle(Workspace):
    def test_generic_assistant_preserves_input_and_adapts_tool_bounds(self):
        data = fixture()
        session = ToolSession(data, self.root)
        case = session.execute('get_case', {})
        self.assertEqual((case['n'], case['k'], case['squared_amplitude_denominator']), (4, 2, 2))
        schema = next(t['function']['parameters'] for t in session.tools() if t['function']['name'] == 'make_candidate')
        self.assertEqual(schema['properties']['angles']['maxItems'], 4)
        self.assertEqual(schema['properties']['angles']['items']['maximum'], 3)
        session.execute('make_candidate', {'phase_changes': [{'word': 0, 'bits': '0000', 'quarter_turns': 2}]})
        expected = copy.deepcopy(data)
        expected['words'][0][0]['coordinates'][0] = -1
        self.assertEqual(session.candidate, expected)
        self.assertEqual(session.current, data)
        # A sign flip need not break a different code: this code still detects weight-one errors.
        result = session.execute('check_exact', {'target': 'candidate'})
        self.assertTrue(result['kl_passed'])
        self.assertEqual(result['pauli_count'], 13)
        self.assertFalse(session.execute('inspect_pauli', {'target': 'candidate'})['found'])
        with self.assertRaises(ValueError):
            session.execute('inspect_pauli', {'target': 'current', 'x_mask': 16, 'z_mask': 0})
        self.assertIn('divided by 2', session.execute('get_reference', {'reference': 'kl'})['text'])

    def test_generic_assistant_can_address_more_than_two_logical_words(self):
        data = {'schema': research.SCHEMA, 'n': 2, 'k': 3, 'distance': 1,
                'denominator': 1, 'q': 11, 'angles': [0, 0], 'words': [
                    [{'bits': bits, 'coordinates': [1, 0, 0, 0, 0, 0, 0, 0]}] for bits in ['00', '01', '10']]}
        session = ToolSession(data, self.root)
        session.execute('make_candidate', {'angles': [10, 9], 'phase_changes': [{'word': 2, 'bits': '10', 'quarter_turns': 1}]})
        self.assertEqual(session.candidate['words'][2][0]['coordinates'], [0, 0, 0, 0, 1, 0, 0, 0])
        self.assertTrue(session.execute('check_exact', {'target': 'candidate'})['passed_requested_checks'])

    def test_generic_bundle_is_self_contained_and_detects_tampering(self):
        run, bundle = self.root / 'run', self.root / 'bundle'
        evidence = sslp_explorer.verify_case(fixture(), run)
        self.assertEqual(evidence['kernel']['status'], 'not_run')
        sslp_explorer.export_bundle(run, bundle)
        self.assertTrue(sslp_explorer.check_bundle(bundle)['hashes_match'])
        self.assertTrue((bundle / 'SS/ExactCode.lean').is_file())
        self.assertFalse((bundle / 'SixQubit/Orbit36Code.lean').exists())
        path = bundle / 'case.json'
        data = json.loads(path.read_text())
        data['words'][0][0]['coordinates'][0] = 2
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'hash mismatch'):
            sslp_explorer.check_bundle(bundle)

    def test_negative_example_cannot_export_as_success(self):
        run = self.root / 'run'
        report = sslp_explorer.verify_case(fixture('02-fail-kl-four-qubit'), run)
        self.assertFalse(report['passed_requested_checks'])
        with self.assertRaisesRegex(ValueError, 'failed run'):
            sslp_explorer.export_bundle(run, self.root / 'bundle')


if __name__ == '__main__':
    unittest.main()
