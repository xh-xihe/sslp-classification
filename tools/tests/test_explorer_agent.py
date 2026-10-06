"""Model/verification boundaries, protocol adapters and bounded tool execution."""
import copy
import io
import json
from pathlib import Path
import shutil
import sys
import unittest
from unittest.mock import patch
from urllib.error import HTTPError, URLError
import uuid

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from explorer import class36
from explorer.agent import ToolSession, run_agent
from explorer.providers import (ModelClient, Provider, ProviderError, load_config,
                                normalize_message, request_json, strict_json)


LOCAL = Provider('local-test', 'ollama', 'test-model', 'open_weights', 'http://127.0.0.1:11434')


def call(name, args, identifier='call_test'):
    return {'id': identifier, 'type': 'function',
            'function': {'name': name, 'arguments': json.dumps(args)}}


class ScriptedClient:
    provider = LOCAL
    def __init__(self, messages):
        self.messages = iter(messages)
        self.requests = []
    def probe(self):
        return {'status': 'available', 'observed_revision': 'test-fixture'}
    def complete(self, messages, tools):
        self.requests.append(copy.deepcopy(messages))
        return {'message': next(self.messages), 'finish_reason': 'stop', 'usage': {}, 'seconds': 0}


class Workspace(unittest.TestCase):
    def setUp(self):
        self.path = TOOLS.parent / 'tmp' / 'agent-tests' / uuid.uuid4().hex
        self.path.mkdir(parents=True)
        self.addCleanup(self.cleanup)
    def cleanup(self):
        if self.path.resolve().is_relative_to((TOOLS.parent / 'tmp/agent-tests').resolve()):
            shutil.rmtree(self.path)


class ConfigurationTests(Workspace):
    def config(self, mutate=None):
        data = json.loads((TOOLS / 'explorer/models.example.json').read_text(encoding='utf-8'))
        if mutate:
            mutate(data)
        path = self.path / 'models.json'
        path.write_text(json.dumps(data), encoding='utf-8')
        return path

    def test_open_default_and_disabled_closed_option(self):
        default, models = load_config(self.config())
        self.assertEqual(models[default].model_class, 'open_weights')
        with self.assertRaisesRegex(ProviderError, 'disabled'):
            ModelClient(models['closed-compatible'])

    def test_closed_requires_explicit_selection(self):
        def change(data):
            data['providers'][2]['enabled'] = True
            data['default_provider'] = 'closed-compatible'
        with self.assertRaisesRegex(ProviderError, 'default provider must be an open'):
            load_config(self.config(change))

    def test_reject_bad_urls_plaintext_keys_and_unbounded_settings(self):
        changes = [{'base_url': 'http://remote.example/v1'}, {'base_url': 'https://user:secret@example.com'},
                   {'base_url': 'https://example.com?api_key=secret'}, {'base_url': 'http://[bad'},
                   {'base_url': 'http://localhost:bad'}, {'api_key': 'literal-secret'},
                   {'max_output_tokens': True}, {'timeout_seconds': 99999}]
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ProviderError):
                load_config(self.config(lambda d: d['providers'][0].update(change)))

    def test_json_rejects_duplicate_keys_and_nonfinite_numbers(self):
        for text in ('{"status":false,"status":true}', '{"x":NaN}', '[Infinity]'):
            with self.assertRaises(ProviderError):
                strict_json(text)


class AdapterTests(unittest.TestCase):
    def test_ollama_tool_replay_and_revision_probe(self):
        requests = []
        def transport(p, route, payload=None):
            requests.append((route, payload))
            if route == '/api/version':
                return {'version': 'fixture'}
            if route == '/api/tags':
                return {'models': [{'name': 'test-model', 'digest': 'abc'}]}
            return {'done': True, 'done_reason': 'stop', 'model': p.model,
                    'message': {'role': 'assistant', 'content': '', 'tool_calls': [
                        {'function': {'name': 'check_exact', 'arguments': {'target': 'current'}}}]}}
        client = ModelClient(LOCAL, transport)
        self.assertEqual(client.probe()['observed_revision'], 'abc')
        response = client.complete([{'role': 'assistant', 'content': '', 'tool_calls': [call('get_case', {})]},
                                    {'role': 'tool', 'name': 'get_case', 'tool_call_id': 'call_test', 'content': '{}'}], [])
        payload = requests[-1][1]
        self.assertEqual(payload['messages'][0]['tool_calls'][0]['function']['arguments'], {})
        self.assertEqual(payload['messages'][1]['tool_name'], 'get_case')
        self.assertFalse(payload['think'])
        self.assertEqual(json.loads(response['message']['tool_calls'][0]['function']['arguments']), {'target': 'current'})

    def test_compatible_adapter_preserves_call_ids_and_usage(self):
        requests = []
        provider = Provider('closed-test', 'chat_completions', 'fixture-closed', 'closed', 'https://example.invalid/v1')
        def transport(p, route, payload=None):
            requests.append((route, payload))
            return {'model': p.model, 'choices': [{'finish_reason': 'tool_calls', 'message': {
                'role': 'assistant', 'content': None, 'tool_calls': [call('check_exact', {'target': 'current'}, 'vendor_42')]}}],
                'usage': {'prompt_tokens': 12, 'completion_tokens': 8}}
        message = {'role': 'tool', 'name': 'get_case', 'tool_call_id': 'vendor_41', 'content': '{}'}
        result = ModelClient(provider, transport).complete([message], [])
        self.assertEqual(requests[0][0], '/chat/completions')
        self.assertEqual(requests[0][1]['messages'][0]['tool_call_id'], 'vendor_41')
        self.assertNotIn('think', requests[0][1])
        self.assertEqual(result['message']['tool_calls'][0]['id'], 'vendor_42')
        self.assertEqual(result['usage'], {'input_tokens': 12, 'output_tokens': 8})

    def test_truncated_response_never_yields_a_tool_call(self):
        response = {'done': True, 'done_reason': 'length', 'message': {
            'role': 'assistant', 'content': '', 'tool_calls': [{'function': {'name': 'check_lean', 'arguments': {'target': 'current'}}}]}}
        with self.assertRaisesRegex(ProviderError, 'truncated'):
            ModelClient(LOCAL, lambda *args: response).complete([], [])

    def test_protocol_rejects_forged_or_duplicate_tool_arguments(self):
        bad = {'role': 'assistant', 'tool_calls': [call('check_exact', {})]}
        bad['tool_calls'][0]['function']['arguments'] = '{"target":"current","target":"candidate"}'
        with self.assertRaises(ProviderError):
            normalize_message(bad, 'chat_completions')
        with self.assertRaises(ProviderError):
            normalize_message({'role': 'assistant', 'tool_calls': [call('get_case', {}), call('get_case', {})]}, 'chat_completions')

    def test_transport_does_not_echo_secret_error_body_or_follow_redirect(self):
        secret = b'private-key-and-provider-debug-data'
        for code in (302, 401, 500):
            with patch('explorer.providers.build_opener') as opener:
                opener.return_value.open.side_effect = HTTPError('https://example.invalid', code, 'error', {}, io.BytesIO(secret))
                with self.assertRaises(ProviderError) as caught:
                    request_json(LOCAL, '/api/chat', {})
                self.assertNotIn(secret.decode(), str(caught.exception))
                self.assertIn('no fallback', str(caught.exception))
                self.assertEqual(opener.return_value.open.call_count, 1)

    def test_timeout_explains_per_request_limit_without_retry(self):
        for failure in (TimeoutError('private detail'), URLError(TimeoutError('private detail'))):
            with self.subTest(failure=type(failure).__name__), patch('explorer.providers.build_opener') as opener:
                opener.return_value.open.side_effect = failure
                with self.assertRaises(ProviderError) as caught:
                    request_json(LOCAL, '/api/chat', {})
                message = str(caught.exception)
                self.assertIn('120 seconds for one request', message)
                self.assertIn('other Ollama requests finish', message)
                self.assertIn('no fallback attempted', message)
                self.assertNotIn('private detail', message)
                self.assertEqual(opener.return_value.open.call_count, 1)


class ToolBoundaryTests(Workspace):
    def setUp(self):
        super().setUp()
        self.data = class36.example()
        self.session = ToolSession(self.data, self.path)

    def test_real_sign_change_fails_kl_and_preserves_original_input(self):
        before = class36.digest(self.data)
        original = self.session.execute('check_exact', {'target': 'current'})
        candidate = self.session.execute('make_candidate', {'angles': self.data['gate']['angles'], 'phase_changes': [
            {'word': 0, 'bits': '000000', 'quarter_turns': 2}]})
        result = self.session.execute('check_exact', {'target': 'candidate'})
        self.assertTrue(original['kl_passed'])
        self.assertFalse(result['kl_passed'])
        self.assertTrue(result['normalization_and_orthogonality'])
        self.assertEqual(result['pauli_count'], 154)
        self.assertEqual(result['input_sha256'], candidate['input_sha256'])
        self.assertEqual(class36.digest(self.session.current), before)
        self.assertEqual(result['kernel_status'], 'not_run')
        failed = result['first_failure']
        row = self.session.execute('inspect_pauli', {'target': 'candidate', 'x_mask': failed['x_mask'], 'z_mask': failed['z_mask']})
        self.assertEqual(row['matrix_coordinates'], failed['matrix_coordinates'])

    def test_changed_gate_does_not_imply_failed_kl(self):
        self.session.execute('make_candidate', {'angles': [1, 1, 1, 1, 1, 3], 'phase_changes': []})
        result = self.session.execute('check_exact', {'target': 'candidate'})
        self.assertTrue(result['kl_passed'])
        self.assertFalse(result['gate_support_matches_requested_residues'])
        self.assertFalse(result['passed_requested_checks'])

    def test_negation_preserves_gate_and_every_other_amplitude(self):
        # A requested logical residue is part of the input, even when mismatched.
        self.session.current['gate']['logical_residues'] = [2, 3]
        original = copy.deepcopy(self.session.current)
        self.session.execute('make_candidate', {'phase_changes': [
            {'word': 0, 'bits': '000000', 'quarter_turns': 2}]})
        candidate = copy.deepcopy(self.session.candidate)
        changed = next(row for row in candidate['words'][0] if row['bits'] == '000000')
        changed['coordinates'] = [-x for x in changed['coordinates']]
        candidate['id'] = original['id']
        self.assertEqual(candidate, original)
        self.assertEqual(self.session.current, original)
        result = self.session.execute('check_exact', {'target': 'candidate'})
        self.assertTrue(result['normalization_and_orthogonality'])
        self.assertEqual(result['failed_pauli_count'], 18)
        row = self.session.execute('inspect_pauli', {'target': 'candidate'})
        self.assertTrue(row['found'])
        self.assertEqual((row['x_mask'], row['z_mask']), (33, 0))
        self.assertEqual(tuple(row['matrix_coordinates'][0][1]), (24, 0, 0, 0, 0, 0, 0, 0))
        self.assertEqual(row['matrix_denominator'], 120)
        self.assertEqual(row['matrix_exact'], [['0', '1/5'], ['1/5', '0']])
        self.assertEqual(row['kl_violations'], ['nonzero off-diagonal entries'])

    def test_first_failure_selection_does_not_invent_a_failure_or_accept_half_mask(self):
        row = self.session.execute('inspect_pauli', {'target': 'current'})
        self.assertFalse(row['found'])
        self.assertNotIn('matrix_coordinates', row)
        for field in ('x_mask', 'z_mask'):
            with self.assertRaises(ValueError):
                self.session.execute('inspect_pauli', {'target': 'current', field: 0})

    def test_failed_model_attempt_is_recorded_and_actual_checks_survive(self):
        client = ScriptedClient([])
        response = {'message': {'role': 'assistant', 'content': '', 'tool_calls': [
            call('check_exact', {'target': 'current'})]}, 'seconds': 0}
        with patch.object(client, 'complete', side_effect=[response, ProviderError('provider timed out')]):
            report, _ = run_agent(client, self.data, 'check', self.path)
        self.assertEqual(report['status'], 'provider_error')
        self.assertEqual([x['status'] for x in report['model_invocations']], ['completed', 'failed'])
        self.assertEqual(report['model_invocations'][-1]['round'], 2)
        self.assertEqual(len(report['verification']), 1)
        self.assertTrue(report['verification'][0]['exact']['kl_passed'])
        self.assertEqual(report['verification'][0]['kernel']['status'], 'not_run')
        self.assertIn('1 completed verification record(s) retained', report['error'])
        with patch.object(client, 'complete', side_effect=ProviderError('provider timed out')):
            failed, _ = run_agent(client, self.data, 'check', self.path)
        self.assertEqual(failed['verification'], [])
        self.assertEqual(failed['model_invocations'][0]['round'], 1)
        self.assertEqual(failed['model_invocations'][0]['status'], 'failed')
        self.assertIn('No verification records', failed['error'])

    def test_missing_explanation_citations_get_one_bounded_repair(self):
        check = {'role': 'assistant', 'content': '', 'tool_calls': [call('check_exact', {'target': 'current'})]}
        for final_text, expected_citations in [('Lean not run. Passed [tool:t1].', 'present'),
                                                ('Still no citations.', 'missing')]:
            client = ScriptedClient([check, {'role': 'assistant', 'content': 'Passed.'},
                                     {'role': 'assistant', 'content': final_text}])
            report, _ = run_agent(client, self.data, 'check', self.path)
            self.assertEqual(len(report['tools']), 1)
            self.assertEqual(len(report['model_invocations']), 3)
            self.assertEqual(len(report['explanation_feedback']), 1)
            self.assertEqual(report['answer']['text'], final_text)
            self.assertEqual(report['answer']['citations']['status'], expected_citations)
            self.assertIn('Successful records: t1', client.requests[2][-1]['content'])
        limited = ScriptedClient([check, {'role': 'assistant', 'content': 'Passed.'}])
        report, _ = run_agent(limited, self.data, 'check', self.path, max_rounds=2)
        self.assertEqual(report['explanation_feedback'], [])
        self.assertEqual(report['answer']['citations']['status'], 'missing')

    def test_unknown_tools_paths_status_fields_and_invalid_masks_rejected(self):
        cases = [('shell', {'command': 'anything'}), ('get_case', {'path': '../private'}),
                 ('check_exact', {'target': 'current', 'kernel_status': 'passed'}),
                 ('inspect_pauli', {'target': 'current', 'x_mask': 7, 'z_mask': 0}),
                 ('inspect_pauli', {'target': 'current', 'x_mask': True, 'z_mask': 0}),
                 ('check_lean', {'target': 'current'})]
        for name, args in cases:
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.session.execute(name, args)
        self.assertEqual(self.session.kernel, {})

    def test_rejected_candidate_is_atomic(self):
        change = {'word': 0, 'bits': '000000', 'quarter_turns': 2}
        with self.assertRaises(ValueError):
            self.session.execute('make_candidate', {'angles': [1, 1, 1, 1, 2, 3], 'phase_changes': [change, change]})
        self.assertIsNone(self.session.candidate)
        self.assertEqual(self.session.current, self.data)

    def test_model_claim_cannot_create_evidence(self):
        client = ScriptedClient([{'role': 'assistant', 'content': '{"kernel_status":"passed","full_manuscript_certified":true}'}])
        report, _ = run_agent(client, self.data, 'verify', self.path)
        self.assertEqual(report['answer']['kind'], 'untrusted_model_explanation')
        self.assertEqual(report['verification'], [])
        self.assertFalse(report['full_manuscript_certified'])

    def test_tool_budget_stops_batch_before_execution(self):
        client = ScriptedClient([{'role': 'assistant', 'content': '', 'tool_calls': [
            call('check_exact', {'target': 'current'}, 'a'), call('check_exact', {'target': 'current'}, 'b')]}])
        report, session = run_agent(client, self.data, 'verify', self.path, max_tools=1)
        self.assertEqual(report['status'], 'budget_exhausted')
        self.assertEqual(report['tools'], [])
        self.assertEqual(session.exact, {})

    def test_tool_errors_return_to_model_without_fabricating_results(self):
        client = ScriptedClient([{'role': 'assistant', 'content': '', 'tool_calls': [call('shell', {})]},
                                 {'role': 'assistant', 'content': '该工具不可用。'}])
        report, _ = run_agent(client, self.data, 'run shell', self.path)
        self.assertFalse(report['tools'][0]['output']['ok'])
        self.assertEqual(report['verification'], [])
        self.assertEqual(client.requests[1][-1]['role'], 'tool')

    def test_kernel_status_comes_from_executor_and_single_job_budget(self):
        session = ToolSession(self.data, self.path, allow_lean=True)
        actual = {'input_sha256': class36.digest(self.data), 'kernel': {'status': 'failed'}, 'passed_requested_checks': False}
        with patch('sslp_explorer.verify_case', return_value=actual) as verify:
            result = session.execute('check_lean', {'target': 'current'})
            self.assertEqual(result['kernel']['status'], 'failed')
            self.assertEqual(verify.call_args.kwargs['lean'], True)
            with self.assertRaisesRegex(ValueError, 'budget exhausted'):
                session.execute('check_lean', {'target': 'current'})
            self.assertEqual(verify.call_count, 1)


if __name__ == '__main__':
    unittest.main()
