"""Real loopback/worker boundaries; test model never needs Ollama or network access."""
import http.client
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import time
import unittest
import uuid

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from explorer import class36
from explorer.agent import audit_citations
from explorer.jobs import JobManager, TERMINAL, QueueFull, write_json
from explorer.process_control import ProcessTree
from sslp_service import LocalServer, SITE


def wait_for(predicate, timeout=15):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        result = predicate()
        if result:
            return result
        time.sleep(.05)
    raise AssertionError('timed out waiting for test condition')


class Workspace(unittest.TestCase):
    def setUp(self):
        self.base = (TOOLS.parent / 'tmp/job-tests').resolve()
        self.path = self.base / uuid.uuid4().hex
        self.path.mkdir(parents=True)
        self.addCleanup(self.cleanup)

    def cleanup(self):
        assert self.path.resolve().is_relative_to(self.base)
        shutil.rmtree(self.path)

    def manager(self, **kwargs):
        manager = JobManager(self.path / 'jobs', TOOLS / 'explorer/models.example.json', **kwargs)
        self.addCleanup(manager.close)
        return manager


class CitationTests(unittest.TestCase):
    def test_missing_failed_and_unknown_references_are_not_valid(self):
        trace = [{'id': 't1', 'output': {'ok': True}}, {'id': 't2', 'output': {'ok': False}}]
        for text, status in [('result', 'missing'), ('[tool:t1]', 'present'),
                             ('[tool:t2]', 'invalid'), ('[tool:t99]', 'invalid'),
                             ('[tool:t1] [tool:t2]', 'invalid')]:
            self.assertEqual(audit_citations(text, trace)['status'], status)
        self.assertEqual(audit_citations('no tools', [])['status'], 'not_applicable')


class HTTPTests(Workspace):
    def setUp(self):
        super().setUp()
        self.jobs = self.manager()
        self.server = LocalServer(('127.0.0.1', 0), self.jobs)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.addCleanup(self.stop_server)

    def stop_server(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(5)

    def request(self, method, path, body=None, *, authenticated=True, extra=None):
        headers = {'Origin': SITE}
        if authenticated:
            headers['Authorization'] = 'Bearer ' + self.server.token
        if body is not None:
            headers['Content-Type'] = 'application/json'
            body = json.dumps(body)
        headers.update(extra or {})
        connection = http.client.HTTPConnection('127.0.0.1', self.server.server_port, timeout=5)
        try:
            connection.request(method, path, body, headers)
            response = connection.getresponse()
            return response.status, dict(response.headers), response.read()
        finally:
            connection.close()

    def test_pairing_is_not_cors_readable_and_status_requires_auth(self):
        code, headers, body = self.request('GET', '/connect', authenticated=False)
        self.assertEqual(code, 200)
        self.assertIn(self.server.token.encode(), body)
        self.assertNotIn('Access-Control-Allow-Origin', headers)
        self.assertEqual(headers['Cache-Control'], 'no-store')
        self.assertEqual(self.request('GET', '/v1/status', authenticated=False)[0], 401)
        self.assertEqual(self.request('GET', '/v1/status')[0], 200)

    def test_wrong_origin_host_and_unknown_path_rejected(self):
        self.assertEqual(self.request('GET', '/v1/status', extra={'Origin': 'https://untrusted.invalid'})[0], 403)
        self.assertEqual(self.request('GET', '/v1/status', extra={'Host': 'untrusted.invalid'})[0], 403)
        self.assertEqual(self.request('GET', '/v1/jobs/' + 'a'*32 + '/artifacts/../../models.json')[0], 404)
        self.assertEqual(self.request('GET', '/v1/status?token=x')[0], 400)

    def test_preflight_only_allows_expected_origin_headers_and_method(self):
        headers = {'Access-Control-Request-Method': 'POST', 'Access-Control-Request-Headers': 'authorization,content-type'}
        code, result, _ = self.request('OPTIONS', '/v1/jobs', authenticated=False, extra=headers)
        self.assertEqual(code, 204)
        self.assertEqual(result['Access-Control-Allow-Origin'], SITE)
        headers['Access-Control-Request-Headers'] = 'x-other'
        self.assertEqual(self.request('OPTIONS', '/v1/jobs', authenticated=False, extra=headers)[0], 403)

    def test_job_input_fields_size_and_disabled_model_rejected(self):
        valid = {'kind': 'exact', 'input': class36.example()}
        for patch in ({'script': 'x'}, {'kind': 'shell'}, {'input': {}}, {'provider': 'closed-compatible'}):
            self.assertEqual(self.request('POST', '/v1/jobs', {**valid, **patch})[0], 400)
        self.assertEqual(self.request('POST', '/v1/jobs', {}, extra={'Content-Length': '2000001'})[0], 413)

    def test_real_exact_worker_result_and_artifact_remain_bound_to_input(self):
        data = class36.example()
        code, _, raw = self.request('POST', '/v1/jobs', {'kind': 'exact', 'input': data})
        self.assertEqual(code, 202)
        job = json.loads(raw)
        identifier = job['id']
        done = wait_for(lambda: (j if (j := self.jobs.get(identifier))['state'] in TERMINAL else None))
        self.assertEqual(done['state'], 'completed', (self.path/'jobs'/identifier/'worker.log').read_text())
        code, _, raw = self.request('GET', '/v1/jobs/' + identifier + '/result')
        result = json.loads(raw)
        self.assertEqual(code, 200)
        self.assertEqual(result['input_sha256'], class36.digest(data))
        self.assertTrue(result['verification'][0]['exact']['kl_passed'])
        self.assertEqual(result['verification'][0]['kernel']['status'], 'not_run')
        self.assertEqual(self.request('GET', '/v1/jobs/' + identifier + '/artifacts/report.json')[2], raw)
        self.assertEqual(self.request('GET', '/v1/jobs/' + identifier + '/artifacts/worker.log')[0], 404)

    def test_research_input_reaches_real_worker_with_own_digest(self):
        data = json.loads((TOOLS.parent / 'artifacts/workbench-acceptance-20260929/01-pass-four-qubit.json').read_text())
        code, _, raw = self.request('POST', '/v1/jobs', {'kind': 'exact', 'input': data})
        self.assertEqual(code, 202)
        identifier = json.loads(raw)['id']
        done = wait_for(lambda: (j if (j := self.jobs.get(identifier))['state'] in TERMINAL else None))
        self.assertEqual(done['state'], 'completed', (self.path/'jobs'/identifier/'worker.log').read_text())
        result = json.loads(self.request('GET', '/v1/jobs/' + identifier + '/result')[2])
        self.assertEqual(result['input_sha256'], class36.digest(data))
        self.assertEqual(result['verification'][0]['exact']['pauli_count'], 13)
        self.assertTrue(result['verification'][0]['exact']['kl_passed'])
        self.assertEqual(result['verification'][0]['kernel']['status'], 'not_run')


class SlowModel(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass
    def do_GET(self):
        self.server.entered.set()
        self.server.release.wait(10)
        try:
            self.send_response(503)
            self.end_headers()
        except ConnectionError:
            pass  # A cancelled/expired worker closes its outstanding request.


class QueueTests(Workspace):
    def slow_manager(self, **kwargs):
        server = ThreadingHTTPServer(('127.0.0.1', 0), SlowModel)
        server.daemon_threads = True
        server.entered, server.release = threading.Event(), threading.Event()
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        def close():
            server.release.set()
            server.shutdown()
            server.server_close()
            thread.join(5)
        self.addCleanup(close)
        config = json.loads((TOOLS / 'explorer/models.example.json').read_text())
        config['providers'][0]['base_url'] = f'http://127.0.0.1:{server.server_port}'
        path = self.path/'models.json'
        write_json(path, config)
        manager = JobManager(self.path/'jobs', path, **kwargs)
        self.addCleanup(manager.close)
        return manager, server

    def test_cancel_running_and_queued_then_continue_with_real_work(self):
        manager, server = self.slow_manager(max_pending=2)
        active = manager.submit({'kind': 'agent', 'input': class36.example(), 'question': 'test'})
        self.assertTrue(server.entered.wait(10))
        queued = manager.submit({'kind': 'exact', 'input': class36.example()})
        with self.assertRaises(QueueFull):
            manager.submit({'kind': 'exact', 'input': class36.example()})
        self.assertEqual(manager.cancel(queued['id'])['state'], 'cancelled')
        manager.cancel(active['id'])
        wait_for(lambda: manager.get(active['id'])['state'] == 'cancelled')
        with self.assertRaises(KeyError):
            manager.artifact(active['id'], 'report.json')
        fresh = manager.submit({'kind': 'exact', 'input': class36.example()})
        wait_for(lambda: manager.get(fresh['id'])['state'] == 'completed')

    def test_total_timeout_kills_worker_waiting_on_model(self):
        manager, server = self.slow_manager(timeout=1)
        job = manager.submit({'kind': 'agent', 'input': class36.example(), 'question': 'test'})
        self.assertTrue(server.entered.wait(10))
        wait_for(lambda: manager.get(job['id'])['state'] == 'timeout')
        with self.assertRaises(KeyError):
            manager.artifact(job['id'], 'report.json')

    def test_restart_marks_incomplete_job_interrupted_and_preserves_completed(self):
        directory = self.path/'jobs'
        identifier = uuid.uuid4().hex
        (directory/identifier).mkdir(parents=True)
        write_json(directory/identifier/'job.json', {'id': identifier, 'state': 'running', 'created_at': 0})
        completed = uuid.uuid4().hex
        (directory/completed).mkdir(parents=True)
        write_json(directory/completed/'job.json', {'id': completed, 'state': 'completed', 'created_at': 0})
        manager = self.manager()
        self.assertEqual(manager.get(identifier)['state'], 'interrupted')
        self.assertEqual(manager.get(completed)['state'], 'completed')
        with self.assertRaisesRegex(ValueError, 'another service'):
            JobManager(directory, TOOLS/'explorer/models.example.json')


@unittest.skipUnless(os.name == 'nt', 'Windows Job Object limits')
class ProcessTests(Workspace):
    def launch(self, script, memory=128):
        process = subprocess.Popen([sys.executable, '-c', script], stdin=subprocess.PIPE,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        def cleanup():
            if process.poll() is None:
                process.kill()
            process.wait(5)
            if process.stdin and not process.stdin.closed:
                process.stdin.close()
        self.addCleanup(cleanup)
        tree = ProcessTree(process, memory)
        self.addCleanup(tree.close)
        process.stdin.write(b'GO\n')
        process.stdin.close()
        return process, tree

    def test_memory_limit_is_enforced(self):
        script = 'import sys; sys.stdin.readline()\ntry: x=bytearray(256*1024*1024)\nexcept MemoryError: sys.exit(42)\nsys.exit(1)'
        process, _ = self.launch(script)
        self.assertEqual(process.wait(10), 42)

    def test_terminate_kills_descendant_and_root(self):
        child_file = self.path/'child.pid'
        script = ('import sys,subprocess,time;from pathlib import Path;sys.stdin.readline();'
                  'child=subprocess.Popen([sys.executable,"-c","import time;time.sleep(60)"]);'
                  f'Path({str(child_file)!r}).write_text(str(child.pid));time.sleep(60)')
        process, tree = self.launch(script)
        wait_for(lambda: child_file.exists() and child_file.read_text())
        import ctypes
        from ctypes import wintypes
        api = ctypes.WinDLL('kernel32', use_last_error=True)
        api.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        api.OpenProcess.restype = wintypes.HANDLE
        api.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        api.CloseHandle.argtypes = [wintypes.HANDLE]
        handle = api.OpenProcess(0x100000, False, int(child_file.read_text()))
        self.assertTrue(handle)
        try:
            tree.terminate()
            self.assertNotEqual(process.wait(5), 0)
            self.assertEqual(api.WaitForSingleObject(handle, 5000), 0)
        finally:
            api.CloseHandle(handle)


if __name__ == '__main__':
    unittest.main()
