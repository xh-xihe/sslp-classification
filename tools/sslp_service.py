#!/usr/bin/env python3
"""Loopback-only SSLP job service; pair through /connect, never expose tokens in logs."""
import argparse
import hmac
import html
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import re
import secrets
import threading
from urllib.parse import urlsplit

from explorer.jobs import JobManager, QueueFull
from explorer.providers import strict_json

ROOT = Path(__file__).resolve().parent.parent
SITE = 'https://sslp-explorer-class36.xh-xihe.chatgpt.site'
ORIGINS = {SITE, 'http://localhost:5173', 'http://127.0.0.1:5173'}


class LocalServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = False

    def __init__(self, address, manager, *, token=None, site=SITE):
        if address[0] != '127.0.0.1':
            raise ValueError('this companion service only binds to IPv4 loopback')
        if site not in ORIGINS:
            raise ValueError('connection page must target a known workbench origin')
        self.manager, self.token, self.site = manager, token or secrets.token_urlsafe(32), site
        self.slots = threading.BoundedSemaphore(12)
        super().__init__(address, Handler)

    def process_request(self, request, client_address):
        if not self.slots.acquire(blocking=False):
            self.shutdown_request(request)
            return
        try:
            super().process_request(request, client_address)
        except BaseException:
            self.slots.release()
            raise

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            self.slots.release()


class Handler(BaseHTTPRequestHandler):
    server_version = 'SSLPCompanion/1'

    def setup(self):
        super().setup()
        self.connection.settimeout(10)

    def log_message(self, format, *args):
        pass  # URLs, authorization and model text never go into HTTP access logs.

    def send(self, status, value, *, cors=True, content_type='application/json; charset=utf-8', filename=None):
        body = value if isinstance(value, bytes) else json.dumps(value, ensure_ascii=False, allow_nan=False).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Referrer-Policy', 'no-referrer')
        self.send_header('X-Frame-Options', 'DENY')
        self.send_header('Content-Security-Policy', "default-src 'none'; style-src 'unsafe-inline'; frame-ancestors 'none'; base-uri 'none'; form-action 'none'")
        origin = self.headers.get('Origin')
        if cors and origin in ORIGINS:
            self.send_header('Access-Control-Allow-Origin', origin)
            self.send_header('Vary', 'Origin')
        if filename:
            self.send_header('Content-Disposition', 'attachment; filename="' + filename + '"')
        self.end_headers()
        self.wfile.write(body)

    def allowed(self, auth=True):
        port = self.server.server_port
        if self.headers.get_all('Host') is None or len(self.headers.get_all('Host')) != 1 or self.headers['Host'] not in (f'127.0.0.1:{port}', f'localhost:{port}'):
            self.send(403, {'error': 'invalid_host'}, cors=False)
            return False
        if self.headers.get('Origin') and self.headers['Origin'] not in ORIGINS:
            self.send(403, {'error': 'origin_not_allowed'}, cors=False)
            return False
        authorization = self.headers.get('Authorization', '')
        if auth and (len(authorization) > 256 or not hmac.compare_digest(authorization.encode(), ('Bearer ' + self.server.token).encode())):
            self.send(401, {'error': 'connection_required'})
            return False
        return True

    def do_OPTIONS(self):
        if not self.allowed(auth=False):
            return
        if self.headers.get('Origin') not in ORIGINS or self.headers.get('Access-Control-Request-Method') not in ('GET', 'POST'):
            self.send(403, {'error': 'preflight_rejected'}, cors=False)
            return
        requested = {h.strip().lower() for h in self.headers.get('Access-Control-Request-Headers', '').split(',') if h.strip()}
        if requested - {'authorization', 'content-type'}:
            self.send(403, {'error': 'headers_not_allowed'})
            return
        self.send_response(204)
        self.send_header('Access-Control-Allow-Origin', self.headers['Origin'])
        self.send_header('Access-Control-Allow-Methods', 'GET, POST')
        self.send_header('Access-Control-Allow-Headers', 'Authorization, Content-Type')
        self.send_header('Access-Control-Allow-Private-Network', 'true')
        self.send_header('Vary', 'Origin')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', '0')
        self.end_headers()

    def do_GET(self):
        try:
            path = urlsplit(self.path)
            if path.query:
                self.send(400, {'error': 'query_parameters_not_supported'}, cors=False)
                return
            if path.path == '/health':
                if self.allowed(auth=False):
                    self.send(200, {'service': 'sslp-local-jobs', 'schema': 'sslp.job-api.v1'}, cors=False)
                return
            if path.path == '/connect':
                if not self.allowed(auth=False):
                    return
                target = self.server.site + '/#sslp_key=' + self.server.token + '&sslp_port=' + str(self.server.server_port)
                page = f'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Connect SSLP Workbench</title>
<style>body{{font:16px/1.8 system-ui,sans-serif;color:#252830;background:#fafbfc;max-width:580px;margin:12vh auto;padding:24px}}h1{{font-size:26px}}a{{display:inline-block;background:#285cc4;color:white;padding:10px 20px;border-radius:6px;text-decoration:none}}small{{display:block;color:#616975;margin-top:24px}}</style>
<h1>Local compute is ready</h1><p>Connect to submit research questions to Qwen, run exact checks, or execute Lean verification. Jobs use this computer.</p>
<a href="{html.escape(target, quote=True)}" rel="noreferrer">Connect SSLP Workbench →</a>
<p>Already editing a project? Copy the code below into the Assistant panel in your open workbench:</p>
<input aria-label="Connection code" readonly value="{self.server.token}" style="width:100%;padding:10px;box-sizing:border-box;border:1px solid #d8dee8;border-radius:5px;font:14px monospace">
<small>Allow local network access if your browser asks. The connection is kept only in the current page; return here to reconnect after a refresh.</small></html>'''
                self.send(200, page.encode('utf-8'), cors=False, content_type='text/html; charset=utf-8')
                return
            if not self.allowed():
                return
            manager = self.server.manager
            if path.path == '/v1/status':
                self.send(200, {'schema': 'sslp.job-api.v1', 'default_provider': manager.default,
                                'providers': [p.public() for p in manager.providers.values()], 'jobs': manager.recent(),
                                'capabilities': {'research_code_v1': {'exact': True, 'lean': True, 'assistant': True}},
                                'limits': {'concurrent': 1, 'pending': manager.max_pending,
                                           'wall_seconds': manager.timeout, 'worker_memory_mib': manager.memory_mib}})
                return
            match = re.fullmatch(r'/v1/jobs/([0-9a-f]{32})(?:/(result|artifacts/([A-Za-z0-9_.-]+)))?', path.path)
            if not match:
                self.send(404, {'error': 'not_found'})
                return
            identifier, operation, filename = match.groups()
            if not operation:
                self.send(200, manager.get(identifier))
                return
            file = manager.artifact(identifier, filename or 'report.json')
            if not file.is_file():
                raise KeyError('artifact unavailable')
            if file.stat().st_size > 64 * 1024 * 1024:
                raise ValueError('artifact exceeds limit')
            self.send(200, file.read_bytes(), content_type='application/json; charset=utf-8' if operation == 'result' else 'application/octet-stream', filename=filename)
        except KeyError:
            self.send(404, {'error': 'job_or_artifact_unavailable'})
        except (ValueError, OSError):
            self.send(400, {'error': 'invalid_request'})

    def do_POST(self):
        try:
            if not self.allowed():
                return
            if self.headers.get('Content-Type', '').split(';')[0] != 'application/json' or self.headers.get('Transfer-Encoding'):
                raise ValueError('JSON content type and content length required')
            lengths = self.headers.get_all('Content-Length') or []
            if len(lengths) != 1 or not re.fullmatch(r'\d{1,7}', lengths[0]) or not 1 <= int(lengths[0]) <= 2_000_000:
                self.send(413, {'error': 'invalid_request_size'})
                return
            raw = self.rfile.read(int(lengths[0]))
            if len(raw) != int(lengths[0]):
                raise ValueError('incomplete request')
            body = strict_json(raw.decode('utf-8'))
            if self.path == '/v1/jobs':
                self.send(202, self.server.manager.submit(body))
                return
            match = re.fullmatch(r'/v1/jobs/([0-9a-f]{32})/cancel', self.path)
            if match and body == {}:
                self.send(200, self.server.manager.cancel(match[1]))
                return
            self.send(404, {'error': 'not_found'})
        except QueueFull as exc:
            self.send(429, {'error': str(exc)})
        except KeyError:
            self.send(404, {'error': 'job_not_found'})
        except (ValueError, OSError):
            self.send(400, {'error': 'invalid_job_request'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, default=ROOT / 'tools/explorer/models.example.json')
    parser.add_argument('--jobs-dir', type=Path, default=ROOT / 'tmp/sslp-service/jobs')
    parser.add_argument('--port', type=int, default=8766)
    parser.add_argument('--site', default=SITE, choices=sorted(ORIGINS))
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--memory-mib', type=int, default=6144)
    args = parser.parse_args()
    manager = JobManager(args.jobs_dir, args.config, timeout=args.timeout, memory_mib=args.memory_mib)
    try:
        with LocalServer(('127.0.0.1', args.port), manager, site=args.site) as server:
            print(f'SSLP local service ready: http://127.0.0.1:{server.server_port}/connect', flush=True)
            try:
                server.serve_forever(poll_interval=.25)
            except KeyboardInterrupt:
                pass
    finally:
        manager.close()


if __name__ == '__main__':
    main()
