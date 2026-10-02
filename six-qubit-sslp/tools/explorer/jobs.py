"""One-worker local task queue with persistent records and bounded process trees."""
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time
import uuid

from . import class36, research
from .process_control import DirectoryLease, ProcessTree
from .providers import load_config, strict_json

ROOT = Path(__file__).resolve().parents[2]
TERMINAL = {'completed', 'failed', 'cancelled', 'timeout', 'interrupted'}


class QueueFull(ValueError):
    pass


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.new')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n', encoding='utf-8')
    os.replace(temporary, path)


def folder_size(folder):
    size = 0
    for path in folder.rglob('*'):
        try:
            if path.is_file():
                size += path.stat().st_size
        except FileNotFoundError:
            pass  # progress records use atomic replacement
    return size


def validate_request(body, default, providers):
    if not isinstance(body, dict) or set(body) - {'kind', 'input', 'question', 'provider', 'allow_lean'}:
        raise ValueError('unknown job fields')
    kind = body.get('kind')
    if kind not in ('agent', 'exact', 'lean'):
        raise ValueError('unsupported job kind')
    data = body.get('input')
    if isinstance(data, dict) and data.get('schema') == research.SCHEMA:
        research.validate(data)
    else:
        class36.validate(data)
    provider = body.get('provider', default)
    if not isinstance(provider, str) or provider not in providers or not providers[provider].enabled:
        raise ValueError('provider is missing or disabled')
    allow = body.get('allow_lean', False)
    if type(allow) is not bool:
        raise ValueError('allow_lean must be boolean')
    question = body.get('question', '')
    if not isinstance(question, str) or len(question) > 8000 or (kind == 'agent' and not question.strip()):
        raise ValueError('agent question requires 1 to 8000 characters')
    if kind != 'agent' and (question or allow or 'provider' in body):
        raise ValueError('model settings apply only to agent jobs')
    return {'kind': kind, 'input': copy.deepcopy(data), 'question': question,
            'provider': provider, 'allow_lean': allow}


class JobManager:
    def __init__(self, directory, config, *, timeout=600, memory_mib=6144, max_pending=4):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=True)
        self.config = Path(config).resolve()
        self.default, self.providers = load_config(config)
        if not 1 <= timeout <= 3600 or not 128 <= memory_mib <= 32768 or not 1 <= max_pending <= 16:
            raise ValueError('invalid service resource budget')
        self.timeout, self.memory_mib, self.max_pending = timeout, memory_mib, max_pending
        self.lease = DirectoryLease(self.directory / '.service.lock')
        self.condition = threading.Condition(threading.RLock())
        self.jobs, self.pending = {}, []
        self.stopping = False
        for path in self.directory.glob('*/job.json'):
            if not re.fullmatch(r'[0-9a-f]{32}', path.parent.name):
                continue
            job = strict_json(path.read_text(encoding='utf-8'))
            if job.get('state') not in TERMINAL:
                job.update(state='interrupted', finished_at=time.time(), error='Service restarted; this job was not automatically rerun.')
                write_json(path, job)
            self.jobs[job['id']] = job
        self.thread = threading.Thread(target=self._loop, name='sslp-job-queue', daemon=True)
        self.thread.start()

    def submit(self, body):
        request = validate_request(body, self.default, self.providers)
        with self.condition:
            if self.stopping:
                raise QueueFull('service is stopping')
            if len(self.jobs) >= 1000 or sum(j['state'] not in TERMINAL for j in self.jobs.values()) >= self.max_pending:
                raise QueueFull('The job queue is full. Wait for existing jobs to finish.')
            identifier = uuid.uuid4().hex
            folder = self.directory / identifier
            folder.mkdir()
            write_json(folder / 'request.json', request)
            job = {'id': identifier, 'kind': request['kind'], 'state': 'queued',
                   'input_sha256': class36.digest(request['input']),
                   'provider': request['provider'] if request['kind'] == 'agent' else None,
                   'created_at': time.time(), 'started_at': None, 'finished_at': None,
                   'cancel_requested': False, 'error': None}
            self.jobs[identifier] = job
            self._save(job)
            self.pending.append(identifier)
            self.condition.notify()
            return copy.deepcopy(job)

    def _save(self, job):
        write_json(self.directory / job['id'] / 'job.json', job)

    def get(self, identifier):
        with self.condition:
            if identifier not in self.jobs:
                raise KeyError('unknown job')
            job = copy.deepcopy(self.jobs[identifier])
        path = self.directory / identifier / 'progress.json'
        if path.is_file():
            try:
                job['progress'] = strict_json(path.read_text(encoding='utf-8'))
            except (ValueError, OSError):
                pass
        if job['state'] == 'completed':
            job['artifacts'] = [name for name in ('report.json', 'candidate.json', 'Certificate.lean', 'evidence.json', 'verification.zip')
                                if self.artifact(identifier, name).is_file()]
        return job

    def recent(self):
        with self.condition:
            identifiers = sorted(self.jobs, key=lambda k: self.jobs[k]['created_at'], reverse=True)[:12]
        return [self.get(identifier) for identifier in identifiers]

    def cancel(self, identifier):
        with self.condition:
            if identifier not in self.jobs:
                raise KeyError('unknown job')
            job = self.jobs[identifier]
            if job['state'] not in TERMINAL:
                job['cancel_requested'] = True
                if job['state'] == 'queued':
                    job.update(state='cancelled', finished_at=time.time())
                else:
                    job['state'] = 'cancelling'
                self._save(job)
                self.condition.notify()
        return self.get(identifier)

    def artifact(self, identifier, name):
        with self.condition:
            if identifier not in self.jobs or self.jobs[identifier]['state'] != 'completed':
                raise KeyError('completed job required')
        names = {'report.json': 'report.json', 'candidate.json': 'candidate.json',
                 'Certificate.lean': 'lean-job/Certificate.lean', 'evidence.json': 'lean-job/evidence.json',
                 'verification.zip': 'verification-bundle.zip'}
        if name not in names:
            raise KeyError('unknown artifact')
        return self.directory / identifier / 'output' / names[name]

    def _loop(self):
        while True:
            with self.condition:
                self.condition.wait_for(lambda: self.pending or self.stopping)
                if self.stopping and not self.pending:
                    return
                identifier = self.pending.pop(0)
                job = self.jobs[identifier]
                if job['state'] != 'queued':
                    continue
                if self.stopping:
                    job.update(state='cancelled', finished_at=time.time())
                    self._save(job)
                    continue
                job.update(state='running', started_at=time.time())
                self._save(job)
            self._run(identifier)

    def _run(self, identifier):
        folder = self.directory / identifier
        process, tree = None, None
        state, error = 'failed', 'The job failed without a complete result.'
        try:
            with (folder / 'worker.log').open('wb') as log:
                environment = dict(os.environ, PYTHONIOENCODING='utf-8')
                process = subprocess.Popen([sys.executable, str(ROOT / 'tools/sslp_worker.py'), str(folder),
                                            str(self.config), str(self.memory_mib)], cwd=ROOT, env=environment,
                                           stdin=subprocess.PIPE, stdout=log, stderr=subprocess.STDOUT,
                                           creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0,
                                           start_new_session=os.name != 'nt')
                tree = ProcessTree(process, self.memory_mib)
                process.stdin.write(b'GO\n')
                process.stdin.close()
                start = time.monotonic()
                while process.poll() is None:
                    with self.condition:
                        cancel = self.jobs[identifier]['cancel_requested'] or self.stopping
                    if cancel:
                        state, error = 'cancelled', 'Job cancelled; partial results were not marked complete.'
                        tree.terminate()
                        break
                    if time.monotonic() - start > self.timeout:
                        state, error = 'timeout', 'Job exceeded its total time limit; this is not a mathematical rejection.'
                        tree.terminate()
                        break
                    if folder_size(folder) > 64 * 1024 * 1024:
                        state, error = 'failed', 'Job output exceeded the size limit.'
                        tree.terminate()
                        break
                    time.sleep(.15)
                process.wait(timeout=15)
                if state not in ('cancelled', 'timeout') and process.returncode == 0:
                    report_path = folder / 'output/report.json'
                    report = strict_json(report_path.read_text(encoding='utf-8'))
                    if report['input_sha256'] != self.jobs[identifier]['input_sha256']:
                        raise ValueError('result input mismatch')
                    state, error = 'completed', None
        except (OSError, ValueError, subprocess.SubprocessError, KeyError):
            state, error = 'failed', 'Job did not complete. Inspect its local worker log.'
        finally:
            if tree:
                tree.close()  # KILL_ON_JOB_CLOSE also cleans any remaining Windows descendants.
            if process and process.stdin and not process.stdin.closed:
                process.stdin.close()
            if process and process.poll() is None:
                process.kill()
                process.wait(timeout=15)
            # Only remove a lock owned by this now-terminated worker. Other
            # verification drivers' locks are never adopted or removed.
            if process and process.poll() is not None:
                lock = ROOT / '.lake/build/certification/build.lock'
                try:
                    if lock.read_text().strip() == str(process.pid):
                        lock.unlink()
                except OSError:
                    pass
            with self.condition:
                job = self.jobs[identifier]
                if job['cancel_requested'] and state == 'completed':
                    state, error = 'cancelled', 'Job cancelled.'
                job.update(state=state, error=error, finished_at=time.time())
                self._save(job)

    def close(self):
        with self.condition:
            self.stopping = True
            self.condition.notify_all()
        self.thread.join(timeout=20)
        if self.thread.is_alive():
            raise RuntimeError('worker shutdown did not complete')
        self.lease.close()
