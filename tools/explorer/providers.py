"""Explicit model routing; models cannot create verification evidence.

Standard-library transports for local Ollama and Chat Completions-compatible
servers. Configuration is trusted operator input; tool arguments never choose
an endpoint or credential. No provider fallback or redirects are performed.
"""
from dataclasses import dataclass
import ipaddress
import json
import os
from pathlib import Path
import re
import socket
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import Request, HTTPRedirectHandler, ProxyHandler, build_opener


class ProviderError(ValueError):
    pass


def strict_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('duplicate JSON key')
            result[key] = value
        return result
    def constant(_):
        raise ValueError('nonfinite JSON number')
    try:
        return json.loads(text, object_pairs_hook=pairs, parse_constant=constant)
    except (ValueError, RecursionError) as exc:
        raise ProviderError('invalid JSON') from exc


def bounded_int(value, low, high):
    return type(value) is int and low <= value <= high


@dataclass(frozen=True)
class Provider:
    id: str
    adapter: str
    model: str
    model_class: str
    base_url: str
    enabled: bool = True
    api_key_env: str | None = None
    timeout_seconds: int = 120
    max_output_tokens: int = 1600
    context_tokens: int = 8192
    revision: str | None = None

    def public(self):
        return {'id': self.id, 'adapter': self.adapter, 'model': self.model,
                'model_class': self.model_class, 'enabled': self.enabled,
                'configured_revision': self.revision,
                'timeout_seconds': self.timeout_seconds,
                'max_output_tokens': self.max_output_tokens}


def load_config(path):
    path = Path(path)
    if path.stat().st_size > 65536:
        raise ProviderError('model configuration exceeds 64 KB')
    data = strict_json(path.read_text(encoding='utf-8'))
    if not isinstance(data, dict) or set(data) != {'schema', 'default_provider', 'providers'}:
        raise ProviderError('invalid model configuration fields')
    if data['schema'] != 'sslp.model-providers.v1' or not isinstance(data['providers'], list):
        raise ProviderError('unsupported model configuration')
    if not 1 <= len(data['providers']) <= 16:
        raise ProviderError('one to sixteen providers required')
    providers = {}
    fields = set(Provider.__dataclass_fields__)
    for item in data['providers']:
        if not isinstance(item, dict) or set(item) - fields:
            raise ProviderError('unknown provider fields (store credentials in environment variables)')
        try:
            p = Provider(**item)
        except TypeError as exc:
            raise ProviderError('missing provider configuration') from exc
        if not isinstance(p.id, str) or not re.fullmatch(r'[a-z][a-z0-9_-]{0,47}', p.id) or p.id in providers:
            raise ProviderError('invalid or duplicate provider id')
        if p.adapter not in ('ollama', 'chat_completions') or p.model_class not in ('open_weights', 'closed'):
            raise ProviderError('unsupported adapter or model class')
        if not isinstance(p.model, str) or not 1 <= len(p.model) <= 160 or any(ord(c) < 32 for c in p.model):
            raise ProviderError('invalid model name')
        if type(p.enabled) is not bool:
            raise ProviderError('enabled must be a boolean')
        if p.revision is not None and (not isinstance(p.revision, str) or len(p.revision) > 160):
            raise ProviderError('invalid revision')
        if not bounded_int(p.timeout_seconds, 1, 300) or not bounded_int(p.max_output_tokens, 64, 8192) or not bounded_int(p.context_tokens, 2048, 32768):
            raise ProviderError('provider budget outside supported limits')
        if p.api_key_env is not None and (not isinstance(p.api_key_env, str) or not re.fullmatch(r'[A-Z][A-Z0-9_]{0,79}', p.api_key_env)):
            raise ProviderError('invalid credential environment-variable name')
        if not isinstance(p.base_url, str):
            raise ProviderError('invalid provider URL')
        try:
            url = urlsplit(p.base_url)
            _ = url.port
        except ValueError as exc:
            raise ProviderError('invalid provider URL') from exc
        try:
            local = url.hostname == 'localhost' or ipaddress.ip_address(url.hostname or '').is_loopback
        except ValueError:
            local = False
        if (url.scheme not in ('http', 'https') or not url.hostname or url.username or url.password
                or url.query or url.fragment or any(ord(c) < 33 for c in p.base_url)):
            raise ProviderError('provider URL must have a plain HTTP(S) origin and optional path')
        if url.scheme == 'http' and not local:
            raise ProviderError('remote model endpoints require HTTPS')
        providers[p.id] = p
    default = data['default_provider']
    if not isinstance(default, str) or default not in providers or not providers[default].enabled:
        raise ProviderError('default provider must be enabled')
    if providers[default].model_class != 'open_weights':
        raise ProviderError('default provider must be an open-weight model; select closed providers explicitly')
    return default, providers


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def timeout_message(provider):
    detail = ("Ollama may be waiting for another request or loading the model. "
              "Let other Ollama requests finish, then retry; direct exact and Lean checks need no model. "
              if provider.adapter == 'ollama' else "Retry when the selected provider is responsive. ")
    return (f'provider timed out after {provider.timeout_seconds} seconds for one request; '
            + detail + 'no fallback attempted')


def request_json(provider, route, payload=None):
    headers = {'Accept': 'application/json'}
    if provider.api_key_env:
        key = os.environ.get(provider.api_key_env)
        if not key:
            raise ProviderError('missing credential environment variable: ' + provider.api_key_env)
        if '\r' in key or '\n' in key:
            raise ProviderError('invalid credential')
        headers['Authorization'] = 'Bearer ' + key
    body = None
    if payload is not None:
        body = json.dumps(payload, ensure_ascii=False, allow_nan=False).encode('utf-8')
        if len(body) > 262144:
            raise ProviderError('model request exceeds 256 KB context budget')
        headers['Content-Type'] = 'application/json'
    url = provider.base_url.rstrip('/') + route
    # Configured endpoints are direct: do not leak localhost payloads via ambient proxies.
    opener = build_opener(ProxyHandler({}), NoRedirect())
    try:
        with opener.open(Request(url, data=body, headers=headers), timeout=provider.timeout_seconds) as response:
            raw = response.read(2_000_001)
        if len(raw) > 2_000_000:
            raise ProviderError('model response exceeds 2 MB')
        result = strict_json(raw.decode('utf-8'))
        if not isinstance(result, dict):
            raise ProviderError('model response must be an object')
        return result
    except HTTPError as exc:
        # Do not copy provider error bodies, authorization headers, or secrets to logs.
        raise ProviderError(f'provider returned HTTP {exc.code}; no fallback attempted') from None
    except (TimeoutError, socket.timeout):
        raise ProviderError(timeout_message(provider)) from None
    except URLError as exc:
        if isinstance(exc.reason, (TimeoutError, socket.timeout)):
            raise ProviderError(timeout_message(provider)) from None
        raise ProviderError('provider unavailable or response invalid; no fallback attempted') from None
    except (OSError, UnicodeError, RecursionError):
        raise ProviderError('provider unavailable or response invalid; no fallback attempted') from None


def normalize_message(raw, adapter):
    if not isinstance(raw, dict) or raw.get('role') != 'assistant':
        raise ProviderError('expected an assistant message')
    content = raw.get('content') or ''
    if not isinstance(content, str) or len(content) > 40000:
        raise ProviderError('invalid assistant text')
    calls = raw.get('tool_calls', []) or []
    if not isinstance(calls, list) or len(calls) > 8:
        raise ProviderError('too many or malformed tool calls')
    normalized, identifiers = [], set()
    for index, call in enumerate(calls):
        if not isinstance(call, dict) or not isinstance(call.get('function'), dict):
            raise ProviderError('invalid tool call')
        function = call['function']
        name, args = function.get('name'), function.get('arguments')
        if not isinstance(name, str) or not re.fullmatch(r'[a-z_]{1,64}', name):
            raise ProviderError('invalid tool name')
        if isinstance(args, str):
            if len(args) > 16000:
                raise ProviderError('tool arguments exceed budget')
            args = strict_json(args)
        if not isinstance(args, dict) or len(json.dumps(args)) > 16000:
            raise ProviderError('tool arguments must be a bounded object')
        identifier = call.get('id', f'call_{index}') if adapter == 'ollama' else call.get('id')
        if not isinstance(identifier, str) or not re.fullmatch(r'[A-Za-z0-9_-]{1,128}', identifier) or identifier in identifiers:
            raise ProviderError('missing or duplicate tool-call identifier')
        identifiers.add(identifier)
        normalized.append({'id': identifier, 'type': 'function',
                           'function': {'name': name, 'arguments': json.dumps(args, ensure_ascii=False)}})
    return {'role': 'assistant', 'content': content, **({'tool_calls': normalized} if normalized else {})}


class ModelClient:
    def __init__(self, provider, transport=request_json):
        if not provider.enabled:
            raise ProviderError('selected provider is disabled; configure it before selecting it')
        self.provider, self.transport = provider, transport

    def probe(self):
        p = self.provider
        if p.adapter == 'ollama':
            version = self.transport(p, '/api/version')
            listing = self.transport(p, '/api/tags')
            models = listing.get('models')
            if not isinstance(models, list):
                raise ProviderError('invalid model listing')
            match = next((x for x in models if isinstance(x, dict) and x.get('name') == p.model), None)
            if match is None:
                raise ProviderError('configured local model is not installed')
            if p.revision and match.get('digest') != p.revision:
                raise ProviderError('installed model digest differs from configured revision')
            return {'status': 'available', 'provider': p.public(), 'server_version': version.get('version'),
                    'observed_revision': match.get('digest')}
        listing = self.transport(p, '/models')
        models = listing.get('data')
        if not isinstance(models, list) or not any(isinstance(x, dict) and x.get('id') == p.model for x in models):
            raise ProviderError('configured model is not listed by provider')
        return {'status': 'available', 'provider': p.public(), 'observed_revision': None}

    def complete(self, messages, tools):
        p = self.provider
        start = time.monotonic()
        if p.adapter == 'ollama':
            converted = []
            for message in messages:
                row = {k: v for k, v in message.items() if k in ('role', 'content', 'tool_calls')}
                if row.get('tool_calls'):
                    row['tool_calls'] = [{'function': {'name': c['function']['name'],
                                          'arguments': strict_json(c['function']['arguments'])}}
                                         for c in row['tool_calls']]
                if message['role'] == 'tool':
                    row['tool_name'] = message['name']
                converted.append(row)
            response = self.transport(p, '/api/chat', {
                'model': p.model, 'messages': converted, 'tools': tools, 'stream': False,
                'think': False, 'keep_alive': '5m',
                'options': {'temperature': 0, 'num_ctx': p.context_tokens, 'num_predict': p.max_output_tokens}})
            raw = response.get('message')
            finish = response.get('done_reason')
            if response.get('done') is not True:
                raise ProviderError('incomplete model response')
            usage = {'input_tokens': response.get('prompt_eval_count'), 'output_tokens': response.get('eval_count')}
        else:
            converted = [{k: v for k, v in m.items() if k != 'name'} for m in messages]
            response = self.transport(p, '/chat/completions', {
                'model': p.model, 'messages': converted, 'tools': tools, 'stream': False,
                'temperature': 0, 'max_tokens': p.max_output_tokens, 'tool_choice': 'auto'})
            choices = response.get('choices')
            if not isinstance(choices, list) or len(choices) != 1 or not isinstance(choices[0], dict):
                raise ProviderError('expected exactly one completion')
            raw, finish = choices[0].get('message'), choices[0].get('finish_reason')
            raw_usage = response.get('usage') or {}
            if not isinstance(raw_usage, dict):
                raise ProviderError('invalid usage metadata')
            usage = {'input_tokens': raw_usage.get('prompt_tokens'), 'output_tokens': raw_usage.get('completion_tokens')}
        if finish not in ('stop', 'tool_calls'):
            raise ProviderError('model output was truncated or unfinished; tools were not executed')
        message = normalize_message(raw, p.adapter)
        usage = {k: v if bounded_int(v, 0, 10**9) else None for k, v in usage.items()}
        return {'message': message, 'finish_reason': finish, 'usage': usage,
                'reported_model': response.get('model'), 'seconds': round(time.monotonic() - start, 3)}
