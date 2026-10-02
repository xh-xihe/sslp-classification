#!/usr/bin/env python3
"""Local SSLP assistant: explicit providers, bounded tools, separate evidence."""
import argparse
import json
from pathlib import Path
import sys

from explorer import class36, research
from explorer.agent import run_agent
from explorer.providers import ModelClient, ProviderError, load_config, strict_json

ROOT = Path(__file__).resolve().parent.parent


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n', encoding='utf-8')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, default=ROOT / 'tools/explorer/models.example.json')
    parser.add_argument('--provider', help='Explicit provider id; never falls back to another provider')
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('providers', help='List configured models without making network calls')
    sub.add_parser('probe', help='Check the selected endpoint and model availability')
    run = sub.add_parser('run', help='Run a bounded assistant task and save actual tool results')
    question = run.add_mutually_exclusive_group(required=True)
    question.add_argument('--question')
    question.add_argument('--question-file', type=Path)
    run.add_argument('--input', type=Path, help='Code JSON exported by the workbench; otherwise canonical case')
    run.add_argument('--output', type=Path, required=True, help='A new directory for this run')
    run.add_argument('--allow-lean', action='store_true', help='Allow one real input-bound Lean job')
    run.add_argument('--max-rounds', type=int, default=6)
    run.add_argument('--max-tools', type=int, default=10)
    run.add_argument('--lean-timeout', type=int, default=180)
    args = parser.parse_args(argv)
    try:
        default, providers = load_config(args.config)
        if args.command == 'providers':
            print(json.dumps({'default_provider': default, 'providers': [p.public() for p in providers.values()]}, ensure_ascii=False, indent=2))
            return 0
        selected = args.provider if args.provider is not None else default
        if selected not in providers:
            raise ProviderError('unknown provider id')
        client = ModelClient(providers[selected])
        if args.command == 'probe':
            print(json.dumps(client.probe(), ensure_ascii=False, indent=2))
            return 0
        if args.input:
            if args.input.stat().st_size > 2_000_000:
                raise ValueError('input exceeds 2 MB')
            data = strict_json(args.input.read_text(encoding='utf-8'))
        else:
            data = class36.example()
        (research if data.get('schema') == research.SCHEMA else class36).validate(data)
        if args.question_file and args.question_file.stat().st_size > 32000:
            raise ValueError('question file exceeds 32 KB')
        question = args.question_file.read_text(encoding='utf-8') if args.question_file else args.question
        args.output.mkdir(parents=True, exist_ok=False)
        write_json(args.output / 'input.json', data)
        print(f'Running {selected} / {client.provider.model}; model text is not a certificate.', flush=True)
        report, session = run_agent(client, data, question, args.output, allow_lean=args.allow_lean,
                                    max_rounds=args.max_rounds, max_tools=args.max_tools,
                                    lean_timeout=args.lean_timeout)
        if session.candidate is not None:
            write_json(args.output / 'candidate.json', session.candidate)
        for key, exact in session.exact.items():
            write_json(args.output / f'exact-{key}.json', exact)
        write_json(args.output / 'run.json', report)
        print(json.dumps({'status': report['status'], 'error': report['error'], 'provider': selected,
                          'tool_calls': len(report['tools']), 'seconds': report['seconds'],
                          'report': str(args.output / 'run.json')}, ensure_ascii=False))
        print('\nModel explanation (not a certificate):\n' + report['answer']['text'])
        print('\nTool evidence: ' + json.dumps([{'input_sha256': row['input_sha256'],
                                                'exact_kl_passed': row['exact']['kl_passed'] if row['exact'] else None,
                                                'kernel_status': row['kernel']['status']} for row in report['verification']], ensure_ascii=False))
        return 0 if report['status'] == 'answered' else 2
    except (ValueError, OSError) as exc:
        print('Assistant error: ' + str(exc), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
