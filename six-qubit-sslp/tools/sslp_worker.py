#!/usr/bin/env python3
"""Internal gated worker. Only the local service launches this process."""
import json
import os
from pathlib import Path
import sys


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.new')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n', encoding='utf-8')
    os.replace(temporary, path)


def main():
    # The parent assigns the OS process-tree limits BEFORE allowing work.
    if sys.stdin.readline().strip() != 'GO':
        return 2
    job_dir, config = Path(sys.argv[1]), Path(sys.argv[2])
    if os.name != 'nt':
        import resource
        bound = int(sys.argv[3]) * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (bound, bound))
    return run_job(job_dir, config)


def run_job(job_dir, config):
    """Execute a validated fixed-kind request; OS limits are set by main/parent."""
    from explorer import class36
    from explorer.agent import run_agent, exact_summary
    from explorer.providers import ModelClient, load_config, strict_json
    import sslp_explorer
    request = strict_json((job_dir / 'request.json').read_text(encoding='utf-8'))
    data = request['input']
    adapter = sslp_explorer.case_adapter(data)
    adapter.validate(data)
    output = job_dir / 'output'
    output.mkdir()
    progress = lambda event: write_json(job_dir / 'progress.json', event)
    if request['kind'] == 'agent':
        default, providers = load_config(config)
        client = ModelClient(providers[request.get('provider') or default])
        report, session = run_agent(client, data, request['question'], output,
                                    allow_lean=request['allow_lean'], progress=progress)
        if session.candidate is not None:
            write_json(output / 'candidate.json', session.candidate)
        for key, exact in session.exact.items():
            write_json(output / f'exact-{key}.json', exact)
        kernel_dir = output / 'lean-job'
    elif request['kind'] == 'exact':
        progress({'phase': 'exact'})
        exact = adapter.exact_checks(data)
        write_json(output / 'exact.json', exact)
        report = {'schema': 'sslp.direct-job-result.v1', 'kind': 'exact', 'input_sha256': class36.digest(data),
                  'verification': [{'input_sha256': class36.digest(data), 'exact': exact_summary(exact), 'kernel': {'status': 'not_run'}}]}
        kernel_dir = output / 'nonexistent'
    else:
        import sslp_explorer
        progress({'phase': 'lean'})
        kernel_dir = output / 'lean-job'
        evidence = sslp_explorer.verify_case(data, kernel_dir, lean=True, timeout=180)
        exact = strict_json((kernel_dir / 'exact.json').read_text(encoding='utf-8'))
        report = {'schema': 'sslp.direct-job-result.v1', 'kind': 'lean', 'input_sha256': class36.digest(data),
                  'verification': [{'input_sha256': class36.digest(data), 'exact': exact_summary(exact), 'kernel': evidence['kernel']}]}
    if (kernel_dir / 'evidence.json').is_file():
        import sslp_explorer
        # A rejected/timed-out proof still has a useful completed report.
        # Only successful checks can become a successful-example bundle.
        evidence = strict_json((kernel_dir / 'evidence.json').read_text(encoding='utf-8'))
        if evidence.get('passed_requested_checks'):
            progress({'phase': 'packaging'})
            sslp_explorer.export_bundle(kernel_dir, output / 'verification-bundle')
    write_json(output / 'report.json', report)
    progress({'phase': 'finished'})
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
