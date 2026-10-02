"""Archive the fetched GitHub baselines without modifying the working tree."""
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parents[2]
heads = {
    'sixqubit-classification': '7ac9a049a8cfb997427a24cb33547fb0592fc170',
    'main': '8eb16e2f31b512b3bebc8d8a276bd2efd720d706',
    'dev-zc': '52e43c8d36f5c1317cd1ec380e380e5e8ad879d3',
}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=root).decode('utf8').strip()


remote = heads['sixqubit-classification']
trees = {}
for name in ['MainTheory', 'SixQubit', 'SS']:
    local_tree = git('rev-parse', f'HEAD:{name}')
    remote_tree = git('rev-parse', f'{remote}:six-qubit-sslp/{name}')
    assert local_tree == remote_tree, ('baseline changed; repeat comparison', name)
    trees[name] = dict(local_head_tree=local_tree, github_tree=remote_tree, identical=True)
reused = ['ColoredBound', 'BinaryPivot', 'FiniteLift', 'PivotSmithNormalForm',
          'SharpSectorBound', 'SharpSectorZDetection', 'GeneralLiftOrder',
          'GeneralSpectralSectors', 'BetaAtPivotRank']
files = {}
for name in reused:
    path = f'MainTheory/{name}.lean'
    assert not git('diff', 'HEAD', '--', path), ('reused source changed', path)
    files[path] = dict(
        github_blob=git('rev-parse', f'{remote}:six-qubit-sslp/{path}'),
        local_head_blob=git('rev-parse', f'HEAD:{path}'),
        working_sha256=hashlib.sha256((root/path).read_bytes()).hexdigest(),
        url=f'https://github.com/xh-xihe/dyadic-lifts/blob/{remote}/six-qubit-sslp/{path}')
    assert files[path]['github_blob'] == files[path]['local_head_blob']
result = dict(
    compared_at_utc=datetime.now(timezone.utc).isoformat(),
    remote=git('remote', 'get-url', 'origin'),
    local_head=git('rev-parse', 'HEAD'),
    local_branch=git('branch', '--show-current'),
    observed_remote_heads=heads,
    commits={branch: git('show', '-s', '--format=%H %cs %s', commit)
             for branch, commit in heads.items()},
    method='Read-only git ls-remote followed by fetch --no-tags; compare Git tree and blob identities. '
           'The branch snapshots are the heads observed during this session, not a claim about future heads.',
    proof_subtree='six-qubit-sslp', proof_trees=trees, reused_sources=files,
    note='The committed proof baselines match exactly despite different repository layouts and commit '
         'histories. Uncommitted 20260924 proof increments are additional local work. No merge, '
         'checkout, commit or push was performed.')
(Path(__file__).parent/'github-comparison.json').write_text(
    json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
print('Verified identical GitHub/local committed proof trees and', len(files), 'reused source files')
