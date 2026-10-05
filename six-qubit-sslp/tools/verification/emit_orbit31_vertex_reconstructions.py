"""Propose integer face reconstructions; every identity is checked by Lean."""
import argparse
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
BLOCK = 16


def vec(items):
    return '![' + ','.join(map(str, items)) + ']'


def generate():
    data = json.loads((ROOT / 'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    M = s.Matrix(data['matrix'])
    matrices = []
    for point in data['primals']:
        support = [j for j in range(16) if point['mask'] >> j & 1]
        A = M[:, support]
        assert A.rank() == len(support)
        C = s.zeros(16, 7)
        for k, j in enumerate(support):
            rhs = s.zeros(len(support), 1)
            rhs[k] = 1
            row, parameters = A.T.gauss_jordan_solve(rhs)
            row = row.subs({v: 0 for v in parameters})
            for i in range(7):
                C[j, i] = row[i]
        assert C*A == s.Matrix(16, len(support), lambda j, k: int(j == support[k]))
        assert all((8*v).q == 1 for v in C)
        matrices.append(vec(vec(int(8*C[j, i]) for i in range(7)) for j in range(16)))
    assert len(matrices) == 204
    outputs = {}
    shards = []
    for start in range(0, 204, BLOCK):
        shard = start // BLOCK
        name = f'Shard{shard:03d}'
        count = min(BLOCK, 204-start)
        shards.append((name, start, count))
        outputs[f'MainTheory/Generated/Orbit31VertexReconstructions/{name}.lean'] = f'''import MainTheory.Orbit31VertexCertificateBase

/-! Kernel-checked integer face reconstructions for vertices {start}--{start+count-1}. -/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31VertexReconstructions.{name}
open MainTheory.Orbit31VertexCertificateBase
def candidates : Fin {count} → Matrix (Fin 16) (Fin 7) ℤ := {vec(matrices[start:start+count])}
theorem checked : ∀ j : Fin {count}, Valid ⟨{start}+j.val,by omega⟩ (candidates j) := by decide +kernel
end MainTheory.Generated.Orbit31VertexReconstructions.{name}
'''
    imports = '\n'.join(f'import MainTheory.Generated.Orbit31VertexReconstructions.{name}' for name, _, _ in shards)
    text = imports + '''

/-! Each of the 204 real candidates is unique on its face and is a vertex. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31VertexReconstructions.Aggregate
open MainTheory.Orbit31VertexCertificateBase
noncomputable section
def candidate (v : Fin 204) : Matrix (Fin 16) (Fin 7) ℤ :=
'''
    for i, (name, start, count) in enumerate(shards):
        local = f'⟨v.val-{start},by omega⟩'
        if i < len(shards)-1:
            text += f'  if h{i} : v.val < {start+count} then {name}.candidates {local} else\n'
        else:
            text += f'  {name}.candidates {local}\n'
    text += '\ntheorem valid (v : Fin 204) : Valid v (candidate v) := by\n  unfold candidate\n'
    for i, (name, start, count) in enumerate(shards):
        prefix = '  ' + '  '*i
        if i < len(shards)-1:
            text += f'{prefix}by_cases h{i} : v.val < {start+count}\n'
            text += f'{prefix}· rw [dif_pos h{i}]\n'
            proof_prefix = prefix+'  '
        else:
            proof_prefix = prefix
        text += f'''{proof_prefix}have hi : (⟨{start}+(v.val-{start}),by omega⟩ : Fin 204) = v := by
{proof_prefix}  apply Fin.ext
{proof_prefix}  dsimp
{proof_prefix}  omega
{proof_prefix}simpa only [hi] using {name}.checked ⟨v.val-{start},by omega⟩
'''
        if i < len(shards)-1:
            text += f'{prefix}· rw [dif_neg h{i}]\n'
    text += '''
theorem every_candidate_extreme (v : Fin 204) :
    MainTheory.Orbit31SupportSemantics.primal v ∈
    ({p | MainTheory.MatrixPositiveSupportCertificates.Feasible
      MainTheory.Orbit31SupportBase.M MainTheory.Orbit31SupportBase.b p} :
      Set (Fin 16 → ℝ)).extremePoints ℝ := extreme (valid v)
end
end MainTheory.Generated.Orbit31VertexReconstructions.Aggregate
'''
    outputs['MainTheory/Generated/Orbit31VertexReconstructions/Aggregate.lean'] = text
    return outputs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generate()
    for relative, text in outputs.items():
        path = ROOT / relative
        if args.check:
            if path.read_text(encoding='utf8') != text:
                raise SystemExit(f'stale source: {relative}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf8', newline='\n')
    print(f'{len(outputs)} vertex reconstruction modules ' + ('checked' if args.check else 'emitted'))


if __name__ == '__main__':
    main()
