"""Exact six-qubit case adapter. No numerical result is a kernel certificate."""
import hashlib
import copy
import json
import math
from pathlib import Path

from generators import gen36code as arithmetic
from core.orbit import fiber

ROOT = Path(__file__).resolve().parents[2]
SCHEMA = 'sslp.code-instance.v1'
BASIS = ['1', 'sqrt(2)', 'sqrt(3)', 'sqrt(6)', 'i', 'i*sqrt(2)', 'i*sqrt(3)', 'i*sqrt(6)']
CONVENTIONS = {'qubit_labels': [1, 2, 3, 4, 5, 6],
               'bitstring': 'leftmost character is qubit 1; integer mask bit 0 is qubit 1',
               'pauli': 'i^popcount(x&z) X^x Z^z',
               'phase_gate': 'diag(1, exp(2*pi*i*a/q))',
               'logical_basis': ['psi_0', 'psi_1']}


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':'), allow_nan=False).encode('utf-8')


def digest(value):
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def example():
    words = arithmetic.build_amps()
    sources = {}
    for name in ('main.tex', 'supplementary.tex'):
        path = ROOT / 'documents/20260924' / name
        if path.is_file():
            sources[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return {'schema': SCHEMA, 'id': 'class36-canonical-20260924',
            'paper': {'version': '20260924', 'sources_sha256': sources,
                      'labels': ['eq:six-C5-code0', 'eq:six-C5-code1', 'eq:six-C5-logical-action']},
            'n': 6, 'k': 2, 'distance_lower_bound': 3,
            'orbit': {'id': 36, 'gauge': 'symmetric', 'table_angles': [1, 1, 1, 2, 2, 4]},
            'conventions': copy.deepcopy(CONVENTIONS),
            'amplitude_encoding': {'basis': BASIS.copy(), 'common_scale': '1/(2*sqrt(30))'},
            'gate': {'q': 5, 'angles': list(arithmetic.ASTAR), 'logical_residues': [0, 4]},
            'words': [[{'bits': arithmetic.unmask(mask), 'coordinates': list(value)}
                       for mask, value in sorted(word.items())] for word in words]}


def integer(value, low, high):
    return type(value) is int and low <= value <= high


def validate(data):
    if not isinstance(data, dict):
        raise ValueError('code instance must be a JSON object')
    if data.get('schema') != SCHEMA:
        raise ValueError('unsupported code-instance schema')
    if any(type(data.get(k)) is not int or data[k] != v
           for k, v in [('n', 6), ('k', 2), ('distance_lower_bound', 3)]):
        raise ValueError('this adapter supports only n=6, K=2, distance lower bound 3')
    if data.get('conventions') != CONVENTIONS:
        raise ValueError('unsupported or missing bit/phase/logical-basis conventions')
    if data.get('orbit') != {'id': 36, 'gauge': 'symmetric', 'table_angles': [1, 1, 1, 2, 2, 4]}:
        raise ValueError('this adapter requires the documented class-36 symmetric gauge')
    if data.get('amplitude_encoding') != {'basis': BASIS, 'common_scale': '1/(2*sqrt(30))'}:
        raise ValueError('unsupported exact amplitude representation')
    gate = data.get('gate', {})
    if not isinstance(gate, dict):
        raise ValueError('gate must be a JSON object')
    if type(gate.get('q')) is not int or gate['q'] != 5:
        raise ValueError('this first adapter supports q=5')
    if not isinstance(gate.get('angles'), list) or len(gate['angles']) != 6 or not all(integer(x, 0, 4) for x in gate['angles']):
        raise ValueError('angles must be six integers in [0,4]')
    if not isinstance(gate.get('logical_residues'), list) or len(gate['logical_residues']) != 2 or not all(integer(x, 0, 4) for x in gate['logical_residues']):
        raise ValueError('logical residues must be two integers in [0,4]')
    if not isinstance(data.get('words'), list) or len(data['words']) != 2:
        raise ValueError('two logical words are required')
    words = []
    for rows in data['words']:
        if not isinstance(rows, list) or not 1 <= len(rows) <= 64:
            raise ValueError('each word must contain 1 to 64 entries')
        word = {}
        for row in rows:
            if not isinstance(row, dict):
                raise ValueError('amplitude entry must be a JSON object')
            bits, coords = row.get('bits'), row.get('coordinates')
            if not isinstance(bits, str) or len(bits) != 6 or set(bits) - {'0', '1'}:
                raise ValueError('invalid six-character bitstring')
            if not isinstance(coords, list) or len(coords) != 8 or not all(integer(x, -1000000, 1000000) for x in coords):
                raise ValueError('each exact amplitude needs eight bounded integers')
            mask = arithmetic.mask(bits)
            if mask in word:
                raise ValueError('duplicate basis string: ' + bits)
            word[mask] = tuple(coords)
        words.append(word)
    return words


def exact_checks(data):
    words = validate(data)
    g = arithmetic
    target = (120,) + (0,) * 7
    norm = [g.matelt(w, w, sorted(w), 0, 0) for w in words]
    cross = g.matelt(words[0], words[1], sorted(words[1]), 0, 0)
    normalization = norm == [target, target] and cross == g.ZERO
    rows = []
    for x in range(64):
        for z in range(64):
            if (x | z).bit_count() > 2:
                continue
            raw = [[g.matelt(a, b, sorted(b), x, z) for b in words] for a in words]
            phase = (1, 0, 0, 0, 0, 0, 0, 0)
            for _ in range((x & z).bit_count()):
                phase = g.zmul(phase, (0, 0, 0, 0, 1, 0, 0, 0))
            matrix = [[g.zmul(phase, value) for value in line] for line in raw]
            rows.append({'x_mask': x, 'z_mask': z, 'pauli': g.paulilabel(x, z),
                         'matrix_coordinates': matrix, 'matrix_denominator': 120,
                         'passed': matrix[0][0] == matrix[1][1] and matrix[0][1] == matrix[1][0] == g.ZERO})
    fibers = [fiber(data['gate']['angles'], 5, r) for r in data['gate']['logical_residues']]
    supports_ok = all(all(g.unmask(m) in f for m, v in w.items() if v != g.ZERO)
                      for w, f in zip(words, fibers))
    moment_rows = []
    for subset in [(i,) for i in range(6)] + [(i, j) for i in range(6) for j in range(i + 1, 6)]:
        expectations = []
        for word in words:
            value = g.ZERO
            for mask, amp in word.items():
                if all(mask & (1 << bit) for bit in subset):
                    value = g.zadd(value, g.zmul(g.zconj(amp), amp))
            expectations.append(value)
        moment_rows.append({'qubits': [i + 1 for i in subset], 'coordinates': expectations,
                            'denominator': 120, 'passed': expectations[0] == expectations[1]})
    probabilities, preview = [], []
    for word in words:
        probabilities.append({g.unmask(m): list(g.zmul(g.zconj(v), v)) for m, v in sorted(word.items())})
        preview.append({g.unmask(m): [g.zfloat(v).real / math.sqrt(120), g.zfloat(v).imag / math.sqrt(120)]
                        for m, v in sorted(word.items())})
    return {'schema': 'sslp.exact-check.v1', 'input_sha256': digest(data),
            'method': 'exact integer arithmetic in Z[sqrt(2),sqrt(3),i]',
            'scope': 'this supplied instance only; distance at least 3',
            'kernel_status': 'not_run',
            'passed': normalization and supports_ok and all(row['passed'] for row in rows),
            'normalization_and_orthogonality': normalization, 'norm_coordinates': norm,
            'fibers': fibers, 'support_matches_gate': supports_ok,
            'pauli_count': len(rows), 'kl': rows, 'moments': moment_rows,
            'probability_coordinates': probabilities, 'probability_denominator': 120,
            'preview': {'method': 'floating_point_display_only', 'amplitudes': preview},
            'circuit': {'encoder': {'kind': 'abstract_isometry', 'gate_decomposition': 'not_implemented'},
                        'transversal_layer': [{'qubit': i + 1, 'gate': 'phase', 'turns': [a, 5]}
                                              for i, a in enumerate(data['gate']['angles'])]}}


def lean_certificate(data):
    """Generate closed, typed input checks; untrusted prose is never interpolated."""
    words = validate(data)
    def literal(x):
        return str(x) if x >= 0 else f'({x})'
    lines = ['import SixQubit.Orbit36Code', 'import Lean.Util.CollectAxioms', '',
             'set_option maxRecDepth 40000', 'namespace SSLPExplorerCase',
             'open SixQubit.Orbit36Code', 'noncomputable section', '']
    for index, word in enumerate(words):
        terms = [f"if num x = {m} then z8 {' '.join(map(literal, v))}" for m, v in sorted(word.items())]
        lines += [f'def data{index} (x : SS.BitString 6) : ZQ :=',
                  '  ' + ' else\n  '.join(terms) + ' else ZQ.zero',
                  f'theorem data{index}_matches : ∀ x, data{index} x = c{index}z x := by decide',
                  f'def state{index} : SS.State 6 ℂ := stC data{index}',
                  f'theorem state{index}_matches : state{index} = {"c36" if index == 0 else "d36"} := by',
                  f'  funext x; simp only [state{index}, {"c36" if index == 0 else "d36"}, stC, data{index}_matches]', '']
    angles = ', '.join(map(str, data['gate']['angles']))
    lines += [f'def angles : Fin 6 → ZMod 5 := ![{angles}]']
    for index, residue in enumerate(data['gate']['logical_residues']):
        lines += [f'theorem fiber{index} : ∀ x, data{index} x ≠ ZQ.zero → SS.weight angles x = ({residue} : ZMod 5) := by decide',
                  f'theorem support{index} : SS.SSConditionState angles ({residue} : ZMod 5) state{index} := by',
                  '  intro x hx', f'  apply fiber{index} x', '  intro hz', '  apply hx',
                  f'  simp [state{index}, stC, hz, toC_zero]',
                  f'theorem logical{index} (zeta : ℂ) :',
                  f'    SS.Dact (fun r : ZMod 5 => zeta ^ r.val) angles state{index} =',
                  f'      fun x => zeta ^ {residue} * state{index} x := by',
                  f'  simpa using SS.Dact_eq_global_of_SS (fun r : ZMod 5 => zeta ^ r.val) angles ({residue} : ZMod 5) state{index} support{index}', '']
    lines += ['open scoped BigOperators',
              'def totalAngle (x : SS.BitString 6) : Nat := ∑ j, if x j then (angles j).val else 0',
              'theorem residue_eq : ∀ x, totalAngle x % 5 = (SS.weight angles x).val := by decide',
              'def physicalGate (zeta : ℂ) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=',
              '  fun x => (∏ j, zeta ^ (if x j then (angles j).val else 0)) * psi x',
              'theorem physical_eq (zeta : ℂ) (hz : zeta ^ 5 = 1) (psi : SS.State 6 ℂ) :',
              '    physicalGate zeta psi = SS.Dact (fun r : ZMod 5 => zeta ^ r.val) angles psi := by',
              '  funext x',
              '  have hp : zeta ^ totalAngle x = zeta ^ (totalAngle x % 5) := by',
              '    calc',
              '      zeta ^ totalAngle x = zeta ^ (totalAngle x % 5 + 5 * (totalAngle x / 5)) := by',
              '        rw [Nat.mod_add_div]',
              '      _ = zeta ^ (totalAngle x % 5) := by rw [pow_add, pow_mul, hz, one_pow, mul_one]',
              '  simp only [physicalGate, SS.Dact, Finset.prod_pow_eq_pow_sum]',
              '  change zeta ^ totalAngle x * psi x = _',
              '  rw [hp, residue_eq]',
              'def encode (alpha beta : ℂ) : SS.State 6 ℂ := fun x => alpha * state0 x + beta * state1 x',
              'theorem physical_logical (zeta : ℂ) (hz : zeta ^ 5 = 1) (alpha beta : ℂ) :',
              f'    physicalGate zeta (encode alpha beta) = encode (zeta ^ {data["gate"]["logical_residues"][0]} * alpha) (zeta ^ {data["gate"]["logical_residues"][1]} * beta) := by',
              '  rw [physical_eq zeta hz]', '  funext x',
              '  have h0 := congrFun (logical0 zeta) x',
              '  have h1 := congrFun (logical1 zeta) x',
              '  simp only [SS.Dact] at h0 h1 ⊢',
              '  simp only [encode]',
              '  calc',
              '    _ = alpha * (zeta ^ (SS.weight angles x).val * state0 x) + beta * (zeta ^ (SS.weight angles x).val * state1 x) := by ring',
              '    _ = _ := by rw [h0, h1]; ring',
              'theorem distance : SS.HasDistance ![state0, state1] 3 := by',
              '  rw [state0_matches, state1_matches]; exact canonical_is_code',
              'theorem normalized0 : SS.innerC state0 state0 = 1 := by',
              '  rw [state0_matches]; exact c36_normalized',
              'theorem normalized1 : SS.innerC state1 state1 = 1 := by',
              '  rw [state1_matches]; exact d36_normalized',
              'theorem orthogonal : SS.innerC state0 state1 = 0 := by',
              '  rw [state0_matches, state1_matches]; exact c36_orthogonal_d36',
              'end', 'end SSLPExplorerCase', '']
    roots = ['distance', 'normalized0', 'normalized1', 'orthogonal', 'logical0', 'logical1', 'physical_logical']
    lines += ['run_cmd do', '  let env ← Lean.getEnv',
              '  let roots : Array Lean.Name := #[' + ', '.join('`SSLPExplorerCase.' + x for x in roots) + ']',
              '  for root in roots do', '    if (env.checked.get.find? root).isNone then',
              '      throwError "Missing checked declaration: {root}"',
              '  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect',
              '  let (_, state) := (action.run env).run {}',
              '  for name in state.axioms do',
              '    unless #[`propext, `Classical.choice, `Quot.sound].contains name do',
              '      throwError "Unexpected axiom: {name}"',
              '  Lean.logInfo m!"SSLP_CASE_KERNEL_OK roots={roots.size} axioms={state.axioms}"', '']
    return '\n'.join(lines)
