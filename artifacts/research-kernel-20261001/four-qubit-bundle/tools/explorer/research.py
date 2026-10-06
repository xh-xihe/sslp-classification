"""Bounded explicit-code input, exact diagnostics, and input-derived Lean proofs.

No paper/canonical code equality is required. Only validated integers enter Lean.
"""
from . import class36

SCHEMA = 'sslp.research-code.v1'
TARGET = 'SS.ExactCode'
ROOT_COUNT = 3
SCOPE = ('supplied codewords: normalization, orthogonality, requested Pauli-distance lower bound; '
         'supplied diagonal physical phase layer on every logical superposition, assuming zeta^q=1; '
         'K=1 is a rank-one KL statement, not nontrivial logical information')


def validate(data):
    fields = {'schema', 'n', 'k', 'distance', 'denominator', 'q', 'angles', 'words'}
    if not isinstance(data, dict) or set(data) != fields or data.get('schema') != SCHEMA:
        raise ValueError('expected sslp.research-code.v1 with exactly the documented input fields')
    def integer(name, low, high):
        if not class36.integer(data[name], low, high):
            raise ValueError(f'{name} must be an integer from {low} to {high}')
        return data[name]
    n = integer('n', 1, 6)
    k = integer('k', 1, min(4, 2**n))
    integer('distance', 1, min(3, n + 1))
    integer('denominator', 1, 1_000_000)
    q = integer('q', 2, 64)
    if not isinstance(data['angles'], list) or len(data['angles']) != n or not all(
            class36.integer(a, 0, q - 1) for a in data['angles']):
        raise ValueError('angles require n integer exponents in [0,q-1]')
    if not isinstance(data['words'], list) or len(data['words']) != k:
        raise ValueError('expected K logical words')
    words = []
    for entries in data['words']:
        if not isinstance(entries, list) or not 1 <= len(entries) <= 2**n:
            raise ValueError('each word needs 1 to 2^n support entries')
        word = {}
        for row in entries:
            if not isinstance(row, dict) or set(row) != {'bits', 'coordinates'}:
                raise ValueError('an amplitude entry requires bits and coordinates')
            bits, coords = row['bits'], row['coordinates']
            if not isinstance(bits, str) or len(bits) != n or set(bits) - {'0', '1'}:
                raise ValueError('basis string must contain exactly n bits')
            mask = sum((1 << i) for i, bit in enumerate(bits) if bit == '1')
            if mask in word:
                raise ValueError('duplicate basis string')
            if not isinstance(coords, list) or len(coords) != 8 or not all(
                    class36.integer(c, -1_000_000, 1_000_000) for c in coords):
                raise ValueError('each amplitude requires eight bounded integer coordinates')
            word[mask] = tuple(coords)
        words.append(word)
    return words


def fibers(data, words):
    return [sorted({sum(a for i, a in enumerate(data['angles']) if mask & (1 << i)) % data['q']
                    for mask, coords in word.items() if any(coords)}) for word in words]


def exact_checks(data):
    words = validate(data)
    g, rows = class36.arithmetic, []
    for x in range(2**data['n']):
        for z in range(2**data['n']):
            if (x | z).bit_count() >= data['distance']:
                continue
            phase = (1, 0, 0, 0, 0, 0, 0, 0)
            for _ in range((x & z).bit_count()):
                phase = g.zmul(phase, (0, 0, 0, 0, 1, 0, 0, 0))
            matrix = [[g.zmul(phase, g.matelt(a, b, sorted(b), x, z)) for b in words] for a in words]
            passed = all(cell == (matrix[0][0] if j == k else g.ZERO)
                         for j, line in enumerate(matrix) for k, cell in enumerate(line))
            label = ''.join(('Y' if z & (1 << i) else 'X') + str(i + 1) if x & (1 << i)
                            else 'Z' + str(i + 1) if z & (1 << i) else '' for i in range(data['n'])) or 'I'
            rows.append({'x_mask': x, 'z_mask': z, 'pauli': label, 'matrix_coordinates': matrix,
                         'matrix_denominator': data['denominator'], 'passed': passed})
    target = (data['denominator'],) + (0,) * 7
    normalized = all(cell == (target if j == k else g.ZERO)
                     for j, line in enumerate(rows[0]['matrix_coordinates']) for k, cell in enumerate(line))
    residues = fibers(data, words)
    gate_ok = all(len(r) == 1 for r in residues)
    return {'schema': 'sslp.exact-check.v1', 'input_sha256': class36.digest(data),
            'method': 'exact integer arithmetic in Z[sqrt(2),sqrt(3),i]',
            'scope': f"supplied input only; target distance at least {data['distance']}",
            'kernel_status': 'not_run', 'n': data['n'], 'k': data['k'], 'target_distance': data['distance'],
            'passed': normalized and gate_ok and all(row['passed'] for row in rows),
            'normalization_and_orthogonality': normalized, 'support_matches_gate': gate_ok,
            'pauli_count': len(rows), 'kl': rows, 'support_residues': residues,
            'logical_residues': [r[0] if len(r) == 1 else None for r in residues]}


def lean_certificate(data):
    words = validate(data)
    n, k, d, D, q = (data[key] for key in ('n', 'k', 'distance', 'denominator', 'q'))
    def literal(value):
        return str(value) if value >= 0 else f'({value})'
    lines = ['import SS.ExactCode', 'import Lean.Util.CollectAxioms',
             'set_option maxRecDepth 40000', 'set_option maxHeartbeats 8000000',
             'namespace SSLPResearchCase', 'open SS.ExactAmplitude SS.ExactCode',
             'open scoped BigOperators',
             f'def num (s : SS.BitString {n}) : Nat := ∑ i, if s i then 2 ^ i.val else 0',
             f'def nbit (m : Nat) : SS.BitString {n} := fun i => Nat.testBit m i.val',
             f'theorem num_lt : ∀ s, num s < {2**n} := by decide',
             'theorem nbit_num : ∀ s, nbit (num s) = s := by decide']
    for j, word in enumerate(words):
        entries = [f"if num s = {m} then z8 {' '.join(literal(c) for c in coords)}" for m, coords in sorted(word.items())]
        lines += [f'def c{j} (s : SS.BitString {n}) : ZQ := ' + ' else '.join(entries) + ' else ZQ.zero',
                  f'def L{j} : List (SS.BitString {n}) := [' + ', '.join(f'nbit {m}' for m in sorted(word)) + ']']
    lines += [f'def coeff : Fin {k} → SS.BitString {n} → ZQ := ![' + ', '.join(f'c{j}' for j in range(k)) + ']',
              f'def supports : Fin {k} → List (SS.BitString {n}) := ![' + ', '.join(f'L{j}' for j in range(k)) + ']',
              'theorem support_nodup : ∀ j, (supports j).Nodup := by decide',
              'theorem vanishes : ∀ j s, s ∉ supports j → coeff j s = ZQ.zero := by decide',
              'theorem gram_check : ∀ j k, zmat (coeff j) (coeff k) (supports k) (fun _ => false) (fun _ => false) =',
              f'    if j = k then z8 {D} 0 0 0 0 0 0 0 else ZQ.zero := by decide',
              f'theorem finite_kl : ∀ m < {2**n}, ∀ z < {2**n},',
              f'    (⟨nbit m, nbit z⟩ : SS.PauliString {n}).wt ≤ {d-1} → ∀ j k,',
              '    zmat (coeff j) (coeff k) (supports k) (nbit m) (nbit z) =',
              '      if j = k then zmat (coeff 0) (coeff 0) (supports 0) (nbit m) (nbit z) else ZQ.zero := by decide',
              'noncomputable section',
              f'def states : Fin {k} → SS.State {n} ℂ := fun j => stC (scale {D}) (coeff j)',
              'theorem orthonormal : ∀ j k, SS.innerC (states j) (states k) = if j = k then 1 else 0 :=',
              f'  orthonormal_of_checks {D} (by decide) coeff supports support_nodup vanishes gram_check',
              f'theorem distance : SS.HasDistance states {d} := by',
              f'  apply distance_of_checks (scale {D}) coeff supports 0 {d} support_nodup vanishes',
              '  intro P hw j k',
              '  have hx := nbit_num P.x', '  have hz := nbit_num P.z',
              '  have h := finite_kl (num P.x) (num_lt _) (num P.z) (num_lt _) (by rw [hx, hz]; exact hw) j k',
              '  rwa [hx, hz] at h', 'end']
    # If the support test fails, Lean independently refuses fiber_check.
    residues = [r[0] if r else 0 for r in fibers(data, words)]
    lines += [f'def angles : Fin {n} → Nat := ![' + ', '.join(map(str, data['angles'])) + ']',
              f'def residues : Fin {k} → Nat := ![' + ', '.join(map(str, residues)) + ']',
              f'theorem fiber_check : ∀ j s, coeff j s ≠ ZQ.zero → exponent angles s % {q} = residues j := by decide',
              f'theorem gate_action (zeta : ℂ) (hz : zeta ^ {q} = 1) (alpha : Fin {k} → ℂ) :',
              f'    physicalGate zeta angles (encode (scale {D}) coeff alpha) =',
              f'      encode (scale {D}) coeff (fun j => zeta ^ residues j * alpha j) :=',
              f'  physical_logical zeta {q} hz angles residues (scale {D}) coeff fiber_check alpha',
              'end SSLPResearchCase', 'run_cmd do', '  let env ← Lean.getEnv',
              '  let roots : Array Lean.Name := #[`SSLPResearchCase.orthonormal, `SSLPResearchCase.distance, `SSLPResearchCase.gate_action]',
              '  for root in roots do', '    if (env.checked.get.find? root).isNone then',
              '      throwError "Missing checked declaration: {root}"',
              '  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect',
              '  let (_, state) := (action.run env).run {}',
              '  for name in state.axioms do',
              '    unless #[`propext, `Classical.choice, `Quot.sound].contains name do',
              '      throwError "Unexpected axiom: {name}"',
              '  Lean.logInfo m!"SSLP_CASE_KERNEL_OK roots={roots.size} axioms={state.axioms}"', '']
    return '\n'.join(lines)
