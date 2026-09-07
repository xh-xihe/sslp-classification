"""Exact candidate generation for L([0,1]) in the four open moment orbits.

Start with the five-qubit perfect-code stabilizers.  Append an ancilla in
C|0> psi + S|1> Z_0 psi.  Logical Pauli representatives, followed by local
Cliffords, put this family in parity fibers of weights 3,4,5,6.
All Gaussian arithmetic below is integral; independent Lean coefficient
certificates, not this generator, must establish the resulting statements.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/generators'))
from genreal import ZERO, zadd, zneg, zconj, zmul


def write_source(path, text):
    if path.exists() and path.read_text(encoding='utf-8') == text:
        return
    path.write_text(text, encoding='utf-8')


def write_manifest():
    directory = ROOT/'SixQubit/Generated/OpenLFamilies'
    order = []
    for orbit in range(1,5):
        order += [f'Orbit{orbit}Data', *(f'Orbit{orbit}Check{i}' for i in range(8)),
                  f'Orbit{orbit}']
    expected = {leaf+'.lean' for leaf in order}
    actual = {path.name for path in directory.glob('*.lean')}
    if actual != expected:
        raise ValueError('Generated Lean file coverage differs from the forty expected modules')
    modules = ['SixQubit.Generated.OpenLFamilies.'+leaf for leaf in order]
    manifest = ['# lean_files='+str(len(order))]
    manifest += [hashlib.sha256((directory/(leaf+'.lean')).read_bytes()).hexdigest()+'  '+module
                 for leaf,module in zip(order,modules)]
    write_source(directory/'serial-build-order.txt','\n'.join(modules)+'\n')
    write_source(directory/'generation-manifest.sha256','\n'.join(manifest)+'\n')


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def neg(a):
    return (-a[0], -a[1])


def itimes(a, k):
    for _ in range(k % 4):
        a = (-a[1], a[0])
    return a


def pauli(a, x, z):
    return [itimes(a[y ^ x], (x & z).bit_count() +
                   2*((z & (y ^ x)).bit_count() % 2)) for y in range(len(a))]


def masks(word):
    return (sum(1 << j for j, p in enumerate(word) if p in 'XY'),
            sum(1 << j for j, p in enumerate(word) if p in 'ZY'))


def perfect_code():
    c = [(1, 0)] + [(0, 0)]*31
    for word in ('XZZXI', 'IXZZX', 'XIXZZ', 'ZXIXZ'):
        moved = pauli(c, *masks(word))
        c = [add(a, b) for a, b in zip(c, moved)]
    assert sum(a*a+b*b for a, b in c) == 16
    return [c, pauli(c, 31, 0)]


def hadamard(a, j):
    return [add(a[y & ~(1 << j)], neg(a[y | (1 << j)])) if y & (1 << j)
            else add(a[y & ~(1 << j)], a[y | (1 << j)]) for y in range(64)]


def local_diagonalize(a, x, z):
    for j in range(6):
        if (x >> j) & 1:
            if (z >> j) & 1:
                a = [itimes(v, -1) if (y >> j) & 1 else v for y, v in enumerate(a)]
            a = hadamard(a, j)
    return a


def coefficient(a, sqrt_two):
    out = [0]*8
    out[1 if sqrt_two else 0] = a[0]
    out[5 if sqrt_two else 4] = a[1]
    return tuple(out)


def make_family(weight):
    base = perfect_code()
    candidate = None
    for x in range(32):
        for z in range(32):
            anticommutes = x & 1
            if (x | z).bit_count() + anticommutes != weight:
                continue
            moved = [pauli(a, x, z) for a in base]
            if moved in ([base[0], [neg(v) for v in base[1]]],
                         [[neg(v) for v in base[0]],base[1]]):
                candidate = (x, z, False)
                break
            if moved in ([base[1], base[0]],
                         [[neg(v) for v in base[1]],[neg(v) for v in base[0]]]):
                candidate = (x, z, True)
                break
        if candidate:
            break
    if candidate is None:
        raise ValueError('No logical representative of weight ' + str(weight))
    x, z, logical_h = candidate
    if logical_h:
        base = [[add(a,b) for a,b in zip(*base)], [add(a,neg(b)) for a,b in zip(*base)]]
    px, pz = x << 1, (z << 1) | (x & 1)
    tables = []
    for a in base:
        c = [a[y >> 1] if y % 2 == 0 else (0,0) for y in range(64)]
        s = [(neg(a[y >> 1]) if y & 2 else a[y >> 1]) if y % 2 else (0,0)
             for y in range(64)]
        tables.append([local_diagonalize(c, px, pz), local_diagonalize(s, px, pz)])
    active = [j for j in range(6) if ((px | pz) >> j) & 1]
    inactive = [j for j in range(6) if j not in active]
    sigma = inactive + active
    def unpermute(y):
        return sum(((y >> j) & 1) << old for j, old in enumerate(sigma))
    powers = px.bit_count() + int(logical_h)
    denominator = 4 * 2**((powers + 1)//2)
    tables = [[[coefficient(a[unpermute(y)], powers % 2) for y in range(64)]
               for a in pair] for pair in tables]
    parity = sum(1 << j for j in range(6-weight,6))
    def parity_of(pair):
        return {(y & parity).bit_count()%2 for a in pair for y,v in enumerate(a) if v != ZERO}
    if parity_of(tables[0]) == {1}:
        tables.reverse()
    assert parity_of(tables[0]) == {0} and parity_of(tables[1]) == {1}
    return dict(weight=weight, denominator=denominator, tables=tables,
                original_logical_masks=[x,z], logical_h=logical_h, sigma=sigma)


def qmat(a,b,x,z):
    result = [ZERO,ZERO,ZERO]
    for y in range(64):
        ac, ass = a[0][y^x], a[1][y^x]
        bc, bs = b[0][y], b[1][y]
        terms = [zmul(zconj(ac),bc),
                 zadd(zmul(zconj(ac),bs),zmul(zconj(ass),bc)), zmul(zconj(ass),bs)]
        if (y&z).bit_count()%2:
            terms = [zneg(v) for v in terms]
        result = [zadd(v,w) for v,w in zip(result,terms)]
    return result


def check_family(family):
    a,b = family['tables']
    size = family['denominator']**2
    scalar = lambda value: (value,0,0,0,0,0,0,0)
    for word in (a,b):
        assert qmat(word,word,0,0) == [scalar(size),ZERO,scalar(size)]
    traces = []
    for x in range(64):
        for z in range(64):
            wt = (x|z).bit_count()
            if wt > 2:
                continue
            aa,bb = qmat(a,a,x,z),qmat(b,b,x,z)
            assert aa == bb, (family['weight'], 'unequal diagonals', x,z)
            assert qmat(a,b,x,z) == [ZERO]*3, (family['weight'],'off diagonal',x,z)
            trace = [zadd(v,w) for v,w in zip(aa,bb)]
            if wt and trace != [ZERO]*3:
                traces.append(dict(x=x,z=z,weight=wt,coefficients=trace))
    assert sorted(row['weight'] for row in traces) == [1,2], traces
    family['low_traces'] = traces
    return family


def lean_int(value):
    return str(value) if value >= 0 else '('+str(value)+')'


def lean_zq(value):
    if tuple(value) == ZERO:
        return 'ZQ.zero'
    return '(z8 '+' '.join(lean_int(x) for x in value)+')'


def lean_table(word):
    """A six-level Boolean trie avoids repeated 32-entry numeric scans."""
    leaves = ['⟨ZQ.zero, '+lean_zq(word[0][y])+', '+lean_zq(word[1][y])+'⟩'
              for y in range(64)]
    def branch(bit, values):
        if all(value == values[0] for value in values):
            return values[0]
        low = branch(bit+1, values[::2])
        high = branch(bit+1, values[1::2])
        return f'(if x {bit} then {high} else {low})'
    return branch(0, leaves)


def emit_lean(family):
    orbit = family['weight']-2
    namespace = f'SixQubit.OpenLOrbit{orbit}'
    lines = ['import SixQubit.ParityCircleFamily', '',
             '/- Exact generated amplitude candidate; every certificate field is kernel checked. -/',
             'namespace '+namespace, '',
             'open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily', '',
             'set_option maxHeartbeats 20000000', 'set_option maxRecDepth 100000', '',
             'def angle : Fin 6 → ZMod 2 := !['+
             ', '.join(['0']*(6-family['weight'])+['1']*family['weight'])+']', '']
    for i, word in enumerate(family['tables']):
        support = [y for y in range(64) if word[0][y] != ZERO or word[1][y] != ZERO]
        lines += [f'def L{i} : List (SS.BitString 6) :=',
                  '  ['+', '.join('nbit '+str(y) for y in support)+']', '',
                  f'def c{i} (x : SS.BitString 6) : LinZ :=']
        lines += ['  '+lean_table(word), '']
    for name,row in zip(('onePauli','twoPauli'),sorted(family['low_traces'],key=lambda row:row['weight'])):
        lines += [f'def {name} : SS.PauliString 6 := ⟨nbit {row["x"]}, nbit {row["z"]}⟩']
    lines += ['',
      'def klCheck (P : SS.PauliString 6) : Prop :=',
      '  CircleZero (QuadZ.sub (qmat c0 c0 L0 P.x P.z) (qmat c1 c1 L1 P.x P.z)) ∧',
      '    CircleZero (qmat c0 c1 L1 P.x P.z) ∧ CircleZero (qmat c1 c0 L0 P.x P.z)',
      '', 'instance (P : SS.PauliString 6) : Decidable (klCheck P) := by',
      '  unfold klCheck', '  infer_instance', '',
      'def sameMasks (P Q : SS.PauliString 6) : Prop :=',
      '  num P.x = num Q.x ∧ num P.z = num Q.z', '',
      'instance (P Q : SS.PauliString 6) : Decidable (sameMasks P Q) := by',
      '  unfold sameMasks', '  infer_instance', '',
      'theorem sameMasks_eq {P Q : SS.PauliString 6} (h : sameMasks P Q) : P = Q := by',
      '  have hx : P.x = Q.x := by simpa only [nbit_num] using congrArg nbit h.1',
      '  have hz : P.z = Q.z := by simpa only [nbit_num] using congrArg nbit h.2',
      '  cases P; cases Q; cases hx; cases hz; rfl', '',
      'def sparseCheck (P : SS.PauliString 6) : Prop :=',
      '  P.wt ≤ 2 → ¬ sameMasks P identityPauli → ¬ sameMasks P onePauli →',
      '    ¬ sameMasks P twoPauli →',
      '    CircleZero (qtrace c0 c1 L0 L1 P)', '',
      'instance (P : SS.PauliString 6) : Decidable (sparseCheck P) := by',
      '  unfold sparseCheck', '  infer_instance', '',
      'theorem kl_masks : ∀ m < 64, ∀ k < 64,',
      '    (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 →',
      '      klCheck ⟨nbit m, nbit k⟩ := by decide', '',
      'theorem kl_all (P : SS.PauliString 6) (hP : P.wt ≤ 2) : klCheck P := by',
      '  have hp : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by',
      '    cases P; simp only [nbit_num]',
      '  have h := kl_masks (num P.x) (num_lt _) (num P.z) (num_lt _)',
      '  rw [hp] at h', '  exact h hP', '',
      'theorem sparse_masks : ∀ m < 64, ∀ k < 64,',
      '    sparseCheck ⟨nbit m, nbit k⟩ := by decide', '',
      'theorem sparse_all (P : SS.PauliString 6) (hP : P.wt ≤ 2)',
      '    (hi : P ≠ identityPauli) (h1 : P ≠ onePauli) (h2 : P ≠ twoPauli) :',
      '    CircleZero (qtrace c0 c1 L0 L1 P) := by',
      '  have hp : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by',
      '    cases P; simp only [nbit_num]',
      '  have h := sparse_masks (num P.x) (num_lt _) (num P.z) (num_lt _)',
      '  dsimp only at h', '  rw [hp] at h', '  exact h hP hi h1 h2', '',
      'def certificate : Certificate where', '  angle := angle', '  c0 := c0', '  c1 := c1',
      '  L0 := L0', '  L1 := L1', f'  denominator := {family["denominator"]}',
      '  denominator_pos := by decide', '  L0_nodup := by decide', '  L1_nodup := by decide',
      '  vanishes0 := by decide', '  vanishes1 := by decide',
      '  fiber0 := by decide', '  fiber1 := by decide', '  kl := kl_all',
      '  norm0 := by decide', '  norm1 := by decide', '  onePauli := onePauli',
      '  twoPauli := twoPauli', '  oneWeight := by decide', '  twoWeight := by decide',
      '  oneNumY := by decide', '  twoNumY := by decide',
      '  trace1 := by decide', '  trace2 := by decide', '  sparse := sparse_all', '',
      'end '+namespace, '']
    directory = ROOT / 'SixQubit/Generated/OpenLFamilies'
    directory.mkdir(parents=True,exist_ok=True)
    kl_start = next(i for i,line in enumerate(lines) if line.startswith('theorem kl_masks'))
    kl_end = next(i for i,line in enumerate(lines) if line.startswith('theorem kl_all'))
    sparse_start = next(i for i,line in enumerate(lines) if line.startswith('theorem sparse_masks'))
    sparse_end = next(i for i,line in enumerate(lines) if line.startswith('theorem sparse_all'))
    certificate_start = lines.index('def certificate : Certificate where')
    write_source(directory/f'Orbit{orbit}Data.lean',
        '\n'.join(lines[:kl_start]+['end '+namespace,'']))
    header = ['namespace '+namespace,'',
              'open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily','',
              'set_option maxHeartbeats 20000000','set_option maxRecDepth 100000','']
    for block in range(8):
        theorem_lines = []
        for sparse in (False, True):
            stem = 'sparse_masks' if sparse else 'kl_masks'
            for offset in range(8):
                mask = 8*block+offset
                proposition = (f'sparseCheck ⟨nbit {mask}, nbit k⟩' if sparse else
                    f'(⟨nbit {mask}, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → '+
                    f'klCheck ⟨nbit {mask}, nbit k⟩')
                theorem_lines += [f'theorem {stem}_fixed_{mask} : ∀ k < 64,',
                                  '    '+proposition+' := by decide', '']
            proposition = (f'sparseCheck ⟨nbit (8*{block}+m), nbit k⟩' if sparse else
                f'(⟨nbit (8*{block}+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → '+
                f'klCheck ⟨nbit (8*{block}+m), nbit k⟩')
            theorem_lines += [f'theorem {stem}_{block} : ∀ m < 8, ∀ k < 64,',
                              '    '+proposition+' := by',
                              '  intro m hm', '  interval_cases m']
            for offset in range(8):
                theorem_lines += [f'  · exact {stem}_fixed_{8*block+offset}']
            theorem_lines += ['']
        content = [f'import SixQubit.Generated.OpenLFamilies.Orbit{orbit}Data','']+header+\
            theorem_lines+['end '+namespace,'']
        write_source(directory/f'Orbit{orbit}Check{block}.lean','\n'.join(content))
    wrapper = [f'import SixQubit.Generated.OpenLFamilies.Orbit{orbit}Check{block}' for block in range(8)]
    wrapper += ['']+header
    for sparse in (False,True):
        if sparse:
            wrapper += ['theorem sparse_all (P : SS.PauliString 6) (hP : P.wt ≤ 2)',
                        '    (hi : P ≠ identityPauli) (h1 : P ≠ onePauli) (h2 : P ≠ twoPauli) :',
                        '    CircleZero (qtrace c0 c1 L0 L1 P) := by']
        else:
            wrapper += ['theorem kl_all (P : SS.PauliString 6) (hP : P.wt ≤ 2) : klCheck P := by']
        wrapper += ['  have hb := num_lt P.x',
                    '  have hcases : '+' ∨ '.join(f'num P.x / 8 = {block}' for block in range(8))+' := by omega',
                    '  rcases hcases with '+' | '.join(['h']*8)]
        for block in range(8):
            theorem = ('sparse_masks_' if sparse else 'kl_masks_')+str(block)
            wrapper += [f'  · have he : 8*{block} + num P.x % 8 = num P.x := by omega',
                        f'    have hp : (⟨nbit (8*{block}+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by',
                        '      rw [he, nbit_num, nbit_num]',
                        f'    have hg := {theorem} (num P.x%8) (Nat.mod_lt _ (by decide))',
                        '      (num P.z) (num_lt _)']
            wrapper += ['    rw [hp] at hg','    exact hg hP'+
                        (' (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h))'+
                         ' (fun h => h2 (sameMasks_eq h))' if sparse else '')]
        wrapper += ['']
    wrapper += lines[certificate_start:]
    target = directory/f'Orbit{orbit}.lean'
    write_source(target,'\n'.join(wrapper))
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'tmp/open-l-family-candidates.json')
    parser.add_argument('--emit-lean', action='store_true')
    parser.add_argument('--manifest-only', action='store_true')
    args = parser.parse_args()
    if args.manifest_only:
        write_manifest()
        return
    families = [check_family(make_family(weight)) for weight in (3,4,5,6)]
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(families,indent=2)+'\n',encoding='utf-8')
    for family in families:
        print('weight',family['weight'],'denominator',family['denominator'],
              'logical',family['original_logical_masks'],
              'low traces',[(r['x'],r['z']) for r in family['low_traces']])
        if args.emit_lean:
            print('Wrote',emit_lean(family).relative_to(ROOT))
    if args.emit_lean:
        write_manifest()
    print('Exact candidates checked; Lean kernel certificates are still required.')


if __name__ == '__main__':
    main()
