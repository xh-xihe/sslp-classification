#!/usr/bin/env python3
"""Emit the directory-level orbit status census.

`WImageSettled62` proves the 51 empty images and the 11 exact nonempty ones,
but about *paper representatives* -- `SixQubit.OrbitNN.av` and its two residue
fibres.  Its own docstring says so:

    This file does not claim the still-separate generated-directory transport
    from the 66 canonical orbit representatives.

`thm:six-WE-status` is a statement about the 66 orbits, i.e. about the
directory keys, so that gap is the whole distance between the theorem and what
was proved.  The `Order*NoCompletion` modules close it for logical orders 4
through 9 and `OrderRange` for four more keys; this generator does the
remaining twenty-nine, all of logical order two or three, by exactly the same
route: identify the generated fibre pair with the paper orbit's two residue
fibres, transport along the stored cube action, and only then consult the
numeric paper-orbit table.

The result is `DirectoryOrbitStatus`: for every one of the 66 keys, either
`NoCompletion` (51 of them) or `HasCompletion` (11), or membership in the four
the paper leaves open.

Usage:  python tools/generators/emit_directory_orbit_status_lean.py
"""
import io
import os
import re

ROOT = os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASE = 'MainTheory.Generated.FiniteOrbitBase'
SHORT = ''  # names are used unqualified under `open MainTheory.Generated.FiniteOrbitBase`
OUT = os.path.join(ROOT, 'MainTheory', 'DirectoryOrbitStatus.lean')

# Paper orbits already transported to their directory key elsewhere.
ALREADY = {
    # key -> module namespace providing directoryKey<k>_{no,has}Completion
    24: 'OrderFourNoCompletion', 25: 'OrderFourNoCompletion',
    26: 'OrderFourNoCompletion', 27: 'OrderFourNoCompletion',
    28: 'OrderFourNoCompletion', 29: 'OrderFourNoCompletion',
    30: 'OrderFourNoCompletion', 31: 'OrderFourNoCompletion',
    61: 'OrderFourNoCompletion', 62: 'OrderFourNoCompletion',
    56: 'OrderSevenNoCompletion', 57: 'OrderSevenNoCompletion',
    58: 'OrderSevenNoCompletion', 59: 'OrderSevenNoCompletion',
    60: 'OrderSevenNoCompletion',
    52: 'OrderSixNoCompletion', 53: 'OrderSixNoCompletion',
    54: 'OrderSixNoCompletion', 55: 'OrderSixNoCompletion',
    63: 'OrderEightNoCompletion', 64: 'OrderEightNoCompletion',
    65: 'OrderNineNoCompletion',
}

# The eleven realized paper orbits: module holding `av`, the two residues, and
# a point of the image together with the theorem naming it.
REALIZED = {
    7: ('SixQubit.Orbit7Real', 0, 1, 'MainTheory.WImages.FI 1',
        'MainTheory.WImages.WImage_orbit7', 'image'),
    8: ('SixQubit.Orbit8Real', 0, 1, 'MainTheory.WImages.FI 1',
        'MainTheory.WImages.WImage_orbit8', 'image'),
    9: ('SixQubit.Orbit9Real', 0, 1, 'MainTheory.Levels.E2A',
        'MainTheory.WImages.WImage_orbit9', 'single'),
    10: ('SixQubit.Orbit10Real', 0, 2, 'MainTheory.Levels.E2A',
         'MainTheory.WImages.WImage_orbit10', 'single'),
    11: ('SixQubit.Orbit11Real', 0, 2, 'MainTheory.WImages.E1A',
         'MainTheory.WImages.WImage_orbit11', 'single'),
    16: ('SixQubit.Orbit16Real', 0, 2, 'MainTheory.Levels.E2A',
         'MainTheory.WImages.WImage_orbit16', 'single'),
    21: ('SixQubit.Orbit21Cert', 0, 2, 'MainTheory.Levels.E2A',
         'MainTheory.Levels.WImage_orbit21', 'single'),
    22: ('SixQubit.Orbit22Real', 0, 2, 'MainTheory.Levels.E2A',
         'MainTheory.WImages.WImage_orbit22', 'single'),
    23: ('SixQubit.Orbit23Real', 0, 2, 'MainTheory.WImages.E1A',
         'MainTheory.WImages.WImage_orbit23', 'single'),
    36: ('SixQubit.Orbit36Transport', 0, 1, 'MainTheory.WImages.R5A',
         'MainTheory.WImages.WImage_orbit36', 'single'),
    45: ('SixQubit.Orbit45Support', 0, 3, 'MainTheory.WImages.FII 1',
         'MainTheory.WImages.WImage_orbit45', 'image'),
}

# Keys already carrying a completion witness, and where it lives.
HAS_ALREADY = {
    34: 'MainTheory.OrderFiveUniqueCompletion.directoryKey34_hasCompletion',
    6: 'MainTheory.OrderRange.key06_hasCompletion',
    9: 'MainTheory.OrderRange.key09_hasCompletion',
    45: 'MainTheory.OrderRange.key45_hasCompletion',
}


def read(rel):
    return io.open(os.path.join(ROOT, rel), encoding='utf-8').read()


def tables():
    src = read('MainTheory/Generated/FiniteOrbitBase.lean')
    keys = {int(a): (int(q), int(m)) for a, q, m in re.findall(
        r'^def key(\d\d) : MainTheory\.FiniteOrbitPipeline\.OrbitKey := '
        r'⟨(\d+), (\d+),', src, re.M)}
    ids = [int(x) for x in re.findall(
        r'\d+', re.search(r'def paperOrbitId[^\n]*\n(.*?)\n\]',
                          src, re.S).group(1))]
    rep = [int(x) for x in re.findall(
        r'\d+', re.search(r'def representativeAt : Fin 66 . Fin 215 :=\s*!\['
                          r'(.*?)\n\]', src, re.S).group(1))]
    ng = read('MainTheory/WImageNoGo51.lean')
    nogo = {}
    for blk in ng.split('theorem WImage_orbit')[1:]:
        o = int(re.match(r'(\d+)_empty', blk).group(1))
        mo = re.search(r'MainTheory\.Levels\.WImage (SixQubit\.\w+)\.av\s+'
                       r'(\S+)\s+(\S+)\s*=\s*∅', blk.replace('\n', ' '))
        if mo:
            nogo[o] = (mo.group(1), mo.group(2), mo.group(3))
    return keys, ids, rep, nogo


def transport(k, q, m, o, i, av, r0, r1, kind, witness=None, thm=None,
              shape=None):
    """One key: fibres, mask identification, cube transport, conclusion."""
    out = [
        'def paper%dFibers : FiberPair 6' % o,
        '  | false => Finset.univ.filter fun x => SS.weight %s.av x = %s'
        % (av, r0),
        '  | true => Finset.univ.filter fun x => SS.weight %s.av x = %s'
        % (av, r1),
        '',
        'theorem input%03d_fibers_eq_paper%d :' % (i, o),
        '    fibersOfPair input%03d = paper%dFibers := by' % (i, o),
        '  funext c',
        '  cases c <;> decide',
        '',
        'theorem paper%d_equivalent_key%02d :' % (o, k),
        '    MainTheory.DistanceSignature.LabeledEquivalent',
        '      %d %d paper%dFibers %d %d key%02d.fibers := by'
        % (q, m, o, q, m, k),
        '  change MainTheory.DistanceSignature.LabeledEquivalent',
        '    input%03d.q input%03d.m paper%dFibers' % (i, i, o),
        '      key%02d.q key%02d.m key%02d.fibers' % (k, k, k),
        '  rw [← input%03d_fibers_eq_paper%d]' % (i, o),
        '  exact OrbitWitness.labeledEquivalent_of_validFor',
        '    MainTheory.Generated.FiniteOrbitWitnessShard%03d.witness_validFor'
        % i,
        '',
        'theorem keyAt%02d_eq : keyAt %d = key%02d := by decide' % (k, k, k),
        '',
    ]
    if kind == 'nogo':
        out += [
            'theorem paper%d_noCompletion : NoCompletion paper%dFibers := by'
            % (o, o),
            '  apply not_completion_of_WImage_empty %s.av %s %s paper%dFibers'
            % (av, r0, r1, o),
            '    rfl rfl',
            '  exact MainTheory.WImageNoGo51.WImage_orbit%d_empty' % o,
            '',
            'theorem directoryKey%02d_noCompletion :' % k,
            '    NoCompletion (keyAt %d).fibers := by' % k,
            '  rw [keyAt%02d_eq]' % k,
            '  exact not_completion_of_fiberEquivalent paper%d_noCompletion'
            % o,
            '    paper%d_equivalent_key%02d.2.2' % (o, k),
            '',
        ]
    else:
        member = ['  rw [%s]' % thm]
        member += (['  exact ⟨1, by norm_num, rfl⟩'] if shape == 'image'
                   else ['  rfl'])
        out += [
            'theorem paper%d_hasCompletion : HasCompletion paper%dFibers := by'
            % (o, o),
            '  apply completion_of_mem_WImage %s.av %s %s paper%dFibers rfl rfl'
            % (av, r0, r1, o),
            '    (A := %s)' % witness,
        ] + member + [
            '',
            'theorem directoryKey%02d_hasCompletion :' % k,
            '    HasCompletion (keyAt %d).fibers := by' % k,
            '  rw [keyAt%02d_eq]' % k,
            '  exact completion_of_fiberEquivalent paper%d_hasCompletion' % o,
            '    paper%d_equivalent_key%02d.2.2' % (o, k),
            '',
        ]
    return out


def main():
    keys, ids, rep, nogo = tables()
    covered_m = {4, 5, 6, 7, 8, 9}
    todo = [k for k in range(66)
            if k not in HAS_ALREADY and keys[k][1] not in covered_m
            and ids[k] > 4]
    shards = sorted(rep[k] for k in todo)
    lines = [
        'import MainTheory.OrderRange',
        'import MainTheory.WImageSettled62',
    ]
    lines += ['import MainTheory.Generated.FiniteOrbitWitnessShard%03d' % i
              for i in shards]
    lines += [
        '',
        '/-!',
        '# The completion status of all 66 directory keys',
        '',
        '`WImageSettled62` proves the 51 empty weight-enumerator images and',
        'the 11 exact nonempty ones, but about *paper representatives*: an',
        'angle vector `SixQubit.OrbitNN.av` and its two residue fibres.  Its',
        'own docstring records the gap --',
        '',
        '> This file does not claim the still-separate generated-directory',
        '> transport from the 66 canonical orbit representatives.',
        '',
        '-- and `thm:six-WE-status` is a statement about the 66 orbits, so',
        'that gap was the whole distance between the theorem and what was',
        'proved.  The `Order*NoCompletion` modules close it for logical orders',
        '4 through 9, `OrderRange` for four more keys, and this file for the',
        'remaining twenty-nine, all of logical order two or three.',
        '',
        'Every one is the same three steps: identify the generated fibre pair',
        'with the paper orbit\'s two residue fibres by an exact mask',
        'computation, transport the no-go (or the completion) along the',
        'stored, kernel-checked cube action, and only then consult the',
        'numeric paper-orbit table.',
        '',
        'The census at the end is `thm:six-WE-status` at the directory level:',
        '51 keys admit no exact normalized distance-three completion, 11 do,',
        'and the remaining four are exactly the paper\'s open orbits',
        '`W_1, W_2, W_3, W_4`.',
        '-/',
        '',
        'namespace MainTheory.DirectoryOrbitStatus',
        '',
        'open MainTheory.CubeAction',
        'open MainTheory.CubeCompletionTransport',
        'open MainTheory.FiniteOrbitPipeline',
        'open MainTheory.Generated.FiniteOrbitBase',
        '',
        'set_option maxRecDepth 100000',
        '',
    ]
    for k in todo:
        q, m = keys[k]
        o = ids[k]
        i = rep[k]
        if o in REALIZED:
            av, r0, r1, w, thm, shape = REALIZED[o]
            lines += transport(k, q, m, o, i, av, r0, r1, 'realized',
                               witness=w, thm=thm, shape=shape)
        else:
            av, r0, r1 = nogo[o]
            lines += transport(k, q, m, o, i, av, r0, r1, 'nogo')

    nogo_keys = sorted([k for k in range(66)
                        if ids[k] > 4 and ids[k] not in REALIZED])
    has_keys = sorted([k for k in range(66) if ids[k] in REALIZED])
    open_keys = sorted([k for k in range(66) if ids[k] <= 4])

    def ref_no(k):
        if k in ALREADY:
            return 'MainTheory.%s.directoryKey%02d_noCompletion' % (
                ALREADY[k], k)
        if keys[k][1] == 5:
            return ('MainTheory.OrderFiveUniqueCompletion'
                    '.directoryKey%02d_noCompletion' % k)
        return 'directoryKey%02d_noCompletion' % k

    def ref_has(k):
        return HAS_ALREADY.get(k, 'directoryKey%02d_hasCompletion' % k)

    lines += [
        '/-! ## The census -/',
        '',
        '/-- The 51 keys the no-go analysis rules out. -/',
        'def noGoKeys : List (Fin 66) := [%s]'
        % ', '.join(str(k) for k in nogo_keys),
        '',
        '/-- The 11 keys an exact code realizes. -/',
        'def realizedKeys : List (Fin 66) := [%s]'
        % ', '.join(str(k) for k in has_keys),
        '',
        '/-- The four keys `main.tex` leaves open: `W_1` through `W_4`. -/',
        'def openKeys : List (Fin 66) := [%s]'
        % ', '.join(str(k) for k in open_keys),
        '',
        'theorem noGoKeys_length : noGoKeys.length = 51 := by decide',
        'theorem realizedKeys_length : realizedKeys.length = 11 := by decide',
        'theorem openKeys_length : openKeys.length = 4 := by decide',
        '',
        '/-- The three lists partition the sixty-six keys. -/',
        'theorem keys_partition :',
        '    (noGoKeys ++ realizedKeys ++ openKeys).toFinset ='
        ' (Finset.univ : Finset (Fin 66)) := by decide',
        '',
        'theorem keys_nodup : (noGoKeys ++ realizedKeys ++ openKeys).Nodup :='
        ' by decide',
        '',
        '/-- The open keys are exactly the paper\'s orbits 1, 2, 3 and 4. -/',
        'theorem openKeys_paperIds :',
        '    openKeys.map paperOrbitId = [1, 2, 3, 4] := by decide',
        '',
        '/-! The three lists are read off the generated paper-orbit table,',
        'so they are cross-checked against the paper-facing lists in',
        '`WImageNoGo51` and `WImageSettled62` rather than trusted.  Without',
        'this a transcription slip in that table would silently move a key',
        'from one census column to another. -/',
        '',
        'theorem noGoKeys_paperIds :',
        '    (noGoKeys.map paperOrbitId).toFinset =',
        '      MainTheory.WImageNoGo51.noGoOrbitIds.toFinset := by decide',
        '',
        'theorem realizedKeys_paperIds :',
        '    (realizedKeys.map paperOrbitId).toFinset =',
        '      MainTheory.WImageSettled62.realizedOrbitIds.toFinset := by'
        ' decide',
        '',
        'theorem openKeys_paperIds_eq :',
        '    (openKeys.map paperOrbitId).toFinset =',
        '      MainTheory.WImageSettled62.openOrbitIds.toFinset := by decide',
        '',
        '/-- **No key on the no-go list admits an exact normalized',
        'distance-three completion.** -/',
        'theorem noCompletion_of_mem_noGoKeys (k : Fin 66)'
        ' (h : k ∈ noGoKeys) :',
        '    NoCompletion (keyAt k).fibers := by',
        '  fin_cases k',
    ]
    for k in range(66):
        if k in nogo_keys:
            lines.append('  · exact %s' % ref_no(k))
        else:
            lines.append('  · exact absurd h (by decide)')
    lines += [
        '',
        '/-- **Every key on the realized list is realized by an actual exact',
        'code.** -/',
        'theorem hasCompletion_of_mem_realizedKeys (k : Fin 66)'
        ' (h : k ∈ realizedKeys) :',
        '    HasCompletion (keyAt k).fibers := by',
        '  fin_cases k',
    ]
    for k in range(66):
        if k in has_keys:
            lines.append('  · exact %s' % ref_has(k))
        else:
            lines.append('  · exact absurd h (by decide)')
    lines += [
        '',
        '/-- **`thm:six-WE-status` at the directory level.**  Every key is',
        'settled one way or the other except the four the paper boxes as',
        'open. -/',
        'theorem settled_or_open (k : Fin 66) :',
        '    NoCompletion (keyAt k).fibers ∨',
        '      HasCompletion (keyAt k).fibers ∨ k ∈ openKeys := by',
        '  by_cases hn : k ∈ noGoKeys',
        '  · exact Or.inl (noCompletion_of_mem_noGoKeys k hn)',
        '  by_cases hr : k ∈ realizedKeys',
        '  · exact Or.inr (Or.inl (hasCompletion_of_mem_realizedKeys k hr))',
        '  refine Or.inr (Or.inr ?_)',
        '  revert hn hr',
        '  revert k',
        '  decide',
        '',
        'end MainTheory.DirectoryOrbitStatus',
        '',
    ]
    io.open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
    print('wrote', os.path.relpath(OUT, ROOT),
          '(%d new transports)' % len(todo))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
