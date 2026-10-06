#!/usr/bin/env python3
"""Regenerate orbit traces and spectra in a separate directory and compare bytes."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/generators'))
sys.path.insert(0, str(ROOT / 'tools'))
from lean_source import imports


def write_collected_manifest():
    directory = ROOT / 'SixQubit/Generated/Orbit3CollectedRows'
    paths = {f'SixQubit.Generated.Orbit3CollectedRows.{p.stem}': p for p in directory.glob('*.lean')}
    ordered, active = [], set()
    def visit(name):
        if name in ordered:
            return
        if name in active:
            raise ValueError('Generated import cycle')
        active.add(name)
        for dep in imports(paths[name].read_text(encoding='utf8')):
            if dep in paths:
                visit(dep)
        active.remove(name)
        ordered.append(name)
    for name in sorted(paths):
        visit(name)
    (directory / 'generation-manifest.sha256').write_text('# lean_files=' + str(len(paths)) + '\n' + ''.join(
        hashlib.sha256(paths[name].read_bytes()).hexdigest() + '  ' + name + '\n' for name in ordered), encoding='utf8')
    (directory / 'serial-build-order.txt').write_text('\n'.join(ordered) + '\n', encoding='utf8')


def main():
    import emit_orbit3_collected_rows as collected
    import emit_orbit3_row_trace as traces
    import emit_orbit3_spin_rows as spin
    import emit_orbit3_hadamard_rows as hadamard
    import emit_orbit3_target_traces as target
    import emit_orbit2_spectra as spectra
    import emit_orbit2_physical_spectra as physical_spectra
    temp = ROOT / 'tmp/orbit-final-source-regeneration'
    temp.mkdir(exist_ok=True)
    rows = temp / 'Orbit3CollectedRows'
    rows.mkdir(exist_ok=True)
    collected.generate(rows / 'Data.lean')
    traces.generate(0, rows / 'Trace000.lean', rows / 'Trace000Checks.lean')
    traces.generate_step_probe(0, 0, rows / 'Trace000Step00.lean')
    traces.generate_all(rows, temp / 'Orbit3CollectedKLRows.lean')
    spin.generate(rows)
    spin.generate_aggregate(temp / 'Orbit3CollectedSpinRows.lean')
    hadamard.generate(rows)
    hadamard.generate_aggregate(temp / 'Orbit3CollectedHadamardRows.lean')
    target.generate(temp / 'Orbit3TargetTraces', temp / 'Orbit3TargetData.lean', temp / 'Orbit3CollectedTarget.lean')
    spectra.generate(ROOT / 'results/orbit2-kernel/gram-blocks.json', temp / 'Orbit2Spectra')
    physical_spectra.generate(temp / 'Orbit2PhysicalSpectra.lean')
    records = []
    for candidate in sorted(temp.rglob('*.lean')):
        path = ROOT / 'SixQubit/Generated' / candidate.relative_to(temp)
        if not path.exists() or path.read_bytes() != candidate.read_bytes():
            raise ValueError('Generated source differs: ' + str(path.relative_to(ROOT)))
        records.append({'path': path.relative_to(ROOT).as_posix(),
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    import subprocess
    for generator, relative in (
        ('generate_orbit45_printed_walsh.py', 'MainTheory/Orbit45PrintedWalsh.lean'),
        ('generate_orbit45_printed_moments.py', 'MainTheory/Orbit45PrintedMoments.lean'),
        ('generate_orbit2_remaining_coordinates.py', 'MainTheory/Orbit2RemainingCoordinates.lean'),
    ):
        subprocess.run([sys.executable, str(ROOT / 'tools/verification' / generator), '--check'],
                       cwd=ROOT,check=True)
        path=ROOT/relative
        records.append({'path': relative,'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    evidence = ROOT / 'artifacts/orbit-certification-20261003/final-generated-source-regeneration.json'
    evidence.write_text(json.dumps({'status': 'PASS', 'files': len(records), 'records': records}, indent=2) + '\n', encoding='utf8')
    write_collected_manifest()
    print('PASS byte-exact regenerated Lean sources:', len(records), flush=True)


if __name__ == '__main__':
    main()
