#!/usr/bin/env python3
"""Bind completed actual orbit-3 proofs, retaining the separate full-paper gate."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'artifacts/orbit-certification-20261003'
sys.path.insert(0, str(ROOT / 'tools'))
from lean_audit import audit_names


def main():
    names = ('orbit3-kl-build.json', 'orbit3-target-build.json',
             'orbit3-target-closure-build.json', 'orbit3-spin-hadamard-build.json',
             'orbit3-full-image-build.json', 'final-orbit-audit-build.json')
    for name in names:
        if json.loads((ART / name).read_text(encoding='utf8'))['status'] != 'PASS':
            raise ValueError('Build not passed: ' + name)
    log = ROOT / '.lake/build/certification/logs/MainTheory/OrbitCertificationFinalAudit.log'
    records = [json.loads(line) for line in log.read_text(encoding='utf8').splitlines()]
    count = len(audit_names((ROOT / 'MainTheory/OrbitCertificationFinalAudit.lean').read_text(encoding='utf8')))
    expected = f'CERTIFICATION_AXIOMS_OK roots={count} axioms=[propext, Quot.sound, Classical.choice]'
    if not any(r.get('data') == expected and r.get('severity') == 'information' for r in records):
        raise ValueError('The actual-encoder axiom audit did not pass')
    audit = ART / 'final-orbit-axioms.log'
    audit.write_text(expected + '\n', encoding='utf8')
    path = ROOT / 'results/orbit-certification-20261003.json'
    data = json.loads(path.read_text(encoding='utf8'))
    for source, sha in data['sources_sha256'].items():
        if hashlib.sha256((ROOT / source).read_bytes()).hexdigest() != sha:
            raise ValueError('Manuscript changed: ' + source)
    for stage in data['stages']:
        if stage['id'] == 'orbit3-full-converse':
            stage.update(status='kernel_checked_content_validated', missing=[],
                declarations=['MainTheory.Orbit3FullImage.all_primitive_rows_zero',
                              'MainTheory.Orbit3FullImage.target_coordinates',
                              'MainTheory.Orbit3FullImage.target_zero',
                              'MainTheory.Orbit3FullImage.actual_A3_zero',
                              'MainTheory.Orbit3FullImage.exact_distance_three',
                              'MainTheory.Orbit3FullImage.actual_enumerator',
                              'MainTheory.Orbit3FullImage.directory_image'],
                scope='Actual full-KL orbit-3 encoders satisfy all 203 KL, five spin and three Hadamard primitive rows. All 120 actual target Paulis yield the 269-coordinate sextic target. Its vanishing gives A3=0, exact distance three and the complete FI interval image including attainment.',
                evidence=['artifacts/orbit-certification-20261003/' + n for n in names] +
                         [audit.relative_to(ROOT).as_posix()])
    data['current_orbit3_kernel_evidence'] = {
        'builds': ['artifacts/orbit-certification-20261003/' + n for n in names],
        'actual_image_axiom_audit': audit.relative_to(ROOT).as_posix(),
        'final_serial_validation': 'pending; the full external inventory and every local module require unified validation'}
    data['kernel_build_status'] = 'actual orbit2 and orbit3 full images passed; unified full-local build pending'
    data['axiom_audit_status'] = f'{count} final actual-encoder and semantic roots use only propext, Quot.sound, Classical.choice; whole-paper audit remains separate'
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
    print('Recorded checked Orbit 3 actual image; full-paper status remains partial.')


if __name__ == '__main__':
    main()
