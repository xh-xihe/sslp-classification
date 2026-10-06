#!/usr/bin/env python3
"""Record the checked root integration; never declare the whole paper complete."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'artifacts/orbit-certification-20261003'


def main():
    builds = ('orbit2-integrated-build.json', 'orbit2-full-image-build.json',
              'orbit2-spectra-build.json', 'orbit2-spectral-table-build.json',
              'orbit2-physical-spectra-build.json')
    for name in builds:
        if json.loads((ART / name).read_text(encoding='utf8'))['status'] != 'PASS':
            raise ValueError('Build not passed: ' + name)
    audit = ART / 'orbit2-final-image-axioms.log'
    raw = audit.read_bytes()
    audit_text = raw.decode('utf16' if raw.startswith(b'\xff\xfe') else 'utf8').strip()
    if audit_text != (
            'CERTIFICATION_AXIOMS_OK roots=9 axioms=[propext, Quot.sound, Classical.choice]'):
        raise ValueError('The actual-image axiom audit did not pass')
    audit.write_text(audit_text + '\n', encoding='utf8')
    path = ROOT / 'results/orbit-certification-20261003.json'
    data = json.loads(path.read_text(encoding='utf8'))
    for source, sha in data['sources_sha256'].items():
        if hashlib.sha256((ROOT / source).read_bytes()).hexdigest() != sha:
            raise ValueError('Manuscript changed: ' + source)
    for stage in data['stages']:
        if stage['id'] == 'orbit2-full-converse':
            stage.update(status='kernel_checked_content_validated', missing=[],
                declarations=[
                    'MainTheory.Orbit2FullImage.logicalZ',
                    'MainTheory.Orbit2FullImage.actual_enumerator',
                    'MainTheory.Orbit2FullImage.actual_A3_zero',
                    'MainTheory.Orbit2FullImage.exact_distance_three',
                    'MainTheory.Orbit2FullImage.directory_image'],
                scope='Actual full-KL directory completions map to the shared root Encoder. Their normalized enumerators have the whole FI interval as image, including attainment and exact distance three.',
                evidence=['artifacts/orbit-certification-20261003/' + name for name in builds[:2]] +
                         [audit.relative_to(ROOT).as_posix()])
    data['stages'] = [s for s in data['stages'] if s['id'] != 'orbit2-si-spectral-table']
    data['stages'].append({
        'id': 'orbit2-si-spectral-table', 'status': 'kernel_checked_content_validated',
        'declarations': ['MainTheory.Orbit2SpectralTable.counts_correct',
                         'MainTheory.Orbit2SpectralTable.number_of_blocks',
                         'MainTheory.Orbit2SpectralTable.number_of_coordinates',
                         'SixQubit.Generated.Orbit2PhysicalSpectra.physical_dimensions',
                         'SixQubit.Generated.Orbit2PhysicalSpectra.physical_characteristic_polynomials'],
        'scope': 'All 111 physical quartic blocks, totaling 492 coordinates, have the seven SI characteristic-polynomial patterns and stated multiplicities. Each original physical matrix is identified with the shifted root positivity matrix plus 4I.',
        'evidence': ['artifacts/orbit-certification-20261003/' + name for name in builds[2:]]})
    data['orbit2_colleague_review']['integration_status'] = (
        'PASS: shared root libraries and actual MainTheory directoryImage 1, with standard-axiom audit')
    data['current_orbit2_kernel_evidence'] = {
        'builds': ['artifacts/orbit-certification-20261003/' + name for name in builds],
        'actual_image_axiom_audit': audit.relative_to(ROOT).as_posix(),
        'final_serial_validation': 'pending; must rehash the full external inventory and validate all content stamps'}
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
    print('Recorded checked Orbit 2 image and physical spectral table; overall status remains partial.')


if __name__ == '__main__':
    main()
