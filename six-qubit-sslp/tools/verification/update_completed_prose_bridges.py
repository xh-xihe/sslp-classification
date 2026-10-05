#!/usr/bin/env python3
"""Update only the prose assertions whose actual kernel bridges are completed."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'artifacts/orbit-certification-20261003'


def main():
    for filename in ('orbit2-full-image-build.json', 'orbit3-full-image-build.json',
                     'orbit2-physical-spectra-build.json', 'seven-qubit-logical-action-build.json',
                     'common-mean-replacement-build.json', 'positive-affine-moments-build.json'):
        if json.loads((ART / filename).read_text(encoding='utf8'))['status'] != 'PASS':
            raise ValueError('Unpassed bridge: ' + filename)
    path = ROOT / 'results/prose-review-20261003.json'
    data = json.loads(path.read_text(encoding='utf8'))
    for source, sha in data['sources_sha256'].items():
        if hashlib.sha256((ROOT / source).read_bytes()).hexdigest() != sha:
            raise ValueError('The manuscript changed: ' + source)
    updates = {
        'si-orbit2-new-converse': (
            ['MainTheory.Orbit2FullImage.actual_A3_zero', 'MainTheory.Orbit2FullImage.actual_enumerator',
             'MainTheory.Orbit2FullImage.directory_image',
             'SixQubit.Generated.Orbit2PhysicalSpectra.physical_characteristic_polynomials'],
            'Actual full-KL complex encoders map into the integrated root orbit-two proof. Its full normalized FI image, both containment and attainment, is kernel checked. All 111 physical quartic blocks are identified and have the seven stated SI spectral patterns.'),
        'si-orbit3-new-converse': (
            ['MainTheory.Orbit3FullImage.all_primitive_rows_zero',
             'MainTheory.Orbit3FullImage.target_coordinates', 'MainTheory.Orbit3FullImage.target_zero',
             'MainTheory.Orbit3FullImage.actual_enumerator', 'MainTheory.Orbit3FullImage.directory_image'],
            'Actual full-KL complex encoders satisfy every KL, spin and Hadamard primitive row. All 120 actual target Paulis yield the 269-coordinate sextic target; its vanishing gives the actual A3=0 and full FI interval image, with attainment.'),
    }
    for row in data['assertions']:
        if row['id'] in updates:
            declarations, reason = updates[row['id']]
            row.update(kind='covered', declarations=declarations, reason=reason)
    additions = [
        ('seven-qubit-actual-example', 'ex:seven-qubit-rationalization',
         ['MainTheory.SevenQubitLogicalAction.family_eigenvalues',
          'MainTheory.SevenQubitRationalFamily.family_infinite_order',
          'MainTheory.SevenQubitMinimumOrder.minimum_physical_order',
          'MainTheory.SevenQubitLogicalCharacter.projectiveEquiv'],
         'The new actual seven-qubit complex code has logical group ZMod 6, the stated actual eigenvalues and irrational infinite-order representatives. Its exact minimum physical order for the target class is twelve.'),
        ('generic-common-mean-action', 'lem:common-mean-rational-replacement',
         ['MainTheory.CommonMeanReplacement.support_value',
          'MainTheory.CommonMeanReplacement.replacement_on_direct_sum'],
         'The common-mean argument and its exact physical exponential scalar hold for arbitrary finite supports, distributions and supported subspaces, without rational-probability or KL assumptions.'),
        ('generic-positive-affine-moments', 'lem:positive-affine-moments',
         ['MainTheory.PositiveAffineMoments.affineSpan_eq'],
         'The positive-square-moment lemma is now proved for arbitrary finite real point sets of different cardinalities, including its affine annihilator argument; it is not restricted to computational-basis supports.'),
    ]
    ids = {r['id'] for r in data['assertions']}
    for ident, locator, declarations, reason in additions:
        if ident not in ids:
            data['assertions'].append(dict(id=ident, source='main.tex', locator=locator,
                statement=locator, line=1, kind='covered', declarations=declarations, reason=reason))
    data['method'] += (' Updated on 2026-10-04 only for completed actual orbit images, physical '
                       'spectral tables, the seven-qubit example and two generic geometric bridges. '
                       'Unreviewed claims and author-held main errata remain outside a completion claim.')
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
    print('Updated completed actual prose bridges; the full prose review remains partial.')


if __name__ == '__main__':
    main()
