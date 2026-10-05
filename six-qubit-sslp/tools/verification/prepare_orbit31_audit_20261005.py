"""Select explicit orbit-31, orbit-32 and orbit-33 roots for inspection/audit.

Selection never decides manuscript coverage. Every listed module must compile,
and the separately reviewed types must be tied to exact manuscript statements.
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from lean_source import code_only
from lean_audit import audit_names
import verify


def modules():
    paths = list((ROOT/'MainTheory').glob('Orbit31*.lean'))
    paths = [p for p in paths if p.stem != 'Orbit31Identification']
    paths += list((ROOT/'MainTheory').glob('Orbit32Printed*.lean'))
    for name in ('Orbit33PrintedBlocks','Orbit33ScalarReflection','Orbit33NormalizedPairs',
                 'Orbit33PhysicalReflection','Orbit33ProjectorArgument',
                 'ComplementaryPhasePair','GridSupportAlgebra',
                 'OrderFiveWalshRemainingDisplays','OrderFiveGridRemainingDisplays',
                 'OrderFourWalshRemainingDisplays','OrderThreePrintedMoments',
                 'OrderThreePrintedCrossRows','OrderThreePrintedRanks',
                 'ArbitrarySplitPerfectCode','ArbitrarySplitSixQubit',
                 'StandardFiveSyndromeDisplays','StandardFiveJointSpace','Orbit49PrintedRows',
                 'Orbit49PrintedAlgebra','Orbit49PhysicalCompletion',
                 'RectangularFlipCharacters','PhysicalPhaseQuotients',
                 'Orbit50PrintedRows','Orbit50PhysicalTriangle',
                 'Orbit51PrintedRows','Orbit51PrintedAlgebra','Orbit51PhysicalCompletion',
                 'OrderTwoPrintedMoments','OrderTwoPrintedWalsh','OrderTwoPrintedRanks',
                 'OrderTwoShellProjectors','HalfAngleFiberFlip',
                 'IndexedCodeMoments','Orbit45PhysicalPrintedRows','Orbit45PhysicalSpinFlip',
                 'Orbit45AffineGauge','Orbit45CrossFactors','Orbit45PhysicalProbabilityDomain',
                 'Orbit45RelativeLogicalPhase','Orbit45PrintedDiagonalContribution','Orbit45ShadowNormalization',
                 'Orbit45PhysicalGauge','Orbit45BottomGauge','Orbit45TopGauge','Orbit45PhysicalPhaseNormalForm',
                 'Orbit45PhysicalCanonicalForm','Orbit45OrientedCoherences','Orbit45PrintedLogicalAction',
                 'Orbit45DressingParseval','Orbit45PrintedOffContribution','Orbit45PrintedEnumerator',
                 'Orbit45TriangleExistence',
                 'Orbit29PrintedFaceAudit','Orbit29PairBalance','Orbit29PhysicalPairReduction',
                 'Orbit29PrintedSimplex','Orbit29SimplexRelativeInterior','Orbit29SimplexDimensions',
                 'Orbit29PhysicalRatios','Orbit29PhysicalPairGauge','Orbit29PrintedEta',
                 'Orbit29MomentRank','Orbit29MomentPolytope'):
        path=ROOT/'MainTheory'/(name+'.lean')
        if path.is_file():
            paths.append(path)
    split = ROOT/'MainTheory/Orbit3PrintedSplitMatrices.lean'
    if split.is_file():
        paths.append(split)
    paths += list((ROOT/'MainTheory/Generated').rglob('Orbit31*.lean'))
    for dirname in ('Orbit31SupportCoverage', 'Orbit31PhaseCoverage',
                    'Orbit31CrossRows', 'Orbit31VertexReconstructions', 'Orbit31DirectTriangles'):
        paths += list((ROOT/'MainTheory/Generated'/dirname).glob('*.lean'))
    paths += [ROOT/'MainTheory'/name for name in (
        'MatrixPositiveSupportCertificates.lean', 'MatrixPositiveSupportVertices.lean',
        'FiniteListCertificateCounts.lean', 'SignedPhaseSupport.lean')]
    return sorted(set(paths))


def declarations(path):
    namespace, stack, names = '', [], []
    for line in code_only(path.read_text(encoding='utf8')).splitlines():
        if match := re.match(r'^namespace\s+(\S+)', line):
            stack.append(namespace)
            name = match.group(1)
            namespace = (namespace+'.'+name) if namespace else name
        elif re.match(r'^(?:noncomputable\s+)?section(?:\s|$)', line):
            stack.append(namespace)
        elif re.match(r'^end(?:\s|$)', line):
            namespace = stack.pop()
        elif match := re.match(r'^(?:def|abbrev|structure|theorem|lemma)\s+([\w\'\u0080-\uffff]+)', line):
            names.append(namespace+'.'+match.group(1))
    if stack:
        raise ValueError(f'unclosed namespace/section: {path}')
    return names


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    paths = modules()
    roots = sorted({name for path in paths for name in declarations(path)} |
                   {'SixQubit.Orbit31.momentMatrix_rank',
                    'MainTheory.SupportKetExpansion.expansion',
                    'MainTheory.SupportKetExpansion.indexed_expansion',
                    *('SixQubit.Orbit'+str(o)+'.'+n for o in (50,51) for n in
                      ('av','S0_eq_fiber','S1_eq_fiber'))})
    if (ROOT/'MainTheory/Orbit33NormalizedPairs.lean').is_file():
        roots=sorted(set(roots)|{'MainTheory.Orbit33NormalizedPairs.Frame.'+field for field in
          ('u','v','a','b','unitU','unitV','factors','phaseSigns','phaseNonzero','orthogonalFar')})
    if (ROOT/'MainTheory/Orbit45PhysicalSpinFlip.lean').is_file():
        import importlib
        for module in ('review_orbit31_completion_20261005','review_orbit33_completion_20261005',
                       'review_order_four_five_remaining_20261005','review_order_three_printed_20261005',
                       'review_order_two_printed_20261005','review_orbit45_physical_displays_20261005',
                       'review_orbit29_printed_20261005'):
            review=importlib.import_module(module)
            roots=sorted(set(roots)|{name for row in review.GROUPS for name in row[1]}|
                         {name for row in review.PROSE for name in row[-2]})
    evidence = ROOT/'artifacts/manuscript-certification-20261005'
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence/'orbit31-extra-roots.json').write_text(json.dumps(roots, indent=2)+'\n', encoding='utf8')
    if args.apply:
        path = ROOT/'MainTheory/ManuscriptCertificationAudit20261005.lean'
        source = path.read_text(encoding='utf8')
        marker = '\n-- BEGIN CURRENT ORBIT31 CORRESPONDENCE ROOTS\n'
        if marker in source:
            source = source.split(marker)[0]
        imports = '\n'.join('import '+p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.') for p in paths)
        imports += '\nimport SixQubit.Orbit31MomentRank'
        imports += '\nimport MainTheory.SupportKetExpansion'
        # Import headers must precede declarations. Reapplication replaces only
        # the generated import block and the generated final root block.
        import_begin = '-- BEGIN CURRENT ORBIT31 IMPORTS\n'
        import_end = '-- END CURRENT ORBIT31 IMPORTS\n'
        if import_begin in source:
            before, old = source.split(import_begin, 1)
            _, after = old.split(import_end, 1)
            source = before+after
        source = import_begin+imports+'\n'+import_end+source
        # Inspection may repeat existing roots, but the shared axiom inventory
        # requires each declaration exactly once across all audit files.
        existing = set(audit_names(source))
        for relative in verify.AUDIT_FILES:
            if ROOT/relative != path:
                existing.update(audit_names((ROOT/relative).read_text(encoding='utf8')))
        audit_roots = [name for name in roots if name not in existing]
        source += marker
        for start in range(0, len(audit_roots), 64):
            source += '#certification_axioms [\n  '+',\n  '.join(audit_roots[start:start+64])+'\n]\n\n'
        path.write_text(source, encoding='utf8', newline='\n')
    print(f'orbit-31 inspection roots: {len(roots)}; modules: {len(paths)}')


if __name__ == '__main__':
    main()
