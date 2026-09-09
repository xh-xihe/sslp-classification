"""Regression tests for certification failures and build cache validity.

Run: python -m unittest discover -s tools/tests -v
No large Lean build is performed. Optional tiny Lean negative controls run when
CERTIFICATION_LEAN_TESTS=1, using only Lean itself and disposable source files.
"""
from contextlib import redirect_stdout
import hashlib
import gzip
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import shutil
import uuid
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'tools'))
import build_lean
import lean_source
import verify


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, REPO / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


readme = load('readme_check', 'tools/check-readme-names.py')
manifest = load('paper_manifest', 'tools/verification/mkmanifest.py')
generated = load('generated_manifest', 'tools/verification/generated_manifests.py')


class WorkspaceTest(unittest.TestCase):
    def setUp(self):
        (REPO / 'tmp').mkdir(exist_ok=True)
        self.root = REPO / 'tmp' / ('test-certification-' + uuid.uuid4().hex)
        self.root.mkdir()

    def tearDown(self):
        if self.root.resolve().parent == (REPO / 'tmp').resolve():
            shutil.rmtree(self.root)

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding='utf-8')
        return path


class ReadmeFailures(WorkspaceTest):
    def test_failure_without_unknown_word_is_rejected_and_logged(self):
        error = 'error: input file could not be opened\n'
        def fail(*args, **kwargs):
            return subprocess.CompletedProcess(args[0], 2, '', error)
        with redirect_stdout(io.StringIO()):
            self.assertEqual(readme.check_names(['MainTheory.foo'], fail, self.root), 1)
        self.assertEqual((self.root / 'tmp/verification/readme-names.log').read_text(), error)
        self.assertEqual(list((self.root / 'tmp/verification').glob('readme-*.lean')), [])


class LeanLexing(unittest.TestCase):
    def test_nested_comments_strings_and_real_escape_hatches(self):
        source = '/- sorry /- native_decide -/ axiom -/\n-- admit\n' \
                 'def text := "sorry axiom"\n theorem bad : False := by\n  admit\n'
        code = lean_source.code_only(source)
        self.assertEqual(code.count('\n'), source.count('\n'))
        self.assertEqual([match.group() for match in verify.FORBIDDEN.finditer(code)], ['admit'])

    def test_imports_and_prime_audit_names(self):
        self.assertEqual(lean_source.imports('public import SS.Basic MainTheory.X -- hi\n'),
                         ['SS.Basic', 'MainTheory.X'])
        self.assertEqual(lean_source.audit_names("#print axioms MainTheory.foo' -- hi\n"),
                         ["MainTheory.foo'"])
        with self.assertRaises(ValueError):
            lean_source.code_only('/- unfinished')


class AxiomAudit(WorkspaceTest):
    def setUp(self):
        super().setUp()
        for index, relative in enumerate(verify.AUDIT_FILES):
            self.write(relative, 'import Lean\n#print axioms Test.root%d\n' % index)

    def test_empty_audit_file_fails_closed(self):
        self.write(verify.AUDIT_FILES[1], 'import Lean\n')
        with self.assertRaisesRegex(ValueError, 'no declarations'):
            verify.axiom_inventory(self.root)

    def test_duplicate_root_is_rejected(self):
        self.write(verify.AUDIT_FILES[1], 'import Lean\n#print axioms Test.root0\n')
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            verify.axiom_inventory(self.root)

    def check_with_output(self, output, exit_code=0):
        roots, modules, hashes = verify.axiom_inventory(self.root)
        with patch.object(verify, 'axiom_inventory', return_value=(roots, modules, hashes)), \
             patch.object(verify, 'REPORT_DIR', self.root / 'reports'), \
             patch.object(verify, 'run', return_value=subprocess.CompletedProcess([], exit_code, output, '')):
            return verify.check_axioms()

    def test_no_success_marker_and_wrong_count_are_rejected(self):
        self.assertFalse(self.check_with_output('')[0])
        count = len(verify.axiom_inventory(self.root)[0])
        self.assertFalse(self.check_with_output(
            f'CERTIFICATION_AXIOMS_OK roots={count - 1} axioms=[propext]')[0])

    def test_unexpected_axiom_and_nonzero_exit_are_rejected(self):
        count = len(verify.axiom_inventory(self.root)[0])
        self.assertFalse(self.check_with_output(
            f'CERTIFICATION_AXIOMS_OK roots={count} axioms=[sorryAx]')[0])
        marker = f'CERTIFICATION_AXIOMS_OK roots={count} axioms=[propext]'
        self.assertFalse(self.check_with_output(marker, 1)[0])
        self.assertTrue(self.check_with_output(marker)[0])


class PaperManifest(WorkspaceTest):
    @staticmethod
    def table():
        rows = [r'\begin{longtable}{r}', r'\label{tab:66orbits}']
        for oid in range(1, 67):
            status = 'no-go' if oid >= 16 else 'WE'
            rows.append('%d & 3 & 3 & $(1,1,1,1,1,1)$ & $(22,21)$ & 6 & 1 & 1 & \\textsf{%s} \\\\' % (oid, status))
        rows.append(r'\end{longtable}')
        return '\n'.join(rows)

    def test_complete_table_and_ordered_fibres(self):
        table = self.table()
        self.assertEqual(len(manifest.parse_table(table)), 66)
        with self.assertRaisesRegex(manifest.ManifestError, 'ordered fiber'):
            manifest.parse_table(table.replace('$(22,21)$', '$(21,22)$', 1))

    def test_all_statistical_columns_are_preserved_and_change_the_manifest(self):
        table = self.table()
        original = manifest.parse_table(table)
        self.assertEqual({key: original[1][0][key] for key in
                          ('r_star', 'lp_dimension', 'multiplicity')},
                         {'r_star': 6, 'lp_dimension': 1, 'multiplicity': 1})
        for before, after, key, value in (
                ('& 6 & 1 & 1 &', '& 5 & 1 & 1 &', 'r_star', 5),
                ('& 6 & 1 & 1 &', '& 6 & 2 & 1 &', 'lp_dimension', 2),
                ('& 6 & 1 & 1 &', '& 6 & 1 & 2 &', 'multiplicity', 2)):
            changed = manifest.parse_table(table.replace(before, after, 1))
            self.assertNotEqual(original, changed)
            self.assertEqual(changed[1][0][key], value)

    def test_missing_duplicate_and_malformed_rows_fail(self):
        lines = self.table().splitlines()
        for bad in ('\n'.join(lines[:2] + lines[3:]),
                    '\n'.join(lines[:3] + [lines[2]] + lines[3:]),
                    self.table().replace('$(22,21)$', 'BROKEN', 1)):
            with self.assertRaises(manifest.ManifestError):
                manifest.parse_table(bad)

    def test_private_source_hashes_and_inventory_are_checked(self):
        directory = self.root / 'documents/20260905'
        self.write('documents/20260905/main.tex', 'private text')
        self.write('documents/20260905/supplementary.tex', self.table())
        existing = {'_no_go': {'lean_modules': {str(oid): 'Order9' if oid == 66 else 'Orbit%d' % oid
                                               for oid in range(16, 67)}}}
        result = manifest.build_manifest(directory, existing, self.root)
        self.assertEqual(len(result['_paper']['sources_sha256']), 2)
        self.write('documents/20260905/main.tex', 'changed private text')
        changed = manifest.build_manifest(directory, existing, self.root)
        self.assertNotEqual(result['_paper'], changed['_paper'])
        existing['_no_go']['lean_modules'].pop('16')
        with self.assertRaisesRegex(manifest.ManifestError, '51'):
            manifest.build_manifest(directory, existing, self.root)


class GeneratedManifest(WorkspaceTest):
    def setUp(self):
        super().setUp()
        self.relative = 'MainTheory/Generated/Fixture'
        rows = []
        for leaf, source in [('A', 'namespace Test\nend Test\n'), ('B', 'import MainTheory.Generated.Fixture.A\n')]:
            path = self.write(self.relative + '/' + leaf + '.lean', source)
            rows.append('%s  MainTheory.Generated.Fixture.%s' % (build_lean.file_hash(path), leaf))
        self.write(self.relative + '/generation-manifest.sha256', '# lean_files=2\n' + '\n'.join(rows))
        self.write(self.relative + '/serial-build-order.txt',
                   'MainTheory.Generated.Fixture.A\nMainTheory.Generated.Fixture.B\n')

    def test_exact_hash_coverage_and_topology(self):
        self.assertEqual(generated.check_directory(self.root, self.relative), 2)
        self.write(self.relative + '/Unexpected.lean', '')
        with self.assertRaisesRegex(ValueError, 'coverage'):
            generated.check_directory(self.root, self.relative)
        (self.root / self.relative / 'Unexpected.lean').unlink()
        self.write(self.relative + '/A.lean', '-- changed\n')
        with self.assertRaisesRegex(ValueError, 'SHA-256'):
            generated.check_directory(self.root, self.relative)

    def test_build_order_cannot_omit_or_precede_dependency(self):
        self.write(self.relative + '/serial-build-order.txt',
                   'MainTheory.Generated.Fixture.B\nMainTheory.Generated.Fixture.A\n')
        with self.assertRaisesRegex(ValueError, 'topological'):
            generated.check_directory(self.root, self.relative)


class SignGeneratedManifest(WorkspaceTest):
    def setUp(self):
        super().setUp()
        prefix = 'MainTheory.Generated.SignBeta1'
        raw = json.dumps({'sign_order': 2, 'levels': [[{}], [{}]]}).encode()
        path = self.root / 'results/sign-beta-proposals/beta1.json.gz'
        path.parent.mkdir(parents=True)
        path.write_bytes(gzip.compress(raw, mtime=0))
        self.entries = []
        for depth in (1, 2):
            for kind in ('Data', 'Proof'):
                node = f'{prefix}.{kind}.N{depth:02d}_0000'
                module = f'{prefix}.{kind}.G{depth:02d}_0000'
                source = f'namespace {node}\nend {node}\n'
                lean_path = self.write(module.replace('.', '/') + '.lean', source)
                self.entries.append(dict(module=module, nodes=[node], imports=[],
                    sha256=build_lean.file_hash(lean_path)))
        self.manifest = dict(schema=1, proposal_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                             modules=self.entries)
        self.save_manifest()

    def save_manifest(self):
        self.write('MainTheory/Generated/SignBeta1/manifest.json', json.dumps(self.manifest))

    def test_proposal_and_source_changes_are_rejected(self):
        self.assertEqual(generated.check_sign_family(self.root, 1), 4)
        source = self.root / 'MainTheory/Generated/SignBeta1/Proof/G01_0000.lean'
        source.write_text(source.read_text() + '-- changed\n')
        with self.assertRaisesRegex(ValueError, 'source SHA-256'):
            generated.check_sign_family(self.root, 1)

    def test_omitted_proposal_node_is_rejected(self):
        self.manifest['modules'] = self.entries[:-1]
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'node coverage'):
            generated.check_sign_family(self.root, 1)

    def test_relabelled_node_is_rejected_even_with_matching_hash(self):
        entry = self.entries[-1]
        old = entry['nodes'][0]
        new = old.replace('N02', 'N03')
        source = f'namespace {new}\nend {new}\n'
        lean_path = self.write(entry['module'].replace('.', '/') + '.lean', source)
        entry['nodes'] = [new]
        entry['sha256'] = build_lean.file_hash(lean_path)
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'node coverage'):
            generated.check_sign_family(self.root, 1)


class SerialBuild(WorkspaceTest):
    def test_unused_tooling_package_needs_no_build_artifacts(self):
        self.write('lean-toolchain', 'fixture')
        self.write('lakefile.lean', 'fixture')
        self.write('lake-manifest.json', json.dumps({'packages': [
            {'name': 'Cli', 'type': 'path'}, {'name': 'Mathlib', 'type': 'path'}]}))
        self.write('toolchain/bin/' + ('lean.exe' if os.name == 'nt' else 'lean'), 'compiler')
        self.write('toolchain/lib/lean/Lean.olean', 'Lean')
        mathlib = self.write('.lake/packages/Mathlib/.lake/build/lib/lean/Mathlib.olean', 'Mathlib')
        runner = lambda command, **kwargs: subprocess.CompletedProcess(
            command, 0, str(self.root / 'toolchain') + '\n', '')
        first, _, _ = build_lean.external_context(self.root, runner, ['Mathlib'])
        mathlib.write_text('modified artifact')
        second, _, _ = build_lean.external_context(self.root, runner, ['Mathlib'])
        self.assertNotEqual(first, second)
        with self.assertRaisesRegex(build_lean.BuildError, 'missing prebuilt external import: Cli'):
            build_lean.external_context(self.root, runner, ['Cli'])

    def test_malformed_stamp_is_never_adopted(self):
        path = build_lean.stamp_path(self.root, 'SS.Fixture')
        path.parent.mkdir(parents=True)
        for value in ([], 'invalid', {'schema': build_lean.SCHEMA, 'fingerprint': 'x', 'outputs': []}):
            path.write_text(json.dumps(value))
            self.assertIsNone(build_lean.valid_cache(self.root, 'SS.Fixture', 'x'))

    def test_dependency_order_and_cycle(self):
        graph = {'A': [], 'B': ['A'], 'C': ['B']}
        self.assertEqual(build_lean.topological_order(graph, ['C']), ['A', 'B', 'C'])
        with self.assertRaisesRegex(build_lean.BuildError, 'cycle'):
            build_lean.topological_order({'A': ['B'], 'B': ['A']})

    def test_content_changes_invalidate_without_timestamp_reliance(self):
        source = self.write('SS/Fixture.lean', 'def fixture := 1\n')
        old_time = source.stat().st_mtime_ns
        first = build_lean.fingerprint(build_lean.file_hash(source), {'Dep': 'key1'}, 'context')
        source.write_text('def fixture := 2\n')
        os.utime(source, ns=(old_time, old_time))
        second = build_lean.fingerprint(build_lean.file_hash(source), {'Dep': 'key1'}, 'context')
        third = build_lean.fingerprint(build_lean.file_hash(source), {'Dep': 'key2'}, 'context')
        self.assertNotEqual(first, second)
        self.assertNotEqual(second, third)

    def fake_compile(self, exit_code=0, mutate_source=None):
        def runner(command, **kwargs):
            if exit_code == 0:
                Path(command[command.index('-o') + 1]).write_bytes(b'new olean')
                Path(command[command.index('-i') + 1]).write_bytes(b'new ilean')
            if mutate_source:
                mutate_source.write_text('-- changed during compile\n')
            return subprocess.CompletedProcess(command, exit_code)
        return runner

    def test_failure_preserves_old_cache_and_writes_no_stamp(self):
        source = self.write('SS/Fixture.lean', 'def fixture := 1\n')
        old = self.write('.lake/build/lib/lean/SS/Fixture.olean', 'old proof cache')
        with self.assertRaises(build_lean.BuildError):
            build_lean.compile_module(self.root, 'SS.Fixture', source,
                build_lean.file_hash(source), 'fingerprint', self.fake_compile(exit_code=1))
        self.assertEqual(old.read_text(), 'old proof cache')
        self.assertFalse(build_lean.stamp_path(self.root, 'SS.Fixture').exists())

    def test_source_race_preserves_old_cache(self):
        source = self.write('SS/Fixture.lean', 'def fixture := 1\n')
        old = self.write('.lake/build/lib/lean/SS/Fixture.olean', 'old proof cache')
        with self.assertRaisesRegex(build_lean.BuildError, 'during compilation'):
            build_lean.compile_module(self.root, 'SS.Fixture', source,
                build_lean.file_hash(source), 'fingerprint', self.fake_compile(mutate_source=source))
        self.assertEqual(old.read_text(), 'old proof cache')

    def test_success_promotes_then_hash_validates_outputs(self):
        source = self.write('SS/Fixture.lean', 'def fixture := 1\n')
        self.write('.lake/build/lib/lean/SS/Fixture.olean.private', 'obsolete sidecar')
        build_lean.compile_module(self.root, 'SS.Fixture', source,
            build_lean.file_hash(source), 'fingerprint', self.fake_compile())
        self.assertIsNotNone(build_lean.valid_cache(self.root, 'SS.Fixture', 'fingerprint'))
        self.assertFalse((self.root / '.lake/build/lib/lean/SS/Fixture.olean.private').exists())
        self.write('.lake/build/lib/lean/SS/Fixture.olean', 'tampered proof cache')
        self.assertIsNone(build_lean.valid_cache(self.root, 'SS.Fixture', 'fingerprint'))


@unittest.skipUnless(os.environ.get('CERTIFICATION_LEAN_TESTS') == '1', 'opt-in tiny Lean controls')
class LeanNegativeControls(WorkspaceTest):
    def test_actual_warning_is_a_build_error(self):
        path = self.write('Warning.lean', 'import Lean\nrun_cmd Lean.logWarning "verification warning control"\n')
        proc = subprocess.run(['lake', 'env', 'lean', *build_lean.LEAN_FLAGS, str(path)], cwd=REPO,
                              capture_output=True, text=True, encoding='utf-8', errors='replace')
        self.assertNotEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn('verification warning control', proc.stdout + proc.stderr)

    def execute(self, declaration, roots):
        source = verify.render_axiom_harness(roots, ['Lean'])
        source = source.replace('\nrun_cmd do\n', '\n' + declaration + '\nrun_cmd do\n')
        path = self.write('Control.lean', source)
        return subprocess.run(['lake', 'env', 'lean', '-j', '1', str(path)], cwd=REPO,
                              capture_output=True, text=True, encoding='utf-8', errors='replace')

    def test_absent_root_is_rejected(self):
        proc = self.execute('', ['DoesNotExist'])
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('Missing kernel declaration', proc.stdout + proc.stderr)

    def test_custom_axiom_is_rejected(self):
        proc = self.execute('axiom TestUntrusted : False', ['TestUntrusted'])
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('Unexpected transitive axiom', proc.stdout + proc.stderr)

    def test_valid_root_succeeds(self):
        proc = self.execute('theorem TestTrusted : True := True.intro', ['TestTrusted'])
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn('CERTIFICATION_AXIOMS_OK roots=1', proc.stdout + proc.stderr)

    def test_kernel_decision_has_no_untrusted_axiom(self):
        proc = self.execute(
            'theorem TestKernelDecision : (List.range 64).length = 64 := by decide +kernel',
            ['TestKernelDecision'])
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn('CERTIFICATION_AXIOMS_OK roots=1', proc.stdout + proc.stderr)


@unittest.skipUnless(os.environ.get('CERTIFICATION_LEAN_TESTS') == '1', 'opt-in Lean certificate controls')
class QuadraticPruneNegativeControls(WorkspaceTest):
    def execute(self, statement):
        path = self.write('QuadraticControl.lean',
            'import MainTheory.SignQuadraticChunkPrune\n'
            'set_option maxRecDepth 100000\n'
            'open MainTheory.SignQuadraticMinimum MainTheory.SignQuadraticChunkPrune\n'
            + statement + '\n')
        return subprocess.run(['lake', 'env', 'lean', '-j', '1', '-DwarningAsError=true', str(path)],
            cwd=REPO, capture_output=True, text=True, encoding='utf-8', errors='replace')

    def test_correct_restricted_minimum(self):
        proc = self.execute('example : restrictedMinimum 1 0 0 !![1] ![none] = 1 := by decide +kernel')
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_overstated_quadratic_lower_bound_is_rejected(self):
        proc = self.execute('example : 2 ≤ restrictedMinimum 1 0 0 !![1] ![none] := by decide +kernel')
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('false', (proc.stdout + proc.stderr).lower())
        self.assertNotIn('does not exist', proc.stdout + proc.stderr)

    def test_wrong_chunk_fixed_bits_are_rejected(self):
        proc = self.execute('example : Matches (fixedHighBits (N := 10) 3 (8 : Fin 1024)) '
            '(MainTheory.SignRowEnumeration.row (N := 10) (0 : Fin 1024)) := by decide +kernel')
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('false', (proc.stdout + proc.stderr).lower())
        self.assertNotIn('does not exist', proc.stdout + proc.stderr)


if __name__ == '__main__':
    unittest.main()
