"""Check that proof navigation excludes archives and binds exact source contents."""
from pathlib import Path
import shutil
import sys
import unittest
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import repository_index as index


class RepositoryIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp_root = Path(__file__).resolve().parents[2] / 'tmp'
        self.temp_root.mkdir(exist_ok=True)
        self.root = self.temp_root / ('test-repository-index-' + uuid.uuid4().hex)
        self.root.mkdir()

    def tearDown(self):
        if self.root.resolve().parent != self.temp_root.resolve():
            raise RuntimeError('Test cleanup path escaped the workspace temp directory')
        shutil.rmtree(self.root)

    def test_archive_and_scratch_are_not_active_modules(self):
        for relative in ['SS.lean', 'SS/Basic.lean', 'archive/stages/Test.lean', 'scratch/Test.lean']:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('import Lean\n', encoding='utf-8')
        data = index.catalog(self.root)
        self.assertEqual([r['module'] for r in data['modules']], ['SS.Basic', 'SS'])

    def test_digest_is_portable_but_sensitive_to_proof_changes(self):
        (self.root / 'SS').mkdir()
        path = self.root / 'SS/Basic.lean'
        path.write_bytes(b'theorem a : True := trivial\r\n')
        first = index.catalog(self.root)['modules'][0]['sha256_lf']
        path.write_bytes(b'theorem a : True := trivial\n')
        self.assertEqual(index.catalog(self.root)['modules'][0]['sha256_lf'], first)
        path.write_bytes(b'theorem b : True := trivial\n')
        self.assertNotEqual(index.catalog(self.root)['modules'][0]['sha256_lf'], first)

    def test_orbit_prefixes_do_not_mix_two_digit_orbits(self):
        self.assertEqual(index.topic('MainTheory/Orbit2FullImage.lean'), 'Orbit 2: physical encoder bridges')
        self.assertEqual(index.topic('MainTheory/Orbit3FullImage.lean'), 'Orbit 3: scalar and sextic encoder bridges')
        self.assertNotEqual(index.topic('MainTheory/Orbit21UnsignedClasses.lean'), 'Orbit 2: physical encoder bridges')
        self.assertNotEqual(index.topic('MainTheory/Orbit36Rigidity.lean'), 'Orbit 3: scalar and sextic encoder bridges')


if __name__ == '__main__':
    unittest.main()
