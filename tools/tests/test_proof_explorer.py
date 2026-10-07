"""Regression controls for source-bound explorer generation, without a browser."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from build_explorer import INPUTS, orbit_tags, parse_guides, payload, script_json


class ExplorerTests(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)
        self.paths=['MainTheory/Orbit2FullImage.lean','MainTheory/Orbit3FullImage.lean']
        catalog={'module_count':2,'modules':[{'path':p,'library':'MainTheory','topic':'Encoder bridges'} for p in self.paths]}
        self.write(INPUTS[0],json.dumps(catalog))
        status={'active_lean_modules':2,'orbit2_full_image':'kernel_checked','orbit3_full_image':'kernel_checked',
                'paper_version':'20261003','date':'2026-10-05','axiom_roots':2,'held_main_issues':5,
                'open_enumerator_images':[1,4],'si_fully_kernel_correspondence':'complete'}
        self.write(INPUTS[1],json.dumps(status))
        self.write(INPUTS[2],'## Supplementary material\n| Orbit 2: image | [source](../'+self.paths[0]+') |\n| Orbit 3: image | [source](../'+self.paths[1]+') |\n')
        for p in self.paths:self.write(p,'theorem directory_image : True := by trivial\n')
        resources=['results/orbit2-kernel/gram-blocks.json','tools/certificates/orbit2_exact_certificate.py',
                   'results/orbit3-kernel/certificate.json','results/orbit3-kernel/scalar-certificate.json',
                   'tools/certificates/orbit3_exact_sextic_certificate.py',
                   'artifacts/manuscript-certification-20261005/proof-acceptance-16227.json',
                   'artifacts/manuscript-certification-20261005/axioms-9375.json',
                   'artifacts/manuscript-certification-20261005/publication-binding-16227.json',
                   'docs/manuscript-correspondence.md']
        for p in resources:self.write(p,'{}')

    def write(self,path,text):
        target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(text,encoding='utf-8',newline='\n')

    def change_json(self,path,change):
        data=json.loads((self.root/path).read_text());change(data);self.write(path,json.dumps(data))

    def test_actual_orbit_numbers_do_not_alias_two_and_twenty(self):
        self.assertEqual(orbit_tags('MainTheory/Orbit20DisplayCompletion.lean'),[20])
        self.assertEqual(orbit_tags('Orbit2/Complete.lean'),[2])
        self.assertEqual(orbit_tags('Orbits 13, 17 and 20: actual error rows'),[13,17,20])

    def test_guides_require_real_catalog_targets_and_nonempty_input(self):
        with self.assertRaisesRegex(ValueError,'uncataloged'):
            parse_guides('## Main-text theory\n| image | [x](../Missing.lean) |',self.paths)
        with self.assertRaisesRegex(ValueError,'empty'):
            parse_guides('# No proof rows',self.paths)

    def test_inventory_counts_cannot_silently_drop_sources(self):
        self.change_json(INPUTS[0],lambda d:d.update(module_count=3))
        with self.assertRaisesRegex(ValueError,'count'):
            payload(self.root)

    def test_source_catalog_status_mismatch_is_rejected(self):
        self.change_json(INPUTS[1],lambda d:d.update(active_lean_modules=3))
        with self.assertRaisesRegex(ValueError,'different module counts'):
            payload(self.root)

    def test_missing_catalog_source_is_rejected(self):
        (self.root/self.paths[0]).unlink()
        with self.assertRaisesRegex(ValueError,'Missing catalog source'):
            payload(self.root)

    def test_lost_endpoint_status_is_not_presented_as_checked(self):
        self.change_json(INPUTS[1],lambda d:d.update(orbit2_full_image='pending'))
        with self.assertRaisesRegex(ValueError,'recorded proof status'):
            payload(self.root)

    def test_deleted_exact_certificate_link_is_rejected(self):
        (self.root/'results/orbit3-kernel/certificate.json').unlink()
        with self.assertRaisesRegex(ValueError,'Missing exact certificate'):
            payload(self.root)

    def test_missing_full_image_guide_is_rejected(self):
        self.write(INPUTS[2],'## Supplementary material\n| Orbit 3: image | [source](../'+self.paths[1]+') |\n')
        with self.assertRaisesRegex(ValueError,'Missing curated full-image guide'):
            payload(self.root)

    def test_missing_theorem_endpoint_is_rejected(self):
        self.write(self.paths[0],'-- endpoint removed\n')
        with self.assertRaisesRegex(ValueError,'declaration no longer exists'):
            payload(self.root)

    def test_script_payload_cannot_terminate_its_json_element(self):
        value={'title':'</script><script>alert(1)</script>','text':'<>&\u2028'}
        safe=script_json(value)
        self.assertNotIn('<',safe)
        self.assertEqual(json.loads(safe),value)

    def test_status_and_input_hashes_are_bound_without_adding_coverage(self):
        first=payload(self.root)
        self.assertEqual(first['status']['paper_version'],'20261003')
        self.assertEqual(first['status']['held_main_issues'],5)
        self.assertNotIn('covered',first['modules'][0])
        path=self.root/INPUTS[2]
        path.write_bytes(path.read_bytes().replace(b'\n',b'\r\n'))
        self.assertEqual(payload(self.root)['source_hashes_lf'],first['source_hashes_lf'])


if __name__=='__main__':unittest.main()
