"""Negative controls for repository navigation checks; no Lean or network needed."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_navigation import anchors, check_links, check_svgs, links


class NavigationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding='utf-8')

    def test_missing_target_and_missing_anchor_are_failures(self):
        self.write('README.md', '[missing](absent.md) [anchor](doc.md#absent)')
        self.write('doc.md', '# Present\n')
        count, errors = check_links(self.root, ['README.md'])
        self.assertEqual(count, 2)
        self.assertEqual(len(errors), 2)
        self.assertIn('missing target', errors[0])
        self.assertIn('missing anchor', errors[1])

    def test_markdown_images_html_and_encoded_paths_are_checked(self):
        self.write('README.md', '![image](assets/image.svg) <a href="docs/a%20b.md#one">x</a>')
        self.write('assets/image.svg', 'placeholder')
        self.write('docs/a b.md', '# One\n')
        self.assertEqual(check_links(self.root, ['README.md']), (2, []))

    def test_code_examples_and_comments_are_not_links(self):
        text = '```md\n[x](no.md)\n```\n`[x](no.md)`\n<!-- [x](no.md) -->\n[x](yes.md)'
        self.assertEqual(links(text), ['yes.md'])

    def test_fenced_heading_does_not_supply_an_anchor(self):
        self.write('README.md', '[x](doc.md#fake)')
        self.write('doc.md', '# Real\n```md\n# Fake\n```\n')
        self.assertIn('missing anchor', check_links(self.root, ['README.md'])[1][0])

    def test_duplicate_unicode_and_inline_code_heading_slugs(self):
        result = anchors('# Hello, `Lean`!\n# Hello, `Lean`!\n# 核验\n<a id="custom"></a>')
        self.assertTrue({'hello-lean', 'hello-lean-1', '核验', 'custom'}.issubset(result))

    def test_external_links_are_not_fetched_and_escapes_fail(self):
        self.write('README.md', '[web](https://example.invalid/path) [escape](../outside.md)')
        count, errors = check_links(self.root, ['README.md'])
        self.assertEqual(count, 1)
        self.assertIn('escapes repository', errors[0])

    def test_reference_definition_and_same_page_anchor(self):
        self.write('README.md', '# Here\n[x][local]\n[local]: doc.md\n[x](#here)')
        self.write('doc.md', '# Document')
        self.assertEqual(check_links(self.root, ['README.md']), (2, []))

    def test_missing_navigation_file_cannot_pass_vacuously(self):
        self.assertIn('missing navigation document', check_links(self.root, ['README.md'])[1][0])

    def test_svg_rejects_remote_resources_active_content_and_bad_xml(self):
        self.write('docs/assets/a.svg', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1 1"><title>Test</title><script/><image href="https://example.invalid/x"/></svg>')
        self.write('docs/assets/b.svg', '<svg>')
        count, errors = check_svgs(self.root)
        self.assertEqual(count, 2)
        self.assertTrue(any('active embedded' in error for error in errors))
        self.assertTrue(any('external resource' in error for error in errors))
        self.assertTrue(any('invalid SVG' in error for error in errors))


if __name__ == '__main__':
    unittest.main()
