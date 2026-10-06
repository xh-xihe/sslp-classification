"""Symbolic transcription control for the reviewed 20260924 displayed basis.

This supports human formula review; it is not a new Lean proof.
"""
import hashlib
import itertools
import json
from pathlib import Path
import unittest
import sympy as s

ROOT = Path(__file__).resolve().parents[2]

class DisplayedBasisReview(unittest.TestCase):
    def test_export_is_bound_to_the_reviewed_manuscript(self):
        data = json.loads((ROOT/'results/sslp-explorer/class36-20260924.json').read_text())
        paper = ROOT/'documents/20260924/main.tex'
        if not paper.exists():
            self.skipTest('documents/ holds the unpublished manuscript and is not in a checkout')
        self.assertEqual(hashlib.sha256(paper.read_bytes()).hexdigest(), data['paper']['sources_sha256']['documents/20260924/main.tex'])

    def test_expanded_paper_formulas_match_every_coordinate(self):
        data = json.loads((ROOT/'results/sslp-explorer/class36-20260924.json').read_text())
        omega = (-1+s.I*s.sqrt(3))/2
        edge = {'1100':1,'0011':1,'1010':omega,'0101':omega,'1001':omega**2,'0110':omega**2}
        psi0 = {'000000':1/s.sqrt(10),'000011':1/s.sqrt(10)}
        psi1 = {'111100':1/s.sqrt(10),'111111':1/s.sqrt(10)}
        for bits in itertools.product('01',repeat=4):
            prefix = ''.join(bits)
            if prefix.count('1') == 3: psi0[prefix+'10'] = 1/s.sqrt(10)
            if prefix.count('1') == 1: psi1[prefix+'01'] = -1/s.sqrt(10)
        for bits, amplitude in edge.items():
            psi0[bits+'01'] = amplitude/s.sqrt(15)
            psi1[bits+'10'] = -s.conjugate(amplitude)/s.sqrt(15)
        basis = [1,s.sqrt(2),s.sqrt(3),s.sqrt(6),s.I,s.I*s.sqrt(2),s.I*s.sqrt(3),s.I*s.sqrt(6)]
        for paper_word, exported_word in zip([psi0,psi1], data['words']):
            exact = {a['bits']:sum(c*b for c,b in zip(a['coordinates'],basis))/(2*s.sqrt(30)) for a in exported_word}
            self.assertEqual(set(paper_word),set(exact))
            for bits in paper_word:
                self.assertEqual(s.simplify(exact[bits]-paper_word[bits]),0,bits)
        for index,word in enumerate([psi0,psi1]):
            for bits in word:
                total=sum(int(bit)*a for bit,a in zip(bits,[1,1,1,1,2,3]))
                self.assertEqual(total%5,[0,4][index])
                self.assertEqual(4*total%5,[0,1][index])

if __name__ == '__main__':
    unittest.main()
