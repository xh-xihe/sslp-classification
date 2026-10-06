"""Type-export checks must fail closed on stale or incomplete evidence."""
import json
import unittest
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))

from export_claim_types import parse_types, requested_roots


class ExportTypesTests(unittest.TestCase):
    def setUp(self):
        self.ledger = {'sources': {'main': 'current'}, 'claims': [
            {'id': 'main:c', 'statement_sha256': 'statement',
             'lean_declarations': ['Proof.first']}]}
        self.candidates = {'sources_sha256': {'main': 'current'}, 'candidates': [
            {'current_id': 'main:c', 'current_statement_sha256': 'statement',
             'prior_lean_declarations': ['Proof.second']}]}

    def test_candidate_binding(self):
        self.assertEqual(requested_roots(self.ledger,self.candidates),
                         ['Proof.first','Proof.second'])

    def test_changed_source_rejected(self):
        self.candidates['sources_sha256']['main'] = 'old'
        with self.assertRaisesRegex(ValueError,'different manuscript'):
            requested_roots(self.ledger,self.candidates)

    def test_changed_statement_rejected(self):
        self.candidates['candidates'][0]['current_statement_sha256'] = 'other'
        with self.assertRaisesRegex(ValueError,'Changed candidate'):
            requested_roots(self.ledger,self.candidates)

    def test_lean_command_injection_rejected(self):
        self.ledger['claims'][0]['lean_declarations'] = ['Proof.first]\n#eval 0']
        with self.assertRaisesRegex(ValueError,'Invalid Lean'):
            requested_roots(self.ledger)

    def message(self,name='Proof.first',type='True'):
        return json.dumps({'severity':'information','data':'CERTIFICATION_TYPE '+
                           json.dumps({'name':name,'type':type,'kind':'theorem'})})

    def test_complete_export(self):
        result = parse_types(self.message(),['Proof.first'])
        self.assertEqual(result[0]['name'],'Proof.first')

    def test_missing_type_rejected(self):
        with self.assertRaisesRegex(ValueError,'roots differ'):
            parse_types(self.message(),['Proof.first','Proof.second'])

    def test_duplicate_type_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate'):
            parse_types(self.message()+'\n'+self.message(),['Proof.first'])

    def test_empty_type_rejected(self):
        with self.assertRaisesRegex(ValueError,'empty'):
            parse_types(self.message(type=''),['Proof.first'])

    def test_lean_error_rejected_even_with_type(self):
        error = json.dumps({'severity':'error','data':'Missing kernel declaration'})
        with self.assertRaisesRegex(ValueError,'Lean rejected'):
            parse_types(self.message()+'\n'+error,['Proof.first'])


if __name__ == '__main__':
    unittest.main()
