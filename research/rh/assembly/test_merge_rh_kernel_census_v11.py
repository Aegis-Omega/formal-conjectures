#!/usr/bin/env python3
"""Small, independent regression checks for exact-head kernel/source census joins."""
import json
import pathlib
import tempfile
import unittest
import sys
import zipfile
import merge_rh_kernel_census_v11 as m

ROOT=pathlib.Path(__file__).resolve().parent
SOURCE=ROOT/'census_current_head_266414e.zip'
KERNEL=ROOT/'cofinal_current_head_266414e.zip'
SHAS='bc49536e6568de0f89f5495cd8e2c5e59d49aa9cff55498d1dec46aec64d1680'
SHAK='9e63de8692a1f6e8c701b5985e2dbe0eb199605a641aa81a632c114e61e28165'

class TestMerge(unittest.TestCase):
    @unittest.skipUnless(SOURCE.is_file() and KERNEL.is_file(),'private large CI fixtures unavailable')
    def test_real_end_to_end_sha_verification(self):
        r,receipt=m.merge(SOURCE,KERNEL,SHAS,SHAK)
        self.assertEqual(r['census_policy']['scope'],'PARTIAL_KERNEL')
        self.assertEqual(r['kernel_inventory']['coverage'],'PARTIAL')
        self.assertIsNone(r['summary']['total_declarations'])
        self.assertEqual(len(r['kernel_inventory']['declarations']),receipt['materialized_roots'])
        self.assertEqual(receipt['materialized_roots'],receipt['root_standard_axiom_pass'])
        self.assertGreater(receipt['reachable_declarations'],receipt['materialized_roots'])
        self.assertIsNone(r['rh_inventory']['RH_PROVEN_UNCONDITIONALLY'])
        self.assertEqual(r['rh_inventory']['canonical_admission']['status'],'HOLD')
        self.assertIn('sorryAx',receipt['canonical_rh_candidate_axioms']['RiemannHypothesis.riemannHypothesis'])
        sys.path.insert(0,str(ROOT))
        from validate_repository_census_v11 import validate
        schema=json.loads((ROOT/'repository-census.schema.json').read_text())
        self.assertEqual(validate(r,schema),[])
    @unittest.skipUnless(SOURCE.is_file() and KERNEL.is_file(),'private large CI fixtures unavailable')
    def test_wrong_source_digest_fails(self):
        with self.assertRaisesRegex(ValueError,'SOURCE_ZIP_DIGEST_MISMATCH'):
            m.merge(SOURCE,KERNEL,'0'*64,SHAK)
    @unittest.skipUnless(SOURCE.is_file() and KERNEL.is_file(),'private large CI fixtures unavailable')
    def test_wrong_kernel_digest_fails(self):
        with self.assertRaisesRegex(ValueError,'KERNEL_ZIP_DIGEST_MISMATCH'):
            m.merge(SOURCE,KERNEL,SHAS,'1'*64)
    def test_invalid_digest_format_fails(self):
        with self.assertRaisesRegex(ValueError,'REQUIRE_FULL_ZIP_SHA256_RECEIPTS'):
            m.merge(SOURCE,KERNEL,'abc',SHAK)
    def test_stream_parser_requires_kernel_rows(self):
        with tempfile.NamedTemporaryFile(suffix='.zip') as f:
            with zipfile.ZipFile(f.name,'w') as z:
                z.writestr('assembly/repository_census.json','{"kernel_reachable_declaration_inventory": []}')
            with zipfile.ZipFile(f.name) as z:
                with self.assertRaisesRegex(ValueError,'KERNEL_ROWS_MISSING_OR_UNTERMINATED'):
                    list(m.iter_kernel_rows(z))
    @unittest.skipUnless(SOURCE.is_file() and KERNEL.is_file(),'private large CI fixtures unavailable')
    def test_passport_nonpromotion_false_rh(self):
        # Direct control over the in-memory RH admission boundary is tested
        # with the independently verified result rather than synthetic proof.
        obj=json.loads((ROOT/'repository_census_v1.1_kernel_bound.json').read_text())
        obj['rh_inventory']['RH_PROVEN_UNCONDITIONALLY']=True
        sys.path.insert(0,str(ROOT))
        from validate_repository_census_v11 import validate
        schema=json.loads((ROOT/'repository-census.schema.json').read_text())
        self.assertTrue(any('closed_canonical_rh_declarations' in x or 'canonical_admission' in x for x in validate(obj,schema)))

if __name__=='__main__':unittest.main(verbosity=2)
