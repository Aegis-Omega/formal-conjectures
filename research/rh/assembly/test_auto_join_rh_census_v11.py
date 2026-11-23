#!/usr/bin/env python3
"""Read-only artifact discovery and automatic evidence join regressions."""
import json
import pathlib
import shutil
import tempfile
import unittest
import zipfile
from unittest.mock import patch

import auto_join_rh_census_v11 as a

HERE=pathlib.Path(__file__).parent
HEAD='266414e97274323bfdc59bd1426913967d2c5348'
SZIP=HERE/'census_current_head_266414e.zip'
KZIP=HERE/'cofinal_current_head_266414e.zip'
SHAK='9e63de8692a1f6e8c701b5985e2dbe0eb199605a641aa81a632c114e61e28165'
SHAS='bc49536e6568de0f89f5495cd8e2c5e59d49aa9cff55498d1dec46aec64d1680'

class TestAutoJoin(unittest.TestCase):
 def test_selector_rejects_unfinished_wrong_sha_and_expired(self):
  obj={
   'workflow_runs':[
    dict(id=8,head_sha='a'*40,name=a.SOURCE_WORKFLOW,status='completed',conclusion='success'),
    dict(id=9,head_sha=HEAD,name=a.SOURCE_WORKFLOW,status='in_progress',conclusion=None),
    dict(id=10,head_sha=HEAD,name=a.SOURCE_WORKFLOW,status='completed',conclusion='success')]
  }
  artifact=dict(id=55,name='rh-all-pr-source-graph-10-1',digest='sha256:'+SHAS,
                expired=False,workflow_run=dict(head_sha=HEAD,id=10))
  def api(repo,token,path):
   return obj if 'actions/runs?' in path else dict(artifacts=[dict(artifact,expired=True),artifact])
  with patch.object(a,'api',side_effect=api):
   run,found,digest=a.select_artifact('test/repo','unused',HEAD,a.SOURCE_WORKFLOW)
  self.assertEqual((run['id'],found['id'],digest),(10,55,SHAS))
 def test_not_ready_keeps_hold_without_join(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);(root/'evidence-cofinal').mkdir()
   with patch.object(a.subprocess,'check_output',return_value=HEAD),patch.object(a,'select_artifact',return_value=None):
    r=a.do_join('kernel-local','test/repo',HEAD,'unused',root/'output',root)
   self.assertEqual(r['status'],'COUNTERPART_NOT_READY')
   self.assertFalse((root/'output'/'repository_census_v1.1_kernel_bound.json').exists())
 def test_exact_head_mismatch_fails_before_api(self):
  with tempfile.TemporaryDirectory() as tmp:
   with patch.object(a.subprocess,'check_output',return_value='0'*40):
    with self.assertRaisesRegex(ValueError,'CHECKOUT_SHA_MISMATCH'):
     a.do_join('source-local','test/repo',HEAD,'unused',pathlib.Path(tmp)/'out',pathlib.Path(tmp))
 @unittest.skipUnless(SZIP.is_file() and KZIP.is_file(),'private large CI fixtures unavailable')
 def test_original_receipts_reconcile_in_automatic_source_local_path(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp)
   with zipfile.ZipFile(SZIP) as z:z.extractall(root)
   path=root/'research/rh/assembly';path.mkdir(parents=True)
   shutil.copyfile(HERE/'repository-census.schema.json',path/'repository-census.schema.json')
   run=dict(id=41164475149)
   artifact=dict(id=13030100108,digest='sha256:'+SHAK)
   def local_copy(repo,token,artifact,expected,destination):
    self.assertEqual(expected,SHAK)
    shutil.copyfile(KZIP,destination)
    return expected
   with patch.object(a.subprocess,'check_output',return_value=HEAD),patch.object(a,'select_artifact',return_value=(run,artifact,SHAK)),patch.object(a,'retrieve_verified',side_effect=local_copy):
    receipt=a.do_join('source-local','Aegis-Omega/formal-conjectures',HEAD,'unused',root/'output',root)
   self.assertEqual(receipt['status'],'PASS')
   self.assertEqual(receipt['root_standard_axiom_pass'],receipt['materialized_roots'])
   out=json.loads((root/'output'/'repository_census_v1.1_kernel_bound.json').read_text())
   self.assertIsNone(out['summary']['total_declarations'])
   self.assertEqual(out['kernel_inventory']['exact_replay_head'],HEAD)
   self.assertIsNone(out['rh_inventory']['RH_PROVEN_UNCONDITIONALLY'])

if __name__=='__main__': unittest.main(verbosity=2)
