#!/usr/bin/env python3
"""Run precise positive and negative census v1.1 admission and preservation tests."""
import copy,json,sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from validate_repository_census_v11 import validate
from repository_census_v11 import convert

S=json.load(open(Path(__file__).with_name('repository-census.schema.json')))
OLD={
 'provenance':{'repo':'Aegis-Omega/formal-conjectures','exact_head':'3465d59be4d295900c281a6176d43a40ad0ecba9'},
 'generated_at_utc':'2026-10-31T03:20:00+00:00',
 'rh_path_inventory':[{'path_id':'KREIN_TRANSPORT','status':'ACTIVE',
 'source':'AEGISOverlay/RHKreinMultiplicativeTransportV1.lean',
 'symbol':'every_moment_zero_packet_finite_actual_weil_partition',
 'git_blob':'d882947b11b1981bb7ed9daedcfc702f972627e2',
 'obligation':'Prove global mixed Weil bound'}],
 'authority_inventory':[{'artifact':'PR #92','current_authority':True,'scope':'integration only'},
                        {'artifact':'repository_census.json','current_authority':False,'scope':'not RH admission'}],
 'source_counts':{}
}
D=convert(OLD)

class CensusTests(unittest.TestCase):
    def assertRejected(self,d,expected,prev=None):
        errors=validate(d,S,prev)
        self.assertTrue(any(expected in x for x in errors),errors)
    def test_schema_is_draft_07(self):
        import jsonschema
        jsonschema.Draft7Validator.check_schema(S)
        self.assertEqual(S['$schema'],'http://json-schema.org/draft-07/schema#')
    def test_valid_source_only_preflight(self):self.assertEqual(validate(D,S),[])
    def test_cannot_fake_verified_rh(self):
        d=copy.deepcopy(D);d['rh_inventory']['RH_PROVEN_UNCONDITIONALLY']=True
        self.assertRejected(d,'should be non-empty')
    def test_cannot_fake_source_counts_as_kernel(self):
        d=copy.deepcopy(D);d['kernel_inventory']['total_declarations']=999
        self.assertRejected(d,'null')
    def test_unknown_count_negative(self):
        d=copy.deepcopy(D);d['summary']['total_modules']=-10
        self.assertRejected(d,'minimum')
    def test_loss_of_temporal_voice(self):
        d=copy.deepcopy(D);d['authority_lineage'][0]['temporal']['temporal_status']='REVOKED'
        d['authority_lineage'][0]['temporal']['statement_as_recorded']=None
        self.assertRejected(d,'LOST_HISTORICAL_STATEMENT')
    def test_pr_source_drift(self):
        d=copy.deepcopy(D);d['rh_inventory']['paths'][0]['sources'][0]['exact_head_sha']='a'*40
        self.assertRejected(d,'SAME_REPO_ARTIFACT_HEAD_MISMATCH')
    def test_path_summary_contradiction(self):
        d=copy.deepcopy(D);d['summary']['active_rh_paths']=[]
        self.assertRejected(d,'ACTIVE_RH_PATHS_INCONSISTENT')
    def test_unknown_admission_claim(self):
        d=copy.deepcopy(D);d['summary']['current_rh_status']='VERIFIED'
        self.assertRejected(d,'RH_STATUS_CONTRADICTION')
    def test_cannot_delete_old_authority_record(self):
        d=copy.deepcopy(D);d['authority_lineage']=d['authority_lineage'][1:]
        self.assertRejected(d,'HISTORY_ERASED',D)
    def test_cannot_delete_semantic_parent(self):
        d=copy.deepcopy(D);d['semantic_ancestry']=[{
          'artifact_id':'child','semantic_parents':['parent'],'semantic_children':[],
          'responds_to':[],'preserves_temporal_voice':True,
          'evidentiary_contribution':'record','temporal':D['bitemporal_metadata']}]
        old=copy.deepcopy(d);d['semantic_ancestry'][0]['semantic_parents']=[]
        self.assertRejected(d,'SEMANTIC_PARENT_REMOVED',old)
    def test_requires_closed_discharge_receipt(self):
        d=copy.deepcopy(D);d['math_frontier']['closed_obligations']=[copy.deepcopy(d['math_frontier']['open_obligations'][0])]
        d['math_frontier']['closed_obligations'][0]['status']='VERIFIED'
        d['math_frontier']['open_obligations']=d['math_frontier']['open_obligations'][1:]
        d['summary']['open_obligations']-=1
        self.assertRejected(d,'CLOSED_OBLIGATION_MISSING_RECEIPT')
    def test_no_census_as_admission_authority(self):
        d=copy.deepcopy(D);d['authority_inventory']['is_census_authority']=True
        self.assertRejected(d,'False')

if __name__=='__main__':unittest.main(verbosity=2)
