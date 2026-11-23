#!/usr/bin/env python3
"""Draft-07 plus cross-record invariants for AEGIS Repository Census v1.1.

Never treats validity of JSON as proof of its reported source or kernel facts.
"""
from __future__ import annotations
import argparse
from datetime import datetime
import json
from pathlib import Path
import sys
from jsonschema import Draft7Validator,FormatChecker

REQUIRED_RH_CHECKS={'EXACT_HEAD','LEAN_KERNEL','NO_SORRY_AX','CANONICAL_TYPE',
                    'ALLOWED_AXIOMS','DEPENDENCY_CLOSURE','PASSPORT_ATTESTED'}
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}


def check_semantics(d,previous=None):
    errors=[]
    def expect(pred,msg):
        if not pred:errors.append(msg)
    head=d['exact_head_sha'];s=d['summary'];source=d['source_inventory'];kernel=d['kernel_inventory']
    rh=d['rh_inventory'];frontier=d['math_frontier'];authority=d['authority_inventory']
    expect(d['repository']['full_name']!='UNKNOWN','REPOSITORY_IDENTITY_UNKNOWN')
    expect(s['total_modules']==source['total_modules'],'MODULE_COUNT_CONTRADICTION')
    expect((s['total_declarations'] is None and kernel['coverage'] != 'COMPLETE') or s['total_declarations']==kernel['total_declarations'], 'KERNEL_DECLARATION_COUNT_CONTRADICTION')
    expect((s['total_theorems'] is None and kernel['coverage'] != 'COMPLETE') or s['total_theorems']==kernel['total_theorems'], 'KERNEL_THEOREM_COUNT_CONTRADICTION')
    expect(s['total_axioms']==kernel['total_axioms'],'KERNEL_AXIOM_COUNT_CONTRADICTION')
    expect(s['current_rh_status']==rh.get('current_rh_status'),'RH_STATUS_CONTRADICTION')
    if source['coverage']=='COMPLETE':
        expect(source['total_modules']==len(source['modules']),'SOURCE_MODULES_NOT_ENUMERATED')
        expect(source['source_declaration_occurrences']==len(source['declarations']),
               'SOURCE_DECLARATION_COUNT_NOT_ENUMERATED')
        expect(source['source_theorem_occurrences']==sum(x['kind']=='theorem' for x in source['declarations']),
               'SOURCE_THEOREM_COUNT_NOT_ENUMERATED')
        expect(source['source_axiom_occurrences']==sum(x['kind']=='axiom' for x in source['declarations']),
               'SOURCE_AXIOM_COUNT_NOT_ENUMERATED')
    if kernel['coverage']=='COMPLETE':
        expect(kernel['total_declarations']==len(kernel['declarations']),'KERNEL_DECLARATION_INVENTORY_INCOMPLETE')
        expect(kernel['exact_replay_head']==head,'KERNEL_HEAD_MISMATCH')
    for name,seen,which in [('active_rh_paths',s['active_rh_paths'],'ACTIVE'),
      ('questioned_rh_paths',s['questioned_rh_paths'],'QUESTIONED'),
      ('superseded_rh_paths',s['superseded_rh_paths'],'SUPERSEDED')]:
        expected={p['path_id'] for p in rh['paths'] if p['temporal_status']==which}
        expect(len(seen)==len(set(seen)) and set(seen)==expected,name.upper()+'_INCONSISTENT')
    paths=[p['path_id'] for p in rh['paths']]
    expect(len(paths)==len(set(paths)),'DUPLICATE_RH_PATH_ID')
    allobs=frontier['open_obligations']+frontier['closed_obligations']+frontier['unknown_obligations']
    ids=[o['obligation_id'] for o in allobs]
    expect(len(ids)==len(set(ids)),'DUPLICATE_MATH_OBLIGATION_ID')
    for group,state in [('open_obligations','OPEN'),('closed_obligations','VERIFIED'),('unknown_obligations','UNKNOWN')]:
        for o in frontier[group]:
            expect(o['status']==state,'OBLIGATION_GROUP_STATUS_MISMATCH '+o['obligation_id'])
            if state=='VERIFIED':expect(o['discharge_receipt'] is not None,'CLOSED_OBLIGATION_MISSING_RECEIPT '+o['obligation_id'])
    for label,group in [('open_obligations','open_obligations'),('closed_obligations','closed_obligations')]:
        n=s[label]
        if n is not None:expect(n==len(frontier[group]),'OBLIGATION_SUMMARY_COUNT_CONTRADICTION '+label)
    def check_ref(r):
        expect(r['exact_head_sha']==head or r['repository']!=d['repository']['full_name'],
               'SAME_REPO_ARTIFACT_HEAD_MISMATCH '+r['artifact_id'])
    for a in d['sources']:check_ref(a['reference'])
    for p in rh['paths']:
        for r in p['sources']:check_ref(r)
    for o in allobs:
        for r in o['sources']:check_ref(r)
    for dec in kernel['declarations']:
        check_ref(dec['artifact'])
        if dec['kernel_status']=='VERIFIED':
            expect(set(dec['axioms']) <= ALLOWED_AXIOMS,'UNEXPECTED_AXIOM '+dec['identifier'])
            expect(dec.get('no_sorry_ax') is True,'KERNEL_CLAIM_WITHOUT_SORRY_AUDIT '+dec['identifier'])
    if rh['RH_PROVEN_UNCONDITIONALLY'] is True:
        passport=rh['rh_evidence_passport'];adm=rh['canonical_admission'];closed=rh['closed_canonical_rh_declarations']
        expect(passport is not None and passport['verification_status']=='VERIFIED',
               'RH_ADMISSION_WITHOUT_VERIFIED_PASSPORT')
        if passport:
            expect(passport['repository']==d['repository']['full_name'] and passport['exact_head_sha']==head,
                   'RH_ADMISSION_PASSPORT_NOT_EXACT_HEAD')
            expect(adm['evidence_passport_id']==passport['artifact_id'],'RH_ADMISSION_PASSPORT_ID_MISMATCH')
        expect(set(adm['verified_predicates'])==REQUIRED_RH_CHECKS,'RH_ADMISSION_PREDICATES_INCOMPLETE')
        for dec in closed:
            expect(dec.get('type_defeq_riemann_hypothesis') is True,'RH_DECLARATION_WRONG_TYPE')
            expect(dec['kernel_status']=='VERIFIED' and dec.get('no_sorry_ax') is True,
                   'RH_DECLARATION_NOT_AXIOM_CLEAN')
            expect(set(dec['axioms']) <= ALLOWED_AXIOMS,'RH_DECLARATION_UNEXPECTED_AXIOMS')
        expect(s['current_rh_status']=='VERIFIED','RH_ADMISSION_SUMMARY_CONTRADICTION')
    elif s['current_rh_status']=='VERIFIED':expect(False,'RH_VERIFIED_WITHOUT_PASSPORT_ADMISSION')
    for lst in [d['authority_lineage'],authority['artifacts']]:
        names=[a['artifact_id'] for a in lst]
        expect(len(names)==len(set(names)),'DUPLICATE_AUTHORITY_ID')
        for a in lst:
            if a['artifact_id']=='repository_census.json':
                expect(not a['current_authority'],'CENSUS_CANNOT_DECLARE_ITSELF_AUTHORITY')
            if a['temporal']['temporal_status'] in ('SUPERSEDED','QUESTIONED','REVOKED'):
                expect(bool(a['temporal']['statement_as_recorded']),
                       'LOST_HISTORICAL_STATEMENT '+a['artifact_id'])
    ancestry=d['semantic_ancestry'];graph={a['artifact_id']:a for a in ancestry}
    expect(len(graph)==len(ancestry),'DUPLICATE_SEMANTIC_ANCESTRY_ID')
    for a in ancestry:
        for parent in a['semantic_parents']:
            if parent in graph:expect(a['artifact_id'] in graph[parent]['semantic_children'],
                'SEMANTIC_PARENT_BACKLINK_MISSING '+a['artifact_id'])
        for child in a['semantic_children']:
            if child in graph:expect(a['artifact_id'] in graph[child]['semantic_parents'],
                'SEMANTIC_CHILD_BACKLINK_MISSING '+a['artifact_id'])
    if previous:
        old={x['artifact_id']:x for x in previous['authority_lineage']}
        current={x['artifact_id']:x for x in d['authority_lineage']}
        for artifact,a in old.items():
            expect(artifact in current,'HISTORY_ERASED '+artifact)
            if artifact in current:
                expect(a['temporal']['statement_as_recorded']==current[artifact]['temporal']['statement_as_recorded'],
                       'HISTORICAL_VOICE_CHANGED '+artifact)
        oldanc={x['artifact_id']:x for x in previous['semantic_ancestry']}
        newanc={x['artifact_id']:x for x in ancestry}
        for artifact,a in oldanc.items():
            expect(artifact in newanc,'SEMANTIC_ANCESTRY_ERASED '+artifact)
            if artifact in newanc:
                expect(set(a['semantic_parents'])<=set(newanc[artifact]['semantic_parents']),
                       'SEMANTIC_PARENT_REMOVED '+artifact)
                expect(set(a['responds_to'])<=set(newanc[artifact]['responds_to']),
                       'SEMANTIC_RESPONSE_REMOVED '+artifact)
    return errors


def validate(d,schema,previous=None):
    Draft7Validator.check_schema(schema)
    errors=[f'SCHEMA {"/".join(map(str,e.absolute_path))}: {e.message}'
            for e in Draft7Validator(schema,format_checker=FormatChecker()).iter_errors(d)]
    if not errors:
        errors+=check_semantics(d,previous)
    return sorted(errors)


def main():
    a=argparse.ArgumentParser()
    a.add_argument('--schema',type=Path,required=True)
    a.add_argument('--input',type=Path,required=True)
    a.add_argument('--previous',type=Path)
    x=a.parse_args()
    data=json.loads(x.input.read_text());schema=json.loads(x.schema.read_text());previous=json.loads(x.previous.read_text()) if x.previous else None
    errors=validate(data,schema,previous)
    print(json.dumps({'status':'PASS' if not errors else 'FAIL','errors':errors,'schema_version':'1.1.0','head':data.get('exact_head_sha')},indent=2))
    return int(bool(errors))

if __name__=='__main__':sys.exit(main())
