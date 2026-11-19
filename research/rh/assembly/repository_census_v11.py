#!/usr/bin/env python3
"""Convert source-only AEGIS v1/preflight census into conservative v1.1.

No field in this adapter establishes a Lean kernel proof or RH verdict.
"""
from __future__ import annotations
import argparse
import datetime
import json
import pathlib
import re


def normalize_repo(repo):
    m=re.fullmatch(r'(?:https://github\.com/|git@github\.com:)([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+?)(?:\.git|/)?',repo)
    return m.group(1) if m else repo

SHA = re.compile(r'^[0-9a-f]{40}$')


def temporal(observed=None, statement=None, status='UNKNOWN'):
    return dict(normative_effect_at=None,known_to_evaluator_at=observed,
                forensically_admissible_at=None,temporal_status=status,
                statement_as_recorded=statement)


def ref(head, repo, path, artifact_id, sha1=None, role='SOURCE', status='UNKNOWN'):
    return dict(artifact_id=artifact_id,repository=repo,exact_head_sha=head,path=path,
                content_sha256=None,git_blob_sha1=sha1 if sha1 and SHA.fullmatch(sha1) else None,
                evidence_role=role,verification_status=status)


def convert(v1, repository=None, head=None):
    prov=v1.get('provenance',{})
    root=v1.get('repository',{})
    if isinstance(root,str):root={'name':root}
    repo=normalize_repo(repository or prov.get('repo') or root.get('name') or 'UNKNOWN')
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',repo):
        raise ValueError('CANONICAL_REPOSITORY_OWNER_NAME_REQUIRED')
    kernel_record=v1.get('kernel_inventory_summary',{})
    if kernel_record.get('status')=='EXACT_HEAD_LEAN_EXPORT_BUNDLE_VERIFIED' or v1.get('kernel_reachable_declaration_inventory'):
        raise ValueError('VERIFIED_KERNEL_EVIDENCE_REQUIRES_NONLOSSY_V11_IMPORT')
    head=head or prov.get('exact_head') or root.get('exact_head')
    if not head or not SHA.fullmatch(head):raise ValueError('EXACT_HEAD_SHA_REQUIRED')
    observed=v1.get('generated_at_utc') or v1.get('generated_at')
    if not observed:raise ValueError('GENERATION_TIME_REQUIRED')
    source_mods=[]
    for row in v1.get('module_inventory',[]):
        if not isinstance(row,dict):raise ValueError('INVALID_MODULE_ROW')
        path=row['path'];sha=row.get('sha256');blob=row.get('blob_sha1')
        if not sha or not blob:raise ValueError('MODULE_SOURCE_HASH_MISSING:'+path)
        source_mods.append(dict(path=path,source_sha256=sha,git_blob_sha1=blob,
            imports=row.get('imports_source',[]),declaration_occurrences=row.get('source_declaration_occurrences'),
            provenance='TRACKED_SOURCE',namespace_candidate=row.get('module_name_candidate')))
    source_decl=[]
    for row in v1.get('declaration_inventory',[]):
        if 'module_path' not in row:continue  # Older preflight observations are not file-enumerated declarations.
        source_decl.append(dict(source_local_name=row.get('source_local_name'),kind=row['kind'],
           module_path=row['module_path'],line=row['line'],verification='SOURCE_SYNTAX_ONLY',
           declared_axioms=None,formal_dependencies=None))
    is_complete=bool(source_mods and v1.get('source_counts',{}).get('tracked_lean_files') == len(source_mods))
    sc=v1.get('source_counts',{})
    paths=[];obs=[]
    raw_paths=v1.get('rh_path_inventory',[])
    for p in raw_paths:
        identifier=p['path_id']; e=p.get('evidence') or {}
        path=p.get('source') or (e.get('path') if isinstance(e,dict) else None)
        symbol=p.get('symbol') or (e.get('source_symbol') if isinstance(e,dict) else None)
        blob=p.get('git_blob') or (e.get('blob_sha1') if isinstance(e,dict) else None)
        refs=[ref(head,repo,path,f'path:{identifier}:source',blob)] if path else []
        state=p.get('status','UNKNOWN')
        if state not in ('ACTIVE','QUESTIONED','SUPERSEDED','REVOKED','UNKNOWN'):state='UNKNOWN'
        limitation=p.get('obligation') or p.get('classification') or 'No globally discharged proof obligation reported'
        paths.append(dict(path_id=identifier,temporal_status=state,proof_status='UNKNOWN',
          canonical_target='_root_.RiemannHypothesis',declared_endpoints=[symbol] if symbol else [],
          assumptions=[],blocks=[identifier+'_GLOBAL_GATE'],sources=refs,
          authority_ref=None,superseded_by=None,scientific_limitation=limitation))
        obs.append(dict(obligation_id=identifier+'_GLOBAL_GATE',statement=limitation,status='OPEN' if path else 'UNKNOWN',
          blocked_by=[],sources=refs,discharge_receipt=None,
          temporal=temporal(observed,limitation,'QUESTIONED' if state=='QUESTIONED' else 'ACTIVE'),
          route_ids=[identifier],counterexample_status='CANDIDATE' if state=='QUESTIONED' else 'UNKNOWN'))
    # Preserve explicit old preflight obligations without double-counting.
    observed_ids={x['obligation_id'] for x in obs}
    for old in v1.get('obligation_inventory',[]):
        oid=old['id']
        if oid in observed_ids:continue
        note=old.get('obligation','Unspecified historical obligation')
        path=old.get('source')
        obs.append(dict(obligation_id=oid,statement=note,status='UNKNOWN',blocked_by=old.get('blocked_by',[]),
           sources=[ref(head,repo,path,f'obligation:{oid}:source')] if path else [],discharge_receipt=None,
           temporal=temporal(observed,note),route_ids=[],counterexample_status='UNKNOWN'))
    orig_auth=v1.get('authority_inventory',[])
    auth=[]
    for a in orig_auth:
        if not isinstance(a,dict) or not a.get('artifact'):continue
        current=bool(a.get('current_authority')) and a['artifact']!='repository_census.json'
        # Metadata such as a supersedes text does not establish an executable authority transition.
        auth.append(dict(artifact_id=a['artifact'],current_authority=current,authority_source=None,
            supersedes=[],superseded_by=None,temporal=temporal(observed,a.get('scope')),
            authority_scope=a.get('scope') or 'Unspecified non-admission authority',
            admission_eligibility='HOLD'))
    totals={'total_modules':sc.get('tracked_lean_files') if is_complete else None,
       'total_declarations':None,'total_theorems':None,'total_axioms':None,'total_rh_related_declarations':None}
    active=[p['path_id'] for p in paths if p['temporal_status']=='ACTIVE']
    questioned=[p['path_id'] for p in paths if p['temporal_status']=='QUESTIONED']
    superseded=[p['path_id'] for p in paths if p['temporal_status']=='SUPERSEDED']
    gin=v1.get('branch_inventory_summary',{})
    return dict(schema='aegis.rh.repository-census',version='1.1.0',generated_at=observed,
      repository={'full_name':repo,'repository_id':None},exact_head_sha=head,
      census_policy=dict(unknown_counts_must_be_null=True,estimates_forbidden=True,
          source_facts_separate_from_kernel_facts=True,kernel_facts_separate_from_rh_verdict=True,
          rh_admission_source='RH_EVIDENCE_PASSPORT',scope='SOURCE_ONLY',
          declared_exclusions=['No complete Lean environment replay','No all-history commit census']),
      preservation_policy=dict(preserve_temporal_voice=True,preserve_semantic_ancestry=True,
          preserve_evidentiary_contribution=True,authority_change_does_not_delete_history=True,
          immutable_source_receipts=True,no_unproven_admission=True),
      bitemporal_metadata=temporal(observed,'Source-only census; not RH verdict'),
      authority_lineage=auth,semantic_ancestry=[],sources=[],
      git_inventory=dict(coverage='PARTIAL' if gin.get('state')=='VERIFIED_SOURCE_GRAPH_ONLY' else 'NOT_ASSESSED',
          total_commits=None,total_prs=(gin.get('counts') or {}).get('prs') if gin.get('state')=='VERIFIED_SOURCE_GRAPH_ONLY' else None,
          total_branches=(gin.get('counts') or {}).get('live_branches') if gin.get('state')=='VERIFIED_SOURCE_GRAPH_ONLY' else None,
          total_source_trees=(gin.get('counts') or {}).get('rh_trees_fetched') if gin.get('state')=='VERIFIED_SOURCE_GRAPH_ONLY' else None,
          commits=[],branches=[],source_graph=None,historical_commit_census_complete=False,
          note='All PR/branch heads are not every historical commit'),
      source_inventory=dict(coverage='COMPLETE' if is_complete else 'NOT_ASSESSED',
          total_modules=totals['total_modules'],source_declaration_occurrences=sc.get('source_declaration_occurrences') if is_complete else None,
          source_theorem_occurrences=sc.get('source_theorem_occurrences') if is_complete else None,
          source_axiom_occurrences=sc.get('source_axiom_occurrences') if is_complete else None,
          rh_related_source_occurrences=sc.get('rh_related_source_declaration_occurrences') if is_complete else None,
          modules=source_mods,declarations=source_decl,source_only=True),
      kernel_inventory=dict(coverage='NOT_ASSESSED',total_declarations=None,total_theorems=None,total_axioms=None,
          declarations=[],environment_receipt=None,lean_version=None,mathlib_sha=None,exact_replay_head=None,
          inference_limit='KERNEL_RESULTS_REQUIRE_EXACT_REPLAY'),
      theorem_inventory=dict(coverage='NOT_ASSESSED',total_theorems=None,theorems=[],kernel_verified_theorems=None,
          cross_repo_equivalences=[]),
      rh_inventory=dict(paths=paths,closed_canonical_rh_declarations=[],RH_PROVEN_UNCONDITIONALLY=None,
          rh_evidence_passport=None,canonical_admission=dict(status='UNKNOWN',verified_at=None,evidence_passport_id=None,
          verified_predicates=[]),current_rh_status='NOT_ASSESSED'),
      math_frontier=dict(open_obligations=[o for o in obs if o['status']=='OPEN'],closed_obligations=[],
          unknown_obligations=[o for o in obs if o['status']=='UNKNOWN'],scope='SELECTED_ROUTES_ONLY',frontier_evidence=[]),
      authority_inventory=dict(artifacts=auth,decisions=[],is_census_authority=False,
          rh_admission_authority='RH_EVIDENCE_PASSPORT',authority_register=None),
      summary=dict(**totals,active_rh_paths=active,questioned_rh_paths=questioned,superseded_rh_paths=superseded,
          open_obligations=len([o for o in obs if o['status']=='OPEN']) if obs else None,
          closed_obligations=None,current_rh_status='NOT_ASSESSED',
          census_completeness='PARTIAL' if is_complete else 'NOT_ASSESSED',
          limitations=['Source syntax is not formal Lean declaration authority',
            'An RH proof is not established by this census'],non_proof_statement='CENSUS_IS_NOT_RH_ADMISSION'))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=pathlib.Path,required=True)
    ap.add_argument('--output',type=pathlib.Path,required=True)
    a=ap.parse_args()
    result=convert(json.loads(a.source.read_text()))
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+'\n')
    print('CENSUS_V11_GENERATED SOURCE_ONLY',result['exact_head_sha'])

if __name__=='__main__':main()
