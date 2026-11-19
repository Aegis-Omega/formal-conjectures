#!/usr/bin/env python3
"""Join two exact-head GitHub Actions receipts into a bounded v1.1 census.

Inputs: the native source-census ZIP and cofinal Lean audit ZIP. Never upgrades
source occurrences to kernel declarations or a RH proof, and never infers
all-history coverage from the current imported Lean environment.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import pathlib
import re
import zipfile
from contextlib import contextmanager

SHA256=re.compile(r'^[a-f0-9]{64}$')
STANDARD_AXIOMS={'propext','Classical.choice','Quot.sound'}
CANONICAL='RiemannHypothesis.riemannHypothesis'

class DirectoryArtifact:
    """Read a CI working directory, never a user-controlled absolute path."""
    def __init__(self,path): self.root=path.resolve()
    def _file(self,name):
        p=(self.root/name).resolve()
        if not p.is_relative_to(self.root) or not p.is_file() or p.is_symlink():
            raise ValueError('UNSAFE_OR_MISSING_LOCAL_ARTIFACT:'+name)
        return p
    def read(self,name):return self._file(name).read_bytes()
    def open(self,name):return self._file(name).open('rb')

@contextmanager
def artifact_reader(path):
    if path.is_dir():yield DirectoryArtifact(path)
    else:
        with zipfile.ZipFile(path) as zipdata:yield zipdata


def sha256_stream(stream):
    h=hashlib.sha256()
    for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()


def sha_file(path):
    with path.open('rb') as f:return sha256_stream(f)


def load(z,path):
    return json.loads(z.read(path))


def git_source(path,sha,repo,head,role='KERNEL'):
    return dict(artifact_id=path,repository=repo,exact_head_sha=head,
       path=path,content_sha256=sha,git_blob_sha1=None,
       evidence_role=role,verification_status='VERIFIED',
       content_kind='GitHub Actions immutable artifact; exact run and SHA recorded externally')


def iter_kernel_rows(z):
    """Stream huge JSON array, materializing one declaration at a time, not 500MB."""
    found=False;collect=False;buf=[]
    with z.open('assembly/repository_census.json') as fp:
        for raw in fp:
            line=raw.decode('utf-8')
            if not found:
                if line.strip()=='"kernel_reachable_declaration_inventory": [':found=True
                continue
            if line=="  ],\n":
                if collect:raise ValueError('UNTERMINATED_KERNEL_ROW')
                return
            if line=="    {\n":
                if collect:raise ValueError('NESTED_ROW_AT_TOP_LEVEL')
                buf=[line];collect=True
            elif collect:
                buf.append(line)
                if line in ("    },\n","    }\n"):
                    row=json.loads(''.join(buf).rstrip().rstrip(','))
                    yield row
                    buf=[];collect=False
    raise ValueError('KERNEL_ROWS_MISSING_OR_UNTERMINATED')


def merge(source_zip,kernel_zip,expected_source_sha,expected_kernel_sha):
    # A remote Actions ZIP must be verified against its GitHub-reported digest;
    # a local working tree is permitted only for files produced by this same job.
    for path,expected,label in ((source_zip,expected_source_sha,'SOURCE'),
                                (kernel_zip,expected_kernel_sha,'KERNEL')):
        if path.is_dir():
            if expected is not None:raise ValueError(label+'_DIRECTORY_CANNOT_HAVE_ZIP_DIGEST')
        else:
            if not isinstance(expected,str) or not SHA256.fullmatch(expected):
                raise ValueError('REQUIRE_FULL_ZIP_SHA256_RECEIPTS')
            if sha_file(path)!=expected:raise ValueError(label+'_ZIP_DIGEST_MISMATCH')
    with artifact_reader(source_zip) as src,artifact_reader(kernel_zip) as proof:
        s=load(src,'repository_census_v1.1.json')
        base=load(src,'repository_census.json')
        passport=load(proof,'assembly/RH_EVIDENCE_PASSPORT.json')
        env=load(proof,'assembly/environment-rh-candidates.json')
        blocker=load(proof,'assembly/RH_BLOCKER.json')
        official=load(proof,'assembly/RH_OFFICIAL_SUBMISSION.json')
        head=s['exact_head_sha'];repo=s['repository']['full_name']
        if (head!=base['repository']['exact_head'] or head!=passport['exact_replay_sha']
            or head!=passport['active_integration_target']['exact_sha']
            or head!=official['exact_head'] or
            base['kernel_inventory_summary']['status']!='UNKNOWN'):
            raise ValueError('CROSS_ARTIFACT_HEAD_OR_STATUS_MISMATCH')
        if s['kernel_inventory']['coverage']!='NOT_ASSESSED':
            raise ValueError('SOURCE_CENSUS_ALREADY_KERNEL_CLAIMED')
        if s['summary']['total_declarations'] is not None:
            raise ValueError('SOURCE_ALREADY_KERNEL_COUNTED')
        info=json.loads(src.read('pr_branch_coherence.json'))
        if info['target_exact_sha']!=head or info['inventory_complete'] is not True:
            raise ValueError('PR_GRAPH_MISMATCH_OR_INCOMPLETE')
        if (not isinstance(passport['root_coverage']['root_count'],int) or
            passport['root_coverage']['root_count']<=0 or
            passport['root_coverage']['resolved_root_count']!=passport['root_coverage']['root_count']):
            raise ValueError('ROOT_COVERAGE_MISMATCH')
        if sha256_stream(proof.open('assembly/proof-terms.json')) != passport['proof_term_graph_sha256']:
            raise ValueError('PROOF_TERMS_HASH_MISMATCH')
        passport_hash=hashlib.sha256(proof.read('assembly/RH_EVIDENCE_PASSPORT.json')).hexdigest()
        env_hash=hashlib.sha256(proof.read('assembly/environment-rh-candidates.json')).hexdigest()
        cohort=load(proof,'assembly/RH_OFFICIAL_SUBMISSION.json')
        if cohort['imported_environment_sha256']!=env_hash:raise ValueError('ENVIRONMENT_HASH_MISMATCH')
        if (env['inspected_count']!=env['semantic_declarations_checked'] or
            env['inspected_count']<env['semantic_theorems_checked'] or
            passport['rh_closure_scan']['imported_environment_declaration_count']!=env['inspected_count'] or
            passport['rh_closure_scan']['reachable_declaration_count']<=0):
            raise ValueError('KERNEL_COUNT_INCONSISTENT')
        roots=passport.get('new_candidate_axioms')
        if not isinstance(roots,dict) or len(roots)!=passport['root_coverage']['root_count']:
            raise ValueError('ROOT_LIST_MISMATCH')
        wanted=set(roots);retained={};n=0;ids=set()
        for row in iter_kernel_rows(proof):
            key=row.get('declaration');n+=1
            if not isinstance(key,str) or key in ids:raise ValueError('DUPLICATE_KERNEL_IDENTIFIER')
            ids.add(key)
            if key in wanted:
                if row['axioms']!=roots[key]:raise ValueError('ROOT_AXIOMS_DO_NOT_MATCH_PASSPORT:'+key)
                retained[key]=row
        if n!=passport['rh_closure_scan']['reachable_declaration_count'] or len(retained)!=len(roots):
            raise ValueError('INCOMPLETE_KERNEL_DEPENDENCY_SCAN')
        rh_candidates=env['declarations']
        if (not isinstance(rh_candidates,list) or
            passport['rh_closure_scan']['imported_environment_rh_type_candidates']!=len(rh_candidates) or
            any(x.get('type_defeq_riemann_hypothesis') is not True for x in rh_candidates)):
            raise ValueError('CANONICAL_RH_EVIDENCE_CONFLICT')
        # A census never promotes RH. If a newer kernel actually finds a closed
        # candidate, the independent RH_EVIDENCE_PASSPORT admission flow owns it.
        if official.get('ready_for_official_submission') is True:
            raise ValueError('ADMISSION_REQUIRES_INDEPENDENT_GATE')
        if official.get('ready_for_official_submission') is not False:
            raise ValueError('UNEXPECTED_OFFICIAL_ADMISSION')
        result=copy.deepcopy(s)
        proofref=git_source('assembly/RH_EVIDENCE_PASSPORT.json',passport_hash,repo,head,'RH_EVIDENCE_PASSPORT')
        envref=git_source('assembly/environment-rh-candidates.json',env_hash,repo,head,'KERNEL')
        result['sources'].extend([
          dict(source_id='cofinal-current-evidence-passport',reference=proofref,
               source_kind='EVIDENCE_PASSPORT',claims_supported=[f'{len(retained)} root audits','exact-head proof closure','canonical RH OPEN'],time_basis=None),
          dict(source_id='cofinal-current-environment-census',reference=envref,
               source_kind='LEAN_ENVIRONMENT',claims_supported=[
                   f"{env['inspected_count']} imported declarations",
                   f"{env['semantic_theorems_checked']} theorem declarations",
                   f"{len(env['declarations'])} canonical RH candidates"
               ],time_basis=None)])
        kernel_rows=[];theorem_rows=[];approved=0
        for key,row in sorted(retained.items()):
            standard=bool(row['has_body'] and not row['is_axiom'] and set(row['axioms'])<=STANDARD_AXIOMS)
            if standard:approved+=1
            k=dict(identifier=key,module=row['module'],kind='axiom' if row['is_axiom'] else 'body_bearing',
                type_expr=row['type_expr'],axioms=row['axioms'],direct_dependencies=row['dependencies'],
                has_body=row['has_body'],kernel_status='VERIFIED' if standard else 'UNKNOWN',
                artifact=proofref.copy(),no_sorry_ax=standard,type_defeq_riemann_hypothesis=None)
            kernel_rows.append(k)
            theorem_rows.append(dict(identifier=key,module=row['module'],statement=row['type_expr'],
                proof_status='VERIFIED' if standard else 'UNKNOWN',dependency_identifiers=row['dependencies'],
                evidence=[proofref.copy()],axioms=row['axioms'],proved_at=passport.get('recorded_at'),
                math_statement_equivalence_verified=None,assumptions=[]))
        result['kernel_inventory'].update(dict(coverage='PARTIAL',total_declarations=env['inspected_count'],
             total_theorems=env['semantic_theorems_checked'],total_axioms=None,
             declarations=kernel_rows,environment_receipt=envref,
             lean_version=passport['lean_version'],mathlib_sha=passport['mathlib_sha'],
             exact_replay_head=head))
        result['theorem_inventory'].update(dict(coverage='PARTIAL',total_theorems=env['semantic_theorems_checked'],
            theorems=theorem_rows,kernel_verified_theorems=None))
        result['census_policy']['scope']='PARTIAL_KERNEL'
        result['census_policy']['declared_exclusions'].extend([
            f'Only {len(kernel_rows)} of {n} reachable declarations individually materialized in v1.1 kernel rows',
            'Environment totals include Mathlib and imports; not AEGIS-only or historical totals',
            'RH admission is controlled by the independent passport and official gate, not this census'])
        result['rh_inventory']['rh_evidence_passport']=proofref
        result['rh_inventory']['current_rh_status']='OPEN'
        result['rh_inventory']['canonical_admission']['status']='HOLD'
        result['rh_inventory']['RH_PROVEN_UNCONDITIONALLY']=None
        # Imported-environment counts are NOT repository or all-history totals.
        result['summary'].update(total_declarations=None,
            total_theorems=None,total_axioms=None,current_rh_status='OPEN')
        result['summary']['limitations'].extend([
            'Kernel counts scoped to compiled/imported Lean environment on pinned exact HEAD',
            f'{len(kernel_rows)} selected root declarations materialized; {n} dependencies indexed in original certified graph',
            'Canonical RH submission requires the independent gate; census does not decide RH'])
        result['summary']['census_completeness']='PARTIAL'
        # Provenance is head-bound, but a passport is evidence rather than a sovereign admission decision.
        result['bitemporal_metadata']['statement_as_recorded']='Source census and exact-head imported Lean evidence, RH admission HOLD'
        result['generated_at']=passport['recorded_at']
        return result,dict(exact_head=head,source_zip_sha256=expected_source_sha,kernel_zip_sha256=expected_kernel_sha,
            passport_sha256=passport_hash,environment_sha256=env_hash,
            source_declarations=s['source_inventory']['source_declaration_occurrences'],
            imported_environment_declarations=env['inspected_count'],imported_environment_theorems=env['semantic_theorems_checked'],
            reachable_declarations=n,materialized_roots=len(kernel_rows),root_standard_axiom_pass=approved,
            canonical_rh_candidate_axioms={x['identifier']:x.get('axioms') for x in rh_candidates},rh_admission='HOLD')


def main():
    a=argparse.ArgumentParser()
    a.add_argument('--source-zip',type=pathlib.Path,required=True)
    a.add_argument('--kernel-zip',type=pathlib.Path,required=True)
    a.add_argument('--source-zip-sha256',required=True)
    a.add_argument('--kernel-zip-sha256',required=True)
    a.add_argument('--output',type=pathlib.Path,required=True)
    a.add_argument('--receipt',type=pathlib.Path,required=True)
    args=a.parse_args()
    result,receipt=merge(args.source_zip,args.kernel_zip,args.source_zip_sha256,args.kernel_zip_sha256)
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
    args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print('CENSUS_KERNEL_CROSS_EVIDENCE_PASS',receipt)

if __name__=='__main__':main()
