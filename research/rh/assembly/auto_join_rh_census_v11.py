#!/usr/bin/env python3
"""Join independently successful exact-head CI artifacts without rerunning Lean.

This utility is intentionally read-only against GitHub and cannot admit RH.
Missing counterpart evidence is recorded as NOT_READY, never as a proof failure.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import urllib.request
import urllib.parse
import zipfile

from merge_rh_kernel_census_v11 import merge

SOURCE_WORKFLOW='RH all-PR source graph (exact-head audit)'
KERNEL_WORKFLOW='RH cofinal actual Schur kernel join'
SHA=re.compile(r'^[a-f0-9]{40}$')
DIGEST=re.compile(r'^sha256:([a-f0-9]{64})$')


def api(repo,token,path):
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',repo):
        raise ValueError('BAD_REPOSITORY')
    url='https://api.github.com/repos/'+repo+'/'+path.lstrip('/')
    req=urllib.request.Request(url,headers={
        'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json',
        'User-Agent':'AEGIS-Exact-Head-Census-Join','X-GitHub-Api-Version':'2022-11-28'})
    with urllib.request.urlopen(req,timeout=40) as response:return json.load(response)


def select_artifact(repo,token,head,workflow_name):
    """Require a successful run and an unexpired, SHA-pinned native artifact."""
    for page in range(1,11):
        query=urllib.parse.urlencode({'head_sha':head,'event':'pull_request','per_page':100,'page':page})
        data=api(repo,token,'actions/runs?'+query)
        runs=data['workflow_runs']
        for run in runs:
            if (run.get('head_sha')!=head or run.get('name')!=workflow_name or
                    run.get('status')!='completed' or run.get('conclusion')!='success'):
                continue
            candidate=api(repo,token,f"actions/runs/{run['id']}/artifacts?per_page=100")
            for a in candidate.get('artifacts',[]):
                digest=a.get('digest') or ''
                wr=a.get('workflow_run') or {}
                if (a.get('expired') is False and DIGEST.fullmatch(digest) and
                    wr.get('head_sha')==head and wr.get('id')==run['id'] and
                    a.get('name','').startswith('rh-all-pr-source-graph-' if workflow_name==SOURCE_WORKFLOW else 'rh-cofinal-actual-schur-')):
                    return run,a,DIGEST.fullmatch(digest).group(1)
        if len(runs)<100:break
    return None


def retrieve_verified(repo,token,artifact,expected_sha,destination):
    """Use the GitHub Authorization header only with api.github.com.

    urllib's default HTTP redirects can forward authorization to a different
    host, so disable redirects before requesting the signed Actions ZIP URL.
    The signed download itself is fetched WITHOUT the GitHub token.
    """
    class NoRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self,req,fp,code,msg,headers,newurl):return None
    endpoint='https://api.github.com/repos/'+repo+'/actions/artifacts/'+str(artifact['id'])+'/zip'
    opener=urllib.request.build_opener(NoRedirect())
    request=urllib.request.Request(endpoint,headers={
        'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json',
        'User-Agent':'AEGIS-Exact-Head-Census-Join'})
    try:
        with opener.open(request,timeout=40) as r:
            if r.status!=200:raise ValueError('ARTIFACT_REDIRECT_MISSING')
            signed=r.url
    except urllib.error.HTTPError as ex:
        if ex.code not in (301,302,303,307,308):raise
        signed=ex.headers.get('Location')
    if not signed or urllib.parse.urlparse(signed).scheme!='https':
        raise ValueError('ARTIFACT_SIGNED_URL_INVALID')
    # Redirect host gets no API Authorization header.
    h=hashlib.sha256()
    with urllib.request.urlopen(urllib.request.Request(signed,headers={'User-Agent':'AEGIS-Census-Join'}),timeout=120) as src, destination.open('wb') as out:
        while chunk:=src.read(1024*1024):
            h.update(chunk);out.write(chunk)
    actual=h.hexdigest()
    if actual!=expected_sha:
        destination.unlink(missing_ok=True)
        raise ValueError('ARTIFACT_ZIP_SHA256_MISMATCH')
    if not zipfile.is_zipfile(destination):raise ValueError('ARTIFACT_ZIP_INVALID')
    return actual


def do_join(mode,repo,head,token,output_dir,checkout):
    if not SHA.fullmatch(head):raise ValueError('INVALID_EXACT_SHA')
    current=subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip()
    if current!=head:raise ValueError('CHECKOUT_SHA_MISMATCH')
    if mode=='kernel-local':
        local=checkout/'evidence-cofinal'
        other=SOURCE_WORKFLOW
    elif mode=='source-local':
        local=checkout
        other=KERNEL_WORKFLOW
    else:raise ValueError('UNKNOWN_MODE')
    if not local.is_dir():raise ValueError('LOCAL_EVIDENCE_MISSING')
    selected=select_artifact(repo,token,head,other)
    output_dir.mkdir(parents=True,exist_ok=True)
    status_path=output_dir/'census_auto_join_status.json'
    if selected is None:
        receipt={'status':'COUNTERPART_NOT_READY','exact_head':head,'mode':mode,
                 'counterpart_workflow':other,'RH_PROVEN_UNCONDITIONALLY':None,
                 'claim':'no kernel/census join performed, no RH admission'}
        status_path.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
        print('CENSUS_JOIN_COUNTERPART_NOT_READY',other,head)
        return receipt
    run,artifact,digest=selected
    with tempfile.TemporaryDirectory(prefix='rh-census-join-') as tmp:
        remote=Path(tmp)/'counterpart.zip'
        retrieve_verified(repo,token,artifact,digest,remote)
        source,proof=(remote,local) if mode=='kernel-local' else (local,remote)
        source_hash,kernel_hash=(digest,None) if mode=='kernel-local' else (None,digest)
        result,receipt=merge(source,proof,source_hash,kernel_hash)
        if result['exact_head_sha']!=head:raise ValueError('RESULT_HEAD_MISMATCH')
        # Always run the project semantic+Draft-07 validator; a passing schema
        # never serves as an unconditional RH admission receipt.
        from validate_repository_census_v11 import validate
        schema=json.loads((checkout/'research/rh/assembly/repository-census.schema.json').read_text())
        problems=validate(result,schema)
        if problems:raise ValueError('SCHEMA_OR_SEMANTIC_VALIDATION_FAILED:'+str(problems[:5]))
        out=output_dir/'repository_census_v1.1_kernel_bound.json'
        out.write_text(json.dumps(result,sort_keys=True,ensure_ascii=False,indent=2)+'\n')
        receipt.update(status='PASS',counterpart_run_id=run['id'],
                       counterpart_artifact_id=artifact['id'],counterpart_digest=digest,
                       output_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
                       kernel_counts_scope='IMPORTED_LEAN_ENVIRONMENT_NOT_AEGIS_AUTHORSHIP',
                       current_rh_verdict='NOT_ADMITTED_BY_CENSUS')
        (output_dir/'repository_census_v1.1_kernel_receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
        status_path.write_text(json.dumps({'status':'PASS','exact_head':head,'mode':mode,
                   'output_sha256':receipt['output_sha256'],'counterpart_run_id':run['id']},indent=2)+'\n')
        print('CENSUS_KERNEL_CROSS_EVIDENCE_PASS',head,'kernel_roots',receipt['materialized_roots'])
        return receipt


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mode',required=True,choices=['kernel-local','source-local'])
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--repo',default=os.environ.get('GITHUB_REPOSITORY'))
    ap.add_argument('--exact-head',default=os.environ.get('PR_HEAD_EXACT'))
    ap.add_argument('--checkout',type=Path,default=Path('.'))
    args=ap.parse_args()
    token=os.environ.get('GH_TOKEN')
    if not token:raise ValueError('GITHUB_TOKEN_REQUIRED_FOR_READ_ONLY_ARTIFACT_DISCOVERY')
    do_join(args.mode,args.repo,args.exact_head,token,args.output_dir,args.checkout.resolve())

if __name__=='__main__':main()
