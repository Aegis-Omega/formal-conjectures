#!/usr/bin/env python3
"""Head-bound source/declaration census. Source observations are NOT kernel proofs."""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

DECL = re.compile(r"^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial|local)[ \t]+)*(theorem|lemma|def|abbrev|opaque|axiom|constant|instance|structure|class|inductive|coinductive|example)\b[ \t]*([^\s(:{=]*)", re.M)
IMPORT = re.compile(r"^[ \t]*import[ \t]+([^\n]+)", re.M)
PROBES = re.compile(r"^[ \t]*#print[ \t]+axioms[ \t]+(\S+)", re.M)
PATHS = [
 ("FOUR_LOG_THREE","QUESTIONED","AEGISOverlay/RHFourLogThreeWeightedRHBridgeV1.lean","HasWeightedFourLogThreeReconstruction","Universal same-mother selector not established; geometric obstruction candidate"),
 ("KREIN_TRANSPORT","ACTIVE","AEGISOverlay/RHKreinMultiplicativeTransportV1.lean","every_moment_zero_packet_finite_actual_weil_partition","Missing universal actual mixed Weil sign estimate"),
 ("CVS_L43","ACTIVE","research/rh/checkpoints/20261026_window_l43/RHWindowL43ExhaustionV1.lean","rh_iff_windows_above_two_thirds","Need all log windows above 2/3"),
 ("FESHBACH_K3","ACTIVE","research/rh/feshbach_lean_v1/CvSK3FourierMinorV2.lean","detG_ne_zero_of_posN","Exact-head kernel proof and K3e/K3f still require admission"),
 ("SCHUR_OPTIMIZED","ACTIVE","AEGISOverlay/RHOptimizedSchurGlobalJoinV1.lean","riemannHypothesis_of_optimized_actual_row_producer","Global hselect producer is an explicit unproved premise"),
 ("COFINAL_CERTIFICATES","ACTIVE","AEGISOverlay/RHCofinalActualTerminalV1.lean","riemannHypothesis_of_cofinal_lower_certificates","Universal cofinal certificate producer not supplied"),
]

def run(*args,cwd=None):
    return subprocess.check_output(args,cwd=cwd,text=True).strip()

def digest(b):
    return hashlib.sha256(b).hexdigest()

def git_blob(b):
    return hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()

def code_only(code):
    out=list(code);i=0;depth=0;string=False;escape=False
    while i<len(code):
        if depth:
            if code.startswith("/-",i):
                out[i:i+2]=[' ',' '];depth+=1;i+=2;continue
            if code.startswith("-/",i):
                out[i:i+2]=[' ',' '];depth-=1;i+=2;continue
            if code[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if code[i]!='\n':out[i]=' '
            if escape:escape=False
            elif code[i]=='\\':escape=True
            elif code[i]=='"':string=False
            i+=1;continue
        if code.startswith("/-",i):
            out[i:i+2]=[' ',' '];depth=1;i+=2;continue
        if code.startswith("--",i):
            while i<len(code) and code[i]!='\n':out[i]=' ';i+=1
            continue
        if code[i]=='"':out[i]=' ';string=True
        i+=1
    return ''.join(out)

def source_scan(root):
    files=subprocess.check_output(['git','ls-files','-z','--','*.lean'],cwd=root).split(b'\0')
    modules=[];decls=[]
    for name in sorted(x.decode() for x in files if x):
        path=root/name
        if not path.is_file() or path.is_symlink():raise RuntimeError('TRACKED_SOURCE_INVALID '+name)
        raw=path.read_bytes();code=code_only(raw.decode('utf-8'))
        local=[]
        for m in DECL.finditer(code):
            row={'module_path':name,'source_local_name':m.group(2) or None,
                 'kind':m.group(1),'line':code.count('\n',0,m.start())+1,
                 'verification':'SOURCE_SYNTAX_ONLY','axioms':None,'formal_dependencies':None}
            local.append(row);decls.append(row)
        imports=[]
        for m in IMPORT.finditer(code):
            imports.extend(x for x in m.group(1).split()
                           if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*",x))
        modules.append({'path':name,'blob_sha1':git_blob(raw),'sha256':digest(raw),
            'module_name_candidate':name[:-5].replace('/','.') if name.startswith(('AEGISOverlay/','FormalConjectures/','FormalConjecturesForMathlib/')) else Path(name).stem,
            'imports_source':sorted(set(imports)),
            'axiom_probes_source':PROBES.findall(code),
            'source_declaration_occurrences':len(local),
            'rh_related_source':name.startswith(('research/rh/','AEGISOverlay/','AegisRH/'))
                or Path(name).stem.startswith(('RH','Weil','CvS'))})
    return modules,decls

def build(root,graph_path=None,proof_path=None):
    head=run('git','rev-parse','HEAD',cwd=root)
    tree=run('git','rev-parse','HEAD^{tree}',cwd=root)
    if run('git','status','--porcelain','--untracked-files=no',cwd=root):
        raise RuntimeError('WORKTREE_DIRTY_SOURCE_IS_NOT_EXACT_HEAD')
    modules,decls=source_scan(root)
    by_path={x['path']:x for x in modules}
    paths=[];obligations=[]
    for ident,state,path,symbol,goal in PATHS:
        matches=[d for d in decls if d['module_path']==path and d['source_local_name']==symbol]
        source=({'path':path,'blob_sha1':by_path[path]['blob_sha1'],'source_symbol':symbol,
                 'line':matches[0]['line'],'proof_status':'KERNEL_UNVERIFIED'}
                if matches and path in by_path else None)
        paths.append({'path_id':ident,'status':state if source else 'UNKNOWN',
                      'evidence':source,'classification':'strategy triage only'})
        obligations.append({'id':ident+'_GLOBAL_GATE','status':'OPEN' if source else 'UNKNOWN',
                            'obligation':goal,'source':source,'blocked_by':[],
                            'discharge_receipt':None})
    branch={'state':'UNKNOWN','reason':'all-PR graph not supplied'}
    graph=None
    if graph_path is not None:
        graph=json.loads(graph_path.read_text())
        if graph.get('target_exact_sha')!=head:raise RuntimeError('EXACT_HEAD_PR_GRAPH_MISMATCH')
        if graph.get('inventory_complete') is not True:raise RuntimeError('INCOMPLETE_PR_BRANCH_GRAPH')
        variants=defaultdict(set)
        for tree_row in graph.get('tree_by_sha',{}).values():
            for path,blob in tree_row.get('sources',{}).items():variants[path].add(blob)
        branch={'state':'VERIFIED_SOURCE_GRAPH_ONLY','graph_sha256':digest(graph_path.read_bytes()),
                'counts':graph.get('counts',{}),
                'rh_unique_source_paths_in_graph':len(variants),
                'rh_unique_path_blob_variants_in_graph':sum(map(len,variants.values())),
                'rh_divergent_source_paths':sum(len(v)>1 for v in variants.values()),
                'claim_limit':'PR and live branch heads, RH subtree only, not every historical commit'}
        rows=[n for n in graph.get('github_pr_base_graph',{}).get('nodes',[])
              if n.get('number')==92 and n.get('head_sha')==head]
        if len(rows)!=1:raise RuntimeError('PR92_HEAD_NOT_IN_BRANCH_GRAPH')
    kernel={'status':'UNKNOWN','reason':'source-only census; no exact-head kernel receipts'}
    if proof_path:
        proof=json.loads(proof_path.read_text())
        kernel={'status':'UNVERIFIED_EXPORT_WITHOUT_EXACT_HEAD_RECEIPT',
                'proof_graph_sha256':digest(proof_path.read_bytes()),
                'root_count':len(proof.get('roots',[])),
                'reachable_declaration_rows':len(proof.get('declarations',[])),
                'claim_limit':'This graph is root-reachable only, not all Lean declarations'}
    counts=Counter(x['kind'] for x in decls)
    rhpaths={m['path'] for m in modules if m['rh_related_source']}
    authority=[{'artifact':'PR #92','current_authority':bool(graph),
        'scope':'integration/review only, never automatic RH theorem admission',
        'exact_head':head,'supersedes':['PR #93 duplicate K3 source-graft (documented in PR discussion)']
        if graph else []},
        {'artifact':'repository_census.json','current_authority':False,
         'scope':'exact Git source inventory only; full Lean declaration authority OPEN',
         'exact_head':head,'supersedes':[]}]
    return {'schema':'aegis.rh.repository-census.v1',
        'generated_at_utc':datetime.now(timezone.utc).isoformat(),
        'repository':{'name':run('git','config','--get','remote.origin.url',cwd=root)
                  if subprocess.run(['git','config','--get','remote.origin.url'],cwd=root,capture_output=True).returncode==0
                  else 'UNKNOWN','exact_head':head,'git_tree':tree},
        'scope':{'tracked_git_sources':'COMPLETE_EXACT_HEAD','branch_source_graph':branch['state'],
                 'total_git_history':'NOT_EXHAUSTIVE','other_repositories':'NOT_ASSESSED',
                 'lean_environment':'KERNEL_UNVERIFIED'},
        'total_modules':len(modules),
        'total_declarations':None,'total_theorems':None,'total_axioms':None,
        'total_rh_related_declarations':None,
        'source_counts':{'tracked_lean_files':len(modules),
             'unique_source_blob_sha1s':len({m['blob_sha1'] for m in modules}),
             'source_declaration_occurrences':len(decls),
             'source_theorem_occurrences':counts['theorem'],
             'source_axiom_occurrences':counts['axiom'],
             'by_kind':dict(sorted(counts.items())),
             'rh_related_tracked_modules':len(rhpaths),
             'rh_related_source_declaration_occurrences':
                 sum(d['module_path'] in rhpaths for d in decls),
             'warning':'All source counts are syntactic occurrences, not Lean kernel-checked declarations'},
        'branch_inventory_summary':branch,'kernel_inventory_summary':kernel,
        'declaration_inventory':decls,'module_inventory':modules,
        'rh_path_inventory':paths,
        'active_rh_paths':[p for p in paths if p['status']=='ACTIVE'],
        'questioned_rh_paths':[p for p in paths if p['status']=='QUESTIONED'],
        'superseded_rh_paths':[], 'unknown_rh_paths':[p for p in paths if p['status']=='UNKNOWN'],
        'open_obligations':[o for o in obligations if o['status']=='OPEN'],
        'closed_obligations':[], 'unknown_obligations':[o for o in obligations if o['status']=='UNKNOWN'],
        'authority_inventory':authority,'current_rh_status':'NOT_ASSESSED_ON_THIS_CENSUS',
        'limits':['Lean macros, namespaces and generated declarations require elaborated kernel environment',
                  'Open obligations list covers explicit selected routes only; it is not mathematically exhaustive',
                  'No total of theorem proofs or axioms can be inferred from source regex',
                  'Branch graph enumerates RH sources at PR/branch heads, not entire historical commit universe']}

def self_test():
    s='''/- theorem Fake : False := by sorry\n /- lemma Hidden -/\n-/\nimport Mathlib.Tactic\n-- axiom Nope : False\nnamespace N\nprivate theorem real : True := by trivial\nlemma another : True := by trivial\n#print axioms N.real\n'''
    c=code_only(s)
    assert [(m.group(1),m.group(2)) for m in DECL.finditer(c)]==[('theorem','real'),('lemma','another')]
    assert PROBES.findall(c)==['N.real']
    assert git_blob(b'hi\n')=='45b983be36b73c0788dc9cbcb76cbb80fc7bb057'
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        subprocess.run(['git','init','-q',str(root)],check=True)
        for name,val in [('user.email','fixture@example.invalid'),('user.name','Fixture')]:
            subprocess.run(['git','-C',str(root),'config',name,val],check=True)
        (root/'A.lean').write_text(s)
        subprocess.run(['git','-C',str(root),'add','A.lean'],check=True)
        subprocess.run(['git','-C',str(root),'commit','-qm','fixture'],check=True)
        r=build(root)
        assert r['source_counts']['source_declaration_occurrences']==2
        assert r['total_declarations'] is None
        graph={'target_exact_sha':r['repository']['exact_head'],'inventory_complete':True,
               'github_pr_base_graph':{'nodes':[{'number':92,'head_sha':r['repository']['exact_head']}]},'tree_by_sha':{}}
        g=root/'graph.json';g.write_text(json.dumps(graph))
        assert build(root,g)['branch_inventory_summary']['state']=='VERIFIED_SOURCE_GRAPH_ONLY'
        graph['target_exact_sha']='wrong';g.write_text(json.dumps(graph))
        try:build(root,g)
        except RuntimeError as e:assert str(e)=='EXACT_HEAD_PR_GRAPH_MISMATCH'
        else:raise AssertionError('stale graph was admitted')
    print('REPOSITORY_CENSUS_SELF_TEST_PASS')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path('.'))
    ap.add_argument('--graph',type=Path)
    ap.add_argument('--proof-graph',type=Path)
    ap.add_argument('--output',type=Path,default=Path('repository_census.json'))
    ap.add_argument('--self-test',action='store_true')
    a=ap.parse_args()
    if a.self_test:self_test()
    else:
        result=build(a.root.resolve(),a.graph,a.proof_graph)
        a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
        print('REPOSITORY_CENSUS_SOURCE_COUNT',result['total_modules'],
              result['source_counts']['source_declaration_occurrences'],
              'KERNEL_TOTALS_UNKNOWN',result['repository']['exact_head'])
