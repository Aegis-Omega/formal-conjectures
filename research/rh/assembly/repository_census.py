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


def kernel_graph_census(head, proof_path, passport_path, environment_path, terms_path, tracked_by_path):
    """Reuse the existing Lean exporter, never guess a declaration's kernel status."""
    supplied=[proof_path,passport_path,environment_path,terms_path]
    if any(x is None for x in supplied):
        raise RuntimeError("INCOMPLETE_LEAN_EVIDENCE_BUNDLE")
    graph=json.loads(proof_path.read_text())
    passport=json.loads(passport_path.read_text())
    environment=json.loads(environment_path.read_text())
    terms=json.loads(terms_path.read_text())
    if graph.get('exact_replay_sha')!=head or passport.get('exact_replay_sha')!=head:
        raise RuntimeError('LEAN_EVIDENCE_HEAD_MISMATCH')
    if passport.get('proof_term_graph_sha256')!=digest(terms_path.read_bytes()):
        raise RuntimeError('LEAN_PROOF_TERMS_DIGEST_MISMATCH')
    if graph.get('roots')!=terms.get('roots'):
        raise RuntimeError('LEAN_PROOF_ROOTS_MISMATCH')
    if not isinstance(graph.get('declarations'),list) or not isinstance(terms.get('declarations'),list):
        raise RuntimeError('LEAN_PROOF_DECLARATIONS_MISSING')
    source_rows={r['identifier']:r for r in terms['declarations']}
    assembled_rows={r['identifier']:r for r in graph['declarations']}
    if len(source_rows)!=len(terms['declarations']) or len(assembled_rows)!=len(graph['declarations']):
        raise RuntimeError('DUPLICATE_LEAN_DECLARATION_IDENTIFIER')
    if source_rows.keys()!=assembled_rows.keys() or not source_rows:
        raise RuntimeError('LEAN_PROOF_SOURCE_DAG_INCONSISTENT')
    if not set(terms['roots'])<=source_rows.keys():
        raise RuntimeError('LEAN_ROOT_OUTSIDE_REACHABLE_DAG')
    checked=[]
    for key,root in sorted(source_rows.items()):
        row=assembled_rows[key]
        for field in ('identifier','module','is_axiom','has_body','axioms','direct_dependencies'):
            if row.get(field)!=root.get(field):
                raise RuntimeError('LEAN_PROOF_GRAPH_ROW_DRIFT '+key+' '+field)
        if not isinstance(row.get('axioms'),list) or not isinstance(row.get('direct_dependencies'),list):
            raise RuntimeError('LEAN_PROOF_GRAPH_INVALID_AXIOMS_OR_DEPS '+key)
        src=row.get('source')
        if isinstance(src,dict):
            source_path=src.get('source')
            local=tracked_by_path.get(source_path)
            if local and src.get('sha256')!=local['sha256']:
                raise RuntimeError('LEAN_SOURCE_IDENTITY_DRIFT '+source_path)
        checked.append({'declaration':key,'module':row['module'],
                        'kind':'axiom' if row['is_axiom'] else
                           ('body_bearing' if row['has_body'] else 'UNKNOWN'),
                        'is_axiom':row['is_axiom'],'has_body':row['has_body'],
                        'axioms':row['axioms'],'dependencies':row['direct_dependencies'],
                        'source':src,'kernel_scope':'EXACT_HEAD_REACHABLE_DAG'})
    scan=graph.get('rh_closure_scan') or {}
    pscan=passport.get('rh_closure_scan') or {}
    for k in ('imported_environment_declaration_count','imported_environment_rh_type_candidates',
              'reachable_declaration_count','closed_canonical_rh_declarations'):
        if scan.get(k)!=pscan.get(k):
            raise RuntimeError('LEAN_PASSPORT_CLOSURE_SCAN_DRIFT '+k)
    if (scan.get('imported_environment_declaration_count')!=environment.get('inspected_count')
        or scan.get('imported_environment_rh_type_candidates')!=len(environment.get('declarations',[]))
        or scan.get('reachable_declaration_count')!=len(checked)):
        raise RuntimeError('LEAN_ENVIRONMENT_CENSUS_COUNTER_MISMATCH')
    if (environment.get('defeq_target_type')!='RiemannHypothesis'
        or environment.get('inspected_count',0)<len(checked)
        or environment.get('semantic_theorems_checked',0)>environment.get('inspected_count',0)):
        raise RuntimeError('LEAN_ENVIRONMENT_CENSUS_INVALID')
    env_matches=environment['declarations']
    if any(x.get('type_defeq_riemann_hypothesis') is not True for x in env_matches):
        raise RuntimeError('LEAN_RH_TYPE_WITNESS_INVALID')
    if sorted(scan.get('closed_canonical_rh_from_imported_environment',[]))!=sorted(
        x['identifier'] for x in env_matches
        if x.get('has_body') is True and x.get('is_axiom') is False
        and isinstance(x.get('axioms'),list)
        and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}):
        raise RuntimeError('LEAN_CANONICAL_RH_CLOSURE_CONFLICT')
    return ({'status':'EXACT_HEAD_LEAN_EXPORT_BUNDLE_VERIFIED',
             'exact_head':head,'proof_graph_sha256':digest(proof_path.read_bytes()),
             'proof_terms_sha256':digest(terms_path.read_bytes()),
             'evidence_passport_sha256':digest(passport_path.read_bytes()),
             'environment_census_sha256':digest(environment_path.read_bytes()),
             'root_count':len(terms['roots']),
             'reachable_declaration_rows':len(checked),
             'imported_environment_declarations':environment['inspected_count'],
             'imported_environment_theorems':environment['semantic_theorems_checked'],
             'imported_environment_axioms':None,
             'canonical_rh_type_candidates':len(env_matches),
             'canonical_rh_closed_in_imported_environment':scan.get('closed_canonical_rh_declarations',[]),
             'claim_limit':'Counts cover this imported Lean environment / selected DAG, not all repo branches'},
            checked,env_matches)

def build(root,graph_path=None,proof_path=None,passport_path=None,environment_path=None,terms_path=None):
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
    kernel={'status':'UNKNOWN','reason':'source-only census; no exact-head Lean evidence bundle'}
    verified_decls=[];rh_candidates=[]
    if any(x is not None for x in (proof_path,passport_path,environment_path,terms_path)):
        kernel,verified_decls,rh_candidates=kernel_graph_census(
            head,proof_path,passport_path,environment_path,terms_path,by_path)
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
                 'lean_environment':kernel['status']},
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
        'kernel_reachable_declaration_inventory':verified_decls,
        'kernel_rh_type_candidates':rh_candidates,
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
                  'Branch graph enumerates RH sources at PR/branch heads, not entire historical commit universe',
                  'Kernel proof DAG and imported-environment totals have different coverage and cannot be added together']}

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
    # A fabricated bundle tests structural consistency; no assertion of real proof.
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        subprocess.run(['git','init','-q',str(root)],check=True)
        for name,val in [('user.email','fixture@example.invalid'),('user.name','Fixture')]:
            subprocess.run(['git','-C',str(root),'config',name,val],check=True)
        (root/'A.lean').write_text('theorem witness : True := by trivial\n')
        subprocess.run(['git','-C',str(root),'add','A.lean'],check=True)
        subprocess.run(['git','-C',str(root),'commit','-qm','fixture'],check=True)
        h=run('git','rev-parse','HEAD',cwd=root)
        declaration={'identifier':'Fixture.witness','module':'A','is_axiom':False,
                     'has_body':True,'axioms':['propext'],
                     'direct_dependencies':[]}
        terms={'roots':['Fixture.witness'],'declarations':[declaration]}
        (root/'terms.json').write_text(json.dumps(terms))
        graph={'exact_replay_sha':h,'roots':terms['roots'],
               'declarations':[dict(declaration)],'rh_closure_scan':{
                 'reachable_declaration_count':1,'imported_environment_declaration_count':4,
                 'imported_environment_rh_type_candidates':0,'closed_canonical_rh_declarations':[],
                 'closed_canonical_rh_from_imported_environment':[]}}
        passport={'exact_replay_sha':h,'proof_term_graph_sha256':digest((root/'terms.json').read_bytes()),
                  'rh_closure_scan':graph['rh_closure_scan']}
        environment={'inspected_count':4,'semantic_theorems_checked':2,
                     'defeq_target_type':'RiemannHypothesis','declarations':[]}
        for name,data in [('graph.json',graph),('passport.json',passport),('env.json',environment)]:
            (root/name).write_text(json.dumps(data))
        paths=[root/z for z in ('graph.json','passport.json','env.json','terms.json')]
        out=build(root,proof_path=paths[0],passport_path=paths[1],environment_path=paths[2],terms_path=paths[3])
        assert out['kernel_inventory_summary']['imported_environment_declarations']==4
        assert out['kernel_reachable_declaration_inventory'][0]['dependencies']==[]
        assert out['total_declarations'] is None
        passport['exact_replay_sha']='stale';paths[1].write_text(json.dumps(passport))
        try:build(root,proof_path=paths[0],passport_path=paths[1],environment_path=paths[2],terms_path=paths[3])
        except RuntimeError as e:assert str(e)=='LEAN_EVIDENCE_HEAD_MISMATCH'
        else:raise AssertionError('stale proof passport admitted')
        try:build(root,proof_path=paths[0])
        except RuntimeError as e:assert str(e)=='INCOMPLETE_LEAN_EVIDENCE_BUNDLE'
        else:raise AssertionError('partial proof evidence admitted')
    print('REPOSITORY_CENSUS_SELF_TEST_PASS')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path('.'))
    ap.add_argument('--graph',type=Path)
    ap.add_argument('--proof-graph',type=Path)
    ap.add_argument('--proof-passport',type=Path)
    ap.add_argument('--environment-census',type=Path)
    ap.add_argument('--proof-terms',type=Path)
    ap.add_argument('--output',type=Path,default=Path('repository_census.json'))
    ap.add_argument('--self-test',action='store_true')
    a=ap.parse_args()
    if a.self_test:self_test()
    else:
        result=build(a.root.resolve(),a.graph,a.proof_graph,a.proof_passport,a.environment_census,a.proof_terms)
        a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
        print('REPOSITORY_CENSUS_SOURCE_COUNT',result['total_modules'],
              result['source_counts']['source_declaration_occurrences'],
              'KERNEL_TOTALS_UNKNOWN',result['repository']['exact_head'])
