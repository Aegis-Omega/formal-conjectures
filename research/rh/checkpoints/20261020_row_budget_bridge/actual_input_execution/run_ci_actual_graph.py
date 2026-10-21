"""Reuse the pinned declaration-graph exporter for the newly compiled actual roots."""
from pathlib import Path
import zipfile,subprocess,os,json,hashlib,sys
repo=Path.cwd();d=repo/'research/rh/checkpoints/20261020_row_budget_bridge'
roots=['AEGIS.CvSActualLiteralInputsV1.sourceKernel_signed','AEGIS.CvSActualLiteralInputsV1.projectedEntry_as_Y','AEGIS.CvSActualLiteralInputsV1.Q_mem','AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin','AEGIS.CvSActualBasisBudgetV1.actualBudget_le_original','AEGIS.CvSActualRowConsumerV1.hfin','AEGIS.CvSActualRowConsumerV1.hB','AEGIS.CvSActualGramWindowV1.gramUp_nonneg','AEGIS.CvSActualGramWindowV1.gramTail_nonneg','AEGIS.CvSActualGramWindowV1.actual_hlow','AEGIS.CvSActualGramWindowV1.window_of_actual_rows','AEGIS.CvSActualGramWindowV1.window_of_trace_le_six','AEGIS.CvSKreinScalarUniformV1.gap_lower','AEGIS.CvSKreinScalarUniformV1.schur_budget_with_reserve']
with zipfile.ZipFile(d/'full_table_execution/FULL_TABLE_PROOF_GRAPH.zip') as z:s=z.read('FullTableProofGraph.lean').decode()
s=s.replace('import CvSFullBudgetJoinV1\nimport CvSFullTableRejectV1','import CvSActualGramWindowV1')
a=s.index('  let roots : List Name := [');b=s.index('  let mut pending',a)
s=s[:a]+'  let roots : List Name := [\n    '+',\n    '.join('``'+n for n in roots)+']\n'+s[b:]
s=s.replace('/workspace/aegis-full-table-bridge/NATIVE_FULL_TABLE_PROOF_GRAPH.json','ACTUAL_SOURCE_PROOF_GRAPH_RAW.json')
p=repo/'ActualSourceProofGraph.lean';p.write_text(s)
env=os.environ.copy();env['LEAN_PATH']=str(repo/'.lake/ringout')+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
cmd=['lean','-DwarningAsError=true',str(p)]
with (repo/'actual-proof-graph.log').open('w') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,(repo/'actual-proof-graph.log').read_text()[-5000:]
rawpath=repo/'ACTUAL_SOURCE_PROOF_GRAPH_RAW.json';raw=json.loads(rawpath.read_text());nodes={n['identifier']:n for n in raw['declarations']};allow={'propext','Classical.choice','Quot.sound'}
assert raw['roots']==roots and len(nodes)==len(raw['declarations'])
assert all(set(n['axioms'])<=allow for n in nodes.values())
assert all(not n['is_axiom'] or n['identifier'] in allow for n in nodes.values())
assert all(v in nodes for n in nodes.values() for v in n['direct_dependencies'])
sys.setrecursionlimit(100000);indices={};low={};stack=[];on=set();groups=[]
def visit(v):
 indices[v]=low[v]=len(indices);stack.append(v);on.add(v)
 for u in nodes[v]['direct_dependencies']:
  if u not in indices:visit(u);low[v]=min(low[v],low[u])
  elif u in on:low[v]=min(low[v],indices[u])
 if indices[v]==low[v]:
  g=[]
  while True:
   x=stack.pop();on.remove(x);g.append(x)
   if x==v:break
  groups.append(g)
for v in nodes:
 if v not in indices:visit(v)
metadata=0
gids={n:i for i,g in enumerate(groups) for n in g};dag=[]
for i,g in enumerate(groups):
 if len(g)>1 or any(x in nodes[x]['direct_dependencies'] for x in g):
  assert all(nodes[x]['kind'] in ['inductive','constructor'] for x in g),'PROOF_DEPENDENCY_CYCLE'
  metadata+=1
 dep=sorted({gids[n] for x in g for n in nodes[x]['direct_dependencies'] if gids[n]!=i})
 assert all(x<i for x in dep)
 dag.append({'id':i,'declarations':g,'direct_dependency_groups':dep})
# Resolve actual original-import source bytes, not the historical native import copies.
full=repo/'.lake/actual-source-graph-full-table';full.mkdir(exist_ok=True)
with zipfile.ZipFile(d/'full_table_execution/FULL_TABLE_SOURCES.zip') as z:
 for name in z.namelist():
  assert Path(name).name==name
  if name.endswith('.lean'):(full/name).write_bytes(z.read(name))
tracked=subprocess.check_output(['git','ls-files','--','*.lean'],text=True).splitlines();by_stem={}
for name in tracked:by_stem.setdefault(Path(name).stem,[]).append(repo/name)
leanprefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip());manifest=[]
for module in sorted({n['origin_module'] for n in nodes.values()}):
 rel=Path(*module.split('.')).with_suffix('.lean')
 first=[repo/'.lake/actual-input-sources'/rel,full/rel,repo/rel,repo/'.li-provider'/rel,leanprefix/'src/lean'/rel]
 first += [a/rel for a in (repo/'.lake/packages').iterdir() if a.is_dir()]
 src=next((x for x in first if x.is_file()),None)
 if src is None:
  choices=by_stem.get(module,[])
  assert choices,'MISSING_SOURCE '+module
  assert len({hashlib.sha256(x.read_bytes()).hexdigest() for x in choices})==1,'AMBIGUOUS_SOURCE '+module
  src=choices[0]
 data=src.read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 origin='source tree or pinned toolchain';relative=str(src.relative_to(repo)) if src.is_relative_to(repo) else str(src)
 if src.is_relative_to(repo/'.lake/packages/mathlib'):
  inner=str(src.relative_to(repo/'.lake/packages/mathlib'))
  expected=subprocess.check_output(['git','-C',str(repo/'.lake/packages/mathlib'),'rev-parse','HEAD:'+inner],text=True).strip()
  assert blob==expected,'USED_MATHLIB_SOURCE_CHANGED '+module
  origin='pinned Mathlib blob'
 elif src.is_relative_to(repo/'.li-provider'):origin='existing pinned external-provider build recipe; actual compiled source bytes'
 elif src.is_relative_to(repo/'.lake/actual-input-sources'):origin='ACTUAL_INPUT_SOURCES.zip/'+src.name
 elif src.is_relative_to(full):origin='FULL_TABLE_SOURCES.zip/'+src.name
 manifest.append({'module':module,'path':relative,'blob_sha':blob,'sha256':hashlib.sha256(data).hexdigest(),'origin':origin})
summary={'status':'PASS','source_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'lean':subprocess.check_output(['lean','--version'],text=True).strip(),'mathlib':subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip(),'roots':roots,'root_types':{n:nodes[n]['type_expr'] for n in roots},'declaration_count':len(nodes),'groups':dag,'source_manifest':manifest,'missing_dependencies':0,'proof_cycles':0,'metadata_cyclic_groups':metadata,'axioms':sorted(allow),'raw_graph_sha256':hashlib.sha256(rawpath.read_bytes()).hexdigest(),'export_command':cmd,'scope':'Actual source budget and conditional fixed-window zero-side reduction. Explicit Krein/trace/scalar and support premises remain; canonical unconditional RH is not asserted.'}
(repo/'ACTUAL_SOURCE_PROOF_GRAPH.json').write_text(json.dumps(summary,indent=2)+'\n')
with zipfile.ZipFile(repo/'ACTUAL_SOURCE_PROOF_GRAPH.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in [rawpath,p,repo/'ACTUAL_SOURCE_PROOF_GRAPH.json',Path(__file__)]:z.write(f,f.name)
print('ACTUAL_SOURCE_PROOF_GRAPH_PASS',len(nodes),'declarations',len(roots),'roots; no missing dependencies or proof cycles; standard axioms only',flush=True)
