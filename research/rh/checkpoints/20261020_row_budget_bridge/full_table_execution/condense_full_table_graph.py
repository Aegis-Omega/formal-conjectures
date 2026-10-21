"""Fail-closed dependency, axiom and source audit of the complete finite table."""
from pathlib import Path
import json,sys,hashlib,subprocess,zipfile
sys.setrecursionlimit(100000)
w=Path(__file__).resolve().parent;repo=Path('/workspace/formal-conjectures');d=repo/'research/rh/checkpoints/20261020_row_budget_bridge'
rawpath=w/'NATIVE_FULL_TABLE_PROOF_GRAPH.json';raw=json.loads(rawpath.read_text());nodes={a['identifier']:a for a in raw['declarations']};allow={'propext','Classical.choice','Quot.sound'}
assert len(nodes)==len(raw['declarations'])
assert all(set(a['axioms'])<=allow for a in nodes.values())
assert all(v in nodes for a in nodes.values() for v in a['direct_dependencies'])
assert all(not a['is_axiom'] or a['identifier'] in allow for a in nodes.values())
indices={};low={};stack=[];on=set();groups=[]
def visit(v):
 indices[v]=low[v]=len(indices);stack.append(v);on.add(v)
 for u in nodes[v]['direct_dependencies']:
  if u not in indices:visit(u);low[v]=min(low[v],low[u])
  elif u in on:low[v]=min(low[v],indices[u])
 if indices[v]==low[v]:
  g=[]
  while True:
   a=stack.pop();on.remove(a);g.append(a)
   if a==v:break
  groups.append(g)
for v in nodes:
 if v not in indices:visit(v)
gids={a:i for i,g in enumerate(groups) for a in g};dag=[];metadata=0
for i,g in enumerate(groups):
 cyc=len(g)>1 or any(a in nodes[a]['direct_dependencies'] for a in g)
 if cyc:
  metadata+=1;assert all(nodes[a]['kind'] in ['inductive','constructor'] for a in g),(g,[nodes[a]['kind'] for a in g])
 dep=sorted({gids[b] for a in g for b in nodes[a]['direct_dependencies'] if gids[b]!=i});assert all(a<i for a in dep)
 dag.append({'id':i,'declarations':g,'direct_dependency_groups':dep,'kernel_metadata_group':cyc})
old=json.loads((d/'AEGIS_RH_EXACT_HEAD_PROOF_GRAPH.json').read_text());locations={a['module']:Path(a['path']) for a in old.get('source_manifest',[]) if a.get('path')}
locations.update({p.stem:p for p in w.glob('*.lean')})
locations.update({'CvSRowBudgetAlgebraV1':repo/'research/rh/checkpoints/20261020_row_budget/CvSRowBudgetAlgebraV1.lean','CvSFiniteCongruenceV1':repo/'research/rh/feshbach_lean_v1/CvSFiniteCongruenceV1.lean'})
prefix=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=repo,text=True).strip());manifest=[]
for m in sorted({a['origin_module'] for a in nodes.values()}):
 rel=Path(*m.split('.')).with_suffix('.lean');choices=[locations.get(m),repo/rel,prefix/'src/lean'/rel]+[p/rel for p in (repo/'.lake/packages').iterdir() if p.is_dir()]
 p=next((p for p in choices if p is not None and p.is_file()),None);assert p is not None,'MISSING_SOURCE '+m
 b=p.read_bytes();manifest.append({'module':m,'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'blob_sha':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()})
obj={'scope':'Complete selected native proof closure for all 19321 ordered row-envelope output comparisons, real membership composition, quantitative relative budget and rejection controls. Six input-membership families remain explicit. Not an unconditional actual-CvS or RH theorem.','source_base_commit':'b133be9d88ca0a58ad5ea90aeee3fc5c765be445','roots':raw['roots'],'root_group_ids':[gids[a] for a in raw['roots']],'declaration_count':len(nodes),'metadata_cyclic_groups':metadata,'proof_cycles':0,'missing_dependencies':0,'axioms':sorted(allow),'groups':dag,'source_manifest':manifest,'raw_graph_sha256':hashlib.sha256(rawpath.read_bytes()).hexdigest(),'lean':'4.33.1','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474'}
(w/'FULL_TABLE_PROOF_GRAPH.json').write_text(json.dumps(obj,separators=(',',':'))+'\n')
with zipfile.ZipFile(w/'FULL_TABLE_PROOF_GRAPH.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in [rawpath,w/'FullTableProofGraph.lean',Path(__file__)]:z.write(p,p.name)
print(json.dumps({'roots':len(raw['roots']),'declarations':len(nodes),'modules':len(manifest),'proof_cycles':0,'metadata_scc':metadata,'missing_dependencies':0,'axioms':sorted(allow)}))
