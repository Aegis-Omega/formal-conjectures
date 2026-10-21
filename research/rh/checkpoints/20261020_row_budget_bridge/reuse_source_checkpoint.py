"""Reuse only source-identical, hash-verified and fully axiom-audited compilation state.

A CI audit-log routing failure does not invalidate completed kernel compilations.
This is dependency reuse, not a claim of fresh compilation of cached theorems.
Any failed check returns nonzero; the caller then executes the full source build.
"""
from pathlib import Path
import hashlib,json,subprocess,shutil,re,sys
from audit_source_rows import audit,NAMES

RUN=39463716271
COMMIT='f8ff0e2006b6393055dcc97597c79ef3f0dcfcf1'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
LI='35df682f3b709ffe5fbcfdd452dfa964bd622b87'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe_path(root,name):
    p=Path(name)
    assert not p.is_absolute() and '..' not in p.parts, 'UNSAFE_PATH'
    return root/p
def main():
    repo=Path.cwd();target=Path(sys.argv[1]);cache=repo/'.lake/source-cross-row-checkpoint'
    cache.mkdir(parents=True,exist_ok=True)
    # Bind archived .lean.src inputs, generators, JSON data and configuration too.
    # Matching only *.lean would miss those genuine proof inputs.
    subprocess.run(['git','fetch','--no-tags','--depth=1','origin',COMMIT],check=True,
      stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=90)
    prefix='research/rh/checkpoints/20261020_row_budget_bridge/'
    metadata={prefix+n for n in ['AEGIS_RH_EXACT_HEAD_PROOF_GRAPH.json',
      'AEGIS_RH_KERNEL_RECEIPT.json','AEGIS_RH_LEAN_PATCH.diff','FINAL_SOURCE_BINDING.json',
      'AEGIS_RH_MATHEMATICAL_ALIGNMENT.md','AEGIS_RH_Q16_CERTIFICATE.md',
      'AEGIS_RH_ZERO_COORDINATE_AUDIT.md','AEGIS_RH_FINAL_DECISION.md',
      'first_column_execution/README.md','BASELINE.md','NEXT_STEPS.md']}
    metadata.add('.github/workflows/rh-cvs-actual-row-replay.yml')
    changes=subprocess.check_output(['git','diff','--no-renames','--name-status',COMMIT,'--'],text=True).splitlines()
    for line in changes:
        status,path=line.split('\t',1)
        assert path in metadata or (status=='A' and path.startswith(prefix)), 'PROOF_INPUT_TREE_CHANGED '+path
    if '--validate-existing' not in sys.argv:
        subprocess.run(['gh','run','download',str(RUN),'--repo','tarikskalic33/formal-conjectures',
          '--name','source-cross-row-'+COMMIT,'--dir',str(cache)],check=True,timeout=180,
          stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    manifest=json.loads((cache/'SOURCE_CROSS_ROW_CHECKPOINT.json').read_text())
    assert manifest['source_commit']==COMMIT
    assert manifest['lean_toolchain']=='leanprover/lean4:v4.33.1'
    assert manifest['mathlib_sha']==MATHLIB and manifest['li_criterion_sha']==LI
    for path,sha in manifest['source_sha256'].items():
        assert digest(safe_path(repo,path))==sha, 'CHANGED_SOURCE '+path
    for path,sha in manifest['log_sha256'].items():
        assert digest(safe_path(cache,path))==sha, 'LOG_HASH_MISMATCH '+path
    actual=(cache/'actual-row-bridge.log').read_text();ring=(cache/'ring.log').read_text()
    assert not re.search(r'error:|error\(lean',actual+'\n'+ring), 'COMPILER_ERROR'
    rows=audit(actual,ring)
    assert len(rows)==len(NAMES)==105
    binaries=manifest['binary_sha256'];assert binaries
    for path,sha in binaries.items():
        assert path.startswith('.lake/ringout/') and path.endswith('.olean')
        assert digest(safe_path(cache,path))==sha, 'BINARY_HASH_MISMATCH '+path
    # New modules may not replace any cached unqualified module name.
    stems={Path(n).stem for n in binaries}
    tracked=subprocess.check_output(['git','ls-files','--','*.lean'],text=True).splitlines()
    for name in set(tracked)-set(manifest['source_sha256']):
        assert Path(name).stem not in stems, 'NEW_MODULE_SHADOWS_CACHE '+name
    assert not target.exists() or not list(target.rglob('*.olean')), 'NONEMPTY_TARGET'
    target.mkdir(parents=True,exist_ok=True)
    for path in binaries:
        rel=Path(path).relative_to('.lake/ringout');dst=target/rel
        dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(cache/path,dst)
    output=target if '--validate-existing' in sys.argv else repo
    for name in ['actual-row-bridge.log','ring.log']:shutil.copyfile(cache/name,output/name)
    roots=['CvSActualRowInputL12V1','RowBudgetFirstColumnV1','CvSFirstColumnRejectV1']
    lean=''.join('import '+n+'\n' for n in roots)
    lean+=''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in NAMES)
    (output/'SOURCE_CHECKPOINT_REAUDIT.lean').write_text(lean)
    receipt={'status':'SOURCE_IDENTICAL_DEPENDENCIES_REUSED','source_run':RUN,'source_commit':COMMIT,
      'prior_math_step_outcome':manifest['math_step_outcome'],'prior_run_is_not_relabelled_success':True,
      'validated_axiom_roots':rows,'verified_binary_count':len(binaries),
      'source_tree_changes_checked':changes,
      'source_manifest_sha256':digest(cache/'SOURCE_CROSS_ROW_CHECKPOINT.json'),
      'scope':'Previously kernel-compiled, source-identical dependencies. All 105 relevant axiom audits are present across the two original logs. Fresh import/type/axiom re-audit follows. No cached theorem is represented as newly source-compiled.'}
    (output/'SOURCE_CROSS_ROW_REUSE_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('SOURCE_IDENTICAL_CHECKPOINT_REUSE',COMMIT,len(binaries),'binaries; 105 standard-axiom roots')
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('CHECKPOINT_NOT_REUSED',type(e).__name__,str(e));raise SystemExit(1)
