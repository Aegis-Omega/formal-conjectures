"""Compile the actual-import moment trace bridge and reject missing/extra axioms."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path.cwd()
source = root / 'research/rh/checkpoints/20261020_row_budget_bridge/CvSMomentTraceV1.lean'
target = root / '.lake/ringout/CvSMomentTraceV1.olean'
names = ['momentFunction_continuous', 'augment_continuous', 'moment_orthogonal',
         'augment_orthogonal', 'energy_le_augmented_dist', 'slack_le_augmented_trace',
         'complement_bound_with_moments']
expected = {'AEGIS.CvSMomentTraceV1.' + name for name in names}
command = ['lean', '-DwarningAsError=true', '-o', str(target), str(source)]
started = time.monotonic()
result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
text = result.stdout
(root / 'moment-trace-replay.log').write_text(text)
audits = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    audits[name] = [a.strip() for a in axioms.split(',') if a.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    audits[name] = []
passed = (result.returncode == 0 and expected <= audits.keys()
          and all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}
                  for a in audits.values()))
receipt = {
    'repository': 'tarikskalic33/formal-conjectures',
    'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'lean': subprocess.check_output(['lean', '--version'], text=True).strip(),
    'mathlib': subprocess.check_output(['git', '-C', '.lake/packages/mathlib',
                                      'rev-parse', 'HEAD'], text=True).strip(),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'source_blob': subprocess.check_output(['git', 'hash-object', str(source)], text=True).strip(),
    'command': command, 'exit_code': result.returncode,
    'seconds': time.monotonic() - started, 'compiler_output': text,
    'axiom_audits': audits, 'required_roots': sorted(expected),
    'status': 'PASS' if passed else 'FAIL',
    'scope': 'For every finite low family and every bounded moment-zero complement, '
             'the two exponential moment functions may be included in the trace trial '
             'space. The complement theorem still requires its pointwise Krein '
             'inequality and actual augmented trace bound. Not unconditional RH.'}
if passed:
    receipt['binary_sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()
(root / 'MOMENT_TRACE_KERNEL_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(text)
print('MOMENT_TRACE_KERNEL_' + receipt['status'], len(audits), 'audits')
raise SystemExit(0 if passed else 1)
