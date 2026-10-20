from pathlib import Path
import json,sys,hashlib
sys.set_int_max_str_digits(0)
w=Path('/workspace/aegis-row-budget-bridge')
p=w/'CELL0_INPUTS.json'
assert hashlib.sha256(p.read_bytes()).hexdigest() == '1bcf1419ed38775c23248810edb618a7f196dfba5b7d95ead68cd10baaac8324'
a=json.loads(p.read_text())['Z0'];base=1<<280;bound=1<<128
m=[(lo+hi)//2 for lo,hi in a]
r=[max(mi-lo,hi-mi) for (lo,hi),mi in zip(a,m)]
assert len(a)==301 and all(-bound<=x<=bound for v in [m,r,list(map(abs,m))] for x in v)
def pack(v):
    ans=0
    for x in reversed(v): ans=x+base*ans
    return ans
def row(v):
    off=[x+bound for x in v]
    return f'⟨{pack(off)}, {pack(off[::-1])}, {sum(v)}, {len(v)}⟩'
p=w/'RowBudgetPackedZ0Pilot.lean';s=p.read_text()
cache='def cache : PackedIntervalRow := ⟨'+',\n'.join(row(v) for v in [m,list(map(abs,m)),r])+'⟩\n'
a=s.index('def cache :');b=s.index('theorem packing_exact',a)
assert s[a:b]==cache
print('EXACT_PACKED_CACHE_REGENERATED_BYTES_MATCH',hashlib.sha256(s.encode()).hexdigest())
