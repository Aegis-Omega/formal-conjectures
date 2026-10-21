"""Propose exact Q input checks from the already-staged cross rows, retaining 2*pi."""
from pathlib import Path
import sys,json
sys.set_int_max_str_digits(0)
w=Path(__file__).resolve().parent
ns={'__file__':str(w/'generate_source_products.py')}
exec(compile((w/'generate_source_products.py').read_text().split('for key,rows in')[0],'cache-encoder-only','exec'),ns)
D=ns['D'];vec=ns['vec'];lst=ns['lst'];head=ns['head']
for b,start in enumerate(range(0,139,10)):
 stop=min(139,start+10);name=f'CvSSourceQCache{b}'
 s='/- Verified cache of the 141 inner source cross rows; unchanged endpoints. -/\nimport CvSSourceQNormalizeV1\n'+''.join(f'import CvSSourceProduct{i}\n' for i in range(start,stop))+head+f'namespace AEGIS.{name}\n'
 for i in range(start,stop):
  a=[row[i] for row in D['Y'][80:221]]
  s+=vec('column'+str(i),a).replace('values := '+lst(a),f'values := (AEGIS.CvSSourceProduct{i}.Y.drop 80).take 141')
 s+=f'end AEGIS.{name}\n';(w/(name+'.lean')).write_text(s)
for j in range(139):
 s='/- Every original Q input entry, enclosed using the correctly normalized actual cross product. -/\n'+f'import CvSSourceQCache{j//10}\nimport CvSCachedOutput{j}\nimport CvSFullCachedTableV1\n'+head+f'namespace AEGIS.CvSSourceQCheck{j}\n'
 s+='open AEGIS.CvSSourceQNormalizeV1\n'
 s+=f'''def check (i : ℕ) : Bool := contains (AEGIS.CvSCachedOutput{j}.q.getD i ⟨0, 0⟩)
    (normalize (evalDot (AEGIS.CvSFullCachedTableV1.column i).x
      AEGIS.CvSSourceQCache{j//10}.column{j}))
theorem checked : (List.range 139).all check = true := by decide +kernel
theorem all_rows (i : Fin 139) : check i.val = true :=
  List.all_eq_true.mp checked i.val (List.mem_range.mpr i.isLt)
end AEGIS.CvSSourceQCheck{j}
#print axioms AEGIS.CvSSourceQCheck{j}.checked
#print axioms AEGIS.CvSSourceQCheck{j}.all_rows
'''
 (w/f'CvSSourceQCheck{j}.lean').write_text(s)
print('Generated normalized source-Q cache and check candidates; not yet kernel verified')
