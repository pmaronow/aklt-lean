from pathlib import Path
root=Path(__file__).resolve().parents[1]
removed=0
for p in (root/'data/prefix').glob('*.bin'):
 
 if p.stem.startswith('packed_'):continue
 base,X,cl=p.stem.rsplit('_',2)
 for f in (root/'logs').glob(f'h3_{base}_T*_{X}_{cl}.out'):
  if '# TAIL' in f.read_text():
   removed+=p.stat().st_size;p.unlink();break
print('removed_bytes',removed)
