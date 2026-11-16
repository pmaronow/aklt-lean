from pathlib import Path
# Cache only accelerates numerical searches. All output and operation logs remain.
root=Path(__file__).resolve().parents[1]
for p in (root/'data/prefix').glob('*.bin'):
 if any(f'h3_{p.stem}_T' in x.name and '# TAIL' in x.read_text() for x in (root/'logs').glob('h3_*.out')):pass
# Completed first sweep: preserve none; recomputing prefixes is cheap enough.
for pattern in ['typedminsafe_m9_L18_K36_*.bin','typedminsafe_m10_L16_K28_*.bin','typedminsafe_m10_L18_K24_*.bin','typedminsafe_m11_L16_K20_*.bin']:
 for p in (root/'data/prefix').glob(pattern):p.unlink()
