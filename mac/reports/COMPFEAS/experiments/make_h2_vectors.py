from pathlib import Path
p=Path('experiments/alm_vector.c');s=p.read_text().replace('wr = 0.25','wr = 0.2');Path('experiments/alm_fifth_vector.c').write_text(s)
