import csv
from fractions import Fraction as F
from decimal import Decimal,localcontext
def dec(x):
    with localcontext() as c:
        c.prec=32
        return str(Decimal(x.numerator)/Decimal(x.denominator))
q=F(3923,4000)
W=[[F(0),F(0)] for _ in range(16)]
for r in csv.DictReader(open('audit/trails_integer.csv')):
    n,s,t=map(int,(r['n'],r['s'],r['t']))
    v=F(1000,2883)**s*F(200,561)**t*F(1,5)**(n-s-t)
    for col,kind in enumerate(('all','forbid')):W[n][col]+=int(r[kind])*v
for col,kind in enumerate(('all','forbid')):
    print('\nConvention:',kind)
    for n in range(16):print(n,dec(W[n][col]/q**n))
    a=max((W[n][col]/q**n,n) for n in range(8));b=max((W[n][col]/q**n,n) for n in range(8,16))
    print('small max:',dec(a[0]),'at n=',a[1])
    print('block max:',str(b[0]),'decimal=',dec(b[0]),'at n=',b[1])
    C=max(a[0],100*b[0]);print('C=',dec(C),'<=153:',C<=153,'<=202:',C<=202)
    if col:
        assert C<=153
        # Also certify C for the literal q=lambda^(1/8) in the lemma: lambda>.9807^8.
        conservative=max(max(W[n][col]/F('.9807')**n for n in range(8)),100*max(W[n][col]/F('.9807')**n for n in range(8,16)))
        print('C at smaller rate .9807=',dec(conservative),'<=153:',conservative<=153)
        assert conservative<=153
