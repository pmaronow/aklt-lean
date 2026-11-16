"""Pattern dict for the patch engine from (kinds, present bonds, out) of pext.py (agent 57)."""
import patch
V = (0, 0)
T = set((i, j) for i in range(-2, 3) for j in range(-2, 3) if abs(i) + abs(j) <= 2)
def build(kinds, present, out):
    sites = sorted(set(kinds) | set(x for b in present for x in b) | {V})
    kk = {x: kinds.get(x, 'u') for x in sites}; kk[V] = 'u'
    bonds = sorted(present)
    slots = [x for x in sites for y in patch.nbrs(x) if y not in T]
    kn = dict(kk); kn[V] = 'd'
    return dict(v=V, sites=sites, kinds_cur=kk, kinds_next=kn, bonds_cur=bonds,
                bonds_next=[b for b in bonds if b != patch.bkey(V, out)], slots=slots, kind_all=kk)
