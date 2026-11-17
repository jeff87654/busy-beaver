import sys
from trace_stream import Stream, const, lpow, from_list, show, step, bcfg, tm

def lst(s, n=20):
    out = []
    cur = s
    for _ in range(n):
        out.append(cur.hd())
        cur = cur.tl()
    return out

# Trace Bcfg 2 1 0, print left/right as nearest-first lists with state & head
cfg = bcfg(2, 1, 0, [0, 1, 1, 1, 2])
for st in range(0, 50):
    l, q, hd, r = cfg
    print('%3d %-2s L=%-14s <hd=%d> R=%s' % (st, q, ''.join(map(str, lst(l, 10))), hd, ''.join(map(str, lst(r, 12)))))
    if tm.table[('ABCDEFG'.index(q), hd)][2] is None:
        print('HALT'); break
    cfg = step(cfg)
