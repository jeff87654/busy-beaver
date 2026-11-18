import sys
from trace_stream import Stream, const, lpow, from_list, show, step, bcfg, tm

def to_list(s, n=40):
    out = []
    cur = s
    for _ in range(n):
        out.append(cur.hd())
        cur = cur.tl()
    return out

def recognize(cfg):
    l, st, hd, r = cfg
    if st != 'B':
        return None
    L = to_list(l, 40)
    k = 0
    while k < len(L) and L[k] == 2: k += 1
    o = 0
    while k + o < len(L) and L[k + o] == 1: o += 1
    if o == 0 or o % 2 == 0: return None
    mv = (o - 1) // 2
    R = [hd] + to_list(r, 40)
    n = 0
    while n < len(R) and R[n] == 1: n += 1
    return (k, n, mv, tuple(R[n:n + 8]))

def g(k, x):
    if k == 0: return x + 1
    y = 0
    for _ in range(2 * x + 2): y = g(k - 1, y)
    return y

def run_until(cfg, pred, limit=2000000):
    for st in range(limit):
        q = recognize(cfg)
        if pred(cfg, q, st): return st, cfg
        if cfg[1] == 'Z' or tm.table[('ABCDEFG'.index(cfg[1]), cfg[2])][2] is None:
            return st, cfg
        cfg = step(cfg)
    return limit, cfg

print('=== B_rule check: start B(k,n,m) 0 7 7 2, find B(k,0,exp) ===')
tail = [0, 1, 1, 1, 2]  # distinctive
for k, n, mv in [(1, 1, 0), (1, 2, 0), (1, 1, 1), (2, 1, 0), (2, 2, 0), (2, 1, 1), (3, 1, 0)]:
    cfg = bcfg(k, n, mv, tail)
    exp = mv
    for _ in range(n): exp = g(k - 1, exp)
    st, cfg2 = run_until(cfg, lambda c, q, s: q is not None and q[0] == k and q[1] == 0 and q[2] == exp)
    q = recognize(cfg2)
    ok = q is not None and q[:3] == (k, 0, exp)
    print('B(%d,%d,%d) -> B(%d,0,%d): steps=%d got=%s tail_ok=%s' %
          (k, n, mv, k, exp, st, q[:3] if q else None,
           q is not None and q[3] == tuple(tail)))
    if q: print('   got tail:', q[3], 'expected:', tuple(tail))

print()
print('=== Check ALL B-configs visited from B(2,1,0), with tail marker ===')
cfg = bcfg(2, 1, 0, [0, 1, 1, 1, 2])
seen = set()
for st in range(200):
    q = recognize(cfg)
    if q and q[:3] not in seen:
        seen.add(q[:3])
        print('%3d B(%d,%d,%d) tail=%s' % (st, q[0], q[1], q[2], q[3]))
    if tm.table[('ABCDEFG'.index(cfg[1]), cfg[2])][2] is None: break
    cfg = step(cfg)
