import sys
sys.path.insert(0, 'C:/Users/Lenovo/.workbuddy/skills/tm-halting-proof/scripts')
from tm_lib import parse_machine

M = '2RD1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LG1LD_1RC2LE1LG_1RG0LA1RZ_1LD2RA2LG'
tm = parse_machine(M)

class Stream:
    def __init__(self, h, t):
        self.h = h
        self.t = t
    def hd(self): return self.h
    def tl(self): return self.t

def const(x):
    s = Stream(x, None)
    s.t = s
    return s

def lpow(x, n, s):
    for _ in range(n): s = Stream(x, s)
    return s

def from_list(xs, tail):
    for x in reversed(xs): tail = Stream(x, tail)
    return tail

def show_stream(s, n=14):
    out = []
    cur = s
    for _ in range(n):
        out.append(cur.hd())
        cur = cur.tl()
    return ''.join(str(x) for x in out) + '...'

def show(cfg):
    l, st, hd, r = cfg
    return '...' + show_stream(l)[::-1] + '[' + st + ':' + str(hd) + ']' + show_stream(r)

def step(cfg):
    l, st, hd, r = cfg
    w, d, q = tm.table[('ABCDEFG'.index(st), hd)]
    q = 'Z' if q is None else 'ABCDEFG'[q]
    if d == 'L':
        return (l.tl(), q, l.hd(), Stream(w, r))
    return (Stream(w, l), q, r.hd(), r.tl())

def bcfg(k, n, mv, rlist):
    l = lpow(2, k, lpow(1, 2 * mv + 1, const(0)))
    r = lpow(1, n, from_list(rlist, const(0)))
    return (l, 'B', r.hd(), r.tl())

if __name__ == '__main__':
    for params in [(1, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 1), (3, 1, 0)]:
        print('=== Bcfg', params, '===')
        cfg = bcfg(*params, [0, 1, 2])
        for st in range(0, 60):
            print('%3d %s' % (st, show(cfg)))
            cfg = step(cfg)
