"""Independent literal checks for M14_fw3x4 (BB(14), Gemini 4 Neon), written for the independent audit of Neon's Coq
proof (2026-11-23); it shares no code with Neon's tools.   python m14_fw3x4_lit_chk.py   (a few seconds)
It checks: the core string (start G) and the TNF string (start A) are the same machine, all 14 states are reached,
M14_fw3's repo name and TNF form agree, the configuration after the 240-step opening (Boot_240), and the macro and
bridge rules of BB14_M14_fw3x4.v by literal simulation at small parameters (random right tails).
Tape model: config = (state, left, head, right); left/right are lists, nearest-to-head first, implicitly
followed by zeros forever.  Coq notation used by the proof (BusyCoq):
   l {{q}}> r  ==  state q, left l, head = hd r, right = tl r
   l <{{q}} r  ==  state q, left = tl l, head = hd l, right r
   x >> z (cons), xs *> z (prepend list), xs ^^ n (list repeated n times)."""
import random, sys

TNF = "1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_---0LF_0LN1LA_0RE1LN"
CORE = "1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LL1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LG1LN_1RN0LH_1RK0LL"
OLD_CORE = "1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_1LN1LK_1RK0LH_1LD0RK"
OLD_TNF = "1RB1RA_1RC1RJ_1RD0LK_0LE1RI_---0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM"
# the published name of M14_fw3 in the busy-beaver repo (halt written 1RZ)
OLD_REPO = "1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK"
ST = "ABCDEFGHIJKLMN"


def parse(s):
    rows = s.split("_")
    assert len(rows) == 14, len(rows)
    t = {}
    for i, row in enumerate(rows):
        assert len(row) == 6
        for sym in (0, 1):
            tr = row[3 * sym:3 * sym + 3]
            if tr == "---" or tr[2] == "Z":
                t[(ST[i], sym)] = None
            else:
                t[(ST[i], sym)] = (int(tr[0]), tr[1], tr[2])
    return t


def step(t, c):
    q, L, h, R = c
    tr = t[(q, h)]
    if tr is None:
        return None
    w, d, q2 = tr
    if d == "R":
        L2 = [w] + L
        h2 = R[0] if R else 0
        R2 = R[1:]
    else:
        R2 = [w] + R
        h2 = L[0] if L else 0
        L2 = L[1:]
    return (q2, L2, h2, R2)


def trim(xs):
    xs = list(xs)
    while xs and xs[-1] == 0:
        xs.pop()
    return xs


def norm(c):
    q, L, h, R = c
    return (q, tuple(trim(L)), h, tuple(trim(R)))


def run_to(t, c, target, maxsteps, plus=True):
    """steps from c until norm == norm(target); returns step count or None. plus: require >= 1 step."""
    tgt = norm(target)
    n = 0
    if not plus and norm(c) == tgt:
        return 0
    while n < maxsteps:
        c = step(t, c)
        n += 1
        if c is None:
            return None
        if norm(c) == tgt:
            return n
    return None


# ---- Coq-notation builders (sides are lists) ----
def rep(xs, n):
    return list(xs) * n


def R_(l, q, r):   # l {{q}}> r
    r = list(r) or [0]
    return (q, list(l), r[0], r[1:])


def L_(l, q, r):   # l <{{q}} r
    l = list(l) or [0]
    return (q, l[1:], l[0], list(r))


def W(j, b):
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = W(j - 1, x)
    return x


def Ca(j, b, z): return R_(rep([1], b) + rep([0, 1], j), "A", [0] + z)
def Ch(j, b, z): return L_(rep([0, 1], j), "H", [1] + rep([1], b) + [0] + z)
def Ce_z(p, a, c, d, z): return R_(rep([1], a + 2) + rep([0, 1], p), "I", rep([1, 0], c) + [0] + rep([1, 0], d) + z)
def Cd_z(p, b, d, z): return R_(rep([1], b + 2) + rep([0, 1], p), "I", rep([1, 0], d) + z)
def blk(a, z): return [1] + rep([1], a) + [0] + z
def c_end(p, a): return R_(rep([1], a + 7) + rep([0, 1], p), "K", [])


results = []


def check(name, src, tgt, maxsteps=10 ** 6, plus=True, t=None):
    t = t or TM
    n = run_to(t, src, tgt, maxsteps, plus)
    ok = n is not None
    results.append((name, ok, n))
    if not ok:
        print("MISMATCH", name, file=sys.stderr)
    return ok


def main():
    global TM
    out = []
    tnf, core = parse(TNF), parse(CORE)
    oldc, oldt, oldr = parse(OLD_CORE), parse(OLD_TNF), parse(OLD_REPO)
    TM = core
    # 1. relabelling: derive the first-visit (TNF) order of the core machine from G by simulation
    def first_visit(t, start, steps):
        c = (start, [], 0, [])
        order = [start]
        for i in range(steps):
            c = step(t, c)
            if c is None:
                break
            if c[0] not in order:
                order.append(c[0])
        return order
    order = first_visit(core, "G", 100000)
    out.append(f"core first-visit order from G: {''.join(order)} ({len(order)} states)")
    perm = {q: ST[i] for i, q in enumerate(order)}
    ok = len(order) == 14
    for (q, s), tr in core.items():
        tr2 = tnf[(perm[q], s)]
        exp = None if tr is None else (tr[0], tr[1], perm[tr[2]])
        ok &= tr2 == exp
    out.append(f"core --perm--> TNF table equal (all 28 entries): {ok}; perm = " +
               ", ".join(f"{a}->{b}" for a, b in sorted(perm.items())))
    file_perm = dict(zip("ABCDEFGHIJKLMN", "BCMNEIAKDHLFJG"))
    out.append(f"perm equals the file's perm_f: {perm == file_perm}")
    # canonical TNF also requires: first-visit order A.. and transitions; check TNF from A visits in order ABC..
    o2 = first_visit(tnf, "A", 100000)
    out.append(f"TNF first-visit order from A: {''.join(o2)} (canonical: {''.join(o2) == ST})")
    # old machine
    o3 = first_visit(oldc, "A", 100000)
    perm3 = {q: ST[i] for i, q in enumerate(o3)}
    ok3 = len(o3) == 14 and all(
        oldt[(perm3[q], s)] == (None if tr is None else (tr[0], tr[1], perm3[tr[2]])) for (q, s), tr in oldc.items())
    out.append(f"old core (start A) --first-visit perm--> old TNF: {ok3}; old core == repo name (1RZ as halt): {oldc == oldr}")
    # lockstep run 2e6 steps core vs tnf
    a = ("G", [], 0, []); b = ("A", [], 0, [])
    mism = 0
    for i in range(200_000):
        a = step(core, a); b = step(tnf, b)
        if (a is None) != (b is None) or (a and (perm[a[0]] != b[0] or norm(a)[1:] != norm(b)[1:])):
            mism += 1; break
        if a is None:
            break
    out.append(f"lockstep core(G) vs TNF(A) 200,000 steps: mismatches={mism}")
    # 2. boot 240 steps
    c = ("G", [], 0, [])
    for i in range(240):
        c = step(core, c)
    boot_tgt = Ch(6, 3, [0, 1, 0, 0, 0, 1, 1])
    out.append(f"after 240 steps from blank: state={c[0]} left={''.join(map(str, trim(c[1])))[::-1]} "
               f"head={c[2]} right={''.join(map(str, trim(c[3])))}; equals Ch 6 3 [0100011]: {norm(c) == norm(boot_tgt)}")
    # first time the Ch 6 3 config is hit
    out.append(f"first hit of Ch 6 3 [0100011] at step {run_to(core, ('G', [], 0, []), boot_tgt, 1000, False)}")
    ones = sum(trim(c[1])) + c[2] + sum(trim(c[3]))
    out.append(f"ones at step 240: {ones}")

    # 3. rules
    rnd = random.Random(20261123)
    def rz(k=None):
        k = rnd.randint(0, 6) if k is None else k
        return [rnd.randint(0, 1) for _ in range(k)]
    for _ in range(25):
        j, b, z = rnd.randint(0, 6), rnd.randint(0, 8), rz()
        check("CA_SH", Ca(j, b, [1, 0] + z), Ca(j + 1, b, z))
        check("CA_EXIT", Ca(j, b, [0] + z), R_(rep([1], b + 2) + rep([0, 1], j), "I", z))
        check("CA_CH", Ca(j, b, [1, 1] + z), Ch(j, b, [1] + z))
        check("CH_0", Ch(0, b, z), Ca(0, b + 3, z))
        check("CH_S", Ch(j + 1, b, z), Ca(j, 2, blk(b + 1, z)))
        k, c_, d_ = rnd.randint(0, 6), rnd.randint(0, 3), rnd.randint(0, 3)
        check("CA_SH_iter", Ca(j, b, rep([1, 0], k) + z), Ca(j + k, b, z), plus=False)
        p_ = rnd.randint(0, 6)
        check("E_EVEN", R_(rep([1], 2 * k + 2) + rep([0, 1], p_ + 1), "I", [1, 0] + z), Ch(p_, 1, rep([1, 0], k + 1) + [0] + z))
        m = rnd.randint(0, 6)
        check("C_REL_aux", Cd_z(p_ + 1, 2 * m + 1, d_ + 1, z), Ch(p_, 3, [0] + rep([1, 0], m) + [0] + rep([1, 0], d_) + z))
        a_ = rnd.randint(0, 8)
        check("D_STEP_aux", Ce_z(p_, a_, 0, d_ + 2, z), Ch(p_, a_ + 4, [0] + rep([1, 0], d_) + z))
        q_ = rnd.randint(0, 4)
        check("L_bounce_to_Ch", L_(rep([0, 1], p_ + 1), "L", rep([0, 1], q_ + 2) + z), Ch(p_, 6, rep([0, 1], q_) + z))
        check("Outer_reload_entry", Ce_z(p_, 2 * k, 0, 0, [1, 0, 0, 1, 0] + z), L_(rep([0, 1], p_), "L", rep([0, 1], k + 3) + [0, 0] + z))
        check("Boot_0011_to_Loop1", R_(rep([1], 2 * k + 2) + rep([0, 1], p_ + 1), "I", [0, 0, 1, 1]),
              L_(rep([0, 1], p_), "L", [0, 1, 0, 0] + rep([1, 0], k) + [1, 1, 1, 1]))
        check("Trans1_entry", Ce_z(p_, 2 * k, 0, 0, [1, 0, 0, 1, 1, 1, 1]), L_(rep([0, 1], p_), "L", rep([0, 1], k + 3) + [0, 1, 1, 1]))
        check("Trans1_010111_to_Ch", Ce_z(p_, a_, 0, 0, [1, 0, 1, 1, 1]), Ch(p_, a_ + 4, [1, 1]))
        check("Trans1_empty_even", R_(rep([1], 2 * k + 2) + rep([0, 1], p_ + 1), "I", []),
              L_(rep([0, 1], p_), "L", [0, 1, 0, 0] + rep([1, 0], k) + [1, 1]))
        check("Trans2_E0_to_L", Ce_z(p_, 2 * k, 0, 0, [1, 0, 0, 1, 1]), L_(rep([0, 1], p_), "L", rep([0, 1], k + 4)))
        check("Trans2_empty_odd", Cd_z(p_, 2 * m + 1, 0, []), L_(rep([0, 1], p_), "L", rep([0, 1], m + 2) + [1]))
        check("Trans2_011_reload", Ce_z(p_ + 1, 2 * k, 0, 0, [1, 1]), L_(rep([0, 1], p_), "L", [0, 1, 0, 0] + rep([1, 0], k + 2) + [0, 1, 1]))
        check("Trans3_0100011_reload", Ce_z(p_ + 1, 2 * k, 0, 0, [1, 0, 0, 0, 1, 1]), L_(rep([0, 1], p_), "L", [0, 1, 0, 0] + rep([1, 0], k + 4)))
        check("Trans4_E1_to_L", Ce_z(p_, 2 * k, 0, 0, [1, 0, 0, 1, 0]), L_(rep([0, 1], p_), "L", rep([0, 1], k + 3)))
        okh = check("Trans4_HALT", Ce_z(p_, a_, 0, 0, [1]), c_end(p_, a_))
        ce = c_end(p_, a_)
        results.append(("c_end_halted", core[(ce[0], ce[2])] is None, 0))
        results.append(("c_end ones = p+a+7", sum(ce[1]) + ce[2] + sum(ce[3]) == p_ + a_ + 7, 0))
    # rules that involve W: only small j / p
    for j in range(0, 3):
        for b in range(0, 4 if j < 2 else 2):
            for _ in range(3):
                z = rz()
                if W(j, b) < 5000:
                    check(f"CH_CA j={j}", Ch(j, b, z), Ca(j, W(j, b), z), maxsteps=10 ** 8)
    for p_ in range(0, 2):
        for k in range(0, 4):
            for _ in range(2):
                z, c_, d_ = rz(), rnd.randint(0, 2), rnd.randint(0, 2)
                check(f"CE_EVEN p'={p_}", Ce_z(p_ + 1, 2 * k, c_ + 1, d_, z), Ce_z(p_ + k + 1, W(p_, 1), c_, d_, z), maxsteps=10 ** 8)
                m = rnd.randint(0, 3)
                check(f"C_REL p'={p_}", Cd_z(p_ + 1, 2 * m + 1, d_ + 1, z), Ce_z(p_, W(p_, 3), m, d_, z), maxsteps=10 ** 8)
                a_ = rnd.randint(0, 3)
                check(f"D_STEP p={p_}", Ce_z(p_, a_, 0, d_ + 2, z), Cd_z(p_, W(p_, a_ + 4), d_, z), maxsteps=10 ** 8)
    for p_ in range(0, 2):
        for q_ in range(0, 3):
            z = rz()
            check(f"L_bounce_exec p={p_}", L_(rep([0, 1], p_ + 1), "L", rep([0, 1], q_ + 3) + z), Cd_z(p_, W(p_, 6), q_, [1] + z), maxsteps=10 ** 8)
    # sanity: a deliberately wrong target must fail (the checker can say no)
    neg = run_to(core, Ca(2, 3, [1, 0]), Ca(3, 4, []), 10 ** 5) is None
    out.append(f"negative control (wrong target rejected): {neg}")
    from collections import Counter
    tot = Counter(); bad = Counter()
    for name, ok, n in results:
        key = name.split(" ")[0]
        tot[key] += 1
        bad[key] += (not ok)
    out.append(f"rule checks: {len(results)} total, {sum(bad.values())} failures")
    for k in tot:
        out.append(f"   {k:24s} {tot[k]:4d} checks, {bad[k]} failures")
    print("\n".join(out))


if __name__ == "__main__":
    main()
