"""zeros_filter.py: find grow-and-count candidates in mini-follower histories by the length of the CLEARED list.

Input: a history TSV in the mfg_batch.py format (plain or .gz), one machine per line:
    machine <TAB> kind <TAB> nstages <TAB> bigjumps <TAB> history
where history is ' ; '-joined stage records; the jump records read
    J k=<tokens> far=<clean|junk> ev=<event> zeros=<zeros> r=<representatives>
k counts all tokens of the list at the jump, zeros= the zero digits (D1 tokens) next to the event, i.e. the list
that the jump clears.  k - zeros is the number of non-zero tokens (parked values, counters, blockers).

A machine is selected when, over >= S jump records (split into three equal windows; peaks are used because one
period of these machines spans several jumps and the counts oscillate within a period):
  grow : the peak of zeros= increases from window to window and the last peak is >= G x the first peak;
  count: the peak of the non-zero token count k - zeros decreases from window to window.
LOOP rows (the follower found an affine loop) are skipped unless --kinds says otherwise.  Machines with identical jump
histories (siblings differing only in slots the run never reads) are grouped; groups are ranked by the zeros growth
factor (last peak / first peak).

--compare-k adds the old k-based measure for comparison: the growth of k per jump after the 4th jump (as in
ana.py, whose default threshold is 30), the rank of each group under it, and the k-based top list.

  python zeros_filter.py HISTORY.tsv[.gz] [--grow 2] [--min-jumps 8] [--kinds HALT,MAXSTAGES,TIME,WIDE,FAIL,CRASH]
                         [--top 50] [--members] [--compare-k] [--show MACHINE ...]

Screening only: the histories come from single residue-class representatives of huge values, so a selection is a
candidate to be checked (literal replays, symbolic follow2, a proof), not a result."""
import argparse
import gzip
import re
import sys
from collections import defaultdict

JREC = re.compile(r'J k=(\d+) far=(\S+) ev=(\S+) zeros=(\d+) r=\S+')


def read_rows(path):
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt') as f:
        for line in f:
            p = line.rstrip('\r\n').split('\t')
            if len(p) < 5:
                continue
            js = JREC.findall(p[4])
            yield p[0], p[1], [int(x[0]) for x in js], [int(x[3]) for x in js], p[4].split(' ; ')[-1]


def thirds(v):
    t = len(v) // 3
    return [max(v[:t]), max(v[t:len(v) - t]), max(v[len(v) - t:])]


def stats(ks, zs, S, G):
    """(selected, zeros peaks, non-zero peaks) for one jump history"""
    if len(zs) < max(S, 3):
        return False, None, None
    zp = thirds(zs)
    nzp = thirds([k - z for k, z in zip(ks, zs)])
    grow = zp[0] < zp[1] < zp[2] and zp[2] >= G * max(1, zp[0])
    count = nzp[0] > nzp[1] > nzp[2]
    return grow and count, zp, nzp


def kgrowth(ks):
    """ana.py's measure: growth of k per jump after the 4th jump"""
    return (ks[-1] - ks[3]) / max(1, len(ks) - 3) if len(ks) >= 4 else None


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('file')
    ap.add_argument('--grow', type=float, default=2.0, help='last zeros peak >= GROW x first peak (default 2)')
    ap.add_argument('--min-jumps', type=int, default=8, help='at least this many jump records (default 8)')
    ap.add_argument('--kinds', default='HALT,MAXSTAGES,TIME,WIDE,FAIL,CRASH',
                    help='verdicts to consider (default: all but LOOP); HALT alone = halters only')
    ap.add_argument('--top', type=int, default=50)
    ap.add_argument('--members', action='store_true', help='list every machine of each selected group')
    ap.add_argument('--compare-k', action='store_true', help='show the k-based (ana.py) measure and ranking')
    ap.add_argument('--show', nargs='*', default=[], help='machines to report whether selected or not')
    a = ap.parse_args()
    kinds = set(a.kinds.split(','))

    groups = defaultdict(list)          # (kind, k/zeros history, last record) -> machines
    hist = {}
    nrows = 0
    for m, kind, ks, zs, last in read_rows(a.file):
        nrows += 1
        key = (kind, tuple(ks), tuple(zs), last)
        groups[key].append(m)
        hist[m] = key

    sel, kall = [], []
    for key, ms in groups.items():
        kind, ks, zs, last = key
        if kind not in kinds:
            continue
        ok, zp, nzp = stats(ks, zs, a.min_jumps, a.grow)
        kg = kgrowth(ks)
        if kg is not None:
            kall.append((kg, key))
        if ok:
            sel.append((zp[2] / max(1, zp[0]), key, zp, nzp))
    sel.sort(key=lambda r: -r[0])
    kall.sort(key=lambda r: -r[0])
    krank = {key: i + 1 for i, (_, key) in enumerate(kall)}

    print(f'# {a.file}: {nrows} rows, {len(groups)} distinct histories; kinds {",".join(sorted(kinds))}; '
          f'>= {a.min_jumps} jumps, zeros peak growth >= {a.grow}, non-zero peak falling')
    print(f'# selected {len(sel)} groups ({sum(len(groups[r[1]]) for r in sel)} machines)')
    cols = ['rank', 'growth', 'zeros_peaks', 'nonzero_peaks', 'jumps', 'kind', 'n_machines']
    if a.compare_k:
        cols += ['k_first..last', 'k_growth/jump', f'k_rank/{len(kall)}']
    cols += ['machine', 'last_record']
    print('\t'.join(cols))
    for i, (g, key, zp, nzp) in enumerate(sel[:a.top]):
        kind, ks, zs, last = key
        ms = groups[key]
        row = [str(i + 1), f'{g:.2f}', '/'.join(map(str, zp)), '/'.join(map(str, nzp)), str(len(zs)), kind, str(len(ms))]
        if a.compare_k:
            kg = kgrowth(ks)
            row += [f'{ks[0]}..{ks[-1]}', f'{kg:.1f}' if kg is not None else '-', str(krank.get(key, '-'))]
        row += [ms[0], last[:40]]
        print('\t'.join(row))
        if a.members:
            for m in ms[1:]:
                print(f'\t\t\t\t\t\t\t{m}')

    if a.compare_k:
        n30 = sum(1 for kg, _ in kall if kg >= 30)
        print(f'# k-based measure (ana.py): {n30} of {len(kall)} groups have k growth >= 30 per jump; top {min(10, len(kall))}:')
        for kg, key in kall[:10]:
            ok, zp, nzp = stats(key[1], key[2], a.min_jumps, a.grow)
            print(f'#   k_growth={kg:.1f}\tk={key[1][0]}..{key[1][-1]}\tzeros={key[2][0]}..{key[2][-1]}\t{key[0]}\t'
                  f'zeros-filter={"yes" if ok else "no"}\t{groups[key][0]}')

    for m in a.show:
        if m not in hist:
            print(f'# show {m}: not in the file')
            continue
        key = hist[m]
        kind, ks, zs, last = key
        ok, zp, nzp = stats(ks, zs, a.min_jumps, a.grow)
        pos = next((i + 1 for i, r in enumerate(sel) if r[1] == key), None)
        kg = kgrowth(ks)
        print(f'# show {m}: kind {kind}, {len(zs)} jumps, zeros {zs[0] if zs else "-"}..{zs[-1] if zs else "-"} '
              f'(peaks {zp}), non-zero peaks {nzp}, selected={"yes, rank " + str(pos) if pos else "no"}'
              + (f', k {ks[0]}..{ks[-1]}, k growth/jump {kg:.1f}, k rank {krank.get(key, "-")}/{len(kall)}' if kg is not None else ''))


if __name__ == '__main__':
    main()
