"""Select the screen set from renum output (reconstruction of the selection used for data/mf_GH.tsv).
Keeps a printed renum leaf when
  - E0 (the base machine's halting slot) points into a new state (I or J),
  - an undefined transition is reachable in the state graph (otherwise the machine cannot halt at all), and
  - it is not an early small halter: all starts halt and the first start (b = 0) halts within EARLY steps.
Pads machines to 10 states with ------ (stage35g reads 10-state strings).
  python select_set.py RENUM_OUT.tsv [EARLY=100000] > set.txt"""
import sys


def halt_possible(m):
    rows = m.split('_')
    seen, todo = {0}, [0]
    while todo:
        q = todo.pop()
        for c in (0, 1):
            x = rows[q][3 * c:3 * c + 3]
            if x[2] in '-Z':
                return True
            n = ord(x[2]) - 65
            if n not in seen:
                seen.add(n)
                todo.append(n)
    return False


def main():
    early = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    for line in open(sys.argv[1]):
        f = line.rstrip('\r\n').split('\t')
        if f[0].startswith('#'):
            continue
        m = f[0]
        while m.count('_') < 9:
            m += '_------'
        if m.split('_')[4][2] not in 'IJ' or not halt_possible(m):
            continue
        if all(x.startswith('H') for x in f[1:]) and int(f[1].split(':')[1]) <= early:
            continue
        print(m)


if __name__ == '__main__':
    main()
