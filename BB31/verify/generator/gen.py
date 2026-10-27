"""Generate the Coq development of BB31 / BB33 from the templates in tmpl/.

  python gen.py            # writes BB31/verify/multifile/BB31_*.v and BB33/verify/multifile/BB33_*.v

The machines run the same pair-level program as BB29 up to relabeling (BB29/analysis/REPORT.md section 7);
only the role -> state map, the depth-scanner table and the initial configuration differ.
Templates use @M@ for the machine name; rules.v also takes @ROLES@, @E@, @E1@ (= E - 1).
The role table below was checked against the exact pair tables (bb29/pm_full.py), and every
rule is re-proved by busycoq's `execute` in the generated <M>_rules.v.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]   # repository root (this file is BB31/verify/generator/gen.py)

# state character -> Coq constructor: A..Z -> qA..qZ, then [ \ ] ^ _ ` a -> qAA..qAG
def ctor(c):
    i = ord(c) - 65
    if i < 26:
        return 'q' + chr(65 + i)
    return 'qA' + chr(65 + i - 26)

MACHINES = {
    'BB31': dict(
        dir='BB31/verify/multifile',
        roles=dict(B='B', D='D', F='F', H='H', K='K', N='M', P='O', V='W', Y='Z', RB='_', LB='\\'),
        dep='QSU]R', esc='T',
        steps=360,
        hydra='root -> X1 -> X2 -> X3 -> X4, X2 = (leaf, X3), X3 = (leaf, X4), X4 = 4 leaves',
        sp0='[[]; []; [leaf]; [leaf]; [leaf; leaf; leaf]]',
        x0='powtower 4 (ofin 4)', x0text='omega^omega^omega^omega^4',
        ind='Individual312',
        thms=[('halt', 'BB31_halt', 'halts BB31_tm.tm c0'),
              ('hardy_bound', 'BB31_halt', 'PRE Hardy.HH (HydraOrd.olist BB31_halt.hs0) 4 <= N + 2'),
              ('x0_eq', 'BB31_halt', 'HydraOrd.olist BB31_halt.hs0 = Ord.powtower 4 (Ord.ofin 4)'),
              ('hardy_score', 'BB31_bound', 'PRE Ord.FGH (Ord.tower 4) 4 <= N + 2'),
              ('sigma_lower_bound_w4', 'BB31_bound', 'PRE Ord.FGH (Ord.tower 4) 3 < N'),
              ('sigma_lower_bound', 'BB31_bound', 'PRE Ord.FGH (Ord.tower 3) 3 < N')],
    ),
    'BB33': dict(
        dir='BB33/verify/multifile',
        roles=dict(B='B', D='D', F='F', H='H', K='K', N='N', P='P', V='Z', Y=']', RB='A', LB='_'),
        dep='RTVX`SU', esc='W',
        steps=288,
        hydra='root -> Y1 -> Y2 -> Y3 -> Y4 -> Y5 -> Y6, Y4 = (leaf, Y5), Y6 = 3 leaves',
        sp0='[[]; []; []; []; [leaf]; []; [leaf; leaf]]',
        x0='powtower 6 (ofin 3)', x0text='omega^omega^omega^omega^omega^omega^3',
        ind='Individual332',
        thms=[('halt', 'BB33_halt', 'halts BB33_tm.tm c0'),
              ('hardy_bound', 'BB33_halt', 'PRE Hardy.HH (HydraOrd.olist BB33_halt.hs0) 4 <= N + 2'),
              ('x0_eq', 'BB33_halt', 'HydraOrd.olist BB33_halt.hs0 = Ord.powtower 6 (Ord.ofin 3)'),
              ('hardy_score', 'BB33_bound', 'PRE Ord.FGH (Ord.powtower 5 (Ord.ofin 3)) 4 <= N + 2'),
              ('sigma_lower_bound_w6', 'BB33_bound', 'PRE Ord.FGH (Ord.tower 6) 3 < N'),
              ('sigma_lower_bound', 'BB33_bound', 'PRE Ord.FGH (Ord.tower 4) 3 < N')],
    ),
}

TEMPLATES = ['rules.v', 'scan.v', 'round.v', 'game.v', 'halt.v', 'bound.v', 'check_bound.py']


def roles_block(m):
    r = m['roles']
    lines = []
    for role in ['B', 'D', 'F', 'H', 'K', 'N', 'P', 'V', 'Y', 'RB', 'LB']:
        lines.append(f'Notation r{role} := {ctor(r[role])} (only parsing).   (* {r[role]} *)')
    E = len(m['dep'])
    lines.append('')
    lines.append(f'(** Hydra height limit: depths 0..{E - 1} = ' + ' '.join(m['dep']) + f', escape at depth {E} = {m["esc"]}. *)')
    lines.append(f'Definition E : nat := {E}.')
    arms = ' | '.join(f'{i}%nat => {ctor(c)}' for i, c in enumerate(m['dep']))
    lines.append(f'Definition dq (i : nat) : Q := match i with {arms} | _ => {ctor(m["esc"])} end.')
    return '\n'.join(lines)


def main():
    for name, m in MACHINES.items():
        out = REPO / m['dir']
        out.mkdir(exist_ok=True)
        E = len(m['dep'])
        for t in TEMPLATES:
            src = HERE / 'tmpl' / t
            stem, ext = t.rsplit('.', 1)
            if (HERE / 'tmpl' / f'{stem}_{name}.{ext}').exists():
                src = HERE / 'tmpl' / f'{stem}_{name}.{ext}'
            if not src.exists() or t.endswith('.py'):   # the workspace checker is not published
                continue
            s = src.read_text(encoding='utf-8')
            s = s.replace('@ROLES@', roles_block(m)).replace('@E1@', str(E - 1)).replace('@E@', str(E))
            s = (s.replace('@STEPS@', str(m['steps'])).replace('@HYDRA@', m['hydra'])
                  .replace('@SP0@', m['sp0']).replace('@X0TEXT@', m['x0text']).replace('@X0@', m['x0']))
            thms = ',\n'.join(f"    '{n}': ('{mod}', " + (f"PRE + '{st[4:]}'" if st.startswith('PRE ') else f"'{st}'") + ')'
                              for n, mod, st in m['thms'])
            s = s.replace('@THMS@', thms).replace('@IND@', m['ind'])
            s = s.replace('@M@', name)
            dst = out / (t if t.endswith('.py') else f'{name}_{t}')
            if not dst.exists() or dst.read_text(encoding='utf-8') != s:
                dst.write_text(s, encoding='utf-8')
                print('wrote', dst)


if __name__ == '__main__':
    main()
