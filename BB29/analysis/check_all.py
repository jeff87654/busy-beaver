# check_all.py : rerun every validation in this directory (moderate sizes; ~5-10 min). Prints one line per check.
import subprocess, sys, os
here=os.path.dirname(os.path.abspath(__file__))
def run(args, timeout=1800):
    r=subprocess.run([sys.executable,'-u']+args,cwd=here,capture_output=True,text=True,timeout=timeout,creationflags=0x08000000|0x40 if os.name=='nt' else 0)
    return (r.stdout+r.stderr).strip().splitlines()
jobs=[
 (['blank_family.py','BB29','4000000'],'blank-tape run vs hydra model (BB29)'),
 (['blank_family.py','BB31','4000000'],'blank-tape run vs hydra model (BB31)'),
 (['blank_family.py','BB33','4000000'],'blank-tape run vs hydra model (BB33)'),
 (['rand_family.py','BB29','11','300','3'],'random K(a,b,h,d), height<=3 (BB29)'),
 (['rand_family.py','BB31','12','200','5'],'random K(a,b,h,d), height<=5 (BB31)'),
 (['rand_family.py','BB33','13','200','7'],'random K(a,b,h,d), height<=7 (BB33)'),
 (['rand_family.py','BB29','14','150','4'],'NEGATIVE control: height 4 on BB29 (expect bad>0)'),
 (['tmcross.py','BB29','6000000','1,2,3,6,21,61,151'],'TM-literal cross-check (BB29)'),
 (['tmcross.py','BB31','6000000','1,2,3,6,21,61,151'],'TM-literal cross-check (BB31)'),
 (['tmcross.py','BB33','6000000','1,2,3,6,21,61,151'],'TM-literal cross-check (BB33)'),
 (['ordinal_check.py','BB29','6000000','BB29,BB31,BB33'],'ordinal step alpha->alpha[m+3] / alpha-1 at chop configs'),
 (['formula_check.py'],'closed form W/T_k vs model run to HALT'),
 (['usage.py','BB29'],'TM transitions never used (BB29)'),
]
for args,desc in jobs:
    try: out=run(args)
    except subprocess.TimeoutExpired: out=['TIMEOUT']
    print('==',desc); [print('   ',l) for l in out if 'unsorted' not in l][:12] if False else None
    for l in [l for l in out if 'unsorted' not in l][-8:]: print('   ',l)
