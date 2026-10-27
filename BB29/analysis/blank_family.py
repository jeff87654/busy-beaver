# blank_family.py MACH maxsteps : run the exact pair machine from the blank tape; compare all macro events with the model
import sys
from family import *
from hydra import ordinal, oshow, height
name=sys.argv[1]
pe,st=pm_events(name,{},0,CFG[name]['start'],int(sys.argv[2]),100000)
k0=next(i for i,e in enumerate(pe) if e is not None); print('  unclean events before first clean one:',k0, pe[:k0]); pe=pe[k0:]; first=pe[0]; me=[first]+model(*first,len(pe)-1)
bad=[i for i,(x,y) in enumerate(zip(pe,me)) if x!=y]
print(name,'pair steps',st,'events',len(pe),'mismatches',len(bad), 'first bad' if bad else '', bad[:1])
for e in pe[:8]: print('  K(a=%d,b=%d) d=%d height=%d  o=%s'%(e[0],e[1],e[3],height(e[2]),oshow(ordinal(e[2]))), '' if e is not pe[0] else ' hydra='+str(e[2]))
chops=[e for e in pe if e[0]!='HALT' and e[1]==0]
print('  first C(m)=K(m,0) configs:',[(e[0],oshow(ordinal(e[2]))) for e in chops[:4]])
