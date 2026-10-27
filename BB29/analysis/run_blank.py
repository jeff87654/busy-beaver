from check_hydra import *
t={}; evs=pm_events(t,0,'A>',3000000,400)
first=evs[0]; print('first event',first)
a,b,h,d=first
mod=[first]+model(a,b,h,d,len(evs)-1)
bad=0
for i,(x,y) in enumerate(zip(evs,mod)):
    if not same(x,y):
        print('MISMATCH at event',i); print(' tm   ',x); print(' model',y); bad=1; break
print('compared',min(len(evs),len(mod)),'events; ok' if not bad else '')
for e in evs[:12]: print(e[0],e[1],e[3],oshow(ordinal(e[2])))
