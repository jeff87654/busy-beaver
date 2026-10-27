# comp.py: read dump lines from stdin; tokenize pair-letter strings and compress tandem repeats
import sys,re
def tok(s):
    # tokens: [j] = xx(yx)^j yy ; keep head markers
    s=re.sub(r'xx((?:yx)*)yy', lambda m:' [%d] '%(len(m.group(1))//2), s)
    return s
def tandem(toks):
    # greedy compress repeats of token sequences, periods up to 12
    changed=True
    while changed:
        changed=False
        best=None
        for p in range(1,13):
            i=0
            while i+2*p<=len(toks):
                k=1
                while i+(k+1)*p<=len(toks) and toks[i+k*p:i+(k+1)*p]==toks[i:i+p]: k+=1
                if k>=2:
                    gain=(k-1)*p
                    if best is None or gain>best[0]: best=(gain,i,p,k)
                    i+=k*p
                else: i+=1
        if best and best[0]>=2:
            g,i,p,k=best
            unit=toks[i:i+p]
            t='('+' '.join(unit)+')^%d'%k if p>1 else unit[0]+'^%d'%k
            toks=toks[:i]+[t]+toks[i+k*p:]
            changed=True
    return toks
for line in sys.stdin:
    p=line.split(' ',2)
    if len(p)<3: print(line.strip()); continue
    s=tok(p[2].strip())
    toks=[]
    for part in s.split():
        if part.startswith('['): toks.append(part)
        else: toks.extend(re.findall(r'<[^>]*>|.',part))
    print(p[0],p[1],' '.join(tandem(toks)))
