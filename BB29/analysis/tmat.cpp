// tmat <machine> <steps...>: run from blank; at each listed step count print "step state pos lo bits" (bits from lo to hi)
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
int main(int argc,char**argv){
  std::string m=argv[1]; int n=(m.size()+1)/7; int W[64][2],D[64][2],N[64][2];
  for(int i=0;i<n;i++)for(int s=0;s<2;s++){const char*t=m.c_str()+7*i+3*s; if(t[0]=='-'){N[i][s]=-1;continue;} W[i][s]=t[0]-'0'; D[i][s]=t[1]=='R'?1:-1; N[i][s]=t[2]-'A';}
  size_t SZ=1<<26; std::vector<unsigned char> tape(SZ,0); long long base=SZ/2,pos=base,lo=pos,hi=pos; int q=0; long long st=0;
  for(int k=2;k<argc;k++){ long long target=atoll(argv[k]);
    while(st<target){ int s=tape[pos]; int nq=N[q][s]; if(nq<0){printf("HALT %lld\n",st);return 0;}
      tape[pos]=W[q][s]; pos+=D[q][s]; q=nq; st++; if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
    printf("%lld %c %lld %lld ",st,'A'+q,pos-base,lo-base); for(long long i=lo;i<=hi;i++) putchar('0'+tape[i]); putchar('\n'); }
}
