// dump <machine> <steps> <snapStates> <maxSnaps> <align>: on entry to a snap state print step, state, and pair letters (00=0 01=c 10=x 11=y), head marked by '<Q>' before its pair or '<Q:2>' if on 2nd cell
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
int main(int argc,char**argv){
  std::string m=argv[1]; long long maxs=atoll(argv[2]); std::string sn=argv[3]; long long maxsn=atoll(argv[4]); int al=atoi(argv[5]);
  bool snap[64]={0}; for(char c:sn) snap[c-'A']=1;
  int n=(m.size()+1)/7; int W[64][2],D[64][2],N[64][2];
  for(int i=0;i<n;i++)for(int s=0;s<2;s++){const char*t=m.c_str()+7*i+3*s; if(t[0]=='-'){N[i][s]=-1;continue;} W[i][s]=t[0]-'0'; D[i][s]=t[1]=='R'?1:-1; N[i][s]=t[2]-'A';}
  size_t SZ=1<<27; std::vector<unsigned char> tape(SZ,0); long long pos=SZ/2, lo=pos, hi=pos; int q=0; long long st=0; long long cnt=0;
  long long base=SZ/2; // cell base+k has absolute coordinate k
  while(st<maxs){
    int s=tape[pos]; int nq=N[q][s];
    if(nq<0){ long long ones=0; for(long long i=lo;i<=hi;i++) ones+=tape[i]; printf("HALT %lld ones=%lld\n",st,ones); return 0;}
    tape[pos]=W[q][s]; pos+=D[q][s]; q=nq; st++;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<=2||pos>=(long long)SZ-3){printf("overflow\n");return 1;}
    if(snap[q] && cnt<maxsn){ cnt++;
      long long a=lo-2; while(((a-base-al)%2+2)%2) a--;
      printf("%lld %c ",st,'A'+q);
      for(long long i=a;i<=hi+2;i+=2){ if(i==pos) printf("<%c>",'A'+q); else if(i+1==pos) printf("<%c:2>",'A'+q);
        int p=tape[i]*2+tape[i+1]; putchar("0cxy"[p]); }
      putchar('\n'); }
  }
  long long ones=0; for(long long i=lo;i<=hi;i++) ones+=tape[i];
  printf("END %lld ones=%lld width=%lld\n",st,ones,hi-lo+1);
}
