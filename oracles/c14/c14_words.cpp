// Oracle A: enumerate restricted-growth coordinate flip words,
// independent of all manuscript cycle counts.
#include <array>
#include <cstdint>
#include <iostream>
#include <cassert>
using u128=unsigned __int128;
constexpr int L=14;
std::array<unsigned long long,8> P{};
std::array<unsigned long long,15> nodes{};
void dfs(int step,int used,int vertex,u128 visited) {
    ++nodes[step];
    if(step==L) { if(vertex==0) ++P[used]; return; }
    for(int col=0;col<=used && col<7;++col) {
        int new_used=used+(col==used);
        int v2=vertex^(1<<col);
        if(step==L-1) {if(v2==0) ++P[new_used]; continue;}
        if(v2==0) continue;
        u128 bit=((u128)1)<<v2;
        if(visited & bit) continue;
        // Any bit set in v2 must be toggled in remaining steps.
        if(__builtin_popcount((unsigned)v2)>L-step-1) continue;
        dfs(step+1,new_used,v2,visited|bit);
    }
}
unsigned long long fact(int n){unsigned long long x=1;for(int i=2;i<=n;i++)x*=i;return x;}
unsigned long long choose(int n,int k){return fact(n)/(fact(k)*fact(n-k));}
int main(){dfs(0,0,0,(u128)1); for(int k=0;k<=7;k++)std::cout<<"P["<<k<<"]="<<P[k]<<"\n";
 for(int n=4;n<=7;++n){ unsigned long long oriented_at_origin=0;
 for(int k=1;k<=n && k<=7;k++) oriented_at_origin+=choose(n,k)*fact(k)*P[k];
 assert(((1ULL<<n)*oriented_at_origin)%28==0);
 std::cout<<"Q"<<n<<" root_oriented="<<oriented_at_origin<<" cycles="<<((1ULL<<n)*oriented_at_origin/28)<<"\n"; }
 for(int i=0;i<15;i++)std::cout<<"nodes["<<i<<"]="<<nodes[i]<<"\n";
}
