// Oracle B: independent even-block partition enumeration.
// Every closed coordinate-flip word of length 14 uniquely determines a
// partition of its 14 step positions by coordinate, with every block even.
// Blocks are canonically ordered by their smallest position.
// Unlike Oracle A this never enumerates arbitrary partial cube paths.
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
using namespace std;
constexpr int L=14;
static array<uint8_t,L> label{};
static array<unsigned long long,8> total{},simple{};
static unsigned long long leafs=0;
using u128=unsigned __int128;
void check128(int k) {
    ++total[k]; ++leafs;
    int vertex=0;
    u128 seen=1;
    for(int t=0;t<L;++t) {
        vertex ^= 1<<label[t];
        if(t<L-1) {
            if(vertex==0 || (seen & (u128(1)<<vertex)))return;
            seen |= u128(1)<<vertex;
        }
    }
    if(vertex==0)++simple[k];
}
void partition(uint16_t remaining,int next_id) {
    if(!remaining){check128(next_id);return;}
    if(next_id>=7)return;
    int first=std::countr_zero(remaining);
    uint16_t other=remaining^(uint16_t(1)<<first);
    // At each stage select an odd-sized subset of the remaining positions;
    // together with first it forms a 2,4,... sized coordinate block.
    for(uint16_t sub=other;sub;sub=(sub-1)&other) {
        if((std::popcount(sub)&1)==0)continue;
        uint16_t block=sub|(uint16_t(1)<<first);
        for(int t=0;t<L;++t) if(block &(uint16_t(1)<<t))label[t]=next_id;
        partition(remaining^block,next_id+1);
    }
}
int main(){partition((1<<L)-1,0);
 for(int k=0;k<=7;++k)cout<<"even_partitions["<<k<<"]="<<total[k]<<" simple["<<k<<"]="<<simple[k]<<"\n";
 cout<<"leafs="<<leafs<<"\n";
 assert(total[7]==135135);
 assert(simple[7]==38232);
}
