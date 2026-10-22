// Independent exhaustive all-k<=8 check of the matching/cycle criterion.
// Never constructs a hypercube or evaluates c_{2k}(Q_n).
// For each perfect matching of 2k step positions, compares
// chord-intersection connectivity against distinct mod-2 prefix sums.
// k=8 processes all (16-1)!! = 2,027,025 matchings.
#include <array>
#include <cstdint>
#include <iostream>
using namespace std;
static uint64_t matchings_count=0,connected_count=0,simple_count=0,mismatches=0;
static int endpoint_color[16], a[8], b[8];

static bool chord_connected(int k) {
    bool reachable[8]={false};reachable[0]=true;
    int stack[8],top=0;stack[top++]=0;
    int touched=1;
    while(top) {
        int i=stack[--top];
        for(int j=0;j<k;j++) {
            if(reachable[j])continue;
            bool x=(a[i]<a[j] && a[j]<b[i] && b[i]<b[j]) ||
                   (a[j]<a[i] && a[i]<b[j] && b[j]<b[i]);
            if(x){reachable[j]=true;stack[top++]=j;touched++;}
        }
    }
    return touched==k;
}
static bool prefix_simple(int k) {
    bool seen[256]={false};seen[0]=true;
    int x=0;
    for(int p=0;p<2*k;p++) {
        x^=1<<endpoint_color[p];
        if(p<2*k-1){if(seen[x])return false;seen[x]=true;}
    }
    return x==0;
}
static void dfs(uint32_t mask,int depth,int k) {
    if(depth==k) {
        matchings_count++;
        bool c=chord_connected(k), s=prefix_simple(k);
        connected_count+=c;simple_count+=s;
        if(c!=s)mismatches++;
        return;
    }
    int first=0;
    while(mask&(1u<<first))first++;
    for(int j=first+1;j<2*k;j++) {
        if(mask&(1u<<j))continue;
        a[depth]=first;b[depth]=j;
        endpoint_color[first]=endpoint_color[j]=depth;
        dfs(mask|(1u<<first)|(1u<<j),depth+1,k);
    }
}
int main() {
    const uint64_t expected_totals[]={0,1,3,15,105,945,10395,135135,2027025};
    const uint64_t expected_connected[]={0,1,1,4,27,248,2830,38232,593859};
    for(int k=2;k<=8;k++) {
        matchings_count=connected_count=simple_count=mismatches=0;
        dfs(0,0,k);
        cout<<"k="<<k<<" matchings="<<matchings_count
            <<" connected="<<connected_count<<" simple="<<simple_count
            <<" mismatches="<<mismatches<<'\n';
        if(matchings_count!=expected_totals[k] ||
           connected_count!=expected_connected[k] ||
           simple_count!=expected_connected[k] || mismatches)return 1;
    }
    cout<<"PASS: all 2,027,025 8-chord pairings, 0 predicate mismatches\n";
}
