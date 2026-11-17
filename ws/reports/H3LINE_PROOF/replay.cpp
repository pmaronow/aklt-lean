// Independent exact replay of H3-line, as specified in h3line.tex.
// No source or executable from MATH_FIT/programs is included or invoked.
// Build: g++ -std=c++20 -O3 -Wall -Wextra replay.cpp -lz -o replay
// Run:   ./replay [input-data-directory]
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/rational.hpp>
#include <zlib.h>

using Big = boost::multiprecision::cpp_int;
using Rat = boost::rational<Big>;
using Wide = unsigned __int128;
using Pt = std::pair<int,int>;
using Bond = std::pair<Pt,Pt>;
constexpr int N = 3741, M = 10, L = 12, R = 70, B = 20;
constexpr uint64_t V = uint64_t(1)<<20, D = uint64_t(1)<<48;
const std::array<Pt,4> step{{{1,0},{0,1},{-1,0},{0,-1}}};
const Rat xs(1000,961), xt(200,187), hC(6,5);
const std::array<Rat,2> alpha{Rat(145217,1000000),Rat(150000,1000000)};
const std::array<Rat,2> beta{Rat(352782,1000000),Rat(357549,1000000)};
const std::array<Rat,2> beta1{Rat(340008,1000000),Rat(344661,1000000)};
const Big Delta = 13478025000ULL;
std::filesystem::path source;

void need(bool yes, const std::string &s) {
    if (!yes) throw std::runtime_error(s);
}
Pt add(Pt x, int d) { return {x.first+step[d].first,x.second+step[d].second}; }
Bond bond(Pt x, Pt y) { return x<y ? Bond{x,y} : Bond{y,x}; }
Big power(Big a, unsigned n) {
    Big r=1;
    while(n) { if(n&1) r*=a; n>>=1; if(n) a*=a; }
    return r;
}
Rat ratpower(Rat a, unsigned n) {
    return Rat(power(a.numerator(),n),power(a.denominator(),n));
}
Rat rpower(int n) { return n>=0 ? ratpower(Rat(12,13),n) : ratpower(Rat(13,12),-n); }
Big floorq(const Rat &x) { need(x>=Rat(0),"negative floor"); return x.numerator()/x.denominator(); }
Big ceilq(const Rat &x) { need(x>=Rat(0),"negative ceiling"); return (x.numerator()+x.denominator()-1)/x.denominator(); }
uint64_t u64(const Big &x) {
    need(x>=0 && x<=std::numeric_limits<uint64_t>::max(),"u64 overflow");
    return x.convert_to<uint64_t>();
}
uint64_t ceiling(const Rat &t) {
    Big p=ceilq(Rat(D)*t);
    need(Rat(p,D)>=t && (p==0 ? t==Rat(0) : Rat(p-1,D)<t),"ceiling enclosure");
    return u64(p);
}
std::string strwide(Wide x) {
    if(!x) return "0";
    std::string s;
    while(x) { s.push_back('0'+x%10); x/=10; }
    std::reverse(s.begin(),s.end()); return s;
}
unsigned bits(Wide x) { unsigned n=0; while(x) { x>>=1; ++n; } return n; }
unsigned bits(const Big &x) { return x==0 ? 0 : boost::multiprecision::msb(x)+1; }
unsigned bits(uint32_t x) { return std::bit_width(x); }
std::string fraction(const Rat &x) {
    return x.numerator().str()+"/"+x.denominator().str();
}

// Explicit little-endian decoders; witness files are not native structs.
struct Input {
    std::ifstream plain;
    gzFile zip=nullptr;
    std::string name;
    explicit Input(const std::filesystem::path &p, bool compressed=false):name(p.string()) {
        if(compressed) { zip=gzopen(name.c_str(),"rb"); need(zip,"open "+name); }
        else { plain.open(p,std::ios::binary); need(bool(plain),"open "+name); }
    }
    ~Input() { if(zip) gzclose(zip); }
    void read(unsigned char *dst, size_t n) {
        if(zip) {
            while(n) {
                unsigned take=std::min<size_t>(n,1<<24);
                int got=gzread(zip,dst,take);
                need(got==int(take),"truncated "+name);
                dst+=take; n-=take;
            }
        } else { plain.read(reinterpret_cast<char*>(dst),n); need(size_t(plain.gcount())==n,"truncated "+name); }
    }
    uint64_t qword() {
        unsigned char b[8]; read(b,8); uint64_t u=0;
        for(int j=0;j<8;++j) u|=uint64_t(b[j])<<(8*j);
        return u;
    }
    std::vector<uint32_t> words(size_t n) {
        std::vector<unsigned char> raw(4*n); read(raw.data(),raw.size());
        std::vector<uint32_t> a(n);
        for(size_t j=0;j<n;++j)
            a[j]=uint32_t(raw[4*j]) | uint32_t(raw[4*j+1])<<8 |
                 uint32_t(raw[4*j+2])<<16 | uint32_t(raw[4*j+3])<<24;
        return a;
    }
    void end() {
        unsigned char c;
        if(zip) {
            int got=gzread(zip,&c,1); need(got==0 && gzeof(zip),"trailing bytes or gzip error "+name);
            int status=gzclose(zip); zip=nullptr; need(status==Z_OK,"gzip close "+name);
        } else { plain.read(reinterpret_cast<char*>(&c),1); need(plain.eof(),"trailing bytes "+name); }
    }
};

struct State { int rep=0; std::array<int,4> dest{},kind{}; };
std::array<State,N> states;
std::vector<int> pi(1<<(2*M),-1);

void automaton() {
    std::vector<int> words;
    std::array<uint64_t,11> counts{};
    std::set<Bond> used;
    std::function<void(Pt,int,int)> enumerate=[&](Pt x,int j,int code) {
        ++counts[j];
        if(j==M) { words.push_back(code); return; }
        for(int d=0;d<4;++d) {
            Pt y=add(x,d); Bond e=bond(x,y);
            if(used.contains(e)) continue;
            used.insert(e); enumerate(y,j+1,code*4+d); used.erase(e);
        }
    };
    enumerate({0,0},0,0);
    const std::array<uint64_t,11> expected{1,4,12,36,108,316,916,2628,7500,21268,60092};
    need(counts==expected,"raw enumeration counts");
    std::ifstream f(source/"windows_m10_min.txt");
    int nr,nq; need(bool(f>>nr>>nq) && nr==60092 && nq==N,"automaton header");
    for(int code:words) {
        int got,cl; need(bool(f>>got>>cl) && got==code && cl>=0 && cl<N,"raw map indexing");
        pi[code]=cl;
    }
    for(int q=0;q<N;++q) {
        State &s=states[q]; need(bool(f>>s.rep),"representative row");
        for(int &t:s.dest) need(bool(f>>t),"successor column");
        for(int &k:s.kind) need(bool(f>>k),"kind column");
        need(s.rep>=0 && s.rep<int(pi.size()) && pi[s.rep]==q,"representative surjection");
    }
    std::string extra; need(!(f>>extra) && f.eof(),"automaton trailing tokens");
    uint64_t rawdirections=0;
    for(int code:words) {
        std::array<int,M> dirs{}; int rest=code;
        for(int j=M-1;j>=0;--j) { dirs[j]=rest%4; rest/=4; }
        std::array<Pt,M+1> path{};
        used.clear();
        for(int j=0;j<M;++j) { path[j+1]=add(path[j],dirs[j]); used.insert(bond(path[j],path[j+1])); }
        bool revisit=std::find(path.begin(),path.begin()+M,path[M])!=path.begin()+M;
        const State &s=states[pi[code]];
        for(int d=0;d<4;++d) {
            ++rawdirections;
            bool admitted=d!=(dirs.back()+2)%4 && !used.contains(bond(path[M],add(path[M],d)));
            if(!admitted) { need(s.dest[d]==-1 && s.kind[d]==-1,"quotient inadmissibility"); continue; }
            int k=revisit ? 2 : (d==dirs.back() ? 0 : 1);
            int next=((code<<2)|d)&((1<<(2*M))-1);
            need(pi[next]>=0 && s.dest[d]==pi[next] && s.kind[d]==k,"quotient labelled successor/kind");
            if(k!=2) need((s.rep&3)==dirs.back(),"quotient incoming direction");
        }
    }
    std::array<uint64_t,3> edges{};
    for(const State &s:states) for(int d=0;d<4;++d) if(s.dest[d]>=0) {
        need(s.dest[d]<N && s.kind[d]>=0 && s.kind[d]<=2,"class edge range"); ++edges[s.kind[d]];
    }
    need(edges==std::array<uint64_t,3>{2516,5032,1872},"quotient edge counts");
    std::cout<<"AUTOMATON raw=60092 classes=3741 raw_direction_tests="<<rawdirections
             <<" edges="<<edges[0]<<","<<edges[1]<<","<<edges[2]<<" PASS\n";
}

Rat hp(int a,int b) { return (a+2)%4==b ? Rat(1) : hC; }
std::array<int,2> others(int incoming,int outgoing) {
    std::array<int,2> answer{}; int j=0;
    for(int d=0;d<4;++d) if(d!=(incoming+2)%4 && d!=outgoing) answer[j++]=d;
    need(j==2,"arrival/outgoing reversal"); return answer;
}
Rat reward(int incoming,int outgoing,bool deadf,bool deadg) {
    auto fg=others(incoming,outgoing); int t=incoming==outgoing ? 0 : 1;
    if(deadf && deadg) return Rat(0);
    if(deadf) return beta1[t]*hp(fg[1],outgoing);
    if(deadg) return beta1[t]*hp(fg[0],outgoing);
    return alpha[t]*hp(fg[0],fg[1])+beta[t]*(hp(fg[0],outgoing)+hp(fg[1],outgoing));
}
Rat diagonal(int phase,int kind) {
    if(kind==2) return Rat(1,5);
    if(phase==0) return (kind==0 ? xs : xt)/Rat(3);
    if(phase==1 || phase==2) return kind==0 ? xs/Rat(3) : Rat(1,3);
    return Rat(1,3);
}
bool changes(int p,int k) { return (p==0 && k==1) || (p==1 && k==0); }
int changed(int p) { return p==0 ? 2 : 3; }
struct Edge { int d,to,phase; Rat t; uint64_t p; };
std::array<std::array<std::vector<Edge>,N>,4> free_edges;
std::array<std::array<std::array<uint64_t,5>,4>,4> response_ceil{};
std::array<std::array<uint64_t,3>,4> diagonal_ceil{};

void coefficients() {
    Big lcm=1;
    auto accumulate=[&](const Rat &t) {
        Big den=t.denominator(); lcm=lcm/boost::integer::gcd(lcm,den)*den;
        need((Delta%den)==0,"prefix common denominator");
    };
    for(int p=0;p<4;++p) for(int k=0;k<3;++k) {
        diagonal_ceil[p][k]=ceiling(diagonal(p,k)); accumulate(diagonal(p,k));
    }
    for(int a=0;a<4;++a) for(int d=0;d<4;++d) if(d!=(a+2)%4) {
        auto fg=others(a,d); Rat x=a==d ? xs : xt;
        for(int delta=0;delta<5;++delta) {
            Rat t=x*reward(a,d,delta==fg[0],delta==fg[1])/Rat(3);
            response_ceil[a][d][delta]=ceiling(t); accumulate(t);
        }
        for(bool df:{false,true}) for(bool dg:{false,true}) accumulate(x*reward(a,d,df,dg)/Rat(3));
    }
    need(lcm==Delta,"Delta is the regenerated lcm");
    for(int p=0;p<4;++p) for(int q=0;q<N;++q) for(int d=0;d<4;++d) if(states[q].dest[d]>=0) {
        int k=states[q].kind[d], to=states[q].dest[d];
        Rat t=diagonal(p,k); free_edges[p][q].push_back({d,to,p,t,ceiling(t)});
        if(changes(p,k)) {
            Rat x=k==0 ? xs : xt;
            t=x*reward(states[q].rep&3,d,false,false)/Rat(3);
            free_edges[p][q].push_back({d,to,changed(p),t,ceiling(t)});
        }
    }
    std::cout<<"COEFFICIENTS Delta="<<Delta<<" diagonal_ceilings="
             <<diagonal_ceil[0][0]<<","<<diagonal_ceil[0][1]<<","
             <<diagonal_ceil[3][0]<<","<<diagonal_ceil[0][2]<<" PASS\n";
}

std::vector<uint32_t> z, ell;
size_t zi(int sigma,int p,int q) { return (size_t(sigma)*4+p)*N+q; }
size_t li(int axis,int p,int q,int k) { return (((size_t(axis)*4+p)*N+q)*141)+(k+R); }
Rat cap(int axis,int p,int q,int k) {
    return std::min(Rat(z[zi(2*axis,p,q)])*rpower(k),Rat(z[zi(2*axis+1,p,q)])*rpower(-k));
}
std::vector<uint32_t> capfloors, capceilings;
Wide eta=~Wide(0); uint32_t zmin=UINT32_MAX,zmax=0;

void tilted() {
    Input in(source/"axis_z_integer.bin"); z=in.words(16*N); in.end();
    unsigned maxsum=0; uint64_t rows=0, lower=0;
    for(int s=0;s<4;++s) for(int p=0;p<4;++p) for(int q=0;q<N;++q) {
        uint32_t value=z[zi(s,p,q)]; need(value>0,"tilted positivity");
        zmin=std::min(zmin,value); zmax=std::max(zmax,value);
        if(p>=2) { need(value>=V,"tilted terminal bound"); ++lower; }
        Wide sum=0;
        for(const Edge &e:free_edges[p][q]) {
            int displacement=(s<2 ? step[e.d].first : step[e.d].second)*(s%2 ? -1 : 1);
            uint64_t a=ceiling(e.t*rpower(displacement));
            sum+=Wide(a)*z[zi(s,e.phase,e.to)];
        }
        Wide rhs=Wide(D)*value; need(sum<rhs,"tilted strictly positive residual");
        eta=std::min(eta,rhs-sum); maxsum=std::max(maxsum,bits(sum)); ++rows;
    }
    need(zmax==83704870 && zmin==10486,"tilted extrema receipt");
    need(Big(zmax)*power(Big(12),71)<=Big(V)*power(Big(13),71),"exterior C/D <= 1");
    std::cout<<"TILTED rows="<<rows<<" values="<<z.size()<<" min="<<zmin<<" max="<<zmax
             <<" width="<<bits(zmax)<<" eta="<<strwide(eta)<<" eta_bits="<<bits(eta)
             <<" max_row_sum_bits="<<maxsum<<" terminal_lower_tests="<<lower<<" PASS\n";
    // Optional folded H2: all-phase residual is stronger than the needed A diagonal residual.
    need(eta*8000>=Wide(D)*zmax,"folded H2 contraction margin");
    need(uint64_t(zmax)<8000ULL*zmin,"folded H2 vector ratio");
    need(power(Big(1600000),10)<2*power(Big(1495813),10),"folded H2 C_V");
    std::cout<<"FOLDED_H2 q=7999/8000 CV=16000 PASS\n";
}

void lines() {
    Input in(source/"line_integer.bin");
    for(uint64_t v:std::array<uint64_t,5>{10,70,N,20,48}) need(in.qword()==v,"line header");
    ell=in.words(8*N*141); in.end();
    capfloors.resize(8*N*141); capceilings.resize(16*N);
    Input init(source/"line_init_integer.bin"), tails(source/"line_tails_integer.bin");
    auto supplied_floors=init.words(8*N*141), supplied_ceilings=tails.words(16*N); init.end(); tails.end();
    // Compute powers once, independently of the supplied tables.
    std::array<Rat,143> rp,rm;
    for(int k=-71;k<=71;++k) { rp[k+71]=rpower(k); rm[k+71]=rpower(-k); }
    uint64_t capchecks=0,center=0,off=0; uint32_t mx=0;
    for(int axis=0;axis<2;++axis) for(int p=0;p<4;++p) for(int q=0;q<N;++q) for(int k=-71;k<=71;++k) {
        Rat c=std::min(Rat(z[zi(2*axis,p,q)])*rp[k+71],Rat(z[zi(2*axis+1,p,q)])*rm[k+71]);
        if(k>=-70 && k<=70) {
            size_t at=li(axis,p,q,k); uint32_t c0=u64(floorq(c));
            capfloors[at]=c0; need(supplied_floors[at]==c0,"regenerated cap floor table");
            uint32_t v=ell[at]; mx=std::max(mx,v); need(v<=c0,"line below rational cap"); ++capchecks;
            if(p>=2) {
                if(k==0) { need(v==V,"line C/D coordinate-zero terminal"); ++center; }
                else { need(v<=V,"line off-zero C/D upper bound"); ++off; }
            }
        } else {
            size_t at=(((size_t(axis)*4+p)*N+q)*2)+(k>0);
            capceilings[at]=u64(ceilq(c)); need(supplied_ceilings[at]==capceilings[at],"regenerated outgoing cap ceilings");
        }
    }
    uint64_t rows=0,boundary=0; unsigned maxsum=0;
    for(int axis=0;axis<2;++axis) for(int p=0;p<4;++p) for(int q=0;q<N;++q) for(int k=-70;k<=70;++k) {
        if(p>=2 && k==0) continue;
        Wide sum=0;
        for(const Edge &e:free_edges[p][q]) {
            int next=k+(axis==0 ? step[e.d].first : step[e.d].second);
            uint32_t val=std::abs(next)<=70 ? ell[li(axis,e.phase,e.to,next)] :
                capceilings[(((size_t(axis)*4+e.phase)*N+e.to)*2)+(next>0)];
            sum+=Wide(e.p)*val;
        }
        need(sum<=Wide(D)*ell[li(axis,p,q,k)],"one-coordinate free row");
        maxsum=std::max(maxsum,bits(sum)); ++rows; if(std::abs(k)==70) ++boundary;
    }
    std::cout<<"LINES values="<<ell.size()<<" rows="<<rows<<" boundary_rows="<<boundary
             <<" cap_tests="<<capchecks<<" C_D_zero_tests="<<center<<" C_D_off_zero_tests="<<off
             <<" max="<<mx<<" width="<<bits(mx)<<" max_row_sum_bits="<<maxsum<<" PASS\n";
    uint32_t maxfloor=*std::max_element(capfloors.begin(),capfloors.end());
    uint32_t maxceil=*std::max_element(capceilings.begin(),capceilings.end());
    std::cout<<"DERIVED_CAP_TABLES floors="<<capfloors.size()<<" max_floor="<<maxfloor
             <<" floor_bits="<<bits(maxfloor)<<" ceilings="<<capceilings.size()
             <<" max_ceiling="<<maxceil<<" ceiling_bits="<<bits(maxceil)<<" PASS\n";
}

// Supplementary diagnostics; these are not extra hypotheses in H3-line.
void probes() {
    uint64_t failed_zero_rows=0; Rat worst(0); int worstaxis=-1,worstphase=-1,worstq=-1;
    for(int j=0;j<2;++j) for(int p=2;p<4;++p) for(int q=0;q<N;++q) {
        Rat row(0);
        for(const Edge &e:free_edges[p][q])
            row+=e.t*Rat(ell[li(j,e.phase,e.to,j==0 ? step[e.d].first : step[e.d].second)]);
        Rat ratio=row/Rat(V);
        if(ratio>Rat(1)) ++failed_zero_rows;
        if(ratio>worst) { worst=ratio; worstaxis=j; worstphase=p; worstq=q; }
    }
    std::cout<<"PROBE omitted_C_D_zero_rows="<<4*N<<" violating_free_row="<<failed_zero_rows
             <<" max_exact_ratio="<<fraction(worst)<<" at_axis="<<worstaxis+1
             <<" phase="<<worstphase<<" q="<<worstq<<"\n"<<std::flush;
    uint64_t rows=0;
    for(int j=0;j<2;++j) {
        std::map<int,std::vector<Rat>> cache;
        for(int k:{-101,-100,-99,-72,-71,71,72,99,100,101}) {
            Rat a=rpower(k),b=rpower(-k); auto &values=cache[k]; values.reserve(4*N);
            for(int p=0;p<4;++p) for(int q=0;q<N;++q)
                values.push_back(std::min(Rat(z[zi(2*j,p,q)])*a,Rat(z[zi(2*j+1,p,q)])*b));
        }
        auto value=[&](int p,int q,int k)->Rat {
            return std::abs(k)<=70 ? Rat(ell[li(j,p,q,k)]) : cache.at(k)[p*N+q];
        };
        for(int k:{-100,-71,71,100}) for(int p=0;p<4;++p) for(int q=0;q<N;++q) {
            Rat row(0);
            for(const Edge &e:free_edges[p][q])
                row+=e.t*value(e.phase,e.to,k+(j==0 ? step[e.d].first : step[e.d].second));
            need(row<=value(p,q,k),"direct rational tail/interface probe"); ++rows;
        }
    }
    std::cout<<"PROBE exact_tail_rows_at_-100_-71_71_100="<<rows<<" PASS\n"<<std::flush;
}

uint32_t outer(int p,int q,Pt x,Pt v) {
    int kx=x.first-v.first,ky=x.second-v.second;
    need(std::abs(kx)<=70 && std::abs(ky)<=70,"finite patch exterior within stored lines");
    return std::min(ell[li(0,p,q,kx)],ell[li(1,p,q,ky)]);
}
size_t ui(int p,int q,Pt x) { return ((size_t(p)*N+q)*1681)+(x.first+B)*41+x.second+B; }
bool inside(Pt x) { return std::abs(x.first)<=B && std::abs(x.second)<=B; }

struct Prefix {
    Pt target;
    int first;
    const std::vector<uint32_t> &u;
    std::set<Bond> used;
    std::map<Pt,int> departures;
    struct Item { Rat x,k; int index; };
    std::vector<Item> items;
    Big accumulator=0;
    Rat shortsum=Rat(0);
    uint64_t nodes=0,leaves=0,hits=0,mults=0;
    Prefix(Pt v,int d,const std::vector<uint32_t> &values):target(v),first(d),u(values) {}
    int count(Pt x) const { auto it=departures.find(x); return it==departures.end() ? 0 : it->second; }
    bool dead(Pt x) const { return x==Pt{0,0} || count(x)>=2; }
    Rat shortvalue(int n,int revisits) const {
        std::vector<Item> order=items;
        std::stable_sort(order.begin(),order.end(),[](const Item &a,const Item &b) {
            if(a.k==Rat(0) || b.k==Rat(0)) return a.k!=Rat(0) && b.k==Rat(0);
            Rat lhs=(a.x-Rat(1))*b.x*b.k, rhs=(b.x-Rat(1))*a.x*a.k;
            return lhs==rhs ? a.index<b.index : lhs<rhs;
        });
        Rat prod(1),sum(0);
        for(const auto &i:order) { prod*=i.x; sum+=prod*i.k; }
        return sum*ratpower(Rat(3,5),revisits)/Rat(power(Big(3),n));
    }
    void visit(Pt x,int n,int incoming,int code,const std::array<Big,4> &a,int revisits) {
        ++nodes;
        if(x==target) { ++hits; shortsum+=shortvalue(n,revisits); return; }
        if(n==L) {
            need(inside(x) && pi[code]>=0,"exact prefix endpoint lookup");
            ++leaves; for(int p=0;p<4;++p) accumulator+=a[p]*u[ui(p,pi[code],x)];
            return;
        }
        int prior=count(x);
        for(int d=0;d<4;++d) {
            if(n==0 && (d!=first || d==(incoming+2)%4)) continue;
            Pt y=add(x,d); Bond e=bond(x,y);
            if(y==Pt{0,0} || used.contains(e)) continue;
            need(d!=(incoming+2)%4,"noninitial reversal is a used bond");
            need(!dead(y),"true outgoing neighbour live");
            std::array<Big,4> b{};
            if(prior) {
                for(int p=0;p<4;++p) b[p]=a[p]*(Delta/5);
                mults+=4;
            } else {
                auto fg=others(incoming,d);
                Rat k=reward(incoming,d,dead(add(x,fg[0])),dead(add(x,fg[1])));
                Rat xx=d==incoming ? xs : xt;
                Big diagonalnum=u64(Delta*(xx/Rat(3)).numerator()/(xx/Rat(3)).denominator());
                Rat response=xx*k/Rat(3);
                need(Delta%response.denominator()==0,"true response denominator");
                Big c=Delta/response.denominator()*response.numerator();
                if(d==incoming) b={a[0]*diagonalnum,a[1]*diagonalnum,a[2]*diagonalnum,a[3]*(Delta/3)+a[1]*c};
                else b={a[0]*diagonalnum,a[1]*(Delta/3),a[2]*(Delta/3)+a[0]*c,a[3]*(Delta/3)};
                items.push_back({xx,k,n}); mults+=5;
            }
            departures[x]=prior+1; used.insert(e);
            visit(y,n+1,d,((code<<2)|d)&((1<<(2*M))-1),b,revisits+(prior>0));
            used.erase(e); if(prior) departures[x]=prior; else departures.erase(x);
            if(!prior) items.pop_back();
        }
    }
};

Rat patch(char X,int d0,uint64_t ceiling9,const std::array<uint64_t,3> &expected) {
    Pt v=X=='B' ? Pt{1,0} : Pt{0,1};
    std::string name="line_"+std::string(1,X)+"_m10_R20_d"+std::to_string(d0)+"_integer.bin.gz";
    Input in(source/name,true);
    std::array<int64_t,9> header{10,12,20,N,1681,v.first,v.second,20,d0};
    for(int64_t h:header) need(in.qword()==uint64_t(h),"patch header "+name);
    auto zero=in.words(4*N);
    for(int p=0;p<4;++p) for(int q=0;q<N;++q)
        need(zero[p*N+q]==ell[li(0,p,q,0)],"patch redundant line-zero metadata");
    auto u=in.words(4*N*1681); in.end();
    auto next=[&](int p,int q,Pt x)->uint32_t { return inside(x) ? u[ui(p,q,x)] : outer(p,q,x,v); };
    uint64_t rows=0,caps=0,terminals=0,boundary=0,outgoing=0,knownrows=0;
    unsigned maxsum=0; uint32_t mx=0; Wide minimum=~Wide(0);
    for(int p=0;p<4;++p) for(int q=0;q<N;++q) for(int xx=-B;xx<=B;++xx) for(int yy=-B;yy<=B;++yy) {
        Pt x{xx,yy}; uint32_t val=u[ui(p,q,x)]; mx=std::max(mx,val);
        need(val<=outer(p,q,x,v),"patch below F_infinity "+name); ++caps;
        if(x==Pt{0,0} || x==v) {
            uint32_t wanted=(x==v && p>=2) ? V : 0;
            need(val==wanted,"patch terminal value "+name); ++terminals; continue;
        }
        bool known=x==Pt{-1,0} || x==add({-1,0},d0);
        Wide sum=0;
        for(int d=0;d<4;++d) {
            int to=states[q].dest[d],k=states[q].kind[d]; if(to<0) continue;
            if(known && (k==2 || (x==Pt{-1,0} && d==d0) || (x==add({-1,0},d0) && d==(d0+2)%4))) continue;
            Pt y=add(x,d); if(y==Pt{0,0}) continue;
            sum+=Wide(known ? diagonal_ceil[0][2] : diagonal_ceil[p][k])*next(p,to,y);
            if(!inside(y)) ++outgoing;
            if(!known && changes(p,k)) {
                int delta=4;
                for(int j=0;j<4;++j) if(add(x,j)==Pt{0,0}) delta=j;
                sum+=Wide(response_ceil[states[q].rep&3][d][delta])*next(changed(p),to,y);
            }
        }
        Wide rhs=Wide(D)*val; need(sum<=rhs,"stationary patch row "+name);
        minimum=std::min(minimum,rhs-sum); maxsum=std::max(maxsum,bits(sum));
        ++rows; if(std::abs(xx)==B || std::abs(yy)==B) ++boundary; if(known) ++knownrows;
    }
    need(rows==25124556 && caps==25154484 && terminals==29928,"patch counts");
    std::cout<<"PATCH "<<X<<"/"<<d0<<" values="<<u.size()<<" rows="<<rows<<" boundary_rows="<<boundary
             <<" exterior_direction_terms="<<outgoing<<" known_rows="<<knownrows
             <<" caps="<<caps<<" terminal_values="<<terminals<<" max="<<mx<<" width="<<bits(mx)
             <<" max_row_sum_bits="<<maxsum<<" min_residual="<<strwide(minimum)<<" PASS\n"<<std::flush;
    Prefix pre{v,d0,u};
    pre.visit({-1,0},0,2,0,{Big(1),Big(1),Big(0),Big(0)},0);
    need(std::array<uint64_t,3>{pre.nodes,pre.leaves,pre.hits}==expected,"prefix enumeration receipt");
    Big tailden=power(Delta,12)*V;
    Rat J=pre.shortsum+Rat(pre.accumulator,tailden);
    Big left=Big(1000000000)*(pre.shortsum.numerator()*tailden+pre.accumulator*pre.shortsum.denominator());
    Big right=Big(ceiling9)*pre.shortsum.denominator()*tailden;
    need(left<=right,"cleared rational prefix bound");
    std::cout<<"PREFIX "<<X<<"/"<<d0<<" nodes="<<pre.nodes<<" leaves="<<pre.leaves<<" hits="<<pre.hits
             <<" phase_multiplications="<<pre.mults<<" accumulator_bits="<<bits(pre.accumulator)
             <<" ceiling_1e9="<<ceiling9<<"\n  short="<<fraction(pre.shortsum)
             <<"\n  tail_numerator="<<pre.accumulator<<"\n  J="<<fraction(J)<<" PASS\n"<<std::flush;
    return J;
}

void closing(const Rat &q,uint64_t cv,const std::string &label) {
    Rat H(6,5),C(22899,25000),rho0(967725,1000000),rho(78709,80000);
    Rat b=(Rat(1)+q)/Rat(2),r=q/b;
    Rat bound=Rat(2)*H*C*Rat(cv)/b/b*r/ratpower(Rat(1)-r,3);
    need(bound==Rat(16)*H*C*Rat(cv)*q/ratpower(Rat(1)-q,3),"B_* simplification");
    Rat eps=std::min((Rat(1)-b)/Rat(2),(Rat(1)-rho0)/(Rat(2)*bound));
    Rat theta=Rat(1)-eps;
    Rat CT=Rat(2)*ratpower(Rat(12,5),24)*ratpower(Rat(cv)/(Rat(1)-q),2);
    Rat A=H*std::max(Rat(2),CT)/(Rat(1)-rho);
    need(CT>Rat(2) && eps==(Rat(1)-rho0)/(Rat(2)*bound),"closing chosen minimum and CT");
    need(Rat(0)<q*q && q*q<q && q<b && b<theta && theta<Rat(1),"closing theta inequalities");
    need(rho0<rho && rho<Rat(1) && eps*bound<=(Rat(1)-rho0)/Rat(2),"closing witness inequalities");
    std::cout<<"CLOSING "<<label<<" q="<<fraction(q)<<" CV="<<cv
             <<"\n  B_star="<<fraction(bound)<<"\n  epsilon="<<fraction(eps)<<"\n  CT="<<fraction(CT)
             <<"\n  A="<<fraction(A)<<"\n  rho="<<fraction(rho)<<" PASS\n";
}

int main(int argc,char **argv) {
    try {
        source=argc>1 ? argv[1] : "../MATH_FIT/data";
        automaton(); coefficients(); tilted(); lines(); probes();
        std::array<Rat,5> J;
        J[0]=patch('B',1,343236463,{139985,89150,937});
        J[1]=patch('B',2,281251920,{161929,103257,922});
        J[2]=patch('C',1,522717990,{105025,66947,715});
        J[3]=patch('C',2,372660908,{155673,99168,1036});
        J[4]=patch('C',3,264538742,{145485,92748,861});
        Rat rho0(967725,1000000);
        need(Rat(2)*J[0]+J[1]<=rho0 && J[2]+J[3]+J[4]<=rho0*hC,"assembled true-kernel bounds");
        std::cout<<"ASSEMBLY B="<<fraction(Rat(2)*J[0]+J[1])<<"\n  C/hC="
                 <<fraction((J[2]+J[3]+J[4])/hC)<<" PASS\n";
        closing(Rat(Big("1119948287353"),Big("1120437614225")),10,"retained_H2");
        closing(Rat(7999,8000),16000,"folded_H2");
        std::cout<<"ALL H3-LINE CHECKS PASSED\n";
    } catch(const std::exception &e) { std::cerr<<"FAIL: "<<e.what()<<"\n"; return 1; }
}
