// relaxed_walk.cpp (claude, 2026-09-17)
// Metropolis walk on Z_n-symmetric quadrangulations of the sphere whose vertices carry n-bit labels (the regions of an
// arrangement of n Jordan curves with only double crossings), with DUPLICATE labels allowed. Every face is a cube square
// (labels u, u^a, u^a^b, u^b in cyclic order). Moves: lens insertion (RII), lens removal (inverse RII), triangle flip
// (RIII); each is applied to all n rotation images at once and rejected if the images' dart footprints overlap.
// Energy E = sum over labels |mult(L) - 1| = (missing labels) + (duplicate regions). E = 0 <=> all 2^n labels once.
// The moves never change the number of components of any curve, so a state reached from a valid start with E = 0 is a
// simple symmetric n-Venn diagram; verifyVenn() re-checks that natively (labels, Euler, symmetry, one cycle per curve)
// before anything is exported as a diagram.
// CLI: ./relaxed_walk n seconds seed out_prefix T0 T1 [load] [--strict] [pT pR] [reportEvery] [exportEvery]
//   load: '-' for the interval sphere, a v13-style export (faces of label strings) or a raw state (*.raw) from this program.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <string>
#include <vector>
#include <array>
#include <unordered_map>
#include <random>
#include <chrono>
#include <algorithm>
using namespace std;
typedef uint32_t U;
static int n; static U FULL;
// ---------------- write journal (exact undo of any move sequence while active) ----------------
struct JE{ int kind; void* p; size_t i; uint64_t old; };
static std::vector<JE> J_; static bool jon_=false;
template<class T> struct TC;
template<> struct TC<int>{ static const int code=1; }; template<> struct TC<U>{ static const int code=2; };
template<> struct TC<uint16_t>{ static const int code=3; }; template<> struct TC<uint8_t>{ static const int code=4; }; template<> struct TC<char>{ static const int code=5; };
template<class T> static inline void jset(std::vector<T>& a, size_t i, T v){ if(jon_) J_.push_back({TC<T>::code,&a,i,(uint64_t)a[i]}); a[i]=v; }
template<class T> static inline void jpush(std::vector<T>& a, T v){ if(jon_) J_.push_back({10+TC<T>::code,&a,0,0}); a.push_back(v); }
template<class T> static inline void jpop(std::vector<T>& a){ if(jon_) J_.push_back({20+TC<T>::code,&a,0,(uint64_t)a.back()}); a.pop_back(); }
static inline void jsetl(long& x, long v){ if(jon_) J_.push_back({30,&x,0,(uint64_t)x}); x=v; }
template<class T> static void jundo1(const JE& e){ auto* a=(std::vector<T>*)e.p; int k=e.kind%10; (void)k; if(e.kind<10) (*a)[e.i]=(T)e.old; else if(e.kind<20) a->pop_back(); else a->push_back((T)e.old); }
static void jundoTo(size_t mark){ while(J_.size()>mark){ const JE e=J_.back(); J_.pop_back(); if(e.kind==30){ *(long*)e.p=(long)e.old; continue; }
    switch(e.kind%10){ case 1: jundo1<int>(e); break; case 2: jundo1<U>(e); break; case 3: jundo1<uint16_t>(e); break; case 4: jundo1<uint8_t>(e); break; case 5: jundo1<char>(e); break; default: abort(); } } }

// darts
static vector<int> twin_, nxt_, prv_, orig_, rotd_, dpos_, live_, freeD_; static vector<uint8_t> axis_; static vector<char> dalive_;
// vertices
static vector<U> label_; static vector<int> adart_, deg_, rotv_, freeV_; static vector<char> valive_;
static vector<uint16_t> mult_; static long E_=0, missing_=0, dups_=0, nV_=0, nEdges_=0;
static bool strictMode=false; static bool checkEvery=false; static double lambda_=1.0; static double tHot_=-1;
static std::vector<std::vector<int>> byLabel; static std::vector<int> posInLabel;      // live regions per label
static std::vector<U> missingList, dupList; static std::vector<int> missingPos, dupPos; // labels with mult 0 / mult >= 2

static bool verifyStructure(std::string& why); static void saveRaw(const std::string& path);
static inline U rot1(U m){ return (m>>1)|((m&1u)<<(n-1)); }
static inline bool isPole(U L){ return L==0||L==FULL; }
static inline void listAdd(std::vector<U>& L, std::vector<int>& P, U x); static inline void listDel(std::vector<U>& L, std::vector<int>& P, U x);
static int newDart(){ int d; if(!freeD_.empty()){ d=freeD_.back(); jpop(freeD_); } else { d=(int)twin_.size(); jpush(twin_,-1); jpush(nxt_,-1); jpush(prv_,-1); jpush(orig_,-1); jpush(rotd_,-1); jpush(dpos_,-1); jpush(axis_,(uint8_t)0); jpush(dalive_,(char)0); }
  jset(dalive_,(size_t)d,(char)1); jset(dpos_,(size_t)d,(int)live_.size()); jpush(live_,d); return d; }
static void freeDart(int d){ jset(dalive_,(size_t)d,(char)0); int p=dpos_[d], last=live_.back(); jset(live_,(size_t)p,last); jset(dpos_,(size_t)last,p); jpop(live_); jset(dpos_,(size_t)d,-1); jpush(freeD_,d); }
static int newVertex(U L){ int v; if(!freeV_.empty()){ v=freeV_.back(); jpop(freeV_); } else { v=(int)label_.size(); jpush(label_,(U)0); jpush(adart_,-1); jpush(deg_,0); jpush(rotv_,-1); jpush(valive_,(char)0); jpush(posInLabel,-1); }
  jset(valive_,(size_t)v,(char)1); jset(label_,(size_t)v,L); jset(deg_,(size_t)v,0); jset(adart_,(size_t)v,-1); jsetl(nV_,nV_+1); int m=mult_[L];
  if(m==0){ jsetl(missing_,missing_-1); jsetl(E_,E_-1); listDel(missingList,missingPos,L); } else { jsetl(dups_,dups_+1); jsetl(E_,E_+1); if(m==1) listAdd(dupList,dupPos,L); } jset(mult_,(size_t)L,(uint16_t)(m+1));
  jset(posInLabel,(size_t)v,(int)byLabel[L].size()); jpush(byLabel[L],v); return v; }
static void freeVertex(int v){ jset(valive_,(size_t)v,(char)0); jsetl(nV_,nV_-1); U L=label_[v]; int m=mult_[L]-1; jset(mult_,(size_t)L,(uint16_t)m);
  if(m==0){ jsetl(missing_,missing_+1); jsetl(E_,E_+1); listAdd(missingList,missingPos,L); } else { jsetl(dups_,dups_-1); jsetl(E_,E_-1); if(m==1) listDel(dupList,dupPos,L); } jpush(freeV_,v);
  { auto& R=byLabel[L]; int p=posInLabel[v]; int last=R.back(); jset(R,(size_t)p,last); jset(posInLabel,(size_t)last,p); jpop(R); jset(posInLabel,(size_t)v,-1); } }
static inline void listAdd(std::vector<U>& L, std::vector<int>& P, U x){ jset(P,(size_t)x,(int)L.size()); jpush(L,x); }
static inline void listDel(std::vector<U>& L, std::vector<int>& P, U x){ int p=P[x]; U last=L.back(); jset(L,(size_t)p,last); jset(P,(size_t)last,p); jpop(L); jset(P,(size_t)x,-1); }
static inline void link(int a,int b){ jset(nxt_,(size_t)a,b); jset(prv_,(size_t)b,a); }
static int mkEdge(int p,int q,int ax){ int d=newDart(), e=newDart(); jset(twin_,(size_t)d,e); jset(twin_,(size_t)e,d); jset(orig_,(size_t)d,p); jset(orig_,(size_t)e,q); jset(axis_,(size_t)d,(uint8_t)ax); jset(axis_,(size_t)e,(uint8_t)ax); jset(deg_,(size_t)p,deg_[p]+1); jset(deg_,(size_t)q,deg_[q]+1); jsetl(nEdges_,nEdges_+1); return d; }
static void rmEdge(int d){ int e=twin_[d]; jset(deg_,(size_t)orig_[d],deg_[orig_[d]]-1); jset(deg_,(size_t)orig_[e],deg_[orig_[e]]-1); jsetl(nEdges_,nEdges_-1); freeDart(d); freeDart(e); }
static inline bool onebit(U x){ return x && !(x&(x-1)); }

// ---------------- sites ----------------
struct RIIsite{ int d1,d2,d3,d4,e1,e2,e3,e4,u,ua,ub,uc,uab,uac,a,b,c; U lx,ly; };
static bool checkRII(int d1, RIIsite& s){
  if(d1<0||!dalive_[d1]) return false; int e1=twin_[d1]; int d2=nxt_[d1], d3=nxt_[d2], d4=nxt_[d3]; if(nxt_[d4]!=d1) return false;
  int e2=nxt_[e1], e3=nxt_[e2], e4=nxt_[e3]; if(nxt_[e4]!=e1) return false; if(d2==e1||d3==e1||d4==e1) return false;
  int a=axis_[d1], b=axis_[d2], c=axis_[e2]; if(b==c||a==b||a==c) return false;
  s.d1=d1; s.d2=d2; s.d3=d3; s.d4=d4; s.e1=e1; s.e2=e2; s.e3=e3; s.e4=e4; s.a=a; s.b=b; s.c=c;
  s.u=orig_[d1]; s.ua=orig_[e1]; s.ub=orig_[d4]; s.uc=orig_[e3]; s.uab=orig_[d3]; s.uac=orig_[e4];
  U Lu=label_[s.u]; if(label_[s.ua]!=(Lu^(1u<<a))||label_[s.ub]!=(Lu^(1u<<b))||label_[s.uc]!=(Lu^(1u<<c))||label_[s.uab]!=(Lu^(1u<<a)^(1u<<b))||label_[s.uac]!=(Lu^(1u<<a)^(1u<<c))) return false;
  s.lx=Lu^(1u<<b)^(1u<<c); s.ly=s.lx^(1u<<a); return true; }
static void applyRII(const RIIsite& s,int* nv,int* nd){
  int x=newVertex(s.lx), y=newVertex(s.ly); rmEdge(s.d1);
  int g1=mkEdge(s.uc,x,s.b), g1p=twin_[g1], g2=mkEdge(x,s.ub,s.c), g2p=twin_[g2], g3=mkEdge(s.uab,y,s.c), g3p=twin_[g3], g4=mkEdge(y,s.uac,s.b), g4p=twin_[g4], g5=mkEdge(y,x,s.a), g5p=twin_[g5];
  link(s.e2,g1); link(g1,g2); link(g2,s.d4); link(s.d4,s.e2);
  link(s.d2,g3); link(g3,g4); link(g4,s.e4); link(s.e4,s.d2);
  link(s.e3,g4p); link(g4p,g5); link(g5,g1p); link(g1p,s.e3);
  link(g2p,g5p); link(g5p,g3p); link(g3p,s.d3); link(s.d3,g2p);
  jset(adart_,(size_t)s.u,s.e2); jset(adart_,(size_t)s.ua,s.d2); jset(adart_,(size_t)x,g2); jset(adart_,(size_t)y,g4);
  nv[0]=x; nv[1]=y; int arr[10]={g1,g1p,g2,g2p,g3,g3p,g4,g4p,g5,g5p}; memcpy(nd,arr,sizeof arr); }
static void fpRII(const RIIsite& s,int* f){ int arr[8]={s.d1,s.d2,s.d3,s.d4,s.e1,s.e2,s.e3,s.e4}; memcpy(f,arr,sizeof arr); }

struct RIIIsite{ int f1,f2,f3,b1,b2,b3,h1,h2,h3,h4,h5,h6,v,t1,t2,t3,X12,X23,X31,a,b,c; U lv,lw; };
static bool checkRIII(int f1, RIIIsite& s){   // site = a dart f1 out of v (dart-based so that rotation images are consistent)
  if(f1<0||!dalive_[f1]) return false; int v=orig_[f1]; if(deg_[v]!=3) return false;
  int b1=prv_[f1], f2=twin_[b1], b2=prv_[f2], f3=twin_[b2], b3=prv_[f3]; if(twin_[b3]!=f1) return false; if(orig_[f2]!=v||orig_[f3]!=v) return false;
  int h1=nxt_[f1], h2=nxt_[h1]; if(nxt_[h2]!=b1) return false; int h3=nxt_[f2], h4=nxt_[h3]; if(nxt_[h4]!=b2) return false; int h5=nxt_[f3], h6=nxt_[h5]; if(nxt_[h6]!=b3) return false;
  int a=axis_[f1], b=axis_[f2], c=axis_[f3]; if(a==b||b==c||a==c) return false;
  s.f1=f1;s.f2=f2;s.f3=f3;s.b1=b1;s.b2=b2;s.b3=b3;s.h1=h1;s.h2=h2;s.h3=h3;s.h4=h4;s.h5=h5;s.h6=h6;s.v=v;s.a=a;s.b=b;s.c=c;
  s.t1=orig_[h1]; s.X12=orig_[h2]; s.t2=orig_[h3]; s.X23=orig_[h4]; s.t3=orig_[h5]; s.X31=orig_[h6];
  if(orig_[b1]!=s.t2||orig_[b2]!=s.t3||orig_[b3]!=s.t1) return false;
  U L=label_[v]; s.lv=L; if(label_[s.t1]!=(L^(1u<<a))||label_[s.t2]!=(L^(1u<<b))||label_[s.t3]!=(L^(1u<<c))||label_[s.X12]!=(L^(1u<<a)^(1u<<b))||label_[s.X23]!=(L^(1u<<b)^(1u<<c))||label_[s.X31]!=(L^(1u<<c)^(1u<<a))) return false;
  s.lw=L^(1u<<a)^(1u<<b)^(1u<<c); return true; }
static void applyRIII(const RIIIsite& s,int* nv,int* nd){
  int w=newVertex(s.lw); rmEdge(s.f1); rmEdge(s.f2); rmEdge(s.f3); freeVertex(s.v);
  int k1=mkEdge(w,s.X12,s.c), k1p=twin_[k1], k2=mkEdge(w,s.X23,s.a), k2p=twin_[k2], k3=mkEdge(w,s.X31,s.b), k3p=twin_[k3];
  link(k1,s.h2); link(s.h2,s.h3); link(s.h3,k2p); link(k2p,k1);
  link(k2,s.h4); link(s.h4,s.h5); link(s.h5,k3p); link(k3p,k2);
  link(k3,s.h6); link(s.h6,s.h1); link(s.h1,k1p); link(k1p,k3);
  jset(adart_,(size_t)w,k1); jset(adart_,(size_t)s.t1,s.h1); jset(adart_,(size_t)s.t2,s.h3); jset(adart_,(size_t)s.t3,s.h5); jset(adart_,(size_t)s.X12,s.h2); jset(adart_,(size_t)s.X23,s.h4); jset(adart_,(size_t)s.X31,s.h6);
  nv[0]=w; int arr[6]={k1,k1p,k2,k2p,k3,k3p}; memcpy(nd,arr,sizeof arr); }
static void fpRIII(const RIIIsite& s,int* f){ int arr[12]={s.f1,s.f2,s.f3,s.b1,s.b2,s.b3,s.h1,s.h2,s.h3,s.h4,s.h5,s.h6}; memcpy(f,arr,sizeof arr); }

struct InvSite{ int s0,sp,g1,g1p,g2,g2p,g3,g3p,g4,g4p,d2,d3,d4,e2,e3,e4,x,y,u,ua,ub,uc,uab,uac,a; U lx,ly; };
static bool checkInv(int s0, InvSite& s){
  if(s0<0||!dalive_[s0]) return false; int x=orig_[s0], sp=twin_[s0], y=orig_[sp]; if(deg_[x]!=3||deg_[y]!=3) return false;
  int g3p=nxt_[s0], d3=nxt_[g3p], g2p=nxt_[d3]; if(nxt_[g2p]!=s0) return false;
  int g1p=nxt_[sp], e3=nxt_[g1p], g4p=nxt_[e3]; if(nxt_[g4p]!=sp) return false;
  int g2=twin_[g2p], g1=twin_[g1p], g3=twin_[g3p], g4=twin_[g4p];
  if(orig_[g2]!=x||orig_[g1p]!=x||orig_[g4]!=y||orig_[g3p]!=y) return false;
  int d4=nxt_[g2], e2=nxt_[d4]; if(nxt_[e2]!=g1||nxt_[g1]!=g2) return false;
  int e4=nxt_[g4], d2=nxt_[e4]; if(nxt_[d2]!=g3||nxt_[g3]!=g4) return false;
  int all[16]={s0,sp,g1,g1p,g2,g2p,g3,g3p,g4,g4p,d2,d3,d4,e2,e3,e4}; for(int i=0;i<16;i++) for(int j=i+1;j<16;j++) if(all[i]==all[j]) return false;
  int u=orig_[e2], ua=orig_[d2], ub=orig_[d4], uc=orig_[g1], uab=orig_[d3], uac=orig_[e4];
  int a=axis_[s0]; U Lu=label_[u]; if(label_[ua]!=(Lu^(1u<<a))) return false; U bb=label_[ub]^Lu, cc=label_[uc]^Lu; if(!onebit(bb)||!onebit(cc)||bb==cc||bb==(1u<<a)||cc==(1u<<a)) return false;
  if(label_[uab]!=(Lu^(1u<<a)^bb)||label_[uac]!=(Lu^(1u<<a)^cc)||label_[x]!=(Lu^bb^cc)||label_[y]!=(Lu^bb^cc^(1u<<a))) return false;
  s.s0=s0;s.sp=sp;s.g1=g1;s.g1p=g1p;s.g2=g2;s.g2p=g2p;s.g3=g3;s.g3p=g3p;s.g4=g4;s.g4p=g4p;s.d2=d2;s.d3=d3;s.d4=d4;s.e2=e2;s.e3=e3;s.e4=e4;s.x=x;s.y=y;s.u=u;s.ua=ua;s.ub=ub;s.uc=uc;s.uab=uab;s.uac=uac;s.a=a;s.lx=label_[x];s.ly=label_[y]; return true; }
static void applyInv(const InvSite& s,int* nv,int* nd){
  rmEdge(s.s0); rmEdge(s.g1); rmEdge(s.g2); rmEdge(s.g3); rmEdge(s.g4); freeVertex(s.x); freeVertex(s.y);
  int d1=mkEdge(s.u,s.ua,s.a), e1=twin_[d1];
  link(d1,s.d2); link(s.d2,s.d3); link(s.d3,s.d4); link(s.d4,d1);
  link(e1,s.e2); link(s.e2,s.e3); link(s.e3,s.e4); link(s.e4,e1);
  jset(adart_,(size_t)s.u,s.e2); jset(adart_,(size_t)s.ua,s.d2); jset(adart_,(size_t)s.ub,s.d4); jset(adart_,(size_t)s.uc,s.e3); jset(adart_,(size_t)s.uab,s.d3); jset(adart_,(size_t)s.uac,s.e4);
  (void)nv; nd[0]=d1; nd[1]=e1; }
static void fpInv(const InvSite& s,int* f){ int arr[16]={s.s0,s.sp,s.g1,s.g1p,s.g2,s.g2p,s.g3,s.g3p,s.g4,s.g4p,s.d2,s.d3,s.d4,s.e2,s.e3,s.e4}; memcpy(f,arr,sizeof arr); }


// ---------------- bigon removal / insertion (genuine Reidemeister II on a degree-2 region) ----------------
// removal at dart e1 = L->A where deg L == 2: faces [e1:L->A, f1:A->M1, f2:M1->B, f3:B->L] and [e2:L->B, g1:B->M2, g2:M2->A, g3:A->L],
// label M1 == label M2 == L^a^b, M1 != M2 as objects. Result: L deleted, M1 and M2 merged into M, edges M-A (twin f1 <-> twin g2)
// and M-B (twin f2 <-> twin g1). dE = (L: -1 if dup else +1) + (-1 for the merged duplicate) in {-2, 0}.
static inline int sigma(int d){ return twin_[prv_[d]]; }   // next out-dart around orig(d)
struct BigSite{ int e1,e2,f1,f2,f3,g1,g2,g3,tf1,tf2,tg1,tg2,L,A,B,M1,M2,a,b; U lL,lM; vector<int> m2darts; };
static long bigFail[16]={0}; static bool checkBigI(int e1, BigSite& s, int& why);
static bool checkBig(int e1, BigSite& s){ int why=0; bool ok=checkBigI(e1,s,why); if(!ok) bigFail[why]++; return ok; }
static bool checkBigI(int e1, BigSite& s, int& why){
  if(e1<0||!dalive_[e1]) { why=1; return false; } int L=orig_[e1]; if(deg_[L]!=2) { why=2; return false; } int e2=sigma(e1); if(e2==e1||orig_[e2]!=L) { why=3; return false; } if(sigma(e2)!=e1) { why=4; return false; }
  int f1=nxt_[e1], f2=nxt_[f1], f3=nxt_[f2]; if(nxt_[f3]!=e1||f3!=twin_[e2]) { why=5; return false; }
  int g1=nxt_[e2], g2=nxt_[g1], g3=nxt_[g2]; if(nxt_[g3]!=e2||g3!=twin_[e1]) { why=6; return false; }
  int A=orig_[f1], M1=orig_[f2], B=orig_[g1], M2=orig_[g2]; if(A==B||M1==M2||M1==L||M2==L||M1==A||M1==B||M2==A||M2==B) { why=7; return false; }
  int a=axis_[e1], b=axis_[e2]; if(a==b) { why=8; return false; } U lL=label_[L]; if(label_[A]!=(lL^(1u<<a))||label_[B]!=(lL^(1u<<b))||label_[M1]!=(lL^(1u<<a)^(1u<<b))||label_[M2]!=label_[M1]) { why=9; return false; }
  if(isPole(label_[M1])) { why=10; return false; }
  s.e1=e1;s.e2=e2;s.f1=f1;s.f2=f2;s.f3=f3;s.g1=g1;s.g2=g2;s.g3=g3;s.tf1=twin_[f1];s.tf2=twin_[f2];s.tg1=twin_[g1];s.tg2=twin_[g2];s.L=L;s.A=A;s.B=B;s.M1=M1;s.M2=M2;s.a=a;s.b=b;s.lL=lL;s.lM=label_[M1];
  s.m2darts.clear(); int d=g2, k=0; do{ s.m2darts.push_back(d); d=sigma(d); k++; } while(d!=g2 && k<=deg_[M2]); if(d!=g2||k!=deg_[M2]) { why=11; return false; }
  return true; }
static void applyBig(const BigSite& s,int* nv,int* nd){
  // re-originate M2's surviving out-darts to M1
  for(int d:s.m2darts) if(d!=s.g2) jset(orig_,(size_t)d,s.M1);
  // retwin: M-A = tf1 <-> tg2 ; M-B = tf2 <-> tg1
  jset(twin_,(size_t)s.tf1,s.tg2); jset(twin_,(size_t)s.tg2,s.tf1); jset(twin_,(size_t)s.tf2,s.tg1); jset(twin_,(size_t)s.tg1,s.tf2);
  // degrees and counts
  jset(deg_,(size_t)s.M1,deg_[s.M1]+deg_[s.M2]-2); jset(deg_,(size_t)s.A,deg_[s.A]-2); jset(deg_,(size_t)s.B,deg_[s.B]-2); jsetl(nEdges_,nEdges_-4);
  jset(adart_,(size_t)s.M1,s.tf1); jset(adart_,(size_t)s.A,s.tg2); jset(adart_,(size_t)s.B,s.tf2);
  int del[8]={s.e1,s.e2,s.f1,s.f2,s.f3,s.g1,s.g2,s.g3}; for(int i=0;i<8;i++) freeDart(del[i]);
  freeVertex(s.L); freeVertex(s.M2); (void)nv; (void)nd; }
static void fpBig(const BigSite& s, vector<int>& f){ f.assign({s.e1,s.e2,s.f1,s.f2,s.f3,s.g1,s.g2,s.g3,s.tf1,s.tf2,s.tg1,s.tg2}); for(int d:s.m2darts) f.push_back(d); int d=s.tf1,k=0; do{ f.push_back(d); d=sigma(d); k++; } while(d!=s.tf1 && k<=deg_[s.M1]); }
// insertion at out-dart mA = M->A (axis b) with mB = the k-th sigma-successor of mA (M->B, axis a != b):
// M1 keeps mA and the darts from mA up to before mB; M2 gets mB and the rest; new L = M^a^b. dE = (L: -1 if missing else +1) + 1.
struct InsSite{ int mA,mB,tmA,tmB,M,A,B,a,b; U lL,lM; vector<int> grp2; };
static int insK_=1;
static bool checkIns(int mA, InsSite& s){
  if(mA<0||!dalive_[mA]) return false; int M=orig_[mA]; if(deg_[M]<2) return false; if(isPole(label_[M])) return false;
  int mB=mA; for(int i=0;i<insK_;i++) mB=sigma(mB); if(mB==mA) return false; int b=axis_[mA], a=axis_[mB]; if(a==b) return false;
  int A=orig_[twin_[mA]], B=orig_[twin_[mB]]; if(A==B||A==M||B==M) return false;
  s.mA=mA;s.mB=mB;s.tmA=twin_[mA];s.tmB=twin_[mB];s.M=M;s.A=A;s.B=B;s.a=a;s.b=b;s.lM=label_[M];s.lL=s.lM^(1u<<a)^(1u<<b);
  s.grp2.clear(); int d=mB, k=0; do{ s.grp2.push_back(d); d=sigma(d); k++; } while(d!=mA && k<=deg_[M]); if(d!=mA) return false;
  return true; }
static void applyIns(const InsSite& s,int* nv,int* nd){
  int L=newVertex(s.lL), M2=newVertex(s.lM); int M1=s.M;
  for(int d:s.grp2) jset(orig_,(size_t)d,M2);
  int e1=newDart(), g3=newDart(), e2=newDart(), f3=newDart(), f1=newDart(), f2=newDart(), g1=newDart(), g2=newDart();
  auto setd=[&](int d,int o,int ax){ jset(orig_,(size_t)d,o); jset(axis_,(size_t)d,(uint8_t)ax); };
  setd(e1,L,s.a); setd(g3,s.A,s.a); setd(e2,L,s.b); setd(f3,s.B,s.b); setd(f1,s.A,s.b); setd(f2,M1,s.a); setd(g1,s.B,s.a); setd(g2,M2,s.b);
  auto tw=[&](int x,int y){ jset(twin_,(size_t)x,y); jset(twin_,(size_t)y,x); };
  tw(e1,g3); tw(e2,f3); tw(f1,s.mA); tw(f2,s.tmB); tw(g1,s.mB); tw(g2,s.tmA);
  link(e1,f1); link(f1,f2); link(f2,f3); link(f3,e1);
  link(e2,g1); link(g1,g2); link(g2,g3); link(g3,e2);
  int g2n=(int)s.grp2.size(); jset(deg_,(size_t)M1,deg_[M1]-g2n+1); jset(deg_,(size_t)M2,g2n+1); jset(deg_,(size_t)L,2); jset(deg_,(size_t)s.A,deg_[s.A]+2); jset(deg_,(size_t)s.B,deg_[s.B]+2); jsetl(nEdges_,nEdges_+4);
  jset(adart_,(size_t)L,e1); jset(adart_,(size_t)M2,s.mB); jset(adart_,(size_t)M1,s.mA);
  nv[0]=L; nv[1]=M2; int arr[8]={e1,g3,e2,f3,f1,f2,g1,g2}; memcpy(nd,arr,sizeof arr); }
static void fpIns(const InsSite& s, vector<int>& f){ f.assign({s.tmA,s.tmB}); int d=s.mA,k=0; do{ f.push_back(d); d=sigma(d); k++; } while(d!=s.mA && k<=deg_[s.M]); }

// ---------------- energy prediction ----------------
static long dEadd(U L,int cnt){ long m=mult_[L], d=0; for(int i=0;i<cnt;i++){ d+=(m==0?-1:+1); m++; } return d; }
static long dErem(U L,int cnt){ long m=mult_[L], d=0; for(int i=0;i<cnt;i++){ d+=(m==1?+1:-1); m--; } return d; }
static long dEaddOrbit(U L){ return isPole(L)? dEadd(L,n) : (long)n*dEadd(L,1); }
static long dEremOrbit(U L){ return isPole(L)? dErem(L,n) : (long)n*dErem(L,1); }
static bool createsDup(U L){ return mult_[L]>=1; }   // strict mode helper (orbit labels distinct, poles would dup at n>1 anyway)

// ---------------- symmetric move application ----------------
static int stamp_=0, istamp_=0; static vector<int> mark_, markImg_;
static long acc_[5]={0,0,0,0,0}, prop_[5]={0,0,0,0,0};
static int lastFocus=-1;
static bool tryMove(int kind,int site0,double T,mt19937_64& rng,bool force=false){
  static vector<RIIsite> S2; static vector<RIIIsite> S3; static vector<InvSite> SI; static vector<BigSite> SB; static vector<InsSite> SN; S2.resize(n); S3.resize(n); SI.resize(n); SB.resize(n); SN.resize(n);
  if((int)mark_.size()<(int)twin_.size()){ mark_.resize(twin_.size(),0); markImg_.resize(twin_.size(),0); }
  stamp_++; int cur=site0; int fp[16]; int fpn = kind==0?8:(kind==1?12:16); static vector<int> fpv;
  for(int k=0;k<n;k++){
    bool ok; if(kind==0){ ok=checkRII(cur,S2[k]); if(ok) fpRII(S2[k],fp); } else if(kind==1){ ok=checkRIII(cur,S3[k]); if(ok) fpRIII(S3[k],fp); } else if(kind==2){ ok=checkInv(cur,SI[k]); if(ok) fpInv(SI[k],fp); }
    else if(kind==3){ ok=checkBig(cur,SB[k]); if(ok){ fpBig(SB[k],fpv); fpn=0; istamp_++; for(int d:fpv){ if(markImg_[d]==istamp_) continue; markImg_[d]=istamp_; if(mark_[d]==stamp_) return false; mark_[d]=stamp_; } } }
    else { ok=checkIns(cur,SN[k]); if(ok){ fpIns(SN[k],fpv); fpn=0; istamp_++; for(int d:fpv){ if(markImg_[d]==istamp_) continue; markImg_[d]=istamp_; if(mark_[d]==stamp_) return false; mark_[d]=stamp_; } } }
    if(!ok) return false;
    for(int i=0;i<fpn;i++){ if(mark_[fp[i]]==stamp_) return false; mark_[fp[i]]=stamp_; }
    cur = rotd_[cur]; if(cur<0) return false;
  }
  if(cur!=site0) return false;
  long dE=0, dMiss=0, dDup=0; { static vector<int> simd; static vector<U> touched; if(simd.size()<mult_.size()) simd.assign(mult_.size(),0); touched.clear();
    auto add=[&](U L){ int m=mult_[L]+simd[L]; if(m==0){ dE-=1; dMiss-=1; } else { dE+=1; dDup+=1; } if(simd[L]==0) touched.push_back(L); simd[L]++; if(strictMode && m>=1) dE+=1000000; };
    auto rem=[&](U L){ int m=mult_[L]+simd[L]; if(m==1){ dE+=1; dMiss+=1; } else { dE-=1; dDup-=1; } if(simd[L]==0) touched.push_back(L); simd[L]--; };
    for(int k=0;k<n;k++){ if(kind==0){ add(S2[k].lx); add(S2[k].ly); } else if(kind==1){ rem(S3[k].lv); add(S3[k].lw); } else if(kind==2){ rem(SI[k].lx); rem(SI[k].ly); } else if(kind==3){ rem(SB[k].lL); rem(SB[k].lM); } else { add(SN[k].lL); add(SN[k].lM); } }
    for(U L:touched) simd[L]=0; if(dE>=1000000) return false; }
  prop_[kind]++;
  double dEeff=(double)dMiss+lambda_*(double)dDup;
  if(!force && dEeff>0){ double p=exp(-dEeff/((double)n*T)); if(uniform_real_distribution<double>(0,1)(rng)>=p) return false; }
  long E0=E_;
  static vector<array<int,2>> NV; static vector<array<int,10>> ND; NV.resize(n); ND.resize(n);
  for(int k=0;k<n;k++){ if(kind==0) applyRII(S2[k],NV[k].data(),ND[k].data()); else if(kind==1) applyRIII(S3[k],NV[k].data(),ND[k].data()); else if(kind==2) applyInv(SI[k],NV[k].data(),ND[k].data()); else if(kind==3) applyBig(SB[k],NV[k].data(),ND[k].data()); else applyIns(SN[k],NV[k].data(),ND[k].data()); }
  int nvc = kind==0?2:(kind==1?1:(kind==4?2:0)), ndc = kind==0?10:(kind==1?6:(kind==2?2:(kind==4?8:0)));
  for(int k=0;k<n;k++){ int k2=(k+1)%n; for(int i=0;i<nvc;i++) jset(rotv_,(size_t)NV[k][i],NV[k2][i]); for(int i=0;i<ndc;i++) jset(rotd_,(size_t)ND[k][i],ND[k2][i]); }
  if(E_-E0!=dE){ fprintf(stderr,"energy prediction mismatch kind %d: predicted %ld actual %ld\n",kind,dE,E_-E0); abort(); }
  if(kind==0) lastFocus = mult_[label_[NV[0][1]]]>1 ? NV[0][1] : NV[0][0]; else if(kind==1) lastFocus=NV[0][0]; else if(kind==2) lastFocus=orig_[ND[0][0]]; else if(kind==3) lastFocus=SB[0].M1; else lastFocus=NV[0][1];
  acc_[kind]++;
  if(checkEvery){ string why; if(!verifyStructure(why)){ fprintf(stderr,"structure broken after move kind %d: %s\n",kind,why.c_str()); saveRaw("broken.raw"); abort(); } }
  return true; }


// ---------------- hunt: short lookahead around a region for a move sequence with net dE < 0 (journaled undo) ----------------
static long hunts_=0, huntWins_=0; static int huntDepth=2, huntBranch=10;
static void genCand(int v, vector<pair<int,int>>& c){ c.clear(); if(v<0||!valive_[v]) return; int d0=adart_[v], d=d0; int k=0;
  do{ int w=orig_[twin_[d]]; if(deg_[v]==3){ if(k==0) c.push_back({1,d}); if(deg_[w]==3) c.push_back({2,d}); }
      c.push_back({0,d}); c.push_back({0,nxt_[d]}); c.push_back({0,nxt_[nxt_[d]]}); if(deg_[w]==3) c.push_back({1,twin_[d]});
      d=twin_[prv_[d]]; k++; } while(d!=d0 && k<32); }
static bool hunt(int v, int depth, long Estart, mt19937_64& rng){
  static vector<vector<pair<int,int>>> pool(8); if(depth<=0||depth>=(int)pool.size()) return false; auto& c=pool[depth]; genCand(v,c); shuffle(c.begin(),c.end(),rng);
  int tried=0;
  for(auto& kd:c){ if(tried>=huntBranch) break; size_t mark=J_.size();
    if(!tryMove(kd.first,kd.second,0.0,rng,true)) continue; tried++;
    if(E_<Estart) return true;
    if(depth>1 && E_<=Estart+2*n && hunt(lastFocus,depth-1,Estart,rng)) return true;
    jundoTo(mark); }
  return false; }
// ---------------- construction from unordered cube-square faces (label-unique states) ----------------
static bool buildFromFaces(const vector<array<U,4>>& cyc){   // each face given as u, u^i, u^i^j, u^j (cyclic, either direction)
  size_t F=cyc.size(); vector<int> ori(F,-1);
  unordered_map<uint64_t, vector<pair<int,int>>> edges; edges.reserve(F*4);
  auto key=[&](U p,U q){ if(p>q) swap(p,q); return ((uint64_t)p<<32)|q; };
  for(size_t f=0;f<F;f++) for(int k=0;k<4;k++) edges[key(cyc[f][k],cyc[f][(k+1)%4])].push_back({(int)f,k});
  for(auto& kv:edges) if(kv.second.size()!=2){ fprintf(stderr,"edge with %zu faces\n",kv.second.size()); return false; }
  // BFS orientation
  vector<int> q; ori[0]=0; q.push_back(0); size_t qi=0;
  while(qi<q.size()){ int f=q[qi++];
    for(int k=0;k<4;k++){ U p=cyc[f][k], r=cyc[f][(k+1)%4]; if(ori[f]) swap(p,r);   // f traverses p->r
      auto& lst=edges[key(p,r)]; auto other = lst[0].first==f&&lst[0].second==k ? lst[1] : lst[0]; int g=other.first, kk=other.second;
      int need = (cyc[g][kk]==r && cyc[g][(kk+1)%4]==p) ? 0 : 1;   // g must traverse r->p
      if(ori[g]==-1){ ori[g]=need; q.push_back(g); } else if(ori[g]!=need){ fprintf(stderr,"non-orientable face structure\n"); return false; } } }
  if(q.size()!=F){ fprintf(stderr,"faces not connected\n"); return false; }
  // vertices
  unordered_map<U,int> vid; vid.reserve(F);
  for(auto& c:cyc) for(U L:c) if(!vid.count(L)){ vid[L]=newVertex(L); }
  unordered_map<uint64_t,int> dmap; dmap.reserve(F*4);
  for(size_t f=0;f<F;f++){ U v[4]; for(int k=0;k<4;k++) v[k]=cyc[f][ ori[f]? (4-k)%4 : k ]; int ds[4];
    for(int k=0;k<4;k++){ int d=newDart(); orig_[d]=vid[v[k]]; axis_[d]=(uint8_t)__builtin_ctz(v[k]^v[(k+1)%4]); ds[k]=d; uint64_t kk=((uint64_t)v[k]<<32)|v[(k+1)%4]; if(dmap.count(kk)){ fprintf(stderr,"double dart\n"); return false; } dmap[kk]=d; }
    for(int k=0;k<4;k++) link(ds[k],ds[(k+1)%4]); }
  for(int d:live_){ U p=label_[orig_[d]]; U r=label_[orig_[nxt_[d]]]; auto it=dmap.find(((uint64_t)r<<32)|p); if(it==dmap.end()){ fprintf(stderr,"missing twin\n"); return false; } twin_[d]=it->second; }
  for(int d:live_){ deg_[orig_[d]]++; adart_[orig_[d]]=d; } nEdges_=live_.size()/2;
  for(int v=0;v<(int)label_.size();v++) if(valive_[v]){ auto it=vid.find(rot1(label_[v])); if(it==vid.end()){ fprintf(stderr,"not rotation symmetric (labels)\n"); return false; } rotv_[v]=it->second; }
  for(int d:live_){ U p=rot1(label_[orig_[d]]), r=rot1(label_[orig_[nxt_[d]]]); auto it=dmap.find(((uint64_t)p<<32)|r); if(it==dmap.end()){ fprintf(stderr,"not rotation symmetric (darts)\n"); return false; } rotd_[d]=it->second; }
  return true; }
static void intervalSphere(){
  vector<char> pres(1u<<n,0); pres[0]=pres[FULL]=1; for(int i=0;i<n;i++) for(int L=1;L<n;L++){ U m=0; for(int t=0;t<L;t++) m|=1u<<((i+t)%n); pres[m]=1; }
  vector<array<U,4>> cyc; for(U x=0;x<=FULL;x++){ if(!pres[x]) continue; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ if((x>>i&1)||(x>>j&1)) continue; if(pres[x^(1u<<i)]&&pres[x^(1u<<j)]&&pres[x^(1u<<i)^(1u<<j)]) cyc.push_back({x,x^(1u<<i),x^(1u<<i)^(1u<<j),x^(1u<<j)}); } }
  if(!buildFromFaces(cyc)){ fprintf(stderr,"interval sphere build failed\n"); exit(2); } }
static bool loadFacesJson(const string& path){
  FILE* f=fopen(path.c_str(),"r"); if(!f) return false; string text; char buf[1<<16]; size_t r; while((r=fread(buf,1,sizeof buf,f))>0) text.append(buf,r); fclose(f);
  size_t p=text.find("\"faces\""); if(p==string::npos) return false; vector<array<U,4>> cyc; vector<U> quad; size_t i=text.find('[',p);
  while(i<text.size()){
    if(text[i]=='"'){ size_t j=text.find('"',i+1); string lab=text.substr(i+1,j-i-1); if((int)lab.size()!=n) return false; U m=0; for(int b=0;b<n;b++) if(lab[b]=='1') m|=1u<<b; quad.push_back(m); i=j+1;
      if(quad.size()==4){ U c=quad[0]&quad[1]&quad[2]&quad[3]; U sp=(quad[0]|quad[1]|quad[2]|quad[3])^c; if(__builtin_popcount(sp)!=2) return false; int a=__builtin_ctz(sp), b=31-__builtin_clz(sp); cyc.push_back({c,c^(1u<<a),c^(1u<<a)^(1u<<b),c^(1u<<b)}); quad.clear(); } continue; }
    if(text[i]==']' && (text.compare(i,9,"],\"moves\"")==0 || text.compare(i,2,"]}")==0 || text.compare(i,3,"],\n")==0)) { if(quad.empty()) break; }
    i++; }
  fprintf(stderr,"loaded %zu faces\n",cyc.size()); return buildFromFaces(cyc); }
// raw state save/load (exact, duplicates allowed)
static void saveRaw(const string& path){ FILE* f=fopen(path.c_str(),"w"); fprintf(f,"%d %zu %zu\n",n,label_.size(),twin_.size());
  for(size_t v=0;v<label_.size();v++) fprintf(f,"%d %u %d\n", valive_[v]?1:0, label_[v], rotv_[v]);
  for(size_t d=0;d<twin_.size();d++) fprintf(f,"%d %d %d %d %d %d\n", dalive_[d]?1:0, twin_[d], nxt_[d], orig_[d], axis_[d], rotd_[d]); fclose(f); }
static bool loadRaw(const string& path){ FILE* f=fopen(path.c_str(),"r"); if(!f) return false; int nn; size_t NV,ND; if(fscanf(f,"%d %zu %zu",&nn,&NV,&ND)!=3||nn!=n) return false;
  for(size_t v=0;v<NV;v++){ int al,rv; unsigned L; fscanf(f,"%d %u %d",&al,&L,&rv); label_.push_back(L); adart_.push_back(-1); deg_.push_back(0); rotv_.push_back(rv); valive_.push_back(al); posInLabel.push_back(-1);
    if(al){ nV_++; int m=mult_[L]; if(m==0){missing_--;E_--; listDel(missingList,missingPos,L);} else {dups_++;E_++; if(m==1) listAdd(dupList,dupPos,L);} mult_[L]=m+1; posInLabel[v]=(int)byLabel[L].size(); byLabel[L].push_back((int)v); } else freeV_.push_back((int)v); }
  for(size_t d=0;d<ND;d++){ int al,tw,nx,og,ax,rd; fscanf(f,"%d %d %d %d %d %d",&al,&tw,&nx,&og,&ax,&rd); twin_.push_back(tw); nxt_.push_back(nx); prv_.push_back(-1); orig_.push_back(og); axis_.push_back((uint8_t)ax); rotd_.push_back(rd); dalive_.push_back(al); dpos_.push_back(-1); if(al){ dpos_[d]=(int)live_.size(); live_.push_back((int)d); } else freeD_.push_back((int)d); }
  fclose(f); for(int d:live_){ prv_[nxt_[d]]=d; deg_[orig_[d]]++; adart_[orig_[d]]=d; } nEdges_=live_.size()/2; return true; }

// ---------------- verification ----------------
static bool verifyStructure(string& why){
  vector<char> seen(twin_.size(),0); long F=0;
  for(int d:live_){ if(seen[d]) continue; int c=0, e=d; U labs[4]; do{ seen[e]=1; labs[c]=label_[orig_[e]]; e=nxt_[e]; c++; if(c>4) break; } while(e!=d);
    if(c!=4||e!=d){ why="face not a 4-cycle"; return false; } U sp=labs[0]^labs[2]; if(__builtin_popcount(sp)!=2||(labs[1]^labs[3])!=sp||!onebit(labs[0]^labs[1])){ why="face not a cube square"; return false; } F++; }
  if(nV_-nEdges_+F!=2){ why="Euler characteristic"; return false; }
  { long dsum=0; for(int v=0;v<(int)label_.size();v++) if(valive_[v]){ int d0=adart_[v]; if(d0<0||!dalive_[d0]||orig_[d0]!=v){ why="adart"; return false; } int d=d0,k=0; do{ if(orig_[d]!=v){ why="rotation origin"; return false; } d=twin_[prv_[d]]; k++; } while(d!=d0 && k<=deg_[v]); if(k!=deg_[v]){ why="vertex rotation not a single cycle of length deg"; return false; } dsum+=k; } if(dsum!=(long)live_.size()){ why="degree sum"; return false; } }
  for(int d:live_){ if(!dalive_[twin_[d]]||twin_[twin_[d]]!=d||orig_[twin_[d]]!=orig_[nxt_[d]]){ why="twin structure"; return false; } }
  for(int v=0;v<(int)label_.size();v++) if(valive_[v]){ int rv=rotv_[v]; if(rv<0||!valive_[rv]||label_[rv]!=rot1(label_[v])){ why="vertex rotation"; return false; } }
  for(int d:live_){ int rd=rotd_[d]; if(rd<0||!dalive_[rd]||orig_[rd]!=rotv_[orig_[d]]||twin_[rd]!=rotd_[twin_[d]]||nxt_[rd]!=rotd_[nxt_[d]]||axis_[rd]!=(axis_[d]+n-1)%n){ why="dart rotation"; return false; } }
  // each curve one cycle: faces with axis i connected through axis-i edges
  for(int i=0;i<n;i++){ long total=0; int start=-1; for(int d:live_) if(axis_[d]==i){ total++; if(start<0) start=d; } total/=2; // each face with axis i has 2 darts of axis i... counted per dart: darts of axis i = 2 per face per side -> total darts axis i = 2*faces? each face has exactly 2 axis-i darts; so faces_i = darts_i/2
    if(total==0){ why="curve missing"; return false; }
    long vis=0; int d=start; // d is an axis-i dart in some face; the other axis-i dart of this face is nxt(nxt(d)); cross via twin
    do{ vis++; int d2=nxt_[nxt_[d]]; if(axis_[d2]!=i){ why="face axis pattern"; return false; } d=twin_[d2]; } while(d!=start && vis<=total);
    if(vis!=total){ why="curve not a single cycle"; return false; } }
  return true; }
static bool verifyVenn(string& why){ if(!verifyStructure(why)) return false; for(U L=0;L<=FULL;L++) if(mult_[L]!=1){ why="label multiplicity"; return false; } return true; }
static void exportFacesJson(const string& path){
  FILE* f=fopen(path.c_str(),"w"); fprintf(f,"{\"n\":%d,\"labels\":%ld,\"energy\":%ld,\"missing\":%ld,\"duplicates\":%ld,\"faces\":[",n,nV_,E_,missing_,dups_);
  vector<char> seen(twin_.size(),0); bool first=true;
  for(int d:live_){ if(seen[d]) continue; fprintf(f,"%s[",first?"":","); first=false; int e=d; int c=0; do{ seen[e]=1; U L=label_[orig_[e]]; string s(n,'0'); for(int b=0;b<n;b++) if(L>>b&1) s[b]='1'; fprintf(f,"%s\"%s\"",c?",":"",s.c_str()); e=nxt_[e]; c++; } while(e!=d && c<8); fprintf(f,"]"); }
  fprintf(f,"],\"full\":%s}\n",E_==0?"true":"false"); fclose(f); }

int main(int argc,char** argv){
  if(argc<7){ fprintf(stderr,"usage: %s n seconds seed out_prefix T0 T1 [load|-] [--strict] [pT pR] [reportEvery] [exportEvery]\n",argv[0]); return 1; }
  n=atoi(argv[1]); double seconds=atof(argv[2]); unsigned long seed=strtoul(argv[3],0,10); string out=argv[4]; double T0=atof(argv[5]), T1=atof(argv[6]);
  string load=argc>7?argv[7]:"-"; int ai=8; if(argc>ai && string(argv[ai])=="--strict"){ strictMode=true; ai++; }
  double pT=argc>ai+1?atof(argv[ai]):0.25, pR=argc>ai+1?atof(argv[ai+1]):0.25; if(argc>ai+1) ai+=2; double reportEvery=argc>ai?atof(argv[ai]):10.0; double exportEvery=argc>ai+1?atof(argv[ai+1]):60.0;
  FULL=(1u<<n)-1; mult_.assign(1u<<n,0); missing_=1L<<n; E_=missing_;
  byLabel.assign(1u<<n,{}); missingPos.assign(1u<<n,-1); dupPos.assign(1u<<n,-1); missingList.reserve(1u<<n); for(U L=0;L<=FULL;L++) listAdd(missingList,missingPos,L);
  double pTarget=getenv("RW_TARGET")?atof(getenv("RW_TARGET")):0.5; if(getenv("RW_THOT")) tHot_=atof(getenv("RW_THOT")); double lam0=getenv("RW_LAMBDA0")?atof(getenv("RW_LAMBDA0")):1.0, lam1=getenv("RW_LAMBDA1")?atof(getenv("RW_LAMBDA1")):lam0; double lamPeriod=getenv("RW_LAMBDA_PERIOD")?atof(getenv("RW_LAMBDA_PERIOD")):0.0; double pHunt=getenv("RW_HUNT")?atof(getenv("RW_HUNT")):0.0; double pB=getenv("RW_PB")?atof(getenv("RW_PB")):0.15; huntDepth=getenv("RW_DEPTH")?atoi(getenv("RW_DEPTH")):2; huntBranch=getenv("RW_BRANCH")?atoi(getenv("RW_BRANCH")):10;
  if(load=="-") intervalSphere(); else if(load.size()>4&&load.substr(load.size()-4)==".raw"){ if(!loadRaw(load)){ fprintf(stderr,"raw load failed\n"); return 2; } } else if(!loadFacesJson(load)){ fprintf(stderr,"load failed\n"); return 2; }
  fprintf(stderr,"start: V=%ld E(dges)=%ld missing=%ld dups=%ld energy=%ld strict=%d\n",nV_,nEdges_,missing_,dups_,E_,(int)strictMode);
  { string why; bool ok=verifyStructure(why); fprintf(stderr,"start structure: %s %s\n",ok?"OK":"BROKEN",why.c_str()); if(!ok) return 3; }
  if(getenv("RW_CHECK")) checkEvery=true;

  // ---------------- replicas (parallel tempering) ----------------
  struct Replica{ vector<int> twin,nxt,prv,orig,rotd,dpos,live,freeD,adart,deg,rotv,freeV,posInLabel,missingPos,dupPos; vector<uint8_t> axis; vector<char> dalive,valive; vector<U> label,missingList,dupList; vector<uint16_t> mult; vector<vector<int>> byLabel; long E,missing,dups,nV,nEdges; double T; mt19937_64 rng; long bestE, steps; };
  auto swapState=[&](Replica& r){ swap(twin_,r.twin); swap(nxt_,r.nxt); swap(prv_,r.prv); swap(orig_,r.orig); swap(rotd_,r.rotd); swap(dpos_,r.dpos); swap(live_,r.live); swap(freeD_,r.freeD); swap(adart_,r.adart); swap(deg_,r.deg); swap(rotv_,r.rotv); swap(freeV_,r.freeV); swap(posInLabel,r.posInLabel); swap(missingPos,r.missingPos); swap(dupPos,r.dupPos); swap(axis_,r.axis); swap(dalive_,r.dalive); swap(valive_,r.valive); swap(label_,r.label); swap(missingList,r.missingList); swap(dupList,r.dupList); swap(mult_,r.mult); swap(byLabel,r.byLabel); swap(E_,r.E); swap(missing_,r.missing); swap(dups_,r.dups); swap(nV_,r.nV); swap(nEdges_,r.nEdges); };
  vector<double> temps; { const char* e=getenv("RW_TEMPS"); string ts=e?e:""; if(ts.empty()){ temps={T0}; } else { size_t i=0; while(i<ts.size()){ size_t j=ts.find(',',i); if(j==string::npos) j=ts.size(); temps.push_back(atof(ts.substr(i,j-i).c_str())); i=j+1; } } }
  int K=(int)temps.size(); long chunk=getenv("RW_CHUNK")?atol(getenv("RW_CHUNK")):200000;
  vector<Replica> rep(K);
  for(int k=0;k<K;k++){ Replica& r=rep[k]; r.twin=twin_; r.nxt=nxt_; r.prv=prv_; r.orig=orig_; r.rotd=rotd_; r.dpos=dpos_; r.live=live_; r.freeD=freeD_; r.adart=adart_; r.deg=deg_; r.rotv=rotv_; r.freeV=freeV_; r.posInLabel=posInLabel; r.missingPos=missingPos; r.dupPos=dupPos; r.axis=axis_; r.dalive=dalive_; r.valive=valive_; r.label=label_; r.missingList=missingList; r.dupList=dupList; r.mult=mult_; r.byLabel=byLabel; r.E=E_; r.missing=missing_; r.dups=dups_; r.nV=nV_; r.nEdges=nEdges_; r.T=temps[k]; r.rng.seed(seed*1000+k); r.bestE=E_; r.steps=0; }
  auto t0=chrono::steady_clock::now(); auto el=[&](){ return chrono::duration<double>(chrono::steady_clock::now()-t0).count(); };
  long bestE=E_; double lastRep=0, lastExp=0, lastBestSave=-1e9; long bestSaveCap=getenv("RW_BESTCAP")?atol(getenv("RW_BESTCAP")):3000; bool done=false; long swapsTried=0, swapsAcc=0;
  auto proposal=[&](double T, mt19937_64& rng){
    double r=uniform_real_distribution<double>(0,1)(rng);
    if(r<pHunt && (!dupList.empty()||!missingList.empty())){ hunts_++; long Es=E_; jon_=true; J_.clear(); bool win=false;
      if(!dupList.empty() && (missingList.empty() || uniform_real_distribution<double>(0,1)(rng)<0.5)){ U D=dupList[uniform_int_distribution<size_t>(0,dupList.size()-1)(rng)]; auto& R=byLabel[D]; int v=R[uniform_int_distribution<size_t>(0,R.size()-1)(rng)]; win=hunt(v,huntDepth,Es,rng); }
      else { U L=missingList[uniform_int_distribution<size_t>(0,missingList.size()-1)(rng)]; int b=uniform_int_distribution<int>(0,n-1)(rng), c=uniform_int_distribution<int>(0,n-1)(rng);
        if(b!=c){ U Lu=L^(1u<<b)^(1u<<c); auto& R=byLabel[Lu]; if(!R.empty()){ int u=R[uniform_int_distribution<size_t>(0,R.size()-1)(rng)];
          int d0=adart_[u], d=d0; int tries=0; do{ int a=axis_[d]; if(a!=b&&a!=c){ int ax1=axis_[nxt_[d]], ax2=axis_[nxt_[twin_[d]]]; if((ax1==b&&ax2==c)||(ax1==c&&ax2==b)){
                if(tryMove(0,d,0.0,rng,true)){ if(E_<Es) win=true; else if(hunt(lastFocus,huntDepth,Es,rng)) win=true; else if(E_>Es) jundoTo(0); else win=false; }
                break; } } d=twin_[prv_[d]]; tries++; } while(d!=d0 && tries<64); } } }
      if(win) huntWins_++; jon_=false; J_.clear(); return; }
    if(r<pHunt+pTarget && (!missingList.empty()||!dupList.empty())){ if(tHot_>=0) T=tHot_;
      bool doMissing = dupList.empty() || (!missingList.empty() && uniform_real_distribution<double>(0,1)(rng) < (double)missingList.size()/(missingList.size()+dupList.size()));
      if(doMissing){ U L=missingList[uniform_int_distribution<size_t>(0,missingList.size()-1)(rng)]; int b=uniform_int_distribution<int>(0,n-1)(rng), c=uniform_int_distribution<int>(0,n-1)(rng); if(b==c) return;
        U Lu=L^(1u<<b)^(1u<<c); auto& R=byLabel[Lu]; if(R.empty()) return; int u=R[uniform_int_distribution<size_t>(0,R.size()-1)(rng)];
        int d0=adart_[u], d=d0; int tries=0; do{ int a=axis_[d]; if(a!=b&&a!=c){ int ax1=axis_[nxt_[d]], ax2=axis_[nxt_[twin_[d]]]; if((ax1==b&&ax2==c)||(ax1==c&&ax2==b)){ tryMove(0,d,T,rng); break; } } d=twin_[prv_[d]]; tries++; } while(d!=d0 && tries<64); }
      else { U D=dupList[uniform_int_distribution<size_t>(0,dupList.size()-1)(rng)]; auto& R=byLabel[D]; int v=R[uniform_int_distribution<size_t>(0,R.size()-1)(rng)];
        if(deg_[v]==2){ tryMove(3,adart_[v],T,rng); return; } if(deg_[v]!=3) return;
        int d0=adart_[v], d=d0; int k=uniform_int_distribution<int>(0,2)(rng); for(int i=0;i<k;i++) d=twin_[prv_[d]];
        if(uniform_real_distribution<double>(0,1)(rng)<0.5){ tryMove(1,d,T,rng); } else { int dd=d; for(int i=0;i<3;i++){ if(deg_[orig_[twin_[dd]]]==3 && tryMove(2,dd,T,rng)) break; dd=twin_[prv_[dd]]; } } }
      return; }
    int d=live_[uniform_int_distribution<size_t>(0,live_.size()-1)(rng)];
    double rr=(r-pHunt-pTarget)/(1-pHunt-pTarget);
    if(rr<pB){ if(deg_[orig_[d]]==2) tryMove(3,d,T,rng); else { insK_=1+uniform_int_distribution<int>(0,max(1,deg_[orig_[d]]-1)-1)(rng); tryMove(4,d,T,rng); } }
    else if(rr<pB+pT){ if(deg_[orig_[d]]==3) tryMove(1,d,T,rng); }
    else if(rr<pB+pT+pR){ if(deg_[orig_[d]]==3&&deg_[orig_[twin_[d]]]==3) tryMove(2,d,T,rng); }
    else tryMove(0,d,T,rng); };
  // the globals now hold a copy identical to rep[0]; run replicas by swapping their state in and out
  while(!done){
    double t=el(); if(t>=seconds) break; if(lamPeriod>0){ double ph=fmod(t,lamPeriod)/lamPeriod; double tri = ph<0.5? 2*ph : 2-2*ph; lambda_=lam0+(lam1-lam0)*tri; } else lambda_=lam0+(lam1-lam0)*(t/seconds);
    for(int k=0;k<K && !done;k++){ Replica& r=rep[k]; swapState(r); double T = (K==1)? T0+(T1-T0)*(t/seconds) : r.T;
      for(long i=0;i<chunk;i++){ proposal(T,r.rng); r.steps++; if(E_<r.bestE){ r.bestE=E_; if(E_<bestE){ bestE=E_; if(E_<=bestSaveCap && el()-lastBestSave>=5.0){ saveRaw(out+"-best.raw"); lastBestSave=el(); } }
          if(E_==0){ string why; bool ok=verifyVenn(why); fprintf(stderr,"t=%.1f replica %d (T=%.3f) ENERGY ZERO: native check %s %s\n",el(),k,T,ok?"PASSED":"FAILED",why.c_str()); exportFacesJson(out+"-venn.json"); saveRaw(out+"-venn.raw"); if(ok){ done=true; break; } } } }
      swapState(r); }
    if(K>1){ for(int k=0;k+1<K;k++){ Replica &a=rep[k], &b=rep[k+1]; swapsTried++; double la = a.T>0? 1.0/a.T : 1e18, lb = b.T>0? 1.0/b.T : 1e18; double dl=la-lb; double dE=(double)(a.E-b.E)/n; double arg=dl*dE; bool acc = arg>=0 || uniform_real_distribution<double>(0,1)(a.rng) < exp(arg);
        if(a.T==0) acc = b.E<=a.E; if(acc){ swapsAcc++; double Ta=a.T, Tb=b.T; swap(a,b); a.T=Ta; b.T=Tb; } } }
    if(t-lastRep>=reportEvery){ lastRep=t; string line; for(int k=0;k<K;k++){ char buf[128]; snprintf(buf,sizeof buf," [T=%.2f E=%ld m=%ld d=%ld]",rep[k].T,rep[k].E,rep[k].missing,rep[k].dups); line+=buf; } fprintf(stderr,"t=%.0f best=%ld lam=%.2f swaps %ld/%ld acc L/T/R/B/I=%ld/%ld/%ld/%ld/%ld of %ld/%ld/%ld/%ld/%ld%s\n",t,bestE,lambda_,swapsAcc,swapsTried,acc_[0],acc_[1],acc_[2],acc_[3],acc_[4],prop_[0],prop_[1],prop_[2],prop_[3],prop_[4],line.c_str()); if(getenv("RW_DBG")){ fprintf(stderr,"bigFail:"); for(int i=0;i<16;i++) if(bigFail[i]) fprintf(stderr," [%d]=%ld",i,bigFail[i]); fprintf(stderr,"\n"); } }
    if(t-lastExp>=exportEvery){ lastExp=t; swapState(rep[0]); saveRaw(out+"-last.raw"); swapState(rep[0]); }
  }
  swapState(rep[0]);
  if(getenv("RW_DBG2")){ long cnt[16]={0}, n2=0, okc=0; for(int v=0;v<(int)label_.size();v++) if(valive_[v]&&deg_[v]==2){ n2++; BigSite bs; int why=0; if(checkBigI(adart_[v],bs,why)) okc++; else cnt[why]++; }
    fprintf(stderr,"deg-2 vertices: %ld, removable by checkBig: %ld, failures:",n2,okc); for(int i=0;i<16;i++) if(cnt[i]) fprintf(stderr," [%d]=%ld",i,cnt[i]); fprintf(stderr,"\n"); }
  saveRaw(out+"-last.raw"); exportFacesJson(out+"-last.json");
  long steps=0; for(auto& r:rep) steps+=r.steps;
  printf("{\"n\":%d,\"seed\":%lu,\"seconds\":%.1f,\"steps\":%ld,\"energy\":%ld,\"missing\":%ld,\"dups\":%ld,\"best_energy\":%ld,\"complete\":%s,\"labels\":%ld}\n",n,seed,el(),steps,E_,missing_,dups_,bestE,done?"true":"false",nV_);
  return 0; }
