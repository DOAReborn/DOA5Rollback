namespace sc {
static volatile LONG ctxFrame,ctxConf;
static unsigned callLogs;
static volatile LONG gate;
static volatile LONG blocked;
static volatile LONG nBlocked;
static volatile LONG fired;
struct Call { BYTE slot; DWORD target; WORD count; };
struct List { Call c[48]; unsigned n; };
static List cur,prev; static SRWLOCK lock=SRWLOCK_INIT;
static DWORD total[40]; static unsigned casses;

static unsigned emptyLogs;
static bool EmptyMethod(DWORD ecx,DWORD slot) {
    const DWORD obj=Read(reinterpret_cast<void*>(ecx)),vt=obj?Read(reinterpret_cast<void*>(obj)):0;
    const DWORD target=vt?Read(reinterpret_cast<void*>(vt+slot*4)):0;if(!target)return false;
    BYTE c[3]={};if(!Copy(c,reinterpret_cast<void*>(target),3))return false;
    const bool empty=(c[0]==0x32 || c[0]==0x33) && c[1]==0xC0 && (c[2]==0xC2 || c[2]==0xC3);
    if(empty && emptyLogs<6){++emptyLogs;cp::Logf("SCENE : methode n%lu vide sur ce stage (%06lX) : jamais bloquee ni rejouee.",slot,target-reinterpret_cast<DWORD>(base));}
    return empty;
}

static DWORD diagLo,diagHi,diagLo2,diagHi2; static bool Diag(DWORD f){if constexpr(!kTest){(void)f;return false;}else return (diagHi && f>=diagLo && f<=diagHi) || (diagHi2 && f>=diagLo2 && f<=diagHi2);}

#ifdef DOA5RB_RELEASE
static constexpr bool diagEvt=false;
#else
static bool diagEvt=false;
#endif
 static volatile LONG diagEvtImage=-1; static unsigned diagEvtLignes;
static const DWORD diagRng[7]={0x20906E0,0x10844E8,0x2071378,0x2072A58,0x2070830,0x206FE68,0x1087AB0};
static void DiagRngTexte(char* out,size_t cap,bool empreinte){size_t n=0;out[0]=0;static BYTE t[0x9C0];
    for(int r=0;r<7;++r){const DWORD a=reinterpret_cast<DWORD>(base+diagRng[r]);const DWORD p=Read(reinterpret_cast<void*>(a+0x9C0)),c=Read(reinterpret_cast<void*>(a+0x9C4));
        const unsigned idx=p>=a && p<=a+0x9C0?(p-a)/4:0xFFFF;DWORD h=2166136261u;
        if(empreinte){Copy(t,base+diagRng[r],sizeof(t));for(DWORD k=0;k<sizeof(t);++k)h=(h^t[k])*16777619u;}
        const int w=empreinte?_snprintf_s(out+n,cap-n,_TRUNCATE,"%s%u/%lu/%04lX",r?" ":"",idx,c,h&0xFFFF):_snprintf_s(out+n,cap-n,_TRUNCATE,"%s%u/%lu",r?" ":"",idx,c);
        if(w>0)n+=w;}}
static DWORD __cdecl Note(DWORD ecx,DWORD slot,const DWORD* args) {
    const bool event=(slot==18 || slot==25 || slot==30) && !EmptyMethod(ecx,slot);
    if(diagEvt && event && slot==18 && diagEvtLignes<1000 && Read(base+0x1087A4C)==4){++diagEvtLignes;char g[200];DiagRngTexte(g,sizeof g,true);
        cp::Logf("DIAG EVT n18 image %ld (confirmee %ld, %s) : arguments %04lX.%04lX %04lX.%04lX %04lX.%04lX %04lX.%04lX ; generateurs (6 effets + combat, indice/compteur/empreinte) avant : %s.",
            ctxFrame,ctxConf,gate?"predite : ignore":"execute",args[0]>>16,args[0]&0xFFFF,args[1]>>16,args[1]&0xFFFF,args[2]>>16,args[2]&0xFFFF,args[3]>>16,args[3]&0xFFFF,g);
        InterlockedExchange(&diagEvtImage,ctxFrame);}
    if(event && (callLogs<250 || Diag(static_cast<DWORD>(ctxFrame))) && Read(base+0x1087A4C)==4) {
        ++callLogs;DWORD a[4]={};memcpy(a,args,slot==18?16:slot==25?4:8);

        char ou[24]="hors du jeu";
        if constexpr(kTest){const DWORD ret=args[-1],b0=reinterpret_cast<DWORD>(base);if(ret>=b0 && ret<b0+0x21F8000)_snprintf_s(ou,sizeof ou,_TRUNCATE,"game+%06lX",ret-b0);}
        cp::Logf("SCENE appel n%lu pendant l'image %ld (confirmee %ld) : %s ; arguments %08lX %08lX %08lX %08lX ; appel de %s.",
            slot,ctxFrame,ctxConf,gate?"IGNORE (image predite)":"execute",a[0],a[1],a[2],a[3],ou);
    }
    if(event && !gate)InterlockedExchange(&fired,1);
    if(event && gate){InterlockedExchange(&blocked,1);InterlockedIncrement(&nBlocked);return 1;}
    if(Read(base+0x1087A4C)!=4)return 0;
    const DWORD obj=Read(reinterpret_cast<void*>(ecx)),vt=obj?Read(reinterpret_cast<void*>(obj)):0;
    const DWORD target=vt?Read(reinterpret_cast<void*>(vt+slot*4)):0;
    AcquireSRWLockExclusive(&lock);
    if(slot<40)++total[slot];
    bool found=false;
    for(unsigned i=0;i<cur.n;++i)if(cur.c[i].slot==slot && cur.c[i].target==target){++cur.c[i].count;found=true;break;}
    if(!found && cur.n<48){cur.c[cur.n].slot=static_cast<BYTE>(slot);cur.c[cur.n].target=target;cur.c[cur.n].count=1;++cur.n;}
    ReleaseSRWLockExclusive(&lock);
    return 0;
}
static void Text(const List& l,char* out,size_t cap) {
    size_t len=0;out[0]=0;const DWORD b=reinterpret_cast<DWORD>(base);
    for(unsigned i=0;i<l.n;++i){const int w=_snprintf_s(out+len,cap-len,_TRUNCATE," n%u>%06lX x%u",l.c[i].slot,l.c[i].target>=b?l.c[i].target-b:l.c[i].target,l.c[i].count);if(w<=0)break;len+=w;}
}

static List ring64[64]; static DWORD ringAt[64]; static unsigned zoneLogs;
static void ZoneReport(DWORD x,DWORD from,DWORD to) {
    if(zoneLogs>=6)return;++zoneLogs;const DWORD b=reinterpret_cast<DWORD>(base);
    cp::Logf("SCENE ZONE : changement de zone %lu -> %lu a l'image %lu (reference) : appels rares des 64 images precedentes :",from,to,x);
    struct E{BYTE slot;DWORD target;unsigned frames;DWORD f[8];};E e[96];unsigned ne=0;
    for(unsigned i=0;i<64;++i){const DWORD f=ringAt[i];if(!f || f+64<=x || f>x)continue;const List& l=ring64[i];
        for(unsigned j=0;j<l.n;++j){unsigned k=0;for(;k<ne;++k)if(e[k].slot==l.c[j].slot && e[k].target==l.c[j].target)break;
            if(k==ne){if(ne>=96)continue;e[ne].slot=l.c[j].slot;e[ne].target=l.c[j].target;e[ne].frames=0;++ne;}
            if(e[k].frames<8)e[k].f[e[k].frames]=f;++e[k].frames;}}
    for(unsigned k=0;k<ne;++k){if(e[k].frames>8)continue;char t[160];size_t ln=0;t[0]=0;for(unsigned i=0;i<e[k].frames;++i){const int w=_snprintf_s(t+ln,sizeof(t)-ln,_TRUNCATE," %lu",e[k].f[i]);if(w>0)ln+=w;}
        cp::Logf("SCENE ZONE :   n%u > %06lX dans %u image(s) :%s.",e[k].slot,e[k].target>=b?e[k].target-b:e[k].target,e[k].frames,t);}
    cp::Logf("SCENE ZONE : %u methode(s) differente(s) appelees dans ces 64 images.",ne);
}

static void AtFrame(DWORD x,bool changed) {
    AcquireSRWLockExclusive(&lock);
    ring64[x%64]=cur;ringAt[x%64]=x;
    if(changed && casses<20) {
        ++casses;char a[700],b[700];Text(cur,a,sizeof(a));Text(prev,b,sizeof(b));
        cp::Logf("SCENE casse a l'image %lu : methodes appelees cette image :%s ; image precedente :%s",x,a,b);
    }
    prev=cur;cur.n=0;
    ReleaseSRWLockExclusive(&lock);
}
static void Summary() {
    char line[500];size_t len=0;line[0]=0;
    for(unsigned s=0;s<40;++s)if(total[s]){const int w=_snprintf_s(line+len,sizeof(line)-len,_TRUNCATE," n%u:%lu",s,total[s]);if(w>0)len+=w;total[s]=0;}
    if(len)cp::Logf("SCENE appels par methode (3 s) :%s",line);
}

static bool Install(BYTE* image) {
    static const DWORD wrappers[]={0x59DB40,0x59DB50,0x59DC50,0x59DC80,0x59DC90,0x59DCA0,0x59DCB0,0x59DCC0,0x59DCD0,0x59DCF0,0x59DD40,0x59DD50};
    BYTE* code=static_cast<BYTE*>(VirtualAlloc(nullptr,0x1000,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE));if(!code)return false;
    BYTE* p=code;unsigned ok=0;
    for(DWORD w:wrappers) {
        BYTE* s=image+w;
        if(!(s[0]==0x55 && s[1]==0x8B && s[2]==0xEC && s[3]==0x8B && s[4]==0x09 && s[5]==0x8B && s[6]==0x01 && s[7]==0x8B && s[8]==0x40 && s[10]==0x5D && s[11]==0xFF && s[12]==0xE0))continue;
        const BYTE off=s[9];BYTE* stub=p;
        *p++=0x60;*p++=0x9C;*p++=0x8D;*p++=0x44;*p++=0x24;*p++=0x28;*p++=0x50;
        *p++=0x6A;*p++=static_cast<BYTE>(off/4);*p++=0x51;
        *p++=0xE8;{DWORD rel=reinterpret_cast<DWORD>(&Note)-(reinterpret_cast<DWORD>(p)+4);memcpy(p,&rel,4);p+=4;}
        *p++=0x83;*p++=0xC4;*p++=0x0C;
        *p++=0x89;*p++=0x44;*p++=0x24;*p++=0x20;
        *p++=0x9D;*p++=0x61;
        const WORD ret=off==0x48?0x18:off==0x64?4:off==0x78?8:0;
        if(ret){*p++=0x85;*p++=0xC0;*p++=0x74;*p++=0x05;
                *p++=0x33;*p++=0xC0;*p++=0xC2;memcpy(p,&ret,2);p+=2;}
        *p++=0x8B;*p++=0x09;*p++=0x8B;*p++=0x01;*p++=0x8B;*p++=0x40;*p++=off;*p++=0xFF;*p++=0xE0;
        DWORD old=0,ig=0;if(!VirtualProtect(s,5,PAGE_EXECUTE_READWRITE,&old))continue;
        s[0]=0xE9;const DWORD rel=reinterpret_cast<DWORD>(stub)-(reinterpret_cast<DWORD>(s)+5);memcpy(s+1,&rel,4);
        VirtualProtect(s,5,old,&ig);FlushInstructionCache(GetCurrentProcess(),s,5);++ok;
    }
    FlushInstructionCache(GetCurrentProcess(),code,0x1000);
    cp::Logf("SCENE : %u enveloppes de methodes de la scene suivies.",ok);
    return ok>0;
}
}
