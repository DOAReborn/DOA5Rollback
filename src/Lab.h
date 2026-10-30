static volatile LONG g_netRemoteDev=-1;
static volatile LONG g_netLocalDev=-1;
static volatile LONG g_trBypass=0;
static volatile LONG g_roomOpen=0;
static volatile LONG g_selHold=0;
namespace sel { static bool Tick(); }
namespace net {
static bool enabled; static int role=1; static volatile LONG active; static DWORD remoteHave;
static bool verrouCourant=true; static DWORD verrouImage;
static DWORD localPlace=0,remotePlace=1; static volatile LONG& remoteDev=g_netRemoteDev; static volatile LONG& localDev=g_netLocalDev;
static bool UpdateHook(); static void OnConfirmed(DWORD j); static void Report();
}
namespace lab {
using cp::Logf;
constexpr unsigned RING=32,IR=128;
constexpr DWORD REF_FRAMES=16384,RAW_FRAMES=8192,RAWHALF=0xD90,LOGIC=0x910,RAWSZ=2*RAWHALF+LOGIC,MAXCORE=32,SLOTS=0x10878F8,SLOT=0x2C;
static DWORD delay=4;
static const char* coreNames[]={"rng","players","player_secondary","player_history_previous","player_history_current",
    "feed_globals","stream_cursor","body_position","animation_time","animation_advance_gate"};

static DWORD* refHash; static BYTE* refRaw; static bool* refHave; static DWORD replayId; static int pass;
static unsigned coreIdx[MAXCORE],coreCount,refCoreCount; static const char* refCoreName[MAXCORE];
static DWORD stableMask; static BYTE rawMask[RAWSZ]; static DWORD rawMasked;

struct In { BYTE b[SLOT]; };
static In p2true[IR],p2used[IR]; static bool haveTrue[IR];
static BYTE* ring; static DWORD ringCap,ringBytes,ringFrame[RING];
static bool prepared; static DWORD prepFrame,nextFrame,realFrame,lastConfirmed,lastCompared,lastFrame,lastSeen;
static BYTE lastClock; static DWORD roundFrames; static DWORD stableDecor,stableFrames; static DWORD stableScene=0xFFFFFFFF,sceneFrames; static unsigned zoneLogs; static DWORD sZoneCross; static DWORD lastEvent;
static bool resim,rollbackPlanned; static DWORD resimEnd,rollbackTo;
static unsigned tickInUpdate; static bool advancedLast,advancedNow;
static volatile LONG extraNow,forget; static volatile LONG takeoverExtra;

static volatile LONG cutRest; static unsigned sCut,cutLogs; static DWORD sLockNext;

static DWORD replayCutAt,resimTarget; static unsigned sReplayCut,replayCutLogs;

static bool horlogeImage=false,clockOn; static float clockBase; static DWORD clockFrame0; static unsigned clockLogs;

static bool horlogeAbsolue=false;
static void PinClock(DWORD f){
    if(!clockOn)return;
    const float v=horlogeAbsolue?static_cast<float>(f)/60.0f:clockBase+static_cast<float>(static_cast<long>(f-clockFrame0))/60.0f;
    *reinterpret_cast<float*>(base+0xEDAA24)=v;*reinterpret_cast<float*>(base+0xEDAA34)=v;}
static DWORD prepApres1=250,roundNo;

static DWORD effHead[RING]; static bool effetsAnnules=false; static unsigned effLogs; static DWORD sEffKilled;

constexpr unsigned EFFMAX=160; static DWORD effSet[RING][EFFMAX]; static BYTE effN[RING];
static unsigned EffList(DWORD* out,unsigned cap){unsigned n=0,k=0;DWORD node=Read(base+0x206C514);while(node && k<1024){const DWORD e=Read(reinterpret_cast<void*>(node+8));if(e && n<cap)out[n++]=e;node=Read(reinterpret_cast<void*>(node));++k;}return n;}

static volatile LONG heapN; static DWORD heapList[16]; static bool heapBad[16]; static DWORD guetAbs,guetAbsDe,guetAbsA; static unsigned heapLogs;
static void HeapCheck(const char* when,DWORD x);

static unsigned timerLogs; static DWORD sTimerCut;
static void TimerCheck(const char* when,DWORD x);
static float speedAt[RING],slowAt[RING]; static bool ralentiRemis=true; static unsigned sSlowReset,slowLogs;

static DWORD slowReq[RING][3],slowDer[RING][2];

static DWORD sondeEcart=60;
static DWORD sondeAt,sondeAt2; static int sondePhase; static bool sondeNow; static DWORD sondeTarget;

static DWORD retoursForces,profForcee=4,sForces; static unsigned forceLogs;
static DWORD dernierEvt,sForcesEvites;
static unsigned evitesLogs;
static BYTE npAt[RING]; static DWORD sForcesNp; static unsigned npLogs;
static unsigned suiviLogs; static DWORD suiviRb[4],suiviRef[4]; static bool suiviVu;
static DWORD *sPgAddr,*sPgHash,sPgN; static DWORD *sDfAddr,sDfN; static BYTE* sDfCopy;
constexpr DWORD SONDE_PAGES=700000,SONDE_DIFF=4096;

static DWORD sondeOwnExtra[3];

static bool SondeScannable(const MEMORY_BASIC_INFORMATION& mi); static bool SondeOwn(DWORD a); static void SondeWhere(DWORD a,char* out,size_t n);
static DWORD sondeRefAt; static DWORD *srPg,*srBlk,srN,*srImg; static bool srHave; static BYTE* srNoise; static unsigned srPlay;
static bool SondeProche();
static DWORD BlkHash(const DWORD* p){DWORD h=2166136261u;for(int i=0;i<32;++i)h=(h^p[i])*16777619u;return h;}
static bool SrHashPage(DWORD a,DWORD* out){__try{for(int b=0;b<32;++b)out[b]=BlkHash(reinterpret_cast<const DWORD*>(a+b*128));return true;}__except(EXCEPTION_EXECUTE_HANDLER){return false;}}
static void SondeRefScan(bool reference,DWORD x){
    LARGE_INTEGER t0,t1,f;QueryPerformanceCounter(&t0);QueryPerformanceFrequency(&f);
    constexpr DWORD MAXP=400000;
    if(!srPg){srPg=static_cast<DWORD*>(VirtualAlloc(nullptr,MAXP*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));srBlk=static_cast<DWORD*>(VirtualAlloc(nullptr,MAXP*32*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));}
    if(!srPg || !srBlk){Logf("SONDE REF : memoire indisponible.");return;}
    if(!srNoise)srNoise=static_cast<BYTE*>(VirtualAlloc(nullptr,MAXP*32/8,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    const DWORD skip[]={reinterpret_cast<DWORD>(srPg),reinterpret_cast<DWORD>(srBlk),reinterpret_cast<DWORD>(ring),reinterpret_cast<DWORD>(refRaw),reinterpret_cast<DWORD>(refHash),sondeOwnExtra[0],sondeOwnExtra[1],sondeOwnExtra[2]};
    DWORD skipBase[8];for(int k=0;k<8;++k){MEMORY_BASIC_INFORMATION mi={};skipBase[k]=skip[k]&&VirtualQuery(reinterpret_cast<void*>(skip[k]),&mi,sizeof(mi))?reinterpret_cast<DWORD>(mi.AllocationBase):0;}
    DWORD a=0x10000;MEMORY_BASIC_INFORMATION mi;DWORD stacks[512];unsigned ns=0;DWORD n=0,diffBlk=0,diffPg=0,missing=0;unsigned logs=0;DWORD blk[32];
    if(!reference && !srImg)srImg=static_cast<DWORD*>(VirtualAlloc(nullptr,0x2200*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(srImg)memset(srImg,0,0x2200*4);
    while(a<0xFFFE0000 && VirtualQuery(reinterpret_cast<void*>(a),&mi,sizeof(mi))) {
        const DWORD rb=reinterpret_cast<DWORD>(mi.BaseAddress),re=rb+static_cast<DWORD>(mi.RegionSize),ab=reinterpret_cast<DWORD>(mi.AllocationBase);
        if(mi.State==MEM_COMMIT && (mi.Protect&PAGE_GUARD) && ns<512)stacks[ns++]=ab;
        bool bad=!SondeScannable(mi) || mi.Type==MEM_MAPPED;for(unsigned k=0;k<ns && !bad;++k)if(stacks[k]==ab)bad=true;for(int k=0;k<8 && !bad;++k)if(skipBase[k]==ab)bad=true;
        if(!bad)for(DWORD p=rb;p<re;p+=4096){
            if(SondeOwn(p))continue;
            if(reference){if(n>=MAXP)break;if(SrHashPage(p,srBlk+n*32)){srPg[n]=p;++n;}}
            else{

                DWORD lo=0,hi=srN;while(lo<hi){const DWORD mid=(lo+hi)/2;if(srPg[mid]<p)lo=mid+1;else hi=mid;}
                if(lo>=srN || srPg[lo]!=p){++missing;continue;}
                if(!SrHashPage(p,blk))continue;bool pd=false;
                for(int b=0;b<32;++b)if(blk[b]!=srBlk[lo*32+b]){
                    const DWORD bi=lo*32+b;
                    if(srPlay<=1){if(srNoise)srNoise[bi>>3]|=static_cast<BYTE>(1u<<(bi&7));++diffBlk;pd=true;continue;}
                    if(srNoise && (srNoise[bi>>3]>>(bi&7)&1))continue;
                    ++diffBlk;pd=true;

                    {const DWORD ad=p+b*128,gb=reinterpret_cast<DWORD>(base);
                     if(ad>=gb && ad<gb+0x21F8000){if(srImg)++srImg[(ad-gb)>>16];
                        static unsigned imgLogs;if(imgLogs<300){++imgLogs;char t[330];size_t ln=0;t[0]=0;const DWORD* q=reinterpret_cast<const DWORD*>(ad);
                            for(int k=0;k<32;++k){const int m=_snprintf_s(t+ln,sizeof(t)-ln,_TRUNCATE," %08lX",q[k]);if(m>0)ln+=m;}
                            Logf("SONDE REF image game+%06lX :%s.",ad-gb,t);}}
                     else if(logs<400){++logs;char w[200];SondeWhere(ad,w,sizeof w);char ob[96]="";DWORD o=0,d=0;
                        if(cp::Describe(ad,o,d) && o){const DWORD v=Read(reinterpret_cast<void*>(o));_snprintf_s(ob,sizeof ob,_TRUNCATE," ; objet %08lX table %06lX +%lX",o,cp::InRdata(v)?v-gb:v,ad-o);}
                        char t[330];size_t ln=0;t[0]=0;const DWORD* q=reinterpret_cast<const DWORD*>(ad);
                        for(int k=0;k<32;++k){const int m=_snprintf_s(t+ln,sizeof(t)-ln,_TRUNCATE," %08lX",q[k]);if(m>0)ln+=m;}
                        Logf("SONDE REF bloc %s%s :%s.",w,ob,t);}}}
                if(pd)++diffPg;
            }}
        if(re<=a)break;a=re;}
    QueryPerformanceCounter(&t1);
    if(!reference && srPlay>1 && srImg){for(int r=0;r<30;++r){DWORD best=0,bi=0;for(DWORD i=0;i<0x2200;++i)if(srImg[i]>best){best=srImg[i];bi=i;}
        if(!best)break;Logf("SONDE REF image du jeu game+%06lX (64 Ko) : %lu bloc(s) differents.",bi<<16,best);srImg[bi]=0;}}
    if(reference){srN=n;srHave=true;srPlay=0;if(srNoise)memset(srNoise,0,MAXP*32/8);Logf("SONDE REF : reference de l'image %lu : %lu page(s) relevee(s) en %.0f ms.",x,n,(t1.QuadPart-t0.QuadPart)*1000.0/f.QuadPart);}
    else Logf(srPlay<=1?"SONDE REF (passe de BRUIT, sans prediction) : image %lu : %lu bloc(s) de 128 octets differents":"SONDE REF (passe avec prediction, bruit retire) : image %lu confirmee : %lu bloc(s) de 128 octets differents dans %lu page(s) ; %lu page(s) absentes de la reference ; %.0f ms.",x,diffBlk,diffPg,missing,(t1.QuadPart-t0.QuadPart)*1000.0/f.QuadPart);
}
static bool sondeAuto,autoReprepDone; static unsigned sondeMoitie; static DWORD autoRng[512][2]; static unsigned autoN; static bool autoArmed; static DWORD autoVerdictAt;
static DWORD PageHash(const DWORD* p){DWORD h=2166136261u;for(int i=0;i<1024;++i)h=(h^p[i])*16777619u;return h;}
static bool SondeOwn(DWORD a){
    auto in=[a](const void* b,SIZE_T n){const DWORD s=reinterpret_cast<DWORD>(b);return b && a>=s && a<s+n;};
    {const NT_TIB* tib=reinterpret_cast<const NT_TIB*>(NtCurrentTeb());const DWORD lo=reinterpret_cast<DWORD>(tib->StackLimit),hi=reinterpret_cast<DWORD>(tib->StackBase);
     if(a+4096>lo-0x100000 && a<hi)return true;}
    return in(sPgAddr,SONDE_PAGES*4) || in(sPgHash,SONDE_PAGES*4) || in(sDfAddr,SONDE_DIFF*4) || in(sDfCopy,SONDE_DIFF*4096);}
static bool SondeScannable(const MEMORY_BASIC_INFORMATION& mi){
    if(mi.State!=MEM_COMMIT || (mi.Protect&(PAGE_GUARD|PAGE_NOCACHE|PAGE_WRITECOMBINE)))return false;
    const DWORD pr=mi.Protect&0xFF;return pr==PAGE_READWRITE || pr==PAGE_WRITECOPY || pr==PAGE_EXECUTE_READWRITE || pr==PAGE_EXECUTE_WRITECOPY;}
static bool SondeHash(DWORD a,DWORD& h){__try{h=PageHash(reinterpret_cast<const DWORD*>(a));return true;}__except(EXCEPTION_EXECUTE_HANDLER){return false;}}
static bool SondeCopy(BYTE* d,DWORD a){__try{memcpy(d,reinterpret_cast<const void*>(a),4096);return true;}__except(EXCEPTION_EXECUTE_HANDLER){return false;}}
static void SondeWhere(DWORD a,char* out,size_t n){
    MEMORY_BASIC_INFORMATION mi={};VirtualQuery(reinterpret_cast<void*>(a),&mi,sizeof(mi));
    const DWORD ab=reinterpret_cast<DWORD>(mi.AllocationBase);
    if(ab==reinterpret_cast<DWORD>(base)){_snprintf_s(out,n,_TRUNCATE,"game+%06lX",a-ab);return;}
    char name[MAX_PATH]="";
    if(mi.Type==MEM_IMAGE && GetModuleFileNameA(reinterpret_cast<HMODULE>(ab),name,MAX_PATH)){const char* b=strrchr(name,'\\');_snprintf_s(out,n,_TRUNCATE,"%s+%lX",b?b+1:name,a-ab);return;}
    _snprintf_s(out,n,_TRUNCATE,"%08lX (alloc %08lX +%lX, %s)",a,ab,a-ab,mi.Type==MEM_PRIVATE?"prive":mi.Type==MEM_MAPPED?"mappe":"image");}
static void SondeBefore() {
    LARGE_INTEGER t0,t1,f;QueryPerformanceCounter(&t0);QueryPerformanceFrequency(&f);
    if(sondePhase==1) {
        if(!sPgAddr){sPgAddr=static_cast<DWORD*>(VirtualAlloc(nullptr,SONDE_PAGES*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));sPgHash=static_cast<DWORD*>(VirtualAlloc(nullptr,SONDE_PAGES*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));}
        if(!sDfAddr){sDfAddr=static_cast<DWORD*>(VirtualAlloc(nullptr,SONDE_DIFF*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));sDfCopy=static_cast<BYTE*>(VirtualAlloc(nullptr,SONDE_DIFF*4096,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));}
        if(!sPgAddr || !sPgHash || !sDfAddr || !sDfCopy){Logf("SONDE : memoire indisponible.");sondePhase=0;return;}
        sPgN=0;DWORD a=0x10000;MEMORY_BASIC_INFORMATION mi;DWORD stacks[512];unsigned ns=0,skipped=0;
        while(a<0xFFFE0000 && VirtualQuery(reinterpret_cast<void*>(a),&mi,sizeof(mi))) {
            const DWORD rb=reinterpret_cast<DWORD>(mi.BaseAddress),re=rb+static_cast<DWORD>(mi.RegionSize);
            const DWORD ab=reinterpret_cast<DWORD>(mi.AllocationBase);
            if(mi.State==MEM_COMMIT && (mi.Protect&PAGE_GUARD) && ns<512)stacks[ns++]=ab;
            bool stack=false;for(unsigned k=0;k<ns;++k)if(stacks[k]==ab)stack=true;
            if(stack && SondeScannable(mi)){skipped+=static_cast<DWORD>(mi.RegionSize)/4096;}
            else if(SondeScannable(mi))for(DWORD p=rb;p<re && sPgN<SONDE_PAGES;p+=4096){if(SondeOwn(p))continue;DWORD h;if(SondeHash(p,h)){sPgAddr[sPgN]=p;sPgHash[sPgN]=h;++sPgN;}}
            if(re<=a)break;a=re;}
        Logf("SONDE : %u pile(s) ecartee(s) (%u page(s)).",ns,skipped);
    } else {
        for(DWORD i=0;i<sDfN;++i)if(!SondeCopy(sDfCopy+i*4096,sDfAddr[i]))sDfAddr[i]=0;
    }
    QueryPerformanceCounter(&t1);
    Logf("SONDE phase %d image %lu : %lu page(s) relevee(s) avant la remise en %.0f ms (ring %08lX, refRaw %08lX).",sondePhase,sondeTarget,
        sondePhase==1?sPgN:sDfN,(t1.QuadPart-t0.QuadPart)*1000.0/f.QuadPart,reinterpret_cast<DWORD>(ring),reinterpret_cast<DWORD>(refRaw));
}
static void SondeAfter() {
    char w[200];
    if(sondePhase==1) {
        sDfN=0;unsigned logs=0;
        for(DWORD i=0;i<sPgN;++i){DWORD h;if(!SondeHash(sPgAddr[i],h) || h==sPgHash[i])continue;
            if(sDfN<SONDE_DIFF)sDfAddr[sDfN++]=sPgAddr[i];
            if(logs<400){++logs;SondeWhere(sPgAddr[i],w,sizeof(w));Logf("SONDE page differente apres recalcul : %s.",w);}}
        Logf("SONDE phase 1 : %lu page(s) differente(s) sur %lu ; phase 2 a l'image %lu.",sDfN,sPgN,sondeTarget+sondeEcart);
        {bool j1=false;const DWORD pj=reinterpret_cast<DWORD>(base)+0xFD0000;for(DWORD i=0;i<sDfN;++i)if(sDfAddr[i]==pj)j1=true;
         Logf("SONDE : position du J1 (page game+FD0000) %s apres le recalcul a entrees egales%s.",j1?"DIFFERENTE":"IDENTIQUE",autoVerdictAt?" (APRES ajout automatique des pages)":"");}
        if(sondeAuto && !autoVerdictAt) {
            const DWORD own[]={reinterpret_cast<DWORD>(ring),reinterpret_cast<DWORD>(refRaw),sondeOwnExtra[0],sondeOwnExtra[1],
                sondeOwnExtra[2],reinterpret_cast<DWORD>(refHash),reinterpret_cast<DWORD>(sPgAddr),reinterpret_cast<DWORD>(sPgHash),reinterpret_cast<DWORD>(sDfAddr),reinterpret_cast<DWORD>(sDfCopy)};
            DWORD ownBase[10];for(int k=0;k<10;++k){MEMORY_BASIC_INFORMATION mi={};ownBase[k]=own[k]&&VirtualQuery(reinterpret_cast<void*>(own[k]),&mi,sizeof(mi))?reinterpret_cast<DWORD>(mi.AllocationBase):0;}
            DWORD cand[SONDE_DIFF];unsigned nc=0;
            for(DWORD i=0;i<sDfN;++i){MEMORY_BASIC_INFORMATION mi={};if(!VirtualQuery(reinterpret_cast<void*>(sDfAddr[i]),&mi,sizeof(mi)) || mi.Type!=MEM_PRIVATE)continue;
                const DWORD ab=reinterpret_cast<DWORD>(mi.AllocationBase);bool mine=false;for(int k=0;k<10;++k)if(ownBase[k]==ab)mine=true;if(mine)continue;cand[nc++]=sDfAddr[i];}
            unsigned from=0,to=nc;if(sondeMoitie==1)to=nc/2;else if(sondeMoitie==2)from=nc/2;
            autoN=0;for(unsigned i=from;i<to && autoN<512;++i){if(autoN && autoRng[autoN-1][1]==cand[i]){autoRng[autoN-1][1]+=4096;continue;}autoRng[autoN][0]=cand[i];autoRng[autoN][1]=cand[i]+4096;++autoN;}
            Logf("SONDE AUTO : %u page(s) du tas candidates, %u retenue(s) (moitie %u) en %u plage(s) : re-preparation avec ces plages.",nc,to-from,sondeMoitie,autoN);
            autoArmed=true;autoVerdictAt=sondeTarget+120;
        }
        else if(sondeAuto && autoVerdictAt)autoArmed=false;
        sondePhase=2;sondeTarget+=sondeEcart;
    } else {
        unsigned logs=0,pages=0;
        for(DWORD i=0;i<sDfN;++i){if(!sDfAddr[i])continue;const DWORD* before=reinterpret_cast<const DWORD*>(sDfCopy+i*4096);DWORD after[1024];
            if(!SondeCopy(reinterpret_cast<BYTE*>(after),sDfAddr[i]))continue;
            unsigned n=0;for(int k=0;k<1024;++k)if(before[k]!=after[k])++n;
            if(!n)continue;++pages;
            {DWORD fk=0;for(int k=0;k<1024;++k)if(before[k]!=after[k]){fk=k;break;}const DWORD a=sDfAddr[i]+fk*4;
             const LONG hn=heapN<16?heapN:16;for(LONG h=0;h<hn;++h){const DWORD hp=heapList[h];if(!hp)continue;
                __try{const DWORD H=*reinterpret_cast<const DWORD*>(hp+0xC),lo=*reinterpret_cast<const DWORD*>(hp+0x14),hi=*reinterpret_cast<const DWORD*>(hp+0x18);if(a<lo || a>=hi || H>0x40)continue;
                    DWORD b=lo;unsigned it=0;while(b<hi && it<2000000){const LONG sz=*reinterpret_cast<const LONG*>(b+4);const DWORD asz=static_cast<DWORD>(sz<0?-sz:sz);
                        if(a<b+H+asz){const DWORD pl=b+H,t=*reinterpret_cast<const DWORD*>(pl);char tn[32];if(t>=reinterpret_cast<DWORD>(base) && t<reinterpret_cast<DWORD>(base)+0x21F8000)_snprintf_s(tn,sizeof tn,_TRUNCATE,"game+%06lX",t-reinterpret_cast<DWORD>(base));else _snprintf_s(tn,sizeof tn,_TRUNCATE,"%08lX",t);
                            Logf("SONDE proprietaire de %08lX : bloc %08lX (+%lX) de 0x%lX octets %s (tas %ld), 1er mot %s, suivants %08lX %08lX %08lX.",a,pl,a-pl,asz,sz<0?"occupe":"LIBRE",h,tn,*reinterpret_cast<const DWORD*>(pl+4),*reinterpret_cast<const DWORD*>(pl+8),*reinterpret_cast<const DWORD*>(pl+12));
                            if(asz==0xD0 && sz<0 && !guetAbs){guetAbs=a;guetAbsDe=sondeTarget+1;guetAbsA=sondeTarget+2;Logf("SONDE : guet materiel arme sur %08lX (noeud de 0xD0), images %lu a %lu.",a,guetAbsDe,guetAbsA);}break;}
                        b+=H+asz;++it;}
                }__except(EXCEPTION_EXECUTE_HANDLER){}}}
            unsigned perPage=0;
            for(int k=0;k<1024 && logs<3000 && perPage<12;++k)if(before[k]!=after[k]){++logs;++perPage;const DWORD a=sDfAddr[i]+k*4;SondeWhere(a,w,sizeof(w));
                float fb,fa;memcpy(&fb,&before[k],4);memcpy(&fa,&after[k],4);
                Logf("SONDE mot %s : avant %08lX apres %08lX (flottants %g / %g ; %u mot(s) differents dans la page).",w,before[k],after[k],fb,fa,n);}}
        Logf("SONDE phase 2 : %u page(s) encore differente(s) ; fin de la sonde%s.",pages,sondeAt2 && sondeTarget<sondeAt2?" (2e sonde a venir)":" pour cette lecture");
        sondePhase=3;if(sondeAt2 && sondeTarget<sondeAt2){sondePhase=1;sondeTarget=sondeAt2;}
        if(autoArmed){sondePhase=1;sondeTarget=autoVerdictAt;}
    }
}

constexpr unsigned SEQMAX=16;
static DWORD seqNode[256][SEQMAX]; static BYTE seqCount[256]; static unsigned sSeqKilled,seqLogs;
static unsigned SeqList(DWORD* out) {
    const DWORD mgr=Read(base+0xFCE348);if(!mgr)return 0;
    const DWORD head=Read(reinterpret_cast<void*>(mgr+0x10));if(!head)return 0;
    unsigned n=0;DWORD node=Read(reinterpret_cast<void*>(head));
    while(node && node!=head && n<SEQMAX){out[n++]=node;node=Read(reinterpret_cast<void*>(node));}
    return n;
}
static DWORD hashAt[IR][MAXCORE]; static BYTE rawAt[IR][RAWSZ];
static const char* lastReason;
static DWORD refDecor[REF_FRAMES],decorAt[IR];
struct DecorComp { DWORD component,owner,descriptor,length; BYTE data[64]; };
struct DecorState { DWORD scene; unsigned n; DecorComp c[4]; };
static DecorState decorRing[RING];
static bool rebuildOk;
static DWORD sDecorRestored; static DWORD scanAge;
static DWORD structAt[IR]; static DWORD sStateOnly; static DWORD sDecorCross,sDecorBad; static unsigned decorLogs;
static DWORD blockedAt,eventBlockedAt; static DWORD sEvReplayed,sEvBlocked;
static DWORD sKoBlocked,sKoReplayed;

constexpr DWORD STAGEMAX=0x2000;
static DWORD stageComp,stageAddr,stageSize; static BYTE *refStage,*stageRing; static BYTE stageMask[STAGEMAX/4];

static DWORD essaiPerm[32],sansRemise[32]; static unsigned nEssaiPerm,nSansRemise;

static DWORD margeCourteZ[32],margeCourte=30; static unsigned nMargeCourte;
static DWORD SceneVt(){const DWORD mgr=Read(base+0x2072580);if(!mgr)return 0;const DWORD o=Read(reinterpret_cast<void*>(mgr+0xC));
    return o?Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base):0;}

static DWORD ZoneFamily(DWORD vt){if(vt<0x2200000)return 0;const DWORD b0=reinterpret_cast<DWORD>(base);const DWORD col=Read(reinterpret_cast<void*>(vt+b0-4));
    return (col>b0+0x966000 && col<b0+0x2094000)?(0x10000000u|(col-b0)):0;}
static bool InList(const DWORD* l,unsigned n,DWORD v){const DWORD k=ZoneFamily(v);for(unsigned i=0;i<n;++i)if(l[i]==v || (k && l[i]==k))return true;return false;}

static DWORD physZones[32]; static unsigned nPhysZones; static bool physWait=true;
static bool PhysZone(){const DWORD vt=SceneVt();return vt==0xBF9A20 || (nPhysZones && InList(physZones,nPhysZones,vt));}
static bool restoreStage=true; static DWORD sStageBad,sStageWords,sStageSkipped,sStageRestores,sStructSkip,sStructSeen; static unsigned stageLogs,skipLogs;
static DWORD stageHits[STAGEMAX/4];
static unsigned evLogs;
typedef void(__cdecl* SceneFrameFn)(float);
static bool sceneFrameOk,sceneSteps=true; static float lastDt,lastSpeed=1.0f; static unsigned speedLogs; static DWORD sSceneCalls; static bool fightNow,sceneDone; static DWORD lastMult=1; static unsigned multLogs;
static void SceneFrame() {
    if(!sceneFrameOk || !sceneSteps)return;

    float speed=*reinterpret_cast<const float*>(base+0xD2EA10);
    if(!(speed>0.0f && speed<=4.0f))speed=1.0f;
    float slow=*reinterpret_cast<const float*>(base+0xF9CEC0);
    if(!(slow>=0.0f && slow<=4.0f))slow=1.0f;
    speed*=slow;

    {const DWORD iMode=Read(base+0x108B490);if(iMode<4){const DWORD mode=Read(base+0x108B448+iMode*16);
        if(mode<16){const DWORD mult=Read(base+0x9C1DB4+mode*12);if(mult>=1 && mult<=4){speed*=static_cast<float>(mult);
            if(mult!=lastMult && multLogs<40){++multLogs;Logf("Scene : multiple de pas du jeu %lu (mode %lu) applique a la scene par pas (lab173f).",mult,mode);}lastMult=mult;}}}}
    if(speed!=lastSpeed && speedLogs<60){++speedLogs;Logf("Scene : ralenti %.4f (vitesse du jeu x facteur) suivi par la scene.",speed);}
    lastSpeed=speed;
    TimerCheck("avant la scene",lastFrame+1);
    __try{reinterpret_cast<SceneFrameFn>(base+0x597AA0)(speed);++sSceneCalls;}__except(EXCEPTION_EXECUTE_HANDLER){}
}

static DWORD sUpdates,sTicks,sRollbacks,sDepth,sDepthMax,sPred,sMiss,sOk,sBadCore,sBadRaw,sSkip; static DWORD sRoundObjKept; static BYTE roundFlagLast; static DWORD roundFlagAt; static double sMs,sMaxMs;
static unsigned badLogs; static LARGE_INTEGER qpf,updateStart; static DWORD lastReport;
static DWORD tOk,tBad,tRollbacks,firstBad;

static BYTE* Slot(int p){return base+SLOTS+p*SLOT;}
static unsigned K(DWORD f){return f%IR;}
static BYTE* Ring(DWORD f){return ring+(f%RING)*ringBytes;}
static DWORD safeUntil,confFloor,safeFrames=600,sSafeFrames; static unsigned safeLogs;

static DWORD sFight,sNp[7],tFight,tNp[7];

static bool finDetectee=false; static DWORD stableNeed=30;
static bool finApresBascule=false;

static bool sceneHorsExe=false;
static bool winOpen; static DWORD winStart,winLastAct,winOrigin,winCnt[5];
static DWORD sWinCount,sWinSum,sWinMax,sWinEarly,sWinSaved; static unsigned winLogs;
static unsigned ActiveSeqs(){const DWORD mgr=Read(base+0xFCE348);if(!mgr)return 0;const DWORD head=Read(reinterpret_cast<void*>(mgr+0x10));if(!head)return 0;
    unsigned n=0,g=0;DWORD node=Read(reinterpret_cast<void*>(head));
    while(node && node!=head && g<16){BYTE a=0;Copy(&a,reinterpret_cast<void*>(node+0xC),1);if(a)++n;node=Read(reinterpret_cast<void*>(node));++g;}
    return n;}
static void WinOpen(DWORD x,DWORD origin){if(!winOpen){winOpen=true;winStart=x;winOrigin=origin;for(DWORD& c:winCnt)c=0;}winLastAct=x;}

static DWORD ambFrames,ambCnt[5]; static unsigned ambMask,curSig,ambLogs; static bool ambiantOn=true;
static const char* const SIG_NOMS[5]={"decor","structure","zone","pointeur","sequence"};
static DWORD prepRetry,prepFails; static volatile LONG updateCount; static bool noUpdateLogged;

static bool predictionCourHome=true;
static bool predictionHotZone=true;
static bool predictionHautFlow=false;
static bool NoPredictStage(){
    const DWORD mgr=Read(base+0x2072580);if(!mgr)return false;
    const DWORD o=Read(reinterpret_cast<void*>(mgr+0xC));
    if(!o)return false;const DWORD vt=Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base);

    return (vt==0xBEC570 && !predictionHotZone) || (vt==0xBF3090 && !predictionCourHome) || (vt==0xBF48D0 && !predictionHautFlow);}

static bool PermanentZone(){
    const DWORD mgr=Read(base+0x2072580);if(!mgr)return false;
    const DWORD o=Read(reinterpret_cast<void*>(mgr+0xC));
    if(!o)return false;const DWORD vt=Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base);
    switch(vt){
        case 0x9A8990:
        case 0x9AFD64:
        case 0x97ABAC:
        case 0x9A02C0:
        case 0x9A4244:
        case 0x97C824:
        case 0x9A3F88:
        case 0xBEAD20:
        case 0x9A0C8C:
        case 0x97B954:
        case 0xBF6A5C:
        case 0x9AA394:
        case 0xBFF00C:

        case 0xBF58BC:
        case 0x980170:
        case 0xBEC570:

            return true;
    }
    return nEssaiPerm && InList(essaiPerm,nEssaiPerm,vt);}
static DWORD WinLen(){return PermanentZone()?0:safeFrames;}

static bool FixedWindowZone(){
    const DWORD mgr=Read(base+0x2072580);if(!mgr)return false;
    const DWORD o=Read(reinterpret_cast<void*>(mgr+0xC));
    if(!o)return false;const DWORD vt=Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base);
    return vt==0xBF7A24 || vt==0xBF9A20;}

static bool CinematicNow(){
    const float sp=*reinterpret_cast<const float*>(base+0xD2EA10),sl=*reinterpret_cast<const float*>(base+0xF9CEC0);
    return (sp<0.999f || sp>1.001f) || (sl<0.999f || sl>1.001f);
}

static DWORD cineLast;

static DWORD CINE_TAIL=90;

static bool KitZone(){const DWORD vt=SceneVt();return nEssaiPerm && InList(essaiPerm,nEssaiPerm,vt) && vt!=0xBF7A24 && vt!=0xBF9A20;}
static bool SeqGuardZone(){return FixedWindowZone() || KitZone();}
static bool predictionSequences=false;

static bool Speculative(){const DWORD f=static_cast<DWORD>(sc::ctxFrame);return sc::gate!=0 || (eventBlockedAt && eventBlockedAt<f) || (blockedAt && blockedAt<f);}
static bool SeqActiveNow(){DWORD n[SEQMAX];const unsigned c=SeqList(n);for(unsigned i=0;i<c;++i){BYTE a=0;Copy(&a,reinterpret_cast<void*>(n[i]+0xC),1);if(a)return true;}return false;}
static DWORD qNode[RING][2][8]; static BYTE qN[RING][2]; static DWORD sQueueRemoved; static unsigned queueLogs;
static unsigned QueueList(int w,DWORD* out){const DWORD head=Read(base+(w?0xFD14C8:0xFD14BC));if(!head)return 0;unsigned n=0;DWORD node=Read(reinterpret_cast<void*>(head));while(node && node!=head && n<8){out[n++]=node;node=Read(reinterpret_cast<void*>(node));}return n;}
static void QueueSave(DWORD x){for(int w=0;w<2;++w)qN[x%RING][w]=static_cast<BYTE>(QueueList(w,qNode[x%RING][w]));}
static void QueueRestore(DWORD r,DWORD x){
    for(int w=0;w<2;++w){DWORD now[8];const unsigned n=QueueList(w,now);
        for(unsigned i=0;i<n;++i){bool was=false;for(unsigned k=0;k<qN[r%RING][w];++k)if(qNode[r%RING][w][k]==now[i])was=true;if(was)continue;
            __try{const DWORD nd=now[i],nx=*reinterpret_cast<DWORD*>(nd),pv=*reinterpret_cast<DWORD*>(nd+4);*reinterpret_cast<DWORD*>(pv)=nx;*reinterpret_cast<DWORD*>(nx+4)=pv;
                --*reinterpret_cast<DWORD*>(base+(w?0xFD14CC:0xFD14C0));reinterpret_cast<void(__cdecl*)(void*)>(base+0x85B14B)(reinterpret_cast<void*>(nd));}__except(EXCEPTION_EXECUTE_HANDLER){continue;}
            ++sQueueRemoved;if(queueLogs<30){++queueLogs;Logf("Labo DEMANDES : retour %lu -> %lu : demande de cinematique deposee dans une image annulee retiree (file %d).",x,r,w+1);}}}
}

static DWORD smPtr[RING],snPtr[RING][SEQMAX]; static BYTE snN[RING],smData[RING][0x30],snData[RING][SEQMAX][0x60]; static DWORD sSeqRestored,sSeqNodesRestored; static unsigned seqRestLogs;
static bool SeqPhotoOn(){return predictionSequences && SeqGuardZone();}
static void SeqSave(DWORD x){
    smPtr[x%RING]=0;snN[x%RING]=0;if(!SeqPhotoOn())return;
    const DWORD mgr=Read(base+0xFCE348);if(!mgr || !Copy(smData[x%RING],reinterpret_cast<void*>(mgr),0x30))return;
    DWORD n[SEQMAX];const unsigned c=SeqList(n);unsigned k=0;
    for(unsigned i=0;i<c;++i)if(Copy(snData[x%RING][k],reinterpret_cast<void*>(n[i]+8),0x60))snPtr[x%RING][k++]=n[i];
    snN[x%RING]=static_cast<BYTE>(k);smPtr[x%RING]=mgr;
}
static void SeqRestore(DWORD r,DWORD x){
    if(!SeqPhotoOn())return;const DWORD mgr=Read(base+0xFCE348);
    if(!mgr || smPtr[r%RING]!=mgr){if(seqRestLogs<20){++seqRestLogs;Logf("Labo SEQUENCES : retour %lu -> %lu : gestionnaire %08lX absent de la photo (%08lX) : non remis.",x,r,mgr,smPtr[r%RING]);}return;}
    DWORD now[SEQMAX];const unsigned c=SeqList(now);unsigned back=0,missing=0;
    for(unsigned k=0;k<snN[r%RING];++k){bool here=false;for(unsigned i=0;i<c;++i)if(now[i]==snPtr[r%RING][k])here=true;
        if(!here){++missing;continue;}
        __try{memcpy(reinterpret_cast<void*>(snPtr[r%RING][k]+8),snData[r%RING][k],0x60);++back;}__except(EXCEPTION_EXECUTE_HANDLER){}}
    __try{const DWORD head=*reinterpret_cast<const DWORD*>(mgr+0x10),cnt=*reinterpret_cast<const DWORD*>(mgr+0x14);
        memcpy(reinterpret_cast<void*>(mgr),smData[r%RING],0x30);*reinterpret_cast<DWORD*>(mgr+0x10)=head;*reinterpret_cast<DWORD*>(mgr+0x14)=cnt;}__except(EXCEPTION_EXECUTE_HANDLER){}
    ++sSeqRestored;sSeqNodesRestored+=back;
    if((missing || seqRestLogs<6) && seqRestLogs<30){++seqRestLogs;Logf("Labo SEQUENCES : retour %lu -> %lu : gestionnaire remis, %u noeud(s) remis, %u ABSENT(S) (supprime(s) depuis), %u dans la liste.",x,r,back,missing,c);}
}

static bool Engagee(DWORD v,bool privee);
constexpr unsigned POSECTL=4; constexpr DWORD POSEBUF=0x10000;
static DWORD poseCtl[POSECTL],posePrev[POSECTL][8]; static unsigned nPoseCtl; static bool poseDyn=true;
static BYTE* poseRing; static DWORD poseLen[RING],poseFrame[RING]; static DWORD sPoseRestored,sPoseChanges,sPoseBytes; static unsigned poseLogs,poseRestLogs;
static DWORD sPoseOverflow; static bool poseOverflowLogged;
static void PoseAdd(BYTE*& o,const BYTE* end,DWORD a,DWORD n){
    if(a<0x10000 || !n)return;
    if(o+8+n>end){++sPoseOverflow;return;}
    if(!Engagee(a,true))return;
    __try{memcpy(o+8,reinterpret_cast<const void*>(a),n);}__except(EXCEPTION_EXECUTE_HANDLER){return;}
    memcpy(o,&a,4);memcpy(o+4,&n,4);o+=8+n;}

static DWORD poseVal[RING][POSECTL][4],poseValFrame[RING],poseScene[RING][2],poseMots[RING][2]; static DWORD flowSuiviDe,flowSuiviA; static unsigned flowSuiviLignes;
static void FlowSuiviArme(DWORD x,const char* pourquoi){
    if(!kTest || SceneVt()!=0xBF48D0 || flowSuiviLignes>=12000)return;
    const bool dedans=flowSuiviA && x>=flowSuiviDe && x<=flowSuiviA;if(!dedans)flowSuiviDe=x;flowSuiviA=x+240;
    Logf("FLOW SUIVI : %s a l'image %lu : positions et radeau notes a chaque image confirmee jusqu'a l'image %lu.",pourquoi,x,flowSuiviA);}
static void FlowSuivi(DWORD j){
    if(!kTest || !flowSuiviA || j<flowSuiviDe || j>flowSuiviA || flowSuiviLignes>=12000 || poseValFrame[j%RING]!=j)return;
    const BYTE* r=rawAt[K(j)];DWORD w[6];memcpy(w,r+0xC,12);memcpy(w+3,r+0x6D4,12);
    char t[700];size_t n=0;auto ad=[&](const char* f,DWORD v){const int k=_snprintf_s(t+n,sizeof(t)-n,_TRUNCATE,f,v>>16,v&0xFFFF);if(k>0)n+=k;};
    t[0]=0;for(int k=0;k<6;++k)ad(k==3?" ; J2 %04lX.%04lX":k==0?"J1 %04lX.%04lX":" %04lX.%04lX",w[k]);
    ad(" ; scene %04lX.%04lX",poseScene[j%RING][0]);ad(" %04lX.%04lX",poseScene[j%RING][1]);
    {const int k=_snprintf_s(t+n,sizeof(t)-n,_TRUNCATE," ; mots +8C..+10C : %lu non nul(s)",poseMots[j%RING][0]);if(k>0)n+=k;}ad(" empreinte %04lX.%04lX",poseMots[j%RING][1]);
    for(unsigned i=0;i<nPoseCtl;++i){const int k=_snprintf_s(t+n,sizeof(t)-n,_TRUNCATE," ; c%u",i);if(k>0)n+=k;for(int m=0;m<4;++m)ad(" %04lX.%04lX",poseVal[j%RING][i][m]);}
    ++flowSuiviLignes;Logf("FLOW SUIVI image %lu : %s.",j,t);
    if(j==flowSuiviA)flowSuiviA=0;}
static void PoseSave(DWORD x){
    if(kTest && nPoseCtl){poseValFrame[x%RING]=x;
        for(unsigned i=0;i<nPoseCtl;++i){const DWORD c=poseCtl[i];poseVal[x%RING][i][0]=Read(reinterpret_cast<void*>(c+0x140));poseVal[x%RING][i][1]=Read(reinterpret_cast<void*>(c+0x114));
            poseVal[x%RING][i][2]=Read(reinterpret_cast<void*>(c+0xB4));poseVal[x%RING][i][3]=Read(reinterpret_cast<void*>(c+0xC0));}
        const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;
        poseScene[x%RING][0]=o?Read(reinterpret_cast<void*>(o+0x198)):0;poseScene[x%RING][1]=o?Read(reinterpret_cast<void*>(o+0x1A0)):0;
        {DWORD m[33]={};if(o)Copy(m,reinterpret_cast<void*>(o+0x8C),sizeof m);DWORD nz=0,h=2166136261u;for(DWORD v:m){if(v)++nz;h=(h^v)*16777619u;}
         poseMots[x%RING][0]=nz;poseMots[x%RING][1]=h;}}
    poseLen[x%RING]=0;poseFrame[x%RING]=0xFFFFFFFF;if(!nPoseCtl)return;
    BYTE* b=nullptr;
    if(poseDyn){if(!poseRing)poseRing=static_cast<BYTE*>(VirtualAlloc(nullptr,static_cast<SIZE_T>(RING)*POSEBUF,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));if(poseRing)b=poseRing+static_cast<SIZE_T>(x%RING)*POSEBUF;}
    BYTE* o=b;const BYTE* end=b?b+POSEBUF:nullptr;
    static const DWORD offs[8]={0x9C,0xA0,0xA4,0x5C,0x60,0x64,0x68,0xC0};
    for(unsigned i=0;i<nPoseCtl;++i){const DWORD c=poseCtl[i];DWORD p[8];for(int k=0;k<8;++k)p[k]=Read(reinterpret_cast<void*>(c+offs[k]));
        DWORD q[8],v[8];memcpy(q,p,sizeof q);memcpy(v,posePrev[i],sizeof v);q[3]=q[4]=q[5]=q[6]=v[3]=v[4]=v[5]=v[6]=0;    for(int u=4;u<7;++u)for(int w=u;w>3 && q[w-1]>q[w];--w){const DWORD t=q[w];q[w]=q[w-1];q[w-1]=t;}for(int u=4;u<7;++u)for(int w=u;w>3 && v[w-1]>v[w];--w){const DWORD t=v[w];v[w]=v[w-1];v[w-1]=t;}
        if(memcmp(q,v,sizeof q)){++sPoseChanges;
            if(poseLogs<40){++poseLogs;Logf("Labo POSES : controleur %u image %lu : pointeurs pistes %08lX %08lX %08lX, emplacements %08lX %08lX %08lX %08lX, clip %08lX (avant %08lX %08lX %08lX, %08lX %08lX %08lX %08lX, %08lX).",
                i,x,p[0],p[1],p[2],p[3],p[4],p[5],p[6],p[7],posePrev[i][0],posePrev[i][1],posePrev[i][2],posePrev[i][3],posePrev[i][4],posePrev[i][5],posePrev[i][6],posePrev[i][7]);}
            }
        memcpy(posePrev[i],p,sizeof p);
        if(!b)continue;
        const DWORD np=Read(reinterpret_cast<void*>(c+0xA8)),nb=Read(reinterpret_cast<void*>(c+0xE8)),md=Read(reinterpret_cast<void*>(c+0xBC));
        if(np && np<=256)for(int k=0;k<3;++k)PoseAdd(o,end,p[k],np*0x88);
        DWORD vus[4];unsigned nv=0;
        for(int k=3;k<7;++k){const DWORD sl=p[k];bool dup=false;for(unsigned u=0;u<nv;++u)if(vus[u]==sl)dup=true;if(dup || sl<0x10000)continue;vus[nv++]=sl;
            PoseAdd(o,end,sl,0x10);
            if(nb && nb<=256)for(DWORD a=0;a<3;++a){const DWORD t=Read(reinterpret_cast<void*>(sl+a*4));PoseAdd(o,end,t,(a==0 && (md==0 || md==1 || md==3))?0x10:nb*0x10);}}
    }
    if(b){poseLen[x%RING]=static_cast<DWORD>(o-b);poseFrame[x%RING]=x;if(poseLen[x%RING]>sPoseBytes)sPoseBytes=poseLen[x%RING];}
    if(sPoseOverflow && !poseOverflowLogged){poseOverflowLogged=true;
        Logf("Labo POSES : image %lu : tampon de 0x%lX octets plein, %lu bloc(s) non photographie(s) (jamais remis aux retours) : agrandir POSEBUF.",x,POSEBUF,sPoseOverflow);}
}
static void PoseRestore(DWORD r,DWORD x){
    if(!poseDyn || !poseRing || poseFrame[r%RING]!=r)return;
    const BYTE* b=poseRing+static_cast<SIZE_T>(r%RING)*POSEBUF;const DWORD len=poseLen[r%RING];const BYTE* o=b;unsigned n=0,refus=0;
    while(o+8<=b+len){DWORD a=0,nn=0;memcpy(&a,o,4);memcpy(&nn,o+4,4);if(o+8+nn>b+len)break;
        if(Engagee(a,true)){__try{memcpy(reinterpret_cast<void*>(a),o+8,nn);++n;}__except(EXCEPTION_EXECUTE_HANDLER){++refus;}}else ++refus;
        o+=8+nn;}
    ++sPoseRestored;
    if(poseRestLogs<6 || (refus && poseRestLogs<30)){++poseRestLogs;Logf("Labo POSES : retour %lu -> %lu : %u bloc(s) remis (%lu octets photographies), %u refuse(s).",x,r,n,len,refus);}
}

constexpr unsigned GR_MAX=400;
static DWORD grList[RING],grEnd[RING],grN[RING],grObj[RING][GR_MAX]; static BYTE grEnt[RING][GR_MAX][0x18],grData[RING][GR_MAX][0xBC]; static DWORD sGrRestored,sGrSkipped; static unsigned grLogs;
static bool GroundOn(){return SceneVt()==0xBF7A24 || KitZone();}

static bool solElargi=true;
static DWORD GroundRayOffset(DWORD fn){
    if(!fn)return 0;
    if(solElargi){
        __try{const BYTE* p=reinterpret_cast<const BYTE*>(fn);const DWORD rayon=reinterpret_cast<DWORD>(base)+0x63DD20;
            for(DWORD k=0;k+16<=0x300;++k){
                if(p[k]==0xCC && p[k+1]==0xCC && p[k+2]==0xCC)break;
                if(p[k]!=0x8B)continue;const BYTE m=p[k+1];if((m&0xC0)!=0x80 || (m&7)==4)continue;
                if(*reinterpret_cast<const DWORD*>(p+k+2)!=0x9C)continue;
                const int r=(m>>3)&7;DWORD j=k+6,off=0;
                if(r==0 && p[j]==0x05){off=*reinterpret_cast<const DWORD*>(p+j+1);j+=5;}
                else if(p[j]==0x81 && p[j+1]==0xC0+r){off=*reinterpret_cast<const DWORD*>(p+j+2);j+=6;}
                else if(p[j]==0x83 && p[j+1]==0xC0+r){off=static_cast<DWORD>(static_cast<LONG>(static_cast<signed char>(p[j+2])));j+=3;}
                else continue;
                if(off<0x40 || off>=0x1000 || p[j]!=0x50+r || p[j+1]!=0xE8)continue;
                if(fn+j+6+static_cast<DWORD>(*reinterpret_cast<const LONG*>(p+j+2))==rayon)return off;}
        }__except(EXCEPTION_EXECUTE_HANDLER){}
        return 0;}
    __try{const BYTE* p=reinterpret_cast<const BYTE*>(fn);
        for(DWORD k=0;k<0x140;++k){
            if(p[k]==0x8B && p[k+1]==0x81 && p[k+2]==0x9C && p[k+3]==0 && p[k+4]==0 && p[k+5]==0 && p[k+6]==0x05 && p[k+11]==0x50 && p[k+12]==0xE8){
                const DWORD off=*reinterpret_cast<const DWORD*>(p+k+7);const LONG rel=*reinterpret_cast<const LONG*>(p+k+13);
                const DWORD tgt=fn+k+17+static_cast<DWORD>(rel);
                if(tgt==reinterpret_cast<DWORD>(base)+0x63DD20 && off>=0x40 && off<0x1000)return off;}
            if(p[k]==0xC2 || (p[k]==0xC3 && k>0x40))break;}
    }__except(EXCEPTION_EXECUTE_HANDLER){}
    return 0;}
static DWORD grZ,grOff;
static bool GroundList(DWORD& cb,DWORD& ce){
    cb=ce=0;grZ=grOff=0;const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;if(!o)return false;
    const DWORD b=Read(reinterpret_cast<void*>(o+0x10)),e=Read(reinterpret_cast<void*>(o+0x14));const DWORD n=b&&e>b&&e-b<=0x100?(e-b)/4:0;
    for(DWORD i=0;i<n;++i){const DWORD g=Read(reinterpret_cast<void*>(b+i*4));const DWORD vt=g?Read(reinterpret_cast<void*>(g)):0;
        const DWORD off=vt?GroundRayOffset(Read(reinterpret_cast<void*>(vt+0x24))):0;if(!off)continue;
        const DWORD z=Read(reinterpret_cast<void*>(g+0x9C));if(z<0x10000)continue;
        cb=Read(reinterpret_cast<void*>(z+off));ce=Read(reinterpret_cast<void*>(z+off+4));grZ=z;grOff=off;
        return cb && ce>cb && ce-cb<=GR_MAX*0x18 && !((ce-cb)%0x18);}
    return false;}

constexpr DWORD CT_MAX=0x600;
static DWORD ctBeg[RING],ctLen[RING]; static BYTE ctData[RING][CT_MAX]; static DWORD sCtRestored; static unsigned ctLogs;
static void ContactSave(DWORD k){
    ctLen[k]=0;if(!grZ)return;const DWORD b=Read(reinterpret_cast<void*>(grZ+grOff+0xC)),e=Read(reinterpret_cast<void*>(grZ+grOff+0x10));
    if(!b || e<b || e-b>CT_MAX || ((e-b)%0x18))return;
    if(e>b && !Copy(ctData[k],reinterpret_cast<void*>(b),e-b))return;
    ctBeg[k]=b;ctLen[k]=e-b;
    if(ctLogs<4 && e>b){++ctLogs;Logf("Labo SOL : tableau des contacts %08lX (%lu element(s)) suivi (scene +0x%lX).",b,(e-b)/0x18,grOff+0xC);}}
static void ContactRestore(DWORD k){
    if(!ctLen[k] || !grZ)return;const DWORD b=Read(reinterpret_cast<void*>(grZ+grOff+0xC)),e=Read(reinterpret_cast<void*>(grZ+grOff+0x10));
    if(b!=ctBeg[k] || e-b!=ctLen[k])return;
    __try{memcpy(reinterpret_cast<void*>(b),ctData[k],ctLen[k]);++sCtRestored;}__except(EXCEPTION_EXECUTE_HANDLER){}}

static DWORD poolBlk,poolSize,poolHdr,poolH,poolAt[RING],poolFor; static BYTE* poolRing; static DWORD poolRingCap,sPoolRestored; static unsigned poolLogs;
static bool OwnerBlock(DWORD a,DWORD& blk,DWORD& size,DWORD& hdr,DWORD& H){
    const LONG hn=heapN<16?heapN:16;
    for(LONG h=0;h<hn;++h){const DWORD hp=heapList[h];if(!hp)continue;
        __try{const DWORD h0=*reinterpret_cast<const DWORD*>(hp+0xC),lo=*reinterpret_cast<const DWORD*>(hp+0x14),hi=*reinterpret_cast<const DWORD*>(hp+0x18);
            if(a<lo || a>=hi || h0>0x40)continue;DWORD b=lo;unsigned it=0;
            while(b<hi && it<2000000){const LONG sz=*reinterpret_cast<const LONG*>(b+4);const DWORD asz=static_cast<DWORD>(sz<0?-sz:sz);if(!asz)break;
                if(a<b+h0+asz){if(sz>=0)return false;blk=b+h0;size=asz;hdr=b;H=h0;return true;}
                b+=h0+asz;++it;}
        }__except(EXCEPTION_EXECUTE_HANDLER){}}
    return false;}
static bool PoolStillThere(){__try{return poolBlk && *reinterpret_cast<const LONG*>(poolHdr+4)==-static_cast<LONG>(poolSize);}__except(EXCEPTION_EXECUTE_HANDLER){return false;}}
static void PoolSave(DWORD x,DWORD firstObj,DWORD listAddr){
    const DWORD k=x%RING;poolAt[k]=0xFFFFFFFF;if(!firstObj)return;
    if(poolFor!=listAddr || !PoolStillThere()){poolFor=listAddr;poolBlk=0;DWORD b,sz,hd,H;
        if(OwnerBlock(firstObj,b,sz,hd,H) && sz>=0x1000 && sz<=0x40000){poolBlk=b;poolSize=sz;poolHdr=hd;poolH=H;}
        if(poolLogs<6){++poolLogs;Logf("Labo SOL : bloc des objets de collision %s (%08lX, 0x%lX octets).",poolBlk?"suivi":"NON trouve",poolBlk,poolBlk?poolSize:0);}}
    if(!poolBlk)return;
    if(poolRingCap<poolSize){if(poolRing)VirtualFree(poolRing,0,MEM_RELEASE);poolRing=static_cast<BYTE*>(VirtualAlloc(nullptr,static_cast<SIZE_T>(RING)*poolSize,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));poolRingCap=poolRing?poolSize:0;}
    if(!poolRing)return;
    if(Copy(poolRing+static_cast<SIZE_T>(k)*poolSize,reinterpret_cast<void*>(poolBlk),poolSize))poolAt[k]=x;}
static void PoolRestore(DWORD r){
    const DWORD k=r%RING;if(poolAt[k]!=r || !poolRing || !PoolStillThere())return;
    __try{memcpy(reinterpret_cast<void*>(poolBlk),poolRing+static_cast<SIZE_T>(k)*poolSize,poolSize);++sPoolRestored;}__except(EXCEPTION_EXECUTE_HANDLER){}}
static void GroundSave(DWORD x){
    const DWORD k=x%RING;grN[k]=0;if(!GroundOn())return;DWORD cb,ce;if(!GroundList(cb,ce))return;
    const DWORD n=(ce-cb)/0x18;if(!Copy(grEnt[k],reinterpret_cast<void*>(cb),n*0x18))return;
    for(DWORD i=0;i<n;++i){DWORD co=0;memcpy(&co,grEnt[k][i]+8,4);grObj[k][i]=(co>=0x10000 && Copy(grData[k][i],reinterpret_cast<void*>(co),0xBC))?co:0;}
    grList[k]=cb;grEnd[k]=ce;grN[k]=n;
    }
static void GroundRestore(DWORD r,DWORD x){
    const DWORD k=r%RING;if(!grN[k])return;DWORD cb,ce;
    if(!GroundList(cb,ce) || cb!=grList[k] || ce!=grEnd[k]){++sGrSkipped;if(grLogs<20){++grLogs;Logf("Labo SOL : retour %lu -> %lu : liste des collisions deplacee (%08lX-%08lX, photo %08lX-%08lX) : NON remise.",x,r,cb,ce,grList[k],grEnd[k]);}return;}
    __try{memcpy(reinterpret_cast<void*>(cb),grEnt[k],grN[k]*0x18);for(DWORD i=0;i<grN[k];++i)if(grObj[k][i])memcpy(reinterpret_cast<void*>(grObj[k][i]),grData[k][i],0xBC);}__except(EXCEPTION_EXECUTE_HANDLER){}
    ++sGrRestored;}

static DWORD TecmoAllocSize(DWORD v);
constexpr DWORD CAM_OBJ=0x400;
static DWORD cvPtr[RING],cvBeg[RING],cvN[RING],ccPtr[RING][3],ccSize[RING][3]; static BYTE cvObj[RING][0x10],cvEl[RING][64],ccData[RING][3][CAM_OBJ]; static DWORD sCamRestored; static unsigned camLogs;
static void CamSave(DWORD x){
    const DWORD k=x%RING;cvPtr[k]=0;for(int i=0;i<3;++i)ccPtr[k][i]=0;if(!SeqPhotoOn())return;
    const DWORD vp=Read(base+0xFCE658);
    if(vp && Copy(cvObj[k],reinterpret_cast<void*>(vp),0x10)){DWORD b,e;memcpy(&b,cvObj[k],4);memcpy(&e,cvObj[k]+4,4);const DWORD n=b&&e>=b&&e-b<=64?e-b:0;
        if(!n || Copy(cvEl[k],reinterpret_cast<void*>(b),n)){cvPtr[k]=vp;cvBeg[k]=b;cvN[k]=n;}}
    static const DWORD slots[3]={0xFCE5D0,0xFCE5E4,0xFCE5E8};
    for(int i=0;i<3;++i){const DWORD p=Read(base+slots[i]);if(p<0x10000)continue;DWORD sz=TecmoAllocSize(p)&~3u;if(!sz)sz=0x100;if(sz>CAM_OBJ)sz=CAM_OBJ;
        if(Copy(ccData[k][i],reinterpret_cast<void*>(p),sz)){ccPtr[k][i]=p;ccSize[k][i]=sz;}}
    if(camLogs<3){++camLogs;Logf("Labo CAMERA : liste des demandes %08lX (%lu octet(s)) ; controleurs %08lX (0x%lX) %08lX (0x%lX) %08lX (0x%lX).",cvPtr[k],cvN[k],ccPtr[k][0],ccSize[k][0],ccPtr[k][1],ccSize[k][1],ccPtr[k][2],ccSize[k][2]);}
}
static void CamRestore(DWORD r,DWORD x){
    if(!SeqPhotoOn())return;const DWORD k=r%RING;bool any=false;
    __try{
        if(cvPtr[k] && Read(base+0xFCE658)==cvPtr[k]){const DWORD vp=cvPtr[k];const DWORD capNow=*reinterpret_cast<const DWORD*>(vp+8),begNow=*reinterpret_cast<const DWORD*>(vp);
            if(begNow==cvBeg[k] || !cvN[k]){DWORD cap;memcpy(&cap,cvObj[k]+8,4);if(begNow==cvBeg[k] && capNow==cap){memcpy(reinterpret_cast<void*>(vp),cvObj[k],0x10);if(cvN[k])memcpy(reinterpret_cast<void*>(cvBeg[k]),cvEl[k],cvN[k]);any=true;}}}
        static const DWORD slots[3]={0xFCE5D0,0xFCE5E4,0xFCE5E8};
        for(int i=0;i<3;++i)if(ccPtr[k][i] && Read(base+slots[i])==ccPtr[k][i]){memcpy(reinterpret_cast<void*>(ccPtr[k][i]),ccData[k][i],ccSize[k][i]);any=true;}
    }__except(EXCEPTION_EXECUTE_HANDLER){}
    if(any)++sCamRestored;
}

static void DiagSeq(DWORD x,const char* quoi){
    const DWORD mgr=Read(base+0xFCE348);float mt=0;if(mgr)Copy(&mt,reinterpret_cast<void*>(mgr+8),4);
    DWORD n[SEQMAX];const unsigned c=SeqList(n);char l[1400];size_t ln=0;l[0]=0;
    for(unsigned i=0;i<c;++i){DWORD id=0,pc=0,fl=0;BYTE a=0,f5=0,f6=0,f7=0,f8=0;float t=0,w=0;Copy(&id,reinterpret_cast<void*>(n[i]+8),4);Copy(&a,reinterpret_cast<void*>(n[i]+0xC),1);
        Copy(&f5,reinterpret_cast<void*>(n[i]+0xD),1);Copy(&f6,reinterpret_cast<void*>(n[i]+0xE),1);Copy(&f7,reinterpret_cast<void*>(n[i]+0xF),1);Copy(&f8,reinterpret_cast<void*>(n[i]+0x10),1);
        Copy(&fl,reinterpret_cast<void*>(n[i]+0x18),4);Copy(&t,reinterpret_cast<void*>(n[i]+0x20),4);Copy(&w,reinterpret_cast<void*>(n[i]+0x24),4);Copy(&pc,reinterpret_cast<void*>(n[i]+0x30),4);
        DWORD op[4]={};if(pc)Copy(op,reinterpret_cast<void*>(pc),16);
        const int q=_snprintf_s(l+ln,sizeof(l)-ln,_TRUNCATE," [%lu %s%u%u%u%u fl %lX t %.1f att %.1f pc %08lX op %lu : %08lX %08lX %08lX %08lX]",id,a?"A":"-",f5,f6,f7,f8,fl,t,w,pc,op[0]&0xFFFF,op[0],op[1],op[2],op[3]);if(q>0)ln+=q;}
    {const DWORD vp=Read(base+0xFCE658);DWORD b=vp?Read(reinterpret_cast<void*>(vp)):0,e=vp?Read(reinterpret_cast<void*>(vp+4)):0;
     const int q=_snprintf_s(l+ln,sizeof(l)-ln,_TRUNCATE," ; camera mode %ld, demandes :",static_cast<LONG>(Read(base+0xFCE5CC)));if(q>0)ln+=q;
     for(DWORD a2=b;b && e>b && a2<e && a2<b+32;a2+=4){const int q2=_snprintf_s(l+ln,sizeof(l)-ln,_TRUNCATE," %lX",Read(reinterpret_cast<void*>(a2)));if(q2>0)ln+=q2;}
     static const DWORD slots[3]={0xFCE5D0,0xFCE5E4,0xFCE5E8};
     for(int i=0;i<3;++i){const DWORD p=Read(base+slots[i]);if(!p)continue;float f10=0;Copy(&f10,reinterpret_cast<void*>(p+0x10),4);
         const int q3=_snprintf_s(l+ln,sizeof(l)-ln,_TRUNCATE," ; ctl%d id %lX etat %lX +10 %.2f",i,Read(reinterpret_cast<void*>(p+0x20)),Read(reinterpret_cast<void*>(p+0x30)),f10);if(q3>0)ln+=q3;}}
    Logf("DIAG SEQ image %lu %s : gestionnaire t %.1f, %u noeud(s) :%s.",x,quoi,mt,c,l);}
static DWORD sPhysAwakeFrames; static unsigned physAwakeLogs; static bool physAwakeLast;

static DWORD physCalme,physLastMove;
static bool PhysAwake(){
    if(!PhysZone() || (!physWait && SceneVt()!=0xBF9A20))return false;

    const DWORD pm=Read(base+0x2072190),sc=pm?Read(reinterpret_cast<void*>(pm+0xC)):0;if(!sc)return false;
    const DWORD sent=sc+0x40+0xC;unsigned n=0,awake=0;
    __try{DWORD nd=*reinterpret_cast<const DWORD*>(sc+0x40+0x14);
        while(nd && nd!=sent && n<512){++n;const DWORD e=*reinterpret_cast<const DWORD*>(nd);
            if(e && *reinterpret_cast<const DWORD*>(e+0x88)==0 && *reinterpret_cast<const BYTE*>(e+0xC8)==0){const DWORD b=*reinterpret_cast<const DWORD*>(e+0xB0);
                if(b){const float vx=*reinterpret_cast<const float*>(b+0x30),vy=*reinterpret_cast<const float*>(b+0x34),vz=*reinterpret_cast<const float*>(b+0x38),w=*reinterpret_cast<const float*>(b+0x60);
                    float thr=*reinterpret_cast<const float*>(b+0xE8);if(!(thr>0.0f))thr=*reinterpret_cast<const float*>(base+0xF10808);
                    if(sqrtf(vx*vx+vy*vy+vz*vz)+w>thr)++awake;}}
            nd=*reinterpret_cast<const DWORD*>(nd+8);}
    }__except(EXCEPTION_EXECUTE_HANDLER){return false;}
    const bool moving=awake>0;
    if(physLastMove>realFrame)physLastMove=0;if(moving)physLastMove=realFrame;
    const bool on=moving || (physCalme && physLastMove && realFrame<=physLastMove+physCalme);
    if(on!=physAwakeLast && physAwakeLogs<40){++physAwakeLogs;Logf("Labo PHYSIQUE : %u corps en mouvement sur %u : prediction %s (image %lu).",awake,n,on?"COUPEE":"reprise",realFrame);}
    physAwakeLast=on;if(on)++sPhysAwakeFrames;
    return on;
}

static DWORD SEQ_TAIL=8;
static DWORD seqLast,sSeqTailFrames; static unsigned seqTailLogs;

static unsigned ncFlags;
static bool NearCinematic(DWORD j){
    if(seqLast && j+600<seqLast)seqLast=0;
    const bool seqOn=SeqGuardZone() && SeqActiveNow();
    if(seqOn && j>seqLast)seqLast=j;
    const bool libre=predictionSequences && SeqGuardZone();
    const bool seq=seqOn && !libre;
    const bool tail=!seqOn && seqLast && j<=seqLast+SEQ_TAIL;
    if(tail && j==seqLast+1 && seqTailLogs<20){++seqTailLogs;Logf("Labo : fin de sequence a l'image %lu : pas de prediction jusqu'a l'image %lu.",seqLast,seqLast+SEQ_TAIL);}
    ncFlags=0;
    if(CinematicNow())ncFlags=1;else if(seq)ncFlags=2;else if(tail)ncFlags=4;else if(PhysAwake())ncFlags=8;else if(cineLast && j<=cineLast+((nMargeCourte && InList(margeCourteZ,nMargeCourte,SceneVt()))?margeCourte:CINE_TAIL))ncFlags=16;
    return ncFlags!=0;}

static bool Engagee(DWORD v,bool privee){
    DWORD e=0;if(cp::HeapPointer(v&~3u,e))return true;
    if(v>=reinterpret_cast<DWORD>(base) && v<reinterpret_cast<DWORD>(base)+0x21F8000)return !privee;
    MEMORY_BASIC_INFORMATION mi={};return VirtualQuery(reinterpret_cast<void*>(v),&mi,sizeof(mi)) && mi.State==MEM_COMMIT && (!privee || mi.Type==MEM_PRIVATE);}
static bool ModeOk(DWORD m){const DWORD v=Read(reinterpret_cast<void*>(m+8));return v==2 || v==1;}
static DWORD confHash[128][32]; static DWORD checkFrom,checkTo,lastCheck,sChkOk,sChkBad; static bool checkPending; static unsigned chkLogs,vlogs;
static DWORD Confirmed(){
    if(net::active){DWORD c=net::remoteHave;if(c>realFrame)c=realFrame;return c>prepFrame?c:prepFrame;}
   DWORD c=realFrame>delay?realFrame-delay:0;if(c<confFloor)c=confFloor;return c>prepFrame?c:prepFrame;}

static DWORD ConfirmedNext(){
    if(net::active){const DWORD c=net::remoteHave;return c>prepFrame?c:prepFrame;}
    return Confirmed();}

static bool SondeProche(){return srPlay>=2 && realFrame+1>=sondeRefAt && realFrame<=sondeRefAt;}
static bool FramePredicted(DWORD f){
    if(net::active)return f>ConfirmedNext();
    if(f<=Confirmed())return false;

    if((f==realFrame+1 || (f==realFrame && f==prepFrame+1)) && (f<=safeUntil || !base[0xFCDE54] || NoPredictStage() || NearCinematic(f) || (sondeRefAt && (srPlay==1 || SondeProche()))))return false;
    return true;}
static DWORD ReplayIdentity(BYTE* r) {
    BYTE* stream=reinterpret_cast<BYTE*>(Read(r+4));if(!stream)return 0;
    const DWORD size=Read(stream+8),buffer=Read(stream+4);
    return size^(buffer?cp::FastHash(reinterpret_cast<void*>(buffer),size<256?size&~3u:256):0);
}
static void ReadRaw(BYTE* out){Copy(out,base+0xFD0540,RAWHALF);Copy(out+RAWHALF,base+0xFCF788,RAWHALF);Copy(out+2*RAWHALF,base+0xFCEE78,LOGIC);}
static void CoreHashes(DWORD* out){for(unsigned i=0;i<coreCount;++i){const cp::Range& r=cp::ranges[coreIdx[i]];const DWORD h=cp::FastHash(r.address,r.size);out[i]=h?h:1;}}

static DWORD DecorHash() {
    DWORD h=0;
    for(const cp::Component& c:cp::components) {
        if(!cp::ComponentLive(c))continue;
        DWORD o=0,d=0;if(!cp::Describe(c.address,o,d) || !cp::InRdata(Read(reinterpret_cast<void*>(o))))continue;
        cp::MemoryStream ms={reinterpret_cast<DWORD>(base)+0x9BA1F4,cp::stageScratch,sizeof(cp::stageScratch),0};
        memset(cp::stageScratch,0,64);
        if(!cp::CallSave(o,d,&ms) || ms.position>sizeof(cp::stageScratch))continue;
        h=h*0x01000193u^cp::FastHash(cp::stageScratch,(ms.position+3)&~3u)^d;
    }
    return h;
}
typedef DWORD(__cdecl* SceneFn)();typedef void(__cdecl* RebuildFn)(DWORD);typedef void(__cdecl* FinishFn)();
static DWORD CurrentScene(){return rebuildOk?reinterpret_cast<SceneFn>(base+0x5964C0)():0xFF;}

static DWORD SaveDecor(DecorState& st) {
    DWORD h=0;st.n=0;st.scene=CurrentScene();
    for(const cp::Component& c:cp::components) {
        if(!cp::ComponentLive(c))continue;
        DWORD o=0,d=0;if(!cp::Describe(c.address,o,d) || !cp::InRdata(Read(reinterpret_cast<void*>(o))))continue;
        cp::MemoryStream ms={reinterpret_cast<DWORD>(base)+0x9BA1F4,cp::stageScratch,sizeof(cp::stageScratch),0};
        memset(cp::stageScratch,0,64);
        if(!cp::CallSave(o,d,&ms) || ms.position>sizeof(cp::stageScratch))continue;
        h=h*0x01000193u^cp::FastHash(cp::stageScratch,(ms.position+3)&~3u)^d;
        if(st.n<4 && ms.position<=64){DecorComp& e=st.c[st.n++];e.component=c.address;e.owner=o;e.descriptor=d;e.length=ms.position;memcpy(e.data,cp::stageScratch,64);}
    }
    return h;
}

static bool Rebuild(const DecorState& st,double& ms) {
    if(!rebuildOk || st.scene>1 || Read(base+0x2054540+st.scene*0xA8+0x18)==0xFFFFFFFFu)return false;
    LARGE_INTEGER f,t0,t1;QueryPerformanceFrequency(&f);QueryPerformanceCounter(&t0);
    __try{reinterpret_cast<RebuildFn>(base+0x597AF0)(st.scene);reinterpret_cast<FinishFn>(base+0x597B10)();}
    __except(EXCEPTION_EXECUTE_HANDLER){return false;}
    QueryPerformanceCounter(&t1);ms=double(t1.QuadPart-t0.QuadPart)*1000.0/double(f.QuadPart);
    return true;
}
static void LoadDecor(const DecorState& st) {
    for(unsigned i=0;i<st.n;++i) {
        const DecorComp& e=st.c[i];DWORD o=0,d=0;
        if(!cp::Describe(e.component,o,d) || o!=e.owner || d!=e.descriptor)continue;
        memcpy(cp::stageScratch,e.data,64);memset(cp::stageScratch+e.length,0,16);
        cp::MemoryStream s={reinterpret_cast<DWORD>(base)+0x9BA1F4,cp::stageScratch,e.length+16,0};
        cp::CallLoad(o,d,&s);
    }
}

static DWORD StructHash() {
    DWORD h=0x811C9DC5;
    for(unsigned i=0;i<cp::blockCount;++i){DWORD then=0;memcpy(&then,cp::blockSaved+cp::blocks[i].offset,4);if(!cp::InRdata(then))continue;
        h=(h^Read(reinterpret_cast<void*>(cp::blocks[i].address)))*0x01000193u;}
    for(const cp::Component& c:cp::components)if(c.address)h=(h^c.address)*0x01000193u;
    return h;
}
static void Hex(const DecorState& st,char* out,size_t cap) {
    size_t len=0;out[0]=0;
    for(unsigned i=0;i<st.n;++i){const DecorComp& e=st.c[i];
        int w=_snprintf_s(out+len,cap-len,_TRUNCATE,"%s[%06lX:",i?" ":"",e.descriptor-reinterpret_cast<DWORD>(base));if(w>0)len+=w;
        for(DWORD k=0;k<e.length && k<16;++k){w=_snprintf_s(out+len,cap-len,_TRUNCATE,"%02X",e.data[k]);if(w>0)len+=w;}
        w=_snprintf_s(out+len,cap-len,_TRUNCATE,"]");if(w>0)len+=w;}
}
static bool FindStage() {
    stageComp=stageAddr=stageSize=0;
    const DWORD mgr=Read(base+0x2072580);if(!mgr || !Read(reinterpret_cast<void*>(mgr+0x10)))return false;
    const DWORD o=Read(reinterpret_cast<void*>(mgr+0xC));DWORD end=0;
    if(!o || !cp::HeapPointer(o,end))return false;
    DWORD size=cp::RecordedSize(o);
    if(!cp::InRdata(Read(reinterpret_cast<void*>(o)))){
        const DWORD fam=sceneHorsExe?ZoneFamily(Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base)):0;
        static unsigned hxLogs;
        if(fam && hxLogs<8){++hxLogs;Logf(size?"SCENE : scene du module de maps (RTTI %06lX) suivie et remise aux retours, 0x%lX octets (SceneHorsExe=1, essai).":
            "SCENE : scene du module de maps (RTTI %06lX) : taille d'allocation inconnue (%lu), bloc non suivi (SceneHorsExe=1, essai).",fam&0xFFFFFF,size);}
        if(!fam || !size)return false;}
    if(!size || size>STAGEMAX)size=STAGEMAX;if(size>end-o)size=end-o;size&=~3u;
    stageComp=mgr;stageAddr=o;stageSize=size;return size>0;
}
static bool ExactPointer(DWORD v){return v>=0x10000 && ((v>=reinterpret_cast<DWORD>(base) && v<reinterpret_cast<DWORD>(base)+0x21F8000) || cp::RecordedSize(v)!=0);}
static bool Flags(DWORD v){return !(v&0xFEFEFEFEu);}
static bool StagePointer(DWORD a,DWORD b){if(Flags(a) && Flags(b))return false;return ExactPointer(a) || ExactPointer(b);}
constexpr unsigned NEXTRA=8;
static DWORD exAddr[NEXTRA],exSize[NEXTRA],exVt[NEXTRA]; static unsigned exCount; static BYTE* exRing; static DWORD sExWords;

static bool exNoVt[NEXTRA];

struct PhysSeg{DWORD a,n;};
constexpr int PHYS_AL=9;
static DWORD physPoolA,physPoolN;
static PhysSeg physSeg[80]; static unsigned physN; static DWORD physBytes,physScene,physPm,physAl[PHYS_AL],physLim[PHYS_AL]; static int physAlN; static BYTE* physRing; static DWORD physRingCap;
static DWORD physAt[RING],physUse[RING][PHYS_AL]; static bool physOk; static DWORD physCont[6],physTab[6],physNch[6]; static unsigned physLogs; static DWORD sPhysRestores,sPhysSkips;
static bool PhysAdd(DWORD a,DWORD n){if(!a || !n || n>0x400000 || physN>=80)return false;physSeg[physN].a=a;physSeg[physN].n=n;++physN;physBytes+=n;return true;}
static void PhysAddContainer(int i,DWORD c){physCont[i]=c;physTab[i]=Read(reinterpret_cast<void*>(c+4));physNch[i]=Read(reinterpret_cast<void*>(c+8));const DWORD bs=Read(reinterpret_cast<void*>(c));
    if(!physTab[i] || !physNch[i] || physNch[i]>8 || !bs || bs>4096){physTab[i]=0;return;}PhysAdd(physTab[i],physNch[i]*4);
    for(DWORD k=0;k<physNch[i];++k)PhysAdd(Read(reinterpret_cast<void*>(physTab[i]+k*4)),(1u<<k)*bs*12);}
static void PhysWaitIdle(){const DWORD ev=physPm?Read(reinterpret_cast<void*>(physPm+0x10)):0;if(ev)WaitForSingleObject(reinterpret_cast<HANDLE>(ev),100);}

static DWORD PhysUsedEnd(DWORD A){
    __try{const DWORD H=*reinterpret_cast<const DWORD*>(A+0xC),first=*reinterpret_cast<const DWORD*>(A+0x14),end=*reinterpret_cast<const DWORD*>(A+0x18);
        if(!*reinterpret_cast<const DWORD*>(A+0x10) || first>=end || H>0x40)return 0;
        DWORD bk=first;unsigned k=0;
        while(bk<end && k<200000){const LONG sz=*reinterpret_cast<const LONG*>(bk+4);const DWORD asz=static_cast<DWORD>(sz<0?-sz:sz);
            if(sz>=0 && bk+H+asz>=end)return bk+H;
            bk+=H+asz;++k;}
        return end;
    }__except(EXCEPTION_EXECUTE_HANDLER){return 0;}
}
static bool PhysAddAllocator(DWORD A,const char* nom,char* l,size_t cap,size_t& ln){
    if(!A || physAlN>=PHYS_AL)return true;
    for(int i=0;i<physAlN;++i)if(physAl[i]==A)return true;
    if(Read(reinterpret_cast<void*>(A))==reinterpret_cast<DWORD>(base)+0xC126CC){const DWORD in=Read(reinterpret_cast<void*>(A+4));
        const int w=_snprintf_s(l+ln,cap-ln,_TRUNCATE," %s:enveloppe->%08lX",nom,in);if(w>0)ln+=w;A=in;for(int i=0;i<physAlN;++i)if(physAl[i]==A)return true;}
    if(Read(reinterpret_cast<void*>(A))==reinterpret_cast<DWORD>(base)+0x9722FC && Read(reinterpret_cast<void*>(A+4))==reinterpret_cast<DWORD>(base)+0xC1262C){
        PhysAdd(A,4);const int w=_snprintf_s(l+ln,cap-ln,_TRUNCATE," %s:interne",nom);if(w>0)ln+=w;A+=4;}
    if(Read(reinterpret_cast<void*>(A))!=reinterpret_cast<DWORD>(base)+0xC1262C){DWORD v[6];for(int k=0;k<6;++k)v[k]=Read(reinterpret_cast<void*>(A+k*4));
        const int w=_snprintf_s(l+ln,cap-ln,_TRUNCATE," %s:%08lX(table %06lX : %08lX %08lX %08lX %08lX %08lX)",nom,A,v[0]-reinterpret_cast<DWORD>(base),v[1],v[2],v[3],v[4],v[5]);if(w>0)ln+=w;return false;}
    const DWORD rb=Read(reinterpret_cast<void*>(A+0x10)),end=Read(reinterpret_cast<void*>(A+0x18)),ue=PhysUsedEnd(A);
    if(!rb || !ue){const int w=_snprintf_s(l+ln,cap-ln,_TRUNCATE," %s:illisible",nom);if(w>0)ln+=w;return false;}

    const bool hole=physPoolA && physPoolA>=rb && physPoolA+physPoolN<=ue;const DWORD usedNet=(ue-rb)-(hole?physPoolN:0);
    DWORD lim=ue+usedNet+0x10000;if(lim>end || lim<rb)lim=end;
    const DWORD net=(lim-rb)-(hole?physPoolN:0);
    if(net>0x200000){const int w=_snprintf_s(l+ln,cap-ln,_TRUNCATE," %s:utilise 0x%lX TROP",nom,ue-rb);if(w>0)ln+=w;return false;}
    if(A<physScene || A>=physScene+0x2F0)PhysAdd(A,0x34);
    if(hole){PhysAdd(rb,physPoolA-rb);PhysAdd(physPoolA+physPoolN,lim-(physPoolA+physPoolN));}else PhysAdd(rb,lim-rb);
    physAl[physAlN]=A;physLim[physAlN]=lim;++physAlN;
    const int w=_snprintf_s(l+ln,cap-ln,_TRUNCATE," %s:utilise 0x%lX photo 0x%lX/0x%lX",nom,ue-rb,lim-rb,end-rb);if(w>0)ln+=w;
    return true;
}
static void PhysPrepare(){
    physN=0;physBytes=0;physOk=false;physAlN=0;for(unsigned i=0;i<RING;++i)physAt[i]=0xFFFFFFFF;
    if(!PhysZone())return;

    physPm=Read(base+0x2072190);const DWORD sc=physPm?Read(reinterpret_cast<void*>(physPm+0xC)):0;if(!sc)return;physScene=sc;
    const DWORD sv=Read(reinterpret_cast<void*>(sc+0x160));
    physPoolA=Read(reinterpret_cast<void*>(sc+0x154));physPoolN=Read(reinterpret_cast<void*>(sc+0x2B4));PhysAdd(sc,0x2F0);PhysAdd(sv,0x298);
    char l[900];size_t ln=0;l[0]=0;bool ok=true;
    static const char* const nm[6]={"r0","r1","r2","r3","r4","r5"};
    for(int i=0;i<6;++i)ok=PhysAddAllocator(sc+0x164+i*0x34,nm[i],l,sizeof l,ln) && ok;
    ok=PhysAddAllocator(Read(base+0x2092450),"globale",l,sizeof l,ln) && ok;
    ok=PhysAddAllocator(Read(reinterpret_cast<void*>(sc+0x14C)),"s14C",l,sizeof l,ln) && ok;
    ok=PhysAddAllocator(Read(reinterpret_cast<void*>(sc+0x150)),"s150",l,sizeof l,ln) && ok;
    const DWORD conts[6]={sc+0x40,sc+0x6C,sc+0x98,sc+0xC4,sv+0x8,sv+0x34};
    for(int i=0;i<6;++i)PhysAddContainer(i,conts[i]);
    if(physLogs<8){++physLogs;Logf("Labo PHYSIQUE : scene %08lX solveur %08lX ; reserves :%s ; listes : %lu %lu %lu %lu %lu %lu troncon(s) ; %u morceaux, %lu octets.",
        sc,sv,l,physNch[0],physNch[1],physNch[2],physNch[3],physNch[4],physNch[5],physN,physBytes);}
    if(!ok){Logf("Labo PHYSIQUE : une reserve illisible ou trop grande : physique non photographiee.");physN=0;return;}
    if(physBytes>0x400000){Logf("Labo PHYSIQUE : %lu octets a photographier, trop : physique non photographiee.",physBytes);physN=0;return;}
    if(physRingCap<physBytes){if(physRing)VirtualFree(physRing,0,MEM_RELEASE);physRing=static_cast<BYTE*>(VirtualAlloc(nullptr,static_cast<SIZE_T>(RING)*physBytes,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));physRingCap=physRing?physBytes:0;}
    if(!physRing){Logf("Labo PHYSIQUE : memoire indisponible.");physN=0;return;}
    physOk=true;
}
static void PhysSave(DWORD x){
    if(!physOk)return;PhysWaitIdle();
    for(int i=0;i<physAlN;++i){const DWORD ue=PhysUsedEnd(physAl[i]);physUse[x%RING][i]=ue;if(!ue || ue+0x40>physLim[i]){physAt[x%RING]=0xFFFFFFFF;
        if(physLogs<20){++physLogs;Logf("Labo PHYSIQUE : image %lu : reserve %d utilisee jusqu'a %08lX, au-dela de la photo (%08lX) : photo de cette image ecartee.",x,i,ue,physLim[i]);}return;}}
    BYTE* d=physRing+(x%RING)*physBytes;
    for(unsigned i=0;i<physN;++i){if(!Copy(d,reinterpret_cast<void*>(physSeg[i].a),physSeg[i].n)){physAt[x%RING]=0xFFFFFFFF;return;}d+=physSeg[i].n;}
    physAt[x%RING]=x;
}
static const char* PhysInvalid(){
    if(Read(base+0x2072190)!=physPm || Read(reinterpret_cast<void*>(physPm+0xC))!=physScene)return "scene physique changee";
    for(int i=0;i<physAlN;++i){const DWORD ue=PhysUsedEnd(physAl[i]);if(!ue || ue+0x40>physLim[i])return "reserve utilisee au-dela de la photo";}
    for(int i=0;i<6;++i)if(physTab[i] && (Read(reinterpret_cast<void*>(physCont[i]+4))!=physTab[i] || Read(reinterpret_cast<void*>(physCont[i]+8))!=physNch[i]))return "troncons d'une liste changes";
    return nullptr;
}
static void PhysRestore(DWORD r,DWORD x){
    if(!physOk || physAt[r%RING]!=r)return;
    if(const char* why=PhysInvalid()){++sPhysSkips;if(physLogs<20){++physLogs;Logf("Labo PHYSIQUE : retour %lu -> %lu : physique NON remise (%s) ; photo desactivee.",x,r,why);}physOk=false;return;}
    PhysWaitIdle();const BYTE* d=physRing+(r%RING)*physBytes;
    for(unsigned i=0;i<physN;++i){__try{memcpy(reinterpret_cast<void*>(physSeg[i].a),d,physSeg[i].n);}__except(EXCEPTION_EXECUTE_HANDLER){break;}d+=physSeg[i].n;}
    ++sPhysRestores;
}
static DWORD TecmoAllocSize(DWORD v){
    const LONG n=heapN<16?heapN:16;
    for(LONG h=0;h<n;++h){const DWORD hp=heapList[h];if(!hp)continue;
        __try{const DWORD H=*reinterpret_cast<const DWORD*>(hp+0xC),lo=*reinterpret_cast<const DWORD*>(hp+0x14),hi=*reinterpret_cast<const DWORD*>(hp+0x18);
            if(!*reinterpret_cast<const DWORD*>(hp+0x10) || v<lo+H || v>=hi)continue;
            const DWORD hdr=v-H;const LONG sz=*reinterpret_cast<const LONG*>(hdr+4);if(sz>=0)return 0;
            const DWORD prev=*reinterpret_cast<const DWORD*>(hdr);if(prev){if(prev<lo || prev>=hi)return 0;const LONG ps=*reinterpret_cast<const LONG*>(prev+4);if(prev+H+static_cast<DWORD>(ps<0?-ps:ps)!=hdr)return 0;}
            return static_cast<DWORD>(-sz);}__except(EXCEPTION_EXECUTE_HANDLER){return 0;}}
    return 0;
}
static bool TecmoPtr(DWORD v){
    if(v<0x10000 || (v&3))return false;const LONG n=heapN<16?heapN:16;
    for(LONG h=0;h<n;++h){const DWORD hp=heapList[h];if(!hp)continue;DWORD lo=0,hi=0;__try{lo=*reinterpret_cast<const DWORD*>(hp+0x14);hi=*reinterpret_cast<const DWORD*>(hp+0x18);}__except(EXCEPTION_EXECUTE_HANDLER){continue;}if(v>=lo && v<hi)return true;}
    return false;
}
static void AddHeapObjects(){
    for(unsigned b=0;b<NEXTRA;++b)exNoVt[b]=false;
    if(!stageAddr)return;
    char l[400];size_t len=0;l[0]=0;unsigned seen=0,added=0;
    for(DWORD k=0;k<stageSize;k+=4){const DWORD v=Read(reinterpret_cast<void*>(stageAddr+k));const DWORD sz=TecmoAllocSize(v);if(!sz || v==stageAddr)continue;
        bool dup=false;for(unsigned b=0;b<exCount;++b)if(exAddr[b]==v)dup=true;if(dup)continue;
        ++seen;unsigned ptrs=0;const DWORD nw=(sz<=STAGEMAX?sz:STAGEMAX)/4;for(DWORD w=0;w<nw;++w){const DWORD u=Read(reinterpret_cast<void*>(v+w*4));if(u>=0x10000 && !(u&3) && (cp::PointerLike(u) || TecmoPtr(u)))++ptrs;}
        const bool ok=sz>=0x40 && sz<=STAGEMAX && exCount<NEXTRA && ptrs*8<=nw;
        if(ok){exAddr[exCount]=v;exSize[exCount]=sz&~3u;exVt[exCount]=0;exNoVt[exCount]=true;++exCount;++added;}
        if(seen<=14){const int w=_snprintf_s(l+len,sizeof(l)-len,_TRUNCATE," +%lX:0x%lX/%u adr%s",k,sz,ptrs,ok?"":"(non)");if(w>0)len+=w;}}
    static unsigned hoLogs;if(hoLogs<8){++hoLogs;Logf("Labo : objets du tas vises par le bloc de la scene (Fuel) : %u vu(s), %u photographie(s) :%s.",seen,added,l);}
}
static BYTE* ExRing(DWORD f,unsigned b){return exRing+((f%RING)*NEXTRA+b)*STAGEMAX;}

static unsigned exDetruits;
static void FindExtra() {
    exCount=0;exDetruits=0;
    for(const cp::Component& c:cp::components) {
        if(!cp::ComponentLive(c) || exCount>=NEXTRA)continue;
        DWORD o=0,d=0,end=0;if(!cp::Describe(c.address,o,d) || !cp::InRdata(Read(reinterpret_cast<void*>(o))) || !cp::HeapPointer(o,end) || o==stageAddr)continue;
        if(Read(reinterpret_cast<void*>(o))==reinterpret_cast<DWORD>(base)+0x977E7C){bool dup=false;for(unsigned i=0;i<exCount;++i)if(exAddr[i]==o)dup=true;if(!dup)++exDetruits;continue;}
        bool dup=false;for(unsigned i=0;i<exCount;++i)if(exAddr[i]==o)dup=true;if(dup)continue;
        DWORD size=cp::RecordedSize(o);if(!size)size=0x400;if(size>STAGEMAX)size=STAGEMAX;if(size>end-o)size=end-o;size&=~3u;if(!size)continue;
        exAddr[exCount]=o;exSize[exCount]=size;exVt[exCount]=Read(reinterpret_cast<void*>(o));++exCount;
    }
}
static void SaveExtra(DWORD f){for(unsigned b=0;b<exCount;++b)Copy(ExRing(f,b),reinterpret_cast<void*>(exAddr[b]),exSize[b]);}
static bool StageValid(){return stageAddr && Read(reinterpret_cast<void*>(stageComp+0xC))==stageAddr;}
static void SaveStage(BYTE* out){memset(out,0,STAGEMAX);if(stageAddr)Copy(out,reinterpret_cast<void*>(stageAddr),stageSize);}

static DWORD sListeInvalide; static unsigned listeInvalideLogs;
static unsigned TimerNodes(DWORD* out,unsigned cap){
    unsigned n=0;DWORD node=Read(base+0xF91230),last=reinterpret_cast<DWORD>(base+0xF91230);
    while(node){
        bool dup=(node&3)!=0 || n>=cap;for(unsigned i=0;i<n && !dup;++i)if(out[i]==node)dup=true;
        if(dup){++sListeInvalide;return 0;}
        out[n++]=node;last=node+4;node=Read(reinterpret_cast<void*>(node+4));
    }
    if(Read(base+0xCC4720)!=last){++sListeInvalide;
        if(listeInvalideLogs<5){++listeInvalideLogs;Logf("Labo MINUTERIES : liste des minuteries incoherente (%u maillon(s), queue differente) : aucun lien garde d'apres la liste.",n);}
        return 0;}
    return n;
}

static bool DansBloc(DWORD a);
static unsigned g_twRaison; static DWORD sCompteursRemis;
static bool Flottant(DWORD v,float& f){memcpy(&f,&v,4);const float a=f<0?-f:f;return a==a && a>=0.001f && a<=1.0e6f;}
static bool CompteurFlottant(DWORD a,DWORD b){float x,y;if(!Flottant(a,x) || !Flottant(b,y))return false;float d=x-y;if(d<0)d=-d;return d>=0.01f && d<=64.0f;}
static bool TimerWord(DWORD a,DWORD old,DWORD now,const DWORD* tn,unsigned n){
    for(unsigned i=0;i<n;++i)if(tn[i]+4==a){g_twRaison=1;return true;}
    if(CompteurFlottant(old,now) && !DansBloc(old) && !DansBloc(now)){++sCompteursRemis;return false;}
    for(unsigned i=0;i<n;++i)if(tn[i]==old || tn[i]==now){g_twRaison=2;return true;}
    if(old==a-4 || now==a-4){g_twRaison=3;return true;}
    for(DWORD v:{old,now})if(v>=0x10000 && !(v&3) && Read(reinterpret_cast<void*>(v+4))==v){g_twRaison=4;return true;}
    return false;
}
static DWORD sTimerWordsKept; static unsigned timerWordLogs;

static bool remisePartielle=false; static DWORD sStructPart; static unsigned partLogs;

static bool remiseMinuteries=false; static DWORD tlHead[RING],tlTail[RING]; static BYTE tlInside[RING]; static DWORD sListeEntiere,sListeGardee; static unsigned listeLogs;
static bool DansBloc(DWORD a){return stageAddr && a>=stageAddr && a+0x10<=stageAddr+stageSize;}
static bool ListeDansBloc(){
    DWORD node=Read(base+0xF91230),last=reinterpret_cast<DWORD>(base+0xF91230);unsigned n=0;
    while(node){if(!DansBloc(node) || ++n>256)return false;last=node+4;node=Read(reinterpret_cast<void*>(node+4));if(node==last-4)return false;}
    return Read(base+0xCC4720)==last;}
static void PhotoListe(DWORD x){tlHead[x%RING]=Read(base+0xF91230);tlTail[x%RING]=Read(base+0xCC4720);tlInside[x%RING]=ListeDansBloc()?1:0;}
static bool ModuleOuNul(DWORD v){return !v || (v>=reinterpret_cast<DWORD>(base) && v<reinterpret_cast<DWORD>(base)+0x21F8000);}

static DWORD RestoreStage(DWORD f) {
    if(!restoreStage || !StageValid() || ringFrame[f%RING]!=f)return 0;
    const DWORD svt=SceneVt();
    if(svt==0x980170 || (nSansRemise && InList(sansRemise,nSansRemise,svt)))return 0;

    const bool strict=svt==0xBEC570;
    const BYTE* s=stageRing+(f%RING)*STAGEMAX;DWORD n=0;
    DWORD tn[512];const unsigned tnN=TimerNodes(tn,512);
    static BYTE garde[STAGEMAX/0x40];memset(garde,0,sizeof garde);unsigned nGarde=0;
    for(DWORD k=0;k<stageSize;k+=4) {
        DWORD old=0,now=0;memcpy(&old,s+k,4);
        if(!Copy(&now,reinterpret_cast<void*>(stageAddr+k),4) || now==old || (!strict && (!old || !now)) || !StagePointer(old,now))continue;
        if(TimerWord(stageAddr+k,old,now,tn,tnN) || (ModuleOuNul(old) && ModuleOuNul(now)))continue;
        if(remisePartielle){if(!garde[k/0x40]){garde[k/0x40]=1;++nGarde;}continue;}
        ++sStructSkip;if(skipLogs<24){++skipLogs;Logf("Labo SCENE : retour a %lu : structure de la scene changee (+%lX : %08lX -> %08lX) : bloc laisse tel quel.",f,k,old,now);}
        goto extra;
    }

    static BYTE lien[STAGEMAX/4];bool listeEntiere=false;
    if(remiseMinuteries && tlInside[f%RING] && ListeDansBloc()){
        listeEntiere=true;memset(lien,0,sizeof lien);
        for(unsigned i=0;i<tnN;++i)if(DansBloc(tn[i]))lien[(tn[i]+4-stageAddr)/4]=1;
        DWORD node=tlHead[f%RING];unsigned c=0;
        while(node && DansBloc(node) && c++<256){const DWORD o=node+4-stageAddr;lien[o/4]=1;DWORD nx=0;memcpy(&nx,s+o,4);if(nx==node)break;node=nx;}
        ++sListeEntiere;
    } else if(tnN && remiseMinuteries)++sListeGardee;
    if(nGarde){++sStructPart;if(partLogs<24){++partLogs;Logf("Labo SCENE : retour a %lu : structure de la scene changee : %u fenetre(s) de 64 octets laissee(s) telle(s) quelle(s), reste du bloc remis.",f,nGarde);}}
    char dl[700];size_t dn=0;dl[0]=0;
    for(DWORD k=0;k<stageSize;k+=4) {
        DWORD old=0,now=0;memcpy(&old,s+k,4);
        if(!Copy(&now,reinterpret_cast<void*>(stageAddr+k),4) || now==old)continue;
        if(listeEntiere && lien[k/4]){__try{*reinterpret_cast<DWORD*>(stageAddr+k)=old;}__except(EXCEPTION_EXECUTE_HANDLER){break;}++n;continue;}
        if(garde[k/0x40])continue;
        if(TimerWord(stageAddr+k,old,now,tn,tnN)) {
            ++sTimerWordsKept;if(timerWordLogs<20){++timerWordLogs;Logf("Labo MINUTERIES : retour a %lu : lien de minuterie du bloc de la scene +%lX garde (raison %u ; photo %08lX, actuel %08lX ; bloc +%lX).",f,k,g_twRaison,old,now,DansBloc(old)?old-stageAddr:(DansBloc(now)?now-stageAddr:0xFFFF));}
            continue;
        }
        if(StagePointer(old,now) && !(ModuleOuNul(old) && ModuleOuNul(now))) {
            ++sStageSkipped;if(skipLogs<24){++skipLogs;Logf("Labo SCENE : retour a %lu : mot +%lX non remis (adresse ?) : photo %08lX, actuel %08lX.",f,k,old,now);}
            continue;
        }
        __try{*reinterpret_cast<DWORD*>(stageAddr+k)=old;}__except(EXCEPTION_EXECUTE_HANDLER){break;}
        if(sc::Diag(f) && n<20){const int q=_snprintf_s(dl+dn,sizeof(dl)-dn,_TRUNCATE," +%lX %08lX<-%08lX",k,old,now);if(q>0)dn+=q;}
        ++n;++stageHits[k/4];
    }
    if(listeEntiere){__try{*reinterpret_cast<DWORD*>(base+0xF91230)=tlHead[f%RING];*reinterpret_cast<DWORD*>(base+0xCC4720)=tlTail[f%RING];}__except(EXCEPTION_EXECUTE_HANDLER){}
        if(listeLogs<10){++listeLogs;Logf("Labo MINUTERIES : retour a %lu : liste des minuteries remise entiere (%u maillon(s) aujourd'hui).",f,tnN);}}
    if(sc::Diag(f) && n)Logf("DIAG SCENE : retour a %lu : %lu mot(s) du bloc remis (photo<-actuel) :%s.",f,n,dl);
    sStageWords+=n;if(n)++sStageRestores;
extra:
    for(unsigned b=0;b<exCount;++b) {
        if(!exNoVt[b] && Read(reinterpret_cast<void*>(exAddr[b]))!=exVt[b])continue;
        if(exNoVt[b] && (TecmoAllocSize(exAddr[b])&~3u)!=exSize[b])continue;
        const BYTE* e=ExRing(f,b);bool structural=false;
        for(DWORD k=0;k<exSize[b] && !structural;k+=4){DWORD old=0,now=0;memcpy(&old,e+k,4);if(Copy(&now,reinterpret_cast<void*>(exAddr[b]+k),4) && now!=old && old && now && StagePointer(old,now))structural=true;}
        if(structural){++sStructSkip;continue;}
        for(DWORD k=0;k<exSize[b];k+=4) {
            DWORD old=0,now=0;memcpy(&old,e+k,4);
            if(!Copy(&now,reinterpret_cast<void*>(exAddr[b]+k),4) || now==old || StagePointer(old,now) || (exNoVt[b] && (TecmoPtr(old) || TecmoPtr(now))))continue;
            __try{*reinterpret_cast<DWORD*>(exAddr[b]+k)=old;++sExWords;}__except(EXCEPTION_EXECUTE_HANDLER){break;}
        }
    }
    return n;
}
static void StageTop(char* out,size_t cap) {
    size_t len=0;out[0]=0;
    for(unsigned t=0;t<12;++t) {
        DWORD best=0,bi=0;for(DWORD i=0;i<STAGEMAX/4;++i)if(stageHits[i]>best){best=stageHits[i];bi=i;}
        if(!best)break;
        const int w=_snprintf_s(out+len,cap-len,_TRUNCATE," +%lX x%lu",bi*4,best);if(w>0)len+=w;stageHits[bi]=0;
    }
    memset(stageHits,0,sizeof(stageHits));
}
static bool Alloc() {
    if(!refStage)refStage=static_cast<BYTE*>(VirtualAlloc(nullptr,static_cast<SIZE_T>(RAW_FRAMES)*STAGEMAX,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!stageRing)stageRing=static_cast<BYTE*>(VirtualAlloc(nullptr,RING*STAGEMAX,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!exRing)exRing=static_cast<BYTE*>(VirtualAlloc(nullptr,RING*NEXTRA*STAGEMAX,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!exRing)return false;
    if(!refStage || !stageRing)return false;
    if(!refHash) {
        refHash=static_cast<DWORD*>(VirtualAlloc(nullptr,REF_FRAMES*MAXCORE*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
        refRaw=static_cast<BYTE*>(VirtualAlloc(nullptr,static_cast<SIZE_T>(RAW_FRAMES)*RAWSZ,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
        refHave=static_cast<bool*>(VirtualAlloc(nullptr,REF_FRAMES,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    }
    return refHash && refRaw && refHave;
}
static const char* QuickCheck() {
    if(GetCurrentThreadId()!=cp::threadId)return "thread different";
    if(Read(base+0xFCE790)!=cp::manager || !ModeOk(cp::manager) ||
       Read(reinterpret_cast<void*>(cp::manager+0xC))!=reinterpret_cast<DWORD>(cp::reader))return "lecteur de replay different";
    for(unsigned i=0;i<cp::guardCount;++i){BYTE b[32];if(!Copy(b,cp::guards[i].address,cp::guards[i].size)||memcmp(b,cp::guards[i].bytes,cp::guards[i].size))return "garde modifiee";}
    if(!cp::AnimationCheck())return "selecteurs d'animation incoherents";
    return nullptr;
}
static void Unprepare(const char* why) {
    clockOn=false;
    if(prepared && why!=lastReason){Logf("Labo : arret (%s).",why);lastReason=why;}
    prepared=false;resim=false;rollbackPlanned=false;cp::Release();
    InterlockedExchange(&kb::noKO,0);InterlockedExchange(&kb::blocked,0);blockedAt=0;
    InterlockedExchange(&sc::gate,0);InterlockedExchange(&sc::blocked,0);eventBlockedAt=0;
}
static bool PrepareCommon(BYTE* r,DWORD m,DWORD x) {
    const char* why=cp::Prepare(r,m);
    if(why){prepRetry=++prepFails>=3?0xFFFFFFFFu:x+120;if(prepFails==3)Logf("Labo : 3 refus, plus de tentative pour ce round.");if(why!=lastReason){Logf("Labo : preparation refusee a l'image %lu (%s).",x,why);lastReason=why;}return false;}
    coreCount=0;
    for(const char* n:coreNames)for(unsigned i=0;i<cp::count && coreCount<MAXCORE;++i)if(!strcmp(cp::ranges[i].name,n)){coreIdx[coreCount++]=i;}
    return true;
}

constexpr DWORD NODESZ=0xD0,NODEMAX=256,NODEWIN=64;
static DWORD nodeP[NODEMAX]; static unsigned nNodes; static DWORD* nodeRef; static WORD* nodeRefN; static DWORD nodeAt[IR][NODEMAX];
static DWORD nodeDiagDe,nodeDiagA; static BYTE *nodeRefRaw,*nodeAtRaw; static unsigned nodeLogs; static BYTE nodeKnown[NODEMAX]; static DWORD guetRadeau;
static void NodesSet(DWORD x){
    nNodes=0;memset(nodeKnown,0,sizeof nodeKnown);const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;if(!o)return;
    const DWORD tab=Read(reinterpret_cast<void*>(o+0x2C)),n=Read(reinterpret_cast<void*>(o+0x30));
    for(DWORD k=1;tab && n<=4096 && k<n && nNodes<NODEMAX;++k){const DWORD p=Read(reinterpret_cast<void*>(tab+k*4));if(p<0x10000 || !Engagee(p,true))continue;nodeP[nNodes++]=p;}

    {const unsigned nm=nNodes;for(unsigned i=0;i<nm && nNodes+5<=NODEMAX;++i){const DWORD c=Read(reinterpret_cast<void*>(nodeP[i]+0x20));if(c<0x10000 || !Engagee(c,true))continue;
        const unsigned e0=nNodes;nodeP[nNodes++]=c;nodeP[nNodes++]=c+0xD0;
        for(DWORD off:{0x9Cu,0xA0u,0xA4u}){const DWORD t=Read(reinterpret_cast<void*>(c+off));if(t>=0x10000 && Engagee(t,true))nodeP[nNodes++]=t;}
        static unsigned cl;if(cl<12){++cl;Logf("Labo NOEUDS : controleur du modele n%u (%08lX) = entrees n%u a n%u (c, c+0xD0, pistes).",i+1,c,e0+1,nNodes);}}}
    if(!nodeRef)nodeRef=static_cast<DWORD*>(VirtualAlloc(nullptr,RAW_FRAMES*NODEMAX*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!nodeRefN)nodeRefN=static_cast<WORD*>(VirtualAlloc(nullptr,RAW_FRAMES*2,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(nodeDiagA && nodeDiagA>=nodeDiagDe){
        if(!nodeRefRaw)nodeRefRaw=static_cast<BYTE*>(VirtualAlloc(nullptr,NODEWIN*NODEMAX*NODESZ,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
        if(!nodeAtRaw)nodeAtRaw=static_cast<BYTE*>(VirtualAlloc(nullptr,IR*NODEMAX*NODESZ,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));}
    static unsigned l;if(l<12){++l;Logf("Labo NOEUDS : %u modele(s) suivis un par un a l'image %lu (scene %06lX).",nNodes,x,Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base));}

    if(guetRadeau && nNodes && !guetAbs){const DWORD par=Read(reinterpret_cast<void*>(nodeP[0]+0x20));if(par>=0x10000){guetAbs=par+guetRadeau;guetAbsDe=nodeDiagDe;guetAbsA=nodeDiagA;
        Logf("Labo NOEUDS : guet arme sur le parent du modele n1 : %08lX + 0x%lX = %08lX, images %lu-%lu.",par,guetRadeau,guetAbs,guetAbsDe,guetAbsA);}}
}
static DWORD NodeHash(DWORD p){DWORD h=2166136261u;const BYTE* b=reinterpret_cast<const BYTE*>(p);__try{for(DWORD k=0;k<NODESZ;++k)h=(h^b[k])*16777619u;}__except(EXCEPTION_EXECUTE_HANDLER){return 0;}return h;}

struct Citr{DWORD img,mdl,cpt,w14;float tmr,x,y,z;BYTE chute,decl[6],arme[2],s3dc[4];};
static bool releveCitr; static Citr citr[IR]; static Citr citrDer[2]; static bool citrDerOk[2]; static unsigned citrLogs[2];
static void CitrLire(DWORD x,Citr& c){
    memset(&c,0,sizeof c);c.img=x;const BYTE* g=base+0xF9069C;
    Copy(c.decl,g,6);Copy(&c.tmr,g+8,4);Copy(&c.cpt,g+0xC,4);Copy(c.arme,g+0x10,2);Copy(&c.w14,g+0x14,4);c.chute=base[0xF90638];
    const DWORD m=Read(base+0xF90634);c.mdl=0xFFFF;
    if(m>=0x10000){Copy(&c.x,reinterpret_cast<void*>(m+0x9C),4);Copy(&c.y,reinterpret_cast<void*>(m+0xA0),4);Copy(&c.z,reinterpret_cast<void*>(m+0xA4),4);
        const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;
        const DWORD tab=o?Read(reinterpret_cast<void*>(o+0x2C)):0,n=o?Read(reinterpret_cast<void*>(o+0x30)):0;
        for(DWORD k=0;tab && n<=4096 && k<n;++k)if(Read(reinterpret_cast<void*>(tab+k*4))==m){c.mdl=k;break;}}
    if(stageAddr)Copy(c.s3dc,reinterpret_cast<void*>(stageAddr+0x3DC),4);
}
static void CitrLog(int p,const Citr& c){
    if(citrDerOk[p] && !c.chute && !memcmp(&citrDer[p].mdl,&c.mdl,sizeof(Citr)-sizeof(DWORD)))return;
    citrDer[p]=c;citrDerOk[p]=true;if(citrLogs[p]>=6000)return;++citrLogs[p];
    Logf("CITROUILLE %s image %lu : chute %u, modele n%lu, pos %.4f %.4f %.4f, declencheurs %u%u%u%u%u%u, minuterie %.4f, compteur %lu, arme %u/%u, +14 %08lX, scene +3DC %02X %02X %02X %02X.",
        p?"rb":"ref",c.img,c.chute,c.mdl,c.x,c.y,c.z,c.decl[0],c.decl[1],c.decl[2],c.decl[3],c.decl[4],c.decl[5],c.tmr,c.cpt,c.arme[0],c.arme[1],c.w14,c.s3dc[0],c.s3dc[1],c.s3dc[2],c.s3dc[3]);
}
static void CitrNoter(DWORD x){if(releveCitr && SceneVt()==0x97E110)CitrLire(x,citr[K(x)]);}
static void CitrRb(DWORD j){if(releveCitr && (kTest && pass==2) && citr[K(j)].img==j && SceneVt()==0x97E110)CitrLog(1,citr[K(j)]);}
static void NodesRef(DWORD x){
    if(releveCitr && (kTest && pass==1) && SceneVt()==0x97E110){Citr c;CitrLire(x,c);CitrLog(0,c);}
    if(!nNodes || !nodeRef || !nodeRefN || x>=RAW_FRAMES)return;nodeRefN[x]=static_cast<WORD>(nNodes);
    for(unsigned i=0;i<nNodes;++i)nodeRef[x*NODEMAX+i]=NodeHash(nodeP[i]);
    if(nodeRefRaw && x>=nodeDiagDe && x<=nodeDiagA && x-nodeDiagDe<NODEWIN)for(unsigned i=0;i<nNodes;++i)Copy(nodeRefRaw+(static_cast<SIZE_T>(x-nodeDiagDe)*NODEMAX+i)*NODESZ,reinterpret_cast<void*>(nodeP[i]),NODESZ);}
static void NodesAt(DWORD x){
    CitrNoter(x);
    if(!nNodes)return;for(unsigned i=0;i<nNodes;++i)nodeAt[K(x)][i]=NodeHash(nodeP[i]);
    if(nodeAtRaw && x>=nodeDiagDe && x<=nodeDiagA)for(unsigned i=0;i<nNodes;++i)Copy(nodeAtRaw+(static_cast<SIZE_T>(K(x))*NODEMAX+i)*NODESZ,reinterpret_cast<void*>(nodeP[i]),NODESZ);}
static void NodesCompare(DWORD j){
    if(!nNodes || !nodeRef || !nodeRefN || j>=RAW_FRAMES || nodeRefN[j]!=nNodes)return;

    unsigned bad=0;for(unsigned i=0;i<nNodes;++i)if(nodeRef[j*NODEMAX+i]!=nodeAt[K(j)][i])++bad;
    for(unsigned i=0;i<nNodes;++i){if(nodeRef[j*NODEMAX+i]==nodeAt[K(j)][i] || nodeKnown[i])continue;nodeKnown[i]=1;
        if(nodeLogs>=120)continue;++nodeLogs;
        char t[500];size_t ln=0;t[0]=0;
        if(nodeRefRaw && nodeAtRaw && j>=nodeDiagDe && j<=nodeDiagA && j-nodeDiagDe<NODEWIN){
            const DWORD* r=reinterpret_cast<const DWORD*>(nodeRefRaw+(static_cast<SIZE_T>(j-nodeDiagDe)*NODEMAX+i)*NODESZ);const DWORD* c=reinterpret_cast<const DWORD*>(nodeAtRaw+(static_cast<SIZE_T>(K(j))*NODEMAX+i)*NODESZ);
            unsigned shown=0;for(DWORD k=0;k<NODESZ/4 && shown<10;++k)if(r[k]!=c[k]){const int w=_snprintf_s(t+ln,sizeof(t)-ln,_TRUNCATE," +%lX ref %08lX / %08lX",k*4,r[k],c[k]);if(w>0)ln+=w;++shown;}}
        Logf("Labo NOEUDS image confirmee %lu : modele n%u (%08lX) differe de la reference pour la 1re fois (%u modele(s) differents a cette image)%s%s.",j,i+1,nodeP[i],bad,ln?" :":"",t);}
}
static void PrepareReference(BYTE* r,DWORD m,DWORD x) {
    if(!PrepareCommon(r,m,x))return;
    refCoreCount=coreCount;for(unsigned i=0;i<coreCount;++i)refCoreName[i]=cp::ranges[coreIdx[i]].name;
    cineLast=0;seqLast=0;prepared=true;prepFrame=x;lastReason=nullptr;
    clockOn=horlogeImage;clockFrame0=x;clockBase=*reinterpret_cast<const float*>(base+0xEDAA24);
    cp::ScanRegions();FindStage();
    Logf("Labo REFERENCE : enregistrement a partir de l'image %lu (%u plages du coeur) ; bloc d'etat de la scene : %s (0x%lX octets).",x,coreCount,stageAddr?"trouve":"absent",stageSize);
    NodesSet(x);
}

static double PrepMs(LARGE_INTEGER& t){LARGE_INTEGER n,f;QueryPerformanceCounter(&n);QueryPerformanceFrequency(&f);const double ms=double(n.QuadPart-t.QuadPart)*1000.0/double(f.QuadPart);t=n;return ms;}

static const char* NomZone(DWORD vt){
    switch(vt){
    case 0x9A8990:return "Fighting Entertainment";case 0x9AFD64:return "Dojo";case 0x97ABAC:return "Aircraft Carrier";case 0x9A02C0:return "Sweat";
    case 0x9A4244:return "Arrival";case 0x97C824:return "Forest";case 0x9A3F88:return "Dead or Alive";case 0xBEAD20:return "Depth";case 0x9A0C8C:return "Lab";
    case 0x97B954:return "Desert Wasteland";case 0xBF6A5C:return "Sanctuary";case 0x9AA394:return "Temple of the Dragon (exterieur)";
    case 0xBFF00C:return "Temple of the Dragon (interieur)";case 0xBF58BC:return "Flow (bas)";case 0xBF48D0:return "Flow (haut)";case 0x980170:return "Zack Island";
    case 0xBEC570:return "Hot Zone";case 0xBF7A24:return "Fuel (haut)";case 0xBF9A20:return "Fuel (bas)";case 0x97D064:return "Lost World";
    case 0x97E110:return "Lorelei hante (haut)";case 0x97EEBC:return "Lorelei hante (bas)";case 0x9819A8:return "Sky City";case 0x980A74:case 0x9812A8:return "Lorelei";
    case 0xBFB810:case 0xBFC2E8:return "Scramble";case 0xBE95D4:case 0xC00C8C:return "Streets";case 0xBFD82C:return "End of the World";
    case 0xBF1C94:return "Home";case 0xBF3090:return "Home (cour)";case 0xBED8F0:return "Circus";case 0xBEE79C:return "Tiger Show";
    case 0x97B0A4:return "Danger Zone (PS4, StageDNZ)";case 0x977EA0:return "Crimson (PS4, StageCRM)";case 0x97A214:return "Crimson 2 / bas de Crimson (PS4, StageCRM2)";
    default:return "inconnu (module de maps ?)";}}

typedef void(__fastcall* GraineFn)(void* rng,void* inutile,DWORD graine);
static bool graineFaite;

static bool graineG1=false;

static bool ctrlCompletFlow=false;
static void GrainesEffets(DWORD x,const char* quand) {
    static BYTE t[0x9C0];Copy(t,base+0x1087AB0,sizeof t);DWORD h=2166136261u;for(DWORD k=0;k<sizeof t;++k)h=(h^t[k])*16777619u;
    h^=x*0x9E3779B9u;

    static const DWORD rv[5]={0x2071378,0x2072A58,0x2070830,0x206FE58,0x206DE88};
    const GraineFn f=reinterpret_cast<GraineFn>(base+0xFE010);
    bool ok=true;__try{for(int k=0;k<5;++k)f(base+rv[k],nullptr,h^static_cast<DWORD>((k+1)*0x85EBCA6Bu));
        if(graineG1)f(base+0x20906E0,nullptr,h^static_cast<DWORD>(6*0x85EBCA6Bu));}__except(EXCEPTION_EXECUTE_HANDLER){ok=false;}
    static unsigned n;if(n<200){++n;Logf("Generateurs des effets 3 a 5%s : meme graine des deux cotes a l'image %lu (%s) : %08lX%s.",graineG1?" et 1":"",x,quand,h,ok?"":" : ECHEC");}
}
static void PrepareRollback(BYTE* r,DWORD m,DWORD x) {
    {const DWORD vt=SceneVt();Logf("Stage : %s (table de methodes %06lX).",NomZone(vt),vt);

     const DWORD va=vt+reinterpret_cast<DWORD>(base);HMODULE hm=nullptr;
     if(vt>=0x2200000 && GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS|GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,reinterpret_cast<LPCSTR>(va),&hm) && hm){
         Logf("Stage : table de methodes dans un autre module, decalage %06lX.",va-reinterpret_cast<DWORD>(hm));}

     else if(vt>=0x2200000){const DWORD col=Read(reinterpret_cast<void*>(va-4));const DWORD b0=reinterpret_cast<DWORD>(base);
         Logf("Stage : table de methodes hors module (memoire allouee) ; RTTI %06lX.",col>b0 && col<b0+0x2200000?col-b0:0);}}
    if(net::active && !graineFaite){graineFaite=true;GrainesEffets(x,"debut de la phase en ligne");}
    badLogs=0;seqLast=0;

    cineLast=0;
    LARGE_INTEGER pt;QueryPerformanceCounter(&pt);double pm[10]={};
    if(!PrepareCommon(r,m,x))return;
    pm[0]=PrepMs(pt);
    if((kTest && pass==2) && coreCount!=refCoreCount){Logf("Labo : plages du coeur differentes de la reference (%u / %u).",coreCount,refCoreCount);cp::Release();return;}
    {

        const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;
        const DWORD zvt=o?Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base):0;
        if(o && zvt==0xBF7A24) {

            const DWORD cb=Read(reinterpret_cast<void*>(o+0x150)),ce=Read(reinterpret_cast<void*>(o+0x154));
            const bool okl=cb && ce>cb && ce-cb<=0x4000 && !((ce-cb)%0x18) && true;
            unsigned nc=0,okc=0;
            for(DWORD q=cb;okl && q<ce;q+=0x18){const DWORD co=Read(reinterpret_cast<void*>(q+8));if(co<0x10000)continue;
                if(!Engagee(co,false))continue;
                ++nc;++okc;}
            Logf("Labo : haut de Fuel : liste des collisions du sol %08lX-%08lX (%lu element(s)) %s ; %u objet(s) de collision, %u ajoute(s).",cb,ce,cb&&ce>cb?(ce-cb)/0x18:0,okl?"ajoutee":"NON ajoutee",nc,okc);
            for(DWORD q=cb;okl && q<ce && q<cb+0x18*6;q+=0x18)Logf("Labo : haut de Fuel :   collision %08lX %08lX %08lX %08lX drapeaux %08lX %08lX.",Read(reinterpret_cast<void*>(q)),Read(reinterpret_cast<void*>(q+4)),
                Read(reinterpret_cast<void*>(q+8)),Read(reinterpret_cast<void*>(q+0xC)),Read(reinterpret_cast<void*>(q+0x10)),Read(reinterpret_cast<void*>(q+0x14)));
        }
        if(o && KitZone()) {

            const DWORD b=Read(reinterpret_cast<void*>(o+0x10)),e=Read(reinterpret_cast<void*>(o+0x14));const DWORD n=b&&e>b&&e-b<=0x100?(e-b)/4:0;DWORD done[8];unsigned nd=0;
            for(DWORD i=0;i<n;++i){const DWORD g=Read(reinterpret_cast<void*>(b+i*4));const DWORD vt=g?Read(reinterpret_cast<void*>(g)):0;
                const DWORD off=vt?GroundRayOffset(Read(reinterpret_cast<void*>(vt+0x24))):0;if(!off)continue;
                const DWORD z=Read(reinterpret_cast<void*>(g+0x9C));if(z<0x10000)continue;bool dup=false;for(unsigned k=0;k<nd;++k)if(done[k]==z)dup=true;if(dup || nd>=8)continue;done[nd++]=z;
                const DWORD cb=Read(reinterpret_cast<void*>(z+off)),ce=Read(reinterpret_cast<void*>(z+off+4));
                Logf("Labo SOL : zone %06lX : liste des collisions a [fournisseur+0x9C]+0x%lX.",zvt,off);
                const bool okl=cb && ce>cb && ce-cb<=GR_MAX*0x18 && !((ce-cb)%0x18);
                unsigned nc=0,okc=0;DWORD omin=0xFFFFFFFF,omax=0;
                for(DWORD q=cb;okl && q<ce;q+=0x18){const DWORD co=Read(reinterpret_cast<void*>(q+8));if(co<0x10000)continue;
                    if(!Engagee(co,false))continue;
                    if(co<omin)omin=co;if(co>omax)omax=co;
                    ++nc;++okc;}
                Logf("Labo SOL : zone %06lX, fournisseur [%lu] %08lX -> %08lX%s : liste des collisions %08lX-%08lX (%lu element(s)) %s ; %u objet(s) de collision (%08lX..%08lX), %u ajoute(s).",zvt,i,g,z,z==o?" (la scene)":"",
                    cb,ce,cb&&ce>cb?(ce-cb)/0x18:0,okl?"ajoutee":"NON ajoutee",nc,nc?omin:0,omax,okc);}
            if(!nd)Logf("Labo SOL : zone %06lX : aucune fonction de hauteur au rayon reconnu : collisions du sol non photographiees.",zvt);

        }
        if(o && SeqGuardZone()) {
            {const bool okd=cp::Add(base+0xF9CB50,0x10,"drapeaux_sequence_danger");static unsigned sdLogs;if(sdLogs<4){++sdLogs;Logf("Labo : drapeaux de sequence de danger (game+F9CB50, 0x10) %s.",okd?"ajoutes a la photo":"REFUS");}}
            {const bool okc=cp::Add(base+0xF9CC30,0x270,"compteurs_combo");static unsigned ccLogs;if(ccLogs<4){++ccLogs;Logf("Labo : compteurs de combo (game+F9CC30, 0x270) %s.",okc?"ajoutes a la photo":"REFUS");}}
        }

        if(o && zvt==0x97E110) {
            const bool okt=cp::Add(base+0xF9060C,0xC0,"citrouille_lorelei") && cp::Add(base+0xCC3FF8,4,"citrouille_joueur");
            static unsigned ctLogs;if(ctLogs<4){++ctLogs;Logf("Labo : citrouille de Lorelei hante (game+F9060C, 0xC0 ; game+CC3FF8, 4) %s.",okt?"ajoutee a la photo":"REFUS");}

            {const DWORD tab=Read(reinterpret_cast<void*>(o+0x2C)),n=Read(reinterpret_cast<void*>(o+0x30));unsigned nm=0,okm=0;
             for(unsigned i=0;tab && n<=4096 && i<12;++i){const DWORD idx=Read(base+0xCC4164+i*4)&0x3FF;if(idx==0x3FF || idx>=n)continue;
                 const DWORD m=Read(reinterpret_cast<void*>(tab+idx*4));if(m<0x10000)continue;++nm;if(cp::Add(reinterpret_cast<BYTE*>(m),0xD0,"citrouille_modele"))++okm;}
             static unsigned cmLogs;if(cmLogs<4){++cmLogs;Logf("Labo : modeles des citrouilles de Lorelei hante : %u trouve(s), %u ajoute(s) a la photo (0xD0 octets chacun).",nm,okm);}}
        }

        if(o && zvt==0x980170) {

            const bool okz=cp::Add(base+0xF91180,0xB0,"coco_zack") && cp::Add(base+0xCC43AC,4,"coco_joueur") && cp::Add(reinterpret_cast<BYTE*>(o+0x5C0),0x170,"coco_scene");
            const DWORD tab=Read(reinterpret_cast<void*>(o+0x2C)),n=Read(reinterpret_cast<void*>(o+0x30));unsigned nm=0,okm=0;
            for(unsigned i=0;tab && n<=4096 && i<12;++i){const DWORD idx=Read(base+0xCC45AC+i*4)&0x3FF;if(idx==0x3FF || idx>=n)continue;
                const DWORD m=Read(reinterpret_cast<void*>(tab+idx*4));if(m<0x10000)continue;++nm;if(cp::Add(reinterpret_cast<BYTE*>(m),0xD0,"coco_modele"))++okm;}
            static unsigned czLogs;if(czLogs<4){++czLogs;Logf("Labo : noix de coco de Zack Island (game+F91180, 0xB0 ; game+CC43AC ; fin du bloc de scene +5C0, 0x170) %s ; modeles : %u trouve(s), %u ajoute(s).",okz?"ajoutees a la photo":"REFUS",nm,okm);}
        }

        if(o && (zvt==0x97A214 || zvt==0x977EA0)) {
            const bool okc=cp::Add(base+0xF8E680,0x70,"crimson_danger") && cp::Add(base+0xCC2AD8,4,"crimson_joueur") && cp::Add(base+0xF8E6F0,0x9C8,"crimson_generateur");
            static unsigned crLogs;if(crLogs<4){++crLogs;Logf("Labo : Crimson : objet qui tombe (game+F8E680, 0x70 ; game+CC2AD8, 4 ; generateur game+F8E6F0) %s.",okc?"ajoute a la photo":"REFUS");}

            {const DWORD tab=Read(reinterpret_cast<void*>(o+0x2C)),n=Read(reinterpret_cast<void*>(o+0x30));unsigned nm=0,okm=0;
             DWORD ids[10];for(unsigned i=0;i<8;++i)ids[i]=Read(base+0xCC2E38+i*4)&0x3FF;ids[8]=0xF7;ids[9]=0xDA;
             for(unsigned i=0;tab && n<=4096 && i<10;++i){if(ids[i]==0x3FF || ids[i]>=n)continue;bool vu=false;for(unsigned k=0;k<i;++k)if(ids[k]==ids[i])vu=true;if(vu)continue;
                 const DWORD m=Read(reinterpret_cast<void*>(tab+ids[i]*4));if(m<0x10000)continue;++nm;if(cp::Add(reinterpret_cast<BYTE*>(m),0xD0,"crimson_modele"))++okm;}
             static unsigned cpLogs;if(cpLogs<4){++cpLogs;Logf("Labo : Crimson : modeles du panneau : %u trouve(s), %u ajoute(s) a la photo (0xD0 octets chacun).",nm,okm);}}

            {const bool okl=cp::Add(base+0xF8F1D0,0x2C,"crimson_lanceur");
             static unsigned clLogs;if(clLogs<4){++clLogs;Logf("Labo : Crimson : lanceur du panneau (game+F8F1D0, 0x2C) %s.",okl?"ajoute a la photo":"REFUS");}}
        }
        if(o && zvt==0xBF48D0) {
            const bool okx=cp::Add(base+0x2073BD4,4,"flow_explosion_active");
            static unsigned fxLogs;if(fxLogs<4){++fxLogs;Logf("Labo : Flow : drapeau de l'explosion du radeau (game+2073BD4, 4) %s.",okx?"ajoute a la photo":"REFUS");}
        }
        if(o && zvt==0xBF48D0) {
            if(zvt!=0xBF48D0)Logf("Labo : zone %06lX : contacts, collisions du sol et noeuds photographies comme le haut de Flow (lignes 'Flow (haut)' ci-dessous).",zvt);
            const DWORD b=Read(reinterpret_cast<void*>(o+0x16C)),e=Read(reinterpret_cast<void*>(o+0x170));
            const bool ok=b && e>b && e-b<=0x2000 && cp::Add(reinterpret_cast<BYTE*>(b),e-b,"flow_contacts");
            Logf("Labo : Flow (haut) : tableau des contacts %08lX-%08lX (%lu element(s)) %s.",b,e,b&&e>b?(e-b)/0x18:0,ok?"ajoute a la photo":"NON ajoute");

            {const DWORD cb=Read(reinterpret_cast<void*>(o+0x160)),ce=Read(reinterpret_cast<void*>(o+0x164));
             const bool ok3=cb && ce>cb && ce-cb<=0x4000 && cp::Add(reinterpret_cast<BYTE*>(cb),ce-cb,"flow_collisions");
             Logf("Labo : Flow (haut) : liste des collisions du sol %08lX-%08lX (%lu element(s)) %s.",cb,ce,cb&&ce>cb?(ce-cb)/0x18:0,ok3?"ajoutee a la photo":"NON ajoutee");

             {unsigned nc=0,okc=0;for(DWORD q=cb;ok3 && q<ce;q+=0x18){const DWORD co=Read(reinterpret_cast<void*>(q+8));
                 if(co<reinterpret_cast<DWORD>(base) || co>=reinterpret_cast<DWORD>(base)+0x21F8000)continue;++nc;if(cp::Add(reinterpret_cast<BYTE*>(co),0xBC,"flow_objet_collision"))++okc;
                 if(nc<=3){char t[600];size_t ln=0;t[0]=0;for(DWORD k=0;k<0xBC;k+=4){const int w=_snprintf_s(t+ln,sizeof(t)-ln,_TRUNCATE," %08lX",Read(reinterpret_cast<void*>(co+k)));if(w>0)ln+=w;}
                     Logf("Labo : Flow (haut) : objet de collision %08lX :%s.",co,t);}}
              Logf("Labo : Flow (haut) : %u objet(s) de collision, %u ajoute(s) a la photo.",nc,okc);}
             for(DWORD q=cb;ok3 && q<ce && q<cb+0x18*12;q+=0x18)Logf("Labo : Flow (haut) :   collision %08lX %08lX %08lX %08lX drapeaux %08lX %08lX.",Read(reinterpret_cast<void*>(q)),Read(reinterpret_cast<void*>(q+4)),
                 Read(reinterpret_cast<void*>(q+8)),Read(reinterpret_cast<void*>(q+0xC)),Read(reinterpret_cast<void*>(q+0x10)),Read(reinterpret_cast<void*>(q+0x14)));}

            const DWORD mod=Read(reinterpret_cast<void*>(o+0x2C));DWORD lo=0,hi=0;unsigned nn=0;
            for(DWORD k=0;mod && k<0x800;k+=4){const DWORD m=Read(reinterpret_cast<void*>(mod+k));if(m<0x01000000 || m>0x7FFF0000)continue;
                if(lo && (m+0x20000<lo || m>lo+0x20000))continue;
                if(!Engagee(m,true))continue;
                if(!lo || m<lo)lo=m;if(m+0xD0>hi)hi=m+0xD0;++nn;}
            const bool ok2=lo && hi>lo && hi-lo<=0x20000 && cp::Add(reinterpret_cast<BYTE*>(lo),hi-lo,"flow_noeuds");
            Logf("Labo : Flow (haut) : %u noeud(s) du decor %08lX-%08lX (0x%lX octets) %s.",nn,lo,hi,hi-lo,ok2?"ajoutes a la photo":"NON ajoutes");

            {const DWORD nbM=mod?Read(reinterpret_cast<void*>(o+0x30)):0;unsigned hors=0,okh=0,dans=0;
             for(DWORD k=1;mod && nbM<=4096 && k<nbM;++k){const DWORD m=Read(reinterpret_cast<void*>(mod+k*4));if(m<0x10000 || !Engagee(m,true))continue;
                 if(ok2 && m>=lo && m+0xD0<=hi){++dans;continue;}
                 ++hors;if(cp::Add(reinterpret_cast<BYTE*>(m),0xD0,"flow_noeud_isole"))++okh;}
             Logf("Labo : Flow (haut) : %lu modele(s) dans le tableau : %u dans le bloc des noeuds, %u ailleurs dont %u ajoute(s) a la photo.",nbM>1?nbM-1:0,dans,hors,okh);}
        }
    }
    {

        const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;

        const DWORD ovt=o?Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base):0;
        const DWORD mod=(o && (ovt==0xC00C8C || ovt==0xBE95D4 || ovt==0xBF48D0 || ovt==0xBF7A24 || ovt==0xBF9A20 || ovt==0xBFB810 || ovt==0xBFC2E8 || KitZone()))?Read(reinterpret_cast<void*>(o+0x2C)):0;static DWORD seen[256];unsigned ns=0,added=0;static DWORD mseen[256];unsigned nm=0,madded=0;

        const DWORD tabMod=mod,nbMod=mod?Read(reinterpret_cast<void*>(o+0x30)):0;

        const bool ctrlComplet=(ovt==0xC00C8C || ovt==0xBE95D4 || ovt==0xBFB810 || ovt==0xBFC2E8);unsigned nPistes=0;DWORD oPistes=0;const bool cachePose=(ovt==0xBF48D0 || ovt==0xBF58BC);unsigned nCache=0,nSlots=0,nCtrlFlow=0;DWORD oCache=0;nPoseCtl=0; static DWORD slotSeen[64];
        for(DWORD k=1;tabMod && nbMod<=4096 && k<nbMod && ns<256;++k){const DWORD m=Read(reinterpret_cast<void*>(tabMod+k*4));if(m<0x10000)continue;
            if(!Engagee(m,true))continue;
            const DWORD c=Read(reinterpret_cast<void*>(m+0x20));if(c<0x10000)continue;
            bool dup=false;for(unsigned i=0;i<ns;++i)if(seen[i]==c)dup=true;if(dup)continue;seen[ns++]=c;
            if(!Engagee(c,true))continue;
            if(ctrlComplet){
                if(cp::Add(reinterpret_cast<BYTE*>(c+0x10),0x110,"controleur_animation"))++added;
                const DWORD np=Read(reinterpret_cast<void*>(c+0xA8));
                if(np && np<=256)for(DWORD off:{0x9Cu,0xA0u,0xA4u}){const DWORD p=Read(reinterpret_cast<void*>(c+off));if(p<0x10000 || !Engagee(p,true))continue;
                    if(oPistes+np*0x88<=0x80000 && cp::Add(reinterpret_cast<BYTE*>(p),np*0x88,"pistes_animation")){++nPistes;oPistes+=np*0x88;}}
                continue;}

            if(cp::Add(reinterpret_cast<BYTE*>(c+0x114),4,"temps_animation"))++added;

            if(cachePose && nPoseCtl<POSECTL){static const DWORD po[8]={0x9C,0xA0,0xA4,0x5C,0x60,0x64,0x68,0xC0};for(int k=0;k<8;++k)posePrev[nPoseCtl][k]=Read(reinterpret_cast<void*>(c+po[k]));poseCtl[nPoseCtl++]=c;}
            if(cachePose){const DWORD nb=Read(reinterpret_cast<void*>(c+0xE8));
                if(nb && nb<=256 && cp::Add(reinterpret_cast<BYTE*>(c+0x5C),0x10,"poses_pointeurs")){++nCache;
                    for(DWORD off=0x5C;off<=0x68;off+=4){const DWORD sl=Read(reinterpret_cast<void*>(c+off));if(sl<0x10000 || !Engagee(sl,true))continue;
                        bool dupS=false;for(unsigned u=0;u<nSlots;++u)if(slotSeen[u]==sl)dupS=true;if(dupS || nSlots>=64)continue;slotSeen[nSlots++]=sl;
                        if(cp::Add(reinterpret_cast<BYTE*>(sl),0x10,"poses_emplacement"))++nCache;
                        const DWORD md=Read(reinterpret_cast<void*>(c+0xBC));
                        for(DWORD a=0;a<3;++a){const DWORD t=Read(reinterpret_cast<void*>(sl+a*4));if(t<0x10000 || !Engagee(t,true))continue;const DWORD tl=(a==0 && (md==0 || md==1 || md==3))?0x10:nb*0x10;
                            if(cp::Add(reinterpret_cast<BYTE*>(t),tl,"poses_tableau")){++nCache;oCache+=tl;}}}}

                const DWORD np=Read(reinterpret_cast<void*>(c+0xA8));
                if(np && np<=256)for(DWORD off:{0x9Cu,0xA0u,0xA4u}){const DWORD p=Read(reinterpret_cast<void*>(c+off));if(p<0x10000 || !Engagee(p,true))continue;
                    if(oPistes+np*0x88<=0x80000 && cp::Add(reinterpret_cast<BYTE*>(p),np*0x88,"pistes_animation")){++nPistes;oPistes+=np*0x88;}}}
            if(cachePose && ctrlCompletFlow){unsigned k3=0;
                if(cp::Add(reinterpret_cast<BYTE*>(c+0x10),0x4C,"controleur_flow_a"))++k3;if(cp::Add(reinterpret_cast<BYTE*>(c+0x6C),0xA8,"controleur_flow_b"))++k3;
                if(cp::Add(reinterpret_cast<BYTE*>(c+0x118),0x8,"controleur_flow_c"))++k3;if(k3==3)++nCtrlFlow;}
            }
        if(mod)Logf("Labo : temps d'animation des modeles du decor : %lu modele(s) dans le tableau de la scene, %u controleur(s), %u ajoute(s) a la photo.",nbMod>1 && nbMod<=4096?nbMod-1:0,ns,added);
        if(cachePose)Logf("Labo : Flow : cache de poses des animations : %u plage(s), %u emplacement(s), %lu octets de tableaux ; pistes par os : %u tableau(x), %lu octets%s.",nCache,nSlots,oCache,nPistes,oPistes,ctrlCompletFlow?(nCtrlFlow?" ; controleurs complets (ControleurCompletFlow=1)":" ; controleurs complets : AUCUN ajoute"):"");
        if(ctrlComplet)Logf("Labo : %s : controleurs d'animation complets (+0x10 a +0x11F) : %u ; pistes par os : %u tableau(x), %lu octets.",ovt==0xBFB810 || ovt==0xBFC2E8?"Scramble":"Streets",added,nPistes,oPistes);
        if(nm)Logf("Labo : avancement des modeles du decor (+0x60) : %u modele(s), %u ajoute(s) a la photo.",nm,madded);
        static unsigned rngLogs;if(rngLogs<3){++rngLogs;Logf("Labo : generateurs aleatoires des effets dans la photo : %u / 6.",cp::rngExtra);}
        if(SeqGuardZone()){const bool a=cp::Add(base+0xD33550,0x50,"demande_sequence"),b=cp::Add(base+0xD2EA18,0x1C,"evenement_params"),c2=cp::Add(base+0xFD14B8,4,"demandes_drapeaux");

            static unsigned sgLogs;if(sgLogs<4){++sgLogs;Logf("Labo : sequences en transaction (zone %06lX) : demande en attente %s, parametres d'evenement %s, drapeaux %s.",SceneVt(),a?"photographiee":"REFUS",b?"photographies":"REFUS",c2?"photographies":"REFUS");}}
    }
    sondeOwnExtra[0]=reinterpret_cast<DWORD>(refStage);sondeOwnExtra[1]=reinterpret_cast<DWORD>(stageRing);sondeOwnExtra[2]=reinterpret_cast<DWORD>(exRing);
    if(autoArmed && autoN){unsigned ok=0;DWORD bytes=0;for(unsigned i=0;i<autoN;++i)if(cp::Add(reinterpret_cast<BYTE*>(autoRng[i][0]),autoRng[i][1]-autoRng[i][0],"sonde_auto")){++ok;bytes+=autoRng[i][1]-autoRng[i][0];}
        Logf("SONDE AUTO : %u / %u plage(s) ajoutee(s) a la photo (%lu octets).",ok,autoN,bytes);}
    {
        const DWORD mgr=Read(base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;
        if(o){const DWORD b=Read(reinterpret_cast<void*>(o+0x10)),e=Read(reinterpret_cast<void*>(o+0x14)),idx=Read(base+0xF8E638);
            const DWORD n=b&&e>b?(e-b)/4:0;const DWORD g=idx<n?Read(reinterpret_cast<void*>(b+idx*4)):0;const DWORD vt=g?Read(reinterpret_cast<void*>(g)):0;
            const DWORD fn=vt?Read(reinterpret_cast<void*>(vt+0x24)):0;
            Logf("Labo SOL : scene %06lX, %lu fournisseur(s), index %lu, fournisseur %08lX (table %06lX), hauteur = %06lX.",Read(reinterpret_cast<void*>(o))-reinterpret_cast<DWORD>(base),n,idx,g,
                vt?vt-reinterpret_cast<DWORD>(base):0,fn?fn-reinterpret_cast<DWORD>(base):0);
            for(DWORD i=0;i<n && i<8;++i){const DWORD gi=Read(reinterpret_cast<void*>(b+i*4));const DWORD vi=gi?Read(reinterpret_cast<void*>(gi)):0;
                Logf("Labo SOL :   [%lu] %08lX table %06lX hauteur %06lX.",i,gi,vi?vi-reinterpret_cast<DWORD>(base):0,vi?Read(reinterpret_cast<void*>(vi+0x24))-reinterpret_cast<DWORD>(base):0);}}
    }
    {const DWORD zv=SceneVt();clockOn=horlogeImage && (!net::active || zv==0xBF48D0 || zv==0xBF58BC);}
    clockFrame0=x;clockBase=*reinterpret_cast<const float*>(base+0xEDAA24);

    if(clockOn)PinClock(x);
    if(clockOn && clockLogs<6){++clockLogs;if(horlogeAbsolue)Logf("Labo : horloge du decor ABSOLUE (image/60) a partir de l'image %lu (avant : %.4f s).",x,clockBase);else Logf("Labo : horloge du decor fixee a l'image : %.4f s a l'image %lu, +1/60 par image.",clockBase,x);}
    ringBytes=cp::total;
    if(ringCap<ringBytes){if(ring)VirtualFree(ring,0,MEM_RELEASE);ring=static_cast<BYTE*>(VirtualAlloc(nullptr,ringBytes*RING,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));ringCap=ring?ringBytes:0;}
    if(!ring){Logf("Labo : memoire insuffisante.");cp::Release();return;}
    for(DWORD& f:ringFrame)f=0xFFFFFFFF;
    pm[1]=PrepMs(pt);

    DWORD h[MAXCORE];CoreHashes(h);stableMask=0;char names[400];size_t len=0;names[0]=0;
    for(unsigned i=0;i<coreCount;++i){if(pass==3 || refHash[x*MAXCORE+i]==h[i])stableMask|=1u<<i;
        else{const int w=_snprintf_s(names+len,sizeof(names)-len,_TRUNCATE,"%s%s",len?", ":"",refCoreName[i]);if(w>0)len+=w;}}
    pm[2]=PrepMs(pt);
    cp::DecorBuild();
    pm[3]=PrepMs(pt);
    rawMasked=0;
    if(x<RAW_FRAMES){BYTE now[RAWSZ];ReadRaw(now);const BYTE* ref=refRaw+static_cast<SIZE_T>(x)*RAWSZ;
        cp::ScanRegions();scanAge=0;
        for(DWORD o=0;o<RAWSZ;o+=4){const bool d=memcmp(now+o,ref+o,4)!=0;memset(rawMask+o,d?1:0,4);if(d)++rawMasked;}}
    pm[4]=PrepMs(pt);
    DWORD stageMasked=0;

    if(FindStage()){BYTE* now=stageRing+(x%RING)*STAGEMAX;SaveStage(now);
        if(x<RAW_FRAMES){const BYTE* ref=refStage+static_cast<SIZE_T>(x)*STAGEMAX;
            for(DWORD o=0;o<STAGEMAX;o+=4){stageMask[o/4]=memcmp(now+o,ref+o,4)?1:0;stageMasked+=stageMask[o/4];}}
        else memset(stageMask,0,sizeof(stageMask));}
    else stageAddr=0;
    pm[5]=PrepMs(pt);
    PhysPrepare();
    FindExtra();if(SceneVt()==0xBF9A20)AddHeapObjects();else for(unsigned b=0;b<NEXTRA;++b)exNoVt[b]=false;SaveExtra(x);
    pm[6]=PrepMs(pt);
    memset(stageHits,0,sizeof(stageHits));stageLogs=skipLogs=evLogs=0;
    Logf("Labo SCENE : bloc d'etat %s (scene courante, table de methodes %06lX, 0x%lX octets, %lu mots deja differents de la reference ecartes) ; remise aux retours : %s.",
        stageAddr?"suivi":"ABSENT",stageAddr?Read(reinterpret_cast<void*>(stageAddr))-reinterpret_cast<DWORD>(base):0,stageSize,stageMasked,restoreStage?"oui":"non");

    if(stageAddr && (SceneVt()==0xBF48D0 || SceneVt()==0xBF58BC)){float t4=0,t8=0,tC=0;DWORD w=Read(reinterpret_cast<void*>(stageAddr+0x194));memcpy(&t4,&w,4);
        w=Read(reinterpret_cast<void*>(stageAddr+0x198));memcpy(&t8,&w,4);w=Read(reinterpret_cast<void*>(stageAddr+0x19C));memcpy(&tC,&w,4);
        Logf("Flow : temps de la scene a la preparation (image %lu, round %lu) : +194 %.3f, +198 %.3f, +19C %.3f (a comparer entre les deux PC).",x,roundNo,t4,t8,tC);}
    {char l[300];size_t len=0;l[0]=0;for(unsigned b=0;b<exCount;++b){const int w=_snprintf_s(l+len,sizeof(l)-len,_TRUNCATE," %06lX/0x%lX",exVt[b]-reinterpret_cast<DWORD>(base),exSize[b]);if(w>0)len+=w;}
     Logf("Labo SCENE : %u objet(s) du decor photographie(s) aussi (table de methodes/taille) :%s ; taille d'allocation connue du bloc de la scene : 0x%lX ; zone %lu ; %u objet(s) de scene detruit(s) ecarte(s).",exCount,l,stageAddr?cp::RecordedSize(stageAddr):0,CurrentScene(),exDetruits);}
    pm[7]=PrepMs(pt);
    safeUntil=confFloor=0;InterlockedExchange(&sc::fired,0);zoneLogs=0;winOpen=false;dernierEvt=0;
    if(lastEvent && x<lastEvent+WinLen()){safeUntil=lastEvent+WinLen();Logf("Labo : evenement de scene a l'image %lu, avant la preparation : mode sans prediction jusqu'a l'image %lu.",lastEvent,safeUntil);
        if(finApresBascule){WinOpen(x,1);Logf("Labo : fin anticipee possible des que la scene est calme (FinApresBascule=1).");}}
    prepared=true;prepFrame=x;nextFrame=x+1;realFrame=x+1;lastConfirmed=x;lastCompared=x;lastFrame=x;resim=false;rollbackPlanned=false;lastReason=nullptr;
    if(realFrame<=safeUntil && !net::active)confFloor=realFrame;
    memset(haveTrue,0,sizeof(haveTrue));
    InterlockedExchange(&kb::noKO,0);InterlockedExchange(&kb::blocked,0);blockedAt=0;
    InterlockedExchange(&sc::gate,0);InterlockedExchange(&sc::blocked,0);eventBlockedAt=0;

    if(!net::enabled || (kTest && pass==2))NodesSet(x);else nNodes=0;
    cp::ReadAll(Ring(x));ringFrame[x%RING]=x;QueueSave(x);PhysSave(x);SeqSave(x);GroundSave(x);CamSave(x);PoseSave(x);

    effHead[x%RING]=Read(base+0x206C514);effN[x%RING]=static_cast<BYTE>(EffList(effSet[x%RING],EFFMAX));speedAt[x%RING]=*reinterpret_cast<const float*>(base+0xD2EA10);slowAt[x%RING]=*reinterpret_cast<const float*>(base+0xF9CEC0);memcpy(slowReq[x%RING],base+0xDD8FB4,12);slowDer[x%RING][0]=Read(base+0xF9CEBC);slowDer[x%RING][1]=Read(base+0x10879C0);CoreHashes(hashAt[K(x)]);ReadRaw(rawAt[K(x)]);decorAt[K(x)]=SaveDecor(decorRing[x%RING]);structAt[K(x)]=StructHash();NodesAt(x);
    seqCount[x%256]=static_cast<BYTE>(SeqList(seqNode[x%256]));
    pm[8]=PrepMs(pt);
    Logf("Labo ROLLBACK actif a partir de l'image %lu (retard %lu images, %u plages par photo, %lu octets) ; plages du coeur stables %u/%u (ecartees : %s) ; mots des blocs joueurs masques %lu/%lu.",
        x,delay,cp::count,ringBytes,static_cast<unsigned>(__popcnt(stableMask)),coreCount,len?names:"aucune",rawMasked,RAWSZ/4);
    pm[9]=PrepMs(pt);
    double tot=0;for(double v:pm)tot+=v;
    Logf("Labo : detail des plages : liberation %.1f, lecteur %.1f, globales %.1f, poses %.1f, animation %.1f, temps %.1f, canaux %.1f, physique %.1f, fenetres %.1f (%u plages), allocation %.1f, controle %.1f, lecture %.1f ; VirtualQuery %u appel(s), %u evite(s).",
        cp::prepT[0],cp::prepT[1],cp::prepT[2],cp::prepT[3],cp::prepT[4],cp::prepT[5],cp::prepT[6],cp::prepT[7],cp::prepT[8],cp::count,cp::prepT[9],cp::prepT[10],cp::prepT[11],cp::vqCalls,cp::vqHits);
    Logf("Labo : preparation en %.1f ms : plages %.1f, anneau %.1f, empreintes %.1f, decor %.1f (%u objets), blocs joueurs %.1f, bloc scene %.1f, objets du decor %.1f, journal %.1f, photo %.1f, journal %.1f.",
        tot,pm[0],pm[1],pm[2],pm[3],cp::blockCount,pm[4],pm[5],pm[6],pm[7],pm[8],pm[9]);
}
static void Compare(DWORD j) {
    FlowSuivi(j);
    if(pass==3){memcpy(confHash[K(j)],hashAt[K(j)],coreCount*4);++sOk;++tOk;net::OnConfirmed(j);return;}
    if(j>=REF_FRAMES || !refHave[j])return;
    const DWORD* ref=refHash+j*MAXCORE;const DWORD* now=hashAt[K(j)];DWORD bad=0;
    for(unsigned i=0;i<coreCount;++i)if((stableMask>>i&1) && ref[i]!=now[i])bad|=1u<<i;
    DWORD rawOff=0xFFFFFFFF;
    if(j<RAW_FRAMES){const BYTE* r=refRaw+static_cast<SIZE_T>(j)*RAWSZ;const BYTE* n=rawAt[K(j)];
        if(++scanAge>=600){scanAge=0;cp::ScanRegions();}
        for(DWORD o=0;o<RAWSZ;o+=4){if(rawMask[o] || !memcmp(r+o,n+o,4))continue;
            DWORD a=0,b=0;memcpy(&a,r+o,4);memcpy(&b,n+o,4);if(cp::PointerLike(a) || cp::PointerLike(b))continue;
            rawOff=o;break;}}
    if(kTest && pass==2 && j<RAW_FRAMES && j>=1 && refHave[j-1] && SceneVt()==0xBFC2E8) {
        static const DWORD off[4]={0x30,0x6C8+0x30,0x4F0,0x6C8+0x4F0};static const char* nom[4]={"J1 +30","J2 +30","J1 +4F0","J2 +4F0"};
        const BYTE* r=refRaw+static_cast<SIZE_T>(j)*RAWSZ;const BYTE* n=rawAt[K(j)];
        for(int i=0;i<4;++i){DWORD a=0,b=0;memcpy(&a,r+off[i],i<2?1:4);memcpy(&b,n+off[i],i<2?1:4);
            if(suiviVu && (a!=suiviRef[i] || b!=suiviRb[i]) && suiviLogs<300){++suiviLogs;
                Logf("Labo SUIVI %s image %lu : reference %lX (avant %lX), rollback %lX (avant %lX)%s.",nom[i],j,a,suiviRef[i],b,suiviRb[i],a!=b?" : DIFFERENT":"");}
            suiviRef[i]=a;suiviRb[i]=b;}
        suiviVu=true;
    }
    if(stageAddr && j<RAW_FRAMES && ringFrame[j%RING]==j) {
        const BYTE* r=refStage+static_cast<SIZE_T>(j)*STAGEMAX;const BYTE* n=stageRing+(j%RING)*STAGEMAX;
        char list[400];size_t len=0;list[0]=0;unsigned total=0;
        for(DWORD o=0;o<stageSize;o+=4) {
            if(stageMask[o/4] || !memcmp(r+o,n+o,4))continue;
            DWORD a=0,b=0;memcpy(&a,r+o,4);memcpy(&b,n+o,4);if(StagePointer(a,b))continue;
            if(++total<=8){const int w=_snprintf_s(list+len,sizeof(list)-len,_TRUNCATE," +%lX ref %08lX / %08lX",o,a,b);if(w>0)len+=w;}
        }
        if(total){++sStageBad;if(stageLogs<24){++stageLogs;Logf("Labo SCENE : bloc d'etat different de la reference a l'image confirmee %lu (%u mot(s)) :%s.",j,total,list);}}
    }
    NodesCompare(j);
    CitrRb(j);
    if(refDecor[j]!=decorAt[K(j)]){++sDecorBad;if(decorLogs<10){++decorLogs;Logf("Labo DECOR different de la reference a l'image confirmee %lu.",j);}}
    if(!bad && rawOff==0xFFFFFFFF){++sOk;++tOk;return;}
    if(bad)++sBadCore;else ++sBadRaw;
    ++tBad;if(!firstBad)firstBad=j;
    if(badLogs>=8)return;
    ++badLogs;char names[300];size_t len=0;names[0]=0;
    for(unsigned i=0;i<coreCount;++i)if(bad>>i&1){const int w=_snprintf_s(names+len,sizeof(names)-len,_TRUNCATE,"%s%s",len?", ":"",refCoreName[i]);if(w>0)len+=w;}
    if(rawOff!=0xFFFFFFFF) {
        const BYTE* r=refRaw+static_cast<SIZE_T>(j)*RAWSZ;const BYTE* n=rawAt[K(j)];DWORD a=0,b=0;memcpy(&a,r+rawOff,4);memcpy(&b,n+rawOff,4);
        Logf("Labo ECART image confirmee %lu : plages %s ; blocs joueurs : %s +%lX (joueur %lu +%lX) reference %08lX, rollback %08lX.",j,len?names:"aucune",
            rawOff<RAWHALF?"joueurs FD0540":rawOff<2*RAWHALF?"secondaires FCF788":"logique FCEE78",rawOff<2*RAWHALF?rawOff%RAWHALF:rawOff-2*RAWHALF,
            rawOff<2*RAWHALF?(rawOff%RAWHALF)/0x6C8:(rawOff-2*RAWHALF)/0x488,rawOff<2*RAWHALF?(rawOff%RAWHALF)%0x6C8:(rawOff-2*RAWHALF)%0x488,a,b);
    } else Logf("Labo ECART image confirmee %lu : plages %s.",j,names);
}

static void Inject() {
    if(pass!=2 || !prepared)return;
    BYTE* s=Slot(1);const DWORD j=nextFrame;const unsigned k=K(j);
    memcpy(p2true[k].b,s,SLOT);haveTrue[k]=true;
    const DWORD conf=Confirmed();
    if(j>conf) {
        In pred=p2true[K(conf)];memcpy(pred.b+4,pred.b,4);memset(pred.b+8,0,4);
        memcpy(s,pred.b,SLOT);++sPred;
    }
    memcpy(p2used[k].b,s,SLOT);
}

static void Frontier(BYTE* r) {
    ++cp::frontierCount;++tickInUpdate;
    const DWORD m=Read(base+0xFCE790);
    const bool fighting=r && m && ModeOk(m) && Read(base+0x1087A4C)==4 &&
        Read(reinterpret_cast<void*>(m+0xC))==reinterpret_cast<DWORD>(r);
    fightNow=fighting;
    if(!fighting){if(prepared)Unprepare("hors combat");lastClock=0;roundFrames=0;return;}
    const bool versus=Read(reinterpret_cast<void*>(m+8))==1;
    const DWORD x=versus?Read(reinterpret_cast<void*>(m+0x1C)):Read(r+0x2C);
    if(versus && (vlogs<3 || (prepared && x%600==0)) && x>0){++vlogs;Logf("Versus : image du gestionnaire %lu, de l'enregistreur %lu%s.",x,Read(r+0x2C),resim?" (recalcul)":"");}
    if(!versus && Read(reinterpret_cast<void*>(m+0x1C))!=x)return;
    if(!Alloc())return;
    {static bool f9;const bool k=kTest && !net::enabled && (GetAsyncKeyState(VK_F9)&0x8000)!=0;
        if(k && !f9){InterlockedExchange(&forget,1);Logf("Labo : F9 : la prochaine lecture sera une nouvelle REFERENCE.");}f9=k;}

    if(!resim && versus && (pass!=3 || x+60<lastSeen)) {
        pass=3;tOk=tBad=tRollbacks=firstBad=0;badLogs=0;lastCheck=0;checkPending=false;
        Logf("Labo : combat EN DIRECT (versus) : rollback en direct, entrees du J2 recues avec %lu images de retard.",delay);
        if(prepared)Unprepare("nouveau combat");roundFrames=0;lastClock=0;lastEvent=0;prepRetry=0;prepFails=0;
    }
    else if(kTest && !resim && !versus && (pass==0 || pass==3 || x+60<lastSeen)) {
        const DWORD id=ReplayIdentity(r);
        if(InterlockedExchange(&forget,0) || id!=replayId || !pass){replayId=id;pass=1;memset(refHave,0,REF_FRAMES);Logf("Labo : nouvelle lecture = REFERENCE (replay %08lX).",id);ambFrames=0;ambMask=0;for(DWORD& c:ambCnt)c=0;}
        else{pass=2;tOk=tBad=tRollbacks=firstBad=0;tFight=0;for(DWORD& v:tNp)v=0;badLogs=0;Logf("Labo : nouvelle lecture = ROLLBACK (meme replay).");for(int h=0;h<16;++h)heapBad[h]=false;++srPlay;autoArmed=false;autoReprepDone=false;autoN=0;autoVerdictAt=0;if(sondeAt){sondePhase=1;sondeTarget=sondeAt;sondeNow=false;}}
        if(prepared)Unprepare("nouvelle lecture");roundFrames=0;roundNo=0;lastClock=0;lastEvent=0;prepRetry=0;prepFails=0;
    }
    if(!resim)lastSeen=x;

    const bool fresh=!resim && x!=lastFrame;
    BYTE clock=0;Copy(&clock,base+0x10885DA,1);
    if(!prepared && InterlockedExchange(&sc::fired,0))lastEvent=x;
    if(fresh){if(clock>lastClock+2){if(prepared)Unprepare("nouveau round");roundFrames=0;++roundNo;lastEvent=0;prepRetry=0;prepFails=0;}lastClock=clock;++roundFrames;
        if(!prepared){const DWORD d=DecorHash();if(d==stableDecor)++stableFrames;else{stableDecor=d;stableFrames=0;}
            const DWORD sc0=CurrentScene();if(sc0==stableScene)++sceneFrames;else{stableScene=sc0;sceneFrames=0;}}}
    const bool decided=cp::RoundDecided();
    if(fresh && roundFrames<=1)graineFaite=false;

    if(fresh && !net::enabled && ((kTest && pass==1) || (kTest && pass==2)) && (roundNo<=1?x==59:roundFrames==60))GrainesEffets(x,roundNo<=1?"labo, image 59 du 1er round":"labo, 60e image du round");
    if((kTest && pass==1)) {

        if(prepared && fresh && stageAddr && !StageValid()){Unprepare("changement de zone (reference) : nouvelle preparation sur la zone d'arrivee");}
        if(!prepared){if(roundFrames>=250 && sceneFrames>=30 && (stableFrames>=5 || roundFrames>=300) && !decided && x>=prepRetry)PrepareReference(r,m,x);}
        if(prepared && !decided && x<REF_FRAMES && fresh) {
            CoreHashes(refHash+x*MAXCORE);if(x<RAW_FRAMES){ReadRaw(refRaw+static_cast<SIZE_T>(x)*RAWSZ);SaveStage(refStage+static_cast<SIZE_T>(x)*STAGEMAX);}refDecor[x]=DecorHash();NodesRef(x);refHave[x]=true;if(sondeRefAt && x==sondeRefAt)SondeRefScan(true,x);
            sc::AtFrame(x,x>0 && refHave[x-1] && refDecor[x]!=refDecor[x-1]);
            if(sc::Diag(x))DiagSeq(x,"REFERENCE");
            {static DWORD zPrev=0xFFFFFFFF,zAt;const DWORD z=CurrentScene();if(zAt+1==x && z!=zPrev && zPrev!=0xFFFFFFFF)sc::ZoneReport(x,zPrev,z);zPrev=z;zAt=x;}
        }
        if(prepared && decided){Unprepare("K.O. ou temps ecoule");}
        if(prepared && fresh)PinClock(x+1);
        sc::ctxFrame=static_cast<LONG>(x+1);sc::ctxConf=static_cast<LONG>(x);
        lastFrame=x;return;
    }
    if(pass!=2 && pass!=3)return;
    if(!updateCount){if(!noUpdateLogged){noUpdateLogged=true;Logf("Labo : les mises a jour du jeu ne sont PAS suivies (autre mod sur le meme point, Replay Takeover actif ?) : rollback desactive.");}lastFrame=x;return;}
    if(prepared && net::enabled && !net::active){Unprepare("phase en ligne terminee");lastFrame=x;return;}
    if(!prepared){if((!net::enabled || net::active) && roundFrames>=(pass==3?60u:((kTest && pass==2) && roundNo==1?prepApres1:250u)) && sceneFrames>=30 && (stableFrames>=5 || roundFrames>=(pass==3?90u:300u)) && !decided && x>=prepRetry && (pass==3 || (x<REF_FRAMES && refHave[x])))PrepareRollback(r,m,x);lastFrame=x;return;}
    if(x!=nextFrame){if(x==lastFrame && !resim)return;Logf("Labo : image %lu calculee, %lu attendue.",x,nextFrame);Unprepare("images non consecutives");return;}
    if(const char* why=QuickCheck()){Unprepare(why);return;}

    if(prepared && fresh && stageAddr && !StageValid() && !FramePredicted(x)){Unprepare("changement de zone : nouvelle preparation sur la zone d'arrivee");lastFrame=x;return;}
    {

        const DWORD* avant=seqNode[(x-1)%256];const bool prec=x>0 && ringFrame[(x-1)%RING]==x-1;const unsigned an=prec?seqCount[(x-1)%256]:0;
        seqCount[x%256]=static_cast<BYTE>(SeqList(seqNode[x%256]));
        {

            bool change=prec && seqCount[x%256]!=an;
            for(unsigned i=0;prec && !change && i<seqCount[x%256];++i){bool vu=false;for(unsigned k=0;k<an;++k)if(avant[k]==seqNode[x%256][i])vu=true;if(!vu)change=true;}
            if(change && x>dernierEvt)dernierEvt=x;
        }
        for(unsigned i=0;i<seqCount[x%256];++i){bool vu=false;for(unsigned k=0;k<an;++k)if(avant[k]==seqNode[x%256][i])vu=true;
            if(vu || !prec)continue;
            const DWORD until=(realFrame>x?realFrame:x)+WinLen();
            WinOpen(x,3);
            if(until>safeUntil){if(safeUntil<realFrame && safeLogs<30){++safeLogs;Logf("Labo : sequence scriptee lancee a l'image %lu : mode sans prediction jusqu'a l'image %lu.",x,until);}safeUntil=until;}
            break;}
    }
    cp::ReadAll(Ring(x));ringFrame[x%RING]=x;QueueSave(x);PhysSave(x);SeqSave(x);GroundSave(x);CamSave(x);PoseSave(x);effHead[x%RING]=Read(base+0x206C514);effN[x%RING]=static_cast<BYTE>(EffList(effSet[x%RING],EFFMAX));speedAt[x%RING]=*reinterpret_cast<const float*>(base+0xD2EA10);slowAt[x%RING]=*reinterpret_cast<const float*>(base+0xF9CEC0);memcpy(slowReq[x%RING],base+0xDD8FB4,12);slowDer[x%RING][0]=Read(base+0xF9CEBC);slowDer[x%RING][1]=Read(base+0x10879C0);CoreHashes(hashAt[K(x)]);ReadRaw(rawAt[K(x)]);decorAt[K(x)]=SaveDecor(decorRing[x%RING]);structAt[K(x)]=StructHash();NodesAt(x);
    if(sc::Diag(x) && (kTest && pass==2))DiagSeq(x,resim?"ROLLBACK recalcul":"ROLLBACK");
    if(sc::Diag(x) && (kTest && pass==2)) {
        const BYTE* rr=x<RAW_FRAMES && refHave[x]?refRaw+static_cast<SIZE_T>(x)*RAWSZ:nullptr;const BYTE* cr=rawAt[K(x)];
        auto W=[](const BYTE* p,DWORD o)->DWORD{DWORD v=0;if(p)memcpy(&v,p+o,4);return v;};
        DWORD s188=0,s190=0,s1A8=0,r188=0,r190=0,r1A8=0;
        if(stageAddr){s188=Read(reinterpret_cast<void*>(stageAddr+0x188));s190=Read(reinterpret_cast<void*>(stageAddr+0x190));s1A8=Read(reinterpret_cast<void*>(stageAddr+0x1A8));
            if(x<RAW_FRAMES && refHave[x]){const BYTE* rs=refStage+static_cast<SIZE_T>(x)*STAGEMAX;memcpy(&r188,rs+0x188,4);memcpy(&r190,rs+0x190,4);memcpy(&r1A8,rs+0x1A8,4);}}
        DWORD sn[SEQMAX];const unsigned ns=SeqList(sn);
        Logf("DIAG image %lu%s (confirmee %lu) : J2 utilise %08lX vraie %08lX ; J1 +C %08lX/%08lX +10 %08lX/%08lX +14 %08lX/%08lX ; J2 +C %08lX/%08lX ; seq %u ; scene +188 %lX/%lX +190 %lX/%lX +1A8 %lX/%lX (actuel/reference).",
            x,resim?" RECALCUL":"",Confirmed(),*reinterpret_cast<const DWORD*>(p2used[K(x)].b),*reinterpret_cast<const DWORD*>(p2true[K(x)].b),
            W(cr,0xC),W(rr,0xC),W(cr,0x10),W(rr,0x10),W(cr,0x14),W(rr,0x14),W(cr,0x6C8+0xC),W(rr,0x6C8+0xC),ns,s188,r188,s190,r190,s1A8,r1A8);
    }
    if(stageAddr){SaveStage(stageRing+(x%RING)*STAGEMAX);PhotoListe(x);}
    SaveExtra(x);
    if(stageAddr && x>0 && ringFrame[(x-1)%RING]==x-1) {
        const BYTE* a=stageRing+((x-1)%RING)*STAGEMAX;const BYTE* b=stageRing+(x%RING)*STAGEMAX;
        for(DWORD k=0;k<stageSize;k+=4){DWORD p=0,q=0;memcpy(&p,a+k,4);memcpy(&q,b+k,4);

            if(p!=q && p && q && StagePointer(p,q)){++sStructSeen;WinOpen(x,2);const bool labo=Read(reinterpret_cast<void*>(stageAddr))==reinterpret_cast<DWORD>(base)+0x9A0C8C;
                const DWORD until=realFrame+(labo?60:WinLen());
                if(until>safeUntil){if(safeUntil<realFrame && safeLogs<30){++safeLogs;Logf("Labo : structure de la scene changee a l'image %lu (+%lX) : mode sans prediction jusqu'a l'image %lu.",x,k,until);}safeUntil=until;}
                break;}}
    }
    nextFrame=x+1;lastFrame=x;
    if(!resim)advancedNow=true;
    if(InterlockedExchange(&kb::blocked,0)){++sKoBlocked;if(!blockedAt || x<blockedAt)blockedAt=x;}
    const bool evNow=InterlockedExchange(&sc::blocked,0)!=0;
    if(evNow){++sEvBlocked;if(!eventBlockedAt || x<eventBlockedAt)eventBlockedAt=x;}
    bool evFired=false;
    const bool firedNow=InterlockedExchange(&sc::fired,0)!=0;
    if(firedNow && resim && !evNow && eventBlockedAt && x==eventBlockedAt) {
        static unsigned dblLogs;if(dblLogs<20 || sc::Diag(x)){++dblLogs;Logf("Labo SCENE : evenement bloque de l'image %lu execute pendant un recalcul : pas de 2e rejeu.",x);}
        eventBlockedAt=0;}
    if(firedNow && x>dernierEvt)dernierEvt=x;
    if(firedNow || eventBlockedAt) {
        evFired=true;WinOpen(x,1);
        const DWORD until=(realFrame>x?realFrame:x)+WinLen();
        if(until>safeUntil){if(safeUntil<realFrame && safeLogs<30){++safeLogs;Logf("Labo : evenement de scene a l'image %lu : mode sans prediction jusqu'a l'image %lu.",x,until);}safeUntil=until;}
    }
    if(!resim) {
        unsigned sig=0;
        if(x>0 && ringFrame[(x-1)%RING]==x-1){
            if(decorAt[K(x)]!=decorAt[K(x-1)])sig|=1;
            if(structAt[K(x)]!=structAt[K(x-1)])sig|=2;
            if(decorRing[x%RING].scene!=decorRing[(x-1)%RING].scene)sig|=4;
            if(stageAddr){const BYTE* a=stageRing+((x-1)%RING)*STAGEMAX;const BYTE* b=stageRing+(x%RING)*STAGEMAX;
                for(DWORD k=0;k<stageSize;k+=4){DWORD p=0,q=0;memcpy(&p,a+k,4);memcpy(&q,b+k,4);if(p!=q && p && q && StagePointer(p,q)){sig|=8;break;}}}}
        if(ActiveSeqs())sig|=16;
        curSig=sig;
        if(!winOpen && realFrame>safeUntil && !evFired && !eventBlockedAt) {
            ++ambFrames;for(int b=0;b<5;++b)if(sig>>b&1)++ambCnt[b];
            if(ambFrames>=60 && ambFrames%30==0){unsigned m=0;for(int b=0;b<5;++b)if(ambCnt[b]*2>=ambFrames)m|=1u<<b;
                if(m!=ambMask){ambMask=m;if(ambLogs<20){++ambLogs;char t[120];size_t n=0;t[0]=0;for(int b=0;b<5;++b)if(m>>b&1){const int w=_snprintf_s(t+n,sizeof(t)-n,_TRUNCATE,"%s%s",n?", ":"",SIG_NOMS[b]);if(w>0)n+=w;}
                    Logf("Labo SIGNAUX AMBIANTS (apres %lu images de calme) : %s%s.",ambFrames,n?t:"aucun",ambiantOn?"":" (non utilises : Ambiant=0)");}}}
        }
    }
    if(winOpen && !resim) {
        bool act=evFired || eventBlockedAt!=0;
        for(int b=0;b<5;++b)if(curSig>>b&1)++winCnt[b];
        if(curSig & ~(ambiantOn?ambMask:0u))act=true;
        if(act)winLastAct=x;
        else if(x>=winLastAct+stableNeed) {
            const DWORD suites=winLastAct>winStart?winLastAct-winStart:0,capEnd=winStart+safeFrames;
            ++sWinCount;sWinSum+=suites;if(suites>sWinMax)sWinMax=suites;
            const bool early=finDetectee && safeUntil>realFrame && !NoPredictStage() && !FixedWindowZone();
            if(early){sWinSaved+=safeUntil-realFrame;safeUntil=realFrame;++sWinEarly;}
            if(winLogs<80 || sc::Diag(x)){++winLogs;Logf("Labo MESURE : %s a l'image %lu : suites jusqu'a %lu (%lu image(s)), scene calme depuis %lu images a %lu ; fenetre fixe jusqu'a %lu%s ; signaux decor %lu, structure %lu, zone %lu, pointeur %lu, sequence %lu (ambiants %X).",
                winOrigin==1?"evenement de scene":winOrigin==2?"changement de structure":"sequence scriptee",winStart,winLastAct,suites,stableNeed,x,capEnd,early?" -> FIN ANTICIPEE, prediction reprise":"",
                winCnt[0],winCnt[1],winCnt[2],winCnt[3],winCnt[4],ambMask);}
            winOpen=false;
        }
    }
    if(decided){Logf("Labo : K.O. ou temps ecoule a l'image %lu (entrees confirmees jusqu'a %lu).",x,Confirmed());Unprepare("fin du round");return;}
    if(sondeRefAt && x==sondeRefAt && (kTest && pass==2) && srHave && x<=Confirmed()){static DWORD done;if(done!=x+0x10000*tRollbacks){done=x+0x10000*tRollbacks;SondeRefScan(false,x);}}
    HeapCheck("fin d'image",x);
    PinClock(x+1);
    InterlockedExchange(&kb::noKO,FramePredicted(x)?1:0);

    {bool pred=FramePredicted(x+1);
     if(pred && net::active && x==realFrame && !resim && !rollbackPlanned && net::verrouCourant){pred=false;net::verrouImage=x+1;++sLockNext;}
     InterlockedExchange(&sc::gate,pred?1:0);}
    sc::ctxFrame=static_cast<LONG>(x+1);sc::ctxConf=static_cast<LONG>(ConfirmedNext());
    if(rollbackPlanned && tickInUpdate==1) {
        rollbackPlanned=false;
        if(sondeNow)SondeBefore();
        HeapCheck("avant le retour",x);TimerCheck("avant le retour",x);
        if(sc::Diag(x) || sc::Diag(rollbackTo))Logf("DIAG retour : image perdue %lu, retour a %lu, recalcul de %lu a %lu.",x,rollbackTo,rollbackTo+1,x);
        const bool haveTo=ringFrame[rollbackTo%RING]==rollbackTo;
        const bool stateChanged=haveTo && decorAt[K(x)]!=decorAt[K(rollbackTo)];
        const bool structChanged=haveTo && (structAt[K(x)]!=structAt[K(rollbackTo)] || decorRing[x%RING].scene!=decorRing[rollbackTo%RING].scene);

        const bool sceneChanged=haveTo && decorRing[x%RING].scene!=decorRing[rollbackTo%RING].scene;
        const bool homeStage=stageAddr && Read(reinterpret_cast<void*>(stageAddr))==reinterpret_cast<DWORD>(base)+0xBF1C94;
        if(sceneChanged)++sZoneCross;
        if(sceneChanged && !homeStage && zoneLogs<20){++zoneLogs;Logf("Labo DECOR : retour de %lu a %lu a travers un changement de zone hors HOME : pas de reconstruction.",x,rollbackTo);}
        const bool decorChanged=sceneChanged && homeStage;
        if(stateChanged && !structChanged){++sStateOnly;if(decorLogs<12 && false){++decorLogs;char a[160],b[160];Hex(decorRing[rollbackTo%RING],a,sizeof(a));Hex(decorRing[x%RING],b,sizeof(b));
            Logf("Labo DECOR : retour de %lu a %lu : seul l'etat du decor a change (structure identique, scene %lu) : %s -> %s ; pas de reconstruction.",x,rollbackTo,decorRing[x%RING].scene,a,b);}}
        if(decorChanged && decorLogs<12){++decorLogs;char a[160],b[160];Hex(decorRing[rollbackTo%RING],a,sizeof(a));Hex(decorRing[x%RING],b,sizeof(b));
            Logf("Labo DECOR : retour de %lu a %lu : decor change (%s ; scenes %lu -> %lu) : %s -> %s.",x,rollbackTo,structChanged?"structure":"etat",decorRing[rollbackTo%RING].scene,decorRing[x%RING].scene,a,b);}
        double ms=0;bool rebuilt=false;
        if(decorChanged)rebuilt=Rebuild(decorRing[rollbackTo%RING],ms);

        const DWORD roundObjLive=Read(base+0xFCDDCC);
        const BYTE roundFlagLive=base[0xFCDE54];static unsigned roundFlagLogs;
        if(ringFrame[rollbackTo%RING]==rollbackTo && cp::WriteAll(Ring(rollbackTo))) {
            {const DWORD restored=Read(base+0xFCDDCC);
             if(roundObjLive && restored!=roundObjLive){*reinterpret_cast<DWORD*>(base+0xFCDDCC)=roundObjLive;++sRoundObjKept;
                if(sRoundObjKept<=10)Logf("Labo : retour %lu -> %lu : objet d'etat du round different dans la photo (%08lX, actuel %08lX) : actuel garde.",x,rollbackTo,restored,roundObjLive);}}
            if(base[0xFCDE54]!=roundFlagLive && roundFlagLogs<10){++roundFlagLogs;Logf("Labo : retour %lu -> %lu a travers la bascule du round (DE54 %u dans la photo, %u avant le retour) : NE DEVRAIT PLUS ARRIVER.",x,rollbackTo,base[0xFCDE54],roundFlagLive);}
            const DWORD depth=x-rollbackTo;++sRollbacks;++tRollbacks;sDepth+=depth;if(depth>sDepthMax)sDepthMax=depth;
            if(decorChanged) {
                ++sDecorCross;if(rebuilt){LoadDecor(decorRing[rollbackTo%RING]);++sDecorRestored;}
                if(decorLogs<10){++decorLogs;Logf("Labo DECOR : retour de l'image %lu a %lu a travers une casse : %s (%.2f ms).",x,rollbackTo,rebuilt?"scene reconstruite et etat du decor recharge":"REFUS de la reconstruction",ms);}
            }
            HeapCheck("apres la photo",x);TimerCheck("apres la photo",x);
            if(SeqGuardZone())QueueRestore(rollbackTo,x);
            SeqRestore(rollbackTo,x);
            GroundRestore(rollbackTo,x);
            CamRestore(rollbackTo,x);
            PoseRestore(rollbackTo,x);
            PhysRestore(rollbackTo,x);
            if(SeqGuardZone() && eventBlockedAt>rollbackTo)eventBlockedAt=0;
            RestoreStage(rollbackTo);
            HeapCheck("apres le bloc de la scene",x);
            if(effetsAnnules || SceneVt()==0xBEC570) {
                DWORD now[EFFMAX];const unsigned nn=EffList(now,EFFMAX);const DWORD* then=effSet[rollbackTo%RING];const unsigned tn=effN[rollbackTo%RING];
                unsigned created=0,killed=0,gone=0;
                for(unsigned i=0;i<nn;++i){bool was=false;for(unsigned j=0;j<tn;++j)if(then[j]==now[i]){was=true;break;}if(was)continue;++created;
                    __try{if(*reinterpret_cast<DWORD*>(now[i]+4)){*reinterpret_cast<DWORD*>(now[i]+4)=0;++killed;}}__except(EXCEPTION_EXECUTE_HANDLER){}}
                for(unsigned j=0;j<tn;++j){bool still=false;for(unsigned i=0;i<nn;++i)if(then[j]==now[i]){still=true;break;}if(!still)++gone;}
                sEffKilled+=killed;
                if((created || gone) && (effLogs<60 || sc::Diag(x))){++effLogs;Logf("Labo EFFETS : retour %lu -> %lu : %u effet(s) vivants (photo %u) ; %u cree(s) depuis (%u desactive(s)) ; %u MORT(S) depuis l'image visee.",x,rollbackTo,nn,tn,created,killed,gone);}
            }
            if(ralentiRemis) {
                float* sp=reinterpret_cast<float*>(base+0xD2EA10);float* sl=reinterpret_cast<float*>(base+0xF9CEC0);
                const float sp0=speedAt[rollbackTo%RING],sl0=slowAt[rollbackTo%RING];const float spNow=*sp,slNow=*sl;bool did=false;
                if(sp0>0.999f && sp0<1.001f && (spNow<0.999f || spNow>1.001f)){*sp=sp0;did=true;}
                if(sl0>0.999f && sl0<1.001f && (slNow<0.999f || slNow>1.001f)){*sl=sl0;did=true;
                    memcpy(base+0xDD8FB4,slowReq[rollbackTo%RING],12);*reinterpret_cast<DWORD*>(base+0xF9CEBC)=slowDer[rollbackTo%RING][0];*reinterpret_cast<DWORD*>(base+0x10879C0)=slowDer[rollbackTo%RING][1];}
                if(did){++sSlowReset;if(slowLogs<30 || sc::Diag(x)){++slowLogs;Logf("Labo : retour %lu -> %lu a travers le debut d'un ralenti (vitesse %.4f, facteur %.4f) : remis a 1 (demande du ralenti remise aussi).",x,rollbackTo,spNow,slNow);}}
            }
            {
                DWORD now[SEQMAX];const unsigned n=SeqList(now);const DWORD* then=seqNode[rollbackTo%256];const unsigned tn=seqCount[rollbackTo%256];
                for(unsigned i=0;i<n;++i){bool was=false;for(unsigned k=0;k<tn;++k)if(then[k]==now[i])was=true;
                    if(was)continue;BYTE act=0;Copy(&act,reinterpret_cast<void*>(now[i]+0xC),1);if(!act)continue;
                    const DWORD id=Read(reinterpret_cast<void*>(now[i]+8));
                    __try{*reinterpret_cast<BYTE*>(now[i]+0xC)=0;}__except(EXCEPTION_EXECUTE_HANDLER){continue;}
                    ++sSeqKilled;if(seqLogs<20){++seqLogs;Logf("Labo : retour %lu -> %lu : sequence scriptee %lu lancee dans une image predite annulee (le recalcul la relance une seule fois).",x,rollbackTo,id);}}
            }
            HeapCheck("apres le retour",x);TimerCheck("apres le retour",x);
            resim=true;resimEnd=resimTarget?resimTarget:x;resimTarget=0;nextFrame=rollbackTo+1;lastFrame=rollbackTo;
            PinClock(rollbackTo+1);
            InterlockedExchange(&kb::noKO,rollbackTo>Confirmed()?1:0);
            InterlockedExchange(&sc::gate,rollbackTo+1>Confirmed()?1:0);
            sc::ctxFrame=static_cast<LONG>(rollbackTo+1);sc::ctxConf=static_cast<LONG>(Confirmed());
        } else ++sSkip;
        return;
    }
    if(evNow && net::active && x>Confirmed() && !cutRest) {
        InterlockedExchange(&cutRest,1);++sCut;
        if(cutLogs<20){++cutLogs;Logf("Labo SCENE : evenement de scene dans l'image predite %lu (confirmee %lu)%s : pas suivants de cette mise a jour sautes, attente de la confirmation.",x,Confirmed(),resim?" pendant un recalcul":"");}
        if(resim){resim=false;resimEnd=x;}
    }
    if(resim && x==resimEnd){resim=false;lastFrame=x;if(sondeNow){sondeNow=false;SondeAfter();}}
}
static DWORD ReplayPendingFrom(){DWORD f=0;if(eventBlockedAt)f=eventBlockedAt;if(blockedAt && (!f || blockedAt<f))f=blockedAt;return f;}
static void InputsDiffer(DWORD j,bool& differ){differ=memcmp(p2true[K(j)].b,p2used[K(j)].b,SLOT)!=0;}

static bool FightingNow(BYTE* r) {
    const DWORD m=Read(base+0xFCE790);
    return r && m && ModeOk(m) && Read(base+0x1087A4C)==4 && Read(reinterpret_cast<void*>(m+0xC))==reinterpret_cast<DWORD>(r);
}
static void HeapWhere(DWORD a,char* out,size_t cap){
    for(unsigned r=0;r<cp::count;++r){const DWORD a0=reinterpret_cast<DWORD>(cp::ranges[r].address);if(a>=a0-0x40 && a<a0+cp::ranges[r].size+0x40){_snprintf_s(out,cap,_TRUNCATE,"plage photographiee '%s' %+ld",cp::ranges[r].name,static_cast<long>(a-a0));return;}}
    if(stageAddr && a>=stageAddr-0x40 && a<stageAddr+stageSize+0x40){_snprintf_s(out,cap,_TRUNCATE,"bloc de la scene %+ld",static_cast<long>(a-stageAddr));return;}
    for(unsigned i=0;i<RING;++i)for(unsigned j=0;j<effN[i];++j){const DWORD e=effSet[i][j];if(a>=e-0x40 && a<e+0x200){_snprintf_s(out,cap,_TRUNCATE,"effet de la photo de l'image %lu %+ld",ringFrame[i],static_cast<long>(a-e));return;}}
    {DWORD node=Read(base+0x206C514);unsigned k=0;while(node && k<1024){const DWORD e=Read(reinterpret_cast<void*>(node+8));if(e && a>=e-0x40 && a<e+0x200){_snprintf_s(out,cap,_TRUNCATE,"effet vivant %+ld",static_cast<long>(a-e));return;}
        if(a>=node-0x40 && a<node+0x34){_snprintf_s(out,cap,_TRUNCATE,"maillon d'effet vivant %+ld",static_cast<long>(a-node));return;}node=Read(reinterpret_cast<void*>(node));++k;}}
    _snprintf_s(out,cap,_TRUNCATE,"hors photo");
}
static void HeapCheckIn(const char* when,DWORD x);

static void HeapCheck(const char* when,DWORD x){
    if constexpr(kTest){
        const DWORD g=Read(base+0x2080934);if(!g || !heapN)return;
        CRITICAL_SECTION* cs=reinterpret_cast<CRITICAL_SECTION*>(g+0x6C);EnterCriticalSection(cs);HeapCheckIn(when,x);LeaveCriticalSection(cs);
    } else {(void)when;(void)x;(void)&HeapCheckIn;}
}
static void HeapCheckIn(const char* when,DWORD x){
    const LONG n=heapN<16?heapN:16;
    for(LONG h=0;h<n;++h){if(heapBad[h])continue;const DWORD hp=heapList[h];if(!hp)continue;
        const char* why=nullptr;DWORD bad=0,prv=0,bucket=0,w4=0,w8=0,wc=0;
        __try{
            if(!*reinterpret_cast<const DWORD*>(hp+0x10))continue;
            const DWORD tbl=*reinterpret_cast<const DWORD*>(hp+0x1C),nb=*reinterpret_cast<const DWORD*>(hp+0x24),lo=*reinterpret_cast<const DWORD*>(hp+0x14),hi=*reinterpret_cast<const DWORD*>(hp+0x18);
            if(nb>4096)continue;
            for(DWORD b=0;b<nb && !why;++b){DWORD node=*reinterpret_cast<const DWORD*>(tbl+b*4),prev=0,steps=0;
                while(node){
                    if(node<lo || node>=hi){why="maillon hors du tas";}
                    else if(*reinterpret_cast<const DWORD*>(node+8)!=prev){why="lien arriere faux";}
                    else if(*reinterpret_cast<const LONG*>(node+4)<0){why="bloc OCCUPE dans la liste libre";}
                    else if(++steps>300000){why="CYCLE";}
                    if(why){bad=node;prv=prev;bucket=b;if(node>=lo && node<hi){w4=*reinterpret_cast<const DWORD*>(node+4);w8=*reinterpret_cast<const DWORD*>(node+8);wc=*reinterpret_cast<const DWORD*>(node+0xC);}break;}
                    prev=node;node=*reinterpret_cast<const DWORD*>(node+0xC);}}
        }__except(EXCEPTION_EXECUTE_HANDLER){why="lecture impossible";}
        if(!why)continue;
        heapBad[h]=true;if(heapLogs>=20)continue;++heapLogs;
        char w1[120],w2[120];HeapWhere(bad,w1,sizeof w1);HeapWhere(prv,w2,sizeof w2);
        Logf("TAS CASSE (%s, image %lu, %s, passe %d) : tas %ld seau %lu : %s ; maillon %08lX (%s) [+4 %08lX +8 %08lX +C %08lX], precedent %08lX (%s).",
            when,x,resim?"recalcul":"normal",pass,h,bucket,why,bad,w1,w4,w8,wc,prv,w2);
    }
}
static void TimerCheck(const char* when,DWORD x){
    DWORD seen[512];unsigned n=0;DWORD* link=reinterpret_cast<DWORD*>(base+0xF91230);DWORD node=0,cut=0,to=0;
    __try{
        while((node=*link)!=0){
            bool loop=false;for(unsigned i=0;i<n;++i)if(seen[i]==node){loop=true;break;}
            if(loop){cut=reinterpret_cast<DWORD>(link)-4;to=node;*link=0;*reinterpret_cast<DWORD**>(base+0xCC4720)=link;break;}
            if(n>=512)return;
            seen[n++]=node;link=reinterpret_cast<DWORD*>(node+4);
        }
    }__except(EXCEPTION_EXECUTE_HANDLER){return;}
    if(!cut)return;
    ++sTimerCut;if(timerLogs>=40)return;++timerLogs;
    char w1[120],w2[120];HeapWhere(cut,w1,sizeof w1);HeapWhere(to,w2,sizeof w2);
    float t=0;DWORD act=0;Copy(&t,reinterpret_cast<void*>(cut+8),4);act=Read(reinterpret_cast<void*>(cut+0xC));
    char a[32]="?";if(act>=reinterpret_cast<DWORD>(base))_snprintf_s(a,sizeof a,_TRUNCATE,"game+%06lX",act-reinterpret_cast<DWORD>(base));
    Logf("MINUTERIES (%s, image %lu, %s) : CYCLE coupe apres %u maillon(s) : maillon %08lX (%s ; temps %.3f, action %s) -> %08lX (%s)%s.",
        when,x,resim?"recalcul":"normal",n,cut,w1,t,a,to,w2,cut==to?" = LUI-MEME (minuterie terminee restee dans la liste)":"");
}
static void UpdateStart() {
    InterlockedIncrement(&updateCount);
    sceneDone=false;
    if(rollbackPlanned)++sSkip;
    if(resim){Logf("Labo : recalcul incomplet (image %lu attendue, fin %lu).",nextFrame,resimEnd);Unprepare("recalcul incomplet");}
    tickInUpdate=0;rollbackPlanned=false;advancedLast=advancedNow;advancedNow=false;
    InterlockedExchange(&cutRest,0);
    LONG extra=0;
    if(sel::Tick()) {
        InterlockedExchange(&g_selHold,1);InterlockedExchange(&extraNow,-1);
        if(!qpf.QuadPart)QueryPerformanceFrequency(&qpf);
        QueryPerformanceCounter(&updateStart);return;
    }
    InterlockedExchange(&g_selHold,0);
    if(net::UpdateHook()) {
        InterlockedExchange(&extraNow,-1);
        if(!qpf.QuadPart)QueryPerformanceFrequency(&qpf);
        QueryPerformanceCounter(&updateStart);return;
    }
    if(((kTest && pass==2) || pass==3) && prepared && (advancedLast || net::active) && !base[0x10879B1]) {
        if(autoArmed && sondePhase==1 && sondeTarget==autoVerdictAt && !resim && autoN && !autoReprepDone){autoReprepDone=true;Unprepare("sonde automatique : re-preparation");
            if(!qpf.QuadPart)QueryPerformanceFrequency(&qpf);QueryPerformanceCounter(&updateStart);InterlockedExchange(&extraNow,0);return;}
        realFrame=lastFrame+1;
        PinClock(realFrame);
        if(realFrame<=safeUntil){if(!net::active)confFloor=realFrame;++sSafeFrames;}
        {const bool fightOn=base[0xFCDE54]!=0,nps=fightOn && NoPredictStage(),nc=fightOn && !nps && NearCinematic(realFrame);
         if(!net::active && (!fightOn || nps || nc || (sondeRefAt && (srPlay==1 || SondeProche()))))confFloor=realFrame;
         npAt[realFrame%RING]=static_cast<BYTE>(realFrame<=safeUntil || !fightOn || nps || nc);
         if((kTest && pass==2) && fightOn){++sFight;++tFight;int c=-1;if(realFrame<=safeUntil)c=0;else if(nps)c=1;
             else if(nc)c=ncFlags&1?2:ncFlags&2?3:ncFlags&4?4:ncFlags&8?5:6;
             if(c>=0){++sNp[c];++tNp[c];}}}
        const DWORD conf=Confirmed();
        DWORD m=0;
        for(DWORD j=lastConfirmed+1;j<=conf && j<=lastFrame;++j){bool d=false;if(haveTrue[K(j)])InputsDiffer(j,d);if(d){m=j;++sMiss;break;}}
        if(conf>lastConfirmed)lastConfirmed=conf;
        if(blockedAt && blockedAt-1<=conf){if(!m || blockedAt<m)m=blockedAt;++sKoReplayed;blockedAt=0;}
        const DWORD ev=eventBlockedAt;
        if(eventBlockedAt && eventBlockedAt<=conf){if(!m || eventBlockedAt<m)m=eventBlockedAt;++sEvReplayed;replayCutAt=eventBlockedAt;eventBlockedAt=0;}
        if(base[0xFCDE54]!=roundFlagLast){roundFlagLast=base[0xFCDE54];roundFlagAt=realFrame;}
        if(CinematicNow())cineLast=realFrame;
        if(pass==3 && !m && !checkPending && realFrame>safeUntil && realFrame-lastCheck>=300 && lastCompared>prepFrame+8 && base[0xFCDE54] && lastCompared>roundFlagAt+10 && !net::active && !NoPredictStage() && !CinematicNow() && lastCompared>cineLast+CINE_TAIL+10) {
            m=lastCompared-5;checkFrom=m;checkTo=lastCompared;checkPending=true;lastCheck=realFrame;
        }
        if((kTest && pass==2) && !m && (sondePhase==1 || sondePhase==2) && realFrame>=sondeTarget && realFrame>prepFrame+2 && ringFrame[(realFrame-1)%RING]==realFrame-1 && !CinematicNow()){
            m=realFrame;sondeNow=true;sondeTarget=realFrame;Logf("SONDE : retour force de 0 image a l'image %lu (memes entrees).",realFrame);}
        if((kTest && pass==2) && !m && retoursForces && realFrame>prepFrame+profForcee+2 && realFrame%retoursForces==0 && !CinematicNow()){
            const DWORD mm=realFrame-profForcee+1;

            bool np=false;for(DWORD j=mm;j<=realFrame;++j)if(npAt[j%RING])np=true;
            if(np){++sForcesNp;if(npLogs<20){++npLogs;Logf("Labo : retour force evite a l'image %lu (image sans prediction entre %lu et %lu ; %lu depuis le debut).",realFrame,mm,realFrame,sForcesNp);}}
            else if(dernierEvt && mm<=dernierEvt){++sForcesEvites;if(evitesLogs<40){++evitesLogs;Logf("Labo : retour force evite a l'image %lu (evenement ou sequence a l'image %lu ; %lu evite(s) depuis le debut).",realFrame,dernierEvt,sForcesEvites);}}
            else if(ringFrame[(mm-1)%RING]==mm-1){m=mm;++sForces;
                if(forceLogs<10){++forceLogs;Logf("Labo : RETOUR FORCE de %lu image(s) a l'image %lu (memes entrees ; %lu depuis le debut).",profForcee,realFrame,sForces);}}}
        const bool ok=m && realFrame-m+1<RING && ringFrame[(m-1)%RING]==m-1;
        if(ok){rollbackTo=m-1;rollbackPlanned=true;extra=static_cast<LONG>(realFrame-m+1);resimTarget=0;
            if(replayCutAt && replayCutAt>=m && replayCutAt<realFrame){
                extra=static_cast<LONG>(replayCutAt-m+1);resimTarget=replayCutAt;++sReplayCut;
                if(replayCutLogs<20 || sc::Diag(replayCutAt)){++replayCutLogs;Logf("Labo : rejeu de l'evenement de l'image %lu : recalcul de %lu a %lu seulement, puis une image par mise a jour.",replayCutAt,m,replayCutAt);}}}
        replayCutAt=0;
        if(sc::Diag(realFrame) || (m && sc::Diag(m)))Logf("DIAG maj : image %lu, confirmee %lu, sans prediction jusqu'a %lu ; m=%lu%s%s.",realFrame,conf,safeUntil,m,
            m?(ok?" -> retour planifie a ":" -> RETOUR IMPOSSIBLE (anneau)"):"",m&&ok?(rollbackTo==m-1?"m-1":""):"");
        if(ev && ev<=conf && evLogs<40){++evLogs;Logf("Labo SCENE : evenement ignore a l'image %lu, maintenant confirmee (%lu) : %s (retour a %lu, image affichee %lu).",ev,conf,ok?"rejeu":"REJEU IMPOSSIBLE",m?m-1:0,realFrame);}
        InterlockedExchange(&kb::noKO,lastFrame>conf?1:0);
        InterlockedExchange(&sc::gate,lastFrame+1>conf?1:0);
        sc::ctxFrame=static_cast<LONG>(lastFrame+1);sc::ctxConf=static_cast<LONG>(conf);
    }
    InterlockedExchange(&extraNow,extra);
    if(!qpf.QuadPart)QueryPerformanceFrequency(&qpf);
    QueryPerformanceCounter(&updateStart);
}
static void UpdateEnd() {
    LARGE_INTEGER t;QueryPerformanceCounter(&t);
    net::Report();
    if((pass!=2 && pass!=3) || !prepared)return;
    const double ms=double(t.QuadPart-updateStart.QuadPart)*1000.0/double(qpf.QuadPart);
    ++sUpdates;sTicks+=1+extraNow;sMs+=ms;if(ms>sMaxMs)sMaxMs=ms;
    if(checkPending && !resim) {
        checkPending=false;DWORD bad=0;DWORD first=0;
        for(DWORD j=checkFrom;j<=checkTo;++j)for(unsigned i=0;i<coreCount;++i)if(confHash[K(j)][i]!=hashAt[K(j)][i]){bad|=1u<<i;if(!first)first=j;}
        if(!bad)++sChkOk;
        else{++sChkBad;if(chkLogs<12){++chkLogs;char names[300];size_t len=0;names[0]=0;
            for(unsigned i=0;i<coreCount;++i)if(bad>>i&1){const int w=_snprintf_s(names+len,sizeof(names)-len,_TRUNCATE,"%s%s",len?", ":"",cp::ranges[coreIdx[i]].name);if(w>0)len+=w;}
            Logf("Labo DIRECT : verification a blanc %lu-%lu : RECALCUL DIFFERENT des l'image %lu (%s).",checkFrom,checkTo,first,names);}}
    }
    const DWORD conf=Confirmed();
    DWORD lim=conf;{const DWORD pend=ReplayPendingFrom();if(pend && pend<=lim)lim=pend-1;}
    for(DWORD j=lastCompared+1;j<=lim && j<=lastFrame;++j)Compare(j);
    {const DWORD c=lim<lastFrame?lim:lastFrame;if(c>lastCompared)lastCompared=c;}
    const DWORD now=GetTickCount();
    if(now-lastReport<3000)return;
    lastReport=now;
    Logf("Labo : %lu maj (%lu pas), moyenne %.2f ms, max %.2f ms ; %lu rollbacks (profondeur moyenne %.1f, max %lu), %lu images predites, %lu mauvaises predictions ; images confirmees : %lu identiques, %lu ecarts (coeur %lu, blocs joueurs %lu) ; retours sautes %lu.",
        sUpdates,sTicks,sUpdates?sMs/sUpdates:0.0,sMaxMs,sRollbacks,sRollbacks?double(sDepth)/sRollbacks:0.0,sDepthMax,sPred,sMiss,sOk,sBadCore+sBadRaw,sBadCore,sBadRaw,sSkip);
    if(sEvBlocked||sEvReplayed){Logf("  Scene : %lu evenement(s) (casses, dangers) bloque(s) dans des images predites, %lu rejoue(s) une fois confirme(s).",sEvBlocked,sEvReplayed);sEvBlocked=sEvReplayed=0;}
    if(sStageRestores||sStageBad||sStageSkipped){char top[300];StageTop(top,sizeof(top));
        Logf("  Scene (bloc d'etat) : %lu retour(s) avec remise (%lu mots, %lu non remis), %lu image(s) confirmee(s) differente(s) de la reference ; mots remis :%s.",sStageRestores,sStageWords,sStageSkipped,sStageBad,top);
        sStageRestores=sStageWords=sStageSkipped=sStageBad=0;}
    if(sSceneCalls){Logf("  Scene : %lu mise(s) a jour de la scene par pas (dt 1 ; dernier dt natif %.4f) ; %lu mot(s) d'objets du decor remis.",sSceneCalls,lastDt,sExWords);sSceneCalls=0;sExWords=0;}
    if(sStructSkip||sStructSeen||sStructPart){Logf("  Structure de la scene : %lu changement(s) vu(s), %lu bloc(s) laisse(s) tel quel aux retours, %lu remise(s) partielle(s).",sStructSeen,sStructSkip,sStructPart);sStructSkip=sStructSeen=sStructPart=0;}
    if(sZoneCross){Logf("  Zone : %lu retour(s) a travers un changement de zone.",sZoneCross);sZoneCross=0;}
    if(sSafeFrames){Logf("  Mode sans prediction (sequence de scene) : %lu image(s).",sSafeFrames);sSafeFrames=0;}
    {DWORD np=0;for(DWORD v:sNp)np+=v;if(np)Logf("  Sans prediction (vrai compte) : %lu / %lu image(s) du combat : fenetre %lu, stage %lu, ralenti %lu, sequence %lu, fin de sequence %lu, physique %lu, apres ralenti %lu.",
        np,sFight,sNp[0],sNp[1],sNp[2],sNp[3],sNp[4],sNp[5],sNp[6]);sFight=0;for(DWORD& v:sNp)v=0;}
    if(sPhysRestores||sPhysSkips){Logf("  Physique : %lu retour(s) avec le monde physique remis, %lu refus.",sPhysRestores,sPhysSkips);sPhysRestores=sPhysSkips=0;}
    if(sCamRestored){Logf("  Camera : %lu retour(s) avec la camera des sequences remise.",sCamRestored);sCamRestored=0;}
    if(sGrRestored||sGrSkipped){Logf("  Sol : %lu retour(s) avec la liste des collisions remise (bloc entier %lu fois, contacts %lu fois), %lu refus (liste deplacee).",sGrRestored,sPoolRestored,sCtRestored,sGrSkipped);sGrRestored=sGrSkipped=sPoolRestored=sCtRestored=0;}
    if(sSeqRestored){Logf("  Sequences : %lu retour(s) avec le gestionnaire remis, %lu noeud(s) remis.",sSeqRestored,sSeqNodesRestored);sSeqRestored=sSeqNodesRestored=0;}
    if(sQueueRemoved){Logf("  Demandes de cinematique : %lu retiree(s) aux retours (deposees dans des images annulees).",sQueueRemoved);sQueueRemoved=0;}
    if(sTimerWordsKept||sTimerCut||sListeEntiere||sListeGardee||sListeInvalide||sCompteursRemis){Logf("  Minuteries : %lu lien(s) du bloc de la scene garde(s) aux retours, %lu cycle(s) coupe(s) ; liste remise entiere %lu fois, hors du bloc %lu fois, incoherente %lu fois ; %lu compteur(s) flottant(s) remis.",sTimerWordsKept,sTimerCut,sListeEntiere,sListeGardee,sListeInvalide,sCompteursRemis);sListeInvalide=0;sCompteursRemis=0;sTimerWordsKept=0;sTimerCut=0;sListeEntiere=0;sListeGardee=0;}
    if(winOpen)Logf("  Fenetre ouverte depuis l'image %lu (derniere activite %lu) : signaux decor %lu, structure %lu, zone %lu, pointeur %lu, sequence %lu ; ambiants %X (calme appris : %lu images).",
        winStart,winLastAct,winCnt[0],winCnt[1],winCnt[2],winCnt[3],winCnt[4],ambMask,ambFrames);
    if(sWinCount){Logf("  Mesure des suites : %lu fenetre(s), suites moyenne %lu, max %lu image(s) ; %lu fin(s) anticipee(s), %lu image(s) sans prediction evitee(s).",
        sWinCount,sWinSum/sWinCount,sWinMax,sWinEarly,sWinSaved);sWinCount=sWinSum=sWinMax=sWinEarly=sWinSaved=0;}
    if(sChkOk||sChkBad){Logf("  Verifications a blanc (direct) : %lu identique(s), %lu differente(s).",sChkOk,sChkBad);sChkOk=sChkBad=0;}
    if(sSeqKilled){Logf("  Sequences scriptees lancees dans une image predite annulees au retour : %lu.",sSeqKilled);sSeqKilled=0;}
    if(sCut){Logf("  Evenements de scene dans une image predite : %lu mise(s) a jour coupee(s) en attendant la confirmation.",sCut);sCut=0;}
    if(sLockNext){Logf("  En ligne sans prediction : %lu fin(s) de pas avant l'entree suivante (taches de fin de pas executees, image suivante attendue).",sLockNext);sLockNext=0;}
    if(sReplayCut){Logf("  Rejeux d'evenement termines sur l'image de l'evenement : %lu.",sReplayCut);sReplayCut=0;}
    if(sSlowReset){Logf("  Retours a travers le debut d'un ralenti (remis a 1) : %lu.",sSlowReset);sSlowReset=0;}
    if(sKoBlocked||sKoReplayed){Logf("  K.O. : %lu coup(s) mortel(s) bloque(s) dans des images predites, %lu rejoue(s) une fois confirme(s).",sKoBlocked,sKoReplayed);sKoBlocked=sKoReplayed=0;}
    if(sDecorCross||sDecorBad||sStateOnly){Logf("  Decor : %lu retour(s) a travers une casse (%lu remis), %lu avec seulement l'etat change, %lu image(s) confirmee(s) au decor different de la reference.",sDecorCross,sDecorRestored,sStateOnly,sDecorBad);sDecorCross=sDecorBad=sDecorRestored=sStateOnly=0;}
    Logf("  Total de cette lecture : %lu rollbacks, %lu images confirmees identiques, %lu ecarts%s.",tRollbacks,tOk,tBad,firstBad?" (premier ecart ci-dessus)":"");
    {DWORD np=0;for(DWORD v:tNp)np+=v;if(tFight)Logf("  Total sans prediction : %lu / %lu image(s) du combat (%.1f %%) : fenetre %lu, stage %lu, ralenti %lu, sequence %lu, fin de sequence %lu, physique %lu, apres ralenti %lu.",
        np,tFight,100.0*np/tFight,tNp[0],tNp[1],tNp[2],tNp[3],tNp[4],tNp[5],tNp[6]);}
    sUpdates=sTicks=sRollbacks=sDepth=sDepthMax=sPred=sMiss=sOk=sBadCore=sBadRaw=sSkip=0;sMs=sMaxMs=0;
}

static DWORD __cdecl TickCount() {
    const DWORD i=(Read(base+0x108B490)-2)&3;BYTE* rec=base+0x108B448+i*16;
    const DWORD native=Read(base+0x9C1DB0+Read(rec)*12)+Read(rec+8);
    {static DWORD prevNative=1,prevMode=0;static unsigned logs;const DWORD mode=Read(rec);
     if((native!=prevNative || mode!=prevMode) && logs<300){++logs;Logf("Rythme : pas natifs %lu (avant %lu), mode %lu (pas %lu, multiple %lu), supplement %ld, image %lu.",native,prevNative,mode,Read(base+0x9C1DB0+mode*12),Read(base+0x9C1DB0+mode*12+4),static_cast<long>(Read(rec+8)),lastFrame);}
     prevNative=native;prevMode=mode;}
    if(g_selHold)return 0;
    if(extraNow<0 || net::active)return native+static_cast<DWORD>(extraNow);
    return native+static_cast<DWORD>(extraNow)+static_cast<DWORD>(takeoverExtra);
}
}
static __declspec(naked) void TickCountThunk() {
    __asm {
        push edx
        call lab::TickCount
        pop edx
        ret
    }
}
