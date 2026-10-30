namespace rt {
static bool g_on=false;
static bool ownPresent=false;
static bool Actif(){return g_on;}

constexpr DWORD RVA_MANAGER      =0xFCE790;
constexpr DWORD RVA_REPLAY_STATE =0xD2EBB8;
constexpr DWORD RVA_DEVICES      =0x2057928;
constexpr DWORD RVA_SLOTS        =0x10878F8;
constexpr DWORD RVA_FEED         =0x3396B0;
constexpr DWORD RVA_POLLER       =0x43B7F0;
constexpr DWORD RVA_FIGHT_FRAME  =0x337A10;
constexpr DWORD RVA_FIGHT_STATE  =0x1087A4C;
constexpr DWORD RVA_REPLAY_AGAIN =0x10885F8;
constexpr DWORD RVA_RESTART_FLAG =0x108851C;
constexpr DWORD RVA_UPDATE_PTR   =0xF79E7C;
constexpr DWORD RVA_UPDATE_FN    =0x3F4DB0;
constexpr DWORD RVA_PACE_INTERVAL=0xF0D178;
constexpr DWORD RVA_PACE_ENABLED =0xF0D170;
constexpr DWORD RVA_PLAYERS      =0xFD0540;
constexpr DWORD PAD_SIZE=0x2C, PAD_DWORDS=PAD_SIZE/4, DEVICES_BYTES=5*PAD_SIZE;

static void Log(const char* t) {
    if constexpr(kTest){char l[600];_snprintf_s(l,sizeof l,_TRUNCATE,"TAKEOVER : %s",t);::Log(l);}
}
static char g_root[MAX_PATH]="";

static bool  g_skipPresent=true;

static DWORD g_btnTake=0x4000;
static DWORD g_btnRewind=0x200;
static DWORD g_btnRelease=0x100;
static bool  g_maskTake=false;
static DWORD g_btnExact=0x400;
static DWORD g_catchTicks=10;

static DWORD g_btnPrevRound=0x1000, g_btnNextRound=0x2000;
static DWORD g_roundTicks=40;
static DWORD g_roundPoints=2;

static bool  g_logButtons=false;
static bool  g_showChoice=true;
static DWORD g_btnConfirm=0x10;
static DWORD g_btnCancel=0x20;
static bool  g_maskConfirm=false;

static BYTE* g_base=nullptr;
static BYTE* volatile g_player RT_ASM("_rt_player")=nullptr;
static volatile LONG g_takeSlot=-1;
static volatile LONG g_takeFrame=-1;
static volatile LONG g_takeChosen=0;
static volatile LONG g_rewindPending=0;
static LONG g_restartFrom=-1;
static volatile LONG g_rewindTarget=-1;
static volatile LONG g_restartAsked=0;
static bool  g_seenReset=false;
static DWORD g_rewindStart=0,g_restartTick=0;
static volatile LONG g_ffUpdates=0;
static DWORD g_live[DEVICES_BYTES/4];
static bool  g_blanked=false;
static volatile LONG g_lastDevice=-1;
static SRWLOCK g_actLock=SRWLOCK_INIT;
static volatile LONG g_selecting=0;
static volatile LONG g_selCursor=0;
static volatile LONG g_freezeReq=0;
static bool  g_frozenByUs=false;
static bool  g_selArmed=false;
static volatile LONG g_releaseAtArrival=0;
static volatile LONG g_restoreRelease=0;
static bool  g_roundSeenDecided=false;

static BYTE* base=nullptr;
static bool Copy(void* dst,const void* src,size_t n) {
    RT_TRY { memcpy(dst,src,n); return true; }
    RT_EXCEPT { memset(dst,0,n); return false; }
}
static DWORD Read(const void* p) { DWORD v=0; Copy(&v,p,4); return v; }
#include "TakeoverUI.h"
#include "TakeoverCheckpoint.h"

static DWORD ReplayMode() {
    void* obj=*reinterpret_cast<void**>(g_base+RVA_MANAGER);
    return obj?*reinterpret_cast<DWORD*>(static_cast<BYTE*>(obj)+8):0;
}
static bool ReplayPlaying() { const DWORD m=ReplayMode(); return m==2u||m==4u; }

constexpr DWORD RVA_NET_READER=0xF8F208, RVA_MATCHING=0xF8189C;
static bool Online() { return net::active||net::modeCombat||(g_base&&(Read(g_base+RVA_NET_READER)||Read(g_base+RVA_MATCHING))); }
static volatile LONG g_onlineSkips=0, g_onlineLeaks=0;
static DWORD PlayerFrame() { BYTE* o=g_player; return o?*reinterpret_cast<DWORD*>(o+0x2C):0xFFFFFFFFu; }

static LONG RewindTarget() { return g_takeFrame<1?1:g_takeFrame; }
static bool CatchingUp() { return g_rewindTarget>=0&&!g_rewindPending; }
static DWORD& At(DWORD rva) { return *reinterpret_cast<DWORD*>(g_base+rva); }

static bool IsHuman(LONG who) { return At(RVA_PLAYERS+who*0x6C8)==1; }

static volatile LONG g_camResetReq=0;
static void ResetReplayCamera() {
    BYTE* c=g_base+0xFC7168;DWORD mode=0;
    if(!Copy(&mode,c,4) || mode==7)return;
    DWORD off[6]={};float rest=0;Copy(off,c+4,24);Copy(&rest,c+0x20,4);
    const bool moved=off[0]||off[1]||off[2]||off[3]||off[4]||off[5]||rest!=1.0f;
    RT_TRY {
        for(DWORD o=0x04;o<=0x1C;o+=4)*reinterpret_cast<DWORD*>(c+o)=0;
        *reinterpret_cast<DWORD*>(c+0x2C)=0;
        *reinterpret_cast<float*>(c+0x20)=1.0f;
        *reinterpret_cast<DWORD*>(c+0x24)=0;
        c[0x28]=0;
        *reinterpret_cast<DWORD*>(c+0x34)=0;
        c[0x3C]=0;
    } RT_EXCEPT {return;}
    if(moved)Log("Camera du replay remise a sa position par defaut (reprise en main).");
}
static void TakeNow(const char* from,LONG who) {
    g_takeChosen=who;
    g_takeFrame=static_cast<LONG>(PlayerFrame());
    InterlockedExchange(&g_takeSlot,who);
    InterlockedExchange(&g_camResetReq,1);
    InterlockedExchange(&cp::requestSave,1);
    if(!ui::g_dataOk) ui::ReadReplayData();
    g_roundSeenDecided=false;
    char l[128];sprintf_s(l,"%s : reprise en main du joueur %ld a l image %ld.",from,who+1,g_takeFrame); Log(l);
}
static void CloseSelector() {
    InterlockedExchange(&g_selecting,0);
    ui::SelectorClosed();
    InterlockedExchange(&g_freezeReq,2);
}
static void SelectToggle() {
    AcquireSRWLockExclusive(&g_actLock);
    if(g_selecting) {const LONG other=1-g_selCursor; if(IsHuman(other)) InterlockedExchange(&g_selCursor,other);}
    ReleaseSRWLockExclusive(&g_actLock);
}
static void ActionPrimary(const char* from,bool exact=false) {
    AcquireSRWLockExclusive(&g_actLock);
    char l[160];
    if(g_selecting) {
        CloseSelector();
        TakeNow(from,g_selCursor);
    } else if(g_rewindTarget>=0) {

    } else if(g_takeSlot<0) {
        if(!ReplayPlaying()||!g_player) {sprintf_s(l,"%s ignore : aucun replay en lecture.",from); Log(l);}
        else if(g_showChoice&&IsHuman(1)) {
            InterlockedExchange(&g_selCursor,IsHuman(g_takeChosen)?g_takeChosen:0);
            ui::SelectorOpened();
            g_selArmed=false;
            InterlockedExchange(&g_selecting,1);
            InterlockedExchange(&g_freezeReq,1);
            sprintf_s(l,"%s : choix du joueur (combat fige).",from); Log(l);
        } else TakeNow(from,IsHuman(g_takeChosen)?g_takeChosen:0);
    } else if(cp::roundOver) {
        sprintf_s(l,"%s ignore : round termine (K.O. ou temps ecoule), retour desactive jusqu a la prochaine reprise.",from); Log(l);
    } else if(cp::active&&(!exact||cp::rebuildAvailable)) {
        InterlockedExchange(&g_restoreRelease,0);
        if(exact) InterlockedExchange(&cp::forceRebuild,1);
        InterlockedExchange(&cp::requestRestore,1);
        sprintf_s(l,"%s : retour au point de controle (image %ld)%s.",from,g_takeFrame,exact?", decor remis a neuf":""); Log(l);
    } else {
        InterlockedExchange(&g_takeSlot,-1);
        InterlockedExchange(&g_releaseAtArrival,0);
        InterlockedExchange(&g_rewindTarget,RewindTarget());
        InterlockedExchange(&g_rewindPending,1);
        sprintf_s(l,"%s : retour %sa l image %ld par redemarrage et rattrapage accelere.",from,exact?"EXACT ":"",g_takeFrame); Log(l);
    }
    ReleaseSRWLockExclusive(&g_actLock);
}
static void ActionRelease(const char* from) {
    AcquireSRWLockExclusive(&g_actLock);
    char l[128];
    if(g_selecting) {CloseSelector(); sprintf_s(l,"%s : choix annule.",from);}
    else if(g_rewindTarget>=0) l[0]=0;
    else if(g_takeSlot>=0) {
        InterlockedExchange(&g_takeSlot,-1);
        if(cp::active) {
            InterlockedExchange(&g_restoreRelease,1);
            InterlockedExchange(&cp::requestRestore,1);
            sprintf_s(l,"%s : retour au point de controle (image %ld), le replay reprend normalement.",from,g_takeFrame);
        } else if(cp::roundOver) {
            sprintf_s(l,"%s : main rendue (round termine, pas de retour).",from);
        } else {
            InterlockedExchange(&g_releaseAtArrival,1);
            InterlockedExchange(&g_rewindTarget,RewindTarget());
            InterlockedExchange(&g_rewindPending,1);
            sprintf_s(l,"%s : retour a l image %ld par rattrapage accelere, puis le replay reprend.",from,g_takeFrame);
        }
    }
    else sprintf_s(l,"%s ignore : aucune reprise en main en cours.",from);
    if(l[0]) Log(l);
    ReleaseSRWLockExclusive(&g_actLock);
}

constexpr DWORD RVA_ROUND_ON=0xFCDE54;
static LONG g_roundStarts[16]; static volatile LONG g_roundCount=0;
static volatile LONG g_roundSeek=0;
static LONG g_seekFromRound=-1;
static void NoteRoundStart(LONG f) {
    for(LONG i=0;i<g_roundCount;++i) if(g_roundStarts[i]>=f-120&&g_roundStarts[i]<=f+120) return;
    if(g_roundCount>=16) return;
    LONG i=g_roundCount;
    while(i>0&&g_roundStarts[i-1]>f){g_roundStarts[i]=g_roundStarts[i-1];--i;}
    g_roundStarts[i]=f; InterlockedIncrement(&g_roundCount);
    char l[96];sprintf_s(l,"Round %ld : debut (FIGHT) a l image %ld.",i+1,f);Log(l);
}
static LONG CurrentRound(LONG f) { LONG k=-1; for(LONG i=0;i<g_roundCount;++i) if(g_roundStarts[i]<=f) k=i; return k; }

static volatile LONG g_roundRestore=0; static LONG g_roundRestoreIdx=-1;

static cp::Bank* g_banks[16]={};
static volatile LONG g_engineRound=-1; static bool g_engineBanked=false;
static volatile LONG g_bankLoadReq=-1;
static volatile LONG g_roundSaveIdx=-1;
static void BanksClear(const char* why) {
    bool any=false; for(cp::Bank* b : g_banks) if(b&&b->used){b->used=false; any=true;}
    if(g_engineRound>=0) any=true;
    InterlockedExchange(&g_engineRound,-1); g_engineBanked=false;
    if(any){char l[128];sprintf_s(l,"Points des rounds effaces (%s).",why);Log(l);}
}
static bool NearStart(LONG idx,LONG sf) { return sf>=g_roundStarts[idx]-30&&sf<=g_roundStarts[idx]+30; }
static bool RoundPointFor(LONG idx) {
    if(idx<0||idx>=g_roundCount||idx>=16||g_takeSlot>=0) return false;
    if(g_engineRound==idx&&cp::active&&!cp::roundOver&&NearStart(idx,static_cast<LONG>(cp::savedFrame))) return true;
    return g_roundPoints==2&&g_banks[idx]&&g_banks[idx]->used&&NearStart(idx,static_cast<LONG>(g_banks[idx]->savedFrame));
}
static void EndRoundSeek(const char* why) {
    InterlockedExchange(&g_rewindTarget,-1);
    InterlockedExchange(&g_roundSeek,0);
    InterlockedExchange(&g_releaseAtArrival,0);
    InterlockedExchange(&g_ffUpdates,0);
    char l[160];sprintf_s(l,"Saut de round : %s (image %lu, %lu ms).",why,PlayerFrame(),GetTickCount()-g_rewindStart);Log(l);
    MessageBeep(MB_OK);
}
static void RoundSeek(LONG dir) {
    char l[160];
    if(!ReplayPlaying()||!g_player||g_takeSlot>=0||g_rewindTarget>=0||g_selecting) return;
    const LONG f=static_cast<LONG>(PlayerFrame()), k=CurrentRound(f);
    LONG target=-1;
    if(dir<0) {
        if(k<0){Log("Round precedent : aucun debut de round connu.");return;}
        target=(f-g_roundStarts[k]>120||k==0)?g_roundStarts[k]:g_roundStarts[k-1];
    } else if(k+1<g_roundCount) target=g_roundStarts[k+1];
    g_rewindStart=GetTickCount();
    InterlockedExchange(&g_ffUpdates,0);
    InterlockedExchange(&g_releaseAtArrival,1);
    if(target<0) {
        g_seekFromRound=k;
        g_seenReset=true; g_restartFrom=-1;
        InterlockedExchange(&g_roundSeek,2);
        InterlockedExchange(&g_rewindTarget,0x7FFFFFFF);
        sprintf_s(l,"Select+R1 : avance rapide jusqu'au round suivant (depuis l'image %ld).",f);Log(l);
        return;
    }
    InterlockedExchange(&g_roundSeek,1);
    if(target<f) {
        InterlockedExchange(&g_rewindTarget,target);
        InterlockedExchange(&g_rewindPending,1);
    } else {
        g_seenReset=true; g_restartFrom=-1;
        InterlockedExchange(&g_rewindTarget,target);
    }
    sprintf_s(l,"%s : saut au round %ld (image %ld, depuis %ld).",dir<0?"Select+L1":"Select+R1",CurrentRound(target)+1,target,f);Log(l);
}
static void RoundSeekKey(LONG dir) { AcquireSRWLockExclusive(&g_actLock); RoundSeek(dir); ReleaseSRWLockExclusive(&g_actLock); }
static DWORD RoundPointMask() { DWORD m=0; for(LONG i=0;i<g_roundCount&&i<16;++i) if(RoundPointFor(i)) m|=1u<<i; return m; }
static void SeekToRound(LONG idx,bool instant=true) {
    char l[160];
    if(!ReplayPlaying()||!g_player||g_takeSlot>=0||g_rewindTarget>=0||g_roundRestore) return;
    const LONG f=static_cast<LONG>(PlayerFrame());
    if(instant&&idx<g_roundCount&&(g_roundStarts[idx]<f||(g_roundPoints==2&&idx!=CurrentRound(f)))&&RoundPointFor(idx)&&(g_roundPoints==2||idx==CurrentRound(f))) {
        g_roundRestoreIdx=idx;
        InterlockedExchange(&g_roundRestore,1);
        if(g_engineRound==idx&&cp::active) InterlockedExchange(&cp::requestRestore,1);
        else InterlockedExchange(&g_bankLoadReq,idx);
        sprintf_s(l,"Menu des rounds : retour instantane au debut du round %ld (depuis l'image %ld%s).",idx+1,f,g_engineRound==idx?"":", point en banque");Log(l);
        return;
    }
    g_rewindStart=GetTickCount();
    InterlockedExchange(&g_ffUpdates,0);
    InterlockedExchange(&g_releaseAtArrival,1);
    if(idx>=g_roundCount) {
        g_seekFromRound=CurrentRound(f);
        g_seenReset=true; g_restartFrom=-1;
        InterlockedExchange(&g_roundSeek,2);
        InterlockedExchange(&g_rewindTarget,0x7FFFFFFF);
        sprintf_s(l,"Menu des rounds : avance rapide jusqu'au round suivant (depuis l'image %ld).",f);Log(l);
        return;
    }
    const LONG target=g_roundStarts[idx<0?0:idx];
    InterlockedExchange(&g_roundSeek,1);
    if(target<f) {InterlockedExchange(&g_rewindTarget,target); InterlockedExchange(&g_rewindPending,1);}
    else {g_seenReset=true; g_restartFrom=-1; InterlockedExchange(&g_rewindTarget,target);}
    sprintf_s(l,"Menu des rounds : saut au round %ld (image %ld, depuis %ld).",idx+1,target,f);Log(l);
}

static volatile LONG g_roundMenu=0; static volatile LONG g_roundCursor=0; static bool g_menuArmed=false;
static void OpenRoundMenu() {
    if(!ReplayPlaying()||!g_player||g_takeSlot>=0||g_rewindTarget>=0||g_selecting||g_roundMenu) return;
    if(!g_roundCount){Log("Menu des rounds : aucun debut de round vu pour l'instant (attendre le FIGHT).");return;}
    const LONG cur=CurrentRound(static_cast<LONG>(PlayerFrame()));
    ui::g_menuN=g_roundCount; ui::g_menuCur=cur; ui::g_menuNext=(cur+1>=g_roundCount);
    ui::g_menuInstant=g_roundPoints==2?RoundPointMask():(RoundPointFor(cur)?1u<<cur:0u);
    InterlockedExchange(&g_roundCursor,cur<0?0:cur);
    g_menuArmed=false;
    InterlockedExchange(&g_roundMenu,1);
    InterlockedExchange(&g_freezeReq,1);
    char l[96];sprintf_s(l,"Menu des rounds ouvert (%ld round(s) connus, en cours : %ld).",g_roundCount,cur+1);Log(l);
}
static void CloseRoundMenu(LONG choose) {
    InterlockedExchange(&g_roundMenu,0);
    InterlockedExchange(&g_freezeReq,2);
    if(choose>=0) SeekToRound(choose); else Log("Menu des rounds ferme.");
}

constexpr DWORD RVA_CFG_REPLAY=0xF9CB60, RVA_CFG_LOCAL=0xF9CBA0, CFG_SIZE=0x10;
static bool  g_ownConfig=true;
static BYTE  g_cfgSaved[4][CFG_SIZE]; static bool g_cfgHeld[4]={false,false,false,false};
static void ConfigRestore() {
    for(int p=0;p<4;++p) if(g_cfgHeld[p]) {memcpy(g_base+RVA_CFG_REPLAY+p*CFG_SIZE,g_cfgSaved[p],CFG_SIZE); g_cfgHeld[p]=false;}
}
static void ConfigApply(LONG slot,LONG device) {
    LONG place=0;
    for(LONG p=0;p<4;++p) if(g_base[0x10877C0+p]==device) {place=p; break;}
    const BYTE* mine=g_base+RVA_CFG_LOCAL+place*CFG_SIZE;
    for(LONG p : {slot,slot^2}) {
        BYTE* dst=g_base+RVA_CFG_REPLAY+p*CFG_SIZE;
        if(!g_cfgHeld[p]) {
            memcpy(g_cfgSaved[p],dst,CFG_SIZE); g_cfgHeld[p]=true;
            if(p==slot && memcmp(dst,mine,CFG_SIZE)) {char l[96];sprintf_s(l,"Configuration de la place %ld appliquee au joueur %ld.",place+1,p+1);Log(l);}
        }
        if(memcmp(dst,mine,CFG_SIZE)) memcpy(dst,mine,CFG_SIZE);
    }
}
static void __cdecl OnFed() {
    if(!g_base) return;
    if(Online()) {InterlockedIncrement(&g_onlineLeaks); return;}
    const LONG target=g_rewindTarget;
    if(target>=0&&!g_rewindPending&&!g_restartAsked) {
        const LONG f=static_cast<LONG>(PlayerFrame());

        if(f<target) g_seenReset=true;
        else if(!g_seenReset&&g_restartFrom>target&&f<g_restartFrom) g_seenReset=true;
        else if(g_seenReset) {
            char l[160];
            sprintf_s(l,"Revenu a l image %ld en %lu ms (%ld mises a jour).",f,GetTickCount()-g_rewindStart,g_ffUpdates);
            Log(l);
            InterlockedExchange(&g_ffUpdates,0);
            InterlockedExchange(&g_rewindTarget,-1);
            if(InterlockedExchange(&g_roundSeek,0)) {InterlockedExchange(&g_releaseAtArrival,0); Log("Saut de round termine : le replay reprend normalement.");}
            else if(InterlockedExchange(&g_releaseAtArrival,0)) Log("Le replay reprend normalement.");
            else {
                InterlockedExchange(&g_takeSlot,g_takeChosen);
                InterlockedExchange(&cp::requestSave,1);
            }
            MessageBeep(MB_OK);
        }
    }
    const LONG slot=g_takeSlot;
    if(slot<0||!ReplayPlaying()) {ConfigRestore(); return;}
    LONG d=g_lastDevice;
    if(d<0||d>3) {d=g_base[0x10877C0]; if(d>3) d=0;}
    if(g_ownConfig) ConfigApply(slot,d);
    DWORD pad[PAD_DWORDS];
    memcpy(pad,g_live+d*PAD_DWORDS,PAD_SIZE);
    DWORD mine=g_btnRewind|g_btnRelease|g_btnExact;
    if(g_maskTake) mine|=g_btnTake;
    if(g_maskConfirm) mine|=g_btnConfirm;
    pad[0]&=~mine; pad[1]&=~mine; pad[2]&=~mine;
    BYTE* slots=g_base+RVA_SLOTS;
    memcpy(slots+slot*PAD_SIZE,pad,PAD_SIZE);
    memcpy(slots+(slot^2)*PAD_SIZE,pad,PAD_SIZE);
}
static BYTE* g_resumeFeed RT_ASM("_rt_resumeFeed")=nullptr;
#ifdef _MSC_VER
static __declspec(naked) void OriginalFeed() { __asm { push ebp
                                                       mov  ebp,esp
                                                       sub  esp,0x2C
                                                       jmp  [g_resumeFeed] } }
static __declspec(naked) void FeedThunk() {
    __asm {
        mov  g_player,ecx
        call OriginalFeed
        pushad
        pushfd
        call OnFed
        popfd
        popad
        ret
    }
}
#else
extern "C" void rt_OnFed() { OnFed(); }
extern "C" void FeedThunk();
__asm__(".intel_syntax noprefix\n"
    ".text\n"
    "_rt_OriginalFeed:\n"
    "push ebp\n"
    "mov ebp,esp\n"
    "sub esp,0x2C\n"
    "jmp dword ptr [_rt_resumeFeed]\n"
    ".globl _FeedThunk\n"
    "_FeedThunk:\n"
    "mov dword ptr [_rt_player],ecx\n"
    "call _rt_OriginalFeed\n"
    "pushad\n"
    "pushfd\n"
    "call _rt_OnFed\n"
    "popfd\n"
    "popad\n"
    "ret\n"
    ".att_syntax prefix\n");
#endif

static DWORD g_lastHeld[4]={0}, g_lastAxes[4]={0};
static void LogButtons(LONG d,const DWORD* p) {
    DWORD axes=0;
    const float* f=reinterpret_cast<const float*>(p+3);
    for(int i=0;i<6;++i) {if(f[i]>0.5f) axes|=1u<<(2*i); else if(f[i]<-0.5f) axes|=2u<<(2*i);}
    if(p[0]==g_lastHeld[d]&&axes==g_lastAxes[d]) return;
    g_lastHeld[d]=p[0]; g_lastAxes[d]=axes;
    char l[200];
    sprintf_s(l,"manette %ld : maintenu %08lX  axes %+.2f %+.2f %+.2f %+.2f %+.2f %+.2f  (+24 %08lX +28 %08lX)",
        d,p[0],f[0],f[1],f[2],f[3],f[4],f[5],p[9],p[10]);
    Log(l);
}
static LONG g_stickSide[4]={0};

static DWORD g_prevHeld[4]={0};
static void __cdecl OnPollEnter() {
    if(g_blanked&&g_base) {memcpy(g_base+RVA_DEVICES,g_live,DEVICES_BYTES); g_blanked=false;}
}
static void __cdecl OnPollExit() {
    if(!g_base||Online()) return;
    {

        static DWORD lastPlaying=0;
        if(ReplayPlaying()||g_restartAsked||g_rewindPending||g_rewindTarget>=0||g_roundSeek) lastPlaying=GetTickCount();
        else if(g_roundCount&&GetTickCount()-lastPlaying>1500){InterlockedExchange(&g_roundCount,0); Log("Rounds notes oublies (plus de replay en lecture)."); BanksClear("plus de replay");}
    }
    ui::LogicFrame();
    BYTE* dev=g_base+RVA_DEVICES;
    memcpy(g_live,dev,DEVICES_BYTES);
    DWORD pressed=0,held=0;
    for(LONG d=0;d<4;++d) {
        const DWORD* p=g_live+d*PAD_DWORDS;
        if(p[0]||p[1]||p[2]||p[3]||p[4]) g_lastDevice=d;
        pressed|=p[0]&~g_prevHeld[d];
        held|=p[0];
        g_prevHeld[d]=p[0];
        if(g_logButtons) LogButtons(d,p);
    }
    if(g_selecting&&!g_selArmed) {
        if(!held) g_selArmed=true;
        pressed=0;
    }
    if(g_selecting) {
        if(!ReplayPlaying()) {AcquireSRWLockExclusive(&g_actLock); CloseSelector(); ReleaseSRWLockExclusive(&g_actLock);}

        if(pressed&0xF) SelectToggle();
        if(g_btnConfirm&&(pressed&g_btnConfirm)) {ActionPrimary("Croix"); g_maskConfirm=true; pressed&=~g_btnTake;}
        else if(g_btnCancel&&(pressed&g_btnCancel)) ActionRelease("Rond");
        for(LONG d=0;d<4;++d) {
            const float* ax=reinterpret_cast<const float*>(g_live+d*PAD_DWORDS+3);
            const LONG side=ax[0]>0.5f?1:ax[0]<-0.5f?-1:ax[1]>0.5f?2:ax[1]<-0.5f?-2:0;
            if(side&&side!=g_stickSide[d]&&g_selArmed) SelectToggle();
            g_stickSide[d]=side;
        }
    }
    if(g_roundMenu) {
        if(!g_menuArmed){if(!held) g_menuArmed=true; pressed=0;}
        const LONG m=ui::g_menuN+(ui::g_menuNext?1:0);
        static LONG stick[4]={0};
        LONG move=0;
        if(pressed&1) move=-1; else if(pressed&2) move=1;
        for(LONG d=0;d<4;++d){const float* ax=reinterpret_cast<const float*>(g_live+d*PAD_DWORDS+3);
            const LONG side=ax[1]>0.5f?1:ax[1]<-0.5f?-1:0;
            if(side&&side!=stick[d]&&g_menuArmed&&!move) move=side;
            stick[d]=side;}
        if(move&&m>0) InterlockedExchange(&g_roundCursor,(g_roundCursor+move+m)%m);
        AcquireSRWLockExclusive(&g_actLock);
        if(!ReplayPlaying()) CloseRoundMenu(-1);
        else if(g_btnConfirm&&(pressed&g_btnConfirm)) {g_maskConfirm=true; CloseRoundMenu(g_roundCursor);}
        else if((g_btnCancel&&(pressed&g_btnCancel))||(g_btnRelease&&(pressed&g_btnRelease))) CloseRoundMenu(-1);
        ReleaseSRWLockExclusive(&g_actLock);
        if(ReplayPlaying()){memset(dev,0,DEVICES_BYTES); g_blanked=true;}
        return;
    }
    if(g_maskTake&&!(held&g_btnTake)) g_maskTake=false;
    if(g_maskConfirm&&!(held&g_btnConfirm)) g_maskConfirm=false;
    bool consumed=false;
    if(g_takeSlot>=0||g_rewindTarget>=0) {
        if(g_btnRewind&&(pressed&g_btnRewind)) {ActionPrimary("Select"); consumed=true;}
        if(g_btnRelease&&(pressed&g_btnRelease)) {ActionRelease("Start"); consumed=true;}
        if(g_btnExact&&(pressed&g_btnExact)&&g_takeSlot>=0) {ActionPrimary("L3",true); consumed=true;}
    } else {
        if(g_btnTake&&(pressed&g_btnTake)) {ActionPrimary("L2"); g_maskTake=true; consumed=g_selecting||g_takeSlot>=0;}
        else if(g_selecting&&g_btnRelease&&(pressed&g_btnRelease)) {ActionRelease("Start"); consumed=true;}
    }

    static LONG selDev=-1; static bool selUsed=false; LONG synth=-1; DWORD hide=0;
    if(!consumed&&g_takeSlot<0&&g_rewindTarget<0&&!g_selecting&&ReplayPlaying()&&g_btnRewind&&(g_btnPrevRound||g_btnNextRound)) {
        if(held&g_btnRewind) {
            if(selDev<0){selUsed=false; for(LONG d=0;d<4;++d) if(g_live[d*PAD_DWORDS]&g_btnRewind){selDev=d;break;}}
            if(g_btnPrevRound&&(pressed&g_btnPrevRound)){AcquireSRWLockExclusive(&g_actLock); OpenRoundMenu(); ReleaseSRWLockExclusive(&g_actLock); selUsed=true;}
            else if(g_btnNextRound&&(pressed&g_btnNextRound)){RoundSeekKey(1); selUsed=true;}
            hide=g_btnRewind|g_btnPrevRound|g_btnNextRound;
        } else if(selDev>=0) {
            if(!selUsed) synth=selDev;
            selDev=-1;
        }
    } else selDev=-1;
    if((g_takeSlot>=0||g_selecting||consumed)&&ReplayPlaying()) {memset(dev,0,DEVICES_BYTES); g_blanked=true;}
    else if(hide||synth>=0) {
        DWORD* w=reinterpret_cast<DWORD*>(dev);
        for(LONG d=0;d<5;++d){w[d*PAD_DWORDS]&=~hide; w[d*PAD_DWORDS+1]&=~hide; w[d*PAD_DWORDS+2]&=~hide;}
        if(synth>=0){const LONG ds[2]={synth,4}; for(LONG d : ds){w[d*PAD_DWORDS]|=g_btnRewind; w[d*PAD_DWORDS+1]|=g_btnRewind;}}
        g_blanked=true;
    }
}
static BYTE* g_resumePoll RT_ASM("_rt_resumePoll")=nullptr;
#ifdef _MSC_VER
static __declspec(naked) void OriginalPoll() { __asm { push ebp
                                                       mov  ebp,esp
                                                       sub  esp,0x6C
                                                       jmp  [g_resumePoll] } }
static __declspec(naked) void PollThunk() {
    __asm {
        pushad
        pushfd
        call OnPollEnter
        popfd
        popad
        call OriginalPoll
        pushad
        pushfd
        call OnPollExit
        popfd
        popad
        ret
    }
}
#else
extern "C" void rt_OnPollEnter() { OnPollEnter(); }
extern "C" void rt_OnPollExit() { OnPollExit(); }
extern "C" void PollThunk();
__asm__(".intel_syntax noprefix\n"
    ".text\n"
    "_rt_OriginalPoll:\n"
    "push ebp\n"
    "mov ebp,esp\n"
    "sub esp,0x6C\n"
    "jmp dword ptr [_rt_resumePoll]\n"
    ".globl _PollThunk\n"
    "_PollThunk:\n"
    "pushad\n"
    "pushfd\n"
    "call _rt_OnPollEnter\n"
    "popfd\n"
    "popad\n"
    "call _rt_OriginalPoll\n"
    "pushad\n"
    "pushfd\n"
    "call _rt_OnPollExit\n"
    "popfd\n"
    "popad\n"
    "ret\n"
    ".att_syntax prefix\n");
#endif

constexpr DWORD RVA_FREEZE=0x313010, RVA_UNFREEZE=0x313030, RVA_FROZEN=0x10879B1;

static DWORD g_humanFlags[2]; static bool g_humanValid=false;
static void __cdecl OnFightFrame() {
    if(!g_base) return;
    if(Online()) {g_humanValid=false; InterlockedIncrement(&g_onlineSkips); return;}
    if(!ReplayPlaying()) g_humanValid=false;
    else if(!g_humanValid&&g_rewindTarget<0&&!g_restartAsked) {
        g_humanFlags[0]=At(RVA_PLAYERS); g_humanFlags[1]=At(RVA_PLAYERS+0x6C8); g_humanValid=true;
    }
    if(g_freezeReq) {
        typedef void (__cdecl *VoidFn)();
        const LONG req=InterlockedExchange(&g_freezeReq,0);
        if(req==1&&!g_base[RVA_FROZEN]) {reinterpret_cast<VoidFn>(g_base+RVA_FREEZE)(); g_frozenByUs=true;}
        else if(req==2&&g_frozenByUs) {reinterpret_cast<VoidFn>(g_base+RVA_UNFREEZE)(); g_frozenByUs=false;}
    }

    if(g_takeSlot>=0&&g_rewindTarget<0&&!g_restartAsked&&!g_rewindPending) {
        const LONG f=static_cast<LONG>(PlayerFrame());
        if(!ReplayPlaying()||(g_takeFrame>=0&&f+1<g_takeFrame)) {
            InterlockedExchange(&g_takeSlot,-1);
            g_roundSeenDecided=false;
            char l[128];sprintf_s(l,"Replay relance ou arrete (image %ld, reprise a %ld) : la main revient au replay.",f,g_takeFrame);Log(l);
        }
    }

    if(cp::active&&g_takeSlot>=0&&g_rewindTarget<0&&static_cast<LONG>(cp::savedFrame)-1>g_takeFrame) {
        g_takeFrame=static_cast<LONG>(cp::savedFrame)-1;
        char l[96];sprintf_s(l,"Point differe pose : reprise comptee a l image %ld.",g_takeFrame);Log(l);
    }

    if(g_takeSlot>=0&&g_rewindTarget<0) {
        const bool decided=cp::RoundDecided();
        if(decided) g_roundSeenDecided=true;
        else if(g_roundSeenDecided&&At(RVA_FIGHT_STATE)==4) {
            g_roundSeenDecided=false;
            InterlockedExchange(&g_takeSlot,-1);
            Log("Nouveau round : la main revient aux entrees du replay.");
        }
    }
    const LONG cpResult=InterlockedExchange(&cp::lastResult,0);
    if(cpResult&&g_roundRestore) {
        InterlockedExchange(&g_roundRestore,0);
        if(cpResult==1) {Log("Saut de round instantane termine : le replay reprend normalement."); MessageBeep(MB_OK);}
        else {
            Log("Retour instantane au round refuse : rattrapage accelere.");
            AcquireSRWLockExclusive(&g_actLock); SeekToRound(g_roundRestoreIdx,false); ReleaseSRWLockExclusive(&g_actLock);
        }
    }
    else if(cpResult==2&&g_rewindTarget<0) {
        if(cp::roundOver) Log("Retour refuse : round termine (K.O. ou temps ecoule).");
        else {

            InterlockedExchange(&g_takeSlot,-1);
            InterlockedExchange(&g_releaseAtArrival,g_restoreRelease);
            InterlockedExchange(&g_rewindTarget,RewindTarget());
            InterlockedExchange(&g_rewindPending,1);
            Log("Retour par rattrapage accelere.");
        }
    }
    if(g_rewindPending) {
        InterlockedExchange(&g_rewindPending,0);
        const DWORD st=At(RVA_FIGHT_STATE), rs=At(RVA_REPLAY_STATE);
        if(st!=4||(rs!=1&&rs!=3)) {
            char l[128];sprintf_s(l,"Retour abandonne : pas en combat de replay (etat %lu, replay %lu).",st,rs);Log(l);
            InterlockedExchange(&g_rewindTarget,-1);
            return;
        }
        At(RVA_REPLAY_AGAIN)=1;
        g_base[RVA_RESTART_FLAG]=1;
        InterlockedExchange(&g_restartAsked,1);
        g_seenReset=false;
        g_restartFrom=static_cast<LONG>(PlayerFrame());
        g_rewindStart=g_restartTick=GetTickCount();
    } else if(g_restartAsked) {
        if(!g_base[RVA_RESTART_FLAG]) {
            InterlockedExchange(&g_restartAsked,0);
            if(g_humanValid&&(At(RVA_PLAYERS)!=g_humanFlags[0]||At(RVA_PLAYERS+0x6C8)!=g_humanFlags[1])) {
                At(RVA_PLAYERS)=g_humanFlags[0]; At(RVA_PLAYERS+0x6C8)=g_humanFlags[1];
                Log("Redemarrage : joueurs humains remis.");
            }
        }
        else if(GetTickCount()-g_restartTick>5000) {
            Log("Retour abandonne : redemarrage non pris en compte par le jeu.");
            g_base[RVA_RESTART_FLAG]=0; At(RVA_REPLAY_AGAIN)=0;
            InterlockedExchange(&g_restartAsked,0);
            InterlockedExchange(&g_rewindTarget,-1);
        }
    }
}
static BYTE* g_resumeFightFrame RT_ASM("_rt_resumeFightFrame")=nullptr;
#ifdef _MSC_VER
static __declspec(naked) void FightFrameThunk() {
    __asm {
        pushad
        pushfd
        call OnFightFrame
        popfd
        popad
        push ebp
        mov  ebp,esp
        push -1
        jmp  [g_resumeFightFrame]
    }
}
#else
extern "C" void rt_OnFightFrame() { OnFightFrame(); }
extern "C" void FightFrameThunk();
__asm__(".intel_syntax noprefix\n"
    ".text\n"
    ".globl _FightFrameThunk\n"
    "_FightFrameThunk:\n"
    "pushad\n"
    "pushfd\n"
    "call _rt_OnFightFrame\n"
    "popfd\n"
    "popad\n"
    "push ebp\n"
    "mov ebp,esp\n"
    "push -1\n"
    "jmp dword ptr [_rt_resumeFightFrame]\n"
    ".att_syntax prefix\n");
#endif

static bool  g_paceLifted=false;
static DWORD g_paceSaved=0,g_paceEnabledSaved=0;
static void PaceControl(bool fast) {
    DWORD& interval=At(RVA_PACE_INTERVAL);
    DWORD& enabled=At(RVA_PACE_ENABLED);
    if(fast) {
        if(!g_paceLifted) {g_paceSaved=interval; g_paceEnabledSaved=enabled; g_paceLifted=true;}
        interval=0; enabled=1;
    } else if(g_paceLifted) {
        interval=g_paceSaved; enabled=g_paceEnabledSaved; g_paceLifted=false;
    }
}
static volatile LONG g_extraTicks=0; static volatile LONG g_stepInUpdate=0;
static void PlanTicks() {
    LONG extra=0;
    const LONG target=g_rewindTarget;
    if(target>=0&&!g_rewindPending&&!g_restartAsked&&g_seenReset&&g_catchTicks>1&&!g_base[RVA_FROZEN]) {
        const LONG remaining=target-static_cast<LONG>(PlayerFrame());
        extra=static_cast<LONG>(g_roundSeek?g_roundTicks:g_catchTicks)-1;
        if(remaining-1<extra) extra=remaining-1;
        if(extra<0) extra=0;
    }
    InterlockedExchange(&g_extraTicks,extra);
    InterlockedExchange(&lab::takeoverExtra,extra);
}
static void BeforeUpdate() {
    if(!g_on)return;
    if(Online()){InterlockedExchange(&g_extraTicks,0);InterlockedExchange(&lab::takeoverExtra,0);return;}
    PlanTicks();
    InterlockedExchange(&g_stepInUpdate,0);
}
static void AfterUpdate() {
    if(!g_on)return;
    if(Online()){PaceControl(false);return;}
    const bool fast=CatchingUp();
    if(fast) InterlockedIncrement(&g_ffUpdates);
    PaceControl(fast);
}

static volatile LONG g_selectorDraws=0;

typedef HRESULT (__stdcall *PresentFn)(void*,const RECT*,const RECT*,HWND,const void*);

struct PresentPatch { void** vt; PresentFn orig; };
static PresentPatch g_pp[4];
static volatile LONG g_ppCount=0;
static volatile LONG g_presents=0;
static PresentFn OrigPresent(void* dev) {
    void** vt=*static_cast<void***>(dev);
    const LONG n=g_ppCount;
    for(LONG i=0;i<n;++i) if(g_pp[i].vt==vt) return g_pp[i].orig;
    return g_pp[0].orig;
}

static bool PresentSkip() {
    if(!g_on) return false;
    const LONG n=InterlockedIncrement(&g_presents);
    return g_skipPresent&&CatchingUp()&&(n&7);
}
static void PresentDraw(IDirect3DDevice9* d3d) {
    if(!g_on) return;
    if(ReplayPlaying()&&!CatchingUp()&&!Online()) {
        const bool human[2]={IsHuman(0),IsHuman(1)};
        if(g_roundMenu) ui::Draw(d3d,4,g_roundCursor,human);
        else if(g_selecting) {ui::RenderFaces(); ui::Draw(d3d,1,g_selCursor,human); InterlockedIncrement(&g_selectorDraws);}
        else if(g_takeSlot>=0) {if(ui::g_bar) ui::Draw(d3d,2,g_takeSlot,human);}
        else if(ui::g_box&&g_rewindTarget<0&&ui::ReplayHudShown()) ui::Draw(d3d,3,0,human);
    }
}
static HRESULT __stdcall PresentHook(void* dev,const RECT* a,const RECT* b,HWND w,const void* r) {
    if(PresentSkip()) return S_OK;
    PresentDraw(static_cast<IDirect3DDevice9*>(dev));
    return OrigPresent(dev)(dev,a,b,w,r);
}
static bool PatchPresent(void** vt) {
    if(vt[17]==reinterpret_cast<void*>(&PresentHook)) return true;
    if(g_ppCount>=4) return false;
    DWORD old=0,ig=0;
    if(!VirtualProtect(&vt[17],4,PAGE_READWRITE,&old)) return false;
    g_pp[g_ppCount]={vt,reinterpret_cast<PresentFn>(vt[17])};
    InterlockedIncrement(&g_ppCount);
    InterlockedExchange(reinterpret_cast<volatile LONG*>(&vt[17]),static_cast<LONG>(reinterpret_cast<DWORD>(&PresentHook)));
    VirtualProtect(&vt[17],4,old,&ig);
    return true;
}

constexpr DWORD RVA_GRAPHICS=0x2080938;
static void CheckGameDevice() {
    const DWORD gfx=Read(g_base+RVA_GRAPHICS); if(!gfx) return;
    const DWORD dev=Read(reinterpret_cast<void*>(gfx+0xC4)); if(!dev) return;
    void** vt=reinterpret_cast<void**>(Read(reinterpret_cast<void*>(dev)));
    if(!vt||Read(&vt[17])==reinterpret_cast<DWORD>(&PresentHook)) return;
    const bool ok=PatchPresent(vt);
    char l[160];sprintf_s(l,"Affichage : le peripherique du jeu a sa propre table (outil graphique intercale ?) : %s.",ok?"accroche":"ECHEC");Log(l);
}

static bool HookPresent() {
    HMODULE d3d=GetModuleHandleA("d3d9.dll"); if(!d3d) return false;
    typedef IDirect3D9* (WINAPI *CreateFn)(UINT);
    CreateFn create=reinterpret_cast<CreateFn>(GetProcAddress(d3d,"Direct3DCreate9"));
    if(!create) return false;
    HWND w=CreateWindowExA(0,"STATIC","rt",WS_POPUP,0,0,8,8,nullptr,nullptr,nullptr,nullptr);
    IDirect3D9* d=create(D3D_SDK_VERSION);
    bool ok=false;
    if(d&&w) {
        D3DPRESENT_PARAMETERS pp={}; pp.Windowed=TRUE; pp.SwapEffect=D3DSWAPEFFECT_DISCARD; pp.hDeviceWindow=w;
        IDirect3DDevice9* dev=nullptr;
        if(SUCCEEDED(d->CreateDevice(D3DADAPTER_DEFAULT,D3DDEVTYPE_HAL,w,D3DCREATE_SOFTWARE_VERTEXPROCESSING|D3DCREATE_MULTITHREADED,&pp,&dev))&&dev) {
            ok=PatchPresent(*reinterpret_cast<void***>(dev));
            dev->Release();
        }
    }
    if(d) d->Release();
    if(w) DestroyWindow(w);
    return ok;
}

typedef void(__cdecl* SceneFrameFn)(float);
static bool g_sceneFrameOk=false;

static DWORD PHOTO_START=0xF00000, PHOTO_SIZE=0x200000;
static bool g_photos=false; static volatile LONG g_photoReq=0; static LONG g_photoCount=0; static BYTE* g_photoBuf=nullptr;

struct PhotoHeader { char magic[4]; DWORD index,frame,fightState,scene,camera,takeSlot,start,size; };
static BYTE CurrentCamera() { BYTE c=0xFF; Copy(&c,g_base+0xFC7159,1); return c; }
static DWORD g_photoKind=0;
static void TakePhoto() {
    if(!g_photoBuf) g_photoBuf=static_cast<BYTE*>(VirtualAlloc(nullptr,PHOTO_SIZE,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!g_photoBuf) return;
    for(DWORD o=0;o<PHOTO_SIZE;o+=0x1000) Copy(g_photoBuf+o,g_base+PHOTO_START+o,0x1000);
    PhotoHeader h={{'P','H','O','1'},static_cast<DWORD>(++g_photoCount),PlayerFrame(),At(RVA_FIGHT_STATE),cp::CurrentScene(),CurrentCamera(),
                   g_photoKind,PHOTO_START,PHOTO_SIZE};

    static const char* kinds[4]={"F8","au point","apres le retour","au FIGHT"};
    char l[160];sprintf_s(l,"Photo %lu (%s) : image %lu, etat %lu, scene %lu, camera %lu.",h.index,kinds[g_photoKind<4?g_photoKind:0],h.frame,h.fightState,h.scene,h.camera);Log(l);
    if(!g_photoKind) MessageBeep(MB_ICONASTERISK);
}

struct MatchVar { DWORD rva,size; };

static const MatchVar kMatchVars[]={{0x10885BC,1},{0xCD6D9E,1},{0xF8A9B8,1}};
constexpr DWORD RVA_UI_REG=0xF8A770, RVA_HUD_VT=0xC0CAFC;
struct MatchState { bool saved; BYTE vals[64]; DWORD hudObj,hudArr,hudCount,hudShown[2]; DWORD hudSprite[8][4]; BYTE hudBytes[8][4][0xF0]; };
static MatchState g_match[17];

static DWORD g_blankObj=0,g_blankArr=0,g_blankCount=0; static DWORD g_blankSprite[8][2]; static BYTE g_blankBytes[8][2][0xF0];
static DWORD FindHud() {
    DWORD n=0,arr=0; Copy(&n,g_base+RVA_UI_REG+4,4); Copy(&arr,g_base+RVA_UI_REG+0xC,4);
    if(!arr||n>4096) return 0;
    for(DWORD i=0;i<n;++i){DWORD e=0,vt=0; if(Copy(&e,reinterpret_cast<void*>(arr+i*4),4)&&e&&Copy(&vt,reinterpret_cast<void*>(e),4)&&vt==reinterpret_cast<DWORD>(g_base+RVA_HUD_VT)) return e;}
    return 0;
}
static void MatchSave(MatchState& ms) {
    DWORD o=0; for(const MatchVar& v : kMatchVars){Copy(ms.vals+o,g_base+v.rva,v.size); o+=v.size;}
    ms.saved=true;
    ms.hudCount=0; ms.hudObj=FindHud(); if(!ms.hudObj) return;
    DWORD cnt=0; Copy(&cnt,reinterpret_cast<void*>(ms.hudObj+0x1AC),4); Copy(&ms.hudArr,reinterpret_cast<void*>(ms.hudObj+0x1B4),4);
    Copy(ms.hudShown,reinterpret_cast<void*>(ms.hudObj+0x200),8);
    if(cnt>8||!ms.hudArr) return;
    for(DWORD i=0;i<cnt;++i) {
        DWORD m=0; if(!Copy(&m,reinterpret_cast<void*>(ms.hudArr+i*4),4)||!m||!Copy(ms.hudSprite[i],reinterpret_cast<void*>(m),16)){cnt=i;break;}
        for(DWORD k=0;k<4;++k) if(!ms.hudSprite[i][k]||!Copy(ms.hudBytes[i][k],reinterpret_cast<void*>(ms.hudSprite[i][k]),0xF0)) ms.hudSprite[i][k]=0;
    }
    ms.hudCount=cnt;
    if(!g_base[0xFD0549]&&!g_base[0xFD0C11]&&cnt) {
        g_blankObj=ms.hudObj; g_blankArr=ms.hudArr; g_blankCount=cnt;
        for(DWORD i=0;i<cnt;++i) for(DWORD j=0;j<2;++j){g_blankSprite[i][j]=ms.hudSprite[i][1+2*j]; memcpy(g_blankBytes[i][j],ms.hudBytes[i][1+2*j],0xF0);}
    }
}
static void MatchRestore(const MatchState& ms) {
    if(!ms.saved||g_base[0x10885BC]==ms.vals[0]) return;
    const BYTE from=g_base[0x10885BC];
    RT_TRY {DWORD o=0; for(const MatchVar& v : kMatchVars){memcpy(g_base+v.rva,ms.vals+o,v.size); o+=v.size;}} RT_EXCEPT {}
    unsigned sprites=0; const char* hud="introuvable";
    if(ms.hudObj&&ms.hudObj==FindHud()) {
        DWORD cnt=0,arr=0; Copy(&cnt,reinterpret_cast<void*>(ms.hudObj+0x1AC),4); Copy(&arr,reinterpret_cast<void*>(ms.hudObj+0x1B4),4);
        hud="change";
        if(cnt==ms.hudCount&&arr==ms.hudArr) {
            hud="remis";
            RT_TRY {
                if(g_blankObj==ms.hudObj&&g_blankArr==arr&&g_blankCount==cnt) {
                    for(DWORD i=0;i<cnt;++i) {
                        DWORD now[4]={}; DWORD m=*reinterpret_cast<DWORD*>(arr+i*4); if(!m) continue; memcpy(now,reinterpret_cast<void*>(m),16);
                        for(DWORD j=0;j<2;++j) {
                            BYTE* sp=reinterpret_cast<BYTE*>(g_blankSprite[i][j]);
                            if(!sp||now[1+2*j]!=g_blankSprite[i][j]) continue;
                            memcpy(sp,g_blankBytes[i][j],0xF0); ++sprites;
                        }
                    }
                } else hud="sans modele des marques eteintes";
                DWORD shown[2]={g_base[0xFD0549],g_base[0xFD0C11]};
                memcpy(reinterpret_cast<void*>(ms.hudObj+0x200),shown,8);
                typedef void(__fastcall* HudRefreshFn)(DWORD obj,DWORD unused);
                reinterpret_cast<HudRefreshFn>(g_base+0x6CED30)(ms.hudObj,0);
            } RT_EXCEPT {hud="ECHEC";}
        }
    }
    char l[160];sprintf_s(l,"Etat du match remis : round %u -> %u, affichage des rounds %s (%u sprite(s)).",from+1,ms.vals[0]+1,hud,sprites);Log(l);
}
static void FrameEnd() {
    if(!g_on) return;
    if(Online()) {InterlockedIncrement(&g_onlineSkips); return;}

    cp::hashMode=(g_rewindTarget>=0&&!g_rewindPending&&!g_restartAsked)?2:(g_takeSlot<0&&g_rewindTarget<0&&ReplayPlaying())?1:0;
    if(InterlockedExchange(&g_camResetReq,0)) ResetReplayCamera();
    {
        static BYTE lastOn=0; const BYTE on=g_base[RVA_ROUND_ON];
        if(!ReplayPlaying()) lastOn=0;
        else {
            if(on&&!lastOn) {
                const LONG f=static_cast<LONG>(PlayerFrame());
                NoteRoundStart(f);
                InterlockedExchange(&cp::fullWindowStart,f);
                if(g_photos){g_photoKind=3; TakePhoto();}
                if(g_roundSeek==2&&CurrentRound(f)>g_seekFromRound) EndRoundSeek("arrive au debut du round suivant");

                const bool arriving=g_rewindTarget>=0&&g_seenReset&&!g_restartAsked&&!g_rewindPending&&f>=g_rewindTarget-2;
                if(g_roundPoints&&g_takeSlot<0&&!g_selecting&&(g_rewindTarget<0||arriving)) {
                    InterlockedExchange(&g_roundSaveIdx,CurrentRound(f));
                    InterlockedExchange(&cp::requestSave,1);
                }
            }
            lastOn=on;
        }
        if(g_roundSeek==2&&!ReplayPlaying()) EndRoundSeek("fin du replay, pas de round suivant");
    }
    InterlockedExchange(&cp::keepAcrossRounds,g_roundPoints==2&&g_takeSlot<0?1:0);

    if(g_restartAsked||g_rewindPending) BanksClear("redemarrage du replay");
    if(g_roundPoints==2&&(cp::requestSave||g_bankLoadReq>=0)&&g_engineRound>=0&&g_engineRound<16&&cp::active) {

        LONG k=g_engineRound; if(!g_banks[k]) g_banks[k]=cp::BankNew();
        if(g_banks[k]) cp::BankStore(*g_banks[k]);
    }
    if(cp::requestSave&&g_roundSaveIdx<0) {InterlockedExchange(&g_engineRound,-1); g_engineBanked=false;}
    {
        const LONG k=InterlockedExchange(&g_bankLoadReq,-1);
        if(k>=0) {
            const bool ok=k<16&&g_banks[k]&&cp::BankLoad(*g_banks[k]);
            if(ok){InterlockedExchange(&g_engineRound,k); g_engineBanked=true; InterlockedExchange(&cp::requestRestore,1);}
            else InterlockedExchange(&cp::lastResult,2);
            char l[96];sprintf_s(l,"Point du round %ld %s.",k+1,ok?"remis dans le moteur depuis la banque":"introuvable en banque");Log(l);
        }
    }
    const LONG savesBefore=cp::saveCount;
    cp::Frontier(g_player);
    if(cp::saveCount!=savesBefore) {
        const LONG k=InterlockedExchange(&g_roundSaveIdx,-1);
        InterlockedExchange(&g_engineRound,k); g_engineBanked=false;
    } else if(!cp::requestSave) InterlockedExchange(&g_roundSaveIdx,-1);
    if(g_roundPoints==2&&g_engineRound>=0&&g_engineRound<16&&!g_engineBanked&&cp::active&&cp::hashedFrames>cp::stableFrames) {
        LONG k=g_engineRound; if(!g_banks[k]) g_banks[k]=cp::BankNew();
        if(g_banks[k]&&cp::BankStore(*g_banks[k])) {g_engineBanked=true; char l[96];sprintf_s(l,"Point du round %ld mis en banque (image %lu).",k+1,cp::savedFrame);Log(l);}
    }
    {
        static LONG saves=0,restores=0;
        const LONG slot=g_engineRound>=0&&g_engineRound<16?g_engineRound:16;
        if(cp::saveCount!=saves){saves=cp::saveCount; MatchSave(g_match[slot]);}
        if(cp::restoreCount!=restores){restores=cp::restoreCount; MatchRestore(g_match[slot]);}
    }
    if(g_photos) {
        static LONG saves=0,restores=0;
        if(cp::saveCount!=saves) {saves=cp::saveCount; g_photoKind=1; TakePhoto();}
        if(cp::restoreCount!=restores) {restores=cp::restoreCount; g_photoKind=2; TakePhoto();}
        if(InterlockedExchange(&g_photoReq,0)) {g_photoKind=0; TakePhoto();}
    }
    const LONG step=InterlockedIncrement(&g_stepInUpdate);
    if(g_sceneFrameOk && g_extraTicks>0 && step<1+g_extraTicks)
        RT_TRY{reinterpret_cast<SceneFrameFn>(g_base+0x597AA0)(1.0f);}RT_EXCEPT{}
}

static void PhysicsSeen(DWORD object) {if(g_on&&!Online()) cp::NotePhysics(object);}
static void ComponentSeen(DWORD component) {if(g_on&&!Online()) cp::NoteComponent(component);}
static void AllocSeen(DWORD result,DWORD size) {if(g_on&&!Online()&&size&&size<0x4000000) cp::RecordAllocation(result,size);}
static DWORD WINAPI Keys(void*) {
    bool f5=false,f6=false,fl=false,fr=false,fe=false,fx=false;
    DWORD openedAt=0; LONG drawsAtOpen=0; bool silentLogged=false;
    for(;;) {
        Sleep(40);
        {
            static bool wasOnline=false; const bool on=Online();
            if(on!=wasOnline) {
                char l[200];
                if(on) sprintf_s(l,"En ligne : module en veille (aucune accroche active, touches F5/F6/F7 ignorees).");
                else sprintf_s(l,"Hors ligne : module actif (%ld passages en veille, %ld actions de replay vues en ligne).",g_onlineSkips,g_onlineLeaks);
                Log(l); wasOnline=on;
            }
            if(on) {f5=f6=fl=fr=fe=fx=false; continue;}
        }
        if(ownPresent) CheckGameDevice();
        { static bool f7=false; const bool n7=(GetAsyncKeyState(VK_F7)&0x8000)!=0;
          if(n7&&!f7&&g_takeSlot>=0) ActionPrimary("F7",true); f7=n7; }
        if(g_selecting) {
            if(!openedAt) {openedAt=GetTickCount(); drawsAtOpen=g_selectorDraws;}
            else if(!silentLogged&&GetTickCount()-openedAt>1500&&g_selectorDraws==drawsAtOpen) {
                silentLogged=true;
                char l[160];sprintf_s(l,"Fenetre de choix ouverte mais jamais dessinee (%ld presentations interceptees au total).",g_presents);Log(l);
            }
        } else openedAt=0;
        const bool n5=(GetAsyncKeyState(VK_F5)&0x8000)!=0;
        if(n5&&!f5) ActionPrimary("F5");
        f5=n5;
        const bool nl=(GetAsyncKeyState(VK_LEFT)&0x8000)!=0, nr=(GetAsyncKeyState(VK_RIGHT)&0x8000)!=0;
        const bool ne=(GetAsyncKeyState(VK_RETURN)&0x8000)!=0, nx=(GetAsyncKeyState(VK_ESCAPE)&0x8000)!=0;
        if(g_selecting) {
            if((nl&&!fl)||(nr&&!fr)) SelectToggle();
            if(ne&&!fe) ActionPrimary("Entree");
            if(nx&&!fx) ActionRelease("Echap");
        }
        fl=nl; fr=nr; fe=ne; fx=nx;
        const bool n6=(GetAsyncKeyState(VK_F6)&0x8000)!=0;
        if(n6&&!f6) ActionRelease("F6");
        f6=n6;
        if(g_photos) { static bool f8=false; const bool n8=(GetAsyncKeyState(VK_F8)&0x8000)!=0;
          if(n8&&!f8) InterlockedExchange(&g_photoReq,1); f8=n8; }
    }
}
static DWORD ReadHex(const char* ini,const char* key,DWORD def) {
    char v[32]; GetPrivateProfileStringA("ReplayTakeover",key,"",v,sizeof(v),ini);
    return v[0]?strtoul(v,nullptr,0):def;
}

static void IniText(const char* ini,const char* en,const char* fr,const char* def,char* out,DWORD n) {
    GetPrivateProfileStringA("ReplayTakeover",en,"\x01",out,n,ini);if(out[0]!=1)return;
    GetPrivateProfileStringA("ReplayTakeover",fr?fr:en,def,out,n,ini);
}
static DWORD IniHex(const char* ini,const char* en,const char* fr,DWORD def){char v[32];IniText(ini,en,fr,"",v,sizeof v);return v[0]?strtoul(v,nullptr,0):def;}
static UINT IniUint(const char* ini,const char* en,const char* fr,UINT def){char v[32];IniText(ini,en,fr,"",v,sizeof v);return v[0]?static_cast<UINT>(strtoul(v,nullptr,0)):def;}

static void Install(BYTE* image,const wchar_t* iniW) {
    char ini[MAX_PATH];if(!WideCharToMultiByte(CP_ACP,0,iniW,-1,ini,MAX_PATH,nullptr,nullptr))return;
    if(!GetPrivateProfileIntA("ReplayTakeover","Enabled",0,ini)){::Log("Replay Takeover : coupe ([ReplayTakeover] Enabled=0).");return;}
    if(g_labo){::Log("Replay Takeover : coupe avec Labo=1 (le labo lit les replays).");return;}
    g_skipPresent=IniUint(ini,"SkipPresent",nullptr,1)!=0;
    g_btnTake=IniHex(ini,"TakeButton","BoutonPrise",0x4000);
    g_btnRewind=IniHex(ini,"RewindButton","BoutonRetour",0x200);
    g_btnRelease=IniHex(ini,"ReleaseButton","BoutonRendre",0x100);
    g_btnExact=IniHex(ini,"ExactRewindButton","BoutonRetourExact",0x400);
    {UINT t=IniUint(ini,"CatchUpSteps","PasRattrapage",10); g_catchTicks=t<1?1:t>16?16:t;}
    g_btnPrevRound=IniHex(ini,"PreviousRoundButton","BoutonRoundPrecedent",0x1000);
    g_btnNextRound=IniHex(ini,"NextRoundButton","BoutonRoundSuivant",0x2000);
    {UINT t=IniUint(ini,"RoundSteps","PasRound",40); g_roundTicks=t<1?1:t>120?120:t;}
    g_roundPoints=IniUint(ini,"RoundPoints","PointsRound",2); if(g_roundPoints>2) g_roundPoints=2;
    g_logButtons=kTest && IniUint(ini,"LogButtons","JournalBoutons",0)!=0;
    g_showChoice=IniUint(ini,"PlayerChoice","ChoixJoueur",1)!=0;
    g_photos=false; cp::diagEnabled=false;
    g_ownConfig=IniUint(ini,"MyButtonConfig","MaConfiguration",1)!=0;
    g_btnConfirm=IniHex(ini,"ConfirmButton","BoutonValider",0x10);
    g_btnCancel=IniHex(ini,"CancelButton","BoutonAnnuler",0x20);
    ui::g_bar=IniUint(ini,"ControlBar","BandeauReprise",1)!=0;
    ui::g_hint=IniUint(ini,"HelpLineL2","AideL2",0)!=0;
    ui::g_box=IniUint(ini,"TakeControlBox","EncartL2",1)!=0;
    {char v[32];IniText(ini,"PadStyle","StyleManette","PlayStation",v,32);ui::g_pad=(v[0]=='X'||v[0]=='x')?1:0;}
    static const BYTE feed[6]={0x55,0x8B,0xEC,0x83,0xEC,0x2C};
    static const BYTE poll[6]={0x55,0x8B,0xEC,0x83,0xEC,0x6C};
    static const BYTE fight[5]={0x55,0x8B,0xEC,0x6A,0xFF};
    if(memcmp(image+RVA_FEED,feed,6)||memcmp(image+RVA_POLLER,poll,6)||memcmp(image+RVA_FIGHT_FRAME,fight,5)||!lab::sceneFrameOk){
        ::cp::LogR("Replay Takeover : REFUS (lecteur %d, manettes %d, boucle du combat %d, scene %d : code different).",!memcmp(image+RVA_FEED,feed,6),!memcmp(image+RVA_POLLER,poll,6),!memcmp(image+RVA_FIGHT_FRAME,fight,5),lab::sceneFrameOk?1:0);return;}
    cp::allocations=static_cast<cp::Allocation*>(VirtualAlloc(nullptr,cp::allocationSlots*sizeof(cp::Allocation),MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!cp::allocations){::Log("Replay Takeover : REFUS (memoire).");return;}
    g_base=base=image; ui::B=image;
    cp::rebuildAvailable=lab::rebuildOk;
    g_sceneFrameOk=lab::sceneFrameOk;
    const bool okFeed=Detour(image+RVA_FEED,feed,6,reinterpret_cast<void*>(&FeedThunk),&g_resumeFeed);
    const bool okPoll=Detour(image+RVA_POLLER,poll,6,reinterpret_cast<void*>(&PollThunk),&g_resumePoll);
    const bool okFight=Detour(image+RVA_FIGHT_FRAME,fight,5,reinterpret_cast<void*>(&FightFrameThunk),&g_resumeFightFrame);
    g_on=okFeed&&okPoll&&okFight;
    ownPresent=!(ind::on && ind::nb>0);
    const bool okPres=ownPresent?HookPresent():true;
    if(ui::g_box&&!ui::HookHud()) Log("Interface du replay : REFUS (vtable differente), encart desactive.");
    if(ui::g_hint) Log(ui::HookText()?"Ligne d aide du replay : 'Take control' ajoute.":"Ligne d aide du replay : REFUS (code different).");
    ::cp::LogR("Replay Takeover 2.7 integre : %s (lecteur %d, manettes %d, boucle du combat %d, affichage %s, decor remis a neuf %s, rattrapage %lu pas par image).",
        g_on?"ACTIF hors ligne pendant les replays":"REFUS",okFeed,okPoll,okFight,ownPresent?(okPres?"accroche":"non"):"par l'indicateur",cp::rebuildAvailable?"oui":"non",g_catchTicks);
    if(!g_on)return;
    {char l[300];sprintf_s(l,"Touches : F5 / bouton %08lX = prendre la main ; pendant la reprise F5 / bouton %08lX = revenir au point, F6 / bouton %08lX = revenir au point et rendre la main, F7 / bouton %08lX = retour avec le decor remis a neuf.",
        g_btnTake,g_btnRewind,g_btnRelease,g_btnExact);Log(l);}
    HANDLE t=CreateThread(nullptr,0,Keys,nullptr,0,nullptr); if(t) CloseHandle(t);
}
}
