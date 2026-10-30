#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <wincrypt.h>
#include <intrin.h>
#include <float.h>
#include <cstdio>
#include <cstring>
#include <cstdarg>
#include <cstdint>
#include <cstdlib>
#include <cctype>
#include <cwchar>
#include <initializer_list>
#include <d3d9.h>
#pragma comment(lib,"advapi32.lib")
#pragma comment(lib,"user32.lib")
#include "TakeoverCompat.h"
static_assert(sizeof(void*)==4,"Module x86 uniquement");

#ifdef DOA5RB_RELEASE
constexpr bool kTest=false;
#else
constexpr bool kTest=true;
#endif
constexpr DWORD EXPECTED_TIMESTAMP=0x5a1faa36;
constexpr DWORD EXPECTED_IMAGE_SIZE=0x021f8000;
static const char* GAME_SHA="88d12d42ba49ac696de1acbb25da12615726e8b6259fc24dd6e7d4d939f89bbc";
static BYTE* g_base=nullptr;

static wchar_t g_logPath[MAX_PATH]; static bool g_logOn,g_logRaw; static SRWLOCK g_logLock=SRWLOCK_INIT; static long g_logBytes; static DWORD g_t0;
static long g_logMax=8*1024*1024;

static constexpr DWORD LOG_TAMPON=512*1024;
static char g_logTampon[2][LOG_TAMPON]; static DWORD g_logPlein; static int g_logCourant;
static SRWLOCK g_logFichierLock=SRWLOCK_INIT; static HANDLE g_logFichier=INVALID_HANDLE_VALUE; static volatile DWORD g_logFil;
static void EcrireFichier(const char* p,DWORD n) {
    if(!n)return;
    if(g_logFichier==INVALID_HANDLE_VALUE)g_logFichier=CreateFileW(g_logPath,FILE_APPEND_DATA,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,nullptr,OPEN_ALWAYS,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(g_logFichier==INVALID_HANDLE_VALUE)return;
    DWORD w=0;WriteFile(g_logFichier,p,n,&w,nullptr);
}

static bool Prendre(SRWLOCK* v,unsigned essais) {
    if(!essais){AcquireSRWLockExclusive(v);return true;}
    for(unsigned i=0;i<essais;++i){if(TryAcquireSRWLockExclusive(v))return true;Sleep(1);}
    return false;
}
static void ViderJournal(unsigned essais) {
    if(!Prendre(&g_logFichierLock,essais))return;
    if(!Prendre(&g_logLock,essais)){ReleaseSRWLockExclusive(&g_logFichierLock);return;}
    const int c=g_logCourant;const DWORD n=g_logPlein;g_logCourant=c^1;g_logPlein=0;
    ReleaseSRWLockExclusive(&g_logLock);
    EcrireFichier(g_logTampon[c],n);
    ReleaseSRWLockExclusive(&g_logFichierLock);
}
static DWORD WINAPI FilJournal(LPVOID) { for(;;){Sleep(200);ViderJournal(0);} }
static void Log(const char* t,bool crash=false) {
    if(!g_logOn || g_logBytes>g_logMax)return;
    char l[600];size_t n=0;
    for(const char* p=t;*p && n<sizeof(l)-2;) {
        size_t k=0;while(isxdigit(static_cast<unsigned char>(p[k])))++k;
        if(k>=7 && !g_logRaw){l[n++]='#';p+=k;continue;}
        if(k){for(size_t i=0;i<k && n<sizeof(l)-2;++i)l[n++]=p[i];p+=k;continue;}
        l[n++]=*p++;
    }
    l[n]=0;
    char e[640];const int k=_snprintf_s(e,sizeof e,_TRUNCATE,"t=%lu %s\n",GetTickCount()-g_t0,l);
    if(k<=0)return;
    for(int essai=0;essai<2;++essai){
        if(crash){if(!Prendre(&g_logLock,100))return;}else AcquireSRWLockExclusive(&g_logLock);
        const bool place=g_logPlein+static_cast<DWORD>(k)<=LOG_TAMPON;
        if(place){memcpy(g_logTampon[g_logCourant]+g_logPlein,e,k);g_logPlein+=k;g_logBytes+=k;}
        ReleaseSRWLockExclusive(&g_logLock);
        if(place)break;
        ViderJournal(crash?100:0);
    }
    if(crash || !g_logFil)ViderJournal(crash?100:0);
}

static BYTE* base=nullptr;
static bool Copy(void* dst,const void* src,size_t n) {
    __try { memcpy(dst,src,n); return true; }
    __except(EXCEPTION_EXECUTE_HANDLER) { memset(dst,0,n); return false; }
}
static DWORD Read(const void* p) { DWORD v=0; Copy(&v,p,4); return v; }
#include "Checkpoint.h"
#include "KoBlock.h"
#include "Scene.h"
#include "Lab.h"
#include "DetMath.h"
#include "Online.h"
#include "Audio.h"

namespace rt{static bool Actif(); static void FrameEnd(); static void PhysicsSeen(DWORD); static void ComponentSeen(DWORD); static void AllocSeen(DWORD,DWORD);
    static void BeforeUpdate(); static void AfterUpdate(); static bool PresentSkip(); static void PresentDraw(IDirect3DDevice9*); static void Install(BYTE*,const wchar_t*);}
#include "Indicateur.h"

constexpr DWORD RVA_UPDATE_PTR=0xF79E7C,RVA_UPDATE_FN=0x3F4DB0;
typedef void (__cdecl *UpdateFn)();
static UpdateFn g_origUpdate=nullptr;

typedef int (__cdecl *ImageAvecPasFn)(int);
static ImageAvecPasFn g_imageAvecPas=nullptr; static DWORD g_imageAvecPasCherche;
static void __cdecl UpdateWrapper() {
    if(!g_imageAvecPas && GetTickCount()-g_imageAvecPasCherche>=2000){g_imageAvecPasCherche=GetTickCount();
        for(const char* m:{"DOA5LR-HighFps.asi","DOA5Tools.asi"}){const HMODULE h=GetModuleHandleA(m);
            if(h && (g_imageAvecPas=reinterpret_cast<ImageAvecPasFn>(GetProcAddress(h,"HighFps_ImageAvecPas")))!=nullptr){Log("HighFps detecte : images sans pas de logique suivies (match en rollback : aussi avant Fight et apres le K.O.).");break;}}}
    if(g_imageAvecPas && !g_imageAvecPas(net::active?1:net::modeCombat?2:0)){
        InterlockedIncrement(&lab::updateCount);lab::sceneDone=false;InterlockedExchange(&lab::cutRest,0);InterlockedExchange(&lab::extraNow,-1);
        if(!lab::qpf.QuadPart)QueryPerformanceFrequency(&lab::qpf);
        QueryPerformanceCounter(&lab::updateStart);
        g_origUpdate();
        if(net::active && net::EnCombatSalon())net::LirePaquets();
        au::Report();
        return;
    }
    rt::BeforeUpdate();
    lab::UpdateStart();
    g_origUpdate();
    lab::UpdateEnd();
    rt::AfterUpdate();
    au::Report();
}
static void InstallUpdateWrapper() {
    if(g_origUpdate) return;
    DWORD* slot=reinterpret_cast<DWORD*>(g_base+RVA_UPDATE_PTR);
    const DWORD expected=reinterpret_cast<DWORD>(g_base+RVA_UPDATE_FN);
    if(*slot!=expected) {static bool said=false;if(!said && *slot){said=true;Log("Mises a jour : le point est deja pris par un autre module (Replay Takeover actif ?) : rollback impossible.");}return;}
    g_origUpdate=reinterpret_cast<UpdateFn>(expected);
    InterlockedExchange(reinterpret_cast<volatile LONG*>(slot),static_cast<LONG>(reinterpret_cast<DWORD>(&UpdateWrapper)));
    Log("Mises a jour du jeu suivies.");
}

static BYTE* g_prevCopy=nullptr; static BYTE* g_prevFibers=nullptr;
static void __cdecl InputCopyHook() { net::BeforeCopy(); reinterpret_cast<void(__cdecl*)()>(g_prevCopy)(); }

static void __cdecl FibersHook() { net::BeforeCopy(); reinterpret_cast<void(__cdecl*)()>(g_prevFibers)(); }
static BYTE* g_fightFrameFn=nullptr;

static unsigned g_dtLogs;

#ifdef DOA5RB_RELEASE
static constexpr bool g_sondeScenes=false;
#else
static bool g_sondeScenes;
#endif
static unsigned g_sondeLogs;
static void SondeScenes() {
    struct V{DWORD a[9];float sp;};static V prev;static bool first=true;
    V v;const BYTE* b=g_base;
    v.a[0]=*reinterpret_cast<const DWORD*>(b+0xF9CB54);v.a[1]=*reinterpret_cast<const DWORD*>(b+0xF9CB58);
    v.a[2]=*reinterpret_cast<const DWORD*>(b+0xFCE5F8);v.a[3]=*reinterpret_cast<const DWORD*>(b+0xFCE5F4);
    v.a[4]=*reinterpret_cast<const DWORD*>(b+0xFCE5CC);v.a[5]=b[0xFCE600];
    v.a[6]=*reinterpret_cast<const DWORD*>(b+0xD33554);v.a[7]=*reinterpret_cast<const DWORD*>(b+0xFD14CC);
    v.a[8]=*reinterpret_cast<const DWORD*>(b+0x1087A4C);v.sp=*reinterpret_cast<const float*>(b+0xDD8FBC);
    if(!first && !memcmp(&v,&prev,sizeof v))return;
    first=false;prev=v;if(g_sondeLogs>=1500)return;++g_sondeLogs;
    cp::Logf("SONDE SCENES image %lu : verrou %lu (prec %lu), scene 0x%lX, finie 0x%lX, etat %ld, drapeau %lu, attente %ld, file %lu, phase %lu, vitesse %.3f, gel %u.",
        lab::lastFrame,v.a[0],v.a[1],v.a[2],v.a[3],static_cast<long>(v.a[4]),v.a[5],static_cast<long>(v.a[6]),v.a[7],v.a[8],v.sp,b[0x10879B1]);
}

#ifdef DOA5RB_RELEASE
static constexpr bool g_testMurAot=false;
#else
static bool g_testMurAot;
#endif
static bool g_murPb; static DWORD g_murDepuis=0xFFFFFFFF; static unsigned g_murLogs;
static void MurAot() {
    if(reinterpret_cast<DWORD(__cdecl*)()>(g_base+0x5964E0)()!=28)return;
    const float sp=*reinterpret_cast<const float*>(g_base+0xDD8FBC);
    const bool scene=*reinterpret_cast<const DWORD*>(g_base+0xFCE5F8)!=0xFFFFFFFF;
    if(sp!=1.0f || scene){if(sp<0.5f)g_murPb=true;g_murDepuis=0xFFFFFFFF;return;}
    if(!g_murPb)return;
    if(g_murDepuis==0xFFFFFFFF){g_murDepuis=lab::lastFrame;return;}
    if(lab::lastFrame<g_murDepuis+60)return;
    g_murPb=false;g_murDepuis=0xFFFFFFFF;
    __try{
        const DWORD mgr=*reinterpret_cast<const DWORD*>(g_base+0x2072580);if(!mgr)return;
        BYTE* o=*reinterpret_cast<BYTE**>(mgr+0xC);if(!o)return;
        DWORD* nodes=*reinterpret_cast<DWORD**>(o+0x2C);const DWORD n=*reinterpret_cast<const DWORD*>(o+0x30);
        if(!nodes || n<=66 || n>=0x400 || !nodes[66])return;
        reinterpret_cast<void(__cdecl*)(void*,void*,int)>(g_base+0x63E280)(o+0x130,reinterpret_cast<void*>(nodes[66]),1);
        if(g_murLogs<40){++g_murLogs;cp::Logf("ESSAI MUR AOT : collision du mur devant le titan (noeud 66) remise apres le Power Blow, image %lu.",lab::lastFrame);}
    }__except(EXCEPTION_EXECUTE_HANDLER){}
}
static void __cdecl SceneFrameHook(float dt) {
    if(g_sondeScenes)SondeScenes();
    if(g_testMurAot)MurAot();

    {static float prev=1.0f;const float sp=*reinterpret_cast<const float*>(g_base+0xD2EA10);static float prevSp=1.0f;
     if((dt!=prev || sp!=prevSp) && lab::extraNow==0 && g_dtLogs<300){++g_dtLogs;cp::Logf("Rythme : dt natif de la scene %.4f (avant %.4f), vitesse du jeu %.4f, gel %u, image %lu.",dt,prev,sp,g_base[0x10879B1],lab::lastFrame);}
     prev=dt;prevSp=sp;}
    lab::lastDt=dt; if(lab::sceneDone){lab::sceneDone=false;return;} if(net::modeCombat)return;     reinterpret_cast<lab::SceneFrameFn>(g_base+0x597AA0)(dt); }

#ifdef DOA5RB_RELEASE
static constexpr bool g_labo=false;
#else
static bool g_labo;
#endif
static BYTE* g_resumeFeed=nullptr;
static void __cdecl LaboFed(){lab::Inject();}
static __declspec(naked) void OriginalFeed() {
    __asm {
        push ebp
        mov  ebp,esp
        sub  esp,0x2C
        jmp  [g_resumeFeed]
    }
}
static __declspec(naked) void FeedThunk() {
    __asm {
        call OriginalFeed
        pushad
        pushfd
        call LaboFed
        popfd
        popad
        ret
    }
}
namespace sf{static bool on=true,synchroSuivante=true; static DWORD __fastcall WriterHook(BYTE* S); static BYTE __fastcall EmitHook(BYTE* S);}
namespace d173{static void Envoyee(DWORD f,DWORD cine,const BYTE* rec); static void Voiture(const char* qui,DWORD num); static void Trace(bool emetteur);}
namespace cam{static bool garder=true; static unsigned lignes; static void __fastcall SetHook(BYTE* S,void*,DWORD a,DWORD b,DWORD c,DWORD d,DWORD e); static void __cdecl ReqPB(int a,int b,int c); static void __cdecl ReqAutre(int a,int b,int c); static void __cdecl ApplyHook(int a,int b,int c,DWORD d,int e);}
namespace guet{static void Tick(); static DWORD rva,de[2],a[2],absA,rva2;}
static void __cdecl FrameEnd() {
    rt::FrameEnd();
    au::fightThread=GetCurrentThreadId();
    BYTE* r=nullptr;{const DWORD mg=Read(g_base+0xFCE790);const DWORD mode=mg?Read(reinterpret_cast<void*>(mg+8)):0;
        if(mode==1 || (g_labo && mode==2))r=reinterpret_cast<BYTE*>(Read(reinterpret_cast<void*>(mg+0xC)));}
    const bool fight=lab::FightingNow(r);
    if(!fight)net::FinCombat();

    if(lab::sceneFrameOk && lab::sceneSteps && (net::modeCombat || g_labo) && fight && !g_base[0x10879B1]){lab::SceneFrame();lab::sceneDone=true;}
    lab::Frontier(r);
    if(fight)InterlockedExchange(&net::frontiereVue,1);
    net::AtFrontier();
    guet::Tick();
}

static BYTE* g_resumeStep=nullptr; static BYTE* g_stepByte=nullptr;
static __declspec(naked) void StepThunk() {
    __asm {
        cmp  lab::cutRest,0
        jne  skip
        mov  eax,g_stepByte
        mov  al,byte ptr [eax]
        jmp  [g_resumeStep]
    skip:
        ret
    }
}
static __declspec(naked) void FightEndThunk() {
    __asm {
        call [g_fightFrameFn]
        pushfd
        pushad
        mov ebx,esp
        sub esp,528
        and esp,0FFFFFFF0h
        fxsave [esp]
        mov esi,esp
        cld
        call FrameEnd
        fxrstor [esi]
        mov esp,ebx
        popad
        popfd
        ret
    }
}

static BYTE* g_resumePhysics=nullptr;
static void __cdecl PhysicsSeen(DWORD object) {cp::NotePhysics(object);rt::PhysicsSeen(object);}
static __declspec(naked) void PhysicsThunk() {
    __asm {
        pushfd
        pushad
        push ecx
        call PhysicsSeen
        add esp,4
        popad
        popfd
        push ebp
        mov ebp,esp
        push esi
        mov esi,ecx
        jmp [g_resumePhysics]
    }
}

static BYTE *g_resumeComponentLoad=nullptr,*g_resumeComponentSave=nullptr;
static void __cdecl ComponentSeen(DWORD component) {cp::NoteComponent(component);rt::ComponentSeen(component);}
static __declspec(naked) void ComponentLoadThunk() {
    __asm {
        pushfd
        pushad
        push ecx
        call ComponentSeen
        add esp,4
        popad
        popfd
        push ebp
        mov ebp,esp
        push -1
        jmp [g_resumeComponentLoad]
    }
}
static __declspec(naked) void ComponentSaveThunk() {
    __asm {
        pushfd
        pushad
        push ecx
        call ComponentSeen
        add esp,4
        popad
        popfd
        push ebp
        mov ebp,esp
        push -1
        jmp [g_resumeComponentSave]
    }
}

static __declspec(thread) DWORD g_allocReturns[16],g_allocSizes[16]; static __declspec(thread) int g_allocDepth;
static DWORD __cdecl AllocationEnter(DWORD ret,DWORD arg) {
    if(g_allocDepth>=16) return 0;
    g_allocReturns[g_allocDepth]=ret; g_allocSizes[g_allocDepth]=arg; ++g_allocDepth; return 1;
}
static DWORD __cdecl AllocationLeave(DWORD result) {
    --g_allocDepth;
    if(g_allocSizes[g_allocDepth]&&g_allocSizes[g_allocDepth]<0x4000000) cp::RecordAllocation(result,g_allocSizes[g_allocDepth]);
    rt::AllocSeen(result,g_allocSizes[g_allocDepth]);
    return g_allocReturns[g_allocDepth];
}
static __declspec(naked) void AllocationAfter() {
    __asm {
        push edx
        push eax
        push eax
        call AllocationLeave
        add esp,4
        mov ecx,eax
        pop eax
        pop edx
        jmp ecx
    }
}
static __declspec(naked) void AllocationThunk() {
    __asm {
        push ecx
        push edx
        push eax
        push dword ptr [esp+0x10]
        push dword ptr [esp+0x10]
        call AllocationEnter
        add esp,8
        test eax,eax
        jz keep
        mov dword ptr [esp+0xC],offset AllocationAfter
    keep:
        pop eax
        pop edx
        pop ecx
        add ecx,4
        mov eax,[ecx]
        jmp dword ptr [eax+0x14]
    }
}

static bool Detour(BYTE* target,const BYTE* expected,SIZE_T len,void* thunk,BYTE** resume) {
    if(memcmp(target,expected,len)) return false;
    *resume=target+len;
    BYTE patch[16]={0xE9};if(len>sizeof(patch))return false;
    *reinterpret_cast<DWORD*>(patch+1)=reinterpret_cast<DWORD>(thunk)-(reinterpret_cast<DWORD>(target)+5);
    for(SIZE_T i=5;i<len;++i) patch[i]=0x90;
    DWORD old=0,ig=0;
    if(!VirtualProtect(target,len,PAGE_EXECUTE_READWRITE,&old)) return false;
    memcpy(target,patch,len);
    VirtualProtect(target,len,old,&ig);
    FlushInstructionCache(GetCurrentProcess(),target,len);
    return true;
}

static DWORD g_specPas,g_specVu; static unsigned g_specTrace,g_specTraceLignes,g_specZoneLignes;
static DWORD g_zoneDepart=0xFFFFFFFF;
static bool SpecActif(){return !net::active && g_specVu && GetTickCount()-g_specVu<1000;}
static DWORD SpecZone(){return reinterpret_cast<DWORD(__cdecl*)()>(g_base+0x5964C0)();}
static void SpecZoneCmd(DWORD cmd){
    if(!SpecActif())return;g_specTrace=300;
    if(g_specZoneLignes<400){++g_specZoneLignes;cp::Logf("Spectateur : commande de zone n%lu au pas du flux %lu (zone %lu).",cmd,g_specPas,SpecZone());}}
static void SpecZoneSet(DWORD zone,DWORD ret){
    if(!SpecActif())return;g_specTrace=300;
    if(g_specZoneLignes>=400)return;++g_specZoneLignes;const DWORD b=reinterpret_cast<DWORD>(g_base);
    if(ret>=b && ret<b+EXPECTED_IMAGE_SIZE)cp::Logf("Spectateur : bascule vers la zone %lu (appel de game+%06lX) au pas du flux %lu (zone %lu avant).",zone,ret-b,g_specPas,SpecZone());
    else cp::Logf("Spectateur : bascule vers la zone %lu (appel hors du jeu : correction du spectateur) au pas du flux %lu (zone %lu avant).",zone,g_specPas,SpecZone());}

static BYTE* g_zoneOrig[3]; static volatile LONG g_zoneBlocked; static unsigned g_zoneLogs;
static DWORD __cdecl ZoneGate(DWORD cmd) {
    if(*reinterpret_cast<const DWORD*>(g_base+0x1087A4C)!=4)return 0;
    const bool pred=lab::prepared && lab::SeqGuardZone() && lab::Speculative();
    if(g_zoneLogs<400){++g_zoneLogs;cp::Logf("SCENE ZONE : bascule de zone par script (n%lu) pendant l'image %ld (confirmee %ld) : %s.",cmd,sc::ctxFrame,sc::ctxConf,pred?"ATTEND (image predite)":"execute");}
    if constexpr(kTest){SpecZoneCmd(cmd);if(!pred)net::TraceTransition();}
    if(pred){InterlockedExchange(&sc::blocked,1);InterlockedIncrement(&sc::nBlocked);InterlockedIncrement(&g_zoneBlocked);return 1;}
    InterlockedExchange(&sc::fired,1);return 0;
}
static __declspec(naked) void ZoneThunk56() {
    __asm {
        pushad
        push 56
        call ZoneGate
        add  esp,4
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  zattend
        mov  eax,g_zoneOrig
        jmp  eax
    zattend:
        mov  eax,6
        ret
    }
}
static __declspec(naked) void ZoneThunk145() {
    __asm {
        pushad
        push 145
        call ZoneGate
        add  esp,4
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  zattend
        mov  eax,g_zoneOrig+4
        jmp  eax
    zattend:
        mov  eax,6
        ret
    }
}
static __declspec(naked) void ZoneThunk147() {
    __asm {
        pushad
        push 147
        call ZoneGate
        add  esp,4
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  zattend
        mov  eax,g_zoneOrig+8
        jmp  eax
    zattend:
        mov  eax,6
        ret
    }
}

static BYTE* g_sceneStopResume=nullptr; static DWORD g_sceneMgrVar; static unsigned g_aotRel;
#ifdef DOA5RB_RELEASE
static constexpr bool g_testVerrouAot=false;
#else
static bool g_testVerrouAot;
#endif
static bool Where(DWORD v,char* out,size_t n);static bool AfterCall(DWORD v);
static void __cdecl AotLockRelease(DWORD esp) {
    if(*reinterpret_cast<const DWORD*>(g_base+0xFCE5F8)!=0x4F2)return;
    DWORD* l=reinterpret_cast<DWORD*>(g_base+0xF9CB54);
    if(g_aotRel<40){++g_aotRel;
        char t[600];size_t m=_snprintf_s(t,sizeof t,_TRUNCATE,"%s : arret de la scene de suite 0x4F2 (verrou %lu, etat %ld)%s, image %lu ; pile :",g_testVerrouAot?"ESSAI AOT":"SONDE SCENES",*l,
            *reinterpret_cast<const long*>(g_base+0xFCE5CC),(g_testVerrouAot && *l)?" : commandes rendues":"",lab::lastFrame);
        unsigned k=0;for(DWORD a=esp;a<esp+0x1000 && k<16;a+=4){DWORD v=0;if(!Copy(&v,reinterpret_cast<const void*>(a),4))break;char w[32];if(!Where(v,w,sizeof w) || !AfterCall(v))continue;const int q=_snprintf_s(t+m,sizeof(t)-m,_TRUNCATE," %s",w);if(q>0)m+=q;++k;}
        cp::Logf("%s",t);}
    if(g_testVerrouAot && *l)*l=0;
}
static __declspec(naked) void SceneStopThunk() {
    __asm {
        pushad
        push esp
        call AotLockRelease
        add  esp,4
        popad
        push eax
        mov  eax,g_sceneMgrVar
        mov  ecx,[eax]
        pop  eax
        jmp  dword ptr [g_sceneStopResume]
    }
}

static BYTE* g_skipResume=nullptr; static unsigned g_aotSkip;
static int __cdecl AotSkipGate() {
    if(*reinterpret_cast<const DWORD*>(g_base+0xFCE5F8)!=0x4F2 || *reinterpret_cast<const long*>(g_base+0xFCE5CC)!=4)return 0;
    if(g_aotSkip<40){++g_aotSkip;cp::Logf("ESSAI AOT : saut de la scene de suite 0x4F2 refuse (jouee jusqu'au bout), image %lu.",lab::lastFrame);}
    return 1;
}
static __declspec(naked) void SceneSkipThunk() {
    __asm {
        pushad
        call AotSkipGate
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  refuse
        push ebp
        mov  ebp,esp
        push ecx
        push ebx
        jmp  dword ptr [g_skipResume]
    refuse:
        xor  eax,eax
        ret
    }
}

static BYTE* g_seqResume=nullptr;
static DWORD __cdecl SeqLaunchNote(DWORD mgr,DWORD script,DWORD id,DWORD esp);
static __declspec(naked) void SeqLaunchThunk() {
    __asm {
        pushad
        lea  eax,[esp+32]
        push eax
        push dword ptr [esp+44]
        push dword ptr [esp+44]
        push ecx
        call SeqLaunchNote
        add  esp,16
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  sbloque
        push ebp
        mov  ebp,esp
        push -1
        jmp  [g_seqResume]
    sbloque:
        ret  0x10
    }
}

static BYTE* g_reqResume=nullptr; static volatile LONG g_reqDeferred; static unsigned g_reqLogs;
static DWORD __cdecl RequestGate() {
    if(*reinterpret_cast<const DWORD*>(g_base+0x1087A4C)!=4 || !lab::prepared || !lab::SeqGuardZone() || !lab::Speculative())return 0;
    const DWORD h1=*reinterpret_cast<const DWORD*>(g_base+0xFD14BC),h2=*reinterpret_cast<const DWORD*>(g_base+0xFD14C8);
    bool q1=false,q2=false;__try{q1=h1 && *reinterpret_cast<const DWORD*>(h1)!=h1;q2=h2 && *reinterpret_cast<const DWORD*>(h2)!=h2;}__except(EXCEPTION_EXECUTE_HANDLER){}
    const LONG d=*reinterpret_cast<const LONG*>(g_base+0xD33554);const bool fl=g_base[0xD33590] && g_base[0xD33591];
    if(!q1 && !q2 && d==-1 && !fl)return 0;
    InterlockedExchange(&sc::blocked,1);InterlockedIncrement(&sc::nBlocked);InterlockedIncrement(&g_reqDeferred);
    if(g_reqLogs<40){++g_reqLogs;cp::Logf("DEMANDES : traitement des demandes de cinematique differe pendant l'image %ld (confirmee %ld) : file %s/%s, demande %ld%s.",sc::ctxFrame,sc::ctxConf,q1?"pleine":"vide",q2?"pleine":"vide",d,fl?", drapeaux":"");}
    return 1;
}
static __declspec(naked) void ReqThunk() {
    __asm {
        pushad
        call RequestGate
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  rdiffere
        push ebp
        mov  ebp,esp
        push ecx
        movss xmm0,dword ptr [ebp+8]
        jmp  [g_reqResume]
    rdiffere:
        ret
    }
}

static BYTE* g_rmKeep=nullptr; static BYTE* g_rmDel=nullptr; static volatile LONG g_rmDeferred; static unsigned g_rmLogs;
static DWORD __cdecl RemovalGate(DWORD node) {
    if(*reinterpret_cast<const DWORD*>(g_base+0x1087A4C)!=4 || !lab::prepared || !lab::SeqPhotoOn() || !lab::Speculative())return 0;
    InterlockedExchange(&sc::blocked,1);InterlockedIncrement(&sc::nBlocked);InterlockedIncrement(&g_rmDeferred);
    if(g_rmLogs<40){++g_rmLogs;DWORD id=0;Copy(&id,reinterpret_cast<const void*>(node+8),4);cp::Logf("SEQUENCES : fin du script %lu pendant l'image provisoire %ld (confirmee %ld) : noeud garde, image rejouee une fois confirmee.",id,sc::ctxFrame,sc::ctxConf);}
    return 1;
}
static __declspec(naked) void RemoveThunk() {
    __asm {
        cmp  byte ptr [esi+0xC],0
        jnz  rgarde
        pushad
        push esi
        call RemovalGate
        add  esp,4
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  rgarde
        jmp  [g_rmDel]
    rgarde:
        jmp  [g_rmKeep]
    }
}

static BYTE* g_setZoneResume=nullptr; static unsigned g_setZoneLogs;
static void __cdecl SetZoneNote(DWORD zone,DWORD ret) {
    if(*reinterpret_cast<const DWORD*>(g_base+0x1087A4C)!=4)return;
    if(!net::active && ret==reinterpret_cast<DWORD>(g_base)+0x315126)g_zoneDepart=zone;
    if constexpr(kTest){SpecZoneSet(zone,ret);net::TraceTransition();}
    if(g_setZoneLogs>=400)return;++g_setZoneLogs;
    const DWORD b=reinterpret_cast<DWORD>(g_base);const unsigned depart=g_base[0xFCDACC];
    if(ret>=b && ret<b+EXPECTED_IMAGE_SIZE)cp::Logf("SCENE ZONE : bascule vers la zone %lu (appel de game+%06lX) pendant l'image %ld (confirmee %ld)%s ; depart %02X.",zone,ret-b,sc::ctxFrame,sc::ctxConf,sc::gate?" : IMAGE PREDITE":"",depart);
    else cp::Logf("SCENE ZONE : bascule vers la zone %lu (appel hors du jeu) pendant l'image %ld (confirmee %ld)%s ; depart %02X.",zone,sc::ctxFrame,sc::ctxConf,sc::gate?" : IMAGE PREDITE":"",depart);
}
static __declspec(naked) void SetZoneThunk() {
    __asm {
        pushad
        push dword ptr [esp+32]
        push dword ptr [esp+40]
        call SetZoneNote
        add  esp,8
        popad
        push ebp
        mov  ebp,esp
        mov  eax,[ebp+8]
        jmp  [g_setZoneResume]
    }
}
static void ReleveGel();
static void FreeThunk(); static BYTE* g_resumeFree=nullptr;

static unsigned g_flowEtatLogs;
static bool FlowEtatGate(int etat) {
    const bool pred=sc::gate!=0;
    if(pred){InterlockedExchange(&sc::blocked,1);InterlockedIncrement(&sc::nBlocked);}
    else{InterlockedExchange(&sc::fired,1);lab::FlowSuiviArme(static_cast<DWORD>(sc::ctxFrame),etat==2?"passage a l'etat 2":"passage a l'etat 3");}
    if(g_flowEtatLogs<20){++g_flowEtatLogs;cp::Logf("Flow haut : passage a l'etat %d pendant l'image %ld (confirmee %ld) : %s.",etat,sc::ctxFrame,sc::ctxConf,pred?"IGNORE (image predite)":"execute");}
    return !pred;
}
static void __fastcall FlowEtat2Hook(BYTE* self){if(FlowEtatGate(2))reinterpret_cast<void(__fastcall*)(BYTE*)>(g_base+0x5FEFA0)(self);}

static void __fastcall FlowEtat3Hook(BYTE* self){if(FlowEtatGate(3))reinterpret_cast<void(__fastcall*)(BYTE*)>(g_base+0x5FDF50)(self);}

static unsigned g_pileLogs; static BYTE* g_pileResume=nullptr;
static void __cdecl PileRenduRetrait(DWORD obj) {
    DWORD* tete=reinterpret_cast<DWORD*>(g_base+0x20842BC);
    __try{
        DWORD prec=0,cur=*tete;unsigned rang=0;
        while(cur && rang<256){
            DWORD* lien=reinterpret_cast<DWORD*>(cur+4);
            if(cur==obj){const DWORD suiv=*lien;*lien=0;if(prec)*reinterpret_cast<DWORD*>(prec+4)=suiv;else *tete=suiv;
                if(rang && g_pileLogs<40){++g_pileLogs;cp::Logf("RENDU : objet retire de la pile au rang %u (pas au sommet) : il serait reste dans la pile apres sa destruction (lab172).",rang);}
                return;}
            prec=cur;cur=*lien;++rang;}
    }__except(EXCEPTION_EXECUTE_HANDLER){}
}
static unsigned g_homeCasseLogs;
static void __fastcall HomeBreakHook(BYTE* self,void*,DWORD id){
    DWORD sc0=0,tab=0,n=0;
    __try{sc0=*reinterpret_cast<const DWORD*>(self);if(sc0){tab=*reinterpret_cast<const DWORD*>(sc0+0x2C);n=*reinterpret_cast<const DWORD*>(sc0+0x30);}}__except(EXCEPTION_EXECUTE_HANDLER){sc0=0;}
    const bool hors=id!=0x3FF && (!sc0 || !tab || n>4096 || (id&0x3FF)>=n);
    if(g_homeCasseLogs<40){++g_homeCasseLogs;cp::Logf("Home (cour) : casse de l'objet %04lX.%04lX (indice %lu, %lu entree(s) dans le tableau de la scene)%s.",id>>16,id&0xFFFF,id&0x3FF,n,hors?" : HORS DU TABLEAU, ignoree":"");}
    if(hors)return;
    reinterpret_cast<void(__fastcall*)(BYTE*,void*,DWORD)>(g_base+0x5FB5E0)(self,nullptr,id);
}
#include "Takeover.h"
static DWORD WINAPI Keys(void*) {
    Log(au::HookSetEvent()?"Son : SetEvent du fil du combat suivi.":"Son : REFUS de l accroche SetEvent.");
    Log(au::Install()?"Son : voix XAudio2 2.7 suivies (sons des recalculs dedoublonnes).":"Son : REFUS de l accroche XAudio2 2.7.");
    bool f5=false;LONG majVue=0;DWORD majDepuis=GetTickCount();bool gelNote=false;
    for(;;) { Sleep(40); InstallUpdateWrapper(); net::TicSalon(); net::TicPoignee();
        {
            const LONG m=lab::updateCount;const DWORD now=GetTickCount();
            if(m!=majVue || !(net::active || (g_labo && lab::prepared))){majVue=m;majDepuis=now;gelNote=false;}
            else if(!gelNote && now-majDepuis>3000){gelNote=true;ReleveGel();}
        }

        DWORD pid=0;HWND w=GetForegroundWindow();if(w)GetWindowThreadProcessId(w,&pid);
        const bool touche=(GetAsyncKeyState(VK_F5)&0x8000)!=0,bas=touche && pid==GetCurrentProcessId();
        if(touche && !f5 && !bas)Log("F5 : fenetre du jeu pas au premier plan, abandon ignore.");
        if(bas && !f5){if(net::active)InterlockedExchange(&net::demandeAbandon,1);
            else if(net::modeCombat)InterlockedExchange(&net::demandeAbandonNatif,1);
            else if(!rt::Actif())Log("F5 : aucun combat contre un adversaire avec le mod en cours, abandon ignore.");}
        f5=touche; }
}

static bool HashMatches(const char* path,const char* expected) {
    HANDLE f=CreateFileA(path,GENERIC_READ,FILE_SHARE_READ,nullptr,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(f==INVALID_HANDLE_VALUE)return false;
    HCRYPTPROV p=0;HCRYPTHASH h=0;bool ok=false;DWORD read=0;BYTE buf[65536],dig[32];DWORD n=32;
    if(!CryptAcquireContextA(&p,nullptr,nullptr,PROV_RSA_AES,CRYPT_VERIFYCONTEXT))goto done;
    if(!CryptCreateHash(p,CALG_SHA_256,0,0,&h))goto done;
    for(;;){if(!ReadFile(f,buf,sizeof(buf),&read,nullptr))goto done;if(!read)break;if(!CryptHashData(h,buf,read,0))goto done;}
    if(CryptGetHashParam(h,HP_HASHVAL,dig,&n,0)){char hex[65];for(unsigned i=0;i<32;++i)sprintf_s(hex+i*2,3,"%02x",dig[i]);ok=strcmp(hex,expected)==0;}
done:
    if(h)CryptDestroyHash(h);if(p)CryptReleaseContext(p,0);CloseHandle(f);return ok;
}
static BYTE* CallTarget(BYTE* image,DWORD at) {
    BYTE* call=image+at; if(call[0]!=0xE8)return nullptr;
    return reinterpret_cast<BYTE*>(reinterpret_cast<DWORD>(call)+5+*reinterpret_cast<DWORD*>(call+1));
}

static bool ForeignHook(BYTE* image,BYTE* t) {
    if(!t)return false;
    auto nt=reinterpret_cast<IMAGE_NT_HEADERS32*>(image+reinterpret_cast<IMAGE_DOS_HEADER*>(image)->e_lfanew);
    if(t>=image && t<image+nt->OptionalHeader.SizeOfImage)return false;
    MEMORY_BASIC_INFORMATION m{}; return VirtualQuery(t,&m,sizeof m)==sizeof m && m.State==MEM_COMMIT && m.Type==MEM_IMAGE &&
        (m.Protect&(PAGE_EXECUTE|PAGE_EXECUTE_READ|PAGE_EXECUTE_READWRITE|PAGE_EXECUTE_WRITECOPY));
}
static bool CallSite(BYTE* image,DWORD at,DWORD target,void* hook,BYTE** prev=nullptr) {
    BYTE* call=image+at;DWORD old=0,ig=0;BYTE* t=CallTarget(image,at);
    if(t!=image+target && !(prev && ForeignHook(image,t)))return false;
    if(prev)*prev=t;
    if(!VirtualProtect(call,5,PAGE_EXECUTE_READWRITE,&old))return false;
    *reinterpret_cast<DWORD*>(call+1)=reinterpret_cast<DWORD>(hook)-reinterpret_cast<DWORD>(call)-5;
    VirtualProtect(call,5,old,&ig);FlushInstructionCache(GetCurrentProcess(),call,5);return true;
}

static void InstallCrashFilter(HINSTANCE h);
static void __fastcall SpecSceneHook(BYTE* obj,void*,void* arg);
static void __fastcall SpecRecvHook(BYTE* obj,void*,void* arg);

static UINT IniInt(const wchar_t* ini,const wchar_t* en,const wchar_t* fr,UINT def){
    const UINT v=GetPrivateProfileIntW(L"Rollback",en,-1,ini);if(v!=static_cast<UINT>(-1))return v;
    return fr?GetPrivateProfileIntW(L"Rollback",fr,static_cast<INT>(def),ini):def;}
static void IniStr(const wchar_t* ini,const wchar_t* en,const wchar_t* fr,const wchar_t* def,wchar_t* out,DWORD n){
    GetPrivateProfileStringW(L"Rollback",en,L"\x01",out,n,ini);if(out[0]!=1)return;
    GetPrivateProfileStringW(L"Rollback",fr?fr:en,def,out,n,ini);}

static DWORD g_reglages=2166136261u;
static void Reglage(const wchar_t* cle,DWORD v){
    for(const wchar_t* c=cle;*c;++c)g_reglages=(g_reglages^static_cast<BYTE>(*c))*16777619u;
    for(int i=0;i<4;++i)g_reglages=(g_reglages^((v>>(8*i))&0xFF))*16777619u;}
static UINT IniExpert(const wchar_t* ini,const wchar_t* cle,UINT def){
    const UINT v=kTest?GetPrivateProfileIntW(L"Rollback",cle,static_cast<INT>(def),ini):def;
    if(wcscmp(cle,L"RetardLocal") && wcscmp(cle,L"RedescenteDouce") && wcscmp(cle,L"MargeSansPrediction") && wcscmp(cle,L"FluxSpectateurConfirme") && wcscmp(cle,L"FluxCameraGardee") && wcscmp(cle,L"FluxSynchroSuivante"))Reglage(cle,v);
    return v;}
static DWORD WINAPI Worker(LPVOID self) {
    wchar_t dir[MAX_PATH];if(!GetModuleFileNameW(static_cast<HMODULE>(self),dir,MAX_PATH))return 0;
    wchar_t* s=wcsrchr(dir,L'\\');if(!s)return 0;s[1]=0;
    wchar_t ini[MAX_PATH];swprintf_s(ini,L"%sDOA5Rollback.ini",dir);swprintf_s(g_logPath,L"%sDOA5Rollback.log",dir);
    if(!GetPrivateProfileIntW(L"Rollback",L"Enabled",1,ini))return 0;
    g_logOn=GetPrivateProfileIntW(L"Rollback",L"Log",1,ini)!=0;
    if(g_logOn){wchar_t prec[MAX_PATH];swprintf_s(prec,L"%sDOA5Rollback.precedent.log",dir);MoveFileExW(g_logPath,prec,MOVEFILE_REPLACE_EXISTING);
        FILE* f=nullptr;if(!_wfopen_s(&f,g_logPath,L"w")&&f)fclose(f);
        DWORD id=0;HANDLE lt=CreateThread(nullptr,0,FilJournal,nullptr,0,&id);if(lt){CloseHandle(lt);g_logFil=id;}}
    g_t0=GetTickCount();
    if(IniInt(ini,L"Indicator",L"Indicateur",1)){InterlockedExchange(&ind::on,1);ind::Installer();}
    {ind::position=IniInt(ini,L"IndicatorPosition",L"IndicateurPosition",1)?1:0;const UINT h=IniInt(ini,L"IndicatorHeight",L"IndicateurHaut",62);ind::hautRef=h>1000?62:static_cast<int>(h);
     const UINT t=IniInt(ini,L"IndicatorSize",L"IndicateurTaille",1);ind::taille=t<1?1:t>4?4:static_cast<int>(t);
     ind::texte=IniInt(ini,L"IndicatorText",L"IndicateurTexte",1)?1:0;
     ind::ping=IniInt(ini,L"IndicatorPing",L"IndicateurPing",1)?1:0;
     {wchar_t lg[8]={};IniStr(ini,L"IndicatorLanguage",L"IndicateurLangue",L"EN",lg,8);ind::anglais=_wcsicmp(lg,L"FR")!=0;}
     cp::Logf("Indicateur : %s, haut %d (pour 1080), taille %d, texte %s, ping %s.",ind::position?"en haut au milieu (au-dessus du minuteur)":"coin haut gauche",ind::hautRef,ind::taille,
         !ind::texte?"coupe":ind::anglais?"FRAMES / DESYNC":"FRAMES / DESYNCHRO",ind::ping?"affiche":"coupe");}
    if constexpr(!kTest)Log("=== DOA5Rollback 0.8 (release, 0.77-lab176c-lorelei) ===");
    else Log("=== DOA5Rollback 0.77-lab176c-lorelei (test ; lorelei : 980A74 et 9812A8 (2e chute de Lorelei) dans la liste par defaut d'EssaiPermanent ; lab176c : reglages du Takeover en anglais (noms de la 2.7 lus a defaut) ; lab176b : Takeover : Hot Zone, retour par rattrapage quand le danger a change depuis le point (plantage au chargement suivant) ; lab176 : Replay Takeover 2.7 integre (hors ligne, replays, [ReplayTakeover] Enabled=1) ; lab175 : releves par image de la photo de preparation (etat du decor du round precedent : desynchro de Home en debut de round), releve du flux sur 16000 lignes ; lab174 : synchro du stage de chaque image du flux prise apres la scene du pas suivant, comme le jeu d'origine (voiture de Scramble, 2e chute de Lorelei ; FluxSynchroSuivante) ; lab173g : images du flux entieres, 20 avant et 90 pendant chaque cinematique (diagnostic) ; lab173f : scene par pas avec le multiple de pas du jeu (intros et fins de round a dt 2 comme le spectateur : voiture de Scramble) ; lab173e : minuteur de la voiture de Scramble suivi image du flux par image du flux des l'intro (diagnostic) ; lab173d : evenement camera du flux suivi, remis au recalcul d'une image (FluxCameraGardee), octets du releve lisibles ; lab173c : releve des images du flux envoyees et recues pendant les cinematiques, minuteur de la voiture de Scramble (diagnostic) ; lab173b : image du flux gardee quand le jeu l'ecrit (la lab173 attendait la fin du pas du combat : rien garde) ; lab173 : flux des spectateurs envoye depuis les images confirmees, dans l'ordre (FluxSpectateurConfirme) ; snow4 : bissection de la desynchro (empreintes image par image echangees a la 1re desynchro), garde-fou des images predites pendant une sequence sans photo ; snow3 : essai SceneHorsExe (scene des stages du module de maps photographiee), appelant des evenements de scene au journal ; snow1 : graphe du decor borne et compteurs, controle RTTI des composants, redescente du retard sans trou, empreinte des reglages ; snow2 : abandon F5 hors rollback recu, zones validees dans les valeurs de release, plage de Zack, LAB et SETTINGS a l'indicateur, pas de hausse du retard pour une fenetre d'une image, noeuds du decor suivis au labo seulement, verificateur du tas en version de test seulement, diagnostics du son et de Flow ; rendu : retrait robuste de la pile des objets de rendu (crash du spectateur a Hot Zone) ; Home (cour) : casse d'un objet hors du tableau de la scene ignoree (crash du spectateur) ; FLOW SUIVI : positions et radeau a chaque image confirmee apres un changement d'etat du haut de Flow ; Flow : poses et pistes d'animation du decor photographiees a chaque image (radeau apres un Power Blow, PoseDynamique=1 par defaut) ; ControleurCompletFlow : controleur d'animation complet du decor de Flow (essai, radeau apres un Power Blow) ; GraineG1 : generateur des effets 1 seme a chaque round (essai) ; labo : retours forces seulement sur des images predictibles en ligne, trace J1/J2 +30 et +4F0 ; labo : pas de retour force avant un lancement ou une fin de sequence ; labo : pas de retour force avant un lancement ou une fin de sequence ; Flow haut : passages aux etats 2 et 3 traites comme des evenements de scene (liberation en double) ; labo : pas de retour force avant un evenement execute ; composants du decor perimes ignores (plantage /GS) ; reconnaissance du sol elargie SolElargi (Flow haut, Crimson 2) ; fin anticipee apres une bascule de zone FinApresBascule (essai) ; spectateur : zone de l'hote appliquee d'apres la zone de depart notee au chargement (cliffhanger de Scramble) ; manette en clair ; spectateur : bit de zone du flux, commandes et bascules de zone au pas du flux, positions toutes les 10 images 5 s apres, nom du stage ; joueurs : positions toutes les 10 images apres une bascule de zone ; trace de la manette locale TraceManette ; horloge du decor HorlogeImage de nouveau appliquee (lab162) ; reglages du joueur en anglais, DESYNC par defaut, configuration de release, ni classe RTTI ni nom de module au journal ; lanceur du panneau de Crimson dans la photo ; modeles du panneau de Crimson dans la photo ; horloge du decor posee avant la photo de preparation ; noix de coco de Zack Island dans la photo ; modeles des citrouilles de Lorelei hante dans la photo : desynchro a l'atterrissage ; labo : releve de la citrouille ; retours forces RetoursForces ; journal ecrit en arriere-plan : plus de gel du a l'ecriture ; releve du spectateur ; indicateur : aller-retour en MS ; indicateur : FRAME(S) apres le retard, DESYNCHRO en violet ; compteurs flottants du decor remis aux retours meme s'ils ressemblent a des adresses : desynchro du panneau de Crimson ; liste des minuteries verifiee avant de garder des liens : desynchro du panneau de Crimson ; fin de round : dernieres entrees renvoyees 1 s, attente coupee a 1 s une fois le round decide ; essai du mur d'AOT : TestMurAot ; essai 2 AOT : scene de suite jouee jusqu'au bout ; pile a l'arret de la scene de suite AOT ; essai du correctif AOT : TestVerrouAot ; sonde des scenes et du verrou des commandes ; spectateur : bascule de zone recue corrigee ; graphe du decor prepare a l'avance aussi apres une chute en plein round ; marge courte apres un ralenti par zone ; photo : 6 generateurs d'origine + celui de Crimson par zone ; Crimson : objet qui tombe dans la photo ; zones du module de maps par famille RTTI ; 11 generateurs aleatoires dans la photo, 2 de plus re-semes ; classe RTTI des scenes du module de maps ; noms des stages PS4 ; labo : 1re image apres une preparation sans prediction si fenetre (plancher de confirmation) ; indicateur en haut au milieu, au-dessus du minuteur ; Flow : temps de la scene note a la preparation ; ralenti : demande et cache remis avec le facteur ; Flow : drapeau de l'explosion du radeau dans la photo ; Flow : cache de poses ET pistes des animations dans la photo (radeau) ; labo : guet arme sur la racine du radeau (GuetRadeau) ; labo : controleurs d'animation suivis avec les noeuds ; labo : noeuds signales a leur 1re difference ; labo : noeuds du decor compares un par un a la reference (NoeudsDe/NoeudsA) ; Flow haut : tous les modeles du tableau dans la photo ; labo : sonde, blocs de l'image du jeu ecrits un par un ; labo : sonde, prediction coupee seulement sur l'image sondee ; labo : sonde de reference avec les objets du tas ; horloge du decor absolue utilisable en ligne (HorlogeImage=2 : Flow) ; labo : horloge du decor absolue (HorlogeImage=2), aussi dans la reference ; 32 zones en essai permanent, marge apres ralenti reglable (MargeRalenti) ; Streets et Scramble : controleurs d'animation complets et pistes par os dans la photo (train) ; labo : reference preparee de nouveau apres un changement de zone ; labo : sonde de reference aussi dans la passe avec prediction ; nouvelle preparation apres un changement de zone en cours de round : Streets ; labo : graine du 1er round a l'image 59 du replay ; generateurs des effets 3 a 5 resynchronises a chaque round : tigres de Tiger Show ; citrouille de Lorelei hante dans la photo ; entrees sur le canal Steam 4, marque de salon 72 ; temps d'animation : vrai tableau des modeles de la scene ; diagnostic des evenements de stage DiagEvenements ; objets de scene detruits ecartes de la photo, preparation sans VirtualQuery (gel du debut de round) ; images sans pas de logique de HighFps (reprise du collegue) ; journal 32 Mo avec SuiviEtat, bloc de scene suivi apres l'image 8192 ; poignee : decision a 90 images, attente 1,5 s si debut confirme ; diag poignee de main sautee ; poignee de main : decision a 30 images, attente sur place 0,3 s, gel toujours retire ; liste des minuteries remise entiere, remise du bloc de scene a travers un changement de structure, suivi continu SuiviEtat, etat complet a la desynchro, nom du stage, journal 8 Mo ; poignee de main decidee par J1, annonce gardee 2 s apres le debut, indicateur 4 couleurs + retard ; 0.77 + mode labo, diagnostic, mesure des suites, detail des empreintes a la desynchro, fin detectee en option, F9 au labo, rejeu d'evenement termine sur son image, porte des evenements juste en local, sonde de l'etat non photographie, ralenti remis a 1 au retour, plages en plus ; meme protocole que la 0.77) : rollback dans le combat en ligne des salons (2 joueurs). Tout se fait en memoire. ===");
    {UINT d=IniExpert(ini,L"RetardLocal",2);net::localDelay=d>6?6:d;net::modeRetard=static_cast<LONG>(net::localDelay);}
    {
        wchar_t r[16]={};IniStr(ini,L"Delay",L"Retard",L"",r,16);
        if(!_wcsicmp(r,L"AUTO"))net::modeRetard=-1;else if(r[0]>=L'0' && r[0]<=L'9'){const long v=wcstol(r,nullptr,10);net::modeRetard=v>6?6:v;}
        lab::predictionCourHome=IniExpert(ini,L"PredictionCourHome",1)!=0;
        lab::predictionHautFlow=IniExpert(ini,L"PredictionHautFlow",1)!=0;
        lab::predictionHotZone=IniExpert(ini,L"PredictionHotZone",1)!=0;
        sf::on=IniExpert(ini,L"FluxSpectateurConfirme",1)!=0;
        cam::garder=IniExpert(ini,L"FluxCameraGardee",1)!=0;
        sf::synchroSuivante=IniExpert(ini,L"FluxSynchroSuivante",1)!=0;
        lab::predictionSequences=IniExpert(ini,L"PredictionSequences",1)!=0;
        lab::physCalme=IniExpert(ini,L"PhysiqueCalme",10);     if(lab::physCalme)cp::Logf("Labo : prediction reprise %lu image(s) apres le dernier corps physique en mouvement.",lab::physCalme);
        lab::SEQ_TAIL=IniExpert(ini,L"MargeFinSequence",0);     if(lab::SEQ_TAIL!=8)cp::Logf("Labo : marge apres la fin d'une sequence : %lu image(s).",lab::SEQ_TAIL);
        if(lab::predictionSequences)cp::Logf("Labo : PredictionSequences=1 : prediction pendant les sequences des zones d'essai (essai).");
        lab::effetsAnnules=IniExpert(ini,L"EffetsAnnules",0)!=0;
        UINT lim=IniInt(ini,L"RollbackLimit",L"LimiteRollback",net::AVANCEMAX);net::avanceMax=lim<1?1:lim>net::AVANCEMAX?net::AVANCEMAX:lim;
        net::redescenteDouce=IniExpert(ini,L"RedescenteDouce",1)!=0;
        {const UINT q=IniExpert(ini,L"MargeSansPrediction",2);net::margeSansPrediction=q>6?6:q;}
        cp::Logf("RETARD : %s ; mode sans prediction : trajet mesure + %lu image(s) (MargeSansPrediction) (snow1).",
            net::redescenteDouce?"baisse d'une image a la fois, sans lecture de manette perdue (RedescenteDouce=1)":"baisse d'un coup (RedescenteDouce=0)",net::margeSansPrediction);
    }
    lab::remiseMinuteries=IniExpert(ini,L"RemiseMinuteries",1)!=0;     if(lab::remiseMinuteries)cp::Logf("MINUTERIES : liste remise entiere aux retours quand elle tient dans le bloc de la scene (RemiseMinuteries=1).");
    lab::remisePartielle=IniExpert(ini,L"RemisePartielleScene",1)!=0;     if(lab::remisePartielle)cp::Logf("SCENE : remise partielle du bloc de la scene a travers un changement de structure (RemisePartielleScene=1).");
#ifndef DOA5RB_RELEASE
    net::suiviEtat=GetPrivateProfileIntW(L"Rollback",L"SuiviEtat",0,ini)!=0;if(net::suiviEtat){g_logMax=32*1024*1024;cp::Logf("SUIVI : suivi continu de l'etat a chaque image confirmee multiple de 30 (SuiviEtat=1) ; journal plafonne a 32 Mo.");}
    sc::diagEvt=GetPrivateProfileIntW(L"Rollback",L"DiagEvenements",0,ini)!=0;if(sc::diagEvt)cp::Logf("DIAG : evenements de stage suivis (DiagEvenements=1) : generateurs aleatoires a chaque appel n18 et fins de pas des 60 images suivantes.");
    net::traceManette=GetPrivateProfileIntW(L"Rollback",L"TraceManette",0,ini)!=0;if(net::traceManette)cp::Logf("MANETTE : trace des entrees locales a chaque changement (TraceManette=1).");
    {UINT l=GetPrivateProfileIntW(L"Rollback",L"LatenceEssai",0,ini);net::latenceEssai=l>200?200:l;if(l)cp::Logf("ESSAI : latence simulee de %lu ms sur nos paquets d'entrees.",net::latenceEssai);}
#endif
    lab::restoreStage=true;lab::sceneSteps=true;lab::safeFrames=600;net::enabled=true;
    lab::finDetectee=IniExpert(ini,L"FinDetectee",1)!=0;
    lab::solElargi=IniExpert(ini,L"SolElargi",1)!=0;if(!lab::solElargi)cp::Logf("SOL : reconnaissance d'origine (SolElargi=0).");
    lab::poseDyn=IniExpert(ini,L"PoseDynamique",1)!=0;cp::Logf(lab::poseDyn?"FLOW : poses et pistes d'animation du decor photographiees a chaque image d'apres leurs pointeurs du moment (PoseDynamique=1).":"FLOW : poses et pistes d'animation du decor : photo de la preparation seulement (PoseDynamique=0).");
    lab::ctrlCompletFlow=IniExpert(ini,L"ControleurCompletFlow",0)!=0;if(lab::ctrlCompletFlow)cp::Logf("FLOW : controleur d'animation complet des modeles du decor dans la photo (ControleurCompletFlow=1, essai).");
    lab::graineG1=IniExpert(ini,L"GraineG1",0)!=0;if(lab::graineG1)cp::Logf("GENERATEURS : generateur des effets 1 seme comme les 3 a 5 a chaque round (GraineG1=1, essai).");
    lab::finApresBascule=IniExpert(ini,L"FinApresBascule",0)!=0;if(lab::finApresBascule)cp::Logf("FIN DETECTEE : aussi apres une bascule de zone (FinApresBascule=1, essai).");
    lab::sceneHorsExe=IniExpert(ini,L"SceneHorsExe",0)!=0;if(lab::sceneHorsExe)cp::Logf("SCENE : bloc d'etat des scenes du module de maps suivi et remis aux retours (SceneHorsExe=1, essai).");
    lab::ambiantOn=IniExpert(ini,L"Ambiant",1)!=0;
#ifndef DOA5RB_RELEASE
    g_sondeScenes=GetPrivateProfileIntW(L"Rollback",L"SondeScenes",0,ini)!=0;
    g_testMurAot=GetPrivateProfileIntW(L"Rollback",L"TestMurAot",0,ini)!=0;
#endif
    if(g_testMurAot)cp::Logf("ESSAI MUR AOT : collision du mur devant le titan remise 60 images apres chaque Power Blow sur AOT (TestMurAot=1).");
    if(g_sondeScenes)cp::Logf("SONDE SCENES : verrou des commandes et scenes notes a chaque changement (SondeScenes=1, lecture seule).");
    {
        auto lire=[&](const wchar_t* cle,const wchar_t* def,DWORD* out,unsigned& n){wchar_t t[512]=L"";
            if(kTest)GetPrivateProfileStringW(L"Rollback",cle,def,t,512,ini);else wcscpy_s(t,def);
            wchar_t* p=t;while(*p && n<32){wchar_t* e;const unsigned long v=wcstoul(p,&e,16);if(e==p)break;if(v)out[n++]=v;p=e;while(*p==L',' || *p==L' ')++p;}
            Reglage(cle,n);for(unsigned i=0;i<n;++i)Reglage(L"",out[i]);};
        {UINT q=IniExpert(ini,L"MargeRalenti",90);lab::CINE_TAIL=q>600?600:q;if(lab::CINE_TAIL!=90)cp::Logf("ZONES : marge sans prediction apres un ralenti : %lu image(s) (MargeRalenti ; 90 par defaut).",lab::CINE_TAIL);}
        lire(L"EssaiPermanent",L"BFC2E8,BF58BC,BF7A24,BF9A20,97D064,97E110,97EEBC,BFF00C,9AA394,BEC570,9819A8,BEE79C,BED8F0,BFD82C,9A0C8C,C00C8C,BE95D4,BFB810,BF1C94,BF3090,BF48D0,97B0A4,977EA0,97A214,10C52F50,980A74,9812A8",lab::essaiPerm,lab::nEssaiPerm);lire(L"SansRemiseBloc",L"",lab::sansRemise,lab::nSansRemise);
        lire(L"ZonesMargeCourte",L"977EA0,97A214,10C52F50",lab::margeCourteZ,lab::nMargeCourte);{const UINT mc=IniExpert(ini,L"MargeRalentiCourte",30);lab::margeCourte=mc>600?600:mc;}
        if(lab::nMargeCourte)cp::Logf("ZONES : %u zone(s) avec une marge courte apres un ralenti (%lu images au lieu de %lu).",lab::nMargeCourte,lab::margeCourte,lab::CINE_TAIL);
        lab::physWait=IniExpert(ini,L"PhysiqueAttente",1)!=0;
        lire(L"PhysiqueZones",L"",lab::physZones,lab::nPhysZones);if(lab::nPhysZones)cp::Logf("ZONES : physique photographiee aussi dans %u zone(s) (PhysiqueZones).",lab::nPhysZones);
        if(lab::nEssaiPerm || lab::nSansRemise)cp::Logf("ZONES : %u en essai de rollback permanent, %u sans remise du bloc de scene.",lab::nEssaiPerm,lab::nSansRemise);}
    {UINT q=IniExpert(ini,L"FenetreStable",30);lab::stableNeed=q<5?5:q>600?600:q;}
    if(lab::finDetectee)cp::Logf("FIN DETECTEE : la fenetre sans prediction s'arrete quand la scene est calme depuis %lu images (plafond 600).",lab::stableNeed);

    {const UINT h=IniExpert(ini,L"HorlogeImage",2);     lab::horlogeImage=h!=0;lab::horlogeAbsolue=h==2;
     if(h)cp::Logf("HORLOGE : horloge du decor %s (HorlogeImage=%u).",h==2?"absolue, image/60 a chaque pas (identique sur les deux PC)":"posee depuis la preparation (labo)",h);}
#ifndef DOA5RB_RELEASE
    g_labo=GetPrivateProfileIntW(L"Rollback",L"Labo",0,ini)!=0;
#endif
    ind::labo=g_labo;
    g_logRaw=g_labo && GetPrivateProfileIntW(L"Rollback",L"JournalBrut",0,ini)!=0;
    if(g_logRaw && g_logMax<16*1024*1024)g_logMax=16*1024*1024;
    if(g_labo){UINT d=GetPrivateProfileIntW(L"Rollback",L"RollbackDelay",4,ini);lab::delay=d<1?1:d>8?8:d;
        UINT w=GetPrivateProfileIntW(L"Rollback",L"ModeSurImages",600,ini);lab::safeFrames=w>600?600:w;
        net::enabled=false;
        sc::diagLo=GetPrivateProfileIntW(L"Rollback",L"DiagDe",0,ini);sc::diagHi=GetPrivateProfileIntW(L"Rollback",L"DiagA",0,ini);
        lab::ralentiRemis=GetPrivateProfileIntW(L"Rollback",L"RalentiRemis",1,ini)!=0;
        lab::sondeRefAt=GetPrivateProfileIntW(L"Rollback",L"SondeRef",0,ini);if(lab::sondeRefAt)cp::Logf("LABO : SONDE REFERENCE a l'image %lu.",lab::sondeRefAt);
        lab::retoursForces=GetPrivateProfileIntW(L"Rollback",L"RetoursForces",0,ini);
        lab::releveCitr=GetPrivateProfileIntW(L"Rollback",L"ReleveCitrouille",0,ini)!=0;if(lab::releveCitr)cp::Logf("LABO : RELEVE DE LA CITROUILLE (haut de Lorelei hante), lignes CITROUILLE ref / rb.");
        {const UINT pf=GetPrivateProfileIntW(L"Rollback",L"ProfondeurForcee",4,ini);lab::profForcee=pf<1?1:pf>7?7:pf;}
        if(lab::retoursForces)cp::Logf("LABO : RETOURS FORCES toutes les %lu images de la passe rollback (profondeur %lu, memes entrees).",lab::retoursForces,lab::profForcee);
        lab::sondeAuto=GetPrivateProfileIntW(L"Rollback",L"SondeAuto",0,ini)!=0;lab::sondeMoitie=GetPrivateProfileIntW(L"Rollback",L"SondeMoitie",0,ini);
        {wchar_t g[32]=L"";GetPrivateProfileStringW(L"Rollback",L"GuetAdresse",L"",g,32,ini);guet::rva=wcstoul(g,nullptr,16);
         guet::de[0]=GetPrivateProfileIntW(L"Rollback",L"GuetDe",0,ini);guet::a[0]=GetPrivateProfileIntW(L"Rollback",L"GuetA",0,ini);
         guet::de[1]=GetPrivateProfileIntW(L"Rollback",L"GuetDe2",0,ini);guet::a[1]=GetPrivateProfileIntW(L"Rollback",L"GuetA2",0,ini);
         {wchar_t ga[32]=L"";GetPrivateProfileStringW(L"Rollback",L"GuetAbsolu",L"",ga,32,ini);if(!guet::rva)guet::absA=wcstoul(ga,nullptr,16);}
         {wchar_t g2[32]=L"";GetPrivateProfileStringW(L"Rollback",L"GuetAdresse2",L"",g2,32,ini);guet::rva2=wcstoul(g2,nullptr,16);if(guet::rva2)cp::Logf("LABO : 2e plage du guet sur game+%06lX.",guet::rva2);}
         if(guet::rva || guet::absA)cp::Logf("LABO : GUET materiel sur %s%06lX, images %lu-%lu et %lu-%lu.",guet::rva?"game+":"",guet::rva?guet::rva:guet::absA,guet::de[0],guet::a[0],guet::de[1],guet::a[1]);}
        {UINT q=GetPrivateProfileIntW(L"Rollback",L"PrepApres",250,ini);lab::prepApres1=q<250?250:q>3000?3000:q;if(q!=250)cp::Logf("LABO : 1re preparation du round 1 apres %lu images (Play Again).",lab::prepApres1);}
        {wchar_t pe[256]=L"";GetPrivateProfileStringW(L"Rollback",L"PhotoEnPlus",L"",pe,256,ini);
         wchar_t* p=pe;while(*p && cp::extraWinCount<8){wchar_t* e;const unsigned long a=wcstoul(p,&e,16);if(e==p || *e!=L'-')break;p=e+1;const unsigned long b=wcstoul(p,&e,16);if(e==p)break;
             if(b>a && b-a<=0x100000){cp::extraWin[cp::extraWinCount][0]=a;cp::extraWin[cp::extraWinCount][1]=b;++cp::extraWinCount;cp::Logf("LABO : plage en plus dans la photo : game+%06lX a game+%06lX.",a,b);}
             p=e;while(*p==L',' || *p==L' ')++p;}}
        lab::nodeDiagDe=GetPrivateProfileIntW(L"Rollback",L"NoeudsDe",0,ini);{wchar_t g[16]=L"";GetPrivateProfileStringW(L"Rollback",L"GuetRadeau",L"",g,16,ini);lab::guetRadeau=wcstoul(g,nullptr,16);}
        lab::nodeDiagA=GetPrivateProfileIntW(L"Rollback",L"NoeudsA",0,ini);if(lab::nodeDiagA)cp::Logf("LABO : noeuds du decor copies en entier aux images %lu-%lu.",lab::nodeDiagDe,lab::nodeDiagA);
        lab::sondeEcart=GetPrivateProfileIntW(L"Rollback",L"SondeEcart",60,ini);if(lab::sondeEcart<1)lab::sondeEcart=1;lab::sondeAt=GetPrivateProfileIntW(L"Rollback",L"SondeImage",0,ini);lab::sondeAt2=GetPrivateProfileIntW(L"Rollback",L"SondeImage2",0,ini);if(lab::sondeAt)cp::Logf("LABO : SONDE de l'etat non photographie aux images %lu et %lu de chaque Play Again.",lab::sondeAt,lab::sondeAt+60);
        sc::diagLo2=GetPrivateProfileIntW(L"Rollback",L"DiagDe2",0,ini);sc::diagHi2=GetPrivateProfileIntW(L"Rollback",L"DiagA2",0,ini);
        if(sc::diagHi || sc::diagHi2)cp::Logf("LABO : DIAGNOSTIC detaille des images %lu a %lu et %lu a %lu.",sc::diagLo,sc::diagHi,sc::diagLo2,sc::diagHi2);}
    {
        Reglage(L"TestMurAot",g_testMurAot?1:0);Reglage(L"TestVerrouAot",kTest?GetPrivateProfileIntW(L"Rollback",L"TestVerrouAot",0,ini):0);
        wchar_t es[MAX_PATH]=L"";if(GetModuleFileNameW(nullptr,es,MAX_PATH)){wchar_t* b=wcsrchr(es,L'\\');if(b)b[1]=0;}
        wcscat_s(es,L"DOA5LR-ExtraStages.ini");if(GetFileAttributesW(es)==INVALID_FILE_ATTRIBUTES)swprintf_s(es,L"%sDOA5LR-ExtraStages.ini",dir);
        static const struct{const wchar_t* k;INT d;} az[]={{L"AZUCHI1_Fall",0},{L"AZUCHI2_Fall",0},{L"AZUCHI2_StartCourtyard",0},{L"AZUCHI2_MeshFallback",1}};
        for(const auto& a:az)Reglage(a.k,GetPrivateProfileIntW(L"Gimmicks",a.k,a.d,es));
        net::reglagesMoi=g_reglages?g_reglages:1;
        cp::LogR("Reglages : empreinte %04lX.%04lX (reglages qui touchent la simulation ; envoyee a l'adversaire).",net::reglagesMoi>>16,net::reglagesMoi&0xFFFF);}
    char gamePath[MAX_PATH];if(!GetModuleFileNameA(nullptr,gamePath,MAX_PATH))return 0;
    if(!HashMatches(gamePath,GAME_SHA)){Log("REFUS : empreinte de game.exe differente (version 1.10C requise).");return 0;}
    Sleep(3000);
    BYTE* image=reinterpret_cast<BYTE*>(GetModuleHandleA(nullptr));
    auto dos=reinterpret_cast<IMAGE_DOS_HEADER*>(image);
    auto nt=reinterpret_cast<IMAGE_NT_HEADERS32*>(image+dos->e_lfanew);
    if(nt->FileHeader.TimeDateStamp!=EXPECTED_TIMESTAMP||nt->OptionalHeader.SizeOfImage!=EXPECTED_IMAGE_SIZE){Log("REFUS : image PE differente.");return 0;}
    g_base=base=image;
    if(GetModuleHandleA("DOA5LR-RollbackProbe.asi")||GetModuleHandleA("DOA5LR-ReplayTakeover.asi")){Log("REFUS : DOA5LR-RollbackProbe ou DOA5LR-ReplayTakeover.asi charge (les retirer : la reprise en main est integree, [ReplayTakeover] Enabled=1).");return 0;}
    {

        BYTE* tc=CallTarget(image,0x3F6829); BYTE* tf=CallTarget(image,0x3F4B1A);
        const bool okC=tc==image+0x3F52B0||ForeignHook(image,tc), okF=tf==image+0x423690||ForeignHook(image,tf);
        const bool okS=image[0x597AA0]==0x55&&CallTarget(image,0x3F4C35)==image+0x597AA0, okN=CallTarget(image,0x3F7E97)==image+0x52ABC0;
        const bool okT=image[0x423420]==0x8B&&image[0x423421]==0x0D&&*reinterpret_cast<DWORD*>(image+0x423422)==reinterpret_cast<DWORD>(image+0x108B490);
        if(!okC||!okF||!okS||!okN||!okT){cp::LogR("REFUS (rien n'est accroche) : code different (manettes %d, fibres %d, scene %d, netcode %d, pas %d). Un autre mod modifie le combat ?",okC,okF,okS,okN,okT);return 0;}
        if(tc!=image+0x3F52B0)Log("Recopie des manettes (0x3F6829) deja accrochee par un autre module (Punish Training ?) : enchainement.");
        if(tf!=image+0x423690)Log("Fibres des manettes (0x3F4B1A) deja accrochees par un autre module : enchainement.");
    }

    static const BYTE fight[5]={0x55,0x8B,0xEC,0x6A,0xFF};
    static const BYTE physicsBytes[6]={0x55,0x8B,0xEC,0x56,0x8B,0xF1};
    static const BYTE componentBytes[5]={0x55,0x8B,0xEC,0x6A,0xFF};
    static const BYTE allocationBytes[14]={0x55,0x8B,0xEC,0x83,0xC1,0x04,0x8B,0x01,0x8B,0x40,0x14,0x5D,0xFF,0xE0};
    static const BYTE callBytes[5]={0xE8,0xB4,0x11,0xF4,0xFF};
    bool ok=!memcmp(image+0x337A10,fight,5)&&!memcmp(image+0x3F6857,callBytes,5)&&!memcmp(image+0xC64D0,physicsBytes,6)&&
        !memcmp(image+0x59EC00,componentBytes,5)&&image[0x59EC05]==0x68&&!memcmp(image+0x59ED20,componentBytes,5)&&image[0x59ED25]==0x68&&
        !memcmp(image+0x7CBB80,allocationBytes,14);
    if(ok) {
        cp::allocations=static_cast<cp::Allocation*>(VirtualAlloc(nullptr,cp::allocationSlots*sizeof(cp::Allocation),MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
        BYTE* unused=nullptr;
        ok=cp::allocations&&
            Detour(image+0x7CBB80,allocationBytes,6,&AllocationThunk,&unused)&&
            Detour(image+0xC64D0,physicsBytes,6,&PhysicsThunk,&g_resumePhysics)&&
            Detour(image+0x59EC00,componentBytes,5,&ComponentLoadThunk,&g_resumeComponentLoad)&&
            Detour(image+0x59ED20,componentBytes,5,&ComponentSaveThunk,&g_resumeComponentSave);
        if(ok){g_fightFrameFn=image+0x337A10;ok=CallSite(image,0x3F6857,0x337A10,reinterpret_cast<void*>(&FightEndThunk));}
    }
    if(!ok){Log("REFUS : points de controle impossibles (code different).");return 0;}

    BYTE tickBytes[6]={0x8B,0x0D};*reinterpret_cast<DWORD*>(tickBytes+2)=reinterpret_cast<DWORD>(image+0x108B490);
    BYTE* unusedTick=nullptr;
    if(!Detour(image+0x423420,tickBytes,6,&TickCountThunk,&unusedTick)){Log("REFUS : pas par image (0x423420) : code different.");return 0;}
    {BYTE stepBytes[5]={0xA0};*reinterpret_cast<DWORD*>(stepBytes+1)=reinterpret_cast<DWORD>(image+0x1087A09);g_stepByte=image+0x1087A09;
     Log(Detour(image+0x3F6810,stepBytes,5,&StepThunk,&g_resumeStep)?"Pas du combat (0x3F6810) accroche.":"Pas du combat (0x3F6810) : accroche impossible (pas de coupure apres un evenement de scene predit).");}
    if(g_labo){static const BYTE feed[6]={0x55,0x8B,0xEC,0x83,0xEC,0x2C};
        if(Detour(image+0x3396B0,feed,6,reinterpret_cast<void*>(&FeedThunk),&g_resumeFeed))
            cp::Logf("LABO HORS LIGNE (Labo=1) : replays : 1re lecture = reference, Play Again = rollback compare (retard du J2 %lu images, fenetre sans prediction %lu images). Rollback en ligne desactive avec ce reglage.",lab::delay,lab::safeFrames);
        else Log("LABO : REFUS de l'accroche du lecteur de replay (0x3396B0, code different).");}
    {
        const DWORD mgr=reinterpret_cast<DWORD>(image+0x2072580);
        BYTE a[8]={0xA1,0,0,0,0,0x8B,0x40,0x0C}; memcpy(a+1,&mgr,4);
        BYTE b[13]={0x55,0x8B,0xEC,0x8B,0x45,0x08,0x8B,0x0D,0,0,0,0,0x50}; memcpy(b+8,&mgr,4);
        BYTE c[7]={0x8B,0x0D,0,0,0,0,0xE9}; memcpy(c+2,&mgr,4);
        static const BYTE e[12]={0x55,0x8B,0xEC,0x8B,0x45,0x08,0x83,0xEC,0x10,0x56,0x8B,0xF1};
        lab::rebuildOk=!memcmp(image+0x5964C0,a,8)&&!memcmp(image+0x597AF0,b,13)&&!memcmp(image+0x597B10,c,7)&&!memcmp(image+0x597940,e,12);
    }
    lab::sceneFrameOk=image[0x597AA0]==0x55 && CallSite(image,0x3F4C35,0x597AA0,reinterpret_cast<void*>(&SceneFrameHook));
    if(!lab::sceneFrameOk){Log("REFUS : mise a jour de la scene (0x3F4C35) : code different.");return 0;}
    if(!CallSite(image,0x3F6829,0x3F52B0,reinterpret_cast<void*>(&InputCopyHook),&g_prevCopy)){Log("REFUS : recopie des manettes (0x3F6829) : code different.");return 0;}
    if(!CallSite(image,0x3F4B1A,0x423690,reinterpret_cast<void*>(&FibersHook),&g_prevFibers)){Log("REFUS : fibres des manettes (0x3F4B1A) : code different.");return 0;}
    {
        const unsigned nImp=dm::PatchImports(image),nX87=dm::PatchX87(image);
        cp::Logf("Calculs deterministes prets : %u fonction(s) de d3dx9_43 et %u calcul(s) x87 (actifs seulement contre un adversaire avec le mod).",nImp,nX87);
    }
    sc::Install(image);
    Log(kb::Install(image)?"K.O. : bloqueur installe (coup mortel ramene a vie-1 dans les images predites).":"REFUS : bloqueur de K.O. (code different).");
    static const BYTE seBytes[6]={0x55,0x8B,0xEC,0x83,0xEC,0x0C};
    {
        BYTE* se=image+0x557C40;bool okSe=Detour(se,seBytes,6,&SeThunk,&g_resumeSe);
        if(!okSe && se[0]==0xE9){DWORD old=0,ig=0;
            if(VirtualProtect(se,5,PAGE_EXECUTE_READWRITE,&old)){
                g_chainSe=se+5+*reinterpret_cast<LONG*>(se+1);
                InterlockedExchange(reinterpret_cast<volatile LONG*>(se+1),static_cast<LONG>(reinterpret_cast<DWORD>(&SeThunk)-reinterpret_cast<DWORD>(se)-5));
                VirtualProtect(se,5,old,&ig);FlushInstructionCache(GetCurrentProcess(),se,5);okSe=true;}}
        Log(okSe?"Son : effets sonores des recalculs dedoublonnes.":"Son : REFUS de l accroche 0x557C40.");
    }
    {
        struct Z{DWORD idx,fn;void(*thunk)();};const Z zs[3]={{56,0x32A570,&ZoneThunk56},{145,0x326890,&ZoneThunk145},{147,0x32B490,&ZoneThunk147}};unsigned ok=0;
        for(unsigned i=0;i<3;++i){DWORD* slot=reinterpret_cast<DWORD*>(image+0xD0E048+zs[i].idx*4);DWORD old=0,ig=0;
            if(*slot==reinterpret_cast<DWORD>(image)+zs[i].fn && VirtualProtect(slot,4,PAGE_READWRITE,&old)){g_zoneOrig[i]=image+zs[i].fn;*slot=reinterpret_cast<DWORD>(zs[i].thunk);VirtualProtect(slot,4,old,&ig);++ok;}}
        cp::Logf("Zones : %u / 3 commandes de script de bascule de zone (n56, n145, n147) bloquees dans les images predites (rejouees une fois confirmees).",ok);
        static const BYTE zb[6]={0x55,0x8B,0xEC,0x8B,0x45,0x08};
        Log(Detour(image+0x597AF0,zb,6,&SetZoneThunk,&g_setZoneResume)?"Zones : bascules de zone notees (0x997AF0).":"Zones : REFUS du releve 0x597AF0.");
        {const bool e2=CallSite(image,0x5FF597,0x5FEFA0,reinterpret_cast<void*>(&FlowEtat2Hook)),e3=CallSite(image,0x603BA8,0x5FDF50,reinterpret_cast<void*>(&FlowEtat3Hook));
         Log(e2&&e3?"Flow haut : passages aux etats 2 et 3 traites comme des evenements de scene (0x9FF597, 0xA03BA8).":e2?"Flow haut : etat 2 traite (0x9FF597) ; REFUS de l'accroche 0xA03BA8.":"Flow haut : REFUS de l'accroche 0x9FF597.");}
        {BYTE pr[8]={0x55,0x8B,0xEC,0xA1};const DWORD t=reinterpret_cast<DWORD>(image)+0x20842BC;memcpy(pr+4,&t,4);
         Log(Detour(image+0x7F1690,pr,8,reinterpret_cast<void*>(&PileRenduRetrait),&g_pileResume)?"Rendu : retrait robuste de la pile des objets de rendu (0xBF1690).":"Rendu : REFUS du relais 0xBF1690 (octets differents).");}
        Log(CallSite(image,0x5FBEDD,0x5FB5E0,reinterpret_cast<void*>(&HomeBreakHook))?"Home (cour) : casses en attente verifiees (objet dans le tableau de la scene, 0x9FBEDD).":"Home (cour) : REFUS de l'accroche 0x9FBEDD.");
        static const BYTE sb[5]={0x55,0x8B,0xEC,0x6A,0xFF};
        Log(Detour(image+0x323960,sb,5,&SeqLaunchThunk,&g_seqResume)?"Sequences : lancements notes (0x723960).":"Sequences : REFUS du releve 0x323960.");
        const UINT testAot=kTest?GetPrivateProfileIntW(L"Rollback",L"TestVerrouAot",0,ini):0;
#ifndef DOA5RB_RELEASE
        g_testVerrouAot=testAot!=0;
#endif
        if(testAot==2){static const BYTE kb[5]={0x55,0x8B,0xEC,0x51,0x53};
            Log(Detour(image+0x3654A0,kb,5,&SceneSkipThunk,&g_skipResume)?"ESSAI AOT 2 : la scene de suite du Power Blow de TITAN n'est plus sautee (jouee jusqu'au bout avant le round suivant).":"ESSAI AOT 2 : REFUS du relais 0x7654A0 (octets differents).");}
        if(g_testVerrouAot || (kTest && GetPrivateProfileIntW(L"Rollback",L"SondeScenes",0,ini))){
            g_sceneMgrVar=reinterpret_cast<DWORD>(image+0xFCE5E8);BYTE xb[6]={0x8B,0x0D};memcpy(xb+2,&g_sceneMgrVar,4);
            Log(Detour(image+0x335870,xb,6,&SceneStopThunk,&g_sceneStopResume)?(g_testVerrouAot?"ESSAI AOT : verrou des commandes rendu si la scene de suite du Power Blow de TITAN est coupee (TestVerrouAot=1).":"SONDE SCENES : arret de la scene de suite 0x4F2 note avec sa pile (0x735870)."):"ESSAI AOT : REFUS du relais 0x735870 (octets differents).");}
        static const BYTE rq[9]={0x55,0x8B,0xEC,0x51,0xF3,0x0F,0x10,0x45,0x08};
        Log(Detour(image+0x366100,rq,9,&ReqThunk,&g_reqResume)?"Demandes : traitement des demandes de cinematique differe dans les images predites (Fuel).":"Demandes : REFUS de l accroche 0x366100.");
        static const BYTE rm[6]={0x80,0x7E,0x0C,0x00,0x74,0x04};BYTE* rmr=nullptr;g_rmKeep=image+0x3241B9;g_rmDel=image+0x3241BD;
        Log(Detour(image+0x3241B3,rm,6,&RemoveThunk,&rmr)?"Sequences : fin de script differee dans les images provisoires (0x7241B3, PredictionSequences).":"Sequences : REFUS de l accroche 0x3241B3.");}
    {   static const BYTE fb[5]={0x55,0x8B,0xEC,0x8B,0xC1};
        Log(Detour(image+0x7667C0,fb,5,&FreeThunk,&g_resumeFree)?"Tas : doubles liberations ignorees (allocateur 0xB667C0).":"Tas : REFUS de l accroche 0x7667C0.");}

    if(!CallSite(image,0x3F7E97,0x52ABC0,reinterpret_cast<void*>(&net::NetcodeHook))){Log("REFUS : appel du netcode (0x3F7E97) : code different.");return 0;}
    Log(CallSite(image,0x528594,0x5253B0,reinterpret_cast<void*>(&SpecRecvHook))?"Spectateurs : bascule de zone recue corrigee si le spectateur a deja change de zone.":"Spectateurs : REFUS de l'accroche 0x528594 (zone recue).");
    Log(CallSite(image,0x52612F,0x5252D0,reinterpret_cast<void*>(&SpecSceneHook))?"Spectateurs : zone du stage envoyee seulement sur image confirmee.":"Spectateurs : REFUS de l'accroche 0x52612F (zone du stage).");
    if(sf::on){
        if(!CallSite(image,0x30D4E6,0x526060,reinterpret_cast<void*>(&sf::WriterHook)))Log("Spectateurs : REFUS de l'accroche 0x30D4E6 (ecriture du flux des spectateurs) : flux du jeu garde.");
        else Log(CallSite(image,0x3F4D48,0x5260D0,reinterpret_cast<void*>(&sf::EmitHook))?"Spectateurs : flux envoye depuis les images confirmees, dans l'ordre (lab173b).":"Spectateurs : REFUS de l'accroche 0x3F4D48 (flux des spectateurs).");
        cp::Logf("Spectateurs : evenement camera d'un 1er calcul remis au recalcul de la meme image : %s (FluxCameraGardee, lab173d).",cam::garder?"oui":"non");
        cp::Logf("Spectateurs : synchro du stage de chaque image prise apres la scene du pas suivant : %s (FluxSynchroSuivante, lab174).",sf::synchroSuivante?"oui":"non");}
    if constexpr(kTest){
        const bool c1=CallSite(image,0x4A80D3,0x525F60,reinterpret_cast<void*>(&cam::SetHook)),c2=CallSite(image,0x35D843,0x4A7BD0,reinterpret_cast<void*>(&cam::ReqPB)),
                   c3=CallSite(image,0x356C93,0x4A7BD0,reinterpret_cast<void*>(&cam::ReqAutre)),c4=CallSite(image,0x5284C3,0x4A82B0,reinterpret_cast<void*>(&cam::ApplyHook));
        cp::Logf("CAMERA : suivi de l'evenement camera du flux (pose %d, demandes %d %d, spectateur %d).",c1,c2,c3,c4);}
    if(net::modeRetard<0)cp::LogR("Pret : rollback dans les salons (2 combattants avec le mod, spectateurs acceptes), retard AUTO, limite de rollback %lu.",net::avanceMax);
    else cp::LogR("Pret : rollback dans les salons (2 combattants avec le mod, spectateurs acceptes), retard %ld image(s), limite de rollback %lu.",static_cast<long>(net::modeRetard),net::avanceMax);
    rt::Install(image,ini);
    InstallCrashFilter(static_cast<HINSTANCE>(self));
    HANDLE t=CreateThread(nullptr,0,Keys,nullptr,0,nullptr); if(t) CloseHandle(t);
    return 0;
}

typedef void (__thiscall* SpecSceneFn)(BYTE*,void*);
static DWORD g_zoneEmise=0xFFFFFFFF;
static void __fastcall SpecSceneHook(BYTE* obj,void*,void* arg) {
    const SpecSceneFn orig=reinterpret_cast<SpecSceneFn>(g_base+0x5252D0);
    DWORD* d68=reinterpret_cast<DWORD*>(obj+0xD68);
    if(!net::active){orig(obj,arg);g_zoneEmise=*d68;return;}
    if(g_zoneEmise==0xFFFFFFFF)g_zoneEmise=*d68;
    const bool predite=static_cast<long>(lab::lastFrame)>static_cast<long>(net::remoteHave);
    if(predite){const DWORD zone=reinterpret_cast<DWORD(__cdecl*)()>(g_base+0x5964C0)();*d68=zone;orig(obj,arg);*d68=g_zoneEmise;return;}
    *d68=g_zoneEmise;orig(obj,arg);g_zoneEmise=*d68;
}

namespace sf {
static constexpr DWORD RING=128,RAFALE=12;
struct Rec{DWORD tag;DWORD zone;DWORD cine;BYTE area;bool alt;bool camOk;bool synchroOk;DWORD cam[5];BYTE rec[0x7C];};
static Rec ring[RING];
static bool started,prevOk; static DWORD lastSent,lastCap,prevCap,cineSent=0xFFFFFFFF;
static DWORD sSynchroSuiv,sSynchroAttente;
static DWORD sCap,sRecalc,sEmis,sManque,sAttente,sRafale,sRetard,sSaut,sEcrit,tLog; static unsigned cineLogs;
static void Capture() {
    if(!on || !net::active)return;
    BYTE* S=g_base+0xF8F208;
    if(*reinterpret_cast<const DWORD*>(S)!=1 || !S[0xCD4])return;
    const DWORD mg=Read(g_base+0xFCE790);if(!mg || Read(reinterpret_cast<void*>(mg+8))!=1)return;
    const DWORD x=Read(reinterpret_cast<void*>(mg+0x1C));
    const DWORD slot=*reinterpret_cast<const DWORD*>(S+0xCB0);if(slot>=24)return;
    if(prevOk && x==prevCap+1){Rec& p=ring[prevCap%RING];
        if(p.tag==prevCap && !p.synchroOk){memcpy(p.rec+0x5A,S+0xCF8,16);p.synchroOk=true;++sSynchroSuiv;}}
    Rec& e=ring[x%RING];
    memcpy(e.rec,S+0x110+slot*0x7C,0x7C);memcpy(e.rec+0x5A,S+0xCF8,16);e.synchroOk=!synchroSuivante;
    prevCap=x;prevOk=true;
    const auto etat=reinterpret_cast<bool(__cdecl*)(int)>(g_base+0x313140);
    e.alt=etat(0) || etat(1);
    if(e.alt)reinterpret_cast<void(__cdecl*)(BYTE*,size_t)>(g_base+0x33A520)(e.rec+0x6A,0x12);
    else{e.zone=reinterpret_cast<DWORD(__cdecl*)()>(g_base+0x5964C0)();e.area=g_base[0x2072821];}
    e.cine=Read(g_base+0xFCE5F8);
    if(e.tag==x)++sRecalc;
    if(e.tag!=x)e.camOk=false;
    e.tag=x;++sCap;
    if constexpr(kTest)d173::Voiture("joueur, image",x);
    if(!started){started=true;lastSent=x-1;lastCap=x;cineSent=0xFFFFFFFF;
        if constexpr(kTest)cp::Logf("FLUX SPECTATEUR : envoi des images confirmees a partir de l'image %lu (derniere image du combat vue par le rollback : %lu).",x,lab::lastFrame);}
    if(static_cast<long>(x-lastCap)>0)lastCap=x;
}

static DWORD sCamGarde,sCamPerdu; static unsigned camLignes;
static DWORD __fastcall WriterHook(BYTE* S) {
    DWORD* ev=reinterpret_cast<DWORD*>(S+0xD18);bool pose=ev[0]!=ev[1];DWORD cam[5]={ev[0],ev[1],ev[2],ev[3],ev[4]};DWORD x=0;bool remis=false;
    if(on && net::active && *reinterpret_cast<const DWORD*>(S)==1){const DWORD mg=Read(g_base+0xFCE790);
        if(mg && Read(reinterpret_cast<void*>(mg+8))==1){x=Read(reinterpret_cast<void*>(mg+0x1C));const Rec& p=ring[x%RING];
            if(!pose && p.tag==x && p.camOk){
                if(cam::garder){memcpy(ev,p.cam,sizeof p.cam);memcpy(cam,p.cam,sizeof cam);pose=true;remis=true;++sCamGarde;}
                else ++sCamPerdu;
                if constexpr(kTest){if(camLignes<300){++camLignes;cp::Logf("CAMERA (joueur) : image %lu recalculee SANS l'evenement camera de son 1er calcul (J%lu -> J%lu, %lu %lu %lu) : %s.",x,p.cam[0]+1,p.cam[1]+1,p.cam[2],p.cam[3],p.cam[4],cam::garder?"evenement remis (FluxCameraGardee=1)":"PERDU pour le spectateur");}}}
            else if constexpr(kTest){if(pose && camLignes<300){++camLignes;cp::Logf("CAMERA (joueur) : evenement ecrit dans l'image %lu du flux (J%lu -> J%lu, %lu %lu %lu)%s.",x,cam[0]+1,cam[1]+1,cam[2],cam[3],cam[4],p.tag==x?" (recalcul)":"");}}}}
    const DWORD r=reinterpret_cast<DWORD(__thiscall*)(BYTE*)>(g_base+0x526060)(S);
    if(r){++sEcrit;Capture();if constexpr(kTest){if(*reinterpret_cast<const DWORD*>(S)==1)d173::Trace(true);}
        if(x){Rec& e=ring[x%RING];if(e.tag==x){e.camOk=pose;memcpy(e.cam,cam,sizeof cam);}}}
    else if(remis)memset(ev,0,5*sizeof(DWORD));
    return r;
}
static void EmitOne(BYTE* S,const Rec& e,DWORD f) {
    BYTE* rec=S+0x110+*reinterpret_cast<const DWORD*>(S+0xCB0)*0x7C;
    memcpy(rec,e.rec,0x7C);
    if(!e.alt){
        DWORD* d68=reinterpret_cast<DWORD*>(S+0xD68);DWORD* d6c=reinterpret_cast<DWORD*>(S+0xD6C);
        if(*d68!=e.zone)*d6c^=1;
        BYTE& area=g_base[0x2072821];const BYTE a0=area;area=e.area;
        *d68=reinterpret_cast<DWORD(__cdecl*)()>(g_base+0x5964C0)();
        reinterpret_cast<SpecSceneFn>(g_base+0x5252D0)(S,rec+0x6A);
        *d68=e.zone;area=a0;g_zoneEmise=e.zone;
    }
    if constexpr(kTest){d173::Envoyee(f,e.cine,rec);if(e.camOk && camLignes<300){++camLignes;cp::Logf("CAMERA (joueur) : evenement envoye avec l'image %lu du flux.",f);}}
    reinterpret_cast<void(__thiscall*)(BYTE*)>(g_base+0x525230)(S);
}
static BYTE __fastcall EmitHook(BYTE* S) {
    const auto orig=reinterpret_cast<BYTE(__thiscall*)(BYTE*)>(g_base+0x5260D0);
    if(!started)return orig(S);
    if(!reinterpret_cast<bool(__thiscall*)(BYTE*)>(g_base+0x525D90)(S)){started=false;prevOk=false;return orig(S);}
    const bool fin=!net::active;
    BYTE natif[0x7C];const bool aNatif=fin && S[0xCD4]!=0;
    if(aNatif)memcpy(natif,S+0x110+*reinterpret_cast<const DWORD*>(S+0xCB0)*0x7C,0x7C);
    DWORD lim=lastCap;

    if(!fin && lab::prepared){DWORD c=lab::lastConfirmed;if(static_cast<long>(lab::lastFrame-c)<0)c=lab::lastFrame;
        const DWORD p=lab::ReplayPendingFrom();if(p && static_cast<long>(p-1-c)<0)c=p-1;
        if(synchroSuivante)--c;
        if(static_cast<long>(c-lim)<0)lim=c;}
    if(static_cast<long>(lim-lastSent)>static_cast<long>(RING-RAFALE)){++sSaut;lastSent=lim-RAFALE;}
    DWORD n=0;
    for(DWORD f=lastSent+1;static_cast<long>(lim-f)>=0 && n<(fin?2*RAFALE:RAFALE);++f){
        const Rec& e=ring[f%RING];
        if(e.tag==f && !e.synchroOk && !fin){++sSynchroAttente;break;}
        lastSent=f;
        if(e.tag!=f){++sManque;continue;}
        if constexpr(kTest){if(e.cine!=cineSent && cineLogs<300){++cineLogs;cp::Logf("FLUX SPECTATEUR : image %lu envoyee, cinematique %lX -> %lX (derniere image calculee %lu).",f,cineSent,e.cine,lastCap);}}
        cineSent=e.cine;EmitOne(S,e,f);++n;}
    S[0xCD4]=0;
    sEmis+=n;if(!n)++sAttente;if(n>sRafale)sRafale=n;{const DWORD r=lastCap-lastSent;if(static_cast<long>(r)>0 && r>sRetard)sRetard=r;}
    if constexpr(kTest){const DWORD now=GetTickCount();if(now-tLog>=5000 || fin){tLog=now;
        cp::Logf("FLUX SPECTATEUR 5 s : %lu ecriture(s) du jeu, %lu image(s) gardee(s) dont %lu recalculee(s), %lu envoyee(s), %lu manquante(s), %lu mise(s) a jour sans image, rafale max %lu, retard max %lu image(s)%s ; camera : %lu evenement(s) remis, %lu perdu(s) ; synchro : %lu prise(s) apres la scene du pas suivant, %lu attente(s).",
            sEcrit,sCap,sRecalc,sEmis,sManque,sAttente,sRafale,sRetard,sSaut?" ; RETARD TROP GRAND : images sautees":"",sCamGarde,sCamPerdu,sSynchroSuiv,sSynchroAttente);sCamGarde=sCamPerdu=sSynchroSuiv=sSynchroAttente=0;
        sEcrit=sCap=sRecalc=sEmis=sManque=sAttente=sRafale=sRetard=sSaut=0;}}
    if(fin){started=false;prevOk=false;
        if constexpr(kTest)cp::Logf("FLUX SPECTATEUR : fin de la phase en ligne : %lu image(s) videe(s) jusqu'a l'image %lu, flux du jeu repris%s.",n,lastSent,aNatif?" (image du jeu de cette mise a jour envoyee ensuite)":"");
        if(aNatif){memcpy(S+0x110+*reinterpret_cast<const DWORD*>(S+0xCB0)*0x7C,natif,0x7C);S[0xCD4]=1;return orig(S);}}
    return n?1:0;
}
}

typedef void (__thiscall* SpecRecvFn)(BYTE*,void*);
typedef DWORD (__cdecl* ZoneNowFn)();
typedef void (__cdecl* ZoneSetFn)(DWORD);
typedef void (__cdecl* ZoneEndFn)();
static DWORD g_zoneSpect=0xFFFFFFFF,g_bitSpect=0xFFFFFFFF; static unsigned g_specFix;

static DWORD g_specT,g_specN,g_specImg,g_specScene=0xFFFFFFFF; static float g_specPos[6]; static bool g_specPosOk; static unsigned g_specSauts,g_specScenes;
static void NomScene(char* b,size_t n,DWORD s){if(s==0xFFFFFFFF)strcpy_s(b,n,"aucune");else _snprintf_s(b,n,_TRUNCATE,"0x%lX",s);}
static DWORD g_specVt=0xFFFFFFFF; static unsigned g_specStages;
static void SpecReleve(DWORD zone) {
    if(net::active)return;
    ++g_specN;
    float p[6]={};Copy(p,g_base+net::RVA_POSITIONS,12);Copy(p+3,g_base+net::RVA_POSITIONS+0x180,12);
    const DWORD img=Read(g_base+net::RVA_NETCODE+8),scene=Read(g_base+0xFCE5F8);
    {const DWORD vt=lab::SceneVt();
     if(vt!=g_specVt){g_specVt=vt;
        if(g_specStages<400){++g_specStages;
            if(!vt)cp::Logf("Spectateur : plus de stage au pas du flux %lu.",g_specPas);
            else if(vt<EXPECTED_IMAGE_SIZE)cp::Logf("Spectateur : stage %s (table de methodes %06lX) au pas du flux %lu (zone %lu).",lab::NomZone(vt),vt,g_specPas,zone);
            else cp::Logf("Spectateur : stage du module de maps (table hors de l'exe) au pas du flux %lu (zone %lu).",g_specPas,zone);}}}
    if(scene!=g_specScene){
        if(g_specScenes<400){++g_specScenes;char a[16],b[16];NomScene(a,sizeof a,g_specScene);NomScene(b,sizeof b,scene);
            cp::Logf("Spectateur : scene %s -> %s au pas du flux %lu (zone %lu).",a,b,g_specPas,zone);}
        g_specScene=scene;}
    if(g_specPosOk)for(int j=0;j<2;++j){
        float d=0;for(int c=0;c<3;++c){const float e=p[3*j+c]-g_specPos[3*j+c];d+=e*e;}
        if(d>0.75f*0.75f && d==d && g_specSauts<400){++g_specSauts;
            cp::Logf("Spectateur : J%d saute de %.2f m au pas du flux %lu (%.2f %.2f %.2f -> %.2f %.2f %.2f), scene en cours %s.",j+1,sqrtf(d),g_specPas,
                g_specPos[3*j],g_specPos[3*j+1],g_specPos[3*j+2],p[3*j],p[3*j+1],p[3*j+2],scene==0xFFFFFFFF?"aucune":"oui");}}
    memcpy(g_specPos,p,sizeof p);g_specPosOk=true;g_specImg=img;
    if(g_specTrace){--g_specTrace;
        if(g_specTrace%10==0 && g_specTraceLignes<5000){++g_specTraceLignes;char b[16];NomScene(b,sizeof b,scene);
            cp::Logf("Spectateur TRANSITION pas %lu : zone %lu, scene %s, J1 %.2f %.2f %.2f, J2 %.2f %.2f %.2f.",g_specPas,zone,b,p[0],p[1],p[2],p[3],p[4],p[5]);}}
    const DWORD now=GetTickCount();
    if(!g_specT)g_specT=now;
    if(now-g_specT>=5000){char b[16];NomScene(b,sizeof b,scene);
        cp::Logf("Spectateur : %lu passage(s) du flux en %lu ms, image du jeu %lu, zone %lu, scene %s, J1 %.2f %.2f %.2f, J2 %.2f %.2f %.2f, pas du flux %lu.",g_specN,now-g_specT,img,zone,b,p[0],p[1],p[2],p[3],p[4],p[5],g_specPas);
        g_specT=now;g_specN=0;}
}

namespace d173 {
static constexpr unsigned kLignesFlux=16000;
static unsigned lignesRec,lignesEnv,lignesScr; static DWORD cineRec=0xFFFFFFFF,nRec,cineEnv=0xFFFFFFFF,nEnv;
static DWORD sC4=0xFFFFFFFF,sD0,sDC,s200=0xFFFFFFFF,sN;
static void Hex(char* o,size_t n,const BYTE* p,unsigned k){size_t m=0;o[0]=0;for(unsigned i=0;i<k && m+4<n;++i){const int w=_snprintf_s(o+m,n-m,_TRUNCATE,i?" %02X":"%02X",p[i]);if(w>0)m+=w;}}

static void ImageBrute(const char* quoi,DWORD num,DWORD cine,long rang,const BYTE* r){
    char h[400];Hex(h,sizeof h,r,0x7C);cp::Logf("FLUX %s %lu : cinematique %lX (%+ld) : %s.",quoi,num,cine,rang,h);}
static void Image(const char* quoi,DWORD num,DWORD cine,DWORD rang,const BYTE* rec){
    BYTE r[0x7C];if(!Copy(r,rec,0x7C))return;ImageBrute(quoi,num,cine,static_cast<long>(rang),r);}
struct Hist{BYTE r[20][0x7C];DWORD num[20];unsigned n;};
static Hist histE,histR;
static void Garder(Hist& h,DWORD num,const BYTE* rec){const unsigned i=h.n%20;if(Copy(h.r[i],rec,0x7C)){h.num[i]=num;++h.n;}}
static void Avant(Hist& h,const char* quoi,DWORD cine,unsigned& lignes){
    const unsigned k=h.n<20?h.n:20;for(unsigned j=0;j<k && lignes<kLignesFlux;++j){const unsigned i=(h.n-k+j)%20;++lignes;ImageBrute(quoi,h.num[i],cine,-static_cast<long>(k-j),h.r[i]);}}
static void Envoyee(DWORD f,DWORD cine,const BYTE* rec){
    if(cine!=cineEnv){if(cine!=0xFFFFFFFF && cineEnv==0xFFFFFFFF)Avant(histE,"ENVOYE image",cine,lignesEnv);cineEnv=cine;nEnv=0;}
    if(cine!=0xFFFFFFFF && nEnv<90 && lignesEnv<kLignesFlux){++nEnv;++lignesEnv;Image("ENVOYE image",f,cine,nEnv,rec);}
    Garder(histE,f,rec);}
static void Voiture(const char* qui,DWORD num){
    if(lignesScr>=800 || lab::SceneVt()!=0xBFC2E8)return;
    const DWORD mgr=Read(g_base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;if(!o)return;
    DWORD c4=0,d0=0,dc=0;BYTE f200=0;float t204=0,dt=0;
    if(!Copy(&c4,reinterpret_cast<const void*>(o+0x1C4),4) || !Copy(&d0,reinterpret_cast<const void*>(o+0x1D0),4) || !Copy(&dc,reinterpret_cast<const void*>(o+0x1DC),4) ||
       !Copy(&f200,reinterpret_cast<const void*>(o+0x200),1) || !Copy(&t204,reinterpret_cast<const void*>(o+0x204),4) || !Copy(&dt,reinterpret_cast<const void*>(o+0x1B8),4))return;
    ++sN;
    if(c4!=sC4 || d0!=sD0 || dc!=sDC || f200!=s200 || sN%60==0){sC4=c4;sD0=d0;sDC=dc;s200=f200;++lignesScr;
        cp::Logf("SCRAMBLE VOITURE (%s %lu) : etat %lu/%lu/%lu, fini %u, temps %.1f, dt %.3f, cinematique %lX.",qui,num,c4,d0,dc,f200,t204,dt,Read(g_base+0xFCE5F8));}}

static DWORD trN[2],trVt[2]={0xFFFFFFFF,0xFFFFFFFF},trCine[2]={0xFFFFFFFF,0xFFFFFFFF}; static float trDt[2]={-1,-1}; static unsigned trLignes;
static void Trace(bool emetteur){
    const int k=emetteur?0:1;const DWORD vt=lab::SceneVt();
    if(vt!=trVt[k]){trVt[k]=vt;trN[k]=0;trCine[k]=0xFFFFFFFF;trDt[k]=-1;}
    if(vt!=0xBFC2E8 || trLignes>=3000)return;
    const DWORD mgr=Read(g_base+0x2072580);const DWORD o=mgr?Read(reinterpret_cast<void*>(mgr+0xC)):0;if(!o)return;
    float t204=0,dt=0;BYTE f200=0;if(!Copy(&t204,reinterpret_cast<const void*>(o+0x204),4) || !Copy(&dt,reinterpret_cast<const void*>(o+0x1B8),4) || !Copy(&f200,reinterpret_cast<const void*>(o+0x200),1))return;
    ++trN[k];const DWORD cine=Read(g_base+0xFCE5F8);const DWORD mg=Read(g_base+0xFCE790);const DWORD img=mg?Read(reinterpret_cast<void*>(mg+0x1C)):0;
    if(trN[k]%10==1 || cine!=trCine[k] || dt!=trDt[k]){trCine[k]=cine;trDt[k]=dt;++trLignes;
        cp::Logf("SCRAMBLE TRACE (%s) image du flux %lu : temps %.2f, dt %.3f, fini %u, cinematique %lX, image du combat %lu, en ligne %d, a %lu.%03lu s.",
            emetteur?"joueur":"spectateur",trN[k],t204,dt,f200,cine,img,net::active?1:0,GetTickCount()/1000%100000,GetTickCount()%1000);}}
static void Recue(DWORD pas,const BYTE* rec){
    const DWORD cine=Read(g_base+0xFCE5F8);
    if(cine!=cineRec){if(cine!=0xFFFFFFFF && cineRec==0xFFFFFFFF)Avant(histR,"RECU pas",cine,lignesRec);cineRec=cine;nRec=0;}
    if(cine!=0xFFFFFFFF && nRec<90 && lignesRec<kLignesFlux){++nRec;++lignesRec;Image("RECU pas",pas,cine,nRec,rec);}
    Garder(histR,pas,rec);
    Voiture("spectateur, pas du flux",pas);Trace(false);}
}
namespace cam {
static void __fastcall SetHook(BYTE* S,void*,DWORD a,DWORD b,DWORD c,DWORD d,DWORD e){
    if(lignes<400){++lignes;cp::Logf("CAMERA (joueur) : evenement pose pendant l'image %ld (confirmee %ld%s) : J%lu -> J%lu, %lu %lu %lu.",
        sc::ctxFrame,sc::ctxConf,lab::resim?", RECALCUL":sc::ctxFrame>sc::ctxConf?", PREDITE":"",a+1,b+1,c,d,e);}
    reinterpret_cast<void(__thiscall*)(BYTE*,DWORD,DWORD,DWORD,DWORD,DWORD)>(g_base+0x525F60)(S,a,b,c,d,e);}
static void Req(const char* quoi,int a,int b,int c){
    if(lignes<400 && Read(g_base+0x1087A4C)==4){++lignes;cp::Logf("CAMERA (joueur) : demande %s pendant l'image %ld (confirmee %ld%s) : J%d -> J%d, %d.",
        quoi,sc::ctxFrame,sc::ctxConf,lab::resim?", RECALCUL":sc::ctxFrame>sc::ctxConf?", PREDITE":"",a+1,b+1,c);}
    reinterpret_cast<void(__cdecl*)(int,int,int)>(g_base+0x4A7BD0)(a,b,c);}
static void __cdecl ReqPB(int a,int b,int c){Req("Power Blow (0x75D7E0)",a,b,c);}
static void __cdecl ReqAutre(int a,int b,int c){Req("autre coup (0x756C50)",a,b,c);}
static void __cdecl ApplyHook(int a,int b,int c,DWORD d,int e){
    if(lignes<400){++lignes;cp::Logf("CAMERA (spectateur) : evenement rejoue au pas du flux %lu : J%d -> J%d, %d %lu %d, cinematique %lX.",g_specPas,a+1,b+1,c,d,e,Read(g_base+0xFCE5F8));}
    reinterpret_cast<void(__cdecl*)(int,int,int,DWORD,int)>(g_base+0x4A82B0)(a,b,c,d,e);}
}
static void __fastcall SpecRecvHook(BYTE* obj,void*,void* arg) {
    const SpecRecvFn orig=reinterpret_cast<SpecRecvFn>(g_base+0x5253B0);
    const ZoneNowFn zoneNow=reinterpret_cast<ZoneNowFn>(g_base+0x5964C0);
    DWORD* d6c=reinterpret_cast<DWORD*>(obj+0xD6C);
    ++g_specPas;g_specVu=GetTickCount();
    const DWORD bitAvant=*d6c,zoneAvant=zoneNow();
    if(g_bitSpect!=bitAvant || g_zoneSpect==0xFFFFFFFF){
        if constexpr(kTest){if(g_bitSpect!=0xFFFFFFFF && g_specZoneLignes<400){++g_specZoneLignes;
            cp::Logf("Spectateur : flux repris (bit de zone %lu -> %lu entre deux passages) au pas du flux %lu : zone notee %lu.",g_bitSpect&0xFFFF,bitAvant&0xFFFF,g_specPas,zoneAvant);}}
        g_zoneSpect=zoneAvant;}
    orig(obj,arg);
    const DWORD bitApres=*d6c;
    if(bitApres!=bitAvant){
        const DWORD zJeu=zoneNow(),zNotee=g_zoneSpect;const char* corr="";

        const DWORD cible=(g_zoneDepart<2 && bitApres<2)?(bitApres==0?g_zoneDepart:1-g_zoneDepart):0xFFFFFFFF;
        if(cible<2){
            if(zJeu!=cible){
                __try{reinterpret_cast<ZoneSetFn>(g_base+0x597AF0)(cible);reinterpret_cast<ZoneEndFn>(g_base+0x597B10)();}__except(EXCEPTION_EXECUTE_HANDLER){}
                corr=" (lab164 : zone de l'hote appliquee)";
                if(g_specFix<40){++g_specFix;cp::Logf("Spectateur : hote en zone %lu, zone %lu apres le jeu : zone %lu appliquee (depart %lu).",bitApres&0xFFFF,zJeu,cible,g_zoneDepart);}}}
        else if(zoneAvant!=g_zoneSpect && zoneAvant<2 && zJeu!=zoneAvant){
            __try{reinterpret_cast<ZoneSetFn>(g_base+0x597AF0)(zoneAvant);reinterpret_cast<ZoneEndFn>(g_base+0x597B10)();}__except(EXCEPTION_EXECUTE_HANDLER){}
            corr=" (correction lab146 : zone gardee)";
            if(g_specFix<40){++g_specFix;cp::Logf("Spectateur : bascule de zone recue alors que la zone avait deja change (%lu -> %lu) : zone %lu gardee.",g_zoneSpect,zoneAvant,zoneAvant);}}
        if constexpr(kTest){g_specTrace=300;if(g_specZoneLignes<400){++g_specZoneLignes;
            cp::Logf("Spectateur : bit de zone du flux %lu -> %lu au pas du flux %lu : zone avant %lu (au bit precedent %lu), apres le jeu %lu, depart %ld, finale %lu%s.",bitAvant&0xFFFF,bitApres&0xFFFF,g_specPas,zoneAvant,zNotee,zJeu,g_zoneDepart<2?static_cast<long>(g_zoneDepart):-1L,zoneNow(),corr);}}
        g_zoneSpect=zoneNow();
    }
    g_bitSpect=bitApres;
    if constexpr(kTest)SpecReleve(zoneNow());
    if constexpr(kTest){if(!net::active)d173::Recue(g_specPas,reinterpret_cast<const BYTE*>(arg)-0x6A);}
}

static LPTOP_LEVEL_EXCEPTION_FILTER g_prevFilter; static volatile LONG g_crashSeen; static BYTE* g_self; static DWORD g_selfSize;
static bool Where(DWORD v,char* out,size_t cap) {
    const DWORD b=reinterpret_cast<DWORD>(base),me=reinterpret_cast<DWORD>(g_self);
    if(b && v>=b+0x1000 && v<b+0x9A0000){_snprintf_s(out,cap,_TRUNCATE,"game+%06lX",v-b);return true;}
    if(me && v>=me && v<me+g_selfSize){_snprintf_s(out,cap,_TRUNCATE,"rb+%05lX",v-me);return true;}
    return false;
}
static bool AfterCall(DWORD v);

namespace guet {
    static int cur=-1; static bool vehOn;
    static DWORD Addr(LONG w){if(w==1 && rva2)return reinterpret_cast<DWORD>(g_base)+rva2;return absA?absA:reinterpret_cast<DWORD>(g_base)+rva;}
    struct Hit{DWORD eip,r[3];unsigned n;LONG f;DWORD v;bool rs;}; static Hit hits[2][64]; static unsigned nh[2]; static volatile LONG win=-1; static int curPass;
    static LONG CALLBACK Veh(EXCEPTION_POINTERS* e) {
        if(e->ExceptionRecord->ExceptionCode!=EXCEPTION_SINGLE_STEP)return EXCEPTION_CONTINUE_SEARCH;
        CONTEXT* c=e->ContextRecord;if(!(c->Dr6&1))return EXCEPTION_CONTINUE_SEARCH;
        c->Dr6=0;const LONG w=win;if(w<0 || w>1)return EXCEPTION_CONTINUE_EXECUTION;
        DWORD r[3]={};unsigned k=0;for(DWORD p=c->Esp;p<c->Esp+0x400 && k<3;p+=4){DWORD v=0;__try{v=*reinterpret_cast<const DWORD*>(p);}__except(EXCEPTION_EXECUTE_HANDLER){break;}if(AfterCall(v))r[k++]=v;}
        const LONG fr=sc::ctxFrame;DWORD val=0;__try{val=*reinterpret_cast<const DWORD*>(Addr(w));}__except(EXCEPTION_EXECUTE_HANDLER){}
        for(unsigned i=0;i<nh[w];++i)if(hits[w][i].eip==c->Eip && hits[w][i].r[0]==r[0] && hits[w][i].r[1]==r[1] && hits[w][i].f==fr && hits[w][i].rs==lab::resim){++hits[w][i].n;hits[w][i].v=val;return EXCEPTION_CONTINUE_EXECUTION;}
        if(nh[w]<64){Hit& h=hits[w][nh[w]++];h.eip=c->Eip;h.r[0]=r[0];h.r[1]=r[1];h.r[2]=r[2];h.n=1;h.f=fr;h.v=val;h.rs=lab::resim;}
        return EXCEPTION_CONTINUE_EXECUTION;}
    struct Req{DWORD tid;DWORD addr;bool on;};
    static DWORD WINAPI SetDr(LPVOID p) {
        const Req* q=static_cast<const Req*>(p);
        HANDLE t=OpenThread(THREAD_SUSPEND_RESUME|THREAD_GET_CONTEXT|THREAD_SET_CONTEXT,FALSE,q->tid);if(!t)return 0;
        if(SuspendThread(t)!=static_cast<DWORD>(-1)){CONTEXT c{};c.ContextFlags=CONTEXT_DEBUG_REGISTERS;
            if(GetThreadContext(t,&c)){if(q->on){c.Dr0=q->addr;c.Dr7=(c.Dr7&~0x000F0003u)|1u|(1u<<16)|(3u<<18);}else{c.Dr0=0;c.Dr7&=~0x000F0003u;}c.Dr6=0;SetThreadContext(t,&c);}
            ResumeThread(t);}
        CloseHandle(t);return 0;}
    static void Apply(bool on){Req q{GetCurrentThreadId(),Addr(cur),on};HANDLE h=CreateThread(nullptr,0,SetDr,&q,0,nullptr);if(h){WaitForSingleObject(h,2000);CloseHandle(h);}}
    static void Report(int w) {
        cp::Logf("GUET plage %d (images %lu-%lu, lecture %s) : %u ecriture(s) differente(s) de %08lX.",w+1,de[w],a[w],curPass==1?"REFERENCE":"ROLLBACK",nh[w],Addr(w));
        for(unsigned i=0;i<nh[w];++i){char e[32]="?",r0[32]="-",r1[32]="-",r2[32]="-";Where(hits[w][i].eip,e,sizeof e);
            if(hits[w][i].r[0])Where(hits[w][i].r[0],r0,sizeof r0);if(hits[w][i].r[1])Where(hits[w][i].r[1],r1,sizeof r1);if(hits[w][i].r[2])Where(hits[w][i].r[2],r2,sizeof r2);
            cp::Logf("GUET  image %ld%s : %s x%u -> %08lX (retours %s %s %s).",hits[w][i].f,hits[w][i].rs?" (recalcul)":"",e,hits[w][i].n,hits[w][i].v,r0,r1,r2);}}
    static void Tick() {
        if(lab::guetAbs && !rva && !absA){absA=lab::guetAbs;de[0]=lab::guetAbsDe;a[0]=lab::guetAbsA;}
        if((!rva && !absA) || !g_labo)return;
        int want=-1;
        if(((kTest && lab::pass==2) || (kTest && lab::pass==1)) && lab::prepared){const DWORD f=(kTest && lab::pass==1)?lab::lastFrame+1:lab::realFrame;for(int w=0;w<2;++w)if(a[w] && f>=de[w] && f<=a[w])want=w;}
        if(want==cur)return;
        if(cur>=0){InterlockedExchange(&win,-1);Apply(false);Report(cur);}
        cur=want;
        if(want>=0){if(!vehOn){AddVectoredExceptionHandler(1,&Veh);vehOn=true;}nh[want]=0;curPass=lab::pass;InterlockedExchange(&win,want);Apply(true);}
    }
}
static bool AfterCall(DWORD v) {
    BYTE c[6]={};if(!Copy(c,reinterpret_cast<const void*>(v-6),6))return false;
    return c[1]==0xE8 || (c[0]==0xFF && (c[1]&0x38)==0x10) || (c[3]==0xFF && (c[4]&0x38)==0x10) || (c[4]==0xFF && (c[5]&0x38)==0x10);
}
static LONG WINAPI CrashFilter(EXCEPTION_POINTERS* e) {
    if(e && e->ExceptionRecord && e->ContextRecord && !InterlockedExchange(&g_crashSeen,1)) {
        const EXCEPTION_RECORD* r=e->ExceptionRecord;char at[32]="autre module",l[400];
        Where(reinterpret_cast<DWORD>(r->ExceptionAddress),at,sizeof at);
        const bool av=r->ExceptionCode==EXCEPTION_ACCESS_VIOLATION;
        const bool petite=av && r->NumberParameters>=2 && r->ExceptionInformation[1]<0x10000;
        _snprintf_s(l,sizeof l,_TRUNCATE,"CRASH : %s%s a %s ; rollback %s, moteur %s, phase en ligne %s.",
            av?(r->NumberParameters>=1 && r->ExceptionInformation[0]?"violation d'acces en ecriture":"violation d'acces en lecture"):"exception",
            av?(petite?" (adresse quasi nulle)":" (adresse non nulle)"):"",at,
            net::modeCombat?"en mode combat":"inactif",lab::prepared?"prepare":"arrete",net::active?"active":"terminee");
        Log(l,true);
        const DWORD esp=e->ContextRecord->Esp,top=__readfsdword(4);size_t n=0;unsigned k=0;
        n=_snprintf_s(l,sizeof l,_TRUNCATE,"CRASH : pile :");
        for(DWORD a=esp;a+4<=top && a<esp+0x2000 && k<20;a+=4) {
            DWORD v=0;if(!Copy(&v,reinterpret_cast<const void*>(a),4))break;
            char w[32];if(!Where(v,w,sizeof w) || !AfterCall(v))continue;
            const int m=_snprintf_s(l+n,sizeof(l)-n,_TRUNCATE," %s",w);if(m>0)n+=m;++k;
        }
        Log(l,true);
    }
    return g_prevFilter?g_prevFilter(e):EXCEPTION_CONTINUE_SEARCH;
}

static volatile LONG g_dblFree,g_dblLogged;
static DWORD __cdecl FreeFilter(DWORD heap,DWORD p,DWORD esp) {
    if(!p)return 0;
    {const LONG n=lab::heapN<16?lab::heapN:16;bool k=false;for(LONG i=0;i<n;++i)if(lab::heapList[i]==heap){k=true;break;}
     if(!k && lab::heapN<16){const LONG i=InterlockedIncrement(&lab::heapN)-1;if(i<16)lab::heapList[i]=heap;}}
    bool dbl=false;DWORD sz=0;
    __try{
        if(!*reinterpret_cast<const DWORD*>(heap+0x10))return 0;
        const DWORD h=*reinterpret_cast<const DWORD*>(heap+0xC),hdr=p-h;sz=*reinterpret_cast<const DWORD*>(hdr+4);
        if(static_cast<LONG>(sz)>=0)dbl=true;
        else{const DWORD prev=*reinterpret_cast<const DWORD*>(hdr);if(prev){const LONG ps=*reinterpret_cast<const LONG*>(prev+4);if(prev+h+static_cast<DWORD>(ps<0?-ps:ps)!=hdr)dbl=true;}}
    }__except(EXCEPTION_EXECUTE_HANDLER){return 0;}
    if(!dbl)return 0;
    InterlockedIncrement(&g_dblFree);
    if(InterlockedIncrement(&g_dblLogged)<=30) {
        char l[400];size_t n=_snprintf_s(l,sizeof l,_TRUNCATE,"TAS : double liberation IGNOREE (taille %ld, image %lu, %s) ; pile :",static_cast<LONG>(sz),lab::realFrame,lab::resim?"recalcul":"normal");
        unsigned k=0;for(DWORD a=esp;a<esp+0x300 && k<10;a+=4){DWORD v=0;if(!Copy(&v,reinterpret_cast<const void*>(a),4))break;char w[32];if(!Where(v,w,sizeof w) || !AfterCall(v))continue;const int m=_snprintf_s(l+n,sizeof(l)-n,_TRUNCATE," %s",w);if(m>0)n+=m;++k;}
        Log(l);
    }
    return 1;
}
static __declspec(naked) void FreeThunk() {
    __asm {
        pushad
        lea  eax,[esp+32]
        push eax
        push dword ptr [esp+40]
        push ecx
        call FreeFilter
        add  esp,12
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  skip
        push ebp
        mov  ebp,esp
        mov  eax,ecx
        jmp  [g_resumeFree]
    skip:
        ret  4
    }
}
static unsigned g_seqLogs;

static volatile LONG g_seqBlocked;
static DWORD __cdecl SeqLaunchNote(DWORD mgr,DWORD script,DWORD id,DWORD esp) {
    if(*reinterpret_cast<const DWORD*>(g_base+0x1087A4C)!=4)return 0;
    const bool bloque=lab::prepared && mgr==*reinterpret_cast<const DWORD*>(g_base+0xFCE348) && lab::SeqGuardZone() && lab::Speculative();
    if(bloque){InterlockedExchange(&sc::blocked,1);InterlockedIncrement(&sc::nBlocked);InterlockedIncrement(&g_seqBlocked);}
    if(g_seqLogs>=150)return bloque?1:0;++g_seqLogs;
    bool refuse=false;__try{const DWORD head=*reinterpret_cast<const DWORD*>(mgr+0x10);DWORD n=*reinterpret_cast<const DWORD*>(head);unsigned k=0;
        while(n && n!=head && k<64){if(*reinterpret_cast<const DWORD*>(n+8)==id){refuse=*reinterpret_cast<const BYTE*>(n+0xC)!=0;break;}n=*reinterpret_cast<const DWORD*>(n);++k;}}__except(EXCEPTION_EXECUTE_HANDLER){}
    char l[600];size_t m=_snprintf_s(l,sizeof l,_TRUNCATE,"SEQUENCE : lancement de %lu (script %s) pendant l'image %ld (confirmee %ld)%s%s%s ; scene 0x%lX, verrou %lu ; pile :",id,script?"present":"nul",sc::ctxFrame,sc::ctxConf,
        bloque?" PROVISOIRE : BLOQUE":(sc::gate?" PREDITE":""),lab::resim?" RECALCUL":"",refuse?" : REFUSE (deja active)":"",
        *reinterpret_cast<const DWORD*>(g_base+0xFCE5F8),*reinterpret_cast<const DWORD*>(g_base+0xF9CB54));
    unsigned k=0;for(DWORD a=esp;a<esp+0x1000 && k<16;a+=4){DWORD v=0;if(!Copy(&v,reinterpret_cast<const void*>(a),4))break;char w[32];if(!Where(v,w,sizeof w) || !AfterCall(v))continue;const int q=_snprintf_s(l+m,sizeof(l)-m,_TRUNCATE," %s",w);if(q>0)m+=q;++k;}
    Log(l);
    return bloque?1:0;
}

static void ReleveGel() {
    const DWORD id=au::fightThread;if(!id || id==GetCurrentThreadId())return;
    HANDLE t=OpenThread(THREAD_SUSPEND_RESUME|THREAD_GET_CONTEXT,FALSE,id);if(!t)return;
    char l[400];size_t n=0;
    if(SuspendThread(t)!=static_cast<DWORD>(-1)) {
        CONTEXT c{};c.ContextFlags=CONTEXT_CONTROL;
        if(GetThreadContext(t,&c)) {
            char at[32]="autre module";Where(c.Eip,at,sizeof at);
            n=_snprintf_s(l,sizeof l,_TRUNCATE,"GEL : plus aucune mise a jour du jeu depuis 3 s pendant un round en rollback ; fil du combat a %s, pile :",at);
            unsigned k=0;
            for(DWORD a=c.Esp;a<c.Esp+0x2000 && k<20;a+=4){DWORD v=0;if(!Copy(&v,reinterpret_cast<const void*>(a),4))break;
                char w[32];if(!Where(v,w,sizeof w) || !AfterCall(v))continue;const int m=_snprintf_s(l+n,sizeof(l)-n,_TRUNCATE," %s",w);if(m>0)n+=m;++k;}
        }
        ResumeThread(t);
    }
    if(n)Log(l);

    if(g_labo) {
        char e[300];size_t en=_snprintf_s(e,sizeof e,_TRUNCATE,"GEL : echantillons :");
        for(int s2=0;s2<6;++s2){Sleep(30);if(SuspendThread(t)==static_cast<DWORD>(-1))break;CONTEXT c{};c.ContextFlags=CONTEXT_CONTROL;
            if(GetThreadContext(t,&c)){char w[32]="?";Where(c.Eip,w,sizeof w);const int m=_snprintf_s(e+en,sizeof(e)-en,_TRUNCATE," %s",w);if(m>0)en+=m;}ResumeThread(t);}
        Log(e);
        if(SuspendThread(t)!=static_cast<DWORD>(-1)) {
            CONTEXT c{};c.ContextFlags=CONTEXT_CONTROL|CONTEXT_INTEGER;
            if(GetThreadContext(t,&c)) {
                DWORD vals[260];unsigned nv=0;const DWORD regs[]={c.Eax,c.Ebx,c.Ecx,c.Edx,c.Esi,c.Edi,c.Ebp};for(DWORD r:regs)vals[nv++]=r;
                for(DWORD a=c.Esp;a<c.Esp+0x400 && nv<260;a+=4){DWORD v=0;if(!Copy(&v,reinterpret_cast<const void*>(a),4))break;vals[nv++]=v;}
                unsigned logs=0;
                for(unsigned i=0;i<nv && logs<24;++i){const DWORD v=vals[i];if(v<0x10000)continue;const char* nm=nullptr;DWORD off=0;
                    for(unsigned r=0;r<cp::count;++r){const DWORD a0=reinterpret_cast<DWORD>(cp::ranges[r].address);if(v>=a0 && v<a0+cp::ranges[r].size){nm=cp::ranges[r].name;off=v-a0;break;}}
                    if(!nm && lab::stageAddr && v>=lab::stageAddr && v<lab::stageAddr+lab::stageSize){nm="bloc_scene";off=v-lab::stageAddr;}
                    for(unsigned b=0;!nm && b<lab::exCount;++b)if(v>=lab::exAddr[b] && v<lab::exAddr[b]+lab::exSize[b]){nm="objet_decor_photo";off=v-lab::exAddr[b];}
                    if(!nm)continue;++logs;cp::Logf("GEL : %s %08lX dans la plage photographiee '%s' +%lX.",i<7?"registre":"pile",v,nm,off);}
                if(!logs)Log("GEL : aucun registre ni mot de pile ne pointe dans la photo.");
            }
            ResumeThread(t);
        }
    }
    CloseHandle(t);
}
static void InstallCrashFilter(HINSTANCE h) {
    g_self=reinterpret_cast<BYTE*>(h);
    auto nt=reinterpret_cast<IMAGE_NT_HEADERS32*>(g_self+reinterpret_cast<IMAGE_DOS_HEADER*>(g_self)->e_lfanew);
    g_selfSize=nt->OptionalHeader.SizeOfImage;
    g_prevFilter=SetUnhandledExceptionFilter(&CrashFilter);
}

struct DOA5RB_NetInfo { int taille; int phaseActive; int pingMs; int retardLocal; int modeRetard; int limiteRollback; };
extern "C" __declspec(dllexport) void __cdecl DOA5RB_SetDelay(int n){InterlockedExchange(&net::modeRetard,n<0?-1:(n>6?6:n));}
extern "C" __declspec(dllexport) int __cdecl DOA5RB_GetNetInfo(DOA5RB_NetInfo* o){
    if(!o || o->taille<static_cast<int>(sizeof(DOA5RB_NetInfo)))return 0;
    o->phaseActive=net::active?1:0;o->pingMs=static_cast<int>(net::rttLisse+0.5f);o->retardLocal=static_cast<int>(net::localDelay);
    o->modeRetard=static_cast<int>(net::modeRetard);o->limiteRollback=static_cast<int>(net::avanceMax);return 1;
}
BOOL WINAPI DllMain(HINSTANCE h,DWORD reason,LPVOID) {
    if(reason==DLL_PROCESS_ATTACH) {DisableThreadLibraryCalls(h); HANDLE t=CreateThread(nullptr,0,Worker,h,0,nullptr); if(t) CloseHandle(t);}
    else if(reason==DLL_PROCESS_DETACH && g_logOn)ViderJournal(20);
    return TRUE;
}
