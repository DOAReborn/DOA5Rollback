#include <objbase.h>
#include <mmsystem.h>
#include <mmreg.h>
#pragma comment(lib,"ole32.lib")
namespace au {
using cp::Logf;
static const GUID CLSID_XAudio2_7={0x5a508685,0xa254,0x4fba,{0x9b,0x82,0x9a,0x24,0xb0,0x03,0x06,0xaf}};
static const GUID IID_IXAudio2_7={0x8bcf1f58,0x9fe7,0x4583,{0x8a,0xc6,0xe2,0xad,0xc4,0x65,0xc8,0xbb}};
typedef HRESULT(__stdcall* StartFn)(void* voice,UINT32 flags,UINT32 operationSet);
typedef HRESULT(__stdcall* SubmitFn)(void* voice,const void* buffer,const void* wma);
static StartFn origStart; static SubmitFn origSubmit;
static volatile LONG mute;
static volatile DWORD fightThread;
static volatile LONG nStart,nSubmit,nSubmitResim,nSubmitOther,nMuted,logged;
static void Stack(char* out,size_t cap) {
    void* frames[24];const USHORT got=RtlCaptureStackBackTrace(1,24,frames,nullptr);
    size_t len=0;out[0]=0;unsigned n=0;
    for(USHORT i=0;i<got && n<14;++i){const DWORD v=reinterpret_cast<DWORD>(frames[i]);
        if(v<reinterpret_cast<DWORD>(base) || v>=reinterpret_cast<DWORD>(base)+0x966000)continue;
        const int w=_snprintf_s(out+len,cap-len,_TRUNCATE,"%s%06lX",n?",":"",v-reinterpret_cast<DWORD>(base));if(w<=0)break;len+=w;++n;}
}
static bool InFight(){return Read(base+0x1087A4C)==4;}
static void Note(const char* what,void* voice) {
    if(!InFight() || logged>=40)return;
    InterlockedIncrement(&logged);
    const bool onFight=GetCurrentThreadId()==fightThread;
    char stack[200];Stack(stack,sizeof(stack));
    Logf("SON %s voix %08lX : fil %lu%s, %s ; pile %s",what,reinterpret_cast<DWORD>(voice),GetCurrentThreadId(),onFight?" (combat)":" (autre fil)",
        !onFight?"-":lab::resim?"PENDANT UN RECALCUL":"image normale",stack);
}
static HRESULT __stdcall StartHook(void* voice,UINT32 flags,UINT32 op) {
    InterlockedIncrement(&nStart);Note("Start",voice);
    return origStart(voice,flags,op);
}
static HRESULT __stdcall SubmitHook(void* voice,const void* buffer,const void* wma) {
    InterlockedIncrement(&nSubmit);
    const bool onFight=GetCurrentThreadId()==fightThread;
    if(!onFight)InterlockedIncrement(&nSubmitOther);
    else if(lab::resim) {
        InterlockedIncrement(&nSubmitResim);
        if(mute){InterlockedIncrement(&nMuted);return S_OK;}
    }
    Note("Submit",voice);
    return origSubmit(voice,buffer,wma);
}
static bool Patch(void** vt,unsigned index,void* hook,void** orig) {
    DWORD old=0,ig=0;if(!VirtualProtect(&vt[index],4,PAGE_READWRITE,&old))return false;
    *orig=vt[index];vt[index]=hook;VirtualProtect(&vt[index],4,old,&ig);return true;
}

static bool Install() {
    if(FAILED(CoInitializeEx(nullptr,COINIT_MULTITHREADED)))return false;
    void* xa=nullptr;bool ok=false;
    if(SUCCEEDED(CoCreateInstance(CLSID_XAudio2_7,nullptr,CLSCTX_INPROC_SERVER,IID_IXAudio2_7,&xa)) && xa) {
        void** vx=*static_cast<void***>(xa);
        typedef HRESULT(__stdcall* InitFn)(void*,UINT32,UINT32);
        typedef HRESULT(__stdcall* MasterFn)(void*,void**,UINT32,UINT32,UINT32,UINT32,const void*);
        typedef HRESULT(__stdcall* SourceFn)(void*,void**,const WAVEFORMATEX*,UINT32,float,void*,const void*,const void*);
        typedef ULONG(__stdcall* ReleaseFn)(void*);
        typedef void(__stdcall* DestroyFn)(void*);
        void *master=nullptr,*voice=nullptr;
        if(SUCCEEDED(reinterpret_cast<InitFn>(vx[5])(xa,0,1)) &&
           SUCCEEDED(reinterpret_cast<MasterFn>(vx[10])(xa,&master,2,44100,0,0,nullptr)) && master) {
            WAVEFORMATEX wf={};wf.wFormatTag=WAVE_FORMAT_PCM;wf.nChannels=1;wf.nSamplesPerSec=44100;wf.wBitsPerSample=16;wf.nBlockAlign=2;wf.nAvgBytesPerSec=88200;
            if(SUCCEEDED(reinterpret_cast<SourceFn>(vx[8])(xa,&voice,&wf,0,2.0f,nullptr,nullptr,nullptr)) && voice) {
                void** vt=*static_cast<void***>(voice);
                ok=Patch(vt,19,reinterpret_cast<void*>(&StartHook),reinterpret_cast<void**>(&origStart)) &&
                   Patch(vt,21,reinterpret_cast<void*>(&SubmitHook),reinterpret_cast<void**>(&origSubmit));
                reinterpret_cast<DestroyFn>((*static_cast<void***>(voice))[18])(voice);
            }
            reinterpret_cast<DestroyFn>((*static_cast<void***>(master))[18])(master);
        }
        reinterpret_cast<ReleaseFn>(vx[2])(xa);
    }
    CoUninitialize();
    return ok;
}

typedef BOOL(WINAPI* SetEventFn)(HANDLE);
static SetEventFn origSetEvent;
static DWORD eventStacks[48]; static unsigned eventStackCount;
static volatile LONG nEvent,nEventResim;
static BOOL WINAPI SetEventHook(HANDLE h) {
    if(GetCurrentThreadId()==fightThread && InFight()) {
        InterlockedIncrement(&nEvent);if(lab::resim)InterlockedIncrement(&nEventResim);
        char stack[200];Stack(stack,sizeof(stack));
        DWORD hs=0;for(const char* c=stack;*c;++c)hs=hs*31+static_cast<BYTE>(*c);
        bool seen=false;for(unsigned i=0;i<eventStackCount;++i)if(eventStacks[i]==hs){seen=true;break;}
        if(!seen && eventStackCount<8){eventStacks[eventStackCount++]=hs;
            Logf("SON SetEvent depuis le fil du combat (%s) : pile %s",lab::resim?"PENDANT UN RECALCUL":"image normale",stack);}
    }
    return origSetEvent(h);
}
static bool HookSetEvent() {
    void** slot=reinterpret_cast<void**>(base+0x966114);
    void* k=reinterpret_cast<void*>(GetProcAddress(GetModuleHandleA("kernel32.dll"),"SetEvent"));
    HMODULE kb=GetModuleHandleA("kernelbase.dll");void* k2=kb?reinterpret_cast<void*>(GetProcAddress(kb,"SetEvent")):nullptr;
    if(*slot!=k && *slot!=k2)return false;
    DWORD old=0,ig=0;if(!VirtualProtect(slot,4,PAGE_READWRITE,&old))return false;
    origSetEvent=reinterpret_cast<SetEventFn>(*slot);*slot=reinterpret_cast<void*>(&SetEventHook);VirtualProtect(slot,4,old,&ig);return true;
}

static volatile LONG dedupe=1;
struct SeRecord { DWORD frame; unsigned n; DWORD id[16],ret[16]; };
static SeRecord seRec[128];
static volatile LONG nSe,nSeResim,nSeDropped,nSeNewResim;

struct SeDrop { DWORD frame,id,ret; bool flow; };
static SeDrop seDrops[64]; static unsigned seDropN,seDropLogs; static DWORD seCallers[64][2]; static unsigned seCallerN;
static void NoterDrop(DWORD j,DWORD id,DWORD ret){
    bool vu=false,nouveau=false;for(unsigned i=0;i<seCallerN;++i)if(seCallers[i][0]==id && seCallers[i][1]==ret){vu=true;break;}
    if(!vu && seCallerN<64){seCallers[seCallerN][0]=id;seCallers[seCallerN][1]=ret;++seCallerN;nouveau=true;}
    const bool flow=lab::flowSuiviA && j>=lab::flowSuiviDe && j<=lab::flowSuiviA;
    if((nouveau || flow) && seDropN<64)seDrops[seDropN++]={j,id,ret,flow};
}
static DWORD __cdecl SeFilter(DWORD id,DWORD ret) {
    if(GetCurrentThreadId()!=fightThread || (lab::pass!=2 && lab::pass!=3) || !lab::prepared)return 0;
    InterlockedIncrement(&nSe);
    const DWORD j=lab::nextFrame;SeRecord& r=seRec[j%128];
    if(r.frame!=j){r.frame=j;r.n=0;}
    bool known=false;for(unsigned i=0;i<r.n;++i)if(r.id[i]==id && r.ret[i]==ret){known=true;break;}
    if(lab::resim) {
        InterlockedIncrement(&nSeResim);

        static DWORD lastId,lastRet,repeat;
        if(id==lastId && ret==lastRet)++repeat;else{lastId=id;lastRet=ret;repeat=0;}
        if(known && dedupe && ret!=reinterpret_cast<DWORD>(base)+0x63C84C && repeat<8){InterlockedIncrement(&nSeDropped);if constexpr(kTest)NoterDrop(j,id,ret);else (void)&NoterDrop;return 1;}
        if(!known)InterlockedIncrement(&nSeNewResim);
    }
    if(!known && r.n<16){r.id[r.n]=id;r.ret[r.n]=ret;++r.n;}
    return 0;
}
static DWORD lastReport;
static void Report() {
    if constexpr(kTest){for(unsigned i=0;i<seDropN && seDropLogs<3000;++i){const SeDrop& d=seDrops[i];++seDropLogs;
        Logf("SON : effet %04lX.%04lX demande par game+%06lX ignore au recalcul de l'image %lu (deja joue au 1er calcul : l'appelant recoit -1)%s.",
            d.id>>16,d.id&0xFFFF,d.ret-reinterpret_cast<DWORD>(base),d.frame,d.flow?" [FLOW SUIVI]":" [1re fois pour cet appelant]");}
        seDropN=0;}
    const DWORD now=GetTickCount();if(now-lastReport<30000)return;lastReport=now;
    const LONG s=InterlockedExchange(&nSubmit,0),r=InterlockedExchange(&nSubmitResim,0),o=InterlockedExchange(&nSubmitOther,0),m=InterlockedExchange(&nMuted,0),st=InterlockedExchange(&nStart,0);
    const LONG se=InterlockedExchange(&nSe,0),ser=InterlockedExchange(&nSeResim,0),sed=InterlockedExchange(&nSeDropped,0),sen=InterlockedExchange(&nSeNewResim,0);
    if(se)Logf("SON bilan 30 s : %ld demandes d'effets sonores (0x557C40), dont %ld pendant un recalcul : %ld ignorees (deja jouees), %ld nouvelles ; dedoublonnage %s.",se,ser,sed,sen,dedupe?"ACTIF":"inactif");
    const LONG e=InterlockedExchange(&nEvent,0),er=InterlockedExchange(&nEventResim,0);
    if(e)Logf("SON bilan 30 s : %ld SetEvent depuis le fil du combat, dont %ld pendant un recalcul.",e,er);
    if(s||st)Logf("SON bilan 30 s : %ld Start, %ld SubmitSourceBuffer dont %ld sur un autre fil que le combat et %ld pendant un recalcul (%ld bloques, sourdine %s).",
        st,s,o,r,m,mute?"ACTIVE":"inactive");
}
}
static BYTE* g_resumeSe=nullptr;
static BYTE* g_chainSe=nullptr;
static __declspec(naked) void SeThunk() {
    __asm {
        mov  eax,[esp+4]
        mov  ecx,[esp]
        pushad
        push ecx
        push eax
        call au::SeFilter
        add  esp,8
        mov  [esp+28],eax
        popad
        test eax,eax
        jnz  drop
        cmp  g_chainSe,0
        jne  chain
        push ebp
        mov  ebp,esp
        sub  esp,0xC
        jmp  [g_resumeSe]
    chain:
        jmp  [g_chainSe]
    drop:
        or   eax,-1
        ret
    }
}
