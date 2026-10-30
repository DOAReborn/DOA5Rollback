namespace ind {
static volatile LONG on;

static int position=1,hautRef=62,taille=1;

static int texte=1; static bool anglais=true;

static int ping=1;
typedef HRESULT (WINAPI* Present_t)(IDirect3DDevice9*,const RECT*,const RECT*,HWND,const RGNDATA*);
typedef HRESULT (WINAPI* CreateDevice_t)(IDirect3D9*,UINT,D3DDEVTYPE,HWND,DWORD,D3DPRESENT_PARAMETERS*,IDirect3DDevice9**);
typedef IDirect3D9* (WINAPI* Create9_t)(UINT);
struct Accroche { void** vt; Present_t present; };
static Accroche accroches[4]; static volatile LONG nb;
static CreateDevice_t createOrig;

static bool labo;

static D3DCOLOR Couleur(){
    if(on && labo && net::EnCombatSalon())return D3DCOLOR_XRGB(0x30,0x60,0xF0);
    if(!on || !net::modeCombat || !net::EnCombatSalon())return 0;
    if(net::active){
        if(net::sDesyncs)return D3DCOLOR_XRGB(0xB0,0x40,0xF0);
        const bool muet=!net::advSur || GetTickCount()-net::dernierRecu>500;
        if(muet || net::verrouCourant)return D3DCOLOR_XRGB(0xF0,0x90,0x10);
        return D3DCOLOR_XRGB(0x20,0xD0,0x20);
    }
    return net::R32(net::RVA_PHASE)==2?D3DCOLOR_XRGB(0xE0,0x20,0x20):0;
}

static void Chiffre(IDirect3DDevice9* d,IDirect3DSurface9* s,int x,int y,int n,D3DCOLOR c,int k=1){
    static const BYTE seg[10]={0x3F,0x06,0x5B,0x4F,0x66,0x6D,0x7D,0x07,0x7F,0x6F};
    const int w=10*k,h=18*k,t=2*k,m=h/2;
    const RECT r[7]={{x,y,x+w,y+t},{x+w-t,y,x+w,y+m},{x+w-t,y+m,x+w,y+h},{x,y+h-t,x+w,y+h},{x,y+m,x+t,y+h},{x,y,x+t,y+m},{x,y+m-1,x+w,y+m+1}};
    for(int i=0;i<7;++i)if(seg[n%10]>>i&1)d->ColorFill(s,&r[i],c);
}

static const BYTE* Glyphe(char ch){
    static const BYTE F[7]={0x1F,0x10,0x10,0x1E,0x10,0x10,0x10},R[7]={0x1E,0x11,0x11,0x1E,0x14,0x12,0x11},A[7]={0x0E,0x11,0x11,0x1F,0x11,0x11,0x11},
        M[7]={0x11,0x1B,0x15,0x15,0x11,0x11,0x11},E[7]={0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F},S[7]={0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E},
        D[7]={0x1E,0x11,0x11,0x11,0x11,0x11,0x1E},Y[7]={0x11,0x11,0x0A,0x04,0x04,0x04,0x04},N[7]={0x11,0x19,0x15,0x13,0x11,0x11,0x11},
        C[7]={0x0E,0x11,0x10,0x10,0x10,0x11,0x0E},H[7]={0x11,0x11,0x11,0x1F,0x11,0x11,0x11},O[7]={0x0E,0x11,0x11,0x11,0x11,0x11,0x0E},
        L[7]={0x10,0x10,0x10,0x10,0x10,0x10,0x1F},B[7]={0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E},T[7]={0x1F,0x04,0x04,0x04,0x04,0x04,0x04},
        I[7]={0x0E,0x04,0x04,0x04,0x04,0x04,0x0E},G[7]={0x0E,0x11,0x10,0x17,0x11,0x11,0x0F};
    static const BYTE CH[10][7]={{0x0E,0x11,0x13,0x15,0x19,0x11,0x0E},{0x04,0x0C,0x04,0x04,0x04,0x04,0x0E},{0x0E,0x11,0x01,0x02,0x04,0x08,0x1F},
        {0x1E,0x01,0x01,0x0E,0x01,0x01,0x1E},{0x02,0x06,0x0A,0x12,0x1F,0x02,0x02},{0x1F,0x10,0x1E,0x01,0x01,0x11,0x0E},{0x06,0x08,0x10,0x1E,0x11,0x11,0x0E},
        {0x1F,0x01,0x02,0x04,0x08,0x08,0x08},{0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E},{0x0E,0x11,0x11,0x0F,0x01,0x02,0x0C}};
    if(ch>='0' && ch<='9')return CH[ch-'0'];
    switch(ch){case 'F':return F;case 'R':return R;case 'A':return A;case 'M':return M;case 'E':return E;case 'S':return S;case 'D':return D;
        case 'Y':return Y;case 'N':return N;case 'C':return C;case 'H':return H;case 'O':return O;
        case 'L':return L;case 'B':return B;case 'T':return T;case 'I':return I;case 'G':return G;default:return nullptr;}
}
static int LargeurTexte(const char* t,int k){const int n=static_cast<int>(strlen(t));return n?n*12*k-2*k:0;}
static void Texte(IDirect3DDevice9* d,IDirect3DSurface9* s,int x,int y,const char* t,D3DCOLOR c,int k){
    const int p=2*k;
    for(;*t;++t,x+=6*p){const BYTE* g=Glyphe(*t);if(!g)continue;
        for(int r=0;r<7;++r)for(int b=4;b>=0;){if(!(g[r]>>b&1)){--b;continue;}int e=b;while(e>=0 && (g[r]>>e&1))--e;
            const RECT q={x+(4-b)*p,y+r*p,x+(4-e)*p,y+r*p+p};d->ColorFill(s,&q,c);b=e;}}
}
static HRESULT WINAPI PresentHook(IDirect3DDevice9* d,const RECT* a,const RECT* b,HWND w,const RGNDATA* r){
    void** vt=*reinterpret_cast<void***>(d);Present_t orig=nullptr;
    for(LONG i=0;i<nb;++i)if(accroches[i].vt==vt)orig=accroches[i].present;
    if(rt::PresentSkip())return D3D_OK;
    const D3DCOLOR c=Couleur();
    if(c){IDirect3DSurface9* bb=nullptr;
        if(SUCCEEDED(d->GetBackBuffer(0,0,D3DBACKBUFFER_TYPE_MONO,&bb)) && bb){
            const int k=taille;const DWORD rt=net::retardActuel>99?99:net::retardActuel;
            const bool desync=!labo && texte && net::active && net::sDesyncs;
            const int nd=(!labo && net::active && !desync)?(rt>=10?2:1):0;
            const char* mot=labo?"LAB":!texte || !net::active?"":desync?(anglais?"DESYNC":"DESYNCHRO"):net::reglagesDiff?(anglais?"SETTINGS":"REGLAGES"):(rt==1?"FRAME":"FRAMES");
            char pg[16]="";if(ping && net::active && net::advSur && net::rttLisse>0.5f){const int ms=static_cast<int>(net::rttLisse+0.5f);_snprintf_s(pg,sizeof pg,_TRUNCATE,"%d MS",ms>999?999:ms);}
            const int lc=nd?nd*14*k-4*k:0,lm=LargeurTexte(mot,k),lp=LargeurTexte(pg,k);
            int x0=8,y0=8;D3DSURFACE_DESC sd{};
            if(position==1 && SUCCEEDED(bb->GetDesc(&sd)) && sd.Width>=320 && sd.Height>=240){
                const int large=16*k+(lc?6*k+lc:0)+(lm?(lc?10*k:6*k)+lm:0)+(lp?16*k+lp:0);x0=static_cast<int>(sd.Width)/2-large/2;y0=static_cast<int>(sd.Height)*hautRef/1080;}
            const RECT q={x0,y0,x0+16*k,y0+16*k};d->ColorFill(bb,&q,c);
            const D3DCOLOR blanc=D3DCOLOR_XRGB(0xFF,0xFF,0xFF);int xc=x0+22*k;
            if(nd){const int yc=y0-k;
                if(nd==2){Chiffre(d,bb,xc,yc,static_cast<int>(rt/10),blanc,k);Chiffre(d,bb,xc+14*k,yc,static_cast<int>(rt%10),blanc,k);}
                else Chiffre(d,bb,xc,yc,static_cast<int>(rt),blanc,k);
                xc+=lc+10*k;}
            if(lm){Texte(d,bb,xc,y0+k,mot,blanc,k);xc+=lm;}
            if(lp)Texte(d,bb,xc+16*k,y0+k,pg,D3DCOLOR_XRGB(0xB8,0xB8,0xB8),k);
            bb->Release();}}
    rt::PresentDraw(d);
    return orig?orig(d,a,b,w,r):D3D_OK;
}
static void AccrocherDevice(IDirect3DDevice9* dev){
    void** vt=*reinterpret_cast<void***>(dev);DWORD old;
    for(LONG i=0;i<nb;++i)if(accroches[i].vt==vt)return;
    if(nb>=4 || vt[17]==reinterpret_cast<void*>(&PresentHook))return;
    if(!VirtualProtect(&vt[17],4,PAGE_EXECUTE_READWRITE,&old))return;
    accroches[nb].vt=vt;accroches[nb].present=reinterpret_cast<Present_t>(vt[17]);InterlockedIncrement(&nb);
    vt[17]=reinterpret_cast<void*>(&PresentHook);VirtualProtect(&vt[17],4,old,&old);
    Log("Indicateur : affichage accroche.");
}
static HRESULT WINAPI CreateDeviceHook(IDirect3D9* d3d,UINT a,D3DDEVTYPE t,HWND w,DWORD f,D3DPRESENT_PARAMETERS* pp,IDirect3DDevice9** out){
    const HRESULT hr=createOrig(d3d,a,t,w,f,pp,out);
    if(SUCCEEDED(hr) && out && *out && t==D3DDEVTYPE_HAL)AccrocherDevice(*out);
    return hr;
}
static void Installer(){
    HMODULE m=LoadLibraryA("d3d9.dll");Create9_t c=m?reinterpret_cast<Create9_t>(GetProcAddress(m,"Direct3DCreate9")):nullptr;
    IDirect3D9* d3d=c?c(D3D_SDK_VERSION):nullptr;if(!d3d){Log("Indicateur : REFUS (d3d9 introuvable).");return;}
    void** vt=*reinterpret_cast<void***>(d3d);DWORD old;
    if(vt[16]!=reinterpret_cast<void*>(&CreateDeviceHook) && VirtualProtect(&vt[16],4,PAGE_EXECUTE_READWRITE,&old)){
        createOrig=reinterpret_cast<CreateDevice_t>(vt[16]);vt[16]=reinterpret_cast<void*>(&CreateDeviceHook);VirtualProtect(&vt[16],4,old,&old);}
    d3d->Release();
}
}
