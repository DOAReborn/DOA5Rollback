#pragma once
#pragma comment(lib,"gdi32.lib")
namespace ui {

static BYTE* B=nullptr;
static void LogF(const char* f,...) {char l[256];va_list a;va_start(a,f);vsnprintf(l,sizeof l,f,a);va_end(a);Log(l);}

static bool g_bar=true;
static bool g_hint=false;
static bool g_box=true;

static BYTE* volatile g_hud=nullptr; static volatile DWORD g_hudTick=0;
static void* g_hudUpdate=nullptr;
static bool ReplayHudShown() {
    BYTE* h=g_hud;
    if(!h||GetTickCount()-g_hudTick>300) return false;
    const DWORD screen=Read(B+0xF8A7AC);
    if(screen==0xFFFFFFFF||screen==0xB) return false;
    return Read(h+0x12C0)==0;
}
static int  g_pad=0;

static WCHAR g_name[2][64]; static BYTE g_char[2]={0xFF,0xFF}; static bool g_dataOk=false;
static void ReadReplayData() {
    g_dataOk=false;
    BYTE* buf=reinterpret_cast<BYTE*>(Read(B+0xFCE790)); buf=buf?reinterpret_cast<BYTE*>(Read(buf)):nullptr;
    if(!buf||Read(buf)!=0x52504249) return;
    for(int p=0;p<2;++p) {
        BYTE c=0xFF; Copy(&c,buf+(p?0x6E:0x4E),1); g_char[p]=c;
        lstrcpynW(g_name[p],p?L"P2":L"P1",64);
    }
    g_dataOk=true;
}

constexpr int FW=93,FH=54;
static DWORD g_face[2][FW*FH]; static volatile LONG g_faceOk[2]={0,0};
static volatile LONG g_groupAsked=0,g_wantFaces=0,g_facesDone=0;
static IDirect3DTexture9* TextureAt(DWORD obj,UINT w,UINT h,D3DFORMAT fmt) {
    MEMORY_BASIC_INFORMATION mi; DWORD vt=Read(reinterpret_cast<void*>(obj));
    if(obj<0x10000||!vt||!VirtualQuery(reinterpret_cast<void*>(vt),&mi,sizeof mi)||mi.Type!=MEM_IMAGE) return nullptr;
    IDirect3DTexture9* t=reinterpret_cast<IDirect3DTexture9*>(obj); D3DSURFACE_DESC d;
    if(FAILED(t->GetLevelDesc(0,&d))||d.Width!=w||(h&&d.Height!=h)||d.Format!=fmt) return nullptr;
    return t;
}
static bool CapturePicture(DWORD id,int w,int h,DWORD* out) {
    if(id==0xFFFFFFFF) return false;
    const DWORD rec=reinterpret_cast<DWORD(__cdecl*)(DWORD)>(B+0x7CF680)(id);
    if(!rec) return false;
    const DWORD texi=Read(reinterpret_cast<void*>(rec+0x14)),group=id>>16;
    if(group>=Read(B+0x20825D4)) return false;
    const DWORD entry=Read(B+0x20825D8)+group*0x28,blk=Read(reinterpret_cast<void*>(entry+0xC));
    DWORD tb=blk?Read(reinterpret_cast<void*>(blk+0x20)):0; if(tb) tb+=blk;
    DWORD ti=tb?Read(reinterpret_cast<void*>(tb+4)):0; if(ti) ti+=blk;
    char tag[8];
    if(!ti||!Copy(tag,reinterpret_cast<void*>(ti),8)||memcmp(tag,"texinfo",8)||texi>=Read(reinterpret_cast<void*>(ti+0x10))) return false;
    const DWORD e=ti+0x20+texi*12; float v=0; Copy(&v,reinterpret_cast<void*>(e+8),4);
    IDirect3DTexture9* img=TextureAt(Read(reinterpret_cast<void*>(Read(reinterpret_cast<void*>(Read(reinterpret_cast<void*>(e)))))),w,h,D3DFMT_L8);
    IDirect3DTexture9* pal=TextureAt(Read(reinterpret_cast<void*>(Read(reinterpret_cast<void*>(Read(reinterpret_cast<void*>(e+4)))))),256,0,D3DFMT_A8R8G8B8);
    D3DSURFACE_DESC pd; int rows=8;
    if(pal&&SUCCEEDED(pal->GetLevelDesc(0,&pd))) rows=static_cast<int>(pd.Height);
    const int row=static_cast<int>(v*rows);
    if(!img||!pal||row<0||row>=rows) return false;
    DWORD palette[256]; D3DLOCKED_RECT lr; RECT rr={0,row,256,row+1};
    if(FAILED(pal->LockRect(0,&lr,&rr,D3DLOCK_READONLY))) return false;
    memcpy(palette,lr.pBits,sizeof palette); pal->UnlockRect(0);
    if(FAILED(img->LockRect(0,&lr,nullptr,D3DLOCK_READONLY))) return false;
    for(int y=0;y<h;++y){const BYTE* s=static_cast<const BYTE*>(lr.pBits)+y*lr.Pitch; for(int x=0;x<w;++x) out[y*w+x]=palette[s[x]];}
    img->UnlockRect(0);
    return true;
}
static bool GroupLoaded(DWORD g) { return reinterpret_cast<char(__cdecl*)(DWORD)>(B+0x7D5A00)(g)!=0; }

static void LogicFrame() {
    if(g_wantFaces&&g_groupAsked==0) {
        if(GroupLoaded(0x1D4)) InterlockedExchange(&g_groupAsked,2);
        else {reinterpret_cast<char(__cdecl*)(DWORD,DWORD,DWORD)>(B+0x7D59A0)(0x1D4,0,0); InterlockedExchange(&g_groupAsked,1);}
    }
    if(g_groupAsked==1&&(g_facesDone||!g_wantFaces)) {
        reinterpret_cast<void(__cdecl*)(DWORD)>(B+0x7D5A70)(0x1D4); InterlockedExchange(&g_groupAsked,3);
    }
}

static void RenderFaces() {
    if(!g_wantFaces||g_facesDone||(g_groupAsked!=1&&g_groupAsked!=2)||!GroupLoaded(0x1D4)) return;
    for(int p=0;p<2;++p) {
        const BYTE c=g_char[p];
        const DWORD id=c<=0x30?reinterpret_cast<DWORD(__cdecl*)(DWORD)>(B+0x256B90)(c):0xFFFFFFFF;
        InterlockedExchange(&g_faceOk[p],CapturePicture(id,FW,FH,g_face[p])?1:0);
    }
    InterlockedExchange(&g_facesDone,1);
    LogF("Visages : P1 %s, P2 %s.",g_faceOk[0]?"oui":"non",g_faceOk[1]?"oui":"non");
}
static void SelectorOpened() {
    ReadReplayData();
    if(g_groupAsked==1) return;
    InterlockedExchange(&g_faceOk[0],0); InterlockedExchange(&g_faceOk[1],0);
    InterlockedExchange(&g_facesDone,0); InterlockedExchange(&g_groupAsked,0);
    InterlockedExchange(&g_wantFaces,1);
}
static void SelectorClosed() { InterlockedExchange(&g_wantFaces,0); }

static HDC g_dc=nullptr; static HBITMAP g_bmp=nullptr; static DWORD* g_bits=nullptr; static int g_bw=0,g_bh=0;
static IDirect3DTexture9* g_tex=nullptr; static int g_tw=0,g_th=0; static IDirect3DDevice9* g_texDev=nullptr;
static HFONT g_fTitle=nullptr,g_fItem=nullptr,g_fText=nullptr,g_fSmall=nullptr; static int g_fontH=0;
static HFONT MakeFont(int h,int weight,bool italic,const WCHAR* face) {
    return CreateFontW(-h,0,0,0,weight,italic,0,0,DEFAULT_CHARSET,0,0,ANTIALIASED_QUALITY,0,face);
}
static void Fonts(int unit) {
    if(unit==g_fontH) return;
    for(HFONT* f:{&g_fTitle,&g_fItem,&g_fText,&g_fSmall}) if(*f){DeleteObject(*f);*f=nullptr;}
    g_fTitle=MakeFont(unit*40/100,FW_BLACK,true,L"Arial Black");
    g_fItem =MakeFont(unit*32/100,FW_BLACK,true,L"Arial Black");
    g_fText =MakeFont(unit*27/100,FW_NORMAL,false,L"Bahnschrift");
    g_fSmall=MakeFont(unit*24/100,FW_NORMAL,false,L"Bahnschrift");
    g_fontH=unit;
}
static bool Canvas(int w,int h) {
    if(w==g_bw&&h==g_bh&&g_bmp) return true;
    if(g_bmp){DeleteObject(g_bmp);g_bmp=nullptr;}
    if(!g_dc) g_dc=CreateCompatibleDC(nullptr);
    BITMAPINFO bi={}; bi.bmiHeader={sizeof(BITMAPINFOHEADER),w,-h,1,32,BI_RGB};
    g_bmp=CreateDIBSection(g_dc,&bi,DIB_RGB_COLORS,reinterpret_cast<void**>(&g_bits),nullptr,0);
    if(!g_bmp) return false;
    SelectObject(g_dc,g_bmp); g_bw=w; g_bh=h; SetBkMode(g_dc,TRANSPARENT);
    return true;
}

static void FillA(int x,int y,int w,int h,COLORREF c,BYTE a) {
    GdiFlush();
    const DWORD px=(DWORD(a)<<24)|(DWORD(GetRValue(c))<<16)|(DWORD(GetGValue(c))<<8)|GetBValue(c);
    for(int j=y<0?0:y;j<y+h&&j<g_bh;++j) for(int i=x<0?0:x;i<x+w&&i<g_bw;++i) g_bits[j*g_bw+i]=px;
}

static void Brush(int x,int y,int w,int t,COLORREF c) {
    GdiFlush();
    for(int i=0;i<w;++i) {
        const float u=static_cast<float>(i)/w, k=u<0.08f?u/0.08f:u>0.92f?(1-u)/0.08f:1.0f;
        const int th=static_cast<int>(t*k+0.5f); const BYTE a=static_cast<BYTE>(255*(0.55f+0.45f*k));
        for(int j=0;j<th;++j){const int yy=y+j-th/2; if(yy>=0&&yy<g_bh&&x+i>=0&&x+i<g_bw)
            g_bits[yy*g_bw+x+i]=(DWORD(a)<<24)|(DWORD(GetRValue(c))<<16)|(DWORD(GetGValue(c))<<8)|GetBValue(c);}
    }
}

static void Text(HFONT f,COLORREF c,int x,int y,int w,int h,const WCHAR* s,UINT fmt) {
    GdiFlush();

    for(int j=y<0?0:y;j<y+h&&j<g_bh;++j) for(int i=x<0?0:x;i<x+w&&i<g_bw;++i) g_bits[j*g_bw+i]|=0x01000000;
    RECT r={x,y,x+w,y+h}; SelectObject(g_dc,f); SetTextColor(g_dc,c);
    DrawTextW(g_dc,s,-1,&r,fmt|DT_SINGLELINE|DT_VCENTER|DT_END_ELLIPSIS|DT_NOPREFIX);
    GdiFlush();
    for(int j=y<0?0:y;j<y+h&&j<g_bh;++j) for(int i=x<0?0:x;i<x+w&&i<g_bw;++i) {
        DWORD& p=g_bits[j*g_bw+i]; if(!(p&0xFF000000)) p|=0xFF000000;
    }
}
static void Picture(const DWORD* px,int pw,int ph,int x,int y,int w,int h) {
    GdiFlush();
    for(int j=0;j<h;++j) {
        const int dy=y+j; if(dy<0||dy>=g_bh) continue;
        float sy=(j+0.5f)*ph/h-0.5f; if(sy<0) sy=0; const int y0=static_cast<int>(sy),y1=y0+1<ph?y0+1:y0; const float fy=sy-y0;
        for(int i=0;i<w;++i) {
            const int dx=x+i; if(dx<0||dx>=g_bw) continue;
            float sx=(i+0.5f)*pw/w-0.5f; if(sx<0) sx=0; const int x0=static_cast<int>(sx),x1=x0+1<pw?x0+1:x0; const float fx=sx-x0;
            const DWORD q[4]={px[y0*pw+x0],px[y0*pw+x1],px[y1*pw+x0],px[y1*pw+x1]};
            const float wq[4]={(1-fx)*(1-fy),fx*(1-fy),(1-fx)*fy,fx*fy}; float ch[4]={0,0,0,0};
            for(int k=0;k<4;++k) for(int b=0;b<4;++b) ch[b]+=wq[k]*((q[k]>>(b*8))&0xFF);
            const float a=ch[3]/255; DWORD& d=g_bits[dy*g_bw+dx]; DWORD n=0xFF000000;
            for(int b=0;b<3;++b){const float v=ch[b]*a+((d>>(b*8))&0xFF)*(1-a); n|=static_cast<DWORD>(v+0.5f)<<(b*8);}
            d=n;
        }
    }
}

enum Btn { B_OK, B_BACK, B_TAKE, B_RETRY, B_RESET, B_RETURN, B_LR };
static void GdiBegin(int x,int y,int w,int h) {
    GdiFlush(); for(int j=y<0?0:y;j<y+h&&j<g_bh;++j) for(int i=x<0?0:x;i<x+w&&i<g_bw;++i) g_bits[j*g_bw+i]|=0x01000000;
}
static void GdiEnd(int x,int y,int w,int h) {
    GdiFlush(); for(int j=y<0?0:y;j<y+h&&j<g_bh;++j) for(int i=x<0?0:x;i<x+w&&i<g_bw;++i){DWORD& p=g_bits[j*g_bw+i]; if(!(p&0xFF000000)) p|=0xFF000000;}
}
static int Pill(int x,int y,int h,const WCHAR* label) {
    SelectObject(g_dc,g_fSmall); SIZE sz; GetTextExtentPoint32W(g_dc,label,lstrlenW(label),&sz);
    const int w=sz.cx+h*7/10;
    GdiBegin(x,y,w,h);
    HBRUSH br=CreateSolidBrush(RGB(235,235,235)); HPEN pen=CreatePen(PS_SOLID,1,RGB(235,235,235));
    SelectObject(g_dc,br); SelectObject(g_dc,pen); RoundRect(g_dc,x,y,x+w,y+h,h*6/10,h*6/10);
    DeleteObject(br); DeleteObject(pen);
    RECT r={x,y,x+w,y+h}; SetTextColor(g_dc,RGB(20,20,20)); DrawTextW(g_dc,label,-1,&r,DT_CENTER|DT_VCENTER|DT_SINGLELINE|DT_NOPREFIX);
    GdiEnd(x,y,w,h);
    return w;
}
static int Round(int x,int y,int h,int shape,COLORREF col,const WCHAR* letter) {
    GdiBegin(x,y,h,h);
    HBRUSH br=CreateSolidBrush(RGB(28,28,28)); HPEN rim=CreatePen(PS_SOLID,1,RGB(200,200,200));
    SelectObject(g_dc,br); SelectObject(g_dc,rim); Ellipse(g_dc,x,y,x+h,y+h); DeleteObject(br); DeleteObject(rim);
    const int c=h/2,r=h*27/100,t=h/11<2?2:h/11;
    HPEN pen=CreatePen(PS_SOLID,t,col); SelectObject(g_dc,pen); SelectObject(g_dc,GetStockObject(NULL_BRUSH));
    if(shape==0){MoveToEx(g_dc,x+c-r,y+c-r,nullptr);LineTo(g_dc,x+c+r,y+c+r);MoveToEx(g_dc,x+c+r,y+c-r,nullptr);LineTo(g_dc,x+c-r,y+c+r);}
    else if(shape==1) Ellipse(g_dc,x+c-r,y+c-r,x+c+r,y+c+r);
    else if(shape==2) Rectangle(g_dc,x+c-r,y+c-r,x+c+r,y+c+r);
    else if(shape==3){POINT pt[4]={{x+c,y+c-r},{x+c+r,y+c+r*8/10},{x+c-r,y+c+r*8/10},{x+c,y+c-r}};Polyline(g_dc,pt,4);}
    else {RECT rr={x,y,x+h,y+h}; SelectObject(g_dc,g_fSmall); SetTextColor(g_dc,col); DrawTextW(g_dc,letter,-1,&rr,DT_CENTER|DT_VCENTER|DT_SINGLELINE);}
    DeleteObject(pen);
    GdiEnd(x,y,h,h);
    return h;
}
static int Arrows(int x,int y,int h) {
    const int w=h*16/10; GdiBegin(x,y,w,h);
    HBRUSH br=CreateSolidBrush(RGB(235,235,235)); SelectObject(g_dc,br); SelectObject(g_dc,GetStockObject(NULL_PEN));
    POINT l[3]={{x,y+h/2},{x+h*6/10,y+h/6},{x+h*6/10,y+h*5/6}}, r[3]={{x+w,y+h/2},{x+w-h*6/10,y+h/6},{x+w-h*6/10,y+h*5/6}};
    Polygon(g_dc,l,3); Polygon(g_dc,r,3); DeleteObject(br);
    GdiEnd(x,y,w,h); return w;
}
static int Icon(Btn b,int x,int y,int h) {
    const bool ps=g_pad==0;
    switch(b) {
    case B_OK:     return ps?Round(x,y,h,0,RGB(120,170,255),nullptr):Round(x,y,h,4,RGB(110,200,80),L"A");
    case B_BACK:   return ps?Round(x,y,h,1,RGB(255,90,90),nullptr):Round(x,y,h,4,RGB(240,80,70),L"B");
    case B_TAKE:   return Pill(x,y,h,ps?L"L2":L"LT");
    case B_RETRY:  return Pill(x,y,h,ps?L"SELECT":L"VIEW");
    case B_RESET:  return Pill(x,y,h,ps?L"L3":L"LS");
    case B_RETURN: return Pill(x,y,h,ps?L"START":L"MENU");
    case B_LR:     return Arrows(x,y,h);
    }
    return 0;
}
struct Prompt { Btn b; const WCHAR* text; };

static void Prompts(const Prompt* p,int n,int xr,int y,int h,HFONT f,COLORREF c,bool icons=true) {
    const int ih=h*62/100,gap=h*45/100,pad=h/5;
    SelectObject(g_dc,f);
    int total=0,iw[8],tw[8];
    for(int i=0;i<n;++i){SIZE sz;GetTextExtentPoint32W(g_dc,p[i].text,lstrlenW(p[i].text),&sz);tw[i]=sz.cx;
        iw[i]=p[i].b==B_LR?ih*16/10:(p[i].b==B_OK||p[i].b==B_BACK)?ih:0;
        if(!iw[i]){SelectObject(g_dc,g_fSmall);const WCHAR* lb=p[i].b==B_TAKE?(g_pad?L"LT":L"L2"):p[i].b==B_RETRY?(g_pad?L"VIEW":L"SELECT"):
            p[i].b==B_RESET?(g_pad?L"LS":L"L3"):(g_pad?L"MENU":L"START");SIZE s2;GetTextExtentPoint32W(g_dc,lb,lstrlenW(lb),&s2);iw[i]=s2.cx+ih*7/10;SelectObject(g_dc,f);}
        total+=iw[i]+pad+tw[i]+(i?gap:0);}
    int x=xr-total;
    for(int i=0;i<n;++i){
        if(i) x+=gap;
        x+=(icons?Icon(p[i].b,x,y+(h-ih)/2,ih):iw[i])+pad;
        Text(f,c,x,y,tw[i]+4,h,p[i].text,DT_LEFT); x+=tw[i];
    }
}

static void PaintSelector(int W,int H,LONG sel,const bool human[2]) {

    const int u=H/8;
    FillA(0,0,W,H,RGB(0,0,0),228);
    const int left=W*18/100,right=W*82/100;
    Text(g_fTitle,RGB(255,255,255),left-u/4,u*7/10,W/2,u*7/10,L"TAKE CONTROL",DT_LEFT);
    Brush(left-u/4,u*14/10,W*38/100,u/14,RGB(235,235,235));
    for(int p=0;p<2;++p) {
        const int y=u*17/10+p*u*17/10,h=u*15/10;
        const bool on=p==sel;
        if(on) FillA(left-u/4,y,right-left+u/2,h,RGB(62,62,62),235);
        const COLORREF main=!human[p]?RGB(90,90,90):on?RGB(255,255,255):RGB(150,150,150);
        Text(g_fItem,main,left,y,u*42/10,h,p?L"PLAYER 2":L"PLAYER 1",DT_LEFT);
        const int fh=h*84/100,fw=fh*FW/FH,fx=left+u*44/10,fy=y+(h-fh)/2;
        if(g_faceOk[p]) {FillA(fx-2,fy-2,fw+4,fh+4,on?RGB(235,235,235):RGB(110,110,110),255); Picture(g_face[p],FW,FH,fx,fy,fw,fh);}
        WCHAR who[96]; swprintf(who,96,L"%ls%ls",g_dataOk?g_name[p]:(p?L"P2":L"P1"),human[p]?L"":L"   (CPU, not available)");
        Text(g_fText,main,fx+fw+u/2,y,right-(fx+fw+u/2),h,who,DT_LEFT);
    }
    Brush(left-u/4,u*52/10,right-left+u/2,u/22,RGB(220,220,220));
    WCHAR info[200]; const LONG s=sel<0?0:sel>1?1:sel;
    swprintf(info,200,L"Play as %ls from here. The checkpoint is set at this moment.",g_dataOk?g_name[s]:(s?L"P2":L"P1"));
    Text(g_fText,RGB(235,235,235),left-u/4,u*54/10,right-left+u/2,u*9/10,info,DT_CENTER);
    const Prompt pr[2]={{B_OK,L"OK"},{B_BACK,L"Back"}};
    Prompts(pr,2,right+u/4,u*65/10,u*8/10,g_fText,RGB(225,225,225));
}

static LONG g_menuN=0,g_menuCur=-1; static DWORD g_menuInstant=0; static bool g_menuNext=false;
static void PaintRounds(int W,int H,LONG sel) {
    const int u=H/10;
    FillA(0,0,W,H,RGB(0,0,0),228);
    const int left=W*18/100,right=W*82/100;
    Text(g_fTitle,RGB(255,255,255),left-u/4,u*5/10,W/2,u*7/10,L"ROUND SELECT",DT_LEFT);
    Brush(left-u/4,u*12/10,W*38/100,u/14,RGB(235,235,235));
    const LONG m=g_menuN+(g_menuNext?1:0);
    const int top=u*15/10,bottom=u*80/10;
    int rh=m>0?(bottom-top)/m:u; if(rh>u*12/10) rh=u*12/10;
    for(LONG i=0;i<m;++i) {
        const int y=top+i*rh,h=rh*92/100;
        const bool on=i==sel;
        if(on) FillA(left-u/4,y,right-left+u/2,h,RGB(62,62,62),235);
        const COLORREF main=on?RGB(255,255,255):RGB(150,150,150);
        WCHAR label[48],note[64];
        if(i<g_menuN){swprintf(label,48,L"ROUND %ld",i+1); swprintf(note,64,L"%ls",((g_menuInstant>>i)&1)?(i==g_menuCur?L"current round : instant":L"instant"):i==g_menuCur?L"current round":L"");}
        else {swprintf(label,48,L"NEXT ROUND"); swprintf(note,64,L"not seen yet : fast forward");}
        Text(g_fItem,main,left,y,u*50/10,h,label,DT_LEFT);
        Text(g_fText,main,left+u*52/10,y,right-(left+u*52/10),h,note,DT_LEFT);
    }
    Brush(left-u/4,u*81/10,right-left+u/2,u/22,RGB(220,220,220));
    Text(g_fText,RGB(235,235,235),left-u/4,u*82/10,right-left+u/2,u*8/10,L"The replay jumps to the FIGHT of the chosen round.",DT_CENTER);
    const Prompt pr[2]={{B_OK,L"OK"},{B_BACK,L"Back"}};
    Prompts(pr,2,right+u/4,u*91/10,u*8/10,g_fText,RGB(225,225,225));
}

static void PaintHint(int W,int H) {
    FillA(0,0,W,H,RGB(0,0,0),0);
    const Prompt pr[1]={{B_TAKE,L"Take control"}};
    Prompts(pr,1,W-H/3+2,2,H,g_fText,RGB(0,0,0),false);
    Prompts(pr,1,W-H/3,0,H,g_fText,RGB(240,240,240));
}

static void PaintBar(int W,int H,LONG slot) {
    FillA(0,0,W,H,RGB(0,0,0),215);
    Brush(W*3/100,1,W*94/100,2,RGB(200,200,200));
    WCHAR l[120]; swprintf(l,120,L"IN CONTROL  %ls",g_dataOk?g_name[slot&1]:(slot&1?L"P2":L"P1"));
    Text(g_fText,RGB(255,255,255),W*4/100,0,W*36/100,H,l,DT_LEFT);
    const Prompt pr[3]={{B_RETRY,L"Restart from checkpoint"},{B_RESET,L"Restart + reset stage"},{B_RETURN,L"Return to replay"}};
    Prompts(pr,3,W*96/100,0,H,g_fSmall,RGB(225,225,225));
}

static void Blit(IDirect3DDevice9* d,float x0,float y0,int w,int h) {
    IDirect3DStateBlock9* sb=nullptr;
    if(FAILED(d->CreateStateBlock(D3DSBT_ALL,&sb))) return;
    IDirect3DSurface9 *bb=nullptr,*rt=nullptr;
    if(FAILED(d->GetBackBuffer(0,0,D3DBACKBUFFER_TYPE_MONO,&bb))||!bb){sb->Release();return;}
    D3DSURFACE_DESC sd; bb->GetDesc(&sd);
    d->GetRenderTarget(0,&rt); d->SetRenderTarget(0,bb);
    D3DVIEWPORT9 vp={0,0,sd.Width,sd.Height,0,1}; d->SetViewport(&vp);
    d->BeginScene();
    d->SetVertexShader(nullptr); d->SetPixelShader(nullptr); d->SetFVF(D3DFVF_XYZRHW|D3DFVF_TEX1);
    d->SetTexture(0,g_tex); for(int i=1;i<8;++i) d->SetTexture(i,nullptr);
    d->SetTextureStageState(0,D3DTSS_COLOROP,D3DTOP_SELECTARG1); d->SetTextureStageState(0,D3DTSS_COLORARG1,D3DTA_TEXTURE);
    d->SetTextureStageState(0,D3DTSS_ALPHAOP,D3DTOP_SELECTARG1); d->SetTextureStageState(0,D3DTSS_ALPHAARG1,D3DTA_TEXTURE);
    d->SetTextureStageState(0,D3DTSS_TEXCOORDINDEX,0); d->SetTextureStageState(0,D3DTSS_TEXTURETRANSFORMFLAGS,D3DTTFF_DISABLE);
    d->SetTextureStageState(1,D3DTSS_COLOROP,D3DTOP_DISABLE); d->SetTextureStageState(1,D3DTSS_ALPHAOP,D3DTOP_DISABLE);
    d->SetSamplerState(0,D3DSAMP_MINFILTER,D3DTEXF_POINT); d->SetSamplerState(0,D3DSAMP_MAGFILTER,D3DTEXF_POINT);
    d->SetSamplerState(0,D3DSAMP_MIPFILTER,D3DTEXF_NONE);
    d->SetSamplerState(0,D3DSAMP_ADDRESSU,D3DTADDRESS_CLAMP); d->SetSamplerState(0,D3DSAMP_ADDRESSV,D3DTADDRESS_CLAMP);
    d->SetSamplerState(0,D3DSAMP_SRGBTEXTURE,0); d->SetRenderState(D3DRS_SRGBWRITEENABLE,FALSE);
    d->SetRenderState(D3DRS_ALPHABLENDENABLE,TRUE); d->SetRenderState(D3DRS_SRCBLEND,D3DBLEND_SRCALPHA);
    d->SetRenderState(D3DRS_DESTBLEND,D3DBLEND_INVSRCALPHA); d->SetRenderState(D3DRS_BLENDOP,D3DBLENDOP_ADD);
    d->SetRenderState(D3DRS_ALPHATESTENABLE,FALSE); d->SetRenderState(D3DRS_ZENABLE,D3DZB_FALSE);
    d->SetRenderState(D3DRS_ZWRITEENABLE,FALSE); d->SetRenderState(D3DRS_STENCILENABLE,FALSE);
    d->SetRenderState(D3DRS_SCISSORTESTENABLE,FALSE); d->SetRenderState(D3DRS_CULLMODE,D3DCULL_NONE);
    d->SetRenderState(D3DRS_FOGENABLE,FALSE); d->SetRenderState(D3DRS_LIGHTING,FALSE); d->SetRenderState(D3DRS_COLORWRITEENABLE,0xF);
    const float x1=x0+w,y1=y0+h;
    struct V{float x,y,z,w,u,v;} q[4]={{x0,y0,0,1,0,0},{x1,y0,0,1,1,0},{x0,y1,0,1,0,1},{x1,y1,0,1,1,1}};
    d->DrawPrimitiveUP(D3DPT_TRIANGLESTRIP,2,q,sizeof(V));
    d->EndScene();
    d->SetRenderTarget(0,rt); if(rt) rt->Release();
    sb->Apply(); sb->Release(); bb->Release();
}

static int g_lastKind=0; static LONG g_lastSel=-2,g_lastFaces=-1,g_lastMenu=-1;
static void Draw(IDirect3DDevice9* d,int kind,LONG sel,const bool human[2]) {
    IDirect3DSurface9* bb=nullptr;
    if(FAILED(d->GetBackBuffer(0,0,D3DBACKBUFFER_TYPE_MONO,&bb))||!bb) return;
    D3DSURFACE_DESC sd; bb->GetDesc(&sd); bb->Release();
    float gh=static_cast<float>(sd.Height),gw=gh*16/9,gx=0,gy=0;
    if(gw>sd.Width){gw=static_cast<float>(sd.Width);gh=gw*9/16;gy=(sd.Height-gh)/2;} else gx=(sd.Width-gw)/2;
    int w,h; float x,y;
    if(kind==1){w=static_cast<int>(gw);h=static_cast<int>(gh*0.416f);x=gx;y=gy+(gh-h)/2;}
    else if(kind==2){w=static_cast<int>(gw);h=static_cast<int>(gh*0.065f);x=gx;y=gy+gh*0.765f;}
    else if(kind==4){w=static_cast<int>(gw);h=static_cast<int>(gh*0.6f);x=gx;y=gy+(gh-h)/2;}
    else {w=static_cast<int>(gw*0.17f);h=static_cast<int>(gh*0.055f);x=gx+gw*0.785f;y=gy+gh*0.832f;}
    if(w<32||h<8) return;
    if(d!=g_texDev&&g_tex){g_tex->Release();g_tex=nullptr;}
    const LONG faces=g_faceOk[0]+2*g_faceOk[1];
    const LONG menu=static_cast<LONG>((static_cast<DWORD>(g_menuN)<<24)^(g_menuInstant<<6)^(g_menuNext?32u:0u)^static_cast<DWORD>(g_menuCur&31));
    if(!g_tex||g_tw!=w||g_th!=h||kind!=g_lastKind||sel!=g_lastSel||faces!=g_lastFaces||(kind==4&&menu!=g_lastMenu)) {
        if(!g_tex||g_tw!=w||g_th!=h) {
            if(g_tex){g_tex->Release();g_tex=nullptr;}
            if(FAILED(d->CreateTexture(w,h,1,0,D3DFMT_A8R8G8B8,D3DPOOL_MANAGED,&g_tex,nullptr))) return;
            g_tw=w;g_th=h;g_texDev=d;
        }
        if(!Canvas(w,h)) return;
        Fonts(static_cast<int>(gh/10.8f));
        if(kind==1) PaintSelector(w,h,sel,human); else if(kind==2) PaintBar(w,h,sel); else if(kind==4) PaintRounds(w,h,sel); else PaintHint(w,h);
        GdiFlush();
        D3DLOCKED_RECT lr;
        if(FAILED(g_tex->LockRect(0,&lr,nullptr,0))) return;
        for(int j=0;j<h;++j) memcpy(static_cast<BYTE*>(lr.pBits)+j*lr.Pitch,g_bits+j*w,w*4);
        g_tex->UnlockRect(0);
        g_lastKind=kind;g_lastSel=sel;g_lastFaces=faces;g_lastMenu=menu;
    }
    Blit(d,static_cast<float>(static_cast<int>(x))-0.5f,static_cast<float>(static_cast<int>(y))-0.5f,w,h);
}

static void* g_textOriginal=nullptr;
typedef const WCHAR*(__cdecl* TextFn)(DWORD,DWORD,DWORD);
static const WCHAR* __cdecl TextC(DWORD lang,DWORD id,DWORD flags) {
    const WCHAR* t=reinterpret_cast<TextFn>(g_textOriginal)(lang,id,flags);
    if(!g_hint||!t||IsBadReadPtr(t,2)||!wcsstr(t,L"Photo mode")||wcsstr(t,L"[pad:L2]")) return t;
    static WCHAR buf[2][400]; static int k=0; WCHAR* b=buf[k^=1];
    static DWORD logged=0xFFFFFFFF; if(logged!=id){logged=id; LogF("Ligne d aide du replay : texte 0x%lX complete.",id);}
    swprintf(b,400,L"%ls  @[pad:L2]Take control",t);
    return b;
}
}
extern "C" const WCHAR* __cdecl rt_TextC(DWORD a,DWORD b,DWORD c) { return ui::TextC(a,b,c); }
#ifdef _MSC_VER
static __declspec(naked) void TextThunk() {
    __asm {
        push ecx
        push edx
        push dword ptr [esp+20]
        push dword ptr [esp+20]
        push dword ptr [esp+20]
        call rt_TextC
        add esp,12
        pop edx
        pop ecx
        ret
    }
}
#else
extern "C" void TextThunk();
__asm__(".intel_syntax noprefix\n"
    ".text\n"
    ".globl _TextThunk\n"
    "_TextThunk:\n"
    "push ecx\n"
    "push edx\n"
    "push dword ptr [esp+20]\n"
    "push dword ptr [esp+20]\n"
    "push dword ptr [esp+20]\n"
    "call _rt_TextC\n"
    "add esp,12\n"
    "pop edx\n"
    "pop ecx\n"
    "ret\n"
    ".att_syntax prefix\n");
#endif
extern "C" void __cdecl rt_HudSeen(BYTE* m) { ui::g_hud=m; ui::g_hudTick=GetTickCount(); }
static void* g_hudJump=nullptr;
#ifdef _MSC_VER
static __declspec(naked) void HudThunk() {
    __asm {
        pushad
        pushfd
        push ecx
        call rt_HudSeen
        add esp,4
        popfd
        popad
        jmp [g_hudJump]
    }
}
#else
extern "C" void HudThunk();
extern "C" void* rt_hudUpdate;
void* rt_hudUpdate=nullptr;
__asm__(".intel_syntax noprefix\n"
    ".text\n"
    ".globl _HudThunk\n"
    "_HudThunk:\n"
    "pushad\n"
    "pushfd\n"
    "push ecx\n"
    "call _rt_HudSeen\n"
    "add esp,4\n"
    "popfd\n"
    "popad\n"
    "jmp dword ptr [_rt_hudUpdate]\n"
    ".att_syntax prefix\n");
#endif
namespace ui {
static bool HookHud() {
    void** slot=reinterpret_cast<void**>(B+0x99D06C+33*4);
    if(*slot!=static_cast<void*>(B+0x250AF0)) return false;
    DWORD old=0,ig=0; if(!VirtualProtect(slot,4,PAGE_READWRITE,&old)) return false;
    g_hudUpdate=*slot; g_hudJump=*slot;
#ifndef _MSC_VER
    rt_hudUpdate=*slot;
#endif
    *slot=reinterpret_cast<void*>(&HudThunk); VirtualProtect(slot,4,old,&ig);
    return true;
}

static bool HookText() {
    BYTE* t=B+0x745BA0; static const BYTE pro[5]={0x55,0x8B,0xEC,0x6A,0xFF};
    BYTE cur[5]; if(!Copy(cur,t,5)) return false;
    DWORD old=0,ig=0;
    if(!memcmp(cur,pro,5)) {
        BYTE* tr=static_cast<BYTE*>(VirtualAlloc(nullptr,16,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE));
        if(!tr) return false;
        memcpy(tr,pro,5); tr[5]=0xE9; *reinterpret_cast<DWORD*>(tr+6)=reinterpret_cast<DWORD>(t+5)-reinterpret_cast<DWORD>(tr+10);
        g_textOriginal=tr;
        if(!VirtualProtect(t,5,PAGE_EXECUTE_READWRITE,&old)) return false;
        t[0]=0xE9; *reinterpret_cast<DWORD*>(t+1)=reinterpret_cast<DWORD>(&TextThunk)-reinterpret_cast<DWORD>(t+5);
    } else if(cur[0]==0xE9) {
        g_textOriginal=t+5+*reinterpret_cast<LONG*>(cur+1);
        if(!VirtualProtect(t,5,PAGE_EXECUTE_READWRITE,&old)) return false;
        InterlockedExchange(reinterpret_cast<volatile LONG*>(t+1),static_cast<LONG>(reinterpret_cast<DWORD>(&TextThunk)-reinterpret_cast<DWORD>(t+5)));
    } else return false;
    VirtualProtect(t,5,old,&ig); FlushInstructionCache(GetCurrentProcess(),t,5);
    return true;
}
}
