#include <cmath>
namespace dm {

static volatile LONG on;
static void* origImp[5];
struct M { float m[4][4]; };
struct V3 { float x,y,z; };
struct Q { float x,y,z,w; };
struct P { float a,b,c,d; };
static const double HALFPI_HI=1.5707963267341256e+00, HALFPI_LO=6.0771005065061922e-11, TWO_OVER_PI=0.63661977236758134308;
static double SinPoly(double r){const double r2=r*r;return r*(1.0+r2*(-1.0/6+r2*(1.0/120+r2*(-1.0/5040+r2*(1.0/362880+r2*(-1.0/39916800+r2*(1.0/6227020800.0)))))));}
static double CosPoly(double r){const double r2=r*r;return 1.0+r2*(-0.5+r2*(1.0/24+r2*(-1.0/720+r2*(1.0/40320+r2*(-1.0/3628800+r2*(1.0/479001600+r2*(-1.0/87178291200.0)))))));}
static void SinCos(float a,float& s,float& c) {
    const double x=a;const double k=floor(x*TWO_OVER_PI+0.5);const double r=(x-k*HALFPI_HI)-k*HALFPI_LO;
    const double sr=SinPoly(r),cr=CosPoly(r);const int q=static_cast<int>(k-4.0*floor(k*0.25));
    switch(q){case 0:s=static_cast<float>(sr);c=static_cast<float>(cr);break;case 1:s=static_cast<float>(cr);c=static_cast<float>(-sr);break;
              case 2:s=static_cast<float>(-sr);c=static_cast<float>(-cr);break;default:s=static_cast<float>(-cr);c=static_cast<float>(sr);break;}
}
static M* WINAPI MatrixMultiply(M* out,const M* a,const M* b) {
    if(!on && origImp[0])return reinterpret_cast<M* (WINAPI*)(M* out,const M* a,const M* b)>(origImp[0])(out,a,b);
    M t;for(int i=0;i<4;++i)for(int j=0;j<4;++j)t.m[i][j]=a->m[i][0]*b->m[0][j]+a->m[i][1]*b->m[1][j]+a->m[i][2]*b->m[2][j]+a->m[i][3]*b->m[3][j];
    *out=t;return out;
}
static M* WINAPI MatrixInverse(M* out,float* det,const M* mm) {
    if(!on && origImp[1])return reinterpret_cast<M* (WINAPI*)(M* out,float* det,const M* mm)>(origImp[1])(out,det,mm);
    const float* m=&mm->m[0][0];float inv[16];
    inv[0]=m[5]*m[10]*m[15]-m[5]*m[11]*m[14]-m[9]*m[6]*m[15]+m[9]*m[7]*m[14]+m[13]*m[6]*m[11]-m[13]*m[7]*m[10];
    inv[4]=-m[4]*m[10]*m[15]+m[4]*m[11]*m[14]+m[8]*m[6]*m[15]-m[8]*m[7]*m[14]-m[12]*m[6]*m[11]+m[12]*m[7]*m[10];
    inv[8]=m[4]*m[9]*m[15]-m[4]*m[11]*m[13]-m[8]*m[5]*m[15]+m[8]*m[7]*m[13]+m[12]*m[5]*m[11]-m[12]*m[7]*m[9];
    inv[12]=-m[4]*m[9]*m[14]+m[4]*m[10]*m[13]+m[8]*m[5]*m[14]-m[8]*m[6]*m[13]-m[12]*m[5]*m[10]+m[12]*m[6]*m[9];
    inv[1]=-m[1]*m[10]*m[15]+m[1]*m[11]*m[14]+m[9]*m[2]*m[15]-m[9]*m[3]*m[14]-m[13]*m[2]*m[11]+m[13]*m[3]*m[10];
    inv[5]=m[0]*m[10]*m[15]-m[0]*m[11]*m[14]-m[8]*m[2]*m[15]+m[8]*m[3]*m[14]+m[12]*m[2]*m[11]-m[12]*m[3]*m[10];
    inv[9]=-m[0]*m[9]*m[15]+m[0]*m[11]*m[13]+m[8]*m[1]*m[15]-m[8]*m[3]*m[13]-m[12]*m[1]*m[11]+m[12]*m[3]*m[9];
    inv[13]=m[0]*m[9]*m[14]-m[0]*m[10]*m[13]-m[8]*m[1]*m[14]+m[8]*m[2]*m[13]+m[12]*m[1]*m[10]-m[12]*m[2]*m[9];
    inv[2]=m[1]*m[6]*m[15]-m[1]*m[7]*m[14]-m[5]*m[2]*m[15]+m[5]*m[3]*m[14]+m[13]*m[2]*m[7]-m[13]*m[3]*m[6];
    inv[6]=-m[0]*m[6]*m[15]+m[0]*m[7]*m[14]+m[4]*m[2]*m[15]-m[4]*m[3]*m[14]-m[12]*m[2]*m[7]+m[12]*m[3]*m[6];
    inv[10]=m[0]*m[5]*m[15]-m[0]*m[7]*m[13]-m[4]*m[1]*m[15]+m[4]*m[3]*m[13]+m[12]*m[1]*m[7]-m[12]*m[3]*m[5];
    inv[14]=-m[0]*m[5]*m[14]+m[0]*m[6]*m[13]+m[4]*m[1]*m[14]-m[4]*m[2]*m[13]-m[12]*m[1]*m[6]+m[12]*m[2]*m[5];
    inv[3]=-m[1]*m[6]*m[11]+m[1]*m[7]*m[10]+m[5]*m[2]*m[11]-m[5]*m[3]*m[10]-m[9]*m[2]*m[7]+m[9]*m[3]*m[6];
    inv[7]=m[0]*m[6]*m[11]-m[0]*m[7]*m[10]-m[4]*m[2]*m[11]+m[4]*m[3]*m[10]+m[8]*m[2]*m[7]-m[8]*m[3]*m[6];
    inv[11]=-m[0]*m[5]*m[11]+m[0]*m[7]*m[9]+m[4]*m[1]*m[11]-m[4]*m[3]*m[9]-m[8]*m[1]*m[7]+m[8]*m[3]*m[5];
    inv[15]=m[0]*m[5]*m[10]-m[0]*m[6]*m[9]-m[4]*m[1]*m[10]+m[4]*m[2]*m[9]+m[8]*m[1]*m[6]-m[8]*m[2]*m[5];
    const float d=m[0]*inv[0]+m[1]*inv[4]+m[2]*inv[8]+m[3]*inv[12];
    if(det)*det=d;
    if(d==0.0f)return nullptr;
    const float id=1.0f/d;float* o=&out->m[0][0];for(int i=0;i<16;++i)o[i]=inv[i]*id;
    return out;
}
static M* WINAPI MatrixRotationAxis(M* out,const V3* pv,float angle) {
    if(!on && origImp[2])return reinterpret_cast<M* (WINAPI*)(M* out,const V3* pv,float angle)>(origImp[2])(out,pv,angle);
    float x=pv->x,y=pv->y,z=pv->z;const float len=sqrtf(x*x+y*y+z*z);
    if(len!=0.0f){x/=len;y/=len;z/=len;}
    float s,c;SinCos(angle,s,c);const float cd=1.0f-c;
    out->m[0][0]=cd*x*x+c;   out->m[1][0]=cd*x*y-s*z; out->m[2][0]=cd*x*z+s*y; out->m[3][0]=0.0f;
    out->m[0][1]=cd*y*x+s*z; out->m[1][1]=cd*y*y+c;   out->m[2][1]=cd*y*z-s*x; out->m[3][1]=0.0f;
    out->m[0][2]=cd*z*x-s*y; out->m[1][2]=cd*z*y+s*x; out->m[2][2]=cd*z*z+c;   out->m[3][2]=0.0f;
    out->m[0][3]=0.0f;out->m[1][3]=0.0f;out->m[2][3]=0.0f;out->m[3][3]=1.0f;
    return out;
}
static Q* WINAPI QuaternionRotationMatrix(Q* out,const M* pm) {
    if(!on && origImp[3])return reinterpret_cast<Q* (WINAPI*)(Q* out,const M* pm)>(origImp[3])(out,pm);
    const float (*m)[4]=pm->m;const float trace=m[0][0]+m[1][1]+m[2][2]+1.0f;
    if(trace>1.0f){const float s=2.0f*sqrtf(trace);out->x=(m[1][2]-m[2][1])/s;out->y=(m[2][0]-m[0][2])/s;out->z=(m[0][1]-m[1][0])/s;out->w=0.25f*s;return out;}
    int mx=0;for(int i=1;i<3;++i)if(m[i][i]>m[mx][mx])mx=i;
    float s;
    switch(mx){
    case 0:s=2.0f*sqrtf(1.0f+m[0][0]-m[1][1]-m[2][2]);out->x=0.25f*s;out->y=(m[0][1]+m[1][0])/s;out->z=(m[0][2]+m[2][0])/s;out->w=(m[1][2]-m[2][1])/s;break;
    case 1:s=2.0f*sqrtf(1.0f+m[1][1]-m[0][0]-m[2][2]);out->x=(m[0][1]+m[1][0])/s;out->y=0.25f*s;out->z=(m[1][2]+m[2][1])/s;out->w=(m[2][0]-m[0][2])/s;break;
    default:s=2.0f*sqrtf(1.0f+m[2][2]-m[0][0]-m[1][1]);out->x=(m[0][2]+m[2][0])/s;out->y=(m[1][2]+m[2][1])/s;out->z=0.25f*s;out->w=(m[0][1]-m[1][0])/s;break;
    }
    return out;
}
static P* WINAPI PlaneFromPoints(P* out,const V3* a,const V3* b,const V3* c) {
    if(!on && origImp[4])return reinterpret_cast<P* (WINAPI*)(P* out,const V3* a,const V3* b,const V3* c)>(origImp[4])(out,a,b,c);
    const float e1x=b->x-a->x,e1y=b->y-a->y,e1z=b->z-a->z,e2x=c->x-a->x,e2y=c->y-a->y,e2z=c->z-a->z;
    float nx=e1y*e2z-e1z*e2y,ny=e1z*e2x-e1x*e2z,nz=e1x*e2y-e1y*e2x;
    const float len=sqrtf(nx*nx+ny*ny+nz*nz);if(len!=0.0f){nx/=len;ny/=len;nz/=len;}else{nx=ny=nz=0.0f;}
    out->a=nx;out->b=ny;out->c=nz;out->d=-(a->x*nx+a->y*ny+a->z*nz);
    return out;
}

static unsigned PatchImports(BYTE* image) {
    struct R { const char* name; void* fn; } repl[]={
        {"D3DXMatrixMultiply",reinterpret_cast<void*>(&MatrixMultiply)},{"D3DXMatrixInverse",reinterpret_cast<void*>(&MatrixInverse)},
        {"D3DXMatrixRotationAxis",reinterpret_cast<void*>(&MatrixRotationAxis)},{"D3DXQuaternionRotationMatrix",reinterpret_cast<void*>(&QuaternionRotationMatrix)},
        {"D3DXPlaneFromPoints",reinterpret_cast<void*>(&PlaneFromPoints)}};
    const IMAGE_DOS_HEADER* dos=reinterpret_cast<const IMAGE_DOS_HEADER*>(image);
    const IMAGE_NT_HEADERS32* nt=reinterpret_cast<const IMAGE_NT_HEADERS32*>(image+dos->e_lfanew);
    const IMAGE_DATA_DIRECTORY& dir=nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
    unsigned n=0;
    for(const IMAGE_IMPORT_DESCRIPTOR* d=reinterpret_cast<const IMAGE_IMPORT_DESCRIPTOR*>(image+dir.VirtualAddress);d->Name;++d) {
        if(_stricmp(reinterpret_cast<const char*>(image+d->Name),"d3dx9_43.dll"))continue;
        const IMAGE_THUNK_DATA32* names=reinterpret_cast<const IMAGE_THUNK_DATA32*>(image+(d->OriginalFirstThunk?d->OriginalFirstThunk:d->FirstThunk));
        IMAGE_THUNK_DATA32* slots=reinterpret_cast<IMAGE_THUNK_DATA32*>(image+d->FirstThunk);
        for(;names->u1.AddressOfData;++names,++slots) {
            if(names->u1.Ordinal&IMAGE_ORDINAL_FLAG32)continue;
            const char* nm=reinterpret_cast<const char*>(reinterpret_cast<const IMAGE_IMPORT_BY_NAME*>(image+names->u1.AddressOfData)->Name);
            for(unsigned ri=0;ri<5;++ri){const R& r=repl[ri];if(strcmp(nm,r.name))continue;DWORD old=0,ig=0;
                if(VirtualProtect(&slots->u1.Function,4,PAGE_READWRITE,&old)){origImp[ri]=reinterpret_cast<void*>(slots->u1.Function);slots->u1.Function=reinterpret_cast<DWORD>(r.fn);VirtualProtect(&slots->u1.Function,4,old,&ig);++n;}}
        }
    }
    return n;
}

static float __cdecl DetCosf(float a){float s,c;SinCos(a,s,c);return c;}
static float __cdecl DetSinf(float a){float s,c;SinCos(a,s,c);return s;}

static __declspec(naked) void CosDispatch(){__asm{cmp dm::on,0}__asm{jne det}__asm{fld dword ptr [esp+4]}__asm{fcos}__asm{ret}__asm{det: jmp DetCosf}}
static __declspec(naked) void SinDispatch(){__asm{cmp dm::on,0}__asm{jne det}__asm{fld dword ptr [esp+4]}__asm{fsin}__asm{ret}__asm{det: jmp DetSinf}}
static double AtanSmall(double t){
    const double t2=t*t;double r=0.0;
    for(int k=21;k>=3;k-=2)r=(r+((k/2)%2?-1.0:1.0)/k)*t2;
    return t*(1.0+r);
}
static double AtanUnit(double x){
    const double TAN15=0.26794919243112270,SQRT3=1.7320508075688772,PI6=0.52359877559829887;
    if(x<=TAN15)return AtanSmall(x);
    return PI6+AtanSmall((x*SQRT3-1.0)/(x+SQRT3));
}
static double __cdecl DetAtan2(double y,double x) {
    const double PI=3.14159265358979323846,PI2=1.57079632679489661923;
    if(x==0.0 && y==0.0)return (_copysign(1.0,x)<0)?_copysign(PI,y):_copysign(0.0,y);
    const double ax=fabs(x),ay=fabs(y);
    double a=ay<=ax?AtanUnit(ay/ax):PI2-AtanUnit(ax/ay);
    if(x<0)a=PI-a;
    return y<0?-a:a;
}

static __declspec(naked) void FpatanThunk() {
    __asm {
        cmp   dm::on,0
        jne   det
        fpatan
        fstp  dword ptr [esp+0x1C]
        ret
    det:
        push  eax
        push  ecx
        push  edx
        sub   esp,128
        movups [esp],xmm0
        movups [esp+16],xmm1
        movups [esp+32],xmm2
        movups [esp+48],xmm3
        movups [esp+64],xmm4
        movups [esp+80],xmm5
        movups [esp+96],xmm6
        movups [esp+112],xmm7
        sub   esp,16
        fstp  qword ptr [esp+8]
        fstp  qword ptr [esp]
        call  DetAtan2
        add   esp,16
        movups xmm0,[esp]
        movups xmm1,[esp+16]
        movups xmm2,[esp+32]
        movups xmm3,[esp+48]
        movups xmm4,[esp+64]
        movups xmm5,[esp+80]
        movups xmm6,[esp+96]
        movups xmm7,[esp+112]
        add   esp,128
        pop   edx
        pop   ecx
        pop   eax
        fstp  dword ptr [esp+0x1C]
        ret
    }
}
static bool WriteCode(BYTE* at,const BYTE* code,size_t n){DWORD old=0,ig=0;if(!VirtualProtect(at,n,PAGE_EXECUTE_READWRITE,&old))return false;
    memcpy(at,code,n);VirtualProtect(at,n,old,&ig);FlushInstructionCache(GetCurrentProcess(),at,n);return true;}
static unsigned PatchX87(BYTE* image) {
    unsigned n=0;
    static const BYTE cosB[]={0x55,0x8B,0xEC,0x83,0xE4,0xF8,0xD9,0x45,0x08,0xD9,0xFF,0x8B,0xE5,0x5D,0xC3};
    static const BYTE sinB[]={0x55,0x8B,0xEC,0x83,0xE4,0xF8,0xD9,0x45,0x08,0xD9,0xFE,0x8B,0xE5,0x5D,0xC3};
    static const BYTE atB[]={0xD9,0xF3,0xD9,0x5C,0x24,0x18};
    struct J { DWORD rva; const BYTE* orig; size_t len; void* fn; bool call; } js[]={
        {0xA410,cosB,sizeof(cosB),reinterpret_cast<void*>(&CosDispatch),false},
        {0xA420,sinB,sizeof(sinB),reinterpret_cast<void*>(&SinDispatch),false},
        {0xB7EF,atB,sizeof(atB),reinterpret_cast<void*>(&FpatanThunk),true}};
    for(const J& j:js){BYTE* at=image+j.rva;if(memcmp(at,j.orig,j.len))continue;
        BYTE c[6]={static_cast<BYTE>(j.call?0xE8:0xE9),0,0,0,0,0x90};const DWORD rel=reinterpret_cast<DWORD>(j.fn)-reinterpret_cast<DWORD>(at)-5;memcpy(c+1,&rel,4);
        if(WriteCode(at,c,j.call?6:5))++n;}
    return n;
}
}
