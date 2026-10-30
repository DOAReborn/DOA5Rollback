namespace kb {
static volatile LONG noKO=0, blocked=0;
static bool installed=false;
constexpr DWORD SITE=0x31B87A, NONLETHAL=0x31B884, LETHAL=0x31B9C3;
static bool Install(BYTE* image) {
    BYTE* s=image+SITE;
    static const BYTE expect[6]={0x66,0x39,0x46,0xFE,0x0F,0x86};
    if(memcmp(s,expect,6)) return false;
    if(reinterpret_cast<DWORD>(s)+10+*reinterpret_cast<DWORD*>(s+6)!=reinterpret_cast<DWORD>(image+LETHAL)) return false;
    BYTE* code=static_cast<BYTE*>(VirtualAlloc(nullptr,0x100,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE));
    if(!code) return false;
    BYTE* p=code;
    auto b=[&](BYTE x){*p++=x;};
    auto d=[&](DWORD x){memcpy(p,&x,4);p+=4;};
    auto rel=[&](DWORD target){d(reinterpret_cast<DWORD>(image+target)-(reinterpret_cast<DWORD>(p)+4));};
    b(0x66);b(0x39);b(0x46);b(0xFE);
    b(0x0F);b(0x87);rel(NONLETHAL);
    b(0x83);b(0x3D);d(reinterpret_cast<DWORD>(&noKO));b(0);
    b(0x0F);b(0x84);rel(LETHAL);
    b(0xF0);b(0xFF);b(0x05);d(reinterpret_cast<DWORD>(&blocked));
    b(0x66);b(0x8B);b(0x46);b(0xFE);
    b(0x66);b(0x48);
    b(0x66);b(0x89);b(0x46);b(0x2C);
    b(0xE9);rel(NONLETHAL);
    FlushInstructionCache(GetCurrentProcess(),code,0x100);
    BYTE patch[10]={0xE9}; *reinterpret_cast<DWORD*>(patch+1)=reinterpret_cast<DWORD>(code)-(reinterpret_cast<DWORD>(s)+5);
    for(int i=5;i<10;++i) patch[i]=0x90;
    DWORD old=0,ig=0;
    if(!VirtualProtect(s,10,PAGE_EXECUTE_READWRITE,&old)) return false;
    memcpy(s,patch,10); VirtualProtect(s,10,old,&ig); FlushInstructionCache(GetCurrentProcess(),s,10);
    installed=true; return true;
}
}
