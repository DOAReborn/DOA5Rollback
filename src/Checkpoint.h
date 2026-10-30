namespace cp {
struct Range { BYTE* address; DWORD size; const char* name; DWORD offset; };
struct Guard { BYTE* address; DWORD size; BYTE bytes[32]; };
struct Cursor { BYTE* target; void* allocation; };
static Range ranges[1024]; static unsigned count;
static Guard guards[1024]; static unsigned guardCount;
static Cursor cursors[258]; static unsigned cursorCount;
static BYTE* animation[2];
static DWORD total,manager,threadId; static BYTE* reader;
static BYTE *saved,*scratch;
static constexpr DWORD limit=4*1024*1024;

static volatile LONG active;
static DWORD savedFrame,lastFrame,frontierCount;
static volatile LONG requestSave,requestRestore;
static volatile LONG lastResult;
static volatile LONG roundOver;

static void LogR(const char* format,...) {
    char line[1024];va_list a;va_start(a,format);_vsnprintf_s(line,sizeof line,_TRUNCATE,format,a);va_end(a);Log(line);
}
#ifdef DOA5RB_RELEASE
template<class... A> static inline void Logf(const char*,A...) {}
#else
static void Logf(const char* format,...) {

    char line[1024];va_list a;va_start(a,format);_vsnprintf_s(line,sizeof line,_TRUNCATE,format,a);va_end(a);Log(line);
}
#endif

struct Seen { DWORD object,stamp; };
static Seen seen[8];
static void NotePhysics(DWORD object) {
    unsigned oldest=0;
    for(unsigned i=0;i<8;++i){if(seen[i].object==object){seen[i].stamp=frontierCount;return;}if(seen[i].stamp<seen[oldest].stamp)oldest=i;}
    seen[oldest]={object,frontierCount};
}

static bool vqCache; static MEMORY_BASIC_INFORMATION vqTab[256]; static unsigned vqN,vqCalls,vqHits;
static SIZE_T VQ(const void* p,MEMORY_BASIC_INFORMATION* m) {
    if(vqCache){const DWORD a=reinterpret_cast<DWORD>(p);
        for(unsigned i=0;i<vqN;++i){const DWORD b=reinterpret_cast<DWORD>(vqTab[i].BaseAddress);if(a>=b && a-b<vqTab[i].RegionSize){*m=vqTab[i];++vqHits;return sizeof(*m);}}}
    ++vqCalls;const SIZE_T r=VirtualQuery(p,m,sizeof(*m));
    if(r && vqCache && vqN<256)vqTab[vqN++]=*m;
    return r;
}
struct VQScope { VQScope(){vqCache=true;vqN=0;vqCalls=vqHits=0;} ~VQScope(){vqCache=false;} };
static bool Writable(BYTE* p,DWORD n) {
    if(!p || !n || reinterpret_cast<uintptr_t>(p)+n<reinterpret_cast<uintptr_t>(p))return false;
    BYTE* end=p+n;
    while(p<end) {
        MEMORY_BASIC_INFORMATION m={};if(!VQ(p,&m))return false;
        DWORD protection=m.Protect&0xFF;
        if(m.State!=MEM_COMMIT || (m.Protect&PAGE_GUARD) ||
           (protection!=PAGE_READWRITE && protection!=PAGE_WRITECOPY))return false;
        BYTE* next=static_cast<BYTE*>(m.BaseAddress)+m.RegionSize;
        if(next<=p)return false;p=next<end?next:end;
    } return true;
}
static bool Readable(DWORD address,MEMORY_BASIC_INFORMATION& m) {
    if(!address || !VQ(reinterpret_cast<void*>(address),&m))return false;
    DWORD p=m.Protect&0xFF;
    return m.State==MEM_COMMIT && !(m.Protect&PAGE_GUARD) &&
        (p==PAGE_READONLY || p==PAGE_READWRITE || p==PAGE_WRITECOPY);
}
static bool Add(BYTE* p,DWORD n,const char* name) {
    if(!n)return true;
    if(count==1024 || n>limit-total || !Writable(p,n))return false;
    for(unsigned i=0;i<count;++i)if(p<ranges[i].address+ranges[i].size && ranges[i].address<p+n)return false;
    ranges[count++]={p,n,name,total};total+=n;return true;
}
static bool GuardAt(BYTE* p,DWORD n) {
    if(guardCount==1024 || n>32)return false;
    Guard& g=guards[guardCount++];g.address=p;g.size=n;return Copy(g.bytes,p,n);
}

static bool AnimationCheck() {
    for(BYTE* d:animation) {
        if(!d)return false;
        DWORD seenMask=0;
        for(unsigned i=0;i<4;++i) {
            DWORD p=Read(d+0x5C+i*4),which=3;
            for(unsigned j=0;j<3;++j)if(p==reinterpret_cast<DWORD>(d+8+j*0x1C))which=j;
            if(which==3)return false;
            if(i){if(seenMask&(1u<<which))return false;seenMask|=1u<<which;}
        }
    } return true;
}
static bool PrepareAnimation() {
    for(unsigned i=0;i<2;++i) {
        BYTE* idAddress=base+0xFD0540+i*0x6C8+0x28;BYTE id=0;
        if(!Copy(&id,idAddress,1)||id>1||!GuardAt(idAddress,1))return false;
        BYTE* d=base+0xFCC760+DWORD(id)*0x9C;animation[i]=d;
        if(i && d==animation[0])return false;
        BYTE n=0;if(!Copy(&n,d+0x94,1)||n!=21)return false;
        if(!GuardAt(d,8)||!GuardAt(d+0x88,0x14)||!Add(d,0x9C,"animation_descriptor"))return false;
        for(unsigned k=0;k<2;++k)
            if(!Add(reinterpret_cast<BYTE*>(Read(d+k*4)),DWORD(n)*64,"animation_matrices"))return false;
        for(DWORD off:{8u,0x24u,0x40u,0x6Cu}) {
            if(!GuardAt(d+off,12))return false;
            for(unsigned k=0;k<3;++k)
                if(!Add(reinterpret_cast<BYTE*>(Read(d+off+k*4)),DWORD(n)*16,"animation_vectors"))return false;
        }
    }
    return AnimationCheck() && Add(base+0xFCC220,32,"animation_previous_root") &&
        Add(base+0xFCACB0,32,"animation_movement") && Add(base+0xFC92E0,0xC00,"animation_world_cache");
}

static bool CheckChannels() {
    for(unsigned i=0;i<cursorCount;++i){
        if(!cursors[i].target)continue;
        MEMORY_BASIC_INFORMATION m={};
        if(!Readable(reinterpret_cast<DWORD>(cursors[i].target),m) || m.AllocationBase!=cursors[i].allocation)return false;
    }
    return true;
}
static bool PrepareChannels() {
    if(!GuardAt(base+0xFCC9D0,32))return false;
    for(unsigned p=0;p<2;++p){
        BYTE* table=base+0xFCC9D0+p*16;
        if(Read(table+12)!=21)return false;
        for(unsigned k=0;k<3;++k){
            BYTE* block=reinterpret_cast<BYTE*>(Read(table+k*4));
            unsigned objects=k?21:1;
            if(!Writable(block,k?21*0x88:0x84))return false;
            for(unsigned i=0;i<objects;++i)for(unsigned axis=0;axis<3;++axis){
                BYTE* c=block+i*0x88+axis*0x2C;
                if(cursorCount>=258)return false;
                DWORD address=Read(c+4);MEMORY_BASIC_INFORMATION m={};
                if(!address)cursors[cursorCount++]={nullptr,nullptr};
                else {
                    if(!Readable(address,m) || !GuardAt(reinterpret_cast<BYTE*>(address),16))return false;
                    cursors[cursorCount++]={reinterpret_cast<BYTE*>(address),m.AllocationBase};
                }
                if(!Add(c,0x2C,"channel"))return false;
            }
        }
    }
    return cursorCount==258 && CheckChannels();
}
static const char* Check() {
    if(GetCurrentThreadId()!=threadId)return "thread different";
    if(Read(base+0xFCE790)!=manager || (Read(reinterpret_cast<void*>(manager+8))!=2 && Read(reinterpret_cast<void*>(manager+8))!=1) ||
       Read(reinterpret_cast<void*>(manager+0xC))!=reinterpret_cast<DWORD>(reader))return "lecteur de replay different";
    if(Read(base+0x1087A4C)!=4)return "pas en combat";
    for(unsigned i=0;i<guardCount;++i){BYTE b[32];if(!Copy(b,guards[i].address,guards[i].size)||memcmp(b,guards[i].bytes,guards[i].size))return "garde modifiee";}
    for(unsigned i=0;i<count;++i)if(!Writable(ranges[i].address,ranges[i].size))return "plage non inscriptible";
    if(!AnimationCheck())return "selecteurs d'animation incoherents";
    if(!CheckChannels())return "donnees de mouvement dechargees";
    return nullptr;
}
static bool ReadAll(BYTE* dest) {
    for(unsigned i=0;i<count;++i)if(!Copy(dest+ranges[i].offset,ranges[i].address,ranges[i].size))return false;
    return true;
}
static bool WriteAll(const BYTE* src) {
    __try {for(unsigned i=0;i<count;++i)memcpy(ranges[i].address,src+ranges[i].offset,ranges[i].size);return true;}
    __except(EXCEPTION_EXECUTE_HANDLER){return false;}
}
static void Release() {
    if(saved)HeapFree(GetProcessHeap(),0,saved);
    saved=scratch=nullptr;
    count=guardCount=cursorCount=0;total=0;animation[0]=animation[1]=nullptr;InterlockedExchange(&active,0);
}

struct Component { DWORD address,stamp,owner,table; };
static Component components[64]; static DWORD componentScenes[3]; static unsigned componentPurges;
static void NoteComponent(DWORD address) {
    const DWORD mgr=Read(base+0x2072580);DWORD sc[3]={0,0,0};
    if(mgr){sc[0]=Read(reinterpret_cast<void*>(mgr));sc[1]=Read(reinterpret_cast<void*>(mgr+4));sc[2]=Read(reinterpret_cast<void*>(mgr+0xC));}
    if(memcmp(sc,componentScenes,sizeof sc)){memcpy(componentScenes,sc,sizeof sc);memset(components,0,sizeof components);
        if(componentPurges<20)Logf("DECOR : changement de scene : composants du decor oublies (lab165).");++componentPurges;}
    const DWORD owner=Read(reinterpret_cast<void*>(address)),table=Read(reinterpret_cast<void*>(address+4));
    unsigned oldest=0;
    for(unsigned i=0;i<64;++i){if(components[i].address==address){components[i].stamp=frontierCount;components[i].owner=owner;components[i].table=table;return;}if(components[i].stamp<components[oldest].stamp)oldest=i;}
    components[oldest]={address,frontierCount,owner,table};
}
static bool ComponentLive(const Component& c){
    return c.address && c.stamp+600>=frontierCount && Read(reinterpret_cast<void*>(c.address))==c.owner && Read(reinterpret_cast<void*>(c.address+4))==c.table;}
struct MemoryStream { DWORD vtable; BYTE* buffer; DWORD size,position; };
struct Archive { MemoryStream* stream; BYTE owns,accumulator,mask,pad; };
typedef void(__cdecl* Serialize)(DWORD owner,Archive* archive);
typedef void(__cdecl* Apply)(DWORD owner);
typedef void(__fastcall* Flush)(Archive* archive,void* unused);
struct StageState { DWORD component,owner,descriptor,length; BYTE data[0x200]; };
static StageState stageStates[64]; static unsigned stageCount;
static BYTE stageScratch[0x1000];
static bool InText(DWORD v){return v>=reinterpret_cast<DWORD>(base)+0x1000 && v<reinterpret_cast<DWORD>(base)+0x966000;}
static bool InRdata(DWORD v){return v>=reinterpret_cast<DWORD>(base)+0x966000 && v<reinterpret_cast<DWORD>(base)+0xCB3000;}

static DWORD rttiRefus; static unsigned rttiLogs;
static bool CppTable(DWORD t) {
    const DWORD col=Read(reinterpret_cast<void*>(t-4));
    if(!InRdata(col) || Read(reinterpret_cast<void*>(col))!=0)return false;
    const DWORD td=Read(reinterpret_cast<void*>(col+0xC)),chd=Read(reinterpret_cast<void*>(col+0x10));
    if(td<reinterpret_cast<DWORD>(base)+0xCB3000 || td>=reinterpret_cast<DWORD>(base)+0x21F8000 || !InRdata(chd) || Read(reinterpret_cast<void*>(chd))!=0)return false;
    const DWORD nb=Read(reinterpret_cast<void*>(chd+8));
    return nb>=1 && nb<=64 && InRdata(Read(reinterpret_cast<void*>(chd+0xC)));
}
static bool Describe(DWORD component,DWORD& owner,DWORD& descriptor) {
    owner=Read(reinterpret_cast<void*>(component));descriptor=Read(reinterpret_cast<void*>(component+4));
    if(!owner || !InRdata(descriptor) || !InText(Read(reinterpret_cast<void*>(descriptor))) ||
        !InText(Read(reinterpret_cast<void*>(descriptor+4))))return false;
    if(CppTable(descriptor)){++rttiRefus;if(rttiLogs<10){++rttiLogs;Logf("DECOR : entree refusee : sa table (game+%06lX) est une table de methodes C++ (RTTI), pas une table de serialisation (snow1).",descriptor-reinterpret_cast<DWORD>(base));}return false;}
    return true;
}
static bool CallSave(DWORD owner,DWORD descriptor,MemoryStream* s) {
    __try {
        Archive a={s,1,0,1,0};
        reinterpret_cast<Serialize>(Read(reinterpret_cast<void*>(descriptor+4)))(owner,&a);
        reinterpret_cast<Flush>(base+0x59EBC0)(&a,nullptr);
        return true;
    } __except(EXCEPTION_EXECUTE_HANDLER){return false;}
}
static bool CallLoad(DWORD owner,DWORD descriptor,MemoryStream* s) {
    __try {
        Archive a={s,1,0,1,0};
        reinterpret_cast<Serialize>(Read(reinterpret_cast<void*>(descriptor)))(owner,&a);
        DWORD apply=Read(reinterpret_cast<void*>(descriptor+8));
        if(InText(apply))reinterpret_cast<Apply>(apply)(owner);
        return true;
    } __except(EXCEPTION_EXECUTE_HANDLER){return false;}
}
static void StageSave() {
    stageCount=0;
    for(const Component& c:components) {
        if(!ComponentLive(c) || c.stamp+2<frontierCount || stageCount>=64)continue;
        DWORD owner,descriptor;if(!Describe(c.address,owner,descriptor))continue;
        MemoryStream s={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,sizeof(stageScratch),0};
        memset(stageScratch,0,sizeof(stageScratch));
        if(!CallSave(owner,descriptor,&s) || s.position>sizeof(stageStates[0].data))continue;
        StageState& st=stageStates[stageCount++];
        st.component=c.address;st.owner=owner;st.descriptor=descriptor;st.length=s.position;memcpy(st.data,stageScratch,s.position);
    }
}
static void StageLoad() {
    for(unsigned i=0;i<stageCount;++i) {
        StageState& st=stageStates[i];DWORD owner,descriptor;
        if(!Describe(st.component,owner,descriptor) || owner!=st.owner || descriptor!=st.descriptor)continue;
        memcpy(stageScratch,st.data,st.length);memset(stageScratch+st.length,0,16);
        MemoryStream s={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,st.length+16,0};
        CallLoad(owner,descriptor,&s);
    }
}

static DWORD AllocSlot(DWORD address){return (address*2654435761u)>>13;}
struct Allocation { DWORD address,size; };
static Allocation* allocations; static constexpr DWORD allocationSlots=1u<<19; static SRWLOCK allocationLock=SRWLOCK_INIT;
static DWORD allocFill,allocRefused;
static void RecordAllocation(DWORD address,DWORD size) {
    if(!address || !allocations)return;
    AcquireSRWLockExclusive(&allocationLock);
    const DWORD h=AllocSlot(address);bool noted=false;
    for(DWORD i=0;i<64;++i){Allocation& a=allocations[(h+i)&(allocationSlots-1)];if(!a.address||a.address==address){if(!a.address)++allocFill;a.address=address;a.size=size;noted=true;break;}}
    if(!noted)++allocRefused;
    ReleaseSRWLockExclusive(&allocationLock);
}
static DWORD RecordedSize(DWORD address) {
    if(!allocations)return 0;
    AcquireSRWLockShared(&allocationLock);DWORD size=0;const DWORD h=AllocSlot(address);
    for(DWORD i=0;i<64;++i){const Allocation& a=allocations[(h+i)&(allocationSlots-1)];if(!a.address)break;if(a.address==address){size=a.size;break;}}
    ReleaseSRWLockShared(&allocationLock);return size;
}
struct Region { DWORD start,end; };
static Region regions[16384]; static unsigned regionCount;
struct Block { DWORD address,size,offset; WORD depth; bool bounded; };
static constexpr unsigned maxBlocks=3000,stableFrames=10;
static constexpr DWORD maxBlockBytes=4*1024*1024,pageStart=0x1070000,pageCount=16;
static Block blocks[maxBlocks]; static unsigned blockCount; static DWORD blockBytes;
static DWORD blockSet[16384];
static BYTE *blockSaved,*pageSaved; static DWORD *blockHashes,*pageHashes;
static unsigned hashedFrames;

static DWORD regionMap[65536/32];
static void ScanRegions() {
    memset(regionMap,0,sizeof(regionMap));
    regionCount=0;DWORD a=0x10000;
    while(regionCount<16384) {
        MEMORY_BASIC_INFORMATION m={};if(!VirtualQuery(reinterpret_cast<void*>(a),&m,sizeof(m)))break;
        DWORD s=reinterpret_cast<DWORD>(m.BaseAddress),e=s+static_cast<DWORD>(m.RegionSize);
        if(m.State==MEM_COMMIT && m.Type==MEM_PRIVATE && !(m.Protect&PAGE_GUARD) && (m.Protect&0xFF)==PAGE_READWRITE){regions[regionCount++]={s,e};for(DWORD g=s>>16;g<=((e-1)>>16);++g)regionMap[g>>5]|=1u<<(g&31);}
        if(e<=a)break;a=e;
    }
}
static bool HeapPointer(DWORD v,DWORD& regionEnd) {
    if(v&3)return false;
    if(!(regionMap[v>>21]&(1u<<((v>>16)&31))))return false;
    unsigned lo=0,hi=regionCount;
    while(lo<hi){unsigned mid=(lo+hi)/2;if(regions[mid].end<=v)lo=mid+1;else hi=mid;}
    if(lo>=regionCount || v<regions[lo].start)return false;
    auto own=[&](const void* p,DWORD n){DWORD s=reinterpret_cast<DWORD>(p);return p && v>=s && v<s+n;};
    if(own(blockSaved,maxBlockBytes+pageCount*0x1000)||own(saved,total*2)||own(blockHashes,(maxBlocks+pageCount)*(stableFrames+1)*4))return false;
    regionEnd=regions[lo].end;return true;
}
static bool PointerLike(DWORD v) {
    DWORD e=0;
    return (v>=reinterpret_cast<DWORD>(base) && v<reinterpret_cast<DWORD>(base)+0x21F8000) || HeapPointer(v,e);
}

static constexpr unsigned setProbeMax=64;
static DWORD gPtrWords,gFloatWords,gProbes,gSetFull,gBudget; static bool gStopped;
static bool GraphBudgetOut(){return blockBytes+0x800>maxBlockBytes;}
static void AddBlock(DWORD address,WORD depth) {
    DWORD regionEnd=0;
    if(blockCount>=maxBlocks || !HeapPointer(address,regionEnd))return;
    ++gPtrWords;{const DWORD e=(address>>23)&0xFF;if(e>=0x70 && e<=0x90)++gFloatWords;}
    if(depth && GraphBudgetOut()){++gBudget;return;}
    const DWORD h=(address*2654435761u)>>18;bool inserted=false;
    for(unsigned i=0;i<setProbeMax;++i){++gProbes;DWORD& slot=blockSet[(h+i)&16383];if(slot==address)return;if(!slot){slot=address;inserted=true;break;}}
    if(!inserted){++gSetFull;return;}
    DWORD size=depth?0x800:0x2000;if(size>regionEnd-address)size=regionEnd-address;
    DWORD exact=RecordedSize(address);if(exact && exact<size)size=exact;size&=~3u;
    if(!size || blockBytes+size>maxBlockBytes)return;
    blocks[blockCount++]={address,size,blockBytes,depth,exact!=0};blockBytes+=size;
}
static DWORD FastHash(const void* p,DWORD n) {
    DWORD h=0x9E3779B9;
    __try{const DWORD* d=static_cast<const DWORD*>(p);for(DWORD i=0;i<n/4;++i){h^=d[i];h=(h<<5)|(h>>27);h*=0x01000193;}}
    __except(EXCEPTION_EXECUTE_HANDLER){return 0xDEADDEAD;}
    return h;
}

static SRWLOCK graphLock=SRWLOCK_INIT; static bool graphOpen; static unsigned graphNext; static DWORD graphWords,graphSteps; static double graphMs;
static bool DecorAlloc() {
    if(!blockSaved)blockSaved=static_cast<BYTE*>(VirtualAlloc(nullptr,maxBlockBytes+pageCount*0x1000,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!blockHashes)blockHashes=static_cast<DWORD*>(VirtualAlloc(nullptr,(maxBlocks+pageCount)*(stableFrames+1)*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!blockSaved || !blockHashes)return false;
    pageSaved=blockSaved+maxBlockBytes;pageHashes=blockHashes+maxBlocks*(stableFrames+1);return true;
}
static void GraphBegin() {
    memset(blockSet,0,sizeof(blockSet));blockCount=0;blockBytes=0;ScanRegions();
    gPtrWords=gFloatWords=gProbes=gSetFull=gBudget=0;gStopped=false;
    AddBlock(Read(base+0x2072580),0);
    for(const Component& c:components)if(ComponentLive(c))AddBlock(Read(reinterpret_cast<void*>(c.address)),0);
    graphNext=0;graphWords=0;graphSteps=0;graphMs=0;graphOpen=true;
}
static bool GraphRun(DWORD budget) {
    LARGE_INTEGER f,t0,t1;QueryPerformanceFrequency(&f);QueryPerformanceCounter(&t0);
    DWORD done=0;
    for(;graphNext<blockCount && done<budget;++graphNext) {
        if(GraphBudgetOut() || blockCount>=maxBlocks){gStopped=true;graphNext=blockCount;break;}
        const unsigned i=graphNext;if(blocks[i].depth>=3)continue;
        static DWORD tmp[0x2000/4];const DWORD n=blocks[i].size/4;Copy(tmp,reinterpret_cast<void*>(blocks[i].address),n*4);done+=n;
        for(DWORD o=0;o<n;++o)AddBlock(tmp[o],static_cast<WORD>(blocks[i].depth+1));
    }
    QueryPerformanceCounter(&t1);graphWords+=done;++graphSteps;graphMs+=(t1.QuadPart-t0.QuadPart)*1000.0/static_cast<double>(f.QuadPart);
    return graphNext>=blockCount;
}

static void DecorGraphStep(bool debut,DWORD budget) {
    if(!DecorAlloc())return;
    AcquireSRWLockExclusive(&graphLock);
    if(debut || !graphOpen)GraphBegin();
    if(graphNext<blockCount)GraphRun(budget);
    ReleaseSRWLockExclusive(&graphLock);
}
static void DecorGraphDrop(){AcquireSRWLockExclusive(&graphLock);graphOpen=false;ReleaseSRWLockExclusive(&graphLock);}
static void DecorBuild() {
    hashedFrames=0;
    if(!DecorAlloc()){blockCount=0;return;}
    LARGE_INTEGER f,t0,t1,t2;QueryPerformanceFrequency(&f);QueryPerformanceCounter(&t0);
    AcquireSRWLockExclusive(&graphLock);
    const bool avance=graphOpen;const DWORD avantMots=graphOpen?graphWords:0,avantPas=graphOpen?graphSteps:0;const double avantMs=graphOpen?graphMs:0;
    if(!graphOpen)GraphBegin();
    GraphRun(0xFFFFFFFFu);
    graphOpen=false;
    ReleaseSRWLockExclusive(&graphLock);
    QueryPerformanceCounter(&t1);
    for(unsigned i=0;i<blockCount;++i)Copy(blockSaved+blocks[i].offset,reinterpret_cast<void*>(blocks[i].address),blocks[i].size);
    Copy(pageSaved,base+pageStart,pageCount*0x1000);
    QueryPerformanceCounter(&t2);
    const double k=1000.0/static_cast<double>(f.QuadPart);
    Logf("Labo : decor : graphe %s (%lu mots en %lu pas, %.1f ms), fin a la photo %.1f ms (%lu mots), %u objets, copie %.1f ms.",
        avance?"prepare a l'avance":"PAS prepare",avantMots,avantPas,avantMs,(t1.QuadPart-t0.QuadPart)*k,graphWords-avantMots,blockCount,(t2.QuadPart-t1.QuadPart)*k);
    Logf("Labo : decor (snow1) : %lu Ko pris, %s ; %lu mot(s) pris pour des pointeurs, dont %lu a l'air de flottants ; %.2f sondage(s) par mot, %lu sortie(s) table pleine, %lu refus du budget ; tailles connues : %lu case(s) prise(s) sur %lu, %lu taille(s) non notee(s).",
        blockBytes/1024,gStopped?"parcours arrete au budget":"parcours complet",gPtrWords,gFloatWords,gPtrWords?static_cast<double>(gProbes)/gPtrWords:0.0,gSetFull,gBudget,allocFill,allocationSlots,allocRefused);
}

static void DecorRecord(DWORD index) {
    if(!blockHashes || index>stableFrames || index!=hashedFrames)return;
    DWORD* row=blockHashes+index*maxBlocks;
    for(unsigned i=0;i<blockCount;++i)row[i]=FastHash(reinterpret_cast<void*>(blocks[i].address),blocks[i].size);
    DWORD* prow=pageHashes+index*pageCount;
    for(unsigned i=0;i<pageCount;++i)prow[i]=FastHash(base+pageStart+i*0x1000,0x1000);
    ++hashedFrames;
}
static void DecorRestore() {
    if(!blockHashes || hashedFrames<=stableFrames)return;
    DWORD written=0;
    for(unsigned i=0;i<blockCount;++i) {
        bool stable=true;for(DWORD k=1;k<=stableFrames;++k)if(blockHashes[k*maxBlocks+i]!=blockHashes[i]){stable=false;break;}
        const Block& b=blocks[i];
        if(!stable || !b.bounded)continue;
        DWORD typeNow=0,typeThen=0;memcpy(&typeThen,blockSaved+b.offset,4);
        if(!Copy(&typeNow,reinterpret_cast<void*>(b.address),4) || typeNow!=typeThen)continue;
        for(DWORD k=0;k+4<=b.size;k+=4) {
            DWORD old=0,now=0;memcpy(&old,blockSaved+b.offset+k,4);
            if(!Copy(&now,reinterpret_cast<void*>(b.address+k),4) || now==old || PointerLike(old) || PointerLike(now))continue;
            __try{*reinterpret_cast<DWORD*>(b.address+k)=old;written+=4;}__except(EXCEPTION_EXECUTE_HANDLER){}
        }
    }
    for(unsigned i=0;i<pageCount;++i) {
        bool stable=true;for(DWORD k=1;k<=stableFrames;++k)if(pageHashes[k*pageCount+i]!=pageHashes[i]){stable=false;break;}
        if(!stable)continue;
        for(DWORD k=0;k<0x1000;k+=4) {
            DWORD old=0,now=0;memcpy(&old,pageSaved+i*0x1000+k,4);Copy(&now,base+pageStart+i*0x1000+k,4);
            if(now==old || PointerLike(old) || PointerLike(now))continue;
            __try{*reinterpret_cast<DWORD*>(base+pageStart+i*0x1000+k)=old;written+=4;}__except(EXCEPTION_EXECUTE_HANDLER){}
        }
    }
    if(written)Logf("Point de controle : decor remis (%lu octets).",written);
}

static DWORD extraWin[8][2]; static unsigned extraWinCount; static unsigned rngExtra;
static bool AddWindow(DWORD start,DWORD end,const char* name) {
    BYTE* a=base+start;BYTE* e=base+end;
    while(a<e) {
        BYTE* next=e;BYTE* skip=nullptr;
        for(unsigned i=0;i<count;++i) {
            BYTE* rs=ranges[i].address;BYTE* re=rs+ranges[i].size;
            if(re<=a || rs>=e)continue;
            if(rs<=a){if(re>skip)skip=re;}else if(rs<next)next=rs;
        }
        if(skip){a=skip;continue;}
        if(!Add(a,static_cast<DWORD>(next-a),name))return false;
        a=next;
    }
    return true;
}
static BYTE savedClock;

static bool RoundDecided() {
    short h0=0,h1=0;BYTE clock=0;
    Copy(&h0,base+0xFD0540+0x2C,2);Copy(&h1,base+0xFD0540+0x6C8+0x2C,2);Copy(&clock,base+0x10885DA,1);
    return h0<=0 || h1<=0 || clock==0;
}

static double prepT[12];
static double PT(LARGE_INTEGER& t){LARGE_INTEGER n,f;QueryPerformanceCounter(&n);QueryPerformanceFrequency(&f);const double ms=double(n.QuadPart-t.QuadPart)*1000.0/double(f.QuadPart);t=n;return ms;}
static const char* Prepare(BYTE* r,DWORD m) {
    LARGE_INTEGER pt;QueryPerformanceCounter(&pt);memset(prepT,0,sizeof(prepT));
    VQScope vqs;
    Release();
    prepT[0]=PT(pt);
    if(RoundDecided())return "round deja termine (K.O. ou temps ecoule)";
    reader=r;manager=m;threadId=GetCurrentThreadId();
    if(!GuardAt(reader,0x20) || !GuardAt(reinterpret_cast<BYTE*>(m),0x18))return "en-tete lecteur";
    BYTE* stream=reinterpret_cast<BYTE*>(Read(reader+4));
    BYTE* wrapper=reinterpret_cast<BYTE*>(Read(reader+8));
    if(!stream || !wrapper || Read(wrapper)!=reinterpret_cast<DWORD>(stream) ||
       Read(stream)!=reinterpret_cast<DWORD>(base+0x9BA1F4) || Read(stream+12)>Read(stream+8) ||
       !GuardAt(stream,12) || !GuardAt(wrapper,4))return "flux du replay";
    prepT[1]=PT(pt);

    {static const DWORD rngs[]={0x20906E0,0x10844E8,0x2071378,0x2072A58,0x2070830,0x206FE68};unsigned ok=0;
     for(DWORD r:rngs)if(Add(base+r,0x9C8,"rng_effets"))++ok;rngExtra=ok;}
    if(!Add(base+0x1087AB0,0x9C8,"rng") || !Add(base+0xFD0540,0xD90,"players") ||
       !Add(base+0xFCEE78,0x910,"logic") || !Add(base+0x10878F8,0xB0,"slots") ||
       !Add(base+0xFCE99C,8,"feed_globals") || !Add(reader+0x20,0x74,"reader_scalars") ||
       !Add(reinterpret_cast<BYTE*>(m)+0x18,0x18,"manager_scalars") ||
       !Add(stream+12,4,"stream_cursor"))return "plages globales";
    if(!Add(base+0xFCF788,0xD90,"player_secondary"))return "plages globales";
    if(!Add(base+0xFCED68,0x68,"player_history_previous") || !Add(base+0xFCEDD8,0x68,"player_history_current"))return "plages globales";
    prepT[2]=PT(pt);
    BYTE* owner=reinterpret_cast<BYTE*>(Read(base+0x20720D4));
    if(!GuardAt(base+0x20720D4,4))return "liste des owners";
    for(unsigned i=0;i<2;++i) {
        if(!owner || !GuardAt(owner+8,0x10))return "liste des owners";
        for(DWORD off: {0x18u,0xC0u}) {
            if(!GuardAt(owner+off,8))return "liste des owners";
            DWORD begin=Read(owner+off),end=Read(owner+off+4);
            if(end<begin || end-begin>65536 || !Add(reinterpret_cast<BYTE*>(begin),end-begin,off==0x18?"pose":"array_c0"))return "tableaux de pose";
        }
        owner=reinterpret_cast<BYTE*>(Read(owner+0x10));
    }
    if(owner)return "plus de deux personnages";
    prepT[3]=PT(pt);
    if(!PrepareAnimation())return "animation";
    prepT[4]=PT(pt);
    for(unsigned player=0;player<2;++player)
        for(DWORD off:{0x10u,0x14u,0x1Cu,0x24u,0x34u})
            if(!Add(base+0xFCAB00+player*0x3C+off,4,"animation_time"))return "temps d'animation";
    prepT[5]=PT(pt);
    if(!PrepareChannels())return "canaux d'animation";
    prepT[6]=PT(pt);
    if(!Add(base+0xFCC214,4,"animation_advance_gate"))return "indicateur d'avancement";
    for(unsigned player=0;player<2;++player)
        if(!Add(base+0xFCBB00+player*0x180,12,"body_position"))return "position corps";
    for(const Seen& s:seen) {
        if(!s.object || s.stamp+2<frontierCount)continue;
        BYTE* p=reinterpret_cast<BYTE*>(s.object);
        if(!GuardAt(p+4,4) || !GuardAt(p+0x4C,8) || !Add(p,0x30C,"physics"))return "physique";
    }
    prepT[7]=PT(pt);

    if(!AddWindow(0xFCBAB0,0xFCBDB0,"w1_corps") || !AddWindow(0xFCA000,0xFCB700,"w2_mouvement") ||
       !AddWindow(0xFC7000,0xFCA000,"w3_blocs") || !AddWindow(0xFCC000,0xFD0540,"w4_globaux") ||
       !AddWindow(0xFB8000,0xFC0000,"w6_cameras"))return "fenetres statiques";
    for(unsigned i=0;i<extraWinCount;++i)if(!AddWindow(extraWin[i][0],extraWin[i][1],"plage_en_plus"))return "plage en plus";
    prepT[8]=PT(pt);
    saved=static_cast<BYTE*>(HeapAlloc(GetProcessHeap(),0,total*2));
    prepT[9]=PT(pt);
    if(!saved){Release();return "memoire";}
    scratch=saved+total;
    const char* reason=Check();
    prepT[10]=PT(pt);
    if(reason){Release();return reason;}
    if(!ReadAll(saved)){Release();return "lecture";}
    Copy(&savedClock,base+0x10885DA,1);
    prepT[11]=PT(pt);
    return nullptr;
}
static void Drop(const char* reason) {
    if(!active)return;
    Logf("Point de controle abandonne : %s.",reason);
    Release();
}
static bool DoRestore(DWORD f) {
    const char* reason=Check();
    if(reason){Logf("Point de controle : retour refuse (%s).",reason);return false;}
    if(!WriteAll(saved) || !ReadAll(scratch) || memcmp(saved,scratch,total)) {
        Logf("Point de controle : ERREUR d'ecriture, abandonne.");Release();return false;
    }
    lastFrame=savedFrame;
    DecorRestore();
    StageLoad();
    Logf("Point de controle : retour instantane de l'image %lu a l'image %lu.",f,savedFrame);
    return true;
}

static void Frontier(BYTE* r) {
    ++frontierCount;
    DWORD m=Read(base+0xFCE790);
    bool fighting=r && m && Read(reinterpret_cast<void*>(m+8))==2 && Read(base+0x1087A4C)==4 &&
        Read(reinterpret_cast<void*>(m+0xC))==reinterpret_cast<DWORD>(r);
    if(!fighting) {
        if(active && Read(base+0x1087A4C)!=4){Drop("fin du combat, du round ou du replay");InterlockedExchange(&roundOver,1);}
        if(InterlockedExchange(&requestRestore,0))InterlockedExchange(&lastResult,2);
        InterlockedExchange(&requestSave,0);
        return;
    }
    DWORD f=Read(r+0x2C);
    if(Read(reinterpret_cast<void*>(m+0x1C))!=f)return;
    BYTE clock=0;Copy(&clock,base+0x10885DA,1);
    if(active && (r!=reader || m!=manager))Drop("autre lecteur de replay");
    else if(active && f<lastFrame)Drop("le replay est reparti en arriere");
    else if(active && clock>savedClock){Drop("nouveau round");InterlockedExchange(&roundOver,1);}
    else if(active && RoundDecided()){Drop("K.O. ou temps ecoule, retour desactive jusqu'a la prochaine reprise");InterlockedExchange(&roundOver,1);}
    lastFrame=f;
    if(InterlockedExchange(&requestSave,0)) {
        InterlockedExchange(&roundOver,0);
        const char* reason=Prepare(r,m);
        if(reason) {
            if(RoundDecided()){InterlockedExchange(&roundOver,1);Logf("Point de controle impossible a l'image %lu : %s ; retour desactive.",f,reason);}
            else Logf("Point de controle impossible a l'image %lu (%s) : retour par rattrapage accelere.",f,reason);
            return;
        }
        savedFrame=f;InterlockedExchange(&active,1);
        StageSave();DecorBuild();DecorRecord(0);
        Logf("Point de controle pose a l'image %lu (%u plages, %lu octets, %u objets de decor).",f,count,total,blockCount);
        return;
    }
    if(InterlockedExchange(&requestRestore,0)) {
        InterlockedExchange(&lastResult,active && DoRestore(f)?1:2);
        return;
    }
    if(active && f>savedFrame)DecorRecord(f-savedFrame);
}
}
