namespace cp {
struct Range { BYTE* address; DWORD size; const char* name; DWORD offset; };
struct Guard { BYTE* address; DWORD size; BYTE bytes[32]; };
struct Cursor { BYTE* target; void* allocation; };
static Range ranges[1024]; static unsigned count;
static Guard guards[1024]; static unsigned guardCount;
static Cursor cursors[258]; static unsigned cursorCount;

struct PhysicsRef { unsigned range,guard; };
static PhysicsRef physicsRefs[8]; static unsigned physicsCount;
static bool skip[1024];
static bool decorStale;
static BYTE* animation[2];
static DWORD total,manager,threadId; static BYTE* reader;
static BYTE *saved,*scratch;
static constexpr DWORD limit=1024*1024;

static volatile LONG active;
static DWORD savedFrame,lastFrame,frontierCount;
static volatile LONG requestSave,requestRestore;
static volatile LONG lastResult;
static volatile LONG roundOver;
static volatile LONG saveCount,restoreCount;
static volatile LONG keepAcrossRounds;

static void Logf(const char* format,...) {
    char line[512];va_list a;va_start(a,format);vsprintf_s(line,format,a);va_end(a);Log(line);
}

struct Seen { DWORD object,stamp; };
static Seen seen[8];
static void NotePhysics(DWORD object) {
    unsigned oldest=0;
    for(unsigned i=0;i<8;++i){if(seen[i].object==object){seen[i].stamp=frontierCount;return;}if(seen[i].stamp<seen[oldest].stamp)oldest=i;}
    seen[oldest]={object,frontierCount};
}
static bool Writable(BYTE* p,DWORD n) {
    if(!p || !n || reinterpret_cast<uintptr_t>(p)+n<reinterpret_cast<uintptr_t>(p))return false;
    BYTE* end=p+n;
    while(p<end) {
        MEMORY_BASIC_INFORMATION m={};if(!VirtualQuery(p,&m,sizeof(m)))return false;
        DWORD protection=m.Protect&0xFF;
        if(m.State!=MEM_COMMIT || (m.Protect&PAGE_GUARD) ||
           (protection!=PAGE_READWRITE && protection!=PAGE_WRITECOPY))return false;
        BYTE* next=static_cast<BYTE*>(m.BaseAddress)+m.RegionSize;
        if(next<=p)return false;p=next<end?next:end;
    } return true;
}
static bool Readable(DWORD address,MEMORY_BASIC_INFORMATION& m) {
    if(!address || !VirtualQuery(reinterpret_cast<void*>(address),&m,sizeof(m)))return false;
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
static bool PhysicsGuard(unsigned g) {
    for(unsigned i=0;i<physicsCount;++i)if(g==physicsRefs[i].guard || g==physicsRefs[i].guard+1)return true;
    return false;
}

static const char* Check(bool tolerant=false) {
    if(GetCurrentThreadId()!=threadId)return "thread different";
    if(Read(base+0xFCE790)!=manager || Read(reinterpret_cast<void*>(manager+8))!=2 ||
       Read(reinterpret_cast<void*>(manager+0xC))!=reinterpret_cast<DWORD>(reader))return "lecteur de replay different";
    if(Read(base+0x1087A4C)!=4)return "pas en combat";
    for(unsigned i=0;i<guardCount;++i){
        if(tolerant && PhysicsGuard(i))continue;
        BYTE b[32];if(!Copy(b,guards[i].address,guards[i].size)||memcmp(b,guards[i].bytes,guards[i].size))return "garde modifiee";
    }
    for(unsigned i=0;i<count;++i)if(!skip[i] && !Writable(ranges[i].address,ranges[i].size))return "plage non inscriptible";
    if(!AnimationCheck())return "selecteurs d'animation incoherents";
    if(!CheckChannels())return "donnees de mouvement dechargees";
    return nullptr;
}
static bool ReadAll(BYTE* dest) {
    for(unsigned i=0;i<count;++i)if(!Copy(dest+ranges[i].offset,ranges[i].address,ranges[i].size))return false;
    return true;
}
static bool WriteAll(const BYTE* src) {
    RT_TRY {for(unsigned i=0;i<count;++i)if(!skip[i])memcpy(ranges[i].address,src+ranges[i].offset,ranges[i].size);return true;}
    RT_EXCEPT{return false;}
}
static bool SameAsSaved(const BYTE* now) {
    for(unsigned i=0;i<count;++i)if(!skip[i] && memcmp(now+ranges[i].offset,saved+ranges[i].offset,ranges[i].size))return false;
    return true;
}
static void Release() {
    if(saved)HeapFree(GetProcessHeap(),0,saved);
    saved=scratch=nullptr;
    count=guardCount=cursorCount=physicsCount=0;total=0;animation[0]=animation[1]=nullptr;InterlockedExchange(&active,0);
    memset(skip,0,sizeof(skip));decorStale=false;
}

struct Component { DWORD address,stamp; };
static Component components[64];
static void NoteComponent(DWORD address) {
    unsigned oldest=0;
    for(unsigned i=0;i<64;++i){if(components[i].address==address){components[i].stamp=frontierCount;return;}if(components[i].stamp<components[oldest].stamp)oldest=i;}
    components[oldest]={address,frontierCount};
}
struct MemoryStream { DWORD vtable; BYTE* buffer; DWORD size,position; };
struct Archive { MemoryStream* stream; BYTE owns,accumulator,mask,pad; };
typedef void(__cdecl* Serialize)(DWORD owner,Archive* archive);
typedef void(__cdecl* Apply)(DWORD owner);
typedef void(__fastcall* Flush)(Archive* archive,void* unused);
struct StageState { DWORD component,owner,descriptor,length; BYTE data[0x200]; DWORD ownerTag; };
static StageState stageStates[64]; static unsigned stageCount;
static bool OwnerAlive(const StageState& st);
static BYTE stageScratch[0x1000];
static bool InText(DWORD v){return v>=reinterpret_cast<DWORD>(base)+0x1000 && v<reinterpret_cast<DWORD>(base)+0x966000;}
static bool InRdata(DWORD v){return v>=reinterpret_cast<DWORD>(base)+0x966000 && v<reinterpret_cast<DWORD>(base)+0xCB3000;}
static bool Describe(DWORD component,DWORD& owner,DWORD& descriptor) {
    owner=Read(reinterpret_cast<void*>(component));descriptor=Read(reinterpret_cast<void*>(component+4));
    return owner && InRdata(descriptor) && InText(Read(reinterpret_cast<void*>(descriptor))) &&
        InText(Read(reinterpret_cast<void*>(descriptor+4)));
}
static bool CallSave(DWORD owner,DWORD descriptor,MemoryStream* s) {
    RT_TRY {
        Archive a={s,1,0,1,0};
        reinterpret_cast<Serialize>(Read(reinterpret_cast<void*>(descriptor+4)))(owner,&a);
        reinterpret_cast<Flush>(base+0x59EBC0)(&a,nullptr);
        return true;
    } RT_EXCEPT{return false;}
}
static DWORD loadOnlyOwner;
static bool CallLoad(DWORD owner,DWORD descriptor,MemoryStream* s) {
    RT_TRY {
        Archive a={s,1,0,1,0};
        reinterpret_cast<Serialize>(Read(reinterpret_cast<void*>(descriptor)))(owner,&a);
        DWORD apply=Read(reinterpret_cast<void*>(descriptor+8));
        if(owner!=loadOnlyOwner && InText(apply))reinterpret_cast<Apply>(apply)(owner);
        return true;
    } RT_EXCEPT{return false;}
}

struct StageRaw { DWORD owner,size; BYTE data[0x1400]; };
static StageRaw stageRaws[8]; static unsigned stageRawCount;
static bool FlagWord(DWORD v){return !(v&0xFEFEFEFEu);}
static DWORD RecordedSize(DWORD address);
static void StageRawSave(DWORD owner) {
    for(unsigned i=0;i<stageRawCount;++i)if(stageRaws[i].owner==owner)return;
    if(stageRawCount>=8)return;
    MEMORY_BASIC_INFORMATION mb={};if(!VirtualQuery(reinterpret_cast<void*>(owner),&mb,sizeof(mb)) || mb.State!=MEM_COMMIT)return;
    const DWORD end=reinterpret_cast<DWORD>(mb.BaseAddress)+static_cast<DWORD>(mb.RegionSize);
    DWORD size=RecordedSize(owner);if(!size || size>sizeof(stageRaws[0].data))size=sizeof(stageRaws[0].data);if(size>end-owner)size=end-owner;size&=~3u;
    StageRaw& r=stageRaws[stageRawCount];r.owner=owner;r.size=size;
    if(size && Copy(r.data,reinterpret_cast<void*>(owner),size))++stageRawCount;
}
static DWORD StageRawFlags() {
    DWORD n=0;
    for(unsigned i=0;i<stageRawCount;++i) {
        const StageRaw& r=stageRaws[i];bool alive=false;
        for(unsigned k=0;k<stageCount;++k)if(stageStates[k].owner==r.owner){DWORD o=0,d=0;alive=Describe(stageStates[k].component,o,d) && o==r.owner && OwnerAlive(stageStates[k]);break;}
        if(!alive)continue;
        for(DWORD k=0;k<r.size;k+=4) {
            DWORD old=0,now=0;memcpy(&old,r.data+k,4);
            if(!Copy(&now,reinterpret_cast<void*>(r.owner+k),4) || now==old || !FlagWord(old) || !FlagWord(now))continue;
            bool fault=false;
            RT_TRY{*reinterpret_cast<DWORD*>(r.owner+k)=old;++n;}RT_EXCEPT{fault=true;}
            if(fault)break;
        }
    }
    return n;
}
static void StageSave() {
    stageCount=0;stageRawCount=0;
    for(const Component& c:components) {
        if(!c.address || stageCount>=64)continue;
        DWORD owner,descriptor;if(!Describe(c.address,owner,descriptor) || !InRdata(Read(reinterpret_cast<void*>(owner))))continue;
        MemoryStream s={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,sizeof(stageScratch),0};
        memset(stageScratch,0,sizeof(stageScratch));
        if(!CallSave(owner,descriptor,&s) || s.position>sizeof(stageStates[0].data))continue;
        StageState& st=stageStates[stageCount++];
        st.component=c.address;st.owner=owner;st.descriptor=descriptor;st.length=s.position;memcpy(st.data,stageScratch,s.position);
        StageRawSave(owner);
    }
}

static char stageChangedList[160]; static bool homeStateChanged; static bool stageChanged[64];
static bool PointerLike(DWORD v);

static DWORD rawSkipDescriptor;

static bool FsmIndexWord(DWORD owner,DWORD k,DWORD old,DWORD now) {
    if(k<8)return false;
    const DWORD table=Read(reinterpret_cast<void*>(owner+k-8)),states=Read(reinterpret_cast<void*>(owner+k-4));
    if(!states || states>64 || !PointerLike(table))return false;
    const LONG o=static_cast<LONG>(old),w=static_cast<LONG>(now);
    if(o<-1 || o>=static_cast<LONG>(states) || w<-1 || w>=static_cast<LONG>(states))return false;
    return true;
}
static void StageRawRestoreChanged() {
    for(unsigned i=0;i<stageRawCount;++i) {
        const StageRaw& r=stageRaws[i];bool changed=false;
        for(unsigned k=0;k<stageCount;++k)if(stageStates[k].owner==r.owner && stageChanged[k]){DWORD o=0,d=0;changed=Describe(stageStates[k].component,o,d) && o==r.owner && (!rawSkipDescriptor || d!=rawSkipDescriptor);break;}
        if(!changed)continue;
        char l[400];int n=sprintf_s(l,"Point de controle : bloc du decor %08lX remis :",r.owner);unsigned words=0;
        for(DWORD k=0;k<r.size;k+=4) {
            DWORD old=0,now=0;memcpy(&old,r.data+k,4);
            if(!Copy(&now,reinterpret_cast<void*>(r.owner+k),4) || now==old || PointerLike(old) || PointerLike(now))continue;
            if(FsmIndexWord(r.owner,k,old,now)){Logf("Point de controle : bloc %08lX +%lX : index d'automate laisse (%ld, point %ld).",r.owner,k,static_cast<long>(now),static_cast<long>(old));continue;}
            bool fault=false;
            RT_TRY{*reinterpret_cast<DWORD*>(r.owner+k)=old;}RT_EXCEPT{fault=true;}
            if(fault)break;
            if(++words<=10 && n<360)n+=sprintf_s(l+n,sizeof(l)-n," +%lX %lX>%lX",k,now,old);
        }
        if(words){if(n<380)sprintf_s(l+n,sizeof(l)-n," (%u mots)",words);Log(l);}
    }
}
static unsigned StageChanges() {
    unsigned n=0;int len=0;stageChangedList[0]=0;homeStateChanged=false;memset(stageChanged,0,sizeof(stageChanged));
    for(unsigned i=0;i<stageCount;++i) {
        const StageState& st=stageStates[i];DWORD owner,descriptor;
        if(!Describe(st.component,owner,descriptor) || owner!=st.owner || descriptor!=st.descriptor)continue;
        MemoryStream s={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,sizeof(stageScratch),0};
        memset(stageScratch,0,sizeof(stageScratch));
        if(!CallSave(owner,descriptor,&s))continue;
        if(s.position!=st.length || memcmp(stageScratch,st.data,st.length)) {
            ++n;stageChanged[i]=true;
            if(descriptor==reinterpret_cast<DWORD>(base)+0xBF1548)homeStateChanged=true;
            if(len<140)len+=sprintf_s(stageChangedList+len,sizeof(stageChangedList)-len," %06lX",descriptor-reinterpret_cast<DWORD>(base));
        }
    }
    return n;
}

static bool HomeStage() {
    for(unsigned i=0;i<stageCount;++i)if(stageStates[i].descriptor==reinterpret_cast<DWORD>(base)+0xBF1548)return true;
    return false;
}

static bool diagEnabled;
static DWORD HeapTag(DWORD address);

struct FsmSeen { DWORD owner,offset,index,object; };
static FsmSeen fsmPoint[96]; static unsigned fsmPointCount;
static unsigned FsmScan(DWORD owner,DWORD size,FsmSeen* out,unsigned max) {
    unsigned n=0;
    for(DWORD o=0;o+0x18<=size && n<max;o+=4) {
        DWORD w[5];if(!Copy(w,reinterpret_cast<void*>(owner+o+4),20))continue;
        const DWORD table=w[0],states=w[1],index=w[2],object=w[3];
        if(!table || (table&3) || states<1 || states>64 || !(index<states || index==0xFFFFFFFFu))continue;

        DWORD cls=0,fc=0,fd=0;
        if(!Copy(&cls,reinterpret_cast<void*>(table+4),4) || !cls || !Copy(&fc,reinterpret_cast<void*>(cls+4),4) || !Copy(&fd,reinterpret_cast<void*>(cls+8),4))continue;
        if(!InText(fc) || !InText(fd))continue;
        out[n++]={owner,o,index,object};o+=0x14;
    }
    return n;
}

static void HexLine(char* l,size_t size,int& n,DWORD address,DWORD bytes) {
    DWORD w[52]={};if(bytes>sizeof(w))bytes=sizeof(w);
    if(!address || !Copy(w,reinterpret_cast<void*>(address),bytes)){n+=sprintf_s(l+n,size-n," (illisible)");return;}
    for(DWORD k=0;k<bytes/4 && n<static_cast<int>(size)-12;++k)n+=sprintf_s(l+n,size-n," %08lX",w[k]);
}
static DWORD HzOwner() {
    for(unsigned i=0;i<stageCount;++i)if(stageStates[i].descriptor==reinterpret_cast<DWORD>(base)+0xBEC17C)return stageStates[i].owner;
    return 0;
}
static void HzGroupDump(DWORD owner,const char* when) {
    if(!diagEnabled || !owner)return;
    const DWORD group=Read(reinterpret_cast<void*>(owner+0x188)),res=Read(reinterpret_cast<void*>(owner+0x2C));
    char l[700];int n=sprintf_s(l,"Diag groupe Hot Zone %s : etat %lu etape %lu ; groupe %08lX +00..+3B :",when,Read(reinterpret_cast<void*>(owner+0x17C)),Read(reinterpret_cast<void*>(owner+0x1C8)),group);
    HexLine(l,sizeof(l),n,group,0x3C);Log(l);
    n=sprintf_s(l,"Diag groupe Hot Zone %s : parties +3C..+CB :",when);HexLine(l,sizeof(l),n,group?group+0x3C:0,0x90);Log(l);
    if(!res)return;
    static const DWORD slots[]={0x74,0x90,0x94,0x268};
    for(DWORD o:slots) {
        const DWORD node=Read(reinterpret_cast<void*>(res+o));
        n=sprintf_s(l,"Diag noeud Hot Zone %s : +%lX = %08lX :",when,o,node);HexLine(l,sizeof(l),n,node,o==0x94?0x80:0x40);Log(l);
        const DWORD shape=node?Read(reinterpret_cast<void*>(node+0x1C)):0;
        n=sprintf_s(l,"Diag forme Hot Zone %s : +%lX forme %08lX :",when,o,shape);HexLine(l,sizeof(l),n,shape,0x60);
        DWORD link=shape?Read(reinterpret_cast<void*>(shape+8)):0;
        for(int k=0;k<4 && link && n<620;++k){DWORD w[4]={};Copy(w,reinterpret_cast<void*>(link),16);n+=sprintf_s(l+n,sizeof(l)-n," | lien %08lX : %08lX %08lX %08lX %08lX",link,w[0],w[1],w[2],w[3]);link=w[0];}
        Log(l);
    }
}

struct HzFlag { DWORD entry,word,offset; };
static HzFlag hzFlags[256]; static unsigned hzFlagCount;
static void HzFlagsSave(DWORD owner) {
    hzFlagCount=0;if(!owner)return;
    const DWORD res=Read(reinterpret_cast<void*>(owner+0x2C));if(!res)return;
    for(DWORD o=0;o<0x400 && hzFlagCount<256;o+=4) {
        const DWORD node=Read(reinterpret_cast<void*>(res+o));
        if(node<0x10000 || Read(reinterpret_cast<void*>(node+0x10))!=node)continue;
        const DWORD entry=Read(reinterpret_cast<void*>(node+0x1C));
        if(entry<0x10000 || Read(reinterpret_cast<void*>(entry))!=node)continue;
        bool dup=false;for(unsigned k=0;k<hzFlagCount;++k)if(hzFlags[k].entry==entry)dup=true;
        if(!dup)hzFlags[hzFlagCount++]={entry,Read(reinterpret_cast<void*>(entry+0xC)),o};
    }
}
static void HzFlagsRestore(bool write) {
    char l[900];int n=sprintf_s(l,"Point de controle : Hot Zone : drapeaux des noeuds (%u entrees) :",hzFlagCount);unsigned fixed=0;
    for(unsigned k=0;k<hzFlagCount;++k) {
        const DWORD cur=Read(reinterpret_cast<void*>(hzFlags[k].entry+0xC));
        if(cur==hzFlags[k].word || (cur&0xFFFFFF)!=(hzFlags[k].word&0xFFFFFF))continue;
        bool ok=true;if(write){RT_TRY{*reinterpret_cast<volatile DWORD*>(hzFlags[k].entry+0xC)=hzFlags[k].word;}RT_EXCEPT{ok=false;}}
        ++fixed;if(n<860)n+=sprintf_s(l+n,sizeof(l)-n," +%lX(id %08lX) %08lX>%08lX%s",hzFlags[k].offset,Read(reinterpret_cast<void*>(Read(reinterpret_cast<void*>(hzFlags[k].entry)))),cur,hzFlags[k].word,ok?"":"!");
    }
    if(!fixed)sprintf_s(l+n,sizeof(l)-n," aucun change.");
    Log(l);
}
static DWORD hzLastState=0xFFFFFFFFu;
static void HzWatch() {
    if(!diagEnabled)return;
    const DWORD owner=HzOwner();if(!owner)return;
    const DWORD state=Read(reinterpret_cast<void*>(owner+0x17C));
    if(state==hzLastState)return;
    char when[48];sprintf_s(when,"etat %lu -> %lu",hzLastState,state);hzLastState=state;
    HzGroupDump(owner,when);
}
static void FsmSpySave() {
    fsmPointCount=0;if(!diagEnabled)return;
    for(unsigned i=0;i<stageCount;++i) {
        if(stageStates[i].descriptor!=reinterpret_cast<DWORD>(base)+0xBEC17C)continue;
        DWORD size=RecordedSize(stageStates[i].owner);if(!size || size>0x4000)size=0x2000;
        fsmPointCount+=FsmScan(stageStates[i].owner,size,fsmPoint+fsmPointCount,96-fsmPointCount);
        static const DWORD known[]={0x208,0x4E4,0x5B4,0x93C,0x1BD4,0x1C0C,0x1C44,0x1C8C};
        for(DWORD k:known){DWORD w[6]={};Copy(w,reinterpret_cast<void*>(stageStates[i].owner+k-0xC),24);DWORD cls=0;if(w[1])Copy(&cls,reinterpret_cast<void*>(w[1]+4),4);
            Logf("Diag automate +%lX : +0 %08lX table %08lX nb %lu index %ld objet %08lX occupe %02lX ; classe0 %08lX",k-0xC,w[0],w[1],w[2],static_cast<long>(w[3]),w[4],w[5]&0xFF,cls);}
    }
    char l[480];int n=sprintf_s(l,"Diag automates au point : %u",fsmPointCount);
    for(unsigned k=0;k<fsmPointCount && n<440;++k)n+=sprintf_s(l+n,sizeof(l)-n," +%lX=%ld",fsmPoint[k].offset,static_cast<long>(fsmPoint[k].index));
    Log(l);
    HzGroupDump(HzOwner(),"au point");
}
static void FsmSpyCompare(const char* when) {
    if(!diagEnabled)return;
    HzGroupDump(HzOwner(),when);
    if(!fsmPointCount)return;
    char l[480];int n=sprintf_s(l,"Diag automates %s :",when);unsigned changed=0;
    for(unsigned k=0;k<fsmPointCount;++k) {
        DWORD idx=0,obj=0;Copy(&idx,reinterpret_cast<void*>(fsmPoint[k].owner+fsmPoint[k].offset+0xC),4);Copy(&obj,reinterpret_cast<void*>(fsmPoint[k].owner+fsmPoint[k].offset+0x10),4);
        if(idx==fsmPoint[k].index && obj==fsmPoint[k].object)continue;
        ++changed;if(n<440)n+=sprintf_s(l+n,sizeof(l)-n," +%lX %ld>%ld%s",fsmPoint[k].offset,static_cast<long>(fsmPoint[k].index),static_cast<long>(idx),obj!=fsmPoint[k].object?"*":"");
    }
    if(n<460)sprintf_s(l+n,sizeof(l)-n," (%u change(s) ; * = objet d'etat remplace)",changed);
    Log(l);
}

static bool OwnerAlive(const StageState& st){return !st.ownerTag || HeapTag(st.owner)==st.ownerTag;}
static void StageLoad() {
    for(unsigned i=0;i<stageCount;++i) {
        StageState& st=stageStates[i];DWORD owner,descriptor;
        if(!Describe(st.component,owner,descriptor) || owner!=st.owner || descriptor!=st.descriptor)continue;
        if(!OwnerAlive(st))continue;
        memcpy(stageScratch,st.data,st.length);memset(stageScratch+st.length,0,16);
        MemoryStream s={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,st.length+16,0};
        CallLoad(owner,descriptor,&s);
    }
}

struct Allocation { DWORD address,size; };
static Allocation* allocations; static constexpr DWORD allocationSlots=1u<<19; static SRWLOCK allocationLock=SRWLOCK_INIT;
static void RecordAllocation(DWORD address,DWORD size) {
    if(!address || !allocations)return;
    AcquireSRWLockExclusive(&allocationLock);
    DWORD h=(address>>3)*2654435761u;
    for(DWORD i=0;i<64;++i){Allocation& a=allocations[(h+i)&(allocationSlots-1)];if(!a.address||a.address==address){a.address=address;a.size=size;break;}}
    ReleaseSRWLockExclusive(&allocationLock);
}
static DWORD RecordedSize(DWORD address) {
    if(!allocations)return 0;
    AcquireSRWLockShared(&allocationLock);DWORD size=0,h=(address>>3)*2654435761u;
    for(DWORD i=0;i<64;++i){const Allocation& a=allocations[(h+i)&(allocationSlots-1)];if(!a.address)break;if(a.address==address){size=a.size;break;}}
    ReleaseSRWLockShared(&allocationLock);return size;
}
struct Region { DWORD start,end; };
static Region regions[16384]; static unsigned regionCount;
struct Block { DWORD address,size,offset; WORD depth; bool bounded; DWORD heapTag; };

static DWORD stageHeapStart,stageHeapEnd;
static void StageHeapFind() {
    stageHeapStart=stageHeapEnd=0;
    const DWORD d=reinterpret_cast<DWORD>(base)+0x2066D50;
    if(Read(reinterpret_cast<void*>(d))!=reinterpret_cast<DWORD>(base)+0xC1262C || Read(reinterpret_cast<void*>(d+0xC))!=0x10)return;
    const DWORD s0=Read(reinterpret_cast<void*>(d+0x10)),e0=Read(reinterpret_cast<void*>(d+0x18));
    if(s0 && e0>s0){stageHeapStart=s0;stageHeapEnd=e0;}
}
static DWORD HeapTag(DWORD address) {
    if(!stageHeapStart || address<stageHeapStart+0x10 || address>=stageHeapEnd)return 0;
    DWORD v=0;Copy(&v,reinterpret_cast<void*>(address-0xC),4);return v;
}
static void StageTagOwners() {
    for(unsigned i=0;i<stageCount;++i){const DWORD t=HeapTag(stageStates[i].owner);stageStates[i].ownerTag=(t&0x80000000u)?t:0;}
}

static unsigned rebindPending,rebindFrames;
static unsigned RebindRecreated(bool logIt) {
    unsigned done=0;
    for(unsigned i=0;i<stageCount;++i) {
        StageState& st=stageStates[i];
        if(!(rebindPending&(1u<<(i&31))))continue;
        for(const Component& c:components) {
            DWORD o=0,d=0;if(!c.address || c.address==st.component || !Describe(c.address,o,d) || d!=st.descriptor || o==st.owner)continue;
            const DWORD t=HeapTag(o);if(!(t&0x80000000u))continue;
            memcpy(stageScratch,st.data,st.length);memset(stageScratch+st.length,0,16);
            MemoryStream ms={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,st.length+16,0};
            const bool ok=CallLoad(o,d,&ms);
            if(logIt || true)Logf("Point de controle : composant %06lX recree par la reconstruction (%08lX -> %08lX) : etat du point charge%s.",d-reinterpret_cast<DWORD>(base),st.owner,o,ok?"":" (ECHEC)");
            st.component=c.address;st.owner=o;st.ownerTag=t;rebindPending&=~(1u<<(i&31));++done;break;
        }
    }
    return done;
}
static constexpr unsigned maxBlocks=8000,stableFrames=10;
static constexpr DWORD maxBlockBytes=8*1024*1024,pageStart=0x1070000,pageCount=16;
static Block blocks[maxBlocks]; static unsigned blockCount; static DWORD blockBytes;
static DWORD blockSet[32768];
static BYTE *blockSaved,*pageSaved; static DWORD *blockHashes,*pageHashes;
static unsigned hashedFrames;
static void ScanRegions() {
    regionCount=0;DWORD a=0x10000;
    while(regionCount<16384) {
        MEMORY_BASIC_INFORMATION m={};if(!VirtualQuery(reinterpret_cast<void*>(a),&m,sizeof(m)))break;
        DWORD s=reinterpret_cast<DWORD>(m.BaseAddress),e=s+static_cast<DWORD>(m.RegionSize);
        if(m.State==MEM_COMMIT && m.Type==MEM_PRIVATE && !(m.Protect&PAGE_GUARD) && (m.Protect&0xFF)==PAGE_READWRITE)regions[regionCount++]={s,e};
        if(e<=a)break;a=e;
    }
}
static bool HeapPointer(DWORD v,DWORD& regionEnd) {
    if(v&3)return false;
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
static void AddBlock(DWORD address,WORD depth) {
    DWORD regionEnd=0;
    if(blockCount>=maxBlocks || !HeapPointer(address,regionEnd))return;
    DWORD h=(address>>2)*2654435761u;bool inserted=false;
    for(unsigned i=0;i<32768;++i){DWORD& slot=blockSet[(h+i)&32767];if(slot==address)return;if(!slot){slot=address;inserted=true;break;}}
    if(!inserted)return;
    DWORD size=depth?0x800:0x2000;if(size>regionEnd-address)size=regionEnd-address;
    DWORD exact=RecordedSize(address);if(exact && exact<size)size=exact;size&=~3u;
    if(!size || blockBytes+size>maxBlockBytes)return;
    blocks[blockCount++]={address,size,blockBytes,depth,exact!=0,0};blockBytes+=size;
}
static DWORD FastHash(const void* p,DWORD n) {
    DWORD h=0x9E3779B9;
    RT_TRY{const DWORD* d=static_cast<const DWORD*>(p);for(DWORD i=0;i<n/4;++i){h^=d[i];h=(h<<5)|(h>>27);h*=0x01000193;}}
    RT_EXCEPT{return 0xDEADDEAD;}
    return h;
}
static void DecorBuild() {
    hashedFrames=0;
    if(!blockSaved)blockSaved=static_cast<BYTE*>(VirtualAlloc(nullptr,maxBlockBytes+pageCount*0x1000,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!blockHashes)blockHashes=static_cast<DWORD*>(VirtualAlloc(nullptr,(maxBlocks+pageCount)*(stableFrames+1)*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!blockSaved || !blockHashes){blockCount=0;return;}
    pageSaved=blockSaved+maxBlockBytes;pageHashes=blockHashes+maxBlocks*(stableFrames+1);
    memset(blockSet,0,sizeof(blockSet));blockCount=0;blockBytes=0;ScanRegions();
    AddBlock(Read(base+0x2072580),0);
    for(const Component& c:components)if(c.address)AddBlock(Read(reinterpret_cast<void*>(c.address)),0);
    for(unsigned i=0;i<blockCount;++i) {
        if(blocks[i].depth>=3)continue;
        for(DWORD o=0;o+4<=blocks[i].size;o+=4)AddBlock(Read(reinterpret_cast<void*>(blocks[i].address+o)),static_cast<WORD>(blocks[i].depth+1));
    }
    for(unsigned i=0;i<blockCount;++i)Copy(blockSaved+blocks[i].offset,reinterpret_cast<void*>(blocks[i].address),blocks[i].size);
    StageHeapFind();
    for(unsigned i=0;i<blockCount;++i) {
        const DWORD tag=blocks[i].bounded?HeapTag(blocks[i].address):0;
        const DWORD bytes=0u-tag;
        blocks[i].heapTag=((tag&0x80000000u) && bytes>=blocks[i].size && bytes<=blocks[i].size+0x40)?tag:0;
    }
    Copy(pageSaved,base+pageStart,pageCount*0x1000);
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
    DWORD written=0;unsigned fsmKept=0;
    for(unsigned i=0;i<blockCount;++i) {
        bool stable=true;for(DWORD k=1;k<=stableFrames;++k)if(blockHashes[k*maxBlocks+i]!=blockHashes[i]){stable=false;break;}
        const Block& b=blocks[i];
        if(!stable || !b.bounded)continue;
        DWORD typeNow=0,typeThen=0;memcpy(&typeThen,blockSaved+b.offset,4);
        if(!Copy(&typeNow,reinterpret_cast<void*>(b.address),4) || typeNow!=typeThen)continue;
        if(b.heapTag && HeapTag(b.address)!=b.heapTag)continue;
        for(DWORD k=0;k+4<=b.size;k+=4) {
            DWORD old=0,now=0;memcpy(&old,blockSaved+b.offset+k,4);
            if(!Copy(&now,reinterpret_cast<void*>(b.address+k),4) || now==old || PointerLike(old) || PointerLike(now))continue;
            if(FsmIndexWord(b.address,k,old,now)){++fsmKept;continue;}
            RT_TRY{*reinterpret_cast<DWORD*>(b.address+k)=old;written+=4;}RT_EXCEPT{}
        }
    }
    for(unsigned i=0;i<pageCount;++i) {
        bool stable=true;for(DWORD k=1;k<=stableFrames;++k)if(pageHashes[k*pageCount+i]!=pageHashes[i]){stable=false;break;}
        if(!stable)continue;
        for(DWORD k=0;k<0x1000;k+=4) {
            DWORD old=0,now=0;memcpy(&old,pageSaved+i*0x1000+k,4);Copy(&now,base+pageStart+i*0x1000+k,4);
            if(now==old || PointerLike(old) || PointerLike(now))continue;
            RT_TRY{*reinterpret_cast<DWORD*>(base+pageStart+i*0x1000+k)=old;written+=4;}RT_EXCEPT{}
        }
    }
    if(written || fsmKept)Logf("Point de controle : decor remis (%lu octets ; %u index d'automate laisse(s)).",written,fsmKept);
}

static void DecorDiff(const char* when) {
    if(!diagEnabled || !blockHashes || hashedFrames<=stableFrames)return;
    unsigned objects=0,lines=0;DWORD words=0,ptrs=0;
    for(unsigned i=0;i<blockCount;++i) {
        bool stable=true;for(DWORD k=1;k<=stableFrames;++k)if(blockHashes[k*maxBlocks+i]!=blockHashes[i]){stable=false;break;}
        const Block& b=blocks[i];
        if(!stable)continue;
        DWORD typeThen=0,typeNow=0;memcpy(&typeThen,blockSaved+b.offset,4);
        if(!Copy(&typeNow,reinterpret_cast<void*>(b.address),4) || typeNow!=typeThen)continue;
        unsigned w=0,p=0;char l[420];int n=0;
        for(DWORD k=0;k+4<=b.size;k+=4) {
            DWORD old=0,now=0;memcpy(&old,blockSaved+b.offset+k,4);
            if(!Copy(&now,reinterpret_cast<void*>(b.address+k),4) || now==old)continue;
            const bool ptr=PointerLike(old) || PointerLike(now);
            if(ptr)++p;else ++w;
            if(w+p==1)n=sprintf_s(l,"Diag decor %s : %08lX (prof. %u, %lu o, type %08lX) :",when,b.address,b.depth,b.size,InRdata(typeThen)?typeThen-reinterpret_cast<DWORD>(base):typeThen);
            if(w+p<=8 && n<360)n+=sprintf_s(l+n,sizeof(l)-n," +%lX %08lX>%08lX%s",k,old,now,ptr?"*":"");
        }
        if(!w && !p)continue;
        ++objects;words+=w;ptrs+=p;
        if(lines<30){if(n<400)sprintf_s(l+n,sizeof(l)-n," (%u mots, %u pointeurs)",w,p);Log(l);++lines;}
    }
    Logf("Diag decor %s : %u objet(s) stable(s) different(s) du point (%lu mots, %lu pointeurs).",when,objects,words,ptrs);
}

struct DiagObj { DWORD src,ptr,size,offset; };
static DiagObj diagObjs[512]; static unsigned diagCount; static BYTE* diagBuf; static DWORD diagBytes;
static void DiagSave() {
    diagCount=0;diagBytes=0;
    if(!diagEnabled)return;
    if(!diagBuf)diagBuf=static_cast<BYTE*>(VirtualAlloc(nullptr,8u<<20,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!diagBuf)return;
    ScanRegions();
    static const DWORD srcs[3][2]={{0xFD0540,0xD90},{0xFCF788,0xD90},{0xFCEE78,0x910}};
    for(const auto& s:srcs)for(DWORD o=0;o+4<=s[1];o+=4) {
        const DWORD v=Read(base+s[0]+o);DWORD regionEnd=0;
        if(diagCount>=512 || !HeapPointer(v,regionEnd))continue;
        bool dup=false;for(unsigned i=0;i<diagCount;++i)if(diagObjs[i].ptr==v){dup=true;break;}
        if(dup)continue;
        DWORD size=RecordedSize(v);if(!size)size=0x400;if(size>0x10000)size=0x10000;if(size>regionEnd-v)size=regionEnd-v;
        if(diagBytes+size>(8u<<20))break;
        if(!Copy(diagBuf+diagBytes,reinterpret_cast<void*>(v),size))continue;
        diagObjs[diagCount++]={s[0]+o,v,size,diagBytes};diagBytes+=size;
    }
    Logf("Diag tas : %u objets pointes par les joueurs copies au point (%lu octets).",diagCount,diagBytes);
}
static void DiagCompare() {
    if(!diagEnabled || !diagCount)return;
    unsigned lines=0,changed=0;
    for(unsigned i=0;i<diagCount && lines<80;++i) {
        const DiagObj& d=diagObjs[i];BYTE now[0x400];unsigned diff=0;char l[400];int n=0;
        for(DWORD o=0;o<d.size;o+=sizeof(now)) {
            const DWORD part=d.size-o<sizeof(now)?d.size-o:static_cast<DWORD>(sizeof(now));
            if(!Copy(now,reinterpret_cast<void*>(d.ptr+o),part))break;
            for(DWORD k=0;k<part;++k)if(now[k]!=diagBuf[d.offset+o+k]) {
                if(!diff)n=sprintf_s(l,"Diag tas : objet %08lX (RVA %06lX, %lu o) :",d.ptr,d.src,d.size);
                if(++diff<=12 && n<340)n+=sprintf_s(l+n,sizeof(l)-n," +%lX %02X>%02X",o+k,diagBuf[d.offset+o+k],now[k]);
            }
        }
        if(diff){++changed;if(n<380)sprintf_s(l+n,sizeof(l)-n," (%u octets)",diff);Log(l);++lines;}
    }
    Logf("Diag tas : %u objet(s) sur %u pas revenus a l'etat du point.",changed,diagCount);
}

static DWORD compAtSave[64]; static unsigned compAtSaveCount;

static void ComponentSnapshot() {
    compAtSaveCount=0;
    for(const Component& c:components)if(c.address && compAtSaveCount<64)compAtSave[compAtSaveCount++]=c.address;
}
static unsigned NewComponents() {
    unsigned n=0;
    for(const Component& c:components) {
        if(!c.address || c.stamp+2<frontierCount)continue;
        bool old=false;for(unsigned i=0;i<compAtSaveCount;++i)if(compAtSave[i]==c.address){old=true;break;}
        if(!old)++n;
    }
    return n;
}

static unsigned lastFreed;

static bool TransientType(DWORD type) {
    if(type&3)return true;
    const DWORD col=Read(reinterpret_cast<void*>(type-4));
    if(!InRdata(col))return false;
    const DWORD td=Read(reinterpret_cast<void*>(col+12));
    if(td<reinterpret_cast<DWORD>(base)+0x966000 || td>=reinterpret_cast<DWORD>(base)+0x21F0000)return false;
    char name[96]={};if(!Copy(name,reinterpret_cast<void*>(td+8),sizeof(name)-1))return false;
    return strstr(name,"@TFlash@@")!=nullptr;
}
static unsigned DecorTypeChanges() {
    lastFreed=0;
    if(!blockSaved)return 0;unsigned n=0;

    unsigned freed=0,minor=0;
    for(unsigned i=0;i<blockCount;++i) {
        if(!blocks[i].heapTag || HeapTag(blocks[i].address)==blocks[i].heapTag)continue;
        DWORD type=0;memcpy(&type,blockSaved+blocks[i].offset,4);
        if(type==reinterpret_cast<DWORD>(base)+0x9C0BC8)continue;
        if(InRdata(type) && TransientType(type))continue;
        if(blocks[i].size<=0x80){++minor;continue;}
        ++n;++lastFreed;
        if(diagEnabled && ++freed<=8)Logf("Diag decor : objet %08lX (profondeur %u, %lu o, type %08lX) libere ou reutilise (en-tete %08lX -> %08lX).",
            blocks[i].address,blocks[i].depth,blocks[i].size,InRdata(type)?type-reinterpret_cast<DWORD>(base):type,blocks[i].heapTag,HeapTag(blocks[i].address));
    }
    if(diagEnabled && (minor || lastFreed))Logf("Diag decor : %u gros objet(s) et %u petit(s) objet(s) libere(s) depuis le point.",lastFreed,minor);
    for(unsigned i=0;i<blockCount;++i) {
        if(blocks[i].heapTag && HeapTag(blocks[i].address)!=blocks[i].heapTag)continue;
        DWORD then=0,now=0;memcpy(&then,blockSaved+blocks[i].offset,4);
        if(!InRdata(then))continue;

        if(then==reinterpret_cast<DWORD>(base)+0x9C0BC8)continue;

        if(then==reinterpret_cast<DWORD>(base)+0x96CCEC || then==reinterpret_cast<DWORD>(base)+0x96CC40)continue;
        if(TransientType(then))continue;
        if(!Copy(&now,reinterpret_cast<void*>(blocks[i].address),4) || now!=then) {
            ++n;
            if(diagEnabled && n<=6)Logf("Diag decor : objet %08lX (profondeur %u, %lu o) type %06lX -> %08lX.",blocks[i].address,blocks[i].depth,blocks[i].size,
                then-reinterpret_cast<DWORD>(base),InRdata(now)?now-reinterpret_cast<DWORD>(base):now);
        }
    }
    return n;
}

static bool rebuildAvailable;
static volatile LONG forceRebuild;
typedef DWORD(__cdecl* SceneFn)();
typedef void(__cdecl* RebuildFn)(DWORD);
typedef void(__cdecl* FinishFn)();

static DWORD sceneAtPoint=0xFF;
static DWORD CurrentScene(){return rebuildAvailable?reinterpret_cast<SceneFn>(base+0x5964C0)():0xFF;}
static bool RebuildScene(double& ms,DWORD n) {
    if(!rebuildAvailable)return false;
    if(n>1 || Read(base+0x2054540+n*0xA8+0x18)==0xFFFFFFFFu)return false;
    LARGE_INTEGER f,t0,t1;QueryPerformanceFrequency(&f);QueryPerformanceCounter(&t0);
    RT_TRY{reinterpret_cast<RebuildFn>(base+0x597AF0)(n);reinterpret_cast<FinishFn>(base+0x597B10)();}
    RT_EXCEPT{return false;}
    QueryPerformanceCounter(&t1);ms=double(t1.QuadPart-t0.QuadPart)*1000.0/double(f.QuadPart);
    return true;
}

static bool AddWindow(DWORD start,DWORD end,const char* name) {
    BYTE* a=base+start;BYTE* e=base+end;
    while(a<e) {
        BYTE* next=e;BYTE* covered=nullptr;
        for(unsigned i=0;i<count;++i) {
            BYTE* rs=ranges[i].address;BYTE* re=rs+ranges[i].size;
            if(re<=a || rs>=e)continue;
            if(rs<=a){if(re>covered)covered=re;}else if(rs<next)next=rs;
        }
        if(covered){a=covered;continue;}
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
static const char* Prepare(BYTE* r,DWORD m) {
    Release();
    if(RoundDecided())return "round deja termine (K.O. ou temps ecoule)";
    reader=r;manager=m;threadId=GetCurrentThreadId();
    if(!GuardAt(reader,0x20) || !GuardAt(reinterpret_cast<BYTE*>(m),0x18))return "en-tete lecteur";
    BYTE* stream=reinterpret_cast<BYTE*>(Read(reader+4));
    BYTE* wrapper=reinterpret_cast<BYTE*>(Read(reader+8));
    if(!stream || !wrapper || Read(wrapper)!=reinterpret_cast<DWORD>(stream) ||
       Read(stream)!=reinterpret_cast<DWORD>(base+0x9BA1F4) || Read(stream+12)>Read(stream+8) ||
       !GuardAt(stream,12) || !GuardAt(wrapper,4))return "flux du replay";

    if(!Add(base+0x1087AB0,0x9C8,"rng") || !Add(base+0xFD0540,0xD90,"players") ||
       !Add(base+0xFCEE78,0x910,"logic") || !Add(base+0x10878F8,0xB0,"slots") ||
       !Add(base+0xFCE99C,8,"feed_globals") || !Add(reader+0x20,0x74,"reader_scalars") ||
       !Add(reinterpret_cast<BYTE*>(m)+0x18,0x18,"manager_scalars") ||
       !Add(stream+12,4,"stream_cursor"))return "plages globales";
    if(!Add(base+0xFCF788,0xD90,"player_secondary"))return "plages globales";
    if(!Add(base+0xFCED68,0x68,"player_history_previous") || !Add(base+0xFCEDD8,0x68,"player_history_current"))return "plages globales";
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
    if(!PrepareAnimation())return "animation";
    for(unsigned player=0;player<2;++player)
        for(DWORD off:{0x10u,0x14u,0x1Cu,0x24u,0x34u})
            if(!Add(base+0xFCAB00+player*0x3C+off,4,"animation_time"))return "temps d'animation";
    if(!PrepareChannels())return "canaux d'animation";
    if(!Add(base+0xFCC214,4,"animation_advance_gate"))return "indicateur d'avancement";
    for(unsigned player=0;player<2;++player)
        if(!Add(base+0xFCBB00+player*0x180,12,"body_position"))return "position corps";
    for(const Seen& s:seen) {
        if(!s.object || s.stamp+2<frontierCount)continue;
        BYTE* p=reinterpret_cast<BYTE*>(s.object);
        const unsigned g=guardCount;
        if(!GuardAt(p+4,4) || !GuardAt(p+0x4C,8) || !Add(p,0x30C,"physics"))return "physique";
        if(physicsCount<8)physicsRefs[physicsCount++]={count-1,g};
    }
    if(!AddWindow(0xFCBAB0,0xFCBDB0,"w1_corps") || !AddWindow(0xFCA000,0xFCB700,"w2_mouvement") ||
       !AddWindow(0xFC7000,0xFCA000,"w3_blocs") || !AddWindow(0xFCC000,0xFD0540,"w4_globaux") ||
       !AddWindow(0xFB8000,0xFC0000,"w6_cameras"))return "fenetres statiques";
    saved=static_cast<BYTE*>(HeapAlloc(GetProcessHeap(),0,total*2));
    if(!saved){Release();return "memoire";}
    scratch=saved+total;
    const char* reason=Check();
    if(reason){Release();return reason;}
    if(!ReadAll(saved)){Release();return "lecture";}
    Copy(&savedClock,base+0x10885DA,1);
    return nullptr;
}
static void Drop(const char* reason) {
    if(!active)return;
    Logf("Point de controle abandonne : %s.",reason);
    Release();
}

static bool StageEvent() {
    DWORD a=0,b=0;Copy(&a,base+0xF9CB54,4);Copy(&b,base+0xF9CB58,4);return a||b;
}
static bool DoRestore(DWORD f) {
    if(StageEvent()) {
        Logf("Point de controle : sequence de stage en cours (cliffhanger, chute, vault...) : retour instantane refuse.");
        InterlockedExchange(&forceRebuild,0);return false;
    }
    const bool forced=InterlockedExchange(&forceRebuild,0)!=0;
    unsigned created=0,replaced=0,stateChanged=0;
    if(!decorStale){created=NewComponents();replaced=DecorTypeChanges();stateChanged=StageChanges();}
    const DWORD sceneNow=CurrentScene();
    const bool sceneChanged=sceneAtPoint<2 && sceneNow!=sceneAtPoint;

    struct SlowDanger { DWORD descriptor,first,end; };

    static const SlowDanger slowDangers[]={{0xBED5D8,0x1A4,0x1B4},{0x9818C8,0x194,0x198},{0xBEC17C,0x1D0,0x1D4},{0xBF4570,0x1A0,0x1A8},{0xBFEC80,0x1C8,0x1D4},{0x9AA22C,0x1E8,0x1EC},{0xBFB100,0x190,0x194},{0xBFB100,0x1AC,0x1B0},{0xBEC17C,0x1C4,0x1C8}};
    bool slowStage=false;

    bool sakuraInstant=false;

    bool hotzoneInstant=false,hotzoneSoft=false;
    auto hotzoneBarrelAtPoint=[&]()->DWORD {
        for(unsigned k=0;k<stageCount;++k) {
            if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+0xBEC17C)continue;
            for(unsigned r=0;r<stageRawCount;++r)
                if(stageRaws[r].owner==stageStates[k].owner && stageRaws[r].size>=0x1D4){DWORD v=0;memcpy(&v,stageRaws[r].data+0x1D0,4);return v;}
        }
        return 0xFFFFFFFFu;
    };

    auto hotzoneInstantOk=[&]()->bool {
        for(unsigned k=0;k<stageCount;++k) {
            if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+0xBEC17C)continue;
            for(unsigned r=0;r<stageRawCount;++r) {
                if(stageRaws[r].owner!=stageStates[k].owner || stageRaws[r].size<0x1E0)continue;
                const BYTE* d=stageRaws[r].data;DWORD state=0;memcpy(&state,d+0x17C,4);
                return (state==3 || state==4) && !d[0x1CF] && !d[0x1D5] && !d[0x1D7];
            }
        }
        return false;
    };
    auto sakuraIntactAtPoint=[&]()->bool {
        for(unsigned k=0;k<stageCount;++k) {
            if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+0x9AA22C)continue;
            for(unsigned r=0;r<stageRawCount;++r)
                if(stageRaws[r].owner==stageStates[k].owner && stageRaws[r].size>=0x1EC){DWORD v=0;memcpy(&v,stageRaws[r].data+0x1E8,4);return v==1;}
        }
        return false;
    };
    for(const SlowDanger& sd:slowDangers) for(unsigned k=0;k<stageCount;++k) {
        if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+sd.descriptor)continue;
        slowStage=true;
        if(!stateChanged || !stageChanged[k])continue;
        for(unsigned r=0;r<stageRawCount;++r) {
            if(stageRaws[r].owner!=stageStates[k].owner || sd.end>stageRaws[r].size)continue;
            for(DWORD o=sd.first;o<sd.end;o+=4) {
                DWORD then=0,now=0;memcpy(&then,stageRaws[r].data+o,4);
                if(Copy(&now,reinterpret_cast<void*>(stageRaws[r].owner+o),4) && now!=then) {
                    if(sd.descriptor==0x9AA22C && o==0x1E8 && then==1 && !created && replaced==lastFreed && !sceneChanged && !forced) {
                        Logf("Point de controle : banc de Sakura casse depuis le point (+1E8 %lX -> %lX) : reconstruction de la scene (comme HOME).",then,now);
                        sakuraInstant=true;continue;
                    }

                    if(sd.descriptor==0xBEC17C && o==0x1C4 && !sceneChanged && !forced && hotzoneInstantOk()) {
                      Logf("Point de controle : mur du tank de Hot Zone touche depuis le point (+1C4 %lX -> %lX) : reconstruction de la scene.",then,now);
                      hotzoneInstant=true;continue;
                    }
                    Logf("Point de controle : danger touche depuis le point (composant %06lX, +%lX %lX -> %lX) : retour instantane refuse, retour par rattrapage.",sd.descriptor,o,then,now);
                    return false;
                }
            }
        }
    }

    static const DWORD slowStates[]={0xBFEC80};
    bool templeInstant=false;
    auto templeTop=[&](bool checkNow)->bool {
        for(unsigned k=0;k<stageCount;++k) {
            if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+0xBFEC80)continue;
            DWORD o=0,d=0;if(checkNow && (!Describe(stageStates[k].component,o,d) || o!=stageStates[k].owner))return false;
            for(unsigned r=0;r<stageRawCount;++r) {
                if(stageRaws[r].owner!=stageStates[k].owner || stageRaws[r].size<0x1D4)continue;
                for(DWORD x=0x1C8;x<0x1D4;x+=4) {
                    DWORD then=0,now=0;memcpy(&then,stageRaws[r].data+x,4);if(then)return false;
                    if(checkNow && (!Copy(&now,reinterpret_cast<void*>(stageRaws[r].owner+x),4) || now))return false;
                }
                return true;
            }
        }
        return false;
    };
    if(stateChanged) for(DWORD d:slowStates) for(unsigned k=0;k<stageCount;++k) {
        if(!stageChanged[k] || stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+d)continue;

        if(!created && replaced==lastFreed && !sceneChanged && !forced && templeTop(true)) {
            Logf("Point de controle : objet cassable casse depuis le point (composant %06lX) : reconstruction de la scene (comme HOME).",d);
            templeInstant=true;break;
        }
        Logf("Point de controle : objet cassable casse depuis le point (composant %06lX) : retour instantane refuse, retour par rattrapage.",d);
        return false;
    }
    if(decorStale && !HomeStage() && templeTop(false)) {
        if(!templeTop(true)){Logf("Point de controle : etage change depuis la reconstruction : retour par rattrapage.");decorStale=false;return false;}
        templeInstant=true;
    }
    if(decorStale && !HomeStage() && !templeInstant && sakuraIntactAtPoint())sakuraInstant=true;
    if(decorStale && !HomeStage() && !templeInstant && hotzoneBarrelAtPoint()!=0xFFFFFFFFu && hotzoneInstantOk())hotzoneInstant=true;

    if(!hotzoneInstant && stateChanged && !sceneChanged && !forced && !HomeStage() && !templeInstant && !sakuraInstant)
        for(unsigned k=0;k<stageCount;++k) {
            if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+0xBEC17C || !stageChanged[k])continue;
            if(hotzoneInstantOk()) {
                Logf("Point de controle : etat de Hot Zone change depuis le point (apres le muret) : reconstruction de la scene.");
                hotzoneInstant=true;break;
            }
            for(unsigned r=0;r<stageRawCount;++r) {
                if(stageRaws[r].owner!=stageStates[k].owner || stageRaws[r].size<0x180)continue;
                DWORD then=0;memcpy(&then,stageRaws[r].data+0x17C,4);
                if(then==3 || then==4){Logf("Point de controle : Hot Zone apres le muret avec un danger deja parti au point : retour par rattrapage.");return false;}
            }

            Logf("Point de controle : etat de Hot Zone change depuis le point : retour par rattrapage (rechargement seul evite).");
            return false;
        }
    if(hotzoneInstant) {

        for(unsigned k=0;k<stageCount;++k) {
            if(stageStates[k].descriptor!=reinterpret_cast<DWORD>(base)+0xBEC17C)continue;
            for(unsigned r=0;r<stageRawCount;++r) {
                if(stageRaws[r].owner!=stageStates[k].owner || stageRaws[r].size<0x180)continue;
                DWORD then=0;memcpy(&then,stageRaws[r].data+0x17C,4);const DWORD now=Read(reinterpret_cast<void*>(stageRaws[r].owner+0x17C));
                if(then<5 && now>=5 && now<=6) {
                    Logf("Point de controle : tank de Hot Zone parti depuis le point (etat %lu -> %lu) : retour par rattrapage.",then,now);
                    decorStale=false;return false;
                }
            }
        }
    }
    const bool instantRebuild=templeInstant || sakuraInstant || hotzoneInstant;
    FsmSpyCompare("avant le retour");
    if(stateChanged && diagEnabled) for(unsigned r=0;r<stageRawCount;++r) {
        bool changed=false;for(unsigned k=0;k<stageCount;++k)if(stageStates[k].owner==stageRaws[r].owner && stageChanged[k])changed=true;
        if(!changed)continue;
        char l[480];int n=sprintf_s(l,"Diag decor avant rechargement %08lX (%lX octets) :",stageRaws[r].owner,stageRaws[r].size);unsigned w=0;
        for(DWORD o=0;o+4<=stageRaws[r].size;o+=4) {
            DWORD then=0,now=0;memcpy(&then,stageRaws[r].data+o,4);
            if(!Copy(&now,reinterpret_cast<void*>(stageRaws[r].owner+o),4) || now==then || PointerLike(then) || PointerLike(now))continue;

            if((then>0xFFFF && then<0xFFFF0000u) || (now>0xFFFF && now<0xFFFF0000u))continue;
            if(++w<=16 && n<440)n+=sprintf_s(l+n,sizeof(l)-n," +%lX %lX>%lX",o,then,now);
        }
        Log(l);
    }
    if(stateChanged && diagEnabled) for(unsigned k=0;k<stageCount;++k) {
        if(!stageChanged[k])continue;
        const StageState& st=stageStates[k];DWORD owner,descriptor;
        if(!Describe(st.component,owner,descriptor))continue;
        MemoryStream ms={reinterpret_cast<DWORD>(base)+0x9BA1F4,stageScratch,sizeof(stageScratch),0};
        memset(stageScratch,0,sizeof(stageScratch));
        if(!CallSave(owner,descriptor,&ms))continue;
        char l[480];int n=sprintf_s(l,"Diag etat serialise %06lX (%lu>%lu octets) :",descriptor-reinterpret_cast<DWORD>(base),st.length,ms.position);unsigned w=0;
        for(DWORD o=0;o<st.length && o<ms.position;++o) {
            if(stageScratch[o]==st.data[o])continue;
            if(++w<=24 && n<440)n+=sprintf_s(l+n,sizeof(l)-n," %lX:%02X>%02X",o,st.data[o],stageScratch[o]);
        }
        if(n<460)sprintf_s(l+n,sizeof(l)-n," (%u octets)",w);
        Log(l);
    }
    if(stateChanged)Logf("Point de controle : etat du decor change depuis le point (composants%s)%s.",stageChangedList,
        (homeStateChanged || instantRebuild)?"":" : recharge sans reconstruire la scene");
    const bool rebuild=forced || decorStale || created || replaced || (stateChanged && (homeStateChanged || instantRebuild)) || sceneChanged;

    (void)slowStage;
    if(rebuild && !HomeStage() && !instantRebuild) {
        Logf("Point de controle : reconstruction de la scene evitee sur ce stage (%u objet(s) cree(s), %u detruit(s) ou remplace(s)) : retour par rattrapage.",created,replaced);
        decorStale=false;return false;
    }

    if(sceneChanged && !HomeStage()) {
        Logf("Point de controle : changement de zone depuis le point (scene %lu -> %lu) : retour instantane refuse sur ce stage.",sceneAtPoint,sceneNow);
        return false;
    }
    memset(skip,0,sizeof(skip));
    const char* reason=Check(rebuild);
    if(reason){Logf("Point de controle : retour refuse (%s).",reason);return false;}
    if(rebuild) {

        double ms=0;
        DWORD hzOwner=0;
        if(hotzoneInstant)for(unsigned i=0;i<stageCount;++i)if(stageStates[i].descriptor==reinterpret_cast<DWORD>(base)+0xBEC17C)hzOwner=stageStates[i].owner;
        const DWORD hzRes0=hzOwner?Read(reinterpret_cast<void*>(hzOwner+0x2C)):0;
        const DWORD hzBack0=hzRes0?Read(reinterpret_cast<void*>(hzRes0+0x9C)):0;
        struct HzNodes{DWORD n70,n74,n8C,n268;};auto nodes=[&](DWORD res)->HzNodes{HzNodes h={};if(res){h.n70=Read(reinterpret_cast<void*>(res+0x70));h.n74=Read(reinterpret_cast<void*>(res+0x74));h.n8C=Read(reinterpret_cast<void*>(res+0x8C));h.n268=Read(reinterpret_cast<void*>(res+0x268));}return h;};
        const HzNodes hzN0=nodes(hzRes0);
        if(!RebuildScene(ms,sceneAtPoint<2?sceneAtPoint:sceneNow)) {
            Logf("Point de controle : decor modifie depuis le point (%u composant(s) nouveau(x), %u objet(s) detruit(s) ou remplace(s)) et reconstruction de la scene impossible : retour instantane refuse.",created,replaced);
            return false;
        }
        unsigned dropped=0;
        for(unsigned i=0;i<physicsCount;++i) {
            const PhysicsRef& ph=physicsRefs[i];bool same=true;
            for(unsigned g=ph.guard;g<ph.guard+2;++g){BYTE b[32];if(!Copy(b,guards[g].address,guards[g].size)||memcmp(b,guards[g].bytes,guards[g].size))same=false;}
            if(!same){skip[ph.range]=true;++dropped;}
        }
        if(hzOwner && diagEnabled){const DWORD r1=Read(reinterpret_cast<void*>(hzOwner+0x2C));const DWORD b1=r1?Read(reinterpret_cast<void*>(r1+0x9C)):0;const HzNodes n1=nodes(r1);
            Logf("Diag Hot Zone reconstruction : proprietaire %08lX, ressource %08lX -> %08lX, ressource+9C %08lX -> %08lX, noeuds +70 %08lX -> %08lX, +74 %08lX -> %08lX, +8C %08lX -> %08lX, +268 %08lX -> %08lX.",
                hzOwner,hzRes0,r1,hzBack0,b1,hzN0.n70,n1.n70,hzN0.n74,n1.n74,hzN0.n8C,n1.n8C,hzN0.n268,n1.n268);HzGroupDump(hzOwner,"apres reconstruction");}
        if(hzOwner && Read(reinterpret_cast<void*>(hzOwner+0x17C))==0) {

            typedef void(__fastcall* StateInitFn)(DWORD owner,DWORD unused);
            bool ok=true;
            RT_TRY{reinterpret_cast<StateInitFn>(base+0x5C9630)(hzOwner,0);}RT_EXCEPT{ok=false;}
            Logf("Point de controle : Hot Zone : initialisation de l'etat 0 rejouee%s (etat %lu).",ok?"":" (ECHEC)",Read(reinterpret_cast<void*>(hzOwner+0x17C)));
            HzGroupDump(hzOwner,"apres initialisation");

            const StageRaw* raw=nullptr;for(unsigned i=0;i<stageRawCount;++i)if(stageRaws[i].owner==hzOwner)raw=&stageRaws[i];
            const DWORD pointState=raw && raw->size>0x1D0?*reinterpret_cast<const DWORD*>(raw->data+0x17C):0;
            if(ok && raw && (pointState==3 || pointState==4)) {
                typedef void(__fastcall* StepFn)(DWORD owner,DWORD unused);
                auto put32=[&](DWORD o,DWORD v){RT_TRY{*reinterpret_cast<volatile DWORD*>(hzOwner+o)=v;}RT_EXCEPT{}};
                auto put8=[&](DWORD o,BYTE v){RT_TRY{*reinterpret_cast<volatile BYTE*>(hzOwner+o)=v;}RT_EXCEPT{}};
                bool stepOk=true;
                put32(0x17C,2);put32(0x1C8,1);put8(0x1CC,1);put8(0x1CD,0);put8(0x1CE,0);
                RT_TRY{reinterpret_cast<StepFn>(base+0x5B2170)(hzOwner,0);}RT_EXCEPT{stepOk=false;}
                const DWORD after3=Read(reinterpret_cast<void*>(hzOwner+0x17C));
                if(pointState==4 && stepOk) {
                    put32(0x1C8,2);put8(0x1CD,1);put8(0x1C4,raw->data[0x1C4]);put8(0x1C5,raw->data[0x1C5]);
                    RT_TRY{reinterpret_cast<StepFn>(base+0x5B2450)(hzOwner,0);}RT_EXCEPT{stepOk=false;}
                }
                const DWORD reached=Read(reinterpret_cast<void*>(hzOwner+0x17C));
                if(stepOk && reached==pointState)loadOnlyOwner=hzOwner;

                if(loadOnlyOwner){static const DWORD keep[]={0x1D0,0x1D3,0x1D4,0x1D6,0x1D8,0x1E0,0x1E4};for(DWORD o:keep)put8(o,raw->data[o]);}
                Logf("Point de controle : Hot Zone : transitions rejouees jusqu'a l'etat %lu (apres muret %lu, atteint %lu)%s.",pointState,after3,reached,loadOnlyOwner?"":" (ECHEC : apply normal)");
                HzGroupDump(hzOwner,"apres transitions");
            }
        }
        Logf("Point de controle : scene %lu reconstruite par le jeu en %.2f ms (%s ; %u composant(s) nouveau(x), %u objet(s) detruit(s) ou remplace(s) ; scene courante avant %lu, apres %lu ; %u objet(s) physique(s) du decor saute(s)).",
            sceneAtPoint,ms,sceneChanged?"changement de zone depuis le point":forced?"demande":decorStale?"decor deja reconstruit pour ce point":(stateChanged && !created && !replaced)?"etat des cassables change depuis le point":"decor modifie depuis le point",
            created,replaced,sceneNow,CurrentScene(),dropped);
        decorStale=true;
    }
    if(!WriteAll(saved) || !ReadAll(scratch) || !SameAsSaved(scratch)) {
        Logf("Point de controle : ERREUR d'ecriture, abandonne.");Release();return false;
    }
    lastFrame=savedFrame;
    if(!rebuild)DecorRestore();
    else if(hotzoneInstant){DecorDiff("apres reconstruction");DecorRestore();}

    StageLoad();
    if(rebuild) {
        rebindPending=0;
        for(unsigned i=0;i<stageCount && i<32;++i){DWORD o=0,d=0;if(!Describe(stageStates[i].component,o,d) || o!=stageStates[i].owner || !OwnerAlive(stageStates[i]))rebindPending|=1u<<i;}
        if(rebindPending){RebindRecreated(true);rebindFrames=rebindPending?60:0;}
    }
    if(rebuild && hotzoneInstant) {

        typedef void(__fastcall* CollisionSetFn)(DWORD owner,DWORD unused);
        for(unsigned i=0;i<stageCount;++i) {
            if(stageStates[i].descriptor!=reinterpret_cast<DWORD>(base)+0xBEC17C)continue;
            DWORD owner=0,descriptor=0;if(!Describe(stageStates[i].component,owner,descriptor) || owner!=stageStates[i].owner)continue;
            const DWORD state=Read(reinterpret_cast<void*>(owner+0x17C));
            bool ok=true;
            RT_TRY{reinterpret_cast<CollisionSetFn>(base+0x5ABC00)(owner,0);}RT_EXCEPT{ok=false;}
            Logf("Point de controle : Hot Zone : groupe de collision remis pour l'etat %lu%s.",state,ok?"":" (ECHEC)");
            HzFlagsRestore(true);
        }
    }
    loadOnlyOwner=0;
    if(rebuild && hotzoneInstant)DecorDiff("apres le retour");
    const DWORD flags=StageRawFlags();

    rawSkipDescriptor=hotzoneSoft?reinterpret_cast<DWORD>(base)+0xBEC17C:0;
    if(!rebuild && stateChanged)StageRawRestoreChanged();
    rawSkipDescriptor=0;
    BYTE camera=0xFF;Copy(&camera,base+0xFC7159,1);
    Logf("Point de controle : retour instantane de l'image %lu a l'image %lu%s%s (camera %u).",f,savedFrame,rebuild?" (decor remis a neuf)":"",flags?" ; drapeaux de la scene remis":"",camera);
    DiagCompare();
    FsmSpyCompare("apres le retour");
    return true;
}

static volatile LONG hashMode;
struct FrameHash { DWORD epoch,frame,rng,p1,p2,x1,x2,a1,a2; };
static constexpr DWORD hashSlots=1u<<15;
static FrameHash* hashRing; static DWORD hashEpoch=1,hashLastFrame,hashCompared,hashScanAt;
static LONG hashPrevMode; static bool hashBad;

static volatile LONG hashVerify; static DWORD hashVerifyFrom,hashPrevF;
static DWORD HashNoPointers(DWORD address,DWORD n) {
    DWORD h=0x811C9DC5;
    for(DWORD o=0;o+4<=n;o+=4){DWORD v=0;Copy(&v,reinterpret_cast<void*>(address+o),4);if(PointerLike(v))continue;h^=v;h=(h<<7)|(h>>25);h*=0x01000193;}
    return h;
}
static void FrameHashes(FrameHash& h,DWORD f) {
    const DWORD p=reinterpret_cast<DWORD>(base)+0xFD0540;
    h.epoch=hashEpoch;h.frame=f;h.rng=FastHash(base+0x1087AB0,0x9C8);

    auto play=[&](DWORD q)->DWORD {DWORD h=0x811C9DC5;for(DWORD o:{0x10u,0x14u,0x18u,0x2Cu,0x64u}){DWORD v=0;Copy(&v,reinterpret_cast<void*>(q+o),4);h^=v;h*=0x01000193;}return h;};
    h.p1=play(p);h.p2=play(p+0x6C8);
    Copy(&h.x1,reinterpret_cast<void*>(p+0x10),4);Copy(&h.x2,reinterpret_cast<void*>(p+0x6C8+0x10),4);
    Copy(&h.a1,reinterpret_cast<void*>(p+0x64),4);Copy(&h.a2,reinterpret_cast<void*>(p+0x6C8+0x64),4);
}

static constexpr DWORD fullSlots=8192,fullBytes=0xD90;
static BYTE* fullRing; static DWORD* fullTag; static volatile LONG fullWindowStart=-1;
static void FullNote(DWORD f) {
    if(!diagEnabled || fullWindowStart<0 || f<static_cast<DWORD>(fullWindowStart) || f>=static_cast<DWORD>(fullWindowStart)+600)return;
    if(!fullRing){fullRing=static_cast<BYTE*>(VirtualAlloc(nullptr,fullSlots*fullBytes,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));fullTag=static_cast<DWORD*>(VirtualAlloc(nullptr,fullSlots*4,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));}
    if(!fullRing || !fullTag)return;
    const DWORD k=f&(fullSlots-1);
    if(fullTag[k]==f+1)return;
    if(Copy(fullRing+k*fullBytes,base+0xFD0540,fullBytes))fullTag[k]=f+1;
}
static void FullDiff(DWORD f) {
    if(!fullRing || !fullTag || fullTag[f&(fullSlots-1)]!=f+1){Logf("Diag ecart : blocs complets de l'image %lu non notes.",f);return;}
    const BYTE* then=fullRing+(f&(fullSlots-1))*fullBytes;
    BYTE now[fullBytes];if(!Copy(now,base+0xFD0540,fullBytes))return;
    char l[600];int n=sprintf_s(l,"Diag ecart image %lu, mots differents des blocs joueurs (FD0540) :",f);unsigned w=0;
    for(DWORD o=0;o+4<=fullBytes;o+=4) {
        DWORD a,b;memcpy(&a,then+o,4);memcpy(&b,now+o,4);
        if(a==b)continue;
        if(++w<=20 && n<540)n+=sprintf_s(l+n,sizeof(l)-n," J%lu+%lX %lX>%lX%s",o/0x6C8+1,o%0x6C8,a,b,(PointerLike(a)||PointerLike(b))?"(adr)":"");
    }
    if(n<580)sprintf_s(l+n,sizeof(l)-n," (%u mots)",w);
    Log(l);
}
static DWORD hashDiff,hashFirstBad;
static void HashSummary(const char* what) {
    if(!hashCompared && !hashDiff)return;
    if(!hashDiff)Logf("%s : %lu image(s) identiques au replay d'origine.",what,hashCompared);
    else Logf("%s : %lu image(s) identiques, %lu DIFFERENTE(S) (premier ecart a l'image %lu).",what,hashCompared,hashDiff,hashFirstBad);
}
static void HashCompare(const FrameHash& slot,const FrameHash& now,DWORD f,const char* what) {
    if(slot.rng==now.rng && slot.p1==now.p1 && slot.p2==now.p2){++hashCompared;return;}
    ++hashDiff;
    if(hashBad)return;
    hashBad=true;hashFirstBad=f;FullDiff(f);
    float x1a,x1b,x2a,x2b;memcpy(&x1a,&slot.x1,4);memcpy(&x1b,&now.x1,4);memcpy(&x2a,&slot.x2,4);memcpy(&x2b,&now.x2,4);
    Logf("%s : ECART a l'image %lu (apres %lu image(s) identiques) : aleatoire %s, joueur 1 %s (x %.3f / %.3f, action %lX / %lX), joueur 2 %s (x %.3f / %.3f, action %lX / %lX).",
        what,f,hashCompared,slot.rng==now.rng?"identique":"DIFFERENT",slot.p1==now.p1?"identique":"DIFFERENT",x1a,x1b,slot.a1,now.a1,
        slot.p2==now.p2?"identique":"DIFFERENT",x2a,x2b,slot.a2,now.a2);
}
static void HashReset(){hashCompared=hashDiff=0;hashBad=false;}
static void FrameHashCheck(DWORD f) {
    const LONG mode=hashMode;
    if(!hashRing){hashRing=static_cast<FrameHash*>(VirtualAlloc(nullptr,hashSlots*sizeof(FrameHash),MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));if(!hashRing)return;}
    if(mode!=hashPrevMode) {
        if(hashPrevMode==2)HashSummary("Controle du rattrapage");
        if(hashPrevMode==1 && hashVerify){HashSummary("Controle apres retour instantane");InterlockedExchange(&hashVerify,0);}
        if(mode==2)HashReset();
        hashPrevMode=mode;
    }
    if(!mode)return;
    if(frontierCount>=hashScanAt){ScanRegions();hashScanAt=frontierCount+600;}
    FullNote(f);
    FrameHash now;FrameHashes(now,f);
    FrameHash& slot=hashRing[f&(hashSlots-1)];
    const DWORD prevF=hashPrevF;hashPrevF=f;

    const bool first=f!=prevF && f!=0;
    const bool known=slot.epoch==hashEpoch && slot.frame==f;
    if(mode==1 && hashVerify) {
        if(known){if(first)HashCompare(slot,now,f,"Controle apres retour instantane");return;}
        if(f>hashLastFrame) {
            HashSummary("Controle apres retour instantane");
            InterlockedExchange(&hashVerify,0);
        }
        if(first){now.epoch=hashEpoch;slot=now;}
        if(f>hashLastFrame)hashLastFrame=f;
        return;
    }
    if(mode==1) {
        if(f<prevF)++hashEpoch;
        hashLastFrame=f;now.epoch=hashEpoch;
        if(first && (slot.epoch!=hashEpoch || slot.frame!=f))slot=now;
        return;
    }
    if(!known) {
        if(first){now.epoch=hashEpoch;slot=now;}
        if(f>hashLastFrame)hashLastFrame=f;
        return;
    }
    if(first)HashCompare(slot,now,f,"Controle du rattrapage");
}

struct Bank {
    bool used; DWORD savedFrame;
    Range ranges[1024]; unsigned count; Guard guards[1024]; unsigned guardCount; Cursor cursors[258]; unsigned cursorCount;
    PhysicsRef physicsRefs[8]; unsigned physicsCount; bool skip[1024]; bool decorStale; BYTE* animation[2];
    DWORD total,manager,threadId; BYTE* reader; BYTE* saved; DWORD savedCap;
    BYTE savedClock; DWORD sceneAtPoint;
    StageState stageStates[64]; unsigned stageCount; StageRaw stageRaws[8]; unsigned stageRawCount;
    FsmSeen fsmPoint[96]; unsigned fsmPointCount; HzFlag hzFlags[256]; unsigned hzFlagCount;
    Block blocks[maxBlocks]; unsigned blockCount; DWORD blockBytes; DWORD blockSet[32768]; unsigned hashedFrames;
    BYTE* decor; DWORD decorCap; DWORD* hashes; BYTE pages[pageCount*0x1000];
    DWORD compAtSave[64]; unsigned compAtSaveCount; DWORD stageHeapStart,stageHeapEnd;
};
static constexpr DWORD hashBytes=(maxBlocks+pageCount)*(stableFrames+1)*4;
static Bank* BankNew() { return static_cast<Bank*>(VirtualAlloc(nullptr,sizeof(Bank),MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE)); }
static bool BankStore(Bank& b) {
    if(!active || !saved || !total)return false;
    if(b.savedCap<total){if(b.saved)HeapFree(GetProcessHeap(),0,b.saved);b.saved=static_cast<BYTE*>(HeapAlloc(GetProcessHeap(),0,total));b.savedCap=b.saved?total:0;}
    if(!b.saved)return false;
    if(blockBytes && b.decorCap<blockBytes){if(b.decor)VirtualFree(b.decor,0,MEM_RELEASE);b.decor=static_cast<BYTE*>(VirtualAlloc(nullptr,blockBytes,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));b.decorCap=b.decor?blockBytes:0;}
    if(!b.hashes)b.hashes=static_cast<DWORD*>(VirtualAlloc(nullptr,hashBytes,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if((blockBytes && !b.decor) || !b.hashes)return false;
    memcpy(b.saved,saved,total);
    memcpy(b.ranges,ranges,sizeof(ranges));b.count=count;memcpy(b.guards,guards,sizeof(guards));b.guardCount=guardCount;
    memcpy(b.cursors,cursors,sizeof(cursors));b.cursorCount=cursorCount;memcpy(b.physicsRefs,physicsRefs,sizeof(physicsRefs));b.physicsCount=physicsCount;
    memcpy(b.skip,skip,sizeof(skip));b.decorStale=decorStale;b.animation[0]=animation[0];b.animation[1]=animation[1];
    b.total=total;b.manager=manager;b.threadId=threadId;b.reader=reader;b.savedFrame=savedFrame;b.savedClock=savedClock;b.sceneAtPoint=sceneAtPoint;
    memcpy(b.stageStates,stageStates,sizeof(stageStates));b.stageCount=stageCount;memcpy(b.stageRaws,stageRaws,sizeof(stageRaws));b.stageRawCount=stageRawCount;
    memcpy(b.fsmPoint,fsmPoint,sizeof(fsmPoint));b.fsmPointCount=fsmPointCount;memcpy(b.hzFlags,hzFlags,sizeof(hzFlags));b.hzFlagCount=hzFlagCount;
    memcpy(b.blocks,blocks,sizeof(Block)*blockCount);b.blockCount=blockCount;b.blockBytes=blockBytes;memcpy(b.blockSet,blockSet,sizeof(blockSet));b.hashedFrames=hashedFrames;
    if(blockBytes && blockSaved)memcpy(b.decor,blockSaved,blockBytes);
    if(blockHashes)memcpy(b.hashes,blockHashes,hashBytes);
    if(pageSaved)memcpy(b.pages,pageSaved,sizeof(b.pages));
    memcpy(b.compAtSave,compAtSave,sizeof(compAtSave));b.compAtSaveCount=compAtSaveCount;b.stageHeapStart=stageHeapStart;b.stageHeapEnd=stageHeapEnd;
    b.used=true;
    return true;
}
static bool BankLoad(const Bank& b) {
    if(!b.used || !b.saved)return false;
    if(!blockSaved)blockSaved=static_cast<BYTE*>(VirtualAlloc(nullptr,maxBlockBytes+pageCount*0x1000,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!blockHashes)blockHashes=static_cast<DWORD*>(VirtualAlloc(nullptr,hashBytes,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE));
    if(!blockSaved || !blockHashes)return false;
    Release();
    saved=static_cast<BYTE*>(HeapAlloc(GetProcessHeap(),0,b.total*2));
    if(!saved)return false;
    scratch=saved+b.total;memcpy(saved,b.saved,b.total);
    memcpy(ranges,b.ranges,sizeof(ranges));count=b.count;memcpy(guards,b.guards,sizeof(guards));guardCount=b.guardCount;
    memcpy(cursors,b.cursors,sizeof(cursors));cursorCount=b.cursorCount;memcpy(physicsRefs,b.physicsRefs,sizeof(physicsRefs));physicsCount=b.physicsCount;
    memcpy(skip,b.skip,sizeof(skip));decorStale=b.decorStale;animation[0]=b.animation[0];animation[1]=b.animation[1];
    total=b.total;manager=b.manager;threadId=b.threadId;reader=b.reader;savedFrame=b.savedFrame;savedClock=b.savedClock;sceneAtPoint=b.sceneAtPoint;
    memcpy(stageStates,b.stageStates,sizeof(stageStates));stageCount=b.stageCount;memcpy(stageRaws,b.stageRaws,sizeof(stageRaws));stageRawCount=b.stageRawCount;
    memcpy(fsmPoint,b.fsmPoint,sizeof(fsmPoint));fsmPointCount=b.fsmPointCount;memcpy(hzFlags,b.hzFlags,sizeof(hzFlags));hzFlagCount=b.hzFlagCount;
    memcpy(blocks,b.blocks,sizeof(Block)*b.blockCount);blockCount=b.blockCount;blockBytes=b.blockBytes;memcpy(blockSet,b.blockSet,sizeof(blockSet));hashedFrames=b.hashedFrames;
    pageSaved=blockSaved+maxBlockBytes;pageHashes=blockHashes+maxBlocks*(stableFrames+1);
    if(blockBytes)memcpy(blockSaved,b.decor,blockBytes);
    memcpy(blockHashes,b.hashes,hashBytes);memcpy(pageSaved,b.pages,sizeof(b.pages));
    memcpy(compAtSave,b.compAtSave,sizeof(compAtSave));compAtSaveCount=b.compAtSaveCount;stageHeapStart=b.stageHeapStart;stageHeapEnd=b.stageHeapEnd;
    rebindPending=rebindFrames=0;diagCount=0;
    InterlockedExchange(&roundOver,0);
    InterlockedExchange(&active,1);
    return true;
}

static void Frontier(BYTE* r) {
    HzWatch();
    ++frontierCount;
    if(rebindFrames){RebindRecreated(false);if(!rebindPending)rebindFrames=0;else if(!--rebindFrames)Logf("Point de controle : composant recree introuvable apres la reconstruction.");}
    DWORD m=Read(base+0xFCE790);
    bool fighting=r && m && Read(reinterpret_cast<void*>(m+8))==2 && Read(base+0x1087A4C)==4 &&
        Read(reinterpret_cast<void*>(m+0xC))==reinterpret_cast<DWORD>(r);
    if(!fighting) {
        if(active && Read(base+0x1087A4C)!=4 && !(keepAcrossRounds && r && r==reader)){Drop("fin du combat, du round ou du replay");InterlockedExchange(&roundOver,1);}
        if(InterlockedExchange(&requestRestore,0))InterlockedExchange(&lastResult,2);
        InterlockedExchange(&requestSave,0);
        return;
    }
    DWORD f=Read(r+0x2C);
    if(Read(reinterpret_cast<void*>(m+0x1C))!=f)return;
    BYTE clock=0;Copy(&clock,base+0x10885DA,1);
    if(active && (r!=reader || m!=manager))Drop("autre lecteur de replay");
    else if(active && f<lastFrame)Drop("le replay est reparti en arriere");
    else if(active && clock>savedClock && !keepAcrossRounds){Drop("nouveau round");InterlockedExchange(&roundOver,1);}
    else if(active && !keepAcrossRounds && RoundDecided()){Drop("K.O. ou temps ecoule, retour desactive jusqu'a la prochaine reprise");InterlockedExchange(&roundOver,1);}
    lastFrame=f;
    FrameHashCheck(f);
    static bool deferLogged=false;

    if(requestSave && (StageEvent() || f==0)) {
        if(!deferLogged){Logf("Point de controle differe a l'image %lu : %s.",f,f==0?"intro en cours":"sequence de stage en cours");deferLogged=true;}
        return;
    }
    deferLogged=false;
    if(InterlockedExchange(&requestSave,0)) {
        InterlockedExchange(&roundOver,0);
        const char* reason=Prepare(r,m);
        if(reason) {
            if(RoundDecided()){InterlockedExchange(&roundOver,1);Logf("Point de controle impossible a l'image %lu : %s ; retour desactive.",f,reason);}
            else Logf("Point de controle impossible a l'image %lu (%s) : retour par rattrapage accelere.",f,reason);
            return;
        }
        savedFrame=f;InterlockedExchange(&active,1);InterlockedIncrement(&saveCount);
        StageSave();DecorBuild();StageTagOwners();FsmSpySave();HzFlagsSave(HzOwner());DecorRecord(0);ComponentSnapshot();sceneAtPoint=CurrentScene();DiagSave();
        BYTE camera=0xFF;Copy(&camera,base+0xFC7159,1);
        Logf("Point de controle pose a l'image %lu (%u plages, %lu octets, %u objets de decor, scene %lu, camera %u).",f,count,total,blockCount,sceneAtPoint,camera);
        return;
    }
    if(InterlockedExchange(&requestRestore,0)) {
        const bool ok=active && DoRestore(f);
        if(ok){InterlockedIncrement(&restoreCount);
            if(hashVerify)HashSummary("Controle apres retour instantane (avant le retour suivant)");
            HashReset();hashVerifyFrom=savedFrame;InterlockedExchange(&hashVerify,1);}
        InterlockedExchange(&lastResult,ok?1:2);
        return;
    }
    if(active && f>savedFrame)DecorRecord(f-savedFrame);
}
}
