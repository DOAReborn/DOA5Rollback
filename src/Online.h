namespace sel { static bool Tick(){return false;} }
namespace net {
using cp::Logf;
typedef unsigned long long u64s;
static DWORD localDelay=2;
static LONG diagPasEvt=-1;
#ifdef DOA5RB_RELEASE
static constexpr bool suiviEtat=false;
#else
static bool suiviEtat=false;
#endif

static DWORD suiviImg,suiviN;
#ifdef DOA5RB_RELEASE
static constexpr DWORD latenceEssai=0;
#else
static DWORD latenceEssai=0;
#endif

#ifdef DOA5RB_RELEASE
static constexpr bool traceManette=false;
#else
static bool traceManette=false;
#endif

constexpr DWORD AVANCEMAX=8,NB=256,MAX_MOTS=64,EMPREINTE_PAS=30,ABANDON_MS=5000,ABANDON_DEBUT_MS=20000,ABANDON_FIN_MS=1000,RAFALE_FIN=60;

constexpr int CANAL=4,CANAL_LIAISON=2,CANAL_POIGNEE=3;
constexpr DWORD MAGIC_PRET=0x50425244u;
constexpr DWORD MARGE_POIGNEE=20,POIGNEE_MAX_MS=10000,PRET_FRAIS_MS=300,PRET_ECART_MAX=600;

constexpr LONG POIGNEE_ECART_DECISION=90; constexpr DWORD SUR_PLACE_MAX_MS=300,SUR_PLACE_CONFIRME_MS=1500;

constexpr DWORD MAGIC=0x35425244u;
constexpr DWORD RVA_NETCODE=0xF7A238,RVA_NETCODE_FN=0x52ABC0,RVA_ECRIRE_APP=0x43B180,RVA_COPIER=0x3F52B0,RVA_APPAREILS=0x2057928,
    RVA_APP_LOCAL=0x10877B8,RVA_APP_PLACE=0x10877C0,RVA_TYPE_MATCH=0xF818A0,RVA_GEST=0xFCE790,RVA_ETAT=0x1087A4C,RVA_PHASE=0xDD94D4,
    RVA_RESEAU_PTR=0x20924BC,RVA_IAT_MM=0x9663F0,RVA_POSITIONS=0xFCBB00,RVA_JOUEURS=0xFD0540,RVA_ALEA=0x1087AB0;

constexpr int MM_NB=17,MM_MEMBRE=18,MM_DONNEE=24,MM_POSER=25,NT_ENVOYER=0,NT_DISPO=1,NT_LIRE=2,NT_ACCEPTER=3;

static void** SVT(void* o){return *reinterpret_cast<void***>(o);}
static bool SalonValide(u64s id){const DWORD lo=static_cast<DWORD>(id),hi=static_cast<DWORD>(id>>32);return lo && (hi>>24)==1 && ((hi>>20)&0xF)==8 && (hi&0x40000);}
static bool UtilisateurValide(u64s id){const DWORD lo=static_cast<DWORD>(id),hi=static_cast<DWORD>(id>>32);return lo && (hi>>24)==1 && ((hi>>20)&0xF)==1;}
static DWORD R32(DWORD rva){return Read(base+rva);}
static BYTE R8(DWORD rva){BYTE v=0;Copy(&v,base+rva,1);return v;}
static void* Matchmaking(){typedef void* (__cdecl* A)();const DWORD f=R32(RVA_IAT_MM);void* r=nullptr;__try{if(f)r=reinterpret_cast<A>(f)();}__except(EXCEPTION_EXECUTE_HANDLER){r=nullptr;}return r;}
static void* Reseau(){static void* n;if(n)return n;HMODULE a=GetModuleHandleA("steam_api.dll");typedef void* (__cdecl* A)();
    A f=a?reinterpret_cast<A>(GetProcAddress(a,"SteamNetworking")):nullptr;__try{if(f)n=f();}__except(EXCEPTION_EXECUTE_HANDLER){n=nullptr;}return n;}
static bool Envoyer(u64s to,const void* b,DWORD n,int canal){void* net=Reseau();if(!net||!to)return false;bool ok=false;
    __try{ok=reinterpret_cast<bool(__thiscall*)(void*,u64s,const void*,uint32_t,int,int)>(SVT(net)[NT_ENVOYER])(net,to,b,n,0,canal);}__except(EXCEPTION_EXECUTE_HANDLER){ok=false;}return ok;}
static void Accepter(u64s who){void* net=Reseau();if(!net||!who)return;__try{reinterpret_cast<bool(__thiscall*)(void*,u64s)>(SVT(net)[NT_ACCEPTER])(net,who);}__except(EXCEPTION_EXECUTE_HANDLER){}}

static int Recevoir(void* b,DWORD cap,int canal,u64s* de){void* net=Reseau();if(!net)return -1;uint32_t taille=0,lu=0;bool ok=false;
    __try{if(!reinterpret_cast<bool(__thiscall*)(void*,uint32_t*,int)>(SVT(net)[NT_DISPO])(net,&taille,canal))return -1;
        ok=reinterpret_cast<bool(__thiscall*)(void*,void*,uint32_t,uint32_t*,u64s*,int)>(SVT(net)[NT_LIRE])(net,b,cap,&lu,de,canal);}
    __except(EXCEPTION_EXECUTE_HANDLER){return -1;}
    return ok?static_cast<int>(lu):-1;}

static SRWLOCK advLock=SRWLOCK_INIT;
static u64s adversaire;
static u64s salon; static DWORD nombre; static int placePubliee=-1; static DWORD dernierTicSalon,dernierMaintien;
static long dernierEtat[6]={-9,-9,-9,-9,-9,-9}; static volatile LONG liaisonOk;

constexpr DWORD MAGIC_ABANDON=0x41425244u;
static volatile LONG demandeAbandonNatif; static volatile LONG natifMoi,natifLui; static volatile LONG natifImageMoi,natifImageLui,natifPlaceMoi,natifPlaceLui;

constexpr DWORD MAGIC_REGLAGES=0x52425244u;
static DWORD reglagesMoi,reglagesLui; static u64s reglagesDe; static volatile LONG reglagesDiff;
static void NoterReglages(u64s de,DWORD r){
    if(de==reglagesDe && r==reglagesLui)return;
    reglagesDe=de;reglagesLui=r;InterlockedExchange(&reglagesDiff,r!=reglagesMoi?1:0);
    if(r!=reglagesMoi)cp::LogR("Reseau : REGLAGES DIFFERENTS chez l'adversaire (empreinte %04lX.%04lX, la mienne %04lX.%04lX) : DOA5Rollback.ini (reglages experts, listes de zones), chutes d'Azuchi (DOA5LR-ExtraStages.ini) ou version du module differents : desynchros possibles.",
        r>>16,r&0xFFFF,reglagesMoi>>16,reglagesMoi&0xFFFF);
    else Logf("Reseau : reglages identiques chez l'adversaire (empreinte %04lX.%04lX).",r>>16,r&0xFFFF);}

constexpr DWORD MAGIC_BISSECTION=0x48425244u;
struct BisEmp { DWORD img,a,b; float pos[6]; WORD vie[2]; };
static BisEmp bisMoi[EMPREINTE_PAS]; static DWORD bisN,bisEpoque,bisFaute; static long bisVerifOk; static volatile LONG bisGen;
struct BisRecu { DWORD mot,a,b,quand; bool ok; };
static BisRecu bisRecu[32];
static void NoterBissection(const DWORD* m,DWORD now){BisRecu& r=bisRecu[(m[1]&0xFFFF)%32];r.mot=m[1];r.a=m[2];r.b=m[3];r.quand=now;r.ok=true;}
static void BisGroupes(char* t,size_t n,DWORD gr,const char* sep){static const char* const noms[4]={"position J1","position J2","vies","alea"};
    t[0]=0;size_t m=0;for(unsigned i=0;i<4;++i)if((gr>>i)&1u){const int q=_snprintf_s(t+m,n-m,_TRUNCATE,"%s%s",m?sep:"",noms[i]);if(q<0)return;m+=static_cast<size_t>(q);}}
static void TicBissection(DWORD now){
    static LONG vu;static DWORD debut;static bool attente;
    const LONG g=bisGen;if(g==vu)return;
    if(!attente){attente=true;debut=now;}
    const BisRecu* lui[EMPREINTE_PAS]={};DWORD recus=0;
    for(DWORD k=0;k<bisN;++k){const DWORD d=(bisMoi[k].img-1-bisEpoque)&0xFFFF;const BisRecu& r=bisRecu[d%32];
        if(r.ok && r.mot==((bisEpoque<<16)|d) && now-r.quand<10000){lui[k]=&r;++recus;}}
    if(recus<bisN && now-debut<3000)return;
    vu=g;attente=false;
    if(!recus){Logf("Reseau : BISSECTION : aucune empreinte image par image recue de l'adversaire en 3 s (version sans bissection ?).");return;}
    long premiere=-1,identique=-1;DWORD groupes=0,differentes=0,kp=0;
    for(DWORD k=0;k<bisN;++k){if(!lui[k])continue;const long f=static_cast<long>(bisMoi[k].img-1);
        const DWORD da=lui[k]->a^bisMoi[k].a,db=lui[k]->b^bisMoi[k].b;
        if(!da && !db){if(premiere<0)identique=f;continue;}
        ++differentes;if(premiere<0){premiere=f;kp=k;groupes=((da>>16)?1u:0u)|((da&0xFFFF)?2u:0u)|((db>>16)?4u:0u)|((db&0xFFFF)?8u:0u);}}
    if(premiere<0){cp::LogR("Reseau : BISSECTION de la desynchro de l'image %lu : les %lu image(s) recue(s) sur %lu ont les memes empreintes (positions, vies, alea) : l'image fautive manque ?",bisFaute,recus,bisN);return;}
    char gt[64];BisGroupes(gt,sizeof gt,groupes,", ");
    char it[24]="aucune recue";if(identique>=0)_snprintf_s(it,sizeof it,_TRUNCATE,"%ld",identique);
    char vt[24]="aucune";if(bisVerifOk>=0)_snprintf_s(vt,sizeof vt,_TRUNCATE,"image %ld",bisVerifOk);
    const BisEmp& e=bisMoi[kp];
    cp::LogR("Reseau : BISSECTION de la desynchro de l'image %lu : 1re image differente %ld (%s), derniere identique avant elle %s, verification identique precedente %s ; %lu image(s) differente(s) sur %lu recue(s). Chez moi a l'image %ld : J1 %.4f %.4f %.4f, J2 %.4f %.4f %.4f, vies %u %u.",
        bisFaute,premiere,gt,it,vt,differentes,recus,premiere,e.pos[0],e.pos[1],e.pos[2],e.pos[3],e.pos[4],e.pos[5],e.vie[0],e.vie[1]);
    if constexpr(kTest){char l[700]="";int m=0;unsigned c=0;
        for(DWORD k=0;k<bisN && c<8;++k){if(!lui[k])continue;const DWORD da=lui[k]->a^bisMoi[k].a,db=lui[k]->b^bisMoi[k].b;if(!da && !db)continue;
            char g2[64];BisGroupes(g2,sizeof g2,((da>>16)?1u:0u)|((da&0xFFFF)?2u:0u)|((db>>16)?4u:0u)|((db&0xFFFF)?8u:0u),"+");
            const int q=_snprintf_s(l+m,sizeof l-m,_TRUNCATE,"%s%lu (%s)",c?", ":" ",bisMoi[k].img-1,g2);if(q<0)break;m+=q;++c;}
        Logf("Reseau : BISSECTION : images differentes :%s%s.",l,differentes>c?", ...":"");}}

static volatile LONG finCombatTick;
static bool AbandonNatifRecevable(DWORD image){
    if(GetTickCount()-static_cast<DWORD>(finCombatTick)<2000)return false;
    return image<=R32(RVA_NETCODE+8)+120;}
static int PlaceLocale(){for(int p=0;p<4;++p)if(R8(RVA_APP_LOCAL+p)!=0xFF)return p;return 0xFF;}

static volatile LONG idLocalConnu,idLocal;
static void LireIdLocal(){if(idLocalConnu)return;__try{idLocal=reinterpret_cast<LONG(__cdecl*)()>(base+0x5048C0)();InterlockedExchange(&idLocalConnu,1);}__except(EXCEPTION_EXECUTE_HANDLER){}}
static int MembreNetcode(){
    if(!idLocalConnu)return -1;
    const DWORD n=R32(RVA_NETCODE+0xA0);if(!n || n>4 || !R32(RVA_NETCODE+4))return -1;
    for(DWORD i=0;i<n;++i)if(static_cast<LONG>(R32(RVA_NETCODE+0x40+i*0x18))==idLocal)return 1;
    return 0;
}
static u64s Adversaire(){AcquireSRWLockShared(&advLock);const u64s a=adversaire;ReleaseSRWLockShared(&advLock);return a;}
static void PoserAdversaire(u64s a){AcquireSRWLockExclusive(&advLock);adversaire=a;ReleaseSRWLockExclusive(&advLock);}

constexpr int MAXCAND=8; static u64s candidats[MAXCAND]; static int nbCandidats;
static void PoserCandidats(const u64s* c,int n){AcquireSRWLockExclusive(&advLock);nbCandidats=n;for(int i=0;i<n;++i)candidats[i]=c[i];ReleaseSRWLockExclusive(&advLock);}
static int LireCandidats(u64s* c){AcquireSRWLockShared(&advLock);const int n=nbCandidats;for(int i=0;i<n;++i)c[i]=candidats[i];ReleaseSRWLockShared(&advLock);return n;}
static void TicSalon() {
    const DWORD now=GetTickCount();if(now-dernierTicSalon<250)return;dernierTicSalon=now;
    TicBissection(now);
    if(R32(RVA_TYPE_MATCH)!=3){if(salon){Logf("Salon : quitte.");salon=0;PoserAdversaire(0);InterlockedExchange(&liaisonOk,0);memset(dernierEtat,0xF7,sizeof(dernierEtat));}return;}
    const DWORD reseau=R32(RVA_RESEAU_PTR);u64s s=0;
    if(!reseau || !Copy(&s,reinterpret_cast<void*>(reseau+0xB0),8) || !SalonValide(s))return;
    void* mm=Matchmaking();if(!mm)return;
    if(s!=salon){LARGE_INTEGER q;QueryPerformanceCounter(&q);nombre=q.LowPart^(now*2654435761u);salon=s;placePubliee=-1;PoserAdversaire(0);InterlockedExchange(&liaisonOk,0);Logf("Salon : rejoint.");}
    const int maPlace=MembreNetcode()==0?0xFF:PlaceLocale();
    __try{
        if(maPlace!=placePubliee){char m[24];sprintf_s(m,"72:%08lX:%d",nombre,maPlace);
            reinterpret_cast<void(__thiscall*)(void*,u64s,const char*,const char*)>(SVT(mm)[MM_POSER])(mm,salon,"doa5rb",m);placePubliee=maPlace;}
        char moi[12];sprintf_s(moi,"%08lX",nombre);
        const int n=reinterpret_cast<int(__thiscall*)(void*,u64s)>(SVT(mm)[MM_NB])(mm,salon);
        long marques=0,moiTrouve=0;u64s adv=0,autre=0;u64s cand[MAXCAND];int nc=0;
        for(int j=0;j<n && j<64;++j){
            u64s membre=0;reinterpret_cast<u64s*(__thiscall*)(void*,u64s*,u64s,int)>(SVT(mm)[MM_MEMBRE])(mm,&membre,salon,j);
            if(!UtilisateurValide(membre))continue;
            const char* v=reinterpret_cast<const char*(__thiscall*)(void*,u64s,u64s,const char*)>(SVT(mm)[MM_DONNEE])(mm,salon,membre,"doa5rb");
            char c[24]={};if(v)Copy(c,v,sizeof(c)-1);c[sizeof(c)-1]=0;
            if(strncmp(c,"72:",3) || strlen(c)<13 || c[11]!=':')continue;
            ++marques;if(!strncmp(c+3,moi,8)){moiTrouve=1;continue;}
            const long place=strtol(c+12,nullptr,10);autre=membre;if(nc<MAXCAND)cand[nc++]=membre;
            if((maPlace==0 && place==1) || (maPlace==1 && place==0))adv=membre;
        }
        if(!adv && n==2 && marques==2 && moiTrouve)adv=autre;

        PoserAdversaire(adv);PoserCandidats(cand,nc);
        {static u64s advReglages;if(adv!=advReglages){advReglages=adv;reglagesDe=0;reglagesLui=0;InterlockedExchange(&reglagesDiff,0);}}
        if(adv){
            if(now-dernierMaintien>=1000){Accepter(adv);const DWORD m=MAGIC;Envoyer(adv,&m,4,CANAL_LIAISON);dernierMaintien=now;
                if(reglagesMoi){const DWORD r[4]={MAGIC_REGLAGES,reglagesMoi,0,0};Envoyer(adv,r,16,CANAL_LIAISON);}}
            for(int g=0;g<16;++g){BYTE t[16];u64s de=0;const int lu=Recevoir(t,sizeof(t),CANAL_LIAISON,&de);if(lu<0)break;if(de==adv && lu==4)InterlockedExchange(&liaisonOk,1);
                if(de==adv && lu==16){DWORD r[4];memcpy(r,t,16);if(r[0]==MAGIC_REGLAGES)NoterReglages(de,r[1]);}
                bool membre=false;for(int i=0;i<nc;++i)if(cand[i]==de)membre=true;
                if(membre && lu==16){DWORD r[4];memcpy(r,t,16);if(r[0]==MAGIC_BISSECTION)NoterBissection(r,now);}
                if(membre && lu==12){DWORD m[3];memcpy(m,t,12);if(m[0]==MAGIC_ABANDON && m[2]<=1 && !natifLui && MembreNetcode()==1 && static_cast<int>(m[2])!=PlaceLocale() && AbandonNatifRecevable(m[1])){
                    natifImageLui=static_cast<LONG>(m[1]);natifPlaceLui=static_cast<LONG>(m[2]);InterlockedExchange(&natifLui,1);
                    Logf("Reseau : l'adversaire abandonne (F5, netcode du jeu) : il perd les rounds restants (image du jeu %lu).",m[1]);}}}
            if(natifMoi){const DWORD m[3]={MAGIC_ABANDON,static_cast<DWORD>(natifImageMoi),static_cast<DWORD>(natifPlaceMoi)};for(int i=0;i<nc;++i)Envoyer(cand[i],m,12,CANAL_LIAISON);}
        }
        long e[6]={n,marques,moiTrouve,maPlace,adv?1:0,liaisonOk};
        if(memcmp(e,dernierEtat,sizeof(e))){memcpy(dernierEtat,e,sizeof(e));
            Logf("Salon : %ld membre(s), %ld marque(s) du mod, moi %s, ma place %ld, adversaire %s, liaison %s.",n,marques,moiTrouve?"trouve":"pas encore",static_cast<long>(maPlace),adv?"pret":"absent",liaisonOk?"ouverte":"pas encore");}
    }__except(EXCEPTION_EXECUTE_HANDLER){}
}

#pragma pack(push,1)
struct Entete { DWORD magic; BYTE type,place; WORD n; DWORD epoque,premiere,recu,imageEmpreinte,empreinte; short avance,pad; DWORD heure,echo; };
#pragma pack(pop)
static u64s adv;
static u64s cand[MAXCAND]; static int nCand; static bool advSur;

static volatile LONG demandeAbandon; static bool abandonMoi,abandonLui; static DWORD abandonImageMoi,abandonImageLui;
static void PlaceAbandon(DWORD& place,DWORD& image){
    if(abandonMoi && abandonLui){place=0;image=abandonImageMoi>abandonImageLui?abandonImageMoi:abandonImageLui;}
    else if(abandonMoi){place=localPlace;image=abandonImageMoi;} else {place=remotePlace;image=abandonImageLui;}
}
static DWORD epoque,premiereImage;
static int appLocal,appDistant,padLocal;
static DWORD local[NB],distant[NB],utilise[NB];
static long localMax,distantMax,ackDistant;
static DWORD dernierRecu,dernierBilan;
static DWORD empreintes[NB]; static DWORD empreinteImage[NB];
static DWORD derniereConf;
static DWORD mesEmpreintes[16],mesImages[16];
static volatile LONG abandonne; static long sImages,sAttentes,sEnvoyes,sRecus,sIgnores,sVerifs,sDesyncs,sPredites,premiereDesync=-1;
static long sAutrePhase; static DWORD derniereEpoqueAutre; static unsigned autrePhaseLogs;
static volatile LONG frontiereVue;
static DWORD debutPhase1=0xFFFFFFFF;
static bool combatDecide; static volatile LONG modeCombat;

static DWORD heureAdverse,heureRecue; static float rttLisse; static DWORD retardActuel; static DWORD dernierRetardJournal;

static DWORD manetteDernier=0xFFFFFFFF; static unsigned manetteLignes; static long manetteSautes;

static bool redescenteDouce=true; static DWORD margeSansPrediction=2; static bool retardProvisoire; static DWORD rttN,rttNDebut;
static DWORD MotManette(){return padLocal<4?R32(RVA_APPAREILS+padLocal*0x2C)&0x7FFFFFFF:0;}
static DWORD LireManette(long de,long a){
    const DWORD w=MotManette();
    if constexpr(kTest){
        if(traceManette && manetteLignes<50000 && (w!=manetteDernier || manetteSautes)){++manetteLignes;
            char autres[96]="";int m=0;
            for(int k=0;k<4;++k){if(k==padLocal)continue;const DWORD v=R32(RVA_APPAREILS+k*0x2C)&0x7FFFFFFF;
                if(v){const int q=_snprintf_s(autres+m,sizeof autres-m,_TRUNCATE," ; appareil %d = %04lX.%04lX",k,v>>16,v&0xFFFF);if(q>0)m+=q;}}
            Logf("MANETTE images %ld a %ld : %04lX.%04lX (appareil %d, retard %lu%s)%s.",de,a,w>>16,w&0xFFFF,padLocal,retardActuel,manetteSautes?", apres des lectures sautees":"",autres);}
        manetteDernier=w;manetteSautes=0;}
    return w;}

static float posAt[NB][6]; static DWORD posImg[NB],zoneAt[NB]; static long traceDe=-1; static bool traceProchaine; static unsigned traceLignes;
static void TraceTransition(){
    if(!active){traceProchaine=true;return;}
    const long f=sc::ctxFrame>0?static_cast<long>(sc::ctxFrame):static_cast<long>(lab::lastFrame);
    if(traceDe<0 || f>traceDe+300)traceDe=f;}
static DWORD sessions; static short avanceAdverse; static float syncEma; static DWORD dernierePause; static long sPauses; static bool dernierVerrou;

static DWORD Fnv(DWORD h,const void* p,size_t n){const BYTE* o=static_cast<const BYTE*>(p);for(size_t i=0;i<n;++i)h=(h^o[i])*16777619u;return h;}
static DWORD Empreinte(){static BYTE t[0x9C0];DWORD h=2166136261u;
    Copy(t,base+RVA_POSITIONS,12);h=Fnv(h,t,12);Copy(t,base+RVA_POSITIONS+0x180,12);h=Fnv(h,t,12);
    const WORD v[2]={static_cast<WORD>(R32(RVA_JOUEURS+0x2C)),static_cast<WORD>(R32(RVA_JOUEURS+0x6C8+0x2C))};h=Fnv(h,v,4);
    Copy(t,base+RVA_ALEA,sizeof(t));return Fnv(h,t,sizeof(t));}
static void EcrireDetails(DWORD img);
static void EcrireEtat(DWORD img);

static BisEmp bisCalc[NB],bisConf[NB]; static long verifOk=-1;
static DWORD Pli(DWORD h){return (h^(h>>16))&0xFFFF;}
static void NoterBis(DWORD x){BisEmp& e=bisCalc[x%NB];e.img=x+1;
    Copy(e.pos,base+RVA_POSITIONS,12);Copy(e.pos+3,base+RVA_POSITIONS+0x180,12);
    e.vie[0]=static_cast<WORD>(R32(RVA_JOUEURS+0x2C));e.vie[1]=static_cast<WORD>(R32(RVA_JOUEURS+0x6C8+0x2C));
    static DWORD t[0x9C0/4];Copy(t,base+RVA_ALEA,sizeof(t));DWORD h=2166136261u;for(const DWORD w:t)h=(h^w)*16777619u;
    e.a=(Pli(Fnv(2166136261u,e.pos,12))<<16)|Pli(Fnv(2166136261u,e.pos+3,12));e.b=(Pli(Fnv(2166136261u,e.vie,4))<<16)|Pli(h);}
static void EnvoyerBis(DWORD img){
    const DWORD de=img-epoque>=EMPREINTE_PAS?img-(EMPREINTE_PAS-1):epoque;DWORD n=0;
    for(DWORD f=de;f<=img && n<EMPREINTE_PAS;++f){const BisEmp& e=bisConf[f%NB];if(e.img!=f+1)continue;bisMoi[n++]=e;
        const DWORD m[4]={MAGIC_BISSECTION,(epoque<<16)|((f-epoque)&0xFFFF),e.a,e.b};Envoyer(adv,m,16,CANAL_LIAISON);}
    bisN=n;bisEpoque=epoque;bisFaute=img;bisVerifOk=verifOk;InterlockedIncrement(&bisGen);}

static long gardeImages; static bool gardeVu;
static void GardeSansPhoto(DWORD x){if constexpr(kTest){
    if(!lab::FramePredicted(x) || !lab::SeqActiveNow() || lab::SeqPhotoOn())return;
    ++gardeImages;if(gardeVu)return;gardeVu=true;
    DWORD n[lab::SEQMAX];const unsigned c=lab::SeqList(n);
    Logf("Reseau : GARDE-FOU : image %lu predite pendant une sequence de scene (%u noeud(s)) dans la zone %06lX, ou les sequences ne sont pas photographiees : un retour ne les remet pas.",x,c,lab::SceneVt());}}
static bool EnCombatSalon(){const DWORD g=R32(RVA_GEST);return R32(RVA_TYPE_MATCH)==3 && R32(RVA_ETAT)==4 && g && Read(reinterpret_cast<void*>(g+8))==1 && R32(RVA_NETCODE+4)!=0;}
static void EcrireApp(int app,DWORD maintenu,DWORD precedent){
    typedef void (__thiscall* F)(void*,DWORD,DWORD,DWORD*,DWORD);
    reinterpret_cast<F>(base+RVA_ECRIRE_APP)(base+RVA_APPAREILS+app*0x2C,maintenu,precedent,nullptr,0);}

static long Tampon(){return 1;}

static volatile LONG modeRetard=2; static DWORD avanceMax=AVANCEMAX;
static DWORD RetardAuto(){const float r=rttLisse;if(r<=0)return 2;return r<=60?1:r<=100?2:r<=150?3:4;}
static DWORD MotLocal(long f){return f<static_cast<long>(premiereImage)+Tampon()?0:local[f%NB];}
static DWORD MotDistant(long f){
    if(f<static_cast<long>(premiereImage)+Tampon())return 0;
    if(f<=distantMax)return distant[f%NB];
    return distantMax>=static_cast<long>(premiereImage)+Tampon()?distant[distantMax%NB]:0;}

static void Bilan(bool force){const DWORD now=GetTickCount();if(!force && now-dernierBilan<3000)return;dernierBilan=now;
    Logf("Reseau : %ld image(s) calculee(s) dont %ld predite(s), %ld attente(s), %ld paquet(s) envoye(s), %ld recu(s), %ld ignore(s), avance de l'adversaire %ld, %ld verification(s), %ld desynchro(s).",
        sImages,sPredites,sAttentes,sEnvoyes,sRecus,sIgnores,distantMax-static_cast<long>(lab::lastFrame),sVerifs,sDesyncs);
    if(sAutrePhase){Logf("Reseau : %ld paquet(s) de l'adversaire d'une autre phase (derniere epoque %lu, la mienne %lu).",sAutrePhase,derniereEpoqueAutre,static_cast<DWORD>(epoque));sAutrePhase=0;}
    if(sPauses)Logf("Reseau : %ld pause(s) d'equilibrage (j'etais en avance sur l'adversaire).",sPauses);
    sImages=sPredites=sAttentes=sEnvoyes=sRecus=sIgnores=sVerifs=sPauses=0;}

static unsigned rafaleFin,rafaleLogs;
static void Terminer(const char* pourquoi){
    if(!active)return;Bilan(true);
    cp::LogR("Reseau : fin de la phase en ligne n%lu (%s) : image %lu, %ld desynchro(s) au total%s.",sessions,pourquoi,lab::lastFrame,sDesyncs,premiereDesync>=0?" (premiere ci-dessus)":"");
    if constexpr(kTest){if(gardeImages)Logf("Reseau : GARDE-FOU : %ld image(s) calculee(s) en prediction pendant une sequence de scene sans photo des sequences dans cette phase.",gardeImages);}
    InterlockedExchange(&active,0);base[RVA_NETCODE+0x2C]=0;}
static void Commencer(u64s a,DWORD j){
    {const LONG m=modeRetard;localDelay=m<0?RetardAuto():static_cast<DWORD>(m);}
    retardProvisoire=redescenteDouce && modeRetard<0 && rttLisse<=0;rttNDebut=rttN;
    adv=a;nCand=LireCandidats(cand);advSur=false;epoque=premiereImage=j;autrePhaseLogs=0;sAutrePhase=0;
    if(abandonMoi)abandonImageMoi=j+60;if(abandonLui)abandonImageLui=j+60;
    const int p=PlaceLocale();localPlace=static_cast<DWORD>(p);remotePlace=1-localPlace;
    appLocal=R8(RVA_APP_PLACE+p);appDistant=R8(RVA_APP_PLACE+(1-p));padLocal=R8(RVA_APP_LOCAL+p);
    memset(local,0,sizeof(local));memset(distant,0,sizeof(distant));memset(utilise,0,sizeof(utilise));memset(empreinteImage,0,sizeof(empreinteImage));memset(mesImages,0,sizeof(mesImages));
    localMax=distantMax=static_cast<long>(j)+Tampon()-1;ackDistant=static_cast<long>(j)-1;remoteHave=static_cast<DWORD>(distantMax);
    derniereConf=0;sDesyncs=0;premiereDesync=-1;avanceAdverse=0;syncEma=0;retardActuel=localDelay;dernierePause=0;InterlockedExchange(&sc::diagEvtImage,-1);diagPasEvt=-1;dernierVerrou=false;verrouCourant=true;verrouImage=0;suiviImg=0;dernierRecu=GetTickCount();++sessions;InterlockedExchange(&abandonne,0);
    memset(lab::haveTrue,0,sizeof(lab::haveTrue));
    for(DWORD f=j;f<j+static_cast<DWORD>(Tampon());++f){lab::p2true[lab::K(f)]={};lab::haveTrue[lab::K(f)]=true;}
    rafaleFin=0;manetteDernier=0xFFFFFFFF;manetteSautes=0;
    memset(bisCalc,0,sizeof(bisCalc));memset(bisConf,0,sizeof(bisConf));verifOk=-1;gardeImages=0;gardeVu=false;
    if constexpr(kTest){traceDe=traceProchaine?static_cast<long>(j):-1;traceProchaine=false;}
    InterlockedExchange(&active,1);
    if constexpr(kTest)Logf("Reseau : phase en ligne n%lu : rollback a partir de l'image %lu (je joue J%d, retard local %lu image(s)%s, aller-retour %.0f ms, limite de rollback %lu).",
        sessions,j,p+1,localDelay,modeRetard<0?" AUTO":"",rttLisse,avanceMax);
    else cp::LogR("Reseau : phase en ligne n%lu : rollback a partir de l'image %lu (J%d, retard %lu image(s)%s, limite %lu).",sessions,j,p+1,localDelay,modeRetard<0?" AUTO":"",avanceMax);
}
static void LirePaquets(){
    for(int g=0;g<64;++g){
        BYTE t[sizeof(Entete)+MAX_MOTS*4+16];u64s de=0;const int lu=Recevoir(t,sizeof(t),CANAL,&de);if(lu<0)break;
        Entete e;if(lu<static_cast<int>(sizeof(e))){++sIgnores;continue;}
        memcpy(&e,t,sizeof(e));
        if(e.magic!=MAGIC || e.type!=3 || e.n>MAX_MOTS || static_cast<DWORD>(lu)!=sizeof(e)+e.n*4u || e.place!=static_cast<BYTE>(remotePlace)){++sIgnores;continue;}
        if(de!=adv) {
            bool connu=false;for(int i=0;i<nCand;++i)if(cand[i]==de)connu=true;
            if(advSur || !connu || e.epoque!=epoque){++sIgnores;continue;}
            adv=de;PoserAdversaire(de);Accepter(de);Log("Reseau : adversaire corrige : les paquets de la phase viennent d'un autre membre du salon (marque de place en retard).");
        }
        if(e.epoque!=epoque){++sAutrePhase;derniereEpoqueAutre=e.epoque;
            if(autrePhaseLogs<4){++autrePhaseLogs;Logf("Reseau : paquet de l'adversaire d'une AUTRE phase (epoque %lu, la mienne %lu, place %u) : ignore.",static_cast<DWORD>(e.epoque),static_cast<DWORD>(epoque),static_cast<unsigned>(e.place));}
            continue;}
        advSur=true;
        if((e.pad&0x4000) && !abandonLui && static_cast<DWORD>((e.pad>>13)&1)==remotePlace){
            abandonLui=true;abandonImageLui=epoque+(e.pad&0x1FFF);Logf("Reseau : l'adversaire abandonne (F5) : il perd les rounds restants (a partir de l'image %lu).",abandonImageLui);}
        ++sRecus;dernierRecu=GetTickCount();avanceAdverse=e.avance;
        if(e.heure){heureAdverse=e.heure;heureRecue=dernierRecu;}
        if(e.echo){const DWORD rtt=dernierRecu-e.echo;if(rtt<2000){rttLisse=rttLisse?rttLisse*0.9f+0.1f*static_cast<float>(rtt):static_cast<float>(rtt);++rttN;}}
        if(e.recu && static_cast<long>(e.recu)-1>ackDistant && static_cast<long>(e.recu)-1<=localMax)ackDistant=static_cast<long>(e.recu)-1;
        const DWORD* mots=reinterpret_cast<const DWORD*>(t+sizeof(e));
        for(DWORD k=0;k<e.n;++k){const long f=static_cast<long>(e.premiere+k);
            if(f<=distantMax)continue;
            if(f!=distantMax+1 || f-static_cast<long>(lab::lastFrame)>=static_cast<long>(lab::IR)-8)break;
            const DWORD w=mots[k]&0x7FFFFFFF;distant[f%NB]=w;distantMax=f;
            lab::In in={};memcpy(in.b,&w,4);lab::p2true[lab::K(f)]=in;lab::haveTrue[lab::K(f)]=true;}
        remoteHave=static_cast<DWORD>(distantMax);
        if(e.imageEmpreinte){const DWORD img=e.imageEmpreinte-1,i=(img/EMPREINTE_PAS)%16;
            if(mesImages[i]==img+1){++sVerifs;if(mesEmpreintes[i]!=e.empreinte){++sDesyncs;
                if(premiereDesync<0){premiereDesync=static_cast<long>(img);cp::LogR("Reseau : DESYNCHRONISATION : l'image confirmee %lu differe de celle de l'adversaire.",img);EnvoyerBis(img);if constexpr(kTest){EcrireDetails(img);EcrireEtat(img);}}}
                else if(premiereDesync<0)verifOk=static_cast<long>(img);
                mesImages[i]=0;}}
    }
}

struct Attente { DWORD due,taille; BYTE b[sizeof(Entete)+MAX_MOTS*4]; };
static Attente fileEssai[64]; static unsigned fileTete,fileQueue;
static void ViderFileEssai(){const DWORD now=GetTickCount();
    while(fileTete!=fileQueue && static_cast<long>(now-fileEssai[fileTete%64].due)>=0){if(Envoyer(adv,fileEssai[fileTete%64].b,fileEssai[fileTete%64].taille,CANAL))++sEnvoyes;++fileTete;}}
static void EnvoyerEntrees(){
    BYTE t[sizeof(Entete)+MAX_MOTS*4];
    const long av=static_cast<long>(lab::lastFrame)-distantMax;
    const DWORD maintenant=GetTickCount();
    Entete e={MAGIC,3,static_cast<BYTE>(localPlace),0,epoque,0,static_cast<DWORD>(distantMax+1),derniereConf,0,static_cast<short>(av<-999?-999:av>999?999:av),0,
              maintenant?maintenant:1,heureAdverse?heureAdverse+(maintenant-heureRecue):0};
    if(derniereConf){const DWORD i=((derniereConf-1)/EMPREINTE_PAS)%16;e.empreinte=mesEmpreintes[i];}
    if(abandonMoi)e.pad=static_cast<short>(0x4000|((localPlace&1)<<13)|((abandonImageMoi-epoque)&0x1FFF));
    long p=ackDistant+1;if(localMax-p+1>static_cast<long>(MAX_MOTS))p=localMax-static_cast<long>(MAX_MOTS)+1;if(p>localMax)p=localMax;
    e.premiere=static_cast<DWORD>(p);e.n=static_cast<WORD>(localMax-p+1);
    memcpy(t,&e,sizeof(e));for(DWORD k=0;k<e.n;++k)memcpy(t+sizeof(e)+4*k,&local[(p+k)%NB],4);
    const DWORD taille=sizeof(e)+e.n*4u;
    if(!advSur)for(int i=0;i<nCand;++i)if(cand[i]!=adv)Envoyer(cand[i],t,taille,CANAL);
    if(!latenceEssai){if(Envoyer(adv,t,taille,CANAL))++sEnvoyes;return;}

    const DWORD now=GetTickCount();
    if(fileQueue-fileTete<64){Attente& a=fileEssai[fileQueue%64];a.due=now+latenceEssai;a.taille=taille;memcpy(a.b,t,taille);++fileQueue;}
    ViderFileEssai();
}

static void AbandonNatif(){
    if(!EnCombatSalon())return;
    const DWORD img=R32(RVA_NETCODE+8);
    if(InterlockedExchange(&demandeAbandonNatif,0) && !natifMoi){const int p=PlaceLocale();if(p<=1){natifImageMoi=static_cast<LONG>(img+60);natifPlaceMoi=p;InterlockedExchange(&natifMoi,1);
        Logf("Reseau : abandon demande (F5, netcode du jeu) : je perds les rounds restants (image du jeu %lu).",img+60);}}
    LONG place=-1;DWORD image=0;
    if(natifMoi && natifLui){place=0;image=static_cast<DWORD>(natifImageMoi>natifImageLui?natifImageMoi:natifImageLui);}
    else if(natifMoi){place=natifPlaceMoi;image=static_cast<DWORD>(natifImageMoi);} else if(natifLui){place=natifPlaceLui;image=static_cast<DWORD>(natifImageLui);}
    if(place<0 || img<image)return;
    __try{*reinterpret_cast<WORD*>(base+0xFD0540+place*0x6C8+0x2C)=0;*reinterpret_cast<DWORD*>(base+0xFCDE2C+4)=59;}__except(EXCEPTION_EXECUTE_HANDLER){}
}

static volatile LONG pretMoi;
static volatile LONG imageMoi,debutMoi;
static volatile LONG pretLui,imageLui,debutLui,pretLuiTick;
static DWORD debutConvenu,pretDepuis,surPlaceDepuis;
static volatile LONG apresDebutF,apresDebutTick;
static volatile LONG annulerMoi,annulerDepuis,annuleLui;
static void EnvoyerAnnonce(DWORD f){const int p=PlaceLocale();if(p>1)return;
    const DWORD m[5]={MAGIC_PRET,static_cast<DWORD>(p),f,static_cast<DWORD>(imageMoi),static_cast<DWORD>(debutMoi)};
    u64s c[MAXCAND];const int nc=LireCandidats(c);for(int i=0;i<nc;++i)Envoyer(c[i],m,sizeof(m),CANAL_POIGNEE);}
static void EnvoyerPret(){const LONG f=pretMoi;if(f){EnvoyerAnnonce(static_cast<DWORD>(f));return;}
    const LONG g=apresDebutF;if(g && GetTickCount()-static_cast<DWORD>(apresDebutTick)<=2000)EnvoyerAnnonce(static_cast<DWORD>(g));}
static void TicPoignee(){
    u64s c[MAXCAND];const int nc=LireCandidats(c);const int p=PlaceLocale();
    for(int g=0;g<32;++g){DWORD m[5];u64s de=0;const int lu=Recevoir(m,sizeof(m),CANAL_POIGNEE,&de);if(lu<0)break;
        bool membre=false;for(int i=0;i<nc;++i)if(c[i]==de)membre=true;
        if(!membre || lu!=20 || m[0]!=MAGIC_PRET || m[1]>1 || static_cast<int>(m[1])==p || !m[2])continue;
        if(m[2]&0x80000000u){const LONG a=static_cast<LONG>(m[2]&0x7FFFFFFFu);InterlockedExchange(&pretLui,0);
            if(InterlockedExchange(&annuleLui,a)!=a)Logf("Reseau : poignee de main : annulation recue de l'adversaire (%ld).",a);continue;}
        InterlockedExchange(&pretLuiTick,static_cast<LONG>(GetTickCount()));InterlockedExchange(&imageLui,static_cast<LONG>(m[3]&0x7FFFFFFFu));
        InterlockedExchange(&debutLui,static_cast<LONG>(m[4]&0x7FFFFFFFu));InterlockedExchange(&pretLui,static_cast<LONG>(m[2]));}
    EnvoyerPret();
    if(annulerMoi){if(GetTickCount()-static_cast<DWORD>(annulerDepuis)>3000)InterlockedExchange(&annulerMoi,0);
        else EnvoyerAnnonce(static_cast<DWORD>(annulerMoi)|0x80000000u);}
}
static bool figeParNous=false;
static void Degeler(){if(figeParNous){base[RVA_NETCODE+0x2C]=0;figeParNous=false;}}

static unsigned diagPoigneeLogs; static DWORD diagPoigneeTick;
static void DiagPoignee(const char* pourquoi,DWORD j,DWORD ph,u64s a,int p){
    if(!pretMoi || diagPoigneeLogs>=30 || GetTickCount()-diagPoigneeTick<1000)return;
    ++diagPoigneeLogs;diagPoigneeTick=GetTickCount();
    Logf("Reseau : DIAG poignee de main sautee (%s) : image %lu, phase du jeu %lu, adversaire %s, ma place %d, abandon %ld, mode combat %ld, en combat %d.",
        pourquoi,j,ph,a?"connu":"AUCUN",p,static_cast<long>(abandonne),static_cast<long>(modeCombat),EnCombatSalon()?1:0);}
enum { POIGNEE_NATIF=0, POIGNEE_DEBUT=1, POIGNEE_SUR_PLACE=2 };
static bool AnnonceFraiche(){return pretLui && GetTickCount()-static_cast<DWORD>(pretLuiTick)<=PRET_FRAIS_MS;}
static int Annuler(const char* pourquoi,DWORD j){
    const LONG f=debutConvenu?static_cast<LONG>(debutConvenu):pretMoi?pretMoi:static_cast<LONG>(j);
    InterlockedExchange(&pretMoi,0);InterlockedExchange(&debutMoi,0);
    InterlockedExchange(&annulerDepuis,static_cast<LONG>(GetTickCount()));InterlockedExchange(&annulerMoi,f);InterlockedExchange(&abandonne,1);
    Logf("Reseau : poignee de main : %s (image %lu, debut %lu) : netcode du jeu pour ce round.",pourquoi,j,debutConvenu);return POIGNEE_NATIF;}
static int Poignee(DWORD j){
    if(!pretMoi){InterlockedExchange(&apresDebutF,0);debutConvenu=0;surPlaceDepuis=0;pretDepuis=GetTickCount();InterlockedExchange(&debutMoi,0);InterlockedExchange(&annuleLui,0);
        InterlockedExchange(&imageMoi,static_cast<LONG>(j));InterlockedExchange(&pretMoi,static_cast<LONG>(j));
        Logf("Reseau : poignee de main : pret a l'image %lu (netcode du jeu en attendant).",j);}
    InterlockedExchange(&imageMoi,static_cast<LONG>(j));EnvoyerPret();
    if(annuleLui && !debutConvenu){InterlockedExchange(&annuleLui,0);return Annuler("l'adversaire a annule",j);}
    if(!debutConvenu){
        const bool frais=AnnonceFraiche();const LONG lui=imageLui;
        if(frais && PlaceLocale()==0 && labs(lui-static_cast<LONG>(j))<=POIGNEE_ECART_DECISION){
            debutConvenu=static_cast<DWORD>(lui>static_cast<LONG>(j)?lui:static_cast<LONG>(j))+MARGE_POIGNEE+static_cast<DWORD>(labs(lui-static_cast<LONG>(j)));InterlockedExchange(&debutMoi,static_cast<LONG>(debutConvenu));
            Logf("Reseau : poignee de main : adversaire a l'image %ld (moi %lu, attente %lu ms) : rollback a partir de l'image %lu.",lui,j,GetTickCount()-pretDepuis,debutConvenu);}
        else if(frais && PlaceLocale()==1 && debutLui){
            if(static_cast<DWORD>(debutLui)<j)return Annuler("debut recu deja passe",j);
            debutConvenu=static_cast<DWORD>(debutLui);InterlockedExchange(&debutMoi,debutLui);
            Logf("Reseau : poignee de main : debut recu de J1 : rollback a partir de l'image %lu (moi %lu, attente %lu ms).",debutConvenu,j,GetTickCount()-pretDepuis);}
        else if(GetTickCount()-pretDepuis>POIGNEE_MAX_MS)return Annuler("pas d'accord en 10 s",j);
        if(!debutConvenu)return POIGNEE_NATIF;
    }
    if(j<debutConvenu)return POIGNEE_NATIF;
    if(j>debutConvenu)return Annuler("image convenue deja passee",j);

    if(!surPlaceDepuis)surPlaceDepuis=GetTickCount();
    const bool pret=AnnonceFraiche() && static_cast<DWORD>(debutLui)==debutConvenu && imageLui+4>=static_cast<LONG>(j);
    if(!pret){if(annuleLui)return Annuler("l'adversaire a annule",j);
        const bool confirme=AnnonceFraiche() && static_cast<DWORD>(debutLui)==debutConvenu;
        if(GetTickCount()-surPlaceDepuis<(confirme?SUR_PLACE_CONFIRME_MS:SUR_PLACE_MAX_MS))return POIGNEE_SUR_PLACE;
        return Annuler(confirme?"adversaire pas a l'image convenue apres 1,5 s (debut confirme)":"adversaire pas a l'image convenue apres 0,3 s (debut pas confirme)",j);}
    Logf("Reseau : poignee de main : adversaire a l'image %ld, attente sur place %lu ms.",static_cast<long>(imageLui),GetTickCount()-surPlaceDepuis);
    InterlockedExchange(&apresDebutTick,static_cast<LONG>(GetTickCount()));InterlockedExchange(&apresDebutF,pretMoi);
    InterlockedExchange(&pretMoi,0);
    return POIGNEE_DEBUT;
}

typedef void (__thiscall* NetcodeFn)(void*,void*);
static void __fastcall NetcodeHook(void* self,void*,void* arg) {
    if(!combatDecide && EnCombatSalon()){
        LireIdLocal();
        combatDecide=true;const LONG m=enabled && Adversaire()!=0 && MembreNetcode()!=0;
        InterlockedExchange(&modeCombat,m);InterlockedExchange(&dm::on,m);
        Logf("Reseau : debut du combat : %s.",m?"adversaire avec le mod (scene par pas, calculs deterministes, rollback pendant les rounds)":"netcode du jeu seulement");
        {

            unsigned actifs=0,equipes=0;for(int f=0;f<16;++f){if(R8(0xF79EA8+0xD4+f*0x1C+0x16))++actifs;if(R8(0xF79EA8+0xD4+f*0x1C+0x18))++equipes;}
            Logf("Reseau : netcode du jeu : %lu membre(s) ; session : %u fiche(s), %u active(s), %u avec equipe ; ma place %d ; salon %ld membre(s).",
                R32(RVA_NETCODE+0xA0),static_cast<unsigned>(R8(0xF79EA8+0x29D)),actifs,equipes,PlaceLocale(),static_cast<long>(dernierEtat[0]));
        }
    }
    const DWORD j=lab::lastFrame+1;

    const DWORD ph=R32(RVA_PHASE);
    if(ph!=1 || !frontiereVue || !EnCombatSalon())debutPhase1=0xFFFFFFFF;else if(debutPhase1==0xFFFFFFFF)debutPhase1=j;
    const bool phase=frontiereVue && EnCombatSalon() && (ph==2 || (ph==1 && debutPhase1!=0xFFFFFFFF && j>=debutPhase1+30));
    {

        static bool grapheRound=false;

        const bool reprep=ph==2 && active && !lab::prepared && lab::sceneFrames>=2;
        if(ph==0 || ph==1 || (ph==2 && !active && !lab::prepared) || reprep){if(modeCombat && (!active || reprep) && !lab::prepared && EnCombatSalon())
            {cp::DecorGraphStep(!grapheRound,30000);grapheRound=true;}}
        else if(grapheRound){grapheRound=false;cp::DecorGraphDrop();}
    }
    if(!active)AbandonNatif();
    if(!phase){DiagPoignee("hors phase",j,ph,Adversaire(),PlaceLocale());Degeler();if(pretMoi)InterlockedExchange(&pretMoi,0);if(active){Terminer("phase terminee");rafaleFin=RAFALE_FIN;EnvoyerEntrees();if(rafaleLogs<5){++rafaleLogs;Logf("Reseau : fin de phase : mes dernieres entrees (jusqu'a l'image %ld) renvoyees pendant 1 s.",localMax);}}else if(rafaleFin){--rafaleFin;EnvoyerEntrees();}if(latenceEssai)ViderFileEssai();InterlockedExchange(&abandonne,0);reinterpret_cast<NetcodeFn>(base+RVA_NETCODE_FN)(self,arg);return;}
    if(active && InterlockedExchange(&demandeAbandon,0) && !abandonMoi){
        abandonMoi=true;abandonImageMoi=lab::lastFrame+60;Logf("Reseau : abandon demande (F5) : je perds les rounds restants (a partir de l'image %lu).",abandonImageMoi);}
    if(!active){
        const u64s a=Adversaire();const int p=PlaceLocale();
        if(abandonne || !modeCombat || !a || p>1 || !Reseau() || !enabled){DiagPoignee("conditions",j,ph,a,p);Degeler();reinterpret_cast<NetcodeFn>(base+RVA_NETCODE_FN)(self,arg);return;}
        const int al=R8(RVA_APP_PLACE+p),ad=R8(RVA_APP_PLACE+(1-p));
        if((al!=5 && al!=6) || (ad!=5 && ad!=6) || al==ad){InterlockedExchange(&abandonne,1);Logf("Reseau : REFUS : manettes du netcode inattendues (%d, %d).",al,ad);Degeler();reinterpret_cast<NetcodeFn>(base+RVA_NETCODE_FN)(self,arg);return;}

        if(ph!=2)DiagPoignee("phase du jeu differente de 2",j,ph,a,p);
        const int pg=ph==2?Poignee(j):POIGNEE_NATIF;
        if(pg==POIGNEE_SUR_PLACE){base[RVA_NETCODE+0x2C]=1;figeParNous=true;return;}
        Degeler();
        if(pg==POIGNEE_NATIF){reinterpret_cast<NetcodeFn>(base+RVA_NETCODE_FN)(self,arg);return;}
        Commencer(a,j);Accepter(adv);
    }

    const bool sansPrediction=!lab::resim && !lab::rollbackPlanned && (verrouCourant || !lab::prepared);
    if(static_cast<long>(j)>distantMax && sansPrediction) {

        static unsigned n;if(n<20){++n;Logf("Reseau : image %lu : entree pas encore la et moteur arrete (fin de round) : pas fige.",j);}
        base[RVA_NETCODE+0x2C]=1;InterlockedExchange(&lab::cutRest,1);++sAttentes;return;
    }

    if(sansPrediction && static_cast<long>(j)+1>distantMax)InterlockedExchange(&lab::cutRest,1);

    if(static_cast<long>(j)>localMax){const DWORD w=LireManette(localMax+1,static_cast<long>(j));
        for(long f=localMax+1;f<=static_cast<long>(j);++f)local[f%NB]=w;localMax=static_cast<long>(j);}
    const DWORD l=MotLocal(static_cast<long>(j)),lp=MotLocal(static_cast<long>(j)-1);
    const DWORD d=MotDistant(static_cast<long>(j)),dp=utilise[(j-1)%NB];
    utilise[j%NB]=d;
    {lab::In in={};memcpy(in.b,&d,4);lab::p2used[lab::K(j)]=in;}
    if(static_cast<long>(j)>distantMax)++sPredites;
    EcrireApp(appLocal,l,lp);EcrireApp(appDistant,d,dp);
    reinterpret_cast<void(__cdecl*)()>(base+RVA_COPIER)();
    base[RVA_NETCODE+0x2C]=0;
    ++sImages;
}

static void BeforeCopy(){
    if(!active)return;const long j=static_cast<long>(lab::lastFrame)+1;
    if(abandonMoi || abandonLui){DWORD place=0,image=0;PlaceAbandon(place,image);
        if(static_cast<DWORD>(j)>=image){const WORD zero=0;__try{*reinterpret_cast<WORD*>(base+0xFD0540+place*0x6C8+0x2C)=zero;

            *reinterpret_cast<DWORD*>(base+0xFCDE2C+4)=59;}__except(EXCEPTION_EXECUTE_HANDLER){}}}
    EcrireApp(appLocal,MotLocal(j-1),MotLocal(j-2));EcrireApp(appDistant,utilise[(j-1)%NB],utilise[(j-2)%NB]);
}

struct DetailEmp { DWORD img; float pos[6]; WORD vie[2]; DWORD aleaIdx,aleaCtr,aleaH; };
static DetailEmp details[32];
static void NoterDetail(DWORD x){DetailEmp& d=details[(x/EMPREINTE_PAS)%32];d.img=x;Copy(d.pos,base+RVA_POSITIONS,12);Copy(d.pos+3,base+RVA_POSITIONS+0x180,12);
    d.vie[0]=static_cast<WORD>(R32(RVA_JOUEURS+0x2C));d.vie[1]=static_cast<WORD>(R32(RVA_JOUEURS+0x6C8+0x2C));
    const DWORD a=reinterpret_cast<DWORD>(base+RVA_ALEA),ptr=R32(RVA_ALEA+0x9C0);d.aleaIdx=ptr>=a && ptr<=a+0x9C0?(ptr-a)/4:0xFFFF;d.aleaCtr=R32(RVA_ALEA+0x9C4);
    static BYTE t[0x9C0];Copy(t,base+RVA_ALEA,sizeof(t));d.aleaH=Fnv(2166136261u,t,sizeof(t));}
static void EcrireDetails(DWORD img){
    for(int k=10;k>=0;--k){const long f=static_cast<long>(img)-k*static_cast<long>(EMPREINTE_PAS);if(f<0)continue;const DetailEmp& d=details[(f/EMPREINTE_PAS)%32];if(d.img!=static_cast<DWORD>(f))continue;
        Logf("DETAIL EMPREINTE image %lu : J1 %.4f %.4f %.4f ; J2 %.4f %.4f %.4f ; vies %u %u ; alea indice %lu compteur %lu empreinte %08lX.",
            d.img,d.pos[0],d.pos[1],d.pos[2],d.pos[3],d.pos[4],d.pos[5],d.vie[0],d.vie[1],d.aleaIdx,d.aleaCtr,d.aleaH);}}

struct EtatEmp { DWORD img,nStage,vtStage; WORD rngIdx[6],rngCtr[6]; DWORD rngH[6]; BYTE raw[lab::RAWSZ]; BYTE stage[lab::STAGEMAX]; };
static EtatEmp etats[4];
static void NoterEtat(DWORD x){EtatEmp& e=etats[(x/EMPREINTE_PAS)%4];e.img=x;lab::ReadRaw(e.raw);
    e.nStage=lab::stageAddr && lab::stageSize<=lab::STAGEMAX?lab::stageSize&~3u:0;e.vtStage=lab::SceneVt();
    if(e.nStage)Copy(e.stage,reinterpret_cast<void*>(lab::stageAddr),e.nStage);
    if(suiviEtat){static const DWORD rngs[6]={0x20906E0,0x10844E8,0x2071378,0x2072A58,0x2070830,0x206FE68};
        for(int r=0;r<6;++r){static BYTE t[0x9C0];Copy(t,base+rngs[r],sizeof(t));e.rngH[r]=Fnv(2166136261u,t,sizeof(t));
            const DWORD a=reinterpret_cast<DWORD>(base+rngs[r]),ptr=R32(rngs[r]+0x9C0);e.rngIdx[r]=static_cast<WORD>(ptr>=a && ptr<=a+0x9C0?(ptr-a)/4:0xFFFF);e.rngCtr[r]=static_cast<WORD>(R32(rngs[r]+0x9C4));}}}
static void EcrireBloc(DWORD img,const char* nom,const BYTE* p,DWORD n){
    for(DWORD o=0;o<n;o+=64){char l[400];int m=_snprintf_s(l,sizeof l,_TRUNCATE,"ETAT image %lu %s +%04lX :",img,nom,o);if(m<0)continue;
        for(DWORD w=o;w<o+64 && w+4<=n;w+=4){DWORD v;memcpy(&v,p+w,4);
            const int k=v>=0x10000 && !(v&3) && cp::PointerLike(v)?_snprintf_s(l+m,sizeof l-m,_TRUNCATE," *"):_snprintf_s(l+m,sizeof l-m,_TRUNCATE," %04lX.%04lX",v>>16,v&0xFFFF);
            if(k>0)m+=k;}
        Log(l);}}
static void EcrireEtat(DWORD img){
    for(int k=1;k>=0;--k){const long f=static_cast<long>(img)-k*static_cast<long>(EMPREINTE_PAS);if(f<0)continue;const EtatEmp& e=etats[(f/EMPREINTE_PAS)%4];if(e.img!=static_cast<DWORD>(f))continue;
        Logf("ETAT image %lu : blocs joueurs J1 (+0000) / J2 (+06C8), secondaires (+0D90), logique (+1B20) ; scene %06lX (0x%lX octets).",e.img,e.vtStage,e.nStage);
        EcrireBloc(e.img,"joueurs",e.raw,lab::RAWSZ);if(e.nStage)EcrireBloc(e.img,"scene",e.stage,e.nStage);}}

static BYTE suiviRaw[lab::RAWSZ],suiviStage[lab::STAGEMAX];
static bool Adresse(DWORD v){return v>=0x10000 && !(v&3) && cp::PointerLike(v);}
static void SuiviDelta(DWORD img,const char* nom,const BYTE* avant,const BYTE* p,DWORD n){
    char l[400];int m=-1;unsigned k=0;
    for(DWORD w=0;w+4<=n;w+=4){DWORD a,v;memcpy(&a,avant+w,4);memcpy(&v,p+w,4);if(a==v)continue;
        if(m<0){m=_snprintf_s(l,sizeof l,_TRUNCATE,"SUIVI image %lu %s :",img,nom);if(m<0)return;}
        const int q=Adresse(v)?_snprintf_s(l+m,sizeof l-m,_TRUNCATE," +%04lX=*",w):_snprintf_s(l+m,sizeof l-m,_TRUNCATE," +%04lX=%04lX.%04lX",w,v>>16,v&0xFFFF);
        if(q>0)m+=q;
        if(++k==14){Log(l);m=-1;k=0;}}
    if(m>0)Log(l);}
static void Suivi(DWORD j){
    if(!suiviEtat)return;const EtatEmp& e=etats[(j/EMPREINTE_PAS)%4];if(e.img!=j)return;
    {char l[300];int m=_snprintf_s(l,sizeof l,_TRUNCATE,"SUIVI image %lu alea-effets :",j);
     for(int r=0;r<6 && m>0;++r){const int q=_snprintf_s(l+m,sizeof l-m,_TRUNCATE," %u/%u/%04lX",e.rngIdx[r],e.rngCtr[r],e.rngH[r]&0xFFFF);if(q>0)m+=q;}
     if(m>0)Log(l);}
    if(!suiviImg || e.nStage!=suiviN){Logf("SUIVI image %lu base : scene %06lX (0x%lX octets).",j,e.vtStage,e.nStage);EcrireBloc(j,"base-joueurs",e.raw,lab::RAWSZ);if(e.nStage)EcrireBloc(j,"base-scene",e.stage,e.nStage);}
    else{SuiviDelta(j,"joueurs",suiviRaw,e.raw,lab::RAWSZ);if(e.nStage)SuiviDelta(j,"scene",suiviStage,e.stage,e.nStage);}
    memcpy(suiviRaw,e.raw,lab::RAWSZ);memcpy(suiviStage,e.stage,lab::STAGEMAX);suiviImg=j;suiviN=e.nStage;}

static DWORD diagPasStage[lab::STAGEMAX/4]; static unsigned diagPasLignes;
static void DiagPas(DWORD x){
    const LONG e=sc::diagEvtImage;if(!sc::diagEvt || e<0 || diagPasLignes>=20000)return;
    if(x+2<static_cast<DWORD>(e) || x>static_cast<DWORD>(e)+60)return;
    const DWORD n=lab::stageAddr?lab::stageSize:0;
    if(diagPasEvt!=e){diagPasEvt=e;if(n)Copy(diagPasStage,reinterpret_cast<void*>(lab::stageAddr),n);}
    char g[160];sc::DiagRngTexte(g,sizeof g,false);
    char l[700];int m=_snprintf_s(l,sizeof l,_TRUNCATE,"DIAG PAS image %lu (%s) : generateurs %s ; scene :",x,lab::resim?"recalcul":lab::FramePredicted(x)?"predite":"confirmee",g);
    static DWORD cur[lab::STAGEMAX/4];unsigned k=0;
    if(n){Copy(cur,reinterpret_cast<void*>(lab::stageAddr),n);
        for(DWORD w=0;w<n/4 && m>0;++w){if(cur[w]==diagPasStage[w])continue;const DWORD v=cur[w];
            const int q=Adresse(v)?_snprintf_s(l+m,sizeof l-m,_TRUNCATE," +%04lX=*",w*4):_snprintf_s(l+m,sizeof l-m,_TRUNCATE," +%04lX=%04lX.%04lX",w*4,v>>16,v&0xFFFF);
            if(q>0)m+=q;if(++k>=24)break;}
        memcpy(diagPasStage,cur,n);}
    if(!k && m>0)_snprintf_s(l+m,sizeof l-m,_TRUNCATE," rien");
    ++diagPasLignes;Log(l);}
static void AtFrontier(){if(!active)return;const DWORD x=lab::lastFrame;
    if constexpr(kTest){posImg[x%NB]=x;Copy(posAt[x%NB],base+RVA_POSITIONS,12);Copy(posAt[x%NB]+3,base+RVA_POSITIONS+0x180,12);
        zoneAt[x%NB]=reinterpret_cast<DWORD(__cdecl*)()>(base+0x5964C0)();}
    NoterBis(x);GardeSansPhoto(x);
    if(x%EMPREINTE_PAS==0){empreintes[x%NB]=Empreinte();empreinteImage[x%NB]=x+1;if constexpr(kTest){NoterDetail(x);NoterEtat(x);}}if constexpr(kTest)DiagPas(x);}

static void OnConfirmed(DWORD j){
    if constexpr(kTest){
        const long d=static_cast<long>(j)-traceDe;
        if(active && traceDe>=0 && d>=0 && d<=300 && d%10==0 && posImg[j%NB]==j && traceLignes<5000){++traceLignes;const float* p=posAt[j%NB];
            Logf("TRANSITION image %lu (+%ld) : zone %lu, J1 %.2f %.2f %.2f, J2 %.2f %.2f %.2f.",j,d,zoneAt[j%NB],p[0],p[1],p[2],p[3],p[4],p[5]);}}
    if(active && bisCalc[j%NB].img==j+1){const DWORD pend=lab::ReplayPendingFrom();if(!pend || j<pend)bisConf[j%NB]=bisCalc[j%NB];}
    if(!active || j%EMPREINTE_PAS || empreinteImage[j%NB]!=j+1)return;
    {const DWORD pend=lab::ReplayPendingFrom();if(pend && j>=pend)return;}
    const DWORD i=(j/EMPREINTE_PAS)%16;mesEmpreintes[i]=empreintes[j%NB];mesImages[i]=j+1;derniereConf=j+1;Suivi(j);}

static bool UpdateHook() {
    if(!active)return false;
    if(!EnCombatSalon()){Terminer("hors combat");return false;}
    LirePaquets();
    if(!advSur && annuleLui && static_cast<DWORD>(annuleLui)==epoque){InterlockedExchange(&annuleLui,0);InterlockedExchange(&abandonne,1);
        Terminer("l'adversaire a manque l'image convenue : netcode du jeu pour ce round");return false;}
    const long j=static_cast<long>(lab::lastFrame)+1;

    if(lab::CinematicNow() && static_cast<DWORD>(j)>lab::cineLast)lab::cineLast=static_cast<DWORD>(j);
    const bool verrou=!lab::prepared || static_cast<DWORD>(j)<=lab::safeUntil || !base[0xFCDE54] || lab::NoPredictStage() || lab::NearCinematic(static_cast<DWORD>(j));
    {
        if(retardProvisoire && rttN-rttNDebut>=60){retardProvisoire=false;
            const DWORD a=RetardAuto();if(a<localDelay){Logf("Reseau : image %ld : aller-retour mesure (%.0f ms) : retard de la phase %lu -> %lu image(s) (AUTO, redescente sans trou).",j,rttLisse,localDelay,a);localDelay=a;}}
        DWORD r=localDelay;

        const bool fenetreCourte=lab::prepared && base[0xFCDE54] && static_cast<DWORD>(j)<=lab::safeUntil && lab::safeUntil-static_cast<DWORD>(j)<2 && lab::WinLen()==0 && !lab::NoPredictStage();
        if(verrou && rttLisse>0 && !fenetreCourte){const DWORD besoin=static_cast<DWORD>((rttLisse*0.5f+8.0f)/16.667f)+margeSansPrediction;if(besoin>r)r=besoin;}
        if(r>12)r=12;
        if(redescenteDouce && r<retardActuel)
            r=(j+static_cast<long>(retardActuel)==localMax+1 && MotManette()==local[localMax%NB])?retardActuel-1:retardActuel;
        if(r!=retardActuel){retardActuel=r;const DWORD now=GetTickCount();
            if(now-dernierRetardJournal>=1000){dernierRetardJournal=now;Logf("Reseau : image %ld : retard local %lu image(s) (aller-retour %.0f ms, %s).",j,r,rttLisse,verrou?"sans prediction":"avec prediction");}}
    }
    if(j+static_cast<long>(retardActuel)>localMax){
        const DWORD w=LireManette(localMax+1,j+static_cast<long>(retardActuel));
        for(long f=localMax+1;f<=j+static_cast<long>(retardActuel);++f)local[f%NB]=w;
        localMax=j+static_cast<long>(retardActuel);
    }
    else if(traceManette)++manetteSautes;
    EnvoyerEntrees();
    Bilan(false);
    if(verrou!=dernierVerrou){dernierVerrou=verrou;Logf("Reseau : image %ld : %s.",j,verrou?"sans prediction (entrees de l'adversaire attendues)":"prediction et rollback");}
    verrouCourant=verrou;
    bool attendre=verrou?j>distantMax:j-distantMax>static_cast<long>(avanceMax);
    if(static_cast<DWORD>(j)==verrouImage && j>distantMax)attendre=true;
    {
        const float mon=static_cast<float>(j-1-distantMax);
        syncEma=syncEma*0.9f+0.1f*((mon-static_cast<float>(avanceAdverse))*0.5f);
        if(!attendre && syncEma>=1.5f && static_cast<DWORD>(j)>=dernierePause+20){attendre=true;dernierePause=static_cast<DWORD>(j);syncEma-=1.0f;++sPauses;}
    }

    const bool finRound=advSur && cp::RoundDecided();
    if(attendre){++sAttentes;const DWORD lim=advSur?(finRound?ABANDON_FIN_MS:ABANDON_MS):ABANDON_DEBUT_MS;
        static unsigned attenteDebutLogs;if(!advSur && GetTickCount()-dernierRecu>ABANDON_MS && GetTickCount()-dernierRecu<=ABANDON_MS+20 && attenteDebutLogs<10){++attenteDebutLogs;Logf("Reseau : image %ld : aucun paquet de l'adversaire depuis 5 s en debut de phase (encore dans l'intro ?) : attente jusqu'a 20 s.",j);}
        if(GetTickCount()-dernierRecu>lim){InterlockedExchange(&abandonne,1);Terminer(advSur?(finRound?"round decide, plus rien recu de l'adversaire depuis 1 s":"plus rien recu de l'adversaire depuis 5 s"):"aucun paquet de l'adversaire en 20 s au debut de la phase");return false;}}
    return attendre;
}
static void Report(){}

static void FinCombat(){InterlockedExchange(&frontiereVue,0);abandonMoi=abandonLui=false;InterlockedExchange(&demandeAbandon,0);InterlockedExchange(&finCombatTick,static_cast<LONG>(GetTickCount()));
    InterlockedExchange(&natifMoi,0);InterlockedExchange(&natifLui,0);InterlockedExchange(&demandeAbandonNatif,0);if(!combatDecide)return;if(active)Terminer("fin du combat");combatDecide=false;InterlockedExchange(&modeCombat,0);InterlockedExchange(&dm::on,0);}
}
