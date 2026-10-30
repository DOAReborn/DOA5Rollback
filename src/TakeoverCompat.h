#pragma once
#ifdef _MSC_VER
#define RT_TRY    __try
#define RT_EXCEPT __except(EXCEPTION_EXECUTE_HANDLER)
#define RT_ASM(name)
#define RT_THREAD __declspec(thread)
#else
#include <setjmp.h>
#define RT_ASM(name) __asm__(name) __attribute__((used))
#define RT_THREAD __thread
namespace rtguard {
    struct Frame { jmp_buf jb; Frame* prev; };
    static __thread Frame* top=nullptr;
    static PVOID handler=nullptr;
    static LONG CALLBACK OnException(EXCEPTION_POINTERS* e) {
        const DWORD c=e->ExceptionRecord->ExceptionCode;
        if(!top||(c!=EXCEPTION_ACCESS_VIOLATION&&c!=EXCEPTION_ILLEGAL_INSTRUCTION&&c!=EXCEPTION_PRIV_INSTRUCTION&&
                  c!=EXCEPTION_INT_DIVIDE_BY_ZERO&&c!=EXCEPTION_ARRAY_BOUNDS_EXCEEDED&&c!=EXCEPTION_DATATYPE_MISALIGNMENT))
            return EXCEPTION_CONTINUE_SEARCH;
        Frame* f=top; top=f->prev; longjmp(f->jb,1);
    }
    struct Guard {
        Frame f; int n=0;
        Guard(){ if(!handler) handler=AddVectoredExceptionHandler(1,OnException); f.prev=top; top=&f; }
        ~Guard(){ if(top==&f) top=f.prev; }
        bool once(){ return n++==0; }
    };
}
#define RT_TRY    for(rtguard::Guard _rtg; _rtg.once(); ) if(!setjmp(_rtg.f.jb))
#define RT_EXCEPT else
#endif
