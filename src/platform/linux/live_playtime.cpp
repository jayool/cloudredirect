#include "live_playtime.h"
#include "log.h"

#include <atomic>
#include <cstring>
#include <csetjmp>
#include <csignal>
#include <mutex>
#include <queue>
#include <sys/mman.h>
#include <unistd.h>

namespace LivePlaytime {

// Resolved steamclient.so entry points (file offsets from IDA, base added at
// runtime; sig-scanned below).
//   sub_182F530  writer:   (CUser*, Game** games, int count) -> syncTime
//   sub_182F840  wrapper:  (CUser*, Response_msg*) -> calls writer (games@+20,count@+12)
//   sub_2AC91C0  msg ctor: zeroes the CProtoBufMsg wrapper
//   sub_2ACA490  msg init: allocates the inner MessageLite body at wrapper[8]
//   sub_2AC8970  msg dtor
//   sub_1132CD0  registry int write (CUser+2648 obj, 3, key, val)
//   off_2E15B4C  CProtoBufMsg<...Response> typed wrapper vtable
//   off_2EA3FFC  CPlayer_GetLastPlayedTimes_Response descriptor
// Pointer-holding args are word-sized (4 bytes on i386, 8 on x86_64); counts
// stay int. uintptr_t keeps the 32-bit behaviour byte-identical.
using WriterFn   = int(*)(uintptr_t pUser, uintptr_t games, int count);
using WrapperFn  = int(*)(uintptr_t pUser, uintptr_t respMsg);
using MsgCtorFn  = void(*)(uintptr_t self, uintptr_t a2, uintptr_t a3);
using MsgInitFn  = void(*)(uintptr_t self);
using MsgDtorFn  = void(*)(uintptr_t self);

static uintptr_t g_base = 0;
static ParseFromArrayFn g_parseFromArray = nullptr;
static WrapperFn  g_wrapper = nullptr;   // sub_182F840
static MsgCtorFn  g_msgCtor = nullptr;
static MsgInitFn  g_msgInit = nullptr;
static MsgDtorFn  g_msgDtor = nullptr;
static uintptr_t  g_respWrapperVt = 0;   // base + 0x2E15B4C
static uintptr_t  g_respDescriptor = 0;  // base + 0x2EA3FFC

// Inner CPlayer_GetLastPlayedTimes_Response: games array ptr and element count.
// CProtoBufMsg wrapper: inner body pointer.
//   32-bit: games @ +20, count @ +12, inner at wrapper byte +0x20, array adj +4.
//   64-bit: games @ +0x20, count @ +0x18, inner at wrapper byte +0x38, array adj +8.
#if defined(__x86_64__)
static constexpr size_t RESP_OFF_GAMES_ARRAY = 0x20;
static constexpr size_t RESP_OFF_GAMES_COUNT = 0x18;
static constexpr size_t WRAP_INNER_OFF       = 0x38;  // wrapper+0x38 = m_pProtoBufBody
static constexpr size_t WRAP_BYTES           = 0x50;  // wrapper allocation (ctor writes up to +0x48)
static constexpr uintptr_t GAMES_ARRAY_ADJ   = 8;
#else
static constexpr size_t RESP_OFF_GAMES_ARRAY = 20;
static constexpr size_t RESP_OFF_GAMES_COUNT = 12;
static constexpr size_t WRAP_INNER_OFF       = 0x20;  // wrapper[8] = m_pProtoBufBody
static constexpr size_t WRAP_BYTES           = 48;    // wrapper allocation (ctor writes up to +0x1C)
static constexpr uintptr_t GAMES_ARRAY_ADJ   = 4;
#endif

// Captured CUser pointer (recorded by the writer-entry detour).
static std::atomic<uintptr_t> g_pUser{0};

// Signature scan; PIC call/add displacements are wildcarded.
struct Sig { const uint8_t* bytes; const uint8_t* mask; size_t len; };

#if defined(__x86_64__)
// steamrt64 client. Writer, msg ctor/init/dtor by SysV prologue (rip-relative
// lea displacements wildcarded; struct offsets kept).

// writer sub (rdi=CUser, rsi=games, edx=count):
//   41 57 41 56 41 55 41 54 55 53  push r15..rbx
//   48 83 ec 38                    sub rsp,0x38
//   64 48 8b 04 25 28 00 00 00     mov rax,fs:0x28
//   48 89 44 24 28                 mov [rsp+0x28],rax
//   31 c0 85 d2                    xor eax,eax; test edx,edx
static const uint8_t kWriterB[] = {0x41,0x57,0x41,0x56,0x41,0x55,0x41,0x54,0x55,0x53,0x48,0x83,0xEC,0x38,0x64,0x48,0x8B,0x04,0x25,0x28,0x00,0x00,0x00,0x48,0x89,0x44,0x24,0x28,0x31,0xC0,0x85,0xD2};
static const uint8_t kWriterM[] = {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1};

// msg ctor: 55 66 0f ef c0 81 ce 00 00 00 80 41 b9 01 00 00 00 53 48 8d 05 <disp>
static const uint8_t kCtorB[] = {0x55,0x66,0x0F,0xEF,0xC0,0x81,0xCE,0x00,0x00,0x00,0x80,0x41,0xB9,0x01,0x00,0x00,0x00,0x53,0x48,0x8D,0x05,0,0,0,0};
static const uint8_t kCtorM[] = {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0};

// msg init: 53 48 83 7f 38 00 48 89 fb 74 1c 48
static const uint8_t kInitB[] = {0x53,0x48,0x83,0x7F,0x38,0x00,0x48,0x89,0xFB,0x74,0x1C,0x48};
static const uint8_t kInitM[] = {1,1,1,1,1,1,1,1,1,1,1,1};

// msg dtor: 55 48 8d 05 <disp> 53 48 89 fb 48 83 ec 08 80 7f 19 00
static const uint8_t kDtorB[] = {0x55,0x48,0x8D,0x05,0,0,0,0,0x53,0x48,0x89,0xFB,0x48,0x83,0xEC,0x08,0x80,0x7F,0x19,0x00};
static const uint8_t kDtorM[] = {1,1,1,1,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1};
#else
// writer sub_182F530:  E8 ?? ?? ?? ?? 05 ?? ?? ?? ?? 55 89 E5 57 56 53 83 EC 3C 8B 4D 10 89 45 D0 85 C9 0F 8E
static const uint8_t kWriterB[] = {0xE8,0,0,0,0, 0x05,0,0,0,0, 0x55,0x89,0xE5,0x57,0x56,0x53,0x83,0xEC,0x3C,0x8B,0x4D,0x10,0x89,0x45,0xD0,0x85,0xC9,0x0F,0x8E};
static const uint8_t kWriterM[] = {1,0,0,0,0, 1,0,0,0,0, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1};

// Wrapper sub_182F840 loads games@[a2+20]/count@[a2+12]; Apply() inlines those,
// so only the writer + message helpers are sig-scanned.

// msg ctor sub_2AC91C0: 57 56 53 8B 74 24 10 E8 ?? ?? ?? ?? 81 C3 ?? ?? ?? ?? 83 EC 08 C7 46 04 00 00 00 00
static const uint8_t kCtorB[] = {0x57,0x56,0x53,0x8B,0x74,0x24,0x10,0xE8,0,0,0,0,0x81,0xC3,0,0,0,0,0x83,0xEC,0x08,0xC7,0x46,0x04,0,0,0,0};
static const uint8_t kCtorM[] = {1,1,1,1,1,1,1,1,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0};

// msg init sub_2ACA490: 56 53 E8 ?? ?? ?? ?? 81 C3 ?? ?? ?? ?? 83 EC 04 8B 74 24 10 8B 46 20 85 C0 74 22
static const uint8_t kInitB[] = {0x56,0x53,0xE8,0,0,0,0,0x81,0xC3,0,0,0,0,0x83,0xEC,0x04,0x8B,0x74,0x24,0x10,0x8B,0x46,0x20,0x85,0xC0,0x74,0x22};
static const uint8_t kInitM[] = {1,1,1,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1};

// msg dtor sub_2AC8970: 57 56 E8 ?? ?? ?? ?? 81 C6 ?? ?? ?? ?? 53 8B 5C 24 10 8B 53 28
static const uint8_t kDtorB[] = {0x57,0x56,0xE8,0,0,0,0,0x81,0xC6,0,0,0,0,0x53,0x8B,0x5C,0x24,0x10,0x8B,0x53,0x28};
static const uint8_t kDtorM[] = {1,1,1,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,1,1,1};
#endif

static void* ScanSig(uintptr_t base, size_t size, const uint8_t* b, const uint8_t* m, size_t len) {
    if (size < len) return nullptr;
    const uint8_t* s = (const uint8_t*)base;
    const uint8_t* end = s + size - len;
    for (; s <= end; ++s) {
        bool ok = true;
        for (size_t i = 0; i < len; ++i)
            if (m[i] && s[i] != b[i]) { ok = false; break; }
        if (ok) return (void*)s;
    }
    return nullptr;
}

// Crash guard: a layout mismatch in the parse/writer calls faults to SIGSEGV;
// convert it to a skipped update instead of a crash.
static sigjmp_buf g_jmp;
static volatile sig_atomic_t g_inCall = 0;
static void CrashHandler(int sig) {
    if (g_inCall) siglongjmp(g_jmp, sig);
    raise(sig);
}
class CallGuard {
public:
    CallGuard() {
        struct sigaction sa = {};
        sa.sa_handler = CrashHandler;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = SA_RESETHAND;
        sigaction(SIGSEGV, &sa, &m_segv);
        sigaction(SIGBUS, &sa, &m_bus);
        g_inCall = 1;
    }
    ~CallGuard() {
        g_inCall = 0;
        sigaction(SIGSEGV, &m_segv, nullptr);
        sigaction(SIGBUS, &m_bus, nullptr);
    }
private:
    struct sigaction m_segv = {};
    struct sigaction m_bus = {};
};

// CUser-capture detour on the writer entry.
//   32-bit (__cdecl): the PIC thunk + frame setup occupy the first bytes, so we
//   detour at +0x0D and read CUser from [ebp+8].
//   64-bit (SysV): no PIC thunk; detour at the entry and read CUser from rdi.
#if defined(__x86_64__)
static constexpr size_t WRITER_PROLOGUE = 0;    // detour at entry
static constexpr size_t WRITER_STOLEN   = 14;   // 6 pushes + sub rsp,0x38
#else
static constexpr size_t WRITER_PROLOGUE = 0x0D; // detour point offset
static constexpr size_t WRITER_STOLEN   = 6;    // 57 56 53 83 EC 3C
#endif
static constexpr size_t WRITER_RESUME   = WRITER_PROLOGUE + WRITER_STOLEN;

static std::atomic<bool> g_captureInstalled{false};
static uint8_t* g_writerStart = nullptr;
static uint8_t* g_hookPoint = nullptr;
static uint8_t  g_savedBytes[16];
static size_t   g_savedLen = 0;
static uint8_t* g_trampoline = nullptr;

// Recorded on the writer's natural entry (32: [ebp+8]; 64: rdi).
extern "C" void LivePlaytime_CaptureUser(uintptr_t pUser) {
    if (pUser && !g_pUser.load(std::memory_order_acquire)) {
        g_pUser.store(pUser, std::memory_order_release);
        LOG("[Stats] Captured CUser=%p for live playtime updates", (void*)pUser);
    }
}

static bool MakeWritable(void* addr, size_t len) {
    long ps = sysconf(_SC_PAGESIZE);
    uintptr_t page = (uintptr_t)addr & ~(uintptr_t)(ps - 1);
    uintptr_t endA = (uintptr_t)addr + len;
    size_t pl = ((endA - page) + (ps - 1)) & ~(size_t)(ps - 1);
    return mprotect((void*)page, pl, PROT_READ | PROT_WRITE | PROT_EXEC) == 0;
}

// Trampoline: call the capture hook with CUser, then run the stolen prologue
// and resume.
#if defined(__x86_64__)
//   push rdi/rsi/rax/rcx/rdx/r8..r11   (rdi = CUser = arg1, kept live)
//   movabs rax, CaptureUser ; call rax
//   pop  (reverse)
//   <stolen 14>             ; 6 pushes + sub rsp,0x38
//   jmp qword [rip+0] ; .quad writer+WRITER_STOLEN   (register-free)
static bool BuildTrampoline(uint8_t* hookPoint) {
    long ps = sysconf(_SC_PAGESIZE);
    g_trampoline = (uint8_t*)mmap(nullptr, ps, PROT_READ | PROT_WRITE | PROT_EXEC,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (g_trampoline == MAP_FAILED) { g_trampoline = nullptr; return false; }

    uint8_t* p = g_trampoline;
    auto emit = [&](std::initializer_list<uint8_t> b) { for (uint8_t x : b) *p++ = x; };
    auto emit64 = [&](uint64_t v) { for (int i = 0; i < 8; ++i) { *p++ = v & 0xFF; v >>= 8; } };

    emit({0x57, 0x56, 0x50, 0x51, 0x52});           // push rdi,rsi,rax,rcx,rdx
    emit({0x41,0x50, 0x41,0x51, 0x41,0x52, 0x41,0x53}); // push r8,r9,r10,r11
    emit({0x48, 0xB8}); emit64((uint64_t)(uintptr_t)&LivePlaytime_CaptureUser); // movabs rax, hook
    emit({0xFF, 0xD0});                             // call rax
    emit({0x41,0x5B, 0x41,0x5A, 0x41,0x59, 0x41,0x58}); // pop r11,r10,r9,r8
    emit({0x5A, 0x59, 0x58, 0x5E, 0x5F});           // pop rdx,rcx,rax,rsi,rdi

    memcpy(p, hookPoint, WRITER_STOLEN);            // stolen prologue
    p += WRITER_STOLEN;

    uintptr_t resume = (uintptr_t)g_writerStart + WRITER_RESUME;
    emit({0xFF, 0x25, 0x00, 0x00, 0x00, 0x00});     // jmp qword [rip+0]
    emit64((uint64_t)resume);                       // .quad resume (no register touched)
    return true;
}
#else
// Trampoline: run stolen bytes, then read CUser from [ebp+8] and call the
// capture hook, then resume. ebp is already valid at the hook point.
//   <stolen: push edi; push esi; push ebx; sub esp,0x3C>
//   pushad
//   push dword [ebp+8]        ; a1 = CUser
//   mov  eax, LivePlaytime_CaptureUser
//   call eax
//   add  esp, 4
//   popad
//   push <resume>
//   ret
static bool BuildTrampoline(uint8_t* hookPoint) {
    long ps = sysconf(_SC_PAGESIZE);
    g_trampoline = (uint8_t*)mmap(nullptr, ps, PROT_READ | PROT_WRITE | PROT_EXEC,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (g_trampoline == MAP_FAILED) { g_trampoline = nullptr; return false; }

    uint8_t* p = g_trampoline;
    auto emit = [&](std::initializer_list<uint8_t> b) { for (uint8_t x : b) *p++ = x; };
    auto emit32 = [&](uint32_t v) { *p++=v&0xFF; *p++=(v>>8)&0xFF; *p++=(v>>16)&0xFF; *p++=(v>>24)&0xFF; };

    memcpy(p, hookPoint, WRITER_STOLEN);  // stolen prologue insns
    p += WRITER_STOLEN;

    emit({0x60});                                   // pushad
    emit({0xFF, 0x75, 0x08});                       // push dword [ebp+8]  (CUser)
    emit({0xB8}); emit32((uint32_t)(uintptr_t)&LivePlaytime_CaptureUser); // mov eax, hook
    emit({0xFF, 0xD0});                             // call eax
    emit({0x83, 0xC4, 0x04});                       // add esp, 4
    emit({0x61});                                   // popad

    uintptr_t resume = (uintptr_t)g_writerStart + WRITER_RESUME;
    emit({0x68}); emit32((uint32_t)resume);         // push resume
    emit({0xC3});                                   // ret
    return true;
}
#endif

// Resolve vtable and descriptor from RTTI + code analysis (survives Steam updates).
// 1. Find RTTI typestring for CProtoBufMsg<...Response> in .rodata
// 2. Scan .data.rel.ro for typeinfo (ptr to typestring at offset +4)
// 3. Scan .data.rel.ro for vtable header ({0, typeinfo_ptr}) -> vptr = header + 8
// 4. Find wrapper function that stores the vptr, extract descriptor from wrapper[1] store
static bool ResolveVtableAndDescriptor(uintptr_t base, size_t size) {
    // Step 1: find the RTTI name string
    static const char kRttiName[] = "12CProtoBufMsgI35CPlayer_GetLastPlayedTimes_ResponseE";
    const uint8_t* s = (const uint8_t*)base;
    const uint8_t* end = s + size - sizeof(kRttiName);
    uintptr_t nameAddr = 0;
    for (const uint8_t* p = s; p <= end; ++p) {
        if (memcmp(p, kRttiName, sizeof(kRttiName) - 1) == 0) {
            nameAddr = (uintptr_t)p;
            break;
        }
    }
    if (!nameAddr) {
        LOG("[Stats] LivePlaytime: RTTI name string not found");
        return false;
    }

    // Step 2: find typeinfo (scan for a word-sized pointer to nameAddr).
    // Pointers/vtable slots are word-sized: 4 bytes on i386, 8 on x86_64.
    constexpr size_t W = sizeof(uintptr_t);
    uintptr_t tiAddr = 0;
    for (const uint8_t* p = s; p + W <= end; p += W) {
        if (*(const uintptr_t*)p == nameAddr) {
            tiAddr = (uintptr_t)p - W; // typeinfo = { vptr_to_typeinfo_class, name_ptr }
            break;
        }
    }
    if (!tiAddr) {
        LOG("[Stats] LivePlaytime: typeinfo not found for RTTI name at %p", (void*)nameAddr);
        return false;
    }

    // Step 3: find vtable header ({offset_to_top=0, typeinfo_ptr=tiAddr})
    uintptr_t vptr = 0;
    for (const uint8_t* p = s + W; p + W <= end; p += W) {
        if (*(const uintptr_t*)p == tiAddr && *(const uintptr_t*)(p - W) == 0) {
            vptr = (uintptr_t)p + W; // skip past typeinfo_ptr -> first vfunc slot
            break;
        }
    }
    if (!vptr) {
        LOG("[Stats] LivePlaytime: vtable not found for typeinfo at %p", (void*)tiAddr);
        return false;
    }
    g_respWrapperVt = vptr;
    LOG("[Stats] LivePlaytime: RTTI-resolved vptr=%p (typeinfo=%p)", (void*)vptr, (void*)tiAddr);

    // Step 4: find descriptor pointer. The CProtoBufMsg wrapper stores
    // [0]=wrapper_vptr, [1]=&raw_response_vptr. Resolve the raw Response class's
    // vptr from its RTTI, then scan .data.rel.ro for a pointer to it.
    static const char kRawRttiName[] = "35CPlayer_GetLastPlayedTimes_Response";
    uintptr_t rawNameAddr = 0;
    for (const uint8_t* p = s; p <= end - sizeof(kRawRttiName); ++p) {
        if (memcmp(p, kRawRttiName, sizeof(kRawRttiName) - 1) == 0) {
            // Distinguish from the CProtoBufMsg wrapper's RTTI
            if (p > s && *(p - 1) == 'I') continue; // "...I35CPlayer..." is the wrapper
            rawNameAddr = (uintptr_t)p;
            break;
        }
    }
    if (!rawNameAddr) {
        LOG("[Stats] LivePlaytime: raw Response RTTI name not found");
        return false;
    }

    // Find raw typeinfo (word pointer to rawNameAddr at the name slot of typeinfo)
    uintptr_t rawTiAddr = 0;
    for (const uint8_t* p = s; p + W <= end; p += W) {
        if (*(const uintptr_t*)p == rawNameAddr) {
            rawTiAddr = (uintptr_t)p - W;
            break;
        }
    }
    if (!rawTiAddr) {
        LOG("[Stats] LivePlaytime: raw Response typeinfo not found");
        return false;
    }

    // Find raw vtable header ({0, rawTiAddr}) -> raw vptr = header + 2 words
    uintptr_t rawVptr = 0;
    for (const uint8_t* p = s + W; p + W <= end; p += W) {
        if (*(const uintptr_t*)p == rawTiAddr && *(const uintptr_t*)(p - W) == 0) {
            rawVptr = (uintptr_t)p + W;
            break;
        }
    }
    if (!rawVptr) {
        LOG("[Stats] LivePlaytime: raw Response vtable not found");
        return false;
    }

    // Descriptor = pointer in .data.rel.ro whose value is rawVptr
    uintptr_t descAddr = 0;
    for (const uint8_t* p = s; p + W <= end; p += W) {
        if (*(const uintptr_t*)p == rawVptr && (uintptr_t)p != (rawVptr - W)) {
            // Skip the vtable's own typeinfo-neighbour slot.
            descAddr = (uintptr_t)p;
            break;
        }
    }
    if (!descAddr) {
        LOG("[Stats] LivePlaytime: descriptor pointer not found for raw vptr %p", (void*)rawVptr);
        return false;
    }
    g_respDescriptor = descAddr;
    LOG("[Stats] LivePlaytime: RTTI-resolved descriptor=%p (rawVptr=%p)", (void*)descAddr, (void*)rawVptr);
    return true;
}

bool Resolve(uintptr_t base, size_t size, ParseFromArrayFn parse) {
    g_base = base;
    g_parseFromArray = parse;

    void* writer = ScanSig(base, size, kWriterB, kWriterM, sizeof(kWriterB));
    void* ctor   = ScanSig(base, size, kCtorB,   kCtorM,   sizeof(kCtorB));
    void* init   = ScanSig(base, size, kInitB,   kInitM,   sizeof(kInitB));
    void* dtor   = ScanSig(base, size, kDtorB,   kDtorM,   sizeof(kDtorB));

    if (!writer || !ctor || !init || !dtor) {
        LOG("[Stats] LivePlaytime: signature scan incomplete (writer=%p ctor=%p init=%p dtor=%p) -- live UI updates disabled",
            writer, ctor, init, dtor);
        return false;
    }

    g_writerStart = (uint8_t*)writer;
    g_msgCtor = (MsgCtorFn)ctor;
    g_msgInit = (MsgInitFn)init;
    g_msgDtor = (MsgDtorFn)dtor;

    if (!ResolveVtableAndDescriptor(base, size)) {
        LOG("[Stats] LivePlaytime: vtable/descriptor resolution failed -- live UI updates disabled");
        return false;
    }

    LOG("[Stats] LivePlaytime resolved: writer=%p ctor=%p init=%p dtor=%p",
        writer, ctor, init, dtor);
    return true;
}

bool InstallUserCapture() {
    if (!g_writerStart) return false;
    bool expected = false;
    if (!g_captureInstalled.compare_exchange_strong(expected, true)) return true;

    g_hookPoint = g_writerStart + WRITER_PROLOGUE;
    if (!BuildTrampoline(g_hookPoint)) {
        g_captureInstalled.store(false);
        return false;
    }
    g_savedLen = WRITER_STOLEN;
    memcpy(g_savedBytes, g_hookPoint, g_savedLen);
    if (!MakeWritable(g_hookPoint, g_savedLen)) {
        g_captureInstalled.store(false);
        return false;
    }
#if defined(__x86_64__)
    // Absolute indirect jmp (ff 25 <rip+0> + imm64 = 14 bytes == WRITER_STOLEN).
    uint64_t dst = (uint64_t)(uintptr_t)g_trampoline;
    g_hookPoint[0] = 0xFF; g_hookPoint[1] = 0x25;
    g_hookPoint[2] = 0x00; g_hookPoint[3] = 0x00; g_hookPoint[4] = 0x00; g_hookPoint[5] = 0x00;
    memcpy(g_hookPoint + 6, &dst, 8);
#else
    int32_t rel = (int32_t)((uintptr_t)g_trampoline - ((uintptr_t)g_hookPoint + 5));
    g_hookPoint[0] = 0xE9;
    memcpy(g_hookPoint + 1, &rel, 4);
    for (size_t i = 5; i < g_savedLen; ++i) g_hookPoint[i] = 0x90; // nop pad
#endif
    __builtin___clear_cache((char*)g_hookPoint, (char*)g_hookPoint + g_savedLen);
    LOG("[Stats] LivePlaytime CUser-capture detour installed at %p", g_hookPoint);
    return true;
}

void RemoveUserCapture() {
    if (!g_captureInstalled.load(std::memory_order_acquire)) return;
    if (g_hookPoint && MakeWritable(g_hookPoint, g_savedLen)) {
        memcpy(g_hookPoint, g_savedBytes, g_savedLen);
        __builtin___clear_cache((char*)g_hookPoint, (char*)g_hookPoint + g_savedLen);
    }
    g_captureInstalled.store(false, std::memory_order_release);
}

bool Ready() {
    return g_msgCtor && g_msgInit && g_msgDtor && g_parseFromArray &&
           g_pUser.load(std::memory_order_acquire) != 0;
}

void Apply(const std::vector<uint8_t>& respBody) {
    if (respBody.empty() || !Ready()) return;
    uintptr_t pUser = g_pUser.load(std::memory_order_acquire);

    // CProtoBufMsg<CPlayer_GetLastPlayedTimes_Response> on the stack: ctor zeroes
    // it, word[0]=typed vtable, word[1]=descriptor, init allocates the inner
    // MessageLite body at wrapper+WRAP_INNER_OFF.
    alignas(uintptr_t) uint8_t wrapper[WRAP_BYTES] = {0};
    uintptr_t self = (uintptr_t)wrapper;

    CallGuard guard;
    if (sigsetjmp(g_jmp, 1) != 0) {
        LOG("[Stats] LivePlaytime::Apply crashed in steamclient call -- skipped");
        return;
    }

    g_msgCtor(self, 0, 0);
    *(uintptr_t*)(wrapper + 0)                 = g_respWrapperVt;
    *(uintptr_t*)(wrapper + sizeof(uintptr_t)) = g_respDescriptor;
    g_msgInit(self);

    uintptr_t inner = *(uintptr_t*)(wrapper + WRAP_INNER_OFF);
    if (!inner) {
        LOG("[Stats] LivePlaytime::Apply: inner body alloc failed");
        return;
    }

    if (!g_parseFromArray((void*)inner, respBody.data(), (int)respBody.size())) {
        LOG("[Stats] LivePlaytime::Apply: ParseFromArray failed (%zu bytes)", respBody.size());
        g_msgDtor(self);
        return;
    }

    // wrapper logic: v = *(inner + GAMES_ARRAY); if (v) v += ADJ;
    //                writer(pUser, v, *(inner + GAMES_COUNT)).
    uintptr_t arrayBase = *(uintptr_t*)((uint8_t*)inner + RESP_OFF_GAMES_ARRAY);
    int       count     = *(int*)((uint8_t*)inner + RESP_OFF_GAMES_COUNT);
    uintptr_t games     = arrayBase ? (arrayBase + GAMES_ARRAY_ADJ) : 0;

    if (games && count > 0) {
        auto writer = (WriterFn)(g_writerStart);
        writer(pUser, games, count);
        LOG("[Stats] LivePlaytime::Apply: pushed %d game(s) to live client map", count);
    } else {
        LOG("[Stats] LivePlaytime::Apply: no games parsed (count=%d)", count);
    }

    g_msgDtor(self);
}

// ── Net-thread-safe queue ──────────────────────────────────────────────────
static std::queue<std::vector<uint8_t>> g_queue;
static std::mutex g_queueMutex;

void Queue(const std::vector<uint8_t>& respBody) {
    if (respBody.empty()) return;
    std::lock_guard<std::mutex> lock(g_queueMutex);
    g_queue.push(respBody);
}

void DrainOnNetThread() {
    if (!Ready()) return;
    std::vector<std::vector<uint8_t>> batch;
    {
        std::lock_guard<std::mutex> lock(g_queueMutex);
        while (!g_queue.empty()) {
            batch.push_back(std::move(g_queue.front()));
            g_queue.pop();
        }
    }
    for (auto& body : batch)
        Apply(body);
}

} // namespace LivePlaytime
