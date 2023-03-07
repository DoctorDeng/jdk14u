/*
 * Copyright (c) 1998, 2019, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "classfile/vmSymbols.hpp"
#include "jfr/jfrEvents.hpp"
#include "jfr/support/jfrThreadId.hpp"
#include "logging/log.hpp"
#include "logging/logStream.hpp"
#include "memory/allocation.inline.hpp"
#include "memory/resourceArea.hpp"
#include "oops/markWord.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/atomic.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/interfaceSupport.inline.hpp"
#include "runtime/mutexLocker.hpp"
#include "runtime/objectMonitor.hpp"
#include "runtime/objectMonitor.inline.hpp"
#include "runtime/orderAccess.hpp"
#include "runtime/osThread.hpp"
#include "runtime/safepointMechanism.inline.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/thread.inline.hpp"
#include "services/threadService.hpp"
#include "utilities/dtrace.hpp"
#include "utilities/macros.hpp"
#include "utilities/preserveException.hpp"
#if INCLUDE_JFR
#include "jfr/support/jfrFlush.hpp"
#endif

#ifdef DTRACE_ENABLED

// Only bother with this argument setup if dtrace is available
// TODO-FIXME: probes should not fire when caller is _blocked.  assert() accordingly.


#define DTRACE_MONITOR_PROBE_COMMON(obj, thread)                           \
  char* bytes = NULL;                                                      \
  int len = 0;                                                             \
  jlong jtid = SharedRuntime::get_java_tid(thread);                        \
  Symbol* klassname = ((oop)obj)->klass()->name();                         \
  if (klassname != NULL) {                                                 \
    bytes = (char*)klassname->bytes();                                     \
    len = klassname->utf8_length();                                        \
  }

#define DTRACE_MONITOR_WAIT_PROBE(monitor, obj, thread, millis)            \
  {                                                                        \
    if (DTraceMonitorProbes) {                                             \
      DTRACE_MONITOR_PROBE_COMMON(obj, thread);                            \
      HOTSPOT_MONITOR_WAIT(jtid,                                           \
                           (monitor), bytes, len, (millis));               \
    }                                                                      \
  }

#define HOTSPOT_MONITOR_contended__enter HOTSPOT_MONITOR_CONTENDED_ENTER
#define HOTSPOT_MONITOR_contended__entered HOTSPOT_MONITOR_CONTENDED_ENTERED
#define HOTSPOT_MONITOR_contended__exit HOTSPOT_MONITOR_CONTENDED_EXIT
#define HOTSPOT_MONITOR_notify HOTSPOT_MONITOR_NOTIFY
#define HOTSPOT_MONITOR_notifyAll HOTSPOT_MONITOR_NOTIFYALL

#define DTRACE_MONITOR_PROBE(probe, monitor, obj, thread)                  \
  {                                                                        \
    if (DTraceMonitorProbes) {                                             \
      DTRACE_MONITOR_PROBE_COMMON(obj, thread);                            \
      HOTSPOT_MONITOR_##probe(jtid,                                        \
                              (uintptr_t)(monitor), bytes, len);           \
    }                                                                      \
  }

#else //  ndef DTRACE_ENABLED

#define DTRACE_MONITOR_WAIT_PROBE(obj, thread, millis, mon)    {;}
#define DTRACE_MONITOR_PROBE(probe, obj, thread, mon)          {;}

#endif // ndef DTRACE_ENABLED

// Tunables ...
// The knob* variables are effectively final.  Once set they should
// never be modified hence.  Consider using __read_mostly with GCC.

int ObjectMonitor::Knob_SpinLimit    = 5000;    // derived by an external tool -

static int Knob_Bonus               = 100;     // spin success bonus
static int Knob_BonusB              = 100;     // spin success bonus
static int Knob_Penalty             = 200;     // spin failure penalty
static int Knob_Poverty             = 1000;
static int Knob_FixedSpin           = 0;
static int Knob_PreSpin             = 10;      // 20-100 likely better

DEBUG_ONLY(static volatile bool InitDone = false;)

// -----------------------------------------------------------------------------
// Theory of operations -- Monitors lists, thread residency, etc:
//
// * A thread acquires ownership of a monitor by successfully
//   CAS()ing the _owner field from null to non-null.
//
// * Invariant: A thread appears on at most one monitor list --
//   cxq, EntryList or WaitSet -- at any one time.
//
// * Contending threads "push" themselves onto the cxq with CAS
//   and then spin/park.
//
// * After a contending thread eventually acquires the lock it must
//   dequeue itself from either the EntryList or the cxq.
//
// * The exiting thread identifies and unparks an "heir presumptive"
//   tentative successor thread on the EntryList.  Critically, the
//   exiting thread doesn't unlink the successor thread from the EntryList.
//   After having been unparked, the wakee will recontend for ownership of
//   the monitor.   The successor (wakee) will either acquire the lock or
//   re-park itself.
//
//   Succession is provided for by a policy of competitive handoff.
//   The exiting thread does _not_ grant or pass ownership to the
//   successor thread.  (This is also referred to as "handoff" succession").
//   Instead the exiting thread releases ownership and possibly wakes
//   a successor, so the successor can (re)compete for ownership of the lock.
//   If the EntryList is empty but the cxq is populated the exiting
//   thread will drain the cxq into the EntryList.  It does so by
//   by detaching the cxq (installing null with CAS) and folding
//   the threads from the cxq into the EntryList.  The EntryList is
//   doubly linked, while the cxq is singly linked because of the
//   CAS-based "push" used to enqueue recently arrived threads (RATs).
//
// * Concurrency invariants:
//
//   -- only the monitor owner may access or mutate the EntryList.
//      The mutex property of the monitor itself protects the EntryList
//      from concurrent interference.
//   -- Only the monitor owner may detach the cxq.
//
// * The monitor entry list operations avoid locks, but strictly speaking
//   they're not lock-free.  Enter is lock-free, exit is not.
//   For a description of 'Methods and apparatus providing non-blocking access
//   to a resource,' see U.S. Pat. No. 7844973.
//
// * The cxq can have multiple concurrent "pushers" but only one concurrent
//   detaching thread.  This mechanism is immune from the ABA corruption.
//   More precisely, the CAS-based "push" onto cxq is ABA-oblivious.
//
// * Taken together, the cxq and the EntryList constitute or form a
//   single logical queue of threads stalled trying to acquire the lock.
//   We use two distinct lists to improve the odds of a constant-time
//   dequeue operation after acquisition (in the ::enter() epilogue) and
//   to reduce heat on the list ends.  (c.f. Michael Scott's "2Q" algorithm).
//   A key desideratum is to minimize queue & monitor metadata manipulation
//   that occurs while holding the monitor lock -- that is, we want to
//   minimize monitor lock holds times.  Note that even a small amount of
//   fixed spinning will greatly reduce the # of enqueue-dequeue operations
//   on EntryList|cxq.  That is, spinning relieves contention on the "inner"
//   locks and monitor metadata.
//
//   Cxq points to the set of Recently Arrived Threads attempting entry.
//   Because we push threads onto _cxq with CAS, the RATs must take the form of
//   a singly-linked LIFO.  We drain _cxq into EntryList  at unlock-time when
//   the unlocking thread notices that EntryList is null but _cxq is != null.
//
//   The EntryList is ordered by the prevailing queue discipline and
//   can be organized in any convenient fashion, such as a doubly-linked list or
//   a circular doubly-linked list.  Critically, we want insert and delete operations
//   to operate in constant-time.  If we need a priority queue then something akin
//   to Solaris' sleepq would work nicely.  Viz.,
//   http://agg.eng/ws/on10_nightly/source/usr/src/uts/common/os/sleepq.c.
//   Queue discipline is enforced at ::exit() time, when the unlocking thread
//   drains the cxq into the EntryList, and orders or reorders the threads on the
//   EntryList accordingly.
//
//   Barring "lock barging", this mechanism provides fair cyclic ordering,
//   somewhat similar to an elevator-scan.
//
// * The monitor synchronization subsystem avoids the use of native
//   synchronization primitives except for the narrow platform-specific
//   park-unpark abstraction.  See the comments in os_solaris.cpp regarding
//   the semantics of park-unpark.  Put another way, this monitor implementation
//   depends only on atomic operations and park-unpark.  The monitor subsystem
//   manages all RUNNING->BLOCKED and BLOCKED->READY transitions while the
//   underlying OS manages the READY<->RUN transitions.
//
// * Waiting threads reside on the WaitSet list -- wait() puts
//   the caller onto the WaitSet.
//
// * notify() or notifyAll() simply transfers threads from the WaitSet to
//   either the EntryList or cxq.  Subsequent exit() operations will
//   unpark the notifyee.  Unparking a notifee in notify() is inefficient -
//   it's likely the notifyee would simply impale itself on the lock held
//   by the notifier.
//
// * An interesting alternative is to encode cxq as (List,LockByte) where
//   the LockByte is 0 iff the monitor is owned.  _owner is simply an auxiliary
//   variable, like _recursions, in the scheme.  The threads or Events that form
//   the list would have to be aligned in 256-byte addresses.  A thread would
//   try to acquire the lock or enqueue itself with CAS, but exiting threads
//   could use a 1-0 protocol and simply STB to set the LockByte to 0.
//   Note that is is *not* word-tearing, but it does presume that full-word
//   CAS operations are coherent with intermix with STB operations.  That's true
//   on most common processors.
//
// * See also http://blogs.sun.com/dave


void* ObjectMonitor::operator new (size_t size) throw() {
  return AllocateHeap(size, mtInternal);
}
void* ObjectMonitor::operator new[] (size_t size) throw() {
  return operator new (size);
}
void ObjectMonitor::operator delete(void* p) {
  FreeHeap(p);
}
void ObjectMonitor::operator delete[] (void *p) {
  operator delete(p);
}

// -----------------------------------------------------------------------------
// Enter support
// 重量级锁获取入口.
void ObjectMonitor::enter(TRAPS) {
  // The following code is ordered to check the most common cases first
  // and to reduce RTS->RTO cache line upgrades on SPARC and IA32 processors.
  Thread * const Self = THREAD;

  // 1. 尝试通过 CAS 将 monitor 拥有者设置为当前线程.
  void * cur = Atomic::cmpxchg(&_owner, (void*)NULL, Self);
  // 1.1 设置成功即成功获取到 monitor, 此时直接返回.
  if (cur == NULL) {
    assert(_recursions == 0, "invariant");
    return;
  }
  // 1.2 如果当前线程已拥有 monitor， 则将计数重入次数 +1.
  if (cur == Self) {
    // TODO-FIXME: check for integer overflow!  BUGID 6557169.
    _recursions++;
    return;
  }

  // 1.2 如果当前线程第一次进入 monitor 则将 _ower 设置为当前线程并将重入次数设置为 1.
  if (Self->is_lock_owned((address)cur)) {
    assert(_recursions == 0, "internal state error");
    _recursions = 1;
    // Commute owner from a thread-specific on-stack BasicLockObject address to
    // a full-fledged "Thread *".
    _owner = Self;
    return;
  }

  // We've encountered genuine contention.
  assert(Self->_Stalled == 0, "invariant");
  Self->_Stalled = intptr_t(this);

  // Try one round of spinning *before* enqueueing Self
  // and before going through the awkward and expensive state
  // transitions.  The following spin is strictly optional ...
  // Note that if we acquire the monitor from an initial spin
  // we forgo posting JVMTI events and firing DTRACE probes.
  // 2. 尝试通过自旋反复获取锁.
  if (TrySpin(Self) > 0) {
    assert(_owner == Self, "must be Self: owner=" INTPTR_FORMAT, p2i(_owner));
    assert(_recursions == 0, "must be 0: recursions=" INTX_FORMAT, _recursions);
    assert(((oop)object())->mark() == markWord::encode(this),
           "object mark must match encoded this: mark=" INTPTR_FORMAT
           ", encoded this=" INTPTR_FORMAT, ((oop)object())->mark().value(),
           markWord::encode(this).value());
    Self->_Stalled = 0;
    return;
  }

  assert(_owner != Self, "invariant");
  assert(_succ != Self, "invariant");
  assert(Self->is_Java_thread(), "invariant");
  JavaThread * jt = (JavaThread *) Self;
  assert(!SafepointSynchronize::is_at_safepoint(), "invariant");
  assert(jt->thread_state() != _thread_blocked, "invariant");
  assert(this->object() != NULL, "invariant");
  assert(_contentions >= 0, "invariant");

  // Prevent deflation at STW-time.  See deflate_idle_monitors() and is_busy().
  // Ensure the object-monitor relationship remains stable while there's contention.
  Atomic::inc(&_contentions);

  JFR_ONLY(JfrConditionalFlushWithStacktrace<EventJavaMonitorEnter> flush(jt);)
  EventJavaMonitorEnter event;
  if (event.should_commit()) {
    event.set_monitorClass(((oop)this->object())->klass());
    event.set_address((uintptr_t)(this->object_addr()));
  }

  { // Change java thread status to indicate blocked on monitor enter.
    // 修改 java 线程状态为: 阻塞在 monitor enter 上.
    JavaThreadBlockedOnMonitorEnterState jtbmes(jt, this);

    Self->set_current_pending_monitor(this);

    DTRACE_MONITOR_PROBE(contended__enter, this, object(), jt);
    if (JvmtiExport::should_post_monitor_contended_enter()) {
      JvmtiExport::post_monitor_contended_enter(jt, this);

      // The current thread does not yet own the monitor and does not
      // yet appear on any queues that would get it made the successor.
      // This means that the JVMTI_EVENT_MONITOR_CONTENDED_ENTER event
      // handler cannot accidentally consume an unpark() meant for the
      // ParkEvent associated with this ObjectMonitor.
    }

    OSThreadContendState osts(Self->osthread());
    ThreadBlockInVM tbivm(jt);

    // TODO-FIXME: change the following for(;;) loop to straight-line code.
    for (;;) {
      jt->set_suspend_equivalent();
      // cleared by handle_special_suspend_equivalent_condition()
      // or java_suspend_self()
      // 真正进入 ObjectMonitor 实现.
      EnterI(THREAD);

      if (!ExitSuspendEquivalent(jt)) break;

      // We have acquired the contended monitor, but while we were
      // waiting another thread suspended us. We don't want to enter
      // the monitor while suspended because that would surprise the
      // thread that suspended us.
      //
      // 当获取 monitor 后, 如果发现此时另外一个线程暂停了当前线程, 则退出 monitor, 防止线程在被挂起时进入 monitor 发生意外.
      _recursions = 0;
      _succ = NULL;
      exit(false, Self);

      jt->java_suspend_self();
    }
    Self->set_current_pending_monitor(NULL);

    // We cleared the pending monitor info since we've just gotten past
    // the enter-check-for-suspend dance and we now own the monitor free
    // and clear, i.e., it is no longer pending. The ThreadBlockInVM
    // destructor can go to a safepoint at the end of this block. If we
    // do a thread dump during that safepoint, then this thread will show
    // as having "-locked" the monitor, but the OS and java.lang.Thread
    // states will still report that the thread is blocked trying to
    // acquire it.
  }

  Atomic::dec(&_contentions);
  assert(_contentions >= 0, "invariant");
  Self->_Stalled = 0;

  // Must either set _recursions = 0 or ASSERT _recursions == 0.
  assert(_recursions == 0, "invariant");
  assert(_owner == Self, "invariant");
  assert(_succ != Self, "invariant");
  assert(((oop)(object()))->mark() == markWord::encode(this), "invariant");

  // The thread -- now the owner -- is back in vm mode.
  // Report the glorious news via TI,DTrace and jvmstat.
  // The probe effect is non-trivial.  All the reportage occurs
  // while we hold the monitor, increasing the length of the critical
  // section.  Amdahl's parallel speedup law comes vividly into play.
  //
  // Another option might be to aggregate the events (thread local or
  // per-monitor aggregation) and defer reporting until a more opportune
  // time -- such as next time some thread encounters contention but has
  // yet to acquire the lock.  While spinning that thread could
  // spinning we could increment JVMStat counters, etc.

  DTRACE_MONITOR_PROBE(contended__entered, this, object(), jt);
  if (JvmtiExport::should_post_monitor_contended_entered()) {
    JvmtiExport::post_monitor_contended_entered(jt, this);

    // The current thread already owns the monitor and is not going to
    // call park() for the remainder of the monitor enter protocol. So
    // it doesn't matter if the JVMTI_EVENT_MONITOR_CONTENDED_ENTERED
    // event handler consumed an unpark() issued by the thread that
    // just exited the monitor.
  }
  if (event.should_commit()) {
    event.set_previousOwner((uintptr_t)_previous_owner_tid);
    event.commit();
  }
  OM_PERFDATA_OP(ContendedLockAttempts, inc());
}

// Caveat: TryLock() is not necessarily serializing if it returns failure.
// Callers must compensate as needed.
// 尝试通过 CAS 方式获取锁(即 ObjectMonitor).
int ObjectMonitor::TryLock(Thread * Self) {
  // 如果 ObjectMonitor 被其他线程持有, 返回 0.
  void * own = _owner;
  if (own != NULL) return 0;
  // 尝试通过 CAS 将 _owner 设置为当前线程, 成功返回 1.
  if (Atomic::replace_if_null(&_owner, Self)) {
    assert(_recursions == 0, "invariant");
    return 1;
  }
  // 获取锁失败返回 -1.
  // The lock had been free momentarily, but we lost the race to the lock.
  // Interference -- the CAS failed.
  // We can either return -1 or retry.
  // Retry doesn't make as much sense because the lock was just acquired.
  return -1;
}

// Convert the fields used by is_busy() to a string that can be
// used for diagnostic output.
const char* ObjectMonitor::is_busy_to_string(stringStream* ss) {
  ss->print("is_busy: contentions=%d, waiters=%d, owner=" INTPTR_FORMAT
            ", cxq=" INTPTR_FORMAT ", EntryList=" INTPTR_FORMAT, _contentions,
            _waiters, p2i(_owner), p2i(_cxq), p2i(_EntryList));
  return ss->base();
}

#define MAX_RECHECK_INTERVAL 1000

// 真正进入 monitor 的方法.
void ObjectMonitor::EnterI(TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "invariant");
  assert(((JavaThread *) Self)->thread_state() == _thread_blocked, "invariant");

  // Try the lock - TATAS
  // 1. 尝试通过 CAS 获取锁, 如果成功直接返回.
  if (TryLock (Self) > 0) {
    assert(_succ != Self, "invariant");
    assert(_owner == Self, "invariant");
    assert(_Responsible != Self, "invariant");
    return;
  }

  assert(InitDone, "Unexpectedly not initialized");

  // We try one round of spinning *before* enqueueing Self.
  //
  // If the _owner is ready but OFFPROC we could use a YieldTo()
  // operation to donate the remainder of this thread's quantum
  // to the owner.  This has subtle but beneficial affinity
  // effects.
  // 2. CAS 获取锁失败, 再尝试通过置自适应自旋获取锁, 如果成功直接返回.
  if (TrySpin(Self) > 0) {
    assert(_owner == Self, "invariant");
    assert(_succ != Self, "invariant");
    assert(_Responsible != Self, "invariant");
    return;
  }

  // The Spin failed -- Enqueue and park the thread ...
  // 3. 如果通过 CAS 和自适应自旋(spin) 尝试获取锁都失败, 则将线程入队到 _cxq 中, 并 park(阻塞) 该线程
  assert(_succ != Self, "invariant");
  assert(_owner != Self, "invariant");
  assert(_Responsible != Self, "invariant");

  // Enqueue "Self" on ObjectMonitor's _cxq.
  //
  // Node acts as a proxy for Self.
  // As an aside, if were to ever rewrite the synchronization code mostly
  // in Java, WaitNodes, ObjectMonitors, and Events would become 1st-class
  // Java objects.  This would avoid awkward lifecycle and liveness issues,
  // as well as eliminate a subset of ABA issues.
  // TODO: eliminate ObjectWaiter and enqueue either Threads or Events.

  ObjectWaiter node(Self);
  Self->_ParkEvent->reset();
  node._prev   = (ObjectWaiter *) 0xBAD;
  node.TState  = ObjectWaiter::TS_CXQ;

  // Push "Self" onto the front of the _cxq.
  // Once on cxq/EntryList, Self stays on-queue until it acquires the lock.
  // Note that spinning tends to reduce the rate at which threads
  // enqueue and dequeue on EntryList|cxq.

  // 将 "Self"(当前线程) 入队到 _cxq 队列头部. 一旦进入 cxq/EntryList，self 就会一直在队列中，直到它获得锁为止.
  // 注意：自旋会降低线程在 EntryList|cxq 上入队和出队的速率.
  ObjectWaiter * nxt;
  for (;;) {
    // _cxq 队列为单向链表, 从链表头部入队.
    // 将节点指向原有的头节点.
    node._next = nxt = _cxq;
    // CAS 更新头节点为当前入队的节点.
    if (Atomic::cmpxchg(&_cxq, nxt, &node) == nxt) break;
    // 如果入队失败, 则表示 _cxq 队列发生了变化, 在重试前尝试通过 CAS 获取锁.
    // Interference - the CAS failed because _cxq changed.  Just retry.
    // As an optional optimization we retry the lock.
    if (TryLock (Self) > 0) {
      assert(_succ != Self, "invariant");
      assert(_owner == Self, "invariant");
      assert(_Responsible != Self, "invariant");
      return;
    }
  }

  // Check for cxq|EntryList edge transition to non-null.  This indicates
  // the onset of contention.  While contention persists exiting threads
  // will use a ST:MEMBAR:LD 1-1 exit protocol.  When contention abates exit
  // operations revert to the faster 1-0 mode.  This enter operation may interleave
  // (race) a concurrent 1-0 exit operation, resulting in stranding, so we
  // arrange for one of the contending thread to use a timed park() operations
  // to detect and recover from the race.  (Stranding is form of progress failure
  // where the monitor is unlocked but all the contending threads remain parked).
  // That is, at least one of the contended threads will periodically poll _owner.
  // One of the contending threads will become the designated "Responsible" thread.
  // The Responsible thread uses a timed park instead of a normal indefinite park
  // operation -- it periodically wakes and checks for and recovers from potential
  // strandings admitted by 1-0 exit operations.   We need at most one Responsible
  // thread per-monitor at any given moment.  Only threads on cxq|EntryList may
  // be responsible for a monitor.
  //
  // Currently, one of the contended threads takes on the added role of "Responsible".
  // A viable alternative would be to use a dedicated "stranding checker" thread
  // that periodically iterated over all the threads (or active monitors) and unparked
  // successors where there was risk of stranding.  This would help eliminate the
  // timer scalability issues we see on some platforms as we'd only have one thread
  // -- the checker -- parked on a timer.
  // 3. 当线程进入 cxq 队列后, 检查原有的 cxq 或 EntryList 是否都为空.
  // * 都为空则表示当前线程为等待获取锁的第一个线程, 此时该线程会被指定为 "负责线程"(responsible thread).
  // * 如果非空则表示存在竞争. 
  // 当一直有竞争时，退出线程将使用 ST:MEMBAR:LD 1-1 退出协议.
  // 当竞争减弱时退出操作恢复到更快的 1-0 模式. 此操作可能会交错(竞争)并发的 1-0 退出操作，导致搁浅(stranding)，因此
  // 安排一个争用线程使用 timed park() 操作检测并从竞争中恢复.(搁浅是进程 failure 的一种形式 monitor 已解锁，但所有争用线程仍处于 parked 状态.)

  // 至少有一个争用线程将定期轮询 _owner. 其中一个争用线程将成为指定的 "负责线程"(responsible thread)。
  // 负责线程使用 timed park() ，而不是正常的无限 park 操作--它定期唤醒、检查 1-0 exit 操作允许的潜在搁浅(stranding)并从中恢复
  // 在任意时刻，每个 monitor 最多需要一个负责线程。只有 cxq | EntryList 上的线程才能负责 monitor.
  // 目前，其中一个争用线程承担了 "Responsible(负责)" 的新增角色.
  if (nxt == NULL && _EntryList == NULL) {
    // Try to assume the role of responsible thread for the monitor.
    // CONSIDER:  ST vs CAS vs { if (Responsible==null) Responsible=Self }
    // 如果当前线程符合 负责线程 条件，则更新负责线程为当前线程.
    Atomic::replace_if_null(&_Responsible, Self);
  }

  // The lock might have been released while this thread was occupied queueing
  // itself onto _cxq.  To close the race and avoid "stranding" and
  // progress-liveness failure we must resample-retry _owner before parking.
  // Note the Dekker/Lamport duality: ST cxq; MEMBAR; LD Owner.
  // In this case the ST-MEMBAR is accomplished with CAS().
  //
  // TODO: Defer all thread state transitions until park-time.
  // Since state transitions are heavy and inefficient we'd like
  // to defer the state transitions until absolutely necessary,
  // and in doing so avoid some transitions ...

  // 此线程将自身添加到 _cxq 对列中时, 锁可能已被释放.
  // 停止竞争，避免 "stranding(搁浅)" 和 progress-liveness(进程活跃) 失败且在 park 前必须重新采样 _owner.
  // 请注意 Dekker/Lamport 的二元性：St cxq；MEMBAR；LD Owner.
  // 在本例中，ST-MEMBAR 由 CAS() 完成.
  int nWakeups = 0;
  int recheckInterval = 1;

  // park 当前线程.
  for (;;) {

    if (TryLock(Self) > 0) break;
    assert(_owner != Self, "invariant");

    // park self
    // 如果是负责线程(responsible thread)使用带超时时间的 park.
    if (_Responsible == Self) {
      Self->_ParkEvent->park((jlong) recheckInterval);
      // Increase the recheckInterval, but clamp the value.
      recheckInterval *= 8;
      if (recheckInterval > MAX_RECHECK_INTERVAL) {
        recheckInterval = MAX_RECHECK_INTERVAL;
      }
    } else {
      // 非负责线程(responsible thread) 使用 park 永久阻塞(除非被唤醒).
      Self->_ParkEvent->park();
    }
    // 被唤醒后再次尝试获取锁.
    if (TryLock(Self) > 0) break;

    // The lock is still contested.
    // Keep a tally of the # of futile wakeups.
    // Note that the counter is not protected by a lock or updated by atomics.
    // That is by design - we trade "lossy" counters which are exposed to
    // races during updates for a lower probe effect.

    // This PerfData object can be used in parallel with a safepoint.
    // See the work around in PerfDataManager::destroy().
    // 获取不到锁时表示锁仍处于争用状态, 此时记录无用唤醒次数.
    OM_PERFDATA_OP(FutileWakeups, inc());
    ++nWakeups;

    // Assuming this is not a spurious wakeup we'll normally find _succ == Self.
    // We can defer clearing _succ until after the spin completes
    // TrySpin() must tolerate being called with _succ == Self.
    // Try yet another round of adaptive spinning.
    // 再次尝试通过自旋方式获取锁.
    if (TrySpin(Self) > 0) break;

    // We can find that we were unpark()ed and redesignated _succ while
    // we were spinning.  That's harmless.  If we iterate and call park(),
    // park() will consume the event and return immediately and we'll
    // just spin again.  This pattern can repeat, leaving _succ to simply
    // spin on a CPU.

    if (_succ == Self) _succ = NULL;

    // Invariant: after clearing _succ a thread *must* retry _owner before parking.
    // 不变量: 在清除 _succ 之后，线程 "必须" 重试 _owner 才能 park(阻塞).
    // 内存屏障, 禁用指令重排序.
    OrderAccess::fence();
  }

  // Egress :
  // Self has acquired the lock -- Unlink Self from the cxq or EntryList.
  // Normally we'll find Self on the EntryList .
  // From the perspective of the lock owner (this thread), the
  // EntryList is stable and cxq is prepend-only.
  // The head of cxq is volatile but the interior is stable.
  // In addition, Self.TState is stable.

  // Self(当前线程) 获得了锁, 从 cxq 或 EntryList 取消链接(即从列表中移除该线程).
  // 通常会在 EntryList 上找到当前线程.
  // 从锁所有者（此线程）的角度来看，EntryList 是稳定的，cxq 是仅前置(prepend-only)的.
  // 另外 Self.TState 是稳定的.
  assert(_owner == Self, "invariant");
  assert(object() != NULL, "invariant");
  // I'd like to write:
  //   guarantee (((oop)(object()))->mark() == markWord::encode(this), "invariant") ;
  // but as we're at a safepoint that's not safe.
  // 将当前线程从 cxq 或 EntryList 中移除.
  UnlinkAfterAcquire(Self, &node);
  if (_succ == Self) _succ = NULL;

  assert(_succ != Self, "invariant");
  // 如果是负责线程(responsible thread)则将 _Responsible 重置为 null.
  if (_Responsible == Self) {
    _Responsible = NULL;
    OrderAccess::fence(); // Dekker pivot-point

    // We may leave threads on cxq|EntryList without a designated
    // "Responsible" thread.  This is benign.  When this thread subsequently
    // exits the monitor it can "see" such preexisting "old" threads --
    // threads that arrived on the cxq|EntryList before the fence, above --
    // by LDing cxq|EntryList.  Newly arrived threads -- that is, threads
    // that arrive on cxq after the ST:MEMBAR, above -- will set Responsible
    // non-null and elect a new "Responsible" timer thread.
    //
    // This thread executes:
    //    ST Responsible=null; MEMBAR    (in enter epilogue - here)
    //    LD cxq|EntryList               (in subsequent exit)
    //
    // Entering threads in the slow/contended path execute:
    //    ST cxq=nonnull; MEMBAR; LD Responsible (in enter prolog)
    //    The (ST cxq; MEMBAR) is accomplished with CAS().
    //
    // The MEMBAR, above, prevents the LD of cxq|EntryList in the subsequent
    // exit operation from floating above the ST Responsible=null.
  }

  // We've acquired ownership with CAS().
  // CAS is serializing -- it has MEMBAR/FENCE-equivalent semantics.
  // But since the CAS() this thread may have also stored into _succ,
  // EntryList, cxq or Responsible.  These meta-data updates must be
  // visible __before this thread subsequently drops the lock.
  // Consider what could occur if we didn't enforce this constraint --
  // STs to monitor meta-data and user-data could reorder with (become
  // visible after) the ST in exit that drops ownership of the lock.
  // Some other thread could then acquire the lock, but observe inconsistent
  // or old monitor meta-data and heap data.  That violates the JMM.
  // To that end, the 1-0 exit() operation must have at least STST|LDST
  // "release" barrier semantics.  Specifically, there must be at least a
  // STST|LDST barrier in exit() before the ST of null into _owner that drops
  // the lock.   The barrier ensures that changes to monitor meta-data and data
  // protected by the lock will be visible before we release the lock, and
  // therefore before some other thread (CPU) has a chance to acquire the lock.
  // See also: http://gee.cs.oswego.edu/dl/jmm/cookbook.html.
  //
  // Critically, any prior STs to _succ or EntryList must be visible before
  // the ST of null into _owner in the *subsequent* (following) corresponding
  // monitorexit.  Recall too, that in 1-0 mode monitorexit does not necessarily
  // execute a serializing instruction.

  return;
}

// ReenterI() is a specialized inline form of the latter half of the
// contended slow-path from EnterI().  We use ReenterI() only for
// monitor reentry in wait().
//
// In the future we should reconcile EnterI() and ReenterI().
// ReenterI() 是 EnterI() 中争用慢路径后半部分的专用内联形式. ReenterI() 仅用于从  monitor 重新 wait().
void ObjectMonitor::ReenterI(Thread * Self, ObjectWaiter * SelfNode) {
  assert(Self != NULL, "invariant");
  assert(SelfNode != NULL, "invariant");
  assert(SelfNode->_thread == Self, "invariant");
  assert(_waiters > 0, "invariant");
  assert(((oop)(object()))->mark() == markWord::encode(this), "invariant");
  assert(((JavaThread *)Self)->thread_state() != _thread_blocked, "invariant");
  JavaThread * jt = (JavaThread *) Self;

  int nWakeups = 0;
  for (;;) {
    ObjectWaiter::TStates v = SelfNode->TState;
    guarantee(v == ObjectWaiter::TS_ENTER || v == ObjectWaiter::TS_CXQ, "invariant");
    assert(_owner != Self, "invariant");

    // 1. 尝试获取锁.
    if (TryLock(Self) > 0) break;
    if (TrySpin(Self) > 0) break;

    // State transition wrappers around park() ...
    // ReenterI() wisely defers state transitions until
    // it's clear we must park the thread.
    // 2. 获取锁失败, park(阻塞)自身.
    {
      OSThreadContendState osts(Self->osthread());
      ThreadBlockInVM tbivm(jt);

      // cleared by handle_special_suspend_equivalent_condition()
      // or java_suspend_self()
      jt->set_suspend_equivalent();
      Self->_ParkEvent->park();

      // were we externally suspended while we were waiting?
      for (;;) {
        if (!ExitSuspendEquivalent(jt)) break;
        if (_succ == Self) { _succ = NULL; OrderAccess::fence(); }
        jt->java_suspend_self();
        jt->set_suspend_equivalent();
      }
    }

    // Try again, but just so we distinguish between futile wakeups and
    // successful wakeups.  The following test isn't algorithmically
    // necessary, but it helps us maintain sensible statistics.
    // 3. 被唤醒时再次尝试获取锁.
    if (TryLock(Self) > 0) break;

    // The lock is still contested.
    // Keep a tally of the # of futile wakeups.
    // Note that the counter is not protected by a lock or updated by atomics.
    // That is by design - we trade "lossy" counters which are exposed to
    // races during updates for a lower probe effect.
    // 更新无效唤醒计数.
    ++nWakeups;

    // Assuming this is not a spurious wakeup we'll normally
    // find that _succ == Self.
    if (_succ == Self) _succ = NULL;

    // Invariant: after clearing _succ a contending thread
    // *must* retry  _owner before parking.
    OrderAccess::fence();

    // This PerfData object can be used in parallel with a safepoint.
    // See the work around in PerfDataManager::destroy().
    OM_PERFDATA_OP(FutileWakeups, inc());
  }

  // Self has acquired the lock -- Unlink Self from the cxq or EntryList .
  // Normally we'll find Self on the EntryList.
  // Unlinking from the EntryList is constant-time and atomic-free.
  // From the perspective of the lock owner (this thread), the
  // EntryList is stable and cxq is prepend-only.
  // The head of cxq is volatile but the interior is stable.
  // In addition, Self.TState is stable.
  // 3. 获取锁成功, 解除当前线程与 cxq 或 EntryList 的链接.
  assert(_owner == Self, "invariant");
  assert(((oop)(object()))->mark() == markWord::encode(this), "invariant");
  UnlinkAfterAcquire(Self, SelfNode);
  if (_succ == Self) _succ = NULL;
  assert(_succ != Self, "invariant");
  SelfNode->TState = ObjectWaiter::TS_RUN;
  OrderAccess::fence();      // see comments at the end of EnterI()
}

// By convention we unlink a contending thread from EntryList|cxq immediately
// after the thread acquires the lock in ::enter().  Equally, we could defer
// unlinking the thread until ::exit()-time.
// 从 EntryList | cxq 中取消一个争用线程的链接(即将争用线程从两队列中移除).
void ObjectMonitor::UnlinkAfterAcquire(Thread *Self, ObjectWaiter *SelfNode) {
  assert(_owner == Self, "invariant");
  assert(SelfNode->_thread == Self, "invariant");

  if (SelfNode->TState == ObjectWaiter::TS_ENTER) {
    // Normal case: remove Self from the DLL EntryList .
    // This is a constant-time operation.
    ObjectWaiter * nxt = SelfNode->_next;
    ObjectWaiter * prv = SelfNode->_prev;
    if (nxt != NULL) nxt->_prev = prv;
    if (prv != NULL) prv->_next = nxt;
    if (SelfNode == _EntryList) _EntryList = nxt;
    assert(nxt == NULL || nxt->TState == ObjectWaiter::TS_ENTER, "invariant");
    assert(prv == NULL || prv->TState == ObjectWaiter::TS_ENTER, "invariant");
  } else {
    assert(SelfNode->TState == ObjectWaiter::TS_CXQ, "invariant");
    // Inopportune interleaving -- Self is still on the cxq.
    // This usually means the enqueue of self raced an exiting thread.
    // Normally we'll find Self near the front of the cxq, so
    // dequeueing is typically fast.  If needbe we can accelerate
    // this with some MCS/CHL-like bidirectional list hints and advisory
    // back-links so dequeueing from the interior will normally operate
    // in constant-time.
    // Dequeue Self from either the head (with CAS) or from the interior
    // with a linear-time scan and normal non-atomic memory operations.
    // CONSIDER: if Self is on the cxq then simply drain cxq into EntryList
    // and then unlink Self from EntryList.  We have to drain eventually,
    // so it might as well be now.

    ObjectWaiter * v = _cxq;
    assert(v != NULL, "invariant");
    if (v != SelfNode || Atomic::cmpxchg(&_cxq, v, SelfNode->_next) != v) {
      // The CAS above can fail from interference IFF a "RAT" arrived.
      // In that case Self must be in the interior and can no longer be
      // at the head of cxq.
      if (v == SelfNode) {
        assert(_cxq != v, "invariant");
        v = _cxq;          // CAS above failed - start scan at head of list
      }
      ObjectWaiter * p;
      ObjectWaiter * q = NULL;
      for (p = v; p != NULL && p != SelfNode; p = p->_next) {
        q = p;
        assert(p->TState == ObjectWaiter::TS_CXQ, "invariant");
      }
      assert(v != SelfNode, "invariant");
      assert(p == SelfNode, "Node not found on cxq");
      assert(p != _cxq, "invariant");
      assert(q != NULL, "invariant");
      assert(q->_next == p, "invariant");
      q->_next = p->_next;
    }
  }

#ifdef ASSERT
  // Diagnostic hygiene ...
  SelfNode->_prev  = (ObjectWaiter *) 0xBAD;
  SelfNode->_next  = (ObjectWaiter *) 0xBAD;
  SelfNode->TState = ObjectWaiter::TS_RUN;
#endif
}

// -----------------------------------------------------------------------------
// Exit support
//
// exit()
// ~~~~~~
// Note that the collector can't reclaim the objectMonitor or deflate
// the object out from underneath the thread calling ::exit() as the
// thread calling ::exit() never transitions to a stable state.
// This inhibits GC, which in turn inhibits asynchronous (and
// inopportune) reclamation of "this".
// 请注意，垃圾收集器无法恢复 objectMonitor 或从调用 ::exit() 的线程下面放空对象，
// 因为线程调用 ::exit() 永远不会过渡到稳定的状态. 
// 这抑制了 GC，从而抑制异步的 GC （和不合时宜的）“this” 的开垦。
//
// We'd like to assert that: (THREAD->thread_state() != _thread_blocked) ;
// There's one exception to the claim above, however.  EnterI() can call
// exit() to drop a lock if the acquirer has been externally suspended.
// In that case exit() is called with _thread_state as _thread_blocked,
// but the monitor's _contentions field is > 0, which inhibits reclamation.
//
// 1-0 exit
// ~~~~~~~~
// ::exit() uses a canonical 1-1 idiom with a MEMBAR although some of
// the fast-path operators have been optimized so the common ::exit()
// operation is 1-0, e.g., see macroAssembler_x86.cpp: fast_unlock().
// The code emitted by fast_unlock() elides the usual MEMBAR.  This
// greatly improves latency -- MEMBAR and CAS having considerable local
// latency on modern processors -- but at the cost of "stranding".  Absent the
// MEMBAR, a thread in fast_unlock() can race a thread in the slow
// ::enter() path, resulting in the entering thread being stranding
// and a progress-liveness failure.   Stranding is extremely rare.
// We use timers (timed park operations) & periodic polling to detect
// and recover from stranding.  Potentially stranded threads periodically
// wake up and poll the lock.  See the usage of the _Responsible variable.

// ::exit() 使用一个典型的带有 MEMBAR (即常称的 Memory barrier, 内存屏障) 的 1-1 语句(idiom)，
// 尽管一些快速路径运算符(fast-path operators)已被优化，因此常见的 ::exit() 操作为 1-0，
// 例如，请参见 macroAssembler_x86.cpp:fast_unlock(). fast_unlock() 发出的代码消除了通常的 MEMBAR. 这大大提高了延迟--MEMBAR 和 CAS 在现代处理器上具有相当大的本地延迟--但代价是“搁浅(stranding)”。
// 如果没有 MEMBAR，fast_unlock() 中的线程可以在 slow::enter() 路径中与线程竞争，导致进入线程被搁浅(stranding)，进程活跃度(progress-liveness)失败(failure).
// 搁浅极为罕见, 我们使用计时器（timed park 操作）和定期轮询来检测和恢复搁浅.
// 可能搁浅的线程会定期唤醒并轮询锁.请参见 _Reresponsible 变量的用法
//
// The CAS() in enter provides for safety and exclusion, while the CAS or
// MEMBAR in exit provides for progress and avoids stranding.  1-0 locking
// eliminates the CAS/MEMBAR from the exit path, but it admits stranding.
// We detect and recover from stranding with timers.
// enter 中的 CAS() 提供了安全和互斥功能，而 exit 中的 CAS 或 MEMBAR(Memory barrier, 内存屏障) 提供改进(progress)并避免搁浅.
// 1-0 锁定消除了出口路径上的 CAS/MEMBAR，但允许搁浅(stranding). 我们用计时器检测并从搁浅中恢复.
// 
// If a thread transiently strands it'll park until (a) another
// thread acquires the lock and then drops the lock, at which time the
// exiting thread will notice and unpark the stranded thread, or, (b)
// the timer expires.  If the lock is high traffic then the stranding latency
// will be low due to (a).  If the lock is low traffic then the odds of
// stranding are lower, although the worst-case stranding latency
// is longer.  Critically, we don't want to put excessive load in the
// platform's timer subsystem.  We want to minimize both the timer injection
// rate (timers created/sec) as well as the number of timers active at
// any one time.  (more precisely, we want to minimize timer-seconds, which is
// the integral of the # of active timers at any instant over time).
// Both impinge on OS scalability.  Given that, at most one thread parked on
// a monitor will use a timer.
// 如果一个线程暂时搁浅，它将 park(即休眠) 直到
// （a）另一个线程获得锁，然后释放锁，这时退出的线程会注意到并解除搁浅的线程.
// （b）计时器到期. 
// 如果锁是高流量的，那么由于 (a), 搁浅的延迟会很低. 
// 如果锁的流量很低，那么搁浅的几率就比较低，尽管最坏的情况下，搁浅的延迟会更长.
// 最关键的是，我们不希望给平台的定时器子系统带来过多的负荷. 
// 我们希望将定时器的注入率（创建的定时器/秒）以及在任何时候都处于活动状态的定时器的数量降到最低.
//  (更确切地说，我们希望最小化定时器秒数，也就是在任何时刻活跃的定时器数量在时间上的积分）.
// 两者都会对操作系统的可扩展性造成影响. 考虑到这些，最多只有一个 park 在 monitor 上的线程会使用一个定时器.
//
// There is also the risk of a futile wake-up. If we drop the lock
// another thread can reacquire the lock immediately, and we can
// then wake a thread unnecessarily. This is benign, and we've
// structured the code so the windows are short and the frequency
// of such futile wakups is low.
// 还有一个风险是徒劳的唤醒: 如果我们放弃了锁，另一个线程可以立即重新获得锁，那么我们就会不必要地唤醒一个线程.
// 这是良性的，而且我们的代码结构使窗口很短，这种徒劳的唤醒的频率很低.
// 退出 monitor(释放锁) 的方法.
void ObjectMonitor::exit(bool not_suspended, TRAPS) {
  Thread * const Self = THREAD;
  // 当锁不被当前线程持有时.
  if (THREAD != _owner) {
    if (THREAD->is_lock_owned((address) _owner)) {
      // Transmute _owner from a BasicLock pointer to a Thread address.
      // We don't need to hold _mutex for this transition.
      // Non-null to Non-null is safe as long as all readers can
      // tolerate either flavor.
      assert(_recursions == 0, "invariant");
      _owner = THREAD;
      _recursions = 0;
    } else {
      // Apparent unbalanced locking ...
      // Naively we'd like to throw IllegalMonitorStateException.
      // As a practical matter we can neither allocate nor throw an
      // exception as ::exit() can be called from leaf routines.
      // see x86_32.ad Fast_Unlock() and the I1 and I2 properties.
      // Upon deeper reflection, however, in a properly run JVM the only
      // way we should encounter this situation is in the presence of
      // unbalanced JNI locking. TODO: CheckJNICalls.
      // See also: CR4414101
#ifdef ASSERT
      LogStreamHandle(Error, monitorinflation) lsh;
      lsh.print_cr("ERROR: ObjectMonitor::exit(): thread=" INTPTR_FORMAT
                    " is exiting an ObjectMonitor it does not own.", p2i(THREAD));
      lsh.print_cr("The imbalance is possibly caused by JNI locking.");
      print_debug_style_on(&lsh);
#endif
      assert(false, "Non-balanced monitor enter/exit!");
      return;
    }
  }

  // 如果重入次数不等于 0 则将计数 -1 并直接返回.
  if (_recursions != 0) {
    _recursions--;        // this is simple recursive enter
    return;
  }

  // Invariant: after setting Responsible=null an thread must execute
  // a MEMBAR or other serializing instruction before fetching EntryList|cxq.
  // 不变量: 在设置 Responsible=null 后，线程必须在获取 EntryList | cxq 前执行 MEMBAR(Memory barrier, 内存屏障) 或其他序列化指令.
  _Responsible = NULL;

#if INCLUDE_JFR
  // get the owner's thread id for the MonitorEnter event
  // if it is enabled and the thread isn't suspended
  if (not_suspended && EventJavaMonitorEnter::is_enabled()) {
    _previous_owner_tid = JFR_THREAD_ID(Self);
  }
#endif

  for (;;) {
    assert(THREAD == _owner, "invariant");

    // release semantics: prior loads and stores from within the critical section
    // must not float (reorder) past the following store that drops the lock.
    // 1.  将 _owner 置为 null.
    Atomic::release_store(&_owner, (void*)NULL);   // drop the lock
    // 内存屏障(Memory barrier, 或称为 MEMBAR), 防止指令重排序.
    OrderAccess::storeload();                      // See if we need to wake a successor
    // 2. 如果 _cxq 和 _EntryList 为空或者 _succ(假定继承人) 不为 NULL 直接退出.
    if ((intptr_t(_EntryList)|intptr_t(_cxq)) == 0 || _succ != NULL) {
      return;
    }
    // Other threads are blocked trying to acquire the lock.

    // Normally the exiting thread is responsible for ensuring succession,
    // but if other successors are ready or other entering threads are spinning
    // then this thread can simply store NULL into _owner and exit without
    // waking a successor.  The existence of spinners or ready successors
    // guarantees proper succession (liveness).  Responsibility passes to the
    // ready or running successors.  The exiting thread delegates the duty.
    // More precisely, if a successor already exists this thread is absolved
    // of the responsibility of waking (unparking) one.
    //
    // The _succ variable is critical to reducing futile wakeup frequency.
    // _succ identifies the "heir presumptive" thread that has been made
    // ready (unparked) but that has not yet run.  We need only one such
    // successor thread to guarantee progress.
    // See http://www.usenix.org/events/jvm01/full_papers/dice/dice.pdf
    // section 3.3 "Futile Wakeup Throttling" for details.
    //
    // Note that spinners in Enter() also set _succ non-null.
    // In the current implementation spinners opportunistically set
    // _succ so that exiting threads might avoid waking a successor.
    // Another less appealing alternative would be for the exiting thread
    // to drop the lock and then spin briefly to see if a spinner managed
    // to acquire the lock.  If so, the exiting thread could exit
    // immediately without waking a successor, otherwise the exiting
    // thread would need to dequeue and wake a successor.
    // (Note that we'd need to make the post-drop spin short, but no
    // shorter than the worst-case round-trip cache-line migration time.
    // The dropped lock needs to become visible to the spinner, and then
    // the acquisition of the lock by the spinner must become visible to
    // the exiting thread).

    // It appears that an heir-presumptive (successor) must be made ready.
    // Only the current lock owner can manipulate the EntryList or
    // drain _cxq, so we need to reacquire the lock.  If we fail
    // to reacquire the lock the responsibility for ensuring succession
    // falls to the new owner.
    //
    // 3. 在释放锁时其他线程获取了锁, 则直接退出. 
    if (!Atomic::replace_if_null(&_owner, THREAD)) {
      return;
    }

    guarantee(_owner == THREAD, "invariant");

    ObjectWaiter * w = NULL;

    w = _EntryList;
    // 4. 如果 _EntryList 不为空则唤醒 _EntryList 队列头部线程, 并将其设置为 _succ (假定继承人).
    if (w != NULL) {
      // I'd like to write: guarantee (w->_thread != Self).
      // But in practice an exiting thread may find itself on the EntryList.
      // Let's say thread T1 calls O.wait().  Wait() enqueues T1 on O's waitset and
      // then calls exit().  Exit release the lock by setting O._owner to NULL.
      // Let's say T1 then stalls.  T2 acquires O and calls O.notify().  The
      // notify() operation moves T1 from O's waitset to O's EntryList. T2 then
      // release the lock "O".  T2 resumes immediately after the ST of null into
      // _owner, above.  T2 notices that the EntryList is populated, so it
      // reacquires the lock and then finds itself on the EntryList.
      // Given all that, we have to tolerate the circumstance where "w" is
      // associated with Self.
      assert(w->TState == ObjectWaiter::TS_ENTER, "invariant");
      ExitEpilog(Self, w);
      return;
    }

    // If we find that both _cxq and EntryList are null then just
    // re-run the exit protocol from the top.
    w = _cxq;
    if (w == NULL) continue;

    // Drain _cxq into EntryList - bulk transfer.
    // First, detach _cxq.
    // The following loop is tantamount to: w = swap(&cxq, NULL)
    // 5. 将 _cxq 中的所有线程批量转移到 EntryList.

    // 5.1 将 _cxq 指向 NULL.
    for (;;) {
      assert(w != NULL, "Invariant");
      ObjectWaiter * u = Atomic::cmpxchg(&_cxq, w, (ObjectWaiter*)NULL);
      if (u == w) break;
      w = u;
    }

    assert(w != NULL, "invariant");
    assert(_EntryList == NULL, "invariant");

    // Convert the LIFO SLL anchored by _cxq into a DLL.
    // The list reorganization step operates in O(LENGTH(w)) time.
    // It's critical that this step operate quickly as
    // "Self" still holds the outer-lock, restricting parallelism
    // and effectively lengthening the critical section.
    // Invariant: s chases t chases u.
    // TODO-FIXME: consider changing EntryList from a DLL to a CDLL so
    // we have faster access to the tail.
    // 5.2 将 _cxq 中的节点放入 _EntryList.
    //     在实现上直接将 _EntryList 指向 _cxq 队列中的头节点，并将每个节点的 _prev 指针指向其上一个节点.
    _EntryList = w;
    ObjectWaiter * q = NULL;
    ObjectWaiter * p;
    for (p = w; p != NULL; p = p->_next) {
      guarantee(p->TState == ObjectWaiter::TS_CXQ, "Invariant");
      p->TState = ObjectWaiter::TS_ENTER;
      p->_prev = q;
      q = p;
    }

    // In 1-0 mode we need: ST EntryList; MEMBAR #storestore; ST _owner = NULL
    // The MEMBAR is satisfied by the release_store() operation in ExitEpilog().

    // See if we can abdicate to a spinner instead of waking a thread.
    // A primary goal of the implementation is to reduce the
    // context-switch rate.
    // 如果存在 _succ (假定继承人) 直接退出.
    if (_succ != NULL) continue;

    w = _EntryList;
    // 5.3 唤醒 _EntryList 队列头部线程, 并将其设置为 _succ (假定继承人).
    if (w != NULL) {
      guarantee(w->TState == ObjectWaiter::TS_ENTER, "invariant");
      ExitEpilog(Self, w);
      return;
    }
  }
}

// ExitSuspendEquivalent:
// A faster alternate to handle_special_suspend_equivalent_condition()
//
// handle_special_suspend_equivalent_condition() unconditionally
// acquires the SR_lock.  On some platforms uncontended MutexLocker()
// operations have high latency.  Note that in ::enter() we call HSSEC
// while holding the monitor, so we effectively lengthen the critical sections.
//
// There are a number of possible solutions:
//
// A.  To ameliorate the problem we might also defer state transitions
//     to as late as possible -- just prior to parking.
//     Given that, we'd call HSSEC after having returned from park(),
//     but before attempting to acquire the monitor.  This is only a
//     partial solution.  It avoids calling HSSEC while holding the
//     monitor (good), but it still increases successor reacquisition latency --
//     the interval between unparking a successor and the time the successor
//     resumes and retries the lock.  See ReenterI(), which defers state transitions.
//     If we use this technique we can also avoid EnterI()-exit() loop
//     in ::enter() where we iteratively drop the lock and then attempt
//     to reacquire it after suspending.
//
// B.  In the future we might fold all the suspend bits into a
//     composite per-thread suspend flag and then update it with CAS().
//     Alternately, a Dekker-like mechanism with multiple variables
//     would suffice:
//       ST Self->_suspend_equivalent = false
//       MEMBAR
//       LD Self_>_suspend_flags

bool ObjectMonitor::ExitSuspendEquivalent(JavaThread * jSelf) {
  return jSelf->handle_special_suspend_equivalent_condition();
}

// 退出流程:
// 1. 将 _succ(假定继承人)设置为 EntryList 队列中的头节点对应线程.
// 2. 将 _owner 设置为 null.
// 3. 唤醒 EntryList 队列中的头节点对应线程
void ObjectMonitor::ExitEpilog(Thread * Self, ObjectWaiter * Wakee) {
  assert(_owner == Self, "invariant");

  // Exit protocol:
  // 1. ST _succ = wakee
  // 2. membar #loadstore|#storestore;
  // 2. ST _owner = NULL
  // 3. unpark(wakee)

  _succ = Wakee->_thread;
  ParkEvent * Trigger = Wakee->_event;

  // Hygiene -- once we've set _owner = NULL we can't safely dereference Wakee again.
  // The thread associated with Wakee may have grabbed the lock and "Wakee" may be
  // out-of-scope (non-extant).
  Wakee  = NULL;

  // Drop the lock
  Atomic::release_store(&_owner, (void*)NULL);
  OrderAccess::fence();                               // ST _owner vs LD in unpark()

  DTRACE_MONITOR_PROBE(contended__exit, this, object(), Self);
  Trigger->unpark();

  // Maintain stats and report events to JVMTI
  OM_PERFDATA_OP(Parks, inc());
}


// -----------------------------------------------------------------------------
// Class Loader deadlock handling.
//
// complete_exit exits a lock returning recursion count
// complete_exit/reenter operate as a wait without waiting
// complete_exit requires an inflated monitor
// The _owner field is not always the Thread addr even with an
// inflated monitor, e.g. the monitor can be inflated by a non-owning
// thread due to contention.
intx ObjectMonitor::complete_exit(TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "Must be Java thread!");
  JavaThread *jt = (JavaThread *)THREAD;

  assert(InitDone, "Unexpectedly not initialized");

  if (THREAD != _owner) {
    if (THREAD->is_lock_owned ((address)_owner)) {
      assert(_recursions == 0, "internal state error");
      _owner = THREAD;   // Convert from basiclock addr to Thread addr
      _recursions = 0;
    }
  }

  guarantee(Self == _owner, "complete_exit not owner");
  intx save = _recursions; // record the old recursion count
  _recursions = 0;        // set the recursion level to be 0
  exit(true, Self);           // exit the monitor
  guarantee(_owner != Self, "invariant");
  return save;
}

// reenter() enters a lock and sets recursion count
// complete_exit/reenter operate as a wait without waiting
void ObjectMonitor::reenter(intx recursions, TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "Must be Java thread!");
  JavaThread *jt = (JavaThread *)THREAD;

  guarantee(_owner != Self, "reenter already owner");
  enter(THREAD);       // enter the monitor
  guarantee(_recursions == 0, "reenter recursion");
  _recursions = recursions;
  return;
}

// Checks that the current THREAD owns this monitor and causes an
// immediate return if it doesn't. We don't use the CHECK macro
// because we want the IMSE to be the only exception that is thrown
// from the call site when false is returned. Any other pending
// exception is ignored.
#define CHECK_OWNER()                                                  \
  do {                                                                 \
    if (!check_owner(THREAD)) {                                        \
       assert(HAS_PENDING_EXCEPTION, "expected a pending IMSE here."); \
       return;                                                         \
     }                                                                 \
  } while (false)

// Returns true if the specified thread owns the ObjectMonitor.
// Otherwise returns false and throws IllegalMonitorStateException
// (IMSE). If there is a pending exception and the specified thread
// is not the owner, that exception will be replaced by the IMSE.
bool ObjectMonitor::check_owner(Thread* THREAD) {
  if (_owner == THREAD) {
    return true;
  }
  if (THREAD->is_lock_owned((address)_owner)) {
    _owner = THREAD;  // convert from BasicLock addr to Thread addr
    _recursions = 0;
    return true;
  }
  THROW_MSG_(vmSymbols::java_lang_IllegalMonitorStateException(),
             "current thread is not owner", false);
}

static void post_monitor_wait_event(EventJavaMonitorWait* event,
                                    ObjectMonitor* monitor,
                                    jlong notifier_tid,
                                    jlong timeout,
                                    bool timedout) {
  assert(event != NULL, "invariant");
  assert(monitor != NULL, "invariant");
  event->set_monitorClass(((oop)monitor->object())->klass());
  event->set_timeout(timeout);
  event->set_address((uintptr_t)monitor->object_addr());
  event->set_notifier(notifier_tid);
  event->set_timedOut(timedout);
  event->commit();
}

// -----------------------------------------------------------------------------
// Wait/Notify/NotifyAll
//
// Note: a subset of changes to ObjectMonitor::wait()
// will need to be replicated in complete_exit

// 条件变量(condition) 实现, 即 Object.wait().
void ObjectMonitor::wait(jlong millis, bool interruptible, TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "Must be Java thread!");
  JavaThread *jt = (JavaThread *)THREAD;

  assert(InitDone, "Unexpectedly not initialized");

  CHECK_OWNER();  // Throws IMSE if not owner.

  EventJavaMonitorWait event;

  // check for a pending interrupt
  if (interruptible && jt->is_interrupted(true) && !HAS_PENDING_EXCEPTION) {
    // post monitor waited event.  Note that this is past-tense, we are done waiting.
    if (JvmtiExport::should_post_monitor_waited()) {
      // Note: 'false' parameter is passed here because the
      // wait was not timed out due to thread interrupt.
      JvmtiExport::post_monitor_waited(jt, this, false);

      // In this short circuit of the monitor wait protocol, the
      // current thread never drops ownership of the monitor and
      // never gets added to the wait queue so the current thread
      // cannot be made the successor. This means that the
      // JVMTI_EVENT_MONITOR_WAITED event handler cannot accidentally
      // consume an unpark() meant for the ParkEvent associated with
      // this ObjectMonitor.
    }
    if (event.should_commit()) {
      post_monitor_wait_event(&event, this, 0, millis, false);
    }
    THROW(vmSymbols::java_lang_InterruptedException());
    return;
  }

  assert(Self->_Stalled == 0, "invariant");
  Self->_Stalled = intptr_t(this);
  jt->set_current_waiting_monitor(this);

  // create a node to be put into the queue
  // Critically, after we reset() the event but prior to park(), we must check
  // for a pending interrupt.
  ObjectWaiter node(Self);
  node.TState = ObjectWaiter::TS_WAIT;
  Self->_ParkEvent->reset();
  OrderAccess::fence();          // ST into Event; membar ; LD interrupted-flag

  // Enter the waiting queue, which is a circular doubly linked list in this case
  // but it could be a priority queue or any data structure.
  // _WaitSetLock protects the wait queue.  Normally the wait queue is accessed only
  // by the the owner of the monitor *except* in the case where park()
  // returns because of a timeout of interrupt.  Contention is exceptionally rare
  // so we use a simple spin-lock instead of a heavier-weight blocking lock.

  // 1. 将当前线程添加到 _WaitSet 中, 为了避免并发问题使用了自旋锁.
  // 获取自旋锁.
  Thread::SpinAcquire(&_WaitSetLock, "WaitSet - add");
  AddWaiter(&node);
  // 释放自旋锁.
  Thread::SpinRelease(&_WaitSetLock);

  // 2. 重置重入次数、更新 _waiters 计数 并调用 exit 方法退出 monitor.
  _Responsible = NULL;

  intx save = _recursions;     // record the old recursion count
  _waiters++;                  // increment the number of waiters
  _recursions = 0;             // set the recursion level to be 1
  exit(true, Self);                    // exit the monitor
  guarantee(_owner != Self, "invariant");

  // The thread is on the WaitSet list - now park() it.
  // On MP systems it's conceivable that a brief spin before we park
  // could be profitable.
  //
  // TODO-FIXME: change the following logic to a loop of the form
  //   while (!timeout && !interrupted && _notified == 0) park()

  // 3. 该线程位于 Waitset 列表中 - 现在 park(阻塞)它.
  // 在 MP 系统上，在 park 之前还要进行自旋操作.
  int ret = OS_OK;
  int WasNotified = 0;

  // Need to check interrupt state whilst still _thread_in_vm
  bool interrupted = interruptible && jt->is_interrupted(false);

  // 4. 状态转换:
  // * 如果节点在 WaitSet 中(节点状态为 TS_WAIT)则将其从 WaitSet 中移除.
  // * 如果节点状态为 TS_RUN 则重新执行 enter 方法进入 monitor,
  // * 如果节点状态为 TS_ENTER 或 TS_CXQ, 则调用 ReenterI 尝试重新进入 monitor.
  // 注：ReenterI 相比于 enter 方法不会将当前线程添加到 cxq 或 EntryList 中(因为处于 TS_ENTER 或 TS_CXQ 状态的节点已经处于两队列中), 仅会尝试获取锁, 失败则会 park(阻塞) 自身.
  { // State transition wrappers
    OSThread* osthread = Self->osthread();
    OSThreadWaitState osts(osthread, true);
    {
      ThreadBlockInVM tbivm(jt);
      // Thread is in thread_blocked state and oop access is unsafe.
      jt->set_suspend_equivalent();

      if (interrupted || HAS_PENDING_EXCEPTION) {
        // Intentionally empty
      } else if (node._notified == 0) {
        if (millis <= 0) {
          Self->_ParkEvent->park();
        } else {
          ret = Self->_ParkEvent->park(millis);
        }
      }

      // were we externally suspended while we were waiting?
      if (ExitSuspendEquivalent (jt)) {
        // TODO-FIXME: add -- if succ == Self then succ = null.
        jt->java_suspend_self();
      }

    } // Exit thread safepoint: transition _thread_blocked -> _thread_in_vm

    // 节点可能位于 WaitSet、EntryList（或 cxq) 或处于从 WaitSet 到 EntryList 的转换中.
    // 看看是否需要从 WaitSet 中删除节点.
    // 如果线程不在等待队列(WaitSet)中, 使用双重检查锁定(double-checked locking)来避免抓取 _WaitSetLock

    // 请注意，在取回 TState 之前，不需要 fence(又称为内存屏障, 能够防止指令重排序的指令).
    // 在最坏的情况下，将获取由 is 线程写入的过时的 TS_WAIT 值(也许甚至可以通过查看处理器自己的 store buffer 来满足，尽管鉴于先前的 ST 和此负载之间的代码路径的长度极不可能). 
    // 如果以下 LD 获取过时的 TS_WAIT 值，那么将获取锁，然后重新获取最新的 TS_WAIT 值. 也就是说，我们安全的失败了.
    // Node may be on the WaitSet, the EntryList (or cxq), or in transition
    // from the WaitSet to the EntryList.
    // See if we need to remove Node from the WaitSet.
    // We use double-checked locking to avoid grabbing _WaitSetLock
    // if the thread is not on the wait queue.
    //
    // Note that we don't need a fence before the fetch of TState.
    // In the worst case we'll fetch a old-stale value of TS_WAIT previously
    // written by the is thread. (perhaps the fetch might even be satisfied
    // by a look-aside into the processor's own store buffer, although given
    // the length of the code path between the prior ST and this load that's
    // highly unlikely).  If the following LD fetches a stale TS_WAIT value
    // then we'll acquire the lock and then re-fetch a fresh TState value.
    // That is, we fail toward safety.

    // TState 为 TS_WAIT 表示节点在 WaitSet 中, 由于节点目前刚从 WaitSet 中被唤醒, 因此需要从 WaitSet 中移除当前节点.
    if (node.TState == ObjectWaiter::TS_WAIT) {
      Thread::SpinAcquire(&_WaitSetLock, "WaitSet - unlink");
      if (node.TState == ObjectWaiter::TS_WAIT) {
        // 将当前节点从 WaitSet 重移除.
        DequeueSpecificWaiter(&node);       // unlink from WaitSet
        assert(node._notified == 0, "invariant");
        node.TState = ObjectWaiter::TS_RUN;
      }
      Thread::SpinRelease(&_WaitSetLock);
    }

    // The thread is now either on off-list (TS_RUN),
    // on the EntryList (TS_ENTER), or on the cxq (TS_CXQ).
    // The Node's TState variable is stable from the perspective of this thread.
    // No other threads will asynchronously modify TState.
    // 线程现在不在列表上 (TS_RUN), 在 EntryList (TS_ENTER)或 cxq (TS_cxq) 上.
    // 从这个线程的角度来看，节点的 TState 变量是稳定的.
    // 没有其他线程会异步修改 TState.
    guarantee(node.TState != ObjectWaiter::TS_WAIT, "invariant");
    OrderAccess::loadload();
    // 重置 _succ(假定继承人), 如果 _succ 为自身.
    if (_succ == Self) _succ = NULL;
    WasNotified = node._notified;

    // Reentry phase -- reacquire the monitor.
    // re-enter contended monitor after object.wait().
    // retain OBJECT_WAIT state until re-enter successfully completes
    // Thread state is thread_in_vm and oop access is again safe,
    // although the raw address of the object may have changed.
    // (Don't cache naked oops over safepoints, of course).

    // post monitor waited event. Note that this is past-tense, we are done waiting.
    if (JvmtiExport::should_post_monitor_waited()) {
      JvmtiExport::post_monitor_waited(jt, this, ret == OS_TIMEOUT);

      if (node._notified != 0 && _succ == Self) {
        // In this part of the monitor wait-notify-reenter protocol it
        // is possible (and normal) for another thread to do a fastpath
        // monitor enter-exit while this thread is still trying to get
        // to the reenter portion of the protocol.
        //
        // The ObjectMonitor was notified and the current thread is
        // the successor which also means that an unpark() has already
        // been done. The JVMTI_EVENT_MONITOR_WAITED event handler can
        // consume the unpark() that was done when the successor was
        // set because the same ParkEvent is shared between Java
        // monitors and JVM/TI RawMonitors (for now).
        //
        // We redo the unpark() to ensure forward progress, i.e., we
        // don't want all pending threads hanging (parked) with none
        // entering the unlocked monitor.
        node._event->unpark();
      }
    }

    if (event.should_commit()) {
      post_monitor_wait_event(&event, this, node._notifier_tid, millis, ret == OS_TIMEOUT);
    }

    OrderAccess::fence();

    assert(Self->_Stalled != 0, "invariant");
    Self->_Stalled = 0;

    assert(_owner != Self, "invariant");
    ObjectWaiter::TStates v = node.TState;
    // 如果状态为 TS_RUN 则重新执行 enter 方法进入 monitor, 否则调用 ReenterI 方法进入 monitor.
    if (v == ObjectWaiter::TS_RUN) {
      enter(Self);
    } else {
      guarantee(v == ObjectWaiter::TS_ENTER || v == ObjectWaiter::TS_CXQ, "invariant");
      ReenterI(Self, &node);
      node.wait_reenter_end(this);
    }

    // Self has reacquired the lock.
    // Lifecycle - the node representing Self must not appear on any queues.
    // Node is about to go out-of-scope, but even if it were immortal we wouldn't
    // want residual elements associated with this thread left on any lists.
    guarantee(node.TState == ObjectWaiter::TS_RUN, "invariant");
    assert(_owner == Self, "invariant");
    assert(_succ != Self, "invariant");
  } // OSThreadWaitState()

  jt->set_current_waiting_monitor(NULL);
  // 获取锁成功后还原记录的重入次数, 更新 _waiters 计数.
  guarantee(_recursions == 0, "invariant");
  _recursions = save;     // restore the old recursion count
  _waiters--;             // decrement the number of waiters

  // Verify a few postconditions
  assert(_owner == Self, "invariant");
  assert(_succ != Self, "invariant");
  assert(((oop)(object()))->mark() == markWord::encode(this), "invariant");

  // check if the notification happened
  if (!WasNotified) {
    // no, it could be timeout or Thread.interrupt() or both
    // check for interrupt event, otherwise it is timeout
    if (interruptible && jt->is_interrupted(true) && !HAS_PENDING_EXCEPTION) {
      THROW(vmSymbols::java_lang_InterruptedException());
    }
  }

  // NOTE: Spurious wake up will be consider as timeout.
  // Monitor notify has precedence over thread interrupt.
}


// Consider:
// If the lock is cool (cxq == null && succ == null) and we're on an MP system
// then instead of transferring a thread from the WaitSet to the EntryList
// we might just dequeue a thread from the WaitSet and directly unpark() it.
// 考虑：
// 如果锁很酷 (cxq == null && succ == null)，并且在一个 MP 系统上
// 然后将线程从 WaitSet 传输到 EntryList
// 我们可能只是将一个线程从 WaitSet 中取出，并直接对其进行 unpark() (唤醒阻塞的线程的方法).

// 实际的 Object.notify() 实现方法.
// * 如果 EntryList 为空, 将 WaitSet 头部节点移动到 _EntryList 中, 该节点为第一个节点.
// * 如果 EntryList 非空, 将 WaitSet 头部节点通过 CAS 移动到 _cxq 中, 该节点为头部(head)节点.
void ObjectMonitor::INotify(Thread * Self) {
  Thread::SpinAcquire(&_WaitSetLock, "WaitSet - notify");
  // 获取 WaitSet 队列头部节点.
  ObjectWaiter * iterator = DequeueWaiter();
  // 如果 WaitSet 不为空在进行 notify() 操作.
  if (iterator != NULL) {
    guarantee(iterator->TState == ObjectWaiter::TS_WAIT, "invariant");
    guarantee(iterator->_notified == 0, "invariant");
    // Disposition - what might we do with iterator ?
    // a.  add it directly to the EntryList - either tail (policy == 1)
    //     or head (policy == 0).
    // b.  push it onto the front of the _cxq (policy == 2).
    // For now we use (b).

    // 处置 - 我们可以用迭代器做什么?
    // a. 将节点直接添加到 EntryList - 任意尾部(policy == 1)或头部(policy == 0).
    // b. 将节点推送到 _cxq (policy == 2)
    // 现在我们使用 (b)
    iterator->TState = ObjectWaiter::TS_ENTER;

    iterator->_notified = 1;
    iterator->_notifier_tid = JFR_THREAD_ID(Self);

    ObjectWaiter * list = _EntryList;
    if (list != NULL) {
      assert(list->_prev == NULL, "invariant");
      assert(list->TState == ObjectWaiter::TS_ENTER, "invariant");
      assert(list != iterator, "invariant");
    }

    // prepend to cxq
    // * 如果 EntryList 为空, 直接将节点添加到 _EntryList 中, 该节点为第一个节点.
    // * 如果 EntryList 非空, 通过 CAS 将节点添加到 _cxq 中, 该节点为头部(head)节点.
    if (list == NULL) {
      iterator->_next = iterator->_prev = NULL;
      _EntryList = iterator;
    } else {
      iterator->TState = ObjectWaiter::TS_CXQ;
      for (;;) {
        ObjectWaiter * front = _cxq;
        iterator->_next = front;
        if (Atomic::cmpxchg(&_cxq, front, iterator) == front) {
          break;
        }
      }
    }

    // _WaitSetLock protects the wait queue, not the EntryList.  We could
    // move the add-to-EntryList operation, above, outside the critical section
    // protected by _WaitSetLock.  In practice that's not useful.  With the
    // exception of  wait() timeouts and interrupts the monitor owner
    // is the only thread that grabs _WaitSetLock.  There's almost no contention
    // on _WaitSetLock so it's not profitable to reduce the length of the
    // critical section.

    // _WaitSetLock 保护等待队列(wait queue), 而不是 EntryList.
    // 我们可以将上面的 add-to-EntryList 操作移到受 _WaitSetLock 保护的关键部分之外.
    // 实际上，这是没有用的. 除了 wait() 超时和中断之外，monitor 所有者是唯一获取 _WaitSetLock 的线程.
    // 几乎没有关于 _WaitSetLoc k的争论，因此减少关键部分的长度无利可图.
    iterator->wait_reenter_begin(this);
  }
  Thread::SpinRelease(&_WaitSetLock);
}

// Consider: a not-uncommon synchronization bug is to use notify() when
// notifyAll() is more appropriate, potentially resulting in stranded
// threads; this is one example of a lost wakeup. A useful diagnostic
// option is to force all notify() operations to behave as notifyAll().
//
// Note: We can also detect many such problems with a "minimum wait".
// When the "minimum wait" is set to a small non-zero timeout value
// and the program does not hang whereas it did absent "minimum wait",
// that suggests a lost wakeup bug.
// Object.notify() 实现.
void ObjectMonitor::notify(TRAPS) {
  CHECK_OWNER();  // Throws IMSE if not owner.
  // 如果 _WaitSet 为空直接返回.
  if (_WaitSet == NULL) {
    return;
  }
  DTRACE_MONITOR_PROBE(notify, this, object(), THREAD);
  INotify(THREAD);
  OM_PERFDATA_OP(Notifications, inc(1));
}


// The current implementation of notifyAll() transfers the waiters one-at-a-time
// from the waitset to the EntryList. This could be done more efficiently with a
// single bulk transfer but in practice it's not time-critical. Beware too,
// that in prepend-mode we invert the order of the waiters. Let's say that the
// waitset is "ABCD" and the EntryList is "XYZ". After a notifyAll() in prepend
// mode the waitset will be empty and the EntryList will be "DCBAXYZ".
// notifyAll() 的当前实现将 waiters 一次一个地从 waitset 传输到 EntryList.
// 单次批量传输可以更有效地实现这一点，但实际上并不需要时间.
// 还要注意，在预端模式(prepend-mode)下，我们会颠倒 waiters 的顺序. 假设 waitset 是 "ABCD"，EntryList 是 "XYZ".
// 在预端模式模式下执行 notifyAll() 后，waitset 将为空，EntryList 将为 "DCBAXYZ".

// Object.notifyAll() 实现, 目前实现逻辑如下:
// 在循环调用 INotify() 方法, 将 WaitSet 中的线程逐个转移到 _cxq 队列中.
// 每次转移都会将 WaitSet 队列头部节点, 添加到 _cxq 队列头部.
// 假设 waitset 是 "ABCD" _cxq 是 "XYZ", 转移后 waitset 为空, 而 _cxq 为 "DCBAXYZ"
void ObjectMonitor::notifyAll(TRAPS) {
  CHECK_OWNER();  // Throws IMSE if not owner.
  if (_WaitSet == NULL) {
    return;
  }

  DTRACE_MONITOR_PROBE(notifyAll, this, object(), THREAD);
  int tally = 0;
  // 在循环中调用 INotify() 逐个将 waitset 中的节点转移到 _cxq 中.
  while (_WaitSet != NULL) {
    tally++;
    INotify(THREAD);
  }

  OM_PERFDATA_OP(Notifications, inc(tally));
}

// -----------------------------------------------------------------------------
// Adaptive Spinning Support
//
// Adaptive spin-then-block - rational spinning
//
// Note that we spin "globally" on _owner with a classic SMP-polite TATAS
// algorithm.  On high order SMP systems it would be better to start with
// a brief global spin and then revert to spinning locally.  In the spirit of MCS/CLH,
// a contending thread could enqueue itself on the cxq and then spin locally
// on a thread-specific variable such as its ParkEvent._Event flag.
// That's left as an exercise for the reader.  Note that global spinning is
// not problematic on Niagara, as the L2 cache serves the interconnect and
// has both low latency and massive bandwidth.
//
// Broadly, we can fix the spin frequency -- that is, the % of contended lock
// acquisition attempts where we opt to spin --  at 100% and vary the spin count
// (duration) or we can fix the count at approximately the duration of
// a context switch and vary the frequency.   Of course we could also
// vary both satisfying K == Frequency * Duration, where K is adaptive by monitor.
// For a description of 'Adaptive spin-then-block mutual exclusion in
// multi-threaded processing,' see U.S. Pat. No. 8046758.
//
// This implementation varies the duration "D", where D varies with
// the success rate of recent spin attempts. (D is capped at approximately
// length of a round-trip context switch).  The success rate for recent
// spin attempts is a good predictor of the success rate of future spin
// attempts.  The mechanism adapts automatically to varying critical
// section length (lock modality), system load and degree of parallelism.
// D is maintained per-monitor in _SpinDuration and is initialized
// optimistically.  Spin frequency is fixed at 100%.
//
// Note that _SpinDuration is volatile, but we update it without locks
// or atomics.  The code is designed so that _SpinDuration stays within
// a reasonable range even in the presence of races.  The arithmetic
// operations on _SpinDuration are closed over the domain of legal values,
// so at worst a race will install and older but still legal value.
// At the very worst this introduces some apparent non-determinism.
// We might spin when we shouldn't or vice-versa, but since the spin
// count are relatively short, even in the worst case, the effect is harmless.
//
// Care must be taken that a low "D" value does not become an
// an absorbing state.  Transient spinning failures -- when spinning
// is overall profitable -- should not cause the system to converge
// on low "D" values.  We want spinning to be stable and predictable
// and fairly responsive to change and at the same time we don't want
// it to oscillate, become metastable, be "too" non-deterministic,
// or converge on or enter undesirable stable absorbing states.
//
// We implement a feedback-based control system -- using past behavior
// to predict future behavior.  We face two issues: (a) if the
// input signal is random then the spin predictor won't provide optimal
// results, and (b) if the signal frequency is too high then the control
// system, which has some natural response lag, will "chase" the signal.
// (b) can arise from multimodal lock hold times.  Transient preemption
// can also result in apparent bimodal lock hold times.
// Although sub-optimal, neither condition is particularly harmful, as
// in the worst-case we'll spin when we shouldn't or vice-versa.
// The maximum spin duration is rather short so the failure modes aren't bad.
// To be conservative, I've tuned the gain in system to bias toward
// _not spinning.  Relatedly, the system can sometimes enter a mode where it
// "rings" or oscillates between spinning and not spinning.  This happens
// when spinning is just on the cusp of profitability, however, so the
// situation is not dire.  The state is benign -- there's no need to add
// hysteresis control to damp the transition rate between spinning and
// not spinning.

// Spinning: Fixed frequency (100%), vary duration
// 尝试通过自旋获取锁. 自旋方式有两种：
// 1. 固定次数自旋.
// 2. 自适应自旋((Adaptive Spinning).
int ObjectMonitor::TrySpin(Thread * Self) {
  // Dumb, brutal spin.  Good for comparative measurements against adaptive spinning.
  int ctr = Knob_FixedSpin;
  // 1. 如果是固定次数的自旋, 则自旋固定的次数(由 Knob_FixedSpin 确定), 自旋过程中通过 CAS 尝试获取锁.
  if (ctr != 0) {
    while (--ctr >= 0) {
      if (TryLock(Self) > 0) return 1;
      SpinPause();
    }
    return 0;
  }

  // 2. 预自旋 Knob_PreSpin + 1 次, 如果成功增加 _SpinDuration（自旋次数）然后返回.
  // Knob_PreSpin 初始值 10.
  for (ctr = Knob_PreSpin + 1; --ctr >= 0;) {
    if (TryLock(Self) > 0) {
      // Increase _SpinDuration ...
      // Note that we don't clamp SpinDuration precisely at SpinLimit.
      // Raising _SpurDuration to the poverty line is key.
      int x = _SpinDuration;
      // 自旋次数不能超过 Knob_SpinLimit(5000).
      if (x < Knob_SpinLimit) {
        // 自旋次数最低值为 Knob_Poverty(1000) .
        if (x < Knob_Poverty) x = Knob_Poverty;
        // 自旋成功时, 自旋次数一次增加 Knob_BonusB(100) .
        _SpinDuration = x + Knob_BonusB;
      }
      return 1;
    }
    SpinPause();
  }

  // Admission control - verify preconditions for spinning
  //
  // We always spin a little bit, just to prevent _SpinDuration == 0 from
  // becoming an absorbing state.  Put another way, we spin briefly to
  // sample, just in case the system load, parallelism, contention, or lock
  // modality changed.
  //
  // Consider the following alternative:
  // Periodically set _SpinDuration = _SpinLimit and try a long/full
  // spin attempt.  "Periodically" might mean after a tally of
  // the # of failed spin attempts (or iterations) reaches some threshold.
  // This takes us into the realm of 1-out-of-N spinning, where we
  // hold the duration constant but vary the frequency.

  // 准入控制 - 验证自旋的前提条件.
  // 
  // 我们总是旋转一点，只是为了防止 _SpinDuration(旋转持续时间) == 0 成为一种吸引人的状态. 
  // 换句话说，我们简单地旋转到示例，以防系统加载、并行、争用或锁定形态改变.
  // 考虑以下替代方案：

  // 定期设置 _spinduration = _spinlimit 并尝试长/完全自旋. "定期"可能意味着在失败的自旋尝试（或迭代）的故障 ＃ 的计数之后达到一些阈值.
  // 这将我们带入 1-Out-N 的自旋，在那里自旋时间固定, 但改变频率.
  //

  // 3. 根据 _SpinDuration (自旋次数)进行自适应自旋.
  ctr = _SpinDuration;
  // 3.1 如果自旋次数小于等于 0 直接退出.
  if (ctr <= 0) return 0;
  // 3.2 如果线程不是 java 线程或 VM 线程或 _owner 未运行, 直接返回.
  //     当获取锁的线程未运行时通过自旋方式获取锁没有任何意义, 因为锁不会被释放.
  if (NotRunnable(Self, (Thread *) _owner)) {
    return 0;
  }

  // We're good to spin ... spin ingress.
  // CONSIDER: use Prefetch::write() to avoid RTS->RTO upgrades
  // when preparing to LD...CAS _owner, etc and the CAS is likely
  // to succeed.
  if (_succ == NULL) {
    _succ = Self;
  }
  Thread * prv = NULL;

  // There are three ways to exit the following loop:
  // 1.  A successful spin where this thread has acquired the lock.
  // 2.  Spin failure with prejudice
  // 3.  Spin failure without prejudice

  //有三种方法可以退出以下循环：
  // 1. 自旋期间此线程成功获得锁.
  // 2. 带偏向的自旋失败.
  // 3. 无偏向的自旋失败.
  // 根据 _SpinDuration(自旋次数)进行自旋.
  while (--ctr >= 0) {

    // Periodic polling -- Check for pending GC
    // Threads may spin while they're unsafe.
    // We don't want spinning threads to delay the JVM from reaching
    // a stop-the-world safepoint or to steal cycles from GC.
    // If we detect a pending safepoint we abort in order that
    // (a) this thread, if unsafe, doesn't delay the safepoint, and (b)
    // this thread, if safe, doesn't steal cycles from GC.
    // This is in keeping with the "no loitering in runtime" rule.
    // We periodically check to see if there's a safepoint pending.

    // JVM 不希望自旋线程延迟 JVM 到达 stop-the-world(STW) 安全点或窃取 GC 的周期.
    //（a）如果线程不安全，则不会延迟安全点(safepoint).
    //（b）如果线程安全，则不会窃取 GC 的周期.
    // 因此这里会周期的检查, 让能够自旋的是不安全的线程.
    if ((ctr & 0xFF) == 0) {
      if (SafepointMechanism::should_block(Self)) {
        goto Abort;           // abrupt spin egress
      }
      SpinPause();
    }

    // Probe _owner with TATAS
    // If this thread observes the monitor transition or flicker
    // from locked to unlocked to locked, then the odds that this
    // thread will acquire the lock in this spin attempt go down
    // considerably.  The same argument applies if the CAS fails
    // or if we observe _owner change from one non-null value to
    // another non-null value.   In such cases we might abort
    // the spin without prejudice or apply a "penalty" to the
    // spin count-down variable "ctr", reducing it by 100, say.

    Thread * ox = (Thread *) _owner;
    // 如果 monitor 未被获取, 尝试通过 CAS 获取锁.
    // 获取成功则增加 _SpinDuration(自旋次数).
    if (ox == NULL) {
      ox = (Thread*)Atomic::cmpxchg(&_owner, (void*)NULL, Self);

      if (ox == NULL) {
        // The CAS succeeded -- this thread acquired ownership
        // Take care of some bookkeeping to exit spin state.
        if (_succ == Self) {
          _succ = NULL;
        }

        // Increase _SpinDuration :
        // The spin was successful (profitable) so we tend toward
        // longer spin attempts in the future.
        // CONSIDER: factor "ctr" into the _SpinDuration adjustment.
        // If we acquired the lock early in the spin cycle it
        // makes sense to increase _SpinDuration proportionally.
        // Note that we don't clamp SpinDuration precisely at SpinLimit.
        int x = _SpinDuration;
        if (x < Knob_SpinLimit) {
          if (x < Knob_Poverty) x = Knob_Poverty;
          _SpinDuration = x + Knob_Bonus;
        }
        return 1;
      }

      // The CAS failed ... we can take any of the following actions:
      // * penalize: ctr -= CASPenalty
      // * exit spin with prejudice -- goto Abort;
      // * exit spin without prejudice.
      // * Since CAS is high-latency, retry again immediately.
      prv = ox;
      goto Abort;
    }

    // Did lock ownership change hands ?
    // 当上次循环的 _owner 和此处循环不一样, 则表示期间锁被释放然后被其他线程获取, 此时直接退出. 
    if (ox != prv && prv != NULL) {
      goto Abort;
    }
    prv = ox;

    // Abort the spin if the owner is not executing.
    // The owner must be executing in order to drop the lock.
    // Spinning while the owner is OFFPROC is idiocy.
    // Consider: ctr -= RunnablePenalty ;
    if (NotRunnable(Self, ox)) {
      goto Abort;
    }
    if (_succ == NULL) {
      _succ = Self;
    }
  }

  // Spin failed with prejudice -- reduce _SpinDuration.
  // TODO: Use an AIMD-like policy to adjust _SpinDuration.
  // AIMD is globally stable.
  // 带偏向的自旋失败, 减少磁选次数.
  {
    int x = _SpinDuration;
    if (x > 0) {
      // Consider an AIMD scheme like: x -= (x >> 3) + 100
      // This is globally sample and tends to damp the response.
      // 自旋次数一次减少 Knob_Penalty(200).
      x -= Knob_Penalty;
      if (x < 0) x = 0;
      _SpinDuration = x;
    }
  }

 Abort:
  if (_succ == Self) {
    _succ = NULL;
    // Invariant: after setting succ=null a contending thread
    // must recheck-retry _owner before parking.  This usually happens
    // in the normal usage of TrySpin(), but it's safest
    // to make TrySpin() as foolproof as possible.
    OrderAccess::fence();
    if (TryLock(Self) > 0) return 1;
  }
  return 0;
}

// NotRunnable() -- informed spinning
//
// Don't bother spinning if the owner is not eligible to drop the lock.
// Spin only if the owner thread is _thread_in_Java or _thread_in_vm.
// The thread must be runnable in order to drop the lock in timely fashion.
// If the _owner is not runnable then spinning will not likely be
// successful (profitable).
//
// Beware -- the thread referenced by _owner could have died
// so a simply fetch from _owner->_thread_state might trap.
// Instead, we use SafeFetchXX() to safely LD _owner->_thread_state.
// Because of the lifecycle issues, the _thread_state values
// observed by NotRunnable() might be garbage.  NotRunnable must
// tolerate this and consider the observed _thread_state value
// as advisory.
//
// Beware too, that _owner is sometimes a BasicLock address and sometimes
// a thread pointer.
// Alternately, we might tag the type (thread pointer vs basiclock pointer)
// with the LSB of _owner.  Another option would be to probabilistically probe
// the putative _owner->TypeTag value.
//
// Checking _thread_state isn't perfect.  Even if the thread is
// in_java it might be blocked on a page-fault or have been preempted
// and sitting on a ready/dispatch queue.
//
// The return value from NotRunnable() is *advisory* -- the
// result is based on sampling and is not necessarily coherent.
// The caller must tolerate false-negative and false-positive errors.
// Spinning, in general, is probabilistic anyway.


int ObjectMonitor::NotRunnable(Thread * Self, Thread * ox) {
  // Check ox->TypeTag == 2BAD.
  if (ox == NULL) return 0;

  // Avoid transitive spinning ...
  // Say T1 spins or blocks trying to acquire L.  T1._Stalled is set to L.
  // Immediately after T1 acquires L it's possible that T2, also
  // spinning on L, will see L.Owner=T1 and T1._Stalled=L.
  // This occurs transiently after T1 acquired L but before
  // T1 managed to clear T1.Stalled.  T2 does not need to abort
  // its spin in this circumstance.
  intptr_t BlockedOn = SafeFetchN((intptr_t *) &ox->_Stalled, intptr_t(1));

  if (BlockedOn == 1) return 1;
  if (BlockedOn != 0) {
    return BlockedOn != intptr_t(this) && _owner == ox;
  }

  assert(sizeof(((JavaThread *)ox)->_thread_state == sizeof(int)), "invariant");
  int jst = SafeFetch32((int *) &((JavaThread *) ox)->_thread_state, -1);;
  // consider also: jst != _thread_in_Java -- but that's overspecific.
  return jst == _thread_blocked || jst == _thread_in_native;
}


// -----------------------------------------------------------------------------
// WaitSet management ...

ObjectWaiter::ObjectWaiter(Thread* thread) {
  _next     = NULL;
  _prev     = NULL;
  _notified = 0;
  _notifier_tid = 0;
  TState    = TS_RUN;
  _thread   = thread;
  _event    = thread->_ParkEvent;
  _active   = false;
  assert(_event != NULL, "invariant");
}

void ObjectWaiter::wait_reenter_begin(ObjectMonitor * const mon) {
  JavaThread *jt = (JavaThread *)this->_thread;
  _active = JavaThreadBlockedOnMonitorEnterState::wait_reenter_begin(jt, mon);
}

void ObjectWaiter::wait_reenter_end(ObjectMonitor * const mon) {
  JavaThread *jt = (JavaThread *)this->_thread;
  JavaThreadBlockedOnMonitorEnterState::wait_reenter_end(jt, _active);
}

inline void ObjectMonitor::AddWaiter(ObjectWaiter* node) {
  assert(node != NULL, "should not add NULL node");
  assert(node->_prev == NULL, "node already in list");
  assert(node->_next == NULL, "node already in list");
  // put node at end of queue (circular doubly linked list)
  if (_WaitSet == NULL) {
    _WaitSet = node;
    node->_prev = node;
    node->_next = node;
  } else {
    ObjectWaiter* head = _WaitSet;
    ObjectWaiter* tail = head->_prev;
    assert(tail->_next == head, "invariant check");
    tail->_next = node;
    head->_prev = node;
    node->_next = head;
    node->_prev = tail;
  }
}

inline ObjectWaiter* ObjectMonitor::DequeueWaiter() {
  // dequeue the very first waiter
  ObjectWaiter* waiter = _WaitSet;
  if (waiter) {
    DequeueSpecificWaiter(waiter);
  }
  return waiter;
}

inline void ObjectMonitor::DequeueSpecificWaiter(ObjectWaiter* node) {
  assert(node != NULL, "should not dequeue NULL node");
  assert(node->_prev != NULL, "node already removed from list");
  assert(node->_next != NULL, "node already removed from list");
  // when the waiter has woken up because of interrupt,
  // timeout or other spurious wake-up, dequeue the
  // waiter from waiting list
  ObjectWaiter* next = node->_next;
  if (next == node) {
    assert(node->_prev == node, "invariant check");
    _WaitSet = NULL;
  } else {
    ObjectWaiter* prev = node->_prev;
    assert(prev->_next == node, "invariant check");
    assert(next->_prev == node, "invariant check");
    next->_prev = prev;
    prev->_next = next;
    if (_WaitSet == node) {
      _WaitSet = next;
    }
  }
  node->_next = NULL;
  node->_prev = NULL;
}

// -----------------------------------------------------------------------------
// PerfData support
PerfCounter * ObjectMonitor::_sync_ContendedLockAttempts       = NULL;
PerfCounter * ObjectMonitor::_sync_FutileWakeups               = NULL;
PerfCounter * ObjectMonitor::_sync_Parks                       = NULL;
PerfCounter * ObjectMonitor::_sync_Notifications               = NULL;
PerfCounter * ObjectMonitor::_sync_Inflations                  = NULL;
PerfCounter * ObjectMonitor::_sync_Deflations                  = NULL;
PerfLongVariable * ObjectMonitor::_sync_MonExtant              = NULL;

// One-shot global initialization for the sync subsystem.
// We could also defer initialization and initialize on-demand
// the first time we call ObjectSynchronizer::inflate().
// Initialization would be protected - like so many things - by
// the MonitorCache_lock.

void ObjectMonitor::Initialize() {
  assert(!InitDone, "invariant");

  if (!os::is_MP()) {
    Knob_SpinLimit = 0;
    Knob_PreSpin   = 0;
    Knob_FixedSpin = -1;
  }

  if (UsePerfData) {
    EXCEPTION_MARK;
#define NEWPERFCOUNTER(n)                                                \
  {                                                                      \
    n = PerfDataManager::create_counter(SUN_RT, #n, PerfData::U_Events,  \
                                        CHECK);                          \
  }
#define NEWPERFVARIABLE(n)                                                \
  {                                                                       \
    n = PerfDataManager::create_variable(SUN_RT, #n, PerfData::U_Events,  \
                                         CHECK);                          \
  }
    NEWPERFCOUNTER(_sync_Inflations);
    NEWPERFCOUNTER(_sync_Deflations);
    NEWPERFCOUNTER(_sync_ContendedLockAttempts);
    NEWPERFCOUNTER(_sync_FutileWakeups);
    NEWPERFCOUNTER(_sync_Parks);
    NEWPERFCOUNTER(_sync_Notifications);
    NEWPERFVARIABLE(_sync_MonExtant);
#undef NEWPERFCOUNTER
#undef NEWPERFVARIABLE
  }

  DEBUG_ONLY(InitDone = true;)
}

void ObjectMonitor::print_on(outputStream* st) const {
  // The minimal things to print for markWord printing, more can be added for debugging and logging.
  st->print("{contentions=0x%08x,waiters=0x%08x"
            ",recursions=" INTX_FORMAT ",owner=" INTPTR_FORMAT "}",
            contentions(), waiters(), recursions(),
            p2i(owner()));
}
void ObjectMonitor::print() const { print_on(tty); }

#ifdef ASSERT
// Print the ObjectMonitor like a debugger would:
//
// (ObjectMonitor) 0x00007fdfb6012e40 = {
//   _header = 0x0000000000000001
//   _object = 0x000000070ff45fd0
//   _next_om = 0x0000000000000000
//   _pad_buf0 = {
//     [0] = '\0'
//     ...
//     [103] = '\0'
//   }
//   _owner = 0x0000000000000000
//   _previous_owner_tid = 0
//   _recursions = 0
//   _EntryList = 0x0000000000000000
//   _cxq = 0x0000000000000000
//   _succ = 0x0000000000000000
//   _Responsible = 0x0000000000000000
//   _Spinner = 0
//   _SpinDuration = 5000
//   _contentions = 0
//   _WaitSet = 0x0000700009756248
//   _waiters = 1
//   _WaitSetLock = 0
// }
//
void ObjectMonitor::print_debug_style_on(outputStream* st) const {
  st->print_cr("(ObjectMonitor*) " INTPTR_FORMAT " = {", p2i(this));
  st->print_cr("  _header = " INTPTR_FORMAT, header().value());
  st->print_cr("  _object = " INTPTR_FORMAT, p2i(_object));
  st->print_cr("  _next_om = " INTPTR_FORMAT, p2i(_next_om));
  st->print_cr("  _pad_buf0 = {");
  st->print_cr("    [0] = '\\0'");
  st->print_cr("    ...");
  st->print_cr("    [%d] = '\\0'", (int)sizeof(_pad_buf0) - 1);
  st->print_cr("  }");
  st->print_cr("  _owner = " INTPTR_FORMAT, p2i(_owner));
  st->print_cr("  _previous_owner_tid = " JLONG_FORMAT, _previous_owner_tid);
  st->print_cr("  _recursions = " INTX_FORMAT, _recursions);
  st->print_cr("  _EntryList = " INTPTR_FORMAT, p2i(_EntryList));
  st->print_cr("  _cxq = " INTPTR_FORMAT, p2i(_cxq));
  st->print_cr("  _succ = " INTPTR_FORMAT, p2i(_succ));
  st->print_cr("  _Responsible = " INTPTR_FORMAT, p2i(_Responsible));
  st->print_cr("  _Spinner = %d", _Spinner);
  st->print_cr("  _SpinDuration = %d", _SpinDuration);
  st->print_cr("  _contentions = %d", _contentions);
  st->print_cr("  _WaitSet = " INTPTR_FORMAT, p2i(_WaitSet));
  st->print_cr("  _waiters = %d", _waiters);
  st->print_cr("  _WaitSetLock = %d", _WaitSetLock);
  st->print_cr("}");
}
#endif
