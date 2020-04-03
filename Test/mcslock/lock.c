#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

struct lock {
  uint32_t wait;
  struct lock *next;
};

typedef struct lock lock;

#ifdef __GNUC__

#define CAS(_a, _n, _o)                                                 \
  ({ __typeof__(_o) __o = _o;                                           \
    __asm__ __volatile__(                                               \
                         "lock cmpxchg %3,%1"                           \
                         : "=a" (__o), "=m" (*(volatile unsigned int *)(_a)) \
                         :  "0" (__o), "r" (_n) );                      \
    __o;                                                                \
  })

#define MFENCE() asm volatile ("mfence" ::: "memory")

#endif

void acquire(lock **tail, lock *myLock) {
  lock *oldTail;
  lock *readTail;

  (*myLock).next = NULL;

  oldTail = *tail;
  readTail = CAS(tail, myLock, oldTail);
  while (readTail != oldTail) {
    oldTail = *tail;
    readTail = CAS(tail, myLock, oldTail);
  }

  if (oldTail != NULL) {
    (*myLock).wait = 1;
    MFENCE();
    (*oldTail).next = myLock;
    while ((*myLock).wait != 0) {}
  }
}

void release(lock **tail, lock* myLock) {
  lock *nextLock;
  lock *readTail;

  readTail = CAS(tail, NULL, myLock);
  if (readTail == myLock) {
  }
  else {
    while ((*myLock).next == NULL) {}

    nextLock = (*myLock).next;
    (*nextLock).wait = 0;
  }
}

// testing
lock locks[6];
char messages[5][20] =
  {
   "thread 1",
   "thread 2",
   "thread 3",
   "thread 4",
   "thread 5"
};
lock *tail;

void my_puts_unlocked(char *str) {
  while (*str != '\0') {
    putc_unlocked(*str, stdout);
    ++ str;
  }
  putc_unlocked('\n', stdout);
}

void racy_printer(void *arg) {
  uint32_t index = (uint32_t) arg;
  index = index;
  for (int i = 0; i < 10; ++ i) {
    acquire(&tail, &locks[index]);
    my_puts_unlocked(messages[index]);
    release(&tail, &locks[index]);
  }
}

#ifdef __GNUC__

#include <pthread.h>

void thread_create(void (*thread) (void *), void *arg) {
  pthread_t pthread;

  pthread_create(&pthread, NULL, (void * (*) (void *))thread, arg);
}

#endif

int main() {
  tail = NULL;
  acquire(&tail, &locks[5]);
  for (int i = 0; i < 5; ++ i) {
    thread_create(racy_printer, (void *)i);
  }
  my_puts_unlocked("Finished thread creation");
  release(&tail, &locks[5]);
  sleep(1);
  return 0;
}
