#pragma once
#include "DafnyRuntime.h"

// Extern for sqrt
uint32 rnd()
{
  uint32 x = (uint32) rand() % 0xFFFF;
  return x;
}

void init_random()
{
  srand(time(NULL));
}

void print_uint32(uint32 i)
{
  printf("%lu\n", i);
}


// Extern for lock
// testing
char messages[6][50] =
  {
   "thread 1",
   "thread 2",
   "thread 3",
   "thread 4",
   "thread 5",
   "Finished thread creation"
};

void my_puts_unlocked(uint32 i) {
  char* str = messages[i];
  while (*str != '\0') {
    #ifdef __GNUC__
    putc_unlocked(*str, stdout);
    #else 
    putc(*str, stdout);
    #endif
    ++ str;
  }
   #ifdef __GNUC__
    putc_unlocked('\n', stdout);
    #else 
    putc('\n', stdout);
    #endif
}

void my_sleep(uint32 n) {
  sleep(n);
}

// Extern for enqueue
void enqueue_log(uint32 k, uint32 v) {}
void dequeue_log(uint32 k, uint32 v) {}
