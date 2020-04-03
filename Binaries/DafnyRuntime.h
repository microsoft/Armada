#pragma once
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
typedef unsigned char       uint8;
typedef unsigned short     uint16;
typedef unsigned long      uint32;


// ClightTSO does not support 64-bit int, so we use 32-bit for now.
#ifdef __GNUC__
typedef unsigned long long uint64;
#else
typedef unsigned long uint64;
#endif

typedef char       int8;
typedef short     int16;
typedef long      int32;

// ClightTSO does not support 64-bit int, so we use 32-bit for now.
#ifdef __GNUC__
typedef long long int64;
#else
typedef long      int64;
#endif

typedef pthread_t tid;

/*********************************************************
 *  UTILITIES                                            *
 *********************************************************/



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



