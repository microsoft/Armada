// This file contains the benchmark for armada implementation of bounded_singleproducer_singleconsumer queue.


// 1. Armada with CompCertTSO
//    First copy bench_armada.c, extern.h and DafnyRuntime.h to the CompCertTSO directory,
//    Then run the following instruction to compile:
//    ./ccomp -ralloc -stdlib runtime -lpthread -o bench_armada bench_armada.c

// To run the benchmark:
// ./bench_armada number_elements number_of_runs | tee log_{number_elements}_{number_of_runs}.txt

// number_elements is the size of the queue, it has to be 2^n, n > 0;
// number_of_runs is the number of runs we want to exec.
// The program will print total_time(secs) and throughput(ops/sec) for each run to stdout
// and tee will log the reults to the file.

#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <stdlib.h> 
#include <time.h>

// Dafny program queue.arm compiled into ClightTSO
#include "DafnyRuntime.h"
#include "extern.h"
// namespace _8_SharedStructs 
struct BSSQueueElement;
typedef struct BSSQueueElement BSSQueueElement;
struct BSSQueueElement {
  uint32 key;
  uint32 value;
};
struct QbssState;
typedef struct QbssState QbssState;
struct QbssState {
  uint32 array_size;
  uint32 mask;
  uint32 read_index;
  uint32 write_index;
  struct BSSQueueElement* element_array;
  uint32* user_state;
};
// namespace _11_EnqueueBSS 
// Global Variables
// Param Stucts
struct _params_of_enqueue_log;
typedef struct _params_of_enqueue_log _params_of_enqueue_log;
struct _params_of_enqueue_log {
  uint32 k;
  uint32 v;
};
struct _params_of_dequeue_log;
typedef struct _params_of_dequeue_log _params_of_dequeue_log;
struct _params_of_dequeue_log {
  uint32 k;
  uint32 v;
};
struct _params_of_enqueue;
typedef struct _params_of_enqueue _params_of_enqueue;
struct _params_of_enqueue {
  struct QbssState* state;
  uint32 k;
  uint32 v;
};
struct _params_of_dequeue;
typedef struct _params_of_dequeue _params_of_dequeue;
struct _params_of_dequeue {
  struct QbssState* state;
  uint32* k;
  uint32* v;
};
struct _params_of_init_queue;
typedef struct _params_of_init_queue _params_of_init_queue;
struct _params_of_init_queue {
  struct QbssState* que;
  uint32 size;
};
struct _params_of__main;
typedef struct _params_of__main _params_of__main;
struct _params_of__main {
};
// Method Decls
void* _thread_of_enqueue_log (void* vargs);
void* _thread_of_dequeue_log (void* vargs);
uint32 enqueue(struct QbssState* state, uint32 k, uint32 v);
void* _thread_of_enqueue (void* vargs);
uint32 dequeue(struct QbssState* state, uint32* k, uint32* v);
void* _thread_of_dequeue (void* vargs);
void init_queue(struct QbssState* que, uint32 size);
void* _thread_of_init_queue (void* vargs);
void _main();
void* _thread_of__main (void* vargs);
// Methods Defns
// Skipped extern method enqueue_log
void* _thread_of_enqueue_log (void* vargs) {
  _params_of_enqueue_log args = *((_params_of_enqueue_log *) vargs);
  enqueue_log (args.k,args.v);
  return NULL;
}
// Skipped extern method dequeue_log
void* _thread_of_dequeue_log (void* vargs) {
  _params_of_dequeue_log args = *((_params_of_dequeue_log *) vargs);
  dequeue_log (args.k,args.v);
  return NULL;
}
// Beginning of method enqueue
uint32 enqueue(struct QbssState* state, uint32 k, uint32 v)
{
  uint32 ret = 0;
  uint32 _0_write__index;
  _0_write__index = (*(state)).write_index;
after_0: ;
  uint32 _1_mask;
  _1_mask = (*(state)).mask;
  uint32 _2_read__index;
  _2_read__index = (*(state)).read_index;
  struct BSSQueueElement* _3_e = NULL;
  if ((((_0_write__index) + ((uint32)1)) & (_1_mask)) != (_2_read__index)) {
    _3_e = ((*(state)).element_array) + (_0_write__index);
  after_2: ;
    (*(_3_e)).key = k;
  after_3: ;
    (*(_3_e)).value = v;
  after_4: ;
    (*(state)).write_index = ((_0_write__index) + ((uint32)1)) & (_1_mask);
  after_5: ;
    ret = (uint32)1;
    return ret;
  after_6: ;
  }
after_1: ;
  ret = (uint32)0;
  return ret;
}
void* _thread_of_enqueue (void* vargs) {
  _params_of_enqueue args = *((_params_of_enqueue *) vargs);
  enqueue (args.state,args.k,args.v);
  return NULL;
}
// End of method enqueue

// Beginning of method dequeue
uint32 dequeue(struct QbssState* state, uint32* k, uint32* v)
{
  uint32 ret = 0;
  uint32 _4_write__index;
  _4_write__index = (*(state)).write_index;
  uint32 _5_mask;
  _5_mask = (*(state)).mask;
  uint32 _6_read__index;
  _6_read__index = (*(state)).read_index;
  struct BSSQueueElement* _7_e = NULL;
  uint32 _8_key = 0;
  uint32 _9_value = 0;
  if ((_6_read__index) != (_4_write__index)) {
    _7_e = ((*(state)).element_array) + (_6_read__index);
    if ((k) != (NULL)) {
      _8_key = (*(_7_e)).key;
      *k = _8_key;
    }
    if ((v) != (NULL)) {
      _9_value = (*(_7_e)).value;
      *v = _9_value;
    }
    (*(state)).read_index = ((_6_read__index) + ((uint32)1)) & (_5_mask);
    ret = (uint32)1;
    return ret;
  }
  ret = (uint32)0;
  return ret;
}
void* _thread_of_dequeue (void* vargs) {
  _params_of_dequeue args = *((_params_of_dequeue *) vargs);
  dequeue (args.state,args.k,args.v);
  return NULL;
}
// End of method dequeue

// Beginning of method init_queue
void init_queue(struct QbssState* que, uint32 size)
{
  (*(que)).array_size = size;
  (*(que)).user_state = NULL;
  (*(que)).mask = (size) - ((uint32)1);
  (*(que)).element_array = (struct BSSQueueElement*) calloc((size_t)(size), sizeof(struct BSSQueueElement));
  (*(que)).write_index = (uint32)0;
  (*(que)).read_index = (uint32)0;
}
void* _thread_of_init_queue (void* vargs) {
  _params_of_init_queue args = *((_params_of_init_queue *) vargs);
  init_queue (args.que,args.size);
  return NULL;
}
// End of method init_queue


// Beginning of Bench code

void cleanup_queue(struct QbssState* que) {
  free((*que).element_array); 
}

struct param {
  uint32 warmup_queires;
  uint32 total_queries;
};


struct QbssState qbsss;

void run_enqueue(uint32 warmup_queires ,uint32 total_queries) {
  //printf("enqueue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  int ret;
  uint32 value;
  for(int i = 0; i < warmup_queires; ++i) {
    value = i;
    do {
      ret = enqueue( &qbsss, (uint32)0, (void*) value );
    } while(!ret);
    //printf("Warm-up Enqueued = %d\n", value);
  }
  struct timespec start, stop;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  for(int i = 0; i < total_queries; ++i) {
    value = i;
    do {
      ret = enqueue( &qbsss, (uint32)0, (void*) value );
    } while(!ret);
    //printf("Enqueued = %d\n", value);
  }
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &stop);
  double total_time_in_sec =  (stop.tv_sec - start.tv_sec) + (stop.tv_nsec - start.tv_nsec) / 1e9;
  double tput = (double) total_queries / total_time_in_sec;
  printf("%.f, %.f\n",total_time_in_sec, tput);
  fflush(stdout);
}


void run_dequeue(uint32 warmup_queires ,uint32 total_queries) {
  //printf("dequeue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  uint32 value;
  int ret;
  for(int i = 0; i < warmup_queires; ++i) {
    do {
      ret = dequeue( &qbsss, NULL, (void**) &value );
    } while(!ret);
  }
  for(int i = 0; i < total_queries; ++i) {
      do {
      ret = dequeue( &qbsss, NULL, (void**) &value );
    } while(!ret);
  }
}

void* thread_run_enqueue(void* vargs) {
  struct param* args = (struct param*) vargs;
  run_enqueue(args->warmup_queires, args->total_queries);
}

void* thread_run_dequeue(void* vargs) {
  struct param* args = (struct param*) vargs;
  run_dequeue(args->warmup_queires, args->total_queries);
}



void bench(uint32 number_elements, uint32 warmup_queires ,uint32 total_queries) {
  pthread_t tid1, tid2;
  struct param 
    param;
  param.warmup_queires = warmup_queires;
  param.total_queries = total_queries;
  init_queue( &qbsss, number_elements);
  pthread_create(&tid1, NULL, thread_run_enqueue, &param);
  pthread_create(&tid2, NULL, thread_run_dequeue, &param);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  cleanup_queue(&qbsss);
 }

int main(int argc, char *argv[])
{
  if(argc != 3) {
    printf("Invalid number of args\n");
    return -1;
  }
  uint32 number_elements = (uint32)atoi(argv[1]);
  uint32 number_of_runs = (uint32) atoi(argv[2]);
  uint32 warmup = 5000000;
  uint32 total =  50000000;
  printf("number_elements = %u, warmup_queires = %u, total_queries = %u\n",number_elements,warmup,total);
  printf("total_time(secs), throughput(ops/sec)\n");
  fflush(stdout);
  for(int i = 0; i < number_of_runs; ++i) {
    bench(number_elements, warmup, total);
  }
  return 0;
}