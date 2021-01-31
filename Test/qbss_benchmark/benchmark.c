#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <stdlib.h> 
#include <time.h>

#include "DafnyRuntime.h"

// Definitions for Armada datatypes
struct BSSQueueElement;
typedef struct BSSQueueElement BSSQueueElement;
struct BSSQueueElement {
  uint64 key;
  uint64 value;
};

struct QbssState;
typedef struct QbssState QbssState;
struct QbssState {
volatile uint64 number_elements;
volatile uint64 mask;
volatile uint64 write_index;
volatile uint64 read_index;
volatile struct BSSQueueElement* element_array;
};

// Method Decls
void init_queue(struct QbssState* qbss, uint64 size);
void* _thread_of_init_queue (void* vargs);
uint64 enqueue(struct QbssState* qbss, uint64 k, uint64 v);
void* _thread_of_enqueue (void* vargs);
uint64 dequeue(struct QbssState* qbss, uint64* k, uint64* v);
void* _thread_of_dequeue (void* vargs);

// Beginning of Bench code

void cleanup_queue(struct QbssState* que) {
  free((*que).element_array); 
}

struct param {
  uint64 warmup_queires;
  uint64 total_queries;
};

struct QbssState qbss;
void run_enqueue_armada(uint32 warmup_queires ,uint32 total_queries) {
  //printf("enqueue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  int ret;
  uint32 value;
  for(uint32 i = 0; i < warmup_queires; ++i) {
    value = i;
    do {
      ret = enqueue(&qbss, (uint64)0, (uint64)value);
    } while(!ret);
  }
  struct timespec start, stop;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  for(int i = 0; i < total_queries; ++i) {
    value = i;
    do {
      ret = enqueue(&qbss, (uint64)0, (void*)value );
    } while(!ret);
  }
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &stop);
  double total_time_in_sec =  (stop.tv_sec - start.tv_sec) + (stop.tv_nsec - start.tv_nsec) / 1e9f;
  double tput = (double) total_queries / total_time_in_sec;
  printf("%.f, %.f\n",total_time_in_sec, tput);
  fflush(stdout);
}

void run_dequeue_armada(uint32 warmup_queires ,uint32 total_queries) {
  uint32 value;
  int ret;
  for(uint32 i = 0; i < warmup_queires; ++i) {
    do {
      ret = dequeue(&qbss, NULL, (void*) &value );
    } while(!ret);
  }
  for(uint32 i = 0; i < total_queries; ++i) {
      do {
        ret = dequeue(&qbss, NULL, (void*) &value );
    } while(!ret);
  }
}

void* thread_run_enqueue_armada(void* vargs) {
  struct param* args = (struct param*) vargs;
  run_enqueue_armada(args->warmup_queires, args->total_queries);
}

void* thread_run_dequeue_armada(void* vargs) {
  struct param* args = (struct param*) vargs;
  run_dequeue_armada(args->warmup_queires, args->total_queries);
}

void bench(uint64 number_elements, uint64 warmup_queires, uint64 total_queries) {
  pthread_t tid1, tid2;
  struct param 
    param;
  param.warmup_queires = warmup_queires;
  param.total_queries = total_queries;
  init_queue(&qbss, number_elements);
  pthread_create(&tid1, NULL, thread_run_enqueue_armada, &param);
  pthread_create(&tid2, NULL, thread_run_dequeue_armada, &param);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  cleanup_queue(&qbss);
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
  // printf("number_elements = %u, warmup_queires = %u, total_queries = %u\n",number_elements,warmup,total);
  printf("total_time(secs), throughput(ops/sec)\n");
  fflush(stdout);
  for(int i = 0; i < number_of_runs; ++i) {
    bench(number_elements, warmup, total);
  }
  return 0;
}
