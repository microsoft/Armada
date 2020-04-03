// This file contains the benchmark for aramda implementation of bounded_singleproducer_singleconsumer queue.

// To compile the benchmark:
// Without -O2:
// gcc -fno-strict-aliasing -llfds711 -lpthread -o bench_armada_gcc bench_armada_gcc.c
// With -O2:
// gcc -fno-strict-aliasing -O2 -DNDEBUG  -llfds711 -lpthread -o bench_armada_gcc bench_armada_gcc.c

// To run the benchmark:
// ./bench_armada_gcc number_elements number_of_runs | tee log_{number_elements}_{number_of_runs}.txt
// number_elements is the size of the queue, it has to be 2^n, n > 0;
// number_of_runs is the number of runs we want to exec.

// The program will print total_time(secs) and throughput(ops/sec) for each run to stdout
// and tee will log the reults to the file.

#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <stdlib.h> 
#include <time.h>
#include "liblfds711.h"

typedef unsigned long      uint32;

struct param {
  uint32 warmup_queires;
  uint32 total_queries;
};

struct armada_QbssState 
  qbsss;


void run_enqueue(uint32 warmup_queires ,uint32 total_queries) {
  //printf("enqueue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  int ret;
  uint32 value;
  for(int i = 0; i < warmup_queires; ++i) {
    value = i;
    do {
      ret = armada_enqueue( &qbsss, 0, value );
    } while(!ret);
    //printf("Warm-up Enqueued = %d\n", value);
  }
  struct timespec start, stop;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  for(int i = 0; i < total_queries; ++i) {
    value = i;
    do {
      ret = armada_enqueue( &qbsss, 0, value );
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
      ret = armada_dequeue( &qbsss, NULL, (void**) &value );
    } while(!ret);
  }
  for(int i = 0; i < total_queries; ++i) {
      do {
      ret = armada_dequeue( &qbsss, NULL, (void**) &value );
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
  struct armada_BSSQueueElement* 
    qbsse = calloc(number_elements, sizeof(struct armada_BSSQueueElement));
  pthread_t tid1, tid2;
  struct param 
    param;
  param.warmup_queires = warmup_queires;
  param.total_queries = total_queries;

  armada_init_queue( &qbsss, qbsse, number_elements, NULL );
  pthread_create(&tid1, NULL, thread_run_enqueue, &param);
  pthread_create(&tid2, NULL, thread_run_dequeue, &param);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
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