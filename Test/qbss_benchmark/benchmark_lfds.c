// this file contains the benchmark for liblfds implementation of bounded_singleproducer_singleconsumer queue.

// you need to first build and install liblfds:
// 0. download the liblfds7.1.1 repo: git clone https://github.com/liblfds/liblfds7.1.1.git
// 1. go to liblfds7.1.1/liblfds711/build/gcc_gnumake
// 2. run "sudo make so_uninstall" to clean up the env.
// 3. run "make clean" to clean up the cache.
// 4. run "make so_rel" to build with release flag (-o2), or "make so_vanilla" to build with no flag.
// 5. run "sudo make so_install" to install the lib. 


// to setput the following configs:
// 1. liblfds with bitmask: build the original lib with "so_vanilla".
// 2. liblfds with bitmask (-o2): build the original lib with "so_rel"
// 3. liblfds with modulo: 
//     (1). modify line 31 of the file liblfds7.1.1/liblfds711/src/lfds711_queue_bounded_singleproducer_singleconsumer/lfds711_queue_bounded_singleproducer_singleconsumer_enqueue.c:
//        "qbsss->write_index = (qbsss->write_index + 1) & qbsss->mask;" -> "qbsss->write_index = (qbsss->write_index + 1) % qbsss->number_elements;"
//     (2). modify line 32 of the file liblfds7.1.1/liblfds711/src/lfds711_queue_bounded_singleproducer_singleconsumer/lfds711_queue_bounded_singleproducer_singleconsumer_dequeue.c:
//        "qbsss->read_index = (qbsss->read_index + 1) & qbsss->mask;" -> "qbsss->read_index = (qbsss->read_index + 1) % qbsss->number_elements;"
//     (3). build and install with flag "so_vanilla".
// 4. liblfds with modulo (-o2):
//      (1) : same as "liblfds with modulo"
//      (2) : same as "liblfds with modulo"
//      (3) : build and install with flag "so_rel"


// to compile the benchmark:
// without -o2:
// gcc -fno-strict-aliasing -llfds711 -lpthread -o bench_lfds bench_lfds.c
// with -o2:
// gcc -fno-strict-aliasing -o2 -dndebug  -llfds711 -lpthread -o bench_lfds bench_lfds.c

// to run the benchmark:
// ./bench_lfds number_elements number_of_runs | tee log_{number_elements}_{number_of_runs}.txt
// number_elements is the size of the queue, it has to be 2^n, n > 0;
// number_of_runs is the number of runs we want to exec.

// the program will print total_time(secs) and throughput(ops/sec) for each run to stdout
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

struct lfds711_queue_bss_state 
  qbsss;


void run_enqueue(uint32 warmup_queires ,uint32 total_queries) {
  //printf("enqueue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  int ret;
  uint32 value;
  for(int i = 0; i < warmup_queires; ++i) {
    value = i;
    do {
      ret = lfds711_queue_bss_enqueue( &qbsss, NULL, (void*)&value );
    } while(!ret);
    //printf("warm-up enqueued = %d\n", value);
  }
  struct timespec start, stop;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  for(int i = 0; i < total_queries; ++i) {
    value = i;
    do {
      ret = lfds711_queue_bss_enqueue( &qbsss, NULL, (void*)&value );
    } while(!ret);
    //printf("enqueued = %d\n", value);
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
      ret = lfds711_queue_bss_dequeue( &qbsss, NULL, (void**) &value );
    } while(!ret);
  }
  for(int i = 0; i < total_queries; ++i) {
      do {
        ret = lfds711_queue_bss_dequeue( &qbsss, NULL, (void**) &value );
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
  struct lfds711_queue_bss_element* 
    qbsse = calloc(number_elements, sizeof(struct lfds711_queue_bss_element));
  pthread_t tid1, tid2;
  struct param 
    param;
  param.warmup_queires = warmup_queires;
  param.total_queries = total_queries;

  lfds711_queue_bss_init_valid_on_current_logical_core( &qbsss, qbsse, number_elements, NULL);
  pthread_create(&tid1, NULL, thread_run_enqueue, &param);
  pthread_create(&tid2, NULL, thread_run_dequeue, &param);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  lfds711_queue_bss_cleanup( &qbsss, NULL );
 }

int main(int argc, char *argv[])
{
  if(argc != 3) {
    printf("invalid number of args\n");
    return -1;
  }
  uint32 number_elements = (uint32)atoi(argv[1]);
  uint32 number_of_runs = (uint32) atoi(argv[2]);
  uint32 warmup = 5000000;
  uint32 total =  50000000;
  printf("total_time(secs), throughput(ops/sec)\n");
  fflush(stdout);
  for(int i = 0; i < number_of_runs; ++i) {
    bench(number_elements, warmup, total);
  }
  return 0;
}
