// Dafny program queue.arm compiled into ClightTSO
#include "DafnyRuntime.h"
#include "extern.h"
// namespace _8_SharedStructs 
struct BSSQueueElement;
typedef struct BSSQueueElement BSSQueueElement;
struct BSSQueueElement {
  uint64 key;
uint64 value;
};
struct QbssState;
typedef struct QbssState QbssState;
struct QbssState {
  uint64 number_elements;
uint64 mask;
uint64 write_index;
uint64 read_index;
struct BSSQueueElement* element_array;
uint64 array_size;
};
struct BackoffState;
typedef struct BackoffState BackoffState;
struct BackoffState {
  uint64 lock;
uint64 backoff_iteration_frequency_counters[2];uint64 metric;
uint64 total_operations;
};
// namespace _11_QueueBSS__TSObypass 
// Global Variables
struct QbssState queue;
// Param Stucts
struct _params_of_init_queue;
typedef struct _params_of_init_queue _params_of_init_queue;
struct _params_of_init_queue {
  uint64 size;
};
struct _params_of_enqueue;
typedef struct _params_of_enqueue _params_of_enqueue;
struct _params_of_enqueue {
  uint64 k;
uint64 v;
};
struct _params_of_dequeue;
typedef struct _params_of_dequeue _params_of_dequeue;
struct _params_of_dequeue {
  uint64* k;
uint64* v;
};
struct _params_of__main;
typedef struct _params_of__main _params_of__main;
struct _params_of__main {
};
// Method Decls
void init_queue(uint64 size);
void* _thread_of_init_queue (void* vargs);
uint64 enqueue(uint64 k, uint64 v);
void* _thread_of_enqueue (void* vargs);
uint64 dequeue(uint64* k, uint64* v);
void* _thread_of_dequeue (void* vargs);
void _main();
void* _thread_of__main (void* vargs);
// Methods Defns
// Beginning of method init_queue
void init_queue(uint64 size)
{
  (queue).array_size = size;
  (queue).read_index = (uint64)0;
  (queue).write_index = (uint64)0;
  (queue).element_array = (struct BSSQueueElement*) calloc((size_t)((queue).array_size), sizeof(struct BSSQueueElement));
}
void* _thread_of_init_queue (void* vargs) {
  _params_of_init_queue args = *((_params_of_init_queue *) vargs);
init_queue (args.size);
return NULL;
}
// End of method init_queue

// Beginning of method enqueue
uint64 enqueue(uint64 k, uint64 v)
{
  uint64 ret = 0;
  struct BSSQueueElement* _0_e = NULL;
  uint64 _1_read__index = 0;
  uint64 _2_array__size = 0;
  uint64 _3_write__index = 0;
  uint64 _4_modulo = 0;
  uint64 _5_tmp__write__index = 0;
  struct BSSQueueElement* _6_element = NULL;
  struct BSSQueueElement* _7_tmp__array = NULL;
  _3_write__index = (queue).write_index;
after_0: ;
  _5_tmp__write__index = (_3_write__index) + ((uint64)1);
after_1: ;
  _2_array__size = (queue).array_size;
after_2: ;
  _4_modulo = (_5_tmp__write__index) % (_2_array__size);
after_3: ;
  _1_read__index = (queue).read_index;
  if ((_1_read__index) != (_4_modulo)) {
    _3_write__index = (queue).write_index;
  after_5: ;
    _7_tmp__array = (queue).element_array;
    _6_element = ((queue).element_array) + (_3_write__index);
    _0_e = _6_element;
  after_6: ;
    (*(_0_e)).key = k;
  after_7: ;
    (*(_0_e)).value = v;
  after_8: ;
    _3_write__index = (queue).write_index;
    _5_tmp__write__index = (_3_write__index) + ((uint64)1);
    _2_array__size = (queue).array_size;
    _4_modulo = (_5_tmp__write__index) % (_2_array__size);
    (queue).write_index = _4_modulo;
  after_9: ;
    ret = (uint64)1;
return ret;
  }
after_4: ;
  ret = (uint64)0;
return ret;
  return ret;
}
void* _thread_of_enqueue (void* vargs) {
  _params_of_enqueue args = *((_params_of_enqueue *) vargs);
enqueue (args.k,args.v);
return NULL;
}
// End of method enqueue

// Beginning of method dequeue
uint64 dequeue(uint64* k, uint64* v)
{
  uint64 ret = 0;
  struct BSSQueueElement* _8_e = NULL;
  uint64 _9_read__index = 0;
  uint64 _10_array__size = 0;
  uint64 _11_write__index = 0;
  uint64 _12_modulo = 0;
  uint64 _13_tmp__read__index = 0;
  uint64 _14_tmp__int = 0;
  struct BSSQueueElement* _15_tmp__array = NULL;
  struct BSSQueueElement* _16_element = NULL;
  _9_read__index = (queue).read_index;
after_10: ;
  _11_write__index = (queue).write_index;
  if ((_9_read__index) != (_11_write__index)) {
    _9_read__index = (queue).read_index;
  after_12: ;
    _15_tmp__array = (queue).element_array;
    _16_element = (_15_tmp__array) + (_9_read__index);
    _8_e = _16_element;
    if ((k) != (NULL)) {
      _14_tmp__int = (*(_8_e)).key;
      *k = _14_tmp__int;
    }
    if ((v) != (NULL)) {
      _14_tmp__int = (*(_8_e)).value;
      *v = _14_tmp__int;
    }
    _9_read__index = (queue).read_index;
    _13_tmp__read__index = (_9_read__index) + ((uint64)1);
  after_13: ;
    _10_array__size = (queue).array_size;
  after_14: ;
    _12_modulo = (_13_tmp__read__index) % (_10_array__size);
  after_15: ;
    (queue).read_index = _12_modulo;
  after_16: ;
    ret = (uint64)1;
return ret;
  }
after_11: ;
  ret = (uint64)0;
return ret;
  return ret;
}
void* _thread_of_dequeue (void* vargs) {
  _params_of_dequeue args = *((_params_of_dequeue *) vargs);
dequeue (args.k,args.v);
return NULL;
}
// End of method dequeue

// Beginning of method _main
void _main()
{
  uint64 _17_tid1;
  _17_tid1 = (uint64)0;
  uint64 _18_tid2;
  _18_tid2 = (uint64)0;
  uint64* _19_k;
  _19_k = NULL;
  uint64* _20_v;
  _20_v = NULL;
  _19_k = (uint64*) calloc((size_t)1, sizeof(uint64));
  _20_v = (uint64*) calloc((size_t)1, sizeof(uint64));
  (queue).array_size = (uint64)4;
after_17: ;
  (queue).read_index = (uint64)0;
after_18: ;
  (queue).write_index = (uint64)0;
after_19: ;
  (queue).element_array = (struct BSSQueueElement*) calloc((size_t)((queue).array_size), sizeof(struct BSSQueueElement));
  // Marked as Ghost
if (((((queue).element_array) != (NULL)) && ((_19_k) != (NULL))) && ((_20_v) != (NULL))) {
  }
}
void* _thread_of__main (void* vargs) {
  _params_of__main args = *((_params_of__main *) vargs);
_main ();
return NULL;
}
////////////////////////////////////////////////////////////////////////////////
// Beginning of benchmark code
////////////////////////////////////////////////////////////////////////////////

void cleanup_queue(struct QbssState* que) {
  free((*que).element_array); 
}

struct param {
  uint64 warmup_queires;
  uint64 total_queries;
};


struct QbssState qbsss;

void run_enqueue(uint64 warmup_queires ,uint64 total_queries) {
  //printf("enqueue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  int ret;
  uint64 value;
  for(int i = 0; i < warmup_queires; ++i) {
    value = i;
    do {
      ret = enqueue(0, value);
    } while(!ret);
    //printf("Warm-up Enqueued = %d\n", value);
  }
  struct timespec start, stop;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  for(int i = 0; i < total_queries; ++i) {
    value = i;
    do {
      ret = enqueue((uint64)0, value );
    } while(!ret);
    //printf("Enqueued = %d\n", value);
  }
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &stop);
  double total_time_in_sec =  (stop.tv_sec - start.tv_sec) + (stop.tv_nsec - start.tv_nsec) / 1e9;
  double tput = (double) total_queries / total_time_in_sec;
  printf("%.f, %.f\n",total_time_in_sec, tput);
  fflush(stdout);
}


void run_dequeue(uint64 warmup_queires ,uint64 total_queries) {
  //printf("dequeue warmup_queires = %u total_queries = %u\n",warmup_queires,total_queries);
  uint64 value;
  int ret;
  for(int i = 0; i < warmup_queires; ++i) {
    do {
      ret = dequeue(NULL, &value );
    } while(!ret);
  }
  for(int i = 0; i < total_queries; ++i) {
      do {
      ret = dequeue(NULL, &value );
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



void bench(uint64 number_elements, uint64 warmup_queires ,uint64 total_queries) {
  pthread_t tid1, tid2;
  struct param 
    param;
  param.warmup_queires = warmup_queires;
  param.total_queries = total_queries;
  init_queue(number_elements);
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
  uint64 number_elements = (uint64)atoi(argv[1]);
  uint64 number_of_runs = (uint64) atoi(argv[2]);
  uint64 warmup = 5000000;
  uint64 total =  50000000;
  printf("number_elements = %u, warmup_queires = %u, total_queries = %u\n",number_elements,warmup,total);
  printf("total_time(secs), throughput(ops/sec)\n");
  fflush(stdout);
  for(int i = 0; i < number_of_runs; ++i) {
    bench(number_elements, warmup, total);
  }
  return 0;
}
