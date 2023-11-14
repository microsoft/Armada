#include <stdint.h>
#include <pthread.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
void _main() {
  int* p;
  int arr[10];
  p = (int*) calloc(sizeof(int), 1);
  *p = 2;
  arr[2] = 1;
}


int main() {
  _main();
  pthread_exit(NULL);
}