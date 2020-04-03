ARMADA_ROOT := ../../
C_FLAGS_RELEASE := -O2 -DNDEBUG
C_FLAGS := $(C_FLAGS_RELEASE)

CC := gcc $(C_FLAGS)
CCOMP := /armada/compcert/ccomp -stdlib /armada/compcert -I/armada/armada/Binaries -lpthread

queue.c: queue.arm
	mono $(ARMADA_ROOT)/Binaries/Armada.exe /armadaPath:$(ARMADA_ROOT) queue.arm /compileTarget:clight /spillTargetCode:3

queue_ccomp.c: queue.c queue_ccomp.patch
	patch queue.c queue_ccomp.patch -o queue_ccomp.c

queue_gcc.c: queue.c queue_gcc.patch
	patch queue.c queue_gcc.patch -o queue_gcc.c

queue_gcc.o: queue_gcc.c
	$(CC) queue_gcc.c -I$(ARMADA_ROOT)/Binaries/ -lpthread -c -o queue_gcc.o -Iliblfds711_modulo/inc/

queue_ccomp.o: queue_ccomp.c
	$(CCOMP) -c queue_ccomp.c

.PHONY: liblfds_modulo

liblfds_modulo:
	$(MAKE) --directory=liblfds711_modulo/build/gcc_gnumake/ ar_rel

liblfds:
	$(MAKE) --directory=liblfds711/build/gcc_gnumake/ ar_rel

benchmark_lfds_modulo: liblfds_modulo
	$(CC) benchmark_lfds.c -o benchmark_lfds_modulo -Iliblfds711_modulo/inc/ -lpthread -Lliblfds711_modulo/bin -llfds711

benchmark_lfds: liblfds
	$(CC) benchmark_lfds.c -o benchmark_lfds -Iliblfds711/inc/ -lpthread -Lliblfds711/bin -llfds711

benchmark_gcc: benchmark.c queue_gcc.o
	$(CC) benchmark.c queue_gcc.o -o benchmark_gcc -I$(ARMADA_ROOT)/Binaries/ -lpthread 

benchmark_ccomp: benchmark.c queue_ccomp.o
	$(CCOMP) benchmark.c queue_ccomp.o -o benchmark_ccomp

.PHONY: all
all: benchmark_ccomp benchmark_gcc benchmark_lfds benchmark_lfds_modulo

.PHONY: clean
clean:
	rm -f benchmark queue_gcc.o queue_ccomp.o queue.c queue_gcc.c queue_ccomp.c benchmark_lfds benchmark_lfds_modulo
