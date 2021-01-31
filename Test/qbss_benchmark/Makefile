ARMADA_ROOT := ../../
C_FLAGS_RELEASE := -O2 -DNDEBUG
C_FLAGS := $(C_FLAGS_RELEASE)

CC := gcc $(C_FLAGS)

queue.c: queue.arm queue.patch
	mono $(ARMADA_ROOT)/Binaries/Armada.exe /armadaPath:$(ARMADA_ROOT) queue.arm /compileTarget:clight /spillTargetCode:3
	patch queue.c queue.patch

queue.o: queue.c
	$(CC) queue.c -I$(ARMADA_ROOT)/Binaries/ -lpthread -c -o queue.o -Iliblfds711_modulo/inc/

.PHONY: liblfds_modulo

liblfds_modulo:
	$(MAKE) --directory=liblfds711_modulo/build/gcc_gnumake/ ar_rel

liblfds:
	$(MAKE) --directory=liblfds711/build/gcc_gnumake/ ar_rel

benchmark_lfds_modulo: liblfds_modulo
	$(CC) benchmark_lfds.c -o benchmark_lfds_modulo -Iliblfds711_modulo/inc/ -lpthread -Lliblfds711_modulo/bin -llfds711

benchmark_lfds: liblfds
	$(CC) benchmark_lfds.c -o benchmark_lfds -Iliblfds711/inc/ -lpthread -Lliblfds711/bin -llfds711

benchmark: benchmark.c queue.o
	$(CC) benchmark.c queue.o -o benchmark -I$(ARMADA_ROOT)/Binaries/ -lpthread 

.PHONY: all
all: benchmark benchmark_lfds benchmark_lfds_modulo

.PHONY: clean
clean:
	rm -f benchmark queue.o queue.c benchmark_lfds benchmark_lfds_modulo
