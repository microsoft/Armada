
DAFNYS=$(wildcard *.arm)
CPPS=$(subst .arm,.c,$(DAFNYS))
EXECS=$(subst .arm,,$(DAFNYS))
DAFNY_DIR=../..
DAFNY=$(DAFNY_DIR)/Binaries/Dafny.exe
DAFNY_RUNTIME_DIR=$(DAFNY_DIR)/Binaries
DAFNY_RUNTIME_CPP=$(DAFNY_RUNTIME_DIR)/DafnyRuntime.h
DAFNY_DEPS=$(DAFNY) $(DAFNY_RUNTIME_DIR)/Dafny.exe $(DAFNY_RUNTIME_DIR)/DafnyPipeline.dll $(DAFNY_RUNTIME_CPP)
TEST_LOG=tests.log
ifeq ($(OS),Windows_NT)
	MONO=""
else 
	MONO="mono"
endif
 CFLAGS += -Wall -Wextra -Wpedantic -I$(DAFNY_RUNTIME_DIR)

.SECONDARY: $(CPPS)

all:$(EXECS)
#all:hello ints

vars:
	echo $(DAFNYS)
	echo $(CPPS)
	echo $(EXECS)

%.c: %.arm $(DAFNY) $(DAFNY_DEPS)
	$(MONO) $(DAFNY) /compile:0 /spillTargetCode:3 /compileTarget:clight extern.h $<

%.cs: %.arm $(DAFNY) $(DAFNY_DEPS)
	$(MONO) $(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cs $<

$(EXECS): % : %.c $(DAFNY_RUNTIME_CPP)
	$(CC) $(CFLAGS) -o $@ $<

test: $(EXECS)
	for e in $(EXECS); do echo; echo "*******************"; echo "Running $$e"; echo "*******************"; echo; ./$$e; done | tee $(TEST_LOG)
#	grep unexpected $(TEST_LOG)
#	if [ $$? -ne 0 ]; then
#	  echo "FAILED A TEST"
#	else
#		echo "SUCCESS!"
#	fi

clean:
	rm -f *.c *.dfy $(EXECS) $(TEST_LOG)
