.PHONY: build check test c-build c-check c-test bench

TCC ?= tcc
C_SOURCES := $(wildcard compiler/*.c)
C_OBJECTS := $(patsubst compiler/%.c,build/c/%.o,$(C_SOURCES))
C_HEADERS := $(wildcard compiler/*.h)
C_SCHEMA := core/schema.def
C_OPS := core/ops.def

build: build/ledgerc

check: c-check

test: build build/bench-gen
	node --test test/*.test.mjs

c-check:
	@mkdir -p build
	@for source in $(C_SOURCES); do $(TCC) -Wall -Werror -c $$source -o build/c-check.o || exit 1; done
	@rm -f build/c-check.o
	@echo 'c check passed'

# c-build compiles each module and links the compiler executable build/ledgerc.
c-build: $(C_OBJECTS) build/ledgerc

build/ledgerc: $(C_SOURCES) $(C_HEADERS) $(C_SCHEMA) $(C_OPS)
	@mkdir -p build
	$(TCC) -Wall -Werror -o $@ $(C_SOURCES) -lpthread

build/c/schema.o: $(C_SCHEMA)
build/c/operations.o: $(C_OPS)

build/c/%.o: compiler/%.c $(C_HEADERS)
	@mkdir -p build/c
	$(TCC) -Wall -Werror -c $< -o $@

c-test: build/c-modules-test build/c-output-test
	./build/c-modules-test
	./build/c-output-test

build/c-modules-test: test/c-modules.c test/c-alloc.c $(filter-out compiler/main.c,$(C_SOURCES)) $(C_HEADERS) $(C_SCHEMA) $(C_OPS)
	@mkdir -p build
	$(TCC) -Wall -Werror -Dmalloc=ledger_test_malloc -o $@ test/c-modules.c test/c-alloc.c $(filter-out compiler/main.c,$(C_SOURCES))

build/c-output-test: test/c-output.c compiler/main.c compiler/runtime.c $(C_HEADERS)
	@mkdir -p build
	$(TCC) -Wall -Werror -o $@ test/c-output.c compiler/runtime.c -lpthread

build/bench-gen: test/bench-gen.c
	@mkdir -p build
	$(TCC) -Wall -Werror -o $@ test/bench-gen.c

# bench (M5 part A, design item 1): N, the exit code, the seconds and the max
# RSS (bytes) of build/ledgerc on a bench log of N entries.
bench: build/ledgerc build/bench-gen
	@mkdir -p build/bench
	@for n in 1000 4000 16000; do \
	  ./build/bench-gen $$n > build/bench/log-$$n.ledger || exit 1; \
	  /usr/bin/time -l ./build/ledgerc build/bench/log-$$n.ledger > build/bench/log-$$n.json 2> build/bench/log-$$n.time; \
	  rc=$$?; \
	  awk -v n=$$n -v rc=$$rc '/ real / {s = $$1} /maximum resident set size/ {r = $$1} \
	    END {print "N " n " rc " rc " seconds " s " max RSS " r}' build/bench/log-$$n.time; \
	done
