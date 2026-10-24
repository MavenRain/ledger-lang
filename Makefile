.PHONY: build check test c-build c-check c-test bench certificate-check certificate-test

TCC ?= tcc
C_SOURCES := $(wildcard compiler/*.c)
C_OBJECTS := $(patsubst compiler/%.c,build/c/%.o,$(C_SOURCES))
C_HEADERS := $(wildcard compiler/*.h)
C_SCHEMA := core/schema.def
C_OPS := core/ops.def
C_CERT := core/certificate.def

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

build/ledgerc: $(C_SOURCES) $(C_HEADERS) $(C_SCHEMA) $(C_OPS) $(C_CERT)
	@mkdir -p build
	$(TCC) -Wall -Werror -o $@ $(C_SOURCES) -lpthread

build/c/schema.o: $(C_SCHEMA)
build/c/operations.o: $(C_OPS)
build/c/certificate.o: $(C_SCHEMA) $(C_OPS) $(C_CERT)

build/c/%.o: compiler/%.c $(C_HEADERS)
	@mkdir -p build/c
	$(TCC) -Wall -Werror -c $< -o $@

c-test: build/c-modules-test build/c-output-test
	./build/c-modules-test
	./build/c-output-test

build/c-modules-test: test/c-modules.c test/c-alloc.c $(filter-out compiler/main.c,$(C_SOURCES)) $(C_HEADERS) $(C_SCHEMA) $(C_OPS) $(C_CERT)
	@mkdir -p build
	$(TCC) -Wall -Werror -Dmalloc=ledger_test_malloc -o $@ test/c-modules.c test/c-alloc.c $(filter-out compiler/main.c,$(C_SOURCES))

build/c-output-test: test/c-output.c compiler/main.c compiler/runtime.c compiler/certificate.c compiler/sha256.c $(C_HEADERS) $(C_SCHEMA) $(C_OPS) $(C_CERT)
	@mkdir -p build
	$(TCC) -Wall -Werror -o $@ test/c-output.c compiler/runtime.c compiler/certificate.c compiler/sha256.c -lpthread

build/c-certificate-test: test/c-certificate.c $(filter-out compiler/main.c,$(C_SOURCES)) $(C_HEADERS) $(C_SCHEMA) $(C_OPS) $(C_CERT)
	@mkdir -p build
	$(TCC) -Wall -Werror -o $@ test/c-certificate.c $(filter-out compiler/main.c,$(C_SOURCES))

# certificate-check (M5 design item 10, delta B-1): checks the core module in
# the mechanism-lang kernel under /usr/bin/time -l, after the C certificate
# regressions. A watchdog (ruling Q-M5-38 (a)) reads the ps RSS and the
# footprint of the kernel each 0.1 s and kills it (kill -9) above CERT_LIMIT
# bytes (default 4294967296) on either. It fails on an absent kernel, on a
# refusal, on a kill, and on a max RSS or a peak footprint above 4 GB (ruling
# Q-M5-28). MECH_BIN names the kernel. Then it checks the certificates of
# CERT_PROGRAMS (ruling Q-M5-30 (a)) and of CERT_EXTRA (default empty; delta
# E-1 (f)) in the same way.
CERT_PROGRAMS := examples/crm.ledger test/certificate-small.ledger test/certificate-write1.ledger test/certificate-write3.ledger test/certificate-read-m2.ledger test/certificate-read-m3.ledger test/certificate-read-m4.ledger test/certificate-read-m6a.ledger test/certificate-read-m6b.ledger test/certificate-read-m6c.ledger test/certificate-read-m6d.ledger test/certificate-read-m6e.ledger test/certificate-write-m7a.ledger test/certificate-write-m7b.ledger test/certificate-write-m7b2.ledger test/certificate-write-m7b3.ledger test/certificate-write-m7b4.ledger test/certificate-write-m7b5.ledger test/certificate-write-m7c.ledger test/certificate-write-m7c2.ledger test/certificate-write-m7c2b.ledger test/certificate-write-m7c3.ledger test/certificate-write-m7d.ledger test/certificate-write-m7d2.ledger test/certificate-write-m7d2a.ledger test/certificate-write-m7d4.ledger
CERT_EXTRA ?=
MECH_BIN ?= /Users/oobi/Documents/mechanism-lang/_tcc/bin/mech
CERT_LIMIT ?= 4294967296
# CERT_WATCH: one kernel check of build/cert/NAME.mech (NAME in the shell
# variable name) under the watchdog. An empty ps or footprint read (a
# sandboxed run) counts as 0.
CERT_WATCH = /usr/bin/time -l "$(MECH_BIN)" check build/cert/$$name.mech > build/cert/$$name.out 2> build/cert/$$name.time & \
  tp=$$!; mp=; killed=0; \
  while kill -0 $$tp 2> /dev/null; do \
    test -n "$$mp" || mp=$$(pgrep -P $$tp -x "$$(basename "$(MECH_BIN)")" | head -1); \
    if test -n "$$mp"; then \
      kb=$$(ps -o rss= -p $$mp 2> /dev/null | tr -d ' '); \
      fb=$$(footprint -f bytes --noCategories -p $$mp 2> /dev/null | awk '/phys_footprint: [0-9]/ {sub(/.*phys_footprint: /, ""); print $$1; exit}'); \
      if test $$(( $${kb:-0} * 1024 )) -gt $(CERT_LIMIT) || test "$${fb:-0}" -gt $(CERT_LIMIT); then kill -9 $$mp 2> /dev/null; killed=1; fi; \
    fi; \
    sleep 0.1; \
  done; \
  wait $$tp; rc=$$?; \
  rss=$$(awk '/maximum resident set size/ {print $$1}' build/cert/$$name.time); \
  foot=$$(awk '/peak memory footprint/ {print $$1}' build/cert/$$name.time); \
  echo "cert $$name rc $$rc max RSS $$rss footprint $$foot"; \
  test $$killed -eq 0 || { echo "cert $$name killed above 4 GB"; exit 1; }; \
  test $$rc -eq 0 || { head -1 build/cert/$$name.time; exit 1; }; \
  test "$$rss" -le $(CERT_LIMIT) && test "$$rss" -le 4294967296 || { echo "cert $$name max RSS above 4 GB"; exit 1; }; \
  test "$$foot" -le $(CERT_LIMIT) && test "$$foot" -le 4294967296 || { echo "cert $$name footprint above 4 GB"; exit 1; }
certificate-test: build/c-certificate-test
	@mkdir -p build/cert
	@test -x "$(MECH_BIN)" || { echo "certificate-test: no kernel at $(MECH_BIN)"; exit 1; }
	./build/c-certificate-test "$(MECH_BIN)"

certificate-check: build/ledgerc certificate-test
	@mkdir -p build/cert
	@test -x "$(MECH_BIN)" || { echo "certificate-check: no kernel at $(MECH_BIN)"; exit 1; }
	@echo "kernel $(MECH_BIN) sha256 $$(shasum -a 256 < "$(MECH_BIN)" | cut -c1-16) K HEAD $$(git -C "$$(dirname "$(MECH_BIN)")/../.." log -1 --format=%h)"
	./build/ledgerc --certificate-core > build/cert/core.mech
	@name=core; $(CERT_WATCH)
	@for file in $(CERT_PROGRAMS) $(CERT_EXTRA); do \
	  name=$$(basename $$file .ledger); \
	  ./build/ledgerc --certificate $$file > build/cert/$$name.mech || { echo "cert $$name refused"; exit 1; }; \
	  $(CERT_WATCH); \
	done

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
