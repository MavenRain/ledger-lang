.PHONY: build check test

build:
	node bin/build.mjs

check:
	node bin/build.mjs --check

test: build
	node --stack-size=7000 --max-old-space-size=1024 --test test/*.test.mjs
