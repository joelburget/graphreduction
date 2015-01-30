.PHONY: build

profile:
	./dist/build/main/main +RTS -hd || hp2ps main.hp

build:
	cabal configure --enable-executable-profiling
	cabal build
