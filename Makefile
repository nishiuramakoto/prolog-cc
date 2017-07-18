BENCH=dist/build/bench/bench
BENCH2=dist/build/bench2/bench2

.PHONY: push set-remote test tests shell bench pl docs coverage

all : build-as-yesod

build-as-yesod:
	cd .. && stack build


set-remote: push
	git remote set-url origin http://aki23b.ddns.net/git/prolog-fd.git

push :
	git remote set-url origin /mnt/debian/var/www/git/prolog-fd.git && \
	git push --all origin

####################################################################


test : bench2

test: bench2

tests:
	(cd specs; runghc -i../src Specs)

shell:
	ghci -isrc -iprolog-graph -outputdir dist/build Prolog GraphViz Quote IsString -XOverloadedStrings -XQuasiQuotes

bench8:
	( cd bench; \
	  ghc -i../src -O --make Bench -main-is Bench -o runbench && \
	  time -p ./runbench 8 \
	)

bench7:
	( cd bench; \
	  ghc -i../src -O --make Bench -main-is Bench -o runbench && \
	  time -p ./runbench 7 \
	)

bench6:
	( cd bench; \
	  ghc -i../src -O --make Bench -main-is Bench -o runbench && \
	  time -p ./runbench 6 \
	)

bench5:
	( cd bench; \
	  ghc -i../src -O --make Bench -main-is Bench -o runbench && \
	  time -p ./runbench 5 \
	)

bench4:
	( cd bench; \
	  ghc -i../src -O --make Bench -main-is Bench -o runbench && \
	  time -p ./runbench 4 \
	)
bench:
	cabal build && time -p $(BENCH) 6

# bench2:
# 	( cabal build &&  time -p $(BENCH2) 8 \
# 	)

bench2:
	cabal build &&  time -p $(BENCH2) bench/queens1.pl

bench2-prof: prof
	( cabal build &&  time -p $(BENCH2) 7 +RTS -p \
	)

prof:
	cabal configure --enable-library-profiling --enable-executable-profiling --ghc-option=-fprof-auto && \
	cabal build

pl:
	ghc -isrc -outputdir dist/build -O --make Console -main-is Console -o $@

docs:
	cabal configure && cabal haddock --hyperlink-source

coverage:
	ghc -fhpc -isrc -outputdir dist/build Specs -main-is Specs -o coverage/runspecs
	cd coverage; ./runspecs ../specs 2>/dev/null >/dev/null
	hpc report coverage/runspecs
	hpc markup coverage/runspecs --destdir=coverage --exclude=Prolog --exclude=Specs
	rm coverage/runspecs*

.PHONY : prof bench2-prof bench bench2 bench4 bench5 bench6 bench7 bench8
