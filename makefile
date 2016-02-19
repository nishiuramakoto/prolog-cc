.PHONY: tests shell bench pl docs coverage

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
bench: bench4

bench2:
	( cd bench; \
	  ghc -i../src -O --make Bench2 -main-is Bench2 -o runbench2 && \
	  time -p ./runbench2 \
	)

bench2-prof:
	( cd bench; \
	  ghc -prof -fprof-auto -rtsopts -i../src  -O --make Bench2 -main-is Bench2 -o runbench2 && \
	  time -p ./runbench2 +RTS -p \
	)


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

.PHONY : bench bench2 bench4 bench5 bench6 bench7 bench8
