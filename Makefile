default: dist
	cabal build
configure dist: $(wildcard Setup.hs *.cabal)
	cabal configure -ftest
clean:
	cabal $@

.PHONY: clean default configure
