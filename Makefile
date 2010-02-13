default: dist
	cabal build
configure dist: $(wildcard Setup.hs *.cabal)
	cabal configure
clean:
	cabal $@

.PHONY: clean default configure
