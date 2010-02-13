default: dist
	cabal build
configure dist: $(wildcard Setup.hs *.cabal)
	cabal configure

.PHONY: default configure
