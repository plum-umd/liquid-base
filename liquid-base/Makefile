LIQUID_EXE?=liquid

verify:
	cd src; $(LIQUID_EXE) Liquid/ProofCombinators.hs && $(LIQUID_EXE) Data/Proxy.hs && $(LIQUID_EXE) Data/List.hs && $(LIQUID_EXE) Data/List/NonEmpty.hs && $(LIQUID_EXE) Data/Semigroup.hs && $(LIQUID_EXE) Data/Functor.hs && $(LIQUID_EXE) Data/Lattice.hs

build:
	stack build
