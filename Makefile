# Makefile

all: install

install:
	coqc Cases.v
	coqc Power.v
	coqc ListCalculus.v
	coqc StreamCalculus.v
	coqc DualMoessnersSieve.v
	coqc BinomialCoefficients.v
	coqc PascalsTriangle.v
	coqc CharacteristicFunction.v
	coqc StreamMoessnersSieve.v
	coqc MoessnersTheorem.v
	coqc TriangleGrid.v
	coqc LongsTheorem.v
	coqc Horner.v

docs:
	mkdir -p docs
	coqdoc --no-lib-name --html *.v -d docs/
	cp coqdoc_sf.css docs/coqdoc.css

clean:
	rm *.vo
	rm *.glob
	rm -rf docs/

zip:
	zip code.zip *.v coqdoc_sf.css Makefile

.PHONY: all clean docs install zip
