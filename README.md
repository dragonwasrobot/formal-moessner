# A Formal Study of Moessner's Sieve

Final monograph also available at: http://ebooks.au.dk/index.php/aul/catalog/book/213

## Installation

0. Download the 3rd party library paco, located at:
   http://plv.mpi-sws.org/paco/paco-1.2.7.zip
   More info about the project can be found at:
	 http://plv.mpi-sws.org/paco/
1. Unzip the paco project and run 'make install' in the 'src' folder of the
   project. This will install 'paco' in the Coq installation directory such that
   it can be 'Required' like any other standard library module.
2. Now run 'make install' in the 'src' folder of the Moessner project in order
   to compile all Coq scripts.
3. The code base of the Moessner project is now ready to be explored and stepped
   through.

## Project structure

Below we list the Coq scripts which accompany each of the different chapters.

Chapter 4 (lists and streams):
- ListCalculus.v
- StreamCalculus.v

Chapter 5 (A dual to Moessner's sieve):
- DualMoessnersSieve.v
- StreamMoessnersSieve.v

Chapter 6 (Pascals' triangle and the binomial coefficient):
- BinomialCoefficients.v
- PascalsTriangle.v

Chapter 7 (A characteristic function of Moessner's sieve):
- CharacteristicFunction.v

Chapter 8 (Proving Moessner's theorem):
- MoessnersTheorem.v

Chapter 9 (A grid of triangles):
- TriangleGrid.v

Chapter 10 (Proving Long's theorem):
- LongsTheorem.v

Chapter 11 (Deriving Moessner's sieve from Horner's method):
- Horner.v

Misc:
- Cases.v
- Power.v
