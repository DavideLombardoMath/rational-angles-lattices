# rational-angles-lattices
Code and data accompanying the paper "Classification of rational angles in plane lattices II"
by R. Dvornicich, D. Lombardo, F. Veneziano, U. Zannier

File					Description
-----------------------------------------------------------------------------------------------------------------------
Reduce bounds/RuleOutDivisors-222.m			Computational proof of Proposition 7.4
Reduce bounds/RuleOutDivisors-32.m			Computational proof of Proposition 5.4
Subsums/EstimateSubsums.m								Computational verification of Propositions 5.2, 6.1, and 7.1.
222.m																		Computations used in the classification of spaces having at least three rational angles
32.m																		Computations used in the classification of spaces having a rational triple (but no rational quadruple)
abcd.m																	Computations used in the classification of spaces with ab=cd
CurvesGenus0.m													Provides a method to determine whether a (possibly singular) genus-0 curve C/Q has infinitely many rational points.
CurvesGenus1.m													Provides a method to determine Y(Q) when Y/Q is a smooth curve of genus 1 with at least one and at most finitely many rational points
CurvesGenus2.m													Provides methods to (try to) determine the set of rational points C(Q) when C has genus 2
CurvesGenus3.m													Provides methods to (try to) determine the set of rational points C(Q) when C has genus 3
Degree.m													      Bounds the degree of Q(x,y,z) over its subfields Q(x,y), Q(x,z), and Q(y,z)
LatticeCollisions.m											For each of the rational families considered in the paper, checks that the only "collisions" happen between complex conjugate lattices
Lattices.m													    Helper functions to study lattices (test for homothety, list rational angles, compute tau from (a,b,c,d,x,y,z))
NontrivialCurves.m											Given a curve in P_3(a,b,c,d), determine whether (at least some of) its rational points are geometrically meaningful for the problem at hand
RationalFamilies.m											Provides parametrisations for the 5 rational families studied in the paper and generates equations for the presence of an additional rational angle in a lattice belonging to one of these families
SeveralDifferentAmplitudes.m						Determines which members of the rational families of spaces considered in the paper have angles of many different amplitudes
TabulateAdditionalAngles.m							Generates the tables describing additional rational angles in the five rational families considered in the paper
TracePoly.m													    Given a polynomial p with coefficients in a number field K, returns the polynomial over Q whose coefficients are the traces of the coefficients of p
Triples.m													      Helper functions to generate one representative for each symmetry-equivalence class of triples of roots of unity
ZeroDimensionalSubschemes.m							Methods to compute rational points on zero-dimensional subschemes of P_3(a,b,c,d) and discard those without geometric meaning
