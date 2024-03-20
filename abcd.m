/*
Computations accompanying the proof of Theorem 6.3
*/

SetLogFile("abcd.out");
load "Triples.m";
load "ZeroDimensionalSubschemes.m";
load "TracePoly.m";
load "NontrivialCurves.m";
load "CurvesGenus0.m";
load "Lattices.m";

for n in [ i : i in [2..42] | i in Divisors(30) or i in Divisors(42) or i in Divisors(18) or i in Divisors(24) ] do
	"n =", n;
	// Initialisation: the cyclotomic field K=Q(zeta_n),
	// the polynomial ring in 4 variables over K,
	// and the polynomial ring in 4 variables over Q
	K<zetan> := CyclotomicField(n);
	R<a,b,c,d> := PolynomialRing(K, 4);
	RR<a0,b0,c0,d0> := PolynomialRing(Rationals(),4);
	BasisK := Basis(K);

	// Compute a full list of triples [e1, e2, e3]
	// where x=zeta_n^{e_1}, y=zeta_n^{e_2},
	// z=zeta_n^{e_3} up to symmetry equivalence
	triples := InequivalentTriples(n);
	"Inequivalent triples", #triples;

	for t in triples do	// for each choice of (x,y,z) do
		x := zetan^t[1];
		y := zetan^t[2];
		z := zetan^t[3];

		// construct the equation for the case ab=cd
		eqn := a*x*z - a*x - a*y*z + a*y - b*x*y*z + b*x*y + b*z - b - c*x*y + c*x + c*y*z - c*z + d*x*y*z - d*x*z - d*y + d;

		// construct the corresponding variety over the rationals
		// also adding the equation ab-cd = 0
		eqs := [RR!TracePolynomial(eqn*z) : z in BasisK ];
		S := Scheme(ProjectiveSpace(RR), eqs cat [a0*b0-c0*d0]);

		IC := IrreducibleComponents(S);
		IC := [ReducedSubscheme(i) : i in IC];

		// Separate the irreducible components of S
		// according to their dimension.
		// The equation eqn cuts out a surface
		// so every component has dimension at most 2
		IC2 := [ i : i in IC | Dimension(i) eq 2 ];
		IC1 := [ i : i in IC | Dimension(i) eq 1 ];
		IC0 := [ i : i in IC | Dimension(i) eq 0 ];

		if #IC2 ge 1 then
			"For the triple", t[1], t[2], t[3], "the scheme S is a surface";
			IC2;
		end if;

		// Further separate the 1-dimensional components
		// according to their genus, and only keep those
		// that make geometric sense (this is achieved
		// by a call to IsabcdNontrivial)
		IC1 := [ i : i in IC1 | IsNontrivialabcd(i) ];
		HigherGenusCurves := [ Curve(i) : i in IC1 | Genus(Curve(i)) gt 0 ];
		Genus0Curves := [ Curve(i) : i in IC1 | Genus(Curve(i)) eq 0 ];

		// Print output. For the 0-dimensional components
		// we find their rational points (if any), discard
		// those without geometric significance, and
		// obtain the corresponding lattices.
		IsolatedRationalPoints := [RationalPointsabcd(c) : c in IC0];
		IsolatedRationalPoints := [IP : IP in IsolatedRationalPoints | #IP gt 0 ];
		if #IsolatedRationalPoints gt 0 then
			"The triple", t[1], t[2], t[3], "leads to isolated rational points";
			IsolatedRationalPoints;
			"Description of the corresponding lattices:";
			for RatPtComp in IsolatedRationalPoints do
				for RatPt in RatPtComp do
					GeometricLattices := DescribeGeometricRealisations(RatPt[1], RatPt[2], RatPt[3], RatPt[4], x,y,z);
					"The solution", [* RatPt[1],RatPt[2],RatPt[3],RatPt[4], x,y,z *], "corresponds to", #GeometricLattices, "homothety classes of lattices.";
					for lat in GeometricLattices do
						"Angles in lattice";
						AllAffineAnglesInGivenLattice( lat[1] : rootx := lat[2] );
					end for;
				end for;
			end for;
		end if;


		if #Genus0Curves gt 0 then
			"The triple", t[1], t[2], t[3], "leads to nontrivial genus 0 curves";
			Genus0Curves;
		end if;

		if #HigherGenusCurves gt 0 then
			"The triple", t[1], t[2], t[3], "leads to curve(s) of positive genus";
			"Curves:", HigherGenusCurves;
			"Genera:", [Genus(C) : C in HigherGenusCurves];
		end if;

	end for;
end for;

exit;
