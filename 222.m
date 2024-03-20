/*
Computations accompanying the proof of Theorem 7.7
*/
SetLogFile("222.out");
load "Triples.m";
load "ZeroDimensionalSubschemes.m";
load "TracePoly.m";
load "NontrivialCurves.m";

/*
list of possible values of n, taking into account the bounds of Corollary 7.5
*/
for n in [ 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40, 42, 48, 60, 72, 84, 120, 144 ] do
	"n =", n;
	K<zetan> := CyclotomicField(n);
	R<a,b,c,d> := PolynomialRing(K, 4);
	RR<a0,b0,c0,d0> := PolynomialRing(Rationals(),4);

	BasisK := Basis(K);

	triples := InequivalentTriples(n);
	"Number of triples of roots of unity, up to symmetry equivalence:", #triples;

	for t in triples do
		x := zetan^t[1];
		y := zetan^t[2];
		z := zetan^t[3];

		// Construct the (2)+(2)+(2) equation
		monomials := [x^2 * y^2 * z^2, 1, 
		x^2 * y^2 * z, z,
		x^2 * y * z^2, y,
		x * y^2 * z^2, x,
		x^2 * y^2, z^2,
		x^2 * y*z, y * z,
		x^2 * z^2, y^2,
		x * y^2 * z, x * z,
		x * y * z^2, x * y,
		y^2 * z^2, x^2,
		x^2 * y, y * z^2,
		x^2 * z, y^2 * z,
		x * y^2, x * z^2,
		x * y * z
		];

		coefficients := [ -b*(a-c)*(b-d)*d, -b*(a-c)*(b-d)*d,
		b*(a*b*c + a*b*d - 2*a*c*d - 2*b*c*d + c^2*d + c*d^2), b*(a*b*c + a*b*d - 2*a*c*d - 2*b*c*d + c^2*d + c*d^2),
		d*(a^2*b + a*b^2 - 2*a*b*c - 2*a*b*d + a*c*d + b*c*d), d*(a^2*b + a*b^2 - 2*a*b*c - 2*a*b*d + a*c*d + b*c*d),
		(a - c)*(b - d)*(a*b + c*d), (a - c)*(b - d)*(a*b + c*d),
		-b*(b - c)*c*(a - d), -b*(b - c)*c*(a - d),
		-a^2*b*c - a*b^2*c - a^2*b*d - a*b^2*d + 8*a*b*c*d - a*c^2*d - b*c^2*d - a*c*d^2 - b*c*d^2, -a^2*b*c - a*b^2*c - a^2*b*d - a*b^2*d + 8*a*b*c*d - a*c^2*d - b*c^2*d - a*c*d^2 - b*c*d^2,
		-a*(b - c)*(a - d)*d, -a*(b - c)*(a - d)*d,
		-2 * a^2 * b^2 + a^2 * b * c + a * b^2 * c - 2 * a * b * c^2 + a^2 * b * d + a * b^2 * d + a * c^2 * d + b * c^2 * d - 2 * a * b * d^2 + a * c * d^2 + b * c * d^2 - 2 * c^2 * d^2, -2 * a^2 * b^2 + a^2 * b * c + a * b^2 * c - 2 * a * b * c^2 + a^2 * b * d + a * b^2 * d + a * c^2 * d + b * c^2 * d - 2 * a * b * d^2 + a * c * d^2 + b * c * d^2 - 2 * c^2 * d^2,
		-2*a^2*b^2 + a^2*b*c + a*b^2*c + a^2*b*d + a*b^2*d - 2*a^2*c*d-2*b^2*c*d + a*c^2*d + b*c^2*d + a*c*d^2 + b*c*d^2 - 2*c^2*d^2, -2*a^2*b^2 + a^2*b*c + a*b^2*c + a^2*b*d + a*b^2*d - 2*a^2*c*d-2*b^2*c*d + a*c^2*d + b*c^2*d + a*c*d^2 + b*c*d^2 - 2*c^2*d^2,
		-a*(a - c)*c*(b - d), -a*(a - c)*c*(b - d),
		c*(a^2*b + a*b^2 - 2*a*b*c - 2*a*b*d + a*c*d + b*c*d), c*(a^2*b + a*b^2 - 2*a*b*c - 2*a*b*d + a*c*d + b*c*d),
		a*(a*b*c + a*b*d - 2*a*c*d - 2*b*c*d + c^2*d + c*d^2), a*(a*b*c + a*b*d - 2*a*c*d - 2*b*c*d + c^2*d + c*d^2),
		(b - c)*(a - d)*(a*b + c*d), (b - c)*(a - d)*(a*b + c*d),
		2*(2*a^2*b^2 - a^2*b*c - a*b^2*c + 2*a*b*c^2 - a^2*b*d - a*b^2*d + 2*a^2*c*d - 4*a*b*c*d+2*b^2*c*d - a*c^2*d - b*c^2*d + 2*a*b*d^2 - a*c*d^2 - b*c*d^2 + 2*c^2*d^2)];

		eqn := &+[monomials[i] * coefficients[i] : i in [1..#coefficients]];	// the (2)+(2)+(2) equation

		eqs := [RR!TracePolynomial(eqn*z) : z in BasisK ];			// We consider solutions in rational numbers,
											// so the coefficient of every element in a 
											// Q-basis of K has to vanish. This is equivalent
											// to all the traces vanishing
	
		S := Scheme(ProjectiveSpace(RR), eqs);
		IC := IrreducibleComponents(S);
		IC := [ReducedSubscheme(i) : i in IC];
		IC1 := [ i : i in IC | Dimension(i) eq 1 and IsNontrivial222(Curve(i)) ];		// 1-dimensional components (only keep those with geometric interest)
		IC0 := [ i : i in IC | Dimension(i) eq 0 ];						// 0-dimensional components
	

		HigherGenusCurves := [ Curve(i) : i in IC1 | Genus(Curve(i)) gt 0 ];			// further separate the curves according to their genus
		Genus0Curves := [ Curve(i) : i in IC1 | Genus(Curve(i)) eq 0 ];

		// 0-dimensional components: find rational points
		// and only keep those with geometric meaning
		IsolatedRationalPoints := [RationalPoints222(c) : c in IC0];
		IsolatedRationalPoints := [IP : IP in IsolatedRationalPoints | #IP gt 0 ];
		if #IsolatedRationalPoints gt 0 then
			"The triple", t[1], t[2], t[3], "leads to isolated rational points";
			IsolatedRationalPoints;
		end if;

		// Print the list of the genus-0 curves found
		// and the list of the genera of the other
		// curves
		if #Genus0Curves gt 0 then
			"The triple", t[1], t[2], t[3], "leads to nontrivial genus 0 curves";
			Genus0Curves;
		end if;

		if #HigherGenusCurves gt 0 then
			"The triple", t[1], t[2], t[3], "leads to curves of positive genera given by", [Genus(C) : C in HigherGenusCurves];
		end if;
	end for;
end for;

exit;
