/*
Computational proof of Proposition 5.4
*/

SetLogFile("RuleOutDivisors-32.out");
load "../TracePoly.m";

for n in [3^3, 5^2, 7^2, 7, 11, 13, 3^2*5, 3*5] do
	"n =", n;

	// Construct the 7-dimensional
	// affine space over K = Q(\zeta_n)
	// and over Q
	// The variable u is auxiliary, and used
	// to impose that certain elements are invertible
	// through equations of the form f*u=1,
	// where f is the function whose vanishing
	// locus we want to avoid
	K<zetan> := CyclotomicField(n);
	R<a,b,c,xp,yp,zp,u> := PolynomialRing(K, 7);
	RR<a0,b0,c0,xp0,yp0,zp0,u0> := PolynomialRing(Rationals(),7);
	BasisK := Basis(K);

	// List triples up to Galois equivalence
	// and z --> 1/z
	triples := CartesianProduct( [ Divisors(n), [0..(n-1)], [0..Floor(n/2)] ] );
	
	// Loop over triples
	for t in triples do
		if GCD([n,t[1], t[2], t[3]]) eq 1 then		// this condition ensures that the common order of x,y,z is a multiple of n

			x := zetan^t[1]*xp;			// write each root of unity as the product of a root of unity of order
			y := zetan^t[2]*yp;			// dividing n, zetan^t[i], and a root of unity of order prime to n,
			z := zetan^t[3]*zp;			// called xp, yp, zp

			monomials := [
			    x^2*y*z,
			    x^2*y,
			    x^2*z,
			    x^2,
			    x*y^2*z,
			    x*y^2,
			    x*y*z,
			    x*y,
			    x*z,
			    x,
			    y^2*z,
			    y^2,
			    y*z,
			    y
			];

			coefficients := [
			    a*c,
			    -a*b,
			    -a*c + b*c,
			    a*b - b*c,
			    a^2 - a*c,
			    -a^2 + a*b,
			    -2*a^2 + a*b + a*c - 2*b*c,
			    2*a^2 - a*b - a*c + 2*b*c,
			    a^2 - a*b,
			    -a^2 + a*c,
			    -a*b + b*c,
			    a*c - b*c,
			    a*b,
			    -a*c
			];

			eqn := &+[monomials[i] * coefficients[i] : i in [1..#coefficients]];	// One of the equations of V_{\xi_1, \xi_2, \xi_3}.
			eqs := [RR!TracePolynomial(eqn*z) : z in BasisK ];			// Taking the trace down to Q of the various eqn*z
												// is equivalent to intersecting its conjugates,
												// so that the polynomials in eqs define V_{\xi_1, \xi_2, \xi_3, Q}

			// Construct the set of invertible elements described in the statement of the proposition
			invertible := [ u0, a0, b0, c0, a0-b0, b0-c0, c0-a0, xp0, yp0, zp0 ];
			if t[1] eq t[2] then
				Append(~invertible, xp0-yp0);
			end if;
			if t[1] eq n then
				Append(~invertible, xp0-1);
			end if;
			if t[2] eq 0 then
				Append(~invertible, yp0-1);
			end if;
			if t[3] eq 0 then
				Append(~invertible, zp0-1);
			end if;

			S := Scheme(AffineSpace(RR), eqs cat [&*invertible-1]);	// the intersection of V_{\xi_1, \xi_2, \xi_3, Q} with 
										// the locus where the functions in S do not vanish
			S := ReducedSubscheme(S);

			assert Dimension(S) eq -1;				// Check that the variety V_{\xi_1, \xi_2, \xi_3, Q}
										// intersects trivially the locus where
										// the elements of S are invertible
		end if;
	end for;
end for;

exit;
