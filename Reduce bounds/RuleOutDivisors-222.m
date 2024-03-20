/*
Computational proof of Proposition 7.4
See RuleOutDivisors-32.m for detailed comments
*/

SetLogFile("RuleOutDivisors-222.out");

load "../Triples.m";
load "../TracePoly.m";

for n in [11, 13, 17, 19, 23] cat [2^5, 3^3, 5^2, 7^2] cat [5*7, 3^2*7, 2^4*7, 2^3*7] cat [3^2*5, 2^4*5] do
	"n =", n;
	K<zetan> := CyclotomicField(n);
	R<a,b,c,d,xp,yp,zp,u,v> := PolynomialRing(K, 9);
	RR<a0,b0,c0,d0,xp0,yp0,zp0,u0,v0> := PolynomialRing(Rationals(),9);

	BasisK := Basis(K);

	triples := InequivalentTriples(n);
	"Number of inequivalent triples:", #triples;

	for t in triples do
		x := zetan^t[1]*xp;
		y := zetan^t[2]*yp;
		z := zetan^t[3]*zp;


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

		eqn := &+[monomials[i] * coefficients[i] : i in [1..#coefficients]];
		eqs := [RR!TracePolynomial(eqn*z) : z in BasisK ];

		S := Scheme(AffineSpace(RR), eqs cat [xp0*yp0*zp0*u0-1, a0*b0*c0*d0*(a0-b0)*(a0-c0)*(a0-d0)*(b0-c0)*(b0-d0)*(c0-d0)*(a0*b0-c0*d0)*v0-1]);
		S := ReducedSubscheme(S);
		assert Dimension(S) eq -1;
	end for;
end for;

exit;
