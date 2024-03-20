/*
Computations verifying part of the statements in section 7.
Specifically, this file computes, for every rational family
studied in section 7, an equation in the variables [lambda : mu]
that encodes the presence in V_{[lambda : mu]} of an angle
with a given (squared) amplitude.
*/

load "TracePoly.m";
load "Lattices.m";
load "RationalFamilies.m";
SetLogFile("TabulateAdditionalAngles.out");

/*
Given a rational family (specified by n
and angleTau) and an amplitude j,
prints in human-readable form the
conditions that ensure that a member
[lambda : mu] of the family has an
angle of the given amplitude, and
also displays the coordinates of 
the vectors in the lattice forming
an angle of that amplitude
*/
procedure ConditionsAdditionalAngle(n, angleTau, j)
	// Initialise the cyclotomic field,
	// an auxiliary polynomial ring in
	// a,b and t = mu/lambda, and the
	// rational family to be studied
	K<z> := CyclotomicField(n);
	R<a,b,t> := PolynomialRing(K,3);
	tau := BaseTau(n,angleTau)[1]*1 + BaseTau(n,angleTau)[2] * t;
	taubar := tau / z^angleTau;

	// Print information
	"Lattice with tau in Q(\zeta_n), n =", n;
	"Tau =", tau;
	"Squared angle between 1 and tau: zeta_n ^", angleTau;
	"Conditions for the existence of angles with squared amplitude zeta_n ^", j;

	/*
	Obtain the condition for the existence
	of an additional angle. S is the 0-dim
	scheme whose points parametrise rational
	angles with squared amplitude zeta_n^j
	*/
	_, DiscA, S := GenerateEquationFromAngle(n, angleTau, j);
	DiscA := R!DiscA;

	/*
	DiscA is formally a polynomial with
	coefficients in K. We are interested
	in it being a square in Q. We convert
	it to a polynomial with rational coefficients
	(which it already has) and clear
	denominators by multiplying by the
	square of a common denominator,
	which does not alter the property
	of being a square in Q. Finally, we
	clear any square factors common to
	all the (now integral) coefficients
	*/
	U<t0> := PolynomialRing(Rationals());
	hypPoly := &+[ Rationals()!Coefficient(DiscA, t, i) * t0^i : i in [0..4] ];
	CommonDenom := LCM([Denominator(c) : c in Coefficients(hypPoly)]);
	hypPoly := hypPoly*CommonDenom^2;
	gcd := GCD( [ Integers()!Coefficient(hypPoly, i) : i in [0..4] ] );
	_, gcd2 := SquareFreeFactorization(gcd);
	hypPoly := 1/gcd2^2 * hypPoly;

	/*
	We study the equation u^2 = c^2 * DiscA(t),
	where c is the constant constructed above
	that ensures that we work with integral
	coefficients. In particular, if C is the
	hyperelliptic curve u^2 = c^2 * DiscA(t),
	working in the function field F of C
	allows us to write down the coordinates
	of the elements of the lattice that
	form angles of squared amplitude zeta_n^j
	in terms of t = mu/lambda and u.
	Notice that -- since we are working with
	the affine coordinate t and not the projective
	coordinates [lambda : mu] -- the present u
	is in fact 1/lambda^2 times the u considered
	in the paper
	*/
	C := HyperellipticCurve( hypPoly );

	F := FunctionField(C);
	AssignNames(~F,["t","u"]);
	T<a0,b0> := PolynomialRing(F, 2);

	// We construct the base-change of the scheme S
	// to the function field of F, and obtain its
	// F-rational points
	function ConvertPolynomial(p)
		return &+[ Rationals()!(Coefficient(Coefficient(Coefficient(p,a,i),b,j),t,k)) * a0^i * b0^j * F.1^k : i in [0..2], j in [0..2], k in [0..4] ] ;
	end function;

	SF := Scheme(AffineSpace(T), [ ConvertPolynomial(R!p) : p in Generators(DefiningIdeal(S)) ]);
	RPSF := RationalPoints(SF);

	V<lambda,mu,u> := PolynomialRing(Rationals(),3);


	// Print output in the coordinates used in the paper
	"Let u be such that u^2 =", &+[ Coefficient(hypPoly,i) * mu^i * lambda^(4-i) : i in [0..4] ] ;
	"Factorisation:", Factorisation(&+[ Coefficient(hypPoly,i) * mu^i * lambda^(4-i) : i in [0..4] ] );
	"The values of (a,b) that give an angle with squared amplitude zeta_n ^", j, "are";


	/*
	The numerator and denominator of the first (resp. second) 
	coordinate of the rational points of S_F are of the form 
	f(t) + g(t)*u, f(t)-g(t)*u (indeed, they are two Galois-conjugate
	points). We extract f(t), g(t) by taking the half-sum and 
	half-difference of the first coordinates of the two rational
	points, and similarly for the second coordinates.
	To convert back to the coordinates used in the paper, we replace
	t --> mu/lambda, multiply back by lambda^2 both numerator and 
	denominator, and then divide by lambda the denominator
	(notice that the tau used in the code is
	BaseTau[1] + (mu/lambda)*BaseTau[2], while in the paper
	we use lambda*BaseTau[1] + mu*BaseTau[2]. It follows that a, b
	also need to be rescaled by a factor of lambda, which cancels
	a factor of lambda from the denominator).
	*/
	
	traceA := 1/2*(Numerator(RPSF[1][1]) + Numerator(RPSF[2][1]));
	varA := 1/2*(Numerator(RPSF[1][1]) - Numerator(RPSF[2][1]));
	DenA := Denominator(RPSF[1][1]);
	traceB := 1/2*(Numerator(RPSF[1][2]) + Numerator(RPSF[2][2]));
	varB := 1/2*(Numerator(RPSF[1][2]) - Numerator(RPSF[2][2]));
	DenB := Denominator(RPSF[1][2]);

	assert DenA eq Denominator(RPSF[2][1]);
	assert DenB eq Denominator(RPSF[2][2]);

	// Print output in the form used in the paper.
	"a";
	if Evaluate(varA,[0,1]) ge 0 then
		sign := " \\pm ";
	else
		sign := " \\mp ";
	end if;
	Sprint(&+ [ Rationals()!Coefficient(traceA,Parent(traceA).1,i) * lambda^(2-i) * mu^(i) : i in [1..2] ] + Evaluate(traceA, [0,0]) * lambda^2) cat sign cat Sprint(Abs(Evaluate(varA,[0,1])) * u);
	Rationals()!Coefficient(DenA, Parent(DenA).1, 1) * mu + Evaluate(DenA, [0,0]) * lambda;

	"b";
	if Evaluate(varB,[0,1]) ge 0 then
		sign := " \\pm ";
	else
		sign := " \\mp ";
	end if;

	Sprint(&+ [ Rationals()!Coefficient(traceB,Parent(traceB).1,i) * lambda^(2-i) * mu^(i) : i in [1..2] ] + Evaluate(traceB, [0,0]) * lambda^2) cat sign cat Sprint(Abs(Evaluate(varB,[0,1])) * u);
	Rationals()!Coefficient(DenB, Parent(DenB).1, 1) * mu + Evaluate(DenB, [0,0]) * lambda;

	// Finally, we look for a rational point of small height on C,
	// use it to interpret it as an elliptic curve, and compute
	// the corresponding Mordell-Weil group
	ratpts := RationalPoints(C : Bound := 10);

	E := MinimalModel(EllipticCurve(C, ratpts[1]));
	"Chosen rational point: (lambda : mu : u) = ", [ratpts[1][3], ratpts[1][1], ratpts[1][2]];
	E;
	G,m := MordellWeilGroup(E);
	_, testRank := Rank(E);
	if not testRank then
		"Error: cannot determine the rank of E(Q)";
	end if;
	"Mordell-Weil group", G;
	for i in [1..#Generators(G)] do
		"Generator", i, "with order", Order(G.i), ":", m(G.i);
	end for;
end procedure;


// Print output
"n = 8, angleTau = 1";
for j in [2,4] do
	"=================================";
	ConditionsAdditionalAngle(8, 1, j);
end for;

"n = 10, angleTau = 1";
for j in [2..5] do
	"=================================";
	ConditionsAdditionalAngle(10, 1, j);
end for;

"n = 10, angleTau = 2";
for j in [4,5] do
	"=================================";
	ConditionsAdditionalAngle(10, 2, j);
end for;

"n = 12, angleTau = 1";
for j in [2,3,4,6] do
	"=================================";
	ConditionsAdditionalAngle(12, 1, j);
end for;

"n = 12, angleTau = 3";
for j in [2,4] do
	"=================================";
	ConditionsAdditionalAngle(12, 3, j);
end for;

quit;
