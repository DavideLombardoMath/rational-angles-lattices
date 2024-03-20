SetLogFile("RationalFamilies.out");
load "TracePoly.m";
load "Lattices.m";


/*
Parametrisations of the 5 rational
families studied in the paper, and
generation of the equation describing
spaces in this family having an
additional angle of prescribed
amplitude.
*/

/*
Given n in {8,10,12} and an integer
angleTau, returns a basis for the
2-dimensional Q-vector space of 
elements tau in Q(zeta_n) such that
the angle between the complex conjugate
of tau and tau is given by zeta_n^angleTau
*/
function BaseTau(n,angleTau)
	K<z> := CyclotomicField(n);
	if [n,angleTau] eq [8,1] then
		return [ z^2-z^3, 1+z ];
	end if;
	if [n,angleTau] eq [10,1] then
		return [ -2-2*z^2+z^3, 1+z ];
	end if;
	if [n,angleTau] eq [10,2] then
		return [ 1+z^2, z ];
	end if;
	if [n,angleTau] eq [12,1] then
		return [ z+z^2-z^3, 1+z ];
	end if;
	if [n,angleTau] eq [12,3] then
		return [ z+z^2, 1+z^3 ];
	end if;
end function;


/*
Consider the rational family corresponding to the
given values of n and angleTau. Compute the
quartic homogeneous form f_j(lambda,mu) such that 
the lattice parametrised by [lambda : mu] has a 
rational angle of squared amplitude zeta_n^j if 
and only if f_j(lambda,mu) is the square of a
rational number
*/
function GenerateEquationFromAngle(n, angleTau, j)
	R<lambda,mu,u,v> := PolynomialRing(Rationals(),4);
	K<z> := CyclotomicField(n);
	T<a,b,t> := PolynomialRing(K,3);
	bTau := BaseTau(n,angleTau);
	tau := bTau[1] + t*bTau[2];
	taubar := tau / z^angleTau; // by definition of angleTau

	// (tau+a, tau+b) form an angle of squared amplitude
	// zeta_n^j if and only if a,b satisfy the following
	// equation
	eqn := (tau+a)*(taubar+b)-z^j*(taubar+a)*(tau+b);

	// we are interested in the rational solutions, so we take
	// the trace of these equations to Q
	eqs := [ TracePolynomial(eqn*z^i) / EulerPhi(n) : i in [0..Degree(K)-1] ];

	S := Scheme(AffineSpace(Parent(eqs[1])), eqs);

	/*
	The scheme (geometrically) consists of two points,
	hence one is rational if and only if the other one
	is. We compute a quadratic equation for the coordinate
	a; there is a solution for a (hence also for b) if
	and only if the discriminant of the quadratic equation
	is a square.
	*/
	fa := Generators(EliminationIdeal(DefiningIdeal(S),{a,t}))[1];
	aa := Coefficient(fa,a,2);
	ab := Coefficient(fa,a,1);
	ac := Coefficient(fa,a,0);
	DiscA := ab^2 - 4*aa*ac;

	return &+[lambda^(4-i) * mu^(i) * Rationals()!Coefficient(DiscA,t,i) : i in [0..4]], DiscA, S;
end function;


/*
Consider the rational family corresponding to the
given values of n and angleTau. Compute the values
of (a,b) such that (tau+a, tau+b) is a rational
angle of squared amplitude zeta_n^j, provided that
a, b can be expressed as rational functions in
\mu over \lambda
*/
function ParametrisationAngle(n, angleTau, j)
	R<lambda,mu,u,v> := PolynomialRing(Rationals(),4);
	K<z> := CyclotomicField(n);
	T<a,b, Lambda, Mu> := PolynomialRing(K,4);
	U := FieldOfFractions(T);
	AssignNames(~U, ["a", "b", "lambda", "mu"]);
	bTau := BaseTau(n,angleTau);
	tau := Lambda * bTau[1] + Mu * bTau[2];
	taubar := tau / z^angleTau; // by definition of angleTau

	// (tau+a, tau+b) form an angle of squared amplitude
	// zeta_n^j if and only if a,b satisfy the following
	// equation
	eqn := (tau+a)*(taubar+b)-z^j*(taubar+a)*(tau+b);

	// we are interested in the rational solutions, so we take
	// the trace of these equations to Q
	eqs := [ TracePolynomial(eqn*z^i) / EulerPhi(n) : i in [0..Degree(K)-1] ];

	S := Scheme(AffineSpace(Parent(eqs[1])), eqs);

	// fa is an equation for a in terms of lambda, mu
	fa := Generators(EliminationIdeal(DefiningIdeal(S),{a, Lambda, Mu}))[1];
	F := Factorisation(fa);


	Results := [];

	for f in F do
		if Degree(f[1], a) gt 0 then
		Sf := Scheme(AffineSpace(Parent(eqs[1])), eqs cat [f[1]]);
		fb := Generators(EliminationIdeal(DefiningIdeal(Sf), {b,Lambda, Mu}))[1];

		a1 := Coefficient(f[1],a,1);
		a0 := Coefficient(f[1],a,0);

		b1 := Coefficient(fb,b,1);
		b0 := Coefficient(fb,b,0);

		Append(~Results, [-a0/a1, -b0/b1]);
		end if;
	end for;
	return Results;
end function;




/*
Given a rational family and a list of squared amplitudes
of angles which admit rational parametrisations, lists
the points [lambda : mu] for which 
(i) the parametrisations of some of these angles are
  ill-defined (vanishing denominators),
(ii) some of the "extra" rational angles involve 1 or tau
*/
function CollisionAngles(n, angleTau, jList)
	points := {};
	RationalFunctions := [];
	for j in jList do
		res := ParametrisationAngle(n, angleTau, j);
		for r in res do
			RationalFunctions := RationalFunctions cat r;
		end for;
	end for;
	
	A := Parent(ChangeRing(Numerator(RationalFunctions[1]),Rationals()));
	P := ProjectiveSpace(A);

	

	"Vanishing of numerators";
	localpts := {};
	for f in RationalFunctions do
		S := Scheme(P, [ A!ChangeRing(Numerator(f),Rationals()), A.1, A.2]);
		points := points join {P : P in RationalPoints(S)};
		localpts := localpts join {P : P in RationalPoints(S)};
	end for;
	"Points:", localpts;

	"Vanishing of denominators";
	localpts := {};
	for f in RationalFunctions do
		S := Scheme(P, [ A!ChangeRing(Denominator(f),Rationals()), A.1, A.2]);
		points := points join {P : P in RationalPoints(S)};
		localpts := localpts join {P : P in RationalPoints(S)};
	end for;
	"Points:", localpts;


	"Collisions";
	localpts := {};
	for f1 in RationalFunctions do
	for f2 in RationalFunctions do
		if f1 ne f2 then
			S := Scheme(P, [ A!ChangeRing(Numerator(f1-f2),Rationals()), A.1, A.2]);
			points := points join {P : P in RationalPoints(S)};
			localpts := localpts join {P : P in RationalPoints(S)};
		end if;
	end for;
	end for;
	"Points:", localpts;

	"== Description of the special lattices ==";
	base := BaseTau(n, angleTau);
	for P in points do
		"[lambda : mu] = ", P[3], P[4];
		tau := P[3] * base[1] + P[4] * base[2];
		// tau;
		TypeOfSpace(tau);
		AllAffineAnglesInGivenLattice(tau);
	end for;

	return A;
end function;


/*
Given:
(a) a rational family, parametrised by n (the order of a root of unity zeta_n)
    and angleTau (such that the squared angle of tau is zeta_n^angleTau);
(b) a list of indices j such that the rational family contains angles
    of squared amplitude zeta_n^j, parametrised by rational functions in mu
    and lambda;
(c) the data of an "elliptic family", given as a 5-tuple (Num1, Den1, Num2,
    Den2, Delta), where the 'extra' rational angles in the elliptic family
    are parametrised by (Num_1 \pm u)/(Den_1) and (Num_2 \mp u)/(Den_2),
    with u^2 = Delta;

we compute all projective points [lambda : mu] for which one of the following
holds:

(i)   u=0, so that the \pm choices of signs give the same angle;
(ii)  (Num_1 \pm u)/(Den_1) = (Num_2 \mp u)/(Den_2);
(iii) the value of (Num_i \pm u)/(Den_i) coincides with the value of one of
      the rational functions parametrising the angles of squared amplitude
      zeta_n^j, for some j in jList;
(iv)  one of the denominators Den_1 or Den_2 vanishes;
(v)   (Num_1 \pm u)/(Den_1) or (Num_2 \mp u)/(Den_2) vanishes, so that one
      of the 'extra' angles in the elliptic family is adjacent to tau.

For each such point, we compute the exact type of the space parametrised by
[lambda : mu].
*/
procedure CollisionAnglesEllipticFamilies(n, angleTau, jList, Num1, Den1, Num2, Den2, Delta)
	// The variable "points" will hold the finite set of special points
	// given by cases (i), (ii), (iii), (iv) and (v) above
	points := {};

	// We start by computing the rational functions that parametrise
	// the endpoints of the angles of squared amplitude \zeta_n^j
	// for j in jList
	RationalFunctions := [];
	for j in jList do
		res := ParametrisationAngle(n, angleTau, j);
		for r in res do
			RationalFunctions := RationalFunctions cat r;
		end for;
	end for;
	
	A := Parent(Delta);
	P := ProjectiveSpace(A);

	
	// The zero locus of the vanishing of Delta, and its rational points
	print "Vanishing of discriminant";
	S := Scheme(P, [ Delta, A.1, A.2 ]);
	RationalPoints(S);
	points := points join {P : P in RationalPoints(S)};

	// One has (Num_1 \pm u)/(Den_1) = (Num_2 \mp u)/(Den_2)
	// if and only if (Num_1 \pm u)*(Den_2) = (Num_2 \mp u)*(Den_1),
	// if and only if (Num1 Den2 - Den1 Num2) = \mp u (Den1 + Den2);
	// squaring and replacing u^2 = Delta, this gives the equation below,
	// of which we compute the zero-locus
	print "Collisions between two of the 'extra' angles";
	S := Scheme(P, [ (Den2*Num1-Den1*Num2)^2-Delta*(Den1+Den2)^2, A.1, A.2 ]);
	RationalPoints(S);
	points := points join {P : P in RationalPoints(S)};


	// Next, we look at collisions between one of the 'extra' angles 
	// given by the elliptic parametrisation and one of the angles
	// having a rational parametrisations
	print "Collisions between one of the 'extra' angles and one of the 'standard' ones";
	localpts := {};
	for f in RationalFunctions do
		B := Parent(f);
		g := Numerator( (A!Numerator(f)/A!Denominator(f)*Den1-Num1)^2-Delta );
		S := Scheme(P, [ g, A.1, A.2 ]);
		points := points join {P : P in RationalPoints(S)};
		localpts := localpts join {P : P in RationalPoints(S)};
	end for;


	for f in RationalFunctions do
		g := Numerator( (A!Numerator(f)/A!Denominator(f)*Den2-Num2)^2-Delta );
		S := Scheme(P, [ g, A.1, A.2 ]);
		points := points join {P : P in RationalPoints(S)};
		localpts := localpts join {P : P in RationalPoints(S)};
	end for;
	"Points:", localpts;

	// We look at the vanishing locus of the algebraic functions
	// appearing as denominators in the 'extra' angles.
	print "Vanishing of denominator of one of the 'extra' angles";

	localpts := {};
	S := Scheme(P, [ Den1, A.1, A.2 ]);
	points := points join {P : P in RationalPoints(S)};
	localpts := localpts join {P : P in RationalPoints(S)};
	S := Scheme(P, [ Den2, A.1, A.2 ]);
	points := points join {P : P in RationalPoints(S)};
	localpts := localpts join {P : P in RationalPoints(S)};
	"Points:", localpts;



	// Finally, we look at the vanishing locus of the algebraic functions
	// given by the elliptic parametrisation
	print "Vanishing of the parameter of one of the 'extra' angles";

	localpts := {};
	S := Scheme(P, [ Num1^2-Delta, A.1, A.2 ]);
	points := points join {P : P in RationalPoints(S)};
	localpts := localpts join {P : P in RationalPoints(S)};
	S := Scheme(P, [ Num2^2-Delta, A.1, A.2 ]);
	points := points join {P : P in RationalPoints(S)};
	localpts := localpts join {P : P in RationalPoints(S)};
	"Points:", localpts;


	// For each of the special points found above,
	// print a description of (a lattice representing)
	// the corresponding space
	"== Description of the special lattices ==";
	base := BaseTau(n, angleTau);
	for P in points do
		print "[lambda : mu] = ", P[3], P[4];


		// if Delta is not a rational square, then
		// the point we are looking at does not represent
		// an actual member of the elliptic family
		DiscAtPoint := Evaluate(Delta, [P[1], P[2], P[3], P[4]]);
		print "Discriminant at point", DiscAtPoint;

		if IsSquare(DiscAtPoint) then		
			tau := P[3] * base[1] + P[4] * base[2];
			print TypeOfSpace(tau);
			print AllAffineAnglesInGivenLattice(tau);

		else
			"Discriminant at point is not a square";
		end if;
	end for;


end procedure;


"==== n = 8, squared angle \zeta_{8} ====";
"=== Rational angles ===";
ParametrisationAngle(8, 1, 1);
ParametrisationAngle(8, 1, 3);
A := CollisionAngles(8,1,[1,3]);

lambda := A.3;
mu := A.4;

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_8^2 ===";
CollisionAnglesEllipticFamilies(8, 1, [1,3], 
lambda^2 - mu^2,
mu,
-2*lambda*mu,
lambda,
lambda^4 + lambda^3*mu + lambda^2*mu^2 + lambda*mu^3
);

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_8^4 ===";

CollisionAnglesEllipticFamilies(8, 1, [1,3], 
lambda^2 - 2*lambda*mu - mu^2,
lambda + mu,
lambda^2 - 2*lambda*mu - mu^2,
lambda + mu,
3*lambda^4 + 2*lambda^3*mu + 4*lambda^2*mu^2 + 2*lambda*mu^3 + mu^4
);



"\n\n\n\n";

"==== n = 10, squared angle \zeta_{10} ====";
"=== Rational angles ===";
ParametrisationAngle(10, 1, 1);
A := CollisionAngles(10,1,[1]);

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{10}^2 ===";
CollisionAnglesEllipticFamilies(10, 1, [1], 
-3*lambda^2 + 7*lambda*mu - 2*mu^2,
-4*lambda + 2*mu,
-5*lambda^2 + 5*lambda*mu,
-2*lambda,
33*lambda^4 - 38*lambda^3*mu + 21*lambda^2*mu^2 - 4*lambda*mu^3
 );


"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{10}^3 ===";

CollisionAnglesEllipticFamilies(10, 1, [1], lambda^2 + 11*lambda*mu - 6*mu^2,
-2*lambda + 4*mu,
-(9*lambda^2 - lambda*mu - 4*mu^2),
-(4*lambda + 2*mu),
41*lambda^4 - 38*lambda^3*mu + 9*lambda^2*mu^2 + 8*lambda*mu^3 - 4*mu^4
 );

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{10}^4 ===";

CollisionAnglesEllipticFamilies(10, 1, [1], 
6*lambda^2 - 4*lambda*mu - mu^2,
4*lambda,
-(-2*lambda^2 + 8*lambda*mu - 3*mu^2),
-(-2*lambda + 2*mu),
28*lambda^4 - 40*lambda^3*mu + 28*lambda^2*mu^2 - 8*lambda*mu^3 + mu^4
 );


"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{10}^5 ===";

CollisionAnglesEllipticFamilies(10, 1, [1], 
-4*lambda^2 + 6*lambda*mu - mu^2,
-3*lambda + mu,
-4*lambda^2 + 6*lambda*mu - mu^2,
-3*lambda + mu,
31*lambda^4 - 38*lambda^3*mu + 24*lambda^2*mu^2 - 7*lambda*mu^3 + mu^4
 );




"\n\n\n\n";

"==== n = 10, squared angle \zeta_{10}^2 ====";
"=== Rational angles ===";
ParametrisationAngle(10, 2, 2);
A := CollisionAngles(10,2,[2]);

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{10}^4 ===";

CollisionAnglesEllipticFamilies(10, 2, [2], 
-2*lambda^2 - lambda*mu + mu^2,
2*lambda,
-3*lambda*mu - mu^2,
2*mu,
4*lambda^3*mu + 5*lambda^2*mu^2 + 2*lambda*mu^3 + mu^4
 );

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{10}^5 ===";

CollisionAnglesEllipticFamilies(10, 2, [2], 
-lambda^2 - 2*lambda*mu,
lambda + mu,
-lambda^2 - 2*lambda*mu,
lambda + mu,
lambda^4 + 3*lambda^3*mu + 4*lambda^2*mu^2 + 2*lambda*mu^3 + mu^4
 );



"\n\n\n\n";


"==== n = 12, squared angle \zeta_{12} ====";
"=== Rational angles ===";
ParametrisationAngle(12, 1, 1);
ParametrisationAngle(12, 1, 5);
A := CollisionAngles(12,1,[1,5]);

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{12}^2 ===";

CollisionAnglesEllipticFamilies(12, 1, [1,5], 
lambda^2 - mu^2,
mu,
-lambda^2 - 2*lambda*mu,
lambda,
lambda^4 + 2*lambda^3*mu + 2*lambda^2*mu^2 + lambda*mu^3
 );


"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{12}^3 ===";

CollisionAnglesEllipticFamilies(12, 1, [1,5], 
-2*lambda^2 - 6*lambda*mu - mu^2,
4*lambda + 2*mu,
2*lambda^2 - 2*lambda*mu - 3*mu^2,
2*mu,
4*lambda^4 + 8*lambda^3*mu + 16*lambda^2*mu^2 + 12*lambda*mu^3 + 5*mu^4
);


"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{12}^4 ===";

CollisionAnglesEllipticFamilies(12, 1, [1,5], 
lambda^2 - 2*lambda*mu - 2*mu^2,
lambda + 2*mu,
-lambda^2 - 4*lambda*mu - mu^2,
2*lambda + mu,
5*lambda^4 + 10*lambda^3*mu + 12*lambda^2*mu^2 + 7*lambda*mu^3 + 2*mu^4
);



"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{12}^6 ===";

CollisionAnglesEllipticFamilies(12, 1, [1,5], 
-2*lambda*mu - mu^2,
lambda + mu,
-2*lambda*mu - mu^2,
lambda + mu,
2*lambda^4 + 4*lambda^3*mu + 5*lambda^2*mu^2 + 3*lambda*mu^3 + mu^4
);



"\n\n\n\n";

"==== n = 12, squared angle \zeta_{12}^3 ====";
"=== Rational angles ===";
ParametrisationAngle(12, 3, 3);
A := CollisionAngles(12,3,[3]);

"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{12}^2 ===";

CollisionAnglesEllipticFamilies(12, 3, [3], 
-(-2*lambda*mu - mu^2),
-(lambda + mu),
lambda^2 - mu^2,
mu,
lambda^4 - lambda^2*mu^2 - 2*lambda*mu^3 - mu^4
);


"\n\n";
"=== Elliptic family: angle of squared amplitude \zeta_{12}^4 ===";

CollisionAnglesEllipticFamilies(12, 3, [3], 
-(-lambda^2 - 4*lambda*mu - mu^2),
-(2*lambda + mu),
2*lambda^2 + 2*lambda*mu - mu^2,
-lambda + mu,
5*lambda^4 + 4*lambda^3*mu + 3*lambda^2*mu^2 - 2*lambda*mu^3 - mu^4
);

