/*
Given a rational family lambda*t1 + mu*t2, where
t1, t2 are fixed elements of the n-th cyclotomic
field (for n = 8, 10, 12) and [lambda : mu] is 
parametrised by P_{1,Q}, compute:
* the points [ lambda' : mu' ] that give a lattice
  homothetic to the lattice corresponding to
  [lambda : mu]
* the parameters [ lambda'' : mu'' ] that correspond
  to the complex conjugate lattice
*/

load "Lattices.m";
load "RationalFamilies.m";
SetLogFile("LatticeCollisions.out");

/*
Given an element t of a cyclotomic
field K = Q(z) and an integer i
with 0 <= i < deg(K/Q), returns
the coefficient of z^i in t
*/
function zCoefficient(t, i)
	V, map := KSpace(Parent(t), Rationals());
	return map(t)[i+1];
end function;

/*
Given a polynomial p with coefficients
in a cyclotomic field K and an integer
i with 0 <= i < deg(K/Q), returns the
polynomial giving the coefficient of z^i 
in the polynomial p
*/
function zCoefficientPoly(p, i)
	coeffs := Coefficients(p);
	mons := Monomials(p);
	return &+[ zCoefficient(coeffs[j], i) * mons[j] : j in [1..#coeffs] ];
end function;

procedure LatticeCollisions(n, AngleTau)
	/*
	Initialise the cyclotomic field K,
	the polynomial ring R in the
	variables lambda, mu, lambda', mu',
	and the families tau and tau'
	*/
	K<z> := CyclotomicField(n);
	R<lambda, mu, lambdap, mup> := PolynomialRing(K,4);
	bt := BaseTau(n,AngleTau);
	tau := bt[1] * lambda + bt[2] * mu;
	taup := bt[1] * lambdap + bt[2] * mup;
	
	/* Construct the matrix whose rows are the
	coordinates of 1, tau, tau', tau*tau'
	in the basis {1,z,z^2,z^3} */
	M := Matrix(R,4,4, [1,0,0,0] cat [zCoefficientPoly(tau,i) : i in [0..3]] cat [zCoefficientPoly(taup,i) : i in [0..3]] cat [zCoefficientPoly(tau*taup,i) : i in [0..3]] );

	/* The spaces <1, tau> and <1, tau'> are
	homothetic if and only if the determinant
	of M vanishes. We hence factor det(M) */
	factors := [ f[1] : f in Factorisation(Determinant(M)) ];

	/* det(M) is bilinear and vanishes
	if [lambda : mu] = [lambda' : mu'] */
	assert (lambda*mup-mu*lambdap) in factors;
	assert #factors eq 2;

	/* we are only interested in the
	nontrivial factor, different
	from lambda*mu' - mu*lambda' */
	otherFactor := [ f : f in factors | f ne lambda*mup-mu*lambdap ][1];
	f := otherFactor;
	/* f is of the form g_1(lamba,mu) * lambda' + g_2(lambda,mu) * mu'
	hence vanishes only for [lambda' : mu'] = [ -g_2(lambda,mu) : g_1(lambda,mu) ] */
	"The lattice parametrised by", [lambda,mu], "is homothetic (only) to the lattice parametrised by", [-Coefficient(f,mup,1), Coefficient(f,lambdap,1)];


	/* Now we consider the complex conjugate lattice,
	which is <1, taubar> = <1/taubar, 1>.
	Up to a nonzero rational number, 1/taubar is also
	equal to the product of the conjugates of tau
	different from taubar */
	autos := [ iso<K->K | K.1^i> : i in [1..n] | GCD(i,n) eq 1 ];
	taus := [ auto(bt[1]) * lambda + auto(bt[2]) * mu : auto in autos ];
	OneOverTaubar := taus[1]*taus[2]*taus[3];

	/* 1/taubar is a sum f_i(lambda,mu) * z^i, where
	each f_i is a polynomial with rational coefficients.
	If the various f_i have common factors, they evaluate
	to a rational number for every value of [lambda:mu],
	hence we can factor them out */
	coefs := [zCoefficientPoly(OneOverTaubar, i) : i in [0..3]];
	g := GCD(coefs);
	simplifiedOneOverTaubar := [ R!(c / g) : c in coefs ];
	g2 := GCD( [ GCD( [Integers()!a : a in Coefficients(c) ] ) : c in simplifiedOneOverTaubar | c ne 0 ] );
	simplifiedOneOverTaubar := [ 1/g2*c : c in simplifiedOneOverTaubar ];

	// Some basic linear algebra to express
	// 1/taubar in terms of the basis bt[1], bt[2]
	V := VectorSpace(K,4);
	bt1Vector := V![zCoefficient(bt[1],i) : i in [0..3]];
	bt2Vector := V![zCoefficient(bt[2],i) : i in [0..3]];
	Ev1 := V![Evaluate(p,[1,0,0,0]) : p in simplifiedOneOverTaubar];
	Ev2 := V![Evaluate(p,[0,1,0,0]) : p in simplifiedOneOverTaubar];
	W := VectorSpaceWithBasis([bt1Vector, bt2Vector]);
	vLambda := Coordinates(W, W!Ev1);
	vMu := Coordinates(W, W!Ev2);
	"The complex conjugate lattice is parametrised by", [vLambda[i] * lambda + vMu[i] * mu : i in [1..2]];
end procedure;



// Print output

"=== n = 8, angleTau = zeta_8 ===";
LatticeCollisions(8,1);

"\n=== n = 10, angleTau = zeta_{10} ===";
LatticeCollisions(10,1);
"\n=== n = 10, angleTau = zeta_{10}^2 ===";
LatticeCollisions(10,2);

"\n=== n = 12, angleTau = zeta_{12} ===";
LatticeCollisions(12,1);
"\n=== n = 12, angleTau = zeta_{12}^3 ===";
LatticeCollisions(12,3);

exit;