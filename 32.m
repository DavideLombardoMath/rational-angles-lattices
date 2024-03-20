/*
Computations complementing the proof of Theorem 5.6
*/

SetLogFile("32.out");
load "Triples.m";
load "TracePoly.m";
load "CurvesGenus0.m";
load "Lattices.m";

/*
The possible values of n, taking into account the bounds given by Corollary 5.5
*/
ValuesOfn := [ j : j in Divisors(2^4*3^2*5) | j ne 1 and (j mod 15 ne 0) and EulerPhi(j) gt 2 ];

// Store the minimal polynomials of the
// different values of tau found
minpolys := [ [] : i in [1..2^4*3^2*5] ];

for n in ValuesOfn do
	"n =", n;

	K<z> := CyclotomicField(n);
	for e1 in Divisors(n) do		// Up to the Galois action, we may always assume
						// that e1 divides n

	for e2 in [1..(n-1)] do			// We loop over all possible values of e2,
						// except e2=0 since it would correspond to y=1

		if GCD([e1,e2,n]) eq 1 then	// if GCD(e1,e2,n)>1, then the roots of unity x,y
						// lie in a smaller cyclotomic field,
						// and therefore the corresponding value of tau
						// has already been considered
			x := z^e1;
			y := z^e2;
			if x ne 1 and x ne y then	// non-degeneracy conditions
				tau := x*(y-1)/(x-y);
				if Degree(MinimalPolynomial(tau)) gt 2 then	// if tau lies in a quadratic field,
										// then the corresponding lattice is
										// (up to homothety) the quadratic field
										// itself, and has already been studied
					type := TypeOfSpace(tau);
					if Max(type) eq 3 and #type ge 2 then	// if the space contains no rational 4-tuple
										// and at least 2 distinct tuples of 
										// rational angles
						Append(~minpolys[n], MinimalPolynomial(tau));		// store the minimal polynomial of tau
					end if;
				end if;
			end if;
		end if;
	end for;
	end for;
end for;


/*
Print output: all the distinct lattices
found, up to homothety, and the corresponding
rational angles
*/
for n in [1..2^4*3^2*5] do
	if #minpolys[n] gt 0 then
		"Lattices for n =", n;
		latt := DistinctLattices(minpolys[n]);
		for l in latt do
		"tau =", l;
		AllAffineAnglesInGivenLattice(l);
		end for;
	end if;
end for;

exit;
