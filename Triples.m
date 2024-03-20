/*
Helper function to generate a
non-redundant list of triples
of roots of unity of a given
order, up to symmetry equivalence
*/

/*
Given two multisets t1, t2
consisting of three elements
and represented as ordered lists
checks whether t1=t2 as multisets
*/
function SameUnorderedTriple(t1,t2)
	if Min(t1) ne Min(t2) then
		return false;
	end if;
	if Max(t1) ne Max(t2) then
		return false;
	end if;
	if &+t1 ne &+t2 then
		return false;
	end if;
	return true;
end function;


/*
The next function tries to determine
(as quickly as possible) whether two
triples are symmetry equivalent
*/
function EquivalentTriples(t1,t2,n)
	// due to the way these triples are built
	// they are certainly not equivalent if
	// t1[1] =/= t2[1]
	// Indeed, the first element of a triple
	// is min(GCD(n,e1), GCD(n,e2), GCD(n,e3))
	if t1[1] ne t2[1] then
		return false;
	end if;

	// the quantity (a,n) is invariant
	// under both a --> ka with (k,n)=1
	// and a --> -a
	if not SameUnorderedTriple( [GCD(i,n) : i in t1], [GCD(i,n) : i in t2] ) then
		return false;
	end if;

	
	/*
	preliminary test, based on the fact that if {a,b,c}
	is equivalent to {a',b',c'} = {\pm ka, \pm kb, \pm kc}
	and a^2+b^2+c^2 is invertible mod n
	then we can easily recover k^2
	as k^2 = ( (a')^2 + (b')^2 + (c')^2 ) / (a^2+b^2+c^2)
	We can then test whether 
	k^2 * {a^2,b^2,c^2} = { (a')^2, (b')^2, (c')^2 }

	On the other hand, a necessary condition for equivalence
	is that either both a^2+b^2+c^2 and (ka)^2+(kb)^2+(kc)^2 are
	invertible, or none of the two is
	*/
	s1 := &+[ a^2 : a in t1 ];
	s2 := &+[ a^2 : a in t2 ];
	if GCD(s1,n) eq 1 and not GCD(s2,n) eq 1 then
		return false;
	end if;

	if not GCD(s1,n) eq 1 and GCD(s2,n) eq 1 then
		return false;
	end if;
	
	if GCD(s1,n) eq 1 and GCD(s2,n) eq 1 then
		k2 := (s2*InverseMod(s1, n)) mod n;
		if not SameUnorderedTriple( [a^2*k2 mod n : a in t1], [a^2 mod n : a in t2] ) then
			return false;
		end if;
	end if;
	// end of preliminary test
	
	/*
	if we have been unable to rule out that the two
	triples are equivalent, we revert to the
	definition and check exhaustively all possible
	permutations, choices of sign, and choices of
	Galois action (=invertible elements mod n)
	*/
	invertibles := [ i : i in [1..n] | GCD(i,n) eq 1 ];

	/*
	Notice that if both triples t1 and t2 contain
	an element that is invertible modulo n,
	then the only possible choices of Galois action
	are those that transform a fixed invertible element
	in t1 to one of the invertible elements in t2 (up to
	sign, but these are taken care of later)
	The next few lines exploit this fact to
	minimize the number of Galois automorphisms
	that we need to try
	*/
	foundInvertible := false;
	for j in t1 do
		if not foundInvertible then
			if GCD(j,n) eq 1 then
				invertibles := [ i*InverseMod(j,n) : i in t2 | GCD(i,n) eq 1 ];
				foundInvertible := true;
			end if;
		end if;
	end for;

	// K = I^3 = {-1,1}^3 takes into account the possible
	// choices of sign
	I := [-1,1];
	K := CartesianPower(I,3);
	for i in invertibles do
	for k in K do
		if SameUnorderedTriple ( [ (t1[j] * i * k[j]) mod n : j in [1..3] ], [ t2[j] mod n : j in [1..3] ] ) then
			return true;
		end if;
	end for;
	end for;
	return false;
end function;

/*
For a positive integer n, returns a list
of representatives of triples (e1,e2,e3)
up to symmetry equivalence
*/
function InequivalentTriples(n)
	triples := [];

	d1 := [ d : d in Divisors(n) | d ne n ];	// up to symmetry equivalence, the first
							// element of the triple can always be assumed 
							// to be a divisor of n

for e1 in d1 do
	for e2 in [i : i in [e1..Floor(n/2)] | GCD(i,n) ge e1 ] do	// up to symmetry equivalence, we
									// may assume that (e_2,n) >= (e_1,n) = e_1,
									// hence in particular e_2 >= e_1,
									// and also e_2 <= n/2. Since the triple
									// (e_1, e_2, e_3) contains at most
									// one zero, one can assume that it is e_3
									// (if the triple does in fact contain a 0)
		for e3 in [i : i in [0] cat [e2..Floor(n/2)] | GCD(i,n) ge e1 ] do	// we may assume that (e_3, n) >= e_1
											// and e_3 <= n/2, e_3 >= e_2, (e_3,n) >= e_1

			if GCD([e1,e2,e3,n]) eq 1 then					// the condition ensures that Q(zeta_n)
											// is the smallest field containing
											// zeta_n^{e_1}, zeta_n^{e_2}, zeta_n^{e_3}

				if EulerPhi(Integers()!(n/e1)) le 2*EulerPhi(Integers()!(n/GCD([n,e2,e3]))) then			
											// x lies in an at most quadratic extension of Q(y,z)
					t := [e1,e2,e3];
					test := true;
					for ttest in triples do
						if test then
							test := test and not EquivalentTriples(t, ttest, n);	// check that the triple is not equivalent
														// to any triple already found
						end if;
					end for;
					if test then
						Append(~triples, t);
					end if;
				end if;
			end if;
		end for;
	end for;
end for;

return triples;
end function;

