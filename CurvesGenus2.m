/*
Let C be a curve of genus 2 over the field
of rational numbers.
The following function attempts to compute
the set of rational points C(Q).
It succeeds whenever the Mordell-Weil rank 
rk Jac(C)(Q) can be proven to be at most 1.
After checking for local solubility at the
small primes not dividing the discriminant of C:
* we perform a descent on Jac(C) to prove that
  it has rank at most 1; if this fails, throw an
  error.
* if the rank is 0, Chabauty immediately applies
  to find all the rational points on C.
* otherwise, if the rank is 1, we find a rational 
  point on J of infinite order. Such a point
  necessarily generates a finite-index subgroup
  of the Mordell-Weil group J(Q), and can
  therefore be used to carry out Chabauty's method
  and determine the set of rational points C(Q).
*/
function G2Chabauty(C)
	// Test for local solubility
	for p in [i : i in [3..13] | IsPrime(i) and not i in BadPrimes(C)] do
		if #RationalPoints(ChangeRing(C,FiniteField(p))) eq 0 then
			return {};
		end if;
	end for;

	J := Jacobian(C);

	// case rk J(Q) = 0
	if RankBound(J) eq 0 then
		return Chabauty0(J);
	end if;

	// case rk J(Q) > 1,
	// or at least rk J(Q) cannot
	// be proven to be <= 1
	if RankBound(J) ne 1 then
		error "Cannot prove that the Jacobian has rank <=1";
	end if;	

	// case rk J(Q) = 1
	// Find a rational point on J
	// of infinite order
	CurrentBound := 10;
	rp := [];
	while rp eq [] do
		CurrentBound := 2*CurrentBound;
		rp := RationalPoints(J : Bound := CurrentBound);
		rp := [P : P in rp | Order(P) eq 0];
	end while;
	GeneratorFiniteIndexSubgroup := rp[1];

	// we are all set to apply Chabauty
	points := Chabauty(GeneratorFiniteIndexSubgroup);
	return points;
end function;

