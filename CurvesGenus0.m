/*
Determine whether a (possibly singular) 
genus-0 curve over the rational numbers 
has infinitely many rational points
*/
function HasInfinitelyManyRationalPointsGenus0(C)
	if Degree(FieldOfGeometricIrreducibility(C)) eq 1 then
		K := CanonicalDivisor(C);
		CAntiCan := Conic(Image(DivisorMap(-K)));	// Take anti-canonical image.

		return HasRationalPoint(CAntiCan);		// If the anti-canonical image
								// has a rational point, then
								// it is isomorphic to P_{1,Q},
								// hence it has infinitely many
								// rational points. Since C and
								// CAntiCan are isomorphic outside
								// of finitely many points, they
								// either both have infinitely many
								// rational points or they both
								// have finitely many rational
								// points						
	else
		if IsIrreducible(C) then
			return false;				// irreducible + rational point ==> geom. irred., so not geom irred + irred => no rat pt
		end if;
		error "This should not happen";
		return false;
	end if;
end function;