/*
Methods to study the set of rational
points C(Q) when C has genus 3
and non-trivial automorphisms
*/

/*
Function to compute the rational
points of C as above
*/
function StudyGenus3(C)
		// Compute hyperelliptic, geometrically hyperelliptic, or planar model
		test := IsHyperelliptic(C);
		if test then
			// The curve is hyperelliptic over the ground field
			_, X, mapX := IsHyperelliptic(C);
		else
			if IsGeometricallyHyperelliptic(C) then // The smooth curve in the birational equivalence
								// class of C is hyperelliptic over Qbar but not 
								// over Q, hence all rational points are singular
				return true, SingularPoints(C);
			else
				// The smooth model can be canonically embedded as a plane quartic
				mapX := CanonicalMap(C);
				X := CanonicalImage(C, mapX);
			end if;
		end if;
		
		/*
		At this point we have a birational map
		C --> X, where X is smooth and given
		either by a hyperelliptic equation or
		as the zero locus of a homogeneous
		quartic equation in three variables
		*/

		// Compute automorphisms
		if test then
			AG, mapAG := AutomorphismGroup(X);
			AG := {mapAG(g) : g in AG};
		else
			AG := {g : g in Automorphisms(C)};
		end if;

		GoodQuotientFound := false;

		// Look for genus 1 quotients having
		// only finitely many rational points
		for beta in AG do
			if not GoodQuotientFound then
				H := AutomorphismGroup(X, [beta]);
				Y, mapY := CurveQuotient(H);
				if Genus(Y) eq 1 then
					E := Jacobian(Y);
					r := Rank(E);
					if r eq 0 then
						// Found a quotient of genus 1 and rank 0
						GoodQuotientFound := true;
						rpY := RationalPointsGenus1Rank0(Y);
					end if;
				end if;
			end if;
		end for;


		if not GoodQuotientFound then	// no genus 1 quotient has rank 0
		// Look for genus 2 quotients amenable
		// to a Chabauty computation
			for beta in AG do
				if not GoodQuotientFound then
					H := AutomorphismGroup(X, [beta]);
					Y, mapY := CurveQuotient(H);
	
					if Genus(Y) eq 2 then
						if RankBound(Jacobian(Y)) le 1 then
							GoodQuotientFound := true;
							Ysim, mapsim := SimplifiedModel(Y);
	
							// Chabauty applies, compute rational points
							// It is easier to work with the "simplified"
							// model Ysim, which is in any case isomorphic
							// to Y
							rpYsim := G2Chabauty(Ysim);
	
							// Pull-back the rational points on Ysim
							// to rational points on Y
							rpY := {};
							for ysim in rpYsim do
								rpY := rpY join { Pullback(mapsim,ysim) };
							end for;
						end if;
					end if;
				end if;
			end for;
		end if;

		if GoodQuotientFound then
			// At this point we know a map
			// X --> Y and the set Y(Q)
			// We determine X(Q) by pullback

			rpX := {};
			for y in rpY do
				rpX := rpX join RationalPoints(Pullback(mapY,y));
			end for;

			/*
			In turn, X is not the original curve C,
			but we also know a map C --> X, and we
			now know X(Q), so we may further pull
			back to C to determine C(Q).	
			We also take care of the fact that
			C --> X is not necessarily an isomorphism
			by throwing in the singular points of C
			*/

			rpC := {};
			for x in rpX do
				try
					rpC := rpC join RationalPoints(Pullback(mapX,x));
				catch e
					rpC := rpC join { Pullback(mapX,x) };
				end try;
			end for;
			return true, rpC join {Q : Q in SingularPoints(C)};
		else
			// if no "good" quotient has been found, return false
			// to signal that the procedure failed
			return false, [];
		end if;
end function;
