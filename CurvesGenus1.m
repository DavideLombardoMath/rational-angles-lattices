/*
Given a smooth curve Y/Q of genus 1,
assumed to have a rational point,
the following function:
* finds a rational point P of small
  height
* finds an isomorphism from Y to 
  an elliptic curve E in Weierstrass
  form, using P as the origin of the
  group law
* checks whether rk E(Q) = 0; if it
  is not, it throws an error and quits
* if it is, E(Q) is finite, hence Y(Q)
  is also finite. We first compute E(Q)
  using MAGMA's internal machinery, and
  then pull back each rational point
  to Y. This yields the finite set Y(Q).
*/

function RationalPointsGenus1Rank0(Y)
	if IsSingular(Y) then
		error "Y is singular";
	end if;
	rps := RationalPoints(Y : Bound := 20);
	E, map := EllipticCurve(Y, rps[1]);
	if RankBound(E) ne 0 then
		error "Elliptic curve of positive rank";
	end if;
	G, Gmap := MordellWeilGroup(E);
	_, inversemap := IsInvertible(map);
	Ratpts := { inversemap(Gmap(g)) : g in G };
	return Ratpts;
end function;