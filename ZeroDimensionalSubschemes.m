/*
Given a 0-dimensional subscheme of P_3(a,b,c,d),
the following functions computes its rational points
and filters out those that do not have geometric
meaning for the problem at hand. More precisely,

* GeometricallyMeaningfulRationalPoints only keeps
  those points (a,b,c,d) for which a,b are different,
  c,d are different, and {a,b}, {c,d} are different;

* RationalPointsabcd performs the same tests, and in
  addition checks that at most 1 among {a,b,c,d}
  vanishes (if that is not the case, then the rational
  point corresponds to a space having at least a
  4-tuple of rational angles)

* RationalPoints222 performs the same tests as
  GeometricallyMeaningfulRationalPoints, and in
  addition tests that no variable vanishes
  (otherwise, the point would correspond to
  a space with at least a triple of rational angles),
  that no two variables coincide (same reason),
  and that a*b is different from c*d
*/

function GeometricallyMeaningfulRationalPoints(ZeroDim)
	RP := RationalPoints(ZeroDim);
	RPList := [];
	for l in RP do
		RPList := RPList cat [l];
	end for;
	RPList := [pt : pt in RPList | (pt[1] ne pt[2]) and (pt[3] ne pt[4]) ];
	RPList := [pt : pt in RPList | {pt[1], pt[2]} ne {pt[3], pt[4]} ];
	return RPList;
end function;


function RationalPointsabcd(ZeroDim)
	RPList := GeometricallyMeaningfulRationalPoints(ZeroDim);
	RPList := [pt : pt in RPList | #[i : i in [1..4] | pt[i] eq 0] lt 2 ];
	return RPList;
end function;

function RationalPoints222(ZeroDim)
	RPList := GeometricallyMeaningfulRationalPoints(ZeroDim);
	RPList := [pt : pt in RPList | &and([ pt[i] ne 0 : i in [1..4]]) ];
	RPList := [pt : pt in RPList | &and([ pt[i] ne pt[j] : i in [1..4], j in [1..4] | i ne j]) ];
	RPList := [pt : pt in RPList | pt[1]*pt[2] ne pt[3]*pt[4] ];
	return RPList;
end function;