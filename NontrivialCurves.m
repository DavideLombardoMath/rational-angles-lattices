/*
Given a curve C in P^3(a,b,c,d) we test whether its rational points
can have geometric meaning for the problem at hand: in particular,
the function IsNontrivialabcd checks that:
* no two variables vanish identically along C, for
  otherwise the point is either meaningless (if a=b=0 o c=d=0) or
  corresponds to a space of type (4) (if one variable from {a,b} and
  one variable from {c,d} vanish
* nor (a=c and b=d) nor (a=d and b=c) hold identically along C,
  since points with these properties do not correspond to spaces
  with 3 different angles
* neither a=b nor c=d hold identically along C, because when a=b
  the pair (tau+a, tau+b) does not determine an angle

In addition to the above, the function IsNontrivial222 also checks
that ab-cd does not vanish identically along the curve, as well as
that no single variable vanishes along the curve (if one among 
a,b,c,d is zero, then the space has a triple of rational angles
containing 1, \tau)
*/

function IsNontrivialabcd(C)
	P := AmbientSpace(C);

	// test if two variables vanish identically on curve
	for X in Subsets({1,2,3,4}, 2) do
		XList := SetToSequence(X);
		S := Scheme(P, [P.XList[1], P.XList[2]]);
		if IsSubscheme(C,S) then
			return false;
		end if;
	end for;

	// test if a=c, b=d or
	// a=d, b=c hold identically
	// along the curve
	S := Scheme(P, [P.1-P.3, P.2-P.4]);
	if IsSubscheme(C,S) then
		return false;
	end if;
	S := Scheme(P, [P.1-P.4, P.2-P.3]);
	if IsSubscheme(C,S) then
		return false;
	end if;

	// test if a=b or c=d holds identically
	S := Scheme(P, [P.1-P.2]);
	if IsSubscheme(C,S) then
		return false;
	end if;
	S := Scheme(P, [P.3-P.4]);
	if IsSubscheme(C,S) then
		return false;
	end if;

	return true;
end function;


function IsNontrivial222(C)
	if not IsNontrivialabcd(C) then
		return false;
	end if;

	P := AmbientSpace(C);

	// test whether C is contained in one of the coordinate planes
	for i in [1..Dimension(P)+1] do				
		S := Scheme(P, [P.i]);
		if IsSubscheme(C, S) then
			return false;
		end if;
	end for;

	// test if ab=cd identically along C
	S := Scheme(P, [P.1*P.2-P.3*P.4]);
	if IsSubscheme(C,S) then
		return false;
	end if;

	return true;
end function;
