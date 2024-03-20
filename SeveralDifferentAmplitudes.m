/*
Computations verifying part of the statements in section 7.
Specifically, this file computes, for every rational family
studied in section 7, the finitely many lattices that have
angles with more than one "extra" amplitude beyond those
that can be rationally parametrised.
*/

load "CurvesGenus1.m";
load "CurvesGenus2.m";
load "CurvesGenus3.m";
load "TracePoly.m";
load "Lattices.m";
load "RationalFamilies.m";

SetLogFile("SeveralDifferentAmplitudes.out");

R<lambda,mu,u,v> := PolynomialRing(Rationals(),4);

/*
Given two non-proportional, homogeneous quartic
forms f_1(lambda, mu) and f_2(lambda, mu),
return all pairs [lambda : mu] in P_1(Q)
such that both f_1(lambda,mu) and f_2(lambda,mu)
are squares in Q. (This only succeeds if 
it is possible to determine the set of rational
points on certain genus 3 curves)
See Proposition 7.9 for details.
*/
function LatticesFromIntersectionQuadrics(f1, f2)
	S<t,w,z> := PolynomialRing(Rationals(),3);
	h := hom<R->S | [t,1,w,z]>;

	g := GCD(f1,f2);
	if g eq 1 then
		C3 := Curve( AffineSpace(S), [ w^2-h(f1*f2) , z ] );
	else
		C3 := Curve(AffineSpace(S), [ w^2-h(f1), z^2-h(f2) ] );
	end if;

	test, ratpts := StudyGenus3(C3);
	if not test then
		error "Cannot the determine the set of rational points on the relevant genus 3 curve";
	end if;
	lattices := { [P[1],1] : P in ratpts } join { [0,1] } ;
	lattices := { P : P in lattices | IsSquare(Evaluate(f1, [P[1],P[2],0,0])) and IsSquare(Evaluate(f2, [P[1],P[2],0,0])) };

	return lattices;
end function;


/*
Given an integer n in {8,10,12}, the squared angle
that characterises the rational family, and lists
of amplitudes list_i, list_j, determine (for each
i in list_i and j in list_j) all the lattices in 
the rational family having a rational angle of 
squared amplitude zeta_n^i and a rational angle
of squared amplitude zeta_n^j. For each such lattice,
also print the list of all rational angles in the 
lattice
*/
function PrintSolutions(n,angleTau,listI,listJ)
	IntTaus := [];
	for i in listI do
	for j in listJ do
		if i lt j then
			"====", n, angleTau, i, j, "====";
			f1 := R!GenerateEquationFromAngle(n,angleTau,i);
			f2 := R!GenerateEquationFromAngle(n,angleTau,j);
			lattices := LatticesFromIntersectionQuadrics(f1,f2);
			for P in lattices do
				"-------------------------";
				lambda := P[1];
				mu := P[2];
				bTau := BaseTau(n,angleTau);
				K<z> := CyclotomicField(n);
				tau := bTau[1] * lambda + bTau[2] * mu;
				IntTaus := IntTaus cat [tau];
				"Angles in lattice with tau =", tau;
				AllAffineAnglesInGivenLattice(tau);
			end for;
		end if;
	end for;
	end for;
	return IntTaus;
end function;



// Print output
n := 8;
angleTau := 1;
listI := [2];
listJ := [4];

taus8 := PrintSolutions(n,angleTau,listI,listJ);

n := 10;
angleTau := 1;
listI := [2..5];
listJ := [2..5];

taus10 := PrintSolutions(n,angleTau,listI,listJ);

n := 10;
angleTau := 2;
listI := [4,5];
listJ := [5];

taus102 := PrintSolutions(n,angleTau,listI,listJ);

n := 12;
angleTau := 1;
listI := [2,3,4,6];
listJ := [3,4,6];

taus12 := PrintSolutions(n,angleTau,listI,listJ);

n := 12;
angleTau := 3;
listI := [2];
listJ := [4];

taus123 := PrintSolutions(n,angleTau,listI,listJ);

exit;
