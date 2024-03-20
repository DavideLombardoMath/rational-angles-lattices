/*
Given a polynomial p (in several variables)
with coefficients in a number field K, return
the polynomial over Q whose coefficients are
the traces from K to Q of the coefficients of p
*/
function TracePolynomial(p)
	if p eq 0 then
		return 0;
	end if;
	mons := Monomials(p);
	coeffs := Coefficients(p);
	tracedcoeffs := [ Trace(c) : c in coeffs ];
	return &+[tracedcoeffs[i]*mons[i] : i in [1..#mons]];
end function;

