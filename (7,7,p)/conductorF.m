// The number field K
P<x>:=PolynomialRing(Rationals());
K<z>:=NumberField(x^3 - x^2 - 2*x + 1);
OK:=Integers(K);

I2:=Factorisation(2*OK)[1,1];
I3:=Factorisation(3*OK)[1,1];
I7:=Factorisation(7*OK)[1,1];





// The Frey elliptic curve F and its twists
alfa:=z^2 + z - 2;
beta:=-z^2 + 4;
gamma:=-z - 2;

function FreyF(a,b,d);
	A:=alfa*(a+b)^2;
	B:=beta*(a^2 + (-z)*a*b + b^2);
    return EllipticCurve([0,d*(B-A),0,-d^2*A*B,0]);
end function;

// Compute the valuation at I2 of the conductor of F^{(delta)} under the assumptions v_2(a + b) = 1 and delta = 1 (mod 4).
// We have (v_2(c_4^{delta}),v_2(c_6^{delta}),v_2(Delta^{delta})) = (4,6,8), hence we are in a Case 6, 7 or 8 in Tate's classification.
// We apply Proposition 3 in [Papadopoulos]. It only depends on a and b modulo 2^5. 
// We note that the inequalities in (a) and (b) of loc. cit. are independent of the choice of delta = 1 (mod 4). Therefore we set delta = 1.
// If no assertion fails, then we are in Case 6 and the valuation at I2 of the conductor of F^{(delta)} is 4, as claimed in the paper.

for a,b in [0..32] do
	if (Valuation(a+b,2) eq 1) and (a*b mod 2 ne 0) then
		F:=FreyF(a,b,1);
		r:=2*z;
		a1:=aInvariants(F)[1];
		a2:=aInvariants(F)[2];
		a3:=aInvariants(F)[3];
		a4:=aInvariants(F)[4];
		a6:=aInvariants(F)[5];
		b2:=bInvariants(F)[1];
		b4:=bInvariants(F)[2];
		b6:=bInvariants(F)[3];
		b8:=bInvariants(F)[4];
		assert Valuation(b8 + 3*r*b6 + 3*r^2*b4 + r^3*b2 + 3*r^4,I2) ge 5;
		t:=2*z*(1+z);
		assert Valuation(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1,I2) eq 3;
	end if;
end for;

// Compute the valuation at I2 of the conductor of F^{(delta)} under the assumptions v_2(a + b) > 1 and delta = 1 (mod 4).
// We have (v_2(c_4^{delta}),v_2(c_6^{delta}),v_2(Delta^{delta})) = (4,6,8 + nu) with nu = 4(v_2(a + b) - 1) \geq 4, hence we are either in a Case 7 in Tate's classification or non-minimal.
// We apply Proposition 4 in [Papadopoulos]. It only depends on a and b modulo 2^5. 
// We note that the inequalities in (a) and (b) of loc. cit. are independent of the choice of delta = 1 (mod 4). Therefore we set delta = 1.
// If no assertion fails, then we are in a non-minimal case and the valuation at I2 of the conductor of F^{(delta)} is as claimed in the paper.

for a,b in [0..32] do
	if (Valuation(a+b,2) gt 1) and (a*b mod 2 ne 0) then
		F:=FreyF(a,b,1);
		r:=0;
		a1:=aInvariants(F)[1];
		a2:=aInvariants(F)[2];
		a3:=aInvariants(F)[3];
		a4:=aInvariants(F)[4];
		a6:=aInvariants(F)[5];
		b2:=bInvariants(F)[1];
		b4:=bInvariants(F)[2];
		b6:=bInvariants(F)[3];
		b8:=bInvariants(F)[4];
		assert Valuation(b8 + 3*r*b6 + 3*r^2*b4 + r^3*b2 + 3*r^4,I2) ge 5;
		s:=1+z;
		assert Valuation(a2 + 3*r - s*a1 - s^2,I2) ge 2;
	end if;
end for;



// Compute the valuation at I2 of the conductor of F^{(delta)} under the assumptions ab even and delta = 1 (mod 4).
// We have (v_2(c_4^{delta}),v_2(c_6^{delta}),v_2(Delta^{delta})) = (4,5,4), hence we are in a Case 3, 4 or 5 in Tate's classification.
// We apply Propositions 1 and 2 in [Papadopoulos]. It only depends on a and b modulo 2^3. 
// We note that the conditions in loc. cit. are independent of the choice of delta = 1 (mod 4). Therefore we set delta = 1.
// If no assertion fails, then the valuation at I2 of the conductor of F^{(delta)} is as claimed in the paper.

for a,b in [0..8] do
	if (Valuation(a*b,2) gt 0) and ([a mod 2, b mod 2] ne [0,0]) then
		F:=FreyF(a,b,1);
		r:=1+z+z^2;
		t:=z;
		a1:=aInvariants(F)[1];
		a2:=aInvariants(F)[2];
		a3:=aInvariants(F)[3];
		a4:=aInvariants(F)[4];
		a6:=aInvariants(F)[5];
		b2:=bInvariants(F)[1];
		b4:=bInvariants(F)[2];
		b6:=bInvariants(F)[3];
		b8:=bInvariants(F)[4];
		assert Valuation(a4 + r^2,I2) gt 0;
		assert Valuation(t^2 + a4*a2 - a6,I2) gt 0;
		if Valuation(a*b,2) gt 1 then
			assert Valuation(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1,I2) ge 2;
			assert Valuation(b8 + 3*r*b6 + 3*r^2*b4 + r^3*b2 + 3*r^4,I2) lt 3; // We are in Case 4
		end if;
		if Valuation(a*b,2) eq 1 then
			assert Valuation(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1,I2) lt 2; // We are in Case 3
		end if;
	end if;
end for;


// Compute the valuation at I2 of the conductor of F^{(delta)} under the assumptions ab = 2 (mod 4) and delta = z^2 - 2 (mod 4).
// We have (v_2(c_4^{delta}),v_2(c_6^{delta}),v_2(Delta^{delta})) = (4,5,4), hence we are in a Case 3, 4 or 5 in Tate's classification.
// We apply Propositions 1 and 2 in [Papadopoulos]. It only depends on a and b modulo 2^3. 
// We note that the conditions in loc. cit. are independent of the choice of delta = z^2 - 2 (mod 4). Therefore we set delta = z^2 - 2.
// If no assertion fails, then we are in Case 4 and the valuation at I2 of the conductor of F^{(delta)} is 4, as claimed in the paper.

for a,b in [0..8] do
	if Valuation(a*b,2) eq 1 then
		F:=FreyF(a,b,z^2-2);
		r:=z+z^2;
		t:=1+z+z^2;
		a1:=aInvariants(F)[1];
		a2:=aInvariants(F)[2];
		a3:=aInvariants(F)[3];
		a4:=aInvariants(F)[4];
		a6:=aInvariants(F)[5];
		b2:=bInvariants(F)[1];
		b4:=bInvariants(F)[2];
		b6:=bInvariants(F)[3];
		b8:=bInvariants(F)[4];
		assert Valuation(a4 + r^2,I2) gt 0;
		assert Valuation(t^2 + a4*a2 - a6,I2) gt 0;
		assert Valuation(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1,I2) ge 2;
		assert Valuation(b8 + 3*r*b6 + 3*r^2*b4 + r^3*b2 + 3*r^4,I2) lt 3;
	end if;
end for;

