// This function computes the running time (in hours)
t0:=Realtime();
function Realhours();
   return Realtime(t0)/3600;
end function;


// The Frey elliptic curve E
function FreyE(a,b)
	a2:=-(a-b)^2;
    a4:=-2*a^4 + a^3*b - 5*a^2*b^2 + a*b^3 -2*b^4;
    a6:=a^6 - 6*a^5*b + 8*a^4*b^2 - 13*a^3*b^3 + 8*a^2*b^4 - 6*a*b^5 + b^6;
    return EllipticCurve([0,a2,0,a4,a6]);
end function;


// Computation of the conductor of E at 2
for a, b in [1..32] do 
	if [a mod 2, b mod 2] ne [0,0] and a le b then
	E:=FreyE(a,b);
		if Valuation(a+b,2) eq 1 then
			assert Valuation(Conductor(E),2) eq 4;
		end if;
		if Valuation(a+b,2) gt 1 then
			assert Valuation(Conductor(E),2) eq 3;
		end if;
		if Valuation(a+b,2) eq 0 then
			if Valuation(a*b,2) gt 1 then assert Valuation(Conductor(E),2) eq 2; end if;
			if Valuation(a*b,2) eq 1 then assert Valuation(Conductor(E),2) eq 3; end if;
		end if;
	end if;
end for;

// Computation of the conductor of E at 7
for a, b in [1..7] do 
	if [a mod 7, b mod 7] ne [0,0] and a le b then
		E:=FreyE(a,b);
		assert Valuation(Conductor(E),7) eq 2;
       end if;
end for;


// This function returns the list of prime ideals P|p for which there is a possible congruence (mod P) between f and the Frey curve by checking this congruence with the Frobenius elements at a prime q.

function BoundOverQ(q,f);
	F:=CoefficientField(f);
	OF:=Integers(F);
	L:={};
	for x,y in [0..q-1] do
  		if [x,y] ne [0,0] then
	    		C:=FreyE(x,y);
			if LocalInformation(C,q)[3] eq 0 then
				diffq:=TraceOfFrobenius(C,q)-Coefficient(f,q);
			else
				diffq:=(q+1)^2-Coefficient(f,q)^2;
			end if;
			if diffq eq 0 then
				return {}; // here p is unbounded
			else
				fact:=Set([I[1] : I in Factorisation(diffq*OF)]); // here p is bounded using congruences for the a_q coefficients
				//print fact;
				if fact ne {} then
					L:=L join fact;
				end if;
			end if;
	    end if;
	end for;
	if q eq 3 then
		return L; 
	else
		return L join Set([I[1] : I in Factorisation(q*OF)]);
	end if;
end function;

// For a given level N, this function returns the possible surviving forms using the "good" primes q less than 40 
function Bound(N);
	forms:=Newforms(CuspidalSubspace(ModularForms(N,2)));
	setofprimes:=[x : x in PrimesUpTo(40) | x notin [2,7] and (x mod 7 ne 1)];
	for i in [1..#forms] do
		f:=forms[i,1];
		Sf:={};
		bool:=0;
  		for q in setofprimes do
		    Sq:=BoundOverQ(q,f);
		    if Sq ne {} then
			if bool eq 0 then
				Sf:=Sq;
				bool:=1;
			end if;
			Sf:=Sf meet Sq;
		    end if;
		end for;
		//print "i, bool, Sf=",i, bool, Sf;
		if (Sf eq {}) and (bool eq 0) then
			print "*********************************";
		    	print "Form no",i," not eliminated !";
	  	else
			survivingprimes:=[P : P in Sf | Characteristic(ResidueClassField(P)) gt 3 and Characteristic(ResidueClassField(P)) ne 7];
			print "*********************************";
			if survivingprimes eq [] then
				print "Form no",i,"eliminated";
			else
				print "Form no",i;
				print "with coefficient field :", CoefficientField(f) ;
				print "not eliminated for the following prime ideals :", survivingprimes;
			end if;
		end if;  
	end for;
return "";
end function;



// Eliminating newforms
print "Eliminating forms at level 2^2*7^2 = 196";
Bound(196);
print "++++++++++++++++++++++", Realhours();
print "";

print "Only form no 2 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,0) :";
fE:=Newform(FreyE(1,0));
forms1:=Newforms(CuspidalSubspace(ModularForms(196,2)));
for i in [1..#forms1] do
	f:=forms1[i,1];
	print Coefficient(fE,3)-Coefficient(f,3);
end for;
print "";
print "++++++++++++++++++++++", Realhours();
print "";

print "";
print "Eliminating forms at level 2^3*7^2 = 392";
Bound(392);
print "++++++++++++++++++++++", Realhours();
print "";

print "Only form no 1 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,-1) :";
fE:=Newform(FreyE(1,-1));
forms2:=Newforms(CuspidalSubspace(ModularForms(392,2)));
for i in [1..#forms2] do
	f:=forms2[i,1];
	print Coefficient(fE,3)-Coefficient(f,3);
end for;
print "++++++++++++++++++++++", Realhours();
print "";
