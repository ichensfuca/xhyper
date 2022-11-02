// The number field K
P<x>:=PolynomialRing(Rationals());
K<z>:=NumberField(x^3 - x^2 - 2*x + 1);
OK:=Integers(K);

I2:=Factorisation(2*OK)[1,1];
I3:=Factorisation(3*OK)[1,1];
I7:=Factorisation(7*OK)[1,1];


// This function computes the running time (in hours)
t0:=Realtime();
function Realhours();
   return Realtime(t0)/3600;
end function;


// The Frey elliptic curve F and its twists
alfa:=z^2 + z - 2;
beta:=-z^2 + 4;
gamma:=-z - 2;

function FreyF(a,b,d);
	A:=alfa*(a+b)^2;
	B:=beta*(a^2 + -z*a*b + b^2);
	return EllipticCurve([0,d*(B-A),0,-d^2*A*B,0]);
end function;




// Given a form f, this function computes a possible bound for p using the NORM OF THE DIFFERENCE between the a_Q coefficients for Q|q 


function BoundOverK(q,f,curve,twist);
F:=CoefficientField(f);
factQ:=Factorisation(q*OK);
B:=1;
for x,y in [0..q-1] do
	if x le y and [x,y] ne [0,0] then
		Bxy:=0;
		C:=curve(x,y,twist);
		for i in [1..#factQ] do
			Q:=factQ[i,1];
			if LocalInformation(C,Q)[3] eq 0 then
				diffQ:=Norm(TraceOfFrobenius(C,Q)-HeckeEigenvalue(f,Q));
			else
				diffQ:=Norm((Norm(Q)+1)^2-HeckeEigenvalue(f,Q)^2);
      			end if;
			Bxy:=Gcd(Integers()!Bxy,Integers()!diffQ);
    		end for;
		if Bxy eq 0 then
			return []; // Here p is unbounded
		else
			B:=B*Bxy;
		end if;
	end if;
end for;
return [q*B];
end function;

// Given a form f, this function computes a possible bound for P using the DIFFERENCE between the a_Q coefficients for Q|q 

function refined_BoundOverK(q,f,curve,twist);
F:=CoefficientField(f);
if F eq Rationals() then
	OF:=1;
else
	OF:=Integers(F);
end if;
factQ:=Factorisation(q*OK);
B:=1*OF;
for x,y in [0..q-1] do
	if x le y and [x,y] ne [0,0] then
		Bxy:=0*OF;
		C:=curve(x,y,twist);
		for i in [1..#factQ] do
			Q:=factQ[i,1];
			if LocalInformation(C,Q)[3] eq 0 then
				diffQ:=TraceOfFrobenius(C,Q)-HeckeEigenvalue(f,Q);
			else
				diffQ:=(Norm(Q)+1)^2-HeckeEigenvalue(f,Q)^2;
      			end if;
			if F eq Rationals() then
				Bxy:=Gcd(Integers()!Bxy,Integers()!diffQ);			
			else
				Bxy:=Gcd(Bxy,diffQ*OF);
			end if;
    		end for;
		if Bxy eq 0*OF then
			return []; // Here p is unbounded
		else
			B:=B*Bxy;
		end if;
	end if;
end for;
return [q*B];
end function;




// For the forms in "forms", this function returns the possible ideals P|p with p\ge5 using the "good" primes q in AuxiliaryPrimes using and standard elimination

function Bound(forms,curve,twist,AuxiliaryPrimes);
	print "Performing standard elimination for",#forms,"form(s) with set of auxiliary primes",AuxiliaryPrimes;
	for i in [1..#forms] do
		f:=forms[i];
		print "";
		print "Checking form no",i;
		print "";
		Sf:={};
		bool:=0;
  		for q in AuxiliaryPrimes do
			if bool eq 0 or Sf ne {} then
				print "Dealing with q =",q;
				if BoundOverK(q,f,curve,twist) ne [] then // Here f can be discarded for large enough p
					Sq:=Set([I[1] : I in Factorisation(BoundOverK(q,f,curve,twist)[1])]);
					if bool eq 0 then
						print "This form can be eliminated for large enough p !";
						Sf:=Sq;
						bool:=1;
					end if;
					Sf:=Sf meet Sq;
					Sf:={p : p in Sf | p gt 3 and p ne 7};
			    	end if;
			end if;
		end for;
		if bool eq 0 then
		    	print "Form no",i," not eliminated for large enough p";
	  	else
			if Sf eq {} then
				print "Form no",i,"is eliminated";
			else
				print "Form no",i;
				print "with coefficient field :", CoefficientField(f) ;
				print "is not eliminated for prime(s) :",Sf;
			end if;
		end if;
		print "*************************************************************";
	end for;
return "";
end function;


// For the form f, this function returns the possible ideals P|p with p\ge5 using the "good" primes q in AuxiliaryPrimes and refined elimination

function refined_Bound(f,curve,twist,AuxiliaryPrimes);
	print "Performing refined elimination with set of auxiliary primes",AuxiliaryPrimes;
	print "";
	Sf:={};
	bool:=0;
  	for q in AuxiliaryPrimes do
		if bool eq 0 or Sf ne {} then
			print "Dealing with q =",q;
			if refined_BoundOverK(q,f,curve,twist) ne [] then // Here f can be discarded for large enough p
				Sq:=Set([I[1] : I in Factorisation(refined_BoundOverK(q,f,curve,twist)[1])]);
				if bool eq 0 then
					print "This form can be eliminated for large enough p !";
					Sf:=Sq;
					bool:=1;
				end if;
				Sf:=Sf meet Sq;
				Sf:={P : P in Sf | Characteristic(ResidueClassField(P)) gt 3};
		    	end if;
		end if;
	end for;
	if bool eq 0 then
	    	print "The form is not eliminated for large enough p";
	else
		if Sf eq {} then
			print "The form is eliminated";
		else
			print "The form with coefficient field :", CoefficientField(f) ;
			print "is not eliminated for",#Sf,"prime ideal(s) above :", Set([Norm(P) : P in Sf]);
		end if;
	end if;
	print "*************************************************************";
	return "";
end function;



print "";
print "******************************************************************";
print "PART B : eliminating in the case 7 dividing a+b";
print "";


print "";
print "Eliminating the case ab even...";
print "";


N4:=I2^3*I3*I7;
print "Computing forms at level N4 = I2^3*I3*I7...";
forms4:=Eigenforms(NewSubspace(HilbertCuspForms(K,N4)));
print "Done !";
print "There are ", #forms4, "newforms";
print "++++++++++++++++++++++", Realhours();


print "";
print "... with ab divisible by 2 exactly once";
print "";

print "We first perform standard elimination at level N4 = I2^3*I3*I7 using primes q = 13, 29, 41 and 43 and the Frey curve twisted by z^2 - 2 :";
Bound(forms4,FreyF,z^2-2,[5,13,29,41,43]);
print "++++++++++++++++++++++", Realhours();


print "";
print "The prime p = 5 survives for the forms no 56 and 84 ; we discard it using refined elimination with q = 13, 29, 41 and 43 :";
refined_Bound(forms4[56],FreyF,z^2-2,[13,29,41,43]);
refined_Bound(forms4[84],FreyF,z^2-2,[13,29,41,43]);
print "++++++++++++++++++++++", Realhours();
print "";

print "";
print "The prime p = 17 survives for the form no 121 ; we discard it using refined elimination with q = 5 :";
refined_Bound(forms4[121],FreyF,z^2-2,[5]);
print "++++++++++++++++++++++", Realhours();
print "";


