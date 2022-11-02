


// This function computes the running time (in hours)
t0:=Realtime();
function Realhours();
   return Realtime(t0)/3600;
end function;

// Functions related to the curve E


// The Frey elliptic curve E
function FreyE(a,b)
    a2:=-(a-b)^2;
    a4:=-2*a^4 + a^3*b - 5*a^2*b^2 + a*b^3 -2*b^4;
    a6:=a^6 - 6*a^5*b + 8*a^4*b^2 - 13*a^3*b^3 + 8*a^2*b^4 - 6*a*b^5 + b^6;
    return EllipticCurve([0,a2,0,a4,a6]);
end function;



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
function BoundQ(N);
	forms:=Newforms(CuspidalSubspace(ModularForms(N,2)));
        // The condition x mod 7 ne 1 ensures we have good reduction.
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
		if (Sf eq {}) and (bool eq 0) then
		    	print "Form no",i," not eliminated !";
	  	else
			survivingprimes:=[P : P in Sf | Characteristic(ResidueClassField(P)) gt 3 and Characteristic(ResidueClassField(P)) ne 7];
			if survivingprimes eq [] then
				print "Form no",i,"eliminated";
			else
				print "Form no",i;
				//print "with coefficient field :", CoefficientField(f) ;
				print "not eliminated for the following prime ideals :", survivingprimes;
			end if;
		end if;  
	end for;
return "";
end function;


// Functions related to the curve F

// The number field K
R1<X>:=PolynomialRing(Rationals());
m1:=X^3 + X^2 - 2*X - 1;
K<z>:=NumberField(m1);
OK:=Integers(K);

// Minimal model of the Frey elliptic curve F and its twists
alfa:=z^2 + z - 2;
beta:=-z^2 + 4;
gamma:=-z - 2;

function FreyF(a,b,d);
	A:=alfa*(a+b)^2;
	B:=beta*(a^2 + -z*a*b + b^2);
	return EllipticCurve([0,d*(B-A),0,-d^2*A*B,0]);
end function;


// Given a form f, this function computes a possible bound for p using the norm of the difference between the a_Q coefficients for Q|q
// The testing of whether we are in the good or multiplicative reduction case uses the fact that the model for F is minimal at q.
 
function BoundOverK(q,f,curve,twist);
F:=CoefficientField(f);
factQ:=Factorisation(q*OK);
B:=1;
for x in [0..q-1] do
	for y in [x..q-1] do
		if [x,y] ne [0,0] then
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
end for;
return [q*B];
end function;


// For each form in "forms", this function returns the possible residue characteristics p (with p greater than 3 and different from 7) of the prime ideals P using the primes q in AuxiliaryPrimes.

function Bound(forms,curve,twist,AuxiliaryPrimes);
	for i in [1..#forms] do
		f:=forms[i];
		t1:=Realtime();
		Sf:={};
		bool:=0;
  		for q in AuxiliaryPrimes do
			if bool eq 0 or Sf ne {} then
				//print "Dealing with q =",q;
				BK:=BoundOverK(q,f,curve,twist);
				if BK ne [] then // Here f can be discarded for large enough p
					Sq:=Set([I[1] : I in Factorisation(BK[1])]);
					if bool eq 0 then
						//print "This form can be eliminated for large enough p !";
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
				print "Form no",i,"is not eliminated for prime(s) :",Sf;
			end if;
		end if;
	end for;
return "";
end function;


// The next function applies a finer elimination technique to a pair (f,p) by comparing traces of Frobenius at prime ideals above a given prime number q. 
// It is fast but requires to to know the specific value of p and only allows the use of one auxiliary prime.
// The testing of whether we are in the good or multiplicative reduction case uses the fact that the model for F is minimal at q.

function refined_Bound(f,curve,twist,q,p);
	t1:=Realtime();
	factQ:=Factorisation(q*OK);
	//print "There are",#factQ,"prime ideals above q in K";
	F:=CoefficientField(f);
	//print "The degree of the coefficient field F of f is", Degree(F);
	OF:=Integers(F);
	factP:=[I[1] : I in Factorization(p*OF)];
	//print "There are",#factP,"prime ideals above p in F";
	ResFields:=[<PP,toPP> where PP,toPP := ResidueClassField(I) : I in factP];
	for x in [0..q-1] do
		for y in [x..q-1] do
			if [x,y] ne [0,0] then
				C:=curve(x,y,twist);
				for res in ResFields do
					bool:=0;
					for i in [1..#factQ] do
						if bool eq 0 then
						Q:=factQ[i,1];
						afQ:=HeckeEigenvalue(f,Q);
						if LocalInformation(C,Q)[3] eq 0 then 
							if res[2](OF!afQ - TraceOfFrobenius(C,Q)) ne res[2](0) then
								bool:=1;
							end if;
						end if;
						if LocalInformation(C,Q)[3] ne 0 then 
							if res[2](OF!afQ^2 - (Norm(Q) + 1)^2) ne res[2](0) then
								bool:=1;
							end if;
		      				end if;
		      				end if;
		    			end for;
		    			if bool eq 0 then
						return "The form is NOT eliminated !";
		    			end if;
    				end for;
			end if;
		end for;
	end for;
	print "The refined elimination with q =",q,"works. The form is eliminated for p =",p;
	//print "Running time for this form (in seconds) =", Realtime()-t1;
	return "";
end function;


// Functions related to the curve C

I2:=Factorisation(2*OK)[1,1];
I3:=Factorisation(3*OK)[1,1];
I7:=Factorisation(7*OK)[1,1];
I11:=11*OK;

fact13:=Factorisation(13*OK);
I13a:=fact13[1,1];
I13b:=fact13[2,1];
I13c:=fact13[3,1];

fact29:=Factorisation(29*OK);
I29a:=fact29[1,1];
I29b:=fact29[2,1];
I29c:=fact29[3,1];


Py<y>:=PolynomialRing(K);
L:=ext<K | y^2 - (z-2)>; // this is CyclotomicField(7)
OL:=Integers(L);
M:=ext<K | y^2 + 1>;
OM:=Integers(M);


print "Determining the splitting behaviour of the auxiliary primes [5,11,13,17,29] in L = Cyclotomic(7) and M = K(\sqrt{-1})..";

function SplitBools(Q,OM,OL)
	// Q is a prime in K (hence principal)
	// OM, OL are the ring of integers of quadratic extensions M/K, L/K such that M/Q and L/Q are Galois
	// returns 2 booleans which are true when Q splits in M/K or L/K respectively
	_,genQ:=IsPrincipal(Q);
	factQM:=Factorisation(genQ*OM);
	if #factQM eq 2 then
		bolMq:=true;
	else
		bolMq:=false;
	end if;
	
	factQL:=Factorisation(genQ*OL);
	if #factQL eq 2 then
		bolLq:=true;
	else
		bolLq:=false;
	end if;
	return bolMq, bolLq;
end function;

bolM5,bolL5:=SplitBools(5*OK,OM,OL);
bolM11,bolL11:=SplitBools(11*OK,OM,OL);
bolM13,bolL13:=SplitBools(I13a,OM,OL);
bolM29,bolL29:=SplitBools(I29a,OM,OL);

print "..done.";



// This function computes the value at a prime ideal Q in K of the quadratic character corresponding to the extension L/K

function twistL(Q)
	bolMq,bolLq:=SplitBools(Q,OM,OL);
	if bolLq then
		return 1;
	else 
		return -1;
	end if;
end function;

G:=Automorphisms(K);
R<x>:=PolynomialRing(K);


// This function is necessary to deal with some incompatibility of universes arising in the output of some Magma functions.
// Return the set of prime divisors of x, with special treatment when x is zero or a unit.
S:=Parent({1,2,3});
function primeset(x)
  x:=Integers()!x;

  if x eq 0 then
    return S!{0};
  elif x in {-1,1} then
    return S!{x};
  else 
    return S!Set(PrimeDivisors(x));
  end if;
end function;


// Returns the base change to K of the hyperelliptic Frey curve C constructed by Kraus attached to solution (a,b,c) 
function FreyC(a,b);
  R<x>:=PolynomialRing(K);
  return HyperellipticCurve(x^7 + 7*a*b*x^5 + 14*a^2*b^2*x^3 + 7*a^3*b^3*x + b^7 - a^7);
end function;


// This function finds the automorphism of G mapping ideal (or element) Q1 to Q2
function find_g(Q1,Q2,G);
  for g in G do
    if Q2 eq g(Q1) then
      return g;
    end if;
  end for;
end function;


// The Jacobian J=J(C) is of GL2-type over K. We want to extract the traces of Frobenius of the 2-dim representations of G_K attached to J/K . 
// For a prime Q of K of good reduction the degree 6 Euler factor at Q factors into 3 degree 2 polynomials, where the middle coefficients 
// are minus the traces.

function tracefrobenius(C,Q,K);
  R:=PolynomialRing(K);	
  Lf:=EulerFactor(C,Q);
  Lf:=Reverse(Lf);
  Lfactor:=Factorization(R!Lf);
  
  return [-Coefficient(f[1],1) : f in Lfactor]; 
end function;


function tracesList(C,QQs,G);
  // QQs is a list of primes in K above the same rational prime q not in {2,3,7} 	
  // G = Automorphisms(K) is cyclic
  tLQ:=tracefrobenius(C,QQs[1],K);
  ggs:=[find_g(QQs[1],Q,G) : Q in QQs];
  tL:=[[g(tr) : g in ggs] : tr in tLQ];
  return tL;
end function;


function BoundForm(q,QQs,bolMq,f,twist,LL,curveC,exponents,G,KtoLL)
// q is a rational prime not in {2,3,7} and QQs is a subset of primes in K above q
// bolMq should be true if the primes in QQs split in M/K where M = K(\sqrt{-1})
// Note that M/Q is Galois and so the primes in QQs will behave the same way in each of these extensions, because they are all above the same rational prime q
// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
// twist should be the quadratic character of K which fixes L = Cyclotomic(7)
// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
// curveC should be the Frey hyperelliptic curve FreyC
// exponents should be a set with a list of prime exponents to eliminate; if no restrictions are known set exponents:={}
// G should be Automorphism(K)
// KtoLL should be a field inclusion of K into LL
// auxiliary flag returned is whether the exceptional exponent list is empty


if #exponents eq 0 then
	bolq:=true;
else
	print "We still have to eliminate exponents p =",exponents;
	bolq:=q in exponents;
end if;	

print "Performing standard elimination with",#QQs,"prime ideal(s) of residue characteristic(s)",{Characteristic(ResidueClassField(Q)) : Q in QQs};

B:={};
hL:=[HeckeEigenvalue(f,Q)*twist(Q) : Q in QQs];


Lbad:=Gcd([Integers()!AbsoluteNorm(LL!(Norm(QQs[i])+1)^2 - LL!hL[i]^2) : i in [1..#QQs]]);

if #exponents eq 0 then 
	B:=B join primeset(Lbad);
else 
	B:=B join {p : p in exponents | Lbad mod p eq 0};		    
end if;

if bolMq then
	for x,y in [0..q-1] do
		if [x,y] ne [0,0] and x le y and (x+y) mod q ne 0 then
			C:=curveC(x,y);
			tL:=tracesList(C,QQs,G);
		        Lxy:=1;
		        for u in tL do
				Lxy:=Lxy*Gcd([Integers()!AbsoluteNorm(KtoLL(u[i]) - LL!hL[i]) : i in [1..#QQs]]);
		        end for;
			if #exponents eq 0 then 
		    		B:=B join primeset(Lxy);
			    else 
	         		B:=B join {p : p in exponents | Lxy mod p eq 0};		    
	      	        end if;
  	  	end if;  
	end for;
else
	for x,y in [0..q-1] do
		if [x,y] ne [0,0] and x le y and (x+y) mod q ne 0 then
			C:=curveC(x,y);
			tL:=tracesList(C,QQs,G);
		        Lxy:=1;
		        for u in tL do
				Lxy:=Lxy*Gcd([Integers()!AbsoluteNorm(KtoLL(u[i]^2) - LL!hL[i]^2) : i in [1..#QQs]]);
		        end for;
			if #exponents eq 0 then 
		    		B:=B join primeset(Lxy);
			    else 
	         		B:=B join {p : p in exponents | Lxy mod p eq 0};		    
	      	        end if;
  	  	end if;  
	end for;
end if;

if bolq then
	B:=B join {q};
	return B, false;
else 
	if #B eq 0 then
		return B, true;
	else
		return B, false;
	end if;
end if;
end function;


function RefinedEliminationForm(q,QQs,bolMq,f,twist,LL,curveC,p,factP,G,KtoLL);
// q is a rational prime not in {2,3,7} and QQs is a subset of primes in K above q
// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
// twist should be the quadratic character of K which fixes L = Cyclotomic(7)
// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f. 
// LL can be given as a relative extension
// KtoLL should be a field inclusion of K into LL
// factP should be the list of primes ideals in LL above p to eliminate
// bolMq should be true if the primes in QQs split in M/K where M = K(\sqrt{-1})
// Note that M/Q is Galois and so the primes in QQs will behave the same way in each of these extensions, because they are all above the same rational prime q
// curveC should be the Frey hyperelliptic curve FreyC



afQ:=[HeckeEigenvalue(f,Q)*twist(Q) : Q in QQs];

ResFields:=[<QQ,toQQ> where QQ,toQQ := ResidueClassField(I) : I in factP];
zeroes:=[*[res[2](0) : j in [1..#QQs]] : res in ResFields*];
list2:=[*[res[2]((Norm(QQs[1])+1)^2 - afQ[i]^2) : i in [1..#QQs]] : res in ResFields*];

BoolBadRed:=({list2[i] eq zeroes[i] : i in [1..#ResFields]} eq {false});

BoolGoodRed:=true;

if BoolBadRed then
	if bolMq then
		for x,y in [0..q-1] do
			if [x,y] ne [0,0] and x le y and (x+y) mod q ne 0 and BoolGoodRed then
				C:=curveC(x,y);
				tL:=tracesList(C,QQs,G);
			        for t in tL do
		     			 list:=[*[res[2](afQ[i] - KtoLL(t[i]))  : i in [1..#QQs]]: res in ResFields*];
		     			 if not ({list[i] eq zeroes[i] : i in [1..#ResFields]} eq {false}) then 
		     			 	BoolGoodRed:=false;
		      				break;
		      			end if;	
		     		end for;	 
		      	end if;  
		end for;
	else
		for x,y in [0..q-1] do
			if [x,y] ne [0,0] and x le y and (x+y) mod q ne 0 and BoolGoodRed then
				C:=curveC(x,y);
				tL:=tracesList(C,QQs,G);
				for t in tL do
					list:=[*[res[2](afQ[i]^2 - KtoLL(t[i])^2)  : i in [1..#QQs]]: res in ResFields*];
					if not ({list[i] eq zeroes[i] : i in [1..#ResFields]} eq {false}) then 
						BoolGoodRed:=false;      				
						break;
					end if;
				end for;
			end if;		
		end for;	 
	end if;  
end if;

if BoolBadRed eq false then 
	print "form not eliminated for p =", p;
	return false;
else
	if BoolGoodRed then 
	 	print "form eliminated for p =", p;
		return true;	
	else
		print "form not eliminated for p =", p;
		return false;
	end if;	
end if;
end function;



print "*******************************************";
print "* Using the curve E, we show that either  *";
print "* (1) 7 does not divide a+b and 4|ab, or  *";
print "* (2) 7 divides a+b and (2||ab or 4|a+b). *";
print "*******************************************";


// Eliminating newforms
print "Eliminating forms at level 2^2*7^2 = 196";
BoundQ(196);
print "Only form no 2 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,0) :";
fE:=Newform(FreyE(1,0));
forms:=Newforms(CuspidalSubspace(ModularForms(196,2)));
for i in [1..#forms] do
	f:=forms[i,1];
	print Coefficient(fE,3)-Coefficient(f,3);
end for;
print "Done !";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "Eliminating forms at level 2^3*7^2 = 392";
BoundQ(392);

print "Only form no 1 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,-1) :";
fE:=Newform(FreyE(1,-1));
forms:=Newforms(CuspidalSubspace(ModularForms(392,2)));
for i in [1..#forms] do
	f:=forms[i,1];
	print Coefficient(fE,3)-Coefficient(f,3);
end for;

print "";
print "********************************************************";
print "* We have proved that we are in Case (1) or (2) above. *";
print "********************************************************";
print "";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();





print "";
print "**************************************************";
print "* Using the curve F, we rule out case (1) above. *";
print "**************************************************";
print "";

N:=I2^3*I3;
print "Computing forms at level I2^3*I3...";
forms:=Eigenforms(NewSubspace(HilbertCuspForms(K,N)));
print "Done !";
print "There are ", #forms, "newforms";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";

print "We first perform standard elimination at level I2^3*I3 using primes q = 5, 13, 29 and 41 and the Frey curve twisted by -7 :";
Bound(forms,FreyF,-7,[5,13,29,41]);

print "";
print "The prime p = 5 survives for the form no 24 ; we discard it using refined elimination with q = 13 :";

print "";
print "++++++++++++++++++++++";
print "Performing refined elimination for the form no 24 with q = 13";
refined_Bound(forms[24],FreyF,-7,13,5);


print "";
print "****************************";
print "* Case (1) is eliminated ! *";
print "****************************";
print "";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "*******************************************************";
print "* Using the curve F, we rule out case (2) when 4|a+b. *";
print "*******************************************************";
print "";


N:=I2*I3*I7;
print "Computing forms at level I2*I3*I7...";
forms:=Eigenforms(NewSubspace(HilbertCuspForms(K,N)));
print "Done !";
print "There are ", #forms, "newforms";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";


print "We first perform standard elimination at level I2*I3*I7 using primes q = 5, 13, 29 and 41 and the Frey curve not twisted :";
Bound(forms,FreyF,1,[5,13,29,41]);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";

print "";
print "The primes p = 5, 13 survive for the form no 3 ; we discard p = 5 using refined elimination with q = 29 :";

print "";
print "++++++++++++++++++++++";
refined_Bound(forms[3],FreyF,1,29,5);




print "For each form f at level I2*I3*I7, we compute Norm(a_Q(f)-(Norm(Q)+1)) mod 13 for any of the three prime ideals Q above 29 in K :";
print "";
Q29:=Factorisation(29*OK)[1,1];
for i in [1..#forms] do
	f:=forms[i];
	print "Form no",i,": Norm(a_Q(f)-(Norm(Q)+1)) mod 13 =",Integers()!Norm(HeckeEigenvalue(f,Q29)-(Norm(Q29)+1)) mod 13;
end for;
print "";
print "Hence form no 3 is the *unique* form with reducible mod 13 representation whose existence is predicted by Martin's result.";
F:=CoefficientField(forms[3]);
print "It has exactly",#Factorisation(13*Integers(F)),"prime ideal above 13 in its coefficient field.";

print "";
print "***************************************";
print "* Case (2) when 4|a+b is eliminated ! *";
print "***************************************";
print "";

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();




print "";
print "************************************************************";
print "* Using the curve C, we rule out case (2) when ab is even. *";
print "************************************************************";
print "";


print "Since 7 divides a+b, we know that our Frey representation arises after twisting by the mod 7 cyclotomic character (which is quadratic when restricted to K) from a form of level I2^2*I3*I7.";

N:=I2^2*I3*I7;
print "Computing forms in level I2^2*I3*I7..";
forms:=Eigenforms(NewSubspace(HilbertCuspForms(K,N)));
print "..done.";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";


// We test which forms have coefficient field containing K
print "Eliminating forms by checking whether K is included in the field of coefficients..";
degForms:=[];
index:=[];
for i in [1..#forms] do
	f:=forms[i];
	F:=BaseField(f);
	degF:=Degree(F);
	bolF:=false;
	if degF mod 3 eq 0 then 
		subsDeg3:=Subfields(F,3);
		for fld in subsDeg3 do
			if IsIsomorphic(K,fld[1]) then bolF:=true; end if;
		end for;
	end if;
	if bolF then 
		Append(~index,i); 
		Append(~degForms,degF);
	end if;
end for;
print "done.";
print "";
print "Only the forms no",index,"have coefficient field containing K";


print "";
print "We finally eliminate each of these forms in turn:";

print "";
print "Eliminating form 9..";
f:=forms[9];
Kf:=BaseField(f);
_,KtoKf:=IsSubfield(K,Kf);
Bf5:=BoundForm(5,[5*OK],bolM5,f,twistL,Kf,FreyC,{},G,KtoKf);
Bf5:={x : x in Bf5 | x notin {1,2,3,7}};
Bf13:=BoundForm(13,[I13a,I13b],bolM13,f,twistL,Kf,FreyC,Bf5,G,KtoKf);
if #Bf13 eq 0 then 
	print "Eliminated form 9";
else	
  	print "Form 9 not eliminated for exponents", Bf13;
end if;  	
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "Eliminating form 10..";
f:=forms[10];
Kf:=BaseField(f);
_,KtoKf:=IsSubfield(K,Kf);
Bf13a:=BoundForm(13,[I13a],bolM13,f,twistL,Kf,FreyC,{},G,KtoKf);
Bf13a:={x : x in Bf13a | x notin {1,2,3,7}};
Bf11:=BoundForm(11,[11*OK],bolM11,f,twistL,Kf,FreyC,Bf13a,G,KtoKf);
if #Bf11 eq 0 then 
	print "Eliminated form 10";
else	
  	print "Form 10 not eliminated for exponents", Bf11;
end if; 
assert #Bf11 eq 1;
p:=Rep(Bf11); 
print "We use refined elimination with auxiliary prime q = 29 to deal with p =",p;
factP:=[I[1] : I in Factorisation(p*Integers(Kf))];
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
_:=RefinedEliminationForm(29,[I29a,I29b,I29c],bolM29,f,twistL,Kf,FreyC,p,factP,G,KtoKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";





print "";
for i in [15,17,18] do 
	print "";
	print "Eliminating form number",i;
	f:=forms[i];
	Kf:=BaseField(f);
	_,KtoKf:=IsSubfield(K,Kf);
	Bf5:=BoundForm(5,[5*OK],bolM5,f,twistL,Kf,FreyC,{},G,KtoKf);
	Bf5:={x : x in Bf5 | x notin {1,2,3,7}};
	Bf13a:=BoundForm(13,[I13a],bolM13,f,twistL,Kf,FreyC,Bf5,G,KtoKf);
	if #Bf13a eq 0 then 
  		print "Eliminated form i =", i;
  	else	
	  	print "Form i =", i, " not eliminated for exponents", Bf13a;
	end if;  	
  	print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
end for;


print "";
print "Eliminating form 19..";
f:=forms[19];
Kf:=BaseField(f);
_,KtoKf:=IsSubfield(K,Kf);
Bf5:=BoundForm(5,[5*OK],bolM5,f,twistL,Kf,FreyC,{},G,KtoKf);
Bf5:={x : x in Bf5 | x notin {1,2,3,7}};
Bf13a:=BoundForm(13,[I13a],bolM13,f,twistL,Kf,FreyC,Bf5,G,KtoKf);
Bf11:=BoundForm(11,[11*OK],bolM11,f,twistL,Kf,FreyC,Bf13a,G,KtoKf);
if #Bf11 eq 0 then 
	print "Eliminated form 19.";
else	
  	print "Form 19 not eliminated for exponents", Bf11;
end if;  	
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";
print "We have eliminated all the forms.";
print "";

print "";
print "********************************************************";
print "* The main theorem is proved using curves E, F and C ! *";
print "********************************************************";
print "";




