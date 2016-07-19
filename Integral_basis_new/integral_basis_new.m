Attach("/Users/JB/Mathematik/Programming/Magma/Diss/Helpfunctions/Helpfunctions.m");
Attach("/Users/JB/Mathematik/Programming/Magma/Diss/+IdealsFF/+IdealsFF.m");



Cpk := function(p,k)

Fqt:=Parent(p);	t:=Fqt.1;

KxT<x> := PolynomialRing(Fqt);

f:=((x^6+4*p*x^3+3*p^2*x^2+4*p^2)^2+p^6)^3+p^k;

while not IsIrreducible(f) do

	k:=k-1;
	f:=((x^6+4*p*x^3+3*p^2*x^2+4*p^2)^2+p^6)^3+p^k;
end while;

return FunctionField(f);

end function;


///////////////////////////////////////////////////
///////////////////////////////////////////////////
//			Example 1
///////////////////////////////////////////////////
///////////////////////////////////////////////////
/*

k := FiniteField(7);

A<t> := PolynomialRing(k);

p := t^3+2;		// t^3 + 4*t + 4;//RandomPrimePolynomial(A,3);

F := Cpk(p,23);
*/




Ampnk := function(m,p,n,k)

Fqt:=Parent(p);

KxT<x> := PolynomialRing(Fqt);

f:=	&*[(x+2*j)^n+2*p^k:j in [0..m-1]]+2*p^(m*n*k);
print"f",f;
return FunctionField(f);

end function;




///////////////////////////////////////////////////
///////////////////////////////////////////////////
//			Example 1
///////////////////////////////////////////////////
///////////////////////////////////////////////////


//k := GF(3);

//A<t> := PolynomialRing(k);

//p := t^2+1;		// t^3 + 4*t + 4;//RandomPrimePolynomial(A,3);

//m := 4;

//n := Integers()!(64/m);
//F := Ampnk(m,p,n,3);	







////////////////////////////////

///////////////

function p_Length(z,p)

F := Parent(z); A := Parent(p);
Montes(F,p);
Vals := [];

for P in F`PrimeIdeals[p] do
	Append(~Vals,PValuation(z,P)/P`e);
end for;

return Vals;

end function;



///////////////

function Reduce(z,P,val)

F_P := P`Type[#P`Type]`Fq;	Fp := CoefficientRing(P`Type[1]`psi);
P_val := PValuation(z,P);
if P_val/P`e gt val then
	z_mod_P := F_P!0;
else
	z_mod_P := Reduction(z,P,P_val+1)[P_val+1];
end if;
return Eltseq(z_mod_P,Fp),P_val;

end function;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


function ReductionAlgorithm(Elt_list,Elt_P_mod_list,p)

F := Parent(Elt_list[1]); k := ConstantField(F);

length := [p_Length(i,p):i in Elt_list];
tmp := Floor(Min(length[1]));
Elt_list[1] := Elt_list[1]/p^tmp;	length[1] := [i-tmp:i in length[1]];
not_reduced := true;

while not_reduced do
	min_lengthes := [Min(j):j in length];
	max_val :=min_lengthes[1];
	longest := Elt_list[1];
	elts_of_same_mod_length := [];
	positions_of_elts :=[];
	for j in [1..#min_lengthes] do
		i := min_lengthes[j];
		if i eq max_val then
			Append(~elts_of_same_mod_length,Elt_list[j]);
			Append(~positions_of_elts,j);
		end if;
	end for;		
	

	Class_of_primes := [];
	for P in F`PrimeIdeals[p] do
		if P`e mod Denominator(max_val) eq 0 then
			Append(~Class_of_primes,P);
		end if;
	end for;

	if #elts_of_same_mod_length gt 1 then
		
		//Will work so far only for cases where the residue class field is finite!
		_,ind := Max([i`f:i in Class_of_primes]);
		F_P := 	Class_of_primes[ind]`Type[#Class_of_primes[ind]`Type]`Fq;
		Fp:= CoefficientRing(Class_of_primes[ind]`Type[1]`psi); 
		phi := Class_of_primes[ind]`Type[1]`Redmap^-1;

		Relation_matrix := [ &cat[Reduce(elts_of_same_mod_length[1],P,max_val):P in Class_of_primes]];
		
		for i in [2..#elts_of_same_mod_length] do
			pos := positions_of_elts[i];
			Append(~Relation_matrix, Elt_P_mod_list[pos-1]);		//[Embed(F_P,P`Type[#P`Type]`Fq,Reduce(i,P)):P in Class_of_primes]
		end for;
		M_rel := Matrix(Relation_matrix);
		E,R := EchelonForm(M_rel);			m := Ncols(R);	
		print"what",M_rel,E,R;
		print"data",elts_of_same_mod_length;
	
		r := Rank(E);
				print"r",r;
		if r lt Nrows(E) then //and forall{i:i in [1..m]|R[m,i] in k}
			//Now we apply reduction step
			check := 0;
			for ll in [r+1..m] do
			
				if not R[ll,1] eq 0 and forall{i:i in [1..m]|R[ll,i] in Fp} and check eq 0 then
				
					new_element:=elts_of_same_mod_length[1]+
								&+[phi(R[ll,j]/R[ll,1])*elts_of_same_mod_length[j]:j in [2..m]];
					tmp := p_Length(new_element,p);
					length[1] := [i-Floor(Min(tmp)):i in tmp];
					Elt_list[1] := new_element/p^Floor(Min(tmp));		
					check +:=1;
					print"tut sich was?",Elt_list[1];
				end if;
				
				if ll eq m and check eq 0 then
					not_reduced := false;
				end if;
			end for;
			
			
		
		else
			not_reduced := false;
		end if;
	else
		not_reduced := false;
	end if;


end while;
//print"watn", &cat [&cat[Reduce(Elt_list[1],P):P in Class_of_primes]], Elt_P_mod_list;
Elt_P_mod_list := [&cat [&cat[Reduce(Elt_list[1],P,Min(length[1])):P in Class_of_primes]]] cat Elt_P_mod_list;

return  Elt_list,Elt_P_mod_list,Min(length[1]);

end function;





///////////////

function p_integral_basis(F,p)

Montes(F,p);

Elt_list := [1];
F_p := 	CoefficientRing(F`PrimeIdeals[p,1]`Type[1]`psi);


Elt_P_mod_list := [&cat[Eltseq(i`Type[#i`Type]`Fq!1,F_p):i in F`PrimeIdeals[p]]];


for i in [1..Degree(F)-1] do
print"asdasd",i;
	Elt_list,Elt_P_mod_list :=  ReductionAlgorithm([F.1^i] cat Elt_list,Elt_P_mod_list,p);
	
end for;


return Reverse(Elt_list);

end function;





