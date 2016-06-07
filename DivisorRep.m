freeze;


import "+Divisors.m";

AddAttribute(FldFun,"referece_divisor");
AddAttribute(FldFun,"range");
AddAttribute(FldFun,"referece_basis");
AddAttribute(FldFun,"Minus_diff_ideal");
AddAttribute(FldFun,"Minus_diff_basis");
AddAttribute(FldFun,"Different_Divisor");
AddAttribute(FldFun,"Matrix_max_order");
AddAttribute(FldFun,"zero_divisor");

//Record for new divisor representation
				
New_divisor_rep:=recformat<
red_basis: SeqEnum,
succ_min: SeqEnum,
Iinf:Rec,
d: RngIntElt,
k: RngIntElt,
n_w: RngIntElt,
a: FldFunElt
>;




////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic Count_nonzero_rows(T::ModMatRngElt)->RngIntElt
{}

n := Ncols(T);	m := 0; zero_row := Rows(ZeroMatrix(CoefficientRing(T),1,n))[1];
for i in Rows(T) do

	if not i eq zero_row then 
		m := m+1;
	end if;

end for;
return m;
end intrinsic;

/////////////////////////////////////////

intrinsic Count_nonzero_rows(T::AlgMatElt)->RngIntElt
{}

n := Ncols(T);	m := 0; zero_row := Rows(ZeroMatrix(CoefficientRing(T),1,n))[1];
for i in Rows(T) do

	if not i eq zero_row then 
		m := m+1;
	end if;

end for;
return m;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic ExtendedReductionAlgorithm(T::ModMatRngElt)->AlgMatElt
{Let the rows of T generate a lattice L in K^n, Output: T, whose rows form a reduced basis of L}


NumberRedSteps:=0;
lc := LCM([Denominator(i):i in Eltseq(T)]);
K := BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n := Ncols(T);	m := Nrows(T);	T := ChangeRing(lc*T,kt);
s:=1;

if m eq 1 then return T,Maximum([Degree(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p := [];
Sort(~VectorNorm,~p);
T := Matrix([T[i]:i in Eltseq(p)]);

while s lt m do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..n] do
			if not T[i,j] eq 0 and Degree(T[i,j]) eq VectorNorm[i] then			
				M[i,j]:=LeadingCoefficient(T[i,j]);				
			end if; 				
		end for;
	end for;
	Mprime,P:=EchelonForm(M);
	s:=Rank(Mprime);
	NumberRedSteps:=NumberRedSteps+m-s;

	if s lt m then
			//Transform P in a shape to read out all relations
		Su:=SubmatrixRange(P,s+1,1,m,m);
		P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
		for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			for i in [1..u-1] do
				if not P[j,i] eq 0 then								
				AddRow(~T,P[j,i]/P[j,u]*t^(VectorNorm[u]-VectorNorm[i]),i,u);
				end if;
			end for;
			VectorNorm[u]:=Maximum([Degree(l):l in ElementToSequence(T[u])]);
		end for;
		p:=[];
		Sort(~VectorNorm,~p);
		T:=Matrix([T[i]:i in Eltseq(p)]);
		m := Count_nonzero_rows(T);
	end if;
end while;	
print"NumberRedSteps",NumberRedSteps;
tmp := Rows(T);	Sort(~tmp,~p);
T := Matrix(Reverse(tmp)); VectorNorm := Reverse([VectorNorm[i]:i in  Eltseq(p)]);
tmp := [i-Degree(lc):i in VectorNorm];
return (1/K!lc)*ChangeRing(Submatrix(T,1,1,m,n),K),[tmp[i]: i in [1..m]],NumberRedSteps;

end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



intrinsic ExtendedReductionAlgorithm(T::AlgMatElt)->AlgMatElt
{Let the rows of T generate a lattice L in K^n, Output: T, whose rows form a reduced basis of L}

NumberRedSteps:=0;
lc := LCM([Denominator(i):i in Eltseq(T)]);
K := BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n := Ncols(T);m:=Nrows(T);
T := ChangeRing(lc*T,kt);

s:=1;

if m eq 1 then return T,Maximum([Degree(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p := [];
Sort(~VectorNorm,~p);
T := Matrix([T[i]:i in Eltseq(p)]);

while s lt m do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..n] do
			if not T[i,j] eq 0 and Degree(T[i,j]) eq VectorNorm[i] then			
				M[i,j]:=LeadingCoefficient(T[i,j]);				
			end if; 				
		end for;
	end for;
	Mprime,P:=EchelonForm(M);
	s:=Rank(Mprime);
	NumberRedSteps:=NumberRedSteps+m-s;

	if s lt m then
			//Transform P in a shape to read out all relations
		Su:=SubmatrixRange(P,s+1,1,m,m);
		P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
		for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			for i in [1..u-1] do
				if not P[j,i] eq 0 then								
				AddRow(~T,P[j,i]/P[j,u]*t^(VectorNorm[u]-VectorNorm[i]),i,u);
				end if;
			end for;
			VectorNorm[u]:=Maximum([Degree(l):l in ElementToSequence(T[u])]);
		end for;
		p:=[];
		Sort(~VectorNorm,~p);
		T:=Matrix([T[i]:i in Eltseq(p)]);
		m := Count_nonzero_rows(T);
	end if;
end while;	
print"NumberRedSteps",NumberRedSteps;
tmp := Rows(T);
Sort(~tmp,~p);
T := Matrix(Reverse(tmp)); VectorNorm := Reverse([VectorNorm[i]:i in  Eltseq(p)]);
tmp := [i-Degree(lc):i in VectorNorm];
return (1/K!lc)*ChangeRing(Submatrix(T,1,1,m,n),K),[tmp[i]: i in [1..m]],NumberRedSteps;

end intrinsic;




////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Basis_reduction(B::SeqEnum,Iinf::Rec)->SeqEnum
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one}


//if #B le 1 then return B,[1]; end if;
F := Parent(B[1]);	n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;

//////////////////////////Producing bases/////////////////////////
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M1 := Matrix(K,n,&cat [Eltseq(i):i in B]);
M2 := Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
Mhelp := M2^(-1); T := M1*Mhelp;
RedT,SuccMin,NumberOfRedSteps:=ExtendedReductionAlgorithm(T);

if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([Degree(j):j in i]):i in RowSequence(T)];
	redbasis:=[i:i in B];
	SuccMin:=[i+infex:i in SuccMin];
	
else	
	redbasis:=[&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..Nrows(RedT)]];
	SuccMin:=[i+infex:i in SuccMin];

end if;

return redbasis,SuccMin;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



intrinsic Basis_reduction(B::SeqEnum,Bprime::SeqEnum,M2::AlgMatElt,infex::RngIntElt)->SeqEnum
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one}

//if #B le 1 then return B,[1]; end if;
F := Parent(B[1]);	n:=Degree(F);
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;
//////////////////////////Producing bases/////////////////////////
M1 := Matrix(K,n,&cat [Eltseq(i):i in B]);
Mhelp := M2^(-1); T := M1*Mhelp;
RedT,SuccMin,NumberOfRedSteps:=ExtendedReductionAlgorithm(T);

if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([Degree(j):j in i]):i in RowSequence(T)];
	redbasis:=[i:i in B];
	SuccMin:=[i+infex:i in SuccMin];
	
else	
	redbasis:=[&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..Nrows(RedT)]];
	SuccMin:=[i+infex:i in SuccMin];

end if;

return redbasis,SuccMin;
end intrinsic;

//############################

intrinsic Old_Rep(E::Rec)->Rec
{}

basis := E`red_basis;	F := Parent(basis[1]);  
I := ideal(F,basis);	I_inf:=E`Iinf;
D := Divisor(I)+Divisor(I_inf);


return D+E`k*F`referece_divisor+Divisor(E`a),D,-1*(D-F`range*F`referece_divisor);
end intrinsic;

//############################

intrinsic New_representation(E::Rec)->Rec
{Takes a divisor in the free representation and outputs its 'Mekdisi' representation
	with repsect to a reference divisor B}

require IsDivisor(E): "Argument should be a divisor in free representation";

F := E`FiniteIdeal`Parent;	Base := F`referece_divisor;
e := Degree(E);	b :=	Degree(Base);	g := GENUS(F);
m := Ceiling((g+e)/b);	tmp:=m*Base-E; RRSpace2(~tmp);
_,ind := Minimum(tmp`ApproximatedSuccessiveMinima);	f :=tmp`SRedBasis[ind];
D := Divisor(f)+m*Base-E;	

n := F`range;
k := m-n;
//k_1 := Floor((e-2*g)/b);
tmp:= n*Base-D; RRSpace(~tmp); succmin := tmp`ApproximatedSuccessiveMinima;

return rec<New_divisor_rep|red_basis := tmp`SRedBasis,	succ_min := succmin,
					Iinf := tmp`InfiniteIdeal,d := Degree(D), k := k,	n_w := n,	a := f>,D,tmp;

end intrinsic;


//############################

intrinsic degree(E::Rec)->RngIntElt
{}

F := Parent(E`red_basis[1]);	b := Degree(F`referece_divisor); 	

return (F`range+E`k)*b-E`d;

end intrinsic;



//############################


intrinsic ini_representation(~F::FldFun,B::Rec,n::RngIntElt)
{}
F`range := n;
F`referece_divisor := B;	kt := PolynomialRing(ConstantField(F));
ktx := PolynomialRing(kt);
F`range := n;	Div :=	n*B;
RRSpace(~Div);	F`referece_basis := Div`SRedBasis;
Minus_diff := -1*Different_Divisor(F);
F`Minus_diff_ideal := Minus_diff`InfiniteIdeal;
F`Minus_diff_basis := SemiReducedBasis(Minus_diff);

Bfin,finitefac:=IdealBase(Div`FiniteIdeal);
Bfin := [i*finitefac:i in Bfin];
F`Matrix_max_order:= Matrix([Eltseq(i):i in Bfin]);

F`zero_divisor := New_representation(Divisor(F!1));

end intrinsic;

//############################

intrinsic Complementary_basis(basis::SeqEnum)->SeqEnum
{Computes orthogonal basis w.r.t to the trace}
//print"comple_basis_1",basis;
F := Parent(basis[1]); A := PolynomialRing(ConstantField(F));
basis := [b: b in basis];	
//print"comple_basis_2";
M_temp := Matrix(BaseField(F),Degree(F),[Trace(b_i*b_j): b_i in basis,b_j in basis]);
//print"comple_basis_2.1";
M := M_temp^-1;
//print"comple_basis_3";
L := Rows(M);

basis_com := [];
//print"comple_basis_4";
for elt in L do
	tmp := &+[elt[i]*basis[i]:i in [1..Degree(F)]];
	Append(~basis_com,tmp);
end for;
//print"comple_basis_5";
return basis_com;

end intrinsic;

//############################

intrinsic BasisCheck(B1::SeqEnum,B2::SeqEnum)->SeqEnum
{}

F := Parent(B1[1]);
A := PolynomialRing(ConstantField(F));
M1 := Matrix([Eltseq(i):i in B1]);
M2 := Matrix([Eltseq(i):i in B2]);
M := M1*M2^-1;

return Determinant(M),Max([Degree(A!Denominator(i)): i in  &cat[Eltseq(i):i in Rows(M)]]);

end intrinsic;

//############################

intrinsic Minus_D(D_basis::SeqEnum,I_D_inf::Rec,D_deg::RngIntElt:early_exit := false)->SeqEnum
{Takes a reduced basis of D and determiens a reduced basis of -D; if fast_break then 
	outputs a in L(-D)}

F := Parent(D_basis[1]); deg_F := Degree(F);	
Diff_D_basis := Complementary_basis(D_basis);
t := PolynomialRing(ConstantField(F)).1;
Montes(InfinityRepresentation(F),t);	Binf,_,_,_,_,infex := pBasis(I_D_inf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
dim_D := D_deg-GENUS(F)+1;
dim := 0;	products := []; basis := [];
for b in Diff_D_basis do
	for c in F`Minus_diff_basis do
		prod := b*c;	
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);

			if early_exit and succmin[1] le 0 then
				return basis,succmin;
			end if;
//			print"-&+succmin+deg_F",succmin;
			if -&+succmin+deg_F eq dim_D then
				print"early exit";	
				return basis,succmin;
			end if;	
		end if;
	end for;
end for;

end intrinsic;



//############################

intrinsic Minus_D_simple_a(D_basis::SeqEnum,I_D_inf::Rec,D_deg::RngIntElt:early_exit := false)->SeqEnum
{Takes a reduced basis of D and determiens a reduced basis of -D; if fast_break then 
	outputs a in L(-D)}


F := Parent(D_basis[1]); deg_F := Degree(F);	
Diff_D_basis := Complementary_basis(D_basis);
t := PolynomialRing(ConstantField(F)).1;
Montes(InfinityRepresentation(F),t);	Binf,_,_,_,_,infex := pBasis(I_D_inf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
dim_D := D_deg-GENUS(F)+1;
dim := 0;	products := []; basis := [];
for b in Diff_D_basis do
	for c in F`Minus_diff_basis do
		prod := b*c;	
		
		if not prod in products then
			Append(~products,prod);

			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);

			
			if early_exit and succmin[1] le 0 then
				return basis,succmin;
			end if;
			//print"succmin",succmin,-&+succmin+deg_F;	
			
			if -&+succmin+deg_F eq dim_D then
				print"early exit";	
//				print"\n\n\n basis",basis;		
				return basis,succmin;
				
			end if;	

		end if;
	end for;
end for;

end intrinsic;


//############################


intrinsic Complementary_basis_eff(basis::SeqEnum)->SeqEnum
{Computes orthogonal basis w.r.t to the trace}
print"comple_basis_1",basis;
F := Parent(basis[1]); A := PolynomialRing(ConstantField(F));
basis := ToHermiteBasis(basis);	
//print"comple_basis_2";
M_temp := Matrix(BaseField(F),Degree(F),[Trace(b_i*b_j): b_i in basis,b_j in basis]);
//print"comple_basis_2.1";
M := M_temp^-1;
//print"comple_basis_3";
L := Rows(M);

basis_com := [];
//print"comple_basis_4";
for elt in L do
	tmp := &+[elt[i]*basis[i]:i in [1..Degree(F)]];
	Append(~basis_com,tmp);
end for;
//print"comple_basis_5";
return basis_com;

end intrinsic;

//############################

intrinsic Minus_D_eff(D_basis::SeqEnum,I_D_inf::Rec,D_deg::RngIntElt:early_exit := false)->SeqEnum
{Takes a reduced basis of D and determiens a reduced basis of -D; if fast_break then 
	outputs a in L(-D)}

early_exit := true;
F := Parent(D_basis[1]); deg_F := Degree(F);	
//print"Minus_1";
Diff_D_basis := Complementary_basis_eff(D_basis);
//print"Minus_2";
t := PolynomialRing(ConstantField(F)).1;
Montes(InfinityRepresentation(F),t);	Binf,_,_,_,_,infex := pBasis(I_D_inf,t);
//print"Minus_3";
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
dim_D := D_deg-GENUS(F)+1;

dim := 0;	products := []; basis := [];


for b in Diff_D_basis do


	for c in F`Minus_diff_basis do
		prod := b*c;	
		
		if not prod in products then
			Append(~products,prod);

			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
print"daten",succmin;
			
			if early_exit and succmin[1] le 0 then
				return basis,succmin;
			end if;
			//print"succmin",succmin,-&+succmin+deg_F;	
			
			if -&+succmin+deg_F eq dim_D then
				print"early exit";	
						
				return basis,succmin;
				
			end if;	

		end if;
	end for;
end for;
print"Minus_4";
end intrinsic;



//############################

intrinsic Add_new(D::Rec,E::Rec:DivClass := true)->Rec
{Takes divisors D,E in new representation w.r.t. the reference divisor B and computes D+E
	in new representation w.r.t B}

F := Parent(E`red_basis[1]);	F2 := (D`Iinf)`Parent;
d := D`d;	e := E`d;	b := Degree(F`referece_divisor);	
n := F`range; g := GENUS(F);	deg_F := Degree(F);
dim_sum := 2*n*b-d-e+1-g;	Iinf := D`Iinf*E`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
Iinf := Iinf*((n*F`referece_divisor)`InfiniteIdeal)^-1;
//				PutInZ(Iinf);

rhs := n*b-2*GENUS(F);	
require d le rhs and e le rhs: "Degree of D and/or E too large";

Basis1 := D`red_basis;	Basis2 := E`red_basis;
dim := 0;	products := []; basis := [];


for b1 in Basis1 do
	for b2 in Basis2 do
		prod := b1*b2;	
		
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
		
			number_of_negative_entries := 0;
			for i in succmin do
				if i le 0 then 
					number_of_negative_entries := number_of_negative_entries+1;
				end if;
			end for;
			if -&+succmin+number_of_negative_entries eq dim_sum then
				print"early exit";	

				if DivClass then
					a := D`a*E`a;
				else
					a := F!1;	
				end if;
				sum := rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], 
								 Iinf := Iinf, d := d+e, k :=D`k+E`k+n,	a := a>;	
				tmp := sum;				 
				if sum`d gt n*b-2*g then
					//print"Into Degree reduction";
				//	print"hier???",basis;
					sum := Degree_reduction(sum:DivClass := DivClass);
				end if;				 
				return sum,tmp;
			end if;	

		end if;
	end for;
end for;

print"might be wrong",-&+succmin+deg_F , dim_sum;
sum:= rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], Iinf := Iinf,
											d := d+e, k :=D`k+E`k+n,	a := a>;

											
if sum`d gt n*b-2*g then
	sum := Degree_reduction(sum);
end if;				 
return sum;
											

end intrinsic;


//############################

intrinsic Add_new_2(D::Rec,E::Rec:DivClass := true)->Rec
{Takes divisors D,E in new representation w.r.t. the reference divisor B and computes D+E
	in new representation w.r.t B, using Degree_reduction_2}

F := Parent(E`red_basis[1]);	F2 := (D`Iinf)`Parent;
d := D`d;	e := E`d;	b := Degree(F`referece_divisor);	
n := F`range; g := GENUS(F);	deg_F := Degree(F);
dim_sum := 2*n*b-d-e+1-g;	Iinf := D`Iinf*E`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
Iinf := Iinf*((n*F`referece_divisor)`InfiniteIdeal)^-1;
//				PutInZ(Iinf);

rhs := n*b-2*GENUS(F);	
require d le rhs and e le rhs: "Degree of D and/or E too large";

Basis1 := D`red_basis;	Basis2 := E`red_basis;
dim := 0;	products := []; basis := [];


for b1 in Basis1 do
	for b2 in Basis2 do
		prod := b1*b2;	
		
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
		
			number_of_negative_entries := 0;
			for i in succmin do
				if i le 0 then 
					number_of_negative_entries := number_of_negative_entries+1;
				end if;
			end for;
			if -&+succmin+number_of_negative_entries eq dim_sum then
				print"early exit";	

				if DivClass then
					a := D`a*E`a;
				else
					a := F!1;	
				end if;
				sum := rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], 
								 Iinf := Iinf, d := d+e, k :=D`k+E`k+n,	a := a>;	
				tmp := sum;				 
				if sum`d gt n*b-2*g then
					//print"Into Degree reduction";
				//	print"hier???",basis;
					sum := Degree_reduction_2(sum:DivClass := DivClass);
				end if;				 
				return sum,tmp;
			end if;	

		end if;
	end for;
end for;

print"might be wrong",-&+succmin+deg_F , dim_sum;
sum:= rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], Iinf := Iinf,
											d := d+e, k :=D`k+E`k+n,	a := a>;

											
if sum`d gt n*b-2*g then
	sum := Degree_reduction(sum);
end if;				 
return sum;
											

end intrinsic;


//############################

intrinsic Add_new_3(D::Rec,E::Rec:DivClass := true)->Rec
{Takes divisors D,E in new representation w.r.t. the reference divisor B and computes D+E
	in new representation w.r.t B, using Degree_reduction_2}

F := Parent(E`red_basis[1]);	F2 := (D`Iinf)`Parent;
d := D`d;	e := E`d;	b := Degree(F`referece_divisor);	
n := F`range; g := GENUS(F);	deg_F := Degree(F);
dim_sum := 2*n*b-d-e+1-g;	Iinf := D`Iinf*E`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
Iinf := Iinf*((n*F`referece_divisor)`InfiniteIdeal)^-1;
//				PutInZ(Iinf);

rhs := n*b-2*GENUS(F);	
require d le rhs and e le rhs: "Degree of D and/or E too large";

Basis1 := D`red_basis;	Basis2 := E`red_basis;
dim := 0;	products := []; basis := [];


for b1 in Basis1 do
	for b2 in Basis2 do
		prod := b1*b2;	
		
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
		
			number_of_negative_entries := 0;
			for i in succmin do
				if i le 0 then 
					number_of_negative_entries := number_of_negative_entries+1;
				end if;
			end for;
			if -&+succmin+number_of_negative_entries eq dim_sum then
				print"early exit";	

				if DivClass then
					a := D`a*E`a;
				else
					a := F!1;	
				end if;
				sum := rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], 
								 Iinf := Iinf, d := d+e, k :=D`k+E`k+n,	a := a>;	
				tmp := sum;				 
				if sum`d gt n*b-2*g then
					//print"Into Degree reduction";
				//	print"hier???",basis;
					sum := Degree_reduction_3(sum:DivClass := DivClass);
				end if;				 
				return sum,tmp;
			end if;	

		end if;
	end for;
end for;

print"might be wrong",-&+succmin+deg_F , dim_sum;
sum:= rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], Iinf := Iinf,
											d := d+e, k :=D`k+E`k+n,	a := a>;

											
if sum`d gt n*b-2*g then
	sum := Degree_reduction_3(sum);
end if;				 
return sum;
											

end intrinsic;



//############################

intrinsic Add_new_eff(D::Rec,E::Rec)->Rec
{Takes divisors D,E in new representation w.r.t. the reference divisor B and computes D+E
	in new representation w.r.t B}

F := Parent(E`red_basis[1]);	F2 := (D`Iinf)`Parent;
d := D`d;	e := E`d;	b := Degree(F`referece_divisor);	
n := F`range; g := GENUS(F);	deg_F := Degree(F);
dim_sum := 2*n*b-d-e+1-g;	Iinf := D`Iinf*E`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
Iinf := Iinf*((n*F`referece_divisor)`InfiniteIdeal)^-1;
rhs := n*b-2*GENUS(F);	
require d le rhs and e le rhs: "Degree of D and/or E too large";

Basis1 := D`red_basis;	Basis2 := E`red_basis;
dim := 0;	products := []; basis := [];


for b1 in Basis1 do
	for b2 in Basis2 do
		prod := b1*b2;	
		
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
			//print"succmin before",succmin,-&+succmin+deg_F;
			//succmin := [i-infex:i in succmin];
		//	print"succmin",succmin,-&+succmin+deg_F;	
			number_of_negative_entries := 0;
			for i in succmin do
				if i le 0 then 
					number_of_negative_entries := number_of_negative_entries+1;
				end if;
			end for;
			if -&+succmin+number_of_negative_entries eq dim_sum then
				print"early exit";	
//				print"data:",dim_sum,succmin,basis,-&+succmin+deg_F,deg_F;
				sum := rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], 
								 Iinf := Iinf, d := d+e, k :=D`k+E`k+n >;	
				tmp := sum;				 
				if sum`d gt n*b-2*g then
					//print"Into Degree reduction";
				//	print"hier???",basis;
					sum := Degree_reduction_eff(sum);
				end if;				 
				return sum,tmp;
			end if;	

		end if;
	end for;
end for;

print"might be wrong",-&+succmin+deg_F , dim_sum;
sum:= rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], Iinf := Iinf,
											d := d+e, k :=D`k+E`k+n>;
											
if sum`d gt n*b-2*g then
	sum := Degree_reduction_eff(sum);
end if;				 
return sum;
											

end intrinsic;

//############################

intrinsic Add_new_simple_a(D::Rec,E::Rec)->Rec
{Takes divisors D,E in new representation w.r.t. the reference divisor B and computes D+E
	in new representation w.r.t B}

F := Parent(E`red_basis[1]);	F2 := (D`Iinf)`Parent;
d := D`d;	e := E`d;	b := Degree(F`referece_divisor);	
n := F`range; g := GENUS(F);	deg_F := Degree(F);
dim_sum := 2*n*b-d-e+1-g;	Iinf := D`Iinf*E`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
Iinf := Iinf*((n*F`referece_divisor)`InfiniteIdeal)^-1;
rhs := n*b-2*GENUS(F);	
require d le rhs and e le rhs: "Degree of D and/or E too large";

Basis1 := D`red_basis;	Basis2 := E`red_basis;
dim := 0;	products := []; basis := [];


for b1 in Basis1 do
	for b2 in Basis2 do
		prod := b1*b2;	
		
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
			//print"succmin before",succmin,-&+succmin+deg_F;
			//succmin := [i-infex:i in succmin];
		//	print"succmin",succmin,-&+succmin+deg_F;	
			number_of_negative_entries := 0;
			for i in succmin do
				if i le 0 then 
					number_of_negative_entries := number_of_negative_entries+1;
				end if;
			end for;
			if -&+succmin+number_of_negative_entries eq dim_sum then
				print"early exit";	
//				print"data:",dim_sum,succmin,basis,-&+succmin+deg_F,deg_F;
				sum := rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], 
								 Iinf := Iinf, d := d+e, k :=D`k+E`k+n >;	
				tmp := sum;				 
				if sum`d gt n*b-2*g then
					//print"Into Degree reduction";
				//	print"hier???",basis;
					sum := Degree_reduction_simple_a(sum);
				end if;				 
				return sum,tmp;
			end if;	

		end if;
	end for;
end for;

print"might be wrong",-&+succmin+deg_F , dim_sum;
sum:= rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], Iinf := Iinf,
											d := d+e, k :=D`k+E`k+n>;
											
if sum`d gt n*b-2*g then
	sum := Degree_reduction(sum);
end if;				 
return sum;
														

end intrinsic;

//############################

intrinsic Add_new2(D::Rec,E::Rec)->Rec
{Takes divisors D,E in new representation w.r.t. the reference divisor B and computes D+E
	in new representation w.r.t B}

F := Parent(E`red_basis[1]);	F2 := (D`Iinf)`Parent;
d := D`d;	e := E`d;	b := Degree(F`referece_divisor);	
n := F`range; g := GENUS(F);	deg_F := Degree(F);
dim_sum := 2*n*b-d-e+1-g;	Iinf := D`Iinf*E`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M2 := Matrix(BaseField(F),deg_F,&cat [Eltseq(i):i in Bprime]);
Iinf := Iinf*((n*F`referece_divisor)`InfiniteIdeal)^-1;
rhs := n*b-2*GENUS(F);	
require d le rhs and e le rhs: "Degree of D and/or E too large";

Basis1 := D`red_basis;	Basis2 := E`red_basis;
dim := 0;	products := []; basis := [];


for b1 in Basis1 do
	for b2 in Basis2 do
		prod := b1*b2;	
		
		if not prod in products then
			Append(~products,prod);
			Append(~basis,prod);
			basis, succmin := Basis_reduction(basis,Bprime,M2,infex);
			
			if -&+succmin+deg_F eq dim_sum then
				print"early exit";	
				
				sum := rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], 
								 Iinf := Iinf, d := d+e, k :=D`k+E`k+n >;	
				tmp := sum;				 
				if sum`d gt n*b-2*g then
					sum := Degree_reduction2(sum);
				end if;				 
				return sum,tmp;
			end if;	

		end if;
	end for;
end for;

print"might be wrong",-&+succmin+deg_F , dim_sum;
sum:= rec<New_divisor_rep|red_basis := basis, succ_min := [i+n:i in succmin], Iinf := Iinf,
											d := d+e, k :=D`k+E`k+n>;
											
if sum`d gt n*b-2*g then
	sum := Degree_reduction2(sum);
end if;				 
return sum;
											

end intrinsic;

//############################

intrinsic infinity_ideal(a::FldFunElt)->Rec
{}
tt := Realtime();
F := Parent(a);
//print"\n \n a",a;
fac := [];
for i in PrimesAtInfinity(F) do
	tmp := PValuation(a,i);
//	print"a-vals",tmp;
	Append(~fac,i^tmp);
end for;
//print"computes a-vals tool", Realtime()-tt;
return &*fac;
end intrinsic;

//############################


intrinsic Degree_reduction_2(D::Rec:DivClass := true)->Rec
{}

tt := Realtime();
F := Parent(D`red_basis[1]); n := F`range; B := F`referece_divisor;	
d := D`d;	b := Degree(B);		g := GENUS(F);
//require d gt n*b-2*g and d le 2*n*b-4*g: "Degree of input not in the right interval";
//print"deg_red 1";
Iinf_new := (D`Iinf)^(-1)*B`InfiniteIdeal^n;//((D`Iinf)*B`InfiniteIdeal^(-n))^(-1);
//D`Iinf corresponds to nB-D but Iinf_new corredsponds to D.

B_minus,succmin_D := Minus_D(D`red_basis,Iinf_new,d:early_exit:=false);
//print"deg_red 2";
l := Ceiling((d-n*b+2*g)/b);

_,ind := Min(succmin_D);
a := B_minus[ind];	
	
	
if a in ConstantField(F) then

	a := F!1;	
		
end if;	

	//PutInZ(a);
print"before basis 2",D`red_basis;
basis := [i*a :i in D`red_basis];
Iinf := D`Iinf*(B`InfiniteIdeal)^l*infinity_ideal(F!a); 
	print"Basis 2",basis;
//print"Degree_reduction took",Realtime()-tt;
if not DivClass then
	a := 1;
end if;
return rec<New_divisor_rep|red_basis := basis, succ_min := [i-l:i in D`succ_min], Iinf := Iinf,
											d := d-l*b, k :=D`k-l, a := D`a*a>;


end intrinsic;



//############################


intrinsic Degree_reduction_3(D::Rec:DivClass := true)->Rec
{}

F := Parent(D`red_basis[1]); n := F`range; B := F`referece_divisor;	
d := D`d;	b := Degree(B);		g := GENUS(F);
Iinf_new := (D`Iinf)^(-1)*B`InfiniteIdeal^n;//((D`Iinf)*B`InfiniteIdeal^(-n))^(-1);


B_minus,succmin_D := Minus_D(D`red_basis,Iinf_new,d:early_exit:=false);
l := Ceiling((d-n*b+2*g)/b);

_,ind := Min(succmin_D);
a := B_minus[ind];	
	
	
if a in ConstantField(F) then

	a := F!1;	
	Remove(~succmin_D,ind);	 Remove(~B_minus,ind);
	_,ind := Min(succmin_D);	a := B_minus[ind];
end if;	

basis := [i*a :i in D`red_basis];
print"Basis 3",basis;
Iinf := D`Iinf*(B`InfiniteIdeal)^l*infinity_ideal(F!a); 

if not DivClass then
	a := 1;
end if;
return rec<New_divisor_rep|red_basis := basis, succ_min := [i-l:i in D`succ_min], Iinf := Iinf,
											d := d-l*b, k :=D`k-l, a := D`a*a>;


end intrinsic;


//############################


intrinsic Degree_reduction(D::Rec:DivClass := true)->Rec
{}

PutInZ(D);
F := Parent(D`red_basis[1]); n := F`range; B := F`referece_divisor;	
d := D`d;	b := Degree(B);		g := GENUS(F);
l := Ceiling((d-n*b+2*g)/b);
Iinf_new := (D`Iinf)^(-1)*B`InfiniteIdeal^n;//((D`Iinf)*B`InfiniteIdeal^(-n))^(-1);
I_tmp := Iinf_new*(B`InfiniteIdeal)^-l;

print"Degree_re 1";
print"check ideal before",I_tmp`Factorization;	
if forall{i:i in I_tmp`Factorization|i[3]  le 0 } then  // So if D-l*B is still effective

	a := 1;
else
print"Degree_re 1.?";
	B_minus,succmin_D := Minus_D(D`red_basis,Iinf_new,d:early_exit:=false);
	_,ind := Min(succmin_D);
	a := B_minus[ind];	

end if;
	print"Basis 1 before",D`red_basis;
	print"asdas",a;
basis := [i*a :i in D`red_basis];
	print"Basis 1",basis;

print"Degree_re 2";
Iinf := D`Iinf*(B`InfiniteIdeal)^l*infinity_ideal(F!a); 
if not DivClass then	a := 1;	end if;
//if not forall{i:i in Iinf`Factorization|i[3]  le 0 } then PutInZ(D); end if;
return rec<New_divisor_rep|red_basis := basis, succ_min := [i-l:i in D`succ_min], Iinf := Iinf,
											d := d-l*b, k :=D`k-l, a := D`a*a>;


end intrinsic;

//############################


intrinsic Negative(D::Rec:DivClass := true)->Rec
{}


F := Parent(D`red_basis[1]); n := F`range; B := F`referece_divisor;	
d := D`d;	b := Degree(B);		g := GENUS(F);
//require d gt n*b-2*g and d le 2*n*b-4*g: "Degree of input not in the right interval";
//print"deg_red 1";
l := Ceiling((2*g-d+n*b)/b);
d_negative :=  -n*b+l*b+d; 
_,ind := Min(D`succ_min);// sollte elemente mit groesster nicht positiver länge nehmen!

Iinf_new := (D`Iinf)^-1*B`InfiniteIdeal^l;
B_minus,succmin_D := Minus_D(D`red_basis,Iinf_new,d_negative:early_exit:=false);
// Computing a red basis of (-n+l)*B+D_iso

a := D`red_basis[ind];	basis := [i*a :i in B_minus]; 
Iinf := Iinf_new*infinity_ideal(F!a); 
//print"deg_red 4";
//print"Degree_reduction took",Realtime()-tt;
if not DivClass then
	a := 1;
end if;
return rec<New_divisor_rep|red_basis := basis, succ_min := [i-l:i in succmin_D], Iinf := Iinf,
											d := (2*n-l)*b-d, k :=-(D`k+l), a := (D`a)^-1*a>;


end intrinsic;

//############################

intrinsic Scalar_mult(k::RngIntElt,D::Rec:DivClass := true)->Rec
{Computes k*D}



F := Parent(D`red_basis[1]);
if k eq 0 then return F`zero_divisor; end if;

if k lt 0 then
	D := Negative(D);
	k := -k;
end if;

BinaryCeoffs:=IntegerToBinary(k);
_,ind := Max(BinaryCeoffs);		
if ind eq 1 then D_final := D; end if;

for i in [2..#BinaryCeoffs] do
	D := Add_new(D,D:DivClass := DivClass);
	if ind eq i then D_final := D; end if;
	if not ind eq i and not BinaryCeoffs[i] eq 0 then
		D_final := Add_new(D_final,D:DivClass := DivClass);
	end if;
end for;

return D_final;
end intrinsic;

//############################

intrinsic Scalar_mult_2(k::RngIntElt,D::Rec:DivClass := true)->Rec
{Computes k*D, uses Add_new_2}

F := Parent(D`red_basis[1]);
if k eq 0 then return F`zero_divisor; end if;

if k lt 0 then
	D := Negative(D);
	k := -k;
end if;

BinaryCeoffs:=IntegerToBinary(k);
_,ind := Max(BinaryCeoffs);		
if ind eq 1 then D_final := D; end if;
for i in [2..#BinaryCeoffs] do
	D := Add_new_2(D,D:DivClass := DivClass);
	if ind eq i then D_final := D; end if;
	if not ind eq i and not BinaryCeoffs[i] eq 0 then
		D_final := Add_new_2(D_final,D:DivClass := DivClass);
	end if;
end for;

return D_final;
end intrinsic;


//############################

intrinsic Scalar_mult_3(k::RngIntElt,D::Rec:DivClass := true)->Rec
{Computes k*D, uses Add_new_3}

F := Parent(D`red_basis[1]);
if k eq 0 then return F`zero_divisor; end if;

if k lt 0 then
	D := Negative(D);
	k := -k;
end if;

BinaryCeoffs:=IntegerToBinary(k);
_,ind := Max(BinaryCeoffs);		
if ind eq 1 then D_final := D; end if;

for i in [2..#BinaryCeoffs] do
	D := Add_new_3(D,D:DivClass := DivClass);
	if ind eq i then D_final := D; end if;
	if not ind eq i and not BinaryCeoffs[i] eq 0 then
		D_final := Add_new_3(D_final,D:DivClass := DivClass);
	end if;
end for;

return D_final;
end intrinsic;

//############################

intrinsic Different_Divisor(F::FldFun)->Rec
{Computes the different divisor of F}

if assigned F`Different_Divisor then 
	return F`Different_Divisor;
end if;

F`Different_Divisor := Complementary_Divisor(Divisor(F!1));
return F`Different_Divisor;


end intrinsic;

//############################


intrinsic Complementary_Divisor(D::Rec)->Rec
{Takes a divisor D, outputs the complementary divisor D^#}

Ifin := D`FiniteIdeal;	Iinf := D`InfiniteIdeal;
F := Ifin`Parent;

if assigned F`Different_Divisor then 
	return F`Different_Divisor-D;
end if;

if not D eq Divisor(F!1) then
	return Different_Divisor(F)-D;
end if;

Ifin_C := Complementary_ideal(Ifin);
Iinf_C := Complementary_ideal(Iinf:Inf := true);

temp1 := SumListToString((Ifin_C^-1)`Factorization,false);
temp2 := SumListToString((Iinf_C^-1)`Factorization,true);

DC := Divisor(F!1);

DC`FiniteIdeal := Ifin_C;	DC`InfiniteIdeal := Iinf_C;	

if #temp1 gt 0 and #temp2 gt 0 then
		DC`FactorizationString:=temp1 cat "+(" cat temp2 cat " )";
	else
		DC`FactorizationString:=temp1 cat temp2;
	end if;

return DC;

end intrinsic;

//############################

intrinsic Complementary_ideal(I::Rec:Inf:=false)->Rec
{Taking a fractional ideal I of the finite maximal order, outputs I^#}

require IsIdealRecord(I): "I has to be an ideal record";
F := I`Parent;
Factorization(~I);
if not Inf then

	I_basis,I_factor:=IdealBase(I);
else
	kt<t> := PolynomialRing(ConstantField(F));
	Montes(F,t);
	I_basis,_,_,_,_,I_exp:=pBasis(I,t);
	I_factor := (F!t)^I_exp;
end if;
I_basis := [b*I_factor: b in I_basis];
M := Matrix(BaseField(F),Degree(F),[Trace(b_i*b_j): b_i in I_basis,b_j in I_basis])^-1;
L := Rows(M);

I_basis_com := [];

for elt in L do

	tmp := &+[elt[i]*I_basis[i]:i in [1..Degree(F)]];
	Append(~I_basis_com,tmp);
end for;

I_C := (ideal(F,I_basis_com))^1;

if Inf then
	Fac := [**];
	for i in I_C`Factorization do	
		if i[1] eq t then
			Append(~Fac,i);
		end if;
	end for;

	I_C`Factorization := Fac; 
	I_C`FactorizationString:=FactorListToString(I_C`Factorization);
end if;

return I_C;

end intrinsic;


//############################

intrinsic SM(D::Rec)->Rec
{Returns the (approximated) successive minima of the divisor class of D}

return [i-D`k:i in D`succ_min];


end intrinsic;


//############################

intrinsic dimension(D::Rec)->Rec
{Returns the dimension of the divisor class of D}

succ_min := SM(D);

dim := 0;
for i in succ_min do

	if i le 0 then dim := dim-i+1; end if;

end for;

return dim;

end intrinsic;


//############################

intrinsic basis_of_class(D::Rec)->SeqEnum
{Returns a basis of the Riemann Roch space of the divisor class of D}

succ_min := SM(D); 	F := Parent(D`red_basis[1]);
T := BaseField(F).1;
basis := [];
for i in [1..Degree(F)] do
	sm_i := succ_min[i];
	if sm_i le 0 then 
		basis := basis cat [D`red_basis[i]*T^l:l in [0..-sm_i]]; 
	end if;

end for;

return basis;


end intrinsic;
