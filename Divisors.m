freeze;


import "+IdealsFF.m": Montes;
		
//Attributes for dealing with places at infinity

AddAttribute(FldFun,"PrimesAtInfinity");
AddAttribute(FldFun,"Cf");
AddAttribute(FldFun,"InfinityRepresentation");
AddAttribute(FldFun,"Fin");
AddAttribute(FldFun,"Genus");
AddAttribute(FldFun,"Index");
AddAttribute(FldFun,"IndexBases");
AddAttribute(FldFun,"MonicDefiningPoly");
AddAttribute(FldFun,"ReductionON");
AddAttribute(FldFun,"DivisorOfDegree1");
AddAttribute(FldFun,"ConstanFieldIndex");


//Records for places and Divisors

DivisorRecord:=recformat<
    FiniteIdeal: Rec, 
    InfiniteIdeal: Rec,
    FactorizationString:  MonStgElt,
    SuccessiveMinima:	SeqEnum,
    ApproximatedSuccessiveMinima:	SeqEnum,
	RedBasis:	SeqEnum,
	SRedBasis:	SeqEnum,
	Basis:	SeqEnum,
	SmallDiv:	Rec,
	r:	RngIntElt,
	a:	FldFunElt,	
	IsPrincipal:	BoolElt
    >;
    
    
    



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic InfinityRepresentation(F::FldFun)->FldFun
{Input: Function field F with indeterminate T, outpout: Function field F with indeterminate 1/T}

	F`Fin:=1;
	if not assigned F`InfinityRepresentation or not assigned F`Cf then
		kt:=PolynomialRing(ConstantField(F));	t:=kt.1;	T:=BaseField(F).1;
		f:=DefiningMonicPolynomial(F);	n:=Degree(f);	Coeff:=Coefficients(f);

		Cf:=Maximum([Ceiling(Degree(Coeff[j])/(-j+n+1)): j in [1..#Coeff-1]]);
		CoeffList:=Eltseq(T^(-n*Cf)*PolynomialRing(Parent(T))!Evaluate(f,t^Cf*Parent(f).1));
		CoeffNewf:=[];
		for i in CoeffList do
			TMP:=0;
			for j in Terms(Numerator(i)) do 
				TMP:=TMP+LeadingCoefficient(j)*t^(Degree(Denominator(i))-Degree(j));
			end for;
			Append(~CoeffNewf,TMP);
		end for;
		Newf:=Parent(f)!CoeffNewf;

		F`InfinityRepresentation:=FunctionField(Newf);
		F`Cf:=Cf;
	else
		return 	F`InfinityRepresentation;
		
	end if;
	F`InfinityRepresentation`Fin:=0;
	F`InfinityRepresentation`InfinityRepresentation:=F;
	F`InfinityRepresentation`Cf:=F`Cf;
	return F`InfinityRepresentation,F`Cf;

end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic TranslationMap(z::FldFunElt,F::FldFun)->FldFunElt
{Input: z element of function field F with indeterminate T, output: z element of 
isomorphic function field F` with indeterminate 1/T }

	K:=Parent(z); KT:=BaseField(K);	T:=KT.1;
	Coeffs:=Eltseq(z);
	d:=K`Cf;
	Newz:=F![Evaluate(Coeffs[i],1/T)*(1/T)^(d*(i-1)):i in [1..Degree(F)]];
	return Newz;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Place(P::Rec)->Rec
{Construction of the place of a record}

require IsPrimeIdeal(P): "Argument should be a prime ideal";

K:=P`Parent;

if not assigned K`InfinityRepresentation then
	K`InfinityRepresentation:=InfinityRepresentation(K);
end if;

if not assigned K`Fin then
	K`InfinityRepresentation:=InfinityRepresentation(K);
	D:= rec<DivisorRecord|FiniteIdeal:=P,InfiniteIdeal := ideal(K`InfinityRepresentation,
	K`InfinityRepresentation!1),FactorizationString:=SumListToString((P^1)`Factorization,false)>;
else
	if K`Fin eq 1 then
		D:= rec<DivisorRecord|FiniteIdeal:=P,InfiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),FactorizationString:=SumListToString((P^1)`Factorization,false)>;	
	else	
		D:= rec<DivisorRecord|FiniteIdeal:=ideal(K`InfinityRepresentation,K`InfinityRepresentation!1),
		InfiniteIdeal:=P,FactorizationString:=Sprintf( "P(%o,%o)", 1/P`Parent!P`PolynomialGenerator,P`Position)  >;
	end if;
end if;	
if IsReductionOn(K) then
	DivisorReduction(~D);
end if; 

return D;	

end intrinsic;

//////////////////////////////////////////////////////////////////////
////////////////////////Divisor Arithmetic////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Add(D1::Rec,D2::Rec)->Rec
{Adding two divisors in OM representation}

	Dfin:=D1`FiniteIdeal*D2`FiniteIdeal;
	Dinf:=D1`InfiniteIdeal*D2`InfiniteIdeal;

	temp1:=SumListToString((Dfin^-1)`Factorization,false);
	temp2:=SumListToString((Dinf^-1)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<DivisorRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,
		FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<DivisorRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,
		FactorizationString:=temp1 cat temp2>;
	end if;
		
	return D;	
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic '+'(D1::Rec,D2::Rec)->Rec
{Adding two divisors in OM representation}

F:=D1`FiniteIdeal`Parent;

if IsReductionOn(F) then
	D:=Add(D1,D2);
	DivisorReduction(~D1);	DivisorReduction(~D2);
	D1_tmp:=D1`SmallDiv;	D1_r:=D1`r;	 D1_a:=D1`a;
	D2_tmp:=D2`SmallDiv;	D2_r:=D2`r;	 D2_a:=D2`a;	
	Dtmp:=Add(D1_tmp,D2_tmp);
	DivisorReduction(~Dtmp);
	D`SmallDiv:=Dtmp`SmallDiv;	D`r:=D1_r+D2_r+Dtmp`r;	D`a:=D1_a*D2_a*Dtmp`a;
	return D;
	
end if;
	
return Add(D1,D2);

		
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '-'(D1::Rec,D2::Rec)->Rec
{Subtraction of two divisor in OM representation}

	Dfin:=D1`FiniteIdeal*(D2`FiniteIdeal)^-1;
	Dinf:=D1`InfiniteIdeal*(D2`InfiniteIdeal)^-1;

	temp1:=SumListToString((Dfin^-1)`Factorization,false);
	temp2:=SumListToString((Dinf^-1)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<DivisorRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<DivisorRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
	end if;
	return D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '*'(k::RngIntElt,D::Rec)->Rec
{Multiplying a divisor in OM representation with an integer}

	F:=D`FiniteIdeal`Parent;
	Dfin:=D`FiniteIdeal^k;
	Dinf:=D`InfiniteIdeal^k;
	D_old:=D;
	temp1:=SumListToString((Dfin^-1)`Factorization,false);
	temp2:=SumListToString((Dinf^-1)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<DivisorRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<DivisorRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
	end if;
	
	if IsReductionOn(F) then
	
		DivisorReduction(~D_old);
		SetReduction(F:On:=false);
		Dtmp:=k*D_old`SmallDiv;
		DivisorReduction(~Dtmp);
		D`SmallDiv:=Dtmp`SmallDiv;
		D`r:=Dtmp`r+k*D_old`r;
		D`a:=Dtmp`a*D_old`a^k;
		SetReduction(F);
	
	end if;
	
	return D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Divisor(I::Rec)->Rec
{Input: A fractional ideal I in OM representation; 
Output: A divisor in OM representation having the ideal representation I and the trivial ideal.}

	K:=I`Parent;
	if not assigned K`Fin then
		K`Fin:=1;
	end if;
	if not assigned  K`InfinityRepresentation then
		K`InfinityRepresentation:=InfinityRepresentation(K);
	end if;
	if not assigned (I^1)`Factorization and K`Fin eq 1 then 

		D:= rec<DivisorRecord|FiniteIdeal:=ideal(K,K!1),
		InfiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),FactorizationString:="">;
	end if;
	if not assigned (I^1)`Factorization and K`Fin eq 0 then 

		D:= rec<DivisorRecord|FiniteIdeal:=ideal(K`InfinityRepresentation
		,K`InfinityRepresentation!1),
		InfiniteIdeal:=ideal(K,K!1),FactorizationString:="">;
	end if;
	if K`Fin eq 1 then 

		D:= rec<DivisorRecord|FiniteIdeal:=I,InfiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),
		FactorizationString:=SumListToString((I^-1)`Factorization,false)>;
	else	

		D:= rec<DivisorRecord|FiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),InfiniteIdeal:=I,
		FactorizationString:=SumListToString((I^-1)`Factorization,true)>;
	end if;

	if IsReductionOn(K) then
			DivisorReduction(~D);
	end if;	
	
	return D;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Divisor(z::FldFunElt)->Rec
{Produces the principal divisor in OM representation of non-zero function of a function field}

	require not z eq 0: "Argument should be a non zero";
	K:=Parent(z);	Ifin:=ideal(K,z)^1;
	Iinf:=&*[i^(PValuation(z,i)): i in PrimesAtInfinity(K)];
	temp1:=SumListToString((Ifin)`Factorization,false);
	temp2:=SumListToString((Iinf)`Factorization,true);
	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<DivisorRecord|FiniteIdeal:=Ifin^-1,InfiniteIdeal:=Iinf^-1,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<DivisorRecord|FiniteIdeal:=Ifin^-1,InfiniteIdeal:=Iinf^-1,FactorizationString:=temp1 cat temp2>;
	end if;
	D`IsPrincipal:=true;	
	D`a:=1/z;
	if IsReductionOn(K) then
			D`SmallDiv:=Divisor(K!1);	D`r:=0;			
	end if;	
	return D;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Support(D::Rec)->SeqEnum
{Determines the support of a divisor}

	K:=D`FiniteIdeal`Parent;
	L1:=((D`FiniteIdeal)^-1)`Factorization;
	FinitePrimes:=[];	FiniteExponents:=[];
	for i in L1 do
		Append(~FinitePrimes,K`PrimeIdeals[i[1],i[2]]);
		Append(~FiniteExponents,i[3]);
	end for;

	L2:=((D`InfiniteIdeal)^-1)`Factorization;	PAI:=PrimesAtInfinity(K);
	InfinitePrimes:=[];	InfiniteExponents:=[];
	for i in L2 do
		Append(~InfinitePrimes,PAI[i[2]]);
		Append(~InfiniteExponents,i[3]);
	end for;
	
	return InfinitePrimes cat FinitePrimes,InfiniteExponents cat FiniteExponents;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////    


intrinsic GCD(D1::Rec,D2::Rec)->Rec
{Determines the GCD of two divisor D1 and D2}

GC:=[]; Expo_1:=[];	Expo_2:=[];
PL_1,Ex_1:=Support(D1);	PL_2,Ex_2:=Support(D2);
for i in [1..#PL_1] do
	for j in [1..#PL_2] do
		if PL_1[i] eq PL_2[j] then 
			Append(~GC,PL_1[i]);
			Append(~Expo_1,Ex_1[i]);
			Append(~Expo_2,Ex_2[j]);
		end if;
	end for;	
end for;
return GC,Expo_1,Expo_2;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Height(D::Rec)->RngIntElt
{Determines the height of a divisor}

	Supp,Expos:=Support(D);
	if #Expos eq 0 then
		return 0,0;
	else
		return &+[Abs(Expos[i])*Degree(Supp[i]):i in [1..#Expos]],Maximum([Degree(Supp[i]):i in [1..#Expos]]);
	end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PlacesAtInfinity(K::FldFun)->SeqEnum
{Produces the places at infinity of K}

	if not assigned K`PrimesAtInfinity then
	
		if not assigned K`InfinityRepresentation then
			K`InfinityRepresentation,K`Cf:=InfinityRepresentation(K);	
		end if;
	
		Montes(K`InfinityRepresentation,PolynomialRing(ConstantField(K)).1);
		K`PrimesAtInfinity:=K`InfinityRepresentation`PrimeIdeals[PolynomialRing(ConstantField(K)).1];
	
	end if;

	return [Place(i): i in K`PrimesAtInfinity];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PrimesAtInfinity(K::FldFun)->SeqEnum
{Produces the prime ideals of the infinite maximal order of K}

	if not assigned K`PrimesAtInfinity then
	
		if not assigned K`InfinityRepresentation then
			K`InfinityRepresentation,K`Cf:=InfinityRepresentation(K);	
		end if;
	
		Montes(K`InfinityRepresentation,PolynomialRing(ConstantField(K)).1);
		K`PrimesAtInfinity:=K`InfinityRepresentation`PrimeIdeals[PolynomialRing(ConstantField(K)).1];
	
	end if;

	return K`PrimesAtInfinity;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////



intrinsic IsDivisor(D::Rec)->BoolElt
{True iff D is a record of type DivisorRecord.}
return    Names(D) eq Names(rec<DivisorRecord|>);
end intrinsic;

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IsPlace(P::Rec)->BoolElt
{True iff P is a record of type DivisorRecord.}
if    Names(P) eq Names(rec<DivisorRecord|>) then
	Ifin := P`FiniteIdeal^1; 
	Iinf := P`InfiniteIdeal^1;
	Factorization(~Ifin);	Factorization(~Iinf);
	if (#Ifin`Factorization eq 1 and #Iinf`Factorization eq 0 and Ifin`Factorization[1,3] eq 1)
		or (#Ifin`Factorization eq 0 and #Iinf`Factorization eq 1 and Iinf`Factorization[1,3] eq 1)
	then return true;
	end if;
end if;

return false;
end intrinsic;


//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic IsEffective(D::Rec)->BoolElt
{}
_,coeffs := Support(D);
return    forall{i:i in coeffs|i  ge 0 };
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic SumListToString(list,inf)->MonStgElt
{Technical function to write down a factorization in a pretty form. For internal use only}
if #list eq 0 then return ""; end if;
R<t>:=Parent(list[1,1]);
str:="";
run:=0;
for x in list do
	run:=run+1;	
  if x[3] ne 1 then str:= str cat Sprintf(" %o*",x[3]) ; end if;
 	 if run eq #list then
 		if 	inf eq false then 
		  str:=str cat Sprintf( "P(%o,%o)", R!x[1],x[2]);
		else
	      str:=str cat Sprintf( "P(1/t,%o)", x[2]);  
	    end if;  
	else
		if 	inf eq false then 
			str:=str cat Sprintf( "P(%o,%o)+", R!x[1],x[2]);
		else
			str:=str cat Sprintf( "P(1/t,%o)+",x[2]);
		end if;	  
      end if;
end for;
return Substring(str,1,#str);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic PValuation(D::Rec, P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of a divisor at the prime ideal P}

require IsDivisor(D): "First argument should be a divisor";
require IsPrimeIdeal(P) or IsPlace(P): "Second argument should be a prime ideal or a place";

if IsPlace(P) then
	
	tmp:=P`FiniteIdeal^1;
	if #(tmp`Factorization) eq 0 then
		P:=P`InfiniteIdeal;
	else
		P:=P`FiniteIdeal;
	end if;

end if;
S1,S2:=Support(D);
bool,pos:=P in S1;
if bool then 
	return S2[pos];
else
	return 0;
end if;	
		

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic RRSpace(~D::Rec:Reduced:=false)
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one if
Reduced:=true. No divisorreduction is applied}

if Reduced and assigned D`RedBasis then return; end if;
if not Reduced and assigned D`SRedBasis then return; end if;
//if assigned D`SmallDiv then tmp:=Reduced;RRSpace2(~D:Reduced:=tmp);	return; end if;
Ifin:=D`FiniteIdeal;	Iinf:=D`InfiniteIdeal;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;
//////////////////////////Producing bases/////////////////////////
Bfin,finitefac:=IdealBase(Ifin);
Montes(F2,t);

InfPrimes:=PrimesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;
if Reduced eq true then
	Binf,Values,_,_,_,infex:=pBasisRed(Iinf,t:Reduced:=true);	
else
	Binf,_,_,_,_,infex:=pBasis(Iinf,t);
end if;
Bprime:=[TranslationMap(i,F):i in Binf];
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);
M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);

if Reduced eq true then
	denmax:=K!Sort([Denominator(i):i in Bprime])[n];
	Mhelp:=Inverse(M2,denmax);
else
	Mhelp:=M2^(-1);
end if;
T := M1*Mhelp;
if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T,Values);
else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T);
end if;	

if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([deg(j):j in i]):i in RowSequence(T)];

	redbasis:=[i*finitefac:i in Bfin];
	SuccMin:=[Deg(K!finitefac)+i+infex:i in SuccMin];
else	
	redbasis:=[finitefac * &+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
	SuccMin:=[i+infex+Deg(K!finitefac):i in SuccMin];

end if;

if Reduced eq true then
	D`RedBasis:=redbasis;
	D`SuccessiveMinima:=SuccMin;
else	
	D`SRedBasis:=redbasis;
	D`ApproximatedSuccessiveMinima:=SuccMin;
end if;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////



intrinsic ReductionAlgorithm(T::AlgMatElt:InA:=false)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
NumberRedSteps:=0;

lc:=LCM([Denominator(i):i in Eltseq(T)]);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n:=Ncols(T);m:=Nrows(T);
T:=Parent(ZeroMatrix(kt,n,n))!(lc*T);

s:=1;

if m eq 1 then return T,Maximum([Deg(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p:=[];
Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);

while s lt m do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..m] do
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
		Su:=SubmatrixRange(P,s+1,1,n,n);
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
	end if;
end while;	
print"NumberRedSteps",NumberRedSteps;
if InA then 
	return lc,T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
else
	return (1/K!lc)*T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic ReductionAlgorithm(T::AlgMatElt, Values::SeqEnum)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}

Vals:=SetToSequence(Set(Values));
lc,T,VectorNorm,NumberRedSteps:=ReductionAlgorithm(T:InA:=true);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);

if #Vals eq 1 then 
	return (1/K!lc)*T,VectorNorm,NumberRedSteps;
end if;

l:=1;	VectorNorm:=[Norm(i,Values):i in RowSequence(T)];
p:=[];	Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);
while l le #Vals do
	ColumnIndex:=[ y : y in  [1..#Values] | Values[y] eq Vals[l]];
	RowIndex:=[ y : y in  [1..#VectorNorm] | (VectorNorm[y]-Ceiling(VectorNorm[y])) eq Vals[l]];

	m:=#RowIndex;	n:=#ColumnIndex;	M:=ZeroMatrix(k,m,n);
	if m gt 1 then
		for i in [1..m] do
			for j in [1..n] do
				if not T[RowIndex[i],ColumnIndex[j]] eq 0 
					and Degree(T[RowIndex[i],ColumnIndex[j]])+Vals[l] eq VectorNorm[RowIndex[i]] then			
					M[i,j]:=LeadingCoefficient(T[RowIndex[i],ColumnIndex[j]]);				
				end if; 				
			end for;
		end for;
		Mprime,P:=EchelonForm(M);
		s:=Rank(Mprime);
		if s eq m then 
			if m lt n and not Vals[l] in [Vals[i]:i in [l+1..#Vals]] then 
				Append(~Vals,Vals[l]);
			end if;	
						
		else
			NumberRedSteps:=NumberRedSteps+m-s;
			Su:=SubmatrixRange(P,s+1,1,m,m);
			P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
			for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			jj:=RowIndex[u];
				for i in [1..u-1] do
					
					if not P[j,i] eq 0 then
						ii:=RowIndex[i];
						AddRow(~T,P[j,i]/P[j,u]*t^(Ceiling(VectorNorm[jj])-Ceiling(VectorNorm[ii])),ii,jj);
					end if;	
				end for;

				VectorNorm[jj]:=Norm(ElementToSequence(T[jj]),Values);
			
				if not VectorNorm[jj]-Ceiling(VectorNorm[jj]) in [Vals[i]:i in [l+1..#Vals]] then 
					Append(~Vals,VectorNorm[jj]-Ceiling(VectorNorm[jj]));
				end if;				

			end for;
			p:=[];			Sort(~VectorNorm,~p);		T:=Matrix([T[i]:i in Eltseq(p)]);
		end if;

	end if;
	l:=l+1;
end while;	

return  (1/K!lc)*T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;

end intrinsic;



/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic RandomDivisorClass(F::FldFun)->Rec
{Produces a representative of a divisor class of degree 0.}
require IsGlobal(F): "Function field is not global";

g:=GENUS(F);
Fq:=ConstantField(F);	q:=#Fq;		A:=DivisorOfDegree1(F);
d:=Random([1..Maximum([g,1])]);
if d eq 1 then 
	d_tmp:=Random([0..q]);
	if d_tmp eq q then 
		P:=Random(PlacesAtInfinity(F));
		return P-Degree(P)*A;
	else	
		p:=PolynomialRing(Fq).1-Fq!d_tmp;
		Montes(F,p);
		P:=Divisor(Random(F`PrimeIdeals[p]));
		return P-Degree(P)*A;
	end if;	
else
	p:=RandomPrimePolynomial(PolynomialRing(Fq),d);
	Montes(F,p);
	P:=Divisor(Random(F`PrimeIdeals[p]));
	return P-Degree(P)*A;
end if;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic RandomDivisor(F::FldFun,l::RngIntElt)->Rec
{Produces a divisor.}


a := Random(F,l);
while  a eq 0 do
	a := Random(F,l);
end while;

S1 := Support(Divisor(a));
g := GENUS(F);
D := &+[Random([-g..g])*Divisor(i):i in S1];

return D;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Degree(I::Rec)->RngIntElt
{computes the Degree of a place, prime ideal or a divisor}


if IsPrimeIdealRecord(I) then
	K:=I`Parent;
	if IsFinite(ConstantField(K)) then
		deg:= Integers()!(Degree(I`Type[#I`Type]`Fq)/Degree(ConstantField(K)));
	else
		deg:=Degree(I`Type[#I`Type]`Fq);
	end if;
	return deg;
end if;


if IsIdealRecord(I) then
	K:=I`Parent;
	I:=K`PrimeIdeals[I`Factorization[1,1],I`Factorization[1,2]];
	return $$(I);
end if;


/*if IsPlace(I) then
print"asd";
	Ifin:=I`FiniteIdeal^-1;	Iinf:=I`InfiniteIdeal^-1;
	print"Ifin;",Ifin;
	if #Ifin`Factorization eq 0 then
		return $$(Iinf);
	else
		return $$(Ifin);		
	end if;
end if;*/

if IsDivisor(I) then	

	K:=I`FiniteIdeal`Parent;
	L1:=((I`FiniteIdeal)^-1)`Factorization;
	if #L1 gt 0 then
		dfin:=&+[i[3]*$$(K`PrimeIdeals[i[1],i[2]]): i in L1];
	else
		dfin:=0;
	end if;

	L2:=((I`InfiniteIdeal)^-1)`Factorization;
	if #L2 gt 0 then
		PAI:=PrimesAtInfinity(K);

		dinf:=&+[i[3]*$$(PAI[i[2]]): i in L2];
	else
		dinf:=0;
	end if;	

	return dfin+dinf;
end if;	
	

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Dimension(D::Rec)->RngIntElt
{Determines the dimension of the Riemann-Roch space of D}

if assigned D`Basis then return #D`Basis; end if;
F:=D`FiniteIdeal`Parent;
if Degree(D) lt 0 then return 0; end if;
if Degree(D) ge 2*GENUS(F)-1 then
	return Degree(D)+1-GENUS(F);
end if;

if  assigned D`SuccessiveMinima then
	D`ApproximatedSuccessiveMinima := [Ceiling(i):i in D`SuccessiveMinima];
end if;

if not assigned D`SuccessiveMinima and not assigned D`ApproximatedSuccessiveMinima then
	RRSpace2(~D);
end if;
	succMin:=D`ApproximatedSuccessiveMinima;
dim:=0;
for i in succMin do
	if i le 0 then	
		dim:=dim+1-i;	
	end if;
end for;

return dim;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic DivisorOfDegree1(F)->Rec
{}

Fq:=ConstantField(F); A := PolynomialRing(Fq);
require IsFinite(Fq):"Constant field must be finite.";

if assigned F`DivisorOfDegree1 then return F`DivisorOfDegree1; end if;

Pinf:=PrimesAtInfinity(F); 
u := exists(ind){ y : y in Pinf | Degree(y) eq 1};
if u then return Divisor(ind); end if;

Pfin:=F`PrimeIdeals[A.1]; 
u := exists(ind){ y : y in Pfin | Degree(y) eq 1};
if u then return Divisor(ind); end if;


P_0 := Pinf[1];	d_0 :=Degree(P_0);
for i in PrimesAtInfinity(F) do

	P:=i; d:=Degree(P);
	if d eq 1 then return Divisor(P); end if;
	if GCD([d,d_0]) eq 1 then
		_,a,b:=ExtendedGreatestCommonDivisor(d_0,d);
		return a*Divisor(P)+b*Divisor(P_0);
	else
		if d lt d_0 then
			P_0:=P;		d_0:=d;
		end if;
		
	end if;
	
end for;

g,indi:=GENUS(F);

require indi eq 1:"Constant field is not the exact constant field.";


r:=Ceiling(Log(#Fq,2*g));	L:=PrimePolynomials(PolynomialRing(Fq),r);
for i in L do 
	Montes(F,i);
	for j in F`PrimeIdeals[i] do
		
		P:=i; d:=Degree(P);
		if d eq 1 then return Divisor(P); end if;
			if GCD([d,d_0]) eq 1 then
				_,a,b:=ExtendedGreatestCommonDivisor(d_0,d);
			return a*Divisor(P)+b*Divisor(P_0);
		else
			if d lt d_0 then
				P_0:=P;		d_0:=d;
			end if;		
		end if;	
		
	end for;
	
end for;


end intrinsic;
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic Basis(D::Rec:Reduction:=true)->RngIntElt
{Determines the basis of the Riemann-Roch space of D}

if Degree(D) lt 0 then return []; end if;

if not assigned D`RedBasis and not assigned D`SRedBasis then

	if Reduction eq true then
		RRSpace2(~D);
	else	
		RRSpace(~D);	
	end if;

end if;
		succMin:=D`ApproximatedSuccessiveMinima;	


if assigned D`RedBasis then 
	SemiRedBasis:=D`RedBasis;
else
	SemiRedBasis:=D`SRedBasis;
end if;

T:=BaseField(D`FiniteIdeal`Parent).1;
basis:=[];

for i in [1..#succMin] do
	if succMin[i] le 0 then	
		Append(~basis,[SemiRedBasis[i]*T^jj:jj in [ 0..-succMin[i] ] ]);	
	end if;
end for;

return &cat basis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Basis(~D::Rec:Reduction:=true)
{Determines the basis of the Riemann-Roch space of D}

if Degree(D) lt 0 then D`Basis:=[]; return ; end if;

if not assigned D`RedBasis and not assigned D`SRedBasis then

	if Reduction eq true then
		RRSpace2(~D);
	else	
		RRSpace(~D);	
	end if;

end if;
		succMin:=D`ApproximatedSuccessiveMinima;	


if assigned D`RedBasis then 
	SemiRedBasis:=D`RedBasis;
else
	SemiRedBasis:=D`SRedBasis;
end if;

T:=BaseField(D`FiniteIdeal`Parent).1;
basis:=[];

for i in [1..#succMin] do
	if succMin[i] le 0 then	
		Append(~basis,[SemiRedBasis[i]*T^jj:jj in [ 0..-succMin[i] ] ]);	
	end if;
end for;

D`Basis:=&cat basis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ReducedBasis(D::Rec)->SeqEnum
{Determines a reduced basis the lattice corresponding to D}

if not assigned D`RedBasis  then
	RRSpace2(~D:Reduced:=true);
end if;

return D`RedBasis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic SemiReducedBasis(D::Rec)->SeqEnum
{Determines a reduced basis the lattice corresponding to D}

if not assigned D`RedBasis  then
	RRSpace2(~D);
end if;

return D`SRedBasis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IsPrincipal(D::Rec)->BoolElt
{}

if not Degree(D) eq 0 then return false; end if;

if Dimension(D) ge 0 then 
	return true;
else
	return false;
end if;	
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic PoleDivisor(a::FldFunElt)->FldFun
{Determines the pole divisor of a non zero function z}

require not a eq 0:"Argument must be non zero";

F:=Parent(a); kt:=PolynomialRing(ConstantField(F));

if a in ConstantField(F) then return Divisor(F!1); end if;
den := kt!Denominator(a);	num := Numerator(a);
primes := Factorization(den);

FintePoles:=[];
for i in primes do

	Montes(F,i[1]);
	for j in F`PrimeIdeals[i[1]] do
		tmp:=PValuation(num,j);
		if tmp lt j`e*i[2] then
			Append(~FintePoles,j^(j`e*i[2]-tmp));
		end if;
	end for;

end for;

InfinitePol:=[];

for i in PrimesAtInfinity(F) do

	tmp:=PValuation(num,i);
	if tmp lt -i`e*Degree(den) then
		Append(~InfinitePol,i^(-i`e*Degree(den)-tmp));
	end if;
end for;

if #FintePoles eq 0 or #InfinitePol eq 0 then 
	if #FintePoles eq 0 and #InfinitePol eq 0 then
		D:=	Divisor(F!1);	
	//	if IsReductionOn(F) then DivisorReduction(~D); end if;
		return D;
	end if;

	if #FintePoles eq 0 then
		D:=&+[Divisor(i):i in InfinitePol];
	else
		D:= &+[Divisor(i):i in FintePoles];
	end if;

	if IsReductionOn(F) then DivisorReduction(~D); end if;
	return -1*D;
end if;


D:=&+[Divisor(i):i in FintePoles]+&+[Divisor(i):i in InfinitePol];

if IsReductionOn(F) then
	DivisorReduction(~D);
end if;

return -1*D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic ZeroDivisor(a::FldFunElt)->FldFun
{Determines the zero divisor of a non zero function z}

require not a eq 0:"Argument must be non zero";

return PoleDivisor(1/a);

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Are_equivalent(D1::Rec,D2::Rec)->BoolElt
{Tests if two divisor belong to the same class of degree zero}

require Degree(D1) eq  Degree(D2):"Arguments must have the same degree";

D := D1-D2; DivisorReduction(~D:DivisorClass := true);
if Dimension(D) gt 0 then
	return true;
else
return false;
end if;
end intrinsic;


//////////////////////////////////////////////////////////////////////
/////////////////////Divisor Reduction////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic ElementaryReduction(D::Rec,A::Rec)->Rec
{}

//print"D",D`FactorizationString;
if Height(D) lt 2*GENUS(D`FiniteIdeal`Parent)+1 then return D,0,D`FiniteIdeal`Parent!1;end if; //3*GENUS(D`FiniteIdeal`Parent)
print"ER1";
if Degree(A) eq 0 then  
	return D,0,D`FiniteIdeal`Parent!0;
end if;
F:=D`FiniteIdeal`Parent;	r1:=Ceiling(-Degree(D)/Degree(A));	r2:=Ceiling((GENUS(F)-Degree(D))/Degree(A));
//r1 := Min([r1,r2]); r2 :=Max([r1,r2]);
ElementList:=[];
if r1 lt 1 then
	shift:=-Min([r1,r2])+1;
else	
	shift:=0;	
end if;
print"ER2";
if not r1 eq r2 then
	dimlist:=[];	dimlist[r2+shift]:=1; 	
	dim2:=1;
	
	Dtmp:=D+r1*A;  RRSpace(~Dtmp);	dimlist[1]:=Dimension(Dtmp);
	ElementList[1]:=Dtmp`SRedBasis[1];	
print"ER3";
	if dimlist[1] gt 0 then
print"ER3.1",ElementList[1],Height(Dtmp);
		return Dtmp+Divisor(ElementList[1]),-r1,ElementList[1];
	end if;
	
	D1:=D+(r2-1)*A; RRSpace(~D1);	dim1 := Dimension(D1);	dimlist[(r2-1)+shift]:=1;
print"ER4";	
	if dim1 eq 0 then
		r:=r2; 	D2:=D1+A; RRSpace(~D2); ElementList[r2+shift]:=D2`SRedBasis[1];

	else
		R:=r2-1;
		L:=r1; 
		
		while not dim1 eq 0 or dim2 eq 0 do
			
			r1:=L+Floor((R-L)/2);	r2:=r1+1;	D1:=D+r1*A;		D2:=D1+A;
			if IsDefined(dimlist,r1+shift) then
				dim1:=dimlist[r1+shift];
			else
				RRSpace(~D1);	dim1 := Dimension(D1);	dimlist[r1+shift]:=dim1;
				ElementList[r1+shift]:=D1`SRedBasis[1];
			end if;
print"ER5";			
			if dim1 eq 0 then 
				if IsDefined(dimlist,r2+shift) then
				dim2:=dimlist[r2+shift];
				else
					RRSpace(~D2);	dim2 := Dimension(D2);	dimlist[r2+shift] := dim2;
					ElementList[r2+shift]:=D2`SRedBasis[1];
				end if;
			else
				dim2 := 1;	dimlist[r2+shift] := dim2;
			end if;
			
			if dim1 gt 0 and dim2 gt 0 then				
				R:=r1;
			else
				L:=r2;
			end if;
			
			if dim1 eq 1 and r1 gt 1 then
				if IsDefined(dimlist,r1-1+shift) then
					if dimlist[r1-1+shift] eq 0 then r:=r1; break; end if;
				end if;
			end if;

			if dim2 eq 0 and IsDefined(dimlist,r2+1+shift) then
					if dimlist[r2+1+shift] eq 1 then r:=r2+1; break; end if;
			end if;

			r:=r2;
print"ER6";
		end while;
		
	end if;

else

	r:=r1;

end if;
D0:=D+r*A;
print"ER7";
if IsDefined(ElementList,r+shift) then
	a:=ElementList[r+shift];
else	
	 RRSpace(~D0); 	a:=D0`SRedBasis[1];
end if;
print"ER8,a",a,Height(D0);

return D0+Divisor(a),-r,a,D0;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Summands(D::Rec)->SeqEnum
{Binary dissction of a divosor}
K:=D`FiniteIdeal`Parent;
Divis,Coeffs:=Support(D);
TheDi:=[];

BinaryCeoffs:=[IntegerToBinary(i):i in Coeffs];

max:=Maximum([#ii:ii in BinaryCeoffs]);
L:=[1..#Coeffs];
H:=[];
for i in [1..max] do

	temp:=Divisor(K!1);
	L:=SetToSequence(Set(L) diff Set(H));
	for j in L do
		
		if IsDefined(BinaryCeoffs[j],i) then
			if Abs(BinaryCeoffs[j,i]) eq 1 then
				temp:=temp-BinaryCeoffs[j,i]*Divisor(Divis[j]);
			end if;
		else
			Append(~H,j);
		end if;
		
	end for;
	if #temp`FactorizationString gt 0 then
	TheDi[i]:=temp;
	end if;
end for;

return TheDi;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic SupportReduction(D::Rec,A::Rec)->Rec
{}
K:=D`FiniteIdeal`Parent;

if Height(D) lt 2*GENUS(K)+1 then return D,0,K!1;end if;

Divis,Coeffs:=Support(D);
if #Divis le 1 then
	return D,0,K!1;
end if;

DD:=Divisor(K!1);
TheRs:=[];
TheAs:=[];

for i in [1..#Coeffs] do
		DD,r,a:=ElementaryReduction(Coeffs[i]*Place(Divis[i])+DD,A);
		//print"supp";DD`FactorizationString;
		TheRs[i]:=r;
		TheAs[i]:=a;

end for;
return DD,-1*&+[TheRs[i]:i in [1..#TheRs]],&*[ TheAs[i]:i in [1..#TheAs]];
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic HeightReduction(D::Rec,A::Rec:DivisorClass:=false)->Rec
{}
K:=D`FiniteIdeal`Parent;
if Height(D) lt 2*GENUS(K)+1 then return D,0,K!1;end if;//3*GENUS(K)

rA_1,rA_2:=Support(A);
rD_1,rD_2:=Support(D);

Acoeffs_inD:=[];

for i in [1..#rA_1] do
	for j in [1..#rD_1] do	
		if rA_1[i] eq rD_1[j] then
			Append(~Acoeffs_inD,rD_2[j]/rA_2[i]); break;		
		else
			Append(~Acoeffs_inD,0)	; break;	
		end if;
	end for;
end for;	
r_start:=0;

if forall{o:o in Acoeffs_inD|o gt 0} then 
	r_start:=Minimum([Floor(i):i in Acoeffs_inD]);
end if;	

D:=D-r_start*A;
if Height(D) lt 2*GENUS(K)+1 then return D,r_start,K!1;end if;//3*GENUS(K)

TheDi := Summands(D);	TheA := [];	TheR := [];	r_run := 0;	a_run := K!1;

for i in [1..#TheDi] do
	if IsDefined(TheDi,i) then
		DD,r,a:=SupportReduction(TheDi[i],A);
		TheDi[i]:=DD;	TheR[i]:=r;		TheA[i]:=a;
	end if;	
end for;
DD:=TheDi[#TheDi]; a_run:=TheA[#TheA]; r_run:=TheR[#TheR];
for j:=#TheDi-1 to 1 by  -1 do
	if IsDefined(TheDi,j) then
		DD,r,a:=ElementaryReduction(2*DD+TheDi[j],A);
		r_run:=r+2*r_run+TheR[j];
		if not DivisorClass then		
			a_run:=a*a_run^2*TheA[j];
		else
			a_run := 1;
		end if;					
	else
		DD,r,a:=ElementaryReduction(2*DD,A);
		r_run:=r+2*r_run;	
		if not DivisorClass then						
			a_run:=a*a_run^2;	
		else
			a_run := 1;
		end if;							
	end if;	
end for;

return DD,r_run,a_run;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic RiemannRochSpace(~D::Rec:Reduction:=true)
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

if Reduction eq true then

	RRSpace2(~D);
else

	RRSpace(~D);	
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic GENUS(K::FldFun:AbsIrr:=true)->SeqEnum
{Compute the genus g of a function field K/k and the index gc=[k_0:k], where k_0 is the full constant field.}
t1:=Realtime();
if assigned K`Genus then return Integers()!K`Genus,K`ConstanFieldIndex;end if;

t:=PolynomialRing(ConstantField(K)).1;
n:=Degree(K);
index,DegList:=Index(K);
K_iso:=InfinityRepresentation(K);
Montes(K_iso,t);
DegList:= DegList cat [Degree(i):i in K_iso`PrimeIdeals[t]];
indexlocal:=K_iso`LocalIndex[t];
d:=K`Cf;
Append(~DegList,Integers()!(-indexlocal+Integers()!(d*(n-1)*n/2)-index));
Append(~DegList,n);
gc:=GCD(DegList);
gcold:=gc;
newinf:=-n-indexlocal+Integers()!(d*(n-1)*n/2)-index;
tmpp:=1;
if newinf lt 0 then return 0,gc; end if; 
if newinf eq 0 then return 1,1;end if;

if gc gt 1 and not AbsIrr then 
	if IsFinite(ConstantField(K))	then
		Fp:=GF(Characteristic(ConstantField(K)),Degree(ConstantField(K))*gc);
		Fpt:=RationalFunctionField(Fp);	KxT<x> := PolynomialAlgebra(Fpt);
		tmpp:=Factorization(KxT!DefiningPolynomial(K));
		gc:=#Factorization(KxT!DefiningPolynomial(K));
	else
		gc:=Dimension(Divisor(K!1));
	end if;
else 
	gc:=1;	
end if;

g:=1+(-n-indexlocal+Integers()!(d*(n-1)*n/2)-index)/gc;
K`Genus:=Integers()!g;	K`ConstanFieldIndex:=gc;

return Integers()!g,gc,tmpp;


end intrinsic;
///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////


intrinsic SuccessiveMinima(D::Rec:Reduction:=true)->SeqEnum
{Determines the SuccessiveMinima of the lattice corresponding to the divisor D}

if Reduction eq true then 
	RRSpace2(~D:Reduced:=true);
else
	RRSpace(~D:Reduced:=true);
end if;
return D`SuccessiveMinima;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic ApproximatedSuccessiveMinima(D::Rec:Reduction:=true)->SeqEnum
{Determines the SuccessiveMinima of the lattice corresponding to the divisor D}

if Reduction eq true then 
	RRSpace2(~D);
else
	RRSpace(~D);
end if;
return D`ApproximatedSuccessiveMinima;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic SuccessiveMinima(~D::Rec:Reduction:=true)
{Determines the SuccessiveMinima of the lattice corresponding to the divisor D}

if Reduction eq true then 
	RRSpace2(~D:Reduced:=true);
else
	RRSpace(~D:Reduced:=true);
end if;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic Signature(F::FldFun) -> SeqEnum
{}
signature:=[];
for i in PrimesAtInfinity(F) do
	if i`e eq 1 then
		Append(~signature,[0:j in [1..i`f]]);
	else
		Append(~signature,[-j/i`e:j in [0..i`e-1]]);	
	end if;	
end for;
signature:=&cat signature;
return Sort(signature);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic DivisorReduction(~D::Rec:DivisorClass:=false) 
{}
check:=false;
F:=D`FiniteIdeal`Parent;
if assigned D`IsPrincipal and not assigned D`r then
	D`r:=0; D`SmallDiv:=Divisor(F!1);
	return;
end if;

if IsReductionOn(F) then 
	check:=true;
	SetReduction(F:On:=false);		
end if;
A:=PoleDivisor(F!BaseField(F).1);
D0,r,a:=HeightReduction(D,A:DivisorClass);
if check then 
	SetReduction(F);	
end if;

D`SmallDiv:=D0;	D`r:=r;	D`a:=F!a;
		
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic SetReduction(F::FldFun:On:=true)
{}

if not assigned F`InfinityRepresentation then

	F`InfinityRepresentation:=InfinityRepresentation(F);
end if;

F`ReductionON:=On;
F`InfinityRepresentation`ReductionON:=On;	


end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic IsReductionOn(F::FldFun)-> BoolElt
{}

if assigned F`ReductionON then

	if F`ReductionON then return true; end if;
	
end if;

return false;

end intrinsic;


/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////