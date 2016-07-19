//TestFile

pBasisTriangular

Attach("/Users/JB/Mathematik/Programming/Magma/Diss/Helpfunctions/Helpfunctions.m");
Attach("~/Mathematik/Programming/Magma/FunctionFields/+IdealsFF.m");

F := Random_FunctionField_with_index(2,13,7);

I := RandomDivisor(F,4)`FiniteIdeal;

idealBasis(I);
