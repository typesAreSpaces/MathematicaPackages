(* ::Package:: *)

BeginPackage["QuantumGates`"];

Zeros::usage"";
Ones::usage"";
ComputationalBS::usage"";
Kp::usage"";
Blocks::usage"";
Conj::usage"";
Fp::usage"";
ZeroMatrixQ::usage"";

Id::usage"";
H::usage"Hadamard gate";
S::usage"";
T::usage"";
X::usage"";
Y::usage"";
Z::usage"";
CX::usage"";
CCX::usage"";
CY::usage"";
CCY::usage"";
CZ::usage"";
CCZ::usage"";
NOT::usage"";
CNOT::usage"";
CCNOT::usage"";


Begin["`Private`"];


(*Helper functions*)
Zeros[n_]:=Table[{0},{n}];
Ones[n_]:=Table[{1},{n}];
ComputationalBS[p_,nQubits_]:=Table[{If[p==i,1,0]},{i,1,2^nQubits}];

Kp=KroneckerProduct;
Blocks[x__]:=BlockDiagonalMatrix[{x}];

Conj[U_,V_]:=U . V . ConjugateTranspose[U];

(*Frobenius inner product*)
Fp[U_,V_]:=Tr[ConjugateTranspose[U] . V];

ZeroMatrixQ[M_]:=MatrixQ[M,PossibleZeroQ];


(*Quantum gates*)
Id={{1,0},{0,1}};
H=1/Sqrt[2]{{1,1},{1,-1}};
S={{1,0},{0,I}};
T={{1,0},{0,Exp[I Pi/4]}};
X={{0,1},{1,0}};
Y={{0,-I},{I, 0}};
Z={{1,0},{0,-1}};
CX=Blocks[Id,X];
CCX=Blocks[Id,Id,Id,X];
CY=Blocks[Id,Y];
CCY=Blocks[Id,Id,Id,Y];
CZ=Blocks[Id,Z];
CCZ=Blocks[Id,Id,Id,Z];
NOT=X;
CNOT=CX;
CCNOT=CCX;


End[];
EndPackage[];
