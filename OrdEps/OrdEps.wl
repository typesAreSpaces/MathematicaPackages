(* ::Package:: *)

BeginPackage["OrdEps`"];

ord::usage="ord[f_,x_,a_]";
eps::usage="eps[f_,x_,a_]";

Begin["`Private`"];

ordAux[f_,x_,a_,acc_]:=
	Block[{q,r},
		{q,r}=PolynomialQuotientRemainder[f,(x-a),x];
		If[r!=0,acc,ordAux[q,x,a,acc+1]]
	];
ord[f_,x_,a_]:=ordAux[f,x,a,0];
ord[f_,a_]:=ord[f,x,a];
eps[f_,x_,a_]:=If[Evaluate[f/.x->a+1/1000]>0,1,-1];
eps[f_,a_]:=eps[f,x,a];

End[];

EndPackage[];
