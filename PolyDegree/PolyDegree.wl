(* ::Package:: *)

BeginPackage["PolyDegree`"];


PolyDegree::usage="PolyDegree[poly] computes the total degree
\tof a polynomial poly
* poly is a polynomial";
PolyDegreeVar::usage="PolyDegreeVar[poly,x] computes the total degree
\tof a polynomial poly with respect to the variable x.
* x is a symbol variable
* poly is a polynomial";


Begin["`Private`"];


PolyDegree[poly_]:=Max@Exponent[MonomialList[poly]/.Thread[Variables[poly]->\[FormalX]],\[FormalX]];
AuxPolyDegreeVar[poly_,x_,accum_]:=If[poly===0,accum,AuxPolyDegreeVar[D[poly,x],x,accum+1]];
PolyDegreeVar[poly_,x_]:=AuxPolyDegreeVar[poly,x,-1];


End[];


EndPackage[];
