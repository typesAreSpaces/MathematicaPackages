(* ::Package:: *)

BeginPackage["CauchyBounds`"];


CauchyBounds::usage=""


Begin["`Private`"];


CauchyBounds[poly_, var_] := Module[
    {coeffs, an, bound},
    coeffs = CoefficientList[poly, var];
    an = Last[coeffs]; (*Leading coefficient*)
    bound = Fold[#1+Abs[#2]/Abs[an]&, 0, coeffs]
    
]


End[];


EndPackage[];
