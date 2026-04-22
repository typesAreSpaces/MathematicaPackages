(* ::Package:: *)

BeginPackage["TruncGaussian`"];


trunc::usage="trunc[x, n, a, b, c] computes a truncated Gaussian
* x is a variable
* n is the power of the truncated Gaussian, an integer
* a is amplitude of the Gauss, a real
* b is the x-point which the Gaussian reaches its maximum value, a real
* c is the spread of the square, a real";


Begin["`Private`"];


trunc[x_,n_,a_,b_,c_]:=a Sum[(-1)^k ((x-b)/c)^(2k)/(2^k k!),{k,0,2n}]


End[];


EndPackage[];
