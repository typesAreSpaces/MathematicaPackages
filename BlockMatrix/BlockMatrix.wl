(* ::Package:: *)

BeginPackage["BlockMatrix`"];


BlockMatrix::usage="BlockMatrix[m_] computes a block matrix containing 
\tthe input matrix in the indicated order with respect to their 
\tposition in the list.
* m is a List of matrices.";
ExtractFromBlockMatrix::usage="ExtractFromBlockMatrix[matrix_,sizes_List] computes
\ta list of matrices from a block matrix.
* matrix is a block Matrix, 
* size is a list with size of each block";


Begin["`Private`"];


BlockMatrix[m_]:=ArrayFlatten[Block[{dim=Length[m]},Table[If[i==j,m[[i]],0],{i,1,dim},{j,1,dim}]]]
ExtractFromBlockMatrix[matrix_,sizes_List]:=With[{
accumF=Function[x,
Block[{accum=0,sol=Table[0,{i,Length[x]}]},
For[i=1,i<=Length[x],i++,
sol[[i]]=accum;
accum=accum+x[[i]];
];
sol
]
]
},With[{accumL=accumF[sizes]},
Table[matrix[[accumL[[i]]+1;;accumL[[i]]+sizes[[i]],accumL[[i]]+1;;accumL[[i]]+sizes[[i]]]],{i,Length[sizes]}]
]]


End[];


EndPackage[];
