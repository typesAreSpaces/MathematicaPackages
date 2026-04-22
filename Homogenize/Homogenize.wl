(* ::Package:: *)

BeginPackage["Homogenize`"];


HomogenizeExcludingCWithH::usage="HomogenizeExcludingCWithH[f_,c_,H_]
computes a homogeneous polynomial excluding H
* f is a polynomial
* c is a parameter to exclude (it has no weight)
* H is the polynomial to homogenize with";


Begin["`Private`"];


Needs["PolyDegree`"];


HomogenizeExcludingCWithH[f_,c_,H_]:=
With[{f1=Expand[f]},
	With[{list=List@@f1},
		With[{tolift=
			With[{deg=PolyDegree[f1/.c->1]},
				Map[
					H^If[NumericQ[#],deg,
						With[{curdeg=Fold[(#1+#2)&,0,
							Map[
								If[ListQ[#],#[[2]],1]&,
								Select[
									Map[#/.Power->List&,
										With[{listterms=#/.Times->List},
											If[!ListQ[listterms],{listterms},listterms]
										]
									],
									ListQ[#]||!(NumericQ[#]||SameQ[#,c])&
								]
							]
						]}, deg-curdeg]
					]&,
				Map[#/.Times->List&,list]]
			]},
			Fold[#1+#2&,0,
				Table[tolift[[i]]*list[[i]],{i,1,Length[tolift]}]
			]
		]
	]
]


End[];


EndPackage[];
