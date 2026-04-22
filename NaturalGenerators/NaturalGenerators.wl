(* ::Package:: *)

BeginPackage["NaturalGenerators`"];
NaturalGenerators::usage="NaturalGenerators[x_Symbol,intervals_List]
\tcomputes natural generators from the description of a semialgebraic set
\twhich in the univariate case is a list of intervals and isolated points.
* x is symbol
* interval is a list of Interval[{a, b}]";
Begin["`Private`"];
NaturalGenerators[x_Symbol,intervals_List]:=
With[{size=Length[intervals]},
	With[{ 
		inBetweenIntervals=Table[
			(x-intervals[[i,1,2]])(x-intervals[[i+1,1,1]]),
			{i,1,size-1}
		]
	},
		Join[
			inBetweenIntervals,
			If[size>0,
				With[{
					minPoint=intervals[[1,1,1]],
					maxPoint=intervals[[size,1,2]]
				},
					Switch[minPoint,
						-Infinity,Switch[maxPoint,Infinity,{},_,{maxPoint-x}],
						_,Switch[maxPoint,Infinity,{x-minPoint},_,{x-minPoint,maxPoint-x}]
					]
				]
			]
		]
	]
]
End[];
EndPackage[];
