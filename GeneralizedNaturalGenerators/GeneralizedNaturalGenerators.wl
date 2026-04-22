(* ::Package:: *)

BeginPackage["GeneralizedNaturalGenerators`"];

GenNatGenerators::usage="GenNatGenerators[x_Symbol, G_List] computes
\tthe generalized natural generators of a basis G
* x is a symbol variable
* G is a list of polynomials";

Begin["`Private`"];

Needs["DorisAlgorithmCompactCase`"];
Needs["NonNegativityCheckUnivariate`"];
Needs["DebuggerMessage`"];

GeneralizedNaturalGeneratorsLevel = Max[
	DorisAlgorithmCompactCaseLevel,
	NonNegativityCheckUnivariateLevel, 
	DebuggerMessageLevel
] + 1;
DebuggerMessageInternal[code_] := DebuggerMessage[code, GeneralizedNaturalGeneratorsLevel];

monFunc[i_Integer, m_Integer, vectorOrders_List, x_Symbol, intervals_List, polarity_, leftOrRight_]:= 
If[
	i==0, 1, 
	If[i==m+1, -1, 
		With[
			{
				exp = Switch[polarity,
					"", vectorOrders[[i, 2]],
					"+", vectorOrders[[i, 3]],
					"-", vectorOrders[[i, 4]]
				],
				value = Switch[leftOrRight,
					"l", intervals[[i, 1, 1]],
					"r", intervals[[i, 1, 2]]
				]
			}, 
			(x-value)^exp
		]
	]
]

ineqToInterval[ineq_]:=
	Block[{size=Length[ineq]},
		If[size==5,
			Interval[{ineq[[1]],ineq[[5]]}],
			If[size==2,
				Block[{operator=ineq[[0]],num=ineq[[2]]},
					If[operator===LessEqual,
						Interval[{-Infinity,num}],
						If[operator===GreaterEqual,
							Interval[{num,Infinity}],
							If[operator==Equal,
								Interval[{num, num}],
								ineq
							]
						]
					]
				],
				ineq
			]
		]
	]
	
toIntervals[ineqs_]:=
	If[ineqs==={},
		{},
		If[ineqs[[0]]===Or,
			Block[{list=ineqs/.Or->List},
				Map[ineqToInterval,list]
			],
			{ineqToInterval[ineqs]}
		]
	]

GenNatGenerators[x_Symbol, G_List]:=
With[
	(*{intervals = InputNonNegativeIntervals[x, G]},*)
	{intervals = toIntervals[Reduce[G>=0,x]]},
	With[{
		size = Length[intervals],
		completeVectorOfOrders = Map[CompleteVectorOfOrders[x, #, G]&, intervals]
	},
		DebuggerMessageInternal[(Write[Global`COutputStream, "Complete vector of orders: ", completeVectorOfOrders])&];
		DebuggerMessageInternal[(Write[Global`COutputStream, "Input basis: ", G])&];
		DebuggerMessageInternal[(Write[Global`COutputStream, "Number of intervals: ", size])&];
		Join[
			Table[
				monFunc[i, size, completeVectorOfOrders, x, intervals, "-", "r"]*monFunc[i+1, size, completeVectorOfOrders, x, intervals, "+", "l"], 
				{i, 0, size}
			],
			Table[
				With[{
					omega = completeVectorOfOrders[[i, 2]],
					omegaPlus = completeVectorOfOrders[[i, 3]],
					omegaNeg = completeVectorOfOrders[[i, 4]],
					ai = intervals[[i, 1, 1]],
					bi = intervals[[i, 1, 2]]
				},
					If[Max[omega, omegaPlus, omegaNeg] != omega && ai == bi,
						monFunc[i-1, size, completeVectorOfOrders, x, intervals, "-", "r"]*monFunc[i, size, completeVectorOfOrders, x, intervals, "", "l"]*monFunc[i+1, size, completeVectorOfOrders, x, intervals, "+", "l"]
					]
				],
				{i, 1, size}
			]//Select[#,(Not[SameQ[#, Null]])&]&
		]
	]
];

End[];

EndPackage[];
