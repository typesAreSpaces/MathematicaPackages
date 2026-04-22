(* ::Package:: *)

BeginPackage["DorisAlgorithmCompactCase`"];


kDataAtA::usage="kDataAtA[x_Symbol,fs_List,a_] computes a triple 
\t{c, d, e}, c = k_a^(fs), d = k_a^{+}(fs), and e = k_a^{-}(fs)
* x is a variable
* fs is a list of polynomials
* a is a real number";
KVectorAtA::usage="KVectorAtA[x_Symbol, fs_List, a_] computes a 
\ttriple {d, c, e}, c = k_a^(fs), d = k_a^{+}(fs), and e = k_a^{-}(fs)
* x is a variable
* fs is a list of polynomials
* a is a real number";
DorisAlgorithmCompactCaseLevel::usage="Defines a number which is greater than the DebuggingLevel of their package dependencies."
DataAtA::usage="DataAtA[x_Symbol,f_,a_] computes a pair 
\t{c, d} such that `c' is ord_a(f) and `d' eps_a(f)
* x is a variable
* f is a polynomial
* a is a real number";


CompleteVectorOfOrders::usage="CompleteVectorOfOrders[x_Symbol, interval_, G_List]
\tcomputes the output is the complete vector of order ((Type, omega_i, omega_i^+, omega_i^-)_i)
* 'x' is a symbol
* interval is just one interval of the form Interval[{a, b}]
* G is a list of polynomials";


DorisAlgorithmCompactCase::usage="DorisAlgorithmCompactCase[x_Symbol,g_,fs_List]
\treturns True if and only if g in QM(fs)
* x is variable
* g is a polynomial
* fs is a list of polynomials";


Begin["`Private`"];


Needs["NonNegativityCheckUnivariate`"]
Needs["DebuggerMessage`"]
DorisAlgorithmCompactCaseLevel = Max[NonNegativityCheckUnivariateLevel, DebuggerMessageLevel] + 1;
DebuggerMessageInternal[code_] := DebuggerMessage[code, DorisAlgorithmCompactCaseLevel];


Zip[l1_List,l2_List]:=Transpose[{l1,l2}]


(*Input: l : {Intervals[{a, b}]}, aux1 : {Intervals[{a, b}]}, aux2 : {Intervals[{a, b}]}*)
(*Output: aux1 contains the isolated points from l and aux2 the rest of the intervals of l*)
SplitListAux[{},aux1_List,aux2_List]:={aux1,aux2}
SplitListAux[l_List,aux1_List,aux2_List]:=
With[{head = First[l], tail=Drop[l,1]},
	If[SameQ[head[[1]][[1]],head[[1]][[2]]],
		SplitListAux[tail,Append[aux1,head],aux2],
		SplitListAux[tail,aux1,Append[aux2,head]]
	]
];
SplitList[l_List]:=SplitListAux[l,{},{}]


(*Input: x : Var, f : Poly[x], a : Real number, n : Integer*)
(*Output: Returns a pair {c, d} such that `c' is ord_a(f) and `d' eps_a(f)*)
DataAtAAux[x_Symbol,f_,a_,n_Integer]:=
With[{fDeriv=Simplify[D[f,x]], evalA=Simplify[f/.x->a]},
	If[SameQ[evalA,0],
		DataAtAAux[x,fDeriv,a,n+1],
		{n, If[evalA>0,1,-1]}
	]
]


DataAtA[x_Symbol,f_,a_]:=DataAtAAux[x,f,a,0]


(*Input: x : Var, fs : {Poly[x]}, a : Real number*)
(*Output: Returns a triple {c, d, e}, c = k_a^(fs), d = k_a^{+}(fs),
and e = k_a^{-}(fs)
*)
kDataAtA[x_Symbol,fs_List,a_]:=With[{points=Map[DataAtA[x,#,a]&,fs]},
	With[{
		kNoSign=Select[points,(And[Mod[#[[1]],2]==0,#[[2]]==-1])&],
		kPlus=Select[points,(And[Mod[#[[1]],2]==1,#[[2]]==1])&],
		kMinus=Select[points,(And[Mod[#[[1]],2]==1,#[[2]]==-1])&]
	},
		With[{
			minKNoSign=Fold[Min[#1,#2[[1]]]&,Infinity,kNoSign],
			minKPlus=Fold[Min[#1,#2[[1]]]&,Infinity,kPlus],
			minKMinus=Fold[Min[#1,#2[[1]]]&,Infinity,kMinus]
		},
			DebuggerMessageInternal[With[{},
				Write[Global`COutputStream, "Basis: ", fs];
				Write[Global`COutputStream, "Points: ", points];
				Write[Global`COutputStream, "kNoSign: ", kNoSign];
				Write[Global`COutputStream, "kPlus: ", kPlus];
				Write[Global`COutputStream, "kMinus: ", kMinus];
			]&];
			{minKNoSign,minKPlus,minKMinus}
		]
	]
]
KVectorAtA[x_Symbol, fs_List, a_]:=
With[{sol=kDataAtA[x,fs,a]},
	With[{k=sol[[1]],kPlus=sol[[2]],kMinus=sol[[3]]},
		{kPlus, k, kMinus}
	]
]


(*Input: x : Var, l : Non Isolated Intervals of fs, g : Poly[x], fs : {Poly[x]}*)
(*Output: \forall i \in l . let a = LeftBoundary(i) in EvenQ[ord_a(g)] \lor ord_a(g)\[GreaterEqual] k_a^{+}(fs) *)
ConditionOne[x_Symbol,l_List,g_,fs_List]:=
With[{},
	DebuggerMessageInternal[With[{},
		Write[Global`COutputStream, "--Checking First Condition"];
		Write[Global`COutputStream,"--This condition is true if for all left boundaries 'a' it is the case that ord_a(g) is even or ord_a(g) >= k_a^+(fs)"];
	]&];
With[{
	LeftPoints=Select[Map[#[[1]][[1]]&,l],Not[SameQ[#,-Infinity]]&]
},	
	DebuggerMessageInternal[With[{},
		Write[Global`COutputStream, "The testing polynomial is : ", g];
		Write[Global`COutputStream, "The basis is : ", fs//Simplify];
		Write[Global`COutputStream, "The left boundary points are: ", LeftPoints];
		Write[Global`COutputStream, ""];
	]&];
	With[{
		gOrdA=Map[DataAtA[x,g,#][[1]]&,LeftPoints],
		fsKaPlus=Map[kDataAtA[x,fs,#][[2]]&,LeftPoints]
	},
		DebuggerMessageInternal[With[{},
			Write[Global`COutputStream, "The ord values of testing polynomial are : ", gOrdA];
			Write[Global`COutputStream, "The k^+ vector values of the basis are : ", fsKaPlus];
			Write[Global`COutputStream, ""];
		]&];
		Fold[
			And[#1,#2]&,True,
			Map[
				Or[Mod[#[[1]],2]==0,#[[1]]>=#[[2]]]&,
				Zip[gOrdA,fsKaPlus]
			]
		]
	]
]
]


(*Input: x : Var, l : Non Isolated Intervals of fs, g : Poly[x], fs : {Poly[x]}*)
(*Output: \forall i \in l . let a = RightBoundary(i) in EvenQ[ord_a(g)] \lor ord_a(g)\[GreaterEqual] k_a^{-}(fs) *)
ConditionTwo[x_Symbol,l_List,g_,fs_List]:=With[{},
DebuggerMessageInternal[With[{},
	Write[Global`COutputStream, "--Checking Second Condition"];
	Write[Global`COutputStream, "--This condition is true if for all right boundaries 'a' it is the case that ord_a(g) is even or ord_a(g) >= k_a^-(fs)"];
]&];
With[{
	RightPoints=Select[Map[#[[1, 2]]&,l],Not[SameQ[#,Infinity]]&]
},
	DebuggerMessageInternal[With[{},
		Write[Global`COutputStream, "The testing polynomial is : ", g];
		Write[Global`COutputStream, "The basis is : ", fs//Simplify];
		Write[Global`COutputStream, "The right boundary points are: ", RightPoints];
		Write[Global`COutputStream, ""];
	]&];
	With[{
		gOrdA=Map[DataAtA[x,g,#][[1]]&,RightPoints],
		fsKaMinus=Map[kDataAtA[x,fs,#][[3]]&,RightPoints]
	},
		DebuggerMessageInternla[With[{},
			Write[Global`COutputStream, "The ord values of testing polynomial are : ", gOrdA];
			Write[Global`COutputStream, "The k^- vector values of the basis are : ", fsKaMinus];
			Write[Global`COutputStream, ""];
		]&];
		Fold[
			And[#1,#2]&, True, 
			Map[
				Or[Mod[#[[1]],2]==0,#[[1]]>=#[[2]]]&,
				Zip[gOrdA,fsKaMinus]
			]
		]
	]
]
]


(*Input: x : Var, l : Isolated Intervals of fs, g : Poly[x], fs : {Poly[x]}*)
(*
Output: \forall i \in l . (EvenQ[ord_a(g)] \land eps_a(g) = 1) \lor 
Case 1: min(k_a(fs), k_a^{+}(fs), k_a^{-})(fs)) = k_a(fs): ord_a(g)\[GreaterEqual] k_a(fs) 
Case 2: min(k_a(fs), k_a^{+}(fs), k_a^{-})(fs)) = k_a^{+}(fs): (OddQ[ord_a(g)] \land eps_a(g)=1 \land ord_a(gs)\[GreaterEqual] k_a^{+}(fs)) \lor ord_a(g)\[GreaterEqual] min(k_a^{-}(fs),k_a(fs))
Case 3: min(k_a(fs), k_a^{+}(fs), k_a^{-})(fs)) = k_a^{-}(fs): (OddQ[ord_a(g)] \land eps_a(g)=-1 \land ord_a(gs)\[GreaterEqual] k_a^{-}(fs)) \lor ord_a(g)\[GreaterEqual] min(k_a^{+}(fs),k_a(fs))
*)
ConditionThree[x_Symbol,IsolatedPoints_List,g_,fs_List]:=With[{},
DebuggerMessageInternal[With[{},
	Write[Global`COutputStream, "--Checking Third Condition"];
	Write[Global`COutputStream, "--This condition is true if:"];
	Write[Global`COutputStream, "Case 1: min(k_a(fs), k_a^{+}(fs), k_a^{-})(fs)) = k_a(fs): ord_a(g)\[GreaterEqual] k_a(fs)"];
	Write[Global`COutputStream, "Case 2: min(k_a(fs), k_a^{+}(fs), k_a^{-})(fs)) = k_a^{+}(fs): (OddQ[ord_a(g)] and eps_a(g)=1 and ord_a(gs)\[GreaterEqual] k_a^{+}(fs)) or ord_a(g)\[GreaterEqual] min(k_a^{-}(fs),k_a(fs))"];
	Write[Global`COutputStream, "Case 3: min(k_a(fs), k_a^{+}(fs), k_a^{-})(fs)) = k_a^{-}(fs): (OddQ[ord_a(g)] and eps_a(g)=-1 and ord_a(gs)\[GreaterEqual] k_a^{-}(fs)) or ord_a(g)\[GreaterEqual] min(k_a^{+}(fs),k_a(fs))"];
	Write[Global`COutputStream, "The testing polynomial is : ", g];
	Write[Global`COutputStream, "The basis is : ", fs//Simplify];
	Write[Global`COutputStream, "The isolated points are: ", IsolatedPoints];
]&];
With[{
	gOrdA=Map[DataAtA[x,g,#]&,IsolatedPoints],
	fsK=Map[kDataAtA[x,fs,#]&,IsolatedPoints]
},
	DebuggerMessageInternal[With[{},
		Write[Global`COutputStream, "The ord values of testing polynomial are : ", gOrdA//Map[#[[1]]&,#]&];
		Write[Global`COutputStream, "The epsilon values of testing polynomial  are : ", gOrdA//Map[#[[2]]&,#]&];
		Write[Global`COutputStream, "The k,k^+,k^- vector values of the basis are : ", fsK];
		Write[Global`COutputStream, ""];
	]&];
	With[{
		conditionsFirstPart=Map[And[Mod[#[[1]],2]==0,#[[2]]==1]&,gOrdA],
		conditionsSecondPart=Map[
			With[{
				CurrentgOrdA=#[[1]][[1]],
				CurrentgSignA=#[[1]][[2]],
				CurrentkNoSignA=#[[2]][[1]],
				CurrentkPlusA=#[[2]][[2]],
				CurrentkMinusA=#[[2]][[3]]
			},
				Switch[Min[CurrentkNoSignA,CurrentkPlusA,CurrentkMinusA],
					CurrentkNoSignA, CurrentgOrdA>=CurrentkNoSignA,
					CurrentkPlusA, Or[
						And[Mod[CurrentgOrdA,2]==1,And[CurrentgSignA==1,CurrentgOrdA>= CurrentkPlusA]],
						CurrentgOrdA>=Min[CurrentkMinusA,CurrentkNoSignA]
					],
					CurrentkMinusA, Or[
						And[Mod[CurrentgOrdA,2]==1,And[CurrentgSignA==-1,CurrentgOrdA>= CurrentkMinusA]],
						CurrentgOrdA>=Min[CurrentkPlusA,CurrentkNoSignA]
					]
				]
			]&,
			Zip[gOrdA,fsK]
		]
	},
		DebuggerMessageInternal[With[{},
			Write[Global`COutputStream, ""];
		]&];
		Fold[
			And[#1,#2]&,
			True,
			Map[Or[#[[1]],#[[2]]]&,Zip[conditionsFirstPart,conditionsSecondPart]]
		]
	]
]
]


(*Input: x : Var, g : Poly[x], fs : {Poly[x]}*)
(*Output: True if and only if g \in QM(fs)*)
DorisAlgorithmCompactCase[x_Symbol,g_,fs_List]:=
With[{intervals=SplitList[InputNonNegativeIntervals[x,fs]]},
	With[{
		IsolatedPoints=Map[#[[1]][[1]]&,intervals[[1]]],
		NonIsolatedIntervals=intervals[[2]]
	},
		DebuggerMessageInternal[With[{},
			Write[Global`COutputStream, "* Executing DorisAlgorithmCompactCase with *"];
			Write[Global`COutputStream, "Symbol: ", x];
			Write[Global`COutputStream, "Testing polynomial: ", g]; 
			Write[Global`COutputStream, "Basis: ", fs]; 
			Write[Global`COutputStream, ""];
		]&];
		With[{
			nonnegativity=SameQ[Reduce[Implies[Fold[And[#1,#2]&,True,Map[#>=0&,fs]],g>=0], x, Reals], True],
			cond1=ConditionOne[x,NonIsolatedIntervals,g,fs],
			cond2=ConditionTwo[x,NonIsolatedIntervals,g,fs],
			cond3=ConditionThree[x,IsolatedPoints,g,fs]
		},
			And[nonnegativity,And[cond1,And[cond2,cond3]]]
		]
	]
]


CompleteVectorOfOrders[x_Symbol, interval_, G_List]:=
With[{
	a=interval[[1,1]], 
	b=interval[[1,2]]
},
	With[{kTupleA = kDataAtA[x, G, a]},
		If[a != b,
			With[{
				kTupleB = kDataAtA[x, G, b]
			},
				{"IntervalType", Infinity, kTupleA[[2]], kTupleB[[3]]}
			],
			With[{
				kVar = kTupleA[[1]],
				kPlus = kTupleA[[2]],
				kMinus = kTupleA[[3]]
			},
				If[kVar < kPlus && kVar < kMinus, {"A", kVar, kVar + 1, kVar + 1},
					If[kVar > kPlus && kVar > kMinus, {"B", Max[kPlus, kMinus] + 1, kPlus, kMinus},
						If[kPlus < kVar && kVar < kMinus, {"C", kVar, kPlus, kVar + 1},
							If[kMinus < kVar && kVar < kPlus, {"D", kVar, kVar + 1, kMinus},
								{"Error"}
							]
						]
					]
				]
			]
		]
	]
]


End[];


EndPackage[];
