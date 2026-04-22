(* ::Package:: *)

BeginPackage["NonNegativityCheckUnivariate`"];


InputNonNegativeIntervals::usage="InputNonNegativeIntervals[x, G]
\tcomputes a list with Interval[{a_i, b_i}] such that 
\tSemialgebraic(fs) = \bigcup_i Interval[{a_i, b_i}]
* x is a symbol variable
* G is a list of polynomials";
NonNegativityCheckUnivariate::usage="NonNegativityCheckUnivariate[x, g, G]
\tchecks if g in SemiAlgebraic(G).
* x is a symbol variable
* g is a polynomial
* G is a list of polynomials";
NonNegativityCheckUnivariateLevel::usage=""


Begin["`Private`"];
Needs["DebuggerMessage`"];
NonNegativityCheckUnivariateLevel = DebuggerMessageLevel + 1;
DebuggerMessageInternal[code_] := DebuggerMessage[code, NonNegativityCheckUnivariateLevel];


MapToList[m_Association]:=KeyValueMap[Flatten[{##}]&,m]


CrossProd[l1_List,l2_List]:=Flatten[Table[{l1[[i]],l2[[j]]},{i,1,Length[l1]},{j,1,Length[l2]}],1]


Zip[l1_List,l2_List]:=Transpose[{l1,l2}]


(*Input: l is {{x \[Rule] a}} where a is a root, m is auxiliar Associative data structure*)
(*Output: A list of real roots*)
RealRootFilter[l_List,m_Association]:=
If[Length[l]==0,
m,
With[{
head=First[l][[1]][[2]],
tail=Drop[l,1]
},
If[Im[head]==0,
If[KeyExistsQ[m,head],
RealRootFilter[tail,ReplacePart[m,Key[head]->m[head]+1]],
RealRootFilter[tail,Append[m,head->1]]
],
RealRootFilter[tail,m]
]
]
]


(*Input: m : Associative data structure*)
(*Output: Returns a list of (singleton) intervals of real roos with even multiplicity
of some polynomial*)
ExtractEvenRootInfo[m_Association]:=Map[Interval[#[[1]],#[[1]]]&,Select[MapToList[m],EvenQ[#[[2]]]&]]


(*Input: `open' is an open interval of the form Interval[{a, b}],
`closed' is an closed interval of the form Interval[{a, b}]*)
(*Output: True iff the intersection of `open' and `closed' is non-empty*)
IntersectOpenAndClose[open_Interval,closed_Interval]:=With[{
a=open[[1]][[1]],
b=open[[1]][[2]],
c=closed[[1]][[1]],
d=closed[[1]][[2]]},
(c<d&&((c<b<=d&&a<b)||(b>d&&a<d)))||(c==d&&b>d&&a<d)
]


(*Input: x : Var, f : Poly[x], m : Associative data structure*)
(*Output: A list of pairs (closed intervals) of real numbers including -Infinity, Infinity 
where f is non-negative*)
GenerateNonNegativeIntervals[x_Symbol,f_,m_Association]:=
With[{
deg=Exponent[f,x],
extendedPoints=Append[Prepend[
Map[#[[1]]&,Select[MapToList[m],OddQ[#[[2]]]&]],
-Infinity],Infinity]
},
With[{
coeff=Switch[deg,-Infinity,0,0,f,_,Coefficient[f,x^deg]],
numPoints=Length[extendedPoints]
},
Switch[Mod[numPoints,2],
0,Switch[Sign[coeff],
1,Table[{extendedPoints[[i]],extendedPoints[[i+1]]},{i,1,numPoints,2}],
-1,Table[{extendedPoints[[i+1]],extendedPoints[[i+2]]},{i,1,numPoints-2,2}],
0,Message["Error: polynomial cannot be the zero polynomial"]],
1,Switch[Sign[coeff],
1,Table[{extendedPoints[[i+1]],extendedPoints[[i+2]]},{i,1,numPoints-2,2}],
-1,Table[{extendedPoints[[i]],extendedPoints[[i+1]]},{i,1,numPoints-2,2}],
0,Message["Error: polynomial cannot be the zero polynomial"]]
]
]
]


(*Input: x : Var, f : Poly[x], m : Associative data structure*)
(*Output: A list of pairs (open intervals) of real numbers including -Infinity, Infinity 
where f is negative*)
GenerateNegativeIntervals[x_Symbol,f_,m_Association]:=
With[{
deg=Exponent[f,x],
extendedPoints=Append[Prepend[
Map[#[[1]]&,Select[MapToList[m],OddQ[#[[2]]]&]],
-Infinity],Infinity]
},
With[{
coeff=Switch[deg,-Infinity,0,0,f,_,Coefficient[f,x^deg]],
numPoints=Length[extendedPoints]
},
Switch[Mod[numPoints,2],
0,Switch[Sign[coeff],
1,Table[{extendedPoints[[i+1]],extendedPoints[[i+2]]},{i,1,numPoints-2,2}],
-1,Table[{extendedPoints[[i]],extendedPoints[[i+1]]},{i,1,numPoints-1,2}],
0,Message["Error: polynomial cannot be the zero polynomial"]],
1,Switch[Sign[coeff],
1,Table[{extendedPoints[[i]],extendedPoints[[i+1]]},{i,1,numPoints-2,2}],
-1,Table[{extendedPoints[[i+1]],extendedPoints[[i+2]]},{i,1,numPoints-2,2}],
0,Message["Error: polynomial cannot be the zero polynomial"]]
]
]
]


(*Input: todo : {Intervals[{Real, Real}]}, 
toremove : {Intervals[{Real, Real}]} (singletons), 
aux : {Intervals[{Real, Real}]}}*)
(*Output: the resulting list removes the singleton points in toremove from todo *)
RefineTestingIntervals[{},_,aux_]:=aux;
RefineTestingIntervals[todo_List,{},_]:=todo;
RefineTestingIntervals[todo_List,toremove_List,aux_List]:=With[{
headTodo=First[todo],tailTodo=Drop[todo,1],
pointToRemove=First[toremove][[1]][[1]],tailToRemove=Drop[toremove,1]
},
If[IntervalMemberQ[headTodo,pointToRemove],
With[{
lowerInterval=Interval[{headTodo[[1]][[1]],pointToRemove}],upperInterval=Interval[{pointToRemove,headTodo[[1]][[2]]}]
},
RefineTestingIntervals[Prepend[tailTodo,upperInterval],tailToRemove,Append[aux,lowerInterval]]
],
RefineTestingIntervals[tailTodo,toremove,Append[aux,headTodo]]
]
]


(*Input: x : Var, g : Poly[x]*)
(*Output: TODO*)
TestingNegativeIntervals[x_Symbol,g_]:=With[{
gRoots=RealRootFilter[Solve[g==0,x],<||>]
},
With[{
gOddIntervals=Map[Interval[#]&,GenerateNegativeIntervals[x,g,gRoots]],
gEvenRoots=ExtractEvenRootInfo[gRoots]
},
RefineTestingIntervals[gOddIntervals,gEvenRoots,{}]
]
]


(*Input: set1 and set2 are lists of Interval[{a, b}]*)
(*Output: list which contains intervals which are the intersection
of the intervals in set1 and set2*)
RefineInputIntervals[set1_List,set2_List]:=
With[{refined=Map[IntervalIntersection[#[[1]],#[[2]]]&,CrossProd[set1,set2]]},
	Select[refined,Not[SameQ[#,Interval[]]]&]
]


(*Input: x : Var, fs : {Poly[x]}*)
(*Output: returns a list with Interval[{a_i, b_i}] such that Semialgebraic(fs) = \bigcup_i Interval[{a_i, b_i}]*)
InputNonNegativeIntervals[x_Symbol,fs_List]:=
With[
{
	intervals = Fold[
		RefineInputIntervals[#1,#2]&,
		{Interval[{-Infinity,Infinity}]},
		With[{fnRoots=Map[RealRootFilter[Solve[#==0,x],<||>]&,fs]},
			With[{
				fnOddIntervals=Map[Map[Interval,#]&,Map[GenerateNonNegativeIntervals[x,#[[1]],#[[2]]]&,Zip[fs,fnRoots]]],
				fnEvenIntervals=Map[ExtractEvenRootInfo,fnRoots]
			},
				Map[Join[#[[1]],#[[2]]]&,Zip[fnOddIntervals,fnEvenIntervals]]
			]
		]
	]//Fold[IntervalUnion,Interval[],#]&
},
	Table[Interval[intervals[[i]]],{i, Length[intervals]}]
]


(*Input: x : Var, g : Poly[x], fs : {Poly[x]}*)
(*Output: True iff g_ \in SemiAlgebraic(fs)*)
NonNegativityCheckUnivariate[x_Symbol,g_,fs_List]:=
Not[
Fold[#1||#2&,False,
Map[
IntersectOpenAndClose[#[[1]],#[[2]]]&,
CrossProd[
TestingNegativeIntervals[x,g],
InputNonNegativeIntervals[x,fs]
]
]
]
]


End[];


EndPackage[];
