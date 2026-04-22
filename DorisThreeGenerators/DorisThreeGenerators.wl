(* ::Package:: *)

BeginPackage["DorisThreeGenerators`"];

OmegaPlusMinusVector::usage="OmegaPlusMinusVector[x_Symbol,intervals_List,G_List]
\tcomputes omega plusminus vector as defined on page 56 of Doris thesis
* x is a symbol
* intervals is a list of Interval[{a, b}]
* G is a list of polynomials;"
DorisThreeGenerators::usage="DorisThreeGenerators[x_Symbol,G_List]
\tcomputes the three generators of the Doris basis of a given 
\tbasis G, i.e., returns {intervals, omegaplusminus vector, hNeg, hPos, hVar}
* x is a symbol
* G is a list of polynomials;"
DorisThreeGeneratorsLevel::usage="Defines a number which is greater than the DebuggingLevel of their package dependencies."

Begin["`Private`"];

Needs["NonNegativityCheckUnivariate`"];
Needs["DorisAlgorithmCompactCase`"];
Needs["DebuggerMessage`"];

DorisThreeGeneratorsLevel = Max[
	NonNegativityCheckUnivariateLevel, 
	DebuggerMessageLevel, 
	DorisAlgorithmCompactCaseLevel
] + 1;
DebuggerMessageInternal[code_] := DebuggerMessage[code, DorisThreeGeneratorsLevel];
 
(*Definition @ Page 56*)
OmegaPlusMinusVector[x_Symbol,intervals_List,G_List]:=Table[
	With[{ai=intervals[[i,1,1]],bi=intervals[[i,1,2]]},
		If[ai==bi,
			With[{kTupleA=kDataAtA[x,G,ai]},
				With[{
					ka=kTupleA[[1]],
					kaPos=kTupleA[[2]],
					kaNeg=kTupleA[[3]]
				},
					If[ka<kaPos&&ka<kaNeg(*Type A*), {"A",ka,ka+1,ka+1},
						If[ka>kaPos&&ka>kaNeg(*Type B*), {"B",Max[kaPos,kaNeg]+1,kaPos,kaNeg},
							If[kaPos<ka&&ka<kaNeg(*Type C*), {"C",ka,kaPos,ka+1},
								If[kaNeg<ka&&ka<kaPos(*Type D*), {"D",ka,ka+1,kaNeg},
									{"Error"}
								]
							]
						]
					]
				]
			],
			With[{kTupleA=kDataAtA[x,G,ai],kTupleB=kDataAtA[x,G,bi]},
				With[{kaPos=kTupleA[[2]], kbNeg=kTupleB[[3]]},
					{"Interval",Infinity,kaPos,kbNeg}
				]
			]
		]
	],
	{i,Length[intervals]}
]

DorisThreeGenerators[x_Symbol,G_List]:=
	With[{intervals=InputNonNegativeIntervals[x,G]},
		With[{omegaplusminus=OmegaPlusMinusVector[x,intervals,G]},
			With[{size=Length[intervals]},
				DebuggerMessageInternal[With[{},
					Write[Global`COutputStream, "* Executing DorisThreeGenerators with *"];
					Write[Global`COutputStream, "Symbol: ", x];
					Write[Global`COutputStream, "Basis: ", G]; 
					Write[Global`COutputStream, ""];
					Write[Global`COutputStream, "Intervals of original basis: ", intervals]; 
					Write[Global`COutputStream, "Complete vector of orders of original basis : ", omegaplusminus];
					Write[Global`COutputStream, ""]]& 
				];
				Block[{
					hAux=1,
					hNeg=-1,
					hPos=1,
					hVar=If[(size>=2&&omegaplusminus[[2,1]]=="C"),-1,1],
					signVar=If[(size>=2&&omegaplusminus[[2,1]]=="C"),-1,1]
				},
					Table[
						With[{
							type=omegaplusminus[[i,1]],
							omegai=omegaplusminus[[i,2]],
							omegaiPos=omegaplusminus[[i,3]],
							omegaiNeg=omegaplusminus[[i,4]],
							ai=intervals[[i,1,1]],
							bi=intervals[[i,1,2]]
						},
							DebuggerMessageInternal[With[{},
								Write[Global`COutputStream, "=> Current interval #",i, " is {",ai,", ",bi,"}" ];
								Write[Global`COutputStream, "=> Current type ", type];
								Write[Global`COutputStream, "hVar before entering body loop: ", hVar];
								Write[Global`COutputStream, "hNeg before entering  body loop: ", hNeg];
								Write[Global`COutputStream, "hPos before entering  body loop: ", hPos];
								Write[Global`COutputStream, "Omega vector plus/minus of H before entering body loop ", OmegaPlusMinusVector[x, intervals, {hNeg, hPos, hVar}]];
								Write[Global`COutputStream, "eps bi of hNeg ", DataAtA[x, hNeg, bi][[2]]];
								Write[Global`COutputStream, "eps bi of hPos ", DataAtA[x, hPos, bi][[2]]];
								Write[Global`COutputStream, "Current intervals of new basis ", InputNonNegativeIntervals[x, {hNeg, hPos, hVar}]];
							]&];
							If[ai<bi,
								DebuggerMessageInternal[(Write[Global`COutputStream, "*Interval case"])&];
								hNeg=hNeg (x-ai)^omegaiPos(x-bi)^omegaiNeg;
								hVar=If[signVar==-1,
									If[i!=size&&omegaplusminus[[i+1,1]]=="C",
										hVar (x-ai)^omegaiPos(x-bi)^omegaiNeg,
										-hVar(x-ai)^omegaiPos
									],
									If[i!=size&&omegaplusminus[[i+1,1]]=="C",
										-hVar(x-bi)^omegaiNeg,
										hVar
									]
								];,
								
								Switch[type,
									"A",
										DebuggerMessageInternal[(Write[Global`COutputStream, "*Isolated point case Type A"])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "kData at ", ai, " of H (before) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										hNeg=hNeg (x-ai)^omegai;
										hPos=hPos;
										hVar=If[signVar==-1,
											If[i!=size&&omegaplusminus[[i+1,1]]=="C",
												hVar (x-ai)^omegai,
												-hVar(x-ai)^omegaiPos
											],
											If[i!=size&&omegaplusminus[[i+1,1]]=="C",
												-hVar(x-bi)^omegaiNeg,
												hVar
											]
										];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of original basis is ", KVectorAtA[x, G, ai]])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "kData at ", ai, " of H (after) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										,
									"B",
										DebuggerMessageInternal[(Write[Global`COutputStream, "*Isolated point case Type B"])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of H (before) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										hAux=hNeg;
										hNeg=-hPos(x-bi)^omegaiNeg;
										hPos=-hAux(x-ai)^omegaiPos;
										hVar=If[signVar==-1,
											If[i!=size&&omegaplusminus[[i+1,1]]=="C",
												hVar (x-ai)^omegai,
												-hVar(x-ai)^omegaiPos
											],
											If[i!=size&&omegaplusminus[[i+1,1]]=="C",
												-hVar(x-bi)^omegaiNeg,
												hVar
											]
										];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of original basis is ", KVectorAtA[x, G, ai]])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of H (after) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										,
									"C",
										DebuggerMessageInternal[(Write[Global`COutputStream, "*Isolated point case Type C"])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of H (before) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										hAux=hPos;
										hNeg=hNeg (x-ai)^omegai;
										hPos=-hVar(x-ai)^omegaiPos;
										hVar=If[i!=size&&omegaplusminus[[i+1,1]]=="C",
											-hAux(x-bi)^omegaiNeg,
											hAux
										];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of original basis is ", KVectorAtA[x, G, ai]])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of H (after) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										,
									"D",
										DebuggerMessageInternal[(Write[Global`COutputStream, "*Isolated point case Type D"])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of H (before) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										hAux=hVar;
										hNeg=hNeg (x-ai)^omegai;
										hVar=-hPos(x-bi)^omegaiNeg;
										hPos=If[signVar==-1,
											-hAux(x-ai)^omegaiPos,
											hAux
										];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of original basis is ", KVectorAtA[x, G, ai]])&];
										DebuggerMessageInternal[(Write[Global`COutputStream, "- kData at ", ai, " of H (after) is ", KVectorAtA[x, {hNeg, hPos, hVar}, ai]])&];
										,
									_, "WrongCase"
								]
							];
							DebuggerMessageInternal[With[{},
								Write[Global`COutputStream, "hVar after leaving body loop: ", hVar];
								Write[Global`COutputStream, "hNeg after leaving body loop: ", hNeg];
								Write[Global`COutputStream, "hPos after leaving body loop: ", hPos];
								Write[Global`COutputStream, "Omega vector plus/minus of H before entering body loop ", OmegaPlusMinusVector[x, intervals, {hNeg, hPos, hVar}]];
								]&
							];
							DebuggerMessageInternal[(Write[Global`COutputStream, "signVar before last body loop step ", signVar])&];
							signVar=If[(i!=size&&omegaplusminus[[i+1,1]]=="C")||type=="D",-1,1];
							DebuggerMessageInternal[(Write[Global`COutputStream, "signVar after last body loop step ", signVar])&];
							DebuggerMessageInternal[(Write[Global`COutputStream, ""])&]; 1
						],
						{i,size}
					];
					DebuggerMessageInternal[With[{},
						Write[Global`COutputStream, "Final value of hVar: ", hVar];
						Write[Global`COutputStream, "Final value of hNeg: ", hNeg];
						Write[Global`COutputStream, "Final value of hPos: ", hPos];]&
					];
				DebuggerMessageInternal[With[{},
					Write[Global`COutputStream, "Intervals of new basis: ", InputNonNegativeIntervals[x,{hNeg, hPos, hVar}]]; 
					Write[Global`COutputStream, "Complete vector of orders of new basis : ", OmegaPlusMinusVector[x, intervals, {hNeg, hPos, hVar}]];
					Write[Global`COutputStream, "Current intervals of new basis ", InputNonNegativeIntervals[x, {hNeg, hPos, hVar}]];
					Write[Global`COutputStream, ""];
				&]];
				{intervals,omegaplusminus,hNeg,hPos,hVar}
			]
		]	
	]
]

End[];

EndPackage[];
