(* ::Package:: *)

BeginPackage["WeifengTwoGenerators`"];

WeifengSignatureWithRoots::usage="WeifengSignatureWithRoots[x_Symbol,G_List] computes the Weifeng Signature
\tof the polynomial f with respect to the basis G including information of roots and intervals.
* x is a symbol variable
* G is a list of polynomials";
WeifengSignatureExt::usage="WeifengSignatureExt[x, f, G] computes the Weifeng Signature
\tof the polynomial f with respect to the basis G.
* x is a symbol variable
* f is a polynomial
* G is a list of polynomials";
WeifengSignature::usage="WeifengSignature[x,intervals,G] computes the Weifeng Signature
\tof a basis G with respect to the intervals given.
WeifengSignature[x_Symbol,G_List] computes the Weifeng Signature
\tof a basis G with respect to SemiAlgebraic(G)
* x is a symbol variable
* intervals is a list of Intervals[{a, b}]
* G is a list of polynomials";

WeifengTwoGens::usage="WeifengTwoGens[x_Symbol, G_List] computes the 
\t2-basis generator Weifeng basis
* x is a symbol variable
* G is a list of polynomials";

Begin["`Private`"];

Needs["NonNegativityCheckUnivariate`"];
Needs["DorisAlgorithmCompactCase`"];
Needs["DebuggerMessage`"];

WeifengTwoGensLevel = Max[NonNegativityCheckUnivariateLevel, DorisAlgorithmCompactCaseLevel, DebuggerMessageLevel] + 1;
DebuggerMessageInternal[code_] := DebuggerMessage[code, WeifengTwoGensLevel]; 

WeifengSignature[x_Symbol,intervals_List,G_List]:= 
  Map[
	  Function[interval,
		  With[{asPair=interval[[1]]},
		    With[
          {
            a=asPair[[1]],
			      b=asPair[[2]]
          },
			    With[
            {
              kTupleA=kDataAtA[x,G,a],
              kTupleB=kDataAtA[x,G,b]
            },
				    With[
              {
                ka=kTupleA[[1]],
				        kaPos=kTupleA[[2]],
				        kaNeg=kTupleA[[3]],
				        kb=kTupleB[[1]],
				        kbPos=kTupleB[[2]],
				        kbNeg=kTupleB[[3]]
              },
				      If[a!=b, 
                {"Interval",Infinity,kaPos,kbNeg},
                  If[ka<kaPos && ka<kaNeg,
                    {"A",ka,ka+1,ka+1},
                      If[ka>kaPos&&ka>kaNeg,
                        {"B",Max[kaPos,kaNeg]+1,kaPos,kaNeg},
                          If[kaPos<ka&&ka<kaNeg,
                            {"C",ka,kaPos,ka + 1},
                              If[kaNeg<ka&&ka<kaPos,
                                {"D",ka,ka+1,kaNeg},
                                  If[ka==Infinity,
                                    If[ka==kaPos,
                                      {"E", Infinity, Infinity, kaNeg},
                                        If[ka==kaNeg,
                                          {"E", Infinity, kaPos, Infinity},
                                          {"WrongCase"}
                                        ]
                                    ],
                                    {"WrongCase"}
                                  ]
                              ]
                          ]
                      ]
                  ]
              ]
            ]
          ]
        ]
		  ]
	  ],
	intervals
  ]
	
WeifengSignature[x_Symbol,G_List]:= 
	With[{intervals=InputNonNegativeIntervals[x,G]},
		WeifengSignature[x,intervals,G]
	]
	
WeifengSignatureWithRoots[x_Symbol,G_List]:= 
  With[{intervals=InputNonNegativeIntervals[x,G]},
    Map[
	      Function[interval,
		      With[{asPair=interval[[1]]},
		        With[
              {
                a=asPair[[1]],
			          b=asPair[[2]]
              },
			        With[
                {
                  kTupleA=kDataAtA[x,G,a],
                  kTupleB=kDataAtA[x,G,b]
                },
				        With[
                  {
                    ka=kTupleA[[1]],
				            kaPos=kTupleA[[2]],
				            kaNeg=kTupleA[[3]],
				            kb=kTupleB[[1]],
				            kbPos=kTupleB[[2]],
				            kbNeg=kTupleB[[3]]
                  },
				          If[a!=b, 
                    {{"Interval", {a, b}},Infinity,kaPos,kbNeg},
                      If[ka<kaPos && ka<kaNeg,
                        {{"A", a},ka,ka+1,ka+1},
                          If[ka>kaPos&&ka>kaNeg,
                            {{"B", a},Max[kaPos,kaNeg]+1,kaPos,kaNeg},
                              If[kaPos<ka&&ka<kaNeg,
                                {{"C", a},ka,kaPos,ka + 1},
                                  If[kaNeg<ka&&ka<kaPos,
                                    {{"D", a},ka,ka+1,kaNeg},
                                      If[ka==Infinity,
                                        If[ka==kaPos,
                                          {{"E", a}, Infinity, Infinity, kaNeg},
                                            If[ka==kaNeg,
                                              {{"E", a}, Infinity, kaPos, Infinity},
                                              {"WrongCase"}
                                            ]
                                        ],
                                        {"WrongCase"}
                                      ]
                                  ]
                              ]
                          ]
                      ]
                  ]
                ]
              ]
            ]
		      ]
	      ],
	    intervals
    ]
  ] 

	
WeifengSignatureExt[x_Symbol, f_, G_List] :=
	With[{intervals=InputNonNegativeIntervals[x,G]},
		WeifengSignature[x,intervals,{f}]
	]

WeifengTwoGens[x_Symbol, G_List]:=
	With[{intervals=InputNonNegativeIntervals[x,G]},
	     With[{weifengTriplets = WeifengSignature[x,intervals,G],
		   n = Length[intervals]},
		  DebuggerMessageInternal[
			  With[{},
			       Write[Global`COutputStream, "Polynomials in basis: ", G//Simplify];
			       Write[Global`COutputStream, ""];
			  ]
			  &
		  ];
		  Block[{f=-1, g=1},
			Map[Function[i,
				     With[{ai=intervals[[i,1,1]],
					   bi=intervals[[i,1,2]],
					   type=weifengTriplets[[i,1]],
					   ki=weifengTriplets[[i,2]],
					   kiPos=weifengTriplets[[i,3]],
					   kiNeg=weifengTriplets[[i,4]]},
					  DebuggerMessageInternal[
						  With[{},
						       Write[Global`COutputStream, "Iteration #", i];
						       Write[Global`COutputStream, "Current interval: ", intervals[[i]]];
						       Write[Global`COutputStream, "Current type: ", type];
						       Write[Global`COutputStream, "k_i ", ki];
						       Write[Global`COutputStream, "k_i^+ ", kiPos];
						       Write[Global`COutputStream, "k_i^- ", kiNeg];
						       Write[Global`COutputStream,
							     "Current state of f (before entering body loop): ", f];
						       Write[Global`COutputStream,
							     "Current state of g (before entering body loop): ", g];
						       Write[Global`COutputStream, ""];
						  ]
						  &
					  ];
					  If[ai<bi,
					     f=f*(x-ai)^kiPos*(x-bi)^kiNeg,
					     If[type=="A",
						f=f*(x-ai)^ki,
						If[type=="B",
						   If[i==1,
						      f=f*(x-ai)^kiNeg;
						      g=g*(x-ai)^kiPos,
						      If[i==n,
							 f=f*(-x+ai)^kiPos;
							 g=g*(-x+ai)^kiNeg,
							 With[{d=intervals[[i+1,1,1]]-ai},
							      f=f (x-ai)^kiPos(x-(ai+d/5));g=g (x-ai)^kiNeg(x-(ai+2d/5))
							 ]
						      ]
						   ],
						   If[type=="C",
						      f=f*(x-ai)^ki;
						      If[i==1,
							 g=g*(x-ai)^kiPos,
							 With[{d=ai-intervals[[i-1,1,2]]},
							      g=g*(x-(ai-d/5))*(x-ai)^kiPos
							 ]
						      ],
						      If[type=="D",
							 f=f*(x-ai)^ki;
							 If[i==n,
							    g=g*(-x+ai)^kiNeg,
							    With[{d=intervals[[i+1,1,1]]-ai},
								 g=g*(x-ai)^kiNeg*(x-(ai+d/5))
							    ]
							 ],
							 Print["Wrong Case"]
						      ]
						   ]
						]
					     ]
					  ];
					  DebuggerMessageInternal[
						  With[{},
						       Write[Global`COutputStream,
							     "Current state of f (after entering body loop): ", f];
						       Write[Global`COutputStream,
							     "Current state of g (after entering body loop): ", g];
						       Write[Global`COutputStream, ""];
						  ]
						  &
					  ];
					  1
				     ]
			    ],
			    Range[n]
			];
			
			DebuggerMessageInternal[
				With[{},
				     Write[Global`COutputStream, "Final value of f : ", f];
				     Write[Global`COutputStream, "Final value of g : ", g];
				     Write[Global`COutputStream, ""];
				]
				&
			];
			{f, g}
		  ]
	     ]
	]

End[];

EndPackage[];
