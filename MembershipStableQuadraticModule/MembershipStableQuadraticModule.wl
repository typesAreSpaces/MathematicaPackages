(* ::Package:: *)

BeginPackage["MembershipStableQuadraticModule`"];

MembershipStableQM::usage="MembershipStableQM[param_,
\tf_, G_List,
\tboundFunction_,
\ttol_, maxite_, method_]
* param is a free symbol variable
* f is a polynomial
* G is a list of polynomials
* boundFunction is a bound function to limit the 
\tsearch degree of sums of squares multipliers
* tol is a float number indicating the solver tolerance
* maxite is an integer indicating the maximum number of iterations
* method is a string which could be \"CSDP\",\"DSDP\", or \"SCS\"";
RoundingProjectionUnivariateCase::usage="RoundingProjectionUnivariateCase[param_,
\tf_, G_List,
\tboundFunction_,
\tsolverTol_, maxite_, method_, 
\tratTol_]
* param is a free symbol variable
* f is a polynomial
* G is a list of polynomials
* boundFunction is a bound function to limit the 
\tsearch degree of sums of squares multipliers
* solveTol is a float number indicating the solver tolerance
* maxite is an integer indicating the maximum number of iterations
* method is a string which could be \"CSDP\",\"DSDP\", or \"SCS\"
* ratTol is the tolerance for rationalization. Use a fraction.";
RoundingProjectionUnivariateCaseLS::usage="RoundingProjectionUnivariateCaseLS[param_,
  f_, G_List,
  boundFunction_,
  solverTol_, maxite_, method_, 
  ratTol_] 
* param is a free symbol variable
* f is a polynomial
* G is a list of polynomials
* boundFunction is a bound function to limit the 
\tsearch degree of sums of squares multipliers
* solveTol is a float number indicating the solver tolerance
* maxite is an integer indicating the maximum number of iterations
* method is a string which could be \"CSDP\",\"DSDP\", or \"SCS\"
* ratTol is the tolerance for rationalization. Use a fraction.";
UnivOutputPoly::usage="UnivOutputPoly[x_, gens_, sizes_, blockMatrix_]"

Begin["`Private`"];

Needs["BlockMatrix`"];
Needs["PolyDegree`"];
Needs["EnumsAtMostDegree`"];

ListRulesToAssoc[l_List] := l//.x:{__Rule}:>Association[x];

GetCoefficientOf[exp_, polyAsRules_] := Lookup[polyAsRules, {exp}, 0]//First;

DegreeOfMultiplier[boundDegF_] :=
Function[g,
  With[{diff = boundDegF-PolyDegree[g]},
    If[diff > 0, Floor[diff/2], 0]
  ]
]

MonsAssocByDegree[boundDegF_, vars_, filteredG_] := 
ListRulesToAssoc @ Map[
  (#->MonomialsAtMostDegree[vars, #])&,
  Union[Map[DegreeOfMultiplier[boundDegF], filteredG]]
]

EncodingSOSMatrices[boundDegF_, vars_, filteredG_, expList_] := 
Map[
  Function[exp,
    Map[
      Function[g,
        With[{mons = MonsAssocByDegree[boundDegF, vars, filteredG][DegreeOfMultiplier[boundDegF][g]]},
          With[{matrix =
            Table[
              CoefficientRules[mons[[i]]*mons[[j]]*g, vars],
                {i, Length[mons]},
                {j, Length[mons]}
              ]
            },
            Map[GetCoefficientOf[exp, #]&, matrix, {2}]
          ]
        ]
      ], 
      filteredG
    ]
  ], 
  expList
]

SOSMultipliers[boundDegF_, vars_, gramMatrix_, filteredG_] :=
Flatten[
  Block[{currPos = 1},
    Map[
      Function[g,
        With[{mons = MonsAssocByDegree[boundDegF, vars, filteredG][DegreeOfMultiplier[boundDegF][g]]},
          currPos = currPos + Length[mons];
          {mons} . gramMatrix[[currPos-Length[mons];;currPos-1,currPos-Length[mons];;currPos-1]] . Transpose[{mons}]
        ]
      ], 
      filteredG
    ]
  ]
]

UnivOutputPoly[x_, gens_, sizes_, blockMatrix_] :=
With[
  {
    mons = Table[{Table[x^j, {j, 0, sizes[[i]] - 1}]}, {i, Length[sizes]}],
    matrices = ExtractFromBlockMatrix[blockMatrix, sizes]
  },
  Expand[
    Sum[mons[[i]] . matrices[[i]] . Transpose[mons[[i]]]*gens[[i]], 
      {i, Length[sizes]}
    ][[1, 1]]
  ]
]


DebugMembershiptStableQM = True;

MembershipStableQM[param_,
  f_, G_List,
  boundFunction_,
  tol_, maxite_, method_] :=
With[{boundDegF = boundFunction[PolyDegree[f]]},
  With[{
    (* filteredG removes generators with degree greater than boundFunction[PolyDegree[f]] and appends g_0 := 1 *)
    filteredG = Prepend[Select[G, PolyDegree[#] <= boundDegF&], 1]
  },
  
    If[DebugMembershiptStableQM, Print["generators: ", filteredG]];
    With[{vars = Variables[Append[filteredG, f]]},
      With[{
	      fCoeffRules = CoefficientRules[f, vars],
	      (*ExponentsAtMostDegree starts with monomials of lower degree first*)
	      expList = ExponentsAtMostDegree[Length[vars], boundDegF]
	    },
	      With[{
          (* cmatrices = { Mat_i[m, m] | i \in {1, ..., |expList| } where m = \sum{i=1}^s d_i *)
	        cmatrices = EncodingSOSMatrices[boundDegF, vars, filteredG, expList],
	        fCoeffs = Map[Function[exp, GetCoefficientOf[exp, fCoeffRules]], expList]
	      },
	        With[{
	          cmatricesLengths = Map[Length, cmatrices[[1]]],
	          cmatricesTotalLength = Map[Length, cmatrices[[1]]] // Fold[#1 + #2 &, 0, #]&
	        },
	          With[{
              parametricMatrix = Table[
	              If[i < j, Subscript[param, i, j, k], Subscript[param, j, i, k]],
	              {k, Length[cmatricesLengths]},
	              {i, cmatricesLengths[[k]]},
	              {j, cmatricesLengths[[k]]}
	            ]//BlockMatrix,
              params = Flatten[
	              Table[
	                Subscript[param, i, j, k],
	                {k, Length[cmatricesLengths]},
	                {i, cmatricesLengths[[k]]},
	                {j, i, cmatricesLengths[[k]]}
	              ]
	            ]
            },
              With[
              {
	              constraints = {
	                Table[
	                  Tr[BlockMatrix[cmatrices[[i]]] . parametricMatrix] == fCoeffs[[i]], 
                      {i, Length[cmatrices]}
	                ],
	                VectorGreaterEqual[
                    {parametricMatrix, 0}, 
                    {"SemidefiniteCone", cmatricesTotalLength}
                  ]
	              }
	            },
                If[AnyTrue[constraints[[1]], # === False &],
                  {"No Gram matrix found",0,0,0,0},
                  If[DebugMembershiptStableQM, 
                    Print["Constraints: ", constraints];
                    Print["cmatrices: ", cmatrices];
                    Print["parametricMatrix: ", parametricMatrix];
                    Print["params: ", params];
                    Print["method: ", method];
                    Print["tol: ", tol];
                    Print["First part: ", Table[
	                  Tr[BlockMatrix[cmatrices[[i]]] . parametricMatrix], 
                        {i, Length[cmatrices]}
	                  ]];
                    Print["Second part: ", Table[
	                     fCoeffs[[i]],
                        {i, Length[cmatrices]}
	                  ]];
                  ];
	                With[{sol = SemidefiniteOptimization[
                              (*Barrier function*)
                              -Tr[parametricMatrix],
	                            constraints,
	                            Map[Element[#, Reals]&, params],
	                            Method->method,
	                            MaxIterations->maxite,
	                            PerformanceGoal->"Quality",
	                            Tolerance->tol
	                ] // Quiet},
	                  If[sol[[1,2]] === Indeterminate,
                      {"No Gram matrix found",0,0,0,0},
	                    With[{gramMatrix = parametricMatrix/.sol},
	                      With[{sosMultipliers = SOSMultipliers[boundDegF, vars, gramMatrix, filteredG]},
	                        {
	                          gramMatrix,
	                          sosMultipliers,
	                          (* Representation of f in QuadMod(G) found using SDP solver*)
	                          Dot[sosMultipliers, filteredG],
	                          cmatricesLengths,
	                          filteredG
	                        }
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
	  ]
  ]
]


DebugRoundingProjectionUnivariateCase = False;

RoundingProjectionUnivariateCase[param_,
  f_, G_List,
  boundFunction_,
  solverTol_, maxite_, method_, 
  ratTol_] :=
With[{result = MembershipStableQM[param, f, G, boundFunction, solverTol, maxite, method] // Quiet}, 
  If[result[[1]] === "No Gram matrix found",
    {"No Gram matrix found",0,0,0},
    With[
    {
      numericMatrix = result[[1]], 
      sizes = result[[4]], 
      generators = result[[5]],
      x = (Variables[f])[[1]]
    },
      If[DebugRoundingProjectionUnivariateCase,
        Print["generators: ", generators];
        Print["numericMatrix: ", numericMatrix];
      ]; 
      With[
      {
        rationalMatrix = Map[Rationalize[#, ratTol] &, numericMatrix, {2}],
        mons = Table[{Table[x^j, {j, 0, sizes[[i]] - 1}]}, {i, Length[sizes]}],
        paramMatrices = Table[
          If[i < j, Subscript[param, i, j, k], Subscript[param, j, i, k]], 
          {k, Length[sizes]}, 
          {i, sizes[[k]]}, 
          {j, sizes[[k]]}
        ]
      },
        
        If[DebugRoundingProjectionUnivariateCase, 
          Print["Rational matrix: ", rationalMatrix];
        ];
        With[
        {
          blockMatrices = ExtractFromBlockMatrix[rationalMatrix, sizes],
          obj = rationalMatrix - BlockMatrix[paramMatrices]
            // Flatten // Map[#^2 &] // Fold[#1 + #2 &, 0, #] &,
          vars = paramMatrices // Map[Flatten] // Flatten
        },
          With[
          {
            (*vars = Variables[obj],*)
            paramH = (Sum[
              mons[[i]] . paramMatrices[[i]] . Transpose[mons[[i]]]*generators[[i]], 
              {i, Length[sizes]}
            ])[[1, 1]] // Expand
          },
            With[{xDegreeParamH = PolyDegreeVar[paramH, x]},
              With[
              {
                constraints = Table[
                  Coefficient[paramH, x, deg] == Coefficient[f, x, deg],
                  {deg, 0, Max[PolyDegree[f], xDegreeParamH]}
                ] // Fold[#1 && #2 &, True, #] &
              },
                If[DebugRoundingProjectionUnivariateCase, 
                  Print["obj: ", obj];
                  Print["constraints: ", constraints];
                  Print["vars: ", vars];
                ];
                With[
                {
                  (*Approach using Mathematica Minimize function.*) 
                  sol = Minimize[{obj, constraints}, vars, Reals] // Quiet
                },
                  If[sol[[2, 1, 2]] === Indeterminate,
  
                    "No solution",
  
                    If[DebugRoundingProjectionUnivariateCase, 
                      Print["Solution found: ", sol];
                    ];
                      
                    With[
                    {
                      fixedMatrices = paramMatrices /. (sol[[2]])
                    },
                      (*If[DebugRoundingProjectionUnivariateCase, *)
                      If[True,
                        Print["Projection matrices: ", fixedMatrices];
                        Print["Is the new matrix a SDP matrix? ", 
                          fixedMatrices // Map[Eigenvalues] // Flatten // Map[# >= 0 &] // Fold[#1 && #2 &, True, #] &
                        ];
                      ]; 
                      With[
                      {
                        fixedMultipliers = Table[
                          mons[[i]] . fixedMatrices[[i]] . Transpose[mons[[i]]] // #[[1, 1]] &,
                          {i, Length[sizes]}
                        ]
                      },
                        {
                          (*Projection Matrix*)
                          fixedMatrices,
                          (*Fixed multipliers for generators*)
                          fixedMultipliers,
                          (*The following should be the original polynomial f*)
                          Sum[fixedMultipliers[[i]]*generators[[i]], 
                            {i, Length[sizes]}
                          ] // Expand,
                          generators
                        }
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
  ]
]


DebugRoundingProjectionUnivariateCaseLS = False;

RoundingProjectionUnivariateCaseLS[param_,
  f_, G_List,
  boundFunction_,
  solverTol_, maxite_, method_, 
  ratTol_] :=
With[{result = MembershipStableQM[param, f, G, boundFunction, solverTol, maxite, method] // Quiet},
  If[result[[1]] === "No Gram matrix found",
    {"No Gram matrix found",0,0,0},
    With[
    {
      numericMatrix = result[[1]], 
      sizes = result[[4]], 
      generators = result[[5]],
      x = (Variables[f])[[1]]
    },
     If[DebugRoundingProjectionUnivariateCaseLS, 
        Print["numericMatrix:"];
        Print[MatrixForm[numericMatrix]];
      ];
      With[
      {
        rationalMatrix = Map[Rationalize[#, ratTol] &, numericMatrix, {2}],
        mons = Table[{Table[x^j, {j, 0, sizes[[i]] - 1}]}, {i, Length[sizes]}],
        paramMatrices = Table[
          If[i < j, Subscript[param, i, j, k], Subscript[param, j, i, k]], 
          {k, Length[sizes]}, 
          {i, sizes[[k]]}, 
          {j, sizes[[k]]}
        ]
      },
        If[DebugRoundingProjectionUnivariateCaseLS, 
          Print["Parametric matrix:"];
          Print[MatrixForm[BlockMatrix[paramMatrices]]];
          Print["Rational matrix:"];
          Print[MatrixForm[rationalMatrix]];
        ];
        With[
        {
          blockMatrices = ExtractFromBlockMatrix[rationalMatrix, sizes],
          vars = paramMatrices // Map[Flatten] // Flatten
        },
          With[
          {
            paramPoly = UnivOutputPoly[x, generators, sizes, BlockMatrix[paramMatrices]]
          },
            If[DebugRoundingProjectionUnivariateCaseLS, 
              Print["generators: ", generators];
              Print["paramPoly: ", paramPoly];
            ];
            With[{xDegreeParamPoly = PolyDegreeVar[paramPoly, x]},
              With[
              {
                constraints = Table[
                  Coefficient[paramPoly, x, deg] == Coefficient[f, x, deg],
                  {deg, 0, Max[PolyDegree[f], xDegreeParamPoly]}
                ] // Fold[#1 && #2 &, True, #] &
              },
                If[DebugRoundingProjectionUnivariateCaseLS, 
                  Print["generators: ", generators];
                  Print["constraints: ", constraints];
                  Print["paramPoly: ", paramPoly];
                  Print["Target polynomial: ", f];
                ];
                With[
                {
                  linearSolutions = Solve[constraints, vars] // Quiet
                },
                  If[DebugRoundingProjectionUnivariateCaseLS, 
                    Print["Found this solution: ", linearSolutions[[1]]];
                  ];
                  If[Length[linearSolutions] == 0,
  
                    "No solution",
  
                    With[
                    {
                      (*We 'put together' the substitution of linearSolutions[1] in vars together
                      with the elements of blockMatrices so pendingContraints effectively filters
                      element-wise the contraints*)
                      elementWiseContraints = MapThread[
                        {#1, #2} &, 
                        {vars /. (linearSolutions[[1]]), blockMatrices // Map[Flatten] // Flatten}
                      ]
                    },
                      If[DebugRoundingProjectionUnivariateCaseLS,
                        Print["Hmm0: ", vars];
                        Print["Hmm1: ", vars /. (linearSolutions[[1]])];
                        Print["Hmm2: ", blockMatrices // Map[Flatten] // Flatten];
                        Print["Hmm3: ", blockMatrices // Map[MatrixForm]];
                        Print["elementWiseContraints: ", elementWiseContraints];
                      ];
                      With[{pendingContraints = Select[elementWiseContraints, Not @ NumberQ @ #[[1]] &]},
                        With[{independentParams = pendingContraints// Map[#[[1]] &] // Variables},
                          If[DebugRoundingProjectionUnivariateCaseLS,
                            Print["pendingContraints: ", pendingContraints];
                            Print["independentParams: ", independentParams];
                          ];
                          With[
                          {
                            coeffsArray = pendingContraints 
                              // Map[#[[1]] &] // CoefficientArrays[#, independentParams] & // Normal 
                          },
                            With[
                            {
                              leastSquaresMatrix = coeffsArray[[2]],
                              leastSquaresVector = (pendingContraints // Map[#[[2]] &]) - coeffsArray[[1]]
                            },
                              If[DebugRoundingProjectionUnivariateCaseLS,
                                Print["leastSquaresMatrix: ", MatrixForm[leastSquaresMatrix]];
                                Print["coeffsArray - Vector: ", MatrixForm[coeffsArray[[1]]]];
                                Print["leastSquaresVector: ", MatrixForm[leastSquaresVector]];
                              ];
                              With[
                              {
                                moreSolutions = MapThread[
                                  #1 -> #2 &, 
                                  {independentParams, LeastSquares[leastSquaresMatrix, leastSquaresVector]}
                                ]
                              },
                                With[{allSolutions = Join[linearSolutions[[1]] /. moreSolutions, moreSolutions]},
                                  With[
                                  {
                                    fixedMatrices = paramMatrices /. allSolutions
                                  },
                                    (*If[DebugRoundingProjectionUnivariateCaseLS, *)
                                    If[True, 
                                      Print["Projection matrices:"];
                                      Print[MatrixForm[BlockMatrix[fixedMatrices]]];
                                      Print["Is the new matrix a SDP matrix? ",
                                        fixedMatrices // Map[Eigenvalues] // Flatten // Map[# >= 0 &] // Fold[#1 && #2 &, True, #] &
                                      ];
                                    ];
                                    With[
                                    {
                                      fixedMultipliers = Table[
                                        mons[[i]] . fixedMatrices[[i]] . Transpose[mons[[i]]] // #[[1, 1]] &,
                                        {i, Length[sizes]}
                                      ]
                                    },
                                      {
                                        (*Projection Matrix*)
                                        fixedMatrices,
                                        (*Fixed multipliers for generators*)
                                        fixedMultipliers,
                                        (*The following should be the original polynomial f*)
                                        Sum[fixedMultipliers[[i]]*generators[[i]], 
                                          {i, Length[sizes]}
                                        ] // Expand,
                                        generators
                                      }
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
                ]
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
