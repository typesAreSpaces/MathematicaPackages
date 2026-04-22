(* ::Package:: *)

BeginPackage["MonogenicQuadMod`"];
compactRepr::usage="compactRepr[x, param, n] computes a generalized 
parameterized sums of squares polynomial with parameter
param in R[x] with degree n.
* x is a variable
* param is a free variable
* n is an integer";
leadCoeff1::usage="leadCoeff1[x, param, n] computes a generalized 
parameterized sums of squares polynomial with parameter
param in R[x] with degree n. The leading coefficient of the resulting
polynomial is 1.
* x is a variable
* param is a free variable
* n is an integer";
fullRepr::usage="fullRepr[x_, param_, n_Integer] computes a generalized 
parameterized sums of squares polynomial with parameter
param in R[x] with degree n. It adds a parametric coefficient for each
sum of squares.
* x is a variable
* param is a free variable
* n is an integer";
findCertificatesAux::usage="findCertificatesAux[x_, f_, g_, n1_Integer, n2_Integer, s0_, s1_, auxCoeff_, repr1_ : compactRepr, repr2_ : compactRepr]
(attempts to) compute(s) solutions to the fullRepr problem with respect to f";
findCertificates::usage="findCertificates[x_, f_, g_, n1_Integer, n2_Integer, s0_, s1_, repr1_ : compactRepr, repr2_ : compactRepr]";
findCertificates2::usage="findCertificates2[x_, f_, g_, n1_Integer, n2_Integer, s0_, s1_]";

Begin["`Private`"];

setupEquations[x_List, y_List] :=
With[{min = Min[Length[x], Length[y]], 
  max = Max[Length[x], Length[y]], 
  bigger = If[Length[x] > Length[y], x, y]}, 
 Join[Table[x[[i]] == y[[i]], {i, min}], 
  Table[bigger[[i]] == 0, {i, min + 1, max}]]]

compactRepr2[x_, param_, n_Integer] :=
With[{poly = Subscript[param, 0] Product[(x - Subscript[param, i, 1])^2 + Subscript[param, i, 2], {i, n}]}, 
  {
    Subscript[param, 0],
    Table[Subscript[param, i, 1], {i, n}],
    Table[Subscript[param, i, 2], {i, n}],
    poly
  }
]

compactRepr[x_, param_, n_Integer] :=
With[{poly = Subscript[param, 0]^2 Product[(x - Subscript[param, i, 1])^2 + Subscript[param, i, 2]^2, {i, n}]}, 
  {
    Prepend[
      Join[
        Table[Subscript[param, i, 1], {i, n}], 
        Table[Subscript[param, i, 2], {i, n}]
      ], 
      Subscript[param, 0]
    ], 
    poly
  }
]

leadCoeff1[x_, param_, n_Integer] :=
With[{poly = Product[(x - Subscript[param, i, 1])^2 + Subscript[param, i, 2]^2, {i, n}]}, 
  {
    Join[
      Table[Subscript[param, i, 1], {i, n}], 
      Table[Subscript[param, i, 2], {i, n}]
    ], 
    poly
  }
]

fullRepr[x_, param_, n_Integer] :=
With[{poly = Product[(Subscript[param, i, 0]^2)((x - Subscript[param, i, 1])^2 + Subscript[param, i, 2]^2), {i, n}]}, 
  {
    Join[
      Table[Subscript[param, i, 0], {i, n}],
      Table[Subscript[param, i, 1], {i, n}], 
      Table[Subscript[param, i, 2], {i, n}]
    ], 
    poly
  }
]

findCertificatesAux[x_, f_, g_, n1_Integer, n2_Integer, s0_, s1_, auxCoeff_, repr1_ : compactRepr, repr2_ : compactRepr] :=
With[{
  sos0F = repr1[x, s0, n1], 
  sos1F = repr2[x, s1, n2]
},
 With[{
   params0 = sos0F[[1]], 
   params1 = sos1F[[1]], 
   sos0 = sos0F[[2]], 
   sos1 = sos1F[[2]]
},
  With[{repr = sos0 + sos1*g},
   With[{
     systemEqs = 
      setupEquations[CoefficientList[auxCoeff^2 * f, x], CoefficientList[repr, x]],
     params = Prepend[Join[params0, params1], auxCoeff] 
  },
    (*Print[repr];*)
    (*Print[systemEqs];*)
    (*Print[params];*)
    With[{sol = FindInstance[Prepend[systemEqs, auxCoeff != 0], params, Reals]},
     If[Length[sol] > 0,
      Print[repr];
      Print[repr /. sol[[1]]];
      sol,
      "No solution found"
      ]
     ]
    ]
   ]
  ]
 ]

findCertificates[x_, f_, g_, n1_Integer, n2_Integer, s0_, s1_, repr1_ : compactRepr, repr2_ : compactRepr] :=
With[{
  sos0F = repr1[x, s0, n1], 
  sos1F = repr2[x, s1, n2]
},
 With[{
   params0 = sos0F[[1]], 
   params1 = sos1F[[1]], 
   sos0 = sos0F[[2]], 
   sos1 = sos1F[[2]]
},
  With[{repr = sos0 + sos1*g},
   With[{
     systemEqs = 
      setupEquations[CoefficientList[f, x], CoefficientList[repr, x]],
     params = Join[params0, params1]
  },
    Print[repr];
    Print[systemEqs];
    Print[params];
    With[{sol = FindInstance[systemEqs, params, Reals]},
     If[Length[sol] > 0,
      Print[repr];
      Print[repr /. sol[[1]]];
      sol,
      "No solution found"
      ]
     ]
    ]
   ]
  ]
 ]

findCertificates2[x_, f_, g_, n1_Integer, n2_Integer, s0_, s1_] :=
With[{
  sos0F = compactRepr2[x, s0, n1], 
  sos1F = compactRepr2[x, s1, n2]
},
 With[{
   param0Pos = sos0F[[1]], 
   param1Pos = sos1F[[1]], 
   params0 = sos0F[[2]], 
   params1 = sos1F[[2]], 
   params0NonNeg = sos0F[[3]], 
   params1NonNeg = sos1F[[3]], 
   sos0 = sos0F[[4]], 
   sos1 = sos1F[[4]]
},
  With[{repr = sos0 + sos1*g},
   With[{
     systemEqs = 
      setupEquations[CoefficientList[f, x], CoefficientList[repr, x]],
     posConstraints = {param0Pos > 0, param1Pos > 0},
     nonNegConstraints = Join[Thread[params0NonNeg >= 0], Thread[params1NonNeg >= 0]],
     params = Prepend[Prepend[Join[params0, params1, params0NonNeg, params1NonNeg], param0Pos], param1Pos]
  },
    Print[repr];
    Print[systemEqs];
    Print[params];
    Print[posConstraints];
    Print[nonNegConstraints];
    With[{sol = FindInstance[Join[systemEqs, posConstraints, nonNegConstraints], params, Reals]},
     If[Length[sol] > 0,
      Print[repr];
      Print[repr /. sol[[1]]];
      sol,
      "No solution found"
      ]
     ]
    ]
   ]
  ]
 ]


End[];

EndPackage[];
