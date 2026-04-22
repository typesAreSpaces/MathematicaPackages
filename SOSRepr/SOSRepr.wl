(* ::Package:: *)

BeginPackage["SOSRepr`"];
SOSRepr::usage="SOSRepr[f_, x_] computes a sums of squares
representation of f using Brahmagupta's identity
* f is a polynomial
* x is a variable";

Begin["`Private`"];

SOSRepr[f_, x_] :=
 With[{roots = Solve[f == 0, x]},
  With[{signRight = f /. Last[roots]},
   With[{leadCoeff = Last[CoefficientList[f, x]]},
    With[{squaredTerms = Map[
        With[{subs = Apply[Plus, #]},
          With[{re = Re[subs[[2]]], im = Im[subs[[2]]]},
           (x - re)^2 + im^2
           ]
          ] &,
        roots
        ]},
     leadCoeff*PowerExpand[Sqrt[Fold[Times, 1, squaredTerms]]]
     ]
    ]
   ]
  ]

End[];

EndPackage[];
