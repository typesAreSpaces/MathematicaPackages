(* ::Package:: *)

BeginPackage["Compactification`"];

compactificationBounded::usage = ""
compactificationRight::usage = ""
compactificationBoth::usage = ""
compactification::usage = ""

Begin["`Private`"];

Needs["CauchyBounds`"];

(*0 means input is bounded*)
(*1 means input is both unbounded*)
(*2 means input is left unbounded*)
(*3 means input is right unbounded*)

auxDegree[p_,x_,acc_]:=If[p===0,acc,auxDegree[D[p,x],x,acc+1]];
degree[p_,x_]:=If[p===0,0,auxDegree[p,x,0]-1]

IsBounded[f_, x_] := Module[{coeffs, l},
    coeffs = CoefficientList[Expand[f], x];
    l = Length[coeffs];
    If[Last[coeffs] > 0,
        If[Mod[l, 2] == 0, 3, 1],
        (*otherwise Last[coeffs] < 0*)
        If[Mod[l, 2] == 0, 2, 0]
    ]
]

compactificationBounded[f_, x_] := Module[{eps}, 
  eps := Maximize[f, x][[1]] + 1; 
  {1 / eps, 1, 1 / eps * (eps - f)}
]

compactificationRight[f_, bound_, x_] := Module[{n, M, eps, alpha, sigma, tau, h},
    n = degree[f,x];
    M=If[CountRoots[f,x]==n&&Discriminant[f,x]!=0,CauchyBounds[f, x],CauchyBounds[Evaluate[D[f,x]], x]];
    eps = Maximize[{f, -M <= x <= Max[M, bound]}, x][[1]];
    (*There exists a unique value for alpha*)
    alpha = x /. Solve[eps - f == 0, Reals][[1]];
    sigma = 1 / eps;
    h = -(x - alpha);
    tau = sigma PolynomialQuotient[eps - f, h, x];
    {sigma, tau, h}
]

compactificationBoth[f_, lowerbound_, upperbound_, x_] := Module[{n, M, eps, sol, alpha, beta, sigma, tau, h},
    If[NumericQ[f] && f > 0,
        {1 / f, 0, 0},
        n = degree[f,x];
        M = If[CountRoots[f,x]==n&&Discriminant[f,x]!=0,CauchyBounds[f, x], CauchyBounds[Evaluate[D[f,x]], x]];
        (*M=33/16;*)
        eps = Maximize[{f, Min[-M, lowerbound] <= x <= Max[M, upperbound]}, x][[1]];
        (*Print["eps:", eps];
          Print["eps-f:" ,eps-f];   
          Print["M:", M];*)
        (*There exists only two values for alpha*)
        sol = Solve[eps - f == 0, Reals];
        alpha = x /. sol[[1]];
        beta = x /. sol[[2]];
        sigma = 1 / eps;
        h = -(x - alpha) (x - beta);
        tau = sigma PolynomialQuotient[eps - f, h, x];
        {sigma, tau, h}
    ]
]

compactification[f_, G_List, x_] := Module[{case, semialgG, lowerbound, upperbound, fOp, boundDone}, 
  case = IsBounded[f, x]; 
  semialgG = Reduce[G >= 0, x]; 

  boundDone = False;
  If[Head[semialgG] === Inequality, 
    lowerbound = semialgG[[1]];
    upperbound = semialgG[[5]]; 
    boundDone = True;
  ];
  If[Head[semialgG] == Equal,
    lowerbound = semialgG[[2]]; 
    upperbound = semialgG[[2]];
    boundDone = True;
  ];
  If[boundDone === False,
    lowerbound = First[List @@ semialgG];
    If[Head[lowerbound] === Inequality, lowerbound = lowerbound[[1]]];
    If[Head[lowerbound] === Equal, lowerbound = lowerbound[[2]]];
    upperbound = Last[List @@ semialgG];
    If[Head[upperbound] === Inequality, upperbound = upperbound[[5]]];
    If[Head[upperbound] === Equal, upperbound = upperbound[[2]]];
  ]; 

  lowerbound = lowerbound - 1;
  upperbound = upperbound + 1;

  fOp = Evaluate[f /. x -> -x]; 
  Switch[case, 
    0, compactificationBounded[f, x],
    1, compactificationBoth[f, lowerbound, upperbound, x], 
    2, Evaluate[compactificationRight[fOp, upperbound, x] /. x -> -x], 
    3, compactificationRight[f, upperbound, x]
  ]
]

End[];


EndPackage[];
