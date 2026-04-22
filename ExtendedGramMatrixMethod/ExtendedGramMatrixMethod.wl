(* ::Package:: *)

BeginPackage["ExtendedGramMatrixMethod`"];

findGramMatrices::usage="";
getGramCertificate::usage="";
getGramCertificateEig::usage="";
getGramCertificateMons::usage="";
getGramCertificateEigMons::usage="";

Begin["`Private`"];

(*
findGramMatrices[f,gens,x,dim,param] returns a list of Gram matrices A_i such that
f ~ \sum_i {{m^T A_i m} \cdot g_i} where gens = {g_1, ..., g_s}, g_0 := 1
*)

findGramMatrices[f_, gens_, x_, dim_, param_] :=
    Module[
        {ngens = Length[gens], monomialBasis, sdpMatrices, polys, coeffs,
             vars, sol, solMatrices, cert}
        ,
        (*1. Build monomial basis efficiently*)
        monomialBasis = x ^ Range[0, dim - 1];
        (*2. Construct symmetric parameter matrices*) sdpMatrices =
            Array[
                If[#2 >= #3,
                    param[#1, #2, #3]
                    ,
                    param[#1, #3, #2]
                ]&
                ,
                {ngens + 1, dim, dim}
            ];
        (*3. Build polynomial combinations directly*)
        polys = Map[monomialBasis . # . Transpose[monomialBasis]&, sdpMatrices
            ] . Prepend[gens, 1];
        (*4. Coefficients of template - input polynomial*)
        coeffs = Normal @ CoefficientList[polys - f, x];
        (*5. Collect all SDP variables*)
        vars = Variables[sdpMatrices];
        (*6. Run SDP*)
        sol = SemidefiniteOptimization[0, Thread[coeffs == 0] && Table[
            VectorGreaterEqual[{sdpMatrices[[i]], 0}, {"SemidefiniteCone", dim}],
             {i, Length[sdpMatrices]}], vars, Method -> "DSDP", MaxIterations -> 
            10000, PerformanceGoal -> "Quality", Tolerance -> 10 ^ -8];
        sdpMatrices /. sol
    ]


(*
getGramCertifcate[gramMatrices,x,dim] returns a list `cert' of the polynomials in the sums of squares decomposition
i.e., Map[Total[Map[#^2&,#]]&,cert].Prepend[gens,1] is input polynomial f
*)

getGramCertificate[gramMatrices_, x_, dim_] :=
    Map[CholeskyDecomposition[#] . x ^ Range[0, dim - 1]&, gramMatrices
        ]

getGramCertificateEig[gramMatrices_, x_, dim_] :=
    Map[
        Function[mat,
            Module[{vals, vecs},
                {vals, vecs} = Eigensystem[mat];
                vecs = Map[Normalize, vecs];
                DiagonalMatrix[Map[Sqrt[#]&, vals]] . (vecs . x ^ Range[
                    0, dim - 1])
            ]
        ]
        ,
        gramMatrices
    ]

getGramCertificateMons[gramMatrices_, mons_] := 
 Map[CholeskyDecomposition[#] . mons &, gramMatrices]
getGramCertificateEigMons[gramMatrices_, mons_] := Map[Function[mat,
   Module[{vals, vecs},
    {vals, vecs} = Eigensystem[mat];
    vecs = Map[Normalize, vecs];
    DiagonalMatrix[Map[Sqrt[#] &, vals]] . (vecs . mons)
    ]
   ],
  gramMatrices
  ]


End[];
EndPackage[];
