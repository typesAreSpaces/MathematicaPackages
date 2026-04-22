(* ::Package:: *)

BeginPackage["PlotGrid`"];


PlotGrid::usage="PlotGrid[x_, fs_, intervals_, headerMsg_] plots many things
* x is a variable
* fs is a list of polynomials
* intervals is a list of intervals {a, b}
* headerMsg is a custom string denoting a header message";


Begin["`Private`"];


PlotGrid[x_, fs_, intervals_, headerMsg_]:=
GraphicsGrid[
  Map[
    Block[{leftEndPoint = #[[1]], rightEndPoint = #[[2]]},
      Block[{plots = 
        Map[Block[{f = #[[1]], msg = #[[2]], color = #[[3]]},
          Plot[f, {x, leftEndPoint, rightEndPoint}, PlotLabel-> msg, PlotStyle -> {color}]]&, 
          fs
        ]},
        Prepend[plots, headerMsg[leftEndPoint, rightEndPoint]]
      ]
    ]&, 
  intervals], 
Frame->All, ImageSize->Large];

End[];


EndPackage[];
