(* ::Package:: *)

BeginPackage["EnumsAtMostDegree`"];


ExponentsAtMostDegree::usage="ExponentsAtMostDegree[varsLength_Integer,degree_Integer]"
MonomialsAtMostDegree::usage="MonomialsAtMostDegree[vars_List,degree_Integer]"
ExponentsWithDegree::usage="ExponentsWithDegree[varsLength_Integer,degree_Integer]"
MonomialsWithDegree::usage="MonomialsWithDegree[vars_List,degree_Integer]"


Begin["`Private`"];


atMostDegreePartitions[varsLength_Integer,degree_Integer]:=Flatten[Map[IntegerPartitions[#,varsLength]&,Range[0,degree]],1]
withDegreePartitions[varsLength_Integer,degree_Integer]:=IntegerPartitions[degree,varsLength]
paddingPartitions[varsLength_Integer,partitions_List]:=PadRight[#,{Length@#,varsLength}]& [partitions]

ExponentsAtMostDegree[varsLength_Integer,degree_Integer]:=
Flatten[
	Map[Permutations,
		paddingPartitions[varsLength,atMostDegreePartitions[varsLength,degree]]
	],
	1
]

ExponentsWithDegree[varsLength_Integer,degree_Integer]:=
Flatten[
	Map[Permutations,
		paddingPartitions[varsLength,withDegreePartitions[varsLength,degree]]
	],
	1
]


MonomialsAtMostDegree[vars_List,degree_Integer]:=Times@@@(vars^#&/@ExponentsAtMostDegree[Length[vars],degree]);
MonomialsWithDegree[vars_List,degree_Integer]:=Times@@@(vars^#&/@ExponentsWithDegree[Length[vars],degree]);


End[];


EndPackage[];
