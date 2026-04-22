(* ::Package:: *)

BeginPackage["DebuggerMessage`"];
DebuggerMessage::usage="If `enableDebugging` is defined then 
DebuggerMessage executes `code` 
given as an argument of the form (x -> `actual code`) returning 1 as output; 
otherwise the function returns 0."
DebuggerMessageLevel::usage="Defines a number which is greater than the DebuggingLevel of their package dependencies."
NewOutput::usage="Input, fileName : String. 
Output, returns a file object with addres in OutputDir/fileName. 
Requirements, the file path needs to be valid. It also needs to be closed using Close[...]"
CloseOutput::usage="Input, fileObject : a pointer returned by NewFileOutput[...]
Output, closes the file object passed as argument. It also provides post-processing
to the file created like removing extra quotes."
NewOutput::usage="Input, No arguments. 
Output, Sets Global`COutputStream to $Output."
CloseOutput::usage="Input, No arguments.
Output, clears Global`COutputStream. Returns 0"
DebugCode::usage = "TODO"


Begin["`Private`"];

DebuggerMessageLevel = 0;

OutputDir = "/home/jose/Documents/GithubProjects/phd-thesis/Software/Output";

DebuggerMessage[code_, debuggingLevel_Integer]:=
If[ValueQ[Global`enableDebugging] && Global`enableDebugging <= debuggingLevel,
	code[]; 1,
	0
]

DebuggerMessage[code_] := DebuggerMessage[code, 0]

NewOutput[]:=With[{}, Global`COutputStream = $Output; 0];

NewOutput[fileName_]:= If[fileName == "", 
	NewOutput[]; Global`IsFile = False; fileName,
	With[{actualFileName = FileNameJoin[{OutputDir, fileName}]}, 
		Global`COutputStream = OpenWrite[actualFileName];
		Global`IsFile = True;
		actualFileName
	]
]

CloseOutput[fileName_] := With[{}, 
	If[Global`IsFile,
		Close[Global`COutputStream];
		Run[StringJoin["mv ",fileName," ", fileName, "temp"]];
		Run[StringJoin["cat ", fileName, "temp | tr -d '\"' > ", fileName]];
		Run[StringJoin["rm ", fileName, "temp"]]
		,
		Clear[Global`COutputStream]	
	];
	Clear[Global`IsFile];
	0
]

DebugCode[fileName_, code_, level_Integer] := 
Block[
{
	a = NewOutput[fileName], 
	Global`enableDebugging=level
}, 
	output = code[]; 
	CloseOutput[a];
	Clear[Global`enableDebugging]; 
	Print["Debugging done"];
	output
];

End[];
EndPackage[];
