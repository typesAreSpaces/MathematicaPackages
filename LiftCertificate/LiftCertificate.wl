(* ::Package:: *)

BeginPackage["LiftCertificate`"];

liftCertificate::usage="Lift a certificate from one basis to another.
- oldCertificate is {s0, ..., sm1} where 
  s0 + sum_{i=1}{m1}{si taui} equals some input polynomial
- certificates is Table[certificatei, {i,1,m2}] where 
  certificatei is the certificate of each taui with respect to 
  some set of generators";

Begin["`Private`"];

(*liftCertificate[oldCertificate_, certificates_] :=*)
 (*Module[{i, j, numGenerators, numSubs, currSOS, output},*)
  (*numGenerators = Length[certificates[[1]]] - 1;*)
  (*output = Table[0, numGenerators + 1];*)
  (*numSubs = Length[oldCertificate] - 1;*)
  
  (*output[[1]] = oldCertificate[[1]];*)
  (*For[i = 2, i <= numSubs + 1, i++,*)
   (*currSOS = oldCertificate[[i]];*)
   (*[>Unpack certificates[i]<]*)
   (*For[j = 1, j <= numGenerators + 1, j++,*)
    (*output[[j]] = output[[j]] + currSOS certificates[[i - 1, j]];*)
    (*]*)
   (*];*)
  
  (*Return[output];*)
  (*]*)

liftCertificate[oldCertificate_, certificates_] := Flatten[
  {oldCertificate} . Prepend[certificates, Prepend[Table[0, Length[certificates[[1]]] - 1], 1]]
  ]

End[];

EndPackage[];
