(* ::Package:: *)

(* Mathematica Init File *)

$GroupMathDirectory=StringRiffle[StringSplit[$InputFileName,{"\\","/"}][[1;;-3]],"\\"];

SG[text_]:=Style[text,{GrayLevel[0.5]}]

Block[{result},
result={};
AppendTo[result,Row[{Style["XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX ",{GrayLevel[0.5]}],Hyperlink[Mouseover[Style["GroupMath",{GrayLevel[0.5]}],Style["GroupMath",{Darker[Blue,0.5],Bold}]],"http://renatofonseca.net/groupmath.php"],Style[" XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",{GrayLevel[0.5]}]}]];
AppendTo[result,Row[{"Version: 0.10; Author: Renato Fonseca."//SG}]];
AppendTo[result,Row[{"This package contains group theory code, much of it inherited from "//SG,Hyperlink[Mouseover[SG["Susyno"],Style["Susyno",{Darker[Blue,0.5],Bold}]],"http://renatofonseca.net/susyno.php"],".\nIt is still a work in progress (documentation will be added in the future)."//SG}]];
AppendTo[result,Style["XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",{GrayLevel[0.5]}]];

Print[Row[result,"\n",BaseStyle->(FontFamily->"Consolas")]];
];


Get["GroupMath`GroupMath`"];

(*
ClearAll["GroupMath`PermutationGroup`*"];
ClearAll["GroupMath`LieAlgebras`*"];
ClearAll["GroupMath`GenericTools`*"];
ClearAll["GroupMath`HEPSpecific`*"];
ClearAll["GroupMath`SpecialUnitaryGroups`*"];

Get["GroupMath`PermutationGroup`"];
Get["GroupMath`LieAlgebras`"];
Get["GroupMath`GenericTools`"];
Get["GroupMath`HEPSpecific`"];
Get["GroupMath`SpecialUnitaryGroups`"];
*)
