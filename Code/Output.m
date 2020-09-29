(* ::Package:: *)

(* ::Input::Initialization:: *)
(* Draws the Young diagram with the associated partition \[Lambda] *)
Options[DrawYoungDiagram]={ScaleFactor->20};
DrawYoungDiagram[\[Lambda]_,OptionsPattern[]]:=Module[{t\[Lambda],horizontalLines,verticalLines,result},
If[\[Lambda]==={},Return[Graphics[{},ImageSize->0]]];
t\[Lambda]=TransposePartition[\[Lambda]];

horizontalLines=Table[Line[{{0,-i},{\[Lambda][[i]],-i}}],{i,Length[\[Lambda]]}];
PrependTo[horizontalLines,Line[{{0,0},{\[Lambda][[1]],0}}]];
verticalLines=Table[Line[{{i,0},{i,-t\[Lambda][[i]]}}],{i,Length[t\[Lambda]]}];
PrependTo[verticalLines,Line[{{0,0},{0,-t\[Lambda][[1]]}}]];
result=Graphics[Join[horizontalLines,verticalLines],ImageSize->(OptionValue[ScaleFactor]Length[t\[Lambda]]),ImagePadding->None,ImageMargins->0,PlotRange->{{0,Length[t\[Lambda]]+0.2},{-(Length[\[Lambda]]+0.2),0}}];

Return[result];
]

(* Leave a 1-pixel border around the picture, because Mathematica sometimes crops the images *)
DrawYoungDiagramRaster[\[Lambda]_,scaleFactor_:9]:=DrawYoungDiagramRaster[\[Lambda],scaleFactor]=Module[{t\[Lambda],horizontalLines,verticalLines,result,nH,nV,dataArray},
If[\[Lambda]==={},Return[Null]];
t\[Lambda]=TransposePartition[\[Lambda]];

nH=scaleFactor Length[t\[Lambda]]+1;
nV=scaleFactor Length[\[Lambda]]+1;

horizontalLines=Table[{{0,-i},{\[Lambda][[i]],-i}},{i,Length[\[Lambda]]}];
PrependTo[horizontalLines,{{0,0},{\[Lambda][[1]],0}}];
verticalLines=Table[{{i,0},{i,-t\[Lambda][[i]]}},{i,Length[t\[Lambda]]}];
PrependTo[verticalLines,{{0,0},{0,-t\[Lambda][[1]]}}];

horizontalLines=scaleFactor horizontalLines;
verticalLines=scaleFactor verticalLines;

dataArray=ConstantArray[1,2+{nV,nH}]; (* leave 1 pixel border *)
Do[
dataArray[[2-hl[[1,2]],2+hl[[1,1]];;2+hl[[2,1]]]]=0dataArray[[2-hl[[1,2]],2+hl[[1,1]];;2+hl[[2,1]]]];
,{hl,horizontalLines}];
Do[
dataArray[[2-vl[[1,2]];;2-vl[[2,2]],2+vl[[1,1]]]]=0dataArray[[2-vl[[1,2]];;2-vl[[2,2]],2+vl[[1,1]]]];
,{vl,verticalLines}];

(* leave 1 pixel border *)
result=SetAlphaChannel[Image[dataArray,ImageSize->2+{nH,nV}],Image[1-dataArray,ImageSize->2+{nH,nV}]];
Return[result];
]
