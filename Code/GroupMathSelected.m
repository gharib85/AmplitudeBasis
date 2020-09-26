(* ::Package:: *)

(* ::Input:: *)
(*(* main dependent functions *)*)
(*{DimR,Adjoint,SnIrrepDim,GenerateStandardTableaux, DecomposeSnProduct, PlethysmsN,ReduceRepProductBase1,ReduceRepProductBase2,HookContentFormula}*)


(* ::Input:: *)
(*(* other dependent functions *)*)
(*Union[*)
(*(* DimR *){DimRBaseMethod,PositiveRoots,FindM,MatrixD,SimpleProduct},*)
(*(* Adjoin *){AdjointBaseMethod,PositiveRoots,FindM},*)
(*(* SnIrrepDim *){},*)
(*(* GenerateStandardTableaux *){TransposePartition,TransposeTableaux,MaxIndex,GenerateStandardTableauxAux},*)
(*(* DecomposeSnProduct *){SnClassOrder,SnClassCharacter,RimHooks,PartitionSequence,RebuiltPartitionFromSequence},*)
(*(* PlethysmsN *){Plethysms,SnClassOrder,SnClassCharacter,RimHooks,PartitionSequence,RebuiltPartitionFromSequence,Adams,PositiveRoots,FindM,MatrixD,SimpleProduct,VDecomp,AltDom,LongestWeylWord,ReduceRepPolyProduct,IsSimpleGroupQ,RepName,RepName\[UnderBracket]BaseMethod,RepsUpToDimNNoConjugates,RepsUpToDimN,RepsUpToDimNAuxilarMethod,RepresentationIndex,RepresentationIndex\[UnderBracket]BaseMethod,ConjugacyClass,CMtoFamilyAndSeries,GroupsWithRankN2,CartanMatrix,ConjugateIrrep,ConjugateIrrepBase,GatherWeights},*)
(*(* ReduceRepProduct *){DominantWeights,PositiveRoots,FindM,MatrixD,DominateConjugate,SpecialMatrixD,ReflectWeight,SimpleProduct,WeylOrbit},*)
(*(* HookContentFormula *){}*)
(*]*)


(* ::Subsubsection::Closed:: *)
(*Generic Tool*)


(* ::Input::Initialization:: *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

GatherWeights[listW_]:=Module[{aux},
aux=Flatten[listW,1];
aux=Gather[aux,#1[[1]]==#2[[1]]&];

aux={#[[1,1]],Plus@@#[[1;;-1,2]]}&/@aux;
aux=DeleteCases[aux,x_/;x[[2]]==0];

Return[aux];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

GatherWeights[listW_,listMult_]:=Module[{aux},
aux=Table[{#[[1]],listMult[[i]]#[[2]]}&/@listW[[i]],{i,Length[listW]}];
aux=Flatten[aux,1];
aux=Gather[aux,#1[[1]]==#2[[1]]&];

aux={#[[1,1]],Plus@@#[[1;;-1,2]]}&/@aux;
aux=DeleteCases[aux,x_/;x[[2]]==0];
Return[aux];
]



(* ::Subsubsection::Closed:: *)
(*Permutation Group*)


(* ::Input::Initialization:: *)
(* Hook length formula for the dimension of the Sn representations. Should be the same as SnClassCharacter[partition,ConstantArray[1,Total[partition]]] *)
SnIrrepDim[partition_]:=Module[{n1,n2,inverseP,result},
n1=partition[[1]];
n2=Length[partition];
inverseP=Count[partition,x_/;x>=#]&/@Range[n1];
result=Table[Max[partition[[j]]+inverseP[[i]]-(j-1)-(i-1)-1,1],{i,n1},{j,n2}];
result=Total[partition]!/(Times@@Flatten[result]);
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This method decomposes the product of a list of Sn representations into its irreducible parts *)
DecomposeSnProduct[partitionsList_]:=Module[{n,characterTable,aux,result},
(* must be the same as for all partitions in partitionsList *)
n=Total[partitionsList[[1]]]; 
result=1/n!Table[Sum[SnClassOrder[i]Product[SnClassCharacter[inputPartition,i],{inputPartition,partitionsList}]SnClassCharacter[j,i],{i,IntegerPartitions[n]}],{j,IntegerPartitions[n]}];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* See arXiv:math/0309225v1[math.CO] - this is an auxiliar method to calculate SnClassCharacter *)
(* Note: a partitition is a list of non-increasing positive integers - see http://en.wikipedia.org/wiki/Young_tableau *)
PartitionSequence[partition_]:=Module[{sequence},
sequence=ConstantArray[1,partition[[-1]]];
AppendTo[sequence,0];
Do[
sequence=Join[sequence,ConstantArray[1,partition[[-i]]-partition[[-i+1]]]];
AppendTo[sequence,0];
,{i,2,Length[partition]}];
Return[sequence];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* See arXiv:math/0309225v1[math.CO] - this is an auxiliar method to calculate SnClassCharacter *)
(* This method finds all the rim hooks \[Xi] with length l and returns a list with all the possibilities {partition\\[Xi], leg length of rim hook \[Xi]} which is writen as {partition\\[Xi],ll(\[Xi])}*)
RimHooks[partition_,l_]:=Module[{seqMinusHook,sequence,length,result},
sequence=PartitionSequence[partition];
result={};

Do[
If[sequence[[i]]==1&&sequence[[i+l]]==0,

seqMinusHook=sequence;seqMinusHook[[i]]=0;seqMinusHook[[i+l]]=1;
length=Count[sequence[[i;;i+l]],0]-1;
AppendTo[result,{RebuiltPartitionFromSequence[seqMinusHook],length}];
];

,{i,Length[sequence]-l}];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* See arXiv:math/0309225v1[math.CO] - this is an auxiliar method to calculate SnClassCharacter *)
(* RebuiltPartitionFromSequence[PartitionSequence[partition]]=partition *)
RebuiltPartitionFromSequence[sequence_]:=Module[{start,end,validSequence,counter1s,result},
counter1s=0;result={};
Do[
If[sequence[[i]]==0,
PrependTo[result,counter1s];
,
counter1s++;
];

,{i,Length[sequence]}];
Return[DeleteCases[result,0]];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* See arXiv:math/0309225v1[math.CO] for the way to compute SnClassCharacter from the Murnaghan-Nakayama rule  *)
(* \[Lambda] is the representation; \[Mu] is the conjugacy class. This method computes the character of conjugacy class \mu in the irreducible representation \[Lambda]  *)
SnClassCharacter[partition\[Lambda]_,partition\[Mu]_]:=SnClassCharacter[partition\[Lambda],partition\[Mu]]=Module[{new\[Lambda]s,new\[Mu],n,result},

If[Length[partition\[Lambda]]==0,Return[1]];

n=Total[partition\[Lambda]];
If[n!=Total[partition\[Mu]],Return["Error in SnClassCharacter function: both partitions must be of the same order."]];

new\[Lambda]s=RimHooks[partition\[Lambda],partition\[Mu][[1]]];
new\[Mu]=partition\[Mu][[2;;-1]];

result=Sum[(-1)^new\[Lambda]s[[i,2]] SnClassCharacter[new\[Lambda]s[[i,1]],new\[Mu]],{i,Length[new\[Lambda]s]}];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Reference: Unless otherwise stated, the reference for the code below was the Lie Manual available in http://www-math.univ-poitiers.fr/~maavl/LiE/ *)

(* Size of a given conjugacy class of Sn. The formula is easy but see for example "Enumerative Combinatorics", Richard P.Stanley, http://math.mit.edu/~rstan/ec/ec1.pdf, 1.3.2 Proposition *)
SnClassOrder[partition_]:=SnClassOrder[partition]=Module[{aux,n,result},
n=Total[partition];
aux=Tally[partition];
result=n!/Product[aux[[i,1]]^aux[[i,2]] aux[[i,2]]!,{i,Length[aux]}];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

VDecomp[cm_,dominantWeight_]:=Module[{result},
result=AltDom[cm,WeylOrbit[cm,dominantWeight]];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

AltDom[cm_,weights_,weylWord_]:=Module[{cmInv,matD,cmID,aux,prov,result},
prov={#,1}&/@weights;


Do[
(* aux=SimpleProduct[prov[[j]],cm[[i]],cmID]; *)
If[prov[[j,2]]!=0,
Which[prov[[j,1,weylWord[[i]]]]>=0,Null,
prov[[j,1,weylWord[[i]]]]==-1,prov[[j,2]]=0,
prov[[j,1,weylWord[[i]]]]<=-2,prov[[j,2]]=-prov[[j,2]];prov[[j,1]]=prov[[j,1]]-(prov[[j,1,weylWord[[i]]]]+1)cm[[weylWord[[i]]]];

];

];

,{i,Length[weylWord]},{j,Length[prov]}];
prov=DeleteCases[prov,x_/;x[[2]]==0];

Return[prov];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

AltDom[cm_,weights_]:=AltDom[cm,weights,LongestWeylWord[cm]]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Adams[cm_,n_,rep_]:=Module[{aux,result},
aux=DominantWeights[cm,rep];
aux={#[[1]] n,#[[2]]}&/@aux;

result=Table[{VDecomp[cm,aux[[i,1]]],aux[[i,2]]},{i,Length[aux]}];
result=Table[{result[[i,1,j,1]],result[[i,1,j,2]]result[[i,2]]},{i,Length[result]},{j,Length[result[[i,1]]]}];
result=Flatten[result,1];
Return[result];
]
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Plethysms[cm_,weight_,partition_]:=Plethysms[cm,weight,partition]=Module[{n,kList,aux,aux1,aux2,factor,sum},

n=Plus@@partition;

(* If group = U1 *)
If[cm===U1,
Return[If[Length[partition]==1,{{n weight,1}},{}]];
];

kList=IntegerPartitions[n];
sum={};

Do[
factor=1/n!SnClassOrder[kList[[i]]]SnClassCharacter[partition,kList[[i]]];

aux=Adams[cm,#,weight]&/@kList[[i]];

aux=ReduceRepPolyProduct[cm,aux];
aux={#[[1]],factor #[[2]]}&/@aux;

AppendTo[sum,aux];
,{i,Length[kList]}];

sum=GatherWeights[sum];
Return[sum];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Added 18/December/2018 *)
(* Essentially it uses Plethysms to calculate the all plethysms for all partitions of some n *)

PlethysmsN[groupSimple_,rep_,n_]:=PlethysmsN[groupSimple,rep,n]=Module[{partitions,result},
partitions=IntegerPartitions[n];
result={Plethysms[groupSimple,rep,#],#}&/@partitions;
result=DeleteCases[result,{{},_}];

result=Table[{result[[i,1,j,1]],result[[i,2]],result[[i,1,j,2]]},{i,Length[result]},{j,Length[result[[i,1]]]}];
result=Flatten[result,1];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* This method calculates the decompositions of a product of sums of irreps: (R11+R12+R13+...) x (R21+R22+R23+...) x ... *)
(* polyList = list of lists of representations to be multiplied. The method outputs the decomposition of such a product *)
ReduceRepPolyProduct[cm_,polyList_]:=Module[{n,aux,aux2},

n=Length[polyList];
aux=polyList[[1]];
If[n<=1,Return[aux]];
Do[
aux=Tuples[{aux,polyList[[i+1]]}];

aux2=ReduceRepProduct[cm,#[[1;;2,1]]]&/@aux;

aux=GatherWeights[aux2,#[[1,2]]#[[2,2]]&/@aux];
,{i,n-1}];

Return[aux];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Hook-content formula: counts the number of semi-standard Young tableaux of shape given by partition and with the cells filled with the numbers 1,...,n *)
HookContentFormula[partition_,nMax_]:=Module[{n1,n2,inverseP,hookLengths,content,result,aux},
n1=partition[[1]];
n2=Length[partition];
inverseP=Count[partition,x_/;x>=#]&/@Range[n1];

aux=Table[If[partition[[j]]+inverseP[[i]]-(j-1)-(i-1)-1>0,(nMax+i-j)/(partition[[j]]+inverseP[[i]]-(j-1)-(i-1)-1),1],{i,n1},{j,n2}];
result=Times@@Flatten[aux];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

TransposeTableaux[tableaux_]:=DeleteCases[Transpose[PadRight[#,Length[tableaux[[1]]],Null]&/@tableaux],Null,-1]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

TransposePartition[partition_]:=Module[{n1,n2,inverseP},
If[partition==={},Return[{}]];
n1=partition[[1]];
n2=Length[partition];
inverseP=Count[partition,x_/;x>=#]&/@Range[n1];
Return[inverseP];
]

(* Returns a Young tableaux with the entries filled with the maximum entry in each square, if the tableaux is to be standard *)
MaxIndex[partition_]:=Module[{partitionT,result},
partitionT=TransposePartition[partition];
result=Table[
Total[partition]-Total[partition[[1;;i-1]]]-Total[partitionT[[1;;j-1]]]+(i-1)(j-1)
,{i,Length[partition]},{j,partition[[i]]}];
result=Total[partition]+1-result;
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Generates all Standard Tableaux with a given shape *)
GenerateStandardTableaux[\[Lambda]_]:=Module[{n,\[Lambda]T,canonicalTableaux,canonicalTableauxT,affectedByList,minIndTable,maxIndTable,result},
If[\[Lambda]==={},Return[{}]];

n=Total[\[Lambda]];
\[Lambda]T=TransposePartition[\[Lambda]];
canonicalTableaux=MapThread[Range,{Accumulate[\[Lambda]]-\[Lambda]+1,Accumulate[\[Lambda]]}];
canonicalTableauxT=TransposeTableaux[canonicalTableaux];

affectedByList=ConstantArray[{},n];

Do[AppendTo[affectedByList[[canonicalTableaux[[i,j-1]]]],canonicalTableaux[[i,j]]],{i,1,Length[\[Lambda]]},{j,2,\[Lambda][[i]]}];
Do[AppendTo[affectedByList[[canonicalTableauxT[[i,j-1]]]],canonicalTableauxT[[i,j]]],{i,1,Length[\[Lambda]T]},{j,2,\[Lambda]T[[i]]}];

maxIndTable=Flatten[MaxIndex[\[Lambda]]];
minIndTable=ConstantArray[1,n];

result=GenerateStandardTableauxAux[ConstantArray[0,n],1,affectedByList,minIndTable,maxIndTable];
result=Transpose[MapThread[result[[All,#1;;#2]]&,{Accumulate[\[Lambda]]-\[Lambda]+1,Accumulate[\[Lambda]]}]];

Return[result];
]

(* Auxiliar function to GenerateStandardTableaux *)
GenerateStandardTableauxAux[incompleteList_,idxToFill_,affectedByList_,minIndTable_,maxIndTable_]:=Module[{i,possibleFillings,aux,possibities,minIndTables,result},
If[Abs[maxIndTable-minIndTable]=!=maxIndTable-minIndTable,Return[{}]];

possibleFillings=Complement[Range[minIndTable[[idxToFill]],maxIndTable[[idxToFill]]],incompleteList[[1;;idxToFill-1]]];
possibities=Table[aux=incompleteList;aux[[idxToFill]]=i;aux,{i,possibleFillings}];
minIndTables=Table[aux=minIndTable;aux[[affectedByList[[idxToFill]]]]=Table[Max[aux[[el]],i+1],{el,affectedByList[[idxToFill]]}];aux,{i,possibleFillings}];

If[idxToFill==Length[incompleteList],
Return[possibities];
,
result=Table[GenerateStandardTableauxAux[possibities[[i]],idxToFill+1,affectedByList,minIndTables[[i]],maxIndTable],{i,Length[possibleFillings]}];
Return[Flatten[result,1]];
];
]


(* ::Subsubsection::Closed:: *)
(*Draw Young Diagram*)


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


(* ::Subsubsection::Closed:: *)
(*Lie Algebra*)


(* ::Input::Initialization:: *)
CartanMatrix[name_String,numberId_Integer]:=CartanMatrix[name,numberId]=Module[{result},
result="Unknown simple lie algebra. Try SU(n) [n>1],SO(n) [n=3 or >4],Sp(2n) [n>1] or the exceptionals G(2),F(4),E(6),E(7),E(8).";

(* Classical algebras *)

If[(ToUpperCase[name]=="A"||ToUpperCase[name]=="B"||ToUpperCase[name]=="C")&&numberId==1,
result={{2}};
];
If[ToUpperCase[name]=="A"&&numberId>1,
result=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{numberId,numberId}]//Normal;
];
If[ToUpperCase[name]=="B"&&numberId>1,
result=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{numberId,numberId}]//Normal;
result[[numberId-1,numberId]]=-2;
];
If[ToUpperCase[name]=="C"&&numberId>1,
result=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{numberId,numberId}]//Normal;
result[[numberId,numberId-1]]=-2;
];
If[ToUpperCase[name]=="D"&&numberId>=2,
If[numberId==2,result=2IdentityMatrix[2] (* This is SO4=SU2xSU2 *),
result=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{numberId,numberId}]//Normal;
result[[numberId,numberId-1]]=0;
result[[numberId-1,numberId]]=0;
result[[numberId,numberId-2]]=-1;
result[[numberId-2,numberId]]=-1;
]
];

(* Classical algebras, with alternative names *)

If[ToUpperCase[name]=="SU", (*   SU(n+1)=A(n)   *)
result=CartanMatrix["A", numberId-1]];
If[ToUpperCase[name]=="SP"&&EvenQ[numberId], (*   Sp(2n)=C(n)   *)
result=CartanMatrix["C", numberId/2]];
If[ToUpperCase[name]=="SO"&&!EvenQ[numberId], (*   SO(2n+1)=B(n)   *)
result=CartanMatrix["B", (numberId-1)/2]];
If[ToUpperCase[name]=="SO"&&EvenQ[numberId], (*   SO(2n)=D(n)   *)
result=CartanMatrix["D", numberId/2]];


(* Exceptional algebras *)

If[ToUpperCase[name]=="G"&&numberId==2,
result={{2,-3},{-1,2}};
];

If[ToUpperCase[name]=="F"&&numberId==4,
result=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{4,4}]//Normal;
result[[2,3]]=-2;
];

If[ToUpperCase[name]=="E"&&(numberId==6||numberId==7||numberId==8),
result=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{numberId,numberId}]//Normal;
result[[numberId-1,numberId]]=0;result[[numberId,numberId-1]]=0;result[[3,numberId]]=-1;result[[numberId,3]]=-1;
];

Return[result];
]

(*Assign to some variables the groups' Cartan matrix*)

Do[
Evaluate[ToExpression["SU"<>ToString[i]]]=Evaluate[ToExpression["Su"<>ToString[i]]]=Evaluate[ToExpression["su"<>ToString[i]]]=CartanMatrix["SU",i];
,{i,2,32}]
Do[
Evaluate[ToExpression["SO"<>ToString[i]]]=Evaluate[ToExpression["So"<>ToString[i]]]=Evaluate[ToExpression["so"<>ToString[i]]]=CartanMatrix["SO",i];
,{i,5,32}]
Do[
Evaluate[ToExpression["SP"<>ToString[i]]]=Evaluate[ToExpression["Sp"<>ToString[i]]]=Evaluate[ToExpression["sp"<>ToString[i]]]=CartanMatrix["SP",i];
,{i,2,32,2}]
SO3=So3=so3=CartanMatrix["SO",3];

E6=e6=CartanMatrix["E",6];
E7=e7=CartanMatrix["E",7];
E8=e8=CartanMatrix["E",8];
G2=g2=CartanMatrix["G",2];
F4=f4=CartanMatrix["F",4];
U1=u1=CartanMatrix["U",1]=CartanMatrix["u",1]={};

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Returns True if group is ***not*** a list of groups {g1,g2,...} *)
(* Examples: IsSimpleGroupQ[U1]=IsSimpleGroupQ[SO10]=True; IsSimpleGroupQ[{SO10}]=IsSimpleGroupQ[{U1,U1}]=IsSimpleGroupQ[{SU3,SU2,U1}]=False. *)
IsSimpleGroupQ[group_]:=If[Depth[group]==2||(Depth[group]==3&&group=!=ConstantArray[U1,Length[group]]),Return[True],Return[False]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* DESCRIPTION: Returns the list of positive roots of a group *)
PositiveRoots[cm_]:=PositiveRoots[cm]=Module[{n,weights,aux1,aux2,aux3,cont},
n=Length[cm]; (* =number of simple roots *)
weights=cm;
aux1=Table[KroneckerDelta[i,j],{i,n},{j,n}];
cont=0;

While[cont<Length[weights],
cont++;
aux2=aux1[[cont]];

Do[
aux3=aux2;
aux3[[i]]++;
If[FindM[aux1,aux2,i]-weights[[cont,i]]>0 && Count[aux1,aux3]==0,
weights=Append[weights,weights[[cont]]+cm[[i]]];
aux1=Append[aux1,aux3];
,Null];

,{i,n}];
];

Return[weights];]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

SpecialMatrixD[cm_]:=SpecialMatrixD[cm]=Module[{n,result,k},
n=Length[cm];
result=Table[0,{i,n},{j,4}];

Do[
k=1;
Do[
If[cm[[i,j]]==-1,
result[[i,k]]=j;k++;
];
If[cm[[i,j]]==-2,
result[[i,k]]=j;result[[i,k+1]]=j;k=k+2;
];
If[cm[[i,j]]==-3,
result[[i,k]]=j;result[[i,k+1]]=j;result[[i,k+2]]=j;k=k+3;
];
,{j,n}],{i,n}];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

ReflectWeight[cm_,weight_,i_]:=Module[{mD,result},
result= weight;
result[[i]]=-weight[[i]];
mD=SpecialMatrixD[cm];
Do[
If[mD[[i,j]]!=0,result[[mD[[i,j]]]]+=weight[[i]]];
,{j,4}];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This function fails for example if cm={{2,0},{0,2}}= SU2xSU2. This is not 100% satisfactory, but in practice is not a problem. *)
DominantConjugate[cm_,weight_]:=DominantConjugate[cm,weight]=Module[{index,dWeight,i,mD},
If[cm=={{2}},Return[If[weight[[1]]<0,{-weight,1},{weight,0}]]]; (* for SU2 the code below would not work *)
index=0;
dWeight=weight;
i=1;
mD=SpecialMatrixD[cm];

While[i<=Length[cm],
If[dWeight[[i]]<0,
index++;
dWeight=ReflectWeight[cm,dWeight,i];
i=Min[mD[[i,1]],i+1]; (* Original reference suggests just i=mD[[i,1]]; But this would lead to a bug. *)
,i++];
];
Return[{dWeight,index}];
]

WeylOrbit[cm_,weight_]:=WeylOrbit[cm,weight]=Module[{lastListWl,n,result,aux,temp},
n=Length[cm];

lastListWl={weight};

result=Reap[
Sow[{weight}];
While[Length[lastListWl]!=0,

temp=If[Abs[#]==-#,Null,ConstantArray[#,n]-# cm]&/@lastListWl; (* This carries out at once the WeylReflections *)
lastListWl=Reap[Do[

If[lastListWl[[j,i]]>0&&temp[[j,i,i+1;;n]] ==Abs[temp[[j,i,i+1;;n]]],
Sow[temp[[j,i]]];
];
,{j,Length[lastListWl]},{i,n}]][[2]];

If[lastListWl!={},
lastListWl=lastListWl[[1]];
Sow[lastListWl];
];
]][[2,1]];

result=Flatten[result,1];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

DominantWeights[cm_,w_]:=DominantWeights[cm,w]=Module[{proots,listw,counter,aux,functionAux,result,aux1,aux2,n,k,cmInv,matD,cmID,deltaTimes2},
cmInv=Inverse[cm];

(* ------------------------ Generate the dominant weights without dimentionality information ------------------------*)

proots=PositiveRoots[cm];
listw={w};
counter=1;
While[counter<=Length[listw],
aux=Table[listw[[counter]]-proots[[i]],{i,Length[proots]}];
listw=DeleteDuplicates[Join[listw,DeleteCases[aux,x_/;x!=Abs[x]]]];
counter++;
];
listw=Sort[listw,OrderedQ[{-{#1-#2}.cmInv,0{#1}}]&]; 

(* ------------------------ Get dimentionality information ------------------------*)

result={{listw[[1]],1}};
functionAux[x__]=0;
functionAux[listw[[1]]]=1;

(* Invert cm and get the diagonal matrix with entries <root i, root i> *)
n=Length[cm];
matD=MatrixD[cm];
cmID=cmInv.matD;
deltaTimes2=Sum[proots[[i]],{i,Length[proots]}];

Do[

Do[
k=1;

While[(aux1=functionAux[DominantConjugate[cm,k proots[[i]]+listw[[j]]][[1]]])!=0,
aux2=k proots[[i]]+listw[[j]];
functionAux[listw[[j]]]+=2 aux1 SimpleProduct[aux2,proots[[i]],cmID];
k++;

];

,{i,Length[proots]}];

functionAux[listw[[j]]]=functionAux[listw[[j]]]/SimpleProduct[listw[[1]]+listw[[j]]+deltaTimes2,listw[[1]]-listw[[j]],cmID];


result=Append[result,{listw[[j]],functionAux[listw[[j]]]}];
,{j,2,Length[listw]}];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Reference:  the Lie Manual available in http://www-math.univ-poitiers.fr/~maavl/LiE/ *)
LongestWeylWord[cm_]:=LongestWeylWord[cm]=Module[{n,weight,aux,result},
n=Length[cm];
weight=-ConstantArray[1,n];
result={};
While[weight!=Abs[weight],
aux=Position[weight,x_/;x<0,1,1][[1,1]];
weight=ReflectWeight[cm,weight,aux];
PrependTo[result,aux];
];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Adjoint[input__]:=If[Depth[{input}]<=4,Return[AdjointBaseMethod[input]],Return[AdjointBaseMethod@@@Transpose[{input}]]];

(* DESCRIPTION: Max weight of the adjoint representation is just the largest  positive root of the algebra [NOTE: this is correct only if the given group is simple. Otherwise the adjoint representation is not even irreducible] *)
AdjointBaseMethod[cm_]:=If[cm==={},0,If[cm===ConstantArray[{},Length[cm]],ConstantArray[0,Length[cm]],PositiveRoots[cm][[-1]]]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

ConjugateIrrep[input__]:=ConjugateIrrep[input]=If[IsSimpleGroupQ[{input}[[1]]],ConjugateIrrepBase[input],ConjugateIrrepBase@@@Transpose[{input}]];

(* Old, innefient way of calculating the conjugate representation *)
(* ConjugateIrrepBase[cm_,rep_]:=If[cm==={},-rep,-Weights[cm,rep][[-1,1]]] *)

(* See for example "A SHORT INTRODUCTION TO SIMPLE LIE ALGEBRA REPRESENTATIONS", JOSH GUFFIN, http://www.math.upenn.edu/~guffin/teaching/talks/rep.pdf *)
ConjugateIrrepBase[cm_,rep_]:=If[cm==={}||cm===ConstantArray[{},Length[cm]],-rep,-Fold[ReflectWeight[cm,#1,#2]&,rep,LongestWeylWord[cm]]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

SimpleProduct[v1_,v2_,cmID_]:=1/2 ({v1}.cmID.Transpose[{v2}])[[1,1]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(*DESCRIPTION: This method returns a diagonal matrix with the values <root i, root i> *)
MatrixD[cm_]:=MatrixD[cm]=Module[ {positions,result,coord1,coord2},
positions=Position[cm,-1|-2|-3,-1];
positions=Sort[Select[positions,#[[1]]<#[[2]]&]];

(*Assume for now that all roots are the same size*)
result=Table[1,{i,Length[cm]}];
Do[
coord1=positions[[j,1]];
coord2=positions[[j,2]];
(*Give the correct value to <\alpha,\alpha>*)
result[[coord2]]=cm[[coord2,coord1]]/cm[[coord1,coord2]] result[[coord1]];
,{j,Length[positions]}];

result=DiagonalMatrix[result];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* DESCRIPTION: Returns the weights of a representation (with dimentionalities) *)
Weights;
Unprotect[Weights];
Weights[cm_,w_]:=Weights[cm,w]=Module[{dW,result,invCM},

(* Reorder the weights of conjugate representations so that RepMatrices[group,ConjugateIrrep[group,w]]=-Conjugate[RepMatrices[group,w]] and Invariants[group,{w,ConjugateIrrep[group,w]},{False,False}]=a[1]b[1]+...+a[n]b[n] *)
If[OrderedQ[{w,ConjugateIrrep[cm,w]}]&& ConjugateIrrep[cm,w]=!=w,Return[{-1,1}#&/@Weights[cm,ConjugateIrrep[cm,w]]]]; 

invCM=Inverse[cm];
dW=DominantWeights[cm,w];
result=Table[{#,dW[[i,2]]}&/@WeylOrbit[cm,dW[[i,1]]],{i,Length[dW]}];
result=Apply[Join,result];
result=Sort[{-#[[1]].invCM,#}&/@result];
result=result[[All,2]];
(*  result=Sort[result,OrderedQ[{-{#1[[1]]-#2[[1]]}.invCM,0{#1[[1]]}}]&]; *)

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Auxiliar method *)
FindM[ex_,el_,indice_]:=Module[{auxMax,aux1,aux2},
aux1=el[[indice]];
aux2=el;
aux2[[indice]]=0;
auxMax=0;
Do[

If[Count[ex,aux2]==1,auxMax=aux1-i+1;Goto[end];
,Null];
aux2[[indice]]=aux2[[indice]]+1;

,{i,aux1+1}];
Label[end];
Return[auxMax];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Reduces a direct product representation in its irreducible parts *)

Options[ReduceRepProduct]={UseName->False};
ReduceRepProduct[group_,repsList_,OptionsPattern[]]:=ReduceRepProduct[group,repsList]=Module[{output},
If[IsSimpleGroupQ[group],
output=ReduceRepProductBase[group,repsList];
,
output={#[[1;;-1,1]],Times@@#[[1;;-1,2]]}&/@Tuples[MapThread[ReduceRepProductBase[#1,#2]&,{group,Transpose[repsList]}]];
];
If[OptionValue[UseName],output={RepName[group,Simplify[#[[1]]]],#[[2]]}&/@output];
Return[output];
];

(* Deals with possible factor groups/reps *)
ReduceRepProductBase[cm_,repsList_]:=Module[{n,orderedList,result},

(* If the group is U1 - trivial *)
If[cm==U1,Return[{{Plus@@repsList,1}}]];

(* If there is only one rep in listReps - trivial *)
If[Length[repsList]==1,Return[{{repsList[[1]],1}}]];

orderedList=Sort[repsList,DimR[cm,#1]<DimR[cm,#2]&];
n=Length[orderedList];
result=ReduceRepProductBase2[cm,orderedList[[n-1]],orderedList[[n]]];
Do[
result=ReduceRepProductBase1[cm,orderedList[[n-i]],result];
,{i,2,n-1}];
Return[result];
]

ReduceRepProductBase1[cm_,rep1_,listReps_]:=Module[{result},
result=Table[({#[[1]],listReps[[i,2]]#[[2]]})&/@ReduceRepProductBase2[cm,rep1,listReps[[i,1]]],{i,Length[listReps]}];
result=Join@@result;
result=GatherBy[result,#[[1]]&];
result=Table[{result[[i,1,1]],Sum[result[[i,j,2]],{j,Length[result[[i]]]}]},{i,Length[result]}];
Return[result];
]

ReduceRepProductBase2[cm_,w1_,w2_]:=Module[{l1,wOrbit,delta,n,aux,dim,allIrrep,result},
n=Length[cm];
delta=Table[1,{i,n}];

l1=DominantWeights[cm,w1];
dim[x_]=0;
allIrrep={};
Do[
wOrbit=WeylOrbit[cm,l1[[i,1]]];
Do[
aux=DominantConjugate[cm,wOrbit[[j]]+w2+delta];

If[aux[[1]]-1==Abs[aux[[1]]-1], (*regular*)
dim[aux[[1]]-delta]+=(-1)^aux[[2]] l1[[i,2]];
allIrrep=DeleteDuplicates[Append[allIrrep,aux[[1]]-delta]];
];
,{j,Length[wOrbit]}];

,{i,Length[l1]}];

result=Table[{allIrrep[[i]],dim[allIrrep[[i]]]},{i,Length[allIrrep]}];
result=DeleteCases[result,x_/;x[[2]]==0];
Return[result];
];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Calculates the dimention of a irrep *)
DimR[input__]:=DimR[input]=Switch[Depth[{input}],x_/;(x==3||x==4),DimRBaseMethod[input],5,DimRBaseMethod@@@Transpose[{input}]];

DimRBaseMethod[cm_,w_]:=Module[{n,proots,cmInv,matD,cmID,delta,result},
If[cm==={},Return[1]]; (* U1 group *)
If[cm===ConstantArray[{},Length[cm]],Return[ConstantArray[1,Length[cm]]]]; (* multiple U1 group *)

n=Length[cm];
proots=PositiveRoots[cm];

(* Invert cm and get the diagonal matrix with entries <root i, root i> *)
cmInv=Inverse[cm];
matD=MatrixD[cm];
cmID=cmInv.matD;
delta=1/2 Sum[proots[[i]],{i,Length[proots]}];
result=Product[SimpleProduct[proots[[i]],w+delta,cmID]/SimpleProduct[proots[[i]],delta,cmID]  ,{i,Length[proots]}];

Return[result];
]



(* ::Input::Initialization:: *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Uses formula XI.31 of "Semi-Simple Lie Algebras and Their Representations", page 91 *)
RepresentationIndex[input__]:=(* RepresentationIndex[input]=*)Switch[Depth[{input}],x_/;(x==3||x==4),RepresentationIndex\[UnderBracket]BaseMethod[input],5,RepresentationIndex\[UnderBracket]BaseMethod@@@Transpose[{input}]];

RepresentationIndex\[UnderBracket]BaseMethod[cm_,rep_]:=Module[{\[Delta],cmInv,matD,cmID,result},
\[Delta]=ConstantArray[1,Length[cm]];
cmInv=Inverse[cm];
matD=MatrixD[cm];
cmID=cmInv.matD/Max[matD];

(* Factor of 2 ensures is due to the fact that SimpleProduct is defined such that Max[<\[Alpha],\[Alpha]>]=1 (considering all positive roots), but we would want it to be =2 *)
result=DimR[cm,rep]/DimR[cm,Adjoint[cm]]2SimpleProduct[rep,rep+2\[Delta],cmID];
Return[result];
]


(* ::Input::Initialization:: *)
ConjugacyClass[cm_,rep_]:=Module[{series,n,aux,result},
If[cm===U1,Return[{rep}]];
{series,n}=CMtoFamilyAndSeries[cm];

(* If[series==="A",result={Mod[Sum[rep[[i]],{i,n}],n+1]}]; *)
If[series==="A",result={Mod[Sum[i rep[[i]],{i,n}],n+1]}];
If[series==="B",result={Mod[rep[[n]],2]}];
If[series==="C",result={Mod[Sum[rep[[i]],{i,1,n,2}],2]}];

If[series==="D"&&OddQ[n],result={Mod[rep[[-2]]+rep[[-1]],2],Mod[2Sum[rep[[i]],{i,1,n-2,2}]+(n-2)rep[[-2]]+n rep[[-1]],4]}];
If[series==="D"&&EvenQ[n],result={Mod[rep[[-2]]+rep[[-1]],2],Mod[2Sum[rep[[i]],{i,1,n-3,2}]+(n-2)rep[[-2]]+n rep[[-1]],4]}]

If[series==="E"&&n==6,result={Mod[rep[[1]]-rep[[2]]+rep[[4]]-rep[[5]],3]}];
If[series==="E"&&n==7,result={Mod[rep[[4]]+rep[[6]]+rep[[7]],2]}];
If[series==="E"&&n==8,result={0}];
If[series==="F",result={0}];
If[series==="G",result={0}];

Return[result];
]

(* For both RepsUpToDimN, RepsUpToDimNNoConjugates: list is sorted according to smaller dim, smaller representation index, smallar conjugacy class numbers, larger Dynkin coefficients [in this order of importance] *)

(* For a simple group, this method calculates all the representations up to a given size maxDim *)
Options[RepsUpToDimN]={UseName->False,SortResult->True};
Options[RepsUpToDimNNoConjugates]={UseName->False,SortResult->True};

RepsUpToDimN[group_,maxDim_,OptionsPattern[]]:=RepsUpToDimN[group,maxDim,UseName->OptionValue[UseName],SortResult->OptionValue[SortResult]]=Module[{result},
(* This is for speed: calculate the expression for a generic representation of the group and pass it on to RepsUpToDimNAuxilarMethod *)
fastDimR[w_]:=Evaluate[DimR[group,Array[rdm\[UnderBracket]mrk,Length[group]]]]/.MapThread[Rule,{Evaluate[Array[rdm\[UnderBracket]mrk,Length[group]]],w}];

result=Reap[RepsUpToDimNAuxilarMethod[group,ConstantArray[0,Length[group]],1,maxDim,fastDimR]][[2,1]];

If[OptionValue[SortResult],result=Sort[result,OrderedQ[{Join[{DimR[group,#1],RepresentationIndex[group,#1]},ConjugacyClass[group,#1],-#1],Join[{DimR[group,#2],RepresentationIndex[group,#2]},ConjugacyClass[group,#2],-#2]}]&]];

If[OptionValue[UseName],result=RepName[group,#]&/@result];

Return[result];
]
(* Same as RepsUpToDimN but returns only one representation for each pair of conjugate representations *)
RepsUpToDimNNoConjugates[group_,maxDim_,OptionsPattern[]]:=Module[{aux,cR,cRTag,rTag,result},
aux=RepsUpToDimN[group,maxDim];
result=aux;
Do[
cR=ConjugateIrrep[group,aux[[i]]];
cRTag=Join[{RepresentationIndex[group,cR]},ConjugacyClass[group,cR],-cR];
rTag=Join[{RepresentationIndex[group,aux[[i]]]},ConjugacyClass[group,aux[[i]]],-aux[[i]]];
If[!OrderedQ[{rTag,cRTag}],result[[i]]=False,result[[i]]==aux[[i]]];
,{i,Length[aux]}];
result=DeleteCases[result,False];

If[OptionValue[SortResult],result=Sort[result,OrderedQ[{Join[{DimR[group,#1],RepresentationIndex[group,#1]},ConjugacyClass[group,#1],-#1],Join[{DimR[group,#2],RepresentationIndex[group,#2]},ConjugacyClass[group,#2],-#2]}]&]];

If[OptionValue[UseName],result=RepName[group,#]&/@result];

Return[result];
]

(* This is a recursive auxiliar method used by RepsUpToDimN and is not meant to be used directly *)
RepsUpToDimNAuxilarMethod[group_,w_,digit_,max_,fastDimR_]:=Module[{wAux,newResult},
wAux=w;
wAux[[digit]]=0;

(* If it is a leaf ... *)
If[digit==Length[w],
While[fastDimR[wAux]<=max,
Sow[wAux]; (* works like AppendTo[<some list>] with the encosing Reap (in RepsUpToDimN) *)
wAux[[digit]]++;
];,
While[fastDimR[wAux]<=max,
RepsUpToDimNAuxilarMethod[group,wAux,digit+1,max,fastDimR];
wAux[[digit]]++;
];
];

]



(* ::Input::Initialization:: *)
(* Code for getting the name of representations given by Dynkin coefficients *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Options[RepName]={ReturnAll->False};
Options[RepName\[UnderBracket]BaseMethod]={ReturnAll->False};

(* Matches the names of Slansky with two exceptions: {0,2} of SU(3) is the 6 [not {2,0}], and in SO(10) {0,0,0,2,0} is the 126 [not {0,0,0,0,2}]. On the other hand, it matches reference 1206.6379 completely (as far as could be checked) *)
(* UPDATE: these exceptions were taken care off (ie, implemented), so that Slansky's convention is followed. *)
RepName[group_,rep_,OptionsPattern[]]:= RepName[group,rep,ReturnAll->OptionValue[ReturnAll]]=If[IsSimpleGroupQ[group],RepName\[UnderBracket]BaseMethod[group,rep,ReturnAll->OptionValue[ReturnAll]],If[OptionValue[ReturnAll],RepName\[UnderBracket]BaseMethod[#1,#2,ReturnAll->OptionValue[ReturnAll]]&@@@MapThread[List,{group,rep}],If[Length[group]==1,RepName\[UnderBracket]BaseMethod[group[[1]],rep[[1]],ReturnAll->OptionValue[ReturnAll]],CircleTimes@@(RepName\[UnderBracket]BaseMethod[#1,#2,ReturnAll->OptionValue[ReturnAll]]&@@@MapThread[List,{group,rep}])]]]

RepName\[UnderBracket]BaseMethod[group_,rep_,OptionsPattern[]]:=Module[{dim,reps,cR,cRTag,rTag,barQ,compareRep,nPrimes,subscript,printForm,result,aux},

If[group===U1,
result={If[Length[rep]<2,ToString[StandardForm[rep]],"("<>ToString[StandardForm[rep]]<>")"],{1,False,0}};
If[!OptionValue[ReturnAll],result=result[[1]]];
Return[result];
];

(* Exceptions to the rules below *)
(*
If[group===SU3&&rep==={0,2},
result={OverBar[Style["6",Bold]],{6,True,0}};
If[!OptionValue[ReturnAll],result=result[[1]]];
Return[result];
];
If[group===SU3&&rep==={2,0},
result={Style["6",Bold],{6,False,0}};
If[!OptionValue[ReturnAll],result=result[[1]]];
Return[result];
];
If[group===SO10&&rep==={0,0,0,2,0},
result={OverBar[Style["126",Bold]],{126,True,0}};
If[!OptionValue[ReturnAll],result=result[[1]]];
Return[result];
];
If[group===SO10&&rep==={0,0,0,0,2},
result={Style["126",Bold],{126,False,0}};
If[!OptionValue[ReturnAll],result=result[[1]]];
Return[result];
];
*)

dim=DimR[group,rep];
reps=RepsUpToDimNNoConjugates[group,dim];
reps=DeleteCases[reps,x_/;DimR[group,x]!=dim];
reps=Sort[reps,OrderedQ[{Join[{DimR[group,#1],RepresentationIndex[group,#1]},ConjugacyClass[group,#1],-#1],Join[{DimR[group,#2],RepresentationIndex[group,#2]},ConjugacyClass[group,#2],-#2]}]&];

(* A bar is needed? *)
cR=ConjugateIrrep[group,rep];
cRTag=Join[{RepresentationIndex[group,cR]},ConjugacyClass[group,cR],-cR];
rTag=Join[{RepresentationIndex[group,rep]},ConjugacyClass[group,rep],-rep];
barQ=!OrderedQ[{rTag,cRTag}];

(* How many primes are needed? *)
nPrimes=Flatten[If[barQ,Position[reps,cR],Position[reps,rep]]][[1]]-1;


(* Print the result *)
printForm=Style[ToString[dim]<>StringJoin[ConstantArray["'",nPrimes]],Bold];
If[barQ,printForm=OverBar[printForm]];
result={printForm,{dim,barQ,nPrimes}};


(* So(8) requires special care *)
If[group===SO8,
subscript="";
aux=Tally[rep[[{1,3,4}]]];
nPrimes=Length[DeleteDuplicates[Sort/@DeleteDuplicates/@reps[[1;;nPrimes+1,{1,3,4}]]]]-1;

(* nPrimes=If[rep=!={0,0,0,0},Quotient[nPrimes,3Length[aux]-3],0]; *)

If[Length[aux]>1,
(*2*)
If[rep[[3]]==rep[[4]],subscript="v"];
If[rep[[1]]==rep[[4]],subscript="c"];
If[rep[[1]]==rep[[3]],subscript="s"];

(*3*)
If[rep[[1]]>rep[[4]]>rep[[3]],subscript="vs"];
If[rep[[1]]>rep[[3]]>rep[[4]],subscript="vc"];
If[rep[[4]]>rep[[1]]>rep[[3]],subscript="sv"];
If[rep[[4]]>rep[[3]]>rep[[1]],subscript="sc"];
If[rep[[3]]>rep[[1]]>rep[[4]],subscript="cv"];
If[rep[[3]]>rep[[4]]>rep[[1]],subscript="cs"];
];

printForm=ToString[dim]<>StringJoin[ConstantArray["'",nPrimes]];
If[subscript=!="",printForm=Subscript[printForm,subscript]];
printForm=Style[printForm,Bold];
If[barQ,printForm=OverBar[printForm]];
result={printForm,{dim,barQ,{nPrimes,subscript}}};

];



If[!OptionValue[ReturnAll],result=result[[1]]];
Return[result];
]


(* ::Input::Initialization:: *)
GroupsWithRankN2[n_]:=Module[{res},
res={};
If[n>0,AppendTo[res,{"A",n}]];
If[n>2,AppendTo[res,{"D",n}]];
If[n>1,AppendTo[res,{"B",n}]];
If[n>1,AppendTo[res,{"C",n}]];

If[n==2,AppendTo[res,{"G",2}]];
If[n==4,AppendTo[res,{"F",4}]];
If[n==6,AppendTo[res,{"E",6}]];
If[n==7,AppendTo[res,{"E",7}]];
If[n==8,AppendTo[res,{"E",8}]];

Return[res];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

CMtoFamilyAndSeries[cm_]:=Module[{aux,result},
If[cm==={},Return["U1"]];
aux=GroupsWithRankN2[Length[cm]];
result=aux[[Position[CartanMatrix@@@aux,cm][[1,1]]]];
Return[result];
]

