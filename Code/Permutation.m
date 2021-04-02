(* ::Package:: *)

(* ::Input::Initialization:: *)
(* product in group algebra *)
pp2[a_,b_]:=Module[{}, 
Switch[Head[a],
Plus,pp2[#,b]&/@a,
Times,Sum[MapAt[pp2[#,b]&,a,i],{i,Length[a]}],
Cycles,Switch[Head[b],
Plus,pp2[a,#]&/@b,
Times,Sum[MapAt[pp2[a,#]&,b,i],{i,Length[b]}],
Cycles,PermutationProduct[b,a],
_,0
],
_,0
]
](* 2-element *)
pp[permlist_]:=If[Length[permlist]>1,pp2[First[permlist],pp[Rest[permlist]]],First[permlist]]


(* ::Input::Initialization:: *)
(* generate index replacement rule for given permutation *)
IndexPermute[cyc_Cycles,indset_]:=AssociationThread[indset->Permute[indset,cyc]]
IndexInvPermute[cyc_Cycles,indset_]:=AssociationThread[Permute[indset,cyc]->indset]


(* ::Input::Initialization:: *)
(*********************** irreducible ideal of group algebra *******************)

(*Given a tableau Generate List vertical cycle groups and horizontal cycle groups*)
GenerateCycleGauge[Tableau_]:=Module[{len=Length[Tableau],len1=Length[Tableau[[1]]],tTabvertical},tTabvertical=Cases[#,_Integer]&/@Transpose[Join[#,Table["x",{i,1,len1-Length[#]}]]&/@Tableau];{Tableau,tTabvertical}]

(*Generate the list of permutations from the given array*)
GenerateCyclesFromList[l_]:=#/.Cycles[x__]:>Cycles[Map[l[[#1]]&,x,{2}]]&/@(GroupElements[SymmetricGroup[Length[l]]])

(*function to calculate the parity of the Cycle*)
permutationSignature[perm_?PermutationCyclesQ]:=Apply[Times,(-1)^(Length/@First[perm]-1)];

(*Generate irreducible Young Symmetrizer with given Tableau*)
GenerateYoungSymmetrizer[Tableau_]:=Module[{cyclegroups=GenerateCycleGauge[Tableau],vgroup,hgroup,h,v},
hgroup=GenerateCyclesFromList/@cyclegroups[[1]];
vgroup=GenerateCyclesFromList/@cyclegroups[[2]];
vgroup=vgroup*Map[permutationSignature[#]&,(vgroup),{2}];
v=pp[Total/@vgroup];
h =pp[Total/@hgroup];
pp[{h,v}]
]
(*generate a table with different Cycles and corresponding coefficients for a given ordinary polynomial with cycles*)
ColistPP[p_]:=Module[{cycleslist,Colist},
cycleslist=Cases[Variables[p],Cycles[_]];
If[Length[cycleslist]==0,Return[Null]];
Colist =(CoefficientList[p,#]&/@cycleslist)[[1;;-1,2]];
Join[Transpose[{cycleslist}],Transpose[{Colist}],2]
]
(*Functions related to find P,Q of a permutation in a Young Tableaux*)
FindPQ[plist_,qlist_,perm_]:=Module[{ptemp,qtemp,npl=Length[plist],nql=Length[qlist]},Do[If[PermutationProduct[qlist[[j]],plist[[i]]]==perm,ptemp=plist[[i]];qtemp=qlist[[j]];Break[]],{i,1,npl},{j,1,nql}];{ptemp,qtemp}];
R[ST_,x_,y_]:= FindPermutation[Flatten[ST[[x]]],Flatten[ST[[y]]]];
DistPP[x_]:=If[Length[x]>1,(PermutationProduct@@Reverse[{#}]&)@@@Distribute[x,List],x];
GetPQFromPerm[t_,perm_]:=Module[{cg,pl,ql,pql},cg=GenerateCycleGauge[t];
pl=DeleteDuplicates[Flatten[DistPP/@Subsets[GenerateCyclesFromList/@cg[[1]]]]];
ql=DeleteDuplicates[Flatten[DistPP/@Subsets[GenerateCyclesFromList/@cg[[2]]]]];
FindPQ[pl,ql,perm]
]
NormalizeQ[t1_,t2_]:=Module[{nrow=Length[t2],plist,Q=False},
Do[plist=(Position[t1,#]&/@t2[[i]])[[1;;-1,1,2]];If[(SortBy[Tally[plist],Last])[[-1,2]]>1,Q=True;Break[]],{i,1,nrow}];Q
]


(* ::Input::Initialization:: *)
(* basis Subscript[b, \[Mu]\[Nu]] for Sn irrep space *)
Generateb[part_]:=Module[{Pnumu,Qnumu,Rnumu,ymu,e,b,ndim=SnIrrepDim[part],n=Total[part],ng=Total[part]!,ST,YSlist,PQtemp,e1coeff,gP,gW},
ST=GenerateStandardTableaux[part];
YSlist=(GenerateYoungSymmetrizer/@ST);
Do[Rnumu[i,j]=R[ST,i,j];If[NormalizeQ[ST[[i]],ST[[j]]],Pnumu[i,j]=0;Qnumu[i,j]=0,PQtemp=GetPQFromPerm[ST[[j]],R[ST,i,j]];Pnumu[i,j]=PQtemp[[1]];Qnumu[i,j]=PQtemp[[2]];],{i,1,ndim},{j,1,ndim}];
ymu[ndim]=Cycles[{}];
Do[ymu[ndim-k]=(Cycles[{}]-Sum[pp[{Pnumu[ndim-k,l],ymu[l]}],{l,ndim-k+1,ndim}]),{k,1,ndim-1}];
Do[e[mu]=ndim/ng (pp[{(GenerateYoungSymmetrizer[ST[[mu]]]),ymu[mu]}]),{mu,1,ndim}];
Switch[permutationBasis,
"left",Return[pp[{R[ST,#,1],e[1]}]&/@Range[1,ndim]],
"right",Return[pp[{R[ST,1,#],e[#]}]&/@Range[1,ndim]]]
]
YO[yng_,pos_:1,otherbasis_:1]:=Generateb[yng][[otherbasis]]/.Cycles[x_]:>Cycles[x+pos-1]


(* ::Input::Initialization:: *)
breakCycle[{first_,rest___}]:={first,#}&/@{rest}
toTranspositions[Cycles[{}]]:=Cycles[{}]
toTranspositions[perm_?PermutationCyclesQ]:=Cycles/@List/@Flatten[breakCycle/@First[perm],1]

Clear[PermRepFromGenerator];
PermRepFromGenerator[gen_,Cycles[{}]]:=gen[[1]].gen[[1]]
PermRepFromGenerator[gen_,perm:Cycles[{{_,_}}]]:=Module[{P1=gen[[1]],W=gen[[2]],x,y},
{x,y}=Sort[{perm[[1,1,1]],perm[[1,1,2]]}];
If[y-x== 1,Nest[W.#.Inverse[W]&,P1,x-1],
Fold[(#2.#1.#2)&,PermRepFromGenerator[gen,Cycles[{{x,x+1}}]],Table[PermRepFromGenerator[gen,Cycles[{{i,i+1}}]],{i,x+1,y-1}]]
]
]
PermRepFromGenerator[gen_,perm_?PermutationCyclesQ]:=Dot@@(PermRepFromGenerator[gen]/@Reverse@toTranspositions[perm])
PermRepFromGenerator[gen_,sym_]:=Module[{},
sym/.perm_Cycles:>PermRepFromGenerator[gen,perm]
]
PermRepFromGenerator[gen_]:=PermRepFromGenerator[gen,#]&


(* ::Input::Initialization:: *)
(************* inner product (needs data folder SnMat) *******************)

ReadMatrices[matmap_,n_,dir_]:=Module[{nintpart=Length[IntegerPartitions[n]],ge,mat},ge=ToExpression/@Import[dir<>"/s"<>ToString[n]<>"/s"<>ToString[n],"List"];Do[mat=ToExpression/@Import[dir<>"/s"<>ToString[n]<>"/s"<>ToString[n]<>"_"<>ToString[i]<>".dat","List"];MapThread[Set,{matmap[i][#]&/@ge,mat}],{i,1,nintpart}]
]

PR[matmap_,ge_,\[Sigma]_,k_,l_,snreplist_,symbollist_,indiceslist_]:=Module[{nG=Length[ge],n\[Sigma],nlist},nlist=Length[(matmap[#][Cycles[{}]])[[1]]]&/@snreplist;
n\[Sigma]=Length[(matmap[\[Sigma]][Cycles[{}]])[[1]]];
n\[Sigma]/nG Sum[
Inverse[(matmap[\[Sigma]][ge[[g]]])][[k,l]] Times@@(Sum[#2[i]((matmap[#1][ge[[g]]])[[i,#3]]),{i,1,#4}]&@@@Transpose[{snreplist,symbollist,indiceslist,nlist}])
,{g,1,nG}]
]

GetCGCM[replist_,matmap_:0]:=Module[{n=Total@First@replist,mat,result={},intpart,listreppos,listrep,listirrepdim,multiplicity,listdim,symbollist,indiceslist,listbasis,irrepbasis,multicount,rank,cglist,cglistn,ranktemp},
If[matmap===0,ReadMatrices[mat,n,NotebookDirectory[]<>"SnMat"],mat=matmap];
intpart=IntegerPartitions[n]; (* list of Sn irrep *)
listreppos=Position[intpart,#][[1,1]]&/@replist;
listdim = SnIrrepDim/@replist;
listirrepdim= SnIrrepDim/@intpart;
listrep=DecomposeSnProduct[replist]; (* {n_1,n_2,...}, n_i being multiplicity of irrep intpart\[LeftDoubleBracket]i\[RightDoubleBracket] *)
symbollist=u/@Range[1,Length[replist]];
indiceslist=Distribute[Range[1,#]&/@listdim,List];
listbasis=Times@@Flatten[MapThread[Map,{symbollist,#}]]&/@(Partition[#,1]&/@indiceslist);

Do[multiplicity=listrep[[i]];
If[multiplicity== 0,Continue[]];
multicount=0;
rank=0;
cglistn={};
Do[irrepbasis=PR[mat,GroupElements[SymmetricGroup[n]],i,1,#,listreppos,symbollist,j]&/@Range[1,listirrepdim[[i]]]; (* key step, result in terms of abstract basis u[x][y] *)
If[!(IntegerQ[irrepbasis[[1]]]),
cglist=Table[Coefficient[irrepbasis[[mb]],#]&/@listbasis,{mb,1,listirrepdim[[i]]}]; (* take away u-basis *)
ranktemp=MatrixRank[Join[cglistn,cglist]];
If[ranktemp>rank,cglistn=Join[cglistn,cglist];multicount++;rank=ranktemp]; (* find new independent rep space *)
If[multicount==multiplicity,AppendTo[result,intpart[[i]]->Partition[cglistn,listirrepdim[[i]]]];Break[]] (* find enough spaces *)
],
{j,indiceslist}],
{i,1,Length[listirrepdim]}
];
Map[Fold[Partition,#,Reverse[Rest[listdim]]]&,result,{4}]
]


(* ::Input::Initialization:: *)
(********************** Young tableau related *******************)
TransposeYng[yng_]:=Length/@TransposeTableaux[Range/@yng]

Dynk2Yng[rep_]:=Reverse@Accumulate@Reverse@Abs[rep]
Yng2Dynk[group_,yng_]:=-Differences@PadRight[yng,Length[group]+1]


(* ::Input::Initialization:: *)
(* Modification of the GroupMath MyRepProduct *)
MyRepProduct[cm_,repsList_,select_:Identity]:=MyRepProduct[cm,repsList,select]=Module[{n,orderedList,result},
If[cm==U1,Return[{{Plus@@repsList,1}}]];If[Length[repsList]==1,Return[{{repsList[[1]],1}}]];orderedList=Sort[repsList,DimR[cm,#1]<DimR[cm,#2]&];n=Length[orderedList];result=ReduceRepProductBase2[cm,orderedList[[n-1]],orderedList[[n]]];Do[result=ReduceRepProductBase1[cm,orderedList[[n-i]],select@result];,{i,2,n-1}];Return[result]
]

FindIrrepCombination[group_,IPlist_,rep_]:=FindIrrepCombination[group,IPlist,rep]=
(*IPlist is a list of {__,__}, where the first slot is the Dykin coefficient of the corresponding representation, the second slot is the number of this representation*)
Module[{nbox,yng=Dynk2Yng[rep],select,PlethysmsNlist,IrrepListAmongNIP,IrrepListFromReduce,SingletPositionList,SUNirrep,SNirrep,NumSUN},
nbox=Total@Flatten[Dynk2Yng/@Join@@ConstantArray@@@IPlist];
select=Select[And@@Thread[Dynk2Yng[#[[1]]]<=yng+(nbox-Total@yng)/(1+Length[group])]&];
PlethysmsNlist=select/@(PlethysmsN[group,##]&@@@IPlist);
IrrepListAmongNIP=Distribute[DeleteDuplicates/@PlethysmsNlist[[1;;-1,1;;-1,1]],List];
IrrepListFromReduce=MyRepProduct[group,#,select]&/@IrrepListAmongNIP;
SingletPositionList=Position[IrrepListFromReduce,{rep,_}][[1;;-1,1]];
NumSUN=Cases[#,{rep,temp_}:>temp]&/@(IrrepListFromReduce[[#]]&/@SingletPositionList);
SUNirrep=IrrepListAmongNIP[[#]]&/@SingletPositionList;
SNirrep=Table[Cases[PlethysmsNlist[[i]],{IrrepListAmongNIP[[#]][[i]],x_,y_}:>{x,y}],{i,1,Length[IPlist]}]&/@SingletPositionList;
{SUNirrep,SNirrep,Flatten[NumSUN]}
]


(* ::Subsubsection:: *)
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
