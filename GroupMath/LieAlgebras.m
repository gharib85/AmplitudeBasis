(* ::Package:: *)

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

CMtoName[group_]:=If[IsSimpleGroupQ[group],CMtoName\[UnderBracket]Aux[group],CMtoName\[UnderBracket]Aux/@group]
CMtoName\[UnderBracket]Aux[cm_]:=Module[{aux,result},

result="Unknown group";
Which[cm=={},result="U1",
cm==G2,result="G2",
cm==F4,result="F4",
cm==E6,result="E6",
cm==E7,result="E7",
cm==E8,result="E8",
True,
aux=CMtoFamilyAndSeries[cm];
If[aux[[1]]=="A",result="SU"<>ToString[aux[[2]]+1]];
If[aux[[1]]=="B",result="SO"<>ToString[2aux[[2]]+1]];
If[aux[[1]]=="C",result="SP"<>ToString[2aux[[2]]]];
If[aux[[1]]=="D",result="SO"<>ToString[2aux[[2]]]];
];

Return[result];
]

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

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This commented version of the WeylOrbit function is equivalent to the one being used, and it is more human readable (but slower) *)
(*
WeylOrbit[cm_,weight_]:=Module[{wL,counter,n,result,aux},
n=Length[cm];
counter=0;
wL[counter]={weight};
result={weight};

While[Length[wL[counter]]\[NotEqual]0,

counter++;
wL[counter]={};

Do[

If[wL[counter-1][[j,i]]>0 ,
aux=ReflectWeight[cm,wL[counter-1][[j]],i][[i+1;;n]];
If[aux\[Equal]Abs[aux],
wL[counter]=Append[wL[counter],ReflectWeight[cm,wL[counter-1][[j]],i]];
]];
,{j,Length[wL[counter-1]]},{i,n}];
result=Join[result,wL[counter]];
];

Return[result];
]
*)

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

(*  Wrapper function of RepMinimalMatrices\[UnderBracket]BaseMethod: if the given group is not simple*)
RepMinimalMatrices[group_,rep_]:=Module[{repMats,identities,aux,aux2,dimsG,dimsGAcc,res},

If[IsSimpleGroupQ[group],
Return[RepMinimalMatrices\[UnderBracket]BaseMethod[group,rep]],

(* Else ... group is not just a single factor group *)
repMats=Table[If[group[[i]]=={},SparseArray[{{rep[[i]]}}],Flatten[RepMinimalMatrices\[UnderBracket]BaseMethod[group[[i]],rep[[i]]],1]],{i,Length[group]}];
If[Length[repMats]==1,Return[If[group==={U1},{repMats},{InverseFlatten[repMats[[1]],{Length[group]/3,3}]}]]];

identities=Table[{IdentityMatrix[Length[repMats[[i,1]]]]},{i,Length[group]}];

aux=Table[identities,{i,Length[group]}];
Do[
aux[[i,i]]=repMats[[i]];
,{i,Length[group]}];

res={};
Do[
AppendTo[res,KroneckerProduct@@Table[If[k==i,aux[[i,k,j]],aux[[i,k,1]]],{k,Length[group]}]];
,{i,Length[group]},{j,Length[repMats[[i]]]}];

(* [START] Correctly slice the list of matrices into sublist *)
dimsG=Max[3Length[#],1]&/@group;
dimsGAcc=Accumulate[dimsG]-dimsG;
aux=res;
res={};
Do[
aux2=aux[[dimsGAcc[[i]]+Range[dimsG[[i]]]]];
aux2=If[group[[i]]===U1,{aux2},InverseFlatten[aux2,{dimsG[[i]]/3,3}]];
AppendTo[res,aux2];
,{i,Length[group]}];
(* [END] Correctly slice the list of matrices into sublist *)

Return[res];
];
]

(* Calculates the generators of a irrep based on the Chevalley-Serre relations *)
RepMinimalMatrices\[UnderBracket]BaseMethod[cm_,maxW_]:=RepMinimalMatrices\[UnderBracket]BaseMethod[cm,maxW]=Module[{aux1,aux2,aux3,aux4,aux6,aux7,aux8,n,listw,up,down,dim,dim1,dim2,dim3,col,matrixT,matrix,index,posBegin,posEnd,begin,end,b1,e1,b2,e2,matrixE,matrixF,matrixH},

If[cm===U1,Return[{{SparseArray[{{maxW}},{1,1}]}}]];

(* Reorder the weights of conjugate representations so that RepMatrices[group,ConjugateIrrep[group,w]]=-Conjugate[RepMatrices[group,w]] and Invariants[group,{w,ConjugateIrrep[group,w]},{False,False}]=a[1]b[1]+...+a[n]b[n] *)
If[OrderedQ[{maxW,ConjugateIrrep[cm,maxW]}]&& ConjugateIrrep[cm,maxW]=!=maxW,Return[-RepMinimalMatrices[cm,ConjugateIrrep[cm,maxW]][[All,{2,1,3}]]]]; 

n=Length[cm];
listw=Weights[cm,maxW];

dim[x__]:=0;
up[x__]=Table[{},{i,n}];
down[x__]=Table[{},{i,n}];
Do[
dim[listw[[i,1]]]=listw[[i,2]];
,{i,Length[listw]}];
up[listw[[1,1]]]=Table[{{0}},{i,n}];

Do[
matrixT={};
Do[
col={};
Do[
dim1=dim[listw[[element,1]]+cm[[i]]];
dim2=dim[listw[[element,1]]+cm[[i]]+cm[[j]]];
dim3=dim[listw[[element,1]]+cm[[j]]];

If[dim1!=0&&dim3!=0,
If[dim2!=0,
aux1=up[listw[[element,1]]+cm[[i]]][[j]];
aux2=down[listw[[element,1]]+cm[[i]]+cm[[j]]][[i]];

If[i!=j,col=Join[col,aux1.aux2], col=Join[col,aux1.aux2+(listw[[element,1,i]] +cm[[i,i]])IdentityMatrix[dim1]]];
,
If[i!=j,col=Join[col,NullMatrix[dim1,dim3]], col=Join[col,(listw[[element,1,i]] +cm[[i,i]])IdentityMatrix[dim1]]];
];

];

,{i,n}];

If[col!={},
matrixT=Join[matrixT,Transpose[col]];
];

,{j,n}];

(* Separate the two matrices in the product (w+\[Alpha]i)i * wj *)
matrix=Transpose[matrixT];

aux1=Sum[dim[listw[[element,1]]+cm[[i]]],{i,n}];
aux2=dim[listw[[element,1]]];

aux3=PadRight[CholeskyTypeDecomposition[matrix],{aux1,aux2}];
aux4=Transpose[aux3];
If[aux3.aux4!= matrix,Print["Error!", aux3//MatrixForm,aux4//MatrixForm,matrix//MatrixForm];];


(* Obtain the blocks in  (w+\[Alpha]i)i and wj. Use it to feed the recursive algorith so that we can calculate the next w's *)

aux1={{0,0}}; (* format (+-): (valid cm raise index i - 1, start position of weight w+cm[[i-1]]-1) *)
Do[
If[dim[listw[[element,1]]+cm[[i]]]!=0,
aux1=Append[aux1,{i,aux1[[-1,2]]+dim[listw[[element,1]]+cm[[i]]]}];];
,{i,n}];

Do[
index=aux1[[i+1,1]];
posBegin=aux1[[i,2]]+1;
posEnd=aux1[[i+1,2]];


aux2=down[listw[[element,1]]+cm[[index]]];
aux2[[index]]=aux3[[posBegin;;posEnd]];
down[listw[[element,1]]+cm[[index]]]=aux2;

aux2=up[listw[[element,1]]];
aux2[[index]]=Transpose[Transpose[aux4][[posBegin;;posEnd]]];
up[listw[[element,1]]]=aux2;
,{i,Length[aux1]-1}];

,{element,2,Length[listw]}];

(* Put the collected pieces together and build the 3n matrices: hi,ei,fi *)

begin[listw[[1,1]]]=1;
end[listw[[1,1]]]=listw[[1,2]];

Do[
begin[listw[[element,1]]]=begin[listw[[element-1,1]]]+listw[[element-1,2]];
end[listw[[element,1]]]=end[listw[[element-1,1]]]+listw[[element,2]];
,{element,2,Length[listw]}];

aux1=Table[{1+Sum[listw[[j,2]],{j,i-1}],Sum[listw[[j,2]],{j,i}]},{i,Length[listw]}];
aux2=Sum[listw[[i,2]],{i,Length[listw]}];
aux3=SparseArray[PadRight[{{}},{aux2,aux2}]];

Do[
aux6=aux3; (* e[i] *)
aux7=aux3; (* f[i] *)
aux8=aux3; (* h[i] *)
Do[ 

If[dim[listw[[element,1]]+cm[[i]]]!=0,
b1=begin[listw[[element,1]]+cm[[i]]];
e1=end[listw[[element,1]]+cm[[i]]];
b2=begin[listw[[element,1]]];
e2=end[listw[[element,1]]];
aux6[[b1;;e1,b2;;e2]]=Transpose[up[listw[[element,1]]][[i]]];
];

If[dim[listw[[element,1]]-cm[[i]]]!=0,
b1=begin[listw[[element,1]]-cm[[i]]];
e1=end[listw[[element,1]]-cm[[i]]];
b2=begin[listw[[element,1]]];
e2=end[listw[[element,1]]];
aux7[[b1;;e1,b2;;e2]]=Transpose[down[listw[[element,1]]][[i]]];
];

b1=begin[listw[[element,1]]];
e1=end[listw[[element,1]]];
aux8[[b1;;e1,b1;;e1]]=listw[[element,1,i]] IdentityMatrix[listw[[element,2]]];

,{element,Length[listw]}];
matrixE[i]=SparseArray[aux6];
matrixF[i]=SparseArray[aux7];
matrixH[i]=SparseArray[aux8];

,{i,n}];

aux1=Table[{matrixE[i],matrixF[i],matrixH[i]},{i,n}];

Return[aux1]; (*  result is a list with entries {e[i],f[i],h[i]} *)
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Calculates the Casimir invariant of an irrep *)
Casimir[input__]:=Casimir[input]=Switch[Depth[{input}],x_/;(x==3||x==4),CasimirBaseMethod[input],5,CasimirBaseMethod@@@Transpose[{input}]];

(* Uses formula XI.23 of "Semi-Simple Lie Algebras and Their Representations", page 89 *)

CasimirBaseMethod[cm_,w_]:=Module[{n,cmInv,matD,cmID,proots,deltaTimes2,result},
If[cm==={}||cm===ConstantArray[{},Length[cm]],Return[w^2]]; (* U1 group or multiple U1 groups *)

n=Length[cm];
proots=PositiveRoots[cm];

cmInv=Inverse[cm];
matD=MatrixD[cm];
cmID=cmInv.matD/Max[matD]; (* Note: Max[matD] is to cut a factor of 2 in the SP class of groups. As it is, it is assumed that Max[<\[Alpha],\[Alpha]>]=1 (considering all positive roots). This happens naturally for all groups, except the SP class *)
deltaTimes2=Sum[proots[[i]],{i,Length[proots]}];
result=SimpleProduct[w,w+deltaTimes2,cmID];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

DynkinIndex[cm_,rep_]:=DynkinIndex[cm,rep]=Simplify[Casimir[cm,rep] DimR[cm,rep]/DimR[cm,Adjoint[cm]]]

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

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)


(* Auxiliar method (used for building invariants) *)
BlockW[w1_,w2_,listW_,repMat_]:=Module[{dim,b,e,aux1},

dim[0]=0;
Do[dim[i]=dim[i-1]+listW[[i,2]],{i,Length[listW]}];

Do[b[listW[[i,1]]]=dim[i-1]+1;
e[listW[[i,1]]]=dim[i];
,{i,Length[listW]}];

aux1=repMat[[b[w1];;e[w1],b[w2];;e[w2]]];

Return[aux1];

]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* This method returns the complete set of matrices that make up a representation, with the correct casimir and trace normalizations *)
RepMatrices[group_,rep_]:=Module[{repMats,identities,aux,aux2,dimsG,dimsGAcc,res},
If[IsSimpleGroupQ[group],
Return[RepMatricesBaseMethod[group,rep]],

(* Else ... group is not just a single factor group *)
repMats=Table[If[group[[i]]=={},{SparseArray[{{rep[[i]]}}]},RepMatricesBaseMethod[group[[i]],rep[[i]]]],{i,Length[group]}];
If[Length[repMats]==1,Return[repMats[[1]]]];

identities=Table[{SparseArray[IdentityMatrix[Length[repMats[[i,1]]]]]},{i,Length[group]}];

aux=Table[identities,{i,Length[group]}];
Do[
aux[[i,i]]=repMats[[i]];
,{i,Length[group]}];

res={};
Do[
AppendTo[res,KroneckerProduct@@Table[If[k==i,aux[[i,k,j]],aux[[i,k,1]]],{k,Length[group]}]];
,{i,Length[group]},{j,Length[repMats[[i]]]}];

Return[res];
];
]

RepMatricesBaseMethod[cm_,maxW_]:=RepMatricesBaseMethod[cm,maxW]=Module[{listE,listF,listH,listTotal,n,pRoots,sR,dimG,dimR,rep,matrixCholesky,aux,j},
n=Length[cm];
pRoots=PositiveRoots[cm];
rep=RepMinimalMatrices[cm,maxW];
listE=Table[SparseArray[rep[[i,1]]],{i,n}];
listF=Table[SparseArray[rep[[i,2]]],{i,n}];
listH=Table[SparseArray[rep[[i,3]]],{i,n}];

dimG=2Length[pRoots]+Length[cm];
dimR=DimR[cm,maxW];
sR=Casimir[cm,maxW] dimR/dimG;

If[dimR==1, (*trivial rep, therefore all matrices are null*)
listTotal=Table[listE[[1]],{i,dimG}];
Goto[end];
];

(* If it's not the trivial rep, generate the matrices of the remaining algebra elements. The positive roots of the algebra serve as a guide in this process of doing comutators  *)
Do[
j=1;While[(aux=Position[pRoots[[1;;i]],pRoots[[i]]-pRoots[[j]]])=={},j++];

listE=Append[listE,listE[[aux[[1,1]]]].listE[[j]]-listE[[j]].listE[[aux[[1,1]]]]];
listF=Append[listF,listF[[aux[[1,1]]]].listF[[j]]-listF[[j]].listF[[aux[[1,1]]]]];

,{i,n+1,Length[pRoots]}];


Do[
(* Change from the operadores T+, T- to Tx,Ty *)
aux=listE[[i]];
listE[[i]]=listE[[i]]+ listF[[i]];
listF[[i]]=aux-listF[[i]];

(* Control the normalization of the Tx,Ty matrices with the trace condition *)
 listE[[i]]=SparseArray[Simplify[Sqrt[sR]/Sqrt[ Tr[listE[[i]].listE[[i]]]]]listE[[i]]]; 
listF[[i]]=SparseArray[Simplify[Sqrt[sR]/Sqrt[ Tr[listF[[i]].listF[[i]]]]]listF[[i]]];
,{i,Length[listE]}];

matrixCholesky=Inverse[cm].MatrixD[cm]; (* See the casimir expression in a book on lie algebras *)
aux=Simplify[CholeskyDecomposition[matrixCholesky]];
listH=Table[SparseArray[Sum[aux[[i,j]]listH[[j]],{j,n}]],{i,n}];

(* Up to multiplicative factors, Tz are now correct. We fix again the normalization with the trace condition *)
listH=Table[SparseArray[Simplify[Sqrt[sR]/Sqrt[ Tr[listH[[i]].listH[[i]]]]]listH[[i]]],{i,n}];

listTotal=Join[listE,listF,listH];

(* Make sure the final matrices are simplified *)
listTotal=Table[SparseArray[Simplify[listTotal[[i]]//ArrayRules],{dimR,dimR}],{i,Length[listTotal]}];

Label[end];

Return[listTotal];
];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Computes the list of adjoint matrices given justa a group cm (representation used is {1,0,...}) . It uses the antisymmetry of the structure constants *)
GaugeRep[cm_]:=Module[{mats,rep,res,n, factor},

If[!IsSimpleGroupQ[cm],Return[SimplifySA/@BlockDiagonalNTensor[GaugeRep/@cm]]];

If[cm==={},Return[SparseArray[{{{0}}}]]]; (* U1 case *)

rep=UnitVector[Length[cm],1];
(* For the E7, E8 groups these representations are better (ie smaller) *)
If[cm==E7,rep={0,0,0,0,0,1,0}];
If[cm==E8,rep={0,0,0,0,0,0,1,0}];
mats=RepMatrices[cm,rep];

n=Length[mats];
factor=Simplify[Length[mats]/(Length[mats[[1]]] Casimir[cm,rep])];

(*2 (from commutator) *)
res= factor Table[If[i>k>j,Tr[mats[[i]].mats[[j]].mats[[k]]],0],{i,n} ,{k,n},{j,n} ];
res=SimplifySA/@(res-Conjugate[res]);
res=Transpose[res,{1,2,3}]-Transpose[res,{1,3,2}]-Transpose[res,{2,1,3}]+Transpose[res,{2,3,1}]+Transpose[res,{3,1,2}]-Transpose[res,{3,2,1}];
res=SimplifySA/@  res;

Return[res];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* The invariants are symmetrized with SnIrrepGenerators. To be precise, invariants/.{a\[Rule]b,b\[Rule]a}=SnM1.invariants and invariants/.{a\[Rule]b,b\[Rule]c,c\[Rule]d,d\[Rule]e,...,X\[Rule]a}=SnM2.invariants where X is some letter (depends on the number of repeated representations n) and {SnM1,SnM2} are the matrices given by SnIrrepGenerators. This is assuming just a single representation repeated n times. For more complicated cases the generalization is trivial. In terms of the invariants in tensor form, Transpose[invariants,{1,3,2,4,5,6,...}]=SnM1.invariants and Transpose[invariants,{1,3,4,5,6,...,2}]=SnM2.invariants  *)
Options[SymmetrizeInvariants]={DistinguishFields->False,OrthogonalizeGenerators->True};

SymmetrizeInvariants[liegroup_,representations_,invariantsTensors_,cjs_,OptionsPattern[]]:=Module[{representationsWithConj,symmetries,fakeConjugationCharges,repsTemp,flattenedInvariants,allColumns,stop,count,maxRank,columnsToTrack,aux,invRef,groupOfIndices,permuteInvs12,permuteInvs1\[UnderBracket]n,refP12,refP1\[UnderBracket]n,ids,aux0,aux1,aux2,aux3,aux4,aux5,newStates,result,distinguishReps},

(* If there are no invariants, stop here *)
If[invariantsTensors==={},$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries={};Return[{}]];

(* Need to take care of conjugations. In particular, conjugated fields are always considered different from the non-conjuated ones, so there is no symmetrization between the two sets of fields. *)
(* [TODO?] A possible exception to this are representations R which are complex since, in the corrently used basis, R^* is exactly equal to the conjugated representation R'=ConjugateIrrep[group,R]. *)

(* PermutationSymmetryOfInvariants now has the option DistinguishFields, so the old method of adding fake U1's to distinguish conjugated and non-conjugated fields does not need to be performed by hand *)
distinguishReps=If[OptionValue[DistinguishFields]===False,ConstantArray[0, Length[representations]],OptionValue[DistinguishFields]];

(* Assuming that OptionValue[DistinguishFields] is a list of integers ... we can further differentiate the fields with the conjugations in the following way *)
(* Update: no; do not make a further differentiation. As such, now the distinguishReps used to call PermutationSymmetryOfInvariants is exactly the same given as input to Invariants *)
(* distinguishReps=2distinguishReps+(cjs/.{False\[Rule]0,True\[Rule]1}); *)


representationsWithConj=Table[If[cjs[[i]],representations[[i]],ConjugateIrrep[liegroup,representations[[i]]]],{i,Length[representations]}];

symmetries=PermutationSymmetryOfInvariants[liegroup,representationsWithConj,DistinguishFields->distinguishReps];
(* To improve consistency across Mathematica versions: *)

symmetries[[2]]=Sort[symmetries[[2]],PadRight[Flatten[#1[[1]]],Max[Length[Flatten[#1[[1]]]],Length[Flatten[#2[[1]]]]]]>PadRight[Flatten[#2[[1]]],Max[Length[Flatten[#1[[1]]]],Length[Flatten[#2[[1]]]]]]&];
(* $GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries is a global variable which will save the permutation symmetry of the last Invariants calculation *)
$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries=symmetries;

(* If there are no repeated representations, nothing else needs to be done *)
If[Length[Tally[MapThread[List,{representationsWithConj,distinguishReps}]]]===Length[representationsWithConj],Return[invariantsTensors]];

(* [START]Don't handle the complete invariants: just find a minimum set of entries which reveal the linear independence of the invariants *)
flattenedInvariants=Flatten/@invariantsTensors;
allColumns=DeleteDuplicates[ArrayRules[flattenedInvariants][[1;;-2,1,2]]];

count=0;
stop=False;
maxRank=0;
columnsToTrack={};

While[count<Length[allColumns]&&!stop,
count++;
aux=MatrixRank[flattenedInvariants[[All,allColumns[[Append[columnsToTrack,count]]]]]];
If[aux>maxRank,AppendTo[columnsToTrack,count];maxRank=aux];
stop=(aux==Length[invariantsTensors]);
];
columnsToTrack=allColumns[[columnsToTrack]];
invRef=PseudoInverse[flattenedInvariants[[All,columnsToTrack]]];
(* [END]Don't handle the complete invariants: just find a minimum set of entries which reveal the linear independence of the invariants *)

(* [START]Generate the Sn transformation matrices of the invariants under permutations of each set of equal representations *)
permuteInvs12={};
permuteInvs1\[UnderBracket]n={};
Do[
groupOfIndices=symmetries[[1,groupOfIndicesI]];
If[Length[groupOfIndices]>1,
aux=Range[Length[representations]];
aux[[groupOfIndices[[{1,2}]]]]=Reverse[aux[[groupOfIndices[[{1,2}]]]]];
AppendTo[permuteInvs12,(Flatten/@Transpose[invariantsTensors,Prepend[aux+1,1]])[[All,columnsToTrack]]];

aux=Range[Length[representations]];
aux[[groupOfIndices]]=aux[[RotateLeft[groupOfIndices]]];
AppendTo[permuteInvs1\[UnderBracket]n,(Flatten/@Transpose[invariantsTensors,Prepend[aux+1,1]])[[All,columnsToTrack]]];
];
,{groupOfIndicesI,Length[symmetries[[1]]]}];
refP12=Simplify[#.invRef]&/@permuteInvs12;
refP1\[UnderBracket]n=Simplify[#.invRef]&/@permuteInvs1\[UnderBracket]n;
(* [END]Generate the Sn transformation matrices of the invariants under permutations of each set of equal representations *)

(* The standardized Sn irrep generators *)
newStates={};
Do[
aux0={};
Do[
If[Length[symmetries[[1,groupOfIndicesI]]]>1,
ids=IdentityMatrix[SnIrrepDim[#]]&/@SnIrrep[[1]];

aux=SnIrrepGenerators[SnIrrep[[1,groupOfIndicesI]],OrthogonalizeGenerators->OptionValue[OrthogonalizeGenerators]];
aux2=ids;
aux2[[groupOfIndicesI]]=aux[[1]];
aux2=If[Length[symmetries[[1]]]>1,KroneckerProduct@@aux2,aux2[[1]]];

aux3=ids;
aux3[[groupOfIndicesI]]=aux[[2]];
aux3=If[Length[symmetries[[1]]]>1,KroneckerProduct@@aux3,aux3[[1]]];

aux0=AppendTo[aux0,Simplify[{aux2,aux3}]];
];

,{groupOfIndicesI,Length[SnIrrep[[1]]]}];

If[OptionValue[OrthogonalizeGenerators],
aux4=Transpose/@MapThread[KroneckerProduct,{aux0[[All,1]],refP12}];
aux5=Transpose/@MapThread[KroneckerProduct,{aux0[[All,2]],refP1\[UnderBracket]n}];

aux4=Join[aux4,aux5];
aux4=Flatten[Simplify[(#-IdentityMatrix[Length[aux4[[1]]]])]&/@aux4,1];
aux4=Simplify[Orthogonalize[Flatten[InverseFlatten[#,{Length[aux0[[1,1]]],Length[refP12[[1]]]}]&/@NullSpace2[aux4,1],1],Simplify[Conjugate[#1]. #2]&]];

,

aux4=Transpose/@MapThread[KroneckerProduct,{Transpose[Inverse[#]]&/@aux0[[All,1]],refP12}];
aux5=Transpose/@MapThread[KroneckerProduct,{Transpose[Inverse[#]]&/@aux0[[All,2]],refP1\[UnderBracket]n}];

aux4=Join[aux4,aux5];
aux4=Flatten[Simplify[(#-IdentityMatrix[Length[aux4[[1]]]])]&/@aux4,1];
aux4=Simplify[Flatten[InverseFlatten[#,{Length[aux0[[1,1]]],Length[refP12[[1]]]}]&/@NullSpace2[aux4,1],1]];

];

newStates=Join[newStates,aux4];
,{SnIrrep,symmetries[[2]]}];
newStates=Simplify[Normalize/@newStates];
(* compute the invariants in the final form *)
result=SimplifySA[SparseArray[newStates].invariantsTensors];
Return[result];
]


NormalizeInvariants[liegroup_,representations_,invariantsTensors_]:=Module[{aux,result,startAndEnds},
If[Length[invariantsTensors]==0,Return[{}]];
aux=Simplify[Table[Total[invI invJ,{1,-1}],{invI,invariantsTensors},{invJ,invariantsTensors}]];
aux=SparseArray[Inverse[CholeskyTypeDecomposition[aux]]];
result=aux.invariantsTensors;
result=(Times@@(Times@@DimR[liegroup,#]&/@representations))^(1/4)result;
Return[result];
]

(* Unfortunately, this sign fixing cannot be done at the same time as NormalizeInvariants. So, the sequence is:
1. NormalizeInvariants; 2. SymmetrizeInvariants; 3. FixSignOfInvariants.
*)
FixSignOfInvariants[invariantsTensorsIn_]:=Module[{invariantsTensors,aux,startAndEnds,posRefElement,invs,refElement},
invariantsTensors=invariantsTensorsIn;
(* [Start] Ensure that for each permutation group irrep, the sign of the first entry of the first invariant must be positive *)
aux=Flatten[MapThread[ConstantArray[#1,#2]&,{Times@@@Map[SnIrrepDim,$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries[[2,All,1]],{2}],$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries[[2,All,2]]}]];
startAndEnds=StartsEnds[aux];
Do[
invs=invariantsTensors[[startAndEnds[[1,i]];;startAndEnds[[2,i]]]];
aux=ArrayRules[invs];
posRefElement=Position[aux[[All,2]],x_/;x!=0,{1}][[1,1]];
refElement=aux[[posRefElement,1]];
If[Sign[refElement]==-1,
invariantsTensors[[startAndEnds[[1,i]];;startAndEnds[[2,i]]]]=-invs;
];
,{i,Length[$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries[[2]]]}];
(* [End] Ensure that for each permutation group irrep, the sign of the first entry of the first invariant must be positive *)

Return[invariantsTensors];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Invariants3Mod and IrrepInProduct are auxiliar methods *)
Invariants3Mod[cm_,reps_,conjs_]:=Module[{},
If[(conjs[[1]]&&conjs[[2]]&&conjs[[3]])||((!conjs[[1]])&&(!conjs[[2]])&&(!conjs[[3]])),Return[InvariantsOld[cm,reps[[1]],reps[[2]],reps[[3]]]]];
If[(conjs[[1]]&&conjs[[2]]&&(!conjs[[3]]))||((!conjs[[1]])&&(!conjs[[2]])&&(conjs[[3]])),Return[InvariantsOld[cm,reps[[1]],reps[[2]],reps[[3]],True]]];

If[(conjs[[1]]&&(!conjs[[2]])&&conjs[[3]])||((!conjs[[1]])&&(conjs[[2]])&&(!conjs[[3]])),Return[InvariantsOld[cm,reps[[1]],reps[[3]],reps[[2]],True]/.{c->b,b->c}]];
If[((!conjs[[1]])&&conjs[[2]]&&conjs[[3]])||((conjs[[1]])&&(!conjs[[2]])&&(!conjs[[3]])),Return[InvariantsOld[cm,reps[[3]],reps[[2]],reps[[1]],True]/.{c->a,a->c}]];
]

Options[IrrepInProduct]={Conjugations->{}};
IrrepInProduct[cm_,reps_,OptionsPattern[]]:=Module[{aux,vector,conjs},

(* Option allows the user to conjugate the representations given as input. By default, no conjugation is done *)
conjs=If[OptionValue[Conjugations]==={},ConstantArray[False,Length[reps]],OptionValue[Conjugations]];
conjs[[3]]=!conjs[[3]];
aux=Invariants3Mod[cm,reps,conjs];
vector=DeleteDuplicates[Sort[Cases[aux,c[__],-1]]];
aux=CoefficientArrays[#,vector][[2]]&/@aux;

Return[aux];
]
(* "SnNonOrthogonal" is possible for the option NormalizeAndSymmetrize *)
$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries = Null;
Options[Invariants]={Conjugations->{},(* BasisRotation\[Rule]Null,*)TensorForm->False,DistinguishFields->False,NormalizeAndSymmetrize->True,FactorGroupExtraConjugation->{}};
Invariants[groupOriginal_,rOriginalIn_,OptionsPattern[]]:=Module[{distFieds,distFiedsOriginal,auxOrderingReps, orderingReps,orderingRepsInv,nSinglet,rOriginal,ruleToRepositionReps,result,variables,tensors,pU1s,pNonU1s,hyperchargesSum,group,r,cjs,cjsOriginal,rotationToTheSymbols,variablesToRotate,rotationRules,aux4,aux5,aux6,cjsFcts,cjsTable,orthogonalizeSnGenerators},

(* Option allows to conjugate the representations given as input. By default, no conjugation is done *)
cjs=If[OptionValue[Conjugations]==={},ConstantArray[False,Length[rOriginalIn]],OptionValue[Conjugations]];
distFieds=If[OptionValue[DistinguishFields]===False, Position[DeleteDuplicates[MapThread[List,{rOriginalIn,cjs}]],#][[1,1]]&/@MapThread[List,{rOriginalIn,cjs}],OptionValue[DistinguishFields]];

(* cjsTable contains the conjugation information for each field AND each gauge factor group. This feature is useful to deal with the Lorentz group *)
If[!IsSimpleGroupQ[groupOriginal],
cjsFcts=If[OptionValue[FactorGroupExtraConjugation]==={},ConstantArray[False,Length[groupOriginal]],OptionValue[FactorGroupExtraConjugation]],
cjsFcts=If[OptionValue[FactorGroupExtraConjugation]==={},False,OptionValue[FactorGroupExtraConjugation]];
];
If[!IsSimpleGroupQ[groupOriginal],
cjsTable=Table[i==j,{i,cjs},{j,cjsFcts}],
cjsTable=Flatten[Table[i==cjsFcts,{i,cjs}]];
];


(* [TAG-A] Make sure that providing a permutation of the input reps does not lead to a different result (ie, introduction of phases) appart from a trivial change of letter *)
(* Sorts according to {-<dimension of rep>, <Dynkin coefficients of rep>, <conjugated?>, <position of rep as given by the user>}, *)
If[IsSimpleGroupQ[groupOriginal],
auxOrderingReps=Table[{-DimR[groupOriginal,rOriginalIn[[i]]],rOriginalIn[[i]],cjs[[i]],i},{i,Length[rOriginalIn]}];,
auxOrderingReps=Table[{-Times@@DimR[groupOriginal,rOriginalIn[[i]]],rOriginalIn[[i]],i},{i,Length[rOriginalIn]}];
];

orderingReps=Ordering[auxOrderingReps];
orderingRepsInv=Table[Position[orderingReps,i][[1,1]],{i,Length[rOriginalIn]}];
ruleToRepositionReps=Table[ToExpression[FromCharacterCode[96+i]]->ToExpression[FromCharacterCode[96+orderingReps[[i]]]],{i,Length[rOriginalIn]}];
rOriginal=rOriginalIn[[orderingReps]];
cjsOriginal=cjs;
distFiedsOriginal=distFieds;
cjs=cjs[[orderingReps]];
distFieds=distFieds[[orderingReps]];
(* rOriginal=rOriginalIn; *)


(* Deal with U1's *)
If[groupOriginal===ConstantArray[U1,Length[groupOriginal]]&&E^(I FullSimplify[Sum[rOriginal[[i]]If[cjs[[i]],-1,1],{i,Length[rOriginal]}]])===If[Length[groupOriginal]==0,1,ConstantArray[1,Length[groupOriginal]]],result={Product[ToExpression[FromCharacterCode[96+i]],{i,Length[rOriginal]}]};variables=Table[{ToExpression[FromCharacterCode[96+i]]},{i,Length[rOriginal]}];Goto[end\[UnderBracket]part\[UnderBracket]of\[UnderBracket]Invariants]];
If[groupOriginal===ConstantArray[U1,Length[groupOriginal]]&&E^(I FullSimplify[Sum[rOriginal[[i]]If[cjs[[i]],-1,1],{i,Length[rOriginal]}]])!=1,result={};variables={};Goto[end\[UnderBracket]part\[UnderBracket]of\[UnderBracket]Invariants]];

(* Remove U1s and hypercharges *)
pU1s=Flatten[Position[groupOriginal,U1]];
pNonU1s=Flatten[Position[groupOriginal,x_/;x!=U1,{1}]];
hyperchargesSum=FullSimplify[Sum[rOriginal[[i,pU1s]]If[cjs[[i]],-1,1],{i,Length[rOriginal]}]];
If[!(E^(I hyperchargesSum)===0hyperchargesSum+1),result={};variables={};Goto[end\[UnderBracket]part\[UnderBracket]of\[UnderBracket]Invariants]];
group=groupOriginal[[pNonU1s]];
r=rOriginal[[All,pNonU1s]];
(* /Deal with U1's *)

InvariantsAux[otherStuff_,cm_,reps_,conjs_]:=Module[{aux1,aux1c,aux2,aux3,prov,trueReps,i1,j1},

If[Length[reps]==3,

aux1=Invariants3Mod[cm,reps,conjs];
aux1=(aux1//Normal)/.{a->ToExpression[FromCharacterCode[97+Length[otherStuff]]],b->ToExpression[FromCharacterCode[98+Length[otherStuff]]],c->ToExpression[FromCharacterCode[99+Length[otherStuff]]]};

aux2=otherStuff[[1]];
Do[
aux2=Flatten[Expand[otherStuff[[i1]] /.aux2],1];
,{i1,2,Length[otherStuff]}];

aux2=Flatten[Expand[aux1/.aux2]];
AppendTo[result,aux2];
Return[];
];

trueReps=Table[If[conjs[[i1]],ConjugateIrrep[cm,reps[[i1]]],reps[[i1]]],{i1,Length[reps]}];
aux1=ReduceRepProduct[cm,{trueReps[[1]],trueReps[[2]]}][[1;;-1,1]];
aux1=ConjugateIrrep[cm,#]&/@aux1;

aux2=ReduceRepProduct[cm,trueReps[[3;;-1]]][[1;;-1,1]];

aux1=Intersection[aux1,aux2];

Do[
aux2=(IrrepInProduct[cm,Append[reps[[1;;2]],aux1[[i1]]],Conjugations->Append[conjs[[1;;2]],True]] //Normal )/.{a->ToExpression[FromCharacterCode[96+Length[otherStuff]+1]],b->ToExpression[FromCharacterCode[96+Length[otherStuff]+2]]};
aux3=Flatten[Array[ToExpression[FromCharacterCode[96+Length[otherStuff]+2]],DimR[cm,aux1[[i1]]]]];
aux2=(MapThread[Rule,{aux3,#}])&/@aux2;

InvariantsAux[Append[otherStuff,aux2],cm,Prepend[reps[[3;;-1]],aux1[[i1]]],Prepend[conjs[[3;;-1]],True]];
,{i1,Length[aux1]}];
];

result={};

Piecewise[
{{InvariantsAux[{},group,r,cjs],Length[r]>3},
{result=Invariants3Mod[group,r,cjs],Length[r]==3},
{result=InvariantsOld[group,r[[1]],r[[2]],!(cjs[[1]]==cjs[[2]])],Length[r]==2},
{result=InvariantsOld[group,r[[1]],cjs[[1]]],Length[r]==1}
}];

(* BasisRotation - DO IT HERE: a[i]\[Rule] ..., b[i]\[Rule]..., etc *)
(* Be careful about conjugations cjs! *)
(* Be careful about how the transformation of a or a^T or a^* *)
(* THINK: do we need to apply BasisRotation here? Can't it be 'above' when Lagrangian is generated? *)

(* OptionValue[BasisRotation] *)

result=Flatten[result];
(*
result=result/.ruleToRepositionReps; cjs=cjsOriginal;(* restore ordering of reps [Update: no need to do it here; see below]*)

If[OptionValue[BasisRotation]=!=Null&&Length[result]>0,
rotationToTheSymbols=Conjugate[OptionValue[BasisRotation]];
Do[
If[cjs[[i]],rotationToTheSymbols[[i]]=Conjugate[rotationToTheSymbols[[i]]]];
,{i,Length[cjs]}];

variablesToRotate=Table[Flatten[Array[ToExpression[FromCharacterCode[96+i]],DimR[group,r[[i]]]]],{i,Length[r]}];
rotationRules={};
Do[
rotationRules=Join[rotationRules,MapThread[Rule,{variablesToRotate[[i]],rotationToTheSymbols[[i]].variablesToRotate[[i]]}]];
,{i,Length[r]}];
result=Expand[result/.rotationRules];
];
*)
variables=Sort/@Sort[Gather[Variables[result],Head[#1]==Head[#2]&],OrderedQ[{#1[[1]],#2[[1]]}]&];





Label[end\[UnderBracket]part\[UnderBracket]of\[UnderBracket]Invariants];

(* Extract the tensor form of the result *)
tensors=CoefficientArrays[result,Flatten[variables]];
aux4=Length/@variables;
aux5=Accumulate[aux4]-aux4+1;
tensors=tensors[[-1,All,Table[aux5[[i]];;Accumulate[aux4][[i]],{i,Length[variables]}]/.List->Sequence]];

If[tensors=!={}&&OptionValue[NormalizeAndSymmetrize]=!=False,
(* Normalized the invariants *)
orthogonalizeSnGenerators=If[OptionValue[NormalizeAndSymmetrize]==="SnNonOrthogonal",True,False];
tensors=NormalizeInvariants[groupOriginal,Table[If[!cjs[[i]],rOriginal[[i]] ,ConjugateIrrep[groupOriginal,rOriginal[[i]]]],{i,Length[rOriginalIn]}],tensors];
(* Symmetrize the invariants in a standard way (as given by PermutationSymmetryOfInvariants/SnIrrepGenerators) *)
tensors=SymmetrizeInvariants[groupOriginal,rOriginal,tensors,cjs,DistinguishFields->distFieds,OrthogonalizeGenerators->orthogonalizeSnGenerators];
tensors=FixSignOfInvariants[tensors];
];
If[!OptionValue[TensorForm],result=Expand[Fold[#1.#2&,tensors,Reverse[variables]]]];

(* [Start] Restore ordering of representations which was changed in [TAG-A] *)

If[!OptionValue[TensorForm],result=result/.ruleToRepositionReps];

If[tensors=!={}&&OptionValue[TensorForm], (* otherwise, there is no need to do anything else *)
tensors=Transpose[tensors,Prepend[1+orderingReps,1]];
variables=variables[[orderingRepsInv]]/.ruleToRepositionReps;
];
If[tensors=!={}&&OptionValue[NormalizeAndSymmetrize],
$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries[[1]]=$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries[[1]]/.MapThread[Rule,{Range[Length[rOriginalIn]],orderingReps}];
];
(* [End] Restore ordering of representations which was changed in [TAG-A] *)
If[!OptionValue[TensorForm],Return[result],Return[{tensors,variables}]];

]


(* This is the old wrapper method that calculates invariants of combinations of up to 3 fields. The new method (Invariants) may contain an arbitrary number of fields and has a different input syntax *)
InvariantsOld[arguments__]:=InvariantsOld[arguments]=Module[{result,argumentsList,nArgs,conjugate,aux,aux2,numberGroups},

argumentsList=Drop[{arguments},-1];
conjugate={arguments}[[-1]];
(* The conjugation argument is optional (default value=False) *)
If[!(TrueQ[conjugate]||TrueQ[!conjugate]),argumentsList={arguments};conjugate=False];
nArgs=Length[argumentsList];
numberGroups=Length[argumentsList[[1]]];


(* If the first argument is just one matrix (simple group) simply use the methods InvariantsBaseMethod *)
If[Depth[argumentsList[[1]]]==3,result=InvariantsBaseMethod[arguments],

(* ... if not (semi-simple group), some work must be done before using InvariantsBaseMethod *)

Do[
aux[i]=InvariantsBaseMethod[(#[[i]]&/@argumentsList )/.{x__}:>x,conjugate];
,{i,numberGroups}];

result=aux[1];
Do[
aux2={};
Do[
If[nArgs==4,
aux2=Join[aux2,aux[i] /.a[x1_]b[x2_]c[x3_ ]:>(result[[j]]/.{a[y1__]:>a[y1,x1],b[y1__]:>b[y1,x2],c[y1__]:>c[y1,x3]})]];
If[nArgs==3,
aux2=Join[aux2,aux[i] /.a[x1_]b[x2_]:>(result[[j]]/.{a[y1__]:>a[y1,x1],b[y1__]:>b[y1,x2]})]];
If[nArgs==2,
aux2=Join[aux2,aux[i] /.a[x1_]:>(result[[j]]/.{a[y1__]:>a[y1,x1]})]];

,{j,Length[result]}]; (* maybe there is more than one invariant in aux[i]; that's why this extra loop is needed *)
result=aux2;
,{i,2,numberGroups}];

];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvariantsBaseMethod[cm_,rep1_,conj_Symbol:False]:=Module[{result},

result=If[rep1==Table[0,{i,Length[cm]}],{a[1]},{}];
Return[result];
];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvariantsBaseMethod[cm_,rep1_,rep2_,conj_Symbol:False]:=Module[{n,array1,array2,aux1,aux2,aux3,aux4,r1,r2,w1,w2,dim1,dim2,b1,b2,e1,e2,matrixE,bigMatrix,expr,cont,coefs,result},

Off[Solve::"svars"];
n=Length[cm];
w1=Weights[cm,rep1];
w2=Weights[cm,rep2];
r1=RepMinimalMatrices[cm,rep1];
r2=RepMinimalMatrices[cm,rep2];

If[conj,
Do[
w2[[i,1]]=-w2[[i,1]];

,{i,Length[w2]}];
Do[
r2[[i,j]]=-Transpose[r2[[i,j]]];
,{i,n},{j,3}];];

(*---------------------*)
array1[x__]:=0;
array2[x__]:=0;
Do[array1[w1[[i,1]]]=w1[[i,2]],{i,Length[w1]}];
Do[array2[w2[[i,1]]]=w2[[i,2]],{i,Length[w2]}];
(*---------------------*)
aux1={};
Do[
If[array2[-w1[[i,1]]]!=0,aux1=Append[aux1,{w1[[i,1]],-w1[[i,1]]}]];
,{i,Length[w1]}];
(*---------------------*)
dim1[0]=0;
Do[dim1[i]=dim1[i-1]+array1[aux1[[i,1]]]array2[aux1[[i,2]]],{i,Length[aux1]}];

Do[b1[aux1[[i]]]=dim1[i-1]+1;
e1[aux1[[i]]]=dim1[i];
,{i,Length[aux1]}];
(*---------------------*)


bigMatrix={};
Do[

(*--------------------- Code for the e's --------------------- *)

aux2={};
Do[
If[array1[aux1[[j,1]]+cm[[i]]]!=0,
aux2=Append[aux2,{aux1[[j,1]]+cm[[i]],aux1[[j,2]]}]];
If[array2[aux1[[j,2]]+cm[[i]]]!=0,
aux2=Append[aux2,{aux1[[j,1]],aux1[[j,2]]+cm[[i]]}]];
,{j,Length[aux1]}];

aux2=DeleteDuplicates[aux2];

If[Length[w1]==1 && Length[w2]==1,aux2=aux1];  (* Special care is needed if both reps are singlets *)


(*---------------------*)
dim2[0]=0;
Do[dim2[i]=dim2[i-1]+array1[aux2[[i,1]]]array2[aux2[[i,2]]],{i,Length[aux2]}];

Do[b2[aux2[[i]]]=dim2[i-1]+1;
e2[aux2[[i]]]=dim2[i];
,{i,Length[aux2]}];
(*---------------------*)

If[dim2[Length[aux2]]!=0&&dim1[Length[aux1]]!=0,
matrixE=SparseArray[{},{dim2[Length[aux2]],dim1[Length[aux1]]}],matrixE={}];

Do[

If[array1[aux1[[j,1]]+cm[[i]]]!=0,
aux3=aux1[[j]];
aux4={aux1[[j,1]]+cm[[i]],aux1[[j,2]]};

matrixE[[b2[aux4];;e2[aux4],b1[aux3];;e1[aux3]]]=KroneckerProduct[BlockW[aux1[[j,1]]+cm[[i]],aux1[[j,1]],w1,r1[[i,1]]],IdentityMatrix[array2[aux1[[j,2]]]]];

];

If[array2[aux1[[j,2]]+cm[[i]]]!=0,
aux3=aux1[[j]];
aux4={aux1[[j,1]],aux1[[j,2]]+cm[[i]]};

matrixE[[b2[aux4];;e2[aux4],b1[aux3];;e1[aux3]]]=KroneckerProduct[IdentityMatrix[array1[aux1[[j,1]]]],BlockW[aux1[[j,2]]+cm[[i]],aux1[[j,2]],w2,r2[[i,1]]]];

];
,{j,Length[aux1]}];


If[bigMatrix!={},bigMatrix=SparseArray[bigMatrix]];
bigMatrix=Join[bigMatrix ,matrixE];
,{i,n}];

(*---------------------*)

dim1[0]=0;
Do[dim1[i]=dim1[i-1]+w1[[i,2]],{i,Length[w1]}];

dim2[0]=0;
Do[dim2[i]=dim2[i-1]+w2[[i,2]],{i,Length[w2]}];

Do[b1[w1[[i,1]]]=dim1[i-1];
,{i,Length[w1]}];

Do[b2[w2[[i,1]]]=dim2[i-1];
,{i,Length[w2]}];


If[Length[bigMatrix]!=0,
aux4=NullSpace2[bigMatrix,If[Length[bigMatrix]<10000,100,500]];

Do[
expr[i0]=0;
cont=0;
Do[
Do[
cont++;
expr[i0]+=aux4[[1,cont]]a[b1[aux1[[i,1]]]+j1] b[b2[aux1[[i,2]]]+j2];
,{j1,array1[aux1[[i,1]]]},{j2,array2[aux1[[i,2]]]}];
,{i,Length[aux1]}];
,{i0,Length[aux4]}];

result=Table[expr[i0],{i0,Length[aux4]}];

,result={}];

(* Special treatment - This code ensures that well known cases come out in the expected form *)

 (* Two SU(2) doublets and no conjugation ... fix the sign *)
If[cm==SU2&&rep1==rep2=={1}&&!conj, result=-result];

(* /Special treatment *)

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvariantsBaseMethod[cm_,rep1_,rep2_,rep3_,conj_Symbol:False]:=Module[{n,array1,array2,array3,aux1,aux2,aux3,aux4,r1,r2,r3,w1,w2,w3,dim1,dim2,dim3,b1,b2,b3,e1,e2,matrixE,bigMatrix,expr,cont,coefs,result},

Off[Solve::"svars"];
n=Length[cm];

w1=Weights[cm,rep1];
w2=Weights[cm,rep2];
w3=Weights[cm,rep3];
r1=RepMinimalMatrices[cm,rep1];
r2=RepMinimalMatrices[cm,rep2];
r3=RepMinimalMatrices[cm,rep3];

If[conj,
Do[
w3[[i,1]]=-w3[[i,1]];

,{i,Length[w3]}];
Do[
r3[[i,j]]=-Transpose[r3[[i,j]]];
,{i,n},{j,3}];];

(*---------------------*)
array1[x__]:=0;
array2[x__]:=0;
array3[x__]:=0;
Do[array1[w1[[i,1]]]=w1[[i,2]],{i,Length[w1]}];
Do[array2[w2[[i,1]]]=w2[[i,2]],{i,Length[w2]}];
Do[array3[w3[[i,1]]]=w3[[i,2]],{i,Length[w3]}];
(*---------------------*)
aux1={};
Do[
If[array3[-w1[[i,1]]-w2[[j,1]]]!=0,aux1=Append[aux1,{w1[[i,1]],w2[[j,1]],-w1[[i,1]]-w2[[j,1]]}]];
,{i,Length[w1]},{j,Length[w2]}];
(*---------------------*)
dim1[0]=0;
Do[dim1[i]=dim1[i-1]+array1[aux1[[i,1]]]array2[aux1[[i,2]]]array3[aux1[[i,3]]],{i,Length[aux1]}];

Do[b1[aux1[[i]]]=dim1[i-1]+1;
e1[aux1[[i]]]=dim1[i];
,{i,Length[aux1]}];
(*---------------------*)


bigMatrix={};
Do[

(*--------------------- Code for the e's --------------------- *)

aux2={};
Do[
If[array1[aux1[[j,1]]+cm[[i]]]!=0,
aux2=Append[aux2,{aux1[[j,1]]+cm[[i]],aux1[[j,2]],aux1[[j,3]]}]];
If[array2[aux1[[j,2]]+cm[[i]]]!=0,
aux2=Append[aux2,{aux1[[j,1]],aux1[[j,2]]+cm[[i]],aux1[[j,3]]}]];
If[array3[aux1[[j,3]]+cm[[i]]]!=0,
aux2=Append[aux2,{aux1[[j,1]],aux1[[j,2]],aux1[[j,3]]+cm[[i]]}]];
,{j,Length[aux1]}];
aux2=DeleteDuplicates[aux2];
If[Length[w1]==1 && Length[w2]==1&& Length[w3]==1,aux2=aux1];   (* Special care is needed if all 3 reps are singlets *)
(*---------------------*)
dim2[0]=0;
Do[dim2[i]=dim2[i-1]+array1[aux2[[i,1]]]array2[aux2[[i,2]]]array3[aux2[[i,3]]],{i,Length[aux2]}];

Do[b2[aux2[[i]]]=dim2[i-1]+1;
e2[aux2[[i]]]=dim2[i];
,{i,Length[aux2]}];
(*---------------------*)


If[dim2[Length[aux2]]!=0&&dim1[Length[aux1]]!=0,
matrixE=SparseArray[{},{dim2[Length[aux2]],dim1[Length[aux1]]}],matrixE={}];

Do[

If[array1[aux1[[j,1]]+cm[[i]]]!=0,
aux3=aux1[[j]];
aux4={aux1[[j,1]]+cm[[i]],aux1[[j,2]],aux1[[j,3]]};

matrixE[[b2[aux4];;e2[aux4],b1[aux3];;e1[aux3]]]=KroneckerProduct[BlockW[aux1[[j,1]]+cm[[i]],aux1[[j,1]],w1,r1[[i,1]]],IdentityMatrix[array2[aux1[[j,2]]]],IdentityMatrix[array3[aux1[[j,3]]]]];
];

If[array2[aux1[[j,2]]+cm[[i]]]!=0,
aux3=aux1[[j]];
aux4={aux1[[j,1]],aux1[[j,2]]+cm[[i]],aux1[[j,3]]};

matrixE[[b2[aux4];;e2[aux4],b1[aux3];;e1[aux3]]]=KroneckerProduct[IdentityMatrix[array1[aux1[[j,1]]]],BlockW[aux1[[j,2]]+cm[[i]],aux1[[j,2]],w2,r2[[i,1]]],IdentityMatrix[array3[aux1[[j,3]]]]];
];

If[array3[aux1[[j,3]]+cm[[i]]]!=0,
aux3=aux1[[j]];
aux4={aux1[[j,1]],aux1[[j,2]],aux1[[j,3]]+cm[[i]]};

matrixE[[b2[aux4];;e2[aux4],b1[aux3];;e1[aux3]]]=KroneckerProduct[IdentityMatrix[array1[aux1[[j,1]]]],IdentityMatrix[array2[aux1[[j,2]]]],BlockW[aux1[[j,3]]+cm[[i]],aux1[[j,3]],w3,r3[[i,1]]]];
];


,{j,Length[aux1]}];

If[bigMatrix!={},bigMatrix=SparseArray[bigMatrix]];
bigMatrix=Join[bigMatrix ,matrixE];

,{i,n}];

(*---------------------*)

dim1[0]=0;
Do[dim1[i]=dim1[i-1]+w1[[i,2]],{i,Length[w1]}];

dim2[0]=0;
Do[dim2[i]=dim2[i-1]+w2[[i,2]],{i,Length[w2]}];

dim3[0]=0;
Do[dim3[i]=dim3[i-1]+w3[[i,2]],{i,Length[w3]}];

Do[b1[w1[[i,1]]]=dim1[i-1];
,{i,Length[w1]}];

Do[b2[w2[[i,1]]]=dim2[i-1];
,{i,Length[w2]}];

Do[b3[w3[[i,1]]]=dim3[i-1];
,{i,Length[w3]}];

If[Length[bigMatrix]!=0,


aux4=NullSpace2[bigMatrix,If[Length[bigMatrix]<10000,100,500]];


Do[
expr[i0]=0;
cont=0;
Do[
Do[
aux2=0;
Do[
cont++;
aux2+=aux4[[i0,cont]]a[b1[aux1[[i,1]]]+j1] b[b2[aux1[[i,2]]]+j2] c[b3[aux1[[i,3]]]+j3];
,{j2,array2[aux1[[i,2]]]},{j3,array3[aux1[[i,3]]]}];
expr[i0]+=aux2;
,{j1,array1[aux1[[i,1]]]}]

,{i,Length[aux1]}];
,{i0,Length[aux4]}];

result=Table[expr[i0],{i0,Length[aux4]}];

,result={}];


(* Special treatment - This code ensures that well known cases come out in the expected form *)


(* Two SU(2) doublets and a singlet no conjugation on the doublets ... fix the sign *)
If[cm==SU2&&Sort[{rep1,rep2,rep3}]=={{0},{1},{1}}&&(!conj||rep3=={0}), result=-result]; 

(* /Special treatment *)

Return[result];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX ANOMALIES XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Check if a model is anomally free or not *)
TriangularAnomalyCheck[groups_,reps_,nF_:Null]:=Module[{nFlavours,anomalies,result},
(* If no number of flavours were given assume that they are all =1 *)
nFlavours=If[nF===Null,ConstantArray[1,Length[reps]],nF];

anomalies=Total[nFlavours (TriangularAnomalyValue[groups,#]&/@reps)];
result=(anomalies===0 anomalies);
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* For 1 field/representation this method gives a list which, when summed for all the representations in a model (note: including flavour multiplicity), must be the {0,0,...} list *)

Options[TriangularAnomalyValue]={Verbose->False};
TriangularAnomalyValue[groups_,rep_,OptionsPattern[]]:=Module[{posU1s,posSUNs,dimRep,dynkins,n,sigmas,aux,aux2,part1,part2,result,groupNames},

posU1s=Position[groups,{},{1}]//Flatten;
posSUNs=Position[groups,x_/;Length[x]>1&&x===CartanMatrix["A",Length[x]],{1}]//Flatten;

dimRep=Times@@DimR[groups,rep] ;
dynkins=dimRep DynkinIndex[groups,rep]/DimR[groups,rep];


result={};

(* Y Y' Y'' cases (with maybe Y!=Y'!=Y'') *)
Do[
If[i<j<k,AppendTo[result,{{i,j,k},dimRep rep[[i]]rep[[j]]rep[[k]]}]];
,{i,posU1s},{j,posU1s},{k,posU1s}];


(* Y Y Y' (with maybe Y=Y') cases and T T Y cases *)
Do[
aux=dynkins rep[[i]];
aux2=Table[{i,j,j},{j,Length[groups]}];
result=Join[result,Transpose[{aux2,aux}]];
,{i,posU1s}];

(* TTT cases - see "Gauge groups without triangular anomaly", Susumu Okubo, 1977 *)
Do[
n=Length[groups[[i]]]+1;
sigmas=-Prepend[Accumulate[rep[[i]]],0];
sigmas=sigmas+1/2(n+1)-Range[n]-1/n Total[sigmas];
aux=Total[dimRep n/((n^2-1)(n^2-4))sigmas^3];
AppendTo[result,{{i,i,i},aux}];
,{i,posSUNs}];

If[OptionValue[Verbose],

groupNames=CMtoName[groups];
aux=Flatten[Position[groupNames,#]]&/@DeleteDuplicates[groupNames];
Do[If[Length[el]>1,groupNames[[el[[i]]]]=Subscript[groupNames[[el[[i]]]], i]],{el,aux},{i,Length[el]}];
Print[Row[{Style["XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",GrayLevel[0.5]],"\n",Style[">>> The input group has the following factors: ",{Bold,Darker[Red]}],groupNames,".\n",Style[Row[{">>> There are ",Length[result]," anomalies to consider: "}],{Bold,Darker[Red]}],Times@@groupNames[[#]]&/@result[[All,1]],".\n",Style[">>> The values of the anomalies given by the TriangularAnomalyValue function follow this order.",{Bold,Darker[Red]}],Style["\nXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",GrayLevel[0.5]]},BaseStyle->{FontFamily->"Consolas"}]];

];
result=result[[All,2]];
Return[result];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX LISTING ALL REPS UP TO SOME SIZE XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

ConjugacyClassGroupModIndices[cm_]:=Module[{series,n,result},
If[cm===U1,Return[{-1}]]; (* This -1 is just symbolic, so that the user knows there is a U1 *)
{series,n}=CMtoFamilyAndSeries[cm];

If[series==="A",result={n+1}];
If[series==="B",result={2}];
If[series==="C",result={2}];

If[series==="D",result={2,4}];

If[series==="E"&&n==6,result={3}];
If[series==="E"&&n==7,result={2}];
If[series==="E"&&n==8,result={0}];
If[series==="F",result={0}];
If[series==="G",result={0}];
Return[result];
]

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


(* Code below somewhat experimental [for speeding up invariants function] 04/Feb/2014 *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

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

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This function is used to speed up the calculation of invariants, by breaking the original group into smaller ones. *)

(* Given a simple group cm, this function will output a {subgroup, <info>}, where subgroup is a regular subalgebra of cm obtained by converting dots of its Dynkin diagram to U(1)s. <info> provides information on the surviving generators: <info>'s element i is of the form  {False,{i1,i2,...,iN}} (for non-U1 dots) or {True,{i1,i2,...,iN}} for U1 dots, such that the generators {i1,i2,...,iN}.(RepMinimalMatrices[group,rep][[All,3]]) (U1s) or {i1,i2,...,iN}.RepMinimalMatrices[group,rep] are generators of the subgroup associated with its dot i *)

(* It is important latter on that in subgroup the U1s appear in the position from which they were taken from group *)
AuxiliarRegularDecompositionOfGroup\[UnderBracket]InvariantsSpeedUp[cm_]:=Module[{aux,group,subgroup,u1sPosition,hypercharges,minimalGeneratorsOfSubgroup,reorderNonU1Roots},

reorderNonU1Roots={};

group=CMtoFamilyAndSeries[cm];
If[group[[1]]==="A",
subgroup=Flatten[ConstantArray[{SU3,U1},Quotient[group[[2]],3]],1];
u1sPosition=3Range[Quotient[group[[2]],3]];
Switch[Mod[group[[2]],3],1,AppendTo[subgroup,SU2],2,AppendTo[subgroup,SU3]];
];

If[group[[1]]==="B",
If[group[[2]]==2,
subgroup={SO5};
u1sPosition={};
,
subgroup=Join[Flatten[ConstantArray[{U1,SU3},Quotient[group[[2]],3]-1],1],{U1,SO5}];
u1sPosition=(1+Length[cm])-3Range[Quotient[group[[2]],3]];
Switch[Mod[group[[2]],3],1,PrependTo[subgroup,SU2],2,PrependTo[subgroup,SU3]];
];

];
(* Same as with B family actually *)
If[group[[1]]==="C",
If[group[[2]]==2,
subgroup={SP4};
u1sPosition={};
,
subgroup=Join[Flatten[ConstantArray[{U1,SU3},Quotient[group[[2]],3]-1],1],{U1,SP4}];
u1sPosition=(1+Length[cm])-3Range[Quotient[group[[2]],3]];
Switch[Mod[group[[2]],3],1,PrependTo[subgroup,SU2],2,PrependTo[subgroup,SU3]];
];

];

If[group[[1]]==="D",
subgroup=Join[Flatten[ConstantArray[{U1,SU3},Quotient[group[[2]],3]-1],1],{U1,SU2,SU2}];
u1sPosition=(1+Length[cm])-3Range[Quotient[group[[2]],3]];
Switch[Mod[group[[2]],3],1,PrependTo[subgroup,SU2],2,PrependTo[subgroup,SU3]];
];

(* Test this exception *)
(*
If[group==={"D",5},subgroup={SU2,U1,SU4};u1sPosition={2};reorderNonU1Roots={1,2,4,3,5}];
*)

If[group==={"E",6},subgroup={SU3,U1,SU3,SU2};u1sPosition={3}];
If[group==={"E",7},subgroup={SU3,U1,SU3,U1,SU2};u1sPosition={3,6}];
If[group==={"E",8},subgroup={SU3,U1,SU3,U1,SU2,SU2};u1sPosition={3,6}];
If[group==={"F",4},subgroup={SU3,U1,SU2};u1sPosition={3}];
If[group==={"G",2},subgroup={SU2,U1;u1sPosition={2}}];

(* How this works: *)
(* Looking at the Serre relations ([Ei,Fj]=\[Delta]ij Hi, [Hi,Ej]=Aji Ej, [Hi,Fj]=-Aji Fj), we see that the conversion of a dot in a Dynkin diagram to a U1 results in discarding the associated Ei,Fi but not the Hi. All other generators remain the same. As for the Hi associated to the U1s, by the second and third Serre relations, they must be such that they commute with the surviving Ej and Fj. In practice, this means finding the nullspace of the Cartan matrix of the original group, with the rows corresponding to the U1 dots/roots removed. *)
hypercharges={True,#}&/@NullSpace[cm[[Complement[Range[Length[cm]],u1sPosition]]]];

(* minimalGeneratorsOfSubgroup={<item 1>,...} where <item I> = {False,{i1,i2,...,iN}} means that {i1,i2,...,iN}.RepMinimalMatrices[group,rep] are to be extracted (non-U1 group), and <item I> = {True,{i1,i2,...,iN}} means that {i1,i2,...,iN}.(RepMinimalMatrices[group,rep][[All,3]]) should be extracted (U1 factor) *)
If[reorderNonU1Roots==={},
minimalGeneratorsOfSubgroup=Table[If[MemberQ[u1sPosition,i],Null,{False,UnitVector[Length[cm],i]}],{i,Length[cm]}];,
minimalGeneratorsOfSubgroup=Table[If[MemberQ[u1sPosition,i],Null,{False,UnitVector[Length[cm],reorderNonU1Roots[[i]]]}],{i,Length[cm]}];
];
minimalGeneratorsOfSubgroup[[u1sPosition]]=hypercharges;


(* 
(* Embedding 1/2 *)
If[group==={"D",5},subgroup={SU2,U1,SU3,U1};minimalGeneratorsOfSubgroup={{False,{1,0,0,0,0}},{True,{-1,-2,0,0,2}},{False,{0,0,1,0,0}},{False,{0,0,0,1,0}},{True,{3,6,4,2,0}}}];

(* Embedding 3/4 *)
If[group==={"D",5},subgroup={SU3,U1,SU2,U1};minimalGeneratorsOfSubgroup={{False,{1,0,0,0,0}},{False,{0,1,0,0,0}},{True,{0,0,0,0,1}},{False,{0,0,0,1,0}},{True,{2,4,6,3,0}}}];
*)

(* Embedding 3/4 *)
If[group==={"D",5},subgroup={SU3,U1,SU2,U1};minimalGeneratorsOfSubgroup={{False,{1,0,0,0,0}},{False,{0,1,0,0,0}},{True,{0,0,0,0,1}},{False,{0,0,0,1,0}},{True,{2,4,6,3,0}}}];

Return[{subgroup,minimalGeneratorsOfSubgroup}];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This is inspired on BreakRep from SSB.m. The difference is that the subreps are known. Also, this function is to be used to speed up the Invariants function *)
(* The output is {list of irreps of the subgroup,W} such that Inverse[W].<original group matrices combination I>.W=<subgroup matrix I>. Note that W is not unitary in general. The invariants Inv^abc obtained with <subgroup matrices> can be corrected to <original group matrices> as Inv^abc \[Rule] Inv^a'b'c' Inverse[W]a'a Inverse[W]b'b Inverse[W]c'c  *)
BreakRepMod[bigGroup_,smallerGroup_,repToBreak_,gaugeRotInfo_]:=Module[{repMatrices1,projectionMatrix, listOfIrreps,aux,aux2,aux3,nInvs,count,linearCombinations,irreps,timeU,counter,printedInfo,diagMatsPositions,relevantComponents,relevantRows},

aux=SparseArray[RepMinimalMatrices[bigGroup,repToBreak]];
repMatrices1=SimplifySA/@Flatten[Table[If[gaugeRotInfo[[i,1]]===False,gaugeRotInfo[[i,2]].aux,gaugeRotInfo[[i,2]].SparseArray[aux[[All,{3}]]]],{i,Length[bigGroup]}],1];
projectionMatrix=gaugeRotInfo[[All,2]];
listOfIrreps=Tally[DecomposeReps[{bigGroup},{repToBreak},smallerGroup,projectionMatrix]][[All,1]];

count=0;
linearCombinations={};
irreps={};

counter=0;
(* printedInfo=PrintTemporary[Dynamic[Row[{"Total states rotated so far: ",count,"/",DimR[bigGroup,repToBreak]},""]]]; *)
Do[

aux=BuildProductRepMinimal[smallerGroup,listOfIrreps[[irrepIndex]]];
diagMatsPositions=Position[Flatten[Table[If[gaugeRotInfo[[i,1]]===False,{False,False,True},{True}],{i,Length[bigGroup]}],1],True][[All,1]];
aux3=Transpose[Diagonal/@repMatrices1[[diagMatsPositions]]];
aux2=DeleteDuplicates[Transpose[Diagonal/@aux[[diagMatsPositions]]]];

relevantComponents=DeleteDuplicates[Flatten[Position[aux3,x_/;MemberQ[aux2,x]]]];
relevantRows=DeleteDuplicates[ArrayRules[repMatrices1[[All,All,relevantComponents]]][[1;;-2,1,2]]];
relevantComponents=DeleteDuplicates[Join[relevantComponents,relevantRows]];

aux2=InvariantsSuperFreeFormMod[repMatrices1[[All,relevantComponents,relevantComponents]],SimplifySA/@aux,True]; 
nInvs=Length[aux2];
(* There are for sure these irreps *)

(* Separate the direct product of groups correctly *)
aux2=aux2 /.a[j_]:>a[relevantComponents[[j]]];
Do[
aux2[[j]]=aux2[[j]]/.b[j_]:>b[j+counter];
counter+=Length[aux[[1]]];
,{j,nInvs}];

 aux2=CoefficientArrays[#,Join[Array[a,Dimensions[repMatrices1][[-1]]],Array[b,Dimensions[repMatrices1][[-1]]]]][[3]]&/@aux2;
aux2=#[[1;;Dimensions[repMatrices1][[-1]],Dimensions[repMatrices1][[-1]]+1;;-1]]&/@aux2;

 aux2=SimplifySA[Total[aux2]]; 
AppendTo[linearCombinations,aux2];
AppendTo[irreps,Table[listOfIrreps[[irrepIndex]],{j,nInvs}]];

count+=nInvs Length[aux[[1]]];

,{irrepIndex,Length[listOfIrreps]}];

(* NotebookDelete[printedInfo]; *)
If[count==DimR[bigGroup,repToBreak],Null,Print["ERROR (BreakRepMod): Dimensions of the subrepresentations don't add up."]];

irreps=Flatten[irreps,1];
 (* linearCombinations=Flatten[linearCombinations,1]; *)

(* The conjugation takes care of the fact that we got this result from coefficients a,b *)
(* N's and RootApproximant are meant to simplify the expressions in a quick and accurate way. If problems arrise, change to Simplify *)

(* linearCombinations=RootApproximant[Chop[Conjugate[Transpose[#]]]]&/@N[linearCombinations]; *)
(* Make sure that the norm of the new states is the same as the old ones *)
(* linearCombinations=RootApproximant[#/Norm[#]]&/@N[linearCombinations]; *)

Return[{irreps,linearCombinations}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This function outputs {<list>,<3d tensor>} where <list> = {<el1>,<el2>,...} where each <el> contains the positions of combinations of the representations which contain invariants. The resulting big 3-d tensor is the second ouput *)
GetMultipleTrilinearInvariantsCombinations[group_,reps_]:=Module[{aux,aux2,invs,posNonU1s,resultTensor,dims,accDims,countInv,dimsI},

posNonU1s=Flatten[Position[group,x_/;x=!={},{1},Heads->False]];

aux=Table[{ConjugateIrrep[group,#[[1]]],#[[2]]}&/@ReduceRepProduct[group,{reps[[1,rI]],reps[[2,rJ]]}],{rI,Length[reps[[1]]]},{rJ,Length[reps[[2]]]}];
aux=Table[If[MemberQ[aux[[rI,rJ,All,1]],reps[[3,rK]]],{{rI,rJ,rK},Total[Cases[aux[[rI,rJ]],x_/;x[[1]]==reps[[3,rK]]:>x[[2]]]]},False],{rI,Length[reps[[1]]]},{rJ,Length[reps[[2]]]},{rK,Length[reps[[3]]]}];
aux=DeleteCases[Flatten[aux,2],False];

dims=Map[Times@@DimR[group,#]&,reps,{2}];
accDims=Accumulate[#]-#&/@dims;
(* ***************** *)
resultTensor={};
countInv=0;
Do[
dimsI={DimR[group[[posNonU1s]],reps[[1,aux[[i,1,1]],posNonU1s]]],DimR[group[[posNonU1s]],reps[[2,aux[[i,1,2]],posNonU1s]]],DimR[group[[posNonU1s]],reps[[3,aux[[i,1,3]],posNonU1s]]]};

invs=Invariants[group,{reps[[1,aux[[i,1,1]]]],reps[[2,aux[[i,1,2]]]],reps[[3,aux[[i,1,3]]]]},TensorForm->True][[1]];

(* resultTensor[[countInv;;countInv+Length[invs[[i]]]-1,accDims[[aux[[i,1]]]]-dims[[aux[[i,1]]]]+1;;accDims[[aux[[i,1]]]],accDims[[aux[[i,2]]]]-dims[[aux[[i,2]]]]+1;;accDims[[aux[[i,2]]]],accDims[[aux[[i,3]]]]-dims[[aux[[i,3]]]]+1;;accDims[[aux[[i,3]]]]]]=invs[[i]]; *)
aux2=ArrayRules[invs][[1;;-2]];
aux2[[All,1]]=({countInv,accDims[[1,aux[[i,1,1]]]],accDims[[2,aux[[i,1,2]]]],accDims[[3,aux[[i,1,3]]]]}+#)&/@aux2[[All,1]];
resultTensor=Join[resultTensor,aux2];

countInv+=Length[invs];
,{i,Length[aux]}];

resultTensor=SparseArray[resultTensor,{countInv,(accDims+dims)[[1,-1]],(accDims+dims)[[2,-1]],(accDims+dims)[[3,-1]]}];

Return[{aux,resultTensor}];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* This is the end function which effective calculates trilinear invariants (and matching coefficients with particular subgroup embeddings which are determined in AuxiliarRegularDecompositionOfGroup) *)
SMethod[group_,reps_]:=Module[{subgroup,subreps,trilinearCombinations,gaugeRotInfo,aux,aux2,rotMatrices,rotatedInvariants,repM,validCombinationOfSubInvs,validCombinationsOfSubInvariants,finalResult,projectionMatrix},
Print["MEMORY IN USE 0: ",MemoryInUse[]];
tmp=TimeUsed[];
{subgroup,gaugeRotInfo}=AuxiliarRegularDecompositionOfGroup\[UnderBracket]InvariantsSpeedUp[group];
aux=BreakRepMod[group,subgroup,#,gaugeRotInfo]&/@reps;
subreps=aux[[All,1]];
aux2=GetMultipleTrilinearInvariantsCombinations[subgroup,subreps];
trilinearCombinations=aux2[[1]]; (* for output only *)
projectionMatrix=gaugeRotInfo[[All,2]]; (* for output only *)

Print["TIME USED 1: ",TimeUsed[]-tmp];
rotMatrices=Total/@aux[[All,2]];

(* ---------------- Rotate invariants ---------------- *)
rotatedInvariants=aux2[[2]];
Do[
rotatedInvariants=DotN[rotMatrices[[i]],rotatedInvariants,i+1];
,{i,Length[reps]}];
rotatedInvariants=SimplifySA[rotatedInvariants];

Print["TIME USED 2: ",TimeUsed[]-tmp];
Print["S1 ",rotatedInvariants];
(* ---------------- [END] Rotate invariants ---------------- *)

(* Get only the raising operators of the discarded dots in the Cartan diagram which were converted to U1s *)
repM=Table[RepMinimalMatrices[group,reps[[i]]][[Flatten[Position[gaugeRotInfo,x_/;x[[1]]=!=False,{1},Heads->False]],1]],{i,Length[reps]}];
Print["S2b ",repM];
Print["TIME USED 3: ",TimeUsed[]-tmp];

validCombinationsOfSubInvariants={};
Do[
AppendTo[validCombinationsOfSubInvariants,SimplifySA[Sum[DotN[repM[[j,i]],rotatedInvariants,j+1],{j,Length[reps]}]]];
,{i,Length[repM[[1]]]}]; 

Print["TIME USED 4: ",TimeUsed[]-tmp];
validCombinationsOfSubInvariants=SparseArray[validCombinationsOfSubInvariants];
Print["MEMORY IN USE 1: ",MemoryInUse[]];
validCombinationsOfSubInvariants=Flatten[validCombinationsOfSubInvariants,{{2},Join[{1},2+Range[Length[reps]]]}];
Print["MEMORY IN USE 2: ",MemoryInUse[]];
validCombinationsOfSubInvariants=NullSpace2T[validCombinationsOfSubInvariants,500];
Print["MEMORY IN USE 3: ",MemoryInUse[]];


finalResult=SparseArray[validCombinationsOfSubInvariants,Dimensions[validCombinationsOfSubInvariants]].rotatedInvariants;
Print["MEMORY IN USE 4a: ",MemoryInUse[]];
aux=Sqrt[Sqrt[Times@@Flatten[DimR[group,#]&/@reps]]/Simplify[Total[#,3]&/@SimplifySA[Abs[SimplifySA[finalResult^2]]]]];
finalResult=SimplifySA[aux finalResult];
validCombinationsOfSubInvariants=Simplify[aux validCombinationsOfSubInvariants];

Print["MEMORY IN USE 4b: ",MemoryInUse[]];
Print["TIME USED 5: ",TimeUsed[]-tmp];
Return[{finalResult,{subgroup,projectionMatrix,subreps,trilinearCombinations,validCombinationsOfSubInvariants}}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* (NOT ANY MORE) This function is called by InvariantsBaseMethod[cm_,rep1_,rep2_,rep3_,conj_Symbol:False] if the gauge group is of rank 4 or bigger, to speed up the calculation *)

(* TODO: deal with conjugation *)

InvariantsSpeedUp\[UnderBracket]With\[UnderBracket]SSB[group_,reps_,conj_Symbol:False]:=Module[{subgroup,subreps,gaugeRotInfo,aux,aux2,rotMatrices,rotatedInvariants,repM,validCombinationOfSubInvs,validCombinationsOfSubInvariants,finalResult},

{subgroup,gaugeRotInfo}=AuxiliarRegularDecompositionOfGroup\[UnderBracket]InvariantsSpeedUp[group];
aux=BreakRepMod[group,subgroup,#,gaugeRotInfo]&/@reps;
subreps=aux[[All,1]];
aux2=GetMultipleTrilinearInvariantsCombinations[subgroup,subreps];

rotMatrices=Total/@aux[[All,2]];

(* ---------------- Rotate invariants ---------------- *)
rotatedInvariants=aux2[[2]];
Do[
rotatedInvariants=DotN[rotMatrices[[i]],rotatedInvariants,i+1];
,{i,Length[reps]}];
rotatedInvariants=SimplifySA[rotatedInvariants];
(* ---------------- [END] Rotate invariants ---------------- *)

(* Get only the raising operators of the discarded dots in the Cartan diagram which were converted to U1s *)
repM=Table[RepMinimalMatrices[group,reps[[i]]][[Flatten[Position[gaugeRotInfo,x_/;x[[1]]=!=False,{1},Heads->False]],1]],{i,Length[reps]}];

validCombinationsOfSubInvariants={};
Do[
AppendTo[validCombinationsOfSubInvariants,SimplifySA[Sum[DotN[repM[[j,i]],rotatedInvariants,j+1],{j,Length[reps]}]]];
,{i,Length[repM[[1]]]}]; 

validCombinationsOfSubInvariants=SparseArray[validCombinationsOfSubInvariants];
validCombinationsOfSubInvariants=Flatten[validCombinationsOfSubInvariants,{{2},Join[{1},2+Range[Length[reps]]]}];
validCombinationsOfSubInvariants=NullSpace2T[validCombinationsOfSubInvariants,500];


finalResult=SparseArray[validCombinationsOfSubInvariants,Dimensions[validCombinationsOfSubInvariants]].rotatedInvariants;
aux=Sqrt[Sqrt[Times@@Flatten[DimR[group,#]&/@reps]]/Simplify[Total[#,3]&/@SimplifySA[Abs[SimplifySA[finalResult^2]]]]];
finalResult=SimplifySA[aux finalResult];
validCombinationsOfSubInvariants=Simplify[aux validCombinationsOfSubInvariants];


finalResult=finalResult.Array[c,Dimensions[finalResult][[4]]].Array[b,Dimensions[finalResult][[3]]].Array[a,Dimensions[finalResult][[2]]];
Return[finalResult];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* For simple groups only *)
(* Given a real representation, this function returns the rotation matrix B such that *)
RotationToRealBasis[group_,rep_]:=Module[{V,result},
V=Invariants[group,{rep,rep},TensorForm->True][[1,1]];
result=Transpose[TakagiDecomposition[V]];
Return[result];
]


(* ::Input::Initialization:: *)
(* This method is even simpler to use, if the projection matrix prtMatrix for a particular breaking is already set up *)
(* But there is a problem: in some cases there are multiple SSB chains/paths that lead to different results. Use chains in this case. E.g.: *)
DecomposeRep[chain_,rep_]:=Module[{projectionMatrix,chainMod},
chainMod=Flatten[{chain},\[Infinity],Rule];
projectionMatrix=Table[prjMatrix[chainMod[[i]],chainMod[[i+1]]],{i,Length[chainMod]-1}];
projectionMatrix=If[Length[chainMod]>2,Dot@@Reverse[projectionMatrix],projectionMatrix[[1]]];
Return[DecomposeRep[chainMod[[1]],rep,chainMod[[-1]],projectionMatrix]];
]

(* Use this method - it is more user friendly *)
(* Will it work if the new groups are all U1s? *)
(* oG can be a list of groups *)
Options[DecomposeRep]={UseName->False};
DecomposeRep[oG_,oRep_,newGs_,projectionMatrix_,OptionsPattern[]]:=DecomposeRep[oG,oRep,newGs,projectionMatrix,UseName->OptionValue[UseName]]=Module[{posU1s,posNonU1s,limits,projectionMatrixApart,aux,result},
posU1s=Position[newGs,{},{1}]//Flatten;
posNonU1s=Complement[Range[Length[newGs]],posU1s];

limits=Prepend[1+Accumulate[Max[Length[#],1]&/@newGs],1];
projectionMatrixApart=Table[projectionMatrix[[limits[[i]];;limits[[i+1]]-1]],{i,Length[newGs]}];


aux=DecomposeRep\[UnderBracket]Aux[oG,oRep,newGs[[posNonU1s]],newGs[[posU1s]],Join@@projectionMatrixApart[[posNonU1s]],Join@@projectionMatrixApart[[posU1s]]];

(* initialize the result variable *)
result=ConstantArray[0,{Length[aux],Length[newGs]}];

(* Put the U1s in the right position *)
result[[All,posU1s]]=aux[[All,2]];

(* Put the rest of things in the right postion *)
result[[All,posNonU1s]]=aux[[All,1]];

If[OptionValue[UseName],Return[RepName[newGs,#]&/@result],Return[result]];
]

(* Less user frindly *)
(* Will it work if the new groups are all U1s? *)
(* oG can be a list of groups *)

(* UPDATE: assume that oGin is a list of groups. *)
DecomposeRep\[UnderBracket]Aux[oGIn_,oRepIn_,newGNonU1s_,newGU1s_,projectionMatrixNonU1sIn_,projectionMatrixU1sIn_]:=Module[{aux,aux2,oRepU1s,oRepNonU1s,limits,limitsAc,weights,result,posOGU1s,posOGNonU1s,oG,oRep,projectionMatrixNonU1s,projectionMatrixU1s,conjugacyClassFunction,idx,res,genericRepresentation,resTemp,completeResult,weightsGroups},

(* [OPERATION REV] In the original group, U1s may not come last. However, in the following it is useful that they do, therefore this is changed here *)
posOGU1s=Flatten[Position[oGIn,{},{1},Heads->False]];
posOGNonU1s=Flatten[Position[oGIn,x_/;!(x==={}),{1},Heads->False]];

limits=Max[1,Length[#]]&/@oGIn;
limitsAc=Table[Range@@(Accumulate[limits][[i]]-limits[[i]]+{1,limits[[i]]}),{i,Length[limits]}];

projectionMatrixNonU1s=projectionMatrixNonU1sIn[[All,Flatten[Join[limitsAc[[posOGNonU1s]],limitsAc[[posOGU1s]]]]]];
projectionMatrixU1s=projectionMatrixU1sIn[[All,Flatten[Join[limitsAc[[posOGNonU1s]],limitsAc[[posOGU1s]]]]]];

oG=Join[oGIn[[Flatten[Position[oGIn,x_/;!(x==={}),{1},Heads->False]]]],oGIn[[Flatten[Position[oGIn,{},{1},Heads->False]]]]];
oRep=Join[oRepIn[[Flatten[Position[oGIn,x_/;!(x==={}),{1},Heads->False]]]],oRepIn[[Flatten[Position[oGIn,{},{1},Heads->False]]]]];
(* [OPERATION REV] Ends here *)

oRepU1s=Flatten[oRep[[Flatten[Position[oG,{},{1},Heads->False]]]]];
oRepNonU1s=Flatten[oRep[[Flatten[Position[oG,x_/;!(x==={}),{1},Heads->False]]]]];

(* If there are only U1's in the subgroup *)
If[newGNonU1s==={},

aux=ConstantArray[{{},(projectionMatrixU1s.Join@@#[[1;;-2]])},#[[-1]]]&/@If[oRepU1s==={},WeightsMod[oG,{oRepNonU1s,1}],WeightsMod[oG[[Flatten[Position[oG,x_/;x=!={},{1},Heads->False]]]],{oRepNonU1s,oRepU1s,1}]];
aux=Flatten[aux,1];
Return[aux];
];

limits=Prepend[1+Accumulate[Length/@newGNonU1s],1];

(* [--------------------OPERATION SPEED UP 1--------------------] Start *)
If[Length[oG]==1&&Length[newGNonU1s]==1&&Length[newGU1s]==0&&Length[oG[[1]]]==Length[newGNonU1s[[1]]]&&Det[projectionMatrixNonU1s]!=0,
(* Speed up happens for this case: original group=simple group; new group= simple group with same rank *)

weights=SpeedUp1\[UnderBracket]DecomposeReps[oG[[1]],newGNonU1s[[1]],oRepNonU1s,Inverse[projectionMatrixNonU1s]];

,
(* No speed up *)

(* TODO: seems unnecessary to consider that oG might not be a list of groups [Depth[oG]\[Equal]3] *)
aux2=If[Depth[oG]==3,Weights[oG,oRep],If[oRepU1s==={},WeightsMod[oG,{oRepNonU1s,1}],WeightsMod[oG[[Flatten[Position[oG,x_/;!(x==={}),{1},Heads->False]]]],{oRepNonU1s,oRepU1s,1}]]];

If[newGU1s==={},
weights={(projectionMatrixNonU1s.Flatten[#[[1;;-2]]]),{},#[[-1]]}&/@aux2;
,
weights={(projectionMatrixNonU1s.Flatten[#[[1;;-2]]]),(projectionMatrixU1s.Flatten[#[[1;;-2]]]),#[[-1]]}&/@aux2;
];

(* Work only with weights with no negative coefficients [only these can be Dynkin indices] *)
weights=DeleteCases[weights,x_/;x[[1]]=!=Abs[x[[1]]]];

];
(* [--------------------OPERATION SPEED UP 1--------------------] End *)

result={};

 (* [START] This code computes a function [conjugacyClassFunction] which allows to separate the weights in different classes, speeding up the calculation *) 
idx=1;
res={};
Do[
If[g=!=U1,
genericRepresentation=vr\[UnderBracket]aux[#]&/@Range[idx,idx+Length[g]-1];
idx=idx+Length[g];
resTemp=ConjugacyClass[g,genericRepresentation];
,
resTemp={vr\[UnderBracket]aux[idx]};
idx=idx+1;
];
res=Join[res,resTemp];

,{g,Join[newGNonU1s,newGU1s]}];

conjugacyClassFunction=(res/.vr\[UnderBracket]aux[iii_]:>#[[iii]])&;
 (* [END] This code computes a function [conjugacyClassFunction] which allows to separate the weights in different classes, speeding up the calculation *)


(* Separate the weights according to their conjugacy class to speed up the calculation *)
weightsGroups=Gather[weights,conjugacyClassFunction[Join[#1[[1]],#1[[2]]]]==conjugacyClassFunction[Join[#2[[1]],#2[[2]]]]&]; 

(* Sort weights in a descending fashion *)
weightsGroups=SortWeights[newGNonU1s,#]&/@weightsGroups;

completeResult={};
result=Flatten[Reap[
Do[
While[Length[weights]>0,
aux=Table[weights[[1,1,limits[[i]];;limits[[i+1]]-1]],{i,Length[newGNonU1s]}];
Sow[ConstantArray[{aux,weights[[1,2]]},weights[[1,-1]]]];
weights=RemoveWeights[Simplify[weights],Simplify[WeightsModDominants[newGNonU1s,weights[[1]]]]];
weights=SortWeights[newGNonU1s,weights];
];
,{weights,weightsGroups}]][[2]],2];

completeResult=Join[completeResult,Simplify[result]];

Return[completeResult];
]

(* This is a function that speeds up the calculation of Decompose reps when a) there are no U(1)s in the group and subgroup and b) there is no rank reduction between group and subgroup. So, to simplify, for now this speed up is triggered only when both group and subgroup are simple groups with the same rank. *)
(*
First, a list of all subgroup representations smaller or equal in size to the originalRepresentation are computed. With the inverse projection matrix one finds the corresponding weights of group. Then, with the DominantConjugate conjugate method one can find the multiplicity of those weight in the original representation of group.
*)
SpeedUp1\[UnderBracket]DecomposeReps[groupSimple_,subgroupSimple_,repOfGroup_,inverseProjectionMatrix_]:=Module[{aux,groupDominantWeights,subgroupDomWeightsOfInterest,result,weightMultiplicity},

aux=RepsUpToDimN[subgroupSimple,DimR[groupSimple,repOfGroup],SortResult->False];
subgroupDomWeightsOfInterest=DeleteCases[aux,x_/;!ArrayQ[Simplify[inverseProjectionMatrix.x],_,IntegerQ]];

aux=DominantConjugate[groupSimple,#][[1]]&/@(Simplify[inverseProjectionMatrix.#]&/@subgroupDomWeightsOfInterest);
groupDominantWeights=DominantWeights[groupSimple,repOfGroup];
weightMultiplicity=Cases[groupDominantWeights,x_/;x[[1]]==#:>x[[2]],1,1]&/@aux;

aux=DeleteCases[MapThread[List,{subgroupDomWeightsOfInterest,weightMultiplicity}],x_/;Length[x[[2]]]==0];
result={#[[1]],{},#[[2,1]]}&/@aux;

Return[result];
]

(* Input to this method: cms={cm1,cm2,...}; repTogether={simpleRepsMerged,<U1repsmerged if any>,degeneracy} *)
(* This method outputs the weights of such a group/rep *)
WeightsMod[cms_,repTogether_]:=Module[{aux,aux1,aux2,aux3,dims},
dims=Length/@cms;
aux1={};
aux2=1;

Do[
AppendTo[aux1,repTogether[[1,aux2;;aux2+dims[[i]]-1]]];
aux2=aux2+dims[[i]];
,{i,Length[cms]}];

aux3=Flatten[Reap[Do[
Sow[Weights[cms[[i]],aux1[[i]]]];
,{i,Length[cms]}]][[2]],1];
aux3=Tuples[aux3];

(* "Repair" elements *)
If[Length[repTogether]==2,
aux3={#[[All,1]]//Flatten,repTogether[[-1]]Times@@#[[All,2]]}&/@aux3;
,
aux3={#[[All,1]]//Flatten,repTogether[[2]],repTogether[[-1]]Times@@#[[All,2]]}&/@aux3;
];

Return[aux3];
]

WeightsModDominants[cms_,repTogether_]:=Module[{aux,aux1,aux2,aux3,dims},
dims=Length/@cms;
aux1={};
aux2=1;
Do[
AppendTo[aux1,repTogether[[1,aux2;;aux2+dims[[i]]-1]]];
aux2=aux2+dims[[i]];
,{i,Length[cms]}];

aux3={};
Do[

AppendTo[aux3,DominantWeights[cms[[i]],aux1[[i]]]];
,{i,Length[cms]}];

aux3=Tuples[aux3];

(* "Repair" elements *)
Do[
If[Length[repTogether]==2,
aux3[[i]]={aux3[[i,All,1]]//Flatten,repTogether[[-1]]Times@@aux3[[i,All,2]]},
aux3[[i]]={aux3[[i,All,1]]//Flatten,repTogether[[2]],repTogether[[-1]]Times@@aux3[[i,All,2]]}
];
,{i,Length[aux3]}];


Return[aux3];
]

DimRMod[cms_,repTogether_]:=Module[{aux,aux1,aux2,aux3,dims},
dims=Length/@cms;
aux1={};
aux2=1;
Do[
AppendTo[aux1,DimR[cms[[i]],repTogether[[aux2;;aux2+dims[[i]]-1]]]];
aux2=aux2+dims[[i]];
,{i,Length[cms]}];

Return[Times@@aux1];
]



SortWeights[cms_,weights_]:=Module[{bigCmInv,condensedWeights,aux,aux2},
bigCmInv=Transpose[Inverse[BlockDiagonalMatrix[cms]]];
condensedWeights=Gather[weights,#1[[{1,2}]]===#2[[{1,2}]]&];
condensedWeights=Table[{condensedWeights[[i,1,1]],condensedWeights[[i,1,2]],Total[condensedWeights[[i,All,-1]]]},{i,Length[condensedWeights]}];

condensedWeights={#,bigCmInv.(#[[1]])}&/@condensedWeights;
aux=Sort[condensedWeights,OrderedQ[{#2[[2]],#1[[2]]}]&][[All,1]];
Return[aux];
];

RemoveWeights[mainList_,toRemoveList_]:=Module[{aux,nU1s,nNonU1s,mainListMod,toRemoveListMod,pos},
aux=mainList;
mainListMod=mainList;
toRemoveListMod=toRemoveList;

(* There are U1's mixed in ... merge the U1 information with the simple groups part *)
nU1s=Length[aux[[1,2]]];
nNonU1s=Length[aux[[1,1]]];
If[Length[aux[[1]]]==3,
aux={Join[#[[1]],#[[2]]],#[[3]]}&/@aux;
mainListMod={Join[#[[1]],#[[2]]],#[[3]]}&/@mainListMod;
toRemoveListMod={Join[#[[1]],#[[2]]],#[[3]]}&/@toRemoveListMod;
];

Do[
pos=Position[mainListMod,toRemoveListMod[[i,1]]][[1,1]];
aux[[pos,2]]=aux[[pos,2]]-toRemoveListMod[[i,2]];
,{i,Length[toRemoveListMod]}];

aux=DeleteCases[aux,x_/;x[[2]]==0];

(* If there are U1s ... unmerge the U1/simple group data *)
aux={#[[1,1;;nNonU1s]],#[[1,nNonU1s+1;;-1]],#[[2]]}&/@aux;

Return[aux];
]


(* ::Input::Initialization:: *)
EFH\[UnderBracket]OfExtraDotOfRegularSubAlgebra[simpleGroup_,repMatrices_]:=Module[{mE,mF,mH,combination,weight,cmInv,matD,cmID,newRootSize,posNonZero},

combination=FindAdjointDecompositionInSimpleRoots[simpleGroup];

(* Get mE, mF up to a normalization factor to be fixed at the end *)
mE=repMatrices[[combination[[1]],2]];

Do[
mE=SimplifySA[repMatrices[[el,2]].mE-mE.repMatrices[[el,2]]];
,{el,combination[[2;;-1]]}];

mF=Transpose[mE];


(* Get mH *)
weight=-Adjoint[simpleGroup];
cmInv=Inverse[simpleGroup];matD=MatrixD[simpleGroup];cmID=cmInv.matD;
newRootSize=SimpleProduct[weight,weight,cmID]/SimpleProduct[simpleGroup[[1]],simpleGroup[[1]],cmID](MatrixD[\!\(\*
TagBox["simpleGroup",
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\)][[1,1]]);
mH=-Diagonal[MatrixD[simpleGroup]][[combination]].repMatrices[[combination,3]]/newRootSize;

(* Finaly, normalize correctly mE and mF *)
posNonZero=Cases[ArrayRules[mE.mF-mF.mE][[1;;-2]],x_/;x[[2]]!=0,{1},1];
If[Length[posNonZero]>0, (* otherwise ... the mE.mF-mF.mE is null and nothing else needs to be done *)
posNonZero=posNonZero[[1,1]];
mE=Sqrt[Extract[mH,posNonZero]/Extract[mE.mF-mF.mE,posNonZero]]mE;
mF=Transpose[mE];
];

Return[SimplifySA/@{mE,mF,mH}];
]

(* Finds the sequence of simple roots needed to add to form the adjoint weight \[CapitalLambda]. The output is {s(1), s(2),...,s(n)} such that the series Subscript[\[Alpha], s(1)],Subscript[\[Alpha], s(1)]+Subscript[\[Alpha], s(2)],Subscript[\[Alpha], s(1)]+Subscript[\[Alpha], s(2)]+Subscript[\[Alpha], s(3)],... is some sequence of weights which ends with \[CapitalLambda]. *)
FindAdjointDecompositionInSimpleRoots[group_]:=Module[{weights,weightNow,idx,sequence,continue,i,pos},
weights=Weights[group,Adjoint[group]][[All,1]];
idx=1;
weightNow=0group[[1]];
sequence={};

While[idx=!=Length[weights],
continue=True;
i=1;
pos={};
While[Length[pos]==0,
pos=Position[weights[[1;;-1]],weightNow-group[[i]]];
(* Print[i,"  ",weightNow,"  ",weightNow-group[[i]],"  ",pos]; *)
i++;
];
idx=pos[[1,1]];
weightNow=weightNow-group[[i-1]];
AppendTo[sequence,i-1];
];
Return[sequence];

];

(*
Input example: RegularSubgroupInfo[{U1,SO10,U1},{X1,{1,0,0,0,0},X2},{SU4,SU2,U1},{{2,{-3,2,1}},{2,{4}},{C1,C2,C3}}];
The function computes the U1's that correspond to dots that were excluded [this is essentially the maximum list of U1s that could survive symmetry breaking for the given simple subgroups], and so for each surviving U1 the linear combinations of those U1s must be given.
*)

regularsubgroupinfo::numberOfU1s="There is a total of `1` remnant U(1)'s inside the original group (in addition to the provided simple subgroups).
Make sure that all user-defined unbroken U(1) gauge factors are  a linear combination of these U(1)'s (in other words, each must be specified as an `1`-dimensional list/vector).";

RegularSubgroupInfo[group_,rep_,subgroup_,dotsComposition_]:=Module[{positionU1s,positionNonU1s,matricesGroup,matricesGroupPositions,matricesSubgroup,tempMatrices,dot,extractMatricesPos,u1Combination,aux,aux2,aux3,aux4,missingDots,discardedGenerators,projectionMatrix,dotPositions,nO,tempProjection,availableU1GeneratorsLC,availableU1Generators,extDots,groupMod,combination,minus\[CapitalLambda],cmInv,matD,cmID,newRootSize,groupI,startP,endP,indicesOfRootsOfFactorGroups,subgroupU1sDotPos},
positionU1s=Flatten[Position[subgroup,U1]];
positionNonU1s=Complement[Range[Length[subgroup]],positionU1s];

matricesGroup=Flatten[RepMinimalMatrices[group,rep],2];
(* matricesGroup=InverseFlatten[matricesGroup,{Length[matricesGroup]/3,3}]; *)

matricesGroupPositions=If[Length[#]==0,1,3Length[#]]&/@group;
matricesGroupPositions=Accumulate[matricesGroupPositions]-matricesGroupPositions;

dotPositions=If[Length[#]==0,1,Length[#]]&/@group;
dotPositions=Accumulate[dotPositions]-dotPositions;

nO=Total[Max[Length[#],1]&/@group];

(* ------------- Compute the available U(1)'s generators ------------- *)
aux=Flatten[Table[{dotsComposition[[el,1]],#}&/@dotsComposition[[el,2]],{el,positionNonU1s}],1];
(* aux=DeleteDuplicates[DeleteCases[aux,x_/;x[[2]]<0]]; *)

(* aux=Join[dotsCompletelyRemoved,aux];Print[aux]; *)
missingDots=Complement[Flatten[Table[{i,j},{i,Length[group]},{j,Length[group[[i]]]}],1],Abs[aux]];


aux={#[[1,1]],Sort[#[[All,2]]]}&/@Gather[aux,#1[[1]]==#2[[1]]&];
aux=Sort[Join[aux,{#,{}}&/@Complement[Range[Length[group]],aux[[All,1]],Flatten[Position[group,U1]]]]];

(* [START] This code computes the potential linear combinations of U(1)s which can be factored out of the original group and are not part of the simple subgroups *)
aux2={};
Do[
If[el[[2]]=!={},

extDots=Abs[Cases[el[[2]],x_/;x<0]];
groupMod=group[[el[[1]]]];

If[Length[extDots]>0, (* If the diagram is extended, find the nullspace of the extended diagram *)
groupMod[[extDots[[1]]]]=-Adjoint[group[[el[[1]]]]];
];
aux3=NullSpace[groupMod[[Abs[el[[2]]]]]];
,
aux3=IdentityMatrix[Length[group[[el[[1]]]]]];
];

If[Length[aux3]>0,
AppendTo[aux2,PadRight[Join[ConstantArray[0,dotPositions[[el[[1]]]]],#],nO]&/@(aux3)];
];
,{el,aux}];

aux2=Join[Flatten[aux2,1],UnitVector[nO,#]&/@(dotPositions[[Flatten[Position[group,U1]]]]+1)];
(* [END] This code computes the potential linear combinations of U(1)s which can be factored out of the original group and are not part of the simple subgroups *)


(* At this point, aux2 contains the linear combinations of the roots which yield valid U(1)s that will commute with the {e,f,h} triples of the preserved dots. [Update] To be precise, it contains the linear combinations of the Subscript[\[Alpha], i]/<Subscript[\[Alpha], i],Subscript[\[Alpha], i]>. *)

aux3=Table[If[group[[gI]]===U1,matricesGroup[[{matricesGroupPositions[[gI]]+1}]],matricesGroup[[matricesGroupPositions[[gI]]+3Range[Length[group[[gI]]]]]]],{gI,Length[group]}];
aux3=Flatten[aux3,1];

availableU1GeneratorsLC=aux2;
availableU1Generators=If[aux2=!={},SimplifySA/@(aux2.aux3),{}];

matricesSubgroup={};
projectionMatrix={};
Do[
tempMatrices={};
If[subgroup[[elI]]=!=U1,
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX non U1s XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Do[
dot=dotsComposition[[elI,2,dotI]];

If[dot>0,
extractMatricesPos=matricesGroupPositions[[dotsComposition[[elI,1]]]]+3(dot-1)+{1,2,3};

AppendTo[tempMatrices,matricesGroup[[extractMatricesPos]]];
AppendTo[projectionMatrix,UnitVector[nO,dotPositions[[dotsComposition[[elI,1]]]]+dot]];
,
extractMatricesPos=matricesGroupPositions[[dotsComposition[[elI,1]]]];
aux=matricesGroup[[1+extractMatricesPos;;extractMatricesPos+3Length[group[[dotsComposition[[elI,1]]]]]]];
aux=InverseFlatten[aux,{Length[group[[dotsComposition[[elI,1]]]]],3}];

AppendTo[tempMatrices,EFH\[UnderBracket]OfExtraDotOfRegularSubAlgebra[group[[dotsComposition[[elI,1]]]],aux]];
combination=Table[-Count[dotPositions[[dotsComposition[[elI,1]]]]+FindAdjointDecompositionInSimpleRoots[group[[dotsComposition[[elI,1]]]]],i],{i,nO}];

(* AppendTo[projectionMatrix,aux]; INCORRECT - below is the correct code *)
groupI=group[[dotsComposition[[elI,1]]]];
minus\[CapitalLambda]=-Adjoint[groupI];
cmInv=Inverse[groupI];matD=MatrixD[groupI];cmID=cmInv.matD;
newRootSize=SimpleProduct[minus\[CapitalLambda],minus\[CapitalLambda],cmID]/SimpleProduct[groupI[[1]],groupI[[1]],cmID](matD[[1,1]]);
aux=PadRight[Join[ConstantArray[1,dotPositions[[dotsComposition[[elI,1]]]]],Diagonal[matD]],nO];
combination=combination  aux/newRootSize;

AppendTo[projectionMatrix,combination];
(* [END] AppendTo[projectionMatrix,aux]; INCORRECT - below is the correct code *)
];

,{dotI,Length[dotsComposition[[elI,2]]]}];
AppendTo[matricesSubgroup,tempMatrices];

,
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX U1s XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
If[Length[availableU1GeneratorsLC]!=Length[dotsComposition[[elI]]],
Message[regularsubgroupinfo::numberOfU1s,Length[availableU1GeneratorsLC]];
];
AppendTo[matricesSubgroup,{{SimplifySA[dotsComposition[[elI]].availableU1Generators]}}];
AppendTo[projectionMatrix,dotsComposition[[elI]].availableU1GeneratorsLC]; 
];

,{elI,Length[dotsComposition]}];

(* XXXXXXXXXXXXXXXXXXXXXXXXXX What were the discarded generators? XXXXXXXXXXXXXXXXXXXXXXXXXX *)
aux=Flatten[Table[{dotsComposition[[el,1]],#}&/@dotsComposition[[el,2]],{el,positionNonU1s}],1];
aux=DeleteDuplicates[DeleteCases[aux,x_/;x[[2]]==0]];
missingDots=Complement[Flatten[Table[{i,j},{i,Length[group]},{j,Length[group[[i]]]}],1],aux];

aux={#[[1,1]],Sort[#[[All,2]]]}&/@Gather[aux,#1[[1]]==#2[[1]]&];

(* Out of caution, assume that that there are no U(1)'s and so these correspond to missing generators as well *)
discardedGenerators=Table[If[group[[el[[1]]]]===U1,{},matricesGroup[[matricesGroupPositions[[el[[1]]]]+3(el[[2]]-1)+{1}]]],{el,missingDots}];
discardedGenerators=Join[availableU1Generators,Flatten[discardedGenerators,1]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXX STATUS AT THIS POINT XXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* At this point it has been calculated...;
--------;
For U1s: each line of 'projectionMatrix' corresponds to the linear combination of the Subscript[h, i] (and maybe involving also 2 Subscript[h, -\[CapitalLambda]]/<\[CapitalLambda],\[CapitalLambda]>) which is associated to the U1 factor. 'matricesSubgroup' contains the corresponding linear combination of the Subscript[h, i] (and maybe involving also 2 Subscript[h, -\[CapitalLambda]]/<\[CapitalLambda],\[CapitalLambda]>);
--------;
For non-U1s: each line of 'projectionMatrix' corresponds to the preserved Subscript[\[Alpha], i], or combination of the Subscript[\[Alpha], i]'s if the subgroup involves the extended Dynkin diagram. If the extended Dynkin diagram dot is not involved, this is the same as the preseved Subscript[\[Alpha], i]/<Subscript[\[Alpha], i],Subscript[\[Alpha], i]> otherwhise it is not the same. 'matricesSubgroup' contains the correct combination of the Subscript[\[Alpha], i]/<Subscript[\[Alpha], i],Subscript[\[Alpha], i]>, since this correction is adequately performed in the function EFH\[UnderBracket]OfExtraDotOfRegularSubAlgebra (which returns the Subscript[e, i],Subscript[f, i],Subscript[h, i] associated to the extended dot);

A further problem is related to what happens to the normalization of the simple roots which are preserved: this normalization does not change, which may be a problem. Consider for example SP4 \[Rule] SU2 where the second dot of SP4 is preserved. Since SP4's <Subscript[\[Alpha], 2],Subscript[\[Alpha], 2]> = 2 by the function MatrixD, we may have a problem as in SU2, <Subscript[\[Alpha], 1],Subscript[\[Alpha], 1]> = 1 by the function MatrixD.;
--------;
There a then two (potential) problems;

A-For the extend Dynkin diagram dot, the projection matrix line must be corrected;
B-Chaining the use of the 'matricesSubgroup' with other functions might be a problem, given that the normalization of the subgroup simple roots is not cannonical. EVERYWHERE MatrixD is used must be looked at carefully in these cases (ratios MatrixD(...)/MatrixD(...) are ok though).
 *)

(* 25/Feb/2015 UPDATE: the newer code (pre-25/Feb/2015) has already been changed so that line of 'projectionMatrix' corresponds to the preserved Subscript[\[Alpha], i]/<Subscript[\[Alpha], i],Subscript[\[Alpha], i]> or combination of the Subscript[\[Alpha], i]/<Subscript[\[Alpha], i],Subscript[\[Alpha], i]> of the original group *)


Return[{matricesSubgroup,discardedGenerators,projectionMatrix}];
]




(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This is inspired on BreakRep from SSB.m. The difference is that the subreps are known. Also, this function is to be used to speed up the Invariants function *)
(* The output is {list of irreps of the subgroup,W} such that Inverse[W].<original group matrices combination I>.W=<subgroup matrix I>. Note that W is not unitary in general. The invariants Inv^abc obtained with <subgroup matrices> can be corrected to <original group matrices> as Inv^abc \[Rule] Inv^a'b'c' Inverse[W]a'a Inverse[W]b'b Inverse[W]c'c  *)
(* UPDATE: W in the output is now unitary *)

(* Input is the original 'group', the 'subgroup', the 'projectionMatrix', the group's rep to break 'repToBreak', and a list 'preservedGenerators' of the unbroken generators of 'group' corresponding to the ***minimal generators*** of 'subgroup'. As such, 'preservedGenerators'={sg1,sg2,...} where sgI={simpleRoot1gens,simpleRoot2gens, ...} for each factor group in 'subgroup', and with simpleRootJgens={Ej,Fj,Hj} for each simple root in the factor sgI. *)
BreakRepIntoSubgroupIrreps[group_,subgroup_,projectionMatrix_,repToBreak_,preservedGenerators_]:=Module[{repMatrices1, listOfIrreps,aux,aux2,aux3,nInvs,count,linearCombinations,irreps,timeU,counter,printedInfo,diagMatsPositions,relevantComponents,relevantRows,nAs,nBs,vrs,cfs,unitaringTransformation},

repMatrices1=SimplifySA/@Flatten[preservedGenerators,2];

diagMatsPositions=(Cases[ArrayRules[#][[1;;-2]],x_/;(x[[2]]=!=0&&x[[1,1]]=!=x[[1,2]])]==={})&/@repMatrices1;
diagMatsPositions=Flatten[Position[diagMatsPositions,True],1];

listOfIrreps=Tally[DecomposeRep[group,repToBreak,subgroup,projectionMatrix]][[All,1]];

count=0;
linearCombinations={};
irreps={};

counter=0;
(* printedInfo=PrintTemporary[Dynamic[Row[{"Total states rotated so far: ",count,"/",DimR[bigGroup,repToBreak]},""]]]; *)
Do[
aux=Flatten[RepMinimalMatrices[subgroup,listOfIrreps[[irrepIndex]]],2];
aux3=Transpose[Diagonal/@repMatrices1[[diagMatsPositions]]]//Normal;
aux2=DeleteDuplicates[Transpose[Diagonal/@aux[[diagMatsPositions]]]];

relevantComponents=DeleteDuplicates[Flatten[Position[aux3,x_/;MemberQ[aux2,x]]]];
relevantRows=DeleteDuplicates[ArrayRules[repMatrices1[[All,All,relevantComponents]]][[1;;-2,1,2]]];
relevantComponents=DeleteDuplicates[Join[relevantComponents,relevantRows]];

aux2=InvariantsSuperFreeFormMod[repMatrices1[[All,relevantComponents,relevantComponents]],SimplifySA/@aux,True]; 
nInvs=Length[aux2];
(* There are for sure these irreps *)


(* START - Unitarization of invariants *)
(* The idea here is to make sure that the change of basis matrix will be unitary. To do this, if there is more than one subgroup irrep X (X, X',...) in the representation to be rotation, then the states corresponding to X, X', ... must be orthogonal. To make this precise, consider that {Subscript[v, \[Alpha]1],Subscript[v, \[Alpha]2],...,Subscript[v, \[Alpha]m]} \[Alpha]=1 to n are the n m-dimensional irreps. The Subscript[v, \[Alpha]i] encode the combinations of the components of the reducible representations which make up the i component of the \[Alpha] irreducible representation. We need to make a transformation B such that Subscript[w, i\[Alpha]]=Subscript[B, \[Alpha]\[Beta]]Subscript[v, i\[Beta]] are orthonormalized vectors, ie Subscript[w, i\[Alpha]].Subscript[w, j\[Beta]]=Subscript[\[Delta], ij]Subscript[\[Delta], \[Alpha]\[Beta]]. Given that B only operates on the \[Alpha] space, the orthonormality of the Subscript[w, i\[Alpha]] for a given \[Alpha] is taken care of automatically by the group/irrep structure under consideration. And as such, we can take i=1 (for example), and consider just the orthogonalization of the vectors {Subscript[v, 11],Subscript[v, 21],...,Subscript[v, n1]} and extract B from there *)
nAs=Count[Variables[aux2],a[_]];
nBs=Count[Variables[aux2],b[_]];
vrs=Sort[Variables[aux2]];
cfs=CoefficientArrays[aux2,vrs][[3,All,1;;nAs,nAs+1]]; (* only need to take one b column *)

unitaringTransformation=Orthogonalize[cfs,Simplify[Conjugate[#1]. #2]&].PseudoInverse[cfs];
aux2=Expand[unitaringTransformation.aux2];
(* END - Unitarization of invariants *)


(* Separate the direct product of groups correctly *)
aux2=aux2 /.a[j_]:>a[relevantComponents[[j]]];
Do[
aux2[[j]]=aux2[[j]]/.b[j_]:>b[j+counter];
counter+=Length[aux[[1]]];
,{j,nInvs}];

 aux2=CoefficientArrays[#,Join[Array[a,Dimensions[repMatrices1][[-1]]],Array[b,Dimensions[repMatrices1][[-1]]]]][[3]]&/@aux2;
aux2=#[[1;;Dimensions[repMatrices1][[-1]],Dimensions[repMatrices1][[-1]]+1;;-1]]&/@aux2;

 aux2=SimplifySA[Total[aux2]]; 
AppendTo[linearCombinations,aux2];
AppendTo[irreps,Table[listOfIrreps[[irrepIndex]],{j,nInvs}]];

count+=nInvs Length[aux[[1]]];
,{irrepIndex,Length[listOfIrreps]}];

(* NotebookDelete[printedInfo]; *)
If[count==DimR[group,repToBreak],Null,Print["ERROR (BreakRepMod): Dimensions of the subrepresentations don't add up."]];

irreps=Flatten[irreps,1];
 (* linearCombinations=Flatten[linearCombinations,1]; *)

(* The conjugation takes care of the fact that we got this result from coefficients a,b *)
(* N's and RootApproximant are meant to simplify the expressions in a quick and accurate way. If problems arrise, change to Simplify *)

(* linearCombinations=RootApproximant[Chop[Conjugate[Transpose[#]]]]&/@N[linearCombinations]; *)
(* Make sure that the norm of the new states is the same as the old ones *)
(* linearCombinations=RootApproximant[#/Norm[#]]&/@N[linearCombinations]; *)

If[Total[Abs[N[Total[linearCombinations]].ConjugateTranspose[N[Total[linearCombinations]]]-IdentityMatrix[Length[Total[linearCombinations]]]],{2}]>10^-8,Print["ERROR (BreakRepMod): Rotation matrix is not unitary."]];
Return[{irreps,linearCombinations}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Uses RegularSubgroupInfo to provide the projection matrix of a regular embedding *)
RegularSubgroupProjectionMatrix[group_,subgroup_,dotsComposition_]:=Module[{aux,singlet},
singlet=If[IsSimpleGroupQ[group],ConstantArray[0,Length[group]],If[#===U1,0,ConstantArray[0,Length[#]]]&/@group];
Return[RegularSubgroupInfo[group,singlet,subgroup,dotsComposition][[3]]];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* This function outputs {<list>,<N-dimensional tensor>} where <list> = {<el1>,<el2>,...} where each <el> contains the positions of combinations of the representations which contain invariants. The resulting big N-dimensional tensor is the second ouput *)
GetAllNLinearInvariantsCombinations[group_,repsIn_,cjs_]:=Module[{n,singletState,reps,aux,aux2,aux3,invs,posNonU1s,resultTensor,dims,accDims,countInv},

n=Length[repsIn];

(* Conjugate the representations if necessary *)
reps=Table[If[cjs[[repsI]],ConjugateIrrep[group,#]&/@repsIn[[repsI]],repsIn[[repsI]]],{repsI,n}];

posNonU1s=Flatten[Position[group,x_/;x=!={},{1},Heads->False]];


If[Length[repsIn]===1,
singletState=If[#==={},0,#]&/@(ConstantArray[0,Length[#]]&/@group);
aux=Position[repsIn[[1]],singletState];
aux=Table[{auxI,{1,#}&/@auxI,1},{auxI,aux}];
,

aux=ReduceRepProduct[group,#]&/@Tuples[Map[ConjugateIrrep[group,#]&, reps[[1;;Ceiling[n/2]]],{2}]];
aux2=ReduceRepProduct[group,#]&/@Tuples[reps[[Ceiling[n/2]+1;;-1]]];

aux3=Intersection[DeleteDuplicates[Flatten[aux[[All,All,1]],1]],Flatten[aux2[[All,All,1]],1]];

(* This list is of the form {el_1,el_2,...} where each el_N={position in aux,position in aux2,multiplicity of invariant} *)
aux3={#[[1,1]],#[[2,1]],#[[1,2]]#[[2,2]]}&/@Flatten[Table[Tuples[{ {#[[1]],Extract[aux,(#+{0,0,1})]}&/@Position[aux,el],{#[[1]],Extract[aux2,(#+{0,0,1})]}&/@Position[aux2,el]}],{el,aux3}],1];
aux3=Sort[{#[[1,1;;2]],Total[#[[All,3]]]}&/@Gather[aux3,#1[[1;;2]]==#2[[1;;2]]&]];

aux=Tuples[Range[Length[#]]&/@reps[[1;;Ceiling[n/2]]]];
aux2=Tuples[Range[Length[#]]&/@reps[[Ceiling[n/2]+1;;-1]]];
aux={Join[aux[[#[[1,1]]]],aux2[[#[[1,2]]]]],#[[2]]}&/@aux3;
aux={#[[1]],Transpose[{Range[Length[reps]],#[[1]]}],#[[2]]}&/@aux;
];
(* At this point, aux={el_1,el_2,...} where el_N corresponds to a particular combination of fields which is/contains an invariant: el_N={pos_Format1,pos_Format2,nInvs} where pos_Format1={pos rep1, pos rep2, ...} contains the positions of the fields, os_Format2={{1,pos rep1}, {2, pos rep2}, ...} contains the positions of the fields in another formal [which is better for use with Extract], and nInvs is the number of invariants in that particular combination of fields *)

dims=Map[Times@@DimR[group,#]&,reps,{2}];
accDims=Accumulate[#]-#&/@dims;

(* ***************** *)
(* Work with the unconjugated representations from now on *)
reps=repsIn;
resultTensor={};
countInv=0;
Do[
invs=Invariants[group,Extract[reps,aux[[i,2]]],Conjugations->cjs,TensorForm->True][[1]];
aux2=ArrayRules[invs][[1;;-2]];
aux2[[All,1]]=(Join[{countInv},Extract[accDims,aux[[i,2]]]]+#)&/@aux2[[All,1]];
resultTensor=Join[resultTensor,aux2];
countInv+=Length[invs];
,{i,Length[aux]}];

resultTensor=If[countInv==0,{},SparseArray[resultTensor,Join[{countInv},Extract[accDims+dims,Table[{i,-1},{i,Length[reps]}]]]]];
Return[{aux,resultTensor}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* This is the end function which effective calculates trilinear invariants (and matching coefficients with particular subgroup embeddings which are determined in AuxiliarRegularDecompositionOfGroup) *)

Options[SubgroupEmbeddingCoefficients]={Conjugations->{},Verbose->False,StandardizeInvariants->True};

SubgroupEmbeddingCoefficients[group_,reps_,subgroup_,breakingInformation_,OptionsPattern[]]:=SubgroupEmbeddingCoefficients[group,reps,subgroup,breakingInformation]=Module[{regularSubgroupInfo,subreps,cjs,multilinearCombinations,gaugeRotInfo,aux,aux1,aux2,aux3,auxR1,auxR2,rotMatrices,rotatedInvariants,repM,validCombinationOfSubInvs,validCombinationsOfSubInvariants,finalResult,projectionMatrix,preservedGenerators,brokenGenerators,columnsOfInterest,counter,invariantsRotation,tmp},

If[OptionValue[Verbose],ReportData[0,0]];
tmp=TimeUsed[];

(* Option allows to conjugate the representations given as input. By default, no conjugation is done *)
cjs=If[OptionValue[Conjugations]==={},ConstantArray[False,Length[reps]],OptionValue[Conjugations]];

regularSubgroupInfo=RegularSubgroupInfo[group,#,subgroup,breakingInformation]&/@reps;
preservedGenerators=regularSubgroupInfo[[All,1]];
brokenGenerators=regularSubgroupInfo[[All,2]];
projectionMatrix=regularSubgroupInfo[[1,3]]; (* for output only *)

aux=Table[BreakRepIntoSubgroupIrreps[group,subgroup,projectionMatrix,reps[[i]],preservedGenerators[[i]]],{i,Length[reps]}];

subreps=aux[[All,1]];
aux2=GetAllNLinearInvariantsCombinations[subgroup,subreps,cjs];
multilinearCombinations=aux2[[1]]; (* for output only *)

If[OptionValue[Verbose],ReportData[1,TimeUsed[]-tmp]];
rotMatrices=Total/@aux[[All,2]];
rotMatrices=Table[If[cjs[[repI]],SimplifySA[-Conjugate[rotMatrices[[repI]]]],SimplifySA[rotMatrices[[repI]]]],{repI,Length[reps]}];


If[!MemberQ[ReduceRepProduct[group,Table[If[!cjs[[i]],reps[[i]],ConjugateIrrep[group,reps[[i]]]],{i,Length[reps]}]][[All,1]],reps[[1]]0,{1}],Return[{}]];
(* If[Length[aux2[[2]]]\[Equal]0,Return[{{},{subgroup,projectionMatrix,subreps,multilinearCombinations,{}}}]]; *)(* No invariants for sure --- TODO: add other output *)

(* ---------------- Rotate invariants ---------------- *)
rotatedInvariants=aux2[[2]];
Do[
rotatedInvariants=DotN[rotMatrices[[i]],rotatedInvariants,i+1];
,{i,Length[reps]}];
rotatedInvariants=SimplifySA[rotatedInvariants];
If[OptionValue[Verbose],ReportData[2,TimeUsed[]-tmp]];

(* ---------------- [END] Rotate invariants ---------------- *)

(* Get only the raising operators of the discarded dots in the Cartan diagram which were converted to U1s *)
repM=brokenGenerators;
repM=Table[If[cjs[[repI]],-Transpose/@repM[[repI]],repM[[repI]]],{repI,Length[reps]}];

If[OptionValue[Verbose],ReportData[3,TimeUsed[]-tmp]];

validCombinationsOfSubInvariants={};
Do[
AppendTo[validCombinationsOfSubInvariants,SimplifySA[Sum[DotN[repM[[j,i]],rotatedInvariants,j+1],{j,Length[reps]}]]];
,{i,Length[repM[[1]]]}]; 

If[OptionValue[Verbose],ReportData[4,TimeUsed[]-tmp]];
validCombinationsOfSubInvariants=SparseArray[validCombinationsOfSubInvariants];
If[OptionValue[Verbose],ReportData[5,TimeUsed[]-tmp]];
validCombinationsOfSubInvariants=Flatten[validCombinationsOfSubInvariants,{{2},Join[{1},2+Range[Length[reps]]]}];
If[OptionValue[Verbose],ReportData[6,TimeUsed[]-tmp]];
validCombinationsOfSubInvariants=NullSpace2T[validCombinationsOfSubInvariants,500];
If[OptionValue[Verbose],ReportData[7,TimeUsed[]-tmp]];


finalResult=SparseArray[validCombinationsOfSubInvariants,Dimensions[validCombinationsOfSubInvariants]].rotatedInvariants;
If[OptionValue[Verbose],ReportData[8,TimeUsed[]-tmp]];
aux=Sqrt[Sqrt[Times@@Flatten[DimR[group,#]&/@reps]]/Simplify[Total[#,Length[reps]]&/@SimplifySA[Abs[SimplifySA[finalResult^2]]]]];
finalResult=SimplifySA[aux finalResult];
validCombinationsOfSubInvariants=Simplify[aux validCombinationsOfSubInvariants];

If[OptionValue[Verbose],ReportData[9,TimeUsed[]-tmp]];

(* This block of code ensures that the implied invariants of the big/original group are as given by the Invariants function *)
If[OptionValue[StandardizeInvariants],

(* Look at the non-canonical invariants (only at a minimum of the full tensors) *)
aux1=Flatten[finalResult,{{1},Range[2,Length[reps]+1]}];
aux2=ArrayRules[aux1][[1;;-2]];

columnsOfInterest={};
counter=0;
While[Length[columnsOfInterest]<Length[aux1]&&counter<Length[aux1[[1]]],
counter++;
aux3=Append[columnsOfInterest,aux2[[counter,1,2]]];
If[MatrixRank[aux1[[All,aux3]]]>MatrixRank[aux1[[All,columnsOfInterest]]],
AppendTo[columnsOfInterest,aux2[[counter,1,2]]]];
];

auxR2=aux1[[All,columnsOfInterest]];
(* [END] Look at the non-canonical invariants (only at a minimum of the full tensors) *)

(* Extract the canonical invariants from the Invariants function *)
finalResult=Invariants[group,reps,Conjugations->cjs,TensorForm->True][[1]];
aux1=Flatten[finalResult,{{1},Range[2,Length[reps]+1]}];
auxR1=aux1[[All,columnsOfInterest]];
(* [END] Extract the invariants from the Invariants function *)

invariantsRotation=SimplifySA[auxR1.Inverse[auxR2]];
validCombinationsOfSubInvariants=Simplify[invariantsRotation.validCombinationsOfSubInvariants];
];


If[OptionValue[Verbose],ReportData[10,TimeUsed[]-tmp]];

Return[{{finalResult,rotMatrices},{{group,subgroup},projectionMatrix,subreps,multilinearCombinations,validCombinationsOfSubInvariants}}];
]


(* ::Input::Initialization:: *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Computes the list of adjoint matrices given a group cm and a representation rep *)

Dec[cm_,rep_]:=Module[{mats,res},
mats=RepMatrices[cm,rep];

res=Table[Simplify[  Tr[(mats[[i]].mats[[j]]-mats[[j]].mats[[i]]).mats[[comp]]] Length[mats]/(Length[mats[[1]]] Casimir[cm,rep]) ],{i,1,Length[mats]} ,{comp,1,Length[mats]},{j,1,Length[mats]} ];
Return[SparseArray[#,{Length[mats],Length[mats]}]&/@res];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Free form of the Dec method: calculates the adjoint representation matrices given the matrices of a representation *)

DecFree[mats_]:=Module[{mats2,mats3,bMat,aux,res,n},
n=Length[mats];
mats2=SparseArray[mats];
mats3=Transpose[mats2,{2,1,3}];

bMat=Inverse[ListContract[mats3.mats3,{{1,4}}]];
bMat=SimplifySA[bMat];

aux=Transpose[ListContract[mats3.mats3.mats3,{{1,5}}],{1,3,2}];
aux=aux-Transpose[aux,{2,1,3}];
res=Transpose[bMat.Transpose[aux,{2,1,3}],{2,1,3}];
res=SimplifySA[res];
Return[res];
]

CheckDec[mats_]:=Module[{aux},
aux=DecFree[mats];
Return[Simplify[Table[mats[[i]].mats[[j]]-mats[[j]].mats[[i]]-  Sum[aux[[i,k,j]]mats[[k]],{k,Length[mats]}],{i,Length[mats]},{j,Length[mats]}] //Normal]];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
GaugeRepDirectProduct[cms_]:=BlockDiagonal3Tensor[GaugeRep/@cms]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Traces[mats_]:=Table[Simplify[Tr[mats[[i]].mats[[j]]]],{i,Length[mats]},{j,Length[mats]}]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Casimir[mats_]:=Simplify[Sum[mats[[i]].mats[[i]],{i,Length[mats]}]]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

IdentifyGroup[dimCas_]:=Module[{result,aux,n},
(*U(1)*)
If[dimCas=={1,0},Return[{}]]; (* Ill consider this to be U(1)'s Cartan matrix *)


(*Exceptionals*)
result=Switch[dimCas,{14,4},G2,{52,9},F4,{78,12},E6,{133,18},E7,{248,30},E8,_,Null];
If[!(result===Null),Return[result]];

(*SU(n)*)
aux=Solve[{n^2-1,n}==dimCas,n];
aux=Cases[n/.aux,x_/;x>=2&&IntegerQ[x]];
If[Length[aux]!=0,
Return[CartanMatrix["SU",aux[[1]]]];
];

(*SO(n)*)
aux=Solve[{1/2(n^2-n),n-2}==dimCas,n];
aux=Cases[n/.aux,x_/;x>=5&&IntegerQ[x]];
If[Length[aux]!=0,
Return[CartanMatrix["SO",aux[[1]]]];
];

(*SP(2n)*)
aux=Solve[{2n^2+n,2n+2}==dimCas,n];
aux=Cases[n/.aux,x_/;x>=3&&IntegerQ[x]];
If[Length[aux]!=0,
Return[CartanMatrix["SP",2aux[[1]]]];
];

Return["Unknown group"];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

IdentifyGroupFF[mats_]:=Module[{aux},
If[Length[mats]==1,Return[{}]];
aux=DecFree[mats];
aux=Sum[aux[[i,1]].aux[[i,1;;-1,1]],{i,Length[aux]}];
Return[IdentifyGroup[{Length[mats],aux}]];
]

IdentifyGroupNameFF[mats_]:=Module[{aux},
If[Length[mats]==1,Return["U1"]];
aux=DecFree[mats];
aux=Sum[aux[[i]].aux[[i]],{i,Length[aux]}];
Return[IdentifyGroupName[{Length[mats],aux[[1,1]]}]];
]
