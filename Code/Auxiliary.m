(* ::Package:: *)

(* ::Input::Initialization:: *)
Sum2List[x_Plus]:=List@@x
Sum2List[x:Except[Plus]]:=List@x
Prod2List[x_]:=Flatten[{x}/.{Power[b_,n_Integer]:>ConstantArray[b,n],Times->List}]

Identityfunc[x_]:=Switch[Expand[x],_Plus,Expand[1/2 (2 #1&)/@Expand[x]],_,Expand[x]]
FactorSplit[exp_,crit_]:=FactorSplit[crit][exp]
FactorSplit[crit_]:=Merge[{Times@@@GroupBy[Prod2List[#],crit],<|True->1,False->1|>},Apply[Times]]&

LinSolve[basis_]:=Module[{q,r},
{q,r}=QRDecomposition[basis\[Transpose]];
Transpose[Inverse[r].q]//Simplify
]
parsePart[parts_,n_]:=Module[{rest=Complement[Range[n],Union@Flatten[parts]]},
If[rest=={},Return[parts],
If[Length[parts]==1,
Return[Append[parts,rest]],
Return[Join[parts,List/@rest]]
]
]
];
(* Find the coefficient list of an expression (e.g. an amplitude) in STANDARD FORM. *)
FindCor::basis="non-standard expression `1` or incomplete basis `2`";
FindCor[exp_,stBasis_]:=Module[{termlist,B,pos,cor},
(* Amp: the expression (may not be an amplitude,
StBasis: the standard basis (monomials). *)
cor=ConstantArray[0,Length[stBasis]];
termlist=Sum2List[Expand[exp]];
If[termlist=={0},Return[cor]];
termlist=FactorSplit[NumericQ]/@termlist;
B=FactorSplit[NumericQ]/@stBasis;
Do[pos=FirstPosition[Through[B[False]],term[False]];
If[MissingQ[pos],Message[FindCor::basis,Amp,StBasis];Abort[],
pos=pos[[1]] (* first level index *)];
If[KeyExistsQ[term,True],cor[[pos]]=term[True],cor[[pos]]=1];
If[KeyExistsQ[B[[pos]],True],cor[[pos]]/=B[[pos]][True]],
{term,termlist}];

Return[cor]
]
FindCor[StBasis_]:=FindCor[#,StBasis]&

unflatten[e_,{d__?(IntegerQ[#1]&&Positive[#1]&)}]:=Fold[Partition,e,Take[{d},{-1,2,-1}]]/;Length[e]===Times[d]

(* Select a complete basis from a list of vectors *)
basisReduce[subspace_]:=Module[{subbasis,len=Length[subspace],lmax,iter=1,pos=1,poslist={}},
If[len>0,lmax=Length[subspace[[1]]],Return[{}]];
If[!MatrixQ[subspace,NumericQ],Message[basisReduce::input,subspace],subbasis=subspace];
While[iter<=len&&iter<=lmax,
Switch[MatrixRank[subbasis[[;;iter]]],
iter,iter++;AppendTo[poslist,pos],
iter-1,subbasis=Delete[subbasis,iter];len--
];
pos++];
<|"basis"->If[lmax<len,subbasis[[;;lmax]],subbasis],"pos"-> poslist|>
]
basisReduce::input="wrong input matrix: `1`";

Options[basisReducePro]={TargetDim->Null,ShowProgress->False,Tolerance->10^-10};
basisReducePro[prebasis_,f_,OptionsPattern[]]:=Module[{tensorValue={},mtensor={},poslist={},metric={{}},iter=0,tvtemp,metrictemp,vector={},scalar},
If[OptionValue[ShowProgress],
Print[Dynamic[iter],"/",Length[prebasis]];
Print[Dynamic[Length[poslist]],"/",OptionValue[TargetDim]," found: "];
Print[Dynamic[poslist]];
];
Do[iter++;
tvtemp=f[t];
scalar=tvtemp\[Conjugate].tvtemp;
If[Length@tensorValue==0,metrictemp={{scalar}},
vector=tensorValue.tvtemp\[Conjugate];
metrictemp=Append[Append[metric\[ConjugateTranspose],vector]\[ConjugateTranspose],Append[vector,scalar]]
];
If[Chop[Det[metrictemp],OptionValue[Tolerance]]==0,Continue[]];
metric=metrictemp;
AppendTo[tensorValue,tvtemp];
AppendTo[mtensor,t];
AppendTo[poslist,iter];
If[Length[metric]===OptionValue[TargetDim],Break[]];
,{t,prebasis}];
<|"pos"->poslist,"mbasis"->mtensor,"mvalues"->Chop[tensorValue],"metric"->metric|>
]

LinearIntersection[{},basisB_]:={}
LinearIntersection[basisA_,basisB_]:=Module[{basisPlus=Join[basisA,basisB],lA=Length[basisA],sol},sol=NullSpace[Transpose[basisPlus]];
If[Length[sol]==0,Return[{}]];basisReduce[sol[[All,1;;lA]].basisA]["basis"]
]
LinearIntersection[basisA_]:=basisA
LinearIntersection[basisA_,basisB_,basisX__]:=LinearIntersection[LinearIntersection[basisA,basisB],basisX]

MapIntersection[A_,B_]:=Module[{len=Length[A],W,lenW,PA,PB,R},
If[MatrixRank[Join[A,B]]==len,Sow[IdentityMatrix[len],restriction];Return[LinearSolve[B\[Transpose]]/@A]];
W=LinearIntersection[A,B];
lenW=Length[W];If[lenW==0,Return[{{}}]];
PA=LinearSolve[A\[Transpose]]/@W;
PB=LinearSolve[B\[Transpose]]/@W;
If[MatrixRank[Join[PA,PB]]==lenW,Sow[PA,restriction];Return[LinearSolve[PA\[Transpose]]/@PB]];
R=LinearIntersection[PA,PB];Sow[R,restriction];
If[R=={},Return[{{}}]];
MapIntersection[R.A,R.B]
]


(* ::Input::Initialization:: *)
PermuteBasis[y_,YT_]:=Module[{symmetrizer,replacerule,yt=Flatten[YT]},
(*permute the given basis symbolically given the Young tableaux YT*)
If[MatchQ[YT,{{_}}]||MatchQ[YT,{{}..}],Return[y]];
symmetrizer=Prod2List/@Sum2List[Expand[Generateb[Length/@YT][[1]]]];
replacerule={#[[1]],MapThread[Rule,{yt,Permute[yt,InversePermutation@#[[2]]]}]}&/@symmetrizer;
Plus@@(Times@@@({#[[1]],y/.#[[2]]}&/@replacerule))
]
PermuteYBasis[y_,YTs_]:=Fold[PermuteBasis,y,YTs]


(* ::Input::Initialization:: *)
GatherWeights[listW_,listMult_:1]:=Module[{aux},
aux=listW/.{rep_List,weight_?NumberQ}:>(rep->weight);
aux=aux/.{x__Rule}:>Merge[{x},Apply[Plus]];
aux=DeleteCases[Merge[aux listMult,Apply[Plus]],0];
Normal[aux]/.Rule->List
]


(* ::Input::Initialization:: *)
SetAttributes[AssocIni,HoldAll];
AssocIni[assoc_]:=If[!AssociationQ[assoc],assoc=<||>]
AssocIni[assoc1_,assoc2__]:=AssocIni/@{assoc1,assoc2}


(* ::Input::Initialization:: *)
(* Special Definitions *)
tAssumptions={};
tReduce:=TensorReduce[#,Assumptions->tAssumptions]&;
tRank:=TensorRank[#,Assumptions->tAssumptions]&;
tDimensions:=TensorDimensions[#,Assumptions->tAssumptions]&;
tSymmetry=TensorSymmetry[#,Assumptions->tAssumptions]&;
