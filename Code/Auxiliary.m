(* ::Package:: *)

(* ::Input::Initialization:: *)
Sum2List[x_Plus]:=List@@x
Sum2List[x:Except[Plus]]:=List@x
Prod2List[x_]:=Flatten[{x}/.{Power[b_,n_Integer]:>ConstantArray[b,n],Times->List}]

FactorSplit[exp_,crit_]:=Times@@@GroupBy[Prod2List[exp],crit]
FactorSplit[crit_]:=Times@@@GroupBy[Prod2List[#],crit]&

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
<|"basis"->Return[If[lmax<len,subbasis[[;;lmax]],subbasis]],"pos"-> poslist|>
]
basisReduce::input="wrong input matrix: `1`";


(* ::Input::Initialization:: *)
GatherWeights[listW_,listMult_:1]:=Module[{aux},
aux=listW/.{rep_List,weight_?NumberQ}:>(rep->weight);
aux=aux/.{x__Rule}:>Merge[{x},Apply[Plus]];
aux=DeleteCases[Merge[aux listMult,Apply[Plus]],0];
Normal[aux]/.Rule->List
]


(* ::Input:: *)
(*(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)*)
(**)
(*GatherWeights[listW_]:=GatherWeights[listW]=Module[{aux},*)
(*aux=Flatten[listW,1];*)
(*aux=Gather[aux,#1[[1]]==#2[[1]]&];*)
(**)
(*aux={#[[1,1]],Plus@@#[[1;;-1,2]]}&/@aux;*)
(*aux=DeleteCases[aux,x_/;x[[2]]==0];*)
(**)
(*Return[aux];*)
(*]*)
(**)
(*(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)*)
(**)
(*GatherWeights[listW_,listMult_]:=GatherWeights[listW,listMult]=Module[{aux},*)
(*aux=Table[{#[[1]],listMult[[i]]#[[2]]}&/@listW[[i]],{i,Length[listW]}];*)
(*aux=Flatten[aux,1];*)
(*aux=Gather[aux,#1[[1]]==#2[[1]]&];*)
(**)
(*aux={#[[1,1]],Plus@@#[[1;;-1,2]]}&/@aux;*)
(*aux=DeleteCases[aux,x_/;x[[2]]==0];*)
(*Return[aux];*)
(*]*)
(**)
