(* ::Package:: *)

(* ::Input::Initialization:: *)
Sum2List[x_Plus]:=List@@x
Sum2List[x:Except[Plus]]:=List@x
Prod2List[x_]:=Flatten[{x}/.{Power[b_,n_Integer]:>ConstantArray[b,n],Times->List}]

FactorSplit[exp_,crit_]:=Times@@@GroupBy[Prod2List[exp],crit]
FactorSplit[crit_]:=Times@@@GroupBy[Prod2List[#],crit]&

(* Separate numerical factors and symbolic factors of a monomial expression *)
(*normalize[monoAmp_]:=Module[{F,result},
F=Switch[monoAmp,_Times,List@@monoAmp,_,{monoAmp}];
result=Times@@@GatherBy[F,NumericQ];
If[Length[result]==1,PrependTo[result,1]];
If[MatchQ[result[[1]],_Complex],Return[{-I,I} result],Return[result]];
]*)

normalize[monoAmp_]:=Merge[{FactorSplit[monoAmp,NumericQ],<|True->1|>},Apply[Times]]/@{True,False}

(* Find the coefficient list of an expression (e.g. an amplitude) in STANDARD FORM. *)
FindCor::basis="non-standard expression `1` or incomplete basis `2`";
FindCor[Amp_,StBasis_]:=Module[{termlist,B,pos,cor},
(* Amp: the expression (may not be an amplitude,
StBasis: the standard basis (monomials). *)
cor=ConstantArray[0,Length[StBasis]];
termlist=Sum2List[Expand[Amp]];
If[termlist=={0},Return[cor]];
termlist=FactorSplit[NumericQ]/@termlist;
B=FactorSplit[NumericQ]/@StBasis;

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
basisReduce[subspace_,mode_:"basis"]:=Module[{subbasis,len=Length[subspace],lmax,iter=1,pos=1,poslist={}},
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


(* ::Input:: *)
(**)
