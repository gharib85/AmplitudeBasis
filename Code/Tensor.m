(* ::Package:: *)

(* ::Input::Initialization:: *)
Options[SymbolicTC]={WithIndex->True};
SymbolicTC[tensorpoly:_Plus|_List,OptionsPattern[]]:=SymbolicTC[#,WithIndex->OptionValue[WithIndex]]&/@tensorpoly
SymbolicTC[tensorprod_,OptionsPattern[]]:=Module[{coeff=1,heads={},indices={},indtemp,indlist,indcount,freeind,dumind,pairContract,order,tensorfinal},
Do[If[NumericQ[t],coeff*=t;Continue[]];
AppendTo[heads,t[[0]]];
AppendTo[indices,List@@t],
{t,Prod2List[tensorprod]}];
indices=Flatten[indices];
freeind=Select[indices,Count[indices,#]==1&];
dumind=DeleteDuplicates@Select[indices,Count[indices,#]==2&];
If[Complement[indices,freeind,dumind]!={},Print["abnormal indices in ",tensorprod]];

pairContract=First/@Position[indices,#]&/@dumind;
order=InversePermutation@FindPermutation[freeind];
tensorfinal=TensorTranspose[TensorContract[TensorProduct@@heads,pairContract],order];
If[OptionValue[WithIndex],tensorfinal=tensorfinal@@Sort[freeind]];
coeff tensorfinal
]

UnContract[tc:_Plus|_Times|_List]:=UnContract/@tc//Expand
UnContract[tc_/;tc[[0,0]]==TensorContract]:=Module[{tensors=tc[[0,1]],pairContract=tc[[0,2]],indlist=List@@tc,indtemp={}},
Do[indtemp=indtemp~Join~Thread[{Sow[Unique[],d],pair}],{pair,pairContract}];
indtemp=SortBy[indtemp,Last];
indlist=Fold[Insert[#1,#2[[1]],{#2[[2]]}]&,indlist,indtemp];
UnContract[tensors@@indlist]
]
UnContract[tc_/;tc[[0,0]]==TensorProduct]:=Module[{tensors=List@@tc[[0]],indlist=List@@tc,ranks},
ranks=tRank/@tensors;
If[Total[ranks]!=Length[indlist],Print["invalid tensor contraction ",tc]];
Times@@MapThread[Apply,{tensors,FoldPairList[TakeDrop,indlist,ranks]}]
]
UnContract[tc_/;tc[[0,0]]==TensorTranspose]:=Module[{tensor=tc[[0,1]],perm=tc[[0,2]],indlist=List@@tc},
UnContract[tensor@@Permute[indlist,FindPermutation[perm]]]
]
UnContract[tc_]:=tc


(* ::Input::Initialization:: *)
SetAttributes[IndexIterator,HoldRest];
IndexIterator[indlist_,indexct_]:=Module[{index=++indexct[indlist]},
If[indlist=={},Return[0]];
If[index>Length[indlist],Print["index list ",indlist," not enough."];index=indexct[indlist]=1];indlist[[index]]]

TensorAddIndex[indmap_,indexct_,tensorlist_]:=Module[{tensors,dummy,dummyPosList,indexcttemp,tname,slot,dummyReplace={}},
{tensors,dummy}=Reap[UnContract[tensorlist],d];
If[dummy!={},(* replace dummy index and sow m-basis *)
Do[dummyPosList=DeleteCases[Position[tensor,#]&/@dummy[[1]],{}];
If[dummyPosList=={},Continue[]];indexcttemp=indexct;
Do[tname=Head@Extract[tensor,Most@dpos];slot=Last@dpos;AppendTo[dummyReplace,Extract[tensor,dpos]->IndexIterator[indmap[tRep[tname][[slot]]],indexcttemp]],
{dpos,dummyPosList[[All,1]]}],
{tensor,tensors}];
];
tensors/.dummyReplace
]

