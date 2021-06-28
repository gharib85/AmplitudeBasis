(* ::Package:: *)

(* ::Input:: *)
(*GellMann*)
(*GenerateLRT*)
(*Product2ContractV2, GenerateFieldIndex, GenerateFieldTensor,TRefineTensor*)
(*FindIndependentMbasis, SimpGFV2, GetSymBasis*)
(**)


(* ::Input::Initialization:: *)
(* representation matrix for su(n) generators *)
GellMann[n_]:=GellMann[n]=
Flatten[Table[(*Symmetric case*)SparseArray[{{j,k}->1,{k,j}->1},{n,n}],{k,2,n},{j,1,k-1}],1]~Join~Flatten[Table[(*Antisymmetric case*)SparseArray[{{j,k}->-I,{k,j}->+I},{n,n}],{k,2,n},{j,1,k-1}],1]~Join~Table[(*Diagonal case*)Sqrt[2/l/(l+1)] SparseArray[Table[{j,j}->1,{j,1,l}]~Join~{{l+1,l+1}->-l},{n,n}],{l,1,n-1}];


(* ::Subsubsection::Closed:: *)
(*Littlewood-Richardson related*)


(* ::Input::Initialization:: *)
(*find the chain of representations along the direct product decomposition procedure that give the singlet representation in the end*)
findpath[finallist_,group_,finalrep_,repconstr_,replist_]:=Module[{singlet,trepconstr=repconstr[[1;;-1]],replistremain=replist[[1;;-1]],lrepc,lremain,listrep},
lrepc=Length@trepconstr;
lremain=Length@replistremain;
If[lremain==0,Return[]];
If[lrepc==0&&lremain==1,If[replistremain[[1]]==finalrep,finallist={Append[finallist,replistremain[[1]]]};
Return[];,Return[]]];
If[lrepc==0,AppendTo[trepconstr,replist[[1]]];replistremain=replist[[2;;-1]];lremain-=1];
If[lremain==1,
If[Length[Position[MyRepProduct[group,{trepconstr[[-1]],replistremain[[1]]}],{finalrep,_}]]!=0,AppendTo[trepconstr,finalrep];
AppendTo[finallist,trepconstr];
];
];
listrep=MyRepProduct[group,{trepconstr[[-1]],replistremain[[1]]}][[1;;-1,1]];
Do[findpath[finallist,group,finalrep,Append[trepconstr,listrep[[i]]],replistremain[[2;;-1]]],{i, Length[listrep]}];
];
SetAttributes[findpath,HoldFirst];
FindRepPath[group_,finalrep_,replist_]:=Module[{finallist={},repconstr={}},findpath[finallist,group,finalrep,repconstr,replist];(Dynk2Yng/@#&)/@finallist];
FindSingletPath[group_,replist_]:=FindRepPath[group,ConstantArray[0,Length[group]],replist];


(* ::Input::Initialization:: *)
(*The set of the Littlewood-Richardson rules that needed to check at each step of constructing*)
IsNormalYoungDiagramQ[diag_]:=If[Length[diag]==1,True,And@@(diag[[#]]>=diag[[#+1]]&/@Range[1,Length[diag]-1])]
CompYoungDiagramQ[y1_,y2_]:=Module[{y3},y3=PadRight[y1,Length[y2]];And@@MapThread[#1<=#2&,{y3,y2}]];
ColumnConditionQ[l_]:=And@@(#<=1&)/@(Max[#[[1;;-1,2]]]&/@(Tally/@Select[TransposeTableaux[l],Length[#]!=0&]))
RowConditionQ[l_]:=Module[{it,nrow,unique,counter,temp,result=True},
nrow=Length[l];
unique=Union[Cases[Flatten[l],_Integer]];
If[Length[unique]==0,Return[result]];
MapThread[Set,{counter/@unique,Table[0,{i,Length[unique]}]}];
Do[it=-1;
While[(-it)<=Length[l[[k]]],
If[!MatchQ[l[[k,it]],_Integer],Break[]];
counter[l[[k,it]]]+=1;
temp=Select[unique,#<l[[k,it]]&];
If[Length[temp]==0,it-=1;Continue[]];
If[And@@((counter[l[[k,it]]]<=#&)/@(counter/@temp)),
it-=1;
Continue[];,
result=False;Return[result]]];
,{k,1,nrow}];
result
]
EqualYoungDiagramQ[y1_,y2_]:=If[Length[y1]!=Length[y2],False,And@@MapThread[#1==#2&,{y1,y2}]];

FillYD[fdl_,fdlstr_,diag1_,diag1str_,ldiag2_,ldiag2str_,fdiag_,n_]:=
(*fdl: final YoungTableaux with integer,
 fdlstr: final YoungTableaux with indices only,
 diag1: YoungTableaux, 
 diag1str: YoungTableaux with indices only, 
 ldiag2: falttened YoungTableaux with integers that are used to paste on diag1, 
 ldiag2str: falttened YoungTableaux with indices that are used to paste on diag1, 
 fdiag: YoungDiagram*)
Module[{tdiag1,tdiag1str,l1=Length[ldiag2],yd1=Length/@diag1,l=Length[diag1]},
(*Following conditional expression is used to test whether the current constructed YoungTableaux statiesfies the Littlewood-Richardson Rules*)
If[(!IsNormalYoungDiagramQ[yd1]),Return[]];
If[(!CompYoungDiagramQ[yd1,fdiag]),Return[]];
If[(!ColumnConditionQ[diag1]),Return[]];
If[(!RowConditionQ[diag1]),Return[]];
If[l1==0,
If[EqualYoungDiagramQ[yd1,fdiag],If[Length[Position[fdl,diag1]]==0,AppendTo[fdl,diag1];AppendTo[fdlstr,diag1str];];Return[],Return[]],
Do[
(*Pad the integer and indices of the diag2 onto the right of diag1, each one has n possible ways to pad*)
tdiag1=diag1;
tdiag1str=diag1str;
l=Length[tdiag1];
If[i<=l&&i-l<=1,
AppendTo[tdiag1[[i]],ldiag2[[1]]];
AppendTo[tdiag1str[[i]],ldiag2str[[1]]];
,AppendTo[tdiag1,{ldiag2[[1]]}];
AppendTo[tdiag1str,{ldiag2str[[1]]}];
];
FillYD[fdl,fdlstr,tdiag1,tdiag1str,ldiag2[[2;;-1]],ldiag2str[[2;;-1]],fdiag,n];
,{i,1,n}];
];
]
SetAttributes[FillYD,HoldAll];


(* ::Input::Initialization:: *)
LRrule[yt1_,yt2_,fdiag_,n_]:=Module[{fdl={},fdlstr={},ldiag2=Flatten[Table[i&/@yt2[[i]],{i,1,Length[yt2]}]],ldiag2str=Flatten[yt2,1]},
If[Length[ldiag2str]==0,Return[{yt1}]];
FillYD[fdl,fdlstr,yt1,yt1,ldiag2,ldiag2str,fdiag,n];fdlstr]

LRTableaux[fytl_,YTlist_,path_,n_]:=Module[{conlist,lYTlist=Length[YTlist],tYTlist},
If[lYTlist==1,AppendTo[fytl,YTlist[[1]]];Return[]];
conlist=LRrule[YTlist[[1]],YTlist[[2]],path[[1]],n];
If[lYTlist==2,AppendTo[fytl,#]&/@conlist;Return[]];
Do[
tYTlist=YTlist[[3;;-1]];
PrependTo[tYTlist,conlist[[i]]];
LRTableaux[fytl,tYTlist,path[[2;;-1]],n],{i,1,Length[conlist]}]
]
SetAttributes[LRTableaux,HoldFirst]

ConvertPathtoYD[nlist_,ydlist_,n_]:=ConvertPathtoYD[nlist,ydlist,n]=Module[{nl,tydlist},
(*Do not take into account the first elements in ydlist*)
tydlist=PadRight[#,n,0]&/@ydlist;
nl=Accumulate[nlist];
nl=(nl-(Total/@tydlist))/n;
Drop[(tydlist[[#]]+nl[[#]])&/@Range[1,Length[tydlist]]/.{0->Nothing},1]]

dummyFund[fundIndex_]:=ToExpression[StringJoin@@ConstantArray[ToString[fundIndex],2]]

GenerateTYT[numIP_,baserep_,fnamenum_,index_,group_]:=GenerateTYT[numIP,baserep,fnamenum,index,group]=Module[{tindex=index,n=Length[group]+1,standardyt,partbaserep=Dynk2Yng[baserep],ydlist,ll,fytl={}},
(*If[MatchQ[baserep,Singlet[group]],Return[{{}}]];*)
(*Haolin Modified to adapt the j-basis*)
If[MatchQ[baserep,Singlet[group]],Return[ConstantArray[{},numIP]]];
If[!MatchQ[baserep,Fund[group]],tindex=dummyFund[index]];
If[Length[StringCases[fnamenum,"\[Dagger]"]]!=0&&baserep=={1},tindex=dummyFund[index]];
partbaserep=partbaserep/.{0->Nothing};
standardyt=MapThread[Range,{Accumulate[partbaserep]-partbaserep+1,Accumulate[partbaserep]}];
(*the lables of the indices is in the following form: index[i,j,k],
  i labels the i-th group of the repeated fields,
  j labels the j-th field in this group of repeated fields,
  k labels the k-th fundamental indices of this particular field*)
ydlist=Table[Map[tindex[fnamenum,i,#]&,standardyt,{2}],{i,numIP}]
(*ydlist=Table[Map[tindex<>"[ToString["<>ToString[fnamenum]<>"],"<>ToString[i]<>","<>ToString[#]<>"]"&,standardyt,{2}],{i,numIP}]*)
]

GaugeTensorFundInd[group_,rep_,label_]:=Module[{n=Length[group]+1,standardyt,partbaserep=Dynk2Yng[rep]/.{0->Nothing}},
If[MatchQ[rep,Singlet[group]],Return[{{}}]];
standardyt=MapThread[Range,{Accumulate[partbaserep]-partbaserep+1,Accumulate[partbaserep]}];
Map[Subscript[label,#]&,standardyt,{2}]]


(* ::Input::Initialization:: *)
GenerateLRT[group_,indmap_,replist_]:=
(*replist is a list of elements in the following form: {__,__,__}, 
the first slot is the number of repeated fields that construct the representation in the first slot,
the second slot is the representation of the repeated fields,
the last slot is the name of the repeated field*)
Module[{nlist,irreplist,basereplist,index=indmap[Fund[group]],tyt1,pathlists={},result={}},
irreplist=Flatten[ConstantArray[#[[2]],#[[1]]]&/@replist,1];
nlist=(Total[Dynk2Yng[#]])&/@irreplist;
(*Generate tensor Young Tableaux*)
tyt1=Flatten[GenerateTYT@@@(Join[#,{index,group}]&/@replist),1]; (* Young tableau of each field *)
pathlists=ConvertPathtoYD[nlist,#,Length[group]+1]&/@FindSingletPath[group,irreplist];
Do[LRTableaux[result,tyt1,path,Length[group]+1],{path,pathlists}];
result
]

GaugeYT[group_,irreplist_]:=Module[{nlist,basereplist,tyt1,pathlists={},result={},indsort},
nlist=(Total[Dynk2Yng[#]])&/@irreplist;
(*Generate tensor Young Tableaux*)
tyt1=MapIndexed[GaugeTensorFundInd[group,#1,First[#2]]&,irreplist]; (* Young tableau of each field *)
pathlists=ConvertPathtoYD[nlist,#,Length[group]+1]&/@FindSingletPath[group,irreplist];
Do[LRTableaux[result,tyt1,path,Length[group]+1],{path,pathlists}];
Times@@tYDcol[group]@@@Transpose[#]&/@result
]

GenerateLRTYTs[group_,rep_,YTs_]:=
(*Get the Target Tableaux of the target Young diagram of representation "rep" given a series of input young tableaux*)
Module[{nlist,irreplist,basereplist,index=indmap[Fund[group]],tyt1,nonSingletYTs,pathlists={},result={}},
nonSingletYTs=YTs/.{}->Nothing;
irreplist=(Length/@#)&/@nonSingletYTs;
nlist=Total/@irreplist;
irreplist=Yng2Dynk[group,#]&/@irreplist;
pathlists=ConvertPathtoYD[nlist,#,Length[group]+1]&/@FindRepPath[group,rep,irreplist];
Do[LRTableaux[result,nonSingletYTs,path,Length[group]+1],{path,pathlists}];
result
]

PartitionList[list_,part_]:=Module[{endpoint=Accumulate[part]},list[[#]]&/@MapThread[Span,{endpoint-part+1,endpoint}]];
FillSSYTSUN[result_,indexmap_,tableaux_,totaln_,N_,n_]:=Module[{temp=tableaux,ttemp},
Do[
If[(N-insert)<(Length[tableaux[[indexmap[n][[1]]]]]-indexmap[n][[2]]),Return[]];
temp[[Sequence@@indexmap[n]]]=insert;
ttemp=TransposeTableaux[temp];
If[And@@(OrderedQ/@ttemp)&&And@@(Less@@@(temp/.Infinity->Nothing)),
If[n==totaln,AppendTo[result,ttemp];,
FillSSYTSUN[result,indexmap,temp,totaln,N,n+1];
]
],{insert,N}]]
SetAttributes[FillSSYTSUN,HoldAll];
GetSSYTSUN[partition_,group_]:=Module[{N=Length[group]+1,totaln=Total[partition],tempkeys,temptab,indexmap,initialtab,result={}},
tempkeys=Range[totaln];
temptab=TransposeTableaux@PartitionList[tempkeys,partition];
indexmap=Association@MapThread[Rule,{tempkeys,((Position[temptab,#][[1]]))&/@tempkeys}];
initialtab=TransposeTableaux@PartitionList[ConstantArray[Infinity,totaln],partition];
FillSSYTSUN[result,indexmap,initialtab,totaln,N,1];
result
];


(* ::Subsubsection::Closed:: *)
(*Tensor Reduction related*)


(* ::Input::Initialization:: *)
(* Convert the product of the symbolic tensors to the tensor product in the Mathematica format*)
Product2Contract[x_]:=Module[{expr,tensorlist,numberlist,headlist,arglist,uniquelist,listrepeat,tensorp},
If[Head[x]==Times,expr=List@@x,expr=x];
numberlist=Cases[x,_?NumberQ];
tensorlist=Sort[Complement[expr,numberlist]];
headlist=Head/@tensorlist;
arglist=Flatten[List@@@tensorlist];
uniquelist=Union[arglist];
listrepeat=Flatten/@(Position[arglist,#]&/@uniquelist);
tensorp=TensorProduct@@headlist;
Times@@AppendTo[numberlist,TensorContract[tensorp,listrepeat]]
]
(*convert the symbolic gauge group tensors into numerical ones*)
Options[Product2ContractV2]={Symb2Num->{}};
Product2ContractV2[x_,inarglist_,OptionsPattern[]]:=Module[{num,tensorlist,headlist,arglist,uniquelist,listrepeat,tensorp},
tensorlist=Sort@Prod2List[x];
num=Cases[tensorlist,_?NumericQ];
tensorlist=DeleteCases[tensorlist,_?NumericQ];
headlist=Head/@tensorlist;
arglist=Flatten[List@@@tensorlist];
uniquelist=Union[arglist];
listrepeat=Select[Flatten/@(Position[arglist,#]&/@uniquelist),Length[#]==2&];
If[Length[listrepeat]!=0,arglist=Delete[arglist,{#}&/@Flatten[listrepeat]]];
tensorp=TensorProduct@@headlist/.OptionValue[Symb2Num];
If[Length[listrepeat]!=0,tensorp=TensorContract[tensorp,listrepeat]];
(Times@@num)*Transpose[tensorp,FindPermutation[arglist,inarglist]]
]

Product2ContractV3[x_,inarglist_,tval_]:=Module[{},
Switch[x,_Plus,Return[Plus@@(Product2ContractV2[#,inarglist,Symb2Num->tval]&/@Sum2List[x]
)];,
_,Return[Product2ContractV2[x,inarglist,Symb2Num->tval]]];
result
]


(* ::Input::Initialization:: *)
(*label the field name concerning repeated fields*)
GenerateFieldName[model_,groupname_,fs_]:=Module[{dim,result},
dim=DimR[CheckGroup[groupname],model[fs[[1]]][groupname]];
result=ToExpression["t"<>fs[[1]]<>groupname<>ToString[#]]&/@Range[fs[[2]]];
If[Cases[tAssumptions,#,Infinity]=={},AppendTo[tAssumptions,#\[Element]Arrays[{dim}]]]&/@result;
result]

GenerateFieldIndex[model_,groupname_,flist_]:=Module[{symbols,arg,indices},
symbols=model["rep2ind"][groupname]/@(model[#[[1]]][groupname]&/@flist);
arg=Table[{#[[1]],i,1},{i,#[[2]]}]&/@flist;
Flatten@MapThread[#1@@@#2&,{symbols,arg}]
]

GenerateFieldTensor[model_,groupname_,flist_,map_]:=Module[{heads,symbols,arg,indices},
(*This function generate the field tensors with the form: t<>F<>Group[ind["F",n,1]]<>n that can multiplied to the group factor, and also an association that map the field tensors to the indicies they carries on*)
If[Length[flist]==0,Return[1]];
heads=Flatten[GenerateFieldName[model,groupname,#]&/@flist];
indices=GenerateFieldIndex[model,groupname,flist];
map=AssociationThread[heads->indices];
Times@@(Flatten@MapThread[Construct,{heads,indices}])
]
SetAttributes[GenerateFieldTensor,HoldAll]

Contraction2Tensor[TC_,xmap_,indmap_,ct_]:=Module[{tlist,r,tensor,ind=0,tensorlist={},pos,tname,pairRep,ranklist,aux1,indexorder,maporder2index=<||>},
(*convert a single TensorProduct to the tensors without field tensors*)
If[!MatchQ[TC,_TensorContract],Return[TC]];
tlist=List@@TC[[1]];
Do[r=Replace[tRank[t],Except[_Integer]->1];
tensor=Construct[t,++ind];
Do[AppendTo[tensor,++ind],r-1];
AppendTo[tensorlist,tensor],{t,tlist}]; (* t \[Rule] t[i,i+1,...,i+rank-1] *)
tensorlist={#,Complement[tensorlist,#]}&@Select[tensorlist,Length[#]>1&];(* separate field tensors from invariant tensors *) 
Do[pos=Position[tensorlist,#,3]&/@pair;
tname=First@Extract[tensorlist,ReplacePart[#,{1,-1}->0]]&/@pos;
Switch[pos[[All,1,1]],
{2,2},Message[Contraction2Tensor::ffcontr,TC];Abort[],
{1,2},tensorlist=ReplacePart[tensorlist,pos[[1]]->xmap[tname[[2]]]],
{2,1},tensorlist=ReplacePart[tensorlist,pos[[2]]->xmap[tname[[1]]]],
{1,1},pairRep=MapThread[tRep[#1][[#2[[1,3]]]]&,{tname,pos}];
If[RepConj[#1]===#2&@@pairRep,
tensorlist=ReplacePart[tensorlist,(Join@@pos)->#[++ct[#]]&[ indmap[pairRep[[1]]] ] ],
Message[Contraction2Tensor::mismatch,pair,TC];Abort[]]
],
{pair,TC[[2]]}];
Return[Times@@tensorlist[[1]]];
]
SetAttributes[Contraction2Tensor,HoldAll];
Contraction2Tensor::ffcontr="Contraction between fields in `1`";
Contraction2Tensor::mismatch="Contraction mismatch for pair `1` in `2`";

(* Convert a polynomial of TensorContract to product of tensors with specified form of indices *)
CounterIni[indmap_]:=AssociationThread[DeleteDuplicates@Cases[Values[indmap],_Symbol]->0] (* initialize counter for relevant indices *)
UnfoldContraction[x_TensorContract,xmap_,indmap_]:=Module[{ct=CounterIni[indmap]},Contraction2Tensor[x,xmap,indmap,ct]]
UnfoldContraction[x_Times,xmap_,indmap_]:=Module[{ct=CounterIni[indmap]},Times@@(Contraction2Tensor[#,xmap,indmap,ct]&/@Prod2List[x])]
UnfoldContraction[x_Plus,xmap_,indmap_]:=Plus@@(UnfoldContraction[#,xmap,indmap]&/@Sum2List[x])
SetAttributes[UnfoldContraction,HoldRest]

RefineTensor[x_,model_,groupname_,fts_]:=Module[{tempx,flist,tfs,xmap,xposmap,rt,result},
If[x==0,Return[0]];
tempx=Expand[Expand[x]/.Power[z_,y_]:>Times@@ConstantArray[z,y]];
flist=Select[fts,Total[model[#[[1]]][groupname]]!=0&];
tfs=GenerateFieldTensor[model,groupname,flist,xmap];
rt=tReduce[Plus@@(Product2Contract/@(Flatten[{Expand[tempx]}/.Plus->List]*tfs))];
UnfoldContraction[rt,xmap,model["rep2ind"][groupname]]
]
SetAttributes[RefineTensor,HoldFirst]

(* Refine gauge group tensors with the symmetry of the invariant tensors *)
TRefineTensor[x_,model_,groupname_,fts_]:=TRefineTensor[x,model,groupname,fts]=Module[{trank,tdim,result,len},
trank=tRank[x];
tdim=tDimensions[x];
result=Flatten[{x}];
len=Length[result];
result=RefineTensor[#,model,groupname,fts]&/@result;
If[!IntegerQ[trank]||trank==0,Return[result[[1]]]];
unflatten[result,tdim]
]



(* ::Subsubsection:: *)
(*JBasis related*)


(* ::Input::Initialization:: *)
(*Find the partitions in largest subgroups*)
UnionFinder[list_]:=Module[{templist=list,templist2={},lpos,i,flag=True},
If[list=={},Return[{Nothing}],templist=Sort[list,Length[#1]>Length[#2]&];AppendTo[templist2,templist[[1]]];lpos={{1}};];
For[i=2,i<=Length@templist,i++,
If[IntersectingQ[templist[[1]],templist[[i]]],
AppendTo[templist2,templist[[i]]];
AppendTo[lpos,{i}];
];
];
templist=Delete[templist,lpos];
Join[{templist2},UnionFinder[templist]]
]
SetAttributes[UnionFinder,HoldFirst]

(*Find tree structure for each subgroup*)
HierarchyFinder[result_,list_]:=Module[{templist,complist,comppos,remain,lpos,i,j,flag=True},
For[j=1,j<=Length[list],j++,
(*reset two variables, templist store subsets in the list that are consitutes list[[j]]; 
flag record wether the number of the subsets is greater than 2*)
templist={};
flag=True;
For[i=j+1,i<=Length[list],i++,
complist=Complement[list[[j]],list[[i]]];
If[Length@complist==1,
result[list[[j]]]={list[[i]],complist};flag=False;Break[];
];
comppos=Position[list,complist];
If[Length@comppos!=0&&comppos[[1,1]]!=j,
result[list[[j]]]={list[[i]],complist};flag=False;Break[];,
(*Adding Length@comppos\[Equal]0 in the next line is to avoid the error occurred for part the comppos in comppos[[1,1]]*)
If[Length@comppos==0||comppos[[1,1]]!=j,AppendTo[templist,list[[i]]];
]
];
];
If[flag,remain=Complement[list[[j]],Union@@templist];
If[remain!={},templist=Join[templist,List/@remain]];
result[list[[j]]]=templist;];
];
]
SetAttributes[HierarchyFinder,HoldFirst]

FindRepPathV2[group_,replist_,partrule_,hierarchy_]:=
(*Generated the list of possible irreps of next grouping level with corresponding multiplicity;
group: specifiy the group, e.g. SU3,SU2;
replist: a list of irreps of all the fields;
partrule: form of part\[Rule]irreps (e.g. {1,2,3}\[Rule]{0,0} for SU3 group)
*)
Module[{parts=hierarchy[partrule[[1]]],disted,trep=partrule[[2]]},disted=Distribute[ReduceRepProduct[group,#]&/@(Part[replist,#]&/@parts),List];
partrule->MapAt[MapThread[{#1->#2[[1]],#2[[2]]}&,{parts,#}]&,Cases[{#,ReduceRepProduct[group,#[[1;;,1]]]}&/@disted,{x__,{___,{trep,y_},___}}:>{x,y}],{All,1}]
]

FindRepPathV3[asso_,group_,replist_,partrule_,hierarchy_]:=Module[
{subparts=hierarchy[partrule[[1]]],subreps,newsubs},
If[MatchQ[subparts,_Missing|{_}],Return[]];
subreps=FindRepPathV2[group,replist,partrule,hierarchy];
newsubs=DeleteDuplicates[Flatten@subreps[[2,1;;,1,1;;,1]]];
AppendTo[asso,subreps];
FindRepPathV3[asso,group,replist,#,hierarchy]&/@newsubs;
]
SetAttributes[FindRepPathV3,HoldFirst]

AuxResolve[linkedmap_,inputlist_,previouslist_,hierarchy_]:=Module[{temp,temp2},
temp=Join@@@Distribute[(linkedmap[#][[1;;,1,1;;,1]])&/@inputlist,List];
temp2=Select[#,!MatchQ[hierarchy[#[[1]]],_Missing|{{_}..}]&]&/@temp;
MapThread[{#1,#2}&,{Join[previouslist,#]&/@temp,temp2}]
]
AuxResolve2[result_,linkedmap_,inputlist_,previouslist_,hierarchy_]:=Module[{temp},
If[inputlist=={},AppendTo[result,Association@previouslist];Return[]];
temp=AuxResolve[linkedmap,inputlist,previouslist,hierarchy];
Do[AuxResolve2[result,linkedmap,item[[2]],item[[1]],hierarchy],{item,temp}]
]
SetAttributes[AuxResolve2,HoldFirst]
AuxNum[group_,part_,chainmap_,hierarchy_]:=Module[{temp},
If[MatchQ[part,{_}],Return[1],
temp=Times@@Cases[ReduceRepProduct[group,chainmap/@hierarchy[part]],{chainmap[part],x_}:>x];
Return[temp*(Times@@(AuxNum[group,#,chainmap,hierarchy]&/@hierarchy[part]))]
];
]

FindRepPathPartition[group_,replist_,partition_]:=Module[{hierarchy=Association[],n=Length[replist],temp1,linkedmap=Association[],result={},chainmap},temp1=UnionFinder[partition];If[Union@@temp1[[1;;All,1]]==Range[n],AppendTo[hierarchy,Range[n]->temp1[[1;;All,1]]],Print["Not a Good Partition"];Abort[];];(HierarchyFinder[hierarchy,#1]&)/@temp1;FindRepPathV3[linkedmap,group,replist,Range[n]->Singlet[group],hierarchy];
AuxResolve2[result,linkedmap,{Range[n]->Singlet[group]},{},hierarchy];
result=KeySelect[#,Function[x,Cases[partition,x]!={}]]&/@result;Do[chainmap=result[[i]];MapThread[(chainmap[{#1}]=#2)&,{Range[n],replist}];result[[i]]=result[[i]]->Times@@(AuxNum[group,#1,chainmap,hierarchy]&)/@temp1[[1;;All,1]];,{i,Length[result]}];result];


(* ::Input::Initialization:: *)
Options[GaugeJBasis]={Index->"default"};
GaugeJBasis[group_,replist_,parts_,OptionsPattern[]]:=Module[{indmap,nonsingletparts,YTlist,RepParts,YTParts,SUNrepPartlist,SubYTs,vtemp,stemp,coordtemp,tempresult,ranktemp,coordresult={},result,ntarget,
indexct,indlist,ybasis,convert,tensorlist,tensorValue,mbasis,mbasisInd,finalresult,qr},
If[OptionValue[Index]==="default",indmap=Global`INDEX[group],indmap=OptionValue[Index]];
indexct=AssociationThread[Union@Values[indmap]->0];
indlist=IndexIterator[indmap[#],indexct]&/@replist;
ybasis=GaugeYT[group,Abs@replist];If[ybasis=={1},Return[<|"basis"->{1},"jcoord"->{AssociationThread[parts->ConstantArray[Singlet[group],Length[parts]]]->{{1}}}|>]];
convert=UnContract[Times@@MapIndexed[CF[#1[[1]],#2[[1]],#1[[2]]]&,{replist,indlist}\[Transpose]]];
tensorlist=SimpGFV2[tReduce@SymbolicTC[Expand[# convert],WithIndex->False]&/@ybasis];

tensorValue=NumericContraction[tVal[group]]/@tensorlist;
mbasis=basisReduce[Flatten/@tensorValue];
mbasisInd=TensorAddIndex[indmap,indexct,Through[tensorlist[[mbasis["pos"]]]@@DeleteCases[indlist,0]]];
finalresult=<|"basis"->mbasisInd|>;

(*Begin Processing J basis related*)
qr=LinSolve[mbasis["basis"]];
SUNrepPartlist=FindRepPathPartition[group,Abs@replist,parts];
nonsingletparts=Select[Keys@SUNrepPartlist[[1,1]],(!MatchQ[replist[[#]]&/@#,{Singlet[group]..}])&];
YTlist=MapIndexed[DeleteCases[{}]@FoldPairList[TakeDrop,Table[Subscript[#2[[1]], i],{i,Total@Dynk2Yng[#1]}],Dynk2Yng[#1]]&,replist]; (*Young tableaux for the representation*)
RepParts=Map[replist[[#]]&,nonsingletparts,{2}];
YTParts=Map[YTlist[[#]]&,nonsingletparts,{2}];
SubYTs=Table[Distribute[GenerateLRTYTs@@@MapThread[{group,#1,#2}&,{SUNrepPartlist[[i,1]][#]&/@nonsingletparts,YTParts}],List],{i,Length[SUNrepPartlist]}];

Do[tempresult={};ranktemp=0;
ntarget=SUNrepPartlist[[i,2]];
(* loops for particular channel *)
Do[(* loop over ybasis *)
Do[(* loop over young tab *)
stemp=Expand@FixedPoint[Identityfunc,(PermuteYBasis[ybs,YTs]/. Sortarg[tasList[group]])convert];(*Map[2#&,Expand[(PermuteYBasis[ybs,YTs]/.Sortarg[tasList[group]])*convert]]//Expand;*)
If[stemp==0,Continue[]];
vtemp=SymbolicTC[stemp,WithIndex->False];
vtemp=NumericContraction[vtemp,tVal[group]];
coordtemp=Flatten[vtemp].qr;
AppendTo[tempresult,coordtemp];
If[ranktemp+1==MatrixRank[tempresult],ranktemp+=1;If[ranktemp==ntarget,Break[]],
tempresult=Drop[tempresult,-1]]
,{YTs,SubYTs[[i]]}]; 
If[ranktemp==ntarget,Break[]]
,{ybs,ybasis}];
(* end loops for particular channel*)
AppendTo[coordresult,SUNrepPartlist[[i,1]]->tempresult];
,{i,Length[SUNrepPartlist]}
];
AssociateTo[finalresult,"jcoord"->coordresult]
]


(* ::Subsubsection:: *)
(*Symmetrization related*)


(* ::Input::Initialization:: *)
(*find the independent m-basis tensors and store them into the symbolic forms, numerical tensor forms and numerical vector forms*)
FindIndependentMbasis[Mbasis_,tMbasis_,vMbasis_]:=Module[{result,tempI},
result=Part[#,basisReduce[vMbasis]["pos"]]&/@{Mbasis,tMbasis,vMbasis};
tempI=If[Or@@(#\[Element]Reals&/@#),1,I]&/@result[[3]];
tempI*#&/@result
]
(*Delete duplicated list of tensors that are propotional to each other*)
SimpGFV2[x_]:=If[Length[x]>=1,DeleteDuplicates[Replace[#,{_Rational->1,_Integer->1,_Complex->1},{1}]&/@(Flatten@(x/.Plus->List))],x]



(* ::Input:: *)
(*(*symmetrize the group factor numerically with certain group algebra elements*)*)
(*SymBasis[basis_,perms_]:=*)
(*Plus@@(MapThread[(Transpose[basis,#1]*#2)&,Transpose[(ColistPP[perms])]])*)
(**)
(*(*Get the coordinnate of arbitrary group factor tensor in terms of the m-basis*)*)
(*GetCoord[qr_,v_]:=qr[[1]].v.Transpose[Inverse[qr[[2]]]]*)
(**)
(*(*Get the symmetrized group factor tensors from the m-basis*)*)
(*GetSymBasis[tMBasis_,SNIrreps_,disp_,qr_,tdim_]:=Module[{multi=SNIrreps[[2]],key=SNIrreps[[1]],num,perms,displist,tensordim,mrank,resultAux={},result={},i=1,tempv},*)
(*num=Times@@(SnIrrepDim/@key[[1;;-1,2]]);*)
(*displist=disp/@key[[1;;-1,1]];*)
(*perms=Generateb/@key[[1;;-1,2]];*)
(*perms=MapThread[#2/.Cycles[x__]:>Cycles[x+#1]&,{displist,perms}];*)
(*tensordim=Length/@perms;*)
(*perms=pp/@Distribute[perms,List];*)
(*mrank=0;*)
(*While[mrank<num*multi&&i<=Length[tMBasis],*)
(*tempv=Flatten/@(SymBasis[tMBasis[[i]],Expand[#]]&/@perms);*)
(*tempv=GetCoord[qr,#]&/@tempv;*)
(*resultAux=Join[resultAux,tempv];*)
(*(*Assuming newly symmetrized basis either all independent with the existing ones or all live in the exsiting space*)*)
(*If[MatrixRank[resultAux]-mrank==Length[tempv],*)
(*mrank=MatrixRank[resultAux]; *)
(*tempv=unflatten[Simplify[tempv],tdim];*)
(*AppendTo[result,tempv]];*)
(*i++;*)
(*];*)
(*result*)
(*]*)
(**)
(*Options[GaugePermGenerator]={Index->"default"};*)
(*GaugePermGenerator[group_,replist_,OptionsPattern[]]:=Module[{indmap,indexct,*)
(*indlist,ybasis,convert,tensorlist,tensorValue,mbasis,result,dummy,dummyPosList,indexcttemp,dummyReplace={},*)
(*tname,slot,indexRepeat},*)
(*If[OptionValue[Index]==="default",indmap=Global`INDEX[group],indmap=OptionValue[Index]];*)
(**)
(*indexct=AssociationThread[Union@Values[indmap]->0];*)
(*indlist=IndexIterator[indmap[#],indexct]&/@replist;*)
(*ybasis=GaugeYT[group,Abs@replist];If[ybasis=={1},Sow[{1},tl];Return[<||>]];*)
(*convert=MapIndexed[CF[#1[[1]],#2[[1]],#1[[2]]]&,{replist,indlist}\[Transpose]];*)
(*indlist=DeleteCases[indlist,0];*)
(*tensorlist=SimpGFV2[tReduce@SymbolicTC[UnContract[# Times@@convert],WithIndex->False]&/@ybasis];*)
(*tensorValue=tensorlist/.tVal[group];*)
(*mbasis=basisReduce[Flatten/@tensorValue];*)
(*{result,dummy}=Reap[UnContract[Through[tensorlist[[mbasis["pos"]]]@@Sort[indlist]]],d];*)
(*If[dummy!={},(* replace dummy index and sow m-basis *)*)
(*Do[dummyPosList=DeleteCases[Position[tensor,#]&/@dummy[[1]],{}];*)
(*If[dummyPosList=={},Continue[]];indexcttemp=indexct;*)
(*Do[tname=Head@Extract[tensor,Most@dpos];slot=Last@dpos;AppendTo[dummyReplace,Extract[tensor,dpos]->IndexIterator[indmap[tRep[tname][[slot]]],indexcttemp]],*)
(*{dpos,dummyPosList[[All,1]]}],*)
(*{tensor,result}];*)
(*];*)
(*Sow[result/.dummyReplace,tl];*)
(**)
(*indexRepeat=Select[Merge[Thread[DeleteCases[replist,Singlet[group]]->indlist],Identity],Length[#]>1&];*)
(*result=(Map[LinearSolve[Transpose[mbasis["basis"]],Flatten[#1]]&,SymbolicTC[{result/. IndexInvPermute[Cycles[{{1,2}}],#1],result/. IndexInvPermute[Cycles[{Range[Length[#1]]}],#1]},WithIndex->False]/. tVal[group],{2}]&)/@indexRepeat;*)
(*If[Count[replist,Singlet[group]]>1,AssociateTo[result,Singlet[group]->ConstantArray[IdentityMatrix[Length[mbasis["basis"]]],2]]];*)
(*Return[result];*)
(*]*)


(* ::Input:: *)
(*Options[GaugeBasisAux]={OutMode->"p-basis",Index->"default"};*)
(*GaugeBasisAux[group_,replist_,posRepeat_,OptionsPattern[]]:=Module[{shift,yngList,gaugeGen,mbasis,trivial=False,result},*)
(*If[posRepeat==<||>,trivial=True]; (* no repeated fields *)*)
(*{gaugeGen,mbasis}=Reap[GaugePermGenerator[group,replist,Index->OptionValue[Index]],tl];*)
(*If[gaugeGen==<||>,trivial=True]; (* all singlets *)*)
(*result=<|"basis"->mbasis[[1,1]]|>;*)
(*shift=FirstPosition[PositionIndex[replist],First[#]]&/@posRepeat;*)
(**)
(*Switch[Head[posRepeat],*)
(*Association,*)
(*If[trivial,Return[Append[result,"p-basis"-><|{}->IdentityMatrix[Length[mbasis[[1,1]]]]|>]]];*)
(*yngList=IntegerPartitions@Length[#]&/@posRepeat;*)
(*yngList=AssociationThread/@Distribute[{Keys[yngList]}->Distribute[Values[yngList],List],List];*)
(*Append[result,"p-basis"->*)
(*DeleteCases[Association@Map[Normal[#]->*)
(*basisReduce[Dot@@KeyValueMap[PermRepFromGenerator[gaugeGen[[shift[#1][[1]]]],YO[#2,shift[#1][[2]]]]&,#]]["basis"]&,yngList],{}]],*)
(**)
(*List,*)
(*If[trivial,Return[Append[result,"generators"-><|#->{{{1}},{{1}}}&/@posRepeat|>]]];*)
(*Append[result,"generators"->*)
(*Association@MapThread[*)
(*#2->Function[gen,PermRepFromGenerator[gaugeGen[[#1[[1]]]],gen]]/@{Cycles[{{#1[[2]],#1[[2]]+1}}],Cycles[{Range[#1[[2]],#1[[2]]+Length[#2]-1]}]}&,*)
(*{shift,posRepeat}]]*)
(*]*)
(*]*)


(* ::Input::Initialization:: *)
(*

GaugePermGenerator[group_,replist_]:=Module[{indlist,ind,indexRepeat,ybasis,convert,tensorlist,tensorValue,mbasis,qr,mtensor,result,dummy,perm1,perm2,permresult},
indlist=Array[ind,Length[replist]];
indexRepeat=Select[PositionIndex[replist],Length[#]>1&];

ybasis=GaugeYT[group,Abs@replist];If[ybasis=={1},Return[<|"basis"->{1},"generators"-><||>|>]];
convert=UnContract[Times@@MapIndexed[CF[#1[[1]],#2[[1]],#1[[2]]]&,{replist,indlist}\[Transpose]]];
tensorlist=SimpGFV2[tReduce@SymbolicTC[Expand[# convert],WithIndex->False]&/@ybasis];
tensorValue=NumericContraction[tVal[group]]/@tensorlist;
(*tensorValue=tensorlist/.tVal[group];*)
mbasis=basisReduce[Flatten/@tensorValue];
result=<|"basis"->tensorlist[[mbasis["pos"]]]|>;
If[Length[indexRepeat]==0,Return[AssociateTo[result,"generators"-><||>]]];

qr=LinSolve[Flatten/@mbasis["basis"]];
perm1=Normal@IndexInvPermute[Cycles[{{1,2}}],ind/@# ]&/@indexRepeat;
perm2=Normal@IndexInvPermute[Cycles[{Range[Length[#]]}],ind/@#]&/@indexRepeat;
mtensor=UnContract[Through[result["basis"]@@Sort[indlist]]];
permresult=Map[SymbolicTC[mtensor/.#,WithIndex->False]/.tVal[group]&,{perm1,perm2},{2}];
AssociateTo[result,"generators"->Map[(Flatten/@#).qr&,Merge[permresult,Identity],{2}]]
]


*)



(* ::Input::Initialization:: *)
GaugePermGenerator[group_,replist_,debug_:False]:=Module[{indlist,ind,indexRepeat,nonSingletIndex,nonSingletIndexRepeat,ybasis,dimB,convert,tensorlist,tensorValue={},dimtemp=0,iter=0,mbasis,ginv,tvCo,mtensor={},result,dummy,perm1,perm2,permresult,dimtest,ortho={},rowreduce={},qrtemp=0,tvtemp,tvorth,status,step=1,pos,finalresult},
indlist=Array[ind,Length[replist]];
indexRepeat=Select[PositionIndex[replist],Length[#]>1&];
nonSingletIndex=KeyDrop[PositionIndex[replist],{Singlet[group]}];
nonSingletIndexRepeat=KeyDrop[indexRepeat,{Singlet[group]}];

If[debug==True,Print["get ybasis .."]];
ybasis=GaugeYT[group,Abs@replist];If[ybasis=={1},Return[<|"basis"->{1},"generators"-><||>|>]];
dimB=Length[ybasis];
If[debug==True,Print[dimB," ybasis"]];
convert=UnContract[Times@@MapIndexed[CF[#1[[1]],#2[[1]],#1[[2]]]&,{replist,indlist}\[Transpose]]];

If[debug==True,Print["get mbasis .."]];
(*tensorlist=Import["mbasis.m"];*)
tensorlist=SimpGFV2[tReduce@SymbolicTC[Expand[# convert],WithIndex->False]&/@ybasis];
If[debug==True,Print[Length[tensorlist]," monomials"]];

mbasis=basisReducePro[tensorlist,SparseArray@Flatten@NumericContraction[#,tVal[group]]&,TargetDim->dimB,ShowProgress->debug];
(*mbasis=Import["mbasis_result.m"];*)
result=<|"basis"->mbasis["mbasis"]|>;
If[Length[indexRepeat]==0,Return[AssociateTo[result,"generators"-><||>]]];
If[debug==True,Print["mbasis obtained"]];

If[debug==True,Print["linear solve .."]];
ginv=If[dimB<30,Inverse[mbasis["metric"]],
Inverse[mbasis["metric"]//N]];
tvCo=mbasis["mvalues"]\[ConjugateTranspose].ginv\[Conjugate];
If[debug===True,Print["orthonormality: ",MatchQ[Chop@Flatten[(Flatten/@mbasis["mvalues"]).tvCo-IdentityMatrix[dimB]],{0..}]]];

(*If[debug==True,Print["get generators .."]];
perm1=Normal@IndexInvPermute[Cycles[{{1,2}}],ind/@# ]&/@indexRepeat;
perm2=Normal@IndexInvPermute[Cycles[{Range[Length[#]]}],ind/@#]&/@indexRepeat;
permresult=Merge[{perm1,perm2},Identity];
If[debug==True,Print[permresult]];*)
(*Print[nonSingletIndexRepeat];
Print[PositionIndex[replist]];
Print[Union@@Values@nonSingletIndex];
Print[Map[First@FirstPosition[Union@@Values@nonSingletIndex,#]&,nonSingletIndexRepeat,{2}]];*)
If[debug==True,Print["start permuting"]];
permresult=Function[repeat,Transpose[ApplyGenerator[#,First@FirstPosition[Union@@Values@nonSingletIndex,#]&/@repeat ]&/@result["basis"]]]/@nonSingletIndexRepeat;

If[debug==True,Print["numerical components .."]];
permresult=Map[If[True(*(pos=Position[result["basis"],#])\[Equal]{}*),
SparseArray@Flatten@NumericContraction[#,tVal[group]],
Extract[mbasis["mvalues"],pos]]&,permresult,{3}];
If[debug==True,Print[Dimensions/@permresult]];

finalresult=Map[Chop[#.tvCo]&,permresult,{2}];
If[Count[replist,Singlet[group]]>1,AssociateTo[finalresult,Singlet[group]->ConstantArray[IdentityMatrix[Length[result["basis"]]],2]]];

If[debug==True,Print["find coord .."]];
AssociateTo[result,"generators"->Simplify/@finalresult]
]


(* ::Input::Initialization:: *)
Options[GaugeBasisAux]={Index->"default"};
GaugeBasisAux[group_,replist_,posRepeat_,OptionsPattern[]]:=Module[{indmap,indexct,indlist,shift,yngList,gaugeGen,mbasis,mbasisInd,dummy,
trivial=False,result},
If[OptionValue[Index]==="default",indmap=Global`INDEX[group],indmap=OptionValue[Index]];
indexct=AssociationThread[Union@Values[indmap]->0];
indlist=IndexIterator[indmap[#],indexct]&/@replist;
{mbasis,gaugeGen}=Values@GaugePermGenerator[group,replist];
mbasisInd=TensorAddIndex[indmap,indexct,Through[mbasis@@DeleteCases[indlist,0]]];
If[gaugeGen==<||>,trivial=True]; (* all singlets *)
result=<|"basis"->mbasisInd|>;

shift=FirstPosition[PositionIndex[replist],First[#]]&/@posRepeat;
Switch[Head[posRepeat],
Association,
If[trivial,Return[Append[result,"p-basis"-><|{}->IdentityMatrix[Length[mbasis]]|>]]];
yngList=IntegerPartitions@Length[#]&/@posRepeat;
yngList=AssociationThread/@Distribute[{Keys[yngList]}->Distribute[Values[yngList],List],List];
Append[result,"p-basis"->
DeleteCases[Association@Map[Normal[#]->
basisReducePro[Dot@@KeyValueMap[PermRepFromGenerator[gaugeGen[[shift[#1][[1]]]],YO[#2,shift[#1][[2]]]]&,#],Identity]["mvalues"]&,yngList],{}]],

List,
If[trivial,Return[Append[result,"generators"-><|#->{{{1}},{{1}}}&/@posRepeat|>]]];
Append[result,"generators"->
Association@MapThread[
#2->Function[gen,PermRepFromGenerator[gaugeGen[[#1[[1]]]],gen]]/@{Cycles[{{#1[[2]],#1[[2]]+1}}],Cycles[{Range[#1[[2]],#1[[2]]+Length[#2]-1]}]}&,
{shift,posRepeat}]]
]
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
Evaluate[ToExpression["SU"<>ToString[i]]]=CartanMatrix["SU",i];
,{i,2,10}]

(*Do[
Evaluate[ToExpression["SU"<>ToString[i]]]=Evaluate[ToExpression["Su"<>ToString[i]]]=Evaluate[ToExpression["su"<>ToString[i]]]=CartanMatrix["SU",i];
,{i,2,32}]
Do[
Evaluate[ToExpression["SO"<>ToString[i]]]=Evaluate[ToExpression["So"<>ToString[i]]]=Evaluate[ToExpression["so"<>ToString[i]]]=CartanMatrix["SO",i];
,{i,5,32}]
Do[
Evaluate[ToExpression["SP"<>ToString[i]]]=Evaluate[ToExpression["Sp"<>ToString[i]]]=Evaluate[ToExpression["sp"<>ToString[i]]]=CartanMatrix["SP",i];
,{i,2,32,2}]
*)
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




(* ::Input::Initialization:: *)
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

