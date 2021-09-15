(* ::Package:: *)

(* ::Section:: *)
(*Soft Amplitudes*)


Clear[SoftBlocks];
Options[SoftBlocks]={Coord->True,all->True};
SoftBlocks[state_,k_,softparticles_,OptionsPattern[]]:=Module[{num=Length[state],basisIni,len,perm,replaceCor,constraint={},c,coord,gen1,gen2,result},basisIni=SSYT[state,k,OutMode->"amplitude"];
len=Length[basisIni];
Do[perm=Cycles[{Range[i,num]}];
replaceCor=FindCor[basisIni]/@YPermute[reduce[num-1]/@YPermute[basisIni/.{ab[i,_]->0,sb[i,_]->0,ab[_,i]->0,sb[_,i]->0},InversePermutation@perm,num,AmpReduce->False],perm,num,AmpReduce->False];
AppendTo[constraint,FindCor[Array[c,len]]/@DeleteCases[Array[c,len].replaceCor,0]];If[MatchQ[constraint,{{}..}],Continue[],Print["remaining: ",len-MatrixRank[Join@@constraint]]];
,{i,softparticles}];
coord=If[MatchQ[constraint,{{}..}],IdentityMatrix[Length@basisIni],
NullSpace[Join@@constraint]];
If[OptionValue[all],Return[#.basisIni&/@coord]];
gen1=LinearSolve[coord\[Transpose],FindCor[YPermute[#.basisIni,Cycles[{softparticles[[{1,2}]]}],num],basisIni]]&/@coord;
gen2=LinearSolve[coord\[Transpose],FindCor[YPermute[#.basisIni,Cycles[{softparticles}],num],basisIni]]&/@coord;
result=AssociationMap[Part[coord,basisReduce[PermRepFromGenerator[{gen1,gen2},YO[#]]]["pos"]]&,IntegerPartitions[Length[softparticles]]];
#.basisIni&/@Select[result,#!={}&]

(*If[OptionValue[Coord],coord,coord.basisIni]*)
]


(* ::Section:: *)
(*output one by one*)


Options[testPair]={doubleindex->{},AdlerZero->False};
testPair[pairlist_,current_,remain_,tensor_,other_,gotbasis_,ampbasis_,num_,OptionsPattern[]]:=
Module[{templist=pairlist,templist2,tempcurrent=current,tempcurrent2,tempremain=remain,tempremain2,newope,newcoor,newbasis=gotbasis,lbasis},
Switch[tensor[[0]],
	List,Do[ltensor=i;(*Print[{pairlist,current\[LeftDoubleBracket]i,1\[RightDoubleBracket],current\[LeftDoubleBracket]i,2;;\[RightDoubleBracket],tensor\[LeftDoubleBracket]i\[RightDoubleBracket],newbasis,OptionValue[AdlerZero]}];*)
		newbasis=testPair[pairlist,firs@current[[i]],Ex1@current[[i]],tensor[[i]],other[[i]],newbasis,ampbasis,num,
			doubleindex->OptionValue[doubleindex],AdlerZero->OptionValue[AdlerZero]];
		If[newbasis===Null,newbasis={}],{i,Length[tensor]}];
		Throw[newbasis],
	Integer,If[OptionValue[AdlerZero]===False,lbasis=Length[ampbasis],lbasis=OptionValue[AdlerZero]];
		newope=other;
		newcoor=FindCor[reduce[Amp[#]/.{Subscript[D, n_][\[Rho]_]^2:>0},num],ampbasis]&/@Append[newbasis,newope];
		If[MatrixRank[newcoor]>Length[newbasis],newbasis=Append[newbasis,newope];
			lnewbasis=Length[newbasis];
			If[Length[newbasis]===lbasis,Throw[newbasis]](*,Print[newcoor]*)];
		(*Return@*)Return[newbasis]
];
Switch[{current,remain},{{__},{}},Return[newbasis]];
If[OptionValue[AdlerZero]===False,lbasis=Length[ampbasis],lbasis=OptionValue[AdlerZero]];
Do[
Do[(*Print["start=",i,j];*)
templist2=Append[templist,{tempcurrent[[1]],tempremain[[i,j]]}];(*Print["contract=",{tempcurrent[[1]],tempremain[[i,j]]}];*)
tempremain2=(Delete[tempremain,{i,j}]/.{}->Nothing);
tempcurrent2=tempcurrent[[2;;]];(*Print["remain=",{tempcurrent2,tempremain2}];Print["basis=",newbasis];*)
If[Length@tempcurrent2>Length@Flatten[tempremain2],Return@Return@Return[newbasis]];
If[Length@tempcurrent2==0==Length@tempremain2,(*Sow[templist2];Return[];*)
	newope=other tensortooper[TensorContract[tensor,DoubleContract[templist2,OptionValue[doubleindex]]]];(*Print["check=",newope];*)
(*Print["check=",num];
Print["check=",ampbasis];Print["check=",gotbasis];*)newcoor=FindCor[reduce[Amp[#]/.{Subscript[D, n_][\[Rho]_]^2:>0},num],ampbasis]&/@Append[(*gotbasis*)newbasis,newope];(*Print["check=",newcoor];*)
If[MatrixRank[newcoor]>Length[(*gotbasis*)newbasis],newbasis=Append[(*gotbasis*)newbasis,newope];
lnewbasis=Length[newbasis];(*Print[newope];*)
If[Length[newbasis]===lbasis,(*Print["enough"];*)Throw[newbasis](*,Print["not enough"]*)]];(*Print["return=",newbasis];*)Return@Return@Return[newbasis]
];
If[Length@current>1,(*Print["before current>1",newbasis];*)newbasis=testPair[templist2,tempcurrent2,tempremain2,tensor,other,newbasis,ampbasis,num,doubleindex->OptionValue[doubleindex],AdlerZero->OptionValue[AdlerZero]](*;Print["after current>1",newbasis]*),(*Print["tempremain2=",tempremain2];*)
If[Length@tempremain2==1,Return@Return@Return[newbasis]];newbasis=testPair[templist2,tempremain2[[1]],tempremain2[[2;;]],tensor,other,newbasis,ampbasis,num,doubleindex->OptionValue[doubleindex],AdlerZero->OptionValue[AdlerZero]](*;Print[newbasis]*)
];If[i===Length@tempremain&&j===Length@tempremain[[i]],Return@Return@Return[newbasis]](*;Print["newbasis=",newbasis,i,j];Print[tempremain]*)
,{j,Length@tempremain[[i]]}
],{i,Length@tempremain}
]
];

DoubleContract[cont_,ilist_]:=If[ilist==={},cont,cont/.{{x_,y_}/;(!Cases[ilist,x|y]==={}):>c4[x,y,x+1,y+1]}//.{{aa___,c4[x_,y_,z_,v_],bb___}:>If[SubsetQ[ilist,{x}]&&SubsetQ[ilist,{y}],{aa,{x,y},{z,v},bb},{}]}];


(*tensor2state[tensor_,other_,num_]:=Module[{state,tenlist,k},If[tensor[[0]]===List,Return[tensor2state[tensor\[LeftDoubleBracket]1\[RightDoubleBracket],num]]];state=Table[0,{i,num}];If[other\[LeftDoubleBracket]0\[RightDoubleBracket]===Times,tenlist=Join[List@@tensor,List@@other],tenlist=Join[List@@tensor,{other}]];k=Count[tenlist,_de];tenlist=DeleteCases[tenlist,_de|Subscript[\[Phi], _]];Do[Switch[ten,_F,If[Length[ten]===1,state\[LeftDoubleBracket]ten\[LeftDoubleBracket]1\[RightDoubleBracket]\[RightDoubleBracket]=-1,state\[LeftDoubleBracket]ten\[LeftDoubleBracket]1\[RightDoubleBracket]\[RightDoubleBracket]=1],_CL,If[Length[ten]===1,state\[LeftDoubleBracket]ten\[LeftDoubleBracket]1\[RightDoubleBracket]\[RightDoubleBracket]=-2,state\[LeftDoubleBracket]ten\[LeftDoubleBracket]1\[RightDoubleBracket]\[RightDoubleBracket]=2],_ch\[Psi]|_sigma|_sigma2,Do[Switch[ten\[LeftDoubleBracket]fe,1\[RightDoubleBracket],\[Psi],state\[LeftDoubleBracket]ten\[LeftDoubleBracket]fe,2\[RightDoubleBracket]\[RightDoubleBracket]=-1/2,Overscript[\[Psi], _],state\[LeftDoubleBracket]ten\[LeftDoubleBracket]fe,2\[RightDoubleBracket]\[RightDoubleBracket]=1/2],{fe,{1,-1}}],_,Print["coefficients|scalars"]],{ten,tenlist}];{state,k}];*)

Options[testLorBasis]={doubleindex->{},AdlerZero->False};
testLorBasis[tensor_,other_,indgroup_,state_,k_,OptionsPattern[]]:=
	Module[{result,input,ampbasis,lbasis,coor,gen1,gen2,num=Length@state},(*{state,k}=tensor2state[tensor,other,num];Print[{state,k}];*)
		ampbasis=SSYT[state,k,OutMode->"amplitude"];
		lbasis=If[OptionValue[AdlerZero]===False,Length[ampbasis],SoftBlocks[state,k,OptionValue[AdlerZero]]//Length];
		Print["find ",Dynamic[lnewbasis],"/",lbasis," basis"];
		If[tensor[[0]]===List,
			Print["find ",Dynamic[ltensor],"/",Length[tensor]," tensors"];
			input=Reverse@SortBy[#,Length@#&]&/@indgroup;
			result=Catch[testPair[{},input,{},tensor,other,{},ampbasis,num,doubleindex->OptionValue[doubleindex],AdlerZero->lbasis]],
			input=Reverse@SortBy[indgroup,Length@#&];
			result=Catch[testPair[{},firs@input,Ex1@input,tensor,other,{},ampbasis,num,doubleindex->OptionValue[doubleindex],AdlerZero->lbasis]]
		];(*Print[result];*)
		Return[<|"LorBasis"->result,"Trans"->(FindCor[reduce[Amp[#],num],ampbasis]&/@result)|>];If[OptionValue[AdlerZero]===False,Return[result],Print[result];coor=FindCor[reduce[Amp[#],num],ampbasis]&/@result;gen1=LinearSolve[coor\[Transpose],FindCor[YPermute[#.ampbasis,Cycles[{OptionValue[AdlerZero][[{1,2}]]}],num],ampbasis]]&/@coor;
gen2=LinearSolve[coor\[Transpose],FindCor[YPermute[#.ampbasis,Cycles[{OptionValue[AdlerZero]}],num],ampbasis]]&/@coor;
result=AssociationMap[Part[result,basisReduce[PermRepFromGenerator[{gen1,gen2},YO[#]]]["pos"]]&,IntegerPartitions[Length[OptionValue[AdlerZero]]]];
Return[Select[result,#!={}&]]]]


(* ::Section:: *)
(*From states to TensorContract*)


last[lis_List]:=If[lis==={},0,Last[lis]];
firs[lis_List]:=If[lis==={},{},First[lis]];
Ex1[lis_List]:=If[Length@lis<2,{},lis[[2;;]]];
Options[state2tensor]={AdlerZero->False};
state2tensor[state_,k_,OptionsPattern[]]:=Module[{hpart=<|-2->{},-1->{},-1/2->{},0->{},1/2->{},1->{},2->{}|>,tensorcontract=<|"tensor"->{},"contract"->Table[{i},{i,k}],"other"->1|>,Indices=k,fermionpair,si2pair,sipair,fermtensor={},fermcont={},fermother={},fermcur=<|-1/2->{},1/2->{}|>,fermtensor2={},fermcont2={},fermother2={},l\[Gamma],deri},
Do[hpart[h]=Position[state,h]//Flatten;
Switch[h,
-2,AppendTo[tensorcontract["tensor"],CL[#]]&/@hpart[h];Do[AppendTo[tensorcontract["contract"],Table[Indices+i,{i,4}]];Indices+=4,{j,hpart[h]}],2,AppendTo[tensorcontract["tensor"],CL[#,"b"]]&/@hpart[h];Do[AppendTo[tensorcontract["contract"],Table[Indices+i,{i,4}]];Indices+=4,{j,hpart[h]}],-1,AppendTo[tensorcontract["tensor"],F[#]]&/@hpart[h];Do[AppendTo[tensorcontract["contract"],Table[Indices+i,{i,2}]];Indices+=2,{j,hpart[h]}],1,AppendTo[tensorcontract["tensor"],F[#,"b"]]&/@hpart[h];Do[AppendTo[tensorcontract["contract"],Table[Indices+i,{i,2}]];Indices+=2,{j,hpart[h]}],0,tensorcontract["other"]*=Times@@(Subscript[\[Phi], #]&/@hpart[h])],{h,{-2,-1,-1/2,0,1/2,1,2}}];tensorcontract["tensor"]=TensorProduct@@(tensorcontract["tensor"]//Flatten);(*Print[tensorcontract];*)
Switch[{hpart[-1/2],hpart[1/2]},
{{__},{}},fermionpair=Union@Map[Union,Partition[#,2]&/@Permutations[hpart[-1/2]],2];Do[Do[si2pair=Subsets[pa,{si2num}];sipair=Complement[pa,#]&/@si2pair;Do[AppendTo[fermtensor,TensorProduct@@(sigma2[Subscript[\[Psi], #[[1]]],Subscript[\[Psi], #[[2]]]]&/@si2pair[[inum]])];AppendTo[fermother,Times@@(ch\[Psi][Subscript[\[Psi], #[[1]]],1,Subscript[\[Psi], #[[2]]]]&/@sipair[[inum]])];AppendTo[fermcont,Table[{Indices+i,Indices+i+1},{i,1,2Length[si2pair[[inum]]]-1,2}]],{inum,Length[si2pair]}],{si2num,0,2}],{pa,fermionpair}],
{{},{__}},fermionpair=Union@Map[Union,Partition[#,2]&/@Permutations[hpart[1/2]],2];Do[Do[si2pair=Subsets[pa,{si2num}];sipair=Complement[pa,#]&/@si2pair;(*Print[sipair];*)Do[AppendTo[fermtensor,TensorProduct@@(sigma2[Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[1]]],Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[2]]]]&/@si2pair[[inum]])];AppendTo[fermother,Times@@(ch\[Psi][Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[1]]],1,Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[2]]]]&/@sipair[[inum]])];AppendTo[fermcont,Table[{Indices+i,Indices+i+1},{i,1,2Length[si2pair[[inum]]]-1,2}]],{inum,Length[si2pair]}],{si2num,0,2}],{pa,fermionpair}],
{{__},{__}},fermcur[-1/2]=Subsets[hpart[-1/2],{Min[Length[hpart[-1/2]],Length[hpart[1/2]]]}];fermcur[1/2]=Subsets[hpart[1/2],{Min[Length[hpart[-1/2]],Length[hpart[1/2]]]}];(*Print[fermcur];*)If[Length[fermcur[-1/2]]>1,Do[fermionpair=MapThread[{#1,#2}&,#]&/@(Append[fermcur[1/2],#]&/@Permutations[lcur]);Do[AppendTo[fermtensor,TensorProduct@@(sigma[Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[1]]],Subscript[\[Psi], #[[2]]]]&/@pa)];AppendTo[fermother,1];AppendTo[fermcont,Table[{Indices+i},{i,Length[pa]}]],{pa,fermionpair}];l\[Gamma]=Length@fermionpair;(*Print[{fermtensor,fermcont,fermother}];*)fermionpair=Union@Map[Union,Partition[#,2]&/@Permutations[Complement[hpart[-1/2],lcur]],2];(*Print[fermionpair];*)
Do[Do[si2pair=Subsets[pa,{si2num}];sipair=Complement[pa,#]&/@si2pair;Do[AppendTo[fermtensor2,TensorProduct@@(sigma2[Subscript[\[Psi], #[[1]]],Subscript[\[Psi], #[[2]]]]&/@si2pair[[inum]])];AppendTo[fermother2,Times@@(ch\[Psi][Subscript[\[Psi], #[[1]]],1,Subscript[\[Psi], #[[2]]]]&/@sipair[[inum]])];AppendTo[fermcont2,Table[{Indices+Length[fermcur[1/2][[1]]]+i,Indices+Length[fermcur[1/2][[1]]]+i+1},{i,1,2Length[si2pair[[inum]]]-1,2}]],{inum,Length[si2pair]}],{si2num,0,2}],{pa,fermionpair}];Print[{fermtensor2,fermcont2,fermother2}];fermtensor[[-l\[Gamma];;]]=Times[#,fermtensor2]&/@fermtensor[[-l\[Gamma];;]]/.{Times->TensorProduct}//Flatten;fermother[[-l\[Gamma];;]]=Times[#,fermother2]&/@fermother[[-l\[Gamma];;]]//Flatten;Do[fermcont[[-l\[Gamma];;,icon]]=Join[fermcont[[-l\[Gamma];;,icon]],#]&/@fermcont2,{icon,Length[fermcont[[-l\[Gamma];;]]]}];fermcont[[-l\[Gamma];;]]=Flatten[fermcont[[-l\[Gamma];;]],1];fermtensor2=fermother2=fermcont2={},{lcur,fermcur[-1/2]}],(*******************)Do[fermionpair=MapThread[{#1,#2}&,#]&/@(Append[fermcur[-1/2],#]&/@Permutations[lcur]);Do[AppendTo[fermtensor,TensorProduct@@(sigma[Subscript[\[Psi], #[[1]]],Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[2]]]]&/@pa)];AppendTo[fermother,1];AppendTo[fermcont,Table[{Indices+i},{i,Length[pa]}]],{pa,fermionpair}];l\[Gamma]=Length@fermionpair;Print[{fermtensor,fermcont,fermother}];fermionpair=Union@Map[Union,Partition[#,2]&/@Permutations[Complement[hpart[1/2],lcur]],2];Print[fermionpair];If[Length[fermcur[1/2]]>1,Do[Do[si2pair=Subsets[pa,{si2num}];sipair=Complement[pa,#]&/@si2pair;Do[AppendTo[fermtensor2,TensorProduct@@(sigma2[Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[1]]],Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[2]]]]&/@si2pair[[inum]])];AppendTo[fermother2,Times@@(ch\[Psi][Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[1]]],1,Subscript[\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #[[2]]]]&/@sipair[[inum]])];AppendTo[fermcont2,Table[{Indices+Length[fermcur[1/2][[1]]]+i,Indices+Length[fermcur[1/2][[1]]]+i+1},{i,1,2Length[si2pair[[inum]]]-1,2}]],{inum,Length[si2pair]}],{si2num,0,2}],{pa,fermionpair}];(*Print[{fermtensor2,fermcont2,fermother2}];*)fermtensor[[-l\[Gamma];;]]=Times[#,fermtensor2]&/@fermtensor[[-l\[Gamma];;]]/.{Times->TensorProduct}//Flatten;fermother[[-l\[Gamma];;]]=Times[#,fermother2]&/@fermother[[-l\[Gamma];;]]//Flatten;Do[fermcont[[-l\[Gamma];;,icon]]=Join[fermcont[[-l\[Gamma];;,icon]],#]&/@fermcont2,{icon,Length[fermcont[[-l\[Gamma];;]]]}];fermcont[[-l\[Gamma];;]]=Flatten[fermcont[[-l\[Gamma];;]],1];fermtensor2=fermother2=fermcont2={}],{lcur,fermcur[1/2]}](***************)];If[fermtensor[[1,0]]===List,fermtensor=Flatten[fermtensor,1];fermother=Flatten[fermother,1];fermcont=Flatten[fermcont,1]]
(*Do[fermcur[-1/2]=Subsets[hpart[-1/2],{\[Gamma]num}];fermcur[1/2]=Subsets[hpart[1/2],{\[Gamma]num}];Do[fermionpair=Union@Map[Union,Partition[#,2]&/@Permutations[Complement[hpart[-1/2],fermcur[-1/2]\[LeftDoubleBracket]icur\[RightDoubleBracket]]],2];Do[Do[si2pair=Subsets[pa,{si2num}];sipair=Complement[pa,#]&/@si2pair;Do[AppendTo[fermtensor,TensorProduct@@(sigma2[Subscript[\[Psi], #[[1]]],Subscript[\[Psi], #[[2]]]]&/@si2pair\[LeftDoubleBracket]inum\[RightDoubleBracket])];AppendTo[fermother,Times@@(ch\[Psi][Subscript[\[Psi], #[[1]]],1,Subscript[\[Psi], #[[2]]]]&/@sipair\[LeftDoubleBracket]inum\[RightDoubleBracket])];AppendTo[fermcont,Table[{Indices+i,Indices+i+1},{i,1,2Length[si2pair\[LeftDoubleBracket]inum\[RightDoubleBracket]]-1,2}]],{inum,Length[si2pair]}],{si2num,0,2}],{pa,fermionpair}],{icur,Length[fermcur[-1/2]]}],{\[Gamma]num,If[EvenQ@Length[hpart[-1/2]],0,1],Min[Length[hpart[-1/2]],Length[hpart[1/2]]]}]*)];(*Print[fermcont];*)If[!fermtensor==={},tensorcontract["tensor"]=TensorProduct@@@({tensorcontract["tensor"],#}&/@fermtensor);tensorcontract["contract"]=Join[tensorcontract["contract"],#]&/@fermcont;tensorcontract["other"]=Times@@@({tensorcontract["other"],#}&/@fermother);]If[k>0,deri=MultDeriTensor[Length[state],k,AdlerZero->OptionValue[AdlerZero]];fermtensor={};fermcont={};fermother={};
If[!tensorcontract["tensor"][[0]]===List,tensorcontract=List/@tensorcontract];Do[fermtensor=Join[fermtensor,TensorProduct@@@({#,tensorcontract["tensor"][[lt]]}&/@deri)];fermcont=Join[fermcont,ConstantArray[tensorcontract["contract"][[lt]],Length@deri]];fermother=Join[fermother,ConstantArray[tensorcontract["other"][[lt]],Length@deri]],{lt,Length[tensorcontract["tensor"]]}];tensorcontract["tensor"]=fermtensor;tensorcontract["contract"]=fermcont;tensorcontract["other"]=fermother];If[!tensorcontract["tensor"][[0]]===List,tensorcontract=List/@tensorcontract];tensorcontract["tensor"]=Join[tensorcontract["tensor"],TensorProduct[#,epsilon]&/@tensorcontract["tensor"]];tensorcontract["contract"]=Join[tensorcontract["contract"],(Append[#,{last@Flatten[#]+1,last@Flatten[#]+2,last@Flatten[#]+3,last@Flatten[#]+4}]&@#)&/@tensorcontract["contract"]];tensorcontract["other"]=Join[tensorcontract["other"],tensorcontract["other"]];tensorcontract];

(*prodDeri[kk_,particles_List]:=Module[{deri},deri=ConstantArray[de,kk];Do[deri[[i]]=de[particles[[i]]],{i,kk}];deri/.{List\[Rule]TensorProduct}];*)
Options[MultDeriTensor]={AdlerZero->False};
MultDeriTensor[num_,k_,OptionsPattern[]]:=Module[{kk,ad=1},If[OptionValue[AdlerZero]===False,kk=k,kk=k-Length@OptionValue[AdlerZero];ad=Sum[de[i],{i,OptionValue[AdlerZero]}]/.{Plus->TensorProduct}(*;Print[ad]*)];Switch[kk,0,kk={1},1,kk=Expand[Sum[de[i],{i,num}]]//.{Plus->List},_,kk=TensorProduct@@@(DeleteCases[#,_Integer]&/@Flatten/@(Expand[Sum[de[i],{i,num}]^kk]//.{Plus->List,Times->List,Power->ConstantArray}))];TensorProduct[ad,#]&/@kk]


(* ::Section:: *)
(*From states to LorBasis*)


Options[LorBasis]={doubleindex->{},AdlerZero->False,spurion->False};
LorBasis[state_,k_,OptionsPattern[]]:=Module[{tens,stat},If[OptionValue[spurion]===False,stat=state,stat=Delete[state,List/@OptionValue[spurion]]];tens=state2tensor[stat,k,AdlerZero->OptionValue[AdlerZero]];(*Print[tens];*)
testLorBasis[tens["tensor"],tens["other"],tens["contract"],stat,k,doubleindex->OptionValue[doubleindex],AdlerZero->OptionValue[AdlerZero]]]
