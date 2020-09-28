(* ::Package:: *)

$AmplitudeBasisDir = FileNameDrop[$InputFileName,-1];
$CodeFiles=FileNames[__~~".m",FileNameJoin[{$AmplitudeBasisDir,"Code"}]];


(* ::Input::Initialization:: *)
BeginPackage["AmplitudeBasis`"]

(* General *)
{tAssumptions,tRep,tOut,tVal,tYDcol,tSimp,dummyIndexCount,GellMann,ab,sb,SSYT,reduce};

(* Model Input *)
{AddGroup,AddField,AllTypesR,AllTypesC,GetTypes,CheckType,CheckGroup};

(* Lorentz Factor *)
{LorentzBasisForType,LorentzCountForType,OperPoly};

(* Gauge Group Factor *)
{CountGroupFactor,GetGroupFactor,ConvertToFundamental};

(* Formating *)
{PrintTensor,Ampform,transform,Present};

(* j-basis *)
{W2,W2Diagonalize,Mandelstam};

(* Analysis *)
{Type2TermsPro,Type2TermsCount,StatResult,GenerateOperatorList};

(* Useful Lie groups in GroupMath *)
{U1,SU2,SU3,SU4,SU5,SU6};



(* ::Subsection:: *)
(*Configure*)


(* ::Input::Initialization:: *)
permutationBasis="left"; (* or "right" *)
groupList={};
h2f=<|-1->FL,-1/2->\[Psi],0->\[Phi],1/2->OverBar[\[Psi]],1->FR|>;
LorentzIndex={"\[Mu]","\[Nu]","\[Lambda]","\[Rho]","\[Sigma]","\[Eta]","\[Xi]","\[Tau]","\[Upsilon]","\[CurlyPhi]","\[Chi]","\[Psi]","\[Omega]"};
FLAVOR={"p","r","s","t","u","v","w","x","y","z"};


(* ::Input::Initialization:: *)
If[!Global`$DEBUG,Begin["`Private`"]]
Get/@Global`$CodeFiles;


(* ::Input::Initialization:: *)
(* Special Definitions *)
tAssumptions={};
tReduce:=TensorReduce[#,Assumptions->tAssumptions]&;
tRank:=TensorRank[#,Assumptions->tAssumptions]&;
tDimensions:=TensorDimensions[#,Assumptions->tAssumptions]&;
tSymmetry=TensorSymmetry[#,Assumptions->tAssumptions]&;


(* ::Subsection::Closed:: *)
(*Model Input*)


(* ::Input::Initialization:: *)
(* whether a field has the given helicity *)
helicityQ[model_,h_]:=model[#]["helicity"]==h&  
(* judge if reps of group in replist could form a singlet *)
SingletQ[group_,{rep__List}]:=MemberQ[MyRepProduct[group,{rep}][[All,1]],ConstantArray[0,Length[group]]] (* for non-Abelian groups *)
SingletQ[group_,{rep__?NumericQ}]:=Plus[rep]==0 (* for Abelian groups *)
(* get conjugate rep of a given rep *)
RepConj[rep_List]:=Reverse[rep] (* for non-Abelian reps *)
RepConj[charge_?NumericQ]:=-charge (* for Abelian charges *)
Conj[realOp_String]:=realOp (* operator names associate to conjugate operators -- themselves by default *)
realQ[type_]:=Module[{flist=Prod2List[type]},TrueQ[flist==Sort[Conj/@flist]]]
nonAbelian[groupname_]:=Length[CheckGroup[groupname]]>0 (* judge if a group is non-Abelian *)
Singlet[group_]:=Replace[group,_List->0,{Depth[group]-2}]
Fund[group_]:=ReplacePart[Singlet[group],1->1]
AFund[group_]:=ReplacePart[Singlet[group],-1->1]
CheckType[model_,type_,OptionsPattern[]]:=Module[{flist=DeleteCases[Prod2List[type],"D"],inModel},
inModel=KeyExistsQ[model,#]&/@flist;
If[Nand@@inModel,Message[CheckType::unknown,type];Abort[]];
If[OptionValue[Sorted],flist=SortBy[flist,model[#]["helicity"]&]];
If[OptionValue[Counting],flist=Tally[flist]];
Return[flist];
]
Options[CheckType]={Sorted->True, Counting->True};
CheckType::unknown="unrecognized fields in type `1`";

CheckGroup[model_Association,groupname_String]:=Module[{group=ToExpression@StringDrop[groupname,-1]},If[MemberQ[groupList,group]&&MemberQ[model["Gauge"],groupname],group,Message[CheckGroup::ndef,groupname]]]
CheckGroup[groupname_String]:=Module[{group=ToExpression@StringDrop[groupname,-1]},If[MemberQ[groupList,group],group,Message[CheckGroup::ndef,groupname]]]
CheckGroup::ndef="Group `1` not defined.";

(* Names for Abstract Fields *)
state2class=D^#2 Times@@Power@@@MapAt[h2f,Tally[#1],{All,1}]&;

Fields[model_]:=Keys@Select[model,MatchQ[#,_Association]&]
SetSimplificationRule[model_]:=Module[{group,indexset=Catenate@model["rep2indOut"]},
Unprotect[Times];Clear[Times];
Do[group=CheckGroup[model,groupname];Check[tSimp[group]/.{INDEXSET->indexset}//ReleaseHold,"simplification rule for "<>ToString[groupname]<>" not found"],{groupname,model["Gauge"]}];
Protect[Times]
]


(* ::Input::Initialization:: *)
SetAttributes[{AddGroup,AddField},HoldFirst];
(* Adding new Gauge Group to a Model *)
AddGroup[model_,groupname_String,field_String,Globalreps_List,ind_Association]:=Module[{profile,group=ToExpression@StringDrop[groupname,-1],Freps},
(* read group info from profile *)
If[!MemberQ[groupList,group],
profile=FileNameJoin[{Global`$AmplitudeBasisDir,"GroupProfile",StringDrop[groupname,-1]<>"_profile.m"}];
If[FileExistsQ[profile],Get[profile],Message[AddGroup::profile,StringDrop[groupname,-1]];Abort[]];
];

model=Merge[{model,<|"Gauge"->{groupname}|>},Apply[Join]]; (* add gauge group to the model *)
AssociateTo[model[#],groupname->Singlet[group]]&/@Fields[model]; (* pre-existing fields set to singlet by default *)
Freps=MapAt[Adjoint,MapAt[Singlet,CheckGroup/@model["Gauge"],{;;-2}],-1]; (* gauge boson representations under all groups *)
AddField[model,field<>"L",-1,Freps,Globalreps,Hermitian->True];
AddField[model,field<>"R",1,Freps,Globalreps,Hermitian->True]; (* add gauge bosons *)
Conj[field<>"L"]=field<>"R";
Conj[field<>"R"]=field<>"L"; (* define special conjugation relation (not denoted by \[Dagger]) for gauge boson names *)
AssociateTo[model["rep2ind"],groupname->First/@ind]; (* define abstract working index names for all reps of the new group *)
AssociateTo[model["rep2indOut"],groupname->Last/@ind]; (* define list of specific indices for all reps of the new group *)
SetSimplificationRule[model] (* define simplification rules for all gauge groups *)
]
AddGroup::profile="Profile for group `1` not found.";

(* Adding New Field to a Model *)
AddField::overh="helicity of `1` is neither integer nor half-integer.";
Options[AddField]={Flavor->1,Hermitian->False,Chirality->{}};
AddField[model_,field_String,hel_,Greps_List,Globalreps_List,OptionsPattern[]]:=Module[{attribute=<||>,flavor=OptionValue[Flavor],NAgroups,shape},
If[IntegerQ[2hel],AppendTo[attribute,"helicity"->hel],Message[AddField::overh,field]];
AssociateTo[attribute,Thread[model["Gauge"]->Greps]];
AssociateTo[attribute,Thread[model["Global"]->Globalreps]];
Switch[flavor,
_Integer,AssociateTo[attribute,{"nfl"->flavor,"indfl"->FLAVOR}],
_List,AssociateTo[attribute,{"nfl"->flavor[[1]],"indfl"->flavor[[2]]}]];
AssociateTo[attribute,"stat"->If[IntegerQ[hel],"boson","fermion"]];
If[attribute["stat"]=="fermion" ,AssociateTo[attribute,"chirality"->OptionValue[Chirality]]];
AppendTo[model,field->attribute];

NAgroups=Select[model["Gauge"],nonAbelian];
shape=MapThread[DimR[#1,#2]&,{CheckGroup/@NAgroups,Cases[Greps,_List]}];
AppendTo[tAssumptions,ToExpression["t"<>field<>ToString[NAgroups[[#]]]]\[Element]Arrays[{shape[[#]]}]]&/@Range[1,Length[shape]];

If[!OptionValue[Hermitian]&&Last@Characters[field]!="\[Dagger]",AddField[model,field<>"\[Dagger]",-hel,RepConj/@Greps,RepConj/@Globalreps,Flavor->OptionValue[Flavor],Chirality->(OptionValue[Chirality]/.{"left"->"right","right"->"left"})];
Conj[field]=field<>"\[Dagger]";
Conj[field<>"\[Dagger]"]=field;
];
]


(* ::Input::Initialization:: *)
(* for a given helicity state, find (more than) all field combinations in a model that match the helicities and form singlets for all groups *)
state2type[model_,state_,k_]:=Module[{comblist,groups=CheckGroup/@model["Gauge"],singletposition},
(* state: list of helicities for particles in a scattering 
k: number of extra momenta/derivatives
*)
(* field combinations in the model with given helicities *)
comblist=DeleteDuplicatesBy[Distribute[Select[Keys[model],helicityQ[model,#]]&/@state,List],Sort]; 
(* find singlet combinations *)
singletposition=Flatten@Position[MapThread[And,Table[SingletQ[groups[[i]],#]&/@Map[model[#][model["Gauge"][[i]]]&,comblist,{2}],{i,Length[groups]}]],True]; 
(* convert to types: product of fieldname/D strings *)
Times@@@(PadRight[#,Length[state]+k,"D"]&/@comblist[[singletposition]] )(* convert format for AmplitudeBasis *)
] 
AllTypesR[model_,dim_]:=state2type[model,#1,#2]&@@@LorentzList[dim,"real"]//Flatten
AllTypesC[model_,dim_]:=Module[{statelist=LorentzList[dim,"complex"],types,result={}},
Do[types=state2type[model,#1,#2]&@@state;
If[state==MapAt[-Reverse[#]&,state,1],
types=DeleteDuplicates[types,(#1/.{x_String/;x!= "D":>Conj[x]})==#2&]
];
AppendTo[result,types],
{state,statelist}];
Return[result];
]
GetTypes[model_,dmin_,dmax_,file_]:=Module[{dim,types={}},
Do[AppendTo[types,Timing@AllTypesC[model,dim]];
Print["Dim ",dim,": ",Length[Flatten@#2]," types in all, time used ",#1]&@@Last[types],
{dim,Range[dmin,dmax]}];
Put[types[[All,2]],NotebookDirectory[]<>file];
Return[types[[All,2]]];
]
GetTypes[model_,dim_,file_]:=GetTypes[model,dim,dim,file]


(* ::Input::Initialization:: *)
(* Global Charge Analysis *)
BminusL[model_,types_]:=
Module[{},
GroupBy[Flatten@types,(Abs@Total[Times@@@MapAt[(model[#]["Baryon"]-model[#]["Lepton"])&,CheckType[model,#],{All,1}]])&]
]
BLofAll[model_,dim_]:=Module[{types},types=Flatten@AllTypesC[model,dim];
GroupBy[Flatten@types,(Total[Times@@@MapAt[{model[#]["Baryon"],model[#]["Lepton"]}&,CheckType[model,#],{All,1}]])&]
]



(* ::Subsection:: *)
(*Lorentz Basis*)


(* ::Input::Initialization:: *)
(* Symmetrize the list of amplitudes Mlist according to ALL possible Irreps of permutations for RepFields, and show result under basis StBasis *)
Options[PermBasis]={Coord->False};
PermBasis[Mlist_,RepPos_,Num_,OptionsPattern[]]:=PermBasis[Mlist,RepPos,Num]=
Module[{depth=Length[RepPos],Dim=Length[Mlist],SymList,yngList,permAmp,permResult=<||>,SnDimlist={},emptySpaceCor,j,var,ynglist,allbasis,allbasisCor,poslist},
If[depth==0,Return[<|{}->If[OptionValue[Coord],IdentityMatrix[Length[Mlist]],Mlist]|>]];
var=ToExpression/@("SnX"<>#&/@ToString/@Range[depth]); (* abstract index for each Snrep *)

yngList=Distribute[Thread[{IntegerPartitions@Length[#],First[#]}]&/@RepPos,List];
Do[SnDimlist=SnIrrepDim/@yngList[[i,All,1]]; (* tensor dimensions of Snrep space *)
If[Dim<Times@@SnDimlist,Continue[]];
For[emptySpaceCor=ConstantArray[0,Length[Mlist]];j=0,j<depth,j++,
emptySpaceCor=ConstantArray[emptySpaceCor,SnDimlist[[depth-j]]]
];  (* Coordinate for projected out irrep spaces *)
ynglist=MapThread[Append[#1,#2]&,{yngList[[i]],var}]; (* abstract ynglist for each basis vector in Snrep *)
allbasis=Hold@Table@@Evaluate[Join[{Hold@YPermute[Mlist,pp[YO@@@ynglist],Num]},Evaluate[{var,SnDimlist}\[Transpose]]]]; (* permute to get all basis vector *)
allbasisCor=Transpose[Map[FindCor[#,Mlist]&,ReleaseHold[allbasis],{depth+1}],Append[Range[2,depth+1],1]]/.emptySpaceCor->Nothing; 
(* get coordinates of all basis vactors *)
If[Flatten@allbasisCor!={},
poslist=basisReduce[Extract[ConstantArray[1,depth]]/@allbasisCor]["pos"]; (* get positions of independent basis *)
AssociateTo[permResult,First/@yngList[[i]]->allbasisCor[[poslist]]]; (* find independent Snrep spaces and associate to permResult *)
Dim -= Length[poslist]* Times@@SnDimlist;
],
{i,Length[yngList]}];

If[OptionValue[Coord],
Return[permResult], (* return the coordinates under original Mlist basis *) 
Return[#.Mlist&/@permResult] (* return the amplitudes *)  
]; 
]

Options[LorentzBasisForType]={OutputFormat->"operator",Coord->False,FerCom->2,OpenFchain->True,ActivatePrintTensor->True};
LorentzBasisForType[model_,type_,OptionsPattern[]]:=Module[{particles,fieldsReplace,k,state,RepFields,Num,Mlist,resultCor,amp2op,OpBasis},
k=Exponent[type,"D"];
particles=CheckType[model,type,Counting->False];
RepFields=Select[PositionIndex[particles],Length[#]>1&];
state=model[#]["helicity"]&/@particles;
Num=Length[state];

Mlist=SSYT[state,k,OutMode->"amplitude"];
(* generate initial amplitude basis from SSYT *)
resultCor=KeyMap[Thread@Rule[Keys[RepFields],#]&,PermBasis[Mlist,Values@RepFields,Num,Coord->True]];

Switch[OptionValue[OutputFormat],
(* Output amplitude basis *)
"amplitude",If[OptionValue[Coord],
<|"basis"->Ampform/@Mlist,"coord"->resultCor|>,
Map[#.Mlist&,resultCor,{2+Length[RepFields]}]],  
(* Output operator basis *)
"operator",amp2op=MonoLorentzBasis[Mlist,Num,finalform->False];
OpBasis=transform[amp2op["LorBasis"],ReplaceField->{model,type,OptionValue[FerCom]},OpenFchain->OptionValue[OpenFchain],ActivatePrintTensor->OptionValue[ActivatePrintTensor]];
If[OptionValue[Coord],
<|"basis"->OpBasis,"coord"->Map[Inverse[amp2op["Trans"]]\[Transpose].#&,resultCor,{2+Length[RepFields]}]|>, (* output <|basis, coord|> *)
Map[Expand[OpBasis.Inverse[amp2op["Trans"]]\[Transpose].#]&,resultCor,{2+Length[RepFields]}] (* output basis.coord *)
]
]
] 

LorentzCountForType[model_,type_]:=Module[{particles,k,state,RepFields,Num,grank,group,X,p,rep,irrepComb,AllSym},
particles=CheckType[model,type,Counting->False];
k=Exponent[type,"D"];
RepFields=Select[PositionIndex[particles],Length[#]>1&];
state=model[#]["helicity"]&/@particles;
Num=Length[state];
grank=If[Num>3,Num-2,Num];
{nt,n}=yngShape[state,k]; (* young tab info *)
If[nt==0&&n==0,Return[<|Normal[{Length[#]}&/@RepFields]->1|>]];
group=ToExpression["SU"<>ToString[grank]];
rep=Yng2Dynk[group,Length/@(YDzero[Num,nt,n]//TransposeTableaux)]; (* target irrep *)
irrepComb=FindIrrepCombination[group,MapThread[{PadRight[Count[Flatten@Table[ConstantArray[i,nt-2state[[i]]],{i,Num}],#]&/@FirstPosition[particles,#1],grank-1],#2}&,Tally[particles]\[Transpose]],rep][[2;;]]\[Transpose]; (* Main step: apply FindIrrepCombination *)
AllSym=Flatten[ConstantArray[Distribute[Join@@@Apply[ConstantArray,#1,{2}],List],#2]&@@@irrepComb,2]/.{1}->Nothing; (* list all combinations of syms *)
KeyMap[Map[If[OddQ[nt],MapAt[TransposeYng,#,2],#]&],Association[Rule@@@Tally[Thread[Keys[RepFields]->#]&/@AllSym]]]  (* counting and form association, taking transposition of young diagrams when #\[Epsilon] is odd *)
]


(* ::Subsection::Closed:: *)
(*Gauge Group Factor*)


(* ::Input::Initialization:: *)
CountGroupFactor[model_,groupname_,type_]:=Module[{flist=CheckType[model,type],group=CheckGroup[groupname],repfs,relist,sym},
repfs=Cases[flist,{name_String,x_/;x>1}:>name];
relist=FindIrrepCombination[group,MapAt[model[#][groupname]&,#,1]&/@flist,ConstantArray[0,Length[group]]];(* apply FindIrrepCombination *)
sym={DeleteCases[#[[All,1]],{1}],Times@@#[[All,2]]}&/@Distribute[#,List]&/@relist[[2]]; (* collect multiplicity for SUN combinations respectively *)
sym=Join@@MapThread[MapAt[Function[x,#2 x],#1,{All,2}]&,{sym,relist[[3]]}]; 
sym=Merge[Rule@@@sym,Apply[Plus]];(* combine multiplicity from SUM combinations *)
Return[KeyMap[MapThread[Rule,{repfs,#}]&,sym]](* attach repeated field names *)
]


(* ::Input::Initialization:: *)
ConvertToFundamental[model_,groupname_,fname_]:=Module[{rep=model[fname][groupname],convert},
convert=ConvertToFundamental[model,groupname,rep];
If[CheckGroup[model,groupname]==SU2&&rep=={1},
If[StringTake[fname,-1]=="\[Dagger]",Return[convert[[2]]],Return[convert[[1]]]],
Return[convert]];
]
ConvertToFundamental::name="`1` does not have the representation `2`.";

ConvertFactor[model_,groupname_,input_]:=
(*input is the form {field,num}, *)
Module[{fname=input[[1]],num=input[[2]]},
Product[Times@@Map[If[MatchQ[#,1|_dummyIndex],#,Fold[Prepend,#,{i,fname}]]&,Prod2List@ConvertToFundamental[model,groupname,fname],{2}],{i,num}]
]


(* ::Input::Initialization:: *)
SNirrepAuX[input_]:={#[[All,1]],input[[3]]*Times@@#[[All,2]]}&/@Distribute[input[[2]],List]
(* SNirrepAux[{SUNrepeatrep,SNreps,multi}] = {{SNrep_comb,total_multiplicity},...} *)

GetGroupFactor[model_,groupname_,type_,OptionsPattern[]]:=Module[{flist=CheckType[model,type],group=ToExpression@StringDrop[groupname,-1],
SUNreplist,repeatlist,nonsinglets,repeatnonsinglets,repeatsinglets,
displacements,indexlist,Irreplist,SNCollections,nonSingletSN,convertfactor,YDbasis,Mbasis,MbasisAll,tMbasis,tMbasisAll,vMbasis,vMbasisAll,
qr,tdims,coords},
SUNreplist={#[[2]],model[#[[1]]][groupname],#[[1]]}&/@flist; (* {repeat_num, SUNrep, fieldname} *)
repeatlist=Select[SUNreplist,#[[1]]>1&];
nonsinglets=DeleteCases[SUNreplist,{_,Singlet[group],_}];
repeatnonsinglets=DeleteCases[repeatlist,{_,Singlet[group],_}];
repeatsinglets=Cases[repeatlist,{_,Singlet[group],_}];
If[nonsinglets=={},Return[<|"basis"->{1},"coord"-><|(#[[3]]->{#[[1]]}&/@repeatlist)->Nest[List,1,Length[repeatlist]+2]|>|>]];(* return when all fields are singlets *)
displacements=AssociationThread[nonsinglets[[All,3]]->Most@Prepend[Accumulate[nonsinglets[[All,1]]],0]];
indexlist=GenerateFieldIndex[model,groupname,flist];(*Pick out the relevant SU3 indices in order*)
Irreplist=Transpose@FindIrrepCombination[group,SUNreplist[[All,{2,1}]],Singlet[group]]; (* {SUNrepeatrep,SNreps,multi} *)
SNCollections=Normal@Merge[Thread[SUNreplist[[All,3]]->#[[1]]]->#[[2]]&/@SNirrepAuX[#]&/@Irreplist,Total];(*get different SN syms and the corresponding multiplicity*)
SNCollections=MapAt[DeleteCases[#,_->{1}]&,SNCollections,{All,1}];(*retain only repeated fields*)
nonSingletSN=MapAt[Select[#,model[#[[1]]][groupname]!=Singlet[group]&]&,SNCollections,{All,1}];(*Select out SN syms of nonsinglet repeated fields *)

convertfactor=Times@@(ConvertFactor[model,groupname,#]&/@flist);
(*Select out nonsinglet fields for constructing singlet*)
YDbasis=Expand[Flatten[((Times@@(tYDcol[group]@@@Transpose[#]))&/@Map[ToExpression,GenerateLRT[model,groupname,nonsinglets],{2}])]*convertfactor];
MbasisAll=SimpGFV2[Expand/@TRefineTensor[YDbasis,model,groupname,flist]];
tMbasisAll=Product2ContractV2[#,indexlist,Symb2Num->tVal[group]]&/@MbasisAll;
vMbasisAll=Flatten/@tMbasisAll;
MapThread[Set,{{Mbasis,tMbasis,vMbasis},FindIndependentMbasis[MbasisAll,tMbasisAll,vMbasisAll]}];
If[MatrixRank[vMbasis]!=Length[vMbasis],Print["Warning: non-independent basis!!!!!"]];
Mbasis=Switch[OptionValue[OutputMode],
"working",Mbasis,
"tensor contract",Mbasis, (* needs implementation *)
"indexed",Map[Expand,Mbasis/.GenerateReplacingRule[model,type]],
"print",Map[Expand,Mbasis/.GenerateReplacingRule[model,type]]//RefineReplace];

If[Length@repeatlist==0,Return[<|"basis"->Mbasis,"coord"-><|{}->IdentityMatrix[Length[Mbasis]]|>|>]];
If[Length@repeatnonsinglets==0,Return[<|"basis"->Mbasis,"coord"-><|(#[[3]]->{#[[1]]}&/@repeatsinglets)->(Nest[List,#,Length[repeatlist]]&/@IdentityMatrix[Length[Mbasis]])|>|>]];

qr=QRDecomposition[Transpose[vMbasis]];
tdims=Map[SnIrrepDim,SNCollections[[All,1,All,2]],{2}];(*Get tensor dimensions of each SN syms*)
coords=AssociationThread[SNCollections[[All,1]]->MapThread[GetSymBasis[tMbasis,#1,displacements,qr,#2]&,{nonSingletSN,tdims}]];
<|"basis"->Mbasis,"coord"->coords|>
]
Options[GetGroupFactor]={OutputMode->"indexed"};


(* ::Subsection:: *)
(*Formating & Output*)


(* ::Subsubsection:: *)
(*Formating*)


(* ::Input::Initialization:: *)
(******************* Group tensor formating **********************)

(* getting printable form *)
(*PrintTensor="\!\(\*SubsuperscriptBox[\("<>#tensor<>"\), \("<>#downind<>"\), \("<>#upind<>"\)]\)"&;*)
PrintTensor[tensor_Association]:=Module[{srule={}},
Check[AppendTo[srule,"tensorname"->tensor["tensor"]],Message[PrintTensor::noname];Abort[]];
If[KeyExistsQ[tensor,"upind"],AppendTo[srule,"upind"->tensor["upind"]],AppendTo[srule,"upind"->""]];
If[KeyExistsQ[tensor,"downind"],AppendTo[srule,"downind"->tensor["downind"]],AppendTo[srule,"downind"->""]];
StringReplace[\!\(\*
TagBox[
StyleBox["\"\<\\!\\(\\*SubsuperscriptBox[\\(tensorname\\), \\(downind\\), \\(upind\\)]\\)\>\"",
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),srule]
]
PrintTensor[x_:Except[_Association]]:=x

Sortarg[asTlist_]:= #[y__] :> Signature[#[y]]Sort[#[y]]& /@ asTlist 
RefineReplace[x_]:=Module[{asTlist=Select[Keys@tOut,MatchQ[tSymmetry[#],_Antisymmetric]&]},
x/.Sortarg[asTlist]/.tOut]

IndexIterator[indlist_,indexct_]:=Module[{index=++indexct[indlist]},indlist[[index]]]
SetAttributes[IndexIterator,HoldRest];

(* Generate the replacing rule of the tensor indices for the final output form *)
GenerateReplacingRule[model_,type:(_Times|_Power)]:=GenerateReplacingRule[model,CheckType[model,type]]
GenerateReplacingRule[model_,flist_List]:=Module[{nonsingletlist,fexpand,symbollist,arglist,listind,listgen,indexct,indpair,listdummy},
nonsingletlist=AssociationMap[Function[groupname,Select[flist,Function[fname,model[fname[[1]]][groupname]!=Singlet[CheckGroup[groupname]]]]],Select[model["Gauge"],nonAbelian]]; 
fexpand=Flatten[ConstantArray@@@#]&/@nonsingletlist;
symbollist=KeyValueMap[Function[fname,model["rep2ind"][#1][model[fname[[1]]][#1]]]/@#2 &,nonsingletlist]; 
arglist=Map[Function[fname,Array[{fname[[1]],#,1}&,fname[[2]]]],nonsingletlist,{2}];
listind=Join@@MapThread[Function[{symbol,arg},symbol@@@arg],Catenate/@{symbollist,arglist}];

indexct=AssociationThread[Union@Catenate[model["rep2indOut"]]->0]; 
listgen=Join@@KeyValueMap[Function[{groupname,namelist},IndexIterator[model["rep2indOut"][groupname][model[#][groupname]],indexct]&/@namelist],fexpand]; 
indpair=Join@@Values@Merge[model/@{"rep2ind","rep2indOut"},Values[Merge[#,Identity]]& ]//DeleteDuplicates;
listdummy=Function[{ind,indexlist,ct},ind[ii_]:>indexlist[[ct+ii]]]@@@(Append[#,indexct[#[[2]]]]&/@indpair);
Return[Thread[listind->Flatten@listgen]~Join~listdummy];
]


(* ::Input::Initialization:: *)
(* Amplitude Formating *)

changebracket[b_ab]:=<|"tensor"->"<"<>StringJoin@@ToString/@b<>">"|>
changebracket[b_sb]:=<|"tensor"->"["<>StringJoin@@ToString/@b<>"]"|>
changebracket[s_sMand]:=<|"tensor"->"s","downind"-> StringJoin@@ToString/@s|>
changebracket[p_Power]:=Switch[p[[1]],
_ab|_sb|_sMand,Merge[{changebracket[p[[1]]],<|"upind"->ToString[p[[2]]]|>},StringJoin],
_,p]
changebracket[x_]:=x

Options[Ampform]={sVariable->True};
Ampform[amp_,OptionsPattern[]]:=Module[{lor=Expand[amp],coef},
If[OptionValue[sVariable],lor=lor//.{
ab[i_,j_]sb[i_,j_]:>-sMand[i,j],
ab[i_,j_]^n_ sb[i_,j_]:>-sMand[i,j] ab[i,j]^(n-1),
ab[i_,j_]sb[i_,j_]^n_:>-sMand[i,j] sb[i,j]^(n-1),
ab[i_,j_]^n_ sb[i_,j_]^m_:>-sMand[i,j] ab[i,j]^(n-1) sb[i,j]^(m-1)}];
Switch[Head[lor],
Times,PrintTensor[changebracket[#]]&/@lor,
Plus,Ampform/@lor,
_,PrintTensor[changebracket[lor]]]
]


(* Lorentz Structure formating *)


(* ::Input::Initialization:: *)
(* Operator formating *)
SetAttributes[SetIndex,HoldAll]; 
Options[SetIndex]={FieldRename->{}};
Options[groupindex]={FieldRename->{}};
SetIndex[model_, field_, label_,indexct_,flavorct_,OptionsPattern[]] :=
Module[{hel=model[field]["helicity"],fieldname=field,head=Identity,su2antiflag = False,irrep,group,indexList,index,tensorform}, 
If[model[field]["stat"]=="fermion"&&MemberQ[OptionValue[FieldRename],"set chirality"],
fieldname=model[field]["chirality"][[1]];
head=model[field]["chirality"][[2]];
If[head=="right",fieldname=\!\(\*
TagBox[
StyleBox[
RowBox[{"\"\<\\!\\(\\*OverscriptBox[\\(\>\"", "<>", "fieldname", "<>", "\"\<\\), \\(_\\)]\\)\>\""}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]];
tensorform=<|"tensor"->fieldname,"upind"->"","downind"->""|>;
If[model[field]["nfl"]>1, tensorform["downind"]= model[field]["indfl"][[++flavorct]];
tensorform["tensor"]=Inactive[PrintTensor]@tensorform;
tensorform["downind"]=""];
If[StringTake[field,-1] == "\[Dagger]", su2antiflag = True];
Do[irrep=model[field][groupname];
group=CheckGroup[model,groupname];
indexList=model["rep2indOut"][groupname][irrep];
If[indexList=={},Continue[]]; (* singlet *)
index=IndexIterator[indexList,indexct];
If[Fund[group]==irrep,If[group==SU2&&su2antiflag,tensorform["upind"]=tensorform["upind"]<>index,tensorform["downind"]=tensorform["downind"]<>index],
tensorform["upind"]=tensorform["upind"]<>index],
{groupname,Select[model["Gauge"],nonAbelian]}];
Subscript[h2f[hel], label] -> head[Inactive[PrintTensor][tensorform]]
]
groupindex[model_, flistexpand_,OptionsPattern[]] := Module[{indexct,flavorct=0, n= Length[flistexpand]},
indexct=AssociationThread[Union@Catenate[model["rep2indOut"]]->0];
MapThread[SetIndex[model, #1, #2,indexct,flavorct,FieldRename->OptionValue[FieldRename]] & , {flistexpand,Range[n]}]
]

spinorH2C={ch\[Psi]["left"[f1_],q_,"left"[f2_]]:>ch\[Psi][f1,"C",q,f2],
ch\[Psi][ch[p1__,"left"[f1_]],q_,"left"[f2_]]:>ch\[Psi][ch[p1,f1],"C",q,f2],
ch\[Psi]["left"[f1_],q_,ch[p2__,"left"[f2_]]]:>ch\[Psi][f1,"C",q,ch[p2,f2]],
ch\[Psi][ch[p1__,"left"[f1_]],q_,ch[p2__,"left"[f2_]]]:>ch\[Psi][ch[p1,f1],"C",q,ch[p2,f2]]}~Join~
{ch\[Psi]["right"[f1_],q_,"right"[f2_]]:>ch\[Psi][f1,q,"C",f2],
ch\[Psi][ch[p1__,"right"[f1_]],q_,"right"[f2_]]:>ch\[Psi][ch[p1,f1],q,"C",f2],
ch\[Psi]["right"[f1_],q_,ch[p2__,"right"[f2_]]]:>ch\[Psi][f1,q,"C",ch[p2,f2]],
ch\[Psi][ch[p1__,"right"[f1_]],q_,ch[p2__,"right"[f2_]]]:>ch\[Psi][ch[p1,f1],q,"C",ch[p2,f2]]}~Join~
{ch\[Psi]["left"[f1_],1,"right"[f2_]]:>ch\[Psi][f2,1,f1],
ch\[Psi][ch[p1__,"left"[f1_]],1,"right"[f2_]]:>ch\[Psi][f2,1,ch[p1,f1]],
ch\[Psi]["left"[f1_],1,ch[p2__,"right"[f2_]]]:>ch\[Psi][ch[p2,f2],1,f1],
ch\[Psi][ch[p1__,"left"[f1_]],1,ch[p2__,"right"[f2_]]]:>ch\[Psi][ch[p2,f2],1,ch[p1,f1]]}~Join~
{ch\[Psi]["left"[f1_],q_,"right"[f2_]]:>-ch\[Psi][f2,q,f1],
ch\[Psi][ch[p1__,"left"[f1_]],q_,"right"[f2_]]:>-ch\[Psi][f2,q,ch[p1,f1]],
ch\[Psi]["left"[f1_],q_,ch[p2__,"right"[f2_]]]:>-ch\[Psi][ch[p2,f2],q,f1],
ch\[Psi][ch[p1__,"left"[f1_]],q_,ch[p2__,"right"[f2_]]]:>-ch\[Psi][ch[p2,f2],q,ch[p1,f1]]}~Join~
{ch\[Psi]["right"[f1_],q_,"left"[f2_]]:>ch\[Psi][f1,q,f2],
ch\[Psi][ch[p1__,"right"[f1_]],q_,"left"[f2_]]:>ch\[Psi][ch[p1,f1],q,f2],
ch\[Psi]["right"[f1_],q_,ch[p2__,"left"[f2_]]]:>ch\[Psi][f1,q,ch[p2,f2]],
ch\[Psi][ch[p1__,"right"[f1_]],q_,ch[p2__,"left"[f2_]]]:>ch\[Psi][ch[p1,f1],q,ch[p2,f2]]};

listtotime={ch[p__]:>HoldForm[Times[p]],ch\[Psi][p__]:>HoldForm[Times[p]]};
FtoTensor[activate_?BooleanQ]:=Inactivate[{F_["down",a_,"down",b_]:>PrintTensor[<|"tensor"->F,"upind"->"","downind"->a<>b|>],
F_["down",a_,"up",b_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->F,"upind"->"","downind"->a|>],"upind"->b,"downind"->""|>],
F_["up",a_,"down",b_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->F,"upind"->a,"downind"->""|>],"upind"->"","downind"->b|>],
F_["up",a_,"up",b_]:>PrintTensor[<|"tensor"->F,"upind"->a<>b,"downind"->""|>]},If[activate,Null,PrintTensor]];

transform[ope_, OptionsPattern[]] := Module[{result=ope,model, type, fer, fieldlist,Dcon={},fchain={},l2t={}, fieldrename={}},
If[OptionValue[Dcontract],Dcon=Flatten[{Dcontract1, Dcontract2}]];
If[OptionValue[OpenFchain],l2t=listtotime];
If[OptionValue[ReplaceField] === {},Return[result//.Dcon/.FtoTensor[OptionValue[ActivatePrintTensor]]//.l2t]]; (* abstract operators *)
{model, type, fer} = OptionValue[ReplaceField];
fieldlist = CheckType[model,type,Counting->False];
If[fer==4,AppendTo[fieldrename,"set chirality"]; (* rename fermion due to conventional chirality *)
result=result//.{\[Sigma]^(a_) | OverBar[\[Sigma]]^(a_) :> \[Gamma]^a,Subscript[\[Sigma] |  OverBar[\[Sigma]], a_] :> Subscript[\[Gamma], a], Superscript[\[Sigma] | OverBar[\[Sigma]],a_] :> Superscript[\[Gamma], a]}
//. {(a_)[(b_)[\[Gamma], a1_], b1_] :>a[b[\[Sigma], a1], b1]}; (* change \[Sigma] matrices to \[Gamma] matrices *)
fchain=spinorH2C
];
result=result//.Dcon/.FtoTensor[OptionValue[ActivatePrintTensor]]//.l2t;
result=result//.groupindex[model,fieldlist,FieldRename->fieldrename];
result/.fchain
]
Options[transform] = {OpenFchain->True,ActivatePrintTensor->True,Dcontract -> True, ReplaceField -> {}}; 


(* ::Input::Initialization:: *)
(* simplification after contracted with fields *)
RMDelta[in_]:=Module[{rule,delTlist=Select[Keys[tOut], StringMatchQ[ToString[#],"del"~~__]&]},
rule=Rule@@@(Reverse/@Sort/@Cases[List@@in,Alternatives@@(Construct[#,x__]&/@delTlist) :>{x}]);
in/.Thread[delTlist->(1&)]/.rule
]
ContractDelta[in_]:=Switch[Expand[in],_Times,RMDelta[in],_Plus,Plus@@(RMDelta/@List@@Expand[in])]


(* ::Subsubsection::Closed:: *)
(*Output*)


(* ::Input::Initialization:: *)
(*********** show counting result *****************)

StatResult[model_,types_List,OptionsPattern[]]:=Module[{start,file=OptionValue[OutFile],i=1,type,len=Length[types],timelist={},terms={},time,term,nTermList,posR,nTypes,nTermsR,SList,nOpers,nOpersR},
If[file!="null"&&!FileExistsQ[file],Put["Counting Operators ...",file]];
start=SessionTime[];
If[OptionValue[Progress],Print[Dynamic[i],"/",len,"   ",Dynamic[type]]];
Do[i++;
{time,term}=Timing@Type2TermsCount[model,type];
AppendTo[timelist,time];
AppendTo[terms,term];
If[FileExistsQ[file],PutAppend[term,file]];
,{type,types}];
nTermList=Values/@terms;
posR=Complement[Position[realQ/@types,True],Position[nTermList,{}]];
nTypes=Length@Cases[nTermList,Except[{}]];
Print["number of real types: ",2nTypes-Length[posR]];
nTermsR=Total@MapAt[#/2&,2Total/@nTermList,posR];
Print["number of real terms: ",nTermsR];
SList=MapThread[Slist[model,#1,#2]&,{types,terms}];
nOpers=MapThread[Dot,{nTermList,SList}];
nOpersR=Total@MapAt[#/2&,2nOpers,posR]//Simplify;
Print["number of real operators: ",nOpersR];
Print["time: ",SessionTime[]-start];
Return[timelist];
]
Options[StatResult]={OutFile->"null",Progress->False};
StatResult[model_,dim_Integer,OptionsPattern[]]:=Module[{start,types},
Print["-----------------------"];
Print["Enumerating dim ",dim," operators ..."];
start=SessionTime[];
types=Flatten@AllTypesC[model,dim];
Print[" --- find all types (time: ",SessionTime[]-start,")"];
StatResult[model,types,OutFile->OptionValue[OutFile],Progress->OptionValue[Progress]]
]


(* ::Input::Initialization:: *)
(*********** present all operators *****************)

(* present in notebook *)
Options[Present]={MODEL->0};
Present[resultc_,OptionsPattern[]]:=KeyValueMap[Block[{i=1,model=OptionValue[MODEL]}, (* for each class *)
Print["\n---------------------\n",#1,": ",Length[#2]," type(s)"];
KeyValueMap[Block[{j=1,slist}, (* for each type *)
If[AssociationQ[model],slist=Slist[model,#1,#2]];
Print["  ---------\n  ",i++,". [",#1,"] ",Total[Length/@#2]," term(s)\n"];
KeyValueMap[Block[{}, (* for each flavor sym *)
If[AssociationQ[model],
Print["    Flavor Sym: ",MapAt[DrawYoungDiagram[#,ScaleFactor->6]&,#,2]&/@#1,";\n"];
Print["    Operator number per term: ",slist[[j++]],"\n"];
];
Scan[Print["         ",#]&,#2];
]&,#2];
]&,#2];
]&,resultc]

(* present result in TeXForm *)FormEnviTeX[s_]:=StringReplace[StringDelete[StringReplace[StringReplace[s//TeXForm//ToString,{Shortest["\\text{"~~aa__~~"}"]:>aa}],{"\\dagger"->"^{\\dagger}",f:("F"|"B"|"W"|"G")~~d:("L"|"R"):>f~~"_{"~~d~~"}","uc"->"u^{\\mathcal{C}}","dc"->"d^{\\mathcal{C}}","ec"->"e^{\\mathcal{C}}","nf"->"n_f"}],"$"],{"\\psi L"->"\\psi_{\\mathcal{L}}","\\psi R"->"\\psi_{\\mathcal{R}}",Shortest[")_"~~aa__~~"\\right."]:>"\\right)_"~~aa,b:("B_{L}"|"B_{R}")~~ud:("^{"|"_{"):>"("~~b~~")"~~ud,w:("W_{"~~_~~"}^{"~~_~~"}"):>"("~~w~~")",g:("G_{"~~_~~"}^{"~~_~~"}"):>"("~~g~~")"}];
Options[TeXPresent]={MODEL->0};TeXPresent[resultc_,OptionsPattern[],dim_:0]:=Module[{result=DeleteCases[resultc,<||>]},If[OptionValue[MODEL]===0,Print["\\section{","List Dim-",dim," Operators of one flavor}"],Print["\\section{","List Dim-",dim," Operators}"]];KeyValueMap[Block[{ii=1,model=OptionValue[MODEL]},(* for each class *)
Print["\\subsection{$",FormEnviTeX[#1],"$: ",Length[#2]," type(s)}"];Print["\\begin{itemize}"];
KeyValueMap[Block[{jj=1,slist}, (* for each type *)
If[AssociationQ[model],slist=Slist[model,#1,#2](*;Print[slist]*)];
Print["\\item $\\mathbf{type}$ ",ii++,". $",FormEnviTeX[#1],"$: ",Total[Length/@#2]," term(s)\n"];
KeyValueMap[Block[{}, (* for each flavor sym *)
If[AssociationQ[model],Print["    Flavor Sym: $",StringDelete[StringReplace[ToString[#1],{Shortest["-> {"~~a__~~"}"]:>"\\rightarrow\\tiny{\\yng("~~a~~")}","\[Dagger]":>"^{\\dagger}",f:("B"|"W"|"G")~~d:("L"|"R"):>f~~"_{"~~d~~"}"}]," "],"$;\n"];
Print["    Operator number per term: $",FormEnviTeX[slist[[jj++]]],"$\n"];
];
Scan[Print["\\begin{align}\n         ",FormEnviTeX[#],"\n\\end{align}\n"]&,#2];
]&,#2];
]&,#2];Print["\\end{itemize}"];
]&,result]]


(* ::Subsection::Closed:: *)
(*W2 Operator*)


(* ::Input::Initialization:: *)
BridgeQ[I_,i_,j_]:=MemberQ[I,i]\[Xor]MemberQ[I,j]
BridgeQ[I_]:=BridgeQ[I,##]&
BridgeSign[I_,i_,j_]:=If[BridgeQ[I,i,j],1,-1]
MM[I_,i_,j_,k_,l_]:=-BridgeSign[I,i,k](ab[i,l]ab[j,k]+ab[i,k]ab[j,l])/4;
MbMb[I_,i_,j_,k_,l_]:=-BridgeSign[I,i,k](sb[i,l]sb[j,k]+sb[i,k]sb[j,l])/4;
MMb[I_,i_,j_,k_,l_]:=BridgeSign[I,i,k]Sum[(ab[m,i]ab[j,n]+ab[m,j]ab[i,n])(sb[m,k]sb[l,n]+sb[m,l]sb[k,n]),{m,I},{n,I}]/4//Simplify;
Mandelstam[I_]:=(1/2)Sum[s[i,j],{i,I},{j,I}]

W2[Ind_List]:=W2[#,Ind]&
W2[Amp_Plus,Ind_List]:=W2[Ind]/@Amp
W2[Amp:Except[Plus],Ind_List]:=Module[
{list=Prod2List[Amp],ablist={},sblist={},prefactor=1,sf,sg,sfg},
(* find bridges *)
Map[Switch[Head[#],
ab,If[BridgeQ[Ind]@@#,AppendTo[ablist,#],prefactor*=#],
sb,If[BridgeQ[Ind]@@#,AppendTo[sblist,#],prefactor*=#],
_,prefactor*=# (* other factors *)
]&,list];
(* calculations *)
sf=-(3/4)Length[ablist]Times@@ablist+2Sum[MM[Ind,ablist[[i,1]],ablist[[i,2]],ablist[[j,1]],ablist[[j,2]]]Times@@Delete[ablist,{{i},{j}}],{j,Length[ablist]},{i,j-1}];
sg=-(3/4)Length[sblist]Times@@sblist+2Sum[MbMb[Ind,sblist[[i,1]],sblist[[i,2]],sblist[[j,1]],sblist[[j,2]]]Times@@Delete[sblist,{{i},{j}}],{j,Length[sblist]},{i,j-1}];
sfg=Sum[MMb[Ind,ablist[[i,1]],ablist[[i,2]],sblist[[j,1]],sblist[[j,2]]]Times@@Delete[ablist,i]Times@@Delete[sblist,j],{i,Length[ablist]},{j,Length[sblist]}];

Return[prefactor(Mandelstam[Ind] (sf*(Times@@sblist)+(Times@@ablist)*sg)+ sfg)//Simplify]
]


(* ::Input::Initialization:: *)
Options[W2Diagonalize]={OutputFormat->"print"};
W2Diagonalize[state_,k_,Ind_,OptionsPattern[]]:=
Module[{Num=Length[state],iniBasis=SSYT[state,k,OutMode->"amplitude"],stBasis=SSYT[state,k+2,OutMode->"amplitude"],
W2Basis,W2result,eigensys,result},
W2Basis=FindCor[stBasis]/@(reduce[Num]/@(Mandelstam[Ind]iniBasis));W2result=FindCor[stBasis]/@(reduce[Num]/@(W2[Ind]/@iniBasis));
eigensys=Transpose[LinearSolve[Transpose[W2Basis],#]&/@W2result]//Eigensystem;
result=<|"j"->Function[x,(Sqrt[1-4x]-1)/2]/@eigensys[[1]],"transfer"->eigensys[[2]],"j-basis"->eigensys[[2]].iniBasis|>;

Switch[OptionValue[OutputFormat],
"working",result,
"print",result=MapAt[Ampform,result,{Key["j-basis"],All}];
result=MapAt[MatrixForm,result,Key["transfer"]]
]
]


(* ::Subsection:: *)
(*Model Analysis*)


(* ::Item:: *)
(*GroupMath -- HookContentFormula, DrawYoungDiagram*)


(* ::Item:: *)
(*Permutation Group -- GetCGCM*)


(* ::Item:: *)
(*Model Input -- BreakString, state2class*)


(* ::Item:: *)
(*Lorentz Basis -- LorentzBasisForType, LorentzList*)


(* ::Item:: *)
(*Gauge Group Factor -- GenerateSU3, GenerateSU2, RefineReplace, ContractDelta*)


(* ::Subsubsection::Closed:: *)
(*Functions*)


(* ::Input::Initialization:: *)
(* combine factors of an amplitude by inner product decomposition *)
InnerDecomposeKey[model_,FactorSyms_]:=Module[{Grassmann,decompose},
(* arguments:
FactorSyms = {factorSym1, factorSym2, factorSym3, ...}
factorSym = {field1 \[Rule] yng, field2 \[Rule] yng, ...} *)

(* include the total anti-symmetry of fermi-stat, specifically for operators *)
Grassmann=FactorSyms[[1]]/.{Rule->(Rule[#1,Switch[model[#1]["stat"],"boson",{Total[#2]},"fermion",ConstantArray[1,Total[#2]]]]&)};
decompose=Thread/@Normal@Merge[Prepend[FactorSyms,Grassmann],GetCGCM]/.{(field_->yng_->CG_):>((field->yng)->CG[[All,All,1]])}; 
(* decompose Sn syms for each repeated fields *)
Thread[#,Rule]&/@Distribute[Flatten[Thread/@#]&/@decompose,List]
 (* flatten multiplicity of Sn decomposition, and list all combinations of syms for repeated fields *)
]

GetRowsForFirstBasis[transfer_List]:=Module[{rows,len=ArrayDepth[transfer[[1]]]-2},
rows=Prepend[Accumulate/@(Prepend[#,0]&/@Map[Length[Flatten[#,len-1]]&,transfer,{2}]),{1}];
Do[rows[[i+1]]+=rows[[i,-1]],{i,Length[transfer]}];
Most/@Rest[rows]
]

Options[DeSymmetrize]={ColList->True};
DeSymmetrize[M_,rows_,OptionsPattern[]]:=Module[{len=Length[M],colList,N\[Lambda],iter,col\[Lambda]={},cols={}},
If[Det[M]==0,Print["[DeSymmetrize] incomplete basis"];Abort[]];
If[len==1,Return[{{1}}]];
If[TrueQ[OptionValue[ColList]],colList=Range[len],colList=OptionValue[ColList]];

Do[N\[Lambda]=Length[row\[Lambda]];
If[N\[Lambda]==len,AppendTo[cols,Range[len]];Break[]];
AppendTo[cols,Complement[Range[len],colList[[len+1-basisReduce[Reverse[M[[Complement[Range[len],row\[Lambda]]]]\[Transpose][[colList]]]]["pos"]]]]],
{row\[Lambda],rows}];
Return[cols];
]

(* criterion: not ruled out by flavor sym *)
SQ[model_]:=Not@TrueQ[model[#1]["nfl"]<Length[#2]]&


(* ::Input::Initialization:: *)
Options[Type2TermsPro]={OutputFormat->"operator",Basis->"p-basis",FerCom->2,deSym->True,flavorTensor->True,fullform->False,AddFlavor->True};
Type2TermsPro[model_,type_,OptionsPattern[]]:=Module[{flist=CheckType[model,type],NAgroups=Select[model["Gauge"],nonAbelian],
len,nFac,lorentzB,groupB,basisTotal,
SymComb,pCoord,indexCG,indexFac,cols},
len=Count[flist,{_String,_?(#>1&)}];(*num of repeated fields*)
nFac=Length[NAgroups]+1;(*number of factors to do Inner Product Decomposition for Sn groups*)

(********* compute m-basis *********)
lorentzB=LorentzBasisForType[model,type,OutputFormat->OptionValue[OutputFormat],FerCom->OptionValue[FerCom],Coord->True,OpenFchain->False,ActivatePrintTensor->False];
groupB=GetGroupFactor[model,#,type,OutputMode->"indexed"]&/@NAgroups;
basisTotal=Flatten[lorentzB["basis"]\[TensorProduct]Through[(TensorProduct@@groupB)["basis"]]];
If[OptionValue[OutputFormat]=="operator",basisTotal=ContractDelta/@basisTotal];
basisTotal=RefineReplace/@Map[Activate,basisTotal,\[Infinity]]/.listtotime;
If[OptionValue[Basis]=="m-basis",Return[basisTotal]];
If[len==0,Return[<|{}->basisTotal|>]];

(********* compute p-basis *********)
SymComb=Distribute[Normal/@Prepend[Through[groupB["coord"]],lorentzB["coord"]],List];(*list all syms combinations from factors*)
pCoord=Distribute[InnerDecomposeKey[model,#]&@Keys[#]->Distribute[Values[#],List],List]&/@SymComb//Flatten;(*perform IPD and expand multiplicities of basis and IPD*)
pCoord=Merge[pCoord/.{((sym_->CG_)->fac_):>sym->{CG,fac}},Identity];(*merge into association group by Sym*)
indexCG=Drop[Partition[Range[len (1+nFac)],1+nFac]//Transpose,1]//Flatten;
indexFac=len (1+nFac)+Drop[Range[nFac (len+1)],{len+1,-1,len+1}];
pCoord=Map[Map[Flatten,TensorContract[TensorProduct@@Join@@#,Transpose[{indexCG,indexFac}]],{len}]&,pCoord,{2}];

(********* desymmetrize *********)
If[OptionValue[deSym], 
cols=DeSymmetrize[Flatten[Values[pCoord],1+len],GetRowsForFirstBasis[Values[pCoord]]];
pCoord=AssociationThread[Keys[pCoord]->Map[UnitVector[Length[basisTotal],#]&,cols,{2}]],

pCoord=Extract[{All}~Join~ConstantArray[1,len]~Join~{All}]/@pCoord (* Select first basis from Sn irrep *)
];

(* impose spin-stat: remove flavor syms not allowed by nflavor *)
pCoord=KeySelect[pCoord,And@@#/.Rule->SQ[model]&];
(* transform the key format *)
If[OptionValue[flavorTensor],pCoord=KeyMap[Select[Join[#,#->{1}&/@Cases[flist,{x_,1}:> x]],model[#[[1]]]["nfl"]!=1&]&,pCoord]];

If[OptionValue[fullform],Return[<|"m-basis"->basisTotal,"coordinate"->pCoord|>],
Return[#.basisTotal&/@pCoord]]
]

SnDecompose[replist_]:=Join@@MapThread[ConstantArray,{IntegerPartitions[Total@First@replist],DecomposeSnProduct[replist]}]
Type2TermsCount[model_,type_]:=Module[{len,lorentzB,groupB,nFac,SymComb,terms,pairContraction},
lorentzB=LorentzCountForType[model,type];
len=Length[Keys[lorentzB][[1]]]; (* num of repeated fields *)
groupB=CountGroupFactor[model,#,type]&/@Select[model["Gauge"],nonAbelian];
nFac=Length[groupB]+1; (* number of factors to do Inner Product Decomposition for Sn groups *)
SymComb=Distribute[Normal/@Prepend[groupB,lorentzB],List];
terms=Join@@(ConstantArray[Merge[Keys[#],SnDecompose],Times@@Values[#]]&/@SymComb);
terms=Association[Rule@@@Tally[Join@@(Distribute[Thread/@Normal[#],List]&/@terms)]];
terms=KeyMap[Switch[model[#[[1]]]["stat"],"boson",#,"fermion",MapAt[TransposeYng,#,2]]&/@#&,terms]; (* impose spin-statistics to get flavor sym *)
KeySelect[terms,And@@#/.Rule->SQ[model]&] (* remove flavor syms not allowed by nflavor *)
]


(* ::Input::Initialization:: *)
Options[GenerateOperatorList]={ShowClass->True,T2TOptions->{}};
GenerateOperatorList[model_,dim_Integer,OptionsPattern[]]:=Module[{start=SessionTime[],states,types,len,class,iter=0,assoc=<||>,temp},
Print["Generating types of operators ..."];
states=LorentzList[dim];
types=AllTypesC[model,dim];
len=Length[types];
If[OptionValue[ShowClass],
Print["Evaluating class: ",Dynamic[class]," (",Dynamic[iter],"/",Length[states],")"];
Do[class=state2class@@states[[i]];
temp=AssociationMap[Type2TermsPro[model,#,Sequence@@OptionValue[T2TOptions]]&,types[[i]]];
AssociateTo[assoc,class->DeleteCases[temp,<||>]];
iter++,{i,len}],

assoc=DeleteCases[<||>]@AssociationMap[Type2TermsPro[model,#,Sequence@@OptionValue[T2TOptions]]&,Flatten[types]];
];
Print["Time spent: ",SessionTime[]-start];
Return[assoc];
]
GenerateOperatorList[model_,types_List,OptionsPattern[]]:=DeleteCases[<||>]@AssociationMap[Type2TermsPro[model,#,Sequence@@OptionValue[T2TOptions]]&,types]


(* ::Input::Initialization:: *)
(* # operators per term *)
Slist[model_,type_,terms_]:=Module[{flist=CheckType[model,type],n1,n2},
n1=Times@@(model[#]["nfl"]&/@Cases[flist,{_String,1}][[All,1]]); (* single fields with S=nflavor *)
n2=Times@@@(KeyValueMap[HookContentFormula[#2,model[#1]["nfl"]]&,Association@@#]&/@Keys[terms]); (* repfields with non-trivial symmetry *)
n1*n2
]


(* ::Subsection:: *)
(*End of Package*)


(* ::Input::Initialization:: *)
If[Global`$DEBUG,Begin["`Private`"]]
End[];
EndPackage[]
