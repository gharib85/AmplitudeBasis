(* ::Package:: *)

If[$DEBUG=!=True,$DEBUG=False];
$AmplitudeBasisDir = FileNameDrop[$InputFileName,-1];
$CodeFiles=FileNames[__~~".m",FileNameJoin[{$AmplitudeBasisDir,"Code"}]];


(* ::Input::Initialization:: *)
BeginPackage["AmplitudeBasis`"]


(* ::Subsubsection:: *)
(*Declaration*)


(* ::Input::Initialization:: *)
(* Amplitude *)
{ab,sb,s,Mandelstam,SSYT,reduce};

(* Model Input *)
{ModelIni,AddGroup,AddField,AllTypesR,AllTypesC,GetTypes,CheckType,CheckGroup,AssocIni,TotCharge,deltaBL};

(* Lorentz Factor *)
{LorentzList,LorentzBasis,LorentzCount,OperPoly};

(* Gauge Group Factor *)
{GaugeCount,GaugeBasis};

(* Formating *)
{Ampform,transform,Present};

(* j-basis *)
{W2,W2Diagonalize,W2Check};

(* Analysis *)
{Type2TermsPro,Type2TermsCount,StatResult,PrintStat,GenerateOperatorList};

(* Useful Lie groups in GroupMath *)
{U1,SU2,SU3,SU4,SU5,SU6};

(* Group Profile *)
{tAssumptions,tRep,tOut,tVal,tYDcol,tSimp,dummyIndexCount,GellMann,ConvertToFundamental,PrintTensor};


(* ::Subsubsection:: *)
(*Help Text*)


ab::usage="ab[i,j] stands for angle bracket of spinor helicity variables <ij> == \!\(\*SubscriptBox[\(\[Epsilon]\), \(\[Alpha]\[Beta]\)]\)\!\(\*SuperscriptBox[SubscriptBox[\(\[Lambda]\), \(i\)], \(\[Alpha]\)]\)\!\(\*SuperscriptBox[SubscriptBox[\(\[Lambda]\), \(j\)], \(\[Beta]\)]\). Antisymmetry is enforced. 
It can be turned into bracket form by the function Ampform[].";
sb::usage="sb[i,j] stands for angle bracket of spinor helicity variables [ij] == \!\(\*SubscriptBox[\(\[Epsilon]\), \(\*OverscriptBox[\(\[Alpha]\), \(.\)] \*OverscriptBox[\(\[Beta]\), \(.\)]\)]\)\!\(\*SuperscriptBox[SubscriptBox[OverscriptBox[\(\[Lambda]\), \(~\)], \(i\)], OverscriptBox[\(\[Alpha]\), \(.\)]]\)\!\(\*SuperscriptBox[SubscriptBox[OverscriptBox[\(\[Lambda]\), \(~\)], \(j\)], OverscriptBox[\(\[Beta]\), \(.\)]]\). Antisymmetry is enforced. 
It can be turned into bracket form by the function Ampform[].";
s::usage="s[i,j] is shorthand input form of ab[i,j]sb[j,i], which equals the Mandelstam variable \!\(\*SubscriptBox[\(s\), \(ij\)]\).
It can be turned into \!\(\*SubscriptBox[\(s\), \(ij\)]\) by the function Ampform[].";
Mandelstam::usage="Mandelstam[ch] is shorthand input form of \!\(\*SubscriptBox[\(s\), \(ch\)]\) == \!\(\*FractionBox[\(1\), \(2\)]\)\!\(\*SubscriptBox[\(\[Sum]\), \(i, j \[Element] ch\)]\)ab[i,j]sb[j,i].";

SSYT::usage="SSYT[state,k] gives amplitude y-basis in bracket form.
\[Bullet] state: collection of helicities of all external particles;
\[Bullet] k: number of extra momenta (equivalent to number of derivatives in the operator), non-negative integers that are either odd or even are allowed for a given state.
";

reduce::usage="reduce[amp,num] reduces generic N point amplitude to combination of y-basis amplitudes.
\[Bullet] amp: polynomial of ab[] and sb[] as input amplitude;
\[Bullet] num: number of particles, usually necessary due to undetermined number of scalars;
\[Bullet] reduce[num] == reduce[#,num]& is a function to reduce num-point amplitudes.
";

AddGroup::usage="AddGroup[model,groupname,field,reps,ind] add a symmetry group to the model.
\[Bullet] model: the model to be modified;
\[Bullet] groupname: name of the group added to the model, has to be in the form of 'group'<>'identifier' where 'group' is the standard name of the group in Math whose Cartan Matrix is stored in the variable <group>, while the 'identifier' should be a single letter;
\[Bullet] field: name of the gauge boson if it is a gauge group, while the corresponding particles with helicities \[MinusPlus]1 are named field<>'L'/'R';
\[Bullet] reps: possible reps of the gauge bosons under global symmetries;
\[Bullet] ind: indices used for various representations of the group, stored in Association.
";

AddField::usage="AddField[model,field,hel,Greps,reps] add a field/particle specie to the model.
\[Bullet] model: the model to be modified;
\[Bullet] field: name of the field/particle to be added -- if it is complex, its conjugate is named field<>'\[Dagger]';
\[Bullet] hel: helicity of the particle;
\[Bullet] Greps: representations of the particle under all the gauge groups;
\[Bullet] reps: representations of the particle under other groups.
";

AllTypesR::usage="AllTypesR[model,dim] gives the list of types in the model at certain dimension, with conjugating types counted separately.";
AllTypesC::usage="AllTypesC[model,dim] gives the classified types in the model at certain dimension, modulo charge conjugation.";
GetTypes::usage="GetTypes[model,dmin,dmax,file] compute types of the model in a range of dimensions and store in the file.";

CheckType::usage="CheckType[model,type] turns a type in the form of product of field names into list of them, meanwhile checking if they have been added to the model.";
CheckGroup::usage="CheckGroup[model,groupname] returns the group variable by removing the identifier in the groupname, meanwhile checking if the group file is correctly loaded.";

LorentzBasis::usage="LorentzBasis[model,type] enumerates basis amplitude or Lorentz structures for certain type in the model.
Returns the m-basis Lorentz structure and the p-basis as coordinates in m-basis.";
LorentzCount::usage="LorentzCount[model,type] effectively counts the number of amplitudes/Lorentz structures for certain type in the model, classified by permutation symmetries of the identical particles/repeated fields.";

OperPoly::usage="OperPoly[amp,num] turns amplitudes in terms of ab[] and sb[] into corresponding operators.";
transform::usage="transform[oper] turns operators into various forms.";

GaugeBasis::usage="GaugeBasis[model,groupname,type] enumerates gauge group structures in terms of invariant tensors, organized by permutation symmetries of the identical particles/repeated fields.";
GaugeCount::usage="GaugeCount[model,groupname,type] effectively counts the number of group structures for each permutation symmetries of the identical particles/repeated fields.";

Ampform::usage="Ampform[amp] prints amplitudes in terms of ab[] and sb[] as more conventional form <> and [] for reading.";

W2::usage="W2[amp,ch] gives the Casimir \!\(\*SuperscriptBox[\(W\), \(2\)]\) operator for certain channel acting on the amplitude.";
W2Diagonalize::usage="W2Diagonal[state,k,ch] uses Casimir \!\(\*SuperscriptBox[\(W\), \(2\)]\) to obtain j-basis, the amplitudes of Lorentz class [state,k] with definite angular momentum j.";

Type2TermsPro::usage="Type2TermsPro[model,type] enumerates the full p-basis of a type in the model, organized by the flavor symmetries of the identical particle/repeated fields.";
Type2TermsCount::usage="Type2TermsCount[model,type] effectively counts the number of p-basis for each flavor symmetry of a type in the model.";

PrintStat::usage="PrintStat[model,dim] effectively counts the number of types, p-basis and operators at given dimension in a model.";
GenerateOperatorList::usage="GenerateOperatorList[model,dim] enumerates all the p-basis at certain dimension in the model.";


(* ::Subsection:: *)
(*Configure*)


(* ::Input::Initialization:: *)
permutationBasis="left"; (* or "right" *)
groupList={};

maxTry=30;
h2f=<|-2->CL,-1->FL,-1/2->\[Psi],0->\[Phi],1/2->OverBar[\[Psi]],1->FR,2->CR|>;
LorentzIndex=Join[Join[{"\[Mu]","\[Nu]","\[Lambda]","\[Rho]","\[Eta]","\[Xi]"},Alphabet["Greek"][[19;;-1]]],Append[StringJoin[#,"1"]&/@Alphabet["Greek"],StringJoin[#,"2"]&/@Alphabet["Greek"]]];
FLAVOR={"p","r","s","t","u","v","x","y","z"};



(* ::Input::Initialization:: *)
If[!Global`$DEBUG,Begin["`Private`"]]
Do[Get[file],{file,Global`$CodeFiles}];



(* ::Subsection:: *)
(*Model Input*)


(* ::Input::Initialization:: *)
(* whether a field has the given helicity *)
helicityQ[model_,h_]:=model[#]["helicity"]==h&  
(* judge if reps of group in replist could form a singlet *)
SingletQ[group_,{rep__List}]:=MemberQ[MyRepProduct[group,{rep}][[All,1]],ConstantArray[0,Length[group]]] (* for non-Abelian groups *)
SingletQ[{},{rep__?NumericQ}]:=Plus@@rep==0 (* for Abelian groups *)
SingletQ[{},0]:=True
(* get conjugate rep of a given rep *)
RepConj[{1}]:={-1}   (* for su(2) fund *)
RepConj[{-1}]:={1}   (* for su(2) anti-fund *)
RepConj[rep_List]:=Reverse[rep] (* for other non-Abelian reps *)
RepConj[charge_?NumericQ]:=-charge (* for Abelian charges *)
Conj[realOp_String]:=realOp (* operator names associate to conjugate operators -- themselves by default *)
realQ[type_]:=Module[{flist=Prod2List[type]},TrueQ[flist==Sort[Conj/@flist]]]
nonAbelian[groupname_]:=Length[CheckGroup[groupname]]>0 (* judge if a group is non-Abelian *)
Singlet[group_]:=Replace[group,_List->0,{Depth[group]-2}]
Fund[group_]:=ReplacePart[Singlet[group],1->1]
AFund[group_]:=ReplacePart[Singlet[group],-1->1]

CheckType[model_,type_,OptionsPattern[]]:=Module[{flist=DeleteCases[Prod2List[type],"D"|_?NumericQ],inModel},
inModel=KeyExistsQ[model,#]&/@flist;
If[Nand@@inModel,Message[CheckType::unknown,type];Abort[]];
If[OptionValue[Sorted],flist=SortBy[flist,model[#]["helicity"]&]];
If[OptionValue[Counting],flist=Tally[flist]];
Return[flist];
]
Options[CheckType]={Sorted->True, Counting->True};
CheckType::unknown="unrecognized fields in type `1`";

CheckGroup[model_Association,groupname_String]:=Module[{group=ToExpression@StringDrop[groupname,-1]},If[MemberQ[groupList,StringDrop[groupname,-1]]&&MemberQ[model["Groups"],groupname],group,Message[CheckGroup::ndef,groupname]]]
CheckGroup[groupname_String]:=Module[{group=ToExpression@StringDrop[groupname,-1]},If[MemberQ[groupList,StringDrop[groupname,-1]],group,Message[CheckGroup::ndef,groupname]]]
CheckGroup::ndef="Group `1` not defined.";

(* Names for Abstract Fields *)
state2class=D^#2 Times@@Power@@@MapAt[h2f,Tally[#1],{All,1}]&;

Fields[model_]:=DeleteCases[Keys@Select[model,MatchQ[#,_Association]&],"rep2ind"|"rep2indOut"]

Clear[SetSimplificationRule];
SetSimplificationRule[groups__]:=Module[{},
Unprotect[Times,Power];Clear[Times,Power];
Do[Check[ReleaseHold[tSimp[group]],"simplification rule for "<>group<>" not found"],{group,{groups}}];
Protect[Times,Power]
]
SetSimplificationRule[model_Association]:=Module[{group(*,indexset=Catenate@model["rep2indOut"]*)},
Unprotect[Times,Power];
Clear[Times,Power];
Do[group=CheckGroup[groupname];Check[tSimp[group](*/.{INDEXSET->indexset}*)//ReleaseHold,"simplification rule for "<>groupname<>" not found"],{groupname,model["Groups"]}];
Protect[Times,Power]
]
ReSetSimplificationRule[]:=Module[{},
Unprotect[Times,Power];
Clear[Times,Power];
Protect[Times,Power]
]


(* ::Input::Initialization:: *)
SetAttributes[{ModelIni,AddGroup,AddField},HoldFirst];

ModelIni[model_]:=model=<|"Groups"->{},"Gauge"->{},"rep2indOut"-><||>|>
LoadGroup[groupname_String]:=Module[{profile},
If[!MemberQ[groupList,groupname],
profile=FileNameJoin[{Global`$AmplitudeBasisDir,"GroupProfile", groupname<>"_profile.m"}];
If[FileExistsQ[profile],
Get[profile];SetSimplificationRule@@ToExpression/@groupList,
Message[LoadGroup::profile,groupname];Abort[]]]]
LoadGroup::profile="Profile for group `1` not found.";

(* Adding new Gauge Group to a Model *)
Options[AddGroup]={GaugeBoson->None,Index->"default"};
AddGroup[model_,groupname_String,OptionsPattern[]]:=Module[{group=ToExpression@StringDrop[groupname,-1],fieldname=OptionValue[GaugeBoson],ind},
(* read group info from profile *)
LoadGroup[StringDrop[groupname,-1]];

AppendTo[model["Groups"],groupname];(* add gauge group to the model *)
(*model=Merge[{model,<|"Groups"->{groupname}|>},Apply[Join]]; *)
AssociateTo[model[#],groupname->Singlet[group]]&/@Fields[model]; (* pre-existing fields set to singlet by default *)

(* Add Gauge Boson, otherwise a global sym *)
If[fieldname=!=None,
model[groupname]=fieldname;
(*Freps=MapAt[Adjoint,MapAt[Singlet,CheckGroup/@model["Groups"],{;;-2}],-1];*) (* gauge boson representations under all groups *)
AppendTo[model["Gauge"],groupname];
AddField[model,fieldname<>"L",-1,{groupname->Adjoint[group]},Hermitian->True];
AddField[model,fieldname<>"R",1,{groupname->Adjoint[group]},Hermitian->True]; (* add gauge bosons *)
Conj[fieldname<>"L"]=fieldname<>"R";
Conj[fieldname<>"R"]=fieldname<>"L"]; (* define special conjugation relation (not denoted by \[Dagger]) for gauge boson names *)

If[nonAbelian[groupname],If[OptionValue[Index]==="default",ind=Global`INDEX[group],ind=OptionValue[Index]];
AssociateTo[model["rep2indOut"],groupname->ind]; (* define list of specific indices for all reps of the new group *)
AssociateTo[model["rep2indOut"][groupname],Singlet[group]->{}]];
SetSimplificationRule[model] (* define simplification rules for all gauge groups *)
]

(* Adding New Field to a Model *)
AddField::overh="helicity of `1` is neither integer nor half-integer.";

Options[AddField]={Flavor->1,Dim->"default",Hermitian->False,Chirality->{},Spurion->False,Soft->False};

AddField[model_,field_String,hel_,Greps_List,OptionsPattern[]]:=Module[{attribute=<||>,hellist,flavor=OptionValue[Flavor],NAgroups,shape,dim=OptionValue[Dim]},
If[IntegerQ[2hel],AppendTo[attribute,"helicity"->hel],Message[AddField::overh,field]];
If[!MemberQ[hellist=Options[LorentzList,HelicityInclude][[1,2]],Abs[hel]],SetOptions[LorentzList,HelicityInclude->Append[hellist,Abs[hel]]]];
AssociateTo[attribute,AssociationMap[Singlet[CheckGroup[#]]&,model["Groups"]]];
AssociateTo[attribute,Greps];

AssociateTo[attribute,"dim"->If[NumericQ[dim],dim,1+Abs[hel]]];AssociateTo[attribute,"spurion"->OptionValue[Spurion]];AssociateTo[attribute,"soft"->OptionValue[Soft]];

Switch[flavor,
_Integer|_Symbol,AssociateTo[attribute,{"nfl"->flavor,"indfl"->FLAVOR}],
_List,AssociateTo[attribute,{"nfl"->flavor[[1]],"indfl"->flavor[[2]]}]];
AssociateTo[attribute,"stat"->If[IntegerQ[hel],"boson","fermion"]];
If[attribute["stat"]=="fermion" ,AssociateTo[attribute,"chirality"->OptionValue[Chirality]]];
AppendTo[model,field->attribute];

(*NAgroups=Select[model["Groups"],nonAbelian];
shape=MapThread[DimR[#1,#2]&,{CheckGroup/@NAgroups,Abs[attribute/@NAgroups]}];
AppendTo[tAssumptions,ToExpression["t"<>field<>ToString[NAgroups[[#]]]]\[Element]Arrays[{shape[[#]]}]]&/@Range[1,Length[shape]];*)

If[!OptionValue[Hermitian]&&Last@Characters[field]!="\[Dagger]",AddField[model,field<>"\[Dagger]",-hel,MapAt[RepConj,Greps,{All,2}],Flavor->OptionValue[Flavor],Chirality->(OptionValue[Chirality]/.{"left"->"right","right"->"left"})];
Conj[field]=field<>"\[Dagger]";
Conj[field<>"\[Dagger]"]=field;
];
]
AddTypeEOM[filename_]:=Module[{profile},profile=FileNameJoin[{Global`$AmplitudeBasisDir,filename}];
If[FileExistsQ[profile],Get[profile],Message[AddTypeEOM::profile,groupname];Abort[]]]
AddTypeEOM::profile="Profile for TypeEOM `1` not found.";


(* ::Input::Initialization:: *)
CombList[fieldlist_,num_]:=Module[{len=Length[fieldlist],list},
If[len==0,Return[{}]];
list={0}~Join~#~Join~{len+num}&/@Subsets[Range[len+num-1],{len-1}];
list=Differences[#]-1&/@list;
Join@@MapThread[ConstantArray,{fieldlist,#}]&/@list
]
ChargeNormalize[chargelist_]:=If[FirstCase[chargelist,x_/;x!=0]<0,-1,1]*chargelist

Options[GaugeClass]={SymGroup->"default",ClassifyBy->{}};
GaugeClass[model_,type:(_Times|_Power),OptionsPattern[]]:=GaugeClass[model,CheckType[model,type,Counting->False],SymGroup->OptionValue[SymGroup],ClassifyBy->OptionValue[ClassifyBy]]
GaugeClass[model_,fields_List,OptionsPattern[]]:=Module[{greps,greps2,groups},
If[OptionValue[SymGroup]=="default",groups=Select[model["Groups"],KeyExistsQ[model,#]&],groups=OptionValue[SymGroup]];
greps=model[#]/@groups&/@fields\[Transpose];
greps=Replace[Sort/@greps,{x__?NumericQ}:>Plus[x],1];
greps2=((model[#]/@OptionValue[ClassifyBy])&/@fields)\[Transpose];
If[MemberQ[greps,x_?NumericQ/;x!=0],False,{greps,greps2}]
]

Options[state2type]={SymGroup->"default",ClassifyBy->{}};
state2type[model_,state_,k_,OptionsPattern[]]:=Module[{comblist,combindexed,singletcomb,groups},
If[OptionValue[SymGroup]=="default",groups=CheckGroup/@Select[model["Groups"],KeyExistsQ[model,#]&],groups=CheckGroup/@OptionValue[SymGroup]];
(* field combinations in the model with given helicities *)
comblist=Join@@@Distribute[CombList[Select[Keys[model],helicityQ[model,#1]],#2]&@@@Tally[state],List];
combindexed=Delete[GroupBy[comblist,GaugeClass[model,#,SymGroup->OptionValue[SymGroup],ClassifyBy->OptionValue[ClassifyBy]]&],Key[False]];(* find singlet combinations *)
singletcomb=KeySelect[combindexed,And@@MapThread[SingletQ,{groups,Abs[#[[1]]]}]&];
If[singletcomb===<||>,Return[<||>]];
Map[Times@@PadRight[#,Length[state]+k,"D"]&]/@Merge[MapAt[Total/@Last[#]&,Normal[singletcomb],{All,1}],Apply[Join]]
]


(* ::Input::Initialization:: *)
(* # operators per term *)
NOperList[model_,type_,terms_]:=Module[{flist=CheckType[model,type],n1,n2},
n1=Times@@(model[#]["nfl"]&/@Cases[flist,{_String,1}][[All,1]]); (* single fields with S=nflavor *)
n2=Times@@@(KeyValueMap[HookContentFormula[#2,model[#1]["nfl"]]&,Association@@#]&/@Keys[terms]); (* repfields with non-trivial symmetry *)
n1*n2
]


(* ::Input::Initialization:: *)
(* Global Charge Analysis *)
TotCharge[model_,qnum_,type_]:=Module[{particles=CheckType[model,type,Counting->False]},
Total[model[#][qnum]&/@particles]
]
deltaBL[model_,type_]:=Module[{deltaB,deltaL,sign=1},
deltaB=TotCharge[model,"Baryon",type];
deltaL=TotCharge[model,"Lepton",type];
If[deltaB<0,sign=-1];
If[deltaB==0&&deltaL<0,sign=-1];
sign{deltaB,deltaL}
]



(* ::Subsection:: *)
(*Lorentz Basis*)


(* ::Input::Initialization:: *)
(* Symmetrize the list of amplitudes Mlist according to ALL possible Irreps of permutations for RepFields, and show result under basis StBasis *)
Options[LorentzBasisAuxOld]={Coord->False};
LorentzBasisAuxOld[Mlist_,RepPos_,Num_,OptionsPattern[]]:=LorentzBasisAuxOld[Mlist,RepPos,Num]=
Module[{depth=Length[RepPos],Dim=Length[Mlist],SymList,yngList,permAmp,permResult=<||>,SnDimlist={},emptySpaceCor,j,ynglist,allbasis,allbasisCor,poslist},
If[depth==0,Return[<|{}->If[OptionValue[Coord],IdentityMatrix[Length[Mlist]],Mlist]|>]];

yngList=Distribute[Thread[{IntegerPartitions@Length[#],First[#]}]&/@RepPos,List];
Do[SnDimlist=SnIrrepDim/@yngList[[i,All,1]]; (* tensor dimensions of Snrep space *)
If[Dim<Times@@SnDimlist,Continue[]];
For[emptySpaceCor=ConstantArray[0,Length[Mlist]];j=0,j<depth,j++,
emptySpaceCor=ConstantArray[emptySpaceCor,SnDimlist[[depth-j]]]
];  (* Coordinate for projected out irrep spaces *)
ynglist=MapThread[YO@@@(Function[x,Append[#1,x]]/@#2)&,{yngList[[i]],Range/@SnDimlist}]; (* abstract ynglist for each basis vector in Snrep *) 
(*allbasis=Hold@Table@@Evaluate[Join[{YPermute[Mlist,pp[YO@@@ynglist],Num]},Evaluate[{var,SnDimlist}\[Transpose]]]];*) (* permute to get all basis vector *)
allbasisCor=Map[FindCor[Mlist]/@YPermute[Mlist,#,Num]&,Outer[pp@List[##]&,##]&@@ynglist,{depth}];
allbasisCor=Transpose[allbasisCor,Append[Range[2,depth+1],1]]/.emptySpaceCor->Nothing; 
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

Options[LorentzBasis]={OutputFormat->"operator",Coord->False,FerCom->2,OpenFchain->True,ActivatePrintTensor->True,Working->False};
LorentzBasis[model_,type_,OptionsPattern[]]:=Module[{particles,fieldsReplace,k,state,RepFields,Num,Mlist,resultCor,amp2op,OpBasis,flip=False},
k=Exponent[type,"D"];
particles=CheckType[model,type,Counting->False];
RepFields=Select[PositionIndex[particles],Length[#]>1&];
state=model[#]["helicity"]&/@particles;
Num=Length[state];
If[{Num-2,2}.yngShape[state,k]>{Num-2,2}.yngShape[-state,k],flip=True];

Mlist=SSYT[If[flip,-1,1]*state,k,OutMode->"amplitude"];
(* generate initial amplitude basis from SSYT *)
resultCor=KeyMap[Thread@Rule[Keys[RepFields],#]&,LorentzBasisAuxOld[Mlist,Values@RepFields,Num,Coord->True]];
If[flip,Mlist=Mlist/.{ab->sb,sb->ab}];

Switch[OptionValue[OutputFormat],
(* Output amplitude basis *)
"amplitude",If[OptionValue[Coord],
<|"basis"->Ampform/@Mlist,"coord"->resultCor|>,
Map[#.Mlist&,resultCor,{2+Length[RepFields]}]],  
(* Output operator basis *)
"operator",amp2op=MonoLorentzBasis[Mlist,Num,finalform->False];
OpBasis=transform[amp2op["LorBasis"],ReplaceField->{model,type,OptionValue[FerCom]},OpenFchain->OptionValue[OpenFchain],ActivatePrintTensor->OptionValue[ActivatePrintTensor],Working->OptionValue[Working]];
If[OptionValue[Coord],
<|"basis"->OpBasis,"coord"->Map[Inverse[amp2op["Trans"]]\[Transpose].#&,resultCor,{2+Length[RepFields]}]|>, (* output <|basis, coord|> *)
Map[Expand[OpBasis.Inverse[amp2op["Trans"]]\[Transpose].#]&,resultCor,{2+Length[RepFields]}] (* output basis.coord *)
]
]
] 

Clear[LorentzBasisAux];

Options[LorentzBasisAux]={OutMode->"p-basis",OutputFormat->"operator",ReplaceField->{},finalform->True,newmethod->False,AdlerZero->False};
LorentzBasisAux[state_,k_,posRepeat_,OptionsPattern[]]:=Module[{Num=Length[state],flip=False,lorentzGen,ybasis,amp2op,mbasis,shift,yngList,result,grassmann},
If[{Num-2,2}.yngShape[state,k]>{Num-2,2}.yngShape[-state,k],flip=True];
{lorentzGen,ybasis}=Reap@LorentzPermGenerator[If[flip,-1,1]*state,k];
If[flip,ybasis=ybasis/.{ab->sb,sb->ab};lorentzGen=KeyMap[-1#&,lorentzGen]];

Switch[OptionValue[OutputFormat],
"amplitude",mbasis=ybasis[[1,1]];amp2op["Trans"]=IdentityMatrix[Length@mbasis],

"operator",If[OptionValue[newmethod],(*Print[state,k,OptionValue[AdlerZero]];*)amp2op=LorBasis[If[flip,-1,1]state,k,AdlerZero->OptionValue[AdlerZero]]/.If[flip,{h2f[-1/2]->h2f[1/2],h2f[1/2]->h2f[-1/2],h2f[-1]->h2f[1],h2f[1]->h2f[-1],"\[Sigma]"->"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)","\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"->"\[Sigma]"},{}],amp2op=MonoLorentzBasis[ybasis[[1,1]],Length[state],finalform->False]];
mbasis=amp2op["LorBasis"];
(*transform[amp2op["LorBasis"],ReplaceField->OptionValue[ReplaceField],
OpenFchain->OptionValue[finalform],ActivatePrintTensor->OptionValue[finalform]];*)
lorentzGen=Map[Transpose[LinearSolve[Transpose[amp2op["Trans"]],Transpose[(amp2op["Trans"].#)]]]&,lorentzGen,{2}]

];
result=<|"basis"->mbasis,"Trans"->amp2op["Trans"]|>;
shift=FirstPosition[PositionIndex[state],First[#]]&/@posRepeat;
grassmann=If[IntegerQ[state[[First[#]]]],{1,1},{-1,(-1)^(1+Length[#])}]&/@posRepeat;

Switch[Head[posRepeat],
Association,
yngList=IntegerPartitions@Length[#]&/@posRepeat;
yngList=AssociationThread/@Distribute[{Keys[yngList]}->Distribute[Values[yngList],List],List];
Append[result,"p-basis"->
DeleteCases[Association@Map[Normal[#]->
basisReduce[Dot@@KeyValueMap[PermRepFromGenerator[lorentzGen[[shift[#1][[1]]]],YO[#2,shift[#1][[2]]]]&,#]]["basis"]&,yngList],{}]],

List,
(*Append[result,"generators"->
Association@MapThread[
#2->#3 Function[gen,PermRepFromGenerator[lorentzGen[[#1[[1]]]],gen]]/@{Cycles[{{#1[[2]],#1[[2]]+1}}],Cycles[{Range[#1[[2]],#1[[2]]+Length[#2]-1]}]}&,
{shift,posRepeat,grassmann}]]*)
(*for amplitude output format*)
Switch[OptionValue[OutputFormat],
"operator",Append[result,"generators"->Association[MapThread[#2->#3 Function[gen,PermRepFromGenerator[lorentzGen[[#1[[1]]]],gen]]/@{Cycles[{{#1[[2]],#1[[2]]+1}}],Cycles[{Range[#1[[2]],#1[[2]]+Length[#2]-1]}]}&,{shift,posRepeat,grassmann}]]],
"amplitude",Append[result,"generators"->Association[MapThread[#2->Function[gen,PermRepFromGenerator[lorentzGen[[#1[[1]]]],gen]]/@{Cycles[{{#1[[2]],#1[[2]]+1}}],Cycles[{Range[#1[[2]],#1[[2]]+Length[#2]-1]}]}&,{shift,posRepeat}]]]]
]
]

LorentzCount[model_,type_]:=Module[{particles,k,state,RepFields,Num,grank,group,X,p,rep,irrepComb,AllSym},
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


(* ::Subsection:: *)
(*Gauge Group Factor*)


(* ::Input::Initialization:: *)
GaugeCount[model_,groupname_,type_]:=Module[{flist=CheckType[model,type],group=CheckGroup[groupname],repfs,relist,sym},
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

GaugeBasis[model_,groupname_,type_,OptionsPattern[]]:=Module[{flist=CheckType[model,type],group=CheckGroup[model,groupname],indmap=model["rep2ind"][groupname],
SUNreplist,repeatlist,nonsinglets,repeatnonsinglets,repeatsinglets,
displacements,indexlist,Irreplist,SNCollections,nonSingletSN,
convertfactor,fundIndex,YDbasis,Mbasis,MbasisAll,tMbasis,tMbasisAll,vMbasis,vMbasisAll,
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
YDbasis=Expand[Flatten[((Times@@(tYDcol[group]@@@Transpose[#]))&/@GenerateLRT[group,indmap,nonsinglets])]*convertfactor];
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
Options[GaugeBasis]={OutputMode->"indexed"};


(* ::Input::Initialization:: *)
GetComb[group_,list_]:=Module[{temp1,temp2},
temp1=ReduceRepProduct[group,#]&/@list;
temp1=Distribute[#&/@temp1,List];
temp1={#,ReduceRepProduct[group,#[[1;;,1]]]}&/@temp1;
Cases[temp1,{m__,{___,{ConstantArray[0,Length[group]],y_},___}}:>{m,y}]
(*Select[Distribute[#[[1;;,1]]&/@temp1,List],Position[ReduceRepProduct[group,#][[1;;,1]],ConstantArray[0,Length[group]]]\[NotEqual]{}&]*)
];
(*GaugeJBasis[model_,groupname_,type_,parts_,OptionsPattern[]]:=Module[{flist=CheckType[model,type],indexlist,group=CheckGroup[model,groupname],indmap=model["rep2ind"][groupname],SUNreplist,nonsinglets,convertfactor,YDbasisnoConvert,YDbasis,fSUNreplist,nonsingletparts,YTlist,RepParts,YTParts,SUNrepPartlist,SubYTs,MbasisAll,tMbasisAll,vMbasisAll,Mbasis,tMbasis,vMbasis,assoSubYTs,qr,vtemp,stemp,coordtemp,tempresult,ranktemp,coordresult={},finalresult={}},
indexlist=GenerateFieldIndex[model,groupname,flist];
finalresult={"order"->Flatten@(ConstantArray@@@flist)};
SUNreplist={#[[2]],model[#[[1]]][groupname],#[[1]]}&/@flist; (* {repeat_num, SUNrep, fieldname} *)
nonsinglets=DeleteCases[SUNreplist,{_,Singlet[group],_}];
If[nonsinglets=={},AppendTo[finalresult,"basis"->{1}];AppendTo[finalresult,"jcoord"->{{1}}];Return[Association@finalresult]];
convertfactor=Times@@(ConvertFactor[model,groupname,#]&/@flist);
(*prepare y- and m- bases*)
YDbasisnoConvert=Flatten[((Times@@(tYDcol[group]@@@Transpose[#]))&/@GenerateLRT[group,indmap,nonsinglets])];
YDbasis=Expand[YDbasisnoConvert*convertfactor];
MbasisAll=SimpGFV2[Expand/@TRefineTensor[YDbasis,model,groupname,flist]];
tMbasisAll=Product2ContractV2[#,indexlist,Symb2Num->tVal[group]]&/@MbasisAll;
vMbasisAll=Flatten/@tMbasisAll;
qr=QRDecomposition[Transpose[vMbasis]];
MapThread[Set,{{Mbasis,tMbasis,vMbasis},FindIndependentMbasis[MbasisAll,tMbasisAll,vMbasisAll]}];
AppendTo[finalresult,"basis"->Mbasis];
(*Begin Processing J basis related*)
fSUNreplist=Flatten[ConstantArray[#[[2]],#[[1]]]&/@SUNreplist,1];
nonsingletparts=Select[parts,(!MatchQ[fSUNreplist[[#]]&/@#,{Singlet[group]..}])&];
YTlist=Flatten[GenerateTYT@@@(Join[#,{indmap[Fund[group]],group}]&/@SUNreplist),1];
RepParts=MapAt[fSUNreplist[[#]]&,nonsingletparts,{All,All}];
YTParts=MapAt[YTlist[[#]]&,nonsingletparts,{All,All}];
SUNrepPartlist=GetComb[group,RepParts];
SubYTs=Table[Distribute[GenerateLRTYTs@@@MapThread[{group,#1,#2}&,{SUNrepPartlist[[i,1,1;;,1]],YTParts}],List],{i,Length[SUNrepPartlist]}];
assoSubYTs=Association@MapThread[Rule,{{MapThread[Rule,{nonsingletparts,#[[1]]}],#[[2]]}&/@SUNrepPartlist,SubYTs}];
Do[
tempresult={};
ranktemp=0;
Do[
Do[
stemp=Expand[RefineTensor[Expand[Simplify[PermuteYBasis[ybs,YTs]/.Sortarg[tasList[group]]]*convertfactor],model,groupname,flist]];
If[stemp==0,Continue[]];
vtemp=Flatten@Product2ContractV3[stemp,indexlist,tVal[group]];
coordtemp=Simplify[GetCoord[qr,vtemp]];
AppendTo[tempresult,coordtemp];
If[ranktemp+1==MatrixRank[tempresult],ranktemp+=1;Break[];,tempresult=Drop[tempresult,-1];]
,{ybs,YDbasisnoConvert}];
,{YTs,assoSubYTs[key]}];
AppendTo[coordresult,key->tempresult];
,{key,Keys@assoSubYTs}];
AppendTo[finalresult,"jcoord"->coordresult];
Association@finalresult
]*)


(* ::Subsection:: *)
(*Model Analysis*)


(* ::Input::Initialization:: *)
AllTypesR[model_,dim_]:=state2type[model,#1,#2]&@@@LorentzList[dim,Conj->True]//Flatten

Options[AllTypesC]={StatusPrint->False,OutputFile->"",SymGroup->"default",ClassifyBy->{}};
AllTypesC[model_,statelist_,OptionsPattern[]]:=Module[{iter=0,class,file=True,pos,k,types,result=<||>,chargeclasses},
If[OptionValue[StatusPrint],Print["Looking for types in class ",Dynamic[class],",  ",Dynamic[iter],"/",Length[statelist]]];
If[OptionValue[OutputFile]!="",file=NotebookDirectory[]<>OptionValue[OutputFile]];
If[MemberQ[OptionValue[ClassifyBy],"dim"],pos=Position[OptionValue[ClassifyBy],"dim"]];
Do[iter++;class=state2class@@state;k=Exponent[class,D];
types=state2type[model,#1,#2,SymGroup->OptionValue[SymGroup],ClassifyBy->OptionValue[ClassifyBy]]&@@state;
If[state==MapAt[-Reverse[#]&,state,1],
types=DeleteDuplicates[types,(#1/.{x_String/;x!= "D":>Conj[x]})==#2& ]
];
If[Length[pos]!=0,types=KeyMap[MapAt[#+k&,#,pos]&,types]];
AssociateTo[result,class->types],{state,statelist}];

chargeclasses=DeleteDuplicates@Catenate[Keys/@result];
If[chargeclasses=={{}},result=If[Length[#]==0,{},#[{}]]&/@result,
result=AssociationMap[Function[chargeclass,DeleteCases[If[KeyExistsQ[#,chargeclass],#[chargeclass],None]&/@result,None] ],chargeclasses]
];

If[!TrueQ[file],Put[result,file]];
Return[result];
]
AllTypesC[model_,dim_Integer,OptionsPattern[]]:=AllTypesC[model,LorentzList[dim],
StatusPrint->OptionValue[StatusPrint],
OutputFile->OptionValue[OutputFile],
SymGroup->OptionValue[SymGroup],
ClassifyBy->OptionValue[ClassifyBy]]

GetTypes[model_,dmin_,dmax_,file_]:=Module[{dim,types={}},
Do[AppendTo[types,Timing@AllTypesC[model,dim,StatusPrint->True,OutputFile->file<>ToString[dim]<>".m"]];
Print["Dim ",dim,": ",Length[Catenate@#2]," types in all, time used ",#1]&@@Last[types],
{dim,Range[dmin,dmax]}];
(*Put[types[[All,2]],NotebookDirectory[]<>file];*)
Return[types[[All,2]]];
]
GetTypes[model_,dim_,file_]:=GetTypes[model,dim,dim,file]

(*Get Types with EOM relaiton*)
GetRelevantDAux[model_,dimlim_,fields_,nDs_]:=Module[{state,dim,NAgroups=Select[model["Gauge"],nonAbelian],Agroups=Select[model["Gauge"],!nonAbelian[#1]&],dimnow=Total[Abs[model[#]["helicity"]]+1&/@fields]+nDs,funique=DeleteDuplicates[fields],eomlist,result={}},
state=Sort[(model[#1]["helicity"]&)/@fields];
dim=Total[Abs[state]+1]+nDs;
If[Position[LorentzList[dim],{state,nDs}]!={},Sow[Join[fields,ConstantArray["D",nDs]]]];
If[dimnow>dimlim,Return[]];
If[nDs==0,Return[]];
If[nDs==1,
Do[eomlist=EOM[item];
GetRelevantDAux@@@({model,dimlim,Join[DeleteCases[fields,item,1,1],#[[1]]],nDs-1+#[[2]]}&/@eomlist);
,{item,Select[funique,(Abs[model[#]["helicity"]]==1/2||Abs[model[#]["helicity"]]==1)&]}];
Return[result];
];
If[nDs>=2,
Do[If[Length@Select[model[#][gg]&/@fields,Not[#==Singlet[CheckGroup[gg]]]&]>=1,
GetRelevantDAux[model,dimlim,Join[fields,{model[gg]<>"L"}],nDs-2];GetRelevantDAux[model,dimlim,Join[fields,{model[gg]<>"R"}],nDs-2]],{gg,model["Gauge"]}];
Do[eomlist=EOM[item];
GetRelevantDAux@@@({model,dimlim,Join[DeleteCases[fields,item,1,1],#[[1]]],nDs-2+#[[2]]}&/@eomlist);
,{item,Select[funique,(Abs[model[#]["helicity"]]==0)&]}];
Do[eomlist=EOM[item];
GetRelevantDAux@@@({model,dimlim,Join[DeleteCases[fields,item,1,1],#[[1]]],nDs-1+#[[2]]}&/@eomlist);
,{item,Select[funique,(Abs[model[#]["helicity"]]==1/2||Abs[model[#]["helicity"]]==1)&]}];
Return[result]
]
]
GetRelevantD[model_,dimlim_,type_]:=Module[{k=Exponent[type,"D"]},Times@@@Reap[GetRelevantDAux[model,dimlim,CheckType[model,type,Counting->False],k]][[2,1]]]


(* ::Input::Initialization:: *)
GaugeJoin[model_,particles_]:=Module[{groups=CheckGroup/@model["Groups"],reps,result},
reps=(model[#]/@model["Groups"])&/@particles;
result=MapThread[Switch[#1,{},{{Total[#2],1}},{__List},ReduceRepProduct[#1,#2]]&,{groups,reps\[Transpose]}];
{#[[All,1]],Times@@#[[All,2]]}&/@Distribute[result,List]
]
GatherPairGauge[model_]:=Module[{particlePairs,pairGauge,allPairGauge,pairs,result=<||>},
particlePairs=DeleteDuplicates[Tuples[Fields[model],2],Sort[#1]==Sort[Conj/@#2]||Sort[#1]==Sort[#2]&];
pairGauge=AssociationMap[GaugeJoin[model,#]&,particlePairs];
allPairGauge=DeleteDuplicates[Catenate[pairGauge][[All,1]]];
Do[pairs=Position[pairGauge,{rep,_}][[All,1,1]];
If[MemberQ[Keys[result],RepConj/@rep],result[RepConj/@rep]=result[RepConj/@rep]~Join~Map[Conj,pairs,{2}],
AssociateTo[result,rep->pairs]
],{rep,allPairGauge}];
result
]


(* ::Input::Initialization:: *)
(*********** show counting result *****************)

StatResult[model_,types_List]:=Module[{start=SessionTime[],iter=0,terms={}},
Print["Counting operators ",Dynamic[iter],"/",Length[types]];
Do[iter++;AppendTo[terms,Type2TermsCount[model,type]],{type,types}];
Print["Done! time used: ",SessionTime[]-start];
Return[AssociationThread[types->terms]];
]
StatResult[model_,dim_Integer]:=Module[{},Print["Enumerating types ..."];StatResult[model,Catenate@AllTypesC[model,dim]]]

Clear[PresentStat];
PresentStat[stat_Association,nflist_:<||>]:=Module[{terms,nTermList,posR,nTypes,nTermsR,SList,nOpers,nOpersR},
If[Length@nflist!=0,terms=KeySelect[#,And@@#/.Rule->SQ[nflist]&]&/@stat,terms=stat]; (* remove flavor syms not allowed by nflavor *)
nTermList=Values/@terms;
posR=Complement[Position[realQ/@Keys[terms],True],Position[nTermList,{}]];
nTypes=Length@Cases[nTermList,Except[{}]];
(*Print["number of complex types"->nTypes];*)
Print["number of real types"->2nTypes-Length[posR]];
(*Print["number of complex terms"->Plus@@Catenate[nTermList]];*)
nTermsR=Total@MapAt[#/2&,2Total/@nTermList,posR];
Print["number of real terms"->nTermsR];
If[nflist==<||>,Return[]];
SList=KeyValueMap[NOperList[nflist,#1,#2]&,terms];
nOpers=MapThread[Dot,{Values@nTermList,SList}];
(*Print["number of complex operators"->Total@nOpers//Simplify];*)
nOpersR=Total@MapAt[#/2&,2nOpers,posR]//Simplify;
Print["number of real operators"->nOpersR];
]


(* ::Input::Initialization:: *)
(* simplification after contracted with fields *)
(*ContractDelta[in_Times]:=Module[{rule,delTlist=Select[Keys[tOut], StringMatchQ[ToString[#],"del"~~__]&]},
rule=Rule@@@(Reverse/@Sort/@Cases[List@@in,Alternatives@@(Construct[#,x__]&/@delTlist) :>{x}]);
in/.Thread[delTlist->(1&)]/.rule
]*)
Options[ContractDelta]={Working->False};
ContractDelta[in_Times,OptionsPattern[]]:=Module[{delTlist,map,result,pos},
If[Length[tOut]==0,Return[in]];
delTlist=Select[Keys[tOut], StringMatchQ[ToString[#],"del"~~__]&];
map=Association[Rule@@@(Reverse/@Sort/@Cases[List@@in,Alternatives@@(Construct[#,x__]&/@delTlist) :>{x}])];
result=in/.Thread[delTlist->(1&)];
If[OptionValue[Working],Return[result/.map]];
Do[pos=Cases[Position[result,dum],{___,Key["upind"]|Key["downind"],_}];
result=ReplacePart[result,pos->map[dum]],{dum,Keys[map]}];
Return[result]
]
ContractDelta[in_Plus]:=ContractDelta/@in(*Switch[Expand[in],_Times,RMDelta[in],_Plus,Plus@@(RMDelta/@List@@Expand[in])]*)
SetAttributes[ContractDelta,Listable];

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
Options[Type2TermsPro]={OutputFormat->"operator",Basis->"p-basis",FerCom->2,deSym->True,flavorTensor->True,fullform->False,AddFlavor->True,TakeFirstBasis->True,OperAbbreviation->{}};
(* RENAME: ? *)
Type2TermsPro[model_,type_,OptionsPattern[]]:=Module[{flist=CheckType[model,type],NAgroups=Select[model["Groups"],nonAbelian],
len,nFac,lorentzB,groupB,basisTotal,
SymComb,pCoord,indexCG,indexFac,cols},
len=Count[flist,{_String,_?(#>1&)}];(*num of repeated fields*)
nFac=Length[NAgroups]+1;(*number of factors to do Inner Product Decomposition for Sn groups*)

(********* compute m-basis *********)
lorentzB=LorentzBasis[model,type,OutputFormat->OptionValue[OutputFormat],FerCom->OptionValue[FerCom],Coord->True,OpenFchain->False,ActivatePrintTensor->False];
groupB=GaugeBasis[model,#,type,OutputMode->"indexed"]&/@NAgroups;
basisTotal=Expand/@Flatten[TensorProduct@@Through[groupB["basis"]]\[TensorProduct]lorentzB["basis"]];
If[OptionValue[OutputFormat]=="operator",basisTotal=ContractDelta@basisTotal];
basisTotal=PrintOper[RefineReplace@basisTotal,OpAbbr->OptionValue[OperAbbreviation]]/.listtotime;
If[OptionValue[Basis]=="m-basis",Return[basisTotal]];
If[len==0,Return[<|{}->basisTotal|>]];

(********* compute p-basis *********)
SymComb=Distribute[Normal/@Append[Through[groupB["coord"]],lorentzB["coord"]],List];(*list all syms combinations from factors*)
pCoord=Distribute[InnerDecomposeKey[model,#]&@Keys[#]->Distribute[Values[#],List],List]&/@SymComb//Flatten;(*perform IPD and expand multiplicities of basis and IPD*)
pCoord=Merge[pCoord/.{((sym_->CG_)->fac_):>sym->{CG,fac}},Identity];(*merge into association group by Sym*)
indexCG=Drop[Partition[Range[len (1+nFac)],1+nFac]//Transpose,1]//Flatten;
indexFac=len (1+nFac)+Drop[Range[nFac (len+1)],{len+1,-1,len+1}];
pCoord=Map[Map[Flatten,TensorContract[TensorProduct@@Join@@#,Transpose[{indexCG,indexFac}]],{len}]&,pCoord,{2}];

(********* desymmetrize *********)
If[OptionValue[deSym], 
cols=DeSymmetrize[Flatten[Values[pCoord],1+len],GetRowsForFirstBasis[Values[pCoord]]];
pCoord=AssociationThread[Keys[pCoord]->Map[UnitVector[Length[basisTotal],#]&,cols,{2}]],

If[OptionValue[TakeFirstBasis],pCoord=Extract[{All}~Join~ConstantArray[1,len]~Join~{All}]/@pCoord] (* Select first basis from Sn irrep *)
];

(* impose spin-stat: remove flavor syms not allowed by nflavor *)
pCoord=KeySelect[pCoord,And@@#/.Rule->SQ[model]&];
(* transform the key format *)
If[OptionValue[flavorTensor],pCoord=KeyMap[Select[Join[#1,Cases[flist,{x_,1}:>(x->{1})]],!TrueQ[model[#1[[1]]]["nfl"]==1]&]&,pCoord]];

If[OptionValue[fullform],Return[<|"m-basis"->basisTotal,"coordinate"->pCoord|>],
Return[#.basisTotal&/@pCoord]]
]

SnDecompose[replist_]:=Join@@MapThread[ConstantArray,{IntegerPartitions[Total@First@replist],DecomposeSnProduct[replist]}]
Type2TermsCount[model_,type_]:=Module[{len,lorentzB,groupB,nFac,SymComb,terms,pairContraction},
lorentzB=LorentzCount[model,type];
len=Length[Keys[lorentzB][[1]]]; (* num of repeated fields *)
groupB=GaugeCount[model,#,type]&/@Select[model["Groups"],nonAbelian];
nFac=Length[groupB]+1; (* number of factors to do Inner Product Decomposition for Sn groups *)
SymComb=Distribute[Normal/@Prepend[groupB,lorentzB],List];
terms=Join@@(ConstantArray[Merge[Keys[#],SnDecompose],Times@@Values[#]]&/@SymComb);
terms=Association[Rule@@@Tally[Join@@(Distribute[Thread/@Normal[#],List]&/@terms)]];
KeyMap[Switch[model[#[[1]]]["stat"],"boson",#,"fermion",MapAt[TransposeYng,#,2]]&/@#&,terms](* impose spin-statistics to get flavor sym *)
]


(* ::Input::Initialization:: *)
basisReduceByFirst[tensor_,len_]:=Module[{pos},

pos=basisReducePro[Extract[tensor,ConstantArray[1,len]](*,Identity*)]["pos"];
TensorTranspose[Map[Part[#,pos]&,tensor,{len}],Append[Range[2,len+1],1]]
]

(*GetWCs[posRepeat_,replist_]:=Module[{indices,tdims,super},
indices=StringRiffle["\!\(\*SubscriptBox[\(p\), \("<>ToString[#]<>"\)]\)"&/@Flatten[posRepeat],""];
tdims=Range[SnIrrepDim[#]]&/@replist;
super=MapThread[Function[{u},"(["<>StringRiffle[ToString/@#1,","]<>"],"<>ToString[u]<>")"]/@#2&,{replist,tdims}];
super=StringRiffle[#,","]&/@Distribute[super,List];
"\!\(\*SubscriptBox[\((\*SuperscriptBox[\(C\), \("<>#<>"\)])\), \("<>indices<>"\)]\)"&/@super
]*)
(*GetWCs[posRepeat_,posnfl_,replist_]:=Module[{tdims,super,sub},If[Length[posnfl]==0,Return[1]];
(*indices=StringRiffle[StringRiffle["\!\(\*SubscriptBox[\(f\), \("<>ToString[#]<>"\)]\)"&/@#1,""]&/@posnfl,","];*)
sub=StringRiffle[StringRiffle["\*SubscriptBox[\(f\), \("<>ToString[#]<>"\)]"&/@#1,""]&/@posnfl,","];(*StringRiffle[("\!\(\*SubscriptBox[\(p\), \("<>ToString[#1]<>"\)]\)"&)/@Flatten[posRepeat],""];*)tdims=(Range[SnIrrepDim[#1]]&)/@replist;super=MapThread[Function[{u},"\((\(["<>StringRiffle[ToString/@#1,","]<>"]\),"<>ToString[u]<>")\)"]/@#2&,{replist,tdims}];super=(StringRiffle[#1,","]&)/@Distribute[super,List];("\!\(\*SubsuperscriptBox[\(C\), \("<>sub<>"\), \("<>#<>"\)]\)"&)/@super]*)

GetWCs[posRepeat_,posnfl_,replist_]:=Module[{tdims,super,sub,posf1repeat,replistnof1},If[Length[posnfl]==0,Return[1]];
sub=StringRiffle[(StringRiffle[("\*SubscriptBox[\(f\), \("<>ToString[#1]<>"\)]"&)/@#1,""]&)/@posnfl,","];If[posRepeat=={},Return["\!\(\*SubsuperscriptBox[\(C\), \("<>sub<>"\), \( \)]\)"]];
posf1repeat=Flatten[Position[posRepeat,#]&/@Complement[posRepeat,Intersection[posRepeat,posnfl]]];
replistnof1=Drop[replist,posf1repeat];tdims=(Range[SnIrrepDim[#1]]&)/@replistnof1;super=MapThread[Function[{u},"\((\(["<>StringRiffle[ToString/@#1,","]<>"]\),"<>ToString[u]<>")\)"]/@#2&,{replistnof1,tdims}];super=(StringRiffle[#1,","]&)/@Distribute[super,List];("\!\(\*SubsuperscriptBox[\(C\), \("<>sub<>"\), \("<>#1<>"\)]\)"&)/@super]

GetSnGenerators[irrep_]:=Module[{matmaps,n=Total[irrep]},ReadMatrices[matmaps,n,NotebookDirectory[]<>"SnMat"];{matmaps[irrep][Cycles[{{1,2}}]],matmaps[irrep][Cycles[{Range[n]}]]}]
GetWGenerator[ynglist_]:=Module[{len=Length[ynglist],tdims,gens,wgens},tdims=SnIrrepDim/@ynglist[[All,2]];gens=IdentityMatrix/@tdims;
wgens=GetSnGenerators/@ynglist[[All,2]];
Association@MapThread[Rule,{ynglist[[All,1]],If[len===1,wgens,Table[SparseArray[KroneckerProduct@@ReplacePart[gens,i->Transpose@#]]&/@wgens[[i]],{i,len}]]}]
]
GetGaugeIndex[group_,replist_]:=Module[{indmap,indexct},indmap=Global`INDEX[CheckGroup[group]];indexct=AssociationThread[Union[Values[indmap]]->0];(IndexIterator[indmap[#1],indexct]&)/@replist]
GetBasisForType[model_,type_,OptionsPattern[]]:=Module[{particles=CheckType[model,type,Counting->False],state,k,replist,NAgroups=Select[model["Groups"],nonAbelian],ampgaugeind,gaugeind,repindrule,posRepeat,posnfl,yngList,len,lorBasis,gaugeBasis,factors,opBasis,opBasisw,generators,generatorsw,pCoord,ampresult=<||>,yngListamp,SoftPart,Kmy},
state=Delete[model[#]["helicity"]&/@particles,Position[model[#]["spurion"]&/@particles,True]];k=Exponent[type,"D"];
SoftPart=Position[model[#]["soft"]&/@particles,True]//Flatten;If[SoftPart==={},SoftPart=False];

replist=Outer[model[#2][#1]&,NAgroups,particles];

posRepeat=Select[PositionIndex[particles],Length[#]>1&];
posnfl=Values[KeySelect[PositionIndex[particles],model[#]["nfl"]>1&]];
yngList=IntegerPartitions@Length[#]&/@posRepeat;
yngList=Thread/@Distribute[{Keys[yngList]}->Distribute[Values[yngList],List],List];
If[OptionValue[NfSelect],yngList=Select[yngList,And@@(SQ[model]@@@#)&]];
posRepeat=Values[posRepeat];
len=Length[posRepeat];


lorBasis=LorentzBasisAux[state,k,posRepeat,OutputFormat->OptionValue[OutputFormat],newmethod->OptionValue[newmethod],AdlerZero->SoftPart];

Switch[OptionValue[OutputFormat],
"operator",lorBasis=MapAt[transform[#,ReplaceField->{model,type,OptionValue[FerCom]},OpenFchain->False,ActivatePrintTensor->False,Working->OptionValue[Working]]&,lorBasis,Key["basis"]],
"amplitude",lorBasis=MapAt[Ampform,lorBasis,Key["basis"]]
];(*Print[lorBasis];*)
gaugeBasis=MapThread[GaugeBasisAux[CheckGroup[model,#1],#2,posRepeat,Index->model["rep2indOut"][#1]]&,{NAgroups,replist}];
gaugeBasis=Append[#,"Trans"->FindGCoord/@#["basis"]]&/@gaugeBasis;
(*gaugeBasis=Append[#,"Trans"->IdentityMatrix[Length@#["basis"]]]&/@gaugeBasis;*)

(*amplitude output with repeated fields*)
If[OptionValue[OutputFormat]==="amplitude",ampgaugeind=Flatten[MapThread[Function[{u,v},("\!\(\*SubscriptBox[\("<>Take[model["rep2indOut"][u][#1[[1]]],1]<>"\), \("<>ToString[#1[[2]]]<>"\)]\)"&)/@v],{NAgroups,(DeleteCases[Thread[{#1,Range[Length[#1]]}],{{(0)..},_}]&)/@replist}]];(*gaugeind=Flatten[MapThread[Function[{u,v},(Take[model["rep2indOut"][u][#1[[1]]],#1[[2]]]&)/@v],{NAgroups,Tally/@(DeleteCases[#1,{(0)..}]&)/@Replace[replist,{x_/;OrderedQ[x]:>Reverse[x],x_:>Abs[x]},2]}]];*)
gaugeind=Flatten[MapThread[GetGaugeIndex[#1,#2]&,{NAgroups,(DeleteCases[#1,{(0)..}]&)/@Replace[replist,{x_/;OrderedQ[x]:>Reverse[x],x_:>Abs[x]},2]}]];repindrule=MapThread[Rule,{gaugeind,ampgaugeind}];gaugeBasis=gaugeBasis/. repindrule;];
factors=Merge[Append[gaugeBasis,lorBasis],Identity];
factors=MapAt[KeyMap[particles[[First[#]]]&],factors,{Key["generators"],All}];

If[OptionValue[findcor],opBasis=TensorProduct@@factors["basis"],
(*add amplitude outputformat*)
opBasis=If[OptionValue[OutputFormat]==="amplitude",TensorProduct@@factors["basis"],ContractDelta[TensorProduct@@factors["basis"],Working->OptionValue[Working]]];
(*opBasis=ContractDelta[TensorProduct@@factors["basis"],Working->OptionValue[Working]];*)(*Print[TensorProduct@@factors["basis"]//Flatten];*)
(*If[OptionValue[OutputFormat]=="operator",*)
If[!OptionValue[Working],opBasis=PrintOper[RefineReplace@opBasis]];
opBasis=opBasis//.listtotime];
(*,If[!OptionValue[Working],opBasis=RefineReplace@opBasis]];*)
Kmy=TensorProduct@@factors["Trans"];Do[Kmy=ArrayFlatten[Kmy],{re,Length@factors["Trans"]-1}];

If[Length[posRepeat]==0,Return[<|"basis"->GetWCs[posRepeat,posnfl,{}]Flatten@opBasis,"Kmy"->Kmy|>]];
generators=Merge[factors["generators"],SparseArray/@
Flatten[MapThread[TensorProduct,#],{{1},2Range[Length[NAgroups]+1],2Range[Length[NAgroups]+1]+1}]&];

(*add amplitude outputformat*)
If[OptionValue[OutputFormat]=="amplitude",
If[posRepeat=!={},
yngListamp=If[OddQ[2 model[#1[[1]]]["helicity"]],#1[[1]]->ConstantArray[1,Total[#1[[2]]]],#1[[1]]->{Total[#1[[2]]]}]&/@yngList[[1]];
Do[
generatorsw=Merge[{GetWGenerator[yng],generators},MapThread[KroneckerProduct,#]&];
opBasisw=Flatten@TensorProduct[GetWCs[posRepeat,posnfl,yng[[All,2]]],opBasis];
If[Length[opBasisw]==1,ampresult[yng]=opBasisw[[1]];Return[ampresult]];
pCoord=basisReducePro[Dot@@Merge[{generatorsw,#1},PermRepFromGenerator[#1[[1]],YO[#1[[2]]]]&]]["pos"]&@yngListamp;
If[pCoord!={},ampresult[yng]=opBasisw[[#]]&/@pCoord];
,{yng,yngList}];
Return[ampresult];
]
];


If[OptionValue[DeSym],
(* desym monomials *)
pCoord=AssociationMap[basisReducePro[Dot@@Merge[{generators,#},PermRepFromGenerator[#[[1]],YO[#[[2]]]]&]]["pos"]&,yngList];
If[OptionValue[printkpm],
Join[Map[Part[Flatten[opBasis],#]&,pCoord,{2}],<|"p-basis"->Partition[Flatten@Values[Select[AssociationMap[basisReducePro[Dot@@Merge[{generators,#},PermRepFromGenerator[#[[1]],YO[#[[2]]]]&]]["mvalues"]&,yngList],Flatten[#]!={}&]],Length[Flatten@opBasis]],"Kmy"->Kmy|>],
Map[Part[Flatten[opBasis],#]&,pCoord,{2}]],
(* sym result *)
Switch[OptionValue[TakeFirstBasis],
True,pCoord=AssociationMap[basisReducePro[Dot@@Merge[{generators,#},PermRepFromGenerator[#[[1]],YO[#[[2]]]]&]]["mvalues"]&,yngList],
False,
(* full basis *)
pCoord=AssociationMap[basisReduceByFirst[Outer[Dot,##,1]&@@Merge[{generators,#},Table[PermRepFromGenerator[#[[1]],YO[#[[2]],1,i]],{i,SnIrrepDim[#[[2]]]}]&],len]&,yngList]
];
pCoord=Select[pCoord,Flatten[#]!={}&];
<|"basis"->Flatten@opBasis,"p-basis"->pCoord,"Kpy"->Partition[Flatten@Values[pCoord],Length[Flatten@opBasis]],"Kmy"->Kmy|>]
]
Options[GetBasisForType]={OutputFormat->"operator",Working->False,FerCom->2,NfSelect->True,DeSym->False,TakeFirstBasis->True,newmethod->False,findcor->False,printkpm->False};



(* ::Input::Initialization:: *)
GetJBasisForType[model_,type_,partition_,OptionsPattern[]]:=Module[{particles=CheckType[model,type,Counting->False],numpar,state,k,replist,abreplist,NAgroups=Select[model["Groups"],nonAbelian],Agroups = OptionValue[Charges],lorBasis,gaugeBasis,
factors,opBasis,jCoord,result=<||>},
numpar=Length[particles];
state=(model[#1]["helicity"]&)/@particles;k=Exponent[type,"D"];
replist=Outer[model[#2][#1]&,NAgroups,particles];

If[Agroups=={},abreplist=ConstantArray[{},Length[partition]],
abreplist = Outer[model[#2][#1] &, Agroups, particles];
abreplist = Merge[Table[AssociationMap[Total@Part[item, #] &, partition], {item, abreplist}],Identity]
];

Switch[OptionValue[OutputFormat],
"amplitude",lorBasis=LorentzJBasis[state,k,partition],
"operator",lorBasis=MapAt[MonoLorentzBasis[#,Length[state],finalform->False]["LorBasis"]&,
LorentzJBasis[state,k,partition],Key["basis"]];
lorBasis["basis"]=transform[lorBasis["basis"],ReplaceField->{model,type,OptionValue[FerCom]},
OpenFchain->False,ActivatePrintTensor->False,Working->OptionValue[Working]];
];
gaugeBasis=MapThread[GaugeJBasis[CheckGroup[#1],#2,parsePart[partition,numpar],Index->model["rep2indOut"][#1]]&,{NAgroups,replist}];
factors=Merge[Append[gaugeBasis,lorBasis],Identity];

If[OptionValue[OutputFormat]=="operator",
opBasis=ContractDelta[TensorProduct@@factors["basis"],Working->OptionValue[Working]];
If[!OptionValue[Working],opBasis=PrintOper[RefineReplace@opBasis]];
opBasis=opBasis//.listtotime];

jCoord=Merge[#[[All,1]],Identity]->(Flatten/@TensorProduct@@@Distribute[#[[All,2]],List])&/@Distribute[factors["jcoord"],List];If[jCoord!={},
jCoord = MapAt[Merge[{#,abreplist},Apply[Join]]&,jCoord,{All, 1}];
jCoord=MapAt[KeyMap[Map[Subscript[Part[particles,#],#]&]],jCoord,{All,1}]];
Return[<|"basis"->Flatten[opBasis],"groups"-> Join[NAgroups,{"Spin"},Agroups],"j-basis"->jCoord|>];
]
Options[GetJBasisForType]={OutputFormat->"operator",FerCom->2,Charges->{},Working->False};

GetVertices[model_,type_,key_]:=Module[{particles=CheckType[model,type,Counting->False],npart,state,normpart,part,hcy=<||>,vert},npart=Length@particles;
state=(Rule[{#1},model[particles[[#1]]]["helicity"]]&)/@Range[npart];
normpart=MapAt[Last,Normal[key],{All,1,All}];
normpart=MapAt[#[[-1]]&,normpart,{All,2}];
part=normpart[[All,1]];
part=UnionFinder[parsePart[part,npart]];
HierarchyFinder[hcy,#]&/@part;
hcy=Normal@hcy;
hcy=DeleteCases[hcy,{_}->{{_}}];
If[Length[part]>2,AppendTo[hcy,#[[1]]&/@part]];
vert={Cases[#,{_}],Cases[#,{_,__}]}&/@(hcy/.Rule[{x_,z__},y_]:>Append[y,{x,z}]);
vert/.state/.normpart]
AllowedResonance[model_,type_,resPattern_,allowedVertices_]:=And@@(MemberQ[allowedVertices,Sort/@#]&/@GetVertices[model,type,resPattern])


(* ::Input::Initialization:: *)
Options[GenerateOperatorList]={ShowClass->True,AllClass->False,T2TOptions->{}};
GenerateOperatorList[model_,dim_Integer,OptionsPattern[]]:=Module[{start=SessionTime[],states,types,len,class,iter=0,assoc=<||>,temp},
Print["Generating types of operators ..."];
types=AllTypesC[model,dim];
If[OptionValue[ShowClass],
Print["Evaluating class: ",Dynamic[class]," (",Dynamic[iter],"/",Length[types],")"];
Do[If[ !OptionValue[AllClass]&&types[class]=={},Continue[]];
temp=AssociationMap[Type2TermsPro[model,#,Sequence@@OptionValue[T2TOptions]]&,types[class]];
AssociateTo[assoc,class->DeleteCases[temp,<||>]];
iter++,{class,Keys[types]}],

assoc=AssociationMap[Type2TermsPro[model,#,Sequence@@OptionValue[T2TOptions]]&,Catenate@types];
assoc=DeleteCases[assoc,<||>];
];
Print["Time spent: ",SessionTime[]-start];
Return[assoc];
]
GenerateOperatorList[model_,types_List,OptionsPattern[]]:=DeleteCases[<||>]@AssociationMap[Type2TermsPro[model,#,Sequence@@OptionValue[T2TOptions]]&,types]


(* ::Subsection:: *)
(*End of Package*)


(* ::Input::Initialization:: *)
If[Global`$DEBUG,Begin["`Private`"]]
End[];
EndPackage[]



