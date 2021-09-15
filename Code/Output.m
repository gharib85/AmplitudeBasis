(* ::Package:: *)

(* ::Input::Initialization:: *)
PrintTensor[tensor_Association]:=Module[{print="\!\(\*SubsuperscriptBox[\("<>#tensor<>"\), \("<>#downind<>"\), \("<>#upind<>"\)]\)"&,t},
t=Merge[{StringJoin@@@tensor,<|"tensor"->"","downind"->"","upind"->""|>},StringJoin];
print[t]
]
PrintTensor[x_:Except[_Association]]:=x

AddIndex[tensor_,index_]:=tensor=Merge[{tensor,List/@Association[index]},If[Length[#]==1&&Depth[#]==2,#[[1]],Flatten[#]]&]
SetAttributes[AddIndex,HoldFirst];


(* ::Input::Initialization:: *)
(******************* Group tensor formating **********************)

Sortarg[asTlist_]:= #[y__] :> Signature[#[y]]Sort[#[y]]& /@ asTlist 
RefineReplace[x_,OptionsPattern[]]:=Module[{asTlist,printreplace},
If[Length[tOut]==0,Return[x]];
asTlist=Select[Keys[tOut],MatchQ[tSymmetry[#],_Antisymmetric]&];printreplace=If[OptionValue[ActivatePrintTensor],tOut,Inactivate[#,PrintTensor]&/@tOut];
Return[x/.Sortarg[asTlist]/.printreplace]
]
SetAttributes[RefineReplace,Listable];
Options[RefineReplace]={ActivatePrintTensor->True};

(* Generate the replacing rule of the tensor indices for the final output form *)
GenerateReplacingRule[model_,type:(_Times|_Power)]:=GenerateReplacingRule[model,CheckType[model,type]]
GenerateReplacingRule[model_,flist_List]:=Module[{nonsingletlist,fexpand,symbollist,arglist,listind,listgen,indexct,indpair,listdummy},
nonsingletlist=AssociationMap[Function[groupname,Select[flist,Function[fname,model[fname[[1]]][groupname]!=Singlet[CheckGroup[groupname]]]]],Select[model["Groups"],nonAbelian]]; 
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

changebracket[b_ab]:=AngleBracket[StringJoin@@ToString/@b]
changebracket[b_sb]:=<|"tensor"->"["<>StringJoin@@ToString/@b<>"]"|>
changebracket[s_sMand]:=<|"tensor"->"s","downind"-> StringJoin@@ToString/@s|>
changebracket[p_Power]:=Switch[p[[1]],
_sb|_sMand,Merge[{changebracket[p[[1]]],<|"upind"->ToString[p[[2]]]|>},StringJoin],
_ab,Power[changebracket[p[[1]]],p[[2]]],
_,p]
changebracket[x_]:=x

SetAttributes[Ampform,Listable];
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


(* ::Input::Initialization:: *)
(* Operator formating *)
SetAttributes[{SetIndex1,SetIndex2},HoldAll]; 
Options[SetIndex1]={FieldRename->{}};
Options[SetIndex2]={FieldRename->{}};
Options[groupindex1]={FieldRename->{}};
Options[groupindex2]={FieldRename->{}};
SetIndex1[model_,field_,label_,indexct_,flavorct_,OptionsPattern[]]:=Module[{hel=model[field]["helicity"],fieldname=ToExpression@field,head=Identity,su2antiflag=False,irrep,group,indexList,index,tensorform},If[model[field]["stat"]=="fermion"&&MemberQ[OptionValue[FieldRename],"set chirality"],fieldname=model[field]["chirality"][[1]];head=model[field]["chirality"][[2]];If[head=="right",fieldname=OverBar[fieldname]]];If[model[field]["nfl"]==1,tensorform=fieldname,tensorform=Subscript[fieldname,model[field]["indfl"][[++flavorct]]]];Do[irrep=model[field][groupname];group=CheckGroup[model,groupname];indexList=model["rep2indOut"][groupname][irrep];If[indexList=={},tensorform=tensorform[];Continue[]];index=IndexIterator[indexList,indexct];
tensorform=tensorform[index],{groupname,Select[model["Groups"],nonAbelian]}];Subscript[h2f[hel], label]->head[tensorform]]
SetIndex2[model_, field_, label_,indexct_,flavorct_,OptionsPattern[]] :=
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
FullForm]\)]]; (* set fermion name according to chirality *)
tensorform=<|"tensor"->fieldname|>;
If[model[field]["nfl"]>1,AddIndex[tensorform,"downind"-> model[field]["indfl"][[++flavorct]]];
tensorform["tensor"]=Inactive[PrintTensor]@tensorform;
KeyDropFrom [tensorform,"downind"]]; (* add flavor index *)
If[StringTake[field,-1] == "\[Dagger]", su2antiflag = True];
Do[irrep=model[field][groupname];
group=CheckGroup[model,groupname];
indexList=model["rep2indOut"][groupname][irrep];
If[indexList=={},Continue[]]; (* singlet *)
index=IndexIterator[indexList,indexct];
If[Fund[group]==irrep,If[group==SU2&&su2antiflag,AddIndex[tensorform,"upind"->index],AddIndex[tensorform,"downind"->index]],
AddIndex[tensorform,"upind"->{index}]],
{groupname,Select[model["Groups"],nonAbelian]}];
Subscript[h2f[hel], label] -> head[Inactive[PrintTensor]@tensorform]
]
groupindex1[model_, flistexpand_,OptionsPattern[]] := Module[{indexct,flavorct=0, n= Length[flistexpand]},
indexct=AssociationThread[Union@Catenate[model["rep2indOut"]]->0];
MapThread[SetIndex1[model, #1, #2,indexct,flavorct,FieldRename->OptionValue[FieldRename]] & , {flistexpand,Range[n]}]
]
groupindex2[model_, flistexpand_,OptionsPattern[]] := Module[{indexct,flavorct=0, n= Length[flistexpand]},
indexct=AssociationThread[Union@Catenate[model["rep2indOut"]]->0];
MapThread[SetIndex2[model, #1, #2,indexct,flavorct,FieldRename->OptionValue[FieldRename]] & , {flistexpand,Range[n]}]
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
FtoTensor1:={F_["up"|"down",a_,"up"|"down",b_]:>F[a,b]}
FtoTensor2:=Inactivate[{F_["down",a_,"down",b_]:>PrintTensor[<|"tensor"->F,"downind"->{a,b}|>],
F_["down",a_,"up",b_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->F,"downind"->a|>],"upind"->b|>],
F_["up",a_,"down",b_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->F,"upind"->a|>],"downind"->b|>],
F_["up",a_,"up",b_]:>PrintTensor[<|"tensor"->F,"upind"->{a,b}|>],CL_["down",a_,"down",b_,"down",c_,"down",d_]:>PrintTensor[<|"tensor"->CL,"downind"->{a,b,c,d}|>],
CL_["down",a_,"up",b_,"down",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->a|>],"upind"->b|>],"downind"->{c,d}|>],
CL_["up",a_,"down",b_,"down",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->a|>],"downind"->{b,c,d}|>],
CL_["up",a_,"up",b_,"down",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->{a,b}|>],"downind"->{c,d}|>],
CL_["down",a_,"down",b_,"down",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->{a,b,c}|>],"upind"->d|>],
CL_["down",a_,"up",b_,"down",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->a|>],"upind"->b|>],"downind"->c|>],"upind"->d|>],
CL_["up",a_,"down",b_,"down",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->a|>],"downind"->{b,c}|>],"upind"->d|>],
CL_["up",a_,"up",b_,"down",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->{a,b}|>],"downind"->c|>],"upind"->d|>],CL_["down",a_,"down",b_,"up",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->{a,b}|>],"upind"->c|>],"downind"->d|>],
CL_["down",a_,"up",b_,"up",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->a|>],"upind"->{b,c}|>],"downind"->d|>],
CL_["up",a_,"down",b_,"up",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->a|>],"downind"->b|>],"upind"->c|>],"downind"->d|>],
CL_["up",a_,"up",b_,"up",c_,"down",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->{a,b,c}|>],"downind"->d|>],
CL_["down",a_,"down",b_,"up",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->{a,b}|>],"upind"->{c,d}|>],
CL_["down",a_,"up",b_,"up",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"downind"->a|>],"upind"->{b,c,d}|>],
CL_["up",a_,"down",b_,"up",c_,"up",d_]:>PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->PrintTensor[<|"tensor"->CL,"upind"->a|>],"downind"->b|>],"upind"->{c,d}|>],
CL_["up",a_,"up",b_,"up",c_,"up",d_]:>PrintTensor[<|"tensor"->CL,"upind"->{a,b,c,d}|>]},PrintTensor];

transform[ope_, OptionsPattern[]] := Module[{result=ope,model, type, fer, fieldlist,Dcon={},fchain={},l2t={},f2t={},gind={},fieldrename={}},
If[OptionValue[Dcontract],Dcon=Flatten[{Dcontract1, Dcontract2}]];
If[OptionValue[OpenFchain],l2t=listtotime];
If[OptionValue[Working],f2t=FtoTensor1,f2t=FtoTensor2];
If[OptionValue[ReplaceField] === {},Return[result//.Dcon//.f2t//.l2t]]; (* abstract operators *)
{model, type, fer} = OptionValue[ReplaceField];
fieldlist = CheckType[model,type,Counting->False];
If[OptionValue[Working],gind=groupindex1[model,fieldlist,FieldRename->fieldrename],gind=groupindex2[model,fieldlist,FieldRename->fieldrename]];
If[fer==4,AppendTo[fieldrename,"set chirality"]; (* rename fermion due to conventional chirality *)
result=result//.{\[Sigma]^(a_) | OverBar[\[Sigma]]^(a_) :> \[Gamma]^a,Subscript[\[Sigma] |  OverBar[\[Sigma]], a_] :> Subscript[\[Gamma], a], Superscript[\[Sigma] | OverBar[\[Sigma]],a_] :> Superscript[\[Gamma], a]}
//. {(a_)[(b_)[\[Gamma], a1_], b1_] :>a[b[\[Sigma], a1], b1]}; (* change \[Sigma] matrices to \[Gamma] matrices *)
fchain=spinorH2C
];
result=result//.Dcon//.f2t/.gind;
(*result=result/.Activate[groupindex[model,fieldlist,FieldRename->fieldrename],If[OptionValue[ActivatePrintTensor],PrintTensor,Null]];*)
If[OptionValue[ActivatePrintTensor],result=Map[Activate,result,\[Infinity]]];
result/.fchain//.l2t
]
Options[transform] = {OpenFchain->True,ActivatePrintTensor->True,Dcontract -> True, ReplaceField -> {},Working->False}; 


(* ::Input::Initialization:: *)
Options[PrintOper]={OpAbbr->{}};
PrintOper[beforeprint_Times,OptionsPattern[]]:=Module[{factors,abbr=OptionValue[OpAbbr],bosons=1,others=1},
factors=GroupBy[Map[Activate,List @@beforeprint,\[Infinity]],StringQ];
If[KeyExistsQ[factors,True],bosons=StringJoin@@(factors[True]/.abbr)];
If[KeyExistsQ[factors,False],others=Times@@(factors[False]/.abbr)];
Return[bosons*others]
]
SetAttributes[PrintOper,Listable];


(* ::Input::Initialization:: *)
PrintStat[model_,dim_Integer,OptionsPattern[]]:=Module[{start,stat},
Print["-----------------------"];
Print["Enumerating dim ",dim," operators ..."];
start=SessionTime[];
types=Catenate@AllTypesC[model,dim];
Print[" --- find all types (time: ",SessionTime[]-start,")"];
stat=StatResult[model,types];
KeyValueMap[Print["number of ",#1,": ",#2]&,stat];
Print["total time: ",SessionTime[]-start];
]


(* ::Input::Initialization:: *)
(* Draws the Young diagram with the associated partition \[Lambda] *)
Options[DrawYoungDiagram]={ScaleFactor->20};
DrawYoungDiagram[\[Lambda]_,OptionsPattern[]]:=Module[{t\[Lambda],horizontalLines,verticalLines,result},
If[\[Lambda]==={},Return[Graphics[{},ImageSize->0]]];
t\[Lambda]=TransposePartition[\[Lambda]];

horizontalLines=Table[Line[{{0,-i},{\[Lambda][[i]],-i}}],{i,Length[\[Lambda]]}];
PrependTo[horizontalLines,Line[{{0,0},{\[Lambda][[1]],0}}]];
verticalLines=Table[Line[{{i,0},{i,-t\[Lambda][[i]]}}],{i,Length[t\[Lambda]]}];
PrependTo[verticalLines,Line[{{0,0},{0,-t\[Lambda][[1]]}}]];
result=Graphics[Join[horizontalLines,verticalLines],ImageSize->(OptionValue[ScaleFactor]Length[t\[Lambda]]),ImagePadding->None,ImageMargins->0,PlotRange->{{0,Length[t\[Lambda]]+0.2},{-(Length[\[Lambda]]+0.2),0}}];

Return[result];
]

(* Leave a 1-pixel border around the picture, because Mathematica sometimes crops the images *)
DrawYoungDiagramRaster[\[Lambda]_,scaleFactor_:9]:=DrawYoungDiagramRaster[\[Lambda],scaleFactor]=Module[{t\[Lambda],horizontalLines,verticalLines,result,nH,nV,dataArray},
If[\[Lambda]==={},Return[Null]];
t\[Lambda]=TransposePartition[\[Lambda]];

nH=scaleFactor Length[t\[Lambda]]+1;
nV=scaleFactor Length[\[Lambda]]+1;

horizontalLines=Table[{{0,-i},{\[Lambda][[i]],-i}},{i,Length[\[Lambda]]}];
PrependTo[horizontalLines,{{0,0},{\[Lambda][[1]],0}}];
verticalLines=Table[{{i,0},{i,-t\[Lambda][[i]]}},{i,Length[t\[Lambda]]}];
PrependTo[verticalLines,{{0,0},{0,-t\[Lambda][[1]]}}];

horizontalLines=scaleFactor horizontalLines;
verticalLines=scaleFactor verticalLines;

dataArray=ConstantArray[1,2+{nV,nH}]; (* leave 1 pixel border *)
Do[
dataArray[[2-hl[[1,2]],2+hl[[1,1]];;2+hl[[2,1]]]]=0dataArray[[2-hl[[1,2]],2+hl[[1,1]];;2+hl[[2,1]]]];
,{hl,horizontalLines}];
Do[
dataArray[[2-vl[[1,2]];;2-vl[[2,2]],2+vl[[1,1]]]]=0dataArray[[2-vl[[1,2]];;2-vl[[2,2]],2+vl[[1,1]]]];
,{vl,verticalLines}];

(* leave 1 pixel border *)
result=SetAlphaChannel[Image[dataArray,ImageSize->2+{nH,nV}],Image[1-dataArray,ImageSize->2+{nH,nV}]];
Return[result];
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
