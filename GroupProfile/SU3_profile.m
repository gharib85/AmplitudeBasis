(* ::Package:: *)

(* ::Input:: *)
(*(* put in the main file *)*)
(*PrintTensor=\!\(\**)
(*TagBox[*)
(*StyleBox[*)
(*RowBox[{"\"\<\\!\\(\\*SubsuperscriptBox[\\(\>\"", "<>", "#tensor", "<>", "\"\<\\), \\(\>\"", "<>", "#downind", "<>", "\"\<\\), \\(\>\"", "<>", "#upind", "<>", "\"\<\\)]\\)\>\""}],*)
(*ShowSpecialCharacters->False,*)
(*ShowStringCharacters->True,*)
(*NumberMarks->True],*)
(*FullForm]\)&;*)
(*GellMann[n_]:=GellMann[n]=Flatten[Table[(*Symmetric case*)SparseArray[{{j,k}->1,{k,j}->1},{n,n}],{k,2,n},{j,1,k-1}],1]~Join~Flatten[Table[(*Antisymmetric case*)SparseArray[{{j,k}->-I,{k,j}->+I},{n,n}],{k,2,n},{j,1,k-1}],1]~Join~Table[(*Diagonal case*)Sqrt[2/l/(l+1)] SparseArray[Table[{j,j}->1,{j,1,l}]~Join~{{l+1,l+1}->-l},{n,n}],{l,1,n-1}];*)


(* ::Input::Initialization:: *)
If[!AssociationQ[tRep],tRep=<||>];
If[!AssociationQ[tOut],tOut=<||>];
If[!AssociationQ[tList],tList=<||>];
tList[SU3]={del3,eps3a,eps3f,\[Lambda],del8n,fabc,dabc};
If[!AssociationQ[tVal],tVal=<||>];
tVal[SU3]={del3->IdentityMatrix[3],eps3f->LeviCivitaTensor[3],eps3a->LeviCivitaTensor[3],\[Lambda]->GellMann[3],del8n->IdentityMatrix[8],fabc->fG,dabc->dG};
If[!AssociationQ[tYDcol],tYDcol=<||>];
tYDcol[SU3]=eps3a;
If[!IntegerQ[dummyIndexCount],dummyIndexCount=0];
If[!AssociationQ[rep2ind],rep2ind=<||>];
AssociateTo[rep2ind,{{0,0}->Function[x,Nothing],{1,0}->b,{0,1}->b,{1,1}->B}];


(* ::Input::Initialization:: *)
(* Define invariant tensors *)
AppendTo[tAssumptions,del3\[Element]Arrays[{3,3},Reals]];
tRep[del3]={{1,0},{0,1}};
tOut[del3]=PrintTensor[<|"tensor"->"\[Delta]","upind"->ToString[#2],"downind"->ToString[#1]|>]&;

AppendTo[tAssumptions,eps3a\[Element]Arrays[{3,3,3},Reals,Antisymmetric[{1,2,3}]]];
tRep[eps3a]={{0,1},{0,1},{0,1}};
tOut[eps3a]=PrintTensor[<|"tensor"->"\[Epsilon]","upind"->StringJoin@@ToString/@{#1,#2},"downind"->""|>]&;

AppendTo[tAssumptions,eps3f\[Element]Arrays[{3,3,3},Reals,Antisymmetric[{1,2,3}]]];
tRep[eps3f]{{1,0},{1,0},{1,0}};
tOut[eps3f]=PrintTensor[<|"tensor"->"\[Epsilon]","upind"->"","downind"->StringJoin@@ToString/@{#1,#2}|>]&;

AppendTo[tAssumptions,\[Lambda]\[Element]Arrays[{8,3,3},Reals]];
tRep[\[Lambda]]->{{1,1},{1,0},{0,1}};
tOut[\[Lambda]]=PrintTensor[<|"tensor"-> PrintTensor[<|"tensor"->"\[Lambda]","upind"->ToString[#1],"downind"->""|>],"upind"->ToString[#3],"downind"->ToString[#2]|>]&;

AppendTo[tAssumptions,del8n\[Element]Arrays[{8,8},Reals,Symmetric[{1,2}]]];
tRep[del8n]={{1,1},{1,1}};
tOut[del8n]=PrintTensor[<|"tensor"->"\[Delta]","upind"->StringJoin@@ToString/@{#1,#2},"downind"->""|>]&;

AppendTo[tAssumptions,fabc\[Element]Arrays[{8,8,8},Reals,Antisymmetric[{1,2,3}]]];
tRep[fabc]={{1,1},{1,1},{1,1}};
tOut[fabc]=PrintTensor[<|"tensor"->"f","upind"->StringJoin@@ToString/@{#1,#2,#3},"downind"->""|>]&;
fG=SymmetrizedArray[-(I/4)Table[Tr[\[Lambda]G[[a]].\[Lambda]G[[b]].\[Lambda]G[[c]]-\[Lambda]G[[b]].\[Lambda]G[[a]].\[Lambda]G[[c]]],{a,8},{b,8},{c,8}]];

AppendTo[tAssumptions,dabc\[Element]Arrays[{8,8,8},Reals,Symmetric[{1,2,3}]]];
tRep[dabc]={{1,1},{1,1},{1,1}};
tOut[dabc]=PrintTensor[<|"tensor"->"d","upind"->StringJoin@@ToString/@{#1,#2,#3},"downind"->""|>]&;
dG=SymmetrizedArray[1/4 Table[Tr[\[Lambda]G[[a]].\[Lambda]G[[b]].\[Lambda]G[[c]]+\[Lambda]G[[b]].\[Lambda]G[[a]].\[Lambda]G[[c]]],{a,8},{b,8},{c,8}]];


(* ::Input::Initialization:: *)
(* invariant tensor simplification *)
Unprotect[Times];
Clear[Times];
dummyIndexCount=0;
del3[i_,j_]del3[j_,k_]:=del3[i,k];
del3[i_,i_]:=3;
del8n[i_,i_]:=8;
del3n[a_,d_]eps3n[a_,b_,c_]:=eps3n[d,b,c]
del3n[a_,d_]eps3n[b_,a_,c_]:=eps3n[b,d,c]
del3n[a_,d_]eps3n[c_,b_,a_]:=eps3n[c,b,d]
del3n[a_,c_]del3n[a_,b_]:=del3n[c,b]
SetAttributes[del8n,Orderless];
eps3a[i_,j_,k_]eps3f[l_,m_,n_]=Det@Map[del3@@#&, Partition[Distribute[{{i,j,k},{l,m,n}},List],3],{2}];
del3[a_,c_]\[Lambda][J_,a_,b_]:=\[Lambda][J,c,b];
del3[c_,a_]\[Lambda][J_,b_,a_]:=\[Lambda][J,b,c];
\[Lambda][i_,j_,j_]:=0;
eps3f[i_,j_,k_]del3[i_,l_]:=eps3f[l,j,k];
eps3f[i_,j_,k_]del3[j_,l_]:=eps3f[i,l,k];
eps3f[i_,j_,k_]del3[k_,l_]:=eps3f[i,j,l];
eps3a[i_,j_,k_]del3[l_,i_]:=eps3a[l,j,k];
eps3a[i_,j_,k_]del3[l_,j_]:=eps3a[i,l,k];
eps3a[i_,j_,k_]del3[l_,k_]:=eps3a[i,j,l];
SetAttributes[dabc,Orderless];
del8n[a_,d_]fabc[a_,b_,c_]:=fabc[d,b,c]
del8n[a_,d_]fabc[b_,a_,c_]:=fabc[b,d,c]
del8n[a_,d_]fabc[c_,b_,a_]:=fabc[c,b,d]
del8n[a_,d_]dabc[a_,b_,c_]:=dabc[d,b,c]
del8n[a_,d_]dabc[b_,a_,c_]:=dabc[b,d,c]
del8n[a_,d_]dabc[c_,b_,a_]:=dabc[c,b,d]
del8n[a_,c_]del8n[a_,b_]:=del8n[c,b]
\[Lambda][i_,j_,k_]\[Lambda][l_,k_,m_]:=Module[{},dummyIndexCount++;(I fabc[i,l,dummyIndex[dummyIndexCount]]+dabc[i,l,dummyIndex[dummyIndexCount]])\[Lambda][dummyIndex[dummyIndexCount],j,m]+2/3 del8n[i,l]del3[m,j]]
Protect[Times];


ConvertToFundamental[groupname_,{0,1}]:=If[GetGroup[groupname]==SU3,Times@@(eps3f[b[fname,#,1],bb[fname,#,1],bb[fname,#,2]]&/@Range[1,num]),Message[ConvertToFundamental::name]]


ConvertFactor[model_,groupname_,input_]:=
(*input is the form {field,num}, *)
Module[{fname=input[[1]],num=input[[2]],rep},
rep=model[fname][groupname];
Switch[rep,
{0,1}, Return[Times@@(eps3f[b[fname,#,1],bb[fname,#,1],bb[fname,#,2]]&/@Range[1,num])],
{1,1},Return[ Times@@(\[Lambda][B[fname,#,1],b[fname,#,2],e[fname,#,1]]eps3f[e[fname,#,1],b[fname,#,1],b[fname,#,3]]&/@Range[1,num])],
_,Return[1]
]
]


(* ::Input:: *)
(*(* example *)*)
(*dabc[a,b,c]/.dabc->tOut[dabc]*)
(*\[Lambda][A,a,b]/.\[Lambda]->tOut[\[Lambda]]*)