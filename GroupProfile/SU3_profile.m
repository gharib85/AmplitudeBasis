(* ::Package:: *)

(* ::Input::Initialization:: *)
(* Initialization *)
If[MatchQ[groupList,_List],AppendTo[groupList,SU3],groupList={SU3}];
If[!AssociationQ[tRep],tRep=<||>];
If[!AssociationQ[tOut],tOut=<||>];
If[!AssociationQ[tList],tList=<||>];
tList[SU3]={del3,eps3a,eps3f,\[Lambda],del8n,fabc,dabc};
If[!AssociationQ[tVal],tVal=<||>];
tVal[SU3]={del3->IdentityMatrix[3],eps3f->LeviCivitaTensor[3],eps3a->LeviCivitaTensor[3],\[Lambda]->GellMann[3],del8n->IdentityMatrix[8],fabc->fG,dabc->dG};
If[!AssociationQ[tYDcol],tYDcol=<||>];
tYDcol[SU3]=eps3a;
If[!IntegerQ[dummyIndexCount],dummyIndexCount=0];
If[!AssociationQ[tSimp],tSimp=<||>];


(* ::Input::Initialization:: *)
(* Define invariant tensors *)
AppendTo[tAssumptions,del3\[Element]Arrays[{3,3},Reals]];
tRep[del3]={{1,0},{0,1}};
tOut[del3]=PrintTensor[<|"tensor"->"\[Delta]","upind"->#2,"downind"->#1|>]&;

AppendTo[tAssumptions,eps3a\[Element]Arrays[{3,3,3},Reals,Antisymmetric[{1,2,3}]]];
tRep[eps3a]={{0,1},{0,1},{0,1}};
tOut[eps3a]=PrintTensor[<|"tensor"->"\[Epsilon]","upind"->StringJoin[#1,#2,#3],"downind"->""|>]&;

AppendTo[tAssumptions,eps3f\[Element]Arrays[{3,3,3},Reals,Antisymmetric[{1,2,3}]]];
tRep[eps3f]={{1,0},{1,0},{1,0}};
tOut[eps3f]=PrintTensor[<|"tensor"->"\[Epsilon]","upind"->"","downind"->StringJoin[#1,#2,#3]|>]&;

AppendTo[tAssumptions,\[Lambda]\[Element]Arrays[{8,3,3},Reals]];
tRep[\[Lambda]]={{1,1},{1,0},{0,1}};
tOut[\[Lambda]]=PrintTensor[<|"tensor"-> PrintTensor[<|"tensor"->"\[Lambda]","upind"->#1,"downind"->""|>],"upind"->#3,"downind"->#2|>]&;
\[Lambda]G=GellMann[3];

AppendTo[tAssumptions,del8n\[Element]Arrays[{8,8},Reals,Symmetric[{1,2}]]];
tRep[del8n]={{1,1},{1,1}};
tOut[del8n]=PrintTensor[<|"tensor"->"\[Delta]","upind"->StringJoin[#1,#2],"downind"->""|>]&;

AppendTo[tAssumptions,fabc\[Element]Arrays[{8,8,8},Reals,Antisymmetric[{1,2,3}]]];
tRep[fabc]={{1,1},{1,1},{1,1}};
tOut[fabc]=PrintTensor[<|"tensor"->"f","upind"->StringJoin[#1,#2,#3],"downind"->""|>]&;
fG=SymmetrizedArray[-(I/4)Table[Tr[\[Lambda]G[[a]].\[Lambda]G[[b]].\[Lambda]G[[c]]-\[Lambda]G[[b]].\[Lambda]G[[a]].\[Lambda]G[[c]]],{a,8},{b,8},{c,8}]];

AppendTo[tAssumptions,dabc\[Element]Arrays[{8,8,8},Reals,Symmetric[{1,2,3}]]];
tRep[dabc]={{1,1},{1,1},{1,1}};
tOut[dabc]=PrintTensor[<|"tensor"->"d","upind"->StringJoin[#1,#2,#3],"downind"->""|>]&;
dG=SymmetrizedArray[1/4 Table[Tr[\[Lambda]G[[a]].\[Lambda]G[[b]].\[Lambda]G[[c]]+\[Lambda]G[[b]].\[Lambda]G[[a]].\[Lambda]G[[c]]],{a,8},{b,8},{c,8}]];


(* ::Input::Initialization:: *)
tSimp[SU3]=Hold[Block[{},
del3[i_,j_]del3[j_,k_]:=del3[i,k];
del3[i_,i_]:=3;
del8n[i_,i_]:=8;
del3n[a_,d_]eps3n[a_,b_,c_]:=eps3n[d,b,c];
del3n[a_,d_]eps3n[b_,a_,c_]:=eps3n[b,d,c];
del3n[a_,d_]eps3n[c_,b_,a_]:=eps3n[c,b,d];
del3n[a_,c_]del3n[a_,b_]:=del3n[c,b];
SetAttributes[del8n,Orderless];
eps3a[i_String,j_String,k_String]eps3f[l_String,m_String,n_String]:=Det@Map[Apply[del3], Partition[Distribute[{{i,j,k},{l,m,n}},List],3],{2}]/;Intersection@@(First/@Position[INDEXSET,#]&/@{i,j,k,l,m,n})!={};
eps3a[i:Except[_String],j_,k_]eps3f[l_,m_,n_]:=Det@Map[Apply[del3], Partition[Distribute[{{i,j,k},{l,m,n}},List],3],{2}]/;Equal@@Head/@{i,j,k,l,m,n};
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
del8n[a_,d_]fabc[a_,b_,c_]:=fabc[d,b,c];
del8n[a_,d_]fabc[b_,a_,c_]:=fabc[b,d,c];
del8n[a_,d_]fabc[c_,b_,a_]:=fabc[c,b,d];
del8n[a_,d_]dabc[a_,b_,c_]:=dabc[d,b,c];
del8n[a_,d_]dabc[b_,a_,c_]:=dabc[b,d,c];
del8n[a_,d_]dabc[c_,b_,a_]:=dabc[c,b,d];
del8n[a_,c_]del8n[a_,b_]:=del8n[c,b];
\[Lambda][i_,j_,k_]\[Lambda][l_,k_,m_]:=Module[{},dummyIndexCount++;(I fabc[i,l,dummyIndex[dummyIndexCount]]+dabc[i,l,dummyIndex[dummyIndexCount]])\[Lambda][dummyIndex[dummyIndexCount],j,m]+2/3 del8n[i,l]del3[m,j]]
]]


(* ::Input:: *)
(*(* invariant tensor simplification *)*)
(*Unprotect[Times];*)
(*Clear[Times];*)
(*If[!IntegerQ[dummyIndexCount],dummyIndexCount=0];*)
(*del3[i_,j_]del3[j_,k_]:=del3[i,k];*)
(*del3[i_,i_]:=3;*)
(*del8n[i_,i_]:=8;*)
(*del3n[a_,d_]eps3n[a_,b_,c_]:=eps3n[d,b,c]*)
(*del3n[a_,d_]eps3n[b_,a_,c_]:=eps3n[b,d,c]*)
(*del3n[a_,d_]eps3n[c_,b_,a_]:=eps3n[c,b,d]*)
(*del3n[a_,c_]del3n[a_,b_]:=del3n[c,b]*)
(*SetAttributes[del8n,Orderless];*)
(*eps3a[i_,j_,k_]eps3f[l_,m_,n_]=Det@Map[del3@@#&, Partition[Distribute[{{i,j,k},{l,m,n}},List],3],{2}];*)
(*del3[a_,c_]\[Lambda][J_,a_,b_]:=\[Lambda][J,c,b];*)
(*del3[c_,a_]\[Lambda][J_,b_,a_]:=\[Lambda][J,b,c];*)
(*\[Lambda][i_,j_,j_]:=0;*)
(*eps3f[i_,j_,k_]del3[i_,l_]:=eps3f[l,j,k];*)
(*eps3f[i_,j_,k_]del3[j_,l_]:=eps3f[i,l,k];*)
(*eps3f[i_,j_,k_]del3[k_,l_]:=eps3f[i,j,l];*)
(*eps3a[i_,j_,k_]del3[l_,i_]:=eps3a[l,j,k];*)
(*eps3a[i_,j_,k_]del3[l_,j_]:=eps3a[i,l,k];*)
(*eps3a[i_,j_,k_]del3[l_,k_]:=eps3a[i,j,l];*)
(*SetAttributes[dabc,Orderless];*)
(*del8n[a_,d_]fabc[a_,b_,c_]:=fabc[d,b,c]*)
(*del8n[a_,d_]fabc[b_,a_,c_]:=fabc[b,d,c]*)
(*del8n[a_,d_]fabc[c_,b_,a_]:=fabc[c,b,d]*)
(*del8n[a_,d_]dabc[a_,b_,c_]:=dabc[d,b,c]*)
(*del8n[a_,d_]dabc[b_,a_,c_]:=dabc[b,d,c]*)
(*del8n[a_,d_]dabc[c_,b_,a_]:=dabc[c,b,d]*)
(*del8n[a_,c_]del8n[a_,b_]:=del8n[c,b]*)
(*\[Lambda][i_,j_,k_]\[Lambda][l_,k_,m_]:=Module[{},dummyIndexCount++;(I fabc[i,l,dummyIndex[dummyIndexCount]]+dabc[i,l,dummyIndex[dummyIndexCount]])\[Lambda][dummyIndex[dummyIndexCount],j,m]+2/3 del8n[i,l]del3[m,j]]*)
(*Protect[Times];*)


(* ::Input::Initialization:: *)
ConvertToFundamental[model_,groupname_,{0,0}]:=If[CheckGroup[model,groupname]==SU3,1,Message[ConvertToFundamental::name,groupname,{0,0}]]
ConvertToFundamental[model_,groupname_,{1,0}]:=If[CheckGroup[model,groupname]==SU3,1,Message[ConvertToFundamental::name,groupname,{1,0}]]
ConvertToFundamental[model_,groupname_,{0,1}]:=If[CheckGroup[model,groupname]==SU3,eps3f[b[1],bb[1],bb[2]],Message[ConvertToFundamental::name,groupname,{0,1}]]
ConvertToFundamental[model_,groupname_,{1,1}]:=If[CheckGroup[model,groupname]==SU3,
dummyIndexCount++;\[Lambda][B[1],bb[2],dummyIndex[dummyIndexCount]]eps3f[dummyIndex[dummyIndexCount],bb[1],bb[3]],
Message[ConvertToFundamental::name,groupname,{1,1}]]
