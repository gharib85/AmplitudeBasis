(* ::Package:: *)

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


(* ::Input::Initialization:: *)
W2Check[amp_,num_,ch_,j_]:=
reduce[W2[amp,ch],num]==-j(j+1)reduce[amp Mandelstam[ch],num]//Simplify
