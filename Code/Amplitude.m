(* ::Package:: *)

(* ::Text:: *)
(*Building blocks for amplitudes : ab, sb, s*)
(*Young Tableau basis : yngShape, reduce, SSYT*)
(*Enumerate Lorentz classes : LorentzList*)
(*Permute amplitudes by group algebra : YPermute*)


(* ::Input::Initialization:: *)
(* Spinor Brackets: Basic Variables for Amplitudes *)
ab[i_,j_]:=0/;i==j;
ab[i_,j_]:=-ab[j,i]/;j<i;
sb[i_,j_]:=0/;i==j;
sb[i_,j_]:=-sb[j,i]/;j<i;
s[i_,j_]:=ab[i,j]sb[j,i];


(* ::Input::Initialization:: *)
(* Rules for Reduction of Amplitudes into Standard From *)
ruleP1[Num_]:={sb[1,i_]ab[1,j_]:> Table[-sb[k,i]ab[k,j],{k,2,Num}](*~Join~{-esb[i]ab[i,j],sb[j,i]eab[j]}*),
sb[1,i_]^m_ ab[1,j_]:> Table[-sb[1,i]^(m-1)sb[k,i]ab[k,j],{k,2,Num}](*~Join~{-sb[1,i]^(m-1)esb[i]ab[i,j],-sb[1,i]^(m-1)sb[j,i]eab[j]}*),
sb[1,i_]ab[1,j_]^n_:> Table[-ab[1,j]^(n-1)sb[k,i]ab[k,j],{k,2,Num}](*~Join~{-ab[1,j]^(n-1)esb[i]ab[i,j],-ab[1,j]^(n-1)sb[j,i]eab[j]}*),
sb[1,i_]^m_ ab[1,j_]^n_:> Table[-sb[1,i]^(m-1) ab[1,j]^(n-1) sb[k,i]ab[k,j],{k,2,Num}](*~Join~{-sb[1,i]^(m-1) ab[1,j]^(n-1)esb[i]ab[i,j],-sb[1,i]^(m-1) ab[1,j]^(n-1)sb[j,i]eab[j]}*)};
ruleP2[Num_]:={sb[1,2]ab[2,i_/;i>2]:> Table[-sb[1,k]ab[k,i],{k,3,Num}](*~Join~{-esb[1]ab[1,i],-sb[1,i]eab[i]}*),
sb[1,2]^m_ ab[2,i_/;i>2]:> Table[-sb[1,2]^(m-1)sb[1,k]ab[k,i],{k,3,Num}](*~Join~{-sb[1,2]^(m-1)esb[1]ab[1,i],-sb[1,2]^(m-1)sb[1,i]eab[i]}*),
sb[1,2]ab[2,i_/;i>2]^n_:> Table[-ab[2,i]^(n-1)sb[1,k]ab[k,i],{k,3,Num}](*~Join~{-ab[2,i]^(n-1)esb[1]ab[1,i],-ab[2,i]^(n-1)sb[1,i]eab[i]}*),
sb[1,2]^m_ ab[2,i_/;i>2]^n_:> Table[-sb[1,2]^(m-1) ab[2,i]^(n-1) sb[1,k]ab[k,i],{k,3,Num}](*~Join~{-sb[1,2]^(m-1) ab[2,i]^(n-1)esb[1]ab[1,i],-sb[1,2]^(m-1) ab[2,i]^(n-1)sb[1,i]eab[i]}*),
sb[2,i_/;i>2]ab[1,2]:> Table[-sb[k,i]ab[1,k],{k,3,Num}](*~Join~{-esb[i]ab[1,i],-sb[1,i]eab[1]}*),
sb[2,i_/;i>2]^m_ ab[1,2]:> Table[-sb[2,i]^(m-1)sb[k,i]ab[1,k],{k,3,Num}](*~Join~{-sb[2,i]^(m-1)esb[i]ab[1,i],-sb[2,i]^(m-1)sb[1,i]eab[1]}*),
sb[2,i_/;i>2]ab[1,2]^n_:>Table[-ab[1,2]^(n-1)sb[k,i]ab[1,k],{k,3,Num}](*~Join~{-ab[1,2]^(n-1)esb[i]ab[1,i],-ab[1,2]^(n-1)sb[1,i]eab[1]}*),
sb[2,i_/;i>2]^m_ ab[1,2]^n_:> Table[-sb[2,i]^(m-1) ab[1,2]^(n-1) sb[k,i]ab[1,k],{k,3,Num}](*~Join~{-sb[2,i]^(m-1) ab[1,2]^(n-1)esb[i]ab[1,i],-sb[2,i]^(m-1) ab[1,2]^(n-1)sb[1,i]eab[1]}*),
sb[1,3]ab[2,3]:> Table[-sb[1,i]ab[2,i],{i,4,Num}](*~Join~{-esb[1]ab[2,1],-sb[1,2]eab[2]}*),
sb[1,3]^m_ ab[2,3]:> Table[-sb[1,3]^(m-1)sb[1,i]ab[2,i],{i,4,Num}](*~Join~{-sb[1,3]^(m-1)esb[1]ab[2,1],-sb[1,3]^(m-1)sb[1,2]eab[2]}*),
sb[1,3]ab[2,3]^n_:> Table[-ab[2,3]^(n-1)sb[1,i]ab[2,i],{i,4,Num}](*~Join~{-ab[2,3]^(n-1)esb[1]ab[2,1],-ab[2,3]^(n-1)sb[1,2]eab[2]}*),
sb[1,3]^m_ ab[2,3]^n_:> Table[-sb[1,3]^(m-1) ab[2,3]^(n-1) sb[1,i]ab[2,i],{i,4,Num}](*~Join~{-sb[1,3]^(m-1) ab[2,3]^(n-1)esb[1]ab[2,1],-sb[1,3]^(m-1) ab[2,3]^(n-1)sb[1,2]eab[2]}*),
sb[2,3]ab[1,3]:> Table[-sb[2,i]ab[1,i],{i,4,Num}](*~Join~{-esb[2]ab[1,2],-sb[2,1]eab[1]}*),
sb[2,3]^m_ ab[1,3]:> Table[-sb[2,3]^(m-1)sb[2,i]ab[1,i],{i,4,Num}](*~Join~{-sb[2,3]^(m-1)esb[2]ab[1,2],-sb[2,3]^(m-1)sb[2,1]eab[1]}*),
sb[2,3]ab[1,3]^n_:> Table[-ab[1,3]^(n-1)sb[2,i]ab[1,i],{i,4,Num}](*~Join~{-ab[1,3]^(n-1)esb[2]ab[1,2],-ab[1,3]^(n-1)sb[2,1]eab[1]}*),
sb[2,3]^m_ ab[1,3]^n_:> Table[-sb[2,3]^(m-1) ab[1,3]^(n-1) sb[2,i]ab[1,i],{i,4,Num}](*~Join~{-sb[2,3]^(m-1) ab[1,3]^(n-1)esb[2]ab[1,2],-sb[2,3]^(m-1) ab[1,3]^(n-1)sb[2,1]eab[1]}*)
};
ruleP3[Num_]:={sb[2,3]ab[2,3]:> Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}](*~Join~{-2esb[1]eab[1]}~Join~Table[esb[i]eab[i],{i,Num}]*),
sb[2,3]^m_ ab[2,3]:> sb[2,3]^(m-1) Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}](*~Join~{-2sb[2,3]^(m-1)esb[1]eab[1]}~Join~Table[sb[2,3]^(m-1)esb[i]eab[i],{i,Num}]*), 
sb[2,3]ab[2,3]^n_:> ab[2,3]^(n-1) Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}](*~Join~{-2ab[2,3]^(n-1)esb[1]eab[1]}~Join~Table[ab[2,3]^(n-1)esb[i]eab[i],{i,Num}]*),
sb[2,3]^m_ ab[2,3]^n_:>sb[2,3]^(m-1) ab[2,3]^(n-1) Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}](*~Join~{-2sb[2,3]^(m-1) ab[2,3]^(n-1)esb[1]eab[1]}~Join~Table[sb[2,3]^(m-1) ab[2,3]^(n-1)esb[i]eab[i],{i,Num}]*)};
ruleSchA={ab[i_,l_]ab[j_,k_]/;i<j<k<l:>{-ab[i,j]ab[k,l],ab[i,k]ab[j,l]},
ab[i_,l_]^m_ ab[j_,k_]/;i<j<k<l:>ab[i,l]^(m-1) {-ab[i,j]ab[k,l],ab[i,k]ab[j,l]},
ab[i_,l_]ab[j_,k_]^n_/;i<j<k<l:>ab[j,k]^(n-1) {-ab[i,j]ab[k,l],ab[i,k]ab[j,l]},
ab[i_,l_]^m_ ab[j_,k_]^n_/;i<j<k<l:>ab[i,l]^(m-1) ab[j,k]^(n-1) {-ab[i,j]ab[k,l],ab[i,k]ab[j,l]}};
ruleSchS=ruleSchA/.ab->sb;
rule[Num_]:=Join[ruleP1[Num],ruleP2[Num],ruleP3[Num],ruleSchA,ruleSchS];

Clear[reduce];
SetMaxTry[x_]:=maxTry=x;
reduce::overflow="time of reductions exceeds `1`\n 
please use option MaxTry for reduce[] or use SetMaxTry[] to change the limit of time of reduction.";
Options[reduce]={MaxTry->maxTry};
reduce[Amp_,Num_(*,EOMreplace_:{esb->(0&),eab->(0&)}*),OptionsPattern[]]:=(*reduce[Amp,Num(*,EOMreplace*)]=*)
Module[{F=Sum2List@Expand[Amp],F1,iter=1},
While[True,
F1=Sum2List[Plus@@Flatten[F/.rule[Num]]](*/.EOMreplace*); (* replace and combine *)
If[F1===F,Break[],F=F1];
If[iter>=OptionValue[MaxTry],Message[reduce::overflow,OptionValue[MaxTry]];Abort[],iter++]
];
Plus@@F(*/.EOMreplace*)
]
reduce[Num_]:=reduce[#,Num]&


(* ::Input::Initialization:: *)
kmin[state_]:=Module[{hp,hn},
hp=Total@Select[state,Positive];
hn=Total@Select[state,Negative];
Return[Max[{Mod[2hp,2],4Max[state]-2hp,2hn-4Min[state]}]];
]

yngShape::wrongk="wrong number of derivatives/momenta";
yngShape::wrongh="wrong helicity in state `1`";
yngShape::wrongf="wrong fermion number in state `1`";
yngShape[state_,k_]:=Module[{},
If[Nand@@IntegerQ/@(2state),Message[yngShape::wrongh,state]];
If[!IntegerQ[Total[state]],Message[yngShape::wrongf,state]];
If[OddQ[k-kmin[state]]\[Or]k-kmin[state]<0,Message[yngShape::wrongk];Abort[]];
{Total@Select[state,Positive]+k/2,-Total@Select[state,Negative]+k/2}
]

(* initialize young tab A as the input of SSYTfilling *)
(* the amplitude young tab is A\[Transpose], not A *)
YDzero[Num_,nt_,n_]:=Join[ConstantArray[ConstantArray[0,Num-2],nt],ConstantArray[{0,0},n]]
SSYTfilling[A_,filling_,n_:1]:=Module[{f,num,pos,tal,partitions,poslist,list={}},
If[n>Length[filling],Return[{A}]]; (* if all labels are filled in, return the young tableau A *)
{f,num}=filling[[n]]; (* num of f to be filled in *)
pos=DeleteCases[{Range@Length[A],FirstPosition[#,0]&/@A//Flatten}//Transpose,{_,_Missing}]; (* available positions in the Young Diagram *)
If[!OrderedQ@Reverse[pos[[All,2]]],Print[A," is not a standard Young Diagram."];Abort[]]; (* available rows are in descending order *)
tal=Tally[pos[[All,2]]]; (* distribution of pos among rows *)
partitions=Select[Join@@Permutations/@(PadRight[#,Length[tal]]&/@IntegerPartitions[num,Length[tal]]),And@@Thread[#<=tal[[All,2]]]&]; (* ways to partition num of f in different rows *)
poslist=Join@@MapThread[Function[{row,part},Take[Select[pos,#[[2]]==row&],part]],{tal[[All,1]],#}]&/@partitions; (* sublist of positions in pos that we can fill in f *)

Do[
list=Join[list,SSYTfilling[ReplacePart[A,#->f&/@p],filling,n+1]], (* fill in f in various sublist of positions and move forward to the next recursion, join list of results from different branches *)
{p,poslist}];

Return[list] (* send list of results back to the previous recursions *)
]

Clear[SSYT];
Options[SSYT]={OutMode->"amplitude output"};
SSYT[state_,k_,OptionsPattern[]]:=SSYT[state,k]=Module[{nt,n,Num=Length[state],array,ytabs},
{nt,n}=yngShape[state,k];
If[nt==0&&n==0,ytabs={{}},
array=Tally@Flatten@Table[ConstantArray[i,nt-2state[[i]]],{i,Num}];
ytabs=SSYTfilling[YDzero[Num,nt,n],array]];
Switch[OptionValue[OutMode],
"young tab",TransposeTableaux/@ytabs,
"amplitude",amp[#,nt]&/@ytabs,
"amplitude output",Ampform[amp[#,nt]&/@ytabs]]
] (* Output only SSYT for a given number array X *)

(* Generate amplitudes from young tableaux *)
amp::shape="wrong young diagram for amplitudes!";
amp[ytabT_,nt_]:=Module[{trp,iter=0,colb,result=1},
If[ytabT=={},Return[1]];
Do[If[iter<nt,colb=Complement[Range[Length[col]+2],col];result*=Signature@Join[col,colb]sb@@colb,result*=ab@@col];iter++,{col,ytabT}];
Return[result]
]


(* ::Input::Initialization:: *)
GetState[amp_,num_]:=Module[{particle,exp,M,state,k},
exp=amp/.{ab[i_,j_]:>Exp[M-(particle[i]+particle[j])/2],sb[i_,j_]:>Exp[M+(particle[i]+particle[j])/2]};
state=Table[D[exp,particle[i]]/exp//Simplify,{i,num}];
k=D[exp,M]/exp-Total@Abs[state]//Simplify;
{state,k}
]
GetState::multistate="Various scattering states in `1`";
GetState[amplist_List,num_]:=Module[{statelist},
statelist=GetState[num]/@amplist;
If[Length@Tally[statelist]==1,Return[First@statelist],
Message[GetState::multistate,amplist];Abort[]];
]


(* ::Input::Initialization:: *)
(* List All Lorentz Structure at given dimension *)
Options[LorentzList]={Conj->False,HelicityInclude->{0,1/2,1}};
LorentzList[dim_,OptionsPattern[]]:=LorentzList[dim,Conj->OptionValue[Conj],HelicityInclude->OptionValue[HelicityInclude]]=Module[{hlist,n,k,num,Numh,Nh,Nhsol,N0sol,Nhlist={},result},hlist=Sort@DeleteDuplicates@Flatten[{1,-1}\[TensorProduct]OptionValue[HelicityInclude]];
Numh=Map[Subscript[num,#]&,hlist];
Do[n=dim-Num-nt;
For[k=0,k<=2 nt,k++,
Nhsol=Flatten[Outer[Join,##,1]&@@MapThread[Solve[Total[2Abs[#[[2]]]#&/@#1]==2#2-k,#1,NonNegativeIntegers]&,{GroupBy[Numh,Sign[#[[2]]]&]/@{-1,1},{n,nt}}],1];
Do[Nh=Numh/.sol;If[MemberQ[hlist,0],
N0sol=Solve[Total[Numh]==Num/.sol,Subscript[num, 0],NonNegativeIntegers];
If[Length[N0sol]==1&&kmin[Join@@MapThread[ConstantArray,{hlist,Nh/.N0sol[[1]]}]]<=k,AppendTo[Nhlist,{Nh/.N0sol[[1]],k}]],
If[Total[Numh]==Num/.sol,AppendTo[Nhlist,{Numh/.sol,k}]]
],{sol,Nhsol}];

If[n+nt+3==dim,Break[]]
],{Num,3,dim},{nt,0,Floor[(dim-Num)/2]}];

If[OptionValue[Conj],result=Nhlist\[Union](MapAt[Reverse,#1,1]&)/@Nhlist,
result=DeleteDuplicates[Nhlist,#1==MapAt[Reverse,#2,1]&]];
MapAt[Join@@MapThread[ConstantArray,{hlist,#1}]&,result,{All,1}]
]


(* ::Input::Initialization:: *)
(* symmetrize particles in amplitude *)
Options[YPermute]={AmpReduce->True};
YPermute[amp_,permutation_,num_,OptionsPattern[]]:=Module[{plist=Sum2List@Expand@permutation,Flist,A,outlist,permA,result=0},
plist=FactorSplit[#,MatchQ[_Cycles]]&/@plist; (* <|False\[Rule]coeff, True\[Rule]Cycles|> *)
plist=MapAt[IndexInvPermute[#,Range[num]]&,plist,{All,Key[True]}];
Do[result+=p[False]*amp/.{
ab[i_,j_]:>ab[p[True][i],p[True][j]],
sb[i_,j_]:>sb[p[True][i],p[True][j]]},
{p,plist}];
If[OptionValue[AmpReduce],result=reduce[result,num]];
Return[result];
]
YPermute[mlist_List,permutation_,num_]:=YPermute[#,permutation,num]&/@mlist

(*LorentzPermGenerator[ybasis_,Num_]:=Module[{state,hels,k,ini,gen1,gen2,result=<||>},
{state,k}=GetState@@ybasis;
ini=Accumulate[Prepend[Tally[state][[;;-2,2]],0]]+1;
hels=DeleteCases[MapThread[Append,{Tally[state],ini}],{_,1,_}];
gen1=Cycles[{{#,#+1}}]&/@hels[[All,3]];
gen2=Cycles[{Range[#2,#2+#1-1]}]&@@@hels[[All,{2,3}]];

Do[AssociateTo[result,hels[[i,1]]->Table[FindCor[ybasis]/@YPermute[ybasis,gen,Num],{gen,{gen1[[i]],gen2[[i]]}}]],{i,Length[hels]}];
Return[result]
]*)

LorentzPermGenerator[state_,k_]:=Module[{ybasis,Num=Length[state],hels=Tally[state],ini,gen1,gen2,result=<||>},
ybasis=SSYT[state,k,OutMode->"amplitude"];Sow[ybasis];
ini=Accumulate[Prepend[hels[[;;-2,2]],0]]+1;
hels=DeleteCases[MapThread[Append,{hels,ini}],{_,1,_}];
gen1=Cycles[{{#,#+1}}]&/@hels[[All,3]];
gen2=Cycles[{Range[#2,#2+#1-1]}]&@@@hels[[All,{2,3}]];

Do[AssociateTo[result,hels[[i,1]]->Table[FindCor[ybasis]/@YPermute[ybasis,gen,Num],{gen,{gen1[[i]],gen2[[i]]}}]],{i,Length[hels]}];
Return[result]
]



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
{amp=Expand[Amp],list,ablist={},sblist={},prefactor=1,sf,sg,sfg},
(* find bridges *)
If[Head[amp]===Plus,Return[W2[amp,Ind]],
list=Prod2List[amp]];
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
W2Check[amp_,num_,ch_,j_]:=
reduce[W2[amp,ch],num]==-j(j+1) reduce[amp Mandelstam[ch],num]//Simplify//TrueQ


(* ::Input::Initialization:: *)
Options[W2Diagonalize]={OutputFormat->"print",CheckJ->False};
W2Diagonalize[state_,k_,Ind_,OptionsPattern[]]:=
Module[{Num=Length[state],iniBasis=SSYT[state,k,OutMode->"amplitude"],stBasis=SSYT[state,k+2,OutMode->"amplitude"],
W2Basis,W2result,Wrep,rlist,rstr,eigensys,result},Off[LinearSolve::sqmat1];
W2Basis=FindCor[stBasis]/@(reduce[Num]/@(Mandelstam[Ind]iniBasis));
W2result=FindCor[stBasis]/@(reduce[Num]/@(W2[Ind]/@iniBasis));

{Wrep,rlist}=Reap[MapIntersection[W2result,W2Basis],restriction];
If[Wrep=={{}},result=<|"basis"->iniBasis,"j"->{},"transfer"->{},"j-basis"->{}|>,
rstr=Dot@@Reverse[rlist[[1]]];
eigensys=Eigensystem[Wrep\[Transpose]];
result=<|"basis"->iniBasis,"j"->Function[x,(Sqrt[1-4x]-1)/2]/@eigensys[[1]],"transfer"->eigensys[[2]].rstr,"j-basis"->eigensys[[2]].rstr.iniBasis|>
];
If[OptionValue[CheckJ],Print["check eigen equation ..."];
If[And@@MapThread[W2Check[#1,Length[state],Ind,#2]&,result/@{"j-basis","j"}],Print["eigen values verified!"],
Print["eigen system error!"];Abort[]]
];

Switch[OptionValue[OutputFormat],
"working",result,
"print",result=MapAt[Map[Ampform],result,Key["j-basis"]];
result=MapAt[MatrixForm,result,Key["transfer"]]
]
]

(*Jbasis[state_,k_,partition_]:=Module[{jEigen={},jbasisAll,jcomb},
jbasisAll=W2Diagonalize[state,k,#,OutputFormat->"working"]&/@partition;
Do[AppendTo[jEigen,Map[Part[jB["transfer"],#]&,PositionIndex[jB["j"]],{2}]],{jB,jbasisAll}];
jcomb=Distribute[Keys/@jEigen,List];
DeleteCases[AssociationMap[LinearIntersection@@MapThread[#1[#2]&,{jEigen,#}]&,jcomb],{}]
]*)

LorentzJBasis[state_,k_,partition_]:=Module[{jEigen={},jbasisAll,jcomb,result=<|"basis"->SSYT[state,k,OutMode->"amplitude"]|>},
jbasisAll=W2Diagonalize[state,k,#,OutputFormat->"working"]&/@partition;
Do[AppendTo[jEigen,Map[Part[jB["transfer"],#]&,PositionIndex[jB["j"]],{2}]],{jB,jbasisAll}];
jcomb=AssociationThread[partition->#]&/@Distribute[Keys/@jEigen,List];
Append[result,"jcoord"->Normal@DeleteCases[AssociationMap[LinearIntersection@@MapThread[#1[#2]&,{jEigen,Values[#]}]&,jcomb],{}]]
]


(* ::Input::Initialization:: *)
(* to be added: normalization of pwbasis *)
PWExpand[amp:Except[_List],num_,ch_]:=Module[{state,k,PW,coord},
{state,k}=GetState[amp,num];
PW=W2Diagonalize[state,k,ch,OutputFormat->"working"];
coord=FindCor[reduce[amp,num],PW["basis"]];
Append[KeyDrop[PW,{"transfer","basis"}],"coeff"->LinearSolve[PW["transfer"]\[Transpose],coord]]
]
PWExpand[amp_List,num_,ch_]:=Module[{state,k,PW,coordlist},
{state,k}=If[Length[#]>1,Print["amp list with different {state,k}"];Abort[],#[[1,1]]]&@Tally[GetState[#,num]&/@amp];
PW=W2Diagonalize[state,k,ch,OutputFormat->"working"];
coordlist=FindCor[reduce[#,num],PW["basis"]]&/@amp;
Append[KeyDrop[PW,{"transfer","basis"}],"coeff"->coordlist.LinSolve[PW["transfer"]]]
]
PWExpand[amp_,num_,ch_,denom_,jmax_]:=Module[{state,kini,k,jini,extraMand,pw,pw2,coref},
state=First@GetState[amp/denom,num];
kini=Last@GetState[amp,num];
jini=Max[W2Diagonalize[state,k=kmin[state],ch,OutputFormat->"working"]["j"]];
extraMand=Max[0,Floor[jmax-jini]];
pw=W2Diagonalize[state,k+2extraMand,ch,OutputFormat->"working"];
pw2=PWExpand[denom pw["j-basis"],num,ch];
coref=PWExpand[amp Power[Mandelstam[ch],(Last@GetState[pw2["j-basis"][[1]],num]-kini)/2],num,ch]["coeff"];Print[pw2["coeff"]];
Append[KeyDrop[pw,{"transfer","basis"}],"coeff"->LinearSolve[pw2["coeff"][[All,-Length[pw["j"]];;]]\[Transpose],coref[[-Length[pw["j"]];;]]]]
]
