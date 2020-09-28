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
ruleP1[Num_]:={sb[1,i_]ab[1,j_]:> Table[-sb[k,i]ab[k,j],{k,2,Num}],
sb[1,i_]^m_ ab[1,j_]:> Table[-sb[1,i]^(m-1)sb[k,i]ab[k,j],{k,2,Num}],
sb[1,i_]ab[1,j_]^n_:> Table[-ab[1,j]^(n-1)sb[k,i]ab[k,j],{k,2,Num}],
sb[1,i_]^m_ ab[1,j_]^n_:> Table[-sb[1,i]^(m-1) ab[1,j]^(n-1) sb[k,i]ab[k,j],{k,2,Num}]};
ruleP2[Num_]:={sb[1,2]ab[2,i_/;i>2]:> Table[-sb[1,k]ab[k,i],{k,3,Num}],
sb[1,2]^m_ ab[2,i_/;i>2]:> Table[-sb[1,2]^(m-1)sb[1,k]ab[k,i],{k,3,Num}],
sb[1,2]ab[2,i_/;i>2]^n_:> Table[-ab[2,i]^(n-1)sb[1,k]ab[k,i],{k,3,Num}],
sb[1,2]^m_ ab[2,i_/;i>2]^n_:> Table[-sb[1,2]^(m-1) ab[2,i]^(n-1) sb[1,k]ab[k,i],{k,3,Num}],
sb[2,i_/;i>2]ab[1,2]:> Table[-sb[k,i]ab[1,k],{k,3,Num}],
sb[2,i_/;i>2]^m_ ab[1,2]:> Table[-sb[2,i]^(m-1)sb[k,i]ab[1,k],{k,3,Num}],
sb[2,i_/;i>2]ab[1,2]^n_:>Table[-ab[1,2]^(n-1)sb[k,i]ab[1,k],{k,3,Num}],
sb[2,i_/;i>2]^m_ ab[1,2]^n_:> Table[-sb[2,i]^(m-1) ab[1,2]^(n-1) sb[k,i]ab[1,k],{k,3,Num}],sb[1,3]ab[2,3]:> Table[-sb[1,i]ab[2,i],{i,4,Num}],
sb[1,3]^m_ ab[2,3]:> Table[-sb[1,3]^(m-1)sb[1,i]ab[2,i],{i,4,Num}],
sb[1,3]ab[2,3]^n_:> Table[-ab[2,3]^(n-1)sb[1,i]ab[2,i],{i,4,Num}],
sb[1,3]^m_ ab[2,3]^n_:> Table[-sb[1,3]^(m-1) ab[2,3]^(n-1) sb[1,i]ab[2,i],{i,4,Num}],
sb[2,3]ab[1,3]:> Table[-sb[2,i]ab[1,i],{i,4,Num}],
sb[2,3]^m_ ab[1,3]:> Table[-sb[2,3]^(m-1)sb[2,i]ab[1,i],{i,4,Num}],
sb[2,3]ab[1,3]^n_:> Table[-ab[1,3]^(n-1)sb[2,i]ab[1,i],{i,4,Num}],
sb[2,3]^m_ ab[1,3]^n_:> Table[-sb[2,3]^(m-1) ab[1,3]^(n-1) sb[2,i]ab[1,i],{i,4,Num}]
};
ruleP3[Num_]:={sb[2,3]ab[2,3]:> Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}],
sb[2,3]^m_ ab[2,3]:> sb[2,3]^(m-1) Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}],
sb[2,3]ab[2,3]^n_:> ab[2,3]^(n-1) Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}],
sb[2,3]^m_ ab[2,3]^n_:>sb[2,3]^(m-1) ab[2,3]^(n-1) Table[s[i,j],{i,2,Num},{j,Max[i+1,4],Num}]};
ruleSchA={ab[i_,l_]ab[j_,k_]/;i<j<k<l:>{-ab[i,j]ab[k,l],ab[i,k]ab[j,l]},
ab[i_,l_]^m_ ab[j_,k_]/;i<j<k<l:>ab[i,l]^(m-1) {-ab[i,j]ab[k,l],ab[i,k]ab[j,l]},
ab[i_,l_]ab[j_,k_]^n_/;i<j<k<l:>ab[j,k]^(n-1) {-ab[i,j]ab[k,l],ab[i,k]ab[j,l]},
ab[i_,l_]^m_ ab[j_,k_]^n_/;i<j<k<l:>ab[i,l]^(m-1) ab[j,k]^(n-1) {-ab[i,j]ab[k,l],ab[i,k]ab[j,l]}};
ruleSchS=ruleSchA/.ab->sb;
rule[Num_]:=Join[ruleP1[Num],ruleP2[Num],ruleP3[Num],ruleSchA,ruleSchS];

SetMaxTry[x_]:=Block[{},maxTry=x;]
reduce::overflow="time of reductions exceeds `1`\n 
please use option MaxTry for reduce[] or use SetMaxTry[] to change the limit of time of reduction.";
Options[reduce]={MaxTry->maxTry};
reduce[Amp_,Num_,OptionsPattern[]]:=reduce[Amp,Num]=
Module[{F=Sum2List@Expand[Amp],F1,iter=1},
While[True,
F1=Sum2List[Plus@@Flatten[F/.rule[Num]]]; (* replace and combine *)
If[F1===F,Break[],F=F1];
If[iter>=OptionValue[MaxTry],Message[reduce::overflow,OptionValue[MaxTry]];Abort[],iter++]
];
Plus@@F
]
reduce[Num_]:=reduce[#,Num]&


(* ::Input::Initialization:: *)
kmin[input_,mode_:"hlist"]:=Module[{state,hp,hn},
Switch[mode,
"hlist",state=input,
"Nh",state=Join@@MapThread[ConstantArray,{{-1,-1/2,0,1/2,1},input}]
];
hp=Total@Select[state,Positive];
hn=Total@Select[state,Negative];
Return[Max[{Mod[2hp,2],4Max[state]-2hp,2hn-4Min[state]}]];
]

yngShape::wrongk="wrong number of derivatives/momenta";
yngShape::wrongh="wrong helicity in state `1`";
yngShape::wrongf="wrong fermion number in state `1`";
yngShape[state_,k_]:=Module[{},
If[!SubsetQ[{1,1/2,0,-1/2,-1},DeleteDuplicates[state]],Message[yngShape::wrongh,state]];
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
(* List All Lorentz Structure at given dimension *)
LorentzList[dim_,mode_:"complex"]:=Module[{n,k,Nh,Nhlist={},result},
Do[n=dim-N-nt;
For[k=0,k<=2 nt,k++,
Do[Nh={i,2 n-k-2 i,3N+2k-2dim+i+j,2 nt-k-2 j,j};If[Nh[[3]]<0||kmin[Nh,"Nh"]>k,Continue[],AppendTo[Nhlist,{Nh,k}]],{i,0,Floor[n-k/2]},{j,0,Floor[nt-k/2]}];
If[n+nt+3==dim,Break[]]
],{N,3,dim},{nt,0,Floor[(dim-N)/2]}];
Switch[mode,
"complex",result=DeleteDuplicates[Nhlist,#1==MapAt[Reverse,#2,1]&],
"real",result=Nhlist\[Union](MapAt[Reverse,#1,1]&)/@Nhlist];
MapAt[Join@@MapThread[ConstantArray,{{-1,-(1/2),0,1/2,1},#1}]&,result,{All,1}]
]


(* ::Input::Initialization:: *)
(* symmetrize particles in amplitude *)
YPermute[amp_,permutation_,num_]:=Module[{plist=Sum2List@Expand@permutation,Flist,A,outlist,permA,result=0},
plist=FactorSplit[#,MatchQ[_Cycles]]&/@plist;
plist=MapAt[AssociationThread[Permute[Range[num],#]->Range[num]]&,plist,{All,Key[True]}];
Do[result+=p[False]*reduce[amp/.
{ab[i_,j_]:>ab[p[True][i],p[True][j]],sb[i_,j_]:>sb[p[True][i],p[True][j]]},num],
{p,plist}];
Return[result];
]
YPermute[mlist_List,permutation_,num_]:=YPermute[#,permutation,num]&/@mlist
