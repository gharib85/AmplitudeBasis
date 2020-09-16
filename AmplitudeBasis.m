(* ::Package:: *)

(* ::Input::Initialization:: *)
$AmplitudeBasisDir = FileNameDrop[$InputFileName,-1];
BeginPackage["AmplitudeBasis`"]
$GroupMathPackages={FileNameJoin[{Global`$AmplitudeBasisDir,"GroupMath","GenericTools.m"}],FileNameJoin[{Global`$AmplitudeBasisDir,"GroupMath","LieAlgebras.m"}],FileNameJoin[{Global`$AmplitudeBasisDir,"GroupMath","PermutationGroup.m"}]}

(* Useful Lie groups in GroupMath *)
{U1,SU2,SU3,SU4,SU5,SU6};

(* Useful Functions in GroupMath *)
{DimR,Adjoint,SnIrrepDim,GenerateStandardTableaux, DecomposeSnProduct, PlethysmsN,ReduceRepProductBase1,ReduceRepProductBase2,HookContentFormula};

Begin["`Private`"]
Get/@$GroupMathPackages;
End[];


(* ::Subsection:: *)
(*Configure*)


(* ::Input::Initialization:: *)
permutationBasis="left"; (* or "right" *)
reduceTry=20;


(* ::Subsection:: *)
(*General Tools*)


(* ::Subsubsection::Closed:: *)
(*Linear Algebra*)


(* ::Input::Initialization:: *)
Sum2List[x_Plus]:=List@@x
Sum2List[x:Except[Plus]]:=List@x
Prod2List[x_]:=Flatten[{x}/.{Power->ConstantArray,Times->List}]

(* Separate numerical factors and symbolic factors of a monomial expression *)
normalize[monoAmp_]:=Module[{F,result},
F=Switch[monoAmp,_Times,List@@monoAmp,_,{monoAmp}];
result=Times@@@GatherBy[F,NumericQ];
If[Length[result]==1,PrependTo[result,1]];
If[MatchQ[result[[1]],_Complex],Return[{-I,I} result],Return[result]];
]

(* Find the coefficient list of an expression (e.g. an amplitude) in STANDARD FORM. *)
FindCor::basis="non-standard expression `2` or incomplete basis `1`";
FindCor[Amp_,StBasis_]:=Module[{F=Expand[Amp],B=normalize/@StBasis,cor},
(* Amp: the expression (may not be an amplitude,
StBasis: the standard basis (monomials). *)
cor=ConstantArray[0,Length[StBasis]];
If[F==0,Return[cor]];
F=normalize/@Sum2List[F];
Do[If[MemberQ[B[[All,2]],F[[i,2]]],
cor=ReplacePart[cor,Position[B[[All,2]],F[[i,2]]]->F[[i,1]]],
Message[FindCor::basis,Amp,StBasis];Abort[]
],{i,Length[F]}];
cor/B[[All,1]]
]
FindCor[StBasis_]:=FindCor[#,StBasis]&

unflatten[e_,{d__?(IntegerQ[#1]&&Positive[#1]&)}]:=Fold[Partition,e,Take[{d},{-1,2,-1}]]/;Length[e]===Times[d]

(* Select a complete basis from a list of vectors *)
basisReduce[subspace_,mode_:"basis"]:=Module[{subbasis,len=Length[subspace],lmax,iter=1,pos=1,poslist={}},
If[len>0,lmax=Length[subspace[[1]]],Return[{}]];
If[!MatrixQ[subspace,NumericQ],Message[basisReduce::input,subspace],subbasis=subspace];
While[iter<=len&&iter<=lmax,
Switch[MatrixRank[subbasis[[;;iter]]],
iter,iter++;AppendTo[poslist,pos],
iter-1,subbasis=Delete[subbasis,iter];len--
];
pos++];
<|"basis"->Return[If[lmax<len,subbasis[[;;lmax]],subbasis]],"pos"-> poslist|>
]
basisReduce::input="wrong input matrix: `1`";


(* ::Input::Initialization:: *)
(* Special Definitions *)
tAssumptions={};
tReduce:=TensorReduce[#,Assumptions->tAssumptions]&;
tRank:=TensorRank[#,Assumptions->tAssumptions]&;
tDimensions:=TensorDimensions[#,Assumptions->tAssumptions]&;
tSymmetry=TensorSymmetry[#,Assumptions->tAssumptions]&;


(* ::Input::Initialization:: *)
(* representation matrix for su(n) generators *)
GellMann[n_]:=GellMann[n]=
Flatten[Table[(*Symmetric case*)SparseArray[{{j,k}->1,{k,j}->1},{n,n}],{k,2,n},{j,1,k-1}],1]~Join~Flatten[Table[(*Antisymmetric case*)SparseArray[{{j,k}->-I,{k,j}->+I},{n,n}],{k,2,n},{j,1,k-1}],1]~Join~Table[(*Diagonal case*)Sqrt[2/l/(l+1)] SparseArray[Table[{j,j}->1,{j,1,l}]~Join~{{l+1,l+1}->-l},{n,n}],{l,1,n-1}];


(* ::Subsubsection::Closed:: *)
(*Permutation Group*)


(* ::Item:: *)
(*Macro Parameter -- permutationBasis*)


(* ::Item:: *)
(*GroupMath -- DimR, SnIrrepDim,GenerateStandardTableaux, DecomposeSnProduct, PlethysmsN, ReduceRepProductBase1, ReduceRepProductBase2*)


(* ::Input::Initialization:: *)
(* product in group algebra *)
pp2[a_,b_]:=Module[{}, 
Switch[Head[a],
Plus,pp2[#,b]&/@a,
Times,Sum[MapAt[pp2[#,b]&,a,i],{i,Length[a]}],
Cycles,Switch[Head[b],
Plus,pp2[a,#]&/@b,
Times,Sum[MapAt[pp2[a,#]&,b,i],{i,Length[b]}],
Cycles,PermutationProduct[b,a],
_,0
],
_,0
]
](* 2-element *)
pp[permlist_]:=If[Length[permlist]>1,pp2[First[permlist],pp[Rest[permlist]]],First[permlist]]


(* ::Input::Initialization:: *)
(*********************** irreducible ideal of group algebra *******************)

(*Given a tableau Generate List vertical cycle groups and horizontal cycle groups*)
GenerateCycleGauge[Tableau_]:=Module[{len=Length[Tableau],len1=Length[Tableau[[1]]],tTabvertical},tTabvertical=Cases[#,_Integer]&/@Transpose[Join[#,Table["x",{i,1,len1-Length[#]}]]&/@Tableau];{Tableau,tTabvertical}]

(*Generate the list of permutations from the given array*)
GenerateCyclesFromList[l_]:=#/.Cycles[x__]:>Cycles[Map[l[[#1]]&,x,{2}]]&/@(GroupElements[SymmetricGroup[Length[l]]])

(*function to calculate the parity of the Cycle*)
permutationSignature[perm_?PermutationCyclesQ]:=Apply[Times,(-1)^(Length/@First[perm]-1)];

(*Generate irreducible Young Symmetrizer with given Tableau*)
GenerateYoungSymmetrizer[Tableau_]:=Module[{cyclegroups=GenerateCycleGauge[Tableau],vgroup,hgroup,h,v},
hgroup=GenerateCyclesFromList/@cyclegroups[[1]];
vgroup=GenerateCyclesFromList/@cyclegroups[[2]];
vgroup=vgroup*Map[permutationSignature[#]&,(vgroup),{2}];
v=pp[Total/@vgroup];
h =pp[Total/@hgroup];
pp[{h,v}]
]
(*generate a table with different Cycles and corresponding coefficients for a given ordinary polynomial with cycles*)
ColistPP[p_]:=Module[{cycleslist,Colist},
cycleslist=Cases[Variables[p],Cycles[_]];
If[Length[cycleslist]==0,Return[Null]];
Colist =(CoefficientList[p,#]&/@cycleslist)[[1;;-1,2]];
Join[Transpose[{cycleslist}],Transpose[{Colist}],2]
]
(*Functions related to find P,Q of a permutation in a Young Tableaux*)
FindPQ[plist_,qlist_,perm_]:=Module[{ptemp,qtemp,npl=Length[plist],nql=Length[qlist]},Do[If[PermutationProduct[qlist[[j]],plist[[i]]]==perm,ptemp=plist[[i]];qtemp=qlist[[j]];Break[]],{i,1,npl},{j,1,nql}];{ptemp,qtemp}];
R[ST_,x_,y_]:= FindPermutation[Flatten[ST[[x]]],Flatten[ST[[y]]]];
DistPP[x_]:=If[Length[x]>1,(PermutationProduct@@Reverse[{#}]&)@@@Distribute[x,List],x];
GetPQFromPerm[t_,perm_]:=Module[{cg,pl,ql,pql},cg=GenerateCycleGauge[t];
pl=DeleteDuplicates[Flatten[DistPP/@Subsets[GenerateCyclesFromList/@cg[[1]]]]];
ql=DeleteDuplicates[Flatten[DistPP/@Subsets[GenerateCyclesFromList/@cg[[2]]]]];
FindPQ[pl,ql,perm]
]
NormalizeQ[t1_,t2_]:=Module[{nrow=Length[t2],plist,Q=False},
Do[plist=(Position[t1,#]&/@t2[[i]])[[1;;-1,1,2]];If[(SortBy[Tally[plist],Last])[[-1,2]]>1,Q=True;Break[]],{i,1,nrow}];Q
]


(* ::Input::Initialization:: *)
(* basis Subscript[b, \[Mu]\[Nu]] for Sn irrep space *)
Generateb[part_]:=Module[{Pnumu,Qnumu,Rnumu,ymu,e,b,ndim=SnIrrepDim[part],n=Total[part],ng=Total[part]!,ST,YSlist,PQtemp,e1coeff,gP,gW},
ST=GenerateStandardTableaux[part];
YSlist=(GenerateYoungSymmetrizer/@ST);
Do[Rnumu[i,j]=R[ST,i,j];If[NormalizeQ[ST[[i]],ST[[j]]],Pnumu[i,j]=0;Qnumu[i,j]=0,PQtemp=GetPQFromPerm[ST[[j]],R[ST,i,j]];Pnumu[i,j]=PQtemp[[1]];Qnumu[i,j]=PQtemp[[2]];],{i,1,ndim},{j,1,ndim}];
ymu[ndim]=Cycles[{}];
Do[ymu[ndim-k]=(Cycles[{}]-Sum[pp[{Pnumu[ndim-k,l],ymu[l]}],{l,ndim-k+1,ndim}]),{k,1,ndim-1}];
Do[e[mu]=ndim/ng (pp[{(GenerateYoungSymmetrizer[ST[[mu]]]),ymu[mu]}]),{mu,1,ndim}];
Switch[permutationBasis,
"left",Return[pp[{R[ST,#,1],e[1]}]&/@Range[1,ndim]],
"right",Return[pp[{R[ST,1,#],e[#]}]&/@Range[1,ndim]]]
]
YO[yng_,pos_:1,otherbasis_:1]:=Generateb[yng][[otherbasis]]/.Cycles[x_]:>Cycles[x+pos-1]


(* ::Input::Initialization:: *)
(************* inner product (needs data folder SnMat) *******************)

ReadMatrices[matmap_,n_,dir_]:=Module[{nintpart=Length[IntegerPartitions[n]],ge,mat},ge=ToExpression/@Import[dir<>"/s"<>ToString[n]<>"/s"<>ToString[n],"List"];Do[mat=ToExpression/@Import[dir<>"/s"<>ToString[n]<>"/s"<>ToString[n]<>"_"<>ToString[i]<>".dat","List"];MapThread[Set,{matmap[i][#]&/@ge,mat}];,{i,1,nintpart}]]
PR[matmap_,ge_,\[Sigma]_,k_,l_,snreplist_,symbollist_,indiceslist_]:=Module[{nG=Length[ge],n\[Sigma],nlist},nlist=Length[(matmap[#][Cycles[{}]])[[1]]]&/@snreplist;
n\[Sigma]=Length[(matmap[\[Sigma]][Cycles[{}]])[[1]]];
n\[Sigma]/nG Sum[
Inverse[(matmap[\[Sigma]][ge[[g]]])][[k,l]] Times@@(Sum[#2[i]((matmap[#1][ge[[g]]])[[i,#3]]),{i,1,#4}]&@@@Transpose[{snreplist,symbollist,indiceslist,nlist}])
,{g,1,nG}]
]

GetCGCM[replist_,matmap_:0]:=Module[{n=Total@First@replist,mat,result={},intpart,listreppos,listrep,listirrepdim,multiplicity,listdim,symbollist,indiceslist,listbasis,irrepbasis,multicount,rank,cglist,cglistn,ranktemp},
If[matmap===0,ReadMatrices[mat,n,NotebookDirectory[]<>"SnMat"],mat=matmap];
intpart=IntegerPartitions[n]; (* list of Sn irrep *)
listreppos=Position[intpart,#][[1,1]]&/@replist;
listdim = SnIrrepDim/@replist;
listirrepdim= SnIrrepDim/@intpart;
listrep=DecomposeSnProduct[replist]; (* {n_1,n_2,...}, n_i being multiplicity of irrep intpart\[LeftDoubleBracket]i\[RightDoubleBracket] *)
symbollist=u/@Range[1,Length[replist]];
indiceslist=Distribute[Range[1,#]&/@listdim,List];
listbasis=Times@@Flatten[MapThread[Map,{symbollist,#}]]&/@(Partition[#,1]&/@indiceslist);

Do[multiplicity=listrep[[i]];
If[multiplicity== 0,Continue[]];
multicount=0;
rank=0;
cglistn={};
Do[irrepbasis=PR[mat,GroupElements[SymmetricGroup[n]],i,1,#,listreppos,symbollist,j]&/@Range[1,listirrepdim[[i]]]; (* key step, result in terms of abstract basis u[x][y] *)
If[!(IntegerQ[irrepbasis[[1]]]),
cglist=Table[Coefficient[irrepbasis[[mb]],#]&/@listbasis,{mb,1,listirrepdim[[i]]}]; (* take away u-basis *)
ranktemp=MatrixRank[Join[cglistn,cglist]];
If[ranktemp>rank,cglistn=Join[cglistn,cglist];multicount++;rank=ranktemp]; (* find new independent rep space *)
If[multicount==multiplicity,AppendTo[result,intpart[[i]]->Partition[cglistn,listirrepdim[[i]]]];Break[]] (* find enough spaces *)
],
{j,indiceslist}],
{i,1,Length[listirrepdim]}
];
Map[Fold[Partition,#,Reverse[Rest[listdim]]]&,result,{4}]
]


(* ::Input::Initialization:: *)
(********************** Young tableau related *******************)
(* Fill number array X into tableaux p *)
YngFilling[X_,p_]:=Module[{ac},
ac=Prepend[Accumulate[p],0];
Table[Take[X,{ac[[i]]+1,ac[[i+1]]}],{i,Length[p]}]
]

TransposeTableau[yt_]:=DeleteCases[#,"x"]&/@Transpose[PadRight[#,Length[yt[[1]]],"x"]&/@yt]
TransposeYng[yng_]:=Length/@TransposeTableau[Range/@yng]

Dynk2Yng[rep_]:=Reverse@Accumulate@Reverse[rep]
Yng2Dynk[group_,yng_]:=-Differences@PadRight[yng,Length[group]+1]


(* ::Input::Initialization:: *)
(* Modification of the GroupMath MyRepProduct *)
MyRepProduct[cm_,repsList_,select_:Identity]:=MyRepProduct[cm,repsList,select]=Module[{n,orderedList,result},
If[cm==U1,Return[{{Plus@@repsList,1}}]];If[Length[repsList]==1,Return[{{repsList[[1]],1}}]];orderedList=Sort[repsList,DimR[cm,#1]<DimR[cm,#2]&];n=Length[orderedList];result=ReduceRepProductBase2[cm,orderedList[[n-1]],orderedList[[n]]];Do[result=ReduceRepProductBase1[cm,orderedList[[n-i]],select@result];,{i,2,n-1}];Return[result];]

FindIrrepCombination[group_,IPlist_,rep_]:=FindIrrepCombination[group,IPlist,rep]=
(*IPlist is a list of {__,__}, where the first slot is the Dykin coefficient of the corresponding representation, the second slot is the number of this representation*)
Module[{nbox,yng=Dynk2Yng[rep],select,PlethysmsNlist,IrrepListAmongNIP,IrrepListFromReduce,SingletPositionList,SUNirrep,SNirrep,NumSUN},
nbox=Total@Flatten[Dynk2Yng/@Join@@ConstantArray@@@IPlist];
select=Select[And@@Thread[Dynk2Yng[#[[1]]]<=yng+(nbox-Total@yng)/(1+Length[group])]&];
PlethysmsNlist=select/@(PlethysmsN[group,##]&@@@IPlist);
IrrepListAmongNIP=Distribute[DeleteDuplicates/@PlethysmsNlist[[1;;-1,1;;-1,1]],List];
IrrepListFromReduce=MyRepProduct[group,#,select]&/@IrrepListAmongNIP;
SingletPositionList=Position[IrrepListFromReduce,{rep,_}][[1;;-1,1]];
NumSUN=Cases[#,{rep,temp_}:>temp]&/@(IrrepListFromReduce[[#]]&/@SingletPositionList);
SUNirrep=IrrepListAmongNIP[[#]]&/@SingletPositionList;
SNirrep=Table[Cases[PlethysmsNlist[[i]],{IrrepListAmongNIP[[#]][[i]],x_,y_}:>{x,y}],{i,1,Length[IPlist]}]&/@SingletPositionList;
{SUNirrep,SNirrep,Flatten[NumSUN]}
]


(* ::Subsubsection::Closed:: *)
(*Amplitude*)


(* ::Item:: *)
(*Macro Parameter -- reduceTry*)


(* ::Input::Initialization:: *)
(* permute arguments of function A *)
Pm[A_,Y_Cycles,head__]:=Permute[A,InversePermutation@Y]/;MemberQ[{head},Head[A]]
Pm[A_Plus,Y_,head__]:=Pm[#,Y,head]&/@A
Pm[A_Times,Y_,head__]:=Times@@MapAt[Pm[#,Y,head]&,normalize[A],2]
Pm[A_Power,Y_,head__]:=MapAt[Pm[#,Y,head]&,A,1]
Pm[A_,Y_Times,head__]:=Times@@MapAt[Pm[A,#,head]&,normalize[Y],2]
Pm[A_,Y_Plus,head__]:=Pm[A,#,head]&/@Y


(* ::Input::Initialization:: *)
ClearAll[kmin,yngShape,YDzero,SSYTfilling,SSYT, LorentzList];
(* Generating Independent Amplitude Basis using Harmonic Function Method *)
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

Options[SSYT]={OutMode->"amplitude"};
SSYT[state_,k_,OptionsPattern[]]:=SSYT[state,k]=Module[{nt,n,Num=Length[state],array,ytabs},
{nt,n}=yngShape[state,k];
If[nt==0&&n==0,Return[{1}]];
array=Tally@Flatten@Table[ConstantArray[i,nt-2state[[i]]],{i,Num}];
ytabs=TransposeTableau/@SSYTfilling[YDzero[Num,nt,n],array];
Switch[OptionValue[OutMode],
"young tab",ytabs,
"amplitude",amp[#,nt]&/@ytabs]
] (* Output only SSYT for a given number array X *)

(* Spinor Brackets: Basic Variables for Amplitudes *)
ab[i_,j_]:=0/;i==j;
ab[i_,j_]:=-ab[j,i]/;j<i;
sb[i_,j_]:=0/;i==j;
sb[i_,j_]:=-sb[j,i]/;j<i;
s[i_,j_]:=ab[i,j]sb[j,i];

(* Generate amplitudes from reduced SSYT *)
SB[col_]:=Module[{B},
B=Complement[Range[Length[col]+2],col];
Signature@Join[col,B]sb@@B
]
amp::shape="wrong shape!";
amp[ssyt_,nt_]:=Module[{trp,ncol,ls,la},
If[ssyt==Null,Return[1]];
trp=TransposeTableau[ssyt];
ncol=Tally[Length/@trp];
Switch[Length[ncol],
1,If[ncol[[1,1]]==2,
ls=nt;la=ncol[[1,2]]-nt,
Message[amp::shape];Abort[]],
2,If[ncol[[1,1]]>2&&ncol[[2,1]]==2,
ls=ncol[[1,2]];la=ncol[[2,2]],
Message[amp::shape];Abort[]],
_,Message[amp::shape];Abort[]
];

Times@@(SB/@trp[[;;ls]])~Join~Apply[ab,trp[[-la;;]],1]
]

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

reduce::overflow="time of reductions exceeds 20, please increase the reduceTry parameter!";
reduce[Amp_,Num_,tryMax_:reduceTry]:=reduce[Amp,Num]=Module[{F=Sum2List@Expand[Amp],F1,iter=1},
While[True,
F1=Sum2List[Plus@@Flatten[F/.rule[Num]]]; (* replace and combine *)
If[F1===F,Break[],F=F1];
If[iter>=tryMax,Message[reduce::overflow];Abort[],iter++]
];
Plus@@F
]
reduce[Num_]:=reduce[#,Num]&

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


(* ::Subsection:: *)
(*Model Input*)


(* ::Item:: *)
(*Macro Parameter -- maxhelicity*)


(* ::Item:: *)
(*GroupMath -- DimR, Adjoint*)


(* ::Item:: *)
(*General -- Prod2List, tAssumptions, MyRepProduct*)


(* ::Item:: *)
(*Amplitude Basis -- LorentzList*)


(* ::Subsubsection::Closed:: *)
(*Functions*)


(* ::Input::Initialization:: *)
(* whether a field has the given helicity *)
helicityQ[model_,h_]:=model[#][helicity]==h&  
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
If[OptionValue[Sorted],flist=SortBy[flist,model[#][helicity]&]];
If[OptionValue[Counting],flist=Tally[flist]];
Return[flist];
]
Options[CheckType]={Sorted->True, Counting->True};
CheckType::unknown="unrecognized fields in type `1`";

groupList={};
CheckGroup[model_Association,groupname_String]:=Module[{group=ToExpression@StringDrop[groupname,-1]},If[MemberQ[groupList,group]&&MemberQ[model[Gauge],groupname],group,Message[CheckGroup::ndef,groupname]]]
CheckGroup[groupname_String]:=Module[{group=ToExpression@StringDrop[groupname,-1]},If[MemberQ[groupList,group],group,Message[CheckGroup::ndef,groupname]]]
CheckGroup::ndef="Group `1` not defined.";

(* Names for Abstract Fields *)
h2f=<|-1->FL,-1/2->\[Psi],0->\[Phi],1/2->OverBar[\[Psi]],1->FR|>;
state2class=D^#2 Times@@Power@@@MapAt[h2f,Tally[#1],{All,1}]&;

Fields[model_]:=Keys@Select[model,MatchQ[#,_Association]&]
SetSimplificationRule[model_]:=Module[{group},Unprotect[Times];Clear[Times];
Do[group=CheckGroup[model,groupname];Check[tSimp[group]//ReleaseHold,"simplification rule for "<>ToString[groupname]<>" not found"],{groupname,model[Gauge]}];
Protect[Times]
]


(* ::Input::Initialization:: *)
SetAttributes[{AddGroup,AddField},HoldFirst];
(* Adding new Gauge Group to a Model *)
AddGroup[model_,groupname_String,field_String,Globalreps_List,ind_Association]:=Module[{profile,group,Freps},
(* read group info from profile *)
profile=FileNameJoin[{Global`$AmplitudeBasisDir,"GroupProfile",StringDrop[groupname,-1]<>"_profile.m"}];
If[FileExistsQ[profile],Get[profile];group=CheckGroup[groupname],
Message[AddGroup::profile,StringDrop[groupname,-1]];Abort[]];
If[!MatchQ[group,_List],Message[AddGroup::groupnotlist,group];Abort[]]; (* check if group is valid *)

model=Merge[{model,<|Gauge->{groupname}|>},Apply[Join]]; (* add gauge group to the model *)
AssociateTo[model[#],groupname->Singlet[group]]&/@Fields[model]; (* pre-existing fields set to singlet by default *)
Freps=MapAt[Adjoint,MapAt[Singlet,CheckGroup/@model[Gauge],{;;-2}],-1]; (* gauge boson representations under all groups *)
AddField[model,field<>"L",-1,Freps,Globalreps,Hermitian->True];
AddField[model,field<>"R",1,Freps,Globalreps,Hermitian->True]; (* add gauge bosons *)
Conj[field<>"L"]=field<>"R";
Conj[field<>"R"]=field<>"L"; (* define special conjugation relation (not denoted by \[Dagger]) for gauge boson names *)
SetSimplificationRule[model]; (* define simplification rules for all gauge groups *)
AssociateTo[rep2ind,groupname->First/@ind]; (* define abstract working index names for all reps of the new group *)
AssociateTo[rep2indOut,groupname->Last/@ind] (* define list of specific indices for all reps of the new group *)
]
AddGroup::groupnotlist=" Unrecognized gauge group `1`. ";
AddGroup::profile="Profile for group `1` not found.";

(* Adding New Field to a Model *)
AddField::overh="helicity of `1` is neither integer nor half-integer.";
Options[AddField]={Flavor->{1},Hermitian->False};
AddField[model_,field_String,hel_,Greps_List,Globalreps_List,OptionsPattern[]]:=Module[{attribute=<||>,flavor=OptionValue[Flavor],NAgroups,shape},
If[IntegerQ[2hel],AppendTo[attribute,helicity->hel],Message[AddField::overh,field]];
AssociateTo[attribute,Thread[model[Gauge]->Greps]];
AssociateTo[attribute,Thread[model[Global]->Globalreps]];
If[flavor=={1},AppendTo[attribute,nfl->1],AssociateTo[attribute,{nfl->flavor[[1]],indfl->flavor[[2]]}]];
AppendTo[attribute,stat->If[IntegerQ[hel],"boson","fermion"]];
AppendTo[model,field->attribute];

NAgroups=Select[model[Gauge],nonAbelian];
shape=MapThread[DimR[#1,#2]&,{CheckGroup/@NAgroups,Cases[Greps,_List]}];
AppendTo[tAssumptions,ToExpression["t"<>field<>ToString[NAgroups[[#]]]]\[Element]Arrays[{shape[[#]]}]]&/@Range[1,Length[shape]];

If[!OptionValue[Hermitian]&&Last@Characters[field]!="\[Dagger]",AddField[model,field<>"\[Dagger]",-hel,RepConj/@Greps,RepConj/@Globalreps,Flavor->OptionValue[Flavor]];
Conj[field]=field<>"\[Dagger]";
Conj[field<>"\[Dagger]"]=field;
];
]


(* ::Input::Initialization:: *)
(* for a given helicity state, find (more than) all field combinations in a model that match the helicities and form singlets for all groups *)
state2type[model_,state_,k_]:=Module[{comblist,groups=CheckGroup/@model[Gauge],singletposition},
(* state: list of helicities for particles in a scattering 
k: number of extra momenta/derivatives
*)
(* field combinations in the model with given helicities *)
comblist=DeleteDuplicatesBy[Distribute[Select[Keys[model],helicityQ[model,#]]&/@state,List],Sort]; 
(* find singlet combinations *)
singletposition=Flatten@Position[MapThread[And,Table[SingletQ[groups[[i]],#]&/@Map[model[#][model[Gauge][[i]]]&,comblist,{2}],{i,Length[groups]}]],True]; 
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


(* ::Item:: *)
(*GroupMath -- SnIrrepDim*)


(* ::Item:: *)
(*Linear Algebra -- Prod2List, basisReduce, FindCor*)


(* ::Item:: *)
(*Permutation Group -- pp, YO*)


(* ::Item:: *)
(*Amplitude -- ab, sb, Pm, reduce, SSYT*)


(* ::Item:: *)
(*Amp to Op -- transform, MonoLorentzBasis*)


(* ::Subsubsection::Closed:: *)
(*Functions*)


(* ::Input::Initialization:: *)
(* symmetrize particles in amplitude *)
YPermute[Mlist_,permutation_,num_]:=Module[{var,Flist,A,outlist,permA,result},
(* Mlist: the list of amplitudes,
permutation: element of symmetric group algebra,
num: the total number of particles in the amplitudes. *)
var=ToExpression/@("variable"<>#&/@ToString/@Range[num]);

(* def abstract functions for amplitudes Mlist *)
Flist=Function[Evaluate[var],
Evaluate[#/.{ab[i_,j_]:>ab[var[[i]],var[[j]]],sb[i_,j_]:>sb[var[[i]],var[[j]]]}]
]&/@Mlist; 
(* permute an abstract function A *)
permA=Pm[A@@Range[num],permutation,A];
(* obtain permuted versions of the amplitudes and reduce *)
result=reduce[num]/@(permA/.{Thread[A->Flist]}\[Transpose]);

Return[result];
] 

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

Options[LorentzBasisForType]={OutputFormat->"operator",Coord->False,FerCom->2};
LorentzBasisForType[model_,type_,OptionsPattern[]]:=Module[{particles,fieldsReplace,k,state,RepFields,Num,Mlist,resultCor,amp2op,OpBasis},
k=Exponent[type,"D"];
particles=CheckType[model,type,Counting->False];
RepFields=Select[PositionIndex[particles],Length[#]>1&];
state=model[#][helicity]&/@particles;
Num=Length[state];

Mlist=SSYT[state,k];
(* generate initial amplitude basis from SSYT *)
resultCor=KeyMap[Thread@Rule[Keys[RepFields],#]&,PermBasis[Mlist,Values@RepFields,Num,Coord->True]];

Switch[OptionValue[OutputFormat],
"amplitude",If[OptionValue[Coord],
<|basis->Mlist,coord->resultCor|>,
Map[#.Mlist&,resultCor,{2+Length[RepFields]}]],  
"operator",amp2op=MonoLorentzBasis[Mlist,Num,finalform->False];
OpBasis=transform[amp2op["LorBasis"],ReplaceField->{model,type,OptionValue[FerCom]}];
If[OptionValue[Coord],
<|basis->OpBasis,coord->Map[Inverse[amp2op["Trans"]]\[Transpose].#&,resultCor,{2+Length[RepFields]}]|>, (* output <|basis, coord|> *)
Map[Expand[OpBasis.Inverse[amp2op["Trans"]]\[Transpose].#]&,resultCor,{2+Length[RepFields]}] (* output basis.coord *)
]
]
] 

LorentzCountForType[model_,type_]:=Module[{particles,k,state,RepFields,Num,grank,group,X,p,rep,irrepComb,AllSym},
particles=CheckType[model,type,Counting->False];
k=Exponent[type,"D"];
RepFields=Select[PositionIndex[particles],Length[#]>1&];
state=model[#][helicity]&/@particles;
Num=Length[state];
grank=If[Num>3,Num-2,Num];
{nt,n}=yngShape[state,k]; (* young tab info *)
If[nt==0&&n==0,Return[<|Normal[{Length[#]}&/@RepFields]->1|>]];
group=ToExpression["SU"<>ToString[grank]];
rep=Yng2Dynk[group,Length/@(YDzero[Num,nt,n]//TransposeTableau)]; (* target irrep *)
irrepComb=FindIrrepCombination[group,MapThread[{PadRight[Count[Flatten@Table[ConstantArray[i,nt-2state[[i]]],{i,Num}],#]&/@FirstPosition[particles,#1],grank-1],#2}&,Tally[particles]\[Transpose]],rep][[2;;]]\[Transpose]; (* Main step: apply FindIrrepCombination *)
AllSym=Flatten[ConstantArray[Distribute[Join@@@Apply[ConstantArray,#1,{2}],List],#2]&@@@irrepComb,2]/.{1}->Nothing; (* list all combinations of syms *)
KeyMap[Map[If[OddQ[nt],MapAt[TransposeYng,#,2],#]&],Association[Rule@@@Tally[Thread[Keys[RepFields]->#]&/@AllSym]]]  (* counting and form association, taking transposition of young diagrams when #\[Epsilon] is odd *)
]


(* ::Subsubsection::Closed:: *)
(*Amplitude To Operators*)


(* ::Input::Initialization:: *)
SetAttributes[{\[Psi]},Flat];\[Psi][a_*b_]:=\[Psi][a,b];
(* Change Amplitude to \[Psi]'s Combination *)
(* input all the angular bracket then obtain \[Psi]'s Combination *)
operab[a_]:=Module[{alist,oper=1,la},If[a===1,oper=1,alist=Prod2List[a];la=Length[alist];Do[oper*=Subscript[\[Psi], #1][2,Alphabet["Greek"][[i]]]Subscript[\[Psi], #2][1,Alphabet["Greek"][[i]]]&[alist[[i,1]],alist[[i,2]]],{i,la}]];oper];
(* input all the square bracket then obtain Overscript[\[Psi], _]'s Combination *)
opersb[s_]:=Module[{slist,oper=1,ls},If[s===1,oper=1,slist=Prod2List[s];ls=Length[slist];Do[oper*=Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #1][1,Alphabet["English"][[i]]]Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), #2][2,Alphabet["English"][[i]]]&[slist[[i,1]],slist[[i,2]]],{i,ls}]];oper];
(* Change \[Psi]'sCombination to each particle *)
(* input arbitrary \[Psi] and Overscript[\[Psi], _], obtain Subscript[\[Phi], i],Subscript[\[Psi], i] or Subscript[F, i] and some D and \[Sigma]. i means the particle's label *)
change[\[Psi]i_,\[Psi]bi_,i_,Greek_]:=Module[{l\[Psi],l\[Psi]b,ans1=\[Psi]i,ans2=\[Psi]bi,ans=1,iGreek=Greek},Switch[\[Psi]i[[0]],Times,l\[Psi]=Length[\[Psi]i],Integer,l\[Psi]=0,_,l\[Psi]=1];Switch[\[Psi]bi[[0]],Times,l\[Psi]b=Length[\[Psi]bi],Integer,l\[Psi]b=0,_,l\[Psi]b=1];Switch[l\[Psi]-l\[Psi]b,0,Switch[l\[Psi],0,ans=Subscript[\[Phi], i],1,ans1[[0]]=\[Psi];ans2[[0]]=\[Psi];ans=\[Psi][ans1,ans2];ans[[0]]=(\[Sigma]^Alphabet["Greek"][[iGreek]]);ans=ans (Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]] Subscript[\[Phi], i]);iGreek++,_,Do[ans=ans Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];ans=ans Subscript[\[Phi], i]],1,Switch[l\[Psi]b,0,ans1[[0]]=Subscript[\[Psi], i];ans=ans1,1,ans=(\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[1,1]],ans1[[1,2]],ans2[[1]],ans2[[2]]] Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]]Subscript[\[Psi], i][ans1[[2,1]],ans1[[2,2]]];iGreek++,_,Do[ans=ans Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]b}];ans=ans Subscript[\[Psi], i][ans1[[l\[Psi],1]],ans1[[l\[Psi],2]]]],-1,Switch[l\[Psi],0,ans2[[0]]=Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i];ans=ans2,1,ans=(\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]]]Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]]Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i][ans2[[2,1]],ans2[[2,2]]];iGreek++,_,Do[ans=ans Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];ans=ans Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i][ans2[[l\[Psi]b,1]],ans2[[l\[Psi]b,2]]]],2,Switch[l\[Psi]b,0,ans=(\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[1,1]],ans1[[1,2]],2,Alphabet["English"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek+1]])[ans1[[2,1]],ans1[[2,2]],1,Alphabet["English"][[iGreek]]]Subscript[Subscript[Subscript[FL, i], Alphabet["Greek"][[iGreek]]], Alphabet["Greek"][[iGreek+1]]];iGreek+=2,1,ans=(\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[1,1]],ans1[[1,2]],ans2[[1]],ans2[[2]]]Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek+1]])[ans1[[2,1]],ans1[[2,2]],2,Alphabet["English"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek+2]])[ans1[[3,1]],ans1[[3,2]],1,Alphabet["English"][[iGreek]]]Subscript[Subscript[Subscript[FL, i], Alphabet["Greek"][[iGreek+1]]], Alphabet["Greek"][[iGreek+2]]];iGreek+=3,_,Do[ans=ans Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]b}];ans=ans (\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[l\[Psi]-1,1]],ans1[[l\[Psi]-1,2]],2,Alphabet["English"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek+1]])[ans1[[l\[Psi],1]],ans1[[l\[Psi],2]],1,Alphabet["English"][[iGreek]]]Subscript[Subscript[Subscript[FL, i], Alphabet["Greek"][[iGreek]]], Alphabet["Greek"][[iGreek+1]]];iGreek+=2],-2,Switch[l\[Psi],0,ans=(\[Sigma]^Alphabet["Greek"][[iGreek]])[2,Alphabet["Greek"][[iGreek]],ans2[[1,1]],ans2[[1,2]]](\[Sigma]^Alphabet["Greek"][[iGreek+1]])[1,Alphabet["Greek"][[iGreek]],ans2[[2,1]],ans2[[2,2]]]Subscript[Subscript[Subscript[FR, i], Alphabet["Greek"][[iGreek]]], Alphabet["Greek"][[iGreek+1]]];iGreek+=2,1,ans=(\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]]]Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek+1]])[2,Alphabet["Greek"][[iGreek]],ans2[[2,1]],ans2[[2,2]]](\[Sigma]^Alphabet["Greek"][[iGreek+2]])[1,Alphabet["Greek"][[iGreek]],ans2[[3,1]],ans2[[3,2]]]Subscript[Subscript[Subscript[FR, i], Alphabet["Greek"][[iGreek+1]]], Alphabet["Greek"][[iGreek+2]]];iGreek+=3,_,Do[ans=ans Subscript[Subscript[D, i], Alphabet["Greek"][[iGreek]]](\[Sigma]^Alphabet["Greek"][[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];ans=ans (\[Sigma]^Alphabet["Greek"][[iGreek]])[2,Alphabet["Greek"][[iGreek]],ans2[[l\[Psi]b-1,1]],ans2[[l\[Psi]b-1,2]]](\[Sigma]^Alphabet["Greek"][[iGreek+1]])[1,Alphabet["Greek"][[iGreek]],ans2[[l\[Psi]b,1]],ans2[[l\[Psi]b,2]]]Subscript[Subscript[Subscript[FR, i], Alphabet["Greek"][[iGreek]]], Alphabet["Greek"][[iGreek+1]]];iGreek+=2],_,Print["spin over 1"]];{ans,iGreek}];
changesp[\[Psi]i_,\[Psi]bi_,i_]:=Module[{l\[Psi],l\[Psi]b,ans1=\[Psi]i,ans2=\[Psi]bi,ans=1,head,label},Switch[\[Psi]i[[0]],Times,l\[Psi]=Length[\[Psi]i],Integer,l\[Psi]=0,_,l\[Psi]=1];Switch[\[Psi]bi[[0]],Times,l\[Psi]b=Length[\[Psi]bi],Integer,l\[Psi]b=0,_,l\[Psi]b=1];Switch[l\[Psi]-l\[Psi]b,0,Switch[l\[Psi],0,ans=Subscript[\[Phi], i],1,ans1[[0]]=\[Psi];ans2[[0]]=\[Psi];ans=\[Psi][ans1,ans2];ans[[0]]=ch[D, Subscript[\[Phi], i]],_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[\[Phi], i]]],1,Switch[l\[Psi]b,0,ans1[[0]]=Subscript[\[Psi], i];ans=ans1,1,ans=ch[D,Subscript[\[Psi], i]][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]],ans2[[1]],ans2[[2]]] ,_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi]b,Subscript[\[Psi], i]]],-1,Switch[l\[Psi],0,ans2[[0]]=Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i];ans=ans2,1,ans=ch[D,Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i]][ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]]],_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i]]],2,Switch[l\[Psi]b,0,ans=Subscript[FL, i][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]]],1,ans=ch[D,Subscript[FL, i]][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]],ans1[[3,1]],ans1[[3,2]],ans2[[1]],ans2[[2]]],_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi]b,Subscript[FL, i]]],-2,Switch[l\[Psi],0,ans=Subscript[FR, i][ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]]],1,ans=ch[D,Subscript[FR, i]][ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]],ans2[[3,1]],ans2[[3,2]]],_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[FR, i]]],_,Print["spin over 1"]];head=ans[[0]];If[head===Subscript,label=0;head=ans,label=Length[ans]/2];Do[If[ans[[1]]===1,head=Subscript[head,ans[[2]]],head=Superscript[head,ans[[2]]]];ans=Delete[ans,{{1},{2}}],{ii,label}];head];


(* ::Input::Initialization:: *)
\[Sigma]change={\[Sigma]^a_:>\[Sigma][a],Subscript[\[Sigma], a_]:>\[Sigma][a]};

bar[sign_]:=If[sign===1,{},{\[Sigma]->
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)}];\[Sigma]2[a_,iGreek_]:={{Superscript["g",a[[1,1]] a[[2,1]]],-I},{1,\[Sigma][a[[1,1]],a[[2,1]]]},{iGreek}};(* where \[Sigma]^\[Mu]\[Nu]=(i/2)[\[Gamma]^\[Mu],\[Gamma]^\[Nu]]~(i/2)(\[Sigma]^\[Mu]Overscript[\[Sigma], _]^\[Nu]-\[Sigma]^\[Nu]Overscript[\[Sigma], _]^\[Mu]) *)\[Sigma]3[a_,iGreek_,sign_:1]:=Module[{e=Alphabet["Greek"][[iGreek]]},{{Superscript["g",a[[1,1]] a[[2,1]]],-Superscript["g",a[[1,1]] a[[3,1]]],Superscript["g",a[[2,1]] a[[3,1]]],I sign Signature[{a[[1,1]],a[[2,1]],a[[3,1]],e}]Superscript["\[Epsilon]",a[[1,1]]a[[2,1]]a[[3,1]]e]},{\[Sigma][a[[3,1]]],\[Sigma][a[[2,1]]],\[Sigma][a[[1,1]]],\[Sigma][e]},{iGreek+1}}];
(* a is the \[Sigma] chain, such as {\[Sigma]^\[Mu],\[Sigma]^\[Nu],...}.iGreek determines the new \[Sigma] matrix's index. sign determines the first \[Sigma] in \[Sigma] chain is \[Sigma] or Overscript[\[Sigma], _],correspond to 1 and -1 *)
\[Sigma]chain[a_,iGreek_,sign_:1]:=Module[{l=Length[a],ans=a//.\[Sigma]change,n,term1,input,output=0},Switch[l,0,term1={{1},{1},{iGreek}},1,term1={{1},{\[Sigma][a[[1,2]]]},{iGreek}}/.bar[sign],2,term1=\[Sigma]2[ans,iGreek]/.bar[sign],_,n=Quotient[l,2];term1=\[Sigma]3[ans[[1;;3]],iGreek,sign];(*Print[term1];*)Do[If[i===n&&n===(l/2),input=Flatten/@(Append[#,ans[[2i]]]&/@List/@term1[[2]]);output=\[Sigma]2[#,term1[[3,1]]]&/@input,input=Flatten/@(Append[#,ans[[2i;;2i+1]]]&/@List/@term1[[2]]);output=\[Sigma]3[#,term1[[3,1]],sign]&/@input];term1[[3]]=output[[1,3]];term1[[2]]=Flatten[output[[All,2]]];term1[[1]]=MapThread[Times[#1,#2]&,{term1[[1]],output[[All,1]]}]//Flatten(*;Print[term1]*),{i,2,n}];term1=term1/.bar[sign]];term1];


(* ::Input::Initialization:: *)
Chain[x__]:=Module[{c={x}},If[Length[c]>1,HoldForm[Times[x]],HoldForm[x]]];
\[Sigma]trace={\[Sigma][i_,j_]:>0,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[i_,j_]:>0};
(* when calculating the \[Sigma] trace, we make use of \[Sigma]chain[], and set all the \[Sigma] matrix remained go to zero *)
trace[\[Sigma]_,iGreek_:1,sign_:1]:=Module[{l=Length[\[Sigma]],T},Switch[l,_?OddQ,T={0,iGreek},_,T=\[Sigma]chain[\[Sigma],iGreek,sign]//.\[Sigma]trace;T={2T[[1]].T[[2]],T[[3,1]]}];T];
(* Simplify two epsilon tensor. x,y express the indices of two epsilon *)
epsilon2[x_,y_]:=Module[{x1,y1,sign},y1=Permutations[y];x1=ConstantArray[x,Length[y1]];sign=Signature[#]&/@y1;-Times@@@(MapThread[Superscript["g",#1 #2]&,{x1,y1},2]).sign];
(* contract the repeated index, disappear g *)
contract={MapThread[Superscript["g",i_ j_]#1:>#2/;Signature[{i,j}]>0&,{{Subscript[Subscript[D, a_], j_],Subscript[Subscript[Subscript[FL, a_], j_], q_],Subscript[Subscript[Subscript[FL, a_], q_], j_],Subscript[Subscript[Subscript[FR, a_], j_], q_],Subscript[Subscript[Subscript[FR, a_], q_], j_],ch\[Psi][p_,\[Sigma][j_],q_],ch\[Psi][p_,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[j_],q_],ch\[Psi][p_,\[Sigma][j_,q1_],q_],ch\[Psi][p_,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[j_,q1_],q_],ch\[Psi][p_,\[Sigma][q1_,j_],q_],ch\[Psi][p_,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[q1_,j_],q_]},{Subscript[Subscript[D, a], i],Subscript[Subscript[Subscript[FL, a], i], q],Subscript[Subscript[Subscript[FL, a], q], i],Subscript[Subscript[Subscript[FR, a], i], q],Subscript[Subscript[Subscript[FR, a], q], i],ch\[Psi][p,\[Sigma][i],q],ch\[Psi][p,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[i],q],ch\[Psi][p,\[Sigma][i,q1],q],ch\[Psi][p,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[i,q1],q],ch\[Psi][p,\[Sigma][q1,i],q],ch\[Psi][p,
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[q1,i],q]}}],Superscript["g",i_ j_]Superscript["\[Epsilon]",j_ k_ l_ m_]:>Signature[{i,k,l,m}] Signature[{j,k,l,m}] Superscript["\[Epsilon]",i k l m],Subscript[Subscript[Subscript[FL, k_], i_], j_]Superscript["\[Epsilon]",i_ j_ a_ b_]:>2I Subscript[Subscript[Subscript[FL, k], a], b]Signature[{i,j,a,b}],Subscript[Subscript[Subscript[FR, k_], i_], j_]Superscript["\[Epsilon]",i_ j_ a_ b_]:>-2I Subscript[Subscript[Subscript[FR, k], a], b]Signature[{i,j,a,b}],Superscript["\[Epsilon]",i1_ j1_ k1_ l1_]Superscript["\[Epsilon]",i2_ j2_ k2_ l2_]:>epsilon2[{i1,j1,k1,l1},{i2,j2,k2,l2}],Superscript["g",i_ j_]Superscript["g",i_ k_]:>Superscript["g",j k],Superscript["g",i_ i_]:>4,Superscript["g",i_ j_]Superscript["g",i_ j_]:>4}//Flatten;(* let Subscript[F, label] or Subscript[Overscript[F, _], label] absorb redundant epsilon *)Ftilde[iGreek_]:={Subscript[Subscript[Subscript[FL, label_], i_], j_]Superscript["\[Epsilon]",a_ b_ c_ d_]:>-I/2 Subscript[Subscript[Subscript[FL, label], Alphabet["Greek"][[iGreek]]], Alphabet["Greek"][[iGreek+1]]]epsilon2[{i,j,Alphabet["Greek"][[iGreek]],Alphabet["Greek"][[iGreek+1]]},{a,b,c,d}],Subscript[Subscript[Subscript[FR, label_], i_], j_]Superscript["\[Epsilon]",a_ b_ c_ d_]:>I/2 Subscript[Subscript[Subscript[FR, label], Alphabet["Greek"][[iGreek]]], Alphabet["Greek"][[iGreek+1]]]epsilon2[{i,j,Alphabet["Greek"][[iGreek]],Alphabet["Greek"][[iGreek+1]]},{a,b,c,d}]};
(* redefine the index *)
beforeform={Subscript[Subscript[D, i_], j_]:>Subscript[D, i][j],Subscript[D, i_][j_]^2:>0,Subscript[D, i_][j_]ch\[Psi][q_,\[Sigma][j_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[j_],Subscript[f_, i_]]:>0,Subscript[D, i_][j_]ch\[Psi][Subscript[f_, i_],\[Sigma][j_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[j_],q_]:>0,Subscript[D, i_][\[Nu]_]ch\[Psi][q_,\[Sigma][\[Mu]_,\[Nu]_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[\[Mu]_,\[Nu]_],Subscript[f_, i_]]:>-I Subscript[D, i][\[Mu]] ch\[Psi][q,1,Subscript[f, i]],Subscript[D, i_][\[Mu]_]ch\[Psi][q_,\[Sigma][\[Mu]_,\[Nu]_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[\[Mu]_,\[Nu]_],Subscript[f_, i_]]:>I Subscript[D, i][\[Nu]] ch\[Psi][q,1,Subscript[f, i]],Subscript[D, i_][\[Mu]_]ch\[Psi][Subscript[q_, i_],\[Sigma][\[Mu]_,\[Nu]_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[\[Mu]_,\[Nu]_],f_]:>-I Subscript[D, i][\[Nu]] ch\[Psi][Subscript[q, i],1,f],Subscript[D, i_][\[Nu]_]ch\[Psi][Subscript[q_, i_],\[Sigma][\[Mu]_,\[Nu]_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[\[Mu]_,\[Nu]_],f_]:>I Subscript[D, i][\[Mu]] ch\[Psi][Subscript[q, i],1,f],Subscript[Subscript[Subscript[FL, i_], j_], k_]:>Subscript[FL, i][j,k],(Subscript[FL, i_][j_,j_]|Subscript[FR, i_][j_,j_]):>0,Subscript[Subscript[Subscript[FR, i_], j_], k_]:>Subscript[FR, i][j,k],Subscript[FL, i_][\[Mu]_,\[Nu]_](Subscript[FR, j_][\[Mu]_,\[Nu]_]|Subscript[FR, j_][\[Nu]_,\[Mu]_]):>0,Subscript[D, i_][j_](Subscript[FL, i_][j_,k_]|Subscript[FR, i_][j_,k_]|Subscript[FL, i_][k_,j_]|Subscript[FR, i_][k_,j_]):>0,Superscript["\[Epsilon]",i_ j_ k_ l_]:>"\[Epsilon]"[i,j,k,l]};
(* distribute all D to each field *)
Dcontract1={MapThread[MapThread[{Subscript[Subscript[D, i_], j_]#1:>#2,Superscript[Subscript[D, i_],j_]#1:>#3}&,{{#1,ch[p__,#1]},{ch[Subscript[D, j],#2],ch[p,Subscript[D, j],#2]},{ch[Superscript[D,j],#2],ch[p,Superscript[D,j],#2]}}]&,{{Subscript[\[Phi], i_],Subscript[FL, i_][q__],Subscript[FR, i_][q__]},{Subscript[\[Phi], i],Subscript[FL, i][q],Subscript[FR, i][q]}}]}//Flatten;
Dcontract2={MapThread[MapThread[{Subscript[Subscript[D, i_], j_] #1:>#2,Superscript[Subscript[D, i_],j_] #1:>#3}&,{{ch\[Psi][#1,q__],ch\[Psi][ch[p__,#1],q__]},{ch\[Psi][ch[Subscript[D, j],#2],q],ch\[Psi][ch[p,Subscript[D, j],#2],q]},{ch\[Psi][ch[Superscript[D,j],#2],q],ch\[Psi][ch[p,Superscript[D,j],#2],q]}}]&,{{Subscript[\[Psi], i_],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i_]},{Subscript[\[Psi], i],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i]}}],MapThread[MapThread[{Subscript[Subscript[D, i_], j_] #1:>#2,Superscript[Subscript[D, i_],j_] #1:>#3}&,{{ch\[Psi][q__,#1],ch\[Psi][q__,ch[p__,#1]]},{ch\[Psi][q,ch[Subscript[D, j],#2]],ch\[Psi][q,ch[p,Subscript[D, j],#2]]},{ch\[Psi][q,ch[Superscript[D,j],#2]],ch\[Psi][q,ch[p,Superscript[D,j],#2]]}}]&,{{Subscript[\[Psi], i_],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i_]},{Subscript[\[Psi], i],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i]}}]}//Flatten;
listtotime={ch[p__]:>HoldForm[Times[p]],ch\[Psi][p__]:>HoldForm[Times[p]],F_["down",a_,"down",b_]:>Subscript[Subscript[F, a], b],F_["down",a_,"up",b_]:>Superscript[Subscript[F, a],b],F_["up",a_,"down",b_]:>Subscript[Superscript[F,a],b],F_["up",a_,"up",b_]:>Superscript[Superscript[F,a],b]};
(* change tensor index into TensorContract, and get back *)
(* define the antisym tensor and vector *)
antisym[a_]:={a\[Element]Matrices[{4,4},Antisymmetric[{1,2}]]};
sym[v_]:={v\[Element]Arrays[{4}]};
(* change tensor into TensorContract *)
tensorform[o_]:=Module[{lo,tensor={},tensor1,tensor2,index={},P,cont={},other=o},lo=Length[o];Do[Switch[o[[i,0]],Subscript[FL, _],other/=o[[i]];tensor=Append[tensor,F[o[[i,0,2]]]];index=Append[index,{o[[i,1]],o[[i,2]]}],Subscript[FR, _],other/=o[[i]];tensor=Append[tensor,F[o[[i,0,2]],"b"]];index=Append[index,{o[[i,1]],o[[i,2]]}],Subscript[D, _],other/=o[[i]];tensor=Append[tensor,de[o[[i,0,2]]]];index=Append[index,o[[i,1]]],ch\[Psi],Switch[Length[o[[i,2]]],0,Continue[],1,other/=o[[i]];tensor=Append[tensor,sigma[o[[i,1]],o[[i,3]]]];index=Append[index,o[[i,2,1]]],2,other/=o[[i]];tensor=Append[tensor,sigma2[o[[i,1]],o[[i,3]]]];index=Append[index,{o[[i,2,1]],o[[i,2,2]]}]],"\[Epsilon]",other/=o[[i]];tensor=Append[tensor,epsilon];index=Append[index,{o[[i,1]],o[[i,2]],o[[i,3]],o[[i,4]]}]],{i,lo}];index=index//Flatten;Do[P=Position[index,index[[i]]]//Flatten;If[P[[2]]===i,Continue[]];cont=Append[cont,P],{i,Length[index]}];tensor1=Union[Cases[tensor,_sigma],Cases[tensor,_de]];tensor2=DeleteCases[Complement[tensor,tensor1],epsilon];tensor=TensorContract[TensorProduct@@tensor,cont]other;{tensor,tensor1,tensor2,index,cont,other}];
(* change TensorContract into tensor index form *)
LorentzIndex=Append[{"\[Mu]","\[Nu]","\[Lambda]","\[Rho]","\[Eta]","\[Sigma]","\[Xi]"},Alphabet["Greek"][[19;;-1]]]//Flatten;
tensortooper[t_]:=Module[{ten,other,index,tensorterm,lten,term,iGreek=0,indexnum,indexposition,si},tensorterm=Flatten[{t}/.{Power->ConstantArray,Times->List}];tensorterm=Cases[tensorterm,_TensorContract];other=t/(Times@@tensorterm);term=Length[tensorterm];Do[ten=tensorterm[[j]];indexnum=1;lten=Length[ten[[1]]];index=indexposition=ConstantArray["down",2Length[ten[[2]]]];Do[index[[ten[[2,i,1]]]]=index[[ten[[2,i,2]]]]=LorentzIndex[[i+iGreek]],{i,Length[ten[[2]]]}];iGreek+=Length[ten[[2]]];Do[Switch[ten[[1,l]],epsilon,other*=Signature[{index[[indexnum]],index[[indexnum+1]],index[[indexnum+2]],index[[indexnum+3]]}]Superscript["\[Epsilon]",index[[indexnum]]index[[indexnum+1]]index[[indexnum+2]]index[[indexnum+3]]];indexnum+=4,_de,If[indexposition[[indexnum]]==="up",other*=Superscript[Subscript[D, ten[[1,l,1]]],index[[indexnum]]],other*=Subscript[Subscript[D, ten[[1,l,1]]], index[[indexnum]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up"];indexnum++,_F,If[Length[ten[[1,l]]]===1,si=FL,si=FR];other*=Subscript[si, ten[[1,l,1]]][indexposition[[indexnum]],index[[indexnum]],indexposition[[indexnum+1]],index[[indexnum+1]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up";indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up";indexnum+=2,_sigma,Switch[ten[[1,l,1]],Subscript[\[Psi], _],si=\[Sigma],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],si=
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)];If[indexposition[[indexnum]]==="up",other*=ch\[Psi][ten[[1,l,1]],si^index[[indexnum]],ten[[1,l,2]]],other*=ch\[Psi][ten[[1,l,1]],Subscript[si, index[[indexnum]]],ten[[1,l,2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up"];indexnum++,_sigma2,Switch[ten[[1,l,1]],Subscript[\[Psi], _],si=\[Sigma],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],si=
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)];Switch[indexposition[[indexnum;;indexnum+1]],{"up","up"},other*=ch\[Psi][ten[[1,l,1]],Superscript[Superscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[1,l,2]]],{"up","down"},other*=ch\[Psi][ten[[1,l,1]],Subscript[Superscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[1,l,2]]];indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up",{"down","up"},other*=ch\[Psi][ten[[1,l,1]],Superscript[Subscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[1,l,2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up",{"down","down"},other*=ch\[Psi][ten[[1,l,1]],Subscript[Subscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[1,l,2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]=indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up"];indexnum+=2,_,Print["some thing are ignored"]],{l,lten}],{j,term}];other];
part4[m_]:=If[Length[m]>=4,m[[4]],0];


(* ::Input::Initialization:: *)
(* deal with monomial amplitude, input respectively angular brackets and square brackets and particle number *)
OperMonoResp[a_:1,s_:1,n_]:=Module[{opA,opS,\[Psi]i=Table[1,{i,n},{j,2}],op=1,lop,index,opi,iGreek=11,coef,chain={},chainnum={},indexa,index\[Alpha],lchain,\[Sigma]m,oper},opA=operab[a];opS=opersb[s];Do[\[Psi]i[[i,1]]=Cases[opA,Subscript[\[Psi], i][_Integer,_]];\[Psi]i[[i,1,0]]=Times;\[Psi]i[[i,2]]=Cases[opS,Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i][_Integer,_]];\[Psi]i[[i,2,0]]=Times,{i,n}];Do[opi=change [\[Psi]i[[i,1]],\[Psi]i[[i,2]],i,iGreek];op=op opi[[1]];iGreek=opi[[2]],{i,n}];
op[[0]]=List;opS=Cases[op,Subscript[Subscript[Subscript[FL, _], _], _]]\[Union]Cases[op,Subscript[Subscript[Subscript[FR, _], _], _]];coef=1/2^Length[opS]*I^Length[Cases[op,Subscript[Subscript[D, _], _]]];opS=Union[opS,Cases[op,Subscript[Subscript[D, _], _]],Cases[op,Subscript[\[Phi], _]]];opA=Complement[op,opS];lop=Length[opA];Do[Switch[opA[[i,0]],Subscript[\[Psi], _],If[Cases[chain,opA[[i,0]]]!={},Continue[]];index=opA[[i,2]];If[opA[[i,1]]===1,coef=-coef];chain=Append[chain,opA[[i,0]]];index\[Alpha]=Select[opA,#[[2]]==index&];index\[Alpha]=Complement[index\[Alpha],{opA[[i]]}];Do[If[index\[Alpha][[1,0,1]]===\[Sigma],index=index\[Alpha][[1,4]];chain=Append[chain,index\[Alpha][[1,0]]];If[index\[Alpha][[1,3]]===2,coef=-coef];(**) indexa=Select[opA,part4[#]==index&];indexa=Complement[indexa,index\[Alpha]];If[indexa==={},indexa=Select[opA,#[[2]]==index&];chain=Append[chain,indexa[[1,0]]];chainnum=Append[chainnum,Length[chain]];Break[]];If[indexa[[1,1]]===1,coef=-coef];index=indexa[[1,2]];index\[Alpha]=Select[opA,#[[2]]==index&];index\[Alpha]=Complement[index\[Alpha],indexa];chain=Append[chain,indexa[[1,0]]],chain=Append[chain,index\[Alpha][[1,0]]];chainnum=Append[chainnum,Length[chain]];Break[]],{j,lop}],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],If[Cases[chain,opA[[i,0]]]!={},Continue[]];index=opA[[i,2]];If[opA[[i,1]]===2,coef=-coef];chain=Append[chain,opA[[i,0]]];indexa=Select[opA,part4[#]==index&];indexa=Complement[indexa,{opA[[i]]}];Do[If[indexa==={},indexa=Select[opA,#[[2]]==index&];indexa=Complement[indexa,{opA[[i]]}];chain=Append[chain,indexa[[1,0]]];chainnum=Append[chainnum,Length[chain]];Break[]];index=indexa[[1,2]];If[indexa[[1,1]]===1,coef=-coef];index\[Alpha]=Select[opA,#[[2]]==index&];index\[Alpha]=Complement[index\[Alpha],indexa];chain=Append[chain,indexa[[1,0]]];If[index\[Alpha][[1,0,1]]===\[Sigma],If[index\[Alpha][[1,3]]===2,coef=-coef];index=index\[Alpha][[1,4]];indexa=Select[opA,part4[#]==index&];indexa=Complement[indexa,index\[Alpha]];chain=Append[chain,index\[Alpha][[1,0]]],chainnum=Append[chainnum,Length[chain]];chain=Append[chain,index\[Alpha][[1,0]]];Break[]],{j,lop}]],{i,lop}](*after all the \[Psi] chains are found*);If[Length[opA]>Length[chain],Do[If[opA[[i,0,1]]===\[Sigma],If[Cases[chain,opA[[i,0]]]!={},Continue[]];index=opA[[i,4]];If[opA[[i,3]]===2,coef=-coef];(*Print[coef];*)chain=Append[chain,opA[[i,0]]];indexa=Select[opA,part4[#]==index&];indexa=Complement[indexa,{opA[[i]]}];Do[index=indexa[[1,2]];If[indexa[[1,1]]===1,coef=-coef];(*Print[coef];*)index\[Alpha]=Select[opA,#[[2]]==index&];index\[Alpha]=Complement[index\[Alpha],indexa];chain=Append[chain,indexa[[1,0]]];If[Cases[chain,index\[Alpha][[1,0]]]!={},chainnum=Append[chainnum,Length[chain]];Break[]];chain=Append[chain,index\[Alpha][[1,0]]];index=index\[Alpha][[1,4]];If[index\[Alpha][[1,3]]===2,coef=-coef];(*Print[coef];*)indexa=Select[opA,part4[#]==index&];indexa=Complement[indexa,index\[Alpha]],{j,lop}]],{i,lop}]];
(****************************)
(*Print[{opA,opS}];Print[{chain,chainnum,coef,iGreek}];*)coef*=Signature[DeleteCases[chain,\[Sigma]^_]];If[chain==={},oper=1,lchain=Length[chainnum];Switch[chain[[1]],Subscript[\[Psi], _],\[Sigma]m=\[Sigma]chain[chain[[2;;chainnum[[1]]-1]],iGreek,1];iGreek=\[Sigma]m[[3,1]];(*chain={chain[[1]],\[Sigma]m};*)oper=Sum[ch\[Psi][chain[[1]],\[Sigma]m[[2,i]],chain[[chainnum[[1]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],\[Sigma]m=\[Sigma]chain[chain[[2;;chainnum[[1]]-1]],iGreek,-1];iGreek=\[Sigma]m[[3,1]];oper=Sum[ch\[Psi][chain[[1]],\[Sigma]m[[2,i]],chain[[chainnum[[1]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],\[Sigma]^_,{oper,iGreek}=trace[Append[chain[[2;;chainnum[[1]]]],chain[[1]]],iGreek,-1]]];If[lchain>1,Do[Switch[chain[[chainnum[[j-1]]+1]],Subscript[\[Psi], _],\[Sigma]m=\[Sigma]chain[chain[[chainnum[[j-1]]+2;;chainnum[[j]]-1]],iGreek,1];iGreek=\[Sigma]m[[3,1]];oper*= Sum[ch\[Psi][chain[[chainnum[[j-1]]+1]],\[Sigma]m[[2,i]],chain[[chainnum[[j]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],\[Sigma]m=\[Sigma]chain[chain[[chainnum[[j-1]]+2;;chainnum[[j]]-1]],iGreek,-1];iGreek=\[Sigma]m[[3,1]];oper*= Sum[ch\[Psi][chain[[chainnum[[j-1]]+1]],\[Sigma]m[[2,i]],chain[[chainnum[[j]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],\[Sigma]^_,oper*= trace[chain[[chainnum[[j-1]]+1;;chainnum[[j]]]],iGreek][[1]];iGreek= trace[chain[[chainnum[[j-1]]+1;;chainnum[[j]]]],iGreek][[2]]],{j,2,lchain}]];opS[[0]]=Times;oper opS coef];
(* input monomial amplitude, label shows which F will absorb epsilon *)
OperMono[A_,n_]:=Module[{oper,Aa=1,As=1,LA,coeff=1},Switch[A[[0]],ab,oper=OperMonoResp[A,1,n],sb,oper=OperMonoResp[1,A,n],Power,Switch[A[[1,0]],ab,oper=OperMonoResp[A,1,n],sb,oper=OperMonoResp[1,A,n]],Times,LA=Length[A];Do[Switch[A[[i,0]],ab,Aa*=A[[i]],sb,As*=A[[i]],Power,Switch[A[[i,1,0]],ab,Aa*=A[[i]],sb,As*=A[[i]]],_,coeff*=A[[i]]],{i,LA}];oper=coeff*OperMonoResp[Aa,As,n],_,oper=A OperMonoResp[1,1,n]];oper=Expand[Expand[oper]//.contract]//.contract;oper=Expand[oper//.Ftilde[-2]]//.contract//.beforeform];
(* input complete amplitude, firstF shows which F will absorb epsilon *)
OperSpMonoResp[a_:1,s_:1,n_]:=Module[{opA,opS,\[Psi]i=Table[1,{i,n},{j,2}],op=1,lop,index,opi,coef,chain={},chainnum={},indexa,index\[Alpha],lchain,\[Sigma]m,oper},opA=operab[a];opS=opersb[s];Do[\[Psi]i[[i,1]]=Cases[opA,Subscript[\[Psi], i][_Integer,_]];\[Psi]i[[i,1,0]]=Times;\[Psi]i[[i,2]]=Cases[opS,Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i][_Integer,_]];\[Psi]i[[i,2,0]]=Times,{i,n}];Do[opi=changesp[\[Psi]i[[i,1]],\[Psi]i[[i,2]],i];op=op opi,{i,n}];op];
alphachange={"a"->"\!\(\*OverscriptBox[\(\[Alpha]\), \(.\)]\)","b"->"\!\(\*OverscriptBox[\(\[Beta]\), \(.\)]\)","c"->"\!\(\*OverscriptBox[\(\[Gamma]\), \(.\)]\)","d"->"\!\(\*OverscriptBox[\(\[Delta]\), \(.\)]\)","e"->"\!\(\*OverscriptBox[\(\[Epsilon]\), \(.\)]\)","f"->"\!\(\*OverscriptBox[\(\[Zeta]\), \(.\)]\)"};
(* input monomial amplitude, label shows which F will absorb epsilon *)
OperSpMono[A_,n_]:=Module[{oper,Aa=1,As=1,LA,coeff=1},Switch[A[[0]],ab,oper=OperSpMonoResp[A,1,n],sb,oper=OperSpMonoResp[1,A,n],Power,Switch[A[[1,0]],ab,oper=OperSpMonoResp[A,1,n],sb,oper=OperSpMonoResp[1,A,n]],Times,LA=Length[A];Do[Switch[A[[i,0]],ab,Aa*=A[[i]],sb,As*=A[[i]],Power,Switch[A[[i,1,0]],ab,Aa*=A[[i]],sb,As*=A[[i]]],_,coeff*=A[[i]]],{i,LA}];oper=coeff*OperSpMonoResp[Aa,As,n],_,oper=A OperSpMonoResp[1,1,n]];oper=oper//.alphachange//.listtotime];
OperPoly[A_,n_,OptionsPattern[]]:=Module[{operpoly,form,form1,form2,ten,tAssumptions},If[OptionValue[LorForm],(*If[A[[0]]===Plus,operpoly=OperMono[#,n]&/@A,operpoly=OperMono[A,n]];*)operpoly=Thread[head[A,n],Plus]/.{head->OperMono};(*operpoly=Distr[OperMono[A,n]];*)If[operpoly[[0]]===Plus,operpoly=List@@operpoly;
form=tensorform/@operpoly;form1=Union@@form[[All,2]];form2=Union@@form[[All,3]];tAssumptions={epsilon\[Element]Arrays[{4,4,4,4},Antisymmetric[{1,2,3,4}]]}\[Union](antisym/@form2)\[Union](sym/@form1)//Flatten;ten=Map[TensorReduce[#,Assumptions->tAssumptions]&,Plus@@form[[All,1]]//Simplify,{2,3}]//Expand;(*If[ten[[0]]===Plus,operpoly=tensortooper[#,OptionValue[FerCom]]&/@ten,operpoly=tensortooper[ten,OptionValue[FerCom]]];*)operpoly=Thread[head[ten],Plus]/.{head->tensortooper}(*;operpoly=Distr@tensortooper[ten,OptionValue[FerCom]]*),form=Map[TensorReduce,tensorform[operpoly],2];operpoly=tensortooper[form[[1]]]];
If[OptionValue[Dcontract],operpoly=operpoly//.Flatten[{Dcontract1,Dcontract2}],operpoly],(*If[A[[0]]===Plus,operpoly=OperSpMono[#,n]&/@A,operpoly=OperSpMono[A,n]];*)operpoly=Thread[head[A,n],Plus]/.{head->OperSpMono}(*;operpoly=Distr@OperSpMono[A,n]*)(*;operpoly=operpoly//.listtotime*)]];
(*use with Main.n program*)
Options[OperPoly]={LorForm->True,Dcontract->False};


(* ::Input::Initialization:: *)
beforechange={Subscript[Subscript[D, n_], \[Nu]_]|Superscript[Subscript[D, n_],\[Nu]_]:>Subscript[D, n][\[Nu]],Subscript[\[Sigma], \[Mu]_]|Superscript[\[Sigma],\[Mu]_]|\[Sigma]^\[Mu]_:>\[Sigma][\[Mu]],Subscript[\[Gamma], \[Mu]_]|Superscript[\[Gamma],\[Mu]_]|\[Gamma]^\[Mu]_:>\[Gamma][\[Mu]],Subscript[
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\), \[Mu]_]|Superscript[
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\),\[Mu]_]|
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)^\[Mu]_:>
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[\[Mu]],Subscript[Subscript[\[Sigma]_, \[Mu]_], \[Nu]_]|Superscript[Subscript[\[Sigma]_, \[Mu]_],\[Nu]_]|Subscript[Superscript[\[Sigma]_,\[Mu]_],\[Nu]_]|Superscript[Superscript[\[Sigma]_,\[Mu]_],\[Nu]_]:>\[Sigma][\[Mu],\[Nu]],Superscript["\[Epsilon]",Times[a_,b_,c_,d_]]:>"\[Epsilon]"[a,b,c,d]};
SetAttributes[{antichange}, HoldAll];
antichange[PartofAmp_,Greek_]:=Module[{spinor,particle},Switch[PartofAmp,Subscript[D, _][_],particle=PartofAmp[[0,2]];spinor=-I/2*Subscript[\[Psi], particle][1,Alphabet["Greek"][[Greek]]]Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), particle][1,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[1]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]];Greek++,Subscript[FL, _][__],particle=PartofAmp[[0,2]];spinor=1/4*Subscript[\[Psi], particle][1,Alphabet["Greek"][[Greek]]]Subscript[\[Psi], particle][1,Alphabet["Greek"][[Greek+1]]]\[Sigma][PartofAmp[[2]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[4]]][2,Alphabet["Greek"][[Greek+1]],1,Alphabet[][[Greek]]];Greek+=2,Subscript[FR, _][__],particle=PartofAmp[[0,2]];spinor=1/4*Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), particle][1,Alphabet[][[Greek]]]Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), particle][1,Alphabet[][[Greek+1]]]\[Sigma][PartofAmp[[2]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[4]]][1,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek+1]]];Greek+=2,ch\[Psi][Subscript[\[Psi], _],1,Subscript[\[Psi], _]],spinor=PartofAmp[[1]][2,Alphabet["Greek"][[Greek]]]PartofAmp[[3]][1,Alphabet["Greek"][[Greek]]];Greek++,ch\[Psi][Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],1,Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _]],spinor=PartofAmp[[1]][1,Alphabet[][[Greek]]]PartofAmp[[3]][2,Alphabet[][[Greek]]];Greek++,ch\[Psi][Subscript[\[Psi], _],\[Sigma][_]|\[Gamma][_],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _]],spinor=PartofAmp[[1]][2,Alphabet["Greek"][[Greek]]]\[Sigma][PartofAmp[[2,1]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek]]]PartofAmp[[3]][2,Alphabet[][[Greek]]];Greek++,ch\[Psi][Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[_]|\[Gamma][_],Subscript[\[Psi], _]],spinor=PartofAmp[[1]][1,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2,1]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]]PartofAmp[[3]][1,Alphabet["Greek"][[Greek]]];Greek++,ch\[Psi][Subscript[\[Psi], _],\[Sigma][__],Subscript[\[Psi], _]],spinor=I/2*PartofAmp[[1]][2,Alphabet["Greek"][[Greek]]](\[Sigma][PartofAmp[[2,1]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2,2]]][2,Alphabet["Greek"][[Greek+1]],2,Alphabet[][[Greek]]]-\[Sigma][PartofAmp[[2,2]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2,1]]][2,Alphabet["Greek"][[Greek+1]],2,Alphabet[][[Greek]]])PartofAmp[[3]][1,Alphabet["Greek"][[Greek+1]]];Greek+=2,ch\[Psi][Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _],
\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)[__],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _]],spinor=I/2*PartofAmp[[1]][1,Alphabet[][[Greek]]](\[Sigma][PartofAmp[[2,1]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2,2]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek+1]]]-\[Sigma][PartofAmp[[2,2]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2,1]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek+1]]])PartofAmp[[3]][2,Alphabet[][[Greek+1]]];Greek+=2,"\[Epsilon]"[__],spinor=I/4(\[Sigma][PartofAmp[[1]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek+1]]]\[Sigma][PartofAmp[[3]]][2,Alphabet["Greek"][[Greek+1]],2,Alphabet[][[Greek+1]]]\[Sigma][PartofAmp[[4]]][1,Alphabet["Greek"][[Greek+1]],1,Alphabet[][[Greek]]]-\[Sigma][PartofAmp[[1]]][1,Alphabet["Greek"][[Greek]],1,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[2]]][2,Alphabet["Greek"][[Greek+1]],2,Alphabet[][[Greek]]]\[Sigma][PartofAmp[[3]]][1,Alphabet["Greek"][[Greek+1]],1,Alphabet[][[Greek+1]]]\[Sigma][PartofAmp[[4]]][2,Alphabet["Greek"][[Greek]],2,Alphabet[][[Greek+1]]]);Greek+=2,Subscript[\[Phi], _],spinor=1,_,spinor=PartofAmp];(*Print[spinor];*)spinor];\[Sigma]contract={\[Sigma][\[Mu]_][n1_,\[Alpha]_,n2_,a_]\[Sigma][\[Mu]_][n3_,\[Beta]_,n4_,b_]:>(-1)^(n3+n4) 2\[Epsilon][n1,\[Alpha],n3,\[Beta]]\[Epsilon][n2,a,n4,b]};
\[Epsilon]contract={\[Epsilon][n1_,\[Alpha]_,n2_,\[Beta]_]Subscript[\[Psi], i_][n3_,\[Beta]_]:>Subscript[\[Psi], i][n1,\[Alpha]],\[Epsilon][n1_,a_,n2_,b_]Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i_][n3_,b_]:>Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i][n1,a],\[Epsilon][n1_,a_,n2_,b_]\[Epsilon][n3_,b_,n4_,c_]:>\[Epsilon][n1,a,n4,c],\[Epsilon][n1_,a_,n2_,b_]\[Epsilon][n3_,c_,n4_,b_]:>(-1)^(n3+n4+1) \[Epsilon][n1,a,n3,c],\[Epsilon][n1_,b_,n2_,a_]\[Epsilon][n3_,b_,n4_,c_]:>(-1)^(n1+n2+1) \[Epsilon][n2,a,n4,c],\[Epsilon][n1_,a_,n2_,a_]:>2};
asbracket={Subscript[\[Psi], i_][2,a_]Subscript[\[Psi], j_][1,a_]:>ab[i,j],Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), i_][1,a_]Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), j_][2,a_]:>sb[i,j]};
(* operators maked by OperPoly[Amp,particle number,firstF\[Rule]?,Dcontract\[Rule]False] , or Oper[Model,type,Amp,toAmp\[Rule]True] *)
AmpMono[opermono_]:=Module[{Greek=1,oper,amp,fermion,fermionsign={}},oper=opermono//.beforechange;fermion=Cases[oper,_ch\[Psi]];Do[AppendTo[fermionsign,fermion[[ii,1]]];AppendTo[fermionsign,fermion[[ii,3]]],{ii,Length[fermion]}];fermionsign=Signature[fermionsign];amp=fermionsign*antichange[#,Greek]&/@oper;amp=Expand[amp]//.\[Sigma]contract//.\[Epsilon]contract//.asbracket];
Amp[oper_]:=(*If[oper[[0]]===Plus,AmpMono[#]&/@oper,AmpMono[oper]]*)Thread[head[oper],Plus]/.{head->AmpMono};


(* ::Input::Initialization:: *)
(* find monomial Lorentz basis *)
Options[MonoLorentzBasis]={finalform->True};
MonoLorentzBasis[input_List,OptionsPattern[]]:=MonoLorentzBasis[SSYT@@input,Length[state],OptionValue] (* input = {state,k} *)
MonoLorentzBasis[spinorbasis_List,num_Integer,OptionsPattern[]]:=Module[{operbasis,coefbasis,basis,transfer},
operbasis=OperPoly[#,num,Dcontract->False]&/@spinorbasis;operbasis=Flatten[operbasis//.{Plus->List}]//.{Times[_Integer,p__]:>Times[p],Times[_Rational,p__]:>Times[p],Times[_Complex,p__]:>Times[I,p]};coefbasis=FindCor[reduce[#,Length[state]],spinorbasis]&/@(Amp[#]&/@operbasis);basis=Subsets[coefbasis,{Length[spinorbasis]}];Do[If[MatrixRank[basis[[ii]]]===Length[spinorbasis],transfer=basis[[ii]];Break[]],{ii,Length[basis]}];basis=Flatten[Position[coefbasis,#][[1]]&/@transfer];<|"LorBasis"->operbasis[[basis]]//.(Dcontract1\[Union]Dcontract2)//.If[OptionValue[finalform],listtotime,{}],"Trans"->transfer|>];


(* ::Subsection:: *)
(*Gauge Group Factor*)


(* ::Item:: *)
(*Permutation Group -- permutationSignature, pp, Generateb, ColistPP, TransposeTableau, Dynk2Yng, FindIrrepCombination, MyRepProduct*)


(* ::Item:: *)
(*GroupMath -- DimR, SnIrrepDim, PlethysmsN*)


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
ColumnConditionQ[l_]:=And@@(#<=1&)/@(Max[#[[1;;-1,2]]]&/@(Tally/@Select[TransposeTableau[l],Length[#]!=0&]))
RowConditionQ[l_]:=Module[{it,nrow,unique,counter,temp,result=True},
nrow=Length[l];
unique=Union[Cases[Flatten[l],_Integer]];
If[Length[unique]==0,Return[result]];
MapThread[Set,{counter/@unique,Table[0,{i,Length[unique]}]}];
Do[it=-1;
While[(-it)<=Length[l[[k]]],
If[StringQ[l[[k,it]]],Break[]];
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
LRrule2[yt1_,yt2_,fdiag_,n_]:=Module[{fdl={},fdlstr={},ldiag2=Flatten[Table[i&/@yt2[[i]],{i,1,Length[yt2]}]],ldiag2str=Flatten[yt2]},
FillYD[fdl,fdlstr,yt1,yt1,ldiag2,ldiag2str,fdiag,n];fdlstr]

LRTableaux[fytl_,YTlist_,path_,n_]:=Module[{conlist,lYTlist=Length[YTlist],tYTlist},
If[lYTlist==1,AppendTo[fytl,YTlist[[1]]];Return[]];
conlist=LRrule2[YTlist[[1]],YTlist[[2]],path[[1]],n];
If[lYTlist==2,AppendTo[fytl,#]&/@conlist;Return[]];
Do[
tYTlist=YTlist[[3;;-1]];
PrependTo[tYTlist,conlist[[i]]];
LRTableaux[fytl,tYTlist,path[[2;;-1]],n],{i,1,Length[conlist]}
]
]
SetAttributes[LRTableaux,HoldFirst]

ConvertPathtoYD[nlist_,ydlist_,n_]:=ConvertPathtoYD[nlist,ydlist,n]=Module[{nl,tydlist},
(*Do not take into account the first elements in ydlist*)
tydlist=PadRight[#,n,0]&/@ydlist;
nl=Accumulate[nlist];
nl=(nl-(Total/@tydlist))/n;
Drop[(tydlist[[#]]+nl[[#]])&/@Range[1,Length[tydlist]]/.{0->Nothing},1]]

GenerateTYT[irrep_,numIP_,baserep_,fnamenum_,index_,group_]:=GenerateTYT[irrep,numIP,baserep,fnamenum,index,group]=Module[{tindex=index,n=Length[group]+1,standardyt,partbaserep=Dynk2Yng[baserep],ydlist,ll,fytl={}},
If[Total[baserep]==0,Return[{{}}]];
(*added following two lines to adapt the GenerateSU3 and GenerateSU3*)
If[!MatchQ[baserep,{1,0...}],tindex=StringJoin@@ConstantArray[ToString[index],2]];
If[Length[StringCases[fnamenum,"\[Dagger]"]]!=0&&baserep=={1},tindex=StringJoin@@ConstantArray[ToString[index],2]];
partbaserep=partbaserep/.{0->Nothing};
standardyt=MapThread[Range,{Accumulate[partbaserep]-partbaserep+1,Accumulate[partbaserep]}];
ll=ConvertPathtoYD[ConstantArray[Total@partbaserep,numIP],#,n]&/@(FindRepPath[group,irrep,ConstantArray[baserep,numIP]]);
(*the lables of the indices is in the following form: index[i,j,k],
  i labels the i-th group of the repeated fields,
  j labels the j-th field in this group of repeated fields,
  k labels the k-th fundamental indices of this particular field*)
ydlist=Table[Map[tindex<>"[ToString["<>ToString[fnamenum]<>"],"<>ToString[i]<>","<>ToString[#]<>"]"&,standardyt,{2}],{i,numIP}];
LRTableaux[fytl,ydlist,#,n]&/@ll;
fytl
]


(* ::Input::Initialization:: *)
(********************* Littlewood-Richardson *****************)

(*Generate the input for the function GenerateLRT to obtain the y-basis symbolic tensors*)
GenerateLRInput[nonsinglets_]:=If[nonsinglets[[1]]>1,{nonsinglets[[2]],1,nonsinglets[[2]],nonsinglets[[3]]<>ToString[#]}&/@Range[nonsinglets[[1]]],{{nonsinglets[[2]],1,nonsinglets[[2]],nonsinglets[[3]]}}]

nonFund2Fund[groupname_,rep_,flag_:False]:=Module[{group=CheckGroup[groupname],indexFund},indexFund=rep2ind[groupname][Fund[group]];
If[rep!=Fund[group],ToExpression[StringRepeat[ToString[indexFund],2]],
If[group==SU2&&flag,ToExpression[StringRepeat[ToString[indexFund],2]],indexFund]]
]

(*Generate the replacement rule for the symbolic tensor indices of the output of the function GenerateLRT*)
GenerateLRRP[groupname_,nonsinglets_]:=Module[{nfield=nonsinglets[[1]],SUNirrep=nonsinglets[[2]],fname=nonsinglets[[3]],fnlist,nfund,index},
nfund=Total[Dynk2Yng[SUNirrep]];
If[nfield==1,{},
fnlist=Array[fname<>ToString[#]&,nonsinglets[[1]]];
index=nonFund2Fund[groupname,SUNirrep,StringTake[fname,-1]=="\[Dagger]"];(* get appropriate index name *)
Flatten[Table[MapThread[Rule,{index[fnlist[[i]],1,#]&/@Range[nfund],index[fname,i,#]&/@Range[nfund]}],{i,nfield}]]]
]

GenerateLRT[groupname_,replist_]:=
(*replist is a list of elements in the following form: {__,__,__,__}, 
the first slot is the DykinCoefficient of the constructed representation,
the second slot is the number of repeated fields that construct the representation in the first slot,
the third slot is the representation of the repeated fields,
the last slot is the name of the repeated field*)
Module[{group=CheckGroup[groupname],indmap=rep2ind[groupname],nlist,irreplist,basereplist,index,tyt1,pathlists={},result={}},
index=ToString@indmap@Fund[group];
irreplist=replist[[All,1]];
nlist=(#[[2]]*Total[Dynk2Yng[#[[3]]]])&/@replist;
basereplist=replist[[All,3]];
(*Generate tensor Young Tableaux*)
tyt1=Distribute[GenerateTYT@@@(Join[#,{index,group}]&/@replist),List];
pathlists=ConvertPathtoYD[nlist,#,Length[group]+1]&/@FindSingletPath[group,irreplist];
Do[LRTableaux[result,tyt1[[j]],pathlists[[i]],Length[group]+1],{i,1,Length[pathlists]},{j,1,Length[tyt1]}];
result
]


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
Product2ContractV2[x_,inarglist_,OptionsPattern[]]:=Module[{tensorlist,headlist,arglist,uniquelist,listrepeat,tensorp},
tensorlist=Sort@Prod2List[x];
headlist=Head/@tensorlist;
arglist=Flatten[List@@@tensorlist];
uniquelist=Union[arglist];
listrepeat=Select[Flatten/@(Position[arglist,#]&/@uniquelist),Length[#]==2&];
If[Length[listrepeat]!=0,arglist=Delete[arglist,{#}&/@Flatten[listrepeat]]];
tensorp=TensorProduct@@headlist/.OptionValue[Symb2Num];
If[Length[listrepeat]!=0,tensorp=TensorContract[tensorp,listrepeat]];
Transpose[tensorp,FindPermutation[arglist,inarglist]]
]


(* ::Input::Initialization:: *)
(*label the field name concerning repeated fields*)
GenerateFieldName[model_,groupname_,fs_]:=Module[{dim,result},
dim=DimR[CheckGroup[groupname],model[fs[[1]]][groupname]];
result=ToExpression["t"<>fs[[1]]<>groupname<>ToString[#]]&/@Range[fs[[2]]];
If[Cases[tAssumptions,#,Infinity]=={},AppendTo[tAssumptions,#\[Element]Arrays[{dim}]]]&/@result;
result]

GenerateFieldIndex[model_,groupname_,flist_]:=Module[{symbols,arg,indices},
symbols=rep2ind[groupname]/@(model[#[[1]]][groupname]&/@flist);
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
tensorlist=ReplacePart[tensorlist,(Join@@pos)->#[++ct[#]]&[indmap[pairRep[[1]]] ] ],
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
tempx=Expand[Expand[x]/.Power[z_,y_]:>Times@@ConstantArray[z,y]];
flist=Select[fts,Total[model[#[[1]]][groupname]]!=0&];
tfs=GenerateFieldTensor[model,groupname,flist,xmap];
rt=tReduce[Plus@@(Product2Contract/@(Flatten[{Expand[tempx]}/.Plus->List]*tfs))];
UnfoldContraction[rt,xmap,rep2ind[groupname]]
]
SetAttributes[RefineTensor,HoldFirst]

(* Refine gauge group tensors with the symmetry of the invariant tensors *)
TRefineTensor[x_,model_,groupname_,fts_]:=Module[{trank,tdim,result,len},
trank=tRank[x];
tdim=tDimensions[x];
result=Flatten[{x}];
len=Length[result];
result=RefineTensor[#,model,groupname,fts]&/@result;
If[!IntegerQ[trank]||trank==0,Return[result[[1]]]];
unflatten[result,tdim]
]



(* ::Subsubsection::Closed:: *)
(*Symmetrization related*)


(* ::Input::Initialization:: *)
(*symmetrize the group factor numerically with certain group algebra elements*)
SymBasis[basis_,perms_]:=
Plus@@(MapThread[(Transpose[basis,#1]*#2)&,Transpose[(ColistPP[perms])]])

(*find the independent m-basis tensors and store them into the symbolic forms, numerical tensor forms and numerical vector forms*)
FindIndependentMbasis[Mbasis_,tMbasis_,vMbasis_]:=Module[{result,tempI},
result=Part[#,basisReduce[vMbasis]["pos"]]&/@{Mbasis,tMbasis,vMbasis};
tempI=If[Or@@(#\[Element]Reals&/@#),1,I]&/@result[[3]];
tempI*#&/@result
]
(*Delete duplicated list of tensors that are propotional to each other*)
SimpGFV2[x_]:=If[Length[x]>=1,DeleteDuplicates[Replace[#,{_Rational->1,_Integer->1,_Complex->1},{1}]&/@(Flatten@(x/.Plus->List))],x]

(*Get the coordinnate of arbitrary group factor tensor in terms of the m-basis*)
GetCoord[qr_,v_]:=qr[[1]].v.Transpose[Inverse[qr[[2]]]]

(*Get the symmetrized group factor tensors from the m-basis*)
GetSymBasis[tMBasis_,SNIrreps_,disp_,qr_,tdim_]:=Module[{multi=SNIrreps[[2]],key=SNIrreps[[1]],num,perms,displist,tensordim,mrank,resultAux={},result={},i=1,tempv},
num=Times@@(SnIrrepDim/@key[[1;;-1,2]]);
displist=disp/@key[[1;;-1,1]];
perms=Generateb/@key[[1;;-1,2]];
perms=MapThread[#2/.Cycles[x__]:>Cycles[x+#1]&,{displist,perms}];
tensordim=Length/@perms;
perms=pp/@Distribute[perms,List];
mrank=0;
While[mrank<num*multi&&i<=Length[tMBasis],
tempv=Flatten/@(SymBasis[tMBasis[[i]],Expand[#]]&/@perms);
tempv=GetCoord[qr,#]&/@tempv;
resultAux=Join[resultAux,tempv];
(*Assuming newly symmetrized basis either all independent with the existing ones or all live in the exsiting space*)
If[MatrixRank[resultAux]-mrank==Length[tempv],
mrank=MatrixRank[resultAux]; 
tempv=unflatten[Simplify[tempv],tdim];
AppendTo[result,tempv]];
i++;
];
result
]




(* ::Subsubsection::Closed:: *)
(*Integrated Functions*)


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

GetGroupFactor[model_,groupname_,type_,OptionsPattern[]]:=Module[{flist=CheckType[model,type],group=CheckGroup[groupname],
SUNreplist,repeatlist,nonsinglets,repeatnonsinglets,repeatsinglets,
displacements,indexlist,Irreplist,SNCollections,nonSingletSN,
fieldcombs,convertfactor,ruleLRRP,YDbasis,Mbasis,MbasisAll,tMbasis,tMbasisAll,vMbasis,vMbasisAll,
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
SNCollections=MapAt[DeleteCases[#,_->{1}]&,SNCollections,{All,1}];
nonSingletSN=MapAt[Select[#,model[#[[1]]][groupname]!=Singlet[group]&]&,SNCollections,{All,1}];(*Select out SN syms of nonsinglet repeated fields *)

fieldcombs=Join@@(GenerateLRInput/@nonsinglets);
convertfactor=Times@@(ConvertFactor[model,groupname,#]&/@flist);
ruleLRRP=Join@@(GenerateLRRP[groupname,#]&/@nonsinglets);(*Select out nonsinglet fields for constructing singlet*)
YDbasis=Expand[Flatten[((Times@@(tYDcol[group]@@@Transpose[#]))&/@Map[ToExpression,GenerateLRT[groupname,fieldcombs],{2}]/.ruleLRRP)]*convertfactor];
MbasisAll=SimpGFV2[TRefineTensor[YDbasis,model,groupname,flist]];
tMbasisAll=Product2ContractV2[#,indexlist,Symb2Num->tVal[group]]&/@MbasisAll;
vMbasisAll=Flatten/@tMbasisAll;
MapThread[Set,{{Mbasis,tMbasis,vMbasis},FindIndependentMbasis[MbasisAll,tMbasisAll,vMbasisAll]}];
If[MatrixRank[vMbasis]!=Length[vMbasis],Print["Warning: non-independent basis!!!!!"]];

Mbasis=Switch[OptionValue[OutputMode],
"working",Mbasis,
"tensor contract",Mbasis, (* needs implementation *)
"indexed",Mbasis/.GenerateReplacingRule[model,type],
"print",Mbasis/.GenerateReplacingRule[model,type]//RefineReplace];

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
PrintTensor=\!\(\*
TagBox[
StyleBox[
RowBox[{"\"\<\\!\\(\\*SubsuperscriptBox[\\(\>\"", "<>", "#tensor", "<>", "\"\<\\), \\(\>\"", "<>", "#downind", "<>", "\"\<\\), \\(\>\"", "<>", "#upind", "<>", "\"\<\\)]\\)\>\""}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)&;
Sortarg[asTlist_]:= #[y__] :> Signature[#[y]]Sort[#[y]]& /@ asTlist 
RefineReplace[x_]:=Module[{asTlist=Select[Keys@tOut,MatchQ[tSymmetry[#],_Antisymmetric]&]},
x/.Sortarg[asTlist]/.tOut]

IndexIterator[indlist_,indexct_]:=Module[{index=++indexct[indlist]},indlist[[index]]]
SetAttributes[IndexIterator,HoldRest];

(* Generate the replacing rule of the tensor indices for the final output form *)
GenerateReplacingRule[model_,type:(_Times|_Power)]:=GenerateReplacingRule[model,CheckType[model,type]]
GenerateReplacingRule[model_,flist_List]:=Module[{nonsingletlist,fexpand,symbollist,arglist,listind,listgen,indexct,indpair,listdummy},
nonsingletlist=AssociationMap[Function[groupname,Select[flist,Function[fname,model[fname[[1]]][groupname]!=Singlet[CheckGroup[groupname]]]]],Select[model[Gauge],nonAbelian]]; 
fexpand=Flatten[ConstantArray@@@#]&/@nonsingletlist;
symbollist=KeyValueMap[Function[fname,rep2ind[#1][model[fname[[1]]][#1]]]/@#2 &,nonsingletlist]; 
arglist=Map[Function[fname,Array[{fname[[1]],#,1}&,fname[[2]]]],nonsingletlist,{2}];
listind=Join@@MapThread[Function[{symbol,arg},symbol@@@arg],Catenate/@{symbollist,arglist}];

indexct=AssociationThread[Union@Catenate[rep2indOut]->0]; 
listgen=Join@@KeyValueMap[Function[{groupname,namelist},IndexIterator[rep2indOut[groupname][model[#][groupname]],indexct]&/@namelist],fexpand]; 
indpair=Join@@Values@Merge[{rep2ind,rep2indOut},Values[Merge[#,Identity]]& ]//DeleteDuplicates;
listdummy=Function[{ind,indexlist,ct},ind[ii_]:>indexlist[[ct+ii]]]@@@(Append[#,indexct[#[[2]]]]&/@indpair);
Return[Thread[listind->Flatten@listgen]~Join~listdummy];
]


(* Amplitude Formating *)


(* Lorentz Structure formating *)


(* ::Input::Initialization:: *)
(* Operator formating *)
SetAttributes[SetIndex,HoldAll]; 
Options[SetIndex]={FieldRename->{}};
Options[groupindex]={FieldRename->{}};
SetIndex[model_, field_, label_,indexct_,flavorct_,OptionsPattern[]] :=
Module[{hel=model[field][helicity],su2antiflag = False,irrep,group,indexList,index,tensorform}, 
tensorform=<|"tensor"->Replace[field,OptionValue[FieldRename]],"upind"->"","downind"->""|>;
If[model[field][nfl]>1, tensorform["downind"]= model[field][indfl][[++flavorct]];
tensorform["tensor"]=PrintTensor@tensorform;
tensorform["downind"]=""];
If[StringTake[field,-1] == "\[Dagger]", su2antiflag = True];
Do[irrep=model[field][groupname];
group=CheckGroup[model,groupname];
indexList=rep2indOut[groupname][irrep];
If[indexList=={},Continue[]]; (* singlet *)
index=IndexIterator[indexList,indexct];
If[Fund[group]==irrep,If[group==SU2&&su2antiflag,tensorform["upind"]=tensorform["upind"]<>index,tensorform["upind"]=tensorform["upind"]<>index],
tensorform["upind"]=tensorform["upind"]<>index],
{groupname,Select[model[Gauge],nonAbelian]}];
Subscript[h2f[hel], label] -> PrintTensor@tensorform
]
groupindex[model_, flistexpand_,OptionsPattern[]] := Module[{indexct,flavorct=0, n= Length[flistexpand]},
indexct=AssociationThread[Union@Catenate[rep2indOut]->0];
MapThread[SetIndex[model, #1, #2,indexct,flavorct,FieldRename->OptionValue[FieldRename]] & , {flistexpand,Range[n]}]
]
(*groupindex4com[model_, flistexpand_] := Module[{indexct,flcount = 0, n=Length[flistexpand]},
indexct=AssociationThread[Union@Catenate[rep2indOut]->0];
MapThread[SetIndex[model, #1, #2, indexct, flcount]& , {flistexpand, Range[n]}]
] 
*)
bilinear2com={ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(~\)]\),q_,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(~\)]\)],q_,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)],ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(~\)]\),q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)]],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(~\)]\)],q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)]],
ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(_\)]\),q_,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(_\)]\)],q_,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)],ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(_\)]\),q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)]],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(_\)]\)],q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)]],
ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(~\)]\),1,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(~\)]\)],1,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)],ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(~\)]\),1,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)]],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(~\)]\)],1,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)]],
ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(~\)]\),q_,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(~\)]\)],q_,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)],ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(~\)]\),q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)]],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(~\)]\)],q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(_\)]\)]],
ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(_\)]\),q_,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(_\)]\)],q_,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)],ch\[Psi][\!\(\*OverscriptBox[\(f1_\), \(_\)]\),q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)]],ch\[Psi][ch[p1__,\!\(\*OverscriptBox[\(f1_\), \(_\)]\)],q_,ch[p2__,\!\(\*OverscriptBox[\(f2_\), \(~\)]\)]]};
bilinear4com={ch\[Psi][f1_,"C",q,f2_],ch\[Psi][ch[p1__,f1_],"C",q_,f2_],ch\[Psi][f1_,"C",q_,ch[p2__,f2_]],ch\[Psi][ch[p1__,f1_],"C",q_,ch[p2__,f2_]],
ch\[Psi][f1_,q_,"C",f2_],ch\[Psi][ch[p1__,f1_],q_,"C",f2_],ch\[Psi][f1_,q_,"C",ch[p2__,f2_]],ch\[Psi][ch[p1__,f1_],q,"C",ch[p2__,f2_]],
ch\[Psi][f2_,1,f1_],ch\[Psi][f2_,1,ch[p1__,f1_]],ch\[Psi][ch[p2__,f2_],1,f1_],ch\[Psi][ch[p2__,f2_],1,ch[p1__,f1_]],
-ch\[Psi][f2_,q_,f1_],-ch\[Psi][f2_,q_,ch[p1__,f1_]],-ch\[Psi][ch[p2__,f2_],q_,f1_],-ch\[Psi][ch[p2__,f2_],q_,ch[p1__,f1_]],
ch\[Psi][f1_,q_,f2_],ch\[Psi][ch[p1__,f1_],q_,f2_],ch\[Psi][f1_,q_,ch[p2__,f2_]],ch\[Psi][ch[p1__,f1_],q_,ch[p2__,f2_]]};

transform[ope_, OptionsPattern[]] := Module[{Dcon, l2t, fieldlist, model, type, fer,spinor2to4},
If[OptionValue[Dcontract], Dcon = Flatten[{Dcontract1, Dcontract2}], Dcon = {}];
If[OptionValue[final], l2t = listtotime, l2t = {}];
If[OptionValue[ReplaceField] === {}, Return[ope //. Dcon //. l2t],
{model, type, fer} = OptionValue[ReplaceField];
fieldlist = CheckType[model,type,Counting->False]; 
spinor2to4=MapThread[RuleDelayed,{bilinear2com,bilinear4com/.x_Pattern:>x[[1]]}];
Switch[fer,
4,(* four-component fermions *)
ope //. {\[Sigma]^(a_) | OverBar[\[Sigma]]^(a_) :> \[Gamma]^a,Subscript[\[Sigma] |  OverBar[\[Sigma]], a_] :> Subscript[\[Gamma], a], Superscript[\[Sigma] | OverBar[\[Sigma]],a_] :> Superscript[\[Gamma], a]}//. {(a_)[(b_)[\[Gamma], a1_], b1_] :>a[b[\[Sigma], a1], b1]}
//. Dcon //. groupindex[model, fieldlist,FieldRename->Weyl2Dirac] /.spinor2to4//. l2t,
2,(* two-component fermions *)
ope //. Dcon //. groupindex[model, fieldlist] //. l2t]]
]
Options[transform] = {final -> True, Dcontract -> True, ReplaceField -> {}}; 

Oper[A_, n_, OptionsPattern[]] := transform[OperPoly[A, n, LorForm -> OptionValue[LorForm]],
final -> OptionValue[final], 
Dcontract -> OptionValue[Dcontract],
ReplaceField -> OptionValue[ReplaceField]]; 
Options[Oper] = {ReplaceField -> {}, LorForm -> True, Dcontract -> False, final -> True}; 

(* simplification when contracted with fields *)
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
W2Diagonalize[state_,k_,Ind_]:=
Module[{Num=Length[state],iniBasis=SSYT[state,k],stBasis=SSYT[state,k+2],
W2Basis,W2result,eigensys},
W2Basis=FindCor[stBasis]/@(reduce[Num]/@(Mandelstam[Ind]iniBasis));W2result=FindCor[stBasis]/@(reduce[Num]/@(W2[Ind]/@iniBasis));
eigensys=Transpose[LinearSolve[Transpose[W2Basis],#]&/@W2result]//Eigensystem;
<|"j"->eigensys[[1]],"transfer"->eigensys[[2]],"j-basis"->eigensys[[2]].iniBasis|>
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
Grassmann=FactorSyms[[1]]/.{Rule->(Rule[#1,Switch[model[#1][stat],"boson",{Total[#2]},"fermion",ConstantArray[1,Total[#2]]]]&)};
decompose=Thread/@Normal@Merge[Prepend[FactorSyms,Grassmann],GetCGCM]/.{(field_->yng_->CG_):>((field->yng)->CG[[All,All,1]])}; 
(* decompose Sn syms for each repeated fields *)
Thread[#,Rule]&/@Distribute[Flatten[Thread/@#]&/@decompose,List]
 (* flatten multiplicity of Sn decomposition, and list all combinations of syms for repeated fields *)
]

Options[DeSymmetrize]={RecMatrix->False,ColList->True};
DeSymmetrize[M_,rows_,OptionsPattern[]]:=Module[{len=Length[M],colList,N\[Lambda],iter,col\[Lambda]={},cols={}},
If[Det[M]==0,Print["[DeSymmetrize] incomplete basis"];Abort[]];
If[len==1,Return[{{1}}]];
If[TrueQ[OptionValue[ColList]],colList=Range[len],colList=OptionValue[ColList]];

Do[N\[Lambda]=Length[row\[Lambda]];
If[N\[Lambda]==len,AppendTo[cols,Range[len]];Break[]];
AppendTo[cols,Complement[Range[len],colList[[len+1-basisReduce[Reverse[M[[Complement[Range[len],row\[Lambda]]]]\[Transpose][[colList]]]]["pos"]]]]],
{row\[Lambda],rows}];
If[OptionValue[RecMatrix],Print[MapThread[Inverse[M[[#1,#2]]-M[[#1,Complement[Range[len],#2]]].Inverse[M[[Complement[Range[len],#1],Complement[Range[len],#2]]]].M[[Complement[Range[len],#1],#2]]]&,{rows,cols}]]];
Return[cols];
]

(* criterion: not ruled out by flavor sym *)
SQ[model_]:=Not@TrueQ[model[#1][nfl]<Length[#2]]&


(* ::Input::Initialization:: *)
Options[Type2TermsPro]={OutputFormat->"operator",FerCom->2,deSym->True,flavorTensor->True};
Type2TermsPro[model_,type_,OptionsPattern[]]:=Module[{flist,len,lorentzB,groupB,nFac,basisTotal,SymComb,terms,indexCG,indexFac,pairContraction,rows,cols},
flist=CheckType[model,type];
lorentzB=LorentzBasisForType[model,type,OutputFormat->OptionValue[OutputFormat],FerCom->OptionValue[FerCom],Coord->True];
len=Length[Keys[lorentzB[coord]][[1]]];(*num of repeated fields*)
groupB=(*Through[{GenerateSU3,GenerateSU2}[model,type]];*)GetGroupFactor[model,#,type,OutputMode->"indexed"]&/@Select[model[Gauge],nonAbelian];
nFac=Length[groupB]+1;(*number of factors to do Inner Product Decomposition for Sn groups*)

basisTotal=Flatten[lorentzB[basis]\[TensorProduct]Through[(TensorProduct@@groupB)["basis"]]];
If[OptionValue[OutputFormat]=="operator",basisTotal=ContractDelta/@basisTotal];
basisTotal=RefineReplace/@basisTotal;
If[len==0,Return[<|{}->basisTotal|>]];

SymComb=Distribute[Normal/@Prepend[Through[groupB["coord"]],lorentzB[coord]],List];(*list all syms combinations from factors*)
terms=Distribute[InnerDecomposeKey[model,#]&@Keys[#]->Distribute[Values[#],List],List]&/@SymComb//Flatten;(*perform IPD and expand multiplicities of basis and IPD*)
terms=Merge[terms/.{((sym_->CG_)->fac_):>sym->{CG,fac}},Identity];(*merge into association group by Sym*)

indexCG=Drop[Partition[Range[len (1+nFac)],1+nFac]//Transpose,1]//Flatten;
indexFac=len (1+nFac)+Drop[Range[nFac (len+1)],{len+1,-1,len+1}];
pairContraction=Transpose[{indexCG,indexFac}];(*find pairs to contract*)
terms=Map[Map[Flatten,TensorContract[TensorProduct@@Join@@#,pairContraction],{len}]&,terms,{2}];

If[OptionValue[deSym], (* whether to deSymmetrize to simpler form *)
rows=Prepend[Accumulate/@(Prepend[#,0]&/@Map[Length[Flatten[#,len-1]]&,Values[terms],{2}]),{1}];
Do[rows[[i+1]]+=rows[[i,-1]],{i,Length[terms]}];
rows=Drop[#,-1]&/@Drop[rows,1];
cols=DeSymmetrize[Apply[Join,Values[terms],{0,len}],rows];
terms=AssociationThread[Keys[terms]->(Part[basisTotal,#]&/@cols)] ,
(* full form *)
terms=Map[basisTotal.First[#]&,terms,{len+1}]
];

(* impose spin-stat: remove flavor syms not allowed by nflavor *)
terms=KeySelect[terms,And@@#/.Rule->SQ[model]&];
(* transform the key format *)
If[OptionValue[flavorTensor],terms=KeyMap[Select[Join[#,#->{1}&/@Cases[flist,{x_,1}:> x]],model[#[[1]]][nfl]!=1&]&,terms]];

Return[terms];
]

SnDecompose[replist_]:=Join@@MapThread[ConstantArray,{IntegerPartitions[Total@First@replist],DecomposeSnProduct[replist]}]
Type2TermsCount[model_,type_]:=Module[{len,lorentzB,groupB,nFac,SymComb,terms,pairContraction},
lorentzB=LorentzCountForType[model,type];
len=Length[Keys[lorentzB][[1]]]; (* num of repeated fields *)
groupB=CountGroupFactor[model,#,type]&/@Select[model[Gauge],nonAbelian];
nFac=Length[groupB]+1; (* number of factors to do Inner Product Decomposition for Sn groups *)
SymComb=Distribute[Normal/@Prepend[groupB,lorentzB],List];
terms=Join@@(ConstantArray[Merge[Keys[#],SnDecompose],Times@@Values[#]]&/@SymComb);
terms=Association[Rule@@@Tally[Join@@(Distribute[Thread/@Normal[#],List]&/@terms)]];
terms=KeyMap[Switch[model[#[[1]]][stat],"boson",#,"fermion",MapAt[TransposeYng,#,2]]&/@#&,terms]; (* impose spin-statistics to get flavor sym *)
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
n1=Times@@(model[#][nfl]&/@Cases[flist,{_String,1}][[All,1]]); (* single fields with S=nflavor *)
n2=Times@@@(KeyValueMap[HookContentFormula[#2,model[#1][nfl]]&,Association@@#]&/@Keys[terms]); (* repfields with non-trivial symmetry *)
n1*n2
]


(* ::Subsection:: *)
(*End of Package*)


(* ::Input::Initialization:: *)
(* Presented Indices *)
SU3ADJ=ToUpperCase/@Alphabet[][[1;;8]];
SU3FUND=Alphabet[];
SU2ADJ=ToUpperCase/@DeleteCases[Alphabet[][[9;;-1]],"l"];
SU2FUND=Alphabet[][[9;;-1]];
FLAVOR={"p"}\[Union]Alphabet[][[18;;-1]];


(* ::Input::Initialization:: *)
Weyl2Dirac=<| "Q" -> "q","Q\[Dagger]" -> OverBar["q"], "uc" -> OverBar["u"],"uc\[Dagger]"->"u", "dc" -> OverBar["d"],"dc\[Dagger]"->"d", "ec" -> OverBar["e"],"ec\[Dagger]"->"e", "L" -> "l", "L\[Dagger]" -> OverBar["l"]|>;


(* ::Input::Initialization:: *)
(* Define SMEFT *)
SetAttributes[DefSMEFT,HoldFirst];
DefSMEFT[model_,nf_:3]:=Module[{},
model=<|Global->{"Baryon","Lepton"}|>;rep2ind=<||>;rep2indOut=<||>;
AddGroup[model,"SU3c","G",{0,0},<|{0,0}->{Function[x,Nothing],{}},{1,0}->{b,SU3FUND},{0,1}->{b,SU3FUND},{1,1}->{B,SU3ADJ}|>];
AddGroup[model,"SU2w","W",{0,0},<|{0}->{Function[x,Nothing],{}},{1}->{a,SU2FUND},{2}->{A,SU2ADJ}|>];
AddGroup[model,"U1y","B",{0,0},<||>];
AddField[model,"Q",-1/2,{{1,0},{1},1/6},{1/3,0},Flavor->{nf,FLAVOR}];
AddField[model,"uc",-1/2,{{0,1},{0},-2/3},{-1/3,0},Flavor->{nf,FLAVOR}];
AddField[model,"dc",-1/2,{{0,1},{0},1/3},{-1/3,0},Flavor->{nf,FLAVOR}];
AddField[model,"L",-1/2,{{0,0},{1},-1/2},{0,1},Flavor->{nf,FLAVOR}];
AddField[model,"ec",-1/2,{{0,0},{0},1},{0,-1},Flavor->{nf,FLAVOR}];
AddField[model,"H",0,{{0,0},{1},1/2},{0,0}]
]


(* ::Input::Initialization:: *)
EndPackage[]
