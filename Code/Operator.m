(* ::Package:: *)

(* ::Input::Initialization:: *)
su2l=Append[StringJoin[#,"1"]&/@Alphabet["Greek"],StringJoin[#,"2"]&/@Alphabet["Greek"]]//Flatten;
su2r=Append[StringJoin[#,"1"]&/@Alphabet[],StringJoin[#,"2"]&/@Alphabet[]]//Flatten;
SetAttributes[{\[Psi]},Flat];\[Psi][a_*b_]:=\[Psi][a,b];
(* Change Amplitude to \[Psi]'s Combination *)
(* input all the angular bracket then obtain \[Psi]'s Combination *)
operab[a_]:=Module[{alist,oper=1,la},
If[a===1,oper=1,
alist=Prod2List[a];la=Length[alist];
Do[oper*=Subscript[h2f[-1/2], #1][2,su2l[[i]]]Subscript[h2f[-1/2], #2][1,su2l[[i]]]&@@alist[[i]],
{i,la}]];
Return[oper]
]
(* input all the square bracket then obtain Overscript[\[Psi], _]'s Combination *)
opersb[s_]:=Module[{slist,oper=1,ls},
If[s===1,oper=1,
slist=Prod2List[s];ls=Length[slist];
Do[oper*=Subscript[h2f[1/2], #1][1,su2r[[i]]]Subscript[h2f[1/2], #2][2,su2r[[i]]]&@@slist[[i]],
{i,ls}]];
Return[oper]
]
(* Change \[Psi]'sCombination to each particle *)
(* input arbitrary \[Psi] and Overscript[\[Psi], _], obtain Subscript[\[Phi], i],Subscript[\[Psi], i] or Subscript[F, i] and some D and \[Sigma]. i means the particle's label *)
change[\[Psi]i_,\[Psi]bi_,i_,Greek_]:=Module[{l\[Psi],l\[Psi]b,ans1=\[Psi]i,ans2=\[Psi]bi,ans=1,iGreek=Greek},
Switch[\[Psi]i[[0]],
Times,l\[Psi]=Length[\[Psi]i],
Integer,l\[Psi]=0,_,l\[Psi]=1];
Switch[\[Psi]bi[[0]],
Times,l\[Psi]b=Length[\[Psi]bi],
Integer,l\[Psi]b=0,_,l\[Psi]b=1];

Switch[l\[Psi]-l\[Psi]b,
0,Switch[l\[Psi],
0,ans=Subscript[\[Phi], i],
1,ans1[[0]]=\[Psi];ans2[[0]]=\[Psi];ans=\[Psi][ans1,ans2];ans[[0]]=("\[Sigma]"^su2l[[iGreek]]);ans=ans (Subscript[Subscript[D, i], su2l[[iGreek]]] Subscript[h2f[0], i]);iGreek++,
_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]]("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];ans=ans Subscript[h2f[0], i]
],

1,Switch[l\[Psi]b,
0,ans1[[0]]=Subscript[h2f[-1/2], i];ans=ans1,
1,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1,1]],ans1[[1,2]],ans2[[1]],ans2[[2]]] Subscript[Subscript[D, i], su2l[[iGreek]]]Subscript[h2f[-1/2], i][ans1[[2,1]],ans1[[2,2]]];iGreek++,
_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]]("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]b}];ans=ans Subscript[h2f[-1/2], i][ans1[[l\[Psi],1]],ans1[[l\[Psi],2]]]
],

-1,Switch[l\[Psi],
0,ans2[[0]]=Subscript[h2f[1/2], i];ans=ans2,
1,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]]]Subscript[Subscript[D, i], su2l[[iGreek]]]Subscript[h2f[1/2], i][ans2[[2,1]],ans2[[2,2]]];iGreek++,
_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]]("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];ans=ans Subscript[h2f[1/2], i][ans2[[l\[Psi]b,1]],ans2[[l\[Psi]b,2]]]
],

2,Switch[l\[Psi]b,
0,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1,1]],ans1[[1,2]],2,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[ans1[[2,1]],ans1[[2,2]],1,su2r[[iGreek]]] * Subscript[Subscript[Subscript[h2f[-1], i], su2l[[iGreek]]], su2l[[iGreek+1]]];
iGreek+=2,
1,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1,1]],ans1[[1,2]],ans2[[1]],ans2[[2]]] * Subscript[Subscript[D, i], su2l[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[ans1[[2,1]],ans1[[2,2]],2,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+2]])[ans1[[3,1]],ans1[[3,2]],1,su2r[[iGreek]]] * Subscript[Subscript[Subscript[h2f[-1], i], su2l[[iGreek+1]]], su2l[[iGreek+2]]];
iGreek+=3,
_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]b}];
ans=ans ("\[Sigma]"^su2l[[iGreek]])[ans1[[l\[Psi]-1,1]],ans1[[l\[Psi]-1,2]],2,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[ans1[[l\[Psi],1]],ans1[[l\[Psi],2]],1,su2r[[iGreek]]] * Subscript[Subscript[Subscript[h2f[-1], i], su2l[[iGreek]]], su2l[[iGreek+1]]];
iGreek+=2
],

-2,Switch[l\[Psi],
0,ans=("\[Sigma]"^su2l[[iGreek]])[2,su2l[[iGreek]],ans2[[1,1]],ans2[[1,2]]] * ("\[Sigma]"^su2l[[iGreek+1]])[1,su2l[[iGreek]],ans2[[2,1]],ans2[[2,2]]] * Subscript[Subscript[Subscript[h2f[1], i], su2l[[iGreek]]], su2l[[iGreek+1]]];
iGreek+=2,
1,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]]] * Subscript[Subscript[D, i], su2l[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[2,su2l[[iGreek]],ans2[[2,1]],ans2[[2,2]]] * ("\[Sigma]"^su2l[[iGreek+2]])[1,su2l[[iGreek]],ans2[[3,1]],ans2[[3,2]]] * Subscript[Subscript[Subscript[h2f[1], i], su2l[[iGreek+1]]], su2l[[iGreek+2]]];
iGreek+=3,
_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]]("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];
ans=ans ("\[Sigma]"^su2l[[iGreek]])[2,su2l[[iGreek]],ans2[[l\[Psi]b-1,1]],ans2[[l\[Psi]b-1,2]]] * ("\[Sigma]"^su2l[[iGreek+1]])[1,su2l[[iGreek]],ans2[[l\[Psi]b,1]],ans2[[l\[Psi]b,2]]] * Subscript[Subscript[Subscript[h2f[1], i], su2l[[iGreek]]], su2l[[iGreek+1]]];
iGreek+=2
],(**************** gravition *****************)

4,Switch[l\[Psi]b,
0,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1,1]],ans1[[1,2]],2,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[ans1[[2,1]],ans1[[2,2]],1,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+2]])[ans1[[3,1]],ans1[[3,2]],2,su2r[[iGreek+1]]] * ("\[Sigma]"^su2l[[iGreek+3]])[ans1[[4,1]],ans1[[4,2]],1,su2r[[iGreek+1]]] * Subscript[Subscript[Subscript[Subscript[Subscript[h2f[-2], i], su2l[[iGreek]]], su2l[[iGreek+1]]],su2l[[iGreek+2]]],su2l[[iGreek+3]]];
iGreek+=4,
1,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1,1]],ans1[[1,2]],ans2[[1]],ans2[[2]]] * Subscript[Subscript[D, i], su2l[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[ans1[[2,1]],ans1[[2,2]],2,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+2]])[ans1[[3,1]],ans1[[3,2]],1,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+3]])[ans1[[4,1]],ans1[[4,2]],2,su2r[[iGreek+1]]] * ("\[Sigma]"^su2l[[iGreek+4]])[ans1[[5,1]],ans1[[5,2]],1,su2r[[iGreek+1]]] * Subscript[Subscript[Subscript[Subscript[Subscript[h2f[-2], i], su2l[[iGreek+1]]], su2l[[iGreek+2]]],su2l[[iGreek+3]]],su2l[[iGreek+4]]];
iGreek+=5,

_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]b}];
ans=ans ("\[Sigma]"^su2l[[iGreek]])[ans1[[l\[Psi]-3,1]],ans1[[l\[Psi]-3,2]],2,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[ans1[[l\[Psi]-2,1]],ans1[[l\[Psi]-2,2]],1,su2r[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+2]])[ans1[[l\[Psi]-1,1]],ans1[[l\[Psi]-1,2]],2,su2r[[iGreek+1]]] * ("\[Sigma]"^su2l[[iGreek+3]])[ans1[[l\[Psi],1]],ans1[[l\[Psi],2]],1,su2r[[iGreek+1]]] * Subscript[Subscript[Subscript[Subscript[Subscript[h2f[-2], i], su2l[[iGreek]]], su2l[[iGreek+1]]],su2l[[iGreek+2]]],su2l[[iGreek+3]]];
iGreek+=4
],
-4,Switch[l\[Psi],
0,ans=("\[Sigma]"^su2l[[iGreek]])[2,su2l[[iGreek]],ans2[[1,1]],ans2[[1,2]]] * ("\[Sigma]"^su2l[[iGreek+1]])[1,su2l[[iGreek]],ans2[[2,1]],ans2[[2,2]]] * ("\[Sigma]"^su2l[[iGreek+2]])[2,su2l[[iGreek+1]],ans2[[3,1]],ans2[[3,2]]] * ("\[Sigma]"^su2l[[iGreek+3]])[1,su2l[[iGreek+1]],ans2[[4,1]],ans2[[4,2]]] * Subscript[Subscript[Subscript[Subscript[Subscript[h2f[2], i], su2l[[iGreek]]], su2l[[iGreek+1]]],su2l[[iGreek+2]]],su2l[[iGreek+3]]];
iGreek+=4,
1,ans=("\[Sigma]"^su2l[[iGreek]])[ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]]] * Subscript[Subscript[D, i], su2l[[iGreek]]] * ("\[Sigma]"^su2l[[iGreek+1]])[2,su2l[[iGreek]],ans2[[2,1]],ans2[[2,2]]] * ("\[Sigma]"^su2l[[iGreek+2]])[1,su2l[[iGreek]],ans2[[3,1]],ans2[[3,2]]] * ("\[Sigma]"^su2l[[iGreek+3]])[2,su2l[[iGreek+1]],ans2[[4,1]],ans2[[4,2]]] * ("\[Sigma]"^su2l[[iGreek+4]])[1,su2l[[iGreek+1]],ans2[[5,1]],ans2[[5,2]]] * Subscript[Subscript[Subscript[Subscript[Subscript[h2f[2], i], su2l[[iGreek+1]]], su2l[[iGreek+2]]],su2l[[iGreek+3]]],su2l[[iGreek+4]]];
iGreek+=5,
_,Do[ans=ans Subscript[Subscript[D, i], su2l[[iGreek]]]("\[Sigma]"^su2l[[iGreek]])[ans1[[a,1]],ans1[[a,2]],ans2[[a,1]],ans2[[a,2]]];iGreek++,{a,l\[Psi]}];
ans=ans ("\[Sigma]"^su2l[[iGreek]])[2,su2l[[iGreek]],ans2[[l\[Psi]b-3,1]],ans2[[l\[Psi]b-3,2]]] * ("\[Sigma]"^su2l[[iGreek+1]])[1,su2l[[iGreek]],ans2[[l\[Psi]b-2,1]],ans2[[l\[Psi]b-2,2]]] *  ("\[Sigma]"^su2l[[iGreek+2]])[2,su2l[[iGreek+1]],ans2[[l\[Psi]b-1,1]],ans2[[l\[Psi]b-1,2]]] * ("\[Sigma]"^su2l[[iGreek+3]])[1,su2l[[iGreek+1]],ans2[[l\[Psi]b,1]],ans2[[l\[Psi]b,2]]] * Subscript[Subscript[Subscript[Subscript[Subscript[h2f[2], i], su2l[[iGreek]]], su2l[[iGreek+1]]],su2l[[iGreek+2]]],su2l[[iGreek+3]]];
iGreek+=4
],

_,Print["spin over 2"]
];

Return[{ans,iGreek}]
]
changesp[\[Psi]i_,\[Psi]bi_,i_]:=Module[{l\[Psi],l\[Psi]b,ans1=\[Psi]i,ans2=\[Psi]bi,ans=1,head,label},
Switch[\[Psi]i[[0]],
Times,l\[Psi]=Length[\[Psi]i],
Integer,l\[Psi]=0,_,l\[Psi]=1];
Switch[\[Psi]bi[[0]],
Times,l\[Psi]b=Length[\[Psi]bi],
Integer,l\[Psi]b=0,_,l\[Psi]b=1];

Switch[l\[Psi]-l\[Psi]b,
0,Switch[l\[Psi],
0,ans=Subscript[h2f[0], i],
1,ans1[[0]]=\[Psi];ans2[[0]]=\[Psi];ans=\[Psi][ans1,ans2];ans[[0]]=ch[D, Subscript[h2f[0], i]],
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[h2f[0], i]]
],

1,Switch[l\[Psi]b,
0,ans1[[0]]=Subscript[h2f[-1/2], i];ans=ans1,
1,ans=ch[D,Subscript[h2f[-1/2], i]][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]],ans2[[1]],ans2[[2]]] ,
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi]b,Subscript[h2f[-1/2], i]]
],

-1,Switch[l\[Psi],
0,ans2[[0]]=Subscript[h2f[1/2], i];ans=ans2,
1,ans=ch[D,Subscript[h2f[1/2], i]][ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]]],
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[h2f[1/2], i]]
],

2,Switch[l\[Psi]b,
0,ans=Subscript[h2f[-1], i][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]]],
1,ans=ch[D,Subscript[h2f[-1], i]][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]],ans1[[3,1]],ans1[[3,2]],ans2[[1]],ans2[[2]]],
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi]b,Subscript[h2f[-1], i]]
],

-2,Switch[l\[Psi],
0,ans=Subscript[h2f[1], i][ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]]],
1,ans=ch[D,Subscript[h2f[1], i]][ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]],ans2[[3,1]],ans2[[3,2]]],
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[h2f[1], i]]
],
4,Switch[l\[Psi]b,
0,ans=Subscript[h2f[-2], i][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]],ans1[[3,1]],ans1[[3,2]],ans1[[4,1]],ans1[[4,2]]],
1,ans=ch[D,Subscript[h2f[-2], i]][ans1[[1,1]],ans1[[1,2]],ans1[[2,1]],ans1[[2,2]],ans1[[3,1]],ans1[[3,2]],ans1[[4,1]],ans1[[4,2]],ans1[[5,1]],ans1[[5,2]],ans2[[1]],ans2[[2]]],
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi]b,Subscript[h2f[-2], i]]
],

-4,Switch[l\[Psi],
0,ans=Subscript[h2f[2], i][ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]],ans2[[3,1]],ans2[[3,2]],ans2[[4,1]],ans2[[4,2]]],
1,ans=ch[D,Subscript[h2f[2], i]][ans1[[1]],ans1[[2]],ans2[[1,1]],ans2[[1,2]],ans2[[2,1]],ans2[[2,2]],ans2[[3,1]],ans2[[3,2]],ans2[[4,1]],ans2[[4,2]],ans2[[5,1]],ans2[[5,2]]],
_,ans1=\[Psi]@@@ans1;ans2=\[Psi]@@@ans2;ans=\[Psi]@@(ans1*ans2);ans[[0]]=ch[D^l\[Psi],Subscript[h2f[2], i]]
],

_,Print["spin over 2"]
];(*Print[ans];*)

head=ans[[0]];
If[head===Subscript,label=0;head=ans,label=Length[ans]/2];
Do[If[ans[[1]]===1,head=Subscript[head,ans[[2]]],head=Superscript[head,ans[[2]]]];ans=Delete[ans,{{1},{2}}],{ii,label}];
Return[head]
]


(* ::Input::Initialization:: *)
\[Sigma]change={"\[Sigma]"^a_:>"\[Sigma]"[a],Subscript["\[Sigma]", a_]:>"\[Sigma]"[a]};

bar[sign_]:=If[sign===1,{},{"\[Sigma]"->"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"}];
\[Sigma]2[a_,iGreek_]:={{Superscript["g",a[[1,1]] a[[2,1]]],-I},{1,"\[Sigma]"[a[[1,1]],a[[2,1]]]},{iGreek}}
(* where \[Sigma]^\[Mu]\[Nu]=(i/2)[\[Gamma]^\[Mu],\[Gamma]^\[Nu]]~(i/2)(\[Sigma]^\[Mu]Overscript[\[Sigma], _]^\[Nu]-\[Sigma]^\[Nu]Overscript[\[Sigma], _]^\[Mu]) *)
\[Sigma]3[a_,iGreek_,sign_:1]:=Module[{e=DeleteCases[su2l,"\[Sigma]"][[iGreek]]},
{{Superscript["g",a[[1,1]] a[[2,1]]],-Superscript["g",a[[1,1]] a[[3,1]]],Superscript["g",a[[2,1]] a[[3,1]]],I sign Signature[{a[[1,1]],a[[2,1]],a[[3,1]],e}]Superscript["\[Epsilon]",a[[1,1]]a[[2,1]]a[[3,1]]e]},{"\[Sigma]"[a[[3,1]]],"\[Sigma]"[a[[2,1]]],"\[Sigma]"[a[[1,1]]],"\[Sigma]"[e]},{iGreek+1}}
]
(* a is the \[Sigma] chain, such as {\[Sigma]^\[Mu],\[Sigma]^\[Nu],...}.iGreek determines the new \[Sigma] matrix's index. sign determines the first \[Sigma] in \[Sigma] chain is \[Sigma] or Overscript[\[Sigma], _],correspond to 1 and -1 *)
\[Sigma]chain[a_,iGreek_,sign_:1]:=Module[{l=Length[a],ans=a//.\[Sigma]change,n,term1,input,output=0},
Switch[l,
0,term1={{1},{1},{iGreek}},
1,term1={{1},{"\[Sigma]"[a[[1,2]]]},{iGreek}}/.bar[sign],
2,term1=\[Sigma]2[ans,iGreek]/.bar[sign],
_,n=Quotient[l,2];term1=\[Sigma]3[ans[[1;;3]],iGreek,sign];
Do[If[i===n&&n===(l/2),input=Flatten/@(Append[#,ans[[2i]]]&/@List/@term1[[2]]);output=\[Sigma]2[#,term1[[3,1]]]&/@input,
input=Flatten/@(Append[#,ans[[2i;;2i+1]]]&/@List/@term1[[2]]);output=\[Sigma]3[#,term1[[3,1]],sign]&/@input];
term1[[3]]=output[[1,3]];
term1[[2]]=Flatten[output[[All,2]]];
term1[[1]]=MapThread[Times[#1,#2]&,{term1[[1]],output[[All,1]]}]//Flatten,
{i,2,n}];
term1=term1/.bar[sign]
];
Return[term1]
]


(* ::Input::Initialization:: *)
Chain[x__]:=Module[{c={x}},If[Length[c]>1,HoldForm[Times[x]],HoldForm[x]]];
\[Sigma]trace={"\[Sigma]"[i_,j_]:>0,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[i_,j_]:>0};
(* when calculating the \[Sigma] trace, we make use of \[Sigma]chain[], and set all the \[Sigma] matrix remained go to zero *)
trace[\[Sigma]_,iGreek_:1,sign_:1]:=Module[{l=Length[\[Sigma]],T},Switch[l,_?OddQ,T={0,iGreek},_,T=\[Sigma]chain[\[Sigma],iGreek,sign]//.\[Sigma]trace;T={2T[[1]].T[[2]],T[[3,1]]}];T];
(* Simplify two epsilon tensor. x,y express the indices of two epsilon *)
epsilon2[x_,y_]:=Module[{x1,y1,sign},y1=Permutations[y];x1=ConstantArray[x,Length[y1]];sign=Signature[#]&/@y1;-Times@@@(MapThread[Superscript["g",#1 #2]&,{x1,y1},2]).sign];
(* contract the repeated index, disappear g *)
contract={MapThread[Superscript["g",i_ j_]#1:>#2/;Signature[{i,j}]>0&,{{Subscript[Subscript[D, a_], j_],Subscript[Subscript[Subscript[h2f[-1], a_], j_], q_],Subscript[Subscript[Subscript[h2f[-1], a_], q_], j_],Subscript[Subscript[Subscript[h2f[1], a_], j_], q_],Subscript[Subscript[Subscript[h2f[1], a_], q_], j_],ch\[Psi][p_,"\[Sigma]"[j_],q_],ch\[Psi][p_,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[j_],q_],ch\[Psi][p_,"\[Sigma]"[j_,q1_],q_],ch\[Psi][p_,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[j_,q1_],q_],ch\[Psi][p_,"\[Sigma]"[q1_,j_],q_],ch\[Psi][p_,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[q1_,j_],q_],Subscript[Subscript[Subscript[Subscript[CL_, j_], a_],b_],c_],Subscript[Subscript[Subscript[Subscript[CL_, a_], j_],b_],c_],Subscript[Subscript[Subscript[Subscript[CL_, a_], b_],j_],c_],Subscript[Subscript[Subscript[Subscript[CL_, a_], b_],c_],j_]},{Subscript[Subscript[D, a], i],Subscript[Subscript[Subscript[h2f[-1], a], i], q],Subscript[Subscript[Subscript[h2f[-1], a], q], i],Subscript[Subscript[Subscript[h2f[1], a], i], q],Subscript[Subscript[Subscript[h2f[1], a], q], i],ch\[Psi][p,"\[Sigma]"[i],q],ch\[Psi][p,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[i],q],ch\[Psi][p,"\[Sigma]"[i,q1],q],ch\[Psi][p,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[i,q1],q],ch\[Psi][p,"\[Sigma]"[q1,i],q],ch\[Psi][p,
"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[q1,i],q],Subscript[Subscript[Subscript[Subscript[CL, i], a],b],c],Subscript[Subscript[Subscript[Subscript[CL, a], i],b],c],Subscript[Subscript[Subscript[Subscript[CL, a], b],i],c],Subscript[Subscript[Subscript[Subscript[CL, a], b],c],i]}}],Superscript["g",i_ j_]Superscript["\[Epsilon]",j_ k_ l_ m_]:>Signature[{i,k,l,m}] Signature[{j,k,l,m}] Superscript["\[Epsilon]",i k l m],Subscript[Subscript[Subscript[h2f[-1], k_], i_], j_]Superscript["\[Epsilon]",i_ j_ a_ b_]:>2I Subscript[Subscript[Subscript[h2f[-1], k], a], b]Signature[{i,j,a,b}],Subscript[Subscript[Subscript[h2f[1], k_], i_], j_]Superscript["\[Epsilon]",i_ j_ a_ b_]:>-2I Subscript[Subscript[Subscript[h2f[1], k], a], b]Signature[{i,j,a,b}],Superscript["\[Epsilon]",i1_ j1_ k1_ l1_]Superscript["\[Epsilon]",i2_ j2_ k2_ l2_]:>epsilon2[{i1,j1,k1,l1},{i2,j2,k2,l2}],Superscript["g",i_ j_]Superscript["g",i_ k_]:>Superscript["g",j k],Superscript["g",i_ i_]:>4,Superscript["g",i_ j_]Superscript["g",i_ j_]:>4}//Flatten;(* let Subscript[F, label] or Subscript[Overscript[F, _], label] absorb redundant epsilon *)Ftilde[iGreek_]:={Subscript[Subscript[Subscript[h2f[-1], label_], i_], j_]Superscript["\[Epsilon]",a_ b_ c_ d_]:>-I/2 Subscript[Subscript[Subscript[h2f[-1], label], su2l[[iGreek]]], su2l[[iGreek+1]]]epsilon2[{i,j,su2l[[iGreek]],su2l[[iGreek+1]]},{a,b,c,d}],Subscript[Subscript[Subscript[h2f[1], label_], i_], j_]Superscript["\[Epsilon]",a_ b_ c_ d_]:>I/2 Subscript[Subscript[Subscript[h2f[1], label], su2l[[iGreek]]], su2l[[iGreek+1]]]epsilon2[{i,j,su2l[[iGreek]],su2l[[iGreek+1]]},{a,b,c,d}],
(*spin2*)Subscript[Subscript[Subscript[Subscript[Subscript[h2f[-2], label_], i_], j_],k_],l_]Superscript["\[Epsilon]",a_ b_ c_ d_]:>-I/2 Subscript[Subscript[Subscript[Subscript[Subscript[h2f[-2], label], su2l[[iGreek]]], su2l[[iGreek+1]]],k],l]epsilon2[{i,j,su2l[[iGreek]],su2l[[iGreek+1]]},{a,b,c,d}],Subscript[Subscript[Subscript[Subscript[Subscript[h2f[2], label_], i_], j_],k_],l_]Superscript["\[Epsilon]",a_ b_ c_ d_]:>I/2 Subscript[Subscript[Subscript[Subscript[Subscript[h2f[2], label], su2l[[iGreek]]], su2l[[iGreek+1]]],k],l]epsilon2[{i,j,su2l[[iGreek]],su2l[[iGreek+1]]},{a,b,c,d}]};
(* redefine the index *)
beforeform={Subscript[Subscript[D, i_], j_]:>Subscript[D, i][j],Subscript[D, i_][j_]^2:>0,Subscript[D, i_][j_]ch\[Psi][q_,"\[Sigma]"[j_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[j_],Subscript[f_, i_]]:>0,Subscript[D, i_][j_]ch\[Psi][Subscript[f_, i_],"\[Sigma]"[j_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[j_],q_]:>0,Subscript[D, i_][\[Nu]_]ch\[Psi][q_,"\[Sigma]"[\[Mu]_,\[Nu]_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[\[Mu]_,\[Nu]_],Subscript[f_, i_]]:>-I Subscript[D, i][\[Mu]] ch\[Psi][q,1,Subscript[f, i]],Subscript[D, i_][\[Mu]_]ch\[Psi][q_,"\[Sigma]"[\[Mu]_,\[Nu]_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[\[Mu]_,\[Nu]_],Subscript[f_, i_]]:>I Subscript[D, i][\[Nu]] ch\[Psi][q,1,Subscript[f, i]],Subscript[D, i_][\[Mu]_]ch\[Psi][Subscript[q_, i_],"\[Sigma]"[\[Mu]_,\[Nu]_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[\[Mu]_,\[Nu]_],f_]:>-I Subscript[D, i][\[Nu]] ch\[Psi][Subscript[q, i],1,f],Subscript[D, i_][\[Nu]_]ch\[Psi][Subscript[q_, i_],"\[Sigma]"[\[Mu]_,\[Nu]_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[\[Mu]_,\[Nu]_],f_]:>I Subscript[D, i][\[Mu]] ch\[Psi][Subscript[q, i],1,f],Subscript[Subscript[Subscript[h2f[-1], i_], j_], k_]:>Subscript[h2f[-1], i][j,k],(Subscript[h2f[-1], i_][j_,j_]|Subscript[h2f[1], i_][j_,j_]):>0,Subscript[Subscript[Subscript[h2f[1], i_], j_], k_]:>Subscript[h2f[1], i][j,k],Subscript[h2f[-1], i_][\[Mu]_,\[Nu]_](Subscript[h2f[1], j_][\[Mu]_,\[Nu]_]|Subscript[h2f[1], j_][\[Nu]_,\[Mu]_]):>0,Subscript[D, i_][j_](Subscript[h2f[-1], i_][j_,k_]|Subscript[h2f[1], i_][j_,k_]|Subscript[h2f[-1], i_][k_,j_]|Subscript[h2f[1], i_][k_,j_]):>0,Superscript["\[Epsilon]",i_ j_ k_ l_]:>"\[Epsilon]"[i,j,k,l],
(* spin2 *)Subscript[Subscript[Subscript[Subscript[CL_,i_], j_], k_],l_]:>CL[i,j,k,l],(CL_[i_,i_,j_,k_]|CL_[i_,j_,i_,k_]|CL_[i_,j_,k_,i_]|CL_[i_,j_,j_,k_]|CL_[i_,j_,k_,j_]|CL_[i_,j_,k_,k_]):>0,
Subscript[h2f[-1], i_][\[Mu]_,\[Nu]_](Subscript[h2f[2], j_][\[Mu]_,\[Nu]_,\[Sigma]_,\[Delta]_]|Subscript[h2f[2], j_][\[Nu]_,\[Mu]_,\[Sigma]_,\[Delta]_]|Subscript[h2f[2], j_][\[Sigma]_,\[Delta]_,\[Mu]_,\[Nu]_]|Subscript[h2f[2], j_][\[Sigma]_,\[Delta]_,\[Nu]_,\[Mu]_]):>0,
Subscript[h2f[1], i_][\[Mu]_,\[Nu]_](Subscript[h2f[-2], j_][\[Mu]_,\[Nu]_,\[Sigma]_,\[Delta]_]|Subscript[h2f[-2], j_][\[Nu]_,\[Mu]_,\[Sigma]_,\[Delta]_]|Subscript[h2f[-2], j_][\[Sigma]_,\[Delta]_,\[Mu]_,\[Nu]_]|Subscript[h2f[-2], j_][\[Sigma]_,\[Delta]_,\[Nu]_,\[Mu]_]):>0,(Subscript[h2f[-2], i_][\[Mu]_,\[Nu]_,\[Lambda]_,\[Rho]_]|Subscript[h2f[-2], i_][\[Lambda]_,\[Rho]_,\[Mu]_,\[Nu]_])(Subscript[h2f[2], j_][\[Mu]_,\[Nu]_,\[Sigma]_,\[Delta]_]|Subscript[h2f[2], j_][\[Nu]_,\[Mu]_,\[Sigma]_,\[Delta]_]|Subscript[h2f[2], j_][\[Sigma]_,\[Delta]_,\[Mu]_,\[Nu]_]|Subscript[h2f[2], j_][\[Sigma]_,\[Delta]_,\[Nu]_,\[Mu]_]):>0};
(* distribute all D to each field *)
Dcontract1={MapThread[MapThread[{Subscript[Subscript[D, i_], j_]#1:>#2,Superscript[Subscript[D, i_],j_]#1:>#3}&,{{#1,ch[p__,#1]},{ch[Subscript[D, j],#2],ch[p,Subscript[D, j],#2]},{ch[Superscript[D,j],#2],ch[p,Superscript[D,j],#2]}}]&,{{Subscript[h2f[0], i_],Subscript[h2f[-1], i_][q__],Subscript[h2f[1], i_][q__],Subscript[h2f[-2], i_][q__],Subscript[h2f[2], i_][q__]},{Subscript[h2f[0], i],Subscript[h2f[-1], i][q],Subscript[h2f[1], i][q],Subscript[h2f[-2], i][q],Subscript[h2f[2], i][q]}}]}//Flatten;
Dcontract2={MapThread[MapThread[{Subscript[Subscript[D, i_], j_] #1:>#2,Superscript[Subscript[D, i_],j_] #1:>#3}&,{{ch\[Psi][#1,q__],ch\[Psi][ch[p__,#1],q__]},{ch\[Psi][ch[Subscript[D, j],#2],q],ch\[Psi][ch[p,Subscript[D, j],#2],q]},{ch\[Psi][ch[Superscript[D,j],#2],q],ch\[Psi][ch[p,Superscript[D,j],#2],q]}}]&,{{Subscript[h2f[-1/2], i_],Subscript[h2f[1/2], i_]},{Subscript[h2f[-1/2], i],Subscript[h2f[1/2], i]}}],MapThread[MapThread[{Subscript[Subscript[D, i_], j_] #1:>#2,Superscript[Subscript[D, i_],j_] #1:>#3}&,{{ch\[Psi][q__,#1],ch\[Psi][q__,ch[p__,#1]]},{ch\[Psi][q,ch[Subscript[D, j],#2]],ch\[Psi][q,ch[p,Subscript[D, j],#2]]},{ch\[Psi][q,ch[Superscript[D,j],#2]],ch\[Psi][q,ch[p,Superscript[D,j],#2]]}}]&,{{Subscript[h2f[-1/2], i_],Subscript[h2f[1/2], i_]},{Subscript[h2f[-1/2], i],Subscript[h2f[1/2], i]}}]}//Flatten;
(* change tensor index into TensorContract, and get back *)
(* define the antisym tensor and vector *)
antisym[a_]:={a\[Element]Matrices[{4,4},Reals,Antisymmetric[{1,2}]]};Csym[a_]:={a\[Element]Arrays[{4,4,4,4},Reals,{Antisymmetric[{1,2}],Antisymmetric[{3,4}],{Cycles[{{1,3},{2,4}}],1}}]};
sym[v_]:={v\[Element]Arrays[{4}]};


(* ::Input::Initialization:: *)
(* change tensor into TensorContract *)
tensorform[o_]:=Module[{lo=Length[o],tensor={},tensor1,tensor2,tensor3,index={},P,cont={},other=o},
Do[
Switch[o[[i,0]],
Subscript[h2f[-1], _],other/=o[[i]];
tensor=Append[tensor,F[o[[i,0,2]]]];
index=Append[index,{o[[i,1]],o[[i,2]]}],Subscript[h2f[1], _],other/=o[[i]];
tensor=Append[tensor,F[o[[i,0,2]],"b"]];
index=Append[index,{o[[i,1]],o[[i,2]]}],

Subscript[D, _],other/=o[[i]];
tensor=Append[tensor,de[o[[i,0,2]]]];
index=Append[index,o[[i,1]]],

ch\[Psi],Switch[Length[o[[i,2]]],
0,Continue[],
1,other/=o[[i]];
tensor=Append[tensor,sigma[o[[i,1]],o[[i,3]]]];
index=Append[index,o[[i,2,1]]],2,other/=o[[i]];
tensor=Append[tensor,sigma2[o[[i,1]],o[[i,3]]]];
index=Append[index,{o[[i,2,1]],o[[i,2,2]]}]
],

"\[Epsilon]",other/=o[[i]];
tensor=Append[tensor,epsilon];
index=Append[index,{o[[i,1]],o[[i,2]],o[[i,3]],o[[i,4]]}],
(******spin2*******)
Subscript[h2f[-2], _],other/=o[[i]];
tensor=Append[tensor,CL[o[[i,0,2]]]];
index=Append[index,{o[[i,1]],o[[i,2]],o[[i,3]],o[[i,4]]}],Subscript[h2f[2], _],other/=o[[i]];
tensor=Append[tensor,CL[o[[i,0,2]],"b"]];
index=Append[index,{o[[i,1]],o[[i,2]],o[[i,3]],o[[i,4]]}]
],{i,lo}];

index=index//Flatten;
Do[P=Position[index,index[[i]]]//Flatten;
If[P[[2]]===i,Continue[]];
cont=Append[cont,P],
{i,Length[index]}];

tensor1=Union[Cases[tensor,_sigma],Cases[tensor,_de]];
tensor2=Union[Cases[tensor,_F],Cases[tensor,_sigma2]];
tensor3=Cases[tensor,_CL];
tensor=TensorContract[TensorProduct@@tensor,cont]other;

Return[{tensor,tensor1,tensor2,tensor3,index,cont,other}]
]

(* change TensorContract into tensor index form *)
tensortooper[t_]:=
Module[{factors,other,index,tensorterm,iGreek=0,indexnum,indexposition,si},If[t[[0]]===TensorProduct,Return[0]];
factors=GroupBy[Prod2List[t],MatchQ[_TensorContract]];
If[KeyExistsQ[factors,True],tensorterm=factors[True],Return[t]];
If[KeyExistsQ[factors,False],other=Times@@factors[False],other=1];

(*Do[indexnum=1;index=indexposition=ConstantArray["down",2Length[term[[2]]]];
Do[index[[term[[2,i,1]]]]=index[[term[[2,i,2]]]]=LorentzIndex[[i+iGreek]],{i,Length[term[[2]]]}];iGreek+=Length[term[[2]]];
Do[Switch[ten,
epsilon,other*=Signature[{index[[indexnum]],index[[indexnum+1]],index[[indexnum+2]],index[[indexnum+3]]}]Superscript["\[Epsilon]",index[[indexnum]]index[[indexnum+1]]index[[indexnum+2]]index[[indexnum+3]]];indexnum+=4,
_de,If[indexposition[[indexnum]]==="up",
other*=Superscript[Subscript[D, ten[[1]]],index[[indexnum]]],
other*=Subscript[Subscript[D, ten[[1]]], index[[indexnum]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up"];indexnum++,
_F,If[Length[ten]===1,si=h2f[-1],si=h2f[1]];other*=Subscript[si, ten[[1]]][indexposition[[indexnum]],index[[indexnum]],indexposition[[indexnum+1]],index[[indexnum+1]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up";indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up";indexnum+=2,
_sigma,Switch[ten[[1]],
Subscript[h2f[-1/2], _],si="\[Sigma]",
Subscript[h2f[1/2], _],si="\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"];
If[indexposition[[indexnum]]==="up",
other*=ch\[Psi][ten[[1]],si^index[[indexnum]],ten[[2]]],
other*=ch\[Psi][ten[[1]],Subscript[si, index[[indexnum]]],ten[[2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up"];indexnum++,
_sigma2,Switch[ten[[1]],
Subscript[h2f[-1/2], _],si="\[Sigma]",
Subscript[h2f[1/2], _],si="\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"];Switch[indexposition[[indexnum;;indexnum+1]],
{"up","up"},other*=ch\[Psi][ten[[1]],Superscript[Superscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]],
{"up","down"},other*=ch\[Psi][ten[[1]],Subscript[Superscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]];indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up",
{"down","up"},other*=ch\[Psi][ten[[1]],Superscript[Subscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up",
{"down","down"},other*=ch\[Psi][ten[[1]],Subscript[Subscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]=indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up"];indexnum+=2,
_,Print["some thing are ignored"]],
{ten,List@@term[[1]]}],
{term,tensorterm}];*)

Do[indexnum=1;index=indexposition=ConstantArray["down",2Length[term[[2]]]];
Do[index[[term[[2,i,1]]]]=index[[term[[2,i,2]]]]=LorentzIndex[[i+iGreek]],{i,Length[term[[2]]]}];iGreek+=Length[term[[2]]];
Do[Switch[ten,
epsilon,other*=Signature[{index[[indexnum]],index[[indexnum+1]],index[[indexnum+2]],index[[indexnum+3]]}]Superscript["\[Epsilon]",index[[indexnum]]index[[indexnum+1]]index[[indexnum+2]]index[[indexnum+3]]];indexnum+=4,
_de,If[indexposition[[indexnum]]==="up",
other*=Superscript[Subscript[D, ten[[1]]],index[[indexnum]]],
other*=Subscript[Subscript[D, ten[[1]]], index[[indexnum]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up"];indexnum++,
_F,If[Length[ten]===1,si=h2f[-1],si=h2f[1]];other*=Subscript[si, ten[[1]]][indexposition[[indexnum]],index[[indexnum]],indexposition[[indexnum+1]],index[[indexnum+1]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up";indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up";indexnum+=2,
(*************spin2************)
_CL,If[Length[ten]===1,si=h2f[-2],si=h2f[2]];other*=Subscript[si, ten[[1]]][indexposition[[indexnum]],index[[indexnum]],indexposition[[indexnum+1]],index[[indexnum+1]],indexposition[[indexnum+2]],index[[indexnum+2]],indexposition[[indexnum+3]],index[[indexnum+3]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up";indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up";indexposition[[(Position[index,index[[indexnum+2]]]//Flatten)[[2]]]]="up";indexposition[[(Position[index,index[[indexnum+3]]]//Flatten)[[2]]]]="up";indexnum+=4,
_sigma,Switch[ten[[1]],
Subscript[h2f[-1/2], _],si="\[Sigma]",
Subscript[h2f[1/2], _],si="\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"];
If[indexposition[[indexnum]]==="up",
other*=ch\[Psi][ten[[1]],si^index[[indexnum]],ten[[2]]],
other*=ch\[Psi][ten[[1]],Subscript[si, index[[indexnum]]],ten[[2]]];indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up"];indexnum++,
_sigma2,Switch[ten[[1]],
Subscript[h2f[-1/2], _],si="\[Sigma]",
Subscript[h2f[1/2], _],si="\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"];
Switch[indexposition[[indexnum;;indexnum+1]],
{"up","up"},other*=ch\[Psi][ten[[1]],Superscript[Superscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]],
{"up","down"},other*=ch\[Psi][ten[[1]],Subscript[Superscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]];
indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up",
{"down","up"},other*=ch\[Psi][ten[[1]],Superscript[Subscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]];
indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up",
{"down","down"},other*=ch\[Psi][ten[[1]],Subscript[Subscript[si,index[[indexnum]]],index[[indexnum+1]]],ten[[2]]];
	indexposition[[(Position[index,index[[indexnum]]]//Flatten)[[2]]]]="up";
	indexposition[[(Position[index,index[[indexnum+1]]]//Flatten)[[2]]]]="up"];
indexnum+=2,
_,Print["some thing are ignored"]],
{ten,List@@term[[1]]}],
{term,tensorterm}];

Return[other]
]
part4[m_]:=If[Length[m]>=4,m[[4]],0];


(* ::Input::Initialization:: *)
(* deal with monomial amplitude, input respectively angular brackets and square brackets and particle number *)
OperMonoResp[a_:1,s_:1,n_]:=Module[{opA,opS,\[Psi]i=Table[1,{i,n},{j,2}],op=1,lop,index,opi,iGreek=11,coef,chain={},chainnum={},indexa,index\[Alpha],lchain,\[Sigma]m,oper},
opA=operab[a];
opS=opersb[s];
Do[\[Psi]i[[i,1]]=Cases[opA,Subscript[h2f[-1/2], i][_Integer,_]];
\[Psi]i[[i,1,0]]=Times;
\[Psi]i[[i,2]]=Cases[opS,Subscript[h2f[1/2], i][_Integer,_]];
\[Psi]i[[i,2,0]]=Times,{i,n}];
Do[opi=change [\[Psi]i[[i,1]],\[Psi]i[[i,2]],i,iGreek];
op=op opi[[1]];
iGreek=opi[[2]],{i,n}];
op[[0]]=List;(*Print["op=",op];*)
opS=Cases[op,Subscript[Subscript[Subscript[h2f[-1], _], _], _]]\[Union]Cases[op,Subscript[Subscript[Subscript[h2f[1], _], _], _]];
coef=1/2^Length[Cases[op,Subscript[Subscript[Subscript[h2f[-1], _], _], _]|Subscript[Subscript[Subscript[h2f[1], _], _],_]]]*1/4^Length[Cases[op,Subscript[Subscript[Subscript[Subscript[_,_], _], _], _]]]*I^Length[Cases[op,Subscript[Subscript[D, _], _]]];
opA=Cases[op,Power["\[Sigma]",_][__]|Subscript[\[Psi], _][__]|Subscript[
\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\), _][__]];
opS=Complement[op,opA];(*Print["opS=",opS];Print["opA=",opA];Print["coef=",coef];*)
lop=Length[opA];
Do[Switch[opA[[i,0]],
Subscript[h2f[-1/2], _],
If[Cases[chain,opA[[i,0]]]!={},Continue[]];
index=opA[[i,2]];
If[opA[[i,1]]===1,coef=-coef];
chain=Append[chain,opA[[i,0]]];
index\[Alpha]=Select[opA,#[[2]]==index&];
index\[Alpha]=Complement[index\[Alpha],{opA[[i]]}];
Do[If[index\[Alpha][[1,0,1]]==="\[Sigma]",index=index\[Alpha][[1,4]];
chain=Append[chain,index\[Alpha][[1,0]]];
If[index\[Alpha][[1,3]]===2,coef=-coef];
indexa=Select[opA,part4[#]==index&];
indexa=Complement[indexa,index\[Alpha]];
If[indexa==={},
indexa=Select[opA,#[[2]]==index&];
chain=Append[chain,indexa[[1,0]]];
chainnum=Append[chainnum,Length[chain]];
Break[]];
If[indexa[[1,1]]===1,coef=-coef];
index=indexa[[1,2]];
index\[Alpha]=Select[opA,#[[2]]==index&];
index\[Alpha]=Complement[index\[Alpha],indexa];
chain=Append[chain,indexa[[1,0]]],
chain=Append[chain,index\[Alpha][[1,0]]];
chainnum=Append[chainnum,Length[chain]];
Break[]],
{j,lop}],

Subscript[h2f[1/2], _],
If[Cases[chain,opA[[i,0]]]!={},Continue[]];
index=opA[[i,2]];
If[opA[[i,1]]===2,coef=-coef];
chain=Append[chain,opA[[i,0]]];
indexa=Select[opA,part4[#]==index&];
indexa=Complement[indexa,{opA[[i]]}];
Do[If[indexa==={},indexa=Select[opA,#[[2]]==index&];
indexa=Complement[indexa,{opA[[i]]}];
chain=Append[chain,indexa[[1,0]]];
chainnum=Append[chainnum,Length[chain]];
Break[]];
index=indexa[[1,2]];
If[indexa[[1,1]]===1,coef=-coef];
index\[Alpha]=Select[opA,#[[2]]==index&];
index\[Alpha]=Complement[index\[Alpha],indexa];
chain=Append[chain,indexa[[1,0]]];
If[index\[Alpha][[1,0,1]]==="\[Sigma]",If[index\[Alpha][[1,3]]===2,coef=-coef];
index=index\[Alpha][[1,4]];
indexa=Select[opA,part4[#]==index&];
indexa=Complement[indexa,index\[Alpha]];
chain=Append[chain,index\[Alpha][[1,0]]],
chainnum=Append[chainnum,Length[chain]];
chain=Append[chain,index\[Alpha][[1,0]]];
Break[]],
{j,lop}]],
{i,lop}](*after all the \[Psi] chains are found*);

If[Length[opA]>Length[chain],
Do[If[opA[[i,0,1]]==="\[Sigma]",If[Cases[chain,opA[[i,0]]]!={},Continue[]];
index=opA[[i,4]];
If[opA[[i,3]]===2,coef=-coef];
chain=Append[chain,opA[[i,0]]];
indexa=Select[opA,part4[#]==index&];
indexa=Complement[indexa,{opA[[i]]}];
Do[index=indexa[[1,2]];
If[indexa[[1,1]]===1,coef=-coef];
index\[Alpha]=Select[opA,#[[2]]==index&];
index\[Alpha]=Complement[index\[Alpha],indexa];
chain=Append[chain,indexa[[1,0]]];
If[Cases[chain,index\[Alpha][[1,0]]]!={},chainnum=Append[chainnum,Length[chain]];Break[]];
chain=Append[chain,index\[Alpha][[1,0]]];
index=index\[Alpha][[1,4]];
If[index\[Alpha][[1,3]]===2,coef=-coef];
indexa=Select[opA,part4[#]==index&];
indexa=Complement[indexa,index\[Alpha]],
{j,lop}]],
{i,lop}]];
(****************************)

coef*=Signature[DeleteCases[chain,"\[Sigma]"^_]];
If[chain==={},oper=1,
lchain=Length[chainnum];
Switch[chain[[1]],
Subscript[h2f[-1/2], _],\[Sigma]m=\[Sigma]chain[chain[[2;;chainnum[[1]]-1]],iGreek,1];iGreek=\[Sigma]m[[3,1]];oper=Sum[ch\[Psi][chain[[1]],\[Sigma]m[[2,i]],chain[[chainnum[[1]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],
Subscript[h2f[1/2], _],\[Sigma]m=\[Sigma]chain[chain[[2;;chainnum[[1]]-1]],iGreek,-1];iGreek=\[Sigma]m[[3,1]];oper=Sum[ch\[Psi][chain[[1]],\[Sigma]m[[2,i]],chain[[chainnum[[1]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],
"\[Sigma]"^_,{oper,iGreek}=trace[Append[chain[[2;;chainnum[[1]]]],chain[[1]]],iGreek,-1]]];
If[lchain>1,Do[Switch[chain[[chainnum[[j-1]]+1]],
Subscript[h2f[-1/2], _],\[Sigma]m=\[Sigma]chain[chain[[chainnum[[j-1]]+2;;chainnum[[j]]-1]],iGreek,1];iGreek=\[Sigma]m[[3,1]];
oper*= Sum[ch\[Psi][chain[[chainnum[[j-1]]+1]],\[Sigma]m[[2,i]],chain[[chainnum[[j]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],
Subscript[h2f[1/2], _],\[Sigma]m=\[Sigma]chain[chain[[chainnum[[j-1]]+2;;chainnum[[j]]-1]],iGreek,-1];iGreek=\[Sigma]m[[3,1]];
oper*= Sum[ch\[Psi][chain[[chainnum[[j-1]]+1]],\[Sigma]m[[2,i]],chain[[chainnum[[j]]]]] \[Sigma]m[[1,i]],{i,Length[\[Sigma]m[[2]]]}],
"\[Sigma]"^_,oper*= trace[chain[[chainnum[[j-1]]+1;;chainnum[[j]]]],iGreek][[1]];iGreek= trace[chain[[chainnum[[j-1]]+1;;chainnum[[j]]]],iGreek][[2]]],
{j,2,lchain}]];
opS[[0]]=Times;
(*Return[oper opS coef]*)<|"chain"->oper,"field"->opS,"coef"->coef|>
]

(* input monomial amplitude, label shows which F will absorb epsilon *)
OperMono[A_,n_]:=Module[{oper,Aa=1,As=1,LA,coeff=1},
Switch[A[[0]],
ab,oper=OperMonoResp[A,1,n],
sb,oper=OperMonoResp[1,A,n],
Power,Switch[A[[1,0]],
ab,oper=OperMonoResp[A,1,n],
sb,oper=OperMonoResp[1,A,n]],
Times,LA=Length[A];Do[Switch[A[[i,0]],
ab,Aa*=A[[i]],
sb,As*=A[[i]],
Power,Switch[A[[i,1,0]],
ab,Aa*=A[[i]],
sb,As*=A[[i]]],
_,coeff*=A[[i]]],
{i,LA}];
oper=OperMonoResp[Aa,As,n];oper["coef"]=coeff*oper["coef"],
_,oper=OperMonoResp[1,1,n];oper["coef"]=A*oper["coef"]
];
oper=Expand[Expand[(Expand[Expand[oper["chain"]]//.contract]//.contract)oper["field"]oper["coef"]]//.Ftilde[-2]]//.contract//.beforeform;
Return[oper]
]
(* input complete amplitude, firstF shows which F will absorb epsilon *)
OperSpMonoResp[a_:1,s_:1,n_]:=Module[{opA,opS,\[Psi]i=Table[1,{i,n},{j,2}],op=1,lop,index,opi,coef,chain={},chainnum={},indexa,index\[Alpha],lchain,\[Sigma]m,oper},
opA=operab[a];
opS=opersb[s];
Do[\[Psi]i[[i,1]]=Cases[opA,Subscript[h2f[-1/2], i][_Integer,_]];
\[Psi]i[[i,1,0]]=Times;
\[Psi]i[[i,2]]=Cases[opS,Subscript[h2f[1/2], i][_Integer,_]];
\[Psi]i[[i,2,0]]=Times,
{i,n}];
Do[opi=changesp[\[Psi]i[[i,1]],\[Psi]i[[i,2]],i];op=op opi,{i,n}];
Return[op]
]

alphachange={"a"->"\!\(\*OverscriptBox[\(\[Alpha]\), \(.\)]\)","b"->"\!\(\*OverscriptBox[\(\[Beta]\), \(.\)]\)","c"->"\!\(\*OverscriptBox[\(\[Gamma]\), \(.\)]\)","d"->"\!\(\*OverscriptBox[\(\[Delta]\), \(.\)]\)","e"->"\!\(\*OverscriptBox[\(\[Epsilon]\), \(.\)]\)","f"->"\!\(\*OverscriptBox[\(\[Zeta]\), \(.\)]\)"};

(* input monomial amplitude, label shows which F will absorb epsilon *)
OperSpMono[A_,n_]:=Module[{oper,Aa=1,As=1,LA,coeff=1},
Switch[A[[0]],
ab,oper=OperSpMonoResp[A,1,n],
sb,oper=OperSpMonoResp[1,A,n],
Power,Switch[A[[1,0]],
ab,oper=OperSpMonoResp[A,1,n],
sb,oper=OperSpMonoResp[1,A,n]],
Times,LA=Length[A];
Do[Switch[A[[i,0]],
ab,Aa*=A[[i]],
sb,As*=A[[i]],
Power,Switch[A[[i,1,0]],
ab,Aa*=A[[i]],
sb,As*=A[[i]]],
_,coeff*=A[[i]]],
{i,LA}];
oper=coeff*OperSpMonoResp[Aa,As,n],
_,oper=A OperSpMonoResp[1,1,n]];
oper=oper//.alphachange
];

OperPoly[A_,n_,OptionsPattern[]]:=Module[{operpoly,form,form1,form2,form3,ten,tAssumptions},
operpoly=Thread[head[A,n],Plus]/.{head->If[OptionValue[LorForm],OperMono,OperSpMono]};
If[operpoly[[0]]===Plus,If[OptionValue[TenReduce],
operpoly=List@@operpoly;
form=tensorform/@operpoly;(*Print["form=",form];*)
form1=Union@@form[[All,2]];
form2=Union@@form[[All,3]];form3=Union@@form[[All,4]];(*Print["form1=",form1];Print["form2=",form2];Print["form3=",form3];*)
tAssumptions={epsilon\[Element]Arrays[{4,4,4,4},Antisymmetric[{1,2,3,4}]]}\[Union](sym/@form1)\[Union](antisym/@form2)\[Union](Csym/@form3)//Flatten;
ten=Map[TensorReduce[#,Assumptions->tAssumptions]&,Plus@@form[[All,1]]//Simplify,{2,3}]//Expand,form=(tensorform/@(List@@operpoly));ten=Plus@@form[[All,1]]];(*Print["ten=",ten];*)
operpoly=Thread[head[ten],Plus]/.{head->tensortooper},
form=Map[TensorReduce[#,Assumptions->tAssumptions]&,tensorform[operpoly],2];
operpoly=tensortooper[form[[1]]]];
If[OptionValue[Dcontract],operpoly=operpoly//.Flatten[{Dcontract1,Dcontract2}],operpoly]
]
Options[OperPoly]={LorForm->True,Dcontract->False,TenReduce->True};


(* ::Input::Initialization:: *)
beforechange={ch\[Psi][dd__,(Subscript|Superscript)[D,\[Nu]_],fi2:Subscript[fi_,n_]|Subscript[fi_,n_][inde__]]/;(!Cases[h2f,fi]==={}):>Subscript[D,n][\[Nu]]ch\[Psi][dd,fi2],ch\[Psi][(Subscript|Superscript)[D,\[Nu]_],fi2:Subscript[fi_,n_]|Subscript[fi_,n_][inde__]]/;(!Cases[h2f,fi]==={}):>Subscript[D,n][\[Nu]]fi2,ch\[Psi][aa___,Subscript[D,n_][\[Nu]_]fi_,bb___]:>Subscript[D,n][\[Nu]]ch\[Psi][aa,fi,bb],Subscript[Subscript[D, n_], \[Nu]_]|Superscript[Subscript[D, n_],\[Nu]_]:>Subscript[D, n][\[Nu]],
Subscript["\[Sigma]", \[Mu]_]|Superscript["\[Sigma]",\[Mu]_]|"\[Sigma]"^\[Mu]_:>"\[Sigma]"[\[Mu]],
Subscript["\[Gamma]", \[Mu]_]|Superscript["\[Gamma]",\[Mu]_]|"\[Gamma]"^\[Mu]_:>"\[Gamma]"[\[Mu]],
Subscript["\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)", \[Mu]_]|Superscript["\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)",\[Mu]_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"^\[Mu]_:>"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[\[Mu]],
Subscript[Subscript[\[Sigma]_, \[Mu]_], \[Nu]_]|Superscript[Subscript[\[Sigma]_, \[Mu]_],\[Nu]_]|Subscript[Superscript[\[Sigma]_,\[Mu]_],\[Nu]_]|Superscript[Superscript[\[Sigma]_,\[Mu]_],\[Nu]_]:>\[Sigma][\[Mu],\[Nu]],
Superscript["\[Epsilon]",Times[a_,b_,c_,d_]]:>"\[Epsilon]"[a,b,c,d],(fi:Subscript[h2f[-1], n_]|Subscript[h2f[1], n_])[munu_,nu_]:>fi["up",munu,"up",nu]};

SetAttributes[{antichange}, HoldAll];
antichange[PartofAmp_,Greek_]:=Module[{spinor,particle,l\[Sigma]},
Switch[PartofAmp,
Subscript[D, _][_],particle=PartofAmp[[0,2]];
spinor=-I/2*Subscript[h2f[-1/2], particle][1,su2l[[Greek]]]Subscript[h2f[1/2], particle][1,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[1]]][2,su2l[[Greek]],2,su2r[[Greek]]];Greek++,

Subscript[h2f[-1], _][__],particle=PartofAmp[[0,2]];
spinor=1/4*Subscript[h2f[-1/2], particle][1,su2l[[Greek]]]Subscript[h2f[-1/2], particle][1,su2l[[Greek+1]]]"\[Sigma]"[PartofAmp[[2]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[4]]][2,su2l[[Greek+1]],1,su2r[[Greek]]];Greek+=2,

Subscript[h2f[1], _][__],particle=PartofAmp[[0,2]];spinor=1/4*Subscript[h2f[1/2], particle][1,su2r[[Greek]]]Subscript[h2f[1/2], particle][1,su2r[[Greek+1]]]"\[Sigma]"[PartofAmp[[2]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[4]]][1,su2l[[Greek]],2,su2r[[Greek+1]]];Greek+=2,

(******* spin2 begin ********)
Subscript[h2f[-2], _][__],particle=PartofAmp[[0,2]];
spinor=1/16*Subscript[h2f[-1/2], particle][1,su2l[[Greek]]]Subscript[h2f[-1/2], particle][1,su2l[[Greek+1]]]"\[Sigma]"[PartofAmp[[2]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[4]]][2,su2l[[Greek+1]],1,su2r[[Greek]]]Subscript[h2f[-1/2], particle][1,su2l[[Greek+2]]]Subscript[h2f[-1/2], particle][1,su2l[[Greek+3]]]"\[Sigma]"[PartofAmp[[6]]][2,su2l[[Greek+2]],2,su2r[[Greek+1]]]"\[Sigma]"[PartofAmp[[8]]][2,su2l[[Greek+3]],1,su2r[[Greek+1]]];Greek+=4,

Subscript[h2f[2], _][__],particle=PartofAmp[[0,2]];spinor=1/16*Subscript[h2f[1/2], particle][1,su2r[[Greek]]]Subscript[h2f[1/2], particle][1,su2r[[Greek+1]]]"\[Sigma]"[PartofAmp[[2]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[4]]][1,su2l[[Greek]],2,su2r[[Greek+1]]]Subscript[h2f[1/2], particle][1,su2r[[Greek+2]]]Subscript[h2f[1/2], particle][1,su2r[[Greek+3]]]"\[Sigma]"[PartofAmp[[6]]][2,su2l[[Greek+2]],2,su2r[[Greek+2]]]"\[Sigma]"[PartofAmp[[8]]][1,su2l[[Greek+2]],2,su2r[[Greek+3]]];Greek+=4,
(******* spin2 over **********)

ch\[Psi][Subscript[h2f[-1/2], _],1,Subscript[h2f[-1/2], _]],spinor=PartofAmp[[1]][2,su2l[[Greek]]]PartofAmp[[3]][1,su2l[[Greek]]];Greek++,

ch\[Psi][Subscript[h2f[1/2], _],1,Subscript[h2f[1/2], _]],spinor=PartofAmp[[1]][1,su2r[[Greek]]]PartofAmp[[3]][2,su2r[[Greek]]];Greek++,

ch\[Psi][Subscript[h2f[-1/2], _],"\[Sigma]"[_]|"\[Gamma]"[_],Subscript[h2f[1/2], _]],spinor=PartofAmp[[1]][2,su2l[[Greek]]]"\[Sigma]"[PartofAmp[[2,1]]][1,su2l[[Greek]],1,su2r[[Greek]]]PartofAmp[[3]][2,su2r[[Greek]]];Greek++,

ch\[Psi][Subscript[h2f[1/2], _],"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[_]|"\[Gamma]"[_],Subscript[h2f[-1/2], _]],spinor=PartofAmp[[1]][1,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2,1]]][2,su2l[[Greek]],2,su2r[[Greek]]]PartofAmp[[3]][1,su2l[[Greek]]];Greek++,

ch\[Psi][Subscript[h2f[-1/2], _],"\[Sigma]"[__],Subscript[h2f[-1/2], _]],spinor=I/2*PartofAmp[[1]][2,su2l[[Greek]]]("\[Sigma]"[PartofAmp[[2,1]]][1,su2l[[Greek]],1,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2,2]]][2,su2l[[Greek+1]],2,su2r[[Greek]]]-"\[Sigma]"[PartofAmp[[2,2]]][1,su2l[[Greek]],1,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2,1]]][2,su2l[[Greek+1]],2,su2r[[Greek]]])PartofAmp[[3]][1,su2l[[Greek+1]]];Greek+=2,

ch\[Psi][Subscript[h2f[1/2], _],"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[__],Subscript[h2f[1/2], _]],spinor=I/2*PartofAmp[[1]][1,su2r[[Greek]]]("\[Sigma]"[PartofAmp[[2,1]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2,2]]][1,su2l[[Greek]],1,su2r[[Greek+1]]]-"\[Sigma]"[PartofAmp[[2,2]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2,1]]][1,su2l[[Greek]],1,su2r[[Greek+1]]])PartofAmp[[3]][2,su2r[[Greek+1]]];Greek+=2,

ch\[Psi][Subscript[h2f[-1/2],_],"\[Sigma]"[_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[_],"\[Sigma]"[_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[_],__],
l\[Sigma]=Length@PartofAmp-2;
spinor=PartofAmp[[1]][2,su2l[[Greek]]];Do[If[OddQ@li,spinor*="\[Sigma]"[PartofAmp[[li+1,1]]][1,su2l[[Greek+Floor[li/2]]],1,su2r[[Greek+Floor[li/2]]]],
spinor*="\[Sigma]"[PartofAmp[[li+1,1]]][2,su2l[[Greek+Floor[li/2]]],2,su2r[[Greek-1+Floor[li/2]]]]],{li,l\[Sigma]}];If[OddQ@l\[Sigma],spinor*=PartofAmp[[-1]][2,su2r[[Greek+Floor[l\[Sigma]/2]]]],spinor*=PartofAmp[[-1]][1,su2l[[Greek+Floor[l\[Sigma]/2]]]]];
Greek+=Floor[l\[Sigma]/2]+1,

ch\[Psi][Subscript[h2f[1/2],_],"\[Sigma]"[_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[_],"\[Sigma]"[_]|"\!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)"[_],__],
l\[Sigma]=Length@PartofAmp-2;
spinor=PartofAmp[[1]][1,su2r[[Greek]]];Do[If[OddQ@li,spinor*="\[Sigma]"[PartofAmp[[li+1,1]]][2,su2l[[Greek+Floor[li/2]]],2,su2r[[Greek+Floor[li/2]]]],
spinor*="\[Sigma]"[PartofAmp[[li+1,1]]][1,su2l[[Greek-1+Floor[li/2]]],1,su2r[[Greek+Floor[li/2]]]]],{li,l\[Sigma]}];If[OddQ@l\[Sigma],spinor*=PartofAmp[[-1]][1,su2l[[Greek+Floor[l\[Sigma]/2]]]],spinor*=PartofAmp[[-1]][2,su2r[[Greek+Floor[l\[Sigma]/2]]]]];
Greek+=Floor[l\[Sigma]/2]+1,


"\[Epsilon]"[__],spinor=I/4("\[Sigma]"[PartofAmp[[1]]][2,su2l[[Greek]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2]]][1,su2l[[Greek]],1,su2r[[Greek+1]]]"\[Sigma]"[PartofAmp[[3]]][2,su2l[[Greek+1]],2,su2r[[Greek+1]]]"\[Sigma]"[PartofAmp[[4]]][1,su2l[[Greek+1]],1,su2r[[Greek]]]-"\[Sigma]"[PartofAmp[[1]]][1,su2l[[Greek]],1,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[2]]][2,su2l[[Greek+1]],2,su2r[[Greek]]]"\[Sigma]"[PartofAmp[[3]]][1,su2l[[Greek+1]],1,su2r[[Greek+1]]]"\[Sigma]"[PartofAmp[[4]]][2,su2l[[Greek]],2,su2r[[Greek+1]]]);Greek+=2,

Subscript[h2f[0], _],spinor=1,

_,spinor=PartofAmp
];

Return[spinor]
]

\[Sigma]contract={"\[Sigma]"[\[Mu]_][n1_,\[Alpha]_,n2_,a_]"\[Sigma]"[\[Mu]_][n3_,\[Beta]_,n4_,b_]:>(-1)^(n3+n4) 2\[Epsilon][n1,\[Alpha],n3,\[Beta]]\[Epsilon][n2,a,n4,b]};
\[Epsilon]contract={\[Epsilon][n1_,\[Alpha]_,n2_,\[Beta]_]Subscript[h2f[-1/2], i_][n3_,\[Beta]_]:>Subscript[h2f[-1/2], i][n1,\[Alpha]],
\[Epsilon][n1_,a_,n2_,b_]Subscript[h2f[1/2], i_][n3_,b_]:>Subscript[h2f[1/2], i][n1,a],
\[Epsilon][n1_,a_,n2_,b_]\[Epsilon][n3_,b_,n4_,c_]:>\[Epsilon][n1,a,n4,c],
\[Epsilon][n1_,a_,n2_,b_]\[Epsilon][n3_,c_,n4_,b_]:>(-1)^(n3+n4+1) \[Epsilon][n1,a,n3,c],
\[Epsilon][n1_,b_,n2_,a_]\[Epsilon][n3_,b_,n4_,c_]:>(-1)^(n1+n2+1) \[Epsilon][n2,a,n4,c],
\[Epsilon][n1_,a_,n2_,a_]:>2};
asbracket={Subscript[h2f[-1/2], i_][2,a_]Subscript[h2f[-1/2], j_][1,a_]:>ab[i,j],
Subscript[h2f[1/2], i_][1,a_]Subscript[h2f[1/2], j_][2,a_]:>sb[i,j]};
AmpMono[opermono_,operinput_]:=Module[{Greek=1,oper,amp,fermion,fermionsign={}},
oper=opermono//.beforechange;
If[operinput,If[oper[[0]]===ch\[Psi],fermion={oper},fermion=Cases[oper,_ch\[Psi]]];
Do[AppendTo[fermionsign,fermion[[ii,1]]];
AppendTo[fermionsign,fermion[[ii,3]]],
{ii,Length[fermion]}];
fermionsign=Signature[fermionsign];
amp=If[oper[[0]]===ch\[Psi],fermionsign*antichange[oper,Greek],fermionsign*antichange[#,Greek]&/@oper],
amp=Times@@(antichange[#,Greek]&/@(Flatten[{oper}/.{Times->List,Power->ConstantArray}]))];
amp=Expand[amp]//.\[Sigma]contract//.\[Epsilon]contract//.asbracket
]
Amp[oper_,OptionsPattern[]]:=Thread[head[oper,OptionValue[OperInput]],Plus]/.{head->AmpMono};
Options[Amp]={OperInput->True};


(* ::Input::Initialization:: *)
(* find monomial Lorentz basis *)
Options[MonoLorentzBasis]={finalform->True};
MonoLorentzBasis[{1},num_Integer,OptionsPattern[]]:=<|"LorBasis"->{OperPoly[1,num]},"Trans"->{{1}}|>
MonoLorentzBasis[state:{__?NumberQ},k_Integer,OptionsPattern[]]:=MonoLorentzBasis[SSYT[state,k,OutMode->"amplitude"],Length[state],finalform->OptionValue[finalform]]
MonoLorentzBasis[spinorbasis_List,num_Integer,OptionsPattern[]]:=Module[{operbasis,coefbasis,basispos,transfer,basis},
operbasis=OperPoly[#,num,Dcontract->False,TenReduce->False]&/@spinorbasis;operbasis=Flatten[operbasis//.{Plus->List}]//.{Times[_Integer,p__]:>Times[p],Times[_Rational,p__]:>Times[p],Times[_Complex,p__]:>Times[I,p]};coefbasis=FindCor[reduce[#,num],spinorbasis]&/@(Amp/@operbasis);(*basispos=Subsets[coefbasis,{Length[spinorbasis]}];Do[If[MatrixRank[basispos[[ii]]]===Length[spinorbasis],transfer=basispos[[ii]];Break[]],{ii,Length[basispos]}];*)
basis=basisReduce[coefbasis];
(*basispos=Flatten[Position[coefbasis,#][[1]]&/@transfer];
basis=operbasis[[basis["pos"]]];*)
<|"LorBasis"->operbasis[[basis["pos"]]],"Trans"->basis["basis"]|>
]
