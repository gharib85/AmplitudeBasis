(* ::Package:: *)

(* ::Input::Initialization:: *)
(* Initialization *)
If[MatchQ[groupList,_List],AppendTo[groupList,U1],groupList={U1}];
If[!AssociationQ[tRep],tRep=<||>];
If[!AssociationQ[tOut],tOut=<||>];
If[!AssociationQ[tVal],tVal=<||>];
If[!AssociationQ[tYDcol],tYDcol=<||>];
If[!IntegerQ[dummyIndexCount],dummyIndexCount=0];
If[!AssociationQ[tSimp],tSimp=<||>];
