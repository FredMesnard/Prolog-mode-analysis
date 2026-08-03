% Copyright (C) 2003-2026 Fred Mesnard <frederic.mesnard@gmail.com>
%
% This file is part of Prolog-mode-analysis.
%
% Prolog-mode-analysis is free software: you can redistribute it and/or
% modify it under the terms of the GNU Lesser General Public License as
% published by the Free Software Foundation, either version 3 of the
% License, or (at your option) any later version.
%
% Prolog-mode-analysis is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
% Lesser General Public License for more details.
%
% You should have received a copy of the GNU Lesser General Public
% License along with this program.  If not, see
% <https://www.gnu.org/licenses/>.

:- module(prolog_clph,[flatprolog_clph/2,flatprologs_clphs/2,clphclauses_PIs/2]).

:- use_module(library(lists),[append/3]).
:- use_module(utils,[not_member/2,suppress_empty_constraint/2,clause_head/2,clause_body/2,build_clause/3]).

flatprologs_clphs([],[]).
flatprologs_clphs([C|Cs],[CLPH1|CLPHs]) :-
    flatprolog_clph(C,CLPH1),
    flatprologs_clphs(Cs,CLPHs).

flatprolog_clph(FPCl,ObjCl) :-
    %
    %trace,
	clause_head(FPCl,H),
	normalise_atome(H,Hn,Cs),
	clause_body(FPCl,Bs),
	normalise_corps(Bs,Ds),
	suppress_empty_constraint(['$constraint'(Cs)|Ds],Es),
	build_clause(Hn,Es,ObjCl).

normalise_atome(H,Hn,Cs) :-
	functor(H,P,N),
	functor(Hn,P,N),
	normalise_args(N,H,Hn,[],Cs,[]).

normalise_args(0,_H,_Hn,Cs,Cs,_) :- !.
normalise_args(N,H,Hn,Cs,Ds,Vars) :-
	N>0,M is N-1,
	arg(N,H,An),
	arg(N,Hn,Xn),
    %/*
	%% careful: Hn must be normalised, e.g. p(A,A) no, p(A,B) yes
    (var_premiereOcc(An,Vars) ->
        Xn = An, C2s = Cs, Var2s = [An|Vars]
	;
	    C2s = [Xn=An|Cs], Var2s = Vars),
    %*/    
    %C2s = [Xn=An|Cs], Var2s = Vars,
	normalise_args(M,H,Hn,C2s,Ds,Var2s).

var_premiereOcc(X,Xs) :- var(X),not_member(X,Xs).

normalise_corps([],[]).
normalise_corps([A|As],Cns) :-
	normalise_elt(A,Ans),
	append(Ans,Bns,Cns),
	normalise_corps(As,Bns).

normalise_elt('$predef'('$bool'(A)),['$predef'('$bool'(A))]) :-!.
normalise_elt('$predef'('$num'(A)), ['$predef'('$num'(A))]) :-!.
normalise_elt('$predef'('$term_cond'(A)), ['$predef'('$term_cond'(A))]) :-!.
normalise_elt('$predef'(A),['$constraint'(Cs),'$predef'(An)]) :-
	!,normalise_atome(A,An,Cs).
normalise_elt(A,['$constraint'(Cs),An]) :-
	normalise_atome(A,An,Cs).


%% 
clphclauses_PIs(ClpHClauses,PIs) :- clphclauses_PIs(ClpHClauses,[],PIs).
    
    clphclauses_PIs([],PIs,PIs).
    clphclauses_PIs([obj_clause(Head,Body)|ClpHClauses],PIs0,PIs) :-
        functor(Head,P,N),
        (memberchk(P/N,PIs0) -> PIs1=PIs0 ; PIs1 = [P/N|PIs0]),
        clphbody_PIs(Body,PIs1,PIs2),
        clphclauses_PIs(ClpHClauses,PIs2,PIs).
        
        clphbody_PIs([],PIs,PIs).
        clphbody_PIs(['$constraint'(_)|Body],PIs0,PIs) :- !, clphbody_PIs(Body,PIs0,PIs).
        clphbody_PIs(['$predef'(_)|Body],PIs0,PIs)    :- !, clphbody_PIs(Body,PIs0,PIs).
        clphbody_PIs([B|Body],PIs0,PIs) :-
            functor(B,P,N),
            (memberchk(P/N,PIs0) -> PIs1 = PIs0 ; PIs1 = [P/N|PIs0]),
            clphbody_PIs(Body,PIs1,PIs).