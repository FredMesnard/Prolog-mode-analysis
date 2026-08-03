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

:- module(prolog_flatprolog,[prolog_flatprologs/2,prologs_flatprologs/2]).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prolog_flatprologs(ClauseProlog,-ListeClausesFP)
%----------------------------------------------
% Turns an ISO-Prolog clause (with :-, conjunction, disjunction, ->, \+ ...)
% or a DCG term into a list of obj_clause(Head,Body) terms, where:
% 	Head is the head of Clause, and
% 	Body the equivalent resolvent (for termination).
% Here a resolvent is a list (a conjunction) of atoms and of built-ins of the
% form '$predef'(Atom). The variables of each clause of ListeClauses are
% disjoint from those of the other clauses (they are copied).

:- use_module(library(lists),[append/3]).
:- use_module(predef,[predef/1]).
:- use_module(utils,[build_clause/3]).

prologs_flatprologs([],[]).
prologs_flatprologs([C|Cs],FPClauses) :-
    prolog_flatprologs(C,LCl1),
    append(LCl1,Ls,FPClauses),
    prologs_flatprologs(Cs,Ls).

prolog_flatprologs(Clause,ListeClauses) :-
	%expand_term(Clause,EClause),
	EClause=Clause,
	prolog_flatprologs2(EClause,ListeClauses).

prolog_flatprologs2((A :- _),ListClauses) :-
    predef(A),!,
	%write('% WARNING: '),write(A),write(' is a built-in and cannot be redefined'),nl,
	ListClauses=[].
prolog_flatprologs2((A :- Body),ListClauses) :-       
        !,
	tr1s(Body,Body2),	% remplacement controle + 2d ordre
	tr3(Body2,Bodys),	% expansion	
	distribute(Bodys,A,ListClauses).
prolog_flatprologs2(A,ListClauses) :-
    predef(A),!,
	%write('% WARNING: '),write(A),write(' is a built-in and cannot be redefined'),nl,
	ListClauses=[].
prolog_flatprologs2(Fact,[ObjClause]) :-
	build_clause(Fact,[],ObjClause).

distribute([],_,[]).
distribute([BodyTrue|Bodys],H,[ObjCl|ObjCls]) :-
	suppress_true(BodyTrue,Body),
	copy_term(H-Body,Hc-Bodyc),
	build_clause(Hc,Bodyc,ObjCl),
	distribute(Bodys,H,ObjCls).

suppress_true([],[]).
suppress_true(['$predef'(true)|As],Bs) :- !,suppress_true(As,Bs).
suppress_true([A|As],[A|Bs]) :- suppress_true(As,Bs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tr1s(+ClauseBody,-ClauseBody)
% first pass: rewriting of some built-ins
tr1s(A,repeat) :- var(A),!.
tr1s((A,As),Cs)               :- !,tr1(A,B),conc(B,Bs,Cs),tr1s(As,Bs).
tr1s((As ; Bs),(A2s ; B2s))   :- !,tr1s(As,A2s),tr1s(Bs,B2s).
tr1s((As -> Bs),(A2s -> B2s)) :- !,tr1s(As,A2s),tr1s(Bs,B2s).
tr1s(A,B)                     :- tr1(A,B).

tr1(A,repeat) :- var(A),!.
tr1(A,B) :-(tr2(A,C) -> B=C ; B=A).

tr2( \+ (G),            (Gs;true)) :- conc(G,fail,Gs).
tr2( once(G),           But)       :- (buts_suff_inst(G) -> But=G ; But=repeat).
tr2( call(G),           But)       :- (buts_suff_inst(G) -> But=G ; But=repeat).
tr2( setof(_,_^G,_),    (Gs;true)) :- !,conc(G,fail,Gs).
tr2( setof(_,_:G,_),    (Gs;true)) :- !,conc(G,fail,Gs).
tr2( setof(_,G,_),      (Gs;true)) :- conc(G,fail,Gs).
tr2( bagof(_,_:G,_),    (Gs;true)) :- !,conc(G,fail,Gs).
tr2( bagof(_,G,_),      (Gs;true)) :- !,conc(G,fail,Gs).
tr2( findall(_,_:G,_),  (Gs;true)) :- !,conc(G,fail,Gs).
tr2( findall(_,G,_),    (Gs;true)) :- conc(G,fail,Gs).
tr2( throw(_),          fail).
tr2( catch(G,_C,RG),    But) :- (buts_suff_inst((G,RG)) -> But=(G;RG) ; But=repeat).

conc(A,B,(repeat,B)) :-var(A),!.
conc((A,As),B,(A,Cs)) :-!,conc(As,B,Cs).
conc(A,B,(A,B)).

buts_suff_inst(G) :-var(G),!,fail.
buts_suff_inst((G,Gs)) :-!,but_si(G),buts_suff_inst(Gs).
buts_suff_inst(G) :-but_si(G).

but_si(G) :- nonvar(G).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tr3(+Res,-Res*)
% second pass: expansion
tr3((A,As),Ress)     :- !,tr3(A,[[]],As,Ress).
tr3((As ; Bs),Ress)  :- !,tr3((As ; Bs), [[]],'$predef'(true),Ress).
tr3((As -> Bs),Ress) :- !,tr3((As -> Bs), [[]],'$predef'(true),Ress).
tr3(At,[[A]])        :- (local_predef(At) -> A='$predef'(At) ; A=At).

% tr3(At,Res*,Res,Res*)
tr3((As ; Bs),RessIn,Res,RessOut) :-
	!,tr3(As,Ass),
	append_cross(RessIn,Ass,Ress2),
	tr3(Bs,Bss),
	append_cross(RessIn,Bss,Ress3),
	tr3(Res,Ress4),
	append_cross(Ress2,Ress4,Ress5),
	append_cross(Ress3,Ress4,Ress6),
	append(Ress5,Ress6,RessOut).
tr3((As -> Bs),RessIn,Res,RessOut) :-
	!,tr3(As,Ass),
	tr3(Bs,Bss),
	tr3(Res,Ress),
	append_cross(RessIn,Ass,Ress2),
	Ress2=Ress3,
	append_cross(Ress3,Bss,Ress4),
	append_cross(Ress4,Ress,RessOut).
tr3(At,RessIn,Res,RessOut) :-
	functor(At,P,N),functor(Head,P,N),
        (local_predef(Head)-> A='$predef'(At)	; A=At),
	appends(RessIn,[A],Ress2),
	tr3(Res,Ress3),
	append_cross(Ress2,Ress3,RessOut).

%%%%%%%%%%%%%
local_predef( asserta(_)) :- !,warning(asserta/1).
local_predef( assertz(_)) :- !,warning(assertz/1).
local_predef( retract(_)) :- !,warning(retract/1).
local_predef( At)         :- predef(At).

warning(PI) :- write('% WARNING: using '),write(PI),write(' may distort the analysis'),nl.

%%%%%%%%%%%%%
% utilities

% append(Res*,Res,Res*)
appends([],_,[]).
appends([R|Rs],Res,[R1|R2s]) :-
	append(R,Res,R1),
	appends(Rs,Res,R2s).
	
% append_cross(Res*,Res*,Res*)
append_cross(Ress1,Ress2,Ress3) :-
	append_cross2(Ress2,Ress1,Ress3).

append_cross2([],_,[]).
append_cross2([R|Rs],Ress1,Ress2) :-
	appends(Ress1,R,Ress3),
	append(Ress3,Ress4,Ress2),
	append_cross2(Rs,Ress1,Ress4).

%%%%%%%%%%
/*
| ?- prolog_flatprologs(p,L).

| ?- prolog_flatprologs(p(X),L).

| ?- prolog_flatprologs(p(X,X),L).

| ?- prolog_flatprologs((p:-q;r),L).
L = [obj_clause(p, [q]), obj_clause(p, [r])].

| ?- prolog_flatprologs((p:-q;(r;s)),L).

| ?- prolog_flatprologs((p:-(q1;q2);(r;s)),L).

| ?- prolog_flatprologs((p:-q,(r;s),t),L).
L = [obj_clause(p, [q, r, t]), obj_clause(p, [q, s, t])].

?- prolog_flatprologs((p(X,X):-b(X),c(X)),L).
L = [obj_clause(p(_A, _A), [b(_A), c(_A)])].

?- prolog_flatprologs((p(X,a,X):-b(X),c(X)),L).
L = [obj_clause(p(_A, a, _A), [b(_A), c(_A)])].

?- prolog_flatprologs((a:-true),L).
L = [obj_clause(a, [])].

?- prolog_flatprologs((a:-fail),L).
L = [obj_clause(a, ['$predef'(fail)])].

?- prolog_flatprologs((a:-X=1),L).
L = [obj_clause(a, ['$predef'(_=1)])].


*/
