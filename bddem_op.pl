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

:- module(bddem_op,[
		   true/1,
		   false/1,
		   conjunction/3,
		   satisfiable/1,
		   entail/4,
		   equivalent/4,
		   union/6,
		   widening/6,
		   project/4,
		   bddem_available/0
		  ]).

% Boolean (Pos) abstract domain, alternative to bool_op.pl, built on
% bddem/CUDD.
%
% REPRESENTATION CHOICE. A constraint stays a Boolean TERM, exactly as in
% bool_op. This is not a detail: bool_itp.pl and mode_analysis.pl copy_term/2
% constraints and rely on Prolog variable renaming to tie a constraint to the
% atom it constrains. A BDD pointer is an opaque integer, which copy_term does
% not rename. Keeping BDDs across calls would mean carrying the variable list
% with each node and permuting indices at every conjunction, hence exposing
% Cudd_bddPermute as well.
%
% CUDD is therefore used only as a DECISION ENGINE: the term is compiled to a
% BDD at each decision point, and only project/4 converts a BDD back to a
% term. That is the structural handicap of this integration, worth keeping in
% mind when reading the timings: clpb maintains its state incrementally, via
% attributed variables.
%
% CUDD's dynamic reordering is switched off (set_reordering(E,none)): on
% Pos-shaped constraints the creation order is already good, and the group
% sifting that init/1 enables by default costs a lot there, unpredictably.

% The bddem pack is optional. Loading it unconditionally made every run print
% an error when the pack was absent -- even a plain clpb run, which needs
% nothing from it. exists_source/1 checks without loading.
:- if(exists_source(library(bddem))).
:- use_module(library(bddem)).
:- endif.

:- use_module(library(lists)).

:- op(300, fy, ~).
:- op(500, yfx, #).

%%%%
% True when the pack is present AND carries the two additions this domain
% needs. An unpatched pack loads fine but has no exist_abstract/4, so
% project/4 would fail at run time; set_domain/1 checks this beforehand.
bddem_available :-
	current_predicate(bddem:exist_abstract/4),
	current_predicate(bddem:set_reordering/2).

%%%%
true(1).

%%%%
false(0).

%%%%
conjunction(C1,C2,C1*C2).

%%%%
widening(Xs,S,Ys,T,Zs,U) :- union(Xs,S,Ys,T,Zs,U).

%%%%
union(Xs,S,Ys,T,Zs,U) :-
	copy_term(e(Ys,T),e(Xs,Tcxs)),
	project(Xs,S+Tcxs,Zs,U).

%%%%
satisfiable(C) :-
	setup_call_cleanup(new_env(E), sat_(E,C), end(E)).

    sat_(E,C) :-
	term_variables(C,Vs),
	mk_map(E,Vs,M),
	compile(E,C,M,B),
	zero(E,Z),
	B \== Z.

%%%% S entails T iff S and not-T is unsatisfiable.
entail(Xs,S,Ys,T) :-
	\+ \+ ( Xs=Ys, \+ satisfiable(S * ~T) ).

%%%% S is equivalent to T iff their exclusive-or is unsatisfiable.
equivalent(Xs,S,Ys,T) :-
	\+ \+ ( Xs=Ys, \+ satisfiable(S # T) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% project(+Xs,+S,+Ys,-T)
%
% T is a formula over the fresh variables Ys, equivalent to
% "exists (vars(S) \ vars(Xs)) . S", the positions of Ys matching those of Xs.
%
% Measured beforehand on the FilexTC corpus: 4058 calls, |vars(Xs)| =< 8. The
% BDD -> term conversion is therefore done by Shannon decomposition over the
% kept variables only, pruning null branches: the cost is proportional to the
% number of minterms in the result, bounded by 2^8.

project(Xs,S,Ys,T) :-
	length(Xs,N),
	length(Ys,N),
	setup_call_cleanup(new_env(E), project_(E,Xs,S,Ys,T), end(E)).

    project_(E,Xs,S,Ys,T) :-
	garder(Xs,Ys,Paires,Extra),
	term_variables(S,SVars),
	paires_vars(Paires,KeepVars),
	ajouter_vars(KeepVars,SVars,AllVars),
	mk_map(E,AllVars,M),
	compile(E,S,M,B),
	oter_vars(AllVars,KeepVars,ElimVars),
	index_de(ElimVars,M,ElimIdx),
	exist_abstract(E,B,ElimIdx,G),
	zero(E,Z),
	(   G == Z
	->  T = 0
	;   dnf(E,G,Paires,M,[],Produits,[]),
	    somme(Produits,Dnf),
	    conjoindre(Extra,Dnf,T)
	).

% garder(+Xs,+Ys,-Pairs,-Extra)
%   Pairs : Var-Y for each distinct variable of Xs.
%   Extra : constraints accounting for the positions not represented, namely
%           repeated occurrences of one variable and the constants 0/1. Same
%           role as normalize/5 in bool_op.
garder([],[],[],1).
garder([X|Xs],[Y|Ys],Paires,Extra) :-
	garder(Xs,Ys,P0,E0),
	(   var(X)
	->  (   cherche_paire(P0,X,Y0)
	    ->  Paires=P0, Extra=((Y=:=Y0)*E0)
	    ;   Paires=[X-Y|P0], Extra=E0
	    )
	;   Paires=P0,
	    (	X==1 -> Extra=(Y*E0)
	    ;	X==0 -> Extra=((~Y)*E0)
	    ;	Extra=E0
	    )
	).

cherche_paire([K-V|_],X,V) :- K==X, !.
cherche_paire([_|Ps],X,V) :- cherche_paire(Ps,X,V).

paires_vars([],[]).
paires_vars([V-_|Ps],[V|Vs]) :- paires_vars(Ps,Vs).

% dnf(+E,+BDD,+Pairs,+Map,+Literals,-Products,+Tail)
% Shannon decomposition with pruning: we only descend into branches whose BDD
% is non-null, so the cost follows the size of the result.
dnf(_E,_B,[],_M,Acc,[P|T],T) :- !,
	produit(Acc,P).
dnf(E,B,[V-Y|Ps],M,Acc,Produits,T) :-
	cherche(M,V,i(_,Lit)),
	zero(E,Z),
	and(E,B,Lit,B1),
	(   B1 == Z
	->  Produits=Reste
	;   dnf(E,B1,Ps,M,[Y|Acc],Produits,Reste)
	),
	bdd_not(E,Lit,NLit),
	and(E,B,NLit,B0),
	(   B0 == Z
	->  Reste=T
	;   dnf(E,B0,Ps,M,[~Y|Acc],Reste,T)
	).

produit([],1).
produit([L|Ls],P) :- produit_(Ls,L,P).
    produit_([],P,P).
    produit_([L|Ls],Acc,P) :- produit_(Ls,L*Acc,P).

somme([],0).
somme([P|Ps],S) :- somme_(Ps,P,S).
    somme_([],S,S).
    somme_([P|Ps],Acc,S) :- somme_(Ps,P+Acc,S).

conjoindre(1,D,D) :- !.
conjoindre(Extra,D,Extra*D).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Environment, variable table, term -> BDD compilation

new_env(E) :-
	init(E),
	set_reordering(E,none).

mk_map(_E,[],[]).
mk_map(E,[V|Vs],[V-i(Idx,Lit)|M]) :-
	add_var(E,[0.5,0.5],0,Idx),
	equality(E,Idx,1,Lit),
	mk_map(E,Vs,M).

cherche([K-Val|_],V,Val) :- K==V, !.
cherche([_|M],V,Val) :- cherche(M,V,Val).

index_de([],_M,[]).
index_de([V|Vs],M,[I|Is]) :- cherche(M,V,i(I,_)), index_de(Vs,M,Is).

% ajouter_vars(+Vs,+Acc,-Union) - union by identity, Vs first.
ajouter_vars([],Acc,Acc).
ajouter_vars([V|Vs],Acc,U) :-
	(   memberchk_eq(V,Acc)
	->  ajouter_vars(Vs,Acc,U)
	;   ajouter_vars(Vs,[V|Acc],U)
	).

oter_vars([],_,[]).
oter_vars([V|Vs],Ex,R) :-
	(   memberchk_eq(V,Ex)
	->  R=R1
	;   R=[V|R1]
	),
	oter_vars(Vs,Ex,R1).

memberchk_eq(X,[Y|_]) :- X==Y, !.
memberchk_eq(X,[_|Ys]) :- memberchk_eq(X,Ys).

% compile(+E,+Terme,+Map,-BDD)
compile(_E,T,M,B) :- var(T), !, cherche(M,T,i(_,B)).
compile(E,T,_M,B) :- T==1, !, one(E,B).
compile(E,T,_M,B) :- T==0, !, zero(E,B).
compile(E,A*C,M,B) :- !, compile(E,A,M,BA), compile(E,C,M,BC), and(E,BA,BC,B).
compile(E,A+C,M,B) :- !, compile(E,A,M,BA), compile(E,C,M,BC), or(E,BA,BC,B).
compile(E,~A,M,B)  :- !, compile(E,A,M,BA), bdd_not(E,BA,B).
compile(E,A=:=C,M,B) :- !,
	compile(E,A,M,BA), compile(E,C,M,BC),
	bdd_not(E,BA,NA), bdd_not(E,BC,NC),
	and(E,BA,BC,P1), and(E,NA,NC,P2), or(E,P1,P2,B).
compile(E,A#C,M,B) :- !,
	compile(E,A,M,BA), compile(E,C,M,BC),
	bdd_not(E,BA,NA), bdd_not(E,BC,NC),
	and(E,BA,NC,P1), and(E,NA,BC,P2), or(E,P1,P2,B).
compile(E,A=<C,M,B) :- !,          % implication
	compile(E,A,M,BA), compile(E,C,M,BC),
	bdd_not(E,BA,NA), or(E,NA,BC,B).
compile(E,V^A,M,B) :- !,           % explicit existential quantification
	compile(E,A,M,BA),
	term_variables(V,Vs),
	index_de(Vs,M,Is),
	exist_abstract(E,BA,Is,B).
compile(_E,T,_M,_B) :-
	throw(error(domain_error(formule_booleenne,T),bddem_op:compile/4)).
