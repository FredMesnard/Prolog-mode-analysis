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

:- module(utils,[
		 tous_pos/2,
		 not_member/2,
		 suppress_empty_constraint/2,
		 virer_ref/2,
		 write_list/1,
     write_list_list/1,
     sccs_list/2,
		 cg_db_domain_undefpred/4,
		 sccs_db_domain_sccscls/4,
		 graph_sccs/2,
		 call_graph/2,
		 clause_head/2,
		 clause_body/2,
		 build_clause/3,
		 possibly_nonterm_predicates/2
		]).

:- use_module(library(ugraphs),[top_sort/2,vertices_edges_to_ugraph/3]).
:- use_module(library(lists),[reverse/2]).
:- use_module(db).
:- use_module(compat_swi,[with_time_out/3]).
:- use_module(tarjan,[graph_reduce/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% tous_pos(+Vars,-Cs)                                                          

tous_pos([],[]).
tous_pos([X|Xs],[X >= 0 | PosXs]) :-tous_pos(Xs,PosXs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% not_member(+X,+L)

not_member(X,Xs) :- ntmm(Xs,X).
ntmm([],_X).
ntmm([Y|Xs],X):-X \==Y,ntmm(Xs,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% suppress_empty_constraint(+Cs,-Ds)

suppress_empty_constraint([],[]).
suppress_empty_constraint(['$constraint'([])|As],Bs) :-
	!,suppress_empty_constraint(As,Bs).
suppress_empty_constraint([A|As],[A|Bs]) :-
	suppress_empty_constraint(As,Bs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% virer_ref(+PiCls,-Pis)

virer_ref([],[]).
virer_ref([P/N-_|SccR],[P/N|PSs]) :-virer_ref(SccR,PSs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% write_list(+L)

write_list([]) :- nl.
%write_list([E]) :-!,
%        \+ \+ (    numbervars(E,0,_),
%                   print(E),nl).
write_list([E|Es]) :-
        \+ \+ (    numbervars(E,0,_),
                   print(E),
                   write('.'),
                   nl),
        write_list(Es).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% write_list_list(+Ls)

write_list_list([]).
write_list_list([Scc|Es]) :- write_scc(Scc), write_list_list(Es).

    write_scc([]).
    write_scc([_-Es|Scc]) :- write_list(Es),write_scc(Scc).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% sccs_list(+SccsClsNSpec,-ClsNSpec),
sccs_list([],[]).
sccs_list([Scc|Sccs],L) :- scc_list(Scc,L1), append(L1,L2,L), sccs_list(Sccs,L2).

    scc_list([],[]).
    scc_list([_-Es|Scc],L) :- append(Es,L1,L), scc_list(Scc,L1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% cg_db_domain_undefpred(+CallGraph,+Db,+Domain,-ListUndefPreds)
%%
% [w/1-[x/1],x/1-[]]
cg_db_domain_undefpred(CallGraph,Db,Domain,ListUndefPreds) :-
	cg_db_domain_undefpred1(CallGraph,Db,Domain,[],ListUndefPreds).

cg_db_domain_undefpred1([],_Db,_Domain,LUPs,LUPs).
cg_db_domain_undefpred1([P/N-Called|CG],Db,Domain,UndefPreds0,UndefPreds) :-
	cg_db_domain_undefpred2(Called,P,N,Db,Domain,UndefPreds0,UndefPreds1),
	cg_db_domain_undefpred1(CG,Db,Domain,UndefPreds1,UndefPreds).

cg_db_domain_undefpred2([_|_],_P,_N,_Db,_Domain,UndefPreds,UndefPreds).
cg_db_domain_undefpred2([],P,N,Db,Domain,UndefPreds0,UndefPreds1) :-
	get_db(P,N,Domain,Db,Cls),
	cg_db_domain_undefpred3(Cls,P,N,UndefPreds0,UndefPreds1).

cg_db_domain_undefpred3([],P,N,UndefPreds,[P/N|UndefPreds]).
cg_db_domain_undefpred3([_|_],_,_,UndefPreds,UndefPreds).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% sccs_db_domain_sccscls(+Pss,+Assoc,+Domain,-SccsCls).
%%

sccs_db_domain_sccscls([],_,_,[]).
sccs_db_domain_sccscls([Ps|Pss],Assoc,Domain,[SccCls|SccsCls]) :-
	scc_db_domain_scccls(Ps,Assoc,Domain,SccCls),
	sccs_db_domain_sccscls(Pss,Assoc,Domain,SccsCls).

scc_db_domain_scccls([],_,_,[]).
scc_db_domain_scccls([P/N|Pis],A,D,[P/N-Cls|PisCls]) :-
	get_db(P,N,D,A,Cls),
	scc_db_domain_scccls(Pis,A,D,PisCls).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% graph_sccs(+G,-Sccs)
%%     Sccs are the sorted (>) strongly connected components of G   

graph_sccs(G,Sccs) :-
	graph_reduce(G,R),
	top_sort(R,S),
	reverse(S,Sccs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% call_graph(+List_Cls,-G)
%% 	G is the call graph of the program List_Cls
%%	Nb: clauses are of the form: _Functor(H,List_Atoms)

call_graph(List_Cls,Graph) :-
	vertices_edges(List_Cls,[],S,[],A),
	vertices_edges_to_ugraph(S,A,Graph).
	
vertices_edges([],S,S,A,A).
vertices_edges([Cl|Cls],S1,S2,A1,A2) :-
	clause_head(Cl,H),
	functor(H,P,N),
	clause_body(Cl,Body),
	edges(Body,P,N,A1,A3),
	vertices_edges(Cls,[P/N|S1],S2,A3,A2).
	
edges([],_,_,A,A).
edges([At|Ats],P,N,A1,A2) :-
	functor(At,P2,N2),
	clean(P2,N2,P,N,A1,A3),
	edges(Ats,P,N,A3,A2).
	
clean('$predef',1,_,_,A,A) :-!.
clean('$constraint',1,_,_,A,A) :-!.
clean(P2,N2,P,N,A,[P/N-P2/N2|A]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clause_head(Cl,H) :- arg(1,Cl,H).

clause_body(Cl,B) :- arg(2,Cl,B).

build_clause(H,B,obj_clause(H,B)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% possibly_nonterm_predicates(+ListTermConds0,+LPossNonTermPred)
possibly_nonterm_predicates([],[]).
possibly_nonterm_predicates([predicate_term_condition(At,Tc)|Tcs],L) :-
	pntp(Tc,At,Tcs,L).

pntp(Z,At,Tcs,[P/N|L]) :- Z==0,!,functor(At,P,N),possibly_nonterm_predicates(Tcs,L).
pntp(_,_,Tcs,L) :- possibly_nonterm_predicates(Tcs,L).


