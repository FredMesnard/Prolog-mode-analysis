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

:- module(bool_clph_bool,[clphs_clpbs/2]).

:- use_module(utils).
:- use_module(predef,[predef_nat_bool_tc/4]).

    
clphs_clpbs(ClpHClauses,ClpBClauses) :-
    h_bool(ClpHClauses,ClpBClauses).
    
h_bool([],[]).
h_bool([ClpH|ClpHs],[ClpB|ClpBs]) :-
	clause_head(ClpH,Head),
	clause_body(ClpH,Bs),
	h_bool_body(Bs,Bs3),
	build_clause(Head,Bs3,ClpB),
	h_bool(ClpHs,ClpBs).

% clause_head(Cl,H) :- arg(1,Cl,H).
% clause_body(Cl,B) :- arg(2,Cl,B).
% build_clause(H,B,obj_clause(H,B)).

h_bool_body([],[]).
h_bool_body(['$constraint'(Cs)|Bs],['$constraint'(Cbs)|Es]) :-
	!,nb_eqs(Cs,Cbs),
	h_bool_body(Bs,Es).
h_bool_body(['$predef'(A)|Bs],['$predef'(A),'$constraint'(Ba)|Ds]) :-
	!,predef_bool(A,Ba),
    h_bool_body(Bs,Ds).
h_bool_body([B|Bs],[B|Ds]) :-
	h_bool_body(Bs,Ds).

nb_eqs([],1).
nb_eqs([A=Term|Eqs],C*Cs) :-
    term_variables(Term,Vars),
    bool_product(Vars,P),
    C = (A=:=P),
	nb_eqs(Eqs,Cs).

bool_product([],1).
bool_product([X|Xs],X*P) :- 
    bool_product(Xs,P).
    
predef_bool(A=B,BC) :- !,
    term_variables(A,Va),
    bool_product(Va,Pa),
    term_variables(B,Vb),
    bool_product(Vb,Pb),
    BC = (Pa=:=Pb). 
predef_bool(E is _, E) :- !.   
predef_bool('$num'(_),1) :- !.
predef_bool('$bool'(B),B) :- !.
% Every other built-in: its Boolean meaning is in the predef.pl table.  Without
% this clause they all fell through to the catch-all below -- hence `1', no
% information -- and mode analysis never consulted the table at all.  Groundness
% therefore crossed neither functor/3 nor =../2 nor atom_length/2 nor any of the
% rest.  Only =/2 came through, and not by this route: CLP(H) normalisation
% turns it into a constraint before it ever reaches here.
% A's arguments are distinct fresh variables at this point (step 3,
% prolog_clph:flatprologs_clphs/2), so unifying with the table's pattern binds
% the returned formula to the clause's own variables.
predef_bool(A,BC) :- predef_nat_bool_tc(A,_,BC,_), !.
predef_bool(_,1).

