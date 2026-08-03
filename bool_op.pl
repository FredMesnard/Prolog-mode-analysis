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

:- module(bool_op,[
		   true/1,
		   false/1,
		   conjunction/3,
		   satisfiable/1,
		   entail/4,
		   equivalent/4,
		   union/6,
		   widening/6,
		   project/4,
           simplify_constraint/3,
           simplify_constraint_else_false/3
		  ]).

:- use_module(library(clpb)).

:- use_module(compat_swi).

:- dynamic(bool_copy/2).

%%%%
true(1).

%%%%
false(0).

%%%%
conjunction(C1,C2,C1*C2).

%%%%
check(G):- \+ \+ call(G).
	
%%%%%
satisfiable( T ):- check(sat(T)).

%%%%%
entail(Xs, S ,Ys, T ):- check( (Xs=Ys,taut(S =< T,1)) ).

%%%%%
equivalent(Xs, S ,Ys, T ):- check( (Xs=Ys, taut(S =:= T, 1)) ).
	
%%%%%
union(Xs, S ,Ys, T ,Zs, U ):-
	copy_term(e(Ys,T),e(Xs,Tcxs)),
	project(Xs,S+Tcxs,Zs,U).

%%%%% 
widening(Xs,S,Ys,T,Zs,U):-union(Xs,S,Ys,T,Zs,U).

%%%%%

project(Xs,S,Ys,T) :-
	project_brut(Xs,S,Ys,T0),
	renormalise(Ys,T0,T).

project_brut(Xs,S,_,_):-
	sat(S),
    % F
    copy_term(Xs,Ys,Bs),
    strip_bool_constraints(Bs,Cs),
    %copy_term(Xs-S,Ys-Cs),
    %asserta(bool_copy(Xs,1)),call_residue(retract(bool_copy(Ys,1)),C),gather(C,Cs),
	normalize(Ys,X1s,[],Cs,C2s),
	asserta(bool_copy(X1s,C2s)),
	fail.
project_brut(_,_,Ys, T ):-
	retract(bool_copy(Ys,T1)),
 	free_vars(T1,Ys,FreeVars),
	eliminate(FreeVars,T1,T).

%%%%%
% Re-normalisation of project/4's output.
%
% eliminate/3 does not remove the projected variables: it keeps them
% syntactically, under ^ quantifiers. For most programs this stays harmless
% (1 to 5 quantifiers), but on Filex/inorder.pl the clpb residual demands
% hundreds of auxiliary variables: the output carries up to 928 quantifiers
% while its free content never exceeds 12 variables. Every later sat/1 or
% taut/2 then has to redo the elimination over the whole term, hence 4 million
% inferences per call.
%
% So, when the shape is visibly bloated, we recompute a DNF over the free
% variables alone: the formula is posted once, then the valuations of Ys are
% enumerated under propagation (inconsistent prefixes get pruned).
%
% The DNF replaces the original with no size comparison. A first attempt
% compared node counts and only replaced when the DNF was smaller: wrong
% criterion, because what costs is not the size of the term but the number of
% quantifiers clpb must re-eliminate at every later operation. A larger but
% quantifier-FREE DNF is much better. Measured on Filex/inorder.pl: with the
% size criterion, 15 replacements out of 45 and 19.7 s; without it, 21 out of
% 21 and 12.2 s, entail dropping from 1.28 s to 0.14 s. The enumeration itself
% is negligible (0.073 s in total), and the K =< 12 guard bounds the DNF to
% 2^12 minterms.

renormalise(Ys,T0,T) :-
	(   boursoufle(Ys,T0),
	    dnf_projetee(Ys,T0,T1)
	->  T = T1
	;   T = T0
	).

% Only fires on the pathological cases: at most 12 free variables (the
% enumeration is 2^k) and more than 8 accumulated quantifiers, where a healthy
% program produces 1 to 5.
boursoufle(Ys,T0) :-
	term_variables(Ys,VYs), length(VYs,K), K =< 12,
	compte_ex(T0,NE), NE > 8.

compte_ex(T,N) :- compte_ex(T,0,N).
    compte_ex(T,A,A) :- var(T), !.
    compte_ex(_^B,A,N) :- !, A1 is A+1, compte_ex(B,A1,N).
    compte_ex(_,A,A).

taille_terme(T,1) :- (var(T) ; atomic(T)), !.
taille_terme(T,S) :-
	T =.. [_|As],
	foldl_taille(As,1,S).
    foldl_taille([],S,S).
    foldl_taille([A|As],S0,S) :- taille_terme(A,SA), S1 is S0+SA, foldl_taille(As,S1,S).

% sat/1 is posted once only, inside the findall: the valuations are then
% enumerated under the constraints, hence with pruning.
dnf_projetee(Ys,T0,T) :-
	findall(Bits, (sat(T0), valuation(Ys,Bits)), Sols),
	dnf_des_valuations(Ys,Sols,T).

valuation([],[]).
valuation([Y|Ys],[B|Bs]) :-
	(Y = 0, B = 0 ; Y = 1, B = 1),
	valuation(Ys,Bs).

dnf_des_valuations(_Ys,[],0) :- !.
dnf_des_valuations(Ys,Sols,T) :-
	maplist(minterme(Ys),Sols,Produits),
	disjonction(Produits,T).

minterme(Ys,Bits,P) :- litteraux(Ys,Bits,Ls), conjonction_lit(Ls,P).
    litteraux([],[],[]).
    litteraux([Y|Ys],[1|Bs],[Y|Ls])    :- litteraux(Ys,Bs,Ls).
    litteraux([Y|Ys],[0|Bs],[~Y|Ls])   :- litteraux(Ys,Bs,Ls).

conjonction_lit([],1).
conjonction_lit([L|Ls],P) :- conjonction_lit_(Ls,L,P).
    conjonction_lit_([],P,P).
    conjonction_lit_([L|Ls],A,P) :- conjonction_lit_(Ls,L*A,P).

disjonction([P],P) :- !.
disjonction([P|Ps],P+D) :- disjonction(Ps,D).

strip_bool_constraints([],1).
strip_bool_constraints([clpb:sat(C)],C) :- !. 
strip_bool_constraints([clpb:sat(C)|Bs],C*Cs) :- strip_bool_constraints(Bs,Cs).
    
normalize([],[],_,Cs,Cs).
normalize([X|Xs],[Y|Ys],Vars,C1s,C2s) :-
	var(X),member_var(Vars,X),!,normalize(Xs,Ys,Vars,(Y=:=X)*C1s,C2s).
normalize([X|Xs],[X|Ys],Vars,C1s,C2s) :-
	var(X),!,normalize(Xs,Ys,[X|Vars],C1s,C2s).
normalize([X|Xs],[Y|Ys],Vars,C1s,C2s) :-
	(X=0 -> Z= ~Y ;  Z=Y),
	normalize(Xs,Ys,Vars,Z*C1s,C2s).	
	

member_var([Y|_],X) :- X==Y,!.
member_var([_|Ys],X) :- member_var(Ys,X).
	
free_vars(Term,Vars,FreeVars) :- fv(Term,Vars,[],FreeVars).

fv(X,Vars,FV,FV) :- var(X), (member_var(Vars,X) ; member_var(FV,X)),!.
fv(X,_,FV,[X|FV]) :- var(X), !.
fv(X,_,FV,FV) :- atomic(X), !.
fv(X^T,Vars,FV1,FV2) :- !, fv(T,[X|Vars],FV1,FV2).
fv(~T,Vars,FV1,FV2) :- !, fv(T,Vars,FV1,FV2).
fv(T,Vars,FV1,FV2) :- T=..[_,T1,T2], fv(T1,Vars,FV1,FV3), fv(T2,Vars,FV3,FV2).
		
eliminate([],T,T).
eliminate([X|Xs],T,U):-eliminate(Xs,(X^T),U).
	

/* 

examples
	project([X,Y],(X=:=0)*(X=:=Y),A,B).
	project([X,Y],X=:=Y+Z,A,B).
	project([X,Y],(X=:=Y+Z)*(X=:=Y),A,B).
	project([X,Y],X=:=Y+a,A,B).
	project([X,Y,Z],X*Z+(Y=:=1),A,B).

*/


%simplify_constraint(A1s,A2s,_TimeOut) :- !, A2s = A1s.
simplify_constraint(A1s,A2s,TimeOut) :-    
    (satisfiable(A1s)
    -> 
        term_variables(A1s,Vars), 
        with_time_out(bool_op:project(Vars,A1s,Vars,A2s),TimeOut,Result),
        (Result=success 
        -> 
            true 
        ; 
            %writeln('% time_out bool simplify_constraint!'),
            A2s=A1s
        )
    ;
        false(A2s)
    ).


%simplify_constraint_else_false(A1s,A2s,_TimeOut) :- !, A2s = A1s.
simplify_constraint_else_false(A1s,A2s,TimeOut) :-    
    (satisfiable(A1s)
    -> 
        term_variables(A1s,Vars), 
        with_time_out(bool_op:project(Vars,A1s,Vars,A2s),TimeOut,Result),
        (Result=success 
        -> 
            true 
        ; 
            %writeln('% time_out bool simplify_constraint!'),
            false(A2s)
        )
    ;
        false(A2s)
    ).







