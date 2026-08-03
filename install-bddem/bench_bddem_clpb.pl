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

% bddem (CUDD) versus SWI-Prolog's library(clpb).
%
% Semantic bridge: if every bddem variable carries the distribution [0.5,0.5],
% then ret_prob(BDD) = (number of models) / 2^N, which we compare against
% clpb's sat_count/2 divided by 2^N.
%
% Brute-force enumeration acts as an independent third party on the small
% instances: if the two libraries agree but both differ from brute force, it
% is the bridge that is wrong, not them.

:- module(bench_bddem_clpb, [run/0, correction/0, charge/0]).

:- use_module(library(clpb)).
:- use_module(library(bddem)).
:- use_module(library(lists)).
:- use_module(library(apply)).

:- discontiguous famille/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Formulas, in a neutral representation later translated to both libraries:
% this guarantees that both receive the SAME formula.

vlist(N, Vs) :- N1 is N-1, numlist(0, N1, Is), maplist([I,v(I)]>>true, Is, Vs).

mkand([X], X) :- !.
mkand([X|Xs], and(X,R)) :- mkand(Xs, R).
mkor([X], X) :- !.
mkor([X|Xs], or(X,R)) :- mkor(Xs, R).
mkxor([X], X) :- !.
mkxor([X|Xs], xor(X,R)) :- mkxor(Xs, R).

% andchain : exactly 1 model        orchain : 2^N-1 models
% parity   : 2^(N-1) models
% pos      : a chain of X <-> Y/\Z, the very shape of the groundness
%            abstraction mode_analysis works on
% pairing  : X_i <-> X_{i+N/2}, the textbook adversarial case for a naive
%            variable order
famille(andchain, N, F) :- vlist(N, Vs), mkand(Vs, F).
famille(orchain,  N, F) :- vlist(N, Vs), mkor(Vs, F).
famille(parity,   N, F) :- vlist(N, Vs), mkxor(Vs, F).
famille(pos,      N, F) :-
    Last is N-3, numlist(0, Last, Is),
    maplist([I,iff(v(I),and(v(J),v(K)))]>>(J is I+1, K is I+2), Is, Cs),
    mkand(Cs, F).
% N must be even, otherwise the last variable does not occur in the formula
% and the two libraries would not count over the same number of variables.
famille(pairing,  N, F) :-
    0 =:= N mod 2,
    H is N // 2, pairing_cs(0, H, Cs), mkand(Cs, F).

pairing_cs(I, H, []) :- I >= H, !.
pairing_cs(I, H, [iff(v(I),v(J))|Cs]) :-
    J is I+H, I1 is I+1, pairing_cs(I1, H, Cs).

% cnf3: random 3-SAT, clause/variable ratio 2 (below the threshold, hence
% many models: the probability comparison stays informative). The linear
% congruential generator is hand-written so as to be reproducible and
% independent of SWI's RNG. The first clauses systematically cover every
% variable, so that the support of the formula really is the N variables --
% otherwise clpb would count over fewer variables than bddem.
famille(cnf3, N, F) :-
    M is max(1, round(2.0*N)),
    cnf_cover(0, N, CoverCls),
    length(CoverCls, NC),
    Rest is max(0, M-NC),
    cnf_rand(Rest, N, 987654321, RandCls),
    append(CoverCls, RandCls, Cls),
    mkand(Cls, F).

cnf_cover(I, N, []) :- I >= N, !.
cnf_cover(I, N, [or(v(A),or(v(B),v(C)))|Cls]) :-
    A = I, B is min(I+1, N-1), C is min(I+2, N-1),
    I1 is I+3, cnf_cover(I1, N, Cls).

cnf_rand(0, _N, _S, []) :- !.
cnf_rand(K, N, S0, [or(LA,or(LB,LC))|Cls]) :-
    K > 0,
    lcg(S0,S1,A,N), lcg(S1,S2,B,N), lcg(S2,S3,C,N),
    lcg(S3,S4,PA,2), lcg(S4,S5,PB,2), lcg(S5,S6,PC,2),
    lit(v(A),PA,LA), lit(v(B),PB,LB), lit(v(C),PC,LC),
    K1 is K-1, cnf_rand(K1, N, S6, Cls).

lit(V, 0, V).
lit(V, 1, not(V)).

lcg(S0, S1, V, Max) :-
    S1 is (S0*1103515245 + 12345) mod 2147483648,
    V is S1 mod Max.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Translation to clpb

to_clpb(true, _, 1).
to_clpb(false, _, 0).
to_clpb(v(I), Vs, X)         :- nth0(I, Vs, X).
to_clpb(and(A,B), Vs, X*Y)   :- to_clpb(A,Vs,X), to_clpb(B,Vs,Y).
to_clpb(or(A,B), Vs, X+Y)    :- to_clpb(A,Vs,X), to_clpb(B,Vs,Y).
to_clpb(xor(A,B), Vs, X#Y)   :- to_clpb(A,Vs,X), to_clpb(B,Vs,Y).
to_clpb(iff(A,B), Vs, X=:=Y) :- to_clpb(A,Vs,X), to_clpb(B,Vs,Y).
to_clpb(not(A), Vs, ~X)      :- to_clpb(A,Vs,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Translation to bddem (imperative construction)

% Ls: BDDs of the positive literals; Vs: multi-valued variable indices, the
% only thing exist_abstract/4 accepts (the cube is assembled on the C side).
lits_v(E, N, Ls, Vs) :- lits_v_(E, 0, N, Ls, Vs).
lits_v_(_E, I, N, [], []) :- I >= N, !.
lits_v_(E, I, N, [B|Bs], [V|Vs]) :-
    add_var(E, [0.5,0.5], 0, V), equality(E, V, 1, B),
    I1 is I+1, lits_v_(E, I1, N, Bs, Vs).

lits(E, N, Ls) :- lits_v(E, N, Ls, _).

proj_vars([], _Vs, []).
proj_vars([I|Is], Vs, [V|PVs]) :- nth0(I, Vs, V), proj_vars(Is, Vs, PVs).

to_bddem(true, E, _Ls, B)   :- one(E, B).
to_bddem(false, E, _Ls, B)  :- zero(E, B).
to_bddem(v(I), _E, Ls, B)   :- nth0(I, Ls, B).
to_bddem(and(A,B), E, Ls, C):- to_bddem(A,E,Ls,X), to_bddem(B,E,Ls,Y), and(E,X,Y,C).
to_bddem(or(A,B), E, Ls, C) :- to_bddem(A,E,Ls,X), to_bddem(B,E,Ls,Y), or(E,X,Y,C).
to_bddem(not(A), E, Ls, C)  :- to_bddem(A,E,Ls,X), bdd_not(E,X,C).
to_bddem(xor(A,B), E, Ls, C):-
    to_bddem(A,E,Ls,X), to_bddem(B,E,Ls,Y),
    bdd_not(E,X,NX), bdd_not(E,Y,NY),
    and(E,X,NY,P1), and(E,NX,Y,P2), or(E,P1,P2,C).
to_bddem(iff(A,B), E, Ls, C):- to_bddem(xor(A,B),E,Ls,X), bdd_not(E,X,C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Brute force: the independent third party

brute(F, N, Count) :-
    Max is (1<<N)-1,
    aggregate_all(count, (between(0,Max,Bits), eval(F,Bits)), Count).

eval(true, _Bits).
eval(false, _Bits) :- fail.
eval(v(I), Bits)     :- (Bits >> I) /\ 1 =:= 1.
eval(and(A,B), Bits) :- eval(A,Bits), eval(B,Bits).
eval(or(A,B), Bits)  :- (eval(A,Bits) -> true ; eval(B,Bits)).
eval(not(A), Bits)   :- \+ eval(A,Bits).
eval(xor(A,B), Bits) :- (eval(A,Bits) -> \+ eval(B,Bits) ; eval(B,Bits)).
eval(iff(A,B), Bits) :- (eval(A,Bits) -> eval(B,Bits) ; \+ eval(B,Bits)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Measurements

chrono(Goal, Ms, Res) :-
    statistics(walltime, [T0,_]),
    (   catch(call_with_time_limit(10, Goal), E, true)
    ->  (var(E) -> Res = ok ; Res = erreur(E))
    ;   Res = echec
    ),
    statistics(walltime, [T1,_]),
    Ms is T1-T0.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Timing by repetition.
%
% statistics(walltime,...) has millisecond resolution: a single reading of
% 0, 1 or 2 ms is nothing but resolution noise and supports no ratio. So we
% repeat the goal until the total reaches at least 200 ms, then divide.
%
% Absolute rule: a failure or an exception must NEVER come out as a short
% time. That is exactly how one ends up timing an exception (sat_count/2
% invisible from the current module, say) while believing a computation was
% measured.

chrono_rep(Goal, Ms, Iters, Res) :- chrono_rep_(Goal, 1, Ms, Iters, Res).

chrono_rep_(Goal, N, Ms, Iters, Res) :-
    statistics(walltime, [T0,_]),
    (   catch(call_with_time_limit(20, forall(between(1,N,_), Goal)), E, true)
    ->  (var(E) -> R = ok ; R = erreur(E))
    ;   R = echec
    ),
    statistics(walltime, [T1,_]),
    Total is T1-T0,
    (   R \== ok      -> Res = R,  Iters = N, Ms = -1.0
    ;   Total >= 200  -> Res = ok, Iters = N, Ms is Total/N
    ;   N >= 200000   -> Res = ok, Iters = N, Ms is Total/N
    ;   N2 is max(4, N*4), chrono_rep_(Goal, N2, Ms, Iters, Res)
    ).

mesure_clpb_r(F, N, Ms, It, P, Res) :-
    chrono_rep(( length(Vs,N), to_clpb(F,Vs,Expr), sat_count(Expr,C),
                 nb_setval(cnt,C) ), Ms, It, Res),
    (Res == ok -> nb_getval(cnt,C0), P is float(C0 rdiv (1<<N)) ; P = '-').

mesure_bddem_r(F, N, Ms, It, P, Res) :-
    chrono_rep(( init(E), lits(E,N,Ls), to_bddem(F,E,Ls,B),
                 ret_prob(E,B,P0), end(E), nb_setval(prb,P0) ), Ms, It, Res),
    (Res == ok -> nb_getval(prb,P) ; P = '-').

% Same measurement, but pinning CUDD's dynamic reordering method.
% init/1 starts in group_sift; set_reordering(E,none) switches it off.
mesure_bddem_ro_r(F, N, Methode, Ms, It, P, Res) :-
    chrono_rep(( init(E), set_reordering(E,Methode),
                 lits(E,N,Ls), to_bddem(F,E,Ls,B),
                 ret_prob(E,B,P0), end(E), nb_setval(prbr,P0) ), Ms, It, Res),
    (Res == ok -> nb_getval(prbr,P) ; P = '-').

% NATIVE projection: the original formula is built once, then quantified
% directly on the BDD via exist_abstract/4 (Cudd_bddExistAbstract).
mesure_bddem_exist_r(F, N, Is, Ms, It, P, Res) :-
    chrono_rep(( init(E), lits_v(E,N,Ls,Vs), to_bddem(F,E,Ls,B),
                 proj_vars(Is,Vs,PVs), exist_abstract(E,B,PVs,G),
                 ret_prob(E,G,P0), end(E), nb_setval(prbx,P0) ), Ms, It, Res),
    (Res == ok -> nb_getval(prbx,P) ; P = '-').

mesure_clpb(F, N, Ms, P, Res) :-
    chrono(( length(Vs,N), to_clpb(F,Vs,Expr), sat_count(Expr,C),
             nb_setval(cnt, C) ), Ms, Res),
    (   Res == ok
    ->  nb_getval(cnt, C0), P is float(C0 rdiv (1<<N))
    ;   P = '-'
    ).

mesure_bddem(F, N, Ms, P, Res) :-
    chrono(( init(E), lits(E,N,Ls), to_bddem(F,E,Ls,B),
             ret_prob(E,B,P0), end(E), nb_setval(prb, P0) ), Ms, Res),
    (Res == ok -> nb_getval(prb, P) ; P = '-').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Part 1: cross-checking (small instances, brute force still feasible)

correction :-
    format('~n=== CORRECTION : bddem vs clpb vs force brute ===~n~n'),
    format('~w~t~12| ~w~t~16| ~w~t~30| ~w~t~44| ~w~t~58| ~w~n',
           ['famille','N','bddem','clpb','force brute','accord']),
    format('~`-t~66|~n'),
    forall(( member(Fam,[andchain,orchain,parity,pos,pairing]),
             member(N,[4,8,12]) ),
           correction_cas(Fam,N)),
    format('~n').

correction_cas(Fam, N) :-
    famille(Fam, N, F),
    mesure_bddem(F, N, _, Pb, Rb),
    mesure_clpb(F, N, _, Pc, Rc),
    brute(F, N, Cbrute),
    Pbrute is float(Cbrute rdiv (1<<N)),
    (   Rb == ok, Rc == ok,
        abs(Pb-Pc) < 1.0e-9, abs(Pb-Pbrute) < 1.0e-9
    ->  Accord = 'OUI'
    ;   Accord = '*** NON ***'
    ),
    format('~w~t~12| ~w~t~16| ~4f~t~30| ~4f~t~44| ~4f~t~58| ~w~n',
           [Fam,N,Pb,Pc,Pbrute,Accord]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Part 2: scaling up (no brute force, too expensive)

charge :-
    format('~n=== MONTEE EN CHARGE (ms par iteration, repete jusqu a 200 ms) ===~n~n'),
    format('~w~t~12| ~w~t~18| ~w~t~34| ~w~t~50| ~w~t~60| ~w~n',
           ['famille','N','bddem','clpb','clpb/bddem','accord']),
    format('~`-t~72|~n'),
    forall(( member(Fam-Ns,[ andchain-[200],
                             orchain-[200],
                             pairing-[40],
                             parity-[100,200,400,800],
                             pos-[100,200,400,800],
                             cnf3-[20,30,40] ]),
             member(N,Ns) ),
           charge_cas(Fam,N)),
    format('~n').

charge_cas(Fam, N) :-
    famille(Fam, N, F),
    mesure_bddem_r(F, N, Mb, Ib, Pb, Rb),
    mesure_clpb_r(F, N, Mc, Ic, Pc, Rc),
    (   Rb == ok, Rc == ok
    ->  (abs(Pb-Pc) < 1.0e-9 -> A = 'OUI' ; A = '*** NON ***')
    ;   A = '-'
    ),
    etiq(Rb, Mb, Ib, Eb), etiq(Rc, Mc, Ic, Ec),
    (   Rb == ok, Rc == ok, Mb > 0
    ->  Rap is Mc/Mb, format(atom(RapA), '~2fx', [Rap])
    ;   RapA = '-'
    ),
    format('~w~t~12| ~w~t~18| ~w~t~34| ~w~t~50| ~w~t~60| ~w~n',
           [Fam,N,Eb,Ec,RapA,A]).

% Prints "ms/iter (n=iterations)": the repetition count makes it visible
% whether the measurement rose above resolution noise or not.
etiq(ok, Ms, It, A) :- !, format(atom(A), '~4f (n=~w)', [Ms,It]).
etiq(erreur(time_limit_exceeded), _, _, '>20 s') :- !.
etiq(erreur(E), _, _, A) :- !, format(atom(A), 'ERREUR ~w', [E]).
etiq(echec, _, _, 'ECHEC').

etiquette(ok, Ms, Ms) :- !.
etiquette(erreur(time_limit_exceeded), _, '>10000') :- !.
etiquette(erreur(_), _, 'ERREUR') :- !.
etiquette(echec, _, 'ECHEC').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Part 3: projection by Shannon expansion
%
%   exists x. F(x)  <=>  F(0) ou F(1)
%
% The identity derives existential quantification from the operations bddem
% does have (or/4), WITHOUT Cudd_bddExistAbstract. But here it can only be
% applied at the TERM level, no cofactor being exposed on the BDD: every
% eliminated variable DOUBLES the size of the formula, hence a 2^k cost for
% k projected variables. That is what this section measures.

subst(true,  _I, _C, true)  :- !.
subst(false, _I, _C, false) :- !.
subst(v(I),   I,  C, C)     :- !.
subst(v(J),  _I, _C, v(J))  :- !.
subst(not(A), I, C, not(A1))       :- !, subst(A,I,C,A1).
subst(and(A,B), I, C, and(A1,B1))  :- !, subst(A,I,C,A1), subst(B,I,C,B1).
subst(or(A,B),  I, C, or(A1,B1))   :- !, subst(A,I,C,A1), subst(B,I,C,B1).
subst(xor(A,B), I, C, xor(A1,B1))  :- !, subst(A,I,C,A1), subst(B,I,C,B1).
subst(iff(A,B), I, C, iff(A1,B1))  :- !, subst(A,I,C,A1), subst(B,I,C,B1).

existe(I, F, or(F0,F1)) :- subst(F,I,false,F0), subst(F,I,true,F1).

existe_list([], F, F).
existe_list([I|Is], F, G) :- existe(I, F, F1), existe_list(Is, F1, G).

% Wraps Expr in clpb's native ^ quantifiers, over the REAL variables of Vs.
% Written as explicit recursion: with foldl + yall, Vs would be a free
% variable of the lambda, hence copied, and we would quantify over fresh
% variables absent from the formula -- a silent error inflating sat_count by
% 2^k.
quantifie([], _Vs, Expr, Expr).
quantifie([I|Is], Vs, Expr, V^Q) :-
    nth0(I, Vs, V),
    quantifie(Is, Vs, Expr, Q).

taille(true, 1) :- !.
taille(false, 1) :- !.
taille(v(_), 1) :- !.
taille(not(A), S) :- !, taille(A,S1), S is S1+1.
taille(T, S) :- T =.. [_,A,B], taille(A,S1), taille(B,S2), S is S1+S2+1.

% Arbiter: cylindrification by brute force, independent of the identity.
brute_existe(F, Is, N, Count) :-
    Max is (1<<N)-1,
    aggregate_all(count, (between(0,Max,Bits), sat_existe(F,Is,Bits)), Count).

sat_existe(F, Is, Bits) :-
    length(Is, K), Kmax is (1<<K)-1,
    between(0, Kmax, Masque),
    pose_bits(Is, Masque, Bits, Bits2),
    eval(F, Bits2), !.

pose_bits([], _M, Bits, Bits).
pose_bits([I|Is], M, Bits0, Bits) :-
    B is M /\ 1, M1 is M>>1,
    (B =:= 1 -> Bits1 is Bits0 \/ (1<<I) ; Bits1 is Bits0 /\ \(1<<I)),
    pose_bits(Is, M1, Bits1, Bits).

projection :-
    format('~n=== PROJECTION : 4 methodes confrontees ===~n~n'),
    format('~w~t~9| ~w~t~14| ~w~t~20| ~w~t~32| ~w~t~44| ~w~t~56| ~w~t~68| ~w~n',
           ['famille','N','k','bddem natif','bddem Shannon','clpb ^',
            'force brute','accord']),
    format('~`-t~78|~n'),
    forall(( member(Fam,[pos,cnf3]), member(N,[10,12]), member(K,[1,2,3,4]) ),
           projection_cas(Fam,N,K)),
    format('~n').

projection_cas(Fam, N, K) :-
    famille(Fam, N, F),
    K1 is K-1, numlist(0, K1, Is),          % on projette v(0)..v(K-1)
    % 1. bddem, quantification NATIVE sur le BDD
    mesure_bddem_exist_r(F, N, Is, _, _, Px, Rx),
    % 2. bddem, expansion de Shannon au niveau du terme
    existe_list(Is, F, G),
    mesure_bddem_r(G, N, _, _, Pb, Rb),
    % 3. clpb, quantificateur natif ^
    (   catch(( length(Vs,N), to_clpb(F,Vs,Expr),
                quantifie(Is, Vs, Expr, QExpr),
                sat_count(QExpr, Cc), Pc is float(Cc rdiv (1<<N)) ), _, fail)
    ->  true ; Pc = -1.0 ),
    % 4. independent arbiter
    brute_existe(F, Is, N, Cbr), Pbr is float(Cbr rdiv (1<<N)),
    (   Rx == ok, Rb == ok,
        abs(Px-Pbr) < 1.0e-9, abs(Pb-Pbr) < 1.0e-9, abs(Pc-Pbr) < 1.0e-9
    ->  A = 'OUI' ; A = '*** NON ***' ),
    format('~w~t~9| ~w~t~14| ~w~t~20| ~4f~t~32| ~4f~t~44| ~4f~t~56| ~4f~t~68| ~w~n',
           [Fam,N,K,Px,Pb,Pc,Pbr,A]).

% Cost of projection: term-level Shannon (bddem) against clpb's native ^
% quantifier, which operates on the BDD.
% Everything must stay INSIDE this module: sat_count/2 is only visible from
% here, and calling it from user raises an existence_error that a careless
% timer would report as a very fast computation.
cout_projection :-
    format('~n=== COUT DE LA PROJECTION (ms par iteration) ===~n~n'),
    format('~w~t~5| ~w~t~20| ~w~t~40| ~w~t~62| ~w~n',
           ['k','taille formule','bddem natif','bddem Shannon','clpb ^']),
    format('~`-t~84|~n'),
    famille(pos, 20, F),
    forall(member(K,[1,4,8,12,14,16]), cout_projection_cas(F,20,K)),
    format('~n').

cout_projection_cas(F, N, K) :-
    K1 is K-1, numlist(0, K1, Is),
    % native: the original formula, quantified on the BDD -- no expansion
    mesure_bddem_exist_r(F, N, Is, Mx, Ix, _, Rx),
    etiq(Rx, Mx, Ix, Ex),
    chrono_rep(( length(Vs,N), to_clpb(F,Vs,E), quantifie(Is,Vs,E,QE),
                 sat_count(QE,_) ), Mc, Ic, Rc),
    etiq(Rc, Mc, Ic, Ec),
    (   catch(call_with_time_limit(30,
              (existe_list(Is,F,G), taille(G,T))), _, fail)
    ->  mesure_bddem_r(G, N, Mb, Ib, _, Rb), etiq(Rb,Mb,Ib,Eb)
    ;   T = '>30 s', Eb = '-'
    ),
    format('~w~t~5| ~w~t~20| ~w~t~40| ~w~t~62| ~w~n', [K,T,Ex,Eb,Ec]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Part 5: effect of CUDD's dynamic reordering
%
% init/1 unconditionally enables CUDD_REORDER_GROUP_SIFT. Sifting fires on
% node-count thresholds reached during construction, so its cost depends on
% when it trips, which produces times that are non-monotonic in N.
% set_reordering/2 finally allows that hypothesis to be checked, by switching
% it off.

reordonnancement :-
    format('~n=== EFFET DU REORDONNANCEMENT DYNAMIQUE (ms par iteration) ===~n~n'),
    format('~w~t~10| ~w~t~16| ~w~t~36| ~w~t~56| ~w~t~74| ~w~n',
           ['famille','N','group_sift (defaut)','none','clpb','accord']),
    format('~`-t~86|~n'),
    forall(( member(Fam-Ns,[ pos-[400,500,600,700,800,1000],
                             pairing-[20,30,40],
                             parity-[400,800],
                             cnf3-[20,30] ]),
             member(N,Ns) ),
           reordonnancement_cas(Fam,N)),
    format('~n').

reordonnancement_cas(Fam, N) :-
    famille(Fam, N, F),
    mesure_bddem_ro_r(F, N, group_sift, Mg, Ig, Pg, Rg),
    mesure_bddem_ro_r(F, N, none,       Mn, In, Pn, Rn),
    mesure_clpb_r(F, N, Mc, Ic, Pc, Rc),
    (   Rg == ok, Rn == ok, Rc == ok,
        abs(Pg-Pn) < 1.0e-9, abs(Pg-Pc) < 1.0e-9
    ->  A = 'OUI' ; A = '*** NON ***' ),
    etiq(Rg,Mg,Ig,Eg), etiq(Rn,Mn,In,En), etiq(Rc,Mc,Ic,Ec),
    format('~w~t~10| ~w~t~16| ~w~t~36| ~w~t~56| ~w~t~74| ~w~n',
           [Fam,N,Eg,En,Ec,A]).

run :- correction, charge, projection, cout_projection, reordonnancement.
