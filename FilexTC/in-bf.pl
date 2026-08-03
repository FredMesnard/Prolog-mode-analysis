%query: in(i,o).
%% in(Element, Tree) :- Element is an element of the search tree Tree.
%%

%TWTYPES  :- type in(nat,treen).

in(X, tree(X, _, _)).
in(X, tree(Y, Left, _)) :- less(X,Y), in(X, Left).
in(X, tree(Y, _, Right)) :- less(Y,X), in(X, Right).


%TWTYPES     :- type less(nat,nat).

less(0, s(_)).
less(s(X), s(Y)) :- less(X, Y).



/*
% ?- mode_analysis('FilexTC/in-bf.pl',M).
% M = [less(i, o), less(o, i), in(i, o)].

less_io(0,s(_)).
less_io(s(X),s(Y)) :- less_io(X,Y).

less_oi(0,s(_)).
less_oi(s(X),s(Y)) :- less_oi(X,Y).

in_io(X, tree(X, _, _)).
in_io(X, tree(Y, Left, _)) :- less_io(X,Y), in_io(X, Left).
in_io(X, tree(Y, _, Right)) :- less_oi(Y,X), in_io(X, Right).

*/

/*TWDESC

 in(Element, Tree) :- Element is an element of the search tree Tree.

*/


/*TWTYPES

treen(void).
treen(tree(V,L,R)) :-
        nat(V),
        treen(L),
        treen(R).

nat(0).
nat(s(X)) :- nat(X).

*/


/*TWDEMO

selected_norms([nat,treen]).

query(in(b,f,b,f)).
query(in(b,f,f,b)).
query(in(f,f,b,f)).
query(less(b,f,f,f)).
query(less(f,f,b,f)).

*/
