%query: qs(i,o).

/*
% [qs(i,o),part(i,i,o,o),app(i,i,o),less(i,i)]
entry_part(A,B):-{B-C>=1,C>=0,A>=0},entry_part(A,C).
entry_less(D,E):-{F= -1+E,E>=1,G= -1+D,D>=1},entry_less(G,F).
entry_part(A,B):-{H>=0,A-B+H=< -2,A>=0},entry_part(A,H).
entry_app(I,J):-{J>=0,I-K>=1,K>=0},entry_app(K,J).
entry_qs(L):-{L-M>=1,M>=0},entry_qs(M).
entry_qs(L):-{L-N>=1,N>=0},entry_qs(N).
*/


%% qs(Xs, Ys) :- Ys is an ordered permutation of the list Xs.
%%

%TWTYPES     :- type qs(listn,listn).

qs([], []).
qs([X | Xs], Ys) :-
	part(X, Xs, Littles, Bigs),
	qs(Littles, Ls),
	qs(Bigs, Bs),
	app(Ls, [X | Bs], Ys).

%TWTYPES     :- type part(nat,listn,listn,listn).

part(X, [Y | Xs], [Y | Ls], Bs) :-  less(X,Y), part(X, Xs, Ls, Bs).
part(X, [Y | Xs], Ls, [Y | Bs]) :-  part(X, Xs, Ls, Bs).
part(_, [], [], []).


%TWTYPES     :- type app(listn,listn,listn).

app([],X,X).
app([X|Xs],Ys,[X|Zs]) :-
	app(Xs,Ys,Zs).

%TWTYPES :- type less(nat,nat).

less(0, s(_)).
less(s(X), s(Y)) :- less(X, Y).


/*TWDESC

qs(Xs, Ys) :- Ys is an ordered permutation of the list Xs.

*/


/*TWTYPES

listn([]).
listn([X|Xs]) :-
        nat(X),
        listn(Xs).

nat(0).
nat(s(X)) :- nat(X).

*/


/*TWDEMO

selected_norms([listn,nat]).

query(app(b,f,f,f,f,f)).
query(app(f,b,f,f,f,f)).
query(app(f,f,f,f,b,f)).
query(app(f,f,f,f,f,b)).
query(part(f,f,b,f,f,f,f,f)).
query(part(f,f,f,b,f,f,f,f)).
query(part(f,f,f,f,b,f,b,f)).
query(part(f,f,f,f,b,f,f,b)).
query(part(f,f,f,f,f,b,b,f)).
query(part(f,f,f,f,f,b,f,b)).
query(qs(b,f,f,f)).
query(qs(f,b,f,f)).
query(less(f,b,f,f)).
query(less(f,f,f,b)).

*/
