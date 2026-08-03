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

:- module(tarjan,[graph_reduce/2, tarjan_sccs/2]).

% Strongly connected components and the reduced graph (condensation), by
% Tarjan's algorithm.
%
% Written from scratch to replace the version that used to sit in
% compat_swi.pl, whose distribution terms were unclear. Same input and output
% contract, checked by comparison on the call graphs of the corpus.
%
% Input  : a ugraph, a sorted list of Vertex-Neighbours, neighbours sorted,
%          every vertex appearing as a key.
% Output : a ugraph whose vertices are the SCCs (sorted lists of original
%          vertices) and whose edges join two distinct SCCs.
%
% ?- tarjan:graph_reduce([1-[2],2-[1,3],3-[4],4-[3],5-[],6-[]],L).
% L = [[1,2]-[[3,4]], [3,4]-[], [5]-[], [6]-[]].

:- use_module(library(assoc)).
:- use_module(library(ugraphs),[vertices_edges_to_ugraph/3, top_sort/2]).
:- use_module(library(lists)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% graph_reduce(+Graph, -Reduced)

graph_reduce(Graph, Reduced) :-
	tarjan_sccs(Graph, Sccs),
	sommet_scc(Sccs, Table, []),     % the list must be CLOSED here:
	list_to_assoc(Table, Map),       % list_to_assoc/2 keysorts its argument
	aretes(Graph, Map, Aretes0),
	sort(Aretes0, Aretes),
	vertices_edges_to_ugraph(Sccs, Aretes, Reduced).

% Vertex -> containing SCC table, built as a difference list then poured into
% an assoc.
sommet_scc([], T, T).
sommet_scc([Scc|Sccs], T0, T) :-
	sommet_scc_(Scc, Scc, T0, T1),
	sommet_scc(Sccs, T1, T).

    sommet_scc_([], _Scc, T, T).
    sommet_scc_([V|Vs], Scc, [V-Scc|T0], T) :- sommet_scc_(Vs, Scc, T0, T).

% One reduced-graph edge per original edge joining two distinct SCCs;
% duplicates are dropped by the caller's sort/2.
aretes([], _Map, []).
aretes([V-Ns|G], Map, As) :-
	get_assoc(V, Map, Sv),
	aretes_(Ns, Sv, Map, As, As1),
	aretes(G, Map, As1).

    aretes_([], _Sv, _Map, As, As).
    aretes_([W|Ws], Sv, Map, As0, As) :-
	(   get_assoc(W, Map, Sw), Sw \== Sv
	->  As0 = [Sv-Sw|As1]
	;   As0 = As1
	),
	aretes_(Ws, Sv, Map, As1, As).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tarjan_sccs(+Graph, -Sccs)
%
% Sccs is the list, sorted in standard order, of the strongly connected
% components, each one a sorted list of vertices.
%
% State threaded throughout: etat(Index, Info, Stack, Sccs), where Info maps
% each visited vertex to a term info(Index, Lowlink, OnStack).

tarjan_sccs(Graph, Sccs) :-
	list_to_assoc(Graph, GA),
	empty_assoc(A0),
	racines(Graph, GA, etat(0,A0,[],[]), etat(_,_,_,Sccs0)),
	sort(Sccs0, Sccs).

% Every not-yet-visited vertex is the root of one traversal.
racines([], _GA, S, S).
racines([V-_|G], GA, S0, S) :-
	S0 = etat(_,A,_,_),
	(   get_assoc(V, A, _)
	->  S1 = S0
	;   parcours(V, GA, S0, S1)
	),
	racines(G, GA, S1, S).

parcours(V, GA, etat(I0,A0,Pile0,Sc0), S) :-
	I1 is I0+1,
	put_assoc(V, A0, info(I0,I0,true), A1),
	voisins(GA, V, Ns),
	voisins_de(Ns, V, GA, etat(I1,A1,[V|Pile0],Sc0), etat(I2,A2,Pile1,Sc1)),
	get_assoc(V, A2, info(Iv,Lv,_)),
	(   Lv =:= Iv                      % V is the root of its component
	->  depiler(Pile1, V, A2, [], Scc, Pile2, A3),
	    S = etat(I2,A3,Pile2,[Scc|Sc1])
	;   S = etat(I2,A2,Pile1,Sc1)
	).

    % A vertex whose adjacency is missing from the graph is treated as
    % isolated, rather than failing the whole traversal.
    voisins(GA, V, Ns) :- (get_assoc(V, GA, Ns0) -> Ns = Ns0 ; Ns = []).

voisins_de([], _V, _GA, S, S).
voisins_de([W|Ws], V, GA, S0, S) :-
	arc(W, V, GA, S0, S1),
	voisins_de(Ws, V, GA, S1, S).

arc(W, V, GA, S0, S) :-
	S0 = etat(_,A,_,_),
	(   get_assoc(W, A, info(Iw,_,SurPile))
	->  (   SurPile == true            % W is in the component being built
	    ->  abaisser(V, Iw, S0, S)
	    ;   S = S0                     % W belongs to an already closed SCC
	    )
	;   parcours(W, GA, S0, S1),       % W never visited
	    S1 = etat(_,A1,_,_),
	    get_assoc(W, A1, info(_,Lw,_)),
	    abaisser(V, Lw, S1, S)
	).

% Lowlink(V) <- min(Lowlink(V), N)
%
% Read first, write only when the value actually drops. get_assoc/5 looks
% tempting here, but it builds the replacement tree unconditionally, and the
% common case is the one where nothing changes. Measured: slightly slower.
abaisser(V, N, etat(I,A0,Pile,Sc), etat(I,A,Pile,Sc)) :-
	get_assoc(V, A0, info(Iv,Lv,Ov)),
	(   N < Lv
	->  put_assoc(V, A0, info(Iv,N,Ov), A)
	;   A = A0
	).

% Pop up to and including V: those vertices form one component.
depiler([W|Pile], V, A0, Acc, Scc, Pile2, A) :-
	get_assoc(W, A0, info(Iw,Lw,_), A1, info(Iw,Lw,false)),
	(   W == V
	->  msort([W|Acc], Scc), Pile2 = Pile, A = A1
	;   depiler(Pile, V, A1, [W|Acc], Scc, Pile2, A)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The first case comes with the implementation this one replaced; the others
% are the edge cases the two were compared on.
% ?- use_module(tarjan), run_tests.

:- begin_tests(tarjan).

test(sedgewick, [true(L == [[1,2]-[[3,4]], [3,4]-[], [5]-[], [6]-[]])]) :-
	graph_reduce([1-[2],2-[1,3],3-[4],4-[3],5-[],6-[]], L).

test(vide,        [true(L == [])])                    :- graph_reduce([], L).
test(isole,       [true(L == [[a]-[]])])              :- graph_reduce([a-[]], L).
test(boucle,      [true(L == [[a]-[]])])              :- graph_reduce([a-[a]], L).
test(paire,       [true(L == [[a,b]-[]])])            :- graph_reduce([a-[b],b-[a]], L).
test(cycle3,      [true(L == [[a,b,c]-[]])])          :- graph_reduce([a-[b],b-[c],c-[a]], L).
test(chaine,      [true(L == [[a]-[[b]], [b]-[], [c]-[[a]]])]) :-
	graph_reduce([a-[b],b-[],c-[a]], L).
test(losange,     [true(L == [[1,2,3,4]-[], [5]-[]])]) :-
	graph_reduce([1-[2,3],2-[4],3-[4],4-[1],5-[5]], L).
test(vers_cycle,  [true(L == [[x]-[[y,z]], [y,z]-[]])]) :-
	graph_reduce([x-[y],y-[z],z-[y]], L).

% The output must stay a well-formed ugraph: top_sort/2 requires it.
test(top_sort_accepte) :-
	graph_reduce([1-[2],2-[1,3],3-[4],4-[3],5-[],6-[]], L),
	top_sort(L, S),
	length(S, 4).

:- end_tests(tarjan).
