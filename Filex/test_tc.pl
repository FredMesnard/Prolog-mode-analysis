%query: p(o,o).
%p(X,Y) :- cti:{tc(0)}.

%p(X) :- X is 2.

p(X,X) :- q(X).
q(_).