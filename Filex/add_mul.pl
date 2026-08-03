%OI:- use_package(sr/bfall).

%query: mul(i,i,o).


add(0,Y,Y).
add(s(X),Y,s(Z)) :- add(X,Y,Z).

mul(0,_Y,0).
mul(s(X),Y,Z) :- mul(X,Y,T), add(Y,T,Z).