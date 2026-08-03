%query: pair(i).

%pair(0).
pair(s(X)) :- impair(X).

impair(s(X)) :- pair(X).

%pi(X) :- pair(X), impair(X).