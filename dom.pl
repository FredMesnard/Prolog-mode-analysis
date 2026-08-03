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

:- module(dom,[
	       set_domain/1,
	       current_domain/1,
	       true/1,
	       false/1,
	       conjunction/3,
	       satisfiable/1,
	       entail/4,
	       equivalent/4,
	       union/6,
	       widening/6,
	       project/4
	      ]).

% Boolean abstract domain selection.
%
% mode_analysis.pl used to call bool_op directly; it now goes through here, so
% that switching implementations touches nothing in the analysis itself.
% bool_itp.pl already took its domain as a parameter: mode_analysis simply
% passes current_domain/1 down to it.
%
% The default stays bool_op (clpb): nothing changes for an existing call.
%
% ?- dom:set_domain(bddem_op).
% ?- dom:set_domain(bool_op).

:- use_module(bool_op,[]).
:- use_module(bddem_op,[bddem_available/0]).

:- dynamic domaine/1.

domaine(bool_op).

set_domain(M) :-
	(   \+ memberchk(M,[bool_op,bddem_op])
	->  write('% unknown domain: '),write(M),nl,
	    write('% possible values: bool_op, bddem_op'),nl,
	    fail
	;   M == bddem_op, \+ bddem_available
	->  write('% domain bddem_op needs the bddem pack, with the two local'),nl,
	    write('% additions exist_abstract/4 and set_reordering/2.'),nl,
	    write('% Run install-bddem/fix-bddem.sh, then retry.'),nl,
	    fail
	;   retractall(domaine(_)),
	    assertz(domaine(M))
	).

current_domain(M) :- domaine(M).

% Dispatch. The meta-call overhead is the same for both domains, so the
% comparison stays fair; it does however add to bool_op's timing relative to
% the unmodified analysis. Measured at 0.5%, i.e. within noise.
true(X)                 :- domaine(M), M:true(X).
false(X)                :- domaine(M), M:false(X).
conjunction(A,B,C)      :- domaine(M), M:conjunction(A,B,C).
satisfiable(C)          :- domaine(M), M:satisfiable(C).
entail(Xs,S,Ys,T)       :- domaine(M), M:entail(Xs,S,Ys,T).
equivalent(Xs,S,Ys,T)   :- domaine(M), M:equivalent(Xs,S,Ys,T).
union(Xs,S,Ys,T,Zs,U)   :- domaine(M), M:union(Xs,S,Ys,T,Zs,U).
widening(Xs,S,Ys,T,Zs,U):- domaine(M), M:widening(Xs,S,Ys,T,Zs,U).
project(Xs,S,Ys,T)      :- domaine(M), M:project(Xs,S,Ys,T).
