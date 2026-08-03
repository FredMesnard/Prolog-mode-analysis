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

:- module(flag,[current_ma_flag/2,set_ma_flag/2]).

:- use_module(predef).

:- dynamic(current_ma_flag/2).

% default values for flags
current_ma_flag(version,'2.0').
current_ma_flag(process_include_ensure_loaded,no).
current_ma_flag(time_out,10).  % in seconds
current_ma_flag(nb_ite_clpn,4).
current_ma_flag(print_info,yes).
current_ma_flag(poly_lib,poly_clpq).
current_ma_flag(size,term_size).
current_ma_flag(known_predicate,PI) :-
	(var(PI) ->
	    predef(Atom),
	    functor(Atom,P,N),
	    PI=P/N
	;
	    (ground(PI) ->
		PI=P/N,
		functor(Atom,P,N),
		predef(Atom))).

% update value for flag
set_ma_flag(X,_) :- var(X),!,fail.
set_ma_flag(time_out,V) :-
	integer(V), V >= 10, !, % min for timeout
	retractall(current_ma_flag(time_out,_)),
	asserta(current_ma_flag(time_out,V)).
set_ma_flag(nb_ite_clpn,V) :-
	integer(V), V >= 1, !,
	retractall(current_ma_flag(nb_ite_clpn,_)),
	asserta(current_ma_flag(nb_ite_clpn,V)).
set_ma_flag(process_include_ensure_loaded,V) :-
	(V==yes ; V==no),!,
	retractall(current_ma_flag(process_include_ensure_loaded,_)),
	asserta(current_ma_flag(process_include_ensure_loaded,V)).
set_ma_flag(size,N) :-
    (N==term_size ; N==list_size ; N==term_size_list_size),!,
	retractall(current_ma_flag(size,_)),
	asserta(current_ma_flag(size,N)).
set_ma_flag(print_info,V) :-
	(V==yes ; V==no),!,
	retractall(current_ma_flag(print_info,_)),
	asserta(current_ma_flag(print_info,V)).
set_ma_flag(Option,Value) :-
    write('% unknown option/value pair in set_ma_flag/2: '),writeln(Option-Value),
    fail.
