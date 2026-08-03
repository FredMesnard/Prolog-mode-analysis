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

:- module(compat_swi,[with_time_out/3]).

% This file also used to hold graph_reduce/2 and its helpers. They now live in
% tarjan.pl, written from scratch; the two agreed on all 53 Filex call graphs
% and on the whole corpus.

:- use_module(library(time)).

with_time_out(Goal,TimeOut,Res) :- % TimeOut in seconds
	%write('% '),write(TimeOut),nl,write('% '),
	catch(call_with_time_limit(TimeOut,Goal), time_limit_exceeded, Res=time_out),
	(var(Res) -> Res=success; true).
