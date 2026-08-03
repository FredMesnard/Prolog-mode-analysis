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

:- module(file,[file_clauses/2,file_PIs/2]).

:- use_module(flag).
:- use_module(predef).

    
%%
file_clauses(FileName,Clauses) :-
	open(FileName,read,Stream),
	absolute_file_name(FileName,AbsFileName),
	read(Stream,Clause),
	file_clauses(Clause,Stream,[],Clauses,[AbsFileName]),
	close(Stream).

file_clauses(end_of_file,_S,L,L,_F) :- !.
file_clauses((:-  op(Int,Opsp,Ops)),Stream,L1,L2,Fs) :- !,
    op(Int,Opsp,Ops),
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses((:-  discontiguous(_PIs)),Stream,L1,L2,Fs) :- !,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses((:-  dynamic(_PIs)),Stream,L1,L2,Fs) :- !,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses((:-  multifile(_PIs)),Stream,L1,L2,Fs) :- !,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses((:-  initialization(G)),Stream,L1,L2,Fs) :- !,
	read(Stream,Clause),Clause_exp=Clause,
	(current_ma_flag(print_info,yes) -> (write('% Added clause: '),write('$initialization :- '),write(G),writeln('.')) ; true),
	file_clauses(Clause_exp,Stream,[('$initialization' :- G)|L1],L2,Fs).
file_clauses((:-  include(File)),Stream,L1,L2,Fs) :- !,
        current_ma_flag(process_include_ensure_loaded,Flag), % yes/no
	file_clauses_aux(Flag,File,Stream,L1,L2,Fs).
file_clauses((:-  ensure_loaded(File)),Stream,L1,L2,Fs) :- !,
        current_ma_flag(process_include_ensure_loaded,Flag), % yes/no
	file_clauses_aux(Flag,File,Stream,L1,L2,Fs).
%file_clauses((:- include_predef(File)),Stream,L1,L2,Fs) :- !,
%    include_predef(File),
%	read(Stream,Clause),expand_term(Clause,Clause_exp),
%	file_expand_clauses(Clause_exp,Stream,L1,L2,Fs,0,_).
file_clauses((:-  D),Stream,L1,L2,Fs) :- !,
        write('% Unknown skipped directive: '),write(D),nl,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses(Clause,Stream,L1,L2,Fs) :- 
	read(Stream,Clause2),Clause2_exp=Clause2,
	file_clauses(Clause2_exp,Stream,[Clause|L1],L2,Fs).

file_clauses_aux(no,File,Stream,L1,L2,Fs) :-
	write('% '),write(File),write(' will not be included'),nl,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses_aux(yes,File,Stream,L1,L2,Fs) :-
	\+ include_path(Fs,File,_),!,
	write('% WARNING: '),write(File),write(' not found, not included'),nl,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses_aux(yes,File,Stream,L1,L2,Fs) :-
	include_path(Fs,File,AbsFile),
	member(AbsFile,Fs),!,
	write('% '),write(AbsFile),write(' already included'),nl,
	read(Stream,Clause),Clause_exp=Clause,
	file_clauses(Clause_exp,Stream,L1,L2,Fs).
file_clauses_aux(yes,File,Stream,L1,L,Fs) :-
	include_path(Fs,File,AbsFile),
	    open(AbsFile,read,Stream2),
	    read(Stream2,Clause),
	    Clause_exp=Clause,
	    file_clauses(Clause_exp,Stream2,L1,L2,[AbsFile|Fs]),
	    close(Stream2),
	write('% '),write(AbsFile),write(' included'),nl,
	read(Stream,Clause2),Clause2=Clause_exp2,
	file_clauses(Clause_exp2,Stream,L2,L,[AbsFile|Fs]).

%% include_path(+Fs,+File,-AbsFile)
%% Fs is the stack of files being read, most recent first, always absolute.
%% An included file is looked up relative to the directory of the file holding
%% the directive, not relative to the process working directory.
%% Fails if the result is not a readable file.
include_path([Parent|_],File,AbsFile) :-
	file_directory_name(Parent,Dir),
	absolute_file_name(File,AbsFile,[relative_to(Dir),access(read),file_errors(fail)]).


%% Including predefined predicates:
include_predef(File) :-
	open(File,read,Stream),
	read(Stream,Clause),
	include_predef_aux(Clause,Stream),
	write('% Built-ins from '),write(File),write(' added'),nl,
	close(Stream).

include_predef_aux(end_of_file,_) :-!.
include_predef_aux(predef(At,Mn,Mb,Tc),Stream) :-
	predef_iso(At),!,functor(At,F,N),
	assertz(predef:predef_include(At,Mn,Mb,Tc)),
	write('% WARNING: '),write(F/N),write(' was an ISO built-in but is now redefined'),nl,	
	read(Stream,Clause),
	include_predef_aux(Clause,Stream).
include_predef_aux(predef(At,Mn,Mb,Tc),Stream) :-
	predef_include(At),!,functor(At,F,N),
	assertz(predef:predef_include(At,Mn,Mb,Tc)),
	write('% WARNING: '),write(F/N),write(' was a built-in but is now redefined'),nl,	
	read(Stream,Clause),
	include_predef_aux(Clause,Stream).
include_predef_aux(predef(At,Mn,Mb,Tc),Stream) :-
	!,assertz(predef:predef_include(At,Mn,Mb,Tc)),
	%functor(At,P,N),
	%write('% '),write(P/N),write(' is now built-in'),nl,	
	read(Stream,Clause),
	include_predef_aux(Clause,Stream).
include_predef_aux(X,Stream) :-
        write('% WARNING: '),write(X),write(' is not of the form predef(_,_,_,_) and is skipped'),nl,
	read(Stream,Clause),
	include_predef_aux(Clause,Stream).
	

%%%
file_PIs(FileName,PIs) :- 
	open(FileName,read,Stream),
	read(Stream,Clause),
	file_clauses(Clause,Stream,[],PIs),
	close(Stream).

    file_clauses(end_of_file,_S,L,L) :- !.
    file_clauses((:-  _),Stream,L1,L2) :- !,
        read(Stream,Clause),
	    file_clauses(Clause,Stream,L1,L2).
    file_clauses(Clause,Stream,L1,L2) :-
        Clause = (H :- _), !, functor(H,P,N),
        (   memberchk(P/N,L1)
        ->  L1bis = L1
        ;   L1bis = [P/N|L1]
        ), 
	    read(Stream,Clause2),
	    file_clauses(Clause2,Stream,L1bis,L2).
    file_clauses(Head,Stream,L1,L2) :-
        functor(Head,P,N),
        (   memberchk(P/N,L1)
        ->  L1bis = L1
        ;   L1bis = [P/N|L1]
        ), 
	    read(Stream,Clause2),
	    file_clauses(Clause2,Stream,L1bis,L2).


