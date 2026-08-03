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

:- module(mode_analysis,[mode_analysis/2, mode_analysis/3, mode_analysis/6, initial_constraint_atom_from_atom/2]).


:- use_module(file).
:- use_module(prolog_flatprolog).
:- use_module(prolog_clph).
:- use_module(bool_itp).
:- use_module(compat_swi).
:- use_module(db).              
:- use_module(flag).
:- use_module(bool_clph_bool).
:- use_module(dom).      % etait bool_op ; dom redirige vers le domaine choisi
:- use_module(db). 
:- use_module(utils).

:- use_module(library(clpb)).
:- use_module(library(readutil)).


% ?- initial_constraint_atom_from_atom(rev(i,o),Query),mode_analysis('Filex/apprev.pl',Query,Calls).
% Query = '$constraint'(_A*(1*1))-rev(_A, _),
% calls = [rev(i, o), app(i, i, o)] ;
% false.

% ?- initial_constraint_atom_from_atom(rev(i,o),Query),mode_analysis(Query,'Filex/apprev.pl',Calls,ModedInitQuery,ModedHProg,ModedListModes).
% Query = '$constraint'(_A*(1*1))-rev(_A, _B),
% Calls = [rev(i, o), app(i, i, o)],
% ModedInitQuery = '$constraint'(_A*(1*1))-rev_io(_A, _B),
% ModedHProg = [obj_clause(rev_io(_C, _D), ['$constraint'([_C=[], _D=[]])]), obj_clause(rev_io(_C, _D), ['$constraint'([_C=[_E|_F]]), rev_io(_F, _G), '$constraint'([_H=[…]]), app_iio(_G, _H, _D)]), obj_clause(app_iio(_I, _J, _K), ['$constraint'([_I=[], _J=_K])]), obj_clause(app_iio(_I, _J, _K), ['$constraint'([_I=[…|…], … = …]), app_iio(_M, _J, _N)])],
% ModedListModes = [rev_io(i, o), app_iio(i, i, o)]

% ?- initial_constraint_atom_from_atom(rev(o,i),Query),mode_analysis('Filex/apprev.pl',Query,Calls).
% Query = '$constraint'(1*(_A*1))-rev(_, _A),
% Calls = [rev(o, i), rev(o, o), app(o, o, i), app(o, o, o)] ;
% false.

% ?- initial_constraint_atom_from_atom(rev(o,i),Query),mode_analysis(Query,'Filex/apprev.pl',Calls,ModedInitQuery,ModedHProg,ModedListModes).
% Query = '$constraint'(1*(_A*1))-rev(_B, _A),
% Calls = [rev(o, i), rev(o, o), app(o, o, i), app(o, o, o)],
% ModedInitQuery = '$constraint'(1*(_A*1))-rev_oi(_B, _A),
% ModedHProg = [obj_clause(rev_oi(_C, _D), ['$constraint'([_C=[], _D=[]])]), obj_clause(rev_oi(_C, _D), ['$constraint'([_C=[_E|_F]]), rev_oo(_F, _G), '$constraint'([_H=[…]]), app_ooi(_G, _H, _D)]), obj_clause(app_ooi(_I, _J, _K), ['$constraint'([_I=[], _J=_K])]), obj_clause(app_ooi(_I, _J, _K), ['$constraint'([_I=[…|…], … = …]), app_ooi(_M, _J, _N)]), obj_clause(rev_oo(_O, _P), ['$constraint'([… = …|…])]), obj_clause(rev_oo(_O, _P), ['$constraint'([…]), rev_oo(…, …)|…]), obj_clause(app_ooo(_U, _V, _W), ['$constraint'(…)]), obj_clause(app_ooo(…, …, …), […|…])],
% ModedListModes = [rev_oi(o, i), rev_oo(o, o), app_ooi(o, o, i), app_ooo(o, o, o)]

% ?- mode_analysis('Filex/apprev.pl',Calls).
% % Please add a line like %query: p(i,o)
% false.

% ?- mode_analysis('FilexTC/der-fb.pl',Calls).
% Calls = [p(i, o), p(i, i), p(o, o), p(o, i)].

% ?- mode_analysis('FilexTC/in-bf.pl',Calls).
% Calls = [in(i, o), less(i, o), less(o, i)].

% ?- mode_analysis('FilexTC/insert-ffb.pl',Calls).
% Calls = [insert(i, o, i), insert(o, o, i), less(i, i), less(o, i), less(i, o)].

% ?- mode_analysis('FilexTC/parse.pl',Calls).
% Calls = [parse(i, o), app(i, i, o), app(o, o, i)].




mode_analysis(FileName, InitQuery, ListModes) :-
	mode_analysis(InitQuery,FileName, ListModes, _ModedInitQuery, _ModedHProg, _ModedListModes),
	!.
	
mode_analysis(FileName, ListModes) :-
    initial_constraint_atom_from_file(FileName,InitQuery),
	mode_analysis(InitQuery,FileName, ListModes, _ModedInitQuery, _ModedHProg, _ModedListModes),
	!.


mode_analysis(InitQuery,FileName, ListModes,ModedInitQuery,ModedHProg,ModedListModes) :-
    (InitQuery == none -> (writeln('% Please add a line like %query: p(i,o)'),fail) ; true),
    file_clauses(FileName,Clauses),
    %
    prologs_flatprologs(Clauses,FPClauses),
    %write_list(FPClauses),
    flatprologs_clphs(FPClauses,ClpHClauses),
    %write_list(ClpHClauses),
    %
    mode_analysis_(InitQuery,ClpHClauses, ListModes,PIs,_Sccs,RelsInterArgsBool),
    %write_list(ListModes),
    %
    mode_analysis_prog(InitQuery,ClpHClauses,RelsInterArgsBool,PIs, ListModes1,ModedHProg),
    %write_list(ListModes1), write_list(ModedHProg),
    (ListModes1 == ListModes -> true ; (writeln('% Bug: the modes differ'),fail)),
    %
    InitQuery = '$constraint'(B)-PureAtom,
    io(InitQuery,ModedAtom),
    adorn_io_atom(ModedAtom,PureAtom,PureAtomIO), 
    ModedInitQuery = '$constraint'(B)-PureAtomIO,
    %true.
    mode_analysis_(ModedInitQuery,ModedHProg, ModedListModes,ModedPIs,_ModedSccs,_ModedRelsInterArgsBool),
    %writeln(ModedListModes-ModedPIs-ModedSccs-ModedRelsInterArgsBool),
    (single_moded(ModedPIs,ModedListModes) -> true ; (writeln('% Bug: the generated moded program is not singly-moded'),fail)).
    

    mode_analysis_('$constraint'(Product)-Atom,ClpHClauses,  ListModes,PIs,Sccs,RelsInterArgsBool) :-
        clphs_clpbs(ClpHClauses,ClpBClauses),
        %write_list(ClpHClauses),
        %write_list(ClpBClauses),
        %
	    call_graph(ClpBClauses,CallGraph),
	    graph_sccs(CallGraph,Sccs),
        %write_list(Sccs),
        %
	    empty_db(Db0),
	    add_cls_domain_dbs(ClpBClauses,clpb,Db0,Db1),
	    sccs_db_domain_sccscls(Sccs,Db1,clpb,SccsClsB),
        %
        current_ma_flag(time_out,TimeOut),
        current_domain(Domain),
        tp(SccsClsB,Domain,no_widening,BaseBool,[star-union],TimeOut),
        assoc_to_list(BaseBool,RelsInterArgsBool), 
        % FM
        %write_list(RelsInterArgsBool),
        %
        empty_db(Modes0),
        modes_td_ca('$constraint'(Product)-Atom,ClpBClauses,RelsInterArgsBool,Modes0,Modes),
        %print_db(Modes),
        clphclauses_PIs(ClpHClauses,PIs),
        modes_list(PIs,Modes,ListModes).
        
    mode_analysis_prog(InitQuery,ClpHClauses,RelsInterArgsBool,PIs, ListModes,HProg) :-
        clphs_clpbs(ClpHClauses,ClpBClauses),
        %write_list(ClpHClauses),write_list(ClpBClauses),
        empty_db(Modes0),
        modes_td_ca_prog(InitQuery,ClpBClauses,RelsInterArgsBool,ClpHClauses,Modes0,Modes,[],HProg),
        modes_list(PIs,Modes,ListModes).

       
    
     
% ?- mode_analysis:shorten_atom(a(X,Y,Z),[p(i),a(i,o,i)],L).
% L = a(X, Z).     
shorten_atom(PureAtom,ListModes,ShortenedAtom) :-
    copy_term(PureAtom,ModedAtom),
    memberchk(ModedAtom,ListModes),
    functor(PureAtom,P,N),
    atomic_list_concat([entry,P],'_',Pe),
    shorten_atom_aux(N,PureAtom,ModedAtom,Pe,[],ShortenedAtom).

    shorten_atom_aux(0,_PureAtom,_ModedAtom,P,Args,ShortenedAtom) :-
        !,ShortenedAtom =.. [P|Args].
    shorten_atom_aux(I,PureAtom,ModedAtom,P,Args,ShortenedAtom) :-
        I > 0, J is I-1,
        arg(I,ModedAtom,MAi),
        (   MAi= o
        ->  NewArgs = Args
        ;   /*MAi = i */
            arg(I,PureAtom,PAi),
            NewArgs = [PAi|Args]
        ),
        shorten_atom_aux(J,PureAtom,ModedAtom,P,NewArgs,ShortenedAtom).
        
        
%single_moded(PIs,ListModes)
single_moded([],_LM).
single_moded([P/N|PIs],ListModes) :-
    functor(Atom,P,N),
    findall(m,member(Atom,ListModes),[m]),
    single_moded(PIs,ListModes).
    
 
% modes_list(PIs, Modes, L)
modes_list(PIs, Modes, L) :- modes_list(PIs, Modes, [], L0), sort(L0,L).

    modes_list([],_Modes,L,L).
    modes_list([P/N|PIs],Modes,L0,L) :-
        get_db(P,N,mode,Modes,ModesPN),
        append(ModesPN,L0,L1),
        modes_list(PIs,Modes,L1,L).


%%%%
modes_td_ca(ConstrainedAtom,_BoolProg,_BoolModel,Modes,Modes) :-
     ConstrainedAtom = '$constraint'(BC)-_PureAtom,
     \+ satisfiable(BC),
     !.
modes_td_ca(ConstrainedAtom0,BoolProg,BoolModel,Modes0,Modes) :-
    copy_term(ConstrainedAtom0,ConstrainedAtom),
     ConstrainedAtom = '$constraint'(BC)-PureAtom,
     satisfiable(BC),
     io(ConstrainedAtom,ModedAtom),
     %update_modes(ModedAtom,Modes0,Modes1),
     functor(ModedAtom,P,N),
     get_db(P,N,mode,Modes0,ModesPN),
     (  memberchk(ModedAtom,ModesPN)
     -> Modes = Modes0
     ;  add_db(P,N,mode,Modes0,ModedAtom,Modes1),
        matching_clauses(BoolProg,PureAtom,ObjCls),
        modes_td_ca_aux(ObjCls,ConstrainedAtom,BoolProg,BoolModel,Modes1,Modes)
     ).
    
    modes_td_ca_aux([],_CA,_BP,_BM,Modes,Modes).
    modes_td_ca_aux([ObjCl|Cls],CA,BoolProg,BoolModel,Modes0,Modes) :-
        ObjCl =  obj_clause(PureAtom1,Body),
        CA = '$constraint'(B)-PureAtom2,
        PureAtom1 = PureAtom2,
        modes_td_body(Body,B,BoolProg,BoolModel,Modes0,Modes1),
        modes_td_ca_aux(Cls,CA,BoolProg,BoolModel,Modes1,Modes).
     
modes_td_body([],_BCs,_BP,_BM,Modes,Modes).
modes_td_body(['$predef'(_)|Body],BCs,BP,BM,Modes0,Modes) :- 
    !,modes_td_body(Body,BCs,BP,BM,Modes0,Modes).     
modes_td_body(['$constraint'(BC)|Body],BCs,BP,BM,Modes0,Modes) :- 
    !,conjunction(BC,BCs,BCBCs),
    modes_td_body(Body,BCBCs,BP,BM,Modes0,Modes).
modes_td_body([Atom|Body],BCs,BP,BM,Modes0,Modes) :-
     modes_td_ca('$constraint'(BCs)-Atom,BP,BM,Modes0,Modes1),
     functor(Atom,P,N), Atom =.. [P|VarsAtomIn],
     memberchk(P/N-(Vars-BAtom-_-_),BM),
     copy_term(Vars-BAtom,VarsAtomIn-BAtomIn),
     conjunction(BAtomIn,BCs,BCs1),
     modes_td_body(Body,BCs1,BP,BM,Modes1,Modes).
    

matching_clauses(BoolProg,PureAtom,ClsForPureAtom) :-
    findall(obj_clause(PureAtom,B),member(obj_clause(PureAtom,B),BoolProg),ClsForPureAtom).
    
%%%
modes_td_ca_prog(ConstrainedAtom,_BoolProg,_BoolModel,_HProgInit,Modes,Modes,HProg,HProg) :-
     ConstrainedAtom = '$constraint'(BC)-_PureAtom,
     \+ satisfiable(BC),
     !.
modes_td_ca_prog(ConstrainedAtom0,BoolProg,BoolModel,HProgInit,Modes0,Modes,HProg0,HProg) :-
    copy_term(ConstrainedAtom0,ConstrainedAtom),
     ConstrainedAtom = '$constraint'(BC)-PureAtom,
     satisfiable(BC),
     io(ConstrainedAtom,ModedAtom),                 % io('$constraint'(A)-p(A,B),p(i, o))
     adorn_io_atom(ModedAtom,PureAtom,PureAtomIO),  % adorn_io_atom(p(i, o),p(A,B),p_io(A,B))
     functor(ModedAtom,P,N),
     get_db(P,N,mode,Modes0,ModesPN),
     (  memberchk(ModedAtom,ModesPN)
     -> % recursion stops here
        Modes = Modes0,
        HProg = HProg0  
     ;  add_db(P,N,mode,Modes0,ModedAtom,Modes1),
        matching_clauses(BoolProg,PureAtom,ObjClsB),
        matching_clauses(HProgInit,PureAtom,ObjClsH), % assumes the same clause order
        modes_td_ca_prog_aux(ObjClsB,ObjClsH,ConstrainedAtom,PureAtomIO,BoolProg,BoolModel,HProgInit,Modes1,Modes,HProg0,HProg)).
    
    modes_td_ca_prog_aux([],[],_CA,_PAIO,_BP,_BM,_HP,Modes,Modes,HProg,HProg).
    modes_td_ca_prog_aux([ObjClB|ClsB],[ObjClH|ClsH],CA,PureAtomIO,BoolProg,BoolModel,HProgInit,Modes0,Modes,HProg0,HProg) :-
        ObjClB =  obj_clause(PureAtom1,BodyB),
        CA = '$constraint'(Benv)-PureAtom2,
        PureAtom1 = PureAtom2,
        ObjClH = obj_clause(PureAtom1,BodyH),
        NewObjClsH = obj_clause(PureAtomIO,NewBodyH),
        % the call below builds the body NewBodyH of a new clause to be added to HProg0 -> HProg1
        modes_td_body_prog(BodyB,BodyH,NewBodyH,Benv,PureAtomIO,BoolProg,BoolModel,HProgInit,Modes0,Modes1,HProg0,HProg1),
        HProg2 = [NewObjClsH|HProg1],
        modes_td_ca_prog_aux(ClsB,ClsH,CA,PureAtomIO,BoolProg,BoolModel,HProgInit,Modes1,Modes,HProg2,HProg).
     
modes_td_body_prog([],[],[],_BCs,_PAIO,_BP,_BM,_HP,Modes,Modes,HProg,HProg).
% In the CLP(B) program a '$predef' is followed by its Boolean meaning, added
% by bool_clph_bool:h_bool_body/2 and absent from the CLP(H) program. The two
% bodies therefore advance by 2 and by 1. That constraint must be CONJOINED,
% exactly as modes_td_body/6 does: dropping it cost this pass all the
% groundness contributed by built-ins, hence the "% Bug: the modes differ" on
% every program using them.
modes_td_body_prog(['$predef'(_),'$constraint'(Ba)|Body],[P|BodyH],[P|NewBodyH],BCs,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg) :-
    !,conjunction(Ba,BCs,BCs1),
    modes_td_body_prog(Body,BodyH,NewBodyH,BCs1,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg).
% Fallback, should the shape above ever not be the one produced.
%modes_td_body_prog(['$predef'(_),_|Body],[P|BodyH],[P|NewBodyH],BCs,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg) :-
%    !,modes_td_body_prog(Body,BodyH,NewBodyH,BCs,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg).
modes_td_body_prog(['$constraint'(BC)|_Body],[C|_BodyH],[C|NewBodyH],_BCs,_PureAtomIO,_BP,_BM,_HProgInit,Modes,Modes,HProg,HProg) :- 
    \+ satisfiable(BC),
    !,
    NewBodyH = [].
modes_td_body_prog(['$constraint'(BC)|Body],[C|BodyH],[C|NewBodyH],BCs,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg) :- 
    satisfiable(BC),
    !,
    conjunction(BC,BCs,BCBCs),
    modes_td_body_prog(Body,BodyH,NewBodyH,BCBCs,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg).
modes_td_body_prog(_,_,[],BCs,_PureAtomIO,_BP,_BM,_HProgInit,Modes,Modes,HProg,HProg) :-
     \+ satisfiable(BCs),
     !.
modes_td_body_prog([Atom|Body],[Atom|BodyH],[AtomIO|NewBodyH],BCs,PureAtomIO,BP,BM,HProgInit,Modes0,Modes,HProg0,HProg) :-
     ConstrainedAtom = '$constraint'(BCs)-Atom,
     satisfiable(BCs),     
     modes_td_ca_prog(ConstrainedAtom,BP,BM,HProgInit,Modes0,Modes1,HProg0,HProg1),
     io(ConstrainedAtom,ModedAtom),          
     adorn_io_atom(ModedAtom,Atom,AtomIO),  
     functor(Atom,P,N), Atom =.. [P|VarsAtomIn],
     memberchk(P/N-(Vars-BAtom-_-_),BM),
     copy_term(Vars-BAtom,VarsAtomIn-BAtomIn),
     conjunction(BAtomIn,BCs,BCs1),
     modes_td_body_prog(Body,BodyH,NewBodyH,BCs1,PureAtomIO,BP,BM,HProgInit,Modes1,Modes,HProg1,HProg).
    
%%%
% adorn_io_atom(p(i, o),p(A,B),p_io(A,B))
adorn_io_atom(ModedAtom,PureAtom,PureAtomIO) :-
    ModedAtom =.. [P|IOs], L = [P,'_'|IOs], concat_atom(L,NewPredIO),
    PureAtom =.. [P|Args], PureAtomIO =.. [NewPredIO|Args].

%%%    
io(CAtom,ModedAtom) :-
    CAtom = '$constraint'(B0)-PureAtom,
    PureAtom =.. [P|Vars],
    project(Vars,B0,Vars,B),
    functor(PureAtom,P,N),
    functor(ModedAtom,P,N),
    io(1,N,B,PureAtom,ModedAtom).
    
    io(I,N,B,PureAtom,ModedAtom) :-
        I =< N, !, J is I + 1,
        PureAtom =.. [_P|Args],
        arg(I,PureAtom,PAi),
        arg(I,ModedAtom,MAi),
        (  entail(Args,B,Args,(PAi =:= 1)) 
        -> MAi = i 
        ;  MAi = o
        ),
        io(J,N,B,PureAtom,ModedAtom).
    io(J,N,_B,_PureAtom,_ModedAtom) :-
        J > N.
    
    /*
    ?- io('$constraint'(A*B)-p(A,B),MA).
    MA = p(i, i).
    ?- io('$constraint'(A+B)-p(A,B),MA).
    MA = p(o, o).
    ?- io('$constraint'(A)-p(A,B),MA).
    MA = p(i, o).
    ?- io('$constraint'(B)-p(A,B),MA).
    MA = p(o, i).
    */
   
%%% 
update_modes(ModedAtom,M0,M1) :-
    functor(ModedAtom,P,N),
    get_db(P,N,mode,M0,ModesPN),
    (  memberchk(ModedAtom,ModesPN)
    -> M1 = M0
    ;  add_db(P,N,mode,M0,ModedAtom,M1)
    ).
    
    /*
    ?- db:empty_db(D), db:get_db(a,3,mode,D,V1),mode_analysis:update_modes(a(o,i,o),D,E),mode_analysis:update_modes(a(i,i,i),E,F),
       mode_analysis:update_modes(a(i,i,i),F,G),db:print_db(G), db:get_db(a,3,mode,G,V).
    a/3 mode:    a(i,i,i).    a(o,i,o).
    */

%%%
initial_constraint_atom_from_file(FileName,Init) :-
        file_queryOfInterest(FileName,Query), 
		initial_constraint_atom_from_atom(Query,Init).

initial_constraint_atom_from_atom(none,none) :- !.
initial_constraint_atom_from_atom(Query,Init) :-
        Query=..[P|IOArgs], 
        length(IOArgs,N),
        length(VarsArgs,N),
        Atom=..[P|VarsArgs],
        product(IOArgs,VarsArgs,Product),
        Init = '$constraint'(Product)-Atom.

        
    product([],[],1).
    product([IO|IOArgs],[X|Xs],Piox*P) :-
        prod(IO,X,Piox),
        product(IOArgs,Xs,P).
    
        prod(i,X,X). prod(o,_X,1).
        prod(b,X,X). prod(f,_X,1).
        prod(g,X,X). prod(a,_X,1).

    file_queryOfInterest(FileName,Query) :- 
	    open(FileName,read,Stream),
        read_line_to_string(Stream,String),
	    process(String,Stream,Query),
	    close(Stream).

        process(end_of_file,_Stream,none) :- 
            !.
        process(String,_Stream,Query) :-
            (   string_concat("%query: ", PredString, String)
            ;   string_concat("%query:", PredString, String)
            ),
            !,
            term_string(Query,PredString).
        process(_String,Stream,Query) :-
            read_line_to_string(Stream,NextString),
            process(NextString,Stream,Query).

        
