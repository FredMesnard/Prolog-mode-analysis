:- use_module(mode_analysis).
:- use_module(dom,[set_domain/1]).
:- dynamic(res/2).
sweep(Out) :-
    set_domain(bddem_op),
    expand_file_name('Filex/*.pl',Fs),
    forall(member(F,Fs),
      ( catch((mode_analysis(F,C) -> sort(C,S), assertz(res(F,S)) ; assertz(res(F,'$FAIL'))),
              E, assertz(res(F,err(E)))) )),
    open(Out,write,St),
    forall(res(F,C),(writeq(St,F-C),write(St,'.'),nl(St))),
    close(St).
