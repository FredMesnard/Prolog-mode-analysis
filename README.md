# Prolog-mode-analysis

[![tests](https://github.com/FredMesnard/Prolog-mode-analysis/actions/workflows/tests.yml/badge.svg)](https://github.com/FredMesnard/Prolog-mode-analysis/actions/workflows/tests.yml)

A mode (groundness) analyzer for a subset of ISO Prolog, written in SWI-Prolog.

Given a program and an initial call pattern such as `pred(i,o)`, it infers the set of call modes reachable from that query, and generates a *mode-specialized* program in which each `p(i,o)` call becomes a distinct predicate `p_io/2`.

```
$ ./ma.sh FilexTC/parse.pl
domain : bool_op
file   : /.../FilexTC/parse.pl

modes : [parse(i,o),app(i,i,o),app(o,o,i)]
```

## Requirements

SWI-Prolog (tested with 9.0.4 and 10.1.11) and nothing else. There is no build step and no package to install: clone or unpack, and run.

An optional second Boolean domain, built on the `bddem` pack (CUDD), is faster on large programs. It needs the pack plus two small local additions; `install-bddem/fix-bddem.sh` builds and patches it. Everything works without it — `bool_op`, over SWI's `library(clpb)`, is the default.

## Getting started

Check the environment:

```bash
./ma.sh --check
```

Analyze a program, taking the query from its `%query:` header:

```bash
./ma.sh FilexTC/parse.pl
```

Pass the query explicitly, and print the generated moded program too:

```bash
./ma.sh --moded Filex/apprev.pl 'rev(o,i)'
```

Switch to the CUDD-backed domain:

```bash
./ma.sh --bddem Filex/inorder.pl
```

`./ma.sh --help` lists the options. Everything is also reachable by calling `swipl` directly.

## Mode specialization

Inferring modes is only half of it. `--moded` also emits a program in which each predicate is split into one variant per call mode. Take naive reverse:

```prolog
app([], X, X).
app([E|X], Y, [E|Z]) :- app(X, Y, Z).

rev([], []).
rev([E|X], Y) :- rev(X, Z), app(Z, [E], Y).
```

Called as `rev(o,i)` — reconstructing the input list from a reversed one — the analyzer finds that `rev/2` is reached under *two* different modes, and `app/3` likewise:

```
$ ./ma.sh --moded Filex/apprev.pl 'rev(o,i)'

modes : [rev(o,i),rev(o,o),app(o,o,i),app(o,o,o)]

moded program modes : [rev_oi(o,i),rev_oo(o,o),app_ooi(o,o,i),app_ooo(o,o,o)]

moded program :
obj_clause(rev_oi(A,B),['$constraint'([A=[],B=[]])])
obj_clause(rev_oi(A,B),['$constraint'([A=[C|D]]),rev_oo(D,E),'$constraint'([F=[C]]),app_ooi(E,F,B)])
obj_clause(app_ooi(A,B,C),['$constraint'([A=[],B=C])])
obj_clause(app_ooi(A,B,C),['$constraint'([A=[D|E],C=[D|F]]),app_ooi(E,B,F)])
obj_clause(rev_oo(A,B),['$constraint'([A=[],B=[]])])
obj_clause(rev_oo(A,B),['$constraint'([A=[C|D]]),rev_oo(D,E),'$constraint'([F=[C]]),app_ooo(E,F,B)])
obj_clause(app_ooo(A,B,C),['$constraint'([A=[],B=C])])
obj_clause(app_ooo(A,B,C),['$constraint'([A=[D|E],C=[D|F]]),app_ooo(E,B,F)])
```

Two source predicates have become four, each specialized to one call pattern: the entry point `rev_oi/2` recurses into `rev_oo/2`, which in turn calls `app_ooo/3` rather than the `app_ooi/3` used at the top level. Clause bodies appear in the analyzer's internal form — `obj_clause(Head,BodyList)`, with the head-argument bindings pulled out into a leading `'$constraint'` goal — which is the shape the analysis works on throughout.

The same query analyzed without `--moded` reports only the first line, the modes.

## Documentation

| file | |
|---|---|
| `user-manual.md` | the manual: command line, entry points, conventions the analyzed programs must follow, troubleshooting, and a detailed comparison of the two Boolean domains |
| `docs/internals.md` | how it is put together: the nine-stage pipeline, the term vocabulary, the abstract-domain interface, and the gotchas — read this before changing anything |

The modules themselves are commented, and `mode_analysis.pl` opens with worked example queries.

## Layout

```
mode_analysis.pl        entry points and the two top-down passes
bool_itp.pl             bottom-up fixpoint over an abstract domain
bool_op.pl              Boolean domain over library(clpb)      -- default
bddem_op.pl             Boolean domain over the bddem pack     -- optional
dom.pl                  domain selection
tarjan.pl               strongly connected components
ma.sh                   command-line launcher
install-bddem/          what the bddem domain needs
Filex/  FilexTC/        corpora of test programs
```

## Tests

The regression set is the 90 programs of `FilexTC/`, each carrying a `%query:` header. All 90 must succeed, in either domain, in about 5 seconds:

```bash
swipl -g "use_module(mode_analysis), expand_file_name('FilexTC/*.pl',Fs), forall(member(F,Fs), catch((mode_analysis(F,C) -> format('OK   ~w ~w~n',[F,C]) ; format('FAIL ~w~n',[F])), E, format('ERR  ~w ~w~n',[F,E])))" -t halt
```

Unit tests cover the strongly-connected-components step:

```bash
swipl -g "use_module(tarjan), run_tests" -t halt
```

`Filex/` holds larger, messier real programs; 46 of its 47 files carry an active query, the exception being `apprev-no-init-query-should-fail.pl`, which checks that a missing query fails cleanly. `read.pl` is slow enough to be worth excluding from a sweep, and a 48th program, `chat_pt.pl.too.hard`, is slower still — its suffix keeps it out of every `Filex/*.pl` glob.

Both corpora are **inputs to the analyzer, not part of it**, and the licence above does not extend to them. A few are recognisable programs by named authors, reproduced as reference benchmarks; `Filex/README.md` attributes them.

## Licence

GNU LGPL v3 or later. `COPYING.LESSER` holds the LGPL text and `COPYING` the GPL text.

Developed by Fred Mesnard. The `bddem` domain integration, the launcher and the documentation were produced with assistance from Claude (Anthropic), in 2026.
