# Mode analysis — user manual

A mode (groundness) analyzer for a subset of ISO Prolog, written in SWI-Prolog.

Given a program and an initial call pattern such as `rev(i,o)`, the tool infers the set of call modes reachable from that query, and additionally generates a *mode-specialized* program in which each `p(i,o)` call becomes a distinct predicate `p_io/2`.

Two implementations of the Boolean abstract domain are available and **interchangeable**.

| module | built on | status |
|---|---|---|
| `bool_op` | SWI-Prolog's `library(clpb)` | default, no prerequisites |
| `bddem_op` | the `bddem` pack (CUDD), dynamic reordering off | needs the pack and its patches |

They produce the same modes; they differ only in performance. The choice is detailed in [§ 5 Choosing a domain](#5-choosing-a-domain).

---

## 1. Installation

SWI-Prolog is the only mandatory dependency (tested with 9.0.4 and 10.1.11). There is no build step and no package manager.

Using `bddem_op` additionally requires the `bddem` pack **with two local patches**, exposing features CUDD implements but the pack did not surface:

- `exist_abstract/4`, existential quantification, without which `project/4` is impossible;
- `set_reordering/2` and `reordering_status/2`, to control dynamic reordering.

The script `install-bddem/fix-bddem.sh` builds the pack from source and applies the patch; it is idempotent and self-verifying.

Quick environment check:

```bash
./ma.sh --check
```

---

## 2. Command-line use

### 2.1 The `ma.sh` launcher

```
./ma.sh [options] FILE [QUERY]
```

Without `QUERY`, it is read from the file's `%query:` header. The launcher locates itself, so it works from any directory.

| option | effect |
|---|---|
| `-b`, `--bddem` | `bddem_op` domain (CUDD) |
| `-c`, `--clpb` | `bool_op` domain (default) |
| `-m`, `--moded` | also print the generated moded program |
| `-t`, `--timeout SEC` | fixpoint time limit per SCC (minimum 10, default 10) |
| `-q`, `--quiet` | print the modes only |
| `-k`, `--check` | check the environment and exit |
| `-h`, `--help` | help |

Exit codes: `0` success, `1` analysis failed, `2` usage or environment error.

One environment variable, `SWIPL`, names the SWI-Prolog to run; without it the launcher takes the first `swipl` on `PATH`. It matters when a machine carries more than one installation — a package-manager build alongside a `swipl.framework` one, say — because `bddem` is native code linked against exactly one of them, and they share a single pack directory, hence a single `bddem.so`. Note also that `ma.sh` is a `bash` script: an interactive shell alias for `swipl` never reaches it, so the launcher and your terminal can silently disagree on which Prolog is in use. `--check` prints the resolved path for that reason.

```bash
SWIPL=/path/to/swipl ./ma.sh --bddem Filex/inorder.pl
```

Examples:

```bash
./ma.sh FilexTC/parse.pl
```

```bash
./ma.sh --bddem Filex/inorder.pl
```

```bash
./ma.sh --bddem --moded Filex/apprev.pl 'rev(o,i)'
```

The query is passed through the environment rather than interpolated into the Prolog goal: any parentheses, commas or quotes it contains therefore cannot break the goal's syntax.

### 2.2 Calling `swipl` directly

The launcher is only a convenience; everything is reachable directly. **With relative paths you must be at the repository root** — otherwise `use_module(mode_analysis)` fails with `source_sink does not exist`. Absolute paths, for both the module and the analyzed file, lift that constraint.

Default domain, query read from the header:

```bash
swipl -g "use_module(mode_analysis), mode_analysis('FilexTC/parse.pl',C), format('~w~n',[C])" -t halt
```

Switching to `bddem_op`:

```bash
swipl -g "use_module(mode_analysis), use_module(dom,[set_domain/1]), set_domain(bddem_op), mode_analysis('FilexTC/parse.pl',C), format('~w~n',[C])" -t halt
```

The selective import `dom,[set_domain/1]` is deliberate: `dom` also exports the nine abstract-domain operations, which have no business in `user`.

Finding out which domain is active:

```bash
swipl -g "use_module(dom,[current_domain/1]), current_domain(D), format('~w~n',[D])" -t halt
```

### 2.3 Interactive use

```bash
swipl mode_analysis.pl
```

```prolog
?- use_module(dom), set_domain(bddem_op).
?- mode_analysis('FilexTC/parse.pl', Modes).
```

---

## 3. Entry points

`mode_analysis/6` is the real entry point; the other two are shortcuts over it.

| predicate | arguments |
|---|---|
| `mode_analysis/2` | `(File, ListModes)` — query read from the header |
| `mode_analysis/3` | `(File, InitQuery, ListModes)` |
| `mode_analysis/6` | `(InitQuery, File, ListModes, ModedInitQuery, ModedProg, ModedModes)` |

> **The first two arguments are swapped between `/3` and `/6`.** `/3` takes the file first, `/6` takes the query first. This is the single most frequent source of error.

`InitQuery` is not the atom itself but a *constrained atom*, built by `initial_constraint_atom_from_atom/2`: `rev(i,o)` becomes `'$constraint'(A*(1*1))-rev(A,_)`.

---

## 4. Conventions for the analyzed programs

**`%query:` header.** The first line starting with `%query:` supplies the query. The corpus idiom for *disabling* a query line is `%%query:`. A file carrying only `%%query:` lines prints `% Please add a line like %query: p(i,o)` and fails.

**Mode letters.** `i` (input, assumed ground) and `o` (output). `prod/3` accepts two further spellings of the same pair: `b`/`f` (bound/free, hence the `-bf` suffixes in the corpus filenames) and `g`/`a`. The corpus uses `i`/`o` exclusively.

**DCGs are silently ignored.** Term expansion is disabled, so `H --> B` is read as a `-->`/2 fact. The analysis then succeeds and returns `[]` — for instance on `Filex/testdcg1.pl`. Do not read an empty mode list as "no modes reachable" without checking the source.

**`:- include/1` and `:- ensure_loaded/1` are off by default.** The flag `process_include_ensure_loaded` is `no`: the directive is skipped with the message `% <file> will not be included`. To enable it:

```prolog
?- use_module(flag), set_ma_flag(process_include_ensure_loaded, yes).
```

Included paths are then resolved relative to the directory of the file holding the directive, not to the current directory. Only literal paths are accepted: no extension guessing (`ensure_loaded(foo)` will not find `foo.pl`) and no `library(...)` specification.

**Fixpoint time limits.** The `time_out` flag is 10 s per SCC, and `set_ma_flag/2` enforces 10 as the minimum. On timeout the SCC receives the *top* model and the analysis continues on a degraded model, after printing `% WARNING: bool fixpoint TIME OUT`. **This message reports a degraded result**; it is a plain warning.

---

## 5. Choosing a domain

### 5.1 Summary

| criterion | `bool_op` (clpb) | `bddem_op` (CUDD) |
|---|---|---|
| Inferred modes | — identical in every case measured — ||
| Prerequisites | none | `bddem` pack + 2 patches |
| Small programs | **faster** | penalized by creating a CUDD environment per operation |
| Large programs | penalized | **markedly faster** |
| `FilexTC` corpus (90 files) | 4.6 s | **2.3 s** |
| `Filex` corpus (43 files) | 18.4 s | **2.7 s** |
| Behaviour | steady | steady (reordering off) |

**In practice:** for a single, modest file the `bool_op` default is enough and avoids any installation. For a corpus sweep or a large program, `bddem_op` is worth switching to.

### 5.2 Detail

**Correctness.** No disagreement between the two domains has ever been observed: 90/90 on `FilexTC`, 44/44 on `Filex` (`read.pl` included). Both self-checks in `mode_analysis/6` (the two top-down passes must agree, and the regenerated program must be singly-moded) pass in both domains across the whole corpus.

**Measurement conditions.** Every figure in this section comes from a single campaign on a **MacBook Air (`Mac14,2`), Apple M2, 8 cores (4 performance + 4 efficiency), 16 GB, macOS 26.6.1, SWI-Prolog 10.1.11** — one sweep per domain in a single SWI-Prolog process, timing each file separately, analysis time only, startup and compilation excluded. The machine is fanless, so a long run can be throttled; expect a few percent between repeats.

**Corpus totals**

| corpus | `bool_op` | `bddem_op` | ratio |
|---|---|---|---|
| `FilexTC`, 90 files | 4,616 ms | 2,282 ms | 2.02× |
| `Filex`, the 43 other files that resolve (excluding `read.pl`, `chat_pt.pl.too.hard` and the query-less `apprev-no-init-query-should-fail.pl`) | 18,440 ms | 2,742 ms | 6.73× |
| `Filex/read.pl` alone | 26,341 ms | 3,379 ms | 7.80× |

**Where each wins** — the overall gain is very unevenly distributed:

| corpus | bddem wins | bddem loses |
|---|---|---|
| `FilexTC` | 45 files | 45 files |
| `Filex` | 12 files | 31 files |

`bddem_op` is therefore slower on the *majority* of files; it wins only on the expensive ones — but those are what move the total.

**Most favourable cases for `bddem_op`**

| file | `bool_op` | `bddem_op` | ratio |
|---|---|---|---|
| `Filex/inorder.pl` | 12,196 ms | 204 ms | 59.8× |
| `FilexTC/mergesort.pl` | 755 ms | 90 ms | 8.4× |
| `Filex/read.pl` | 26,341 ms | 3,379 ms | 7.8× |
| `Filex/modulaGrammar.pl` | 1,630 ms | 221 ms | 7.4× |
| `Filex/qplan.pl` | 689 ms | 132 ms | 5.2× |
| `FilexTC/quicksort-fb.pl` | 423 ms | 97 ms | 4.4× |

**Least favourable cases** (measurable times only)

| file | `bool_op` | `bddem_op` | ratio |
|---|---|---|---|
| `Filex/sequence.pl` | 19 ms | 52 ms | 0.37× |
| `Filex/average1.pl` | 15 ms | 39 ms | 0.38× |
| `Filex/from_caslog2.pl` | 15 ms | 35 ms | 0.43× |
| `FilexTC/search_tree.pl` | 25 ms | 46 ms | 0.54× |

The pattern is consistent: below a few tens of milliseconds, creating a CUDD environment per operation dominates and `bool_op` wins.

**Design differences**

| | `bool_op` | `bddem_op` |
|---|---|---|
| Engine | clpb, pure Prolog, attributed variables | CUDD, a C library |
| Constraint representation | Boolean term | Boolean term *(forced, see below)* |
| State between operations | incremental | recompiled at each decision point |
| Projection | clpb residual + `^` quantifiers, then re-normalisation | `Cudd_bddExistAbstract`, then DNF |
| Variable reordering | not applicable | off (`set_reordering(E,none)`) |

A constraint stays a **term** in both domains, and that is not a choice: `bool_itp.pl` and `mode_analysis.pl` apply `copy_term/2` to constraints and rely on Prolog variable renaming to tie a constraint to its atom. A BDD pointer is an opaque integer that `copy_term` does not rename. `bddem_op` therefore uses CUDD only as a decision engine, which is its main handicap; keeping BDDs across calls would mean carrying the variable list with each node and permuting indices at every conjunction, hence also exposing `Cudd_bddPermute`.

On the `bool_op` side, `project/4` re-normalises its result: `eliminate/3` does not remove the projected variables, it keeps them under `^` quantifiers. Usually harmless (1 to 5 of them), but on `Filex/inorder.pl` the output carried up to **928 quantifiers** around content that never had more than 12 free variables, every later operation having to redo the elimination. The re-normalisation brought that file down from 36.5 s to 12.8 s and unblocked `read.pl`, which had not been terminating under 60 s. That before/after pair comes from an earlier campaign than the tables above, and only the pair is meaningful, not either figure on its own.

---

## 6. Troubleshooting

| symptom | likely cause |
|---|---|
| `% Please add a line like %query: p(i,o)` | no active `%query:` header; supply one, or pass the query as an argument |
| `source_sink 'mode_analysis' does not exist` | direct `swipl` call from outside the repository root; use `ma.sh` or absolute paths |
| `% WARNING: bool fixpoint TIME OUT` | warning: degraded model, hence less precise modes; re-run with a larger `--timeout` to recover precision |
| empty mode list `[]` | the program is probably written with DCGs, which are silently ignored |
| `% <file> will not be included` | `include`/`ensure_loaded` are off by default |
| `the bddem pack lacks the exist_abstract/4 and set_reordering/2 additions` | re-run `install-bddem/fix-bddem.sh` |
| `% Bug: the modes differ` | divergence between the two top-down passes; this should no longer happen, please report it |

---

## 7. Sweeping a corpus

With `clpb`:
```bash
swipl -g "use_module(mode_analysis), expand_file_name('FilexTC/*.pl',Fs), forall(member(F,Fs), catch((mode_analysis(F,C) -> format('OK   ~w ~w~n',[F,C]) ; format('FAIL ~w~n',[F])), E, format('ERR  ~w ~w~n',[F,E])))" -t halt
```
```bash
swipl -g "use_module(mode_analysis), expand_file_name('Filex/*.pl',Fs), forall(member(F,Fs), catch((mode_analysis(F,C) -> format('OK   ~w ~w~n',[F,C]) ; format('FAIL ~w~n',[F])), E, format('ERR  ~w ~w~n',[F,E])))" -t halt
```
It is faster with `bddem`:
```bash
swipl -g "use_module(mode_analysis), use_module(dom,[set_domain/1]), set_domain(bddem_op), expand_file_name('FilexTC/*.pl',Fs), forall(member(F,Fs), catch((mode_analysis(F,C) -> format('OK   ~w ~w~n',[F,C]) ; format('FAIL ~w~n',[F])), E, format('ERR  ~w ~w~n',[F,E])))" -t halt
```
```bash
swipl -g "use_module(mode_analysis), use_module(dom,[set_domain/1]), set_domain(bddem_op), expand_file_name('Filex/*.pl',Fs), forall(member(F,Fs), catch((mode_analysis(F,C) -> format('OK   ~w ~w~n',[F,C]) ; format('FAIL ~w~n',[F])), E, format('ERR  ~w ~w~n',[F,E])))" -t halt
```

---

## 8. Licence and credits

Licensed under the **GNU LGPL v3 or later**. The text sits at the repository root: `COPYING.LESSER` for the LGPL and `COPYING` for the GPL — both are needed, since LGPL v3 is written as a set of additional permissions on top of GPL v3 rather than as a standalone licence.

Developed by Fred Mesnard. The `bddem` domain integration, the launcher and the documentation were produced with assistance from Claude (Anthropic), in 2026.

All the code is original.
