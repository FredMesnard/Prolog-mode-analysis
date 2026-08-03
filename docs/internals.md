# Internals

How the analyzer is put together, for anyone wanting to read or change it. The user-facing side is in [`user-manual.md`](../user-manual.md); this document assumes you have it.

## The pipeline

`mode_analysis/6` runs a fixed sequence of source-to-source abstractions, then a bottom-up fixpoint, then two top-down passes. Each stage lives in its own module behind a clearly named entry predicate, so a change is almost always local to one stage.

**1. Read** — `file.pl:file_clauses/2`. Reads terms with `read/1`, executes `:- op/3`, skips declarations, and turns `:- initialization(G)` into a `'$initialization' :- G` clause. Term expansion is deliberately disabled, which is why DCG rules are not expanded (see [Gotchas](#gotchas)).

**2. Flatten** — `prolog_flatprolog.pl:prologs_flatprologs/2`. Removes full Prolog control: `;`, `->`, `\+`, `once`, `call`, `findall`, `setof`, `bagof` and `catch` are rewritten (`tr1s`, `tr2`), and disjunction is distributed into separate clauses (`tr3`, `distribute`). Bodies become flat lists, built-in calls wrapped as `'$predef'(Atom)`. Output: `obj_clause(Head, BodyList)`.

**3. Normalize to CLP(H)** — `prolog_clph.pl:flatprologs_clphs/2`. Head and body atom arguments are replaced by distinct fresh variables, the discarded bindings moving into a leading `'$constraint'([X=Term, ...])` goal. After this stage every atom is linear in fresh variables.

**4. Abstract to CLP(B)** — `bool_clph_bool.pl:clphs_clpbs/2`. The groundness (Pos) abstraction: each equation `X = Term` becomes the Boolean constraint `X =:= V1*V2*...` over `term_variables(Term)`. `'$predef'` goals get their Boolean meaning from `predef.pl`. Constraints are Boolean formulas from here on.

**5. Call graph and SCCs** — `utils.pl:call_graph/2`, then `graph_sccs/2`, which condenses the graph with `tarjan.pl:graph_reduce/2` and topologically sorts the result in reverse, so that strongly connected components are solved bottom-up.

**6. Bottom-up fixpoint** — `bool_itp.pl:tp/6`. Least-fixpoint `Tp` iteration per SCC over the abstract domain, producing a *model*: for each `P/N`, a formula over its argument variables describing the groundness dependencies of its answers. Precision and widening are driven by the `[star-union]` control list, and each SCC runs under `with_time_out/3`.

**7. Top-down call patterns** — `mode_analysis.pl:modes_td_ca/6`. Propagates the initial constrained atom through the CLP(B) program, consulting the bottom-up model for what each call *returns* before moving to the next body goal. `io/2` reads a mode off a constraint: an argument is `i` when the constraint entails `X =:= 1`, `o` otherwise. Recursion stops when a mode is already recorded.

**8. Moded program generation** — `mode_analysis.pl:modes_td_ca_prog/8`. A second top-down pass, this time over the *CLP(H)* clauses in lockstep with the CLP(B) ones, emitting the `p_io(...)` variants (`adorn_io_atom/3`) and truncating a clause body at the first unsatisfiable constraint.

The two bodies do not align one-to-one. Step 4 gives every `'$predef'` a following `'$constraint'` holding the built-in's Boolean meaning, and CLP(H) has no element for it. `modes_td_body_prog/12` therefore advances by 2 in CLP(B) for 1 in CLP(H) — and must *conjoin* that constraint, exactly as `modes_td_body/6` does. Dropping it costs this pass all the groundness contributed by built-ins, and makes step 9 abort on any program that uses them.

**9. Self-checks.** The modes from steps 7 and 8 must be identical, and re-analyzing the generated program must yield a singly-moded one. Either failing prints `% Bug: ...` and aborts the analysis rather than returning a doubtful result.

## Core term vocabulary

The same handful of shapes flows through every stage.

| shape | meaning |
|---|---|
| `obj_clause(Head, BodyList)` | the clause representation everywhere after step 2 |
| `'$constraint'(C)` | an abstract constraint goal inside a body: a list of `X = Term` in CLP(H), a Boolean formula in CLP(B) |
| `'$predef'(Atom)` | a call to a built-in, opaque to the analysis proper |
| `'$constraint'(Formula)-Atom` | a *constrained atom*, i.e. a call pattern — the unit the top-down passes work on |
| `i` / `o` | the modes: entailed ground, and everything else |

Reach `obj_clause/2` through `utils.pl`'s `clause_head/2`, `clause_body/2` and `build_clause/3`. They are only `arg/3` in disguise, but they are the abstraction boundary.

`db.pl` holds inferred information in a three-level nested `assoc`: predicate name → arity → `Id` → value, where `Id` names the kind of information (`clpb` for clauses, `mode` for inferred modes). `get_db/5` returns `[]` for a missing key rather than failing, and copies what it returns.

## The abstract domain interface

`bool_itp.pl` never calls a domain directly: it calls `Module:Pred`, with `Module` passed in. A domain module must export

```prolog
true/1  false/1  conjunction/3  satisfiable/1  entail/4
equivalent/4  union/6  widening/6  project/4
```

where `union/6` is disjunction-then-project and `widening/6` is currently just `union/6`.

Two implementations ship: `bool_op.pl` over SWI's `library(clpb)`, the default, and `bddem_op.pl` over the `bddem` pack (CUDD), with dynamic reordering switched off. `dom.pl` selects between them and re-exports the interface; `mode_analysis.pl` goes through it rather than naming a domain, and passes `current_domain/1` down to `tp/6`.

To add a third domain, implement the nine predicates, then register the module in `mod_modprop/2` (`bool_itp.pl`) and in `dom.pl`.

### Why a constraint is always a term

In both domains a constraint is a Boolean **term**, never a handle. That is forced rather than chosen: `bool_itp.pl` and `mode_analysis.pl` apply `copy_term/2` to constraints and rely on Prolog variable renaming to tie a constraint to the atom it constrains. A BDD pointer is an opaque integer that `copy_term` will not rename.

So `bddem_op` uses CUDD only as a *decision engine*, recompiling the term to a BDD at each decision point; only `project/4` converts a BDD back to a term, by Shannon decomposition over the kept variables with null branches pruned. Keeping BDDs alive across operations would mean carrying the variable list with every node and permuting indices at each conjunction — and exposing `Cudd_bddPermute` on top of what the pack already lacks.

### Two performance traps, both load-bearing

**`bool_op:project/4` re-normalises its result.** The underlying `eliminate/3` does not remove the projected variables: it keeps them syntactically, wrapped in `^` quantifiers. That is harmless for most programs — one to five of them — but on `Filex/inorder.pl` the clpb residual needed hundreds of auxiliaries, and output terms ended up carrying up to 928 quantifiers around content that never had more than 12 free variables. Every later `sat/1` or `taut/2` then redid that elimination over the whole term. `renormalise/3` rebuilds a DNF over the free variables alone, guarded to at most 12 of them and triggered only past 8 accumulated quantifiers.

Do not reintroduce a size comparison before accepting that DNF. What costs is the quantifier count, not the node count: a larger but quantifier-free DNF is much cheaper downstream, and measurably so.

**`bddem_op` switches CUDD's dynamic reordering off.** `init/1` in the pack enables group sifting unconditionally. Sifting fires on node-count thresholds reached during construction, so its cost depends on when it trips, which makes running times non-monotonic in program size. On Pos-shaped constraints the creation order is already good and sifting is pure overhead. It is not universally safe to disable, though: on formulas adversarial to the creation order it is what prevents a blow-up.

`bddem_op` also needs the local pack patch adding `exist_abstract/4` and `set_reordering/2` (`install-bddem/bddem-exist_abstract.patch`, applied by `install-bddem/fix-bddem.sh`). Without it the pack exposes no existential quantification at all, and `project/4` is impossible.

## Gotchas

**`%query:` headers.** `file_queryOfInterest/2` scans for the first line starting with `%query:` and reads the rest as a term. `%%query:` is the corpus idiom for *disabling* a query line; a file carrying only those yields `none`, and `mode_analysis/2` prints `% Please add a line like %query: p(i,o)` and fails.

**Mode letters.** `prod/3` accepts three spellings of the same pair: `i`/`o`, `b`/`f` (bound/free — this is where the `-bf` suffixes in `FilexTC` filenames come from), and `g`/`a`. The corpora use `i`/`o` exclusively.

**DCGs are silently ignored.** Term expansion being disabled, `H --> B` is read as a `-->`/2 fact. The analysis then succeeds and returns `[]` — `Filex/testdcg1.pl` gives `[]`, not an error. Never read an empty mode list as "no modes reachable" without looking at the source.

**`:- include/1` and `:- ensure_loaded/1` are off by default.** The `process_include_ensure_loaded` flag defaults to `no`, which skips the directive and prints `% <file> will not be included`. Enable it with `set_ma_flag(process_include_ensure_loaded, yes)`. Included paths are then resolved by `include_path/3` against the directory of the file holding the directive, not the process working directory, so a program can be analyzed from anywhere. The `Fs` accumulator threaded through `file_clauses/5` is the stack of files being read — most recent first, always absolute — and doubles as the re-inclusion guard. A file that cannot be found is reported and skipped rather than aborting the analysis. Only plain path atoms work: no extension guessing, no `library(...)` specs.

**Fixpoint timeouts degrade the result.** The `time_out` flag is 10 s per SCC, and `set_ma_flag/2` enforces that as a minimum. On timeout `bool_itp.pl` assigns the SCC the *top* model via `base_depart_timeout/4` and prints `% WARNING: bool fixpoint TIME OUT`. The analysis continues on that degraded model, which also propagates into step 8's body truncation. The inferred modes stay sound — the top model over-approximates — but they lose precision, and the warning is worth taking seriously rather than reading as noise.

**Some predicate names are French.** The project grew out of a francophone codebase and a number of names still are: `virer_ref` (strip references), `base_depart` (starting base), `maj_base` and `maj_prof` (update), `oprtr` (operator), and, among the local helpers of `tarjan.pl` and `bddem_op.pl`, `racines` (roots), `parcours` (traversal), `voisins_de` (neighbours of), `aretes` (edges), `depiler` (pop), `abaisser` (lower), `sommet_scc` (vertex-to-SCC), `garder` (keep), `cherche` (look up), `somme` and `produit`. All comments are in English.

**Commented-out alternatives.** Several modules carry substantial commented-out example queries and dead alternatives. They are useful as documentation, but they are not maintained: check one against the code before trusting it.

## Where the analyzer stops

`Filex/chat_pt.pl`, the CHAT-80 parser, is the practical ceiling: 158 predicates, and 9 SCCs time out in either domain, so its 347 modes rest on a degraded model. The two shapes that defeat the method are visible there — predicates of very high arity (`possessive/14`, where projection ranges over 14 variables against a corpus maximum of 8) and large mutually recursive components, in this case a grammar knot joining `np`, `pp`, `obj`, `adj_phrase`, `comp_phrase` and their neighbours.
