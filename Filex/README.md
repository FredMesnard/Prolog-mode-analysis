# Test corpora — provenance and attribution

`Filex/` and `FilexTC/` hold Prolog programs used as a test corpus for [Prolog-mode-analysis](../README.md). They are **inputs to the analyzer, not part of it**, and the LGPL notice covering the analyzer does not extend to them.

Most are small textbook predicates — `append/3`, `reverse/2`, `quicksort/2`, and the like — of no identifiable authorship, circulated in the logic-programming community for decades. Several, however, are recognisable programs by named authors, reproduced here because they have long served as reference benchmarks for Prolog analysis. They are included for that purpose alone, with no claim of ownership, and every original header has been left intact.

| file | author, as declared in the file |
|---|---|
| `Filex/chat_pt.pl.too.hard` | the CHAT-80 parser, Fernando C. N. Pereira and David H. D. Warren |
| `Filex/qplan.pl` | the CHAT-80 query planner, David H. D. Warren |
| `Filex/read.pl` | a Prolog reader, David H. D. Warren and Richard O'Keefe, later modified by Alan Mycroft |
| `Filex/mmatrix.pl` | matrix multiplication benchmark, **"Copyright by Manuel Hermenegildo"**, 1986 |
| `Filex/peephole.pl` | a peephole optimizer, author line present but blank |

`Filex/mmatrix.pl` is the only file carrying an explicit copyright notice. It is reproduced verbatim, header included.

If you are one of these authors, or hold rights in any of these programs, and would rather the file were removed or its attribution corrected, please open an issue — it will be acted on.

## Which corpus is which

- **`FilexTC/`** — 90 small programs, each with an active `%query:` header. This is the regression set: all 90 must analyze successfully.
- **`Filex/`** — 53 larger, messier real programs, 38 with an active query. Not a clean baseline. `read.pl` is slow enough to exclude from a sweep by hand (~49 s under clpb). A 54th program, `chat_pt.pl.too.hard`, is excluded by its name: the suffix keeps it out of every `Filex/*.pl` glob because it takes ~5 min under bddem, does not finish after 10 min under clpb, and times out on 9 strongly connected components either way. Rename it back to `.pl` to include it.
