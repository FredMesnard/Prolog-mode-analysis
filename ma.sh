#!/bin/bash
# Command-line launcher for the mode analyzer.
#
#   ./ma.sh [options] FILE [QUERY]
#
# Without QUERY, the query is read from the file's "%query:" header. The script
# locates itself, so it works from any directory, unlike a direct swipl call
# with relative paths.
#
# See user-manual.md.

set -uo pipefail

RACINE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Which SWI-Prolog to run. A machine may carry several -- a package-manager
# build and a swipl.framework one, say -- and the bddem pack is native code
# linked against exactly one of them. This script is bash, so an interactive
# shell alias never reaches it: without SWIPL, the choice is the PATH's.
SWIPL="${SWIPL:-swipl}"

DOMAINE=bool_op
MODED=0
QUIET=0
TIMEOUT=""
FICHIER=""
REQUETE=""

usage() {
    cat <<'FIN'
Usage: ma.sh [options] FILE [QUERY]

  FILE      Prolog program to analyze
  QUERY     call pattern, e.g. "rev(i,o)".
            Omitted, it is read from the file's "%query:" header.

Options:
  -b, --bddem         bddem_op domain (CUDD) -- faster on large programs
  -c, --clpb          bool_op domain (clpb), the default
  -m, --moded         also print the generated moded program
  -t, --timeout SEC   fixpoint time limit per SCC (minimum 10, default 10)
  -q, --quiet         print the modes only
  -k, --check         check the environment and exit
  -h, --help          this help

Exit codes: 0 success, 1 analysis failed, 2 usage or environment error.

Environment:
  SWIPL     the SWI-Prolog to run, name or absolute path.
            Default: the first swipl on PATH. Set it when the machine
            carries several, since the bddem pack is native code bound
            to one of them: SWIPL=/path/to/swipl ./ma.sh -b FILE

Examples:
  ./ma.sh FilexTC/parse.pl
  ./ma.sh --bddem Filex/inorder.pl
  ./ma.sh --bddem --moded Filex/apprev.pl 'rev(o,i)'
FIN
}

erreur() { printf '\033[31mError:\033[0m %s\n' "$*" >&2; exit 2; }

# Probe only: prints ok | absent | non_patche | inconnu and never exits, so
# that --check can report instead of dying.
etat_bddem() {
    "$SWIPL" -q -g "( \\+ exists_source(library(bddem)) -> writeln(absent)
        ; catch(use_module(library(bddem)),_,fail),
          current_predicate(bddem:exist_abstract/4),
          current_predicate(bddem:set_reordering/2)
        -> writeln(ok) ; writeln(non_patche) )" -t halt 2>/dev/null | tail -1
}

# Fatal version, used before an actual bddem_op run.
#
# Every message names the SWI-Prolog concerned and carries SWIPL into the
# suggested command. The pack holds ONE native library, shared by every
# SWI-Prolog on the machine and linked against exactly one of them, so a
# rebuild launched without SWIPL silently retargets it at whatever the PATH
# offers -- undoing the install the message was asking the reader to repair.
verifier_bddem() {
    local OU; OU="$(command -v "$SWIPL")"
    case "$(etat_bddem)" in
        ok) return 0 ;;
        absent) erreur "the bddem pack is not installed for $OU.
Run:  SWIPL=$OU install-bddem/fix-bddem.sh" ;;
        non_patche) erreur "the bddem pack does not load for $OU, or lacks the
exist_abstract/4 and set_reordering/2 additions. If another SWI-Prolog on this
machine has claimed the pack's single native library, rebuild it for this one:
Run:  SWIPL=$OU install-bddem/fix-bddem.sh --clean" ;;
        *) erreur "cannot determine the state of the bddem pack for $OU." ;;
    esac
}

while [ $# -gt 0 ]; do
    case "$1" in
        -b|--bddem)   DOMAINE=bddem_op; shift ;;
        -c|--clpb)    DOMAINE=bool_op;  shift ;;
        -m|--moded)   MODED=1; shift ;;
        -q|--quiet)   QUIET=1; shift ;;
        -t|--timeout) [ $# -ge 2 ] || erreur "--timeout expects a value."
                      TIMEOUT="$2"; shift 2 ;;
        -k|--check)
            command -v "$SWIPL" >/dev/null || erreur "swipl not found. Set SWIPL=/path/to/swipl."
            echo "swipl        : $("$SWIPL" --version)"
            echo "swipl path   : $(command -v "$SWIPL")"
            echo "root         : $RACINE"
            [ -f "$RACINE/mode_analysis.pl" ] || erreur "mode_analysis.pl not found in $RACINE."
            echo "mode_analysis: found"
            case "$(etat_bddem)" in
                ok)         echo "bddem pack   : patched, bddem_op usable" ;;
                absent)     echo "bddem pack   : absent -- only clpb is usable" ;;
                non_patche) echo "bddem pack   : present but unpatched -- run install-bddem/fix-bddem.sh" ;;
                *)          echo "bddem pack   : state undetermined" ;;
            esac
            exit 0 ;;
        -h|--help)    usage; exit 0 ;;
        -*)           erreur "unknown option: $1" ;;
        *)            if [ -z "$FICHIER" ]; then FICHIER="$1"
                      elif [ -z "$REQUETE" ]; then REQUETE="$1"
                      else erreur "too many arguments: $1"; fi
                      shift ;;
    esac
done

[ -n "$FICHIER" ] || { usage; exit 2; }
command -v "$SWIPL" >/dev/null || erreur "swipl not found. Set SWIPL=/path/to/swipl."
[ -f "$RACINE/mode_analysis.pl" ] || erreur "mode_analysis.pl not found in $RACINE."
[ -f "$FICHIER" ] || erreur "file not found: $FICHIER"
[ "$DOMAINE" = bddem_op ] && verifier_bddem

if [ -n "$TIMEOUT" ]; then
    case "$TIMEOUT" in
        ''|*[!0-9]*) erreur "--timeout expects an integer." ;;
    esac
    [ "$TIMEOUT" -ge 10 ] || erreur "--timeout: minimum 10 s (enforced by set_ma_flag/2)."
fi

# Absolute path of the analyzed file: the launcher may be called from anywhere.
FICHIER_ABS="$(cd "$(dirname "$FICHIER")" && pwd)/$(basename "$FICHIER")"

# Parameters travel through the environment rather than being interpolated
# into the Prolog goal: a query containing quotes, parentheses or commas
# therefore cannot break the goal's syntax.
MA_RACINE="$RACINE" MA_FICHIER="$FICHIER_ABS" MA_REQUETE="$REQUETE" \
MA_DOMAINE="$DOMAINE" MA_MODED="$MODED" MA_QUIET="$QUIET" MA_TIMEOUT="$TIMEOUT" \
"$SWIPL" -q -g "
    getenv('MA_RACINE',R), getenv('MA_FICHIER',F),
    getenv('MA_DOMAINE',D), getenv('MA_MODED',M), getenv('MA_QUIET',Q),
    atom_concat(R,'/mode_analysis',MAM), use_module(MAM),
    atom_concat(R,'/dom',DOMM), use_module(DOMM,[set_domain/1]),
    set_domain(D),
    ( getenv('MA_TIMEOUT',TO), TO \\== ''
    -> atom_concat(R,'/flag',FL), use_module(FL,[set_ma_flag/2]),
       atom_number(TO,TON), set_ma_flag(time_out,TON)
    ;  true ),
    ( getenv('MA_REQUETE',RQ), RQ \\== ''
    -> term_to_atom(QT,RQ), initial_constraint_atom_from_atom(QT,IQ),
       ( M == '1'
       -> mode_analysis(IQ,F,C,_,MProg,MModes)
       ;  mode_analysis(F,IQ,C) )
    ;  ( M == '1'
       -> mode_analysis:initial_constraint_atom_from_file(F,IQ),
          mode_analysis(IQ,F,C,_,MProg,MModes)
       ;  mode_analysis(F,C) ) ),
    ( Q == '1'
    -> true
    ;  format('domain : ~w~nfile   : ~w~n~n',[D,F]) ),
    format('modes : ~w~n',[C]),
    ( M == '1'
    -> format('~nmoded program modes : ~w~n~nmoded program :~n',[MModes]),
       forall(member(Cl,MProg), \\+ \\+ (numbervars(Cl,0,_), print(Cl), nl))
    ;  true )
" -t halt
