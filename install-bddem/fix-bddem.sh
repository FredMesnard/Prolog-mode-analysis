#!/bin/bash
# Installs the SWI-Prolog "bddem" pack on macOS by BUILDING IT FROM SOURCE
# (the bundled CUDD 3.0.0 + bddem.c), rather than using the prebuilt binary
# the pack ships.
#
# Why this script is needed -- two blockers:
#
#  1. The shipped lib/<arch>/bddem.so links against "@rpath/libswipl.10.dylib".
#     In a framework-style macOS install that file does not exist: the library
#     IS swipl.framework/Versions/A/swipl. So dlopen fails, and -- the trap --
#     use_module(library(bddem)) APPEARS to succeed while every native
#     predicate stays undefined.
#
#  2. Building as-is does not work either:
#     a) the pack's configure calls aclocal (automake) to bootstrap CUDD,
#        which ships only configure.ac / Makefile.am;
#     b) autoreconf wants "libtoolize", which Homebrew names "glibtoolize";
#     c) at link time swipl-ld unconditionally adds "-L$PLLIBDIR -lswipl",
#        but in a framework build PLLIBDIR does not exist. So we link against
#        the framework ourselves (-framework swipl), which yields the same
#        @rpath dependency the swipl executable itself carries.
#
# The script is idempotent and self-verifying (dlopen + the pack's tests).
#
# Usage :  ./fix-bddem.sh                    (uses the swipl on PATH)
#          SWIPL=/path/to/swipl ./fix-bddem.sh
#          ./fix-bddem.sh --clean            (full rebuild)



set -uo pipefail

die()  { printf '\033[31mError:\033[0m %s\n' "$*" >&2; exit 1; }
info() { printf '\033[34m==>\033[0m %s\n' "$*"; }
ok()   { printf '\033[32m  OK\033[0m %s\n' "$*"; }
warn() { printf '\033[33mWarning:\033[0m %s\n' "$*"; }

# Resolved BEFORE any cd, and in absolute form: the script then moves into the
# pack directory, where "$(dirname "$0")" would become a dangling relative
# path. A call such as "./install-bddem/fix-bddem.sh" used to lose the patch,
# and the build carried on without it.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

CLEAN=0
[ "${1:-}" = "--clean" ] && CLEAN=1

[ "$(uname -s)" = "Darwin" ] || die "this script is for macOS only."

SWIPL=${SWIPL:-$(command -v swipl)}
[ -n "$SWIPL" ] && [ -x "$SWIPL" ] || die "swipl not found. Set SWIPL=/path/to/swipl."
info "swipl : $SWIPL"
"$SWIPL" --version || die "this swipl does not run."

# --- Build variables of THIS swipl ------------------------------------------
RTV=$("$SWIPL" --dump-runtime-variables) || die "--dump-runtime-variables failed."
PLARCH=$(sed  -n 's/^PLARCH="\(.*\)";/\1/p'   <<<"$RTV")
PLSOEXT=$(sed -n 's/^PLSOEXT="\(.*\)";/\1/p'  <<<"$RTV")
PLBASE=$(sed  -n 's/^PLBASE="\(.*\)";/\1/p'   <<<"$RTV")
PLLIBDIR=$(sed -n 's/^PLLIBDIR="\(.*\)";/\1/p' <<<"$RTV")
[ -n "$PLARCH" ] && [ -n "$PLSOEXT" ] || die "cannot read PLARCH/PLSOEXT."
info "arch=$PLARCH  soext=$PLSOEXT"

# --- Build tools ------------------------------------------------------------
command -v cc >/dev/null || die "no C compiler. Install the Command Line Tools: xcode-select --install"

# autoreconf looks for "libtoolize"; Homebrew installs it as "glibtoolize"
# and provides the GNU names in a dedicated gnubin directory.
if ! command -v libtoolize >/dev/null 2>&1; then
    for D in /usr/local/opt/libtool/libexec/gnubin /opt/homebrew/opt/libtool/libexec/gnubin; do
        [ -x "$D/libtoolize" ] && { PATH="$D:$PATH"; export PATH; info "libtoolize picked up from $D"; break; }
    done
fi

MISSING=""
for T in aclocal automake autoconf libtoolize; do
    command -v "$T" >/dev/null 2>&1 || MISSING="$MISSING $T"
done
if [ -n "$MISSING" ]; then
    die "missing tools:$MISSING
Install them, for instance:   brew install automake autoconf libtool"
fi
ok "autotools present ($(aclocal --version | head -1))"

# --- Is the pack installed? -------------------------------------------------
packdir() { "$SWIPL" -q -g "absolute_file_name(pack(bddem),D,[file_type(directory),file_errors(fail)]),writeln(D)" -t halt 2>/dev/null; }
PACKDIR=$(packdir)
if [ -z "$PACKDIR" ] || [ ! -d "$PACKDIR" ]; then
    info "bddem pack absent, downloading..."
    "$SWIPL" -q -g "pack_install(bddem,[interactive(false),test(false),build(none)])" -t halt \
        || "$SWIPL" -q -g "pack_install(bddem,[interactive(false),test(false)])" -t halt \
        || die "pack_install failed."
    PACKDIR=$(packdir)
    [ -n "$PACKDIR" ] || die "pack still not found after installation."
fi
info "pack : $PACKDIR"
cd "$PACKDIR" || die "cannot enter $PACKDIR."

[ -f bddem.c ] || die "bddem.c missing: unexpected pack layout."
[ -d cudd-3.0.0 ] || die "cudd-3.0.0 missing: unexpected pack layout."

# --- exist_abstract/4 patch -------------------------------------------------
# Exposes Cudd_bddExistAbstract, which CUDD already implements but bddem did
# not wrap. Without it, projecting k variables forces the term-level expansion
# "exists x F <=> F(0) or F(1)", in 2^k.
PATCH="$SCRIPT_DIR/bddem-exist_abstract.patch"
if grep -q 'exist_abstract' bddem.c 2>/dev/null; then
    ok "exist_abstract/4 already present in the sources"
elif [ -f "$PATCH" ]; then
    if git apply --check "$PATCH" 2>/dev/null; then
        git apply "$PATCH" && ok "exist_abstract/4 patch applied"
    elif patch -p1 --dry-run < "$PATCH" >/dev/null 2>&1; then
        patch -p1 < "$PATCH" >/dev/null && ok "exist_abstract/4 patch applied (via patch)"
    else
        warn "the exist_abstract/4 patch does not apply to this version of the pack; carrying on without it."
    fi
else
    warn "exist_abstract/4 patch not found ($PATCH); carrying on without it."
fi

# --- Backup of the existing binary ------------------------------------------
LIBDIR="lib/$PLARCH"
LIB="$LIBDIR/bddem.$PLSOEXT"
# One backup only, of the binary the pack ships, taken on the first pass:
# later runs must not pile up copies of our own builds.
BACKUP="$LIB.prebuilt-original"
if [ -f "$LIB" ] && [ ! -f "$BACKUP" ]; then
    cp -p "$LIB" "$BACKUP" && ok "the pack's original binary saved to $PACKDIR/$BACKUP"
fi

# --- Autotools bootstrap + configure ----------------------------------------
if [ "$CLEAN" = "1" ]; then
    info "full clean"
    make distclean >/dev/null 2>&1
    rm -f bddem.o "bddem.$PLSOEXT"
fi

if [ "$CLEAN" = "1" ] || [ ! -f cudd-3.0.0/Makefile ]; then
    info "configuring (aclocal + autoreconf + CUDD configure) -- please wait"
    ./configure > /tmp/bddem-configure.$$.log 2>&1 \
        || { tail -30 /tmp/bddem-configure.$$.log; die "configure failed (log: /tmp/bddem-configure.$$.log)"; }
    ok "configuration done"
else
    ok "CUDD already configured (use --clean to redo everything)"
fi

# --- Build CUDD, then bddem.c -----------------------------------------------
info "building CUDD and bddem.c -- please wait"
make bddem.o > /tmp/bddem-make.$$.log 2>&1 \
    || { tail -30 /tmp/bddem-make.$$.log; die "the build failed (log: /tmp/bddem-make.$$.log)"; }
[ -f bddem.o ] || die "bddem.o was not produced."
CUDD_A=$(ls cudd-3.0.0/cudd/.libs/libcudd.a 2>/dev/null)
[ -n "$CUDD_A" ] || die "libcudd.a was not produced."
ok "objects built"

# --- Linking ----------------------------------------------------------------
# Two cases, depending on the SWI-Prolog install.
LINK_DONE=0
if [ -n "$PLLIBDIR" ] && ls "$PLLIBDIR"/libswipl.*.dylib >/dev/null 2>&1; then
    # Ordinary install: swipl-ld knows what to do.
    info "linking via swipl-ld (libswipl found in $PLLIBDIR)"
    SWIPL_LD="$(dirname "$SWIPL")/swipl-ld"
    [ -x "$SWIPL_LD" ] || die "swipl-ld not found next to swipl."
    "$SWIPL_LD" bddem.o -shared -Lcudd-3.0.0/cudd/.libs/ -lcudd -o "bddem.$PLSOEXT" \
        && LINK_DONE=1
fi
if [ "$LINK_DONE" = "0" ]; then
    # Framework install: PLLIBDIR does not exist, so we link against the
    # framework, which yields the @rpath/swipl.framework/... dependency --
    # exactly the one the swipl executable carries.
    case "$PLBASE" in
        */swipl.framework/*) : ;;
        *) die "neither libswipl.dylib in PLLIBDIR ($PLLIBDIR), nor a framework install (PLBASE=$PLBASE).
Cannot determine how to link." ;;
    esac
    FW_DIR="${PLBASE%%/swipl.framework/*}"
    [ -d "$FW_DIR/swipl.framework" ] || die "framework not found under $FW_DIR."
    info "linking against the framework ($FW_DIR/swipl.framework)"
    cc -o "bddem.$PLSOEXT" -shared bddem.o -Lcudd-3.0.0/cudd/.libs/ -lcudd \
       -F"$FW_DIR" -framework swipl -Wl,-rpath,"$FW_DIR" \
        || die "linking failed."
fi
[ -f "bddem.$PLSOEXT" ] || die "bddem.$PLSOEXT was not produced."
ok "library linked"

# --- Installation -----------------------------------------------------------
mkdir -p "$LIBDIR"
cp "bddem.$PLSOEXT" "$LIB" || die "cannot copy into $LIBDIR."
# Any Mach-O write invalidates the signature: ad-hoc re-signing, required on
# Apple Silicon.
codesign --force --sign - "$LIB" >/dev/null 2>&1 || warn "codesign failed (may be a problem on Apple Silicon)."
ok "installed in $PACKDIR/$LIB"
otool -L "$LIB" | sed -n '2,4p'

# --- Verification -----------------------------------------------------------
info "check: loading the foreign library"
# Do not wrap in a catch-all: halt/1 raises unwind(halt(_)), which a variable
# catcher intercepts, turning success into failure.
"$SWIPL" -q -g "load_foreign_library('$PACKDIR/$LIB')" -t halt \
    || die "the library does not load."
ok "dlopen succeeded"

# The pack's 18 tests do NOT cover our two additions: without this check, an
# unapplied patch came out as success, with a bddem unusable for bddem_op.
info "check: the primitives added by the patch"
"$SWIPL" -q -g "load_foreign_library('$PACKDIR/$LIB'),
        ( current_predicate(exist_abstract/4), current_predicate(set_reordering/2)
        -> true ; halt(1) )" -t halt \
    || die "exist_abstract/4 or set_reordering/2 are missing: the patch was not applied.
Check that bddem-exist_abstract.patch sits next to this script ($SCRIPT_DIR),
then run again."
ok "exist_abstract/4 and set_reordering/2 present"

if [ -f prolog/bddem_test.pl ]; then
    info "check: the pack's test suite"
    # The pack Makefile's "installcheck" target is stale (it calls test/0,
    # which does not exist); the tests are plunit.
    "$SWIPL" -q -g "use_module('$PACKDIR/prolog/bddem_test.pl'),(run_tests->halt(0);halt(1))" -t "halt(1)" \
        || die "some of the pack's tests fail."
    ok "all of the pack's tests pass"
else
    warn "test file absent, verification limited to loading."
fi

# --- Pack status ------------------------------------------------------------
if [ -f status.db ] && grep -q "downloaded" status.db; then
    sed -i.bak "s/,downloaded)\./,built)./" status.db && ok "status.db: marked \"built\""
fi

printf '\n\033[32mbddem is built from source and operational.\033[0m\n'
