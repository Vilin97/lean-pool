"""Textual detection of Lean *statement* changes between two file revisions.

Fetched from origin/main and imported by
``.github/workflows/proof-profile.yml``'s render step so the proof profile
can report, for a refactor PR, whether any declaration changed its
*statement* (its signature: name, binders, and type) rather than only its
proof or definition body. That is the "did this golf touch a theorem?"
question — the reassurance a maintainer wants from a refactor.

The approach is the same as physlib's ``check_golf.py``: parse each side
textually — no Lean build — by stripping comments and string literals,
tracking bracket depth, and splitting each declaration at the top-level
``:=`` / ``where`` that separates its statement from its body. Proof terms
embedded inside a *type* (``⟨x, by omega⟩``, ``(by decide)``) are masked so
that golfing them is not mistaken for a statement change (they are
proof-irrelevant). Only stdlib is used, because this module is fetched and
run standalone in CI, not installed as part of the ``lean_pool`` package.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

# Keywords that introduce a named declaration whose statement we track.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
    "structure",
    "inductive",
    "class",
    "opaque",
)

# Modifiers that may sit between the line start and the declaration keyword
# (``@[...]`` attributes and ``set_option ... in`` / ``open ... in`` prefixes
# are handled structurally, not through this set).
MODIFIERS = {
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "nonrec",
    "scoped",
    "local",
    "mutual",
}

# Keywords that open/close a namespacing scope.
SCOPE_KEYWORDS = {"namespace", "section", "end"}

OPEN_BRACKETS = "([{⟨⦃"
CLOSE_BRACKETS = ")]}⟩⦄"

# Characters that terminate the name token following a declaration keyword.
NAME_STOP = set(" \t\r\n({[⦃⟨:=")


# --------------------------------------------------------------------------- #
# Lean lexical pre-processing
# --------------------------------------------------------------------------- #
def code_view(text: str) -> str:
    """Return ``text`` with comments and string literals blanked to spaces.

    Length and newline positions are preserved so indices computed on the
    result line up with the original source. Block comments (``/- -/``) nest,
    which also covers doc comments (``/-- -/``) and module docs (``/-! -/``).
    """
    out: list[str] = []
    i, n = 0, len(text)
    NORMAL, LINE, BLOCK, STR = 0, 1, 2, 3
    state = NORMAL
    block_depth = 0
    while i < n:
        c = text[i]
        two = text[i : i + 2]
        if state == NORMAL:
            if two == "--":
                out.append("  ")
                i += 2
                state = LINE
                continue
            if two == "/-":
                out.append("  ")
                i += 2
                state = BLOCK
                block_depth = 1
                continue
            if c == '"':
                out.append(" ")
                i += 1
                state = STR
                continue
            out.append(c)
            i += 1
        elif state == LINE:
            if c == "\n":
                out.append("\n")
                state = NORMAL
            else:
                out.append(" ")
            i += 1
        elif state == BLOCK:
            if two == "/-":
                out.append("  ")
                i += 2
                block_depth += 1
                continue
            if two == "-/":
                out.append("  ")
                i += 2
                block_depth -= 1
                if block_depth == 0:
                    state = NORMAL
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
        else:  # STR
            if c == "\\":
                out.append("  " if i + 1 < n else " ")
                i += 2
                continue
            if c == '"':
                out.append(" ")
                state = NORMAL
                i += 1
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
    return "".join(out)


def normalize(fragment: str) -> str:
    """Collapse whitespace so pure reformatting is not seen as a change."""
    return " ".join(fragment.split())


# A leading underscore run at the start of an identifier token — the marker a
# golf adds to a binder that its shorter proof no longer uses (`hM` -> `_hM`).
_LEADING_UNDERSCORE_RE = re.compile(r"(?<![\w'])_+(?=[A-Za-z])")


def ignore_underscore_binders(signature: str) -> str:
    """Drop leading underscores from identifier tokens in a signature.

    Renaming a binder to a ``_``-prefixed name (to mark it unused) is the one
    signature edit a golf routinely makes, and it does *not* change the
    proposition: binder names are alpha-equivalent, so ``∀ (hM : p), q`` and
    ``∀ (_hM : p), q`` are the same type. Stripping the leading underscores
    lets us tell such a rename apart from a genuine change to the type.
    """
    return _LEADING_UNDERSCORE_RE.sub("", signature)


def _ident_char(c: str) -> bool:
    return c.isalnum() or c in "_.'" or ord(c) > 127


def mask_by_blocks(sig_code: str) -> str:
    """Blank the contents of ``by`` tactic blocks embedded inside a statement.

    A statement's *type* can embed proof terms — ``⟨x, by omega⟩`` or an
    argument such as ``(by decide)``. By proof irrelevance those tactic
    blocks do not affect the elaborated type, so golfing them keeps the
    statement. Each embedded ``by`` block runs to the end of its enclosing
    bracket group; we replace it with a placeholder so signatures that
    differ only inside such blocks compare equal.
    """
    out: list[str] = []
    i, n = 0, len(sig_code)
    depth = 0
    while i < n:
        if (
            sig_code[i : i + 2] == "by"
            and (i == 0 or not _ident_char(sig_code[i - 1]))
            and (i + 2 >= n or not _ident_char(sig_code[i + 2]))
        ):
            d0 = depth
            out.append("by<>")
            i += 2
            while i < n:
                c = sig_code[i]
                if c in OPEN_BRACKETS:
                    depth += 1
                elif c in CLOSE_BRACKETS:
                    if depth == d0:
                        break  # close bracket of the enclosing group
                    depth -= 1
                i += 1
            continue
        c = sig_code[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        out.append(c)
        i += 1
    return normalize("".join(out))


# --------------------------------------------------------------------------- #
# Declaration extraction
# --------------------------------------------------------------------------- #
@dataclass
class Decl:
    """A named declaration and its statement (the part before the body)."""

    name: str
    keyword: str
    signature: str  # normalized statement (keyword .. up to `:=` / `where`)
    signature_masked: str  # same, with embedded `by` proof blocks blanked


def _line_prefix(code: str, pos: int) -> str:
    """The text on ``pos``'s line, up to ``pos`` (from the previous newline)."""
    start = code.rfind("\n", 0, pos) + 1
    return code[start:pos]


_WHERE_RE = re.compile(r"(?<![\w.'])where(?![\w'])")


def _block_starts(code: str) -> list[int]:
    """Indices of top-level command starts: non-blank characters in column 0.

    In Mathlib-style Lean, top-level commands (``lemma``, ``def``,
    ``namespace``, ...) begin in column 0, while everything that belongs to a
    command — multi-line signatures, tactic blocks, term proofs — is
    indented. Segmenting on column-0 lines is robust even when a proof body
    contains brackets we cannot balance textually.
    """
    starts = [0] if code and not code[0].isspace() else []
    for i in range(1, len(code)):
        if code[i - 1] == "\n" and not code[i].isspace() and code[i] != "\n":
            starts.append(i)
    return starts


def _read_token(code: str, pos: int, end: int) -> str:
    j = pos
    while j < end and code[j] not in NAME_STOP and code[j] != "@":
        j += 1
    return code[pos:j]


def _strip_prefixes(code: str, start: int, end: int) -> int:
    """Skip attributes / modifiers / ``... in`` prefixes; return keyword index."""
    pos = start
    while pos < end:
        while pos < end and code[pos] in " \t\r\n":
            pos += 1
        if pos >= end:
            break
        if code[pos] == "@" and pos + 1 < end and code[pos + 1] == "[":
            depth = 0
            while pos < end:
                if code[pos] == "[":
                    depth += 1
                elif code[pos] == "]":
                    depth -= 1
                    if depth == 0:
                        pos += 1
                        break
                pos += 1
            continue
        tok = _read_token(code, pos, end)
        if tok in MODIFIERS:
            pos += len(tok)
            continue
        if tok in ("set_option", "open"):
            m = re.compile(r"(?<![\w.'])in(?![\w'])").search(code, pos, end)
            if m:
                pos = m.end()
                continue
        break
    return pos


def _find_boundary(code: str, start: int, end: int) -> int:
    """Index in ``[start, end)`` where the statement ends and the body begins.

    Bracket depth is tracked *locally* to this declaration. The body begins
    at the first top-level ``:=`` or ``where``, or — for equation-compiler
    declarations that have neither — at the first line-leading ``|`` arm
    (recognised by a following top-level ``=>``, which distinguishes a real
    arm from an absolute value ``|x|`` in a type). Returns ``end`` if none.
    """
    b_assign = b_where = b_bar = None
    seen_bars: list[int] = []
    depth = 0
    i = start
    while i < end:
        c = code[i]
        if depth == 0:
            if b_assign is None and code[i : i + 2] == ":=":
                b_assign = i
            elif (
                code[i : i + 2] == "=>"
                and seen_bars
                and b_bar is None
                and b_assign is None
                and b_where is None
            ):
                # A line-leading `|` is an equation-compiler arm only if its
                # `=>` arrives before any top-level `:=`/`where`. This keeps an
                # absolute-value bar in the type (`|x| ≤ ε`) from being read as
                # an arm — its nearest `=>` is inside the proof, after the `:=`
                # — while still catching a genuine `def f : T | p => e` (whose
                # arm `=>` precedes any `:=` sitting inside a later arm body).
                b_bar = seen_bars[0]
            elif b_where is None and _WHERE_RE.match(code, i):
                b_where = i
            if c == "|" and _line_prefix(code, i).strip() == "":
                seen_bars.append(i)
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        i += 1
    candidates = [b for b in (b_assign, b_where, b_bar) if b is not None]
    return min(candidates) if candidates else end


def _apply_scope(stack: list[tuple[str, str]], keyword: str, name: str) -> None:
    if keyword == "namespace":
        stack.append(("namespace", name))
    elif keyword == "section":
        stack.append(("section", name))
    else:  # end
        if name:
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][1] == name:
                    del stack[k:]
                    return
            if stack:
                stack.pop()
        elif stack:
            stack.pop()


def parse_decls(text: str) -> dict[str, Decl]:
    """Parse ``text`` into a map from qualified name to :class:`Decl`."""
    code = code_view(text)
    starts = _block_starts(code)
    ns_stack: list[tuple[str, str]] = []
    result: dict[str, Decl] = {}
    seen: dict[str, int] = {}

    for idx, start in enumerate(starts):
        end = starts[idx + 1] if idx + 1 < len(starts) else len(code)
        kw_pos = _strip_prefixes(code, start, end)
        keyword = _read_token(code, kw_pos, end)

        if keyword in SCOPE_KEYWORDS:
            rest = code[kw_pos + len(keyword) : end].split("\n", 1)[0].strip()
            name = rest.split()[0] if rest else ""
            _apply_scope(ns_stack, keyword, name)
            continue
        if keyword not in DECL_KEYWORDS:
            continue

        # Parse the declaration name.
        j = kw_pos + len(keyword)
        while j < end and code[j] in " \t\r\n":
            j += 1
        k = j
        while k < end and code[k] not in NAME_STOP:
            k += 1
        local = code[j:k]
        if not local:
            continue  # anonymous instance / example — cannot track by name

        boundary = _find_boundary(code, k, end)
        sig_code = code[kw_pos:boundary]
        signature = normalize(sig_code)
        signature_masked = mask_by_blocks(sig_code)

        prefix = ".".join(
            nm for kind, nm in ns_stack if kind == "namespace" and nm
        )
        qualified = (prefix + "." + local) if prefix else local
        if qualified in seen:
            seen[qualified] += 1
            qualified = f"{qualified}#{seen[qualified]}"
        else:
            seen[qualified] = 0
        result[qualified] = Decl(qualified, keyword, signature, signature_masked)
    return result


# --------------------------------------------------------------------------- #
# Comparison
# --------------------------------------------------------------------------- #
@dataclass
class StatementDiff:
    """Which declarations changed statement between two revisions of a file."""

    statement_changed: list[str]  # signature (type) genuinely changed
    binder_renamed: list[str]  # only binder names differ; proposition unchanged
    added: list[str]  # declarations new in head
    removed: list[str]  # declarations gone from head
    head_decl_count: int  # named declarations in the head revision


def compare_statements(base_src: str, head_src: str) -> StatementDiff:
    """Compare two revisions of a file and classify statement changes.

    A declaration counts as ``statement_changed`` only when the elaborated
    *type* really changed. Signature edits that leave the proposition intact
    are excluded: golfing a ``by`` proof term embedded in the type
    (proof-irrelevant), and renaming a binder — most often to a ``_``-prefixed
    unused marker — which is reported separately as ``binder_renamed``.
    Golfing a proof or a definition body (type preserved) is not a statement
    change at all.
    """
    base = parse_decls(base_src)
    head = parse_decls(head_src)
    statement_changed: list[str] = []
    binder_renamed: list[str] = []
    added: list[str] = []
    removed: list[str] = []
    for name, d in head.items():
        b = base.get(name)
        if b is None:
            added.append(name)
            continue
        if b.signature == d.signature:
            continue
        if b.signature_masked == d.signature_masked:
            continue  # only an embedded `by` proof term differs; type unchanged
        if ignore_underscore_binders(b.signature_masked) == ignore_underscore_binders(
            d.signature_masked
        ):
            binder_renamed.append(name)  # only a `_`-binder rename; type unchanged
        else:
            statement_changed.append(name)
    for name in base:
        if name not in head:
            removed.append(name)
    return StatementDiff(
        statement_changed=statement_changed,
        binder_renamed=binder_renamed,
        added=added,
        removed=removed,
        head_decl_count=len(head),
    )
