"""Slice declaration keywords and statement text out of Lean source files.

The lexical helpers here (``code_view``, ``_read_token``, ``_strip_prefixes``
and the statement/body boundary scanner) are adapted from
``scripts/proof-profile/statements.py``. They are copied rather than imported
because that script is fetched standalone from ``origin/main`` in CI and
lives in a different tree; see its docstrings for the original rationale.

The entry point is :func:`statement_slice`: given a pre-parsed
:class:`SourceFile` and a declaration's source range plus name selection, it
returns the refined declaration keyword (``lemma`` vs ``theorem``, ``abbrev``
vs ``def``, ...) and the statement text — the original source from the
keyword up to the top-level ``:=`` / ``where`` / ``|``-arm boundary.
"""

from __future__ import annotations

import re
from collections.abc import Sequence
from dataclasses import dataclass

# Keywords whose presence in the source refines the extractor's coarse kind.
DECLARATION_KEYWORDS = frozenset(
    {
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "structure",
        "class",
        "inductive",
        "opaque",
        "axiom",
    }
)

# Modifiers that may sit between the range start and the declaration keyword
# (from statements.py; ``@[...]`` attributes and ``... in`` prefixes are
# handled structurally, not through this set).
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

OPEN_BRACKETS = "([{⟨⦃"
CLOSE_BRACKETS = ")]}⟩⦄"

# Characters that terminate the name token following a declaration keyword.
NAME_STOP = set(" \t\r\n({[⦃⟨:=")

# Maximum statement length emitted into the site data (schema: <= 1200).
STATEMENT_CHARACTER_LIMIT = 1200

_WHERE_RE = re.compile(r"(?<![\w.'])where(?![\w'])")
_IN_RE = re.compile(r"(?<![\w.'])in(?![\w'])")


def code_view(text: str) -> str:
    """Return ``text`` with comments and string literals blanked to spaces.

    Copied from ``scripts/proof-profile/statements.py``. Length and newline
    positions are preserved so indices computed on the result line up with
    the original source. Block comments (``/- -/``) nest, which also covers
    doc comments (``/-- -/``) and module docs (``/-! -/``).
    """
    out: list[str] = []
    i, n = 0, len(text)
    normal, line, block, string_literal = 0, 1, 2, 3
    state = normal
    block_depth = 0
    while i < n:
        c = text[i]
        two = text[i : i + 2]
        if state == normal:
            if two == "--":
                out.append("  ")
                i += 2
                state = line
                continue
            if two == "/-":
                out.append("  ")
                i += 2
                state = block
                block_depth = 1
                continue
            if c == '"':
                out.append(" ")
                i += 1
                state = string_literal
                continue
            out.append(c)
            i += 1
        elif state == line:
            if c == "\n":
                out.append("\n")
                state = normal
            else:
                out.append(" ")
            i += 1
        elif state == block:
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
                    state = normal
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
        else:  # string literal
            if c == "\\":
                out.append("  " if i + 1 < n else " ")
                i += 2
                continue
            if c == '"':
                out.append(" ")
                state = normal
                i += 1
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
    return "".join(out)


def _read_token(code: str, pos: int, end: int) -> str:
    """Read one token starting at ``pos`` (from statements.py)."""
    j = pos
    while j < end and code[j] not in NAME_STOP and code[j] != "@":
        j += 1
    return code[pos:j]


def _strip_prefixes(code: str, start: int, end: int) -> int:
    """Skip attributes / modifiers / ``... in`` prefixes; return keyword index.

    Copied from ``scripts/proof-profile/statements.py``. Doc comments have
    already been blanked by :func:`code_view`, so leading whitespace covers
    them too.
    """
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
        token = _read_token(code, pos, end)
        if token in MODIFIERS:
            pos += len(token)
            continue
        if token in ("set_option", "open"):
            match = _IN_RE.search(code, pos, end)
            if match:
                pos = match.end()
                continue
        break
    return pos


def _line_prefix(code: str, pos: int) -> str:
    """Return the text on ``pos``'s line, up to ``pos`` (from statements.py)."""
    start = code.rfind("\n", 0, pos) + 1
    return code[start:pos]


def _find_boundary(
    code: str, start: int, end: int, bar_always_ends: bool = False
) -> int:
    """Return the index in ``[start, end)`` where the declaration body begins.

    Adapted from ``scripts/proof-profile/statements.py``. Bracket depth is
    tracked locally. The body begins at the first top-level ``:=`` or
    ``where``, or — for equation-compiler declarations — at the first
    line-leading ``|`` arm (recognised by a following top-level ``=>``).
    When ``bar_always_ends`` is set (inductive-like declarations, whose
    constructor arms carry no ``=>``), any line-leading top-level ``|`` ends
    the statement. Returns ``end`` if no boundary is found.
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
                # `=>` arrives before any top-level `:=`/`where` (keeps an
                # absolute-value bar in a type from being read as an arm).
                b_bar = seen_bars[0]
            elif b_where is None and _WHERE_RE.match(code, i):
                b_where = i
            if c == "|" and _line_prefix(code, i).strip() == "":
                seen_bars.append(i)
                if bar_always_ends and b_bar is None:
                    b_bar = i
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        i += 1
    candidates = [b for b in (b_assign, b_where, b_bar) if b is not None]
    return min(candidates) if candidates else end


@dataclass
class SourceFile:
    """One Lean source file, read once and pre-processed for slicing."""

    text: str
    code: str
    line_offsets: list[int]

    @classmethod
    def from_text(cls, text: str) -> SourceFile:
        """Build a :class:`SourceFile` (blanked view + line offsets) from text."""
        offsets = [0]
        for index, character in enumerate(text):
            if character == "\n":
                offsets.append(index + 1)
        return cls(text=text, code=code_view(text), line_offsets=offsets)

    def offset(self, line: int, column: int) -> int:
        """Return the character offset of 1-based ``line`` / 0-based ``column``."""
        if line < 1:
            return 0
        if line > len(self.line_offsets):
            return len(self.text)
        return min(self.line_offsets[line - 1] + max(column, 0), len(self.text))


def _next_token(code: str, pos: int, end: int) -> str:
    """Return the next token at or after ``pos``, skipping whitespace."""
    while pos < end and code[pos] in " \t\r\n":
        pos += 1
    return _read_token(code, pos, end)


def _boundary_scan_start(
    source: SourceFile,
    keyword_position: int,
    keyword_length: int,
    selection: Sequence[int],
    end: int,
) -> int:
    """Return where the body-boundary scan starts: after the name token.

    The extractor's selection points at the declaration's name token; scanning
    from past it mirrors ``statements.py`` (which scans from after the parsed
    name). When the selection is unusable, scan from after the keyword.
    """
    selection_offset = source.offset(selection[0], selection[1])
    after_keyword = keyword_position + keyword_length
    if selection_offset < after_keyword or selection_offset >= end:
        return after_keyword
    name_end = selection_offset
    while name_end < end and source.code[name_end] not in NAME_STOP:
        name_end += 1
    return name_end


def statement_slice(
    source: SourceFile,
    declaration_range: Sequence[int],
    selection: Sequence[int],
    fallback_kind: str,
) -> tuple[str, str]:
    """Return ``(kind, statement)`` for one declaration.

    ``declaration_range`` is ``[startLine, startCol, endLine, endCol]`` with
    1-based lines; ``selection`` is the ``[line, col]`` of the name token.
    ``kind`` is the source keyword when it is a known declaration keyword
    (``class inductive`` reports ``class``), else ``fallback_kind``. The
    statement is original source from the keyword to the body boundary,
    trimmed only at the edges and capped at 1200 characters.
    """
    start = source.offset(declaration_range[0], declaration_range[1])
    end = source.offset(declaration_range[2], declaration_range[3])
    if end <= start:
        return fallback_kind, ""
    code = source.code
    keyword_position = _strip_prefixes(code, start, end)
    keyword = _read_token(code, keyword_position, end)
    kind = keyword if keyword in DECLARATION_KEYWORDS else fallback_kind
    if keyword not in DECLARATION_KEYWORDS:
        # Attribute/deriving-generated declarations (`@[simps]`, `deriving
        # DecidableEq`, `to_additive`, ...) point their range at a mid-line
        # token; slicing from there yields a meaningless fragment.
        line_start = source.line_offsets[declaration_range[0] - 1]
        if source.text[line_start:start].strip():
            return fallback_kind, ""
    inductive_like = keyword == "inductive" or (
        keyword == "class"
        and _next_token(code, keyword_position + len(keyword), end) == "inductive"
    )
    scan_start = _boundary_scan_start(
        source, keyword_position, len(keyword), selection, end
    )
    boundary = _find_boundary(code, scan_start, end, bar_always_ends=inductive_like)
    statement = source.text[keyword_position:boundary].strip()
    if len(statement) > STATEMENT_CHARACTER_LIMIT:
        statement = statement[: STATEMENT_CHARACTER_LIMIT - 1].rstrip() + "…"
    return kind, statement
