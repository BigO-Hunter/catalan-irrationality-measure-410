#!/usr/bin/env python3
"""Check source requirements before builds; full Palomar verification is still required.

Scanner functions follow PalomarSubmission/scripts/source_requirements.py.
"""
import os
import re
import sys
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
# Lean 4 Init/Meta/Defs.lean identifier characters; Python Unicode classes
# are broader. A qualified identifier also continues across a dot.
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")


def has_module_header(text: str) -> bool:
    """Recognize the initial marker, without confusing comments with headers.

    Documentation comments are commands, not header whitespace. Do not strip a
    BOM or arbitrary Unicode whitespace: Lean's header parser does not either.
    This cheap check precedes installation; execute confirms with --deps-json.
    """
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            # Lean consumes the character after the plain opener before
            # scanning its body (unlike nested openers). Match its parser.
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    """LF/CRLF lines; an unterminated final line counts, a final LF adds none."""
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    """Lean source paths, including contained projects and symlinks to reject.

    Lake configuration shares the line cap, but is exempt from module headers.
    Never traverse symlinks or Git internals.
    """
    files = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


# The libraries this repository ships.  Besides the checks above (which already walk the whole
# tree), these roots are scanned for forbidden tokens and checked against the lakefile.
#
# The submission is a single Lake library, `Submission`, whose content lives under
# `Submission/CatalanCore` and `Submission/CatalanFrames`.  The top-level `CatalanCore`,
# `CatalanFrames` and `CatalanParity` libraries of the modular-architecture design FU are not
# part of this port: requiring them failed every run while asserting nothing about the content
# actually shipped (the token scan then matched no file at all, because `relative.parts[0]`
# was never one of those names).
NEW_ROOTS = ("Submission",)
# `sorry` in the new libraries is a warning while work packages are in flight (stubs
# may appear), fatal with `--strict` (cut-over / snapshots), and always fatal
# in the frozen contract file.  `native_decide` is always fatal.
SORRY_ALWAYS_FATAL = {"CatalanCore/Frame/Spec.lean"}
STRICT = "--strict" in sys.argv
FORBIDDEN_TOKENS = ("native_decide", "sorry")


def strip_comments_and_strings(text: str) -> str:
    """Remove nested block comments, line comments and string literals (newlines are kept)."""
    out = []
    index = 0
    depth = 0
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and text.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            out.append("\n" if text[index] == "\n" else " ")
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text[index] == '"':
            index += 1
            while index < len(text) and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            index += 1
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def check_lakefile(root: Path) -> bool:
    """New libraries must be declared and must not be default targets."""
    path = root / "lakefile.toml"
    if not path.is_file():
        return False
    text = path.read_text(encoding="utf-8")
    ok = True
    default = re.search(r"defaultTargets\s*=\s*\[(.*?)\]", text, re.S)
    defaults = re.findall(r'"([^"]+)"', default.group(1)) if default else []
    for name in NEW_ROOTS:
        if not re.search(rf'name\s*=\s*"{name}"', text):
            print(f"lakefile.toml: library {name} is not declared")
            ok = False
        if name in defaults:
            print(f"lakefile.toml: {name} must not be a default target")
            ok = False
    return ok


def check_new_tokens(relative: Path, text: str) -> bool:
    """Forbid native_decide and unlisted sorry in the new libraries."""
    if relative.parts[0] not in NEW_ROOTS:
        return True
    code = strip_comments_and_strings(text)
    ok = True
    for token in FORBIDDEN_TOKENS:
        if re.search(rf"\b{token}\b", code):
            if token == "sorry" and not STRICT and relative.as_posix() not in SORRY_ALWAYS_FATAL:
                print(f"{relative}: warning: contains `sorry` (fatal with --strict)")
                continue
            print(f"{relative}: contains forbidden `{token}`")
            ok = False
    return ok


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failed = not check_lakefile(root)
    for path in lean_source_files(root):
        relative = path.relative_to(root)
        if path.is_symlink():
            print(f"{relative}: must be a regular Lean file, not a symbolic link")
            failed = True
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            print(f"{relative}: source is not valid UTF-8")
            failed = True
            continue
        if path.name != "lakefile.lean" and not has_module_header(text):
            print(f"{relative}: must use the module header keyword")
            failed = True
        if not check_new_tokens(relative, text):
            failed = True
        if physical_lines(text) > 10_000:
            print(f"{relative}: exceeds 10,000 lines; split into smaller modules")
            failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
