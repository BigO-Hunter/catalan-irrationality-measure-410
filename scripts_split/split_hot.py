#!/usr/bin/env python3
"""Split giant Lean modules chronologically into Part files to cut per-module
elaboration memory peak. Declaration names/statements byte-identical; original
file becomes a public-import shim. Refuses files with unexpected mid-file
top-level commands or private declarations."""
import os, re, sys, math

REAL_RE = re.compile(
    r"^(?:def |theorem |lemma |abbrev |instance |protected def |protected theorem |"
    r"noncomputable def |@\[(?!expose\] public section\s*$)|structure |class |inductive |example )")
UNIT_RE = re.compile(
    r"^(?:" + REAL_RE.pattern[4:-1] +
    r"|set_option \S+ in\s*$|set_option .+ in\s*$|set_option \S+ \S+\s*$|"
    r"#print |#check|variable |/-!|/--)")
END_RE = re.compile(r"^end(\s|$)")
HEADER_OK_RE = re.compile(
    r"^(?:module\s*$|public import |import |@\[expose\] public section\s*$|"
    r"namespace |open |noncomputable section\s*$|section\s*$|section |-!|/--|public\s*$|"
    r"set_option |variable |deriving )")
TARGET_BYTES = 90_000

def doc_block_open(chunk_lines):
    """True if trailing lines end inside an unclosed /-! ... -/ doc block."""
    for l in reversed(chunk_lines):
        s = l.rstrip("\n")
        if s.count("-/") % 2 == 1:  # odd closer -> this line closes a block
            # walk further: find matching opener
            continue
    return False

def analyze(path):
    src = open(path).read()
    lines = src.splitlines(keepends=True)
    if not lines or not lines[0].startswith("module"):
        return None, "no module line"
    if re.search(r"^private ", src, re.M):
        return None, "has private decls"
    h = None
    for i, ln in enumerate(lines):
        if REAL_RE.match(ln):
            h = i
            break
    if h is None:
        return None, "no decls"
    header = lines[:h]
    in_doc = False
    for ln in header:
        if in_doc:
            if "-/" in ln:
                in_doc = False
            continue
        if ln.startswith(("/-!", "/--")):
            if "-/" not in ln:
                in_doc = True
            continue
        if ln.strip() and not HEADER_OK_RE.match(ln):
            return None, f"unexpected header line: {ln.strip()[:60]!r}"
    if not any(l.startswith(("import", "public import")) for l in header):
        return None, "no imports in header"
    starts = [i for i in range(h, len(lines)) if UNIT_RE.match(lines[i])]
    if len(starts) < 4:
        return None, f"only {len(starts)} decls"
    seen_end = False
    cycle_start = set()
    cycle_lines = set()
    i = h
    n = len(lines)
    while i < n:
        m = re.match(r"^end (\S+)\s*$", lines[i])
        if m:
            window = [lines[j].strip() for j in range(i, min(i + 7, n))]
            if "section" in window and \
               any(w == f"namespace {m.group(1)}" for w in window):
                cycle_start.add(i)
                for j in range(i, min(i + 7, n)):
                    if lines[j].strip() == f"namespace {m.group(1)}":
                        cycle_lines.update(range(i, j + 1))
                        break
        i += 1
    in_doc = False
    for i in range(h, len(lines)):
        ln = lines[i]
        if in_doc:
            if "-/" in ln:
                in_doc = False
            continue
        if ln.startswith(("/-!", "/--")) and "-/" not in ln:
            in_doc = True
            continue
        if i in cycle_lines:
            continue
        if END_RE.match(ln):
            seen_end = True
        elif UNIT_RE.match(ln):
            if seen_end:
                return None, f"decl after mid-file end at line {i+1}"
        elif re.match(r"^(section|namespace|noncomputable section|open)\b", ln):
            continue
        elif ln.lstrip() != ln:  # indented continuation line
            continue
        elif ln.strip():
            return None, f"mid-file command line {i+1}: {ln.strip()[:60]!r}"
    starts = sorted(set(starts) | set(cycle_start))
    # trailing tail of `end` lines closes header openings; every part needs it
    t = len(lines)
    while t > h and (not lines[t - 1].strip() or END_RE.match(lines[t - 1])):
        t -= 1
    tail = lines[t:]
    if not tail or not all(END_RE.match(l) or not l.strip() for l in tail):
        return None, "no end-tail"
    return (h, starts, tail), None

def split(path, dry=False):
    info, err = analyze(path)
    if err:
        return f"SKIP ({err})"
    h, starts, tail = info
    lines = open(path).read().splitlines(keepends=True)
    src_size = sum(len(l) for l in lines)
    nparts = max(2, math.ceil(src_size / TARGET_BYTES))
    tail_len = len(tail)
    body_end = len(lines) - tail_len
    # doc-block spans (for gluing docs to their decl)
    doc_spans = []
    i = 0
    while i < len(lines):
        if lines[i].startswith(("/-!", "/--")) and "-/" not in lines[i]:
            j = i
            while j < len(lines) and "-/" not in lines[j]:
                j += 1
            doc_spans.append((i, j))
            i = j + 1
        else:
            i += 1
    def in_doc_span(k):
        return any(s <= k <= e for s, e in doc_spans)
    # units at decl boundaries; pull preceding blank/doc lines into the unit
    bounds = starts[1:] + [body_end]
    units = []
    prev = starts[0]
    for b in bounds:
        cut = b
        while cut > prev and not lines[cut - 1].strip():
            cut -= 1
        while cut > prev and in_doc_span(cut - 1):
            cut = min(s for s, e in doc_spans if s <= cut - 1 <= e)
            while cut > prev and not lines[cut - 1].strip():
                cut -= 1
        units.append((prev, cut))
        prev = cut
    # merge doc-only/blank units into their successor
    merged = []
    pending_start = None
    for a, b in units:
        text = "".join(lines[a:b])
        is_doc_only = not REAL_RE.match(lines[a]) and not text.strip(" \r\n").startswith(("set_option",)) and all(
            (not l.strip()) or l.startswith(("/-!", "/--")) or "-/" in l for l in lines[a:b])
        if is_doc_only:
            if pending_start is None:
                pending_start = a
            continue
        if pending_start is not None:
            a = pending_start
            pending_start = None
        merged.append((a, b))
    if pending_start is not None:  # trailing docs before tail; fold into last real unit
        a, b = merged[-1]
        merged[-1] = (pending_start, b)
    units = merged
    assert units
    assert prev == body_end
    sizes = [sum(len(x) for x in lines[a:b]) for a, b in units]
    total = sum(sizes)
    per = total / nparts
    part_of_unit = []
    acc = 0
    p = 0
    for s in sizes:
        part_of_unit.append(p)
        acc += s
        if acc >= per * (p + 1) and p < nparts - 1:
            p += 1
    modname = path[:-5].replace("/", ".")
    assert modname.startswith("Submission."), modname
    last_imp = max(i for i, l in enumerate(lines[:h]) if l.startswith(("import", "public import")))
    head_imports = lines[:last_imp + 1]
    head_rest = lines[last_imp + 1:h]
    groups = {}
    for i, pp in enumerate(part_of_unit):
        groups.setdefault(pp, []).append(units[i])
    nparts = len(groups)
    if not dry:
        moddir = os.path.join(os.path.dirname(path), os.path.basename(path)[:-5])
        os.makedirs(moddir, exist_ok=True)
        for k, (pp, us) in enumerate(sorted(groups.items())):
            body = "".join("".join(lines[a:b]) for a, b in us)
            imp = f"public import {modname}.P{k}\n" if k > 0 else ""
            content = "".join(head_imports) + imp + "".join(head_rest) + body + "".join(tail)
            with open(os.path.join(moddir, f"P{k+1}.lean"), "w") as f:
                f.write(content)
        shim = "module\n" + "".join(f"public import {modname}.P{k+1}\n" for k in range(nparts))
        with open(path, "w") as f:
            f.write(shim)
    return f"SPLIT {nparts} parts ({src_size} B, {len(units)} decls)"

def main():
    args = sys.argv[1:]
    apply = "--apply" in args
    for f in sys.stdin.read().split():
        print(f, split(f, dry=not apply))

if __name__ == "__main__":
    main()
