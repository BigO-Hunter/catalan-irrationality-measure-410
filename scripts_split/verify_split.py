#!/usr/bin/env python3
"""Verify splits: each part must equal head_imports + [prev import] + head_rest + bodyk + tail
with bodies concatenating (in order) to the original body; shim lists all parts; decl-name
multiset preserved."""
import re, subprocess, sys

REAL_RE = re.compile(r"^(?:def |theorem |lemma |abbrev |instance |protected def |protected theorem |noncomputable def |@\[(?!expose\] public section\s*$)|structure |class |inductive |example )")
UNIT_RE = re.compile(REAL_RE.pattern[:-1] + r"|set_option |#print |#check |/-!|/--)")
END_RE = re.compile(r"^end(\s|$)")
NAME_RE = re.compile(r"^(?:\S+\s+)*?(?:def|theorem|lemma|abbrev|instance|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_.'\"]*)")

def names(text):
    return sorted(m.group(1) for ln in text.splitlines() if (m := NAME_RE.match(ln)))

def verify(path):
    orig = subprocess.run(["git", "show", f"HEAD:{path}"], capture_output=True, text=True).stdout
    lines = orig.splitlines(keepends=True)
    h = next(i for i, l in enumerate(lines) if REAL_RE.match(l))
    last_imp = max(i for i, l in enumerate(lines[:h]) if l.startswith(("import", "public import")))
    head_imports = "".join(lines[:last_imp + 1])
    head_rest = "".join(lines[last_imp + 1:h])
    t = len(lines)
    while t > h and (not lines[t - 1].strip() or END_RE.match(lines[t - 1])):
        t -= 1
    tail = "".join(lines[t:])
    modname = path[:-5].replace("/", ".")
    shim = open(path).read()
    mods = [l.strip() for l in shim.replace("public import ", "").splitlines()[1:] if l.strip()]
    if shim != "module\n" + "".join(f"public import {m}\n" for m in mods):
        return f"FAIL {path}: shim malformed"
    expect = [f"{modname}.P{k+1}" for k in range(len(mods))]
    if mods != expect:
        return f"FAIL {path}: shim imports wrong"
    bodies = []
    d = path[:-5].rsplit("/", 1)
    d = d[0] if len(d) > 1 else ""
    base = path.rsplit("/", 1)[-1][:-5]
    for k, m in enumerate(mods):
        pfile = (f"{d}/{base}/P{k+1}.lean" if d else f"{base}/P{k+1}.lean")
        plines = open(pfile).read().splitlines(keepends=True)
        imp = f"public import {modname}.P{k}\n" if k > 0 else ""
        prefix = head_imports + imp + head_rest
        pl = "".join(plines)
        if not pl.startswith(prefix):
            return f"FAIL {pfile}: prefix mismatch"
        tt = len(plines)
        while tt > 0 and (not plines[tt - 1].strip() or END_RE.match(plines[tt - 1])):
            tt -= 1
        body = "".join(plines[len(prefix.splitlines(keepends=True)):tt])
        bodies.append(body)
    rec = head_imports + head_rest + "".join(bodies) + tail
    if rec != orig:
        for i, (a, b) in enumerate(zip(rec, orig)):
            if a != b:
                return f"FAIL {path}: differs at char {i}: ...{rec[max(0,i-60):i+20]!r} vs ...{orig[max(0,i-60):i+20]!r}"
        return f"FAIL {path}: length {len(rec)} vs {len(orig)}"
    n_orig, n_parts = names(orig), names("".join(bodies))
    if n_orig != n_parts:
        s1, s2 = set(n_orig), set(n_parts)
        return f"FAIL {path}: decls differ; only-orig={sorted(s1-s2)[:5]} only-parts={sorted(s2-s1)[:5]}"
    return None

bad = 0
for p in sys.stdin.read().split():
    r = verify(p)
    if r:
        print(r)
        bad += 1
print("ALL OK" if not bad else f"{bad} FAILURES")
sys.exit(1 if bad else 0)
