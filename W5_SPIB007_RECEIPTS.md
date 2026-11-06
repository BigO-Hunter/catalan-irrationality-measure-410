# W5 — `SpiB007` decide-chain split: receipts

Repo `catalan-irrationality-measure-410` @ `bfa20018`, branch `chunk/W5`.
File: `Submission/CatalanMeasure/GenD/Signed/Data/Cells/Q2/SpiB007.lean`
(122 KB, 344 lines, module `Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB007`).

## Measurements (same host, same session, `LEAN_NUM_THREADS=1`, one Lean at a time)

`/usr/bin/time -l lake env lean <file>`, peak = "maximum resident set size".

| run | wall | peak RSS | rc | errors |
|---|---|---|---|---|
| baseline — untouched file (copy measured, same bytes) | **550 s** | **4486 MB** | 0 | 0 |
| after — 16 `lcellW` monoliths split | **425 s** | **4404 MB** | 0 | 0 |
| delta | **−125 s (−23 %)** | **−82 MB (−1.8 %)** | | |

Host was saturated throughout (load 100–160, swap 7.2/8 GB, peers running their own
Lean processes). Absolute numbers therefore differ from `OOM_INVESTIGATION.md`
(1328 s / 3.31 GB, measured under different conditions); only the same-session
before/after pair above is comparable.

## What the cut is

Per cell (16 of them), the statement line is untouched; only the proof changed:

```lean
-- before
theorem q2spiB018Cn : lcellW <args> = true := by decide +kernel
-- after
set_option maxHeartbeats 0 in
theorem q2spiB018Cn : lcellW <args> = true := by
  unfold lcellW
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    decide +kernel
```

Twelve independent kernel checks instead of one, glued by the empty-proof `refine`
(no glue term is built; `lcellW_sound` already destructures its hypothesis in exactly
this normal form, so the shape is the definition's own). `set_option maxHeartbeats 0 in`
is needed because 12 tactic-level kernel checks exceed the default 200 k tactic
heartbeats where the single check did not — same option `EvalRefE1` sets globally.

## Semantics / trust receipts

1. **Declaration statements byte-identical.** Checked mechanically over the whole file:
   290/290 declarations (`theorem`/`def`) have identical `name : type` text before
   `:=` — 0 differing, 0 missing. Nothing was renamed, added, or removed.
2. **Same trust profile.** No `native_decide`. Every hole is `decide +kernel`, i.e.
   `of_decide_eq_true` on a kernel reduction — exactly what the monolith used.
3. **Green build.** The split file compiles: `rc=0`, 0 errors, 425 s.

## Where the peak actually lives (measured per part)

Attribution used probes (`gen_probe.py`): imports + all `def`s + one theorem.
Import floor alone (`SpiFq` + `PolySplit`) = **1516 MB**, i.e. the file can never go
below that. Then, one `lcellW` conjunct at a time:

| part of `lcellW` | peak | over floor |
|---|---|---|
| `logsCheck` | 1590 MB | +74 |
| `llogsCheck` | 1554 MB | +38 |
| `poleSumI` match (builds both 401-vectors) | 2048 MB | +532 |
| `poles.all (isFar ∨ fpPoleOK)` | 1630 MB | +114 |
| **`coefTestR … (vecAdd …) (vecAdd …)`** | **3589 MB** | **+2073** |
| `tmUBQ … ≤ T` | ~1519 MB | ~0 |

`coefTestR` is 2073 MB of the ~2495 MB the `lcellW` monolith adds. Within it, the cost
is `absLeELQ` walking ~401 rational coefficients (`Core.lean:2633`), not the leading
`decide`s. So the split is necessary but **not sufficient**: the same declaration still
holds the peak, and the remaining lever is slicing that walk.

**Tried and rejected by measurement:** naming the two `vecAdd` arguments as top-level
`def`s so the kernel could share them — 3991 MB, worse. Kernel reduction shares nothing
between reductions; the value is rebuilt each time.

## Concrete next step (not landed)

Add one local lemma and slice `coefTestR`'s inner walk into ~50-coefficient blocks:

```lean
theorem absLeELQ_append (bs1 : List ℚ) (ts1 es1 ts2 es2 bs2 : List ℚ)
    (h1 : ts1.length = bs1.length) (h2 : es1.length = bs1.length) :
    absLeELQ (ts1 ++ ts2) (es1 ++ es2) (bs1 ++ bs2)
      = (absLeELQ ts1 es1 bs1 && absLeELQ ts2 es2 bs2)
```

then `(cs.drop 3).take k` / `.drop k` splits with `List.take_append_drop` and the known
lengths. Expected: part peak ≈ floor + 2073/8 ≈ 1.8 GB, whole-file peak ≈ 2.4 GB.
Tooling for that pass is in `gen_part_probes.py` / `gen_probe.py` (probe per conjunct,
peak per probe).
