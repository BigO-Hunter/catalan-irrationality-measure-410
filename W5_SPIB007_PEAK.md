# W5 — `GenD/Signed/Data/Cells/Q2/SpiB007` peak-RSS attribution

Repo: `catalan-irrationality-measure-410` @ `bfa20018e0bd470805dac30a1916beefe586daa5`,
branch `chunk/W5`. Measured on the campaign host (M4 Max, 128 GB, saturated: load
100-160, swap 7.2/8 GB; `LEAN_NUM_THREADS=1`, one Lean process of mine at a time).
Method is W8's: `/usr/bin/time -l lake env lean <file>`; peak = "maximum resident set size".

## 1. Classification (what the file is, and what dominates)

122 KB, 344 lines, already finely decomposed into per-cell and per-index `decide +kernel`
checks (16 cells x ~11 decls, 38 `plogItemOK` checks). It is **not** a data-term file:
the largest literal is 6.9 KB (`q2spiB018CbP`, `q2spiB018Cr`). The peak is
**decision steps**, not data terms.

Per-declaration peak, imports + all `def`s kept, one theorem per probe
(`gen_probe.py`; peaks include the ~1.52 GB import floor):

| probe | wall | peak |
|---|---|---|
| imports only (`SpiFq` + `PolySplit`) | 7 s | **1516 MB** ← floor for any decl |
| `q2spiB018Pl0` (`plogItemOK`) | 6 s | 1540 MB |
| `q2spiB018CrOK` (`absLeL` over 401 coeffs) | 8 s | 1788 MB |
| `q2spiB018PolyX` (`shiftLKs` 49x401) | 8 s | 1771 MB |
| `q2spiB018LBlock` (`lBlockOK`) | 11 s | 1951 MB |
| `q2spiB018Rest` (`blockRestOK`) | 18 s | 2419 MB |
| **`q2spiB018C0` (`lcellW`)** | **39 s** | **4011 MB** ← the driver |

`lcellW` is the driver. Decomposing one cell's `lcellW` into its 12 conjuncts
(`unfold lcellW; simp only [Bool.and_eq_true, decide_eq_true_eq]; refine <12 holes>`,
the same normal form `lcellW_sound` uses) and measuring each hole alone:

| part | what it is | wall | peak | over floor |
|---|---|---|---|---|
| p3 | `logsCheck` | 15 s | 1590 MB | +74 |
| p4 | `llogsCheck` | 15 s | 1554 MB | +38 |
| p5 | `poleSumI` match (builds both 401-vectors) | 10 s | 2048 MB | +532 |
| p8 | `poles.all (isFar ∨ fpPoleOK)` | 15 s | 1630 MB | +114 |
| **p11** | **`coefTestR … (vecAdd …) (vecAdd …)`** | **45 s** | **3589 MB** | **+2073** |
| p12 | `tmUBQ … ≤ T` | 15 s | ~1519 MB | ~0 |

**p11 alone is 2073 MB of the 2495 MB that the `lcellW` monolith adds over the import
floor.** Everything else in the conjunction is noise by comparison.

## 2. What was tried, and what it measured

1. **Conjunction split of all 16 `lcellW` monoliths** (`split_lcellw.py`: statement
   bytes untouched, `:= by decide +kernel` replaced by the 12-hole `refine` + a tiny
   glue term, `set_option maxHeartbeats 0 in` because 12 separate kernel checks exceed
   the default 200k tactic heartbeats where 1 check did not).
   Single-cell result: **4011 → 3942 MB (-1.7 %)**, 39 s → 29 s. The split is correct
   and it does isolate the parts, but it cannot go below the largest part.
2. **Naming the two vector arguments as top-level `def`s** (so the kernel could stream
   them instead of rebuilding them inside `coefTestR`): **3991 MB — no help**. Kernel
   reduction shares nothing between reductions; the value is rebuilt.
3. **Splitting `coefTestR` itself** is the only remaining lever, and it needs a new
   lemma that does not exist in the tree: `absLeELQ` recurses over `Bl`
   (`Core.lean:2633`), so blocks require
   `absLeELQ (ts1++ts2) (es1++es2) (bs1++bs2) = (absLeELQ ts1 es1 bs1 && absLeELQ ts2 es2 bs2)`
   plus equal-length side conditions, then `(cs.drop 3).take k` / `.drop k` splits.
   Not landed here (host-pressure directive + time); it is the concrete next step.

## 3. Verdict

- The file's floor is **1516 MB of imports**, so "well under 2 GB" cannot be reached
  for this module by any proof restructuring; the realistic target is
  **1516 + largest surviving part**.
- The honour of being the peak belongs to **`coefTestR`'s `absLeELQ` walk over 401
  rational coefficients** (p11, 3589 MB), not to a data term and not to the
  conjunction. Splitting declarations is necessary but not sufficient: the same
  decl keeps the peak.
