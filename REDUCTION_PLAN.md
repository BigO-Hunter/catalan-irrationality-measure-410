# CATALAN-410 — Work-Reduction Plan (post-#182, measured)

Repo: this tree @ `063d100f` (branch `oom-memory-split`). Verifier run 42525033842 ("#182"):
build ladder OOM at widths 4/3/2 (14 GiB cgroup cap), width-1 timed out at 4,722/6,147
(2h08m), verify (width 1) reached 5,109/6,147 in 18,881.7 s. Pre-registered rule fires:
**~35% less work in Cells.Q1/Q2 — NOT more sharding.** This plan is the measured basis for
that reduction. Proof content untouched by this document.

## 1. Kill mechanism — local repro (this machine, 1 s RSS sampler, kill-region rebuild)

| module (catalan-fix) | peak RSS | wall (local 2-lane / verifier) |
|---|---|---|
| Cells.Q1.SmP000 | **3.24 GiB** | ~123 s (verifier) |
| Cells.Q1.FrB040 | 2.42 GiB | 18 s local |
| Cells.Q1.FrB043 | 2.25 GiB | 24 s local |
| Cells.Q1.FrB044 | 2.19 GiB | 16 s local |
| Cells.Q1.FrB042 | 2.17 GiB | 12 s local |
| Cells.Q1.FrB041 | 2.14 GiB | 13 s local |
| Consts.SpikeS0.P4 | 1.78 GiB | 116 s / 167 s |
| Consts.SpikeS1.P4 | 1.79 GiB | 117 s / 172 s |
| Consts.SpikeS2.P4 | 1.77 GiB | 116 s / 168 s |

- 2 independent `lake build` workers (the verifier's width semantics — its log spawns
  "N Lake workers" as separate lake processes): peak concurrent lean RSS sum in the
  kill region = **8.29 GiB** (under cap).
- Uncontrolled lake (all 9 region jobs at once — note `lake -KmaxJobs=2` did **not**
  limit build-job concurrency on lake 5.0.0/4.34.1): peak sum **17.23 GiB** — over the
  14 GiB cap. OOM mechanism demonstrated: multi-job scheduling over this region crosses
  the cap.
- Verifier width-2 died at 14.0 GiB with an in-region anon pair ≤ ~5.7 GiB: the gap is
  accumulated page cache (width-1 run alone peaked 9.7 GiB) + harness. Fewer and lighter
  modules is the correct lever; confirms the pre-registered rule.

## 2. Work accounting

- 6,147 jobs ≈ fresh source modules + cached replay; 1,043 source modules unmeasured ≈
  the 1,038 remaining jobs.
- Measured family averages (verifier logs, 1,701 modules): Cells.Q0 45.2 s × 234,
  Q1 48.3 s × 274, Q2 50.5 s × 241, Consts.SpikeS* ~254 s × 4/quarter, Uniform 2.3 s,
  D58 17.3 s, OAI.Catalan 5.2 s.
- Remaining tail composition: Uniform 413, D58 84, OAI 70, Q0 93, Q1 114, Q2 127, other
  142. **Family-weighted tail ≈ 20.7 k s (≈ 5.7 h single-stream)**; the receipt's 50.4 k s
  used the 48.5 s tail average on all 1,038 (413 of which are ~2 s Uniform modules).
  Cells = ~76% of the remaining work.
- Full-quarter projections: Q1 ≈ 20.4 k s, Q2 ≈ 20.6 k s. **35% of Q1+Q2 ≈ 14.3 k s** —
  the reduction target.
- Verify's last fresh module was Cells.Q2.SmP001.P2: the tail contains the unmeasured
  EvalRefE0/E1/E2/X01/X12 shards (40–59 KB sources — the old 13.75 GiB monolith class)
  and SpikeS*.P4 (~254 s × 12). These must be peak-measured before any resubmission.

## 3. Structure findings (census + pilots — includes one dead end, ruled out by measurement)

- Cells.Q1+Q2 carry 20,066 `decide +kernel` theorems. Heaviest modules (SnP015/018/019/023/
  026, SpmR*GB000, SpiB002) each have ~171 decides.
- **Dead end (do not revisit):** 68% of item theorems carry a `plogs.getD K (([], 0))`
  literal, which looked like trivial empty-data checks. Measured false: `q1snPlogs` has
  exactly 38 real entries (indices 0..37 all real), and a pilot decide of the dm-clauses
  under `t.2 = 0` assumptions FAILS — items are genuine data checks. No trivial-item
  windfall exists.
- **Twins are structural only:** Q0/Q1/Q2 plogs/poles have identical entry shapes and
  lengths, but numerically distinct content (no sign-flip or scale relation found in
  SnFq data). Cross-quarter certificate sharing requires a real algebraic relation —
  parked unless the math says otherwise.
- ~29% of `List ℚ` defs are byte-identical within their file (Q1: 4,317/14,805) — a
  serialization/elaboration redundancy only (kernel re-evaluates per use; dedup does not
  save decide time).
- Data-only H1 modules (pure `def`s, no decides) measure 11–148 s each (avg 48.6 s over
  8) — elaboration + IR + olean serialization of giant data defs is a real, attackable
  cost component.
- Clause pilots (B0–B4, scratch, deleted): import overhead for a SnP000-sized module is
  ~12.35 s locally; individual plog-item clauses decide in ≪ 1 s. Module cost
  concentrates in import loading, item volume (77 in SnP000), and per-cell `cellW`
  decides over ~200-digit rationals.

## 4. Reduction candidates (ranked)

**A. Normalized data references (the likely 35%+ lever; proof-engineering, statements
unchanged).** Each item decide currently evaluates `plogs.getD K` by unfolding
`qlistC (raw_ints% …)` def bodies — repeated across every block of every module of the
same field family (the same 38-entry table re-evaluated per (module × block)). Plan:
per field family, prove once `q1snFq.plogs = q1snPlogsNorm` where `q1snPlogsNorm` is the
fully normalized constructor-literal table (one `rfl`-decide per table), then the
generator emits item theorems against `q1snPlogsNorm` entries (constructor spine walk
instead of def-body eval). Final `BlockFacts` interfaces and statements unchanged —
063d100f reproducibility intact (new commit on top). Estimated 2–4× on item decides.
**Pilot first:** one SnP000 variant, measure end-to-end vs 063d100f baseline
(SmP000-region: 123 s verifier / ~40–60 s local).

**B. Duplicate-def dedup (mechanical, safe, additive with A).** 4,317 identical `List ℚ`
defs in Q1 (similar in Q0/Q2) → one shared def + aliases. Saves elaboration/IR/olean
bytes on data modules (H1-class: avg 48.6 s × ~100+ data modules). Est. 10–20% of
data-module time. No statement changes.

**C. Measure the tail heavyweights before resubmission (blocking check).** EvalRefE0/E1/
E2/X01/X12 shards are unmeasured. If any single shard peaks > 6 GiB, width-2 can never
hold a pair — those modules need the EvalRef-style decomposition regardless of A/B.
Measure with the same sampler before any submit.

**D. Symmetry transport (research, parked).** Only if a real Q0↔Q1↔Q2 relation exists.

**E. More sharding — pre-registered as forbidden.** The cone grew +17 jobs from the last
split and each split adds lake overhead without cutting kernel work.

## 5. Execution order (next session)

1. Pilot A on SnP000 (scratch copy first, then generator change if ≥ 35%).
2. Sweep B across Q0/Q1/Q2 (mechanical).
3. Peak-measure EvalRef shards (C) — blocking gate for resubmission.
4. Local 2-worker full-Cells rebuild; confirm tail fits the offered window; resubmit.

## 6. Environmental note (this host, not the port)

`lean` builds of SmP000 were repeatedly SIGTERM'd ~5–13 s in during this session's
measurements (P4/FrB04x builds ran to completion unaffected; background shells were also
reaped ~4 min in). Peak data for SmP000 above comes from the sampler window before the
kill. Unresolved host-side hazard — worth a look before the next long local build.
