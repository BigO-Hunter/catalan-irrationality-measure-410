# Catalan μ(G) ≤ 410 — verifier OOM investigation (2026-11-05)

## Verifier constraint (from /tmp/bos157/receipt.json)
- cgroup memory cap: 15,032,385,536 B = 14 GiB; swap 0; tasks_limit 4096
- job 1 (build): OOM-kill, peak cgroup = exactly the cap, peak tasks 1299, died at [4255/5858]
- job 2 (verify): OOM-kill, peak = cap, died at [4296/5858] in 5m06s (replaying job 1 artifacts)

## Measured single-module peaks (this machine, `/usr/bin/time -l lake env lean <file>`)
| module | wall | max RSS |
|---|---|---|
| GenD/Signed/Data/Consts/EvalRefE1 (30 lines) | 1066 s | **13.75 GB** |
| GenD/Signed/Data/Cells/Q2/SpiB007 (344 lines) | 1328 s | 3.31 GB |
| OAI/…/FixedModularPlusProductRows40To41 ORIGINAL | 159 s | 2.01 GB |
| … /P1 (split) | 9.9 s | 1.50 GB |
| … /P2 (split) | 169 s | 1.94 GB |

## Conclusion
- A single module (`EvalRefE1`, `by decide +kernel` over huge rational data) peaks at 13.75 GB
  — ~98% of the verifier's entire 14 GiB cgroup, before counting any co-scheduled module or
  page cache. Splitting this file cannot help: the peak is one atomic kernel decision.
- The 74-module split (this branch) reduces *some* 150–300 s modules only marginally
  (PlusRows40To41: 2.01 → 1.94 GB peak). It is not a sufficient fix.
- Therefore a resubmission at a new SHA would very likely OOM again, at EvalRefE1-class modules
  if not earlier. Do not resubmit without either (a) proof engineering on the decide +kernel
  monoliths, or (b) a maintainer-granted larger memory cap / re-dispatch.

## What this branch contains
- 71 modules split into part files + import shims (declaration sets verified identical),
  3 orphan-docstring repairs, ArcsineDenominator reverted to the original single file.
- Full `lake build Submission` green: BUILD_EXIT=0 (logs /private/tmp/catalan_oomfix_build{2,3,4}.log).

## Next step (recommended)
File a factual resource-outcome comment on bigospeedrun/verifier#157 citing the measured
13.75 GB single-module peak and ask the maintainer whether the sandbox cap can be raised,
or whether a submission of this size is expected to fit. Retry only after an answer, or
after EvalRefE1/E2/X12/LinkSlope are re-engineered to lower peak memory.
