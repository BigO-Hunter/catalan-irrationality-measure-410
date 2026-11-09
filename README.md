# Irrationality measures for Catalan's constant and differences of trigamma values

A Lean 4 formalization of sixteen irrationality measures. Let `G = ∑_{j ≥ 0} (−1)^j / (2j+1)^2` be
Catalan's constant, `L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)^2 − 1/(3k+2)^2)` and `ψ′(x) = ∑_{n ≥ 0} 1/(n+x)^2`
the trigamma function, so that `ψ′(1) = ζ(2) = π²/6`. The irrationality exponent `μ(ξ)` of a real number
`ξ` is the infimum of the `μ` such that `|ξ − p/q| > q^(−μ)` for all integers `p` and all sufficiently
large integers `q`.

> **Theorem.**
>
> - μ(G) ≤ 410;
> - μ(G ± 5π²/48) ≤ 31.2876, for both signs;
> - μ(L(2, χ₋₃)) ≤ 13.7046;
> - μ(L(2, χ₋₃) ± π²/9) ≤ 9.4998, for both signs;
> - μ(ψ′(a/5) − π²/6) ≤ 23.8272 for a = 1, 2, 3, 4;
> - μ(ψ′(a/7) − π²/6) ≤ 2207.8697 for a = 1, …, 6;
> - μ(π²) ≤ 6.5253 (weaker than the known bounds, included for completeness).

Each Lean statement has the same form. For a number `x` with exponent `μ` above, it is `|x − a/b| > b^(−μ)`
for every integer `a` and every sufficiently large integer `b`.

All proofs are kernel-checked in Lean and use only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Papers

- S. Litsey, *An irrationality measure for Catalan's constant* (2026), the proof of μ(G) ≤ 410: LaTeX
  source and PDF in [`paper/`](paper/) (`catalan-measure-hexagon.tex` is the single-file version),
  Hexagon preprint [`hexagon:2610.00187`](https://hexagonmath.org/2610.00187).
- S. Litsey, *Irrationality measures for differences of trigamma values* (2026), the other fifteen
  measures: LaTeX source and PDF in [`paper-trigamma/`](paper-trigamma/) (`trigamma-irrationality-hexagon.tex`
  is the single-file version), Hexagon preprint [`hexagon:2610.00401`](https://hexagonmath.org/2610.00401).

Both papers build on OpenAI's proof that `G` is irrational ([openai/math](https://github.com/openai/math);
preprint dated September 24, 2026, released October 6, 2026), and the proof of μ(G) ≤ 410 also builds on
its Lean formalization. Other bounds in the literature:
- For `G`, R. K. Jha proved μ(G) ≤ 10^8 ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).
  M. C. S. Carreira treated the five parameters of OpenAI's construction as free and obtained μ(G) < 2294
  ([doi:10.5281/zenodo.23532239](https://doi.org/10.5281/zenodo.23532239)); H. S. Bojnal instantiated his
  general theorem at the design (36, 6, 2, 3, 2) to obtain μ(G) < 2401.74
  ([proof-factory/catalan-exponent](https://github.com/proof-factory/catalan-exponent)). R. Xu reported
  μ(G) ≤ 727.03 for the design (20, 3, 1, 2, 1), with a numerical certificate in ball arithmetic that is
  not formalized ([issue #5](https://github.com/slitsey/catalan-irrationality-measure/issues/5)).
  C. Davis obtained μ(G) ≤ 528.23288 with the design and arithmetic of this repository and new quadrature
  nodes, formalized in Lean ([1337isnot1337/catalan-constant](https://github.com/1337isnot1337/catalan-constant));
  D. I. Arkhipov modified that development to μ(G) ≤ 528.2327
  ([darkhipo/catalan-constant-gen5](https://github.com/darkhipo/catalan-constant-gen5)).
- For `L(2, χ₋₃)` and its rational linear combinations with `ζ(2)`, Calegari, Dimitrov and Tang give
  24781 (arXiv:2510.04156, Theorem 5.1 and the remark after it).
- We know of no earlier irrationality result for `G ± 5π²/48`, `ψ′(a/5) − ζ(2)` or `ψ′(a/7) − ζ(2)`.

## What to read

| File | Content |
|---|---|
| [`Challenge.lean`](Challenge.lean), [`ChallengeHybrid.lean`](ChallengeHybrid.lean) | the sixteen statements, using Mathlib only, with the constants written as series: μ(G) ≤ 410 in `Challenge.lean` (namespace `CatalanIrrationalityMeasure`) and the other fifteen in `ChallengeHybrid.lean` (namespace `TrigammaDifferences`). This is the whole trusted statement surface |
| [`Solution.lean`](Solution.lean), [`SolutionHybrid.lean`](SolutionHybrid.lean) | their proofs, each file ending with `#print axioms` for its theorems |
| [`comparator.json`](comparator.json), [`comparator-hybrid.json`](comparator-hybrid.json) | configurations for `lake comparator`, stating that each `Solution` file proves exactly the statements of its `Challenge` file with the three permitted axioms. The `comparator` job of the CI workflow [`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) on `comparator.json`, with Lean's kernel and the NanoDa and con-ron kernels bundled with the toolchain; the manually dispatched workflow [`comparator-timing.yml`](.github/workflows/comparator-timing.yml) times the same check with each external kernel separately. `comparator-hybrid.json` is not run in CI |
| [`CatalanMeasure/GenD/`](CatalanMeasure/GenD/) | the proof of μ(G) ≤ 410 |
| [`CatalanCore/Uniform/`](CatalanCore/Uniform/) | the proofs for the differences of trigamma values |
| [`formalization.yaml`](formalization.yaml), [`formalization-hybrid.yaml`](formalization-hybrid.yaml) | provenance, authorship, automation and scope |

## Catalan's constant: μ(G) ≤ 410

OpenAI's proof compares, for a determinant whose entries are linear forms in `1` and `G`, a lower bound
coming from its denominators with an upper bound coming from an integral representation. The construction
depends on five integer parameters `(n₀, b₀, q₀, g₀, h₀)`, a *design*, and every argument here is carried
out for an arbitrary design. The design used is `(58, 9, 3, 5, 3)`: the determinant has size `58N`, and as
a polynomial in the constant it has degree at most `53N`.

- **Rank of the reduction modulo p.** At a prime `p` the denominator of the determinant is smaller by the
  dimension of the kernel of the reduction modulo `p` of the matrix of rational parts. Four closed
  formulas, proved for every design with antisymmetric row combinations, a reflection of Chebyshev
  polynomials modulo `p` and Frobenius relations, bound this dimension for `12N < p ≤ 26N`. Below `12N`
  further kernel vectors come from a single counting inequality for the nullity. On 34 windows of primes
  between `3N` and `16.2N` it is applied to fixed rational subspaces whose ranks are certified by stored
  integer kernel vectors. Together they give a piecewise linear profile with 102 pieces whose area, at
  least `22.05325` in units of `N²`, is the gain in the denominators.
- **A signed bound at the real place.** OpenAI's integrand contains the determinant of the row functions,
  which the energy method bounds only crudely. A Pick matrix argument and a Schur complement reduce it to
  the block of the negative nodes. Heine's formula writes that block as a ratio of two log-gas integrals,
  bounded above by completing squares in Chebyshev moments and below by Jensen's inequality. An energy
  inequality for signed measures keeps the bound concave. The bound holds on every configuration whose
  energy is near the maximum, and OpenAI's bound suffices on the others. It adds `8.29824` in units of
  `N²` to the decay rate.
- **The neighbourhood of G.** A Gauss quadrature formula with `53N` nodes extends the bound to
  `|x − G| ≤ e^(−ρN)` with `ρ = 296.586…`. The cost is paid column by column: a binomial bound for
  generalized Vandermonde determinants and a contour bound for the weight of each column peak at
  different columns.
- **Criterion.** For large `N` the integer polynomials obtained by clearing denominators are at most
  `e^(−ηN²)` on that neighbourhood, with `η = 38.33924`. A criterion with a free lower end of the window
  of primes, which uses the largest prime of the window whose square does not divide `b`, gives
  `|G − a/b| > b^(−410)`. Its last condition reads `410 > dρ/(η − 4dδ) = 409.99999…` with `d = 53` and
  `δ = 2.9·10⁻⁷`. The prime number theorem enters through the denominators and the choice of the prime.

The energy estimates use trial sequences whose generating functions are logarithmic potentials of point
charges near the edges of the support of the extremal measure. They are checked on covers by cells with
an exact local Taylor expansion, as kernel-checked rational inequalities.

In Lean, `CatalanMeasure/GenD/` is the design-generic layer: the denominators, the closed formulas
(`t_rank`, `u_rank`, `u6_rank_closed`, `s_rank`), the nonvanishing, the real place (`Analytic/`, `Cert/`)
and the criterion, assembled by `CatalanMeasure.GenD.measure_of_design` from a `DesignData` record.
`GenD/Uniform/W/` contains the counting inequality (`w_core`), its form for fixed rational subspaces
(`Charts3.host_count`) and the decision procedure for the window conditions (`Charts6.Check.checkHost`,
with soundness `physHost_of_checks`). `GenD/Uniform/Bank532/` holds the profile `wins532` of the 102
intervals and the bound `gain532_ge` for its area. `GenD/D58/` instantiates the design. `GenD/Signed/`
holds the signed bound (`PickDet`, `LemmaT`, `RatioIdentity`, `ReflectionEnergy`, the `Spike*` modules),
the column costs (`BinomVandermonde`, `Keyhole`), the cell certificates (`Data/Cells/`) and the assembly
(`Theorem410`). The generic valuation theorems of the construction are in `CatalanMeasure/Parametric/`.
The theorem is `CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410` in
[`CellsAll.lean`](CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.lean).

## Differences of trigamma values

For `0 < s < t ≤ 1` put `Ψ(s, t) = ψ′(s) − ψ′(t)`. The other fifteen numbers are, up to rational affine
maps (which do not change `μ`), values of `Ψ`:

```text
Ψ(1/4, 1) = 8 (G + 5π²/48),              Ψ(3/4, 1) = −8 (G − 5π²/48),
Ψ(1/3, 1) = (9/2) (L(2, χ₋₃) + π²/9),    Ψ(2/3, 1) = −(9/2) (L(2, χ₋₃) − π²/9),
Ψ(1/3, 2/3) = 9 L(2, χ₋₃),               Ψ(a/q, 1) = ψ′(a/q) − ζ(2).
```

The approximations are determinants of rectangular Löwner matrices of a digamma difference
`ψ(z+1) − ψ(z+s)` (for `L(2, χ₋₃)`, a combination of three digamma functions) at integer nodes: a common
block of `r` nodes, which carries the variable, and an interleaved border of about `cr/2` row nodes and
`cr/2` column nodes, where `c` is the only parameter of the geometry. Three estimates are proved once, for
every shift.

- **Content.** As in the arithmetic method of Rhin and Viola, the `p`-adic valuation of the common
  denominator is bounded prime by prime, by a finite list of local bounds: assignment problems with
  explicit potentials, the rank of the reduction modulo `p` of a rescaled matrix, and windows of the
  border free of poles, where the reduction is translation invariant (for the small primes, which meet
  the border several times, the windows are read modulo `p`). Each is an explicit integer expression in
  the scale, the border, the prime and the first poles of the frame modulo `p`. One theorem turns a
  finite table of affine pieces, checked by comparisons of rational numbers, into the bound
  `(Λ + o(1)) r²` for the logarithm of the denominator, using the prime number theorem in arithmetic
  progressions; the same table serves every shift with the same denominator `q`.
- **Nonvanishing.** By Hermite interpolation in characteristic zero, after deleting a bounded number of
  common nodes (at most 64), some member of the family is nonzero at any given rational point. No prime
  is involved.
- **Decay.** Andréief's identity for the row and column nodes, with Cauchy determinants, reduces the size
  of the determinant to a discrete logarithmic energy. A lower bound for this energy comes from a
  comparison measure on finitely many segments, through the conditional positive definiteness of the
  logarithmic kernel, and is verified on a finite cover by cells in exact rational arithmetic. The result
  is `|P(x)| ≤ e^(−(D − o(1)) r²)` for `|x − ξ| ≤ e^(−γr)`.

Together they give `μ ≤ γ/(D − Λ)`:

| number | (s, t) | c | Λ | D | γ | γ/(D − Λ) | B |
|---|---|---|---|---|---|---|---|
| G ± 5π²/48 | (1/4, 1), (3/4, 1) | 1/5 | 3.5149036 | 3.7447213 | 7.1904273 | 31.28751 | 31.2876 |
| L(2, χ₋₃) | (1/3, 2/3) | 1/2 | 4.0959278 | 4.6435117 | 7.5043742 | 13.70452 | 13.7046 |
| L(2, χ₋₃) ± π²/9 | (1/3, 1), (2/3, 1) | 3/10 | 3.3104458 | 4.0291249 | 6.8272548 | 9.499725 | 9.4998 |
| ψ′(a/5) − π²/6 | (a/5, 1) | 2/9 | 3.5128488 | 3.8135797 | 7.1655663 | 23.82717 | 23.8272 |
| ψ′(a/7) − π²/6 | (a/7, 1) | 1/6 | 3.6391158643 | 3.6424792669 | 7.4259546075 | 2207.870 | 2207.8697 |
| π² | (1/2, 1) | 3/10 | 2.9923824 | 3.9785713 | 6.4350874 | 6.525207 | 6.5253 |

Here `Λ` is the content constant, `D` the decay constant and `γ` the window constant. They are the
rational numbers of the formal proof, rounded outward (`Λ` and `γ` up, `D` down); the column
`γ/(D − Λ)` is the exact quotient, rounded up. The row for π² uses `Ψ(1/2, 1) = π²/3`. Its bound is
weaker than the known bounds for `μ(π²)` and is included for completeness.

The shared results are in `CatalanCore/Uniform/` (namespace `CatalanCore.Uniform`): the content theorem
`Content.BankShared.Check.hasScaledContent_of_check`, and its form for frames with several first poles,
`Content.BankShared.KTerm.hasScaledContent_of_kcheck`; the rank bound
`Content.BankShared.TwoTerm.LP2HypW.gle` and the window bound
`Content.BankShared.TwoTerm.Pre.prefix_gle`; the third-order bound at the primes where the border of the
matrix wraps around, `Content.UFSimple.WrapPrefixCheck.catValid_prefix_full`; the selection theorem `BlockGeom.hasNV0`; the decay theorem
`Decay.AltDecay.altGeom_hasScaledDecay`; and the deduction `measure_of_family_nv0_even`. They also use
modules from the rest of `CatalanCore/` and from `CatalanFrames/` and `CatalanLambda/` (among them the
frames, Cauchy determinants and Andréief's identity). The data of each family are in
`CatalanCore/Uniform/Bank/`.

### G ± 5π²/48

The shifts `1/4` and `3/4`, with `ψ′(1/4) = π² + 8G` and `ψ′(3/4) = π² − 8G`. The two shifts exchange the
two classes of primes modulo 4, so they have the same content constant, and one decay certificate serves
both. The frame, the decay cover and the nonvanishing are in `Bank/Fourths/`, the content table in
`Bank/FourthsContent/`. The theorem is `CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_measure`,
whose Boolean argument selects the sign; the public theorems are `TrigammaDifferences.lambda_minus_measure`
and `TrigammaDifferences.lambda_plus_measure` (the names refer to `λ± = G/2 ± 5π²/96`, so that
`G ± 5π²/48 = 2λ±`).

### L(2, χ₋₃)

The frame is `−⅓ ψ(z + ⅓) + ½ ψ(z + ½) − ⅙ ψ(z + 1)`, with `c = 1/2`. It has three digamma terms, so the
local bounds at a prime `p` involve two first poles; on each class of primes modulo 6 both are affine in
one index, and the content theorem applies with `q` replaced by 6. The content constant is
`Λ = 4.09592776731…`, and `γ/(D − Λ) = 13.704516… < 13.7046`. The content is in `Bank/Chi3/KContent/`
(`chi3_k_content`), the decay in `Bank/Chi3New/` (`chi3_decay`) with its cover in `Bank/Chi3/Cover/`, and
the theorem is `CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measure_L2_k`; the public theorem is
`TrigammaDifferences.chi3_measure`.

### L(2, χ₋₃) ± π²/9

The shifts `1/3` and `2/3`: with `L = L(2, χ₋₃)`, `ψ′(1/3) = 2π²/3 + 9L/2` and `ψ′(2/3) = 2π²/3 − 9L/2`.
The content table uses the primes in the classes modulo 6. The data are in `Bank/Thirds/` and
`Bank/ThirdsContent/`; the theorems are `CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_plus_measure`
and `thirds_minus_measure`, and the public theorems `TrigammaDifferences.chi3_plus_pi2_measure` and
`TrigammaDifferences.chi3_minus_pi2_measure`.

### ψ′(a/5) − π²/6

For `1 ≤ a ≤ 4`, `ψ′(a/5) − ζ(2)` is a rational linear combination of the values `L(2, χ)` for the
Dirichlet characters `χ` modulo 5. The four shifts share one content table, indexed by the four root
classes of the primes, and one decay certificate. The data are in `Bank/Fifths/` and
`Bank/FifthsContent/`; the theorems are `CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths1_measure`,
…, `fifths4_measure`, and the public theorems `TrigammaDifferences.fifths1_measure`, …,
`TrigammaDifferences.fifths4_measure`.

### ψ′(a/7) − π²/6

For `1 ≤ a ≤ 6`, likewise a combination of the values `L(2, χ)`, `χ` modulo 7, and of `π²`, with six root
classes. Here `D − Λ` is about `2.7·10⁻³`, and the exponent is correspondingly large. The data are in
`Bank/Sevenths/` and `Bank/SeventhsContent/`; the theorem is
`CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure`, whose argument is `a − 1` in `Fin 6`,
and the public theorems are `TrigammaDifferences.sevenths1_measure`, …,
`TrigammaDifferences.sevenths6_measure`.

### π²

The shift `1/2`, with `Ψ(1/2, 1) = π²/3`. The data are in `Bank/Halves/` and `Bank/HalvesContent/`; the
theorem is `CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_measure`, and the public theorem is
`TrigammaDifferences.pi2_measure`. The bound `6.5253` is weaker than the known bounds for `μ(π²)`.

## Kernel-checked certificates

All numerical bounds are ordinary kernel-checked rational and integer computations (`decide +kernel`;
no `native_decide`): for `G`, the inverses and residue tables modulo 1009, the trial sequences, the cell
covers and the stored kernel vectors; for the trigamma differences, the content tables and the cell
covers of the decay certificates. The certificate data were computed with floating-point optimisation and
interval arithmetic (Arb), which are not trusted: Lean rechecks every inequality.
Large certificates are split into many small declarations with explicit intermediate values, chained by
general lemmas, and integer recurrences whose values are divisible by large powers of 2, such as the
Chebyshev and Clenshaw recurrences, are checked on the quotients by those powers. The scripts that
generated the data are in [`scripts/`](scripts/); the authoritative proof data are the Lean source
literals.

## Vendored code

Palomar requires Lean v4.35.0-rc2 or later, and every imported file must use Lean's module
system. OpenAI's repository is pinned to Lean v4.34.1 and does not use modules, so 479 files of
OpenAI's formalization (from commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of
[openai/math](https://github.com/openai/math)) and the 10 files that OpenAI adds to
PrimeNumberTheoremAnd are copied into `OAI/` and `PrimeNumberTheoremAnd/`. Each was converted to a
module and adjusted for the newer Lean and Mathlib (see [`PORTING.md`](PORTING.md)). The proof of
μ(G) ≤ 410 imports 386 of the files in `OAI/` and all 10 in `PrimeNumberTheoremAnd/`; the proofs for the
trigamma differences import no file of `OAI/` and, for the Wiener–Ikehara theorem, 9 of the files in
`PrimeNumberTheoremAnd/`. In 37 point-evaluation files of OpenAI's certificate, which the theorems above do not import,
the comparison constants are given to seven digits (the computations are unchanged; see `NOTICE`).
Licences and attributions are in [`NOTICE`](NOTICE); all of this code is under the Apache License 2.0.

The directory `archive/` holds Lean modules that the theorems above do not import. It is not part of
the default build and is not used by any proof above.

## Building and checking

You need [elan](https://github.com/leanprover/elan) and several GiB of free disk.

```text
lake exe cache get
python3 scripts/check-lean-sources.py
lake build
ruby scripts/validate-formalization.rb
ruby scripts/validate-formalization.rb formalization-hybrid.yaml
./scripts/verify-comparator.sh
```

`lake build` builds both solution files. The numerical checks can use several GiB per Lean process; use
a small worker count (for example `LEAN_NUM_THREADS=2`) on memory-constrained machines. The comparator
script checks `comparator.json`; it needs Linux and `bwrap` (bubblewrap).

## Authorship and use of AI

The mathematics, the Lean formalization, the certificate generators and the text were produced by AI systems at the request of the author, who posed the problems, directed the work and is responsible for it: Claude Opus 5.5, Claude Sonnet 5.5 and Claude Haiku 5.5 (Anthropic), running in Claude Code, and GPT-6.1 Sol (OpenAI), running in Codex. The underlying irrationality proof for G and its Lean formalization are OpenAI's, as is the vendored code described above.

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE) ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)).

---

## Why this repo is up

Reproducible verified bounds: Litsey's μ(G) ≤ 410 measure converted to the verifier's Submission layout — public evidence for independent rebuilds.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

The conversion is complete at Lean v4.34.1 / Mathlib d13f23b7. Open work: independent rebuilds; work below the 295 frontier (see catalan-295-litsey-port).

