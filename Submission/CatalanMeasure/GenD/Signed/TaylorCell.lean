module

public import Submission.CatalanMeasure.CellCert.Cell
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

/-!
# Sound Taylor-model cell bound with point coefficients and an exact quadratic maximum

Lean counterpart of the repaired arb bound `lfarb.taylor_box_ub`
(`g-joint-cert-2026-10-29/scripts/lfarb.py`, NOTES section 16.2).  For a field `s + g` on the cell
`[c - r, c + r]` the bound is

`min V (A0 + max (qs l1 A2 r) (qs u1 A2 r) + Σ_{k=3}^{M-1} B_k r^k + B_M r^M) + G`,

where

* `A0 ≥ s(c)`, `l1 ≤ s'(c) ≤ u1`, `A2 ≥ s''(c)/2` are the **point** Taylor coefficients at the
  centre (enclosures, not box-wide bounds);
* `qs a A r` is the **exact maximum** of `a y + A y²` over `|y| ≤ r` (vertex if it lies in the
  cell, else an endpoint);
* `B_k ≥ |s^{(k)}(c)| / k!` for `3 ≤ k < M`, and `B_M ≥ |s^{(M)}(ξ)| / M!` for **all** `ξ` in the
  cell (the remainder enclosure);
* `V` is an optional crude upper bound of `s` on the cell and `G ≥ g` on the cell is a separately
  bounded piece (the `max(g0, gb)` of `taylor_box_ub`).

The old second-order box form `f(m) + |f'(m)| r + max(0, f'') r²/2` is *not* proved here: it is
unsound and non-convergent on the polynomial-density potentials (NOTES 16.1).

Layers:

1. `quadSupR`, `quad_le_quadSupR`, `quadSupR_attained`: the exact quadratic maximum.
2. `IsTower`, `tmUBR`, `taylor_cell_ub`, `taylor_cell_ub_full`: the generic theorem for any
   derivative tower (reusing `CellCert.taylor_tower'`).
3. `quadSupQ`, `tmUBQ`, `tmUBQ_cast`: the same bound on rationals, structurally recursive, for
   `decide +kernel`.
4. Pole (log) fields: `F' = Σ_q Re[ρ_q/(x - p_q)]` with the pole towers `qt` of `CellCert`.
   Point coefficients are exact rationals (`poleCoeff`, from `poleVal`); the remainder is the
   derivative bound of the log terms from the distance of the cell to the nearest pole
   (`poleRemQ`).  `poleCellCheck` is the Boolean checker, `poleCellCheck_sound` its soundness.

Sections 7-13 (general fields, block tails, pole-power sharing): Leibniz towers `mulTower`,
`logTower`, `polyTow` (`P(x) log|x - e|` has exact coefficients `plogCoefQ`, soundness
`plogCoefQ_spec`); `tower_majorant` (Taylor majorant of the `M`-th derivative over a block from the
point coefficients at the block centre), `polyTow_block`, `plog_block`; `FieldQ`/`fieldTower`
(polynomial + `Σ P_e log|x-e|` + pole potential), `fieldCellCheck_sound` (exact coefficients through
order `M-1` per cell, tail `BM` shared by the block) and `blockTailCheck_sound` (the tail);
`poleVec`/`poleVec_getD` (pole coefficients from per-pole power tables `powTabQ`, one table per pole
position shared by every field and every order; equal to `poleCoeff` exactly).

Not in this module: a derivation of the crude box evaluation `V` for pole sums (the `v` fallback of
`taylor_box_ub`, which wins when a pole is at distance `≤ r` from the cell; such cells are bisected
or take `V` from elsewhere), and the value certificate `F(c) ≤ A0` (the consumer's hypothesis).
-/

namespace CatalanMeasure.GenD.Signed.TaylorCell

open Set Nat CatalanMeasure.CellCert

/-! ### 1. The exact maximum of `a y + A y²` over `|y| ≤ r` -/

/-- Exact maximum of `y ↦ a y + A y²` over `|y| ≤ r` (the `_quad_sup` of `lfarb.py`): the vertex
value `a²/(-4A)` if `A < 0` and the vertex lies in the cell, else the larger endpoint value. -/
noncomputable def quadSupR (a A r : ℝ) : ℝ :=
  if A < 0 ∧ |a| ≤ -2 * A * r then a ^ 2 / (-4 * A) else |a| * r + A * r ^ 2

theorem quad_le_quadSupR (a A r y : ℝ) (hy : |y| ≤ r) :
    a * y + A * y ^ 2 ≤ quadSupR a A r := by
  have hr : 0 ≤ r := (abs_nonneg y).trans hy
  unfold quadSupR
  split_ifs with h
  · obtain ⟨hA, -⟩ := h
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (a + 2 * A * y)]
  · have hay : a * y ≤ |a| * |y| := by rw [← abs_mul]; exact le_abs_self _
    have hy2 : y ^ 2 ≤ r ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le y]) ((le_abs_self y).trans hy)
    by_cases hA : 0 ≤ A
    · nlinarith [mul_le_mul_of_nonneg_left hy2 hA, mul_le_mul_of_nonneg_left hy (abs_nonneg a)]
    · replace hA : A < 0 := not_le.mp hA
      have hlt : -2 * A * r < |a| := by
        by_contra hc
        exact h ⟨hA, not_lt.mp hc⟩
      have hAs : 0 ≤ A * (|y| - r) := mul_nonneg_of_nonpos_of_nonpos hA.le (by linarith)
      have hsq : A * |y| ^ 2 = A * y ^ 2 := by rw [sq_abs]
      have key : 0 ≤ (r - |y|) * (|a| + A * (r + |y|)) := by
        refine mul_nonneg (by linarith) ?_
        nlinarith
      nlinarith

/-- The maximum is attained: `quadSupR` is the *exact* maximum, not merely an upper bound. -/
theorem quadSupR_attained (a A r : ℝ) (hr : 0 ≤ r) :
    ∃ y : ℝ, |y| ≤ r ∧ a * y + A * y ^ 2 = quadSupR a A r := by
  unfold quadSupR
  split_ifs with h
  · obtain ⟨hA, ha⟩ := h
    refine ⟨-a / (2 * A), ?_, ?_⟩
    · have h2 : |2 * A| = -2 * A := by rw [abs_of_neg (by linarith)]; ring
      rw [abs_div, abs_neg, h2, div_le_iff₀ (by linarith)]
      linarith
    · have : A ≠ 0 := hA.ne
      field_simp
      ring
  · by_cases ha : 0 ≤ a
    · exact ⟨r, by rw [abs_of_nonneg hr], by rw [abs_of_nonneg ha]⟩
    · replace ha : a < 0 := not_le.mp ha
      exact ⟨-r, by rw [abs_neg, abs_of_nonneg hr], by rw [abs_of_neg ha]; ring⟩

/-- Interval form: `a₁ ∈ [l₁, u₁]` and `a₂ ≤ A₂` (the maximum is convex in `a₁`, monotone in
`a₂`, as in `taylor_box_ub`). -/
theorem quad_le_max (l1 u1 a1 a2 A2 r y : ℝ) (hy : |y| ≤ r) (h1l : l1 ≤ a1) (h1u : a1 ≤ u1)
    (h2 : a2 ≤ A2) :
    a1 * y + a2 * y ^ 2 ≤ max (quadSupR l1 A2 r) (quadSupR u1 A2 r) := by
  have hy2 : a2 * y ^ 2 ≤ A2 * y ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg y)
  rcases le_total 0 y with hy0 | hy0
  · have h3 : a1 * y ≤ u1 * y := mul_le_mul_of_nonneg_right h1u hy0
    have h4 := quad_le_quadSupR u1 A2 r y hy
    exact (by linarith : a1 * y + a2 * y ^ 2 ≤ quadSupR u1 A2 r).trans (le_max_right _ _)
  · have h3 : a1 * y ≤ l1 * y := mul_le_mul_of_nonpos_right h1l hy0
    have h4 := quad_le_quadSupR l1 A2 r y hy
    exact (by linarith : a1 * y + a2 * y ^ 2 ≤ quadSupR l1 A2 r).trans (le_max_left _ _)

/-! ### 2. The generic Taylor-model theorem for a derivative tower -/

/-- `f j` is the `j`-th derivative of `f 0` on the cell `[c - r, c + r]`, for `j ≤ M`
(continuity on the closed cell, derivatives on the open cell; the interface of
`CellCert.taylor_tower'`). -/
structure IsTower (f : ℕ → ℝ → ℝ) (c r : ℝ) (M : ℕ) : Prop where
  cont : ∀ j ≤ M, ContinuousOn (f j) (Icc (c - r) (c + r))
  der : ∀ j < M, ∀ x ∈ Ioo (c - r) (c + r), HasDerivAt (f j) (f (j + 1) x) x

theorem IsTower.add {f g : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hf : IsTower f c r M)
    (hg : IsTower g c r M) : IsTower (fun j x => f j x + g j x) c r M where
  cont j hj := (hf.cont j hj).add (hg.cont j hj)
  der j hj x hx := (hf.der j hj x hx).add (hg.der j hj x hx)

theorem IsTower.sub {f g : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hf : IsTower f c r M)
    (hg : IsTower g c r M) : IsTower (fun j x => f j x - g j x) c r M where
  cont j hj := (hf.cont j hj).sub (hg.cont j hj)
  der j hj x hx := (hf.der j hj x hx).sub (hg.der j hj x hx)

theorem IsTower.smul {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (w : ℝ) (hf : IsTower f c r M) :
    IsTower (fun j x => w * f j x) c r M where
  cont j hj := (hf.cont j hj).const_smul w
  der j hj x hx := (hf.der j hj x hx).const_mul w

/-- Smooth parts: a `C^M` function on `ℝ` has the tower `iteratedDeriv`. -/
theorem isTower_iteratedDeriv {f : ℝ → ℝ} {M : ℕ} (hf : ContDiff ℝ (M : WithTop ℕ∞) f)
    (c r : ℝ) : IsTower (fun j => iteratedDeriv j f) c r M where
  cont j hj := (hf.continuous_iteratedDeriv j (by exact_mod_cast hj)).continuousOn
  der j hj x _ := by
    have hd := (hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)) x
    simpa [iteratedDeriv_succ] using hd.hasDerivAt

/-- The bound of `taylor_box_ub` (without the crude `V` and the separate piece `G`):
`A0 + max (qs l1 A2 r) (qs u1 A2 r) + Σ_{k=3}^{M-1} B_k r^k + B_M r^M`. -/
noncomputable def tmUBR (A0 l1 u1 A2 r : ℝ) (B : ℕ → ℝ) (BM : ℝ) (M : ℕ) : ℝ :=
  A0 + max (quadSupR l1 A2 r) (quadSupR u1 A2 r) + ∑ k ∈ Finset.Ico 3 M, B k * r ^ k + BM * r ^ M

/-- **The soundness theorem (generic form).**  Taylor model of order `M ≥ 3` with point
coefficients at the centre `c` and an exact quadratic maximum: for every `x` in the cell,
`f 0 x ≤ tmUBR ...`.  Hypotheses: point value, first coefficient enclosure, second coefficient
upper bound, bounds of the point coefficients `3 ≤ k < M`, and the remainder enclosure of
`f M / M!` over the whole cell. -/
theorem taylor_cell_ub {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hM : 3 ≤ M) (hf : IsTower f c r M)
    {A0 l1 u1 A2 BM : ℝ} {B : ℕ → ℝ}
    (h0 : f 0 c ≤ A0) (h1l : l1 ≤ f 1 c) (h1u : f 1 c ≤ u1) (h2 : f 2 c / 2 ≤ A2)
    (hB : ∀ k, 3 ≤ k → k < M → |f k c| / (k ! : ℝ) ≤ B k)
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f M x| / (M ! : ℝ) ≤ BM) :
    ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ tmUBR A0 l1 u1 A2 r B BM M := by
  intro x hx
  have hxr : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hr : 0 ≤ r := (abs_nonneg _).trans hxr
  have hcI : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  have hfac : (0 : ℝ) < (M ! : ℝ) := by positivity
  have hbd : ∀ y ∈ Icc (c - r) (c + r), |f M y| ≤ (M ! : ℝ) * BM := by
    intro y hy
    have := hBM y hy
    rw [div_le_iff₀ hfac] at this
    linarith
  have htay := taylor_tower' c r ((M ! : ℝ) * BM) M f hf.cont
    (fun j hj y hy => hf.der j hj y hy) hbd x hx
  have hBM0 : 0 ≤ BM := (div_nonneg (abs_nonneg _) hfac.le).trans (hBM c hcI)
  have hrem : |f 0 x - ∑ j ∈ Finset.range M, f j c * (x - c) ^ j / (j ! : ℝ)| ≤ BM * r ^ M := by
    refine htay.trans ?_
    have e : (M ! : ℝ) * BM * |x - c| ^ M / (M ! : ℝ) = BM * |x - c| ^ M := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxr M) hBM0
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => f j c * (x - c) ^ j / (j ! : ℝ)) hM
  have h3 : ∑ j ∈ Finset.range 3, f j c * (x - c) ^ j / (j ! : ℝ) =
      f 0 c + f 1 c * (x - c) + (f 2 c / 2) * (x - c) ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have hmid : ∑ j ∈ Finset.Ico 3 M, f j c * (x - c) ^ j / (j ! : ℝ) ≤
      ∑ k ∈ Finset.Ico 3 M, B k * r ^ k := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨hk3, hkM⟩ := Finset.mem_Ico.mp hk
    have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
    have hBk := hB k hk3 hkM
    have e : f k c * (x - c) ^ k / (k ! : ℝ) = (f k c / (k ! : ℝ)) * (x - c) ^ k := by ring
    rw [e]
    calc (f k c / (k ! : ℝ)) * (x - c) ^ k ≤ |f k c / (k ! : ℝ)| * |x - c| ^ k := by
          rw [← abs_pow, ← abs_mul]; exact le_abs_self _
      _ ≤ B k * r ^ k := by
          have hab : |f k c / (k ! : ℝ)| = |f k c| / (k ! : ℝ) := by
            rw [abs_div, Nat.abs_cast]
          rw [hab]
          exact mul_le_mul hBk (pow_le_pow_left₀ (abs_nonneg _) hxr k)
            (by positivity) ((div_nonneg (abs_nonneg _) hk0.le).trans hBk)
  have hq := quad_le_max l1 u1 (f 1 c) (f 2 c / 2) A2 r (x - c) hxr h1l h1u h2
  have hrem2 := (abs_le.mp hrem).2
  unfold tmUBR
  linarith

/-- **The full form of `taylor_box_ub`:** `min(v, Taylor model) + max(g0, gb)`, with `V` a crude
upper bound of `f 0` on the cell (the plain interval evaluation `cb[0].upper()`) and `G` an upper
bound of the separately bounded piece `g`. -/
theorem taylor_cell_ub_full {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hM : 3 ≤ M)
    (hf : IsTower f c r M) {A0 l1 u1 A2 BM V G : ℝ} {B : ℕ → ℝ} {g : ℝ → ℝ}
    (h0 : f 0 c ≤ A0) (h1l : l1 ≤ f 1 c) (h1u : f 1 c ≤ u1) (h2 : f 2 c / 2 ≤ A2)
    (hB : ∀ k, 3 ≤ k → k < M → |f k c| / (k ! : ℝ) ≤ B k)
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f M x| / (M ! : ℝ) ≤ BM)
    (hV : ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ V) (hG : ∀ x ∈ Icc (c - r) (c + r), g x ≤ G) :
    ∀ x ∈ Icc (c - r) (c + r),
      f 0 x + g x ≤ min V (tmUBR A0 l1 u1 A2 r B BM M) + G := by
  intro x hx
  have h := taylor_cell_ub hM hf h0 h1l h1u h2 hB hBM x hx
  have := le_min (hV x hx) h
  linarith [hG x hx]

/-! ### 3. The same bound on rationals (for `decide +kernel`) -/

/-- `quadSupR` on rationals (no square roots; one division). -/
def quadSupQ (a A r : ℚ) : ℚ :=
  if A < 0 ∧ qabs' a ≤ -2 * A * r then a ^ 2 / (-4 * A) else qabs' a * r + A * r ^ 2

theorem quadSupQ_cast (a A r : ℚ) :
    ((quadSupQ a A r : ℚ) : ℝ) = quadSupR (a : ℝ) (A : ℝ) (r : ℝ) := by
  unfold quadSupQ quadSupR
  have hc : (A < 0 ∧ qabs' a ≤ -2 * A * r) ↔
      ((A : ℝ) < 0 ∧ |(a : ℝ)| ≤ -2 * (A : ℝ) * (r : ℝ)) := by
    rw [← qabs'_cast]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  split_ifs with h1 h2 h3
  · push_cast; ring
  · exact absurd (hc.mp h1) h2
  · exact absurd (hc.mpr h3) h1
  · push_cast; rw [qabs'_cast]

theorem qmax_cast (a b : ℚ) : ((qmax a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  unfold qmax
  split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (by exact_mod_cast (not_le.mp h).le)]

/-- `Σ_i B_i r^(k₀ + i)`. -/
def powSumQ (r : ℚ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | k, b :: bs => b * r ^ k + powSumQ r (k + 1) bs

theorem powSumQ_cast (r : ℚ) (Bl : List ℚ) :
    ∀ k : ℕ, ((powSumQ r k Bl : ℚ) : ℝ) =
      ∑ i ∈ Finset.range Bl.length, ((Bl.getD i 0 : ℚ) : ℝ) * (r : ℝ) ^ (k + i) := by
  induction Bl with
  | nil => intro k; simp [powSumQ]
  | cons b bs ih =>
    intro k
    rw [powSumQ, List.length_cons, Finset.sum_range_succ']
    push_cast
    rw [ih (k + 1)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show k + (i + 1) = k + 1 + i by omega]

/-- The Taylor-model bound on rationals.  `Bl = [B_3, ..., B_{M-1}]`, `M = |Bl| + 3`, and `BM`
bounds `|f^{(M)}|/M!` on the cell. -/
def tmUBQ (A0 l1 u1 A2 r : ℚ) (Bl : List ℚ) (BM : ℚ) : ℚ :=
  A0 + qmax (quadSupQ l1 A2 r) (quadSupQ u1 A2 r) + powSumQ r 3 Bl + BM * r ^ (Bl.length + 3)

theorem tmUBQ_cast (A0 l1 u1 A2 r : ℚ) (Bl : List ℚ) (BM : ℚ) :
    ((tmUBQ A0 l1 u1 A2 r Bl BM : ℚ) : ℝ) =
      tmUBR (A0 : ℝ) (l1 : ℝ) (u1 : ℝ) (A2 : ℝ) (r : ℝ)
        (fun k => ((Bl.getD (k - 3) 0 : ℚ) : ℝ)) (BM : ℝ) (Bl.length + 3) := by
  unfold tmUBQ tmUBR
  push_cast
  rw [qmax_cast, quadSupQ_cast, quadSupQ_cast, powSumQ_cast r Bl 3,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]

/-- Rational form of the generic theorem. -/
theorem taylor_cell_ub_rat {f : ℕ → ℝ → ℝ} {c r : ℝ} (Bl : List ℚ)
    (hf : IsTower f c r (Bl.length + 3)) {A0 l1 u1 A2 BM : ℚ}
    (h0 : f 0 c ≤ (A0 : ℝ)) (h1l : (l1 : ℝ) ≤ f 1 c) (h1u : f 1 c ≤ (u1 : ℝ))
    (h2 : f 2 c / 2 ≤ (A2 : ℝ))
    (hB : ∀ i < Bl.length, |f (3 + i) c| / ((3 + i) ! : ℝ) ≤ ((Bl.getD i 0 : ℚ) : ℝ))
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f (Bl.length + 3) x| / ((Bl.length + 3) ! : ℝ) ≤ (BM : ℝ))
    (rq : ℚ) (hrq : (rq : ℝ) = r) :
    ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ ((tmUBQ A0 l1 u1 A2 rq Bl BM : ℚ) : ℝ) := by
  intro x hx
  rw [tmUBQ_cast, hrq]
  refine taylor_cell_ub (by omega) hf h0 h1l h1u h2 ?_ hBM x hx
  intro k hk3 hkM
  have := hB (k - 3) (by omega)
  rwa [show 3 + (k - 3) = k by omega] at this

/-! ### 4. Pole (log) fields -/

/-- Casting a list sum of rationals. -/
theorem cast_list_sum_q {α : Type*} (L : List α) (g : α → ℚ) :
    (((L.map g).sum : ℚ) : ℝ) = (L.map (fun a => ((g a : ℚ) : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-- The derivative tower of a field `F` whose derivative is the pole sum `Σ_q Re[ρ_q/(x-p_q)]`
(`F = Σ_q Re[ρ_q log(x - p_q)] + const`): `F^{(j+1)} = Σ_q qt q j`. -/
noncomputable def poleTower (poles : List PoleR) (F : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => F
  | j + 1 => fun x => (poles.map (fun q => qt q j x)).sum

theorem poleTower_zero (poles : List PoleR) (F : ℝ → ℝ) : poleTower poles F 0 = F := rfl

theorem poleTower_succ (poles : List PoleR) (F : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    poleTower poles F (j + 1) x = (poles.map (fun q => qt q j x)).sum := rfl

theorem isTower_poleTower (poles : List PoleR) (F : ℝ → ℝ) (c r : ℝ) (M : ℕ)
    (hne : ∀ y ∈ Icc (c - r) (c + r), ∀ q ∈ poles, (y : ℂ) ≠ q.pc)
    (hF : ∀ y ∈ Icc (c - r) (c + r),
      HasDerivAt F ((poles.map (fun q => qt q 0 y)).sum) y) :
    IsTower (poleTower poles F) c r M where
  cont j _ y hy := by
    cases j with
    | zero => exact (hF y hy).continuousAt.continuousWithinAt
    | succ j => exact (hasDerivAt_listsum_qt poles j y (hne y hy)).continuousAt.continuousWithinAt
  der j _ y hy := by
    have hyc : y ∈ Icc (c - r) (c + r) := ⟨hy.1.le, hy.2.le⟩
    cases j with
    | zero => exact hF y hyc
    | succ j => exact hasDerivAt_listsum_qt poles j y (hne y hyc)

/-- Exact rational Taylor coefficient `F^{(k)}(c)/k! = Σ_q poleVal q c (k-1) / k!`, `k ≥ 1`. -/
def poleCoeff (poles : List PoleR) (c : ℚ) (k : ℕ) : ℚ :=
  (poles.map (fun q => poleVal q c (k - 1))).sum / ((k ! : ℕ) : ℚ)

theorem poleCoeff_spec (poles : List PoleR) (F : ℝ → ℝ) (c : ℚ) (k : ℕ) :
    ((poleCoeff poles c (k + 1) : ℚ) : ℝ) = poleTower poles F (k + 1) (c : ℝ) / ((k + 1)! : ℝ) := by
  unfold poleCoeff
  rw [poleTower_succ, Rat.cast_div, cast_list_sum_q, Rat.cast_natCast]
  simp only [Nat.add_sub_cancel, poleVal_spec]

/-- Rational lower bound for the distance of a pole `p` to the cell `[lo, hi]`:
`max(g, |Im p|, 0.7071 (g + |Im p|))` with `g` the real gap (`‖z‖ ≥ (|Re z| + |Im z|)/√2`).
This is at least as sharp as `poleDl` and within a few percent of the true distance. -/
def poleGap (q : PoleR) (lo hi : ℚ) : ℚ := qmax 0 (qmax (lo - q.pr) (q.pr - hi))

def poleDist (q : PoleR) (lo hi : ℚ) : ℚ :=
  qmax (qmax (poleGap q lo hi) (qabs' q.pi)) ((7071 / 10000) * (poleGap q lo hi + qabs' q.pi))

theorem poleDist_le_norm (q : PoleR) (lo hi : ℚ) (y : ℝ) (h1 : (lo : ℝ) ≤ y) (h2 : y ≤ (hi : ℝ)) :
    ((poleDist q lo hi : ℚ) : ℝ) ≤ ‖(y : ℂ) - q.pc‖ := by
  set z : ℂ := (y : ℂ) - q.pc with hz
  have hre : z.re = y - q.pr := by simp [hz, PoleR.pc]
  have him : z.im = -(q.pi : ℝ) := by simp [hz, PoleR.pc]
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have := Complex.sq_norm_sub_sq_re z
    linarith
  have hg : ((poleGap q lo hi : ℚ) : ℝ) ≤ |z.re| := by
    unfold poleGap
    refine qmax_cast_le _ _ _ (by rw [Rat.cast_zero]; exact abs_nonneg _)
      (qmax_cast_le _ _ _ ?_ ?_)
    · push_cast; rw [hre]; linarith [le_abs_self (y - q.pr)]
    · push_cast; rw [hre]; linarith [neg_abs_le (y - q.pr)]
  have hb : ((qabs' q.pi : ℚ) : ℝ) = |z.im| := by rw [qabs'_cast, him, abs_neg]
  have hre_le : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him_le : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hgn : 0 ≤ ((poleGap q lo hi : ℚ) : ℝ) := by
    unfold poleGap
    have : ((0 : ℚ) : ℝ) ≤ ((qmax 0 (qmax (lo - q.pr) (q.pr - hi)) : ℚ) : ℝ) := by
      rw [qmax_cast]; push_cast; exact le_max_left _ _
    simpa using this
  unfold poleDist
  refine qmax_cast_le _ _ _ (qmax_cast_le _ _ _ (hg.trans hre_le) (by rw [hb]; exact him_le)) ?_
  push_cast
  rw [hb]
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  have hx : 0 ≤ |z.re| + |z.im| := by positivity
  have hsum : (7071 / 10000 : ℝ) * (((poleGap q lo hi : ℚ) : ℝ) + |z.im|) ≤
      (7071 / 10000 : ℝ) * (|z.re| + |z.im|) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith
  have h3 : ‖z‖ < (7071 / 10000 : ℝ) * (|z.re| + |z.im|) := lt_of_lt_of_le hcon hsum
  have h4 : ‖z‖ ^ 2 < ((7071 / 10000 : ℝ) * (|z.re| + |z.im|)) ^ 2 := by
    apply pow_lt_pow_left₀ h3 hn (by norm_num)
  have h5 : z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
  have h6 : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
  nlinarith [sq_nonneg (|z.re| - |z.im|)]

/-- Remainder bound of the pole terms (the derivative bound of log terms from the distance to the
nearest pole): `Σ_q (|Re ρ_q| + |Im ρ_q|) / (M dist_q^M)`, an upper bound of `|F^{(M)}|/M!`
over the cell `[lo, hi]` (`M ≥ 1`). -/
def poleRemQ (poles : List PoleR) (lo hi : ℚ) (M : ℕ) : ℚ :=
  (poles.map (fun q => (qabs' q.rr + qabs' q.ri) / ((M : ℚ) * poleDist q lo hi ^ M))).sum

theorem poleTower_rem (poles : List PoleR) (F : ℝ → ℝ) (lo hi : ℚ)
    (hdl : ∀ q ∈ poles, 0 < poleDist q lo hi) (m : ℕ) (y : ℝ) (h1 : (lo : ℝ) ≤ y)
    (h2 : y ≤ (hi : ℝ)) :
    |poleTower poles F (m + 1) y| / ((m + 1)! : ℝ) ≤ ((poleRemQ poles lo hi (m + 1) : ℚ) : ℝ) := by
  have hfac : (0 : ℝ) < ((m + 1)! : ℝ) := by positivity
  rw [poleTower_succ, div_le_iff₀ hfac]
  have hb : |(poles.map (fun q => qt q m y)).sum| ≤
      (poles.map (fun q => (|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) /
        ((poleDist q lo hi : ℚ) : ℝ) ^ (m + 1))).sum := by
    refine (abs_list_sum_le poles _).trans (List.sum_le_sum (fun q hq => ?_))
    exact qt_bound q m y _ (by exact_mod_cast hdl q hq) (poleDist_le_norm q lo hi y h1 h2)
  refine hb.trans ?_
  unfold poleRemQ
  rw [cast_list_sum_q, ← List.sum_map_mul_right]
  refine List.sum_le_sum (fun q hq => ?_)
  have hd : (0 : ℝ) < ((poleDist q lo hi : ℚ) : ℝ) := by exact_mod_cast hdl q hq
  push_cast
  rw [qabs'_cast, qabs'_cast]
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  apply le_of_eq
  field_simp

/-- Boolean check of the supplied coefficient bounds: `|a_k| ≤ B_k` for `k = k₀, k₀+1, ...`. -/
def coeffBoundsOK (poles : List PoleR) (c : ℚ) : ℕ → List ℚ → Bool
  | _, [] => true
  | k, b :: bs => decide (qabs' (poleCoeff poles c k) ≤ b) && coeffBoundsOK poles c (k + 1) bs

theorem coeffBoundsOK_spec (poles : List PoleR) (c : ℚ) :
    ∀ (Bl : List ℚ) (k : ℕ), coeffBoundsOK poles c k Bl = true →
      ∀ i < Bl.length, qabs' (poleCoeff poles c (k + i)) ≤ Bl.getD i 0 := by
  intro Bl
  induction Bl with
  | nil => intro k _ i hi; simp at hi
  | cons b bs ih =>
    intro k h i hi
    simp only [coeffBoundsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have := ih (k + 1) h.2 j (by simpa using hi)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      simpa using this

/-- The Boolean checker for one cell `[lo, hi]` of a pole field `F` (all data are rationals):
the poles are away from the cell, `l1 ≤ a₁ ≤ u1`, `a₂ ≤ A2`, `|a_k| ≤ B_k` (`3 ≤ k < M`), the
remainder `poleRemQ ≤ BM`, and the Taylor-model bound `tmUBQ ≤ T`. -/
def poleCellCheck (poles : List PoleR) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) : Bool :=
  decide (lo ≤ hi) &&
  poles.all (fun q => decide (0 < poleDist q lo hi)) &&
  decide (l1 ≤ poleCoeff poles ((lo + hi) / 2) 1) &&
  decide (poleCoeff poles ((lo + hi) / 2) 1 ≤ u1) &&
  decide (poleCoeff poles ((lo + hi) / 2) 2 ≤ A2) &&
  coeffBoundsOK poles ((lo + hi) / 2) 3 Bl &&
  decide (poleRemQ poles lo hi (Bl.length + 3) ≤ BM) &&
  decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

/-- **The soundness theorem every Phase 2 per-cell sup check applies (pole fields).**  If the
checker accepts, then `F ≤ T` on the whole cell `[lo, hi]`, given that `F' = Σ_q Re[ρ_q/(x-p_q)]`
on the cell and `F(centre) ≤ A0`. -/
theorem poleCellCheck_sound (poles : List PoleR) (F : ℝ → ℝ) (lo hi A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T : ℚ)
    (hchk : poleCellCheck poles lo hi A0 l1 u1 A2 Bl BM T = true)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F ((poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : F (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), F x ≤ (T : ℝ) := by
  simp only [poleCellCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hlh, hdl⟩, hl1⟩, hu1⟩, hA2⟩, hB⟩, hBM⟩, hT⟩ := hchk
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have hdl' : ∀ q ∈ poles, 0 < poleDist q lo hi := fun q hq => by simpa using hdl q hq
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hne : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), ∀ q ∈ poles, (y : ℂ) ≠ q.pc := by
    intro y hy q hq heq
    rw [hcell] at hy
    have := poleDist_le_norm q lo hi y hy.1 hy.2
    rw [heq, sub_self, norm_zero] at this
    have h2 : (0 : ℝ) < ((poleDist q lo hi : ℚ) : ℝ) := by exact_mod_cast hdl' q hq
    linarith
  have hF' : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      HasDerivAt F ((poles.map (fun q => qt q 0 y)).sum) y := by
    intro y hy; rw [hcell] at hy; exact hF y hy
  have hT0 := isTower_poleTower poles F (c : ℝ) (r : ℝ) (Bl.length + 3) hne hF'
  have hcoef := coeffBoundsOK_spec poles c Bl 3 hB
  intro x hx
  rw [← hcell] at hx
  have key := taylor_cell_ub_rat (f := poleTower poles F) (c := (c : ℝ)) (r := (r : ℝ)) Bl hT0
    (A0 := A0) (l1 := l1) (u1 := u1) (A2 := A2) (BM := BM)
    (by simpa [poleTower_zero] using h0)
    (by
      have := poleCoeff_spec poles F c 0
      have h1' : (l1 : ℝ) ≤ ((poleCoeff poles c 1 : ℚ) : ℝ) := by exact_mod_cast hl1
      simpa [this] using h1')
    (by
      have := poleCoeff_spec poles F c 0
      have h1' : ((poleCoeff poles c 1 : ℚ) : ℝ) ≤ (u1 : ℝ) := by exact_mod_cast hu1
      simpa [this] using h1')
    (by
      have := poleCoeff_spec poles F c 1
      have h2' : ((poleCoeff poles c 2 : ℚ) : ℝ) ≤ (A2 : ℝ) := by exact_mod_cast hA2
      rw [this] at h2'
      simpa [Nat.factorial] using h2')
    (by
      intro i hi
      have h1 := hcoef i hi
      have h2 := poleCoeff_spec poles F c (2 + i)
      have h3 : ((qabs' (poleCoeff poles c (3 + i)) : ℚ) : ℝ) ≤ ((Bl.getD i 0 : ℚ) : ℝ) := by
        exact_mod_cast h1
      rw [qabs'_cast] at h3
      rw [show 3 + i = 2 + i + 1 by omega] at h3 ⊢
      rw [h2] at h3
      rwa [abs_div, Nat.abs_cast] at h3)
    (by
      intro y hy
      rw [hcell] at hy
      have := poleTower_rem poles F lo hi hdl' (Bl.length + 2) y hy.1 hy.2
      have hrem : ((poleRemQ poles lo hi (Bl.length + 2 + 1) : ℚ) : ℝ) ≤ (BM : ℝ) := by
        exact_mod_cast hBM
      exact this.trans hrem)
    r (by simp [hr])
  have := key x hx
  refine this.trans ?_
  exact_mod_cast hT

/-- The checker with a separately bounded piece `g ≤ G` on the cell (the `+ max(g0, gb)` of
`taylor_box_ub`; for example `-log|x|/(2ν)` near `0`, bounded by its endpoint value). -/
theorem poleCellCheck_sound_add (poles : List PoleR) (F g : ℝ → ℝ) (lo hi A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T G : ℚ)
    (hchk : poleCellCheck poles lo hi A0 l1 u1 A2 Bl BM T = true)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F ((poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : F (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (hg : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), g x ≤ (G : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), F x + g x ≤ (T : ℝ) + (G : ℝ) := by
  intro x hx
  have := poleCellCheck_sound poles F lo hi A0 l1 u1 A2 Bl BM T hchk hF h0 x hx
  linarith [hg x hx]

/-! ### 5. Derivative lemmas for the fields (hypothesis `hF` of the checker) -/

/-- `w · log |y - p|` has derivative `Re[w/(x - p)]` (the real pole `p`, real weight `w`). -/
theorem hasDerivAt_log_abs_sub (w p : ℚ) (x : ℝ) (hx : x ≠ (p : ℝ)) :
    HasDerivAt (fun y => (w : ℝ) * Real.log |y - p|) (qt ⟨w, 0, p, 0⟩ 0 x) x := by
  rw [qt_real]
  have h1 : HasDerivAt (fun y : ℝ => y - (p : ℝ)) 1 x := (hasDerivAt_id x).sub_const _
  have h2 := (h1.log (sub_ne_zero.mpr hx)).const_mul (w : ℝ)
  simp only [Real.log_abs] at *
  refine h2.congr_deriv ?_
  ring

/-- `w · log |1 - a y|` has derivative `Re[w/(x - 1/a)]` (the pole `1/a`), `a ≠ 0`. -/
theorem hasDerivAt_log_abs_one_sub (w a : ℚ) (ha : a ≠ 0) (x : ℝ) (hx : (1 : ℝ) - a * x ≠ 0) :
    HasDerivAt (fun y => (w : ℝ) * Real.log |1 - a * y|) (qt ⟨w, 0, 1 / a, 0⟩ 0 x) x := by
  rw [qt_real]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have h1 : HasDerivAt (fun y : ℝ => 1 - (a : ℝ) * y) (-(a : ℝ)) x := by
    simpa using ((hasDerivAt_id x).const_mul (a : ℝ)).const_sub 1
  have h2 := (h1.log hx).const_mul (w : ℝ)
  simp only [Real.log_abs] at *
  refine h2.congr_deriv ?_
  have : x - ((1 / a : ℚ) : ℝ) = -(1 - (a : ℝ) * x) / a := by
    push_cast; field_simp; ring
  rw [this]
  field_simp

/-- `Re[ρ log (y - p)]` for a non-real pole `p` has derivative `Re[ρ/(x - p)]`. -/
theorem hasDerivAt_re_clog (q : PoleR) (hq : q.pi ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (q.rho * Complex.log ((y : ℂ) - q.pc)).re) (qt q 0 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) - q.pc) 1 x :=
    ((hasDerivAt_id x).ofReal_comp).sub_const _
  have hs : ((x : ℂ) - q.pc) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [PoleR.pc, hq]
  have h2 := (h1.clog_real hs).const_mul q.rho
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h2
  refine h3.congr_deriv ?_
  simp [qt, qe]

/-! ### 6. Regression: `log x ≤ 23/100` on `[3/4, 5/4]` through the whole chain -/

example : ∀ x ∈ Icc ((3 / 4 : ℚ) : ℝ) ((5 / 4 : ℚ) : ℝ), Real.log x ≤ ((23 / 100 : ℚ) : ℝ) := by
  refine poleCellCheck_sound [⟨1, 0, 0, 0⟩] Real.log (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (23 / 100) (by decide +kernel) ?_ ?_
  · intro x hx
    have hx0 : x ≠ 0 := by
      have : (0 : ℝ) < ((3 / 4 : ℚ) : ℝ) := by norm_num
      exact (lt_of_lt_of_le this hx.1).ne'
    simpa [qt_real] using Real.hasDerivAt_log hx0
  · norm_num

/-- Negative controls: the model value is `0.2251987...` (true sup `log (5/4) = 0.2231...`); the
checker accepts `0.2252`, rejects `0.2251` (model value above), `0.22` (below the true sup), and a
coefficient bound that is too small. -/
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (2252 / 10000) = true := by decide +kernel
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (2251 / 10000) = false := by decide +kernel
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (22 / 100) = false := by decide +kernel
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 6, 1 / 6, 1 / 7] (5 / 4) (23 / 100) = false := by decide +kernel

/-! ### 7. Leibniz towers: products, `log |x - e|`, polynomials -/

/-- Leibniz tower of a product: `(u v)^{(n)} = Σ_{i+j=n} C(n,i) u^{(i)} v^{(j)}`. -/
def mulTower (u v : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal n, (n.choose ij.1 : ℝ) * (u ij.1 x * v ij.2 x)

theorem mulTower_zero (u v : ℕ → ℝ → ℝ) (x : ℝ) : mulTower u v 0 x = u 0 x * v 0 x := by
  simp [mulTower]

theorem IsTower.mul {u v : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hu : IsTower u c r M)
    (hv : IsTower v c r M) : IsTower (mulTower u v) c r M where
  cont j hj := by
    unfold mulTower
    refine continuousOn_finsetSum _ (fun ij hij => ?_)
    have h := Finset.mem_antidiagonal.mp hij
    exact continuousOn_const.mul ((hu.cont _ (by omega)).mul (hv.cont _ (by omega)))
  der j hj x hx := by
    have h : HasDerivAt (fun y => ∑ ij ∈ Finset.antidiagonal j,
        (j.choose ij.1 : ℝ) * (u ij.1 y * v ij.2 y))
        (∑ ij ∈ Finset.antidiagonal j, (j.choose ij.1 : ℝ) *
          (u (ij.1 + 1) x * v ij.2 x + u ij.1 x * v (ij.2 + 1) x)) x := by
      refine HasDerivAt.fun_sum (fun ij hij => ?_)
      have h := Finset.mem_antidiagonal.mp hij
      exact ((hu.der ij.1 (by omega) x hx).mul (hv.der ij.2 (by omega) x hx)).const_mul _
    have key := Finset.sum_antidiagonal_choose_succ_mul (R := ℝ) (fun a b => u a x * v b x) j
    have e : mulTower u v (j + 1) x = ∑ ij ∈ Finset.antidiagonal j, (j.choose ij.1 : ℝ) *
          (u (ij.1 + 1) x * v ij.2 x + u ij.1 x * v (ij.2 + 1) x) := by
      unfold mulTower
      rw [key]
      have e2 : ∑ ij ∈ Finset.antidiagonal j, (j.choose ij.2 : ℝ) * (u (ij.1 + 1) x * v ij.2 x) =
          ∑ ij ∈ Finset.antidiagonal j, (j.choose ij.1 : ℝ) * (u (ij.1 + 1) x * v ij.2 x) := by
        refine Finset.sum_congr rfl (fun ij hij => ?_)
        rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm]
      rw [e2, add_comm, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ij _ => by ring)
    rw [e]
    exact h

/-- Normalised Leibniz: `(u v)^{(n)}/n! = Σ_{i+j=n} (u^{(i)}/i!)(v^{(j)}/j!)`. -/
theorem mulTower_div (u v : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    mulTower u v n x / (n ! : ℝ) =
      ∑ ij ∈ Finset.antidiagonal n, (u ij.1 x / (ij.1 ! : ℝ)) * (v ij.2 x / (ij.2 ! : ℝ)) := by
  unfold mulTower
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  have h := Finset.mem_antidiagonal.mp hij
  have hf := Nat.add_choose_mul_factorial_mul_factorial ij.1 ij.2
  rw [h] at hf
  have hf' : ((n.choose ij.2 : ℕ) : ℝ) * (ij.1 ! : ℝ) * (ij.2 ! : ℝ) = (n ! : ℝ) := by
    exact_mod_cast hf
  rw [Nat.choose_symm_of_eq_add h.symm]
  have h1 : (ij.1 ! : ℝ) ≠ 0 := by positivity
  have h2 : (ij.2 ! : ℝ) ≠ 0 := by positivity
  have h3 : (n ! : ℝ) ≠ 0 := by positivity
  have h4 : (n.choose ij.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : ij.2 ≤ n)).ne'
  rw [← hf']
  field_simp

/-- `log |x - e|` and its derivatives `(-1)^m m! / (x - e)^(m+1)`. -/
noncomputable def logTower (e : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.log |x - e|
  | m + 1 => fun x => (-1 : ℝ) ^ m * (m ! : ℝ) / (x - e) ^ (m + 1)

theorem hasDerivAt_logTower (e : ℝ) (j : ℕ) (x : ℝ) (hx : x ≠ e) :
    HasDerivAt (logTower e j) (logTower e (j + 1) x) x := by
  have hne : x - e ≠ 0 := sub_ne_zero.mpr hx
  have h1 : HasDerivAt (fun y : ℝ => y - e) 1 x := (hasDerivAt_id x).sub_const _
  cases j with
  | zero =>
    have h2 := h1.log hne
    simp only [logTower]
    simp only [Real.log_abs] at *
    refine h2.congr_deriv ?_
    simp
  | succ m =>
    have h3 : HasDerivAt (fun y : ℝ => (y - e) ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * (x - e) ^ m * 1) x :=
      h1.pow (m + 1)
    have h4 := (hasDerivAt_const x ((-1 : ℝ) ^ m * (m ! : ℝ))).div h3 (pow_ne_zero _ hne)
    simp only [logTower]
    refine h4.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem isTower_logTower (e c r : ℝ) (M : ℕ) (hne : ∀ x ∈ Icc (c - r) (c + r), x ≠ e) :
    IsTower (logTower e) c r M where
  cont j _ y hy := (hasDerivAt_logTower e j y (hne y hy)).continuousAt.continuousWithinAt
  der j _ y hy := hasDerivAt_logTower e j y (hne y ⟨hy.1.le, hy.2.le⟩)

/-- Horner tower of a polynomial given by its coefficient list `[a₀, a₁, ...]` (low to high):
`polyTow p 0 = a₀ + x (a₁ + x (...))`; `polyTow p k = p^{(k)}`. -/
noncomputable def polyTow : List ℚ → ℕ → ℝ → ℝ
  | [], _ => fun _ => 0
  | a :: as, 0 => fun x => (a : ℝ) + x * polyTow as 0 x
  | _ :: as, k + 1 => fun x => x * polyTow as (k + 1) x + ((k : ℝ) + 1) * polyTow as k x

theorem hasDerivAt_polyTow (p : List ℚ) : ∀ (k : ℕ) (x : ℝ),
    HasDerivAt (polyTow p k) (polyTow p (k + 1) x) x := by
  induction p with
  | nil => intro k x; simpa [polyTow] using hasDerivAt_const x (0 : ℝ)
  | cons a as ih =>
    intro k x
    cases k with
    | zero =>
      have h := ((hasDerivAt_id x).mul (ih 0 x)).const_add (a : ℝ)
      simp only [polyTow]
      refine h.congr_deriv ?_
      simp
      ring
    | succ k =>
      have h := ((hasDerivAt_id x).mul (ih (k + 1) x)).add ((ih k x).const_mul ((k : ℝ) + 1))
      simp only [polyTow]
      refine h.congr_deriv ?_
      push_cast
      simp only [id]
      ring

theorem isTower_polyTow (p : List ℚ) (c r : ℝ) (M : ℕ) : IsTower (polyTow p) c r M where
  cont j _ y _ := (hasDerivAt_polyTow p j y).continuousAt.continuousWithinAt
  der j _ y _ := hasDerivAt_polyTow p j y

/-- Beyond the degree the Horner tower vanishes. -/
theorem polyTow_eq_zero (p : List ℚ) : ∀ (k : ℕ), p.length ≤ k → ∀ x, polyTow p k x = 0 := by
  induction p with
  | nil => intro k _ x; simp [polyTow]
  | cons a as ih =>
    intro k hk x
    cases k with
    | zero => simp at hk
    | succ k =>
      simp only [polyTow]
      rw [ih (k + 1) (by simp at hk; omega) x, ih k (by simp at hk; omega) x]
      ring

/-- One Horner step of the exact Taylor shift: from the coefficient list `t` of `q` at `c` to that
of `a + x q(x)`: `c t_k + t_{k-1}` (with `t_{-1} = a`). -/
def shiftStep (c : ℚ) : List ℚ → ℚ → List ℚ
  | [], _ => []
  | s :: ss, prev => (c * s + prev) :: shiftStep c ss s

/-- The first `M + 1` Taylor coefficients at `c` of the polynomial with coefficient list `p`. -/
def shiftL (c : ℚ) (M : ℕ) : List ℚ → List ℚ
  | [] => List.replicate (M + 1) 0
  | a :: as => shiftStep c (shiftL c M as) a

theorem shiftStep_length (c : ℚ) : ∀ (t : List ℚ) (prev : ℚ), (shiftStep c t prev).length = t.length := by
  intro t
  induction t with
  | nil => intro prev; simp [shiftStep]
  | cons s ss ih => intro prev; simp [shiftStep, ih]

theorem shiftL_length (c : ℚ) (M : ℕ) (p : List ℚ) : (shiftL c M p).length = M + 1 := by
  induction p with
  | nil => simp [shiftL]
  | cons a as ih => simp [shiftL, shiftStep_length, ih]

theorem shiftStep_getD (c : ℚ) : ∀ (t : List ℚ) (prev : ℚ) (k : ℕ), k < t.length →
    (shiftStep c t prev).getD k 0 = c * t.getD k 0 + (if k = 0 then prev else t.getD (k - 1) 0) := by
  intro t
  induction t with
  | nil => intro prev k hk; simp at hk
  | cons s ss ih =>
    intro prev k hk
    cases k with
    | zero => simp [shiftStep]
    | succ k =>
      simp only [shiftStep, List.getD_cons_succ]
      rw [ih s k (by simpa using hk)]
      cases k with
      | zero => simp
      | succ k => simp

/-- Exact Taylor coefficients of a polynomial: `p^{(k)}(c)/k!` for `k ≤ M`. -/
theorem shiftL_spec (c : ℚ) (M : ℕ) (p : List ℚ) : ∀ k ≤ M,
    (((shiftL c M p).getD k 0 : ℚ) : ℝ) = polyTow p k (c : ℝ) / (k ! : ℝ) := by
  induction p with
  | nil => intro k _; simp [shiftL, polyTow, ]
  | cons a as ih =>
    intro k hk
    have hl := shiftL_length c M as
    cases k with
    | zero =>
      simp only [shiftL]
      rw [shiftStep_getD c _ _ 0 (by omega)]
      have := ih 0 (by omega)
      simp only [polyTow, Nat.factorial_zero, Nat.cast_one, div_one] at this ⊢
      push_cast
      rw [this]
      ring
    | succ k =>
      simp only [shiftL]
      rw [shiftStep_getD c _ _ (k + 1) (by omega)]
      have h1 := ih (k + 1) hk
      have h2 := ih k (by omega)
      simp only [Nat.add_sub_cancel, ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero k))]
      push_cast
      rw [h1, h2]
      simp only [polyTow]
      have hk1 : ((k + 1 : ℕ) ! : ℝ) = ((k : ℝ) + 1) * (k ! : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hk1]
      have hk0 : (k ! : ℝ) ≠ 0 := by positivity
      have hk2 : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp


/-! ### 8. Exact Taylor coefficients of `P(x) log|x - e|` (Leibniz) -/

/-- `Σ_{j<n} U_j V(k - j)`, structurally recursive. -/
def partialConv (U : List ℚ) (V : ℕ → ℚ) (k : ℕ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => partialConv U V k j + U.getD j 0 * V (k - j)

theorem partialConv_cast (U : List ℚ) (V : ℕ → ℚ) (k n : ℕ) :
    ((partialConv U V k n : ℚ) : ℝ) =
      ∑ j ∈ Finset.range n, ((U.getD j 0 : ℚ) : ℝ) * ((V (k - j) : ℚ) : ℝ) := by
  induction n with
  | zero => simp [partialConv]
  | succ n ih => rw [partialConv, Finset.sum_range_succ, ← ih]; push_cast; rfl

/-- `L^{(m)}(c)/m!` for `L = log|x - e|`, `m ≥ 1`, with `d = c - e`: `(-1)^{m-1} / (m d^m)`. -/
def logTailQ (d : ℚ) (m : ℕ) : ℚ := (-1) ^ (m - 1) / ((m : ℚ) * d ^ m)

theorem logTower_coef_succ (e c : ℝ) (hne : c - e ≠ 0) (m : ℕ) :
    logTower e (m + 1) c / ((m + 1)! : ℝ) = (-1) ^ m / (((m : ℝ) + 1) * (c - e) ^ (m + 1)) := by
  simp only [logTower]
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (m ! : ℝ) ≠ 0 := by positivity
  have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem logTailQ_cast (e c : ℚ) (hne : c - e ≠ 0) (m : ℕ) :
    ((logTailQ (c - e) (m + 1) : ℚ) : ℝ) = logTower (e : ℝ) (m + 1) (c : ℝ) / ((m + 1)! : ℝ) := by
  have h : (c : ℝ) - (e : ℝ) ≠ 0 := by exact_mod_cast hne
  rw [logTower_coef_succ _ _ h]
  unfold logTailQ
  push_cast
  simp

/-- Exact normalised coefficients of `P(x) log|x - e|`: `a_k = L P_k + Σ_{j<k} P_j (-1)^{k-j-1}/((k-j) d^{k-j})`
with `P_j` the Taylor coefficients of `P` at `c`, `d = c - e`, `L = log |c - e|`. -/
def plogCoefQ (Pk : List ℚ) (d L : ℚ) (k : ℕ) : ℚ :=
  L * Pk.getD k 0 + partialConv Pk (logTailQ d) k k

theorem plogCoefQ_spec (P : List ℚ) (e c L : ℚ) (hce : c - e ≠ 0)
    (hL : (L : ℝ) = Real.log |(c : ℝ) - (e : ℝ)|) (K : ℕ) (k : ℕ) (hk : k ≤ K) :
    mulTower (polyTow P) (logTower (e : ℝ)) k (c : ℝ) / (k ! : ℝ) =
      ((plogCoefQ (shiftL c K P) (c - e) L k : ℚ) : ℝ) := by
  rw [mulTower_div, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (polyTow P i (c : ℝ) / (i ! : ℝ)) * (logTower (e : ℝ) j (c : ℝ) / (j ! : ℝ))) k]
  unfold plogCoefQ
  push_cast
  rw [partialConv_cast, Finset.sum_range_succ]
  have hP : ∀ i ≤ K, ((( shiftL c K P).getD i 0 : ℚ) : ℝ) = polyTow P i (c : ℝ) / (i ! : ℝ) :=
    fun i hi => shiftL_spec c K P i hi
  have hlog0 : logTower (e : ℝ) 0 (c : ℝ) / ((0 : ℕ) ! : ℝ) = (L : ℝ) := by
    simp [logTower, hL]
  rw [Nat.sub_self, hlog0, hP k hk]
  rw [add_comm]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    rw [hP i (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
    rw [hm, ← logTailQ_cast e c hce m]


/-! ### 9. Block-level tails: one bound on the `M`-th derivative shared by a block of cells -/

/-- **Majorant of a derivative over a block** (Taylor's theorem for `g j = f (M + j)`).  If `f` has a
tower of order `M + N` on the block `[cb - ρ, cb + ρ]`, the point coefficients satisfy
`|f^{(M+j)}(cb)|/(M+j)! ≤ C_j` for `j < N` and `|f^{(M+N)}|/(M+N)! ≤ H` on the block, then
`|f^{(M)}(x)|/M! ≤ Σ_{j<N} C_j binom(M+j, M) ρ^j + binom(M+N, M) H ρ^N` for `x` in the block. -/
theorem tower_majorant {f : ℕ → ℝ → ℝ} {cb ρ : ℝ} {M N : ℕ} (hf : IsTower f cb ρ (M + N))
    {C : ℕ → ℝ} {H : ℝ}
    (hC : ∀ j < N, |f (M + j) cb| / ((M + j)! : ℝ) ≤ C j)
    (hH : ∀ x ∈ Icc (cb - ρ) (cb + ρ), |f (M + N) x| / ((M + N)! : ℝ) ≤ H) :
    ∀ x ∈ Icc (cb - ρ) (cb + ρ), |f M x| / (M ! : ℝ) ≤
      ∑ j ∈ Finset.range N, C j * ((M + j).choose M : ℝ) * ρ ^ j +
        ((M + N).choose M : ℝ) * H * ρ ^ N := by
  intro x hx
  have hxr : |x - cb| ≤ ρ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hxr
  have hcI : cb ∈ Icc (cb - ρ) (cb + ρ) := ⟨by linarith, by linarith⟩
  have hfacMN : (0 : ℝ) < ((M + N)! : ℝ) := by positivity
  have hH0 : 0 ≤ H := (div_nonneg (abs_nonneg _) hfacMN.le).trans (hH cb hcI)
  have hbd : ∀ y ∈ Icc (cb - ρ) (cb + ρ), |f (M + N) y| ≤ ((M + N)! : ℝ) * H := by
    intro y hy
    have := hH y hy
    rw [div_le_iff₀ hfacMN] at this
    linarith
  have htay := taylor_tower' cb ρ (((M + N)! : ℝ) * H) N (fun j => f (M + j))
    (fun j hj => hf.cont (M + j) (by omega))
    (fun j hj y hy => hf.der (M + j) (by omega) y hy) (by simpa using hbd) x hx
  have htay : |f M x - ∑ j ∈ Finset.range N, f (M + j) cb * (x - cb) ^ j / (j ! : ℝ)| ≤
      ((M + N)! : ℝ) * H * |x - cb| ^ N / (N ! : ℝ) := htay
  have hfacM : (0 : ℝ) < (M ! : ℝ) := by positivity
  rw [div_le_iff₀ hfacM]
  have hchoose : ∀ j : ℕ, ((M + j)! : ℝ) = ((M + j).choose M : ℝ) * (M ! : ℝ) * (j ! : ℝ) := by
    intro j
    have := Nat.add_choose_mul_factorial_mul_factorial M j
    rw [Nat.choose_symm_of_eq_add rfl] at *
    have h2 : (((M + j).choose j * M ! * j ! : ℕ) : ℝ) = ((M + j)! : ℝ) := by exact_mod_cast this
    rw [← h2, ← Nat.choose_symm_of_eq_add (rfl : M + j = M + j)]
    push_cast; ring
  have hsum : |f M x| ≤ ∑ j ∈ Finset.range N, |f (M + j) cb| * ρ ^ j / (j ! : ℝ) +
      ((M + N)! : ℝ) * H * ρ ^ N / (N ! : ℝ) := by
    have h1 : |f M x| ≤ |∑ j ∈ Finset.range N, f (M + j) cb * (x - cb) ^ j / (j ! : ℝ)| +
        ((M + N)! : ℝ) * H * |x - cb| ^ N / (N ! : ℝ) := by
      have := abs_sub_abs_le_abs_sub (f M x) (∑ j ∈ Finset.range N, f (M + j) cb * (x - cb) ^ j / (j ! : ℝ))
      linarith
    refine h1.trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      gcongr
    · gcongr
  refine hsum.trans ?_
  have e1 : ∀ j ∈ Finset.range N, |f (M + j) cb| * ρ ^ j / (j ! : ℝ) ≤
      C j * ((M + j).choose M : ℝ) * ρ ^ j * (M ! : ℝ) := by
    intro j _
    have h1 := hC j (by simpa using ‹j ∈ Finset.range N›)
    have hfj : (0 : ℝ) < ((M + j)! : ℝ) := by positivity
    rw [div_le_iff₀ hfj] at h1
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (j ! : ℝ))]
    rw [hchoose j] at h1
    have hρj : 0 ≤ ρ ^ j := pow_nonneg hρ j
    calc |f (M + j) cb| * ρ ^ j ≤ C j * (((M + j).choose M : ℝ) * (M ! : ℝ) * (j ! : ℝ)) * ρ ^ j :=
          mul_le_mul_of_nonneg_right h1 hρj
      _ = C j * ((M + j).choose M : ℝ) * ρ ^ j * (M ! : ℝ) * (j ! : ℝ) := by ring
  have e2 : ((M + N)! : ℝ) * H * ρ ^ N / (N ! : ℝ) =
      ((M + N).choose M : ℝ) * H * ρ ^ N * (M ! : ℝ) := by
    rw [hchoose N]
    have : (N ! : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e2]
  calc _ ≤ ∑ j ∈ Finset.range N, C j * ((M + j).choose M : ℝ) * ρ ^ j * (M ! : ℝ) +
        ((M + N).choose M : ℝ) * H * ρ ^ N * (M ! : ℝ) := add_le_add (Finset.sum_le_sum e1) le_rfl
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Rational majorant `Σ_i b_i binom(M + j + i, M) ρ^{j+i}` for a list `b` of coefficient bounds
(starting at index `M + j`). -/
def majQ (ρ : ℚ) (M : ℕ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | j, b :: bs => b * ((M + j).choose M : ℚ) * ρ ^ j + majQ ρ M (j + 1) bs

theorem majQ_cast (ρ : ℚ) (M : ℕ) (bs : List ℚ) : ∀ j : ℕ, ((majQ ρ M j bs : ℚ) : ℝ) =
    ∑ i ∈ Finset.range bs.length, ((bs.getD i 0 : ℚ) : ℝ) * ((M + (j + i)).choose M : ℝ) *
      (ρ : ℝ) ^ (j + i) := by
  induction bs with
  | nil => intro j; simp [majQ]
  | cons b bs ih =>
    intro j
    rw [majQ, List.length_cons, Finset.sum_range_succ']
    push_cast
    rw [ih (j + 1)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show j + (i + 1) = j + 1 + i by omega]

/-- `Cb` bounds the normalised Taylor coefficients of the polynomial `P` at `cb`:
`|P^{(k)}(cb)|/k! ≤ Cb_k` for all `k` (the list is at least as long as `P`). -/
def PolyBnd (P : List ℚ) (cb : ℝ) (Cb : List ℚ) : Prop :=
  P.length ≤ Cb.length ∧
    ∀ k < Cb.length, |polyTow P k cb| / (k ! : ℝ) ≤ ((Cb.getD k 0 : ℚ) : ℝ)

/-- Bounds checked against exact Taylor coefficients: `|T_k| ≤ b_k` for `k = k₀, k₀ + 1, ...`. -/
def absLeAll (T : List ℚ) : ℕ → List ℚ → Bool
  | _, [] => true
  | k, b :: bs => decide (qabs' (T.getD k 0) ≤ b) && absLeAll T (k + 1) bs

theorem absLeAll_spec (T : List ℚ) : ∀ (Bl : List ℚ) (k : ℕ), absLeAll T k Bl = true →
    ∀ i < Bl.length, qabs' (T.getD (k + i) 0) ≤ Bl.getD i 0 := by
  intro Bl
  induction Bl with
  | nil => intro k _ i hi; simp at hi
  | cons b bs ih =>
    intro k h i hi
    simp only [absLeAll, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have := ih (k + 1) h.2 j (by simpa using hi)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      simpa using this

/-- The polynomial coefficient bounds from the exact Taylor shift: if `P` is no longer than `Cb`
and `|T_k| ≤ Cb_k` for the shift `T` at `cb` (to order `|Cb|`), then `PolyBnd`. -/
theorem polyBnd_of_check (P : List ℚ) (cb : ℚ) (Cb : List ℚ) (hlen : P.length ≤ Cb.length)
    (hchk : absLeAll (shiftL cb Cb.length P) 0 Cb = true) : PolyBnd P (cb : ℝ) Cb := by
  refine ⟨hlen, fun k hk => ?_⟩
  have h := absLeAll_spec _ Cb 0 hchk k hk
  rw [zero_add] at h
  have h2 := shiftL_spec cb Cb.length P k hk.le
  have h3 : ((qabs' ((shiftL cb Cb.length P).getD k 0) : ℚ) : ℝ) ≤ ((Cb.getD k 0 : ℚ) : ℝ) := by
    exact_mod_cast h
  rw [qabs'_cast, h2, abs_div, Nat.abs_cast] at h3
  exact h3

theorem getD_drop' (l : List ℚ) (M j : ℕ) : (l.drop M).getD j 0 = l.getD (M + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Block bound for a polynomial part**: for `x` in the block `[cb - ρ, cb + ρ]`,
`|P^{(M)}(x)|/M! ≤ Σ_j Cb_{M+j} binom(M+j, M) ρ^j`, from the Taylor coefficients at the block
centre only (the derivatives of order `≥ |P|` vanish). -/
theorem polyTow_block {P : List ℚ} {cb ρ : ℝ} {Cb : List ℚ} (hb : PolyBnd P cb Cb) (ρq : ℚ)
    (hρ : (ρq : ℝ) = ρ) (M : ℕ) :
    ∀ x ∈ Icc (cb - ρ) (cb + ρ),
      |polyTow P M x| / (M ! : ℝ) ≤ ((majQ ρq M 0 (Cb.drop M) : ℚ) : ℝ) := by
  have hN : M + (Cb.drop M).length ≥ P.length := by
    have := hb.1; simp only [List.length_drop]; omega
  have key := tower_majorant (f := polyTow P) (cb := cb) (ρ := ρ) (M := M) (N := (Cb.drop M).length)
    (isTower_polyTow P cb ρ _) (C := fun j => (((Cb.drop M).getD j 0 : ℚ) : ℝ)) (H := 0)
    (fun j hj => by
      rw [getD_drop']
      exact hb.2 (M + j) (by simp only [List.length_drop] at hj; omega))
    (fun x _ => by
      rw [polyTow_eq_zero P _ hN x]; simp)
  intro x hx
  refine (key x hx).trans (le_of_eq ?_)
  rw [majQ_cast, ← hρ]
  simp

/-- Leibniz bound of a product at a point from bounds of the factors' normalised derivatives. -/
theorem mulTower_block_bound {u v : ℕ → ℝ → ℝ} {n : ℕ} {x : ℝ} {U V : ℕ → ℝ}
    (hU : ∀ i ≤ n, |u i x| / (i ! : ℝ) ≤ U i) (hV : ∀ j ≤ n, |v j x| / (j ! : ℝ) ≤ V j) :
    |mulTower u v n x| / (n ! : ℝ) ≤ ∑ ij ∈ Finset.antidiagonal n, U ij.1 * V ij.2 := by
  have hf : (0 : ℝ) < (n ! : ℝ) := by positivity
  have e0 : |mulTower u v n x| / (n ! : ℝ) = |mulTower u v n x / (n ! : ℝ)| := by
    rw [abs_div, abs_of_pos hf]
  rw [e0, mulTower_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ij hij => ?_))
  have h := Finset.mem_antidiagonal.mp hij
  rw [abs_mul, abs_div, abs_div, Nat.abs_cast, Nat.abs_cast]
  exact mul_le_mul (hU _ (by omega)) (hV _ (by omega)) (by positivity)
    ((div_nonneg (abs_nonneg _) (by positivity)).trans (hU _ (by omega)))

/-- Sup-bound vector of the factor `log |x - e|` on a block: `V_0 = Lb`, `V_m = 1/(m dm^m)`. -/
def logVQ (Lb dm : ℚ) (m : ℕ) : ℚ := if m = 0 then Lb else 1 / ((m : ℚ) * dm ^ m)

theorem logTower_block_bound (e : ℝ) (Lb dm : ℚ) (hdm : 0 < dm) (x : ℝ)
    (hLb : |Real.log (|x - e|)| ≤ (Lb : ℝ)) (hd : (dm : ℝ) ≤ |x - e|) (j : ℕ) :
    |logTower e j x| / (j ! : ℝ) ≤ ((logVQ Lb dm j : ℚ) : ℝ) := by
  cases j with
  | zero => simpa [logTower, logVQ] using hLb
  | succ m =>
    have hdm' : (0 : ℝ) < dm := by exact_mod_cast hdm
    have hxe : 0 < |x - e| := lt_of_lt_of_le hdm' hd
    simp only [logTower, logVQ, Nat.succ_ne_zero, if_false]
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
      Nat.factorial_succ]
    push_cast
    have hm : (m ! : ℝ) ≠ 0 := by positivity
    have e1 : (m ! : ℝ) / |x - e| ^ (m + 1) / (((m : ℝ) + 1) * (m ! : ℝ)) =
        1 / (((m : ℝ) + 1) * |x - e| ^ (m + 1)) := by
      field_simp
    rw [e1]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdm'.le hd _) (by positivity)

/-- List of the polynomial block bounds `U_i = Σ_j Cb_{i+j} binom(i+j, i) ρ^j`, `i = 0..M`. -/
def majList (ρ : ℚ) (Cb : List ℚ) (M : ℕ) : List ℚ :=
  (List.range (M + 1)).map (fun i => majQ ρ i 0 (Cb.drop i))

/-- The block tail of a `P(x) log|x - e|` piece: `Σ_{i+m=M} U_i V_m`. -/
def plogTailQ (ρ : ℚ) (Cb : List ℚ) (Lb dm : ℚ) (M : ℕ) : ℚ :=
  partialConv (majList ρ Cb M) (logVQ Lb dm) M (M + 1)

/-- **Block bound for `P(x) log|x - e|`.**  On the block `[cb - ρ, cb + ρ]`, with `Cb` bounding the
Taylor coefficients of `P` at `cb`, `|log|x - e|| ≤ Lb` and `|x - e| ≥ dm > 0`:
`|(P log|x-e|)^{(M)}(x)|/M! ≤ plogTailQ`. -/
theorem plog_block {P : List ℚ} {e : ℚ} {cb ρ : ℝ} {Cb : List ℚ} (hb : PolyBnd P cb Cb) (ρq : ℚ)
    (hρ : (ρq : ℝ) = ρ) (Lb dm : ℚ) (hdm : 0 < dm)
    (hLb : ∀ x ∈ Icc (cb - ρ) (cb + ρ), |Real.log (|x - (e : ℝ)|)| ≤ (Lb : ℝ))
    (hd : ∀ x ∈ Icc (cb - ρ) (cb + ρ), (dm : ℝ) ≤ |x - (e : ℝ)|) (M : ℕ) :
    ∀ x ∈ Icc (cb - ρ) (cb + ρ),
      |mulTower (polyTow P) (logTower (e : ℝ)) M x| / (M ! : ℝ) ≤
        ((plogTailQ ρq Cb Lb dm M : ℚ) : ℝ) := by
  intro x hx
  have hU : ∀ i ≤ M, |polyTow P i x| / (i ! : ℝ) ≤ ((majList ρq Cb M).getD i 0 : ℚ) := by
    intro i hi
    have : (majList ρq Cb M).getD i 0 = majQ ρq i 0 (Cb.drop i) := by
      simp [majList, List.getD_eq_getElem?_getD, List.getElem?_range, Nat.lt_succ_of_le hi]
    rw [this]
    exact polyTow_block hb ρq hρ i x hx
  refine (mulTower_block_bound (U := fun i => (((majList ρq Cb M).getD i 0 : ℚ) : ℝ))
    (V := fun j => ((logVQ Lb dm j : ℚ) : ℝ)) hU
    (fun j _ => logTower_block_bound _ Lb dm hdm x (hLb x hx) (hd x hx) j)).trans (le_of_eq ?_)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (((majList ρq Cb M).getD i 0 : ℚ) : ℝ) * ((logVQ Lb dm j : ℚ) : ℝ)) M]
  unfold plogTailQ
  rw [partialConv_cast]


/-! ### 10. Coefficient vectors; pole sums from shared pole-power tables -/

theorem listsum_div {α : Type*} (L : List α) (f g : α → ℚ) (D : ℚ) (h : ∀ a ∈ L, f a = g a / D) :
    (L.map f).sum = (L.map g).sum / D := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb])), add_div]

/-- Entrywise sum of coefficient vectors (padding by `0`). -/
def vecAdd : List ℚ → List ℚ → List ℚ
  | a :: as, b :: bs => (a + b) :: vecAdd as bs
  | [], bs => bs
  | as, [] => as

theorem vecAdd_getD : ∀ (a b : List ℚ) (k : ℕ), (vecAdd a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  intro a
  induction a with
  | nil => intro b k; simp [vecAdd]
  | cons x xs ih =>
    intro b k
    cases b with
    | nil => simp [vecAdd]
    | cons y ys =>
      cases k with
      | zero => simp [vecAdd]
      | succ k =>
        simp only [vecAdd, List.getD_cons_succ]
        rw [ih ys k]

/-- Sum of a list of coefficient vectors. -/
def vecSum (ls : List (List ℚ)) : List ℚ := ls.foldr vecAdd []

theorem vecSum_getD (ls : List (List ℚ)) (k : ℕ) :
    (vecSum ls).getD k 0 = (ls.map (fun v => v.getD k 0)).sum := by
  induction ls with
  | nil => simp [vecSum]
  | cons v vs ih => simp only [vecSum, List.foldr_cons] at ih ⊢; rw [vecAdd_getD, ih]; simp

theorem getD_map_range (f : ℕ → ℚ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range, hk]

/-- The pole term `(-1)^{k-1}/k · Re[ρ w]` of the `k`-th normalised coefficient, `w = u^k`. -/
def poleTermQ (rr ri : ℚ) (k : ℕ) (w : ℚ × ℚ) : ℚ :=
  (-1) ^ (k - 1) / (k : ℚ) * (rr * w.1 - ri * w.2)

/-- The power table `[u, u², ..., u^n]` (by repeated multiplication; each power once). -/
def powTabAux (u : ℚ × ℚ) : ℕ → ℚ × ℚ → List (ℚ × ℚ)
  | 0, _ => []
  | n + 1, w => w :: powTabAux u n (cmulQ w u)

/-- The shared table of a pole *position* `(pr, pi)` at the centre `c`: `[u, ..., u^M]`,
`u = 1/(c - p)`.  It does not depend on the weights, so every field with the same pole positions
shares it. -/
def powTabQ (pr pi c : ℚ) (M : ℕ) : List (ℚ × ℚ) :=
  powTabAux (uOf ⟨0, 0, pr, pi⟩ c) M (uOf ⟨0, 0, pr, pi⟩ c)

theorem powTabAux_getD (u : ℚ × ℚ) : ∀ (n k : ℕ) (w : ℚ × ℚ), w = cpowQ u k →
    ∀ i < n, (powTabAux u n w).getD i (0, 0) = cpowQ u (k + i) := by
  intro n
  induction n with
  | zero => intro k w _ i hi; omega
  | succ n ih =>
    intro k w hw i hi
    cases i with
    | zero => simpa [powTabAux] using hw
    | succ i =>
      simp only [powTabAux, List.getD_cons_succ]
      rw [ih (k + 1) (cmulQ w u) (by rw [hw]; rfl) i (by omega)]
      rw [show k + 1 + i = k + (i + 1) by omega]

/-- Coefficient vector `[0, a_1, ..., a_M]` of one pole with weight `(rr, ri)` from a power table. -/
def poleVecTab (rr ri : ℚ) (tab : List (ℚ × ℚ)) : List ℚ :=
  0 :: (List.range tab.length).map (fun i => poleTermQ rr ri (i + 1) (tab.getD i (0, 0)))

/-- Coefficient vector of the pole sum from shared tables (one table per pole position). -/
def poleVecShared (poles : List PoleR) (tabs : List (List (ℚ × ℚ))) : List ℚ :=
  vecSum (List.zipWith (fun q tab => poleVecTab q.rr q.ri tab) poles tabs)

/-- The tables of a pole list at the centre `c`, to order `M`. -/
def poleTabs (poles : List PoleR) (c : ℚ) (M : ℕ) : List (List (ℚ × ℚ)) :=
  poles.map (fun q => powTabQ q.pr q.pi c M)

/-- Coefficient vector `[0, a_1, ..., a_M]` of the pole sum (own tables). -/
def poleVec (poles : List PoleR) (c : ℚ) (M : ℕ) : List ℚ :=
  poleVecShared poles (poleTabs poles c M)

theorem powTabQ_length (pr pi c : ℚ) (M : ℕ) : (powTabQ pr pi c M).length = M := by
  unfold powTabQ
  generalize uOf ⟨0, 0, pr, pi⟩ c = u
  suffices h : ∀ (n : ℕ) (w : ℚ × ℚ), (powTabAux u n w).length = n from h M u
  intro n
  induction n with
  | zero => intro w; simp [powTabAux]
  | succ n ih => intro w; simp [powTabAux, ih]

theorem poleVecTab_getD (rr ri : ℚ) (tab : List (ℚ × ℚ)) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ tab.length) :
    (poleVecTab rr ri tab).getD k 0 = poleTermQ rr ri k (tab.getD (k - 1) (0, 0)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold poleVecTab
  rw [List.getD_cons_succ, getD_map_range _ _ _ (by omega)]
  rfl

/-- **Pole-power sharing, exact equality.**  The coefficient `a_k` computed from the power tables
equals `poleCoeff` (which recomputes `u^k` for every `k`). -/
theorem poleVec_getD (poles : List PoleR) (c : ℚ) (M : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ M) :
    (poleVec poles c M).getD k 0 = poleCoeff poles c k := by
  unfold poleVec poleVecShared poleTabs
  rw [vecSum_getD]
  unfold poleCoeff
  have hzip : List.zipWith (fun q tab => poleVecTab q.rr q.ri tab) poles
      (poles.map (fun q => powTabQ q.pr q.pi c M)) =
      poles.map (fun q => poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)) := by
    induction poles with
    | nil => rfl
    | cons q qs ih => simp [List.zipWith_cons_cons, ih]
  rw [hzip, List.map_map]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hfac : (((j + 1)! : ℕ) : ℚ) = ((j : ℚ) + 1) * (j ! : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have key : ∀ q ∈ poles, (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD (j + 1) 0 =
      poleVal q c j / (((j + 1)! : ℕ) : ℚ) := by
    intro q _
    rw [poleVecTab_getD _ _ _ (j + 1) (by omega) (by rw [powTabQ_length]; omega)]
    have h1 : (powTabQ q.pr q.pi c M).getD (j + 1 - 1) (0, 0) = cpowQ (uOf q c) (j + 1) := by
      unfold powTabQ
      rw [Nat.add_sub_cancel]
      have := powTabAux_getD (uOf ⟨0, 0, q.pr, q.pi⟩ c) M 1 (uOf ⟨0, 0, q.pr, q.pi⟩ c)
        (by simp [cpowQ, cmulQ]) j (by omega)
      rw [this, add_comm 1 j]
      rfl
    rw [h1]
    unfold poleTermQ poleVal
    rw [Nat.add_sub_cancel, hfac]
    have h2 : (j ! : ℚ) ≠ 0 := by positivity
    have h3 : ((j : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  have := listsum_div poles (fun q => (poleVecTab q.rr q.ri (powTabQ q.pr q.pi c M)).getD (j + 1) 0)
    (fun q => poleVal q c j) _ key
  exact this


/-! ### 11. A field: polynomial + `Σ_e P_e(x) log|x - e|` + pole potential -/

/-- The data of a field of the Phase 2 form (all rational): a polynomial part (coefficients low to
high), pieces `P_e(x) log|x - e|`, and the pole sum (whose potential `F`, with
`F' = Σ_q Re[ρ_q/(x - p_q)]`, is the function argument of `fieldTower`). -/
structure FieldQ where
  poly : List ℚ
  plogs : List (List ℚ × ℚ)
  poles : List PoleR

/-- Tower of `Σ_e P_e log|x - e|`. -/
noncomputable def plogSumTower (plogs : List (List ℚ × ℚ)) (j : ℕ) (x : ℝ) : ℝ :=
  (plogs.map (fun t => mulTower (polyTow t.1) (logTower (t.2 : ℝ)) j x)).sum

/-- Tower of the whole field: `fieldTower fq F 0 x = poly(x) + Σ_e P_e(x) log|x - e| + F x`. -/
noncomputable def fieldTower (fq : FieldQ) (F : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  polyTow fq.poly j x + plogSumTower fq.plogs j x + poleTower fq.poles F j x

theorem isTower_plogSumTower (plogs : List (List ℚ × ℚ)) (c r : ℝ) (M : ℕ)
    (hne : ∀ t ∈ plogs, ∀ x ∈ Icc (c - r) (c + r), x ≠ (t.2 : ℝ)) :
    IsTower (plogSumTower plogs) c r M := by
  induction plogs with
  | nil =>
    have h : plogSumTower [] = fun _ _ => 0 := by funext j x; simp [plogSumTower]
    rw [h]
    exact ⟨fun j _ => continuousOn_const, fun j _ x _ => hasDerivAt_const x 0⟩
  | cons t ts ih =>
    have h : plogSumTower (t :: ts) = fun j x =>
        mulTower (polyTow t.1) (logTower (t.2 : ℝ)) j x + plogSumTower ts j x := by
      funext j x; simp [plogSumTower]
    rw [h]
    exact ((isTower_polyTow t.1 c r M).mul
      (isTower_logTower (t.2 : ℝ) c r M (hne t (by simp)))).add
      (ih (fun s hs => hne s (by simp [hs])))

theorem isTower_fieldTower (fq : FieldQ) (F : ℝ → ℝ) (c r : ℝ) (M : ℕ)
    (hnee : ∀ t ∈ fq.plogs, ∀ x ∈ Icc (c - r) (c + r), x ≠ (t.2 : ℝ))
    (hnep : ∀ y ∈ Icc (c - r) (c + r), ∀ q ∈ fq.poles, (y : ℂ) ≠ q.pc)
    (hF : ∀ y ∈ Icc (c - r) (c + r),
      HasDerivAt F ((fq.poles.map (fun q => qt q 0 y)).sum) y) :
    IsTower (fieldTower fq F) c r M :=
  ((isTower_polyTow fq.poly c r M).add (isTower_plogSumTower fq.plogs c r M hnee)).add
    (isTower_poleTower fq.poles F c r M hnep hF)

/-- Coefficient vector `[a_0, ..., a_M]` of `P(x) log|x - e|` at `c` (`L = log|c - e|` supplied). -/
def plogVec (P : List ℚ) (e c L : ℚ) (M : ℕ) : List ℚ :=
  let Pk := shiftL c M P
  (List.range (M + 1)).map (fun k => plogCoefQ Pk (c - e) L k)

/-- Sum of the coefficient vectors of the pieces (the logs `Ls` aligned with the pieces). -/
def plogSumVec (c : ℚ) (M : ℕ) : List (List ℚ × ℚ) → List ℚ → List ℚ
  | t :: ts, L :: Ls => vecAdd (plogVec t.1 t.2 c L M) (plogSumVec c M ts Ls)
  | _, _ => []

/-- The logs `L_e` supplied for the pieces (aligned) are rational enclosures of `log |c - e|`:
`|L_e - log |c - e|| ≤ ε_e` (the exact case is `ε_e = 0`). -/
def LogVals (c : ℚ) : List (List ℚ × ℚ) → List ℚ → List ℚ → Prop
  | [], [], [] => True
  | t :: ts, L :: Ls, ε :: εs =>
    |(L : ℝ) - Real.log (|(c : ℝ) - (t.2 : ℝ)|)| ≤ (ε : ℝ) ∧ LogVals c ts Ls εs
  | _, _, _ => False

/-- `P(x) log|x - e|`: the normalised coefficient is *affine* in the value of the log, with
slope the polynomial coefficient `P_k`, so an enclosure of the log gives
`|a_k - plogCoefQ ...| ≤ ε |P_k|`. -/
theorem plogCoef_split (P : List ℚ) (e c : ℚ) (hce : c - e ≠ 0) (K k : ℕ) (hk : k ≤ K) :
    mulTower (polyTow P) (logTower (e : ℝ)) k (c : ℝ) / (k ! : ℝ) =
      Real.log (|(c : ℝ) - (e : ℝ)|) * (((shiftL c K P).getD k 0 : ℚ) : ℝ) +
        ((partialConv (shiftL c K P) (logTailQ (c - e)) k k : ℚ) : ℝ) := by
  rw [mulTower_div, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (polyTow P i (c : ℝ) / (i ! : ℝ)) * (logTower (e : ℝ) j (c : ℝ) / (j ! : ℝ))) k]
  rw [partialConv_cast, Finset.sum_range_succ]
  have hP : ∀ i ≤ K, ((( shiftL c K P).getD i 0 : ℚ) : ℝ) = polyTow P i (c : ℝ) / (i ! : ℝ) :=
    fun i hi => shiftL_spec c K P i hi
  have hlog0 : logTower (e : ℝ) 0 (c : ℝ) / ((0 : ℕ) ! : ℝ) = Real.log (|(c : ℝ) - (e : ℝ)|) := by
    simp [logTower]
  rw [Nat.sub_self, hlog0, hP k hk]
  rw [add_comm]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    rw [hP i (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
    rw [hm, ← logTailQ_cast e c hce m]

theorem plogCoef_approx (P : List ℚ) (e c L ε : ℚ) (hce : c - e ≠ 0)
    (hL : |(L : ℝ) - Real.log (|(c : ℝ) - (e : ℝ)|)| ≤ (ε : ℝ)) (K k : ℕ) (hk : k ≤ K) :
    |mulTower (polyTow P) (logTower (e : ℝ)) k (c : ℝ) / (k ! : ℝ) -
        ((plogCoefQ (shiftL c K P) (c - e) L k : ℚ) : ℝ)| ≤
      ((ε * qabs' ((shiftL c K P).getD k 0) : ℚ) : ℝ) := by
  rw [plogCoef_split P e c hce K k hk]
  unfold plogCoefQ
  push_cast
  have e1 : Real.log (|(c : ℝ) - (e : ℝ)|) * (((shiftL c K P).getD k 0 : ℚ) : ℝ) +
        ((partialConv (shiftL c K P) (logTailQ (c - e)) k k : ℚ) : ℝ) -
      ((L : ℝ) * (((shiftL c K P).getD k 0 : ℚ) : ℝ) +
        ((partialConv (shiftL c K P) (logTailQ (c - e)) k k : ℚ) : ℝ)) =
      (Real.log (|(c : ℝ) - (e : ℝ)|) - (L : ℝ)) * (((shiftL c K P).getD k 0 : ℚ) : ℝ) := by
    ring
  rw [e1, abs_mul, qabs'_cast, abs_sub_comm]
  exact mul_le_mul_of_nonneg_right hL (abs_nonneg _)

/-- Error vector of one piece: `ε |P_k|`, `k = 0..M`. -/
def plogErr1 (P : List ℚ) (c ε : ℚ) (M : ℕ) : List ℚ :=
  let Pk := shiftL c M P
  (List.range (M + 1)).map (fun k => ε * qabs' (Pk.getD k 0))

def plogErrSum (c : ℚ) (M : ℕ) : List (List ℚ × ℚ) → List ℚ → List ℚ
  | t :: ts, ε :: εs => vecAdd (plogErr1 t.1 c ε M) (plogErrSum c M ts εs)
  | _, _ => []

theorem plogSumVec_approx (c : ℚ) (M : ℕ) : ∀ (plogs : List (List ℚ × ℚ)) (Ls εs : List ℚ),
    LogVals c plogs Ls εs → (∀ t ∈ plogs, c - t.2 ≠ 0) → ∀ k ≤ M,
    |plogSumTower plogs k (c : ℝ) / (k ! : ℝ) - (((plogSumVec c M plogs Ls).getD k 0 : ℚ) : ℝ)| ≤
      (((plogErrSum c M plogs εs).getD k 0 : ℚ) : ℝ) := by
  intro plogs
  induction plogs with
  | nil =>
    intro Ls εs hL _ k _
    cases Ls with
    | nil =>
      cases εs with
      | nil => simp [plogSumVec, plogSumTower, plogErrSum]
      | cons => exact absurd hL (by simp [LogVals])
    | cons => exact absurd hL (by cases εs <;> simp [LogVals])
  | cons t ts ih =>
    intro Ls εs hL hne k hk
    cases Ls with
    | nil => exact absurd hL (by cases εs <;> simp [LogVals])
    | cons L Ls =>
      cases εs with
      | nil => exact absurd hL (by simp [LogVals])
      | cons ε εs =>
        obtain ⟨hL1, hL2⟩ := hL
        simp only [plogSumVec, plogErrSum]
        rw [vecAdd_getD, vecAdd_getD]
        push_cast
        have h1 : (plogVec t.1 t.2 c L M).getD k 0 = plogCoefQ (shiftL c M t.1) (c - t.2) L k := by
          unfold plogVec
          exact getD_map_range _ _ _ (by omega)
        have h2 : (plogErr1 t.1 c ε M).getD k 0 = ε * qabs' ((shiftL c M t.1).getD k 0) := by
          unfold plogErr1
          exact getD_map_range _ _ _ (by omega)
        rw [h1, h2]
        push_cast
        have a1 := plogCoef_approx t.1 t.2 c L ε (hne t (by simp)) hL1 M k hk
        have a2 := ih Ls εs hL2 (fun s hs => hne s (by simp [hs])) k hk
        have e : plogSumTower (t :: ts) k (c : ℝ) / (k ! : ℝ) =
            mulTower (polyTow t.1) (logTower (t.2 : ℝ)) k (c : ℝ) / (k ! : ℝ) +
              plogSumTower ts k (c : ℝ) / (k ! : ℝ) := by
          simp only [plogSumTower, List.map_cons, List.sum_cons]; ring
        rw [e]
        push_cast at a1
        have key := (abs_add_le
          (mulTower (polyTow t.1) (logTower (t.2 : ℝ)) k (c : ℝ) / (k ! : ℝ) -
            ((plogCoefQ (shiftL c M t.1) (c - t.2) L k : ℚ) : ℝ))
          (plogSumTower ts k (c : ℝ) / (k ! : ℝ) -
            (((plogSumVec c M ts Ls).getD k 0 : ℚ) : ℝ))).trans (add_le_add a1 a2)
        refine le_trans (le_of_eq ?_) key
        congr 1
        ring

/-- Exact coefficients `[a_0, ..., a_M]` of the field at `c` (with the supplied logs); the entry
`a_0` omits the pole potential `F(c)` (supplied separately as `A0`).  The true coefficients
differ by at most `plogErrSum` (the log enclosure errors). -/
def fieldCoefs (fq : FieldQ) (Ls : List ℚ) (c : ℚ) (M : ℕ) : List ℚ :=
  vecAdd (shiftL c M fq.poly) (vecAdd (plogSumVec c M fq.plogs Ls) (poleVec fq.poles c M))

theorem fieldCoefs_approx (fq : FieldQ) (F : ℝ → ℝ) (Ls εs : List ℚ) (c : ℚ) (M : ℕ)
    (hL : LogVals c fq.plogs Ls εs) (hne : ∀ t ∈ fq.plogs, c - t.2 ≠ 0) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ M) :
    |fieldTower fq F k (c : ℝ) / (k ! : ℝ) - (((fieldCoefs fq Ls c M).getD k 0 : ℚ) : ℝ)| ≤
      (((plogErrSum c M fq.plogs εs).getD k 0 : ℚ) : ℝ) := by
  unfold fieldCoefs
  rw [vecAdd_getD, vecAdd_getD, poleVec_getD _ _ _ _ hk1 hk]
  push_cast
  rw [shiftL_spec c M fq.poly k hk]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [poleCoeff_spec fq.poles F c j]
  have h := plogSumVec_approx c M fq.plogs Ls εs hL hne (j + 1) hk
  have e : fieldTower fq F (j + 1) (c : ℝ) / ((j + 1)! : ℝ) =
      polyTow fq.poly (j + 1) (c : ℝ) / ((j + 1)! : ℝ) +
      plogSumTower fq.plogs (j + 1) (c : ℝ) / ((j + 1)! : ℝ) +
      poleTower fq.poles F (j + 1) (c : ℝ) / ((j + 1)! : ℝ) := by
    simp only [fieldTower]; ring
  rw [e]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ring

/-- `|T_k| + E_k ≤ b_k` for `k = k₀, k₀ + 1, ...`. -/
def absLeAllE (T E : List ℚ) : ℕ → List ℚ → Bool
  | _, [] => true
  | k, b :: bs => decide (qabs' (T.getD k 0) + E.getD k 0 ≤ b) && absLeAllE T E (k + 1) bs

theorem absLeAllE_spec (T E : List ℚ) : ∀ (Bl : List ℚ) (k : ℕ), absLeAllE T E k Bl = true →
    ∀ i < Bl.length, qabs' (T.getD (k + i) 0) + E.getD (k + i) 0 ≤ Bl.getD i 0 := by
  intro Bl
  induction Bl with
  | nil => intro k _ i hi; simp at hi
  | cons b bs ih =>
    intro k h i hi
    simp only [absLeAllE, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have := ih (k + 1) h.2 j (by simpa using hi)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      simpa using this

/-- **The Boolean cell checker for a general field** (exact coefficients through order
`|Bl| + 2`, the remainder bound `BM` coming from a block-level tail): the cell `[lo, hi]` avoids
the logarithmic singularities and the poles, `l1 ≤ a₁ ≤ u1`, `a₂ ≤ A2`, `|a_k| ≤ B_k` for
`3 ≤ k < M = |Bl| + 3`, and `tmUBQ ≤ T`; the coefficient tests are inflated by the log-enclosure
errors `εs`.  The remainder hypothesis `BM` is not checked here. -/
def fieldCellCheck (fq : FieldQ) (Ls εs : List ℚ) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ)
    (BM T : ℚ) : Bool :=
  let cs := fieldCoefs fq Ls ((lo + hi) / 2) (Bl.length + 2)
  let es := plogErrSum ((lo + hi) / 2) (Bl.length + 2) fq.plogs εs
  decide (lo ≤ hi) &&
  fq.plogs.all (fun t => decide (hi < t.2) || decide (t.2 < lo)) &&
  fq.poles.all (fun q => decide (0 < poleDist q lo hi)) &&
  decide (l1 ≤ cs.getD 1 0 - es.getD 1 0) && decide (cs.getD 1 0 + es.getD 1 0 ≤ u1) &&
  decide (cs.getD 2 0 + es.getD 2 0 ≤ A2) &&
  absLeAllE cs es 3 Bl && decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

/-- **Soundness of the general cell checker.**  `hBM` is the block-level tail:
`|f^{(M)}|/M! ≤ BM` on a block `[blo, bhi] ⊇ [lo, hi]` (see `blockTailCheck_sound`). -/
theorem fieldCellCheck_sound (fq : FieldQ) (F : ℝ → ℝ) (Ls εs : List ℚ)
    (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hchk : fieldCellCheck fq Ls εs lo hi A0 l1 u1 A2 Bl BM T = true)
    (hLs : LogVals ((lo + hi) / 2) fq.plogs Ls εs)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F ((fq.poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : fieldTower fq F 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |fieldTower fq F (Bl.length + 3) x| / ((Bl.length + 3)! : ℝ) ≤ (BM : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq F 0 x ≤ (T : ℝ) := by
  simp only [fieldCellCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hlh, hplog⟩, hpole⟩, hl1⟩, hu1⟩, hA2⟩, hB⟩, hT⟩ := hchk
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hdl' : ∀ q ∈ fq.poles, 0 < poleDist q lo hi := fun q hq => by simpa using hpole q hq
  have hnee : ∀ t ∈ fq.plogs, ∀ x ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      x ≠ (t.2 : ℝ) := by
    intro t ht x hx hxe
    rw [hcell] at hx
    rcases hplog t ht with h | h
    · have h' : (hi : ℝ) < (t.2 : ℝ) := by exact_mod_cast (by simpa using h : hi < t.2)
      linarith [hx.2]
    · have h' : (t.2 : ℝ) < (lo : ℝ) := by exact_mod_cast (by simpa using h : t.2 < lo)
      linarith [hx.1]
  have hnec : ∀ t ∈ fq.plogs, c - t.2 ≠ 0 := by
    intro t ht h
    rcases hplog t ht with h1 | h1
    · have : hi < t.2 := by simpa using h1
      simp only [hc] at h; linarith
    · have : t.2 < lo := by simpa using h1
      simp only [hc] at h; linarith
  have hnep : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), ∀ q ∈ fq.poles,
      (y : ℂ) ≠ q.pc := by
    intro y hy q hq heq
    rw [hcell] at hy
    have := poleDist_le_norm q lo hi y hy.1 hy.2
    rw [heq, sub_self, norm_zero] at this
    have h2 : (0 : ℝ) < ((poleDist q lo hi : ℚ) : ℝ) := by exact_mod_cast hdl' q hq
    linarith
  have hF' : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      HasDerivAt F ((fq.poles.map (fun q => qt q 0 y)).sum) y := by
    intro y hy; rw [hcell] at hy; exact hF y hy
  have hT0 := isTower_fieldTower fq F (c : ℝ) (r : ℝ) (Bl.length + 3) hnee hnep hF'
  have hspec := fun k hk1 hk =>
    fieldCoefs_approx fq F Ls εs c (Bl.length + 2) hLs hnec k hk1 hk
  have hcoef := absLeAllE_spec _ _ Bl 3 hB
  intro x hx
  rw [← hcell] at hx
  have key := taylor_cell_ub_rat (f := fieldTower fq F) (c := (c : ℝ)) (r := (r : ℝ)) Bl hT0
    (A0 := A0) (l1 := l1) (u1 := u1) (A2 := A2) (BM := BM) h0
    (by
      have h := abs_le.mp (hspec 1 le_rfl (by omega))
      have h1' : (l1 : ℝ) ≤ (((fieldCoefs fq Ls c (Bl.length + 2)).getD 1 0 : ℚ) : ℝ) -
          (((plogErrSum c (Bl.length + 2) fq.plogs εs).getD 1 0 : ℚ) : ℝ) := by
        exact_mod_cast hl1
      have h2 := h.1
      simp only [Nat.factorial_one, Nat.cast_one, div_one] at h2
      linarith)
    (by
      have h := abs_le.mp (hspec 1 le_rfl (by omega))
      have h1' : (((fieldCoefs fq Ls c (Bl.length + 2)).getD 1 0 : ℚ) : ℝ) +
          (((plogErrSum c (Bl.length + 2) fq.plogs εs).getD 1 0 : ℚ) : ℝ) ≤ (u1 : ℝ) := by
        exact_mod_cast hu1
      have h2 := h.2
      simp only [Nat.factorial_one, Nat.cast_one, div_one] at h2
      linarith)
    (by
      have h := abs_le.mp (hspec 2 (by omega) (by omega))
      have h2' : (((fieldCoefs fq Ls c (Bl.length + 2)).getD 2 0 : ℚ) : ℝ) +
          (((plogErrSum c (Bl.length + 2) fq.plogs εs).getD 2 0 : ℚ) : ℝ) ≤ (A2 : ℝ) := by
        exact_mod_cast hA2
      have h3 := h.2
      simp only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, mul_one, one_mul] at h3
      linarith)
    (by
      intro i hi'
      have h1 := hcoef i hi'
      have h2 := abs_le.mp (hspec (3 + i) (by omega) (by omega))
      have h3 : ((qabs' ((fieldCoefs fq Ls c (Bl.length + 2)).getD (3 + i) 0) : ℚ) : ℝ) +
          (((plogErrSum c (Bl.length + 2) fq.plogs εs).getD (3 + i) 0 : ℚ) : ℝ) ≤
          ((Bl.getD i 0 : ℚ) : ℝ) := by exact_mod_cast h1
      rw [qabs'_cast] at h3
      have e0 : |fieldTower fq F (3 + i) (c : ℝ)| / ((3 + i)! : ℝ) =
          |fieldTower fq F (3 + i) (c : ℝ) / ((3 + i)! : ℝ)| := by
        rw [abs_div, Nat.abs_cast]
      rw [e0, abs_le]
      constructor <;> linarith [h2.1, h2.2,
        le_abs_self (((fieldCoefs fq Ls c (Bl.length + 2)).getD (3 + i) 0 : ℚ) : ℝ),
        neg_abs_le (((fieldCoefs fq Ls c (Bl.length + 2)).getD (3 + i) 0 : ℚ) : ℝ)])
    (by
      intro y hy
      rw [hcell] at hy
      exact hBM y ⟨le_trans (by exact_mod_cast hb1) hy.1, le_trans hy.2 (by exact_mod_cast hb2)⟩)
    r (by simp [hr])
  have := key x hx
  refine this.trans ?_
  exact_mod_cast hT

/-! ### 12. Block-level tail of a field -/

/-- Block data of one `P_e log|x - e|` piece: bounds `Cb` of the Taylor coefficients of `P_e` at
the block centre, `Lb ≥ |log|x - e||` and `dm ≤ |x - e|` on the block. -/
structure PlogBlk where
  Cb : List ℚ
  Lb : ℚ
  dm : ℚ

/-- Boolean part of the block data of the pieces (aligned with the pieces). -/
def plogBlkOK (cb blo bhi : ℚ) : List (List ℚ × ℚ) → List PlogBlk → Bool
  | [], [] => true
  | t :: ts, b :: bs =>
    decide (t.1.length ≤ b.Cb.length) && absLeAll (shiftL cb b.Cb.length t.1) 0 b.Cb &&
    decide (0 < b.dm) && (decide (b.dm ≤ t.2 - bhi) || decide (b.dm ≤ blo - t.2)) &&
    plogBlkOK cb blo bhi ts bs
  | _, _ => false

/-- The logarithm bounds `|log |x - e|| ≤ Lb` on the block (real facts, aligned). -/
def LogBnd (blo bhi : ℚ) : List (List ℚ × ℚ) → List PlogBlk → Prop
  | [], [] => True
  | t :: ts, b :: bs =>
    (∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), |Real.log (|x - (t.2 : ℝ)|)| ≤ (b.Lb : ℝ)) ∧
      LogBnd blo bhi ts bs
  | _, _ => False

def plogTailSum (ρ : ℚ) (M : ℕ) : List (List ℚ × ℚ) → List PlogBlk → ℚ
  | t :: ts, b :: bs => plogTailQ ρ b.Cb b.Lb b.dm M + plogTailSum ρ M ts bs
  | _, _ => 0

/-- The shared tail bound: polynomial part + `Σ` pieces + poles (the poles directly over the block). -/
def blockTailQ (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk) : ℚ :=
  majQ ((bhi - blo) / 2) M 0 (CbP.drop M) + plogTailSum ((bhi - blo) / 2) M fq.plogs pb +
    poleRemQ fq.poles blo bhi M

/-- Boolean checker of the block tail: `|f^{(M)}|/M! ≤ BM` on `[blo, bhi]`. -/
def blockTailCheck (fq : FieldQ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ) (pb : List PlogBlk)
    (BM : ℚ) : Bool :=
  decide (blo ≤ bhi) && decide (1 ≤ M) &&
  decide (fq.poly.length ≤ CbP.length) &&
  absLeAll (shiftL ((blo + bhi) / 2) CbP.length fq.poly) 0 CbP &&
  plogBlkOK ((blo + bhi) / 2) blo bhi fq.plogs pb &&
  fq.poles.all (fun q => decide (0 < poleDist q blo bhi)) &&
  decide (blockTailQ fq blo bhi M CbP pb ≤ BM)

theorem plogSum_block (blo bhi : ℚ) (M : ℕ)
    (hcell : Icc ((((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ))
      ((((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ)) = Icc (blo : ℝ) (bhi : ℝ)) :
    ∀ (plogs : List (List ℚ × ℚ)) (pb : List PlogBlk),
      plogBlkOK ((blo + bhi) / 2) blo bhi plogs pb = true → LogBnd blo bhi plogs pb →
      ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
        |plogSumTower plogs M x| / (M ! : ℝ) ≤
          ((plogTailSum ((bhi - blo) / 2) M plogs pb : ℚ) : ℝ) := by
  intro plogs
  induction plogs with
  | nil =>
    intro pb hok hlog x _
    cases pb with
    | nil => simp [plogSumTower, plogTailSum]
    | cons => exact absurd hlog (by simp [LogBnd])
  | cons t ts ih =>
    intro pb hok hlog x hx
    cases pb with
    | nil => exact absurd hlog (by simp [LogBnd])
    | cons b bs =>
      simp only [plogBlkOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hok
      obtain ⟨⟨⟨⟨hlen, hchk⟩, hdm⟩, hside⟩, hrest⟩ := hok
      obtain ⟨hlog1, hlog2⟩ := hlog
      have hb := polyBnd_of_check t.1 ((blo + bhi) / 2) b.Cb hlen hchk
      have hx' : x ∈ Icc ((((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ))
          ((((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ)) := by rw [hcell]; exact hx
      have hd : ∀ y ∈ Icc ((((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ))
          ((((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ)),
          (b.dm : ℝ) ≤ |y - (t.2 : ℝ)| := by
        intro y hy
        rw [hcell] at hy
        rcases hside with h | h
        · have h' : (b.dm : ℝ) ≤ (t.2 : ℝ) - (bhi : ℝ) := by exact_mod_cast h
          rw [abs_sub_comm]
          exact h'.trans ((by linarith [hy.2] : (t.2 : ℝ) - bhi ≤ t.2 - y).trans (le_abs_self _))
        · have h' : (b.dm : ℝ) ≤ (blo : ℝ) - (t.2 : ℝ) := by exact_mod_cast h
          exact h'.trans ((by linarith [hy.1] : (blo : ℝ) - t.2 ≤ y - t.2).trans (le_abs_self _))
      have hlg : ∀ y ∈ Icc ((((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ))
          ((((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ)),
          |Real.log (|y - (t.2 : ℝ)|)| ≤ (b.Lb : ℝ) := by
        intro y hy; rw [hcell] at hy; exact hlog1 y hy
      have h1 := plog_block hb ((bhi - blo) / 2) rfl b.Lb b.dm hdm hlg hd M x hx'
      have h2 := ih bs hrest hlog2 x hx
      have e : plogSumTower (t :: ts) M x =
          mulTower (polyTow t.1) (logTower (t.2 : ℝ)) M x + plogSumTower ts M x := by
        simp [plogSumTower]
      rw [e, plogTailSum]
      push_cast
      calc |mulTower (polyTow t.1) (logTower (t.2 : ℝ)) M x + plogSumTower ts M x| / (M ! : ℝ)
          ≤ (|mulTower (polyTow t.1) (logTower (t.2 : ℝ)) M x| + |plogSumTower ts M x|) /
              (M ! : ℝ) :=
            div_le_div_of_nonneg_right (abs_add_le _ _) (by positivity)
        _ = |mulTower (polyTow t.1) (logTower (t.2 : ℝ)) M x| / (M ! : ℝ) +
              |plogSumTower ts M x| / (M ! : ℝ) := by rw [add_div]
        _ ≤ _ := add_le_add h1 h2

/-- **Soundness of the block-tail checker.**  On the whole block `[blo, bhi]` (a block of
neighbouring cells), `|f^{(M)}(x)|/M! ≤ BM` for the field tower `fieldTower fq F`, with no
per-cell data: the tail is computed once from the Taylor coefficients at the block centre. -/
theorem blockTailCheck_sound (fq : FieldQ) (F : ℝ → ℝ) (blo bhi : ℚ) (M : ℕ) (CbP : List ℚ)
    (pb : List PlogBlk) (BM : ℚ)
    (hchk : blockTailCheck fq blo bhi M CbP pb BM = true)
    (hlog : LogBnd blo bhi fq.plogs pb) :
    ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), |fieldTower fq F M x| / (M ! : ℝ) ≤ (BM : ℝ) := by
  simp only [blockTailCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hbb, hM1⟩, hlenP⟩, hchkP⟩, hplog⟩, hpole⟩, hBM⟩ := hchk
  have hcell : Icc ((((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ))
      ((((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ)) = Icc (blo : ℝ) (bhi : ℝ) := by
    have e1 : (((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ) = (blo : ℝ) := by
      push_cast; ring
    have e2 : (((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ) = (bhi : ℝ) := by
      push_cast; ring
    rw [e1, e2]
  have hdl' : ∀ q ∈ fq.poles, 0 < poleDist q blo bhi := fun q hq => by simpa using hpole q hq
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  intro x hx
  have hb := polyBnd_of_check fq.poly ((blo + bhi) / 2) CbP hlenP hchkP
  have hx' : x ∈ Icc ((((blo + bhi) / 2 : ℚ) : ℝ) - (((bhi - blo) / 2 : ℚ) : ℝ))
      ((((blo + bhi) / 2 : ℚ) : ℝ) + (((bhi - blo) / 2 : ℚ) : ℝ)) := by rw [hcell]; exact hx
  have hP := polyTow_block hb ((bhi - blo) / 2) rfl (m + 1) x hx'
  have hL := plogSum_block blo bhi (m + 1) hcell fq.plogs pb hplog hlog x hx
  have hPl := poleTower_rem fq.poles F blo bhi hdl' m x hx.1 hx.2
  have hfac : (0 : ℝ) < ((m + 1)! : ℝ) := by positivity
  have e : |fieldTower fq F (m + 1) x| ≤
      |polyTow fq.poly (m + 1) x| + |plogSumTower fq.plogs (m + 1) x| +
        |poleTower fq.poles F (m + 1) x| := by
    unfold fieldTower
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hQ : ((blockTailQ fq blo bhi (m + 1) CbP pb : ℚ) : ℝ) ≤ (BM : ℝ) := by
    exact_mod_cast hBM
  unfold blockTailQ at hQ
  push_cast at hQ
  calc |fieldTower fq F (m + 1) x| / ((m + 1)! : ℝ)
      ≤ (|polyTow fq.poly (m + 1) x| + |plogSumTower fq.plogs (m + 1) x| +
        |poleTower fq.poles F (m + 1) x|) / ((m + 1)! : ℝ) :=
        div_le_div_of_nonneg_right e hfac.le
    _ = |polyTow fq.poly (m + 1) x| / ((m + 1)! : ℝ) +
        |plogSumTower fq.plogs (m + 1) x| / ((m + 1)! : ℝ)
        + |poleTower fq.poles F (m + 1) x| / ((m + 1)! : ℝ) := by rw [add_div, add_div]
    _ ≤ _ := by linarith

/-! ### 13. Regression for the general field chain: `1 + 2x + log x ≤ 3.73` on `[3/4, 5/4]` -/

/-- One tiny field (`poly = 1 + 2x`, one piece `1 · log |x - 0|`, no poles) through the whole
chain `fieldCellCheck_sound` + `blockTailCheck_sound` (block = cell). -/
example : ∀ x ∈ Icc ((3 / 4 : ℚ) : ℝ) ((5 / 4 : ℚ) : ℝ),
    1 + 2 * x + Real.log x ≤ ((373 / 100 : ℚ) : ℝ) := by
  let fq : FieldQ := ⟨[1, 2], [([1], 0)], []⟩
  have hc : fieldCellCheck fq [0] [0] (3 / 4) (5 / 4) 3 3 3 (-1 / 2)
      [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (373 / 100) = true := by decide +kernel
  have hb : blockTailCheck fq (3 / 4) (5 / 4) 8 [3, 2] [⟨[1], 1 / 3, 3 / 4⟩] (5 / 4) = true := by
    decide +kernel
  have hlog : LogBnd (3 / 4) (5 / 4) fq.plogs [⟨[1], 1 / 3, 3 / 4⟩] := by
    refine ⟨fun x hx => ?_, trivial⟩
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
    simp only [Rat.cast_zero, sub_zero, abs_of_pos hx0]
    have h1 := Real.log_le_sub_one_of_pos hx0
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
    rw [Real.log_inv] at h2
    have h3 : x⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ hx0 (by norm_num)]
      have := hx.1; push_cast at this; linarith
    have h4 := hx.2; push_cast at h4
    rw [abs_le]
    constructor <;> push_cast <;> linarith
  have hLs : LogVals ((3 / 4 + 5 / 4) / 2) fq.plogs [0] [0] := by
    refine ⟨?_, trivial⟩
    simp
    norm_num
  have key := fieldCellCheck_sound fq (fun _ => 0) [0] [0] (3 / 4) (5 / 4) 3 3 3 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (373 / 100) hc hLs
    (fun x _ => by simpa [fq] using hasDerivAt_const x (0 : ℝ))
    (by simp [fq, fieldTower, polyTow, plogSumTower, poleTower, mulTower, logTower]; norm_num)
    (3 / 4) (5 / 4) le_rfl le_rfl
    (blockTailCheck_sound fq (fun _ => 0) (3 / 4) (5 / 4) 8 [3, 2] [⟨[1], 1 / 3, 3 / 4⟩] (5 / 4)
      hb hlog)
  intro x hx
  have h := key x hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (by norm_num) hx.1).ne'
  simp [fq, fieldTower, polyTow, plogSumTower, poleTower, mulTower, logTower] at h
  linarith

/-- Negative controls of the field checkers (`decide +kernel` returns `false`). -/
example : fieldCellCheck ⟨[1, 2], [([1], 0)], []⟩ [0] [0] (3 / 4) (5 / 4) 3 3 3 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (370 / 100) = false := by decide +kernel
example : fieldCellCheck ⟨[1, 2], [([1], 0)], []⟩ [0] [0] (3 / 4) (5 / 4) 3 3 3 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 6, 1 / 6, 1 / 7] (5 / 4) (373 / 100) = false := by decide +kernel
example : fieldCellCheck ⟨[1, 2], [([1], 0)], []⟩ [0] [0] (-1 / 4) (5 / 4) 3 3 3 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (373 / 100) = false := by decide +kernel
example : blockTailCheck ⟨[1, 2], [([1], 0)], []⟩ (3 / 4) (5 / 4) 8 [3, 2]
    [⟨[1], 1 / 3, 3 / 4⟩] (12 / 10) = false := by decide +kernel
example : blockTailCheck ⟨[1, 2], [([1], 0)], []⟩ (3 / 4) (5 / 4) 8 [3, 1]
    [⟨[1], 1 / 3, 3 / 4⟩] (5 / 4) = false := by decide +kernel
example : blockTailCheck ⟨[1, 2], [([1], 0)], []⟩ (3 / 4) (5 / 4) 8 [3, 2]
    [⟨[1], 1 / 3, 7 / 8⟩] (5 / 4) = false := by decide +kernel

/-- Power-table sharing agrees with `poleCoeff` on a concrete pole set (exact equality). -/
example : (poleVec [⟨1, 1 / 2, 3 / 5, 1 / 3⟩, ⟨-2, 0, 7 / 4, 0⟩] (1 / 5) 6) =
    [0] ++ (List.range 6).map (fun i =>
      poleCoeff [⟨1, 1 / 2, 3 / 5, 1 / 3⟩, ⟨-2, 0, 7 / 4, 0⟩] (1 / 5) (i + 1)) := by
  decide +kernel

/-! ### 14. Laurent terms: polynomials in `1/x` times `log |a x - b|` (cells away from `0`)

The dilated potentials `dilPot qs c = -(log|c| m(ℝ) + V(1/c))` are *Laurent* in `x`: `Σ_s a_s x^{-s}`
times `log|x|`, `log|a x - 1|`.  A Laurent term is a pair `(a, o)`: the coefficient list `a`
(`Σ_s a_s x^{-s}`) and a factor `o`, either `none` (the constant `1`) or `some (α, β)` (the factor
`log|α x - β|`).  Taylor coefficients at the centre `c ≠ 0` of `x^{-s}` are exact rationals
`(-1)^k C(s+k-1, k) c^{-(s+k)}`; the derivatives of `log|α x - β|` of order `≥ 1` are rational and
only its value is an enclosure.  Block bounds of `x^{-s}` need only a lower bound `mx ≤ |x|`. -/

/-- The tower of `x^{-s}`: `(-1)^j s (s+1) ⋯ (s+j-1) x^{-(s+j)}`. -/
noncomputable def monoInv (s j : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ j * (s.ascFactorial j : ℝ) * (x ^ (s + j))⁻¹

theorem hasDerivAt_monoInv (s j : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (monoInv s j) (monoInv s (j + 1) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y ^ (s + j))⁻¹)
      (-(((s + j : ℕ) : ℝ)) * (x ^ (s + j + 1))⁻¹) x := by
    have := (hasDerivAt_pow (s + j) x).inv (pow_ne_zero _ hx)
    refine this.congr_deriv ?_
    cases hn : s + j with
    | zero => simp
    | succ m =>
      have hxm : x ^ m ≠ 0 := pow_ne_zero _ hx
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  have h2 := h1.const_mul ((-1 : ℝ) ^ j * (s.ascFactorial j : ℝ))
  have hf : monoInv s j = fun y : ℝ => ((-1 : ℝ) ^ j * (s.ascFactorial j : ℝ)) * (y ^ (s + j))⁻¹ :=
    rfl
  rw [hf]
  refine h2.congr_deriv ?_
  have ha : (s.ascFactorial (j + 1) : ℝ) = ((s : ℝ) + j) * (s.ascFactorial j : ℝ) := by
    rw [show s.ascFactorial (j + 1) = (s + j) * s.ascFactorial j from rfl]
    push_cast; ring
  unfold monoInv
  rw [ha, show s + (j + 1) = s + j + 1 from rfl]
  push_cast
  ring

/-- Tower of `Σ_i a_i x^{-(s+i)}`. -/
noncomputable def zTowAux : ℕ → List ℚ → ℕ → ℝ → ℝ
  | _, [], _, _ => 0
  | s, a :: as, j, x => (a : ℝ) * monoInv s j x + zTowAux (s + 1) as j x

/-- Tower of the polynomial in `1/x`, `Σ_s a_s x^{-s}`. -/
noncomputable def zTow (a : List ℚ) : ℕ → ℝ → ℝ := zTowAux 0 a

theorem isTower_monoInv (s : ℕ) (c r : ℝ) (M : ℕ) (h0 : ∀ x ∈ Icc (c - r) (c + r), x ≠ 0) :
    IsTower (monoInv s) c r M where
  cont j _ y hy := (hasDerivAt_monoInv s j y (h0 y hy)).continuousAt.continuousWithinAt
  der j _ y hy := hasDerivAt_monoInv s j y (h0 y ⟨hy.1.le, hy.2.le⟩)

theorem isTower_zTowAux (c r : ℝ) (M : ℕ) (h0 : ∀ x ∈ Icc (c - r) (c + r), x ≠ 0) :
    ∀ (a : List ℚ) (s : ℕ), IsTower (zTowAux s a) c r M := by
  intro a
  induction a with
  | nil =>
    intro s
    have h : zTowAux s [] = fun _ _ => 0 := by funext j x; simp [zTowAux]
    rw [h]
    exact ⟨fun j _ => continuousOn_const, fun j _ x _ => hasDerivAt_const x 0⟩
  | cons a as ih =>
    intro s
    have h : zTowAux s (a :: as) = fun j x => (a : ℝ) * monoInv s j x + zTowAux (s + 1) as j x := by
      funext j x; simp [zTowAux]
    rw [h]
    exact ((isTower_monoInv s c r M h0).smul (a : ℝ)).add (ih (s + 1))

theorem isTower_zTow (a : List ℚ) (c r : ℝ) (M : ℕ) (h0 : ∀ x ∈ Icc (c - r) (c + r), x ≠ 0) :
    IsTower (zTow a) c r M := isTower_zTowAux c r M h0 a 0

/-- Tower of `log |α x - β|`. -/
noncomputable def linLogTower (a b : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.log |a * x - b|
  | m + 1 => fun x => (-1 : ℝ) ^ m * (m ! : ℝ) * a ^ (m + 1) / (a * x - b) ^ (m + 1)

/-- Tower of the constant `1`. -/
noncomputable def oneTower : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | _ + 1 => fun _ => 0

/-- The factor of a Laurent term: `none` is the constant `1`, `some (α, β)` is `log |α x - β|`. -/
noncomputable def lfTower : Option (ℚ × ℚ) → ℕ → ℝ → ℝ
  | none => oneTower
  | some ab => linLogTower (ab.1 : ℝ) (ab.2 : ℝ)

theorem hasDerivAt_linLogTower (a b : ℝ) (j : ℕ) (x : ℝ) (hx : a * x - b ≠ 0) :
    HasDerivAt (linLogTower a b j) (linLogTower a b (j + 1) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => a * y - b) a x := by
    have := ((hasDerivAt_id' x).const_mul a).sub_const b
    simpa using this
  cases j with
  | zero =>
    have h2 := h1.log hx
    have hf : linLogTower a b 0 = fun y : ℝ => Real.log (a * y - b) := by
      funext y; exact Real.log_abs _
    rw [hf]
    refine h2.congr_deriv ?_
    simp [linLogTower]
  | succ m =>
    have h3 : HasDerivAt (fun y : ℝ => (a * y - b) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (a * x - b) ^ m * a) x := h1.pow (m + 1)
    have h4 := (hasDerivAt_const x ((-1 : ℝ) ^ m * (m ! : ℝ) * a ^ (m + 1))).div h3
      (pow_ne_zero _ hx)
    simp only [linLogTower]
    refine h4.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have hm : (m ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem isTower_lfTower (o : Option (ℚ × ℚ)) (c r : ℝ) (M : ℕ)
    (hne : ∀ ab, o = some ab → ∀ x ∈ Icc (c - r) (c + r), (ab.1 : ℝ) * x - (ab.2 : ℝ) ≠ 0) :
    IsTower (lfTower o) c r M := by
  cases o with
  | none =>
    have h : lfTower none = oneTower := rfl
    rw [h]
    refine ⟨fun j _ => ?_, fun j _ x _ => ?_⟩
    · cases j <;> simp [oneTower] <;> exact continuousOn_const
    · cases j <;> simp [oneTower] <;> exact hasDerivAt_const x _
  | some ab =>
    exact ⟨fun j _ y hy => (hasDerivAt_linLogTower _ _ j y (hne ab rfl y hy)).continuousAt.continuousWithinAt,
      fun j _ y hy => hasDerivAt_linLogTower _ _ j y (hne ab rfl y ⟨hy.1.le, hy.2.le⟩)⟩

/-- A Laurent term: the `1/x`-polynomial coefficients and the factor. -/
abbrev LTerm := List ℚ × Option (ℚ × ℚ)

/-- The tower of a list of Laurent terms. -/
noncomputable def lfieldTower (ts : List LTerm) (j : ℕ) (x : ℝ) : ℝ :=
  (ts.map (fun t => mulTower (zTow t.1) (lfTower t.2) j x)).sum

theorem isTower_lfieldTower (ts : List LTerm) (c r : ℝ) (M : ℕ)
    (h0 : ∀ x ∈ Icc (c - r) (c + r), x ≠ 0)
    (hne : ∀ t ∈ ts, ∀ ab, t.2 = some ab → ∀ x ∈ Icc (c - r) (c + r),
      (ab.1 : ℝ) * x - (ab.2 : ℝ) ≠ 0) :
    IsTower (lfieldTower ts) c r M := by
  induction ts with
  | nil =>
    have h : lfieldTower [] = fun _ _ => 0 := by funext j x; simp [lfieldTower]
    rw [h]
    exact ⟨fun j _ => continuousOn_const, fun j _ x _ => hasDerivAt_const x 0⟩
  | cons t ts ih =>
    have h : lfieldTower (t :: ts) = fun j x =>
        mulTower (zTow t.1) (lfTower t.2) j x + lfieldTower ts j x := by
      funext j x; simp [lfieldTower]
    rw [h]
    exact ((isTower_zTow t.1 c r M h0).mul
      (isTower_lfTower t.2 c r M (hne t (by simp)))).add
      (ih (fun s hs => hne s (by simp [hs])))

/-! Exact coefficients. -/

/-- `Σ_{i<n} u_i v_{k-i}`. -/
def convQ (u v : ℕ → ℚ) (k : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => convQ u v k n + u n * v (k - n)

theorem convQ_cast (u v : ℕ → ℚ) (k n : ℕ) :
    ((convQ u v k n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((u i : ℚ) : ℝ) * ((v (k - i) : ℚ) : ℝ) := by
  induction n with
  | zero => simp [convQ]
  | succ n ih => rw [convQ, Finset.sum_range_succ, ← ih]; push_cast; rfl

/-- Normalised Taylor coefficient `k` at `c` of `Σ_i a_i x^{-(s+i)}`. -/
def zHatAux : ℕ → List ℚ → ℚ → ℕ → ℚ
  | _, [], _, _ => 0
  | s, a :: as, c, k =>
    a * ((-1) ^ k * (s.ascFactorial k : ℚ) / ((k ! : ℕ) : ℚ) / c ^ (s + k)) +
      zHatAux (s + 1) as c k

def zHat (a : List ℚ) : ℚ → ℕ → ℚ := zHatAux 0 a

theorem zTowAux_coef (c : ℚ) (hc : c ≠ 0) :
    ∀ (a : List ℚ) (s k : ℕ), zTowAux s a k (c : ℝ) / (k ! : ℝ) = ((zHatAux s a c k : ℚ) : ℝ) := by
  intro a
  induction a with
  | nil => intro s k; simp [zTowAux, zHatAux]
  | cons a as ih =>
    intro s k
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    rw [zTowAux, add_div, ih (s + 1) k, zHatAux]
    push_cast
    unfold monoInv
    have hk : (k ! : ℝ) ≠ 0 := by positivity
    field_simp

/-- Normalised coefficient `m` of the factor at `c`; the value (`m = 0`) of `log |α x - β|` is the
supplied `L`. -/
def lfHat : Option (ℚ × ℚ) → ℚ → ℚ → ℕ → ℚ
  | none, _, _, 0 => 1
  | none, _, _, _ + 1 => 0
  | some _, _, L, 0 => L
  | some ab, c, _, m + 1 =>
    (-1) ^ m * ab.1 ^ (m + 1) / (((m : ℚ) + 1) * (ab.1 * c - ab.2) ^ (m + 1))

theorem lfTower_coef (o : Option (ℚ × ℚ)) (c L : ℚ)
    (hne : ∀ ab, o = some ab → ab.1 * c - ab.2 ≠ 0) (m : ℕ) :
    lfTower o (m + 1) (c : ℝ) / ((m + 1)! : ℝ) = ((lfHat o c L (m + 1) : ℚ) : ℝ) := by
  cases o with
  | none => simp [lfTower, oneTower, lfHat]
  | some ab =>
    have h : (ab.1 : ℝ) * (c : ℝ) - (ab.2 : ℝ) ≠ 0 := by
      have := hne ab rfl
      exact_mod_cast this
    simp only [lfTower, linLogTower, lfHat]
    rw [Nat.factorial_succ]
    push_cast
    have hm : (m ! : ℝ) ≠ 0 := by positivity
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp

/-- Error multiplier of the enclosure of the factor value. -/
def lEps : Option (ℚ × ℚ) → ℚ → ℚ
  | none, _ => 0
  | some _, ε => ε

/-- Coefficient `k` of one Laurent term at `c`. -/
def lTermCoef (t : LTerm) (c L : ℚ) (k : ℕ) : ℚ :=
  convQ (zHat t.1 c) (lfHat t.2 c L) k (k + 1)

theorem lTerm_approx (t : LTerm) (c : ℚ) (hc : c ≠ 0) (L ε : ℚ)
    (hne : ∀ ab, t.2 = some ab → ab.1 * c - ab.2 ≠ 0)
    (hL : ∀ ab, t.2 = some ab → |(L : ℝ) - Real.log (|(ab.1 : ℝ) * (c : ℝ) - (ab.2 : ℝ)|)| ≤ (ε : ℝ))
    (k : ℕ) :
    |mulTower (zTow t.1) (lfTower t.2) k (c : ℝ) / (k ! : ℝ) - ((lTermCoef t c L k : ℚ) : ℝ)| ≤
      ((lEps t.2 ε * qabs' (zHat t.1 c k) : ℚ) : ℝ) := by
  rw [mulTower_div, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (zTow t.1 i (c : ℝ) / (i ! : ℝ)) * (lfTower t.2 j (c : ℝ) / (j ! : ℝ))) k]
  unfold lTermCoef
  rw [convQ_cast, Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum : ∑ i ∈ Finset.range k, (zTow t.1 i (c : ℝ) / (i ! : ℝ)) *
        (lfTower t.2 (k - i) (c : ℝ) / ((k - i)! : ℝ)) =
      ∑ i ∈ Finset.range k, ((zHat t.1 c i : ℚ) : ℝ) * ((lfHat t.2 c L (k - i) : ℚ) : ℝ) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
    rw [hm, lfTower_coef t.2 c L hne m]
    congr 1
    exact zTowAux_coef c hc t.1 0 i
  rw [hsum]
  have hk : zTow t.1 k (c : ℝ) / (k ! : ℝ) = ((zHat t.1 c k : ℚ) : ℝ) := zTowAux_coef c hc t.1 0 k
  rw [hk, Nat.sub_self]
  have e : ∑ i ∈ Finset.range k, ((zHat t.1 c i : ℚ) : ℝ) * ((lfHat t.2 c L (k - i) : ℚ) : ℝ) +
      ((zHat t.1 c k : ℚ) : ℝ) * (lfTower t.2 0 (c : ℝ) / ((0 : ℕ)! : ℝ)) -
      (∑ i ∈ Finset.range k, ((zHat t.1 c i : ℚ) : ℝ) * ((lfHat t.2 c L (k - i) : ℚ) : ℝ) +
        ((zHat t.1 c k : ℚ) : ℝ) * ((lfHat t.2 c L 0 : ℚ) : ℝ)) =
      ((zHat t.1 c k : ℚ) : ℝ) * (lfTower t.2 0 (c : ℝ) / ((0 : ℕ)! : ℝ) -
        ((lfHat t.2 c L 0 : ℚ) : ℝ)) := by ring
  rw [e, abs_mul]
  push_cast
  rw [qabs'_cast, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rcases ho : t.2 with _ | ab
  · simp [ho, lEps, lfTower, oneTower, lfHat]
  · have h1 := hL ab ho
    simp only [ho, lEps, lfTower, linLogTower, lfHat, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [abs_sub_comm]
    exact h1


/-- Coefficient `k` of a list of Laurent terms (the enclosures `(L, ε)` aligned with the terms). -/
def lCoef : List LTerm → List (ℚ × ℚ) → ℚ → ℕ → ℚ
  | t :: ts, v :: vs, c, k => lTermCoef t c v.1 k + lCoef ts vs c k
  | _, _, _, _ => 0

/-- Coefficient error of a list of Laurent terms. -/
def lErr : List LTerm → List (ℚ × ℚ) → ℚ → ℕ → ℚ
  | t :: ts, v :: vs, c, k => lEps t.2 v.2 * qabs' (zHat t.1 c k) + lErr ts vs c k
  | _, _, _, _ => 0

/-- The supplied `(L, ε)` enclose `log |α c - β|` for the logarithmic factors (aligned). -/
def LLogVals (c : ℚ) : List LTerm → List (ℚ × ℚ) → Prop
  | [], [] => True
  | t :: ts, v :: vs =>
    (∀ ab, t.2 = some ab →
      |(v.1 : ℝ) - Real.log (|(ab.1 : ℝ) * (c : ℝ) - (ab.2 : ℝ)|)| ≤ (v.2 : ℝ)) ∧
      LLogVals c ts vs
  | _, _ => False

theorem lfield_approx (c : ℚ) (hc : c ≠ 0) : ∀ (ts : List LTerm) (vs : List (ℚ × ℚ)),
    LLogVals c ts vs → (∀ t ∈ ts, ∀ ab, t.2 = some ab → ab.1 * c - ab.2 ≠ 0) → ∀ k : ℕ,
    |lfieldTower ts k (c : ℝ) / (k ! : ℝ) - ((lCoef ts vs c k : ℚ) : ℝ)| ≤
      ((lErr ts vs c k : ℚ) : ℝ) := by
  intro ts
  induction ts with
  | nil =>
    intro vs hv _ k
    cases vs with
    | nil => simp [lfieldTower, lCoef, lErr]
    | cons => exact absurd hv (by simp [LLogVals])
  | cons t ts ih =>
    intro vs hv hne k
    cases vs with
    | nil => exact absurd hv (by simp [LLogVals])
    | cons v vs =>
      obtain ⟨hv1, hv2⟩ := hv
      have a1 := lTerm_approx t c hc v.1 v.2 (hne t (by simp)) hv1 k
      have a2 := ih vs hv2 (fun s hs => hne s (by simp [hs])) k
      have e : lfieldTower (t :: ts) k (c : ℝ) / (k ! : ℝ) =
          mulTower (zTow t.1) (lfTower t.2) k (c : ℝ) / (k ! : ℝ) +
            lfieldTower ts k (c : ℝ) / (k ! : ℝ) := by
        simp only [lfieldTower, List.map_cons, List.sum_cons]; ring
      rw [e]
      simp only [lCoef, lErr]
      push_cast
      push_cast at a1
      have key := (abs_add_le
        (mulTower (zTow t.1) (lfTower t.2) k (c : ℝ) / (k ! : ℝ) -
          ((lTermCoef t c v.1 k : ℚ) : ℝ))
        (lfieldTower ts k (c : ℝ) / (k ! : ℝ) - ((lCoef ts vs c k : ℚ) : ℝ))).trans
        (add_le_add a1 a2)
      refine le_trans (le_of_eq ?_) key
      congr 1
      push_cast
      ring

/-! Block bounds: only a lower bound `mx ≤ |x|` and a lower bound `dm ≤ |α x - β|` are used. -/

/-- Bound vector of `Σ_i a_i x^{-(s+i)}` (order `j`) on a block with `mx ≤ |x|`. -/
def zBndAux : ℕ → List ℚ → ℚ → ℕ → ℚ
  | _, [], _, _ => 0
  | s, a :: as, mx, j =>
    qabs' a * ((s.ascFactorial j : ℚ) / ((j ! : ℕ) : ℚ)) / mx ^ (s + j) + zBndAux (s + 1) as mx j

def zBnd (a : List ℚ) : ℚ → ℕ → ℚ := zBndAux 0 a

theorem monoInv_block (mx : ℚ) (hmx : 0 < mx) (x : ℝ) (hx : (mx : ℝ) ≤ |x|) (s j : ℕ) :
    |monoInv s j x| / (j ! : ℝ) ≤
      (s.ascFactorial j : ℝ) / (j ! : ℝ) / (mx : ℝ) ^ (s + j) := by
  have hmx' : (0 : ℝ) < mx := by exact_mod_cast hmx
  have hxpos : 0 < |x| := lt_of_lt_of_le hmx' hx
  unfold monoInv
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, abs_inv,
    abs_pow]
  have hj : (0 : ℝ) < (j ! : ℝ) := by positivity
  calc (s.ascFactorial j : ℝ) * (|x| ^ (s + j))⁻¹ / (j ! : ℝ)
      = ((s.ascFactorial j : ℝ) / (j ! : ℝ)) * (|x| ^ (s + j))⁻¹ := by ring
    _ ≤ ((s.ascFactorial j : ℝ) / (j ! : ℝ)) * ((mx : ℝ) ^ (s + j))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_anti₀ (pow_pos hmx' _) (pow_le_pow_left₀ hmx'.le hx _)
    _ = _ := by ring

theorem zTowAux_block (mx : ℚ) (hmx : 0 < mx) (x : ℝ) (hx : (mx : ℝ) ≤ |x|) (j : ℕ) :
    ∀ (a : List ℚ) (s : ℕ), |zTowAux s a j x| / (j ! : ℝ) ≤ ((zBndAux s a mx j : ℚ) : ℝ) := by
  intro a
  induction a with
  | nil => intro s; simp [zTowAux, zBndAux]
  | cons a as ih =>
    intro s
    have hj : (0 : ℝ) < (j ! : ℝ) := by positivity
    have h1 := monoInv_block mx hmx x hx s j
    have h2 := ih (s + 1)
    simp only [zTowAux, zBndAux]
    push_cast
    rw [qabs'_cast]
    calc |(a : ℝ) * monoInv s j x + zTowAux (s + 1) as j x| / (j ! : ℝ)
        ≤ (|(a : ℝ)| * |monoInv s j x| + |zTowAux (s + 1) as j x|) / (j ! : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hj.le
          rw [← abs_mul]; exact abs_add_le _ _
      _ = |(a : ℝ)| * (|monoInv s j x| / (j ! : ℝ)) + |zTowAux (s + 1) as j x| / (j ! : ℝ) := by
          rw [add_div]; ring
      _ ≤ |(a : ℝ)| * ((s.ascFactorial j : ℝ) / (j ! : ℝ) / (mx : ℝ) ^ (s + j)) +
          ((zBndAux (s + 1) as mx j : ℚ) : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
      _ = _ := by
          push_cast
          ring

/-- Bound vector of the factor `lfTower o` on a block: `|log |α x - β|| ≤ Lb`, `|α x - β| ≥ dm`. -/
def lfBnd : Option (ℚ × ℚ) → ℚ → ℚ → ℕ → ℚ
  | none, _, _, 0 => 1
  | none, _, _, _ + 1 => 0
  | some _, Lb, _, 0 => Lb
  | some ab, _, dm, m + 1 => qabs' ab.1 ^ (m + 1) / (((m : ℚ) + 1) * dm ^ (m + 1))

theorem lfTower_bnd (o : Option (ℚ × ℚ)) (Lb dm : ℚ) (x : ℝ) (hdm : ∀ ab, o = some ab → 0 < dm)
    (hLb : ∀ ab, o = some ab → |Real.log (|(ab.1 : ℝ) * x - (ab.2 : ℝ)|)| ≤ (Lb : ℝ))
    (hd : ∀ ab, o = some ab → (dm : ℝ) ≤ |(ab.1 : ℝ) * x - (ab.2 : ℝ)|) (m : ℕ) :
    |lfTower o m x| / (m ! : ℝ) ≤ ((lfBnd o Lb dm m : ℚ) : ℝ) := by
  cases o with
  | none =>
    cases m with
    | zero => simp [lfTower, oneTower, lfBnd]
    | succ m => simp [lfTower, oneTower, lfBnd]
  | some ab =>
    cases m with
    | zero => simpa [lfTower, linLogTower, lfBnd] using hLb ab rfl
    | succ m =>
      have hdm' : (0 : ℝ) < dm := by exact_mod_cast hdm ab rfl
      have hd' := hd ab rfl
      have hpos : 0 < |(ab.1 : ℝ) * x - (ab.2 : ℝ)| := lt_of_lt_of_le hdm' hd'
      simp only [lfTower, linLogTower, lfBnd]
      simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        Nat.abs_cast, Nat.factorial_succ]
      push_cast
      rw [qabs'_cast]
      have hm : (m ! : ℝ) ≠ 0 := by positivity
      have e1 : (m ! : ℝ) * |(ab.1 : ℝ)| ^ (m + 1) / |(ab.1 : ℝ) * x - (ab.2 : ℝ)| ^ (m + 1) /
          (((m : ℝ) + 1) * (m ! : ℝ)) =
          |(ab.1 : ℝ)| ^ (m + 1) / (((m : ℝ) + 1) * |(ab.1 : ℝ) * x - (ab.2 : ℝ)| ^ (m + 1)) := by
        field_simp
      rw [e1]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdm'.le hd' _) (by positivity)

/-- Block tail of one Laurent term. -/
def lTermTail (t : LTerm) (mx Lb dm : ℚ) (M : ℕ) : ℚ :=
  convQ (zBnd t.1 mx) (lfBnd t.2 Lb dm) M (M + 1)

theorem lTerm_block (t : LTerm) (mx Lb dm : ℚ) (hmx : 0 < mx) (hdm : ∀ ab, t.2 = some ab → 0 < dm) (x : ℝ)
    (hx : (mx : ℝ) ≤ |x|)
    (hLb : ∀ ab, t.2 = some ab → |Real.log (|(ab.1 : ℝ) * x - (ab.2 : ℝ)|)| ≤ (Lb : ℝ))
    (hd : ∀ ab, t.2 = some ab → (dm : ℝ) ≤ |(ab.1 : ℝ) * x - (ab.2 : ℝ)|) (M : ℕ) :
    |mulTower (zTow t.1) (lfTower t.2) M x| / (M ! : ℝ) ≤ ((lTermTail t mx Lb dm M : ℚ) : ℝ) := by
  refine (mulTower_block_bound (U := fun i => ((zBnd t.1 mx i : ℚ) : ℝ))
    (V := fun j => ((lfBnd t.2 Lb dm j : ℚ) : ℝ))
    (fun i _ => zTowAux_block mx hmx x hx i t.1 0)
    (fun j _ => lfTower_bnd t.2 Lb dm x hdm hLb hd j)).trans (le_of_eq ?_)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => ((zBnd t.1 mx i : ℚ) : ℝ) * ((lfBnd t.2 Lb dm j : ℚ) : ℝ)) M]
  unfold lTermTail
  rw [convQ_cast]

/-- Linear forms on a block. -/
theorem lin_ge (a b lo hi x d : ℝ) (hx1 : lo ≤ x) (hx2 : x ≤ hi) (h1 : d ≤ a * lo - b)
    (h2 : d ≤ a * hi - b) : d ≤ a * x - b := by
  rcases le_total 0 a with ha | ha
  · nlinarith [mul_le_mul_of_nonneg_left hx1 ha]
  · nlinarith [mul_le_mul_of_nonpos_left hx2 ha]

theorem lin_le (a b lo hi x d : ℝ) (hx1 : lo ≤ x) (hx2 : x ≤ hi) (h1 : a * lo - b ≤ d)
    (h2 : a * hi - b ≤ d) : a * x - b ≤ d := by
  rcases le_total 0 a with ha | ha
  · nlinarith [mul_le_mul_of_nonneg_left hx2 ha]
  · nlinarith [mul_le_mul_of_nonpos_left hx1 ha]

theorem lin_pos (a b lo hi x : ℝ) (hx1 : lo ≤ x) (hx2 : x ≤ hi) (h1 : 0 < a * lo - b)
    (h2 : 0 < a * hi - b) : 0 < a * x - b := by
  rcases le_total 0 a with ha | ha
  · nlinarith [mul_le_mul_of_nonneg_left hx1 ha]
  · nlinarith [mul_le_mul_of_nonpos_left hx2 ha]

theorem lin_neg (a b lo hi x : ℝ) (hx1 : lo ≤ x) (hx2 : x ≤ hi) (h1 : a * lo - b < 0)
    (h2 : a * hi - b < 0) : a * x - b < 0 := by
  rcases le_total 0 a with ha | ha
  · nlinarith [mul_le_mul_of_nonneg_left hx2 ha]
  · nlinarith [mul_le_mul_of_nonpos_left hx1 ha]

/-- Boolean block condition of a factor: `|α x - β| ≥ dm > 0` on `[blo, bhi]`. -/
def linOK (blo bhi dm : ℚ) : Option (ℚ × ℚ) → Bool
  | none => true
  | some ab =>
    decide (0 < dm) &&
      ((decide (dm ≤ ab.1 * blo - ab.2) && decide (dm ≤ ab.1 * bhi - ab.2)) ||
        (decide (ab.1 * blo - ab.2 ≤ -dm) && decide (ab.1 * bhi - ab.2 ≤ -dm)))

theorem linOK_sound (blo bhi dm : ℚ) (o : Option (ℚ × ℚ)) (h : linOK blo bhi dm o = true) :
    ∀ ab, o = some ab → 0 < dm ∧ ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      (dm : ℝ) ≤ |(ab.1 : ℝ) * x - (ab.2 : ℝ)| := by
  intro ab hab
  subst hab
  simp only [linOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hdm, h1 | h1⟩ := h
  · refine ⟨hdm, fun x hx => ?_⟩
    have a1 : (dm : ℝ) ≤ (ab.1 : ℝ) * blo - ab.2 := by exact_mod_cast h1.1
    have a2 : (dm : ℝ) ≤ (ab.1 : ℝ) * bhi - ab.2 := by exact_mod_cast h1.2
    exact (lin_ge _ _ _ _ x _ hx.1 hx.2 a1 a2).trans (le_abs_self _)
  · refine ⟨hdm, fun x hx => ?_⟩
    have a1 : (ab.1 : ℝ) * blo - ab.2 ≤ -(dm : ℝ) := by exact_mod_cast h1.1
    have a2 : (ab.1 : ℝ) * bhi - ab.2 ≤ -(dm : ℝ) := by exact_mod_cast h1.2
    have := lin_le _ _ _ _ x _ hx.1 hx.2 a1 a2
    exact (by linarith : (dm : ℝ) ≤ -((ab.1 : ℝ) * x - ab.2)).trans (neg_le_abs _)

/-- Block data of a Laurent term: `Lb ≥ |log |α x - β||`, `dm ≤ |α x - β|`. -/
structure LBlk where
  Lb : ℚ
  dm : ℚ

def lBlkOK (blo bhi : ℚ) : List LTerm → List LBlk → Bool
  | [], [] => true
  | t :: ts, b :: bs => linOK blo bhi b.dm t.2 && lBlkOK blo bhi ts bs
  | _, _ => false

def LLogBnd (blo bhi : ℚ) : List LTerm → List LBlk → Prop
  | [], [] => True
  | t :: ts, b :: bs =>
    (∀ ab, t.2 = some ab → ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |Real.log (|(ab.1 : ℝ) * x - (ab.2 : ℝ)|)| ≤ (b.Lb : ℝ)) ∧ LLogBnd blo bhi ts bs
  | _, _ => False

def lTailSum (mx : ℚ) (M : ℕ) : List LTerm → List LBlk → ℚ
  | t :: ts, b :: bs => lTermTail t mx b.Lb b.dm M + lTailSum mx M ts bs
  | _, _ => 0

/-- **Block tail checker of the Laurent part**: `|(Σ terms)^{(M)}|/M! ≤ BM` on `[blo, bhi]`, where
`mx ≤ |x|` there. -/
def lTailCheck (blo bhi mx : ℚ) (M : ℕ) (ts : List LTerm) (bs : List LBlk) (BM : ℚ) : Bool :=
  decide (blo ≤ bhi) && decide (0 < mx) && (decide (mx ≤ blo) || decide (bhi ≤ -mx)) &&
    lBlkOK blo bhi ts bs && decide (lTailSum mx M ts bs ≤ BM)

theorem lTail_block (blo bhi mx : ℚ) (M : ℕ) (hmx : 0 < mx)
    (hside : (mx ≤ blo) ∨ (bhi ≤ -mx)) :
    ∀ (ts : List LTerm) (bs : List LBlk), lBlkOK blo bhi ts bs = true → LLogBnd blo bhi ts bs →
      ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
        |lfieldTower ts M x| / (M ! : ℝ) ≤ ((lTailSum mx M ts bs : ℚ) : ℝ) := by
  have hx : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), (mx : ℝ) ≤ |x| := by
    intro x hx
    rcases hside with h | h
    · have : (mx : ℝ) ≤ blo := by exact_mod_cast h
      exact (this.trans hx.1).trans (le_abs_self _)
    · have : (bhi : ℝ) ≤ -(mx : ℝ) := by exact_mod_cast h
      exact (by linarith [hx.2] : (mx : ℝ) ≤ -x).trans (neg_le_abs _)
  intro ts
  induction ts with
  | nil =>
    intro bs hok hlog x _
    cases bs with
    | nil => simp [lfieldTower, lTailSum]
    | cons => exact absurd hlog (by simp [LLogBnd])
  | cons t ts ih =>
    intro bs hok hlog x hxI
    cases bs with
    | nil => exact absurd hlog (by simp [LLogBnd])
    | cons b bs =>
      simp only [lBlkOK, Bool.and_eq_true] at hok
      obtain ⟨hl1, hl2⟩ := hok
      obtain ⟨hg1, hg2⟩ := hlog
      have hdm : ∀ ab, t.2 = some ab → 0 < b.dm :=
        fun ab hab => (linOK_sound blo bhi b.dm t.2 hl1 ab hab).1
      have hd : ∀ ab, t.2 = some ab →
          (b.dm : ℝ) ≤ |(ab.1 : ℝ) * x - (ab.2 : ℝ)| :=
        fun ab hab => (linOK_sound blo bhi b.dm t.2 hl1 ab hab).2 x hxI
      have hLb : ∀ ab, t.2 = some ab →
          |Real.log (|(ab.1 : ℝ) * x - (ab.2 : ℝ)|)| ≤ (b.Lb : ℝ) :=
        fun ab hab => hg1 ab hab x hxI
      have h1 := lTerm_block t mx b.Lb b.dm hmx hdm x (hx x hxI) hLb hd M
      have h2 := ih bs hl2 hg2 x hxI
      have e : lfieldTower (t :: ts) M x =
          mulTower (zTow t.1) (lfTower t.2) M x + lfieldTower ts M x := by
        simp [lfieldTower]
      rw [e, lTailSum]
      push_cast
      calc |mulTower (zTow t.1) (lfTower t.2) M x + lfieldTower ts M x| / (M ! : ℝ)
          ≤ (|mulTower (zTow t.1) (lfTower t.2) M x| + |lfieldTower ts M x|) / (M ! : ℝ) :=
            div_le_div_of_nonneg_right (abs_add_le _ _) (by positivity)
        _ = |mulTower (zTow t.1) (lfTower t.2) M x| / (M ! : ℝ) +
              |lfieldTower ts M x| / (M ! : ℝ) := by rw [add_div]
        _ ≤ _ := add_le_add h1 h2

theorem lTailCheck_sound (blo bhi mx : ℚ) (M : ℕ) (ts : List LTerm) (bs : List LBlk) (BM : ℚ)
    (hchk : lTailCheck blo bhi mx M ts bs BM = true) (hlog : LLogBnd blo bhi ts bs) :
    ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ), |lfieldTower ts M x| / (M ! : ℝ) ≤ (BM : ℝ) := by
  simp only [lTailCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨_, hmx⟩, hside⟩, hok⟩, hBM⟩ := hchk
  intro x hx
  have := lTail_block blo bhi mx M hmx hside ts bs hok hlog x hx
  exact this.trans (by exact_mod_cast hBM)

/-- Cell condition for the Laurent part: the cell avoids `0` and every `α x = β`. -/
def lAvoidOne (lo hi : ℚ) : Option (ℚ × ℚ) → Bool
  | none => true
  | some ab =>
    (decide (0 < ab.1 * lo - ab.2) && decide (0 < ab.1 * hi - ab.2)) ||
      (decide (ab.1 * lo - ab.2 < 0) && decide (ab.1 * hi - ab.2 < 0))

def lAvoid (lo hi : ℚ) (ts : List LTerm) : Bool :=
  (decide (0 < lo) || decide (hi < 0)) && ts.all (fun t => lAvoidOne lo hi t.2)

theorem lAvoid_sound (lo hi : ℚ) (ts : List LTerm) (h : lAvoid lo hi ts = true) :
    (∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ≠ 0) ∧
      ∀ t ∈ ts, ∀ ab, t.2 = some ab → ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
        (ab.1 : ℝ) * x - (ab.2 : ℝ) ≠ 0 := by
  simp only [lAvoid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hz, ht⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hz with h | h
    · have : (0 : ℝ) < lo := by exact_mod_cast h
      exact (lt_of_lt_of_le this hx.1).ne'
    · have : (hi : ℝ) < 0 := by exact_mod_cast h
      exact (lt_of_le_of_lt hx.2 this).ne
  · intro t htm ab hab x hx
    have h1 := ht t htm
    rw [hab] at h1
    simp only [lAvoidOne, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
    rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · have b1 : (0 : ℝ) < (ab.1 : ℝ) * lo - ab.2 := by exact_mod_cast a1
      have b2 : (0 : ℝ) < (ab.1 : ℝ) * hi - ab.2 := by exact_mod_cast a2
      exact (lin_pos _ _ _ _ x hx.1 hx.2 b1 b2).ne'
    · have b1 : (ab.1 : ℝ) * lo - ab.2 < 0 := by exact_mod_cast a1
      have b2 : (ab.1 : ℝ) * hi - ab.2 < 0 := by exact_mod_cast a2
      exact (lin_neg _ _ _ _ x hx.1 hx.2 b1 b2).ne


/-! The cell checker for `fieldTower fq F + lfieldTower ts` (polynomial/log/pole part plus Laurent part). -/

/-- **Generic cell core**: a tower on the cell with enclosed point coefficients `cs ± es` gives the
Taylor-model bound (the final step of `fieldCellCheck_sound`, for an abstract tower). -/
theorem cellCore {f : ℕ → ℝ → ℝ} (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (cs es : List ℚ)
    (hT0 : IsTower f (((lo + hi) / 2 : ℚ) : ℝ) (((hi - lo) / 2 : ℚ) : ℝ) (Bl.length + 3))
    (hspec : ∀ k, 1 ≤ k → k ≤ Bl.length + 2 →
      |f k (((lo + hi) / 2 : ℚ) : ℝ) / (k ! : ℝ) - ((cs.getD k 0 : ℚ) : ℝ)| ≤
        ((es.getD k 0 : ℚ) : ℝ))
    (hl1 : l1 ≤ cs.getD 1 0 - es.getD 1 0) (hu1 : cs.getD 1 0 + es.getD 1 0 ≤ u1)
    (hA2 : cs.getD 2 0 + es.getD 2 0 ≤ A2) (hB : absLeAllE cs es 3 Bl = true)
    (hT : tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)
    (h0 : f 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |f (Bl.length + 3) x| / ((Bl.length + 3)! : ℝ) ≤ (BM : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), f 0 x ≤ (T : ℝ) := by
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hcoef := absLeAllE_spec _ _ Bl 3 hB
  intro x hx
  rw [← hcell] at hx
  have key := taylor_cell_ub_rat (f := f) (c := (c : ℝ)) (r := (r : ℝ)) Bl hT0
    (A0 := A0) (l1 := l1) (u1 := u1) (A2 := A2) (BM := BM) h0
    (by
      have h := abs_le.mp (hspec 1 le_rfl (by omega))
      have h1' : (l1 : ℝ) ≤ ((cs.getD 1 0 : ℚ) : ℝ) - ((es.getD 1 0 : ℚ) : ℝ) := by
        exact_mod_cast hl1
      have h2 := h.1
      simp only [Nat.factorial_one, Nat.cast_one, div_one] at h2
      linarith)
    (by
      have h := abs_le.mp (hspec 1 le_rfl (by omega))
      have h1' : ((cs.getD 1 0 : ℚ) : ℝ) + ((es.getD 1 0 : ℚ) : ℝ) ≤ (u1 : ℝ) := by
        exact_mod_cast hu1
      have h2 := h.2
      simp only [Nat.factorial_one, Nat.cast_one, div_one] at h2
      linarith)
    (by
      have h := abs_le.mp (hspec 2 (by omega) (by omega))
      have h2' : ((cs.getD 2 0 : ℚ) : ℝ) + ((es.getD 2 0 : ℚ) : ℝ) ≤ (A2 : ℝ) := by
        exact_mod_cast hA2
      have h3 := h.2
      simp only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, mul_one, one_mul] at h3
      linarith)
    (by
      intro i hi'
      have h1 := hcoef i hi'
      have h2 := abs_le.mp (hspec (3 + i) (by omega) (by omega))
      have h3 : ((qabs' (cs.getD (3 + i) 0) : ℚ) : ℝ) + ((es.getD (3 + i) 0 : ℚ) : ℝ) ≤
          ((Bl.getD i 0 : ℚ) : ℝ) := by exact_mod_cast h1
      rw [qabs'_cast] at h3
      have e0 : |f (3 + i) (c : ℝ)| / ((3 + i)! : ℝ) = |f (3 + i) (c : ℝ) / ((3 + i)! : ℝ)| := by
        rw [abs_div, Nat.abs_cast]
      rw [e0, abs_le]
      constructor <;> linarith [h2.1, h2.2, le_abs_self ((cs.getD (3 + i) 0 : ℚ) : ℝ),
        neg_abs_le ((cs.getD (3 + i) 0 : ℚ) : ℝ)])
    (by
      intro y hy
      rw [hcell] at hy
      exact hBM y ⟨le_trans (by exact_mod_cast hb1) hy.1, le_trans hy.2 (by exact_mod_cast hb2)⟩)
    r (by simp [hr])
  have := key x hx
  refine this.trans ?_
  exact_mod_cast hT

/-- **The Boolean cell checker for a field with a Laurent part**: `fieldTower fq F + lfieldTower ts`
on the cell `[lo, hi]` (away from `0`, the poles, the logarithmic singularities and `α x = β`);
coefficients are those of `fieldCellCheck` plus the Laurent coefficients `lCoef`, errors added. -/
def lfCellCheck (fq : FieldQ) (ts : List LTerm) (Ls εs : List ℚ) (Lv : List (ℚ × ℚ))
    (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) : Bool :=
  let cs := (List.range (Bl.length + 3)).map (fun k =>
    (fieldCoefs fq Ls ((lo + hi) / 2) (Bl.length + 2)).getD k 0 + lCoef ts Lv ((lo + hi) / 2) k)
  let es := (List.range (Bl.length + 3)).map (fun k =>
    (plogErrSum ((lo + hi) / 2) (Bl.length + 2) fq.plogs εs).getD k 0 +
      lErr ts Lv ((lo + hi) / 2) k)
  decide (lo ≤ hi) &&
  fq.plogs.all (fun t => decide (hi < t.2) || decide (t.2 < lo)) &&
  fq.poles.all (fun q => decide (0 < poleDist q lo hi)) && lAvoid lo hi ts &&
  decide (l1 ≤ cs.getD 1 0 - es.getD 1 0) && decide (cs.getD 1 0 + es.getD 1 0 ≤ u1) &&
  decide (cs.getD 2 0 + es.getD 2 0 ≤ A2) &&
  absLeAllE cs es 3 Bl && decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

/-- **Soundness of `lfCellCheck`.**  `hBM` is the block tail of the *sum* (add the bounds of
`blockTailCheck_sound` and `lTailCheck_sound`, `lTail_add`). -/
theorem lfCellCheck_sound (fq : FieldQ) (F : ℝ → ℝ) (ts : List LTerm) (Ls εs : List ℚ)
    (Lv : List (ℚ × ℚ)) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hchk : lfCellCheck fq ts Ls εs Lv lo hi A0 l1 u1 A2 Bl BM T = true)
    (hLs : LogVals ((lo + hi) / 2) fq.plogs Ls εs)
    (hLv : LLogVals ((lo + hi) / 2) ts Lv)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F ((fq.poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : fieldTower fq F 0 (((lo + hi) / 2 : ℚ) : ℝ) + lfieldTower ts 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤
      (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |fieldTower fq F (Bl.length + 3) x + lfieldTower ts (Bl.length + 3) x| /
        ((Bl.length + 3)! : ℝ) ≤ (BM : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq F 0 x + lfieldTower ts 0 x ≤ (T : ℝ) := by
  simp only [lfCellCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlh, hplog⟩, hpole⟩, hav⟩, hl1⟩, hu1⟩, hA2⟩, hB⟩, hT⟩ := hchk
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hdl' : ∀ q ∈ fq.poles, 0 < poleDist q lo hi := fun q hq => by simpa using hpole q hq
  have hnee : ∀ t ∈ fq.plogs, ∀ x ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      x ≠ (t.2 : ℝ) := by
    intro t ht x hx hxe
    rw [hcell] at hx
    rcases hplog t ht with h | h
    · have h' : (hi : ℝ) < (t.2 : ℝ) := by exact_mod_cast (by simpa using h : hi < t.2)
      linarith [hx.2]
    · have h' : (t.2 : ℝ) < (lo : ℝ) := by exact_mod_cast (by simpa using h : t.2 < lo)
      linarith [hx.1]
  have hnec : ∀ t ∈ fq.plogs, c - t.2 ≠ 0 := by
    intro t ht h
    rcases hplog t ht with h1 | h1
    · have : hi < t.2 := by simpa using h1
      simp only [hc] at h; linarith
    · have : t.2 < lo := by simpa using h1
      simp only [hc] at h; linarith
  have hnep : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), ∀ q ∈ fq.poles,
      (y : ℂ) ≠ q.pc := by
    intro y hy q hq heq
    rw [hcell] at hy
    have := poleDist_le_norm q lo hi y hy.1 hy.2
    rw [heq, sub_self, norm_zero] at this
    have h2 : (0 : ℝ) < ((poleDist q lo hi : ℚ) : ℝ) := by exact_mod_cast hdl' q hq
    linarith
  have hF' : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      HasDerivAt F ((fq.poles.map (fun q => qt q 0 y)).sum) y := by
    intro y hy; rw [hcell] at hy; exact hF y hy
  obtain ⟨hz, hne⟩ := lAvoid_sound lo hi ts hav
  have hlh' : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by simp only [hr]; push_cast; linarith [hlh']
  have hcI : (c : ℝ) ∈ Icc (lo : ℝ) (hi : ℝ) := ⟨by rw [← e1]; linarith, by rw [← e2]; linarith⟩
  have hc0 : c ≠ 0 := by
    intro h; exact hz _ hcI (by rw [h]; simp)
  have hneQ : ∀ t ∈ ts, ∀ ab, t.2 = some ab → ab.1 * c - ab.2 ≠ 0 := by
    intro t ht ab hab h
    refine hne t ht ab hab _ hcI ?_
    have : (ab.1 : ℝ) * (c : ℝ) - (ab.2 : ℝ) = 0 := by exact_mod_cast h
    exact this
  have hT1 := isTower_fieldTower fq F (c : ℝ) (r : ℝ) (Bl.length + 3) hnee hnep hF'
  have hT2 := isTower_lfieldTower ts (c : ℝ) (r : ℝ) (Bl.length + 3)
    (fun x hx => hz x (by rw [← hcell]; exact hx))
    (fun t ht ab hab x hx => hne t ht ab hab x (by rw [← hcell]; exact hx))
  have hTT : IsTower (fun j x => fieldTower fq F j x + lfieldTower ts j x) (c : ℝ) (r : ℝ)
      (Bl.length + 3) := hT1.add hT2
  refine cellCore (f := fun j x => fieldTower fq F j x + lfieldTower ts j x) lo hi A0 l1 u1 A2 Bl BM T
    _ _ hTT ?_ hl1 hu1 hA2 hB hT h0 blo bhi hb1 hb2 hBM
  intro k hk1 hk
  beta_reduce
  have hkM : k < Bl.length + 3 := by omega
  have g1 : ((List.range (Bl.length + 3)).map (fun k =>
      (fieldCoefs fq Ls c (Bl.length + 2)).getD k 0 + lCoef ts Lv c k)).getD k 0 =
      (fieldCoefs fq Ls c (Bl.length + 2)).getD k 0 + lCoef ts Lv c k :=
    getD_map_range _ _ _ hkM
  have g2 : ((List.range (Bl.length + 3)).map (fun k =>
      (plogErrSum c (Bl.length + 2) fq.plogs εs).getD k 0 + lErr ts Lv c k)).getD k 0 =
      (plogErrSum c (Bl.length + 2) fq.plogs εs).getD k 0 + lErr ts Lv c k :=
    getD_map_range _ _ _ hkM
  rw [g1, g2]
  have a1 := fieldCoefs_approx fq F Ls εs c (Bl.length + 2) hLs hnec k hk1 hk
  have a2 := lfield_approx c hc0 ts Lv hLv hneQ k
  simp only [Rat.cast_add]
  have e : (fieldTower fq F k (c : ℝ) + lfieldTower ts k (c : ℝ)) / (k ! : ℝ) =
      fieldTower fq F k (c : ℝ) / (k ! : ℝ) + lfieldTower ts k (c : ℝ) / (k ! : ℝ) := by ring
  rw [e]
  have key := (abs_add_le (fieldTower fq F k (c : ℝ) / (k ! : ℝ) -
      (((fieldCoefs fq Ls c (Bl.length + 2)).getD k 0 : ℚ) : ℝ))
    (lfieldTower ts k (c : ℝ) / (k ! : ℝ) - ((lCoef ts Lv c k : ℚ) : ℝ))).trans
    (add_le_add a1 a2)
  refine le_trans (le_of_eq ?_) key
  congr 1
  ring

/-- Sum of the block tails (the field part and the Laurent part). -/
theorem lTail_add {A B : ℝ → ℝ} {M : ℕ} {x : ℝ} {BA BB : ℝ}
    (hA : |A x| / (M ! : ℝ) ≤ BA) (hB : |B x| / (M ! : ℝ) ≤ BB) :
    |A x + B x| / (M ! : ℝ) ≤ BA + BB := by
  have hf : (0 : ℝ) < (M ! : ℝ) := by positivity
  calc |A x + B x| / (M ! : ℝ) ≤ (|A x| + |B x|) / (M ! : ℝ) :=
        div_le_div_of_nonneg_right (abs_add_le _ _) hf.le
    _ = |A x| / (M ! : ℝ) + |B x| / (M ! : ℝ) := by rw [add_div]
    _ ≤ BA + BB := add_le_add hA hB


/-- At order `0`, the Laurent polynomial is the polynomial evaluated at `1/x`. -/
theorem zTowAux_zero (x : ℝ) : ∀ (a : List ℚ) (s : ℕ),
    zTowAux s a 0 x = (x⁻¹) ^ s * polyTow a 0 x⁻¹ := by
  intro a
  induction a with
  | nil => intro s; simp [zTowAux, polyTow]
  | cons a as ih =>
    intro s
    rw [zTowAux, ih (s + 1)]
    have h : polyTow (a :: as) 0 x⁻¹ = (a : ℝ) + x⁻¹ * polyTow as 0 x⁻¹ := rfl
    rw [h]
    simp only [monoInv, pow_zero, add_zero, Nat.ascFactorial_zero, Nat.cast_one, one_mul, inv_pow]
    ring

theorem zTow_zero (a : List ℚ) (x : ℝ) : zTow a 0 x = polyTow a 0 x⁻¹ := by
  unfold zTow; rw [zTowAux_zero]; simp

/-- Regression: `1/x ≤ 1.34` on `[3/4, 5/4]` through the Laurent cell checker and block tail
(`T = 1.34`; the checker rejects `T = 1.33`, below the true supremum `4/3`). -/
example : lfCellCheck ⟨[], [], []⟩ [([0, 1], none)] [] [] [(0, 0)] (3 / 4) (5 / 4) 1 (-1) (-1) 1
    [1, 1, 1, 1, 1] 14 (134 / 100) = true := by decide +kernel
example : lfCellCheck ⟨[], [], []⟩ [([0, 1], none)] [] [] [(0, 0)] (3 / 4) (5 / 4) 1 (-1) (-1) 1
    [1, 1, 1, 1, 1] 14 (133 / 100) = false := by decide +kernel
example : lfCellCheck ⟨[], [], []⟩ [([0, 1], none)] [] [] [(0, 0)] (-1 / 4) (5 / 4) 1 (-1) (-1) 1
    [1, 1, 1, 1, 1] 14 (134 / 100) = false := by decide +kernel
example : lTailCheck (3 / 4) (5 / 4) (3 / 4) 8 [([0, 1], none)] [⟨0, 0⟩] 14 = true := by
  decide +kernel
example : lTailCheck (3 / 4) (5 / 4) (3 / 4) 8 [([0, 1], none)] [⟨0, 0⟩] 13 = false := by
  decide +kernel
/-- A logarithmic Laurent term: `(log x)/x` has Taylor data `L = log 1 = 0` at `c = 1`. -/
example : lfCellCheck ⟨[], [], []⟩ [([0, 1], some (1, 0))] [] [] [(0, 0)] (3 / 4) (5 / 4) 0 1 1 (-3 / 2)
    [2, 3, 3, 3, 3] 400 (21 / 100) = true := by decide +kernel
example : lfCellCheck ⟨[], [], []⟩ [([0, 1], some (1, 0))] [] [] [(0, 0)] (3 / 4) (5 / 4) 0 1 1 (-3 / 2)
    [2, 3, 3, 3, 3] 400 (17 / 100) = false := by decide +kernel

end CatalanMeasure.GenD.Signed.TaylorCell

#print axioms CatalanMeasure.GenD.Signed.TaylorCell.quad_le_quadSupR
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.quadSupR_attained
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.taylor_cell_ub
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.taylor_cell_ub_full
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.tmUBQ_cast
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleCellCheck_sound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_log_abs_sub
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_log_abs_one_sub
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_re_clog
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.quad_le_max
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_iteratedDeriv
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.taylor_cell_ub_rat
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleTower_rem
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleDist_le_norm
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleCellCheck_sound_add
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_poleTower
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.IsTower.mul
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.mulTower_div
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_logTower
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_logTower
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_polyTow
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.polyTow_eq_zero
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.shiftL_spec
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.plogCoefQ_spec
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.tower_majorant
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.majQ_cast
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.polyBnd_of_check
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.polyTow_block
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.mulTower_block_bound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.logTower_block_bound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.plog_block
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleVec_getD
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_fieldTower
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.fieldCellCheck_sound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.plogSum_block
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.blockTailCheck_sound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.plogCoef_split
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.plogCoef_approx
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.plogSumVec_approx
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.fieldCoefs_approx
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.absLeAllE_spec
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_monoInv
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_lfieldTower
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.lTerm_approx
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.lfield_approx
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.lTerm_block
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.lTailCheck_sound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.lAvoid_sound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.cellCore
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.lfCellCheck_sound
