module

public import Submission.CatalanMeasure.GenD.Signed.FieldForm
public import Submission.CatalanMeasure.GenD.Signed.SigmaCap
public import Submission.CatalanMeasure.GenD.Signed.MarkedCap
public import Submission.CatalanMeasure.GenD.Analytic.Const
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.McC1

/-!
# Glue for the G <= 410 chain (contract items 3, 6, 7, 11, 12, 13)

Small lemmas that connect existing theorems to the `Phase2Data` contract; nothing here edits an
existing statement.

* Item 3 (`hRm`, `hRn`): `rm_err_eq`, `hRm_limit`, `hRm_neg`, `hRm_pos` (the fixed-row field
  `groupedMarkedField` is within `log 2 / n` of `-c log (1 + x^2)` on `|x| <= 1`); for the near field
  `groupedNearField` the difference is `(1/n)(log (1 + x^2) - log |x|)`, which is NOT small near `0`,
  so the limit lemma is windowed (`hRn_window`, `x in (g, 1)`).  The cell lemmas take `hRn` on all of
  `(0, 1)`; `rnPatch` replaces `Rn N` below `g` by `RnL` (`fNearMS` uses `Rn` pointwise), and
  `fNearMS_cell_win` / `fNearMS_cell_top_win` are the cell lemmas with the windowed hypothesis.
* Item 6: `summable_abs_tseq` (`Summable |tseq f tail|` from a finitely supported `f` and `TailOK`).
* Item 7: `nodeCap_mono`, `nodeCap_gap_mono`, `gap_C1_le` (`C1 = 9631/20000` for `J = 53 N`, `n = 58 N`).
* Item 11: `constantClosed` (the real formula in `alpha`), `constantClosed_eq_grouped` (= `hconst`),
  `constantClosed_eq_lim`, `constantClosed_le_lim`, `hP_closed`.
* Item 12: `capInt_le_of_gap` (and rational forms), `zbCap_le`.
* Item 13: `fNearMSLim_affine`, `fNearMSLim_le_affine`, `fNearMSLim_top_split` (the near field limit is
  affine in `(alpha, beta)`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Glue410

open Set Filter

noncomputable section

/-! ### Item 6: summability of `tseq` -/

section Summ

open CatalanMeasure.Signed.FieldForm

theorem summable_tailNorm : ∀ (tail : Tail), TailOK tail →
    Summable fun k : ℕ => (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum
  | [], _ => by
      simp only [List.map_nil, List.sum_nil]
      exact summable_zero
  | zr :: l, h => by
      have h1 : ‖zr.1‖ < 1 := (h zr (by simp)).1
      have h2 : TailOK l := fun z hz => h z (by simp [hz])
      have hg : Summable fun k : ℕ => ‖zr.2‖ * ‖zr.1‖ ^ k :=
        (summable_geometric_of_lt_one (norm_nonneg _) h1).mul_left _
      simp only [List.map_cons, List.sum_cons]
      exact hg.add (summable_tailNorm l h2)

theorem abs_tailSum_le : ∀ (tail : Tail) (k : ℕ),
    |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum
  | [], k => by simp
  | zr :: l, k => by
      simp only [List.map_cons, List.sum_cons, Complex.add_re]
      have h1 : |(zr.2 * zr.1 ^ k).re| ≤ ‖zr.2‖ * ‖zr.1‖ ^ k := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_pow]
      exact (abs_add_le _ _).trans (add_le_add h1 (abs_tailSum_le l k))

theorem tailNorm_nonneg (tail : Tail) (k : ℕ) :
    0 ≤ (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum := by
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨zr, _, rfl⟩ := List.mem_map.1 hx
  positivity

/-- **Item 6.**  `Summable |tseq f tail|` for a finitely supported finite part and an admissible
tail.  Consumers: `Family.hasum` (`FieldForm`), `SignedRegular.hv/ha/hp` (`Interp`), `SpikeEnv.ha`. -/
theorem summable_abs_tseq {f : ℕ → ℝ} {L : ℕ} {tail : Tail} (hf : ∀ k, L < k → f k = 0)
    (hT : TailOK tail) : Summable fun k => |tseq f tail k| := by
  have hS := summable_tailNorm tail hT
  have hF : Summable fun k : ℕ => |f k| := by
    refine summable_of_ne_finset_zero (s := Finset.range (L + 1)) fun k hk => ?_
    have hlt : L < k := by
      by_contra hh
      exact hk (Finset.mem_range.2 (by omega))
    show |f k| = 0
    rw [hf k hlt, abs_zero]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) (hF.add hS)
  show |tseq f tail k| ≤ |f k| + (tail.map (fun zr : ℂ × ℂ => ‖zr.2‖ * ‖zr.1‖ ^ k)).sum
  unfold tseq
  split_ifs with h
  · rw [abs_zero]
    exact add_nonneg (abs_nonneg _) (tailNorm_nonneg tail k)
  · exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_tailSum_le tail k))

theorem Spec_summable_v {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun j => |D.v j| := by
  rw [h.hv]; exact summable_abs_tseq h.hvf h.hvT

theorem Spec_summable_a {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun j => |D.a j| := by
  rw [h.ha]; exact summable_abs_tseq h.haf h.haT

theorem Spec_summable_p {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun j => |D.p j| := by
  rw [h.hp]; exact summable_abs_tseq h.hpf h.hpT

/-- The `hasum` field of `Family D F`, from the spec of any one member. -/
theorem hasum_of_spec {F : TrialForm} {D : SignedData} (h : F.Spec D) :
    Summable fun k => |tseq F.a.f F.a.tail k| :=
  summable_abs_tseq h.haf h.haT

end Summ

/-! ### Item 3: limit lemmas for the fixed-row fields `Rm`, `Rn` -/

section RmRn

open CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic

theorem cast_n_sub_g_sub_one {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    ((P.n N - P.g N - 1 : ℕ) : ℝ) = (P.n N : ℝ) - (P.g0 : ℝ) * N - 1 := by
  have hg := two_g_lt_n hP hN
  rw [Nat.cast_sub (by omega : 1 ≤ P.n N - P.g N), Nat.cast_sub (by omega : P.g N ≤ P.n N)]
  simp [Parameters.g] <;> ring

theorem cast_n_sub_one_sub_two_g {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) = (P.n N : ℝ) - 1 - 2 * (P.g0 : ℝ) * N := by
  have hg := two_g_lt_n hP hN
  rw [Nat.cast_sub (by omega : 2 * P.g N ≤ P.n N - 1), Nat.cast_sub (by omega : 1 ≤ P.n N)]
  simp [Parameters.g] <;> ring

theorem eventually_div_le (M : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, M / (a * N) ≤ ε := by
  have h : Tendsto (fun N : ℕ => M / (a * (N : ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  exact h.eventually (ge_mem_nhds hε)

/-- `groupedMarkedField - (-c log (1 + x^2)) = (1/n) log (1 + x^2)` for `c = (n0 - g0)/n0`. -/
theorem rm_err_eq {P : Parameters} (hP : Admissible P) {c : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) {N : ℕ} (hN : 0 < N) (x : ℝ) :
    groupedMarkedField P N x - (-c * Real.log (1 + x ^ 2)) =
      1 / ((P.n0 : ℝ) * N) * Real.log (1 + x ^ 2) := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold groupedMarkedField
  rw [cast_n_sub_g_sub_one hP hN, n_cast P N, hc]
  field_simp <;> ring

theorem rm_err_le {P : Parameters} (hP : Admissible P) {c : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : |x| ≤ 1) :
    groupedMarkedField P N x - (-c * Real.log (1 + x ^ 2)) ≤ Real.log 2 / ((P.n0 : ℝ) * N) := by
  rw [rm_err_eq hP hc hN x]
  have hx2 : x ^ 2 ≤ 1 := by
    have := abs_le.mp hx
    nlinarith [this.1, this.2]
  have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith)
  calc 1 / ((P.n0 : ℝ) * N) * Real.log (1 + x ^ 2) ≤ 1 / ((P.n0 : ℝ) * N) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = Real.log 2 / ((P.n0 : ℝ) * N) := by ring

/-- **Item 3, `hRm`.**  For `Rm N = groupedMarkedField P N` and `RmL x = -c log (1 + x^2)`
(`c = 53/58` at `P = (58, ., ., 5, .)`; `RmL = rmQ c`): `Rm N x - RmL x <= eps` eventually, uniformly
on `|x| <= 1`. -/
theorem hRm_limit {P : Parameters} (hP : Admissible P) {c : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) {Rm : ℕ → ℝ → ℝ}
    (hRm : ∀ N, Rm N = groupedMarkedField P N) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : ℝ, |x| ≤ 1 → Rm N x - (-c * Real.log (1 + x ^ 2)) ≤ ε := by
  intro ε hε
  filter_upwards [eventually_div_le (Real.log 2) (n0_pos hP) hε, eventually_gt_atTop 0]
    with N h1 hN x hx
  rw [hRm N]
  exact (rm_err_le hP hc hN hx).trans h1

/-- `hRm` in the shape of `fNegM_le_lim` / `fNegM_cell_one`: `x in (-1, 0)`. -/
theorem hRm_neg {P : Parameters} (hP : Admissible P) {c : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) {Rm : ℕ → ℝ → ℝ}
    (hRm : ∀ N, Rm N = groupedMarkedField P N) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      Rm N x - (-c * Real.log (1 + x ^ 2)) ≤ ε := by
  intro ε hε
  filter_upwards [hRm_limit hP hc hRm ε hε] with N hN x hx
  exact hN x (abs_le.2 ⟨hx.1.le, by linarith [hx.2]⟩)

/-- `hRm` in the shape of `fPosMS_cell` / `fPosMR_cell`: `x in (0, 1)`. -/
theorem hRm_pos {P : Parameters} (hP : Admissible P) {c : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) {Rm : ℕ → ℝ → ℝ}
    (hRm : ∀ N, Rm N = groupedMarkedField P N) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      Rm N x - (-c * Real.log (1 + x ^ 2)) ≤ ε := by
  intro ε hε
  filter_upwards [hRm_limit hP hc hRm ε hε] with N hN x hx
  exact hN x (abs_le.2 ⟨by linarith [hx.1], hx.2.le⟩)

/-- `groupedNearField - (-c log (1 + x^2) + c' log |x|) = (1/n)(log (1 + x^2) - log |x|)` for
`c = (n0 - g0)/n0`, `c' = (n0 - 2 g0)/n0` (`53/58`, `24/29` at `P = (58, ., ., 5, .)`). -/
theorem rn_err_eq {P : Parameters} (hP : Admissible P) {c c' : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) (hc' : c' = ((P.n0 : ℝ) - 2 * P.g0) / P.n0)
    {N : ℕ} (hN : 0 < N) (x : ℝ) :
    groupedNearField P N x - (-c * Real.log (1 + x ^ 2) + c' * Real.log |x|) =
      1 / ((P.n0 : ℝ) * N) * (Real.log (1 + x ^ 2) - Real.log |x|) := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 := rm_err_eq hP hc hN x
  have e2 : ((P.n0 : ℝ) * N - 1 - 2 * (P.g0 : ℝ) * N) / ((P.n0 : ℝ) * N) -
      ((P.n0 : ℝ) - 2 * P.g0) / P.n0 = -(1 / ((P.n0 : ℝ) * N)) := by
    field_simp <;> ring
  unfold groupedNearField
  rw [cast_n_sub_one_sub_two_g hP hN, n_cast P N, hc']
  linear_combination h1 + Real.log |x| * e2

theorem rn_err_le {P : Parameters} (hP : Admissible P) {c c' : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) (hc' : c' = ((P.n0 : ℝ) - 2 * P.g0) / P.n0)
    {N : ℕ} (hN : 0 < N) {g x : ℝ} (hg : 0 < g) (hgx : g ≤ x) (hx1 : x ≤ 1) :
    groupedNearField P N x - (-c * Real.log (1 + x ^ 2) + c' * Real.log |x|) ≤
      (Real.log 2 - Real.log g) / ((P.n0 : ℝ) * N) := by
  rw [rn_err_eq hP hc hc' hN x]
  have hx0 : 0 < x := lt_of_lt_of_le hg hgx
  rw [abs_of_pos hx0]
  have h1 : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h2 : Real.log g ≤ Real.log x := Real.log_le_log hg hgx
  calc 1 / ((P.n0 : ℝ) * N) * (Real.log (1 + x ^ 2) - Real.log x) ≤
        1 / ((P.n0 : ℝ) * N) * (Real.log 2 - Real.log g) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (Real.log 2 - Real.log g) / ((P.n0 : ℝ) * N) := by ring

/-- **Item 3, `hRn` (windowed).**  On all of `(0, 1)` the statement `Rn N x - RnL x <= eps` is false
near `0` (the difference is `(1/n)(log (1 + x^2) - log x)`); on a window `(g, 1)`, `g > 0`, it holds
eventually.  `RnL x = -c log (1 + x^2) + c' log |x|` (`= rnQ c c'`). -/
theorem hRn_window {P : Parameters} (hP : Admissible P) {c c' : ℝ}
    (hc : c = ((P.n0 : ℝ) - P.g0) / P.n0) (hc' : c' = ((P.n0 : ℝ) - 2 * P.g0) / P.n0)
    {Rn : ℕ → ℝ → ℝ} (hRn : ∀ N, Rn N = groupedNearField P N) {g : ℝ} (hg : 0 < g) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo g 1,
      Rn N x - (-c * Real.log (1 + x ^ 2) + c' * Real.log |x|) ≤ ε := by
  intro ε hε
  filter_upwards [eventually_div_le (Real.log 2 - Real.log g) (n0_pos hP) hε,
    eventually_gt_atTop 0] with N h1 hN x hx
  rw [hRn N]
  exact (rn_err_le hP hc hc' hN hg hx.1.le hx.2.le).trans h1

end RmRn

/-! ### Item 3 (cont.): the near-field cell lemmas with a windowed `hRn` -/

section Near

open CatalanMeasure.Signed.FieldForm

/-- `Rn N` above `g`, `RnL` at and below `g`.  `fNearMS` uses `Rn` only pointwise, so on cells
inside `(g, 1)` the patched and the true field agree, while the patched one satisfies the
whole-interval hypothesis of `fNearMS_cell`. -/
def rnPatch (Rn : ℕ → ℝ → ℝ) (RnL : ℝ → ℝ) (g : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  if g < y then Rn N y else RnL y

theorem rnPatch_err {Rn : ℕ → ℝ → ℝ} {RnL : ℝ → ℝ} {g : ℝ}
    (hRn : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo g 1, Rn N x - RnL x ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, rnPatch Rn RnL g N x - RnL x ≤ ε := by
  intro ε hε
  filter_upwards [hRn ε hε] with N hN x hx
  unfold rnPatch
  by_cases h : g < x
  · rw [if_pos h]; exact hN x ⟨h, hx.2⟩
  · rw [if_neg h]; linarith

theorem fNearMS_rnPatch {D : SignedData} {Rn : ℕ → ℝ → ℝ} {RnL : ℝ → ℝ} {g : ℝ} {N : ℕ}
    {α β x : ℝ} (hgx : g < x) :
    D.fNearMS (rnPatch Rn RnL g N) α β x = D.fNearMS (Rn N) α β x := by
  have hv : rnPatch Rn RnL g N x = Rn N x := by
    unfold rnPatch; exact if_pos hgx
  simp only [SignedData.fNearMS, SignedData.fNearM, hv]

/-- `fNearMS_cell` with the windowed `hRn`: the cell `(lo, hi)` must lie in the window, `g <= lo`. -/
theorem fNearMS_cell_win {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F)
    {Rn : ℕ → ℝ → ℝ} {RnL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω)
    (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (nhds σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (nhds csL))
    {g : ℝ} (hg : 0 < g)
    (hRn : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo g 1, Rn N x - RnL x ≤ ε)
    {lo hi : ℝ} (hlo : g ≤ lo) (hhi : hi < 1) {T : ℝ → ℝ → ℝ}
    (hlim : ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo lo hi,
      fNearMSLim F RnL α β σ bL KL csL θL x ≤ T α β) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo lo hi,
      (D N).fNearMS (Rn N) α β x ≤ T α β + ε := by
  have key := fNearMS_cell (Rn := rnPatch Rn RnL g) hf hωR hω1 hω0 hbL hKL hθL hσ hcs
    (rnPatch_err hRn) (lo := lo) (hi := hi) (hg.le.trans hlo) hhi hlim
  intro ε hε
  filter_upwards [key ε hε] with N hN α β hβ x hx
  have hgx : g < x := lt_of_le_of_lt hlo hx.1
  rw [← fNearMS_rnPatch (D := (D N)) (Rn := Rn) (RnL := RnL) (N := N) (α := α) (β := β) hgx]
  exact hN α β hβ x hx

/-- `fNearMS_cell_top` with the windowed `hRn`: the top cell `(xc, 1)` must lie in the window,
`g <= xc`. -/
theorem fNearMS_cell_top_win {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F)
    {Rn : ℕ → ℝ → ℝ} {RnL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω)
    (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (nhds σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (nhds csL))
    {g : ℝ} (hg : 0 < g)
    (hRn : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo g 1, Rn N x - RnL x ≤ ε)
    {xc : ℝ} (hxc : g ≤ xc) {gS r0 rS : ℝ → ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hr : ∀ α β : ℝ, 0 ≤ β → r0 α β + δ ≤ rS α β)
    (hsing : ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo xc 1,
      fNearMSLim F RnL α β σ bL KL csL θL x ≤ gS α β + r0 α β * (-Real.log (1 - x ^ 2))) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo xc 1,
      (D N).fNearMS (Rn N) α β x ≤ gS α β + ε + rS α β * (-Real.log (1 - x ^ 2)) := by
  have key := fNearMS_cell_top (Rn := rnPatch Rn RnL g) hf hωR hω1 hω0 hbL hKL hθL hσ hcs
    (rnPatch_err hRn) (hg.le.trans hxc) hδ hr hsing
  intro ε hε
  filter_upwards [key ε hε] with N hN α β hβ x hx
  have hgx : g < x := lt_of_le_of_lt hxc hx.1
  rw [← fNearMS_rnPatch (D := (D N)) (Rn := Rn) (RnL := RnL) (N := N) (α := α) (β := β) hgx]
  exact hN α β hβ x hx

end Near

/-! ### Item 7: `NodeCap` is monotone in `C1`, `umin` (and the other parameters) -/

section Node

theorem nodeCap_mono {gs gs' xc xc' C1 C1' n umin umin' : ℝ} {J : ℕ} {Z : Fin J → ℝ}
    (h : NodeCap gs xc C1 n umin Z) (hgs : gs' ≤ gs) (hxc : xc ≤ xc') (hC : C1 ≤ C1')
    (hn : 0 ≤ n) (hu : 0 ≤ umin) (hu' : umin' ≤ umin) : NodeCap gs' xc' C1' n umin' Z := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => hgs.trans (h1 a), fun a => (h2 a).trans (by linarith), fun a ha => ?_⟩
  have key : C1 * n * (1 - Z a) + 1 ≤ C1' * n * (1 - Z a) + 1 := by
    have h4 : 0 ≤ n * (1 - Z a) := mul_nonneg hn (by linarith [h2 a])
    nlinarith [mul_le_mul_of_nonneg_right hC h4]
  exact (h3 a (hxc.trans ha)).trans key

open CatalanMeasure.GenD.Analytic in
/-- `nodeCap_gap` with any larger `C1'` and any smaller `umin'` (and `gs' <= g`, `xc <= xc'`). -/
theorem nodeCap_gap_mono {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) {xc n : ℝ} (hxc : 0 < xc)
    (hn : 0 < n) (J : ℕ) {gs' xc' C1' umin' : ℝ} (hgs : gs' ≤ g) (hxc' : xc ≤ xc')
    (hC : (J : ℝ) / (n * (2 * xc * Real.sqrt (1 - (2 * g / (1 + g ^ 2)) ^ 2))) ≤ C1')
    (hu : umin' ≤ Real.sqrt (1 - (2 * g / (1 + g ^ 2)) ^ 2) / (2 * ((J : ℝ) + 1))) :
    NodeCap gs' xc' C1' n umin'
      (fun i : Fin J => OAI.InternalCatalan.realCoordinate
        (gapNodesGen (2 * g / (1 + g ^ 2)) J i)) :=
  nodeCap_mono (nodeCap_gap hg0 hg1 hxc hn J) hgs hxc' hC hn.le (by positivity) hu

/-- The node constant of the actual gap nodes is at most `9631/20000`
(`J = 53 N`, `n = 58 N`, `2g/(1+g^2) = 2005000/6410801`, `xc = 999/1000`). -/
theorem gap_C1_le {g xc n : ℝ} {J N : ℕ} (hN : 0 < N) (hJ : (J : ℝ) = 53 * N) (hn : n = 58 * N)
    (hxc : xc = 999 / 1000) (ha : 2 * g / (1 + g ^ 2) = 2005000 / 6410801) :
    (J : ℝ) / (n * (2 * xc * Real.sqrt (1 - (2 * g / (1 + g ^ 2)) ^ 2))) ≤ 9631 / 20000 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [ha, hJ, hn, hxc]
  have e : (53 * (N : ℝ)) / (58 * N * (2 * (999 / 1000) *
        Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2))) =
      53 / (58 * (2 * (999 / 1000) * Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2))) := by
    rw [show (58 : ℝ) * N * (2 * (999 / 1000) * Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2)) =
        N * (58 * (2 * (999 / 1000) * Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2))) by ring,
      show (53 : ℝ) * N = N * 53 by ring, mul_div_mul_left _ _ hNr]
  rw [e]
  exact CatalanMeasure.Signed.Consts.C1_bound

end Node

/-! ### Item 11: the constant `D.constant` in closed form (`hconst`, `hP`) -/

section Const

open CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic

/-- The grouped constant as a real function of the fixed fraction `alpha = (a + b)/n`:
`r = (1 - alpha) n` rows of the first kind and `s = alpha n` fixed rows. -/
def constantClosed (P : Parameters) (N : ℕ) (α : ℝ) : ℝ :=
  (((1 - α) * (P.n N : ℝ)) * ((P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1) +
      (α * (P.n N : ℝ)) * ((P.n N : ℝ) - (P.g0 : ℝ) * N - 1) +
      ((1 - α) * (P.n N : ℝ)) * ((1 - α) * (P.n N : ℝ) - 1) / 2) / (P.n N : ℝ) ^ 2 *
    Real.log 2

/-- The limit `N -> infinity` of `constantClosed P N alpha`. -/
def constantLim (P : Parameters) (α : ℝ) : ℝ :=
  ((1 - α) * (1 + gKappa P) + α * gRes P + (1 - α) ^ 2 / 2) * Real.log 2

theorem groupedConstant_real {P : Parameters} (hP : Admissible P) {N r a b : ℕ} (hN : 0 < N) :
    groupedConstant P N r a b = ((r : ℝ) * ((P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1) +
      ((a + b : ℕ) : ℝ) * ((P.n N : ℝ) - (P.g0 : ℝ) * N - 1) + (r : ℝ) * ((r : ℝ) - 1) / 2) /
        (P.n N : ℝ) ^ 2 * Real.log 2 := by
  have hnpos := n_pos hP hN
  have hC := C_nat P N
  have hCsub : 1 ≤ P.C N := by omega
  have hCR : ((P.C N - 1 : ℕ) : ℝ) = (P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1 := by
    rw [Nat.cast_sub hCsub, hC]; push_cast; ring
  have hdR := cast_n_sub_g_sub_one hP hN
  unfold groupedConstant
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hCR, hdR, Nat.cast_choose_two]

/-- **Item 11, `hconst`.**  `D.constant := constantClosed P` satisfies the `hconst` hypothesis of
`Phase2Data.signedSecondSheetNear` (and `...Nd`, `...Nd_nearOpt`). -/
theorem constantClosed_eq_grouped {P : Parameters} (hP : Admissible P) (N r a b : ℕ)
    (h : r + a + b = P.n N) :
    constantClosed P N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (P.n 0 : ℝ) = 0 := by simp [Parameters.n]
    unfold constantClosed groupedConstant
    rw [h0]
    simp
  · have hnpos := n_pos hP hN
    have hnR : (0 : ℝ) < (P.n N : ℝ) := by exact_mod_cast hnpos
    have hr : (r : ℝ) = (P.n N : ℝ) - ((a + b : ℕ) : ℝ) := by
      have h' : (r : ℝ) + ((a + b : ℕ) : ℝ) = (P.n N : ℝ) := by
        exact_mod_cast (by omega : r + (a + b) = P.n N)
      linarith
    rw [groupedConstant_real hP hN]
    have e1 : (1 - ((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * (P.n N : ℝ) = (r : ℝ) := by
      rw [hr]; field_simp <;> ring
    have e2 : ((a + b : ℕ) : ℝ) / (P.n N : ℝ) * (P.n N : ℝ) = ((a + b : ℕ) : ℝ) := by
      field_simp <;> ring
    unfold constantClosed
    rw [e1, e2]

/-- The `hconst` hypothesis of the end-to-end corollaries, for `constant := constantClosed P`. -/
theorem hconst_closed {P : Parameters} (hP : Admissible P) :
    ∀ N r a b, r + a + b = P.n N →
      constantClosed P N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b :=
  fun N r a b h => constantClosed_eq_grouped hP N r a b h

theorem constantClosed_eq_lim {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (α : ℝ) :
    constantClosed P N α =
      constantLim P α - ((3 / 2) * (1 - α) + α) / (P.n N : ℝ) * Real.log 2 := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold constantClosed constantLim gKappa gRes
  rw [n_cast P N]
  field_simp <;> ring

theorem constantClosed_le_lim {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : constantClosed P N α ≤ constantLim P α := by
  rw [constantClosed_eq_lim hP hN α]
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h0 : 0 ≤ (3 / 2 : ℝ) * (1 - α) + α := by linarith
  have h : 0 ≤ ((3 / 2 : ℝ) * (1 - α) + α) / (P.n N : ℝ) * Real.log 2 :=
    mul_nonneg (div_nonneg h0 (Nat.cast_nonneg _)) hl
  linarith

/-- `constantLim` as a quadratic in `alpha` (for `norm_num`/`nlinarith` against `cP`). -/
theorem constantLim_eq (P : Parameters) (α : ℝ) :
    constantLim P α = ((3 / 2 + gKappa P) + (gRes P - gKappa P - 2) * α + α ^ 2 / 2) *
      Real.log 2 := by
  unfold constantLim; ring

/-- **Item 11, `hP`.**  With `constant := constantClosed P`, the `hP` field of `Phase2Data` follows
from `constantLim P alpha <= cP i alpha` on each interval (`0 <= lo`, `hi <= 1`). -/
theorem hP_closed {P : Parameters} (hP : Admissible P) {I : ℕ} {lo hi : Fin I → ℝ}
    {cP : Fin I → ℝ → ℝ} (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hc : ∀ i, ∀ α ∈ Icc (lo i) (hi i), constantLim P α ≤ cP i α) :
    ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
      constantClosed P N α ≤ cP i α + ε := by
  intro i ε hε
  filter_upwards [eventually_gt_atTop 0] with N hN α hα
  have := constantClosed_le_lim hP hN ((hlo i).trans hα.1) (hα.2.trans (hhi i))
  linarith [hc i α hα]

end Const

/-! ### Item 12: the top-cell terms `capInt` of `zbCap` (`hZB`) -/

section ZB

theorem exp_neg_le_inv_one_add {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 / (1 + y) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp y])

theorem exp_neg_le_inv_quad {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 / (1 + y + y ^ 2 / 2) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by nlinarith [sq_nonneg y]) (Real.quadratic_le_exp_of_nonneg hy)

/-- `r exp (Bd/r)` is increasing in `r > 0` for `Bd <= 0`. -/
theorem mul_exp_mono {Bd r R : ℝ} (hBd : Bd ≤ 0) (hr : 0 < r) (hrR : r ≤ R) :
    r * Real.exp (Bd / r) ≤ R * Real.exp (Bd / R) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have ht : Bd / r ≤ Bd / R := by
    rw [div_le_div_iff₀ hr hR]
    exact mul_le_mul_of_nonpos_left hrR hBd
  have e : Bd / r = Bd / R + (Bd / r - Bd / R) := by ring
  have h1 : Real.exp (Bd / r - Bd / R) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  rw [e, Real.exp_add]
  have hE := Real.exp_pos (Bd / R)
  calc r * (Real.exp (Bd / R) * Real.exp (Bd / r - Bd / R)) ≤ r * (Real.exp (Bd / R) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hE.le) hr.le
    _ = r * Real.exp (Bd / R) := by rw [mul_one]
    _ ≤ R * Real.exp (Bd / R) := mul_le_mul_of_nonneg_right hrR hE.le

/-- **Item 12.**  If the gap `c = g0 - lam` is at most `Bd < 0` and `0 <= r <= Rbd`, then
`capInt c r theta <= Rbd exp (Bd / Rbd)` (including `r = 0`). -/
theorem capInt_le_of_gap {c r θ Bd Rbd : ℝ} (hθ : 0 < θ) (hBd : Bd < 0) (hRbd : 0 < Rbd)
    (hc : c ≤ Bd) (hr0 : 0 ≤ r) (hr : r ≤ Rbd) :
    capInt c r θ ≤ Rbd * Real.exp (Bd / Rbd) := by
  rcases hr0.eq_or_lt with h0 | hpos
  · subst h0
    unfold capInt
    rw [if_neg (lt_irrefl (0 : ℝ)), max_eq_left (by linarith : c ≤ 0), mul_zero]
    exact (mul_pos hRbd (Real.exp_pos _)).le
  · have h1 := capInt_le_mul_exp (c := c) (θ := θ) hpos hθ
    have h2 : c / r ≤ Bd / r := by
      rw [div_le_div_iff₀ hpos hpos]
      exact mul_le_mul_of_nonneg_right hc hpos.le
    have h3 : r * Real.exp (c / r) ≤ r * Real.exp (Bd / r) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) hpos.le
    exact h1.trans (h3.trans (mul_exp_mono hBd.le hpos hr))

/-- Rational form, first order: `capInt c r theta <= Rbd (Rbd / (Rbd - Bd))`. -/
theorem capInt_le_rat {c r θ Bd Rbd : ℝ} (hθ : 0 < θ) (hBd : Bd < 0) (hRbd : 0 < Rbd)
    (hc : c ≤ Bd) (hr0 : 0 ≤ r) (hr : r ≤ Rbd) :
    capInt c r θ ≤ Rbd * (Rbd / (Rbd - Bd)) := by
  refine (capInt_le_of_gap hθ hBd hRbd hc hr0 hr).trans ?_
  have hy : 0 ≤ -Bd / Rbd := div_nonneg (by linarith) hRbd.le
  have h := exp_neg_le_inv_one_add hy
  have e : Real.exp (Bd / Rbd) = Real.exp (-(-Bd / Rbd)) := by congr 1; ring
  rw [e]
  have e2 : 1 / (1 + -Bd / Rbd) = Rbd / (Rbd - Bd) := by
    rw [one_add_div hRbd.ne', one_div_div, ← sub_eq_add_neg]
  rw [e2] at h
  exact mul_le_mul_of_nonneg_left h hRbd.le

/-- Rational form, second order: with `y = -Bd/Rbd`,
`capInt c r theta <= Rbd / (1 + y + y^2/2)`. -/
theorem capInt_le_quad {c r θ Bd Rbd : ℝ} (hθ : 0 < θ) (hBd : Bd < 0) (hRbd : 0 < Rbd)
    (hc : c ≤ Bd) (hr0 : 0 ≤ r) (hr : r ≤ Rbd) :
    capInt c r θ ≤ Rbd * (1 / (1 + -Bd / Rbd + (-Bd / Rbd) ^ 2 / 2)) := by
  refine (capInt_le_of_gap hθ hBd hRbd hc hr0 hr).trans ?_
  have hy : 0 ≤ -Bd / Rbd := div_nonneg (by linarith) hRbd.le
  have h := exp_neg_le_inv_quad hy
  have e : Real.exp (Bd / Rbd) = Real.exp (-(-Bd / Rbd)) := by congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h hRbd.le

/-- **Item 12, `hZB`.**  Pointwise bound of `zbCap` at `(c, d, beta)` (`alpha = c + d + beta`) by
`alpha * max a (max b s) + 2 C1 Rbd exp (Bd/Rbd)`, where `a, b, s` bound `lamN, lamP, lamS` there, and
the gaps `gP - lamP`, `gS - lamS` are at most `Bd < 0` with `0 <= rP, rS <= Rbd`. -/
theorem zbCap_le {S : SigmaCapData} {c d β a b s Bd Rbd : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hβ : 0 ≤ β) (hxc1 : S.xc < 1) (hC1 : 0 ≤ S.C1)
    (hlamN : S.lamN (c + d + β) ≤ a) (hlamP : S.lamP (c + d + β) ≤ b)
    (hlamS : S.lamS (c + d + β) β ≤ s) (hBd : Bd < 0) (hRbd : 0 < Rbd)
    (hgP : S.gP (c + d + β) - S.lamP (c + d + β) ≤ Bd) (hrP0 : 0 ≤ S.rP (c + d + β))
    (hrP : S.rP (c + d + β) ≤ Rbd)
    (hgS : S.gS (c + d + β) β - S.lamS (c + d + β) β ≤ Bd) (hrS0 : 0 ≤ S.rS (c + d + β) β)
    (hrS : S.rS (c + d + β) β ≤ Rbd) :
    zbCap S c d β ≤ (c + d + β) * max a (max b s) + 2 * S.C1 * (Rbd * Real.exp (Bd / Rbd)) := by
  have hθ : 0 < 1 - S.xc := by linarith
  have h1 := capInt_le_of_gap hθ hBd hRbd hgP hrP0 hrP
  have h2 := capInt_le_of_gap hθ hBd hRbd hgS hrS0 hrS
  have hm1 : a ≤ max a (max b s) := le_max_left _ _
  have hm2 : b ≤ max a (max b s) := (le_max_left b s).trans (le_max_right _ _)
  have hm3 : s ≤ max a (max b s) := (le_max_right b s).trans (le_max_right _ _)
  have k1 := mul_le_mul_of_nonneg_left (hlamN.trans hm1) hc
  have k2 := mul_le_mul_of_nonneg_left (hlamP.trans hm2) hd
  have k3 := mul_le_mul_of_nonneg_left (hlamS.trans hm3) hβ
  have hC := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC1
  unfold zbCap
  nlinarith [k1, k2, k3, hC]

end ZB

/-! ### Item 13: the near-field limit is affine in `(alpha, beta)` -/

section Affine

open CatalanMeasure.Signed.FieldForm

/-- Coefficient of `alpha` in `fNearMSLim`. -/
def nearAlphaCoef (x : ℝ) : ℝ := (Real.log (1 + x) + Real.log 2) / 2

/-- Coefficient of `beta` in `fNearMSLim`. -/
def nearBetaCoef (F : TrialForm) (x : ℝ) : ℝ :=
  (-Real.log (1 - x ^ 2)) / (4 * (1 - F.η)) + remC (1 - 2 * F.η) * (2 * Real.log 2)

/-- **Item 13.**  `fNearMSLim` is exactly affine in `(alpha, beta)`:
`fNearMSLim .. alpha beta x = fNearMSLim .. 0 0 x + alpha * A(x) + beta * B(x)`. -/
theorem fNearMSLim_affine (F : TrialForm) (RnL : ℝ → ℝ) (α β σ : ℝ) (bL : ℕ → ℝ) (KL : ℕ)
    (csL θL x : ℝ) :
    fNearMSLim F RnL α β σ bL KL csL θL x =
      fNearMSLim F RnL 0 0 σ bL KL csL θL x + α * nearAlphaCoef x + β * nearBetaCoef F x := by
  unfold fNearMSLim nearAlphaCoef nearBetaCoef
  ring

theorem nearAlphaCoef_le_hi {x hi : ℝ} (hx0 : 0 ≤ x) (hxh : x ≤ hi) :
    nearAlphaCoef x ≤ nearAlphaCoef hi := by
  unfold nearAlphaCoef
  have := Real.log_le_log (by linarith : (0 : ℝ) < 1 + x) (by linarith : 1 + x ≤ 1 + hi)
  linarith

theorem nearAlphaCoef_le_log2 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    nearAlphaCoef x ≤ Real.log 2 := by
  unfold nearAlphaCoef
  have := Real.log_le_log (by linarith : (0 : ℝ) < 1 + x) (by linarith : 1 + x ≤ 2)
  linarith

theorem nearBetaCoef_le_hi {F : TrialForm} (hη : F.η < 1) {x hi : ℝ} (hx0 : 0 ≤ x)
    (hxh : x ≤ hi) (hhi : hi < 1) : nearBetaCoef F x ≤ nearBetaCoef F hi := by
  unfold nearBetaCoef
  have hx2 : x ^ 2 ≤ hi ^ 2 := by nlinarith
  have hpos1 : 0 < 1 - hi ^ 2 := by nlinarith
  have hlog : Real.log (1 - hi ^ 2) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log hpos1 (by linarith)
  have hd : 0 < 4 * (1 - F.η) := by linarith
  have : (-Real.log (1 - x ^ 2)) / (4 * (1 - F.η)) ≤ (-Real.log (1 - hi ^ 2)) / (4 * (1 - F.η)) := by
    rw [div_le_div_iff₀ hd hd]
    exact mul_le_mul_of_nonneg_right (by linarith) hd.le
  linarith

/-- **Item 13, off-top cell.**  From the `(alpha, beta)`-free bound `fNearMSLim .. 0 0 x <= T0` and
bounds `A(x) <= Au`, `B(x) <= Bu` on the cell: `fNearMSLim .. alpha beta x <= T0 + alpha Au + beta Bu`
for `alpha, beta >= 0` (take `Au = A(hi)`, `Bu = B(hi)` by `nearAlphaCoef_le_hi`,
`nearBetaCoef_le_hi`). -/
theorem fNearMSLim_le_affine {F : TrialForm} {RnL : ℝ → ℝ} {α β σ : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    {csL θL x T0 Au Bu : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hz : fNearMSLim F RnL 0 0 σ bL KL csL θL x ≤ T0) (hA : nearAlphaCoef x ≤ Au)
    (hB : nearBetaCoef F x ≤ Bu) :
    fNearMSLim F RnL α β σ bL KL csL θL x ≤ T0 + α * Au + β * Bu := by
  rw [fNearMSLim_affine]
  nlinarith [mul_le_mul_of_nonneg_left hA hα, mul_le_mul_of_nonneg_left hB hβ]

/-- **Item 13, top cell.**  `fNearMSLim .. alpha beta x <= gS + r0 (-log (1 - x^2))` with
`gS = T0 + alpha log 2 + beta remC(1-2 eta) 2 log 2` and `r0 = beta/(4 (1 - eta))` (the shape of
`fNearMS_cell_top`'s `hsing`). -/
theorem fNearMSLim_top_split {F : TrialForm} {RnL : ℝ → ℝ} {α β σ : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    {csL θL x T0 : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hz : fNearMSLim F RnL 0 0 σ bL KL csL θL x ≤ T0) :
    fNearMSLim F RnL α β σ bL KL csL θL x ≤
      (T0 + α * Real.log 2 + β * (remC (1 - 2 * F.η) * (2 * Real.log 2))) +
        (β / (4 * (1 - F.η))) * (-Real.log (1 - x ^ 2)) := by
  rw [fNearMSLim_affine]
  have hA := nearAlphaCoef_le_log2 hx0 hx1
  unfold nearBetaCoef
  have h1 := mul_le_mul_of_nonneg_left hA hα
  have e2 : β * ((-Real.log (1 - x ^ 2)) / (4 * (1 - F.η)) +
      remC (1 - 2 * F.η) * (2 * Real.log 2)) =
      (β / (4 * (1 - F.η))) * (-Real.log (1 - x ^ 2)) +
        β * (remC (1 - 2 * F.η) * (2 * Real.log 2)) := by ring
  nlinarith [h1, e2, hz]

end Affine

end

end CatalanMeasure.Signed.Glue410

#print axioms CatalanMeasure.Signed.Glue410.summable_abs_tseq
#print axioms CatalanMeasure.Signed.Glue410.hRm_limit
#print axioms CatalanMeasure.Signed.Glue410.hRn_window
#print axioms CatalanMeasure.Signed.Glue410.fNearMS_cell_win
#print axioms CatalanMeasure.Signed.Glue410.fNearMS_cell_top_win
#print axioms CatalanMeasure.Signed.Glue410.nodeCap_mono
#print axioms CatalanMeasure.Signed.Glue410.nodeCap_gap_mono
#print axioms CatalanMeasure.Signed.Glue410.gap_C1_le
#print axioms CatalanMeasure.Signed.Glue410.constantClosed_eq_grouped
#print axioms CatalanMeasure.Signed.Glue410.hP_closed
#print axioms CatalanMeasure.Signed.Glue410.capInt_le_of_gap
#print axioms CatalanMeasure.Signed.Glue410.capInt_le_rat
#print axioms CatalanMeasure.Signed.Glue410.capInt_le_quad
#print axioms CatalanMeasure.Signed.Glue410.zbCap_le
#print axioms CatalanMeasure.Signed.Glue410.fNearMSLim_le_affine
#print axioms CatalanMeasure.Signed.Glue410.fNearMSLim_top_split
