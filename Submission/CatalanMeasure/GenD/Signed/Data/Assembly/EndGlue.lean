module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Family
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Cover
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Data

@[expose] public section

/-!
# 410 assembly: end-cell glue (contract rows `hSnA … hSyB`)

* `glue3`: a left end region, an interior `Icc` and a right end region cover `Ioo p q`.
* `rowSN`, `rowSP`, `rowSC`: for one trial `famD X`, the finite-`N` bounds `fNeg ≤ S + ε` on `(-1,0)`,
  `fPosS ≤ S + ε` on `(0,1)`, `fCol ≤ S + ε` on `(0,1)`, from limit-field bounds on an interior interval and
  log-form bounds on the two ends (`fNeg_cell_zero/one`, `fPosS_cell_zero/one`, `fCol_cell_zero/one`,
  `fNeg_unif`, `fPosS_unif`, `fCol_unif`).  The ends need the log-form `fLim ≤ Tr + c log|x|` with `c > 0`
  (`rfLim` has `(22/58) log|x|`, `cfLim` `(3/58) log (1-s)`; NOTES-R).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert

noncomputable section

theorem glue3 {f : ℕ → ℝ → ℝ} {p q r0 a b r1 S0 Sm S1 S : ℝ} (har0 : a ≤ r0) (hr1b : r1 ≤ b)
    (hS0 : S0 ≤ S) (hSm : Sm ≤ S) (hS1 : S1 ≤ S)
    (h0 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo p r0, f N x ≤ S0 + ε)
    (hm : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc a b, f N x ≤ Sm + ε)
    (h1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo r1 q, f N x ≤ S1 + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo p q, f N x ≤ S + ε := by
  intro ε hε
  filter_upwards [h0 ε hε, hm ε hε, h1 ε hε] with N a0 am a1 x hx
  by_cases hxr : x < r0
  · have := a0 x ⟨hx.1, hxr⟩; linarith
  · push_neg at hxr
    by_cases hxb : x ≤ b
    · have := am x ⟨le_trans har0 hxr, hxb⟩; linarith
    · push_neg at hxb
      have := a1 x ⟨lt_of_le_of_lt hr1b hxb, hx.2⟩; linarith

theorem interior_le {f : ℕ → ℝ → ℝ} {L : ℝ → ℝ} {a b Sm : ℝ}
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc a b, |f N x - L x| ≤ ε)
    (hL : ∀ x ∈ Icc a b, L x ≤ Sm) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc a b, f N x ≤ Sm + ε := by
  intro ε hε
  filter_upwards [hu ε hε] with N hN x hx
  have := (abs_le.mp (hN x hx)).2
  have := hL x hx
  linarith

/-- The explicit population fields: `Rf` converges uniformly on `|x| ≤ 1`. -/
theorem hRf_fam (X : FamPar) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, |x| ≤ 1 →
      |(famD X N).Rf x - rfLim P410 x| ≤ ε := by
  have h : Tendsto (fun N : ℕ => 2 * Real.log 2 / ((P410.n N : ℕ) : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => ((P410.n N : ℕ) : ℝ)) atTop atTop := by
      simpa [Parameters.n, P410, D58.Odd.design] using
        tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 58 by norm_num)
    exact tendsto_const_nhds.div_atTop this
  filter_upwards [h.eventually (ge_mem_nhds hε), eventually_gt_atTop 0] with N hN hN0 x hx
  exact (rf_err_le P410 hN0.ne' (by simp [P410, D58.Odd.design]) hx).trans hN

theorem hCf_fam (X : FamPar) {N : ℕ} (hN : 0 < N) (s : ℝ) :
    (famD X N).Cf s = cfLim P410 s :=
  populationPhysicalColumnField_zero P410 hN.ne' (by simp [P410, D58.Odd.design]) s

theorem famD_sigma_tendsto (X : FamPar) :
    Tendsto (fun N => (((famD X N).sp : ℕ) : ℝ) / (famD X N).ν) atTop (𝓝 (20 / 58)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  show (20 / 58 : ℝ) = ((20 * N : ℕ) : ℝ) / (58 * (N : ℝ))
  push_cast; field_simp

theorem famD_R_tail (X : FamPar) (hRt : X.T.R.tail = []) :
    ∀ wr ∈ X.T.form.R.tail, ‖wr.1‖ ≤ (0 : ℝ) := by
  intro wr hwr
  simp [TrialQ.form, SeqQ.form, hRt] at hwr

/-- **Negative free rows**: `fNeg ≤ S + ε` on `(-1, 0)`. -/
theorem rowSN (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {r Tr c hi T a b Sm S : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hsing : ∀ x ∈ Ioo (-r) 0, fNegLim X.T.form (rfLim P410) x ≤ Tr + c * Real.log |x|)
    (hhi : hi < 0) (hlim : ∀ x ∈ Ioo (-1 : ℝ) hi, fNegLim X.T.form (rfLim P410) x ≤ T)
    (ha : -1 < a) (hab : a ≤ b) (hb : b < 0) (har : a ≤ hi) (hrb : -r ≤ b)
    (hL : ∀ x ∈ Icc a b, fNegLim X.T.form (rfLim P410) x ≤ Sm)
    (h0 : Tr + c * Real.log r ≤ S) (h1 : T ≤ S) (h2 : Sm ≤ S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (famD X N).fNeg x ≤ S + ε := by
  have hf := famD_family X hok
  have hωR := famD_R_tail X hRt
  have hRf1 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (famD X N).Rf x - rfLim P410 x ≤ ε := by
    intro ε hε
    filter_upwards [hRf_fam X hε] with N hN x hx
    exact (abs_le.mp (hN x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))).2
  have hRf2 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc a b, |(famD X N).Rf x - rfLim P410 x| ≤ ε := by
    intro ε hε
    filter_upwards [hRf_fam X hε] with N hN x hx
    exact hN x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
  refine glue3 (p := -1) (q := 0) (r0 := hi) (a := a) (b := b) (r1 := -r) har hrb h1 h2 h0 ?_ ?_ ?_
  · exact fun ε hε => fNeg_cell_one hf hωR (by norm_num) le_rfl hRf1 hhi hlim ε hε
  · exact interior_le (fNeg_unif hf ha hab hb hRf2) hL
  · exact fun ε hε => fNeg_cell_zero hf hωR (by norm_num) le_rfl hRf1 hr0 hr1 hc hsing ε hε

/-- **Positive free rows with spike cost**: `fPosS ≤ S + ε` on `(0, 1)`. -/
theorem rowSP (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {r Tr c lo T1 c1 a b Sm S : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hsing : ∀ x ∈ Ioo 0 r, fPosLim X.T.form (rfLim P410) (20 / 58) (bSeq X.bs) X.bs.length
      ((X.CSP : ℝ) / 58) (1 / 1024) x ≤ Tr + c * Real.log |x|)
    (hlo0 : 0 < lo) (hlo1 : lo < 1) (hc1 : 0 < c1)
    (hsing1 : ∀ x ∈ Ioo lo 1, fPosLim X.T.form (rfLim P410) (20 / 58) (bSeq X.bs) X.bs.length
      ((X.CSP : ℝ) / 58) (1 / 1024) x ≤ T1 + c1 * Real.log (1 - x))
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (har : a ≤ r) (hlb : lo ≤ b)
    (hL : ∀ x ∈ Icc a b, fPosLim X.T.form (rfLim P410) (20 / 58) (bSeq X.bs) X.bs.length
      ((X.CSP : ℝ) / 58) (1 / 1024) x ≤ Sm)
    (h0 : Tr + c * Real.log r ≤ S) (h1 : T1 + c1 * Real.log (1 - lo) ≤ S) (h2 : Sm ≤ S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (famD X N).fPosS x ≤ S + ε := by
  have hf := famD_family X hok
  have hωR := famD_R_tail X hRt
  have hcs : Tendsto (fun N => (famD X N).cs) atTop (𝓝 ((X.CSP : ℝ) / 58)) := tendsto_const_nhds
  have hRf1 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (famD X N).Rf x - rfLim P410 x ≤ ε := by
    intro ε hε
    filter_upwards [hRf_fam X hε] with N hN x hx
    exact (abs_le.mp (hN x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))).2
  have hRf2 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc a b, |(famD X N).Rf x - rfLim P410 x| ≤ ε := by
    intro ε hε
    filter_upwards [hRf_fam X hε] with N hN x hx
    exact hN x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
  refine glue3 (p := 0) (q := 1) (r0 := r) (a := a) (b := b) (r1 := lo) har hlb h0 h2 h1 ?_ ?_ ?_
  · intro ε hε
    exact fPosS_cell_zero hf hωR (by norm_num) le_rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (famD_sigma_tendsto X) hcs hRf1 hr0 hr1 hc hsing ε hε
  · exact interior_le (fPosS_unif hf ha hab hb (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (famD_sigma_tendsto X) hcs hRf2) hL
  · intro ε hε
    exact fPosS_cell_one hf hωR (by norm_num) le_rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (famD_sigma_tendsto X) hcs hRf1 hlo0 hlo1 hc1 hsing1 ε hε

/-- **Columns**: `fCol ≤ S + ε` on `(0, 1)`. -/
theorem rowSC (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    {r T0 lo T1 c1 a b Sm S : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hlim0 : ∀ s ∈ Ioo 0 r, cfLim P410 s + 2 * X.T.form.v.Tform s ≤ T0)
    (hlo0 : 0 < lo) (hlo1 : lo < 1) (hc1 : 0 < c1)
    (hsing1 : ∀ s ∈ Ioo lo 1, cfLim P410 s + 2 * X.T.form.v.Tform s ≤ T1 + c1 * Real.log (1 - s))
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (har : a ≤ r) (hlb : lo ≤ b)
    (hL : ∀ s ∈ Icc a b, cfLim P410 s + 2 * X.T.form.v.Tform s ≤ Sm)
    (h0 : T0 ≤ S) (h1 : T1 + c1 * Real.log (1 - lo) ≤ S) (h2 : Sm ≤ S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (famD X N).fCol s ≤ S + ε := by
  have hf := famD_family X hok
  have hC1 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (famD X N).Cf s - cfLim P410 s ≤ ε := by
    intro ε hε
    filter_upwards [eventually_gt_atTop 0] with N hN s hs
    rw [hCf_fam X hN]; simpa using hε.le
  have hC2 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Icc a b, |(famD X N).Cf s - cfLim P410 s| ≤ ε := by
    intro ε hε
    filter_upwards [eventually_gt_atTop 0] with N hN s hs
    rw [hCf_fam X hN]; simpa using hε.le
  refine glue3 (p := 0) (q := 1) (r0 := r) (a := a) (b := b) (r1 := lo) har hlb h0 h2 h1 ?_ ?_ ?_
  · exact fun ε hε => fCol_cell_zero hf hC1 hr0 hr1 hlim0 ε hε
  · exact interior_le (fCol_unif hf ha hab hb hC2) hL
  · exact fun ε hε => fCol_cell_one hf hC1 hlo0 hlo1 hc1 hsing1 ε hε

end

end CatalanMeasure.GenD.Signed.Data.Assembly
