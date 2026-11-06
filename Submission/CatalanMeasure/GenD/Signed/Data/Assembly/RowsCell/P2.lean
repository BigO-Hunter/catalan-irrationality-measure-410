module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.EndGlue
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Bridge
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Core
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.L1Series
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.QTau
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell.P1

@[expose] public section

/-!
# 410 assembly: cell outputs to the contract rows

Each theorem here takes hypotheses of exactly the shape the cell modules export (`…Sup` on the interior,
`…Log` end windows, the `Fq` agreement of plogs and poles and the `ℓ¹` rounding of the polynomial) and
produces one field of `Rows410` for one trial.  No cell module is imported: the instances only plug the
cell theorems in.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic

noncomputable section



/-- **σ⁺ rows (`hpos`) from the R cells at the upper corner only.**  For `x ∈ (0, 1)` the remainder
`rc α (-log (1 - x²))` is nondecreasing in `α` (`rc ≥ 0`), so the corner `α₂` bounds every `α ≤ α₂` (the interval
`[0, 1/200]` needs no corner at `α = 0`). -/
theorem rowPosHi_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {rc : ℝ} (hrc : 0 ≤ rc) {α₂ : ℝ} (Ft F : FieldQ) (Ts : List LTerm) {K : ℝ}
    (hFt : ∀ x ∈ Ioo (0 : ℝ) 1, posLim X x + rc * α₂ * (-Real.log (1 - x ^ 2)) =
      fieldTower Ft (poleF Ft.poles) 0 x + lfieldTower Ts 0 x + K +
        (X.CSP : ℝ) / 58 * (if 1 - 1 / 1024 < x then 1 else 0))
    (hpl : Ft.plogs = F.plogs) (hpo : Ft.poles = F.poles) {δ : ℚ} (hδ : l1Q Ft.poly F.poly ≤ δ)
    {g xc T : ℝ} (hg : 0 < g) (hgxc : g ≤ xc) (hxc : xc ≤ 1 - 1 / 1024)
    (hR : ∀ x ∈ Icc g xc, fieldTower F (poleF F.poles) 0 x + lfieldTower Ts 0 x ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ α₂, ∀ x ∈ Ioo (0 : ℝ) 1, g ≤ x → x < xc →
      (famD X N).fPosMR (groupedMarkedField P410 N) rc α x ≤ T + δ + K + ε := by
  have hlim : ∀ x ∈ Ico g xc, posLim X x ≤ (fun x => T + δ + K - rc * α₂ * (-Real.log (1 - x ^ 2))) x := by
    intro x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx01.1, hx01.2]
    have e := hFt x hx01
    have hi0 : (if 1 - 1 / 1024 < x then (1 : ℝ) else 0) = 0 := by rw [if_neg]; linarith [hx.2]
    rw [hi0] at e
    have := hR x ⟨hx.1, hx.2.le⟩
    have := fieldTower_le_cell Ft F hpl hpo hδ hx1 poleF
    show posLim X x ≤ T + δ + K - rc * α₂ * (-Real.log (1 - x ^ 2))
    linarith
  intro ε hε
  filter_upwards [posMS_fam X hok hRt hg (by linarith) hlim ε hε] with N hN α hα x hx hgx hxx
  have a := hN x ⟨hgx, hxx⟩
  have hL : 0 ≤ -Real.log (1 - x ^ 2) := by
    have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h2 : 1 - x ^ 2 ≤ 1 := by nlinarith
    linarith [Real.log_nonpos h1.le h2]
  unfold SignedData.fPosMR
  have : rc * α * (-Real.log (1 - x ^ 2)) ≤ rc * α₂ * (-Real.log (1 - x ^ 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα hrc) hL
  linarith

/-! ### Near-type rows: corner cells of the trapezoid `{lo ≤ α ≤ hi, 0 ≤ β ≤ α}` -/

/-- The near limit field of a family member (`RnL = -(53/58) log(1+y²) + (24/29) log|y|`). -/
abbrev nearLim (X : FamPar) (α β x : ℝ) : ℝ :=
  fNearMSLim X.T.form (fun y => -((53 : ℝ) / 58) * Real.log (1 + y ^ 2) + (24 / 29) * Real.log |y|) α β
    (20 / 58) (bSeq X.bs) X.bs.length ((X.CSP : ℝ) / 58) (1 / 1024) x

/-- Bilinear interpolation of corner values over the trapezoid, `s = (α-lo)/(hi-lo)`, `t = β/α`. -/
def bilin (lo hi T00 T01 T10 T11 α β : ℝ) : ℝ :=
  (1 - (α - lo) / (hi - lo)) * (1 - β / α) * T00 + (1 - (α - lo) / (hi - lo)) * (β / α) * T01 +
    ((α - lo) / (hi - lo)) * (1 - β / α) * T10 + ((α - lo) / (hi - lo)) * (β / α) * T11

/-- Corner mixing of an affine field: `L α β ≤ bilin` of corner bounds. -/
theorem bilin_mix {L : ℝ → ℝ → ℝ} {L0 A B : ℝ} (hL : ∀ a b, L a b = L0 + a * A + b * B)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi) {T00 T01 T10 T11 : ℝ}
    (h00 : L lo 0 ≤ T00) (h01 : L lo lo ≤ T01) (h10 : L hi 0 ≤ T10) (h11 : L hi hi ≤ T11)
    {α β : ℝ} (hα : α ∈ Icc lo hi) (hβ : β ∈ Icc 0 α) :
    L α β ≤ bilin lo hi T00 T01 T10 T11 α β := by
  have hd : 0 < hi - lo := by linarith
  have hα0 : 0 ≤ α := hlo.trans hα.1
  set s := (α - lo) / (hi - lo) with hs
  set t := β / α with ht
  have hs0 : 0 ≤ s := div_nonneg (by linarith [hα.1]) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).mpr (by linarith [hα.2])
  have ht0 : 0 ≤ t := div_nonneg hβ.1 hα0
  have ht1 : t ≤ 1 := div_le_one_of_le₀ hβ.2 hα0
  have hαs : α = (1 - s) * lo + s * hi := by rw [hs]; field_simp; ring
  have hβt : β = t * α := by
    rcases eq_or_lt_of_le hα0 with h | h
    · have hb : β = 0 := le_antisymm (h ▸ hβ.2) hβ.1
      rw [hb, ← h]; ring
    · rw [ht]; field_simp
  have e : L α β = (1 - s) * (1 - t) * L lo 0 + (1 - s) * t * L lo lo + s * (1 - t) * L hi 0 +
      s * t * L hi hi := by
    rw [hL, hL, hL, hL, hL]
    linear_combination (A + B * t) * hαs + B * hβt
  unfold bilin
  rw [← hs, ← ht, e]
  have w00 : 0 ≤ (1 - s) * (1 - t) := mul_nonneg (by linarith) (by linarith)
  have w01 : 0 ≤ (1 - s) * t := mul_nonneg (by linarith) ht0
  have w10 : 0 ≤ s * (1 - t) := mul_nonneg hs0 (by linarith)
  have w11 : 0 ≤ s * t := mul_nonneg hs0 ht0
  nlinarith [mul_le_mul_of_nonneg_left h00 w00, mul_le_mul_of_nonneg_left h01 w01,
    mul_le_mul_of_nonneg_left h10 w10, mul_le_mul_of_nonneg_left h11 w11]

theorem nearLim_affine (X : FamPar) (x : ℝ) :
    ∀ a b, nearLim X a b x = nearLim X 0 0 x + a * Glue410.nearAlphaCoef x +
      b * Glue410.nearBetaCoef X.T.form x :=
  fun a b => Glue410.fNearMSLim_affine _ _ a b _ _ _ _ _ x

/-- The finite-`N` near field is eventually below its limit plus `(1/2ν)(-log(1-x²))`, on a window `(g, 1)`. -/
theorem nearMS_fam (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {g : ℝ} (hg : 0 < g) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo g 1,
      (famD X N).fNearMS (groupedNearField P410 N) α β x ≤ nearLim X α β x +
        (1 / (2 * (famD X N).ν)) * (-Real.log (1 - x ^ 2)) + ε := by
  have hf := famD_family X hok
  have hP : Admissible P410 := D58.Odd.design_admissible
  have hRn := Glue410.hRn_window hP (c := (53 : ℝ) / 58) (c' := (24 : ℝ) / 29)
    (by norm_num [P410, D58.Odd.design]) (by norm_num [P410, D58.Odd.design])
    (Rn := fun N => groupedNearField P410 N) (fun N => rfl) hg
  have hcs : Tendsto (fun N => (famD X N).cs) atTop (𝓝 ((X.CSP : ℝ) / 58)) := tendsto_const_nhds
  have key := fNearMS_le_lim hf (famD_R_tail X hRt) (by norm_num) le_rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (famD_sigma_tendsto X) hcs (Glue410.rnPatch_err hRn)
  intro ε hε
  filter_upwards [key ε hε] with N hN α β hβ x hx
  rw [← Glue410.fNearMS_rnPatch (D := famD X N) (Rn := fun N => groupedNearField P410 N)
    (RnL := fun y => -((53 : ℝ) / 58) * Real.log (1 + y ^ 2) + (24 / 29) * Real.log |y|) (N := N)
    (α := α) (β := β) hx.1]
  exact hN α β hβ x ⟨hg.trans hx.1, hx.2⟩

/-- **Near rows (`hnear`) from the four corner bounds** on `[g, xc)`: the bound is the bilinear interpolation of the
corner thresholds. -/
theorem rowNear_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi) {g xc T00 T01 T10 T11 : ℝ} (hg : 0 < g) (hxc : xc < 1)
    (h00 : ∀ x ∈ Ico g xc, nearLim X lo 0 x ≤ T00) (h01 : ∀ x ∈ Ico g xc, nearLim X lo lo x ≤ T01)
    (h10 : ∀ x ∈ Ico g xc, nearLim X hi 0 x ≤ T10) (h11 : ∀ x ∈ Ico g xc, nearLim X hi hi x ≤ T11) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, g ≤ x →
      x < xc → (famD X N).fNearMS (groupedNearField P410 N) α β x ≤ bilin lo hi T00 T01 T10 T11 α β + ε := by
  intro ε hε
  have hf := famD_family X hok
  have h2 : ∀ᶠ N in atTop, (-Real.log (1 - xc ^ 2)) / (2 * (famD X N).ν) ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop
      (hf.hν.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually (ge_mem_nhds (by linarith))
  filter_upwards [nearMS_fam X hok hRt (half_pos hg) (ε / 2) (by linarith), h2,
    hf.hν.eventually_gt_atTop 0] with N hN hν2 hνpos α hα β hβ x hx hgx hxx
  have hgx' : x ∈ Ioo (g / 2) 1 := ⟨by linarith, hx.2⟩
  have hxpos : 0 ≤ x := hx.1.le
  have hx2 : x ^ 2 ≤ xc ^ 2 := by nlinarith
  have hlog : Real.log (1 - xc ^ 2) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log (by nlinarith) (by linarith)
  have h6 : (1 / (2 * (famD X N).ν)) * (-Real.log (1 - x ^ 2)) ≤
      (-Real.log (1 - xc ^ 2)) / (2 * (famD X N).ν) := by
    rw [one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hm := bilin_mix (L := fun a b => nearLim X a b x) (nearLim_affine X x) hlo hlh
    (h00 x ⟨hgx, hxx⟩) (h01 x ⟨hgx, hxx⟩) (h10 x ⟨hgx, hxx⟩) (h11 x ⟨hgx, hxx⟩) hα hβ
  have := hN α β hβ.1 x hgx'
  linarith

/-- **Near top rows (`hnearTop`) from the four corner bounds** on `[xc, 1)` of the shape `G + r (-log(1-x²))`; the
finite-`N` correction `(1/2ν)(-log(1-x²))` is absorbed by the margin `δ > 0` on the log coefficient. -/
theorem rowNearTop_cell (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi) {xc G00 G01 G10 G11 r00 r01 r10 r11 δ : ℝ} (hxc : 0 < xc)
    (hδ : 0 < δ)
    (h00 : ∀ x ∈ Ico xc 1, nearLim X lo 0 x ≤ G00 + r00 * (-Real.log (1 - x ^ 2)))
    (h01 : ∀ x ∈ Ico xc 1, nearLim X lo lo x ≤ G01 + r01 * (-Real.log (1 - x ^ 2)))
    (h10 : ∀ x ∈ Ico xc 1, nearLim X hi 0 x ≤ G10 + r10 * (-Real.log (1 - x ^ 2)))
    (h11 : ∀ x ∈ Ico xc 1, nearLim X hi hi x ≤ G11 + r11 * (-Real.log (1 - x ^ 2))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, xc ≤ x →
      (famD X N).fNearMS (groupedNearField P410 N) α β x ≤
        bilin lo hi G00 G01 G10 G11 α β + ε +
          (bilin lo hi r00 r01 r10 r11 α β + δ) * (-Real.log (1 - x ^ 2)) := by
  intro ε hε
  have hf := famD_family X hok
  have h1 : ∀ᶠ N in atTop, 1 / (2 * δ) ≤ (famD X N).ν := hf.hν.eventually_ge_atTop (1 / (2 * δ))
  filter_upwards [nearMS_fam X hok hRt (half_pos hxc) ε hε, h1, hf.hν.eventually_gt_atTop 0]
    with N hN h1N hνpos α hα β hβ x hx hxx
  have hgx' : x ∈ Ioo (xc / 2) 1 := ⟨by linarith, hx.2⟩
  have hL : 0 ≤ -Real.log (1 - x ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by nlinarith [hx.1, hx.2]) (by nlinarith [sq_nonneg x]))
  have hgap : 1 / (2 * (famD X N).ν) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp h1N
    nlinarith
  have h3 : (1 / (2 * (famD X N).ν)) * (-Real.log (1 - x ^ 2)) ≤ δ * (-Real.log (1 - x ^ 2)) :=
    mul_le_mul_of_nonneg_right hgap hL
  have hxI : x ∈ Ico xc 1 := ⟨hxx, hx.2⟩
  have hm := bilin_mix (L := fun a b => nearLim X a b x) (nearLim_affine X x) hlo hlh
    (h00 x hxI) (h01 x hxI) (h10 x hxI) (h11 x hxI) hα hβ
  have hsplit : bilin lo hi (G00 + r00 * (-Real.log (1 - x ^ 2))) (G01 + r01 * (-Real.log (1 - x ^ 2)))
      (G10 + r10 * (-Real.log (1 - x ^ 2))) (G11 + r11 * (-Real.log (1 - x ^ 2))) α β =
      bilin lo hi G00 G01 G10 G11 α β + bilin lo hi r00 r01 r10 r11 α β * (-Real.log (1 - x ^ 2)) := by
    unfold bilin; ring
  rw [hsplit] at hm
  have := hN α β hβ.1 x hgx'
  nlinarith


/-! ### The spike environment from the Frostman cells -/

theorem famD_R_fin (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    (N : ℕ) : ∀ k, (famD X N).R k = X.T.form.R.f (k + 1) := by
  have h := famD_spec X hok N
  have hRt' : X.T.form.R.tail = [] := by simp [TrialQ.form, SeqQ.form, hRt]
  intro k
  rw [TrialForm.R_eq h]
  simp [hRt', gseq]

theorem famD_R_zeroL (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    (N : ℕ) : ∀ k, X.T.form.R.L ≤ k → (famD X N).R k = 0 := by
  intro k hk
  rw [famD_R_fin X hok hRt N]
  exact (famD_spec X hok N).hRf (k + 1) (by omega)

theorem refTilt_succ (R : ℕ → ℝ) (k : ℕ) :
    refTilt R (k + 1) = -(-1 : ℝ) ^ (k + 1) * R k / ((k + 1 : ℕ) : ℝ) := by
  simp [refTilt]

/-- **`SpikeEnv` of the family members** from a Frostman bound `frLim ≤ S0 < Sup` at `τ = 1` on
`[-1, 1]` (the FR cells): `|Q_τ - Q_1| ≤ e Σ |R_k|` (`qTau_sub_le_fin`) and `e = dampE N → 0`. -/
theorem famD_spikeEnv (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (hRt : X.T.R.tail = [])
    {S0 : ℝ} (hfr : ∀ x ∈ Icc (-1 : ℝ) 1, frLim X.T.form x ≤ S0) (hgap : S0 < X.T.Sup) :
    ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (famD X N)) := by
  set L := X.T.form.R.L
  set SR : ℝ := ∑ k ∈ Finset.range L, |X.T.form.R.f (k + 1)|
  have hd : Tendsto (fun N : ℕ => dampE N * SR) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => dampE N) atTop (𝓝 0) := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
      have := (h.inv_tendsto_atTop).const_mul (1 / 2 ^ 30 : ℝ)
      simpa [dampE, div_eq_mul_inv] using this
    simpa using this.mul_const SR
  filter_upwards [hd.eventually (gt_mem_nhds (sub_pos.mpr hgap)), eventually_gt_atTop 0] with N hN hN0
  have h := famD_spec X hok N
  have hR := famD_R_fin X hok hRt N
  have hR0 := famD_R_zeroL X hok hRt N
  have he := dampE_mem N
  have hfs : ∀ {f : ℕ → ℝ}, (∀ k, L ≤ k → f k = 0) → HasSum f (∑ k ∈ Finset.range L, f k) :=
    fun hf => hasSum_sum_of_ne_finset_zero (fun k hk => hf k (by simpa using hk))
  refine ⟨{
    hν := by show (0 : ℝ) < 58 * (N : ℝ); positivity
    he := he
    hsp := by show ((20 * N : ℕ) : ℝ) ≤ 58 * (N : ℝ); push_cast; nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    hθ := by show (1 / 1024 : ℝ) ∈ Ioo (0 : ℝ) 1; constructor <;> norm_num
    ha := Glue410.Spec_summable_a h
    hr := (hfs (fun k hk => by rw [refTilt_succ, hR0 k hk]; simp)).summable
    hra := (hfs (fun k hk => by rw [refTilt_succ, hR0 k hk]; simp)).summable
    Qref := fun x => ∑ k ∈ Finset.range L, refTilt (famD X N).R (k + 1) *
      realEnergyTau (famD X N).e ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x
    hQ := fun x _ => hfs (fun k hk => by rw [refTilt_succ, hR0 k hk]; simp)
    hℓ := ?_
    hbK := fun i hi => by
      show bSeq X.bs i = 0
      have hi' : X.bs.length < i := hi
      unfold bSeq
      rw [if_neg (by omega), List.getD_eq_default _ _ (by omega)]
      simp }⟩
  intro x hx
  have hx1 : |x| ≤ 1 := abs_le.mpr hx
  have hQt := hfs (f := fun k => (-(-1 : ℝ) ^ (k + 1) * (famD X N).R k / ((k + 1 : ℕ) : ℝ)) *
      (1 - dampE N) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)
    (fun k hk => by rw [hR0 k hk]; simp)
  have hQ1 := hfs (f := fun k => (-(-1 : ℝ) ^ (k + 1) * (famD X N).R k / ((k + 1 : ℕ) : ℝ)) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)
    (fun k hk => by rw [hR0 k hk]; simp)
  have hq := Data.Cells.qTau_sub_le_fin (K := L) he.1.le (by linarith [he.2]) hR0 hx hQt hQ1
  have hsum : ∑ k ∈ Finset.range L, |(famD X N).R k| = SR := by
    simp only [SR, hR]
  rw [hsum] at hq
  have hfr' := hfr x hx
  have hTa : barrierTrialT (famD X N).a x = X.T.form.a.Tform x := by
    rw [h.ha]; exact barrierTrialT_tseq h.haf h.haT hx1
  have hQ1e : ∑ k ∈ Finset.range L, (-(-1 : ℝ) ^ (k + 1) * (famD X N).R k / ((k + 1 : ℕ) : ℝ)) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x = frLim X.T.form x + 2 * X.T.form.a.Tform x := by
    unfold frLim
    rw [sub_add_cancel]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hR k, pow_succ]
    ring
  have hQte : (∑ k ∈ Finset.range L, refTilt (famD X N).R (k + 1) *
      realEnergyTau (famD X N).e ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) =
      ∑ k ∈ Finset.range L, (-(-1 : ℝ) ^ (k + 1) * (famD X N).R k / ((k + 1 : ℕ) : ℝ)) *
        (1 - dampE N) ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [refTilt_succ]; rfl
  show _ - 2 * barrierTrialT (famD X N).a x ≤ (X.T.Sup : ℝ)
  rw [hQte, hTa]
  rw [hQ1e] at hq
  have := (abs_le.mp hq).2
  have hSup : X.T.form.Sup = (X.T.Sup : ℝ) := rfl
  linarith

/-! ### Helpers for the row instances (`RowsQ0`–`RowsQ2`) -/

/-- `l1Q` with structural recursion on the first list (the kernel evaluates it; `l1Q` itself is
well-founded because its `[]` case recurses on the second list). -/
def l1S : List ℚ → List ℚ → ℚ
  | [], bs => (bs.map qAbs).sum
  | a :: as, [] => qAbs a + l1S as []
  | a :: as, b :: bs => qAbs (a - b) + l1S as bs

theorem l1Q_nil_left (bs : List ℚ) : l1Q [] bs = (bs.map qAbs).sum := by
  induction bs with
  | nil => simp [l1Q]
  | cons b bs ih => simp [l1Q, ih]

theorem l1Q_eq_l1S (as bs : List ℚ) : l1Q as bs = l1S as bs := by
  induction as generalizing bs with
  | nil => simp [l1S, l1Q_nil_left]
  | cons a as ih => cases bs <;> simp [l1Q, l1S, ih]

/-- The end-window comparison `TR + U + c log (endR) ≤ T` carried by `endUOK`. -/
theorem endUOK_cmp {fq : FieldQ} {ts : List LTerm} {e lo hi : ℚ} {k kR : ℕ} {U TR T : ℚ}
    (hchk : endUOK fq ts e lo hi k kR U TR T = true) :
    (TR : ℝ) + U + (endC fq ts e : ℝ) * Real.log (endR e lo hi : ℝ) ≤ T := by
  unfold endUOK at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨h1, hc⟩, hRk⟩, hT⟩ := hchk
  unfold endOK at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨hle, hel⟩, hR0⟩, hR3⟩, hk⟩, -⟩, -⟩ := h1
  have hlog2 : Real.log ((endR e lo hi : ℚ) : ℝ) ≤ -(69 / 100 * (kR : ℝ)) := by
    have h2 : ((endR e lo hi : ℚ) : ℝ) ≤ ((1 : ℝ) / 2) ^ kR := by
      have := (Rat.cast_le (K := ℝ)).mpr hRk; push_cast at this; exact this
    have hR0' : (0 : ℝ) < (endR e lo hi : ℝ) := by exact_mod_cast hR0
    have h3 := Real.log_le_log hR0' h2
    rw [Real.log_pow, one_div, Real.log_inv] at h3
    have := Real.log_two_gt_d9
    have hk0 : (0 : ℝ) ≤ kR := Nat.cast_nonneg kR
    nlinarith
  have hc' : (0 : ℝ) ≤ (endC fq ts e : ℝ) := by exact_mod_cast hc
  have hT' : ((TR + U - endC fq ts e * (69 / 100 * (kR : ℚ)) : ℚ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  push_cast at hT'
  have := mul_le_mul_of_nonneg_left hlog2 hc'
  linarith

theorem endR_one {lo : ℚ} (h : lo ≤ 1) : endR 1 lo 1 = 1 - lo := by
  unfold endR qmax; split_ifs <;> linarith

theorem endR_zero {lo : ℚ} (h : lo ≤ 0) : endR 0 lo 0 = -lo := by
  unfold endR qmax; split_ifs <;> linarith

/-- **A log-form end window at `E`** of a cell field `fq` on `[lo, hi]` (`hi` the cover end), as the end
modules export it (`…Log`, `…End`, `…Cpos`), with `lo` strictly inside `(lo₀, E)` or `(E, lo₀)`. -/
def EndW (fq : FieldQ) (E hi T : ℚ) (inside : ℚ → Prop) : Prop :=
  ∃ (lo TR U : ℚ) (k kR : ℕ), inside lo ∧
    (∀ x ∈ Icc ((lo : ℚ) : ℝ) ((hi : ℚ) : ℝ), x ≠ ((E : ℚ) : ℝ) →
      fieldTower fq (poleF fq.poles) 0 x ≤ ((TR : ℚ) : ℝ) + ((U : ℚ) : ℝ) +
        ((endC fq [] E : ℚ) : ℝ) * Real.log |x - ((E : ℚ) : ℝ)|) ∧
    endUOK fq [] E lo hi k kR U TR T = true ∧ 0 < endC fq [] E

theorem chord_mono {lo hi a b c d α : ℝ} (hac : a ≤ c) (hbd : b ≤ d) : chord lo hi a b α ≤ chord lo hi c d α := by
  unfold chord
  have h0 := interpL_nonneg lo hi α
  have h1 := interpL_le_one lo hi α
  nlinarith

theorem bilin_mono {lo hi T00 T01 T10 T11 U00 U01 U10 U11 α β : ℝ} (hlo : lo < hi) (hα : α ∈ Icc lo hi)
    (hβ : β ∈ Icc 0 α) (h00 : T00 ≤ U00) (h01 : T01 ≤ U01) (h10 : T10 ≤ U10) (h11 : T11 ≤ U11) :
    bilin lo hi T00 T01 T10 T11 α β ≤ bilin lo hi U00 U01 U10 U11 α β := by
  have hd : 0 < hi - lo := by linarith
  have hs0 : 0 ≤ (α - lo) / (hi - lo) := div_nonneg (by linarith [hα.1]) hd.le
  have hs1 : (α - lo) / (hi - lo) ≤ 1 := div_le_one_of_le₀ (by linarith [hα.2]) hd.le
  have ht0 : 0 ≤ β / α := div_nonneg hβ.1 (hβ.1.trans hβ.2)
  have ht1 : β / α ≤ 1 := div_le_one_of_le₀ hβ.2 (hβ.1.trans hβ.2)
  unfold bilin
  have a1 : 0 ≤ (1 - (α - lo) / (hi - lo)) * (1 - β / α) := mul_nonneg (by linarith) (by linarith)
  have a2 : 0 ≤ (1 - (α - lo) / (hi - lo)) * (β / α) := mul_nonneg (by linarith) ht0
  have a3 : 0 ≤ ((α - lo) / (hi - lo)) * (1 - β / α) := mul_nonneg hs0 (by linarith)
  have a4 : 0 ≤ ((α - lo) / (hi - lo)) * (β / α) := mul_nonneg hs0 ht0
  nlinarith [mul_le_mul_of_nonneg_left h00 a1, mul_le_mul_of_nonneg_left h01 a2,
    mul_le_mul_of_nonneg_left h10 a3, mul_le_mul_of_nonneg_left h11 a4]

/-- `bilin` of the corner values `0, c lo, 0, c hi` of `c β` is `c β`. -/
theorem bilin_lin {lo hi c α β : ℝ} (hlo : lo < hi) (hα0 : 0 < α) :
    bilin lo hi 0 (c * lo) 0 (c * hi) α β = c * β := by
  have hd : hi - lo ≠ 0 := by linarith
  unfold bilin
  field_simp
  ring

end

end CatalanMeasure.GenD.Signed.Data.Assembly
