module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

@[expose] public section

/-!
# 410 assembly: the cap data and the budget rows

The off-top and top-cell bounds of the fixed-row fields at the endpoint trials of each `α`-interval
are the threshold-table values `S_Lean` (rounded up to `2^-40`): chords in `α` of the corner values
for the positive field, bilinear interpolations in `(α, β)` (`bilin`) of the corner values for the
near field.  The log coefficients are `rP α = remC (1/10) α` and `rS = α / 2 + 10^-6`.

`zb410` bounds `zbCap` by `α max(ℓN, ℓP, ℓS) + C₁ (r_P e^{Bd/r_P} + r_S e^{Bd/r_S})`: the lines `ℓ`
are secants above the off-top chords, and `capInt c r θ ≤ r e^{Bd/r}` for a gap `c ≤ Bd < 0`.
The budget inequalities `hbudLo`, `hbudHi` are then, for each line, quadratic in `α` once the cap
term is bounded by a constant on each piece of the interval (`e^{-k} ≤ (3/8)^k`) and `log 2` by its
upper bound; each piece is closed by `quad_nonpos_Icc`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.D58

noncomputable section

namespace Bud410

/-! ### Generic lemmas -/

theorem conv_le {l x y B : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (hx : x ≤ B) (hy : y ≤ B) :
    (1 - l) * x + l * y ≤ B := by nlinarith

theorem chord_le {lo hi x y B α : ℝ} (hx : x ≤ B) (hy : y ≤ B) : chord lo hi x y α ≤ B :=
  conv_le (interpL_nonneg _ _ _) (interpL_le_one _ _ _) hx hy

theorem chord_sub (lo hi a b c d α : ℝ) :
    chord lo hi a b α - chord lo hi c d α = chord lo hi (a - c) (b - d) α := by
  unfold chord; ring

theorem chord_const (lo hi v α : ℝ) : chord lo hi v v α = v := by unfold chord; ring

theorem bilin_sub (lo hi T00 T01 T10 T11 U00 U01 U10 U11 α β : ℝ) :
    bilin lo hi T00 T01 T10 T11 α β - bilin lo hi U00 U01 U10 U11 α β =
      bilin lo hi (T00 - U00) (T01 - U01) (T10 - U10) (T11 - U11) α β := by
  unfold bilin; ring

theorem s_mem {lo hi α : ℝ} (hlo : lo < hi) (hα : α ∈ Icc lo hi) :
    0 ≤ (α - lo) / (hi - lo) ∧ (α - lo) / (hi - lo) ≤ 1 :=
  ⟨div_nonneg (by linarith [hα.1]) (by linarith), div_le_one_of_le₀ (by linarith [hα.2]) (by linarith)⟩

theorem t_mem {α β : ℝ} (hβ : β ∈ Icc 0 α) : 0 ≤ β / α ∧ β / α ≤ 1 :=
  ⟨div_nonneg hβ.1 (hβ.1.trans hβ.2), div_le_one_of_le₀ hβ.2 (hβ.1.trans hβ.2)⟩

theorem bilin_eq (lo hi T00 T01 T10 T11 α β : ℝ) : bilin lo hi T00 T01 T10 T11 α β =
    (1 - (α - lo) / (hi - lo)) * ((1 - β / α) * T00 + β / α * T01) +
      (α - lo) / (hi - lo) * ((1 - β / α) * T10 + β / α * T11) := by
  unfold bilin; ring

theorem bilin_le {lo hi T00 T01 T10 T11 B α β : ℝ} (hlo : lo < hi) (hα : α ∈ Icc lo hi)
    (hβ : β ∈ Icc 0 α) (h00 : T00 ≤ B) (h01 : T01 ≤ B) (h10 : T10 ≤ B) (h11 : T11 ≤ B) :
    bilin lo hi T00 T01 T10 T11 α β ≤ B := by
  obtain ⟨hs0, hs1⟩ := s_mem hlo hα
  obtain ⟨ht0, ht1⟩ := t_mem hβ
  rw [bilin_eq]
  exact conv_le hs0 hs1 (conv_le ht0 ht1 h00 h01) (conv_le ht0 ht1 h10 h11)

/-- The near bound at `β ≤ α` is at most its value at `β = α` (corner values increasing in `β`). -/
theorem bilin_le_top {lo hi T00 T01 T10 T11 α β : ℝ} (hlo : lo < hi) (hα : α ∈ Icc lo hi)
    (hβ : β ∈ Icc 0 α) (h0 : T00 ≤ T01) (h1 : T10 ≤ T11) :
    bilin lo hi T00 T01 T10 T11 α β ≤
      (1 - (α - lo) / (hi - lo)) * T01 + (α - lo) / (hi - lo) * T11 := by
  obtain ⟨hs0, hs1⟩ := s_mem hlo hα
  obtain ⟨ht0, ht1⟩ := t_mem hβ
  rw [bilin_eq]
  have a0 : (1 - β / α) * T00 + β / α * T01 ≤ T01 := by nlinarith
  have a1 : (1 - β / α) * T10 + β / α * T11 ≤ T11 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left a0 (by linarith : (0 : ℝ) ≤ 1 - (α - lo) / (hi - lo)),
    mul_le_mul_of_nonneg_left a1 hs0]

/-- A chord of two chords lies below the secant when `A₁ + B₀ ≤ A₀ + B₁`. -/
theorem quad_chord_le {l A0 A1 B0 B1 : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (hc : A1 + B0 ≤ A0 + B1) :
    (1 - l) * ((1 - l) * A0 + l * A1) + l * ((1 - l) * B0 + l * B1) ≤ (1 - l) * A0 + l * B1 := by
  have e : (1 - l) * A0 + l * B1 - ((1 - l) * ((1 - l) * A0 + l * A1) + l * ((1 - l) * B0 + l * B1)) =
      l * (1 - l) * ((A0 + B1) - (A1 + B0)) := by ring
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - l))
    (by linarith : (0 : ℝ) ≤ (A0 + B1) - (A1 + B0))]

/-- The cap term `r e^{Bd/r}` (`0` at `r = 0`). -/
def cb (Bd r : ℝ) : ℝ := r * Real.exp (Bd / r)

theorem capInt_le_cb {c r θ Bd : ℝ} (hθ : 0 < θ) (hBd : Bd < 0) (hc : c ≤ Bd) (hr : 0 ≤ r) :
    capInt c r θ ≤ cb Bd r := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    unfold capInt cb
    rw [if_neg (lt_irrefl (0 : ℝ)), max_eq_left (by linarith : c ≤ 0)]
    simp
  · refine (capInt_le_mul_exp hpos hθ).trans ?_
    unfold cb
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (div_le_div_of_nonneg_right hc hpos.le)) hpos.le

theorem cb_mono {Bd r R : ℝ} (hBd : Bd ≤ 0) (hr : 0 ≤ r) (hrR : r ≤ R) (hR : 0 < R) :
    cb Bd r ≤ cb Bd R := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0; unfold cb; simp only [zero_mul]; exact (mul_pos hR (Real.exp_pos _)).le
  · exact Glue410.mul_exp_mono hBd hpos hrR

theorem exp_neg_nat_add_le (k : ℕ) {f : ℝ} (hf : 0 ≤ f) :
    Real.exp (-((k : ℝ) + f)) ≤ (3 / 8) ^ k * (1 / (1 + f + f ^ 2 / 2)) := by
  have h1 : Real.exp (-1) ≤ 3 / 8 := by
    have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
  have e : -((k : ℝ) + f) = (k : ℝ) * (-1) + -f := by ring
  rw [e, Real.exp_add, Real.exp_nat_mul]
  exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le h1 k) (Glue410.exp_neg_le_inv_quad hf)
    (Real.exp_pos _).le (by positivity)

theorem cb_le_num {Bd R : ℝ} (k : ℕ) (f : ℝ) (hR : 0 < R) (hy : Bd / R = -((k : ℝ) + f))
    (hf : 0 ≤ f) : cb Bd R ≤ R * ((3 / 8) ^ k * (1 / (1 + f + f ^ 2 / 2))) := by
  unfold cb; rw [hy]; exact mul_le_mul_of_nonneg_left (exp_neg_nat_add_le k hf) hR.le

/-- One piece of one budget line: quadratic in `α` once `log 2 ≤ Lup` (with a nonnegative
coefficient) and the cap term `≤ K`. -/
theorem bud_piece {a1 a2 α L Lup K cap e0 e1 e2 f0 f1 f2 p q : ℝ} (h1 : a1 ≤ α) (h2 : α ≤ a2)
    (hL : L ≤ Lup) (hF : 0 ≤ f0 + f1 * α + f2 * α ^ 2) (hK : cap ≤ K)
    (q0 : (e0 + Lup * f0 + K) + (e1 + Lup * f1 + p) * a1 + (e2 + Lup * f2 + q) * a1 ^ 2 ≤ 0)
    (q1 : (e0 + Lup * f0 + K) + (e1 + Lup * f1 + p) * a2 + (e2 + Lup * f2 + q) * a2 ^ 2 ≤ 0)
    (hs : 0 ≤ e2 + Lup * f2 + q ∨ (e1 + Lup * f1 + p) + 2 * (e2 + Lup * f2 + q) * a1 ≤ 0 ∨
      0 ≤ (e1 + Lup * f1 + p) + 2 * (e2 + Lup * f2 + q) * a2 ∨
      (e1 + Lup * f1 + p) ^ 2 ≤ 4 * (e0 + Lup * f0 + K) * (e2 + Lup * f2 + q)) :
    e0 + e1 * α + e2 * α ^ 2 + L * (f0 + f1 * α + f2 * α ^ 2) + α * (p + q * α) + cap ≤ 0 := by
  have hq := quad_nonpos_Icc q0 q1 hs h1 h2
  have hLF := mul_le_mul_of_nonneg_right hL hF
  have e : e0 + e1 * α + e2 * α ^ 2 + L * (f0 + f1 * α + f2 * α ^ 2) + α * (p + q * α) + cap =
      ((e0 + Lup * f0 + K) + (e1 + Lup * f1 + p) * α + (e2 + Lup * f2 + q) * α ^ 2) +
        (L * (f0 + f1 * α + f2 * α ^ 2) - Lup * (f0 + f1 * α + f2 * α ^ 2)) + (cap - K) := by ring
  rw [e]; linarith

theorem constLim410 (α : ℝ) : Glue410.constantLim P410 α =
    ((1 - α) * (75 / 58) + α * (53 / 58) + (1 - α) ^ 2 / 2) * Real.log 2 := by
  simp only [Glue410.constantLim, gKappa, gRes, P410, D58.Odd.design]
  norm_num

theorem log2_le : Real.log 2 ≤ 6931471808 / 10 ^ 10 := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

/-- `zbCap` of the chord cap data, from bounds `M` of the three off-top bounds and the gaps. -/
theorem zb_bound (E : CapEnd) (lo hi Bd M rSv : ℝ) (hBd : Bd < 0) (hxc : E.xc < 1) (hC1 : 0 ≤ E.C1)
    {c d e : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hN : (E.toS lo hi).lamN (c + d + e) ≤ M) (hP : (E.toS lo hi).lamP (c + d + e) ≤ M)
    (hS : (E.toS lo hi).lamS (c + d + e) e ≤ M)
    (hgP : (E.toS lo hi).gP (c + d + e) - (E.toS lo hi).lamP (c + d + e) ≤ Bd)
    (hgS : (E.toS lo hi).gS (c + d + e) e - (E.toS lo hi).lamS (c + d + e) e ≤ Bd)
    (hrP : 0 ≤ (E.toS lo hi).rP (c + d + e)) (hrS : (E.toS lo hi).rS (c + d + e) e = rSv)
    (hrS0 : 0 ≤ rSv) :
    zbCap (E.toS lo hi) c d e ≤
      (c + d + e) * M + E.C1 * (cb Bd ((E.toS lo hi).rP (c + d + e)) + cb Bd rSv) := by
  have hθ : 0 < 1 - (E.toS lo hi).xc := by show 0 < 1 - E.xc; linarith
  have h1 := capInt_le_cb hθ hBd hgP hrP
  have h2 := capInt_le_cb hθ hBd hgS (hrS ▸ hrS0)
  rw [hrS] at h2
  have k1 := mul_le_mul_of_nonneg_left hN hc
  have k2 := mul_le_mul_of_nonneg_left hP hd
  have k3 := mul_le_mul_of_nonneg_left hS he
  have hC := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC1
  have hC1' : (E.toS lo hi).C1 = E.C1 := rfl
  unfold zbCap
  rw [hC1', hrS]
  nlinarith [k1, k2, k3, hC]

/-! ### Interval 0: `[0, 1/200]` -/

def capE0 : CapEnd where
  gs := 401 / 2500
  xc := 999 / 1000
  C1 := 9631 / 20000
  lamNA := (-488972311 / 1073741824 : ℝ)
  lamNB := (-488072065 / 1073741824 : ℝ)
  lamPA := fun α => chord (0 : ℝ) (1 / 200 : ℝ) (-633965405 / 1073741824 : ℝ) (-633965405 / 1073741824 : ℝ) α
  lamPB := fun α => chord (0 : ℝ) (1 / 200 : ℝ) (-316109909 / 536870912 : ℝ) (-316109909 / 536870912 : ℝ) α
  gPA := fun _ => (-263377245 / 268435456 : ℝ)
  gPB := fun _ => (-525686503 / 536870912 : ℝ)
  rP := fun α => 11 / 8 * α
  lamSA := fun α β => bilin (0 : ℝ) (1 / 200 : ℝ) (-633977113 / 1073741824 : ℝ) (-633977113 / 1073741824 : ℝ) (-630855881 / 1073741824 : ℝ) (-154883223 / 268435456 : ℝ) α β
  lamSB := fun α β => bilin (0 : ℝ) (1 / 200 : ℝ) (-316450799 / 536870912 : ℝ) (-316450799 / 536870912 : ℝ) (-629779419 / 1073741824 : ℝ) (-309226913 / 536870912 : ℝ) α β
  gSA := fun α β => bilin (0 : ℝ) (1 / 200 : ℝ) (-524406595 / 536870912 : ℝ) (-524406595 / 536870912 : ℝ) (-1045093195 / 1073741824 : ℝ) (-258714901 / 268435456 : ℝ) α β
  gSB := fun α β => bilin (0 : ℝ) (1 / 200 : ℝ) (-522714931 / 536870912 : ℝ) (-522714931 / 536870912 : ℝ) (-260427467 / 268435456 : ℝ) (-515738139 / 536870912 : ℝ) α β
  rSA := fun α _ => α / 2 + 1 / 1000000
  rSB := fun α _ => α / 2 + 1 / 1000000

def lineN0 (α : ℝ) : ℝ := chord (0 : ℝ) (1 / 200 : ℝ) (-488972311 / 1073741824 : ℝ) (-488072065 / 1073741824 : ℝ) α
def lineP0 (α : ℝ) : ℝ := chord (0 : ℝ) (1 / 200 : ℝ) (-633965405 / 1073741824 : ℝ) (-316109909 / 536870912 : ℝ) α
def lineS0 (α : ℝ) : ℝ := chord (0 : ℝ) (1 / 200 : ℝ) (-633977113 / 1073741824 : ℝ) (-309226913 / 536870912 : ℝ) α
def cap0 (α : ℝ) : ℝ := 9631 / 20000 * (cb (-19 / 50 : ℝ) (11 / 8 * α) + cb (-19 / 50 : ℝ) (α / 2 + 1 / 1000000))
def zb0 (α : ℝ) : ℝ := α * max (lineN0 α) (max (lineP0 α) (lineS0 α)) + cap0 α

theorem gapP0 (α : ℝ) : (capE0.gPA α - capE0.lamPA α ≤ (-19 / 50 : ℝ)) ∧ (capE0.gPB α - capE0.lamPB α ≤ (-19 / 50 : ℝ)) := by
  constructor
  · show (-263377245 / 268435456 : ℝ) - chord _ _ _ _ α ≤ _
    rw [← chord_const (0 : ℝ) (1 / 200 : ℝ) (-263377245 / 268435456 : ℝ) α, chord_sub]; exact chord_le (by norm_num) (by norm_num)
  · show (-525686503 / 536870912 : ℝ) - chord _ _ _ _ α ≤ _
    rw [← chord_const (0 : ℝ) (1 / 200 : ℝ) (-525686503 / 536870912 : ℝ) α, chord_sub]; exact chord_le (by norm_num) (by norm_num)

theorem gapS0 {α β : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 200 : ℝ)) (hβ : β ∈ Icc 0 α) :
    (capE0.gSA α β - capE0.lamSA α β ≤ (-19 / 50 : ℝ)) ∧ (capE0.gSB α β - capE0.lamSB α β ≤ (-19 / 50 : ℝ)) := by
  constructor
  · show bilin _ _ _ _ _ _ α β - bilin _ _ _ _ _ _ α β ≤ _
    rw [bilin_sub]
    exact bilin_le (by norm_num) hα hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show bilin _ _ _ _ _ _ α β - bilin _ _ _ _ _ _ α β ≤ _
    rw [bilin_sub]
    exact bilin_le (by norm_num) hα hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lamP_le0 (α : ℝ) : (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).lamP α ≤ lineP0 α := by
  show chord _ _ (chord _ _ _ _ α) (chord _ _ _ _ α) α ≤ chord _ _ _ _ α
  unfold chord
  exact quad_chord_le (interpL_nonneg _ _ _) (interpL_le_one _ _ _) (by norm_num)

theorem lamS_le0 {α β : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 200 : ℝ)) (hβ : β ∈ Icc 0 α) :
    (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).lamS α β ≤ lineS0 α := by
  have hl : interpL (0 : ℝ) (1 / 200 : ℝ) α = (α - (0 : ℝ)) / ((1 / 200 : ℝ) - (0 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  obtain ⟨hs0, hs1⟩ := s_mem (show (0 : ℝ) < (1 / 200 : ℝ) by norm_num) hα
  have hA := bilin_le_top (T00 := (-633977113 / 1073741824 : ℝ)) (T01 := (-633977113 / 1073741824 : ℝ)) (T10 := (-630855881 / 1073741824 : ℝ)) (T11 := (-154883223 / 268435456 : ℝ))
    (show (0 : ℝ) < (1 / 200 : ℝ) by norm_num) hα hβ (by norm_num) (by norm_num)
  have hB := bilin_le_top (T00 := (-316450799 / 536870912 : ℝ)) (T01 := (-316450799 / 536870912 : ℝ)) (T10 := (-629779419 / 1073741824 : ℝ)) (T11 := (-309226913 / 536870912 : ℝ))
    (show (0 : ℝ) < (1 / 200 : ℝ) by norm_num) hα hβ (by norm_num) (by norm_num)
  show chord _ _ (bilin _ _ _ _ _ _ α β) (bilin _ _ _ _ _ _ α β) α ≤ chord _ _ _ _ α
  unfold chord
  rw [hl]
  have h1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 1 - (α - (0 : ℝ)) / ((1 / 200 : ℝ) - (0 : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left hB hs0
  have h3 := quad_chord_le (A0 := (-633977113 / 1073741824 : ℝ)) (A1 := (-154883223 / 268435456 : ℝ)) (B0 := (-316450799 / 536870912 : ℝ)) (B1 := (-309226913 / 536870912 : ℝ)) hs0 hs1 (by norm_num)
  linarith

theorem hZB0 (c d e : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (h1 : (0 : ℝ) ≤ c + d + e)
    (h2 : c + d + e ≤ (1 / 200 : ℝ)) : zbCap (capE0.toS (0 : ℝ) (1 / 200 : ℝ)) c d e ≤ zb0 (c + d + e) := by
  have hα : c + d + e ∈ Icc (0 : ℝ) (1 / 200 : ℝ) := ⟨h1, h2⟩
  have hβ : e ∈ Icc 0 (c + d + e) := ⟨he, by linarith⟩
  have hM1 := le_max_left (lineN0 (c + d + e)) (max (lineP0 (c + d + e)) (lineS0 (c + d + e)))
  have hM2 := (le_max_left (lineP0 (c + d + e)) (lineS0 (c + d + e))).trans (le_max_right (lineN0 (c + d + e)) _)
  have hM3 := (le_max_right (lineP0 (c + d + e)) (lineS0 (c + d + e))).trans (le_max_right (lineN0 (c + d + e)) _)
  have hgP : (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).gP (c + d + e) - (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).lamP (c + d + e) ≤ (-19 / 50 : ℝ) := by
    show chord _ _ _ _ _ - chord _ _ _ _ _ ≤ _
    rw [chord_sub]; exact chord_le (gapP0 _).1 (gapP0 _).2
  have hgS : (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).gS (c + d + e) e - (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).lamS (c + d + e) e ≤ (-19 / 50 : ℝ) := by
    show chord _ _ _ _ _ - chord _ _ _ _ _ ≤ _
    rw [chord_sub]; exact chord_le (gapS0 hα hβ).1 (gapS0 hα hβ).2
  have hrS : (capE0.toS (0 : ℝ) (1 / 200 : ℝ)).rS (c + d + e) e = (c + d + e) / 2 + 1 / 1000000 := by
    show chord _ _ ((c + d + e) / 2 + 1 / 1000000) ((c + d + e) / 2 + 1 / 1000000) _ = _
    rw [chord_const]
  exact zb_bound capE0 (0 : ℝ) (1 / 200 : ℝ) (-19 / 50 : ℝ) _ _ (by norm_num) (by show (999 / 1000 : ℝ) < 1; norm_num)
    (by show (0 : ℝ) ≤ 9631 / 20000; norm_num) hc hd he hM1 ((lamP_le0 _).trans hM2)
    ((lamS_le0 hα hβ).trans hM3) hgP hgS (by show (0 : ℝ) ≤ 11 / 8 * (c + d + e); linarith) hrS
    (by linarith)

theorem F_nonneg0 {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 200 : ℝ)) : 0 ≤ (75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2 := by
  have := quad_nonpos_Icc (a := (-75 / 58 : ℝ)) (b := (-621 / 580 : ℝ)) (c := (69 / 80 : ℝ)) (by norm_num) (by norm_num)
    (Or.inl (by norm_num)) hα.1 hα.2
  linarith

theorem cap0_0 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (1 / 200 : ℝ)) : cap0 α ≤ (1 / 1152921504606846976 : ℝ) := by
  unfold cap0
  have e1 := cb_mono (Bd := (-19 / 50 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (11 / 1600 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-19 / 50 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (2501 / 1000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-19 / 50 : ℝ)) (R := (11 / 1600 : ℝ)) 55 (3 / 11 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-19 / 50 : ℝ)) (R := (2501 / 1000000 : ℝ)) 151 (2349 / 2501 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-19 / 50 : ℝ) (11 / 8 * α) + cb (-19 / 50 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((11 / 1600 : ℝ) * ((3 / 8) ^ 55 * (1 / (1 + (3 / 11 : ℝ) + (3 / 11 : ℝ) ^ 2 / 2))) +
          (2501 / 1000000 : ℝ) * ((3 / 8) ^ 151 * (1 / (1 + (2349 / 2501 : ℝ) + (2349 / 2501 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (1 / 1152921504606846976 : ℝ) := by norm_num

theorem bud0lo : ∀ α ∈ Icc (0 : ℝ) (1 / 200 : ℝ),
    interpCInf (0 : ℝ) (1 / 200 : ℝ) (Glue410.constantLim P410 α) (30870737 / 200000000 : ℝ) (145423449 / 1000000000 : ℝ) (14003 / 1000000000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (3 / 10 : ℝ) * chord (0 : ℝ) (1 / 200 : ℝ) (-1913689396221 / 1099511627776 : ℝ) (-1911012921633 / 1099511627776 : ℝ) α + (1 - (3 / 10 : ℝ) - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1868836503 / 1073741824 : ℝ) (-466555285 / 268435456 : ℝ) α +
      (1 - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1724586542717 / 1099511627776 : ℝ) (-858707041103 / 549755813888 : ℝ) α + zb0 α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α := by
  intro α hα
  have hl : interpL (0 : ℝ) (1 / 200 : ℝ) α = (α - (0 : ℝ)) / ((1 / 200 : ℝ) - (0 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  have hE : interpCInf (0 : ℝ) (1 / 200 : ℝ) (Glue410.constantLim P410 α) (30870737 / 200000000 : ℝ) (145423449 / 1000000000 : ℝ) (14003 / 1000000000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (3 / 10 : ℝ) * chord (0 : ℝ) (1 / 200 : ℝ) (-1913689396221 / 1099511627776 : ℝ) (-1911012921633 / 1099511627776 : ℝ) α + (1 - (3 / 10 : ℝ) - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1868836503 / 1073741824 : ℝ) (-466555285 / 268435456 : ℝ) α +
      (1 - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1724586542717 / 1099511627776 : ℝ) (-858707041103 / 549755813888 : ℝ) α -
      ((-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α) =
      (-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) := by
    rw [constLim410]
    simp only [interpCInf, chord, hl, fixLog2, K590.target0, K590.target, K590.secondCost']
    ring
  have hN : lineN0 α = (-488972311 / 1073741824 : ℝ) + (11253075 / 67108864 : ℝ) * α := by simp only [lineN0, chord, hl]; ring
  have hP : lineP0 α = (-633965405 / 1073741824 : ℝ) + (43639675 / 134217728 : ℝ) * α := by simp only [lineP0, chord, hl]; ring
  have hS : lineS0 α = (-633977113 / 1073741824 : ℝ) + (388082175 / 134217728 : ℝ) * α := by simp only [lineS0, chord, hl]; ring
  have hF := F_nonneg0 hα
  have bN : (-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-488972311 / 1073741824 : ℝ) + (11253075 / 67108864 : ℝ) * α) + cap0 α ≤ 0 := by
    exact bud_piece hα.1 hα.2 log2_le hF (cap0_0 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inr (Or.inr (by norm_num))))
  have bP : (-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-633965405 / 1073741824 : ℝ) + (43639675 / 134217728 : ℝ) * α) + cap0 α ≤ 0 := by
    exact bud_piece hα.1 hα.2 log2_le hF (cap0_0 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inl (by norm_num)))
  have bS : (-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-633977113 / 1073741824 : ℝ) + (388082175 / 134217728 : ℝ) * α) + cap0 α ≤ 0 := by
    exact bud_piece hα.1 hα.2 log2_le hF (cap0_0 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have hz : zb0 α = α * max (lineN0 α) (max (lineP0 α) (lineS0 α)) + cap0 α := rfl
  rw [hN, hP, hS, mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1), mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1)] at hz
  have hm := max_le (show α * ((-488972311 / 1073741824 : ℝ) + (11253075 / 67108864 : ℝ) * α) ≤ -((-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap0 α by linarith [bN])
    (max_le (show α * ((-633965405 / 1073741824 : ℝ) + (43639675 / 134217728 : ℝ) * α) ≤ -((-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap0 α by linarith [bP])
      (show α * ((-633977113 / 1073741824 : ℝ) + (388082175 / 134217728 : ℝ) * α) ≤ -((-3237542588147634315969 / 3612067495936000000000 : ℝ) + (-24483632409266911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap0 α by linarith [bS]))
  linarith [hE, hz, hm]

theorem bud0hi : ∀ α ∈ Icc (0 : ℝ) (1 / 200 : ℝ),
    interpCInf (0 : ℝ) (1 / 200 : ℝ) (Glue410.constantLim P410 α) (30870737 / 200000000 : ℝ) (145423449 / 1000000000 : ℝ) (14003 / 1000000000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (223 / 500 : ℝ) * chord (0 : ℝ) (1 / 200 : ℝ) (-1913689396221 / 1099511627776 : ℝ) (-1911012921633 / 1099511627776 : ℝ) α + (1 - (223 / 500 : ℝ) - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1868836503 / 1073741824 : ℝ) (-466555285 / 268435456 : ℝ) α +
      (1 - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1724586542717 / 1099511627776 : ℝ) (-858707041103 / 549755813888 : ℝ) α + zb0 α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α := by
  intro α hα
  have hl : interpL (0 : ℝ) (1 / 200 : ℝ) α = (α - (0 : ℝ)) / ((1 / 200 : ℝ) - (0 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  have hE : interpCInf (0 : ℝ) (1 / 200 : ℝ) (Glue410.constantLim P410 α) (30870737 / 200000000 : ℝ) (145423449 / 1000000000 : ℝ) (14003 / 1000000000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (223 / 500 : ℝ) * chord (0 : ℝ) (1 / 200 : ℝ) (-1913689396221 / 1099511627776 : ℝ) (-1911012921633 / 1099511627776 : ℝ) α + (1 - (223 / 500 : ℝ) - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1868836503 / 1073741824 : ℝ) (-466555285 / 268435456 : ℝ) α +
      (1 - α) * chord (0 : ℝ) (1 / 200 : ℝ) (-1724586542717 / 1099511627776 : ℝ) (-858707041103 / 549755813888 : ℝ) α -
      ((-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α) =
      (-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) := by
    rw [constLim410]
    simp only [interpCInf, chord, hl, fixLog2, K590.target0, K590.target, K590.secondCost']
    ring
  have hN : lineN0 α = (-488972311 / 1073741824 : ℝ) + (11253075 / 67108864 : ℝ) * α := by simp only [lineN0, chord, hl]; ring
  have hP : lineP0 α = (-633965405 / 1073741824 : ℝ) + (43639675 / 134217728 : ℝ) * α := by simp only [lineP0, chord, hl]; ring
  have hS : lineS0 α = (-633977113 / 1073741824 : ℝ) + (388082175 / 134217728 : ℝ) * α := by simp only [lineS0, chord, hl]; ring
  have hF := F_nonneg0 hα
  have bN : (-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-488972311 / 1073741824 : ℝ) + (11253075 / 67108864 : ℝ) * α) + cap0 α ≤ 0 := by
    exact bud_piece hα.1 hα.2 log2_le hF (cap0_0 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inr (Or.inr (by norm_num))))
  have bP : (-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-633965405 / 1073741824 : ℝ) + (43639675 / 134217728 : ℝ) * α) + cap0 α ≤ 0 := by
    exact bud_piece hα.1 hα.2 log2_le hF (cap0_0 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inl (by norm_num)))
  have bS : (-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-633977113 / 1073741824 : ℝ) + (388082175 / 134217728 : ℝ) * α) + cap0 α ≤ 0 := by
    exact bud_piece hα.1 hα.2 log2_le hF (cap0_0 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have hz : zb0 α = α * max (lineN0 α) (max (lineP0 α) (lineS0 α)) + cap0 α := rfl
  rw [hN, hP, hS, mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1), mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1)] at hz
  have hm := max_le (show α * ((-488972311 / 1073741824 : ℝ) + (11253075 / 67108864 : ℝ) * α) ≤ -((-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap0 α by linarith [bN])
    (max_le (show α * ((-633965405 / 1073741824 : ℝ) + (43639675 / 134217728 : ℝ) * α) ≤ -((-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap0 α by linarith [bP])
      (show α * ((-633977113 / 1073741824 : ℝ) + (388082175 / 134217728 : ℝ) * α) ≤ -((-6475085960158214835063 / 7224134991872000000000 : ℝ) + (-24487412723391911 / 85899345920000000 : ℝ) * α + (-529007809238323 / 429496729600000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap0 α by linarith [bS]))
  linarith [hE, hz, hm]

/-! ### Interval 1: `[1/200, 1/16]` -/

def capE1 : CapEnd where
  gs := 401 / 2500
  xc := 999 / 1000
  C1 := 9631 / 20000
  lamNA := (-488072065 / 1073741824 : ℝ)
  lamNB := (-7831627 / 16777216 : ℝ)
  lamPA := fun α => chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-316109909 / 536870912 : ℝ) (-491521 / 1048576 : ℝ) α
  lamPB := fun α => chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-611702649 / 1073741824 : ℝ) (-118855721 / 268435456 : ℝ) α
  gPA := fun _ => (-525686503 / 536870912 : ℝ)
  gPB := fun _ => (-127903819 / 134217728 : ℝ)
  rP := fun α => 11 / 8 * α
  lamSA := fun α β => bilin (1 / 200 : ℝ) (1 / 16 : ℝ) (-629779419 / 1073741824 : ℝ) (-309226913 / 536870912 : ℝ) (-296914197 / 536870912 : ℝ) (-451628379 / 1073741824 : ℝ) α β
  lamSB := fun α β => bilin (1 / 200 : ℝ) (1 / 16 : ℝ) (-617254625 / 1073741824 : ℝ) (-302949221 / 536870912 : ℝ) (-581176527 / 1073741824 : ℝ) (-219277211 / 536870912 : ℝ) α β
  gSA := fun α β => bilin (1 / 200 : ℝ) (1 / 16 : ℝ) (-260427467 / 268435456 : ℝ) (-515738139 / 536870912 : ℝ) (-998929931 / 1073741824 : ℝ) (-871010051 / 1073741824 : ℝ) α β
  gSB := fun α β => bilin (1 / 200 : ℝ) (1 / 16 : ℝ) (-250763479 / 268435456 : ℝ) (-992820325 / 1073741824 : ℝ) (-480136989 / 536870912 : ℝ) (-832354099 / 1073741824 : ℝ) α β
  rSA := fun α _ => α / 2 + 1 / 1000000
  rSB := fun α _ => α / 2 + 1 / 1000000

def lineN1 (α : ℝ) : ℝ := chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-488072065 / 1073741824 : ℝ) (-7831627 / 16777216 : ℝ) α
def lineP1 (α : ℝ) : ℝ := chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-316109909 / 536870912 : ℝ) (-118855721 / 268435456 : ℝ) α
def lineS1 (α : ℝ) : ℝ := chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-309226913 / 536870912 : ℝ) (-219277211 / 536870912 : ℝ) α
def cap1 (α : ℝ) : ℝ := 9631 / 20000 * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
def zb1 (α : ℝ) : ℝ := α * max (lineN1 α) (max (lineP1 α) (lineS1 α)) + cap1 α

theorem gapP1 (α : ℝ) : (capE1.gPA α - capE1.lamPA α ≤ (-7 / 20 : ℝ)) ∧ (capE1.gPB α - capE1.lamPB α ≤ (-7 / 20 : ℝ)) := by
  constructor
  · show (-525686503 / 536870912 : ℝ) - chord _ _ _ _ α ≤ _
    rw [← chord_const (1 / 200 : ℝ) (1 / 16 : ℝ) (-525686503 / 536870912 : ℝ) α, chord_sub]; exact chord_le (by norm_num) (by norm_num)
  · show (-127903819 / 134217728 : ℝ) - chord _ _ _ _ α ≤ _
    rw [← chord_const (1 / 200 : ℝ) (1 / 16 : ℝ) (-127903819 / 134217728 : ℝ) α, chord_sub]; exact chord_le (by norm_num) (by norm_num)

theorem gapS1 {α β : ℝ} (hα : α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ)) (hβ : β ∈ Icc 0 α) :
    (capE1.gSA α β - capE1.lamSA α β ≤ (-7 / 20 : ℝ)) ∧ (capE1.gSB α β - capE1.lamSB α β ≤ (-7 / 20 : ℝ)) := by
  constructor
  · show bilin _ _ _ _ _ _ α β - bilin _ _ _ _ _ _ α β ≤ _
    rw [bilin_sub]
    exact bilin_le (by norm_num) hα hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show bilin _ _ _ _ _ _ α β - bilin _ _ _ _ _ _ α β ≤ _
    rw [bilin_sub]
    exact bilin_le (by norm_num) hα hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lamP_le1 (α : ℝ) : (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).lamP α ≤ lineP1 α := by
  show chord _ _ (chord _ _ _ _ α) (chord _ _ _ _ α) α ≤ chord _ _ _ _ α
  unfold chord
  exact quad_chord_le (interpL_nonneg _ _ _) (interpL_le_one _ _ _) (by norm_num)

theorem lamS_le1 {α β : ℝ} (hα : α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ)) (hβ : β ∈ Icc 0 α) :
    (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).lamS α β ≤ lineS1 α := by
  have hl : interpL (1 / 200 : ℝ) (1 / 16 : ℝ) α = (α - (1 / 200 : ℝ)) / ((1 / 16 : ℝ) - (1 / 200 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  obtain ⟨hs0, hs1⟩ := s_mem (show (1 / 200 : ℝ) < (1 / 16 : ℝ) by norm_num) hα
  have hA := bilin_le_top (T00 := (-629779419 / 1073741824 : ℝ)) (T01 := (-309226913 / 536870912 : ℝ)) (T10 := (-296914197 / 536870912 : ℝ)) (T11 := (-451628379 / 1073741824 : ℝ))
    (show (1 / 200 : ℝ) < (1 / 16 : ℝ) by norm_num) hα hβ (by norm_num) (by norm_num)
  have hB := bilin_le_top (T00 := (-617254625 / 1073741824 : ℝ)) (T01 := (-302949221 / 536870912 : ℝ)) (T10 := (-581176527 / 1073741824 : ℝ)) (T11 := (-219277211 / 536870912 : ℝ))
    (show (1 / 200 : ℝ) < (1 / 16 : ℝ) by norm_num) hα hβ (by norm_num) (by norm_num)
  show chord _ _ (bilin _ _ _ _ _ _ α β) (bilin _ _ _ _ _ _ α β) α ≤ chord _ _ _ _ α
  unfold chord
  rw [hl]
  have h1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 1 - (α - (1 / 200 : ℝ)) / ((1 / 16 : ℝ) - (1 / 200 : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left hB hs0
  have h3 := quad_chord_le (A0 := (-309226913 / 536870912 : ℝ)) (A1 := (-451628379 / 1073741824 : ℝ)) (B0 := (-302949221 / 536870912 : ℝ)) (B1 := (-219277211 / 536870912 : ℝ)) hs0 hs1 (by norm_num)
  linarith

theorem hZB1 (c d e : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (h1 : (1 / 200 : ℝ) ≤ c + d + e)
    (h2 : c + d + e ≤ (1 / 16 : ℝ)) : zbCap (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)) c d e ≤ zb1 (c + d + e) := by
  have hα : c + d + e ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ) := ⟨h1, h2⟩
  have hβ : e ∈ Icc 0 (c + d + e) := ⟨he, by linarith⟩
  have hM1 := le_max_left (lineN1 (c + d + e)) (max (lineP1 (c + d + e)) (lineS1 (c + d + e)))
  have hM2 := (le_max_left (lineP1 (c + d + e)) (lineS1 (c + d + e))).trans (le_max_right (lineN1 (c + d + e)) _)
  have hM3 := (le_max_right (lineP1 (c + d + e)) (lineS1 (c + d + e))).trans (le_max_right (lineN1 (c + d + e)) _)
  have hgP : (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).gP (c + d + e) - (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).lamP (c + d + e) ≤ (-7 / 20 : ℝ) := by
    show chord _ _ _ _ _ - chord _ _ _ _ _ ≤ _
    rw [chord_sub]; exact chord_le (gapP1 _).1 (gapP1 _).2
  have hgS : (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).gS (c + d + e) e - (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).lamS (c + d + e) e ≤ (-7 / 20 : ℝ) := by
    show chord _ _ _ _ _ - chord _ _ _ _ _ ≤ _
    rw [chord_sub]; exact chord_le (gapS1 hα hβ).1 (gapS1 hα hβ).2
  have hrS : (capE1.toS (1 / 200 : ℝ) (1 / 16 : ℝ)).rS (c + d + e) e = (c + d + e) / 2 + 1 / 1000000 := by
    show chord _ _ ((c + d + e) / 2 + 1 / 1000000) ((c + d + e) / 2 + 1 / 1000000) _ = _
    rw [chord_const]
  exact zb_bound capE1 (1 / 200 : ℝ) (1 / 16 : ℝ) (-7 / 20 : ℝ) _ _ (by norm_num) (by show (999 / 1000 : ℝ) < 1; norm_num)
    (by show (0 : ℝ) ≤ 9631 / 20000; norm_num) hc hd he hM1 ((lamP_le1 _).trans hM2)
    ((lamS_le1 hα hβ).trans hM3) hgP hgS (by show (0 : ℝ) ≤ 11 / 8 * (c + d + e); linarith) hrS
    (by linarith)

theorem F_nonneg1 {α : ℝ} (hα : α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ)) : 0 ≤ (75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2 := by
  have := quad_nonpos_Icc (a := (-75 / 58 : ℝ)) (b := (-621 / 580 : ℝ)) (c := (69 / 80 : ℝ)) (by norm_num) (by norm_num)
    (Or.inl (by norm_num)) hα.1 hα.2
  linarith

theorem cap1_0 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (39 / 3200 : ℝ)) : cap1 α ≤ (1543917 / 144115188075855872 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (429 / 25600 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (24379 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (429 / 25600 : ℝ)) 20 (380 / 429 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (24379 / 4000000 : ℝ)) 57 (10397 / 24379 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((429 / 25600 : ℝ) * ((3 / 8) ^ 20 * (1 / (1 + (380 / 429 : ℝ) + (380 / 429 : ℝ) ^ 2 / 2))) +
          (24379 / 4000000 : ℝ) * ((3 / 8) ^ 57 * (1 / (1 + (10397 / 24379 : ℝ) + (10397 / 24379 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (1543917 / 144115188075855872 : ℝ) := by norm_num

theorem cap1_1 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (31 / 1600 : ℝ)) : cap1 α ≤ (37385591169 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (341 / 12800 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (19377 / 2000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (341 / 12800 : ℝ)) 13 (47 / 341 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (19377 / 2000000 : ℝ)) 36 (2428 / 19377 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((341 / 12800 : ℝ) * ((3 / 8) ^ 13 * (1 / (1 + (47 / 341 : ℝ) + (47 / 341 : ℝ) ^ 2 / 2))) +
          (19377 / 2000000 : ℝ) * ((3 / 8) ^ 36 * (1 / (1 + (2428 / 19377 : ℝ) + (2428 / 19377 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (37385591169 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_2 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (17 / 640 : ℝ)) : cap1 α ≤ (848281655091 / 576460752303423488 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (187 / 5120 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (53129 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (187 / 5120 : ℝ)) 9 (109 / 187 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (53129 / 4000000 : ℝ)) 26 (18646 / 53129 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((187 / 5120 : ℝ) * ((3 / 8) ^ 9 * (1 / (1 + (109 / 187 : ℝ) + (109 / 187 : ℝ) ^ 2 / 2))) +
          (53129 / 4000000 : ℝ) * ((3 / 8) ^ 26 * (1 / (1 + (18646 / 53129 : ℝ) + (18646 / 53129 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (848281655091 / 576460752303423488 : ℝ) := by norm_num

theorem cap1_3 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (27 / 800 : ℝ)) : cap1 α ≤ (15907533320883 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (297 / 6400 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (4219 / 250000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (297 / 6400 : ℝ)) 7 (161 / 297 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (4219 / 250000 : ℝ)) 20 (3120 / 4219 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((297 / 6400 : ℝ) * ((3 / 8) ^ 7 * (1 / (1 + (161 / 297 : ℝ) + (161 / 297 : ℝ) ^ 2 / 2))) +
          (4219 / 250000 : ℝ) * ((3 / 8) ^ 20 * (1 / (1 + (3120 / 4219 : ℝ) + (3120 / 4219 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (15907533320883 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_4 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (131 / 3200 : ℝ)) : cap1 α ≤ (69993682689323 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (1441 / 25600 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (81879 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (1441 / 25600 : ℝ)) 6 (314 / 1441 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (81879 / 4000000 : ℝ)) 17 (1151 / 11697 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((1441 / 25600 : ℝ) * ((3 / 8) ^ 6 * (1 / (1 + (314 / 1441 : ℝ) + (314 / 1441 : ℝ) ^ 2 / 2))) +
          (81879 / 4000000 : ℝ) * ((3 / 8) ^ 17 * (1 / (1 + (1151 / 11697 : ℝ) + (1151 / 11697 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (69993682689323 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_5 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (77 / 1600 : ℝ)) : cap1 α ≤ (6396338832333 / 36028797018963968 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (847 / 12800 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (48127 / 2000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (847 / 12800 : ℝ)) 5 (35 / 121 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (48127 / 2000000 : ℝ)) 14 (26222 / 48127 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((847 / 12800 : ℝ) * ((3 / 8) ^ 5 * (1 / (1 + (35 / 121 : ℝ) + (35 / 121 : ℝ) ^ 2 / 2))) +
          (48127 / 2000000 : ℝ) * ((3 / 8) ^ 14 * (1 / (1 + (26222 / 48127 : ℝ) + (26222 / 48127 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (6396338832333 / 36028797018963968 : ℝ) := by norm_num

theorem cap1_6 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (177 / 3200 : ℝ)) : cap1 α ≤ (468348773017705 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (1947 / 25600 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (110629 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (1947 / 25600 : ℝ)) 4 (1172 / 1947 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (110629 / 4000000 : ℝ)) 12 (72452 / 110629 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((1947 / 25600 : ℝ) * ((3 / 8) ^ 4 * (1 / (1 + (1172 / 1947 : ℝ) + (1172 / 1947 : ℝ) ^ 2 / 2))) +
          (110629 / 4000000 : ℝ) * ((3 / 8) ^ 12 * (1 / (1 + (72452 / 110629 : ℝ) + (72452 / 110629 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (468348773017705 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_7 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (1 / 16 : ℝ)) : cap1 α ≤ (438839218052741 / 576460752303423488 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (11 / 128 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (31251 / 1000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (11 / 128 : ℝ)) 4 (4 / 55 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (31251 / 1000000 : ℝ)) 11 (6239 / 31251 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((11 / 128 : ℝ) * ((3 / 8) ^ 4 * (1 / (1 + (4 / 55 : ℝ) + (4 / 55 : ℝ) ^ 2 / 2))) +
          (31251 / 1000000 : ℝ) * ((3 / 8) ^ 11 * (1 / (1 + (6239 / 31251 : ℝ) + (6239 / 31251 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (438839218052741 / 576460752303423488 : ℝ) := by norm_num

theorem bud1lo : ∀ α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ),
    interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (27 / 100 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (27 / 100 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α + zb1 α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α := by
  intro α hα
  have hl : interpL (1 / 200 : ℝ) (1 / 16 : ℝ) α = (α - (1 / 200 : ℝ)) / ((1 / 16 : ℝ) - (1 / 200 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  have hE : interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (27 / 100 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (27 / 100 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α -
      ((-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α) =
      (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) := by
    rw [constLim410]
    simp only [interpCInf, chord, hl, fixLog2, K590.target0, K590.target, K590.secondCost']
    ring
  have hN : lineN1 α = (-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α := by simp only [lineN1, chord, hl]; ring
  have hP : lineP1 α = (-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α := by simp only [lineP1, chord, hl]; ring
  have hS : lineS1 α = (-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α := by simp only [lineS1, chord, hl]; ring
  have hF := F_nonneg1 hα
  have bN : (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inr (Or.inr (Or.inr (by norm_num))))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inl (by norm_num)))
  have bP : (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have bS : (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have hz : zb1 α = α * max (lineN1 α) (max (lineP1 α) (lineS1 α)) + cap1 α := rfl
  rw [hN, hP, hS, mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1), mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1)] at hz
  have hm := max_le (show α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) ≤ -((-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bN])
    (max_le (show α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) ≤ -((-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bP])
      (show α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) ≤ -((-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bS]))
  linarith [hE, hz, hm]

theorem bud1hi : ∀ α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ),
    interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (4431 / 10000 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (4431 / 10000 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α + zb1 α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α := by
  intro α hα
  have hl : interpL (1 / 200 : ℝ) (1 / 16 : ℝ) α = (α - (1 / 200 : ℝ)) / ((1 / 16 : ℝ) - (1 / 200 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  have hE : interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (4431 / 10000 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (4431 / 10000 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α -
      ((-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α) =
      (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) := by
    rw [constLim410]
    simp only [interpCInf, chord, hl, fixLog2, K590.target0, K590.target, K590.secondCost']
    ring
  have hN : lineN1 α = (-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α := by simp only [lineN1, chord, hl]; ring
  have hP : lineP1 α = (-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α := by simp only [lineP1, chord, hl]; ring
  have hS : lineS1 α = (-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α := by simp only [lineS1, chord, hl]; ring
  have hF := F_nonneg1 hα
  have bN : (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inr (Or.inr (Or.inr (by norm_num))))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inl (by norm_num)))
  have bP : (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have bS : (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have hz : zb1 α = α * max (lineN1 α) (max (lineP1 α) (lineS1 α)) + cap1 α := rfl
  rw [hN, hP, hS, mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1), mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1)] at hz
  have hm := max_le (show α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) ≤ -((-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bN])
    (max_le (show α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) ≤ -((-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bP])
      (show α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) ≤ -((-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bS]))
  linarith [hE, hz, hm]

/-! ### The endpoint suprema and constants of the table, and the budget rows -/

def SnA410 : Fin 2 → ℝ := ![(-1913689396221 / 1099511627776 : ℝ), (-1911012921633 / 1099511627776 : ℝ)]
def SnB410 : Fin 2 → ℝ := ![(-1911012921633 / 1099511627776 : ℝ), (-939442945915 / 549755813888 : ℝ)]
def SpA410 : Fin 2 → ℝ := ![(-1868836503 / 1073741824 : ℝ), (-466555285 / 268435456 : ℝ)]
def SpB410 : Fin 2 → ℝ := ![(-466555285 / 268435456 : ℝ), (-917526653 / 536870912 : ℝ)]
def SyA410 : Fin 2 → ℝ := ![(-1724586542717 / 1099511627776 : ℝ), (-858707041103 / 549755813888 : ℝ)]
def SyB410 : Fin 2 → ℝ := ![(-858707041103 / 549755813888 : ℝ), (-816870426147 / 549755813888 : ℝ)]
def rAq : Fin 2 → ℝ := ![(30870737 / 200000000 : ℝ), (145423449 / 1000000000 : ℝ)]
def rBq : Fin 2 → ℝ := ![(145423449 / 1000000000 : ℝ), (9020207 / 200000000 : ℝ)]
def κcq : Fin 2 → ℝ := ![(14003 / 1000000000 : ℝ), (181637 / 62500000 : ℝ)]

theorem hbudLo410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (Glue410.constantLim P410 α) (rAq i) (rBq i) (κcq i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κlo410 i * chord (αA410 i) (αB410 i) (SnA410 i) (SnB410 i) α +
      (1 - κlo410 i - α) * chord (αA410 i) (αB410 i) (SpA410 i) (SpB410 i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA410 i) (SyB410 i) α + ![zb0, zb1] i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α :=
  Fin.forall_fin_two.2 ⟨bud0lo, bud1lo⟩

theorem hbudHi410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (Glue410.constantLim P410 α) (rAq i) (rBq i) (κcq i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κhi410 i * chord (αA410 i) (αB410 i) (SnA410 i) (SnB410 i) α +
      (1 - κhi410 i - α) * chord (αA410 i) (αB410 i) (SpA410 i) (SpB410 i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA410 i) (SyB410 i) α + ![zb0, zb1] i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α :=
  Fin.forall_fin_two.2 ⟨bud0hi, bud1hi⟩

/-! ### The `Rows410` fields -/

def capE410 : Fin 2 → CapEnd := ![capE0, capE1]
def zb410 : Fin 2 → ℝ → ℝ := ![zb0, zb1]
def Bd410 : Fin 2 → ℝ := ![(-19 / 50 : ℝ), (-7 / 20 : ℝ)]
def Rbd410 : Fin 2 → ℝ := ![(11 / 1600 : ℝ), (11 / 128 : ℝ)]

theorem hxc0_410 : ∀ i, 0 ≤ (capE410 i).xc :=
  Fin.forall_fin_two.2 ⟨by show (0 : ℝ) ≤ 999 / 1000; norm_num, by show (0 : ℝ) ≤ 999 / 1000; norm_num⟩

theorem hxc1_410 : ∀ i, (capE410 i).xc < 1 :=
  Fin.forall_fin_two.2 ⟨by show (999 / 1000 : ℝ) < 1; norm_num, by show (999 / 1000 : ℝ) < 1; norm_num⟩

theorem hC1_410 : ∀ i, 0 < (capE410 i).C1 :=
  Fin.forall_fin_two.2 ⟨by show (0 : ℝ) < 9631 / 20000; norm_num, by show (0 : ℝ) < 9631 / 20000; norm_num⟩

theorem hgs410 : ∀ i, (capE410 i).gs ≤ 401 / 2500 :=
  Fin.forall_fin_two.2 ⟨le_refl _, le_refl _⟩

theorem hxc410 : ∀ i, 999 / 1000 ≤ (capE410 i).xc :=
  Fin.forall_fin_two.2 ⟨le_refl _, le_refl _⟩

theorem hC1le410 : ∀ i, 9631 / 20000 ≤ (capE410 i).C1 :=
  Fin.forall_fin_two.2 ⟨le_refl _, le_refl _⟩

theorem hrP410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), remC (1 / 10) * α ≤ (capE410 i).rP α :=
  Fin.forall_fin_two.2 ⟨fun α _ => by show remC (1 / 10) * α ≤ 11 / 8 * α; norm_num [remC],
    fun α _ => by show remC (1 / 10) * α ≤ 11 / 8 * α; norm_num [remC]⟩

theorem hrSA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE410 i).rSA α β :=
  Fin.forall_fin_two.2 ⟨fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2],
    fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2]⟩

theorem hrSB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE410 i).rSB α β :=
  Fin.forall_fin_two.2 ⟨fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2],
    fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2]⟩

theorem hBdPA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE410 i).gPA α - (capE410 i).lamPA α ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun α _ => (gapP0 α).1, fun α _ => (gapP1 α).1⟩

theorem hBdPB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE410 i).gPB α - (capE410 i).lamPB α ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun α _ => (gapP0 α).2, fun α _ => (gapP1 α).2⟩

theorem hBdSA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE410 i).gSA α β - (capE410 i).lamSA α β ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun _ hα _ hβ => (gapS0 hα hβ).1, fun _ hα _ hβ => (gapS1 hα hβ).1⟩

theorem hBdSB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE410 i).gSB α β - (capE410 i).lamSB α β ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun _ hα _ hβ => (gapS0 hα hβ).2, fun _ hα _ hβ => (gapS1 hα hβ).2⟩

theorem hRP410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE410 i).rP α ≤ Rbd410 i :=
  Fin.forall_fin_two.2
    ⟨fun α hα => by
      have h2 : α ≤ 1 / 200 := hα.2
      show 11 / 8 * α ≤ (11 / 1600 : ℝ); linarith,
     fun α hα => by
      have h2 : α ≤ 1 / 16 := hα.2
      show 11 / 8 * α ≤ (11 / 128 : ℝ); linarith⟩

theorem hRSA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE410 i).rSA α β ≤ Rbd410 i :=
  Fin.forall_fin_two.2
    ⟨fun α hα _ _ => by
      have h2 : α ≤ 1 / 200 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 1600 : ℝ); linarith,
     fun α hα _ _ => by
      have h2 : α ≤ 1 / 16 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 128 : ℝ); linarith⟩

theorem hRSB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE410 i).rSB α β ≤ Rbd410 i :=
  Fin.forall_fin_two.2
    ⟨fun α hα _ _ => by
      have h2 : α ≤ 1 / 200 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 1600 : ℝ); linarith,
     fun α hα _ _ => by
      have h2 : α ≤ 1 / 16 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 128 : ℝ); linarith⟩

theorem hZB410 : ∀ (i : Fin 2) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo410 i ≤ c + d + e →
    c + d + e ≤ hi410 i →
    zbCap ((capE410 i).toS (αA410 i) (αB410 i)) c d e ≤ zb410 i (c + d + e) :=
  Fin.forall_fin_two.2 ⟨hZB0, hZB1⟩

end Bud410

end

end CatalanMeasure.GenD.Signed.Data.Assembly
