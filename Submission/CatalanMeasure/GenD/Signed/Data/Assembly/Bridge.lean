module

public import Submission.CatalanMeasure.GenD.Signed.TaylorCell

@[expose] public section

/-!
# 410 assembly: rounded cell fields against the trial fields

The cell modules bound `fieldTower` of a `FieldQ` whose polynomial is the trial polynomial rounded
(to `2^-96`), with the same plogs and poles.  On `|x| ≤ 1` the two polynomials differ by at most the
`ℓ¹` distance of their coefficient lists, so a cell bound transfers to the trial field at that cost.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert

noncomputable section

/-- `|a|` on `ℚ`, by cases (kernel-reducible). -/
def qAbs (a : ℚ) : ℚ := if a < 0 then -a else a

theorem qAbs_cast (a : ℚ) : ((qAbs a : ℚ) : ℝ) = |(a : ℝ)| := by
  unfold qAbs
  split_ifs with h
  · rw [abs_of_neg (by exact_mod_cast h)]; push_cast; ring
  · push_neg at h; rw [abs_of_nonneg (by exact_mod_cast h)]

/-- The `ℓ¹` distance of two coefficient lists (zero-padded). -/
def l1Q : List ℚ → List ℚ → ℚ
  | [], [] => 0
  | a :: as, [] => qAbs a + l1Q as []
  | [], b :: bs => qAbs b + l1Q [] bs
  | a :: as, b :: bs => qAbs (a - b) + l1Q as bs

theorem polyTow_nil (x : ℝ) : polyTow [] 0 x = 0 := rfl

theorem polyTow_cons (a : ℚ) (as : List ℚ) (x : ℝ) :
    polyTow (a :: as) 0 x = (a : ℝ) + x * polyTow as 0 x := rfl

theorem polyTow_sub_le : ∀ (p q : List ℚ) {x : ℝ}, |x| ≤ 1 →
    |polyTow p 0 x - polyTow q 0 x| ≤ ((l1Q p q : ℚ) : ℝ)
  | [], [], x, _ => by simp [polyTow_nil, l1Q]
  | a :: as, [], x, hx => by
    have ih := polyTow_sub_le as [] hx
    simp only [polyTow_nil, sub_zero] at ih
    simp only [polyTow_cons, polyTow_nil, l1Q, sub_zero]
    push_cast; rw [qAbs_cast]
    calc |(a : ℝ) + x * polyTow as 0 x| ≤ |(a : ℝ)| + |x| * |polyTow as 0 x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a : ℝ)| + 1 * ((l1Q as [] : ℚ) : ℝ) := by gcongr
      _ = _ := by ring
  | [], b :: bs, x, hx => by
    have ih := polyTow_sub_le [] bs hx
    simp only [polyTow_nil, zero_sub, abs_neg] at ih
    simp only [polyTow_cons, polyTow_nil, l1Q, zero_sub, abs_neg]
    push_cast; rw [qAbs_cast]
    calc |(b : ℝ) + x * polyTow bs 0 x| ≤ |(b : ℝ)| + |x| * |polyTow bs 0 x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(b : ℝ)| + 1 * ((l1Q [] bs : ℚ) : ℝ) := by gcongr
      _ = _ := by ring
  | a :: as, b :: bs, x, hx => by
    have ih := polyTow_sub_le as bs hx
    rw [polyTow_cons, polyTow_cons, l1Q]
    push_cast; rw [qAbs_cast]; push_cast
    calc |(a : ℝ) + x * polyTow as 0 x - ((b : ℝ) + x * polyTow bs 0 x)|
        = |((a : ℝ) - b) + x * (polyTow as 0 x - polyTow bs 0 x)| := by ring_nf
      _ ≤ |(a : ℝ) - b| + |x| * |polyTow as 0 x - polyTow bs 0 x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a : ℝ) - b| + 1 * ((l1Q as bs : ℚ) : ℝ) := by
          gcongr
      _ = _ := by ring

/-- **Bridge**: a field with the same plogs and poles as a cell field and an `ℓ¹`-close polynomial is
bounded by the cell field plus the `ℓ¹` distance, on `|x| ≤ 1`. -/
theorem fieldTower_le_cell (f g : FieldQ) (hpl : f.plogs = g.plogs) (hpo : f.poles = g.poles)
    {δ : ℚ} (hδ : l1Q f.poly g.poly ≤ δ) {x : ℝ} (hx : |x| ≤ 1) (F : List PoleR → ℝ → ℝ) :
    fieldTower f (F f.poles) 0 x ≤ fieldTower g (F g.poles) 0 x + (δ : ℝ) := by
  unfold fieldTower
  rw [hpl, hpo]
  have h := polyTow_sub_le f.poly g.poly hx
  have hδ' : ((l1Q f.poly g.poly : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  have := (abs_le.mp h).2
  linarith

end

end CatalanMeasure.GenD.Signed.Data.Assembly
