module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Budget
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsConst
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Cls
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsQ0
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsQ1
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsQ2

@[expose] public section

/-!
# 410 assembly: the instance of `Rows410`

`rows410 C0 C1 C2 : Rows410` from the cell statements of the three trials (`CellsQ0`, `CellsQ1`,
`CellsQ2`). Segment `i` has endpoint trials `X i` (side A) and `X (i+1)` (side B). The row
theorems of `RowsQ{t}` conclude at the threshold literals; the budget constants of `Budget` are
equal or larger, and the adapters below pass from one to the other.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.D58
open Bud410
open CatalanMeasure.Signed.Consts (mmaxOf s410)

noncomputable section

namespace RowsInst

theorem ev_mono {ε a b : ℝ} {I : Set ℝ} {f : ℕ → ℝ → ℝ} (hab : a ≤ b)
    (h : ∀ᶠ N : ℕ in atTop, ∀ x ∈ I, f N x ≤ a + ε) : ∀ᶠ N : ℕ in atTop, ∀ x ∈ I, f N x ≤ b + ε :=
  h.mono fun _ hN x hx => (hN x hx).trans (by linarith)

theorem ev_neg {ε L L' g : ℝ} {J : Set ℝ} {f : ℕ → ℝ → ℝ} (hg : g = 401 / 2500) (hL : L ≤ L')
    (h : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(401 / 2500 : ℝ) → f N x ≤ L + ε) :
    ∀ᶠ N : ℕ in atTop, ∀ _α ∈ J, ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -g → f N x ≤ L' + ε :=
  h.mono fun _ hN _ _ x hx hxg => (hN x hx (hg ▸ hxg)).trans (by linarith)

theorem ev_pos {ε g xc a b a' b' : ℝ} {L L' : ℝ → ℝ} {f : ℕ → ℝ → ℝ → ℝ}
    (hg : g = 401 / 2500) (hxc : xc = 999 / 1000) (ha : a' = a) (hb : b' = b)
    (hL : ∀ α, L α ≤ L' α)
    (h : ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc a b, ∀ x ∈ Ioo (0 : ℝ) 1, (401 / 2500 : ℝ) ≤ x → x < 999 / 1000 →
      f N α x ≤ L α + ε) :
    ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc a' b', ∀ x ∈ Ioo (0 : ℝ) 1, g ≤ x → x < xc → f N α x ≤ L' α + ε := by
  subst hg hxc ha hb
  exact h.mono fun _ hN α hα x hx h1 h2 => (hN α hα x hx h1 h2).trans (by linarith [hL α])

theorem ev_top {ε xc c : ℝ} {J : Set ℝ} {G : ℝ → ℝ} {f : ℕ → ℝ → ℝ} (hxc : xc = 999 / 1000)
    (hG : ∀ α, c ≤ G α)
    (h : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (999 / 1000 : ℝ) ≤ x → f N x ≤ c + ε) :
    ∀ᶠ N : ℕ in atTop, ∀ α ∈ J, ∀ x ∈ Ioo (0 : ℝ) 1, xc ≤ x → f N x ≤ G α + ε := by
  subst hxc
  exact h.mono fun _ hN α _ x hx h1 => (hN x hx h1).trans (by linarith [hG α])

theorem ev_near {ε g xc a b a' b' : ℝ} {B L : ℝ → ℝ → ℝ} {f : ℕ → ℝ → ℝ → ℝ → ℝ}
    (hg : g = 401 / 2500) (hxc : xc = 999 / 1000) (ha : a' = a) (hb : b' = b)
    (hL : ∀ α β, B α β ≤ L α β)
    (h : ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc a b, ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (401 / 2500 : ℝ) ≤ x →
      x < 999 / 1000 → f N α β x ≤ B α β + ε) :
    ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc a' b', ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, g ≤ x → x < xc →
      f N α β x ≤ L α β + ε := by
  subst hg hxc ha hb
  exact h.mono fun _ hN α hα β hβ x hx h1 h2 => (hN α hα β hβ x hx h1 h2).trans (by linarith [hL α β])

theorem ev_nearTop {ε xc a b a' b' : ℝ} {B G R r : ℝ → ℝ → ℝ} {f : ℕ → ℝ → ℝ → ℝ → ℝ}
    (hxc : xc = 999 / 1000) (ha : a' = a) (hb : b' = b)
    (hG : ∀ α β, B α β ≤ G α β) (hR : ∀ α β, R α β = r α β)
    (h : ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc a b, ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (999 / 1000 : ℝ) ≤ x →
      f N α β x ≤ B α β + ε + R α β * (-Real.log (1 - x ^ 2))) :
    ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc a' b', ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, xc ≤ x →
      f N α β x ≤ G α β + ε + r α β * (-Real.log (1 - x ^ 2)) := by
  subst hxc ha hb
  exact h.mono fun _ hN α hα β hβ x hx h1 => by
    have := hN α hα β hβ x hx h1
    rw [hR] at this
    linarith [hG α β]

theorem rA_eq : rA410 = rAq := by
  funext i; fin_cases i <;> norm_num [rA410, rAq, rr0, rr1]

theorem rB_eq : rB410 = rBq := by
  funext i; fin_cases i <;> norm_num [rB410, rBq, rr1, rr2]

theorem κc_eq : κc410 = κcq := by
  funext i; fin_cases i <;> norm_num [κc410, κcq, kc01, kc12]

end RowsInst

open RowsInst in
/-- **The rows of the 410 proof**, from the cell statements of the three trials. -/
def rows410 (C0 : RowsQ0.CellsQ0) (C1 : RowsQ1.CellsQ1) (C2 : RowsQ2.CellsQ2) : Rows410 where
  SnA := SnA410
  SnB := SnB410
  SpA := SpA410
  SpB := SpB410
  SyA := SyA410
  SyB := SyB410
  hSnA := by
    intro i ε hε; fin_cases i
    · exact ev_mono (by norm_num [SnA410]) (RowsQ0.rowSN C0 ε hε)
    · exact ev_mono (by norm_num [SnA410]) (RowsQ1.rowSN C1 ε hε)
  hSnB := by
    intro i ε hε; fin_cases i
    · exact ev_mono (by norm_num [SnB410]) (RowsQ1.rowSN C1 ε hε)
    · exact ev_mono (by norm_num [SnB410]) (RowsQ2.rowSN C2 ε hε)
  hSpA := by
    intro i ε hε; fin_cases i
    · exact ev_mono (by norm_num [SpA410]) (RowsQ0.rowSP C0 ε hε)
    · exact ev_mono (by norm_num [SpA410]) (RowsQ1.rowSP C1 ε hε)
  hSpB := by
    intro i ε hε; fin_cases i
    · exact ev_mono (by norm_num [SpB410]) (RowsQ1.rowSP C1 ε hε)
    · exact ev_mono (by norm_num [SpB410]) (RowsQ2.rowSP C2 ε hε)
  hSyA := by
    intro i ε hε; fin_cases i
    · exact ev_mono (by norm_num [SyA410]) (RowsQ0.rowSC C0 ε hε)
    · exact ev_mono (by norm_num [SyA410]) (RowsQ1.rowSC C1 ε hε)
  hSyB := by
    intro i ε hε; fin_cases i
    · exact ev_mono (by norm_num [SyB410]) (RowsQ1.rowSC C1 ε hε)
    · exact ev_mono (by norm_num [SyB410]) (RowsQ2.rowSC C2 ε hε)
  cP := cP410
  hcP := hcP410
  rA := rAq
  rB := rBq
  κc := κcq
  hrA := by intro i ε hε; rw [← rA_eq]; exact hrA410 i hε
  hrB := by intro i ε hε; rw [← rB_eq]; exact hrB410 i hε
  hκ := by intro i ε hε; rw [← κc_eq]; exact hκ410 i hε
  Clsf := fun N k q m1 m2 xn gp yn yp =>
    ClsfCanon (fun i N => (DA410 i N).θ) (fun i N => (DA410 i N).sp) (fun i N => (DA410 i N).g)
      (fun i N => (DA410 i N).ν) (fun N => ((58 * N : ℕ) : ℝ)) (fun N => ((58 * N : ℕ) : ℝ) + 1)
      (mmaxOf s410) N k q m1 m2 xn gp yn yp
  cp := cp410
  cp_pos := fun _ _ _ => by norm_num [cp410]
  cp_le := fun _ _ _ => by norm_num [cp410]
  err_small := by
    intro i ε hε; fin_cases i
    · filter_upwards [err_small410 X0 hε] with N hN α _ using hN
    · filter_upwards [err_small410 X1 hε] with N hN α _ using hN
  cp_theta := by intro i N α; fin_cases i <;> exact le_rfl
  hCls := hCls410 (RowsQ0.rowFR C0) RowsQ0.fr_lt_sup (RowsQ1.rowFR C1) RowsQ1.fr_lt_sup
    (RowsQ2.rowFR C2) RowsQ2.fr_lt_sup
  capE := capE410
  hxc0 := hxc0_410
  hxc1 := hxc1_410
  hC1 := hC1_410
  hrP := hrP410
  hrSA := hrSA410
  hrSB := hrSB410
  Bd := Bd410
  Rbd := Rbd410
  hBdPA := hBdPA410
  hBdPB := hBdPB410
  hBdSA := hBdSA410
  hBdSB := hBdSB410
  hRP := hRP410
  hRSA := hRSA410
  hRSB := hRSB410
  hgs := hgs410
  hxc := hxc410
  hC1le := hC1le410
  hnegA := by
    intro i ε hε; fin_cases i
    · exact ev_neg rfl (by norm_num [capE410, capE0]) (RowsQ0.rowNeg C0 ε hε)
    · exact ev_neg rfl (by norm_num [capE410, capE1]) (RowsQ1.rowNeg C1 ε hε)
  hnegB := by
    intro i ε hε; fin_cases i
    · exact ev_neg rfl (by norm_num [capE410, capE0]) (RowsQ1.rowNeg C1 ε hε)
    · exact ev_neg rfl (by norm_num [capE410, capE1]) (RowsQ2.rowNeg C2 ε hε)
  hposA := by
    intro i ε hε; fin_cases i
    · exact ev_pos rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α => by norm_num [capE410, capE0, chord_const]) (RowsQ0.rowPos_A C0 ε hε)
    · exact ev_pos rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α => by norm_num [capE410, capE1]) (RowsQ1.rowPos_A C1 ε hε)
  hposB := by
    intro i ε hε; fin_cases i
    · exact ev_pos rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α => by norm_num [capE410, capE0, chord_const]) (RowsQ1.rowPos_B C1 ε hε)
    · exact ev_pos rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α => by norm_num [capE410, capE1]) (RowsQ2.rowPos_B C2 ε hε)
  hposTopA := by
    intro i ε hε; fin_cases i
    · exact ev_top rfl (fun α => by norm_num [capE410, capE0]) (RowsQ0.rowPosTop C0 ε hε)
    · exact ev_top rfl (fun α => by norm_num [capE410, capE1]) (RowsQ1.rowPosTop C1 ε hε)
  hposTopB := by
    intro i ε hε; fin_cases i
    · exact ev_top rfl (fun α => by norm_num [capE410, capE0]) (RowsQ1.rowPosTop C1 ε hε)
    · exact ev_top rfl (fun α => by norm_num [capE410, capE1]) (RowsQ2.rowPosTop C2 ε hε)
  hnearA := by
    intro i ε hε; fin_cases i
    · exact ev_near rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (RowsQ0.rowNear_A C0 ε hε)
    · exact ev_near rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (RowsQ1.rowNear_A C1 ε hε)
  hnearB := by
    intro i ε hε; fin_cases i
    · exact ev_near rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (RowsQ1.rowNear_B C1 ε hε)
    · exact ev_near rfl rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (RowsQ2.rowNear_B C2 ε hε)
  hnearTopA := by
    intro i ε hε; fin_cases i
    · exact ev_nearTop rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (fun α β => rfl) (RowsQ0.rowNearTop_A C0 ε hε)
    · exact ev_nearTop rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (fun α β => rfl) (RowsQ1.rowNearTop_A C1 ε hε)
  hnearTopB := by
    intro i ε hε; fin_cases i
    · exact ev_nearTop rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (fun α β => rfl) (RowsQ1.rowNearTop_B C1 ε hε)
    · exact ev_nearTop rfl (by norm_num [lo410]) (by norm_num [hi410])
        (fun α β => le_of_eq rfl) (fun α β => rfl) (RowsQ2.rowNearTop_B C2 ε hε)
  zb := zb410
  hZB := hZB410
  hbudLo := hbudLo410
  hbudHi := hbudHi410

end

end CatalanMeasure.GenD.Signed.Data.Assembly
