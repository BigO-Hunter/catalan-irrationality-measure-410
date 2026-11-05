module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# D2 constants: the slope grid of `LinkCert` (Lemma T)

`ts = 13/128`, `hmesh = 39/2048` (so `hmesh / ts = 3/16`), `J = 24` and `tg j = ts + hmesh (2 j + 1)`.
The grid covers `[ts, 1]` within `hmesh`, and every `tg j` lies in `[ts, 1]`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set

/-- The `j`-th slope-grid point, `t = (247 + 78 j) / 2048`. -/
noncomputable def tgR (j : ℕ) : ℝ := 13 / 128 + 39 / 2048 * (2 * (j : ℝ) + 1)

theorem tgR_eq (j : ℕ) : tgR j = ((247 + 78 * j : ℕ) : ℝ) / 2 ^ 11 := by
  unfold tgR; push_cast; norm_num; ring

theorem tgR_mem {j : ℕ} (hj : j < 24) : tgR j ∈ Icc (13 / 128 : ℝ) 1 := by
  have : (j : ℝ) ≤ 23 := by exact_mod_cast Nat.lt_succ_iff.mp hj
  unfold tgR
  constructor <;> nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem tgR_cover {t : ℝ} (ht : t ∈ Icc (13 / 128 : ℝ) 1) :
    ∃ j : ℕ, j < 24 ∧ |t - tgR j| ≤ 39 / 2048 := by
  set x : ℝ := (t - 13 / 128) / (39 / 1024) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith [ht.1]) (by norm_num)
  have hx1 : x < 24 := by
    rw [hx, div_lt_iff₀ (by norm_num)]; nlinarith [ht.2]
  refine ⟨⌊x⌋₊, ?_, ?_⟩
  · have : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have h24 : ⌊x⌋₊ < 24 := by
      rw [Nat.floor_lt hx0]; exact_mod_cast hx1
    exact h24
  · have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hxt : 39 / 1024 * x = t - 13 / 128 := by
      rw [hx]; field_simp
    simp only [tgR]
    rw [abs_le]
    constructor <;> linarith

end CatalanMeasure.Signed.Consts
