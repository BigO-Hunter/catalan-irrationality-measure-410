module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeC

/-!
# D2 constants: the spike jump `De2` as an integer polynomial inequality

`S_b(-y) - S_b(-rho) <= De2` on a dyadic interval of `y` for `b = bSeq (Bn / 2^60)` from an integer
cell chain for `(De2 + sigma) Lc 2^60 - Lc 2^60 S_b(-y)` (`sigma <= S_b(-rho)` a rational lower
bound, `Lc` a common multiple of `1, ..., len`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed

def sbNegGo (Lc : ℤ) : List ℤ → ℕ → List ℤ
  | [], _ => []
  | b :: bs, j => ((-1) ^ (j + 1) * b * (Lc / ((j : ℤ) + 1))) :: sbNegGo Lc bs (j + 1)

def sbNegInt (Lc : ℤ) (Bn : List ℤ) : List ℤ := 0 :: sbNegGo Lc Bn 0

theorem sbNegGo_eval (Lc : ℤ) (Bn : List ℤ) : ∀ (j0 : ℕ) (y : ℝ),
    zv (sbNegGo Lc Bn j0) y = ∑ i ∈ Finset.range Bn.length,
      (((-1 : ℤ) ^ (j0 + i + 1) * Bn.getD i 0 * (Lc / (((j0 + i : ℕ) : ℤ) + 1)) : ℤ) : ℝ) * y ^ i := by
  induction Bn with
  | nil => intro j0 y; simp [sbNegGo, zv_nil]
  | cons b bs ih =>
    intro j0 y
    rw [sbNegGo, zv_cons, ih (j0 + 1) y, List.length_cons, Finset.sum_range_succ', add_comm,
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero, pow_zero, mul_one]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
    have e : j0 + 1 + i = j0 + (i + 1) := by ring
    rw [e, pow_succ]
    ring

theorem getD_map_dy (Bn : List ℤ) (j : ℕ) :
    ((Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60)).getD j 0 : ℚ) = ((Bn.getD j 0 : ℤ) : ℚ) / 2 ^ 60 := by
  induction Bn generalizing j with
  | nil => simp
  | cons a g ih =>
    cases j with
    | zero => simp
    | succ n => simp only [List.map_cons, List.getD_cons_succ]; exact ih n

theorem sbNegInt_eval (Lc : ℤ) (Bn : List ℤ)
    (hd : ∀ i < Bn.length, (((i : ℕ) : ℤ) + 1) ∣ Lc) (y : ℝ) :
    zv (sbNegInt Lc Bn) y = (Lc : ℝ) * 2 ^ 60 *
      barrierTrialS (bSeq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))) (-y) := by
  unfold sbNegInt
  rw [zv_cons, sbNegGo_eval Lc Bn 0 y]
  unfold barrierTrialS
  have := tsum_bSeq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))
    (fun k t => t * (-y) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, List.length_map]
  simp only [Int.cast_zero, zero_add]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < Bn.length := Finset.mem_range.mp hi
  rw [getD_map_dy]
  have hdv := hd i hi'
  have hne : (((i : ℕ) : ℤ) + 1) ≠ 0 := by positivity
  have hc : (((Lc / (((0 + i : ℕ) : ℤ) + 1) : ℤ)) : ℝ) = (Lc : ℝ) / ((i : ℝ) + 1) := by
    have := Int.cast_div (α := ℝ) (m := Lc) (n := ((i : ℕ) : ℤ) + 1) hdv
      (by exact_mod_cast hne)
    simpa using this
  push_cast
  rw [zero_add] at hc
  simp only [zero_add, hc]
  have hi0 : ((i : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ, pow_succ, neg_pow]
  field_simp
  ring

/-- **`De2`** from the cell chain. -/
theorem De2_of_cov {Bn : List ℤ} {Lc : ℤ} (hd : ∀ i < Bn.length, (((i : ℕ) : ℤ) + 1) ∣ Lc)
    (hLc : 0 < Lc) {ρ σ De2 : ℚ} (c0 : ℤ) (hc0 : (c0 : ℚ) = (De2 + σ) * Lc * 2 ^ 60)
    (hσ : σ ≤ Sbq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60)) (-ρ))
    {S : ℕ} {A B : ℤ} {cs : List ℤ}
    (hcov : zNonnegCov (zAdd [c0] (zSmul (-1) (sbNegInt Lc Bn))) S A cs B = true) {y : ℝ}
    (h1 : (A : ℝ) / 2 ^ S ≤ y) (h2 : y ≤ (B : ℝ) / 2 ^ S) :
    barrierTrialS (bSeq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))) (-y) -
      barrierTrialS (bSeq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))) (-(ρ : ℝ)) ≤ (De2 : ℝ) := by
  have := zNonnegCov_sound _ S cs A B hcov y h1 h2
  rw [zv_add, zv_cons, zv_nil, zv_smul, sbNegInt_eval Lc Bn hd y] at this
  have hb := barrierTrialS_bSeq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60)) (-ρ)
  push_cast at hb
  rw [hb]
  have hσ' : (σ : ℝ) ≤ (Sbq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60)) (-ρ) : ℝ) := by
    exact_mod_cast hσ
  have hc0' : (c0 : ℝ) = ((De2 : ℝ) + σ) * Lc * 2 ^ 60 := by exact_mod_cast hc0
  have hpos : (0 : ℝ) < (Lc : ℝ) * 2 ^ 60 := by
    have : (0 : ℝ) < Lc := by exact_mod_cast hLc
    positivity
  push_cast at this
  rw [hc0'] at this
  set X := barrierTrialS (bSeq (Bn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))) (-y)
  have h3 : 0 ≤ ((De2 : ℝ) + σ - X) * ((Lc : ℝ) * 2 ^ 60) := by nlinarith [this]
  have h4 := nonneg_of_mul_nonneg_left h3 hpos
  linarith

end CatalanMeasure.Signed.Consts
