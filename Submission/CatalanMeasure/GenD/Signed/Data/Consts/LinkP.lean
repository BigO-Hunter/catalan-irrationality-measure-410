module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeP
public import Submission.CatalanMeasure.GenD.Signed.Phase2Contract

/-!
# D2 constants: pointwise polynomial certificates of `LinkCert` (generic soundness)

* `chebGen c0 g`: the monomial form of `c0 + sum_{k >= 1} g_k T_k`; `lpEval_chebGen`.
* `gcertG e g`: the coefficients `G_k = g_{k+1} / (1-e)^(k+1)` of `PolyCert` for which
  `evalCert e g.length (gcertG e g) c0 = c0 + sum g_{k+1} T_{k+1}` (`evalCert_gcert`).
* `evalCert_le_of_cov`: `evalCert <= M` on a dyadic interval from an integer cell chain
  (the fields `hCp_neg/pos`, `hCm_neg/pos`).
* `slope_sound`: `evalCert + 3/16 <= 1 - slopeKernel t` on `[-1, 1]` from the cell chain of `slopeN`
  (the field `hPt` with `hmesh / ts = 3/16`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed

def zMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => zAdd (zSmul a q) (0 :: zMul p q)

theorem zv_mul (p q : List ℤ) (x : ℝ) : zv (zMul p q) x = zv p x * zv q x := by
  induction p with
  | nil => simp [zMul, zv_nil]
  | cons a p ih =>
    simp only [zMul, zv_add, zv_smul, zv_cons, ih]; ring

def chebGen (c0 : ℚ) (g : List ℚ) : List ℚ := chebGo (g.map (fun x => x / 2)) [1] [0, 1] [c0]

theorem getD_map_half (g : List ℚ) (j : ℕ) :
    (g.map (fun x => x / 2)).getD j 0 = g.getD j 0 / 2 := by
  induction g generalizing j with
  | nil => simp
  | cons a g ih =>
    cases j with
    | zero => simp
    | succ n => simp only [List.map_cons, List.getD_cons_succ]; exact ih n

theorem lpEval_chebGen (c0 : ℚ) (g : List ℚ) (y : ℝ) :
    lpEval (chebGen c0 g) y = c0 +
      ∑ j ∈ Finset.range g.length, ((g.getD j 0 : ℚ) : ℝ) *
        (Polynomial.Chebyshev.T ℝ ((j + 1 : ℕ) : ℤ)).eval y := by
  have hT0 : lpEval [1] y = (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval y := by
    simp [lpEval]
  have hT1 : lpEval [0, 1] y = (Polynomial.Chebyshev.T ℝ ((0 + 1 : ℕ) : ℤ)).eval y := by
    simp [lpEval, Polynomial.Chebyshev.T_one]
  have h := chebGo_eval (g.map (fun x => x / 2)) 0 [1] [0, 1] [c0] y hT0 hT1
  unfold chebGen
  rw [h, List.length_map]
  simp only [lpEval, getD_map_half, mul_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e3 : 0 + 1 + j = j + 1 := by ring
  rw [e3]; push_cast; ring

noncomputable def gcertG (e : ℝ) (g : List ℚ) (k : ℕ) : ℝ := ((g.getD k 0 : ℚ) : ℝ) / (1 - e) ^ (k + 1)

theorem evalCert_gcert {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (c0 : ℚ) (g : List ℚ) (y : ℝ) :
    evalCert e g.length (gcertG e g) (c0 : ℝ) y = lpEval (chebGen c0 g) y := by
  rw [lpEval_chebGen]
  unfold evalCert
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hτ : (1 - e) ≠ 0 := by linarith [he.2]
  have : realEnergyTau e = 1 - e := rfl
  rw [this, gcertG]
  field_simp

theorem evalCert_le_of_cov {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {c0 : ℚ} {g : List ℚ}
    {Pn : List ℤ} {sh S : ℕ} {A B : ℤ} {cs : List ℤ} {M : ℤ}
    (hm : chebGen c0 g = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ sh))
    (hcov : zNonnegCov (zAdd [M * 2 ^ sh] (zSmul (-1) Pn)) S A cs B = true) {y : ℝ}
    (h1 : (A : ℝ) / 2 ^ S ≤ y) (h2 : y ≤ (B : ℝ) / 2 ^ S) :
    evalCert e g.length (gcertG e g) (c0 : ℝ) y ≤ M := by
  rw [evalCert_gcert he, hm, lpEval_dyadic]
  have := zNonnegCov_sound _ S cs A B hcov y h1 h2
  rw [zv_add, zv_cons, zv_nil, zv_smul] at this
  push_cast at this
  have hp : (0 : ℝ) < 2 ^ sh := by positivity
  rw [div_le_iff₀ hp]
  linarith

/-- The integer polynomial of the slope inequality, `t = T / 2^11`, `P = Pn / 2^40`, `hmesh/ts = 3/16`
(scaled by `2^84`). -/
def slopeN (Pn : List ℤ) (T : ℤ) : List ℤ :=
  zAdd (zSmul (2 ^ 40) [0, 0, 2 ^ 44 + T ^ 4, 0, 2 * 2 ^ 22 * T ^ 2])
    (zSmul (-1) (zMul (zAdd Pn [3 * 2 ^ 36]) [2 ^ 22 * T ^ 2, 0, 2 ^ 44 + T ^ 4, 0, 2 ^ 22 * T ^ 2]))

theorem slopeN_eval (Pn : List ℤ) (T : ℤ) (y : ℝ) :
    zv (slopeN Pn T) y = 2 ^ 84 *
      (y ^ 2 * (1 + y ^ 2 * ((T : ℝ) / 2 ^ 11) ^ 2) +
        y ^ 2 * ((T : ℝ) / 2 ^ 11) ^ 2 * (((T : ℝ) / 2 ^ 11) ^ 2 + y ^ 2) -
        (zv Pn y / 2 ^ 40 + 3 / 16) * ((((T : ℝ) / 2 ^ 11) ^ 2 + y ^ 2) *
          (1 + y ^ 2 * ((T : ℝ) / 2 ^ 11) ^ 2))) := by
  unfold slopeN
  simp only [zv_add, zv_smul, zv_mul, zv_cons, zv_nil, zv_add]
  push_cast
  field_simp
  ring

theorem slope_sound {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {c0 : ℚ} {g : List ℚ} {Pn : List ℤ}
    {S : ℕ} {T : ℕ} {cs : List ℤ} (hT : 0 < T)
    (hm : chebGen c0 g = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ 40))
    (hcov : covM1P1 (slopeN Pn T) S cs = true) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert e g.length (gcertG e g) (c0 : ℝ) y + 3 / 16 ≤
      1 - slopeKernel ((T : ℝ) / 2 ^ 11) y := by
  have h1 := covM1P1_sound hcov y hy
  rw [slopeN_eval] at h1
  have h84 : (0 : ℝ) < 2 ^ 84 := by positivity
  have hN := (mul_nonneg_iff_of_pos_left h84).mp h1
  rw [evalCert_gcert he, hm, lpEval_dyadic]
  set t : ℝ := (T : ℝ) / 2 ^ 11 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hD : 0 < (t ^ 2 + y ^ 2) * (1 + y ^ 2 * t ^ 2) := by positivity
  unfold slopeKernel
  have key : 1 - (t ^ 2 / (t ^ 2 + y ^ 2) - y ^ 2 * t ^ 2 / (1 + y ^ 2 * t ^ 2)) -
      (zv Pn y / 2 ^ 40 + 3 / 16) =
      (y ^ 2 * (1 + y ^ 2 * t ^ 2) + y ^ 2 * t ^ 2 * (t ^ 2 + y ^ 2) -
        (zv Pn y / 2 ^ 40 + 3 / 16) * ((t ^ 2 + y ^ 2) * (1 + y ^ 2 * t ^ 2))) /
        ((t ^ 2 + y ^ 2) * (1 + y ^ 2 * t ^ 2)) := by
    field_simp
    ring
  have : 0 ≤ 1 - (t ^ 2 / (t ^ 2 + y ^ 2) - y ^ 2 * t ^ 2 / (1 + y ^ 2 * t ^ 2)) -
      (zv Pn y / 2 ^ 40 + 3 / 16) := by
    rw [key]; exact div_nonneg hN hD.le
  linarith

end CatalanMeasure.Signed.Consts
