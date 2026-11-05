module

public import Submission.CatalanMeasure.GenD.Signed.Energy

/-!
# Fixed (marked) nodes in the signed second-sheet energy bound: fields and the A7 interface

The `log 2` count `fixLog2` of the fixed rows and the bound of `constFix` by `constTotal`, the A7
interface for fixed nodes `SpikeCompareFixed` (the marked positives sit in the positive list of the
route II ratio), the η-split and the linearisation of Lemma R′.  The master inequality, the contract and the energy
theorem with first-kind fixed and near-type nodes are `EnergyNear`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### Sums over the four populations -/

theorem sum_split4 (F : ℝ → ℝ) {k q m1 m2 : ℕ} (xn : Fin k → ℝ) (yn : Fin m1 → ℝ)
    (gp : Fin q → ℝ) (yp : Fin m2 → ℝ) :
    ∑ i, F (Fin.append (Fin.append xn yn) (Fin.append gp yp) i) =
      ((∑ b, F (xn b)) + ∑ j, F (yn j)) + ((∑ p, F (gp p)) + ∑ j, F (yp j)) := by
  rw [row_sum_split, row_sum_split, row_sum_split]

/-- The remainder constant `REMC = (1 + 1/ε)/8` of NOTES §12.1, `ε = 1 - 2η`. -/
def remC (ε : ℝ) : ℝ := (1 + 1 / ε) / 8

/-! ### The `log 2` count and the constant with fixed rows -/

/-- The `log 2` coefficient of the fixed rows in the budget (NOTES-ETA §1.4): with `α` the fixed
fraction and `η = (1 - ε)/2`, `constFix ≤ constTotal n + fixLog2 ε α · log 2`. -/
def fixLog2 (ε α : ℝ) : ℝ := (2 * α - α ^ 2) + ((1 - ε) / 2) * (α - α ^ 2 / 4) - α ^ 2 / 4

/-- The D7.1 error is monotone in the row mass. -/
theorem SignedData.eD7_mono (D : SignedData) (hC : 0 ≤ D.Cb) (hτ : D.τ ∈ Ioo (0 : ℝ) 1)
    (hη : D.η ≤ 1) {W W' : ℝ} (hW : 0 ≤ W) (hWW : W ≤ W') : D.eD7 W ≤ D.eD7 W' := by
  unfold SignedData.eD7
  have hK : 0 ≤ 1 - D.τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have hK0 : 0 < 1 - D.τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have hL : 0 ≤ 1 + Real.log (1 / (1 - D.τ ^ 2)) := by
    have : 0 ≤ Real.log (1 / (1 - D.τ ^ 2)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hK0]; nlinarith [hτ.1])
    linarith
  have hc : 0 ≤ D.Cb * (1 - D.τ ^ 2) * (1 + Real.log (1 / (1 - D.τ ^ 2))) := by positivity
  have h1 : 12 * (W + 1) * D.Cb * (1 - D.τ ^ 2) * (1 + Real.log (1 / (1 - D.τ ^ 2))) +
      2 * (1 - D.τ ^ 2) * (2 * (W + 1)) ^ 2 ≤
      12 * (W' + 1) * D.Cb * (1 - D.τ ^ 2) * (1 + Real.log (1 / (1 - D.τ ^ 2))) +
      2 * (1 - D.τ ^ 2) * (2 * (W' + 1)) ^ 2 := by
    have hWW1 : W + 1 ≤ W' + 1 := by linarith
    have hW1 : 0 ≤ W + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hWW1 hc, mul_le_mul_of_nonneg_left
      (mul_le_mul hWW1 hWW1 hW1 (hW1.trans hWW1)) hK]
  exact mul_le_mul_of_nonneg_left h1 (by linarith)

/-- **The constant with fixed rows against the all-free constant** (`ν = n`, `pf + M = n`). -/
theorem SignedData.constFix_le (D : SignedData) (hC : 0 ≤ D.Cb) (he : D.e ∈ Ioo (0 : ℝ) (1 / 8))
    (hη : D.η ≤ 1) {pf M n : ℕ} (hn : pf + M = n) (hνn : D.ν = (n : ℝ)) (hν : 0 < D.ν) :
    D.constFix pf M ≤
      D.constTotal n + fixLog2 (1 - 2 * D.η) ((M : ℝ) / D.ν) * Real.log 2 := by
  have hτ : D.τ ∈ Ioo (0 : ℝ) 1 := realEnergyTau_bounds he
  have hnR : (pf : ℝ) + M = n := by exact_mod_cast hn
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hpf0 : (0 : ℝ) ≤ pf := Nat.cast_nonneg pf
  have hW0 : 0 ≤ ((pf : ℝ) + (M : ℝ) / 2) / D.ν := by positivity
  have hWle : ((pf : ℝ) + (M : ℝ) / 2) / D.ν ≤ (n : ℝ) / D.ν :=
    div_le_div_of_nonneg_right (by linarith) hν.le
  have hmono := D.eD7_mono hC hτ hη hW0 hWle
  have h1 : (n : ℝ) / D.ν = 1 := by rw [← hνn]; exact div_self hν.ne'
  have h2 : (pf : ℝ) / D.ν = 1 - (M : ℝ) / D.ν := by
    rw [eq_sub_iff_add_eq, ← add_div, hnR, h1]
  have h3 : ((pf : ℝ) + (M : ℝ) / 2) / D.ν = 1 - ((M : ℝ) / D.ν) / 2 := by
    rw [add_div, h2]; ring
  unfold SignedData.constFix SignedData.constTotal fixLog2
  rw [h1] at hmono ⊢
  rw [h3] at hmono ⊢
  rw [h2]
  nlinarith [hmono]

/-! ### The A7 interface and the deterministic theorem -/

/-- **The A7 interface with fixed nodes (bound form).**  `LR` is the logarithm of the route II
ratio of the whole configuration; for configurations of the class `Cls` it is bounded by the
consumer's expression at the TRUE positions of the combined sign-split node lists, plus the
spike cost of the positive nodes (free and fixed). -/
def SpikeCompareFixed (D : SignedData) (c' : ℝ) {k q m1 m2 : ℕ}
    (Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ) : Prop :=
  ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ),
    (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
    (∀ b, yn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, yp p ∈ Ioo (0 : ℝ) 1) → Cls xn gp yn yp →
    LR xn gp yn yp / D.ν ^ 2 ≤
      logPref (Fin.append xn yn) (Fin.append gp yp) / D.ν ^ 2 +
        D.numB (Fin.append xn yn) (Fin.append gp yp) - D.denB (Fin.append gp yp) +
        D.spikeTerm (Fin.append gp yp) + D.errJ3 c' ((k + m1) + (q + m2))

/-- **`SpikeCompareFixed` at the configuration's Heine count** (NOTES-ETA §5.1): the class gives
`0 < sp` (reference count) and `sp + g ≤ q + m₂` (positive rows), and the bound holds for
`D.withCount (q + m₂ - g)`. -/
def SpikeCompareFixedCount (D : SignedData) (c' : ℝ) {k q m1 m2 : ℕ}
    (Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ) : Prop :=
  (∀ xn gp yn yp, Cls xn gp yn yp → 0 < D.sp ∧ D.sp + D.g ≤ q + m2) ∧
    SpikeCompareFixed (D.withCount (q + m2 - D.g)) c' Cls LR

/-! ### The η-split and the linearisation of Lemma R′ (PROOF-A 17.33, NOTES §§11-12.1)

Sequence-level statements, with `L(u) = ip u u`.  The fixed nodes enter the `(1 - η)`-share of
the Vandermonde through `I(c)`, `c = a + b/2`; the pointwise form of `eta_split` is the first
square of `quad_master_eta` (EnergyNear), and Lemma R′ turns `REMC · L(b⁺)` into the field
`remC (1 - 2η) · α · (-log (1 - x²))` of `fPosMR`. -/

/-- Young: `L(c + d) ≤ (1 + ε) L(c) + (1 + 1/ε) L(d)`. -/
theorem ip_add_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c d : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) {ε : ℝ} (hε : 0 < ε) :
    ip (fun n => c n + d n) (fun n => c n + d n) ≤ (1 + ε) * ip c c + (1 + 1 / ε) * ip d d := by
  have hcd : IsGeom τ (fun n => c n + d n) := hc.add hd
  have hL := hasSum_ip hτ hcd hcd
  have hR := ((hasSum_ip hτ hc hc).mul_left (1 + ε)).add
    ((hasSum_ip hτ hd hd).mul_left (1 + 1 / ε))
  refine hasSum_le (fun n => ?_) hL hR
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 2 * (c n * d n) ≤ ε * (c n * c n) + (1 / ε) * (d n * d n) := by
    have h0 : 0 ≤ (ε * c n - d n) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e : (ε * c n - d n) ^ 2 / ε =
        ε * (c n * c n) - 2 * (c n * d n) + (1 / ε) * (d n * d n) := by
      field_simp
      ring
    linarith
  show (c n + d n) * (c n + d n) / ((n : ℝ) + 1) ≤
    (1 + ε) * (c n * c n / ((n : ℝ) + 1)) + (1 + 1 / ε) * (d n * d n / ((n : ℝ) + 1))
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_le_div_iff_of_pos_right hn]
  nlinarith [h2]

/-- **The η-split** (NOTES §12.1).  With `I(c) ≥ L(c⁺)` (Theorem 7.1 / D7.1), `ρ⁺ = c⁺ + b⁺/2`,
`ε = 1 - 2η ∈ (0, 1]` and `REMC = (1 + 1/ε)/8`:
`(1 - η) I - (1/2) L(ρ⁺) ≥ - REMC · L(b⁺)`. -/
theorem eta_split {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {cp bp : ℕ → ℝ} (hc : IsGeom τ cp)
    (hb : IsGeom τ bp) {I ε : ℝ} (hε : 0 < ε) (hI : ip cp cp ≤ I) :
    -(remC ε * ip bp bp) ≤ (1 - (1 - ε) / 2) * I -
      (1 / 2) * ip (fun n => cp n + bp n / 2) (fun n => cp n + bp n / 2) := by
  have hb2 : IsGeom τ (fun n => bp n / 2) := by
    simpa [div_eq_inv_mul] using hb.const_mul ((2 : ℝ)⁻¹)
  have hy := ip_add_le hτ hc hb2 hε
  have hq : ip (fun n => bp n / 2) (fun n => bp n / 2) = ip bp bp / 4 := by
    unfold ip
    rw [← tsum_div_const]
    refine tsum_congr fun n => ?_
    ring
  rw [hq] at hy
  unfold remC
  have h1 : (1 + ε) / 2 * ip cp cp ≤ (1 + ε) / 2 * I :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  have h3 : 1 - (1 - ε) / 2 = (1 + ε) / 2 := by ring
  rw [h3]
  have e : (1 + 1 / ε) / 8 * ip bp bp = (1 / 2) * ((1 + 1 / ε) * (ip bp bp / 4)) := by ring
  rw [e]
  nlinarith [h1, hy]

/-- `-log (1 - ab) ≤ (-log (1 - a²) - log (1 - b²))/2` (from `(1 - ab)² ≥ (1 - a²)(1 - b²)`). -/
theorem neg_log_pair_le {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) :
    -Real.log (1 - a * b) ≤ (-Real.log (1 - a ^ 2) - Real.log (1 - b ^ 2)) / 2 := by
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith [ha'.1, ha'.2]
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith [hb'.1, hb'.2]
  have hab : 0 < 1 - a * b := by nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]
  have key : (1 - a ^ 2) * (1 - b ^ 2) ≤ (1 - a * b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h := Real.log_le_log (mul_pos ha2 hb2) key
  rw [Real.log_mul ha2.ne' hb2.ne', Real.log_pow] at h
  push_cast at h
  linarith

/-- **Lemma R′, linearisation** (NOTES §11): for the positive fixed nodes `yp`,
`L(b⁺) = ip (powSum yp) (powSum yp) ≤ (m/ν²) Σ_j -log (1 - y_j²)`, i.e. `α² ∫ -log(1-x²) dσ⁺`
with `α = m/ν`, `σ⁺` the empirical measure of the fixed nodes. -/
theorem lemmaR'_linearisation {m : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (yp : Fin m → ℝ) (hyp : ∀ j, yp j ∈ Ioo (0 : ℝ) 1) :
    ip (powSum τ ν yp) (powSum τ ν yp) ≤ ((m : ℝ) / ν ^ 2) * ∑ j, -Real.log (1 - yp j ^ 2) := by
  have hy : ∀ i, |τ * yp i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1]
    have : |yp i| < 1 := by rw [abs_of_pos (hyp i).1]; exact (hyp i).2
    nlinarith [hτ.2, abs_nonneg (yp i), hτ.1]
  have h := (hasSum_pair_powSum (τ := τ) hν hy hy).tsum_eq
  have hip : ip (powSum τ ν yp) (powSum τ ν yp) =
      -(∑ i, ∑ j, Real.log (1 - (τ * yp i) * (τ * yp j))) / ν ^ 2 := h
  rw [hip]
  have hpair : ∀ i j, -Real.log (1 - (τ * yp i) * (τ * yp j)) ≤
      (-Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2)) / 2 := by
    intro i j
    have h1 := neg_log_pair_le (hy i) (hy j)
    have hmono : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → -Real.log (1 - (τ * t) ^ 2) ≤ -Real.log (1 - t ^ 2) := by
      intro t ht
      have h0 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
      have hle : 1 - t ^ 2 ≤ 1 - (τ * t) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hτ2 (sq_nonneg t)]
      have := Real.log_le_log h0 hle
      linarith
    have := hmono _ (hyp i)
    have := hmono _ (hyp j)
    linarith
  have hs : -(∑ i, ∑ j, Real.log (1 - (τ * yp i) * (τ * yp j))) ≤
      (m : ℝ) * ∑ j, -Real.log (1 - yp j ^ 2) := by
    have h1 : -(∑ i, ∑ j, Real.log (1 - (τ * yp i) * (τ * yp j))) =
        ∑ i, ∑ j, -Real.log (1 - (τ * yp i) * (τ * yp j)) := by
      simp only [Finset.sum_neg_distrib]
    have h2 : ∑ i : Fin m, ∑ j : Fin m, (-Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2)) / 2 =
        (m : ℝ) * ∑ j, -Real.log (1 - yp j ^ 2) := by
      have e : ∀ i : Fin m, ∑ j : Fin m,
          (-Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2)) / 2 =
          ((m : ℝ) * (-Real.log (1 - yp i ^ 2)) + ∑ j, -Real.log (1 - yp j ^ 2)) / 2 := by
        intro i
        rw [← Finset.sum_div]
        congr 1
        have : ∀ j : Fin m, -Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2) =
            -Real.log (1 - yp i ^ 2) + -Real.log (1 - yp j ^ 2) := fun j => by ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      simp only [e]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h1, ← h2]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  rw [div_eq_mul_inv, mul_comm ((m : ℝ) / ν ^ 2), div_eq_mul_inv]
  calc -(∑ i, ∑ j, Real.log (1 - τ * yp i * (τ * yp j))) * (ν ^ 2)⁻¹
      ≤ ((m : ℝ) * ∑ j, -Real.log (1 - yp j ^ 2)) * (ν ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

/-- The remainder field of `fPosFixR` summed over the positive fixed nodes bounds `REMC · L(b⁺)`
by the linearisation. -/
theorem remainder_sum_eq {m : ℕ} {ν rc : ℝ} (hν : 0 < ν) (yp : Fin m → ℝ) :
    (1 / ν) * ∑ j, rc * ((m : ℝ) / ν) * (-Real.log (1 - yp j ^ 2)) =
      rc * (((m : ℝ) / ν ^ 2) * ∑ j, -Real.log (1 - yp j ^ 2)) := by
  rw [← Finset.mul_sum]
  field_simp

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.eta_split
#print axioms CatalanMeasure.Signed.ip_add_le
#print axioms CatalanMeasure.Signed.lemmaR'_linearisation
#print axioms CatalanMeasure.Signed.neg_log_pair_le
#print axioms CatalanMeasure.Signed.remainder_sum_eq
#print axioms CatalanMeasure.Signed.SignedData.constFix_le
