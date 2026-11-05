module

public import Submission.CatalanMeasure.GenD.Analytic.AtomBase
public import Submission.CatalanMeasure.GenD.Analytic.MarkedMixedMajorant
public import Submission.CatalanMeasure.GenD.Analytic.MarkedSecond
public import Submission.CatalanMeasure.Parametric.MarkedAtomAlmostEverywhere
public import Submission.CatalanMeasure.Lemma6

@[expose] public section

/-!
# Analytic layer, group 3: weighted atom points and the atom determinant bound

Generic versions of `GapAtomCost`:

* `MarkedSheetBound P G target r` -- the output of group 2's `marked_sheet_on`
  (`markedSheetProduct ≤ 5^m · sheetPrefactor · exp((n0 N)² (-target + log 2/2 + ε) + r N m)`);
* `WeightedAtomPoint P τ G target ρ` -- generic `WeightedAtomPointOn`;
* `weighted_atom_point_of_sheet` -- generic `weighted_atom_point_on` from the sheet bound and
  the node-weight bound (group 4's `GapWeightBounds`);
* `weighted_atom_det` -- generic `weighted_atom_det_on`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial OAI.InternalCatalan Set Finset MeasureTheory Matrix Filter CatalanMeasure.Parametric
open scoped Topology BigOperators

noncomputable section

/-- Output of group 2's `marked_sheet_on`. -/
def MarkedSheetBound (P : Parameters) (G : ℝ → Prop) (target r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      markedSheetProduct P N hpm x y s ≤
        (5 : ℝ) ^ m * sheetPrefactor P N *
          Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m)

def WeightedAtomPoint (P : Parameters) (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop) (target ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (_hpm : p + m = P.n N)
      (E : Fin p → ℕ), Function.Injective E → (∀ i, E i < P.n N) →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin ((P.n0 - P.g0) * N)),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      (∀ j, realCoordinateInv (y j) = τ N (a j)) →
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
        (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| *
        (∏ j, |restrictedWeight P N (k j) (τ N) (a j)|) ≤
      sheetPrefactor P N * (540000 * (N : ℝ)) ^ m *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          ρ * N * m)

theorem weighted_atom_point_of_sheet {target r w : ℝ} (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hsheet : MarkedSheetBound P G target r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (τ N a)| *
        |restrictedWeight P N k (τ N) a| ≤
          108000*(N : ℝ)*Real.exp (w*N)) : WeightedAtomPoint P τ G target (r + w) := by
  intro ε hε
  filter_upwards [hsheet ε hε,
      hweights, eventually_gt_atTop (0 : ℕ)]
    with N hsheet_N hw hN p m hpm E hEi hEn x y s k a hx hx0 hy hy0 hGy hs hzi hsi hcoord
  let β := fun j => restrictedWeight P N (k j) (τ N) (a j)
  let Q : ℝ := 108000 * N * Real.exp (w * N)
  have hweight (j : Fin m) :
      |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| ≤ Q := by
    rw [hcoord j]
    exact hw (k j) (a j)
  have hbase := original_poly_atoms_mixedDouble_mul_weight_le hP hN hpm
    E hEi hEn x y s β hx hx0 hy hy0 hs hweight
  have hp := hsheet_N p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi
  have hQ : 0 ≤ Q ^ m := by dsimp [Q]; positivity
  have hc : (5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m = (540000 * (N : ℝ)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
      (-target + Real.log 2 / 2 + ε) + r * N * m) *
      Real.exp (w * (N : ℝ)) ^ m =
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
        (-target + Real.log 2 / 2 + ε) + (r+w) * N * m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ markedSheetProduct P N hpm x y s * Q ^ m := hbase
    _ ≤ ((5 : ℝ) ^ m * sheetPrefactor P N *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m)) * Q ^ m := mul_le_mul_of_nonneg_right hp hQ
    _ = sheetPrefactor P N * ((5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m) *
        (Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m) * Real.exp (w * (N : ℝ)) ^ m) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, he]

/-- Factor-free sheet bound (S1): the same shape as `MarkedSheetBound`, for the sheet product
`markedSheetFree` taken **without** the factor `(∏ (1 + s_i))^m`.  The cost `r` is the
`58 c₂''` of PROOF-RHO 2.3. -/
def MarkedSheetFreeBound (P : Parameters) (G : ℝ → Prop) (target r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      markedSheetFree P N hpm x y s ≤
        (5 : ℝ) ^ m * sheetPrefactor P N *
          Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m)

/-- `WeightedAtomPoint` for the column indices `k_j` that enumerate (injectively) columns of
`{0, …, n-1}` not selected by `E` -- exactly the columns the atom determinant leaves free
(`weighted_atom_det`). -/
def WeightedAtomPointBinom (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop) (target ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (_hpm : p + m = P.n N)
      (E : Fin p → ℕ), Function.Injective E → (∀ i, E i < P.n N) →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin ((P.n0 - P.g0) * N)),
      Function.Injective k → (∀ j, k j < P.n N) → (∀ j i, k j ≠ E i) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      (∀ j, realCoordinateInv (y j) = τ N (a j)) →
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
        (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| *
        (∏ j, |restrictedWeight P N (k j) (τ N) (a j)|) ≤
      sheetPrefactor P N * (540000 * (N : ℝ)) ^ m *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          ρ * N * m)

/-- **S1, weight-side assembly.**  The factor-free sheet bound and the combined per-column weight
bound `|common(τ_a)| |weight_k(τ_a)| β_{p,m}(k) ≤ 108000 N exp(Ψ N)`, uniform in `m`, give the
weighted atom point with cost `r + Ψ`. -/
theorem weighted_atom_point_of_sheet_binom {target r w : ℝ} (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hsheet : MarkedSheetFreeBound P G target r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (k : ℕ), k < P.n N → ∀ (a : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (w * N)) :
    WeightedAtomPointBinom P τ G target (r + w) := by
  intro ε hε
  filter_upwards [hsheet ε hε, hweights, eventually_gt_atTop (0 : ℕ)]
    with N hsheet_N hw hN p m hpm E hEi hEn x y s k a hki hkn hkE hx hx0 hy hy0 hGy hs hzi hsi
      hcoord
  let β := fun j => restrictedWeight P N (k j) (τ N) (a j)
  let Q : ℝ := 108000 * N * Real.exp (w * N)
  have hweight (j : Fin m) :
      |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| *
        (CatalanMeasure.binomBeta p m (k j) : ℝ) ≤ Q := by
    rw [hcoord j]
    exact hw p m hpm (k j) (hkn j) (a j)
  have hbase := original_poly_atoms_mixedDouble_binom_mul_weight_le hP hN hpm
    E hEi hEn x y s β k hki hkn hkE hx hx0 hy hy0 hs hweight
  have hp := hsheet_N p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi
  have hQ : 0 ≤ Q ^ m := by dsimp [Q]; positivity
  have hc : (5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m = (540000 * (N : ℝ)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
      (-target + Real.log 2 / 2 + ε) + r * N * m) *
      Real.exp (w * (N : ℝ)) ^ m =
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
        (-target + Real.log 2 / 2 + ε) + (r+w) * N * m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ markedSheetFree P N hpm x y s * Q ^ m := hbase
    _ ≤ ((5 : ℝ) ^ m * sheetPrefactor P N *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m)) * Q ^ m := mul_le_mul_of_nonneg_right hp hQ
    _ = sheetPrefactor P N * ((5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m) *
        (Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m) * Real.exp (w * (N : ℝ)) ^ m) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, he]

/-- The exponent rate `H~(κ)` of the binomial factor `β(k)` at `κ = k/n`: the binary entropy of
`κ` for `κ ≥ 1/2` and `log 2` for `κ < 1/2` (PROOF-RHO 2.1). -/
def binomRate (κ : ℝ) : ℝ := if 1 ≤ 2 * κ then Real.binEntropy κ else Real.log 2

/-- Lemma V rate, uniform in `m`: `β_{p,m}(k) ≤ n exp(n H~(k/n))` for every split `p + m = n`. -/
theorem binomBeta_le_mul_exp {p m n k : ℕ} (hpm : p + m = n) (hk : k < n) :
    (CatalanMeasure.binomBeta p m k : ℝ) ≤ n * Real.exp (n * binomRate ((k : ℝ) / n)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [CatalanMeasure.binomBeta, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    positivity
  · have hnR : (0 : ℝ) < n := by linarith
    have hiff : 1 ≤ 2 * ((k : ℝ) / n) ↔ n ≤ 2 * k := by
      rw [← mul_div_assoc, one_le_div hnR]
      constructor <;> intro h <;> exact_mod_cast h
    unfold binomRate
    split_ifs with h'
    · have h := hiff.mp h'
      have hlog := CatalanMeasure.log_binomBeta_le_entropy p m n k hpm hm hk h
      rcases Nat.eq_zero_or_pos (CatalanMeasure.binomBeta p m k) with h0 | hpos
      · rw [h0]; simp only [Nat.cast_zero]; positivity
      · have hbpos : (0 : ℝ) < CatalanMeasure.binomBeta p m k := by exact_mod_cast hpos
        have hmR : (m : ℝ) ≤ n := by exact_mod_cast (show m ≤ n by omega)
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
        calc (CatalanMeasure.binomBeta p m k : ℝ)
            = Real.exp (Real.log (CatalanMeasure.binomBeta p m k)) :=
              (Real.exp_log hbpos).symm
          _ ≤ Real.exp (Real.log m + n * Real.binEntropy ((k : ℝ) / n)) := Real.exp_le_exp.mpr hlog
          _ = m * Real.exp (n * Real.binEntropy ((k : ℝ) / n)) := by
              rw [Real.exp_add, Real.exp_log hm0]
          _ ≤ _ := by gcongr
    · have h2 := CatalanMeasure.binomBeta_le_two_pow p m k
      have h2R : (CatalanMeasure.binomBeta p m k : ℝ) ≤ 2 ^ p := by exact_mod_cast h2
      have hpn : (2 : ℝ) ^ p ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have he : Real.exp (n * Real.log 2) = 2 ^ n := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      calc (CatalanMeasure.binomBeta p m k : ℝ) ≤ 2 ^ n := h2R.trans hpn
        _ = Real.exp (n * Real.log 2) := he.symm
        _ ≤ n * Real.exp (n * Real.log 2) := le_mul_of_one_le_left (Real.exp_pos _).le hn1

/-- Polynomial factors are eventually absorbed by any exponential rate. -/
theorem eventually_mul_pow_le_exp (C : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ d ≤ Real.exp (ε * N) := by
  have hδ : 0 < ε ^ d / (|C| + 1) := by positivity
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with N hN
  simp only [Function.comp_apply] at hN
  have he := Real.exp_pos (ε * N)
  have hN' : (ε * N) ^ d < ε ^ d / (|C| + 1) * Real.exp (ε * N) := by
    rw [Real.exp_neg] at hN
    have := (mul_inv_lt_iff₀ he).mp (by simpa [div_eq_mul_inv] using hN)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hεd : 0 < ε ^ d := by positivity
  have hC1 : 0 < |C| + 1 := by positivity
  have hNd : (N : ℝ) ^ d * ε ^ d < ε ^ d / (|C| + 1) * Real.exp (ε * N) := by
    rw [← mul_pow, mul_comm]; exact hN'
  have h2 : (N : ℝ) ^ d < Real.exp (ε * N) / (|C| + 1) := by
    have : (N : ℝ) ^ d * ε ^ d < ε ^ d * (Real.exp (ε * N) / (|C| + 1)) := by
      calc _ < _ := hNd
        _ = _ := by ring
    rw [mul_comm ((N : ℝ) ^ d)] at this
    exact lt_of_mul_lt_mul_left this hεd.le
  calc C * (N : ℝ) ^ d ≤ |C| * (N : ℝ) ^ d := by gcongr; exact le_abs_self C
    _ ≤ (|C| + 1) * (N : ℝ) ^ d := by gcongr; linarith
    _ ≤ (|C| + 1) * (Real.exp (ε * N) / (|C| + 1)) := by gcongr
    _ = _ := by field_simp

/-- **Weight side of S1, glue.**  A per-column bound
`|common(τ_a)| |weight_k(τ_a)| ≤ C₀ N^d exp(n ω(k/n))` together with
`ω(κ) + H~(κ) ≤ Ψ` on `[0,1]` gives, for every `w > n₀ Ψ`, the combined bound
`|common| |weight_k| β_{p,m}(k) ≤ 108000 N exp(w N)` for all splits `p + m = n`, eventually in `N`
(the hypothesis `hweights` of `weighted_atom_point_of_sheet_binom`). -/
theorem binom_hweights_of_column_bound (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) {C₀ Ψ w : ℝ} (d : ℕ) (ω : ℝ → ℝ)
    (hC₀ : 0 ≤ C₀)
    (hW : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, k < P.n N → ∀ a : Fin ((P.n0 - P.g0) * N),
      |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| ≤
        C₀ * (N : ℝ) ^ d * Real.exp ((P.n N : ℝ) * ω ((k : ℝ) / P.n N)))
    (hΨ : ∀ κ ∈ Icc (0 : ℝ) 1, ω κ + binomRate κ ≤ Ψ) (hw : (P.n0 : ℝ) * Ψ < w) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (k : ℕ), k < P.n N → ∀ (a : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (w * N) := by
  have hε : 0 < w - (P.n0 : ℝ) * Ψ := by linarith
  filter_upwards [hW, eventually_mul_pow_le_exp (C₀ * (P.n0 : ℝ) / 108000) d hε,
    eventually_gt_atTop (0 : ℕ)] with N hWN hgrow hN p m hpm k hk a
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ (P.n0 : ℝ) := Nat.cast_nonneg _
  have hnR : (0 : ℝ) ≤ (P.n N : ℝ) := Nat.cast_nonneg _
  have hκ : (k : ℝ) / P.n N ∈ Icc (0 : ℝ) 1 := by
    have hnpos : (0 : ℝ) < P.n N := by exact_mod_cast (show 0 < P.n N by omega)
    exact ⟨by positivity, (div_le_one hnpos).mpr (by exact_mod_cast hk.le)⟩
  have hb := binomBeta_le_mul_exp hpm hk
  have hΨk := hΨ _ hκ
  have hW0 := hWN k hk a
  have hWnn : 0 ≤ |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc _ ≤ (C₀ * (N : ℝ) ^ d * Real.exp ((P.n N : ℝ) * ω ((k : ℝ) / P.n N))) *
        ((P.n N : ℝ) * Real.exp ((P.n N : ℝ) * binomRate ((k : ℝ) / P.n N))) :=
        mul_le_mul hW0 hb (Nat.cast_nonneg _) (by positivity)
    _ = C₀ * (N : ℝ) ^ d * (P.n N : ℝ) *
        Real.exp ((P.n N : ℝ) * (ω ((k : ℝ) / P.n N) + binomRate ((k : ℝ) / P.n N))) := by
        rw [mul_add, Real.exp_add]; ring
    _ ≤ C₀ * (N : ℝ) ^ d * (P.n N : ℝ) * Real.exp ((P.n N : ℝ) * Ψ) := by
        gcongr
    _ = (C₀ * (P.n0 : ℝ) * (N : ℝ) ^ d) * N * Real.exp ((P.n0 : ℝ) * Ψ * N) := by
        rw [hn]; ring_nf
    _ ≤ (108000 * Real.exp ((w - (P.n0 : ℝ) * Ψ) * N)) * N * Real.exp ((P.n0 : ℝ) * Ψ * N) := by
        have h1 : C₀ * (P.n0 : ℝ) * (N : ℝ) ^ d ≤ 108000 * Real.exp ((w - (P.n0 : ℝ) * Ψ) * N) := by
          have := mul_le_mul_of_nonneg_left hgrow (by norm_num : (0 : ℝ) ≤ 108000)
          calc C₀ * (P.n0 : ℝ) * (N : ℝ) ^ d
              = 108000 * (C₀ * (P.n0 : ℝ) / 108000 * (N : ℝ) ^ d) := by ring
            _ ≤ _ := this
        gcongr
    _ = _ := by
        rw [show w * (N : ℝ) = (w - (P.n0 : ℝ) * Ψ) * N + (P.n0 : ℝ) * Ψ * N by ring,
          Real.exp_add]
        ring

/-- First-case factor-free bound (field sum `> -1`): the cost `c` is `n₀ c₁` of the new first
budget (PROOF-RHO 2.3). -/
def FreeFirstBound (P : Parameters) (target c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
    (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
    (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
    (-1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) →
    markedSheetFree P N hpm x y s ≤
      ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + c * N * m)

/-- Second-case factor-free bound for the marked fraction `m ≥ α₁ n` (the energy route without
`α(1-α) log 2`, cost `c = 58 c₂''`). -/
def FreeLargeBound (P : Parameters) (G : ℝ → Prop) (target c α1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
    α1 * (P.n N : ℝ) ≤ (m : ℝ) →
    (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
    (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
    (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
    (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
    markedSheetFree P N hpm x y s ≤
      5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + c * N * m)

/-- The signed near-type bound (`m ≤ α₁ n`, second case, rows restricted by `Nd`); this is
`Signed.SignedSecondSheetCoreNd` with `markedSheetCore` written as `markedSheetFree`
(definitionally equal). -/
def FreeNearBound (P : Parameters) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop) (target c alpha1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (m : ℝ) ≤ alpha1 * (P.n N : ℝ) →
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Nd N m y →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      markedSheetFree P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + c * N * m)

/-- Conformance: `free_first_bound_end` is `FreeFirstBound` at cost `n0 * c`. -/
theorem freeFirstBound_of_end {P : Parameters} (hP : Admissible P) {target c : ℝ}
    (D : FirstTrialBoundsEnd P target c) : FreeFirstBound P target ((P.n0 : ℝ) * c) :=
  free_first_bound_end hP D

/-- Conformance: `free_large_bound_end` is `FreeLargeBound` at cost `n0 * cost`. -/
theorem freeLargeBound_of_end {P : Parameters} (hP : Admissible P)
    {α1 target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P α1 target residual nearCap cost G) :
    FreeLargeBound P G target ((P.n0 : ℝ) * cost) α1 :=
  free_large_bound_end hP D

/-- **Bridge: signed sheet bound to the binomial weighted atom point.**  First case
(`FreeFirstBound`, cost `c₁`), second case with `m ≤ α₁ n` (the signed bound, `FreeNearBound` with
`Nd` satisfied by node images `y = realCoordinate ∘ τ ∘ a`, `a` injective) and second case with
`m ≥ α₁ n` (`FreeLargeBound`), each with cost at most `r`; the per-column binomial weight bound
`hweights` (`binom_hweights_of_column_bound`) has rate `w`.  Conclusion: cost `r + w`. -/
theorem weighted_atom_point_binom_of_signed {target r w c₁ c₂ c₃ α₁ : ℝ} (P : Parameters)
    (hP : Admissible P) (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hNd : ∀ N m (y : Fin m → ℝ) (a : Fin m → Fin ((P.n0 - P.g0) * N)), Function.Injective a →
      (∀ j, realCoordinateInv (y j) = τ N (a j)) → Nd N m y)
    (hfirst : FreeFirstBound P target c₁) (hnear : FreeNearBound P G Nd target c₂ α₁)
    (hlarge : FreeLargeBound P G target c₃ α₁)
    (hc₁ : c₁ ≤ r) (hc₂ : c₂ ≤ r) (hc₃ : c₃ ≤ r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (k : ℕ), k < P.n N → ∀ (a : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (w * N)) :
    WeightedAtomPointBinom P τ G target (r + w) := by
  intro ε hε
  filter_upwards [hfirst ε hε, hnear ε hε, hlarge ε hε, hweights, eventually_gt_atTop (0 : ℕ)]
    with N hfirst_N hnear_N hlarge_N hw hN p m hpm E hEi hEn x y s k a hki hkn hkE hx hx0 hy hy0
      hGy hs hzi hsi hcoord
  let β := fun j => restrictedWeight P N (k j) (τ N) (a j)
  let Q : ℝ := 108000 * N * Real.exp (w * N)
  have hweight (j : Fin m) :
      |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| *
        (CatalanMeasure.binomBeta p m (k j) : ℝ) ≤ Q := by
    rw [hcoord j]
    exact hw p m hpm (k j) (hkn j) (a j)
  have hbase := original_poly_atoms_mixedDouble_binom_mul_weight_le hP hN hpm
    E hEi hEn x y s β k hki hkn hkE hx hx0 hy hy0 hs hweight
  have hxi : Function.Injective x := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (hzi (by simpa using hij))
  have hai : Function.Injective a := by
    intro i j hij
    have h1 := hcoord i
    have h2 := hcoord j
    rw [hij] at h1
    have h3 : realCoordinateInv (y i) = realCoordinateInv (y j) := h1.trans h2.symm
    have hyij : y i = y j := by
      rw [← realCoordinate_left_inverse (hy i), h3, realCoordinate_left_inverse (hy j)]
    exact Fin.natAdd_injective _ _ (hzi (by simpa using hyij))
  have hNdy : Nd N m y := hNd N m y a hai hcoord
  have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  have hH : 0 ≤ sheetPrefactor P N := by unfold sheetPrefactor; positivity
  have hF : (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) ≤ sheetPrefactor P N := by
    unfold sheetPrefactor
    exact le_add_of_nonneg_right (by positivity)
  have hI : (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N ≤ sheetPrefactor P N := by
    unfold sheetPrefactor
    exact le_add_of_nonneg_left (by positivity)
  have hNm : (0 : ℝ) ≤ N * m := by positivity
  have hp : markedSheetFree P N hpm x y s ≤
      (5 : ℝ) ^ m * sheetPrefactor P N *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + r * N * m) := by
    by_cases hcase : -1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)
    · have hh := hfirst_N p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
      apply hh.trans
      apply mul_le_mul
      · exact hF.trans (le_mul_of_one_le_left hH h5)
      · apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right hc₁ hNm]
      · exact (Real.exp_pos _).le
      · positivity
    · have hcase' := le_of_not_gt hcase
      by_cases hmm : (m : ℝ) ≤ α₁ * (P.n N : ℝ)
      · have hh := hnear_N p m hpm x y s hmm hx hx0 hy hy0 hGy hNdy hs hzi hsi hcase'
        apply hh.trans
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hI (pow_nonneg (by norm_num) _)
        · apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_right hc₂ hNm]
        · exact (Real.exp_pos _).le
        · positivity
      · have hh := hlarge_N p m hpm x y s (le_of_not_ge hmm) hx hx0 hy hy0 hGy hs hzi hsi hcase'
        apply hh.trans
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hI (pow_nonneg (by norm_num) _)
        · apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_right hc₃ hNm]
        · exact (Real.exp_pos _).le
        · positivity
  have hQ : 0 ≤ Q ^ m := by dsimp [Q]; positivity
  have hc : (5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m = (540000 * (N : ℝ)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
      (-target + Real.log 2 / 2 + ε) + r * N * m) *
      Real.exp (w * (N : ℝ)) ^ m =
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
        (-target + Real.log 2 / 2 + ε) + (r + w) * N * m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ markedSheetFree P N hpm x y s * Q ^ m := hbase
    _ ≤ ((5 : ℝ) ^ m * sheetPrefactor P N *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m)) * Q ^ m := mul_le_mul_of_nonneg_right hp hQ
    _ = sheetPrefactor P N * ((5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m) *
        (Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m) * Real.exp (w * (N : ℝ)) ^ m) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, he]

/-- Generic `weighted_atom_det_on`: the atom determinants are bounded by the weighted atom point. -/
theorem weighted_atom_det (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPoint P τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : Fin (P.n N) → Option (Fin ((P.n0 - P.g0) * N)),
      (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) *
        |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
      atomBaseBoundAt P target N ε * ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N) := by
  filter_upwards [hpoint ε hε,
    eventually_gt_atTop (0 : ℕ)] with N hbound hN f
  classical
  let Pr : Fin (P.n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // Pr k} + Fintype.card {k // ¬ Pr k} = P.n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le Pr
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // Pr k} with hp
  set m := Fintype.card {k // ¬ Pr k} with hm
  let e : Fin (p+m) ≃ Fin (P.n N) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin {k // Pr k}).symm
      (Fintype.equivFin {k // ¬ Pr k}).symm)).trans (Equiv.sumCompl Pr)
  have he1 : ∀ i : Fin p, f (e (Fin.castAdd m i)) = none := by
    intro i
    have h : e (Fin.castAdd m i) = ((Fintype.equivFin {k // Pr k}).symm i).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // Pr k}).symm i).property
  have he2 : ∀ j : Fin m, f (e (Fin.natAdd p j)) ≠ none := by
    intro j
    have h : e (Fin.natAdd p j) = ((Fintype.equivFin {k // ¬ Pr k}).symm j).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // ¬ Pr k}).symm j).property
  let E : Fin p → ℕ := fun i => (e (Fin.castAdd m i)).val
  have hE : Function.Injective E := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (e.injective (Fin.ext hij))
  have hEn : ∀ i, E i < P.n N := fun i => (e (Fin.castAdd m i)).isLt
  let av : Fin m → Fin ((P.n0 - P.g0) * N) := fun j =>
    Classical.choose (Option.ne_none_iff_exists'.mp (he2 j))
  have hav (j : Fin m) : f (e (Fin.natAdd p j)) = some (av j) :=
    Classical.choose_spec (Option.ne_none_iff_exists'.mp (he2 j))
  have hR : 0 ≤ atomBaseBoundAt P target N ε *
      ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N) := by
    apply mul_nonneg
    · unfold atomBaseBoundAt sheetPrefactor
      positivity
    · apply prod_nonneg
      intro k _
      cases f k <;> dsimp [atomColumnCost] <;> positivity
  by_cases hai : Function.Injective av
  swap
  · have hex : ∃ i j, av i = av j ∧ i ≠ j := by
      by_contra hh
      apply hai
      intro i j hij
      by_contra hne
      exact hh ⟨i, j, hij, hne⟩
    obtain ⟨i, j, hij, hne⟩ := hex
    have hcol : e (Fin.natAdd p i) ≠ e (Fin.natAdd p j) := by
      intro h
      exact hne (Fin.natAdd_injective _ _ (e.injective h))
    have hd : (CatalanMeasure.atomMatrix (realBaseMatrix P N)
        (nodeAtomVectors P τ N) f).det = 0 := by
      apply Matrix.det_zero_of_column_eq hcol
      intro r
      simp only [CatalanMeasure.atomMatrix, Matrix.of_apply, hav, Option.elim, hij]
    rw [hd, abs_zero, mul_zero]
    exact hR
  let kv : Fin m → ℕ := fun j => (e (Fin.natAdd p j)).val
  let yv : Fin m → ℝ := fun j => realCoordinate (τ N (av j))
  have hyv : ∀ j, yv j ∈ Ioo (-1 : ℝ) 1 :=
    fun j => realCoordinate_mem (hτmem N (av j))
  have hcoord (j : Fin m) : realCoordinateInv (yv j) =
      τ N (av j) :=
    realCoordinate_right_inverse (hτmem N (av j))
  have hyv0 : ∀ j, yv j ≠ 0 := by
    intro j hj
    have hz := hcoord j
    rw [hj] at hz
    exact hτzero N (av j)
      (by simpa [realCoordinateInv] using hz.symm)
  have hyi : Function.Injective yv := by
    intro i j hij
    apply hai
    apply hτinj N
    rw [← hcoord i, ← hcoord j, hij]
  have hmat : (CatalanMeasure.atomMatrix (realBaseMatrix P N)
      (nodeAtomVectors P τ N) f).submatrix (finCongr hpm) e =
      CatalanMeasure.mixedMatrixWithAtoms realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1))
        (paramPinRowFun P N) (originalPolyAtoms P N yv)
        (paramPinColFun P N E) paramPinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_left, realBaseMatrix]
      rw [realEntry_eq_realPlace_product P]
      congr 1
      funext z
      simp only [paramPinRowFun, paramPinColFun, paramPinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, hav j,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_right,
        nodeAtomVectors, originalPolyAtoms, finCongr_apply, Fin.val_cast]
      rw [hcoord j]
  have hint : ∀ (r : Fin (p+m)) (i : Fin p), Integrable
      (fun z : ℝ × ℝ => paramPinRowFun P N r z.1 *
        (paramPinColFun P N E i z.2 * paramPinKernel z.1 z.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow P N r.val (filteredColumn P N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [paramPinRowFun, paramPinColFun, paramPinKernel]
    ring
  let W : ℝ := ∏ j, |restrictedWeight P N (kv j) (τ N) (av j)|
  let Bd : ℝ := sheetPrefactor P N * (540000*(N : ℝ))^m *
    Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)+ρ*N*m)
  have hW : 0 ≤ W := prod_nonneg (fun j _ => abs_nonneg _)
  have hae : ∀ᵐ w ∂CatalanMeasure.pairMeasure realPlaceMeasure
      (volume.restrict (Ioo (0 : ℝ) 1)) p,
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N)
        (originalPolyAtoms P N yv) (paramPinColFun P N E) paramPinKernel w.1 w.2| * W ≤ Bd := by
    filter_upwards [ae_marked_atom_geometry p yv hyi] with w hw
    rcases hw with ⟨ht, ht0, hx, hx0, hs, hzi, hsi⟩
    let x : Fin p → ℝ := realCoordinate ∘ w.1
    have htx : w.1 = realCoordinateInv ∘ x := by
      funext i
      exact (realCoordinate_right_inverse (ht i)).symm
    rw [htx]
    exact hbound p m hpm E hE hEn x yv w.2 kv av
      hx hx0 hyv hyv0 (fun j => hτG N (av j)) hs hzi hsi hcoord
  have hdet := CatalanMeasure.abs_det_mixedMatrixWithAtoms_mul_weight_le
    realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1)) (paramPinRowFun P N)
    (originalPolyAtoms P N yv) (paramPinColFun P N E) paramPinKernel hW hint hae
  rw [← hmat, abs_det_submatrix_equiv, pairMeasure_real_univ] at hdet
  have hprodW : (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) = W := by
    rw [← e.prod_comp, Fin.prod_univ_add]
    simp only [he1, Option.elim, prod_const_one, one_mul]
    apply prod_congr rfl
    intro j _
    simp only [hav, Option.elim, nodeAtomWeights, W, kv]
  rw [hprodW]
  let c := atomColumnCost ρ N
  have hprod : (∏ k, (f k).elim 1 (fun _ => c)) = c^m := by
    have hh : ∀ k, (f k).elim 1 (fun _ => c) = if Pr k then 1 else c := by
      intro k
      simp only [Pr]
      rcases f k with _ | a <;> simp
    simp_rw [hh]
    rw [prod_ite, prod_const_one, one_mul, prod_const, hm, Fintype.card_subtype]
  rw [hprod]
  have h2p : (2 : ℝ)^p ≤ (2 : ℝ)^(P.n N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hBd : 0 ≤ Bd := by unfold Bd sheetPrefactor; positivity
  calc
    W * |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
        Bd * 2^p := by simpa only [mul_comm] using hdet
    _ ≤ Bd * 2^(P.n N) := mul_le_mul_of_nonneg_left h2p hBd
    _ = _ := by
      unfold Bd atomBaseBoundAt c atomColumnCost
      have he (a b : ℝ) : Real.exp (a+b*(m : ℝ)) = Real.exp a * (Real.exp b)^m := by
        rw [Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [mul_pow]
      ring


/-- `weighted_atom_det` from the binomial weighted atom point (S1): the free columns `kv` are
injective, below `n`, and disjoint from the selected columns `E`. -/
theorem weighted_atom_det_binom (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointBinom P τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : Fin (P.n N) → Option (Fin ((P.n0 - P.g0) * N)),
      (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) *
        |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
      atomBaseBoundAt P target N ε * ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N) := by
  filter_upwards [hpoint ε hε,
    eventually_gt_atTop (0 : ℕ)] with N hbound hN f
  classical
  let Pr : Fin (P.n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // Pr k} + Fintype.card {k // ¬ Pr k} = P.n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le Pr
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // Pr k} with hp
  set m := Fintype.card {k // ¬ Pr k} with hm
  let e : Fin (p+m) ≃ Fin (P.n N) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin {k // Pr k}).symm
      (Fintype.equivFin {k // ¬ Pr k}).symm)).trans (Equiv.sumCompl Pr)
  have he1 : ∀ i : Fin p, f (e (Fin.castAdd m i)) = none := by
    intro i
    have h : e (Fin.castAdd m i) = ((Fintype.equivFin {k // Pr k}).symm i).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // Pr k}).symm i).property
  have he2 : ∀ j : Fin m, f (e (Fin.natAdd p j)) ≠ none := by
    intro j
    have h : e (Fin.natAdd p j) = ((Fintype.equivFin {k // ¬ Pr k}).symm j).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // ¬ Pr k}).symm j).property
  let E : Fin p → ℕ := fun i => (e (Fin.castAdd m i)).val
  have hE : Function.Injective E := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (e.injective (Fin.ext hij))
  have hEn : ∀ i, E i < P.n N := fun i => (e (Fin.castAdd m i)).isLt
  let av : Fin m → Fin ((P.n0 - P.g0) * N) := fun j =>
    Classical.choose (Option.ne_none_iff_exists'.mp (he2 j))
  have hav (j : Fin m) : f (e (Fin.natAdd p j)) = some (av j) :=
    Classical.choose_spec (Option.ne_none_iff_exists'.mp (he2 j))
  have hR : 0 ≤ atomBaseBoundAt P target N ε *
      ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N) := by
    apply mul_nonneg
    · unfold atomBaseBoundAt sheetPrefactor
      positivity
    · apply prod_nonneg
      intro k _
      cases f k <;> dsimp [atomColumnCost] <;> positivity
  by_cases hai : Function.Injective av
  swap
  · have hex : ∃ i j, av i = av j ∧ i ≠ j := by
      by_contra hh
      apply hai
      intro i j hij
      by_contra hne
      exact hh ⟨i, j, hij, hne⟩
    obtain ⟨i, j, hij, hne⟩ := hex
    have hcol : e (Fin.natAdd p i) ≠ e (Fin.natAdd p j) := by
      intro h
      exact hne (Fin.natAdd_injective _ _ (e.injective h))
    have hd : (CatalanMeasure.atomMatrix (realBaseMatrix P N)
        (nodeAtomVectors P τ N) f).det = 0 := by
      apply Matrix.det_zero_of_column_eq hcol
      intro r
      simp only [CatalanMeasure.atomMatrix, Matrix.of_apply, hav, Option.elim, hij]
    rw [hd, abs_zero, mul_zero]
    exact hR
  let kv : Fin m → ℕ := fun j => (e (Fin.natAdd p j)).val
  let yv : Fin m → ℝ := fun j => realCoordinate (τ N (av j))
  have hyv : ∀ j, yv j ∈ Ioo (-1 : ℝ) 1 :=
    fun j => realCoordinate_mem (hτmem N (av j))
  have hcoord (j : Fin m) : realCoordinateInv (yv j) =
      τ N (av j) :=
    realCoordinate_right_inverse (hτmem N (av j))
  have hyv0 : ∀ j, yv j ≠ 0 := by
    intro j hj
    have hz := hcoord j
    rw [hj] at hz
    exact hτzero N (av j)
      (by simpa [realCoordinateInv] using hz.symm)
  have hyi : Function.Injective yv := by
    intro i j hij
    apply hai
    apply hτinj N
    rw [← hcoord i, ← hcoord j, hij]
  have hmat : (CatalanMeasure.atomMatrix (realBaseMatrix P N)
      (nodeAtomVectors P τ N) f).submatrix (finCongr hpm) e =
      CatalanMeasure.mixedMatrixWithAtoms realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1))
        (paramPinRowFun P N) (originalPolyAtoms P N yv)
        (paramPinColFun P N E) paramPinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_left, realBaseMatrix]
      rw [realEntry_eq_realPlace_product P]
      congr 1
      funext z
      simp only [paramPinRowFun, paramPinColFun, paramPinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, hav j,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_right,
        nodeAtomVectors, originalPolyAtoms, finCongr_apply, Fin.val_cast]
      rw [hcoord j]
  have hint : ∀ (r : Fin (p+m)) (i : Fin p), Integrable
      (fun z : ℝ × ℝ => paramPinRowFun P N r z.1 *
        (paramPinColFun P N E i z.2 * paramPinKernel z.1 z.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow P N r.val (filteredColumn P N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [paramPinRowFun, paramPinColFun, paramPinKernel]
    ring
  let W : ℝ := ∏ j, |restrictedWeight P N (kv j) (τ N) (av j)|
  let Bd : ℝ := sheetPrefactor P N * (540000*(N : ℝ))^m *
    Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)+ρ*N*m)
  have hW : 0 ≤ W := prod_nonneg (fun j _ => abs_nonneg _)
  have hae : ∀ᵐ w ∂CatalanMeasure.pairMeasure realPlaceMeasure
      (volume.restrict (Ioo (0 : ℝ) 1)) p,
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N)
        (originalPolyAtoms P N yv) (paramPinColFun P N E) paramPinKernel w.1 w.2| * W ≤ Bd := by
    filter_upwards [ae_marked_atom_geometry p yv hyi] with w hw
    rcases hw with ⟨ht, ht0, hx, hx0, hs, hzi, hsi⟩
    let x : Fin p → ℝ := realCoordinate ∘ w.1
    have htx : w.1 = realCoordinateInv ∘ x := by
      funext i
      exact (realCoordinate_right_inverse (ht i)).symm
    rw [htx]
    have hkv : Function.Injective kv := by
      intro i j hij
      exact Fin.natAdd_injective _ _ (e.injective (Fin.ext hij))
    have hkE : ∀ j i, kv j ≠ E i := by
      intro j i h
      have := e.injective (Fin.ext h)
      have h2 := congrArg Fin.val this
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h2
      have := i.isLt
      omega
    exact hbound p m hpm E hE hEn x yv w.2 kv av hkv (fun j => (e (Fin.natAdd p j)).isLt) hkE
      hx hx0 hyv hyv0 (fun j => hτG N (av j)) hs hzi hsi hcoord
  have hdet := CatalanMeasure.abs_det_mixedMatrixWithAtoms_mul_weight_le
    realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1)) (paramPinRowFun P N)
    (originalPolyAtoms P N yv) (paramPinColFun P N E) paramPinKernel hW hint hae
  rw [← hmat, abs_det_submatrix_equiv, pairMeasure_real_univ] at hdet
  have hprodW : (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) = W := by
    rw [← e.prod_comp, Fin.prod_univ_add]
    simp only [he1, Option.elim, prod_const_one, one_mul]
    apply prod_congr rfl
    intro j _
    simp only [hav, Option.elim, nodeAtomWeights, W, kv]
  rw [hprodW]
  let c := atomColumnCost ρ N
  have hprod : (∏ k, (f k).elim 1 (fun _ => c)) = c^m := by
    have hh : ∀ k, (f k).elim 1 (fun _ => c) = if Pr k then 1 else c := by
      intro k
      simp only [Pr]
      rcases f k with _ | a <;> simp
    simp_rw [hh]
    rw [prod_ite, prod_const_one, one_mul, prod_const, hm, Fintype.card_subtype]
  rw [hprod]
  have h2p : (2 : ℝ)^p ≤ (2 : ℝ)^(P.n N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hBd : 0 ≤ Bd := by unfold Bd sheetPrefactor; positivity
  calc
    W * |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
        Bd * 2^p := by simpa only [mul_comm] using hdet
    _ ≤ Bd * 2^(P.n N) := mul_le_mul_of_nonneg_left h2p hBd
    _ = _ := by
      unfold Bd atomBaseBoundAt c atomColumnCost
      have he (a b : ℝ) : Real.exp (a+b*(m : ℝ)) = Real.exp a * (Real.exp b)^m := by
        rw [Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [mul_pow]
      ring


end

end Analytic
end CatalanMeasure.GenD

#print axioms CatalanMeasure.GenD.Analytic.weighted_atom_point_of_sheet_binom

#print axioms CatalanMeasure.GenD.Analytic.binom_hweights_of_column_bound

#print axioms CatalanMeasure.GenD.Analytic.binomBeta_le_mul_exp

#print axioms CatalanMeasure.GenD.Analytic.eventually_mul_pow_le_exp

#print axioms CatalanMeasure.GenD.Analytic.weighted_atom_det_binom
#print axioms CatalanMeasure.GenD.Analytic.weighted_atom_point_binom_of_signed
