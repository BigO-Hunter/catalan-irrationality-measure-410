module

public import Submission.CatalanMeasure.Main
public import Submission.CatalanMeasure.Quadrature
public import Submission.CatalanMeasure.DetExpansion
public import Submission.CatalanMeasure.PinMajorant
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Submission.CatalanMeasure.ChebyshevNodes
public import Submission.CatalanMeasure.DualTwo
public import Submission.CatalanMeasure.QuadCircle

@[expose] public section

/-!
# Lemma 6: the perturbation estimate, unconditionally

On the disk `|x - G| ≤ exp(-ρ N)` with `ρ = 404.25`,

  `|Δ_N(x) - Δ_N(G)| ≤ exp(n² (-2.290939875 + (log 2)/2 + ε))`  for `N ≥ N₀(ε)`.

Assembly:
* `Quadrature.lean`: `L = Φ(τ) β` with the `J = H N` Chebyshev nodes `τ_a = (x_a - 1)/2` of
  `ChebyshevNodes.lean` and `|β| ≤ 8 J² K^N`, `K = 95 · 10^46` (`QuadCircle.lean`);
* `DetExpansion.lean`: `|det (A + δ Φ β) - det A| ≤ M ((1 + J |δ| B c)^n - 1)` once every
  mixed determinant satisfies `|det M_f| ≤ M c^#(atom columns)`;
* `MixedAndreief.lean` and `PinMajorant.lean`: each mixed determinant is a mixed Andreief
  integral, bounded pointwise by the `p`-node energy majorants;
* `PinSupDual.lean`: OpenAI's certified dual constants bound the `p`-node energies, with a cost
  `n · coef` per atom column.
-/

open Finset Set Filter Polynomial
open scoped BigOperators Nat

namespace OAI.InternalCatalan

/-! ### The quadrature nodes and the size of the weights -/

/-- The quadrature nodes: the roots of `T_J`, moved to `[-1, 0]`. -/
noncomputable def quadNode (J : ℕ) (a : Fin J) : ℝ := CatalanMeasure.chebNode J a

theorem quadNode_mem (J : ℕ) (a : Fin J) : quadNode J a ∈ Ioo (-1 : ℝ) 0 :=
  CatalanMeasure.chebNode_mem a

theorem quadNode_injective (J : ℕ) : Function.Injective (quadNode J) :=
  CatalanMeasure.chebNode_injective J

/-- **Size of the quadrature weights.** -/
theorem quadWeight_quadNode_le (N : ℕ) (a : Fin (H N)) (k : ℕ) :
    |quadWeight N (quadNode (H N)) a k| ≤ (2 : ℝ) ^ (q N + 2) * (3 + 2 * √2) ^ H N :=
  (quadWeight_abs_le (le_refl (H N)) (quadNode (H N)) (fun c => (quadNode_mem _ c).2.le) a k).trans
    (mul_le_mul_of_nonneg_left (CatalanMeasure.chebNode_ratio_le a) (by positivity))

/-- `(3 + 2√2)^65 ≤ 2 e^114`. -/
theorem chebBase_pow_le : (3 + 2 * √2 : ℝ) ^ 65 ≤ 2 * Real.exp 114 := by
  have hs : √2 < 1.415 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hz : (3 + 2 * √2 : ℝ) ≤ 5.83 := by linarith
  have he : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexp : Real.exp 114 = Real.exp 1 ^ 114 := by
    rw [← Real.exp_nat_mul]; norm_num
  calc (3 + 2 * √2 : ℝ) ^ 65 ≤ (5.83 : ℝ) ^ 65 :=
        pow_le_pow_left₀ (by positivity) hz 65
    _ ≤ 2 * (2.718 : ℝ) ^ 114 := by norm_num
    _ ≤ 2 * Real.exp 114 := by
        rw [hexp]
        gcongr

/-! ### OpenAI's certified dual constants with explicit one-point bounds -/

noncomputable def caseOneBx : ℝ := -13244 / 10000 + 24 / 1000000
noncomputable def caseOneBs : ℝ := -14280 / 10000 + 24 / 1000000
noncomputable def caseTwoBx : ℝ := dualBx
noncomputable def caseTwoBs : ℝ := dualBs

theorem caseOne_row_bound : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 →
    realEnergyRowTrialField 1 barrierLambda1 barrierP1 barrierV1 z ≤ caseOneBx := by
  intro z hz hz0
  simpa [realEnergyRowTrialField, barrierCase1X, caseOneBx] using
    barrierCase1X_global_upper ⟨hz.1, hz.2, hz0⟩

theorem caseOne_col_bound : ∀ z ∈ Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField barrierV1 z ≤ caseOneBs := by
  intro z hz
  simpa only [realEnergyColumnTrialField, barrierCase1Y, caseOneBs] using
    barrierCase1Y_global_upper hz

theorem caseTwo_row_bound : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 →
    realEnergyRowTrialField 2 0 dualP2 dualV2 z ≤ caseTwoBx := dual_row_bound

theorem caseTwo_col_bound : ∀ z ∈ Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField dualV2 z ≤ caseTwoBs := dual_col_bound

theorem caseOne_dual_lt :
    realEnergyDualConstant 1 barrierP1 barrierV1 caseOneBx caseOneBs <
      -(229180925 / 100000000 : ℝ) := by
  unfold realEnergyDualConstant caseOneBx caseOneBs
  nlinarith [barrier_case1_norm_coarse_upper, barrier_one_coarse_total_sharp_lt]

theorem caseTwo_dual_lt :
    realEnergyDualConstant 2 dualP2 dualV2 caseTwoBx caseTwoBs <
      -(229180925 / 100000000 : ℝ) := dual_dual_lt

/-- The cost of one atom column in the energy. -/
noncomputable def lemma6Coef : ℝ :=
  max (pinMissingCoefficient 1 barrierLambda1 caseOneBx caseOneBs)
    (pinMissingCoefficient 2 0 caseTwoBx caseTwoBs)

theorem lemma6Coef_lt : lemma6Coef < 53678 / 10000 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lemma6Coef pinMissingCoefficient caseOneBx caseOneBs caseTwoBx caseTwoBs dualBx dualBs
  rw [barrierLambda1]
  apply max_lt
  · rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)]
    norm_num at hl ⊢
    linarith
  · rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)]
    norm_num at hl ⊢
    linarith

theorem lemma6Coef_nonneg : 0 ≤ lemma6Coef := by
  unfold lemma6Coef pinMissingCoefficient
  apply le_trans _ (le_max_right _ _)
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-! ### The pointwise bound for every configuration -/

theorem realRowAmplitude_zero {N : ℕ} (hN : 0 < N) {r : ℕ} (hr : r < n N) :
    realRowAmplitude N r 0 = 0 := by
  rw [realRowAmplitude_of_nonpos N r le_rfl, ← Polynomial.coeff_zero_eq_eval_zero,
    realPoly_coeff, rowP_coeff_eq_zero_of_lt hN hr (by unfold A; omega)]
  simp

theorem rowDet_eq_zero_of_zero {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (τ' : Fin m → ℝ) (t : Fin p → ℝ) {i : Fin p} (hti : t i = 0) :
    CatalanMeasure.rowDet (pinRowFun N) τ' t = 0 := by
  unfold CatalanMeasure.rowDet
  apply Matrix.det_eq_zero_of_column_eq_zero (Fin.castAdd m i)
  intro r
  simp only [Matrix.of_apply, pinRowFun, Fin.append_left, hti]
  exact realRowAmplitude_zero hN (by have := r.isLt; omega)

theorem rowDet_eq_zero_of_not_injective {N : ℕ} {p m : ℕ} (τ' : Fin m → ℝ) (t : Fin p → ℝ)
    (h : ¬ Function.Injective (Fin.append t τ')) :
    CatalanMeasure.rowDet (pinRowFun N) τ' t = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨c, c', hcc, hne⟩ := h
  unfold CatalanMeasure.rowDet
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply, hcc]

theorem mixedDouble_eq_zero_of_rowDet {p m : ℕ} {F : Fin (p + m) → ℝ → ℝ} {τ' : Fin m → ℝ}
    {G : Fin p → ℝ → ℝ} {K : ℝ → ℝ → ℝ} {t s : Fin p → ℝ}
    (h : CatalanMeasure.rowDet F τ' t = 0) : CatalanMeasure.mixedDouble F τ' G K t s = 0 := by
  unfold CatalanMeasure.mixedDouble
  rw [h, zero_mul, zero_mul]

theorem mixedDouble_eq_zero_of_s {p m : ℕ} {F : Fin (p + m) → ℝ → ℝ} {τ' : Fin m → ℝ}
    {G : Fin p → ℝ → ℝ} {K : ℝ → ℝ → ℝ} {t s : Fin p → ℝ} (h : ¬ Function.Injective s) :
    CatalanMeasure.mixedDouble F τ' G K t s = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨j, j', hjj, hne⟩ := h
  unfold CatalanMeasure.mixedDouble
  have : (Matrix.of fun i j : Fin p => K (t i) (s j)).det = 0 := by
    apply Matrix.det_zero_of_column_eq hne
    intro r
    simp only [Matrix.of_apply, hjj]
  rw [this, mul_zero, zero_mul]

/-- **Uniform pointwise bound** for the mixed integrands, for all `p` and all configurations. -/
theorem mixedDouble_uniform_bound {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p m : ℕ) (hpm : p + m = n N)
      (E : Fin p → ℕ), Function.Injective E → (∀ i, E i < n N) →
      ∀ y : Fin m → ℝ, (∀ j, y j ∈ Ioo (-1 : ℝ) 0) →
      ∀ t s : Fin p → ℝ, (∀ i, t i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E)
          pinKernel t s| ≤
        realDeterminantSheetPrefactor N * (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2)) *
          Real.exp ((n N : ℝ) * m * lemma6Coef) := by
  obtain ⟨N₁, h₁⟩ := pin_uniform_dual_eventually (k := 1) (lam := barrierLambda1) (Or.inl rfl)
    barrier_lambdas.2.1 barrierP1 barrierV1 barrier_trials_abs_summable.2.2.1
    barrier_trials_abs_summable.2.2.2 caseOne_row_bound caseOne_col_bound hd
  obtain ⟨N₂, h₂⟩ := pin_uniform_dual_eventually (k := 2) (lam := 0) (Or.inr rfl)
    le_rfl dualP2 dualV2 dualP2_summable dualV2_summable caseTwo_row_bound caseTwo_col_bound hd
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro N hN p m hpm E hE hEn y hy t s ht hs
  have hN0 : 0 < N := by omega
  have hp : p ≤ n N := by omega
  have hn : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by unfold n; omega)
  have hmR : (m : ℝ) = (n N : ℝ) - p := by
    rw [← hpm]
    push_cast
    ring
  set RHS := realDeterminantSheetPrefactor N * (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
      Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2)) *
      Real.exp ((n N : ℝ) * m * lemma6Coef) with hRHS
  have hRHS0 : 0 ≤ RHS := by
    have := realDeterminantSheetPrefactor_nonneg N
    positivity
  -- degenerate configurations
  by_cases hzero : ∃ i, t i = 0
  · obtain ⟨i, hti⟩ := hzero
    rw [mixedDouble_eq_zero_of_rowDet (rowDet_eq_zero_of_zero hN0 hpm _ t hti), abs_zero]
    exact hRHS0
  push Not at hzero
  by_cases hsi : Function.Injective s
  swap
  · rw [mixedDouble_eq_zero_of_s hsi, abs_zero]
    exact hRHS0
  -- coordinates
  obtain ⟨x, rfl, hx, hx0⟩ : ∃ x : Fin p → ℝ, t = realCoordinateInv ∘ x ∧
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) ∧ (∀ i, x i ≠ 0) := by
    refine ⟨realCoordinate ∘ t, ?_, fun i => realCoordinate_mem (ht i), fun i => ?_⟩
    · funext i
      exact (realCoordinate_right_inverse (ht i)).symm
    · intro h0
      apply hzero i
      rw [← realCoordinate_right_inverse (ht i)]
      simp only [Function.comp_apply] at h0
      rw [h0]
      simp [realCoordinateInv]
  by_cases hzi : Function.Injective (Fin.append x y)
  swap
  · have hni : ¬ Function.Injective (Fin.append (realCoordinateInv ∘ x) (realCoordinateInv ∘ y)) := by
      rw [fin_append_comp]
      exact fun hinj => hzi (hinj.of_comp)
    rw [mixedDouble_eq_zero_of_rowDet (rowDet_eq_zero_of_not_injective _ _ hni), abs_zero]
    exact hRHS0
  have hxi : Function.Injective x := by
    intro i i' hii
    have := hzi (a₁ := Fin.castAdd m i) (a₂ := Fin.castAdd m i') (by simpa using hii)
    exact Fin.castAdd_injective _ _ this
  have hcoef1 : pinMissingCoefficient 1 barrierLambda1 caseOneBx caseOneBs ≤ lemma6Coef :=
    le_max_left _ _
  have hcoef2 : pinMissingCoefficient 2 0 caseTwoBx caseTwoBs ≤ lemma6Coef := le_max_right _ _
  have hfinal : ∀ (K V : ℝ), 0 ≤ K → K ≤ realDeterminantSheetPrefactor N →
      V ≤ -(229180925 / 100000000 : ℝ) + d + ((n N : ℝ) - p) / (n N : ℝ) * lemma6Coef →
      K * (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (V + Real.log 2 / 2)) ≤ RHS := by
    intro K V hK0 hK hV
    rw [hRHS, mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
    have hexp : Real.exp ((n N : ℝ) ^ 2 * (V + Real.log 2 / 2)) ≤
        Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2) +
          (n N : ℝ) * m * lemma6Coef) := by
      apply Real.exp_le_exp.mpr
      have h2 : (n N : ℝ) ^ 2 * (((n N : ℝ) - p) / (n N : ℝ) * lemma6Coef) =
          (n N : ℝ) * m * lemma6Coef := by
        rw [hmR]
        field_simp
      nlinarith [sq_nonneg (n N : ℝ)]
    calc K * (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (V + Real.log 2 / 2))
        ≤ realDeterminantSheetPrefactor N * (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2) +
            (n N : ℝ) * m * lemma6Coef) := by
          have hsp := realDeterminantSheetPrefactor_nonneg N
          gcongr
      _ = _ := by ring
  have hpn : 0 ≤ ((n N : ℝ) - p) / (n N : ℝ) := div_nonneg (by rw [← hmR]; positivity) hn.le
  by_cases hcase : (∑ c : Fin (n N), (1 - (Fin.append x y (Fin.cast hpm.symm c)) ^ 2) /
      (1 + (Fin.append x y (Fin.cast hpm.symm c)) ^ 2)) ≤ ((n N - 1 - 2 * g N : ℕ) : ℝ)
  · have hb := abs_mixedDouble_le_caseTwo hN0 hpm E hE hEn x y s hx hx0 hy hs hxi hsi hzi hcase
    have hdual := h₂ N (by omega) p hp x s hx hs hx0 hxi hsi (Or.inl rfl)
    refine hb.trans (hfinal _ _ (by positivity) (le_max_left _ _) ?_)
    have := mul_le_mul_of_nonneg_left hcoef2 hpn
    linarith [caseTwo_dual_lt]
  · have hb := abs_mixedDouble_le_caseOne hN0 hpm E hE hEn x y s hx hx0 hy hs hxi hsi
    have hsplit : (∑ c : Fin (n N), (1 - (Fin.append x y (Fin.cast hpm.symm c)) ^ 2) /
        (1 + (Fin.append x y (Fin.cast hpm.symm c)) ^ 2)) =
        (∑ i, (1 - x i ^ 2) / (1 + x i ^ 2)) + ∑ j, (1 - y j ^ 2) / (1 + y j ^ 2) := by
      rw [sum_fin_cast hpm (fun c => (1 - (Fin.append x y c) ^ 2) / (1 + (Fin.append x y c) ^ 2)),
        Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    have hyw : ∑ j, (1 - y j ^ 2) / (1 + y j ^ 2) ≤ (m : ℝ) := by
      calc ∑ j, (1 - y j ^ 2) / (1 + y j ^ 2) ≤ ∑ _j : Fin m, (1 : ℝ) := by
            apply sum_le_sum
            intro j _
            rw [div_le_one (by positivity)]
            nlinarith [sq_nonneg (y j)]
        _ = m := by simp
    have hcond : ((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
        ∑ i, (1 - x i ^ 2) / (1 + x i ^ 2) := by
      push Not at hcase
      rw [hsplit] at hcase
      rw [← hmR]
      linarith
    have hdual := h₁ N (by omega) p hp x s hx hs hx0 hxi hsi (Or.inr hcond)
    refine hb.trans (hfinal _ _ (by positivity) (le_max_right _ _) ?_)
    have := mul_le_mul_of_nonneg_left hcoef1 hpn
    linarith [caseOne_dual_lt]

/-! ### Every mixed determinant -/

/-- OpenAI's determinant matrix `A_G`. -/
noncomputable def baseMatrix (N : ℕ) : Matrix (Fin (n N)) (Fin (n N)) ℝ :=
  Matrix.of fun r k => determinantEntry N r.val k.val

/-- The atom vectors `Φ(r, a) = φ_r(τ_a)`. -/
noncomputable def atomVectors (N : ℕ) : Fin (n N) → Fin (H N) → ℝ :=
  fun r a => realRowAmplitude N r.val (quadNode (H N) a)

theorem abs_det_submatrix_equiv {k l : ℕ} (M : Matrix (Fin l) (Fin l) ℝ) (g e : Fin k ≃ Fin l) :
    |(M.submatrix g e).det| = |M.det| := by
  have h : M.submatrix g e = (M.submatrix id (g.symm.trans e)).submatrix g g := by
    ext r c
    simp
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_permute', abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (g.symm.trans e)) with hs | hs <;> simp [hs]

theorem ae_pair_rectangle (p : ℕ) :
    ∀ᵐ w ∂(CatalanMeasure.pairMeasure realPlaceMeasure
        (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) p),
      (∀ i, w.1 i ∈ Ioo (-1 : ℝ) 1) ∧ (∀ j, w.2 j ∈ Ioo (0 : ℝ) 1) := by
  have h1 : ∀ᵐ t ∂MeasureTheory.Measure.pi (fun _ : Fin p => realPlaceMeasure),
      ∀ i, t i ∈ Ioo (-1 : ℝ) 1 :=
    Filter.eventually_all.2 (fun _ =>
      MeasureTheory.Measure.tendsto_eval_ae_ae.eventually ae_realPlace_mem)
  have h2 : ∀ᵐ s ∂MeasureTheory.Measure.pi
      (fun _ : Fin p => MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ j, s j ∈ Ioo (0 : ℝ) 1 :=
    Filter.eventually_all.2 (fun _ => MeasureTheory.Measure.tendsto_eval_ae_ae.eventually
      (MeasureTheory.ae_restrict_mem measurableSet_Ioo))
  unfold CatalanMeasure.pairMeasure
  exact ((MeasureTheory.Measure.quasiMeasurePreserving_fst).tendsto_ae.eventually h1).and
    ((MeasureTheory.Measure.quasiMeasurePreserving_snd).tendsto_ae.eventually h2)

theorem pairMeasure_real_univ (p : ℕ) :
    (CatalanMeasure.pairMeasure realPlaceMeasure
        (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) p).real Set.univ = 2 ^ p := by
  unfold CatalanMeasure.pairMeasure
  rw [MeasureTheory.measureReal_def, ← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
    MeasureTheory.Measure.pi_univ, MeasureTheory.Measure.pi_univ]
  simp [realPlaceMeasure_univ, Real.volume_Ioo]

theorem quadNode_coordinate_mem (J : ℕ) (a : Fin J) :
    realCoordinate (quadNode J a) ∈ Ioo (-1 : ℝ) 0 := by
  have hm := quadNode_mem J a
  have hc := realCoordinate_mem (t := quadNode J a) ⟨hm.1, by linarith [hm.2]⟩
  refine ⟨hc.1, ?_⟩
  unfold realCoordinate
  exact div_neg_of_neg_of_pos hm.2 (by positivity)

/-- **Every mixed determinant** `|det M_f| ≤ M c ^ #(atom columns)`. -/
theorem atomMatrix_det_bound {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : Fin (n N) → Option (Fin (H N)),
      |(CatalanMeasure.atomMatrix (baseMatrix N) (atomVectors N) f).det| ≤
        ((2 : ℝ) ^ n N * realDeterminantSheetPrefactor N *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2))) *
        ∏ k, (f k).elim 1 (fun _ => (2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N) *
          Real.exp ((n N : ℝ) * lemma6Coef)) := by
  obtain ⟨N₀, hN₀⟩ := mixedDouble_uniform_bound hd
  refine ⟨N₀, fun N hN f => ?_⟩
  classical
  let P : Fin (n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // P k} + Fintype.card {k // ¬ P k} = n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le P
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // P k} with hp
  set m := Fintype.card {k // ¬ P k} with hm
  let e : Fin (p + m) ≃ Fin (n N) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin {k // P k}).symm
      (Fintype.equivFin {k // ¬ P k}).symm)).trans (Equiv.sumCompl P)
  have he1 : ∀ i : Fin p, f (e (Fin.castAdd m i)) = none := by
    intro i
    have h : e (Fin.castAdd m i) = ((Fintype.equivFin {k // P k}).symm i).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // P k}).symm i).property
  have he2 : ∀ j : Fin m, f (e (Fin.natAdd p j)) ≠ none := by
    intro j
    have h : e (Fin.natAdd p j) = ((Fintype.equivFin {k // ¬ P k}).symm j).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // ¬ P k}).symm j).property
  let E : Fin p → ℕ := fun i => (e (Fin.castAdd m i)).val
  have hE : Function.Injective E := by
    intro i i' hii
    exact Fin.castAdd_injective _ _ (e.injective (Fin.ext hii))
  have hEn : ∀ i, E i < n N := fun i => (e (Fin.castAdd m i)).isLt
  let yv : Fin m → ℝ := fun j =>
    (f (e (Fin.natAdd p j))).elim (-1 / 2) (fun a => realCoordinate (quadNode (H N) a))
  have hyv : ∀ j, yv j ∈ Ioo (-1 : ℝ) 0 := by
    intro j
    simp only [yv]
    rcases f (e (Fin.natAdd p j)) with _ | a
    · norm_num
    · exact quadNode_coordinate_mem _ a
  have hmat : (CatalanMeasure.atomMatrix (baseMatrix N) (atomVectors N) f).submatrix
      (finCongr hpm) e =
      CatalanMeasure.mixedMatrix realPlaceMeasure (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1))
        (pinRowFun N) (realCoordinateInv ∘ yv) (pinColFun N E) pinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrix, Fin.addCases_left, baseMatrix]
      rw [determinantEntry_eq_realPlace_product]
      congr 1
      funext z
      simp only [pinRowFun, pinColFun, pinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (he2 j)
      have hτ := quadNode_mem (H N) a
      simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, ha,
        Option.elim, CatalanMeasure.mixedMatrix, Fin.addCases_right, atomVectors, pinRowFun,
        Function.comp_apply, yv, finCongr_apply, Fin.val_cast]
      rw [realCoordinate_right_inverse ⟨hτ.1, by linarith [hτ.2]⟩]
  have hint : ∀ (r : Fin (p + m)) (i : Fin p), MeasureTheory.Integrable
      (fun z : ℝ × ℝ => pinRowFun N r z.1 * (pinColFun N E i z.2 * pinKernel z.1 z.2))
      (realPlaceMeasure.prod (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow N r.val (filteredColumn N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [pinRowFun, pinColFun, pinKernel]
    ring
  set Bd := realDeterminantSheetPrefactor N * (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
      Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2)) *
      Real.exp ((n N : ℝ) * m * lemma6Coef) with hBd
  have hae : ∀ᵐ w ∂(CatalanMeasure.pairMeasure realPlaceMeasure
      (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) p),
      |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ yv) (pinColFun N E)
        pinKernel w.1 w.2| ≤ Bd := by
    filter_upwards [ae_pair_rectangle p] with w hw
    exact hN₀ N hN p m hpm E hE hEn yv hyv w.1 w.2 hw.1 hw.2
  have hdet := CatalanMeasure.abs_det_mixedMatrix_le (realCoordinateInv ∘ yv) hint hae
  rw [← hmat, abs_det_submatrix_equiv, pairMeasure_real_univ] at hdet
  -- the product over the columns
  set c : ℝ := (2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N) * Real.exp ((n N : ℝ) * lemma6Coef) with hc
  have hprod : ∏ k, (f k).elim 1 (fun _ => c) = c ^ m := by
    have : ∀ k, (f k).elim 1 (fun _ => c) = if P k then 1 else c := by
      intro k
      simp only [P]
      rcases f k with _ | a <;> simp
    simp_rw [this]
    rw [prod_ite, prod_const_one, one_mul, prod_const, hm, Fintype.card_subtype]
  rw [hprod]
  have hcm : c ^ m = (2 : ℝ) ^ (n N * m) * ((2 : ℝ) ^ (2 * h N)) ^ m *
      Real.exp ((n N : ℝ) * m * lemma6Coef) := by
    rw [hc, mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    congr 2
    ring
  have h2p : (2 : ℝ) ^ p ≤ (2 : ℝ) ^ n N := pow_le_pow_right₀ (by norm_num) (by omega)
  have hBd0 : 0 ≤ Bd := by
    have := realDeterminantSheetPrefactor_nonneg N
    positivity
  calc |(CatalanMeasure.atomMatrix (baseMatrix N) (atomVectors N) f).det| ≤ Bd * 2 ^ p := hdet
    _ ≤ Bd * 2 ^ n N := mul_le_mul_of_nonneg_left h2p hBd0
    _ = _ := by
        rw [hcm, hBd]
        ring

/-! ### Assembly -/

/-- The radius exponent of the perturbation lemma. -/
noncomputable def lemma6Rho : ℝ := 40425 / 100

theorem delta_matrix_eq {N : ℕ} (hN : 0 < N) (x : ℝ) :
    aeval x (deltaPoly N) = (Matrix.of fun r k : Fin (n N) =>
      baseMatrix N r k + (x - catalan) *
        ∑ a, atomVectors N r a * quadWeight N (quadNode (H N)) a k.val).det := by
  rw [aeval_deltaPoly]
  congr 1
  ext r k
  simp only [Matrix.of_apply, baseMatrix, atomVectors]
  rw [← filteredCatalanCoeff_quadrature hN le_rfl (quadNode_injective _)
      (fun a => (quadNode_mem _ a).2.le),
    ← filteredEntry_real_affine hN r.isLt k.isLt]
  ring

/-- `K = 95 · 10^46 ≤ e^110.475`. -/
theorem circleK_le_exp : (CatalanMeasure.circleK : ℝ) ≤ Real.exp 110.475 := by
  have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have ht := Real.sum_le_exp_of_nonneg (x := (0.475 : ℝ)) (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  norm_num at ht
  have hsplit : Real.exp 110.475 = Real.exp 1 ^ 110 * Real.exp 0.475 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [hsplit]
  have hK : (CatalanMeasure.circleK : ℝ) = 95 * 10 ^ 46 := by
    unfold CatalanMeasure.circleK; push_cast; ring
  rw [hK]
  calc (95 * 10 ^ 46 : ℝ) ≤ (2.7182818283 : ℝ) ^ 110 *
        (1 + 0.475 + 0.475 ^ 2 / 2 + 0.475 ^ 3 / 6 + 0.475 ^ 4 / 24 + 0.475 ^ 5 / 120) := by
        norm_num
    _ ≤ Real.exp 1 ^ 110 * Real.exp 0.475 := by
        gcongr
        norm_num
        linarith

/-- The explicit numerical condition defining `ρ = 404.25`. -/
theorem rho_condition {N : ℕ} (hN : 2000 ≤ N) :
    (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2 * (CatalanMeasure.circleK : ℝ) ^ N) *
      ((2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N) * Real.exp ((n N : ℝ) * lemma6Coef)) ≤
      Real.exp (lemma6Rho * N) := by
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_two_lt_d9
  have hc := lemma6Coef_lt
  have hK0 : (0 : ℝ) ≤ (CatalanMeasure.circleK : ℝ) := by
    unfold CatalanMeasure.circleK; norm_num
  have hz : (CatalanMeasure.circleK : ℝ) ^ N ≤ Real.exp (110.475 * N) := by
    calc (CatalanMeasure.circleK : ℝ) ^ N ≤ Real.exp 110.475 ^ N :=
          pow_le_pow_left₀ hK0 circleK_le_exp N
      _ = Real.exp (110.475 * N) := by rw [← Real.exp_nat_mul]; ring_nf
  have hpow : (2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N) = Real.exp ((52 * N : ℕ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ← pow_add]
    congr 1
    unfold n h
    omega
  have hN4 : (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2) ≤
      (8 * 48 * 65 ^ 3 * 10 ^ 8) * Real.exp ((N : ℝ) / 25) := by
    have h100 : (N : ℝ) ≤ 100 * Real.exp ((N : ℝ) / 100) := by
      have := Real.add_one_le_exp ((N : ℝ) / 100 - 1)
      have h2 : Real.exp ((N : ℝ) / 100 - 1) ≤ Real.exp ((N : ℝ) / 100) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hq : (N : ℝ) ^ 4 ≤ 10 ^ 8 * Real.exp ((N : ℝ) / 25) := by
      have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      calc (N : ℝ) ^ 4 ≤ (100 * Real.exp ((N : ℝ) / 100)) ^ 4 := pow_le_pow_left₀ h0 h100 4
        _ = 10 ^ 8 * Real.exp ((N : ℝ) / 25) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num
          ring_nf
    have he : (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2) = (8 * 48 * 65 ^ 3) * (N : ℝ) ^ 4 := by
      simp only [n, H, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [he]
    nlinarith [hq]
  have hbig : (8 * 48 * 65 ^ 3 * 10 ^ 8 : ℝ) ≤ Real.exp 38 := by
    have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : Real.exp 38 = Real.exp 1 ^ 38 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (8 * 48 * 65 ^ 3 * 10 ^ 8 : ℝ) ≤ (2.7 : ℝ) ^ 38 := by norm_num
      _ ≤ Real.exp 1 ^ 38 := pow_le_pow_left₀ (by norm_num) h2 38
  have hcR : (n N : ℝ) * lemma6Coef ≤ 48 * N * (53678 / 10000) := by
    simp only [n, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [lemma6Coef_nonneg]
  calc (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2 * (CatalanMeasure.circleK : ℝ) ^ N) *
        ((2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N) * Real.exp ((n N : ℝ) * lemma6Coef))
      = ((n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2)) * (CatalanMeasure.circleK : ℝ) ^ N *
          ((2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N)) * Real.exp ((n N : ℝ) * lemma6Coef) := by ring
    _ ≤ ((8 * 48 * 65 ^ 3 * 10 ^ 8) * Real.exp ((N : ℝ) / 25)) * Real.exp (110.475 * N) *
          Real.exp ((52 * N : ℕ) * Real.log 2) * Real.exp (48 * N * (53678 / 10000)) := by
        rw [hpow]
        gcongr
    _ ≤ Real.exp 38 * Real.exp ((N : ℝ) / 25) * Real.exp (110.475 * N) *
          Real.exp ((52 * N : ℕ) * Real.log 2) * Real.exp (48 * N * (53678 / 10000)) := by
        gcongr
    _ ≤ Real.exp (lemma6Rho * N) := by
        simp only [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        unfold lemma6Rho
        push_cast
        norm_num at hl
        nlinarith

/-- **Lemma 6.**  The perturbation estimate, with `ρ = 404.25`. -/
theorem lemma6_perturbation :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(lemma6Rho * N)) →
        |aeval x (deltaPoly N) - aeval catalan (deltaPoly N)| ≤
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε)) := by
  intro ε hε
  obtain ⟨N₁, hD⟩ := atomMatrix_det_bound (d := ε / 4) (by positivity)
  obtain ⟨N₂, hpre⟩ := realDeterminantPrefactor_eventually_le_exp (d := ε / 8) (by positivity)
  have hfac := factorial_n_le_exp (c := ε / 16) (by positivity)
  have hlog2 : ∀ᶠ N : ℕ in atTop, Real.log 2 ≤ ε / 16 * (n N : ℝ) ^ 2 := by
    have htend : Tendsto (fun N : ℕ => ε / 16 * (n N : ℝ) ^ 2) atTop atTop := by
      have : (fun N : ℕ => ε / 16 * (n N : ℝ) ^ 2) =
          fun N : ℕ => (ε / 16 * 2304) * (N : ℝ) ^ 2 := by
        funext N
        simp only [n, Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [this]
      exact Tendsto.const_mul_atTop (by positivity)
        ((tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
    exact htend.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (max (max N₁ N₂) 2000), hfac, hlog2] with N hN hf hl2
  intro x hx
  have hN0 : 0 < N := by omega
  set δ := x - catalan with hδ
  set Bβ : ℝ := 8 * (H N : ℝ) ^ 2 * (CatalanMeasure.circleK : ℝ) ^ N with hBβ
  set c : ℝ := (2 : ℝ) ^ n N * (2 : ℝ) ^ (2 * h N) * Real.exp ((n N : ℝ) * lemma6Coef) with hc
  set M : ℝ := (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N *
    Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 + Real.log 2 / 2)) with hM
  have hM0 : 0 ≤ M := by
    have := realDeterminantSheetPrefactor_nonneg N
    positivity
  have hc0 : 0 ≤ c := by positivity
  have hB0 : 0 ≤ Bβ := by
    have : (0 : ℝ) ≤ (CatalanMeasure.circleK : ℝ) := by unfold CatalanMeasure.circleK; norm_num
    positivity
  have hmain := CatalanMeasure.abs_det_add_atoms_sub_le (baseMatrix N) (atomVectors N)
    (fun a k => quadWeight N (quadNode (H N)) a k.val) δ hM0 hB0
    (fun a k => CatalanMeasure.quadWeight_chebNode_circle_le N a k.val) hc0 (hD N (by omega))
  rw [delta_matrix_eq hN0 x, aeval_catalan_deltaPoly hN0]
  change |_ - (baseMatrix N).det| ≤ _
  refine hmain.trans ?_
  -- the perturbation is small
  have hsmall : (n N : ℝ) * ((H N : ℝ) * (|δ| * Bβ * c)) ≤ 1 := by
    have hr := rho_condition (N := N) (by omega)
    have hδe : |δ| * Real.exp (lemma6Rho * N) ≤ 1 := by
      calc |δ| * Real.exp (lemma6Rho * N) ≤ Real.exp (-(lemma6Rho * N)) *
            Real.exp (lemma6Rho * N) := mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h0 : 0 ≤ (n N : ℝ) * (H N : ℝ) * Bβ * c := by positivity
    calc (n N : ℝ) * ((H N : ℝ) * (|δ| * Bβ * c)) = |δ| * ((n N : ℝ) * (H N : ℝ) * Bβ * c) := by
          ring
      _ ≤ |δ| * Real.exp (lemma6Rho * N) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ ≤ 1 := hδe
  have hpow := CatalanMeasure.one_add_pow_le_exp (t := (H N : ℝ) * (|δ| * Bβ * c))
    (by positivity) (n N)
  have he1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hfactor : (1 + (H N : ℝ) * (|δ| * Bβ * c)) ^ n N - 1 ≤ 2 := by
    have := Real.exp_le_exp.mpr hsmall
    linarith
  -- the prefactor
  have hfacn : (((n N) ! : ℕ) : ℝ) ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) := hf
  have hpref : (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N ≤
      Real.exp (ε / 8 * (n N : ℝ) ^ 2) * Real.exp (ε / 16 * (n N : ℝ) ^ 2) ^ 2 := by
    have hp := hpre N (by omega)
    unfold realDeterminantPrefactor at hp
    have hf0 : (0 : ℝ) < (((n N) ! : ℕ) : ℝ) := by positivity
    have heq : (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N =
        ((2 : ℝ) ^ n N * realDeterminantSheetPrefactor N / (((n N) ! : ℕ) : ℝ) ^ 2) *
          (((n N) ! : ℕ) : ℝ) ^ 2 := by
      field_simp
    rw [heq]
    exact mul_le_mul hp (pow_le_pow_left₀ hf0.le hfacn 2) (by positivity) (Real.exp_pos _).le
  have h2 : (2 : ℝ) ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hl2
  calc M * ((1 + (H N : ℝ) * (|δ| * Bβ * c)) ^ n N - 1) ≤ M * 2 :=
        mul_le_mul_of_nonneg_left hfactor hM0
    _ ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) * ((2 : ℝ) ^ n N * realDeterminantSheetPrefactor N) *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 + Real.log 2 / 2)) := by
        rw [hM]
        have := realDeterminantSheetPrefactor_nonneg N
        nlinarith [Real.exp_pos ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 +
          Real.log 2 / 2)), mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n N)) this]
    _ ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) *
          (Real.exp (ε / 8 * (n N : ℝ) ^ 2) * Real.exp (ε / 16 * (n N : ℝ) ^ 2) ^ 2) *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 + Real.log 2 / 2)) := by
        gcongr
    _ = Real.exp ((n N : ℝ) ^ 2 *
          (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + (9 / 16) * ε)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        linarith

/-! ### Catalan's constant has a finite irrationality measure -/

/-- **Theorem (Chebyshev window).**  For every `0 < η < 2304 γ`, all large denominators `b`
and all integers `a`, `|G - a/b| > b ^ (-μ)` with `μ = 3 · 404.25 · max (44 / η) 4`. -/
theorem catalan_irrationalityMeasure {η : ℝ} (hη0 : 0 < η) (hη : η < 2304 * measureGap) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3 * lemma6Rho * max (((44 : ℕ) : ℝ) / η) 4)) <
        |catalan - a / b| :=
  catalan_irrationalityMeasure_of_perturbation (by norm_num [lemma6Rho]) hη0 hη
    lemma6_perturbation

/-- **Theorem (prime number theorem window).**  For every `0 < η < 2304 γ`, `ε > 0` and
`c > 1`, the irrationality exponent is at most `(1 + ε) · 404.25 · max (44 / η) (c / ε)`. -/
theorem catalan_irrationalityMeasure_pnt {η ε c : ℝ} (hη0 : 0 < η)
    (hη : η < 2304 * measureGap) (hε : 0 < ε) (hc : 1 < c) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((1 + ε) * lemma6Rho * max (((44 : ℕ) : ℝ) / η) (c / ε))) <
        |catalan - a / b| :=
  catalan_irrationalityMeasure_of_perturbation_pnt (by norm_num [lemma6Rho]) hη0 hη hε hc
    lemma6_perturbation

/-- A certified lower bound for the gap `γ = U - A`. -/
theorem measureGap_gt : (9996945 / 10000000000 : ℝ) < measureGap := by
  have hl := Real.log_two_lt_d9
  unfold measureGap
  norm_num at hl ⊢
  linarith

/-- The decay rate used in the final theorems: just below the full gap `2304 γ`. -/
noncomputable def measureEta : ℝ := 2304 * (9996945 / 10000000000)

theorem measureEta_pos : 0 < measureEta := by unfold measureEta; norm_num

theorem measureEta_lt : measureEta < 2304 * measureGap := by
  unfold measureEta
  linarith [measureGap_gt]

theorem measureEta_ratio_le : ((44 : ℕ) : ℝ) / measureEta ≤ 191031 / 10000 := by
  unfold measureEta
  norm_num

end OAI.InternalCatalan
