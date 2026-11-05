module

public import Submission.CatalanMeasure.GenD.Signed.RatioIdentity
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The β = 2 one-point comparison (Lemmas A, B, C of SIMPLIFY-S2 §2.1)

Hankel matrices `hk μ W s = [∫ t^(i+j) W dμ]` of a weight `W` on a finite measure `μ` carried by
`[0,2]` (`t = 1 + cos θ`).  Main results:

* `trace_mul_inv_antitone` (Lemma A): `tr(P Z'⁻¹) ≤ tr(P Z⁻¹)` for `0 ≤ P`, `0 < Z ≤ Z'`.
* `tail_mass_mono` (Lemma B): for `φ` positive and non-increasing, the one-point tail mass of
  `φ W` above `y` is at most that of `W`.
* `layer_cake` (Lemma C): `∫ g F dμ = g 0 ∫ F dμ + ∫₀² g'(y) ∫_{t>y} F dμ dy`.
-/

namespace CatalanMeasure.GenD.Signed

open MeasureTheory Matrix Finset Polynomial Set

/-! ### Weights -/

/-- Bounded measurable on `[0,2]`. -/
structure Bd (g : ℝ → ℝ) : Prop where
  meas : Measurable g
  bound : ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 2, |g t| ≤ C

/-- Admissible weight: bounded measurable and bounded below by a positive constant on `[0,2]`. -/
structure Adm (g : ℝ → ℝ) : Prop extends Bd g where
  lower : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0 : ℝ) 2, c ≤ g t

/-- `μ` is carried by `[0,2]`. -/
def OnI (μ : Measure ℝ) : Prop := ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 2

/-- The standing hypotheses on the base measure: carried by `[0,2]`, infinite support. -/
structure Setting (μ : Measure ℝ) : Prop where
  supp : OnI μ
  pos : ∀ p : ℝ[X], p ≠ 0 → 0 < ∫ t, (p.eval t) ^ 2 ∂μ

theorem Bd.of_continuous {g : ℝ → ℝ} (hg : Continuous g) : Bd g := by
  refine ⟨hg.measurable, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨C, fun t ht => by simpa using hC t ht⟩

theorem Bd.const (c : ℝ) : Bd (fun _ => c) := Bd.of_continuous continuous_const

theorem Bd.mul {f g : ℝ → ℝ} (hf : Bd f) (hg : Bd g) : Bd (fun t => f t * g t) := by
  refine ⟨hf.meas.mul hg.meas, ?_⟩
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  refine ⟨C * D, fun t ht => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC t ht) (hD t ht) (abs_nonneg _) ((abs_nonneg _).trans (hC t ht))

theorem Bd.add {f g : ℝ → ℝ} (hf : Bd f) (hg : Bd g) : Bd (fun t => f t + g t) := by
  refine ⟨hf.meas.add hg.meas, ?_⟩
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  exact ⟨C + D, fun t ht => (abs_add_le _ _).trans (add_le_add (hC t ht) (hD t ht))⟩

theorem Bd.sub {f g : ℝ → ℝ} (hf : Bd f) (hg : Bd g) : Bd (fun t => f t - g t) := by
  refine ⟨hf.meas.sub hg.meas, ?_⟩
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  exact ⟨C + D, fun t ht => (abs_sub _ _).trans (add_le_add (hC t ht) (hD t ht))⟩

theorem Adm.mul {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g) : Adm (fun t => f t * g t) := by
  refine ⟨hf.toBd.mul hg.toBd, ?_⟩
  obtain ⟨c, hc, hc'⟩ := hf.lower
  obtain ⟨d, hd, hd'⟩ := hg.lower
  exact ⟨c * d, mul_pos hc hd, fun t ht => mul_le_mul (hc' t ht) (hd' t ht) hd.le
    (hc.le.trans (hc' t ht))⟩

theorem Adm.of_continuous {g : ℝ → ℝ} (hg : Continuous g) (hpos : ∀ t ∈ Icc (0 : ℝ) 2, 0 < g t) :
    Adm g := by
  refine ⟨Bd.of_continuous hg, ?_⟩
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_isMinOn
    ⟨0, by simp⟩ hg.continuousOn
  exact ⟨g t0, hpos t0 ht0, fun t ht => hmin ht⟩

theorem Adm.pos {g : ℝ → ℝ} (hg : Adm g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : 0 < g t := by
  obtain ⟨c, hc, hc'⟩ := hg.lower
  exact hc.trans_le (hc' t ht)

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem Bd.integrable_pow_mul (hμ : OnI μ) {g : ℝ → ℝ} (hg : Bd g) (n : ℕ) :
    Integrable (fun t => t ^ n * g t) μ := by
  obtain ⟨C, hC⟩ := hg.bound
  refine Integrable.of_bound (C := 2 ^ n * C)
    ((measurable_id.pow_const n).mul hg.meas).aestronglyMeasurable ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h0 : |t| ≤ 2 := by rw [abs_of_nonneg ht.1]; exact ht.2
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 n) (hC t ht) (abs_nonneg _)
    (by positivity)

theorem Bd.integrable (hμ : OnI μ) {g : ℝ → ℝ} (hg : Bd g) : Integrable g μ := by
  simpa using hg.integrable_pow_mul hμ 0

/-! ### Hankel matrices -/

/-- The Hankel matrix `[∫ t^(i+j) W dμ]_{i,j<s}`. -/
noncomputable def hk (μ : Measure ℝ) (W : ℝ → ℝ) (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun i j => ∫ t, t ^ ((i : ℕ) + (j : ℕ)) * W t ∂μ

theorem hk_eq_hankelMat (W : ℝ → ℝ) (s : ℕ) : hk μ W s = hankelMat μ W s := by
  ext i j
  simp only [hk, hankelMat, Matrix.of_apply, ← mul_assoc, ← pow_add]

theorem hk_isHermitian (W : ℝ → ℝ) (s : ℕ) : (hk μ W s).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, hk, Matrix.of_apply, star_trivial, add_comm]

theorem hk_add (hμ : OnI μ) {f g : ℝ → ℝ} (hf : Bd f) (hg : Bd g) (s : ℕ) :
    hk μ (fun t => f t + g t) s = hk μ f s + hk μ g s := by
  ext i j
  simp only [hk, Matrix.of_apply, Matrix.add_apply, mul_add]
  exact integral_add (hf.integrable_pow_mul hμ _) (hg.integrable_pow_mul hμ _)

theorem hk_sub (hμ : OnI μ) {f g : ℝ → ℝ} (hf : Bd f) (hg : Bd g) (s : ℕ) :
    hk μ (fun t => f t - g t) s = hk μ f s - hk μ g s := by
  ext i j
  simp only [hk, Matrix.of_apply, Matrix.sub_apply, mul_sub]
  exact integral_sub (hf.integrable_pow_mul hμ _) (hg.integrable_pow_mul hμ _)

theorem hk_smul (c : ℝ) (g : ℝ → ℝ) (s : ℕ) :
    hk μ (fun t => c * g t) s = c • hk μ g s := by
  ext i j
  simp only [hk, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only; ring

theorem hk_restrict_add (hμ : OnI μ) {g : ℝ → ℝ} (hg : Bd g) {S : Set ℝ} (hS : MeasurableSet S)
    (s : ℕ) : hk μ g s = hk (μ.restrict S) g s + hk (μ.restrict Sᶜ) g s := by
  ext i j
  simp only [hk, Matrix.of_apply, Matrix.add_apply]
  exact (integral_add_compl hS (hg.integrable_pow_mul hμ _)).symm

/-- The polynomial `∑ x_i X^i`. -/
noncomputable def polyOf {s : ℕ} (x : Fin s → ℝ) : ℝ[X] := ∑ i : Fin s, C (x i) * X ^ (i : ℕ)

theorem eval_polyOf {s : ℕ} (x : Fin s → ℝ) (t : ℝ) :
    (polyOf x).eval t = ∑ i : Fin s, x i * t ^ (i : ℕ) := by
  simp [polyOf, eval_finsetSum]

theorem hk_quad (hμ : OnI μ) {W : ℝ → ℝ} (hW : Bd W) {s : ℕ} (x : Fin s → ℝ) :
    x ⬝ᵥ (hk μ W s *ᵥ x) = ∫ t, ((polyOf x).eval t) ^ 2 * W t ∂μ := by
  have hint : ∀ i j : Fin s, Integrable (fun t => t ^ ((i : ℕ) + (j : ℕ)) * W t) μ :=
    fun i j => hW.integrable_pow_mul hμ _
  have e1 : ∀ t : ℝ, ((polyOf x).eval t) ^ 2 * W t =
      ∑ i : Fin s, ∑ j : Fin s, x i * x j * (t ^ ((i : ℕ) + (j : ℕ)) * W t) := by
    intro t
    rw [eval_polyOf, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  simp_rw [e1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint i j).const_mul _))]
  simp only [dotProduct, mulVec, hk, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

theorem hk_posSemidef (hμ : OnI μ) {W : ℝ → ℝ} (hW : Bd W)
    (h0 : ∀ᵐ t ∂μ, 0 ≤ W t) (s : ℕ) : (hk μ W s).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hk_isHermitian W s) fun x => ?_
  rw [star_trivial, hk_quad hμ hW x]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h0] with t ht
  exact mul_nonneg (sq_nonneg _) ht

theorem polyOf_ne_zero {s : ℕ} {x : Fin s → ℝ} (hx : x ≠ 0) : polyOf x ≠ 0 := by
  intro h0
  apply hx
  funext i
  have := congrArg (fun q : ℝ[X] => q.coeff (i : ℕ)) h0
  simp only [polyOf, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  simpa [Fin.val_inj] using this

theorem hk_posDef (hμ : Setting μ) {W : ℝ → ℝ} (hW : Adm W) (s : ℕ) : (hk μ W s).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (hk_isHermitian W s) fun x hx => ?_
  rw [star_trivial, hk_quad hμ.supp hW.toBd x]
  obtain ⟨c, hc, hc'⟩ := hW.lower
  have hp := hμ.pos _ (polyOf_ne_zero hx)
  have hpb : Bd (fun t => ((polyOf x).eval t) ^ 2) :=
    Bd.of_continuous ((polyOf x).continuous.pow 2)
  have hi1 := hpb.integrable hμ.supp
  have hi2 : Integrable (fun t => ((polyOf x).eval t) ^ 2 * W t) μ :=
    (hpb.mul hW.toBd).integrable hμ.supp
  calc 0 < c * ∫ t, ((polyOf x).eval t) ^ 2 ∂μ := mul_pos hc hp
    _ = ∫ t, c * ((polyOf x).eval t) ^ 2 ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ t, ((polyOf x).eval t) ^ 2 * W t ∂μ := by
      refine integral_mono_ae (hi1.const_mul c) hi2 ?_
      filter_upwards [hμ.supp] with t ht
      nlinarith [sq_nonneg ((polyOf x).eval t), hc' t ht]

/-! ### The kernel and traces -/

/-- The one-point kernel `∑_{i,j} A_{ji} t^(i+j)` of a matrix `A`. -/
noncomputable def kern {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin s, ∑ j : Fin s, A j i * t ^ ((i : ℕ) + (j : ℕ))

theorem trace_hk_mul (hμ : OnI μ) {W : ℝ → ℝ} (hW : Bd W) {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) :
    trace (hk μ W s * A) = ∫ t, kern A t * W t ∂μ := by
  have hint : ∀ i j : Fin s, Integrable (fun t => t ^ ((i : ℕ) + (j : ℕ)) * W t) μ :=
    fun i j => hW.integrable_pow_mul hμ _
  have e1 : ∀ t : ℝ, kern A t * W t =
      ∑ i : Fin s, ∑ j : Fin s, A j i * (t ^ ((i : ℕ) + (j : ℕ)) * W t) := by
    intro t
    simp only [kern, Finset.sum_mul, mul_assoc]
  simp_rw [e1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint i j).const_mul _))]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hk, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

theorem kern_nonneg {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} (hA : A.PosSemidef) (t : ℝ) :
    0 ≤ kern A t := by
  have := hA.dotProduct_mulVec_nonneg (fun i : Fin s => t ^ (i : ℕ))
  simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum] at this
  have e : kern A t = ∑ j : Fin s, ∑ i : Fin s, t ^ (j : ℕ) * (A j i * t ^ (i : ℕ)) := by
    simp only [kern]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]; ring
  rw [e]; exact this

/-! ### Lemma A: inverse is antitone -/

theorem posSemidef_fromBlocks_zero {s : ℕ} {X : Matrix (Fin s) (Fin s) ℝ} (hX : X.PosSemidef) :
    (fromBlocks X (0 : Matrix (Fin s) (Fin s) ℝ) (0 : Matrix (Fin s) (Fin s) ℝ)
      (0 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef := by
  let B : Matrix (Fin s ⊕ Fin s) (Fin s) ℝ :=
    Matrix.of fun i j => Sum.elim (fun a => if a = j then (1 : ℝ) else 0) (fun _ => 0) i
  have h := hX.mul_mul_conjTranspose_same B
  convert h using 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [B, Matrix.mul_apply]

theorem inv_sub_inv_posSemidef {s : ℕ} {Z Z' : Matrix (Fin s) (Fin s) ℝ} (hZ : Z.PosDef)
    (h : (Z' - Z).PosSemidef) : (Z⁻¹ - Z'⁻¹).PosSemidef := by
  have hZ' : Z'.PosDef := by
    have := hZ.add_posSemidef h
    simpa using this
  let _ := hZ.isUnit.invertible
  let _ := hZ'.isUnit.invertible
  have h1 : (fromBlocks Z (1 : Matrix (Fin s) (Fin s) ℝ) (1 : Matrix (Fin s) (Fin s) ℝ)ᴴ
      Z⁻¹).PosSemidef := by
    rw [PosDef.fromBlocks₁₁ _ _ hZ]
    simp
    exact PosSemidef.zero
  have h2 := posSemidef_fromBlocks_zero h
  have h3 : (fromBlocks Z' (1 : Matrix (Fin s) (Fin s) ℝ) (1 : Matrix (Fin s) (Fin s) ℝ)ᴴ
      Z⁻¹).PosSemidef := by
    have := h1.add h2
    convert this using 1
    simp [fromBlocks_add]
  rw [PosDef.fromBlocks₁₁ _ _ hZ'] at h3
  simpa using h3

open scoped MatrixOrder in
theorem trace_mul_nonneg {s : ℕ} {P Q : Matrix (Fin s) (Fin s) ℝ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ trace (P * Q) := by
  have hP' : 0 ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP
  have hR : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP'
  have hRs : (CFC.sqrt P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have h1 : trace (P * Q) = trace (CFC.sqrt P * Q * (CFC.sqrt P)ᴴ) := by
    rw [hRs.isHermitian.eq]
    calc trace (P * Q) = trace (CFC.sqrt P * (CFC.sqrt P * Q)) := by rw [← mul_assoc, hR]
      _ = trace (CFC.sqrt P * Q * CFC.sqrt P) := trace_mul_comm _ _
  rw [h1]
  exact (hQ.mul_mul_conjTranspose_same _).trace_nonneg

/-- Lemma A: `tr(P Z'⁻¹) ≤ tr(P Z⁻¹)` for `P ≥ 0` and `0 < Z ≤ Z'`. -/
theorem trace_mul_inv_antitone {s : ℕ} {P Z Z' : Matrix (Fin s) (Fin s) ℝ} (hP : P.PosSemidef)
    (hZ : Z.PosDef) (h : (Z' - Z).PosSemidef) : trace (P * Z'⁻¹) ≤ trace (P * Z⁻¹) := by
  have := trace_mul_nonneg hP (inv_sub_inv_posSemidef hZ h)
  rw [mul_sub, trace_sub] at this
  linarith

/-! ### The one-point density and Lemma B -/

theorem OnI.restrict {μ : Measure ℝ} (hμ : OnI μ) (S : Set ℝ) : OnI (μ.restrict S) :=
  ae_restrict_of_ae hμ

/-- The one-point density `W · K_W` of the ensemble with weight `W`, as a function of `t`. -/
noncomputable def dens (μ : Measure ℝ) (W : ℝ → ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  W t * kern (hk μ W s)⁻¹ t

theorem continuous_kern {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) : Continuous (kern A) := by
  unfold kern
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_pow _)

theorem Bd.dens {W : ℝ → ℝ} (hW : Bd W) (s : ℕ) (A : Matrix (Fin s) (Fin s) ℝ) :
    Bd (fun t => W t * kern A t) :=
  hW.mul (Bd.of_continuous (continuous_kern A))

theorem integral_dens (hμ : Setting μ) {W : ℝ → ℝ} (hW : Adm W) (s : ℕ) :
    ∫ t, dens μ W s t ∂μ = s := by
  have hH := hk_posDef hμ hW s
  have h1 := trace_hk_mul hμ.supp hW.toBd (hk μ W s)⁻¹
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)] at h1
  simp only [Matrix.trace_one, Fintype.card_fin] at h1
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [dens]; ring

theorem measurable_dens {W : ℝ → ℝ} (hW : Bd W) (s : ℕ) : Measurable (dens μ W s) :=
  (hW.dens s (hk μ W s)⁻¹).meas

theorem integrable_dens (hμ : OnI μ) {W : ℝ → ℝ} (hW : Bd W) (s : ℕ) :
    Integrable (dens μ W s) μ :=
  (hW.dens s (hk μ W s)⁻¹).integrable hμ

theorem trace_add_inv {s : ℕ} {X Y Z : Matrix (Fin s) (Fin s) ℝ} (hZ : Z.PosDef)
    (h : X + Y = Z) : trace (X * Z⁻¹) + trace (Y * Z⁻¹) = s := by
  rw [← trace_add, ← add_mul, h, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit)]
  simp

/-- The tail mass `∫_{t>y} W K_W dμ` as a trace. -/
theorem tail_eq_trace (hμ : OnI μ) {W : ℝ → ℝ} (hW : Bd W) (s : ℕ) (S : Set ℝ) :
    ∫ t in S, dens μ W s t ∂μ = trace (hk (μ.restrict S) W s * (hk μ W s)⁻¹) := by
  rw [trace_hk_mul (hμ.restrict S) hW]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [dens]; ring

/-- Lemma B (β = 2 one-point comparison): a positive non-increasing tilt moves the one-point
law of the ensemble stochastically to the left. -/
theorem tail_mass_mono (hμ : Setting μ) {W φ : ℝ → ℝ} (hW : Adm W) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) (s : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 2) :
    ∫ t in Ioi y, dens μ (fun t => φ t * W t) s t ∂μ ≤ ∫ t in Ioi y, dens μ W s t ∂μ := by
  have hS : MeasurableSet (Ioi y) := measurableSet_Ioi
  have hSc : MeasurableSet (Ioi y)ᶜ := hS.compl
  have hφW : Adm (fun t => φ t * W t) := hφ.mul hW
  have hc : 0 < φ y := hφ.pos hy
  set c := φ y with hcdef
  set H := hk μ W s with hH
  set H' := hk μ (fun t => φ t * W t) s with hH'
  have hHd : H.PosDef := hk_posDef hμ hW s
  have hH'd : H'.PosDef := hk_posDef hμ hφW s
  -- the four pieces
  set X := hk (μ.restrict (Ioi y)ᶜ) W s with hX
  set Y := hk (μ.restrict (Ioi y)) W s with hY
  set X' := hk (μ.restrict (Ioi y)ᶜ) (fun t => φ t * W t) s with hX'
  set Y' := hk (μ.restrict (Ioi y)) (fun t => φ t * W t) s with hY'
  have hHXY : X + Y = H := by
    rw [hH, hk_restrict_add hμ.supp hW.toBd hS s, add_comm]
  have hHXY' : X' + Y' = H' := by
    rw [hH', hk_restrict_add hμ.supp hφW.toBd hS s, add_comm]
  have hXp : X.PosSemidef := hk_posSemidef (hμ.supp.restrict _) hW.toBd
    (by
      refine (ae_restrict_iff' hSc).mpr ?_
      filter_upwards [hμ.supp] with t ht _
      exact (hW.pos ht).le) s
  have hYp : Y.PosSemidef := hk_posSemidef (hμ.supp.restrict _) hW.toBd
    (by
      refine (ae_restrict_iff' hS).mpr ?_
      filter_upwards [hμ.supp] with t ht _
      exact (hW.pos ht).le) s
  have hX'p : X'.PosSemidef := hk_posSemidef (hμ.supp.restrict _) hφW.toBd
    (by
      refine (ae_restrict_iff' hSc).mpr ?_
      filter_upwards [hμ.supp] with t ht _
      exact (hφW.pos ht).le) s
  -- X' ≥ c X on `t ≤ y`
  have hXd : (X' - c • X).PosSemidef := by
    have hb : Bd (fun t => φ t * W t - c * W t) := hφW.toBd.sub ((Bd.const c).mul hW.toBd)
    have := hk_posSemidef (μ := μ.restrict (Ioi y)ᶜ) (hμ.supp.restrict _) hb
      (by
        refine (ae_restrict_iff' hSc).mpr ?_
        filter_upwards [hμ.supp] with t ht hty
        have hty' : t ≤ y := not_lt.mp hty
        have h1 : c ≤ φ t := hφa ht hy hty'
        have h2 := hW.pos ht
        nlinarith) s
    rwa [hk_sub (hμ.supp.restrict _) hφW.toBd ((Bd.const c).mul hW.toBd), hk_smul] at this
  -- Y' ≤ c Y on `t > y`
  have hYd : (c • Y - Y').PosSemidef := by
    have hb : Bd (fun t => c * W t - φ t * W t) := ((Bd.const c).mul hW.toBd).sub hφW.toBd
    have := hk_posSemidef (μ := μ.restrict (Ioi y)) (hμ.supp.restrict _) hb
      (by
        refine (ae_restrict_iff' hS).mpr ?_
        filter_upwards [hμ.supp] with t ht hty
        have hty' : y ≤ t := le_of_lt hty
        have h1 : φ t ≤ c := hφa hy ht hty'
        have h2 := hW.pos ht
        nlinarith) s
    rwa [hk_sub (hμ.supp.restrict _) ((Bd.const c).mul hW.toBd) hφW.toBd, hk_smul] at this
  rw [tail_eq_trace hμ.supp hφW.toBd s, tail_eq_trace hμ.supp hW.toBd s]
  -- M = X' + c Y
  set M := X' + c • Y with hM
  have hMH' : (M - H').PosSemidef := by
    have : M - H' = c • Y - Y' := by rw [hM, ← hHXY']; abel
    rw [this]; exact hYd
  have hMd : M.PosDef := by
    have := hH'd.add_posSemidef hMH'
    simpa using this
  have hN : (c • H).PosDef := hHd.smul hc
  have hMN : (M - c • H).PosSemidef := by
    have : M - c • H = X' - c • X := by rw [hM, ← hHXY, smul_add]; abel
    rw [this]; exact hXd
  -- Step 1
  have e1 := trace_add_inv hH'd hHXY'
  have e2 := trace_add_inv hMd (show X' + c • Y = M from rfl)
  have s1 : trace (X' * M⁻¹) ≤ trace (X' * H'⁻¹) :=
    trace_mul_inv_antitone hX'p hH'd hMH'
  -- Step 2
  have s2 : trace ((c • Y) * M⁻¹) ≤ trace ((c • Y) * (c • H)⁻¹) :=
    trace_mul_inv_antitone (hYp.smul hc.le) hN hMN
  have e3 : trace ((c • Y) * (c • H)⁻¹) = trace (Y * H⁻¹) := by
    have hinv := Matrix.inv_smul' H (Units.mk0 c hc.ne')
      ((Matrix.isUnit_iff_isUnit_det _).mp hHd.isUnit)
    simp only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val] at hinv
    rw [hinv]
    simp only [smul_mul_assoc, mul_smul_comm, trace_smul, smul_eq_mul]
    field_simp
  linarith

/-! ### Lemma C: the layer cake -/

/-- Lemma C (layer cake). -/
theorem layer_cake (hμ : OnI μ) {F : ℝ → ℝ} (hFm : Measurable F) (hF : Integrable F μ)
    {g g' : ℝ → ℝ} (hg : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt g (g' t) t)
    (hg'c : ContinuousOn g' (Icc 0 2)) (hg'm : Measurable g') :
    IntegrableOn (fun y => g' y * ∫ t in Ioi y, F t ∂μ) (Ioc 0 2) ∧
    ∫ t, g t * F t ∂μ =
      g 0 * ∫ t, F t ∂μ + ∫ y in Ioc (0 : ℝ) 2, g' y * ∫ t in Ioi y, F t ∂μ := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 2) with hν
  let G : ℝ → ℝ → ℝ := fun t y => (Iio t).indicator g' y
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn hg'c
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hGm : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := by
    have h1 : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} := measurableSet_lt measurable_snd measurable_fst
    have h2 : (fun p : ℝ × ℝ => G p.1 p.2) = fun p => if p.2 < p.1 then g' p.2 else 0 := by
      ext p; simp [G, Set.indicator]
    rw [h2]
    exact Measurable.ite h1 (hg'm.comp measurable_snd) measurable_const
  have hGb : ∀ t y, y ∈ Ioc (0 : ℝ) 2 → |G t y| ≤ B := by
    intro t y hy
    have hy' : y ∈ Icc (0 : ℝ) 2 := ⟨hy.1.le, hy.2⟩
    simp only [G, Set.indicator]
    split_ifs
    · simpa using hB y hy'
    · simpa using hB0
  have hint : Integrable (Function.uncurry fun t y => F t * G t y) (μ.prod ν) := by
    have hmaj : Integrable (fun z : ℝ × ℝ => |F z.1| * B) (μ.prod ν) :=
      (hF.abs.comp_fst ν).mul_const B
    refine hmaj.mono' ?_ ?_
    · exact ((hFm.comp measurable_fst).mul hGm).aestronglyMeasurable
    · have hae : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ Ioc (0 : ℝ) 2 :=
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hae] with p hp
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hGb p.1 p.2 hp) (abs_nonneg _)
  -- inner integral in `y`
  have hP1 : ∀ t ∈ Icc (0 : ℝ) 2, ∫ y, G t y ∂ν = g t - g 0 := by
    intro t ht
    have e1 : ∫ y, G t y ∂ν = ∫ y in Ioc (0 : ℝ) 2 ∩ Iio t, g' y := by
      simp only [G, hν]
      exact setIntegral_indicator measurableSet_Iio
    have e2 : Ioc (0 : ℝ) 2 ∩ Iio t = Ioo 0 t := by
      ext y
      simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith [ht.2]⟩, h3⟩
    rw [e1, e2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le ht.1] at hx
      exact hg x ⟨hx.1, hx.2.trans ht.2⟩
    · refine (hg'c.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
  -- inner integral in `t`
  have hP2 : ∀ y : ℝ, ∫ t, F t * G t y ∂μ = g' y * ∫ t in Ioi y, F t ∂μ := by
    intro y
    have : ∀ t, F t * G t y = g' y * (Ioi y).indicator F t := by
      intro t
      simp only [G, Set.indicator, Set.mem_Iio, Set.mem_Ioi]
      split_ifs <;> ring
    simp_rw [this]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  have hswap := integral_integral_swap hint
  have hleft : ∀ᵐ t ∂μ, g t * F t = g 0 * F t + ∫ y, F t * G t y ∂ν := by
    filter_upwards [hμ] with t ht
    rw [integral_const_mul, hP1 t ht]; ring
  have hI1 : Integrable (fun t => ∫ y, F t * G t y ∂ν) μ := hint.integral_prod_left
  constructor
  · have := hint.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hP2 y
  · rw [integral_congr_ae hleft, integral_add (hF.const_mul _) hI1, integral_const_mul]
    congr 1
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hP2 y

/-! ### Monotonicity of one-point expectations -/

/-- A non-increasing observable has larger expectation under the tilted ensemble. -/
theorem expect_mono (hμ : Setting μ) {W φ : ℝ → ℝ} (hW : Adm W) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) (s : ℕ) {g g' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt g (g' t) t) (hg'c : ContinuousOn g' (Icc 0 2))
    (hg'm : Measurable g') (hg'n : ∀ t ∈ Icc (0 : ℝ) 2, g' t ≤ 0) :
    ∫ t, g t * dens μ W s t ∂μ ≤ ∫ t, g t * dens μ (fun t => φ t * W t) s t ∂μ := by
  have hφW : Adm (fun t => φ t * W t) := hφ.mul hW
  obtain ⟨h1, e1⟩ := layer_cake hμ.supp (measurable_dens hW.toBd s) (integrable_dens hμ.supp hW.toBd s)
    hg hg'c hg'm
  obtain ⟨h2, e2⟩ := layer_cake hμ.supp (measurable_dens hφW.toBd s)
    (integrable_dens hμ.supp hφW.toBd s) hg hg'c hg'm
  rw [e1, e2, integral_dens hμ hW, integral_dens hμ hφW]
  refine add_le_add_right ?_ _
  refine setIntegral_mono_on h1 h2 measurableSet_Ioc fun y hy => ?_
  have hy' : y ∈ Icc (0 : ℝ) 2 := ⟨hy.1.le, hy.2⟩
  exact mul_le_mul_of_nonpos_left (tail_mass_mono hμ hW hφ hφa s hy') (hg'n y hy')

#print axioms trace_mul_inv_antitone
#print axioms tail_mass_mono
#print axioms layer_cake
#print axioms expect_mono

end CatalanMeasure.GenD.Signed
