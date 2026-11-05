module

public import Submission.CatalanMeasure.GenD.Signed.SpikeOnePoint
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Monotone tilts of the ratio of Hankel determinants (Lemmas D and E of SIMPLIFY-S2 §2.1)

The determinant of an affine path of Hankel matrices has logarithmic derivative `tr(A⁻¹ K)`
(Jacobi's formula, from `Matrix.det_one_add_smul`).  Combined with the one-point comparison
`expect_mono`, this shows that the ratio `det H(φ W) / det H(W)` increases when `W` is tilted by a
positive non-increasing factor `q` (`ratio_mono`).  The two instances used for the spike reduction
are the affine tilts `1/(a + b t)` (`ratio_mono_affine`).
-/

namespace CatalanMeasure.GenD.Signed

open MeasureTheory Matrix Finset Polynomial Set

/-! ### Jacobi's formula along an affine path -/

theorem hasDerivAt_det_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : HasDerivAt (fun r : ℝ => (1 + r • M).det) M.trace 0 := by
  have hfun : (fun r : ℝ => (1 + r • M).det) = fun r : ℝ => 1 + M.trace * r +
      ((1 + (X : ℝ[X]) • M.map C).det.divX.divX).eval r * r ^ 2 := by
    funext r; exact Matrix.det_one_add_smul r M
  rw [hfun]
  set P := (1 + (X : ℝ[X]) • M.map C).det.divX.divX
  have h1 : HasDerivAt (fun r : ℝ => 1 + M.trace * r) M.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul M.trace).const_add 1
  have h2 : HasDerivAt (fun r : ℝ => P.eval r * r ^ 2) 0 0 := by
    have h := (P.hasDerivAt (0 : ℝ)).mul (hasDerivAt_pow 2 (0 : ℝ))
    have e : (Polynomial.eval 0 (derivative P) * (0 : ℝ) ^ 2 +
        P.eval 0 * ((2 : ℕ) * (0 : ℝ) ^ (2 - 1))) = 0 := by simp
    rw [e] at h
    exact h
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3

theorem hasDerivAt_det_affine {n : Type*} [Fintype n] [DecidableEq n] (A K : Matrix n n ℝ)
    (l0 : ℝ) (h : IsUnit (A + l0 • K).det) :
    HasDerivAt (fun l : ℝ => (A + l • K).det)
      ((A + l0 • K).det * ((A + l0 • K)⁻¹ * K).trace) l0 := by
  set N := A + l0 • K with hNdef
  have hN : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N h
  have hfun : ∀ l : ℝ, (A + l • K).det = N.det * (1 + (l - l0) • (N⁻¹ * K)).det := by
    intro l
    have : A + l • K = N * (1 + (l - l0) • (N⁻¹ * K)) := by
      rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, hN, one_mul, hNdef, sub_smul]
      abel
    rw [this, det_mul]
  have h0 := hasDerivAt_det_one_add_smul (N⁻¹ * K)
  have h1 : HasDerivAt (fun l : ℝ => (1 + (l - l0) • (N⁻¹ * K)).det) (N⁻¹ * K).trace l0 :=
    HasDerivAt.comp_sub_const l0 l0 (f := fun r : ℝ => (1 + r • (N⁻¹ * K)).det)
      (by simpa using h0)
  have h2 := h1.const_mul N.det
  simpa [← hfun] using h2

theorem hasDerivAt_log_det_affine {n : Type*} [Fintype n] [DecidableEq n] (A K : Matrix n n ℝ)
    (l0 : ℝ) (h : 0 < (A + l0 • K).det) :
    HasDerivAt (fun l : ℝ => Real.log (A + l • K).det) (((A + l0 • K)⁻¹ * K).trace) l0 := by
  have := (hasDerivAt_det_affine A K l0 h.ne'.isUnit).log h.ne'
  simpa [mul_div_cancel_left₀ _ h.ne'] using this

/-! ### The tilting path -/

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem adm_tilt {q : ℝ → ℝ} (hq : Adm q) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    Adm (fun t => (1 - l) + l * q t) := by
  obtain ⟨c, hc, hc'⟩ := hq.lower
  obtain ⟨C, hC⟩ := hq.bound
  refine ⟨⟨measurable_const.add (measurable_const.mul hq.meas), ⟨|1 - l| + |l| * C, ?_⟩⟩,
    ⟨min 1 c, lt_min one_pos hc, ?_⟩⟩
  · intro t ht
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC t ht) (abs_nonneg _)
  · intro t ht
    have h1 : min 1 c ≤ 1 := min_le_left _ _
    have h2 : min 1 c ≤ q t := (min_le_right _ _).trans (hc' t ht)
    nlinarith [hl.1, hl.2]

/-- Lemma E (monotone tilts): if `q > 0` is non-increasing and `C¹`, then the ratio
`det H(φ W)/det H(W)` is no larger than `det H(φ W q)/det H(W q)`. -/
theorem ratio_mono (hμ : Setting μ) {W φ q q' : ℝ → ℝ} (hW : Adm W) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) (hq : Adm q)
    (hq' : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt q (q' t) t) (hq'c : ContinuousOn q' (Icc 0 2))
    (hq'm : Measurable q') (hq'n : ∀ t ∈ Icc (0 : ℝ) 2, q' t ≤ 0) (s : ℕ) :
    (hk μ (fun t => φ t * W t) s).det / (hk μ W s).det ≤
      (hk μ (fun t => φ t * (W t * q t)) s).det / (hk μ (fun t => W t * q t) s).det := by
  have hsupp := hμ.supp
  -- the path of weights
  let Gl : ℝ → ℝ → ℝ := fun l t => (1 - l) + l * q t
  let Wl : ℝ → ℝ → ℝ := fun l t => W t + l * (W t * (q t - 1))
  have hWl : ∀ l t, Wl l t = W t * Gl l t := by intro l t; simp only [Wl, Gl]; ring
  let K : Matrix (Fin s) (Fin s) ℝ := hk μ (fun t => W t * (q t - 1)) s
  let Kφ : Matrix (Fin s) (Fin s) ℝ := hk μ (fun t => φ t * (W t * (q t - 1))) s
  let A0 : Matrix (Fin s) (Fin s) ℝ := hk μ W s
  let B0 : Matrix (Fin s) (Fin s) ℝ := hk μ (fun t => φ t * W t) s
  have hbK : Bd (fun t => W t * (q t - 1)) := hW.toBd.mul (hq.toBd.sub (Bd.const 1))
  have hbKφ : Bd (fun t => φ t * (W t * (q t - 1))) := hφ.toBd.mul hbK
  have hbφW : Bd (fun t => φ t * W t) := hφ.toBd.mul hW.toBd
  have hmatA : ∀ l : ℝ, hk μ (Wl l) s = A0 + l • K := by
    intro l
    have := hk_add hsupp hW.toBd ((Bd.const l).mul hbK) s
    simp only [Wl]
    rw [this, hk_smul]
  have hmatB : ∀ l : ℝ, hk μ (fun t => φ t * Wl l t) s = B0 + l • Kφ := by
    intro l
    have := hk_add hsupp hbφW ((Bd.const l).mul hbKφ) s
    have e : (fun t => φ t * Wl l t) = fun t => φ t * W t + l * (φ t * (W t * (q t - 1))) := by
      funext t; simp only [Wl]; ring
    rw [e, this, hk_smul]
  have hadmWl : ∀ l ∈ Icc (0 : ℝ) 1, Adm (Wl l) := by
    intro l hl
    have : Wl l = fun t => W t * Gl l t := funext (hWl l)
    rw [this]; exact hW.mul (adm_tilt hq hl)
  have hdetA : ∀ l ∈ Icc (0 : ℝ) 1, 0 < (A0 + l • K).det := by
    intro l hl
    rw [← hmatA]; exact (hk_posDef hμ (hadmWl l hl) s).det_pos
  have hdetB : ∀ l ∈ Icc (0 : ℝ) 1, 0 < (B0 + l • Kφ).det := by
    intro l hl
    rw [← hmatB]; exact (hk_posDef hμ (hφ.mul (hadmWl l hl)) s).det_pos
  -- the derivative expressions
  let hl : ℝ → ℝ → ℝ := fun l t => (q t - 1) / Gl l t
  have hGpos : ∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 2, 0 < Gl l t := fun l hl t ht =>
    (adm_tilt hq hl).pos ht
  have htrA : ∀ l ∈ Icc (0 : ℝ) 1,
      ((A0 + l • K)⁻¹ * K).trace = ∫ t, hl l t * dens μ (Wl l) s t ∂μ := by
    intro l hlm
    rw [← hmatA, trace_mul_comm]
    rw [trace_hk_mul hsupp hbK]
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with t ht
    have := (hGpos l hlm t ht).ne'
    simp only [dens, hl, hWl]
    field_simp
  have htrB : ∀ l ∈ Icc (0 : ℝ) 1,
      ((B0 + l • Kφ)⁻¹ * Kφ).trace = ∫ t, hl l t * dens μ (fun t => φ t * Wl l t) s t ∂μ := by
    intro l hlm
    rw [← hmatB, trace_mul_comm]
    rw [trace_hk_mul hsupp hbKφ]
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with t ht
    have := (hGpos l hlm t ht).ne'
    simp only [dens, hl, hWl]
    field_simp
  -- the observable and its derivative
  have hobs : ∀ l ∈ Icc (0 : ℝ) 1,
      ∫ t, hl l t * dens μ (Wl l) s t ∂μ ≤ ∫ t, hl l t * dens μ (fun t => φ t * Wl l t) s t ∂μ := by
    intro l hlm
    have hc : ContinuousOn q (Icc 0 2) := fun t ht => (hq' t ht).continuousAt.continuousWithinAt
    refine expect_mono hμ (hadmWl l hlm) hφ hφa s (g := hl l)
      (g' := fun t => q' t / (Gl l t) ^ 2) ?_ ?_ ?_ ?_
    · intro t ht
      have h1 : HasDerivAt (fun t => q t - 1) (q' t) t := (hq' t ht).sub_const 1
      have h2 : HasDerivAt (fun t => Gl l t) (l * q' t) t := by
        have := ((hq' t ht).const_mul l).const_add (1 - l)
        simpa [Gl] using this
      have h3 := h1.div h2 (hGpos l hlm t ht).ne'
      convert h3 using 1
      have := (hGpos l hlm t ht).ne'
      simp only [Gl] at this ⊢
      field_simp
      ring
    · refine hq'c.div ?_ ?_
      · exact (continuousOn_const.add (continuousOn_const.mul hc)).pow 2
      · intro t ht
        exact pow_ne_zero 2 (hGpos l hlm t ht).ne'
    · exact hq'm.div ((measurable_const.add (measurable_const.mul hq.meas)).pow_const 2)
    · intro t ht
      exact div_nonpos_of_nonpos_of_nonneg (hq'n t ht) (sq_nonneg _)
  -- monotonicity of F
  let F : ℝ → ℝ := fun l => Real.log (B0 + l • Kφ).det - Real.log (A0 + l • K).det
  have hFd : ∀ l ∈ Icc (0 : ℝ) 1, HasDerivAt F
      (((B0 + l • Kφ)⁻¹ * Kφ).trace - ((A0 + l • K)⁻¹ * K).trace) l := fun l hlm =>
    (hasDerivAt_log_det_affine B0 Kφ l (hdetB l hlm)).sub
      (hasDerivAt_log_det_affine A0 K l (hdetA l hlm))
  have hmono : MonotoneOn F (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun l hlm => (hFd l hlm).continuousAt.continuousWithinAt)
      (f' := fun l => ((B0 + l • Kφ)⁻¹ * Kφ).trace - ((A0 + l • K)⁻¹ * K).trace)
      (fun l hlm => (hFd l (interior_subset hlm)).hasDerivWithinAt) ?_
    intro l hlm
    have hlm' := interior_subset hlm
    rw [htrA l hlm', htrB l hlm']
    linarith [hobs l hlm']
  have h01 := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    zero_le_one
  have hA1 : A0 + (1 : ℝ) • K = hk μ (fun t => W t * q t) s := by
    rw [← hmatA]; congr 1; funext t; simp only [Wl]; ring
  have hB1 : B0 + (1 : ℝ) • Kφ = hk μ (fun t => φ t * (W t * q t)) s := by
    rw [← hmatB]; congr 1; funext t; simp only [Wl]; ring
  simp only [F, zero_smul, add_zero, hA1, hB1] at h01
  have p1 : 0 < (hk μ W s).det := (hk_posDef hμ hW s).det_pos
  have p2 : 0 < (hk μ (fun t => φ t * W t) s).det := (hk_posDef hμ (hφ.mul hW) s).det_pos
  have p3 : 0 < (hk μ (fun t => W t * q t) s).det := (hk_posDef hμ (hW.mul hq) s).det_pos
  have p4 : 0 < (hk μ (fun t => φ t * (W t * q t)) s).det :=
    (hk_posDef hμ (hφ.mul (hW.mul hq)) s).det_pos
  rw [← Real.log_div p2.ne' p1.ne', ← Real.log_div p4.ne' p3.ne'] at h01
  exact (Real.log_le_log_iff (div_pos p2 p1) (div_pos p4 p3)).mp h01

/-! ### Affine tilts and spike factors -/

theorem hk_congr (hμ : OnI μ) {f g : ℝ → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 2, f t = g t) (s : ℕ) :
    hk μ f s = hk μ g s := by
  ext i j
  simp only [hk, Matrix.of_apply]
  refine integral_congr_ae ?_
  filter_upwards [hμ] with t ht
  rw [h t ht]

/-- The ratio `det H(φ W) / det H(W)`. -/
noncomputable def rat (μ : Measure ℝ) (φ W : ℝ → ℝ) (s : ℕ) : ℝ :=
  (hk μ (fun t => φ t * W t) s).det / (hk μ W s).det

theorem rat_congr (hμ : OnI μ) {φ W W' : ℝ → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 2, W t = W' t) (s : ℕ) :
    rat μ φ W s = rat μ φ W' s := by
  unfold rat
  rw [hk_congr hμ h s, hk_congr hμ (f := fun t => φ t * W t) (g := fun t => φ t * W' t)
    (fun t ht => by rw [h t ht]) s]

theorem Adm.one : Adm (fun _ : ℝ => (1 : ℝ)) := Adm.of_continuous continuous_const fun _ _ => one_pos

theorem Adm.pow {f : ℝ → ℝ} (hf : Adm f) (n : ℕ) : Adm (fun t => f t ^ n) := by
  induction n with
  | zero => simpa using Adm.one
  | succ n ih =>
    have := ih.mul hf
    simpa [pow_succ] using this

theorem adm_inv_affine {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : Adm (fun t => (a + b * t)⁻¹) := by
  refine ⟨⟨(measurable_const.add (measurable_const.mul measurable_id)).inv, ⟨a⁻¹, ?_⟩⟩,
    ⟨(a + b * 2)⁻¹, by positivity, ?_⟩⟩
  · intro t ht
    have h1 : a ≤ a + b * t := by nlinarith [ht.1]
    rw [abs_of_pos (by positivity [ht.1])]
    exact inv_anti₀ ha h1
  · intro t ht
    have h1 : a + b * t ≤ a + b * 2 := by nlinarith [ht.2]
    exact inv_anti₀ (by nlinarith [ht.1]) h1

theorem adm_affine {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : Adm (fun t => a + b * t) :=
  Adm.of_continuous (continuous_const.add (continuous_const.mul continuous_id))
    fun t ht => by nlinarith [ht.1]

/-- Lemma E (affine tilts): the ratio is larger for the tilt `1/(a₀ + b₀ t)` than for
`1/(a₁ + b₁ t)` whenever `b₁ a₀ ≤ a₁ b₀`. -/
theorem rat_affine_mono (hμ : Setting μ) {W φ : ℝ → ℝ} (hW : Adm W) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) {a0 b0 a1 b1 : ℝ} (ha0 : 0 < a0) (hb0 : 0 ≤ b0)
    (ha1 : 0 < a1) (hb1 : 0 ≤ b1) (hcond : b1 * a0 ≤ a1 * b0) (s : ℕ) :
    rat μ φ (fun t => W t * (a1 + b1 * t)⁻¹) s ≤ rat μ φ (fun t => W t * (a0 + b0 * t)⁻¹) s := by
  have hden : ∀ t ∈ Icc (0 : ℝ) 2, 0 < a0 + b0 * t := fun t ht => by nlinarith [ht.1]
  have hden1 : ∀ t ∈ Icc (0 : ℝ) 2, 0 < a1 + b1 * t := fun t ht => by nlinarith [ht.1]
  have hq : Adm (fun t => (a1 + b1 * t) * (a0 + b0 * t)⁻¹) :=
    (adm_affine ha1 hb1).mul (adm_inv_affine ha0 hb0)
  have hq' : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt (fun t => (a1 + b1 * t) * (a0 + b0 * t)⁻¹)
      ((b1 * a0 - a1 * b0) / (a0 + b0 * t) ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => a1 + b1 * t) b1 t := by
      simpa using ((hasDerivAt_id t).const_mul b1).const_add a1
    have h2 : HasDerivAt (fun t => a0 + b0 * t) b0 t := by
      simpa using ((hasDerivAt_id t).const_mul b0).const_add a0
    have h3 := h1.mul (h2.inv (hden t ht).ne')
    convert h3 using 1
    have := (hden t ht).ne'
    simp only [Pi.inv_apply]
    field_simp
    ring
  have key := ratio_mono hμ (W := fun t => W t * (a1 + b1 * t)⁻¹) (φ := φ)
    (q := fun t => (a1 + b1 * t) * (a0 + b0 * t)⁻¹)
    (q' := fun t => (b1 * a0 - a1 * b0) / (a0 + b0 * t) ^ 2)
    (hW.mul (adm_inv_affine ha1 hb1)) hφ hφa hq hq'
    (continuousOn_const.div ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht).ne')
    (measurable_const.div ((measurable_const.add (measurable_const.mul measurable_id)).pow_const 2))
    (fun t ht => div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)) s
  refine le_trans (le_of_eq rfl) (key.trans (le_of_eq ?_))
  refine rat_congr hμ.supp (fun t ht => ?_) s
  have := (hden t ht).ne'
  have := (hden1 t ht).ne'
  field_simp

/-- The pole factor `(A + t)⁻¹`; a spike `(1 + 2y u + y²)⁻¹` is `(2y)⁻¹ (A + t)⁻¹` with
`t = 1 + u` and `A = (1 - y)² / (2y)`. -/
noncomputable def poleK (A t : ℝ) : ℝ := (A + t)⁻¹

theorem adm_poleK {A : ℝ} (hA : 0 < A) : Adm (poleK A) := by
  have e : poleK A = fun t => (A + 1 * t)⁻¹ := by funext t; simp [poleK]
  rw [e]; exact adm_inv_affine hA zero_le_one

/-- Deeper spikes (`A` smaller) increase the ratio. -/
theorem rat_pole_mono (hμ : Setting μ) {W φ : ℝ → ℝ} (hW : Adm W) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) {A0 A1 : ℝ} (h0 : 0 < A0) (h01 : A0 ≤ A1) (s : ℕ) :
    rat μ φ (fun t => W t * poleK A1 t) s ≤ rat μ φ (fun t => W t * poleK A0 t) s := by
  have := rat_affine_mono hμ hW hφ hφa (a0 := A0) (b0 := 1) (a1 := A1) (b1 := 1) h0 zero_le_one
    (h0.trans_le h01) zero_le_one (by linarith) s
  simpa [poleK] using this

/-- A phantom factor only increases the ratio. -/
theorem rat_phantom_mono (hμ : Setting μ) {W φ : ℝ → ℝ} (hW : Adm W) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) {A : ℝ} (hA : 0 < A) (s : ℕ) :
    rat μ φ W s ≤ rat μ φ (fun t => W t * poleK A t) s := by
  have := rat_affine_mono hμ hW hφ hφa (a0 := A) (b0 := 1) (a1 := 1) (b1 := 0) hA zero_le_one
    one_pos le_rfl (by linarith) s
  refine le_trans (le_of_eq ?_) (by simpa [poleK] using this)
  exact rat_congr hμ.supp (fun t _ => by simp) s

/-- Moving `M` poles to a common (deeper) position increases the ratio. -/
theorem rat_poles_le (hμ : Setting μ) {φ : ℝ → ℝ} (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) {A : ℝ} (hA : 0 < A) :
    ∀ (M : ℕ) (W : ℝ → ℝ), Adm W → ∀ As : Fin M → ℝ, (∀ p, A ≤ As p) → ∀ s : ℕ,
      rat μ φ (fun t => W t * ∏ p, poleK (As p) t) s ≤
        rat μ φ (fun t => W t * poleK A t ^ M) s := by
  intro M
  induction M with
  | zero => intro W _ As _ s; simp
  | succ M ih =>
    intro W hW As hAs s
    have hA0 : 0 < As 0 := hA.trans_le (hAs 0)
    have hs0 : Adm (poleK (As 0)) := adm_poleK hA0
    have e1 : (fun t => W t * ∏ p : Fin (M + 1), poleK (As p) t) =
        fun t => (W t * poleK (As 0) t) * ∏ p : Fin M, poleK (As p.succ) t := by
      funext t; rw [Fin.prod_univ_succ]; ring
    rw [e1]
    refine (ih (fun t => W t * poleK (As 0) t) (hW.mul hs0) (fun p => As p.succ)
      (fun p => hAs p.succ) s).trans ?_
    have e2 : (fun t => W t * poleK (As 0) t * poleK A t ^ M) =
        fun t => (W t * poleK A t ^ M) * poleK (As 0) t := by funext t; ring
    have e3 : (fun t => W t * poleK A t ^ (M + 1)) =
        fun t => (W t * poleK A t ^ M) * poleK A t := by funext t; rw [pow_succ]; ring
    rw [e2, e3]
    exact rat_pole_mono hμ (hW.mul ((adm_poleK hA).pow M)) hφ hφa hA (hAs 0) s

theorem rat_smul (φ W : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) (s : ℕ) :
    rat μ φ (fun t => c * W t) s = rat μ φ W s := by
  unfold rat
  have e : (fun t => φ t * (c * W t)) = fun t => c * (φ t * W t) := by funext t; ring
  rw [e, hk_smul, hk_smul, Matrix.det_smul, Matrix.det_smul]
  simp only [Fintype.card_fin]
  field_simp

#print axioms ratio_mono
#print axioms rat_affine_mono
#print axioms rat_poles_le
#print axioms rat_phantom_mono

end CatalanMeasure.GenD.Signed
