module

public import Submission.CatalanMeasure.GenD.Signed.EnergyNear

/-!
# Theorem M: mass-weighted interpolation of trials

Phase 2 (theorem-only) lane M of the Theorem A plan.  Two `SignedData` trials `DA`, `DB` at the
fixed fractions `αA < αB` that agree on `ν, e, sp, K, Rf, Cf, θ, η` (`InterpCompat`) are
interpolated linearly in `l = (α - αA)/(αB - αA)` in all the *mass-weighted* data: the reference
measure `μ`, the sequences `v, a, b, R, t, p`, `Sup`, the cap `Cb` and the spike cost `cs`
(`SignedData.interp`).  Then:

* every row field and the column field (`fNeg, fPos, fPosS, fCol` and the fixed-row fields
  `fNegM, fPosM, fPosMS, fPosMR, fNearM, fNearMS`) is *exactly affine* in `l`
  (`fNeg_interp, ..., fNearMS_interp`), hence its supremum is bounded by the chord of the endpoint
  suprema (the paper normalises these fields by the mass `t = 1 - α`; the Lean fields are the
  normalised ones, so no factor `t` appears);
* the total constant is `constant + restQ + convPart`: `restQ` is an exact quadratic polynomial in
  `l` (`isQuadOn_restQ`) whose `l²` coefficient is `curvQ`, the second difference
  `2 (q 0 + q 1) - 4 q (1/2)`; each quadratic piece contributes the combination
  `AA - AB - BA + BB` of its four-term expansion (`nsq_linSeq`, `ip_linSeq`, `refBil_mix`,
  `isQuadOn_ra`, `isQuadOn_denConst`), the three bilinear blocks of the paper.  `convPart =
  4 e (Σ|v| + Σ|a|) + 4 η e Σ|p|` is convex (`constTotal_interp_le`).

§13 (`IntervalEnds`) discharges the `α`-dependent fields `e_mem, v_summable, R_geom, t_geom,
reference, rowNeg, rowPos, column, const_le` of `SignedNearBounds` from data at the two endpoint
trials; §14 reduces `budgetFix` of one interval to two inequalities in `α` (`κlo`, `κhi`) and gives
the elementary quadratic lemmas for checking them; §16 (`SignedNearBounds.ofEnds`) assembles the
contract, which type-checks every output against the consumer.  `spikeFix` (the spike lane) and
`fixedSum` (the σ lane; use `fixedFields_interp`) are not consequences of interpolation.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### 1. Convex combinations of sequences and measures -/

/-- The convex combination `(1 - l) u + l v` of two sequences. -/
def linSeq (l : ℝ) (u v : ℕ → ℝ) : ℕ → ℝ := fun n => (1 - l) * u n + l * v n

theorem linSeq_zero (u v : ℕ → ℝ) : linSeq 0 u v = u := by
  funext n; simp [linSeq]

theorem linSeq_one (u v : ℕ → ℝ) : linSeq 1 u v = v := by
  funext n; simp [linSeq]

/-- The convex combination `(1 - l) m + l n` of two measures. -/
def mixM (l : ℝ) (m n : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - l) • m + ENNReal.ofReal l • n

/-- Species-wise convex combination of two families of reference measures. -/
def mixFam (l : ℝ) (μA μB : Bool → Measure ℝ) : Bool → Measure ℝ := fun τ => mixM l (μA τ) (μB τ)

theorem mixM_zero (m n : Measure ℝ) : mixM 0 m n = m := by
  simp [mixM]

theorem mixM_one (m n : Measure ℝ) : mixM 1 m n = n := by
  simp [mixM]

theorem mixFam_zero (μA μB : Bool → Measure ℝ) : mixFam 0 μA μB = μA := by
  funext τ; exact mixM_zero _ _

theorem mixFam_one (μA μB : Bool → Measure ℝ) : mixFam 1 μA μB = μB := by
  funext τ; exact mixM_one _ _

/-- Convex combination of two signed references `P - N` (both parts mixed). -/
def SRef.mix (l : ℝ) (μA μB : SRef) : SRef := ⟨mixFam l μA.P μB.P, mixFam l μA.N μB.N⟩

theorem SRef.mix_zero (μA μB : SRef) : SRef.mix 0 μA μB = μA := by
  unfold SRef.mix; rw [mixFam_zero, mixFam_zero]

theorem SRef.mix_one (μA μB : SRef) : SRef.mix 1 μA μB = μB := by
  unfold SRef.mix; rw [mixFam_one, mixFam_one]

theorem integrable_mixM {l : ℝ} {m n : Measure ℝ} {f : ℝ → ℝ} (hm : Integrable f m)
    (hn : Integrable f n) : Integrable f (mixM l m n) :=
  (hm.smul_measure ENNReal.ofReal_ne_top).add_measure (hn.smul_measure ENNReal.ofReal_ne_top)

theorem integral_mixM {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {m n : Measure ℝ} {f : ℝ → ℝ}
    (hm : Integrable f m) (hn : Integrable f n) :
    ∫ y, f y ∂(mixM l m n) = (1 - l) * ∫ y, f y ∂m + l * ∫ y, f y ∂n := by
  unfold mixM
  rw [integral_add_measure (hm.smul_measure ENNReal.ofReal_ne_top)
    (hn.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hl0, smul_eq_mul, smul_eq_mul]

theorem BD_mono {m : Measure ℝ} {C C' : ℝ} (h : BD m C) (hC : C ≤ C') : BD m C' := by
  refine le_trans h ?_
  rw [Measure.le_iff']
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl

theorem BD_mixM {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {m n : Measure ℝ} {C D : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hm : BD m C) (hn : BD n D) : BD (mixM l m n) ((1 - l) * C + l * D) := by
  unfold BD at hm hn ⊢
  rw [Measure.le_iff']
  intro s
  have h1 := Measure.le_iff'.1 hm s
  have h2 := Measure.le_iff'.1 hn s
  simp only [mixM, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have e : ENNReal.ofReal ((1 - l) * C + l * D) =
      ENNReal.ofReal (1 - l) * ENNReal.ofReal C + ENNReal.ofReal l * ENNReal.ofReal D := by
    rw [ENNReal.ofReal_add (mul_nonneg (by linarith) hC) (mul_nonneg hl0 hD),
      ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul hl0]
  rw [e]
  calc ENNReal.ofReal (1 - l) * m s + ENNReal.ofReal l * n s
      ≤ ENNReal.ofReal (1 - l) * (ENNReal.ofReal C * (volume.restrict (Ioo (0:ℝ) 1)) s) +
        ENNReal.ofReal l * (ENNReal.ofReal D * (volume.restrict (Ioo (0:ℝ) 1)) s) :=
        add_le_add (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl h2)
    _ = _ := by ring

theorem mixM_real_univ {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {m n : Measure ℝ}
    [IsFiniteMeasure m] [IsFiniteMeasure n] :
    (mixM l m n).real univ = (1 - l) * m.real univ + l * n.real univ := by
  simp only [mixM, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hl0]

theorem sum_mixFam_real {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {m n : Bool → Measure ℝ}
    (hm : ∀ τ, IsFiniteMeasure (m τ)) (hn : ∀ τ, IsFiniteMeasure (n τ)) :
    ∑ τ, (mixFam l m n τ).real univ =
      (1 - l) * ∑ τ, (m τ).real univ + l * ∑ τ, (n τ).real univ := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun τ _ => mixM_real_univ hl0 hl1)

theorem SRef.OK.mono {μ : SRef} {C C' : ℝ} (h : μ.OK C) (hC : C ≤ C') : μ.OK C' :=
  ⟨fun τ => BD_mono (h.hP τ) hC, fun τ => BD_mono (h.hN τ) hC, h.hNm⟩

theorem SRef.OK_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB : SRef} {C D : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hA : μA.OK C) (hB : μB.OK D) : (SRef.mix l μA μB).OK ((1 - l) * C + l * D) := by
  refine ⟨fun τ => BD_mixM hl0 hl1 hC hD (hA.hP τ) (hB.hP τ),
    fun τ => BD_mixM hl0 hl1 hC hD (hA.hN τ) (hB.hN τ), ?_⟩
  have e := sum_mixFam_real hl0 hl1 (fun τ => (hA.hN τ).finite) (fun τ => (hB.hN τ).finite)
  show ∑ τ, (mixFam l μA.N μB.N τ).real univ ≤ 1
  rw [e]
  nlinarith [hA.hNm, hB.hNm]

/-! ### 2. Integrability of the kernel sections and of the moments -/

theorem integrable_of_BD {m : Measure ℝ} {C : ℝ} (h : BD m C) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo (0:ℝ) 1)) : Integrable f m :=
  (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure h

theorem integrableOn_log_sub (x : ℝ) :
    IntegrableOn (fun y : ℝ => Real.log (x - y)) (Ioo (0:ℝ) 1) := by
  have h : IntervalIntegrable (fun t : ℝ => Real.log (x - t)) volume (x - x) (x - (x - 1)) :=
    (intervalIntegral.intervalIntegrable_log' (a := x) (b := x - 1)).comp_sub_left x
  simp only [sub_self, sub_sub_cancel] at h
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h).mono_set
    Ioo_subset_Ioc_self

theorem integrableOn_log_add (x : ℝ) :
    IntegrableOn (fun y : ℝ => Real.log (x + y)) (Ioo (0:ℝ) 1) := by
  have h : IntervalIntegrable (fun t : ℝ => Real.log (x + t)) volume (x - x) (x + 1 - x) :=
    (intervalIntegral.intervalIntegrable_log' (a := x) (b := x + 1)).comp_add_left x
  simp only [sub_self, add_sub_cancel_left] at h
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h).mono_set
    Ioo_subset_Ioc_self

/-- Every section of the log kernel is integrable against a reference measure of bounded
density. -/
theorem integrable_Kt {m : Measure ℝ} {C : ℝ} (h : BD m C) (s t : Bool) (x : ℝ) :
    Integrable (fun y => Kt s t x y) m := by
  by_cases hst : s = t
  · have e : (fun y => Kt s t x y) = fun y => -Real.log (x - y) := by
      funext y; simp [Kt, hst, Real.log_abs]
    rw [e]
    exact integrable_of_BD h (integrableOn_log_sub x).neg
  · have e : (fun y => Kt s t x y) = fun y => -Real.log (x + y) := by
      funext y; simp [Kt, hst]
    rw [e]
    exact integrable_of_BD h (integrableOn_log_add x).neg

theorem integrable_pow_BD {m : Measure ℝ} {C : ℝ} (h : BD m C) (τ : ℝ) (k : ℕ) :
    Integrable (fun y : ℝ => (τ * y) ^ k) m := by
  have := h.finite
  refine Integrable.of_bound (by fun_prop : Continuous fun y : ℝ => (τ * y) ^ k).aestronglyMeasurable
    (|τ| ^ k) ?_
  filter_upwards [h.ae_mem] with y hy
  rw [Real.norm_eq_abs, abs_pow, abs_mul]
  have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (abs_nonneg τ) hy1) k

/-! ### 3. Linearity of the reference fields in the measure -/

theorem rowRef_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB : SRef} {C D : ℝ}
    (hA : μA.OK C) (hB : μB.OK D) (x : ℝ) :
    rowRef (SRef.mix l μA μB) x = (1 - l) * rowRef μA x + l * rowRef μB x := by
  unfold rowRef SRef.mix mixFam
  dsimp only
  simp_rw [integral_mixM hl0 hl1 (integrable_Kt (hA.hP _) _ _ _) (integrable_Kt (hB.hP _) _ _ _),
    integral_mixM hl0 hl1 (integrable_Kt (hA.hN _) _ _ _) (integrable_Kt (hB.hN _) _ _ _)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun τ _ => by ring)

theorem mpos_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB : SRef} {C D : ℝ}
    (hA : μA.OK C) (hB : μB.OK D) (τ : ℝ) :
    mpos (SRef.mix l μA μB) τ = linSeq l (mpos μA τ) (mpos μB τ) := by
  funext n
  unfold mpos SRef.mix mixFam linSeq
  dsimp only
  rw [integral_mixM hl0 hl1 (integrable_pow_BD (hA.hP true) τ _) (integrable_pow_BD (hB.hP true) τ _),
    integral_mixM hl0 hl1 (integrable_pow_BD (hA.hN true) τ _) (integrable_pow_BD (hB.hN true) τ _)]
  ring

theorem mneg_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB : SRef} {C D : ℝ}
    (hA : μA.OK C) (hB : μB.OK D) (τ : ℝ) :
    mneg (SRef.mix l μA μB) τ = linSeq l (mneg μA τ) (mneg μB τ) := by
  funext n
  unfold mneg SRef.mix mixFam linSeq
  dsimp only
  rw [integral_mixM hl0 hl1 (integrable_pow_BD (hA.hP false) τ _) (integrable_pow_BD (hB.hP false) τ _),
    integral_mixM hl0 hl1 (integrable_pow_BD (hA.hN false) τ _) (integrable_pow_BD (hB.hN false) τ _)]
  ring

/-! ### 4. Linearity of the series -/

theorem isGeom_linSeq {τ : ℝ} {c d : ℕ → ℝ} (hc : IsGeom τ c) (hd : IsGeom τ d) (l : ℝ) :
    IsGeom τ (linSeq l c d) :=
  (hc.const_mul (1 - l)).add (hd.const_mul l)

theorem fld_linSeq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c d : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) {x : ℝ} (hx : |x| ≤ 1) (l : ℝ) :
    fld τ (linSeq l c d) x = (1 - l) * fld τ c x + l * fld τ d x := by
  have h := ((hasSum_fld hτ hc hx).mul_left (1 - l)).add ((hasSum_fld hτ hd hx).mul_left l)
  unfold fld
  exact (tsum_congr fun n => by simp only [linSeq]; ring).trans h.tsum_eq

theorem ip_linSeq_right {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c d d' : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) (hd' : IsGeom τ d') (l : ℝ) :
    ip c (linSeq l d d') = (1 - l) * ip c d + l * ip c d' := by
  have h := ((hasSum_ip hτ hc hd).mul_left (1 - l)).add ((hasSum_ip hτ hc hd').mul_left l)
  unfold ip
  exact (tsum_congr fun n => by simp only [linSeq]; ring).trans h.tsum_eq

theorem ip_linSeq_left {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c c' d : ℕ → ℝ} (hc : IsGeom τ c)
    (hc' : IsGeom τ c') (hd : IsGeom τ d) (l : ℝ) :
    ip (linSeq l c c') d = (1 - l) * ip c d + l * ip c' d := by
  have h := ((hasSum_ip hτ hc hd).mul_left (1 - l)).add ((hasSum_ip hτ hc' hd).mul_left l)
  unfold ip
  exact (tsum_congr fun n => by simp only [linSeq]; ring).trans h.tsum_eq

/-- Bilinear expansion of the inner product. -/
theorem ip_linSeq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c c' d d' : ℕ → ℝ} (hc : IsGeom τ c)
    (hc' : IsGeom τ c') (hd : IsGeom τ d) (hd' : IsGeom τ d') (l : ℝ) :
    ip (linSeq l c c') (linSeq l d d') =
      (1 - l) * (1 - l) * ip c d + (1 - l) * l * ip c d' + l * (1 - l) * ip c' d +
        l * l * ip c' d' := by
  rw [ip_linSeq_left hτ hc hc' (isGeom_linSeq hd hd' l), ip_linSeq_right hτ hc hd hd',
    ip_linSeq_right hτ hc' hd hd']
  ring

theorem barrierTrialS_linSeq {u v : ℕ → ℝ} (hu : Summable fun k => |u k|)
    (hv : Summable fun k => |v k|) (l : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (linSeq l u v) x = (1 - l) * barrierTrialS u x + l * barrierTrialS v x := by
  have h := ((barrierTrialS_summable u hu hx).hasSum.mul_left (1 - l)).add
    ((barrierTrialS_summable v hv hx).hasSum.mul_left l)
  unfold barrierTrialS
  exact (tsum_congr fun k => by simp only [linSeq]; ring).trans h.tsum_eq

theorem barrierTrialT_linSeq {u v : ℕ → ℝ} (hu : Summable fun k => |u k|)
    (hv : Summable fun k => |v k|) (l : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT (linSeq l u v) x = (1 - l) * barrierTrialT u x + l * barrierTrialT v x := by
  have h := ((barrierTrialT_summable u hu hx).hasSum.mul_left (1 - l)).add
    ((barrierTrialT_summable v hv hx).hasSum.mul_left l)
  unfold barrierTrialT
  exact (tsum_congr fun k => by simp only [linSeq]; ring).trans h.tsum_eq

theorem denPoly_linSeq (b b' : ℕ → ℝ) (K : ℕ) (g l : ℝ) :
    denPoly (linSeq l b b') K g = (1 - l) * denPoly b K g + l * denPoly b' K g := by
  unfold denPoly linSeq
  have e : ∀ i ∈ Finset.range K, (-g) ^ (i + 1) * ((1 - l) * b (i + 1) + l * b' (i + 1)) /
      ((i + 1 : ℕ) : ℝ) = (1 - l) * ((-g) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ)) +
        l * ((-g) ^ (i + 1) * b' (i + 1) / ((i + 1 : ℕ) : ℝ)) := fun i _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring


/-! ### 5. The interpolated trial -/

/-- **The interpolated trial.**  Linear interpolation, in the weight `l`, of the mass-weighted
data of two trials: the reference measure `μ`, the sequences `v, a, b, R, t, p`, `Sup`, `Cb` and
the spike cost `cs`.  The scale data `ν, e, sp, K, Rf, Cf, θ, η` are those of `DA` (they agree with
those of `DB` under `InterpCompat`); the constant is the problem own constant `c`. -/
def SignedData.interp (DA DB : SignedData) (l c : ℝ) : SignedData where
  ν := DA.ν
  e := DA.e
  sp := DA.sp
  g := DA.g
  v := linSeq l DA.v DB.v
  a := linSeq l DA.a DB.a
  b := linSeq l DA.b DB.b
  K := DA.K
  R := linSeq l DA.R DB.R
  t := linSeq l DA.t DB.t
  μ := SRef.mix l DA.μ DB.μ
  Cb := (1 - l) * DA.Cb + l * DB.Cb
  η := DA.η
  p := linSeq l DA.p DB.p
  Sup := (1 - l) * DA.Sup + l * DB.Sup
  constant := c
  Rf := DA.Rf
  Cf := DA.Cf
  θ := DA.θ
  cs := (1 - l) * DA.cs + l * DB.cs
  kph := DA.kph

/-- Two trials that can be interpolated: they agree on the scale data. -/
structure InterpCompat (DA DB : SignedData) : Prop where
  ν : DB.ν = DA.ν
  e : DB.e = DA.e
  sp : DB.sp = DA.sp
  g : DB.g = DA.g
  K : DB.K = DA.K
  Rf : DB.Rf = DA.Rf
  Cf : DB.Cf = DA.Cf
  θ : DB.θ = DA.θ
  kph : DB.kph = DA.kph
  η : DB.η = DA.η

theorem InterpCompat.τ {DA DB : SignedData} (hc : InterpCompat DA DB) : DB.τ = DA.τ := by
  unfold SignedData.τ; rw [hc.e]

/-- The regularity of a trial that the field linearity needs (all of it is part of the contract
`SignedNearBounds`, except the summability of `a`, which is a hypothesis of the spike lane too). -/
structure SignedRegular (D : SignedData) : Prop where
  he : D.e ∈ Ioo (0 : ℝ) (1 / 8)
  hv : Summable fun j => |D.v j|
  ha : Summable fun j => |D.a j|
  hR : IsGeom D.τ D.R
  ht : IsGeom D.τ D.t
  hμ : D.μ.OK D.Cb
  hC : 0 ≤ D.Cb
  hp : Summable fun j => |D.p j|
  hη0 : 0 ≤ D.η

theorem SignedRegular.tau {D : SignedData} (h : SignedRegular D) : D.τ ∈ Ioo (0 : ℝ) 1 :=
  realEnergyTau_bounds h.he

theorem interp_zero (DA DB : SignedData) (c : ℝ) :
    SignedData.interp DA DB 0 c = { DA with constant := c } := by
  simp [SignedData.interp, linSeq_zero, SRef.mix_zero]

theorem interp_one {DA DB : SignedData} (hc : InterpCompat DA DB) (c : ℝ) :
    SignedData.interp DA DB 1 c = { DB with constant := c } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  simp [SignedData.interp, linSeq_one, SRef.mix_one, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem abs_linSeq_le (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (u v : ℕ → ℝ) (n : ℕ) :
    |linSeq l u v n| ≤ (1 - l) * |u n| + l * |v n| := by
  unfold linSeq
  calc |(1 - l) * u n + l * v n| ≤ |(1 - l) * u n| + |l * v n| := abs_add_le _ _
    _ = (1 - l) * |u n| + l * |v n| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hl0]

theorem summable_abs_linSeq {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {u v : ℕ → ℝ}
    (hu : Summable fun k => |u k|) (hv : Summable fun k => |v k|) :
    Summable fun k => |linSeq l u v k| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => abs_linSeq_le l hl0 hl1 u v n)
    ((hu.mul_left (1 - l)).add (hv.mul_left l))

theorem SignedRegular.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) :
    SignedRegular (SignedData.interp DA DB l c) where
  he := rA.he
  hv := summable_abs_linSeq hl0 hl1 rA.hv rB.hv
  ha := summable_abs_linSeq hl0 hl1 rA.ha rB.ha
  hR := isGeom_linSeq rA.hR (by simpa [hc.τ] using rB.hR) l
  ht := isGeom_linSeq rA.ht (by simpa [hc.τ] using rB.ht) l
  hμ := SRef.OK_mix hl0 hl1 rA.hC rB.hC rA.hμ rB.hμ
  hC := add_nonneg (mul_nonneg (by linarith) rA.hC) (mul_nonneg hl0 rB.hC)
  hp := summable_abs_linSeq hl0 hl1 rA.hp rB.hp
  hη0 := rA.hη0

/-! ### 6. The fields are affine in the weight -/

section Fields

variable {DA DB : SignedData} {l c : ℝ}

theorem abs_neg_tau_mul_le {τ x : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hx : |x| ≤ 1) :
    |-τ * x| ≤ 1 := by
  rw [abs_mul, abs_neg, abs_of_pos hτ.1]
  calc τ * |x| ≤ 1 * 1 := mul_le_mul hτ.2.le hx (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem rowBase_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).rowBase x = (1 - l) * DA.rowBase x + l * DB.rowBase x := by
  obtain ⟨hν, he, hsp, hg, hK, hRf, hCf, hθ, hkph, hη⟩ := hc
  unfold SignedData.rowBase SignedData.τ
  simp only [SignedData.interp, hν, he, hRf, hη]
  rw [barrierTrialS_linSeq rA.hv rB.hv l hx, rowRef_mix hl0 hl1 rA.hμ rB.hμ x,
    barrierTrialT_linSeq rA.hp rB.hp l hx]
  ring

theorem rowBaseM_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rm : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).rowBaseM Rm x =
      (1 - l) * DA.rowBaseM Rm x + l * DB.rowBaseM Rm x := by
  obtain ⟨hν, he, hsp, hg, hK, hRf, hCf, hθ, hkph, hη⟩ := hc
  unfold SignedData.rowBaseM SignedData.τ
  simp only [SignedData.interp, hν, he, hη]
  rw [rowRef_mix hl0 hl1 rA.hμ rB.hμ x, barrierTrialT_linSeq rA.hp rB.hp l hx]
  ring

/-- The negative-species tangent field `κ (mneg μ - t) - R`. -/
theorem fldNeg_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (κ : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    fld (SignedData.interp DA DB l c).τ
        (fun n => κ * (mneg (SignedData.interp DA DB l c).μ (SignedData.interp DA DB l c).τ n -
          (SignedData.interp DA DB l c).t n) - (SignedData.interp DA DB l c).R n) x =
      (1 - l) * fld DA.τ (fun n => κ * (mneg DA.μ DA.τ n - DA.t n) - DA.R n) x +
        l * fld DB.τ (fun n => κ * (mneg DB.μ DB.τ n - DB.t n) - DB.R n) x := by
  have hτ := rA.tau
  have hτB : DB.τ = DA.τ := hc.τ
  rw [hτB]
  have gA : IsGeom DA.τ (fun n => κ * (mneg DA.μ DA.τ n - DA.t n) - DA.R n) :=
    (((isGeom_mneg rA.hμ hτ.1).sub rA.ht).const_mul κ).sub rA.hR
  have gB : IsGeom DA.τ (fun n => κ * (mneg DB.μ DA.τ n - DB.t n) - DB.R n) :=
    (((isGeom_mneg rB.hμ hτ.1).sub (by simpa [hτB] using rB.ht)).const_mul κ).sub
      (by simpa [hτB] using rB.hR)
  have e : (fun n => κ * (mneg (SignedData.interp DA DB l c).μ (SignedData.interp DA DB l c).τ n -
          (SignedData.interp DA DB l c).t n) - (SignedData.interp DA DB l c).R n) =
      linSeq l (fun n => κ * (mneg DA.μ DA.τ n - DA.t n) - DA.R n)
        (fun n => κ * (mneg DB.μ DA.τ n - DB.t n) - DB.R n) := by
    funext n
    show κ * (mneg (SRef.mix l DA.μ DB.μ) DA.τ n - linSeq l DA.t DB.t n) - linSeq l DA.R DB.R n = _
    rw [mneg_mix hl0 hl1 rA.hμ rB.hμ]
    simp only [linSeq]; ring
  rw [e]
  exact fld_linSeq hτ gA gB hx l

/-- The positive-species tangent field. -/
theorem fldPos_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {x : ℝ} (hx : |x| ≤ 1) :
    fld (SignedData.interp DA DB l c).τ
        (fun n => mpos (SignedData.interp DA DB l c).μ (SignedData.interp DA DB l c).τ n +
          (SignedData.interp DA DB l c).R n) x =
      (1 - l) * fld DA.τ (fun n => mpos DA.μ DA.τ n + DA.R n) x +
        l * fld DB.τ (fun n => mpos DB.μ DB.τ n + DB.R n) x := by
  have hτ := rA.tau
  have hτB : DB.τ = DA.τ := hc.τ
  rw [hτB]
  have gA : IsGeom DA.τ (fun n => mpos DA.μ DA.τ n + DA.R n) :=
    (isGeom_mpos rA.hμ hτ.1).add rA.hR
  have gB : IsGeom DA.τ (fun n => mpos DB.μ DA.τ n + DB.R n) :=
    (isGeom_mpos rB.hμ hτ.1).add (by simpa [hτB] using rB.hR)
  have e : (fun n => mpos (SignedData.interp DA DB l c).μ (SignedData.interp DA DB l c).τ n +
          (SignedData.interp DA DB l c).R n) =
      linSeq l (fun n => mpos DA.μ DA.τ n + DA.R n) (fun n => mpos DB.μ DA.τ n + DB.R n) := by
    funext n
    show mpos (SRef.mix l DA.μ DB.μ) DA.τ n + linSeq l DA.R DB.R n = _
    rw [mpos_mix hl0 hl1 rA.hμ rB.hμ]
    simp only [linSeq]; ring
  rw [e]
  exact fld_linSeq hτ gA gB hx l

/-- The near-type tangent field `R - t + (β/2) arcNeg`. -/
theorem fldNear_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (β : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    fld (SignedData.interp DA DB l c).τ
        (fun n => (SignedData.interp DA DB l c).R n - (SignedData.interp DA DB l c).t n +
          β / 2 * arcNeg (SignedData.interp DA DB l c).τ n) x =
      (1 - l) * fld DA.τ (fun n => DA.R n - DA.t n + β / 2 * arcNeg DA.τ n) x +
        l * fld DB.τ (fun n => DB.R n - DB.t n + β / 2 * arcNeg DB.τ n) x := by
  have hτ := rA.tau
  have hτB : DB.τ = DA.τ := hc.τ
  rw [hτB]
  have gA : IsGeom DA.τ (fun n => DA.R n - DA.t n + β / 2 * arcNeg DA.τ n) :=
    (rA.hR.sub rA.ht).add ((isGeom_arcNeg hτ).const_mul _)
  have gB : IsGeom DA.τ (fun n => DB.R n - DB.t n + β / 2 * arcNeg DA.τ n) :=
    ((by simpa [hτB] using rB.hR : IsGeom DA.τ DB.R).sub (by simpa [hτB] using rB.ht)).add
      ((isGeom_arcNeg hτ).const_mul _)
  have e : (fun n => (SignedData.interp DA DB l c).R n - (SignedData.interp DA DB l c).t n +
          β / 2 * arcNeg (SignedData.interp DA DB l c).τ n) =
      linSeq l (fun n => DA.R n - DA.t n + β / 2 * arcNeg DA.τ n)
        (fun n => DB.R n - DB.t n + β / 2 * arcNeg DA.τ n) := by
    funext n
    show linSeq l DA.R DB.R n - linSeq l DA.t DB.t n + β / 2 * arcNeg DA.τ n = _
    simp only [linSeq]; ring
  rw [e]
  exact fld_linSeq hτ gA gB hx l

theorem interp_ν (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).ν = DA.ν := rfl
theorem interp_e (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).e = DA.e := rfl
theorem interp_τ (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).τ = DA.τ := rfl
theorem interp_sp (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).sp = DA.sp := rfl
theorem interp_g (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).g = DA.g := rfl
theorem interp_Sup (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).Sup = (1 - l) * DA.Sup + l * DB.Sup := rfl
theorem interp_K (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).K = DA.K := rfl
theorem interp_θ (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).θ = DA.θ := rfl
theorem interp_cs (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).cs = (1 - l) * DA.cs + l * DB.cs := rfl
theorem interp_Cf (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).Cf = DA.Cf := rfl
theorem interp_Rf (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).Rf = DA.Rf := rfl

theorem SignedRegular.hRτ {DA DB : SignedData} (hc : InterpCompat DA DB) (rB : SignedRegular DB) :
    IsGeom DA.τ DB.R := by simpa [hc.τ] using rB.hR

theorem SignedRegular.htτ {DA DB : SignedData} (hc : InterpCompat DA DB) (rB : SignedRegular DB) :
    IsGeom DA.τ DB.t := by simpa [hc.τ] using rB.ht

/-- The `-2 S_a(-τ x)` trial barrier term is affine. -/
theorem barrierS_a_interp {DA DB : SignedData} {l c : ℝ} (_hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (SignedData.interp DA DB l c).a (-(SignedData.interp DA DB l c).τ * x) =
      (1 - l) * barrierTrialS DA.a (-DA.τ * x) + l * barrierTrialS DB.a (-DA.τ * x) := by
  show barrierTrialS (linSeq l DA.a DB.a) (-DA.τ * x) = _
  exact barrierTrialS_linSeq rA.ha rB.ha l (abs_neg_tau_mul_le rA.tau hx)

theorem denPoly_interp {DA DB : SignedData} {l c : ℝ} (_hc : InterpCompat DA DB) (x : ℝ) :
    denPoly (SignedData.interp DA DB l c).b (SignedData.interp DA DB l c).K x =
      (1 - l) * denPoly DA.b DA.K x + l * denPoly DB.b DA.K x := by
  show denPoly (linSeq l DA.b DB.b) DA.K x = _
  exact denPoly_linSeq _ _ _ _ _

theorem fNeg_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fNeg x = (1 - l) * DA.fNeg x + l * DB.fNeg x := by
  have hτB : DB.τ = DA.τ := hc.τ
  have hνB : DB.ν = DA.ν := hc.ν
  have hηB : DB.η = DA.η := hc.η
  have hηI : (SignedData.interp DA DB l c).η = DA.η := rfl
  unfold SignedData.fNeg
  rw [rowBase_interp hl0 hl1 hc rA rB hx, hηI, fldNeg_interp hl0 hl1 hc rA rB _ hx,
    barrierS_a_interp hc rA rB hx, interp_ν, interp_τ, hτB, hνB, hηB]
  ring

theorem fNegM_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rm : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fNegM Rm x =
      (1 - l) * DA.fNegM Rm x + l * DB.fNegM Rm x := by
  have hτB : DB.τ = DA.τ := hc.τ
  have hνB : DB.ν = DA.ν := hc.ν
  have hηB : DB.η = DA.η := hc.η
  have hηI : (SignedData.interp DA DB l c).η = DA.η := rfl
  unfold SignedData.fNegM
  rw [rowBaseM_interp hl0 hl1 hc rA rB Rm hx, hηI, fldNeg_interp hl0 hl1 hc rA rB _ hx,
    barrierS_a_interp hc rA rB hx, interp_ν, interp_τ, hτB, hνB, hηB]
  ring

theorem fPos_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fPos x = (1 - l) * DA.fPos x + l * DB.fPos x := by
  have hτB : DB.τ = DA.τ := hc.τ
  have hνB : DB.ν = DA.ν := hc.ν
  have hKB : DB.K = DA.K := hc.K
  have hspB : DB.sp = DA.sp := hc.sp
  unfold SignedData.fPos
  rw [rowBase_interp hl0 hl1 hc rA rB hx, fldPos_interp hl0 hl1 hc rA rB hx,
    barrierS_a_interp hc rA rB hx, denPoly_interp hc, interp_ν, interp_sp, interp_Sup, hτB, hνB,
    hKB, hspB]
  ring

theorem fPosS_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fPosS x = (1 - l) * DA.fPosS x + l * DB.fPosS x := by
  unfold SignedData.fPosS
  rw [fPos_interp hl0 hl1 hc rA rB hx, interp_cs, interp_θ, hc.θ]
  ring

theorem fPosM_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rm : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fPosM Rm x =
      (1 - l) * DA.fPosM Rm x + l * DB.fPosM Rm x := by
  have hτB : DB.τ = DA.τ := hc.τ
  have hνB : DB.ν = DA.ν := hc.ν
  have hKB : DB.K = DA.K := hc.K
  have hspB : DB.sp = DA.sp := hc.sp
  unfold SignedData.fPosM
  rw [rowBaseM_interp hl0 hl1 hc rA rB Rm hx, fldPos_interp hl0 hl1 hc rA rB hx,
    barrierS_a_interp hc rA rB hx, denPoly_interp hc, interp_ν, interp_sp, interp_Sup, hτB, hνB,
    hKB, hspB]
  ring

theorem fPosMS_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rm : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fPosMS Rm x =
      (1 - l) * DA.fPosMS Rm x + l * DB.fPosMS Rm x := by
  unfold SignedData.fPosMS
  rw [fPosM_interp hl0 hl1 hc rA rB Rm hx, interp_cs, interp_θ, hc.θ]
  ring

theorem fPosMR_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rm : ℝ → ℝ) (rc α : ℝ) {x : ℝ}
    (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fPosMR Rm rc α x =
      (1 - l) * DA.fPosMR Rm rc α x + l * DB.fPosMR Rm rc α x := by
  unfold SignedData.fPosMR
  rw [fPosMS_interp hl0 hl1 hc rA rB Rm hx]
  ring

theorem fCol_interp (_hl0 : 0 ≤ l) (_hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) {s : ℝ} (hs : |s| ≤ 1) :
    (SignedData.interp DA DB l c).fCol s = (1 - l) * DA.fCol s + l * DB.fCol s := by
  unfold SignedData.fCol
  have hT : barrierTrialT (SignedData.interp DA DB l c).v s =
      (1 - l) * barrierTrialT DA.v s + l * barrierTrialT DB.v s :=
    barrierTrialT_linSeq rA.hv rB.hv l hs
  rw [hT, interp_Cf, interp_ν, hc.Cf, hc.ν]
  ring

/-- The arcsine-compensation constant is affine. -/
theorem phConst_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) :
    (SignedData.interp DA DB l c).phConst = (1 - l) * DA.phConst + l * DB.phConst := by
  have hτ := rA.tau
  have hτB : DB.τ = DA.τ := hc.τ
  have hηB : DB.η = DA.η := hc.η
  unfold SignedData.phConst
  rw [hτB, hηB]
  have gA1 : IsGeom DA.τ (fun n => mneg DA.μ DA.τ n - DA.t n) :=
    (isGeom_mneg rA.hμ hτ.1).sub rA.ht
  have gB1 : IsGeom DA.τ (fun n => mneg DB.μ DA.τ n - DB.t n) :=
    (isGeom_mneg rB.hμ hτ.1).sub (SignedRegular.htτ hc rB)
  have e1 : (fun n => mneg (SignedData.interp DA DB l c).μ (SignedData.interp DA DB l c).τ n -
      (SignedData.interp DA DB l c).t n) =
      linSeq l (fun n => mneg DA.μ DA.τ n - DA.t n) (fun n => mneg DB.μ DA.τ n - DB.t n) := by
    funext n
    show mneg (SRef.mix l DA.μ DB.μ) DA.τ n - linSeq l DA.t DB.t n = _
    rw [mneg_mix hl0 hl1 rA.hμ rB.hμ]
    simp only [linSeq]; ring
  rw [e1]
  show (1 - DA.η) * ip (linSeq l _ _) (arcNeg DA.τ) = _
  rw [ip_linSeq_left hτ gA1 gB1 (isGeom_arcNeg hτ) l]
  ring

theorem fNearM_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rn : ℝ → ℝ) (α β : ℝ) {x : ℝ}
    (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fNearM Rn α β x =
      (1 - l) * DA.fNearM Rn α β x + l * DB.fNearM Rn α β x := by
  have hτB : DB.τ = DA.τ := hc.τ
  have hνB : DB.ν = DA.ν := hc.ν
  have hKB : DB.K = DA.K := hc.K
  have hspB : DB.sp = DA.sp := hc.sp
  have hηB : DB.η = DA.η := hc.η
  have hηI : (SignedData.interp DA DB l c).η = DA.η := rfl
  unfold SignedData.fNearM
  rw [fldNear_interp hl0 hl1 hc rA rB β hx, phConst_interp hl0 hl1 hc rA rB,
    barrierS_a_interp hc rA rB hx, denPoly_interp hc, hηI, interp_ν, interp_τ, interp_sp, hτB,
    hνB, hKB, hspB, hηB, interp_Sup]
  ring

theorem fNearMS_interp (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hc : InterpCompat DA DB)
    (rA : SignedRegular DA) (rB : SignedRegular DB) (Rn : ℝ → ℝ) (α β : ℝ) {x : ℝ}
    (hx : |x| ≤ 1) :
    (SignedData.interp DA DB l c).fNearMS Rn α β x =
      (1 - l) * DA.fNearMS Rn α β x + l * DB.fNearMS Rn α β x := by
  unfold SignedData.fNearMS
  rw [fNearM_interp hl0 hl1 hc rA rB Rn α β hx, interp_cs, interp_θ, hc.θ]
  ring

end Fields


/-! ### 7. Quadratic polynomials in the weight -/

/-- `f` agrees on `[0, 1]` with a polynomial of degree at most `2`. -/
def IsQuadOn (f : ℝ → ℝ) : Prop :=
  ∃ p0 p1 p2 : ℝ, ∀ l ∈ Icc (0 : ℝ) 1, f l = p0 + p1 * l + p2 * l ^ 2

theorem IsQuadOn.const (c : ℝ) : IsQuadOn (fun _ => c) := ⟨c, 0, 0, fun l _ => by ring⟩

theorem IsQuadOn.add {f g : ℝ → ℝ} (hf : IsQuadOn f) (hg : IsQuadOn g) :
    IsQuadOn (fun l => f l + g l) := by
  obtain ⟨a0, a1, a2, ha⟩ := hf
  obtain ⟨b0, b1, b2, hb⟩ := hg
  exact ⟨a0 + b0, a1 + b1, a2 + b2, fun l hl => by
    show f l + g l = _
    rw [ha l hl, hb l hl]; ring⟩

theorem IsQuadOn.const_mul (c : ℝ) {f : ℝ → ℝ} (hf : IsQuadOn f) : IsQuadOn (fun l => c * f l) := by
  obtain ⟨a0, a1, a2, ha⟩ := hf
  exact ⟨c * a0, c * a1, c * a2, fun l hl => by
    show c * f l = _
    rw [ha l hl]; ring⟩

theorem IsQuadOn.congr {f g : ℝ → ℝ} (h : ∀ l ∈ Icc (0 : ℝ) 1, f l = g l) (hg : IsQuadOn g) :
    IsQuadOn f := by
  obtain ⟨a0, a1, a2, ha⟩ := hg
  exact ⟨a0, a1, a2, fun l hl => by rw [h l hl, ha l hl]⟩

/-- The bilinear expansion shape `(1-l)² A + (1-l) l B + l (1-l) C + l² D`. -/
theorem IsQuadOn.four (A B C D : ℝ) :
    IsQuadOn (fun l => (1 - l) * (1 - l) * A + (1 - l) * l * B + l * (1 - l) * C + l * l * D) :=
  ⟨A, -2 * A + B + C, A - B - C + D, fun l _ => by ring⟩

theorem IsQuadOn.affine (a b : ℝ) : IsQuadOn (fun l => (1 - l) * a + l * b) :=
  ⟨a, b - a, 0, fun l _ => by ring⟩

theorem IsQuadOn.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IsQuadOn (f i)) : IsQuadOn (fun l => ∑ i ∈ s, f i l) := by
  have h' : ∀ i ∈ s, ∃ p0 p1 p2 : ℝ, ∀ l ∈ Icc (0 : ℝ) 1,
      f i l = p0 + p1 * l + p2 * l ^ 2 := h
  choose! p0 p1 p2 hp using h'
  refine ⟨∑ i ∈ s, p0 i, ∑ i ∈ s, p1 i, ∑ i ∈ s, p2 i, fun l hl => ?_⟩
  show ∑ i ∈ s, f i l = _
  rw [Finset.sum_congr rfl (fun i hi => hp i hi l hl)]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]

theorem isQuadOn_aff_sq (w x y : ℝ) : IsQuadOn (fun l => w * ((1 - l) * x + l * y) ^ 2) :=
  ⟨w * x ^ 2, w * (2 * x * y - 2 * x ^ 2), w * (x - y) ^ 2, fun l _ => by ring⟩

/-- A function that is a quadratic on `[0,1]` is its chord minus `l (1 - l)` times the second
difference. -/
theorem IsQuadOn.chord {g : ℝ → ℝ} (hg : IsQuadOn g) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    g l = (1 - l) * g 0 + l * g 1 - l * (1 - l) * (2 * (g 0 + g 1) - 4 * g (1 / 2)) := by
  obtain ⟨q0, q1, q2, h⟩ := hg
  have h0 := h 0 ⟨le_rfl, zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one, le_rfl⟩
  have h2 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [h l hl, h0, h1, h2]
  ring

/-! ### 8. Bilinear expansions of the quadratic constants -/

theorem summable_mul_bdd {x y : ℕ → ℝ} {M : ℝ} (hx : ∀ n, |x n| ≤ M)
    (hy : Summable fun n => |y n|) : Summable fun n => x n * y n := by
  refine Summable.of_norm_bounded (hy.mul_left M) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hx n) (abs_nonneg _)

theorem tsum_linSeq_mul {x x' y y' : ℕ → ℝ} (l : ℝ) (h1 : Summable fun n => x n * y n)
    (h2 : Summable fun n => x n * y' n) (h3 : Summable fun n => x' n * y n)
    (h4 : Summable fun n => x' n * y' n) :
    ∑' n, linSeq l x x' n * linSeq l y y' n =
      (1 - l) * (1 - l) * ∑' n, x n * y n + (1 - l) * l * ∑' n, x n * y' n +
        l * (1 - l) * ∑' n, x' n * y n + l * l * ∑' n, x' n * y' n := by
  have h := (((h1.hasSum.mul_left ((1 - l) * (1 - l))).add
    (h2.hasSum.mul_left ((1 - l) * l))).add (h3.hasSum.mul_left (l * (1 - l)))).add
    (h4.hasSum.mul_left (l * l))
  exact (tsum_congr fun n => by simp only [linSeq]; ring).trans h.tsum_eq

/-- `u (n+1) / (n+1)`. -/
def wsh (u : ℕ → ℝ) : ℕ → ℝ := fun n => u (n + 1) / ((n + 1 : ℕ) : ℝ)

/-- `u (n+1)`. -/
def sh (u : ℕ → ℝ) : ℕ → ℝ := fun n => u (n + 1)

theorem wsh_linSeq (l : ℝ) (u v : ℕ → ℝ) : wsh (linSeq l u v) = linSeq l (wsh u) (wsh v) := by
  funext n; simp only [wsh, linSeq]; ring

theorem sh_linSeq (l : ℝ) (u v : ℕ → ℝ) : sh (linSeq l u v) = linSeq l (sh u) (sh v) := by
  funext n; simp only [sh, linSeq]

theorem abs_le_tsum_abs {u : ℕ → ℝ} (hu : Summable fun k => |u k|) (k : ℕ) :
    |u k| ≤ ∑' j, |u j| :=
  le_hasSum hu.hasSum k (fun _ _ => abs_nonneg _)

theorem abs_wsh_le {u : ℕ → ℝ} (hu : Summable fun k => |u k|) (n : ℕ) :
    |wsh u n| ≤ ∑' j, |u j| := by
  unfold wsh
  have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
  exact (div_le_self (abs_nonneg _) hk).trans (abs_le_tsum_abs hu (n + 1))

theorem summable_abs_sh {u : ℕ → ℝ} (hu : Summable fun k => |u k|) :
    Summable fun n => |sh u n| := (summable_nat_add_iff 1).mpr hu

/-- `barrierTrialNormSq` as a pairing. -/
theorem nsq_eq_tsum (u : ℕ → ℝ) :
    barrierTrialNormSq u = ∑' n, wsh u n * sh u n := by
  unfold barrierTrialNormSq wsh sh
  exact tsum_congr fun n => by ring

/-- Bilinear expansion of `barrierTrialNormSq` along the segment. -/
theorem nsq_linSeq {u v : ℕ → ℝ} (hu : Summable fun k => |u k|) (hv : Summable fun k => |v k|)
    (l : ℝ) :
    barrierTrialNormSq (linSeq l u v) =
      (1 - l) * (1 - l) * ∑' n, wsh u n * sh u n + (1 - l) * l * ∑' n, wsh u n * sh v n +
        l * (1 - l) * ∑' n, wsh v n * sh u n + l * l * ∑' n, wsh v n * sh v n := by
  rw [nsq_eq_tsum, wsh_linSeq, sh_linSeq]
  exact tsum_linSeq_mul l (summable_mul_bdd (abs_wsh_le hu) (summable_abs_sh hu))
    (summable_mul_bdd (abs_wsh_le hu) (summable_abs_sh hv))
    (summable_mul_bdd (abs_wsh_le hv) (summable_abs_sh hu))
    (summable_mul_bdd (abs_wsh_le hv) (summable_abs_sh hv))

theorem isQuadOn_nsq {u v : ℕ → ℝ} (hu : Summable fun k => |u k|)
    (hv : Summable fun k => |v k|) : IsQuadOn (fun l => barrierTrialNormSq (linSeq l u v)) :=
  (IsQuadOn.four _ _ _ _).congr (fun l _ => nsq_linSeq hu hv l)

/-- `refTilt R (n + 1)`. -/
def rt (R : ℕ → ℝ) : ℕ → ℝ := fun n => refTilt R (n + 1)

theorem rt_linSeq (l : ℝ) (R R' : ℕ → ℝ) : rt (linSeq l R R') = linSeq l (rt R) (rt R') := by
  funext n
  simp only [rt, refTilt, linSeq, Nat.add_sub_cancel]
  ring

theorem abs_rt_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {R : ℕ → ℝ} (hR : IsGeom τ R) :
    ∃ M, ∀ n, |rt R n| ≤ M := by
  obtain ⟨C, hC⟩ := hR
  refine ⟨|C|, fun n => ?_⟩
  simp only [rt, refTilt, Nat.add_sub_cancel]
  have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  have hkp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  rw [abs_div, abs_of_pos hkp, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hp : τ ^ (n + 1) ≤ 1 := pow_le_one₀ hτ.1.le hτ.2.le
  calc |R n| / ((n + 1 : ℕ) : ℝ) ≤ |R n| := div_le_self (abs_nonneg _) hk
    _ ≤ C * τ ^ (n + 1) := hC n
    _ ≤ |C| * τ ^ (n + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hτ.1.le _)
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = |C| := mul_one _

/-- The pairing `ra` of the reference tilt with the trial `a`, along the segment. -/
theorem ra_eq_tsum (D : SignedData) : D.ra = ∑' n, rt D.R n * sh D.a n := rfl

theorem isQuadOn_ra {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {R R' a a' : ℕ → ℝ} (hR : IsGeom τ R)
    (hR' : IsGeom τ R') (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) :
    IsQuadOn (fun l => ∑' n, rt (linSeq l R R') n * sh (linSeq l a a') n) := by
  obtain ⟨M, hM⟩ := abs_rt_le hτ hR
  obtain ⟨M', hM'⟩ := abs_rt_le hτ hR'
  refine (IsQuadOn.four (∑' n, rt R n * sh a n) (∑' n, rt R n * sh a' n)
    (∑' n, rt R' n * sh a n) (∑' n, rt R' n * sh a' n)).congr (fun l _ => ?_)
  rw [rt_linSeq, sh_linSeq]
  exact tsum_linSeq_mul l (summable_mul_bdd hM (summable_abs_sh ha))
    (summable_mul_bdd hM (summable_abs_sh ha')) (summable_mul_bdd hM' (summable_abs_sh ha))
    (summable_mul_bdd hM' (summable_abs_sh ha'))

theorem isQuadOn_ip_self {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c c' : ℕ → ℝ} (hc : IsGeom τ c)
    (hc' : IsGeom τ c') : IsQuadOn (fun l => ip (linSeq l c c') (linSeq l c c')) :=
  (IsQuadOn.four _ _ _ _).congr (fun l _ => ip_linSeq hτ hc hc' hc hc' l)

/-! ### 9. The reference energy is quadratic along the segment -/

/-- The bilinear form of the reference energy for two nonnegative families. -/
def refBilM (μ ν : Bool → Measure ℝ) : ℝ := pairI μ ν Kt

/-- The bilinear form of the reference energy for two signed references. -/
def refBil (μ ν : SRef) : ℝ :=
  refBilM μ.P ν.P - refBilM μ.P ν.N - refBilM μ.N ν.P + refBilM μ.N ν.N

theorem refEnergy_eq_refBil (μ : SRef) : refEnergy μ = refBil μ μ := rfl

theorem integrable_Kt_prod {m n : Measure ℝ} {C : ℝ} (hm : BD m C) (hn : BD n C) (hC : 0 ≤ C)
    (s t : Bool) : Integrable (fun p : ℝ × ℝ => Kt s t p.1 p.2) (m.prod n) := by
  have h1 : Integrable (fun p : ℝ × ℝ => Ktil (1 / 2) s t p.1 p.2) (m.prod n) :=
    intK_prod hm hn (measurable_Ktil (1 / 2) s t) (c := |Real.log (1 - 1 / 2)| + 1)
      (fun x y hx hy => Ktil_bound (by norm_num) (by norm_num) s t hx hy)
  have h2 : Integrable (fun p : ℝ × ℝ => Dk (1 / 2) s t p.1 p.2) (m.prod n) := by
    unfold Dk
    by_cases hst : s = t
    · simp only [hst, ite_true]
      exact D1_prod hm hn hC (by norm_num) (by norm_num)
    · simp only [hst, ite_false]
      exact D2_prod hm hn (by norm_num) (by norm_num)
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun p => ?_)
  show Ktil (1 / 2) s t p.1 p.2 + Dk (1 / 2) s t p.1 p.2 = Kt s t p.1 p.2
  exact (Kt_eq (1 / 2) s t p.1 p.2).symm

theorem iterInt_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {m n m' n' : Measure ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hm : BD m C) (hn : BD n C) (hm' : BD m' C) (hn' : BD n' C) (s t : Bool) :
    ∫ x, ∫ y, Kt s t x y ∂(mixM l m' n') ∂(mixM l m n) =
      (1 - l) * (1 - l) * (∫ x, ∫ y, Kt s t x y ∂m' ∂m) +
        (1 - l) * l * (∫ x, ∫ y, Kt s t x y ∂n' ∂m) +
        l * (1 - l) * (∫ x, ∫ y, Kt s t x y ∂m' ∂n) + l * l * (∫ x, ∫ y, Kt s t x y ∂n' ∂n) := by
  have hin : ∀ x, ∫ y, Kt s t x y ∂(mixM l m' n') =
      (1 - l) * ∫ y, Kt s t x y ∂m' + l * ∫ y, Kt s t x y ∂n' := fun x =>
    integral_mixM hl0 hl1 (integrable_Kt hm' s t x) (integrable_Kt hn' s t x)
  have hI : ∀ {p q : Measure ℝ}, BD p C → BD q C →
      Integrable (fun x => ∫ y, Kt s t x y ∂q) p := by
    intro p q hp hq
    have := hp.finite
    have := hq.finite
    exact (integrable_Kt_prod hp hq hC s t).integral_prod_left
  simp_rw [hin]
  have hF : ∀ {p : Measure ℝ}, BD p C → Integrable
      (fun x => (1 - l) * ∫ y, Kt s t x y ∂m' + l * ∫ y, Kt s t x y ∂n') p :=
    fun hp => ((hI hp hm').const_mul (1 - l)).add ((hI hp hn').const_mul l)
  rw [integral_mixM hl0 hl1 (hF hm) (hF hn), integral_add ((hI hm hm').const_mul (1 - l))
    ((hI hm hn').const_mul l), integral_add ((hI hn hm').const_mul (1 - l))
    ((hI hn hn').const_mul l), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

theorem refBilM_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB νA νB : Bool → Measure ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h1 : ∀ τ, BD (μA τ) C) (h2 : ∀ τ, BD (μB τ) C) (h3 : ∀ τ, BD (νA τ) C)
    (h4 : ∀ τ, BD (νB τ) C) :
    refBilM (mixFam l μA μB) (mixFam l νA νB) =
      (1 - l) * (1 - l) * refBilM μA νA + (1 - l) * l * refBilM μA νB +
        l * (1 - l) * refBilM μB νA + l * l * refBilM μB νB := by
  have key : ∀ τ τ' : Bool, ∫ x, ∫ y, Kt τ τ' x y ∂(mixM l (νA τ') (νB τ')) ∂(mixM l (μA τ) (μB τ)) =
      (1 - l) * (1 - l) * (∫ x, ∫ y, Kt τ τ' x y ∂(νA τ') ∂(μA τ)) +
        (1 - l) * l * (∫ x, ∫ y, Kt τ τ' x y ∂(νB τ') ∂(μA τ)) +
        l * (1 - l) * (∫ x, ∫ y, Kt τ τ' x y ∂(νA τ') ∂(μB τ)) +
        l * l * (∫ x, ∫ y, Kt τ τ' x y ∂(νB τ') ∂(μB τ)) := fun τ τ' =>
    iterInt_mix hl0 hl1 hC (h1 τ) (h2 τ) (h3 τ') (h4 τ') τ τ'
  unfold refBilM pairI mixFam
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem refBil_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB νA νB : SRef} {C : ℝ}
    (hC : 0 ≤ C) (h1 : μA.OK C) (h2 : μB.OK C) (h3 : νA.OK C) (h4 : νB.OK C) :
    refBil (SRef.mix l μA μB) (SRef.mix l νA νB) =
      (1 - l) * (1 - l) * refBil μA νA + (1 - l) * l * refBil μA νB +
        l * (1 - l) * refBil μB νA + l * l * refBil μB νB := by
  unfold refBil SRef.mix
  dsimp only
  rw [refBilM_mix hl0 hl1 hC h1.hP h2.hP h3.hP h4.hP, refBilM_mix hl0 hl1 hC h1.hP h2.hP h3.hN h4.hN,
    refBilM_mix hl0 hl1 hC h1.hN h2.hN h3.hP h4.hP, refBilM_mix hl0 hl1 hC h1.hN h2.hN h3.hN h4.hN]
  ring

theorem isQuadOn_refEnergy {μA μB : SRef} {C : ℝ} (hC : 0 ≤ C)
    (h1 : μA.OK C) (h2 : μB.OK C) :
    IsQuadOn (fun l => refEnergy (SRef.mix l μA μB)) := by
  refine (IsQuadOn.four (refBil μA μA) (refBil μA μB) (refBil μB μA) (refBil μB μB)).congr
    (fun l hl => ?_)
  rw [refEnergy_eq_refBil]
  exact refBil_mix hl.1 hl.2 hC h1 h2 h1 h2


/-! ### 10. The constant `constTotal` along the segment -/

theorem interp_v (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).v = linSeq l DA.v DB.v := rfl
theorem interp_a (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).a = linSeq l DA.a DB.a := rfl
theorem interp_R (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).R = linSeq l DA.R DB.R := rfl
theorem interp_t (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).t = linSeq l DA.t DB.t := rfl
theorem interp_b (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).b = linSeq l DA.b DB.b := rfl
theorem interp_μ (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).μ = SRef.mix l DA.μ DB.μ := rfl
theorem interp_Cb (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).Cb = (1 - l) * DA.Cb + l * DB.Cb := rfl
theorem interp_constant (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).constant = c := rfl

theorem interp_η (DA DB : SignedData) (l c : ℝ) : (SignedData.interp DA DB l c).η = DA.η := rfl

theorem interp_p (DA DB : SignedData) (l c : ℝ) :
    (SignedData.interp DA DB l c).p = linSeq l DA.p DB.p := rfl

/-- The convex part of the constant: the terms `4 e (Σ|v| + Σ|a|)` and the damping
`4 η e Σ|p|` of the `η`-share. -/
def convPart (D : SignedData) : ℝ :=
  4 * D.e * ((∑' j, |D.v j|) + ∑' k, |D.a k|) + 4 * D.η * D.e * ∑' j, |D.p j|

/-- The part of `constTotal` that is a quadratic form in the data: everything except the problem
constant and the convex part. -/
def restQ (D : SignedData) (p : ℕ) : ℝ :=
  -((p : ℝ) / D.ν) ^ 2 * Real.log 2 + barrierTrialNormSq D.v / 2 + pinZeroError D.ν D.e +
    D.eD7 ((p : ℝ) / D.ν) + (1 - D.η) * refEnergy D.μ + 2 * D.η * barrierTrialNormSq D.p -
    D.η * ((p : ℝ) / D.ν) ^ 2 * Real.log 2 +
    D.η * ((Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / D.ν + 4 * D.e) + D.hadErr +
    2 * (barrierTrialNormSq D.a - ((D.g : ℝ) / D.ν) * D.Sup - D.ra +
        ((Real.log 2 - 2 * Real.log (1 - realEnergyTau D.e ^ 2)) / (2 * D.ν) + 2 * D.e)) +
    ((D.sp : ℝ) / D.ν) ^ 2 * (∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
    2 * ((D.sp : ℝ) / D.ν ^ 2) * (∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2) + D.Kq

theorem constTotal_eq (D : SignedData) (p : ℕ) :
    D.constTotal p = D.constant + restQ D p + convPart D := by
  unfold SignedData.constTotal SignedData.numDenRef SignedData.etaErr trialPairError restQ
    convPart
  ring

/-- The second difference of the quadratic part of the constant along the segment (it is the
coefficient of `l²`; `AA - 2 AB + BB` of the three bilinear blocks). -/
def curvQ (DA DB : SignedData) (p : ℕ) : ℝ :=
  2 * (restQ DA p + restQ DB p) - 4 * restQ (SignedData.interp DA DB (1 / 2) 0) p

theorem eD7_interp {DA DB : SignedData} (hc : InterpCompat DA DB) (l c W : ℝ) :
    (SignedData.interp DA DB l c).eD7 W = (1 - l) * DA.eD7 W + l * DB.eD7 W := by
  have hτB : DB.τ = DA.τ := hc.τ
  unfold SignedData.eD7
  rw [interp_η, interp_τ, interp_Cb, hτB, hc.η]
  ring

theorem isQuadOn_sumsq (K : ℕ) (b b' : ℕ → ℝ) (w : ℕ → ℝ) :
    IsQuadOn (fun l => ∑ i ∈ Finset.range K, w i * linSeq l b b' (i + 1) ^ 2) :=
  IsQuadOn.sum _ (fun i _ => (isQuadOn_aff_sq (w i) (b (i + 1)) (b' (i + 1))).congr
    (fun _ _ => rfl))

theorem isQuadOn_denRef (DA DB : SignedData) (c : ℝ) :
    IsQuadOn (fun l => ((DA.sp : ℝ) / DA.ν) ^ 2 * (∑ i ∈ Finset.range DA.K,
        2 * (SignedData.interp DA DB l c).b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      2 * ((DA.sp : ℝ) / DA.ν ^ 2) * (∑ i ∈ Finset.range DA.K,
        (SignedData.interp DA DB l c).b (i + 1) ^ 2)) := by
  have h1 : IsQuadOn (fun l => ∑ i ∈ Finset.range DA.K,
      2 * linSeq l DA.b DB.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) :=
    (isQuadOn_sumsq DA.K DA.b DB.b (fun i => 2 / ((i + 1 : ℕ) : ℝ))).congr
      (fun l _ => Finset.sum_congr rfl (fun i _ => by ring))
  have h2 : IsQuadOn (fun l => ∑ i ∈ Finset.range DA.K, linSeq l DA.b DB.b (i + 1) ^ 2) :=
    (isQuadOn_sumsq DA.K DA.b DB.b (fun _ => 1)).congr
      (fun l _ => Finset.sum_congr rfl (fun i _ => by ring))
  refine IsQuadOn.congr (g := fun l =>
      ((DA.sp : ℝ) / DA.ν) ^ 2 * (∑ i ∈ Finset.range DA.K,
        2 * linSeq l DA.b DB.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      2 * ((DA.sp : ℝ) / DA.ν ^ 2) * (∑ i ∈ Finset.range DA.K,
        linSeq l DA.b DB.b (i + 1) ^ 2)) (fun l _ => ?_) ?_
  · rw [interp_b]
  · exact (h1.const_mul _).add (h2.const_mul _)

theorem isQuadOn_Kq {DA DB : SignedData} (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (c : ℝ) :
    IsQuadOn (fun l => (SignedData.interp DA DB l c).Kq) := by
  have hτ := rA.tau
  have q1 := isQuadOn_ip_self hτ rA.hR (SignedRegular.hRτ hc rB)
  have q3 := isQuadOn_ip_self hτ rA.ht (SignedRegular.htτ hc rB)
  have gp1 : IsGeom DA.τ (mpos DA.μ DA.τ) := isGeom_mpos rA.hμ hτ.1
  have gp2 : IsGeom DA.τ (mpos DB.μ DA.τ) := isGeom_mpos rB.hμ hτ.1
  have gn1 : IsGeom DA.τ (mneg DA.μ DA.τ) := isGeom_mneg rA.hμ hτ.1
  have gn2 : IsGeom DA.τ (mneg DB.μ DA.τ) := isGeom_mneg rB.hμ hτ.1
  have q2 : IsQuadOn (fun l => ip (mpos (SRef.mix l DA.μ DB.μ) DA.τ)
      (mpos (SRef.mix l DA.μ DB.μ) DA.τ)) :=
    (isQuadOn_ip_self hτ gp1 gp2).congr (fun l hl => by
      rw [mpos_mix hl.1 hl.2 rA.hμ rB.hμ])
  have q4 : IsQuadOn (fun l => ip (mneg (SRef.mix l DA.μ DB.μ) DA.τ)
      (mneg (SRef.mix l DA.μ DB.μ) DA.τ)) :=
    (isQuadOn_ip_self hτ gn1 gn2).congr (fun l hl => by
      rw [mneg_mix hl.1 hl.2 rA.hμ rB.hμ])
  refine IsQuadOn.congr (g := fun l =>
      (1 / 2) * ip (linSeq l DA.R DB.R) (linSeq l DA.R DB.R) +
      (-(1 / 2)) * ip (mpos (SRef.mix l DA.μ DB.μ) DA.τ) (mpos (SRef.mix l DA.μ DB.μ) DA.τ) +
      (1 - DA.η) * ip (linSeq l DA.t DB.t) (linSeq l DA.t DB.t) +
      (-(1 - DA.η)) * ip (mneg (SRef.mix l DA.μ DB.μ) DA.τ) (mneg (SRef.mix l DA.μ DB.μ) DA.τ))
    (fun l _ => ?_) ?_
  · unfold SignedData.Kq
    rw [interp_R, interp_t, interp_μ, interp_τ, interp_η]
    ring
  · exact (((q1.const_mul (1 / 2)).add (q2.const_mul (-(1 / 2)))).add
      (q3.const_mul (1 - DA.η))).add (q4.const_mul (-(1 - DA.η)))

theorem isQuadOn_restQ {DA DB : SignedData} (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (c : ℝ) (p : ℕ) :
    IsQuadOn (fun l => restQ (SignedData.interp DA DB l c) p) := by
  have hτ := rA.tau
  have hC : 0 ≤ max DA.Cb DB.Cb := rA.hC.trans (le_max_left _ _)
  have hmu : IsQuadOn (fun l => refEnergy (SRef.mix l DA.μ DB.μ)) :=
    isQuadOn_refEnergy hC (rA.hμ.mono (le_max_left _ _)) (rB.hμ.mono (le_max_right _ _))
  have hE : IsQuadOn (fun l => (SignedData.interp DA DB l c).eD7 ((p : ℝ) / DA.ν)) :=
    (IsQuadOn.affine (DA.eD7 ((p : ℝ) / DA.ν)) (DB.eD7 ((p : ℝ) / DA.ν))).congr
      (fun l _ => eD7_interp hc l c _)
  have hv := isQuadOn_nsq rA.hv rB.hv
  have ha := isQuadOn_nsq rA.ha rB.ha
  have hpp := isQuadOn_nsq rA.hp rB.hp
  have hra : IsQuadOn (fun l => (SignedData.interp DA DB l c).ra) :=
    isQuadOn_ra hτ rA.hR (SignedRegular.hRτ hc rB) rA.ha rB.ha
  have hden := isQuadOn_denRef DA DB c
  have hKq := isQuadOn_Kq hc rA rB c
  have hS := IsQuadOn.affine DA.Sup DB.Sup
  refine IsQuadOn.congr (g := fun l =>
      (-((p : ℝ) / DA.ν) ^ 2 * Real.log 2 + pinZeroError DA.ν DA.e -
        DA.η * ((p : ℝ) / DA.ν) ^ 2 * Real.log 2 +
        DA.η * ((Real.log 2 - 2 * Real.log (1 - DA.τ ^ 2)) / DA.ν + 4 * DA.e) + DA.hadErr +
        2 * ((Real.log 2 - 2 * Real.log (1 - realEnergyTau DA.e ^ 2)) / (2 * DA.ν) + 2 * DA.e)) +
      (1 / 2) * barrierTrialNormSq (linSeq l DA.v DB.v) +
      (SignedData.interp DA DB l c).eD7 ((p : ℝ) / DA.ν) +
      (1 - DA.η) * refEnergy (SRef.mix l DA.μ DB.μ) +
      (2 * DA.η) * barrierTrialNormSq (linSeq l DA.p DB.p) +
      2 * barrierTrialNormSq (linSeq l DA.a DB.a) +
      (-(2 * ((DA.g : ℝ) / DA.ν))) * ((1 - l) * DA.Sup + l * DB.Sup) +
      (-2) * (SignedData.interp DA DB l c).ra +
      (((DA.sp : ℝ) / DA.ν) ^ 2 * (∑ i ∈ Finset.range DA.K,
        2 * (SignedData.interp DA DB l c).b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      2 * ((DA.sp : ℝ) / DA.ν ^ 2) * (∑ i ∈ Finset.range DA.K,
        (SignedData.interp DA DB l c).b (i + 1) ^ 2)) +
      (SignedData.interp DA DB l c).Kq) (fun l _ => ?_) ?_
  · unfold restQ SignedData.hadErr
    rw [interp_ν, interp_e, interp_sp, interp_v, interp_a, interp_μ, interp_Sup, interp_η,
      interp_p, interp_τ, interp_g, interp_K]
    ring
  · exact (((((((((IsQuadOn.const _).add (hv.const_mul (1 / 2))).add hE).add
      (hmu.const_mul (1 - DA.η))).add (hpp.const_mul (2 * DA.η))).add (ha.const_mul 2)).add
      (hS.const_mul (-(2 * ((DA.g : ℝ) / DA.ν))))).add (hra.const_mul (-2))).add
      hden).add hKq

theorem restQ_interp_zero (DA DB : SignedData) (c : ℝ) (p : ℕ) :
    restQ (SignedData.interp DA DB 0 c) p = restQ DA p := by
  rw [interp_zero]; rfl

theorem restQ_interp_one {DA DB : SignedData} (hc : InterpCompat DA DB) (c : ℝ) (p : ℕ) :
    restQ (SignedData.interp DA DB 1 c) p = restQ DB p := by
  rw [interp_one hc]; rfl

theorem restQ_interp_const (DA DB : SignedData) (l c : ℝ) (p : ℕ) :
    restQ (SignedData.interp DA DB l c) p = restQ (SignedData.interp DA DB l 0) p := rfl

theorem tsum_abs_linSeq_le {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {u v : ℕ → ℝ}
    (hu : Summable fun k => |u k|) (hv : Summable fun k => |v k|) :
    ∑' k, |linSeq l u v k| ≤ (1 - l) * ∑' k, |u k| + l * ∑' k, |v k| :=
  hasSum_le (fun n => abs_linSeq_le l hl0 hl1 u v n)
    (summable_abs_linSeq hl0 hl1 hu hv).hasSum
    ((hu.hasSum.mul_left (1 - l)).add (hv.hasSum.mul_left l))

theorem convPart_interp_le {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) :
    convPart (SignedData.interp DA DB l c) ≤ (1 - l) * convPart DA + l * convPart DB := by
  unfold convPart
  rw [interp_e, interp_η, hc.e, hc.η]
  have h1 := tsum_abs_linSeq_le hl0 hl1 rA.hv rB.hv
  have h2 := tsum_abs_linSeq_le hl0 hl1 rA.ha rB.ha
  have h3 := tsum_abs_linSeq_le hl0 hl1 rA.hp rB.hp
  have he : 0 ≤ 4 * DA.e := by have := rA.he.1; linarith
  have heη : 0 ≤ 4 * DA.η * DA.e := by have := rA.he.1; have := rA.hη0; positivity
  have h4 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) he
  have h5 := mul_le_mul_of_nonneg_left h3 heη
  calc 4 * DA.e * ((∑' j, |(SignedData.interp DA DB l c).v j|) +
        ∑' k, |(SignedData.interp DA DB l c).a k|) +
        4 * DA.η * DA.e * ∑' j, |(SignedData.interp DA DB l c).p j|
      ≤ 4 * DA.e * (((1 - l) * ∑' k, |DA.v k| + l * ∑' k, |DB.v k|) +
          ((1 - l) * ∑' k, |DA.a k| + l * ∑' k, |DB.a k|)) +
        4 * DA.η * DA.e * ((1 - l) * ∑' k, |DA.p k| + l * ∑' k, |DB.p k|) := add_le_add h4 h5
    _ = _ := by ring

/-- **Theorem M (constant).**  Along the segment the total constant is bounded by the chord of the
endpoint constants minus `l (1 - l)` times the second difference `curvQ` of its quadratic part. -/
theorem constTotal_interp_le {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (p : ℕ) :
    (SignedData.interp DA DB l c).constTotal p - c ≤
      (1 - l) * (DA.constTotal p - DA.constant) + l * (DB.constTotal p - DB.constant) -
        l * (1 - l) * curvQ DA DB p := by
  have hl : l ∈ Icc (0 : ℝ) 1 := ⟨hl0, hl1⟩
  have hq : restQ (SignedData.interp DA DB l 0) p =
      (1 - l) * restQ (SignedData.interp DA DB 0 0) p +
        l * restQ (SignedData.interp DA DB 1 0) p -
        l * (1 - l) * (2 * (restQ (SignedData.interp DA DB 0 0) p +
          restQ (SignedData.interp DA DB 1 0) p) -
          4 * restQ (SignedData.interp DA DB (1 / 2) 0) p) :=
    (isQuadOn_restQ hc rA rB 0 p).chord hl
  rw [restQ_interp_zero, restQ_interp_one hc] at hq
  have hq' : restQ (SignedData.interp DA DB l c) p = (1 - l) * restQ DA p + l * restQ DB p -
      l * (1 - l) * curvQ DA DB p := by
    rw [restQ_interp_const DA DB l c p, hq]
    unfold curvQ
    ring
  have hcv := convPart_interp_le (c := c) hl0 hl1 hc rA rB
  rw [constTotal_eq (SignedData.interp DA DB l c) p, constTotal_eq DA p, constTotal_eq DB p]
  rw [interp_constant]
  nlinarith [hq', hcv]


/-! ### 10b. The curvature `curvQ` as three bilinear blocks

`restQ` is a quadratic form in the data `(v, a, p, R, t, μ, b)` plus an affine part.  Write
`curvBlock Z X Y` for its bilinear form (scalars `ν, sp, K, τ` of `Z`, left argument `X`, right
argument `Y`).  Then `curvQ DA DB = AA - AB - BA + BB` with `AA = curvBlock DA DA DA`,
`AB = curvBlock DA DA DB`, and so on (`curvQ_blocks`).  `AA` and `BB` depend on one trial only
(shared between neighbouring intervals), `AB` and `BA` on the pair. -/

/-- The pairing `Σ u(n+1)/(n+1) · v(n+1)` underlying `barrierTrialNormSq`. -/
def nsqBil (u v : ℕ → ℝ) : ℝ := ∑' n, wsh u n * sh v n

/-- The pairing `Σ refTilt R (n+1) · a (n+1)` of the reference tilt with the trial `a`. -/
def raBil (R a : ℕ → ℝ) : ℝ := ∑' n, rt R n * sh a n

/-- The weighted bilinear `b`-sum. -/
def sumBil (w : ℕ → ℝ) (K : ℕ) (b b' : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, w i * (b (i + 1) * b' (i + 1))

/-- The weights of the `b`-part of `numDenRef`. -/
def denW (D : SignedData) (i : ℕ) : ℝ :=
  ((D.sp : ℝ) ^ 2 / D.ν ^ 2) * (2 / ((i + 1 : ℕ) : ℝ)) + 2 * (D.sp : ℝ) / D.ν ^ 2

/-- The bilinear form of the quadratic part `restQ`, with the scalars of `Z`, the left data of `X`
and the right data of `Y`. -/
def curvBlock (Z X Y : SignedData) : ℝ :=
  (1 / 2) * nsqBil X.v Y.v + 2 * nsqBil X.a Y.a + (1 - Z.η) * refBil X.μ Y.μ +
    2 * Z.η * nsqBil X.p Y.p - 2 * raBil X.R Y.a + sumBil (denW Z) Z.K X.b Y.b +
    (1 / 2) * ip X.R Y.R - (1 / 2) * ip (mpos X.μ Z.τ) (mpos Y.μ Z.τ) +
    (1 - Z.η) * (ip X.t Y.t - ip (mneg X.μ Z.τ) (mneg Y.μ Z.τ))

/-- The part of `restQ` that is affine in the data. -/
def restLin (D : SignedData) (p : ℕ) : ℝ :=
  -((p : ℝ) / D.ν) ^ 2 * Real.log 2 + pinZeroError D.ν D.e + D.eD7 ((p : ℝ) / D.ν) -
    D.η * ((p : ℝ) / D.ν) ^ 2 * Real.log 2 +
    D.η * ((Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / D.ν + 4 * D.e) + D.hadErr +
    2 * ((Real.log 2 - 2 * Real.log (1 - realEnergyTau D.e ^ 2)) / (2 * D.ν) + 2 * D.e) -
    2 * ((D.g : ℝ) / D.ν) * D.Sup

theorem sumBil_denW_self (D : SignedData) :
    sumBil (denW D) D.K D.b D.b =
      ((D.sp : ℝ) ^ 2 / D.ν ^ 2) *
          (∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
        (2 * (D.sp : ℝ) / D.ν ^ 2) * ∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2 := by
  unfold sumBil denW
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `restQ` is the affine part plus the diagonal of the bilinear form. -/
theorem restQ_eq_lin_block (D : SignedData) (p : ℕ) :
    restQ D p = restLin D p + curvBlock D D D := by
  have hra : D.ra = raBil D.R D.a := rfl
  unfold restQ restLin curvBlock
  rw [sumBil_denW_self, hra, refEnergy_eq_refBil]
  simp only [nsq_eq_tsum, nsqBil, raBil, SignedData.Kq]
  ring

theorem restLin_interp {DA DB : SignedData} (hc : InterpCompat DA DB) (l c : ℝ) (p : ℕ) :
    restLin (SignedData.interp DA DB l c) p =
      (1 - l) * restLin DA p + l * restLin DB p := by
  have hν : DB.ν = DA.ν := hc.ν
  have he : DB.e = DA.e := hc.e
  have hη : DB.η = DA.η := hc.η
  have h1 := eD7_interp hc l c ((p : ℝ) / DA.ν)
  unfold restLin SignedData.hadErr
  rw [interp_ν, h1, interp_e, interp_g, interp_Sup, interp_η, interp_τ, hν, he, hc.g, hη,
    hc.τ]
  ring

theorem sumBil_linSeq (w : ℕ → ℝ) (K : ℕ) (b b' : ℕ → ℝ) (l : ℝ) :
    sumBil w K (linSeq l b b') (linSeq l b b') =
      (1 - l) * (1 - l) * sumBil w K b b + (1 - l) * l * sumBil w K b b' +
        l * (1 - l) * sumBil w K b' b + l * l * sumBil w K b' b' := by
  have e : ∀ i, w i * (linSeq l b b' (i + 1) * linSeq l b b' (i + 1)) =
      (1 - l) * (1 - l) * (w i * (b (i + 1) * b (i + 1))) +
        (1 - l) * l * (w i * (b (i + 1) * b' (i + 1))) +
        l * (1 - l) * (w i * (b' (i + 1) * b (i + 1))) +
        l * l * (w i * (b' (i + 1) * b' (i + 1))) := fun i => by
    simp only [linSeq]; ring
  unfold sumBil
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem nsqBil_linSeq {u v : ℕ → ℝ} (hu : Summable fun k => |u k|) (hv : Summable fun k => |v k|)
    (l : ℝ) :
    nsqBil (linSeq l u v) (linSeq l u v) =
      (1 - l) * (1 - l) * nsqBil u u + (1 - l) * l * nsqBil u v +
        l * (1 - l) * nsqBil v u + l * l * nsqBil v v := by
  unfold nsqBil
  rw [wsh_linSeq, sh_linSeq]
  exact tsum_linSeq_mul l (summable_mul_bdd (abs_wsh_le hu) (summable_abs_sh hu))
    (summable_mul_bdd (abs_wsh_le hu) (summable_abs_sh hv))
    (summable_mul_bdd (abs_wsh_le hv) (summable_abs_sh hu))
    (summable_mul_bdd (abs_wsh_le hv) (summable_abs_sh hv))

theorem raBil_linSeq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {R R' a a' : ℕ → ℝ} (hR : IsGeom τ R)
    (hR' : IsGeom τ R') (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) (l : ℝ) :
    raBil (linSeq l R R') (linSeq l a a') =
      (1 - l) * (1 - l) * raBil R a + (1 - l) * l * raBil R a' +
        l * (1 - l) * raBil R' a + l * l * raBil R' a' := by
  obtain ⟨M, hM⟩ := abs_rt_le hτ hR
  obtain ⟨M', hM'⟩ := abs_rt_le hτ hR'
  unfold raBil
  rw [rt_linSeq, sh_linSeq]
  exact tsum_linSeq_mul l (summable_mul_bdd hM (summable_abs_sh ha))
    (summable_mul_bdd hM (summable_abs_sh ha')) (summable_mul_bdd hM' (summable_abs_sh ha))
    (summable_mul_bdd hM' (summable_abs_sh ha'))

theorem refBil_mix_pair {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB : SRef}
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hA : μA.OK CA) (hB : μB.OK CB) :
    refBil (SRef.mix l μA μB) (SRef.mix l μA μB) =
      (1 - l) * (1 - l) * refBil μA μA + (1 - l) * l * refBil μA μB +
        l * (1 - l) * refBil μB μA + l * l * refBil μB μB :=
  refBil_mix hl0 hl1 (hCA.trans (le_max_left CA CB))
    (hA.mono (le_max_left _ _)) (hB.mono (le_max_right _ _))
    (hA.mono (le_max_left _ _)) (hB.mono (le_max_right _ _))

/-- Four-term expansion of the bilinear form along the segment. -/
theorem curvBlock_interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) :
    curvBlock DA (SignedData.interp DA DB l c) (SignedData.interp DA DB l c) =
      (1 - l) * (1 - l) * curvBlock DA DA DA + (1 - l) * l * curvBlock DA DA DB +
        l * (1 - l) * curvBlock DA DB DA + l * l * curvBlock DA DB DB := by
  have hτ := rA.tau
  have gR := SignedRegular.hRτ hc rB
  have gt := SignedRegular.htτ hc rB
  have gp1 : IsGeom DA.τ (mpos DA.μ DA.τ) := isGeom_mpos rA.hμ hτ.1
  have gp2 : IsGeom DA.τ (mpos DB.μ DA.τ) := isGeom_mpos rB.hμ hτ.1
  have gn1 : IsGeom DA.τ (mneg DA.μ DA.τ) := isGeom_mneg rA.hμ hτ.1
  have gn2 : IsGeom DA.τ (mneg DB.μ DA.τ) := isGeom_mneg rB.hμ hτ.1
  have n1 := nsqBil_linSeq rA.hv rB.hv l
  have n2 := nsqBil_linSeq rA.ha rB.ha l
  have n3 := nsqBil_linSeq rA.hp rB.hp l
  have r1 := refBil_mix_pair hl0 hl1 rA.hC rA.hμ rB.hμ
  have r3 := raBil_linSeq hτ rA.hR gR rA.ha rB.ha l
  have r4 := sumBil_linSeq (denW DA) DA.K DA.b DB.b l
  have i1 := ip_linSeq hτ rA.hR gR rA.hR gR l
  have i2 := ip_linSeq hτ rA.ht gt rA.ht gt l
  have i3 := ip_linSeq hτ gp1 gp2 gp1 gp2 l
  have i4 := ip_linSeq hτ gn1 gn2 gn1 gn2 l
  unfold curvBlock
  simp only [interp_v, interp_a, interp_R, interp_t, interp_b, interp_μ, interp_p, interp_τ,
    mpos_mix hl0 hl1 rA.hμ rB.hμ, mneg_mix hl0 hl1 rA.hμ rB.hμ]
  rw [n1, n2, n3, r1, r3, r4, i1, i2, i3, i4]
  ring

/-- **The curvature as three bilinear blocks.**  `curvQ = AA - AB - BA + BB`, where `AA`
(`curvBlock DA DA DA`) and `BB` depend on one endpoint trial each and `AB`, `BA` on the pair. -/
theorem curvQ_blocks {DA DB : SignedData} (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (p : ℕ) :
    curvQ DA DB p = curvBlock DA DA DA - curvBlock DA DA DB - curvBlock DA DB DA +
      curvBlock DA DB DB := by
  have key : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → restQ (SignedData.interp DA DB l 0) p =
      (1 - l) * restLin DA p + l * restLin DB p +
        ((1 - l) * (1 - l) * curvBlock DA DA DA + (1 - l) * l * curvBlock DA DA DB +
          l * (1 - l) * curvBlock DA DB DA + l * l * curvBlock DA DB DB) := by
    intro l hl0 hl1
    rw [restQ_eq_lin_block, restLin_interp hc, ← curvBlock_interp (c := 0) hl0 hl1 hc rA rB]
    rfl
  have h0 := key 0 le_rfl zero_le_one
  have h1 := key 1 zero_le_one le_rfl
  have h2 := key (1 / 2) (by norm_num) (by norm_num)
  rw [restQ_interp_zero] at h0
  rw [restQ_interp_one hc] at h1
  unfold curvQ
  rw [h0, h1, h2]
  ring

/-! ### 11. Summing the fixed-row fields -/

theorem fixedFields_interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB)
    (Rm Rn : ℝ → ℝ) (rc α β : ℝ) {m1 m2 s : ℕ} (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ)
    (zp : Fin s → ℝ) (hyn : ∀ j, yn j ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ j, yp j ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ j, zp j ∈ Ioo (0 : ℝ) 1) :
    (1 / (SignedData.interp DA DB l c).ν) *
        ((∑ j, (SignedData.interp DA DB l c).fNegM Rm (yn j)) +
          (∑ j, (SignedData.interp DA DB l c).fPosMR Rm rc α (yp j)) +
          ∑ j, (SignedData.interp DA DB l c).fNearMS Rn α β (zp j)) =
      (1 - l) * ((1 / DA.ν) * ((∑ j, DA.fNegM Rm (yn j)) + (∑ j, DA.fPosMR Rm rc α (yp j)) +
          ∑ j, DA.fNearMS Rn α β (zp j))) +
        l * ((1 / DB.ν) * ((∑ j, DB.fNegM Rm (yn j)) + (∑ j, DB.fPosMR Rm rc α (yp j)) +
          ∑ j, DB.fNearMS Rn α β (zp j))) := by
  have a1 : ∀ x ∈ Ioo (-1 : ℝ) 0, |x| ≤ 1 := fun x hx =>
    (abs_lt.mpr ⟨hx.1, by linarith [hx.2]⟩).le
  have a2 : ∀ x ∈ Ioo (0 : ℝ) 1, |x| ≤ 1 := fun x hx =>
    (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩).le
  rw [Finset.sum_congr rfl (fun j _ => fNegM_interp hl0 hl1 hc rA rB Rm (a1 _ (hyn j))),
    Finset.sum_congr rfl (fun j _ => fPosMR_interp hl0 hl1 hc rA rB Rm rc α (a2 _ (hyp j))),
    Finset.sum_congr rfl (fun j _ => fNearMS_interp hl0 hl1 hc rA rB Rn α β (a2 _ (hzp j)))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, interp_ν, hc.ν]
  ring

/-! ### 12. Masses of the interpolated references -/

theorem mass_mix {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {μA μB : SRef} {C D : ℝ}
    (hA : μA.OK C) (hB : μB.OK D) :
    (SRef.mix l μA μB).mass = (1 - l) * μA.mass + l * μB.mass := by
  unfold SRef.mass SRef.mix
  dsimp only
  rw [sum_mixFam_real hl0 hl1 (fun τ => (hA.hP τ).finite) (fun τ => (hB.hP τ).finite),
    sum_mixFam_real hl0 hl1 (fun τ => (hA.hN τ).finite) (fun τ => (hB.hN τ).finite)]
  ring

/-! ### 13. The interval theorems: the `α`-dependent fields from the endpoint trials -/

/-- The interpolation weight of `α` in `[αA, αB]`, clamped to `[0, 1]`: outside the trial
interval the family is the nearest endpoint trial, so that every member of the family is a convex
combination of the endpoint trials (the contract `SignedNearBounds` asks `spikeFix` for all `α`). -/
def interpL (αA αB α : ℝ) : ℝ := max 0 (min 1 ((α - αA) / (αB - αA)))

theorem interpL_nonneg (αA αB α : ℝ) : 0 ≤ interpL αA αB α := le_max_left _ _

theorem interpL_le_one (αA αB α : ℝ) : interpL αA αB α ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- On the trial interval the weight is the affine ratio. -/
theorem interpL_of_mem {αA αB α : ℝ} (h : αA < αB) (h1 : αA ≤ α) (h2 : α ≤ αB) :
    interpL αA αB α = (α - αA) / (αB - αA) := by
  have hpos : 0 < αB - αA := by linarith
  have r0 : 0 ≤ (α - αA) / (αB - αA) := div_nonneg (by linarith) hpos.le
  have r1 : (α - αA) / (αB - αA) ≤ 1 := (div_le_one hpos).mpr (by linarith)
  unfold interpL
  rw [min_eq_right r1, max_eq_right r0]

/-- The chord through `(αA, sA)` and `(αB, sB)`: the interpolation of two endpoint values. -/
def chord (αA αB sA sB α : ℝ) : ℝ :=
  (1 - interpL αA αB α) * sA + interpL αA αB α * sB

/-- The interpolated trial family of one `α`-interval: trial `N`, fixed fraction `α`; the
constant is the problem own constant `const N α`. -/
def interpFamily (αA αB : ℝ) (DA DB : ℕ → SignedData) (const : ℕ → ℝ → ℝ) :
    ℕ → ℝ → SignedData :=
  fun N α => SignedData.interp (DA N) (DB N) (interpL αA αB α) (const N α)

/-- The hypotheses on the two endpoint trial families of one `α`-interval `[lo, hi] ⊆ [αA, αB]`:
they agree on the scale data and are regular for all large `N`. -/
structure IntervalEnds (αA αB lo hi : ℝ) (DA DB : ℕ → SignedData) : Prop where
  lt : αA < αB
  lo_ge : αA ≤ lo
  hi_le : hi ≤ αB
  compat : ∀ N, InterpCompat (DA N) (DB N)
  regA : ∀ᶠ N : ℕ in Filter.atTop, SignedRegular (DA N)
  regB : ∀ᶠ N : ℕ in Filter.atTop, SignedRegular (DB N)

section Interval

variable {αA αB lo hi : ℝ} {DA DB : ℕ → SignedData}

theorem IntervalEnds.mem (_h : IntervalEnds αA αB lo hi DA DB) {α : ℝ} (_hα : α ∈ Icc lo hi) :
    0 ≤ interpL αA αB α ∧ interpL αA αB α ≤ 1 := by
  exact ⟨interpL_nonneg αA αB α, interpL_le_one αA αB α⟩

/-- Every member of the interpolated family is regular (a convex combination of regular
endpoint trials), for all `α`. -/
theorem IntervalEnds.regular_all (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α : ℝ, SignedRegular (interpFamily αA αB DA DB const N α) := by
  filter_upwards [h.regA, h.regB] with N rA rB α
  exact SignedRegular.interp (interpL_nonneg αA αB α) (interpL_le_one αA αB α) (h.compat N) rA rB

theorem interpFamily_same {ncount : ℕ → ℕ} {Rf Cf : ℕ → ℝ → ℝ} (const : ℕ → ℝ → ℝ)
    (hν : ∀ N, (DA N).ν = (ncount N : ℝ)) (hRf : ∀ N, (DA N).Rf = Rf N)
    (hCf : ∀ N, (DA N).Cf = Cf N) :
    ∀ N α, (interpFamily αA αB DA DB const N α).ν = (ncount N : ℝ) ∧
      (interpFamily αA αB DA DB const N α).Rf = Rf N ∧
      (interpFamily αA αB DA DB const N α).Cf = Cf N ∧
      (interpFamily αA αB DA DB const N α).constant = const N α :=
  fun N _ => ⟨hν N, hRf N, hCf N, rfl⟩

theorem IntervalEnds.regular (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      SignedRegular (interpFamily αA αB DA DB const N α) := by
  filter_upwards [h.regA, h.regB] with N rA rB α hα
  obtain ⟨hl0, hl1⟩ := h.mem hα
  exact SignedRegular.interp hl0 hl1 (h.compat N) rA rB

theorem IntervalEnds.e_mem (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      (interpFamily αA αB DA DB const N α).e ∈ Ioo (0 : ℝ) (1 / 8) := by
  filter_upwards [h.regular const] with N hN α hα using (hN α hα).he

theorem IntervalEnds.v_summable (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      Summable (fun j => |(interpFamily αA αB DA DB const N α).v j|) := by
  filter_upwards [h.regular const] with N hN α hα using (hN α hα).hv

theorem IntervalEnds.R_geom (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      IsGeom (interpFamily αA αB DA DB const N α).τ (interpFamily αA αB DA DB const N α).R := by
  filter_upwards [h.regular const] with N hN α hα using (hN α hα).hR

theorem IntervalEnds.t_geom (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      IsGeom (interpFamily αA αB DA DB const N α).τ (interpFamily αA αB DA DB const N α).t := by
  filter_upwards [h.regular const] with N hN α hα using (hN α hα).ht

/-- `reference`: the bounded densities and the mass `1 - α/2` of `c_r`. -/
theorem IntervalEnds.reference (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ)
    (mA : ∀ᶠ N : ℕ in Filter.atTop, 1 - αA / 2 = (DA N).μ.mass)
    (mB : ∀ᶠ N : ℕ in Filter.atTop, 1 - αB / 2 = (DB N).μ.mass) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      (interpFamily αA αB DA DB const N α).μ.OK (interpFamily αA αB DA DB const N α).Cb ∧
        0 ≤ (interpFamily αA αB DA DB const N α).Cb ∧
        1 - α / 2 = (interpFamily αA αB DA DB const N α).μ.mass := by
  filter_upwards [h.regA, h.regB, mA, mB] with N rA rB ma mb α hα
  obtain ⟨hl0, hl1⟩ := h.mem hα
  have r := SignedRegular.interp (c := const N α) hl0 hl1 (h.compat N) rA rB
  have hpos : αB - αA ≠ 0 := by linarith [h.lt]
  refine ⟨r.hμ, r.hC, ?_⟩
  show 1 - α / 2 = (SRef.mix (interpL αA αB α) (DA N).μ (DB N).μ).mass
  rw [mass_mix hl0 hl1 rA.hμ rB.hμ, ← ma, ← mb,
    interpL_of_mem h.lt (by linarith [h.lo_ge, hα.1]) (by linarith [h.hi_le, hα.2])]
  field_simp
  ring

theorem IntervalEnds.p_summable (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      Summable (fun j => |(interpFamily αA αB DA DB const N α).p j|) := by
  filter_upwards [h.regular const] with N hN α hα using (hN α hα).hp

/-- `rowNeg` from the endpoint suprema of the negative row field. -/
theorem IntervalEnds.rowNeg (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ)
    {SnA SnB : ℝ}
    (hA : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (DA N).fNeg x ≤ SnA + ε)
    (hB : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (DB N).fNeg x ≤ SnB + ε) :
    ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (interpFamily αA αB DA DB const N α).fNeg x ≤ chord αA αB SnA SnB α + ε := by
  intro ε hε
  filter_upwards [h.regA, h.regB, hA hε, hB hε] with N rA rB a b α hα x hx
  obtain ⟨hl0, hl1⟩ := h.mem hα
  have hx1 : |x| ≤ 1 := (abs_lt.mpr ⟨hx.1, by linarith [hx.2]⟩).le
  show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (const N α)).fNeg x ≤ _
  rw [fNeg_interp hl0 hl1 (h.compat N) rA rB hx1]
  unfold chord
  nlinarith [mul_le_mul_of_nonneg_left (a x hx) (by linarith : 0 ≤ 1 - interpL αA αB α),
    mul_le_mul_of_nonneg_left (b x hx) hl0]

/-- `rowPos` from the endpoint suprema of the positive row field with the spike cost. -/
theorem IntervalEnds.rowPos (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ)
    {SpA SpB : ℝ}
    (hA : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (DA N).fPosS x ≤ SpA + ε)
    (hB : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (DB N).fPosS x ≤ SpB + ε) :
    ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi, ∀ x ∈ Ioo (0 : ℝ) 1,
      (interpFamily αA αB DA DB const N α).fPosS x ≤ chord αA αB SpA SpB α + ε := by
  intro ε hε
  filter_upwards [h.regA, h.regB, hA hε, hB hε] with N rA rB a b α hα x hx
  obtain ⟨hl0, hl1⟩ := h.mem hα
  have hx1 : |x| ≤ 1 := (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩).le
  show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (const N α)).fPosS x ≤ _
  rw [fPosS_interp hl0 hl1 (h.compat N) rA rB hx1]
  unfold chord
  nlinarith [mul_le_mul_of_nonneg_left (a x hx) (by linarith : 0 ≤ 1 - interpL αA αB α),
    mul_le_mul_of_nonneg_left (b x hx) hl0]

/-- `column` from the endpoint suprema of the column field. -/
theorem IntervalEnds.column (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ)
    {SyA SyB : ℝ}
    (hA : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      (DA N).fCol s ≤ SyA + ε)
    (hB : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      (DB N).fCol s ≤ SyB + ε) :
    ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi, ∀ s ∈ Ioo (0 : ℝ) 1,
      (interpFamily αA αB DA DB const N α).fCol s ≤ chord αA αB SyA SyB α + ε := by
  intro ε hε
  filter_upwards [h.regA, h.regB, hA hε, hB hε] with N rA rB a b α hα s hs
  obtain ⟨hl0, hl1⟩ := h.mem hα
  have hs1 : |s| ≤ 1 := (abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩).le
  show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (const N α)).fCol s ≤ _
  rw [fCol_interp hl0 hl1 (h.compat N) rA rB hs1]
  unfold chord
  nlinarith [mul_le_mul_of_nonneg_left (a s hs) (by linarith : 0 ≤ 1 - interpL αA αB α),
    mul_le_mul_of_nonneg_left (b s hs) hl0]

/-- `const_le`: the total constant along the interval, from the two endpoint constants and the
one-sided limit `κ` of the curvature `curvQ` (the quadratic part of three bilinear blocks);
`cP` is the problem own bound on `const N α`. -/
theorem IntervalEnds.const_le (h : IntervalEnds αA αB lo hi DA DB) (const : ℕ → ℝ → ℝ)
    (ncount : ℕ → ℕ) {cP : ℝ → ℝ} {rA rB κ : ℝ}
    (hP : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      const N α ≤ cP α + ε)
    (hA : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      (DA N).constTotal (ncount N) - (DA N).constant ≤ rA + ε)
    (hB : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      (DB N).constTotal (ncount N) - (DB N).constant ≤ rB + ε)
    (hκ : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, κ - ε ≤ curvQ (DA N) (DB N) (ncount N)) :
    ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      (interpFamily αA αB DA DB const N α).constTotal (ncount N) ≤
        cP α + chord αA αB rA rB α - interpL αA αB α * (1 - interpL αA αB α) * κ + ε := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  filter_upwards [h.regA, h.regB, hP hε4, hA hε4, hB hε4, hκ hε4] with N rA' rB' p a b k α hα
  obtain ⟨hl0, hl1⟩ := h.mem hα
  set l := interpL αA αB α with hl
  have key := constTotal_interp_le (c := const N α) hl0 hl1 (h.compat N) rA' rB' (ncount N)
  have hq0 : 0 ≤ l * (1 - l) := mul_nonneg hl0 (by linarith)
  have hq1 : l * (1 - l) ≤ 1 / 4 := by nlinarith [sq_nonneg (l - 1 / 2)]
  have e1 : (interpFamily αA αB DA DB const N α).constTotal (ncount N) =
      (SignedData.interp (DA N) (DB N) l (const N α)).constTotal (ncount N) := rfl
  rw [e1]
  have hpα := p α hα
  have h1 := mul_le_mul_of_nonneg_left a (by linarith : 0 ≤ 1 - l)
  have h2 := mul_le_mul_of_nonneg_left b hl0
  have h3 := mul_le_mul_of_nonneg_left k hq0
  have h4 := mul_le_mul_of_nonneg_left hq1 (by linarith : 0 ≤ ε / 4)
  unfold chord
  rw [← hl]
  nlinarith [key, hpα, h1, h2, h3, h4]

end Interval


/-! ### 14. The `budgetFix` reduction for one interval -/

/-- A function affine in `x` that is `≤ 0` at both ends of an interval is `≤ 0` on it. -/
theorem affine_nonpos_of_ends {a b x x0 x1 : ℝ} (h0 : x0 ≤ x) (h1 : x ≤ x1)
    (e0 : a + b * x0 ≤ 0) (e1 : a + b * x1 ≤ 0) : a + b * x ≤ 0 := by
  rcases le_total 0 b with hb | hb
  · nlinarith [mul_le_mul_of_nonneg_left h1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left h0 (neg_nonneg.mpr hb)]

/-- A convex quadratic that is `≤ 0` at both ends of `[l0, l1]` is `≤ 0` on the interval. -/
theorem quad_nonpos_Icc_convex {a b c l0 l1 l : ℝ} (h0 : a + b * l0 + c * l0 ^ 2 ≤ 0)
    (h1 : a + b * l1 + c * l1 ^ 2 ≤ 0) (hc : 0 ≤ c) (hl0 : l0 ≤ l) (hl1 : l ≤ l1) :
    a + b * l + c * l ^ 2 ≤ 0 := by
  rcases eq_or_lt_of_le (hl0.trans hl1) with hEq | hlt
  · have : l = l0 := by linarith
    subst this; exact h0
  · have hden : 0 < l1 - l0 := by linarith
    have e : (l1 - l0) * (a + b * l + c * l ^ 2) =
        (l1 - l) * (a + b * l0 + c * l0 ^ 2) + (l - l0) * (a + b * l1 + c * l1 ^ 2) -
          c * (l - l0) * (l1 - l) * (l1 - l0) := by ring
    have hA := mul_nonneg (by linarith : 0 ≤ l1 - l) (neg_nonneg.mpr h0)
    have hB := mul_nonneg (by linarith : 0 ≤ l - l0) (neg_nonneg.mpr h1)
    have hC := mul_nonneg (mul_nonneg (mul_nonneg hc (by linarith : 0 ≤ l - l0))
      (by linarith : 0 ≤ l1 - l)) hden.le
    have hle : (l1 - l0) * (a + b * l + c * l ^ 2) ≤ (l1 - l0) * 0 := by
      rw [e, mul_zero]; nlinarith
    exact le_of_mul_le_mul_left hle hden

/-- A quadratic `a + b l + c l²` that is `≤ 0` at both ends of `[l0, l1]` is `≤ 0` on the
interval if it is convex, or monotone on the interval, or has non-positive discriminant. -/
theorem quad_nonpos_Icc {a b c l0 l1 l : ℝ} (h0 : a + b * l0 + c * l0 ^ 2 ≤ 0)
    (h1 : a + b * l1 + c * l1 ^ 2 ≤ 0)
    (hshape : 0 ≤ c ∨ b + 2 * c * l0 ≤ 0 ∨ 0 ≤ b + 2 * c * l1 ∨ b ^ 2 ≤ 4 * a * c)
    (hl0 : l0 ≤ l) (hl1 : l ≤ l1) : a + b * l + c * l ^ 2 ≤ 0 := by
  rcases le_or_gt 0 c with hc | hc
  · exact quad_nonpos_Icc_convex h0 h1 hc hl0 hl1
  · rcases hshape with hc' | hm0 | hm1 | hd
    · exact absurd hc' (not_le.mpr hc)
    · have e : a + b * l + c * l ^ 2 = (a + b * l0 + c * l0 ^ 2) +
          (l - l0) * ((b + 2 * c * l0) + c * (l - l0)) := by ring
      have h2 : (b + 2 * c * l0) + c * (l - l0) ≤ 0 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.2 hl0)]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl0) h2]
    · have e : a + b * l + c * l ^ 2 = (a + b * l1 + c * l1 ^ 2) +
          (l1 - l) * (-(b + 2 * c * l1) + c * (l1 - l)) := by ring
      have h2 : -(b + 2 * c * l1) + c * (l1 - l) ≤ 0 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.2 hl1)]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl1) h2]
    · have h4 : 4 * c * (a + b * l + c * l ^ 2) = (2 * c * l + b) ^ 2 + (4 * a * c - b ^ 2) := by
        ring
      by_contra hP
      push Not at hP
      have := mul_neg_of_neg_of_pos (by linarith : 4 * c < 0) hP
      nlinarith [sq_nonneg (2 * c * l + b)]

/-- **`budgetFix` of one interval.**  Linearity in the free negative fraction `κ`: it suffices to
check the budget at `κlo` and `κhi`, for `α` in the interval, with `ZB ≤ zb` (the σ chord).  The
conclusion is the field `budgetFix` of `SignedNearBounds` for this interval. -/
theorem budgetFix_of_kappa_ends {κlo κhi lo hi B cost ε : ℝ} {cInf MXn MXp MY zb : ℝ → ℝ}
    {ZB : ℝ → ℝ → ℝ → ℝ}
    (hZB : ∀ c d e : ℝ, 0 ≤ c → 0 ≤ d → 0 ≤ e → lo ≤ c + d + e → c + d + e ≤ hi →
      ZB c d e ≤ zb (c + d + e))
    (hlo : ∀ α ∈ Icc lo hi, cInf α + fixLog2 ε α * Real.log 2 + κlo * MXn α +
      (1 - κlo - α) * MXp α + (1 - α) * MY α + zb α ≤ B + cost * α)
    (hhi : ∀ α ∈ Icc lo hi, cInf α + fixLog2 ε α * Real.log 2 + κhi * MXn α +
      (1 - κhi - α) * MXp α + (1 - α) * MY α + zb α ≤ B + cost * α) :
    ∀ (κ c d e : ℝ), κlo ≤ κ → κ ≤ κhi → 0 ≤ c → 0 ≤ d → 0 ≤ e → lo ≤ c + d + e →
      c + d + e ≤ hi → κ + (c + d + e) ≤ 1 →
      cInf (c + d + e) + fixLog2 ε (c + d + e) * Real.log 2 +
        κ * MXn (c + d + e) + (1 - κ - (c + d + e)) * MXp (c + d + e) +
        (1 - (c + d + e)) * MY (c + d + e) + ZB c d e ≤ B + cost * (c + d + e) := by
  intro κ c d e hκ0 hκ1 hc hd he hlo' hhi' _
  have hα : c + d + e ∈ Icc lo hi := ⟨hlo', hhi'⟩
  have hz := hZB c d e hc hd he hlo' hhi'
  set α := c + d + e with hαdef
  have key := affine_nonpos_of_ends (a := cInf α + fixLog2 ε α * Real.log 2 +
    (1 - α) * MXp α + (1 - α) * MY α + zb α - (B + cost * α)) (b := MXn α - MXp α)
    (x := κ) hκ0 hκ1 (by nlinarith [hlo α hα]) (by nlinarith [hhi α hα])
  nlinarith [key, hz]

/-! ### 15. The A7 error term needs no new data -/

/-- `errJ3` depends only on `e, sp, ν`, which the interpolation does not change. -/
theorem errJ3_interp (DA DB : SignedData) (l c c' : ℝ) (n : ℕ) :
    (SignedData.interp DA DB l c).errJ3 c' n = DA.errJ3 c' n := rfl


/-! ### 16. The contract assembled from the endpoint trials (type check against `SignedNearBounds`)

`SignedNearBounds.ofEnds` builds the contract of `EnergyNear` for `I` intervals.  Per interval
`i` the data are the two endpoint trial families `DA i`, `DB i` at `αA i < αB i` with
`[lo i, hi i] ⊆ [αA i, αB i]`, the endpoint suprema of the four fields, the endpoint constants and
the one-sided curvature limit, the problem bound `cP` on the problem constant, and the chord `zb`
of the fixed-node dual.  The interpolated family `D i = interpFamily ..` and the caps
`MXn, MXp, MY, cInf` are determined by these data; the fields `same, e_mem, v_summable, R_geom,
t_geom, reference, rowNeg, rowPos, column, const_le, budgetFix` are produced by the interval
theorems above.  The remaining fields (`spikeFix, err_small, fixedSum`, the class `Clsf`, the
admissibility `FixAdm`, and so on) are not consequences of interpolation and are inputs. -/

/-- The cap `cInf` of an interval: the problem bound plus the quadratic along the chord. -/
def interpCInf (αA αB cP rA rB κ α : ℝ) : ℝ :=
  cP + chord αA αB rA rB α - interpL αA αB α * (1 - interpL αA αB α) * κ

def SignedNearBounds.ofEnds {I : ℕ}
    (ncount : ℕ → ℕ) (ncount_pos : ∀ N, 0 < N → 0 < ncount N) (B cost α1 : ℝ) (α1_nonneg : 0 ≤ α1)
    (lo hi : Fin I → ℝ)
    (cover : ∀ α : ℝ, 0 ≤ α → α ≤ α1 → ∃ i, lo i ≤ α ∧ α ≤ hi i)
    (Rf Cf Rm Rn : ℕ → ℝ → ℝ) (constant : ℕ → ℝ → ℝ)
    -- the endpoint trials
    (αA αB : Fin I → ℝ) (DA DB : Fin I → ℕ → SignedData)
    (hends : ∀ i, IntervalEnds (αA i) (αB i) (lo i) (hi i) (DA i) (DB i))
    (hν : ∀ i N, (DA i N).ν = (ncount N : ℝ)) (hRf : ∀ i N, (DA i N).Rf = Rf N)
    (hCf : ∀ i N, (DA i N).Cf = Cf N)
    (mA : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, 1 - αA i / 2 = (DA i N).μ.mass)
    (mB : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, 1 - αB i / 2 = (DB i N).μ.mass)
    -- the endpoint suprema
    (SnA SnB SpA SpB SyA SyB : Fin I → ℝ)
    (hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (DA i N).fNeg x ≤ SnA i + ε)
    (hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (DB i N).fNeg x ≤ SnB i + ε)
    (hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (DA i N).fPosS x ≤ SpA i + ε)
    (hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (DB i N).fPosS x ≤ SpB i + ε)
    (hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      (DA i N).fCol s ≤ SyA i + ε)
    (hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      (DB i N).fCol s ≤ SyB i + ε)
    -- the endpoint constants and the curvature
    (cP : Fin I → ℝ → ℝ) (rA rB κc : Fin I → ℝ)
    (hP : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
      constant N α ≤ cP i α + ε)
    (hrA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      (DA i N).constTotal (ncount N) - (DA i N).constant ≤ rA i + ε)
    (hrB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      (DB i N).constTotal (ncount N) - (DB i N).constant ≤ rB i + ε)
    (hκ : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      κc i - ε ≤ curvQ (DA i N) (DB i N) (ncount N))
    -- the rest of the contract
    (κlo κhi epsSplit : Fin I → ℝ) (epsSplit_pos : ∀ i, 0 < epsSplit i)
    (epsSplit_le : ∀ i, epsSplit i ≤ 1)
    (etaA : ∀ i N, (DA i N).η = (1 - epsSplit i) / 2)
    (ZB : Fin I → ℝ → ℝ → ℝ → ℝ) (zb : Fin I → ℝ → ℝ)
    (Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LRf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ)
    (FixAdm : ∀ (_ m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop)
    (cp : Fin I → ℕ → ℝ → ℝ) (cp_pos : ∀ i N α, 0 < cp i N α) (cp_le : ∀ i N α, cp i N α ≤ 1)
    (err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
      ((DA i N).withCount (ncount N)).errJ3 (cp i N α) (ncount N) ≤ ε)
    (spikeFix : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α k q m1 m2,
      SpikeCompareFixedCount (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α) (cp i N α)
        (Clsf N k q m1 m2) (LRf N k q m1 m2))
    (fixedSum : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
      ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
        (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) →
        (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
        FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (ncount N : ℝ) = α →
        (1 / (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α).ν) *
            ((∑ j, (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α).fNegM (Rm N) (yn j)) +
              (∑ j, (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α).fPosMR (Rm N)
                (remC (epsSplit i)) α (yp j)) +
              ∑ j, (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α).fNearMS (Rn N) α
                ((s : ℝ) / (ncount N : ℝ)) (zp j)) ≤
          ZB i ((m1 : ℝ) / (ncount N : ℝ)) ((m2 : ℝ) / (ncount N : ℝ))
            ((s : ℝ) / (ncount N : ℝ)) + ε)
    (hZB : ∀ (i : Fin I) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo i ≤ c + d + e → c + d + e ≤ hi i →
      ZB i c d e ≤ zb i (c + d + e))
    (hbudLo : ∀ i, ∀ α ∈ Icc (lo i) (hi i),
      interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α +
        fixLog2 (epsSplit i) α * Real.log 2 +
        κlo i * chord (αA i) (αB i) (SnA i) (SnB i) α +
        (1 - κlo i - α) * chord (αA i) (αB i) (SpA i) (SpB i) α +
        (1 - α) * chord (αA i) (αB i) (SyA i) (SyB i) α + zb i α ≤ B + cost * α)
    (hbudHi : ∀ i, ∀ α ∈ Icc (lo i) (hi i),
      interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α +
        fixLog2 (epsSplit i) α * Real.log 2 +
        κhi i * chord (αA i) (αB i) (SnA i) (SnB i) α +
        (1 - κhi i - α) * chord (αA i) (αB i) (SpA i) (SpB i) α +
        (1 - α) * chord (αA i) (αB i) (SyA i) (SyB i) α + zb i α ≤ B + cost * α) :
    SignedNearBounds I where
  ncount := ncount
  ncount_pos := ncount_pos
  B := B
  cost := cost
  α1 := α1
  α1_nonneg := α1_nonneg
  lo := lo
  hi := hi
  cover := cover
  D := fun i => interpFamily (αA i) (αB i) (DA i) (DB i) constant
  Rf := Rf
  Cf := Cf
  Rm := Rm
  Rn := Rn
  constant := constant
  same := fun i => interpFamily_same constant (hν i) (hRf i) (hCf i)
  MXn := fun i => chord (αA i) (αB i) (SnA i) (SnB i)
  MXp := fun i => chord (αA i) (αB i) (SpA i) (SpB i)
  MY := fun i => chord (αA i) (αB i) (SyA i) (SyB i)
  cInf := fun i α => interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α
  κlo := κlo
  κhi := κhi
  epsSplit := epsSplit
  epsSplit_pos := epsSplit_pos
  epsSplit_le := epsSplit_le
  eta_eq := fun i N _ => etaA i N
  ZB := ZB
  Clsf := Clsf
  LRf := LRf
  FixAdm := FixAdm
  e_mem := fun i => (hends i).e_mem constant
  v_summable := fun i => (hends i).v_summable constant
  p_summable := fun i => (hends i).p_summable constant
  R_geom := fun i => (hends i).R_geom constant
  t_geom := fun i => (hends i).t_geom constant
  reference := fun i => (hends i).reference constant (mA i) (mB i)
  cp := cp
  cp_pos := cp_pos
  cp_le := cp_le
  err_small := err_small
  spikeFix := spikeFix
  rowNeg := fun i => (hends i).rowNeg constant (hSnA i) (hSnB i)
  rowPos := fun i => (hends i).rowPos constant (hSpA i) (hSpB i)
  column := fun i => (hends i).column constant (hSyA i) (hSyB i)
  fixedSum := fixedSum
  const_le := fun i => (hends i).const_le constant ncount (hP i) (hrA i) (hrB i) (hκ i)
  budgetFix := fun i => budgetFix_of_kappa_ends
    (cInf := fun α => interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α)
    (MXn := chord (αA i) (αB i) (SnA i) (SnB i)) (MXp := chord (αA i) (αB i) (SpA i) (SpB i))
    (MY := chord (αA i) (αB i) (SyA i) (SyB i)) (zb := zb i) (hZB i) (hbudLo i) (hbudHi i)

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.integral_mixM
#print axioms CatalanMeasure.Signed.BD_mixM
#print axioms CatalanMeasure.Signed.rowRef_mix
#print axioms CatalanMeasure.Signed.fld_linSeq
#print axioms CatalanMeasure.Signed.ip_linSeq
#print axioms CatalanMeasure.Signed.fNeg_interp
#print axioms CatalanMeasure.Signed.fPos_interp
#print axioms CatalanMeasure.Signed.fPosS_interp
#print axioms CatalanMeasure.Signed.fCol_interp
#print axioms CatalanMeasure.Signed.fNegM_interp
#print axioms CatalanMeasure.Signed.fPosM_interp
#print axioms CatalanMeasure.Signed.fPosMS_interp
#print axioms CatalanMeasure.Signed.fPosMR_interp
#print axioms CatalanMeasure.Signed.fNearM_interp
#print axioms CatalanMeasure.Signed.fNearMS_interp
#print axioms CatalanMeasure.Signed.fixedFields_interp
#print axioms CatalanMeasure.Signed.refEnergy_eq_refBil
#print axioms CatalanMeasure.Signed.refBil_mix
#print axioms CatalanMeasure.Signed.isQuadOn_restQ
#print axioms CatalanMeasure.Signed.constTotal_interp_le
#print axioms CatalanMeasure.Signed.curvQ_blocks
#print axioms CatalanMeasure.Signed.IntervalEnds.e_mem
#print axioms CatalanMeasure.Signed.IntervalEnds.v_summable
#print axioms CatalanMeasure.Signed.IntervalEnds.R_geom
#print axioms CatalanMeasure.Signed.IntervalEnds.t_geom
#print axioms CatalanMeasure.Signed.IntervalEnds.reference
#print axioms CatalanMeasure.Signed.IntervalEnds.rowNeg
#print axioms CatalanMeasure.Signed.IntervalEnds.rowPos
#print axioms CatalanMeasure.Signed.IntervalEnds.column
#print axioms CatalanMeasure.Signed.IntervalEnds.const_le
#print axioms CatalanMeasure.Signed.affine_nonpos_of_ends
#print axioms CatalanMeasure.Signed.quad_nonpos_Icc
#print axioms CatalanMeasure.Signed.budgetFix_of_kappa_ends
#print axioms CatalanMeasure.Signed.SignedNearBounds.ofEnds
