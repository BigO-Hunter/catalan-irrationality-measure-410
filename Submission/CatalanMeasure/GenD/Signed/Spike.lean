module

public import Submission.CatalanMeasure.GenD.Signed.SpikePin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The spike reduction (Theorem A7.1, `spike_reduction`)

Let `φ` be positive and non-increasing on `[-1,1]`, `ψr` positive, and let `ψ = ψr · ∏_p k_p`
with `2m - 1` or `2m` spike factors `k_p(u) = (1 + 2 y_p u + y_p²)⁻¹`, `y_p ∈ (0,1)`.  Then

`log Z_s(φψ) - log Z_s(ψ) ≤ m log φ(-1) + log Z_{s-m}(φ ψr) - log Z_{s-m}(ψr)`,

where `Z_s = heineZ s`.  Odd spike counts are handled by one phantom factor.

The proof is the Hankel-determinant argument of `SpikeOnePoint`, `SpikeMonotone`, `SpikePin`: spikes
are moved to a common depth (monotone for the β = 2 one-point comparison), Fischer's inequality
bounds the numerator, and the Schur complement of the denominator converges to the remaining
Hankel matrix.  This file transports the statements from the variable `t = 1 + cos θ` to `heineZ`.
-/

namespace CatalanMeasure.GenD.Signed

open MeasureTheory Matrix Finset Polynomial Set Real

/-! ### The base measure -/

/-- The pushforward of Lebesgue measure on `(0, π]` under `θ ↦ 1 + cos θ`. -/
noncomputable def muT : Measure ℝ :=
  Measure.map (fun θ : ℝ => 1 + Real.cos θ) (volume.restrict (Ioc 0 π))

theorem measurable_muT_map : Measurable (fun θ : ℝ => 1 + Real.cos θ) :=
  measurable_const.add Real.measurable_cos

instance : IsFiniteMeasure muT := by
  unfold muT
  exact Measure.isFiniteMeasure_map _ _

theorem muT_onI : OnI muT := by
  unfold OnI muT
  refine (ae_map_iff measurable_muT_map.aemeasurable
    (p := fun t => t ∈ Icc (0 : ℝ) 2) measurableSet_Icc).mpr ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  constructor
  · linarith [Real.neg_one_le_cos θ]
  · linarith [Real.cos_le_one θ]

theorem muT_integral {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ t, g t ∂muT = ∫ θ in Ioc 0 π, g (1 + Real.cos θ) := by
  unfold muT
  exact integral_map measurable_muT_map.aemeasurable hg.aestronglyMeasurable

theorem muT_pos (p : ℝ[X]) (hp : p ≠ 0) : 0 < ∫ t, (p.eval t) ^ 2 ∂muT := by
  have hm : Measurable (fun t : ℝ => (p.eval t) ^ 2) := (p.continuous.measurable).pow_const 2
  rw [muT_integral hm]
  set f : ℝ → ℝ := fun θ => (p.eval (1 + Real.cos θ)) ^ 2 with hf
  have hc : Continuous f := (p.continuous.comp (continuous_const.add Real.continuous_cos)).pow 2
  have hnn : 0 ≤ f := fun θ => sq_nonneg _
  have hex : ∃ θ0 ∈ Ioo 0 π, p.eval (1 + Real.cos θ0) ≠ 0 := by
    by_contra H0
    have H : ∀ θ ∈ Ioo 0 π, p.eval (1 + Real.cos θ) = 0 := fun θ hθ => by
      by_contra hne
      exact H0 ⟨θ, hθ, hne⟩
    apply hp
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : InjOn (fun θ : ℝ => 1 + Real.cos θ) (Ioo 0 π) := fun a ha b hb h =>
      Real.injOn_cos (Set.Ioo_subset_Icc_self ha) (Set.Ioo_subset_Icc_self hb) (by simpa using h)
    have hinf : ((fun θ => 1 + Real.cos θ) '' Ioo 0 π).Infinite :=
      (Set.Ioo_infinite Real.pi_pos).image hinj
    refine hinf.mono ?_
    rintro _ ⟨θ, hθ, rfl⟩
    exact H θ hθ
  obtain ⟨θ0, hθ0, hne⟩ := hex
  have hfi : Integrable f (volume.restrict (Ioc 0 π)) := hc.integrableOn_Ioc
  rw [integral_pos_iff_support_of_nonneg hnn hfi]
  have hopen : IsOpen (Function.support f) := hc.isOpen_support
  rw [Measure.restrict_apply hopen.measurableSet]
  have hU : IsOpen (Function.support f ∩ Ioo 0 π) := hopen.inter isOpen_Ioo
  have hne' : (Function.support f ∩ Ioo 0 π).Nonempty := by
    refine ⟨θ0, ⟨?_, hθ0⟩⟩
    simp only [Function.mem_support, hf]
    exact pow_ne_zero 2 hne
  exact lt_of_lt_of_le (hU.measure_pos volume hne')
    (measure_mono (inter_subset_inter_right _ Ioo_subset_Ioc_self))

theorem muT_setting : Setting muT := ⟨muT_onI, muT_pos⟩

theorem muT_hardEdge : HardEdge muT := by
  refine ⟨?_, ⟨1 / 25, by norm_num, 1, one_pos, ?_⟩⟩
  · unfold muT
    rw [Measure.map_apply measurable_muT_map (measurableSet_singleton 0),
      Measure.restrict_apply (measurable_muT_map (measurableSet_singleton 0))]
    refine measure_mono_null ?_ (measure_singleton π)
    rintro θ ⟨h1, h2⟩
    have h0 : 1 + Real.cos θ = 0 := h1
    have hcos : Real.cos θ = Real.cos π := by rw [Real.cos_pi]; linarith
    exact Real.injOn_cos ⟨h2.1.le, h2.2⟩ ⟨Real.pi_pos.le, le_rfl⟩ hcos
  · intro a ha ha1
    set r := Real.sqrt a with hrdef
    have hr : r ^ 2 = a := Real.sq_sqrt ha.le
    have hr0 : 0 < r := Real.sqrt_pos.mpr ha
    have hr1 : r ≤ 1 := by
      rw [hrdef]; exact Real.sqrt_le_one.mpr ha1
    have hS : MeasurableSet (Icc (a / 4) a) := measurableSet_Icc
    have hpi3 := Real.pi_gt_three
    have hpi315 := Real.pi_lt_d2
    have hI : Icc (π - 7 / 5 * r) (π - 6 / 5 * r) ⊆
        (fun θ : ℝ => 1 + Real.cos θ) ⁻¹' (Icc (a / 4) a) ∩ Ioc 0 π := by
      intro θ hθ
      set ε := π - θ with hε
      have hε1 : 6 / 5 * r ≤ ε := by rw [hε]; linarith [hθ.2]
      have hε2 : ε ≤ 7 / 5 * r := by rw [hε]; linarith [hθ.1]
      have hcos : Real.cos θ = -Real.cos ε := by
        rw [hε, ← Real.cos_pi_sub]; congr 1; ring
      refine ⟨⟨?_, ?_⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
      · -- lower bound
        have hεπ : |ε| ≤ π := by rw [abs_of_nonneg (by linarith)]; linarith
        have h1 := Real.cos_le_one_sub_mul_cos_sq hεπ
        have h2 : 2 / π ^ 2 * ε ^ 2 ≥ a / 4 := by
          rw [ge_iff_le, ← hr, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have hεsq : (6 / 5 * r) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) hε1 2
          have hπ2 : π ^ 2 ≤ 10 := by nlinarith
          have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
          nlinarith [mul_le_mul_of_nonneg_left hπ2 hr2]
        show a / 4 ≤ 1 + Real.cos θ
        rw [hcos]; linarith
      · -- upper bound
        have h1 := Real.one_sub_sq_div_two_le_cos (x := ε)
        show 1 + Real.cos θ ≤ a
        rw [hcos]
        nlinarith [sq_nonneg r]
    have hμ : ENNReal.ofReal (r / 5) ≤ muT (Icc (a / 4) a) := by
      unfold muT
      rw [Measure.map_apply measurable_muT_map hS,
        Measure.restrict_apply (measurable_muT_map hS)]
      calc ENNReal.ofReal (r / 5) = volume (Icc (π - 7 / 5 * r) (π - 6 / 5 * r)) := by
            rw [Real.volume_Icc]; congr 1; ring
        _ ≤ _ := measure_mono hI
    have h5 : r / 5 ≤ muT.real (Icc (a / 4) a) := by
      unfold Measure.real
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hμ
    nlinarith

/-! ### Transport from `heineZ` to Hankel determinants -/

theorem heineZ_eq_hk (s : ℕ) {f : ℝ → ℝ} (hf : Bd (fun t => f (t - 1))) :
    heineZ s f = (s.factorial : ℝ) * (hk muT (fun t => f (t - 1)) s).det := by
  set W : ℝ → ℝ := fun t => f (t - 1) with hW
  have hmp : MeasurePreserving (fun (θ : Fin s → ℝ) l => 1 + Real.cos (θ l))
      (Measure.pi fun _ : Fin s => volume.restrict (Ioc 0 π))
      (Measure.pi fun _ : Fin s => muT) :=
    measurePreserving_pi _ _ (fun _ => measurable_muT_map.measurePreserving _)
  have hg : Measurable fun σ : Fin s → ℝ => (Matrix.vandermonde σ).det ^ 2 * ∏ l, W (σ l) :=
    ((measurable_det_vandermonde s).pow_const 2).mul
      (Finset.measurable_prod _ fun l _ => hf.meas.comp (measurable_pi_apply l))
  have h1 : heineZ s f = ∫ σ, (Matrix.vandermonde σ).det ^ 2 * ∏ l, W (σ l)
      ∂(Measure.pi fun _ : Fin s => muT) := by
    rw [← hmp.map_eq, integral_map hmp.aemeasurable hg.aestronglyMeasurable]
    unfold heineZ
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have hv : (Matrix.vandermonde fun l => 1 + Real.cos (θ l)).det =
        (Matrix.vandermonde fun l => Real.cos (θ l)).det := by
      simp only [Matrix.det_vandermonde, add_sub_add_left_eq_sub]
    simp only [hv, hW, add_sub_cancel_left]
  have hint : ∀ (p : ℝ[X]) (i : ℕ), Integrable (fun τ => p.eval τ * (τ ^ i * W τ)) muT := by
    intro p i
    have : Bd (fun τ => p.eval τ * (τ ^ i * W τ)) :=
      (Bd.of_continuous p.continuous).mul ((Bd.of_continuous (continuous_pow i)).mul hf)
    exact this.integrable muT_onI
  have hz := zero_integral_eq (μ := muT) (W := W) (s := s) hint
  rw [h1]
  unfold nodeIntegral at hz
  simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.prod_const_one, mul_one] at hz
  rw [hz, hk_eq_hankelMat]

theorem Adm.of_continuousOn {g : ℝ → ℝ} (hm : Measurable g) (hc : ContinuousOn g (Icc 0 2))
    (hp : ∀ t ∈ Icc (0 : ℝ) 2, 0 < g t) : Adm g := by
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  · obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_isMinOn
      ⟨0, by simp⟩ hc
    exact ⟨g t0, hp t0 ht0, fun t ht => hmin ht⟩

theorem adm_shift {g : ℝ → ℝ} (hm : Measurable g) (hc : ContinuousOn g (Icc (-1) 1))
    (hp : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < g u) : Adm (fun t => g (t - 1)) := by
  refine Adm.of_continuousOn (hm.comp (measurable_id.sub_const 1)) ?_ fun t ht =>
    hp _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine hc.comp (continuousOn_id.sub continuousOn_const) fun t ht => ?_
  exact ⟨by show -1 ≤ t - 1; linarith [ht.1], by show t - 1 ≤ 1; linarith [ht.2]⟩

theorem adm_finset_prod {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ S, Adm (f i)) : Adm (fun t => ∏ i ∈ S, f i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Adm.one
  | insert a S ha ih =>
    have := (h a (Finset.mem_insert_self a S)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.prod_insert ha] using this

/-- The pole `A = (1 - y)² / (2y)` of the spike `(1 + 2y u + y²)⁻¹`. -/
noncomputable def poleOf (y : ℝ) : ℝ := (1 - y) ^ 2 / (2 * y)

theorem poleOf_pos {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 0 < poleOf y := by
  unfold poleOf; have : 0 < 1 - y := by linarith
  positivity

theorem spike_eq {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (1 + 2 * y * (t - 1) + y ^ 2)⁻¹ = (2 * y)⁻¹ * poleK (poleOf y) t := by
  unfold poleK poleOf
  rw [← mul_inv]
  congr 1
  field_simp
  ring

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- Pinning for an arbitrary finite index type of poles. -/
theorem pin_bound_fintype (hμ : Setting μ) (hH : HardEdge μ) {ψ φ : ℝ → ℝ} (hψ : Adm ψ)
    (hφ : Adm φ) (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) {m n s : ℕ} (hs : s = m + n)
    {κ : Type*} [Fintype κ] (hcard : Fintype.card κ = 2 * m) (As : κ → ℝ)
    (hAs : ∀ p, 0 < As p) :
    rat μ φ (fun t => ψ t * ∏ p, poleK (As p) t) s ≤
      φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det / (hk μ ψ n).det := by
  let e : κ ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
  have := pin_bound hμ hH hψ hφ hφa hs (fun i => As (e.symm i)) (fun i => hAs _)
  refine le_trans (le_of_eq ?_) this
  congr 1
  funext t
  congr 1
  exact (Equiv.prod_comp e.symm (fun p => poleK (As p) t)).symm

/-- The spike reduction in multiplicative form. -/
theorem spike_ratio {ι : Type*} [Fintype ι] {s m : ℕ} (hms : m ≤ s) {φ ψr : ℝ → ℝ}
    (hφm : Measurable φ) (hφc : ContinuousOn φ (Icc (-1) 1))
    (hφp : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < φ u) (hφa : AntitoneOn φ (Icc (-1 : ℝ) 1))
    (hψm : Measurable ψr) (hψc : ContinuousOn ψr (Icc (-1) 1))
    (hψp : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < ψr u)
    (y : ι → ℝ) (hy : ∀ p, y p ∈ Ioo (0 : ℝ) 1)
    (hM : Fintype.card ι = 2 * m ∨ Fintype.card ι + 1 = 2 * m) :
    heineZ s (fun u => φ u * (ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)) /
        heineZ s (fun u => ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) ≤
      φ (-1) ^ m * heineZ (s - m) (fun u => φ u * ψr u) / heineZ (s - m) ψr := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hms
  have hsub : m + n - m = n := by omega
  rw [hsub]
  -- admissibility
  have hφ' : Adm (fun t => φ (t - 1)) := adm_shift hφm hφc hφp
  have hψ' : Adm (fun t => ψr (t - 1)) := adm_shift hψm hψc hψp
  have hφa' : AntitoneOn (fun t => φ (t - 1)) (Icc (0 : ℝ) 2) := fun a ha b hb hab =>
    hφa ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩
      (by linarith)
  set As : ι → ℝ := fun p => poleOf (y p) with hAs
  have hApos : ∀ p, 0 < As p := fun p => poleOf_pos (hy p).1 (hy p).2
  set c : ℝ := ∏ p, (2 * y p)⁻¹ with hc
  have hcpos : 0 < c := Finset.prod_pos fun p _ => inv_pos.mpr (by linarith [(hy p).1])
  set W0 : ℝ → ℝ := fun t => ψr (t - 1) * ∏ p, poleK (As p) t with hW0
  have hW0adm : Adm W0 := hψ'.mul (adm_finset_prod _ fun p _ => adm_poleK (hApos p))
  have hG : ∀ t, ψr (t - 1) * ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹ = c * W0 t := by
    intro t
    have : ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹ = c * ∏ p, poleK (As p) t := by
      rw [hc, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p _ => spike_eq (hy p).1 t
    rw [this, hW0]; ring
  have hcadm : Adm (fun t => c * W0 t) :=
    (Adm.of_continuous continuous_const fun _ _ => hcpos).mul hW0adm
  -- the two Hankel determinants for the spiked ensemble
  have hnum := heineZ_eq_hk (m + n) (f := fun u => φ u * (ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹))
    (by
      have : (fun t => φ (t - 1) * (ψr (t - 1) * ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹)) =
          fun t => φ (t - 1) * (c * W0 t) := by funext t; rw [hG]
      simpa only [this] using (hφ'.mul hcadm).toBd)
  have hden := heineZ_eq_hk (m + n) (f := fun u => ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)
    (by
      have : (fun t => ψr (t - 1) * ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹) =
          fun t => c * W0 t := by funext t; rw [hG]
      simpa only [this] using hcadm.toBd)
  have hpos : 0 < (hk muT (fun t => c * W0 t) (m + n)).det :=
    (hk_posDef muT_setting hcadm (m + n)).det_pos
  have hrat : heineZ (m + n) (fun u => φ u * (ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)) /
      heineZ (m + n) (fun u => ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) =
      rat muT (fun t => φ (t - 1)) W0 (m + n) := by
    rw [hnum, hden]
    have e1 : (fun t => φ (t - 1) * (ψr (t - 1) * ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹)) =
        fun t => φ (t - 1) * (c * W0 t) := by funext t; rw [hG]
    have e2 : (fun t => ψr (t - 1) * ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹) =
        fun t => c * W0 t := by funext t; rw [hG]
    simp only [e1, e2]
    rw [← rat_smul (μ := muT) (fun t => φ (t - 1)) W0 c hcpos.ne' (m + n)]
    unfold rat
    have hf : (0 : ℝ) < (m + n).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    rw [mul_div_mul_left _ _ hf.ne']
  rw [hrat]
  -- the pinning bound
  have hbound : rat muT (fun t => φ (t - 1)) W0 (m + n) ≤
      φ (0 - 1) ^ m * (hk muT (fun t => φ (t - 1) * ψr (t - 1)) n).det /
        (hk muT (fun t => ψr (t - 1)) n).det := by
    rcases hM with hM | hM
    · exact pin_bound_fintype muT_setting muT_hardEdge hψ' hφ' hφa' rfl hM As hApos
    · -- phantom pole
      have hphantom := rat_phantom_mono muT_setting hW0adm hφ' hφa' (A := 1) one_pos (m + n)
      refine hphantom.trans ?_
      let As' : Option ι → ℝ := fun o => o.elim 1 As
      have := pin_bound_fintype muT_setting muT_hardEdge hψ' hφ' hφa' (rfl : m + n = m + n)
        (κ := Option ι) (by simp [Fintype.card_option, hM]) As'
        (fun o => by cases o with
          | none => exact one_pos
          | some p => exact hApos p)
      refine le_trans (le_of_eq ?_) this
      congr 1
      funext t
      simp only [hW0, As', Fintype.prod_option, Option.elim_none, Option.elim_some]
      ring
  refine hbound.trans (le_of_eq ?_)
  have hn1 := heineZ_eq_hk n (f := fun u => φ u * ψr u)
    (by simpa using (hφ'.mul hψ').toBd)
  have hn2 := heineZ_eq_hk n (f := ψr) hψ'.toBd
  have hfa : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hd2 : 0 < (hk muT (fun t => ψr (t - 1)) n).det := (hk_posDef muT_setting hψ' n).det_pos
  rw [hn1, hn2, zero_sub]
  field_simp

theorem heineZ_pos (s : ℕ) {f : ℝ → ℝ} (hf : Adm (fun t => f (t - 1))) : 0 < heineZ s f := by
  rw [heineZ_eq_hk s hf.toBd]
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos s)) (hk_posDef muT_setting hf s).det_pos

theorem adm_spike_factor {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Adm (fun t => (1 + 2 * y * (t - 1) + y ^ 2)⁻¹) := by
  have := adm_inv_affine (a := (1 - y) ^ 2) (b := 2 * y) (by nlinarith) (by linarith)
  have e : (fun t : ℝ => (1 + 2 * y * (t - 1) + y ^ 2)⁻¹) = fun t => ((1 - y) ^ 2 + 2 * y * t)⁻¹ := by
    funext t; congr 1; ring
  rw [e]; exact this

/-- **Theorem A7.1 (`spike_reduction`).**  Let `φ` be positive and non-increasing on `[-1,1]`,
`ψr` positive, and `ψ = ψr · ∏_{p} (1 + 2 y_p u + y_p²)⁻¹` with `y_p ∈ (0,1)` and `2m` or `2m - 1`
spike factors.  Then deleting the spikes and `m` particles costs at most `φ(-1)^m`:

`log Z_s(φψ) - log Z_s(ψ) ≤ m log φ(-1) + log Z_{s-m}(φ ψr) - log Z_{s-m}(ψr)`. -/
theorem spike_reduction {ι : Type*} [Fintype ι] {s m : ℕ} (hms : m ≤ s) {φ ψr : ℝ → ℝ}
    (hφm : Measurable φ) (hφc : ContinuousOn φ (Icc (-1) 1))
    (hφp : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < φ u) (hφa : AntitoneOn φ (Icc (-1 : ℝ) 1))
    (hψm : Measurable ψr) (hψc : ContinuousOn ψr (Icc (-1) 1))
    (hψp : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < ψr u)
    (y : ι → ℝ) (hy : ∀ p, y p ∈ Ioo (0 : ℝ) 1)
    (hM : Fintype.card ι = 2 * m ∨ Fintype.card ι + 1 = 2 * m) :
    Real.log (heineZ s (fun u => φ u * (ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹))) -
        Real.log (heineZ s (fun u => ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)) ≤
      m * Real.log (φ (-1)) + Real.log (heineZ (s - m) (fun u => φ u * ψr u)) -
        Real.log (heineZ (s - m) ψr) := by
  have hratio := spike_ratio hms hφm hφc hφp hφa hψm hψc hψp y hy hM
  have hφ' : Adm (fun t => φ (t - 1)) := adm_shift hφm hφc hφp
  have hψ' : Adm (fun t => ψr (t - 1)) := adm_shift hψm hψc hψp
  have hΨ : Adm (fun t => ψr (t - 1) * ∏ p, (1 + 2 * y p * (t - 1) + y p ^ 2)⁻¹) :=
    hψ'.mul (adm_finset_prod _ fun p _ => adm_spike_factor (hy p).1 (hy p).2)
  have p1 : 0 < heineZ s (fun u => φ u * (ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)) :=
    heineZ_pos s (hφ'.mul hΨ)
  have p2 : 0 < heineZ s (fun u => ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) :=
    heineZ_pos s hΨ
  have p3 : 0 < heineZ (s - m) (fun u => φ u * ψr u) := heineZ_pos _ (hφ'.mul hψ')
  have p4 : 0 < heineZ (s - m) ψr := heineZ_pos _ hψ'
  have p5 : 0 < φ (-1) := hφp (-1) ⟨le_rfl, by norm_num⟩
  rw [← Real.log_div p1.ne' p2.ne']
  calc Real.log (heineZ s (fun u => φ u * (ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)) /
        heineZ s (fun u => ψr u * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹))
      ≤ Real.log (φ (-1) ^ m * heineZ (s - m) (fun u => φ u * ψr u) / heineZ (s - m) ψr) :=
        Real.log_le_log (div_pos p1 p2) hratio
    _ = m * Real.log (φ (-1)) + Real.log (heineZ (s - m) (fun u => φ u * ψr u)) -
          Real.log (heineZ (s - m) ψr) := by
        rw [Real.log_div (mul_pos (pow_pos p5 m) p3).ne' p4.ne',
          Real.log_mul (pow_pos p5 m).ne' p3.ne', Real.log_pow]

#print axioms spike_reduction
#print axioms spike_ratio

/-! ### The row form of `spike_reduction` -/

theorem cross_pos_of_nonpos {x u : ℝ} (hx : x ∈ Ioc (-1 : ℝ) 0) (hu : u ∈ Icc (-1 : ℝ) 1) :
    0 < 1 + 2 * x * u + x ^ 2 := by
  nlinarith [mul_nonneg (neg_nonneg.mpr hx.2) (sub_nonneg.mpr hu.2), sq_nonneg (1 + x), hx.1]

theorem cross_pos_of_abs_lt {z u : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1) :
    0 < 1 + 2 * z * u + z ^ 2 := by
  have h1 : 0 < 1 + z * u := by
    rcases le_total 0 z with h | h
    · nlinarith [hu.1, hz.2]
    · nlinarith [hu.2, hz.1]
  nlinarith [sq_nonneg (1 + z * u), mul_nonneg (sq_nonneg z) (show 0 ≤ 1 - u ^ 2 by nlinarith [hu.1, hu.2])]

/-- Theorem A7.1 for explicit rows: negative rows `x_b ∈ (-1, 0]`, further positive rows
`z_p ∈ (-1,1)`, and spiked positive rows `y_p ∈ (0,1)` (`2m` or `2m - 1` of them). -/
theorem spike_reduction_rows {k q : ℕ} {ι : Type*} [Fintype ι] {s m : ℕ} (hms : m ≤ s)
    (x : Fin k → ℝ) (hx : ∀ b, x b ∈ Ioc (-1 : ℝ) 0)
    (z : Fin q → ℝ) (hz : ∀ p, z p ∈ Ioo (-1 : ℝ) 1)
    (y : ι → ℝ) (hy : ∀ p, y p ∈ Ioo (0 : ℝ) 1)
    (hM : Fintype.card ι = 2 * m ∨ Fintype.card ι + 1 = 2 * m) :
    Real.log (heineZ s (fun u => (∏ b, (1 + 2 * x b * u + x b ^ 2)) *
          ((∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹) * ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹))) -
        Real.log (heineZ s (fun u => (∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹) *
          ∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹)) ≤
      m * Real.log (∏ b, (1 + 2 * x b * (-1) + x b ^ 2)) +
        Real.log (heineZ (s - m) (fun u => (∏ b, (1 + 2 * x b * u + x b ^ 2)) *
          ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹)) -
        Real.log (heineZ (s - m) (fun u => ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹)) := by
  have hI : ∀ u ∈ Icc (-1 : ℝ) 1, True := fun _ _ => trivial
  refine spike_reduction (φ := fun u => ∏ b, (1 + 2 * x b * u + x b ^ 2))
    (ψr := fun u => ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹) hms ?_ ?_ ?_ ?_ ?_ ?_ ?_ y hy hM
  · exact Finset.measurable_prod _ fun b _ => by fun_prop
  · exact (continuous_finsetProd _ fun b _ => by fun_prop).continuousOn
  · intro u hu
    exact Finset.prod_pos fun b _ => cross_pos_of_nonpos (hx b) hu
  · intro u hu v hv huv
    refine Finset.prod_le_prod₀ (fun b _ => (cross_pos_of_nonpos (hx b) hv).le) fun b _ => ?_
    nlinarith [(hx b).2]
  · exact Finset.measurable_prod _ fun p _ => by fun_prop
  · refine continuousOn_finsetProd _ fun p _ => ?_
    refine ContinuousOn.inv₀ (by fun_prop) fun u hu => (cross_pos_of_abs_lt (hz p) hu).ne'
  · intro u hu
    exact Finset.prod_pos fun p _ => inv_pos.mpr (cross_pos_of_abs_lt (hz p) hu)

#print axioms spike_reduction_rows

end CatalanMeasure.GenD.Signed
