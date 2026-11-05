module

public import Submission.CatalanMeasure.GenD.Signed.Energy
public import Submission.CatalanMeasure.GenD.Signed.RatioIdentity
public import Submission.CatalanMeasure.GenD.Signed.ArcsineDenominator
public import Submission.CatalanMeasure.GenD.Signed.TiltedTangent
public import Submission.CatalanMeasure.GenD.Signed.CrossDilation

/-!
# The spike comparison (A7.2, `spike_compare`)

PROOF-S2 redone in the J2-with-reference / J5 form.  See `NOTES-S2.md` in the Theorem A plan
folder.

* §A: interior distinctness a.e., the upper bound of `denZ` over interior points.
* §B: the J2 right-hand side with the particle sup, and the numerator bound for `heineZ`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set MeasureTheory Filter Topology OAI.InternalCatalan
open CatalanMeasure.GenD.Signed (heineZ)

noncomputable section

/-! ### A. Interior points and the partition function -/

/-- On almost every point of the cube the coordinates are interior and distinct. -/
theorem ae_lebPi_interior_distinct (n : ℕ) :
    ∀ᵐ θ ∂(lebPi n), (∀ l, θ l ∈ Set.Ioo 0 Real.pi) ∧ ∀ l l', l ≠ l' → θ l ≠ θ l' := by
  have h1 := ae_lebPi_distinct n
  have hend : ∀ (e : ℝ), ∀ l : Fin n, ∀ᵐ θ ∂(lebPi n), θ l ≠ e := by
    intro e l
    have hz : lebPi n {θ | θ l = e} = 0 := by
      have hset : {θ : Fin n → ℝ | θ l = e} =
          Set.pi Set.univ (fun i => if i = l then {e} else Set.univ) := by
        ext θ
        simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
        constructor
        · intro h i
          by_cases hi : i = l
          · subst hi; simpa using h
          · simp [hi]
        · intro h
          simpa using h l
      rw [hset]
      unfold lebPi
      rw [Measure.pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (by rw [show (if l = l then ({e} : Set ℝ) else Set.univ) = {e} by simp,
              Measure.restrict_apply (measurableSet_singleton e)]
            exact measure_mono_null Set.inter_subset_left Real.volume_singleton)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with θ h
    simpa using h
  have h0 : ∀ᵐ θ ∂(lebPi n), ∀ l, θ l ≠ 0 := by
    rw [ae_all_iff]; exact fun l => hend 0 l
  have hπ : ∀ᵐ θ ∂(lebPi n), ∀ l, θ l ≠ Real.pi := by
    rw [ae_all_iff]; exact fun l => hend Real.pi l
  filter_upwards [h1, h0, hπ] with θ ⟨hI, hd⟩ h0 hπ
  exact ⟨fun l => ⟨lt_of_le_of_ne (hI l).1 (h0 l).symm, lt_of_le_of_ne (hI l).2 (hπ l)⟩, hd⟩

theorem cos_mem_Ioo_of_mem_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 Real.pi) :
    Real.cos θ ∈ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi h.1.le le_rfl h.2
    have h2 : Real.cos Real.pi = -1 := Real.cos_pi
    linarith
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) h.2.le h.1
    simpa using this

theorem cos_injective_of_ioo {n : ℕ} {θ : Fin n → ℝ} (hI : ∀ l, θ l ∈ Set.Ioo 0 Real.pi)
    (hd : ∀ l l', l ≠ l' → θ l ≠ θ l') : Function.Injective fun l => Real.cos (θ l) := by
  intro l l' h
  by_contra hne
  exact hd l l' hne (Real.injOn_cos ⟨(hI l).1.le, (hI l).2.le⟩ ⟨(hI l').1.le, (hI l').2.le⟩ h)

/-- Upper bound of `denZ` by a bound for the exponent at interior distinct points. -/
theorem denZ_le_interior {s : ℕ} (Q : ℝ → ℝ) (B : ℝ)
    (hB : ∀ θ : Fin s → ℝ, (∀ l, θ l ∈ Set.Ioo 0 Real.pi) → (∀ l l', l ≠ l' → θ l ≠ θ l') →
      denEnergy Q s θ ≤ B) :
    denZ Q s ≤ Real.pi ^ s * Real.exp B := by
  unfold denZ
  have hfin : IsFiniteMeasure (lebPi s) := by unfold lebPi; infer_instance
  have hb : ∀ᵐ θ ∂(lebPi s), ‖Real.exp (denEnergy Q s θ)‖ ≤ Real.exp B := by
    filter_upwards [ae_lebPi_interior_distinct s] with θ ⟨hm, hd⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hB θ hm hd)
  have h1 := norm_integral_le_of_norm_le_const hb
  have h2 : (lebPi s).real Set.univ = Real.pi ^ s := by
    unfold lebPi
    rw [Measure.real, Measure.pi_univ]
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
      sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [h2] at h1
  calc _ ≤ ‖∫ θ, Real.exp (denEnergy Q s θ) ∂(lebPi s)‖ := le_abs_self _
    _ ≤ _ := by rw [mul_comm]; exact h1

theorem denZ_congr {n : ℕ} {Q Q' : ℝ → ℝ} (h : ∀ u ∈ Icc (-1 : ℝ) 1, Q u = Q' u) :
    denZ Q n = denZ Q' n := by
  unfold denZ denEnergy
  congr 1
  funext θ
  congr 2
  exact Finset.sum_congr rfl fun l _ => h _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem denZ_pos {Q : ℝ → ℝ} (hQm : Measurable Q) {M : ℝ}
    (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) : 0 < denZ Q s :=
  (arcsine_jensen_denominator isTrial_arcsine hQm hQb s).1

theorem denEnergy_eq {n : ℕ} (Q : ℝ → ℝ) (θ : Fin n → ℝ) :
    denEnergy Q n θ = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, kerL (θ i) (θ j) + ∑ l, Q (Real.cos (θ l)) := by
  unfold denEnergy
  congr 1
  have : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, kerL (θ i) (θ j) =
      ∑ j, (if i = j then 0 else kerL (θ i) (θ j)) := by
    intro i
    rw [← Finset.sum_erase (Finset.univ) (f := fun j => if i = j then (0 : ℝ) else kerL (θ i) (θ j))
      (a := i) (by simp)]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [(Finset.ne_of_mem_erase hj).symm]
  simp_rw [this]
  exact sum_offdiag_eq_two_mul (fun i j => kerL (θ i) (θ j)) (fun i j => by
    unfold kerL; rw [abs_sub_comm])

/-! ### B. The J2 right-hand side and the numerator bound -/

/-- The right-hand side of `pair_log_add_cross_le_tilted_ref` for `s` particles, `n` rows `(w, y)`,
with the particle field `Σ_i (Qref - 2 T_a)(u_i)` replaced by `s ℓ`. -/
def jTwoRhs (ν e : ℝ) (a r : ℕ → ℝ) (ℓ : ℝ) (n s : ℕ) (w y : Fin n → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ((s : ℝ) / ν) ^ 2 * Real.log 2 + barrierTrialNormSq a + (s : ℝ) * ℓ / ν +
    (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l) - ∑' k : ℕ, r (k + 1) * a (k + 1)) +
    crossTiltNormRef (realEnergyTau e) w y r + trialPairError ν e a

theorem pair_le_jTwoRhs {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s n : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1)
    (r : ℕ → ℝ) (hr : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2))
    (hra : Summable (fun k : ℕ => r (k + 1) * a (k + 1)))
    (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * realEnergyTau e ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x))
    {ℓ : ℝ} (hℓ : ∀ x ∈ Icc (-1 : ℝ) 1, Qref x - 2 * barrierTrialT a x ≤ ℓ) :
    (∑ i : Fin s, ∑ j ∈ Finset.Ioi i, Real.log |u j - u i|) / ν ^ 2 +
        (∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν ≤
      jTwoRhs ν e a r ℓ n s w y := by
  have h := pair_log_add_cross_le_tilted_ref hν he hs hu hui a ha w y hy r hr hra Qref hQ
  have hsum : (∑ i, (Qref (u i) - 2 * barrierTrialT a (u i))) / ν ≤ (s : ℝ) * ℓ / ν := by
    refine div_le_div_of_nonneg_right ?_ hν.le
    calc _ ≤ ∑ _i : Fin s, ℓ := Finset.sum_le_sum fun i _ =>
          hℓ _ ⟨(hu i).1.le, (hu i).2.le⟩
      _ = (s : ℝ) * ℓ := by simp
  unfold jTwoRhs
  linarith

/-- J3, one-sided and without margin: `crossLog x u ≤ crossLog (D x) u - log D` for `|x| < 1`,
`D ∈ (0, 1]` (indeed `D (1 + 2xu + x²) ≤ 1 + 2Dxu + D²x²`, the difference being
`(1 - D)(1 - D x²) ≥ 0`).  Rows entering with a POSITIVE weight (the negatives) need no margin. -/
theorem crossLog_le_dilate {D x u : ℝ} (hD : D ∈ Ioc (0 : ℝ) 1) (hx : |x| < 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    crossLog x u ≤ crossLog (D * x) u - Real.log D := by
  have hA := cross_pos hx hu
  have hDx : |D * x| < 1 := by
    rw [abs_mul, abs_of_pos hD.1]
    nlinarith [abs_nonneg x, hD.2, hD.1]
  have hB := cross_pos hDx hu
  unfold crossLog
  rw [← Real.log_div hB.ne' hD.1.ne']
  apply Real.log_le_log hA
  rw [le_div_iff₀ hD.1]
  have hx2 : x ^ 2 ≤ 1 := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have h1 : 0 ≤ (1 - D) * (1 - D * x ^ 2) :=
    mul_nonneg (by linarith [hD.2]) (by nlinarith [hD.2, hD.1])
  nlinarith [h1]

/-- With `D = (1 - e)²`: `-log D ≤ 4e`. -/
theorem neg_log_tau_sq_le {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) :
    -Real.log ((1 - e) ^ 2) ≤ 4 * e := by
  have hD : 0 < (1 - e) ^ 2 := by nlinarith [he.2]
  have h := Real.one_sub_inv_le_log_of_pos hD
  have h2 : (1 - e) ^ 2 ≥ 49 / 64 := by nlinarith [he.1, he.2]
  have h3 : ((1 - e) ^ 2)⁻¹ - 1 ≤ 4 * e := by
    rw [inv_eq_one_div, div_sub_one hD.ne', div_le_iff₀ hD]
    nlinarith [he.1, he.2]
  linarith

/-- J3, one-sided field form: only the rows with NEGATIVE weight need the margin `c'`. -/
theorem cross_field_sub_dilate_le_one_sided {n : ℕ} {c' e u : ℝ} (hc' : c' ∈ Ioc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (w y : Fin n → ℝ) (hy1 : ∀ l, |y l| < 1)
    (hy : ∀ l, w l < 0 → |y l| ≤ 1 - c') (hu : u ∈ Icc (-1 : ℝ) 1) :
    ∑ l, w l * crossLog (y l) u - ∑ l, w l * crossLog ((1 - e) ^ 2 * y l) u ≤
      (∑ l, |w l|) * (4 * e / c') := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← mul_sub]
  have h4 : 4 * e ≤ 4 * e / c' := by
    rw [le_div_iff₀ hc'.1]; nlinarith [he.1, hc'.2]
  rcases lt_or_ge (w l) 0 with hw | hw
  · have h := abs_crossLog_sub_dilate_le_of_tau hc' he (hy l hw) hu
    calc w l * (crossLog (y l) u - crossLog ((1 - e) ^ 2 * y l) u)
        ≤ |w l * (crossLog (y l) u - crossLog ((1 - e) ^ 2 * y l) u)| := le_abs_self _
      _ = |w l| * |crossLog (y l) u - crossLog ((1 - e) ^ 2 * y l) u| := abs_mul _ _
      _ ≤ |w l| * (4 * e / c') := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  · have hD : (1 - e) ^ 2 ∈ Ioc (0 : ℝ) 1 :=
      ⟨by nlinarith [he.1, he.2], by nlinarith [he.1, he.2]⟩
    have h := crossLog_le_dilate hD (hy1 l) hu
    have h2 := neg_log_tau_sq_le he
    rw [abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (by linarith) hw

/-- Numerator: `log heineZ n f ≤ n log π + 2ν² J2 + J3err`.  The margin `c'` is needed only for
the rows of negative weight (the positives); the others only need `|y| < 1`. -/
theorem log_heineZ_le {ν e c' : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hc' : c' ∈ Ioc (0 : ℝ) 1) {n N : ℕ} (hn : (n : ℝ) ≤ ν)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (w y : Fin N → ℝ)
    (hw : ∀ l, |2 * ν * w l| = 1) (hy1 : ∀ l, |y l| < 1) (hy : ∀ l, w l < 0 → |y l| ≤ 1 - c')
    (r : ℕ → ℝ) (hr : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2))
    (hra : Summable (fun k : ℕ => r (k + 1) * a (k + 1)))
    (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * realEnergyTau e ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x))
    {ℓ : ℝ} (hℓ : ∀ x ∈ Icc (-1 : ℝ) 1, Qref x - 2 * barrierTrialT a x ≤ ℓ)
    {f : ℝ → ℝ} (hf : ∀ u ∈ Icc (-1 : ℝ) 1,
      f u = Real.exp (∑ l, 2 * ν * w l * crossLog (y l) u)) :
    0 < heineZ n f ∧ Real.log (heineZ n f) ≤ (n : ℝ) * Real.log Real.pi +
      2 * ν ^ 2 * jTwoRhs ν e a r ℓ N n w y + (n : ℝ) * ((N : ℝ) * (4 * e / c')) := by
  set Q : ℝ → ℝ := fun u => ∑ l, 2 * ν * w l * crossLog (y l) u with hQdef
  have hQm : Measurable Q := by
    refine Finset.measurable_sum _ fun l _ => ?_
    exact (measurable_crossLog (y l)).const_mul _
  set M : ℝ := ∑ l, (Real.log 4 + 2 * |Real.log (1 - |y l|)|) with hM
  have hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M := by
    intro u hu
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, hw l, one_mul]
    exact abs_crossLog_le (hy1 l) hu
  have hfpos : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < f u := fun u hu => by
    rw [hf u hu]; exact Real.exp_pos _
  have hZ : heineZ n f = denZ Q n := by
    rw [heineZ_eq_denZ f hfpos]
    exact denZ_congr (fun u hu => by rw [hf u hu, Real.log_exp])
  have hpos : 0 < denZ Q n := denZ_pos hQm hQb n
  rw [hZ]
  refine ⟨hpos, ?_⟩
  set B : ℝ := 2 * ν ^ 2 * jTwoRhs ν e a r ℓ N n w y + (n : ℝ) * ((N : ℝ) * (4 * e / c')) with hB
  have hup : denZ Q n ≤ Real.pi ^ n * Real.exp B := by
    refine denZ_le_interior Q B fun θ hI hd => ?_
    have hinj := cos_injective_of_ioo hI hd
    have hu : ∀ i, Real.cos (θ i) ∈ Ioo (-1 : ℝ) 1 := fun i => cos_mem_Ioo_of_mem_Ioo (hI i)
    have hJ2 := pair_le_jTwoRhs hν he hn (u := fun l => Real.cos (θ l)) hu hinj a ha w y hy1 r hr
      hra Qref hQ hℓ
    have hJ3 : ∀ i, ∑ l, (2 * ν * w l) * crossLog (y l) (Real.cos (θ i)) -
        ∑ l, (2 * ν * w l) * crossLog (realEnergyTau e ^ 2 * y l) (Real.cos (θ i)) ≤
        (∑ l, |2 * ν * w l|) * (4 * e / c') := fun i =>
      cross_field_sub_dilate_le_one_sided hc' he (fun l => 2 * ν * w l) y hy1
        (fun l hl => hy l (by
          by_contra hc
          have : 0 ≤ 2 * ν * w l := mul_nonneg (by positivity) (not_lt.mp hc)
          linarith))
        ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hsumw : (∑ l : Fin N, |2 * ν * w l|) = N := by simp [hw]
    rw [denEnergy_eq]
    have hker : ∀ i j, kerL (θ i) (θ j) = Real.log |Real.cos (θ j) - Real.cos (θ i)| := by
      intro i j; unfold kerL; rw [abs_sub_comm]
    simp only [hker]
    set P := ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |Real.cos (θ j) - Real.cos (θ i)| with hP
    set T := ∑ i : Fin n, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (Real.cos (θ i)) with hT
    have hJ2' : 2 * P + 2 * ν * T ≤ 2 * ν ^ 2 * jTwoRhs ν e a r ℓ N n w y := by
      have h1 : P / ν ^ 2 + T / ν ≤ jTwoRhs ν e a r ℓ N n w y := hJ2
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ν ^ 2)
      have e1 : 2 * ν ^ 2 * (P / ν ^ 2 + T / ν) = 2 * P + 2 * ν * T := by
        field_simp
      linarith
    have hA : ∑ i : Fin n, Q (Real.cos (θ i)) ≤ 2 * ν * T + (n : ℝ) * ((N : ℝ) * (4 * e / c')) := by
      have h3 : ∀ i : Fin n, Q (Real.cos (θ i)) ≤ 2 * ν * (∑ l, w l *
          crossLog (realEnergyTau e ^ 2 * y l) (Real.cos (θ i))) + (N : ℝ) * (4 * e / c') := by
        intro i
        have := hJ3 i
        rw [hsumw] at this
        have h4 : ∑ l, (2 * ν * w l) * crossLog (realEnergyTau e ^ 2 * y l) (Real.cos (θ i)) =
            2 * ν * ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (Real.cos (θ i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [h4] at this
        simp only [hQdef]
        linarith
      calc _ ≤ ∑ i : Fin n, (2 * ν * (∑ l, w l *
          crossLog (realEnergyTau e ^ 2 * y l) (Real.cos (θ i))) + (N : ℝ) * (4 * e / c')) :=
            Finset.sum_le_sum fun i _ => h3 i
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [hT]
    rw [hB]
    linarith
  calc Real.log (denZ Q n) ≤ Real.log (Real.pi ^ n * Real.exp B) := Real.log_le_log hpos hup
    _ = (n : ℝ) * Real.log Real.pi + B := by
        rw [Real.log_mul (pow_pos Real.pi_pos n).ne' (Real.exp_pos _).ne', Real.log_pow,
          Real.log_exp]
    _ = _ := by rw [hB]; ring

/-! ### C. Row families, and the J2 difference when spikes are added -/

theorem sum_fin_append {a b : ℕ} (w1 y1 : Fin a → ℝ) (w2 y2 : Fin b → ℝ) (F : ℝ → ℝ → ℝ) :
    ∑ l : Fin (a + b), F (Fin.append w1 w2 l) (Fin.append y1 y2 l) =
      ∑ l, F (w1 l) (y1 l) + ∑ l, F (w2 l) (y2 l) := by
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem crossBeta_append' {a b : ℕ} (τ : ℝ) (w1 y1 : Fin a → ℝ) (w2 y2 : Fin b → ℝ) (k : ℕ) :
    crossBeta τ (Fin.append w1 w2) (Fin.append y1 y2) k =
      crossBeta τ w1 y1 k + crossBeta τ w2 y2 k := by
  unfold crossBeta
  have := sum_fin_append w1 y1 w2 y2 (fun w y => w * y ^ k)
  try simp only at this
  rw [this]
  ring

theorem crossBeta_mul {n n' : ℕ} (τ : ℝ) (w y : Fin n → ℝ) (w' y' : Fin n' → ℝ) (k : ℕ) :
    crossBeta τ w y k * crossBeta τ w' y' k =
      4 * (τ ^ k) ^ 2 * (∑ l, w l * y l ^ k) * (∑ l, w' l * y' l ^ k) / ((k : ℝ) ^ 2) := by
  unfold crossBeta
  have h : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  calc _ = (((-1 : ℝ) ^ k) * (-1) ^ k) *
        (4 * (τ ^ k) ^ 2 * (∑ l, w l * y l ^ k) * (∑ l, w' l * y' l ^ k) / ((k : ℝ) ^ 2)) := by
        ring
    _ = _ := by rw [h, one_mul]

theorem fin_append_forall {a b : ℕ} {α : Type*} (u : Fin a → α) (v : Fin b → α) (P : α → Prop)
    (hu : ∀ i, P (u i)) (hv : ∀ i, P (v i)) : ∀ l, P (Fin.append u v l) := by
  intro l
  induction l using Fin.addCases with
  | left i => simpa [Fin.append_left] using hu i
  | right i => simpa [Fin.append_right] using hv i

theorem summable_mul_of_sq {u v : ℕ → ℝ}
    (hu : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * u (k + 1) ^ 2)
    (hv : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * v (k + 1) ^ 2) :
    Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (u (k + 1) * v (k + 1)) := by
  refine Summable.of_norm_bounded ((hu.add hv).mul_left (1 / 2)) fun k => ?_
  have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  have h := abs_mul_le_amgm 1 (u (k + 1)) (v (k + 1)) one_pos
  have h2 := mul_le_mul_of_nonneg_left h hk
  simp only [one_mul, div_one] at h2
  nlinarith [h2]

theorem summable_beta_sq {n : ℕ} {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (w y : Fin n → ℝ)
    (hy : ∀ l, |y l| < 1) :
    Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * crossBeta τ w y (k + 1) ^ 2 := by
  have hΛs := crossBeta_summable hτ w y hy
  refine (hΛs.mul_left 4).congr (fun k => ?_)
  have := crossBeta_sq τ w y (k + 1) (Nat.succ_pos k)
  linarith only [this]

theorem summable_ctn {n : ℕ} {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (w y : Fin n → ℝ)
    (hy : ∀ l, |y l| < 1) {r : ℕ → ℝ}
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2) :
    Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (crossBeta τ w y (k + 1) - r (k + 1)) ^ 2 / 4 := by
  have hβs := summable_beta_sq hτ w y hy
  have hβ' : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (crossBeta τ w y (k + 1) - r (k + 1)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => ?_) ((hβs.mul_left 2).add (hr.mul_left 2))
    have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_nonneg hk (sq_nonneg (crossBeta τ w y (k + 1) + r (k + 1)))]
  exact hβ'.div_const 4

/-- Adding a family of rows changes the Λ-term of the tilt by three explicit series. -/
theorem ctn_append_sub {a b : ℕ} {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (w1 y1 : Fin a → ℝ)
    (w2 y2 : Fin b → ℝ) (hy1 : ∀ l, |y1 l| < 1) (hy2 : ∀ l, |y2 l| < 1) {r : ℕ → ℝ}
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2) :
    crossTiltNormRef τ (Fin.append w1 w2) (Fin.append y1 y2) r - crossTiltNormRef τ w1 y1 r =
      (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * crossBeta τ w2 y2 (k + 1) ^ 2 / 4) +
      (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (crossBeta τ w2 y2 (k + 1) * crossBeta τ w1 y1 (k + 1)) / 2) -
      ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (r (k + 1) * crossBeta τ w2 y2 (k + 1)) / 2 := by
  have hy : ∀ l, |Fin.append y1 y2 l| < 1 := fin_append_forall y1 y2 (fun t => |t| < 1) hy1 hy2
  have hA := summable_ctn hτ (Fin.append w1 w2) (Fin.append y1 y2) hy hr
  have hR := summable_ctn hτ w1 y1 hy1 hr
  have h2 := summable_beta_sq hτ w2 y2 hy2
  have h1 := summable_beta_sq hτ w1 y1 hy1
  have hF : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * crossBeta τ w2 y2 (k + 1) ^ 2 / 4 :=
    h2.div_const 4
  have hE : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (crossBeta τ w2 y2 (k + 1) * crossBeta τ w1 y1 (k + 1)) / 2 :=
    (summable_mul_of_sq h2 h1).div_const 2
  have hD : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (r (k + 1) * crossBeta τ w2 y2 (k + 1)) / 2 :=
    (summable_mul_of_sq hr h2).div_const 2
  unfold crossTiltNormRef
  rw [← hA.tsum_sub hR, ← hF.tsum_add hE, ← (hF.add hE).tsum_sub hD]
  refine tsum_congr fun k => ?_
  rw [crossBeta_append']
  ring

/-! The three series for a family of spikes `z` of weight `-1/(2ν)`. -/

/-- Weighted double logarithm series. -/
theorem hasSum_log_pair_w {a b : ℕ} {t : Fin a → ℝ} {u : Fin b → ℝ} (w : Fin b → ℝ)
    (ht : ∀ i, |t i| < 1) (hu : ∀ j, |u j| < 1) :
    HasSum (fun n : ℕ => (∑ i, t i ^ (n + 1)) * (∑ j, w j * u j ^ (n + 1)) / ((n : ℝ) + 1))
      (-∑ i, ∑ j, w j * Real.log (1 - t i * u j)) := by
  have h1 : ∀ i j, HasSum (fun n : ℕ => w j * ((t i * u j) ^ (n + 1) / ((n : ℝ) + 1)))
      (w j * -Real.log (1 - t i * u j)) := by
    intro i j
    refine (Real.hasSum_pow_div_log_of_abs_lt_one ?_).mul_left (w j)
    rw [abs_mul]
    calc |t i| * |u j| ≤ 1 * |u j| :=
          mul_le_mul_of_nonneg_right (ht i).le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hu j
  have h2 := hasSum_sum (s := Finset.univ) fun i _ =>
    hasSum_sum (s := Finset.univ) fun j _ => h1 i j
  convert h2 using 1
  · funext n
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  · simp only [mul_neg, Finset.sum_neg_distrib]

/-- The spike weight. -/
def spikeW (ν : ℝ) (M : ℕ) : Fin M → ℝ := fun _ => -(1 / (2 * ν))

theorem abs_dilate_lt {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {n : ℕ} (v : Fin n → ℝ)
    (hv : ∀ i, |v i| < 1) (i : Fin n) : |τ * v i| < 1 := by
  rw [abs_mul, abs_of_pos hτ.1]
  calc τ * |v i| ≤ 1 * |v i| := mul_le_mul_of_nonneg_right hτ.2.le (abs_nonneg _)
    _ < 1 := by rw [one_mul]; exact hv i

theorem tsum_spike_sq {M : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) (z : Fin M → ℝ)
    (hz : ∀ l, |z l| < 1) :
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * crossBeta τ (spikeW ν M) z (k + 1) ^ 2 / 4 =
      -(1 / (4 * ν ^ 2)) * ∑ p, ∑ q, Real.log (1 - (τ * z p) * (τ * z q)) := by
  have ht := abs_dilate_lt hτ z hz
  have h := (hasSum_log_pair ht ht).mul_left (1 / (4 * ν ^ 2))
  rw [show -(1 / (4 * ν ^ 2)) * ∑ p, ∑ q, Real.log (1 - (τ * z p) * (τ * z q)) =
    (1 / (4 * ν ^ 2)) * -∑ p, ∑ q, Real.log (1 - (τ * z p) * (τ * z q)) by ring]
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [crossBeta_sq τ (spikeW ν M) z (k + 1) (Nat.succ_pos k)]
  unfold spikeW
  have hs : ∑ l : Fin M, -(1 / (2 * ν)) * z l ^ (k + 1) = -(1 / (2 * ν)) * ∑ l, z l ^ (k + 1) := by
    rw [Finset.mul_sum]
  have hs2 : ∑ l : Fin M, (τ * z l) ^ (k + 1) = τ ^ (k + 1) * ∑ l, z l ^ (k + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => mul_pow _ _ _
  rw [hs, hs2]
  push_cast
  field_simp
  ring

theorem tsum_spike_cross {M a : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (z : Fin M → ℝ) (hz : ∀ l, |z l| < 1) (w y : Fin a → ℝ) (hy : ∀ l, |y l| < 1) :
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) *
        (crossBeta τ (spikeW ν M) z (k + 1) * crossBeta τ w y (k + 1)) / 2 =
      (1 / ν) * ∑ p, ∑ l, w l * Real.log (1 - (τ * z p) * (τ * y l)) := by
  have h := (hasSum_log_pair_w w (abs_dilate_lt hτ z hz) (abs_dilate_lt hτ y hy)).mul_left
    (-(1 / ν))
  rw [show (1 / ν) * ∑ p, ∑ l, w l * Real.log (1 - (τ * z p) * (τ * y l)) =
    (-(1 / ν)) * -∑ p, ∑ l, w l * Real.log (1 - (τ * z p) * (τ * y l)) by ring]
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [crossBeta_mul]
  unfold spikeW
  have hs : ∑ l : Fin M, -(1 / (2 * ν)) * z l ^ (k + 1) = -(1 / (2 * ν)) * ∑ l, z l ^ (k + 1) := by
    rw [Finset.mul_sum]
  have hs2 : ∑ l : Fin M, (τ * z l) ^ (k + 1) = τ ^ (k + 1) * ∑ l, z l ^ (k + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => mul_pow _ _ _
  have hs3 : ∑ l : Fin a, w l * (τ * y l) ^ (k + 1) = τ ^ (k + 1) * ∑ l, w l * y l ^ (k + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [mul_pow]; ring
  rw [hs, hs2, hs3]
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hk ⊢
  field_simp
  ring

theorem summable_r_geom {r : ℕ → ℝ}
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2) {c : ℝ} (hc : |c| < 1) :
    Summable fun k : ℕ => r (k + 1) * c ^ (k + 1) := by
  have hg : Summable fun k : ℕ => (c ^ 2) ^ (k + 1) := by
    have : |c ^ 2| < 1 := by
      rw [abs_pow]; nlinarith [abs_nonneg c, mul_nonneg (abs_nonneg c) (sub_nonneg.2 hc.le)]
    exact (summable_geometric_of_abs_lt_one this).comp_injective (add_left_injective 1)
  refine Summable.of_norm_bounded ((hr.add hg).mul_left (1 / 2)) fun k => ?_
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : (c ^ 2) ^ (k + 1) = (|c| ^ (k + 1)) ^ 2 := by
    rw [← sq_abs c]; ring
  rw [h1]
  nlinarith [sq_nonneg (|r (k + 1)| - |c| ^ (k + 1)), sq_abs (r (k + 1)),
    mul_nonneg (sq_nonneg (r (k + 1))) (sub_nonneg.2 hk)]

theorem tsum_spike_ref {M : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (z : Fin M → ℝ) (hz : ∀ l, |z l| < 1) {r : ℕ → ℝ}
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2) :
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (r (k + 1) * crossBeta τ (spikeW ν M) z (k + 1)) / 2 =
      (1 / (2 * ν)) * ∑ p, ∑' k : ℕ, r (k + 1) * (-(τ * z p)) ^ (k + 1) := by
  have hc : ∀ p, |-(τ * z p)| < 1 := fun p => by
    rw [abs_neg]; exact abs_dilate_lt hτ z hz p
  have h := Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun p k => r (k + 1) * (-(τ * z p)) ^ (k + 1)) (fun p _ => summable_r_geom hr (hc p))
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  unfold crossBeta spikeW
  have hs : ∑ l : Fin M, -(1 / (2 * ν)) * z l ^ (k + 1) = -(1 / (2 * ν)) * ∑ l, z l ^ (k + 1) := by
    rw [Finset.mul_sum]
  rw [hs]
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : ∀ p, r (k + 1) * (-(τ * z p)) ^ (k + 1) =
      r (k + 1) * ((-1) ^ (k + 1) * τ ^ (k + 1)) * z p ^ (k + 1) := by
    intro p; rw [neg_pow, mul_pow]; ring
  simp only [hp]
  rw [← Finset.mul_sum]
  push_cast at hk ⊢
  field_simp

/-- **The J2 difference when `M` spikes of weight `-1/(2ν)` and `s - s'` extra particles are
added.** -/
theorem jTwo_diff {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {n M : ℕ}
    (a r : ℕ → ℝ) (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2) (ℓ : ℝ)
    (s s' : ℕ) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1) (z : Fin M → ℝ) (hz : ∀ l, |z l| < 1) :
    2 * ν ^ 2 * (jTwoRhs ν e a r ℓ (n + M) s (Fin.append w (spikeW ν M)) (Fin.append y z) -
        jTwoRhs ν e a r ℓ n s' w y) =
      -(((s : ℝ) ^ 2 - (s' : ℝ) ^ 2)) * Real.log 2 + 2 * ν * ((s : ℝ) - s') * ℓ +
      2 * ν * ∑ p, barrierTrialS a (-(realEnergyTau e) * z p) -
      (1 / 2) * ∑ p, ∑ q, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * z q)) +
      2 * ν * ∑ p, ∑ l, w l * Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * y l)) -
      ν * ∑ p, ∑' k : ℕ, r (k + 1) * (-(realEnergyTau e * z p)) ^ (k + 1) := by
  have hτ := realEnergyTau_bounds he
  have hτ' : realEnergyTau e ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2⟩
  have hC := ctn_append_sub hτ' w y (spikeW ν M) z hy hz hr
  rw [tsum_spike_sq hτ' hν z hz, tsum_spike_cross hτ' hν z hz w y hy,
    tsum_spike_ref hτ' hν z hz hr] at hC
  have hS := sum_fin_append w y (spikeW ν M) z
    (fun w y => w * barrierTrialS a (-(realEnergyTau e) * y))
  try simp only at hS
  have hsp : ∑ p, spikeW ν M p * barrierTrialS a (-(realEnergyTau e) * z p) =
      -(1 / (2 * ν)) * ∑ p, barrierTrialS a (-(realEnergyTau e) * z p) := by
    unfold spikeW; rw [Finset.mul_sum]
  have hC' : crossTiltNormRef (realEnergyTau e) (Fin.append w (spikeW ν M)) (Fin.append y z) r =
      crossTiltNormRef (realEnergyTau e) w y r +
        (-(1 / (4 * ν ^ 2)) * ∑ p, ∑ q, Real.log (1 - (realEnergyTau e * z p) *
          (realEnergyTau e * z q)) +
        (1 / ν) * ∑ p, ∑ l, w l * Real.log (1 - (realEnergyTau e * z p) *
          (realEnergyTau e * y l)) -
        (1 / (2 * ν)) * ∑ p, ∑' k : ℕ, r (k + 1) * (-(realEnergyTau e * z p)) ^ (k + 1)) := by
    linarith only [hC]
  unfold jTwoRhs
  rw [hS, hsp, hC']
  field_simp
  ring


/-! ### D. The screening inequality -/

/-- **Screening.** The J2 square already contains the screening of a spike: for one spike `z`,
`Σ_k r_k (-τ z)^k - 2 S_a(-z) ≤ ℓ`, because the left side is the Poisson average (balayage
`β_z`) of the field `Qref - 2 T_a`, which is `≤ ℓ`. -/
theorem screening {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {a r : ℕ → ℝ}
    (ha : Summable fun k : ℕ => |a k|)
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2) (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * τ ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x))
    {ℓ : ℝ} (hℓ : ∀ x ∈ Icc (-1 : ℝ) 1, Qref x - 2 * barrierTrialT a x ≤ ℓ) {z : ℝ}
    (hz : |z| < 1) :
    ∑' k : ℕ, r (k + 1) * (-(τ * z)) ^ (k + 1) - 2 * barrierTrialS a (-z) ≤ ℓ := by
  set c : ℕ → ℝ := fun j => r j * τ ^ j - 2 * a j / (j : ℝ) with hcdef
  have hτa : |τ| < 1 := by rw [abs_of_pos hτ.1]; exact hτ.2
  have ha1 : Summable fun k : ℕ => |a (k + 1)| := (summable_nat_add_iff 1).2 ha
  have hrτ : Summable fun k : ℕ => r (k + 1) * τ ^ (k + 1) := summable_r_geom hr hτa
  have hc : Summable fun k : ℕ => |c (k + 1)| := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (hrτ.abs.add (ha1.mul_left 2))
    simp only [hcdef]
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    calc _ ≤ |r (k + 1) * τ ^ (k + 1)| + |2 * a (k + 1) / ((k + 1 : ℕ) : ℝ)| := abs_sub _ _
      _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [abs_div, abs_mul, abs_two, Nat.abs_cast, div_le_iff₀ (by linarith)]
        nlinarith [abs_nonneg (a (k + 1))]
  have hSa := barrierTrialS_summable a ha (x := -z) (by rw [abs_neg]; exact hz.le)
  have hTa : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => c (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x - 2 * barrierTrialT a x) := by
    intro x hx
    have h1 := hQ x hx
    have h2 := (barrierTrialT_summable a ha (x := x) (abs_le.mpr hx)).hasSum.mul_left 2
    have h3 := h1.sub h2
    have e2 : (fun k : ℕ => c (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) =
        fun k : ℕ => r (k + 1) * τ ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x -
          2 * (a (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
            ((k + 1 : ℕ) : ℝ)) := by
      funext k
      simp only [hcdef]
      ring
    rw [e2]
    exact h3
  have hmain := poisson_average_le hc (ℓ := ℓ) (fun x hx => by rw [(hTa x hx).tsum_eq]; exact hℓ x hx)
    (ρ := z) hz
  have hsplit : ∑' k : ℕ, c (k + 1) * (-z) ^ (k + 1) =
      ∑' k : ℕ, r (k + 1) * (-(τ * z)) ^ (k + 1) - 2 * barrierTrialS a (-z) := by
    have e1 : ∀ k : ℕ, c (k + 1) * (-z) ^ (k + 1) = r (k + 1) * (-(τ * z)) ^ (k + 1) -
        2 * (a (k + 1) * (-z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
      intro k
      simp only [hcdef]
      rw [neg_mul_eq_mul_neg, mul_pow]
      ring
    simp_rw [e1]
    have hτz : |τ * z| < 1 := by
      have := abs_dilate_lt hτ (fun _ : Fin 1 => z) (fun _ => hz) 0
      simpa using this
    have hs1 : Summable fun k : ℕ => r (k + 1) * (-(τ * z)) ^ (k + 1) :=
      summable_r_geom hr (by rw [abs_neg]; exact hτz)
    rw [hs1.tsum_sub (hSa.mul_left 2), tsum_mul_left]
    rfl
  rw [← hsplit]
  exact hmain

/-! ### E. The reduced denominator trial `(s ν' - m β_ρ) / (s - m)` -/

/-- Chebyshev coefficients of `(s ν' - m β_ρ) / (s - m)`. -/
def bRed (s m ρ : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := (s * b k - m * poisSeq ρ k) / (s - m)

theorem summable_bRed {s m ρ : ℝ} {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    (hρ : |ρ| < 1) : Summable fun k : ℕ => |bRed s m ρ b (k + 1)| := by
  have hp := summable_poisSeq hρ
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (((hb.mul_left |s|).add (hp.mul_left |m|)).div_const |s - m|)
  unfold bRed
  rw [abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc _ ≤ |s * b (k + 1)| + |m * poisSeq ρ (k + 1)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_mul]

theorem chebPs_bRed {s m ρ : ℝ} {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    (hρ : |ρ| < 1) (hsm : s - m ≠ 0) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    chebPs (bRed s m ρ b) u =
      (s * chebPs b u - m * chebPs (poisSeq ρ) u) / (s - m) := by
  have h1 := summable_chebTerm hb hu
  have h2 := summable_chebTerm (summable_poisSeq hρ) hu
  have e : ∀ k : ℕ, bRed s m ρ b (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u =
      (s * (b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u) -
        m * (poisSeq ρ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u)) /
        (s - m) := by
    intro k; unfold bRed; ring
  have ht : ∑' k : ℕ, bRed s m ρ b (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u =
      (s * ∑' k : ℕ, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u -
        m * ∑' k : ℕ, poisSeq ρ (k + 1) *
          (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u) / (s - m) := by
    simp_rw [e]
    rw [tsum_div_const, (h1.mul_left s).tsum_sub (h2.mul_left m), tsum_mul_left, tsum_mul_left]
  unfold chebPs
  rw [ht]
  field_simp
  ring

theorem isTrialS_bRed {s m ρ : ℝ} {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    (hρ : |ρ| < 1) (hs : 0 < s - m) {c : ℝ} (hc : 0 < c)
    (hP : ∀ u ∈ Icc (-1 : ℝ) 1,
      (s - m) * c ≤ s * chebPs b u - m * chebPs (poisSeq ρ) u) :
    IsTrialS (bRed s m ρ b) c :=
  ⟨summable_bRed hb hρ, hc, fun u hu => by
    rw [chebPs_bRed hb hρ hs.ne' hu, le_div_iff₀ hs]; linarith [hP u hu]⟩

theorem barrierTrialS_bRed {s m ρ : ℝ} {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    (hρ : |ρ| < 1) (hs : 0 < s - m) {x : ℝ} (hx : |x| ≤ 1) :
    (s - m) * barrierTrialS (bRed s m ρ b) x =
      s * barrierTrialS b x - m * barrierTrialS (poisSeq ρ) x := by
  have hb0 : Summable fun k : ℕ => |b k| := (summable_nat_add_iff 1).1 hb
  have hp0 : Summable fun k : ℕ => |poisSeq ρ k| := (summable_nat_add_iff 1).1 (summable_poisSeq hρ)
  have h1 := barrierTrialS_summable b hb0 hx
  have h2 := barrierTrialS_summable (poisSeq ρ) hp0 hx
  unfold OAI.InternalCatalan.barrierTrialS
  have e : ∀ k : ℕ, (s - m) * (bRed s m ρ b (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) =
      s * (b (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
        m * (poisSeq ρ (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    intro k; unfold bRed; field_simp
  rw [← tsum_mul_left]
  simp_rw [e]
  rw [(h1.mul_left s).tsum_sub (h2.mul_left m), tsum_mul_left, tsum_mul_left]

theorem summable_cross_coeff {b p : ℕ → ℝ} (hb : Summable fun k : ℕ => b (k + 1) ^ 2)
    (hp : Summable fun k : ℕ => p (k + 1) ^ 2) :
    Summable fun i : ℕ => b (i + 1) * p (i + 1) := by
  refine Summable.of_norm_bounded ((hb.add hp).mul_left (1 / 2)) fun i => ?_
  rw [Real.norm_eq_abs]
  nlinarith [abs_mul_le_amgm 1 (b (i + 1)) (p (i + 1)) one_pos]

theorem energy_bRed {s m ρ : ℝ} {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    (hρ : |ρ| < 1) (hs : 0 < s - m) :
    (s - m) ^ 2 * ∑' i : ℕ, 2 * bRed s m ρ b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) =
      s ^ 2 * ∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) -
        2 * s * m * (2 * barrierTrialS b (-ρ)) + m ^ 2 * (-2 * Real.log (1 - ρ ^ 2)) := by
  obtain ⟨hen, hsq⟩ := summable_energy_coeff hb
  obtain ⟨hen', hsq'⟩ := summable_energy_coeff (summable_poisSeq hρ)
  have hsm : s - m ≠ 0 := hs.ne'
  have hb0 : Summable fun k : ℕ => |b k| := (summable_nat_add_iff 1).1 hb
  have hSb := barrierTrialS_summable b hb0 (x := -ρ) (by rw [abs_neg]; exact hρ.le)
  set f2 : ℕ → ℝ := fun i => 2 * (b (i + 1) * (-ρ) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) with hf2
  have hf2s : Summable f2 := hSb.mul_left 2
  have hS : 2 * barrierTrialS b (-ρ) = ∑' i, f2 i := by
    unfold OAI.InternalCatalan.barrierTrialS; rw [tsum_mul_left]
  have e : ∀ i : ℕ, (s - m) ^ 2 * (2 * bRed s m ρ b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) =
      s ^ 2 * (2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) - 2 * s * m * f2 i +
        m ^ 2 * (2 * poisSeq ρ (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) := by
    intro i
    simp only [hf2]
    unfold bRed poisSeq
    field_simp
    ring
  have h1 : ∑' i : ℕ, s ^ 2 * (2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) =
      s ^ 2 * ∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) := tsum_mul_left
  have h2 : ∑' i : ℕ, 2 * s * m * f2 i = 2 * s * m * ∑' i, f2 i := tsum_mul_left
  have h3 : ∑' i : ℕ, m ^ 2 * (2 * poisSeq ρ (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) =
      m ^ 2 * ∑' i : ℕ, 2 * poisSeq ρ (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) := tsum_mul_left
  have hsum : ∑' i : ℕ, (s ^ 2 * (2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) - 2 * s * m * f2 i +
      m ^ 2 * (2 * poisSeq ρ (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))) =
      ∑' i : ℕ, s ^ 2 * (2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) - ∑' i : ℕ, 2 * s * m * f2 i +
      ∑' i : ℕ, m ^ 2 * (2 * poisSeq ρ (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) := by
    rw [Summable.tsum_add ((hen.mul_left (s ^ 2)).sub (hf2s.mul_left (2 * s * m)))
      (hen'.mul_left (m ^ 2)), Summable.tsum_sub (hen.mul_left (s ^ 2)) (hf2s.mul_left (2 * s * m))]
  rw [← tsum_mul_left]
  simp_rw [e]
  rw [hsum, h1, h2, h3, energy_poisSeq hρ, ← hS]

theorem sq_bRed {s m ρ : ℝ} {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    (hρ : |ρ| < 1) (hs : 0 < s - m) :
    (s - m) ^ 2 * ∑' k : ℕ, bRed s m ρ b (k + 1) ^ 2 =
      s ^ 2 * ∑' k : ℕ, b (k + 1) ^ 2 - 2 * s * m * ∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1) +
        m ^ 2 * (ρ ^ 2 / (1 - ρ ^ 2)) := by
  obtain ⟨hen, hsq⟩ := summable_energy_coeff hb
  obtain ⟨hen', hsq'⟩ := summable_energy_coeff (summable_poisSeq hρ)
  have hsm : s - m ≠ 0 := hs.ne'
  have hc := summable_cross_coeff hsq hsq'
  have e : ∀ k : ℕ, (s - m) ^ 2 * bRed s m ρ b (k + 1) ^ 2 =
      s ^ 2 * b (k + 1) ^ 2 - 2 * s * m * (b (k + 1) * poisSeq ρ (k + 1)) +
        m ^ 2 * poisSeq ρ (k + 1) ^ 2 := by
    intro k
    unfold bRed
    field_simp
    ring
  have h1 : ∑' k : ℕ, s ^ 2 * b (k + 1) ^ 2 = s ^ 2 * ∑' k : ℕ, b (k + 1) ^ 2 := tsum_mul_left
  have h2 : ∑' k : ℕ, 2 * s * m * (b (k + 1) * poisSeq ρ (k + 1)) =
      2 * s * m * ∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1) := tsum_mul_left
  have h3 : ∑' k : ℕ, m ^ 2 * poisSeq ρ (k + 1) ^ 2 = m ^ 2 * ∑' k : ℕ, poisSeq ρ (k + 1) ^ 2 :=
    tsum_mul_left
  have hsum : ∑' k : ℕ, (s ^ 2 * b (k + 1) ^ 2 - 2 * s * m * (b (k + 1) * poisSeq ρ (k + 1)) +
      m ^ 2 * poisSeq ρ (k + 1) ^ 2) =
      ∑' k : ℕ, s ^ 2 * b (k + 1) ^ 2 - ∑' k : ℕ, 2 * s * m * (b (k + 1) * poisSeq ρ (k + 1)) +
      ∑' k : ℕ, m ^ 2 * poisSeq ρ (k + 1) ^ 2 := by
    rw [Summable.tsum_add ((hsq.mul_left (s ^ 2)).sub (hc.mul_left (2 * s * m)))
      (hsq'.mul_left (m ^ 2)), Summable.tsum_sub (hsq.mul_left (s ^ 2)) (hc.mul_left (2 * s * m))]
  rw [← tsum_mul_left]
  simp_rw [e]
  rw [hsum, h1, h2, h3, sq_poisSeq hρ]

/-- The closed form of the field integral of the denominator trial. -/
theorem integral_denQs_Q {b : ℕ → ℝ} {c : ℝ} (h : IsTrialS b c) {q : ℕ} (y : Fin q → ℝ)
    (hy : ∀ l, |y l| < 1) :
    ∫ θ in (0 : ℝ)..Real.pi, denQs b θ * (-∑ l, crossLog (y l) (Real.cos θ)) =
      2 * ∑ l, barrierTrialS b (-(y l)) := by
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcont : ∀ l, Continuous fun θ : ℝ => crossLog (y l) (Real.cos θ) := fun l => by
    unfold crossLog
    exact Continuous.log (by fun_prop) fun θ => (cross_pos (hy l) (hmem θ)).ne'
  have e : ∀ θ : ℝ, denQs b θ * (-∑ l, crossLog (y l) (Real.cos θ)) =
      ∑ l, -(denQs b θ * crossLog (y l) (Real.cos θ)) := by
    intro θ
    rw [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum]
  · have hl : ∀ l : Fin q, ∫ θ in (0 : ℝ)..Real.pi, -(denQs b θ * crossLog (y l) (Real.cos θ)) =
        2 * barrierTrialS b (-(y l)) := by
      intro l
      rw [intervalIntegral.integral_neg,
        integral_crossLog_denQs h ⟨by linarith [(abs_lt.mp (hy l)).1], (abs_lt.mp (hy l)).2⟩]
      unfold OAI.InternalCatalan.barrierTrialS
      rw [neg_mul, neg_neg]
      congr 1
      exact tsum_congr fun i => by ring
    simp_rw [hl]
    rw [Finset.mul_sum]
  · intro l _
    exact ((continuous_denQs h.1).mul (hcont l)).neg.intervalIntegrable _ _


/-! ### F. The exact comparison -/

/-- The algebra of the reduced denominator: `DenB - J5(reduced)` in closed form. -/
theorem den_diff_alg {s' m l2 pl Eb Ebp Ep Bb Bbp Bp Ered Bred SqB SqP SqR SzB : ℝ}
    (hs' : 0 < s')
    (hE : Ered * s' ^ 2 = (s' + m) ^ 2 * Eb - 2 * (s' + m) * m * Ebp + m ^ 2 * Ep)
    (hB : Bred * s' ^ 2 = (s' + m) ^ 2 * Bb - 2 * (s' + m) * m * Bbp + m ^ 2 * Bp)
    (hS : s' * SqR = (s' + m) * SqB - m * SqP) :
    ((s' + m) * ((s' + m) - 1) * (-l2 - Eb) + (s' + m) * (2 * SqB + 2 * SzB) +
        (s' + m) * (pl - 2 * Bb)) -
      (s' * (s' - 1) * (-l2 - Ered) + s' * (2 * SqR) + s' * (pl - 2 * Bred)) =
    -l2 * (2 * (s' + m) * m - m ^ 2 - m) - ((s' + m) * m / s') * Eb -
      ((s' - 1) / s') * (2 * (s' + m) * m * Ebp - m ^ 2 * Ep) + 2 * (s' + m) * SzB + 2 * m * SqP +
      m * pl + (2 * (s' + m) * m / s') * Bb - (4 * (s' + m) * m / s') * Bbp +
      (2 * m ^ 2 / s') * Bp := by
  have hs2 : s' ^ 2 ≠ 0 := by positivity
  have hs0 : s' ≠ 0 := hs'.ne'
  have e1 : Ered = ((s' + m) ^ 2 * Eb - 2 * (s' + m) * m * Ebp + m ^ 2 * Ep) / s' ^ 2 := by
    rw [eq_div_iff hs2]; exact hE
  have e2 : Bred = ((s' + m) ^ 2 * Bb - 2 * (s' + m) * m * Bbp + m ^ 2 * Bp) / s' ^ 2 := by
    rw [eq_div_iff hs2]; exact hB
  have e3 : SqR = ((s' + m) * SqB - m * SqP) / s' := by
    rw [eq_div_iff hs0]; linarith
  rw [e1, e2, e3]
  field_simp
  ring

/-- The row weights of the negatives (`+1/(2ν)`) followed by the rest positives (`-1/(2ν)`). -/
def negPosW (ν : ℝ) (k q : ℕ) : Fin (k + q) → ℝ :=
  Fin.append (fun _ : Fin k => 1 / (2 * ν)) (spikeW ν q)

/-- `NumB`: the J2 bound for `s` particles and all rows (negatives, rest positives, spikes) at
their true positions, times `2ν²`, plus `s log π`. -/
def spikeNumB (ν e : ℝ) (a r : ℕ → ℝ) (ℓ : ℝ) (s : ℕ) {k q M : ℕ} (x : Fin k → ℝ) (y : Fin q → ℝ)
    (z : Fin M → ℝ) : ℝ :=
  2 * ν ^ 2 * jTwoRhs ν e a r ℓ (k + q + M) s (Fin.append (negPosW ν k q) (spikeW ν M))
      (Fin.append (Fin.append x y) z) + (s : ℝ) * Real.log Real.pi

/-- `DenB`: the left side of the J5 bound for `s` particles with the denominator trial `b` and the
field `Q = -Σ_{all positives} crossLog`, in closed form (`integral_denQs_Q`). -/
def spikeDenB (b : ℕ → ℝ) (s : ℕ) {q M : ℕ} (y : Fin q → ℝ) (z : Fin M → ℝ) : ℝ :=
  (s : ℝ) * ((s : ℝ) - 1) * (-Real.log 2 - ∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
    (s : ℝ) * (2 * ∑ j, barrierTrialS b (-(y j)) + 2 * ∑ p, barrierTrialS b (-(z p))) +
    (s : ℝ) * (Real.log Real.pi - 2 * ∑' k : ℕ, b (k + 1) ^ 2)

/-- The exact cost of the spike comparison (the part of `m log φ(-1)` is kept apart). -/
def spikeCostNet (ν e : ℝ) (a b : ℕ → ℝ) (s' m : ℕ) (ρ : ℝ) {k q : ℕ} (x : Fin k → ℝ)
    (y : Fin q → ℝ) (z : Fin (2 * m) → ℝ) : ℝ :=
  2 * ν * ∑ p, (barrierTrialS a (-(z p)) - barrierTrialS a (-(realEnergyTau e) * z p)) +
  (1 / 2) * ∑ p, ∑ p', Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * z p')) -
  ∑ p, ∑ i, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * x i)) +
  ∑ p, ∑ j, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * y j)) +
  (m : ℝ) * Real.log 2 -
  (((s' : ℝ) + m) * m / s') * (∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) -
  (((s' : ℝ) - 1) / s') * (2 * ((s' : ℝ) + m) * m * (2 * barrierTrialS b (-ρ)) -
    (m : ℝ) ^ 2 * (-2 * Real.log (1 - ρ ^ 2))) +
  2 * ((s' : ℝ) + m) * ∑ p, barrierTrialS b (-(z p)) +
  2 * (m : ℝ) * ∑ j, (-Real.log (1 - ρ * y j)) +
  (2 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) ^ 2) -
  (4 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1)) +
  (2 * (m : ℝ) ^ 2 / s') * (ρ ^ 2 / (1 - ρ ^ 2))

theorem sum_negPos {ν : ℝ} (hν : 0 < ν) {k q : ℕ} (x : Fin k → ℝ) (y : Fin q → ℝ) (u : ℝ) :
    ∑ l, 2 * ν * negPosW ν k q l * crossLog (Fin.append x y l) u =
      ∑ b, crossLog (x b) u - ∑ j, crossLog (y j) u := by
  have := sum_fin_append (fun _ : Fin k => 1 / (2 * ν)) x (spikeW ν q) y
    (fun w yy => 2 * ν * w * crossLog yy u)
  unfold negPosW
  try simp only at this
  rw [this]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  · unfold spikeW
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

theorem abs_negPosW {ν : ℝ} (hν : 0 < ν) (k q : ℕ) (l : Fin (k + q)) :
    |2 * ν * negPosW ν k q l| = 1 := by
  refine fin_append_forall (fun _ : Fin k => 1 / (2 * ν)) (spikeW ν q)
    (fun t => |2 * ν * t| = 1) (fun _ => ?_) (fun _ => ?_) l
  · field_simp; simp
  · unfold spikeW; field_simp; simp

theorem sum_negPos_log {ν : ℝ} (hν : 0 < ν) {k q : ℕ} (x : Fin k → ℝ) (y : Fin q → ℝ)
    (c t : ℝ) :
    2 * ν * ∑ l, negPosW ν k q l * Real.log (1 - c * (t * Fin.append x y l)) =
      ∑ b, Real.log (1 - c * (t * x b)) - ∑ j, Real.log (1 - c * (t * y j)) := by
  have := sum_fin_append (fun _ : Fin k => 1 / (2 * ν)) x (spikeW ν q) y
    (fun w yy => w * Real.log (1 - c * (t * yy)))
  unfold negPosW
  try simp only at this
  rw [this]
  have hA : 2 * ν * ∑ b : Fin k, 1 / (2 * ν) * Real.log (1 - c * (t * x b)) =
      ∑ b, Real.log (1 - c * (t * x b)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by field_simp
  have hB : 2 * ν * ∑ j : Fin q, spikeW ν q j * Real.log (1 - c * (t * y j)) =
      -∑ j, Real.log (1 - c * (t * y j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by unfold spikeW; field_simp
  rw [mul_add, hA, hB]; ring

/-- The Poisson sum `S_{β_ρ}(x) = -log (1 + ρ x)`. -/
theorem barrierTrialS_poisSeq {ρ x : ℝ} (hρx : |ρ * x| < 1) :
    barrierTrialS (poisSeq ρ) x = -Real.log (1 + ρ * x) := by
  unfold barrierTrialS
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -(ρ * x)) (by rwa [abs_neg])
  rw [show (1 : ℝ) - -(ρ * x) = 1 + ρ * x by ring] at h
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  unfold poisSeq
  rw [show (-ρ) ^ (k + 1) * x ^ (k + 1) = (-(ρ * x)) ^ (k + 1) by
    rw [← mul_pow]; ring]
  push_cast; ring


set_option maxHeartbeats 4000000 in
/-- **A7.2, exact form.**  The reduced problem (`s'` particles, spikes removed) against the full
bound expression: `log heineZ s' (φψ_r) - log heineZ s' ψ_r ≤ NumB - DenB + J3err + Cost`,
with `Cost = spikeCostNet` an explicit expression (no inequality is spent on it).  The `2m` spikes
`z` stay at their true positions in `NumB` and `DenB`. -/
theorem spike_compare_exact {ν e c' : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hc' : c' ∈ Ioc (0 : ℝ) 1) {s' m : ℕ} (hs' : 0 < s') (hsν : (s' : ℝ) ≤ ν)
    (a r : ℕ → ℝ) (ha : Summable fun k => |a k|)
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2)
    (hra : Summable fun k : ℕ => r (k + 1) * a (k + 1)) (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * realEnergyTau e ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x))
    {ℓ : ℝ} (hℓ : ∀ x ∈ Icc (-1 : ℝ) 1, Qref x - 2 * barrierTrialT a x ≤ ℓ)
    {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) {ρ : ℝ} (hρ : |ρ| < 1) {c1 : ℝ}
    (hc1 : 0 < c1)
    (hP : ∀ u ∈ Icc (-1 : ℝ) 1,
      (s' : ℝ) * c1 ≤ ((s' + m : ℕ) : ℝ) * chebPs b u - m * chebPs (poisSeq ρ) u)
    {k q : ℕ} (x : Fin k → ℝ) (y : Fin q → ℝ) (z : Fin (2 * m) → ℝ)
    (hx : ∀ i, |x i| < 1) (hy : ∀ j, |y j| ≤ 1 - c') (hz : ∀ p, |z p| < 1)
    {fN fD : ℝ → ℝ}
    (hfN : ∀ u ∈ Icc (-1 : ℝ) 1,
      fN u = Real.exp (∑ i, crossLog (x i) u - ∑ j, crossLog (y j) u))
    (hfD : ∀ u ∈ Icc (-1 : ℝ) 1, fD u = Real.exp (-∑ j, crossLog (y j) u)) :
    Real.log (heineZ s' fN) - Real.log (heineZ s' fD) ≤
      spikeNumB ν e a r ℓ (s' + m) x y z - spikeDenB b (s' + m) y z +
        (s' : ℝ) * (((k + q : ℕ) : ℝ) * (4 * e / c')) + spikeCostNet ν e a b s' m ρ x y z := by
  have hτ := realEnergyTau_bounds he
  have hτ' : realEnergyTau e ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2⟩
  have hy1 : ∀ j, |y j| < 1 := fun j => by linarith [hy j, hc'.1]
  have hxy1 : ∀ l, |Fin.append x y l| < 1 :=
    fin_append_forall x y (fun t => |t| < 1) hx hy1
  have hxy : ∀ l, negPosW ν k q l < 0 → |Fin.append x y l| ≤ 1 - c' := by
    intro l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l
    · intro h
      exfalso
      unfold negPosW at h
      rw [Fin.append_left] at h
      have : (0 : ℝ) < 1 / (2 * ν) := by positivity
      linarith
    · intro _
      rw [Fin.append_right]
      exact hy j
  have hs'R : (0 : ℝ) < s' := by exact_mod_cast hs'
  have hcast : (((s' + m : ℕ)) : ℝ) = (s' : ℝ) + m := by push_cast; ring
  have hs's : (s' : ℝ) ≤ ν := hsν
  -- numerator
  have hnum := log_heineZ_le (n := s') (N := k + q) hν he hc' hs's a ha (negPosW ν k q)
    (Fin.append x y) (abs_negPosW hν k q) hxy1 hxy r hr hra Qref hQ hℓ (f := fN)
    (fun u hu => by rw [hfN u hu, sum_negPos hν x y u])
  -- the J2 difference
  have hJ := jTwo_diff hν he a r hr ℓ (s' + m) s' (negPosW ν k q) (Fin.append x y) hxy1 z hz
  -- denominator
  have e0 : (s' : ℝ) + m - m = s' := by ring
  have hsm : 0 < (s' : ℝ) + m - m := by rw [e0]; exact hs'R
  have hT : IsTrialS (bRed ((s' : ℝ) + m) m ρ b) c1 :=
    isTrialS_bRed hb hρ hsm hc1 (fun u hu => by
      rw [e0]; have := hP u hu; rw [hcast] at this; exact this)
  set QD : ℝ → ℝ := fun u => -∑ j, crossLog (y j) u with hQD
  have hQm : Measurable QD := (Finset.measurable_sum _ fun j _ => measurable_crossLog (y j)).neg
  have hQb : ∀ u ∈ Icc (-1 : ℝ) 1,
      |QD u| ≤ ∑ j, (Real.log 4 + 2 * |Real.log (1 - |y j|)|) := by
    intro u hu
    rw [hQD]
    simp only [abs_neg]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => abs_crossLog_le (hy1 j) hu)
  have hJ5 := arcsine_jensen_denominator_crude_sum hT hQm hQb s'
  have hint : ∫ θ in (0 : ℝ)..Real.pi, denQs (bRed ((s' : ℝ) + m) m ρ b) θ * QD (Real.cos θ) =
      2 * ∑ j, barrierTrialS (bRed ((s' : ℝ) + m) m ρ b) (-(y j)) :=
    integral_denQs_Q hT y hy1
  rw [hint] at hJ5
  have hfDpos : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < fD u := fun u hu => by
    rw [hfD u hu]; exact Real.exp_pos _
  have hZD : heineZ s' fD = denZ QD s' := by
    rw [heineZ_eq_denZ fD hfDpos]
    exact denZ_congr (fun u hu => by rw [hfD u hu, Real.log_exp])
  rw [← hZD] at hJ5
  -- the atoms
  have hE := energy_bRed hb hρ hsm
  have hB := sq_bRed hb hρ hsm
  rw [e0] at hE hB
  have hSj : (s' : ℝ) * ∑ j, barrierTrialS (bRed ((s' : ℝ) + m) m ρ b) (-(y j)) =
      ((s' : ℝ) + m) * ∑ j, barrierTrialS b (-(y j)) -
        m * ∑ j, (-Real.log (1 - ρ * y j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := barrierTrialS_bRed (s := (s' : ℝ) + m) (m := (m : ℝ)) hb hρ hsm
      (x := -(y j)) (by rw [abs_neg]; exact (hy1 j).le)
    rw [e0] at h1
    have hpr : |ρ * -(y j)| < 1 := by
      rw [abs_mul, abs_neg]
      calc |ρ| * |y j| ≤ 1 * |y j| := mul_le_mul_of_nonneg_right hρ.le (abs_nonneg _)
        _ < 1 := by rw [one_mul]; exact hy1 j
    have h2 := barrierTrialS_poisSeq hpr
    rw [show (1 : ℝ) + ρ * -(y j) = 1 - ρ * y j by ring] at h2
    rw [h1, h2]
  have hden := den_diff_alg (l2 := Real.log 2) (pl := Real.log Real.pi) (m := (m : ℝ))
    (Eb := ∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))
    (Ebp := 2 * barrierTrialS b (-ρ)) (Ep := -2 * Real.log (1 - ρ ^ 2))
    (Bb := ∑' k : ℕ, b (k + 1) ^ 2) (Bbp := ∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1))
    (Bp := ρ ^ 2 / (1 - ρ ^ 2))
    (Ered := ∑' i : ℕ, 2 * bRed ((s' : ℝ) + m) m ρ b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))
    (Bred := ∑' k : ℕ, bRed ((s' : ℝ) + m) m ρ b (k + 1) ^ 2)
    (SqB := ∑ j, barrierTrialS b (-(y j))) (SqP := ∑ j, (-Real.log (1 - ρ * y j)))
    (SqR := ∑ j, barrierTrialS (bRed ((s' : ℝ) + m) m ρ b) (-(y j)))
    (SzB := ∑ p, barrierTrialS b (-(z p))) hs'R (by linarith [hE]) (by linarith [hB]) hSj
  -- screening
  have hscr : ∀ p, ∑' k : ℕ, r (k + 1) * (-(realEnergyTau e * z p)) ^ (k + 1) ≤
      ℓ + 2 * barrierTrialS a (-(z p)) := fun p => by
    have := screening hτ' ha hr Qref hQ hℓ (hz p)
    linarith
  have hscr_sum : ∑ p, ∑' k : ℕ, r (k + 1) * (-(realEnergyTau e * z p)) ^ (k + 1) ≤
      (2 * m : ℝ) * ℓ + 2 * ∑ p, barrierTrialS a (-(z p)) := by
    calc _ ≤ ∑ p : Fin (2 * m), (ℓ + 2 * barrierTrialS a (-(z p))) :=
          Finset.sum_le_sum fun p _ => hscr p
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Finset.mul_sum]
        simp
  have hscr_mul := mul_le_mul_of_nonneg_left hscr_sum hν.le
  -- the cross terms of the spikes against the rows
  have hcross : ∀ p, 2 * ν * ∑ l, negPosW ν k q l *
      Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * Fin.append x y l)) =
      ∑ i, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * x i)) -
        ∑ j, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * y j)) :=
    fun p => sum_negPos_log hν x y _ _
  have hcross_sum : 2 * ν * ∑ p, ∑ l, negPosW ν k q l *
      Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * Fin.append x y l)) =
      ∑ p, ∑ i, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * x i)) -
        ∑ p, ∑ j, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * y j)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => hcross p
  -- assemble
  unfold spikeNumB spikeDenB spikeCostNet
  obtain ⟨hpos, hnum'⟩ := hnum
  obtain ⟨hpos2, hJ5'⟩ := hJ5
  have hlogD : Real.log (heineZ s' fD) = Real.log (denZ QD s') := by rw [hZD]
  rw [hcast] at hJ ⊢
  rw [Finset.sum_sub_distrib]
  linarith [hnum', hJ5', hJ, hden, hscr_mul, hcross_sum, hlogD]


/-! ### G. The bounded cost -/

/-- Lemma 5 (negatives), the elementary inequality. -/
theorem neg_row_bound {t c0 c : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc01 : c0 ≤ 1) (hc : c0 ≤ c) :
    (1 + t) * (1 + c0) ≤ 2 * (1 + c * t) := by
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hc01), mul_nonneg ht (sub_nonneg.2 hc)]

/-- Lemma 5: a negative row against a spike at depth `≥ r`. -/
theorem log_neg_row_le {τ r x z : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hx0 : x ≤ 0) (hx1 : -1 < x) (hzr : r ≤ z) :
    Real.log (1 - x) - Real.log (1 - (τ * z) * (τ * x)) ≤ Real.log (2 / (1 + τ ^ 2 * r)) := by
  have hτ2 : 0 < τ ^ 2 := pow_pos hτ.1 2
  have hτ21 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hz0 : 0 < z := lt_of_lt_of_le hr.1 hzr
  have hxz : (τ * z) * (τ * x) ≤ 0 := by
    have : 0 < τ * z := mul_pos hτ.1 hz0
    nlinarith [mul_nonneg this.le (mul_nonneg hτ.1.le (neg_nonneg.2 hx0))]
  have hd : 0 < 1 - (τ * z) * (τ * x) := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hden : 0 < 1 + τ ^ 2 * r := add_pos one_pos (mul_pos hτ2 hr.1)
  rw [← Real.log_div h1x.ne' hd.ne']
  refine Real.log_le_log (div_pos h1x hd) ?_
  rw [div_le_div_iff₀ hd hden]
  have key := neg_row_bound (t := -x) (c0 := τ ^ 2 * r) (c := τ ^ 2 * z) (by linarith)
    (by linarith) (by nlinarith [hr.2]) (by nlinarith [hzr])
  nlinarith [key]

theorem log_pos_row_le {τ ρ y z : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hz1 : z < 1) (hz0 : 0 < z) (hρ : ρ ≤ τ ^ 2 * z) (_hρ1 : |ρ| < 1) :
    Real.log (1 - (τ * z) * (τ * y)) - Real.log (1 - ρ * y) ≤ 0 := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hlt : (τ * z) * (τ * y) < 1 := by
    have : (τ * z) * (τ * y) = τ ^ 2 * (z * y) := by ring
    rw [this]
    have : z * y < 1 := by nlinarith
    nlinarith [hτ.1, mul_nonneg hy0 hz0.le]
  have hd : 0 < 1 - (τ * z) * (τ * y) := by linarith
  have hρy : ρ * y ≤ (τ * z) * (τ * y) := by
    have : (τ * z) * (τ * y) = (τ ^ 2 * z) * y := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hρ hy0
  have : Real.log (1 - (τ * z) * (τ * y)) ≤ Real.log (1 - ρ * y) :=
    Real.log_le_log hd (by linarith)
  linarith

theorem log_spike_pair_le {τ r z z' : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : r ≤ z) (hz' : r ≤ z') (hz1 : z < 1) (hz1' : z' < 1) :
    Real.log (1 - (τ * z) * (τ * z')) ≤ Real.log (1 - τ ^ 2 * r ^ 2) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
  have h0 : 0 < 1 - (τ * z) * (τ * z') := by
    have : (τ * z) * (τ * z') = τ ^ 2 * (z * z') := by ring
    rw [this]
    have : z * z' < 1 := by nlinarith [hr.1]
    nlinarith [hτ.1, mul_pos (lt_of_lt_of_le hr.1 hz) (lt_of_lt_of_le hr.1 hz')]
  refine Real.log_le_log h0 ?_
  have : r ^ 2 ≤ z * z' := by nlinarith [hr.1]
  have : (τ * z) * (τ * z') = τ ^ 2 * (z * z') := by ring
  nlinarith [mul_le_mul_of_nonneg_left (show r ^ 2 ≤ z * z' by nlinarith [hr.1]) (sq_nonneg τ)]

/-- `|S_a(-z) - S_a(-τ z)| ≤ e ‖a‖₁`: the screening error of one spike. -/
theorem abs_barrierTrialS_sub_le {a : ℕ → ℝ} (ha : Summable fun k : ℕ => |a k|) {e z : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hz : |z| < 1) :
    |barrierTrialS a (-z) - barrierTrialS a (-(realEnergyTau e) * z)| ≤ e * ∑' k : ℕ, |a k| := by
  have hτ := realEnergyTau_bounds he
  have hτe : realEnergyTau e = 1 - e := rfl
  have h1 := barrierTrialS_summable a ha (x := -z) (by rw [abs_neg]; exact hz.le)
  have h2 := barrierTrialS_summable a ha (x := -(realEnergyTau e) * z) (by
    rw [abs_mul, abs_neg, abs_of_pos hτ.1]
    calc realEnergyTau e * |z| ≤ 1 * 1 := mul_le_mul hτ.2.le hz.le (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1)
  have ha1 : Summable fun k : ℕ => |a (k + 1)| := (summable_nat_add_iff 1).2 ha
  unfold barrierTrialS
  rw [← h1.tsum_sub h2]
  have hb : ∀ k : ℕ, |a (k + 1) * (-z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
      a (k + 1) * (-(realEnergyTau e) * z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)| ≤ e * |a (k + 1)| := by
    intro k
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by linarith
    have hpow : |(-z) ^ (k + 1) - (-(realEnergyTau e) * z) ^ (k + 1)| ≤
        ((k + 1 : ℕ) : ℝ) * e := by
      have e1 : (-(realEnergyTau e) * z) ^ (k + 1) = (realEnergyTau e) ^ (k + 1) * (-z) ^ (k + 1) := by
        rw [show -(realEnergyTau e) * z = realEnergyTau e * (-z) by ring, mul_pow]
      rw [e1, ← one_sub_mul, abs_mul, abs_pow, abs_neg]
      have hb1 : (1 - realEnergyTau e ^ (k + 1)) ≤ ((k + 1 : ℕ) : ℝ) * e := by
        have := one_add_mul_le_pow (a := -e) (by linarith [he.1, he.2]) (k + 1)
        rw [hτe]
        have h' : (1 + -e) = 1 - e := by ring
        rw [h'] at this
        push_cast at this ⊢
        nlinarith [this]
      have hb2 : 0 ≤ 1 - realEnergyTau e ^ (k + 1) := by
        have := pow_le_one₀ hτ.1.le hτ.2.le (n := k + 1)
        linarith
      rw [abs_of_nonneg hb2]
      calc _ ≤ (1 - realEnergyTau e ^ (k + 1)) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hz.le) hb2
        _ ≤ _ := by linarith
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, Nat.abs_cast,
      div_le_iff₀ hkp]
    calc |a (k + 1)| * |(-z) ^ (k + 1) - (-(realEnergyTau e) * z) ^ (k + 1)|
        ≤ |a (k + 1)| * (((k + 1 : ℕ) : ℝ) * e) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = _ := by ring
  have hs : Summable fun k : ℕ => e * |a (k + 1)| := ha1.mul_left e
  calc _ ≤ ∑' k : ℕ, |a (k + 1) * (-z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
        a (k + 1) * (-(realEnergyTau e) * z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun k : ℕ =>
          a (k + 1) * (-z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
            a (k + 1) * (-(realEnergyTau e) * z) ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
          (by simpa only [Real.norm_eq_abs] using (h1.sub h2).abs)
    _ ≤ ∑' k : ℕ, e * |a (k + 1)| := by
        refine Summable.tsum_le_tsum hb ?_ hs
        exact (h1.sub h2).abs
    _ = e * ∑' k : ℕ, |a (k + 1)| := tsum_mul_left
    _ ≤ e * ∑' k : ℕ, |a k| := by
        refine mul_le_mul_of_nonneg_left ?_ he.1.le
        rw [ha.tsum_eq_zero_add]
        linarith [abs_nonneg (a 0)]


/-- The cost of A7.2 (§3.5 of SIMPLIFY-S2), with `s = s' + m` and `2m` spikes `z`:
* `2 m k log (2 / (1 + τ² r))`: the `M̂ k Λ_r / 2` term (negatives, Lemma 5);
* `4 ν m e ‖a‖₁`: the screening error (`τ`-damping of the Poisson average);
* `2 m² (log (1 - τ² r²) - log (1 - ρ²))`: the `m² [Σ(β_{τ r}) - Σ(β_ρ)]` term;
* `2 s Σ_p (S_b(-z_p) - S_b(-ρ)) = s Σ_p De(z_p, ρ)`;
* the remaining terms, all `O(m)`. -/
def spikeCost (ν e : ℝ) (a b : ℕ → ℝ) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) {M : ℕ} (z : Fin M → ℝ) : ℝ :=
  2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) +
  4 * ν * m * e * ∑' j : ℕ, |a j| +
  2 * (m : ℝ) ^ 2 * (Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) - Real.log (1 - ρ ^ 2)) +
  2 * ((s' : ℝ) + m) * ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) +
  (m : ℝ) * Real.log 2 -
  (((s' : ℝ) + m) * m / s') * (∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
  (2 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) ^ 2) -
  (4 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1)) +
  (2 * (m : ℝ) ^ 2 / s') * (ρ ^ 2 / (1 - ρ ^ 2)) +
  (4 * ((s' : ℝ) + m) * m / s') * barrierTrialS b (-ρ)

theorem cost_le {ν e r ρ : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hν : 0 < ν) {s' m : ℕ} (hs' : 0 < s') (a b : ℕ → ℝ) (ha : Summable fun k : ℕ => |a k|)
    (hρ : |ρ| < 1) (hρr : ρ ≤ realEnergyTau e ^ 2 * r)
    {k q : ℕ} (x : Fin k → ℝ) (y : Fin q → ℝ) (z : Fin (2 * m) → ℝ)
    (hx0 : ∀ i, x i ≤ 0) (hx1 : ∀ i, -1 < x i) (hy0 : ∀ j, 0 ≤ y j) (hy1 : ∀ j, y j < 1)
    (hzr : ∀ p, r ≤ z p) (hz1 : ∀ p, z p < 1) :
    (m : ℝ) * ∑ i, crossLog (x i) (-1) + spikeCostNet ν e a b s' m ρ x y z ≤
      spikeCost ν e a b s' m ρ r k z := by
  have hτ := realEnergyTau_bounds he
  have hτ' : realEnergyTau e ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2⟩
  have hs'R : (0 : ℝ) < s' := by exact_mod_cast hs'
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcard : ∀ c : ℝ, ∑ _p : Fin (2 * m), c = 2 * (m : ℝ) * c := by
    intro c; simp
  -- negatives
  have hP0 : (m : ℝ) * ∑ i, crossLog (x i) (-1) =
      ∑ p : Fin (2 * m), ∑ i, Real.log (1 - x i) := by
    have h1 : ∀ i, crossLog (x i) (-1) = 2 * Real.log (1 - x i) := by
      intro i
      unfold crossLog
      rw [show 1 + 2 * x i * (-1) + x i ^ 2 = (1 - x i) ^ 2 by ring, Real.log_pow]
      norm_num
    simp_rw [h1]
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hN : ∑ p : Fin (2 * m), ∑ i, Real.log (1 - x i) -
      ∑ p, ∑ i, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * x i)) ≤
      2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ p : Fin (2 * m), ∑ _i : Fin k, Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_le_sum fun i _ =>
            log_neg_row_le hτ' hr (hx0 i) (hx1 i) (hzr p)
      _ = _ := by simp; ring
  -- positives
  have hP : ∑ p, ∑ j, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * y j)) +
      2 * (m : ℝ) * ∑ j, (-Real.log (1 - ρ * y j)) ≤ 0 := by
    have : 2 * (m : ℝ) * ∑ j, (-Real.log (1 - ρ * y j)) =
        ∑ p : Fin (2 * m), ∑ j, (-Real.log (1 - ρ * y j)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    rw [this, ← Finset.sum_add_distrib]
    refine Finset.sum_nonpos fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonpos fun j _ => ?_
    have hz0 : 0 < z p := lt_of_lt_of_le hr.1 (hzr p)
    have := log_pos_row_le hτ' (hy0 j) (hy1 j) (hz1 p) hz0
      (le_trans hρr (mul_le_mul_of_nonneg_left (hzr p) (sq_nonneg _))) hρ
    linarith
  -- spike pairs
  have hΛ : (1 / 2 : ℝ) * ∑ p, ∑ p', Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * z p')) ≤
      2 * (m : ℝ) ^ 2 * Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) := by
    have : ∑ p, ∑ p', Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * z p')) ≤
        ∑ _p : Fin (2 * m), ∑ _p' : Fin (2 * m), Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ =>
        log_spike_pair_le hτ' hr (hzr p) (hzr p') (hz1 p) (hz1 p')
    have h2 : ∑ _p : Fin (2 * m), ∑ _p' : Fin (2 * m), Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) =
        4 * (m : ℝ) ^ 2 * Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) := by
      simp; ring
    linarith
  -- screening error
  have hS : 2 * ν * ∑ p, (barrierTrialS a (-(z p)) - barrierTrialS a (-(realEnergyTau e) * z p)) ≤
      4 * ν * m * e * ∑' j : ℕ, |a j| := by
    have hz : ∀ p, |z p| < 1 := fun p => by
      rw [abs_of_pos (lt_of_lt_of_le hr.1 (hzr p))]; exact hz1 p
    have : ∑ p, (barrierTrialS a (-(z p)) - barrierTrialS a (-(realEnergyTau e) * z p)) ≤
        ∑ _p : Fin (2 * m), e * ∑' j : ℕ, |a j| :=
      Finset.sum_le_sum fun p _ => (le_abs_self _).trans (abs_barrierTrialS_sub_le ha he (hz p))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    nlinarith [this, hν]
  -- the b-part
  have hEp : 0 ≤ (2 * (m : ℝ) ^ 2 / s') * (-Real.log (1 - ρ ^ 2)) := by
    have hm1 := mul_nonneg (abs_nonneg ρ) (sub_nonneg.2 hρ.le)
    have h1 : 0 < 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ, hm1]
    have h2 : Real.log (1 - ρ ^ 2) ≤ 0 := Real.log_nonpos h1.le (by nlinarith [sq_nonneg ρ])
    exact mul_nonneg (by positivity) (by linarith)
  have hDe : ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) =
      ∑ p, barrierTrialS b (-(z p)) - 2 * (m : ℝ) * barrierTrialS b (-ρ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  have hsub : ∑ p, (barrierTrialS a (-(z p)) - barrierTrialS a (-(realEnergyTau e) * z p)) =
      ∑ p, barrierTrialS a (-(z p)) - ∑ p, barrierTrialS a (-(realEnergyTau e) * z p) :=
    Finset.sum_sub_distrib _ _
  rw [hsub] at hS
  have key : spikeCost ν e a b s' m ρ r k z -
      ((m : ℝ) * ∑ i, crossLog (x i) (-1) + spikeCostNet ν e a b s' m ρ x y z) =
      (2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) -
        (∑ p : Fin (2 * m), ∑ i, Real.log (1 - x i) -
          ∑ p, ∑ i, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * x i)))) +
      (4 * ν * m * e * ∑' j : ℕ, |a j| -
        2 * ν * (∑ p, barrierTrialS a (-(z p)) -
          ∑ p, barrierTrialS a (-(realEnergyTau e) * z p))) +
      (2 * (m : ℝ) ^ 2 * Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) -
        (1 / 2 : ℝ) * ∑ p, ∑ p', Real.log (1 - (realEnergyTau e * z p) *
          (realEnergyTau e * z p'))) +
      (-(∑ p, ∑ j, Real.log (1 - (realEnergyTau e * z p) * (realEnergyTau e * y j)) +
        2 * (m : ℝ) * ∑ j, (-Real.log (1 - ρ * y j)))) +
      (2 * (m : ℝ) ^ 2 / s') * (-Real.log (1 - ρ ^ 2)) := by
    unfold spikeCost spikeCostNet
    rw [hP0, hsub, hDe]
    have hs0 : (s' : ℝ) ≠ 0 := hs'R.ne'
    field_simp
    ring
  linarith [key, hN, hS, hΛ, hP, hEp]

/-- **A7.2 (`spike_compare`).**  With the `2m` spikes `z` at depth `≥ r` (their true positions in
`NumB` and `DenB`), the negatives `x ≤ 0`, the rest positives `y ≥ 0`, and the removal scale
`ρ ≤ τ² r` satisfying (P'):
`m log φ(-1) + log heineZ s' (φψ_r) - log heineZ s' ψ_r ≤ NumB - DenB + J3err + Cost`. -/
theorem spike_compare {ν e c' d : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hc' : c' ∈ Ioc (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) {s' m : ℕ} (hs' : 0 < s')
    (hsν : (s' : ℝ) ≤ ν)
    (a r : ℕ → ℝ) (ha : Summable fun k => |a k|)
    (hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2)
    (hra : Summable fun k : ℕ => r (k + 1) * a (k + 1)) (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * realEnergyTau e ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x))
    {ℓ : ℝ} (hℓ : ∀ x ∈ Icc (-1 : ℝ) 1, Qref x - 2 * barrierTrialT a x ≤ ℓ)
    {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) {ρ : ℝ} (hρ : |ρ| < 1)
    (hρd : ρ ≤ realEnergyTau e ^ 2 * d) {c1 : ℝ} (hc1 : 0 < c1)
    (hP : ∀ u ∈ Icc (-1 : ℝ) 1,
      (s' : ℝ) * c1 ≤ ((s' + m : ℕ) : ℝ) * chebPs b u - m * chebPs (poisSeq ρ) u)
    {k q : ℕ} (x : Fin k → ℝ) (y : Fin q → ℝ) (z : Fin (2 * m) → ℝ)
    (hx1 : ∀ i, -1 < x i) (hy : ∀ j, |y j| ≤ 1 - c') (hz : ∀ p, |z p| < 1)
    (hx0 : ∀ i, x i ≤ 0) (hy0 : ∀ j, 0 ≤ y j) (hzd : ∀ p, d ≤ z p)
    {fN fD : ℝ → ℝ}
    (hfN : ∀ u ∈ Icc (-1 : ℝ) 1,
      fN u = Real.exp (∑ i, crossLog (x i) u - ∑ j, crossLog (y j) u))
    (hfD : ∀ u ∈ Icc (-1 : ℝ) 1, fD u = Real.exp (-∑ j, crossLog (y j) u)) :
    (m : ℝ) * ∑ i, crossLog (x i) (-1) + (Real.log (heineZ s' fN) - Real.log (heineZ s' fD)) ≤
      spikeNumB ν e a r ℓ (s' + m) x y z - spikeDenB b (s' + m) y z +
        (s' : ℝ) * (((k + q : ℕ) : ℝ) * (4 * e / c')) + spikeCost ν e a b s' m ρ d k z := by
  have hx : ∀ i, |x i| < 1 := fun i => abs_lt.mpr ⟨hx1 i, by linarith [hx0 i]⟩
  have h1 := spike_compare_exact hν he hc' hs' hsν a r ha hr hra Qref hQ hℓ hb hρ hc1 hP x y z hx
    hy hz hfN hfD
  have hy1 : ∀ j, y j < 1 := fun j => by
    have := (abs_le.mp (hy j)).2
    linarith [hc'.1]
  have hz1 : ∀ p, z p < 1 := fun p => (abs_lt.mp (hz p)).2
  have h2 := cost_le he hd hν hs' a b ha hρ hρd x y z hx0 hx1 hy0 hy1 hzd hz1
  linarith


end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.crossLog_le_dilate
#print axioms CatalanMeasure.Signed.cross_field_sub_dilate_le_one_sided
#print axioms CatalanMeasure.Signed.log_heineZ_le
#print axioms CatalanMeasure.Signed.jTwo_diff
#print axioms CatalanMeasure.Signed.screening
#print axioms CatalanMeasure.Signed.spike_compare_exact
#print axioms CatalanMeasure.Signed.cost_le
#print axioms CatalanMeasure.Signed.spike_compare
#print axioms CatalanMeasure.Signed.integral_denQs_Q
#print axioms CatalanMeasure.Signed.energy_bRed
#print axioms CatalanMeasure.Signed.sq_bRed
#print axioms CatalanMeasure.Signed.den_diff_alg
#print axioms CatalanMeasure.Signed.abs_barrierTrialS_sub_le
