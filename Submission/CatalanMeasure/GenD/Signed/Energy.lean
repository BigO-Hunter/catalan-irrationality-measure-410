module

public import Submission.CatalanMeasure.GenD.Signed.TiltedTangent
public import Submission.CatalanMeasure.GenD.Signed.CrossDilation
public import Submission.CatalanMeasure.GenD.Signed.ArcsineDenominator
public import Submission.CatalanMeasure.GenD.Signed.ReflectionEnergy
public import Submission.CatalanMeasure.GenD.Signed.RatioIdentity
public import Submission.CatalanMeasure.GenD.Signed.PickDet
public import Submission.CatalanMeasure.GenD.Signed.LemmaT
public import Submission.CatalanMeasure.GenD.Signed.LemmaK
public import Submission.CatalanMeasure.FreePopulationFields
public import Submission.CatalanMeasure.Parametric.GroupedFieldAssembly
public import Submission.CatalanMeasure.PinSupDual

/-!
# The signed second-sheet energy bound: assembly layer (Phase 1, theorem-only)

Sibling of `Analytic.second_energy`.  See `NOTES-E.md` in the Theorem A plan folder.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-- Error of the row-Vandermonde-free pin bound. -/
def pinZeroError (ν e : ℝ) : ℝ :=
  (Real.log 2 - Real.log e) / (2 * ν) + (Real.log 2 - 2 * Real.log e) / ν + 12 * e

/-- The pin interaction without the row Vandermonde (`k = 0`), by the 532 lemmas. -/
theorem pin_zero_canonical {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ}
    (hp : (p : ℝ) ≤ ν) {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) :
    pinOffDiagonalInteraction ν 0 x s ≤ -((p : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq v / 2 + (∑ i, -barrierTrialS v (x i)) / ν +
      (∑ j, 2 * barrierTrialT v (s j)) / ν -
      (∑ i, Real.log (1 - x i)) / (2 * ν ^ 2) - (∑ j, Real.log (1 - s j)) / ν ^ 2 +
      4 * e * (∑' j, |v j|) + pinZeroError ν e := by
  have h0 : Summable (fun j : ℕ => |(fun _ : ℕ => (0:ℝ)) j|) := by simp
  have hint := pinOffDiagonalInteraction_le_damped hν (le_refl (0:ℝ)) he hx hs hxi hsi
  have hpow := pin_power_diagonal_sum hν he hp hx
  have hsig := pin_sigma_diagonal_sum hν he hp hs
  have hd := pinDampedInteraction_le_canonicalTrials hν (le_refl (0:ℝ)) he hp hx hs
    (fun _ => 0) v h0 hv
  have hc : ((p.choose 2 : ℕ) : ℝ) ≤ ν ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hp, hν, (Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hsq : (p : ℝ) ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg p) hp 2
  have he0 := he.1
  have hpair : (4 * 0 + 12) * e * ((p.choose 2 : ℕ) : ℝ) / ν ^ 2 + 6 * e * (p : ℝ) ^ 2 / ν ^ 2
      ≤ 12 * e := by
    have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 12 * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * e by positivity)
    rw [← add_div, div_le_iff₀ (sq_pos_of_pos hν)]
    nlinarith only [h1, h2]
  unfold pinZeroError
  simp only [zero_mul, mul_zero, zero_sub, sub_zero, zero_div, zero_add, add_zero] at hint hd hpair
  simp only [mul_pow] at hint
  simp only [neg_div] at hpow hsig
  ring_nf at hint hd hpow hsig hpair ⊢
  linarith only [hint, hd, hpow, hsig, hpair]

/-! ### Row Vandermonde through D7.1 -/

section Rows

open CatalanMeasure.Signed.ReflectionEnergy

/-- Folded kernel equals `-log |x - y|` for nonzero reals (opposite signs: `a + b = |x - y|`). -/
theorem Kt_abs_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Kt (decide (0 < x)) (decide (0 < y)) |x| |y| = -Real.log |x - y| := by
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · have h1 : decide (0 < x) = false := by simp [not_lt.mpr hx'.le]
    have h2 : decide (0 < y) = false := by simp [not_lt.mpr hy'.le]
    simp only [Kt, h1, h2, if_true, abs_of_neg hx', abs_of_neg hy']
    rw [show -x - -y = -(x - y) by ring, abs_neg]
  · have h1 : decide (0 < x) = false := by simp [not_lt.mpr hx'.le]
    have h2 : decide (0 < y) = true := by simp [hy']
    simp only [Kt, h1, h2, Bool.false_eq_true, if_false, abs_of_neg hx', abs_of_pos hy']
    rw [abs_of_neg (by linarith : x - y < 0)]
    ring_nf
  · have h1 : decide (0 < x) = true := by simp [hx']
    have h2 : decide (0 < y) = false := by simp [not_lt.mpr hy'.le]
    simp only [Kt, h1, h2, Bool.true_eq_false, if_false, abs_of_pos hx', abs_of_neg hy']
    rw [abs_of_pos (by linarith : 0 < x - y)]
    ring_nf
  · have h1 : decide (0 < x) = true := by simp [hx']
    have h2 : decide (0 < y) = true := by simp [hy']
    simp only [Kt, h1, h2, if_true, abs_of_pos hx', abs_of_pos hy']

/-- Reduce the double sum over `i ≠ j` of a symmetric function to the ordered pairs. -/
theorem sum_offdiag_eq_two_mul {p : ℕ} (g : Fin p → Fin p → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, if i = j then 0 else g i j) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have h1 : ∀ i : Fin p, (∑ j, if i = j then 0 else g i j) =
      (∑ j ∈ Finset.Ioi i, g i j) + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have hu : (Finset.univ.erase i) = Finset.Ioi i ∪ Finset.Iio i := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
        Finset.mem_Iio]
      exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim ne_of_gt ne_of_lt⟩
    have hd : Disjoint (Finset.Ioi i) (Finset.Iio i) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2
      exact lt_asymm h1 h2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add, hu,
      Finset.sum_union hd]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (Finset.mem_Ioi.mp hj).ne]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (Finset.mem_Iio.mp hj).ne']
  simp only [h1, Finset.sum_add_distrib]
  have h2 : (∑ i : Fin p, ∑ j ∈ Finset.Iio i, g i j) = ∑ j : Fin p, ∑ i ∈ Finset.Ioi j, g i j :=
    Finset.sum_comm' (by intro x y; simp [and_comm])
  rw [h2]
  have : (∑ j : Fin p, ∑ i ∈ Finset.Ioi j, g i j) = ∑ j : Fin p, ∑ i ∈ Finset.Ioi j, g j i :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hg i j
  rw [this]; ring

/-- **A signed reference** `P - N` (the paper's `c_r = t μ_r + (α/2) σ_r` as a difference of two
nonnegative measures per species; Theorem 7.1 needs no sign of `c_r`). -/
structure SRef where
  P : Bool → Measure ℝ
  N : Bool → Measure ℝ

/-- Admissible signed reference: both parts of density `≤ C` on `(0,1)`, and `|N| ≤ 1`. -/
structure SRef.OK (μ : SRef) (C : ℝ) : Prop where
  hP : ∀ τ, BD (μ.P τ) C
  hN : ∀ τ, BD (μ.N τ) C
  hNm : ∑ τ, (μ.N τ).real univ ≤ 1

/-- The total (signed) mass `|P| - |N|`. -/
def SRef.mass (μ : SRef) : ℝ := ∑ τ, (μ.P τ).real univ - ∑ τ, (μ.N τ).real univ

/-- The row field of the reference: `x ↦ ∑_τ ∫ K(x, y) d(P_τ - N_τ)(y)` in folded coordinates. -/
def rowRef (μ : SRef) (x : ℝ) : ℝ :=
  ∑ τ, (∫ y, Kt (decide (0 < x)) τ |x| y ∂(μ.P τ) - ∫ y, Kt (decide (0 < x)) τ |x| y ∂(μ.N τ))

/-- The constant `∬ K d(P - N) d(P - N)` of the reference. -/
def refEnergy (μ : SRef) : ℝ :=
  pairI μ.P μ.P Kt - pairI μ.P μ.N Kt - pairI μ.N μ.P Kt + pairI μ.N μ.N Kt

theorem err_W_mono {W n C ρ : ℝ} (hW : 0 ≤ W) (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hC : 0 ≤ C) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    12 * (W + n) * C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))) + 2 * (1 - ρ) * (2 * (W + n)) ^ 2 ≤
      12 * (W + 1) * C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))) + 2 * (1 - ρ) * (2 * (W + 1)) ^ 2 := by
  have hε : 0 ≤ 1 - ρ := by linarith
  have hL : 0 ≤ Real.log (1 / (1 - ρ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have h1 : 0 ≤ C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))) := by positivity
  have h2 : (2 * (W + n)) ^ 2 ≤ (2 * (W + 1)) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hε, mul_le_mul_of_nonneg_right (by linarith : W + n ≤ W + 1) h1]

/-- **The rows' weighted Vandermonde through D7.1**: with positive node weights `w` of total
mass that of the signed reference `μ = P - N`, the weighted self-energy
`Σ_{i<j} w_i w_j log|x_j - x_i|` is bounded by the `L`-terms against `μ`, the weighted reference
field and constant, the weighted diagonal cost and the explicit error (at `W + 1 ≥ W + |N|`). -/
theorem rows_vandermonde_le_w {p : ℕ} (x : Fin p → ℝ) (w : Fin p → ℝ) (hw : ∀ i, 0 < w i)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hxi : Function.Injective x)
    (μ : SRef) {C : ℝ} (h : μ.OK C) (hC : 0 ≤ C)
    (hmass : ∑ i, w i = μ.mass) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∑ i, ∑ j ∈ Finset.Ioi i, w i * w j * Real.log |x j - x i|) ≤
      -(1 / 2) * (∑ τ, Lpart w (fun i => |x i|) (fun i => decide (0 < x i)) μ.P μ.N ρ τ)
      + (1 / 2) * (∑ i, w i ^ 2 * (-Real.log |x i| + Real.log (1 / (1 - ρ))))
      + (1 / 2) * (12 * (∑ i, w i + 1) * C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))
          + 2 * (1 - ρ) * (2 * (∑ i, w i + 1)) ^ 2)
      - (∑ i, w i * rowRef μ (x i)) + (1 / 2) * refEnergy μ := by
  have ha : ∀ i, |x i| ∈ Ioo (0 : ℝ) 1 := fun i =>
    ⟨abs_pos.mpr (hx0 i), abs_lt.mpr ⟨(hx i).1, (hx i).2⟩⟩
  have hinj : ∀ i j, i ≠ j → decide (0 < x i) = decide (0 < x j) → |x i| ≠ |x j| := by
    intro i j hij hs habs
    apply hij
    apply hxi
    have hs' : (0 < x i ↔ 0 < x j) := by simpa using hs
    rcases lt_or_gt_of_ne (hx0 i) with h1 | h1
    · have h2 : x j < 0 := lt_of_le_of_ne (not_lt.mp (fun hh => by
        have := hs'.mpr hh; linarith)) (hx0 j)
      rw [abs_of_neg h1, abs_of_neg h2] at habs; linarith
    · have h2 : 0 < x j := hs'.mp h1
      rw [abs_of_pos h1, abs_of_pos h2] at habs; exact habs
  have hm : ∑ i, w i + ∑ τ, (μ.N τ).real univ = ∑ τ, (μ.P τ).real univ := by
    rw [hmass]; unfold SRef.mass; ring
  have hD := reflection_energy (w := w) (a := fun i => |x i|)
    (σ := fun i => decide (0 < x i)) (P := μ.P) (N := μ.N) hw ha hinj h.hP h.hN hC hm hρ0 hρ1
  unfold Ioff Ex at hD
  simp only [Kt_abs_eq (hx0 _) (hx0 _)] at hD
  have hoff := sum_offdiag_eq_two_mul (p := p)
    (fun i j => w i * w j * -Real.log |x i - x j|)
    (fun i j => by rw [abs_sub_comm]; ring)
  rw [hoff] at hD
  have e1 : (∑ i, ∑ j ∈ Finset.Ioi i, w i * w j * -Real.log |x i - x j|) =
      -(∑ i, ∑ j ∈ Finset.Ioi i, w i * w j * Real.log |x j - x i|) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_sub_comm]; ring
  have e2 : rowI w (fun i => |x i|) (fun i => decide (0 < x i)) μ.P Kt -
      rowI w (fun i => |x i|) (fun i => decide (0 < x i)) μ.N Kt = ∑ i, w i * rowRef μ (x i) := by
    unfold rowI rowRef
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [e1] at hD
  have hW : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hn0 : 0 ≤ ∑ τ, (μ.N τ).real univ := Finset.sum_nonneg (fun τ _ => measureReal_nonneg)
  have hmono := err_W_mono hW hn0 h.hNm hC hρ0 hρ1
  unfold refEnergy
  linarith only [hD, e2, hmono]

/-- The rows' Vandermonde through D7.1: with weights `1/ν`, the self-energy of the rows is
bounded by the `L`-terms against the reference `μ`, the reference field and constant, the diagonal
cost and the explicit error. -/
theorem rows_vandermonde_le {ν : ℝ} (hν : 0 < ν) {p : ℕ} (x : Fin p → ℝ)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hxi : Function.Injective x)
    (μ : SRef) {C : ℝ} (h : μ.OK C) (hC : 0 ≤ C)
    (hmass : (p : ℝ) / ν = μ.mass) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2 ≤
      -(1 / 2) * (∑ τ, Lpart (fun _ : Fin p => 1 / ν) (fun i => |x i|)
          (fun i => decide (0 < x i)) μ.P μ.N ρ τ)
      + (1 / 2) * (∑ i : Fin p, (1 / ν) ^ 2 * (-Real.log |x i| + Real.log (1 / (1 - ρ))))
      + (1 / 2) * (12 * ((p : ℝ) / ν + 1) * C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))
          + 2 * (1 - ρ) * (2 * ((p : ℝ) / ν + 1)) ^ 2)
      - (∑ i, rowRef μ (x i)) / ν + (1 / 2) * refEnergy μ := by
  have hw : ∀ _i : Fin p, (0 : ℝ) < 1 / ν := fun _ => by positivity
  have hsum : ∑ _i : Fin p, (1 / ν) = (p : ℝ) / ν := by
    simp [div_eq_mul_inv]
  have h := rows_vandermonde_le_w x (fun _ => 1 / ν) hw hx0 hx hxi μ h hC
    (by rw [hsum]; exact hmass) hρ0 hρ1
  rw [hsum] at h
  have e1 : (∑ i, ∑ j ∈ Finset.Ioi i, 1 / ν * (1 / ν) * Real.log |x j - x i|) =
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have e2 : (∑ i, 1 / ν * rowRef μ (x i)) = (∑ i, rowRef μ (x i)) / ν := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, e2] at h
  exact h

/-- **Ordered pairs of an appended list**, for values in any type. -/
theorem sum_Ioi_append_gen {β : Type*} {p m : ℕ} (H : β → β → ℝ) (x : Fin p → β)
    (y : Fin m → β) :
    ∑ a : Fin (p + m), ∑ b ∈ Finset.Ioi a, H (Fin.append x y a) (Fin.append x y b) =
      (∑ i : Fin p, ∑ i' ∈ Finset.Ioi i, H (x i) (x i')) +
        (∑ i : Fin p, ∑ j : Fin m, H (x i) (y j)) +
        ∑ j : Fin m, ∑ j' ∈ Finset.Ioi j, H (y j) (y j') := by
  have hI : ∀ {n : ℕ} (f : Fin n → Fin n → ℝ),
      ∑ a : Fin n, ∑ b ∈ Finset.Ioi a, f a b =
        ∑ a : Fin n, ∑ b : Fin n, if a < b then f a b else 0 := by
    intro n f
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp
  rw [hI (fun a b => H (Fin.append x y a) (Fin.append x y b)), hI (fun i i' => H (x i) (x i')),
    hI (fun j j' => H (y j) (y j'))]
  have h1 : ∀ (i i' : Fin p), (Fin.castAdd m i < Fin.castAdd m i') ↔ i < i' := by
    intro i i'
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h2 : ∀ (i : Fin p) (j : Fin m), Fin.castAdd m i < Fin.natAdd p j := by
    intro i j
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : ∀ (i : Fin p) (j : Fin m), ¬ (Fin.natAdd p j < Fin.castAdd m i) := by
    intro i j
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h4 : ∀ (j j' : Fin m), (Fin.natAdd p j < Fin.natAdd p j') ↔ j < j' := by
    intro j j'
    simp only [Fin.lt_def, Fin.val_natAdd]
    omega
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, h1, h2, h3, h4,
    ite_true, ite_false, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  ring

/-- The weighted Vandermonde of an appended list of (weight, node) pairs splits into the two
blocks and the cross term. -/
theorem wvand_append {p m : ℕ} (w x : Fin p → ℝ) (w' y : Fin m → ℝ) :
    ∑ a : Fin (p + m), ∑ b ∈ Finset.Ioi a, Fin.append w w' a * Fin.append w w' b *
        Real.log |Fin.append x y b - Fin.append x y a| =
      (∑ i, ∑ i' ∈ Finset.Ioi i, w i * w i' * Real.log |x i' - x i|) +
        (∑ i, ∑ j, w i * w' j * Real.log |y j - x i|) +
        ∑ j, ∑ j' ∈ Finset.Ioi j, w' j * w' j' * Real.log |y j' - y j| := by
  have hpair : ∀ a : Fin (p + m), (Fin.append w w' a, Fin.append x y a) =
      Fin.append (fun i => (w i, x i)) (fun j => (w' j, y j)) a := by
    intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  have h := sum_Ioi_append_gen (fun u v : ℝ × ℝ => u.1 * v.1 * Real.log |v.2 - u.2|)
    (fun i => (w i, x i)) (fun j => (w' j, y j))
  simp only [← hpair] at h
  exact h

/-- With constant weights the weighted Vandermonde is the Vandermonde. -/
theorem wvand_const {p : ℕ} (c : ℝ) (x : Fin p → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, (fun _ : Fin p => c) i * (fun _ : Fin p => c) j *
        Real.log |x j - x i| = c ^ 2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The cross term with constant weights. -/
theorem wcross_const {p m : ℕ} (c c' : ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    ∑ i, ∑ j, (fun _ : Fin p => c) i * (fun _ : Fin m => c') j * Real.log |y j - x i| =
      (c * c') * ∑ i, ∑ j, Real.log |y j - x i| := by
  simp only [Finset.mul_sum]

end Rows

/-! ### The weighted Chebyshev tangent (the `η`-share of the row energy)

For node weights `w ≥ 0` of total mass `W ≤ 1`, the weighted Vandermonde is bounded through the
damped Chebyshev expansion of `log |x - y|` by the tangent plane at a trial sequence `u`
(`energy_tangent_of_hasSum`): field `-2 w_i T_u(x_i)`, constant `‖u‖² - W² log 2 / 2`, and the
diagonal and damping costs.  With `u = 0` it is the Chebyshev–Hadamard bound of PROOF-A §17.40. -/

section CosTangent

/-- The weighted damped Chebyshev moment of the nodes. -/
def cosMomW (e : ℝ) {p : ℕ} (w x : Fin p → ℝ) (k : ℕ) : ℝ :=
  ∑ i, w i * (realEnergyTau e ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (x i))

theorem cosMomW_hasSum_sq {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (w x : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => cosMomW e w x k ^ 2 / (k : ℝ))
      (-((∑ i, ∑ j, w i * w j * realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) +
        (∑ i, w i) ^ 2 * Real.log 2) / 2) := by
  have ht := realEnergyTau_bounds he
  have hr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [ht.1, ht.2]
  have hseries : HasSum (fun k : ℕ => ∑ i, ∑ j, w i * w j *
      (2 * (realEnergyTau e ^ 2) ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (x i) *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ)))
      (∑ i, ∑ j, w i * w j *
        (-realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j) - Real.log 2)) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (energy_hasSum_cosine_kernel hr ⟨(hx i).1.le, (hx i).2.le⟩
        ⟨(hx j).1.le, (hx j).2.le⟩).mul_left _
  convert hseries.mul_left (1 / 2) using 1
  · funext k
    unfold cosMomW
    rw [sq, Finset.sum_mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm 2 k, pow_mul]
    ring
  · have hW : (∑ i, w i) ^ 2 = ∑ i, ∑ j, w i * w j := by rw [sq, Finset.sum_mul_sum]
    rw [hW]
    simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul]
    ring

/-- **The weighted Chebyshev tangent.** -/
theorem cos_tangent_w {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hxi : Function.Injective x) (w : Fin p → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≤ 1) (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (∑ i, ∑ j ∈ Finset.Ioi i, w i * w j * Real.log |x j - x i|) ≤
      barrierTrialNormSq u - 2 * (∑ i, w i * barrierTrialT u (x i)) -
        (1 / 2) * (∑ i, w i) ^ 2 * Real.log 2 +
        (1 / 2) * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) * (∑ i, w i ^ 2) +
        2 * e * (∑ i, w i) * (∑' k, |u k|) + 2 * e * (∑ i, w i) ^ 2 := by
  have ht := realEnergyTau_bounds he
  have hr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [ht.1, ht.2]
  have hxI : ∀ i, x i ∈ Icc (-1 : ℝ) 1 := fun i => ⟨(hx i).1.le, (hx i).2.le⟩
  set K : Fin p → Fin p → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j) with hK
  set W : ℝ := ∑ i, w i with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => hw i
  -- pairwise damping
  have hpair : (∑ i, ∑ j ∈ Finset.Ioi i, w i * w j * Real.log |x j - x i|) ≤
      ∑ i, ∑ j ∈ Finset.Ioi i, (w i * w j * K i j + 4 * e * (w i * w j)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
    have h1 := realEnergy_cosine_tau_le he (hxI i) (hxI j) (fun h => hij (hxi h))
    rw [abs_sub_comm] at h1
    have hww : 0 ≤ w i * w j := mul_nonneg (hw i) (hw j)
    have := mul_le_mul_of_nonneg_left h1 hww
    simp only [hK]
    nlinarith [this]
  -- symmetric sums
  have hKs : ∀ i j, w i * w j * K i j = w j * w i * K j i := by
    intro i j
    simp only [hK]
    rw [realEnergyCosineKernel_symm hr (hxI i) (hxI j)]
    ring
  have hS1 := energy_sum_pairs_of_symmetric p (fun i j => w i * w j * K i j) hKs
  have hS2 := energy_sum_pairs_of_symmetric p (fun i j => w i * w j) (fun i j => mul_comm _ _)
  have hWW : ∑ i, ∑ j, w i * w j = W ^ 2 := by rw [hWdef, sq, Finset.sum_mul_sum]
  have hdiag2 : 0 ≤ ∑ i, w i * w i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  -- the series and the tangent
  set a : ℕ → ℝ := cosMomW e w x with ha
  have hS := cosMomW_hasSum_sq he w x hx
  have hS' : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i, ∑ j, w i * w j * K i j) + W ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff (f := fun k : ℕ => a k ^ 2 / (k : ℝ)) 1).2
    simpa using hS
  have habs : ∀ k, |a k| ≤ 1 := by
    intro k
    simp only [ha, cosMomW]
    calc |∑ i, w i * (realEnergyTau e ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (x i))|
        ≤ ∑ i, |w i * (realEnergyTau e ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (x i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hw i), abs_mul, abs_pow, abs_of_pos ht.1]
          have h1 : realEnergyTau e ^ k ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
          have h2 := energy_chebyshev_abs_le_one k (hxI i)
          have h3 : realEnergyTau e ^ k * |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (x i)| ≤ 1 :=
            (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
          exact (mul_le_mul_of_nonneg_left h3 (hw i)).trans_eq (mul_one _)
      _ ≤ 1 := hW
  have htan := energy_tangent_of_hasSum u a hu zero_le_one habs hS'
  -- the trial moment as a sum of damped trial fields
  have hT : HasSum (fun k : ℕ => u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ))
      (∑ i, w i * realEnergyTrialTau u e (x i)) := by
    have h := hasSum_sum (s := Finset.univ) fun i _ =>
      (realEnergyTrialTau_summable u hu he (hx i)).hasSum.mul_left (w i)
    convert h using 1
    · funext k
      simp only [ha, cosMomW, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rfl
  rw [hT.tsum_eq] at htan
  -- damping of the trial field
  have hdamp : ∑ i, w i * barrierTrialT u (x i) - e * (∑' k, |u k|) * W ≤
      ∑ i, w i * realEnergyTrialTau u e (x i) := by
    have : ∀ i, w i * (barrierTrialT u (x i) - e * (∑' k, |u k|)) ≤
        w i * realEnergyTrialTau u e (x i) := fun i =>
      mul_le_mul_of_nonneg_left (by
        have := (abs_le.mp (realEnergyTrialTau_sub_le u hu he (hx i))).1
        linarith) (hw i)
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    simp only [mul_sub, Finset.sum_sub_distrib] at hs
    rw [hWdef, Finset.mul_sum]
    have e1 : ∑ i, w i * (e * ∑' k, |u k|) = ∑ i, e * (∑' k, |u k|) * w i :=
      Finset.sum_congr rfl fun i _ => by ring
    linarith [hs, e1]
  -- the diagonal
  have hdiag : -(∑ i, w i * w i * K i i) ≤
      (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) * (∑ i, w i ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := realEnergy_cosine_tau_diagonal_lower he (hxI i)
    have hww : 0 ≤ w i * w i := mul_self_nonneg _
    simp only [hK]
    nlinarith [mul_le_mul_of_nonneg_left h1 hww]
  have hsq : ∑ i, w i ^ 2 = ∑ i, w i * w i := Finset.sum_congr rfl fun i _ => sq _
  have hpos : 0 ≤ ∑' k, |u k| := tsum_nonneg fun _ => abs_nonneg _
  have he0 : 0 ≤ e := he.1.le
  have hlin : ∑ i, ∑ j ∈ Finset.Ioi i, (w i * w j * K i j + 4 * e * (w i * w j)) =
      (∑ i, ∑ j ∈ Finset.Ioi i, w i * w j * K i j) +
        4 * e * ∑ i, ∑ j ∈ Finset.Ioi i, w i * w j := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hlin] at hpair
  beta_reduce at hS1 hS2
  have hpp : 0 ≤ e * (∑ i, w i * w i) := mul_nonneg he0 hdiag2
  have h4 : 4 * e * (∑ i, ∑ j ∈ Finset.Ioi i, w i * w j) =
      2 * e * W ^ 2 - 2 * e * (∑ i, w i * w i) := by
    linear_combination (-2 * e) * hS2 + (2 * e) * hWW
  have hU : 2 * e * (∑' k, |u k|) * W = 2 * (e * (∑' k, |u k|) * W) := by ring
  linarith only [hpair, hS1, h4, htan, hdamp, hdiag, hsq, hpp, hU]

end CosTangent

/-! ### Cross tilt against a reference (J2 with a reference field)

The tilt is `crossBeta - r`, where `r` is the tilt of a reference measure (a data sequence) and
`Qref` its τ-damped field, `Qref u = Σ_k r_k τ^k T_k(u)`.  The reference field is carried untilted,
so that the Frostman bound `Qref - 2 T_a ≤ Sup` is available at the particles. -/

/-- The Λ term of the configuration minus the reference, dilated by `τ`. -/
def crossTiltNormRef {n : ℕ} (τ : ℝ) (w y : Fin n → ℝ) (r : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (crossBeta τ w y (k + 1) - r (k + 1)) ^ 2 / 4

theorem pair_log_add_cross_le_tilted_ref {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s n : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1)
    (r : ℕ → ℝ) (hr : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2))
    (hra : Summable (fun k : ℕ => r (k + 1) * a (k + 1)))
    (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * realEnergyTau e ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x)) :
    (∑ i : Fin s, ∑ j ∈ Finset.Ioi i, Real.log |u j - u i|) / ν ^ 2 +
        (∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν ≤
      -(1 / 2 : ℝ) * ((s : ℝ) / ν) ^ 2 * Real.log 2 + barrierTrialNormSq a +
        (∑ i, (Qref (u i) - 2 * barrierTrialT a (u i))) / ν +
        (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l) -
          ∑' k : ℕ, r (k + 1) * a (k + 1)) +
        crossTiltNormRef (realEnergyTau e) w y r + trialPairError ν e a := by
  have hτ := realEnergyTau_bounds he
  have hτ' : realEnergyTau e ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2⟩
  have hrx := population_cosine_regularization hν he hs hu hui
  have hS : HasSum (fun k : ℕ => pinCosineMoment ν e u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin s, ∑ j : Fin s,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (u i) (u j)) / ν ^ 2 +
        ((s : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e u k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hu
  have hΛs := crossBeta_summable hτ' w y hy
  have hβs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      crossBeta (realEnergyTau e) w y (k + 1) ^ 2) := by
    refine (hΛs.mul_left 4).congr (fun k => ?_)
    have := crossBeta_sq (realEnergyTau e) w y (k + 1) (Nat.succ_pos k)
    linarith only [this]
  have hβ' : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (crossBeta (realEnergyTau e) w y (k + 1) - r (k + 1)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => ?_) ((hβs.mul_left 2).add (hr.mul_left 2))
    have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_nonneg hk (sq_nonneg (crossBeta (realEnergyTau e) w y (k + 1) +
      r (k + 1)))]
  have ht := tilted_energy_tangent a (pinCosineMoment ν e u)
    (fun k => crossBeta (realEnergyTau e) w y k - r k) ha hS hβ'
  have hcross := crossBeta_pairing_hasSum hν he u hu w y hy
  have href : HasSum (fun k : ℕ => r (k + 1) * pinCosineMoment ν e u (k + 1))
      ((∑ i, Qref (u i)) / ν) := by
    have hsum := (hasSum_sum (s := Finset.univ) (fun i _ => hQ (u i)
      ⟨(hu i).1.le, (hu i).2.le⟩)).div_const ν
    convert hsum using 1
    funext k
    unfold pinCosineMoment
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpair : HasSum (fun k : ℕ => (crossBeta (realEnergyTau e) w y (k + 1) - r (k + 1)) *
      pinCosineMoment ν e u (k + 1))
      ((∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν -
        (∑ i, Qref (u i)) / ν) := by
    convert hcross.sub href using 1
    funext k; ring
  have hba : HasSum (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1))
      (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l)) := by
    have hl : ∀ l, HasSum (fun k : ℕ => a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
        ((k + 1 : ℕ) : ℝ)) (barrierTrialS a (-(realEnergyTau e) * y l)) := by
      intro l
      refine (barrierTrialS_summable a ha ?_).hasSum
      rw [abs_mul, abs_neg, abs_of_pos hτ.1]
      calc _ ≤ 1 * |y l| := mul_le_mul_of_nonneg_right hτ.2.le (abs_nonneg _)
        _ ≤ 1 := by linarith [hy l]
    have hsum := hasSum_sum (s := Finset.univ)
      (fun l _ => ((hl l).mul_left (w l)).mul_left (-2 : ℝ))
    have hconv : ∀ k : ℕ, crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1) =
        ∑ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) := by
      intro k
      have h1 : ∀ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) = (-2 * (-1) ^ (k + 1) * realEnergyTau e ^ (k + 1) *
            a (k + 1) / ((k + 1 : ℕ) : ℝ)) * (w l * y l ^ (k + 1)) := by
        intro l; rw [mul_pow, neg_pow]; ring
      simp only [h1]
      rw [← mul_sum]
      unfold crossBeta
      ring
    have e1 : (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1)) =
        fun k : ℕ => ∑ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) := funext hconv
    rw [e1]
    convert hsum using 1
    rw [mul_sum]
  have hba' : HasSum (fun k : ℕ => (crossBeta (realEnergyTau e) w y (k + 1) - r (k + 1)) *
      a (k + 1)) (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l) -
        ∑' k : ℕ, r (k + 1) * a (k + 1)) := by
    convert hba.sub hra.hasSum using 1
    funext k; ring
  rw [hpair.tsum_eq, hba'.tsum_eq, (pin_hasSum_trialTau_average a ha ν he hu).tsum_eq] at ht
  have hq : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (crossBeta (realEnergyTau e) w y (k + 1) -
      r (k + 1)) ^ 2 / 4) = crossTiltNormRef (realEnergyTau e) w y r := rfl
  rw [hq] at ht
  have hav := pin_average_le_of_le_add hν hs
    (fun i => -2 * realEnergyTrialTau a e (u i))
    (fun i => -2 * barrierTrialT a (u i))
    (c := 2 * e * (∑' k, |a k|))
    (mul_nonneg (mul_nonneg (by norm_num) he.1.le) (tsum_nonneg fun _ => abs_nonneg _))
    (fun i => by
      have hh := (abs_le.mp (realEnergyTrialTau_sub_le a ha he (hu i))).1
      linarith only [hh])
  have hs1 : -2 * ((∑ i, realEnergyTrialTau a e (u i)) / ν) =
      (∑ i, -2 * realEnergyTrialTau a e (u i)) / ν := by
    rw [← Finset.mul_sum]; ring
  have hsplit : (∑ i, (Qref (u i) - 2 * barrierTrialT a (u i))) / ν =
      (∑ i, Qref (u i)) / ν + (∑ i, -2 * barrierTrialT a (u i)) / ν := by
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold trialPairError
  rw [hsplit]
  ring_nf at hrx ht hav hs1 ⊢
  linarith only [hrx, ht, hav, hs1]

/-! ### Obligation 5 -/

theorem bDeriv_eq_negBlaschkeDeriv {n : ℕ} (x : Fin n → ℝ) (a : Fin n) :
    CatalanMeasure.Signed.bDeriv x a = CatalanMeasure.GenD.Signed.negBlaschkeDeriv x a := rfl

/-! ### (d) Distinctness a.e. and the Heine/log-gas bridge -/

section Bridge

/-- The diagonal `θ_l = θ_l'` is null for the product Lebesgue measure on `[0,π]^s`. -/
theorem lebPi_diag_null {s : ℕ} {l l' : Fin s} (hne : l ≠ l') :
    lebPi s {θ | θ l = θ l'} = 0 := by
  have hT := isTrial_arcsine
  have hP := isProbabilityMeasure_denMeasure hT
  have hmap := map_pair_denPi hT (s := s) hne
  have hm : Measurable (fun θ : Fin s → ℝ => (θ l, θ l')) := by fun_prop
  have hatom : ∀ x : ℝ, denMeasure (fun _ => 0) 0 {x} = 0 := by
    intro x
    have h1 : denMeasure (fun _ => 0) 0 ≪ volume.restrict (Set.Icc 0 Real.pi) :=
      withDensity_absolutelyContinuous _ _
    apply h1
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)
  have hD : denPi (fun _ => 0) 0 s {θ | θ l = θ l'} = 0 := by
    have : {θ : Fin s → ℝ | θ l = θ l'} = (fun θ => (θ l, θ l')) ⁻¹' Set.diagonal ℝ := rfl
    rw [this, ← Measure.map_apply hm measurableSet_diagonal, hmap,
      Measure.prod_apply measurableSet_diagonal]
    have hpre : ∀ x : ℝ, Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
      intro x; ext y; simp [Set.mem_diagonal_iff, eq_comm]
    simp only [hpre, hatom, lintegral_zero]
  rw [denPi_eq_withDensity hT] at hD
  have hf : AEMeasurable (fun θ : Fin s → ℝ => ENNReal.ofReal (∏ l, denQ (fun _ => 0) 0 (θ l)))
      (lebPi s) := by
    refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact (continuous_finset_prod _ fun l _ => (continuous_denQ _ _).comp (continuous_apply l)).measurable
  rw [withDensity_apply_eq_zero' hf] at hD
  have hall : {x : Fin s → ℝ | ENNReal.ofReal (∏ l, denQ (fun _ => 0) 0 (x l)) ≠ 0} = Set.univ := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun l _ => denQ_pos hT _
  rwa [hall, Set.univ_inter] at hD

/-- Almost every point of `[0,π]^s` has distinct coordinates, all in `[0, π]`. -/
theorem ae_lebPi_distinct (s : ℕ) :
    ∀ᵐ θ ∂(lebPi s), (∀ l, θ l ∈ Set.Icc 0 Real.pi) ∧ ∀ l l', l ≠ l' → θ l ≠ θ l' := by
  refine Filter.Eventually.and ?_ ?_
  · rw [ae_all_iff]
    intro l
    have hz : lebPi s {θ | θ l ∉ Set.Icc 0 Real.pi} = 0 := by
      have hset : {θ : Fin s → ℝ | θ l ∉ Set.Icc 0 Real.pi} =
          Set.pi Set.univ (fun i => if i = l then (Set.Icc 0 Real.pi)ᶜ else Set.univ) := by
        ext θ
        simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
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
        (by simp [Measure.restrict_apply measurableSet_Icc.compl])
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with θ h
    simpa using h
  · rw [ae_all_iff]; intro l
    rw [ae_all_iff]; intro l'
    by_cases hne : l = l'
    · simp [hne]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (lebPi_diag_null hne)] with θ h _ using h

/-- At a point with distinct cosines, `exp (denEnergy)` is the Heine integrand. -/
theorem exp_denEnergy_eq {s : ℕ} (f : ℝ → ℝ) (θ : Fin s → ℝ)
    (hc : Function.Injective fun l => Real.cos (θ l)) (hf : ∀ l, 0 < f (Real.cos (θ l))) :
    Real.exp (denEnergy (fun u => Real.log (f u)) s θ) =
      (Matrix.vandermonde fun l => Real.cos (θ l)).det ^ 2 * ∏ l, f (Real.cos (θ l)) := by
  set c : Fin s → ℝ := fun l => Real.cos (θ l) with hcdef
  have hne : ∀ i j, i ≠ j → c i - c j ≠ 0 := fun i j hij h => hij (hc (sub_eq_zero.mp h))
  have hA : (∑ l, ∑ l' ∈ Finset.univ.erase l, kerL (θ l) (θ l')) =
      2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |c i - c j| := by
    rw [← sum_offdiag_eq_two_mul (fun i j => Real.log |c i - c j|)
      (fun i j => by rw [abs_sub_comm])]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), if_pos rfl, zero_add]
    refine Finset.sum_congr rfl fun l' hl' => ?_
    rw [if_neg (Finset.ne_of_mem_erase hl').symm]
    rfl
  unfold denEnergy
  rw [hA, Real.exp_add, Matrix.det_vandermonde, ← Finset.prod_pow, Real.exp_sum]
  congr 1
  · rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
    have h0 : 0 < |c i - c j| := abs_pos.mpr (hne i j hij)
    rw [show (2 : ℝ) * Real.log |c i - c j| = Real.log (|c i - c j| ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos h0 2), sq_abs]
    ring
  · exact Finset.prod_congr rfl fun l _ => Real.exp_log (hf l)

theorem heineZ_eq_denZ {s : ℕ} (f : ℝ → ℝ) (hf : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 < f u) :
    CatalanMeasure.GenD.Signed.heineZ s f = denZ (fun u => Real.log (f u)) s := by
  have hmu : volume.restrict (Set.Ioc 0 Real.pi) = volume.restrict (Set.Icc 0 Real.pi) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  unfold CatalanMeasure.GenD.Signed.heineZ denZ lebPi
  simp only [hmu]
  refine integral_congr_ae ?_
  filter_upwards [ae_lebPi_distinct s] with θ ⟨hmem, hdist⟩
  symm
  refine exp_denEnergy_eq f θ ?_ fun l => hf _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  intro l l' h
  by_contra hll
  exact hdist l l' hll (Real.injOn_cos (hmem l) (hmem l') h)

/-- Upper bound of the Heine integral by the pointwise supremum of the exponent. -/
theorem denZ_le {s : ℕ} (Q : ℝ → ℝ) (B : ℝ)
    (hB : ∀ θ : Fin s → ℝ, (∀ l, θ l ∈ Set.Icc 0 Real.pi) → (∀ l l', l ≠ l' → θ l ≠ θ l') →
      denEnergy Q s θ ≤ B) :
    denZ Q s ≤ Real.pi ^ s * Real.exp B := by
  unfold denZ
  have hfin : IsFiniteMeasure (lebPi s) := by unfold lebPi; infer_instance
  have hb : ∀ᵐ θ ∂(lebPi s), ‖Real.exp (denEnergy Q s θ)‖ ≤ Real.exp B := by
    filter_upwards [ae_lebPi_distinct s] with θ ⟨hm, hd⟩
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

end Bridge

/-! ### (a) The prefactor -/

section Pref

/-- Series of the double logarithm: `Σ_n (Σ_i t_i^{n+1})(Σ_j u_j^{n+1})/(n+1) = -Σ_{i,j} log(1 - t_i u_j)`. -/
theorem hasSum_log_pair {a b : ℕ} {t : Fin a → ℝ} {u : Fin b → ℝ}
    (ht : ∀ i, |t i| < 1) (hu : ∀ j, |u j| < 1) :
    HasSum (fun n : ℕ => (∑ i, t i ^ (n + 1)) * (∑ j, u j ^ (n + 1)) / ((n : ℝ) + 1))
      (-∑ i, ∑ j, Real.log (1 - t i * u j)) := by
  have h1 : ∀ i j, HasSum (fun n : ℕ => (t i * u j) ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - t i * u j)) := by
    intro i j
    apply Real.hasSum_pow_div_log_of_abs_lt_one
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
    rw [mul_pow]
  · simp only [Finset.sum_neg_distrib]

/-- The (possibly self-paired) off-diagonal logarithm sum in terms of the full double sum. -/
theorem sum_Ioi_log_eq {a : ℕ} (t : Fin a → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - t i * t j) =
      (1 / 2) * ((∑ i, ∑ j, Real.log (1 - t i * t j)) - ∑ i, Real.log (1 - t i * t i)) := by
  have h := sum_offdiag_eq_two_mul (p := a) (fun i j => Real.log (1 - t i * t j))
    (fun i j => by rw [mul_comm])
  have h2 : (∑ i, ∑ j, if i = j then (0:ℝ) else Real.log (1 - t i * t j)) =
      (∑ i, ∑ j, Real.log (1 - t i * t j)) - ∑ i, Real.log (1 - t i * t i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hj : ∀ j, (if i = j then (0:ℝ) else Real.log (1 - t i * t j)) =
        Real.log (1 - t i * t j) - (if i = j then Real.log (1 - t i * t j) else 0) := by
      intro j; split_ifs <;> simp
    simp only [hj]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  linarith

/-- Dilated prefactor (per `ν²`) of negatives `xn` and positives `gp`. -/
def prefTau {k q : ℕ} (τ ν : ℝ) (xn : Fin k → ℝ) (gp : Fin q → ℝ) : ℝ :=
  ((∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - τ ^ 2 * (xn i * xn j))) -
    ∑ b, ∑ p, Real.log (1 - τ ^ 2 * (gp p * xn b))) / ν ^ 2

/-- Undilated `log Pref` of `route_two`. -/
def logPref {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - xn i * xn j)) -
    ∑ b, ∑ p, Real.log (1 - gp p * xn b)

/-- Dilating the nodes towards `0` only increases the prefactor. -/
theorem logPref_le_prefTau {k q : ℕ} {τ ν : ℝ} (hτ : τ ∈ Set.Ioc (0 : ℝ) 1) (hν : 0 < ν)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (hn : ∀ b, xn b ∈ Set.Ioo (-1 : ℝ) 0)
    (hg : ∀ p, gp p ∈ Set.Ioo (0 : ℝ) 1) :
    logPref xn gp / ν ^ 2 ≤ prefTau τ ν xn gp := by
  unfold logPref prefTau
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ν)
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ.1.le hτ.2
  have hτ0 : 0 < τ ^ 2 := pow_pos hτ.1 2
  refine sub_le_sub (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_)
    (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun p _ => ?_)
  · have h0 : 0 < xn i * xn j := mul_pos_of_neg_of_neg (hn i).2 (hn _).2
    have h1 : xn i * xn j < 1 := by nlinarith [(hn i).1, (hn j).1, (hn i).2, (hn j).2]
    exact Real.log_le_log (by linarith) (by nlinarith)
  · have hgx : gp p * xn b < 0 := mul_neg_of_pos_of_neg (hg p).1 (hn b).2
    exact Real.log_le_log (by nlinarith) (by nlinarith)

/-- Dilated power sums of the nodes, normalised by `ν`, at index `n + 1`. -/
def powSum {m : ℕ} (τ ν : ℝ) (y : Fin m → ℝ) (n : ℕ) : ℝ := (∑ b, (τ * y b) ^ (n + 1)) / ν

theorem hasSum_pair_powSum {a b : ℕ} {τ ν : ℝ} (hν : 0 < ν) {y : Fin a → ℝ} {z : Fin b → ℝ}
    (hy : ∀ i, |τ * y i| < 1) (hz : ∀ j, |τ * z j| < 1) :
    HasSum (fun n : ℕ => powSum τ ν y n * powSum τ ν z n / ((n : ℝ) + 1))
      (-(∑ i, ∑ j, Real.log (1 - (τ * y i) * (τ * z j))) / ν ^ 2) := by
  have h := (hasSum_log_pair hy hz).div_const (ν ^ 2)
  convert h using 1
  funext n
  unfold powSum
  field_simp

/-- The dilated prefactor as quadratic series in the dilated power sums. -/
theorem prefTau_eq {k q : ℕ} {τ ν : ℝ} (hν : 0 < ν) (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (hn : ∀ b, |τ * xn b| < 1) (hg : ∀ p, |τ * gp p| < 1) :
    prefTau τ ν xn gp =
      -(1 / 2) * (∑' n : ℕ, powSum τ ν xn n * powSum τ ν xn n / ((n : ℝ) + 1)) +
      (∑' n : ℕ, powSum τ ν xn n * powSum τ ν gp n / ((n : ℝ) + 1)) -
      (1 / (2 * ν ^ 2)) * ∑ b, Real.log (1 - (τ * xn b) * (τ * xn b)) := by
  have h1 := (hasSum_pair_powSum hν hn hn).tsum_eq
  have h2 := (hasSum_pair_powSum hν hn hg).tsum_eq
  rw [h1, h2]
  unfold prefTau
  have e1 : ∀ i j, Real.log (1 - τ ^ 2 * (xn i * xn j)) = Real.log (1 - (τ * xn i) * (τ * xn j)) :=
    fun i j => by congr 1; ring
  have e2 : ∀ b p, Real.log (1 - τ ^ 2 * (gp p * xn b)) =
      Real.log (1 - (τ * xn b) * (τ * gp p)) := fun b p => by congr 1; ring
  simp only [e1, e2]
  rw [sum_Ioi_log_eq (fun i => τ * xn i)]
  field_simp
  ring

end Pref

/-! ### (b) Geometric sequences and the quadratic algebra -/

section Quad

/-- A sequence dominated by a multiple of `τ^(n+1)`. -/
def IsGeom (τ : ℝ) (c : ℕ → ℝ) : Prop := ∃ C : ℝ, ∀ n, |c n| ≤ C * τ ^ (n + 1)

theorem IsGeom.add {τ : ℝ} {c d : ℕ → ℝ} (hc : IsGeom τ c) (hd : IsGeom τ d) :
    IsGeom τ (fun n => c n + d n) := by
  obtain ⟨C, hC⟩ := hc; obtain ⟨D, hD⟩ := hd
  exact ⟨C + D, fun n => by
    calc |c n + d n| ≤ |c n| + |d n| := abs_add_le _ _
      _ ≤ C * τ ^ (n + 1) + D * τ ^ (n + 1) := add_le_add (hC n) (hD n)
      _ = _ := by ring⟩

theorem IsGeom.neg {τ : ℝ} {c : ℕ → ℝ} (hc : IsGeom τ c) : IsGeom τ (fun n => -c n) := by
  obtain ⟨C, hC⟩ := hc
  exact ⟨C, fun n => by simpa using hC n⟩

theorem IsGeom.sub {τ : ℝ} {c d : ℕ → ℝ} (hc : IsGeom τ c) (hd : IsGeom τ d) :
    IsGeom τ (fun n => c n - d n) := by
  simpa [sub_eq_add_neg] using hc.add hd.neg

theorem IsGeom.const_mul {τ : ℝ} {c : ℕ → ℝ} (a : ℝ) (hc : IsGeom τ c) :
    IsGeom τ (fun n => a * c n) := by
  obtain ⟨C, hC⟩ := hc
  exact ⟨|a| * C, fun n => by
    rw [abs_mul]
    calc |a| * |c n| ≤ |a| * (C * τ ^ (n + 1)) := mul_le_mul_of_nonneg_left (hC n) (abs_nonneg _)
      _ = _ := by ring⟩

/-- Products of two geometric sequences divided by `n + 1` are summable. -/
theorem IsGeom.summable_mul {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) {c d : ℕ → ℝ}
    (hc : IsGeom τ c) (hd : IsGeom τ d) :
    Summable (fun n : ℕ => c n * d n / ((n : ℝ) + 1)) := by
  obtain ⟨C, hC⟩ := hc; obtain ⟨D, hD⟩ := hd
  have hg : Summable (fun n : ℕ => |C * D| * (τ ^ 2) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one (by have := hτ.1; positivity)
      (by nlinarith [hτ.1, hτ.2])).comp_injective (add_left_injective 1)).mul_left _
  refine Summable.of_norm_bounded hg fun n => ?_
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0:ℝ) < (n : ℝ) + 1), abs_mul]
  have h1 : |c n| * |d n| ≤ |C * D| * (τ ^ 2) ^ (n + 1) := by
    calc |c n| * |d n| ≤ (C * τ ^ (n + 1)) * (D * τ ^ (n + 1)) :=
          mul_le_mul (hC n) (hD n) (abs_nonneg _) ((abs_nonneg _).trans (hC n))
      _ ≤ |C * D| * (τ ^ 2) ^ (n + 1) := by
          rw [← pow_mul, mul_comm 2 (n + 1), pow_mul]
          have : (C * τ ^ (n + 1)) * (D * τ ^ (n + 1)) = (C * D) * (τ ^ (n + 1)) ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  calc |c n| * |d n| / ((n : ℝ) + 1) ≤ |c n| * |d n| := div_le_self (by positivity) hn
    _ ≤ _ := h1

/-- Dilated power sums of nodes with `|y| ≤ 1` are geometric. -/
theorem isGeom_powSum {m : ℕ} {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) (y : Fin m → ℝ)
    (hy : ∀ b, |y b| ≤ 1) : IsGeom τ (powSum τ ν y) := by
  refine ⟨(m : ℝ) / ν, fun n => ?_⟩
  unfold powSum
  rw [abs_div, abs_of_pos hν, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hν.le
  calc |∑ b, (τ * y b) ^ (n + 1)| ≤ ∑ b, |(τ * y b) ^ (n + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin m, τ ^ (n + 1) := Finset.sum_le_sum fun b _ => by
        rw [abs_pow, abs_mul, abs_of_pos hτ]
        exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right hτ.le (hy b)) _
    _ = (m : ℝ) * τ ^ (n + 1) := by simp

/-- The inner product `Σ_n c_n d_n / (n+1)`. -/
def ip (c d : ℕ → ℝ) : ℝ := ∑' n : ℕ, c n * d n / ((n : ℝ) + 1)

theorem ip_self_nonneg (c : ℕ → ℝ) : 0 ≤ ip c c :=
  tsum_nonneg fun n => div_nonneg (mul_self_nonneg _) (by positivity)

theorem hasSum_ip {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) {c d : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) : HasSum (fun n : ℕ => c n * d n / ((n : ℝ) + 1)) (ip c d) :=
  (hc.summable_mul hτ hd).hasSum

/-- The tangent-plane inequality for the quadratic part at `α = 0`: Pref, the Λ term and the
`L` terms of D7.1 at weight `2(1 - η)` (signed power sums `B` of the negatives, `P` of the
positives; references `R`, `mp`, `mn`; trial tangent point `t` for the negatives), `η ≤ 1/2`.
Pointwise the difference of the two sides is `(1/2 - η)(P - mp)² + (1 - η)(B - t)²`. -/
theorem quad_master {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) {B P R mp mn t : ℕ → ℝ}
    (hB : IsGeom τ B) (hP : IsGeom τ P) (hR : IsGeom τ R) (hmp : IsGeom τ mp)
    (hmn : IsGeom τ mn) (ht : IsGeom τ t) {η : ℝ} (hη : η ≤ 1 / 2) :
    -(1 / 2) * ip B B + ip B P + (1 / 2) * ip (fun n => B n - P n - R n) (fun n => B n - P n - R n)
        - (1 - η) * ip (fun n => P n - mp n) (fun n => P n - mp n)
        - (1 - η) * ip (fun n => B n - mn n) (fun n => B n - mn n) ≤
      ip P (fun n => mp n + R n) + ip B (fun n => 2 * (1 - η) * (mn n - t n) - R n) +
        (1 / 2) * ip R R - (1 / 2) * ip mp mp + (1 - η) * (ip t t - ip mn mn) := by
  have hBPR : IsGeom τ (fun n => B n - P n - R n) := (hB.sub hP).sub hR
  have hPm : IsGeom τ (fun n => P n - mp n) := hP.sub hmp
  have hBm : IsGeom τ (fun n => B n - mn n) := hB.sub hmn
  have hL : HasSum (fun n : ℕ => (-(1 / 2) * (B n * B n) + B n * P n +
      (1 / 2) * ((B n - P n - R n) * (B n - P n - R n)) -
      (1 - η) * ((P n - mp n) * (P n - mp n)) - (1 - η) * ((B n - mn n) * (B n - mn n))) /
        ((n : ℝ) + 1))
      (-(1 / 2) * ip B B + ip B P +
        (1 / 2) * ip (fun n => B n - P n - R n) (fun n => B n - P n - R n)
        - (1 - η) * ip (fun n => P n - mp n) (fun n => P n - mp n)
        - (1 - η) * ip (fun n => B n - mn n) (fun n => B n - mn n)) := by
    have h := ((((((hasSum_ip hτ hB hB).mul_left (-(1 / 2))).add (hasSum_ip hτ hB hP)).add
      ((hasSum_ip hτ hBPR hBPR).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hPm hPm).mul_left (1 - η))).sub
      ((hasSum_ip hτ hBm hBm).mul_left (1 - η)))
    convert h using 1
    funext n; ring
  have hMR : IsGeom τ (fun n => mp n + R n) := hmp.add hR
  have hBmt : IsGeom τ (fun n => 2 * (1 - η) * (mn n - t n) - R n) :=
    ((hmn.sub ht).const_mul (2 * (1 - η))).sub hR
  have hR' : HasSum (fun n : ℕ => (P n * (mp n + R n) + B n * (2 * (1 - η) * (mn n - t n) - R n) +
      (1 / 2) * (R n * R n) - (1 / 2) * (mp n * mp n) +
      (1 - η) * (t n * t n - mn n * mn n)) / ((n : ℝ) + 1))
      (ip P (fun n => mp n + R n) + ip B (fun n => 2 * (1 - η) * (mn n - t n) - R n) +
        (1 / 2) * ip R R - (1 / 2) * ip mp mp + (1 - η) * (ip t t - ip mn mn)) := by
    have h := (((((hasSum_ip hτ hP hMR).add (hasSum_ip hτ hB hBmt)).add
      ((hasSum_ip hτ hR hR).mul_left (1 / 2))).sub ((hasSum_ip hτ hmp hmp).mul_left (1 / 2))).add
      (((hasSum_ip hτ ht ht).sub (hasSum_ip hτ hmn hmn)).mul_left (1 - η)))
    convert h using 1
    funext n; ring
  refine hasSum_le (fun n => ?_) hL hR'
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hn]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - η by linarith) (sq_nonneg (P n - mp n)),
    mul_nonneg (show (0 : ℝ) ≤ 1 - η by linarith) (sq_nonneg (B n - t n))]

/-- The single-node field `x ↦ Σ_n (τ x)^{n+1} c_n / (n+1)` of a coefficient sequence. -/
def fld (τ : ℝ) (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' n : ℕ, (τ * x) ^ (n + 1) * c n / ((n : ℝ) + 1)

theorem isGeom_node {τ : ℝ} (hτ : 0 < τ) {x : ℝ} (hx : |x| ≤ 1) :
    IsGeom τ (fun n : ℕ => (τ * x) ^ (n + 1)) := by
  refine ⟨1, fun n => ?_⟩
  rw [abs_pow, abs_mul, abs_of_pos hτ, one_mul]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right hτ.le hx) _

theorem hasSum_fld {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) {c : ℕ → ℝ} (hc : IsGeom τ c) {x : ℝ}
    (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => (τ * x) ^ (n + 1) * c n / ((n : ℝ) + 1)) (fld τ c x) :=
  ((isGeom_node hτ.1 hx).summable_mul hτ hc).hasSum

theorem ip_powSum_left {m : ℕ} {τ ν : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (y : Fin m → ℝ) (hy : ∀ b, |y b| ≤ 1) {c : ℕ → ℝ} (hc : IsGeom τ c) :
    ip (powSum τ ν y) c = (∑ b, fld τ c (y b)) / ν := by
  have h := (hasSum_sum (s := Finset.univ) fun b _ => hasSum_fld hτ hc (hy b)).div_const ν
  rw [ip, ← h.tsum_eq]
  congr 1
  funext n
  unfold powSum
  simp only [Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Weighted dilated power sums `Σ_b w_b (τ y_b)^(n+1)`. -/
def wpow (τ : ℝ) {m : ℕ} (w y : Fin m → ℝ) (n : ℕ) : ℝ := ∑ b, w b * (τ * y b) ^ (n + 1)

theorem wpow_append (τ : ℝ) {a b : ℕ} (w y : Fin a → ℝ) (w' y' : Fin b → ℝ) (n : ℕ) :
    wpow τ (Fin.append w w') (Fin.append y y') n = wpow τ w y n + wpow τ w' y' n := by
  unfold wpow
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem wpow_const (τ ν c : ℝ) {m : ℕ} (y : Fin m → ℝ) (n : ℕ) :
    wpow τ (fun _ => c / ν) y n = c * powSum τ ν y n := by
  unfold wpow powSum
  rw [Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem isGeom_wpow {m : ℕ} {τ : ℝ} (hτ : 0 < τ) (w y : Fin m → ℝ) (hy : ∀ b, |y b| ≤ 1) :
    IsGeom τ (wpow τ w y) := by
  refine ⟨∑ b, |w b|, fun n => ?_⟩
  unfold wpow
  calc |∑ b, w b * (τ * y b) ^ (n + 1)| ≤ ∑ b, |w b * (τ * y b) ^ (n + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |w b| * τ ^ (n + 1) := Finset.sum_le_sum fun b _ => by
        rw [abs_mul, abs_pow, abs_mul, abs_of_pos hτ]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (mul_le_of_le_one_right hτ.le (hy b)) _) (abs_nonneg _)
    _ = (∑ b, |w b|) * τ ^ (n + 1) := by rw [Finset.sum_mul]

theorem ip_wpow_left {m : ℕ} {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (w y : Fin m → ℝ)
    (hy : ∀ b, |y b| ≤ 1) {c : ℕ → ℝ} (hc : IsGeom τ c) :
    ip (wpow τ w y) c = ∑ b, w b * fld τ c (y b) := by
  have h := hasSum_sum (s := Finset.univ) fun b _ => (hasSum_fld hτ hc (hy b)).mul_left (w b)
  rw [ip, ← h.tsum_eq]
  congr 1
  funext n
  unfold wpow
  simp only [Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

end Quad

/-! ### Matching D7.1's `L`-terms with the inner products -/

section LMatch

open CatalanMeasure.Signed.ReflectionEnergy

theorem BD.ae_mem {m : Measure ℝ} {C : ℝ} (h : BD m C) : ∀ᵐ y ∂m, y ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [ae_iff]
  show m (Set.Ioo (0 : ℝ) 1)ᶜ = 0
  have h1 := Measure.le_iff'.1 h (Set.Ioo (0 : ℝ) 1)ᶜ
  have h2 : (ENNReal.ofReal C • volume.restrict (Set.Ioo (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo.compl]
    simp
  rw [h2] at h1
  exact le_zero_iff.mp h1

/-- Reference moments are geometric. -/
theorem isGeom_refMoment {m : Measure ℝ} {C : ℝ} (h : BD m C) {τ : ℝ} (hτ : 0 < τ) :
    IsGeom τ (fun n : ℕ => ∫ y, (τ * y) ^ (n + 1) ∂m) := by
  have := h.finite
  refine ⟨m.real Set.univ, fun n => ?_⟩
  have hb : ∀ᵐ y ∂m, ‖(τ * y) ^ (n + 1)‖ ≤ τ ^ (n + 1) := by
    filter_upwards [h.ae_mem] with y hy
    rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hτ]
    have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    exact pow_le_pow_left₀ (by have := abs_nonneg y; positivity)
      (mul_le_of_le_one_right hτ.le hy1) _
  have := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at this
  linarith [mul_comm (τ ^ (n + 1)) (m.real Set.univ)]

/-- Reference species moments (positive species / signed negative species) at index `n + 1`,
of the signed reference `P - N`. -/
def mpos (μ : SRef) (τ : ℝ) (n : ℕ) : ℝ :=
  ∫ y, (τ * y) ^ (n + 1) ∂(μ.P true) - ∫ y, (τ * y) ^ (n + 1) ∂(μ.N true)
def mneg (μ : SRef) (τ : ℝ) (n : ℕ) : ℝ :=
  (-1) ^ (n + 1) * (∫ y, (τ * y) ^ (n + 1) ∂(μ.P false) - ∫ y, (τ * y) ^ (n + 1) ∂(μ.N false))

theorem isGeom_mpos {μ : SRef} {C : ℝ} (h : μ.OK C) {τ : ℝ} (hτ : 0 < τ) :
    IsGeom τ (mpos μ τ) :=
  (isGeom_refMoment (h.hP true) hτ).sub (isGeom_refMoment (h.hN true) hτ)

theorem isGeom_mneg {μ : SRef} {C : ℝ} (h : μ.OK C) {τ : ℝ} (hτ : 0 < τ) :
    IsGeom τ (mneg μ τ) := by
  obtain ⟨K, hK⟩ := (isGeom_refMoment (h.hP false) hτ).sub (isGeom_refMoment (h.hN false) hτ)
  exact ⟨K, fun n => by
    unfold mneg; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hK n⟩

theorem Lpart_true_eq {k q : ℕ} {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) (hn : ∀ b, xn b < 0) (hg : ∀ p, 0 < gp p) (μ : SRef) :
    Lpart (fun _ : Fin (k + q) => 1 / ν) (fun i => |Fin.append xn gp i|)
      (fun i => decide (0 < Fin.append xn gp i)) μ.P μ.N (τ ^ 2) true =
      ip (fun n => powSum τ ν gp n - mpos μ τ n) (fun n => powSum τ ν gp n - mpos μ τ n) := by
  unfold Lpart ip
  simp only [Real.sqrt_sq hτ.le]
  refine tsum_congr fun n => ?_
  have hsum : (∑ i : Fin (k + q), if decide (0 < Fin.append xn gp i) = true then
      1 / ν * (τ * |Fin.append xn gp i|) ^ (n + 1) else 0) = powSum τ ν gp n := by
    rw [Fin.sum_univ_add]
    have h1 : ∀ b : Fin k, (if decide (0 < Fin.append xn gp (Fin.castAdd q b)) = true then
        1 / ν * (τ * |Fin.append xn gp (Fin.castAdd q b)|) ^ (n + 1)
        else 0) = 0 := by
      intro b
      simp [Fin.append_left, not_lt.mpr (hn b).le]
    have h2 : ∀ p : Fin q, (if decide (0 < Fin.append xn gp (Fin.natAdd k p)) = true then
        1 / ν * (τ * |Fin.append xn gp (Fin.natAdd k p)|) ^ (n + 1)
        else 0) = 1 / ν * (τ * gp p) ^ (n + 1) := by
      intro p
      simp [Fin.append_right, hg p, abs_of_pos (hg p)]
    simp only [h1, h2, Finset.sum_const_zero, zero_add]
    unfold powSum
    rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
  rw [hsum]
  show _ = (powSum τ ν gp n - mpos μ τ n) * (powSum τ ν gp n - mpos μ τ n) / ((n : ℝ) + 1)
  unfold mpos
  ring

theorem Lpart_false_eq {k q : ℕ} {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) (hn : ∀ b, xn b < 0) (hg : ∀ p, 0 < gp p) (μ : SRef) :
    Lpart (fun _ : Fin (k + q) => 1 / ν) (fun i => |Fin.append xn gp i|)
      (fun i => decide (0 < Fin.append xn gp i)) μ.P μ.N (τ ^ 2) false =
      ip (fun n => powSum τ ν xn n - mneg μ τ n) (fun n => powSum τ ν xn n - mneg μ τ n) := by
  unfold Lpart ip
  simp only [Real.sqrt_sq hτ.le]
  refine tsum_congr fun n => ?_
  have hsum : (∑ i : Fin (k + q), if decide (0 < Fin.append xn gp i) = false then
      1 / ν * (τ * |Fin.append xn gp i|) ^ (n + 1) else 0) =
      (-1) ^ (n + 1) * powSum τ ν xn n := by
    rw [Fin.sum_univ_add]
    have h1 : ∀ b : Fin k, (if decide (0 < Fin.append xn gp (Fin.castAdd q b)) = false then
        1 / ν * (τ * |Fin.append xn gp (Fin.castAdd q b)|) ^ (n + 1)
        else 0) = (-1) ^ (n + 1) * (1 / ν * (τ * xn b) ^ (n + 1)) := by
      intro b
      have : decide (0 < Fin.append xn gp (Fin.castAdd q b)) = false := by
        simp [Fin.append_left, not_lt.mpr (hn b).le]
      rw [if_pos this]
      simp only [Fin.append_left, abs_of_neg (hn b)]
      rw [show τ * -xn b = -1 * (τ * xn b) by ring, mul_pow]
      ring
    have h2 : ∀ p : Fin q, (if decide (0 < Fin.append xn gp (Fin.natAdd k p)) = false then
        1 / ν * (τ * |Fin.append xn gp (Fin.natAdd k p)|) ^ (n + 1)
        else 0) = 0 := by
      intro p
      simp [Fin.append_right, hg p]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]
    unfold powSum
    rw [← Finset.mul_sum, ← Finset.mul_sum, one_div, inv_mul_eq_div]
  have hsq : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [hsum]
  show _ = (powSum τ ν xn n - mneg μ τ n) * (powSum τ ν xn n - mneg μ τ n) / ((n : ℝ) + 1)
  unfold mneg
  set IP := ∫ y, (τ * y) ^ (n + 1) ∂(μ.P false)
  set IN := ∫ y, (τ * y) ^ (n + 1) ∂(μ.N false)
  set B := powSum τ ν xn n
  set sg : ℝ := (-1) ^ (n + 1)
  have key : (sg * B - IP + IN) ^ 2 = (B - sg * (IP - IN)) * (B - sg * (IP - IN)) := by
    linear_combination (B ^ 2 - (IP - IN) ^ 2) * hsq
  rw [one_div, inv_mul_eq_div, key]

end LMatch

/-! ### The cross tilt of the append configuration -/

section Tilt

/-- The reference tilt sequence attached to a reference moment sequence `R` (index `m = n + 1`). -/
def refTilt (R : ℕ → ℝ) (m : ℕ) : ℝ := -(-1 : ℝ) ^ m * R (m - 1) / (m : ℝ)

/-- Signed cross weights: `+1/(2ν)` on the negatives, `-1/(2ν)` on the positives. -/
def crossW {k q : ℕ} (ν : ℝ) : Fin (k + q) → ℝ :=
  Fin.append (fun _ => 1 / (2 * ν)) (fun _ => -(1 / (2 * ν)))

theorem crossBeta_append {k q : ℕ} {τ ν : ℝ} (hν : 0 < ν) (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (n : ℕ) :
    crossBeta τ (crossW ν) (Fin.append xn gp) (n + 1) =
      -(-1 : ℝ) ^ (n + 1) * (powSum τ ν xn n - powSum τ ν gp n) / ((n : ℝ) + 1) := by
  unfold crossBeta crossW powSum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, mul_pow, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_div, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem crossTiltNormRef_append {k q : ℕ} {τ ν : ℝ} (hν : 0 < ν) (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) (R : ℕ → ℝ) :
    crossTiltNormRef τ (crossW ν) (Fin.append xn gp) (refTilt R) =
      (1 / 4) * ip (fun n => powSum τ ν xn n - powSum τ ν gp n - R n)
        (fun n => powSum τ ν xn n - powSum τ ν gp n - R n) := by
  unfold crossTiltNormRef ip
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [crossBeta_append hν]
  unfold refTilt
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hsq : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  generalize (-1 : ℝ) ^ (n + 1) = sg at hsq ⊢
  rcases eq_or_eq_neg_of_sq_eq_sq sg 1 (by simpa using hsq) with h | h <;> subst h <;>
    field_simp <;> ring

theorem sum_S_append {k q : ℕ} {ν : ℝ} (hν : 0 < ν) (a : ℕ → ℝ) (c : ℝ) (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) :
    -2 * ∑ l, crossW ν l * barrierTrialS a (c * Fin.append xn gp l) =
      (1 / ν) * ((∑ b, -barrierTrialS a (c * xn b)) + ∑ p, barrierTrialS a (c * gp p)) := by
  unfold crossW
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_neg_distrib]
  generalize ∑ b, barrierTrialS a (c * xn b) = A
  generalize ∑ p, barrierTrialS a (c * gp p) = Bq
  field_simp
  ring

end Tilt

/-! ### The data, the bound expressions and the master inequality -/

section Master

open CatalanMeasure.Signed.ReflectionEnergy

/-- `∫ l(x, u) dν'(u) = - denPoly b K x` for the denominator trial `ν'` (J5). -/
def denPoly (b : ℕ → ℝ) (K : ℕ) (g : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range K, (-g) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ)

/-- Data of one instance of the signed second-sheet bound (fixed `N`).  All numerical inputs
(trial sequences, reference measures, field sups) are fields; hypotheses are theorem arguments. -/
structure SignedData where
  ν : ℝ
  e : ℝ
  /-- The reference Heine count `s_r` of the denominator trial `b` (the trial's `W = s_r b`). The
  Heine count of a configuration is its number of positive rows minus `g`; the bounds are taken
  at `withCount` of that count (NOTES-ETA §5.1). -/
  sp : ℕ
  /-- The count offset: Heine count = number of positive rows − `g`. -/
  g : ℕ
  v : ℕ → ℝ
  a : ℕ → ℝ
  b : ℕ → ℝ
  K : ℕ
  R : ℕ → ℝ
  t : ℕ → ℝ
  /-- The D7.1 reference: the paper's `c_r = t μ_r + (α/2) σ_r` (weights `1` on free rows,
  `1/2` on fixed rows; NOTES-ETA §1). -/
  μ : SRef
  Cb : ℝ
  /-- The split parameter of the row log-energy (g-joint-cert NOTES §12.1): a share `1 - η` by
  D7.1 at `μ`, a share `η` by the Chebyshev tangent at `p`. -/
  η : ℝ
  /-- The row Chebyshev trial of the `η`-share (the paper's `u532 + dp`). -/
  p : ℕ → ℝ
  Sup : ℝ
  constant : ℝ
  Rf : ℝ → ℝ
  Cf : ℝ → ℝ
  θ : ℝ
  cs : ℝ
  /-- Phantom charge (per `ν`): bounds the one phantom spike of an odd spike count, an additive
  `O(N)` once per configuration (SIMPLIFY-S2 §2.3); enters `errJ3` as `kph / ν → 0`. -/
  kph : ℝ

namespace SignedData

variable (D : SignedData)

/-- The dilation `τ = 1 - e`. -/
def τ : ℝ := realEnergyTau D.e

/-- `Σ' r_{n+1} a_{n+1}` for the reference tilt. -/
def ra : ℝ := ∑' n : ℕ, refTilt D.R (n + 1) * D.a (n + 1)

def numConst : ℝ :=
  2 * (-(1 / 2 : ℝ) * ((D.sp : ℝ) / D.ν) ^ 2 * Real.log 2 + barrierTrialNormSq D.a +
    ((D.sp : ℝ) / D.ν) * D.Sup - D.ra + trialPairError D.ν D.e D.a) +
    (D.sp : ℝ) * Real.log Real.pi / D.ν ^ 2

def denConst : ℝ :=
  ((D.sp : ℝ) * ((D.sp : ℝ) - 1) *
      (-Real.log 2 - ∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
    (D.sp : ℝ) * (Real.log Real.pi - 2 * ∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2)) / D.ν ^ 2

/-- The numerator bound expression (J2 with reference, doubled, plus `s log π / ν²`),
with the particle sum replaced by `(s/ν) Sup`. -/
def numB {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) : ℝ :=
  D.numConst + (2 / D.ν) * ((∑ b, -barrierTrialS D.a (-D.τ * xn b)) +
      ∑ p, barrierTrialS D.a (-D.τ * gp p)) +
    (1 / 2) * ip (fun n => powSum D.τ D.ν xn n - powSum D.τ D.ν gp n - D.R n)
      (fun n => powSum D.τ D.ν xn n - powSum D.τ D.ν gp n - D.R n)

/-- The denominator bound expression (J5, crude entropy form), per `ν²`. -/
def denB {q : ℕ} (gp : Fin q → ℝ) : ℝ :=
  D.denConst + ((D.sp : ℝ) / D.ν ^ 2) * ∑ p, denPoly D.b D.K (gp p)

/-- Common row field of a free row: the problem's field, the pin terms, the `(1 - η)`-share of
D7.1 (weight `2(1 - η)`: the diagonal cost and the potential of `μ`) and the `η`-share tangent
field `-4 η T_p` (NOTES-ETA §1.4). -/
def rowBase (x : ℝ) : ℝ :=
  D.Rf x - barrierTrialS D.v x - Real.log (1 - x) / (2 * D.ν) +
    ((1 - D.η) / D.ν) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
    2 * (1 - D.η) * rowRef D.μ x - 4 * D.η * barrierTrialT D.p x

/-- Row field on the negatives. -/
def fNeg (x : ℝ) : ℝ :=
  D.rowBase x - (1 / (2 * D.ν)) * Real.log (1 - (D.τ * x) * (D.τ * x)) -
    2 * barrierTrialS D.a (-D.τ * x) +
    fld D.τ (fun n => 2 * (1 - D.η) * (mneg D.μ D.τ n - D.t n) - D.R n) x

/-- Row field on the positives; `2 Sup` is the positive row's share `2 Sup/ν` of the particle
term `2 (x/ν) Sup` at the Heine count `x = #positives − g` (NOTES-ETA §5.1). -/
def fPos (x : ℝ) : ℝ :=
  D.rowBase x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x + 2 * D.Sup

/-- Column field. -/
def fCol (s : ℝ) : ℝ := D.Cf s + 2 * barrierTrialT D.v s - Real.log (1 - s) / D.ν

/-- The constant of the quadratic tangent plane. -/
def Kq : ℝ :=
  (1 / 2) * ip D.R D.R - (1 / 2) * ip (mpos D.μ D.τ) (mpos D.μ D.τ) +
    (1 - D.η) * (ip D.t D.t - ip (mneg D.μ D.τ) (mneg D.μ D.τ))

/-- The D7.1 error at total (weighted) row mass `W`, at weight `2(1 - η)`. -/
def eD7 (W : ℝ) : ℝ :=
  (1 - D.η) * (12 * (W + 1) * D.Cb * (1 - D.τ ^ 2) * (1 + Real.log (1 / (1 - D.τ ^ 2)))
    + 2 * (1 - D.τ ^ 2) * (2 * (W + 1)) ^ 2)

/-- The diagonal and damping cost of the `η`-share (Chebyshev tangent at `p`). -/
def etaErr : ℝ :=
  D.η * ((Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / D.ν + 4 * D.e * (∑' j, |D.p j|) +
    4 * D.e)

/-- The cost of the Chebyshev bound of the fixed-fixed half Vandermonde (PROOF-A §17.40). -/
def hadErr : ℝ := (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / (4 * D.ν) + D.e

/-- The J2/J5 constant at the reference count, with the particle term `2 (x/ν) Sup` moved to the
positive fields (`+ 2 Sup` each) and `- 2 (g/ν) Sup` kept here: `numConst - denConst` of
`withCount x` is at most `numDenRef + 2 ((x + g)/ν) Sup` for `0 < sp ≤ x`
(`numConst_sub_denConst_withCount_le`; NOTES-ETA §5.1). -/
def numDenRef : ℝ :=
  2 * (barrierTrialNormSq D.a - ((D.g : ℝ) / D.ν) * D.Sup - D.ra + trialPairError D.ν D.e D.a) +
    ((D.sp : ℝ) / D.ν) ^ 2 * (∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
    2 * ((D.sp : ℝ) / D.ν ^ 2) * ∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2

/-- **The trial at Heine count `x`**: count `x`, denominator trial `(sp/x) b` (so `x · b_x = sp · b`;
the J5 competitor is Lemma 7.4's mixture `sp ν'_b + (x - sp) arcsine`). -/
def withCount (x : ℕ) : SignedData :=
  { D with sp := x, b := fun k => ((D.sp : ℝ) / x) * D.b k }

/-- The total constant, `p` free rows (no fixed rows). -/
def constTotal (p : ℕ) : ℝ :=
  D.constant - ((p : ℝ) / D.ν) ^ 2 * Real.log 2 + barrierTrialNormSq D.v / 2 +
    4 * D.e * (∑' j, |D.v j|) + pinZeroError D.ν D.e + D.eD7 ((p : ℝ) / D.ν) +
    (1 - D.η) * refEnergy D.μ + 2 * D.η * barrierTrialNormSq D.p -
    D.η * ((p : ℝ) / D.ν) ^ 2 * Real.log 2 + D.etaErr + D.hadErr +
    D.numDenRef + D.Kq

/-- The total constant with `pf` free rows and `M` fixed rows (first kind and near): the
weighted mass of the `(1 - η)` and `η` shares is `(pf + M/2)/ν`, the fixed-fixed half
Vandermonde contributes `-(M/ν)² log 2 / 4` (NOTES-ETA §1.2). -/
def constFix (pf M : ℕ) : ℝ :=
  D.constant - ((pf : ℝ) / D.ν) ^ 2 * Real.log 2 + barrierTrialNormSq D.v / 2 +
    4 * D.e * (∑' j, |D.v j|) + pinZeroError D.ν D.e +
    D.eD7 (((pf : ℝ) + (M : ℝ) / 2) / D.ν) + (1 - D.η) * refEnergy D.μ +
    2 * D.η * barrierTrialNormSq D.p -
    D.η * (((pf : ℝ) + (M : ℝ) / 2) / D.ν) ^ 2 * Real.log 2 + D.etaErr -
    (1 / 4) * ((M : ℝ) / D.ν) ^ 2 * Real.log 2 + D.hadErr +
    D.numDenRef + D.Kq

/-! #### The trial at the configuration's Heine count -/

@[simp] theorem withCount_ν (x : ℕ) : (D.withCount x).ν = D.ν := rfl
@[simp] theorem withCount_e (x : ℕ) : (D.withCount x).e = D.e := rfl
@[simp] theorem withCount_sp (x : ℕ) : (D.withCount x).sp = x := rfl
@[simp] theorem withCount_g (x : ℕ) : (D.withCount x).g = D.g := rfl
@[simp] theorem withCount_a (x : ℕ) : (D.withCount x).a = D.a := rfl
@[simp] theorem withCount_b (x : ℕ) :
    (D.withCount x).b = fun k => ((D.sp : ℝ) / x) * D.b k := rfl
@[simp] theorem withCount_K (x : ℕ) : (D.withCount x).K = D.K := rfl
@[simp] theorem withCount_R (x : ℕ) : (D.withCount x).R = D.R := rfl
@[simp] theorem withCount_Sup (x : ℕ) : (D.withCount x).Sup = D.Sup := rfl
@[simp] theorem withCount_τ (x : ℕ) : (D.withCount x).τ = D.τ := rfl
@[simp] theorem withCount_ra (x : ℕ) : (D.withCount x).ra = D.ra := rfl
@[simp] theorem withCount_cs (x : ℕ) : (D.withCount x).cs = D.cs := rfl
@[simp] theorem withCount_θ (x : ℕ) : (D.withCount x).θ = D.θ := rfl
@[simp] theorem withCount_kph (x : ℕ) : (D.withCount x).kph = D.kph := rfl

theorem denPoly_const_mul (c : ℝ) (b : ℕ → ℝ) (K : ℕ) (g : ℝ) :
    denPoly (fun k => c * b k) K g = c * denPoly b K g := by
  simp only [denPoly, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem withCount_numB (x : ℕ) {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) :
    (D.withCount x).numB xn gp = D.numB xn gp - D.numConst + (D.withCount x).numConst := by
  unfold numB
  simp only [withCount_ν, withCount_a, withCount_τ, withCount_R]
  ring

theorem withCount_denB {x : ℕ} (hx : x ≠ 0) {q : ℕ} (gp : Fin q → ℝ) :
    (D.withCount x).denB gp = D.denB gp - D.denConst + (D.withCount x).denConst := by
  unfold denB
  simp only [withCount_ν, withCount_sp, withCount_b, withCount_K, denPoly_const_mul,
    ← Finset.mul_sum]
  have hx' : (x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hx
  field_simp
  ring

/-- **Lemma 7.3–7.4 at the Heine count `x`** (the `σ²` terms cancel; NOTES-ETA §5.1). -/
theorem numConst_sub_denConst_withCount_le {x : ℕ} (hν : 0 < D.ν) (hx : 0 < x)
    (hsr : D.sp ≤ x) :
    (D.withCount x).numConst - (D.withCount x).denConst ≤
      D.numDenRef + 2 * ((((x : ℝ) + D.g)) / D.ν) * D.Sup := by
  have hX : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hr0 : (0 : ℝ) ≤ D.sp := Nat.cast_nonneg _
  have hrX : (D.sp : ℝ) ≤ x := Nat.cast_le.mpr hsr
  set B := ∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) with hB
  set S := ∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2 with hS
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have eB : ∑ i ∈ Finset.range D.K, 2 * (((D.sp : ℝ) / x) * D.b (i + 1)) ^ 2 /
      ((i + 1 : ℕ) : ℝ) = ((D.sp : ℝ) / x) ^ 2 * B := by
    rw [hB, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have eS : ∑ i ∈ Finset.range D.K, (((D.sp : ℝ) / x) * D.b (i + 1)) ^ 2 =
      ((D.sp : ℝ) / x) ^ 2 * S := by
    rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold numConst denConst numDenRef
  simp only [withCount_ν, withCount_sp, withCount_b, withCount_K, withCount_a, withCount_e,
    withCount_Sup, withCount_ra, withCount_g]
  rw [eB, eS, ← hB, ← hS]
  have key : (2 * (barrierTrialNormSq D.a - ((D.g : ℝ) / D.ν) * D.Sup - D.ra +
        trialPairError D.ν D.e D.a) + ((D.sp : ℝ) / D.ν) ^ 2 * B + 2 * ((D.sp : ℝ) / D.ν ^ 2) * S +
        2 * (((x : ℝ) + D.g) / D.ν) * D.Sup) -
      ((2 * (-(1 / 2 : ℝ) * ((x : ℝ) / D.ν) ^ 2 * Real.log 2 + barrierTrialNormSq D.a +
        ((x : ℝ) / D.ν) * D.Sup - D.ra + trialPairError D.ν D.e D.a) +
        (x : ℝ) * Real.log Real.pi / D.ν ^ 2) -
       ((x : ℝ) * ((x : ℝ) - 1) * (-Real.log 2 - ((D.sp : ℝ) / x) ^ 2 * B) +
        (x : ℝ) * (Real.log Real.pi - 2 * (((D.sp : ℝ) / x) ^ 2 * S))) / D.ν ^ 2) =
      (x : ℝ) * Real.log 2 / D.ν ^ 2 + (D.sp : ℝ) ^ 2 * B / ((x : ℝ) * D.ν ^ 2) +
        2 * (D.sp : ℝ) * S * ((x : ℝ) - D.sp) / ((x : ℝ) * D.ν ^ 2) := by
    field_simp
    ring
  have h1 : 0 ≤ (x : ℝ) * Real.log 2 / D.ν ^ 2 := by positivity
  have h2 : 0 ≤ (D.sp : ℝ) ^ 2 * B / ((x : ℝ) * D.ν ^ 2) := by positivity
  have h3 : 0 ≤ 2 * (D.sp : ℝ) * S * ((x : ℝ) - D.sp) / ((x : ℝ) * D.ν ^ 2) := by
    have : 0 ≤ (x : ℝ) - D.sp := by linarith
    positivity
  linarith

/-- The J2/J5 bound at the Heine count `x`, in the reference trial's terms. -/
theorem numB_sub_denB_withCount_le {x : ℕ} (hν : 0 < D.ν) (hx : 0 < x) (hsr : D.sp ≤ x)
    {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) :
    (D.withCount x).numB xn gp - (D.withCount x).denB gp ≤
      D.numB xn gp - D.denB gp - (D.numConst - D.denConst) + D.numDenRef +
        2 * ((((x : ℝ) + D.g)) / D.ν) * D.Sup := by
  rw [withCount_numB, withCount_denB D hx.ne']
  linarith [D.numConst_sub_denConst_withCount_le hν hx hsr]

end SignedData

theorem row_sum_split {k q : ℕ} (F : ℝ → ℝ) (xn : Fin k → ℝ) (gp : Fin q → ℝ) :
    ∑ i, F (Fin.append xn gp i) = (∑ b, F (xn b)) + ∑ p, F (gp p) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem log_two_sub_nonneg {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    0 ≤ Real.log 2 - 2 * Real.log (1 - τ ^ 2) := by
  have h0 : 0 < 1 - τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have h1 : Real.log (1 - τ ^ 2) ≤ 0 := Real.log_nonpos h0.le (by nlinarith [hτ.1])
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

theorem SignedData.hadErr_nonneg (D : SignedData) (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) : 0 ≤ D.hadErr := by
  have h := log_two_sub_nonneg (realEnergyTau_bounds he)
  unfold SignedData.hadErr
  have : 0 ≤ (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / (4 * D.ν) := by
    apply div_nonneg h; positivity
  linarith [he.1]

/-- **The `η`-share costs** of a row list of total weighted mass `W ≤ 1` with `Σ w² ≤ 1/ν`:
`2η` times the error terms of `cos_tangent_w` are at most `etaErr`. -/
theorem SignedData.eta_err_le (D : SignedData) (hν : 0 < D.ν) (he : D.e ∈ Ioo (0 : ℝ) (1 / 8))
    (hη : 0 ≤ D.η) {W S2 : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1) (hS2W : S2 ≤ 1 / D.ν)
    (hp : 0 ≤ ∑' j, |D.p j|) :
    2 * D.η * ((1 / 2) * (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) * S2 +
      2 * D.e * W * (∑' j, |D.p j|) + 2 * D.e * W ^ 2) ≤ D.etaErr := by
  have hL := log_two_sub_nonneg (realEnergyTau_bounds he)
  have he0 := he.1.le
  unfold SignedData.etaErr
  have h1 : (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) * S2 ≤
      (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / D.ν := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hS2W hL
  have h2 : D.e * W * (∑' j, |D.p j|) ≤ D.e * (∑' j, |D.p j|) := by
    have := mul_le_mul_of_nonneg_left hW (mul_nonneg he0 hp)
    nlinarith [this]
  have h3 : D.e * W ^ 2 ≤ D.e := by
    have : W ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this he0]
  have h4 : (1 / 2) * (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) * S2 +
      2 * D.e * W * (∑' j, |D.p j|) + 2 * D.e * W ^ 2 ≤
      (1 / 2) * ((Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) / D.ν + 4 * D.e * (∑' j, |D.p j|) +
        4 * D.e) := by nlinarith [h1, h2, h3]
  nlinarith [mul_le_mul_of_nonneg_left h4 hη]

/-- `pinOffDiagonalInteraction ν 2` is the pin copy plus the all-row Vandermonde. -/
theorem pinOff_two {p : ℕ} (ν : ℝ) (x s : Fin p → ℝ) :
    pinOffDiagonalInteraction ν 2 x s = pinOffDiagonalInteraction ν 1 x s +
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2 := by
  unfold pinOffDiagonalInteraction; ring

set_option maxHeartbeats 1600000 in
/-- **The master inequality** (`α = 0`).  The free-row log-energy `2 V/ν²` (pin copy and
Vandermonde) splits as `2(1 - η)` D7.1 at `μ` plus `2η` Chebyshev tangent at `p` (NOTES-ETA §1);
under the A7 bound-form hypothesis `hA7` on the route II ratio the full functional is bounded by
the explicit constant plus single-variable fields at the negative rows, positive rows and
columns. -/
theorem signed_master (D : SignedData) {k q : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : D.μ.OK D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : ((k + q : ℕ) : ℝ) / D.ν = D.μ.mass)
    (hη0 : 0 ≤ D.η) (hη : D.η ≤ 1 / 2) (hpS : Summable (fun j => |D.p j|))
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hinj : Function.Injective (Fin.append xn gp))
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (LR spike : ℝ) (x : ℕ) (hx0 : 0 < x) (hsr : D.sp ≤ x) (hxg : (x : ℝ) + D.g = q)
    (hA7 : LR / D.ν ^ 2 ≤ logPref xn gp / D.ν ^ 2 + (D.withCount x).numB xn gp -
      (D.withCount x).denB gp + spike) :
    D.constant + pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |Fin.append xn gp j - Fin.append xn gp i|) / D.ν ^ 2 +
        (∑ i, D.Rf (Fin.append xn gp i)) / D.ν + (∑ j, D.Cf (sc j)) / D.ν + LR / D.ν ^ 2 ≤
      D.constTotal (k + q) + spike + (1 / D.ν) * (∑ b, D.fNeg (xn b)) +
        (1 / D.ν) * (∑ p, D.fPos (gp p)) + (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  -- the Heine count `x` (NOTES-ETA §5.1)
  have hA7c := D.numB_sub_denB_withCount_le hν hx0 hsr xn gp
  rw [hxg] at hA7c
  replace hA7 : LR / D.ν ^ 2 ≤ logPref xn gp / D.ν ^ 2 + D.numB xn gp - D.denB gp +
      (spike + (D.numDenRef - (D.numConst - D.denConst) + 2 * ((q : ℝ) / D.ν) * D.Sup)) := by
    linarith
  have hτb := realEnergyTau_bounds he
  have hτ : D.τ ∈ Ioo (0 : ℝ) 1 := hτb
  have hτ1 : D.τ ∈ Ioc (0 : ℝ) 1 := ⟨hτb.1, hτb.2.le⟩
  have hx : ∀ i, Fin.append xn gp i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact ⟨(hxn b).1, by linarith [(hxn b).2]⟩
    · simp only [Fin.append_right]; exact ⟨by linarith [(hgp p).1], (hgp p).2⟩
  have hx0 : ∀ i, Fin.append xn gp i ≠ 0 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact (hxn b).2.ne
    · simp only [Fin.append_right]; exact (hgp p).1.ne'
  have h1 := pin_zero_canonical hν he hp hx hs hinj hsi D.v hv
  have h2 := rows_vandermonde_le hν (Fin.append xn gp) hx0 hx hinj D.μ hμ hC hmass
    (ρ := D.τ ^ 2) (pow_pos hτ.1 2) (by nlinarith [hτ.1, hτ.2])
  have hτ0 := hτ.1
  have hn' : ∀ b, xn b < 0 := fun b => (hxn b).2
  have hg' : ∀ p, 0 < gp p := fun p => (hgp p).1
  rw [Fintype.sum_bool, Lpart_true_eq hτ0 hν xn gp hn' hg' D.μ,
    Lpart_false_eq hτ0 hν xn gp hn' hg' D.μ] at h2
  -- the `η`-share: the Chebyshev tangent at `p` with weights `1/ν`
  have hWs : ∑ _i : Fin (k + q), (1 / D.ν) = ((k + q : ℕ) : ℝ) / D.ν := by
    simp [div_eq_mul_inv]
  have hW1 : ((k + q : ℕ) : ℝ) / D.ν ≤ 1 := by rw [div_le_one hν]; exact hp
  have hW0 : 0 ≤ ((k + q : ℕ) : ℝ) / D.ν := by positivity
  have hc := cos_tangent_w he (Fin.append xn gp) hx hinj (fun _ => 1 / D.ν)
    (fun _ => by positivity) (by rw [hWs]; exact hW1) D.p hpS
  rw [wvand_const, hWs, show realEnergyTau D.e = D.τ from rfl] at hc
  have hS2 : ∑ _i : Fin (k + q), (1 / D.ν) ^ 2 = ((k + q : ℕ) : ℝ) / D.ν ^ 2 := by
    simp [div_eq_mul_inv]
  have hS2le : ((k + q : ℕ) : ℝ) / D.ν ^ 2 ≤ 1 / D.ν := by
    rw [div_le_div_iff₀ (by positivity) hν]; nlinarith
  rw [hS2] at hc
  have herrη := D.eta_err_le hν he hη0 hW0 hW1 hS2le (tsum_nonneg fun _ => abs_nonneg _)
  have hTp : ∑ i : Fin (k + q), (1 / D.ν) * barrierTrialT D.p (Fin.append xn gp i) =
      (1 / D.ν) * ∑ i, barrierTrialT D.p (Fin.append xn gp i) := by rw [Finset.mul_sum]
  rw [hTp] at hc
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * D.η by linarith)
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * (1 - D.η) by linarith)
  have h3 := logPref_le_prefTau hτ1 hν xn gp hxn hgp
  have hnorm1 : ∀ b, |D.τ * xn b| < 1 := fun b => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |xn b| < 1 := abs_lt.mpr ⟨(hxn b).1, by linarith [(hxn b).2]⟩
    nlinarith [hτ.2, abs_nonneg (xn b)]
  have hnorm2 : ∀ p, |D.τ * gp p| < 1 := fun p => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |gp p| < 1 := abs_lt.mpr ⟨by linarith [(hgp p).1], (hgp p).2⟩
    nlinarith [hτ.2, abs_nonneg (gp p)]
  have h4 := prefTau_eq hν xn gp hnorm1 hnorm2
  have hxn1 : ∀ b, |xn b| ≤ 1 := fun b => (abs_lt.mpr ⟨(hxn b).1, by linarith [(hxn b).2]⟩).le
  have hgp1 : ∀ p, |gp p| ≤ 1 := fun p => (abs_lt.mpr ⟨by linarith [(hgp p).1], (hgp p).2⟩).le
  have hB := isGeom_powSum hτ0 hν xn hxn1
  have hP := isGeom_powSum hτ0 hν gp hgp1
  have hmp : IsGeom D.τ (mpos D.μ D.τ) := isGeom_mpos hμ hτ0
  have hmn : IsGeom D.τ (mneg D.μ D.τ) := isGeom_mneg hμ hτ0
  have h5 := quad_master hτ hB hP hR hmp hmn ht hη
  have hl1 := ip_powSum_left hτ hν gp hgp1 (hmp.add hR)
  have hl2 := ip_powSum_left hτ hν xn hxn1 (((hmn.sub ht).const_mul (2 * (1 - D.η))).sub hR)
  have hsN : ∑ b, D.fNeg (xn b) = (∑ b, D.rowBase (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => 2 * (1 - D.η) * (mneg D.μ D.τ n - D.t n) - D.R n) (xn b) := by
    unfold SignedData.fNeg
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsP : ∑ p, D.fPos (gp p) = (∑ p, D.rowBase (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) + (q : ℝ) * (2 * D.Sup) := by
    unfold SignedData.fPos
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hbase : ∑ i, D.rowBase (Fin.append xn gp i) =
      (∑ i, D.Rf (Fin.append xn gp i)) - (∑ i, barrierTrialS D.v (Fin.append xn gp i)) -
        (∑ i, Real.log (1 - Fin.append xn gp i)) / (2 * D.ν) +
        ((1 - D.η) / D.ν) * (∑ i, (-Real.log |Fin.append xn gp i| +
          Real.log (1 / (1 - D.τ ^ 2)))) -
        2 * (1 - D.η) * (∑ i, rowRef D.μ (Fin.append xn gp i)) -
        4 * D.η * (∑ i, barrierTrialT D.p (Fin.append xn gp i)) := by
    unfold SignedData.rowBase
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_div]
  rw [row_sum_split D.rowBase xn gp] at hbase
  have hsC : ∑ j, D.fCol (sc j) = (∑ j, D.Cf (sc j)) + (∑ j, 2 * barrierTrialT D.v (sc j)) -
      (∑ j, Real.log (1 - sc j)) / D.ν := by
    unfold SignedData.fCol
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hsplit : pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc =
      pinOffDiagonalInteraction D.ν 0 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |Fin.append xn gp j - Fin.append xn gp i|) /
          D.ν ^ 2 := by
    unfold pinOffDiagonalInteraction; ring
  have h4' : prefTau D.τ D.ν xn gp =
      -(1 / 2) * ip (powSum D.τ D.ν xn) (powSum D.τ D.ν xn) +
        ip (powSum D.τ D.ν xn) (powSum D.τ D.ν gp) -
        (1 / (2 * D.ν ^ 2)) * ∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b)) := h4
  have hhad := D.hadErr_nonneg hν he
  unfold SignedData.numB SignedData.denB at hA7
  unfold SignedData.constTotal SignedData.eD7 SignedData.Kq
  rw [hsplit]
  have hsN' := congrArg (fun z => (1 / D.ν) * z) hsN
  have hsP' := congrArg (fun z => (1 / D.ν) * z) hsP
  have hsC' := congrArg (fun z => (1 / D.ν) * z) hsC
  have hbase' := congrArg (fun z => (1 / D.ν) * z) hbase
  beta_reduce at hsN' hsP' hsC' hbase'
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h1 h2' hc' hbase' hsC' hA7
  ring_nf at hA7 h1 h2' hc' herrη h3 h4' h5 hl1 hl2 hbase' hsN' hsP' hsC' ⊢
  linarith only [hA7, h1, h2', hc', herrη, h3, h4', h5, hl1, hl2, hbase', hsN', hsP', hsC', hhad]

/-- The spike cost: `cs` per positive node beyond `1 - θ`, per `ν`. -/
def SignedData.spikeTerm (D : SignedData) {q : ℕ} (gp : Fin q → ℝ) : ℝ :=
  (1 / D.ν) * ∑ p, D.cs * (if 1 - D.θ < gp p then 1 else 0)

/-- The positive field with the spike cost attached. -/
def SignedData.fPosS (D : SignedData) (x : ℝ) : ℝ :=
  D.fPos x + D.cs * (if 1 - D.θ < x then 1 else 0)

/-- The additive error of the spike lemmas: the J3 dilation error `(4e/c')(s/ν)(nrows/ν)`
(`c' ∈ (0,1]` the margin of the non-spike positives; the negatives need none, one-sided J3) plus
the phantom charge `kph/ν` of an odd spike count (SIMPLIFY-S2 §2.3: `O(N)` once, `o(N²)`). -/
def SignedData.errJ3 (D : SignedData) (c' : ℝ) (nrows : ℕ) : ℝ :=
  (4 * D.e / c') * ((D.sp : ℝ) / D.ν) * ((nrows : ℝ) / D.ν) + D.kph / D.ν

/-- **The A7 interface (bound form).**  `LR xn gp` is the logarithm of the route II ratio
`log Pref + log Z(φψ) − log Z(ψ)` (`logRatioZ`).  For every configuration of the class `Cls`
(negatives in `(-1,0)`, positives in `(0,1)`, spikes counted by `cs`) the ratio is bounded by the
consumer's expression `numB − denB` at the TRUE positions plus the spike cost
(`SpikeReduction` followed by `SpikeCompare` of SIMPLIFY-S2 §1.3 and PROOF-A 17.38; the cap `θ`,
the constant `C ≤ 1.02` per spike, and the class bound `M ≤ 1.1228 N` live in `Cls` and `cs`). -/
def SpikeCompare (D : SignedData) (c' : ℝ) {k q : ℕ}
    (Cls : (Fin k → ℝ) → (Fin q → ℝ) → Prop)
    (LR : (Fin k → ℝ) → (Fin q → ℝ) → ℝ) : Prop :=
  ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ), (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
    Cls xn gp →
    LR xn gp / D.ν ^ 2 ≤ logPref xn gp / D.ν ^ 2 + D.numB xn gp - D.denB gp + D.spikeTerm gp +
        D.errJ3 c' (k + q)

/-- **`SpikeCompare` at the configuration's Heine count** (NOTES-ETA §5.1): the class gives
`0 < sp` (reference count) and `sp + g ≤ q`, and the bound holds for `D.withCount (q - g)`. -/
def SpikeCompareCount (D : SignedData) (c' : ℝ) {k q : ℕ}
    (Cls : (Fin k → ℝ) → (Fin q → ℝ) → Prop)
    (LR : (Fin k → ℝ) → (Fin q → ℝ) → ℝ) : Prop :=
  (∀ xn gp, Cls xn gp → 0 < D.sp ∧ D.sp + D.g ≤ q) ∧
    SpikeCompare (D.withCount (q - D.g)) c' Cls LR

/-- The J3 error grows with the count. -/
theorem SignedData.errJ3_withCount_mono (D : SignedData) {c' : ℝ} (hc' : 0 < c')
    (he : 0 ≤ D.e) (hν : 0 < D.ν) {x y : ℕ} (hxy : x ≤ y) (n : ℕ) :
    (D.withCount x).errJ3 c' n ≤ (D.withCount y).errJ3 c' n := by
  unfold SignedData.errJ3
  simp only [SignedData.withCount_e, SignedData.withCount_sp, SignedData.withCount_ν,
    SignedData.withCount_kph]
  have h1 : (x : ℝ) / D.ν ≤ (y : ℝ) / D.ν :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hxy) hν.le
  have h2 : 0 ≤ 4 * D.e / c' := by positivity
  have h3 : 0 ≤ (n : ℝ) / D.ν := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
  linarith

/-- **The joint theorem (deterministic form, fixed `N`).** -/
theorem signed_second_energy_fixed (D : SignedData) {k q : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : D.μ.OK D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : ((k + q : ℕ) : ℝ) / D.ν = D.μ.mass)
    (hη0 : 0 ≤ D.η) (hη : D.η ≤ 1 / 2) (hpS : Summable (fun j => |D.p j|))
    {Cls : (Fin k → ℝ) → (Fin q → ℝ) → Prop} {LR : (Fin k → ℝ) → (Fin q → ℝ) → ℝ}
    {c' : ℝ} (hA7 : SpikeCompareCount D c' Cls LR)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hinj : Function.Injective (Fin.append xn gp))
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc) (hcls : Cls xn gp) :
    D.constant + pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |Fin.append xn gp j - Fin.append xn gp i|) / D.ν ^ 2 +
        (∑ i, D.Rf (Fin.append xn gp i)) / D.ν + (∑ j, D.Cf (sc j)) / D.ν + LR xn gp / D.ν ^ 2 ≤
      D.constTotal (k + q) + (D.withCount (q - D.g)).errJ3 c' (k + q) +
        (1 / D.ν) * (∑ b, D.fNeg (xn b)) +
        (1 / D.ν) * (∑ p, D.fPosS (gp p)) + (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  obtain ⟨hcnt, hA7⟩ := hA7
  obtain ⟨hsr0, hsrg⟩ := hcnt xn gp hcls
  have hA := hA7 xn gp hxn hgp hcls
  have hst : (D.withCount (q - D.g)).spikeTerm gp = D.spikeTerm gp := rfl
  rw [hst, SignedData.withCount_ν] at hA
  have hx0 : 0 < q - D.g := by omega
  have hsr : D.sp ≤ q - D.g := by omega
  have hxg : ((q - D.g : ℕ) : ℝ) + D.g = q := by
    rw [Nat.cast_sub (by omega)]; ring
  have h := signed_master D hν he hp hv hR ht hμ hC hmass hη0 hη hpS xn gp sc hxn hgp hinj hs hsi
    (LR xn gp) (D.spikeTerm gp + (D.withCount (q - D.g)).errJ3 c' (k + q)) (q - D.g) hx0 hsr hxg
    (by linarith only [hA])
  have hsp : D.spikeTerm gp + (1 / D.ν) * (∑ p, D.fPos (gp p)) =
      (1 / D.ν) * (∑ p, D.fPosS (gp p)) := by
    unfold SignedData.spikeTerm SignedData.fPosS
    rw [Finset.sum_add_distrib]; ring
  linarith only [h, hsp]

/-- **The contract** (sibling of `Analytic.SecondTrialBounds`): a family of instances indexed by
`N` (`ncount N = n N` rows and columns), the field caps, the constant's limit, the budget
inequality (linear in the negative fraction `κ`), and the A7 hypothesis `SpikeCompare`.
The numerical inputs (trial sequences, reference measures, field sups) are data and hypotheses
here; Phase 2 supplies them. -/
structure SignedTrialBounds where
  D : ℕ → SignedData
  ncount : ℕ → ℕ
  MXn : ℝ
  MXp : ℝ
  MY : ℝ
  cInf : ℝ
  B : ℝ
  κlo : ℝ
  κhi : ℝ
  Cls : ∀ N k q, (Fin k → ℝ) → (Fin q → ℝ) → Prop
  LR : ∀ N k q, (Fin k → ℝ) → (Fin q → ℝ) → ℝ
  ν_eq : ∀ N, (D N).ν = (ncount N : ℝ)
  ncount_pos : ∀ N, 0 < ncount N
  e_mem : ∀ᶠ N : ℕ in Filter.atTop, (D N).e ∈ Ioo (0 : ℝ) (1 / 8)
  v_summable : ∀ᶠ N : ℕ in Filter.atTop, Summable (fun j => |(D N).v j|)
  R_geom : ∀ᶠ N : ℕ in Filter.atTop, IsGeom (D N).τ (D N).R
  t_geom : ∀ᶠ N : ℕ in Filter.atTop, IsGeom (D N).τ (D N).t
  reference : ∀ᶠ N : ℕ in Filter.atTop, (D N).μ.OK (D N).Cb ∧ 0 ≤ (D N).Cb ∧
    (ncount N : ℝ) / (D N).ν = (D N).μ.mass
  eta_mem : ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ (D N).η ∧ (D N).η ≤ 1 / 2
  p_summable : ∀ᶠ N : ℕ in Filter.atTop, Summable (fun j => |(D N).p j|)
  cp : ℕ → ℝ
  cp_pos : ∀ N, 0 < cp N
  cp_le : ∀ N, cp N ≤ 1
  err_small : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ((D N).withCount (ncount N)).errJ3 (cp N) (ncount N) ≤ ε
  spike : ∀ N k q, SpikeCompareCount (D N) (cp N) (Cls N k q) (LR N k q)
  rowNeg : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (D N).fNeg x ≤ MXn + ε
  rowPos : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (D N).fPosS x ≤ MXp + ε
  column : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ∀ s ∈ Ioo (0 : ℝ) 1, (D N).fCol s ≤ MY + ε
  const_tendsto : Filter.Tendsto (fun N => (D N).constTotal (ncount N)) Filter.atTop (nhds cInf)
  budget : ∀ κ ∈ Icc κlo κhi, cInf + κ * MXn + (1 - κ) * MXp + MY ≤ B

/-- **Theorem `signed_second_energy`.**  For every `δ > 0` and all large `N`, every configuration
of `k` negatives and `q` positives with `k + q = n N` rows and `n N` columns, negative fraction in
`[κlo, κhi]` and in the class `Cls`, has
`constant + E_disc + fields + log(route II ratio)/ν² ≤ B + δ`. -/
theorem signed_second_energy (T : SignedTrialBounds) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (k q : ℕ), k + q = T.ncount N →
      T.κlo ≤ (k : ℝ) / (T.ncount N : ℝ) → (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi →
      ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (sc : Fin (k + q) → ℝ),
      (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append xn gp) → (∀ j, sc j ∈ Ioo (0 : ℝ) 1) →
      Function.Injective sc → T.Cls N k q xn gp →
      (T.D N).constant + pinOffDiagonalInteraction (T.D N).ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append xn gp j - Fin.append xn gp i|) / (T.D N).ν ^ 2 +
        (∑ i, (T.D N).Rf (Fin.append xn gp i)) / (T.D N).ν +
        (∑ j, (T.D N).Cf (sc j)) / (T.D N).ν + T.LR N k q xn gp / (T.D N).ν ^ 2 ≤ T.B + δ := by
  have hε : 0 < δ / 8 := by linarith
  filter_upwards [T.e_mem, T.v_summable, T.R_geom, T.t_geom, T.reference, T.eta_mem,
    T.p_summable, T.rowNeg hε,
    T.rowPos hε, T.column hε, T.err_small hε,
    T.const_tendsto.eventually (gt_mem_nhds (show T.cInf < T.cInf + δ / 8 by linarith))]
    with N he hv hR ht ⟨hμ, hC, hmass⟩ ⟨hη0, hη⟩ hpS hN hP hCo herr hconst k q hkq hlo hhi xn gp sc hxn hgp hinj
      hs hsi hcls
  have hνp : (0 : ℝ) < (T.ncount N : ℝ) := by exact_mod_cast T.ncount_pos N
  have hνe := T.ν_eq N
  have hν : 0 < (T.D N).ν := by rw [hνe]; exact hνp
  have hkqR : ((k + q : ℕ) : ℝ) = (T.ncount N : ℝ) := by exact_mod_cast hkq
  have hp : ((k + q : ℕ) : ℝ) ≤ (T.D N).ν := by rw [hνe, hkqR]
  have hmass' : ((k + q : ℕ) : ℝ) / (T.D N).ν = (T.D N).μ.mass := by
    rw [hkqR]; exact hmass
  have h := signed_second_energy_fixed (T.D N) hν he hp hv hR ht hμ hC hmass' hη0 hη hpS
    (T.spike N k q) xn gp sc hxn hgp hinj hs hsi hcls
  set κ : ℝ := (k : ℝ) / (T.ncount N : ℝ) with hκ
  have hq : (q : ℝ) / (T.ncount N : ℝ) = 1 - κ := by
    have : (k : ℝ) + q = T.ncount N := by exact_mod_cast hkq
    rw [hκ]; field_simp; linarith
  have h1 : (1 / (T.D N).ν) * (∑ b, (T.D N).fNeg (xn b)) ≤ κ * (T.MXn + δ / 8) := by
    have hs1 : ∑ b, (T.D N).fNeg (xn b) ≤ (k : ℝ) * (T.MXn + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun b => (T.D N).fNeg (xn b))
        (T.MXn + δ / 8) (fun b _ => hN _ (hxn b))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D N).ν) * ((k : ℝ) * (T.MXn + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = κ * (T.MXn + δ / 8) := by rw [hνe, hκ]; field_simp
  have h2 : (1 / (T.D N).ν) * (∑ p, (T.D N).fPosS (gp p)) ≤ (1 - κ) * (T.MXp + δ / 8) := by
    have hs1 : ∑ p, (T.D N).fPosS (gp p) ≤ (q : ℝ) * (T.MXp + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun p => (T.D N).fPosS (gp p))
        (T.MXp + δ / 8) (fun p _ => hP _ (hgp p))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D N).ν) * ((q : ℝ) * (T.MXp + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - κ) * (T.MXp + δ / 8) := by rw [hνe, ← hq]; field_simp
  have h3 : (1 / (T.D N).ν) * ∑ j, (T.D N).fCol (sc j) ≤ T.MY + δ / 8 := by
    have hs1 : ∑ j, (T.D N).fCol (sc j) ≤ ((k + q : ℕ) : ℝ) * (T.MY + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun j => (T.D N).fCol (sc j))
        (T.MY + δ / 8) (fun j _ => hCo _ (hs j))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D N).ν) * (((k + q : ℕ) : ℝ) * (T.MY + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = T.MY + δ / 8 := by rw [hνe, hkqR]; field_simp
  have hb := T.budget κ ⟨hlo, hhi⟩
  have hct : (T.D N).constTotal (k + q) = (T.D N).constTotal (T.ncount N) := by rw [hkq]
  have hej : ((T.D N).withCount (q - (T.D N).g)).errJ3 (T.cp N) (k + q) ≤
      ((T.D N).withCount (T.ncount N)).errJ3 (T.cp N) (T.ncount N) := by
    rw [hkq]
    exact (T.D N).errJ3_withCount_mono (T.cp_pos N) he.1.le hν (by omega) _
  rw [hct] at h
  nlinarith only [h, h1, h2, h3, hb, hconst, hδ, herr, hej]

end Master

/-! ### Lemma K/T and Theorem C.3 chains -/

section Chains

open CatalanMeasure.GenD.Signed in
/-- **Lemma T from the class** (Lemma K feeding Lemma T): the Loewner form of
`|Σ_{a>0} B'(x_a) x_a^e c_a²| ≤ (3/2) Σ c_a c_b/(1 - x_a x_b)` from the class data of Lemma K. -/
theorem lemmaT_of_class {n : ℕ} (hn : 0 < n) (x c : Fin n → ℝ) (hxi : Function.Injective x)
    (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) {e : ℕ} (he : 1 ≤ e)
    {d v : ℕ → ℝ} (hv : ∀ k, 0 < v k) {D Δ : ℝ} (hD : HasSum (fun k => d k ^ 2 / v k) D)
    (hDΔ : D ≤ Δ) (F : ℝ → ℕ → ℝ) (H cc ε : ℝ → ℝ)
    (hH : ∀ t, HasSum (fun k => F t k ^ 2 * v k) (H t))
    {a₀ t₀ φ : ℝ} (ha₀ : 0 < a₀) (ht₀ : 0 < t₀)
    (hfew : ((Finset.univ.filter (fun a => |x a| < a₀)).card : ℝ) ≤ φ * n)
    (hsmall : (n : ℝ) * (φ + t₀ ^ 2 / a₀ ^ 2) < e)
    (hstat : ∀ t ∈ Ioc (0 : ℝ) 1, t₀ ≤ t →
      |(∑ a, slopeKernel t (x a)) / n - (cc t + ∑' k, F t k * d k)| ≤ ε t)
    (hbig : ∀ t ∈ Ioc (0 : ℝ) 1, t₀ ≤ t →
      (n : ℝ) * (cc t + Real.sqrt (H t * Δ) + ε t) < e) :
    |∑ a ∈ Finset.univ.filter (fun a => 0 < x a), bDeriv x a * x a ^ e * c a ^ 2| ≤
      (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b) :=
  lemmaT_of_slope x c hxi hx1 hx0 he
    (slope_of_class hn x e hv hD hDΔ F H cc ε hH ha₀ ht₀ hfew hsmall hstat hbig)

open CatalanMeasure.GenD.Signed Matrix in
open scoped ComplexOrder in
/-- **Theorem C.3 with `τ' ≤ 3/2`:** `|det L| ≤ 11^{k₊} det L₋₋` at the level of the block
matrices consumed by `norm_det_fromBlocks_sub_le_two_six`.  The D58 instance must supply
`L = fromBlocks A Cᴴ C (D - 6 T)` with `A = L₋₋` (negative block, positive definite), the Pick
matrix `fromBlocks A Cᴴ C D` positive semidefinite with norm ≤ 2, and `T` with `‖T‖ ≤ τ ≤ 3/2`
(Loewner form), which comes from `lemmaT_of_class`. -/
theorem abs_det_fromBlocks_le_eleven {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : Matrix m m ℂ} {C : Matrix n m ℂ} {D T : Matrix n n ℂ}
    (hA : A.PosDef) (hL : (fromBlocks A Cᴴ C D).PosSemidef)
    (hb : ((2 : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks A Cᴴ C D).PosSemidef)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 3 / 2)
    (hT1 : ((τ : ℂ) • (1 : Matrix n n ℂ) - T).PosSemidef)
    (hT2 : ((τ : ℂ) • (1 : Matrix n n ℂ) + T).PosSemidef) :
    ‖(fromBlocks A Cᴴ C (D - (6 : ℂ) • T)).det‖ ≤ 11 ^ Fintype.card n * A.det.re := by
  have h := norm_det_fromBlocks_sub_le_two_six hA hL hb hT1 hT2
  have hre : 0 ≤ A.det.re := ((Complex.lt_def.mp hA.det_pos).1).le
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hre)
  exact pow_le_pow_left₀ (by linarith) (by linarith) _

end Chains

/-! ### The concrete ratio -/

/-- `log Pref + log Z(φψ) − log Z(ψ)` of `route_two` with `φ = ∏_b (1 + 2 x_b u + x_b²)` and
`ψ = ∏_p (1 + 2 g_p u + g_p²)⁻¹`; this is the `LR` of the contract. -/
def logRatioZ {k q : ℕ} (sp : ℕ) (xn : Fin k → ℝ) (gp : Fin q → ℝ) : ℝ :=
  logPref xn gp +
    Real.log (CatalanMeasure.GenD.Signed.heineZ sp (fun u =>
      (∏ b, (1 + 2 * xn b * u + xn b ^ 2)) / ∏ p, (1 + 2 * gp p * u + gp p ^ 2))) -
    Real.log (CatalanMeasure.GenD.Signed.heineZ sp (fun u =>
      1 / ∏ p, (1 + 2 * gp p * u + gp p ^ 2)))





section RouteTwo

open CatalanMeasure.GenD.Signed

theorem heineZ_pos {s : ℕ} (f : ℝ → ℝ) (hf : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 < f u)
    (hc : ContinuousOn (fun u => Real.log (f u)) (Set.Icc (-1 : ℝ) 1))
    (hm : Measurable (fun u => Real.log (f u))) : 0 < heineZ s f := by
  rw [heineZ_eq_denZ f hf]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact (arcsine_jensen_denominator isTrial_arcsine hm
    (fun u hu => by simpa [Real.norm_eq_abs] using hM u hu) s).1

theorem fac_pos {y u : ℝ} (hy : |y| < 1) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    0 < 1 + 2 * y * u + y ^ 2 := by
  have h1 : |y * u| ≤ |y| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨hu.1, hu.2⟩)
  have h2 := (abs_le.mp h1).1
  nlinarith [sq_abs y, abs_nonneg y, sq_nonneg (1 - |y|)]

/-- The log of the `route_two` determinant ratio is `logRatioZ`. -/
theorem log_route_two {q : ℕ} (g : Fin q → ℝ) (hg : ∀ i, |g i| < 1) (s k e : ℕ) (hk : 0 < k)
    (hs : q < 2 * s) (he : e + q + 1 = 2 * s + k) (x : Fin k → ℝ) (hinj : Function.Injective x)
    (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1) :
    Real.log ((kMat x + dMinus (hOfRoots g) q e x).det / (kMat x).det) = logRatioZ s x g := by
  rw [route_two g hg s k e hk hs he x hinj hx0 hx1]
  have hpos : ∀ a b : ℝ, |a| < 1 → |b| < 1 → 0 < 1 - a * b := by
    intro a b ha hb
    have := mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg a) ha hb.le
    have h2 : |a * b| < 1 := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
    linarith [(abs_lt.mp h2).2]
  have hA : 0 < ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (1 - x i * x j) :=
    Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => hpos _ _ (hx1 i) (hx1 j)
  have hB : 0 < ∏ b : Fin k, ∏ i : Fin q, (1 - g i * x b)⁻¹ :=
    Finset.prod_pos fun b _ => Finset.prod_pos fun i _ => inv_pos.mpr (hpos _ _ (hg i) (hx1 b))
  have hfac : ∀ (z : Fin k → ℝ) (w : Fin q → ℝ), (∀ b, |z b| < 1) → (∀ i, |w i| < 1) →
      ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 < (∏ b, (1 + 2 * z b * u + z b ^ 2)) /
        ∏ i, (1 + 2 * w i * u + w i ^ 2) := by
    intro z w hz hw u hu
    exact div_pos (Finset.prod_pos fun b _ => fac_pos (hz b) hu)
      (Finset.prod_pos fun i _ => fac_pos (hw i) hu)
  have hfac1 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 < 1 / ∏ i, (1 + 2 * g i * u + g i ^ 2) := fun u hu =>
    one_div_pos.mpr (Finset.prod_pos fun i _ => fac_pos (hg i) hu)
  have cont : ∀ (z : Fin k → ℝ), Continuous fun u : ℝ => ∏ b, (1 + 2 * z b * u + z b ^ 2) :=
    fun z => continuous_finset_prod _ fun b _ => by fun_prop
  have contg : Continuous fun u : ℝ => ∏ i, (1 + 2 * g i * u + g i ^ 2) :=
    continuous_finset_prod _ fun b _ => by fun_prop
  have hZ1 : 0 < heineZ s (fun u => (∏ b, (1 + 2 * x b * u + x b ^ 2)) /
      ∏ i, (1 + 2 * g i * u + g i ^ 2)) := by
    refine heineZ_pos _ (hfac x g hx1 hg) ?_ ?_
    · refine ContinuousOn.log ((cont x).continuousOn.div contg.continuousOn fun u hu =>
        (Finset.prod_pos fun i _ => fac_pos (hg i) hu).ne') fun u hu => (hfac x g hx1 hg u hu).ne'
    · exact ((cont x).measurable.div contg.measurable).log
  have hZ2 : 0 < heineZ s (fun u => 1 / ∏ i, (1 + 2 * g i * u + g i ^ 2)) := by
    refine heineZ_pos _ hfac1 ?_ ?_
    · exact ContinuousOn.log (continuousOn_const.div contg.continuousOn fun u hu =>
        (Finset.prod_pos fun i _ => fac_pos (hg i) hu).ne') fun u hu => (hfac1 u hu).ne'
    · exact (measurable_const.div contg.measurable).log
  rw [Real.log_mul (mul_pos hA hB).ne' (div_pos hZ1 hZ2).ne', Real.log_mul hA.ne' hB.ne',
    Real.log_div hZ1.ne' hZ2.ne']
  unfold logRatioZ logPref
  rw [Real.log_prod (fun i _ => (Finset.prod_pos fun j _ => hpos _ _ (hx1 i) (hx1 j)).ne'),
    Real.log_prod (fun b _ => (Finset.prod_pos fun i _ =>
      inv_pos.mpr (hpos _ _ (hg i) (hx1 b))).ne')]
  simp only [Real.log_prod (fun j _ => (hpos _ _ (hx1 _) (hx1 j)).ne'),
    Real.log_prod (fun i _ => (inv_pos.mpr (hpos _ _ (hg i) (hx1 _))).ne'), Real.log_inv,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  ring

end RouteTwo


section Bridge532

/-- **Bridge to the 532 functional.**  For `a = b = 0` the grouped value is the contract's left
side: pin principal (free-row copy) plus the all-row Vandermonde plus the fields. -/
theorem groupedValue_free_eq (ν c : ℝ) (R M L C : ℝ → ℝ) {r : ℕ} (z s : Fin r → ℝ)
    (x y : Fin 0 → ℝ) :
    CatalanMeasure.Parametric.groupedValueWithFields ν c R M L C z x y s =
      c + pinOffDiagonalInteraction ν 1 z s +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) / ν ^ 2 +
        (∑ i, R (z i)) / ν + (∑ j, C (s j)) / ν := by
  have hap : (Fin.append z x : Fin (r + 0) → ℝ) = z := funext fun i => Fin.append_left z x i
  unfold CatalanMeasure.Parametric.groupedValueWithFields
    CatalanMeasure.Parametric.groupedPopulationInteraction
    CatalanMeasure.Parametric.crossCauchyProduct
  rw [hap]
  simp
  ring

/-- A sum over ordered pairs `i < j` of a symmetric function is invariant under relabelling. -/
theorem sum_Ioi_perm {p : ℕ} (g : ℝ → ℝ → ℝ) (hg : ∀ a b, g a b = g b a) (x : Fin p → ℝ)
    (e : Equiv.Perm (Fin p)) :
    ∑ i, ∑ j ∈ Finset.Ioi i, g (x (e i)) (x (e j)) = ∑ i, ∑ j ∈ Finset.Ioi i, g (x i) (x j) := by
  have h1 := sum_offdiag_eq_two_mul (p := p) (fun i j => g (x (e i)) (x (e j)))
    (fun i j => hg _ _)
  have h2 := sum_offdiag_eq_two_mul (p := p) (fun i j => g (x i) (x j)) (fun i j => hg _ _)
  have h3 : (∑ i : Fin p, ∑ j : Fin p, if i = j then (0 : ℝ) else g (x (e i)) (x (e j))) =
      ∑ i : Fin p, ∑ j : Fin p, if i = j then (0 : ℝ) else g (x i) (x j) := by
    rw [← Equiv.sum_comp e (fun i => ∑ j : Fin p, if i = j then (0 : ℝ) else g (x i) (x j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e (fun j => if e i = j then (0 : ℝ) else g (x (e i)) (x j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [e.injective.eq_iff]
  linarith

/-- `pinOffDiagonalInteraction` is invariant under independent relabellings of rows and columns. -/
theorem pinOff_perm {p : ℕ} (ν k : ℝ) (x s : Fin p → ℝ) (e e' : Equiv.Perm (Fin p)) :
    pinOffDiagonalInteraction ν k (fun i => x (e i)) (fun j => s (e' j)) =
      pinOffDiagonalInteraction ν k x s := by
  unfold pinOffDiagonalInteraction
  have a1 := sum_Ioi_perm (fun a b => Real.log |b - a|) (fun a b => by rw [abs_sub_comm]) x e
  have a2 := sum_Ioi_perm (fun a b => Real.log (1 - a * b)) (fun a b => by rw [mul_comm]) x e
  have a3 := sum_Ioi_perm (fun a b => Real.log |b - a|) (fun a b => by rw [abs_sub_comm]) s e'
  have a4 : (∑ i : Fin p, ∑ j : Fin p, Real.log (1 - 2 * x (e i) * s (e' j) + x (e i) ^ 2)) =
      ∑ i : Fin p, ∑ j : Fin p, Real.log (1 - 2 * x i * s j + x i ^ 2) := by
    rw [← Equiv.sum_comp e (fun i => ∑ j : Fin p, Real.log (1 - 2 * x i * s j + x i ^ 2))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp e' (fun j => Real.log (1 - 2 * x (e i) * s j + x (e i) ^ 2))
  rw [a1, a2, a3, a4]

end Bridge532

end
end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.pin_zero_canonical
#print axioms CatalanMeasure.Signed.rows_vandermonde_le
#print axioms CatalanMeasure.Signed.pair_log_add_cross_le_tilted_ref
#print axioms CatalanMeasure.Signed.bDeriv_eq_negBlaschkeDeriv
#print axioms CatalanMeasure.Signed.lebPi_diag_null
#print axioms CatalanMeasure.Signed.heineZ_eq_denZ
#print axioms CatalanMeasure.Signed.denZ_le
#print axioms CatalanMeasure.Signed.heineZ_pos
#print axioms CatalanMeasure.Signed.logPref_le_prefTau
#print axioms CatalanMeasure.Signed.prefTau_eq
#print axioms CatalanMeasure.Signed.quad_master
#print axioms CatalanMeasure.Signed.Lpart_true_eq
#print axioms CatalanMeasure.Signed.Lpart_false_eq
#print axioms CatalanMeasure.Signed.crossTiltNormRef_append
#print axioms CatalanMeasure.Signed.signed_master
#print axioms CatalanMeasure.Signed.signed_second_energy_fixed
#print axioms CatalanMeasure.Signed.signed_second_energy
#print axioms CatalanMeasure.Signed.lemmaT_of_class
#print axioms CatalanMeasure.Signed.abs_det_fromBlocks_le_eleven
#print axioms CatalanMeasure.Signed.log_route_two
#print axioms CatalanMeasure.Signed.groupedValue_free_eq
#print axioms CatalanMeasure.Signed.pinOff_perm
#print axioms CatalanMeasure.Signed.pinOff_two
#print axioms CatalanMeasure.Signed.rows_vandermonde_le_w
#print axioms CatalanMeasure.Signed.cos_tangent_w
#print axioms CatalanMeasure.Signed.wvand_append
#print axioms CatalanMeasure.Signed.ip_wpow_left
