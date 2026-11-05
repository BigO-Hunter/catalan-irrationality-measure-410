module

public import Submission.CatalanMeasure.GenD.Signed.EnergyFixed
public import Submission.CatalanMeasure.GenD.Signed.ArcsinePhantom

/-!
# The signed second-sheet energy bound with fixed first-kind and near-type nodes

Extension of `Signed.EnergyFixed` by a third fixed population: the **near-type** positive nodes
`zp` (the set `S` of the marked positives of Lemma 17.43.1, `MarkedExpansion`).  In the
`S`-term of the determinant expansion the pairs (near, other) carry `log (1 - x y)` instead of
`log |x - y|` (the `groupedPairProduct` of the 532 route).  The near step follows PROOF-A §17.43
and joint-cert NOTES §17.2 (the near field of `scripts/nearcert.py`):

* **the η split** (NOTES §12.1, NOTES-ETA §1): the non-near Vandermonde is `2 WV_w + ½ V(M)` with
  weights `1` (free) and `1/2` (fixed); `2(1 - η) WV_w` by weighted D7.1 at `μ = c_r`, `2η WV_w`
  by the Chebyshev tangent at `p`, `½ V(M)` by the Chebyshev bound (PROOF-A §17.40);
* **mass defect, arcsine compensation** (17.2 step 2): the weighted D7.1 uses the reference `μ` of
  mass `(k + q)/ν + (m₁ + m₂ + s)/(2ν)` (independent of the near count), the defect `s/(2ν)`
  filled by the arcsine law (`rows_vandermonde_phantom`);
* **positive cross-Cauchy pairs** (step 1): `Σ log (1 - u z)/ν² ≤ -ip (P, Q)` cancels the cross
  term of the decay convexity `½ L(ρ⁺)` exactly;
* **negative cross pairs** (step 4): the free rows and half of the first-kind rows go against the
  spare negative `L`-term of D7.1 (Cauchy–Schwarz, cost `ip (Q, Q)/(4(1 - η))`), the other half of
  the first-kind negatives is bounded pointwise by `log (1 + z)` (the `(α/2) log (1 + x)` field);
* **near self-energy** (step 5): the near-near Vandermonde plus `½ ip (Q, Q)` is at most the
  diagonal `(1/(2ν²)) Σ -log (1 - z²)`;
* the fixed rows carry their own row fields `Rm` (first kind, `groupedMarkedField`) and `Rn`
  (near, `groupedNearField`), the exact fields of the 532 identity `log_groupedProduct`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### Power sums of appended lists -/

theorem powSum_append {a b : ℕ} (τ ν : ℝ) (y : Fin a → ℝ) (z : Fin b → ℝ) (n : ℕ) :
    powSum τ ν (Fin.append y z) n = powSum τ ν y n + powSum τ ν z n := by
  unfold powSum
  rw [row_sum_split (fun u => (τ * u) ^ (n + 1)) y z]
  ring

theorem powSum_split3 {a b c : ℕ} (τ ν : ℝ) (gp : Fin a → ℝ) (yp : Fin b → ℝ) (zp : Fin c → ℝ)
    (n : ℕ) :
    powSum τ ν (Fin.append gp (Fin.append yp zp)) n =
      powSum τ ν (Fin.append gp yp) n + powSum τ ν zp n := by
  rw [powSum_append, powSum_append, powSum_append]; ring

theorem powSum_nonneg {m : ℕ} {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) (y : Fin m → ℝ)
    (hy : ∀ j, y j ∈ Ioo (0 : ℝ) 1) (n : ℕ) : 0 ≤ powSum τ ν y n := by
  unfold powSum
  exact div_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg
    (mul_nonneg hτ.le (hy j).1.le) _) hν.le

theorem ip_const_mul_left (β : ℝ) (u v : ℕ → ℝ) :
    ip (fun n => β * u n) v = β * ip u v := by
  unfold ip
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem ip_const_mul_right (β : ℝ) (u v : ℕ → ℝ) :
    ip u (fun n => β * v n) = β * ip u v := by
  unfold ip
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-! ### The cross Cauchy pairs -/

theorem cross_pp_le {a b : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (u : Fin a → ℝ) (z : Fin b → ℝ) (hu : ∀ i, u i ∈ Ioo (0 : ℝ) 1)
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    (∑ i, ∑ j, Real.log (1 - u i * z j)) / ν ^ 2 ≤ -ip (powSum τ ν u) (powSum τ ν z) := by
  have hu' : ∀ i, |τ * u i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hu i).1]
    nlinarith [hτ.1, hτ.2, (hu i).1, (hu i).2]
  have hz' : ∀ j, |τ * z j| < 1 := fun j => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hz j).1]
    nlinarith [hτ.1, hτ.2, (hz j).1, (hz j).2]
  have h := (hasSum_pair_powSum (τ := τ) hν hu' hz').tsum_eq
  have hip : ip (powSum τ ν u) (powSum τ ν z) =
      -(∑ i, ∑ j, Real.log (1 - (τ * u i) * (τ * z j))) / ν ^ 2 := h
  rw [hip, neg_div, neg_neg]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ν)
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have huz : 0 ≤ u i * z j := mul_nonneg (hu i).1.le (hz j).1.le
  have hlt : u i * z j < 1 := by nlinarith [(hu i).1, (hu i).2, (hz j).1, (hz j).2]
  have e : (τ * u i) * (τ * z j) = τ ^ 2 * (u i * z j) := by ring
  refine Real.log_le_log (by linarith) ?_
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.1.le hτ.2.le : τ ^ 2 ≤ 1) huz]

theorem cross_np_le {a b : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (xn : Fin a → ℝ) (z : Fin b → ℝ) (hx : ∀ i, xn i ∈ Ioo (-1 : ℝ) 0)
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    (∑ i, ∑ j, Real.log (1 - xn i * z j)) / ν ^ 2 ≤ -ip (powSum τ ν xn) (powSum τ ν z) +
      ((a : ℝ) * b / ν ^ 2) * Real.log (1 / τ ^ 2) := by
  have hx' : ∀ i, |τ * xn i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_neg (hx i).2]
    nlinarith [hτ.1, hτ.2, (hx i).1, (hx i).2]
  have hz' : ∀ j, |τ * z j| < 1 := fun j => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hz j).1]
    nlinarith [hτ.1, hτ.2, (hz j).1, (hz j).2]
  have h := (hasSum_pair_powSum (τ := τ) hν hx' hz').tsum_eq
  have hip : ip (powSum τ ν xn) (powSum τ ν z) =
      -(∑ i, ∑ j, Real.log (1 - (τ * xn i) * (τ * z j))) / ν ^ 2 := h
  rw [hip, neg_div, neg_neg]
  have hτ2 : 0 < τ ^ 2 := pow_pos hτ.1 2
  have hL : ∀ i j, Real.log (1 - xn i * z j) ≤
      Real.log (1 - (τ * xn i) * (τ * z j)) + Real.log (1 / τ ^ 2) := by
    intro i j
    have hxz : xn i * z j < 0 := mul_neg_of_neg_of_pos (hx i).2 (hz j).1
    have e : (τ * xn i) * (τ * z j) = τ ^ 2 * (xn i * z j) := by ring
    have hp1 : 0 < 1 - (τ * xn i) * (τ * z j) := by rw [e]; nlinarith
    have hp2 : 0 < 1 - xn i * z j := by linarith
    rw [← Real.log_mul hp1.ne' (by positivity)]
    refine Real.log_le_log hp2 ?_
    rw [e, mul_one_div, le_div_iff₀ hτ2]
    nlinarith [mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.1.le hτ.2.le : τ ^ 2 ≤ 1)
      (neg_nonneg.mpr hxz.le)]
  have hs : ∑ i, ∑ j, Real.log (1 - xn i * z j) ≤
      (∑ i, ∑ j, Real.log (1 - (τ * xn i) * (τ * z j))) +
        (a : ℝ) * b * Real.log (1 / τ ^ 2) := by
    calc ∑ i, ∑ j, Real.log (1 - xn i * z j)
        ≤ ∑ i : Fin a, ∑ j : Fin b,
            (Real.log (1 - (τ * xn i) * (τ * z j)) + Real.log (1 / τ ^ 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hL i j
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  calc (∑ i, ∑ j, Real.log (1 - xn i * z j)) / ν ^ 2
      ≤ ((∑ i, ∑ j, Real.log (1 - (τ * xn i) * (τ * z j))) +
          (a : ℝ) * b * Real.log (1 / τ ^ 2)) / ν ^ 2 :=
        div_le_div_of_nonneg_right hs (sq_nonneg ν)
    _ = _ := by ring

/-- The negative cross pairs, pointwise: `log (1 - y z) ≤ log (1 + z)` for `y ∈ (-1, 0)`. -/
theorem cross_neg_le_log {a b : ℕ} (y : Fin a → ℝ) (z : Fin b → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 0) (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    ∑ i, ∑ j, Real.log (1 - y i * z j) ≤ (a : ℝ) * ∑ j, Real.log (1 + z j) := by
  calc ∑ i, ∑ j, Real.log (1 - y i * z j) ≤ ∑ _i : Fin a, ∑ j, Real.log (1 + z j) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h1 : 0 < 1 - y i * z j := by nlinarith [(hy i).1, (hy i).2, (hz j).1, (hz j).2]
        exact Real.log_le_log h1 (by nlinarith [(hy i).1, (hy i).2, (hz j).1, (hz j).2])
    _ = (a : ℝ) * ∑ j, Real.log (1 + z j) := by simp

/-- **The near self-energy** (NOTES §17.2 step 5): the near-near Vandermonde and the convexity
`½ L(π) = ½ ip (Q, Q)` together are at most the diagonal `(1/(2ν²)) Σ -log (1 - z²)`
(`|z - z'| ≤ 1 - z z'`). -/
theorem near_near_le {b : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) (z : Fin b → ℝ)
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) (hzi : Function.Injective z) :
    (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) / ν ^ 2 +
        (1 / 2) * ip (powSum τ ν z) (powSum τ ν z) ≤
      (1 / (2 * ν ^ 2)) * ∑ j, -Real.log (1 - z j ^ 2) := by
  have hy : ∀ i, |τ * z i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hz i).1]
    nlinarith [hτ.1, hτ.2, (hz i).1, (hz i).2]
  have h := (hasSum_pair_powSum (τ := τ) hν hy hy).tsum_eq
  have hip : ip (powSum τ ν z) (powSum τ ν z) =
      -(∑ i, ∑ j, Real.log (1 - (τ * z i) * (τ * z j))) / ν ^ 2 := h
  set g : Fin b → Fin b → ℝ := fun i j => Real.log (1 - (τ * z i) * (τ * z j)) with hg
  have hgs : ∀ i j, g i j = g j i := fun i j => by simp only [hg]; ring_nf
  have hsplit : ∑ i, ∑ j, g i j = (∑ i, g i i) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
    rw [← sum_offdiag_eq_two_mul g hgs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hgi : ∀ j, g i j = (if i = j then g i j else 0) + (if i = j then 0 else g i j) := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hgi j), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  have hpair : ∀ i, ∀ j ∈ Finset.Ioi i, Real.log |z j - z i| ≤ g i j := by
    intro i j hj
    have hne : z j ≠ z i := fun h => (ne_of_lt (Finset.mem_Ioi.mp hj)).symm (hzi h)
    have hpos : 0 < |z j - z i| := abs_pos.mpr (sub_ne_zero.mpr hne)
    refine Real.log_le_log hpos ?_
    have h1 : |z j - z i| ≤ 1 - z i * z j := by
      rw [abs_le]
      constructor <;> nlinarith [(hz i).1, (hz i).2, (hz j).1, (hz j).2]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
    have h2 : 1 - z i * z j ≤ 1 - (τ * z i) * (τ * z j) := by
      have e : (τ * z i) * (τ * z j) = τ ^ 2 * (z i * z j) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hτ2 (mul_nonneg (hz i).1.le (hz j).1.le)]
    linarith
  have hdiag : ∀ i, -g i i ≤ -Real.log (1 - z i ^ 2) := by
    intro i
    simp only [hg]
    have h0 : 0 < 1 - z i ^ 2 := by nlinarith [(hz i).1, (hz i).2]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
    have hle : 1 - z i ^ 2 ≤ 1 - (τ * z i) * (τ * z i) := by
      have e : (τ * z i) * (τ * z i) = τ ^ 2 * z i ^ 2 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hτ2 (sq_nonneg (z i))]
    have := Real.log_le_log h0 hle
    linarith
  have hS1 : ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i| ≤
      ∑ i, ∑ j ∈ Finset.Ioi i, g i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpair i j hj
  have hS2 : ∑ i, -g i i ≤ ∑ i, -Real.log (1 - z i ^ 2) :=
    Finset.sum_le_sum fun i _ => hdiag i
  rw [hip]
  have hν2 : 0 < ν ^ 2 := by positivity
  have e1 : -(∑ i, ∑ j, Real.log (1 - (τ * z i) * (τ * z j))) = -(∑ i, ∑ j, g i j) := rfl
  rw [e1, hsplit]
  rw [Finset.sum_neg_distrib] at hS2
  have key : (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) / ν ^ 2 +
      (1 / 2) * (-(∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j) / ν ^ 2) =
      ((∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) - ∑ i, ∑ j ∈ Finset.Ioi i, g i j) / ν ^ 2 +
        (1 / (2 * ν ^ 2)) * (-(∑ i, g i i)) := by
    field_simp; ring
  rw [key]
  have h3 : ((∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) -
      ∑ i, ∑ j ∈ Finset.Ioi i, g i j) / ν ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hν2.le
  have h4 : (1 / (2 * ν ^ 2)) * (-(∑ i, g i i)) ≤
      (1 / (2 * ν ^ 2)) * ∑ j, -Real.log (1 - z j ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-! ### Block Vandermondes of the four row populations -/

/-- The Vandermonde `Σ_{i<j} log |y_j - y_i|` of one block. -/
def vd {m : ℕ} (y : Fin m → ℝ) : ℝ := ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |y j - y i|

/-- The cross term `Σ_i Σ_j log |y_j - x_i|` of two blocks. -/
def xd {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) : ℝ := ∑ i, ∑ j, Real.log |y j - x i|

/-- Block-constant weights on an appended list. -/
def wts {a b : ℕ} (c d : ℝ) : Fin (a + b) → ℝ := Fin.append (fun _ : Fin a => c) (fun _ : Fin b => d)

theorem vd_const {m : ℕ} (c : ℝ) (y : Fin m → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, c * c * Real.log |y j - y i| = c ^ 2 * vd y := by
  unfold vd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem xd_const {a b : ℕ} (c d : ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) :
    ∑ i, ∑ j, c * d * Real.log |y j - x i| = c * d * xd x y := by
  unfold xd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

theorem xd_append {a b c : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) (z : Fin c → ℝ) :
    xd x (Fin.append y z) = xd x y + xd x z := by
  unfold xd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem append_xd {a b c : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) (z : Fin c → ℝ) :
    xd (Fin.append x y) z = xd x z + xd y z := by
  unfold xd
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem vd_append {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) :
    vd (Fin.append x y) = vd x + xd x y + vd y := by
  unfold vd xd
  exact sum_Ioi_append_gen (fun u v : ℝ => Real.log |v - u|) x y

/-- **The weighted Vandermonde of the four populations** with block-constant weights. -/
theorem wvand4 {k m1 q m2 : ℕ} (cx cy cg cp : ℝ) (xn : Fin k → ℝ) (yn : Fin m1 → ℝ)
    (gp : Fin q → ℝ) (yp : Fin m2 → ℝ) :
    ∑ a, ∑ b ∈ Finset.Ioi a, Fin.append (wts cx cy) (wts cg cp) a *
        Fin.append (wts cx cy) (wts cg cp) b *
        Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) b -
          Fin.append (Fin.append xn yn) (Fin.append gp yp) a| =
      cx ^ 2 * vd xn + cy ^ 2 * vd yn + cg ^ 2 * vd gp + cp ^ 2 * vd yp +
        cx * cy * xd xn yn + cx * cg * xd xn gp + cx * cp * xd xn yp +
        cy * cg * xd yn gp + cy * cp * xd yn yp + cg * cp * xd gp yp := by
  rw [wvand_append]
  unfold wts
  rw [wvand_append, wvand_append]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Finset.sum_add_distrib,
    vd_const, xd_const]
  ring

theorem append_const {a b : ℕ} (c : ℝ) :
    Fin.append (fun _ : Fin a => c) (fun _ : Fin b => c) = fun _ => c := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- **The Vandermonde of the four populations** (unit weights). -/
theorem vand4 {k m1 q m2 : ℕ} (xn : Fin k → ℝ) (yn : Fin m1 → ℝ) (gp : Fin q → ℝ)
    (yp : Fin m2 → ℝ) :
    vd (Fin.append (Fin.append xn yn) (Fin.append gp yp)) =
      vd xn + vd yn + vd gp + vd yp + xd xn yn + xd xn gp + xd xn yp + xd yn gp + xd yn yp +
        xd gp yp := by
  rw [vd_append, vd_append, vd_append, append_xd, xd_append, xd_append]
  ring

/-- Sums of a block-weighted function over the four populations. -/
theorem sum_W4 {k m1 q m2 : ℕ} (c d : ℝ) (g F : ℝ → ℝ) (xn : Fin k → ℝ) (yn : Fin m1 → ℝ)
    (gp : Fin q → ℝ) (yp : Fin m2 → ℝ) :
    ∑ i, g (Fin.append (wts c d) (wts c d) i) *
        F (Fin.append (Fin.append xn yn) (Fin.append gp yp) i) =
      g c * ((∑ b, F (xn b)) + ∑ p, F (gp p)) + g d * ((∑ j, F (yn j)) + ∑ j, F (yp j)) := by
  unfold wts
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, ← Finset.mul_sum]
  ring

theorem wts_pos1 {a b : ℕ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ i, 0 < wts (a := a) (b := b) c d i := by
  intro i
  unfold wts
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [Fin.append_left]; exact hc
  · simp only [Fin.append_right]; exact hd

theorem wts_pos {a b a' b' : ℕ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ i, 0 < Fin.append (wts (a := a) (b := b) c d) (wts (a := a') (b := b') c d) i := by
  intro i
  unfold wts
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [Fin.append_left]; exact hc
    · simp only [Fin.append_right]; exact hd
  · simp only [Fin.append_right]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [Fin.append_left]; exact hc
    · simp only [Fin.append_right]; exact hd

theorem wts_nonneg {a b a' b' : ℕ} {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ i, 0 ≤ Fin.append (wts (a := a) (b := b) c d) (wts (a := a') (b := b') c d) i := by
  intro i
  unfold wts
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [Fin.append_left]; exact hc
    · simp only [Fin.append_right]; exact hd
  · simp only [Fin.append_right]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [Fin.append_left]; exact hc
    · simp only [Fin.append_right]; exact hd

theorem wpow_wts (τ ν : ℝ) {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) :
    wpow τ (wts (1 / ν) ((1 / 2) / ν)) (Fin.append x y) =
      fun n => powSum τ ν x n + powSum τ ν y n / 2 := by
  funext n
  unfold wts
  rw [wpow_append, wpow_const, wpow_const]
  ring

theorem ip_add_left' {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {u v c : ℕ → ℝ} (hu : IsGeom τ u)
    (hv : IsGeom τ v) (hc : IsGeom τ c) :
    ip (fun n => u n + v n) c = ip u c + ip v c := by
  have h := (hasSum_ip hτ hu hc).add (hasSum_ip hτ hv hc)
  rw [← h.tsum_eq]
  unfold ip
  exact tsum_congr fun n => by ring

/-! ### The quadratic tangent plane with a near species and the η split -/

/-- Pointwise form of `quad_master_eta`.  The difference of the two sides is
`(ε a - (Pm/2 - fp))²/(2ε) + ((1 + 1/ε)/2) Pm fp + (1 - η) (a' - (t - mn) + Q/(2(1-η)))²`,
`ε = 1 - 2η`, `a = Pf + Pm/2 + fp - mp`, `a' = Bf + Bm/2 + fn - mn` (NOTES-ETA §1.3). -/
theorem quad_eta_pt (Bf Bm Pf Pm Q R mp mn t fp fn η : ℝ) (hε : 0 < 1 - 2 * η)
    (hPφ : 0 ≤ Pm * fp) :
    -(1 / 2) * ((Bf + Bm) * (Bf + Bm)) + (Bf + Bm) * (Pf + Pm + Q) +
        (1 / 2) * ((Bf + Bm - (Pf + Pm + Q) - R) * (Bf + Bm - (Pf + Pm + Q) - R)) -
        (1 - η) * ((Pf + Pm / 2 + fp - mp) * (Pf + Pm / 2 + fp - mp)) -
        (1 - η) * ((Bf + Bm / 2 + fn - mn) * (Bf + Bm / 2 + fn - mn)) -
        (Pf + Pm) * Q - Bf * Q - (1 / 2) * (Bm * Q) - (1 / 2) * (Q * Q) ≤
      (Pf + Pm) * (mp + R) + Bf * (2 * (1 - η) * (mn - t) - R) +
        Bm * ((1 - η) * (mn - t) - R) + Q * (R - t + fn) + remC (1 - 2 * η) * (Pm * Pm) +
        (1 / (4 * (1 - η))) * (Q * Q) + (1 / 2) * (R * R) - (1 / 2) * (mp * mp) +
        (1 - η) * (t * t - mn * mn) + 4 * remC (1 - 2 * η) * (fp * fp) +
        2 * (1 - η) * ((mn - t) * fn) := by
  have h1 : 0 < 1 - η := by linarith
  have hε' : (1 - 2 * η) ≠ 0 := hε.ne'
  have h1' : (1 - η) ≠ 0 := h1.ne'
  have key : ((Pf + Pm) * (mp + R) + Bf * (2 * (1 - η) * (mn - t) - R) +
        Bm * ((1 - η) * (mn - t) - R) + Q * (R - t + fn) + remC (1 - 2 * η) * (Pm * Pm) +
        (1 / (4 * (1 - η))) * (Q * Q) + (1 / 2) * (R * R) - (1 / 2) * (mp * mp) +
        (1 - η) * (t * t - mn * mn) + 4 * remC (1 - 2 * η) * (fp * fp) +
        2 * (1 - η) * ((mn - t) * fn)) -
      (-(1 / 2) * ((Bf + Bm) * (Bf + Bm)) + (Bf + Bm) * (Pf + Pm + Q) +
        (1 / 2) * ((Bf + Bm - (Pf + Pm + Q) - R) * (Bf + Bm - (Pf + Pm + Q) - R)) -
        (1 - η) * ((Pf + Pm / 2 + fp - mp) * (Pf + Pm / 2 + fp - mp)) -
        (1 - η) * ((Bf + Bm / 2 + fn - mn) * (Bf + Bm / 2 + fn - mn)) -
        (Pf + Pm) * Q - Bf * Q - (1 / 2) * (Bm * Q) - (1 / 2) * (Q * Q)) =
      ((1 - 2 * η) * (Pf + Pm / 2 + fp - mp) - (Pm / 2 - fp)) ^ 2 / (2 * (1 - 2 * η)) +
        ((1 + 1 / (1 - 2 * η)) / 2) * (Pm * fp) +
        (1 - η) * (Bf + Bm / 2 + fn - mn - (t - mn) + Q / (2 * (1 - η))) ^ 2 := by
    unfold remC
    field_simp
    ring
  have hA : 0 ≤ ((1 - 2 * η) * (Pf + Pm / 2 + fp - mp) - (Pm / 2 - fp)) ^ 2 /
      (2 * (1 - 2 * η)) := div_nonneg (sq_nonneg _) (by linarith)
  have hB : 0 ≤ ((1 + 1 / (1 - 2 * η)) / 2) * (Pm * fp) := by
    have : 0 < 1 / (1 - 2 * η) := by positivity
    exact mul_nonneg (by linarith) hPφ
  have hC : 0 ≤ (1 - η) * (Bf + Bm / 2 + fn - mn - (t - mn) + Q / (2 * (1 - η))) ^ 2 :=
    mul_nonneg h1.le (sq_nonneg _)
  linarith

/-- **The tangent-plane inequality with the η split and a near species** (NOTES-ETA §1.3,
g-joint-cert NOTES §§12.1, 17.2).  `Bf, Bm` the free and first-kind negatives, `Pf, Pm` the free
and first-kind positives, `Q` the near rows, `φp, φn` the moments of the arcsine phantom of the
near mass defect.  Left: the route II prefactor and decay convexity, the D7.1 `L`-terms of the
weighted rows (`2(1 - η)` times, weights `1` free, `1/2` fixed), the positive cross pairs
`-ip (P, Q)`, the negative cross pairs `-ip (Bf, Q) - ½ ip (Bm, Q)` and the near convexity
`-½ ip (Q, Q)`.  Right: linear fields, Lemma R′ remainders and constants. -/
theorem quad_master_eta {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {Bf Bm Pf Pm Q R mp mn t φp φn : ℕ → ℝ}
    (hBf : IsGeom τ Bf) (hBm : IsGeom τ Bm) (hPf : IsGeom τ Pf) (hPm : IsGeom τ Pm)
    (hQ : IsGeom τ Q) (hR : IsGeom τ R) (hmp : IsGeom τ mp) (hmn : IsGeom τ mn)
    (ht : IsGeom τ t) (hφp : IsGeom τ φp) (hφn : IsGeom τ φn)
    (hPφ : ∀ n, 0 ≤ Pm n * φp n) {η : ℝ} (hε : 0 < 1 - 2 * η) :
    -(1 / 2) * ip (fun n => Bf n + Bm n) (fun n => Bf n + Bm n) +
        ip (fun n => Bf n + Bm n) (fun n => Pf n + Pm n + Q n) +
        (1 / 2) * ip (fun n => Bf n + Bm n - (Pf n + Pm n + Q n) - R n)
          (fun n => Bf n + Bm n - (Pf n + Pm n + Q n) - R n)
        - (1 - η) * ip (fun n => Pf n + Pm n / 2 + φp n - mp n)
          (fun n => Pf n + Pm n / 2 + φp n - mp n)
        - (1 - η) * ip (fun n => Bf n + Bm n / 2 + φn n - mn n)
          (fun n => Bf n + Bm n / 2 + φn n - mn n)
        - ip (fun n => Pf n + Pm n) Q - ip Bf Q - (1 / 2) * ip Bm Q - (1 / 2) * ip Q Q ≤
      ip (fun n => Pf n + Pm n) (fun n => mp n + R n) +
        ip Bf (fun n => 2 * (1 - η) * (mn n - t n) - R n) +
        ip Bm (fun n => (1 - η) * (mn n - t n) - R n) +
        ip Q (fun n => R n - t n + φn n) + remC (1 - 2 * η) * ip Pm Pm +
        (1 / (4 * (1 - η))) * ip Q Q + (1 / 2) * ip R R - (1 / 2) * ip mp mp +
        (1 - η) * (ip t t - ip mn mn) + 4 * remC (1 - 2 * η) * ip φp φp +
        2 * (1 - η) * ip (fun n => mn n - t n) φn := by
  have hB : IsGeom τ (fun n => Bf n + Bm n) := hBf.add hBm
  have hP : IsGeom τ (fun n => Pf n + Pm n) := hPf.add hPm
  have hPQ : IsGeom τ (fun n => Pf n + Pm n + Q n) := hP.add hQ
  have hBPR : IsGeom τ (fun n => Bf n + Bm n - (Pf n + Pm n + Q n) - R n) := (hB.sub hPQ).sub hR
  have hPm2 : IsGeom τ (fun n => Pm n / 2) := by
    simpa [div_eq_inv_mul] using hPm.const_mul ((2 : ℝ)⁻¹)
  have hBm2 : IsGeom τ (fun n => Bm n / 2) := by
    simpa [div_eq_inv_mul] using hBm.const_mul ((2 : ℝ)⁻¹)
  have hA1 : IsGeom τ (fun n => Pf n + Pm n / 2 + φp n - mp n) := ((hPf.add hPm2).add hφp).sub hmp
  have hA2 : IsGeom τ (fun n => Bf n + Bm n / 2 + φn n - mn n) := ((hBf.add hBm2).add hφn).sub hmn
  have hL : HasSum (fun n : ℕ => (-(1 / 2) * ((Bf n + Bm n) * (Bf n + Bm n)) +
      (Bf n + Bm n) * (Pf n + Pm n + Q n) +
      (1 / 2) * ((Bf n + Bm n - (Pf n + Pm n + Q n) - R n) *
        (Bf n + Bm n - (Pf n + Pm n + Q n) - R n)) -
      (1 - η) * ((Pf n + Pm n / 2 + φp n - mp n) * (Pf n + Pm n / 2 + φp n - mp n)) -
      (1 - η) * ((Bf n + Bm n / 2 + φn n - mn n) * (Bf n + Bm n / 2 + φn n - mn n)) -
      (Pf n + Pm n) * Q n - Bf n * Q n - (1 / 2) * (Bm n * Q n) - (1 / 2) * (Q n * Q n)) /
        ((n : ℝ) + 1))
      (-(1 / 2) * ip (fun n => Bf n + Bm n) (fun n => Bf n + Bm n) +
        ip (fun n => Bf n + Bm n) (fun n => Pf n + Pm n + Q n) +
        (1 / 2) * ip (fun n => Bf n + Bm n - (Pf n + Pm n + Q n) - R n)
          (fun n => Bf n + Bm n - (Pf n + Pm n + Q n) - R n)
        - (1 - η) * ip (fun n => Pf n + Pm n / 2 + φp n - mp n)
          (fun n => Pf n + Pm n / 2 + φp n - mp n)
        - (1 - η) * ip (fun n => Bf n + Bm n / 2 + φn n - mn n)
          (fun n => Bf n + Bm n / 2 + φn n - mn n)
        - ip (fun n => Pf n + Pm n) Q - ip Bf Q - (1 / 2) * ip Bm Q - (1 / 2) * ip Q Q) := by
    have h := (((((((((hasSum_ip hτ hB hB).mul_left (-(1 / 2))).add (hasSum_ip hτ hB hPQ)).add
      ((hasSum_ip hτ hBPR hBPR).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hA1 hA1).mul_left (1 - η))).sub
      ((hasSum_ip hτ hA2 hA2).mul_left (1 - η))).sub (hasSum_ip hτ hP hQ)).sub
      (hasSum_ip hτ hBf hQ)).sub ((hasSum_ip hτ hBm hQ).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hQ hQ).mul_left (1 / 2))
    convert h using 1
    funext n; ring
  have hMR : IsGeom τ (fun n => mp n + R n) := hmp.add hR
  have hN1 : IsGeom τ (fun n => 2 * (1 - η) * (mn n - t n) - R n) :=
    ((hmn.sub ht).const_mul (2 * (1 - η))).sub hR
  have hN2 : IsGeom τ (fun n => (1 - η) * (mn n - t n) - R n) :=
    ((hmn.sub ht).const_mul (1 - η)).sub hR
  have hQf : IsGeom τ (fun n => R n - t n + φn n) := (hR.sub ht).add hφn
  have hmt : IsGeom τ (fun n => mn n - t n) := hmn.sub ht
  have hR' : HasSum (fun n : ℕ => ((Pf n + Pm n) * (mp n + R n) +
      Bf n * (2 * (1 - η) * (mn n - t n) - R n) +
      Bm n * ((1 - η) * (mn n - t n) - R n) + Q n * (R n - t n + φn n) +
      remC (1 - 2 * η) * (Pm n * Pm n) + (1 / (4 * (1 - η))) * (Q n * Q n) +
      (1 / 2) * (R n * R n) - (1 / 2) * (mp n * mp n) +
      (1 - η) * (t n * t n - mn n * mn n) + 4 * remC (1 - 2 * η) * (φp n * φp n) +
      2 * (1 - η) * ((mn n - t n) * φn n)) / ((n : ℝ) + 1))
      (ip (fun n => Pf n + Pm n) (fun n => mp n + R n) +
        ip Bf (fun n => 2 * (1 - η) * (mn n - t n) - R n) +
        ip Bm (fun n => (1 - η) * (mn n - t n) - R n) +
        ip Q (fun n => R n - t n + φn n) + remC (1 - 2 * η) * ip Pm Pm +
        (1 / (4 * (1 - η))) * ip Q Q + (1 / 2) * ip R R - (1 / 2) * ip mp mp +
        (1 - η) * (ip t t - ip mn mn) + 4 * remC (1 - 2 * η) * ip φp φp +
        2 * (1 - η) * ip (fun n => mn n - t n) φn) := by
    have h := ((((((((((hasSum_ip hτ hP hMR).add (hasSum_ip hτ hBf hN1)).add
      (hasSum_ip hτ hBm hN2)).add (hasSum_ip hτ hQ hQf)).add
      ((hasSum_ip hτ hPm hPm).mul_left (remC (1 - 2 * η)))).add
      ((hasSum_ip hτ hQ hQ).mul_left (1 / (4 * (1 - η))))).add
      ((hasSum_ip hτ hR hR).mul_left (1 / 2))).sub ((hasSum_ip hτ hmp hmp).mul_left (1 / 2))).add
      (((hasSum_ip hτ ht ht).sub (hasSum_ip hτ hmn hmn)).mul_left (1 - η))).add
      ((hasSum_ip hτ hφp hφp).mul_left (4 * remC (1 - 2 * η)))).add
      ((hasSum_ip hτ hmt hφn).mul_left (2 * (1 - η)))
    convert h using 1
    funext n; ring
  refine hasSum_le (fun n => ?_) hL hR'
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hn]
  exact quad_eta_pt (Bf n) (Bm n) (Pf n) (Pm n) (Q n) (R n) (mp n) (mn n) (t n) (φp n) (φn n) η
    hε (hPφ n)

/-! ### Fields of the fixed rows (first kind with `Rm`, near with `Rn`) -/

namespace SignedData

variable (D : SignedData)

/-- Row field of a first-kind fixed row (weight `1/2` in the measure `c` of the `η` split): its
own field `Rm` (the exact `groupedMarkedField` of the 532 identity), the `(1 - η)`-share of D7.1
at weight `1/2` (diagonal cost and `μ`-potential) and the `η`-share tangent field `-2η T_p`. -/
def rowBaseM (Rm : ℝ → ℝ) (x : ℝ) : ℝ :=
  Rm x + ((1 - D.η) / (4 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
    (1 - D.η) * rowRef D.μ x - 2 * D.η * barrierTrialT D.p x

/-- Field of a first-kind fixed negative node. -/
def fNegM (Rm : ℝ → ℝ) (x : ℝ) : ℝ :=
  D.rowBaseM Rm x - (1 / (2 * D.ν)) * Real.log (1 - (D.τ * x) * (D.τ * x)) -
    2 * barrierTrialS D.a (-D.τ * x) +
    fld D.τ (fun n => (1 - D.η) * (mneg D.μ D.τ n - D.t n) - D.R n) x

/-- Field of a first-kind fixed positive node. -/
def fPosM (Rm : ℝ → ℝ) (x : ℝ) : ℝ :=
  D.rowBaseM Rm x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x + 2 * D.Sup

/-- With the spike cost attached. -/
def fPosMS (Rm : ℝ → ℝ) (x : ℝ) : ℝ := D.fPosM Rm x + D.cs * (if 1 - D.θ < x then 1 else 0)

/-- With the spike cost and the Lemma R′ remainder `rc · α · (-log (1 - x²))`. -/
def fPosMR (Rm : ℝ → ℝ) (rc α x : ℝ) : ℝ :=
  D.fPosMS Rm x + rc * α * (-Real.log (1 - x ^ 2))

/-- The arcsine-compensation constant per unit near mass: the cross of the arcsine phantom with
the negative tangent difference `mn - t` (it vanishes at the certificate's tilt `t = mn`). -/
def phConst : ℝ := (1 - D.η) * ip (fun n => mneg D.μ D.τ n - D.t n) (arcNeg D.τ)

/-- **Field of a near-type node** (second-sheet row of Lemma 17.43.1; NOTES §17.2 `f_near` with
the η split, NOTES-ETA §1.4): its own field `Rn`, the decay node terms of a positive node
(`2 S_a`, `-(sp/ν) denPoly`, the tilt `R`), the negative tangent `-t` and the arcsine cross
`(β/2) arcNeg`, the first-kind negatives `(α/2) log (1 + x)`, the Cauchy–Schwarz remainder
`(β/(4(1-η))) (-log (1 - x²))`, the near diagonal `(1/(2ν)) (-log (1 - x²))`, the vanishing
phantom and dilation costs, the arcsine constants and the near share `(η + α/2) log 2` of the
`log 2` count; `β = s/ν`. -/
def fNearM (Rn : ℝ → ℝ) (α β x : ℝ) : ℝ :=
  Rn x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => D.R n - D.t n + β / 2 * arcNeg D.τ n) x +
    (α / 2) * Real.log (1 + x) +
    (β / (4 * (1 - D.η)) + 1 / (2 * D.ν)) * (-Real.log (1 - x ^ 2)) +
    ((1 - D.η) / (4 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2)) + Real.log (1 / D.τ ^ 2) +
    D.phConst + remC (1 - 2 * D.η) * β * ip (arcPos D.τ) (arcPos D.τ) +
    (D.η + α / 2) * Real.log 2 + 2 * D.Sup

/-- With the spike cost attached. -/
def fNearMS (Rn : ℝ → ℝ) (α β x : ℝ) : ℝ :=
  D.fNearM Rn α β x + D.cs * (if 1 - D.θ < x then 1 else 0)

end SignedData

theorem sum_fNegM_eq (D : SignedData) (Rm : ℝ → ℝ) {k : ℕ} (xn : Fin k → ℝ) :
    ∑ b, D.fNegM Rm (xn b) = (∑ b, D.rowBaseM Rm (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => (1 - D.η) * (mneg D.μ D.τ n - D.t n) - D.R n) (xn b) := by
  unfold SignedData.fNegM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem sum_fPosM_eq (D : SignedData) (Rm : ℝ → ℝ) {q : ℕ} (gp : Fin q → ℝ) :
    ∑ p, D.fPosM Rm (gp p) = (∑ p, D.rowBaseM Rm (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) + (q : ℝ) * (2 * D.Sup) := by
  unfold SignedData.fPosM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_fNeg_eq (D : SignedData) {k : ℕ} (xn : Fin k → ℝ) :
    ∑ b, D.fNeg (xn b) = (∑ b, D.rowBase (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => 2 * (1 - D.η) * (mneg D.μ D.τ n - D.t n) - D.R n) (xn b) := by
  unfold SignedData.fNeg
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem sum_fPos_eq (D : SignedData) {q : ℕ} (gp : Fin q → ℝ) :
    ∑ p, D.fPos (gp p) = (∑ p, D.rowBase (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) + (q : ℝ) * (2 * D.Sup) := by
  unfold SignedData.fPos
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_rowBase_eq (D : SignedData) {k : ℕ} (x : Fin k → ℝ) :
    ∑ b, D.rowBase (x b) = (∑ b, D.Rf (x b)) - (∑ b, barrierTrialS D.v (x b)) -
      (∑ b, Real.log (1 - x b)) / (2 * D.ν) +
      ((1 - D.η) / D.ν) * (∑ b, (-Real.log |x b| + Real.log (1 / (1 - D.τ ^ 2)))) -
      2 * (1 - D.η) * (∑ b, rowRef D.μ (x b)) - 4 * D.η * (∑ b, barrierTrialT D.p (x b)) := by
  unfold SignedData.rowBase
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]

theorem sum_rowBaseM_eq (D : SignedData) (Rm : ℝ → ℝ) {k : ℕ} (x : Fin k → ℝ) :
    ∑ b, D.rowBaseM Rm (x b) = (∑ b, Rm (x b)) +
      ((1 - D.η) / (4 * D.ν)) * (∑ b, (-Real.log |x b| + Real.log (1 / (1 - D.τ ^ 2)))) -
      (1 - D.η) * (∑ b, rowRef D.μ (x b)) - 2 * D.η * (∑ b, barrierTrialT D.p (x b)) := by
  unfold SignedData.rowBaseM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem sum_fNearM_eq (D : SignedData) (Rn : ℝ → ℝ) (α β : ℝ) {s : ℕ} (zp : Fin s → ℝ) :
    ∑ j, D.fNearM Rn α β (zp j) = (∑ j, Rn (zp j)) +
      2 * (∑ j, barrierTrialS D.a (-D.τ * zp j)) -
      ((D.sp : ℝ) / D.ν) * (∑ j, denPoly D.b D.K (zp j)) +
      (∑ j, fld D.τ (fun n => D.R n - D.t n + β / 2 * arcNeg D.τ n) (zp j)) +
      (α / 2) * (∑ j, Real.log (1 + zp j)) +
      (β / (4 * (1 - D.η)) + 1 / (2 * D.ν)) * (∑ j, -Real.log (1 - zp j ^ 2)) +
      (s : ℝ) * (((1 - D.η) / (4 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2))) +
      (s : ℝ) * Real.log (1 / D.τ ^ 2) + (s : ℝ) * D.phConst +
      (s : ℝ) * (remC (1 - 2 * D.η) * β * ip (arcPos D.τ) (arcPos D.τ)) +
      (s : ℝ) * ((D.η + α / 2) * Real.log 2) + (s : ℝ) * (2 * D.Sup) := by
  unfold SignedData.fNearM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The barrier sums of the zero trial vanish. -/
theorem barrierTrialNormSq_zero : barrierTrialNormSq (fun _ => (0 : ℝ)) = 0 := by
  simp [barrierTrialNormSq]

theorem barrierTrialT_zero (x : ℝ) : barrierTrialT (fun _ => (0 : ℝ)) x = 0 := by
  simp [barrierTrialT]

/-- The Chebyshev bound of the half fixed-fixed Vandermonde, in the master's variables. -/
theorem had_key (e L α : ℝ) (he0 : 0 ≤ e) (hL2 : 0 ≤ L) (hlog2 : 0 ≤ Real.log 2) (a b c : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hab : a + b ≤ α) (hc : 0 ≤ c) :
    (1 / 2) * (-(1 / 2) * a ^ 2 * Real.log 2 + (1 / 2) * L * (a * c) + 2 * e * a ^ 2) ≤
      -(1 / 4) * (a + b) ^ 2 * Real.log 2 + b * (α / 2) * Real.log 2 + (L * c / 4 + e) := by
  have h1 : a * c ≤ c := mul_le_of_le_one_left hc ha1
  have h2 := mul_le_mul_of_nonneg_left h1 hL2
  have h3 : a ^ 2 ≤ 1 := pow_le_one₀ ha ha1
  have h4 : e * a ^ 2 ≤ e := mul_le_of_le_one_right he0 h3
  have h5 : (a + b) ^ 2 - a ^ 2 ≤ 2 * b * α := by
    have e1 : (a + b) ^ 2 - a ^ 2 = 2 * (b * (a + b)) - b * b := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hab hb
    nlinarith only [this, mul_nonneg hb hb]
  have h6 := mul_le_mul_of_nonneg_left h5 hlog2
  nlinarith only [h2, h4, h6]

/-- The `log 2` shift of the `η`-share between the non-near and the full weighted mass. -/
theorem eta_shift (η : ℝ) (hη0 : 0 ≤ η) (hlog2 : 0 ≤ Real.log 2) (A d : ℝ) (hA : 0 ≤ A)
    (hd : 0 ≤ d) (hAd : A + d ≤ 1) :
    -(η * A ^ 2 * Real.log 2) ≤ -(η * (A + d) ^ 2 * Real.log 2) + η * (2 * d) * Real.log 2 := by
  have h1 : (A + d) ^ 2 - A ^ 2 ≤ 2 * d := by
    have e : (A + d) ^ 2 - A ^ 2 = d * (2 * A + d) := by ring
    rw [e]
    have : 2 * A + d ≤ 2 := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left this hd]
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hη0 hlog2)
  nlinarith only [h2]

/-! ### The master inequality with a near species and the η split -/

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 8192 in
/-- **The master inequality with first-kind fixed and near-type nodes** (NOTES-ETA §1).  Free
rows `xn` (negative), `gp` (positive) with columns `sc`; first-kind fixed rows `yn`, `yp`;
near-type positive rows `zp`.  The non-near Vandermonde `V(F) + V(F ∪ M)` (pin copy and
determinant) is `2 WV_w + ½ V(M)` (weights `1` free, `1/2` fixed): `2(1 - η) WV_w` by weighted D7.1
at `μ` with the arcsine phantom of the near mass defect, `2η WV_w` by the Chebyshev tangent at
`p`, `½ V(M)` by the Chebyshev bound (PROOF-A §17.40); the route II ratio, the prefactor and the
tilted square on the positive list `gp ++ (yp ++ zp)`; the near species through
`quad_master_eta`, `near_near_le` and the cross bounds. -/
theorem signed_master_near (D : SignedData) {k q m1 m2 s : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8))
    (hall : ((((k + m1) + (q + m2)) + s : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : D.μ.OK D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : ((k + q : ℕ) : ℝ) / D.ν + ((m1 + m2 + s : ℕ) : ℝ) / (2 * D.ν) =
      D.μ.mass)
    (hη0 : 0 ≤ D.η) (hε : 0 < 1 - 2 * D.η) (hpS : Summable (fun j => |D.p j|))
    (Rm Rn : ℝ → ℝ) (α : ℝ) (hα : ((m1 + m2 + s : ℕ) : ℝ) / D.ν ≤ α)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ p, zp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hzinj : Function.Injective zp)
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (LR spike : ℝ) (x : ℕ) (hx0 : 0 < x) (hsr : D.sp ≤ x)
    (hxg : (x : ℝ) + D.g = (q : ℝ) + m2 + s)
    (hA7 : LR / D.ν ^ 2 ≤ logPref (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) / D.ν ^ 2 +
      (D.withCount x).numB (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) -
      (D.withCount x).denB (Fin.append gp (Fin.append yp zp)) + spike) :
    D.constant + pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / D.ν ^ 2 +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / D.ν ^ 2 +
        (∑ i, ∑ j, Real.log (1 - Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) /
          D.ν ^ 2 +
        ((∑ b, D.Rf (xn b)) + ∑ p, D.Rf (gp p)) / D.ν +
        ((∑ j, Rm (yn j)) + ∑ j, Rm (yp j)) / D.ν + (∑ j, Rn (zp j)) / D.ν +
        (∑ j, D.Cf (sc j)) / D.ν + LR / D.ν ^ 2 ≤
      D.constFix (k + q) (m1 + m2 + s) + spike +
        (1 / D.ν) * ((∑ b, D.fNeg (xn b)) + ∑ j, D.fNegM Rm (yn j)) +
        (1 / D.ν) * ((∑ p, D.fPos (gp p)) + ∑ j, (D.fPosM Rm (yp j) +
          remC (1 - 2 * D.η) * α * (-Real.log (1 - yp j ^ 2)))) +
        (1 / D.ν) * ∑ j, D.fNearM Rn α ((s : ℝ) / D.ν) (zp j) +
        (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  -- the Heine count `x` (NOTES-ETA §5.1)
  have hA7c := D.numB_sub_denB_withCount_le hν hx0 hsr (Fin.append xn yn)
    (Fin.append gp (Fin.append yp zp))
  rw [hxg] at hA7c
  replace hA7 : LR / D.ν ^ 2 ≤ logPref (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) /
      D.ν ^ 2 + D.numB (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) -
      D.denB (Fin.append gp (Fin.append yp zp)) +
      (spike + (D.numDenRef - (D.numConst - D.denConst) +
        2 * (((q : ℝ) + m2 + s) / D.ν) * D.Sup)) := by
    linarith
  have hτb := realEnergyTau_bounds he
  have hτ : D.τ ∈ Ioo (0 : ℝ) 1 := hτb
  have hτ1 : D.τ ∈ Ioc (0 : ℝ) 1 := ⟨hτb.1, hτb.2.le⟩
  have hτ0 := hτ.1
  have h1η : 0 < 1 - D.η := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hm10 : (0 : ℝ) ≤ m1 := Nat.cast_nonneg m1
  have hm20 : (0 : ℝ) ≤ m2 := Nat.cast_nonneg m2
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hallR : (k : ℝ) + m1 + (q + m2) + s ≤ D.ν := by push_cast at hall; linarith
  have hp : ((k + q : ℕ) : ℝ) ≤ D.ν := by push_cast; linarith
  have hν2 : 0 < D.ν ^ 2 := by positivity
  have hL2 := log_two_sub_nonneg hτ
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- positions
  have hXN : ∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hxn i
    · simp only [Fin.append_right]; exact hyn i
  have hGP : ∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hgp i
    · simp only [Fin.append_right]; exact hyp i
  have hGPall : ∀ p, Fin.append gp (Fin.append yp zp) p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hgp i
    · simp only [Fin.append_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]; exact hyp j
      · simp only [Fin.append_right]; exact hzp j
  have hxF : ∀ i, Fin.append xn gp i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact ⟨(hxn b).1, by linarith [(hxn b).2]⟩
    · simp only [Fin.append_right]; exact ⟨by linarith [(hgp p).1], (hgp p).2⟩
  have hZ : ∀ i, Fin.append (Fin.append xn yn) (Fin.append gp yp) i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact ⟨(hXN b).1, by linarith [(hXN b).2]⟩
    · simp only [Fin.append_right]; exact ⟨by linarith [(hGP p).1], (hGP p).2⟩
  have hab1 : ∀ {m : ℕ} (y : Fin m → ℝ), (∀ b, y b ∈ Ioo (-1 : ℝ) 0) → ∀ b, |y b| ≤ 1 :=
    fun y hy b => (abs_lt.mpr ⟨(hy b).1, by linarith [(hy b).2]⟩).le
  have hab2 : ∀ {m : ℕ} (y : Fin m → ℝ), (∀ b, y b ∈ Ioo (0 : ℝ) 1) → ∀ b, |y b| ≤ 1 :=
    fun y hy b => (abs_lt.mpr ⟨by linarith [(hy b).1], (hy b).2⟩).le
  -- 1. the pin
  have h1 := pin_zero_canonical hν he hp hxF hs hinjF hsi D.v hv
  have e_v := row_sum_split (fun x => -barrierTrialS D.v x) xn gp
  have e_l := row_sum_split (fun x => Real.log (1 - x)) xn gp
  beta_reduce at e_v e_l
  rw [e_v, e_l] at h1
  have hsplitF : pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc =
      pinOffDiagonalInteraction D.ν 0 (Fin.append xn gp) sc + vd (Fin.append xn gp) / D.ν ^ 2 := by
    unfold pinOffDiagonalInteraction vd; ring
  -- 2. the Vandermonde blocks
  have eF := vd_append xn gp
  have eA := vand4 xn yn gp yp
  have hVall : (∑ i, ∑ j ∈ Finset.Ioi i,
      Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
        Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) =
      vd (Fin.append (Fin.append xn yn) (Fin.append gp yp)) := rfl
  have eW := wvand4 (1 / D.ν) ((1 / 2) / D.ν) (1 / D.ν) ((1 / 2) / D.ν) xn yn gp yp
  have eH := wvand4 0 (1 / D.ν) 0 (1 / D.ν) xn yn gp yp
  -- 3. the `(1 - η)`-share: weighted D7.1 with the arcsine phantom
  have hwpos : ∀ i, 0 < Fin.append (wts (a := k) (b := m1) (1 / D.ν) ((1 / 2) / D.ν))
      (wts (a := q) (b := m2) (1 / D.ν) ((1 / 2) / D.ν)) i := wts_pos (by positivity) (by positivity)
  have hWs := sum_W4 (1 / D.ν) ((1 / 2) / D.ν) id (fun _ => 1) xn yn gp yp
  have hW2 := sum_W4 (1 / D.ν) ((1 / 2) / D.ν) (fun w => w ^ 2)
    (fun x => -Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) xn yn gp yp
  have hWr := sum_W4 (1 / D.ν) ((1 / 2) / D.ν) id (rowRef D.μ) xn yn gp yp
  have hWT := sum_W4 (1 / D.ν) ((1 / 2) / D.ν) id (barrierTrialT D.p) xn yn gp yp
  have hWq := sum_W4 (1 / D.ν) ((1 / 2) / D.ν) (fun w => w ^ 2) (fun _ => 1) xn yn gp yp
  beta_reduce at hW2 hWq
  simp only [id] at hWr hWT
  simp only [id, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hWs hWq
  have hWs' : ∑ i, Fin.append (wts (a := k) (b := m1) (1 / D.ν) ((1 / 2) / D.ν))
      (wts (a := q) (b := m2) (1 / D.ν) ((1 / 2) / D.ν)) i =
      (1 / D.ν) * ((k : ℝ) + q) + (1 / 2) / D.ν * ((m1 : ℝ) + m2) := by
    linarith [hWs]
  have hmassW : (∑ i, Fin.append (wts (a := k) (b := m1) (1 / D.ν) ((1 / 2) / D.ν))
      (wts (a := q) (b := m2) (1 / D.ν) ((1 / 2) / D.ν)) i) + (s : ℝ) * ((1 / 2) / D.ν) =
      D.μ.mass := by
    rw [hWs', ← hmass]; push_cast; field_simp; ring
  have h2 := rows_vandermonde_phantom hτ (Fin.append xn yn) (Fin.append gp yp)
    (wts (1 / D.ν) ((1 / 2) / D.ν)) (wts (1 / D.ν) ((1 / 2) / D.ν))
    (wts_pos1 (by positivity) (by positivity)) (wts_pos1 (by positivity) (by positivity))
    (ω := (1 / 2) / D.ν) (by positivity) (φ := (s : ℝ) / D.ν / 2) (by ring)
    hXN hGP hinj D.μ hμ hC hmassW
  rw [wpow_wts, wpow_wts, hW2, hWr] at h2
  rw [hWs', eW] at h2
  beta_reduce at h2
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * (1 - D.η) by linarith)
  -- 4. the `η`-share: the Chebyshev tangent at `p`
  have hWle : (1 / D.ν) * ((k : ℝ) + q) + (1 / 2) / D.ν * ((m1 : ℝ) + m2) ≤ 1 := by
    have e : (1 / D.ν) * ((k : ℝ) + q) + (1 / 2) / D.ν * ((m1 : ℝ) + m2) =
        ((k : ℝ) + q + ((m1 : ℝ) + m2) / 2) / D.ν := by ring
    rw [e, div_le_one hν]; linarith
  have hW0 : 0 ≤ (1 / D.ν) * ((k : ℝ) + q) + (1 / 2) / D.ν * ((m1 : ℝ) + m2) := by positivity
  have hc := cos_tangent_w he _ hZ hinj _ (fun i => (hwpos i).le) (by rw [hWs']; exact hWle)
    D.p hpS
  rw [hWs', hWT, show realEnergyTau D.e = D.τ from rfl, eW] at hc
  have hSq : ∑ i, Fin.append (wts (a := k) (b := m1) (1 / D.ν) ((1 / 2) / D.ν))
      (wts (a := q) (b := m2) (1 / D.ν) ((1 / 2) / D.ν)) i ^ 2 =
      (1 / D.ν) ^ 2 * ((k : ℝ) + q) + ((1 / 2) / D.ν) ^ 2 * ((m1 : ℝ) + m2) := by
    linarith [hWq]
  rw [hSq] at hc
  have hSqle : (1 / D.ν) ^ 2 * ((k : ℝ) + q) + ((1 / 2) / D.ν) ^ 2 * ((m1 : ℝ) + m2) ≤
      1 / D.ν := by
    have e : (1 / D.ν) ^ 2 * ((k : ℝ) + q) + ((1 / 2) / D.ν) ^ 2 * ((m1 : ℝ) + m2) =
        (((k : ℝ) + q + ((m1 : ℝ) + m2) / 4) / D.ν) * (1 / D.ν) := by ring
    rw [e]
    have h1 : ((k : ℝ) + q + ((m1 : ℝ) + m2) / 4) / D.ν ≤ 1 := by rw [div_le_one hν]; linarith
    calc (((k : ℝ) + q + ((m1 : ℝ) + m2) / 4) / D.ν) * (1 / D.ν) ≤ 1 * (1 / D.ν) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 / D.ν := one_mul _
  have herrη := D.eta_err_le hν he hη0 hW0 hWle hSqle (tsum_nonneg fun _ => abs_nonneg _)
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * D.η by linarith)
  -- the `log 2` of the `η`-share at the full weighted mass
  have hshift := fun A d hA hd hAd => eta_shift D.η hη0 hlog2 A d hA hd hAd
  have hWsh := hshift ((1 / D.ν) * ((k : ℝ) + q) + (1 / 2) / D.ν * ((m1 : ℝ) + m2))
    ((s : ℝ) * ((1 / 2) / D.ν)) hW0 (by positivity) (by
      have e : (1 / D.ν) * ((k : ℝ) + q) + (1 / 2) / D.ν * ((m1 : ℝ) + m2) +
          (s : ℝ) * ((1 / 2) / D.ν) = ((k : ℝ) + q + ((m1 : ℝ) + m2 + s) / 2) / D.ν := by ring
      rw [e, div_le_one hν]; linarith)
  -- 5. the fixed-fixed half Vandermonde (Chebyshev bound, PROOF-A §17.40)
  have hHs := sum_W4 (k := k) (m1 := m1) (q := q) (m2 := m2) 0 (1 / D.ν) id (fun _ => 1)
    xn yn gp yp
  have hHq := sum_W4 (k := k) (m1 := m1) (q := q) (m2 := m2) 0 (1 / D.ν) (fun w => w ^ 2)
    (fun _ => 1) xn yn gp yp
  beta_reduce at hHq
  simp only [id, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hHs hHq
  have hHs' : ∑ i, Fin.append (wts (a := k) (b := m1) 0 (1 / D.ν))
      (wts (a := q) (b := m2) 0 (1 / D.ν)) i = (1 / D.ν) * ((m1 : ℝ) + m2) := by
    linarith [hHs]
  have hHq' : ∑ i, Fin.append (wts (a := k) (b := m1) 0 (1 / D.ν))
      (wts (a := q) (b := m2) 0 (1 / D.ν)) i ^ 2 = (1 / D.ν) ^ 2 * ((m1 : ℝ) + m2) := by
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this] at hHq; linarith [hHq]
  have hMle : (1 / D.ν) * ((m1 : ℝ) + m2) ≤ 1 := by
    have e : (1 / D.ν) * ((m1 : ℝ) + m2) = ((m1 : ℝ) + m2) / D.ν := by ring
    rw [e, div_le_one hν]; linarith
  have hH := cos_tangent_w he _ hZ hinj
    (Fin.append (wts (a := k) (b := m1) 0 (1 / D.ν)) (wts (a := q) (b := m2) 0 (1 / D.ν)))
    (wts_nonneg le_rfl (by positivity)) (by rw [hHs']; exact hMle) (fun _ => 0) (by simp)
  rw [hHs', hHq', barrierTrialNormSq_zero, show realEnergyTau D.e = D.τ from rfl, eH] at hH
  simp only [barrierTrialT_zero, mul_zero, Finset.sum_const_zero, abs_zero, tsum_zero,
    add_zero, sub_zero] at hH
  have hkey := fun a b c ha ha1 hb hab hc =>
    had_key D.e (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) α he.1.le hL2 hlog2 a b c ha ha1 hb hab hc
  have hHad := hkey (((m1 : ℝ) + m2) / D.ν) ((s : ℝ) / D.ν) (1 / D.ν) (by positivity)
    (by rw [div_le_one hν]; linarith) (by positivity)
    (by refine le_trans (le_of_eq ?_) hα; push_cast; ring) (by positivity)
  have hhad : D.hadErr = (Real.log 2 - 2 * Real.log (1 - D.τ ^ 2)) * (1 / D.ν) / 4 + D.e := by
    unfold SignedData.hadErr; ring
  -- 6. the decay part (prefactor and the route II ratio)
  have h3 := logPref_le_prefTau hτ1 hν (Fin.append xn yn) (Fin.append gp (Fin.append yp zp))
    hXN hGPall
  have hnorm1 : ∀ b, |D.τ * Fin.append xn yn b| < 1 := fun b => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |Fin.append xn yn b| < 1 := abs_lt.mpr ⟨(hXN b).1, by linarith [(hXN b).2]⟩
    nlinarith only [hτ.2, hτ0, this, abs_nonneg (Fin.append xn yn b)]
  have hnorm2 : ∀ p, |D.τ * Fin.append gp (Fin.append yp zp) p| < 1 := fun p => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |Fin.append gp (Fin.append yp zp) p| < 1 :=
      abs_lt.mpr ⟨by linarith [(hGPall p).1], (hGPall p).2⟩
    nlinarith only [hτ.2, hτ0, this, abs_nonneg (Fin.append gp (Fin.append yp zp) p)]
  have h4 := prefTau_eq hν (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) hnorm1 hnorm2
  -- the sequences
  have hBf := isGeom_powSum hτ0 hν xn (hab1 _ hxn)
  have hBm := isGeom_powSum hτ0 hν yn (hab1 _ hyn)
  have hPf := isGeom_powSum hτ0 hν gp (hab2 _ hgp)
  have hPm := isGeom_powSum hτ0 hν yp (hab2 _ hyp)
  have hQ := isGeom_powSum hτ0 hν zp (hab2 _ hzp)
  have hmp : IsGeom D.τ (mpos D.μ D.τ) := isGeom_mpos hμ hτ0
  have hmn : IsGeom D.τ (mneg D.μ D.τ) := isGeom_mneg hμ hτ0
  have hφp : IsGeom D.τ (fun n => (s : ℝ) / D.ν / 2 * arcPos D.τ n) :=
    (isGeom_arcPos hτ).const_mul _
  have hφn : IsGeom D.τ (fun n => (s : ℝ) / D.ν / 2 * arcNeg D.τ n) :=
    (isGeom_arcNeg hτ).const_mul _
  have hPφ : ∀ n, 0 ≤ powSum D.τ D.ν yp n * ((s : ℝ) / D.ν / 2 * arcPos D.τ n) := fun n =>
    mul_nonneg (powSum_nonneg hτ0 hν yp hyp n)
      (mul_nonneg (by positivity) (arcPos_nonneg hτ0 n))
  have h5 := quad_master_eta hτ hBf hBm hPf hPm hQ hR hmp hmn ht hφp hφn hPφ hε
  beta_reduce at h5
  have hBs : powSum D.τ D.ν (Fin.append xn yn) =
      fun n => powSum D.τ D.ν xn n + powSum D.τ D.ν yn n := funext fun n => powSum_append _ _ xn yn n
  have hPs : powSum D.τ D.ν (Fin.append gp yp) =
      fun n => powSum D.τ D.ν gp n + powSum D.τ D.ν yp n := funext fun n => powSum_append _ _ gp yp n
  have hPQ : powSum D.τ D.ν (Fin.append gp (Fin.append yp zp)) =
      fun n => powSum D.τ D.ν gp n + powSum D.τ D.ν yp n + powSum D.τ D.ν zp n :=
    funext fun n => by rw [powSum_append, powSum_append]; ring
  -- 7. the cross and near facts
  have hcpp := cross_pp_le hτ hν (Fin.append gp yp) zp hGP hzp
  have hcnf := cross_np_le hτ hν xn zp hxn hzp
  have hcnm := cross_np_le hτ hν yn zp hyn hzp
  have hcnm2 := cross_neg_le_log yn zp hyn hzp
  have hnn := near_near_le hτ hν zp hzp hzinj
  have hQQ := lemmaR'_linearisation hτ hν zp hzp
  have hPP := lemmaR'_linearisation hτ hν yp hyp
  rw [hPs] at hcpp
  have hcross : (∑ i, ∑ j, Real.log (1 -
        Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) =
      ((∑ b, ∑ j, Real.log (1 - xn b * zp j)) + ∑ b, ∑ j, Real.log (1 - yn b * zp j)) +
        ∑ p, ∑ j, Real.log (1 - Fin.append gp yp p * zp j) := by
    rw [row_sum_split (fun u => ∑ j, Real.log (1 - u * zp j)) (Fin.append xn yn)
      (Fin.append gp yp), row_sum_split (fun u => ∑ j, Real.log (1 - u * zp j)) xn yn]
  have hL0 : 0 ≤ Real.log (1 / D.τ ^ 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ (pow_pos hτ0 2)]; nlinarith only [hτ.1, hτ.2])
  have herr : ((k : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2) +
      (1 / 2) * (((m1 : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2)) ≤
      (1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2)) := by
    have hkm' : (k : ℝ) + m1 ≤ D.ν := by linarith
    have e : ((k : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2) +
        (1 / 2) * (((m1 : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2)) =
        (((k : ℝ) + m1 / 2) / D.ν) * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2))) := by
      field_simp
    rw [e]
    have hfr : ((k : ℝ) + m1 / 2) / D.ν ≤ 1 := by
      rw [div_le_one hν]; linarith
    calc (((k : ℝ) + m1 / 2) / D.ν) * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2)))
        ≤ 1 * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2))) :=
          mul_le_mul_of_nonneg_right hfr (by positivity)
      _ = _ := one_mul _
  have hlog1 : 0 ≤ ∑ j, Real.log (1 + zp j) :=
    Finset.sum_nonneg fun j _ => Real.log_nonneg (by linarith [(hzp j).1])
  have hm1α : (m1 : ℝ) / D.ν ≤ α := by
    refine le_trans ?_ hα
    exact div_le_div_of_nonneg_right (by push_cast; linarith) hν.le
  have hαt : (1 / 2) * (((m1 : ℝ) * ∑ j, Real.log (1 + zp j)) / D.ν ^ 2) ≤
      (1 / D.ν) * ((α / 2) * ∑ j, Real.log (1 + zp j)) := by
    have e : (1 / 2) * (((m1 : ℝ) * ∑ j, Real.log (1 + zp j)) / D.ν ^ 2) =
        (1 / D.ν) * ((((m1 : ℝ) / D.ν) / 2) * ∑ j, Real.log (1 + zp j)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hlog1)
      (by positivity)
  have hcnm2' : (∑ b, ∑ j, Real.log (1 - yn b * zp j)) / D.ν ^ 2 ≤
      ((m1 : ℝ) * ∑ j, Real.log (1 + zp j)) / D.ν ^ 2 :=
    div_le_div_of_nonneg_right hcnm2 (sq_nonneg _)
  -- the Lemma R′ remainders
  have hlogy : 0 ≤ ∑ j, -Real.log (1 - yp j ^ 2) := Finset.sum_nonneg fun j _ => by
    have h0 : 0 < 1 - yp j ^ 2 := by nlinarith only [(hyp j).1, (hyp j).2]
    have := Real.log_nonpos h0.le (by nlinarith only [sq_nonneg (yp j)])
    linarith
  have hm2α : (m2 : ℝ) / D.ν ≤ α := by
    refine le_trans ?_ hα
    exact div_le_div_of_nonneg_right (by push_cast; linarith) hν.le
  have hrc0 : 0 ≤ remC (1 - 2 * D.η) := by unfold remC; positivity
  have hrem : remC (1 - 2 * D.η) * ip (powSum D.τ D.ν yp) (powSum D.τ D.ν yp) ≤
      (1 / D.ν) * (remC (1 - 2 * D.η) * α * ∑ j, -Real.log (1 - yp j ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hPP hrc0
    refine h.trans ?_
    have e : ((m2 : ℝ) / D.ν ^ 2) * ∑ j, -Real.log (1 - yp j ^ 2) =
        (1 / D.ν) * (((m2 : ℝ) / D.ν) * ∑ j, -Real.log (1 - yp j ^ 2)) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_right hm2α hlogy
    have h2 := mul_le_mul_of_nonneg_left this (show 0 ≤ 1 / D.ν by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hrc0
    calc remC (1 - 2 * D.η) * ((1 / D.ν) * (((m2 : ℝ) / D.ν) * ∑ j, -Real.log (1 - yp j ^ 2)))
        ≤ remC (1 - 2 * D.η) * ((1 / D.ν) * (α * ∑ j, -Real.log (1 - yp j ^ 2))) := h3
      _ = _ := by ring
  have hqrem : (1 / (4 * (1 - D.η))) * ip (powSum D.τ D.ν zp) (powSum D.τ D.ν zp) ≤
      (1 / D.ν) * (((s : ℝ) / D.ν / (4 * (1 - D.η))) * ∑ j, -Real.log (1 - zp j ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hQQ (show 0 ≤ 1 / (4 * (1 - D.η)) by positivity)
    refine h.trans (le_of_eq ?_)
    field_simp
  -- the arcsine constants
  have hφφ : ip (fun n => (s : ℝ) / D.ν / 2 * arcPos D.τ n)
      (fun n => (s : ℝ) / D.ν / 2 * arcPos D.τ n) =
      ((s : ℝ) / D.ν / 2) ^ 2 * ip (arcPos D.τ) (arcPos D.τ) := by
    rw [ip_const_mul_left, ip_const_mul_right]; ring
  have hφn' : ip (fun n => mneg D.μ D.τ n - D.t n) (fun n => (s : ℝ) / D.ν / 2 * arcNeg D.τ n) =
      ((s : ℝ) / D.ν / 2) * ip (fun n => mneg D.μ D.τ n - D.t n) (arcNeg D.τ) :=
    ip_const_mul_right _ _ _
  have hphC : D.phConst = (1 - D.η) * ip (fun n => mneg D.μ D.τ n - D.t n) (arcNeg D.τ) := rfl
  -- 8. from inner products to fields
  have hl1 := ip_powSum_left hτ hν (Fin.append gp yp) (hab2 _ hGP) (hmp.add hR)
  rw [hPs] at hl1
  have e5 := row_sum_split (fun x => fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x) gp yp
  beta_reduce at e5
  rw [e5] at hl1
  have hl2 := ip_powSum_left hτ hν xn (hab1 _ hxn)
    (((hmn.sub ht).const_mul (2 * (1 - D.η))).sub hR)
  have hl3 := ip_powSum_left hτ hν yn (hab1 _ hyn) (((hmn.sub ht).const_mul (1 - D.η)).sub hR)
  have hl4 := ip_powSum_left hτ hν zp (hab2 _ hzp) ((hR.sub ht).add hφn)
  -- 9. the field sums
  have hsN := congrArg (fun z => (1 / D.ν) * z) (sum_fNeg_eq D xn)
  have hsNF := congrArg (fun z => (1 / D.ν) * z) (sum_fNegM_eq D Rm yn)
  have hsP := congrArg (fun z => (1 / D.ν) * z) (sum_fPos_eq D gp)
  have hsPF := congrArg (fun z => (1 / D.ν) * z) (sum_fPosM_eq D Rm yp)
  have hsZ := congrArg (fun z => (1 / D.ν) * z) (sum_fNearM_eq D Rn α ((s : ℝ) / D.ν) zp)
  have hbN := congrArg (fun z => (1 / D.ν) * z) (sum_rowBase_eq D xn)
  have hbP := congrArg (fun z => (1 / D.ν) * z) (sum_rowBase_eq D gp)
  have hbNF := congrArg (fun z => (1 / D.ν) * z) (sum_rowBaseM_eq D Rm yn)
  have hbPF := congrArg (fun z => (1 / D.ν) * z) (sum_rowBaseM_eq D Rm yp)
  beta_reduce at hsN hsNF hsP hsPF hsZ hbN hbP hbNF hbPF
  have hsC : ∑ j, D.fCol (sc j) = (∑ j, D.Cf (sc j)) + (∑ j, 2 * barrierTrialT D.v (sc j)) -
      (∑ j, Real.log (1 - sc j)) / D.ν := by
    unfold SignedData.fCol
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hsC' : (1 / D.ν) * ∑ j, D.fCol (sc j) = (1 / D.ν) * ((∑ j, D.Cf (sc j)) +
      (∑ j, 2 * barrierTrialT D.v (sc j)) - (∑ j, Real.log (1 - sc j)) / D.ν) := by rw [hsC]
  have hrS : ∑ j, (D.fPosM Rm (yp j) + remC (1 - 2 * D.η) * α * (-Real.log (1 - yp j ^ 2))) =
      (∑ j, D.fPosM Rm (yp j)) + ∑ j, remC (1 - 2 * D.η) * α * (-Real.log (1 - yp j ^ 2)) :=
    Finset.sum_add_distrib
  -- the decay forms
  have h4' : prefTau D.τ D.ν (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) =
      -(1 / 2) * ip (powSum D.τ D.ν (Fin.append xn yn)) (powSum D.τ D.ν (Fin.append xn yn)) +
        ip (powSum D.τ D.ν (Fin.append xn yn))
          (powSum D.τ D.ν (Fin.append gp (Fin.append yp zp))) -
        (1 / (2 * D.ν ^ 2)) *
          ∑ b, Real.log (1 - (D.τ * Fin.append xn yn b) * (D.τ * Fin.append xn yn b)) := h4
  unfold SignedData.numB SignedData.denB at hA7
  have e1 := row_sum_split (fun x => -barrierTrialS D.a (-D.τ * x)) xn yn
  have e2 := row_sum_split (fun x => barrierTrialS D.a (-D.τ * x)) gp (Fin.append yp zp)
  have e2' := row_sum_split (fun x => barrierTrialS D.a (-D.τ * x)) yp zp
  have e3 := row_sum_split (fun x => denPoly D.b D.K x) gp (Fin.append yp zp)
  have e3' := row_sum_split (fun x => denPoly D.b D.K x) yp zp
  have e4 := row_sum_split (fun x => Real.log (1 - (D.τ * x) * (D.τ * x))) xn yn
  beta_reduce at e1 e2 e2' e3 e3' e4
  rw [e1, e2, e3, e2', e3'] at hA7
  rw [e4] at h4'
  rw [hBs, hPQ] at hA7 h4'
  beta_reduce at hA7 h4'
  rw [hφφ, hφn'] at h5
  unfold SignedData.constFix SignedData.eD7 SignedData.Kq
  have hrS2 : ∑ j, remC (1 - 2 * D.η) * α * (-Real.log (1 - yp j ^ 2)) =
      remC (1 - 2 * D.η) * α * ∑ j, -Real.log (1 - yp j ^ 2) := by rw [Finset.mul_sum]
  rw [hcross, hVall, hsplitF, hrS, hrS2, eA, eF]
  generalize hZs : ∑ j, D.fNearM Rn α ((s : ℝ) / D.ν) (zp j) = Zs at hsZ ⊢
  rw [hphC] at hsZ
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h1 h2' hc' hA7 hsN hsNF hsP hsPF hsZ hbN hbP hbNF hbPF hQQ hnn hsC' hqrem
  push_cast at h1 h2' hc' hA7 hsN hsNF hsP hsPF hsZ hbN hbP hbNF hbPF hQQ hnn hsC' hcnf hcnm
  push_cast at herr hαt hcnm2' hHad hWsh hH eF eA eW hqrem hrem hhad ⊢
  ring_nf at hA7 h1 h2' hc' herrη h3 h4' h5 hl1 hl2 hl3 hl4
  ring_nf at hsN hsNF hsP hsPF hsZ hbN hbP hbNF hbPF hsC' hnn hcpp hcnf hcnm hcnm2'
  ring_nf at herr hαt hHad hWsh hH eF eA eW hqrem hrem hphC hhad ⊢
  linarith only [hA7, h1, h2', hc', herrη, h3, h4', h5, hl1, hl2, hl3, hl4, hsN, hsNF, hsP, hsPF,
    hsZ, hbN, hbP, hbNF, hbPF, hsC', hnn, hcpp, hcnf, hcnm, hcnm2', herr, hαt, hHad, hWsh, hH,
    eF, eA, eW, hqrem, hrem, hphC, hhad]

theorem fPosMS_le_fPosMR (D : SignedData) (Rm : ℝ → ℝ) {rc α x : ℝ} (hrc : 0 ≤ rc) (hα : 0 ≤ α)
    (hx : x ∈ Ioo (0 : ℝ) 1) : D.fPosMS Rm x ≤ D.fPosMR Rm rc α x := by
  unfold SignedData.fPosMR
  have h1 : Real.log (1 - x ^ 2) ≤ 0 := by
    apply Real.log_nonpos
    · nlinarith [hx.1, hx.2]
    · nlinarith [hx.1, hx.2]
  have : 0 ≤ rc * α * (-Real.log (1 - x ^ 2)) :=
    mul_nonneg (mul_nonneg hrc hα) (by linarith)
  linarith

/-! ### The deterministic theorem with near nodes -/

/-- **The deterministic theorem with first-kind fixed and near-type nodes (fixed `N`).**  The A7
hypothesis is `SpikeCompareFixed` with the marked positives `yp ++ zp` (the near rows are
marked positives of the determinant, in the positive list of the route II ratio).  The positive
fixed rows carry the Lemma R′ remainder `remC (1 - 2η) α (-log (1 - x²))` of the `η` split. -/
theorem signed_second_energy_near_det (D : SignedData) {k q m1 m2 s : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8))
    (hall : ((((k + m1) + (q + m2)) + s : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : D.μ.OK D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : ((k + q : ℕ) : ℝ) / D.ν + ((m1 + m2 + s : ℕ) : ℝ) / (2 * D.ν) =
      D.μ.mass)
    (hη0 : 0 ≤ D.η) (hε : 0 < 1 - 2 * D.η) (hpS : Summable (fun j => |D.p j|))
    (Rm Rn : ℝ → ℝ) (α : ℝ) (hα : ((m1 + m2 + s : ℕ) : ℝ) / D.ν ≤ α)
    {Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin (m2 + s) → ℝ) → Prop}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin (m2 + s) → ℝ) → ℝ}
    {c' : ℝ} (hA7 : SpikeCompareFixedCount D c' Cls LR)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ p, zp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hzinj : Function.Injective zp)
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (hcls : Cls xn gp yn (Fin.append yp zp)) :
    D.constant + pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / D.ν ^ 2 +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / D.ν ^ 2 +
        (∑ i, ∑ j, Real.log (1 - Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) /
          D.ν ^ 2 +
        ((∑ b, D.Rf (xn b)) + ∑ p, D.Rf (gp p)) / D.ν +
        ((∑ j, Rm (yn j)) + ∑ j, Rm (yp j)) / D.ν + (∑ j, Rn (zp j)) / D.ν +
        (∑ j, D.Cf (sc j)) / D.ν + LR xn gp yn (Fin.append yp zp) / D.ν ^ 2 ≤
      D.constFix (k + q) (m1 + m2 + s) +
        (D.withCount (q + (m2 + s) - D.g)).errJ3 c' ((k + m1) + (q + m2) + s) +
        (1 / D.ν) * ((∑ b, D.fNeg (xn b)) + ∑ j, D.fNegM Rm (yn j)) +
        (1 / D.ν) * ((∑ p, D.fPosS (gp p)) +
          ∑ j, D.fPosMR Rm (remC (1 - 2 * D.η)) α (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearMS Rn α ((s : ℝ) / D.ν) (zp j) +
        (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  have hyp' : ∀ p, Fin.append yp zp p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hyp i
    · simp only [Fin.append_right]; exact hzp i
  obtain ⟨hcnt, hA7⟩ := hA7
  obtain ⟨hsr0, hsrg⟩ := hcnt xn gp yn (Fin.append yp zp) hcls
  have hA := hA7 xn gp yn (Fin.append yp zp) hxn hgp hyn hyp' hcls
  have hN : (k + m1) + (q + (m2 + s)) = (k + m1) + (q + m2) + s := by omega
  rw [hN] at hA
  have hst : (D.withCount (q + (m2 + s) - D.g)).spikeTerm (Fin.append gp (Fin.append yp zp)) =
      D.spikeTerm (Fin.append gp (Fin.append yp zp)) := rfl
  rw [hst, SignedData.withCount_ν] at hA
  have hx0 : 0 < q + (m2 + s) - D.g := by omega
  have hsr : D.sp ≤ q + (m2 + s) - D.g := by omega
  have hxg : ((q + (m2 + s) - D.g : ℕ) : ℝ) + D.g = (q : ℝ) + m2 + s := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h := signed_master_near D hν he hall hv hR ht hμ hC hmass hη0 hε hpS Rm Rn α hα xn gp
    yn yp zp sc hxn hgp hyn hyp hzp hinjF hinj hzinj hs hsi (LR xn gp yn (Fin.append yp zp))
    (D.spikeTerm (Fin.append gp (Fin.append yp zp)) +
      (D.withCount (q + (m2 + s) - D.g)).errJ3 c' ((k + m1) + (q + m2) + s))
    (q + (m2 + s) - D.g) hx0 hsr hxg
    (by linarith only [hA])
  have e := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) gp (Fin.append yp zp)
  have e' := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) yp zp
  beta_reduce at e e'
  have hsp : D.spikeTerm (Fin.append gp (Fin.append yp zp)) +
      ((1 / D.ν) * ((∑ p, D.fPos (gp p)) + ∑ j, (D.fPosM Rm (yp j) +
          remC (1 - 2 * D.η) * α * (-Real.log (1 - yp j ^ 2)))) +
        (1 / D.ν) * ∑ j, D.fNearM Rn α ((s : ℝ) / D.ν) (zp j)) =
      (1 / D.ν) * ((∑ p, D.fPosS (gp p)) + ∑ j, D.fPosMR Rm (remC (1 - 2 * D.η)) α (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearMS Rn α ((s : ℝ) / D.ν) (zp j) := by
    unfold SignedData.spikeTerm SignedData.fPosS SignedData.fPosMR SignedData.fPosMS
      SignedData.fNearMS
    rw [e, e']
    simp only [Finset.sum_add_distrib]
    ring
  linarith only [h, hsp]


/-! ### The contract (α-dependent caps) and the theorem -/

/-- **The contract with fixed first-kind and near-type nodes, indexed by α-intervals, with caps
that are FUNCTIONS of the fixed fraction `α = (m₁ + m₂ + s)/n`.**  On interval `i` the trial data
`D i N α` (a `SignedData`: the reference `μ = c_r` of mass `1 - α/2` (free rows weight `1`, fixed
rows weight `1/2`; the near half mass is compensated by the arcsine law, not by the reference),
the split parameter `η = (1 - ε_i)/2` with `ε_i = epsSplit i`, the trial sequences `v, a, p`, the
tilt data) may depend on `N` and `α` only; the caps `MXn MXp MY cInf` are functions of `α` and the
fixed-node sup `ZB` of the three fractions `(m₁/n, m₂/n, s/n)`.  The problem's own data are
`ν = n N`, the free-row field `Rf`, the column field `Cf`, the EXACT fixed-row fields `Rm`
(`groupedMarkedField`) and `Rn` (`groupedNearField`) and the constant `constant N α` (the exact
grouped constant at `α n` fixed rows).  The near field is `fNearMS (Rn N) α β` with `β = s/n`.
The per-fixed-row cost of the second sheet is the field `cost` of the budget: `budgetFix` has
right side `B + cost · α`; its `log 2` count of the fixed rows is `fixLog2 ε_i α`. -/
structure SignedNearBounds (I : ℕ) where
  ncount : ℕ → ℕ
  ncount_pos : ∀ N, 0 < N → 0 < ncount N
  B : ℝ
  cost : ℝ
  α1 : ℝ
  α1_nonneg : 0 ≤ α1
  lo : Fin I → ℝ
  hi : Fin I → ℝ
  cover : ∀ α : ℝ, 0 ≤ α → α ≤ α1 → ∃ i, lo i ≤ α ∧ α ≤ hi i
  D : Fin I → ℕ → ℝ → SignedData
  Rf : ℕ → ℝ → ℝ
  Cf : ℕ → ℝ → ℝ
  Rm : ℕ → ℝ → ℝ
  Rn : ℕ → ℝ → ℝ
  constant : ℕ → ℝ → ℝ
  same : ∀ i N α, (D i N α).ν = (ncount N : ℝ) ∧ (D i N α).Rf = Rf N ∧
    (D i N α).Cf = Cf N ∧ (D i N α).constant = constant N α
  MXn : Fin I → ℝ → ℝ
  MXp : Fin I → ℝ → ℝ
  MY : Fin I → ℝ → ℝ
  cInf : Fin I → ℝ → ℝ
  κlo : Fin I → ℝ
  κhi : Fin I → ℝ
  epsSplit : Fin I → ℝ
  epsSplit_pos : ∀ i, 0 < epsSplit i
  epsSplit_le : ∀ i, epsSplit i ≤ 1
  eta_eq : ∀ i N α, (D i N α).η = (1 - epsSplit i) / 2
  ZB : Fin I → ℝ → ℝ → ℝ → ℝ
  Clsf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  LRf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ
  FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop
  e_mem : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (D i N α).e ∈ Ioo (0 : ℝ) (1 / 8)
  v_summable : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    Summable (fun j => |(D i N α).v j|)
  p_summable : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    Summable (fun j => |(D i N α).p j|)
  R_geom : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    IsGeom (D i N α).τ (D i N α).R
  t_geom : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    IsGeom (D i N α).τ (D i N α).t
  reference : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (D i N α).μ.OK (D i N α).Cb ∧ 0 ≤ (D i N α).Cb ∧
      1 - α / 2 = (D i N α).μ.mass
  cp : Fin I → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ((D i N α).withCount (ncount N)).errJ3 (cp i N α) (ncount N) ≤ ε
  spikeFix : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α k q m1 m2,
    SpikeCompareFixedCount (D i N α) (cp i N α) (Clsf N k q m1 m2) (LRf N k q m1 m2)
  rowNeg : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, (D i N α).fNeg x ≤ MXn i α + ε
  rowPos : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (D i N α).fPosS x ≤ MXp i α + ε
  column : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ s ∈ Ioo (0 : ℝ) 1, (D i N α).fCol s ≤ MY i α + ε
  fixedSum : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) → (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
      FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (ncount N : ℝ) = α →
      (1 / (D i N α).ν) * ((∑ j, (D i N α).fNegM (Rm N) (yn j)) +
          (∑ j, (D i N α).fPosMR (Rm N) (remC (epsSplit i)) α (yp j)) +
          ∑ j, (D i N α).fNearMS (Rn N) α ((s : ℝ) / (ncount N : ℝ)) (zp j)) ≤
        ZB i ((m1 : ℝ) / (ncount N : ℝ)) ((m2 : ℝ) / (ncount N : ℝ))
          ((s : ℝ) / (ncount N : ℝ)) + ε
  const_le : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (D i N α).constTotal (ncount N) ≤ cInf i α + ε
  budgetFix : ∀ i (κ c d e : ℝ), κlo i ≤ κ → κ ≤ κhi i → 0 ≤ c → 0 ≤ d → 0 ≤ e →
    lo i ≤ c + d + e → c + d + e ≤ hi i → κ + (c + d + e) ≤ 1 →
    cInf i (c + d + e) + fixLog2 (epsSplit i) (c + d + e) * Real.log 2 +
      κ * MXn i (c + d + e) + (1 - κ - (c + d + e)) * MXp i (c + d + e) +
      (1 - (c + d + e)) * MY i (c + d + e) + ZB i c d e ≤ B + cost * (c + d + e)

set_option maxHeartbeats 3200000 in
/-- **Theorem `signed_second_energy_near_nodes`.**  For every `δ > 0` and all large `N`, every
configuration of `k` free negatives, `q` free positives (with `k + q` columns), `m₁` first-kind
fixed negatives, `m₂` first-kind fixed positives and `s` near-type positives (distinct),
`(k + m₁) + (q + (m₂ + s)) = n N`, `m₁ + m₂ + s ≤ α₁ n N`, with the free negative fraction in the
range of every interval containing `α = (m₁ + m₂ + s)/n`, admissible fixed nodes and in the class,
has `constant + E_disc + V_nonnear/ν² + V_near/ν² + Cauchy_cross/ν² + fields + LR/ν² ≤ B + cost·α + δ`.
Factor-free statement. -/
theorem signed_second_energy_near_nodes {I : ℕ} (T : SignedNearBounds I) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (k q m1 m2 s : ℕ),
      (k + m1) + (q + (m2 + s)) = T.ncount N →
      ((m1 + m2 + s : ℕ) : ℝ) ≤ T.α1 * (T.ncount N : ℝ) →
      (∀ i, T.lo i ≤ ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) →
        ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
        T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i) →
      ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
        (sc : Fin (k + q) → ℝ),
      (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
      (∀ b, yn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, yp p ∈ Ioo (0 : ℝ) 1) →
      (∀ p, zp p ∈ Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append xn gp) →
      Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)) →
      Function.Injective zp →
      (∀ j, sc j ∈ Ioo (0 : ℝ) 1) → Function.Injective sc →
      T.Clsf N k q m1 (m2 + s) xn gp yn (Fin.append yp zp) → T.FixAdm N m1 m2 s yn yp zp →
      T.constant N (((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ)) +
        pinOffDiagonalInteraction (T.ncount N : ℝ) 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / (T.ncount N : ℝ) ^ 2 +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / (T.ncount N : ℝ) ^ 2 +
        (∑ i, ∑ j, Real.log (1 - Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) /
          (T.ncount N : ℝ) ^ 2 +
        ((∑ b, T.Rf N (xn b)) + ∑ p, T.Rf N (gp p)) / (T.ncount N : ℝ) +
        ((∑ j, T.Rm N (yn j)) + ∑ j, T.Rm N (yp j)) / (T.ncount N : ℝ) +
        (∑ j, T.Rn N (zp j)) / (T.ncount N : ℝ) +
        (∑ j, T.Cf N (sc j)) / (T.ncount N : ℝ) +
        T.LRf N k q m1 (m2 + s) xn gp yn (Fin.append yp zp) / (T.ncount N : ℝ) ^ 2 ≤
      T.B + T.cost * (((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ)) + δ := by
  have hε : 0 < δ / 8 := by linarith
  have hall : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : Fin I,
      (∀ α ∈ Icc (T.lo i) (T.hi i), (T.D i N α).e ∈ Ioo (0 : ℝ) (1 / 8)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), Summable (fun j => |(T.D i N α).v j|)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), Summable (fun j => |(T.D i N α).p j|)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), IsGeom (T.D i N α).τ (T.D i N α).R) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), IsGeom (T.D i N α).τ (T.D i N α).t) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i),
        (T.D i N α).μ.OK (T.D i N α).Cb ∧ 0 ≤ (T.D i N α).Cb ∧
          1 - α / 2 = (T.D i N α).μ.mass) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
        (T.D i N α).fNeg x ≤ T.MXn i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
        (T.D i N α).fPosS x ≤ T.MXp i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ s ∈ Ioo (0 : ℝ) 1,
        (T.D i N α).fCol s ≤ T.MY i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i),
        ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
          (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) →
          (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
          T.FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) = α →
          (1 / (T.D i N α).ν) * ((∑ j, (T.D i N α).fNegM (T.Rm N) (yn j)) +
              (∑ j, (T.D i N α).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j)) +
              ∑ j, (T.D i N α).fNearMS (T.Rn N) α ((s : ℝ) / (T.ncount N : ℝ)) (zp j)) ≤
            T.ZB i ((m1 : ℝ) / (T.ncount N : ℝ)) ((m2 : ℝ) / (T.ncount N : ℝ))
              ((s : ℝ) / (T.ncount N : ℝ)) + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), (T.D i N α).constTotal (T.ncount N) ≤ T.cInf i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i),
        ((T.D i N α).withCount (T.ncount N)).errJ3 (T.cp i N α) (T.ncount N) ≤ δ / 8) ∧
      (∀ α k q m1 m2, SpikeCompareFixedCount (T.D i N α) (T.cp i N α) (T.Clsf N k q m1 m2)
        (T.LRf N k q m1 m2)) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [T.e_mem i, T.v_summable i, T.p_summable i, T.R_geom i, T.t_geom i,
      T.reference i, T.rowNeg i hε, T.rowPos i hε, T.column i hε, T.fixedSum i hε,
      T.const_le i hε, T.err_small i hε, T.spikeFix i]
      with N h1 h2 h2p h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    exact ⟨h1, h2, h2p, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  filter_upwards [hall, Filter.eventually_gt_atTop 0] with N hN hN0 k q m1 m2 s hkq hα hκ xn gp
    yn yp zp sc hxn hgp hyn hyp hzp hinjF hinj hzinj hs hsi hcls hadm
  have hνp : (0 : ℝ) < (T.ncount N : ℝ) := by exact_mod_cast T.ncount_pos N hN0
  have hkqR : (((k + m1) + (q + (m2 + s)) : ℕ) : ℝ) = (T.ncount N : ℝ) := by exact_mod_cast hkq
  set n : ℝ := (T.ncount N : ℝ) with hn
  set α : ℝ := ((m1 + m2 + s : ℕ) : ℝ) / n with hαdef
  set β : ℝ := (s : ℝ) / n with hβdef
  have hm10 : (0 : ℝ) ≤ m1 := Nat.cast_nonneg m1
  have hm20 : (0 : ℝ) ≤ m2 := Nat.cast_nonneg m2
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  have hα1 : α ≤ T.α1 := by rw [hαdef, div_le_iff₀ hνp]; exact hα
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  obtain ⟨i, hlo, hhi⟩ := T.cover α hα0 hα1
  obtain ⟨h1, h2, h2p, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hN i
  have hαI : α ∈ Icc (T.lo i) (T.hi i) := ⟨hlo, hhi⟩
  obtain ⟨hνD, hRfD, hCfD, hcD⟩ := T.same i N α
  rw [← hn] at hνD
  have he := h1 α hαI
  have hv := h2 α hαI
  have hpS := h2p α hαI
  have hR := h3 α hαI
  have ht := h4 α hαI
  obtain ⟨hμ, hC, hmu1⟩ := h5 α hαI
  have hν : 0 < (T.D i N α).ν := by rw [hνD]; exact hνp
  have hsum : (k : ℝ) + m1 + (q + (m2 + s)) = n := by
    have := hkqR; push_cast at this; linarith
  have hallN : ((((k + m1) + (q + m2)) + s : ℕ) : ℝ) ≤ (T.D i N α).ν := by
    rw [hνD]; push_cast; linarith
  have hfree : ((k + q : ℕ) : ℝ) / (T.D i N α).ν = 1 - α := by
    rw [hνD, hαdef]; push_cast
    field_simp; linarith
  have hmass' : ((k + q : ℕ) : ℝ) / (T.D i N α).ν +
      ((m1 + m2 + s : ℕ) : ℝ) / (2 * (T.D i N α).ν) = (T.D i N α).μ.mass := by
    rw [← hmu1, hfree, hνD, hαdef]
    field_simp
    ring
  have hαD : ((m1 + m2 + s : ℕ) : ℝ) / (T.D i N α).ν ≤ α := by rw [hνD]
  have hηD := T.eta_eq i N α
  have hεi := T.epsSplit_pos i
  have hεi1 := T.epsSplit_le i
  have hη0 : 0 ≤ (T.D i N α).η := by rw [hηD]; linarith
  have hε : 0 < 1 - 2 * (T.D i N α).η := by rw [hηD]; linarith
  have hrcD : remC (1 - 2 * (T.D i N α).η) = remC (T.epsSplit i) := by rw [hηD]; ring_nf
  have h := signed_second_energy_near_det (T.D i N α) hν he hallN hv hR ht hμ hC hmass'
    hη0 hε hpS (T.Rm N) (T.Rn N) α hαD (h12 α k q m1 (m2 + s)) xn gp yn yp zp sc
    hxn hgp hyn hyp hzp hinjF hinj hzinj hs hsi hcls
  rw [hrcD] at h
  set κ : ℝ := (k : ℝ) / n with hκdef
  set c : ℝ := (m1 : ℝ) / n with hc
  set d : ℝ := (m2 : ℝ) / n with hd
  have hcde : c + d + β = α := by
    rw [hc, hd, hβdef, hαdef]; push_cast; ring
  have hq : (q : ℝ) / n = 1 - κ - α := by
    rw [hκdef, ← hcde, hc, hd, hβdef]; field_simp; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hκα : κ + α ≤ 1 := by
    have : 0 ≤ (q : ℝ) / n := by positivity
    linarith
  obtain ⟨hκlo, hκhi⟩ := hκ i hlo hhi
  -- free negatives
  have g1 : (1 / (T.D i N α).ν) * (∑ b, (T.D i N α).fNeg (xn b)) ≤
      κ * (T.MXn i α + δ / 8) := by
    have hs1 : ∑ b, (T.D i N α).fNeg (xn b) ≤ (k : ℝ) * (T.MXn i α + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun b => (T.D i N α).fNeg (xn b))
        (T.MXn i α + δ / 8) (fun b _ => h6 α hαI _ (hxn b))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α).ν) * ((k : ℝ) * (T.MXn i α + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = κ * (T.MXn i α + δ / 8) := by rw [hνD, hκdef]; field_simp
  -- free positives
  have g2 : (1 / (T.D i N α).ν) * (∑ p, (T.D i N α).fPosS (gp p)) ≤
      (1 - κ - α) * (T.MXp i α + δ / 8) := by
    have hs1 : ∑ p, (T.D i N α).fPosS (gp p) ≤ (q : ℝ) * (T.MXp i α + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun p => (T.D i N α).fPosS (gp p))
        (T.MXp i α + δ / 8) (fun p _ => h7 α hαI _ (hgp p))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α).ν) * ((q : ℝ) * (T.MXp i α + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - κ - α) * (T.MXp i α + δ / 8) := by rw [hνD, ← hq]; field_simp
  -- columns
  have hcol : ((k + q : ℕ) : ℝ) / n = 1 - α := by rw [← hfree, hνD]
  have g3 : (1 / (T.D i N α).ν) * ∑ j, (T.D i N α).fCol (sc j) ≤
      (1 - α) * (T.MY i α + δ / 8) := by
    have hs1 : ∑ j, (T.D i N α).fCol (sc j) ≤
        ((k + q : ℕ) : ℝ) * (T.MY i α + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun j => (T.D i N α).fCol (sc j))
        (T.MY i α + δ / 8) (fun j _ => h8 α hαI _ (hs j))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α).ν) * (((k + q : ℕ) : ℝ) * (T.MY i α + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - α) * (T.MY i α + δ / 8) := by rw [hνD, ← hcol]; field_simp
  -- fixed nodes
  have hβD : (s : ℝ) / (T.D i N α).ν = β := by rw [hνD]
  have g4 : (1 / (T.D i N α).ν) * ((∑ j, (T.D i N α).fNegM (T.Rm N) (yn j)) +
      (∑ j, (T.D i N α).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j)) +
      ∑ j, (T.D i N α).fNearMS (T.Rn N) α β (zp j)) ≤ T.ZB i c d β + δ / 8 := by
    have := h9 α hαI m1 m2 s yn yp zp hyn hyp hzp hadm (by rw [← hαdef])
    rw [hc, hd, hβdef]; exact this
  have hb := T.budgetFix i κ c d β hκlo hκhi hc0 hd0 hβ0 (by rw [hcde]; exact hlo)
    (by rw [hcde]; exact hhi) (by rw [hcde]; exact hκα)
  rw [hcde] at hb
  -- the constant
  have hη1 : (T.D i N α).η ≤ 1 := by rw [hηD]; linarith
  have hN' : (k + q) + (m1 + m2 + s) = T.ncount N := by omega
  have hct := (T.D i N α).constFix_le hC he hη1 hN' (by rw [hνD]) hν
  have hαν : ((m1 + m2 + s : ℕ) : ℝ) / (T.D i N α).ν = α := by rw [hνD]
  rw [hαν, show 1 - 2 * (T.D i N α).η = T.epsSplit i by rw [hηD]; ring] at hct
  have hconst := h10 α hαI
  have herr := h11 α hαI
  have hej : ((T.D i N α).withCount (q + (m2 + s) - (T.D i N α).g)).errJ3 (T.cp i N α)
      ((k + m1) + (q + m2) + s) ≤
      ((T.D i N α).withCount (T.ncount N)).errJ3 (T.cp i N α) (T.ncount N) := by
    have e : (k + m1) + (q + m2) + s = T.ncount N := by omega
    rw [e]
    exact (T.D i N α).errJ3_withCount_mono (T.cp_pos i N α) he.1.le hν (by omega) _
  rw [hβD, hνD, hRfD, hCfD, hcD] at h
  simp only [mul_add] at g1 g2 g3 g4 hb h
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hm1 := mul_nonneg hκ0 hδ.le
  have hm2 := mul_nonneg (show 0 ≤ 1 - κ - α by linarith) hδ.le
  have hm3 := mul_nonneg (show 0 ≤ 1 - α by linarith) hδ.le
  have hm4 := mul_nonneg hα0 hδ.le
  rw [hνD] at g1 g2 g3 g4
  nlinarith only [h, hct, g1, g2, g3, g4, hb, hconst, hδ, hm1, hm2, hm3, hm4, herr, hej]

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.near_near_le
#print axioms CatalanMeasure.Signed.quad_master_eta
#print axioms CatalanMeasure.Signed.cross_pp_le
#print axioms CatalanMeasure.Signed.cross_np_le
#print axioms CatalanMeasure.Signed.cross_neg_le_log
#print axioms CatalanMeasure.Signed.wvand4
#print axioms CatalanMeasure.Signed.signed_master_near
#print axioms CatalanMeasure.Signed.signed_second_energy_near_det
#print axioms CatalanMeasure.Signed.signed_second_energy_near_nodes
