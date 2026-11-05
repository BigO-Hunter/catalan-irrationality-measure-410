module

public import Submission.CatalanMeasure.GenD.Signed.EnergyNear
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Theorem S: the σ bound with the top cap, and the `fixedSum` constructor

The fixed-node part of the signed second-sheet contract (`SignedNearBounds.fixedSum`) asks, for
every admissible configuration of first-kind negative nodes `yn`, first-kind positive nodes `yp` and
near-type nodes `zp` (of fractions `c, d, β` of the `n` rows), for the bound

`(1/ν) (Σ fNegM(yn) + Σ fPosMR(yp) + Σ fNearMS(zp)) ≤ ZB c d β + ε`.

The paper's route (PHASE2-SIMPLIFY §2.2, "Theorem S") needs no cell LP.  For a fixed-node measure
`ν` of mass `α` that is capped by `κ` only through `κ([x,1]) ≤ C₁ (1-x)` on `[x_c, 1]`, and
`λ` an upper bound of the node field off the top cell `[x_c, 1)`,

`∫ ψ dν ≤ α λ + C₁ ∫_0^{1-x_c} (g₀ + r log(1/u) - λ)^+ du`,

where `g₀ + r (-log (1 - x²))` majorises `ψ` on the top cell (`r` is the REMC coefficient).  The
integral has the closed form `capInt`:
`r u* (1 + log (1/u*)) - gap u*`, `u* = min (e^{-gap/r}) (1 - x_c)`, `gap = λ - g₀`.

Here the fixed nodes are finitely many points, so "`ν ≤ κ`" is a counting statement
(`FixAdmCap`): the number of nodes in `[x, 1)` is at most `C₁ n (1 - x)` for `x ∈ [x_c, 1)`.

* Section 1: the primitive `capPrim`, the closed form `capInt`, its basic bounds.
* Section 2: the counting lemma (`sum_le_of_count`: sort the nodes, compare with the primitive).
* Section 3: the family sum bound `sum_le_topCap` (one node family, one field).
* Section 4: the three-family bound for the fields `fNegM`, `fPosMR`, `fNearMS`
  (`fixed_sum_le_cap`) and the constructor `fixedSumAt_of_cap` for the contract field `fixedSum`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set

noncomputable section

/-! ### 1. The cap primitive and its closed form -/

/-- Primitive `∫_0^t (c + r (-log u)) du = t (c + r - r log t)` (and `capPrim c r 0 = 0`). -/
def capPrim (c r t : ℝ) : ℝ := t * (c + r - r * Real.log t)

theorem capPrim_zero (c r : ℝ) : capPrim c r 0 = 0 := by simp [capPrim]

/-- Concavity of the primitive: `G(t) - G(s) ≥ (t - s) G'(t)`. -/
theorem capPrim_sub_ge {c r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    (t - s) * (c + r * (-Real.log t)) ≤ capPrim c r t - capPrim c r s := by
  have hlog : s - t ≤ s * (Real.log s - Real.log t) := by
    rcases hs.eq_or_lt with rfl | hpos
    · simp only [zero_mul, zero_sub]; linarith
    · have hs0 : s ≠ 0 := hpos.ne'
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hpos ht)
      rw [inv_div, Real.log_div hpos.ne' ht.ne'] at h
      have h2 := mul_le_mul_of_nonneg_left h hpos.le
      have e : s * (1 - t / s) = s - t := by field_simp
      linarith
  have key : capPrim c r t - capPrim c r s - (t - s) * (c + r * (-Real.log t)) =
      r * ((t - s) + s * (Real.log s - Real.log t)) := by
    unfold capPrim; ring
  have : 0 ≤ r * ((t - s) + s * (Real.log s - Real.log t)) := mul_nonneg hr (by linarith)
  linarith

/-- The primitive is increasing up to `exp (c / r)`, where its derivative vanishes. -/
theorem capPrim_mono {c r s t : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ Real.exp (c / r)) : capPrim c r s ≤ capPrim c r t := by
  have ht0 : 0 ≤ t := hs.trans hst
  rcases ht0.eq_or_lt with rfl | htpos
  · have hs0 : s = 0 := le_antisymm hst hs
    subst hs0
    exact le_rfl
  · have h := capPrim_sub_ge (c := c) hr.le hs hst htpos
    have hlog : Real.log t ≤ c / r := (Real.log_le_iff_le_exp htpos).mpr ht
    have hlt : Real.log t * r ≤ c := (le_div_iff₀ hr).mp hlog
    have hnn : 0 ≤ c + r * (-Real.log t) := by nlinarith
    have := mul_nonneg (sub_nonneg.2 hst) hnn
    linarith

/-- **The closed form** of `∫_0^θ (c + r log (1/u))^+ du` (`c = g₀ - λ`, `r ≥ 0`): for `r > 0`,
`u* (c + r - r log u*)` with `u* = min (exp (c / r)) θ`, i.e. `r u* (1 + log (1/u*)) - gap u*`
with `gap = -c`; for `r = 0`, `θ (c)^+`. -/
def capInt (c r θ : ℝ) : ℝ :=
  if 0 < r then capPrim c r (min (Real.exp (c / r)) θ) else θ * max 0 c

theorem capInt_nonneg {c r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 < θ) : 0 ≤ capInt c r θ := by
  unfold capInt
  rcases hr.eq_or_lt with rfl | hpos
  · rw [if_neg (lt_irrefl (0 : ℝ))]
    exact mul_nonneg hθ.le (le_max_left _ _)
  · rw [if_pos hpos]
    have hus0 : 0 < min (Real.exp (c / r)) θ := lt_min (Real.exp_pos _) hθ
    have := capPrim_mono (c := c) hpos le_rfl hus0.le (min_le_left _ _)
    rw [capPrim_zero] at this
    exact this

/-- A rational-friendly majorant: `capInt c r θ ≤ r exp (c / r)` (`r > 0`). -/
theorem capInt_le_mul_exp {c r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) :
    capInt c r θ ≤ r * Real.exp (c / r) := by
  unfold capInt
  rw [if_pos hr]
  obtain ⟨u, hu⟩ : ∃ u, u = min (Real.exp (c / r)) θ := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; exact lt_min (Real.exp_pos _) hθ
  have hE : 0 < Real.exp (c / r) := Real.exp_pos _
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hE)
  rw [inv_div, Real.log_div hu0.ne' hE.ne', Real.log_exp] at h
  have h2 : r * (1 - Real.exp (c / r) / u) ≤ r * (Real.log u - c / r) :=
    mul_le_mul_of_nonneg_left h hr.le
  have hr_ne : r ≠ 0 := hr.ne'
  have hu_ne : u ≠ 0 := hu0.ne'
  have e1 : r * (c / r) = c := by field_simp
  have h4 : c + r - r * Real.log u ≤ r * (Real.exp (c / r) / u) := by nlinarith [h2, e1]
  unfold capPrim
  calc u * (c + r - r * Real.log u) ≤ u * (r * (Real.exp (c / r) / u)) :=
        mul_le_mul_of_nonneg_left h4 hu0.le
    _ = r * Real.exp (c / r) := by field_simp

/-! ### 2. The counting lemma -/

/-- **Sorted comparison.**  Let `u : Fin m → ℝ` be positions such that every position at which `φ`
is positive has at most `K u_j` positions `≤ u_j` (a counting form of `ν ≤ κ`, `κ([0,u]) ≤ K u`).
If `φ ≥ 0` is antitone on `(0, ∞)` and `G` satisfies the step inequality
`φ((k+1)/K) ≤ K (G((k+1)/K) - G(k/K))`, then `Σ φ(u_j) ≤ K (G(m/K) - G 0)`.  (The `k`-th
smallest position is at least `(k+1)/K`.) -/
theorem sum_le_of_count {m : ℕ} (u : Fin m → ℝ) (φ G : ℝ → ℝ) {K : ℝ} (hK : 0 < K)
    (hφ0 : ∀ t, 0 ≤ φ t) (hanti : ∀ s t, 0 < s → s ≤ t → φ t ≤ φ s)
    (hcount : ∀ j, 0 < φ (u j) →
      ((Finset.univ.filter (fun i => u i ≤ u j)).card : ℝ) ≤ K * u j)
    (hstep : ∀ k : ℕ, φ (((k : ℝ) + 1) / K) ≤
      K * (G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K))) :
    ∑ j, φ (u j) ≤ K * (G ((m : ℝ) / K) - G 0) := by
  have hmono : Monotone (u ∘ Tuple.sort u) := Tuple.monotone_sort u
  have h1 : ∑ j, φ (u j) = ∑ k, φ (u (Tuple.sort u k)) :=
    (Equiv.sum_comp (Tuple.sort u) (fun j => φ (u j))).symm
  have h2 : ∀ k : Fin m, φ (u (Tuple.sort u k)) ≤ φ ((((k : ℕ) : ℝ) + 1) / K) := by
    intro k
    by_cases hpos : 0 < φ (u (Tuple.sort u k))
    · have hc := hcount (Tuple.sort u k) hpos
      have hsub : (Finset.Iic k).image (Tuple.sort u) ⊆
          Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k)) := by
        intro i hi
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hmono (Finset.mem_Iic.mp hl)
      have hcard1 : ((Finset.Iic k).image (Tuple.sort u)).card = (k : ℕ) + 1 := by
        rw [Finset.card_image_of_injective _ (Tuple.sort u).injective, Fin.card_Iic]
      have hk1 : (k : ℕ) + 1 ≤
          (Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k))).card := by
        rw [← hcard1]; exact Finset.card_le_card hsub
      have hk2 : (((k : ℕ) : ℝ) + 1) ≤ K * u (Tuple.sort u k) := by
        have : (((k : ℕ) + 1 : ℕ) : ℝ) ≤
            ((Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k))).card : ℝ) := by
          exact_mod_cast hk1
        push_cast at this
        linarith
      have hk3 : ((((k : ℕ) : ℝ) + 1) / K) ≤ u (Tuple.sort u k) := by
        rw [div_le_iff₀ hK]; linarith [mul_comm K (u (Tuple.sort u k))]
      exact hanti _ _ (div_pos (by positivity) hK) hk3
    · exact (not_lt.mp hpos).trans (hφ0 _)
  have e1 : ∑ k : Fin m, (G ((((k : ℕ) : ℝ) + 1) / K) - G (((k : ℕ) : ℝ) / K)) =
      ∑ k ∈ Finset.range m, (G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K)) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K)) m
  have e2 : ∑ k ∈ Finset.range m, (G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K)) =
      G ((m : ℝ) / K) - G 0 := by
    have h := Finset.sum_range_sub (fun k : ℕ => G ((k : ℝ) / K)) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at h
    exact h
  calc ∑ j, φ (u j) = ∑ k, φ (u (Tuple.sort u k)) := h1
    _ ≤ ∑ k : Fin m, φ ((((k : ℕ) : ℝ) + 1) / K) := Finset.sum_le_sum (fun k _ => h2 k)
    _ ≤ ∑ k : Fin m, K * (G ((((k : ℕ) : ℝ) + 1) / K) - G (((k : ℕ) : ℝ) / K)) :=
        Finset.sum_le_sum (fun k _ => hstep k)
    _ = K * (G ((m : ℝ) / K) - G 0) := by
        rw [← Finset.mul_sum, e1, e2]

/-- **Sorted comparison with one extra node.**  As `sum_le_of_count`, but the count is
`#{i | u_i ≤ u_j} ≤ K u_j + 1` and all positions are `≥ umin > 0`; the smallest position is bounded
by `φ umin`.  `G` must be monotone on `[0, ∞)`.  Then `Σ φ(u_j) ≤ φ umin + K (G(m/K) - G 0)`. -/
theorem sum_le_of_count1 {m : ℕ} (u : Fin m → ℝ) (φ G : ℝ → ℝ) {K umin : ℝ} (hK : 0 < K)
    (humin : 0 < umin) (hum : ∀ j, umin ≤ u j)
    (hφ0 : ∀ t, 0 ≤ φ t) (hanti : ∀ s t, 0 < s → s ≤ t → φ t ≤ φ s)
    (hG : ∀ s t, 0 ≤ s → s ≤ t → G s ≤ G t)
    (hcount : ∀ j, 0 < φ (u j) →
      ((Finset.univ.filter (fun i => u i ≤ u j)).card : ℝ) ≤ K * u j + 1)
    (hstep : ∀ k : ℕ, φ (((k : ℝ) + 1) / K) ≤
      K * (G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K))) :
    ∑ j, φ (u j) ≤ φ umin + K * (G ((m : ℝ) / K) - G 0) := by
  cases m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_div, sub_self,
      mul_zero, add_zero]
    exact hφ0 _
  | succ m' =>
    have hmono : Monotone (u ∘ Tuple.sort u) := Tuple.monotone_sort u
    have h1 : ∑ j, φ (u j) = ∑ k, φ (u (Tuple.sort u k)) :=
      (Equiv.sum_comp (Tuple.sort u) (fun j => φ (u j))).symm
    have h2 : ∀ k : Fin m', φ (u (Tuple.sort u k.succ)) ≤ φ ((((k : ℕ) : ℝ) + 1) / K) := by
      intro k
      by_cases hpos : 0 < φ (u (Tuple.sort u k.succ))
      · have hc := hcount (Tuple.sort u k.succ) hpos
        have hsub : (Finset.Iic k.succ).image (Tuple.sort u) ⊆
            Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k.succ)) := by
          intro i hi
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmono (Finset.mem_Iic.mp hl)
        have hcard1 : ((Finset.Iic k.succ).image (Tuple.sort u)).card = (k : ℕ) + 2 := by
          rw [Finset.card_image_of_injective _ (Tuple.sort u).injective, Fin.card_Iic]
          simp
        have hk1 : (k : ℕ) + 2 ≤
            (Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k.succ))).card := by
          rw [← hcard1]; exact Finset.card_le_card hsub
        have hk2 : (((k : ℕ) : ℝ) + 2) ≤
            ((Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k.succ))).card : ℝ) := by
          have : (((k : ℕ) + 2 : ℕ) : ℝ) ≤
              ((Finset.univ.filter (fun i => u i ≤ u (Tuple.sort u k.succ))).card : ℝ) := by
            exact_mod_cast hk1
          push_cast at this
          linarith
        have hk3 : ((((k : ℕ) : ℝ) + 1) / K) ≤ u (Tuple.sort u k.succ) := by
          rw [div_le_iff₀ hK]; linarith [mul_comm K (u (Tuple.sort u k.succ))]
        exact hanti _ _ (div_pos (by positivity) hK) hk3
      · exact (not_lt.mp hpos).trans (hφ0 _)
    have e1 : ∑ k : Fin m', (G ((((k : ℕ) : ℝ) + 1) / K) - G (((k : ℕ) : ℝ) / K)) =
        ∑ k ∈ Finset.range m', (G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K)) :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K)) m'
    have e2 : ∑ k ∈ Finset.range m', (G (((k : ℝ) + 1) / K) - G ((k : ℝ) / K)) =
        G ((m' : ℝ) / K) - G 0 := by
      have h := Finset.sum_range_sub (fun k : ℕ => G ((k : ℝ) / K)) m'
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at h
      exact h
    have hfirst : φ (u (Tuple.sort u 0)) ≤ φ umin := hanti _ _ humin (hum _)
    have hrest : ∑ k : Fin m', φ (u (Tuple.sort u k.succ)) ≤ K * (G ((m' : ℝ) / K) - G 0) := by
      calc ∑ k : Fin m', φ (u (Tuple.sort u k.succ))
          ≤ ∑ k : Fin m', φ ((((k : ℕ) : ℝ) + 1) / K) := Finset.sum_le_sum (fun k _ => h2 k)
        _ ≤ ∑ k : Fin m', K * (G ((((k : ℕ) : ℝ) + 1) / K) - G (((k : ℕ) : ℝ) / K)) :=
            Finset.sum_le_sum (fun k _ => hstep k)
        _ = K * (G ((m' : ℝ) / K) - G 0) := by rw [← Finset.mul_sum, e1, e2]
    have hGm : G ((m' : ℝ) / K) ≤ G (((m' + 1 : ℕ) : ℝ) / K) :=
      hG _ _ (by positivity) (by push_cast; exact div_le_div_of_nonneg_right (by linarith) hK.le)
    rw [h1, Fin.sum_univ_succ]
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right hGm (G 0)) hK.le
    linarith

/-- The integrand of the cap: `(c + r (-log u))^+` on `(0, θ]`, zero beyond. -/
def topPhi (c r θ u : ℝ) : ℝ := if u ≤ θ then max 0 (c + r * (-Real.log u)) else 0

theorem topPhi_nonneg (c r θ u : ℝ) : 0 ≤ topPhi c r θ u := by
  unfold topPhi
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem topPhi_anti {c r θ : ℝ} (hr : 0 ≤ r) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    topPhi c r θ t ≤ topPhi c r θ s := by
  unfold topPhi
  by_cases ht : t ≤ θ
  · rw [if_pos ht, if_pos (hst.trans ht)]
    have h1 : Real.log s ≤ Real.log t := Real.log_le_log hs hst
    have h2 : r * (-Real.log t) ≤ r * (-Real.log s) :=
      mul_le_mul_of_nonneg_left (neg_le_neg h1) hr
    exact max_le_max le_rfl (by linarith)
  · rw [if_neg ht]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl

theorem topPhi_le_aux {c r θ u Bd Rbd : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hr : 0 ≤ r)
    (hc : c ≤ Bd) (hrR : r ≤ Rbd) : topPhi c r θ u ≤ max 0 Bd + Rbd * (-Real.log u) := by
  have hL : 0 ≤ -Real.log u := by
    have := Real.log_nonpos hu0.le hu1; linarith
  have hR0 : 0 ≤ Rbd := hr.trans hrR
  have hB := le_max_right 0 Bd
  have hB0 := le_max_left 0 Bd
  have hm := mul_le_mul_of_nonneg_right hrR hL
  have hp := mul_nonneg hR0 hL
  unfold topPhi
  split_ifs
  · exact max_le (by linarith) (by nlinarith)
  · linarith

/-- The cap sum for `r > 0`: the primitive truncated at `u* = min (exp (c / r)) θ`. -/
theorem sum_topPhi_le_pos {m : ℕ} (u : Fin m → ℝ) {c r θ K : ℝ} (hr : 0 < r) (hθ : 0 < θ)
    (hK : 0 < K) {umin : ℝ} (humin : 0 < umin) (hum : ∀ j, umin ≤ u j)
    (hcount : ∀ j, 0 < topPhi c r θ (u j) →
      ((Finset.univ.filter (fun i => u i ≤ u j)).card : ℝ) ≤ K * u j + 1) :
    ∑ j, topPhi c r θ (u j) ≤ topPhi c r θ umin + K * capPrim c r (min (Real.exp (c / r)) θ) := by
  obtain ⟨us, hus⟩ : ∃ us, us = min (Real.exp (c / r)) θ := ⟨_, rfl⟩
  rw [← hus]
  have hus0 : 0 < us := by rw [hus]; exact lt_min (Real.exp_pos _) hθ
  have hus1 : us ≤ Real.exp (c / r) := by rw [hus]; exact min_le_left _ _
  have hus2 : us ≤ θ := by rw [hus]; exact min_le_right _ _
  have hmonoP : ∀ s t, 0 ≤ s → s ≤ t → t ≤ us → capPrim c r s ≤ capPrim c r t :=
    fun s t hs hst ht => capPrim_mono hr hs hst (ht.trans hus1)
  have hstep : ∀ k : ℕ, topPhi c r θ (((k : ℝ) + 1) / K) ≤
      K * (capPrim c r (min (((k : ℝ) + 1) / K) us) - capPrim c r (min ((k : ℝ) / K) us)) := by
    intro k
    have hb0 : 0 < ((k : ℝ) + 1) / K := by positivity
    have ha0 : 0 ≤ (k : ℝ) / K := by positivity
    have hba : ((k : ℝ) + 1) / K - (k : ℝ) / K = 1 / K := by ring
    have hKba : K * (((k : ℝ) + 1) / K - (k : ℝ) / K) = 1 := by
      rw [hba]; exact mul_one_div_cancel hK.ne'
    have hab : (k : ℝ) / K ≤ ((k : ℝ) + 1) / K := by
      have : 0 < 1 / K := by positivity
      linarith
    by_cases hbu : ((k : ℝ) + 1) / K ≤ us
    · rw [min_eq_left hbu, min_eq_left (hab.trans hbu)]
      have hbθ : ((k : ℝ) + 1) / K ≤ θ := hbu.trans hus2
      have hlog : Real.log (((k : ℝ) + 1) / K) ≤ c / r :=
        (Real.log_le_iff_le_exp hb0).mpr (hbu.trans hus1)
      have hnn : 0 ≤ c + r * (-Real.log (((k : ℝ) + 1) / K)) := by
        have : Real.log (((k : ℝ) + 1) / K) * r ≤ c := (le_div_iff₀ hr).mp hlog
        nlinarith
      have hphi : topPhi c r θ (((k : ℝ) + 1) / K) =
          c + r * (-Real.log (((k : ℝ) + 1) / K)) := by
        unfold topPhi; rw [if_pos hbθ]; exact max_eq_right hnn
      rw [hphi]
      have h1 := capPrim_sub_ge (c := c) hr.le ha0 hab hb0
      calc c + r * (-Real.log (((k : ℝ) + 1) / K))
          = K * (((k : ℝ) + 1) / K - (k : ℝ) / K) *
              (c + r * (-Real.log (((k : ℝ) + 1) / K))) := by rw [hKba, one_mul]
        _ = K * ((((k : ℝ) + 1) / K - (k : ℝ) / K) *
              (c + r * (-Real.log (((k : ℝ) + 1) / K)))) := by ring
        _ ≤ K * (capPrim c r (((k : ℝ) + 1) / K) - capPrim c r ((k : ℝ) / K)) :=
            mul_le_mul_of_nonneg_left h1 hK.le
    · have hbus : us < ((k : ℝ) + 1) / K := not_le.mp hbu
      have hphi : topPhi c r θ (((k : ℝ) + 1) / K) = 0 := by
        unfold topPhi
        by_cases hbθ : ((k : ℝ) + 1) / K ≤ θ
        · rw [if_pos hbθ]
          have hbus' : min (Real.exp (c / r)) θ < ((k : ℝ) + 1) / K := by rw [← hus]; exact hbus
          have h1 : Real.exp (c / r) < ((k : ℝ) + 1) / K := by
            rcases min_lt_iff.mp hbus' with h | h
            · exact h
            · exact absurd hbθ (not_le.mpr h)
          have h2 : c / r < Real.log (((k : ℝ) + 1) / K) :=
            (Real.lt_log_iff_exp_lt hb0).mpr h1
          have h3 : c < Real.log (((k : ℝ) + 1) / K) * r := (div_lt_iff₀ hr).mp h2
          exact max_eq_left (by nlinarith)
        · rw [if_neg hbθ]
      rw [hphi, min_eq_right hbus.le]
      have : capPrim c r (min ((k : ℝ) / K) us) ≤ capPrim c r us :=
        hmonoP _ _ (le_min ha0 hus0.le) (min_le_right _ _) le_rfl
      exact mul_nonneg hK.le (by linarith)
  have h := sum_le_of_count1 u (topPhi c r θ) (fun t => capPrim c r (min t us)) hK humin hum
    (topPhi_nonneg c r θ) (fun s t hs hst => topPhi_anti hr.le hs hst)
    (fun s t hs hst => hmonoP _ _ (le_min hs hus0.le) (min_le_min_right us hst) (min_le_right _ _))
    hcount hstep
  have hG0 : capPrim c r (min (0 : ℝ) us) = 0 := by
    rw [min_eq_left hus0.le]; exact capPrim_zero c r
  have hGm : capPrim c r (min ((m : ℝ) / K) us) ≤ capPrim c r us :=
    hmonoP _ _ (le_min (by positivity) hus0.le) (min_le_right _ _) le_rfl
  calc ∑ j, topPhi c r θ (u j)
      ≤ topPhi c r θ umin +
          K * (capPrim c r (min ((m : ℝ) / K) us) - capPrim c r (min 0 us)) := h
    _ ≤ topPhi c r θ umin + K * capPrim c r us := by
        rw [hG0]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) hK.le)

/-- The cap sum for `r = 0`: the constant `(c)^+` on `(0, θ]`. -/
theorem sum_topPhi_le_zero {m : ℕ} (u : Fin m → ℝ) {c θ K : ℝ} (hθ : 0 < θ) (hK : 0 < K)
    {umin : ℝ} (humin : 0 < umin) (hum : ∀ j, umin ≤ u j)
    (hcount : ∀ j, 0 < topPhi c 0 θ (u j) →
      ((Finset.univ.filter (fun i => u i ≤ u j)).card : ℝ) ≤ K * u j + 1) :
    ∑ j, topPhi c 0 θ (u j) ≤ topPhi c 0 θ umin + K * (θ * max 0 c) := by
  have hcc0 : 0 ≤ max 0 c := le_max_left _ _
  have hstep : ∀ k : ℕ, topPhi c 0 θ (((k : ℝ) + 1) / K) ≤
      K * (max 0 c * min (((k : ℝ) + 1) / K) θ - max 0 c * min ((k : ℝ) / K) θ) := by
    intro k
    have hba : ((k : ℝ) + 1) / K - (k : ℝ) / K = 1 / K := by ring
    have hKba : K * (((k : ℝ) + 1) / K - (k : ℝ) / K) = 1 := by
      rw [hba]; exact mul_one_div_cancel hK.ne'
    have hab : (k : ℝ) / K ≤ ((k : ℝ) + 1) / K := by
      have : 0 < 1 / K := by positivity
      linarith
    by_cases hbθ : ((k : ℝ) + 1) / K ≤ θ
    · have hphi : topPhi c 0 θ (((k : ℝ) + 1) / K) = max 0 c := by
        unfold topPhi; rw [if_pos hbθ]; simp
      rw [hphi, min_eq_left hbθ, min_eq_left (hab.trans hbθ)]
      refine le_of_eq ?_
      calc max 0 c = K * (((k : ℝ) + 1) / K - (k : ℝ) / K) * max 0 c := by rw [hKba, one_mul]
        _ = K * (max 0 c * (((k : ℝ) + 1) / K) - max 0 c * ((k : ℝ) / K)) := by ring
    · have hphi : topPhi c 0 θ (((k : ℝ) + 1) / K) = 0 := by
        unfold topPhi; rw [if_neg hbθ]
      rw [hphi]
      have : max 0 c * min ((k : ℝ) / K) θ ≤ max 0 c * min (((k : ℝ) + 1) / K) θ :=
        mul_le_mul_of_nonneg_left (min_le_min_right θ hab) hcc0
      exact mul_nonneg hK.le (by linarith)
  have h := sum_le_of_count1 u (topPhi c 0 θ) (fun t => max 0 c * min t θ) hK humin hum
    (topPhi_nonneg c 0 θ) (fun s t hs hst => topPhi_anti le_rfl hs hst)
    (fun s t _ hst => mul_le_mul_of_nonneg_left (min_le_min_right θ hst) hcc0) hcount hstep
  calc ∑ j, topPhi c 0 θ (u j)
      ≤ topPhi c 0 θ umin + K * (max 0 c * min ((m : ℝ) / K) θ - max 0 c * min 0 θ) := h
    _ ≤ topPhi c 0 θ umin + K * (θ * max 0 c) := by
        rw [min_eq_left hθ.le]
        have h1 : max 0 c * min ((m : ℝ) / K) θ ≤ max 0 c * θ :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hcc0
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by nlinarith) hK.le)

/-- The cap sum in the closed form `capInt`. -/
theorem sum_topPhi_le {m : ℕ} (u : Fin m → ℝ) {c r θ K : ℝ} (hr : 0 ≤ r) (hθ : 0 < θ)
    (hK : 0 < K) {umin : ℝ} (humin : 0 < umin) (hum : ∀ j, umin ≤ u j)
    (hcount : ∀ j, 0 < topPhi c r θ (u j) →
      ((Finset.univ.filter (fun i => u i ≤ u j)).card : ℝ) ≤ K * u j + 1) :
    ∑ j, topPhi c r θ (u j) ≤ topPhi c r θ umin + K * capInt c r θ := by
  unfold capInt
  rcases hr.eq_or_lt with rfl | hpos
  · rw [if_neg (lt_irrefl (0 : ℝ))]; exact sum_topPhi_le_zero u hθ hK humin hum hcount
  · rw [if_pos hpos]; exact sum_topPhi_le_pos u hpos hθ hK humin hum hcount

/-! ### 3. One node family -/

/-- **Theorem S for one node family (counting form).**  Nodes `xs j < 1` with `0 ≤ x_c < 1`.
Off the top cell the field is at most `lam`; on the top cell `[x_c, 1)` it is at most
`g0 + r (-log (1 - x²))` (`r ≥ 0`); the nodes obey the top cap: the number of nodes `≥ xs j` is
at most `K (1 - xs j) + 1` for every top node (the exact discrete form of the density cap
`ν ≤ κ`), and all nodes satisfy `xs j ≤ 1 - umin`.  Then
`Σ f(xs j) ≤ m lam + (g0 - lam + r log (1/umin))^+ + K ∫_0^{1-x_c} (g0 - lam + r log (1/u))^+ du`,
the integral being `capInt`. -/
theorem sum_le_topCap {m : ℕ} (f : ℝ → ℝ) (xs : Fin m → ℝ) {xc lam g0 r K : ℝ}
    (hxc0 : 0 ≤ xc) (hxc1 : xc < 1) (hr : 0 ≤ r) (hK : 0 < K)
    (hx1 : ∀ j, xs j < 1) {umin : ℝ} (humin : 0 < umin) (hum : ∀ j, umin ≤ 1 - xs j)
    (hlow : ∀ j, xs j < xc → f (xs j) ≤ lam)
    (htop : ∀ j, xc ≤ xs j → f (xs j) ≤ g0 + r * (-Real.log (1 - xs j ^ 2)))
    (hcap : ∀ j, xc ≤ xs j →
      ((Finset.univ.filter (fun i => xs j ≤ xs i)).card : ℝ) ≤ K * (1 - xs j) + 1) :
    ∑ j, f (xs j) ≤ (m : ℝ) * lam + topPhi (g0 - lam) r (1 - xc) umin +
      K * capInt (g0 - lam) r (1 - xc) := by
  have hθ : 0 < 1 - xc := by linarith
  have hu : ∀ j, 0 < 1 - xs j := fun j => by linarith [hx1 j]
  have hpt : ∀ j, f (xs j) ≤ lam + topPhi (g0 - lam) r (1 - xc) (1 - xs j) := by
    intro j
    by_cases hj : xc ≤ xs j
    · have hle : 1 - xs j ≤ 1 - xc := by linarith
      have hx0 : 0 ≤ xs j := hxc0.trans hj
      have hlog : Real.log (1 - xs j) ≤ Real.log (1 - xs j ^ 2) := by
        apply Real.log_le_log (hu j)
        nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - xs j by linarith [hx1 j])]
      have h1 := htop j hj
      have h2 : r * (-Real.log (1 - xs j ^ 2)) ≤ r * (-Real.log (1 - xs j)) :=
        mul_le_mul_of_nonneg_left (neg_le_neg hlog) hr
      have h3 : g0 - lam + r * (-Real.log (1 - xs j)) ≤
          topPhi (g0 - lam) r (1 - xc) (1 - xs j) := by
        unfold topPhi; rw [if_pos hle]; exact le_max_right _ _
      linarith
    · have hgt : ¬ (1 - xs j ≤ 1 - xc) := by intro h; apply hj; linarith
      have h0 : topPhi (g0 - lam) r (1 - xc) (1 - xs j) = 0 := by
        unfold topPhi; rw [if_neg hgt]
      rw [h0]
      linarith [hlow j (not_le.mp hj)]
  have hsum1 : ∑ j, f (xs j) ≤
      ∑ j, (lam + topPhi (g0 - lam) r (1 - xc) (1 - xs j)) :=
    Finset.sum_le_sum fun j _ => hpt j
  have hconst : ∑ j : Fin m, lam = (m : ℝ) * lam := by simp
  rw [Finset.sum_add_distrib, hconst] at hsum1
  have hcnt : ∀ j, 0 < topPhi (g0 - lam) r (1 - xc) (1 - xs j) →
      ((Finset.univ.filter (fun i => 1 - xs i ≤ 1 - xs j)).card : ℝ) ≤ K * (1 - xs j) + 1 := by
    intro j hj
    have hjc : xc ≤ xs j := by
      by_contra hcon
      have hn : ¬ (1 - xs j ≤ 1 - xc) := by intro h; apply hcon; linarith
      unfold topPhi at hj
      rw [if_neg hn] at hj
      exact lt_irrefl _ hj
    have e : (Finset.univ.filter (fun i => 1 - xs i ≤ 1 - xs j)) =
        Finset.univ.filter (fun i => xs j ≤ xs i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro h <;> linarith
    rw [e]
    exact hcap j hjc
  have hphi : ∑ j, topPhi (g0 - lam) r (1 - xc) (1 - xs j) ≤
      topPhi (g0 - lam) r (1 - xc) umin + K * capInt (g0 - lam) r (1 - xc) :=
    sum_topPhi_le (fun j => 1 - xs j) hr hθ hK humin hum hcnt
  linarith

/-! ### 4. The fixed-node fields and the `fixedSum` contract field -/

/-- **Admissibility with the top cap.**  The first-kind negatives lie in `[-1, -g*]`, the positives
(first kind and near) in `[g*, 1)`, and each positive family obeys the top cap: for a node in the
top cell `[x_c, 1)`, the number of nodes of the family at least as large is at most
`C₁ n (1 - x) + 1` (`n` the number of rows; the `+ 1` is the discreteness of the nodes, the density
cap `ν ≤ κ` of the paper holding with its constant `C₁`), and all positives satisfy
`x ≤ 1 - umin` (the node gap at 1).  This is the whole content of `FixAdm` that the σ bound
needs; a contract `FixAdm` only has to imply it (no cap cells, no `κᵢ` table). -/
def FixAdmCap (gs xc C1 n umin : ℝ) {m1 m2 s : ℕ} (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ)
    (zp : Fin s → ℝ) : Prop :=
  (∀ j, yn j ≤ -gs) ∧ (∀ j, gs ≤ yp j) ∧ (∀ j, gs ≤ zp j) ∧
    (∀ j, yp j ≤ 1 - umin) ∧ (∀ j, zp j ≤ 1 - umin) ∧
    (∀ j, xc ≤ yp j →
      ((Finset.univ.filter (fun i => yp j ≤ yp i)).card : ℝ) ≤ C1 * n * (1 - yp j) + 1) ∧
    (∀ j, xc ≤ zp j →
      ((Finset.univ.filter (fun i => zp j ≤ zp i)).card : ℝ) ≤ C1 * n * (1 - zp j) + 1)

/-- The data of the σ bound of one α-interval: `gs = g*`, the start `xc` of the top cell, the cap
density `C1` (per unit of `n`), and the field bounds as functions of the fixed fraction `α`
(and of the near fraction `β`): `lam*` bound the fields off the top cell, `g*` the top-cell
fields without the log term, `r*` the coefficient of `-log (1 - x²)` on the top cell. -/
structure SigmaCapData where
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  lamN : ℝ → ℝ
  lamP : ℝ → ℝ
  gP : ℝ → ℝ
  rP : ℝ → ℝ
  lamS : ℝ → ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  rS : ℝ → ℝ → ℝ

/-- The bound `ZB` of the σ dual with the top cap, in the contract's arguments
`(c, d, β) = (m₁/n, m₂/n, s/n)` (with `α = c + d + β`): the three node masses times the
off-top bounds, plus the two top-cell terms `C₁ · capInt`. -/
def zbCap (S : SigmaCapData) (c d β : ℝ) : ℝ :=
  c * S.lamN (c + d + β) + d * S.lamP (c + d + β) + β * S.lamS (c + d + β) β +
    S.C1 * (capInt (S.gP (c + d + β) - S.lamP (c + d + β)) (S.rP (c + d + β)) (1 - S.xc) +
      capInt (S.gS (c + d + β) β - S.lamS (c + d + β) β) (S.rS (c + d + β) β) (1 - S.xc))

/-- **Theorem S (fixed `N`), the three fixed families.**  Off-top bounds `lamN`, `lamP`, `lamS`
(each plus the slack `ε`) of `fNegM` on `(-1, -g*]`, `fPosMR` and `fNearMS` on `[g*, x_c)`; on the
top cell `fPosMS ≤ gP + ε` (so `fPosMR ≤ gP + ε + rP (-log (1 - x²))` as `rc α ≤ rP`) and
`fNearMS ≤ gS + ε + rS (-log (1 - x²))`.  With the top cap of `FixAdmCap`:
`Σ fNegM + Σ fPosMR + Σ fNearMS ≤ m₁(lamN+ε) + m₂(lamP+ε) + s(lamS+ε) + C₁ ν (capInt + capInt)`
plus the two one-node terms `topPhi … umin` (each `(g0 - lam + r log (1/umin))^+`). -/
theorem fixed_sum_le_cap (S : SigmaCapData) (D : SignedData) (Rm Rn : ℝ → ℝ)
    {rc α β ε umin : ℝ} {m1 m2 s : ℕ} (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
    (hxc0 : 0 ≤ S.xc) (hxc1 : S.xc < 1) (hC1 : 0 < S.C1) (hν : 0 < D.ν)
    (hrc : 0 ≤ rc) (hα : 0 ≤ α) (hrP : rc * α ≤ S.rP α) (hrS : 0 ≤ S.rS α β)
    (hyn : ∀ j, yn j ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ j, yp j ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ j, zp j ∈ Ioo (0 : ℝ) 1)
    (humin : 0 < umin) (hadm : FixAdmCap S.gs S.xc S.C1 D.ν umin yn yp zp)
    (hneg : ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -S.gs → D.fNegM Rm x ≤ S.lamN α + ε)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, S.gs ≤ x → x < S.xc →
      D.fPosMR Rm rc α x ≤ S.lamP α + ε)
    (hposTop : ∀ x ∈ Ioo (0 : ℝ) 1, S.xc ≤ x → D.fPosMS Rm x ≤ S.gP α + ε)
    (hnear : ∀ x ∈ Ioo (0 : ℝ) 1, S.gs ≤ x → x < S.xc →
      D.fNearMS Rn α β x ≤ S.lamS α β + ε)
    (hnearTop : ∀ x ∈ Ioo (0 : ℝ) 1, S.xc ≤ x →
      D.fNearMS Rn α β x ≤ S.gS α β + ε + S.rS α β * (-Real.log (1 - x ^ 2))) :
    (∑ j, D.fNegM Rm (yn j)) + (∑ j, D.fPosMR Rm rc α (yp j)) +
        ∑ j, D.fNearMS Rn α β (zp j) ≤
      (m1 : ℝ) * (S.lamN α + ε) + (m2 : ℝ) * (S.lamP α + ε) + (s : ℝ) * (S.lamS α β + ε) +
        S.C1 * D.ν * (capInt (S.gP α - S.lamP α) (S.rP α) (1 - S.xc) +
          capInt (S.gS α β - S.lamS α β) (S.rS α β) (1 - S.xc)) +
        topPhi (S.gP α - S.lamP α) (S.rP α) (1 - S.xc) umin +
        topPhi (S.gS α β - S.lamS α β) (S.rS α β) (1 - S.xc) umin := by
  obtain ⟨hgn, hgp, hgz, hup, huz, hcp, hcz⟩ := hadm
  have hK : 0 < S.C1 * D.ν := mul_pos hC1 hν
  have hrP0 : 0 ≤ S.rP α := (mul_nonneg hrc hα).trans hrP
  have A : ∑ j, D.fNegM Rm (yn j) ≤ (m1 : ℝ) * (S.lamN α + ε) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => D.fNegM Rm (yn j)) (S.lamN α + ε)
      (fun j _ => hneg _ (hyn j) (hgn j))
    simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have B := sum_le_topCap (D.fPosMR Rm rc α) yp (xc := S.xc) (lam := S.lamP α + ε)
    (g0 := S.gP α + ε) (r := S.rP α) (K := S.C1 * D.ν) hxc0 hxc1 hrP0 hK
    (fun j => (hyp j).2) humin (fun j => by linarith [hup j])
    (fun j hj => hpos _ (hyp j) (hgp j) hj)
    (fun j hj => by
      have hx := hyp j
      have hlog : 0 ≤ -Real.log (1 - yp j ^ 2) := by
        have : Real.log (1 - yp j ^ 2) ≤ 0 := by
          apply Real.log_nonpos <;> nlinarith [hx.1, hx.2]
        linarith
      have h1 := hposTop _ hx hj
      have h2 : rc * α * (-Real.log (1 - yp j ^ 2)) ≤ S.rP α * (-Real.log (1 - yp j ^ 2)) :=
        mul_le_mul_of_nonneg_right hrP hlog
      unfold SignedData.fPosMR
      linarith)
    hcp
  have C := sum_le_topCap (D.fNearMS Rn α β) zp (xc := S.xc) (lam := S.lamS α β + ε)
    (g0 := S.gS α β + ε) (r := S.rS α β) (K := S.C1 * D.ν) hxc0 hxc1 hrS hK
    (fun j => (hzp j).2) humin (fun j => by linarith [huz j])
    (fun j hj => hnear _ (hzp j) (hgz j) hj)
    (fun j hj => hnearTop _ (hzp j) hj)
    hcz
  rw [add_sub_add_right_eq_sub] at B C
  have e := mul_add (S.C1 * D.ν) (capInt (S.gP α - S.lamP α) (S.rP α) (1 - S.xc))
    (capInt (S.gS α β - S.lamS α β) (S.rS α β) (1 - S.xc))
  linarith [A, B, C, e]

/-- The algebra of the normalisation `1/n`. -/
theorem assemble_aux {n m1 m2 s a b c P Q C1 ε : ℝ} (hn : 0 < n) :
    (1 / n) * (m1 * (a + ε) + m2 * (b + ε) + s * (c + ε) + C1 * n * (P + Q)) =
      m1 / n * a + m2 / n * b + s / n * c + C1 * (P + Q) + (m1 + m2 + s) / n * ε := by
  have hn0 : n ≠ 0 := hn.ne'
  field_simp <;> ring

/-- The contract field `fixedSum` of `SignedNearBounds` for ONE α-interval `[lo, hi]`, written with
the interval's data as arguments (`T.ncount`, `T.D i`, `T.Rm`, `T.Rn`, `remC (T.epsSplit i)`,
`T.lo i`, `T.hi i`, `T.ZB i`, `T.FixAdm`).  `fixedSumAt_conform` shows it is exactly the field. -/
def FixedSumAt (ncount : ℕ → ℕ) (D : ℕ → ℝ → SignedData) (Rm Rn : ℕ → ℝ → ℝ)
    (rc lo hi : ℝ) (ZB : ℝ → ℝ → ℝ → ℝ)
    (FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
    ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) → (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
      FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (ncount N : ℝ) = α →
      (1 / (D N α).ν) * ((∑ j, (D N α).fNegM (Rm N) (yn j)) +
          (∑ j, (D N α).fPosMR (Rm N) rc α (yp j)) +
          ∑ j, (D N α).fNearMS (Rn N) α ((s : ℝ) / (ncount N : ℝ)) (zp j)) ≤
        ZB ((m1 : ℝ) / (ncount N : ℝ)) ((m2 : ℝ) / (ncount N : ℝ))
          ((s : ℝ) / (ncount N : ℝ)) + ε

/-- Conformance: the contract field `fixedSum` of interval `i` is `FixedSumAt` (same statement,
binder for `ε` aside). -/
theorem fixedSumAt_conform {I : ℕ} (T : SignedNearBounds I) (i : Fin I) :
    FixedSumAt T.ncount (T.D i) T.Rm T.Rn (remC (T.epsSplit i)) (T.lo i) (T.hi i) (T.ZB i)
      T.FixAdm :=
  fun _ hε => T.fixedSum i hε

/-- **The `fixedSum` constructor (Theorem S).**  Given the endpoint field bounds off the top cell
(`hneg`, `hpos`, `hnear`: eventually in `N`, uniformly for `α ∈ [lo, hi]`, with slack `ε`), the
top-cell bounds without the log term (`hposTop`, `hnearTop`), and a `FixAdm` that implies the top
cap (`hFix`), the field `fixedSum` holds with any `ZB ≥ zbCap S`.  No cell LP; the top cap is
the single count of `FixAdmCap`.  Use: `fixedSum := fun i {ε} hε => fixedSumAt_of_cap (S i) … ε hε`. -/
theorem fixedSumAt_of_cap (S : SigmaCapData) {ncount : ℕ → ℕ} {D : ℕ → ℝ → SignedData}
    {Rm Rn : ℕ → ℝ → ℝ} {rc lo hi : ℝ} {ZB : ℝ → ℝ → ℝ → ℝ}
    {FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop}
    (hxc0 : 0 ≤ S.xc) (hxc1 : S.xc < 1) (hC1 : 0 < S.C1) (hrc : 0 ≤ rc) (hlo : 0 ≤ lo)
    (hhi : hi ≤ 1)
    (hn : ∀ N, 0 < N → 0 < ncount N) (hν : ∀ N α, (D N α).ν = (ncount N : ℝ))
    (hrP : ∀ α ∈ Icc lo hi, rc * α ≤ S.rP α)
    (hrS : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, 0 ≤ S.rS α β)
    (umin : ℕ → ℝ) (hum0 : ∀ N, 0 < umin N) (hum1 : ∀ N, umin N ≤ 1) (Bd Rbd : ℝ)
    (hBdP : ∀ α ∈ Icc lo hi, S.gP α - S.lamP α ≤ Bd)
    (hBdS : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, S.gS α β - S.lamS α β ≤ Bd)
    (hRP : ∀ α ∈ Icc lo hi, S.rP α ≤ Rbd)
    (hRS : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, S.rS α β ≤ Rbd)
    (hn_top : Filter.Tendsto (fun N => (ncount N : ℝ)) Filter.atTop Filter.atTop)
    (hlogu : Filter.Tendsto (fun N => -Real.log (umin N) / (ncount N : ℝ)) Filter.atTop
      (nhds 0))
    (hFix : ∀ N m1 m2 s (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      FixAdm N m1 m2 s yn yp zp →
        FixAdmCap S.gs S.xc S.C1 (ncount N : ℝ) (umin N) yn yp zp)
    (hZB : ∀ c d β, 0 ≤ c → 0 ≤ d → 0 ≤ β → zbCap S c d β ≤ ZB c d β)
    (hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -S.gs → (D N α).fNegM (Rm N) x ≤ S.lamN α + ε)
    (hpos : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, S.gs ≤ x → x < S.xc →
        (D N α).fPosMR (Rm N) rc α x ≤ S.lamP α + ε)
    (hposTop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, S.xc ≤ x → (D N α).fPosMS (Rm N) x ≤ S.gP α + ε)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, S.gs ≤ x → x < S.xc →
        (D N α).fNearMS (Rn N) α β x ≤ S.lamS α β + ε)
    (hnearTop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, S.xc ≤ x →
        (D N α).fNearMS (Rn N) α β x ≤
          S.gS α β + ε + S.rS α β * (-Real.log (1 - x ^ 2))) :
    FixedSumAt ncount D Rm Rn rc lo hi ZB FixAdm := by
  unfold FixedSumAt
  intro ε hε
  have hε' : 0 < ε / 2 := half_pos hε
  have hinv : Filter.Tendsto (fun N => ((ncount N : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hn_top
  have hT : Filter.Tendsto (fun N => 2 * max 0 Bd * ((ncount N : ℝ))⁻¹ +
      2 * Rbd * (-Real.log (umin N) / (ncount N : ℝ))) Filter.atTop (nhds 0) := by
    have := ((tendsto_const_nhds (x := 2 * max 0 Bd)).mul hinv).add
      ((tendsto_const_nhds (x := 2 * Rbd)).mul hlogu)
    simpa using this
  filter_upwards [hneg (ε / 2) hε', hpos (ε / 2) hε', hposTop (ε / 2) hε', hnear (ε / 2) hε',
    hnearTop (ε / 2) hε', hT.eventually (gt_mem_nhds hε'), Filter.eventually_gt_atTop 0]
    with N h1 h2 h3 h4 h5 hfN hN0
  intro α hα m1 m2 s yn yp zp hyn hyp hzp hadm heq
  have hnN : (0 : ℝ) < (ncount N : ℝ) := by exact_mod_cast hn N hN0
  have hνN : (D N α).ν = (ncount N : ℝ) := hν N α
  have hα0 : 0 ≤ α := hlo.trans hα.1
  have hα1 : α ≤ 1 := hα.2.trans hhi
  have hsum : (m1 : ℝ) / (ncount N : ℝ) + (m2 : ℝ) / (ncount N : ℝ) + (s : ℝ) / (ncount N : ℝ) =
      α := by
    rw [← heq]; push_cast; ring
  have hc0 : 0 ≤ (m1 : ℝ) / (ncount N : ℝ) := by positivity
  have hd0 : 0 ≤ (m2 : ℝ) / (ncount N : ℝ) := by positivity
  have hβ0 : 0 ≤ (s : ℝ) / (ncount N : ℝ) := by positivity
  have hβα : (s : ℝ) / (ncount N : ℝ) ≤ α := by linarith
  have hadm' : FixAdmCap S.gs S.xc S.C1 (D N α).ν (umin N) yn yp zp := by
    rw [hνN]; exact hFix N m1 m2 s yn yp zp hadm
  have hmain := fixed_sum_le_cap S (D N α) (Rm N) (Rn N) (rc := rc) (α := α)
    (β := (s : ℝ) / (ncount N : ℝ)) (ε := ε / 2) (umin := umin N) yn yp zp hxc0 hxc1 hC1
    (by rw [hνN]; exact hnN)
    hrc hα0 (hrP α hα) (hrS α hα _ ⟨hβ0, hβα⟩) hyn hyp hzp (hum0 N) hadm'
    (h1 α hα) (h2 α hα) (h3 α hα) (h4 α hα _ ⟨hβ0, hβα⟩) (h5 α hα _ ⟨hβ0, hβα⟩)
  rw [hνN] at hmain ⊢
  have hZ := hZB _ _ _ hc0 hd0 hβ0
  unfold zbCap at hZ
  rw [hsum] at hZ
  have hid := assemble_aux (n := (ncount N : ℝ)) (m1 := (m1 : ℝ)) (m2 := (m2 : ℝ))
    (s := (s : ℝ)) (a := S.lamN α) (b := S.lamP α) (c := S.lamS α ((s : ℝ) / (ncount N : ℝ)))
    (P := capInt (S.gP α - S.lamP α) (S.rP α) (1 - S.xc))
    (Q := capInt (S.gS α ((s : ℝ) / (ncount N : ℝ)) -
      S.lamS α ((s : ℝ) / (ncount N : ℝ))) (S.rS α ((s : ℝ) / (ncount N : ℝ))) (1 - S.xc))
    (C1 := S.C1) (ε := ε / 2) hnN
  have hmul := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 1 / (ncount N : ℝ) by positivity)
  have hε2 : ((m1 : ℝ) + m2 + s) / (ncount N : ℝ) * (ε / 2) ≤ ε / 2 := by
    have h : ((m1 : ℝ) + m2 + s) / (ncount N : ℝ) = α := by rw [← hsum]; ring
    rw [h]; nlinarith [mul_nonneg (sub_nonneg.2 hα1) hε'.le]
  have hrP0 : 0 ≤ S.rP α := (mul_nonneg hrc hα0).trans (hrP α hα)
  have hE1 := topPhi_le_aux (θ := 1 - S.xc) (hum0 N) (hum1 N) hrP0 (hBdP α hα) (hRP α hα)
  have hE2 := topPhi_le_aux (θ := 1 - S.xc) (hum0 N) (hum1 N) (hrS α hα _ ⟨hβ0, hβα⟩)
    (hBdS α hα _ ⟨hβ0, hβα⟩) (hRS α hα _ ⟨hβ0, hβα⟩)
  have hEs := mul_le_mul_of_nonneg_left (add_le_add hE1 hE2)
    (show 0 ≤ 1 / (ncount N : ℝ) by positivity)
  have hEe : 1 / (ncount N : ℝ) * ((max 0 Bd + Rbd * (-Real.log (umin N))) +
      (max 0 Bd + Rbd * (-Real.log (umin N)))) =
      2 * max 0 Bd * ((ncount N : ℝ))⁻¹ +
        2 * Rbd * (-Real.log (umin N) / (ncount N : ℝ)) := by ring
  linarith [hmul, hid, hε2, hZ, hEs, hEe, hfN]

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.capPrim_sub_ge
#print axioms CatalanMeasure.Signed.capInt_le_mul_exp
#print axioms CatalanMeasure.Signed.sum_le_of_count1
#print axioms CatalanMeasure.Signed.topPhi_le_aux
#print axioms CatalanMeasure.Signed.sum_topPhi_le
#print axioms CatalanMeasure.Signed.sum_le_topCap
#print axioms CatalanMeasure.Signed.fixed_sum_le_cap
#print axioms CatalanMeasure.Signed.fixedSumAt_conform
#print axioms CatalanMeasure.Signed.fixedSumAt_of_cap
