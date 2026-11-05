module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeP
public import Submission.CatalanMeasure.GenD.Signed.SpikeEnds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# D2 constants: closed-form spike constants of a finitely supported trial (generic soundness)

For `b = bSeq bs` (finitely supported) the series in `costRem`, `barrierTrialS` and the Poisson
pairing are finite rational sums (`idxSum`).  This file proves
* `costRem_le`: `costRem (l * bSeq bs) s' m rho <= K0` for all `m <= kappa (s' + m)` and every count
  parameter `l in [l1, l2]` from the rational corner check `K0check` (`costRem` is affine in `m / s'` and
  convex in `l`: the screen's "hK uniform in x");
* `De2_of_cov`: `S_b(-y) - S_b(-rho) <= De2` on `[A/2^S, B/2^S]` from an integer cell chain for
  the polynomial `De2 + sigma - S_b(-y)` (scaled by `Lc 2^60`, `Lc` a multiple of `1..K`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed

def idxSum (f : ℕ → ℚ → ℚ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | x :: xs, k => f k x + idxSum f xs (k + 1)

theorem idxSum_cast (f : ℕ → ℚ → ℚ) (bs : List ℚ) : ∀ k0 : ℕ,
    ((idxSum f bs k0 : ℚ) : ℝ) =
      ∑ j ∈ Finset.range bs.length, ((f (k0 + j) (bs.getD j 0) : ℚ) : ℝ) := by
  induction bs with
  | nil => intro k0; simp [idxSum]
  | cons x xs ih =>
    intro k0
    rw [idxSum, Rat.cast_add, ih (k0 + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have : ∀ j, k0 + 1 + j = k0 + (j + 1) := fun j => by ring
    simp only [this]; ring

theorem getD_zero_of_le (bs : List ℚ) {k : ℕ} (h : bs.length ≤ k) : bs.getD k 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem bSeq_succ (bs : List ℚ) (k : ℕ) : bSeq bs (k + 1) = ((bs.getD k 0 : ℚ) : ℝ) := by
  unfold bSeq
  rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]

theorem tsum_bSeq (bs : List ℚ) (g : ℕ → ℝ → ℝ) (hg0 : ∀ k, g k 0 = 0) :
    ∑' k : ℕ, g k (bSeq bs (k + 1)) = ∑ j ∈ Finset.range bs.length, g j ((bs.getD j 0 : ℚ) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range bs.length)]
  · exact Finset.sum_congr rfl fun k _ => by rw [bSeq_succ]
  · intro k hk
    have hk' : bs.length ≤ k := by simpa using hk
    rw [bSeq_succ, getD_zero_of_le bs hk']
    simpa using hg0 k

/-! ### The series of `costRem` as rational sums -/

def S1q (bs : List ℚ) : ℚ := idxSum (fun _ x => x ^ 2) bs 0
def S2q (bs : List ℚ) : ℚ := idxSum (fun k x => 2 * x ^ 2 / ((k : ℚ) + 1)) bs 0
def Spq (bs : List ℚ) (ρ : ℚ) : ℚ := idxSum (fun k x => x * (-ρ) ^ (k + 1)) bs 0
def Sbq (bs : List ℚ) (x : ℚ) : ℚ := idxSum (fun k c => c * x ^ (k + 1) / ((k : ℚ) + 1)) bs 0

theorem tsum_sq_bSeq (bs : List ℚ) :
    ∑' k : ℕ, bSeq bs (k + 1) ^ 2 = (S1q bs : ℝ) := by
  have := tsum_bSeq bs (fun _ t => t ^ 2) (fun _ => by simp)
  rw [this, S1q, idxSum_cast]; push_cast; simp

theorem tsum_S2_bSeq (bs : List ℚ) :
    ∑' i : ℕ, 2 * bSeq bs (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) = (S2q bs : ℝ) := by
  have := tsum_bSeq bs (fun i t => 2 * t ^ 2 / ((i + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, S2q, idxSum_cast]; push_cast; simp

theorem tsum_Sp_bSeq (bs : List ℚ) (ρ : ℚ) :
    ∑' k : ℕ, bSeq bs (k + 1) * poisSeq (ρ : ℝ) (k + 1) = (Spq bs ρ : ℝ) := by
  have := tsum_bSeq bs (fun k t => t * poisSeq (ρ : ℝ) (k + 1)) (fun _ => by simp)
  rw [this, Spq, idxSum_cast]; push_cast; simp [poisSeq]

theorem barrierTrialS_bSeq (bs : List ℚ) (x : ℚ) :
    barrierTrialS (bSeq bs) (x : ℝ) = (Sbq bs x : ℝ) := by
  unfold barrierTrialS
  have := tsum_bSeq bs (fun k t => t * (x : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, Sbq, idxSum_cast]; push_cast; simp

/-! ### `costRem` of the count trial `l * b` -/

/-- The part of `costRem (l b)` that is independent of `m/s'`: with `S1 = Σ b²`, `S2 = Σ 2b²/k`,
`Sp = Σ b (-ρ)^k`, `Sb = S_b(-ρ)`:  `c(l) = l² (2 S1 - S2) - 4 l Sp + 4 l Sb` (convex in `l`). -/
def cq (bs : List ℚ) (ρ l : ℚ) : ℚ :=
  l ^ 2 * (2 * S1q bs - S2q bs) - 4 * l * Spq bs ρ + 4 * l * Sbq bs (-ρ)

/-- The same for a real count parameter. -/
def cR (bs : List ℚ) (ρ : ℚ) (l : ℝ) : ℝ :=
  l ^ 2 * (2 * (S1q bs : ℝ) - (S2q bs : ℝ)) - 4 * l * (Spq bs ρ : ℝ) + 4 * l * (Sbq bs (-ρ) : ℝ)

theorem cq_cast (bs : List ℚ) (ρ l : ℚ) : ((cq bs ρ l : ℚ) : ℝ) = cR bs ρ (l : ℝ) := by
  unfold cq cR; push_cast; ring

/-- `log 2 < LOG2U`. -/
def LOG2U : ℚ := 6931471808 / 10 ^ 10

theorem log_two_lt_LOG2U : Real.log 2 < (LOG2U : ℝ) := by
  have := Real.log_two_lt_d9
  unfold LOG2U; push_cast; norm_num; linarith

theorem tsum_lam_S2 (bs : List ℚ) (l : ℝ) :
    ∑' i : ℕ, 2 * (l * bSeq bs (i + 1)) ^ 2 / ((i + 1 : ℕ) : ℝ) = l ^ 2 * (S2q bs : ℝ) := by
  rw [← tsum_S2_bSeq, ← tsum_mul_left]
  exact tsum_congr fun i => by ring

theorem tsum_lam_S1 (bs : List ℚ) (l : ℝ) :
    ∑' k : ℕ, (l * bSeq bs (k + 1)) ^ 2 = l ^ 2 * (S1q bs : ℝ) := by
  rw [← tsum_sq_bSeq, ← tsum_mul_left]
  exact tsum_congr fun i => by ring

theorem tsum_lam_Sp (bs : List ℚ) (ρ : ℚ) (l : ℝ) :
    ∑' k : ℕ, (l * bSeq bs (k + 1)) * poisSeq (ρ : ℝ) (k + 1) = l * (Spq bs ρ : ℝ) := by
  rw [← tsum_Sp_bSeq, ← tsum_mul_left]
  exact tsum_congr fun i => by ring

theorem barrierTrialS_lam (bs : List ℚ) (x : ℚ) (l : ℝ) :
    barrierTrialS (fun k => l * bSeq bs k) (x : ℝ) = l * (Sbq bs x : ℝ) := by
  rw [← barrierTrialS_bSeq]
  unfold barrierTrialS
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by ring

/-- **`costRem` of `l b`** (the count trial `b_x = (s_r/x) b`, `l = s_r/x`):
`log 2 + c(l) + (c(l) + 2ρ²/(1-ρ²)) (m/s')`; affine in `m/s'`, convex in `l`. -/
theorem costRem_lam_eq (bs : List ℚ) (ρ : ℚ) (l : ℝ) (s' m : ℕ) (hs : 0 < s')
    (hρ : (ρ : ℝ) ^ 2 ≠ 1) :
    costRem (fun k => l * bSeq bs k) s' m (ρ : ℝ) =
      (Real.log 2 + cR bs ρ l) +
        (cR bs ρ l + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((m : ℝ) / s') := by
  have hs' : (s' : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold costRem
  beta_reduce
  have hb := barrierTrialS_lam bs (-ρ) l
  push_cast at hb
  rw [tsum_lam_S2, tsum_lam_S1, tsum_lam_Sp, hb]
  unfold cR
  have h1 : (1 : ℝ) - (ρ : ℝ) ^ 2 ≠ 0 := fun h => hρ (by linarith)
  field_simp
  ring

theorem aff_w_le {L2 c q K0 w wm : ℝ} (h0 : L2 + c ≤ K0) (h1 : L2 + c + (c + q) * wm ≤ K0)
    (hw0 : 0 ≤ w) (hw : w ≤ wm) : L2 + c + (c + q) * w ≤ K0 := by
  by_cases hc : c + q ≤ 0
  · nlinarith [mul_nonneg hw0 (neg_nonneg.mpr hc)]
  · push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_left hw hc.le]

theorem convex_endpoint {Q T l1 l l2 : ℝ} (hQ : 0 ≤ Q) (h1 : l1 ≤ l) (h2 : l ≤ l2) :
    Q * l ^ 2 - T * l ≤ Q * l1 ^ 2 - T * l1 ∨ Q * l ^ 2 - T * l ≤ Q * l2 ^ 2 - T * l2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2⟩ := hcon
  rcases eq_or_lt_of_le h1 with e1 | e1
  · rw [← e1] at c1; exact lt_irrefl _ c1
  rcases eq_or_lt_of_le h2 with e2 | e2
  · rw [e2] at c2; exact lt_irrefl _ c2
  have d1 : Q * l ^ 2 - T * l - (Q * l1 ^ 2 - T * l1) = (l - l1) * (Q * (l + l1) - T) := by ring
  have d2 : Q * l ^ 2 - T * l - (Q * l2 ^ 2 - T * l2) = (l - l2) * (Q * (l + l2) - T) := by ring
  have p1 : 0 < (l - l1) * (Q * (l + l1) - T) := by rw [← d1]; linarith
  have p2 : 0 < (l - l2) * (Q * (l + l2) - T) := by rw [← d2]; linarith
  have q1 : 0 < Q * (l + l1) - T := (mul_pos_iff_of_pos_left (sub_pos.2 e1)).mp p1
  have q2 : Q * (l + l2) - T < 0 := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (sub_nonneg.2 e2.le) h]
  nlinarith [mul_nonneg hQ (sub_nonneg.2 (e1.trans e2).le)]

def K0check (bs : List ℚ) (ρ κ l1 l2 K0 : ℚ) : Bool :=
  decide (0 ≤ 2 * S1q bs - S2q bs) &&
  decide (LOG2U + cq bs ρ l1 ≤ K0) &&
    decide (LOG2U + cq bs ρ l1 + (cq bs ρ l1 + 2 * ρ ^ 2 / (1 - ρ ^ 2)) * (κ / (1 - κ)) ≤ K0) &&
  decide (LOG2U + cq bs ρ l2 ≤ K0) &&
    decide (LOG2U + cq bs ρ l2 + (cq bs ρ l2 + 2 * ρ ^ 2 / (1 - ρ ^ 2)) * (κ / (1 - κ)) ≤ K0)

/-- **`hK` uniformly in the count** (`l = s_r/x ∈ [l1, l2]`): the four corners
(`l ∈ {l1, l2}`, `m/s' ∈ {0, κ/(1-κ)}`) decide it, by convexity in `l` and affinity in `m/s'`. -/
theorem costRem_le {bs : List ℚ} {ρ κ l1 l2 K0 : ℚ} {l : ℝ}
    (hK : K0check bs ρ κ l1 l2 K0 = true) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hρ : (ρ : ℝ) ^ 2 ≠ 1) (hl1 : (l1 : ℝ) ≤ l) (hl2 : l ≤ (l2 : ℝ))
    {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (κ : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs k) s' m (ρ : ℝ) ≤ (K0 : ℝ) := by
  rw [costRem_lam_eq bs ρ l s' m hs hρ]
  unfold K0check at hK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hK
  obtain ⟨⟨⟨⟨hQ, h1a⟩, h1b⟩, h2a⟩, h2b⟩ := hK
  have hκ1' : (κ : ℝ) < 1 := by exact_mod_cast hκ1
  have hκ0' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ0
  have hs0 : (0 : ℝ) < s' := by exact_mod_cast hs
  have hw0 : 0 ≤ (m : ℝ) / s' := by positivity
  have hwm : (m : ℝ) / s' ≤ (κ : ℝ) / (1 - κ) := by
    rw [div_le_div_iff₀ hs0 (by linarith)]
    nlinarith
  have hl2U := log_two_lt_LOG2U
  have cast_a : ∀ l' : ℚ, LOG2U + cq bs ρ l' ≤ K0 →
      Real.log 2 + cR bs ρ (l' : ℝ) ≤ (K0 : ℝ) := by
    intro l' h
    have h' : ((LOG2U + cq bs ρ l' : ℚ) : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast h
    rw [Rat.cast_add, cq_cast] at h'
    linarith
  have cast_b : ∀ l' : ℚ, LOG2U + cq bs ρ l' + (cq bs ρ l' + 2 * ρ ^ 2 / (1 - ρ ^ 2)) *
      (κ / (1 - κ)) ≤ K0 → Real.log 2 + cR bs ρ (l' : ℝ) +
      (cR bs ρ (l' : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((κ : ℝ) / (1 - κ)) ≤ (K0 : ℝ) := by
    intro l' h
    have h' : ((LOG2U + cq bs ρ l' + (cq bs ρ l' + 2 * ρ ^ 2 / (1 - ρ ^ 2)) * (κ / (1 - κ)) : ℚ) : ℝ)
        ≤ (K0 : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [cq_cast] at h'
    linarith
  have hcx : ∀ l' : ℚ, cR bs ρ (l : ℝ) ≤ cR bs ρ (l' : ℝ) →
      LOG2U + cq bs ρ l' ≤ K0 → LOG2U + cq bs ρ l' + (cq bs ρ l' + 2 * ρ ^ 2 / (1 - ρ ^ 2)) *
        (κ / (1 - κ)) ≤ K0 →
      Real.log 2 + cR bs ρ l + (cR bs ρ l + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) *
        ((m : ℝ) / s') ≤ (K0 : ℝ) := by
    intro l' hge ha hb
    have step := aff_w_le (cast_a l' ha) (cast_b l' hb) hw0 hwm
    have : Real.log 2 + cR bs ρ l + (cR bs ρ l + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) *
        ((m : ℝ) / s') ≤ Real.log 2 + cR bs ρ (l' : ℝ) +
        (cR bs ρ (l' : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((m : ℝ) / s') := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.2 hge)]
    exact this.trans step
  have hQ' : (0 : ℝ) ≤ 2 * (S1q bs : ℝ) - (S2q bs : ℝ) := by exact_mod_cast hQ
  have hform : ∀ t : ℝ, cR bs ρ t = (2 * (S1q bs : ℝ) - (S2q bs : ℝ)) * t ^ 2 -
      (4 * (Spq bs ρ : ℝ) - 4 * (Sbq bs (-ρ) : ℝ)) * t := fun t => by unfold cR; ring
  have hconv := convex_endpoint (T := 4 * (Spq bs ρ : ℝ) - 4 * (Sbq bs (-ρ) : ℝ)) hQ' hl1 hl2
  simp only [← hform] at hconv
  rcases hconv with h | h
  · exact hcx l1 h h1a h1b
  · exact hcx l2 h h2a h2b

end CatalanMeasure.Signed.Consts
