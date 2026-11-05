module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPrime
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# The H' family, design-generic

For a digit `s` and block range `k0 ≤ k ≤ k1` the value `hpVal P N p s k0 k1` is the integer bound
of Theorem H' (`m (d2 + 1 - e0)`, `m = min(K, K+1-|JJ|)`), computed from `(n, b, q, g, h, p)`
only.  `hpVal_le_nullity` proves `hpVal ≤ ν` for every admissible design; no design literal occurs.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

/-- `η = H - 1 - s p`, the top of window `s`. -/
def hpEta (P : Parameters) (N p s : ℕ) : ℕ := P.H N - 1 - s * p

/-- `j* = max(1, -g - k0 p, (k1+1) p - (n-1-g))`. -/
def hpJstar (P : Parameters) (N p : ℕ) (k0 k1 : ℤ) : ℤ :=
  max 1 (max (-(P.g N : ℤ) - k0 * p) ((k1 + 1) * p - ((P.n N : ℤ) - 1 - P.g N)))

/-- `d2 = min(h - j*, η - h - h_p)` (`h_p = (p-1)/2`), an integer. -/
def hpDD (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : ℤ :=
  min (hh p - hpJstar P N p k0 k1) ((hpEta P N p s : ℤ) - P.h N - hh p)

/-- Number of slots. -/
def hpD (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : ℕ := (hpDD P N p s k0 k1).toNat + 1

/-- Number of vanishing jets `e0 = (η - p + 1)_+`. -/
def hpElo (P : Parameters) (N p s : ℕ) : ℕ := hpEta P N p s + 1 - p

/-- Digits of the raw columns that see the window. -/
def hpJJ (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : Finset ℕ :=
  (Finset.range (P.L N / p + 2)).filter fun J =>
    max (J * p + (hpEta P N p s - (P.h N + (p - 1) / 2 + (hpDD P N p s k0 k1).toNat))) (P.b N) ≤
      min (J * p + (hpEta P N p s - hpElo P N p s)) (P.L N - 1)

/-- Number of blocks. -/
def hpK (k0 k1 : ℤ) : ℕ := (k1 - k0 + 1).toNat

/-- Applicability of Theorem H' (all the inequalities used). -/
def hpOK (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : Prop :=
  p ≤ P.q N + (P.h N + (p - 1) / 2) ∧ P.h N + (p - 1) / 2 < p ∧
    s * p + 1 ≤ P.H N ∧ 0 ≤ hpDD P N p s k0 k1 ∧ hpElo P N p s < hpD P N p s k0 k1 ∧
    k0 ≤ k1

instance (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : Decidable (hpOK P N p s k0 k1) := by
  unfold hpOK; infer_instance

/-- **Theorem H', integer value.** -/
def hpVal (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : ℕ :=
  if hpOK P N p s k0 k1 then
    min (hpK k0 k1) (hpK k0 k1 + 1 - (hpJJ P N p s k0 k1).card) *
      (hpD P N p s k0 k1 - hpElo P N p s)
  else 0

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem hVirt_zero {K D : ℕ} (k0 jst : ℤ) (hp2 : p ≠ 2) (hj1 : 1 ≤ jst)
    (hjg : -(P.g N : ℤ) - k0 * p ≤ jst)
    (hjn : (k0 + K) * p - jst ≤ (P.n N : ℤ) - 1 - P.g N)
    (hD : (D : ℤ) ≤ hh p - jst + 1) : hVirt P N p K D k0 = 0 := by
  have hpe := p_eq_hh hp2
  unfold hVirt hBad
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro tk _
  obtain ⟨t, k⟩ := tk
  have ht := t.isLt
  have hk := k.isLt
  have hp1 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) * p := by positivity
  have hk1 : (((k : ℕ) : ℤ) + 1) * p ≤ (K : ℤ) * p :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hp1.le
  have hc : cen p K k0 k = k0 * p + ((k : ℕ) : ℤ) * p := by unfold cen; ring
  have hKe : (k0 + K) * (p : ℤ) = k0 * p + (K : ℤ) * p := by ring
  simp only [not_not, HGood, InRange, hlo, hhi, hc]
  have ht' : ((t : ℕ) : ℤ) + 1 ≤ D := by exact_mod_cast ht
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **H' is a nullity lower bound.** -/
theorem hpVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s : ℕ) (k0 k1 : ℤ) : hpVal P N p s k0 k1 ≤ nullity P N p := by
  classical
  unfold hpVal
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  obtain ⟨hq, hv, hs, hdd, hel, hk⟩ := hc
  have hjs : 1 ≤ hpJstar P N p k0 k1 := le_max_left _ _
  have hjs2 : -(P.g N : ℤ) - k0 * p ≤ hpJstar P N p k0 k1 :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hjs3 : (k1 + 1) * (p : ℤ) - ((P.n N : ℤ) - 1 - P.g N) ≤ hpJstar P N p k0 k1 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hdd1 : hpDD P N p s k0 k1 ≤ hh p - hpJstar P N p k0 k1 := min_le_left _ _
  have hdd2 : hpDD P N p s k0 k1 ≤ (hpEta P N p s : ℤ) - P.h N - hh p := min_le_right _ _
  have hhh : hh p = (((p - 1) / 2 : ℕ) : ℤ) := rfl
  have hDe : hpD P N p s k0 k1 = (hpDD P N p s k0 k1).toNat + 1 := rfl
  have hD' : ((hpD P N p s k0 k1 : ℕ) : ℤ) = hpDD P N p s k0 k1 + 1 := by
    rw [hDe]; push_cast; rw [Int.toNat_of_nonneg hdd]
  have hKe : ((hpK k0 k1 : ℕ) : ℤ) = k1 - k0 + 1 := by
    unfold hpK; rw [Int.toNat_of_nonneg (by omega)]
  have hDhp : hpD P N p s k0 k1 ≤ (p - 1) / 2 := by
    have : (hpD P N p s k0 k1 : ℤ) ≤ hh p := by omega
    omega
  have hvirt : hVirt P N p (hpK k0 k1) (hpD P N p s k0 k1) k0 = 0 := by
    refine hVirt_zero k0 (hpJstar P N p k0 k1) hp2 hjs hjs2 ?_ (by omega)
    have : ((k0 + (hpK k0 k1 : ℕ) : ℤ)) = k1 + 1 := by rw [hKe]; ring
    rw [this]; exact sub_le_comm.mp hjs3
  have hD1 : P.h N + (p - 1) / 2 + hpD P N p s k0 k1 ≤ hpEta P N p s + 1 := by
    have : ((P.h N + (p - 1) / 2 + hpD P N p s k0 k1 : ℕ) : ℤ) ≤ (hpEta P N p s : ℤ) + 1 := by
      push_cast; rw [hD']; omega
    exact_mod_cast this
  have hdD : (hpDD P N p s k0 k1).toNat + 1 = hpD P N p s k0 k1 := rfl
  have hmain : ∀ J0 : ℕ, (hpD P N p s k0 k1 - hpElo P N p s) *
      (hpK k0 k1 - ((hpJJ P N p s k0 k1).erase J0).card) -
        hVirt P N p (hpK k0 k1) (hpD P N p s k0 k1) k0 ≤ nullity P N p := fun J0 =>
    hPrime_le_nullity hP hN hp2 hH k0 hDhp (hpJJ P N p s k0 k1) J0 hv hq hs
      (by unfold hpEta at *; omega) (by unfold hpElo hpEta at *; omega)
      (fun j h1 h2 h3 h4 => by
        unfold hpJJ
        rw [Finset.mem_filter, Finset.mem_range]
        have hL : j / p ≤ P.L N / p := Nat.div_le_div_right h2.le
        have hjd := Nat.div_add_mod j p
        have hp0 : 0 < p := (Fact.out : p.Prime).pos
        refine ⟨by omega, ?_⟩
        have e1 : (hpDD P N p s k0 k1).toNat + 1 = hpD P N p s k0 k1 := rfl
        have e2 : j / p * p + j % p = j := by rw [mul_comm]; exact hjd
        simp only [max_le_iff, le_min_iff]
        unfold hpElo hpEta at *
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega)
  rw [hvirt] at hmain
  by_cases hne : (hpJJ P N p s k0 k1).Nonempty
  · obtain ⟨J0, hJ0⟩ := hne
    have h1 := hmain J0
    have hcard := Finset.card_erase_of_mem hJ0
    have hpos : 1 ≤ (hpJJ P N p s k0 k1).card := Finset.card_pos.mpr ⟨J0, hJ0⟩
    have : min (hpK k0 k1) (hpK k0 k1 + 1 - (hpJJ P N p s k0 k1).card) =
        hpK k0 k1 - ((hpJJ P N p s k0 k1).card - 1) := by omega
    rw [this, mul_comm]
    rw [hcard] at h1
    simpa using h1
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 := hmain 0
    rw [hne] at h1 ⊢
    simp only [Finset.erase_empty, Finset.card_empty, Nat.sub_zero, Nat.sub_zero] at h1 ⊢
    have : min (hpK k0 k1) (hpK k0 k1 + 1) = hpK k0 k1 := by omega
    rw [this, mul_comm]
    simpa using h1

#print axioms hpVal_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Slots
