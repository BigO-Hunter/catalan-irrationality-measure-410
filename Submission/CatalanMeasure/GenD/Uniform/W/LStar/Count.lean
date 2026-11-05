module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Theorem
@[expose] public section
set_option Elab.async false

/-!
# Counting lemmas for Theorem L* (lane G6c)

* `sum_jCard_le`: `Σ_{ℓ<p} |jSet ℓ| ≤ L - b`;
* `jCard_pos`: every residue has a digit when `p ≤ L - b`;
* `lstarKap_ge`: if `gg ℓ + lrank ℓ + 1 ≤ |jSet ℓ|` for all `ℓ < p`, then
  `Σ_{ℓ<p} gg ℓ + p ≤ lstarKap + q` (for `p ≤ q`);
* `gap_ge`: the per-residue inequality from explicit linear data.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ}

theorem mod_of {J ℓ p : ℕ} (hℓ : ℓ < p) : (J * p + ℓ) % p = ℓ := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hℓ]

theorem div_of {J ℓ p : ℕ} (hp : 0 < p) (hℓ : ℓ < p) : (J * p + ℓ) / p = J := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hℓ, zero_add]

theorem sum_jCard_le (hp : 0 < p) :
    ∑ ℓ ∈ Finset.range p, (jSet P N p ℓ).card ≤ P.L N - P.b N := by
  classical
  rw [← Finset.card_sigma]
  have : ((Finset.range p).sigma fun ℓ => jSet P N p ℓ).card ≤ (Finset.Ico (P.b N) (P.L N)).card := by
    refine Finset.card_le_card_of_injOn (fun x => x.2 * p + x.1) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · rw [Finset.mem_coe, Finset.mem_sigma] at hx
      rw [Finset.mem_coe, Finset.mem_Ico]
      have := (mem_jSet hp).mp hx.2
      omega
    · rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hx hy
      have h1 := (mem_jSet hp).mp hx.2
      have h2 := (mem_jSet hp).mp hy.2
      have hxy' : x.2 * p + x.1 = y.2 * p + y.1 := hxy
      have e1 : x.1 = y.1 := by
        have := congrArg (· % p) hxy'
        simpa [mod_of hx.1, mod_of hy.1] using this
      have e2 : x.2 = y.2 := by
        have := congrArg (· / p) hxy'
        simpa [div_of hp hx.1, div_of hp hy.1] using this
      exact Sigma.ext e1 (heq_of_eq e2)
  simpa using this

theorem jCard_pos (hp : 0 < p) (hLb : p ≤ P.L N - P.b N) {ℓ : ℕ} (hℓ : ℓ < p) :
    1 ≤ (jSet P N p ℓ).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  refine ⟨(P.b N + p - 1 - ℓ) / p, (mem_jSet hp).mpr ?_⟩
  have h1 := Nat.div_add_mod (P.b N + p - 1 - ℓ) p
  have h2 := Nat.mod_lt (P.b N + p - 1 - ℓ) hp
  have h3 : (P.b N + p - 1 - ℓ) / p * p = p * ((P.b N + p - 1 - ℓ) / p) := Nat.mul_comm _ _
  omega

theorem lrank_le_jCard (P : Parameters) (N p ℓ : ℕ) : lrank P N p ℓ ≤ (jSet P N p ℓ).card - 1 := by
  classical
  unfold lrank
  split_ifs
  · exact min_le_right _ _
  · exact le_refl _

/-- **From residue gaps to a bound on `lstarKap`.** -/
theorem lstarKap_ge (hp : 0 < p) (hLb : p ≤ P.L N - P.b N) (hpq : p ≤ P.q N) (gg : ℕ → ℕ)
    (h : ∀ ℓ < p, gg ℓ + lrank P N p ℓ + 1 ≤ (jSet P N p ℓ).card) :
    ∑ ℓ ∈ Finset.range p, gg ℓ + p ≤ lstarKap P N p + P.q N := by
  have hs := sum_jCard_le (P := P) (N := N) hp
  have h1 : ∑ ℓ ∈ Finset.range p, (gg ℓ + lrank P N p ℓ + 1) ≤
      ∑ ℓ ∈ Finset.range p, (jSet P N p ℓ).card :=
    Finset.sum_le_sum fun ℓ hℓ => h ℓ (Finset.mem_range.mp hℓ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one] at h1
  have hL : P.L N = P.n N + P.b N + P.q N := rfl
  unfold lstarKap
  omega

/-- The per-residue inequality from explicit linear data.  Digits `u2..u1`, blocks `u4..u3`;
here `e0 = H - 1 - ℓ - m p`, `D = p - 1 - e0 + (h - p)`. -/
theorem gap_ge (P : Parameters) (N p ℓ : ℕ) (hp : 0 < p) (hℓ : ℓ < p) (m : ℕ)
    (u1 u2 : ℕ) (u3 u4 : ℤ) (g0 : ℕ)
    (hm1 : m * p + ℓ + 1 ≤ P.H N) (hm2 : P.H N ≤ m * p + p + ℓ)
    (hadm1 : p ≤ P.h N)
    (hadm2 : (P.h N - p) + (p - 1) / 2 + m * p + ℓ + 1 ≤ P.H N)
    (hC1 : u1 * p + ℓ + 1 ≤ P.L N) (hC2 : P.b N ≤ u2 * p + ℓ) (h12 : u2 ≤ u1)
    (hC3 : (P.n N : ℤ) - P.g N - 1 +
      ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p)) < (u3 + 1) * p)
    (hC4 : (P.g N : ℤ) +
      ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p)) < (1 - u4) * p)
    (hu : u4 ≤ u3 + 1) (hg : (g0 : ℤ) + u3 + 1 ≤ u1 - u2 + u4) :
    g0 + lrank P N p ℓ + 1 ≤ (jSet P N p ℓ).card := by
  classical
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hres : idxRes (P.H N) p ℓ = P.H N - 1 - ℓ - m * p := by
    unfold idxRes
    have e : (P.H N : ℤ) - 1 - ℓ = ((P.H N : ℤ) - 1 - ℓ - m * p) + (m : ℤ) * p := by ring
    have h1 : (0 : ℤ) ≤ (P.H N : ℤ) - 1 - ℓ - m * p := by
      have : ((m * p + ℓ + 1 : ℕ) : ℤ) ≤ (P.H N : ℤ) := by exact_mod_cast hm1
      push_cast at this; linarith
    have h2 : (P.H N : ℤ) - 1 - ℓ - m * p < p := by
      have : (P.H N : ℤ) ≤ ((m * p + p + ℓ : ℕ) : ℤ) := by exact_mod_cast hm2
      push_cast at this; linarith
    have : ((P.H N : ℤ) - 1 - ℓ) % p = (P.H N : ℤ) - 1 - ℓ - m * p := by
      conv_lhs => rw [e]
      rw [Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt h1 h2
    rw [this]
    omega
  have hadm : lAdm P N p ℓ := by
    refine ⟨hadm1, ?_⟩
    rw [hres]; omega
  have hJ : u1 - u2 + 1 ≤ (jSet P N p ℓ).card := by
    have hsub : Finset.Icc u2 u1 ⊆ jSet P N p ℓ := by
      intro J hJ
      rw [Finset.mem_Icc] at hJ
      rw [mem_jSet hp]
      have a1 : u2 * p ≤ J * p := Nat.mul_le_mul_right p hJ.1
      have a2 : J * p ≤ u1 * p := Nat.mul_le_mul_right p hJ.2
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hN : (nvSet P N p ℓ).card ≤ (u3 + 1 - u4).toNat := by
    have hD : ((lD P N p ℓ : ℕ) : ℤ) =
        (p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p) := by
      unfold lD
      rw [hres]
      have : P.H N - 1 - ℓ - m * p + 1 ≤ p := by omega
      omega
    have hsub : nvSet P N p ℓ ⊆ Finset.Icc u4 u3 := by
      intro k hk
      unfold nvSet at hk
      rw [Finset.mem_Icc] at hk ⊢
      rw [hD] at hk
      constructor
      · have h1 := Int.ediv_lt_of_lt_mul hpz (by linarith [hC4] :
          (P.g N : ℤ) + ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p)) <
            (1 - u4) * p)
        linarith [hk.1]
      · have h1 := Int.ediv_lt_of_lt_mul hpz (by linarith [hC3] :
          (P.n N : ℤ) - P.g N - 1 +
            ((p : ℤ) - 1 - ((P.H N : ℤ) - 1 - ℓ - m * p) + ((P.h N : ℤ) - p)) < (u3 + 1) * p)
        linarith [hk.2]
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    exact this
  unfold lrank
  rw [if_pos hadm]
  have := min_le_left (nvSet P N p ℓ).card ((jSet P N p ℓ).card - 1)
  omega

end
end CatalanMeasure.GenD.Uniform.W.LStar
