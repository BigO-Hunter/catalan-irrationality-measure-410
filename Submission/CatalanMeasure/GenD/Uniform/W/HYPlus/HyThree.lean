module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HmProf
@[expose] public section
set_option Elab.async false

/-!
# The residue sum has only three terms

For `p ≤ η < 2p`, `emax ≤ η + p`, `ℓ < p` the terms `e < emax` with `p ∣ H-1-ℓ-e`, `H-1 = η + s p`, are
`e = η-ℓ` (window `s`), `e = η-ℓ-p` (window `s+1`, only if `p ≤ η-ℓ`) and `e = η-ℓ+p` (window `s-1`).
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
noncomputable section

theorem dvd_three (p η s ℓ e emax : ℕ) (hp : 0 < p) (hℓ : ℓ < p) (hpη : p ≤ η) (hη2 : η < 2 * p)
    (hem : emax ≤ η + p) (he : e < emax) (Hm1 : ℤ) (hH : Hm1 = η + s * p)
    (hd : (p : ℤ) ∣ Hm1 - ℓ - e) :
    e = η - ℓ ∨ e = η - ℓ + p ∨ (p ≤ η - ℓ ∧ e = η - ℓ - p) := by
  obtain ⟨c, hc⟩ := hd
  rw [hH] at hc
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 : (η : ℤ) - ℓ - e = p * (c - s) := by linarith
  have hlo : (-(2 : ℤ) * p) < p * (c - s) := by
    rw [← h1]; have : (e : ℤ) < η + p := by exact_mod_cast (by omega : e < η + p)
    have : (ℓ : ℤ) < p := by exact_mod_cast hℓ
    linarith
  have hhi : p * (c - s) < (2 : ℤ) * p := by
    rw [← h1]; have : (η : ℤ) < 2 * p := by exact_mod_cast hη2
    have : (0 : ℤ) ≤ ℓ := by positivity
    have : (0 : ℤ) ≤ e := by positivity
    linarith
  have d1 : -2 < c - s := by nlinarith
  have d2 : c - s < 2 := by nlinarith
  have : c - s = -1 ∨ c - s = 0 ∨ c - s = 1 := by omega
  rcases this with h | h | h
  · right; left
    rw [h] at h1
    omega
  · left
    rw [h] at h1
    omega
  · right; right
    rw [h] at h1
    refine ⟨by omega, by omega⟩

theorem resp_sum_three {F : Type*} [AddCommMonoid F] (p η s ℓ emax : ℕ) (hp : 0 < p) (hℓ : ℓ < p)
    (hpη : p ≤ η) (hη2 : η < 2 * p) (hem : emax ≤ η + p) (Hm1 : ℤ) (hH : Hm1 = η + s * p)
    (f : ℕ → ℤ → F) (hf0 : ∀ e σ, emax ≤ e → f e σ = 0) :
    (∑ e ∈ Finset.range emax, if (p : ℤ) ∣ Hm1 - ℓ - e then f e ((Hm1 - ℓ - e) / p) else 0) =
      f (η - ℓ) (s : ℤ) + (if p ≤ η - ℓ then f (η - ℓ - p) ((s : ℤ) + 1) else 0) +
        f (η - ℓ + p) ((s : ℤ) - 1) := by
  classical
  have hz : ∀ e σ, (if e ∈ Finset.range emax then f e σ else 0) = f e σ := by
    intro e σ
    by_cases h : e ∈ Finset.range emax
    · rw [if_pos h]
    · rw [if_neg h, hf0 e σ (by simpa using h)]
  have key : ∀ e ∈ Finset.range emax,
      (if (p : ℤ) ∣ Hm1 - ℓ - e then f e ((Hm1 - ℓ - e) / p) else 0) =
        (if e = η - ℓ then f e (s : ℤ) else 0) +
        (if p ≤ η - ℓ ∧ e = η - ℓ - p then f e ((s : ℤ) + 1) else 0) +
        (if e = η - ℓ + p then f e ((s : ℤ) - 1) else 0) := by
    intro e he
    have he' := Finset.mem_range.mp he
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have hℓη : ℓ ≤ η := by omega
    by_cases h0 : e = η - ℓ
    · have hq : Hm1 - ℓ - e = s * p := by rw [hH]; omega
      rw [if_pos (by rw [hq]; exact dvd_mul_left _ _), if_pos h0,
        if_neg (by omega), if_neg (by omega), hq, Int.mul_ediv_cancel _ hp'.ne']
      simp
    · by_cases h2 : e = η - ℓ + p
      · have hq : Hm1 - ℓ - e = ((s : ℤ) - 1) * p := by
          have he2 : (e : ℤ) = η - ℓ + p := by omega
          rw [hH, he2]; ring
        rw [if_pos (by rw [hq]; exact dvd_mul_left _ _), if_neg h0, if_neg (by omega),
          if_pos h2, hq, Int.mul_ediv_cancel _ hp'.ne']
        simp
      · by_cases h1 : p ≤ η - ℓ ∧ e = η - ℓ - p
        · have hq : Hm1 - ℓ - e = ((s : ℤ) + 1) * p := by
            obtain ⟨a, b⟩ := h1
            have he2 : (e : ℤ) = η - ℓ - p := by omega
            rw [hH, he2]; ring
          rw [if_pos (by rw [hq]; exact dvd_mul_left _ _), if_neg h0, if_pos h1, if_neg h2,
            hq, Int.mul_ediv_cancel _ hp'.ne']
          simp
        · rw [if_neg h0, if_neg h1, if_neg h2, if_neg]
          · simp
          intro hd
          rcases dvd_three p η s ℓ e emax hp hℓ hpη hη2 hem he' Hm1 hH hd with h | h | h
          · exact h0 h
          · exact h2 h
          · exact h1 h
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' (Finset.range emax) (η - ℓ) (fun e => f e (s : ℤ)),
    Finset.sum_ite_eq' (Finset.range emax) (η - ℓ + p) (fun e => f e ((s : ℤ) - 1))]
  have h3 : (∑ e ∈ Finset.range emax, if p ≤ η - ℓ ∧ e = η - ℓ - p then f e ((s : ℤ) + 1) else 0) =
      if p ≤ η - ℓ then (if η - ℓ - p ∈ Finset.range emax then f (η - ℓ - p) ((s : ℤ) + 1) else 0) else 0 := by
    by_cases hc : p ≤ η - ℓ
    · simp only [hc, true_and, if_true]
      exact Finset.sum_ite_eq' _ _ _
    · simp [hc]
  rw [h3, hz, hz, hz]

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
