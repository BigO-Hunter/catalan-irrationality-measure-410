module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPrime
@[expose] public section
set_option Elab.async false

/-!
# Three-window folding is J-flat

For `f` with `(X-1)^v ∣ f`, `deg f < η + p`, `p ≤ η < 2p`, the folded coefficient
`ρ(ℓ) = f[η-ℓ] + [p+ℓ ≤ η] f[η-p-ℓ] + f[η+p-ℓ]` is a polynomial function of `ℓ` of degree `< p - v`.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The cofactor `T`: `W = f - (X^p-1) T`. -/
def foldT (p η : ℕ) (f : (ZMod p)[X]) : (ZMod p)[X] :=
  ∑ e ∈ Finset.range (η + 1),
    monomial e (if e < η - p + 1 then -f.coeff e else f.coeff (e + p))

theorem foldT_coeff (η : ℕ) (f : (ZMod p)[X]) (e : ℕ) :
    (foldT p η f).coeff e =
      if e ≤ η then (if e < η - p + 1 then -f.coeff e else f.coeff (e + p)) else 0 := by
  classical
  simp only [foldT, finset_sum_coeff, coeff_monomial]
  by_cases h : e ≤ η
  · rw [Finset.sum_eq_single e]
    · simp [h]
    · intro b _ hb; simp [hb]
    · intro hh; exact absurd (Finset.mem_range.mpr (by omega)) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => ?_
    have := Finset.mem_range.mp hb
    simp only [ite_eq_right_iff]
    intro hbe; omega

theorem foldW_coeff (f : (ZMod p)[X]) (η m : ℕ) :
    (f - (X ^ p - 1) * foldT p η f).coeff m =
      f.coeff m - ((if p ≤ m then (foldT p η f).coeff (m - p) else 0) - (foldT p η f).coeff m) := by
  rw [coeff_sub, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']

theorem fold3_poly {v η : ℕ} (hv : v < p) (hpη : p ≤ η) (hη2 : η < 2 * p) (f : (ZMod p)[X])
    (hdvd : ((X - 1) ^ v : (ZMod p)[X]) ∣ f) (hdeg : f.natDegree < η + p) :
    ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧ ∀ ℓ : ZMod p,
      f.coeff (η - ℓ.val) + (if p + ℓ.val ≤ η then f.coeff (η - p - ℓ.val) else 0) +
        f.coeff (η + p - ℓ.val) = G.eval ℓ := by
  have hfz : ∀ e, η + p ≤ e → f.coeff e = 0 := fun e he =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  set W := f - (X ^ p - 1) * foldT p η f with hW
  have hWdeg : W.natDegree ≤ η := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hW, foldW_coeff, foldT_coeff, foldT_coeff]
    rw [if_neg (by omega : ¬ m ≤ η)]
    by_cases hmp : m < η + p
    · rw [if_pos (by omega : p ≤ m), if_pos (by omega : m - p ≤ η),
        if_neg (by omega : ¬ m - p < η - p + 1), Nat.sub_add_cancel (by omega : p ≤ m)]
      ring
    · rw [hfz m (by omega), if_pos (by omega : p ≤ m)]
      by_cases hmm : m - p ≤ η
      · rw [if_pos hmm, if_neg (by omega : ¬ m - p < η - p + 1), hfz _ (by omega)]; ring
      · rw [if_neg hmm]; ring
  have hWlo : ∀ i, i + p ≤ η → W.coeff i = 0 := by
    intro i hi
    rw [hW, foldW_coeff, if_neg (by omega : ¬ p ≤ i), foldT_coeff, if_pos (by omega : i ≤ η),
      if_pos (by omega : i < η - p + 1)]
    ring
  have hWd : ((X - 1) ^ v : (ZMod p)[X]) ∣ W := by
    refine dvd_sub hdvd (dvd_mul_of_dvd_left ?_ _)
    rw [← sub_one_pow_prime]
    exact pow_dvd_pow _ hv.le
  obtain ⟨G, hG, hGe⟩ := jflat_poly hv W hWd η hWdeg hWlo
  refine ⟨G, hG, fun ℓ => ?_⟩
  rw [← hGe ℓ]
  have hlp : ℓ.val < p := ZMod.val_lt ℓ
  rw [if_pos (by omega : ℓ.val ≤ η), hW, foldW_coeff, foldT_coeff, foldT_coeff]
  rw [if_pos (by omega : η - ℓ.val ≤ η), if_neg (by omega : ¬ η - ℓ.val < η - p + 1)]
  by_cases hc : p + ℓ.val ≤ η
  · rw [if_pos hc, if_pos (by omega : p ≤ η - ℓ.val), if_pos (by omega : η - ℓ.val - p ≤ η),
      if_pos (by omega : η - ℓ.val - p < η - p + 1),
      show η - ℓ.val - p = η - p - ℓ.val by omega,
      show η - ℓ.val + p = η + p - ℓ.val by omega]
    ring
  · rw [if_neg hc, if_neg (by omega : ¬ p ≤ η - ℓ.val),
      show η - ℓ.val + p = η + p - ℓ.val by omega]
    ring

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
