module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Count
@[expose] public section
set_option Elab.async false

/-!
# Two-window response and the period count (Theorem P mechanism)

`resp_two`: if the profile `w_e` vanishes for `e > η` and for `e + 2p ≤ η`, the slot response is the
sum of the window-`s` and window-`s+1` covectors at `w_{η-ℓ}` and `w_{η-p-ℓ}`.

`period_nullity`: slot data `λ_i = (X^p - 1) P_i` with `P_i` supported in `[ilo, Pmax]`,
`Pmax ≤ η - p`, `η - 2p < ilo`, and profiles in a space `V` on which `ψ(J,s) = ψ(J,s+1)` for every
column that sees the support: the raw response vanishes, so `m · dim V ≤ ν`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

namespace SlotSystem
variable (S : SlotSystem P N p)

theorem wv_eq_zero_of_ge_emax (x : Fin S.D → Fin S.K → ZMod p) {e : ℕ} (he : S.emax ≤ e) :
    wv S.lam x e = 0 := by
  unfold wv
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (S.deg d) he), zero_smul]

/-- Two-window response. -/
theorem resp_two {eta s : ℕ} (heta : (P.H N : ℤ) - 1 - eta = s * p) (J ell : ℕ) (hell : ell < p)
    (x : Fin S.D → Fin S.K → ZMod p) (hhi : ∀ e, eta < e → wv S.lam x e = 0)
    (hlo : ∀ e, e + 2 * p ≤ eta → wv S.lam x e = 0) :
    S.resp J ell x =
      (if ell ≤ eta then S.prof.psi (P.H N) J s (wv S.lam x (eta - ell)) else 0) +
      (if p + ell ≤ eta then S.prof.psi (P.H N) J (s + 1) (wv S.lam x (eta - p - ell)) else 0) := by
  have hp1 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hterm : ∀ e : ℕ, (if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e then
      S.prof.psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p) (wv S.lam x e) else 0) =
      (if e = eta - ell ∧ ell ≤ eta then S.prof.psi (P.H N) J s (wv S.lam x e) else 0) +
      (if e = eta - p - ell ∧ p + ell ≤ eta then
        S.prof.psi (P.H N) J ((s + 1 : ℕ) : ℤ) (wv S.lam x e) else 0) := by
    intro e
    by_cases hc1 : e = eta - ell ∧ ell ≤ eta
    · obtain ⟨rfl, hl⟩ := hc1
      have h2 : ¬ (eta - ell = eta - p - ell ∧ p + ell ≤ eta) := by
        rintro ⟨h, h'⟩; omega
      have : (P.H N : ℤ) - 1 - ell - ((eta - ell : ℕ) : ℤ) = s * p := by
        rw [Nat.cast_sub hl]; linarith
      rw [if_pos (by rw [this]; exact dvd_mul_left _ _), if_pos ⟨rfl, hl⟩, if_neg h2, this,
        Int.mul_ediv_cancel _ hp1.ne', add_zero]
    by_cases hc2 : e = eta - p - ell ∧ p + ell ≤ eta
    · obtain ⟨rfl, hl⟩ := hc2
      have : (P.H N : ℤ) - 1 - ell - ((eta - p - ell : ℕ) : ℤ) = (s + 1 : ℕ) * p := by
        rw [show eta - p - ell = eta - (p + ell) by omega, Nat.cast_sub hl]; push_cast; linarith
      rw [if_pos (by rw [this]; exact dvd_mul_left _ _), if_neg hc1, if_pos ⟨rfl, hl⟩, this,
        Int.mul_ediv_cancel _ hp1.ne', zero_add]
    · rw [if_neg hc1, if_neg hc2, add_zero]
      split_ifs with hd
      · by_cases hw : wv S.lam x e = 0
        · rw [hw, map_zero]
        · exfalso
          have h2 : e ≤ eta := by
            by_contra h; exact hw (hhi e (not_le.mp h))
          have h1 : eta < e + 2 * p := by
            by_contra h; exact hw (hlo e (not_lt.mp h))
          obtain ⟨a, ha⟩ := hd
          have h5 : (((eta - e : ℕ) : ℤ) - ell) = (a - s) * p := by
            rw [Nat.cast_sub h2]; linarith
          have hlt1 : -1 < a - s := by
            by_contra h
            have : (a - s) * (p : ℤ) ≤ -1 * p := by
              apply mul_le_mul_of_nonneg_right _ hp1.le; omega
            omega
          have hlt2 : a - s < 2 := by
            by_contra h
            have : 2 * (p : ℤ) ≤ (a - s) * p := by
              apply mul_le_mul_of_nonneg_right _ hp1.le; omega
            omega
          have : a - s = 0 ∨ a - s = 1 := by omega
          rcases this with h | h
          · rw [h] at h5; apply hc1; refine ⟨by omega, by omega⟩
          · rw [h] at h5; apply hc2; refine ⟨by omega, by omega⟩
      · rfl
  unfold resp
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hl : ell ≤ eta
    · simp only [hl, and_true]
      rw [Finset.sum_ite_eq' (Finset.range S.emax) (eta - ell)
        (fun e => S.prof.psi (P.H N) J s (wv S.lam x e))]
      split_ifs with hm
      · rfl
      · rw [S.wv_eq_zero_of_ge_emax x (by have := Finset.mem_range.not.mp hm; omega), map_zero]
    · simp [hl]
  · by_cases hl : p + ell ≤ eta
    · simp only [hl, and_true]
      rw [Finset.sum_ite_eq' (Finset.range S.emax) (eta - p - ell)
        (fun e => S.prof.psi (P.H N) J ((s + 1 : ℕ) : ℤ) (wv S.lam x e))]
      split_ifs with hm
      · rfl
      · rw [S.wv_eq_zero_of_ge_emax x (by have := Finset.mem_range.not.mp hm; omega), map_zero]
    · simp [hl]

end SlotSystem

end
end CatalanMeasure.GenD.Uniform.W.Slots
