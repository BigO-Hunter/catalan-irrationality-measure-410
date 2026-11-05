module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Count
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.JFlat
@[expose] public section
set_option Elab.async false

/-!
# J-flat kill for slot systems (the H' mechanism)

Let all slot polynomials be divisible by `(X-1)^v` and of degree `≤ η`, where
`η = H - 1 - s p` is the top of a single window `s`, and let the jets `w_e`, `e < e0`
(`η + 1 ≤ e0 + p`) vanish.  Then the slot response of a datum is the single source covector

    resp (J, ℓ) x = [ℓ ≤ η] ψ(J, s)(w_{η-ℓ}),

and, when the covectors `ψ(J, s)`, `J ∈ JJ`, agree on the profile space `V` (`= γ`), the response
is a polynomial function of `j mod p` of degree `< p - v` (`jflat_poly`): cost `(p - q - v)_+`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

namespace SlotSystem
variable (S : SlotSystem P N p)

theorem wv_eq_zero_of_gt {eta : ℕ} (hdeg : ∀ d, (S.lam d).natDegree ≤ eta)
    (x : Fin S.D → Fin S.K → ZMod p) {e : ℕ} (he : eta < e) : wv S.lam x e = 0 := by
  unfold wv
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg d) he), zero_smul]

/-- Single-window response. -/
theorem resp_flat {eta s e0 : ℕ}
    (he0 : eta + 1 ≤ e0 + p) (heta : (P.H N : ℤ) - 1 - eta = s * p) (J ell : ℕ) (hell : ell < p)
    (x : Fin S.D → Fin S.K → ZMod p) (hhi : ∀ e, eta < e → wv S.lam x e = 0)
    (hjet : ∀ e < e0, wv S.lam x e = 0) :
    S.resp J ell x = if ell ≤ eta then S.prof.psi (P.H N) J s (wv S.lam x (eta - ell)) else 0 := by
  have hp1 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hterm : ∀ e : ℕ, (if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e then
      S.prof.psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p) (wv S.lam x e) else 0) =
      if e = eta - ell ∧ ell ≤ eta then S.prof.psi (P.H N) J s (wv S.lam x e) else 0 := by
    intro e
    by_cases hc : e = eta - ell ∧ ell ≤ eta
    · obtain ⟨rfl, hl⟩ := hc
      have : (P.H N : ℤ) - 1 - ell - ((eta - ell : ℕ) : ℤ) = s * p := by
        rw [Nat.cast_sub hl]; linarith
      rw [if_pos (by rw [this]; exact dvd_mul_left _ _), if_pos ⟨rfl, hl⟩, this,
        Int.mul_ediv_cancel _ hp1.ne']
    · rw [if_neg hc]
      split_ifs with hd
      · by_cases hw : wv S.lam x e = 0
        · rw [hw, map_zero]
        · exfalso
          have h1 : e0 ≤ e := by
            by_contra h; exact hw (hjet e (not_le.mp h))
          have h2 : e ≤ eta := by
            by_contra h; exact hw (hhi e (not_le.mp h))
          obtain ⟨a, ha⟩ := hd
          have h5 : (((eta - e : ℕ) : ℤ) - ell) = (a - s) * p := by
            rw [Nat.cast_sub h2]; linarith
          have h6 := Thin.no_mult (a - s) (((eta - e : ℕ) : ℤ) - ell) hp1
            (by omega) (by omega) h5.symm
          apply hc
          refine ⟨by omega, by omega⟩
      · rfl
  unfold resp
  simp_rw [hterm]
  by_cases hl : ell ≤ eta
  · simp only [hl, and_true]
    rw [Finset.sum_ite_eq' (Finset.range S.emax) (eta - ell)
      (fun e => S.prof.psi (P.H N) J s (wv S.lam x e))]
    split_ifs with hm
    · rfl
    · have : S.emax ≤ eta - ell := by
        have := Finset.mem_range.not.mp hm; omega
      have hz : wv S.lam x (eta - ell) = 0 := by
        unfold wv
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (S.deg d) this), zero_smul]
      rw [hz, map_zero]
  · simp [hl]

end SlotSystem

end
end CatalanMeasure.GenD.Uniform.W.Slots
