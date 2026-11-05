module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Core
@[expose] public section
set_option Elab.async false

/-!
# J-flat valuation lemma

If `(X-1)^v ∣ W` over `F_p` (`v < p`) and the coefficients of `W` lie in the window `(η-p, η]`,
then the residue sequence `ℓ ↦ W[η - ℓ]` (`ℓ ∈ F_p`, zero for `ℓ > η`) is a polynomial function of
degree `< p - v` (`jflat_poly`).  This is the direction of the valuation equivalence used by
`w_jflat`.

Steps: (A) `sum_coeff_pow_eq_zero`: `Σ_i W_i i^k = 0` for `k < v`;
(B) `poly_of_moments`: moments `Σ_m f(m) m^k = 0` for `k < v` give a polynomial of degree `< p - v`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Polynomial
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem pow_succ_sub_pow (k : ℕ) (x : ZMod p) :
    (x + 1) ^ k - x ^ k = ∑ m ∈ Finset.range k, (k.choose m : ZMod p) * x ^ m := by
  have h := add_pow x 1 k
  rw [Finset.sum_range_succ] at h
  simp only [one_pow, mul_one, Nat.sub_self, Nat.choose_self, Nat.cast_one] at h
  rw [h]
  simp only [add_sub_cancel_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- (A) Moments of a coefficient sequence divisible by `(X-1)^v`. -/
theorem sum_coeff_pow_eq_zero (v : ℕ) : ∀ (k : ℕ), k < v → ∀ (W : (ZMod p)[X]) (N : ℕ),
    W.natDegree < N → ((X - 1) ^ v : (ZMod p)[X]) ∣ W →
      ∑ i ∈ Finset.range N, W.coeff i * (i : ZMod p) ^ k = 0 := by
  induction v with
  | zero => intro k hk; omega
  | succ v ih =>
    intro k hk W N hN hdvd
    obtain ⟨R, hR⟩ := hdvd
    set Q : (ZMod p)[X] := (X - 1) ^ v * R with hQ
    have hWQ : W = Q * X - Q := by rw [hR, hQ]; ring
    have hdivQ : ((X - 1) ^ v : (ZMod p)[X]) ∣ Q := ⟨R, rfl⟩
    have hWeq : W = (X - 1) * Q := by rw [hWQ]; ring
    by_cases hQ0 : Q = 0
    · have hW0 : W = 0 := by rw [hWeq, hQ0]; ring
      simp [hW0]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hQN : Q.natDegree < N' := by
      have hmon : (X - 1 : (ZMod p)[X]).Monic := monic_X_sub_C 1
      have := hmon.natDegree_mul' hQ0
      rw [← hWeq] at this
      have h1 : (X - 1 : (ZMod p)[X]).natDegree = 1 := natDegree_X_sub_C 1
      omega
    have hQcoeff : Q.coeff N' = 0 := coeff_eq_zero_of_natDegree_lt hQN
    have s1 : ∑ i ∈ Finset.range (N' + 1), (Q * X).coeff i * (i : ZMod p) ^ k =
        ∑ i ∈ Finset.range N', Q.coeff i * ((i : ZMod p) + 1) ^ k := by
      rw [Finset.sum_range_succ']
      simp [coeff_mul_X, coeff_mul_X_zero]
    have s2 : ∑ i ∈ Finset.range (N' + 1), Q.coeff i * (i : ZMod p) ^ k =
        ∑ i ∈ Finset.range N', Q.coeff i * (i : ZMod p) ^ k := by
      rw [Finset.sum_range_succ, hQcoeff, zero_mul, add_zero]
    have e1 : ∑ i ∈ Finset.range (N' + 1), W.coeff i * (i : ZMod p) ^ k =
        ∑ i ∈ Finset.range N', Q.coeff i * (((i : ZMod p) + 1) ^ k - (i : ZMod p) ^ k) := by
      rw [hWQ]
      simp only [coeff_sub, sub_mul, Finset.sum_sub_distrib]
      rw [s1, s2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1]
    simp_rw [pow_succ_sub_pow, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk := Finset.mem_range.mp hm
    have := ih m (by omega) Q N' hQN hdivQ
    calc ∑ i ∈ Finset.range N', Q.coeff i * ((k.choose m : ZMod p) * (i : ZMod p) ^ m)
        = (k.choose m : ZMod p) * ∑ i ∈ Finset.range N', Q.coeff i * (i : ZMod p) ^ m := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, mul_zero]

/-- (B) A function on `{0,…,p-1}` with vanishing moments `Σ f(m) m^k`, `k < v < p`, is a
polynomial function of degree `< p - v`. -/
theorem poly_of_moments (v : ℕ) (hv : v < p) (f : ℕ → ZMod p)
    (hmom : ∀ k, k < v → ∑ m ∈ Finset.range p, f m * (m : ZMod p) ^ k = 0) :
    ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ x : ZMod p, G.eval x = f x.val := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hp1' : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).one_lt; omega
  refine ⟨∑ m ∈ Finset.range p, C (f m) * (1 - (X - C (m : ZMod p)) ^ (p - 1)), ?_, ?_⟩
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro i hi
    have hi' : p - v ≤ i := by exact_mod_cast hi
    rw [finset_sum_coeff]
    have hcoef : ∀ m, (C (f m) * (1 - (X - C (m : ZMod p)) ^ (p - 1))).coeff i =
        - (f m * ((-(m : ZMod p)) ^ (p - 1 - i) * ((p - 1).choose i : ZMod p))) := by
      intro m
      have hi0 : i ≠ 0 := by omega
      have hx : (X - C (m : ZMod p) : (ZMod p)[X]) = X + C (-(m : ZMod p)) := by rw [C_neg]; ring
      have h1 : (1 : (ZMod p)[X]).coeff i = 0 := by rw [coeff_one]; simp [hi0]
      rw [coeff_C_mul, coeff_sub, hx, coeff_X_add_C_pow, h1]
      ring
    simp_rw [hcoef]
    rw [Finset.sum_neg_distrib, neg_eq_zero]
    by_cases hip : i ≤ p - 1
    · have hk : p - 1 - i < v := by omega
      have := hmom (p - 1 - i) hk
      calc ∑ m ∈ Finset.range p, f m * ((-(m : ZMod p)) ^ (p - 1 - i) * ((p - 1).choose i : ZMod p))
          = ((-1) ^ (p - 1 - i) * ((p - 1).choose i : ZMod p)) *
            ∑ m ∈ Finset.range p, f m * (m : ZMod p) ^ (p - 1 - i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [neg_pow]; ring
        _ = 0 := by rw [this, mul_zero]
    · have : (p - 1).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
  · intro x
    rw [eval_finset_sum]
    rw [Finset.sum_eq_single x.val]
    · simp only [eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X]
      rw [ZMod.natCast_zmod_val, sub_self, zero_pow hp1', sub_zero, mul_one]
    · intro m hm hne
      simp only [eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X]
      have hx : x - (m : ZMod p) ≠ 0 := by
        intro h
        apply hne
        have h2 : (m : ZMod p) = x := (sub_eq_zero.mp h).symm
        have hm' := Finset.mem_range.mp hm
        rw [← h2, ZMod.val_natCast, Nat.mod_eq_of_lt hm']
      rw [ZMod.pow_card_sub_one_eq_one hx, sub_self, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (ZMod.val_lt x)) h

/-- **J-flat valuation lemma.** -/
theorem jflat_poly {v : ℕ} (hv : v < p) (W : (ZMod p)[X]) (hdvd : ((X - 1) ^ v : (ZMod p)[X]) ∣ W)
    (eta : ℕ) (hhi : W.natDegree ≤ eta) (hlo : ∀ i, i + p ≤ eta → W.coeff i = 0) :
    ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ ℓ : ZMod p, (if ℓ.val ≤ eta then W.coeff (eta - ℓ.val) else 0) = G.eval ℓ := by
  set fN : ℕ → ZMod p := fun m => if m ≤ eta then W.coeff (eta - m) else 0 with hfN
  have hfp : ∀ m, p ≤ m → fN m = 0 := by
    intro m hm
    simp only [hfN]
    split_ifs with h
    · exact hlo _ (by omega)
    · rfl
  have hfe : ∀ m, eta < m → fN m = 0 := fun m hm => by simp [hfN, not_le.mpr hm]
  have hmom : ∀ k, k < v → ∑ m ∈ Finset.range p, fN m * (m : ZMod p) ^ k = 0 := by
    intro k hk
    have hA : ∀ j, j < v → ∑ i ∈ Finset.range (eta + 1), W.coeff i * (i : ZMod p) ^ j = 0 :=
      fun j hj => sum_coeff_pow_eq_zero v j hj W (eta + 1) (by omega) hdvd
    have h1 : ∑ i ∈ Finset.range (eta + 1), W.coeff i * ((eta : ZMod p) - i) ^ k = 0 := by
      have e : ∀ i : ℕ, W.coeff i * ((eta : ZMod p) - i) ^ k =
          ∑ j ∈ Finset.range (k + 1), ((-1) ^ j * (eta : ZMod p) ^ (k - j) * (k.choose j : ZMod p)) *
            (W.coeff i * (i : ZMod p) ^ j) := by
        intro i
        rw [sub_eq_neg_add, add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [neg_pow]; ring
      simp_rw [e]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [← Finset.mul_sum, hA j (by have := Finset.mem_range.mp hj; omega), mul_zero]
    have h2 : ∑ i ∈ Finset.range (eta + 1), W.coeff i * ((eta : ZMod p) - i) ^ k =
        ∑ m ∈ Finset.range (eta + 1), fN m * (m : ZMod p) ^ k := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.mp hm
      have e1 : eta + 1 - 1 - m = eta - m := by omega
      have hc : (eta : ZMod p) - ((eta - m : ℕ) : ZMod p) = m := by
        rw [Nat.cast_sub (by omega : m ≤ eta)]; ring
      rw [e1, hc]
      simp only [hfN, if_pos (by omega : m ≤ eta)]
    have h3 : ∑ m ∈ Finset.range p, fN m * (m : ZMod p) ^ k =
        ∑ m ∈ Finset.range (eta + 1), fN m * (m : ZMod p) ^ k := by
      have a : ∑ m ∈ Finset.range p, fN m * (m : ZMod p) ^ k =
          ∑ m ∈ Finset.range (p + eta + 1), fN m * (m : ZMod p) ^ k := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
        rw [hfp m (by have := Finset.mem_range.not.mp hm; omega), zero_mul]
      have b : ∑ m ∈ Finset.range (eta + 1), fN m * (m : ZMod p) ^ k =
          ∑ m ∈ Finset.range (p + eta + 1), fN m * (m : ZMod p) ^ k := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
        rw [hfe m (by have := Finset.mem_range.not.mp hm; omega), zero_mul]
      rw [a, b]
    rw [h3, ← h2, h1]
  obtain ⟨G, hG, hGe⟩ := poly_of_moments v hv fN hmom
  exact ⟨G, hG, fun ℓ => by rw [hGe]⟩

#print axioms jflat_poly
end
end CatalanMeasure.GenD.Uniform.W.Slots
