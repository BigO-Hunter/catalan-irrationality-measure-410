module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.TpRows
@[expose] public section
set_option Elab.async false

/-!
# T+ pairs as a slot system (period form)

For `h + (p-1)/2 ≥ p` one has `(X-1)^h (X²-1)^((p-1)/2) = (X^p - 1) · (X-1)^a (X+1)^((p-1)/2)`,
`a = h + (p-1)/2 - p`.  The T+ slot polynomial is therefore `lam d = 2 (X-1)^a (X+1)^((p-1)/2) T_d`
(degree `≤ h - 1 + d`, divisible by `(X-1)^a`), and the profile maps carry the factor `Y - 1`:

    Ty y = (X-1) Σ_k y_k U_{k0+k-1},   Gy y = (X-1) Σ_k y_k T_{k0+k}     (polynomials in `Y = X^p`).

This is the "difference form" `Φ(J,s-1;·) - Φ(J,s;·)` of Theorem MT (`proof4`), built into the
profile maps.  Offsets `d = 0, …, D-1` (`d = 0` is the single row `e_{c}` with weight `2`).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `U_{a+d-1} + U_{a-d-1} = 2 U_{a-1} T_d`. -/
theorem U_pair_sum (R : Type*) [CommRing R] (a d : ℤ) :
    Chebyshev.U R (a + d - 1) + Chebyshev.U R (a - d - 1) =
      2 * Chebyshev.U R (a - 1) * Chebyshev.T R d := by
  have h1 := chebyshev_U_add R a d
  have h2 := chebyshev_U_add R a (-d)
  rw [Chebyshev.T_neg, Chebyshev.U_neg_sub_one] at h2
  rw [show a - d - 1 = a + -d - 1 by ring, h1, h2]
  ring

/-- `T_{a+d} + T_{a-d} = 2 T_a T_d`. -/
theorem T_pair_sum (R : Type*) [CommRing R] (a d : ℤ) :
    Chebyshev.T R (a + d) + Chebyshev.T R (a - d) = 2 * Chebyshev.T R a * Chebyshev.T R d := by
  have h1 := chebyshev_T_add R a d
  have h2 := chebyshev_T_add R a (-d)
  rw [Chebyshev.T_neg, Chebyshev.U_neg_sub_one] at h2
  rw [show a - d = a + -d by ring, h1, h2]
  ring

/-- `(X-1)^h (X²-1)^((p-1)/2) = (X-1)^a (X+1)^((p-1)/2) (X^p - 1)` when `h + (p-1)/2 ≥ p`. -/
theorem period_factor (hph : p ≤ P.h N + (p - 1) / 2) :
    (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) =
      (X - 1) ^ (P.h N + (p - 1) / 2 - p) * (X + 1) ^ ((p - 1) / 2) * (X ^ p - 1) := by
  have e1 : (X ^ 2 - 1 : (ZMod p)[X]) = (X - 1) * (X + 1) := by ring
  have e2 : P.h N + (p - 1) / 2 = (P.h N + (p - 1) / 2 - p) + p := by omega
  have e3 : (X - 1 : (ZMod p)[X]) ^ (P.h N + (p - 1) / 2) =
      (X - 1) ^ (P.h N + (p - 1) / 2 - p) * (X ^ p - 1) := by
    conv_lhs => rw [e2, pow_add, sub_one_pow_prime]
  calc (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2)
      = (X - 1) ^ (P.h N + (p - 1) / 2) * (X + 1) ^ ((p - 1) / 2) := by
        rw [e1, mul_pow, pow_add]; ring
    _ = _ := by rw [e3]; ring

/-- The T+ slot polynomial. -/
def tpLam (P : Parameters) (N p : ℕ) (d : ℕ) : (ZMod p)[X] :=
  2 * (X - 1) ^ (P.h N + (p - 1) / 2 - p) * (X + 1) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (d : ℤ)

theorem tpLam_dvd (P : Parameters) (N p : ℕ) (d : ℕ) :
    ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ tpLam P N p d := by
  unfold tpLam
  exact ⟨2 * (X + 1) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (d : ℤ), by ring⟩

theorem tpLam_natDegree_le (hp2 : p ≠ 2) (d : ℕ) :
    (tpLam P N p d).natDegree ≤ (P.h N + (p - 1) / 2 - p) + (p - 1) / 2 + d := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold tpLam
  have a : (2 : (ZMod p)[X]).natDegree ≤ 0 := by compute_degree
  have b : ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]).natDegree ≤
      P.h N + (p - 1) / 2 - p := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    have := Nat.mul_le_mul_left (P.h N + (p - 1) / 2 - p) this
    simpa using this
  have c : ((X + 1) ^ ((p - 1) / 2) : (ZMod p)[X]).natDegree ≤ (p - 1) / 2 := by
    refine natDegree_pow_le.trans ?_
    have : (X + 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    have := Nat.mul_le_mul_left ((p - 1) / 2) this
    simpa using this
  have e : (Chebyshev.T (ZMod p) (d : ℤ)).natDegree ≤ d := by
    rw [Chebyshev.natDegree_T]; simp
  have h1 := natDegree_mul_le
    (p := (2 * (X - 1) ^ (P.h N + (p - 1) / 2 - p) * (X + 1) ^ ((p - 1) / 2) : (ZMod p)[X]))
    (q := Chebyshev.T (ZMod p) (d : ℤ))
  have h2 := natDegree_mul_le (p := (2 * (X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]))
    (q := (X + 1) ^ ((p - 1) / 2))
  have h3 := natDegree_mul_le (p := (2 : (ZMod p)[X])) (q := (X - 1) ^ (P.h N + (p - 1) / 2 - p))
  omega

/-- `y ↦ (X-1) Σ_k y_k U_{k0+k-1}`. -/
def tpTy (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  (LinearMap.mulLeft (ZMod p) (X - 1 : (ZMod p)[X])).comp (uyMap p K k0)

/-- `y ↦ (X-1) Σ_k y_k T_{k0+k}`. -/
def tpGy (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  (LinearMap.mulLeft (ZMod p) (X - 1 : (ZMod p)[X])).comp (tyMap p K k0)

theorem tpTy_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    tpTy p K k0 y = (X - 1) * ∑ k : Fin K, C (y k) * Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1) := by
  simp [tpTy, uyMap_apply, Finset.mul_sum]

theorem tpGy_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    tpGy p K k0 y = (X - 1) * ∑ k : Fin K, C (y k) * Chebyshev.T (ZMod p) (k0 + (k : ℕ)) := by
  simp [tpGy, tyMap_apply, Finset.mul_sum]

theorem tpU_term (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N *
        (Chebyshev.U (ZMod p) (κ * p + (d : ℤ) - 1) + Chebyshev.U (ZMod p) (κ * p - (d : ℤ) - 1)) =
      tpLam P N p d * ((X ^ p - 1) * (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) := by
  rw [U_pair_sum, U_block hp2 κ, tpLam]
  have hf := period_factor (P := P) (N := N) (p := p) hph
  linear_combination (2 * Chebyshev.T (ZMod p) (d : ℤ) *
    (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) * hf

theorem tpT_term (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + (d : ℤ)) + Chebyshev.T (ZMod p) (κ * p - (d : ℤ))) =
      tpLam P N p d * ((X ^ p - 1) * (Chebyshev.T (ZMod p) κ).comp (X ^ p)) := by
  rw [T_pair_sum, T_block hp2 κ, tpLam]
  have hf := period_factor (P := P) (N := N) (p := p) hph
  linear_combination (2 * Chebyshev.T (ZMod p) (d : ℤ) *
    (Chebyshev.T (ZMod p) κ).comp (X ^ p)) * hf

theorem intrinsicU_tpRows {K D : ℕ} (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ d k, ¬ TpGood P N p k0 d k → x d k = 0) :
    (X - 1) ^ P.h N * intrinsicU P N p (tpRows P N p K D k0 x) =
      ∑ d : Fin D, tpLam P N p (d : ℕ) * (tpTy p K k0 (x d)).comp (X ^ p) := by
  have h := sum_tpPairRows (P := P) (N := N) k0 x hx
    (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (tpRows P N p K D k0 x r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hR : (tpTy p K k0 (x d)).comp (X ^ p) =
      ∑ k : Fin K, C (x d k) * ((X ^ p - 1) *
        (Chebyshev.U (ZMod p) ((k0 : ℤ) + (k : ℕ) - 1)).comp (X ^ p)) := by
    rw [tpTy_apply, mul_comp, sub_comp, X_comp, one_comp, sum_comp', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comp, C_comp]; ring
  rw [hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := tpU_term (P := P) (N := N) hp2 hph ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  simp only [cen]
  linear_combination C (x d k) * e

theorem intrinsicT_tpRows {K D : ℕ} (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ d k, ¬ TpGood P N p k0 d k → x d k = 0) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p (tpRows P N p K D k0 x) =
      ∑ d : Fin D, tpLam P N p (d : ℕ) * (tpGy p K k0 (x d)).comp (X ^ p) := by
  have h := sum_tpPairRows (P := P) (N := N) k0 x hx
    (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (tpRows P N p K D k0 x r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hR : (tpGy p K k0 (x d)).comp (X ^ p) =
      ∑ k : Fin K, C (x d k) * ((X ^ p - 1) *
        (Chebyshev.T (ZMod p) ((k0 : ℤ) + (k : ℕ))).comp (X ^ p)) := by
    rw [tpGy_apply, mul_comp, sub_comp, X_comp, one_comp, sum_comp', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comp, C_comp]; ring
  rw [hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := tpT_term (P := P) (N := N) hp2 hph ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  simp only [cen]
  linear_combination C (x d k) * e

/-- The virtual T+ pairs. -/
def tpBad (P : Parameters) (N p : ℕ) [Fact p.Prime] (K D : ℕ) (k0 : ℤ) :
    Finset (Fin D × Fin K) :=
  Finset.univ.filter (fun dk : Fin D × Fin K => ¬ TpGood P N p k0 dk.1 dk.2)

/-- Number of virtual T+ pairs. -/
def tpVirt (P : Parameters) (N p : ℕ) [Fact p.Prime] (K D : ℕ) (k0 : ℤ) : ℕ :=
  (tpBad P N p K D k0).card

/-- The T+ pair slot system (period form). -/
def tpSystem (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hph : p ≤ P.h N + (p - 1) / 2) (K D : ℕ) (k0 : ℤ)
    (hD : D ≤ (p - 1) / 2 + 1) : SlotSystem P N p where
  K := K
  D := D
  emax := P.h N + D
  prof := ⟨tpTy p K k0, tpGy p K k0⟩
  lam := fun d => tpLam P N p d
  rows := tpRows P N p K D k0
  dom := badDom p K D (tpBad P N p K D k0)
  deg := fun d => by
    have h1 := tpLam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
    have h2 := d.isLt
    have h3 := p_odd_half hp2
    omega
  repU := fun x hx => intrinsicU_tpRows hp2 hph k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tpBad, hg]))
  repT := fun x hx => intrinsicT_tpRows hp2 hph k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tpBad, hg]))
  inj := fun x hx h0 => tpRows_injective_on hp2 hD k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tpBad, hg])) h0

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
