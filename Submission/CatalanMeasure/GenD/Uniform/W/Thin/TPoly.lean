module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.PairRows
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalPairs
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.ChebyshevComposition
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
@[expose] public section
set_option Elab.async false

/-!
# Lemma T for the actual rows: the `T-` pair family in `(X, Y = X^p)` form

For `x : Fin D → Fin K → F_p` vanishing on virtual pairs, with `lam d = 2 (X-1)^h U_d(X)`
(the slot polynomial of the offset `d + 1`),

* `(X-1)^h * intrinsicU c = Σ_d lam d * (tyMap (x d)).comp (X^p)`;
* `(X-1)^h (X^2-1)^((p-1)/2) * intrinsicT c = Σ_d lam d * (gyMap (x d)).comp (X^p)`,

where `tyMap y = Σ_k y_k T_{k0+k}` and `gyMap y = (X^2-1) Σ_k y_k U_{k0+k-1}` (polynomials in
`Y`).  These are the identities `wG = (Y^2-1) U_y(Y) λ`, `F = T_y(Y) λ` of the source (F1–F2).
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `y ↦ Σ_k y_k T_{k0+k}` (a polynomial in `Y`). -/
def tyMap (p K : ℕ) (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (Chebyshev.T (ZMod p) (k0 + (k : ℕ)))

/-- `y ↦ Σ_k y_k U_{k0+k-1}`. -/
def uyMap (p K : ℕ) (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))

/-- `y ↦ (X^2 - 1) Σ_k y_k U_{k0+k-1}`. -/
def gyMap (p K : ℕ) (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  (LinearMap.mulLeft (ZMod p) ((X ^ 2 - 1 : (ZMod p)[X]))).comp (uyMap p K k0)

theorem sum_comp' {ι : Type*} (s : Finset ι) (f : ι → (ZMod p)[X]) (q : (ZMod p)[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.add_comp, ih]

theorem tyMap_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    tyMap p K k0 y = ∑ k : Fin K, C (y k) * Chebyshev.T (ZMod p) (k0 + (k : ℕ)) := by
  simp [tyMap, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

theorem uyMap_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    uyMap p K k0 y = ∑ k : Fin K, C (y k) * Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1) := by
  simp [uyMap, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

theorem gyMap_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    gyMap p K k0 y = (X ^ 2 - 1) * uyMap p K k0 y := rfl

/-- The slot polynomial of offset `d + 1`. -/
def lam (P : Parameters) (N p : ℕ) (d : ℕ) : (ZMod p)[X] :=
  2 * (X - 1) ^ P.h N * Chebyshev.U (ZMod p) (d : ℤ)

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hz
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp hz))

theorem lam_natDegree_le (hp2 : p ≠ 2) (d : ℕ) : (lam P N p d).natDegree ≤ P.h N + d := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold lam
  have h1 : (2 * (X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
    refine natDegree_mul_le.trans ?_
    have a : (2 : (ZMod p)[X]).natDegree ≤ 0 := by compute_degree
    have b : ((X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
      refine natDegree_pow_le.trans ?_
      have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
      nlinarith
    omega
  refine natDegree_mul_le.trans ?_
  have h2 : (Chebyshev.U (ZMod p) (d : ℤ)).natDegree = d := by
    have := Chebyshev.natDegree_U_natCast (R := ZMod p) d
    simpa using this
  omega

/-- `U_{a+d-1} - U_{a-d-1} = 2 T_a U_{d-1}`. -/
theorem U_pair_diff (R : Type*) [CommRing R] (a d : ℤ) :
    Chebyshev.U R (a + d - 1) - Chebyshev.U R (a - d - 1) =
      2 * Chebyshev.T R a * Chebyshev.U R (d - 1) := by
  have h1 := chebyshev_U_add R a d
  have h2 := chebyshev_U_add R a (-d)
  rw [Chebyshev.T_neg, Chebyshev.U_neg_sub_one] at h2
  rw [show a - d - 1 = a + -d - 1 by ring, h1, h2]
  ring

/-- `T_{a+d} - T_{a-d} = 2 (X^2-1) U_{a-1} U_{d-1}`. -/
theorem T_pair_diff (R : Type*) [CommRing R] (a d : ℤ) :
    Chebyshev.T R (a + d) - Chebyshev.T R (a - d) =
      2 * (X ^ 2 - 1) * Chebyshev.U R (a - 1) * Chebyshev.U R (d - 1) := by
  have h1 := chebyshev_T_add R a d
  have h2 := chebyshev_T_add R a (-d)
  rw [Chebyshev.T_neg, Chebyshev.U_neg_sub_one] at h2
  rw [show a - d = a + -d by ring, h1, h2]
  ring

theorem T_block (hp2 : p ≠ 2) (κ : ℤ) :
    Chebyshev.T (ZMod p) (κ * p) = (Chebyshev.T (ZMod p) κ).comp (X ^ p) := by
  rw [Chebyshev.T_mul, chebyshev_T_prime hp2]

theorem U_block (hp2 : p ≠ 2) (κ : ℤ) :
    Chebyshev.U (ZMod p) (κ * p - 1) =
      (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p) * (X ^ 2 - 1) ^ ((p - 1) / 2) := by
  rw [chebyshev_U_mul, chebyshev_T_prime hp2, chebyshev_U_prime hp2]

theorem p_odd_half (hp2 : p ≠ 2) : p = (p - 1) / 2 + (p - 1) / 2 + 1 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd' with h | ⟨m, hm⟩
  · exact absurd h hp2
  · omega

theorem frob_X_sq (hp2 : p ≠ 2) :
    (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * (X ^ 2 - 1) ^ ((p - 1) / 2) * (X ^ 2 - 1) =
      ((X ^ 2 - 1 : (ZMod p)[X])).comp (X ^ p) := by
  have e : (X ^ 2 - 1 : (ZMod p)[X]) ^ p = (X ^ 2 - 1 : (ZMod p)[X]).comp (X ^ p) := by
    rw [sub_pow_char, one_pow]
    simp [← pow_mul, mul_comm]
  rw [← e]
  have e2 : (X ^ 2 - 1 : (ZMod p)[X]) ^ p =
      (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2 + (p - 1) / 2 + 1) :=
    congrArg (fun n => (X ^ 2 - 1 : (ZMod p)[X]) ^ n) (p_odd_half hp2)
  rw [e2]; ring

/-- Offset sum for the `U` part. -/
theorem intrinsicU_tRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ d k, ¬ Good P N p k0 d k → x d k = 0) :
    (X - 1) ^ P.h N * intrinsicU P N p (tRows P N p K D k0 x) =
      ∑ d : Fin D, lam P N p (d : ℕ) * (tyMap p K k0 (x d)).comp (X ^ p) := by
  have h := sum_pairRows (P := P) (N := N) k0 x hx
    (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (tRows P N p K D k0 x r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [tyMap_apply, sum_comp', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := U_pair_diff (ZMod p) (cen p K k0 k) (((d : ℕ) : ℤ) + 1)
  have e' : Chebyshev.U (ZMod p) (cen p K k0 k + ((d : ℕ) + 1) - 1) -
      Chebyshev.U (ZMod p) (cen p K k0 k - ((d : ℕ) + 1) - 1) =
      2 * Chebyshev.T (ZMod p) (cen p K k0 k) * Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) := by
    rw [e]; congr 2; ring
  rw [e', cen, T_block hp2, lam]
  simp only [Polynomial.C_mul_comp]
  ring

/-- Offset sum for the `T` part. -/
theorem intrinsicT_tRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ d k, ¬ Good P N p k0 d k → x d k = 0) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p (tRows P N p K D k0 x) =
      ∑ d : Fin D, lam P N p (d : ℕ) * (gyMap p K k0 (x d)).comp (X ^ p) := by
  have h := sum_pairRows (P := P) (N := N) k0 x hx
    (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (tRows P N p K D k0 x r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [gyMap_apply, uyMap_apply]
  simp only [Polynomial.mul_comp, sum_comp', Polynomial.C_mul_comp,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := T_pair_diff (ZMod p) (cen p K k0 k) (((d : ℕ) : ℤ) + 1)
  have e' : Chebyshev.T (ZMod p) (cen p K k0 k + ((d : ℕ) + 1)) -
      Chebyshev.T (ZMod p) (cen p K k0 k - ((d : ℕ) + 1)) =
      2 * (X ^ 2 - 1) * Chebyshev.U (ZMod p) (cen p K k0 k - 1) *
        Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) := by
    rw [e]; congr 2; ring
  have hU := U_block hp2 ((k0 : ℤ) + (k : ℕ))
  have hcen : cen p K k0 k = (k0 + (k : ℕ)) * p := rfl
  have hf := frob_X_sq (p := p) hp2
  rw [e', hcen, hU, lam, ← hf]
  simp only [map_sub, Polynomial.C_comp]
  ring

end
end CatalanMeasure.GenD.Uniform.W.Thin
