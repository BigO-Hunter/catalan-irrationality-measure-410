module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Period
@[expose] public section
set_option Elab.async false

/-!
# The period count

`period_nullity`: the generic Theorem P count on a slot system.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Coefficient of `(X^p - 1) Q`. -/
theorem lc_period (Q : (ZMod p)[X]) (e : ℕ) :
    (X ^ p * Q - Q).coeff e = (if p ≤ e then Q.coeff (e - p) else 0) - Q.coeff e := by
  rw [coeff_sub, coeff_X_pow_mul']

namespace SlotSystem
variable (S : SlotSystem P N p)

/-- The atom map of a family of tensor atoms `Σ_i s_i ⊗ y_i`. -/
def tensorMap {m : ℕ} (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p) :
    (Fin m → V) →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) :=
  LinearMap.pi fun t => LinearMap.pi fun k =>
    ∑ i : Fin m, sc i t • ((LinearMap.proj k : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p).comp
      (V.subtype.comp (LinearMap.proj i)))

theorem tensorMap_apply {m : ℕ} (V : Submodule (ZMod p) (Fin S.K → ZMod p))
    (sc : Fin m → Fin S.D → ZMod p) (y : Fin m → V) (t : Fin S.D) (k : Fin S.K) :
    S.tensorMap V sc y t k = ∑ i : Fin m, sc i t * (y i : Fin S.K → ZMod p) k := by
  simp [tensorMap, LinearMap.sum_apply]

theorem wv_tensor {m : ℕ} (V : Submodule (ZMod p) (Fin S.K → ZMod p))
    (sc : Fin m → Fin S.D → ZMod p) (Pp : Fin m → (ZMod p)[X])
    (hrel : ∀ i, ∑ t, C (sc i t) * S.lam t = X ^ p * Pp i - Pp i) (y : Fin m → V) (e : ℕ) :
    wv S.lam (S.tensorMap V sc y) e =
      ∑ i : Fin m, (X ^ p * Pp i - Pp i).coeff e • (y i : Fin S.K → ZMod p) := by
  funext k
  have hc : ∀ i, (X ^ p * Pp i - Pp i).coeff e = ∑ t, sc i t * (S.lam t).coeff e := by
    intro i
    rw [← hrel i, finset_sum_coeff]
    exact Finset.sum_congr rfl fun t _ => coeff_C_mul _
  simp only [wv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, S.tensorMap_apply, hc]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => by ring

/-- Injectivity of the tensor atoms (the `λ_i` are independent). -/
theorem period_injective {m : ℕ} (V : Submodule (ZMod p) (Fin S.K → ZMod p))
    (Pp : Fin m → (ZMod p)[X]) (sc : Fin m → Fin S.D → ZMod p)
    (hrel : ∀ i, ∑ t, C (sc i t) * S.lam t = X ^ p * Pp i - Pp i)
    (hind : ∀ cc : Fin m → ZMod p, ∑ i, C (cc i) * (X ^ p * Pp i - Pp i) = 0 → cc = 0) :
    Function.Injective (S.tensorMap V sc) := by
  refine injective_of_zero _ fun y hy => ?_
  funext i
  apply Subtype.ext
  funext k
  have hcc := hind (fun i => (y i : Fin S.K → ZMod p) k) (by
    ext e
    rw [finset_sum_coeff]
    simp only [coeff_C_mul, coeff_zero]
    have := congrFun (S.wv_tensor V sc Pp hrel y e) k
    have h0 : wv S.lam (S.tensorMap V sc y) e = 0 := by
      rw [hy]; unfold wv; simp
    rw [h0] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
  exact congrFun hcc i

/-- The raw response of every tensor atom vanishes. -/
theorem period_resp_zero {m : ℕ} (V : Submodule (ZMod p) (Fin S.K → ZMod p))
    {eta s ilo Pmax : ℕ} (heta : (P.H N : ℤ) - 1 - eta = s * p)
    (hPmax : Pmax + p ≤ eta) (hilo : eta + 1 ≤ ilo + 2 * p)
    (Pp : Fin m → (ZMod p)[X]) (hPdeg : ∀ i, (Pp i).natDegree ≤ Pmax)
    (hPlo : ∀ i e, e < ilo → (Pp i).coeff e = 0)
    (sc : Fin m → Fin S.D → ZMod p)
    (hrel : ∀ i, ∑ t, C (sc i t) * S.lam t = X ^ p * Pp i - Pp i)
    (hVpsi : ∀ j, P.b N ≤ j → j < P.L N → p + j % p ≤ eta → ilo ≤ eta - p - j % p →
      eta - p - j % p ≤ Pmax → ∀ y ∈ V,
        S.prof.psi (P.H N) (j / p) s y = S.prof.psi (P.H N) (j / p) ((s : ℤ) + 1) y)
    (y : Fin m → V) (j : ℕ) (h1 : P.b N ≤ j) (h2 : j < P.L N) :
    S.resp (j / p) (j % p) (S.tensorMap V sc y) = 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hPhi : ∀ i e, Pmax < e → (Pp i).coeff e = 0 := fun i e he =>
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hPdeg i) he)
  have hlam : ∀ i e, (X ^ p * Pp i - Pp i).coeff e =
      (if p ≤ e then (Pp i).coeff (e - p) else 0) - (Pp i).coeff e := fun i e =>
    lc_period (Pp i) e
  have hell : j % p < p := Nat.mod_lt _ hp0
  have hhi : ∀ e, eta < e → wv S.lam (S.tensorMap V sc y) e = 0 := by
    intro e he
    rw [S.wv_tensor V sc Pp hrel y e]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (X ^ p * Pp i - Pp i).coeff e = 0 := by
      rw [hlam]
      by_cases hpe : p ≤ e
      · rw [if_pos hpe, hPhi i (e - p) (by omega), hPhi i e (by omega)]; simp
      · rw [if_neg hpe, hPhi i e (by omega)]; simp
    rw [this, zero_smul]
  have hlo : ∀ e, e + 2 * p ≤ eta → wv S.lam (S.tensorMap V sc y) e = 0 := by
    intro e he
    rw [S.wv_tensor V sc Pp hrel y e]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (X ^ p * Pp i - Pp i).coeff e = 0 := by
      rw [hlam]
      by_cases hpe : p ≤ e
      · rw [if_pos hpe, hPlo i (e - p) (by omega), hPlo i e (by omega)]; simp
      · rw [if_neg hpe, hPlo i e (by omega)]; simp
    rw [this, zero_smul]
  show S.resp (j / p) (j % p) (S.tensorMap V sc y) = 0
  rw [S.resp_two heta (j / p) (j % p) hell _ hhi hlo]
  by_cases hc : p + j % p ≤ eta
  · -- the two windows
    have hA : wv S.lam (S.tensorMap V sc y) (eta - j % p) =
        ∑ i, (Pp i).coeff (eta - p - j % p) • (y i : Fin S.K → ZMod p) := by
      rw [S.wv_tensor V sc Pp hrel y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hlam, if_pos (by omega), hPhi i (eta - j % p) (by omega),
        show eta - j % p - p = eta - p - j % p by omega, sub_zero]
    have hB : wv S.lam (S.tensorMap V sc y) (eta - p - j % p) =
        -∑ i, (Pp i).coeff (eta - p - j % p) • (y i : Fin S.K → ZMod p) := by
      rw [S.wv_tensor V sc Pp hrel y, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hlam]
      by_cases hpu : p ≤ eta - p - j % p
      · rw [if_pos hpu, hPlo i (eta - p - j % p - p) (by omega), zero_sub, neg_smul]
      · rw [if_neg hpu, zero_sub, neg_smul]
    rw [if_pos (by omega : j % p ≤ eta), if_pos hc, hA, hB, map_neg, map_sum, map_sum]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases hr : ilo ≤ eta - p - j % p ∧ eta - p - j % p ≤ Pmax
    · have := hVpsi j h1 h2 hc hr.1 hr.2 (y i) (y i).2
      rw [this]; ring
    · have h0 : (Pp i).coeff (eta - p - j % p) = 0 := by
        by_cases hlt : eta - p - j % p < ilo
        · exact hPlo i _ hlt
        · exact hPhi i _ (by omega)
      rw [h0]; ring
  · rw [if_neg hc, add_zero]
    by_cases hl : j % p ≤ eta
    · rw [if_pos hl]
      have : wv S.lam (S.tensorMap V sc y) (eta - j % p) = 0 := by
        rw [S.wv_tensor V sc Pp hrel y]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hlam, if_neg (by omega), hPhi i (eta - j % p) (by omega)]
        simp
      rw [this, map_zero]
    · rw [if_neg hl]

/-- **Period count (Theorem P mechanism).** -/
theorem period_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {m : ℕ} (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (hdom : ∀ x, x ∈ S.dom)
    {eta s ilo Pmax : ℕ} (heta : (P.H N : ℤ) - 1 - eta = s * p)
    (hPmax : Pmax + p ≤ eta) (hilo : eta + 1 ≤ ilo + 2 * p)
    (Pp : Fin m → (ZMod p)[X]) (hPdeg : ∀ i, (Pp i).natDegree ≤ Pmax)
    (hPlo : ∀ i e, e < ilo → (Pp i).coeff e = 0)
    (sc : Fin m → Fin S.D → ZMod p)
    (hrel : ∀ i, ∑ t, C (sc i t) * S.lam t = X ^ p * Pp i - Pp i)
    (hind : ∀ cc : Fin m → ZMod p, ∑ i, C (cc i) * (X ^ p * Pp i - Pp i) = 0 → cc = 0)
    (hVpsi : ∀ j, P.b N ≤ j → j < P.L N → p + j % p ≤ eta → ilo ≤ eta - p - j % p →
      eta - p - j % p ≤ Pmax → ∀ y ∈ V,
        S.prof.psi (P.H N) (j / p) s y = S.prof.psi (P.H N) (j / p) ((s : ℤ) + 1) y) :
    m * finrank (ZMod p) V ≤ nullity P N p := by
  have h := S.slot_nullity_raw hP hN hp2 hH (S.tensorMap V sc) (fun a => hdom _)
    (S.period_injective V Pp sc hrel hind)
    (0 : (Fin m → V) →ₗ[ZMod p] (Fin 0 → ZMod p)) (fun y _ j h1 h2 =>
      S.period_resp_zero V heta hPmax hilo Pp hPdeg hPlo sc hrel hVpsi y j h1 h2)
  have h0 : finrank (ZMod p) (LinearMap.range (0 : (Fin m → V) →ₗ[ZMod p] (Fin 0 → ZMod p))) = 0 := by
    rw [LinearMap.range_zero]; exact finrank_bot _ _
  have hd : finrank (ZMod p) (Fin m → V) = m * finrank (ZMod p) V := by
    simp [Module.finrank_pi_fintype]
  omega

#print axioms period_nullity
end SlotSystem

end
end CatalanMeasure.GenD.Uniform.W.Slots
