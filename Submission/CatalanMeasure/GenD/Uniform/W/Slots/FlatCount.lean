module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Flat
@[expose] public section
set_option Elab.async false

/-!
# The J-flat slot count (Theorem H' mechanism)

`slot_nullity_flat`: for a slot system whose slot polynomials are divisible by `(X-1)^v`, of
degree `≤ η = H-1-sp`, with the covectors `ψ(J, s)` agreeing with a fixed `γ` on the profile
space `V` for every column that sees the window,

    dim (dom ⊓ Π V) ≤ ν + e0 · dim V + (p - q - v)_+ .
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

namespace SlotSystem
variable (S : SlotSystem P N p)

/-- The residue sequence `ℓ ↦ γ(w_{η-ℓ})` as a linear function of the datum. -/
def flatFun (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (eta : ℕ)
    (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p) :
    S.atoms V →ₗ[ZMod p] (ZMod p → ZMod p) :=
  LinearMap.pi fun ℓ : ZMod p =>
    if ℓ.val ≤ eta then (γ.comp (wvL S.lam (eta - ℓ.val))).comp (S.atoms V).subtype else 0

theorem flatFun_apply (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (eta : ℕ)
    (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p) (a : S.atoms V) (ℓ : ZMod p) :
    S.flatFun V eta γ a ℓ = if ℓ.val ≤ eta then γ (wv S.lam a.1 (eta - ℓ.val)) else 0 := by
  unfold flatFun
  by_cases h : ℓ.val ≤ eta
  · simp [h, wvL_apply]
  · simp [h]

theorem wv_coord (x : Fin S.D → Fin S.K → ZMod p) (e : ℕ) (k : Fin S.K) :
    wv S.lam x e k = (∑ d, C (x d k) * S.lam d).coeff e := by
  simp only [wv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finset_sum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- **J-flat slot count.** -/
theorem slot_nullity_flat (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p)
    {eta s e0 v dm : ℕ} (hv : v < p) (hdm : dm ≤ eta) (hdvd : ∀ d, ((X - 1) ^ v : (ZMod p)[X]) ∣ S.lam d)
    (hdeg : ∀ d, (S.lam d).natDegree ≤ dm) (he0 : eta + 1 ≤ e0 + p)
    (heta : (P.H N : ℤ) - 1 - eta = s * p)
    (hpsi : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ eta → eta ≤ j % p + dm →
      ∀ y ∈ V, S.prof.psi (P.H N) (j / p) s y = γ y) :
    finrank (ZMod p) (S.atoms V) ≤ nullity P N p + e0 * finrank (ZMod p) V + (p - P.q N - v) := by
  have hjet : ∀ u : LinearMap.ker (S.jets V e0), ∀ e < e0, wv S.lam u.1.1 e = 0 := by
    intro u e he
    have := congrFun (LinearMap.mem_ker.mp u.2) ⟨e, he⟩
    have h3 := S.jets_apply V e0 u.1 ⟨e, he⟩
    rw [this] at h3
    simpa using h3.symm
  have h := S.slot_nullity_jflat hP hN hp2 hH (S.atoms V).subtype
    (fun a => ((S.mem_atoms).mp a.2).1) (Submodule.subtype_injective _) (S.jets V e0) v
    ((S.flatFun V eta γ).comp (LinearMap.ker (S.jets V e0)).subtype)
    (fun u => by
      -- polynomial function of degree < p - v
      have hk : ∀ k : Fin S.K, ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
          ∀ ℓ : ZMod p, (if ℓ.val ≤ eta then wv S.lam u.1.1 (eta - ℓ.val) k else 0) = G.eval ℓ := by
        intro k
        have := jflat_poly (p := p) hv (∑ d, C (u.1.1 d k) * S.lam d)
          (Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right (hdvd d) _) eta
          (natDegree_sum_le_of_forall_le _ _ fun d _ =>
            (natDegree_C_mul_le _ _).trans ((hdeg d).trans hdm))
          (fun i hi => by
            rw [← S.wv_coord u.1.1 i k, hjet u i (by omega)]; rfl)
        obtain ⟨G, hG, hGe⟩ := this
        refine ⟨G, hG, fun ℓ => ?_⟩
        rw [← hGe ℓ]
        simp only [S.wv_coord]
      choose Gk hGk using hk
      refine ⟨∑ k, C (γ (fun j => if k = j then 1 else 0)) * Gk k, ?_, fun ℓ => ?_⟩
      · rw [Polynomial.degree_lt_iff_coeff_zero]
        intro i hi
        rw [finset_sum_coeff]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [coeff_C_mul, coeff_eq_zero_of_degree_lt ((hGk k).1.trans_le (by exact_mod_cast hi)),
          mul_zero]
      · simp only [LinearMap.comp_apply, Submodule.subtype_apply, S.flatFun_apply]
        rw [eval_finset_sum]
        simp only [eval_mul, eval_C]
        simp_rw [← (hGk _).2 ℓ]
        by_cases hl : ℓ.val ≤ eta
        · simp only [hl, if_true]
          rw [LinearMap.pi_apply_eq_sum_univ γ (wv S.lam u.1.1 (eta - ℓ.val))]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [smul_eq_mul, mul_comm]
        · simp [hl])
    (fun u j h1 h2 => by
      have hell : j % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
      show S.resp (j / p) (j % p) u.1.1 = _
      rw [S.resp_flat he0 heta (j / p) (j % p) hell u.1.1
        (fun e he => S.wv_eq_zero_of_gt (fun d => (hdeg d).trans hdm) _ he) (hjet u)]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, S.flatFun_apply,
        ZMod.val_natCast]
      by_cases hl : j % p ≤ eta
      · simp only [hl, if_true]
        by_cases hc : e0 + j % p ≤ eta ∧ eta ≤ j % p + dm
        · refine hpsi j h1 h2 hc.1 hc.2 _ ?_
          have hxV := ((S.mem_atoms).mp u.1.2).2
          unfold wv
          exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hxV d)
        · by_cases hc1 : e0 + j % p ≤ eta
          · have hz := S.wv_eq_zero_of_gt hdeg u.1.1 (e := eta - j % p) (by omega)
            rw [hz, map_zero, map_zero]
          · rw [hjet u (eta - j % p) (by omega), map_zero, map_zero]
      · simp [hl])
  have := S.finrank_range_jets_le V e0
  omega

#print axioms slot_nullity_flat
end SlotSystem

end
end CatalanMeasure.GenD.Uniform.W.Slots
