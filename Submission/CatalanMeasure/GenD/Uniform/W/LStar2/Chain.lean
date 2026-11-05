module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Window
@[expose] public section
set_option Elab.async false

/-!
# Kernel chains and `w_flatrank'` (lane G6d)

* `chain_step`: `dim K ≤ dim (K ⊓ ker f) + dim (f K)`;
* `w_flatrank'`: `w_flatrank` with the rank of the whole stack as hypothesis (the window
  relations couple neighbouring residues, so the per-residue rank form is not enough).
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Tier3
noncomputable section

theorem chain_step {k A W : Type*} [Field k] [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup W] [Module k W] (K : Submodule k A) (f : A →ₗ[k] W) :
    finrank k K ≤ finrank k ↥(K ⊓ LinearMap.ker f) + finrank k ↥(K.map f) := by
  let g : K →ₗ[k] W := f.comp K.subtype
  have h := LinearMap.finrank_range_add_finrank_ker g
  have e1 : LinearMap.range g = K.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e2 : finrank k (LinearMap.ker g) = finrank k ↥(K ⊓ LinearMap.ker f) := by
    have e3 : Submodule.map K.subtype (LinearMap.ker g) = K ⊓ LinearMap.ker f := by
      rw [LinearMap.ker_comp, Submodule.map_comap_subtype]
    rw [← e3]
    exact (Submodule.finrank_map_subtype_eq K (LinearMap.ker g)).symm
  rw [e1] at h
  omega

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem w_flatrank' (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hq : 0 < P.q N)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Jset : ZMod p → Finset ℕ) (J0 : ZMod p → ℕ)
    (hJ : ∀ j, P.b N ≤ j → j < P.L N → j / p ∈ Jset (j : ZMod p)) (R : ℕ)
    (hrk : finrank (ZMod p) (LinearMap.range (stackMap (flatPhi (P := P) (N := N) ι Jset J0))) ≤ R) :
    finrank (ZMod p) A - R - (p - P.q N) ≤ nullity P N p := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let Φ : A →ₗ[ZMod p] (∀ ℓ : ZMod p, ↥(Jset ℓ) → ZMod p) := stackMap (flatPhi ι Jset J0)
  let s : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p → ZMod p) :=
    LinearMap.pi fun ℓ => (uResp P N p (J0 ℓ * p + ℓ.val)).comp (ι.comp (LinearMap.ker Φ).subtype)
  have h := w_jflat hp2 hH hq ι hι Φ 0 s
    (fun u => ⟨interpAll p (s u), by simpa using degree_interpAll_lt (s u),
      fun x => (interpAll_eval (s u) x).symm⟩)
    (fun u j h1 h2 => by
      have hu : ∀ ℓ, flatPhi ι Jset J0 ℓ u.1 = 0 := (stackMap_eq_zero_iff _ u.1).mp u.2
      have hℓ := hu (j : ZMod p)
      have hjm : ((j : ZMod p)).val = j % p := ZMod.val_natCast p j
      have hmem := hJ j h1 h2
      have := congrFun hℓ ⟨j / p, hmem⟩
      simp only [flatPhi, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        Pi.zero_apply] at this
      have e : j / p * p + j % p = j := by rw [mul_comm]; exact Nat.div_add_mod j p
      rw [hjm, e] at this
      simp only [s, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, hjm]
      exact sub_eq_zero.mp this)
  have hrk' : finrank (ZMod p) (LinearMap.range Φ) ≤ R := hrk
  omega

#print axioms chain_step
#print axioms w_flatrank'
end
end CatalanMeasure.GenD.Uniform.W.LStar2
