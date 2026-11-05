module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Resp
public import Submission.CatalanMeasure.GenD.Uniform.W.Tier3.FlatRank
@[expose] public section
set_option Elab.async false

/-!
# The kernel family of Theorem C / C' (family form)

`fam_le_nullity`: a finite-dimensional space `A` of pairs `(σ, G)` (`σ = Σ_d w_d U_d`, `(X-1)^h σ = (X^p-1) G`,
`G` supported below `hi ≤ p`), whose cell constant `ψ(a0 - 1) - ψ(a0)` at the positions in the support of
`G` is a single value, gives `dim A - (p - q) ≤ ν`.  The raw response of every member is the function
`ℓ ↦ 2 A_cell G[e0(ℓ)]` of the residue (J-flat), so the filter costs `p - q` (`w_jflat`, `v = 0`).
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `w ↦ w ⊗ z`. -/
def tensorL {K D : ℕ} (z : Fin K → ZMod p) :
    (Fin D → ZMod p) →ₗ[ZMod p] (Fin D → Fin K → ZMod p) where
  toFun w := tensorX w z
  map_add' a b := by funext d k; simp [tensorX, add_mul]
  map_smul' c a := by funext d k; simp [tensorX, mul_assoc]

theorem tensorL_injective {K D : ℕ} (z : Fin K → ZMod p) (hz : z ≠ 0) :
    Function.Injective (tensorL (D := D) z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  funext d
  have := congrFun (congrFun hw d) k
  simp only [tensorL, LinearMap.coe_mk, AddHom.coe_mk, tensorX, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_right hk

/-- **Family form of Theorem C / C'.** -/
theorem fam_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hq : 0 < P.q N) {K D : ℕ} (k0 : ℤ) (z : Fin K → ZMod p) (hz : z ≠ 0)
    (hDp : D ≤ (p - 1) / 2) (hgood : ∀ (d : Fin D) (k : Fin K), Good P N p k0 d k)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (wm : A →ₗ[ZMod p] (Fin D → ZMod p)) (hwm : Function.Injective wm)
    (Gm : A →ₗ[ZMod p] (ZMod p)[X]) (hi : ℕ)
    (hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * Gm a)
    (hsupp : ∀ a e, (Gm a).coeff e ≠ 0 → e < hi) (hhi : hi ≤ p) (hD : p + hi ≤ P.h N + D)
    (Acell : ZMod p)
    (hcell : ∀ a j, P.b N ≤ j → j < P.L N →
      (Gm a).coeff (idxRes (P.H N) p (j % p)) ≠ 0 →
      psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) z -
        psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) z = Acell) :
    finrank (ZMod p) A - (p - P.q N) ≤ nullity P N p := by
  classical
  let ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    (tRows P N p K D k0).comp ((tensorL z).comp wm)
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h1 : tensorL z (wm a) = 0 :=
      tRows_injective_on hp2 hDp k0 _ (fun d k hg => absurd (hgood d k) hg) ha
    have h2 : wm a = 0 := tensorL_injective z hz (by rw [h1, map_zero])
    exact hwm (by rw [h2, map_zero])
  let Φ : A →ₗ[ZMod p] ZMod p := 0
  let sA : A →ₗ[ZMod p] (ZMod p → ZMod p) :=
    LinearMap.pi fun x : ZMod p =>
      ((2 * Acell) • Polynomial.lcoeff (ZMod p) (idxRes (P.H N) p x.val)).comp Gm
  let s : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p → ZMod p) := sA.comp (LinearMap.ker Φ).subtype
  have h := w_jflat hp2 hH hq ι hι Φ 0 s
    (fun u => ⟨interpAll p (s u), by simpa using Tier3.degree_interpAll_lt (s u),
      fun x => (interpAll_eval (s u) x).symm⟩)
    (fun u j hj1 hj2 => by
      have hjH : j < P.H N := lt_of_lt_of_le hj2 (by
        have : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
        omega)
      have hv : ((j : ZMod p)).val = j % p := ZMod.val_natCast p j
      have e1 : uResp P N p j (ι u.1) = 2 * (Gm u.1).coeff (idxRes (P.H N) p (j % p)) *
          (psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) z -
            psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) z) :=
        uResp_tensor hP hN hp2 hH k0 z (wm u.1) (Gm u.1) hi (hrel u.1) (hsupp u.1) hhi hD
          (fun d k hg => absurd (hgood d k) hg) hjH
      have e2 : s u (j : ZMod p) = 2 * Acell * (Gm u.1).coeff (idxRes (P.H N) p (j % p)) := by
        simp only [s, sA, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply,
          LinearMap.smul_apply, Polynomial.lcoeff_apply, smul_eq_mul, hv]
      rw [e1, e2]
      by_cases hc : (Gm u.1).coeff (idxRes (P.H N) p (j % p)) = 0
      · rw [hc]; ring
      · rw [hcell u.1 j hj1 hj2 hc]; ring)
  have hr : finrank (ZMod p) (LinearMap.range Φ) = 0 := by
    simp [Φ]
  rw [hr] at h
  simpa using h

#print axioms fam_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.TheoremC
