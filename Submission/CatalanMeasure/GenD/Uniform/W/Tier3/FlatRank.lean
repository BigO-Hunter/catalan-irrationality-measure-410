module
public import Submission.CatalanMeasure.GenD.Uniform.W.Nullity
public import Submission.CatalanMeasure.GenD.Uniform.W.Jets
@[expose] public section
set_option Elab.async false

/-!
# `w_flatrank`: Theorem W with the full J-flatness map (lane G6, Theorem L*)

For every residue `ℓ` let `Jset ℓ` be a finite set of digits containing all `j / p` with
`b ≤ j < L`, `j % p = ℓ`, and `J0 ℓ` a reference digit.  The J-flatness map of a space of rows `ι : A → F^n`
is `Φ_ℓ a = (R_J(ℓ)(ι a) - R_{J0}(ℓ)(ι a))_{J ∈ Jset ℓ}`.  Then

    dim A - Σ_ℓ rank Φ_ℓ - (p - q)  ≤  ν ,

since on `ker Φ` the raw response depends on `ℓ` only, hence is a polynomial function of degree `< p`
(`w_jflat` with `v = 0`).  Only the ranks `r ℓ ≥ rank Φ_ℓ` enter: a *local relation* at `ℓ` is a bound
`r ℓ < |Jset ℓ| - 1`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Tier3
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The J-flatness map at the residue `ℓ`. -/
def flatPhi {A : Type*} [AddCommGroup A] [Module (ZMod p) A]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (Jset : ZMod p → Finset ℕ) (J0 : ZMod p → ℕ)
    (ℓ : ZMod p) : A →ₗ[ZMod p] (↥(Jset ℓ) → ZMod p) :=
  LinearMap.pi fun J =>
    ((uResp P N p (J.1 * p + ℓ.val)) - (uResp P N p (J0 ℓ * p + ℓ.val))).comp ι

theorem degree_interpAll_lt (s : ZMod p → ZMod p) : (interpAll p s).degree < (p : WithBot ℕ) := by
  have h := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (ZMod p))) (v := id)
    s (Set.injOn_id _)
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  rw [hcard] at h
  exact h

theorem w_flatrank (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hq : 0 < P.q N)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Jset : ZMod p → Finset ℕ) (J0 : ZMod p → ℕ)
    (hJ : ∀ j, P.b N ≤ j → j < P.L N → j / p ∈ Jset (j : ZMod p))
    (r : ZMod p → ℕ) (hr : ∀ ℓ, finrank (ZMod p) (LinearMap.range (flatPhi ι Jset J0 ℓ)) ≤ r ℓ) :
    finrank (ZMod p) A - ∑ ℓ, r ℓ - (p - P.q N) ≤ nullity P N p := by
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
  have hrk : finrank (ZMod p) (LinearMap.range Φ) ≤ ∑ ℓ, r ℓ :=
    (rank_stackMap_le (flatPhi ι Jset J0)).trans (Finset.sum_le_sum fun ℓ _ => hr ℓ)
  omega

#print axioms w_flatrank
end
end CatalanMeasure.GenD.Uniform.W.Tier3
