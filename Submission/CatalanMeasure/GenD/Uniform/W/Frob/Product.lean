module
public import Submission.CatalanMeasure.GenD.Uniform.W.Families
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Frobenius-product families as Theorem W instances

KERNEL-FAMILY-THEOREM (LB): `c(t) = Δ · y^lo · P(y) · Λ(t^p)`, `deg P ≤ dP`, `Λ` in a τ-window of
`β = k+1` coordinates, `e = #seen` seen functionals.  Then `ν ≥ (k+1 - #seen)_+ · (dP+1)`.

The count is `w_product`.  The two facts the construction must supply are packaged in
`FrobProductData`, design-generically:

* `inj`  : (F4) injectivity of `(P, Λ) ↦ c` on `Poly_{≤dP} ⊗ F_p^β` (digit argument,
  `2σ < p`, distinct residues mod `p`, atoms are actual rows).  This needs the tiling-index to
  G-row lemma (G2, `W/Thin`).
* `killed` : (F3) every atom whose `Λ` annihilates the seen functionals has polynomial
  (indeed zero) raw response (G2 `RawKilled` step).
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module CatalanMeasure.Parametric CatalanMeasure.GenD
noncomputable section

/-- Data of a Frobenius-product family: `m = dP + 1` polynomial coordinates, `β = k + 1` window
coordinates, `e` seen functionals `E` on the window, and the atom map `Θ` on all of
`Π ⊗ F_p^β`. -/
structure FrobProductData (P : Parameters) (N p : ℕ) [Fact p.Prime] where
  m : ℕ
  β : ℕ
  e : ℕ
  E : (Fin β → ZMod p) →ₗ[ZMod p] (Fin e → ZMod p)
  Θ : (Fin m → (Fin β → ZMod p)) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)
  inj : Function.Injective Θ
  killed : ∀ x : Fin m → (Fin β → ZMod p), (∀ i, E (x i) = 0) → RawKilled P N p (Θ x)

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The restriction of `Θ` to `Π ⊗ ker E`. -/
def FrobProductData.ι (D : FrobProductData P N p) :
    (Fin D.m → LinearMap.ker D.E) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  D.Θ.comp (LinearMap.pi fun i => (LinearMap.ker D.E).subtype.comp (LinearMap.proj i))

theorem FrobProductData.ι_apply (D : FrobProductData P N p) (x : Fin D.m → LinearMap.ker D.E) :
    D.ι x = D.Θ fun i => (x i : Fin D.β → ZMod p) := rfl

/-- **Theorem (Frobenius products, (LB)).**
`ν ≥ (k+1 - #seen)_+ · (dP+1)`, with `β = k+1`, `e = #seen`, `m = dP+1`. -/
theorem frob_product_nullity (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (D : FrobProductData P N p) :
    D.m * (D.β - D.e) ≤ nullity P N p := by
  refine w_product hp2 hH D.E D.ι ?_ ?_
  · intro x y hxy
    have h := D.inj hxy
    funext i
    exact Subtype.ext (congrFun h i)
  · intro x
    exact D.killed _ fun i => (x i).2

/-- The same, with `k`, `#seen`, `dP` visible. -/
theorem frob_product_bound (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (D : FrobProductData P N p)
    {k nseen dP : ℕ} (hk : D.β = k + 1) (hs : D.e = nseen) (hd : D.m = dP + 1) :
    (k + 1 - nseen) * (dP + 1) ≤ nullity P N p := by
  have h := frob_product_nullity hp2 hH D
  rw [hk, hs, hd] at h
  rw [Nat.mul_comm]
  exact h

/-- Banking: a value dominated by some product family at every point of a window. -/
def frobProductLB (P : Parameters) (App : ℕ → ℕ → Prop) (val : ℕ → ℕ → ℕ)
    (h : ∀ N p : ℕ, 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 → App N p →
      haveI : Fact p.Prime := ⟨hp⟩
      ∃ D : FrobProductData P N p, val N p ≤ D.m * (D.β - D.e)) : NullityLB P :=
  NullityLB.ofWindow P App val fun N p hN hp hp2 hH hA => by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨D, hD⟩ := h N p hN hp hp2 hH hA
    exact hD.trans (frob_product_nullity hp2 hH D)

end
end CatalanMeasure.GenD.Uniform.W
