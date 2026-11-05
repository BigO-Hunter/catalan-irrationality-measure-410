module
public import Submission.CatalanMeasure.GenD.Uniform.W.FrobInst.CType
@[expose] public section
set_option Elab.async false

/-!
# Banking the Frobenius-product bound for any admissible design

`frobInst_bound` : `(dP+1) (K - #seen) ≤ ν` with the explicit atoms `Δ y^lo P(y) Λ(τ)`.
`frobInstLB`     : the `NullityLB` of a window family, with only the window inequalities
(`lo + dP + 1 ≤ (p-1)/2`, all products actual rows) and the count `val ≤ (dP+1)(K - #seen)`
left; `#seen = (seenSet …).card` is the closed floor/residue count of the active window.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- **Frobenius products (LB), design-generic.** -/
theorem frobInst_bound (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K lo dP : ℕ} {k0 : ℤ} (hD : lo + (dP + 1) ≤ (p - 1) / 2)
    (hg : FrobGood P N p K lo (dP + 1) k0) :
    (dP + 1) * (K - (seenSet P N p lo (lo + (dP + 1))).card) ≤ nullity P N p :=
  frob_product_nullity hp2 hH (frobData hP hN hp2 hH hD hg)

/-- The `NullityLB` of a Frobenius-product window family. -/
def frobInstLB (P : Parameters) (hP : Admissible P) (App : ℕ → ℕ → Prop) (val : ℕ → ℕ → ℕ)
    (K lo dP : ℕ → ℕ → ℕ) (k0 : ℕ → ℕ → ℤ)
    (hwin : ∀ N p : ℕ, 0 < N → p.Prime → p ≠ 2 → P.H N < p ^ 2 → App N p →
      lo N p + (dP N p + 1) ≤ (p - 1) / 2 ∧
        FrobGood P N p (K N p) (lo N p) (dP N p + 1) (k0 N p))
    (hval : ∀ N p : ℕ, App N p →
      val N p ≤ (dP N p + 1) * (K N p -
        (seenSet P N p (lo N p) (lo N p + (dP N p + 1))).card)) : NullityLB P :=
  frobProductLB P App val fun N p hN hp hp2 hH hA => by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h1, h2⟩ := hwin N p hN hp hp2 hH hA
    exact ⟨frobData hP hN hp2 hH h1 h2, hval N p hA⟩

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
