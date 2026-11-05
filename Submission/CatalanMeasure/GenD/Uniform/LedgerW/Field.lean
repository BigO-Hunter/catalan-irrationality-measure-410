module

public import Submission.CatalanMeasure.GenD.Uniform.LedgerW.Main
public import Submission.CatalanMeasure.GenD.Final

@[expose] public section

/-!
# The `D_growth` field of `DesignData`

`D_growth_field` has exactly the shape of the field `DesignData.D_growth` for the canonical
normalizer of an arbitrary `NullityLB` (so a `DesignData` is assembled by taking
`Z := canonicalNormalizer P hP lb N0 hN0`, `gD := LedgerW.gD P f κ0 ws` and this theorem).
-/

namespace CatalanMeasure.GenD.Uniform.LedgerW

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Arithmetic

noncomputable section

theorem D_growth_field (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    (N0 : ℕ) (hN0 : P.H 1 < N0)
    (f : PL.Prof) (κ0 : ℝ)
    (hloss : ∀ N p : ℕ, 0 < N → p ≤ P.H N →
      (safeOddLoss P N p : ℝ) ≤ N * f.eval ((p : ℝ) / N))
    (hf0 : ∀ x : ℝ, x ≤ 1 → f.eval x = κ0)
    (charge : ℕ → ℕ → ℕ) (E : ℕ → Finset ℕ) (M : ℕ) (cch : ℝ) (hcch : 0 ≤ cch)
    (hE : ∀ N, (E N).card ≤ M) (hsupport : ∀ N p, p ∉ E N → charge N p = 0)
    (hcharge : ∀ N p, (charge N p : ℝ) ≤ cch * N)
    (ws : List KapWindow) (c : ℝ) (hc : 0 ≤ c)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ (P.H 1 : ℝ))
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (hcert : ∀ w ∈ ws, ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → w.a * N < p →
      (p : ℝ) ≤ w.b * N →
        (N : ℝ) * w.K.eval ((p : ℝ) / N) - c ≤ (lb.kap N p : ℝ) + charge N p ∧
        (N : ℝ) * w.G.eval ((p : ℝ) / N) - c ≤ (safeOddLoss P N p : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer P hP lb N0 hN0).D N) ≤
        (gD P f κ0 ws + ε) * (N : ℝ) ^ 2 :=
  fun _ hε => D_growth_of_nullityLB P hP lb N0 hN0 f κ0 hloss hf0 charge E M cch hcch hE
    hsupport hcharge ws c hc hpos hord hrec hcert hε

end

end CatalanMeasure.GenD.Uniform.LedgerW
