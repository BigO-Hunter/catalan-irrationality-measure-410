module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsA.Block
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# `aLB`: family A (Theorem A) as a `NullityLB`

`aVal P N p = mu1 - mu0 - e - delta` with `mu1 = L - 5p`, `mu0 = max(q, H+q-6p)`, `e = (p+1)/2-q-h`
(truncated), `delta = n - (4p + 2g + 1)` (truncated).  Window `L ≤ 6p`, `b + q ≤ p + mu0`.
This is `proof13/fam13.py: bA` (the python also asks `mu1 ≤ p`, `mu0 < mu1`, which only make the
truncated difference vanish outside the window).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsA
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

/-- The integer bound of Theorem A. -/
def aVal (P : Parameters) (N p : ℕ) : ℕ :=
  uM1 P N p - uM0 P N p - sE P N p - (P.n N - (4 * p + 2 * P.g N + 1))

/-- The window of Theorem A. -/
def aApp (P : Parameters) (N p : ℕ) : Prop :=
  P.L N ≤ 6 * p ∧ P.b N + P.q N ≤ p + uM0 P N p

theorem aVal_le_nullity (P : Parameters) (hP : Admissible P) {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hA : aApp P N p) :
    aVal P N p ≤ nullity P N p := by
  have h := a_rank hP hN hp2 hH hA.1 hA.2
  have hn : P.n N - (4 * p + 2 * P.g N + 1) = P.n N - aNs P N p := by
    unfold aNs; omega
  unfold aVal nullity
  omega

/-- **Family A as a nullity lower bound** (any admissible design). -/
def aLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.ofWindow P (aApp P) (aVal P) (fun N p hN hp hp2 hH hA => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact aVal_le_nullity P hP hN hp2 hH hA)

end
end CatalanMeasure.GenD.Uniform.W.SlotsA
