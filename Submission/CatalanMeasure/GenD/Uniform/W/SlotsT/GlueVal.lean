module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.ProfDeg
@[expose] public section
set_option Elab.async false

/-!
# The integer value of Theorem MT (b), `m = 1`

`mtGlueVal1` is `proof4/thmMT2.py: countMTo(kind = 'b')` with `m = 1`:
`(2 D1 + 1) - (η - p + 1) - elo - V - r`, `V = mixMiss`, `r = (p - q - a)_+`.
`mt_glue_one_le_nullity` proves `mtGlueVal1 ≤ ν` whenever a profile pair `(y, u)` with the stated
equations exists (the hypotheses are not design data, so this is not a `NullityLB`).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Count of Theorem MT (b) with one profile pair. -/
def mtGlueVal1 (P : Parameters) (N p s K D1 elo : ℕ) (k0 : ℤ) : ℕ :=
  (D1 + (D1 + 1)) - ((P.H N - 1 - s * p - p + 1) + elo) - mixMiss P N p K D1 k0 -
    (p - P.q N - (P.h N + (p - 1) / 2 - p))

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem mt_glue_val1_le (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D1 s elo : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) (hph : p ≤ P.h N + (p - 1) / 2)
    (hv : P.h N + (p - 1) / 2 - p < p)
    (hs : s * p + 1 ≤ P.H N) (hpη : p ≤ P.H N - 1 - s * p) (hη2 : P.H N - 1 - s * p < 2 * p)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1) (helo : elo ≤ P.H N - 1 - s * p - p + 1)
    (y u : Fin K → ZMod p) (A B : ZMod p) (hy : y ≠ 0) (hu : u ≠ 0)
    (J1 J2 : Finset ℕ)
    (hJ1 : ∀ J, J ∈ J1 →
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J s y = A ∧
      (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J s u = B)
    (hJ2 : ∀ J, J ∈ J2 →
      (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) y +
        (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) u = A + B)
    (hcov1 : ∀ j, P.b N ≤ j → j < P.L N →
      P.H N - 1 - s * p - (P.h N + D1 - 1) ≤ j % p → j / p ∈ J1)
    (hcov2 : ∀ j, P.b N ≤ j → j < P.L N →
      j % p + elo + p ≤ P.H N - 1 - s * p → j / p ∈ J2) :
    mtGlueVal1 P N p s K D1 elo k0 ≤ nullity P N p := by
  have h := mt_glue_one_le_nullity hP hN hp2 hH k0 hD hph hv hs hpη hη2 hdeg helo y u A B hy hu
    J1 J2 hJ1 hJ2 hcov1 hcov2
  unfold mtGlueVal1
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
