module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueFinal
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (b), one profile pair (`m = 1`)

The case used with a fixed rational cell: one pair `(y, u)` with `y ≠ 0`, `u ≠ 0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- **Theorem MT (b), `m = 1`**: `2 D1 + 1 - (η - p + 1) - elo - V - r ≤ ν`. -/
theorem mt_glue_one_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
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
    D1 + (D1 + 1) ≤ nullity P N p +
      ((P.H N - 1 - s * p - p + 1) + elo + mixMiss P N p K D1 k0) +
        (p - P.q N - (P.h N + (p - 1) / 2 - p)) := by
  have h := mt_glue_le_nullity hP hN hp2 hH (m := 1) (s := s) (elo := elo) k0 hD hph hv hs hpη hη2
    hdeg helo (fun _ => y) (fun _ => u) (fun _ => A) (fun _ => B)
    (linearIndependent_unique_iff.mpr hy) (linearIndependent_unique_iff.mpr hu) J1 J2
    (fun _ J hJ => hJ1 J hJ) (fun _ J hJ => hJ2 J hJ) hcov1 hcov2
  simpa [mul_add, add_assoc] using h

#print axioms mt_glue_le_nullity
#print axioms mt_glue_one_le_nullity

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
