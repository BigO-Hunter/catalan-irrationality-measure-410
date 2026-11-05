module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueVal
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (b), `m = 1`, as a certified-window `NullityLB`

`MTGlueOK P N p s K D1 elo k0` collects everything `mt_glue_val1_le` needs: the inequalities between
the design integers and the existence of a profile pair with the equations on explicit digit sets
(the *cell certificate* for the pair `(N, p)`).  `mtGlueLB` is the `NullityLB` that is `mtGlueVal1`
where the certificate holds and `0` elsewhere (`NullityLB.ofWindow`).  Discharging `MTGlueOK` for all
`p` of a window except finitely many is the job of the cell / bad-prime package (Lemma B).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- The certificate of Theorem MT (b) at `(N, p)`. -/
def MTGlueOK (P : Parameters) (N p s K D1 elo : ℕ) (k0 : ℤ) [Fact p.Prime] : Prop :=
  D1 ≤ (p - 1) / 2 ∧ p ≤ P.h N + (p - 1) / 2 ∧ P.h N + (p - 1) / 2 - p < p ∧
    s * p + 1 ≤ P.H N ∧ p ≤ P.H N - 1 - s * p ∧ P.H N - 1 - s * p < 2 * p ∧
    P.h N + D1 ≤ (P.H N - 1 - s * p) + 1 ∧ elo ≤ P.H N - 1 - s * p - p + 1 ∧
    ∃ (y u : Fin K → ZMod p) (A B : ZMod p) (J1 J2 : Finset ℕ), y ≠ 0 ∧ u ≠ 0 ∧
      (∀ J, J ∈ J1 →
        (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J s y = A ∧
        (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J s u = B) ∧
      (∀ J, J ∈ J2 →
        (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) y +
          (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K).psi (P.H N) J ((s : ℤ) + 1) u = A + B) ∧
      (∀ j, P.b N ≤ j → j < P.L N →
        P.H N - 1 - s * p - (P.h N + D1 - 1) ≤ j % p → j / p ∈ J1) ∧
      (∀ j, P.b N ≤ j → j < P.L N → j % p + elo + p ≤ P.H N - 1 - s * p → j / p ∈ J2)

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem mtGlueVal1_le_of_ok (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {s K D1 elo : ℕ} {k0 : ℤ} (h : MTGlueOK P N p s K D1 elo k0) :
    mtGlueVal1 P N p s K D1 elo k0 ≤ nullity P N p := by
  obtain ⟨hD, hph, hv, hs, hpη, hη2, hdeg, helo, y, u, A, B, J1, J2, hy, hu, hJ1, hJ2, hc1, hc2⟩ := h
  exact mt_glue_val1_le hP hN hp2 hH k0 hD hph hv hs hpη hη2 hdeg helo y u A B hy hu J1 J2
    hJ1 hJ2 hc1 hc2

/-- **`mtGlueLB`**: Theorem MT (b), one profile pair, for a fixed window `(s, K, D1, elo, k0)`,
valid at the primes where the cell certificate holds. -/
def mtGlueLB (P : Parameters) (hP : Admissible P) (s K D1 elo : ℕ) (k0 : ℤ) : NullityLB P :=
  NullityLB.ofWindow P
    (fun N p => ∃ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩; MTGlueOK P N p s K D1 elo k0)
    (fun N p => open Classical in
      if hp : p.Prime then haveI : Fact p.Prime := ⟨hp⟩; mtGlueVal1 P N p s K D1 elo k0 else 0)
    (fun N p hN hp hp2 hH hApp => by
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp', hok⟩ := hApp
      simp only [dif_pos hp]
      exact mtGlueVal1_le_of_ok hP hN hp2 hH hok)

#print axioms mtGlueLB

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
