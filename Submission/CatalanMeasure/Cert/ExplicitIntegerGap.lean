module
public import Submission.CatalanMeasure.Cert.IntegerGap
@[expose] public section
namespace CatalanMeasure.Cert
open Set

/-- A supplied common denominator avoids squaring the size of rational endpoints.
The substitution and both endpoint equalities are kernel-checked inputs. -/
theorem noRoot_of_integer_check {A : List ℚ} {Z : List ℤ} {c l h : ℚ}
    {a b d : ℤ} (hc : c≠0)
    (hA : A=lpSmul c (Z.map (fun z : ℤ => (z:ℚ))))
    (hl : (a:ℚ)/d=l) (hr : (b:ℚ)/d=h)
    (hcheck : ipNoRootCheck Z a b d=true) :
    ∀ x ∈ Ioo (l:ℝ) h, lpEval A x≠0 := by
  intro x hx
  have hlR : (a:ℝ)/d=(l:ℝ) := by exact_mod_cast hl
  have hrR : (b:ℝ)/d=(h:ℝ) := by exact_mod_cast hr
  have hn := ipEval_ne_zero_of_noRootCheck hcheck (by rw [hlR,hrR];exact hx)
  rw [hA,lpEval_smul,lpEval_int_cast]
  exact mul_ne_zero (by exact_mod_cast hc) hn

def PieceNoRoot (A : List ℚ) (p : Piece) : Prop :=
  p.2.2=false → ∀ x ∈ Ioo (p.1:ℝ) p.2.1, lpEval A x≠0

theorem noRootGaps_nil (A : List ℚ) : NoRootGaps A [] := by
  intro p hp
  simp at hp

theorem noRootGaps_cons (A : List ℚ) (p : Piece) (ps : List Piece) :
    NoRootGaps A (p::ps) ↔ PieceNoRoot A p ∧ NoRootGaps A ps := by
  constructor
  · intro h
    exact ⟨h p List.mem_cons_self,fun q hq =>h q (List.mem_cons_of_mem p hq)⟩
  · rintro ⟨hp,hps⟩ q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact hp
    · exact hps q hq

end CatalanMeasure.Cert
