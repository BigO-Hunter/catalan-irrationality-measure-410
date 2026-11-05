module
public import Submission.CatalanMeasure.Parametric.FirstSheetBounds
public import Submission.CatalanMeasure.PopulationDual
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def paramCaseField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  2*(P.g N:ℝ)/(P.n N:ℝ)-2*x^2/(1+x^2)

theorem paramCaseField_sum {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N)
    (z : Fin (P.n N) → ℝ) :
    (∑ i,paramCaseField P N (z i))=
      (∑ i,(1-z i^2)/(1+z i^2))-((P.n N:ℝ)-2*(P.g N:ℝ)) :=by
  have hn : (P.n N:ℝ)≠0 :=by exact_mod_cast (n_pos hP hN).ne'
  have he (x : ℝ) : paramCaseField P N x=
      (1-x^2)/(1+x^2)-(1-2*(P.g N:ℝ)/(P.n N:ℝ)) :=by
    unfold paramCaseField
    field_simp
    ring
  simp_rw [he,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp <;> ring

/-- The complementary first-sheet case yields the exact finite case constraint used by the dual. -/
theorem paramCaseField_first_case {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N)
    (z : Fin (P.n N) → ℝ)
    (hcase : ((P.n N-1-2*P.g N:ℕ):ℝ)<∑ i,(1-z i^2)/(1+z i^2)) :
    -(1:ℝ)<∑ i,paramCaseField P N (z i) :=by
  have hn :=n_pos hP hN
  have hg :=two_g_lt_n hP hN
  have he : ((P.n N-1-2*P.g N:ℕ):ℝ)=(P.n N:ℝ)-1-2*(P.g N:ℝ) :=by
    rw [Nat.cast_sub (by omega : 2*P.g N ≤ P.n N-1),
      Nat.cast_sub (by omega : 1 ≤ P.n N)]
    push_cast
    ring
  rw [he] at hcase
  rw [paramCaseField_sum hP hN]
  linarith

/-- The nonpositive complementary case field gives the actual second-sheet condition. -/
theorem paramCaseField_second_case {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N)
    (z : Fin (P.n N) → ℝ) (hcase : (∑ i,paramCaseField P N (z i)) ≤ -(1:ℝ)) :
    (∑ i,(1-z i^2)/(1+z i^2)) ≤ ((P.n N-1-2*P.g N:ℕ):ℝ) :=by
  have hn :=n_pos hP hN
  have hg :=two_g_lt_n hP hN
  have he : ((P.n N-1-2*P.g N:ℕ):ℝ)=(P.n N:ℝ)-1-2*(P.g N:ℝ) :=by
    rw [Nat.cast_sub (by omega : 2*P.g N ≤ P.n N-1),
      Nat.cast_sub (by omega : 1 ≤ P.n N)]
    push_cast
    ring
  rw [paramCaseField_sum hP hN] at hcase
  rw [he]
  linarith only [hcase]

end
end CatalanMeasure.Parametric
