module
public import Submission.CatalanMeasure.Parametric.LowRankPole
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- An actual factorization of the leading residue gives a determinant saving.
The hypothesis concerns every entry, rather than selected determinant values. -/
theorem residue_factorization_valuation_lower {p n r : ℕ} [hp : Fact p.Prime]
    (M : Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin r) ℚ)
    (B : Matrix (Fin r) (Fin n) ℚ)
    (hM : ∀ i j,(((p:ℚ)^2*M i j).den:ZMod p)≠0)
    (hA : ∀ i j,((A i j).den:ZMod p)≠0)
    (hB : ∀ i j,((B i j).den:ZMod p)≠0)
    (hres : ∀ i j,palindromicRatResidue p ((p:ℚ)^2*M i j)=
      ∑ k,palindromicRatResidue p (A i k)*palindromicRatResidue p (B k j)) :
    -((n+min n r:ℕ):ℤ)≤padicValRat p M.det := by
  have hAB (i j) : (((A*B) i j).den:ZMod p)≠0 := by
    rw [Matrix.mul_apply]
    exact (rational_residue_sum univ (fun k =>A i k*B k j)
      (fun k _ =>(rational_residue_mul (hA i k) (hB k j)).1)).1
  have hABres (i j) : palindromicRatResidue p ((A*B) i j)=
      ∑ k,palindromicRatResidue p (A i k)*palindromicRatResidue p (B k j) := by
    rw [Matrix.mul_apply,palindromicRatResidue_sum univ (fun k =>A i k*B k j)
      (fun k _ =>(rational_residue_mul (hA i k) (hB k j)).1)]
    apply sum_congr rfl
    intro k _
    exact palindromicRatResidue_mul (hA i k) (hB k j)
  let C : Matrix (Fin n) (Fin n) ℚ :=Matrix.of fun i j =>
    ((p:ℚ)^2*M i j-(A*B) i j)/(p:ℚ)
  have hC : ∀ i j,((C i j).den:ZMod p)≠0 := by
    intro i j
    have hd :=(rational_residue_sub (hM i j) (hAB i j)).1
    have hz : palindromicRatResidue p ((p:ℚ)^2*M i j-(A*B) i j)=0 := by
      rw [palindromicRatResidue_sub (hM i j) (hAB i j),hres i j,hABres i j,sub_self]
    exact rational_div_prime_den_ne_zero_of_residue_zero hd hz
  have hpq : (p:ℚ)≠0 :=by exact_mod_cast hp.out.ne_zero
  apply doublePole_valuation_lower M C A B hC hA hB
  ext i j
  simp only [lowRankPoleMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,C,Matrix.of_apply]
  field_simp
  <;> ring

end
end CatalanMeasure.Parametric
