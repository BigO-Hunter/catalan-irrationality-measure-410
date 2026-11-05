module
public import Submission.CatalanMeasure.Parametric.CommonFactor
public import Submission.CatalanMeasure.Quadrature
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset
noncomputable section

def rowCommonFactor (P : Parameters) (N : ℕ) : ℝ[X] :=
  X^(P.A N) * (1-X)^(P.h N)

theorem rowResidual_interpolate {P : Parameters} (hP : Admissible P) {N : ℕ}
    (hN : 0<N) {J : ℕ} (hJ : P.n N-P.g N ≤ J) {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (r : ℕ) :
    OAI.InternalCatalan.realPoly (rowResidualP P N r) =
      ∑ a, C ((OAI.InternalCatalan.realPoly (rowResidualP P N r)).eval (τ a)) *
        OAI.InternalCatalan.quadBasis τ a := by
  have hd := rowResidualP_natDegree_le P N r
  have hg := two_g_lt_n hP hN
  have hdeg : (OAI.InternalCatalan.realPoly (rowResidualP P N r)).degree <
      (#(univ : Finset (Fin J)) : WithBot ℕ) := by
    rw [card_univ,Fintype.card_fin]
    have hn : (OAI.InternalCatalan.realPoly (rowResidualP P N r)).natDegree ≤
        P.n N-P.g N-1 := Polynomial.natDegree_map_le.trans hd
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show
      (OAI.InternalCatalan.realPoly (rowResidualP P N r)).natDegree < J by omega))
  have h := Lagrange.eq_interpolate (s := (univ : Finset (Fin J))) (v := τ)
    (fun x _ y _ hxy => hτ hxy) hdeg
  simpa only [Lagrange.interpolate_apply,OAI.InternalCatalan.quadBasis] using h

/-- Interpolation needs only n-g nodes after removing the shared row factor. -/
theorem rowP_restricted_interpolate {P : Parameters} (hP : Admissible P) {N r : ℕ}
    (hN : 0<N) (hr : r<P.n N) {J : ℕ} (hJ : P.n N-P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ) :
    OAI.InternalCatalan.realPoly (rowP P N r) =
      ∑ a, C ((OAI.InternalCatalan.realPoly (rowResidualP P N r)).eval (τ a)) *
        (rowCommonFactor P N * OAI.InternalCatalan.quadBasis τ a) := by
  rw [rowP_common_factor hP hN hr]
  unfold OAI.InternalCatalan.realPoly
  rw [Polynomial.map_mul]
  have hf : (X^(P.A N)*(1-X)^(P.h N) : ℤ[X]).map (Int.castRingHom ℝ) =
      rowCommonFactor P N := by simp [rowCommonFactor]
  rw [hf]
  change rowCommonFactor P N * OAI.InternalCatalan.realPoly (rowResidualP P N r) = _
  conv_lhs => rw [rowResidual_interpolate hP hN hJ hτ]
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  simp only [OAI.InternalCatalan.realPoly]
  ring

end
end CatalanMeasure.Parametric
