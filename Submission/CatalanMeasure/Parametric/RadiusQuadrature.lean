module
public import Submission.CatalanMeasure.Parametric.ResidualCircle
public import Submission.CatalanMeasure.Parametric.RadiusCoefficients
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Polynomial.Chebyshev Finset
noncomputable section

theorem norm_quadBasis_eval_radius_le {J : ℕ} (a : Fin J) (t : ℂ) {r : ℝ}
    (hr : 1<r) (ht : ‖t‖=r) :
    ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode J) a).map
      (algebraMap ℝ ℂ)).eval t‖ ≤
      ‖(T ℂ (J:ℤ)).eval (2*t+1)‖ / (2*J*(r-1)) := by
  have hJ : 0<J := by have := a.isLt; omega
  have hJR : (0:ℝ)<J := by exact_mod_cast hJ
  rw [OAI.InternalCatalan.quadBasis_eq, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_prod, eval_mul,eval_C,eval_prod]
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,eval_sub,eval_X,eval_C]
  set D := ∏ c ∈ univ.erase a,
    (CatalanMeasure.chebNode J a-CatalanMeasure.chebNode J c) with hD
  have hDge := CatalanMeasure.chebNode_den_ge a
  have hD0 : 0 < |D| := lt_of_lt_of_le (by positivity) hDge
  have hτ := CatalanMeasure.chebNode_mem a
  have hdist : r-1 ≤ ‖t-(CatalanMeasure.chebNode J a:ℂ)‖ := by
    have hh := norm_sub_norm_le t (CatalanMeasure.chebNode J a:ℂ)
    rw [ht,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hτ.2] at hh
    linarith [hτ.1]
  have hdpos : 0<‖t-(CatalanMeasure.chebNode J a:ℂ)‖ :=
    lt_of_lt_of_le (sub_pos.mpr hr) hdist
  have hfull := CatalanMeasure.nodal_eval_complex hJ t
  rw [← Finset.prod_erase_mul _ _ (mem_univ a)] at hfull
  have hmap : (algebraMap ℝ ℂ) (∏ c ∈ univ.erase a,
      (CatalanMeasure.chebNode J a-CatalanMeasure.chebNode J c)⁻¹) =
      ((D⁻¹:ℝ):ℂ) := by rw [hD,← prod_inv_distrib]; simp
  rw [hmap,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_inv]
  have hprod : ‖∏ c ∈ univ.erase a, (t-(CatalanMeasure.chebNode J c:ℂ))‖ =
      ‖(T ℂ (J:ℤ)).eval (2*t+1)‖ / (2^J*2^(J-1)) /
      ‖t-(CatalanMeasure.chebNode J a:ℂ)‖ := by
    have hh := congrArg norm hfull
    rw [norm_mul,norm_div,norm_mul,norm_pow,norm_pow,Complex.norm_ofNat] at hh
    rw [eq_div_iff hdpos.ne',hh]
  simp only [Complex.coe_algebraMap]
  rw [hprod]
  have hinvD : |D|⁻¹ ≤ 2^(J-1)*2^(J-1)/J := by
    rw [inv_le_comm₀ hD0 (by positivity),inv_div]
    exact hDge
  have hinvd : ‖t-(CatalanMeasure.chebNode J a:ℂ)‖⁻¹ ≤ (r-1)⁻¹ := by
    exact (inv_le_inv₀ hdpos (sub_pos.mpr hr)).mpr hdist
  have hJpow : (2:ℝ)^J = 2*2^(J-1) := by rw [← pow_succ']; congr 1; omega
  calc _ = |D|⁻¹ * ‖t-(CatalanMeasure.chebNode J a:ℂ)‖⁻¹ *
      (‖(T ℂ (J:ℤ)).eval (2*t+1)‖ / (2^J*2^(J-1))) := by ring
    _ ≤ (2^(J-1)*2^(J-1)/J) * (r-1)⁻¹ *
      (‖(T ℂ (J:ℤ)).eval (2*t+1)‖ / (2^J*2^(J-1))) := by gcongr
    _ = ‖(T ℂ (J:ℤ)).eval (2*t+1)‖ / (2*J*(r-1)) := by
      rw [hJpow]
      field_simp <;> ring

/-- Uniform circle bound for the residual interpolation basis with the entire
shared nonmonomial factor and filter retained. -/
theorem norm_restricted_filtered_basis_le (N : ℕ) (a : Fin (89*N)) (t : ℂ)
    (ht : ‖t‖=(residualRadius:ℝ)) :
    ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a *
      (1-X)^(12*N)).map (algebraMap ℝ ℂ)).eval t‖ ≤
      500*(residualCircleK:ℝ)^N := by
  have hr : 1<(residualRadius:ℝ) := by norm_num [residualRadius]
  have hJ : (1:ℝ) ≤ (89*N:ℕ) := by exact_mod_cast (show 1≤89*N by have := a.isLt; omega)
  set s : ℝ := ‖t+1‖ with hs
  have hs0 : 0≤s := norm_nonneg _
  have hslow : (residualRadius:ℝ)-1 ≤ s := by
    have hh := norm_sub_norm_le t (-1:ℂ)
    simpa [ht,hs] using hh
  have hs2 : s≤(residualRadius:ℝ)+1 := by
    have hh := norm_add_le t 1
    simpa [ht,hs] using hh
  have hpar : ‖1-t‖^2 = 2*((residualRadius:ℝ)^2+1)-s^2 := by
    have hh := parallelogram_law_with_norm ℝ t (1:ℂ)
    rw [ht,norm_one,← hs,norm_sub_rev] at hh
    nlinarith
  have hz1 : ‖(2*t+1)-1‖=2*(residualRadius:ℝ) := by
    rw [show (2*t+1)-1=2*t by ring,norm_mul,ht]
    norm_num
  have hz2 : ‖(2*t+1)+1‖=2*s := by
    rw [show (2*t+1)+1=2*(t+1) by ring,norm_mul,← hs]
    norm_num
  set B := (residualRadius:ℝ)+s+Real.sqrt (((residualRadius:ℝ)+s)^2-1) with hB
  have hB0 : 0≤B := by
    dsimp [B]
    have hh : (0:ℝ)≤residualRadius := by norm_num [residualRadius]
    positivity
  have hT := CatalanMeasure.norm_T_eval_le (89*N) (2*t+1)
  rw [hz1,hz2,show (2*(residualRadius:ℝ)+2*s)/2=(residualRadius:ℝ)+s by ring,
    ← hB] at hT
  have hKfull := residualCircle_ineq hslow hs2
  rw [← hB,← hpar] at hKfull
  have hrad : 1≤(residualRadius:ℝ)^14 := one_le_pow₀ hr.le
  have hK : B^89*(‖1-t‖^2)^6 ≤ (residualCircleK:ℝ) := by
    exact (le_mul_of_one_le_right (by positivity) hrad).trans hKfull
  have hl := norm_quadBasis_eval_radius_le a t hr ht
  have hl' : ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).map
      (algebraMap ℝ ℂ)).eval t‖ ≤ 500*‖(T ℂ ((89*N:ℕ):ℤ)).eval (2*t+1)‖ := by
    apply hl.trans
    have hd : (0:ℝ)<2*(89*N:ℕ)*((residualRadius:ℝ)-1) := by
      exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hJ)) (sub_pos.mpr hr)
    apply (div_le_iff₀ hd).mpr
    have hh : (500:ℝ)*(2*(89*N:ℕ)*((residualRadius:ℝ)-1)) = (89*N:ℕ) := by
      norm_num [residualRadius]
      ring
    calc
      _ ≤ (89*N:ℕ)*‖(T ℂ ((89*N:ℕ):ℤ)).eval (2*t+1)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hJ
      _ = (500*‖(T ℂ ((89*N:ℕ):ℤ)).eval (2*t+1)‖) *
          (2*(89*N:ℕ)*((residualRadius:ℝ)-1)) := by
            nth_rw 1 [← hh]
            ring
  rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_X,eval_mul,eval_pow,eval_sub,eval_one,eval_X,norm_mul,norm_pow]
  have e1 : ‖1-t‖^(12*N)=((‖1-t‖^2)^6)^N := by
    rw [← pow_mul,← pow_mul]
    congr 1
    ring
  have e2 : B^(89*N)=(B^89)^N := pow_mul B 89 N
  calc
    _ ≤ (500*B^(89*N))*‖1-t‖^(12*N) := by
        exact mul_le_mul_of_nonneg_right
          (hl'.trans (mul_le_mul_of_nonneg_left hT (by norm_num))) (by positivity)
    _ = 500*(B^89*(‖1-t‖^2)^6)^N := by rw [e1,e2,mul_pow,mul_assoc]
    _ ≤ 500*(residualCircleK:ℝ)^N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hK N) (by norm_num)

end
end CatalanMeasure.Parametric
