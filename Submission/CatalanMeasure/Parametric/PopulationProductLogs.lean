module
public import Submission.CatalanMeasure.Parametric.MixedLogs
public import Submission.CatalanMeasure.Parametric.PopulationMajorant
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan Polynomial
open scoped BigOperators
noncomputable section

theorem log_inverse_vandermonde {n : ℕ} (z : Fin n → ℝ)
    (hz0 : ∀ i,z i≠0) (hzi : Function.Injective z) :
    Real.log |∏ i : Fin n,∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)|=
      (∑ i,∑ j ∈ Ioi i,Real.log |z j-z i|)-
      ((n-1:ℕ):ℝ)*(∑ i,Real.log |z i|) :=by
  have hV :=energy_abs_vandermonde_pos z hzi
  have hD : 0<∏ i,|z i|^(n-1) :=prod_pos fun i _ =>pow_pos (abs_pos.mpr (hz0 i)) _
  rw [abs_vandermonde_inv z hz0,Real.log_div hV.ne' hD.ne',log_abs_vandermonde z hzi,
    Real.log_prod (fun i _ =>pow_ne_zero _ (abs_ne_zero.mpr (hz0 i)))]
  simp only [Real.log_pow,← mul_sum]

/-- An exact log identity before any uniform field estimate is imposed. -/
theorem log_populationTwoProduct {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hzi : Function.Injective (fun c : Fin (P.n N) =>Fin.append x y (Fin.cast hpm.symm c))) :
    let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
    Real.log (populationTwoProduct P N hpm x y s)=
      (m:ℝ)*(∑ j,Real.log (1+s j))+
      (∑ i,∑ j ∈ Ioi i,Real.log |z j-z i|)+
      ((P.g N:ℝ)-((P.n N-1:ℕ):ℝ))*(∑ i,Real.log |z i|)+
      (∑ j,Real.log (paramRowNodeWeight P N (y j)))+Real.log (paramPinPrincipal P N x s) :=by
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  have hzi' : Function.Injective z :=hzi
  have hz0' (i : Fin (P.n N)) : z i≠0 :=hz0 _
  have hx (i : Fin p) : x i ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.castAdd m i)
  have hx0 (i : Fin p) : x i≠0 :=by simpa using hz0 (Fin.castAdd m i)
  have hy (j : Fin m) : y j ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.natAdd p j)
  have hy0 (j : Fin m) : y j≠0 :=by simpa using hz0 (Fin.natAdd p j)
  have hPos (j : Fin p) : 0<1+s j :=by linarith [(hs j).1]
  have hPow : 0<(∏ j : Fin p, (1+s j))^m :=pow_pos (prod_pos fun j _ =>hPos j) _
  have hIV : 0 < |∏ i : Fin (P.n N),∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)| :=
    energy_abs_vandermonde_pos (fun i =>(z i)⁻¹) (inv_injective.comp hzi')
  have hZP : 0<∏ i : Fin (P.n N),|z i|^(P.g N) :=prod_pos fun i _ =>pow_pos (abs_pos.mpr (hz0' i)) _
  have hYP : 0<∏ j,paramRowNodeWeight P N (y j) :=
    prod_pos fun j _ =>paramRowNodeWeight_pos P N (hy j) (hy0 j)
  have hPrincipal :=paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi
  change Real.log ((∏ j : Fin p, (1+s j))^m*
    |∏ i : Fin (P.n N),∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)| *
    (∏ i,|z i|^(P.g N))*(∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s)=_
  rw [Real.log_mul (by positivity) hPrincipal.ne',Real.log_mul (by positivity) hYP.ne',
    Real.log_mul (by positivity) hZP.ne',Real.log_mul hPow.ne' hIV.ne',
    Real.log_pow,Real.log_prod (fun j _ =>(hPos j).ne'),
    log_inverse_vandermonde z hz0' hzi',
    Real.log_prod (fun i _ =>pow_ne_zero _ (abs_ne_zero.mpr (hz0' i))),
    Real.log_prod (fun j _ =>(paramRowNodeWeight_pos P N (hy j) (hy0 j)).ne')]
  simp only [Real.log_pow,← mul_sum]
  ring

end
end CatalanMeasure.Parametric
