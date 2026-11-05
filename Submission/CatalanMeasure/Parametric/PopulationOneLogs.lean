module
public import Submission.CatalanMeasure.Parametric.PopulationPhysicalValue
public import Submission.CatalanMeasure.FreePopulationFields
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan Polynomial
open scoped BigOperators
noncomputable section

theorem paramSheetOneWeight_pos (P : Parameters) (N : ℕ) {x : ℝ} (hx0 : x≠0) :
    0<paramSheetOneWeight P N x :=by
  unfold paramSheetOneWeight
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (zpow_pos (abs_pos.mpr hx0) _)

theorem log_paramSheetOneWeight (P : Parameters) (N : ℕ) {x : ℝ} (hx0 : x≠0) :
    Real.log (paramSheetOneWeight P N x)=
      ((P.n N:ℝ)-1)/2*Real.log (1+x^2)+
      ((P.g N:ℝ)-((P.n N-1:ℕ):ℝ))*Real.log |x| :=by
  unfold paramSheetOneWeight
  rw [Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne'
    (zpow_pos (abs_pos.mpr hx0) _).ne',Real.log_rpow (by positivity),Real.log_zpow]
  push_cast
  rfl

theorem log_populationOneProduct {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
    Real.log (populationOneProduct P N hpm x y s)=
      (m:ℝ)*(∑ j,Real.log (1+s j))+
      (∑ i,Real.log (paramSheetOneWeight P N (z i)))+
      (∑ j,Real.log (paramRowNodeWeight P N (y j)))+
      Real.log (paramPinPrincipal P N x s)-((P.n N).choose 2:ℝ)*Real.log 2 :=by
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  have hz0' (i : Fin (P.n N)) : z i≠0 :=hz0 _
  have hx (i : Fin p) : x i ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.castAdd m i)
  have hx0 (i : Fin p) : x i≠0 :=by simpa using hz0 (Fin.castAdd m i)
  have hy (j : Fin m) : y j ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.natAdd p j)
  have hy0 (j : Fin m) : y j≠0 :=by simpa using hz0 (Fin.natAdd p j)
  have hPos (j : Fin p) : 0<1+s j :=by linarith [(hs j).1]
  have hPow : 0<(∏ j : Fin p,(1+s j))^m :=pow_pos (prod_pos fun j _ =>hPos j) _
  have hZP : 0<∏ i,paramSheetOneWeight P N (z i) :=
    prod_pos fun i _ =>paramSheetOneWeight_pos P N (hz0' i)
  have hYP : 0<∏ j,paramRowNodeWeight P N (y j) :=
    prod_pos fun j _ =>paramRowNodeWeight_pos P N (hy j) (hy0 j)
  have hPrincipal :=paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi
  change Real.log ((∏ j : Fin p,(1+s j))^m*(∏ i,paramSheetOneWeight P N (z i))*
    (∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s/
    (2:ℝ)^((P.n N).choose 2))=_
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) hPrincipal.ne',
    Real.log_mul (by positivity) hYP.ne',Real.log_mul hPow.ne' hZP.ne',
    Real.log_pow,Real.log_prod (fun j _ =>(hPos j).ne'),
    Real.log_prod (fun i _ =>(paramSheetOneWeight_pos P N (hz0' i)).ne'),
    Real.log_prod (fun j _ =>(paramRowNodeWeight_pos P N (hy j) (hy0 j)).ne'),Real.log_pow]

def populationPhysicalOneConstant (P : Parameters) (N p : ℕ) : ℝ :=
  populationPhysicalConstant P N p-((P.n N:ℝ)-1)/(2*(P.n N:ℝ))*Real.log 2

def populationPhysicalOneFreeField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  paramPopulationRowField P N 1 x+3/(2*(P.n N:ℝ))*Real.log (1+x^2)

def populationPhysicalOneFixedField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  paramPopulationRowField P N 1 x+1/(2*(P.n N:ℝ))*Real.log (1+x^2)

set_option maxHeartbeats 1200000 in
/-- The first-sheet physical product has exactly the free-population energy. -/
theorem log_populationOneProduct_physical {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (populationOneProduct P N hpm x y s)=
      (P.n N:ℝ)^2*freePopulationValueWithFields (P.n N:ℝ) (populationPhysicalOneConstant P N p)
        (populationPhysicalOneFreeField P N) (populationPhysicalOneFixedField P N)
        (populationPhysicalColumnField P N m) x y s :=by
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  have hx (i : Fin p) : x i ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.castAdd m i)
  have hx0 (i : Fin p) : x i≠0 :=by simpa using hz0 (Fin.castAdd m i)
  have hy (j : Fin m) : y j ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.natAdd p j)
  have hy0 (j : Fin m) : y j≠0 :=by simpa using hz0 (Fin.natAdd p j)
  have hz0' (i : Fin (P.n N)) : z i≠0 :=hz0 _
  have hZsum (F : ℝ → ℝ) : (∑ i : Fin (P.n N),F (z i))=
      (∑ i : Fin p,F (x i))+(∑ j : Fin m,F (y j)) :=by
    rw [show (∑ i : Fin (P.n N),F (z i))=
      ∑ i : Fin (p+m),F (Fin.append x y i) from
        sum_fin_cast hpm (fun i =>F (Fin.append x y i)),Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right]
  have hlog :=log_populationOneProduct hP hN hpm x y s hz hz0 hs hxi hsi
  change Real.log (populationOneProduct P N hpm x y s)=
    (m:ℝ)*(∑ j,Real.log (1+s j))+(∑ i,Real.log (paramSheetOneWeight P N (z i)))+
    (∑ j,Real.log (paramRowNodeWeight P N (y j)))+Real.log (paramPinPrincipal P N x s)-
    ((P.n N).choose 2:ℝ)*Real.log 2 at hlog
  rw [hlog,log_paramPinPrincipal hP hN x s hx hs hx0 hxi hsi]
  simp_rw [log_paramSheetOneWeight P N (hz0' _),log_paramRowNodeWeight P N (hy _) (hy0 _)]
  simp only [sum_add_distrib,← mul_sum]
  rw [hZsum (fun u =>Real.log (1+u^2)),hZsum (fun u =>Real.log |u|)]
  have hn0 :=n_pos hP hN
  have hg :=two_g_lt_n hP hN
  have hn : (P.n N:ℝ)≠0 :=by exact_mod_cast hn0.ne'
  have hn1 : 1 ≤ P.n N :=by omega
  have hC1 : 1 ≤ P.C N :=by unfold Parameters.C Parameters.L;omega
  have hH2 : 2 ≤ P.H N :=by
    have hb : 0<P.b N :=Nat.mul_pos hP.2.1 hN
    unfold Parameters.H Parameters.C Parameters.L
    omega
  have hm : (m:ℝ)=(P.n N:ℝ)-(p:ℝ) :=by
    have hh : (p:ℝ)+(m:ℝ)=(P.n N:ℝ) :=by exact_mod_cast hpm
    linarith
  have hCR : (P.C N:ℝ)=(P.A N:ℝ)+(P.n N:ℝ)-(P.g N:ℝ) :=by
    rw [C_eq_A_add_residual hP hN,Nat.cast_add,Nat.cast_sub (by omega : P.g N ≤ P.n N)]
    ring
  have hHR : (P.H N:ℝ)=(P.C N:ℝ)+(P.h N:ℝ) :=by
    change ((P.C N+P.h N:ℕ):ℝ)=_
    exact Nat.cast_add _ _
  unfold freePopulationValueWithFields populationPhysicalOneConstant populationPhysicalConstant
    populationPhysicalOneFreeField populationPhysicalOneFixedField populationPhysicalColumnField
    paramPopulationRowField pinOffDiagonalInteraction
  norm_num only [show ((1:ℝ)-2)/2=-(1/2:ℝ) by norm_num]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,← Finset.sum_div,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,
    Nat.cast_sub hn1,Nat.cast_sub hC1,Nat.cast_sub hH2,Nat.cast_one,Nat.cast_ofNat,
    Nat.cast_choose_two]
  rw [hm,hHR,hCR]
  field_simp
  ring

end
end CatalanMeasure.Parametric
