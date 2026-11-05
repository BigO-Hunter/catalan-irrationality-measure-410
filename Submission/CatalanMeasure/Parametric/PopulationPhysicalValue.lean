module
public import Submission.CatalanMeasure.Parametric.PopulationProductLogs
public import Submission.CatalanMeasure.Parametric.PopulationFixedFields
public import Submission.CatalanMeasure.PopulationFields
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan Polynomial
open scoped BigOperators
noncomputable section

theorem sum_Ioi_fin_cast {a b : ℕ} (h : a=b) (F : Fin a → Fin a → ℝ) :
    (∑ i : Fin b,∑ j ∈ Ioi i,F (Fin.cast h.symm i) (Fin.cast h.symm j))=
      ∑ i : Fin a,∑ j ∈ Ioi i,F i j :=by subst b;rfl

def populationPhysicalConstant (P : Parameters) (N p : ℕ) : ℝ :=
  (((P.C N-1:ℕ):ℝ)/(P.n N:ℝ)+(p:ℝ)*((p:ℝ)-1)/(2*(P.n N:ℝ)^2))*Real.log 2

def populationPhysicalFreeField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  paramPopulationRowField P N 2 x+2/(P.n N:ℝ)*Real.log (1+x^2)

def populationPhysicalFixedField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  paramPopulationRowField P N 2 x+1/(P.n N:ℝ)*Real.log (1+x^2)

def populationPhysicalColumnField (P : Parameters) (N m : ℕ) (s : ℝ) : ℝ :=
  (P.b N:ℝ)/(P.n N:ℝ)*Real.log s+(P.q N:ℝ)/(P.n N:ℝ)*Real.log (1-s)+
    (m:ℝ)/(P.n N:ℝ)*Real.log (1+s)

set_option maxHeartbeats 1200000 in
/-- The normalized population energy is exactly the log of the actual majorant. -/
theorem log_populationTwoProduct_physical {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hzi : Function.Injective (fun c : Fin (P.n N) =>Fin.append x y (Fin.cast hpm.symm c))) :
    Real.log (populationTwoProduct P N hpm x y s)=
      (P.n N:ℝ)^2*populationValueWithFields (P.n N:ℝ) (populationPhysicalConstant P N p)
        (populationPhysicalFreeField P N) (populationPhysicalFixedField P N)
        (populationPhysicalColumnField P N m) x y s :=by
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  have hPair : (∑ i : Fin (P.n N),∑ j ∈ Ioi i,Real.log |z j-z i|)=
      ∑ i : Fin (p+m),∑ j ∈ Ioi i,Real.log |Fin.append x y j-Fin.append x y i| :=
    sum_Ioi_fin_cast hpm (fun i j =>Real.log |Fin.append x y j-Fin.append x y i|)
  have hZsum : (∑ i : Fin (P.n N),Real.log |z i|)=
      (∑ i : Fin p,Real.log |x i|)+(∑ j : Fin m,Real.log |y j|) :=by
    rw [show (∑ i : Fin (P.n N),Real.log |z i|)=
      ∑ i : Fin (p+m),Real.log |Fin.append x y i| from
        sum_fin_cast hpm (fun i =>Real.log |Fin.append x y i|),Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right]
  have hx (i : Fin p) : x i ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.castAdd m i)
  have hx0 (i : Fin p) : x i≠0 :=by simpa using hz0 (Fin.castAdd m i)
  have hy (j : Fin m) : y j ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.natAdd p j)
  have hy0 (j : Fin m) : y j≠0 :=by simpa using hz0 (Fin.natAdd p j)
  have hlog :=log_populationTwoProduct hP hN hpm x y s hz hz0 hs hxi hsi hzi
  change Real.log (populationTwoProduct P N hpm x y s)=
    (m:ℝ)*(∑ j,Real.log (1+s j))+(∑ i,∑ j ∈ Ioi i,Real.log |z j-z i|)+
    ((P.g N:ℝ)-((P.n N-1:ℕ):ℝ))*(∑ i,Real.log |z i|)+
    (∑ j,Real.log (paramRowNodeWeight P N (y j)))+Real.log (paramPinPrincipal P N x s) at hlog
  rw [hlog,hPair,hZsum,log_paramPinPrincipal hP hN x s hx hs hx0 hxi hsi]
  simp_rw [log_paramRowNodeWeight P N (hy _) (hy0 _)]
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
  unfold populationValueWithFields populationPhysicalConstant populationPhysicalFreeField
    populationPhysicalFixedField populationPhysicalColumnField paramPopulationRowField
    populationOffDiagonalInteraction pinOffDiagonalInteraction
  norm_num only [show ((2:ℝ)-2)/2=0 by norm_num,add_zero]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,← Finset.sum_div,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,
    Nat.cast_sub hn1,Nat.cast_sub hC1,Nat.cast_sub hH2,Nat.cast_one,Nat.cast_ofNat,
    Nat.cast_choose_two]
  rw [hm,hHR,hCR]
  field_simp
  ring

end
end CatalanMeasure.Parametric
