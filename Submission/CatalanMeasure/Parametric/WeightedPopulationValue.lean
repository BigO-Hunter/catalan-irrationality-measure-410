module
public import Submission.CatalanMeasure.Parametric.PopulationOneLogs
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Finset
open scoped BigOperators
noncomputable section

def populationCommonLog (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)|

def populationEndpointColumnField (P : Parameters) (N : ℕ) (a s : ℝ) : ℝ :=
  (P.b N:ℝ)/(P.n N:ℝ)*Real.log s+(P.q N:ℝ)/(P.n N:ℝ)*Real.log (1-s)+a*Real.log (1+s)

def weightedPopulationOneValue (P : Parameters) (N : ℕ) {p m : ℕ} (a : ℝ)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  freePopulationValueWithFields (P.n N:ℝ) (populationPhysicalOneConstant P N p)
    (populationPhysicalOneFreeField P N)
    (fun u =>populationPhysicalOneFixedField P N u-populationCommonLog P N u/(P.n N:ℝ))
    (populationEndpointColumnField P N a) x y s

def weightedPopulationTwoValue (P : Parameters) (N : ℕ) {p m : ℕ} (a : ℝ)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  populationValueWithFields (P.n N:ℝ) (populationPhysicalConstant P N p)
    (populationPhysicalFreeField P N)
    (fun u =>populationPhysicalFixedField P N u-populationCommonLog P N u/(P.n N:ℝ))
    (populationEndpointColumnField P N a) x y s

theorem freePopulationValue_sub_fixed {ν constant : ℝ} (hν : ν≠0) {p m : ℕ}
    (Fx Fy Fs L : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    ν^2*freePopulationValueWithFields ν constant Fx (fun u =>Fy u-L u/ν) Fs x y s=
      ν^2*freePopulationValueWithFields ν constant Fx Fy Fs x y s-∑ j,L (y j) :=by
  unfold freePopulationValueWithFields
  simp only [sum_sub_distrib,← Finset.sum_div]
  field_simp
  ring

theorem populationValue_sub_fixed {ν constant : ℝ} (hν : ν≠0) {p m : ℕ}
    (Fx Fy Fs L : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    ν^2*populationValueWithFields ν constant Fx (fun u =>Fy u-L u/ν) Fs x y s=
      ν^2*populationValueWithFields ν constant Fx Fy Fs x y s-∑ j,L (y j) :=by
  unfold populationValueWithFields
  simp only [sum_sub_distrib,← Finset.sum_div]
  field_simp
  ring

/-- The exact weighted energy removes precisely the common factors retained
    in the quadrature-weight bound. -/
theorem log_populationOneProduct_weighted {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (populationOneProduct P N hpm x y s)-∑ j,populationCommonLog P N (y j)=
      (P.n N:ℝ)^2*weightedPopulationOneValue P N ((m:ℝ)/(P.n N:ℝ)) x y s :=by
  have hn : (P.n N:ℝ)≠0 :=by exact_mod_cast (n_pos hP hN).ne'
  rw [log_populationOneProduct_physical hP hN hpm x y s hz hz0 hs hxi hsi]
  unfold weightedPopulationOneValue
  rw [freePopulationValue_sub_fixed hn]
  rfl

theorem log_populationTwoProduct_weighted {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hzi : Function.Injective (fun c : Fin (P.n N) =>Fin.append x y (Fin.cast hpm.symm c))) :
    Real.log (populationTwoProduct P N hpm x y s)-∑ j,populationCommonLog P N (y j)=
      (P.n N:ℝ)^2*weightedPopulationTwoValue P N ((m:ℝ)/(P.n N:ℝ)) x y s :=by
  have hn : (P.n N:ℝ)≠0 :=by exact_mod_cast (n_pos hP hN).ne'
  rw [log_populationTwoProduct_physical hP hN hpm x y s hz hz0 hs hxi hsi hzi]
  unfold weightedPopulationTwoValue
  rw [populationValue_sub_fixed hn]
  rfl

end
end CatalanMeasure.Parametric
