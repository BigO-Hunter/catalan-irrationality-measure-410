module
public import Submission.CatalanMeasure.PopulationFields
@[expose] public section
namespace OAI.InternalCatalan
open Set Finset Real
open scoped BigOperators
noncomputable section

def freePopulationRegularizationError (ν e : ℝ) : ℝ :=
  (Real.log 2-2*Real.log (1-realEnergyTau e^2))/(2*ν)+
  (Real.log 2-Real.log e)/(2*ν)+(Real.log 2-2*Real.log e)/ν+14*e

theorem free_population_regularization {ν e : ℝ} (hν : 0<ν)
    (he : e ∈ Ioo (0:ℝ) (1/8)) {p : ℕ} (hp : (p:ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i,x i ∈ Ioo (-1:ℝ) 1)
    (hs : ∀ j,s j ∈ Ioo (0:ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    pinOffDiagonalInteraction ν 1 x s ≤pinDampedInteraction ν 1 e x s-
      (∑ i,Real.log (1-x i))/(2*ν^2)-(∑ j,Real.log (1-s j))/ν^2+
      freePopulationRegularizationError ν e :=by
  have he0 : 0 ≤ e :=he.1.le
  have hinteraction :=pinOffDiagonalInteraction_le_damped hν (by norm_num : (0:ℝ) ≤ 1) he hx hs hxi hsi
  have htau :=pin_tau_diagonal_sum hν he (by norm_num : (0:ℝ) ≤ 1) hp hx
  have hpower :=pin_power_diagonal_sum hν he hp hx
  have hsigma :=pin_sigma_diagonal_sum hν he hp hs
  have hc : ((p.choose 2:ℕ):ℝ) ≤ ν^2/2 :=by
    rw [Nat.cast_choose_two]
    nlinarith only [hp,hν,(Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hsq : (p:ℝ)^2 ≤ ν^2 :=pow_le_pow_left₀ (Nat.cast_nonneg p) hp 2
  have hpair : 16*e*((p.choose 2:ℕ):ℝ)/ν^2+6*e*(p:ℝ)^2/ν^2 ≤ 14*e :=by
    have h1 :=mul_le_mul_of_nonneg_left hc (show 0 ≤ 16*e by positivity)
    have h2 :=mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6*e by positivity)
    rw [← add_div,div_le_iff₀ (sq_pos_of_pos hν)]
    nlinarith only [h1,h2]
  norm_num only [one_mul,mul_one,Nat.reduceAdd,Nat.reduceMul] at hinteraction htau
  simp only [mul_pow] at hinteraction
  simp only [neg_mul] at htau
  simp only [neg_div] at hpower hsigma
  unfold freePopulationRegularizationError
  ring_nf at hinteraction htau hpower hsigma hpair ⊢
  linarith only [hinteraction,htau,hpower,hsigma,hpair]

theorem free_population_canonical {ν e : ℝ} (hν : 0<ν)
    (he : e ∈ Ioo (0:ℝ) (1/8)) {p : ℕ} (hp : (p:ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i,x i ∈ Ioo (-1:ℝ) 1)
    (hs : ∀ j,s j ∈ Ioo (0:ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (pp v : ℕ → ℝ) (hpp : Summable (fun j =>|pp j|)) (hv : Summable (fun j =>|v j|)) :
    pinOffDiagonalInteraction ν 1 x s ≤-(3/2:ℝ)*((p:ℝ)/ν)^2*Real.log 2+
      barrierTrialNormSq pp+barrierTrialNormSq v/2+
      (∑ i,(-2*barrierTrialT pp (x i)-barrierTrialS v (x i)))/ν+
      (∑ j,2*barrierTrialT v (s j))/ν-
      (∑ i,Real.log (1-x i))/(2*ν^2)-(∑ j,Real.log (1-s j))/ν^2+
      2*e*(∑' j,|pp j|)+4*e*(∑' j,|v j|)+freePopulationRegularizationError ν e :=by
  have hreg :=free_population_regularization hν he hp hx hs hxi hsi
  have hdual :=pinDampedInteraction_le_canonicalTrials hν (by norm_num : (0:ℝ) ≤ 1)
    he hp hx hs pp v hpp hv
  norm_num only [one_mul,mul_one] at hdual
  linarith only [hreg,hdual]

def freePopulationValueWithFields (ν constant : ℝ) {p m : ℕ}
    (Fx Fy Fs : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  constant+(∑ i,Fx (x i))/ν+(∑ j,Fy (y j))/ν+(∑ j,Fs (s j))/ν+
    pinOffDiagonalInteraction ν 1 x s

/-- The first-sheet dual keeps the case constraint coupled to the fixed-node field. -/
theorem free_population_fields_dual_bound {ν e constant Bx By Bs Kn lam : ℝ}
    (hν : 0<ν) (he : e ∈ Ioo (0:ℝ) (1/8)) (hlam : 0 ≤ lam) {p m : ℕ}
    (hp : (p:ℝ) ≤ ν) (Fx Fy Fs D : ℝ → ℝ)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i,x i ∈ Ioo (-1:ℝ) 1) (hs : ∀ j,s j ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : -(1:ℝ)<∑ i : Fin (p+m),D (Fin.append x y i))
    (pp v : ℕ → ℝ) (hpp : Summable (fun j =>|pp j|)) (hv : Summable (fun j =>|v j|))
    (hKn : barrierTrialNormSq pp+barrierTrialNormSq v/2 ≤ Kn)
    (hFx : ∀ i,Fx (x i)+lam*D (x i)-2*barrierTrialT pp (x i)-barrierTrialS v (x i)-
      Real.log (1-x i)/(2*ν) ≤ Bx)
    (hFy : ∀ j,Fy (y j)+lam*D (y j) ≤ By)
    (hFs : ∀ j,Fs (s j)+2*barrierTrialT v (s j)-Real.log (1-s j)/ν ≤ Bs) :
    freePopulationValueWithFields ν constant Fx Fy Fs x y s ≤
      constant-(3/2:ℝ)*((p:ℝ)/ν)^2*Real.log 2+Kn+
      ((p:ℝ)/ν)*(Bx+Bs)+((m:ℝ)/ν)*By+lam/ν+
      2*e*(∑' j,|pp j|)+4*e*(∑' j,|v j|)+freePopulationRegularizationError ν e :=by
  have hDual :=free_population_canonical hν he hp hx hs hxi hsi pp v hpp hv
  have hCouple :=population_case_coupling hν hlam D x y hcase
  have hRow :=sum_le_sum (s :=(univ:Finset (Fin p))) (fun i _ =>hFx i)
  have hFixed :=sum_le_sum (s :=(univ:Finset (Fin m))) (fun j _ =>hFy j)
  have hColumn :=sum_le_sum (s :=(univ:Finset (Fin p))) (fun j _ =>hFs j)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hRow hFixed hColumn
  have hRow' :=div_le_div_of_nonneg_right hRow hν.le
  have hFixed' :=div_le_div_of_nonneg_right hFixed hν.le
  have hColumn' :=div_le_div_of_nonneg_right hColumn hν.le
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,← Finset.sum_div] at hRow' hFixed' hColumn' hDual
  unfold freePopulationValueWithFields
  ring_nf at hRow' hFixed' hColumn' hDual hCouple ⊢
  linarith only [hRow',hFixed',hColumn',hDual,hKn,hCouple]

end
end OAI.InternalCatalan
