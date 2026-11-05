module
public import Submission.CatalanMeasure.PopulationDual
@[expose] public section
namespace OAI.InternalCatalan
open Set Finset Real
open scoped BigOperators
noncomputable section

def populationValueWithFields (ν constant : ℝ) {p m : ℕ}
    (Fx Fy Fs : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  constant+(∑ i,Fx (x i))/ν+(∑ j,Fy (y j))/ν+(∑ j,Fs (s j))/ν+
    populationOffDiagonalInteraction ν x y s

/-- A full-population dual with the actual finite diagonal corrections in its field hypotheses. -/
theorem population_fields_dual_bound {ν e constant Bx By Bs Kn : ℝ}
    (hν : 0<ν) (he : e ∈ Ioo (0:ℝ) (1/8)) {p m : ℕ}
    (hpm : ((p+m:ℕ):ℝ) ≤ ν)
    (Fx Fy Fs : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i,x i ∈ Ioo (-1:ℝ) 1) (hy : ∀ j,y j ∈ Ioo (-1:ℝ) 1)
    (hs : ∀ j,s j ∈ Ioo (0:ℝ) 1)
    (hzi : Function.Injective (Fin.append x y)) (hsi : Function.Injective s)
    (pp v : ℕ → ℝ) (hpp : Summable (fun j =>|pp j|)) (hv : Summable (fun j =>|v j|))
    (hKn : 2*barrierTrialNormSq pp+barrierTrialNormSq v/2 ≤ Kn)
    (hFx : ∀ i,Fx (x i)-4*barrierTrialT pp (x i)-barrierTrialS v (x i)-
      Real.log (1-x i)/(2*ν) ≤ Bx)
    (hFy : ∀ j,Fy (y j)-2*barrierTrialT pp (y j) ≤ By)
    (hFs : ∀ j,Fs (s j)+2*barrierTrialT v (s j)-Real.log (1-s j)/ν ≤ Bs) :
    populationValueWithFields ν constant Fx Fy Fs x y s ≤
      constant-(3/2:ℝ)*((p:ℝ)/ν)^2*Real.log 2-
      (1/2:ℝ)*(((p+m:ℕ):ℝ)/ν)^2*Real.log 2+Kn+
      ((p:ℝ)/ν)*(Bx+Bs)+((m:ℝ)/ν)*By+
      4*e*(∑' j,|pp j|)+4*e*(∑' j,|v j|)+populationRegularizationError ν e :=by
  have hDual :=population_undamped_canonical_bound hν he hpm hx hy hs hzi hsi pp v hpp hv
  have hRow :=sum_le_sum (s :=(univ:Finset (Fin p))) (fun i _ =>hFx i)
  have hFixed :=sum_le_sum (s :=(univ:Finset (Fin m))) (fun j _ =>hFy j)
  have hColumn :=sum_le_sum (s :=(univ:Finset (Fin p))) (fun j _ =>hFs j)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hRow hFixed hColumn
  have hRow' :=div_le_div_of_nonneg_right hRow hν.le
  have hFixed' :=div_le_div_of_nonneg_right hFixed hν.le
  have hColumn' :=div_le_div_of_nonneg_right hColumn hν.le
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,← Finset.sum_div] at hRow' hFixed' hColumn' hDual
  unfold populationValueWithFields
  ring_nf at hRow' hFixed' hColumn' hDual ⊢
  linarith only [hRow',hFixed',hColumn',hDual,hKn]

/-- The column weight is interpolated exactly, before applying either dual certificate. -/
theorem population_column_affine (ν constant t : ℝ) {p m : ℕ}
    (Fx Fy Fs L : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    populationValueWithFields ν constant Fx Fy (fun z =>Fs z+t*L z) x y s=
      (1-t)*populationValueWithFields ν constant Fx Fy Fs x y s+
      t*populationValueWithFields ν constant Fx Fy (fun z =>Fs z+L z) x y s :=by
  unfold populationValueWithFields
  simp only [sum_add_distrib,← mul_sum]
  ring

theorem population_column_endpoint_bound {ν constant t B₀ B₁ : ℝ} (ht : 0≤t) (ht1 : t≤1)
    {p m : ℕ} (Fx Fy Fs L : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (h₀ : populationValueWithFields ν constant Fx Fy Fs x y s≤B₀)
    (h₁ : populationValueWithFields ν constant Fx Fy (fun z =>Fs z+L z) x y s≤B₁) :
    populationValueWithFields ν constant Fx Fy (fun z =>Fs z+t*L z) x y s≤(1-t)*B₀+t*B₁ :=by
  rw [population_column_affine]
  exact add_le_add (mul_le_mul_of_nonneg_left h₀ (by linarith))
    (mul_le_mul_of_nonneg_left h₁ ht)

/-- The full-population missing-mass cost is a quadratic, with the fixed fields retained. -/
theorem population_endpoint_quadratic (K₀ K₁ B₀ B₁ Y₀ Y₁ t : ℝ) :
    (1-t)*(K₀+(1-t)*B₀+t*Y₀)+t*(K₁+(1-t)*B₁+t*Y₁)+(2*t-t^2)*Real.log 2=
      K₀+B₀+t*(K₁-K₀+B₁-2*B₀+Y₀+2*Real.log 2)+
      t^2*(B₀-B₁+Y₁-Y₀-Real.log 2) :=by ring

end
end OAI.InternalCatalan
