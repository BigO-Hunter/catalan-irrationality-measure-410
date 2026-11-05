module
public import Submission.CatalanMeasure.Parametric.WeightedPopulationValue
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Finset
open scoped BigOperators
noncomputable section

theorem populationOneProduct_pos {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0<populationOneProduct P N hpm x y s :=by
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  have hx (i : Fin p) : x i ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.castAdd m i)
  have hx0 (i : Fin p) : x i≠0 :=by simpa using hz0 (Fin.castAdd m i)
  have hy (j : Fin m) : y j ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.natAdd p j)
  have hy0 (j : Fin m) : y j≠0 :=by simpa using hz0 (Fin.natAdd p j)
  have hPow : 0<(∏ j : Fin p, (1+s j))^m :=
    pow_pos (prod_pos (fun j _ =>by linarith only [(hs j).1])) _
  have hZP : 0<∏ i,paramSheetOneWeight P N (z i) :=
    prod_pos (fun i _ =>paramSheetOneWeight_pos P N (hz0 _))
  have hYP : 0<∏ j,paramRowNodeWeight P N (y j) :=
    prod_pos (fun j _ =>paramRowNodeWeight_pos P N (hy j) (hy0 j))
  have hPrincipal :=paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi
  unfold populationOneProduct
  change 0<(∏ j : Fin p,(1+s j))^m*(∏ i,paramSheetOneWeight P N (z i))*
    (∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s/(2:ℝ)^((P.n N).choose 2)
  positivity

theorem populationTwoProduct_pos {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hzi : Function.Injective (fun c : Fin (P.n N) =>Fin.append x y (Fin.cast hpm.symm c))) :
    0<populationTwoProduct P N hpm x y s :=by
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  have hx (i : Fin p) : x i ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.castAdd m i)
  have hx0 (i : Fin p) : x i≠0 :=by simpa using hz0 (Fin.castAdd m i)
  have hy (j : Fin m) : y j ∈ Ioo (-1:ℝ) 1 :=by simpa using hz (Fin.natAdd p j)
  have hy0 (j : Fin m) : y j≠0 :=by simpa using hz0 (Fin.natAdd p j)
  have hPow : 0<(∏ j : Fin p, (1+s j))^m :=
    pow_pos (prod_pos (fun j _ =>by linarith only [(hs j).1])) _
  have hIV : 0 < |∏ i : Fin (P.n N),∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)| :=
    energy_abs_vandermonde_pos (fun i =>(z i)⁻¹) (inv_injective.comp hzi)
  have hZP : 0<∏ i : Fin (P.n N),|z i|^(P.g N) :=
    prod_pos (fun i _ =>pow_pos (abs_pos.mpr (hz0 _)) _)
  have hYP : 0<∏ j,paramRowNodeWeight P N (y j) :=
    prod_pos (fun j _ =>paramRowNodeWeight_pos P N (hy j) (hy0 j))
  have hPrincipal :=paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi
  unfold populationTwoProduct
  change 0<(∏ j : Fin p,(1+s j))^m*|∏ i : Fin (P.n N),∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)| *
    (∏ i : Fin (P.n N),|z i|^(P.g N))*(∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s
  positivity

end
end CatalanMeasure.Parametric
