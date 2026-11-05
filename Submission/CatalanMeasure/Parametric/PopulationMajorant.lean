module
public import Submission.CatalanMeasure.Parametric.MixedMajorant
public import Submission.CatalanMeasure.Parametric.FirstSheetBounds
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set OAI.InternalCatalan Real
open scoped BigOperators
noncomputable section

def populationTwoProduct (P : Parameters) (N : ℕ) {p m : ℕ} (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  (∏ j, (1+s j))^m*|∏ i : Fin (P.n N),∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)| *
    (∏ i,|z i|^(P.g N))*(∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s

/-- The actual generalized mixed integrand retains the Vandermonde of all row nodes. -/
theorem param_mixedDouble_population_two {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i,E i<P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1)
    (hzi : Function.Injective (fun c : Fin (P.n N) =>Fin.append x y (Fin.cast hpm.symm c)))
    (hn48 : 48 ≤ P.n N) (hD : 0<P.n N-1-2*P.g N)
    (hcase : (∑ c : Fin (P.n N),(1-(Fin.append x y (Fin.cast hpm.symm c))^2)/
      (1+(Fin.append x y (Fin.cast hpm.symm c))^2)) ≤ ((P.n N-1-2*P.g N:ℕ):ℝ)) :
    |CatalanMeasure.mixedDouble (paramPinRowFun P N) (realCoordinateInv ∘ y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| ≤
      (1+10*Real.exp 12*(P.n N:ℝ))^(P.n N)*populationTwoProduct P N hpm x y s :=by
  have hbase :=param_abs_mixedDouble_le_sheet_product hP hN hpm E hE hEn x y s hz hz0 hs
  have hsheet :=realSheetDeterminant_first_sheet_bound hP hN
    (fun c =>Fin.append x y (Fin.cast hpm.symm c)) (fun c =>hz _) (fun c =>hz0 _)
    hzi hn48 hD hcase
  have hprod : 0 ≤ (∏ j : Fin p, (1+s j))^m :=pow_nonneg (prod_nonneg fun j _ =>by linarith [(hs j).1]) _
  have hfixed : 0 ≤ ∏ j,paramRowNodeWeight P N (y j) :=
    prod_nonneg fun j _ =>paramRowNodeWeight_nonneg P N (by simpa using hz (Fin.natAdd p j))
  have hprincipal :=paramPinPrincipal_nonneg P N x s
    (fun i =>by simpa using hz (Fin.castAdd m i)) hs
  calc
    _ ≤ (∏ j : Fin p, (1+s j))^m*
      |realSheetDeterminant P N (fun c =>Fin.append x y (Fin.cast hpm.symm c))| *
      (∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s :=hbase
    _ ≤ (∏ j : Fin p, (1+s j))^m*
      ((1+10*Real.exp 12*(P.n N:ℝ))^(P.n N)*
        |∏ i : Fin (P.n N),∏ j ∈ Ioi i,
          ((Fin.append x y (Fin.cast hpm.symm j))⁻¹-(Fin.append x y (Fin.cast hpm.symm i))⁻¹)| *
        ∏ i : Fin (P.n N),|Fin.append x y (Fin.cast hpm.symm i)|^(P.g N))*
      (∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsheet hprod) hfixed) hprincipal
    _ = _ :=by unfold populationTwoProduct;ring

def paramSheetOneWeight (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  (1+x^2)^(((P.n N:ℝ)-1)/2)*|x|^((P.g N:ℤ)-((P.n N-1:ℕ):ℤ))

def populationOneProduct (P : Parameters) (N : ℕ) {p m : ℕ} (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  (∏ j, (1+s j))^m*(∏ i,paramSheetOneWeight P N (z i))*
    (∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s/
      (2:ℝ)^((P.n N).choose 2)

/-- The first sheet retains every fixed-node weight before applying the energy dual. -/
theorem param_mixedDouble_population_one {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0<N) (hpm : p+m=P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i,E i<P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1)
    (hz0 : ∀ c,Fin.append x y c≠0) (hs : ∀ i,s i ∈ Ioo (0:ℝ) 1) :
    |CatalanMeasure.mixedDouble (paramPinRowFun P N) (realCoordinateInv ∘ y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| ≤
      ((3/2:ℝ)^(P.n N)*(P.n N:ℝ)^((P.n N:ℝ)/2))*
        populationOneProduct P N hpm x y s :=by
  have hbase :=param_abs_mixedDouble_le_sheet_product hP hN hpm E hE hEn x y s hz hz0 hs
  have hsheet :=realSheetDeterminant_abs_le hP hN
    (fun c =>Fin.append x y (Fin.cast hpm.symm c)) (fun c =>hz _) (fun c =>hz0 _)
  have hprod : 0 ≤ (∏ j : Fin p, (1+s j))^m :=
    pow_nonneg (prod_nonneg fun j _ =>by linarith [(hs j).1]) _
  have hfixed : 0 ≤ ∏ j,paramRowNodeWeight P N (y j) :=
    prod_nonneg fun j _ =>paramRowNodeWeight_nonneg P N (by simpa using hz (Fin.natAdd p j))
  have hprincipal :=paramPinPrincipal_nonneg P N x s
    (fun i =>by simpa using hz (Fin.castAdd m i)) hs
  have hle :=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsheet hprod) hfixed) hprincipal
  apply hbase.trans
  convert hle using 1
  unfold populationOneProduct paramSheetOneWeight
  ring

end
end CatalanMeasure.Parametric
