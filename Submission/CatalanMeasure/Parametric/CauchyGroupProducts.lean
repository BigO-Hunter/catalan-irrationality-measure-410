module

public import Submission.CatalanMeasure.Parametric.KernelGram

@[expose] public section

namespace CatalanMeasure.Parametric

open scoped BigOperators

noncomputable section

def cauchyNodeProduct {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∏ i, ∏ j, (1 - x i * x j)

def crossCauchyProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) : ℝ := ∏ i, ∏ j, (1 - x i * y j)

theorem cauchyNodeProduct_pos {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, |x i| < 1) : 0 < cauchyNodeProduct x :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => one_sub_node_mul_pos (hx i) (hx j)

theorem crossCauchyProduct_pos {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, |x i| < 1) (hy : ∀ j, |y j| < 1) :
    0 < crossCauchyProduct x y :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => one_sub_node_mul_pos (hx i) (hy j)

theorem crossCauchyProduct_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) : crossCauchyProduct y x = crossCauchyProduct x y := by
  unfold crossCauchyProduct
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [mul_comm]

theorem cauchyNodeProduct_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) :
    cauchyNodeProduct (Sum.elim x y) =
      cauchyNodeProduct x * cauchyNodeProduct y * crossCauchyProduct x y ^ 2 := by
  unfold cauchyNodeProduct
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
  change (cauchyNodeProduct x * crossCauchyProduct y x) *
    (crossCauchyProduct x y * cauchyNodeProduct y) =
      cauchyNodeProduct x * cauchyNodeProduct y * crossCauchyProduct x y ^ 2
  rw [crossCauchyProduct_symm]
  ring

theorem sqrt_cauchyNodeProduct_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, |x i| < 1) (hy : ∀ j, |y j| < 1) :
    Real.sqrt (cauchyNodeProduct (Sum.elim x y)) =
      Real.sqrt (cauchyNodeProduct x) * Real.sqrt (cauchyNodeProduct y) *
        crossCauchyProduct x y := by
  have ha := cauchyNodeProduct_pos x hx
  have hb := cauchyNodeProduct_pos y hy
  have hc := crossCauchyProduct_pos x y hx hy
  rw [cauchyNodeProduct_sum, Real.sqrt_mul (mul_nonneg ha.le hb.le),
    Real.sqrt_mul ha.le, Real.sqrt_sq hc.le]

theorem cauchy_group_volume_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, |x i| < 1) (hy : ∀ j, |y j| < 1) :
    cauchyNodeProduct (Sum.elim x y) /
      (Real.sqrt (cauchyNodeProduct (Sum.elim x y)) *
        Real.sqrt (cauchyNodeProduct x) * Real.sqrt (cauchyNodeProduct y)) =
      crossCauchyProduct x y := by
  have ha := Real.sqrt_pos.mpr (cauchyNodeProduct_pos x hx)
  have hb := Real.sqrt_pos.mpr (cauchyNodeProduct_pos y hy)
  have hc := Real.sqrt_pos.mpr (cauchyNodeProduct_pos (Sum.elim x y)
    (fun i => by rcases i with i | i; exact hx i; exact hy i))
  calc
    _ = Real.sqrt (cauchyNodeProduct (Sum.elim x y)) /
        (Real.sqrt (cauchyNodeProduct x) * Real.sqrt (cauchyNodeProduct y)) := by
      have hs := Real.sq_sqrt (cauchyNodeProduct_pos (Sum.elim x y)
        (fun i => by rcases i with i | i; exact hx i; exact hy i)).le
      field_simp [ha.ne', hb.ne', hc.ne']
      nlinarith only [hs]
    _ = crossCauchyProduct x y := by
      rw [sqrt_cauchyNodeProduct_sum x y hx hy]
      field_simp

end

end CatalanMeasure.Parametric
