module

public import Submission.CatalanMeasure.Parametric.GroupedSelection
public import Submission.CatalanMeasure.Parametric.MarkedSheetExpansion
public import Submission.CatalanMeasure.GenD.Analytic.MarkedSheet
public import Submission.CatalanMeasure.GenD.Analytic.GroupedProduct

@[expose] public section

/-!
# Copy of the second-population marked sheet product with a restricted energy hypothesis

`Analytic.MarkedSecond` (in the 532 closure, not edited) keeps `marked_selected_sheet_le_grouped`
private and its `second_marked_sheet_product_on` takes the unrestricted
`GroupedMarkedProductCostOn`.  Theorem A needs the old energy route only on the configurations
outside the class `Cls`.  This module copies the private selection lemmas, with proofs, and proves
`second_marked_sheet_product_on_restr`: the same conclusion for the configurations whose
selections (all of them are queried) satisfy a predicate `Q`, from the grouped-product bound
restricted to `Q`.  It imports the same dependencies as `MarkedSecond`, not `MarkedSecond` itself,
and is imported by nothing in the 532 closure.
-/

namespace CatalanMeasure.Signed

open CatalanMeasure.GenD.Analytic
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open scoped BigOperators Topology

noncomputable section

private theorem marked_partition_prod {m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (f : Fin m → ℝ) :
    (∏ i, f i) = (∏ i : Fin a, f (e (Sum.inl i))) *
      (∏ i : Fin b, f (e (Sum.inr i))) := by
  calc
    _ = ∏ i : Fin a ⊕ Fin b, f (e i) :=
      (Fintype.prod_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.prod_sum_type]

private theorem marked_partition_sum {m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (f : Fin m → ℝ) :
    (∑ i, f i) = (∑ i : Fin a, f (e (Sum.inl i))) +
      (∑ i : Fin b, f (e (Sum.inr i))) := by
  calc
    _ = ∑ i : Fin a ⊕ Fin b, f (e i) :=
      (Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_sum_type]

private theorem marked_weighted_laurent_expansion {n g : ℕ}
    (z : Fin n → ℝ) (marked : Fin n → Bool) {w M : ℝ}
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hV : ∀ t : Fin n → Bool,
      w * |(Matrix.of fun i r : Fin n =>
        if t i && marked i && decide (0 ≤ z i) then z i ^ ((r : ℤ) - g)
        else actualLaurentEntry g r (z i)).det| ≤ M) :
    w * |(markedLaurentMatrix g z marked).det| ≤
      M * ∏ i, (if marked i then (5 : ℝ) else 1) := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul]
    exact mul_nonneg hM (prod_nonneg fun i _ => by split_ifs <;> norm_num)
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hb := marked_laurent_det_bound z marked (M := M / w) (div_nonneg hM hw)
    (fun t => (le_div_iff₀ hwpos).mpr (by simpa [mul_comm] using hV t))
  have hh := mul_le_mul_of_nonneg_left hb hw
  change w * |(markedLaurentMatrix g z marked).det| ≤ _ at hh
  calc
    _ ≤ w * (M / w * ∏ i, (if marked i then (5 : ℝ) else 1)) := hh
    _ = _ := by field_simp

private theorem marked_sheet_product_uncast {P : Parameters} {N p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    markedSheetProduct P N hpm x y s =
      ((∏ i, (1 + s i)) ^ m * (∏ j, paramRowNodeWeight P N (y j)) *
        paramPinPrincipal P N x s /
          ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
      |(markedLaurentMatrix (P.g N) (Fin.append x y)
        (Fin.addCases (fun _ => false) (fun _ => true))).det| := by
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  have hm : (markedLaurentMatrix (P.g N) z marked).submatrix
      (finCongr hpm) (finCongr hpm) =
      markedLaurentMatrix (P.g N) (Fin.append x y)
        (Fin.addCases (fun _ => false) (fun _ => true)) := by
    ext i r
    simp [markedLaurentMatrix, z, marked]
  have hd := Matrix.abs_det_submatrix_equiv_equiv (finCongr hpm) (finCongr hpm)
    (markedLaurentMatrix (P.g N) z marked)
  rw [hm] at hd
  unfold markedSheetProduct
  change _ * |(markedLaurentMatrix (P.g N) z marked).det| * _ * _ / _ = _
  rw [← hd]
  ring

private def marked_selection_equiv {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m) :
    Fin (p + a) ⊕ Fin b ≃ Fin (p + m) :=
  ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin b))).trans
    (Equiv.sumAssoc (Fin p) (Fin a) (Fin b))).trans
      ((Equiv.sumCongr (Equiv.refl (Fin p)) e).trans finSumFinEquiv)

private theorem marked_selection_nodes {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun j : Fin (p + a + b) =>
      Fin.append x y (marked_selection_equiv e (finSumFinEquiv.symm j))) =
      Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
        (fun i => y (e (Sum.inr i))) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp [marked_selection_equiv]
  · simp [marked_selection_equiv]

private theorem marked_selection_left {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (t : Fin m → Bool) (hleft : ∀ i, t (e (Sum.inl i)) = false) :
    ∀ i : Fin (p + a),
      Fin.addCases (fun _ => false) t (marked_selection_equiv e (Sum.inl i)) = false := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [marked_selection_equiv, hleft]

private theorem marked_selection_right {p m a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (t : Fin m → Bool) (hright : ∀ i, t (e (Sum.inr i)) = true) :
    ∀ i : Fin b,
      Fin.addCases (fun _ => false) t (marked_selection_equiv (p := p) e (Sum.inr i)) = true := by
  intro i
  simp [marked_selection_equiv, hright]

private theorem marked_selection_actual_nodes {p m a b : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun i : Fin (p + a) => Fin.append x y (marked_selection_equiv e (Sum.inl i))) =
      Fin.append x (fun i => y (e (Sum.inl i))) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [marked_selection_equiv]

private theorem marked_selection_near_nodes {p m a b : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    (fun i : Fin b => Fin.append x y (marked_selection_equiv e (Sum.inr i))) =
      (fun i => y (e (Sum.inr i))) := by
  funext i
  simp [marked_selection_equiv]

private theorem marked_sheet_weight_prod {P : Parameters} (hP : Admissible P)
    {N m : ℕ} (hN : 0 < N) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0) :
    (∏ i, |y i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        (∏ i, paramRowNodeWeight P N (y i)) =
      (∏ i, |(rowCommonFactor P N).eval (realCoordinateInv (y i))|) *
        (∏ i, markedSheetWeight P N (y i)) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  exact marked_sheet_weight_cancellation hP hN (hy i) (hy0 i)

private def marked_sheet_scalar (P : Parameters) (N : ℕ) {p m : ℕ}
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  (∏ i, (1 + s i)) ^ m * (∏ j, paramRowNodeWeight P N (y j)) *
    paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

private theorem marked_grouped_majorant_product {P : Parameters} (hP : Admissible P)
    {N p m a b : ℕ} (hN : 0 < N) (hpm : p + m = P.n N) (hab : a + b = m)
    (e : Fin a ⊕ Fin b ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0) :
    marked_sheet_scalar P N x y s * groupedLaurentMajorant (p := p + a) (q := b)
      (Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
        (fun i => y (e (Sum.inr i)))) (P.g N) =
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s := by
  have hcount : p + a + b = P.n N := by omega
  have hc : (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    apply abs_ne_zero.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcan := marked_sheet_weight_prod hP hN y hy hy0
  have hratio :
      (∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
          (∏ j, paramRowNodeWeight P N (y j)) /
            (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) =
        ∏ j, markedSheetWeight P N (y j) := by
    apply (div_eq_iff hc).mpr
    simpa [mul_comm] using hcan
  have hpow := marked_partition_prod e
    (fun j => |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)))
  have hmarked := marked_partition_prod e (fun j => markedSheetWeight P N (y j))
  let pair := groupedPairProduct (Fin.append x (fun i => y (e (Sum.inl i))))
    (fun i => y (e (Sum.inr i)))
  calc
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        ((∏ i, (1 + s i)) ^ (a + b) *
          (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
          ((∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
            (∏ j, paramRowNodeWeight P N (y j)) /
              (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|)) *
          (∏ j : Fin b, |y (e (Sum.inr j))| ^ (P.n N - 1 - 2 * P.g N)) *
          pair * paramPinPrincipal P N x s) := by
      unfold marked_sheet_scalar groupedLaurentMajorant pair groupedPairProduct
      simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, hcount]
      rw [hpow, hab]
      ring
    _ = _ := by
      rw [hratio, hmarked]
      unfold groupedProduct pair
      rw [prod_mul_distrib]
      ring

private theorem marked_selected_sheet_le_grouped {P : Parameters} (hP : Admissible P)
    {N p m a b : ℕ} (hN : 0 < N) (hpm : p + m = P.n N) (hab : a + b = m)
    (e : Fin a ⊕ Fin b ≃ Fin m) (t : Fin m → Bool)
    (hleft : ∀ i, t (e (Sum.inl i)) = false)
    (hright : ∀ i, t (e (Sum.inr i)) = true)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ i, y i ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y))
    (hn48 : 48 ≤ P.n N) (hng : 2 * P.g N + 1 < P.n N)
    (hweight : (∑ i : Fin (p + m), blaschkeWeight (Fin.append x y i)) ≤
      ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ)) :
    marked_sheet_scalar P N x y s *
      |(Matrix.of fun i r : Fin (p + m) =>
        if (Fin.addCases (fun _ => false) t i : Bool) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det| ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s := by
  have hcount : p + a + b = p + m := by omega
  have htotal : p + a + b = P.n N := by omega
  have hz : ∀ i : Fin (p + m), Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i : Fin (p + m), Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hwnear : 0 ≤ ∑ j : Fin b, blaschkeWeight (y (e (Sum.inr j))) := by
    apply sum_nonneg
    intro j _
    unfold blaschkeWeight
    apply div_nonneg
    · have h1 : 0 < (1 - y (e (Sum.inr j))) * (1 + y (e (Sum.inr j))) :=
        mul_pos (sub_pos.mpr (hy _).2) (by linarith [(hy (e (Sum.inr j))).1])
      nlinarith
    · positivity
  have hsplit :
      (∑ i : Fin (p + a), blaschkeWeight
        (Fin.append x (fun j => y (e (Sum.inl j))) i)) +
      (∑ j : Fin b, blaschkeWeight (y (e (Sum.inr j)))) =
        ∑ i : Fin (p + m), blaschkeWeight (Fin.append x y i) := by
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rw [marked_partition_sum e (fun j => blaschkeWeight (y j))]
    ring
  have hwactual : (∑ i : Fin (p + a), blaschkeWeight
      (Fin.append x (fun j => y (e (Sum.inl j))) i)) ≤
        ((p + a + b - 1 - 2 * P.g N : ℕ) : ℝ) := by
    rw [htotal]
    linarith
  have hactual : ∀ i : Fin (p + a),
      Fin.append x y (marked_selection_equiv e (Sum.inl i)) =
        Fin.append x (fun j => y (e (Sum.inl j))) i :=
    fun i => congrFun (marked_selection_actual_nodes e x y) i
  have hdet := selected_laurent_det_bound (g := P.g N) hcount (Fin.append x y)
    (Fin.addCases (fun _ => false) t) (marked_selection_equiv e)
    (marked_selection_left e t hleft) (marked_selection_right e t hright)
    (by omega) (by omega) hz0 (fun i => abs_lt.mpr (hz i)) hzi
    (by simpa only [hactual] using hwactual)
  rw [marked_selection_nodes] at hdet
  have hscalar : 0 ≤ marked_sheet_scalar P N x y s := by
    unfold marked_sheet_scalar
    exact div_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _)
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i)))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hG : 0 ≤ groupedProduct P N x (fun i => y (e (Sum.inl i)))
      (fun i => y (e (Sum.inr i))) s := by
    have hcross : 0 ≤ crossCauchyProduct
        (Fin.append x (fun i => y (e (Sum.inl i)))) (fun i => y (e (Sum.inr i))) :=
      (crossCauchyProduct_pos _ _
        (fun i => Fin.addCases (fun j => by simpa using abs_lt.mpr (hx j))
          (fun j => by simpa using abs_lt.mpr (hy (e (Sum.inl j)))) i)
        (fun i => abs_lt.mpr (hy _))).le
    have hS : 0 ≤ (∏ i, (1 + s i)) ^ (a + b) :=
      pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _
    have hZ : 0 ≤ ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
      prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
    have hX : 0 ≤ ∏ i : Fin a, markedSheetWeight P N (y (e (Sum.inl i))) :=
      prod_nonneg fun i _ => (markedSheetWeight_pos P N _).le
    have hY : 0 ≤ ∏ i : Fin b, markedSheetWeight P N (y (e (Sum.inr i))) *
        |y (e (Sum.inr i))| ^ (P.n N - 1 - 2 * P.g N) :=
      prod_nonneg fun i _ => mul_nonneg (markedSheetWeight_pos P N _).le
        (pow_nonneg (abs_nonneg _) _)
    have hPair : 0 ≤ groupedPairProduct
        (Fin.append x (fun i => y (e (Sum.inl i)))) (fun i => y (e (Sum.inr i))) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hcross
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hS hZ) hX) hY)
      hPair) (paramPinPrincipal_nonneg P N x s hx hs)
  calc
    _ ≤ marked_sheet_scalar P N x y s *
        groupedLaurentMajorant (p := p + a) (q := b)
          (Fin.append (Fin.append x (fun i => y (e (Sum.inl i))))
            (fun i => y (e (Sum.inr i)))) (P.g N) :=
      mul_le_mul_of_nonneg_left hdet hscalar
    _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ (p + a) *
        groupedProduct P N x (fun i => y (e (Sum.inl i)))
          (fun i => y (e (Sum.inr i))) s :=
      marked_grouped_majorant_product hP hN hpm hab e x y s hy hy0
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by
        have hh : 0 ≤ 10 * Real.exp 12 * (P.n N : ℝ) := by positivity
        linarith) (by omega : p + a ≤ P.n N)) hG

/-- The grouped-product bound of `GroupedMarkedProductCostOn`, restricted to the configurations
`(z, x, y, s)` satisfying `Q`. -/
def GroupedMarkedProductCostOnRestr (P : Parameters) (target cost : ℝ) (G : ℝ → Prop)
    (Q : ∀ (N r a b : ℕ), (Fin r → ℝ) → (Fin a → ℝ) → (Fin b → ℝ) → (Fin r → ℝ) → Prop) :
    Prop :=
  ∀ ε : ℝ, 0<ε →
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      Q N r a b z x y s →
      groupedProduct P N z x y s ≤
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          cost * N * (a + b))

/-- **Restricted second-case sheet bound.**  Same conclusion as `second_marked_sheet_product_on`,
for the configurations all of whose marked selections satisfy `Q` (`hQ`), from the grouped-product
bound restricted to `Q`. -/
theorem second_marked_sheet_product_on_restr {P : Parameters} (hP : Admissible P)
    (target cost : ℝ) (G : ℝ → Prop)
    (Q : ∀ (N r a b : ℕ), (Fin r → ℝ) → (Fin a → ℝ) → (Fin b → ℝ) → (Fin r → ℝ) → Prop)
    (hgrouped : GroupedMarkedProductCostOnRestr P target cost G Q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) →
      Function.Injective s →
      ((∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1) →
      (∀ (a b : ℕ) (_ : a + b = m) (e : Fin a ⊕ Fin b ≃ Fin m),
        Q N p a b x (fun i => y (e (Sum.inl i))) (fun i => y (e (Sum.inr i))) s) →
      markedSheetProduct P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            cost * N * m) := by
  classical
  filter_upwards [hgrouped ε hε,
    eventually_ge_atTop (48 : ℕ)] with N he hN3 p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQ
  have hN : 0 < N := by omega
  have hn1 : 1 * N ≤ P.n0 * N := Nat.mul_le_mul_right N hP.1
  have hn2 : (2 * P.g0 + 1) * N ≤ P.n0 * N :=
    Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.2.2.2)
  have hn3 : (2 * P.g0 + 1) * N = 2 * (P.g0 * N) + N := by ring
  have hn48 : 48 ≤ P.n N := by simp only [Parameters.n]; omega
  have hng : 2 * P.g N + 1 < P.n N := by
    simp only [Parameters.n, Parameters.g]; omega
  have hxi : Function.Injective x := by
    intro i j hij
    have hh := hzi (show Fin.append x y (Fin.castAdd m i) =
      Fin.append x y (Fin.castAdd m j) by simpa using hij)
    simpa using hh
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  have hcaseN : (∑ i, paramCaseField P N (z i)) ≤ -1 := by
    change (∑ i, paramCaseField P N (Fin.append x y (Fin.cast hpm.symm i))) ≤ -1
    rw [sum_fin_cast hpm (fun i => paramCaseField P N (Fin.append x y i))]
    exact hcase
  have hweight := paramCaseField_second_case hP hN z hcaseN
  change (∑ i, blaschkeWeight (Fin.append x y (Fin.cast hpm.symm i))) ≤ _ at hweight
  rw [sum_fin_cast hpm (fun i => blaschkeWeight (Fin.append x y i))] at hweight
  let w := marked_sheet_scalar P N x y s
  let marked : Fin (p + m) → Bool := Fin.addCases (fun _ => false) (fun _ => true)
  let M := (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
    Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m)
  have hw : 0 ≤ w := by
    dsimp [w, marked_sheet_scalar]
    exact div_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _)
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hy i)))
      (paramPinPrincipal_nonneg P N x s hx hs))
      (prod_nonneg fun i _ => abs_nonneg _)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hV : ∀ t : Fin (p + m) → Bool,
      w * |(Matrix.of fun i r : Fin (p + m) =>
        if t i && marked i && decide (0 ≤ Fin.append x y i) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)).det| ≤ M := by
    intro t
    let ty : Fin m → Bool := fun j => t (Fin.natAdd p j) && decide (0 ≤ y j)
    obtain ⟨a, b, hab, e, hleft, hright⟩ := exists_bool_partition ty
    let ya : Fin a → ℝ := fun i => y (e (Sum.inl i))
    let yb : Fin b → ℝ := fun i => y (e (Sum.inr i))
    have hcount : p + a + b = P.n N := by omega
    have hya : ∀ i, ya i ∈ Ioo (-1 : ℝ) 1 := fun i => hy _
    have hyb : ∀ i, yb i ∈ Ioo (0 : ℝ) 1 := by
      intro i
      have hn : 0 ≤ yb i := by
        by_contra hh
        have ht := hright i
        simp [ty, yb, hh] at ht
      exact ⟨lt_of_le_of_ne hn (Ne.symm (hy0 _)), (hy _).2⟩
    have hai : Function.Injective (Fin.append x ya) := by
      have hh := hzi.comp ((marked_selection_equiv (p := p) e).injective.comp
        Sum.inl_injective)
      change Function.Injective
        (fun i : Fin (p + a) => Fin.append x y (marked_selection_equiv e (Sum.inl i))) at hh
      rw [marked_selection_actual_nodes] at hh
      exact hh
    have hbi : Function.Injective yb := by
      have hh := hzi.comp ((marked_selection_equiv (p := p) e).injective.comp
        Sum.inr_injective)
      change Function.Injective
        (fun i : Fin b => Fin.append x y (marked_selection_equiv (p := p) e (Sum.inr i))) at hh
      rw [marked_selection_near_nodes] at hh
      exact hh
    have henergy := he p a b hcount x ya yb s hx hx0 hya (fun i => hyG _) hyb hs hxi hai hbi hsi
      (hQ a b hab e)
    have habR : (a : ℝ) + b = m := by exact_mod_cast hab
    rw [habR] at henergy
    have hsel := marked_selected_sheet_le_grouped hP hN hpm hab e ty
      hleft hright x y s hx hx0 hy hy0 hs hzi hn48 hng hweight
    have hmat : (Matrix.of fun i r : Fin (p + m) =>
        if t i && marked i && decide (0 ≤ Fin.append x y i) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) =
      Matrix.of (fun i r : Fin (p + m) =>
        if (Fin.addCases (fun _ => false) ty i : Bool) then
          Fin.append x y i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (Fin.append x y i)) := by
      ext i r
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [marked, ty]
    rw [hmat]
    exact hsel.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hbound := marked_weighted_laurent_expansion (Fin.append x y) marked hw hM hV
  have hcost : (∏ i : Fin (p + m), if marked i then (5 : ℝ) else 1) = 5 ^ m := by
    simp [marked, Fin.prod_univ_add]
  rw [hcost] at hbound
  rw [marked_sheet_product_uncast]
  change w * |(markedLaurentMatrix (P.g N) (Fin.append x y) marked).det| ≤ _
  calc
    _ ≤ M * 5 ^ m := hbound
    _ = _ := by dsimp [M]; ring


end
end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.second_marked_sheet_product_on_restr
