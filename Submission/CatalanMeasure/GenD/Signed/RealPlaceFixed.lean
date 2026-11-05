module

public import Submission.CatalanMeasure.GenD.Signed.RealPlace
public import Submission.CatalanMeasure.GenD.Signed.SignedDischarge

/-!
# The marked sheet: nodes, marks and the free-row identity

The relabelling of the four sign groups of the marked sheet onto `Fin n` (`sheetNodes`,
`sheetMarks`, `quadEquiv`, `quadNodes`) and the free-row grouped product
(`groupedProduct_free_eq`, `log_groupedProduct_free`, `groupedConstant_free_le`).  The determinant
bound with marked rows is `MarkedExpansion` (Lemma 17.43.1) and the class-branch sheet bound with
near-type rows is `SheetNear`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section SheetFixed

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set

/-- The node vector of the marked sheet on `Fin n`: free rows `x`, then marked rows `y`. -/
def sheetNodes {p m n : ℕ} (hpm : p + m = n) (x : Fin p → ℝ) (y : Fin m → ℝ) : Fin n → ℝ :=
  fun i => Fin.append x y (Fin.cast hpm.symm i)

/-- The marking of the sheet: the rows of `y` are marked. -/
def sheetMarks {p m n : ℕ} (hpm : p + m = n) : Fin n → Bool :=
  fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)

/-- The relabelling of the four sign groups (free negatives, marked negatives, free positives,
marked positives) onto the `p + m` rows. -/
def quadEquiv {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) :
    Fin ((k + m1) + (q + m2)) ≃ Fin (p + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm)).trans
    ((Equiv.sumSumSumComm (Fin k) (Fin m1) (Fin q) (Fin m2)).trans
      ((Equiv.sumCongr σx σy).trans finSumFinEquiv))

theorem quad_apply {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p)
    (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (i : Fin ((k + m1) + (q + m2))) :
    Fin.append (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
      (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b)))) i =
      Fin.append x y (quadEquiv σx σy i) := by
  obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective i
  rcases u with a | a
  · obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective a
    rcases v with b | b <;> simp [quadEquiv, fin_append_eq_elim]
  · obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective a
    rcases v with b | b <;> simp [quadEquiv, fin_append_eq_elim]

/-- `groupedProduct` for `a = b = 0` and any number `r` of free rows. -/
theorem groupedProduct_free_eq (P : Parameters) (N : ℕ) {r : ℕ} (x s : Fin r → ℝ) :
    groupedProduct P N x e0 e0 s =
      (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) * |(Matrix.vandermonde x).det| *
        paramPinPrincipal P N x s := by
  have hap : (Fin.append x e0 : Fin (r + 0) → ℝ) = x := fin_append_nil _ x e0
  unfold groupedProduct groupedPairProduct crossCauchyProduct
  rw [hap, Matrix.det_vandermonde]
  simp

theorem groupedProduct_free_pos {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {r : ℕ} (x s : Fin r → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0 < groupedProduct P N x e0 e0 s := by
  rw [groupedProduct_free_eq]
  have h1 : 0 < ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
    Finset.prod_pos fun i _ => zpow_pos (abs_pos.mpr (hx0 i)) _
  have h2 : 0 < |(Matrix.vandermonde x).det| :=
    abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hxi)
  exact mul_pos (mul_pos h1 h2) (paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi)

theorem log_groupedProduct_free {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {r : ℕ} (x s : Fin r → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (groupedProduct P N x e0 e0 s) = (P.n N : ℝ) ^ 2 *
      (groupedConstant P N r 0 0 + pinOffDiagonalInteraction (P.n N : ℝ) 1 x s +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (P.n N : ℝ) ^ 2 +
        (∑ i, populationPhysicalFreeField P N (x i)) / (P.n N : ℝ) +
        (∑ j, populationPhysicalColumnField P N (0 + 0) (s j)) / (P.n N : ℝ)) := by
  have hap : (Fin.append x e0 : Fin (r + 0) → ℝ) = x := fin_append_nil _ x e0
  have h := log_groupedProduct hP hN x e0 e0 s hx (fun i => i.elim0) (fun i => i.elim0) hs hx0
    (fun i => i.elim0) hxi (by rw [hap]; exact hxi) (fun i => i.elim0) hsi
  rw [h]
  congr 1
  exact groupedValue_free_eq _ _ _ _ _ _ x s e0 e0

/-- The constant of the free rows is at most the constant of all `n` rows. -/
theorem groupedConstant_free_le (P : Parameters) (N : ℕ) {r : ℕ} (hr : r ≤ P.n N) :
    groupedConstant P N r 0 0 ≤ groupedConstant P N (P.n N) 0 0 := by
  unfold groupedConstant
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hd : 0 ≤ (1 : ℝ) / (P.n N : ℝ) ^ 2 := by positivity
  have hc : r * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + r.choose 2 ≤
      P.n N * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + (P.n N).choose 2 := by
    have := Nat.choose_le_choose 2 hr
    have := Nat.mul_le_mul_right (P.C N - 1) hr
    omega
  have hcR : ((r * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + r.choose 2 : ℕ) : ℝ) ≤
      ((P.n N * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + (P.n N).choose 2 : ℕ) : ℝ) := by
    exact_mod_cast hc
  have := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hcR (sq_nonneg (P.n N : ℝ))) hl
  simpa using this

end SheetFixed

section ClassFixed

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set CatalanMeasure.GenD.Signed

/-- The four sign groups, appended: `(free negatives, marked negatives, free positives,
marked positives)` (the node list `Z` of `signed_second_energy_fixed_nodes`). -/
def quadNodes {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (x : Fin p → ℝ) (y : Fin m → ℝ) : Fin ((k + m1) + (q + m2)) → ℝ :=
  Fin.append (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
    (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))))

theorem quadNodes_apply {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p)
    (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (i : Fin ((k + m1) + (q + m2))) :
    quadNodes σx σy x y i = Fin.append x y (quadEquiv σx σy i) :=
  quad_apply σx σy x y i

theorem append_forall {p m : ℕ} {Q : ℝ → Prop} {x : Fin p → ℝ} {y : Fin m → ℝ}
    (hx : ∀ i, Q (x i)) (hy : ∀ j, Q (y j)) (j : Fin (p + m)) : Q (Fin.append x y j) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hx, hy]

end ClassFixed

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.quad_apply
#print axioms CatalanMeasure.Signed.log_groupedProduct_free
