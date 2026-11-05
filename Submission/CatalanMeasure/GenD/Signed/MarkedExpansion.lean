module

public import Submission.CatalanMeasure.GenD.Signed.RealPlace

/-!
# The marked-row determinant: Lemma 17.43.1 (expansion over the near subsets)

* `norm_det_gram_le_gen`, `norm_det_gram_le_gen_full`: `norm_det_gram_le` with the removed
  diagonal `Dg` independent of the diagonal `Dp` of `F(1)`.
* `det_add_diagonal_expand`, `det_add_diagonal_sum_expand`: principal-minor expansion of
  `det (X + diag δ)`.
* `abs_det_laurent_le_marked_expand` (Lemma 17.43.1): the marked Laurent determinant is bounded by
  `11^q ∏|z|^{g-(n-1)} exp (logRatioZ) · Σ_S (6/11)^{|S|} |V(z)| W_S`, `S` ranging over the subsets
  of the marked positives, from Lemma T for ALL positive nodes.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section GramMainGen

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `norm_det_gram_le` with `F(1) = K + D_p` and the removed part `D_g` independent: the
matrix is `K + diag(D_-, D_p - 6 D_g)`. -/
theorem norm_det_gram_le_gen {K11 : Matrix m m ℂ} {K12 : Matrix m n ℂ} {K22 Dm Dp Dg : Matrix _ _ ℂ}
    (hK : (fromBlocks K11 K12 K12ᴴ K22).PosDef) (hA : (K11 + Dm).PosDef)
    (hDg : Dg.IsHermitian)
    (h1 : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp)).PosSemidef)
    (h2 : (fromBlocks K11 K12 K12ᴴ K22 - fromBlocks Dm 0 0 Dp).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 - fromBlocks 0 0 0 Dg).PosSemidef)
    (h4 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 + fromBlocks 0 0 0 Dg).PosSemidef) :
    ‖(fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp - (6 : ℂ) • Dg)).det‖ * K11.det.re ≤
      (2 + 6 * τ) ^ Fintype.card n * (K11 + Dm).det.re *
        (fromBlocks K11 K12 K12ᴴ K22).det.re := by
  classical
  have hK11 : K11.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · have := hK.1.submatrix (Sum.inl : m → m ⊕ n)
      convert this using 1
      ext i j; simp
    · have h := hK.dotProduct_mulVec_pos (x := x ⊕ᵥ (0 : n → ℂ))
        (by intro h; apply hx; funext i; simpa using congrFun h (Sum.inl i))
      simpa [fromBlocks_mulVec, Function.star_sumElim] using h
  have : Invertible K11 := hK11.isUnit.invertible
  have : Invertible (K11 + Dm) := hA.isUnit.invertible
  have hSgpos : (K22 - K12ᴴ * K11⁻¹ * K12).PosDef := by
    have hsemi := (PosDef.fromBlocks₁₁ K12 K22 hK11).mp hK.posSemidef
    refine PosDef.of_dotProduct_mulVec_pos hsemi.1 fun y hy => ?_
    rw [← schur_form_eq hK11.1 K12 K22 y]
    refine hK.dotProduct_mulVec_pos ?_
    intro hc
    apply hy
    funext j
    simpa using congrFun hc (Sum.inr j)
  have hS1 : (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12).PosSemidef :=
    (PosDef.fromBlocks₁₁ K12 (K22 + Dp) hA).mp h1
  have hτc : (0 : ℂ) ≤ (τ : ℂ) := Complex.zero_le_real.mpr hτ
  have hSgH := hSgpos.1
  -- the minimiser
  have hFsplit : fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp) =
      fromBlocks K11 K12 K12ᴴ K22 + fromBlocks Dm 0 0 Dp := by
    ext (i | i) (j | j) <;> simp [fromBlocks]
  have hb : ((2 : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) -
      (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp [Complex.conj_ofNat])).sub
        hS1.1
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e2 := schur_form_ge hA K12 (K22 + Dp) (-((K11⁻¹ * K12) *ᵥ y)) y
      have e3 := h2.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [hFsplit, add_mulVec, dotProduct_add] at e2
      rw [sub_mulVec, dotProduct_sub] at e3
      have e4 : star y ⬝ᵥ (((2 : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) -
          (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12)) *ᵥ y) =
          2 * (star y ⬝ᵥ ((K22 - K12ᴴ * K11⁻¹ * K12) *ᵥ y)) -
            star y ⬝ᵥ ((K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12) *ᵥ y) := by
        rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]; simp
      rw [e4, ← e1]
      set P := star ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ (fromBlocks K11 K12 K12ᴴ K22 *ᵥ
        ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y))
      set Q := star ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ (fromBlocks Dm 0 0 Dp *ᵥ
        ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y))
      set U := star y ⬝ᵥ ((K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12) *ᵥ y)
      have : 2 * P - U = (P - Q) + ((P + Q) - U) := by ring
      rw [this]
      exact add_nonneg e3 (sub_nonneg.mpr e2)
  have hc1 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) - Dg).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).sub hDg
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h3.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
      exact e3
  have hc2 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) + Dg).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).add hDg
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h4.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul]
      exact e3
  have hmain := norm_det_schur_le hSgpos hS1 hDg hτ hb hc1 hc2
  -- determinants
  have hdF : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp - (6 : ℂ) • Dg)).det =
      (K11 + Dm).det * (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dg).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    congr 2
    module
  have hdK : (fromBlocks K11 K12 K12ᴴ K22).det =
      K11.det * (K22 - K12ᴴ * K11⁻¹ * K12).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hA0 := hA.det_pos
  have hK0 := hK11.det_pos
  have hS0 := hSgpos.det_pos
  rw [hdF, hdK, norm_mul, norm_eq_re_of_pos hA0, re_mul_of_pos hK0 hS0]
  have ha := (Complex.lt_def.mp hA0).1
  have hk := (Complex.lt_def.mp hK0).1
  simp only [Complex.zero_re] at ha hk
  calc (K11 + Dm).det.re * ‖(K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dg).det‖ *
        K11.det.re
      ≤ (K11 + Dm).det.re * ((2 + 6 * τ) ^ Fintype.card n *
          (K22 - K12ᴴ * K11⁻¹ * K12).det.re) * K11.det.re := by
        gcongr
    _ = _ := by ring

end GramMainGen

section GramFullGen

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `norm_det_gram_le_gen` on a full matrix over `m ⊕ n`. -/
theorem norm_det_gram_le_gen_full (Kf : Matrix (m ⊕ n) (m ⊕ n) ℂ) (d : m ⊕ n → ℝ) (dg : n → ℝ)
    (hK : Kf.PosDef) (hA : (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).PosDef)
    (h1 : (Kf + diagC d).PosSemidef) (h2 : (Kf - diagC d).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) dg)).PosSemidef)
    (h4 : ((τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) dg)).PosSemidef) :
    ‖(Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p))).det‖ *
        (Kf.submatrix Sum.inl Sum.inl).det.re ≤
      (2 + 6 * τ) ^ Fintype.card n *
        (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).det.re * Kf.det.re := by
  classical
  have hKe : ∀ i j, Kf (Sum.inr i) (Sum.inl j) = star (Kf (Sum.inl j) (Sum.inr i)) :=
    fun i j => (hK.1.apply (Sum.inr i) (Sum.inl j)).symm
  have hfb : Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ = Kf := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe]
  have hsub : Kf.submatrix Sum.inl Sum.inl = Kf.toBlocks₁₁ := rfl
  rw [hsub] at hA ⊢
  have e1 : Matrix.fromBlocks (Kf.toBlocks₁₁ + diagC (fun a => d (Sum.inl a))) Kf.toBlocks₁₂
      Kf.toBlocks₁₂ᴴ (Kf.toBlocks₂₂ + diagC (fun p => d (Sum.inr p))) = Kf + diagC d := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply]
  have e2 : Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ -
      Matrix.fromBlocks (diagC (fun a => d (Sum.inl a))) 0 0 (diagC (fun p => d (Sum.inr p))) =
      Kf - diagC d := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply]
  have e3 : (τ : ℂ) • Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ -
      Matrix.fromBlocks 0 0 0 (diagC dg) =
      (τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) dg) := by
    rw [hfb]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, diagC, Matrix.diagonal_apply]
  have e4 : (τ : ℂ) • Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ +
      Matrix.fromBlocks 0 0 0 (diagC dg) =
      (τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) dg) := by
    rw [hfb]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, diagC, Matrix.diagonal_apply]
  have e5 : Matrix.fromBlocks (Kf.toBlocks₁₁ + diagC (fun a => d (Sum.inl a))) Kf.toBlocks₁₂
      Kf.toBlocks₁₂ᴴ (Kf.toBlocks₂₂ + diagC (fun p => d (Sum.inr p)) - (6 : ℂ) • diagC dg) =
      Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p)) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply] <;> (try split_ifs) <;> (try simp) <;> (try ring)
  have key := norm_det_gram_le_gen (K11 := Kf.toBlocks₁₁) (K12 := Kf.toBlocks₁₂)
    (K22 := Kf.toBlocks₂₂)
    (Dm := diagC (fun a => d (Sum.inl a))) (Dp := diagC (fun p => d (Sum.inr p))) (Dg := diagC dg)
    (by rw [hfb]; exact hK) hA (diagC_conjTranspose _)
    (by rw [e1]; exact h1)
    (by rw [e2]; exact h2)
    hτ
    (by rw [e3]; exact h3)
    (by rw [e4]; exact h4)
  rw [e5, hfb] at key
  exact key

end GramFullGen

section MarkedLaurent

open CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

/-- Weight of the row `i` in the Gram form: `1` on negatives and marked rows, `-5` on free
positives. -/
def omegaM {n : ℕ} (z : Fin n → ℝ) (mk : Fin n → Bool) (i : Fin n) : ℝ :=
  if mk i = true ∨ z i < 0 then 1 else -5

/-- Prefactor of the row `i`: `1/2` on negatives and marked rows, `-1/4` on free positives. -/
def lamM {n : ℕ} (z : Fin n → ℝ) (mk : Fin n → Bool) (i : Fin n) : ℝ :=
  if mk i = true ∨ z i < 0 then 1 / 2 else -(1 / 4)

theorem abs_lamM_le {n : ℕ} (z : Fin n → ℝ) (mk : Fin n → Bool) (i : Fin n) :
    |lamM z mk i| ≤ 1 / 2 := by
  unfold lamM
  split_ifs <;> norm_num [abs_of_pos, abs_of_neg]

theorem markedLaurentEntry_eq {n g : ℕ} (hg : 2 * g + 1 ≤ n) (z : Fin n → ℝ)
    (mk : Fin n → Bool) (hz0 : ∀ i, z i ≠ 0) (i r : Fin n) :
    markedLaurentMatrix g z mk i r =
      lamM z mk i * z i ^ ((g : ℤ) - (n - 1 : ℕ)) *
        (z i ^ (r.rev : ℕ) + omegaM z mk i * z i ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ))) := by
  have h1 : z i ^ ((g : ℤ) - (n - 1 : ℕ)) * z i ^ (r.rev : ℕ) = z i ^ ((g : ℤ) - r) :=
    far_laurent_factor r (hz0 i)
  have h2 : z i ^ ((g : ℤ) - (n - 1 : ℕ)) * z i ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ)) =
      z i ^ ((r : ℤ) - g) := by
    first
      | rw [← zpow_natCast (z i) _, ← zpow_add₀ (hz0 i)]
      | rw [← zpow_add₀ (hz0 i)]
    congr 1
    have := r.isLt
    simp only [Fin.val_rev]
    omega
  by_cases hm : mk i = true
  · have hl : lamM z mk i = 1 / 2 := by simp [lamM, hm]
    have ho : omegaM z mk i = 1 := by simp [omegaM, hm]
    simp only [markedLaurentMatrix, Matrix.of_apply, hm, if_true, hl, ho]
    rw [← h1, ← h2]; ring
  · have hm' : mk i = false := by simpa using hm
    simp only [markedLaurentMatrix, Matrix.of_apply, hm', Bool.false_eq_true, if_false]
    rw [actualLaurentEntry_eq hg (hz0 i) r]
    have hl : lamM z mk i = lamOf (z i) := by simp [lamM, lamOf, hm]
    have ho : omegaM z mk i = omegaOf (z i) := by simp [omegaM, omegaOf, hm]
    rw [hl, ho]

theorem abs_det_laurent_eq_marked {n g : ℕ} (hg : 2 * g + 1 ≤ n) (x : Fin n → ℝ)
    (mk : Fin n → Bool) (hx0 : ∀ i, x i ≠ 0) :
    |(markedLaurentMatrix g x mk).det| =
      (∏ i, |lamM x mk i| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        |(dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).det| := by
  have hmat : (markedLaurentMatrix g x mk) =
      Matrix.diagonal (fun i => lamM x mk i * x i ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i r
    simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id, dMatW, Fin.revPerm_apply,
      Matrix.of_apply]
    rw [markedLaurentEntry_eq hg x mk hx0]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, abs_mul, Finset.abs_prod]
  have hperm : |((dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).submatrix id
      (Fin.revPerm : Equiv.Perm (Fin n))).det| =
      |(dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).det| := by
    simpa using Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl (Fin n))
      (Fin.revPerm : Equiv.Perm (Fin n)) (dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x)
  rw [hperm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_mul, abs_zpow]

/-- **Lemma T on the sign-split index with marked rows**: only the free positives enter the
Loewner form (the marked rows have weight `1`, no `D_p` term). -/
theorem lemmaT_sum_form_marked {n k q e : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin n) (x : Fin n → ℝ)
    (mk : Fin n → Bool)
    (hneg : ∀ b, x (σ (Sum.inl b)) < 0) (hpos : ∀ p, 0 < x (σ (Sum.inr p)))
    (hT : ∀ c : Fin n → ℝ, |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        CatalanMeasure.Signed.bDeriv x a * x a ^ e * c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b)) :
    ∀ u : Fin k ⊕ Fin q → ℝ,
      |∑ a, (Sum.elim (fun _ => (0 : ℝ))
          (fun p => if mk (σ (Sum.inr p)) = true then 0 else
            bdr (fun i => x (σ i)) (Sum.inr p) * x (σ (Sum.inr p)) ^ e) a) * u a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, u a * u b / (1 - x (σ a) * x (σ b)) := by
  classical
  intro u
  have h := hT (fun a => u (σ.symm a))
  have hl : ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
      CatalanMeasure.Signed.bDeriv x a * x a ^ e * (u (σ.symm a)) ^ 2 =
      ∑ a, (Sum.elim (fun _ => (0 : ℝ))
        (fun p => if mk (σ (Sum.inr p)) = true then 0 else
          bdr (fun i => x (σ i)) (Sum.inr p) * x (σ (Sum.inr p)) ^ e) a) * u a ^ 2 := by
    rw [Finset.sum_filter, ← Equiv.sum_comp σ, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have hn' : ∀ b, ¬ (0 < x (σ (Sum.inl b)) ∧ mk (σ (Sum.inl b)) = false) :=
      fun b hb => absurd (hneg b) (not_lt.mpr hb.1.le)
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, zero_add, hn', if_false]
    refine Finset.sum_congr rfl fun p _ => ?_
    cases hm : mk (σ (Sum.inr p)) <;> simp [hm, hpos p, bdr_comp]
  have hr : ∑ a, ∑ b, u (σ.symm a) * u (σ.symm b) / (1 - x a * x b) =
      ∑ a, ∑ b, u a * u b / (1 - x (σ a) * x (σ b)) := by
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp
  rw [hl, hr] at h
  exact h

end MarkedLaurent

section DiagExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- Rows in `s` from `X`, the others from `Y`. -/
def pwMat (s : Finset ι) (X Y : Matrix ι ι R) : Matrix ι ι R := s.piecewise X Y

theorem pwMat_apply (s : Finset ι) (X Y : Matrix ι ι R) (i j : ι) :
    pwMat s X Y i j = if i ∈ s then X i j else Y i j := by
  unfold pwMat Finset.piecewise
  by_cases h : i ∈ s <;> simp [h]

theorem subtype_ite_eq {α β : Type*} [DecidableEq α] {p : α → Prop} (a b : {x // p x}) (u v : β) :
    (if (a : α) = b then u else v) = if a = b then u else v := by
  simp [Subtype.ext_iff]

/-- Rows of `T` replaced by the rows of a diagonal matrix: the determinant factorises. -/
theorem det_piecewise_diag (X : Matrix ι ι R) (δ : ι → R) (T : Finset ι) :
    (pwMat Tᶜ X (Matrix.diagonal δ)).det =
      (∏ a ∈ T, δ a) *
        (X.submatrix (fun a : {a // a ∉ T} => a.1) (fun a : {a // a ∉ T} => a.1)).det := by
  classical
  let e : {a // a ∈ T} ⊕ {a // a ∉ T} ≃ ι := Equiv.sumCompl (fun a => a ∈ T)
  have hrow : ∀ a b : ι, pwMat Tᶜ X (Matrix.diagonal δ) a b =
      if a ∈ T then Matrix.diagonal δ a b else X a b := by
    intro a b
    rw [pwMat_apply]
    by_cases h : a ∈ T <;> simp [h]
  have hM : (pwMat Tᶜ X (Matrix.diagonal δ)).submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal fun a : {a // a ∈ T} => δ a.1) 0
        (X.submatrix (fun a : {a // a ∉ T} => a.1) (fun a : {a // a ∈ T} => a.1))
        (X.submatrix (fun a : {a // a ∉ T} => a.1) (fun a : {a // a ∉ T} => a.1)) := by
    ext (i | i) (j | j)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, e, Equiv.sumCompl_apply_inl,
        hrow, i.2, if_true, Matrix.diagonal_apply]
      exact subtype_ite_eq i j _ _
    · have hij : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
      simp [e, hrow, i.2, Matrix.diagonal_apply, hij]
    · simp [e, hrow, i.2]
    · simp [e, hrow, i.2]
  have h := Matrix.det_submatrix_equiv_self e (pwMat Tᶜ X (Matrix.diagonal δ))
  rw [← h, hM, Matrix.det_fromBlocks_zero₁₂, Matrix.det_diagonal]
  congr 1
  exact Finset.prod_coe_sort T δ

/-- **Principal-minor expansion**: `det (X + diag δ) = Σ_T (∏_{a ∈ T} δ_a) det X_{Tᶜ Tᶜ}`. -/
theorem det_add_diagonal_expand (X : Matrix ι ι R) (δ : ι → R) :
    (X + Matrix.diagonal δ).det =
      ∑ T : Finset ι, (∏ a ∈ T, δ a) *
        (X.submatrix (fun a : {a // a ∉ T} => a.1) (fun a : {a // a ∉ T} => a.1)).det := by
  classical
  have h := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).map_add_univ X
    (Matrix.diagonal δ)
  have h' : (X + Matrix.diagonal δ).det =
      ∑ s : Finset ι, (pwMat s X (Matrix.diagonal δ)).det := h
  rw [h']
  refine Fintype.sum_equiv (Equiv.mk (fun s => sᶜ) (fun s => sᶜ) compl_compl compl_compl) _ _
    (fun s => ?_)
  have := det_piecewise_diag X δ sᶜ
  rw [compl_compl] at this
  exact this

end DiagExpansion

section SumExpansion

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The embedding of `m ⊕ {p // p ∉ S}` into `m ⊕ n`. -/
def tailEmb (S : Finset n) : m ⊕ {p : n // p ∉ S} → m ⊕ n := Sum.map id Subtype.val

theorem tailEmb_injective (S : Finset n) : Function.Injective (tailEmb (m := m) S) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;>
    simp [tailEmb] at h ⊢ <;> first | exact h | exact Subtype.ext h

/-- `m ⊕ {p // p ∉ S}` as the complement of the image of `S` in `m ⊕ n`. -/
def tailEquiv (S : Finset n) :
    m ⊕ {p : n // p ∉ S} ≃ {a : m ⊕ n // a ∉ S.map Function.Embedding.inr} where
  toFun x := ⟨tailEmb S x, by
    rcases x with j | p
    · simp [tailEmb]
    · simpa [tailEmb] using p.2⟩
  invFun a := match a with
    | ⟨Sum.inl j, _⟩ => Sum.inl j
    | ⟨Sum.inr p, h⟩ => Sum.inr ⟨p, by simpa using h⟩
  left_inv x := by rcases x with j | p <;> rfl
  right_inv a := by
    obtain ⟨a | a, h⟩ := a <;> rfl

theorem tailEquiv_val (S : Finset n) (x : m ⊕ {p : n // p ∉ S}) :
    ((tailEquiv S x).1 : m ⊕ n) = tailEmb S x := rfl

variable {R : Type*} [CommRing R]

/-- **Principal-minor expansion for a diagonal supported on the `n` block.** -/
theorem det_add_diagonal_sum_expand (X : Matrix (m ⊕ n) (m ⊕ n) R) (δ : n → R) :
    (X + Matrix.diagonal (Sum.elim (fun _ : m => (0 : R)) δ)).det =
      ∑ S : Finset n, (∏ p ∈ S, δ p) * (X.submatrix (tailEmb S) (tailEmb S)).det := by
  classical
  rw [det_add_diagonal_expand]
  set F : Finset (m ⊕ n) → R := fun T =>
    (∏ a ∈ T, (Sum.elim (fun _ : m => (0 : R)) δ) a) *
      (X.submatrix (fun a : {a // a ∉ T} => a.1) (fun a : {a // a ∉ T} => a.1)).det with hF
  have hsub : (Finset.univ.image (fun S : Finset n => S.map Function.Embedding.inr)) ⊆
      (Finset.univ : Finset (Finset (m ⊕ n))) := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (f := F) (fun T _ hT => ?_)]
  · rw [Finset.sum_image (fun S _ S' _ h => Finset.map_injective _ h)]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hF]
    rw [Finset.prod_map]
    simp only [Function.Embedding.inr_apply, Sum.elim_inr]
    congr 1
    have h := Matrix.det_submatrix_equiv_self (tailEquiv (m := m) S)
      (X.submatrix (fun a : {a // a ∉ S.map Function.Embedding.inr} => a.1)
        (fun a : {a // a ∉ S.map Function.Embedding.inr} => a.1))
    rw [← h]
    rfl
  · by_cases hj : ∃ j : m, Sum.inl j ∈ T
    · obtain ⟨j, hj⟩ := hj
      simp only [hF]
      rw [Finset.prod_eq_zero hj (by simp), zero_mul]
    · exfalso
      apply hT
      rw [Finset.mem_image]
      refine ⟨T.preimage Sum.inr (Sum.inr_injective.injOn), Finset.mem_univ _, ?_⟩
      ext a
      rcases a with j | p
      · simp only [Finset.mem_map, Function.Embedding.inr_apply, reduceCtorEq, and_false,
          exists_false, false_iff]
        exact fun h => hj ⟨j, h⟩
      · simp

end SumExpansion

section GramSub

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem submatrix_add_diagC {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (d : ι → ℝ) (f : κ → ι) (hf : Function.Injective f) :
    (M + diagC d).submatrix f f = M.submatrix f f + diagC (fun a => d (f a)) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, diagC, Matrix.diagonal_apply, hf.eq_iff]

theorem submatrix_sub_diagC {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (d : ι → ℝ) (f : κ → ι) (hf : Function.Injective f) :
    (M - diagC d).submatrix f f = M.submatrix f f - diagC (fun a => d (f a)) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, diagC, Matrix.diagonal_apply, hf.eq_iff]

/-- **The Gram bound on the principal submatrix indexed by `m ⊕ {p ∉ S}`** (Lemma 17.43.1,
step 3): `norm_det_gram_le_gen_full` for the nodes with the positives of `S` removed. -/
theorem norm_det_gram_le_sub (Kf : Matrix (m ⊕ n) (m ⊕ n) ℂ) (d : m ⊕ n → ℝ) (dg : n → ℝ)
    (hK : Kf.PosDef) (hA : (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).PosDef)
    (h1 : (Kf + diagC d).PosSemidef) (h2 : (Kf - diagC d).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) dg)).PosSemidef)
    (h4 : ((τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) dg)).PosSemidef) (S : Finset n) :
    ‖((Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p))).submatrix
        (tailEmb S) (tailEmb S)).det‖ * (Kf.submatrix Sum.inl Sum.inl).det.re ≤
      (2 + 6 * τ) ^ Fintype.card {p : n // p ∉ S} *
        (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).det.re *
          (Kf.submatrix (tailEmb S) (tailEmb S)).det.re := by
  classical
  have hinj := tailEmb_injective (m := m) S
  have hl : ∀ a : m, tailEmb S (Sum.inl a) = Sum.inl a := fun a => rfl
  have hsubl : (Kf.submatrix (tailEmb S) (tailEmb S)).submatrix Sum.inl Sum.inl =
      Kf.submatrix Sum.inl Sum.inl := by
    ext a b; simp [Matrix.submatrix_apply, hl]
  have e1 : (Kf + diagC d).submatrix (tailEmb S) (tailEmb S) =
      Kf.submatrix (tailEmb S) (tailEmb S) + diagC (fun a => d (tailEmb S a)) :=
    submatrix_add_diagC Kf d _ hinj
  have e2 : (Kf - diagC d).submatrix (tailEmb S) (tailEmb S) =
      Kf.submatrix (tailEmb S) (tailEmb S) - diagC (fun a => d (tailEmb S a)) :=
    submatrix_sub_diagC Kf d _ hinj
  have e3 : ((τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) dg)).submatrix (tailEmb S) (tailEmb S) =
      (τ : ℂ) • Kf.submatrix (tailEmb S) (tailEmb S) -
        diagC (Sum.elim (fun _ => 0) (fun p : {p : n // p ∉ S} => dg p.1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.submatrix_apply, diagC, Matrix.diagonal_apply, tailEmb]
    exact subtype_ite_eq a b _ _
  have e4 : ((τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) dg)).submatrix (tailEmb S) (tailEmb S) =
      (τ : ℂ) • Kf.submatrix (tailEmb S) (tailEmb S) +
        diagC (Sum.elim (fun _ => 0) (fun p : {p : n // p ∉ S} => dg p.1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.submatrix_apply, diagC, Matrix.diagonal_apply, tailEmb]
    exact subtype_ite_eq a b _ _
  have key := norm_det_gram_le_gen_full (m := m) (n := {p : n // p ∉ S})
    (Kf.submatrix (tailEmb S) (tailEmb S)) (fun a => d (tailEmb S a))
    (fun p => dg p.1) (hK.submatrix hinj)
    (by rw [hsubl]; simpa [hl] using hA)
    (by rw [← e1]; exact h1.submatrix _)
    (by rw [← e2]; exact h2.submatrix _)
    hτ (by rw [← e3]; exact h3.submatrix _) (by rw [← e4]; exact h4.submatrix _)
  rw [hsubl] at key
  have e5 : (Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p))).submatrix
        (tailEmb S) (tailEmb S) =
      Kf.submatrix (tailEmb S) (tailEmb S) +
        diagC (Sum.elim (fun a => d (tailEmb S (Sum.inl a)))
          (fun p : {p : n // p ∉ S} => d (tailEmb S (Sum.inr p)) - 6 * dg p.1)) := by
    rw [submatrix_add_diagC _ _ _ hinj]
    congr 2
    funext a
    rcases a with a | a <;> rfl
  rw [e5]
  simpa [hl] using key

end GramSub

section CauchyLog

open OAI.InternalCatalan CatalanMeasure.Parametric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `log |z a - z b|` off the diagonal (and `0` on it). -/
def lgd (z : ι → ℝ) (a b : ι) : ℝ := if a = b then 0 else Real.log |z a - z b|

/-- `log (1 - z a z b)`. -/
def lgc (z : ι → ℝ) (a b : ι) : ℝ := Real.log (1 - z a * z b)

theorem lgd_symm (z : ι → ℝ) (a b : ι) : lgd z a b = lgd z b a := by
  unfold lgd
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]

theorem lgc_symm (z : ι → ℝ) (a b : ι) : lgc z a b = lgc z b a := by
  unfold lgc; rw [mul_comm]

theorem sum_sum_split (T : Finset ι) (f : ι → ι → ℝ) :
    ∑ a, ∑ b, f a b = (∑ a ∈ T, ∑ b ∈ T, f a b) + (∑ a ∈ T, ∑ b ∈ Tᶜ, f a b) +
      (∑ a ∈ Tᶜ, ∑ b ∈ T, f a b) + ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, f a b := by
  classical
  rw [← Finset.sum_add_sum_compl T (fun a => ∑ b, f a b)]
  have h1 : ∀ a, ∑ b, f a b = (∑ b ∈ T, f a b) + ∑ b ∈ Tᶜ, f a b :=
    fun a => (Finset.sum_add_sum_compl T (f a)).symm
  simp only [h1, Finset.sum_add_distrib]
  ring

theorem sum_cross_symm (T : Finset ι) (f : ι → ι → ℝ) (hf : ∀ a b, f a b = f b a) :
    ∑ a ∈ Tᶜ, ∑ b ∈ T, f a b = ∑ a ∈ T, ∑ b ∈ Tᶜ, f a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hf b a

/-- **Cauchy's determinant in logarithmic form**:
`log det (1/(1 - t_a t_b)) = Σ_{a ≠ b} log |t_a - t_b| - Σ_{a,b} log (1 - t_a t_b)`. -/
theorem log_det_kR {κ : Type*} [Fintype κ] [DecidableEq κ] (t : κ → ℝ)
    (hinj : Function.Injective t) (ht : ∀ a, |t a| < 1) :
    0 < (kR t).det ∧
      Real.log (kR t).det = (∑ a, ∑ b, lgd t a b) - ∑ a, ∑ b, lgc t a b := by
  classical
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  set t' : Fin (Fintype.card κ) → ℝ := fun i => t (e i) with ht'
  have hinj' : Function.Injective t' := hinj.comp e.injective
  have hden : ∀ i j, 1 - t' i * t' j ≠ 0 := fun i j => (one_sub_node_mul_pos (ht _) (ht _)).ne'
  have hden0 : 0 < ∏ i : Fin (Fintype.card κ), ∏ j : Fin (Fintype.card κ), (1 - t' i * t' j) :=
    Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => one_sub_node_mul_pos (ht _) (ht _)
  have h1 : (kR t').det = (kR t).det := by
    have : kR t' = (kR t).submatrix e e := by ext i j; simp [kR, ht']
    rw [this, Matrix.det_submatrix_equiv_self]
  have hdet : (kR t).det =
      ((∏ i, ∏ j ∈ Finset.Ioi i, (t' j - t' i)) * (∏ i, ∏ j ∈ Finset.Ioi i, (t' j - t' i))) /
        ∏ i : Fin (Fintype.card κ), ∏ j : Fin (Fintype.card κ), (1 - t' i * t' j) := by
    rw [← h1]
    exact cauchy_det_eq_prod t' t' hden
  have hV : (∏ i : Fin (Fintype.card κ), ∏ j ∈ Finset.Ioi i, (t' j - t' i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => absurd (hinj' h) (ne_of_gt (Finset.mem_Ioi.mp hj)))
  have hVV : 0 < (∏ i : Fin (Fintype.card κ), ∏ j ∈ Finset.Ioi i, (t' j - t' i)) *
      (∏ i : Fin (Fintype.card κ), ∏ j ∈ Finset.Ioi i, (t' j - t' i)) := mul_self_pos.mpr hV
  refine ⟨by rw [hdet]; exact div_pos hVV hden0, ?_⟩
  have hVa := abs_mul_abs_self (∏ i : Fin (Fintype.card κ), ∏ j ∈ Finset.Ioi i, (t' j - t' i))
  have hlogden : Real.log (∏ i : Fin (Fintype.card κ), ∏ j : Fin (Fintype.card κ),
      (1 - t' i * t' j)) = ∑ i : Fin (Fintype.card κ), ∑ j : Fin (Fintype.card κ),
        Real.log (1 - t' i * t' j) := by
    rw [Real.log_prod (fun i _ => (Finset.prod_pos fun j _ =>
      one_sub_node_mul_pos (ht _) (ht _)).ne')]
    exact Finset.sum_congr rfl fun i _ => Real.log_prod (fun j _ =>
      (one_sub_node_mul_pos (ht _) (ht _)).ne')
  rw [hdet, Real.log_div hVV.ne' hden0.ne', ← hVa, Real.log_mul (abs_pos.mpr hV).ne'
    (abs_pos.mpr hV).ne', log_abs_vandermonde t' hinj', hlogden]
  have hoff := sum_offdiag_eq_two_mul (p := Fintype.card κ)
    (fun i j => Real.log |t' i - t' j|) (fun i j => by rw [abs_sub_comm])
  have hoff' : (∑ i : Fin (Fintype.card κ), ∑ j ∈ Finset.Ioi i, Real.log |t' j - t' i|) =
      ∑ i : Fin (Fintype.card κ), ∑ j ∈ Finset.Ioi i, Real.log |t' i - t' j| :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [abs_sub_comm]
  have hD : (∑ a, ∑ b, lgd t a b) = ∑ i : Fin (Fintype.card κ), ∑ j : Fin (Fintype.card κ),
      if i = j then (0 : ℝ) else Real.log |t' i - t' j| := by
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [lgd, ht', e.injective.eq_iff]
  have hC : (∑ a, ∑ b, lgc t a b) =
      ∑ i : Fin (Fintype.card κ), ∑ j : Fin (Fintype.card κ), Real.log (1 - t' i * t' j) := by
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [lgc, ht']
  rw [hD, hC]
  linarith [hoff, hoff']

end CauchyLog

section PairIdentity

open CatalanMeasure.Parametric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lgd_sub (z : ι → ℝ) (T : Finset ι) (a b : {a // a ∉ T}) :
    lgd (fun a : {a // a ∉ T} => z a.1) a b = lgd z a.1 b.1 := by
  unfold lgd
  exact (subtype_ite_eq a b _ _).symm

theorem sum_sub_compl (T : Finset ι) (f : ι → ι → ℝ) :
    ∑ a : {a // a ∉ T}, ∑ b : {a // a ∉ T}, f a.1 b.1 = ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, f a b := by
  have h : ∀ x, x ∈ Tᶜ ↔ x ∉ T := fun x => Finset.mem_compl
  calc ∑ a : {a // a ∉ T}, ∑ b : {a // a ∉ T}, f a.1 b.1
      = ∑ a : {a // a ∉ T}, ∑ b ∈ Tᶜ, f a.1 b :=
        Finset.sum_congr rfl fun a _ => (Finset.sum_subtype Tᶜ h (fun b => f a.1 b)).symm
    _ = ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, f a b := (Finset.sum_subtype Tᶜ h (fun a => ∑ b ∈ Tᶜ, f a b)).symm

/-- `log |B'(z_a)| = Σ_c log |z_a - z_c| - Σ_c log (1 - z_c z_a)`. -/
theorem log_abs_bdr (z : ι → ℝ) (hz1 : ∀ a, |z a| < 1) (hinj : Function.Injective z) (a : ι) :
    Real.log |bdr z a| = (∑ c, lgd z a c) - ∑ c, lgc z c a := by
  have hden : 0 < ∏ c, (1 - z c * z a) :=
    Finset.prod_pos fun c _ => one_sub_node_mul_pos (hz1 c) (hz1 a)
  have hne : ∀ c ∈ Finset.univ.erase a, z a - z c ≠ 0 := fun c hc =>
    sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hc).1 (hinj h).symm)
  have hnum : ∏ c ∈ Finset.univ.erase a, (z a - z c) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  unfold bdr
  rw [abs_div, abs_of_pos hden, Real.log_div (abs_ne_zero.mpr hnum) hden.ne', Real.log_abs,
    Real.log_prod hne,
    Real.log_prod (fun c _ => (one_sub_node_mul_pos (hz1 c) (hz1 a)).ne')]
  congr 1
  have h0 : lgd z a a = 0 := by simp [lgd]
  rw [← Finset.sum_erase Finset.univ h0]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [lgd, if_neg (Finset.mem_erase.mp hc).1.symm, Real.log_abs]

/-- The modulus of the Vandermonde, `exp (½ Σ lgd)`, times `W_T`. -/
def Wdet (z : ι → ℝ) (e : ℕ) (T : Finset ι) : ℝ :=
  (∏ a ∈ T, |bdr z a * z a ^ e|) * (kR (fun a : {a // a ∉ T} => z a.1)).det / (kR z).det

/-- The exponent of the near-type term (pairs inside `Tᶜ`, inside `T`, across, and the field
`e log |z|`). -/
def lamS (z : ι → ℝ) (e : ℕ) (T : Finset ι) : ℝ :=
  (1 / 2) * (∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, lgd z a b) + (1 / 2) * (∑ a ∈ T, ∑ b ∈ T, lgd z a b) +
    (∑ a ∈ T, ∑ b ∈ Tᶜ, lgc z a b) + (e : ℝ) * ∑ a ∈ T, Real.log |z a|

theorem Wdet_pos (z : ι → ℝ) (hinj : Function.Injective z) (hz1 : ∀ a, |z a| < 1)
    (hz0 : ∀ a, z a ≠ 0) (e : ℕ) (T : Finset ι) : 0 < Wdet z e T := by
  have hK := (log_det_kR z hinj hz1).1
  have hS := (log_det_kR (fun a : {a // a ∉ T} => z a.1)
    (fun a b h => Subtype.ext (hinj h)) (fun a => hz1 a.1)).1
  unfold Wdet
  refine div_pos (mul_pos (Finset.prod_pos fun a _ => ?_) hS) hK
  exact abs_pos.mpr (mul_ne_zero (bdr_ne_zero hinj hz1 a) (pow_ne_zero _ (hz0 a)))

/-- **The pair identity of Lemma 17.43.1**: `|V(z)| · W_T = exp (lamS z e T)`, i.e.
`|V(z)| W_T = |V(z_{Tᶜ})| |V(z_T)| ∏_{a ∈ T, b ∉ T} (1 - z_a z_b) ∏_{a ∈ T} |z_a|^e`. -/
theorem exp_vand_mul_Wdet (z : ι → ℝ) (hinj : Function.Injective z) (hz1 : ∀ a, |z a| < 1)
    (hz0 : ∀ a, z a ≠ 0) (e : ℕ) (T : Finset ι) :
    Real.exp ((1 / 2) * ∑ a, ∑ b, lgd z a b) * Wdet z e T = Real.exp (lamS z e T) := by
  have hW := Wdet_pos z hinj hz1 hz0 e T
  obtain ⟨hKp, hKl⟩ := log_det_kR z hinj hz1
  obtain ⟨hSp, hSl⟩ := log_det_kR (fun a : {a // a ∉ T} => z a.1)
    (fun a b h => Subtype.ext (hinj h)) (fun a => hz1 a.1)
  have hprod : 0 < ∏ a ∈ T, |bdr z a * z a ^ e| :=
    Finset.prod_pos fun a _ => abs_pos.mpr (mul_ne_zero (bdr_ne_zero hinj hz1 a)
      (pow_ne_zero _ (hz0 a)))
  have hlogprod : Real.log (∏ a ∈ T, |bdr z a * z a ^ e|) =
      ∑ a ∈ T, ((∑ c, lgd z a c) - (∑ c, lgc z c a) + (e : ℝ) * Real.log |z a|) := by
    rw [Real.log_prod (fun a _ => (abs_pos.mpr (mul_ne_zero (bdr_ne_zero hinj hz1 a)
      (pow_ne_zero _ (hz0 a)))).ne')]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [abs_mul, Real.log_mul (abs_pos.mpr (bdr_ne_zero hinj hz1 a)).ne'
      (abs_pos.mpr (pow_ne_zero _ (hz0 a))).ne', log_abs_bdr z hz1 hinj a, abs_pow, Real.log_pow]
  have hlogW : Real.log (Wdet z e T) =
      ∑ a ∈ T, ((∑ c, lgd z a c) - (∑ c, lgc z c a) + (e : ℝ) * Real.log |z a|) +
        Real.log (kR (fun a : {a // a ∉ T} => z a.1)).det - Real.log (kR z).det := by
    unfold Wdet
    rw [Real.log_div (mul_pos hprod hSp).ne' hKp.ne', Real.log_mul hprod.ne' hSp.ne', hlogprod]
  rw [← Real.exp_log hW, ← Real.exp_add]
  congr 1
  have hlgc_sub : ∀ a b : {a // a ∉ T},
      lgc (fun a : {a // a ∉ T} => z a.1) a b = lgc z a.1 b.1 := fun a b => rfl
  rw [hlogW, hSl, hKl]
  simp only [lgd_sub, hlgc_sub]
  rw [sum_sub_compl T (lgd z), sum_sub_compl T (lgc z)]
  have hsplit_d := sum_sum_split T (lgd z)
  have hsplit_c := sum_sum_split T (lgc z)
  have hsd := sum_cross_symm T (lgd z) (lgd_symm z)
  have hsc := sum_cross_symm T (lgc z) (lgc_symm z)
  have hrowsplit : ∀ f : ι → ι → ℝ, ∑ a ∈ T, ∑ c, f a c =
      (∑ a ∈ T, ∑ c ∈ T, f a c) + ∑ a ∈ T, ∑ c ∈ Tᶜ, f a c := by
    intro f
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_add_sum_compl T (f a)).symm
  have h1 := hrowsplit (lgd z)
  have h2 : ∑ a ∈ T, ∑ c, lgc z c a = ∑ a ∈ T, ∑ c, lgc z a c :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => lgc_symm z c a
  have h3 := hrowsplit (lgc z)
  have h4 : ∑ a ∈ T, ((∑ c, lgd z a c) - (∑ c, lgc z c a) + (e : ℝ) * Real.log |z a|) =
      (∑ a ∈ T, ∑ c, lgd z a c) - (∑ a ∈ T, ∑ c, lgc z c a) +
        (e : ℝ) * ∑ a ∈ T, Real.log |z a| := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold lamS
  rw [h4]
  linarith

end PairIdentity

section MainExpand

open CatalanMeasure.GenD.Signed CatalanMeasure.Parametric OAI.InternalCatalan

theorem abs_vandermonde_eq_exp {n : ℕ} (x : Fin n → ℝ) (hinj : Function.Injective x) :
    |(Matrix.vandermonde x).det| = Real.exp ((1 / 2) * ∑ a, ∑ b, lgd x a b) := by
  have hpos : 0 < |(Matrix.vandermonde x).det| :=
    abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  have hlog : Real.log |(Matrix.vandermonde x).det| = (1 / 2) * ∑ a, ∑ b, lgd x a b := by
    rw [Matrix.det_vandermonde, log_abs_vandermonde x hinj]
    have hoff := sum_offdiag_eq_two_mul (fun i j => Real.log |x i - x j|)
      (fun i j => by rw [abs_sub_comm])
    have h3 : ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| =
        ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |x i - x j| :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [abs_sub_comm]
    have h2 : (∑ a, ∑ b, lgd x a b) =
        ∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Real.log |x i - x j| := rfl
    rw [h2, hoff, h3]
    ring
  rw [← hlog, Real.exp_log hpos]

/-- **Lemma 17.43.1 (determinant side).**  For the marked Laurent matrix, from Lemma T for ALL
positive nodes (`hT`), the determinant is bounded by the sum over the subsets `S` of the marked
positives of `6^{|S|} 11^{q-|S|}` times `exp (lamS)`, the near-type (second-sheet) product
`|V(z_{Sᶜ})| |V(z_S)| ∏_{a ∈ S, b ∉ S} (1 - z_a z_b) ∏_{a ∈ S} |z_a|^{n-1-2g}`. -/
theorem abs_det_laurent_le_marked_expand {n k q g : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin n)
    (x : Fin n → ℝ) (mk : Fin n → Bool)
    (hinj : Function.Injective x) (hx1 : ∀ i, |x i| < 1) (hx0 : ∀ i, x i ≠ 0)
    (hneg : ∀ b, x (σ (Sum.inl b)) < 0) (hpos : ∀ p, 0 < x (σ (Sum.inr p)))
    (hk : 0 < k) (hq : 2 * g < q)
    (hT : ∀ c : Fin n → ℝ, |∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
        CatalanMeasure.Signed.bDeriv x a * x a ^ (n - 1 - 2 * g) * c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b)) :
    |(markedLaurentMatrix g x mk).det| ≤
      (∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        Real.exp (logRatioZ (q - g) (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p)))) *
        ∑ S : Finset (Fin q),
          (if ∀ p ∈ S, mk (σ (Sum.inr p)) = true then
            (6 : ℝ) ^ S.card * 11 ^ (q - S.card) *
              Real.exp (lamS (fun i => x (σ i)) (n - 1 - 2 * g)
                (S.map Function.Embedding.inr)) else 0) := by
  classical
  have hcard := Fintype.card_congr σ
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hg : 2 * g + 1 ≤ n := by omega
  -- node data on the sign-split index type
  obtain ⟨z, hz⟩ : ∃ z : Fin k ⊕ Fin q → ℝ, z = fun i => x (σ i) := ⟨_, rfl⟩
  obtain ⟨xn, hxn⟩ : ∃ xn : Fin k → ℝ, xn = fun b => x (σ (Sum.inl b)) := ⟨_, rfl⟩
  obtain ⟨gp, hgp⟩ : ∃ gp : Fin q → ℝ, gp = fun p => x (σ (Sum.inr p)) := ⟨_, rfl⟩
  have hzx : ∀ i, z i = x (σ i) := fun i => by rw [hz]
  have hxnx : ∀ b, xn b = x (σ (Sum.inl b)) := fun b => by rw [hxn]
  have hgpx : ∀ p, gp p = x (σ (Sum.inr p)) := fun p => by rw [hgp]
  have hzl : ∀ b, z (Sum.inl b) = xn b := fun b => by rw [hzx, hxnx]
  have hzr : ∀ p, z (Sum.inr p) = gp p := fun p => by rw [hzx, hgpx]
  rw [← hxn, ← hgp]
  have hzinj : Function.Injective z := by rw [hz]; exact hinj.comp σ.injective
  have hz1 : ∀ i, |z i| < 1 := fun i => by rw [hzx]; exact hx1 _
  have hz0 : ∀ i, z i ≠ 0 := fun i => by rw [hzx]; exact hx0 _
  have hxninj : Function.Injective xn := fun a b h => by
    rw [hxn] at h; exact Sum.inl_injective (σ.injective (hinj h))
  have hxn1 : ∀ b, |xn b| < 1 := fun b => by rw [hxnx]; exact hx1 _
  have hxn0 : ∀ b, xn b ≠ 0 := fun b => by rw [hxnx]; exact hx0 _
  have hgp1 : ∀ p, |gp p| < 1 := fun p => by rw [hgpx]; exact hx1 _
  -- Laurent matrix to the weighted Vandermonde-type matrix
  have hL := abs_det_laurent_eq_marked hg x mk hx0
  have h51 := lemma51_weighted (omegaM x mk) (n - 1 - 2 * g) x hinj hx0 hx1
  have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hKx : 0 < (kMat x).det := kR_det_pos hinj hx0 hx1
  -- the reindexed real matrix
  obtain ⟨d, hd⟩ : ∃ d : Fin k ⊕ Fin q → ℝ,
      d = fun i => bdr z i * z i ^ (n - 1 - 2 * g) := ⟨_, rfl⟩
  have hbd : ∀ i, bdr z i = CatalanMeasure.Signed.bDeriv x (σ i) := fun i => by
    rw [hz]; exact bdr_comp σ x i
  have hnb : ∀ a, negBlaschkeDeriv x a = CatalanMeasure.Signed.bDeriv x a := fun a => rfl
  obtain ⟨dg, hdg⟩ : ∃ dg : Fin q → ℝ,
      dg = fun p => if mk (σ (Sum.inr p)) = true then 0 else d (Sum.inr p) := ⟨_, rfl⟩
  obtain ⟨dF, hdF⟩ : ∃ dF : Fin k ⊕ Fin q → ℝ,
      dF = Sum.elim (fun b => d (Sum.inl b)) (fun p => d (Sum.inr p) - 6 * dg p) := ⟨_, rfl⟩
  have hMι : (kMat x + dW (omegaM x mk) (n - 1 - 2 * g) x).submatrix σ σ =
      kR z + Matrix.diagonal dF := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, kMat, kR, Matrix.of_apply, dW,
      Matrix.diagonal_apply, σ.injective.eq_iff]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      rw [hz]
      rcases i with b | p
      · have h1 : omegaM x mk (σ (Sum.inl b)) = 1 := by simp [omegaM, hneg b]
        simp only [hdF, hd, Sum.elim_inl, h1, hnb, ← hbd, hz]
        ring
      · by_cases hm : mk (σ (Sum.inr p)) = true
        · have h1 : omegaM x mk (σ (Sum.inr p)) = 1 := by simp [omegaM, hm]
          simp only [hdF, hd, hdg, Sum.elim_inr, h1, hnb, ← hbd, hz, hm, if_true]
          ring
        · have h1 : omegaM x mk (σ (Sum.inr p)) = -5 := by
            simp [omegaM, hm, not_lt.mpr (hpos p).le]
          have hm' : mk (σ (Sum.inr p)) = false := by simpa using hm
          simp only [hdF, hd, hdg, Sum.elim_inr, h1, hnb, ← hbd, hz, hm', Bool.false_eq_true,
            if_false]
          ring
    · rw [if_neg hij, if_neg hij, hz]
  have hdet1 : (kMat x + dW (omegaM x mk) (n - 1 - 2 * g) x).det =
      (kR z + Matrix.diagonal dF).det := by
    rw [← hMι, Matrix.det_submatrix_equiv_self]
  have hdetK : (kMat x).det = (kR z).det := by
    have : (kMat x).submatrix σ σ = kR z := by
      ext i j; simp [kMat, kR, hz]
    rw [← this, Matrix.det_submatrix_equiv_self]
  -- complex positivity data
  have hKc : (kC z).PosDef := kC_posDef hzinj hz0 hz1
  have h1c : (kC z + diagC d).PosSemidef := by
    rw [hd]; exact pick_F_nonneg hzinj hz0 hz1 (n - 1 - 2 * g)
  have h2c : (kC z - diagC d).PosSemidef := by
    rw [hd]; exact pick_F_le_two_K hzinj hz0 hz1 (n - 1 - 2 * g)
  -- Lemma T for ALL positives, as complex Loewner inequalities
  obtain ⟨dgA, hdgA⟩ : ∃ dgA : Fin q → ℝ, dgA = fun p => d (Sum.inr p) := ⟨_, rfl⟩
  have hTι : ∀ u : Fin k ⊕ Fin q → ℝ,
      |∑ a, (Sum.elim (fun _ => (0 : ℝ)) dgA a) * u a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, u a * u b / (1 - z a * z b) := by
    have h := lemmaT_sum_form_marked σ x (fun _ => false) hneg hpos (by simpa using hT)
    rw [hdgA, hd, hz]
    simpa using h
  obtain ⟨h3c, h4c⟩ := lemmaT_loewner_complex z (Sum.elim (fun _ => 0) dgA) hTι
  -- the negative block
  have hs2 : q < 2 * (q - g) := by omega
  have he2 : (n - 1 - 2 * g) + q + 1 = 2 * (q - g) + k := by omega
  have hnb' := negBlock_posDef z hzinj hz0 hz1 (q - g) (n - 1 - 2 * g) hk hs2 he2
  have hxz : (fun b => z (Sum.inl b)) = xn := funext hzl
  have hgz : (fun p => z (Sum.inr p)) = gp := funext hzr
  rw [hxz, hgz] at hnb'
  obtain ⟨hM1', hA', hM1pos⟩ := hnb'
  have hM1 : (kC z).submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a)) =
      (kMat xn + dMinus (hOfRoots gp) q (n - 1 - 2 * g) xn).map (fun r : ℝ => (r : ℂ)) := by
    rw [hd]; exact hM1'
  have hA : ((kC z).submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).PosDef := by
    rw [hd]; exact hA'
  have hR0 := route_ratio_pos gp hgp1 (q - g) k (n - 1 - 2 * g) hk hs2 he2 xn hxninj hxn0 hxn1
  have hK11 : 0 < (kMat xn).det := kR_det_pos hxninj hxn0 hxn1
  have hsub11 : (kC z).submatrix Sum.inl Sum.inl = (kR xn).map (fun r : ℝ => (r : ℂ)) := by
    ext a b
    simp [kC, kR, hzl]
  have hGramS := fun S : Finset (Fin q) =>
    norm_det_gram_le_sub (kC z) d dgA hKc hA h1c h2c (τ := 3 / 2) (by norm_num) h3c h4c S
  -- assemble
  have hexp : Real.exp (logRatioZ (q - g) xn gp) =
      (kMat xn + dMinus (hOfRoots gp) q (n - 1 - 2 * g) xn).det / (kMat xn).det := by
    rw [← log_route_two gp hgp1 (q - g) k (n - 1 - 2 * g) hk hs2 he2 xn hxninj hxn0 hxn1]
    exact Real.exp_log hR0
  rw [hexp]
  set Dw := (kMat x + dW (omegaM x mk) (n - 1 - 2 * g) x).det with hDw
  set Dm := (dMatW (omegaM x mk) (n - 1 - 2 * g + n - 1) x).det with hDm
  set M1d := (kMat xn + dMinus (hOfRoots gp) q (n - 1 - 2 * g) xn).det with hM1d
  have hDmeq : Dm = (Matrix.vandermonde x).det * (Dw / (kMat x).det) := by
    rw [h51]; field_simp
  have hDmabs : |Dm| = |(Matrix.vandermonde x).det| * (|Dw| / (kMat x).det) := by
    rw [hDmeq, abs_mul, abs_div, abs_of_pos hKx]
  -- the expansion of the determinant
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin q → ℝ,
      δ = fun p => if mk (σ (Sum.inr p)) = true then 6 * d (Sum.inr p) else 0 := ⟨_, rfl⟩
  obtain ⟨dX, hdX⟩ : ∃ dX : Fin k ⊕ Fin q → ℝ,
      dX = Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dgA p) := ⟨_, rfl⟩
  have hsplitF : kR z + Matrix.diagonal dF =
      (kR z + Matrix.diagonal dX) + Matrix.diagonal (Sum.elim (fun _ : Fin k => (0 : ℝ)) δ) := by
    rw [add_assoc, Matrix.diagonal_add]
    congr 2
    funext a
    rcases a with b | p
    · simp [hdF, hdX]
    · by_cases hm : mk (σ (Sum.inr p)) = true
      · simp [hdF, hdX, hdg, hdgA, hδ, hm] <;> ring
      · simp [hdF, hdX, hdg, hdgA, hδ, hm]
  have hExp := det_add_diagonal_sum_expand (kR z + Matrix.diagonal dX) δ
  rw [← hsplitF] at hExp
  have hDwE : Dw = ∑ S : Finset (Fin q), (∏ p ∈ S, δ p) *
      ((kR z + Matrix.diagonal dX).submatrix (tailEmb S) (tailEmb S)).det := by
    exact hdet1.trans hExp
  -- the bound of one term
  have hterm : ∀ S : Finset (Fin q),
      |((kR z + Matrix.diagonal dX).submatrix (tailEmb S) (tailEmb S)).det| ≤
        11 ^ (q - S.card) * (M1d / (kMat xn).det) *
          ((kR z).submatrix (tailEmb S) (tailEmb S)).det := by
    intro S
    have hG := hGramS S
    have hX : ((kC z + diagC dX).submatrix (tailEmb S) (tailEmb S)) =
        ((kR z + Matrix.diagonal dX).submatrix (tailEmb S) (tailEmb S)).map
          (fun r : ℝ => (r : ℂ)) := by
      ext a b
      by_cases h : tailEmb S a = tailEmb S b <;>
        simp [kC, kR, diagC, Matrix.diagonal_apply, Matrix.submatrix_apply, h]
    have hKS : ((kC z).submatrix (tailEmb S) (tailEmb S)) =
        ((kR z).submatrix (tailEmb S) (tailEmb S)).map (fun r : ℝ => (r : ℂ)) := by
      ext a b
      simp [kC, kR, Matrix.submatrix_apply]
    have hXd : (kC z + diagC (Sum.elim (fun a => d (Sum.inl a))
        (fun p => d (Sum.inr p) - 6 * dgA p))) = kC z + diagC dX := by rw [hdX]
    rw [hXd, hX, hKS, hM1, hsub11, det_map_ofReal, det_map_ofReal,
      det_map_ofReal, det_map_ofReal, Complex.norm_real, Real.norm_eq_abs,
      Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re] at hG
    have h11 : (2 + 6 * (3 / 2 : ℝ)) = 11 := by norm_num
    have hcardS : Fintype.card {p : Fin q // p ∉ S} = q - S.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    rw [h11, hcardS] at hG
    have hb : |((kR z + Matrix.diagonal dX).submatrix (tailEmb S) (tailEmb S)).det| ≤
        11 ^ (q - S.card) * M1d * ((kR z).submatrix (tailEmb S) (tailEmb S)).det /
          (kMat xn).det := (le_div_iff₀ hK11).mpr hG
    calc _ ≤ _ := hb
      _ = _ := by ring
  have hWd : ∀ S : Finset (Fin q),
      Wdet z (n - 1 - 2 * g) (S.map Function.Embedding.inr) =
        (∏ p ∈ S, |d (Sum.inr p)|) * ((kR z).submatrix (tailEmb S) (tailEmb S)).det /
          (kR z).det := by
    intro S
    unfold Wdet
    rw [Finset.prod_map]
    congr 2
    · refine Finset.prod_congr rfl fun p _ => ?_
      simp [hd]
    · have e : (kR z).submatrix (tailEmb S) (tailEmb S) =
          (kR (fun a : {a // a ∉ S.map Function.Embedding.inr} => z a.1)).submatrix
            (tailEquiv (m := Fin k) S) (tailEquiv (m := Fin k) S) := by
        ext a b; rfl
      rw [e, Matrix.det_submatrix_equiv_self]
  have hVz : |(Matrix.vandermonde x).det| =
      Real.exp ((1 / 2) * ∑ a, ∑ b, lgd z a b) := by
    rw [abs_vandermonde_eq_exp x hinj]
    congr 2
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [lgd, hz, σ.injective.eq_iff]
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp ((1 / 2) * ∑ a, ∑ b, lgd z a b) := ⟨_, rfl⟩
  rw [← hEdef] at hVz
  -- the bound of the sum over S
  have hDwb : |Dw| / (kMat x).det ≤ ∑ S : Finset (Fin q),
      (M1d / (kMat xn).det) *
        ((if ∀ p ∈ S, mk (σ (Sum.inr p)) = true then
            (6 : ℝ) ^ S.card * 11 ^ (q - S.card) else 0) *
          Wdet z (n - 1 - 2 * g) (S.map Function.Embedding.inr)) := by
    rw [div_le_iff₀ hKx, hDwE]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [abs_mul]
    have hWS := hWd S
    rw [hWS]
    have hKp : 0 < (kR z).det := by rw [← hdetK]; exact hKx
    by_cases hm : ∀ p ∈ S, mk (σ (Sum.inr p)) = true
    · rw [if_pos hm]
      have hprod : |∏ p ∈ S, δ p| = (6 : ℝ) ^ S.card * ∏ p ∈ S, |d (Sum.inr p)| := by
        rw [Finset.abs_prod]
        have : ∀ p ∈ S, |δ p| = 6 * |d (Sum.inr p)| := by
          intro p hp
          rw [hδ]; simp only [hm p hp, if_true, abs_mul]; norm_num
        rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const]
      rw [hprod]
      have h1 := hterm S
      have hdd : 0 ≤ (6 : ℝ) ^ S.card * ∏ p ∈ S, |d (Sum.inr p)| :=
        mul_nonneg (by positivity) (Finset.prod_nonneg fun p _ => abs_nonneg _)
      calc (6 : ℝ) ^ S.card * (∏ p ∈ S, |d (Sum.inr p)|) *
            |((kR z + Matrix.diagonal dX).submatrix (tailEmb S) (tailEmb S)).det|
          ≤ (6 : ℝ) ^ S.card * (∏ p ∈ S, |d (Sum.inr p)|) *
            (11 ^ (q - S.card) * (M1d / (kMat xn).det) *
              ((kR z).submatrix (tailEmb S) (tailEmb S)).det) := by
            exact mul_le_mul_of_nonneg_left h1 hdd
        _ = _ := by
            rw [hdetK]; field_simp
    · rw [if_neg hm]
      push_neg at hm
      obtain ⟨p, hpS, hpm⟩ := hm
      have : ∏ p ∈ S, δ p = 0 := by
        apply Finset.prod_eq_zero hpS
        rw [hδ]; simp [hpm]
      rw [this]
      simp
  -- final assembly
  have hexpv : ∀ S : Finset (Fin q), E *
      Wdet z (n - 1 - 2 * g) (S.map Function.Embedding.inr) =
        Real.exp (lamS (fun i => x (σ i)) (n - 1 - 2 * g) (S.map Function.Embedding.inr)) := by
    intro S
    have := exp_vand_mul_Wdet z hzinj hz1 hz0 (n - 1 - 2 * g) (S.map Function.Embedding.inr)
    rw [← hEdef, hz] at this
    rw [hz]
    exact this
  have hPi : ∏ i, |lamM x mk i| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) ≤
      ∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) := by
    rw [Finset.prod_mul_distrib]
    have h1 : ∏ i, |lamM x mk i| ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
        (fun i _ => (abs_lamM_le x mk i).trans (by norm_num))
    have h2 : 0 ≤ ∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) :=
      Finset.prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
    nlinarith
  have hPi1 : 0 ≤ ∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) :=
    Finset.prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
  have hM1p : 0 ≤ M1d / (kMat xn).det := hR0.le
  rw [hL, hDmabs, hVz]
  have hsum : ∑ S : Finset (Fin q), (M1d / (kMat xn).det) *
      ((if ∀ p ∈ S, mk (σ (Sum.inr p)) = true then
            (6 : ℝ) ^ S.card * 11 ^ (q - S.card) else 0) *
        Wdet z (n - 1 - 2 * g) (S.map Function.Embedding.inr)) =
      (M1d / (kMat xn).det) * E⁻¹ *
        ∑ S : Finset (Fin q), (if ∀ p ∈ S, mk (σ (Sum.inr p)) = true then
            (6 : ℝ) ^ S.card * 11 ^ (q - S.card) *
              Real.exp (lamS (fun i => x (σ i)) (n - 1 - 2 * g)
                (S.map Function.Embedding.inr)) else 0) := by
    rw [mul_assoc]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hE := hexpv S
    have hEp : 0 < E := by rw [hEdef]; exact Real.exp_pos _
    by_cases hm : ∀ p ∈ S, mk (σ (Sum.inr p)) = true
    · simp only [if_pos hm]
      rw [← hE]
      field_simp
    · simp [hm]
  have hEp : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  calc (∏ i, |lamM x mk i| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (E * (|Dw| / (kMat x).det))
      ≤ (∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (E * (|Dw| / (kMat x).det)) :=
        mul_le_mul_of_nonneg_right hPi (by positivity)
    _ ≤ (∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (E * ∑ S : Finset (Fin q),
          (M1d / (kMat xn).det) *
            ((if ∀ p ∈ S, mk (σ (Sum.inr p)) = true then
                (6 : ℝ) ^ S.card * 11 ^ (q - S.card) else 0) *
              Wdet z (n - 1 - 2 * g) (S.map Function.Embedding.inr))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDwb hEp.le) hPi1
    _ = _ := by
        rw [hsum]
        have hE0 := hEp.ne'
        field_simp

end MainExpand

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.det_add_diagonal_expand
#print axioms CatalanMeasure.Signed.det_add_diagonal_sum_expand
#print axioms CatalanMeasure.Signed.norm_det_gram_le_sub
#print axioms CatalanMeasure.Signed.log_det_kR
#print axioms CatalanMeasure.Signed.exp_vand_mul_Wdet
#print axioms CatalanMeasure.Signed.abs_det_laurent_le_marked_expand
