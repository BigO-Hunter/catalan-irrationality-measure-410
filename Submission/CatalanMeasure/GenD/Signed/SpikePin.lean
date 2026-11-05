module

public import Submission.CatalanMeasure.GenD.Signed.SpikeMonotone
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Pinning of `m` particles by `2m` spikes at the hard edge (Lemma 2⁻ of SIMPLIFY-S2 §2.2)

For `s = m + n` the Hankel matrix of a weight splits into blocks `A` (size `m`), `B`, `D` (size
`n`); `Sch` is the Schur complement `D - Bᵀ A⁻¹ B`.  Fischer's inequality bounds the numerator at
every depth, and the Schur complement of the denominator is monotone in the pole position and tends
to the Hankel matrix of the remaining weight (`pin_bound`).
-/

namespace CatalanMeasure.GenD.Signed

open MeasureTheory Matrix Finset Polynomial Set

/-! ### Determinants are monotone in the Loewner order -/

section DetMono

variable {k : ℕ}

theorem det_le_det_add {X P : Matrix (Fin k) (Fin k) ℝ} (hX : X.PosDef) (hP : P.PosSemidef) :
    X.det ≤ (X + P).det := by
  have hpd : ∀ l ∈ Icc (0 : ℝ) 1, (X + l • P).PosDef := fun l hl =>
    hX.add_posSemidef (hP.smul hl.1)
  have hdet : ∀ l ∈ Icc (0 : ℝ) 1, 0 < (X + l • P).det := fun l hl => (hpd l hl).det_pos
  have hd : ∀ l ∈ Icc (0 : ℝ) 1, HasDerivAt (fun l : ℝ => (X + l • P).det)
      ((X + l • P).det * ((X + l • P)⁻¹ * P).trace) l := fun l hl =>
    hasDerivAt_det_affine X P l (hdet l hl).ne'.isUnit
  have hmono : MonotoneOn (fun l : ℝ => (X + l • P).det) (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun l hl => (hd l hl).continuousAt.continuousWithinAt)
      (f' := fun l => (X + l • P).det * ((X + l • P)⁻¹ * P).trace)
      (fun l hl => (hd l (interior_subset hl)).hasDerivWithinAt) ?_
    intro l hl
    have hl' := interior_subset hl
    refine mul_nonneg (hdet l hl').le ?_
    rw [trace_mul_comm]
    exact trace_mul_nonneg hP (hpd l hl').posSemidef.inv
  have := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    zero_le_one
  simpa using this

theorem det_le_of_loewner {X Y : Matrix (Fin k) (Fin k) ℝ} (hX : X.PosDef)
    (h : (Y - X).PosSemidef) : X.det ≤ Y.det := by
  have := det_le_det_add hX h
  simpa using this

end DetMono

/-! ### Block decomposition and Fischer's inequality -/

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The off-diagonal block. -/
noncomputable def Bblk (μ : Measure ℝ) (w : ℝ → ℝ) (m n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ t, t ^ ((i : ℕ) + (m + (j : ℕ))) * w t ∂μ

/-- The Schur complement `D - Bᵀ A⁻¹ B` of the `(m,n)` block decomposition of `hk μ w (m+n)`. -/
noncomputable def Sch (μ : Measure ℝ) (w : ℝ → ℝ) (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  hk μ (fun t => t ^ (2 * m) * w t) n - (Bblk μ w m n)ᵀ * (hk μ w m)⁻¹ * Bblk μ w m n

theorem hk_blocks (μ : Measure ℝ) (w : ℝ → ℝ) (m n : ℕ) :
    (hk μ w (m + n)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (hk μ w m) (Bblk μ w m n) (Bblk μ w m n)ᵀ
        (hk μ (fun t => t ^ (2 * m) * w t) n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [hk]
  · simp [hk, Bblk]
  · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      fromBlocks_apply₂₁, transpose_apply, hk, Bblk, Matrix.of_apply, Fin.val_castAdd,
      Fin.val_natAdd]
    congr 1; funext t; rw [add_comm]
  · simp only [submatrix_apply, finSumFinEquiv_apply_right, fromBlocks_apply₂₂, hk,
      Matrix.of_apply, Fin.val_natAdd]
    congr 1; funext t; ring

theorem det_hk_split (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) (m n : ℕ) :
    (hk μ w (m + n)).det = (hk μ w m).det * (Sch μ w m n).det := by
  have hA := hk_posDef hμ hw m
  let _ := hA.isUnit.invertible
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)),
    hk_blocks, det_fromBlocks₁₁]
  simp [Sch, invOf_eq_nonsing_inv]

theorem sch_posDef (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) (m n : ℕ) :
    (Sch μ w m n).PosDef := by
  have hH := hk_posDef hμ hw (m + n)
  have hH' := hH.submatrix (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective
  rw [hk_blocks] at hH'
  have hA := hk_posDef hμ hw m
  let _ := hA.isUnit.invertible
  have hpsd : (Sch μ w m n).PosSemidef := by
    have h1 : (fromBlocks (hk μ w m) (Bblk μ w m n) (Bblk μ w m n)ᴴ
        (hk μ (fun t => t ^ (2 * m) * w t) n)).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hH'.posSemidef
    have h2 := (PosDef.fromBlocks₁₁ (Bblk μ w m n) (hk μ (fun t => t ^ (2 * m) * w t) n) hA).mp h1
    simpa [Sch, conjTranspose_eq_transpose_of_trivial] using h2
  rw [hpsd.posDef_iff_det_ne_zero]
  have hd := det_hk_split hμ hw m n
  intro h0
  rw [h0, mul_zero] at hd
  exact hH.det_pos.ne' hd

theorem sch_loewner (hμ : Setting μ) {w v : ℝ → ℝ} (hw : Adm w) (hv : Bd v) (m n : ℕ)
    (h : ∀ t ∈ Icc (0 : ℝ) 2, t ^ (2 * m) * w t ≤ v t) :
    (hk μ v n - Sch μ w m n).PosSemidef := by
  have hA := hk_posDef hμ hw m
  have hbd : Bd (fun t => t ^ (2 * m) * w t) :=
    (Bd.of_continuous (continuous_pow _)).mul hw.toBd
  have h1 : (hk μ v n - hk μ (fun t => t ^ (2 * m) * w t) n).PosSemidef := by
    rw [← hk_sub hμ.supp hv hbd]
    refine hk_posSemidef hμ.supp (hv.sub hbd) ?_ n
    filter_upwards [hμ.supp] with t ht
    linarith [h t ht]
  have h2 : ((Bblk μ w m n)ᵀ * (hk μ w m)⁻¹ * Bblk μ w m n).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hA.inv.posSemidef.conjTranspose_mul_mul_same (Bblk μ w m n)
  have := h1.add h2
  convert this using 1
  simp only [Sch]; abel

/-- Fischer's inequality for Hankel matrices. -/
theorem det_hk_le (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) (m n : ℕ) :
    (hk μ w (m + n)).det ≤ (hk μ w m).det * (hk μ (fun t => t ^ (2 * m) * w t) n).det := by
  rw [det_hk_split hμ hw m n]
  refine mul_le_mul_of_nonneg_left ?_ (hk_posDef hμ hw m).det_pos.le
  have hbd : Bd (fun t => t ^ (2 * m) * w t) :=
    (Bd.of_continuous (continuous_pow _)).mul hw.toBd
  exact det_le_of_loewner (sch_posDef hμ hw m n) (sch_loewner hμ hw hbd m n (fun t _ => le_rfl))

/-! ### The ratio bound at a finite pole position -/

/-- The weight with `2m` poles at `-A`. -/
noncomputable def wpole (ψ : ℝ → ℝ) (A : ℝ) (m : ℕ) (t : ℝ) : ℝ := ψ t * poleK A t ^ (2 * m)

theorem adm_wpole {ψ : ℝ → ℝ} (hψ : Adm ψ) {A : ℝ} (hA : 0 < A) (m : ℕ) : Adm (wpole ψ A m) :=
  hψ.mul ((adm_poleK hA).pow (2 * m))

theorem pole_pow_le {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (m : ℕ) :
    t ^ (2 * m) * poleK A t ^ (2 * m) ≤ 1 := by
  rw [← mul_pow]
  have h0 : 0 ≤ t * poleK A t := mul_nonneg ht (inv_nonneg.mpr (by linarith))
  refine pow_le_one₀ h0 ?_
  unfold poleK
  rw [← div_eq_mul_inv]
  exact (div_le_one (by linarith)).mpr (by linarith)

theorem rat_le_pin (hμ : Setting μ) {ψ φ : ℝ → ℝ} (hψ : Adm ψ) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) (m n : ℕ) {A : ℝ} (hA : 0 < A) :
    rat μ φ (wpole ψ A m) (m + n) ≤
      φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det / (Sch μ (wpole ψ A m) m n).det := by
  have hw := adm_wpole hψ hA m
  have hwφ : Adm (fun t => φ t * wpole ψ A m t) := hφ.mul hw
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := by simp
  -- numerator
  have hnum1 : (hk μ (fun t => φ t * wpole ψ A m t) m).det ≤
      φ 0 ^ m * (hk μ (wpole ψ A m) m).det := by
    have hb : Bd (fun t => φ 0 * wpole ψ A m t - φ t * wpole ψ A m t) :=
      ((Bd.const (φ 0)).mul hw.toBd).sub hwφ.toBd
    have hpsd : (hk μ (fun t => φ 0 * wpole ψ A m t - φ t * wpole ψ A m t) m).PosSemidef := by
      refine hk_posSemidef hμ.supp hb ?_ m
      filter_upwards [hμ.supp] with t ht
      have := hφa h0 ht ht.1
      have := hw.pos ht
      nlinarith
    rw [hk_sub hμ.supp ((Bd.const (φ 0)).mul hw.toBd) hwφ.toBd, hk_smul] at hpsd
    have := det_le_of_loewner (hk_posDef hμ hwφ m) hpsd
    rwa [Matrix.det_smul, Fintype.card_fin] at this
  have hnum2 : (Sch μ (fun t => φ t * wpole ψ A m t) m n).det ≤
      (hk μ (fun t => φ t * ψ t) n).det := by
    refine det_le_of_loewner (sch_posDef hμ hwφ m n)
      (sch_loewner hμ hwφ (hφ.toBd.mul hψ.toBd) m n ?_)
    intro t ht
    have h1 := pole_pow_le hA ht.1 m
    have h2 := hφ.pos ht
    have h3 := hψ.pos ht
    simp only [wpole]
    calc t ^ (2 * m) * (φ t * (ψ t * poleK A t ^ (2 * m)))
        = (φ t * ψ t) * (t ^ (2 * m) * poleK A t ^ (2 * m)) := by ring
      _ ≤ (φ t * ψ t) * 1 := mul_le_mul_of_nonneg_left h1 (mul_pos h2 h3).le
      _ = φ t * ψ t := mul_one _
  have hAw := (hk_posDef hμ hw m).det_pos
  have hSw := (sch_posDef hμ hw m n).det_pos
  have hSφ := (sch_posDef hμ hwφ m n).det_pos
  have hAφ := (hk_posDef hμ hwφ m).det_pos
  unfold rat
  rw [det_hk_split hμ hwφ m n, det_hk_split hμ hw m n]
  have hφ0 : 0 < φ 0 := hφ.pos h0
  calc (hk μ (fun t => φ t * wpole ψ A m t) m).det *
        (Sch μ (fun t => φ t * wpole ψ A m t) m n).det /
        ((hk μ (wpole ψ A m) m).det * (Sch μ (wpole ψ A m) m n).det)
      ≤ (φ 0 ^ m * (hk μ (wpole ψ A m) m).det * (hk μ (fun t => φ t * ψ t) n).det) /
        ((hk μ (wpole ψ A m) m).det * (Sch μ (wpole ψ A m) m n).det) := by
        refine div_le_div_of_nonneg_right ?_ (mul_pos hAw hSw).le
        exact mul_le_mul hnum1 hnum2 hSφ.le (by positivity)
    _ = φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det / (Sch μ (wpole ψ A m) m n).det := by
        field_simp

/-! ### Quadratic forms and the variational characterisation of the Schur complement -/

theorem append_quad {m n : ℕ} (H : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) (x : Fin m → ℝ)
    (z : Fin n → ℝ) :
    (Fin.append x z) ⬝ᵥ (H *ᵥ Fin.append x z) =
      (x ⊕ᵥ z) ⬝ᵥ ((H.submatrix finSumFinEquiv finSumFinEquiv) *ᵥ (x ⊕ᵥ z)) := by
  simp [dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, submatrix_apply]

theorem eval_polyOf_append {m n : ℕ} (x : Fin m → ℝ) (z : Fin n → ℝ) (t : ℝ) :
    (polyOf (Fin.append x z)).eval t = (polyOf x).eval t + t ^ m * (polyOf z).eval t := by
  simp only [eval_polyOf, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.val_castAdd,
    Fin.val_natAdd, Finset.mul_sum, pow_add]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quad_split {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) [Invertible A] (hA : A.IsHermitian) (x : Fin m → ℝ)
    (z : Fin n → ℝ) :
    (x ⊕ᵥ z) ⬝ᵥ ((fromBlocks A B Bᵀ D) *ᵥ (x ⊕ᵥ z)) =
      (x + (A⁻¹ * B) *ᵥ z) ⬝ᵥ (A *ᵥ (x + (A⁻¹ * B) *ᵥ z)) +
        z ⬝ᵥ ((D - Bᵀ * A⁻¹ * B) *ᵥ z) := by
  have := schur_complement_eq₁₁ B D x z hA
  simp only [star_trivial, ← dotProduct_mulVec, conjTranspose_eq_transpose_of_trivial] at this
  exact this

/-- The quadratic form `∫ (P_y + t^m P_c)² w dμ`. -/
noncomputable def Qint (μ : Measure ℝ) (w : ℝ → ℝ) {m n : ℕ} (y : Fin m → ℝ) (c : Fin n → ℝ) :
    ℝ :=
  ∫ t, ((polyOf y).eval t + t ^ m * (polyOf c).eval t) ^ 2 * w t ∂μ

theorem Qint_eq (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) {m n : ℕ} (y : Fin m → ℝ)
    (c : Fin n → ℝ) :
    Qint μ w y c = (y + ((hk μ w m)⁻¹ * Bblk μ w m n) *ᵥ c) ⬝ᵥ
        (hk μ w m *ᵥ (y + ((hk μ w m)⁻¹ * Bblk μ w m n) *ᵥ c)) +
      c ⬝ᵥ (Sch μ w m n *ᵥ c) := by
  have h1 := hk_quad hμ.supp hw.toBd (Fin.append y c)
  simp_rw [eval_polyOf_append] at h1
  unfold Qint
  rw [← h1, append_quad, hk_blocks]
  have hA := hk_posDef hμ hw m
  let _ := hA.isUnit.invertible
  exact quad_split _ _ _ (hk_isHermitian w m) y c

theorem sch_quad_le (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) {m n : ℕ} (y : Fin m → ℝ)
    (c : Fin n → ℝ) : c ⬝ᵥ (Sch μ w m n *ᵥ c) ≤ Qint μ w y c := by
  rw [Qint_eq hμ hw]
  have := (hk_posDef hμ hw m).posSemidef.dotProduct_mulVec_nonneg
    (y + ((hk μ w m)⁻¹ * Bblk μ w m n) *ᵥ c)
  simp only [star_trivial] at this
  linarith

theorem sch_quad_exists (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) {m n : ℕ} (c : Fin n → ℝ) :
    ∃ y : Fin m → ℝ, Qint μ w y c = c ⬝ᵥ (Sch μ w m n *ᵥ c) := by
  refine ⟨-(((hk μ w m)⁻¹ * Bblk μ w m n) *ᵥ c), ?_⟩
  rw [Qint_eq hμ hw]
  simp

theorem Qint_mono (hμ : Setting μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) (m : ℕ) {a a' : ℝ} (ha : 0 < a)
    (haa : a ≤ a') {n : ℕ} (y : Fin m → ℝ) (c : Fin n → ℝ) :
    Qint μ (wpole ψ a' m) y c ≤ Qint μ (wpole ψ a m) y c := by
  have hpb : Bd (fun t => ((polyOf y).eval t + t ^ m * (polyOf c).eval t) ^ 2) :=
    Bd.of_continuous (((polyOf y).continuous.add ((continuous_pow m).mul (polyOf c).continuous)).pow 2)
  have i1 := (hpb.mul (adm_wpole hψ (ha.trans_le haa) m).toBd).integrable hμ.supp
  have i2 := (hpb.mul (adm_wpole hψ ha m).toBd).integrable hμ.supp
  refine integral_mono_ae i1 i2 ?_
  filter_upwards [hμ.supp] with t ht
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have h1 : poleK a' t ≤ poleK a t := inv_anti₀ (by linarith [ht.1]) (by linarith)
  have h2 : 0 ≤ poleK a' t := inv_nonneg.mpr (by linarith [ht.1])
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 _) (hψ.pos ht).le

theorem sch_quad_mono (hμ : Setting μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) (m n : ℕ) {a a' : ℝ}
    (ha : 0 < a) (haa : a ≤ a') (c : Fin n → ℝ) :
    c ⬝ᵥ (Sch μ (wpole ψ a' m) m n *ᵥ c) ≤ c ⬝ᵥ (Sch μ (wpole ψ a m) m n *ᵥ c) := by
  obtain ⟨y, hy⟩ := sch_quad_exists hμ (adm_wpole hψ ha m) (m := m) c
  rw [← hy]
  exact (sch_quad_le hμ (adm_wpole hψ (ha.trans_le haa) m) y c).trans
    (Qint_mono hμ hψ m ha haa y c)

theorem sch_quad_le_hk (hμ : Setting μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) (m n : ℕ) {a : ℝ} (ha : 0 < a)
    (c : Fin n → ℝ) : c ⬝ᵥ (Sch μ (wpole ψ a m) m n *ᵥ c) ≤ c ⬝ᵥ (hk μ ψ n *ᵥ c) := by
  have h := sch_loewner hμ (adm_wpole hψ ha m) hψ.toBd m n (fun t ht => by
    have h1 := pole_pow_le ha ht.1 m
    have h2 := hψ.pos ht
    simp only [wpole]
    calc t ^ (2 * m) * (ψ t * poleK a t ^ (2 * m))
        = ψ t * (t ^ (2 * m) * poleK a t ^ (2 * m)) := by ring
      _ ≤ ψ t * 1 := mul_le_mul_of_nonneg_left h1 h2.le
      _ = ψ t := mul_one _)
  have := h.dotProduct_mulVec_nonneg c
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at this
  linarith

/-! ### The hard edge: divergence of the pinned quadratic form -/

/-- `μ` has no atom at `0` and carries mass `≳ √a` on `[a/4, a]` (a hard edge at `t = 0`). -/
structure HardEdge (μ : Measure ℝ) : Prop where
  atom : μ {0} = 0
  mass : ∃ κ : ℝ, 0 < κ ∧ ∃ a0 : ℝ, 0 < a0 ∧ ∀ a : ℝ, 0 < a → a ≤ a0 →
    κ * a ≤ (μ.real (Icc (a / 4) a)) ^ 2

theorem coeff_polyOf {m : ℕ} (y : Fin m → ℝ) (d : ℕ) :
    (polyOf y).coeff d = if h : d < m then y ⟨d, h⟩ else 0 := by
  simp only [polyOf, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨d, h⟩]
    · simp
    · intro i _ hi
      have : d ≠ (i : ℕ) := fun e => hi (Fin.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : d ≠ (i : ℕ) := by have := i.2; omega
    simp [this]

theorem polyOf_factor {m : ℕ} {y : Fin m → ℝ} (hy : y ≠ 0) :
    ∃ (j : ℕ) (q : ℝ[X]), j < m ∧ polyOf y = X ^ j * q ∧ q.eval 0 ≠ 0 := by
  have hp := polyOf_ne_zero hy
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (polyOf y) hp 0
  simp only [map_zero, sub_zero] at hq hnd
  set j := (polyOf y).rootMultiplicity 0
  have hq0 : q.eval 0 ≠ 0 := by
    intro h
    apply hnd
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact h
  refine ⟨j, q, ?_, hq, hq0⟩
  by_contra hjm
  have h1 : (polyOf y).coeff j = q.coeff 0 := by
    rw [hq, coeff_X_pow_mul']; simp
  rw [coeff_polyOf, coeff_zero_eq_eval_zero] at h1
  simp only [hjm, dite_false] at h1
  exact hq0 h1.symm

theorem window_bound (hμ : Setting μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) {m n : ℕ} {y : Fin m → ℝ}
    (hy : y ≠ 0) (c : Fin n → ℝ) :
    ∃ (K1 η : ℝ), 0 < K1 ∧ 0 < η ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → a < η →
      (K1 / a ^ 2) * μ.real (Icc (a / 4) a) ≤ Qint μ (wpole ψ a m) y c := by
  obtain ⟨j, q, hjm, hpq, hq0⟩ := polyOf_factor hy
  obtain ⟨cψ, hcψ, hcψ'⟩ := hψ.lower
  set T1 : ℝ[X] := q + X ^ (m - j) * polyOf c with hT1def
  have hT1 : ∀ t : ℝ, (polyOf y).eval t + t ^ m * (polyOf c).eval t = t ^ j * T1.eval t := by
    intro t
    have e : t ^ m = t ^ j * t ^ (m - j) := by rw [← pow_add]; congr 1; omega
    rw [hpq, e]
    simp only [hT1def, eval_add, eval_mul, eval_pow, eval_X]
    ring
  have hT10 : T1.eval 0 = q.eval 0 := by
    simp [hT1def, zero_pow (show m - j ≠ 0 by omega)]
  have hq0' : 0 < |q.eval 0| := abs_pos.mpr hq0
  obtain ⟨η, hη, hηT⟩ : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η → |q.eval 0| / 2 ≤ |T1.eval t| := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp T1.continuous.continuousAt (|q.eval 0| / 2)
      (by positivity)
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have := h (show dist t 0 < δ by simpa [Real.dist_eq] using ht)
    rw [Real.dist_eq, hT10] at this
    have h2 := abs_sub_abs_le_abs_sub (q.eval 0) (T1.eval t)
    rw [abs_sub_comm] at this
    linarith
  set K1' : ℝ := ((4 : ℝ) ^ (2 * m) * 2 ^ (2 * m))⁻¹ with hK1'
  have hK1'pos : 0 < K1' := by positivity
  refine ⟨(|q.eval 0| / 2) ^ 2 * cψ * K1', η, by positivity, hη, ?_⟩
  intro a ha ha1 haη
  have hpb : Bd (fun t => ((polyOf y).eval t + t ^ m * (polyOf c).eval t) ^ 2) :=
    Bd.of_continuous (((polyOf y).continuous.add
      ((continuous_pow m).mul (polyOf c).continuous)).pow 2)
  have hwa := adm_wpole hψ ha m
  have hint := (hpb.mul hwa.toBd).integrable hμ.supp
  have hnn : 0 ≤ᵐ[μ] fun t => ((polyOf y).eval t + t ^ m * (polyOf c).eval t) ^ 2 * wpole ψ a m t := by
    filter_upwards [hμ.supp] with t ht
    exact mul_nonneg (sq_nonneg _) (hwa.pos ht).le
  unfold Qint
  refine le_trans ?_ (setIntegral_le_integral hint hnn (s := Icc (a / 4) a))
  have hconst : ∫ _ in Icc (a / 4) a, ((|q.eval 0| / 2) ^ 2 * cψ * K1') / a ^ 2 ∂μ =
      ((|q.eval 0| / 2) ^ 2 * cψ * K1' / a ^ 2) * μ.real (Icc (a / 4) a) := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  rw [← hconst]
  refine setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc ?_
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have hta : t ≤ a := ht.2
  have htI : t ∈ Icc (0 : ℝ) 2 := ⟨ht0.le, by linarith⟩
  rw [hT1 t]
  have hT : |q.eval 0| / 2 ≤ |T1.eval t| := hηT t (by rw [abs_of_pos ht0]; linarith)
  have hT2 : (|q.eval 0| / 2) ^ 2 ≤ (T1.eval t) ^ 2 := by
    rw [← sq_abs (T1.eval t)]; exact pow_le_pow_left₀ (by positivity) hT 2
  have htj : (a / 4) ^ j ≤ t ^ j := pow_le_pow_left₀ (by positivity) ht.1 j
  have hpole : (2 * a)⁻¹ ≤ poleK a t :=
    show (2 * a)⁻¹ ≤ (a + t)⁻¹ from inv_anti₀ (by linarith) (by linarith)
  have hψt : cψ ≤ ψ t := hcψ' t htI
  have hψpos : 0 < ψ t := hψ.pos htI
  have A1 : ((a / 4) ^ j) ^ 2 ≤ (t ^ j) ^ 2 := pow_le_pow_left₀ (by positivity) htj 2
  have A4 : ((2 * a)⁻¹) ^ (2 * m) ≤ poleK a t ^ (2 * m) :=
    pow_le_pow_left₀ (by positivity) hpole _
  have hpow : a ^ (2 * m) ≤ a ^ (2 * j + 2) := pow_le_pow_of_le_one ha.le ha1 (by omega)
  have h4 : (4 : ℝ) ^ (2 * j) ≤ 4 ^ (2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hE : K1' / a ^ 2 ≤ ((a / 4) ^ j) ^ 2 * ((2 * a)⁻¹) ^ (2 * m) := by
    rw [div_le_iff₀ (by positivity)]
    have hu : ((2 * a)⁻¹) ^ (2 * m) = 1 / (2 ^ (2 * m) * a ^ (2 * m)) := by
      rw [inv_pow, mul_pow, one_div]
    have hv : ((a / 4) ^ j) ^ 2 = a ^ (2 * j) / 4 ^ (2 * j) := by
      rw [← pow_mul, div_pow, mul_comm j 2]
    have e : ((a / 4) ^ j) ^ 2 * ((2 * a)⁻¹) ^ (2 * m) * a ^ 2 =
        a ^ (2 * j + 2) / (a ^ (2 * m) * 4 ^ (2 * j) * 2 ^ (2 * m)) := by
      rw [hu, hv]
      field_simp
      ring
    rw [e]
    calc K1' = a ^ (2 * j + 2) / (a ^ (2 * j + 2) * (4 ^ (2 * m) * 2 ^ (2 * m))) := by
          rw [hK1']; field_simp
      _ ≤ a ^ (2 * j + 2) / (a ^ (2 * m) * 4 ^ (2 * j) * 2 ^ (2 * m)) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          calc a ^ (2 * m) * 4 ^ (2 * j) * 2 ^ (2 * m)
              ≤ a ^ (2 * j + 2) * 4 ^ (2 * m) * 2 ^ (2 * m) := by gcongr
            _ = a ^ (2 * j + 2) * (4 ^ (2 * m) * 2 ^ (2 * m)) := by ring
  simp only [wpole]
  calc (|q.eval 0| / 2) ^ 2 * cψ * K1' / a ^ 2
      = ((|q.eval 0| / 2) ^ 2 * cψ) * (K1' / a ^ 2) := by ring
    _ ≤ ((|q.eval 0| / 2) ^ 2 * cψ) * (((a / 4) ^ j) ^ 2 * ((2 * a)⁻¹) ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = ((|q.eval 0| / 2) ^ 2 * ((a / 4) ^ j) ^ 2) * (cψ * ((2 * a)⁻¹) ^ (2 * m)) := by ring
    _ ≤ ((T1.eval t) ^ 2 * (t ^ j) ^ 2) * (ψ t * poleK a t ^ (2 * m)) :=
        mul_le_mul (mul_le_mul hT2 A1 (by positivity) (by positivity))
          (mul_le_mul hψt A4 (by positivity) hψpos.le) (by positivity)
          (by have := hψpos.le; positivity)
    _ = (t ^ j * T1.eval t) ^ 2 * (ψ t * poleK a t ^ (2 * m)) := by ring

theorem Qint_diverges (hμ : Setting μ) (hH : HardEdge μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) {m n : ℕ}
    {y : Fin m → ℝ} (hy : y ≠ 0) (c : Fin n → ℝ) (L : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a ≤ δ → L < Qint μ (wpole ψ a m) y c := by
  obtain ⟨K1, η, hK1, hη, hwin⟩ := window_bound hμ hψ hy c (n := n)
  obtain ⟨κ, hκ, a0, ha0, hmass⟩ := hH.mass
  refine ⟨min (min a0 (η / 2)) (min 1 (K1 ^ 2 * κ / (L ^ 2 + 1))), by positivity, ?_⟩
  intro a ha haδ
  have ha0' : a ≤ a0 := haδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have haη : a < η := lt_of_le_of_lt (haδ.trans ((min_le_left _ _).trans (min_le_right _ _))) (by linarith)
  have ha1 : a ≤ 1 := haδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haK : a ≤ K1 ^ 2 * κ / (L ^ 2 + 1) :=
    haδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine lt_of_lt_of_le ?_ (hwin a ha ha1 haη)
  set P := (K1 / a ^ 2) * μ.real (Icc (a / 4) a) with hP
  have hP0 : 0 ≤ P := by positivity
  have hW := hmass a ha ha0'
  have hP2 : L ^ 2 + 1 ≤ P ^ 2 := by
    have e1 : P ^ 2 = (K1 ^ 2 / a ^ 4) * (μ.real (Icc (a / 4) a)) ^ 2 := by
      rw [hP]; field_simp
    have e2 : (K1 ^ 2 / a ^ 4) * (κ * a) = K1 ^ 2 * κ / a ^ 3 := by field_simp
    have e3 : K1 ^ 2 * κ / a ≤ K1 ^ 2 * κ / a ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [pow_pos ha 2, pow_pos ha 3, mul_le_mul_of_nonneg_left ha1 (pow_pos ha 2).le])
    have e4 : L ^ 2 + 1 ≤ K1 ^ 2 * κ / a := by
      rw [le_div_iff₀ ha]
      rw [le_div_iff₀ (by positivity)] at haK
      linarith
    calc L ^ 2 + 1 ≤ K1 ^ 2 * κ / a := e4
      _ ≤ K1 ^ 2 * κ / a ^ 3 := e3
      _ = (K1 ^ 2 / a ^ 4) * (κ * a) := e2.symm
      _ ≤ (K1 ^ 2 / a ^ 4) * (μ.real (Icc (a / 4) a)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = P ^ 2 := e1.symm
  by_contra hcon
  have hcon := not_lt.mp hcon
  nlinarith [hP0, hcon]

/-! ### Compactness: the Schur complement tends to the Hankel matrix of the remaining weight -/

theorem continuous_Qint (hμ : Setting μ) {w : ℝ → ℝ} (hw : Adm w) {m n : ℕ} (c : Fin n → ℝ) :
    Continuous fun y : Fin m → ℝ => Qint μ w y c := by
  have : (fun y : Fin m → ℝ => Qint μ w y c) = fun y =>
      (y + ((hk μ w m)⁻¹ * Bblk μ w m n) *ᵥ c) ⬝ᵥ
        (hk μ w m *ᵥ (y + ((hk μ w m)⁻¹ * Bblk μ w m n) *ᵥ c)) +
      c ⬝ᵥ (Sch μ w m n *ᵥ c) := funext fun y => Qint_eq hμ hw y c
  rw [this]
  unfold dotProduct mulVec
  fun_prop

theorem norm_le_of_dotProduct_le {m : ℕ} {y : Fin m → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : y ⬝ᵥ y ≤ R ^ 2) : ‖y‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  rw [Real.norm_eq_abs]
  have h1 : y i * y i ≤ y ⬝ᵥ y := by
    unfold dotProduct
    exact Finset.single_le_sum (f := fun i => y i * y i) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have h2 : (y i) ^ 2 ≤ R ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' h2 hR |> fun h3 => abs_le.mpr h3

theorem posDef_coercive {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef) :
    ∃ l : ℝ, 0 < l ∧ ∀ y : Fin m → ℝ, l * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, one_pos, fun y => by simp [Subsingleton.elim y 0]⟩
  set K : Set (Fin m → ℝ) := {y | y ⬝ᵥ y = 1} with hK
  have hcd : Continuous fun y : Fin m → ℝ => y ⬝ᵥ y := by
    unfold dotProduct; fun_prop
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq hcd continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_dotProduct_le zero_le_one (by simpa [hK] using hy.le)
  have hne : K.Nonempty := ⟨Pi.single ⟨0, hm⟩ 1, by simp [hK]⟩
  have hcf : Continuous fun y : Fin m → ℝ => y ⬝ᵥ (A *ᵥ y) := by
    unfold dotProduct mulVec; fun_prop
  obtain ⟨y0, hy0, hmin⟩ := hKc.exists_isMinOn hne hcf.continuousOn
  have hy0ne : y0 ≠ 0 := by
    intro h; have : y0 ⬝ᵥ y0 = 1 := hy0
    rw [h] at this; simp at this
  have hl : 0 < y0 ⬝ᵥ (A *ᵥ y0) := by
    have := hA.dotProduct_mulVec_pos hy0ne
    simpa using this
  refine ⟨y0 ⬝ᵥ (A *ᵥ y0), hl, fun y => ?_⟩
  by_cases hy : y ⬝ᵥ y = 0
  · have : y = 0 := dotProduct_self_eq_zero.mp hy
    subst this; simp
  · have hnn : 0 ≤ y ⬝ᵥ y := by
      unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hpos : 0 < y ⬝ᵥ y := lt_of_le_of_ne hnn (Ne.symm hy)
    set r := Real.sqrt (y ⬝ᵥ y) with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = y ⬝ᵥ y := Real.sq_sqrt hpos.le
    set yh : Fin m → ℝ := r⁻¹ • y with hyh
    have hyhK : yh ∈ K := by
      show yh ⬝ᵥ yh = 1
      rw [hyh, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      field_simp
      linarith
    have h1 := hmin hyhK
    have hy_eq : y = r • yh := by
      rw [hyh, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    have h2 : y ⬝ᵥ (A *ᵥ y) = r ^ 2 * (yh ⬝ᵥ (A *ᵥ yh)) := by
      conv_lhs => rw [hy_eq]
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      ring
    rw [h2, ← hr2, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg r)

theorem tendsto_Qint_zero (hμ : Setting μ) (hμ0 : μ {0} = 0) {ψ : ℝ → ℝ} (hψ : Adm ψ) (m : ℕ)
    {n : ℕ} (c : Fin n → ℝ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hlim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => Qint μ (wpole ψ (a k) m) (0 : Fin m → ℝ) c) Filter.atTop
      (nhds (c ⬝ᵥ (hk μ ψ n *ᵥ c))) := by
  have hpb : Bd (fun t => ((polyOf c).eval t) ^ 2) :=
    Bd.of_continuous ((polyOf c).continuous.pow 2)
  have hbd : Bd (fun t => ((polyOf c).eval t) ^ 2 * ψ t) := hpb.mul hψ.toBd
  have hq := hk_quad hμ.supp hψ.toBd c
  rw [hq]
  have h0 : polyOf (0 : Fin m → ℝ) = 0 := by simp [polyOf]
  have hF : ∀ k, ∀ t, ((polyOf (0 : Fin m → ℝ)).eval t + t ^ m * (polyOf c).eval t) ^ 2 *
      wpole ψ (a k) m t = ((polyOf c).eval t) ^ 2 * ψ t * (t * poleK (a k) t) ^ (2 * m) := by
    intro k t
    simp only [h0, eval_zero, zero_add, wpole, mul_pow, ← pow_mul]
    ring
  have hpbF : ∀ k, Bd (fun t => ((polyOf (0 : Fin m → ℝ)).eval t +
      t ^ m * (polyOf c).eval t) ^ 2 * wpole ψ (a k) m t) := fun k =>
    (Bd.of_continuous (((polyOf (0 : Fin m → ℝ)).continuous.add
      ((continuous_pow m).mul (polyOf c).continuous)).pow 2)).mul (adm_wpole hψ (ha k) m).toBd
  unfold Qint
  refine tendsto_integral_of_dominated_convergence (fun t => ((polyOf c).eval t) ^ 2 * ψ t)
    (fun k => (hpbF k).meas.aestronglyMeasurable) (hbd.integrable hμ.supp) (fun k => ?_) ?_
  · filter_upwards [hμ.supp] with t ht
    rw [hF k t, Real.norm_eq_abs]
    have h1 : (t * poleK (a k) t) ^ (2 * m) ≤ 1 := by
      rw [mul_pow]; exact pole_pow_le (ha k) ht.1 m
    have h2 : 0 ≤ (t * poleK (a k) t) ^ (2 * m) := by
      have : 0 ≤ t * poleK (a k) t :=
        mul_nonneg ht.1 (inv_nonneg.mpr (by linarith [ha k, ht.1]))
      positivity
    have h3 : 0 ≤ ((polyOf c).eval t) ^ 2 * ψ t := mul_nonneg (sq_nonneg _) (hψ.pos ht).le
    rw [abs_of_nonneg (mul_nonneg h3 h2)]
    calc ((polyOf c).eval t) ^ 2 * ψ t * (t * poleK (a k) t) ^ (2 * m)
        ≤ ((polyOf c).eval t) ^ 2 * ψ t * 1 := mul_le_mul_of_nonneg_left h1 h3
      _ = _ := mul_one _
  · have hnz : ∀ᵐ t ∂μ, t ∉ ({0} : Set ℝ) := measure_eq_zero_iff_ae_notMem.mp hμ0
    filter_upwards [hnz] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp_rw [hF]
    have h1 : Filter.Tendsto (fun k => poleK (a k) t) Filter.atTop (nhds t⁻¹) := by
      have := ((hlim.add_const t).inv₀ (by simpa using ht0))
      simpa [poleK] using this
    have h2 : Filter.Tendsto (fun k => (t * poleK (a k) t) ^ (2 * m)) Filter.atTop
        (nhds 1) := by
      have := (h1.const_mul t).pow (2 * m)
      simpa [mul_inv_cancel₀ ht0] using this
    simpa using h2.const_mul (((polyOf c).eval t) ^ 2 * ψ t)

theorem limit_quad (hμ : Setting μ) (hH : HardEdge μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) (m n : ℕ)
    (c : Fin n → ℝ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hanti : Antitone a)
    (hlim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => c ⬝ᵥ (Sch μ (wpole ψ (a k) m) m n *ᵥ c)) Filter.atTop
      (nhds (c ⬝ᵥ (hk μ ψ n *ᵥ c))) := by
  set u : ℕ → ℝ := fun k => c ⬝ᵥ (Sch μ (wpole ψ (a k) m) m n *ᵥ c) with hu
  set Dc := c ⬝ᵥ (hk μ ψ n *ᵥ c) with hDc
  have hmono : Monotone u := monotone_nat_of_le_succ fun k =>
    sch_quad_mono hμ hψ m n (ha (k + 1)) (hanti (Nat.le_succ k)) c
  have hbdd : ∀ k, u k ≤ Dc := fun k => sch_quad_le_hk hμ hψ m n (ha k) c
  have hbddA : BddAbove (Set.range u) := ⟨Dc, by rintro _ ⟨k, rfl⟩; exact hbdd k⟩
  set L := ⨆ k, u k with hL
  have hconv : Filter.Tendsto u Filter.atTop (nhds L) := tendsto_atTop_ciSup hmono hbddA
  have hLle : L ≤ Dc := ciSup_le hbdd
  have huL : ∀ k, u k ≤ L := fun k => le_ciSup hbddA k
  have hge : Dc ≤ L := by
    obtain ⟨y, hy⟩ : ∃ y : ℕ → (Fin m → ℝ), ∀ k, Qint μ (wpole ψ (a k) m) (y k) c = u k := by
      choose y hy using fun k => sch_quad_exists hμ (adm_wpole hψ (ha k) m) (m := m) c
      exact ⟨y, hy⟩
    have hyN : ∀ N k, N ≤ k → Qint μ (wpole ψ (a N) m) (y k) c ≤ L := by
      intro N k hNk
      calc Qint μ (wpole ψ (a N) m) (y k) c ≤ Qint μ (wpole ψ (a k) m) (y k) c :=
            Qint_mono hμ hψ m (ha k) (hanti hNk) (y k) c
        _ = u k := hy k
        _ ≤ L := huL k
    -- boundedness of the minimisers
    have hA0 := hk_posDef hμ (adm_wpole hψ (ha 0) m) m
    obtain ⟨l, hl, hlco⟩ := posDef_coercive hA0
    set z0 : Fin m → ℝ := ((hk μ (wpole ψ (a 0) m) m)⁻¹ * Bblk μ (wpole ψ (a 0) m) m n) *ᵥ c
      with hz0
    have hS0 : 0 ≤ c ⬝ᵥ (Sch μ (wpole ψ (a 0) m) m n *ᵥ c) := by
      have := (sch_posDef hμ (adm_wpole hψ (ha 0) m) m n).posSemidef.dotProduct_mulVec_nonneg c
      simpa using this
    have hL0 : 0 ≤ L := le_trans (by rw [hu]; exact hS0) (huL 0)
    have hbd : ∀ k, (y k + z0) ⬝ᵥ (y k + z0) ≤ (Real.sqrt (L / l)) ^ 2 := by
      intro k
      have h1 := hyN 0 k (Nat.zero_le k)
      rw [Qint_eq hμ (adm_wpole hψ (ha 0) m)] at h1
      have h2 := hlco (y k + z0)
      rw [Real.sq_sqrt (div_nonneg hL0 hl.le), le_div_iff₀ hl]
      nlinarith
    obtain ⟨w, -, φ, hφ, hwlim⟩ :=
      (isCompact_closedBall (0 : Fin m → ℝ) (Real.sqrt (L / l))).tendsto_subseq
      (x := fun k => y k + z0) (fun k => by
        rw [mem_closedBall_zero_iff]
        exact norm_le_of_dotProduct_le (Real.sqrt_nonneg _) (hbd k))
    set ystar : Fin m → ℝ := w - z0 with hystar
    have hytend : Filter.Tendsto (fun j => y (φ j)) Filter.atTop (nhds ystar) := by
      have := hwlim.sub_const z0
      simpa [hystar] using this
    have hN : ∀ N, Qint μ (wpole ψ (a N) m) ystar c ≤ L := by
      intro N
      have hc := continuous_Qint hμ (adm_wpole hψ (ha N) m) (m := m) c
      have ht := (hc.tendsto ystar).comp hytend
      refine le_of_tendsto ht ?_
      filter_upwards [Filter.eventually_ge_atTop N] with j hj
      exact hyN N (φ j) (le_trans hj (hφ.id_le j))
    have hys0 : ystar = 0 := by
      by_contra hne
      obtain ⟨δ, hδ, hdiv⟩ := Qint_diverges hμ hH hψ hne c L
      obtain ⟨N, hNδ⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
      have := hdiv (a N) (ha N) hNδ.le
      linarith [hN N]
    have hQ0 : ∀ N, Qint μ (wpole ψ (a N) m) (0 : Fin m → ℝ) c ≤ L := by
      intro N; have := hN N; rwa [hys0] at this
    exact le_of_tendsto' (tendsto_Qint_zero hμ hH.atom hψ m c ha hlim) hQ0
  have hLeq : L = Dc := le_antisymm hLle hge
  rw [hLeq] at hconv
  exact hconv

theorem tendsto_matrix_of_quad {n : ℕ} {S : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hS : ∀ k, (S k).IsHermitian) (hD : D.IsHermitian)
    (h : ∀ c : Fin n → ℝ, Filter.Tendsto (fun k => c ⬝ᵥ (S k *ᵥ c)) Filter.atTop
      (nhds (c ⬝ᵥ (D *ᵥ c)))) : Filter.Tendsto S Filter.atTop (nhds D) := by
  have polar : ∀ (M : Matrix (Fin n) (Fin n) ℝ), M.IsHermitian → ∀ i j,
      M i j = ((Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) ⬝ᵥ
          (M *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin n → ℝ) ⬝ᵥ (M *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin n → ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1)) / 2 := by
    intro M hM i j
    have h := hM.apply j i
    simp only [star_trivial] at h
    simp [mulVec_add, dotProduct_add, add_dotProduct, h]
    ring
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have e1 : ∀ k, S k i j = ((Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) ⬝ᵥ
          (S k *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin n → ℝ) ⬝ᵥ (S k *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin n → ℝ) ⬝ᵥ (S k *ᵥ Pi.single j 1)) / 2 :=
    fun k => polar _ (hS k) i j
  rw [polar D hD i j]
  simp_rw [e1]
  exact (((h _).sub (h _)).sub (h _)).div_const 2

theorem pin_det_tendsto (hμ : Setting μ) (hH : HardEdge μ) {ψ : ℝ → ℝ} (hψ : Adm ψ) (m n : ℕ)
    {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hanti : Antitone a)
    (hlim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => (Sch μ (wpole ψ (a k) m) m n).det) Filter.atTop
      (nhds (hk μ ψ n).det) := by
  have hS : Filter.Tendsto (fun k => Sch μ (wpole ψ (a k) m) m n) Filter.atTop
      (nhds (hk μ ψ n)) :=
    tendsto_matrix_of_quad (fun k => (sch_posDef hμ (adm_wpole hψ (ha k) m) m n).isHermitian)
      (hk_isHermitian ψ n) (fun c => limit_quad hμ hH hψ m n c ha hanti hlim)
  exact ((continuous_id.matrix_det).tendsto _).comp hS

theorem pin_bound (hμ : Setting μ) (hH : HardEdge μ) {ψ φ : ℝ → ℝ} (hψ : Adm ψ) (hφ : Adm φ)
    (hφa : AntitoneOn φ (Icc (0 : ℝ) 2)) {m n s : ℕ} (hs : s = m + n)
    (As : Fin (2 * m) → ℝ) (hAs : ∀ p, 0 < As p) :
    rat μ φ (fun t => ψ t * ∏ p, poleK (As p) t) s ≤
      φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det / (hk μ ψ n).det := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn : n = s := by omega
    subst hn
    refine le_of_eq ?_
    simp only [pow_zero, one_mul]
    unfold rat
    simp
  subst hs
  set a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hadef
  have ha : ∀ k, 0 < a k := fun k => by positivity
  have hanti : Antitone a := fun j k hjk => by
    simp only [hadef]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hlim : Filter.Tendsto a Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hD0 := (hk_posDef hμ hψ n).det_pos
  have hbound : ∀ᶠ k in Filter.atTop, rat μ φ (fun t => ψ t * ∏ p, poleK (As p) t) (m + n) ≤
      φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det / (Sch μ (wpole ψ (a k) m) m n).det := by
    have hev : ∀ᶠ k in Filter.atTop, ∀ p, a k ≤ As p := by
      rw [Filter.eventually_all]
      intro p
      exact (hlim.eventually (ge_mem_nhds (hAs p)))
    filter_upwards [hev] with k hk
    exact (rat_poles_le hμ hφ hφa (ha k) (2 * m) ψ hψ As hk (m + n)).trans
      (rat_le_pin hμ hψ hφ hφa m n (ha k))
  have hlimit : Filter.Tendsto (fun k => φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det /
      (Sch μ (wpole ψ (a k) m) m n).det) Filter.atTop
      (nhds (φ 0 ^ m * (hk μ (fun t => φ t * ψ t) n).det / (hk μ ψ n).det)) :=
    tendsto_const_nhds.div (pin_det_tendsto hμ hH hψ m n ha hanti hlim) hD0.ne'
  exact ge_of_tendsto hlimit hbound

#print axioms det_le_det_add
#print axioms det_hk_le
#print axioms rat_le_pin
#print axioms Qint_diverges
#print axioms limit_quad
#print axioms pin_bound

end CatalanMeasure.GenD.Signed
