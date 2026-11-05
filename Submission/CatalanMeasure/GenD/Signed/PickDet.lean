module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# Perturbed Schur-complement determinant bound (Theorem C.3) and the Pick Gram fact (A1)

Loewner order is expressed through `Matrix.PosSemidef`: `M ≤ N` means `(N - M).PosSemidef`.

* `abs_det_le_of_loewner`: for Hermitian `M` with `-r ≤ M ≤ r`, `|det M| ≤ r ^ card n`.
* `norm_det_fromBlocks_sub_le`: Theorem C.3 with constants `b, c`:
  if `fromBlocks A Cᴴ C D` is positive semidefinite and `≤ b`, `A` is positive definite and
  `-τ ≤ T ≤ τ`, then `‖det (fromBlocks A Cᴴ C (D - c • T))‖ ≤ (b + c τ) ^ card n * (det A).re`.
* `norm_det_fromBlocks_sub_le_two_six`: the case `b = 2`, `c = 6`.
* `posSemidef_geomGram`, `posSemidef_geomGram_tsum`: Pick kernel `∑_{m<e} (x_a conj x_b)^m` and
  `(1 - x_a conj x_b)⁻¹` are positive semidefinite.
-/

namespace CatalanMeasure.GenD.Signed

open Matrix
open scoped ComplexOrder

section Det

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvalues of a Hermitian matrix squeezed between `-r` and `r` are bounded by `r`. -/
theorem abs_eigenvalue_le {M : Matrix n n ℂ} (hM : M.IsHermitian) {r : ℝ}
    (h1 : ((r : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef)
    (h2 : ((r : ℂ) • (1 : Matrix n n ℂ) + M).PosSemidef) (i : n) :
    |hM.eigenvalues i| ≤ r := by
  set v : n → ℂ := ⇑(hM.eigenvectorBasis i) with hv
  have hn : star v ⬝ᵥ v = 1 := by
    have h := hM.eigenvectorBasis.orthonormal.1 i
    have h' : inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis i) = 1 := by
      simpa using h
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h'
    simpa [hv, dotProduct_comm] using h'
  have e := hM.eigenvalues_eq i
  have q1 := h1.dotProduct_mulVec_nonneg v
  have q2 := h2.dotProduct_mulVec_nonneg v
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, hn] at q1
  rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, hn] at q2
  have r1 := Complex.nonneg_iff.mp q1
  have r2 := Complex.nonneg_iff.mp q2
  simp only [smul_eq_mul, mul_one, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at r1 r2
  rw [abs_le]
  have e' : hM.eigenvalues i = (star v ⬝ᵥ M *ᵥ v).re := by simpa using e
  constructor <;> linarith [r1.1, r2.1]

/-- `|det M| ≤ r ^ card n` for a Hermitian `M` with `-r ≤ M ≤ r`. -/
theorem norm_det_le_of_loewner {M : Matrix n n ℂ} (hM : M.IsHermitian) {r : ℝ}
    (h1 : ((r : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef)
    (h2 : ((r : ℂ) • (1 : Matrix n n ℂ) + M).PosSemidef) :
    ‖M.det‖ ≤ r ^ Fintype.card n := by
  rw [hM.det_eq_prod_eigenvalues, norm_prod]
  calc ∏ i, ‖(hM.eigenvalues i : ℂ)‖ ≤ ∏ _i : n, r := by
        gcongr with i
        simpa [Complex.norm_real] using abs_eigenvalue_le hM h1 h2 i
    _ = r ^ Fintype.card n := by simp

end Det

section Schur

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Theorem C.3 (general constants).  `L1 = fromBlocks A Cᴴ C D ≥ 0`, `L1 ≤ b`, `A > 0`,
`-τ ≤ T ≤ τ`. -/
theorem norm_det_fromBlocks_sub_le
    {A : Matrix m m ℂ} {C : Matrix n m ℂ} {D T : Matrix n n ℂ}
    (hA : A.PosDef)
    (hL : (fromBlocks A Cᴴ C D).PosSemidef)
    {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ((b : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks A Cᴴ C D).PosSemidef)
    {τ c : ℝ} (hc : 0 ≤ c)
    (hT1 : ((τ : ℂ) • (1 : Matrix n n ℂ) - T).PosSemidef)
    (hT2 : ((τ : ℂ) • (1 : Matrix n n ℂ) + T).PosSemidef) :
    ‖(fromBlocks A Cᴴ C (D - (c : ℂ) • T)).det‖ ≤
      (b + c * τ) ^ Fintype.card n * A.det.re := by
  classical
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - C * A⁻¹ * Cᴴ).PosSemidef := by
    have h := (PosDef.fromBlocks₁₁ (A := A) Cᴴ D hA).mp (by simpa using hL)
    simpa using h
  have hCAC : (C * A⁻¹ * Cᴴ).PosSemidef := hA.inv.posSemidef.mul_mul_conjTranspose_same C
  have hDb : ((b : ℂ) • (1 : Matrix n n ℂ) - D).PosSemidef := by
    have := hb.submatrix (Sum.inr : n → m ⊕ n)
    have e : ((b : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks A Cᴴ C D).submatrix
        Sum.inr Sum.inr = (b : ℂ) • (1 : Matrix n n ℂ) - D := by
      ext i j
      simp [Matrix.one_apply]
    rwa [e] at this
  have hcnn : (0 : ℂ) ≤ (c : ℂ) := Complex.zero_le_real.mpr hc
  have hbnn : (0 : ℂ) ≤ (b : ℂ) := Complex.zero_le_real.mpr hb0
  set M : Matrix n n ℂ := (D - (c : ℂ) • T) - C * ⅟A * Cᴴ with hMdef
  rw [invOf_eq_nonsing_inv] at hMdef
  have e1 : ((b + c * τ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - M =
      ((b : ℂ) • (1 : Matrix n n ℂ) - D) + C * A⁻¹ * Cᴴ +
        (c : ℂ) • ((τ : ℂ) • (1 : Matrix n n ℂ) + T) := by
    rw [hMdef]; push_cast; module
  have e2 : ((b + c * τ : ℝ) : ℂ) • (1 : Matrix n n ℂ) + M =
      (D - C * A⁻¹ * Cᴴ) + (b : ℂ) • (1 : Matrix n n ℂ) +
        (c : ℂ) • ((τ : ℂ) • (1 : Matrix n n ℂ) - T) := by
    rw [hMdef]; push_cast; module
  have h1 : (((b + c * τ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef := by
    rw [e1]; exact (hDb.add hCAC).add (hT2.smul hcnn)
  have h2 : (((b + c * τ : ℝ) : ℂ) • (1 : Matrix n n ℂ) + M).PosSemidef := by
    rw [e2]; exact (hS.add (PosSemidef.one.smul hbnn)).add (hT1.smul hcnn)
  have hMh : M.IsHermitian := by
    have hr : (((b + c * τ : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
      isHermitian_one.smul (by rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])
    have := hr.sub h1.1
    simpa using this
  have hbound := norm_det_le_of_loewner hMh h1 h2
  have hdpos : 0 < A.det := hA.det_pos
  have hre : 0 < A.det.re := (Complex.lt_def.mp hdpos).1
  have him : A.det.im = 0 := ((Complex.lt_def.mp hdpos).2).symm
  have hAre : A.det = (A.det.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  rw [det_fromBlocks₁₁, norm_mul, invOf_eq_nonsing_inv]
  have hn : ‖A.det‖ = A.det.re := by
    rw [hAre, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]
    simp
  rw [hn, mul_comm]
  rw [hMdef] at hbound
  exact mul_le_mul_of_nonneg_right hbound hre.le

/-- Theorem C.3: the case `b = 2`, `c = 6`. -/
theorem norm_det_fromBlocks_sub_le_two_six
    {A : Matrix m m ℂ} {C : Matrix n m ℂ} {D T : Matrix n n ℂ}
    (hA : A.PosDef)
    (hL : (fromBlocks A Cᴴ C D).PosSemidef)
    (hb : ((2 : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks A Cᴴ C D).PosSemidef)
    {τ : ℝ}
    (hT1 : ((τ : ℂ) • (1 : Matrix n n ℂ) - T).PosSemidef)
    (hT2 : ((τ : ℂ) • (1 : Matrix n n ℂ) + T).PosSemidef) :
    ‖(fromBlocks A Cᴴ C (D - (6 : ℂ) • T)).det‖ ≤
      (2 + 6 * τ) ^ Fintype.card n * A.det.re := by
  have := norm_det_fromBlocks_sub_le (b := 2) (c := 6) hA hL (by norm_num)
    (by simpa using hb) (by norm_num) hT1 hT2
  simpa using this

end Schur

section Pick

variable {s : Type*} [Fintype s]

/-- Pick Gram fact (A1, finite form): `∑_{k<e} (x_a conj x_b)^k` is positive semidefinite
(a Gram matrix of the vectors `(x_a^k)_a`).  No size condition on `x` is needed. -/
theorem posSemidef_geomGram (x : s → ℂ) (e : ℕ) :
    (Matrix.of fun a b => ∑ k ∈ Finset.range e, (x a * star (x b)) ^ k).PosSemidef := by
  have h : (Matrix.of fun a b => ∑ k ∈ Finset.range e, (x a * star (x b)) ^ k) =
      ∑ k ∈ Finset.range e, vecMulVec (fun a => x a ^ k) (star fun a => x a ^ k) := by
    ext a b
    simp [Matrix.sum_apply, vecMulVec_apply, mul_pow]
  rw [h]
  clear h
  induction e with
  | zero => simpa using PosSemidef.zero
  | succ e ih =>
    rw [Finset.sum_range_succ]
    exact ih.add (posSemidef_vecMulVec_self_star _)

open Filter Topology in
/-- Pick Gram fact (A1, infinite form): for `‖x_a‖ < 1` the Szegő/Pick kernel
`(1 - x_a conj x_b)⁻¹` is positive semidefinite. -/
theorem posSemidef_geomGram_tsum (x : s → ℂ) (hx : ∀ a, ‖x a‖ < 1) :
    (Matrix.of fun a b => (1 - x a * star (x b))⁻¹).PosSemidef := by
  have hlt : ∀ a b, ‖x a * star (x b)‖ < 1 := fun a b => by
    rw [norm_mul, norm_star]
    nlinarith [hx a, hx b, norm_nonneg (x a), norm_nonneg (x b)]
  have ht : ∀ a b, Tendsto (fun e => ∑ k ∈ Finset.range e, (x a * star (x b)) ^ k) atTop
      (𝓝 (1 - x a * star (x b))⁻¹) := fun a b =>
    (hasSum_geometric_of_norm_lt_one (hlt a b)).tendsto_sum_nat
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext a b
    simp only [conjTranspose_apply, of_apply, star_inv₀, star_sub, star_one, star_mul, star_star]
  · intro y
    have hq : Tendsto (fun e => star y ⬝ᵥ ((Matrix.of fun a b =>
        ∑ k ∈ Finset.range e, (x a * star (x b)) ^ k) *ᵥ y)) atTop
        (𝓝 (star y ⬝ᵥ ((Matrix.of fun a b => (1 - x a * star (x b))⁻¹) *ᵥ y))) := by
      simp only [dotProduct, mulVec]
      exact tendsto_finsetSum _ fun a _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun b _ => (ht a b).mul tendsto_const_nhds)
    exact ge_of_tendsto hq (Eventually.of_forall fun e =>
      (posSemidef_geomGram x e).dotProduct_mulVec_nonneg y)

end Pick

end CatalanMeasure.GenD.Signed

#print axioms CatalanMeasure.GenD.Signed.abs_eigenvalue_le
#print axioms CatalanMeasure.GenD.Signed.norm_det_le_of_loewner
#print axioms CatalanMeasure.GenD.Signed.norm_det_fromBlocks_sub_le
#print axioms CatalanMeasure.GenD.Signed.norm_det_fromBlocks_sub_le_two_six
#print axioms CatalanMeasure.GenD.Signed.posSemidef_geomGram
#print axioms CatalanMeasure.GenD.Signed.posSemidef_geomGram_tsum
