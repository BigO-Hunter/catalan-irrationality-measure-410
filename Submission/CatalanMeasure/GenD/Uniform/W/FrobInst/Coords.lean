module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TKill
@[expose] public section
set_option Elab.async false

/-!
# Chebyshev-`U` coordinates of the monomials `y^s`

The T-pair rows of `Thin.PairRows` realise `Δ · Σ_d u_d U_d(y)` (up to the constant `2`).  A
Frobenius-product atom `Δ · y^lo · P(y)` therefore needs the coordinates of the monomials
`y^s`, `s < D`, in the basis `U_0, …, U_{D-1}`: they exist and are unique because
`deg U_d = d` and `2 ≠ 0` (`Polynomial.Sequence.span_degreeLT`).

* `ucoef hp2 D s : Fin D → F_p` with `Σ_d ucoef d • U_d = X^s` for `s < D` (`ucoef_spec`);
* `ucoef_lam` : the same coordinates against the slot polynomials `lam d = 2 (X-1)^h U_d`
  give `2 (X-1)^h X^s` coefficientwise (`ucoef_lamc`).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.Parametric
  CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The sequence `U_0, U_1, …` as a polynomial sequence over `F_p` (`p ≠ 2`). -/
def uSeq (hp2 : p ≠ 2) : Polynomial.Sequence (ZMod p) where
  elems' i := Chebyshev.U (ZMod p) (i : ℤ)
  degree_eq' i := by
    haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
    exact degree_U_natCast (ZMod p) i

theorem X_pow_mem_span_U (hp2 : p ≠ 2) (D s : ℕ) (hs : s < D) :
    (X ^ s : (ZMod p)[X]) ∈
      Submodule.span (ZMod p) (Set.range fun d : Fin D => Chebyshev.U (ZMod p) ((d : ℕ) : ℤ)) := by
  have hrange : (Set.range fun d : Fin D => Chebyshev.U (ZMod p) ((d : ℕ) : ℤ)) =
      (uSeq hp2) '' Set.Iio D := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.is_lt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hrange, (uSeq hp2).span_degreeLT
    (fun i _ => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr ((uSeq hp2).ne_zero i)))]
  rw [Polynomial.mem_degreeLT, degree_X_pow]
  exact_mod_cast hs

theorem exists_ucoef (hp2 : p ≠ 2) (D s : ℕ) (hs : s < D) :
    ∃ cs : Fin D → ZMod p, ∑ d : Fin D, C (cs d) * Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) = X ^ s := by
  obtain ⟨cs, hcs⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp
    (X_pow_mem_span_U hp2 D s hs)
  exact ⟨cs, by simpa [Polynomial.smul_eq_C_mul] using hcs⟩

/-- Coordinates of `y^s` in the basis `U_0 … U_{D-1}` (`0` if `s ≥ D`). -/
def ucoef (hp2 : p ≠ 2) (D s : ℕ) (d : Fin D) : ZMod p :=
  if hs : s < D then (Classical.choose (exists_ucoef hp2 D s hs)) d else 0

theorem ucoef_spec (hp2 : p ≠ 2) (D s : ℕ) (hs : s < D) :
    ∑ d : Fin D, C (ucoef hp2 D s d) * Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) = X ^ s := by
  have h := Classical.choose_spec (exists_ucoef hp2 D s hs)
  simpa [ucoef, hs] using h

/-- `Σ_d ucoef_d · lamc_d(e)` is the `e`-th coefficient of `2 (X-1)^h X^s`. -/
theorem ucoef_lamc (hp2 : p ≠ 2) (D s e : ℕ) (hs : s < D) :
    ∑ d : Fin D, lamc P N p (d : ℕ) e * ucoef hp2 D s d =
      (2 * (X - 1) ^ P.h N * X ^ s : (ZMod p)[X]).coeff e := by
  have h := ucoef_spec hp2 D s hs
  have h2 : (2 * (X - 1) ^ P.h N * X ^ s : (ZMod p)[X]) =
      ∑ d : Fin D, C (ucoef hp2 D s d) * lam P N p (d : ℕ) := by
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold lam
    ring
  rw [h2, finsetSum_coeff]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_C_mul, lamc]
  ring

/-- Low coefficients vanish: `coeff e (2 (X-1)^h X^s) = 0` for `e < s`. -/
theorem coeff_lam_mono_low (e s : ℕ) (h : ℕ) (hes : e < s) :
    (2 * (X - 1) ^ h * X ^ s : (ZMod p)[X]).coeff e = 0 := by
  rw [coeff_mul_X_pow']
  simp [not_le.mpr hes]

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
