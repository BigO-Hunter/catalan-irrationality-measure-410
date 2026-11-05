module

public import Submission.CatalanMeasure.Parametric.RealSheet

/-!
# The positive P-only column as an actual column and a near-sheet residual

This exact identity retains the actual sheet operator on the first summand.
It makes no asymptotic determinant or irrationality-measure claim.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Set OAI.InternalCatalan

noncomputable section

theorem positive_rowP_decomposition {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0 < N) (hr : r < P.n N)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (realPoly (rowP P N r)).eval (realCoordinateInv x) =
      -2 * realRowAmplitude P N r (realCoordinateInv x) +
        3 * ((1 - realCoordinateInv x) ^ P.h N *
          realCoordinateInv x ^ (P.C N - 1) * x ^ rowOffset P N r) := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  rw [rowP_realCoordinateInv_signed hP hN hr hx0,
    realRowAmplitude_sheet hP hN hr hx' hx0, if_neg (not_lt.mpr hx.1.le)]
  ring

/-- The residual has a nonnegative integer exponent after the usual far-sheet
factor is extracted. This is the source of its smallness near zero. -/
theorem near_sheet_factorization {n g r : ℕ} (hng : 2 * g < n)
    {x : ℝ} (hx : x ≠ 0) :
    x ^ ((r : ℤ) - g) =
      x ^ ((g : ℤ) - (n - 1 : ℕ)) * x ^ (n - 1 - 2 * g + r) := by
  rw [← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  omega

end

end CatalanMeasure.Parametric
