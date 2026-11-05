module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ShiftMoments
@[expose] public section
set_option Elab.async false

/-!
# Rational Φ forms (design-free) for the cells of Theorem Z

Computable definitions (coefficient functions of Chebyshev polynomials, the covector
`Φ(J,S;a,b) = Σ_u α(u,J) a[S+1-u] + β(u,J) b[S-u]` over `ℚ`), so that exact identities
among cell values can be checked by `decide +kernel`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open OAI.InternalCatalan
namespace Q

/-- Coefficient of `x^i` in `T_n`. -/
def tc : ℕ → ℕ → ℤ
  | 0, i => if i = 0 then 1 else 0
  | 1, i => if i = 1 then 1 else 0
  | n + 2, i => 2 * (if i = 0 then 0 else tc (n + 1) (i - 1)) - tc n i

/-- Coefficient of `x^i` in `U_n`. -/
def uc : ℕ → ℕ → ℤ
  | 0, i => if i = 0 then 1 else 0
  | 1, i => if i = 1 then 2 else 0
  | n + 2, i => 2 * (if i = 0 then 0 else uc (n + 1) (i - 1)) - uc n i

/-- Coefficient of `x^i` in `U_{k-1}` (zero for `k = 0`). -/
def ucm (k : ℕ) (i : ℕ) : ℤ := if k = 0 then 0 else uc (k - 1) i

/-- Coefficient of `x^i` in `(x²-1) U_{k-1}`. -/
def aTm (k : ℕ) (i : ℕ) : ℤ := (if i < 2 then 0 else ucm k (i - 2)) - ucm k i

/-- Signed coefficient access (negative indices give `0`). -/
def cf (f : ℕ → ℤ) (i : ℤ) : ℤ := if 0 ≤ i then f i.toNat else 0

/-- `α(u,J)`. -/
def alphaQ (u J : ℕ) : ℚ := momentRatSigned ((u : ℤ) - 1) J

/-- `β(u,J) = -(3/2) Z(u,J)`. -/
def betaQ (u J : ℕ) : ℚ := -(3 / 2) * zetaRat u J

/-- The covector `Φ(J,S;a,b)`. -/
def PhiQ (a b : ℕ → ℤ) (J S : ℕ) : ℚ :=
  ∑ u ∈ Finset.range (S + 3),
    (alphaQ u J * (cf a ((S : ℤ) + 1 - u) : ℚ) + betaQ u J * (cf b ((S : ℤ) - u) : ℚ))

/-- `T+` slot of block `k`: `(a,b) = (T_k, U_{k-1})`. -/
def PhiTp (k J S : ℕ) : ℚ := PhiQ (tc k) (ucm k) J S

/-- `T-` slot of block `k`: `(a,b) = ((Y²-1) U_{k-1}, T_k)`. -/
def PhiTm (k J S : ℕ) : ℚ := PhiQ (aTm k) (tc k) J S

/-- `Td_S = T+_{S-1} - T+_S` (period form). -/
def PhiTd (k J S : ℕ) : ℚ := PhiTp k J (S - 1) - PhiTp k J S

/-- Profile combination over blocks `0..K-1`. -/
def comb (K : ℕ) (z : ℕ → ℚ) (f : ℕ → ℚ) : ℚ := ∑ k ∈ Finset.range K, z k * f k

example : PhiTp 2 1 4 = PhiTp 2 1 4 := rfl

end Q
end CatalanMeasure.GenD.Uniform.W.ZoneZ
