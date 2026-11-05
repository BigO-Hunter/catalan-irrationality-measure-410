module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.QForms
@[expose] public section
set_option Elab.async false

/-!
# Rational forms of the HY+ cells (H+ and H- profile maps)

Integer coefficient functions of the profile polynomials of the H+ pair
`(Gy, Ty) = ((1+X)(U_k - U_{k-1}), U_k + U_{k-1})` and of the H- pair
`(Gy, Ty) = ((X-1)(U_k + U_{k-1}), U_k - U_{k-1})` for an integer block index `k`
(`U_{-1} = 0`, `U_{-n-2} = -U_n`), and the rational covectors `PhiHp`, `PhiHm` of a profile
given by integer coordinates `z`.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open CatalanMeasure.GenD.Uniform.W.ZoneZ OAI.InternalCatalan

/-- Coefficient of `x^i` in `U_n`, `n : ℤ`. -/
def ucZ : ℤ → ℕ → ℤ
  | Int.ofNat m, i => Q.uc m i
  | Int.negSucc 0, _ => 0
  | Int.negSucc (m + 1), i => - Q.uc m i

/-- `V_n = U_n - U_{n-1}`. -/
def vc (n : ℤ) (i : ℕ) : ℤ := ucZ n i - ucZ (n - 1) i
/-- `W_n = U_n + U_{n-1}`. -/
def wc (n : ℤ) (i : ℕ) : ℤ := ucZ n i + ucZ (n - 1) i
/-- Coefficients of `X * f`. -/
def shl1 (f : ℕ → ℤ) (i : ℕ) : ℤ := if i = 0 then 0 else f (i - 1)

/-- `(1+X) V_n`. -/
def aHp (n : ℤ) (i : ℕ) : ℤ := vc n i + shl1 (vc n) i
/-- `(X-1) W_n`. -/
def aHm (n : ℤ) (i : ℕ) : ℤ := shl1 (wc n) i - wc n i

/-- Combination `Σ_{k<K} z_k f(k0+k)` of coefficient functions. -/
def combZ (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (f : ℤ → ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, z k * f (k0 + (k : ℤ)) i

/-- `Φ_{H+}(J,S)` of the profile `z`. -/
def PhiHp (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (J S : ℕ) : ℚ :=
  Q.PhiQ (combZ K k0 z aHp) (combZ K k0 z wc) J S

/-- `Φ_{H-}(J,S)` of the profile `z`. -/
def PhiHm (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (J S : ℕ) : ℚ :=
  Q.PhiQ (combZ K k0 z aHm) (combZ K k0 z vc) J S

/-- Small vectors from lists. -/
def vecI (l : List ℤ) : ℕ → ℤ := fun k => l.getD k 0

end CatalanMeasure.GenD.Uniform.W.HYPlus
