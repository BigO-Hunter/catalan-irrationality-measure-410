module
public import Mathlib.LinearAlgebra.Matrix.Rank
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanCore.Uniform.Content
open Matrix
variable (K : Type*) [Field K]

/-- Integer certificates reduce in every characteristic; no impossible algebra
map Q→ZMod p is used. All source denominator exceptions remain explicit. -/
def castMatrix {m n : Nat} (A : Matrix (Fin m) (Fin n) Int) :
    Matrix (Fin m) (Fin n) K := fun i j => (A i j : K)

@[simp] theorem castMatrix_mul {m n r : Nat}
    (A : Matrix (Fin m) (Fin n) Int) (B : Matrix (Fin n) (Fin r) Int) :
    castMatrix K (A*B) = castMatrix K A*castMatrix K B := by
  ext i j
  simp [castMatrix, Matrix.mul_apply]

/-- A checked scaled left inverse proves the advertised basis rank over every
field in which its explicit nonzero scale survives. -/
theorem integral_basis_rank {m d : Nat} (V : Matrix (Fin m) (Fin d) Int)
    (L : Matrix (Fin d) (Fin m) Int) (scale : Int)
    (h : L*V = scale • (1 : Matrix (Fin d) (Fin d) Int))
    (hs : (scale : K) ≠ 0) : (castMatrix K V).rank = d := by
  have hc : castMatrix K L*castMatrix K V = (scale : K) • 1 := by
    rw [← castMatrix_mul, h]
    ext i j
    simp [castMatrix, Matrix.one_apply]
  have hl : ((scale : K)⁻¹ • castMatrix K L)*castMatrix K V = 1 := by
    rw [Matrix.smul_mul, hc, smul_smul, inv_mul_cancel₀ hs, one_smul]
  apply le_antisymm (Matrix.rank_le_width _)
  have hr := Matrix.rank_mul_le_right ((scale : K)⁻¹ • castMatrix K L) (castMatrix K V)
  rw [hl, Matrix.rank_one, Fintype.card_fin] at hr
  exact hr

/-- Exact integer image factorization implies a restriction-rank bound in any
surviving characteristic. Only the small certificate is checked in the kernel. -/
theorem integral_image_rank_le {m n d r : Nat}
    (B : Matrix (Fin m) (Fin n) Int) (V : Matrix (Fin n) (Fin d) Int)
    (C : Matrix (Fin m) (Fin r) Int) (T : Matrix (Fin r) (Fin d) Int)
    (h : B*V=C*T) : (castMatrix K B*castMatrix K V).rank ≤ r := by
  have hc : castMatrix K B*castMatrix K V=castMatrix K C*castMatrix K T := by
    rw [← castMatrix_mul, ← castMatrix_mul,h]
  rw [hc]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- Clearing a whole source map by one scalar is compatible with the same
factorization certificate; the source proves the displayed normalization. -/
theorem cleared_image_rank_le {m n d r : Nat}
    (B : Matrix (Fin m) (Fin n) Int) (V : Matrix (Fin n) (Fin d) Int)
    (C : Matrix (Fin m) (Fin r) Int) (T : Matrix (Fin r) (Fin d) Int)
    (A : Matrix (Fin m) (Fin n) K) (s : K) (hA : A=s • castMatrix K B)
    (h : B*V=C*T) : (A*castMatrix K V).rank ≤ r := by
  have hc : A*castMatrix K V=(s • castMatrix K C)*castMatrix K T := by
    rw [hA, Matrix.smul_mul, ← castMatrix_mul, h, castMatrix_mul, ← Matrix.smul_mul]
  rw [hc]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

#print axioms integral_basis_rank
#print axioms integral_image_rank_le
end CatalanCore.Uniform.Content