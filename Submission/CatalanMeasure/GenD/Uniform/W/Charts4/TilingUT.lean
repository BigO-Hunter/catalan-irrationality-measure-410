module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.TilingPoly
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.ChebyshevComposition
@[expose] public section
set_option Elab.async false

/-!
# The enlarged physical tiling: `U` and `T` identities (design-free)

`tiling_U`, `tiling_T`: for any tiling coordinates `t` and block offset `k0 : ℤ`, the Chebyshev
combination of the enlarged rows `Σ_i rows_i U_{k0 p + i - 1}` (resp. `w Σ_i rows_i T_{k0 p + i}`)
equals `Σ_k (P_κ QA_k + M_κ QC_k) + U_{k0-1}(Y) u_0 w` (resp. with `GA_κ, GC_κ, T_{k0}(Y)`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Polynomial Polynomial.Chebyshev Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem nativePlus_zero (hp2 : p ≠ 2) : nativePlus (p := p) 0 = nativeCenter (p := p) := by
  rw [nativePlus_formula hp2]; simp

theorem cast_pair1 (b k : ℕ) (k0 : ℤ) (j : ℕ) :
    k0 * (p : ℤ) + ((k * p + (j + 1) : ℕ) : ℤ) - 1 = (k0 + k) * p + ((j : ℤ) + 1) - 1 := by
  push_cast; ring

theorem cast_pair2 {j : ℕ} (hj : j + 1 ≤ p) (k : ℕ) (k0 : ℤ) :
    k0 * (p : ℤ) + ((k * p + (p - (j + 1)) : ℕ) : ℤ) - 1 = (k0 + k + 1) * p - ((j : ℤ) + 1) - 1 := by
  rw [Nat.cast_add, Nat.cast_sub hj]; push_cast; ring

theorem tiling_U (hp2 : p ≠ 2) (b : ℕ) (k0 : ℤ)
    (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) :
    ∑ i : Fin (b * p + 1), C (physicalTilingEquiv b ((p - 1) / 2) p (native_half_identity hp2)
        (native_two_ne_zero hp2) t i) * U (ZMod p) (k0 * p + ((i : ℕ) : ℤ) - 1) =
      ∑ k : Fin b, (blkP p (k0 + k) * QA t k + blkM p (k0 + k) * QC t k) +
        (U (ZMod p) (k0 - 1)).comp (X ^ p) * (t.2 0 • nativeCenter (p := p)) := by
  have hpe := native_half_identity hp2
  refine tiling_poly hp2 b t (fun n => U (ZMod p) (k0 * p + (n : ℤ) - 1))
    (fun k => blkP p (k0 + k)) (fun k => blkM p (k0 + k)) ((U (ZMod p) (k0 - 1)).comp (X ^ p))
    ?_ ?_ ?_ ?_
  · intro k j
    have hj : (j : ℕ) + 1 ≤ p := by have := j.isLt; omega
    beta_reduce
    rw [cast_pair1 b k k0 j, cast_pair2 hj k k0]
    exact pairU_plus hp2 (k0 + k) ((j : ℤ) + 1)
  · intro k j
    have hj : (j : ℕ) + 1 ≤ p := by have := j.isLt; omega
    beta_reduce
    rw [cast_pair1 b k k0 j, cast_pair2 hj k k0]
    exact pairU_minus hp2 (k0 + k) ((j : ℤ) + 1)
  · intro k
    have h := pairU_plus hp2 (k0 + k) 0
    rw [nativePlus_zero hp2] at h
    beta_reduce
    have e1 : k0 * (p : ℤ) + (((k : ℕ) * p : ℕ) : ℤ) - 1 = (k0 + k) * p + 0 - 1 := by push_cast; ring
    have e2 : k0 * (p : ℤ) + ((((k : ℕ) + 1) * p : ℕ) : ℤ) - 1 = (k0 + k + 1) * p - 0 - 1 := by
      push_cast; ring
    rw [e1, e2]; exact h
  · have h := chebyshev_U_block (ZMod p) k0 p 0
    rw [CatalanMeasure.Parametric.chebyshev_T_prime hp2,
      CatalanMeasure.Parametric.chebyshev_U_prime hp2] at h
    simp only [Nat.cast_zero, add_zero]
    rw [show k0 * (p : ℤ) + 0 - 1 = k0 * p + 0 - 1 from rfl] at *
    simp only [add_zero] at h
    rw [h]
    simp [nativeCenter]

theorem tiling_T (hp2 : p ≠ 2) (b : ℕ) (k0 : ℤ)
    (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) :
    ∑ i : Fin (b * p + 1), C (physicalTilingEquiv b ((p - 1) / 2) p (native_half_identity hp2)
        (native_two_ne_zero hp2) t i) * (nativeCenter (p := p) * T (ZMod p) (k0 * p + ((i : ℕ) : ℤ))) =
      ∑ k : Fin b, (blkGA p (k0 + k) * QA t k + blkGC p (k0 + k) * QC t k) +
        (T (ZMod p) k0).comp (X ^ p) * (t.2 0 • nativeCenter (p := p)) := by
  have hpe := native_half_identity hp2
  refine tiling_poly hp2 b t (fun n => nativeCenter (p := p) * T (ZMod p) (k0 * p + (n : ℤ)))
    (fun k => blkGA p (k0 + k)) (fun k => blkGC p (k0 + k)) ((T (ZMod p) k0).comp (X ^ p))
    ?_ ?_ ?_ ?_
  · intro k j
    have hj : (j : ℕ) + 1 ≤ p := by have := j.isLt; omega
    beta_reduce
    rw [← mul_add]
    have e1 : k0 * (p : ℤ) + ((k * p + (j + 1) : ℕ) : ℤ) = (k0 + k) * p + ((j : ℤ) + 1) := by
      push_cast; ring
    have e2 : k0 * (p : ℤ) + ((k * p + (p - (j + 1)) : ℕ) : ℤ) = (k0 + k + 1) * p - ((j : ℤ) + 1) := by
      rw [Nat.cast_add, Nat.cast_sub hj]; push_cast; ring
    rw [e1, e2]
    exact pairT_plus hp2 (k0 + k) ((j : ℤ) + 1)
  · intro k j
    have hj : (j : ℕ) + 1 ≤ p := by have := j.isLt; omega
    beta_reduce
    rw [← mul_sub]
    have e1 : k0 * (p : ℤ) + ((k * p + (j + 1) : ℕ) : ℤ) = (k0 + k) * p + ((j : ℤ) + 1) := by
      push_cast; ring
    have e2 : k0 * (p : ℤ) + ((k * p + (p - (j + 1)) : ℕ) : ℤ) = (k0 + k + 1) * p - ((j : ℤ) + 1) := by
      rw [Nat.cast_add, Nat.cast_sub hj]; push_cast; ring
    rw [e1, e2]
    exact pairT_minus hp2 (k0 + k) ((j : ℤ) + 1)
  · intro k
    have h := pairT_plus hp2 (k0 + k) 0
    rw [nativePlus_zero hp2] at h
    beta_reduce
    rw [← mul_add]
    have e1 : k0 * (p : ℤ) + (((k : ℕ) * p : ℕ) : ℤ) = (k0 + k) * p + 0 := by push_cast; ring
    have e2 : k0 * (p : ℤ) + ((((k : ℕ) + 1) * p : ℕ) : ℤ) = (k0 + k + 1) * p - 0 := by
      push_cast; ring
    rw [e1, e2]; exact h
  · simp only [Nat.cast_zero, add_zero]
    rw [T_mul, CatalanMeasure.Parametric.chebyshev_T_prime hp2]
    ring

end
end CatalanMeasure.GenD.Uniform.W.Charts4
