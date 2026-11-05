module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HmRows
@[expose] public section
set_option Elab.async false

/-!
# H- pair identities and the slot polynomial `hmLam`
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The slot polynomial `(X-1)^h (U_{hh-t-1} - U_{hh+t})`. -/
def hmLam (P : Parameters) (N p : ℕ) [Fact p.Prime] (t : ℕ) : (ZMod p)[X] :=
  (X - 1) ^ P.h N * (Chebyshev.U (ZMod p) (hh p - t - 1) - Chebyshev.U (ZMod p) (hh p + t))

theorem hmU_pair (hp2 : p ≠ 2) (κ t : ℤ) :
    Chebyshev.U (ZMod p) (κ * p + hh p - t - 1) -
        Chebyshev.U (ZMod p) (κ * p + hh p + 1 + t - 1) =
      ((Chebyshev.U (ZMod p) κ).comp (X ^ p) - (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) - Chebyshev.U (ZMod p) (hh p + t)) := by
  have hpe := p_eq_hh hp2
  have h1 := physical_pair_U_minus (ZMod p) κ p (hh p - t)
  have h2 := chebyshev_U_reflect (ZMod p) (p : ℤ) (hh p - t)
  have e0 : κ * (p : ℤ) + (hh p - t) = κ * p + hh p - t := by ring
  rw [chebyshev_T_prime hp2] at h1 h2
  have e1 : (κ + 1) * (p : ℤ) - (hh p - t) - 1 = κ * p + hh p + 1 + t - 1 := by
    rw [hpe]; ring
  have e2 : (p : ℤ) - (hh p - t) - 1 = hh p + t := by rw [hpe]; ring
  rw [e1, e0] at h1
  rw [e2] at h2
  rw [h1]
  have h3 : Chebyshev.U (ZMod p) ((hh p - t) - 1) - Chebyshev.U (ZMod p) (hh p + t) =
      (1 + (X : (ZMod p)[X]) ^ p) * Chebyshev.U (ZMod p) (hh p - t - 1) -
        Chebyshev.U (ZMod p) ((p : ℤ) - 1) * Chebyshev.T (ZMod p) (hh p - t) := by
    rw [h2]; ring
  rw [← h3]

theorem hmT_pair (hp2 : p ≠ 2) (κ t : ℤ) :
    (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + hh p - t) -
          Chebyshev.T (ZMod p) (κ * p + hh p + 1 + t)) =
      (X ^ p - 1) * ((Chebyshev.U (ZMod p) κ).comp (X ^ p) +
          (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) - Chebyshev.U (ZMod p) (hh p + t)) := by
  have hpe := p_eq_hh hp2
  have h1 := physical_pair_T_minus (ZMod p) κ p (hh p - t)
  have h2 := chebyshev_U_reflect (ZMod p) (p : ℤ) (hh p - t)
  have e0 : κ * (p : ℤ) + (hh p - t) = κ * p + hh p - t := by ring
  rw [chebyshev_T_prime hp2] at h1 h2
  have e1 : (κ + 1) * (p : ℤ) - (hh p - t) = κ * p + hh p + 1 + t := by
    rw [hpe]; ring
  have e2 : (p : ℤ) - (hh p - t) - 1 = hh p + t := by rw [hpe]; ring
  rw [e1, e0, chebyshev_U_prime hp2] at h1
  rw [chebyshev_U_prime hp2] at h2
  rw [e2] at h2
  rw [h1]
  have h3 : Chebyshev.U (ZMod p) ((hh p - t) - 1) - Chebyshev.U (ZMod p) (hh p + t) =
      (1 + (X : (ZMod p)[X]) ^ p) * Chebyshev.U (ZMod p) (hh p - t - 1) -
        (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (hh p - t) := by
    rw [h2]; ring
  rw [h3]

theorem hmLam_natDegree_lt (hp2 : p ≠ 2) {D : ℕ} (hD : D ≤ (p - 1) / 2) (t : Fin D) :
    (hmLam P N p t).natDegree < P.h N + (p - 1) / 2 + D := by
  have ht := t.isLt
  unfold hmLam
  have e1 : hh p - (t : ℕ) - 1 = (((p - 1) / 2 - t - 1 : ℕ) : ℤ) := by unfold hh; omega
  have e2 : hh p + (t : ℕ) = (((p - 1) / 2 + t : ℕ) : ℤ) := by unfold hh; omega
  rw [e1, e2]
  have a : ((X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  have b : (Chebyshev.U (ZMod p) (((p - 1) / 2 - t - 1 : ℕ) : ℤ) -
      Chebyshev.U (ZMod p) (((p - 1) / 2 + t : ℕ) : ℤ)).natDegree ≤ (p - 1) / 2 + t := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (U_natDegree_le hp2 _).trans (by omega)
    · exact U_natDegree_le hp2 _
  have c := natDegree_mul_le (p := ((X - 1) ^ P.h N : (ZMod p)[X]))
    (q := Chebyshev.U (ZMod p) (((p - 1) / 2 - t - 1 : ℕ) : ℤ) -
      Chebyshev.U (ZMod p) (((p - 1) / 2 + t : ℕ) : ℤ))
  omega

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
