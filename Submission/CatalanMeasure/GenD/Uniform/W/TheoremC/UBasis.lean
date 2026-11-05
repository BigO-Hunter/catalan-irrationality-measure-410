module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TPoly
@[expose] public section
set_option Elab.async false

/-!
# The Chebyshev basis `U_0, …, U_{D-1}` of polynomials of degree `< D` over `F_p` (`p` odd)

`uComb p D w = Σ_d w_d U_d`; `uBasisEquiv p D : (Fin D → F_p) ≃ₗ degreeLT F_p D`.  Used to turn the
polynomial `σ` of a kernel family into its pair coordinates.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Polynomial Module CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `w ↦ Σ_d w_d U_d`. -/
def uComb (p D : ℕ) [Fact p.Prime] : (Fin D → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ d : Fin D, (LinearMap.proj d : (Fin D → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (Chebyshev.U (ZMod p) (d : ℤ))

theorem uComb_apply {D : ℕ} (w : Fin D → ZMod p) :
    uComb p D w = ∑ d : Fin D, C (w d) * Chebyshev.U (ZMod p) (d : ℤ) := by
  simp [uComb, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

theorem degree_term_lt (hp2 : p ≠ 2) (c : ZMod p) {d D : ℕ} (hd : d < D) :
    (C c * Chebyshev.U (ZMod p) (d : ℤ)).degree < D := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have h1 : (C c : (ZMod p)[X]).degree ≤ 0 := Polynomial.degree_C_le
  have h2 : (Chebyshev.U (ZMod p) (d : ℤ)).degree = d := by
    rw [Polynomial.degree_eq_natDegree]
    · have := Chebyshev.natDegree_U_natCast (R := ZMod p) d
      simpa using congrArg (fun n : ℕ => (n : WithBot ℕ)) this
    · intro h0
      have h3 := Chebyshev.leadingCoeff_U_natCast (R := ZMod p) d
      simp only [h0, Polynomial.leadingCoeff_zero] at h3
      exact absurd h3.symm (pow_ne_zero _ (NeZero.ne (2 : ZMod p)))
  calc (C c).degree + (Chebyshev.U (ZMod p) (d : ℤ)).degree
      ≤ 0 + (d : WithBot ℕ) := by rw [h2]; exact add_le_add_left h1 _
    _ = d := by simp
    _ < D := by exact_mod_cast hd

theorem degree_comb_lt (hp2 : p ≠ 2) (w : ℕ → ZMod p) (D : ℕ) :
    (∑ d ∈ Finset.range D, C (w d) * Chebyshev.U (ZMod p) (d : ℤ)).degree < D := by
  have : (∑ d ∈ Finset.range D, C (w d) * Chebyshev.U (ZMod p) (d : ℤ)) ∈
      degreeLT (ZMod p) D := by
    refine Submodule.sum_mem _ fun d hd => ?_
    exact Polynomial.mem_degreeLT.mpr (degree_term_lt hp2 _ (Finset.mem_range.mp hd))
  exact Polynomial.mem_degreeLT.mp this

theorem degree_uComb_lt (hp2 : p ≠ 2) {D : ℕ} (w : Fin D → ZMod p) :
    (uComb p D w).degree < D := by
  rw [uComb_apply]
  have : (∑ d : Fin D, C (w d) * Chebyshev.U (ZMod p) (d : ℤ)) ∈ degreeLT (ZMod p) D := by
    refine Submodule.sum_mem _ fun d _ => ?_
    exact Polynomial.mem_degreeLT.mpr (degree_term_lt hp2 _ d.isLt)
  exact Polynomial.mem_degreeLT.mp this

/-- Triangularity: a vanishing combination has vanishing coefficients (`ℕ`-indexed form). -/
theorem comb_eq_zero_aux (hp2 : p ≠ 2) (w : ℕ → ZMod p) :
    ∀ D : ℕ, ∑ d ∈ Finset.range D, C (w d) * Chebyshev.U (ZMod p) (d : ℤ) = 0 →
      ∀ d < D, w d = 0 := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  intro D
  induction D with
  | zero => intro _ d hd; omega
  | succ D ih =>
    intro h d hd
    rw [Finset.sum_range_succ] at h
    have hdeg := degree_comb_lt hp2 w D
    have hc := congrArg (fun f => f.coeff D) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero] at hc
    have hz : (∑ d ∈ Finset.range D, C (w d) * Chebyshev.U (ZMod p) (d : ℤ)).coeff D = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt hdeg
    rw [hz, zero_add] at hc
    have hU : (Chebyshev.U (ZMod p) (D : ℤ)).coeff D = 2 ^ D := by
      have := Chebyshev.leadingCoeff_U_natCast (R := ZMod p) D
      rw [Polynomial.leadingCoeff, Chebyshev.natDegree_U_natCast] at this
      simpa using this
    rw [Polynomial.coeff_C_mul, hU] at hc
    have hw : w D = 0 := by
      have h2 : (2 : ZMod p) ^ D ≠ 0 := pow_ne_zero _ (NeZero.ne 2)
      exact (mul_eq_zero.mp hc).resolve_right h2
    rw [hw] at h
    simp only [map_zero, zero_mul, add_zero] at h
    by_cases hdD : d = D
    · rw [hdD]; exact hw
    · exact ih h d (by omega)

theorem uComb_injective (hp2 : p ≠ 2) (D : ℕ) : Function.Injective (uComb p D) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  rw [uComb_apply] at hw
  funext d
  have h := comb_eq_zero_aux hp2 (fun n => if h : n < D then w ⟨n, h⟩ else 0) D (by
    rw [← hw, ← Fin.sum_univ_eq_sum_range (fun n => C (if h : n < D then w ⟨n, h⟩ else 0) *
      Chebyshev.U (ZMod p) (n : ℤ)) D]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [d.isLt]) d d.isLt
  simpa [d.isLt] using h

/-- `uComb` as a linear map into `degreeLT`. -/
def uCombLT (hp2 : p ≠ 2) (D : ℕ) : (Fin D → ZMod p) →ₗ[ZMod p] degreeLT (ZMod p) D :=
  LinearMap.codRestrict _ (uComb p D) fun w => Polynomial.mem_degreeLT.mpr (degree_uComb_lt hp2 w)

theorem uCombLT_injective (hp2 : p ≠ 2) (D : ℕ) : Function.Injective (uCombLT hp2 D) := by
  intro a b h
  apply uComb_injective hp2 D
  exact congrArg Subtype.val h

theorem uCombLT_surjective (hp2 : p ≠ 2) (D : ℕ) : Function.Surjective (uCombLT hp2 D) := by
  have hinj : Function.Injective
      (((degreeLTEquiv (ZMod p) D).toLinearMap).comp (uCombLT hp2 D)) :=
    (degreeLTEquiv (ZMod p) D).injective.comp (uCombLT_injective hp2 D)
  have hsurj := LinearMap.surjective_of_injective hinj
  intro s
  obtain ⟨w, hw⟩ := hsurj ((degreeLTEquiv (ZMod p) D) s)
  refine ⟨w, ?_⟩
  exact (degreeLTEquiv (ZMod p) D).injective hw

/-- The Chebyshev `U`-basis of `degreeLT F_p D`. -/
def uBasisEquiv (hp2 : p ≠ 2) (D : ℕ) : (Fin D → ZMod p) ≃ₗ[ZMod p] degreeLT (ZMod p) D :=
  LinearEquiv.ofBijective (uCombLT hp2 D) ⟨uCombLT_injective hp2 D, uCombLT_surjective hp2 D⟩

theorem uBasisEquiv_symm_comb (hp2 : p ≠ 2) (D : ℕ) (s : degreeLT (ZMod p) D) :
    uComb p D ((uBasisEquiv hp2 D).symm s) = (s : (ZMod p)[X]) := by
  have := (uBasisEquiv hp2 D).apply_symm_apply s
  exact congrArg Subtype.val this

#print axioms uBasisEquiv_symm_comb
end
end CatalanMeasure.GenD.Uniform.W.TheoremC
