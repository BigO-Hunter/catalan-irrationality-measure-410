module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPrime
@[expose] public section
set_option Elab.async false

/-!
# The slot basis `g_t` of the H+ system

`f_t = U_{h-t-1} + U_{h+t} = (X-1)^h g_t` with `h = (p-1)/2`, where `g_t` has degree exactly `t`.
Hence every polynomial of degree `< D` (`D ≤ h`) is a combination `Σ_{t<D} s_t g_t`
(`exists_combination`): the slots of the H+ system span `(X-1)^{h+h_p} · F_p[X]_{<D}`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `g_t = (X+1)^h T_{h-t} - (X-1)^{h+1} U_{h-t-1}`. -/
def gBasis (p t : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (X + 1) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (hh p - t) -
    (X - 1) ^ ((p - 1) / 2 + 1) * Chebyshev.U (ZMod p) (hh p - t - 1)

theorem f_eq_gBasis (hp2 : p ≠ 2) (t : ℕ) :
    Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t) =
      (X - 1) ^ ((p - 1) / 2) * gBasis p t := by
  rw [hf_expand hp2]
  unfold gBasis
  have h1 : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) =
      (X - 1) ^ ((p - 1) / 2) * (X + 1) ^ ((p - 1) / 2) := by
    rw [← mul_pow]; congr 1; ring
  have h2 : ((X - 1 : (ZMod p)[X])) ^ p = (X - 1) ^ ((p - 1) / 2) * (X - 1) ^ ((p - 1) / 2 + 1) := by
    rw [← pow_add]; congr 1; have := p_odd_half hp2; omega
  rw [h1, h2]; ring

theorem natDegree_f (hp2 : p ≠ 2) (t : ℕ) (ht : t < (p - 1) / 2) :
    (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)).natDegree =
      (p - 1) / 2 + t := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have e1 : hh p - t - 1 = (((p - 1) / 2 - t - 1 : ℕ) : ℤ) := by unfold hh; omega
  have e2 : hh p + t = (((p - 1) / 2 + t : ℕ) : ℤ) := by unfold hh; omega
  rw [e1, e2]
  have d1 := Chebyshev.natDegree_U_natCast (R := ZMod p) ((p - 1) / 2 - t - 1)
  have d2 := Chebyshev.natDegree_U_natCast (R := ZMod p) ((p - 1) / 2 + t)
  rw [natDegree_add_eq_right_of_natDegree_lt (by omega)]
  exact d2

theorem gBasis_natDegree (hp2 : p ≠ 2) (t : ℕ) (ht : t < (p - 1) / 2) :
    gBasis p t ≠ 0 ∧ (gBasis p t).natDegree = t := by
  have hf := natDegree_f hp2 t ht
  have hfeq := f_eq_gBasis hp2 t
  have hhp : 0 < (p - 1) / 2 := by
    have := (Fact.out : p.Prime).two_le
    have := p_odd_half hp2
    omega
  have hf0 : (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) ≠ 0 := by
    intro h; rw [h] at hf; simp at hf; omega
  have hg0 : gBasis p t ≠ 0 := by
    intro h; rw [h, mul_zero] at hfeq; exact hf0 hfeq
  refine ⟨hg0, ?_⟩
  have hx1 : (X - 1 : (ZMod p)[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ZMod p)
  rw [hfeq, natDegree_mul (pow_ne_zero _ hx1) hg0] at hf
  have : ((X - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).natDegree = (p - 1) / 2 := by
    have h1 : (X - 1 : (ZMod p)[X]).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, h1, mul_one]
  omega

/-- Every polynomial of degree `< D` is a combination of `g_0, …, g_{D-1}`. -/
theorem exists_combination (hp2 : p ≠ 2) :
    ∀ (D : ℕ), D ≤ (p - 1) / 2 → ∀ σ : (ZMod p)[X], σ.degree < D →
      ∃ s : Fin D → ZMod p, σ = ∑ t : Fin D, C (s t) * gBasis p t := by
  intro D
  induction D with
  | zero =>
    intro _ σ hσ
    refine ⟨Fin.elim0, ?_⟩
    have hz : σ = 0 := by
      have h0 : σ.degree < ((0 : ℕ) : WithBot ℕ) := hσ
      rw [Polynomial.degree_lt_iff_coeff_zero] at h0
      ext m; simpa using h0 m (Nat.zero_le _)
    simp [hz]
  | succ D ih =>
    intro hD σ hσ
    by_cases hlt : σ.degree < D
    · obtain ⟨s, hs⟩ := ih (by omega) σ hlt
      refine ⟨Fin.snoc s 0, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp [hs]
    · have hσ0 : σ ≠ 0 := by
        intro h; rw [h] at hlt; simp at hlt
      have hnd : σ.natDegree = D := by
        have h1 : (D : WithBot ℕ) ≤ σ.degree := not_lt.mp hlt
        have h2 := (degree_eq_natDegree hσ0) ▸ h1
        have h3 := (degree_eq_natDegree hσ0) ▸ hσ
        have h4 : D ≤ σ.natDegree := by exact_mod_cast h2
        have h5 : σ.natDegree < D + 1 := by exact_mod_cast h3
        omega
      obtain ⟨hg0, hgd⟩ := gBasis_natDegree hp2 D (by omega)
      set c := σ.leadingCoeff / (gBasis p D).leadingCoeff with hc
      have hlc : (gBasis p D).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
      have hc0 : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hσ0) hlc
      have hq0 : C c * gBasis p D ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc0) hg0
      have hqd : (C c * gBasis p D).natDegree = D := by
        rw [natDegree_C_mul hc0, hgd]
      have hdeq : σ.degree = (C c * gBasis p D).degree := by
        rw [degree_eq_natDegree hσ0, degree_eq_natDegree hq0, hnd, hqd]
      have hlceq : σ.leadingCoeff = (C c * gBasis p D).leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_C, hc]
        field_simp
      have hlt2 := degree_sub_lt hdeq hσ0 hlceq
      rw [degree_eq_natDegree hσ0, hnd] at hlt2
      obtain ⟨s, hs⟩ := ih (by omega) (σ - C c * gBasis p D) (by
        have : (σ - C c * gBasis p D).degree < (D : WithBot ℕ) := by exact_mod_cast hlt2
        exact this)
      refine ⟨Fin.snoc s c, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
      rw [← hs]; ring

#print axioms exists_combination
end
end CatalanMeasure.GenD.Uniform.W.Slots
