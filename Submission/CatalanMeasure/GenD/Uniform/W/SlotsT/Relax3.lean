module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax2
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.AddCount
@[expose] public section
set_option Elab.async false

/-!
# Independence of T- and T+ pairs on the relaxed domain
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- At an actual row `c + e`, `e = d + 1`, the combined coefficient vanishes. -/
theorem row_plus (hp2 : p ≠ 2) {K D1 : ℕ} (hD : D1 ≤ (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (h : ∀ r, tRows P N p K D1 k0 a r + tpRows P N p K (D1 + 1) k0 b r = 0)
    (d : Fin D1) (k : Fin K) (hg : InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1))) :
    a d k + b d.succ k = 0 := by
  have hD' : D1 + 1 ≤ (p - 1) / 2 + 1 := by omega
  have hdl := d.isLt
  have hdd : ((d.succ : Fin (D1 + 1)) : ℕ) = (d : ℕ) + 1 := Fin.val_succ d
  obtain ⟨h1, h2⟩ := hg
  have hrp : (cen p K k0 k + (((d : ℕ) : ℤ) + 1) + P.g N).toNat < P.n N := by omega
  have e1 := h ⟨_, hrp⟩
  rw [tRows_eval hp2 hD k0 a k ⟨_, hrp⟩ (((d : ℕ) : ℤ) + 1) (by omega) (by omega)
    (by simp only; omega),
    tpRows_eval hp2 hD' k0 b k ⟨_, hrp⟩ (((d : ℕ) : ℤ) + 1) (by omega) (by omega)
    (by simp only; omega)] at e1
  have sA1 : ∑ d2 : Fin D1, ((if ((d : ℕ) : ℤ) + 1 = ((d2 : ℕ) : ℤ) + 1 then a d2 k else 0) -
      (if ((d : ℕ) : ℤ) + 1 = -(((d2 : ℕ) : ℤ) + 1) then a d2 k else 0)) = a d k := by
    rw [Finset.sum_eq_single d]
    · rw [if_pos rfl, if_neg (by omega)]; simp
    · intro d2 _ hd2
      have : (d2 : ℕ) ≠ (d : ℕ) := fun hh => hd2 (Fin.ext hh)
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have sB1 : ∑ d2 : Fin (D1 + 1), ((if ((d : ℕ) : ℤ) + 1 = ((d2 : ℕ) : ℤ) then b d2 k else 0) +
      (if ((d : ℕ) : ℤ) + 1 = -((d2 : ℕ) : ℤ) then b d2 k else 0)) = b d.succ k := by
    rw [Finset.sum_eq_single d.succ]
    · rw [if_pos (by omega), if_neg (by omega)]; simp
    · intro d2 _ hd2
      have : (d2 : ℕ) ≠ ((d.succ : Fin (D1 + 1)) : ℕ) := fun hh => hd2 (Fin.ext hh)
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [sA1, sB1] at e1
  exact e1

/-- At an actual row `c - e`, `e = d + 1`: `b - a = 0`. -/
theorem row_minus (hp2 : p ≠ 2) {K D1 : ℕ} (hD : D1 ≤ (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (h : ∀ r, tRows P N p K D1 k0 a r + tpRows P N p K (D1 + 1) k0 b r = 0)
    (d : Fin D1) (k : Fin K) (hg : InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1))) :
    b d.succ k - a d k = 0 := by
  have hD' : D1 + 1 ≤ (p - 1) / 2 + 1 := by omega
  have hdl := d.isLt
  have hdd : ((d.succ : Fin (D1 + 1)) : ℕ) = (d : ℕ) + 1 := Fin.val_succ d
  obtain ⟨h1, h2⟩ := hg
  have hrm : (cen p K k0 k - (((d : ℕ) : ℤ) + 1) + P.g N).toNat < P.n N := by omega
  have e2 := h ⟨_, hrm⟩
  rw [tRows_eval hp2 hD k0 a k ⟨_, hrm⟩ (-(((d : ℕ) : ℤ) + 1)) (by omega) (by omega)
    (by simp only; omega),
    tpRows_eval hp2 hD' k0 b k ⟨_, hrm⟩ (-(((d : ℕ) : ℤ) + 1)) (by omega) (by omega)
    (by simp only; omega)] at e2
  have sA2 : ∑ d2 : Fin D1, ((if -(((d : ℕ) : ℤ) + 1) = ((d2 : ℕ) : ℤ) + 1 then a d2 k else 0) -
      (if -(((d : ℕ) : ℤ) + 1) = -(((d2 : ℕ) : ℤ) + 1) then a d2 k else 0)) = - a d k := by
    rw [Finset.sum_eq_single d]
    · rw [if_neg (by omega), if_pos rfl]; simp
    · intro d2 _ hd2
      have : (d2 : ℕ) ≠ (d : ℕ) := fun hh => hd2 (Fin.ext hh)
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have sB2 : ∑ d2 : Fin (D1 + 1), ((if -(((d : ℕ) : ℤ) + 1) = ((d2 : ℕ) : ℤ) then b d2 k else 0) +
      (if -(((d : ℕ) : ℤ) + 1) = -((d2 : ℕ) : ℤ) then b d2 k else 0)) = b d.succ k := by
    rw [Finset.sum_eq_single d.succ]
    · rw [if_neg (by omega), if_pos (by omega)]; simp
    · intro d2 _ hd2
      have : (d2 : ℕ) ≠ ((d.succ : Fin (D1 + 1)) : ℕ) := fun hh => hd2 (Fin.ext hh)
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [sA2, sB2] at e2
  linear_combination e2

/-- At an actual centre row the coefficient `2 b₀` vanishes. -/
theorem row_zero (hp2 : p ≠ 2) {K D1 : ℕ} (hD : D1 ≤ (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (h : ∀ r, tRows P N p K D1 k0 a r + tpRows P N p K (D1 + 1) k0 b r = 0)
    (k : Fin K) (hg : InRange P N (cen p K k0 k)) : (2 : ZMod p) * b 0 k = 0 := by
  have hD' : D1 + 1 ≤ (p - 1) / 2 + 1 := by omega
  obtain ⟨h1, h2⟩ := hg
  have hrc : (cen p K k0 k + P.g N).toNat < P.n N := by omega
  have e1 := h ⟨_, hrc⟩
  rw [tRows_eval hp2 hD k0 a k ⟨_, hrc⟩ 0 (by omega) (by omega) (by simp only; omega),
    tpRows_eval hp2 hD' k0 b k ⟨_, hrc⟩ 0 (by omega) (by omega) (by simp only; omega)] at e1
  have sA : ∑ d2 : Fin D1, ((if (0 : ℤ) = ((d2 : ℕ) : ℤ) + 1 then a d2 k else 0) -
      (if (0 : ℤ) = -(((d2 : ℕ) : ℤ) + 1) then a d2 k else 0)) = 0 := by
    refine Finset.sum_eq_zero fun d2 _ => ?_
    rw [if_neg (by omega), if_neg (by omega)]; simp
  have sB : ∑ d2 : Fin (D1 + 1), ((if (0 : ℤ) = ((d2 : ℕ) : ℤ) then b d2 k else 0) +
      (if (0 : ℤ) = -((d2 : ℕ) : ℤ) then b d2 k else 0)) = 2 * b 0 k := by
    rw [Finset.sum_eq_single 0]
    · rw [if_pos (by simp), if_pos (by simp)]; ring
    · intro d2 _ hd2
      have : (d2 : ℕ) ≠ ((0 : Fin (D1 + 1)) : ℕ) := fun hh => hd2 (Fin.ext hh)
      have h0 : ((0 : Fin (D1 + 1)) : ℕ) = 0 := rfl
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [sA, sB, zero_add] at e1
  exact e1

/-- **Independence on the relaxed domain.** -/
theorem mix_sep_relax (hp2 : p ≠ 2) {K D1 : ℕ} (hD : D1 ≤ (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (hr : RelaxOK P N p k0 a b)
    (h : ∀ r, tRows P N p K D1 k0 a r + tpRows P N p K (D1 + 1) k0 b r = 0) :
    a = 0 ∧ b = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  obtain ⟨hr1, hr2, hr3⟩ := hr
  have hab : ∀ (d : Fin D1) (k : Fin K), a d k = 0 ∧ b d.succ k = 0 := by
    intro d k
    have hpl : a d k + b d.succ k = 0 := by
      by_cases hg : InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1))
      · exact row_plus hp2 hD k0 a b h d k hg
      · exact hr1 d k hg
    have hmi : b d.succ k - a d k = 0 := by
      by_cases hg : InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1))
      · exact row_minus hp2 hD k0 a b h d k hg
      · exact hr2 d k hg
    have e3 : (2 : ZMod p) * a d k = 0 := by linear_combination hpl - hmi
    have e4 : (2 : ZMod p) * b d.succ k = 0 := by linear_combination hpl + hmi
    exact ⟨(mul_eq_zero.mp e3).resolve_left h2ne, (mul_eq_zero.mp e4).resolve_left h2ne⟩
  have hb0 : ∀ k : Fin K, b 0 k = 0 := by
    intro k
    by_cases hg : InRange P N (cen p K k0 k)
    · exact (mul_eq_zero.mp (row_zero hp2 hD k0 a b h k hg)).resolve_left h2ne
    · exact hr3 k hg
  refine ⟨?_, ?_⟩
  · funext d k; exact (hab d k).1
  · funext i k
    refine Fin.cases ?_ (fun d => ?_) i
    · exact hb0 k
    · exact (hab d k).2

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
