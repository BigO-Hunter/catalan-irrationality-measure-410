module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZRowsT
@[expose] public section
set_option Elab.async false

/-!
# Injectivity of the combined rows on the consistent subspace

On `ZCons` data with `A_0 = 0`, `zRows S A = 0` forces `S = 0` and `A = 0`
(offsets `≤ (p-1)/2`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem aPairRow_eval (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ) (d2 : Fin D)
    (k2 k : Fin K) (r : Fin (P.n N)) (s : ℤ) (hs : s ≤ ((p - 1) / 2 : ℕ))
    (hs' : -((p - 1) / 2 : ℕ) ≤ s) (hr : (r : ℤ) - P.g N = cen p K k0 k + s) :
    aPairRow P N p k0 d2 k2 r =
      (if k2 = k ∧ s = ((d2 : ℕ) : ℤ) then (1 : ZMod p) else 0) -
        (if k2 = k ∧ s = -((d2 : ℕ) : ℤ) then (1 : ZMod p) else 0) := by
  have hd2 := d2.isLt
  have h1 : ((r : ℤ) - P.g N = cen p K k0 k2 + ((d2 : ℕ) : ℤ)) ↔
      (k2 = k ∧ s = ((d2 : ℕ) : ℤ)) := by
    rw [hr]; unfold cen
    constructor
    · intro h
      have := rep_unique hp2 ((k0 : ℤ) + (k : ℕ)) ((k0 : ℤ) + (k2 : ℕ)) s ((d2 : ℕ) : ℤ) hs hs'
        (by omega) (by omega) (by linarith)
      refine ⟨?_, this.2⟩
      have := this.1
      exact Fin.ext (by omega)
    · rintro ⟨rfl, rfl⟩; rfl
  have h2 : ((r : ℤ) - P.g N = cen p K k0 k2 - ((d2 : ℕ) : ℤ)) ↔
      (k2 = k ∧ s = -((d2 : ℕ) : ℤ)) := by
    rw [hr]; unfold cen
    constructor
    · intro h
      have := rep_unique hp2 ((k0 : ℤ) + (k : ℕ)) ((k0 : ℤ) + (k2 : ℕ)) s (-((d2 : ℕ) : ℤ)) hs hs'
        (by omega) (by omega) (by linarith)
      refine ⟨?_, this.2⟩
      have := this.1
      exact Fin.ext (by omega)
    · rintro ⟨rfl, rfl⟩; ring
  unfold aPairRow
  simp only [h1, h2]

theorem aRows_eval (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (k : Fin K) (r : Fin (P.n N)) (s : ℤ)
    (hs : s ≤ ((p - 1) / 2 : ℕ)) (hs' : -((p - 1) / 2 : ℕ) ≤ s)
    (hr : (r : ℤ) - P.g N = cen p K k0 k + s) :
    aRows P N p K D k0 x r =
      ∑ d2 : Fin D, ((if s = ((d2 : ℕ) : ℤ) then x d2 k else 0) -
        (if s = -((d2 : ℕ) : ℤ) then x d2 k else 0)) := by
  rw [aRows_apply]
  refine Finset.sum_congr rfl fun d2 _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [aPairRow_eval hp2 hD k0 d2 k k r s hs hs' hr]
    simp only [eq_self_iff_true, true_and]
    split_ifs <;> first | ring | simp
  · intro k2 _ hk2
    rw [aPairRow_eval hp2 hD k0 d2 k2 k r s hs hs' hr]
    simp [hk2]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Value of the combined row at `c_k + d`, `1 ≤ d ≤ hp`: `S + A`. -/
theorem zRows_plus (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (S A : Fin D → Fin K → ZMod p) (d : Fin D) (hd : 1 ≤ (d : ℕ)) (k : Fin K)
    (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = cen p K k0 k + (d : ℕ)) :
    zRows P N p K D k0 S A r = S d k + A d k := by
  have hdl := d.isLt
  have hs : ((d : ℕ) : ℤ) ≤ (((p - 1) / 2 : ℕ) : ℤ) := by omega
  unfold zRows
  rw [Pi.add_apply, tpRows_eval hp2 hD k0 S k r _ hs (by omega) hr,
    aRows_eval hp2 hD k0 A k r _ hs (by omega) hr]
  have hn1 : ¬ (((d : ℕ) : ℤ) = -((d : ℕ) : ℤ)) := by omega
  rw [Finset.sum_eq_single d, Finset.sum_eq_single d]
  · simp only [if_true, hn1, if_false]; ring
  all_goals first
    | (intro d2 _ hne
       have h3 : (d2 : ℕ) ≠ (d : ℕ) := fun h => hne (Fin.ext h)
       have h4 : ¬ (((d : ℕ) : ℤ) = ((d2 : ℕ) : ℤ)) := by omega
       have h5 : ¬ (((d : ℕ) : ℤ) = -((d2 : ℕ) : ℤ)) := by omega
       simp only [h4, h5, if_false]; ring)
    | (intro h; exact absurd (Finset.mem_univ _) h)

theorem zRows_minus (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (S A : Fin D → Fin K → ZMod p) (d : Fin D) (hd : 1 ≤ (d : ℕ)) (k : Fin K)
    (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = cen p K k0 k - (d : ℕ)) :
    zRows P N p K D k0 S A r = S d k - A d k := by
  have hdl := d.isLt
  have hs : -((d : ℕ) : ℤ) ≤ (((p - 1) / 2 : ℕ) : ℤ) := by omega
  have hs' : -(((p - 1) / 2 : ℕ) : ℤ) ≤ -((d : ℕ) : ℤ) := by omega
  have hr' : (r : ℤ) - P.g N = cen p K k0 k + (-((d : ℕ) : ℤ)) := by rw [hr]; ring
  unfold zRows
  rw [Pi.add_apply, tpRows_eval hp2 hD k0 S k r _ hs hs' hr',
    aRows_eval hp2 hD k0 A k r _ hs hs' hr']
  have hn1 : ¬ (-((d : ℕ) : ℤ) = ((d : ℕ) : ℤ)) := by omega
  rw [Finset.sum_eq_single d, Finset.sum_eq_single d]
  · simp only [if_true, hn1, if_false]; ring
  all_goals first
    | (intro d2 _ hne
       have h3 : (d2 : ℕ) ≠ (d : ℕ) := fun h => hne (Fin.ext h)
       have h4 : ¬ (-((d : ℕ) : ℤ) = ((d2 : ℕ) : ℤ)) := by omega
       have h5 : ¬ (-((d : ℕ) : ℤ) = -((d2 : ℕ) : ℤ)) := by omega
       simp only [h4, h5, if_false]; ring)
    | (intro h; exact absurd (Finset.mem_univ _) h)

theorem zRows_zero (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (S A : Fin D → Fin K → ZMod p) (d : Fin D) (hd : (d : ℕ) = 0) (hA : ∀ k, A d k = 0) (k : Fin K)
    (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = cen p K k0 k) :
    zRows P N p K D k0 S A r = 2 * S d k := by
  have hdl := d.isLt
  have hr' : (r : ℤ) - P.g N = cen p K k0 k + 0 := by rw [hr]; ring
  unfold zRows
  rw [Pi.add_apply, tpRows_eval hp2 hD k0 S k r 0 (by omega) (by omega) hr',
    aRows_eval hp2 hD k0 A k r 0 (by omega) (by omega) hr']
  have hd0 : ((d : ℕ) : ℤ) = 0 := by exact_mod_cast hd
  rw [Finset.sum_eq_single d, Finset.sum_eq_single d]
  · have e1 : (0 : ℤ) = ((d : ℕ) : ℤ) := hd0.symm
    have e2 : ((d : ℕ) : ℤ) = -((d : ℕ) : ℤ) := by omega
    simp only [e1, if_true, hA k]
    rw [if_pos e2, if_pos e2]
    ring
  all_goals first
    | (intro d2 _ hne
       have h3 : (d2 : ℕ) ≠ (d : ℕ) := fun h => hne (Fin.ext h)
       have h4 : ¬ ((0 : ℤ) = ((d2 : ℕ) : ℤ)) := by omega
       have h5 : ¬ ((0 : ℤ) = -((d2 : ℕ) : ℤ)) := by omega
       simp only [h4, h5, if_false]; ring)
    | (intro h; exact absurd (Finset.mem_univ _) h)

/-- **Injectivity** of the combined rows on consistent data with `A_0 = 0`. -/
theorem zRows_injective (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (S A : Fin D → Fin K → ZMod p) (hc : ZCons P N p k0 S A)
    (hA0 : ∀ d : Fin D, (d : ℕ) = 0 → ∀ k, A d k = 0)
    (h0 : zRows P N p K D k0 S A = 0) : S = 0 ∧ A = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have fin2 : ∀ d k, S d k + A d k = 0 → S d k - A d k = 0 → S d k = 0 ∧ A d k = 0 := by
    intro d k a1 a2
    have hS : (2 : ZMod p) * S d k = 0 := by linear_combination a1 + a2
    have hB : (2 : ZMod p) * A d k = 0 := by linear_combination a1 - a2
    exact ⟨(mul_eq_zero.mp hS).resolve_left h2ne, (mul_eq_zero.mp hB).resolve_left h2ne⟩
  have key : ∀ d k, S d k = 0 ∧ A d k = 0 := by
    intro d k
    have hdl := d.isLt
    by_cases hd : (d : ℕ) = 0
    · have hA := hA0 d hd k
      refine ⟨?_, hA⟩
      by_cases hin : InRange P N (cen p K k0 k + (d : ℕ))
      · obtain ⟨h1, h3⟩ := hin
        have hr : (cen p K k0 k + P.g N).toNat < P.n N := by
          have : ((d : ℕ) : ℤ) = 0 := by exact_mod_cast hd
          omega
        have hx := zRows_zero (P := P) (N := N) hp2 hD k0 S A d hd (hA0 d hd) k ⟨_, hr⟩
          (by simp only; omega)
        rw [h0] at hx
        have h4 : (2 : ZMod p) * S d k = 0 := hx.symm
        exact (mul_eq_zero.mp h4).resolve_left h2ne
      · have h5 := (hc d k).1 hin
        rw [hA] at h5
        simpa using h5
    · have hd1 : 1 ≤ (d : ℕ) := by omega
      by_cases hp : InRange P N (cen p K k0 k + (d : ℕ)) <;>
        by_cases hm : InRange P N (cen p K k0 k - (d : ℕ))
      · obtain ⟨hp1, hp3⟩ := hp
        obtain ⟨hm1, hm3⟩ := hm
        have hrp : (cen p K k0 k + (d : ℕ) + P.g N).toNat < P.n N := by omega
        have hrm : (cen p K k0 k - (d : ℕ) + P.g N).toNat < P.n N := by omega
        have e1 := zRows_plus (P := P) (N := N) hp2 hD k0 S A d hd1 k ⟨_, hrp⟩
          (by simp only; omega)
        have e2 := zRows_minus (P := P) (N := N) hp2 hD k0 S A d hd1 k ⟨_, hrm⟩
          (by simp only; omega)
        rw [h0] at e1 e2
        exact fin2 d k e1.symm e2.symm
      · have a2 := (hc d k).2 hm
        obtain ⟨hp1, hp3⟩ := hp
        have hrp : (cen p K k0 k + (d : ℕ) + P.g N).toNat < P.n N := by omega
        have e1 := zRows_plus (P := P) (N := N) hp2 hD k0 S A d hd1 k ⟨_, hrp⟩
          (by simp only; omega)
        rw [h0] at e1
        exact fin2 d k e1.symm a2
      · have a1 := (hc d k).1 hp
        obtain ⟨hm1, hm3⟩ := hm
        have hrm : (cen p K k0 k - (d : ℕ) + P.g N).toNat < P.n N := by omega
        have e2 := zRows_minus (P := P) (N := N) hp2 hD k0 S A d hd1 k ⟨_, hrm⟩
          (by simp only; omega)
        rw [h0] at e2
        exact fin2 d k a1 e2.symm
      · exact fin2 d k ((hc d k).1 hp) ((hc d k).2 hm)
  exact ⟨funext fun d => funext fun k => (key d k).1, funext fun d => funext fun k => (key d k).2⟩

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
