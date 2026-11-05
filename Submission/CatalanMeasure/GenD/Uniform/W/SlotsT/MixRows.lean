module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.TpSystem
@[expose] public section
set_option Elab.async false

/-!
# T- and T+ pairs about the same centres are independent

For pairs `e_{c+e} ∓ e_{c-e}` about the centres `c_k = (k0 + k) p`, with `1 ≤ e ≤ (p-1)/2`
(T-: `e = d + 1`; T+: `e = d`, plus the single row `e = 0`), the evaluation of the row vector at
`c_k + s`, `|s| ≤ (p-1)/2`, is read off coordinatewise (`tRows_eval`, `tpRows_eval`).  Hence
`tRows a + tpRows b = 0` forces `a = 0` and `b = 0` (`mix_sep`).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem rep_unique (hp2 : p ≠ 2) (k k2 s s2 : ℤ) (hs : s ≤ ((p - 1) / 2 : ℕ)) (hs' : -((p - 1) / 2 : ℕ) ≤ s)
    (hs2 : s2 ≤ ((p - 1) / 2 : ℕ)) (hs2' : -((p - 1) / 2 : ℕ) ≤ s2)
    (h : k * p + s = k2 * p + s2) : k = k2 ∧ s = s2 := by
  have hpo := p_odd_half hp2
  have hp1 : (0 : ℤ) < p := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  have h5 : (k - k2) * p = s2 - s := by linarith
  have h6 := no_mult (k - k2) (s2 - s) hp1 (by omega) (by omega) h5
  omega

/-- General evaluation of a T- pair row. -/
theorem tPairRow_eval (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (k0 : ℤ) (d2 : Fin D)
    (k2 k : Fin K) (r : Fin (P.n N)) (s : ℤ) (hs : s ≤ ((p - 1) / 2 : ℕ))
    (hs' : -((p - 1) / 2 : ℕ) ≤ s) (hr : (r : ℤ) - P.g N = cen p K k0 k + s) :
    pairRow P N p k0 d2 k2 r =
      (if k2 = k ∧ s = ((d2 : ℕ) : ℤ) + 1 then (1 : ZMod p) else 0) -
        (if k2 = k ∧ s = -(((d2 : ℕ) : ℤ) + 1) then (1 : ZMod p) else 0) := by
  have hd2 := d2.isLt
  have h1 : ((r : ℤ) - P.g N = cen p K k0 k2 + (((d2 : ℕ) : ℤ) + 1)) ↔
      (k2 = k ∧ s = ((d2 : ℕ) : ℤ) + 1) := by
    rw [hr]; unfold cen
    constructor
    · intro h
      have := rep_unique hp2 ((k0 : ℤ) + (k : ℕ)) ((k0 : ℤ) + (k2 : ℕ)) s (((d2 : ℕ) : ℤ) + 1) hs hs'
        (by omega) (by omega) (by linarith)
      refine ⟨?_, this.2⟩
      have := this.1
      exact Fin.ext (by omega)
    · rintro ⟨rfl, rfl⟩; rfl
  have h2 : ((r : ℤ) - P.g N = cen p K k0 k2 - (((d2 : ℕ) : ℤ) + 1)) ↔
      (k2 = k ∧ s = -(((d2 : ℕ) : ℤ) + 1)) := by
    rw [hr]; unfold cen
    constructor
    · intro h
      have := rep_unique hp2 ((k0 : ℤ) + (k : ℕ)) ((k0 : ℤ) + (k2 : ℕ)) s (-(((d2 : ℕ) : ℤ) + 1)) hs hs'
        (by omega) (by omega) (by linarith)
      refine ⟨?_, this.2⟩
      have := this.1
      exact Fin.ext (by omega)
    · rintro ⟨rfl, rfl⟩; ring
  unfold pairRow
  simp only [h1, h2]

/-- General evaluation of a T+ pair row. -/
theorem tpPairRow_eval (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ) (d2 : Fin D)
    (k2 k : Fin K) (r : Fin (P.n N)) (s : ℤ) (hs : s ≤ ((p - 1) / 2 : ℕ))
    (hs' : -((p - 1) / 2 : ℕ) ≤ s) (hr : (r : ℤ) - P.g N = cen p K k0 k + s) :
    tpPairRow P N p k0 d2 k2 r =
      (if k2 = k ∧ s = ((d2 : ℕ) : ℤ) then (1 : ZMod p) else 0) +
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
  unfold tpPairRow
  simp only [h1, h2]

/-- T- rows at `c_k + s`. -/
theorem tRows_eval (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (k : Fin K) (r : Fin (P.n N)) (s : ℤ)
    (hs : s ≤ ((p - 1) / 2 : ℕ)) (hs' : -((p - 1) / 2 : ℕ) ≤ s)
    (hr : (r : ℤ) - P.g N = cen p K k0 k + s) :
    tRows P N p K D k0 x r =
      ∑ d2 : Fin D, ((if s = ((d2 : ℕ) : ℤ) + 1 then x d2 k else 0) -
        (if s = -(((d2 : ℕ) : ℤ) + 1) then x d2 k else 0)) := by
  rw [tRows_apply]
  refine Finset.sum_congr rfl fun d2 _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [tPairRow_eval hp2 hD k0 d2 k k r s hs hs' hr]
    simp only [eq_self_iff_true, true_and]
    split_ifs <;> simp
  · intro k2 _ hk2
    rw [tPairRow_eval hp2 hD k0 d2 k2 k r s hs hs' hr]
    simp [hk2]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- T+ rows at `c_k + s`. -/
theorem tpRows_eval (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (k : Fin K) (r : Fin (P.n N)) (s : ℤ)
    (hs : s ≤ ((p - 1) / 2 : ℕ)) (hs' : -((p - 1) / 2 : ℕ) ≤ s)
    (hr : (r : ℤ) - P.g N = cen p K k0 k + s) :
    tpRows P N p K D k0 x r =
      ∑ d2 : Fin D, ((if s = ((d2 : ℕ) : ℤ) then x d2 k else 0) +
        (if s = -((d2 : ℕ) : ℤ) then x d2 k else 0)) := by
  rw [tpRows_apply]
  refine Finset.sum_congr rfl fun d2 _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [tpPairRow_eval hp2 hD k0 d2 k k r s hs hs' hr]
    simp only [eq_self_iff_true, true_and]
    split_ifs <;> first | ring | simp
  · intro k2 _ hk2
    rw [tpPairRow_eval hp2 hD k0 d2 k2 k r s hs hs' hr]
    simp [hk2]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Independence of T- and T+ pairs.** -/
theorem mix_sep (hp2 : p ≠ 2) {K D1 : ℕ} (hD : D1 ≤ (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (ha : ∀ d k, ¬ Good P N p k0 d k → a d k = 0)
    (hb : ∀ d k, ¬ TpGood P N p k0 d k → b d k = 0)
    (h : ∀ r, tRows P N p K D1 k0 a r + tpRows P N p K (D1 + 1) k0 b r = 0) :
    a = 0 ∧ b = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hD' : D1 + 1 ≤ (p - 1) / 2 + 1 := by omega
  -- the coefficients of the offsets `d + 1`
  have hab : ∀ (d : Fin D1) (k : Fin K), a d k = 0 ∧
      ∀ dd : Fin (D1 + 1), (dd : ℕ) = (d : ℕ) + 1 → b dd k = 0 := by
    intro d k
    have hdl := d.isLt
    by_cases hg : Good P N p k0 d k
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
      have hrp : (cen p K k0 k + (((d : ℕ) : ℤ) + 1) + P.g N).toNat < P.n N := by omega
      have hrm : (cen p K k0 k - (((d : ℕ) : ℤ) + 1) + P.g N).toNat < P.n N := by omega
      have e1 := h ⟨_, hrp⟩
      have e2 := h ⟨_, hrm⟩
      rw [tRows_eval hp2 hD k0 a k ⟨_, hrp⟩ (((d : ℕ) : ℤ) + 1) (by omega) (by omega)
        (by simp only; omega),
        tpRows_eval hp2 hD' k0 b k ⟨_, hrp⟩ (((d : ℕ) : ℤ) + 1) (by omega) (by omega)
        (by simp only; omega)] at e1
      rw [tRows_eval hp2 hD k0 a k ⟨_, hrm⟩ (-(((d : ℕ) : ℤ) + 1)) (by omega) (by omega)
        (by simp only; omega),
        tpRows_eval hp2 hD' k0 b k ⟨_, hrm⟩ (-(((d : ℕ) : ℤ) + 1)) (by omega) (by omega)
        (by simp only; omega)] at e2
      obtain ⟨dd, hdd⟩ : ∃ dd : Fin (D1 + 1), (dd : ℕ) = (d : ℕ) + 1 := ⟨⟨_, by omega⟩, rfl⟩
      -- evaluate the finite sums
      have sA1 : ∑ d2 : Fin D1, ((if ((d : ℕ) : ℤ) + 1 = ((d2 : ℕ) : ℤ) + 1 then a d2 k else 0) -
          (if ((d : ℕ) : ℤ) + 1 = -(((d2 : ℕ) : ℤ) + 1) then a d2 k else 0)) = a d k := by
        rw [Finset.sum_eq_single d]
        · rw [if_pos rfl, if_neg (by omega)]; simp
        · intro d2 _ hd2
          have : (d2 : ℕ) ≠ (d : ℕ) := fun hh => hd2 (Fin.ext hh)
          rw [if_neg (by omega), if_neg (by omega)]
          simp
        · intro hh; exact absurd (Finset.mem_univ _) hh
      have sA2 : ∑ d2 : Fin D1, ((if -(((d : ℕ) : ℤ) + 1) = ((d2 : ℕ) : ℤ) + 1 then a d2 k else 0) -
          (if -(((d : ℕ) : ℤ) + 1) = -(((d2 : ℕ) : ℤ) + 1) then a d2 k else 0)) = - a d k := by
        rw [Finset.sum_eq_single d]
        · rw [if_neg (by omega), if_pos rfl]; simp
        · intro d2 _ hd2
          have : (d2 : ℕ) ≠ (d : ℕ) := fun hh => hd2 (Fin.ext hh)
          rw [if_neg (by omega), if_neg (by omega)]
          simp
        · intro hh; exact absurd (Finset.mem_univ _) hh
      have sB1 : ∑ d2 : Fin (D1 + 1), ((if ((d : ℕ) : ℤ) + 1 = ((d2 : ℕ) : ℤ) then b d2 k else 0) +
          (if ((d : ℕ) : ℤ) + 1 = -((d2 : ℕ) : ℤ) then b d2 k else 0)) = b dd k := by
        rw [Finset.sum_eq_single dd]
        · rw [if_pos (by omega), if_neg (by omega)]; simp
        · intro d2 _ hd2
          have : (d2 : ℕ) ≠ (dd : ℕ) := fun hh => hd2 (Fin.ext hh)
          rw [if_neg (by omega), if_neg (by omega)]
          simp
        · intro hh; exact absurd (Finset.mem_univ _) hh
      have sB2 : ∑ d2 : Fin (D1 + 1), ((if -(((d : ℕ) : ℤ) + 1) = ((d2 : ℕ) : ℤ) then b d2 k else 0) +
          (if -(((d : ℕ) : ℤ) + 1) = -((d2 : ℕ) : ℤ) then b d2 k else 0)) = b dd k := by
        rw [Finset.sum_eq_single dd]
        · rw [if_neg (by omega), if_pos (by omega)]; simp
        · intro d2 _ hd2
          have : (d2 : ℕ) ≠ (dd : ℕ) := fun hh => hd2 (Fin.ext hh)
          rw [if_neg (by omega), if_neg (by omega)]
          simp
        · intro hh; exact absurd (Finset.mem_univ _) hh
      rw [sA1, sB1] at e1
      rw [sA2, sB2] at e2
      have e3 : (2 : ZMod p) * a d k = 0 := by linear_combination e1 - e2
      have e4 : (2 : ZMod p) * b dd k = 0 := by linear_combination e1 + e2
      refine ⟨(mul_eq_zero.mp e3).resolve_left h2ne, fun dd' hdd' => ?_⟩
      have : dd' = dd := Fin.ext (by omega)
      rw [this]
      exact (mul_eq_zero.mp e4).resolve_left h2ne
    · refine ⟨ha d k hg, fun dd hdd => hb _ k ?_⟩
      intro hg'
      apply hg
      obtain ⟨h1, h2⟩ := hg'
      rw [hdd] at h1 h2
      refine ⟨?_, ?_⟩
      · simpa using h1
      · simpa using h2
  -- the centre rows
  have hb0 : ∀ (z : Fin (D1 + 1)), (z : ℕ) = 0 → ∀ k : Fin K, b z k = 0 := by
    intro z hz k
    by_cases hg : TpGood P N p k0 z k
    · obtain ⟨⟨h1, h2⟩, _⟩ := hg
      rw [hz] at h1 h2
      have hrc : (cen p K k0 k + P.g N).toNat < P.n N := by simp at h1 h2; omega
      have e1 := h ⟨_, hrc⟩
      rw [tRows_eval hp2 hD k0 a k ⟨_, hrc⟩ 0 (by omega) (by omega) (by simp only; omega),
        tpRows_eval hp2 hD' k0 b k ⟨_, hrc⟩ 0 (by omega) (by omega) (by simp only; omega)] at e1
      have sA : ∑ d2 : Fin D1, ((if (0 : ℤ) = ((d2 : ℕ) : ℤ) + 1 then a d2 k else 0) -
          (if (0 : ℤ) = -(((d2 : ℕ) : ℤ) + 1) then a d2 k else 0)) = 0 := by
        refine Finset.sum_eq_zero fun d2 _ => ?_
        rw [if_neg (by omega), if_neg (by omega)]; simp
      have sB : ∑ d2 : Fin (D1 + 1), ((if (0 : ℤ) = ((d2 : ℕ) : ℤ) then b d2 k else 0) +
          (if (0 : ℤ) = -((d2 : ℕ) : ℤ) then b d2 k else 0)) = 2 * b z k := by
        rw [Finset.sum_eq_single z]
        · rw [if_pos (by omega), if_pos (by omega)]; ring
        · intro d2 _ hd2
          have : (d2 : ℕ) ≠ (z : ℕ) := fun hh => hd2 (Fin.ext hh)
          rw [if_neg (by omega), if_neg (by omega)]
          simp
        · intro hh; exact absurd (Finset.mem_univ _) hh
      rw [sA, sB, zero_add] at e1
      exact (mul_eq_zero.mp e1).resolve_left h2ne
    · exact hb _ k hg
  refine ⟨?_, ?_⟩
  · funext d k; exact (hab d k).1
  · funext i k
    refine Fin.cases ?_ (fun d => ?_) i
    · exact hb0 _ rfl k
    · exact (hab d k).2 _ (by simp)

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
