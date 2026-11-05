module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HySysPair
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Add
@[expose] public section
set_option Elab.async false

/-!
# The HY+ slot system

Data `x : Fin (D + D) → Fin (K + K) → F_p`: diagonal blocks `a` (H+ data) and `b` (H- data),
off-diagonal blocks zero, and `HCons a b` (one condition per missing row).
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The domain. -/
def hyDom (P : Parameters) (N p K D : ℕ) (k0 : ℤ) [Fact p.Prime] :
    Submodule (ZMod p) (Fin (D + D) → Fin (K + K) → ZMod p) where
  carrier := {x | blk12 D D K K x = 0 ∧ blk21 D D K K x = 0 ∧
    HCons P N p k0 (blk11 D D K K x) (blk22 D D K K x)}
  zero_mem' := by
    refine ⟨by simp, by simp, ?_, ?_⟩ <;> intro t k _ <;> simp [blk11, blk22]
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨by simp [a1, b1], by simp [a2, b2], fun t k h => ?_, fun t k h => ?_⟩
    · have := a3 t k h; have := b3 t k h
      simp only [map_add, Pi.add_apply] at *; linear_combination a3 t k h + b3 t k h
    · have := a4 t k h; have := b4 t k h
      simp only [map_add, Pi.add_apply] at *; linear_combination a4 t k h + b4 t k h
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨by simp [a1], by simp [a2], fun t k h => ?_, fun t k h => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
      linear_combination c * a3 t k h
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
      linear_combination c * a4 t k h

theorem mem_hyDom {K D : ℕ} (k0 : ℤ) (x : Fin (D + D) → Fin (K + K) → ZMod p) :
    x ∈ hyDom P N p K D k0 ↔ blk12 D D K K x = 0 ∧ blk21 D D K K x = 0 ∧
      HCons P N p k0 (blk11 D D K K x) (blk22 D D K K x) := Iff.rfl

theorem hy_inj (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (a b : Fin D → Fin K → ZMod p) (hc : HCons P N p k0 a b)
    (h0 : ∀ r, sRows P N p K D 1 k0 a r + sRows P N p K D (-1) k0 b r = 0) : a = 0 ∧ b = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hab : ∀ t k, a t k = 0 ∧ b t k = 0 := by
    intro t k
    have s1 : b t k + a t k = 0 := by
      by_cases hg : InRange P N (hlo p K k0 k t)
      · obtain ⟨h1, h2⟩ := hg
        have hr : (hlo p K k0 k t + P.g N).toNat < P.n N := by omega
        have := h0 ⟨_, hr⟩
        rw [sRows_eval_lo hp2 hD 1 k0 a t k ⟨_, hr⟩ (by simp only; omega),
          sRows_eval_lo hp2 hD (-1) k0 b t k ⟨_, hr⟩ (by simp only; omega)] at this
        linear_combination this
      · exact hc.1 t k hg
    have s2 : a t k - b t k = 0 := by
      by_cases hg : InRange P N (hhi p K k0 k t)
      · obtain ⟨h1, h2⟩ := hg
        have hr : (hhi p K k0 k t + P.g N).toNat < P.n N := by omega
        have := h0 ⟨_, hr⟩
        rw [sRows_eval_hi hp2 hD 1 k0 a t k ⟨_, hr⟩ (by simp only; omega),
          sRows_eval_hi hp2 hD (-1) k0 b t k ⟨_, hr⟩ (by simp only; omega)] at this
        linear_combination this
      · exact hc.2 t k hg
    have e3 : (2 : ZMod p) * a t k = 0 := by linear_combination s1 + s2
    have e4 : (2 : ZMod p) * b t k = 0 := by linear_combination s1 - s2
    exact ⟨(mul_eq_zero.mp e3).resolve_left h2ne, (mul_eq_zero.mp e4).resolve_left h2ne⟩
  exact ⟨funext fun t => funext fun k => (hab t k).1, funext fun t => funext fun k => (hab t k).2⟩

theorem hy_blocks_zero {K D : ℕ} (x : Fin (D + D) → Fin (K + K) → ZMod p)
    (h11 : blk11 D D K K x = 0) (h22 : blk22 D D K K x = 0) (h12 : blk12 D D K K x = 0)
    (h21 : blk21 D D K K x = 0) : x = 0 := by
  funext d k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · exact congrFun (congrFun h11 i) a
  · exact congrFun (congrFun h12 i) b
  · exact congrFun (congrFun h21 j) a
  · exact congrFun (congrFun h22 j) b

/-- **The HY+ slot system.** -/
def hySys (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (K D : ℕ) (k0 : ℤ)
    (hD : D ≤ (p - 1) / 2) : SlotSystem P N p where
  K := K + K
  D := D + D
  emax := P.h N + (p - 1) / 2 + D
  prof := profAdd (profHp p K k0) (profHm p K k0)
  lam := Fin.append (fun t : Fin D => hLam P N p (t : ℕ)) (fun t : Fin D => hmLam P N p (t : ℕ))
  rows := (sRows P N p K D 1 k0).comp (blk11 D D K K) + (sRows P N p K D (-1) k0).comp (blk22 D D K K)
  dom := hyDom P N p K D k0
  deg := fun d => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · rw [Fin.append_left]
      have := hLam_natDegree_lt (P := P) (N := N) hp2 hD i
      have := i.isLt
      omega
    · rw [Fin.append_right]
      have := hmLam_natDegree_lt (P := P) (N := N) hp2 hD j
      have := j.isLt
      omega
  repU := fun x hx => by
    obtain ⟨h3, h4, hc⟩ := (mem_hyDom k0 x).mp hx
    have key := hy_repU (P := P) (N := N) hp2 k0 (blk11 D D K K x) (blk22 D D K K x) hc
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [intrinsicU_add', mul_add, ← mul_add, key, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      have hz : fl2 K K (x (Fin.castAdd D i)) = 0 := congrFun h3 i
      show _ = (hTy p K k0).comp (fl1 K K) (x (Fin.castAdd D i)) +
        (hmTy p K k0).comp (fl2 K K) (x (Fin.castAdd D i))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, add_zero]; rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 K K (x (Fin.natAdd D j)) = 0 := congrFun h4 j
      show _ = (hTy p K k0).comp (fl1 K K) (x (Fin.natAdd D j)) +
        (hmTy p K k0).comp (fl2 K K) (x (Fin.natAdd D j))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, zero_add]; rfl
  repT := fun x hx => by
    obtain ⟨h3, h4, hc⟩ := (mem_hyDom k0 x).mp hx
    have key := hy_repT (P := P) (N := N) hp2 k0 (blk11 D D K K x) (blk22 D D K K x) hc
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [intrinsicT_add', mul_add, ← mul_add, key, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      have hz : fl2 K K (x (Fin.castAdd D i)) = 0 := congrFun h3 i
      show _ = (hGy p K k0).comp (fl1 K K) (x (Fin.castAdd D i)) +
        (hmGy p K k0).comp (fl2 K K) (x (Fin.castAdd D i))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, add_zero]; rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 K K (x (Fin.natAdd D j)) = 0 := congrFun h4 j
      show _ = (hGy p K k0).comp (fl1 K K) (x (Fin.natAdd D j)) +
        (hmGy p K k0).comp (fl2 K K) (x (Fin.natAdd D j))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, zero_add]; rfl
  inj := fun x hx h0 => by
    obtain ⟨h3, h4, hc⟩ := (mem_hyDom k0 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at h0
    obtain ⟨e1, e2⟩ := hy_inj hp2 hD k0 _ _ hc (fun r => congrFun h0 r)
    exact hy_blocks_zero x e1 e2 h3 h4

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
