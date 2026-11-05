module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZMainCap
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLB
@[expose] public section
set_option Elab.async false

/-!
# `zHLBcap`: Theorem Z, Law_H(4), window with cap (`p ≤ η < 2p`, `L ≤ 5p`)
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Bad-prime integer of the cap window (adds `6`, so `p ≠ 2, 3`). -/
def ZcH6 : ℕ := Nat.lcm ZcH' 6

/-- The cap window of the Law_H(4) bound. -/
def zHAppCap (P : Parameters) (N p : ℕ) : Prop :=
  ¬ p ∣ ZcH6 ∧
  P.h N + (p - 1) / 2 ≤ p - 1 ∧ P.q N + P.h N ≤ (p - 1) / 2 ∧
  5 * p + 1 ≤ P.H N ∧ P.H N - 1 - 5 * p < p ∧ P.h N + (p - 1) / 2 ≤ P.H N - 4 * p ∧
  P.L N ≤ 5 * p ∧ P.b N < p ∧ P.g N ≤ (p - 1) / 2 ∧ 3 * p + 1 + P.g N ≤ P.n N

/-- The value of the cap-window bound. -/
def zHvalCap (P : Parameters) (N p : ℕ) : ℕ :=
  let hp := (p - 1) / 2
  let t := P.H N - 1 - 5 * p
  let rt := min (P.n N - 1 - P.g N - 3 * p) hp
  let g := P.g N
  (4 * hp + 2) - ((hp - rt) + (hp - g)) -
    ((hp + 1 - P.h N - P.q N) + (hp + 1 - P.h N) + (P.h N + hp - (t + 1)) +
      ((P.h N + min (max g rt) hp) - max (g + P.h N) (t + 1)) +
      ((min (p - 1) (t + p - P.b N) + 1) - (t + 1)) + (t + 1) + (t + 1) + (t + 1 - P.b N))

theorem zHvalCap_le_nullity {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hH2 : P.H N < p ^ 2) (hA : zHAppCap P N p) :
    zHvalCap P N p ≤ nullity P N p := by
  obtain ⟨hc, h1, h2, h3, h4, h5, hL, h6, h7, h8⟩ := hA
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hc' : ¬ p ∣ ZcH' := fun h => hc (h.trans (Nat.dvd_lcm_left _ _))
  have hc6 : ¬ p ∣ 6 := fun h => hc (h.trans (Nat.dvd_lcm_right _ _))
  have hp3' : p ≠ 3 := fun h => hc6 (by rw [h]; norm_num)
  have h3z : (3 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    exact hp3' ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp this)
  have hc0 : ¬ p ∣ ZcH := fun h => hc' (h.trans (Nat.dvd_lcm_left _ _))
  have hcU : ¬ p ∣ DqU.num.natAbs := fun h =>
    hc' (h.trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)))
  have hcY : ¬ p ∣ DqY.num.natAbs := fun h =>
    hc' (h.trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)))
  have hH8 : 8 ≤ P.H N := by omega
  set hpv : ℕ := (p - 1) / 2 with hhpv
  have hodd : p = 2 * hpv + 1 := by have := p_odd_half hp2; omega
  have hcell := cellHyp_H hp2 hc0 (by omega : 7 ≤ P.H N)
  have hcap := cellHypCap_H hp2 hc0 hH8
  have mU : ∀ k < 4, Q.uH k ∈ unitSub p := fun k hk => uH_mem hp2 hc0 hk
  have mU2 : ∀ k < 4, Q.u2H k ∈ unitSub p := fun k hk => u2H_mem hp2 hc0 hk
  have mY1 : ∀ k < 4, Q.y1H k ∈ unitSub p := fun k hk => y1H_mem hp2 hc0 hk
  have mY2 : ∀ k < 4, Q.y2H k ∈ unitSub p := fun k hk => y2H_mem hp2 hc0 hk
  have hDU : palindromicRatResidue p DqU =
      zvec p 4 Q.uH ⟨2, by omega⟩ * zvec p 4 Q.u2H ⟨3, by omega⟩ -
        zvec p 4 Q.uH ⟨3, by omega⟩ * zvec p 4 Q.u2H ⟨2, by omega⟩ := by
    have e1 := map_mul (resHom p) (⟨Q.uH 2, mU 2 (by omega)⟩ : unitSub p) ⟨Q.u2H 3, mU2 3 (by omega)⟩
    have e2 := map_mul (resHom p) (⟨Q.uH 3, mU 3 (by omega)⟩ : unitSub p) ⟨Q.u2H 2, mU2 2 (by omega)⟩
    have e3 := map_sub (resHom p)
      (⟨Q.uH 2, mU 2 (by omega)⟩ * ⟨Q.u2H 3, mU2 3 (by omega)⟩ : unitSub p)
      (⟨Q.uH 3, mU 3 (by omega)⟩ * ⟨Q.u2H 2, mU2 2 (by omega)⟩)
    simp only [resHom_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub] at e1 e2 e3
    rw [DqU, e3, e1, e2]; rfl
  have hDY : palindromicRatResidue p DqY =
      zvec p 4 Q.y1H ⟨2, by omega⟩ * zvec p 4 Q.y2H ⟨3, by omega⟩ -
        zvec p 4 Q.y1H ⟨3, by omega⟩ * zvec p 4 Q.y2H ⟨2, by omega⟩ := by
    have e1 := map_mul (resHom p) (⟨Q.y1H 2, mY1 2 (by omega)⟩ : unitSub p) ⟨Q.y2H 3, mY2 3 (by omega)⟩
    have e2 := map_mul (resHom p) (⟨Q.y1H 3, mY1 3 (by omega)⟩ : unitSub p) ⟨Q.y2H 2, mY2 2 (by omega)⟩
    have e3 := map_sub (resHom p)
      (⟨Q.y1H 2, mY1 2 (by omega)⟩ * ⟨Q.y2H 3, mY2 3 (by omega)⟩ : unitSub p)
      (⟨Q.y1H 3, mY1 3 (by omega)⟩ * ⟨Q.y2H 2, mY2 2 (by omega)⟩)
    simp only [resHom_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub] at e1 e2 e3
    rw [DqY, e3, e1, e2]; rfl
  have mDU : DqU ∈ unitSub p := by
    unfold DqU
    exact Subring.sub_mem _ (Subring.mul_mem _ (mU 2 (by omega)) (mU2 3 (by omega)))
      (Subring.mul_mem _ (mU 3 (by omega)) (mU2 2 (by omega)))
  have mDY : DqY ∈ unitSub p := by
    unfold DqY
    exact Subring.sub_mem _ (Subring.mul_mem _ (mY1 2 (by omega)) (mY2 3 (by omega)))
      (Subring.mul_mem _ (mY1 3 (by omega)) (mY2 2 (by omega)))
  have hnzU := res_ne_zero_of_num DqU mDU hcU
  have hnzY := res_ne_zero_of_num DqY mDY hcY
  rw [hDU] at hnzU
  rw [hDY] at hnzY
  have hind1 : ∀ (c1 c2 : ZMod p), (∀ k : Fin 4, c1 * zvec p 4 Q.uH k + c2 * zvec p 4 Q.u2H k = 0) →
      c1 = 0 ∧ c2 = 0 := fun c1 c2 h =>
    hind_gen _ _ _ _ hnzU c1 c2 (h ⟨2, by omega⟩) (h ⟨3, by omega⟩)
  have hind2 : ∀ (c1 c2 : ZMod p), (∀ k : Fin 4, c1 * zvec p 4 Q.y1H k + c2 * zvec p 4 Q.y2H k = 0) →
      c1 = 0 ∧ c2 = 0 := fun c1 c2 h =>
    hind_gen _ _ _ _ hnzY c1 c2 (h ⟨2, by omega⟩) (h ⟨3, by omega⟩)
  have hphp : hpv < p := by omega
  exact zHcap_le_nullity hP hN hp2 hH2 (hp := hpv) rfl (zvec p 4 Q.uH) (zvec p 4 Q.u2H)
    (zvec p 4 Q.y1H) (zvec p 4 Q.y2H) hcell hcap h3z hind1 hind2 h1 h2 (P.H N - 1 - 5 * p)
    (by omega) h4 (by omega) hL h6 (min (P.n N - 1 - P.g N - 3 * p) hpv) (P.g N)
    (min_le_right _ _) h7 rfl
    (fun d hd hn => design_vtop (rtop := P.n N - 1 - P.g N - 3 * p) hphp (by omega) rfl d hd hn)
    (fun d hd hn => design_v0 hphp (by omega) d hd hn)
    (fun k d hd hk => design_oth (rtop := P.n N - 1 - P.g N - 3 * p) hphp (by omega) k d hd hk)
    (fun k d hd hk => design_oth' (rtop := P.n N - 1 - P.g N - 3 * p) hphp (by omega) k d hd hk)

/-- **Theorem Z, Law_H(4), cap window**, as a nullity lower bound. -/
def zHLBcap (P : Parameters) (hP : Admissible P) : CatalanMeasure.GenD.NullityLB P :=
  CatalanMeasure.GenD.NullityLB.ofWindow P (zHAppCap P) (zHvalCap P)
    (fun N p hN hpp hp2 hH2 hA => by
      haveI : Fact p.Prime := ⟨hpp⟩
      exact zHvalCap_le_nullity hP hN hp2 hH2 hA)

/-- **Theorem Z, Law_H(4)**: the no-cap and cap windows together. -/
def zHLB (P : Parameters) (hP : Admissible P) : CatalanMeasure.GenD.NullityLB P :=
  CatalanMeasure.GenD.NullityLB.sup (zHLBnc P hP) (zHLBcap P hP)

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
