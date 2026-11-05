module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZLLB
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.MainCapL5
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLBcap
@[expose] public section
set_option Elab.async false

/-!
# `zLLB`: Theorem Z, Law_L(4), cap window (`p ≤ η < 2p`, any `L`), as a `NullityLB` (G2h)

Includes the digit-`5` group when `L > 5p` (`L - 5p` extra conditions, `c5M`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The cap window of the Law_L(4) bound (any `L`; `L > 5p` adds the digit-`5` group). -/
def zLApp5 (P : Parameters) (N p : ℕ) : Prop :=
  ¬ p ∣ ZcL6 ∧
  P.h N + (p - 1) / 2 ≤ p - 1 ∧ P.q N + P.h N ≤ (p - 1) / 2 ∧
  5 * p + 1 ≤ P.H N ∧ P.H N - 1 - 5 * p < p ∧ P.h N + (p - 1) / 2 ≤ P.H N - 4 * p ∧
  P.b N < p ∧ P.g N ≤ (p - 1) / 2 ∧
  4 * p ≤ P.n N - 1 - P.g N + (p - 1) / 2 ∧ P.n N - 1 - P.g N < 4 * p ∧ P.g N < P.n N

/-- The value of the Law_L(4) cap-window bound (`d₀ = 4p - (n - 1 - g)`). -/
def zLval5 (P : Parameters) (N p : ℕ) : ℕ :=
  let hp := (p - 1) / 2
  let t := P.H N - 1 - 5 * p
  let d0 := 4 * p - (P.n N - 1 - P.g N)
  let g := P.g N
  (4 * hp + 2) - ((hp - 0) + (hp - g) + d0) -
    ((hp + 1 - P.h N - P.q N) + (hp + 1 - P.h N) + (P.h N + hp - (t + 1)) +
      (t + 1) + (t + 1 - P.b N) + (P.L N - 5 * p))

theorem zLval5_le_nullity {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hH2 : P.H N < p ^ 2) (hA : zLApp5 P N p) :
    zLval5 P N p ≤ nullity P N p := by
  obtain ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hA
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hc' : ¬ p ∣ ZcL' := fun h => hc (h.trans (Nat.dvd_lcm_left _ _))
  have hc6 : ¬ p ∣ 6 := fun h => hc (h.trans (Nat.dvd_lcm_right _ _))
  have hp3' : p ≠ 3 := fun h => hc6 (by rw [h]; norm_num)
  have h3z : (3 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    exact hp3' ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp this)
  have hc0 : ¬ p ∣ ZcL := fun h => hc' (h.trans (Nat.dvd_lcm_left _ _))
  have hcU : ¬ p ∣ DqUL.num.natAbs := fun h =>
    hc' (h.trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)))
  have hcY : ¬ p ∣ DqYL.num.natAbs := fun h =>
    hc' (h.trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)))
  have hH8 : 8 ≤ P.H N := by omega
  set hpv : ℕ := (p - 1) / 2 with hhpv
  have hodd : p = 2 * hpv + 1 := by have := p_odd_half hp2; omega
  have hcell := cellHyp_L hp2 hc0 (by omega : 7 ≤ P.H N)
  have hcell0 := cellHyp0_L hp2 hc0 (by omega : 7 ≤ P.H N)
  have hcap := cellHypCap_L hp2 hc0 hH8
  have hcap1 := cellHypCap1_L hp2 hc0 hH8
  have mU : ∀ k < 5, Q.uL k ∈ unitSub p := fun k hk => uL_mem hp2 hc0 hk
  have mU2 : ∀ k < 5, Q.u2L k ∈ unitSub p := fun k hk => u2L_mem hp2 hc0 hk
  have mY1 : ∀ k < 5, Q.y1L k ∈ unitSub p := fun k hk => y1L_mem hp2 hc0 hk
  have mY2 : ∀ k < 5, Q.y2L k ∈ unitSub p := fun k hk => y2L_mem hp2 hc0 hk
  have hDU : palindromicRatResidue p DqUL =
      zvec p 5 Q.uL ⟨3, by omega⟩ * zvec p 5 Q.u2L ⟨4, by omega⟩ -
        zvec p 5 Q.uL ⟨4, by omega⟩ * zvec p 5 Q.u2L ⟨3, by omega⟩ := by
    have e1 := map_mul (resHom p) (⟨Q.uL 3, mU 3 (by omega)⟩ : unitSub p) ⟨Q.u2L 4, mU2 4 (by omega)⟩
    have e2 := map_mul (resHom p) (⟨Q.uL 4, mU 4 (by omega)⟩ : unitSub p) ⟨Q.u2L 3, mU2 3 (by omega)⟩
    have e3 := map_sub (resHom p)
      (⟨Q.uL 3, mU 3 (by omega)⟩ * ⟨Q.u2L 4, mU2 4 (by omega)⟩ : unitSub p)
      (⟨Q.uL 4, mU 4 (by omega)⟩ * ⟨Q.u2L 3, mU2 3 (by omega)⟩)
    simp only [resHom_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub] at e1 e2 e3
    rw [DqUL, e3, e1, e2]; rfl
  have hDY : palindromicRatResidue p DqYL =
      zvec p 5 Q.y1L ⟨3, by omega⟩ * zvec p 5 Q.y2L ⟨4, by omega⟩ -
        zvec p 5 Q.y1L ⟨4, by omega⟩ * zvec p 5 Q.y2L ⟨3, by omega⟩ := by
    have e1 := map_mul (resHom p) (⟨Q.y1L 3, mY1 3 (by omega)⟩ : unitSub p) ⟨Q.y2L 4, mY2 4 (by omega)⟩
    have e2 := map_mul (resHom p) (⟨Q.y1L 4, mY1 4 (by omega)⟩ : unitSub p) ⟨Q.y2L 3, mY2 3 (by omega)⟩
    have e3 := map_sub (resHom p)
      (⟨Q.y1L 3, mY1 3 (by omega)⟩ * ⟨Q.y2L 4, mY2 4 (by omega)⟩ : unitSub p)
      (⟨Q.y1L 4, mY1 4 (by omega)⟩ * ⟨Q.y2L 3, mY2 3 (by omega)⟩)
    simp only [resHom_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub] at e1 e2 e3
    rw [DqYL, e3, e1, e2]; rfl
  have mDU : DqUL ∈ unitSub p := by
    unfold DqUL
    exact Subring.sub_mem _ (Subring.mul_mem _ (mU 3 (by omega)) (mU2 4 (by omega)))
      (Subring.mul_mem _ (mU 4 (by omega)) (mU2 3 (by omega)))
  have mDY : DqYL ∈ unitSub p := by
    unfold DqYL
    exact Subring.sub_mem _ (Subring.mul_mem _ (mY1 3 (by omega)) (mY2 4 (by omega)))
      (Subring.mul_mem _ (mY1 4 (by omega)) (mY2 3 (by omega)))
  have hnzU := res_ne_zero_of_num DqUL mDU hcU
  have hnzY := res_ne_zero_of_num DqYL mDY hcY
  rw [hDU] at hnzU
  rw [hDY] at hnzY
  have hind1 : ∀ (c1 c2 : ZMod p), (∀ k : Fin 5, c1 * zvec p 5 Q.uL k + c2 * zvec p 5 Q.u2L k = 0) →
      c1 = 0 ∧ c2 = 0 := fun c1 c2 h =>
    hind_gen _ _ _ _ hnzU c1 c2 (h ⟨3, by omega⟩) (h ⟨4, by omega⟩)
  have hind2 : ∀ (c1 c2 : ZMod p), (∀ k : Fin 5, c1 * zvec p 5 Q.y1L k + c2 * zvec p 5 Q.y2L k = 0) →
      c1 = 0 ∧ c2 = 0 := fun c1 c2 h =>
    hind_gen _ _ _ _ hnzY c1 c2 (h ⟨3, by omega⟩) (h ⟨4, by omega⟩)
  have hphp : hpv < p := by omega
  have hnd : P.n N = 4 * p - (4 * p - (P.n N - 1 - P.g N)) + 1 + P.g N := by omega
  exact zLcap5_le_nullity hP hN hp2 hH2 (hp := hpv) rfl (zvec p 5 Q.uL) (zvec p 5 Q.u2L)
    (zvec p 5 Q.y1L) (zvec p 5 Q.y2L) hcell hcell0 hcap hcap1 h3z hind1 hind2 h1 h2
    (P.H N - 1 - 5 * p) (by omega) h4 (by omega) h6 (P.g N) (4 * p - (P.n N - 1 - P.g N))
    h7 rfl (by omega) (by omega)
    (fun d hd hn => by omega)
    (fun d hd hn => designL_vtopm (d0 := 4 * p - (P.n N - 1 - P.g N)) hphp hnd (by omega) d hd hn)
    (fun d hd hn => designL_v0 hphp h10 d hd hn)
    (fun k d hd hk => designL_oth hphp hnd (by omega) hodd.symm k d hd hk)
    (fun k d hd hk hk4 => designL_oth' hphp hnd (by omega) k d hd hk hk4)

/-- **Theorem Z, Law_L(4), cap window**, as a nullity lower bound. -/
def zLLB (P : Parameters) (hP : Admissible P) : CatalanMeasure.GenD.NullityLB P :=
  CatalanMeasure.GenD.NullityLB.ofWindow P (zLApp5 P) (zLval5 P)
    (fun N p hN hpp hp2 hH2 hA => by
      haveI : Fact p.Prime := ⟨hpp⟩
      exact zLval5_le_nullity hP hN hp2 hH2 hA)

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
