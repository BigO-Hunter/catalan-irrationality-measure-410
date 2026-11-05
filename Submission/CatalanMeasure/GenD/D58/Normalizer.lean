module

public import Submission.CatalanMeasure.GenD.D58.Kap
public import Submission.CatalanMeasure.GenD.DenomGrowth2

@[expose] public section

/-!
# D58: the normalizer and the growth of its denominator (instance file)

* `lb`            : the nullity bound `kap = segExp segs - 1`  (`NullityLB`, via `famKap`);
* `Znorm`         : the `Normalizer` of the displaced design (`normalizerOf`);
* `Znorm_growth`  : `log D_N ≤ (gD58 + ε) N²` eventually, with
  `gD58 = (2673/8) log 2 + 116 + 24269/4 - 35369/1848`.
-/

namespace CatalanMeasure.GenD
namespace D58

open PrimeGrowth CatalanMeasure.Parametric Odd Filter

noncomputable section

def kapD58 (N p : ℕ) : ℕ := segExp segs N p - 1

theorem odd_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two hp2)

/-- The nullity lower bound of the displaced design. -/
def lb : NullityLB Odd.design :=
  NullityLB.ofFam Odd.design Odd.design_admissible kapD58
    (fun N p hN hp hp2 _ => by
      have := segExp_le_famKap hN (odd_of_prime hp hp2)
      unfold kapD58
      omega)

theorem lb_kap (N p : ℕ) : lb.kap N p = segExp segs N p - 1 := rfl

theorem segExp_zero_outside {N p : ℕ} (hN : 0 < N) (h : p ≤ 12 * N ∨ 26 * N < p) :
    segExp segs N p = 0 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : segExp segs N p ≤ 0 := by
    apply segExp_le
    intro s hs hc
    simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    obtain ⟨hc1, hc2⟩ := hc
    rcases h with h | h
    · have h' : (p : ℝ) ≤ 12 * N := by exact_mod_cast h
      exfalso
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hc1 <;>
        linarith
    · have h' : (26 : ℝ) * N < p := by exact_mod_cast h
      exfalso
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hc2 <;>
        linarith
  omega

theorem segs_bounds : ∀ s ∈ segs, 12 ≤ s.a ∧ s.b ≤ 26 := by
  intro s hs
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> norm_num

theorem rec_ok_d58 : ∀ N q : ℕ, 79 ≤ N → q.Prime → N < q → q ≤ 2 * N →
    2 * Odd.design.n N ≤ OddProfile.oddLossNat Odd.design N q ∧ lb.kap N q = 0 := by
  intro N q hN hq hNq hqN
  have hN0 : 0 < N := by omega
  refine ⟨?_, ?_⟩
  · unfold OddProfile.oddLossNat
    rw [Odd.design_H, if_pos (by omega), Odd.lower_eq (by omega)]
    unfold Odd.lossNat
    rw [if_pos (by omega)]
    simp only [Parameters.n, Odd.design]
    omega
  · rw [lb_kap, segExp_zero_outside hN0 (Or.inl (by omega))]

theorem hloss_d58 {N p : ℕ} (hN : 0 < N) (hp : p ≤ Odd.design.H N) :
    (OddProfile.oddLossNat Odd.design N p : ℝ) = N * f58.eval ((p : ℝ) / N) := by
  rw [Odd.design_H] at hp
  unfold OddProfile.oddLossNat
  rw [Odd.design_H]
  by_cases h : 2 * p ≤ 78 * N
  · rw [if_pos h, Odd.lower_eq h]
    exact Odd.lossNat_cast hN hp
  · rw [if_neg h, Odd.upper_eq (by omega) hp]
    exact Odd.lossNat_cast hN hp

theorem hf0_d58 (x : ℝ) (hx : x ≤ 1) : f58.eval x = 116 := by
  simp only [PL.Prof.eval, f58, PL.hinges_cons, PL.hinges_nil]
  rw [PL.ramp_of_le (by linarith : x ≤ 59 / 2), PL.ramp_of_le (by linarith : x ≤ 69 / 2),
    PL.ramp_of_le (by linarith : x ≤ 39), PL.ramp_of_le (by linarith : x ≤ 81 / 2),
    PL.ramp_of_le (by linarith : x ≤ 48), PL.ramp_of_le (by linarith : x ≤ 69),
    PL.ramp_of_le (by linarith : x ≤ 70)]
  ring

theorem hgain_d58 : ∀ N p : ℕ, 0 < N → p.Prime → Odd.design.H N < p ^ 2 → p ≤ Odd.design.H N →
    lb.kap N p ≤ OddProfile.oddLossNat Odd.design N p ∧
      (0 < lb.kap N p → 2 * Odd.design.n N ≤ OddProfile.oddLossNat Odd.design N p) := by
  intro N p hN hp hH hpH
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    rw [Odd.design_H] at hH
    omega
  have hk : lb.kap N p ≤ Odd.design.n N := by
    have h := lb.ok N p hN hp hp2 hH
    haveI : Fact p.Prime := ⟨hp⟩
    exact h.trans (Nat.sub_le _ _)
  have hn : Odd.design.n N = 58 * N := by simp [Parameters.n, Odd.design]
  have hloss : 0 < lb.kap N p → OddProfile.oddLossNat Odd.design N p = 116 * N := by
    intro hpos
    have hs : 2 ≤ segExp segs N p := by rw [lb_kap] at hpos; omega
    have hout : ¬ (p ≤ 12 * N ∨ 26 * N < p) := by
      intro h
      rw [segExp_zero_outside hN h] at hs
      omega
    push Not at hout
    unfold OddProfile.oddLossNat
    rw [Odd.design_H, if_pos (by omega), Odd.lower_eq (by omega)]
    unfold Odd.lossNat
    rw [if_pos (by omega)]
  constructor
  · by_cases h0 : lb.kap N p = 0
    · rw [h0]; exact Nat.zero_le _
    · rw [hloss (Nat.pos_of_ne_zero h0)]; omega
  · intro hpos
    rw [hloss hpos, hn]; omega

theorem hgood_d58 : ∀ s ∈ segs, Seg.Good (fun N p => lb.kap N p + 1) s := by
  intro s hs
  have hs' := hs
  unfold segs profSegs at hs'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs'
  have hb := segs_bounds _ hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hb.1; dsimp only at this ⊢; linarith
  · simp only [cellProfs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · exact t.2.2.continuous.continuousOn
  · intro N p hN hp h1 h2
    have := segExp_ge hs h1 h2
    have h' : segExp segs N p ≤ segExp segs N p - 1 + 1 := by omega
    have h'' : ((segExp segs N p : ℕ) : ℝ) ≤ ((segExp segs N p - 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast h'
    refine this.trans (h''.trans (le_of_eq ?_))
    rfl

theorem hord_d58 : segs.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.pairwise_cons,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil,
    and_true]
  norm_num

theorem hwin_d58 : ∀ s ∈ segs, ∀ N p : ℕ, 0 < N → p.Prime → s.a * (N : ℝ) < p →
    (p : ℝ) ≤ s.b * N → p ≠ 2 ∧ Odd.design.H N < p ^ 2 ∧ p ≤ Odd.design.H N := by
  intro s hs N p hN hp h1 h2
  obtain ⟨ha, hb⟩ := segs_bounds s hs
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo : (12 : ℝ) * N < p := by nlinarith
  have hhi : (p : ℝ) ≤ 26 * N := by nlinarith
  have hlo' : 12 * N < p := by exact_mod_cast hlo
  have hhi' : p ≤ 26 * N := by exact_mod_cast hhi
  rw [Odd.design_H]
  refine ⟨by omega, ?_, by omega⟩
  have h13 : 13 ≤ p := by omega
  have := Nat.mul_le_mul (show 12 * N + 1 ≤ p by omega) h13
  nlinarith

/-- The normalizer of the displaced design. -/
def Znorm : Normalizer Odd.design :=
  normalizerOf Odd.design Odd.design_admissible lb 79 (by rw [Odd.design_H]; norm_num)
    (fun N p hN h => Odd.side_of hN h) rec_ok_d58

theorem Znorm_D : Znorm.D = expDenom Odd.design (denExp Odd.design lb) := rfl

/-- The loss integral: `∫_1^78 f58 = 24269/4`. -/
theorem integral_f58 : ∫ x in (1 : ℝ)..78, f58.eval x = 24269 / 4 := by
  rw [PL.Prof.integral_eval f58 (by norm_num)]
  simp only [PL.Prof.area, f58, PL.hingeInt_cons, PL.hingeInt_nil]
  rw [PL.ramp_of_ge (by norm_num : (59 / 2 : ℝ) ≤ 78), PL.ramp_of_ge (by norm_num : (69 / 2 : ℝ) ≤ 78),
    PL.ramp_of_ge (by norm_num : (39 : ℝ) ≤ 78), PL.ramp_of_ge (by norm_num : (81 / 2 : ℝ) ≤ 78),
    PL.ramp_of_ge (by norm_num : (48 : ℝ) ≤ 78), PL.ramp_of_ge (by norm_num : (69 : ℝ) ≤ 78),
    PL.ramp_of_ge (by norm_num : (70 : ℝ) ≤ 78),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 59 / 2), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 69 / 2),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 39), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 81 / 2),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 48), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 69),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 70)]
  norm_num

/-- Growth constant of the denominator in the design's own unit. -/
def gD58 : ℝ := 2673 / 8 * Real.log 2 + 116 + 24269 / 4 - 35369 / 1848

/-- **Growth of the denominator.** -/
theorem Znorm_growth {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (Znorm.D N : ℝ) ≤ (gD58 + ε) * (N : ℝ) ^ 2 := by
  have hH78 : ((Odd.design.H 1 : ℕ) : ℝ) = 78 := by
    rw [Odd.design_H]; norm_num
  have h := denom_growth Odd.design Odd.design_admissible lb f58 segs 116 1 (fun N p hN hp => hloss_d58 hN hp) hf0_d58
    (by rw [Odd.design_H]; norm_num) hgain_d58 hgood_d58 hord_d58 hwin_d58 hε
  rw [hH78, integral_f58, segs_totalArea] at h
  have hA : TwoAdic.A2 (Odd.design.n0 : ℝ) (78 : ℝ) (Odd.design.b0 : ℝ) = 2673 / 8 := by
    simp only [TwoAdic.A2, Odd.design]
    norm_num
  rw [hA] at h
  have e : gD58 + ε = 2673 / 8 * Real.log 2 + (116 + 24269 / 4) - 35369 / 1848 + ε := by
    unfold gD58; ring
  rw [e]
  exact h

end

end D58
end CatalanMeasure.GenD
