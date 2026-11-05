module
public import Submission.CatalanMeasure.GenD.Uniform.W.Tier3.HP2
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HLB
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PLB
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# `hp2LB`: the HP2 family as a `NullityLB` (lane G6)

`hp2Val P N p s k0 k1 ilo` is `hpVal s + perVal (s-1) ilo` when both applicability conditions and the
separation condition of `sum_nullity2` hold, and `0` otherwise.  `hp2Kap` is the maximum over
`(s, k0, k1, ilo)`; `hp2LB` is a nullity lower bound for every admissible design.
-/

namespace CatalanMeasure.GenD.Uniform.W.Tier3
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Applicability of HP2 at `(s, k0, k1, ilo)` (period slot at the window pair `(s-1, s)`). -/
def hp2OK (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) : Prop :=
  1 ≤ s ∧ hpOK P N p s k0 k1 ∧ perOK P N p (s - 1) k0 k1 ilo ∧
    (perPmax P N p (s - 1) k0 k1 < (hpElo P N p s : ℤ) ∨ (hpEta P N p s : ℤ) < ilo + p)

open Classical in
/-- The HP2 integer bound. -/
def hp2Val (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) : ℕ :=
  if hp2OK P N p s k0 k1 ilo then hpVal P N p s k0 k1 + perVal P N p (s - 1) k0 k1 ilo else 0

theorem hp2Val_le_nullity {P : Parameters} {N p : ℕ} [Fact p.Prime] (hP : Admissible P) (hN : 0 < N)
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) :
    hp2Val P N p s k0 k1 ilo ≤ nullity P N p := by
  classical
  unfold hp2Val
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact hp2_le_nullity hP hN hp2 hH s (s - 1) (by omega) k0 k1 ilo h2 h3 h4
  · exact Nat.zero_le _

/-- Maximum of the HP2 values over digits, block ranges and support starts. -/
def hp2Kap (P : Parameters) (N p : ℕ) : ℕ :=
  (Finset.range (P.H N / p + 1)).sup fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
        (Finset.range (hpEta P N p (s - 1) + 1)).sup fun ilo => hp2Val P N p s k0 k1 ilo

/-- **`hp2LB`**: the HP2 family. -/
def hp2LB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := hp2Kap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold hp2Kap
    refine Finset.sup_le fun s _ => Finset.sup_le fun k0 _ => Finset.sup_le fun k1 _ =>
      Finset.sup_le fun ilo _ => ?_
    exact hp2Val_le_nullity hP hN hp2 hH s k0 k1 ilo

theorem hp2Val_le_hp2Kap (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ)
    (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p)
    (hilo : ilo ≤ hpEta P N p (s - 1)) :
    hp2Val P N p s k0 k1 ilo ≤ hp2Kap P N p := by
  unfold hp2Kap
  refine le_trans ?_ (Finset.le_sup (f := fun s =>
      (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
        (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
          (Finset.range (hpEta P N p (s - 1) + 1)).sup fun ilo => hp2Val P N p s k0 k1 ilo)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hs)))
  refine le_trans ?_ (Finset.le_sup (f := fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
        (Finset.range (hpEta P N p (s - 1) + 1)).sup fun ilo => hp2Val P N p s k0 k1 ilo)
    (Finset.mem_Icc.mpr ⟨h0, h01.trans h1⟩))
  refine le_trans ?_ (Finset.le_sup (f := fun k1 =>
      (Finset.range (hpEta P N p (s - 1) + 1)).sup fun ilo => hp2Val P N p s k0 k1 ilo)
    (Finset.mem_Icc.mpr ⟨h01, h1⟩))
  exact Finset.le_sup (f := fun ilo => hp2Val P N p s k0 k1 ilo)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hilo))

/-- Lower bound on `hp2Kap` from a digit/block choice with bounded digit sets. -/
theorem hp2Kap_ge {P : Parameters} {N p s : ℕ} {k0 k1 : ℤ} {ilo cH cP mH mP : ℕ}
    (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p)
    (hilo : ilo ≤ hpEta P N p (s - 1)) (hs1 : 1 ≤ s)
    (hOKH : hpOK P N p s k0 k1) (hOKP : perOK P N p (s - 1) k0 k1 ilo)
    (hx : perPmax P N p (s - 1) k0 k1 < (hpElo P N p s : ℤ) ∨ (hpEta P N p s : ℤ) < ilo + p)
    (hcH : (hpJJ P N p s k0 k1).card ≤ cH) (hcP : (perJJ P N p (s - 1) k0 k1 ilo).card ≤ cP)
    (hmH : mH + cH ≤ hpK k0 k1 + 1) (hmH' : mH ≤ hpK k0 k1) (hmP : mP + cP ≤ hpK k0 k1) :
    mH * (hpD P N p s k0 k1 - hpElo P N p s) +
      mP * ((perPmax P N p (s - 1) k0 k1).toNat - ilo + 1) ≤ hp2Kap P N p := by
  classical
  refine le_trans ?_ (hp2Val_le_hp2Kap P N p s k0 k1 ilo hs h0 h01 h1 hilo)
  unfold hp2Val
  rw [if_pos ⟨hs1, hOKH, hOKP, hx⟩]
  unfold hpVal perVal
  rw [if_pos hOKH, if_pos hOKP]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (le_min hmH' (by omega)))
    (Nat.mul_le_mul_right _ (by omega))

end
end CatalanMeasure.GenD.Uniform.W.Tier3
