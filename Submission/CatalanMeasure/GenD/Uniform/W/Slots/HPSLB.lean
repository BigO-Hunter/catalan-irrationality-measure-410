module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPS
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PLB
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Combine
@[expose] public section
set_option Elab.async false

/-!
# `hpsLB` and `thinLB2sum`

`hpsVal = hpVal + perVal` is a nullity lower bound for every parameter choice (the two families add
when both apply, and each is a lower bound alone).  `hpsLB` is the maximum over
`(s, k0, k1, ilo)`; `thinLB2sum := supList [thinLB; hpsLB]` is the bound with the H' + P sum.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem hpsVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) :
    hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo ≤ nullity P N p := by
  classical
  by_cases h1 : hpOK P N p s k0 k1
  · by_cases h2 : perOK P N p s k0 k1 ilo
    · exact hps_le_nullity hP hN hp2 hH s k0 k1 ilo h1 h2
    · have : perVal P N p s k0 k1 ilo = 0 := by unfold perVal; rw [if_neg h2]
      rw [this, add_zero]
      exact hpVal_le_nullity hP hN hp2 hH s k0 k1
  · have : hpVal P N p s k0 k1 = 0 := by unfold hpVal; rw [if_neg h1]
    rw [this, zero_add]
    exact perVal_le_nullity hP hN hp2 hH s k0 k1 ilo

/-- Maximum of `hpVal + perVal` over digits, block ranges and support starts. -/
def hpsKap (P : Parameters) (N p : ℕ) : ℕ :=
  (Finset.range (P.H N / p + 1)).sup fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
        (Finset.range (hpEta P N p s + 1)).sup fun ilo =>
          hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo

/-- The H' + P sum as a nullity lower bound (any admissible design). -/
def hpsLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := hpsKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold hpsKap
    refine Finset.sup_le fun s _ => Finset.sup_le fun k0 _ => Finset.sup_le fun k1 _ =>
      Finset.sup_le fun ilo _ => ?_
    exact hpsVal_le_nullity hP hN hp2 hH s k0 k1 ilo

/-- **`thinLB2sum`**: the accepted thin bound together with the H' + P sum. -/
def thinLB2sum (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [Thin.thinLB P hP, hpsLB P hP]

theorem thinLB_le_thinLB2sum (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (Thin.thinLB P hP).kap N p ≤ (thinLB2sum P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB2sum]) N p

theorem hpsLB_le_thinLB2sum (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (hpsLB P hP).kap N p ≤ (thinLB2sum P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB2sum]) N p

end
end CatalanMeasure.GenD.Uniform.W.Slots
