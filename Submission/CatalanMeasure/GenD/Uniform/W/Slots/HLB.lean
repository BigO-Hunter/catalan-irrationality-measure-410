module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HFam
@[expose] public section
set_option Elab.async false

/-!
# `H'LB`: the H' family as a `NullityLB`

`hpKap P N p` is the maximum of `hpVal P N p s k0 k1` over the digit `s ≤ H/p` and the block range
`-⌈g/p⌉-1 ≤ k0 ≤ k1 ≤ (n-g)/p + 1`.  It is a nullity lower bound for every admissible design
(`hpLB`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

/-- Smallest block start considered. -/
def hpKmin (P : Parameters) (N p : ℕ) : ℤ := -(((P.g N + p - 1) / p : ℕ) : ℤ) - 1

/-- Largest block end considered. -/
def hpKmax (P : Parameters) (N p : ℕ) : ℤ := (((P.n N - P.g N) / p : ℕ) : ℤ) + 1

/-- Maximum of the H' values over digits and block ranges. -/
def hpKap (P : Parameters) (N p : ℕ) : ℕ :=
  (Finset.range (P.H N / p + 1)).sup fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 => hpVal P N p s k0 k1

theorem hpVal_le_hpKap (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (hs : s ≤ P.H N / p)
    (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p) :
    hpVal P N p s k0 k1 ≤ hpKap P N p := by
  unfold hpKap
  refine le_trans ?_ (Finset.le_sup (f := fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 => hpVal P N p s k0 k1)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hs)))
  refine le_trans ?_ (Finset.le_sup (f := fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 => hpVal P N p s k0 k1)
    (Finset.mem_Icc.mpr ⟨h0, h01.trans h1⟩))
  exact Finset.le_sup (f := fun k1 => hpVal P N p s k0 k1) (Finset.mem_Icc.mpr ⟨h01, h1⟩)

/-- The H' family as a nullity lower bound (any admissible design). -/
def hpLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := hpKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold hpKap
    refine Finset.sup_le fun s _ => Finset.sup_le fun k0 _ => Finset.sup_le fun k1 _ => ?_
    exact hpVal_le_nullity hP hN hp2 hH s k0 k1

end
end CatalanMeasure.GenD.Uniform.W.Slots
