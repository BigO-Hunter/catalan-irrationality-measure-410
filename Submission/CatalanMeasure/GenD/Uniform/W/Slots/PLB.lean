module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PFam
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HLB
@[expose] public section
set_option Elab.async false

/-!
# `PLB`: the period family as a `NullityLB`
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

/-- Maximum of the P values over digits, block ranges and support starts. -/
def perKap (P : Parameters) (N p : ℕ) : ℕ :=
  (Finset.range (P.H N / p + 1)).sup fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
        (Finset.range (hpEta P N p s + 1)).sup fun ilo => perVal P N p s k0 k1 ilo

/-- The period family as a nullity lower bound (any admissible design). -/
def perLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := perKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold perKap
    refine Finset.sup_le fun s _ => Finset.sup_le fun k0 _ => Finset.sup_le fun k1 _ =>
      Finset.sup_le fun ilo _ => ?_
    exact perVal_le_nullity hP hN hp2 hH s k0 k1 ilo

end
end CatalanMeasure.GenD.Uniform.W.Slots
