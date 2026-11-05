module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTFam
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HLB
@[expose] public section
set_option Elab.async false

/-!
# `mtLB`: Theorem MT (variant (1)) as a `NullityLB`

`mtSup` is the maximum of a parameter function over the digit `s ≤ H/p`, the block start `k0`, the
number of blocks `K`, the number of offsets `D1 ≤ (p-1)/2` and `e0 ≤ D1`.  `mtLB` is the pointwise
maximum of the T- and T+ family (`mtVal`) and the T- only family (`mtMinusVal`); both are nullity
lower bounds for every admissible design (`mtLB`'s `ok` field).  No design literal occurs.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Largest number of blocks considered. -/
def mtKmax (P : Parameters) (N p : ℕ) : ℕ := (hpKmax P N p - hpKmin P N p + 1).toNat

/-- Maximum of a parameter function over the digit, blocks and offsets. -/
def mtSup (P : Parameters) (N p : ℕ) (f : ℕ → ℕ → ℤ → ℕ → ℕ → ℕ) : ℕ :=
  (Finset.range (P.H N / p + 1)).sup fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.range (mtKmax P N p + 1)).sup fun K =>
        (Finset.range ((p - 1) / 2 + 1)).sup fun D1 =>
          (Finset.range (D1 + 1)).sup fun e0 => f s K k0 D1 e0

theorem mtSup_le (P : Parameters) (N p : ℕ) (f : ℕ → ℕ → ℤ → ℕ → ℕ → ℕ) (B : ℕ)
    (h : ∀ s K k0 D1 e0, f s K k0 D1 e0 ≤ B) : mtSup P N p f ≤ B := by
  unfold mtSup
  exact Finset.sup_le fun s _ => Finset.sup_le fun k0 _ => Finset.sup_le fun K _ =>
    Finset.sup_le fun D1 _ => Finset.sup_le fun e0 _ => h s K k0 D1 e0

theorem le_mtSup (P : Parameters) (N p : ℕ) (f : ℕ → ℕ → ℤ → ℕ → ℕ → ℕ) (s K : ℕ) (k0 : ℤ)
    (D1 e0 : ℕ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h1 : k0 ≤ hpKmax P N p)
    (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    f s K k0 D1 e0 ≤ mtSup P N p f := by
  unfold mtSup
  refine le_trans ?_ (Finset.le_sup (f := fun s =>
    (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
      (Finset.range (mtKmax P N p + 1)).sup fun K =>
        (Finset.range ((p - 1) / 2 + 1)).sup fun D1 =>
          (Finset.range (D1 + 1)).sup fun e0 => f s K k0 D1 e0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hs)))
  refine le_trans ?_ (Finset.le_sup (f := fun k0 =>
      (Finset.range (mtKmax P N p + 1)).sup fun K =>
        (Finset.range ((p - 1) / 2 + 1)).sup fun D1 =>
          (Finset.range (D1 + 1)).sup fun e0 => f s K k0 D1 e0)
    (Finset.mem_Icc.mpr ⟨h0, h1⟩))
  refine le_trans ?_ (Finset.le_sup (f := fun K =>
        (Finset.range ((p - 1) / 2 + 1)).sup fun D1 =>
          (Finset.range (D1 + 1)).sup fun e0 => f s K k0 D1 e0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hK)))
  refine le_trans ?_ (Finset.le_sup (f := fun D1 =>
          (Finset.range (D1 + 1)).sup fun e0 => f s K k0 D1 e0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hD)))
  exact Finset.le_sup (f := fun e0 => f s K k0 D1 e0) (Finset.mem_range.mpr (Nat.lt_succ_of_le he))

/-- The T- and T+ family (Theorem MT (1)). -/
def mtKap (P : Parameters) (N p : ℕ) : ℕ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    mtSup P N p fun s K k0 D1 e0 => mtVal P N p s K k0 D1 e0
  else 0

/-- The T- only family (Theorem MT (1), T-). -/
def mtMinusKap (P : Parameters) (N p : ℕ) : ℕ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    mtSup P N p fun s K k0 D1 e0 => mtMinusVal P N p s K k0 D1 e0
  else 0

/-- Theorem MT (1), T- and T+, as a nullity lower bound. -/
def mtBothLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := mtKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold mtKap
    rw [dif_pos hp]
    exact mtSup_le P N p _ _ fun s K k0 D1 e0 => mtVal_le_nullity hP hN hp2 hH s K k0 D1 e0

/-- Theorem MT (1), T- only, as a nullity lower bound. -/
def mtMinusLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := mtMinusKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold mtMinusKap
    rw [dif_pos hp]
    exact mtSup_le P N p _ _ fun s K k0 D1 e0 => mtMinusVal_le_nullity hP hN hp2 hH s K k0 D1 e0

/-- **`mtLB`**: Theorem MT, single-window variant (1), T- and T+ (and T- only). -/
def mtLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [mtBothLB P hP, mtMinusLB P hP]

theorem mtBothLB_le_mtLB (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtBothLB P hP).kap N p ≤ (mtLB P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB]) N p

theorem mtMinusLB_le_mtLB (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtMinusLB P hP).kap N p ≤ (mtLB P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB]) N p

#print axioms mtLB

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
