module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyVal
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.Cell
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Combine
@[expose] public section
set_option Elab.async false

/-!
# `mLB'`: Family M as a Theorem HY+ instance, and `thinLB4`

`hyTermG` is the HY+ value at the window `(s, K = s-1, k0 = -1, Dn)` where the cell certificate holds
(`p ∤ Z`, `Z = ZHY_s`, Lemma B) and the numerical hypotheses hold, and `0` elsewhere.
`hyKap` is the maximum over `s ∈ {9, 10, 11}` and `Dn < p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters}

/-- The value of one HY+ window. -/
def hyTermG (P : Parameters) (N p s K Z Dn : ℕ) : ℕ :=
  open Classical in
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    if p ≠ 2 ∧ HYNum P N p s Dn ∧ s + 4 ≤ P.H N ∧ ¬ p ∣ Z then hyVal P N p s K Dn (-1) else 0
  else 0

theorem hyTermG_le (hP : Admissible P) {N p s K Z : ℕ} (hN : 0 < N) (hp : p.Prime) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2)
    (hcell : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ¬ q ∣ Z → ∀ H : ℕ, s + 4 ≤ H →
      ∃ u v y : Fin K → ZMod q, HYCell q K s (-1) H u v y) (Dn : ℕ) :
    haveI : Fact p.Prime := ⟨hp⟩
    hyTermG P N p s K Z Dn ≤ nullity P N p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  unfold hyTermG
  rw [dif_pos hp]
  split_ifs with h
  · exact hyVal_le_nullity hP hN hp2 hH h.2.1 (hcell p hp2 h.2.2.2 _ h.2.2.1)
  · exact Nat.zero_le _

/-- Maximum over `Dn < p` of one window family. -/
def hyKapS (P : Parameters) (N p s K Z : ℕ) : ℕ :=
  (Finset.range p).sup fun Dn => hyTermG P N p s K Z Dn

/-- **The M bound**: maximum over `s ∈ {9, 10, 11}`. -/
def hyKap (P : Parameters) (N p : ℕ) : ℕ :=
  max (hyKapS P N p 9 8 ZHY9) (max (hyKapS P N p 10 9 ZHY10) (hyKapS P N p 11 10 ZHY11))

theorem hyKapS_le (hP : Admissible P) {N p s K Z : ℕ} (hN : 0 < N) (hp : p.Prime) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2)
    (hcell : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ¬ q ∣ Z → ∀ H : ℕ, s + 4 ≤ H →
      ∃ u v y : Fin K → ZMod q, HYCell q K s (-1) H u v y) :
    haveI : Fact p.Prime := ⟨hp⟩
    hyKapS P N p s K Z ≤ nullity P N p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact Finset.sup_le fun Dn _ => hyTermG_le hP hN hp hp2 hH hcell Dn

/-- **`mLB'`**: Family M as a Theorem HY+ instance (replaces the placeholder `mLB`). -/
def mLB' (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.ofWindow P (fun _ _ => True) (hyKap P)
    (fun N p hN hp hp2 hH _ => by
      haveI : Fact p.Prime := ⟨hp⟩
      refine max_le (hyKapS_le hP hN hp hp2 hH ?_) (max_le (hyKapS_le hP hN hp hp2 hH ?_)
        (hyKapS_le hP hN hp hp2 hH ?_))
      · intro q _ h2 hc H hH'; exact hyCell_9 h2 hc (by omega)
      · intro q _ h2 hc H hH'; exact hyCell_10 h2 hc (by omega)
      · intro q _ h2 hc H hH'; exact hyCell_11 h2 hc (by omega))

/-- `thinLB4 := supList [thinLB3; mLB']`. -/
def thinLB4 (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [thinLB3 P hP, mLB' P hP]

theorem thinLB3_le_thinLB4 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (thinLB3 P hP).kap N p ≤ (thinLB4 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB4]) N p

theorem mLB'_le_thinLB4 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mLB' P hP).kap N p ≤ (thinLB4 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB4]) N p

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
