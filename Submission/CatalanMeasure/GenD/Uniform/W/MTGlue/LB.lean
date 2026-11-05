module
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Cell
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Cell17
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Cell18
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (b), `m = 1`, as an unconditional design-generic `NullityLB`

`glueCellLB P hP c` is the `NullityLB` of a rational glue cell `c`: at a prime `p` coprime to the cell
modulus (Lemma B) it is the maximum, over the free integers `D1`, `elo`, of `mtGlueVal1` on those pairs for
which the design part `GlueWin` holds, and `0` elsewhere.  `mtGlueLB'` is the pointwise maximum for the two
cells `s = 17` (`K = 14`, digits `2..15` / `3..16`) and `s = 18` (`K = 15`, digits `2..16` / `3..17`)
of `complete7/mtcon.json`.  No profile hypothesis remains: the existence of `(y, u)` modulo `p` is proved
from the exact rational equations, `cell17_main/over`, `cell18_main/over`.
-/

namespace CatalanMeasure.GenD.Uniform.W.MTGlue
open Module Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.W.ZoneZ
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD CatalanMeasure.Parametric

/-- The glue cell `s = 17`. -/
def cell17 : GlueCell where
  s := 17
  K := 14
  k0 := -1
  y := y17
  u := u17
  A := A17
  B := B17
  J1 := Finset.Icc 2 15
  J2 := Finset.Icc 3 16
  ky := 0
  ku := 0
  hs2 := by norm_num
  hs := by norm_num
  hky := by norm_num
  hku := by norm_num
  hJ1 := fun J hJ => by
    have hJ' := Finset.mem_Icc.mp hJ
    obtain ⟨e1, e2⟩ := cell17_main J (List.mem_range'_1.mpr ⟨hJ'.1, by omega⟩)
    exact ⟨by omega, e1, e2⟩
  hJ2 := fun J hJ => by
    have hJ' := Finset.mem_Icc.mp hJ
    exact ⟨by omega, cell17_over J (List.mem_range'_1.mpr ⟨hJ'.1, by omega⟩)⟩

/-- The glue cell `s = 18`. -/
def cell18 : GlueCell where
  s := 18
  K := 15
  k0 := -1
  y := y18
  u := u18
  A := A18
  B := B18
  J1 := Finset.Icc 2 16
  J2 := Finset.Icc 3 17
  ky := 0
  ku := 0
  hs2 := by norm_num
  hs := by norm_num
  hky := by norm_num
  hku := by norm_num
  hJ1 := fun J hJ => by
    have hJ' := Finset.mem_Icc.mp hJ
    obtain ⟨e1, e2⟩ := cell18_main J (List.mem_range'_1.mpr ⟨hJ'.1, by omega⟩)
    exact ⟨by omega, e1, e2⟩
  hJ2 := fun J hJ => by
    have hJ' := Finset.mem_Icc.mp hJ
    exact ⟨by omega, cell18_over J (List.mem_range'_1.mpr ⟨hJ'.1, by omega⟩)⟩

/-- Non-degeneracy: the first entries of `y` and `u` are nonzero (the moduli are positive). -/
theorem cell17_ky : y17 0 ≠ 0 ∧ u17 0 ≠ 0 := by decide +kernel
theorem cell18_ky : y18 0 ≠ 0 ∧ u18 0 ≠ 0 := by decide +kernel

open Classical in
/-- The value of the cell: maximum of `mtGlueVal1` over the admissible free integers `D1`, `elo`. -/
noncomputable def glueVal (P : Parameters) (c : GlueCell) (N p : ℕ) : ℕ :=
  (Finset.range ((p - 1) / 2 + 1)).sup fun D1 => (Finset.range (P.H N + 1)).sup fun elo =>
    if GlueWin P N p c D1 elo then mtGlueVal1 P N p c.s c.K D1 elo c.k0 else 0

/-- **The glue `NullityLB` of a rational cell.** -/
noncomputable def glueCellLB (P : Parameters) (hP : Admissible P) (c : GlueCell) : NullityLB P :=
  NullityLB.ofWindow P (fun _ p => p.Prime ∧ Nat.Coprime p c.modulus) (glueVal P c)
    (fun N p hN hp hp2 hH hApp => by
      haveI : Fact p.Prime := ⟨hp⟩
      unfold glueVal
      refine Finset.sup_le fun D1 _ => Finset.sup_le fun elo _ => ?_
      by_cases hw : GlueWin P N p c D1 elo
      · rw [if_pos hw]
        exact mtGlueVal1_le_of_ok hP hN hp2 hH (glueCell_ok c hp2 hApp.2 hw)
      · rw [if_neg hw]; exact Nat.zero_le _)

/-- Evaluation: at a good prime and admissible `D1`, `elo` the cell bound dominates `mtGlueVal1`. -/
theorem mtGlueVal1_le_glueCellLB (P : Parameters) (hP : Admissible P) (c : GlueCell) {N p D1 elo : ℕ}
    (hp : p.Prime) (hcop : Nat.Coprime p c.modulus) (hw : GlueWin P N p c D1 elo) :
    mtGlueVal1 P N p c.s c.K D1 elo c.k0 ≤ (glueCellLB P hP c).kap N p := by
  classical
  have h4 := hw.2.2.2.1
  have h1 := hw.1
  have h8 := hw.2.2.2.2.2.2.2.1
  dsimp only [glueCellLB, NullityLB.ofWindow]
  rw [if_pos ⟨hp, hcop⟩]
  unfold glueVal
  refine le_trans ?_ (Finset.le_sup (f := fun D1 => (Finset.range (P.H N + 1)).sup fun elo =>
      if GlueWin P N p c D1 elo then mtGlueVal1 P N p c.s c.K D1 elo c.k0 else 0)
    (Finset.mem_range.mpr (show D1 < (p - 1) / 2 + 1 by omega)))
  refine le_trans ?_ (Finset.le_sup (f := fun elo =>
      if GlueWin P N p c D1 elo then mtGlueVal1 P N p c.s c.K D1 elo c.k0 else 0)
    (Finset.mem_range.mpr (show elo < P.H N + 1 by omega)))
  rw [if_pos hw]

/-- **`mtGlueLB'`**: Theorem MT (b) (glue variant, one profile pair), unconditional, design-generic. -/
noncomputable def mtGlueLB' (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [glueCellLB P hP cell17, glueCellLB P hP cell18]

theorem glueCell17_le (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (glueCellLB P hP cell17).kap N p ≤ (mtGlueLB' P hP).kap N p :=
  NullityLB.le_supList_kap (by simp) N p

theorem glueCell18_le (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (glueCellLB P hP cell18).kap N p ≤ (mtGlueLB' P hP).kap N p :=
  NullityLB.le_supList_kap (by simp) N p

/-- Digit coverage for an interval of digits: a sufficient condition on the design. -/
theorem cov_Icc {P : Parameters} {N p a b : ℕ} (hp : 0 < p) (hlo : a * p ≤ P.b N)
    (hhi : P.L N ≤ (b + 1) * p) :
    ∀ j, P.b N ≤ j → j < P.L N → j / p ∈ Finset.Icc a b := by
  intro j h1 h2
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact (Nat.le_div_iff_mul_le hp).mpr (hlo.trans h1)
  · have : j / p < b + 1 := (Nat.div_lt_iff_lt_mul hp).mpr (lt_of_lt_of_le h2 hhi)
    omega

#print axioms glueCell_ok
#print axioms mtGlueVal1_le_glueCellLB
#print axioms mtGlueLB'
#print axioms cell17_main
#print axioms cell18_over

end CatalanMeasure.GenD.Uniform.W.MTGlue
end
