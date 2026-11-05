module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax6
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTFam
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTLB
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (T- and T+) with one condition per missing row, as a `NullityLB`

`mtVal2` is `proof4/thmMT.py: countMT` for `use = (1,1)`: `m (D1 - e0) + m (D1 + 1 - e0) - V - r`,
`V = mixMiss` the number of missing rows, `r = (p - q - a)_+`, `a = h + (p-1)/2 - p`.
`mtLB2` is the pointwise maximum with the T- only family.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- **Theorem MT, variant (1), T- and T+ (exact missing-row count).** -/
def mtVal2 (P : Parameters) (N p s K : ℕ) (D1 e0 : ℕ) (k0 : ℤ) : ℕ :=
  if mtOK P N p s D1 e0 then
    (D1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) +
      (D1 + 1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) -
      mixMiss P N p K D1 k0 - (p - P.q N - (P.h N + (p - 1) / 2 - p))
  else 0

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem mtVal2_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s K : ℕ) (D1 e0 : ℕ) (k0 : ℤ) : mtVal2 P N p s K D1 e0 k0 ≤ nullity P N p := by
  classical
  unfold mtVal2
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  obtain ⟨hph, hv, hs, hdeg, he0, he0D, hD⟩ := hc
  obtain ⟨J0, hJ0⟩ := exists_J0 (mtJJ P N p s D1 e0) K
  have h := mt_le_nullity' hP hN hp2 hH (K := K) (e0 := e0) (s := s) k0 hD hph
    (mtJJ P N p s D1 e0) J0 hv hs (by unfold hpEta at hdeg; exact hdeg)
    (by unfold hpEta at he0; exact he0) he0D
    (fun j h1 h2 h3 h4 => mtJJ_spec s D1 e0 hdeg j h1 h2 h3 h4)
  rw [← hJ0] at h
  generalize (D1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) = a at *
  generalize (D1 + 1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) = b at *
  omega

/-- The T- and T+ family (exact missing-row count). -/
def mtKap2 (P : Parameters) (N p : ℕ) : ℕ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    mtSup P N p fun s K k0 D1 e0 => mtVal2 P N p s K D1 e0 k0
  else 0

/-- Theorem MT (1), T- and T+, as a nullity lower bound. -/
def mtBothLB2 (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := mtKap2 P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold mtKap2
    rw [dif_pos hp]
    exact mtSup_le P N p _ _ fun s K k0 D1 e0 => mtVal2_le_nullity hP hN hp2 hH s K D1 e0 k0

/-- **`mtLB2`**: Theorem MT, single-window variant (1): T- and T+, and T- only. -/
def mtLB2 (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [mtBothLB2 P hP, mtMinusLB P hP]

theorem mtBothLB2_le_mtLB2 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtBothLB2 P hP).kap N p ≤ (mtLB2 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB2]) N p

theorem mtMinusLB_le_mtLB2 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtMinusLB P hP).kap N p ≤ (mtLB2 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB2]) N p

#print axioms mtLB2

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
