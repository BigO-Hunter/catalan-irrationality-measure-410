module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTPlus
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPSLB
@[expose] public section
set_option Elab.async false

/-!
# `thinLB3 := supList [thinLB2sum; mtLB3; mLB]`
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Placeholder for the M family: the trivial bound until Theorem M is formalised. -/
def mLB (P : Parameters) (_hP : Admissible P) : NullityLB P := NullityLB.zero P

/-- **`thinLB3`**. -/
def thinLB3 (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [thinLB2sum P hP, mtLB3 P hP, mLB P hP]

theorem thinLB2sum_le_thinLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (thinLB2sum P hP).kap N p ≤ (thinLB3 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB3]) N p

theorem mtLB3_le_thinLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtLB3 P hP).kap N p ≤ (thinLB3 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB3]) N p

theorem mLB_le_thinLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mLB P hP).kap N p ≤ (thinLB3 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [thinLB3]) N p

/-! ### Evaluation lemmas: a specific MT window is below `thinLB3` -/

theorem mtVal2_le_thinLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) [Fact p.Prime]
    (s K D1 e0 : ℕ) (k0 : ℤ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0)
    (h1 : k0 ≤ hpKmax P N p) (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    mtVal2 P N p s K D1 e0 k0 ≤ (thinLB3 P hP).kap N p := by
  have h2 : mtVal2 P N p s K D1 e0 k0 ≤ mtKap2 P N p := by
    unfold mtKap2
    rw [dif_pos (Fact.out : p.Prime)]
    exact le_mtSup P N p (fun s K k0 D1 e0 => mtVal2 P N p s K D1 e0 k0) s K k0 D1 e0 hs h0 h1 hK hD he
  exact h2.trans ((mtBothLB2_le_mtLB3 P hP N p).trans (mtLB3_le_thinLB3 P hP N p))

theorem mtMinusVal_le_thinLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) [Fact p.Prime]
    (s K D1 e0 : ℕ) (k0 : ℤ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0)
    (h1 : k0 ≤ hpKmax P N p) (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    mtMinusVal P N p s K k0 D1 e0 ≤ (thinLB3 P hP).kap N p := by
  have h2 : mtMinusVal P N p s K k0 D1 e0 ≤ mtMinusKap P N p := by
    unfold mtMinusKap
    rw [dif_pos (Fact.out : p.Prime)]
    exact le_mtSup P N p (fun s K k0 D1 e0 => mtMinusVal P N p s K k0 D1 e0) s K k0 D1 e0 hs h0 h1 hK hD he
  exact h2.trans ((mtMinusLB_le_mtLB3 P hP N p).trans (mtLB3_le_thinLB3 P hP N p))

theorem mtPlusVal_le_thinLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) [Fact p.Prime]
    (s K D1 e0 : ℕ) (k0 : ℤ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0)
    (h1 : k0 ≤ hpKmax P N p) (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    mtPlusVal P N p s K D1 e0 k0 ≤ (thinLB3 P hP).kap N p := by
  have h2 : mtPlusVal P N p s K D1 e0 k0 ≤ mtPlusKap P N p := by
    unfold mtPlusKap
    rw [dif_pos (Fact.out : p.Prime)]
    exact le_mtSup P N p (fun s K k0 D1 e0 => mtPlusVal P N p s K D1 e0 k0) s K k0 D1 e0 hs h0 h1 hK hD he
  exact h2.trans ((mtPlusLB_le_mtLB3 P hP N p).trans (mtLB3_le_thinLB3 P hP N p))

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
